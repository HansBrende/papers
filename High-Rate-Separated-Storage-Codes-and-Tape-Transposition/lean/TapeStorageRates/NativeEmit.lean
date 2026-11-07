import TapeStorageRates.NativePhysical

/-! The emitting and drain phases append the selected words in true input
order. Splitting the output at s keeps precisely the remaining suffix. -/

namespace TapeStorageRates.Native

open Transpose Transpose.Tape Transpose.Tape.Impl MergeDepth

def emitted {M : TM} {s : ℕ} (r : Registers M s) : List Bool :=
  if r.desc.2 then List.ofFn r.toEmit else []

theorem length_offsetWord {s : ℕ} (n : Fin s) (data : Fin s → Bool) :
    (offsetWord n data).length = n.val := List.length_ofFn

private theorem get_offsetWord {s : ℕ} (r i : Fin s) (data : Fin s → Bool) :
    (offsetWord r data)[i.val]? = if i.val < r.val then some (data i) else none := by
  by_cases hi : i.val < r.val
  · simp [offsetWord,hi,List.getElem_ofFn]
  · rw [ite_eq_right hi,List.getElem?_eq_none (by simpa [length_offsetWord] using Nat.le_of_not_gt hi)]

private def applyBit (x : Option Bool) (out : List Bool) : List Bool :=
  x.elim out (fun b => b::out)

private theorem take_print (xs out : List Bool) (i : ℕ) :
    applyBit xs[i]? ((xs.take i).reverse++out) = (xs.take (i+1)).reverse++out := by
  rw [List.take_add_one]
  cases h : xs[i]? <;> simp [applyBit]

private theorem anchored_print {M : TM} {s : ℕ} (ph ph' : Phase s) (r : Registers M s)
    (ai : ℤ) (aw : Fin M.k → ℤ) (mem : Fin M.k → ℤ → Fin (M.g+1))
    (out : List Bool) (b : Option Bool) :
    (anchored ph r ai aw 0 mem out).apply
      (uniform ph' r .stay (fun j => mem j (aw j+0)) b) =
    anchored ph' r ai aw 0 mem (applyBit b out) := by
  apply Frame.ext
  · rfl
  · rfl
  · rfl
  · funext j p
    simp [anchored,Frame.apply,uniform]
    by_cases h : p=aw j <;> simp [h]
  · cases b <;> rfl

private theorem run_print_from {M : TM} {s : ℕ} (hs : 0<s) (w : List Bool) (o : Option (Config (machine M hs))) (t : ℕ)
    (ph : Fin s → Phase s) (after : Phase s) (r : Registers M s)
    (ai : ℤ) (aw : Fin M.k → ℤ) (mem : Fin M.k → ℤ → Fin (M.g+1))
    (out bits : List Bool) (hbits : bits.length ≤ s)
    (h : runAt (machine M hs) w o t =
      (anchored (ph ⟨0,hs⟩) r ai aw 0 mem out).native hs)
    (tick : ∀ i x a, drive hs (ph i,r) x a =
      some (uniform (nextIndex i ph after) r .stay a bits[i.val]?)) :
    runAt (machine M hs) w o (t+s) =
      (anchored after r ai aw 0 mem (bits.reverse++out)).native hs := by
  let f := fun i : ℕ => anchored (phaseAt ph after i) r ai aw 0 mem ((bits.take i).reverse++out)
  have e := run_frames_from hs w o t s f (by simpa [f,phaseAt,hs] using h) (by
    intro i hi
    let j : Fin s := ⟨i,hi⟩
    have hp : phaseAt ph after i = ph j := phaseAt_fin _ _ j
    change (drive hs (phaseAt ph after i,r) _ _).map _ = some _
    rw [hp,tick]
    change some ((f i).apply (uniform (nextIndex j ph after) r .stay
      (fun a => mem a (aw a+0)) bits[i]?)) = _
    dsimp only [f]
    rw [anchored_print,nextIndex_phaseAt,take_print])
  simpa [f,phaseAt,List.take_of_length_le hbits] using e

theorem run_emit_from {M : TM} {s : ℕ} (hs : 0<s) (w : List Bool) (o : Option (Config (machine M hs))) (t : ℕ)
    (r : Registers M s) (ai : ℤ) (aw : Fin M.k → ℤ)
    (mem : Fin M.k → ℤ → Fin (M.g+1)) (out : List Bool)
    (h : runAt (machine M hs) w o t =
      (anchored (.emit ⟨0,hs⟩) r ai aw 0 mem out).native hs) :
    runAt (machine M hs) w o (t+s) =
      (anchored (if r.stopped then .drain ⟨0,hs⟩ else .left ⟨0,hs⟩) r ai aw 0 mem
        ((emitted r).reverse++out)).native hs := by
  apply run_print_from hs w o t .emit _ r ai aw mem out _ ?_ h
  · intro i x a
    cases hb : r.desc.2 <;> simp [drive,emitted,hb,List.getElem_ofFn]
  · cases hb : r.desc.2 <;> simp [emitted,hb]

theorem run_drain_from {M : TM} {s : ℕ} (hs : 0<s) (w : List Bool) (o : Option (Config (machine M hs))) (t : ℕ)
    (r : Registers M s) (ai : ℤ) (aw : Fin M.k → ℤ)
    (mem : Fin M.k → ℤ → Fin (M.g+1)) (out : List Bool)
    (h : runAt (machine M hs) w o t =
      (anchored (.drain ⟨0,hs⟩) r ai aw 0 mem out).native hs) :
    runAt (machine M hs) w o (t+s) = (anchored .done r ai aw 0 mem
      ((offsetWord r.pendingLen r.pending).reverse++out)).native hs := by
  apply run_print_from hs w o t .drain .done r ai aw mem out _ (by
      rw [length_offsetWord]; exact r.pendingLen.isLt.le) h
  intro i x a
  rw [get_offsetWord]
  rfl

private theorem prefixCells (s : ℕ) (xs : List Bool) (n : ℕ) (h : n ≤ s) (h' : n ≤ xs.length) :
    List.ofFn (fun i : Fin n => cellsOfWord s xs ⟨i.val, i.isLt.trans_le h⟩) = xs.take n := by
  apply List.ext_getElem
  · simp [List.length_take, h']
  · intro i hL hR
    have hi : i < n := by simpa using hL
    have hxs := hi.trans_le h'
    simp [cellsOfWord,List.getElem_ofFn, List.getElem?_eq_getElem hxs]

/-- The table's full word and residual word partition exactly the old pending
word followed by the freshly simulated output. -/
theorem table_output {M : TM} {s : ℕ} (hs : 0<s) (r : Registers M s) :
    let v := localConfig M s r.q r.oi r.ow r.wrk
    let bits := offsetWord r.pendingLen r.pending ++
      (advance M (windowRead r.inp none) s v).1.outRev.reverse
    let r' := updateTable hs r
    emitted r' ++ offsetWord r'.pendingLen r'.pending = bits := by
  dsimp only
  let v := localConfig M s r.q r.oi r.ow r.wrk
  let bits := offsetWord r.pendingLen r.pending ++
    (advance M (windowRead r.inp none) s v).1.outRev.reverse
  have hv := advance_output_le M (windowRead r.inp none) s v
  have hlen : bits.length < 2*s := by
    simp only [bits,List.length_append,List.length_reverse,length_offsetWord]
    change _ ≤ 0+s at hv
    have := r.pendingLen.isLt
    omega
  by_cases enough : s ≤ bits.length
  · have leftover : bits.length % s = bits.length-s := by
      rw [Nat.mod_eq_sub_mod enough, Nat.mod_eq_of_lt (by omega)]
    change (if decide (s ≤ bits.length) then List.ofFn (cellsOfWord s bits) else []) ++
      offsetWord ⟨bits.length%s,_⟩ (cellsOfWord s (if decide (s ≤ bits.length) then bits.drop s else bits)) = bits
    simp only [enough,decide_true,ite_true]
    rw [show List.ofFn (cellsOfWord s bits) = bits.take s from prefixCells s bits s le_rfl enough]
    have tail := prefixCells s (bits.drop s) (bits.length % s) (Nat.mod_lt _ hs).le (by
      simp [leftover])
    rw [show offsetWord ⟨bits.length%s,Nat.mod_lt _ hs⟩ (cellsOfWord s (bits.drop s)) = bits.drop s by
      change List.ofFn _ = _
      rw [tail,List.take_of_length_le (by simp [leftover])]]
    exact List.take_append_drop _ _
  · have short := Nat.lt_of_not_ge enough
    change (if decide (s ≤ bits.length) then List.ofFn (cellsOfWord s bits) else []) ++
      offsetWord ⟨bits.length%s,_⟩ (cellsOfWord s (if decide (s ≤ bits.length) then bits.drop s else bits)) = bits
    simp only [enough,decide_false,Bool.false_eq_true,ite_false,List.nil_append]
    have all := prefixCells s bits (bits.length % s) (Nat.mod_lt _ hs).le (by
      simp [Nat.mod_eq_of_lt short])
    change List.ofFn _ = _
    rw [all, Nat.mod_eq_of_lt short,List.take_length]

end TapeStorageRates.Native
