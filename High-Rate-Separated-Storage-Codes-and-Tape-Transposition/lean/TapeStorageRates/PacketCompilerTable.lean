import TapeStorageRates.PacketCompilerMemory

/-! # The bounded record at batch boundaries and the stationary lookup tick -/

namespace TapeStorageRates.PacketCompiler

open Transpose Transpose.Tape Transpose.Tape.Impl

set_option autoImplicit false

def encodePending (n : ℕ) (w : List Bool) : Fin n → Option Bool := fun i => w[i.val]?

theorem encodePending_injective {n : ℕ} {u v : List Bool} (hu : u.length ≤ n) (hv : v.length ≤ n)
    (h : encodePending n u = encodePending n v) : u = v := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < n
  · exact congrFun h ⟨i,hi⟩
  · simp [List.getElem?_eq_none (by omega : u.length ≤ i), List.getElem?_eq_none (by omega : v.length ≤ i)]

def past (M : TM) (s : ℕ) (w : List Bool) (b : ℕ) : List Bool := (run M w (b*s)).outRev.reverse

noncomputable def boundary {s r : ℕ} (L : CellLayout s r) (hs : 0<s) (M : TM) (w : List Bool)
    (b : ℕ) : Boundary M s r :=
  let c := run M w (b*s)
  ⟨c.state, L.offset hs c.inPos, fun j => (workLayout s).offset hs (c.workPos j),
    encodePending (s+r) (L.pendingAt (centres L hs M w b).output (past M s w b))⟩

noncomputable def emitted {s r : ℕ} (L : CellLayout s r) (hs : 0<s) (M : TM) (w : List Bool)
    (b : ℕ) : Option (Fin s → Bool) :=
  let q := (centres L hs M w b).output
  if q < (centres L hs M w (b+1)).output then some (L.payloadAt q (past M s w (b+1))) else none

def neighbour (u : ℤ) (i : Fin 3) : ℤ := u + i.val - 1

theorem neighbour_near (u : ℤ) (i : Fin 3) : |neighbour u i - u| ≤ 1 := by
  have := i.isLt; unfold neighbour; apply abs_le.2; omega

theorem near_is_neighbour {p q : ℤ} (h : |q-p| ≤ 1) : ∃ i : Fin 3, neighbour p i = q := by
  have hh := abs_le.1 h
  refine ⟨⟨(q-p+1).toNat, by omega⟩, ?_⟩
  change p + ((q-p+1).toNat : ℤ) - 1 = q
  omega

noncomputable def inputAt {s r : ℕ} (L : CellLayout s r) (hs : 0<s) (M : TM) (w : List Bool)
    (b : ℕ) (i : Fin 3) : InputWord s r :=
  tapeCell L none (readInput w) (neighbour (centres L hs M w b).input i)

noncomputable def beforeAt {s r : ℕ} (L : CellLayout s r) (hs : 0<s) (M : TM) (w : List Bool)
    (b : ℕ) (i : Fin 3) (j : Fin M.k) : WorkWord M s :=
  workWord s (run M w (b*s)) j (neighbour ((centres L hs M w b).work j) i)

noncomputable def afterAt {s r : ℕ} (L : CellLayout s r) (hs : 0<s) (M : TM) (w : List Bool)
    (b : ℕ) (i : Fin 3) (j : Fin M.k) : WorkWord M s :=
  workWord s (run M w ((b+1)*s)) j (neighbour ((centres L hs M w b).work j) i)

private theorem workWord_eq_of_capture {M : TM} {s : ℕ} {c d : Config M} (j : Fin M.k) (u : ℤ)
    (h : Native.capture s (c.work j) (u*s) = Native.capture s (d.work j) (u*s)) (i : Fin 3) :
    workWord s c j (neighbour u i) = workWord s d j (neighbour u i) := by
  funext l
  let p := neighbour u i * s + l.val - u*s
  have hfit : Native.Fits s 0 p := by
    have hi : (i.val : ℤ) ≤ 2 := by have := i.isLt; omega
    have hl : (l.val : ℤ) < s := by exact_mod_cast l.isLt
    dsimp [Native.Fits, p, neighbour]
    constructor <;> nlinarith [mul_nonneg (Int.natCast_nonneg i.val) (Int.natCast_nonneg s),
      mul_nonneg (sub_nonneg.2 hi) (Int.natCast_nonneg s), Int.natCast_nonneg l.val]
  have he := congrArg (fun X => Native.windowRead X (0 : Fin (M.g+1)) p) h
  rw [Native.windowRead_capture _ _ _ _ hfit, Native.windowRead_capture _ _ _ _ hfit] at he
  simpa [workWord, p] using he

/-- Equality of the bounded boundary state and the three actual scanned cells on each tape
suffices for every field produced at the table tick. Public batch centres may vary with time. -/
theorem table_fields {M : TM} {s r : ℕ} (L : CellLayout s r) (hs : 0<s) {w v : List Bool} (b : ℕ)
    (hb : centres L hs M w b = centres L hs M v b)
    (hn : centres L hs M w (b+1) = centres L hs M v (b+1))
    (hcore : boundary L hs M w b = boundary L hs M v b)
    (hI : inputAt L hs M w b = inputAt L hs M v b)
    (hW : beforeAt L hs M w b = beforeAt L hs M v b) :
    boundary L hs M w (b+1) = boundary L hs M v (b+1) ∧
      afterAt L hs M w b = afterAt L hs M v b ∧ emitted L hs M w b = emitted L hs M v b := by
  let c := run M w (b*s)
  let d := run M v (b*s)
  let W := workLayout s
  have hbi := congrArg Centres.input hb
  have hbw := congrArg Centres.work hb
  have hbo := congrArg Centres.output hb
  have hno := congrArg Centres.output hn
  have hd : c.inPos = d.inPos := calc
    _ = L.start (centres L hs M w b).input + ((boundary L hs M w b).inputOffset.val : ℤ) :=
      (L.start_add_offset hs _).symm
    _ = _ := by rw [hbi,hcore]; exact L.start_add_offset hs _
  have hdw : c.workPos = d.workPos := by
    funext j
    calc
      _ = W.start ((centres L hs M w b).work j) + (((boundary L hs M w b).workOffset j).val : ℤ) :=
        (W.start_add_offset hs _).symm
      _ = _ := by rw [hbw,hcore]; exact W.start_add_offset hs _
  have hi : ∀ u, |u - L.cell hs c.inPos| ≤ 1 →
      tapeCell L none (readInput w) u = tapeCell L none (readInput v) u := by
    intro u hu
    obtain ⟨i, hi⟩ := near_is_neighbour hu
    have hh := congrFun hI i
    change tapeCell L none (readInput w) (neighbour (centres L hs M w b).input i) =
      tapeCell L none (readInput v) (neighbour (centres L hs M v b).input i) at hh
    rw [← hbi] at hh
    exact hi ▸ hh
  have hwork : ∀ j u, |u - W.cell hs (c.workPos j)| ≤ 1 →
      tapeCell W 0 (c.work j) u = tapeCell W 0 (d.work j) u := by
    intro j u hu
    obtain ⟨i,hi⟩ := near_is_neighbour hu
    have hh := congrFun (congrFun hW i) j
    change workWord s c j (neighbour ((centres L hs M w b).work j) i) =
      workWord s d j (neighbour ((centres L hs M v b).work j) i) at hh
    rw [← hbw] at hh
    rw [tapeCell_workWord, tapeCell_workWord]
    exact hi ▸ hh
  obtain ⟨_,hq,hip,hwpos,hcells,out,_,ho₁,ho₂⟩ :=
    three_cell_batch L hs (c := c) (d := d) (congrArg Boundary.state hcore) hd hdw hi hwork
  simp only [c, d, advance_run, ← show (b+1)*s = b*s+s by ring] at hq hip hwpos hcells ho₁ ho₂
  have hout₁ : past M s w (b+1) = past M s w b ++ out.reverse := by
    simpa [past] using congrArg List.reverse ho₁
  have hout₂ : past M s v (b+1) = past M s v b ++ out.reverse := by
    simpa [past] using congrArg List.reverse ho₂
  let q := (centres L hs M w b).output
  let q' := (centres L hs M w (b+1)).output
  have hp₁ : (L.start q).toNat ≤ (past M s w b).length := by
    simpa [q, centres, past] using (L.prefix_start hs (past M s w b).length).2
  have hp₂ : (L.start q).toNat ≤ (past M s v b).length := by
    simpa only [q,hbo,centres,past,List.length_reverse] using (L.prefix_start hs (past M s v b).length).2
  have hqle : q ≤ q' := by
    rcases centres_output_step L hs M w b with h | h <;> dsimp [q,q'] <;> omega
  have hst := Int.toNat_le_toNat ((L.strictMono hs).monotone hqle)
  have hpending : L.pendingAt q (past M s w b) = L.pendingAt q (past M s v b) := by
    have h := congrArg Boundary.pending hcore
    change encodePending (s+r) (L.pendingAt q (past M s w b)) =
      encodePending (s+r) (L.pendingAt (centres L hs M v b).output (past M s v b)) at h
    rw [← hbo] at h
    apply encodePending_injective _ _ h
    · simpa [q, centres, past] using (L.pendingAt_length_lt hs (past M s w b)).le
    · rw [hbo]
      simpa [centres,past] using (L.pendingAt_length_lt hs (past M s v b)).le
  have hpend' : L.pendingAt q' (past M s w (b+1)) = L.pendingAt q' (past M s v (b+1)) := by
    rw [hout₁,hout₂,L.pendingAt_append q q' _ _ hp₁ hst,L.pendingAt_append q q' _ _ hp₂ hst,hpending]
  refine ⟨?_, ?_, ?_⟩
  · apply Boundary.ext
    · exact hq
    · change L.offset hs _ = L.offset hs _; rw [hip]
    · funext j; change W.offset hs _ = W.offset hs _; rw [hwpos]
    · change encodePending _ (L.pendingAt q' _) = encodePending _ (L.pendingAt (centres L hs M v (b+1)).output _)
      rw [← hno]; exact congrArg (encodePending _) hpend'
  · funext i j
    unfold afterAt
    rw [← hbw]
    exact workWord_eq_of_capture j _ (hcells j) i
  · simp only [emitted, ← hbo, ← hno]
    split
    · congr 1
      change L.payloadAt q _ = L.payloadAt q _
      rw [hout₁,hout₂,L.payloadAt_append q _ _ hp₁,L.payloadAt_append q _ _ hp₂,hpending]
    · rfl

end TapeStorageRates.PacketCompiler
