import TapeStorageRates.NativeCompiler
import Transpose.Tape.Encode

/-! A copying machine whose dummy work head advances on every one. For this
particular source, one independent descriptor bit per complete s-block is
visible in the genuine trace of the compiled native machine. -/

namespace TapeStorageRates.Native

open Transpose Transpose.Tape Transpose.Tape.Impl MergeDepth

private def copyAction (b : Bool) :
    Fin 1 × Dir × (Fin 1 → Fin 1 × Dir) × Option Bool :=
  (0,.right,fun _ => (0,if b then .right else .stay),some b)

/-- Scan left to right and copy; the work alphabet has only its blank. -/
abbrev copier : TM where
  k := 1
  q := 0
  g := 0
  δ := fun _ bit _ => bit.map copyAction

private theorem copy_run (w : List Bool) (i : ℕ) (h : i ≤ w.length) :
    (run copier w i).inPos = i ∧
    (run copier w i).workPos 0 = ((w.take i).count true : ℕ) ∧
    (run copier w i).outRev = (w.take i).reverse := by
  induction i with
  | zero => simp [run_zero,init]
  | succ i ih =>
    obtain ⟨ip,wp,op⟩ := ih (by omega)
    have lo : i<w.length := by omega
    have e : transAt copier w i = some (copyAction w[i]) := by
      change (readInput w (run copier w i).inPos).map copyAction = _
      rw [ip,readInput_natCast,nth_eq_getElem?,List.getElem?_eq_getElem lo]
      rfl
    rw [run_succ_of_some e,List.take_succ_eq_append_getElem lo]
    cases hb : w[i] <;> simp [Dir.shift,ip,wp,op,List.count_append]

theorem copier_halts (w : List Bool) :
    HaltsAt copier w w.length ∧ (run copier w w.length).outRev.reverse = w := by
  obtain ⟨ip,-,op⟩ := copy_run w w.length le_rfl
  refine ⟨⟨?_,?_⟩,by simp [op]⟩
  · intro i hi
    have h := (copy_run w i hi.le).1
    change (readInput w (run copier w i).inPos).map copyAction ≠ none
    rw [h,readInput_natCast,nth_eq_getElem?,List.getElem?_eq_getElem hi]
    exact Option.some_ne_none _
  · change (readInput w (run copier w w.length).inPos).map copyAction = none
    rw [ip,readInput_eq_none (Or.inr le_rfl)]
    rfl

private def expand (s : ℕ) (as : List Bool) := as.flatMap (List.replicate s)

private theorem length_expand (s : ℕ) (as : List Bool) :
    (expand s as).length = as.length*s := by
  induction as with
  | nil => simp [expand]
  | cons a as ih =>
    change (List.replicate s a ++ expand s as).length = (as.length+1)*s
    simp [ih,Nat.succ_mul,Nat.add_comm]

private theorem count_expand (s : ℕ) (as : List Bool) :
    (expand s as).count true = s*as.count true := by
  induction as with
  | nil => simp [expand]
  | cons a as ih =>
    change (List.replicate s a ++ expand s as).count true = _
    rw [List.count_append,ih]
    cases a <;> simp [List.count_replicate,Nat.mul_succ,Nat.add_comm]

/-- The remaining L mod s input bits are fixed zeros. -/
def blockInput (s L : ℕ) (x : Fin (L/s) → Bool) : List Bool :=
  expand s (List.ofFn x) ++ List.replicate (L%s) false

theorem blockInput_length (s L : ℕ) (x : Fin (L/s) → Bool) : (blockInput s L x).length=L := by
  simpa [blockInput,length_expand] using Nat.div_add_mod' L s

private theorem prefix_ones (s L : ℕ) (x : Fin (L/s) → Bool) (j : ℕ) (hj : j ≤ L/s) :
    ((blockInput s L x).take (j*s)).count true = s*((List.ofFn x).take j).count true := by
  let a := List.ofFn x
  have hx : (expand s (a.take j)).length = j*s := by
    simp [length_expand,a,List.length_take,hj]
  have split : blockInput s L x =
      expand s (a.take j) ++ (expand s (a.drop j) ++ List.replicate (L%s) false) := by
    change expand s a ++ _ = _
    simp only [expand,← List.append_assoc,← List.flatMap_append,List.take_append_drop]
  rw [split,← hx,List.take_left,count_expand]

private theorem anchor_interval (M : TM) {s : ℕ} (hs : 0<s) (w : List Bool) (j : ℕ)
    (a : Fin M.k) (alive : ∀ i<j*s, transAt M w i ≠ none) :
    let p := (trace (machine M hs) w).work a ((10*s+1)*j)
    p ≤ (run M w (j*s)).workPos a ∧ (run M w (j*s)).workPos a < p+s := by
  obtain ⟨r,ai,aw,out,atime,-,-,heads,-⟩ := full_blocks M hs w j alive
  dsimp only [runAt] at atime
  rw [← workPos_eq_work,atime,heads]
  have := (r.ow a).isLt
  simp [anchored,Frame.native]

private theorem counts_eq {s a b : ℕ} (_hs : 0<s) {p : ℤ}
    (ha : p ≤ (s*a : ℕ) ∧ ((s*a : ℕ) : ℤ)<p+s)
    (hb : p ≤ (s*b : ℕ) ∧ ((s*b : ℕ) : ℤ)<p+s) : a=b := by
  push_cast at ha hb
  by_contra he
  rcases lt_or_gt_of_ne he with hi | hi
  · have h' : (a : ℤ)+1 ≤ b := by omega
    have := mul_le_mul_of_nonneg_left h' (Int.natCast_nonneg s)
    nlinarith
  · have h' : (b : ℤ)+1 ≤ a := by omega
    have := mul_le_mul_of_nonneg_left h' (Int.natCast_nonneg s)
    nlinarith

theorem blockInput_trace_injective {s : ℕ} (hs : 0<s) (L : ℕ) :
    Function.Injective (fun x : Fin (L/s) → Bool => trace (machine copier hs) (blockInput s L x)) := by
  intro x y eqTrace
  have cum (j : ℕ) (hj : j ≤ L/s) : ((List.ofFn x).take j).count true =
      ((List.ofFn y).take j).count true := by
    have bound : j*s ≤ L := (Nat.mul_le_mul_right s hj).trans (Nat.div_mul_le_self _ _)
    have bound' (z : Fin (L/s) → Bool) : j*s ≤ (blockInput s L z).length := by
      simpa [blockInput_length] using bound
    have necessary (z : Fin (L/s) → Bool) :=
      anchor_interval copier hs (blockInput s L z) j 0 (by
        intro i hi; exact (copier_halts _).1.1 _ (hi.trans_le (bound' z)))
    have a := necessary x
    have b := necessary y
    dsimp only at a b
    rw [show trace (machine copier hs) (blockInput s L x) =
      trace (machine copier hs) (blockInput s L y) from eqTrace,
      (copy_run _ _ (bound' x)).2.1,prefix_ones s L x j hj] at a
    rw [(copy_run _ _ (bound' y)).2.1,prefix_ones s L y j hj] at b
    exact counts_eq hs a b
  funext i
  have before := cum i.val i.isLt.le
  have after := cum (i.val+1) i.isLt
  rw [List.take_succ_eq_append_getElem (by simp),
    List.take_succ_eq_append_getElem (l := List.ofFn y) (by simp),
    List.count_append,List.count_append,before] at after
  have e : List.count true [x i] = List.count true [y i] := by
    simpa [List.getElem_ofFn] using after
  cases hx : x i <;> cases hy : y i <;> simp [hx,hy] at e ⊢

open Classical in
/-- At every length the compiled copier has 2^(L/s) distinct full motion traces
on the exhibited inputs, all of which have the same output length. -/
theorem copy_trace_card {s : ℕ} (hs : 0<s) (L : ℕ) :
    let inputs := (Finset.univ : Finset (Fin (L/s) → Bool))
    (inputs.image (fun x => trace (machine copier hs) (blockInput s L x))).card = 2^(L/s) := by
  classical
  dsimp only
  rw [Finset.card_image_of_injective _ (blockInput_trace_injective hs L)]
  simp

end TapeStorageRates.Native
