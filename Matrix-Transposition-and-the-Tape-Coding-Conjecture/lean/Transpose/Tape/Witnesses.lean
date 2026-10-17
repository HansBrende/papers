import Transpose.Tape.Counting
import Transpose.Tape.Witness

/-!
# Non-vacuity witnesses

* The copy machine of `Sanity.lean` is oblivious on inputs of every length, and it transposes
  `1 × 1` matrices.
* `Witness.tr2` is an oblivious transposer for `2 × 2` matrices with 1-bit entries.
* `Witness.tr2k` is the same with one idle work tape (`k = 1`).
-/

namespace Transpose.Tape.Impl

open Transpose

variable {M : TM}

/-- Obliviousness only needs checking up to the halting time. -/
theorem obliviousOn_of_le {W : Set (List Bool)} {T : ℕ} (hhalt : ∀ w ∈ W, HaltsAt M w T)
    (hagree : ∀ w ∈ W, ∀ w' ∈ W, ∀ τ ≤ T,
      (run M w τ).inPos = (run M w' τ).inPos ∧ (run M w τ).workPos = (run M w' τ).workPos ∧
        (outBit M w τ).isSome = (outBit M w' τ).isSome) :
    ObliviousOn M W T := by
  refine ⟨hhalt, fun w hw w' hw' τ => ?_⟩
  rcases le_or_gt τ T with hτ | hτ
  · exact hagree w hw w' hw' τ hτ
  · have h1 := run_of_le_of_none (hhalt w hw).2 (le_of_lt hτ)
    have h2 := run_of_le_of_none (hhalt w' hw').2 (le_of_lt hτ)
    have h3 := transAt_of_le_of_none (hhalt w hw).2 (le_of_lt hτ)
    have h4 := transAt_of_le_of_none (hhalt w' hw').2 (le_of_lt hτ)
    obtain ⟨a1, a2, -⟩ := hagree w hw w' hw' T le_rfl
    refine ⟨by rw [h1, h2, a1], by rw [h1, h2, a2], ?_⟩
    simp [outBit, h3, h4]

/-! ### The copy machine -/

theorem transAt_copyTM (w : List Bool) (τ : ℕ) :
    transAt Sanity.copyTM w τ =
      (inSym Sanity.copyTM w τ).map (fun b => (0, Dir.right, fun i => i.elim0, some b)) := by
  unfold transAt
  cases inSym Sanity.copyTM w τ <;> rfl

theorem copyTM_inPos (w : List Bool) : ∀ τ ≤ w.length, (run Sanity.copyTM w τ).inPos = τ := by
  intro τ
  induction τ with
  | zero => intro _; rfl
  | succ τ ih =>
    intro hτ
    have h1 := ih (by omega)
    have hsym : inSym Sanity.copyTM w τ = some (w[τ]'(by omega)) := by
      simp only [inSym, h1]
      rw [readInput_natCast, nth_eq_getElem?, List.getElem?_eq_getElem]
    rw [run_succ_inPos, transAt_copyTM, hsym]
    simp [Dir.shift, h1]

theorem copyTM_haltsAt (w : List Bool) : HaltsAt Sanity.copyTM w w.length := by
  refine ⟨fun τ hτ => ?_, ?_⟩
  · rw [transAt_copyTM]
    simp only [inSym, copyTM_inPos w τ (le_of_lt hτ)]
    rw [readInput_natCast, nth_eq_getElem?, List.getElem?_eq_getElem hτ]
    simp
  · rw [transAt_copyTM]
    simp only [inSym, copyTM_inPos w _ le_rfl]
    rw [readInput_natCast, nth_eq_none_of_le le_rfl]
    rfl

theorem copyTM_outBit (w : List Bool) {τ : ℕ} (hτ : τ < w.length) :
    outBit Sanity.copyTM w τ = some (w[τ]'hτ) := by
  simp only [outBit, transAt_copyTM, inSym, copyTM_inPos w τ (le_of_lt hτ)]
  rw [readInput_natCast, nth_eq_getElem?, List.getElem?_eq_getElem hτ]
  rfl

theorem copyTM_obliviousOn (ℓ : ℕ) : ObliviousOn Sanity.copyTM (inputsOfLength ℓ) ℓ := by
  apply obliviousOn_of_le
  · intro w hw
    have hw' : w.length = ℓ := hw
    rw [← hw']; exact copyTM_haltsAt w
  · intro w hw w' hw' τ hτ
    have hl : w.length = ℓ := hw
    have hl' : w'.length = ℓ := hw'
    refine ⟨?_, funext (fun i => i.elim0), ?_⟩
    · rw [copyTM_inPos w τ (by omega), copyTM_inPos w' τ (by omega)]
    · rcases Nat.lt_or_ge τ ℓ with hlt | hge
      · rw [copyTM_outBit w (by omega), copyTM_outBit w' (by omega)]; rfl
      · have e1 : τ = w.length := by omega
        have e2 : τ = w'.length := by omega
        have n1 := (copyTM_haltsAt w).2
        have n2 := (copyTM_haltsAt w').2
        rw [← e1] at n1; rw [← e2] at n2
        simp [outBit, n1, n2]

/-- The copy machine outputs its input. -/
theorem copyTM_output (w : List Bool) :
    (run Sanity.copyTM w w.length).outRev.reverse = w := by
  have hlen : ∀ τ ≤ w.length, (run Sanity.copyTM w τ).outRev.length = τ := by
    intro τ
    induction τ with
    | zero => intro _; rfl
    | succ τ ih =>
      intro hτ
      rw [outRev_length_succ, ih (by omega), copyTM_outBit w (by omega)]
      rfl
  apply list_eq_of_nth (L := w.length)
  · rw [List.length_reverse, hlen _ le_rfl]
  · rfl
  · intro d hd
    have := output_nth_eq_outBit (M := Sanity.copyTM) w hd
      (by rw [copyTM_outBit w hd]; rfl)
    rw [hlen d (le_of_lt hd), copyTM_outBit w hd] at this
    rw [this, nth_eq_getElem?, List.getElem?_eq_getElem hd]

theorem copyTM_transposes (b : ℕ) : Transposes Sanity.copyTM 1 b := by
  intro A
  refine ⟨(encode 1 b A).length, (computesWithin_iff _ _).2
    ⟨_, le_rfl, copyTM_haltsAt _, ?_⟩⟩
  rw [copyTM_output]
  apply encode_eq_of_pointwise
  intro i j t hi hj _
  have : i = 0 := by omega
  have : j = 0 := by omega
  subst_vars
  rfl

/-! ### The `2 × 2` transposer `tr2` -/

theorem tr2_encode (A : Matrix) : encode 2 1 A = [A 0 0 0, A 0 1 0, A 1 0 0, A 1 1 0] := rfl

/-- The common schedule of `tr2`, checked on all 16 inputs. -/
theorem tr2_schedule : ∀ a b c d : Bool, ∀ τ ≤ 5,
    (run Witness.tr2 [a, b, c, d] τ).inPos = ([0, 1, 2, 3, 3, 3] : List ℤ).getD τ 0 ∧
    (outBit Witness.tr2 [a, b, c, d] τ).isSome =
      ([true, false, true, true, true, false] : List Bool).getD τ false := by
  decide

theorem tr2_halts : ∀ a b c d : Bool, HaltsAt Witness.tr2 [a, b, c, d] 5 := by
  intro a b c d
  refine ⟨?_, ?_⟩
  · revert a b c d; decide
  · revert a b c d; decide

theorem tr2_output : ∀ a b c d : Bool,
    (run Witness.tr2 [a, b, c, d] 5).outRev.reverse = [a, c, b, d] := by
  decide

theorem length_four {w : List Bool} (hw : w.length = 4) :
    ∃ a b c d, w = [a, b, c, d] := by
  match w, hw with
  | [a, b, c, d], _ => exact ⟨a, b, c, d, rfl⟩

theorem tr2_obliviousOn : ObliviousOn Witness.tr2 (matrixInputs 2 1) 5 := by
  rw [matrixInputs_eq]
  apply obliviousOn_of_le
  · intro w hw
    obtain ⟨a, b, c, d, rfl⟩ := length_four hw
    exact tr2_halts a b c d
  · intro w hw w' hw' τ hτ
    obtain ⟨a, b, c, d, rfl⟩ := length_four hw
    obtain ⟨a', b', c', d', rfl⟩ := length_four hw'
    obtain ⟨h1, h2⟩ := tr2_schedule a b c d τ hτ
    obtain ⟨h1', h2'⟩ := tr2_schedule a' b' c' d' τ hτ
    exact ⟨h1.trans h1'.symm, funext (fun i => i.elim0), h2.trans h2'.symm⟩

theorem tr2_transposes : Transposes Witness.tr2 2 1 := by
  intro A
  refine ⟨5, (computesWithin_iff _ _).2 ⟨5, le_rfl, ?_, ?_⟩⟩
  · rw [tr2_encode]; exact tr2_halts _ _ _ _
  · rw [tr2_encode, tr2_encode, tr2_output]
    rfl


/-! ### The Cut Lemma is non-trivial on `tr2` -/

theorem tr2_zero_inPos :
    (run Witness.tr2 (encode 2 1 (fun _ _ _ => false)) 2).inPos = 2 ∧
      (run Witness.tr2 (encode 2 1 (fun _ _ _ => false)) 3).inPos = 3 ∧
      (run Witness.tr2 (encode 2 1 (fun _ _ _ => false)) 4).inPos = 3 := by
  decide

theorem tr2_zero_out :
    (outBit Witness.tr2 (encode 2 1 (fun _ _ _ => false)) 2).isSome = true ∧
      (outBit Witness.tr2 (encode 2 1 (fun _ _ _ => false)) 3).isSome = true ∧
      (outBit Witness.tr2 (encode 2 1 (fun _ _ _ => false)) 4).isSome = true ∧
      (run Witness.tr2 (encode 2 1 (fun _ _ _ => false)) 2).outRev.length = 1 ∧
      (run Witness.tr2 (encode 2 1 (fun _ _ _ => false)) 3).outRev.length = 2 ∧
      (run Witness.tr2 (encode 2 1 (fun _ _ _ => false)) 4).outRev.length = 3 := by
  decide

theorem tr2_srcRows :
    srcRows Witness.tr2 (encode 2 1 (fun _ _ _ => false)) 2 1 {2, 3, 4} = {1} := by
  obtain ⟨h2, h3, h4⟩ := tr2_zero_inPos
  ext i
  simp only [srcRows, Finset.mem_filter, Finset.mem_range, Finset.mem_insert,
    Finset.mem_singleton, exists_eq_or_imp, exists_eq_left, h2, h3, h4]
  constructor
  · rintro ⟨hi, h⟩
    rcases h with h | h | h <;> push_cast at h <;> omega
  · rintro rfl; refine ⟨by norm_num, Or.inl ?_⟩; norm_num

theorem tr2_appended (o : ℕ) :
    AppendedDuring Witness.tr2 (encode 2 1 (fun _ _ _ => false)) {2, 3, 4} o ↔
      o = 1 ∨ o = 2 ∨ o = 3 := by
  obtain ⟨s2, s3, s4, l2, l3, l4⟩ := tr2_zero_out
  simp only [AppendedDuring, Finset.mem_insert, Finset.mem_singleton, exists_eq_or_imp,
    exists_eq_left, s2, s3, s4, l2, l3, l4, true_and]
  omega

theorem tr2_snkCols :
    snkCols Witness.tr2 (encode 2 1 (fun _ _ _ => false)) 2 1 {2, 3, 4} = {1} := by
  ext j
  simp only [snkCols, Finset.mem_filter, Finset.mem_range, Finset.mem_singleton, tr2_appended]
  constructor
  · rintro ⟨hj, h⟩
    by_contra hne
    have : j = 0 := by omega
    subst this
    have := h 0 (by norm_num) (by norm_num)
    omega
  · rintro rfl
    exact ⟨by norm_num, fun o h1 h2 => by omega⟩

/-- Non-vacuity of the Cut Lemma: on `tr2`, with the all-zero input and `J = {2, 3, 4}`,
`S_J = {(0, 1)}`. -/
theorem tr2_cutPairs :
    cutPairs Witness.tr2 (encode 2 1 (fun _ _ _ => false)) 2 1 {2, 3, 4} = {(0, 1)} := by
  rw [cutPairs, tr2_srcRows, tr2_snkCols]
  decide

/-- The frozen statement's `TransposesWithin` gives `Transposes` at the frozen entry width. -/
theorem transposes_of_transposesWithin {M : TM} {T : ℕ → ℕ} (h : TransposesWithin M T) :
    ∀ n, 1 ≤ n → Transposes M n (entryBits n) :=
  fun n hn A => ⟨_, h n hn A⟩

/-! ### `tr2k`: `tr2` with one idle work tape -/

/-- The common schedule of `tr2k`, checked on all 16 inputs. -/
theorem tr2k_schedule : ∀ a b c d : Bool, ∀ τ ≤ 5,
    (run Witness.tr2k [a, b, c, d] τ).inPos = ([0, 1, 2, 3, 3, 3] : List ℤ).getD τ 0 ∧
    (run Witness.tr2k [a, b, c, d] τ).workPos ⟨0, by decide⟩ = 0 ∧
    (outBit Witness.tr2k [a, b, c, d] τ).isSome =
      ([true, false, true, true, true, false] : List Bool).getD τ false := by
  decide

theorem tr2k_halts : ∀ a b c d : Bool, HaltsAt Witness.tr2k [a, b, c, d] 5 := by
  intro a b c d
  refine ⟨?_, ?_⟩
  · revert a b c d; decide
  · revert a b c d; decide

theorem tr2k_output : ∀ a b c d : Bool,
    (run Witness.tr2k [a, b, c, d] 5).outRev.reverse = [a, c, b, d] := by
  decide

theorem tr2k_obliviousOn : ObliviousOn Witness.tr2k (matrixInputs 2 1) 5 := by
  rw [matrixInputs_eq]
  apply obliviousOn_of_le
  · intro w hw
    obtain ⟨a, b, c, d, rfl⟩ := length_four hw
    exact tr2k_halts a b c d
  · intro w hw w' hw' τ hτ
    obtain ⟨a, b, c, d, rfl⟩ := length_four hw
    obtain ⟨a', b', c', d', rfl⟩ := length_four hw'
    obtain ⟨h1, h2, h3⟩ := tr2k_schedule a b c d τ hτ
    obtain ⟨h1', h2', h3'⟩ := tr2k_schedule a' b' c' d' τ hτ
    refine ⟨h1.trans h1'.symm, funext (fun i => ?_), h3.trans h3'.symm⟩
    have : i = ⟨0, by decide⟩ := Fin.ext (by
      show i.val = 0
      have h : i.val < 1 := i.isLt
      omega)
    subst this
    exact h2.trans h2'.symm

theorem tr2k_transposes : Transposes Witness.tr2k 2 1 := by
  intro A
  refine ⟨5, (computesWithin_iff _ _).2 ⟨5, le_rfl, ?_, ?_⟩⟩
  · rw [tr2_encode]; exact tr2k_halts _ _ _ _
  · rw [tr2_encode, tr2_encode, tr2k_output]
    rfl

end Transpose.Tape.Impl
