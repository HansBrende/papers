import Transpose.Tape.Counting
import Transpose.Tape.Lemma3

/-!
# The Slot Cut Bound and Discrete Isoperimetry (frozen-model form)

* `slot_cut_bound`: one union of slots, pair residency.
* `sum_entry_labelPart_le`: the entry data summed over the label classes of a slot labelling, for
  any admissible residency; `slot_cut_bound_partition` follows.
* `uncovered_cols_le_slots(_len)`: `σ ≤ M_b` for slot labellings.
* `lower_side_labels`: the lower side `(n - M_b)(n - 2m) b ≤ b Σ_ℓ |S_ℓ|` for one run; it is shared
  with the trace-class form (`isoperimetry_trace`, `CutTrace.lean`).
* `isoperimetry_res_on` (a set of co-entropy `mc`) and its cases `_res`, `isoperimetry`,
  `_touch`.
-/

namespace Transpose.Tape.Impl

open Transpose

variable {M : TM}

/-- **The Slot Cut Bound**, for a single union of slots. -/
theorem slot_cut_bound {n b T r : ℕ} (hobl : ObliviousOn M (matrixInputs n b) T)
    (hcorr : Transposes M n b) {w₀ : List Bool} (hw₀ : w₀ ∈ matrixInputs n b) (hr : 1 ≤ r)
    (U : Set ℕ) :
    b * (cutPairs M w₀ n b (slotSteps r U T)).card ≤
      (memBoundaries U (numSlots r T)).card * Nat.clog 2 (M.q + 1) +
        r * Nat.clog 2 (M.g + 1) *
          ((∑ t : Fin M.k,
            (chordsInto (pairRes r (fun τ => workTraj M w₀ τ t) T) U (numSlots r T)).card) +
            3 * M.k * (memBoundaries U (numSlots r T)).card) := by
  have hJ : ∀ τ ∈ slotSteps r U T, τ < T := fun τ hτ => (mem_slotSteps.1 hτ).1
  have h1 := cut_bound_bits hobl hcorr hw₀ hJ
  rw [entryPoints_slotSteps_card hr] at h1
  have h2 := charging_bound M w₀ hr _ (fun t => pairRes_admissible (unitSteps_workTraj M w₀ t) hr T) U
  calc b * (cutPairs M w₀ n b (slotSteps r U T)).card
      ≤ (memBoundaries U (numSlots r T)).card * Nat.clog 2 (M.q + 1) +
          (entryCells (workTraj M w₀) (slotSteps r U T)).card * Nat.clog 2 (M.g + 1) := h1
    _ ≤ (memBoundaries U (numSlots r T)).card * Nat.clog 2 (M.q + 1) +
          (r * (∑ t : Fin M.k,
            (chordsInto (pairRes r (fun τ => workTraj M w₀ τ t) T) U (numSlots r T)).card) +
            3 * M.k * r * (memBoundaries U (numSlots r T)).card) * Nat.clog 2 (M.g + 1) :=
        Nat.add_le_add_left (Nat.mul_le_mul_right _ h2) _
    _ = _ := by ring

/-! ### Sums over the label classes of a slot labelling -/

theorem mem_crossChords {R : ℕ → Finset ℤ} {lab : ℕ → ℕ} {N z : ℕ} {β : ℤ} :
    (z, β) ∈ crossChords R lab N ↔ z < N ∧ β ∈ R z ∧ ∃ x, lab x ≠ lab z ∧ IsChord R β x z := by
  classical
  simp only [crossChords, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_range,
    Finset.mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨z', h1, β', ⟨h3, h4⟩, rfl, rfl⟩; exact ⟨h1, h3, h4⟩
  · rintro ⟨h1, h3, h4⟩; exact ⟨z, h1, β, ⟨h3, h4⟩, rfl, rfl⟩

/-- `Σ_ℓ μ(U_ℓ) ≤ M_b` (in fact equal). -/
theorem sum_memBoundaries_le (lab : ℕ → ℕ) (N : ℕ) (s : Finset ℕ) :
    ∑ ℓ ∈ s, (memBoundaries {y | lab y = ℓ} N).card ≤ labelChanges lab N := by
  classical
  rw [← Finset.card_biUnion]
  · apply Finset.card_le_card
    intro z hz
    simp only [Finset.mem_biUnion, mem_memBoundaries, Set.mem_ofPred_eq] at hz
    obtain ⟨ℓ, -, hzN, hzℓ, hz1, hzprev⟩ := hz
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨hzN, hz1, by rw [hzℓ]; exact Ne.symm hzprev⟩
  · intro ℓ _ ℓ' _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro z hz hz'
    rw [mem_memBoundaries] at hz hz'
    exact hne (hz.2.1.symm.trans hz'.2.1)

/-- `Σ_ℓ χ(U_ℓ) ≤ χ_cross`, for one tape. -/
theorem sum_chordsInto_le (R : ℕ → Finset ℤ) (lab : ℕ → ℕ) (N : ℕ) (s : Finset ℕ) :
    ∑ ℓ ∈ s, (chordsInto R {y | lab y = ℓ} N).card ≤ (crossChords R lab N).card := by
  classical
  rw [← Finset.card_biUnion]
  · apply Finset.card_le_card
    rintro ⟨z, β⟩ hz
    simp only [Finset.mem_biUnion, mem_chordsInto, Set.mem_ofPred_eq] at hz
    obtain ⟨ℓ, -, hzN, hzℓ, hβ, x, hx, hch⟩ := hz
    rw [mem_crossChords]
    exact ⟨hzN, hβ, x, by rw [hzℓ]; exact hx, hch⟩
  · intro ℓ _ ℓ' _ hne
    rw [Function.onFun, Finset.disjoint_left]
    rintro ⟨z, β⟩ hz hz'
    rw [mem_chordsInto] at hz hz'
    exact hne (hz.2.1.symm.trans hz'.2.1)

theorem labelPart_subset {r : ℕ} (lab : ℕ → ℕ) (T ℓ : ℕ) :
    ∀ τ ∈ labelPart r lab T ℓ, τ < T := fun _ hτ => (mem_slotSteps.1 hτ).1

/-- **The entry data of the label classes of a slot labelling**, for any admissible residency:
`Σ_ℓ e₁(J_ℓ) ≤ M_b` and `Σ_ℓ e₂(J_ℓ) ≤ r (c k M_b + χ_cross)`. -/
theorem sum_entry_labelPart_le {w₀ : List Bool} {T r c : ℕ} (hr : 1 ≤ r)
    (R : Fin M.k → ℕ → Finset ℤ) (hR : ∀ t, AdmissibleRes r (fun τ => workTraj M w₀ τ t) T (R t) c)
    (lab : ℕ → ℕ) (s : Finset ℕ) :
    ∑ ℓ ∈ s, (entryPoints (labelPart r lab T ℓ)).card ≤ labelChanges lab (numSlots r T) ∧
    ∑ ℓ ∈ s, (entryCells (workTraj M w₀) (labelPart r lab T ℓ)).card ≤
      r * (c * M.k * labelChanges lab (numSlots r T) +
        ∑ t : Fin M.k, (crossChords (R t) lab (numSlots r T)).card) := by
  set N := numSlots r T
  refine ⟨le_of_eq_of_le (Finset.sum_congr rfl fun ℓ _ => entryPoints_slotSteps_card hr _ T)
    (sum_memBoundaries_le lab N s), ?_⟩
  calc ∑ ℓ ∈ s, (entryCells (workTraj M w₀) (labelPart r lab T ℓ)).card
      ≤ ∑ ℓ ∈ s, ∑ t : Fin M.k, r * ((chordsInto (R t) {y | lab y = ℓ} N).card +
          c * (memBoundaries {y | lab y = ℓ} N).card) := by
        refine Finset.sum_le_sum fun ℓ _ => ?_
        rw [labelPart, entryCells_slotSteps_card]
        exact Finset.sum_le_sum fun t _ => entryTimes_card_le hr (hR t) _
    _ = r * (∑ t : Fin M.k, ∑ ℓ ∈ s, (chordsInto (R t) {y | lab y = ℓ} N).card +
          c * M.k * ∑ ℓ ∈ s, (memBoundaries {y | lab y = ℓ} N).card) := by
        simp only [Nat.mul_add, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, smul_eq_mul]
        rw [Finset.sum_comm]; ring
    _ ≤ r * (∑ t : Fin M.k, (crossChords (R t) lab N).card + c * M.k * labelChanges lab N) :=
        Nat.mul_le_mul_left _ (Nat.add_le_add
          (Finset.sum_le_sum fun t _ => sum_chordsInto_le _ lab N s)
          (Nat.mul_le_mul_left _ (sum_memBoundaries_le lab N s)))
    _ = _ := by ring

/-- **The Slot Cut Bound, partition form with `M_b`, any admissible residency.** -/
theorem slot_cut_bound_partition {n b T r c : ℕ}
    (hobl : ObliviousOn M (matrixInputs n b) T) (hcorr : Transposes M n b) {w₀ : List Bool}
    (hw₀ : w₀ ∈ matrixInputs n b) (hr : 1 ≤ r)
    (R : Fin M.k → ℕ → Finset ℤ) (hR : ∀ t, AdmissibleRes r (fun τ => workTraj M w₀ τ t) T (R t) c)
    (lab : ℕ → ℕ) :
    b * (∑ ℓ ∈ (Finset.range (numSlots r T)).image lab,
        (cutPairs M w₀ n b (labelPart r lab T ℓ)).card) ≤
      labelChanges lab (numSlots r T) *
          (Nat.clog 2 (M.q + 1) + c * M.k * r * Nat.clog 2 (M.g + 1)) +
        r * Nat.clog 2 (M.g + 1) * ∑ t : Fin M.k, (crossChords (R t) lab (numSlots r T)).card := by
  obtain ⟨he1, he2⟩ := sum_entry_labelPart_le hr R hR lab ((Finset.range (numSlots r T)).image lab)
  refine (cut_bound_sum_bits hobl hcorr hw₀ _ (labelPart r lab T)
    (fun ℓ _ => labelPart_subset lab T ℓ)).trans ?_
  refine (Nat.add_le_add (Nat.mul_le_mul_right _ he1) (Nat.mul_le_mul_right _ he2)).trans_eq ?_
  ring

/-- **`σ ≤ M_b` for slot labellings, for one run** with output at least `n²b` bits by time `T`. -/
theorem uncovered_cols_le_slots_len {n b T r : ℕ} (hb : 1 ≤ b) {w₀ : List Bool}
    (hlenT : n * n * b ≤ (run M w₀ T).outRev.length) (hr : 1 ≤ r) (lab : ℕ → ℕ) :
    n - (((Finset.range (numSlots r T)).image lab).biUnion (fun ℓ =>
        snkCols M w₀ n b (labelPart r lab T ℓ))).card ≤ labelChanges lab (numSlots r T) := by
  classical
  set lab' : ℕ → ℕ := fun τ => lab (τ / r)
  have hstep := uncovered_cols_le_len hb hlenT lab'
  -- the two coverings agree
  have himg : (Finset.range T).image lab' = (Finset.range (numSlots r T)).image lab := by
    ext ℓ
    simp only [Finset.mem_image, Finset.mem_range, lab']
    constructor
    · rintro ⟨τ, hτ, rfl⟩; exact ⟨τ / r, div_lt_numSlots hr hτ, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y * r, (numSlots_spec hr).1 hy, by rw [Nat.mul_div_cancel y (by omega)]⟩
  have hpart : ∀ ℓ, (Finset.range T).filter (fun τ => lab' τ = ℓ) = labelPart r lab T ℓ := by
    intro ℓ; ext τ
    simp only [Finset.mem_filter, Finset.mem_range, labelPart, mem_slotSteps, Set.mem_ofPred_eq,
      lab']
  rw [himg] at hstep
  simp only [hpart] at hstep
  refine le_trans hstep ?_
  -- step label changes inject into slot label changes
  unfold labelChanges
  apply Finset.card_le_card_of_injOn (· / r)
  · intro τ hτ
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq, lab'] at hτ
    obtain ⟨hτT, hτ1, hlab⟩ := hτ
    have hne : (τ - 1) / r ≠ τ / r := fun e => hlab (by rw [e])
    obtain ⟨-, hdiv, hq⟩ := slot_start_of_div_ne hr hτ1 hne
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq]
    exact ⟨div_lt_numSlots hr hτT, hq, by rw [← hdiv]; exact hlab⟩
  · intro τ hτ τ' hτ' he
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq, lab'] at hτ hτ'
    have hne : (τ - 1) / r ≠ τ / r := fun e => hτ.2.2 (by rw [e])
    have hne' : (τ' - 1) / r ≠ τ' / r := fun e => hτ'.2.2 (by rw [e])
    have a := (slot_start_of_div_ne hr hτ.2.1 hne).1
    have a' := (slot_start_of_div_ne hr hτ'.2.1 hne').1
    simp only at he
    rw [← a, ← a', he]

/-- **The Slot Cut Bound, `σ ≤ M_b` for slot labellings.** -/
theorem uncovered_cols_le_slots {n b T r : ℕ} (hb : 1 ≤ b)
    (hobl : ObliviousOn M (matrixInputs n b) T) (hcorr : Transposes M n b) {w₀ : List Bool}
    (hw₀ : w₀ ∈ matrixInputs n b) (hr : 1 ≤ r) (lab : ℕ → ℕ) :
    n - (((Finset.range (numSlots r T)).image lab).biUnion (fun ℓ =>
        snkCols M w₀ n b (labelPart r lab T ℓ))).card ≤ labelChanges lab (numSlots r T) := by
  refine uncovered_cols_le_slots_len hb (le_of_eq ?_) hr lab
  obtain ⟨A₀, rfl⟩ := hw₀
  rw [← List.length_reverse, output_eq_of_haltsAt hcorr A₀ (hobl.1 _ ⟨A₀, rfl⟩), length_encode]

/-! ### Discrete Isoperimetry (the finitary discrete isoperimetric inequality) -/

/-- The number of labels used on `[0, N)` is at most one more than the number of label changes. -/
theorem card_image_lab_le (lab : ℕ → ℕ) (N : ℕ) :
    ((Finset.range N).image lab).card ≤ labelChanges lab N + 1 := by
  classical
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.range_add_one, Finset.image_insert]
    have hch : labelChanges lab (N + 1) = labelChanges lab N +
        (if 1 ≤ N ∧ lab N ≠ lab (N - 1) then 1 else 0) := by
      unfold labelChanges
      rw [Finset.range_add_one, Finset.filter_insert]
      split_ifs with h
      · rw [Finset.card_insert_of_notMem (by simp)]
      · rfl
    by_cases hc : 1 ≤ N ∧ lab N ≠ lab (N - 1)
    · rw [hch, ite_eq_left hc]
      exact le_trans (Finset.card_insert_le _ _) (by omega)
    · rw [hch, ite_eq_right hc, Nat.add_zero]
      by_cases hN : N = 0
      · subst hN; simp
      · have : lab N ∈ (Finset.range N).image lab := by
          push Not at hc
          rw [hc (by omega)]
          exact Finset.mem_image.2 ⟨N - 1, Finset.mem_range.2 (by omega), rfl⟩
        rw [Finset.insert_eq_of_mem this]
        exact ih


/-- **The lower side of Discrete Isoperimetry, for one run** with at least `n²b` output bits by
time `T`: `(n - M_b)(n - 2m) b ≤ b Σ_ℓ |S_{J_ℓ}|` over the label classes, when `r ≤ n b` and every
label class has at most `m` slots. -/
theorem lower_side_labels {w₀ : List Bool} {n b T r : ℕ}
    (hlenT : n * n * b ≤ (run M w₀ T).outRev.length) (hr : 1 ≤ r) (hrnb : r ≤ n * b)
    (lab : ℕ → ℕ) (m : ℕ)
    (hm : ∀ ℓ, ((Finset.range (numSlots r T)).filter (fun y => lab y = ℓ)).card ≤ m) :
    (n - labelChanges lab (numSlots r T)) * (n - 2 * m) * b ≤
      b * ∑ ℓ ∈ (Finset.range (numSlots r T)).image lab,
        (cutPairs M w₀ n b (labelPart r lab T ℓ)).card := by
  classical
  set s := (Finset.range (numSlots r T)).image lab
  rcases Nat.eq_zero_or_pos b with hb0 | hbpos
  · rw [hb0]; simp
  have hrows : ∀ ℓ ∈ s, (srcRows M w₀ n b (labelPart r lab T ℓ)).card ≤ 2 * m := fun ℓ _ =>
    (srcRows_slotSteps_card_le M w₀ hr hrnb _ T).trans (Nat.mul_le_mul_left _
      ((le_of_eq (by congr 1; ext y; simp)).trans (hm ℓ)))
  have hcov : n - (s.biUnion (fun ℓ => snkCols M w₀ n b (labelPart r lab T ℓ))).card ≤
      labelChanges lab (numSlots r T) := uncovered_cols_le_slots_len hbpos hlenT hr lab
  have hpairs := sum_cutPairs_ge M w₀ n b s (labelPart r lab T) (2 * m) hrows
  calc (n - labelChanges lab (numSlots r T)) * (n - 2 * m) * b
      ≤ (s.biUnion (fun ℓ => snkCols M w₀ n b (labelPart r lab T ℓ))).card * (n - 2 * m) * b := by
        apply Nat.mul_le_mul_right; apply Nat.mul_le_mul_right; omega
    _ ≤ _ := by rw [Nat.mul_comm b]; exact Nat.mul_le_mul_right _ hpairs

/-- **Discrete Isoperimetry on a set `W` of co-entropy `≤ mc`** (robust form): the machine is
oblivious and correct only on `W`; each of the `M_b + 1` label classes pays `mc`. -/
theorem isoperimetry_res_on {n b T r c : ℕ} {W : Set (List Bool)}
    (hobl : ObliviousOn M W T) (hcorr : ClassCorrect M n b T W) {w₀ : List Bool}
    (hw₀ : w₀ ∈ W) {mc : ℕ} (hco : 2 ^ (n * n * b) ≤ 2 ^ mc * W.ncard)
    (hr : 1 ≤ r) (hrnb : r ≤ n * b)
    (R : Fin M.k → ℕ → Finset ℤ)
    (hR : ∀ t, AdmissibleRes r (fun τ => workTraj M w₀ τ t) T (R t) c)
    (lab : ℕ → ℕ) (m : ℕ)
    (hm : ∀ ℓ, ((Finset.range (numSlots r T)).filter (fun y => lab y = ℓ)).card ≤ m) :
    2 ^ ((n - labelChanges lab (numSlots r T)) * (n - 2 * m) * b) ≤
      2 ^ ((labelChanges lab (numSlots r T) + 1) * mc) *
      ((M.q + 1) ^ labelChanges lab (numSlots r T) *
        (M.g + 1) ^ (r * (c * M.k * labelChanges lab (numSlots r T) +
          ∑ t : Fin M.k, (crossChords (R t) lab (numSlots r T)).card))) := by
  set s := (Finset.range (numSlots r T)).image lab
  obtain ⟨he1, he2⟩ := sum_entry_labelPart_le hr R hR lab s
  have hlow := lower_side_labels (le_of_eq (outLen_of_classCorrect hcorr hw₀).symm) hr hrnb lab m hm
  rw [Finset.mul_sum] at hlow
  calc _ ≤ 2 ^ (∑ ℓ ∈ s, (cutSet M w₀ n b (labelPart r lab T ℓ)).card) :=
        Nat.pow_le_pow_right (by norm_num) (hlow.trans (Finset.sum_le_sum fun ℓ _ => by
          rw [Nat.mul_comm]; exact cutPairs_card_mul_le M w₀ n b _))
    _ ≤ _ := cut_bound_sum_on hobl hcorr hw₀ hco s (labelPart r lab T)
        (fun ℓ _ => labelPart_subset lab T ℓ)
    _ ≤ _ := Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num)
          (Nat.mul_le_mul_right _ (card_image_lab_le lab _)))
        (Nat.mul_le_mul (Nat.pow_le_pow_right (by omega) he1) (Nat.pow_le_pow_right (by omega) he2))

/-- **Discrete Isoperimetry, any admissible residency**: the case `W` = all matrix inputs, `mc = 0`
of `isoperimetry_res_on`. -/
theorem isoperimetry_res {n b T r c : ℕ}
    (hobl : ObliviousOn M (matrixInputs n b) T) (hcorr : Transposes M n b) {w₀ : List Bool}
    (hw₀ : w₀ ∈ matrixInputs n b) (hr : 1 ≤ r) (hrnb : r ≤ n * b)
    (R : Fin M.k → ℕ → Finset ℤ)
    (hR : ∀ t, AdmissibleRes r (fun τ => workTraj M w₀ τ t) T (R t) c)
    (lab : ℕ → ℕ) (m : ℕ)
    (hm : ∀ ℓ, ((Finset.range (numSlots r T)).filter (fun y => lab y = ℓ)).card ≤ m) :
    2 ^ ((n - labelChanges lab (numSlots r T)) * (n - 2 * m) * b) ≤
      (M.q + 1) ^ labelChanges lab (numSlots r T) *
        (M.g + 1) ^ (r * (c * M.k * labelChanges lab (numSlots r T) +
          ∑ t : Fin M.k, (crossChords (R t) lab (numSlots r T)).card)) := by
  have h := isoperimetry_res_on hobl
    (fun w hw => correct_of_transposes hcorr hw (hobl.1 w hw)) hw₀ (mc := 0)
    (by rw [ncard_matrixInputs, pow_zero, one_mul]) hr hrnb R hR lab m hm
  simpa using h

theorem isoperimetry {n b T r : ℕ} (hobl : ObliviousOn M (matrixInputs n b) T)
    (hcorr : Transposes M n b) {w₀ : List Bool} (hw₀ : w₀ ∈ matrixInputs n b)
    (hr : 1 ≤ r) (hrnb : r ≤ n * b) (lab : ℕ → ℕ) (m : ℕ)
    (hm : ∀ ℓ, ((Finset.range (numSlots r T)).filter (fun y => lab y = ℓ)).card ≤ m) :
    2 ^ ((n - labelChanges lab (numSlots r T)) * (n - 2 * m) * b) ≤
      (M.q + 1) ^ labelChanges lab (numSlots r T) *
        (M.g + 1) ^ (r * (3 * M.k * labelChanges lab (numSlots r T) +
          ∑ t : Fin M.k,
            (crossChords (pairRes r (fun τ => workTraj M w₀ τ t) T) lab (numSlots r T)).card)) :=
  isoperimetry_res hobl hcorr hw₀ hr hrnb _
    (fun t => pairRes_admissible (unitSteps_workTraj M w₀ t) hr T) lab m hm

theorem isoperimetry_touch {n b T r : ℕ}
    (hobl : ObliviousOn M (matrixInputs n b) T)
    (hcorr : Transposes M n b) {w₀ : List Bool} (hw₀ : w₀ ∈ matrixInputs n b)
    (hr : 1 ≤ r) (hrnb : r ≤ n * b) (lab : ℕ → ℕ) (m : ℕ)
    (hm : ∀ ℓ, ((Finset.range (numSlots r T)).filter (fun y => lab y = ℓ)).card ≤ m) :
    2 ^ ((n - labelChanges lab (numSlots r T)) * (n - 2 * m) * b) ≤
      (M.q + 1) ^ labelChanges lab (numSlots r T) *
        (M.g + 1) ^ (r * (2 * M.k * labelChanges lab (numSlots r T) +
          ∑ t : Fin M.k,
            (crossChords (touchRes r (fun τ => workTraj M w₀ τ t) T) lab (numSlots r T)).card)) :=
  isoperimetry_res hobl hcorr hw₀ hr hrnb _
    (fun t => (touchRes_admissible (unitSteps_workTraj M w₀ t) hr T).1) lab m hm

end Transpose.Tape.Impl
