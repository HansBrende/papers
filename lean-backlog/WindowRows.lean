import MergeDepth.FieldPruning

/-!
# Input rows within windows and ordered output-row spans

The input statement uses the actual unit-speed input head and `readPos`.
The output statement derives disjoint span interiors from the actual ordered
append list; no density or contiguity of output times is assumed.
-/

namespace LeanBacklog.WindowRows

open Finset BoundedNesting MergeDepth
open scoped BigOperators

/-- A set of natural positions of diameter at most one row width meets at
most two consecutive row quotients. -/
theorem card_image_div_le_two {S : Finset ℕ} {h : ℕ} (hh : 0 < h)
    (hdiam : ∀ p ∈ S, ∀ q ∈ S, q ≤ p + h) :
    (S.image (fun p => p / h)).card ≤ 2 := by
  by_cases hS : S.Nonempty
  · let p := S.min' hS
    have hp : p ∈ S := min'_mem _ hS
    have hsub : S.image (fun q => q / h) ⊆ Icc (p / h) (p / h + 1) := by
      intro j hj
      obtain ⟨q, hq, rfl⟩ := mem_image.mp hj
      apply mem_Icc.mpr
      constructor
      · exact Nat.div_le_div_right (min'_le _ _ hq)
      · have hle := Nat.div_le_div_right (c := h) (hdiam p hp q hq)
        simpa only [Nat.add_div_right _ hh] using hle
    have hc := card_le_card hsub
    simp only [Nat.card_Icc] at hc
    omega
  · simp [not_nonempty_iff_eq_empty.mp hS]

/-- The actual in-input positions read in a whole time window. Positions
outside the finite input are absent, as required by `readPos`. -/
def inputWindowPositions {k : ℕ} (τ : Trace k) (L h i : ℕ) : Finset (Fin L) :=
  (Ico (i * h) ((i + 1) * h)).biUnion fun t => (readPos τ L t).toFinset

def inputWindowRows {k : ℕ} (τ : Trace k) (L h i : ℕ) : Finset ℕ :=
  (inputWindowPositions τ L h i).image fun p => p.val / h

theorem mem_inputWindowPositions {k L h i : ℕ} {τ : Trace k} {p : Fin L} :
    p ∈ inputWindowPositions τ L h i ↔
      ∃ t, i * h ≤ t ∧ t < (i + 1) * h ∧ readPos τ L t = some p := by
  simp [inputWindowPositions, and_assoc, Option.mem_def]

theorem inputWindowPositions_diameter {k L h i : ℕ} (τ : Trace k)
    {p q : Fin L} (hp : p ∈ inputWindowPositions τ L h i)
    (hq : q ∈ inputWindowPositions τ L h i) : q.val ≤ p.val + h := by
  obtain ⟨s, hs₁, hs₂, hsread⟩ := mem_inputWindowPositions.mp hp
  obtain ⟨t, ht₁, ht₂, htread⟩ := mem_inputWindowPositions.mp hq
  have hspos := readPos_eq_some_iff.mp hsread
  have htpos := readPos_eq_some_iff.mp htread
  have hx : IsWalk τ.input := τ.abs_input_succ_sub_le
  simp only [Nat.add_mul, Nat.one_mul] at hs₂ ht₂
  rcases le_total s t with hst | hts
  · have hlip := hx.lip hst
    omega
  · have hlip := hx.lip hts
    omega

theorem card_inputWindowRows_le_two {k : ℕ} (τ : Trace k) (L h i : ℕ)
    (hh : 0 < h) : (inputWindowRows τ L h i).card ≤ 2 := by
  have hdiam : ∀ p ∈ (inputWindowPositions τ L h i).image Fin.val,
      ∀ q ∈ (inputWindowPositions τ L h i).image Fin.val, q ≤ p + h := by
    intro p hp q hq
    obtain ⟨p', hp', hpp⟩ := mem_image.mp hp
    obtain ⟨q', hq', hqq⟩ := mem_image.mp hq
    rw [← hpp, ← hqq]
    exact inputWindowPositions_diameter τ hp' hq'
  simpa only [inputWindowRows, image_image, Function.comp_def] using
    card_image_div_le_two hh hdiam

/-- The first-to-last span of window numbers occupied by one block of
`h` values of an increasing sequence. Gaps inside the sequence are kept. -/
def rowWindowSpan (a : ℕ → ℕ) (h r : ℕ) : Finset ℕ :=
  Icc (a (r * h) / h) (a ((r + 1) * h - 1) / h)

def badRowSpans (a : ℕ → ℕ) (d h M : ℕ) : Finset (Fin d) :=
  univ.filter fun r => M + 1 < (rowWindowSpan a h r.val).card

/-- Charging the disjoint interior of each long ordered span. The two
endpoint windows may be shared, which is why they are not charged. -/
theorem bad_ordered_spans_count {d N : ℕ} (first last : Fin d → ℕ)
    (hordered : ∀ r s, r < s → last r ≤ first s)
    (hlast : ∀ r, last r < N) (M : ℕ) :
    M * (univ.filter fun r => M + 1 < (Icc (first r) (last r)).card).card ≤ N := by
  let bad : Finset (Fin d) := univ.filter fun r =>
    M + 1 < (Icc (first r) (last r)).card
  let inner : Fin d → Finset ℕ := fun r => Ioo (first r) (last r)
  have hdisjoint : (bad : Set (Fin d)).PairwiseDisjoint inner := by
    intro r hr s hs hrs
    apply disjoint_left.mpr
    intro j hjr hjs
    have hjr' := mem_Ioo.mp hjr
    have hjs' := mem_Ioo.mp hjs
    rcases lt_or_gt_of_ne hrs with hlt | hgt
    · have := hordered r s hlt
      omega
    · have := hordered s r hgt
      omega
  have hsub : bad.biUnion inner ⊆ range N := by
    intro j hj
    obtain ⟨r, hr, hj⟩ := mem_biUnion.mp hj
    exact mem_range.mpr ((mem_Ioo.mp hj).2.trans (hlast r))
  have hsum : (∑ r ∈ bad, (inner r).card) ≤ N := by
    rw [← card_biUnion hdisjoint]
    exact (card_le_card hsub).trans_eq (card_range N)
  have hcharge : M * bad.card ≤ ∑ r ∈ bad, (inner r).card := by
    calc
      M * bad.card = ∑ _r ∈ bad, M := by simp [Nat.mul_comm]
      _ ≤ _ := by
        apply sum_le_sum
        intro r hr
        have hb := (mem_filter.mp hr).2
        simp only [Nat.card_Icc] at hb
        simp only [inner, Nat.card_Ioo]
        omega
  exact hcharge.trans hsum

theorem row_first_lt {d h : ℕ} (hh : 0 < h) (r : Fin d) : r.val * h < d * h :=
  Nat.mul_lt_mul_of_pos_right r.isLt hh

theorem row_last_lt {d h : ℕ} (hh : 0 < h) (r : Fin d) :
    (r.val + 1) * h - 1 < d * h := by
  have hle : (r.val + 1) * h ≤ d * h := Nat.mul_le_mul_right h (by omega)
  have hpos : 0 < (r.val + 1) * h := Nat.mul_pos (by omega) hh
  omega

theorem div_lt_windowCount {h t T : ℕ} (hh : 0 < h) (ht : t < T) :
    t / h < (T + h - 1) / h := by
  have hle : t + h ≤ T + h - 1 := by omega
  have hdiv := Nat.div_le_div_right (c := h) hle
  rw [Nat.add_div_right _ hh] at hdiv
  omega

/-- Sparse append times are allowed: only their order and finite horizon
are used. A bad row pays `M` distinct complete interior time windows. -/
theorem badRowSpans_count {d h T : ℕ} (a : ℕ → ℕ) (hh : 0 < h)
    (hmono : StrictMonoOn a (Set.Iio (d * h)))
    (hT : ∀ j < d * h, a j < T) (M : ℕ) :
    M * (badRowSpans a d h M).card ≤ (T + h - 1) / h := by
  apply bad_ordered_spans_count
    (fun r : Fin d => a (r.val * h) / h)
    (fun r : Fin d => a ((r.val + 1) * h - 1) / h)
  · intro r s hrs
    have hle : (r.val + 1) * h ≤ s.val * h :=
      Nat.mul_le_mul_right h (by exact_mod_cast hrs)
    have hpos : 0 < (r.val + 1) * h := Nat.mul_pos (by omega) hh
    have hidx : (r.val + 1) * h - 1 < s.val * h := by omega
    exact Nat.div_le_div_right (hmono (row_last_lt hh r) (row_first_lt hh s) hidx).le
  · intro r
    exact div_lt_windowCount hh (hT _ (row_last_lt hh r))

theorem mem_rowWindowSpan {d h : ℕ} (a : ℕ → ℕ) (hh : 0 < h)
    (hmono : StrictMonoOn a (Set.Iio (d * h))) (r : Fin d) {j : ℕ}
    (hj₁ : r.val * h ≤ j) (hj₂ : j < (r.val + 1) * h) :
    a j / h ∈ rowWindowSpan a h r.val := by
  have hjd : j < d * h := by
    have := Nat.mul_le_mul_right h (show r.val + 1 ≤ d by omega)
    omega
  have hlo := hmono.monotoneOn (row_first_lt hh r) hjd hj₁
  have hhi := hmono.monotoneOn hjd (row_last_lt hh r)
    (show j ≤ (r.val + 1) * h - 1 by omega)
  exact mem_Icc.mpr ⟨Nat.div_le_div_right hlo, Nat.div_le_div_right hhi⟩

theorem rowWindowSpan_card_le_of_not_bad {a : ℕ → ℕ} {d h M : ℕ}
    {r : Fin d} (hr : r ∉ badRowSpans a d h M) :
    (rowWindowSpan a h r.val).card ≤ M + 1 := by
  simpa [badRowSpans] using hr

/-- Native wrapper. Even a prefix containing MORE than `d*h` appends is
allowed; only its first `d` complete physical output rows are counted. -/
theorem appendTime_badRowSpans_count {k d h T : ℕ} (τ : Trace k) (hh : 0 < h)
    (happ : d * h ≤ (appendList τ T).length) (M : ℕ) :
    M * (badRowSpans (appendTime τ T) d h M).card ≤ (T + h - 1) / h := by
  apply badRowSpans_count (appendTime τ T) hh
  · exact (appendTime_strictMonoOn τ T).mono (fun _ hj => lt_of_lt_of_le hj happ)
  · intro j hj
    exact appendTime_lt τ T (lt_of_lt_of_le hj happ)

theorem appendTime_mem_rowWindowSpan {k d h T : ℕ} (τ : Trace k) (hh : 0 < h)
    (happ : d * h ≤ (appendList τ T).length) (r : Fin d) {j : ℕ}
    (hj : j / h = r.val) :
    appendTime τ T j / h ∈ rowWindowSpan (appendTime τ T) h r.val := by
  apply mem_rowWindowSpan (appendTime τ T) hh
    ((appendTime_strictMonoOn τ T).mono (fun _ hj => lt_of_lt_of_le hj happ)) r
  · have := Nat.mul_div_le j h
    simpa [hj, Nat.mul_comm] using this
  · have := Nat.mod_lt j hh
    have := Nat.mod_add_div j h
    nlinarith

#print axioms card_inputWindowRows_le_two
#print axioms badRowSpans_count
#print axioms appendTime_badRowSpans_count
#print axioms appendTime_mem_rowWindowSpan

end LeanBacklog.WindowRows
