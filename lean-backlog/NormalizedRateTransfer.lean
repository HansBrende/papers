import NormalizedCodeTransfer
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Normalized two-sided rates and the native crux

Restricting two-sided helper relations to symmetric reflexive relations does
not change the common asymptotic rate over all fixed windows. A fixed reverse
degree cutoff is chosen after the requested slack, before the dimension or
alphabet. The normalization payment is absorbed into that slack.

The positive-deficit consequences reuse the proved two-sided transfer; the
capacity hypotheses themselves remain open. No capacity bound is asserted.
-/

namespace LeanBacklog.RowSpread

open Finset BoundedNesting MergeDepth BoundedStackDepth Transpose

universe u

/-- Increasing the exponent preserves a two-sided cardinality bound over
any nonempty finite alphabet, including a one-symbol alphabet. -/
theorem TwoSidedWholeRowCardinalityBound.mono {d w : ℕ} {α : Type u} [Fintype α]
    {a b : ℝ} (h : TwoSidedWholeRowCardinalityBound d w α a)
    (hα : 0 < Fintype.card α) (hab : a ≤ b) :
    TwoSidedWholeRowCardinalityBound d w α b := by
  intro ρ C hρ hC
  exact (h ρ C hρ hC).trans (Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast (show 1 ≤ Fintype.card α by omega)) hab)

/-- At each fixed window, the normalization payment can be made arbitrarily
small by a fixed cutoff. It has no dependence on dimension or alphabet. -/
theorem exists_symmetryPayment_lt (w : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ R : ℕ, symmetryPayment w R < η := by
  obtain ⟨R, hR⟩ := exists_nat_gt (2 * (w : ℝ) / η)
  refine ⟨R, ?_⟩
  unfold symmetryPayment
  rw [div_lt_iff₀ (by positivity)]
  have h := (div_lt_iff₀ hη).mp hR
  nlinarith

/-- Common normalized two-sided rate, uniformly over finite alphabets. -/
def UniformNormalizedTwoSidedWholeRowRate (rate : ℝ) : Prop :=
  ∀ (w : ℕ) (η : ℝ), 0 < η → ∃ d₀ : ℕ, ∀ d ≥ d₀,
    ∀ (α : Type u) [Fintype α], 2 ≤ Fintype.card α →
      NormalizedTwoSidedWholeRowCardinalityBound d w α ((rate + η) * (d : ℝ) ^ 2)

/-- The same target at the canonical, dimension-dependent bit alphabets. -/
def UniformNormalizedTwoSidedWholeRowRateCanonicalBits (rate : ℝ) : Prop :=
  ∀ (w : ℕ) (η : ℝ), 0 < η → ∃ d₀ : ℕ, ∀ d ≥ d₀,
    NormalizedTwoSidedWholeRowCardinalityBound d w (Fin (entryBits d) → Bool)
      ((rate + η) * (d : ℝ) ^ 2)

theorem UniformTwoSidedWholeRowRate.normalized {rate : ℝ}
    (h : UniformTwoSidedWholeRowRate.{u} rate) :
    UniformNormalizedTwoSidedWholeRowRate.{u} rate := by
  intro w η hη
  obtain ⟨d₀, hd₀⟩ := h w η hη
  exact ⟨d₀, fun d hd α _ hα => (hd₀ d hd α hα).normalized⟩

theorem UniformTwoSidedWholeRowRateCanonicalBits.normalized {rate : ℝ}
    (h : UniformTwoSidedWholeRowRateCanonicalBits rate) :
    UniformNormalizedTwoSidedWholeRowRateCanonicalBits rate := by
  intro w η hη
  obtain ⟨d₀, hd₀⟩ := h w η hη
  exact ⟨d₀, fun d hd => (hd₀ d hd).normalized⟩

/-- The rate itself is unchanged; only the window and dimension threshold
used for a requested slack change. -/
theorem UniformNormalizedTwoSidedWholeRowRate.twoSided {rate : ℝ}
    (h : UniformNormalizedTwoSidedWholeRowRate.{u} rate) :
    UniformTwoSidedWholeRowRate.{u} rate := by
  intro w η hη
  obtain ⟨R, hR⟩ := exists_symmetryPayment_lt w (show 0 < η / 2 by positivity)
  obtain ⟨d₀, hd₀⟩ := h (w + R + 1) (η / 2) (by positivity)
  refine ⟨d₀, fun d hd α _ hα => ?_⟩
  apply ((hd₀ d hd α hα).twoSided (R := R) (by omega)).mono (by omega)
  calc
    (rate + η / 2) * (d : ℝ) ^ 2 + symmetryPayment w R * (d : ℝ) ^ 2 =
        (rate + η / 2 + symmetryPayment w R) * (d : ℝ) ^ 2 := by ring
    _ ≤ (rate + η) * (d : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)

theorem UniformNormalizedTwoSidedWholeRowRateCanonicalBits.twoSided {rate : ℝ}
    (h : UniformNormalizedTwoSidedWholeRowRateCanonicalBits rate) :
    UniformTwoSidedWholeRowRateCanonicalBits rate := by
  intro w η hη
  obtain ⟨R, hR⟩ := exists_symmetryPayment_lt w (show 0 < η / 2 by positivity)
  obtain ⟨d₀, hd₀⟩ := h (w + R + 1) (η / 2) (by positivity)
  refine ⟨d₀, fun d hd => ?_⟩
  apply ((hd₀ d hd).twoSided (R := R) (by simp)).mono (by simp)
  calc
    (rate + η / 2) * (d : ℝ) ^ 2 + symmetryPayment w R * (d : ℝ) ^ 2 =
        (rate + η / 2 + symmetryPayment w R) * (d : ℝ) ^ 2 := by ring
    _ ≤ (rate + η) * (d : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)

theorem uniformNormalizedTwoSidedWholeRowRate_iff (rate : ℝ) :
    UniformNormalizedTwoSidedWholeRowRate.{u} rate ↔ UniformTwoSidedWholeRowRate.{u} rate :=
  ⟨fun h => h.twoSided, fun h => h.normalized⟩

theorem uniformNormalizedTwoSidedWholeRowRateCanonicalBits_iff (rate : ℝ) :
    UniformNormalizedTwoSidedWholeRowRateCanonicalBits rate ↔
      UniformTwoSidedWholeRowRateCanonicalBits rate :=
  ⟨fun h => h.twoSided, fun h => h.normalized⟩

/-- Normalization loses no further deficit; the factor two comes only from
the earlier one-sided/two-sided translated-intersection argument. -/
theorem UniformNormalizedTwoSidedWholeRowRate.oneSided {rate : ℝ}
    (h : UniformNormalizedTwoSidedWholeRowRate.{u} rate) :
    UniformWholeRowRate.{u} ((1 + rate) / 2) :=
  h.twoSided.oneSided

theorem UniformNormalizedTwoSidedWholeRowRateCanonicalBits.oneSided {rate : ℝ}
    (h : UniformNormalizedTwoSidedWholeRowRateCanonicalBits rate) :
    UniformWholeRowRateCanonicalBits ((1 + rate) / 2) :=
  h.twoSided.oneSided

/-- Equivalence of the common-positive-deficit questions, for all alphabets. -/
theorem commonDeficit_iff_normalizedTwoSided :
    (∃ δ : ℝ, 0 < δ ∧ UniformWholeRowRate.{u} (1 - δ)) ↔
      ∃ δ : ℝ, 0 < δ ∧ UniformNormalizedTwoSidedWholeRowRate.{u} (1 - δ) := by
  constructor
  · rintro ⟨δ, hδ, h⟩
    refine ⟨δ, hδ, ?_⟩
    apply UniformTwoSidedWholeRowRate.normalized
    intro w η hη
    obtain ⟨d₀, hd₀⟩ := h w η hη
    exact ⟨d₀, fun d hd α _ hα => (hd₀ d hd α hα).twoSided⟩
  · rintro ⟨δ, hδ, h⟩
    refine ⟨δ / 2, by positivity, ?_⟩
    convert h.oneSided using 1; ring

/-- Canonical-width equivalence, in exactly the alphabet scope of the native crux. -/
theorem commonDeficitCanonicalBits_iff_normalizedTwoSided :
    (∃ δ : ℝ, 0 < δ ∧ UniformWholeRowRateCanonicalBits (1 - δ)) ↔
      ∃ δ : ℝ, 0 < δ ∧ UniformNormalizedTwoSidedWholeRowRateCanonicalBits (1 - δ) := by
  rw [commonDeficit_iff_twoSided]
  constructor
  · rintro ⟨δ, hδ, h⟩
    exact ⟨δ, hδ, h.normalized⟩
  · rintro ⟨δ, hδ, h⟩
    exact ⟨δ, hδ, h.twoSided⟩

theorem uniformNormalizedTwoSidedWholeRowRateCanonicalBits_crux
    {k β D : ℕ} {C δ : ℝ} (hC : 1 ≤ C)
    (hbound : UniformNormalizedTwoSidedWholeRowRateCanonicalBits (1 - δ)) :
    Crux k C β D (δ / 2) :=
  uniformTwoSidedWholeRowRateCanonicalBits_crux hC hbound.twoSided

theorem uniformNormalizedTwoSidedWholeRowRate_cruxOn
    {k β D : ℕ} {C δ : ℝ} (hC : 1 ≤ C)
    (hbound : UniformNormalizedTwoSidedWholeRowRate.{0} (1 - δ)) :
    CruxOn (fun _ b => 1 ≤ b) k C β D (δ / 2) :=
  uniformTwoSidedWholeRowRate_cruxOn hC hbound.twoSided

/-- A normalized common positive deficit is a sufficient native exclusion
hypothesis. This implication does not assert such a deficit exists. -/
theorem uniformNormalizedTwoSidedWholeRowRateCanonicalBits_excludes
    {k β : ℕ} {C δ : ℝ} (hC : 1 ≤ C) (hδ : 0 < δ)
    (hbound : UniformNormalizedTwoSidedWholeRowRateCanonicalBits (1 - δ)) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ M : TM, M.k = k → valueWidth M ≤ β → ∀ T : ℕ,
      ¬ ObliviousLinTime M d (entryBits d) C T :=
  uniformTwoSidedWholeRowRateCanonicalBits_excludes hC hδ hbound.twoSided

/-- A fixed normalization cutoff also gives a direct one-window consumer.
Its additional price is exactly the finite symmetry payment. -/
theorem normalizedTwoSidedWholeRow_window_bound_excludes
    {k β R : ℕ} {C ε δ : ℝ} (hC : 1 ≤ C) (hε : 0 < ε)
    (hgap : (169 / 32 : ℝ) * ε +
      symmetryPayment (rowSpreadWindow k β (genieDepth k β C ε) C ε) R < δ)
    (hbound : ∀ η : ℝ, 0 < η → ∃ d₀ : ℕ, ∀ d ≥ d₀,
      NormalizedTwoSidedWholeRowCardinalityBound d
        (rowSpreadWindow k β (genieDepth k β C ε) C ε + R + 1)
        (Fin (entryBits d) → Bool) ((1 - δ + η) * (d : ℝ) ^ 2)) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ M : TM, M.k = k → valueWidth M ≤ β → ∀ T : ℕ,
      ¬ ObliviousLinTime M d (entryBits d) C T := by
  apply twoSidedWholeRow_window_bound_excludes
    (δ := δ - symmetryPayment (rowSpreadWindow k β (genieDepth k β C ε) C ε) R)
    hC hε (by linarith)
  intro η hη
  obtain ⟨d₀, hd₀⟩ := hbound η hη
  refine ⟨d₀, fun d hd => ?_⟩
  convert (hd₀ d hd).twoSided (R := R) (by simp) using 1; ring

#print axioms uniformNormalizedTwoSidedWholeRowRate_iff
#print axioms uniformNormalizedTwoSidedWholeRowRateCanonicalBits_iff
#print axioms commonDeficit_iff_normalizedTwoSided
#print axioms commonDeficitCanonicalBits_iff_normalizedTwoSided
#print axioms uniformNormalizedTwoSidedWholeRowRateCanonicalBits_crux
#print axioms uniformNormalizedTwoSidedWholeRowRateCanonicalBits_excludes
#print axioms normalizedTwoSidedWholeRow_window_bound_excludes

end LeanBacklog.RowSpread
