import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum

/-!
# Finite random-decoder selection

Each constraint has its own finite observation and response types. Independently
sampling a response at every observation pattern gives an exact expected count
of simultaneously accepted source points. A maximizing deterministic decoder
therefore selects at least that many points. No probability-measure machinery,
independent-source assumption, or common response alphabet is required.
-/

namespace LeanBacklog.DecoderSelection

open Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable

universe u v w z

variable {A : Type u} {I : Type v} {B : I → Type w} {C : I → Type z}
  [Fintype I] [∀ i, Fintype (B i)] [∀ i, Fintype (C i)]

/-- A deterministic response table for every constraint and observation. -/
abbrev Decoder (B : I → Type w) (C : I → Type z) := ∀ i, B i → C i

/-- Product weight of a tuple of response tables. -/
def weight (q : ∀ i, B i → C i → ℝ) (δ : Decoder B C) : ℝ :=
  ∏ i, ∏ b, q i b (δ i b)

omit [∀ i, Fintype (C i)] in
theorem weight_nonneg (q : ∀ i, B i → C i → ℝ)
    (hq : ∀ i b c, 0 ≤ q i b c) (δ : Decoder B C) : 0 ≤ weight q δ :=
  prod_nonneg fun i _ => prod_nonneg fun b _ => hq i b (δ i b)

theorem sum_weight (q : ∀ i, B i → C i → ℝ)
    (hq1 : ∀ i b, ∑ c, q i b c = 1) : ∑ δ : Decoder B C, weight q δ = 1 := by
  classical
  unfold weight
  rw [← Fintype.prod_sum (fun i (δ : B i → C i) => ∏ b, q i b (δ b))]
  have hblock (i) : (∑ δ : B i → C i, ∏ b, q i b (δ b)) = 1 := by
    rw [← Fintype.prod_sum (q i)]
    simp [hq1]
  simp [hblock]

/-- Probability that all sampled tables give prescribed responses at one
observation per constraint. This is an exact finite sum identity. -/
theorem accepted_weight (q : ∀ i, B i → C i → ℝ)
    (hq1 : ∀ i b, ∑ c, q i b c = 1)
    (f : ∀ i, C i) (g : ∀ i, B i) :
    (∑ δ : Decoder B C, if ∀ i, δ i (g i) = f i then weight q δ else 0) =
      ∏ i, q i (g i) (f i) := by
  classical
  let p := fun (i : I) (b : B i) (c : C i) =>
    if b = g i → c = f i then q i b c else 0
  have hfactor (δ : Decoder B C) :
      (if ∀ i, δ i (g i) = f i then weight q δ else 0) =
        ∏ i, ∏ b, p i b (δ i b) := by
    simp [p, Fintype.prod_ite_zero, weight]
  simp_rw [hfactor]
  rw [← Fintype.prod_sum (fun i (δ : B i → C i) => ∏ b, p i b (δ b))]
  apply prod_congr rfl
  intro i _
  rw [← Fintype.prod_sum (p i)]
  have hrow (b : B i) : ∑ c, p i b c = if b = g i then q i (g i) (f i) else 1 := by
    by_cases hb : b = g i
    · subst b
      simp [p]
    · simp [p, hb, hq1]
  simp_rw [hrow]
  simp

/-- Points accepted by all the deterministic response tables. -/
noncomputable def accepted (f : ∀ i, A → C i) (g : ∀ i, A → B i)
    (S : Finset A) (δ : Decoder B C) : Finset A := by
  classical
  exact S.filter fun a => ∀ i, δ i (g i a) = f i a

omit [∀ i, Fintype (B i)] [∀ i, Fintype (C i)] in
theorem accepted_subset (f : ∀ i, A → C i) (g : ∀ i, A → B i)
    (S : Finset A) (δ : Decoder B C) : accepted f g S δ ⊆ S := by
  classical
  exact filter_subset _ _

omit [∀ i, Fintype (B i)] [∀ i, Fintype (C i)] in
theorem accepted_determined (f : ∀ i, A → C i) (g : ∀ i, A → B i)
    (S : Finset A) (δ : Decoder B C) :
    ∀ i, ∀ x ∈ accepted f g S δ, ∀ y ∈ accepted f g S δ,
      g i x = g i y → f i x = f i y := by
  classical
  intro i x hx y hy hxy
  have hx' := (mem_filter.mp hx).2 i
  have hy' := (mem_filter.mp hy).2 i
  exact hx'.symm.trans ((congrArg (δ i) hxy).trans hy')

/-- The expected number of accepted points, as a finite sum of weights. -/
theorem expected_card (q : ∀ i, B i → C i → ℝ)
    (hq1 : ∀ i b, ∑ c, q i b c = 1)
    (f : ∀ i, A → C i) (g : ∀ i, A → B i) (S : Finset A) :
    (∑ δ : Decoder B C, weight q δ * (accepted f g S δ).card) =
      ∑ a ∈ S, ∏ i, q i (g i a) (f i a) := by
  classical
  have hcard (δ : Decoder B C) :
      weight q δ * (accepted f g S δ).card =
        ∑ a ∈ S, if ∀ i, δ i (g i a) = f i a then weight q δ else 0 := by
    rw [← sum_filter]
    simp [accepted, mul_comm]
  simp_rw [hcard]
  rw [sum_comm]
  exact sum_congr rfl fun a _ => accepted_weight q hq1 (fun i => f i a) (fun i => g i a)

/-- Some deterministic choice of response tables attains at least the
finite expected count. Normalization supplies a nonempty decoder space,
so no separate nonemptiness assumption on the response types is needed. -/
theorem exists_decoder (q : ∀ i, B i → C i → ℝ)
    (hq : ∀ i b c, 0 ≤ q i b c) (hq1 : ∀ i b, ∑ c, q i b c = 1)
    (f : ∀ i, A → C i) (g : ∀ i, A → B i) (S : Finset A) :
    ∃ δ : Decoder B C,
      (∑ a ∈ S, ∏ i, q i (g i a) (f i a)) ≤ (accepted f g S δ).card := by
  classical
  have hne : (univ : Finset (Decoder B C)).Nonempty := by
    by_contra h
    have hn := sum_weight q hq1
    rw [not_nonempty_iff_eq_empty.mp h, sum_empty] at hn
    norm_num at hn
  obtain ⟨δ, _, hmax⟩ := univ.exists_max_image (fun δ => (accepted f g S δ).card) hne
  refine ⟨δ, ?_⟩
  calc
    _ = ∑ ε : Decoder B C, weight q ε * (accepted f g S ε).card :=
      (expected_card q hq1 f g S).symm
    _ ≤ ∑ ε : Decoder B C, weight q ε * (accepted f g S δ).card := by
      apply sum_le_sum
      intro ε _
      apply mul_le_mul_of_nonneg_left _ (weight_nonneg q hq ε)
      exact_mod_cast hmax ε (mem_univ _)
    _ = (accepted f g S δ).card := by rw [← sum_mul, sum_weight q hq1, one_mul]

/-- Select a subset on which every response is determined by its own
observation. The source set may be arbitrary and the response types dependent. -/
theorem exists_decodable_subset (q : ∀ i, B i → C i → ℝ)
    (hq : ∀ i b c, 0 ≤ q i b c) (hq1 : ∀ i b, ∑ c, q i b c = 1)
    (f : ∀ i, A → C i) (g : ∀ i, A → B i) (S : Finset A) :
    ∃ D : Finset A, D ⊆ S ∧
      (∀ i, ∀ x ∈ D, ∀ y ∈ D, g i x = g i y → f i x = f i y) ∧
      (∑ a ∈ S, ∏ i, q i (g i a) (f i a)) ≤ (D.card : ℝ) := by
  obtain ⟨δ, hδ⟩ := exists_decoder q hq hq1 f g S
  exact ⟨accepted f g S δ, accepted_subset f g S δ, accepted_determined f g S δ, hδ⟩

/-- One source point of positive acceptance weight ensures that the selected
subset is nonempty. This avoids any convention concerning the logarithm of zero. -/
theorem exists_decodable_nonempty_subset (q : ∀ i, B i → C i → ℝ)
    (hq : ∀ i b c, 0 ≤ q i b c) (hq1 : ∀ i b, ∑ c, q i b c = 1)
    (f : ∀ i, A → C i) (g : ∀ i, A → B i) (S : Finset A)
    (hpos : ∃ a ∈ S, ∀ i, 0 < q i (g i a) (f i a)) :
    ∃ D : Finset A, D ⊆ S ∧ D.Nonempty ∧
      (∀ i, ∀ x ∈ D, ∀ y ∈ D, g i x = g i y → f i x = f i y) ∧
      (∑ a ∈ S, ∏ i, q i (g i a) (f i a)) ≤ (D.card : ℝ) := by
  obtain ⟨D, hDS, hdet, hD⟩ := exists_decodable_subset q hq hq1 f g S
  obtain ⟨a, ha, hapos⟩ := hpos
  have hp : 0 < ∏ i, q i (g i a) (f i a) := prod_pos fun i _ => hapos i
  have hsum := single_le_sum (f := fun a => ∏ i, q i (g i a) (f i a))
    (fun a _ => prod_nonneg fun i _ => hq i (g i a) (f i a)) ha
  have hc : 0 < (D.card : ℝ) := hp.trans_le (hsum.trans hD)
  have hne : D.Nonempty := card_pos.mp (by exact_mod_cast hc)
  exact ⟨D, hDS, hne, hdet, hD⟩

#print axioms expected_card
#print axioms exists_decodable_subset
#print axioms exists_decodable_nonempty_subset

end LeanBacklog.DecoderSelection
