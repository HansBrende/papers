import SoftRecovery.Observations

namespace SoftRecovery

open Finset HalfRate MotionDepthCodes
set_option autoImplicit false

variable {A : Type*} [DecidableEq A]

/-- The conditional rank of a whole set; for entropy, `H(S | K)`. -/
def conditionalRank (h : Finset A → ℝ) (S K : Finset A) : ℝ := h (S ∪ K) - h K

theorem conditionalRank_nonneg {h : Finset A → ℝ} (hh : IsPolymatroid h)
    (S K : Finset A) : 0 ≤ conditionalRank h S K :=
  sub_nonneg.mpr (hh.mono subset_union_right)

@[simp] theorem conditionalRank_of_subset (h : Finset A → ℝ)
    {S K : Finset A} (hSK : S ⊆ K) : conditionalRank h S K = 0 := by
  simp [conditionalRank, union_eq_right.mpr hSK]

theorem conditionalRank_antitone {h : Finset A → ℝ} (hh : IsPolymatroid h)
    (S : Finset A) {K L : Finset A} (hKL : K ⊆ L) :
    conditionalRank h S L ≤ conditionalRank h S K := by
  have hs := hh.submod (S ∪ K) L
  rw [union_assoc, union_eq_right.mpr hKL] at hs
  have hm := hh.mono (subset_inter (subset_union_right : K ⊆ S ∪ K) hKL)
  unfold conditionalRank
  linarith

theorem conditionalRank_le {h : Finset A → ℝ} (hh : IsPolymatroid h)
    (S K : Finset A) : conditionalRank h S K ≤ h S := by
  simpa [conditionalRank, hh.empty] using conditionalRank_antitone hh S (empty_subset K)

theorem conditionalRank_contr (h : Finset A → ℝ) (Z S K : Finset A) :
    conditionalRank (contr h Z) S K = conditionalRank h S (K ∪ Z) := by
  simp only [conditionalRank, contr, union_assoc]
  ring

theorem contr_contr (h : Finset A → ℝ) (Z Q : Finset A) :
    contr (contr h Z) Q = contr h (Z ∪ Q) := by
  funext S
  simp only [contr, union_assoc, union_comm Q Z]
  ring

/-- The information a set gains from another set in a common context.
For entropy this is `I(S; T | Z)`. -/
def mutualRank (h : Finset A → ℝ) (S T Z : Finset A) : ℝ :=
  conditionalRank h S Z - conditionalRank h S (T ∪ Z)

theorem mutualRank_symm (h : Finset A → ℝ) (S T Z : Finset A) :
    mutualRank h S T Z = mutualRank h T S Z := by
  unfold mutualRank conditionalRank
  rw [show S ∪ (T ∪ Z) = T ∪ (S ∪ Z) by ac_rfl]
  ring

theorem mutualRank_nonneg {h : Finset A → ℝ} (hh : IsPolymatroid h)
    (S T Z : Finset A) : 0 ≤ mutualRank h S T Z :=
  sub_nonneg.mpr (conditionalRank_antitone hh S subset_union_right)

theorem mutualRank_le_right {h : Finset A → ℝ} (hh : IsPolymatroid h)
    (S T Z : Finset A) : mutualRank h S T Z ≤ conditionalRank h T Z := by
  rw [mutualRank_symm]
  exact sub_le_self _ (conditionalRank_nonneg hh T (S ∪ Z))

/-- Losing the old context costs at most the information not retained by the
new one. Exact functional dependence, rather than set inclusion, suffices. -/
theorem mi_le_add_conditionalRank {h : Finset A → ℝ} (hh : IsPolymatroid h)
    (e : A) (L K : Finset A) :
    mi h e L ≤ mi h e K + conditionalRank h L K := by
  have hmi := mi_mono hh e (subset_union_left : L ⊆ L ∪ K)
  have hm := hh.mono (insert_subset_insert e (subset_union_right : K ⊆ L ∪ K))
  simp only [mi, conditionalRank] at *
  linarith

/-- Partial recovery: pay the helpers' joint conditional rank and the
uncertainty still left after they are supplied. -/
theorem increment_le_conditionalRank_add {h : Finset A → ℝ} (hh : IsPolymatroid h)
    (K F : Finset A) (v : A) :
    increment h K v ≤ conditionalRank h F K + increment h (F ∪ K) v := by
  have hm := hh.mono (insert_subset_insert v (subset_union_right : K ⊆ F ∪ K))
  simp only [increment, conditionalRank]
  linarith

/-- A common reveal is charged by its joint rank conditional on what is
already known, not by a sum of unconditional record capacities. -/
theorem conditional_drop_le_joint {h : Finset A → ℝ} (hh : IsPolymatroid h)
    (C Z Q : Finset A) :
    h (C ∪ Z) - h Z - conditionalRank h Q Z ≤
      h (C ∪ (Z ∪ Q)) - h (Z ∪ Q) := by
  have hs := mutualRank_le_right hh C Q Z
  simp only [mutualRank, conditionalRank, union_comm Q Z] at hs ⊢
  linarith

/-- A deterministic decoder for an entire earlier context certifies zero
conditional rank. This reuses the existing finite-observation entropy API. -/
theorem entropy_conditionalRank_zero_of_recovery {Ω α : Type*}
    [Fintype A] [Fintype Ω] [Fintype α]
    (p : Ω → ℝ) (X : Ω → A → α) (hp : ∀ ω, 0 ≤ p ω) (S K : Finset A)
    (hr : ∀ x y, (∀ a ∈ K, X x a = X y a) → ∀ a ∈ S, X x a = X y a) :
    conditionalRank (codeEntropy p X) S K = 0 := by
  apply sub_eq_zero.mpr
  unfold codeEntropy
  apply TransposeFollowup.observationEntropy_eq_of_same_fibers p hp
  intro x y
  simp only [view_eq_iff]
  constructor
  · exact fun he a ha => he a (mem_union_right S ha)
  · intro he a ha
    exact (mem_union.mp ha).elim (hr x y he a) (he a)

end SoftRecovery
