import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/-! Dimension deficits for a finite arrangement of subspaces. The results are
linear algebra only; no graph or recovery assumptions are encoded here. -/

namespace LeanMachine.SubspaceDefect

open Module Finset
open scoped BigOperators

variable {ι K W : Type*} [Fintype ι] [Field K]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- Twice the dimension of a test space, less its coordinate intersections.
An integer is used so that negative deficits are not truncated. -/
noncomputable def defect (U : ι → Submodule K W) (S : Submodule K W) : ℤ :=
  2 * (finrank K S : ℤ) - ∑ v, (finrank K ↥(U v ⊓ S) : ℤ)

omit [FiniteDimensional K W] in
@[simp] theorem defect_bot (U : ι → Submodule K W) : defect U ⊥ = 0 := by
  unfold defect
  simp only [finrank_bot, Nat.cast_zero, mul_zero, zero_sub, neg_eq_zero]
  apply sum_eq_zero
  intro v _
  rw [inf_bot_eq]
  simp

omit [FiniteDimensional K W] in
@[simp] theorem defect_top (U : ι → Submodule K W) :
    defect U ⊤ = 2 * (finrank K W : ℤ) - ∑ v, (finrank K ↥(U v) : ℤ) := by
  unfold defect
  rw [finrank_top]
  congr 1
  apply sum_congr rfl
  intro v _
  rw [inf_top_eq]

/-- The coordinate intersection dimensions are supermodular. -/
theorem intersection_supermodular (U S T : Submodule K W) :
    finrank K ↥(U ⊓ S) + finrank K ↥(U ⊓ T) ≤
      finrank K ↥(U ⊓ (S ⊓ T)) + finrank K ↥(U ⊓ (S ⊔ T)) := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq (U ⊓ S) (U ⊓ T)
  have hle : (U ⊓ S) ⊔ (U ⊓ T) ≤ U ⊓ (S ⊔ T) :=
    sup_le (inf_le_inf_left _ le_sup_left) (inf_le_inf_left _ le_sup_right)
  have hn := Submodule.finrank_mono hle
  have heq : (U ⊓ S) ⊓ (U ⊓ T) = U ⊓ (S ⊓ T) := by
    simp only [inf_assoc, inf_left_comm, inf_left_idem]
  rw [heq] at h
  omega

theorem submodular (U : ι → Submodule K W) (S T : Submodule K W) :
    defect U (S ⊓ T) + defect U (S ⊔ T) ≤ defect U S + defect U T := by
  have hm := Submodule.finrank_sup_add_finrank_inf_eq S T
  have hs : (∑ v, (finrank K ↥(U v ⊓ S) : ℤ)) + ∑ v, (finrank K ↥(U v ⊓ T) : ℤ) ≤
      (∑ v, (finrank K ↥(U v ⊓ (S ⊓ T)) : ℤ)) +
        ∑ v, (finrank K ↥(U v ⊓ (S ⊔ T)) : ℤ) := by
    rw [← sum_add_distrib, ← sum_add_distrib]
    exact sum_le_sum fun v _ => by exact_mod_cast intersection_supermodular (U v) S T
  dsimp [defect]
  omega

/-- Under positivity on every nonzero test space, intersecting tight spaces
have tight intersection and join. -/
theorem tight_inf_sup (U : ι → Submodule K W)
    (hpos : ∀ S : Submodule K W, S ≠ ⊥ → 1 ≤ defect U S)
    {S T : Submodule K W} (hS : defect U S = 1) (hT : defect U T = 1)
    (hI : S ⊓ T ≠ ⊥) : defect U (S ⊓ T) = 1 ∧ defect U (S ⊔ T) = 1 := by
  have hJ : S ⊔ T ≠ ⊥ := by
    intro h
    apply hI
    apply le_bot_iff.mp
    exact (inf_le_left.trans le_sup_left).trans_eq h
  have hi := hpos _ hI
  have hj := hpos _ hJ
  have hs := submodular U S T
  omega

/-- Equality of the total deficit forces equality in every coordinate's
intersection inclusion. This does not assume distributivity of subspaces. -/
theorem exact_join_of_equality (U : ι → Submodule K W) {S T : Submodule K W}
    (h : defect U (S ⊓ T) + defect U (S ⊔ T) = defect U S + defect U T) (v : ι) :
    U v ⊓ (S ⊔ T) = (U v ⊓ S) ⊔ (U v ⊓ T) := by
  classical
  have hm := Submodule.finrank_sup_add_finrank_inf_eq S T
  have heq : (∑ v, ((finrank K ↥(U v ⊓ S) : ℤ) + (finrank K ↥(U v ⊓ T) : ℤ))) =
      ∑ v, ((finrank K ↥(U v ⊓ (S ⊓ T)) : ℤ) +
        (finrank K ↥(U v ⊓ (S ⊔ T)) : ℤ)) := by
    simp only [sum_add_distrib]
    dsimp [defect] at h
    omega
  have hpoint := (sum_eq_sum_iff_of_le (fun i (_ : i ∈ (univ : Finset ι)) =>
    show (finrank K ↥(U i ⊓ S) : ℤ) + finrank K ↥(U i ⊓ T) ≤
      (finrank K ↥(U i ⊓ (S ⊓ T)) : ℤ) + finrank K ↥(U i ⊓ (S ⊔ T)) by
      exact_mod_cast intersection_supermodular (U i) S T)).mp heq v (mem_univ v)
  have hmod := Submodule.finrank_sup_add_finrank_inf_eq (U v ⊓ S) (U v ⊓ T)
  have hi : (U v ⊓ S) ⊓ (U v ⊓ T) = U v ⊓ (S ⊓ T) := by
    simp only [inf_assoc, inf_left_comm, inf_left_idem]
  rw [hi] at hmod
  apply Eq.symm
  apply Submodule.eq_of_le_of_finrank_eq
    (sup_le (inf_le_inf_left _ le_sup_left) (inf_le_inf_left _ le_sup_right))
  omega

theorem tight_exact_join (U : ι → Submodule K W)
    (hpos : ∀ S : Submodule K W, S ≠ ⊥ → 1 ≤ defect U S)
    {S T : Submodule K W} (hS : defect U S = 1) (hT : defect U T = 1)
    (hI : S ⊓ T ≠ ⊥) (v : ι) :
    U v ⊓ (S ⊔ T) = (U v ⊓ S) ⊔ (U v ⊓ T) := by
  obtain ⟨hi, hj⟩ := tight_inf_sup U hpos hS hT hI
  exact exact_join_of_equality U (by omega) v

/-- Dimension accounting for an actual quotient image, including the removed
intersection. -/
theorem quotient_image_dimension (U S : Submodule K W) :
    finrank K ↥(U.map S.mkQ) + finrank K ↥(U ⊓ S) = finrank K U := by
  let f := S.mkQ.domRestrict U
  have hr : LinearMap.range f = U.map S.mkQ := LinearMap.range_domRestrict U S.mkQ
  have hk : LinearMap.ker f = (U ⊓ S).comap U.subtype := by
    ext x
    simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.mem_inf]
    change S.mkQ x.val = 0 ↔ x.val ∈ U ∧ x.val ∈ S
    simp only [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, x.property, true_and]
  have he := (Submodule.comapSubtypeEquivOfLe (inf_le_left : U ⊓ S ≤ U)).finrank_eq
  rw [← hk] at he
  have hn := LinearMap.finrank_range_add_finrank_ker f
  rw [hr, he] at hn
  exact hn

/-- If the quotient obeys the half bound, its loss is exactly the deficit of
the removed space. This identity is independent of quotient closure. -/
theorem deficit_of_quotient_half (U : ι → Submodule K W) (S : Submodule K W)
    (hquot : 2 * finrank K (W ⧸ S) ≤ ∑ v, finrank K ↥((U v).map S.mkQ)) :
    defect U ⊤ ≤ defect U S := by
  have hq := S.finrank_quotient_add_finrank
  have hs := congrArg (fun f : ι → ℕ => ∑ v, f v)
    (funext fun v => quotient_image_dimension (U v) S)
  simp only [sum_add_distrib] at hs
  rw [defect_top]
  unfold defect
  push_cast [← Nat.cast_sum]
  omega

omit [FiniteDimensional K W] in
/-- Positivity forbids a direction shared by two distinct coordinates. -/
theorem pairwise_disjoint_of_positive (U : ι → Submodule K W)
    (hpos : ∀ S : Submodule K W, S ≠ ⊥ → 1 ≤ defect U S) :
    Pairwise (fun u v => Disjoint (U u) (U v)) := by
  classical
  intro u v huv
  apply disjoint_iff.mpr
  apply (Submodule.eq_bot_iff _).mpr
  rintro x ⟨hxu, hxv⟩
  by_contra hx
  let L : Submodule K W := K ∙ x
  have hL : finrank K L = 1 := finrank_span_singleton hx
  have hL0 : L ≠ ⊥ := by intro h; rw [h, finrank_bot] at hL; omega
  have hu : L ≤ U u := Submodule.span_le.mpr (by simpa using hxu)
  have hv : L ≤ U v := Submodule.span_le.mpr (by simpa using hxv)
  have hsum : (2 : ℤ) ≤ ∑ w, (finrank K ↥(U w ⊓ L) : ℤ) := by
    have hs := sum_le_sum_of_subset_of_nonneg (s := ({u, v} : Finset ι))
      (t := univ) (f := fun w => (finrank K ↥(U w ⊓ L) : ℤ)) (subset_univ _)
      (fun _ _ _ => Int.natCast_nonneg _)
    rw [sum_pair huv, inf_eq_right.mpr hu, inf_eq_right.mpr hv, hL] at hs
    exact hs
  have hp := hpos L hL0
  unfold defect at hp
  rw [hL] at hp
  omega

omit [FiniteDimensional K W] in
/-- When explicit coordinate lower bounds already use the entire budget of
a positive test space, every coordinate bound is exact. -/
theorem exact_intersections (U : ι → Submodule K W) (S : Submodule K W)
    (hpos : 1 ≤ defect U S) (m : ι → ℕ)
    (hm : ∀ v, m v ≤ finrank K (U v ⊓ S : Submodule K W))
    (hbudget : (∑ v, m v) + 1 = 2 * finrank K S) :
    defect U S = 1 ∧ ∀ v, finrank K (U v ⊓ S : Submodule K W) = m v := by
  have hs := sum_le_sum (fun v (_ : v ∈ (univ : Finset ι)) => hm v)
  have hp := hpos
  unfold defect at hp
  push_cast [← Nat.cast_sum] at hp
  have heq : ∑ v, m v = ∑ v, finrank K (U v ⊓ S : Submodule K W) := by omega
  have hpoint := (sum_eq_sum_iff_of_le (fun v (_ : v ∈ (univ : Finset ι)) => hm v)).mp heq
  refine ⟨?_, fun v => (hpoint v (mem_univ v)).symm⟩
  unfold defect
  push_cast [← Nat.cast_sum]
  omega

/-- Every tight space is spanned by its coordinate intersections. No separate
spanning invariant is needed in a tight-growth argument. -/
theorem tight_spanned (U : ι → Submodule K W)
    (hpos : ∀ S : Submodule K W, S ≠ ⊥ → 1 ≤ defect U S)
    {S : Submodule K W} (ht : defect U S = 1) :
    (⨆ v, U v ⊓ S) = S := by
  let P := ⨆ v, U v ⊓ S
  have hle : P ≤ S := iSup_le fun _ => inf_le_right
  have heq : ∀ v, U v ⊓ P = U v ⊓ S := by
    intro v
    apply le_antisymm (inf_le_inf_left _ hle)
    exact le_inf inf_le_left (le_iSup (fun v => U v ⊓ S) v)
  have hp : 0 ≤ defect U P := by
    by_cases hz : P = ⊥
    · rw [hz, defect_bot]
    · exact (by norm_num : (0 : ℤ) ≤ 1).trans (hpos P hz)
  have hmass : (∑ v, (finrank K (U v ⊓ P : Submodule K W) : ℤ)) =
      ∑ v, (finrank K (U v ⊓ S : Submodule K W) : ℤ) := by
    apply sum_congr rfl
    intro v _
    rw [heq]
  unfold defect at hp ht
  apply Submodule.eq_of_le_of_finrank_le hle
  omega

omit [FiniteDimensional K W] in
/-- Dimensions of the same intersection, viewed inside the restricted space. -/
theorem restriction_dimension (U S : Submodule K W) :
    finrank K (U.comap S.subtype) = finrank K (U ⊓ S : Submodule K W) := by
  have hcomap : U.comap S.subtype = (U ⊓ S).comap S.subtype := by
    ext x
    simp only [Submodule.mem_comap, Submodule.mem_inf, Submodule.subtype_apply]
    exact ⟨fun h => ⟨h, x.property⟩, fun h => h.1⟩
  rw [hcomap]
  exact (Submodule.comapSubtypeEquivOfLe (inf_le_right : U ⊓ S ≤ S)).finrank_eq

theorem restricted_span (U : ι → Submodule K W) (S : Submodule K W)
    (hspan : (⨆ v, U v ⊓ S) = S) :
    (⨆ v, (U v).comap S.subtype) = ⊤ := by
  apply Submodule.map_injective_of_injective S.injective_subtype
  rw [Submodule.map_iSup, Submodule.map_top, Submodule.range_subtype]
  simpa only [Submodule.map_comap_eq, Submodule.range_subtype, inf_comm] using hspan

omit [FiniteDimensional K W] in
theorem image_span {Z : Type*} [AddCommGroup Z] [Module K Z]
    (U : ι → Submodule K W) (f : W →ₗ[K] Z) (hf : Function.Surjective f)
    (hspan : (⨆ v, U v) = ⊤) : (⨆ v, (U v).map f) = ⊤ := by
  rw [← Submodule.map_iSup, hspan, Submodule.map_top, LinearMap.range_eq_top.mpr hf]

end LeanMachine.SubspaceDefect
