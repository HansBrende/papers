import LeanMachine.CoordinateSplitting
import Mathlib.LinearAlgebra.Pi

/-! Rank accounting for a finite family of mutually annihilating projections.
Extraction maps on the observed coordinates retain the same directness. -/

namespace LeanMachine.CoordinateSplitting

open Module Finset
open scoped BigOperators Classical

variable {K H A I : Type*} [Field K] [AddCommGroup H] [Module K H]
  [FiniteDimensional K H] [AddCommGroup A] [Module K A] [FiniteDimensional K A]
  [Fintype I]

theorem rank_sum_of_extraction (f : I → H →ₗ[K] A) (P : I → A →ₗ[K] A)
    (hx : ∀ i j, (P i).comp (f j) = if i = j then f i else 0)
    (hi : ∀ i, LinearMap.range (f i) ≤ LinearMap.range (∑ j, f j)) :
    finrank K (LinearMap.range (∑ i, f i)) =
      ∑ i, finrank K (LinearMap.range (f i)) := by
  classical
  have hfun (i j : I) (x : H) : P i (f j x) = if i = j then f i x else 0 := by
    have h := LinearMap.congr_fun (hx i j) x
    by_cases hij : i = j <;>
      simpa only [hij, ite_true, ite_false, LinearMap.comp_apply,
        LinearMap.zero_apply] using h
  have he (i : I) (x : H) : P i ((∑ j, f j) x) = f i x := by
    simp only [LinearMap.sum_apply, map_sum, hfun]
    simp
  have hev (i j : I) (y : LinearMap.range (f j)) :
      P i y.val = if i = j then y.val else 0 := by
    obtain ⟨x, hxv⟩ := y.property
    rw [← hxv, hfun]
    by_cases hij : i = j <;> simp [hij]
  let e : LinearMap.range (∑ i, f i) ≃ₗ[K] (∀ i, LinearMap.range (f i)) :=
    { toFun := fun y i => ⟨P i y.val, by
        obtain ⟨x, hxv⟩ := y.property
        exact ⟨x, by rw [← hxv, he]⟩⟩
      invFun := fun y => ⟨∑ i, (y i).val,
        Submodule.sum_mem _ (fun i _ => hi i (y i).property)⟩
      left_inv := by
        rintro ⟨y, x, rfl⟩
        apply Subtype.ext
        change ∑ i, P i ((∑ j, f j) x) = (∑ j, f j) x
        calc
          _ = ∑ i, f i x := sum_congr rfl (fun i _ => he i x)
          _ = _ := (LinearMap.sum_apply univ f x).symm
      right_inv := by
        intro y
        funext i
        apply Subtype.ext
        change P i (∑ j, (y j).val) = (y i).val
        rw [map_sum]
        simp_rw [hev]
        simp
      map_add' := by intros; ext i; simp
      map_smul' := by intros; ext i; simp }
  rw [e.finrank_eq, Module.finrank_pi_fintype]

theorem projection_sum_rank (p : I → H →ₗ[K] H)
    (hp : ∀ i j, (p i).comp (p j) = if i = j then p i else 0) :
    finrank K (LinearMap.range (∑ i, p i)) =
      ∑ i, finrank K (LinearMap.range (p i)) := by
  apply rank_sum_of_extraction p p hp
  intro i
  rintro _ ⟨x, rfl⟩
  refine ⟨p i x, ?_⟩
  simp only [LinearMap.sum_apply]
  have h (j : I) : p j (p i x) = if j = i then p i x else 0 := by
    have h := LinearMap.congr_fun (hp j i) x
    by_cases hji : j = i
    · subst j
      simpa only [ite_true, LinearMap.comp_apply] using h
    · simpa only [hji, ite_false, LinearMap.comp_apply, LinearMap.zero_apply] using h
  simp_rw [h]
  simp

theorem observed_projection_sum_rank (p : I → H →ₗ[K] H)
    (hp : ∀ i j, (p i).comp (p j) = if i = j then p i else 0)
    (r : H →ₗ[K] A) (D : I → A →ₗ[K] A)
    (hD : ∀ i, (D i).comp r = r.comp (p i)) :
    finrank K (LinearMap.range (r.comp (∑ i, p i))) =
      ∑ i, finrank K (LinearMap.range (r.comp (p i))) := by
  have hsum : r.comp (∑ i, p i) = ∑ i, r.comp (p i) := by
    ext x; simp
  rw [hsum]
  apply rank_sum_of_extraction (fun i => r.comp (p i)) D
  · intro i j
    rw [← LinearMap.comp_assoc, hD, LinearMap.comp_assoc, hp]
    by_cases hij : i = j <;> simp [hij]
  · intro i
    rintro _ ⟨x, rfl⟩
    refine ⟨p i x, ?_⟩
    rw [← hsum]
    change r ((∑ j, p j) (p i x)) = r (p i x)
    congr 1
    simp only [LinearMap.sum_apply]
    have h (j : I) : p j (p i x) = if j = i then p i x else 0 := by
      have h := LinearMap.congr_fun (hp j i) x
      by_cases hji : j = i
      · subst j
        simpa only [ite_true, LinearMap.comp_apply] using h
      · simpa only [hji, ite_false, LinearMap.comp_apply, LinearMap.zero_apply] using h
    simp_rw [h]
    simp

theorem projection_sum_extract (p : I → H →ₗ[K] H)
    (hp : ∀ i j, (p i).comp (p j) = if i = j then p i else 0) (i : I) :
    (p i).comp (∑ j, p j) = p i := by
  ext x
  simp only [LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
  have hfun (j : I) : p i (p j x) = if i = j then p i x else 0 := by
    have h := LinearMap.congr_fun (hp i j) x
    by_cases hij : i = j <;>
      simpa only [hij, ite_true, ite_false, LinearMap.comp_apply,
        LinearMap.zero_apply] using h
  simp_rw [hfun]
  simp

theorem projection_sum_idempotent (p : I → H →ₗ[K] H)
    (hp : ∀ i j, (p i).comp (p j) = if i = j then p i else 0) :
    (∑ i, p i).comp (∑ i, p i) = ∑ i, p i := by
  ext x
  calc
    _ = ∑ i, p i ((∑ j, p j) x) := by simp only [LinearMap.comp_apply, LinearMap.sum_apply]
    _ = ∑ i, p i x := sum_congr rfl
      (fun i _ => LinearMap.congr_fun (projection_sum_extract p hp i) x)
    _ = _ := (LinearMap.sum_apply univ p x).symm

theorem projection_sum_ker (p : I → H →ₗ[K] H)
    (hp : ∀ i j, (p i).comp (p j) = if i = j then p i else 0) (x : H) :
    (∑ i, p i) x = 0 ↔ ∀ i, p i x = 0 := by
  constructor
  · intro h i
    have hh := LinearMap.congr_fun (projection_sum_extract p hp i) x
    simpa only [LinearMap.comp_apply, h, map_zero] using hh.symm
  · intro h
    simp only [LinearMap.sum_apply, h, sum_const_zero]

/-- Balanced factors preserve the weighted half-rate deficit exactly. The
observed-coordinate identities are essential: global directness alone does
not justify deleting their coordinate capacities. -/
theorem half_of_residual {J : Type*} [Fintype J]
    {B : J → Type*} [∀ j, AddCommGroup (B j)] [∀ j, Module K (B j)]
    [∀ j, FiniteDimensional K (B j)]
    (p : I → H →ₗ[K] H)
    (hp : ∀ i j, (p i).comp (p j) = if i = j then p i else 0)
    (r : ∀ j, H →ₗ[K] B j) (D : ∀ i j, B j →ₗ[K] B j)
    (hD : ∀ i j, (D i j).comp (r j) = (r j).comp (p i))
    (hbal : ∀ i, (∑ j, finrank K (LinearMap.range ((r j).comp (p i)))) =
      2 * finrank K (LinearMap.range (p i)))
    (hres : 2 * finrank K (LinearMap.ker (∑ i, p i)) ≤
      ∑ j, finrank K (LinearMap.range ((r j).domRestrict (LinearMap.ker (∑ i, p i))))) :
    2 * finrank K H ≤ ∑ j, finrank K (LinearMap.range (r j)) := by
  have hpid := projection_sum_idempotent p hp
  have hDsum (j : J) : (∑ i, D i j).comp (r j) = (r j).comp (∑ i, p i) := by
    ext x
    simp only [LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
    exact sum_congr rfl (fun i _ => LinearMap.congr_fun (hD i j) x)
  have hrank : (∑ j, finrank K (LinearMap.range ((r j).comp (∑ i, p i)))) =
      2 * finrank K (LinearMap.range (∑ i, p i)) := by
    simp_rw [observed_projection_sum_rank p hp (r _) (fun i => D i _) (fun i => hD i _)]
    rw [sum_comm]
    simp_rw [hbal]
    rw [← mul_sum, projection_sum_rank p hp]
  have hsum := sum_congr (s₁ := (univ : Finset J)) rfl (fun j _ =>
    coordinate_rank_split (∑ i, p i) hpid (r j) (∑ i, D i j) (hDsum j))
  rw [sum_add_distrib, hrank] at hsum
  have hn := LinearMap.finrank_range_add_finrank_ker (∑ i, p i)
  omega

end LeanMachine.CoordinateSplitting
