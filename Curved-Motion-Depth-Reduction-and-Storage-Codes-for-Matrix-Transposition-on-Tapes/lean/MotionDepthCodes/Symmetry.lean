import MotionDepthCodes.Polymatroid

/-!
# Symmetrization

Automorphisms of the side information act on valid polymatroids. Averaging a
valid polymatroid over the automorphism group gives an invariant valid
polymatroid with the same total value and the same sum of singleton values. So
a rate bound needs to be checked only on invariant polymatroids; certificates
then need one elemental inequality per orbit.
-/

namespace MotionDepthCodes

open Finset
open scoped BigOperators
set_option autoImplicit false

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- `σ` is an automorphism of the side information `N`. -/
def IsAut (N : V → Finset V) (σ : Equiv.Perm V) : Prop :=
  ∀ v, (N v).map σ.toEmbedding = N (σ v)

instance (N : V → Finset V) (σ : Equiv.Perm V) : Decidable (IsAut N σ) :=
  inferInstanceAs (Decidable (∀ v, (N v).map σ.toEmbedding = N (σ v)))

omit [DecidableEq V] [Fintype V] in
theorem IsAut.mul {N : V → Finset V} {σ τ : Equiv.Perm V} (hσ : IsAut N σ) (hτ : IsAut N τ) :
    IsAut N (σ * τ) := by
  intro v
  have e : (N v).map (σ * τ).toEmbedding = ((N v).map τ.toEmbedding).map σ.toEmbedding := by
    rw [Finset.map_map]
    rfl
  rw [e, hτ v, hσ (τ v)]
  rfl

omit [DecidableEq V] [Fintype V] in
theorem IsAut.inv {N : V → Finset V} {σ : Equiv.Perm V} (hσ : IsAut N σ) : IsAut N σ⁻¹ := by
  intro v
  have h1 := hσ (σ⁻¹ v)
  have e1 : σ (σ⁻¹ v) = v := by simp
  rw [e1] at h1
  rw [← h1, Finset.map_map]
  have e : σ.toEmbedding.trans σ⁻¹.toEmbedding = Function.Embedding.refl V := by
    ext x
    simp
  rw [e, Finset.map_refl]

/-- The value of `h` after relabelling by `σ`. -/
def relabel (σ : Equiv.Perm V) (h : Finset V → ℝ) (S : Finset V) : ℝ :=
  h (S.map σ.toEmbedding)

omit [Fintype V] in
theorem IsPolymatroid.relabel {h : Finset V → ℝ} (hh : IsPolymatroid h) (σ : Equiv.Perm V) :
    IsPolymatroid (MotionDepthCodes.relabel σ h) where
  empty := by simp [MotionDepthCodes.relabel, hh.empty]
  mono := fun A B hAB => hh.mono (Finset.map_subset_map.mpr hAB)
  submod := fun A B => by
    simp only [MotionDepthCodes.relabel, Finset.map_union, Finset.map_inter]
    exact hh.submod _ _

omit [Fintype V] in
theorem IsValid.relabel {h : Finset V → ℝ} {N : V → Finset V} (hv : IsValid h N)
    {σ : Equiv.Perm V} (hσ : IsAut N σ) : IsValid (MotionDepthCodes.relabel σ h) N := by
  intro v
  simp only [MotionDepthCodes.relabel, Finset.map_insert, hσ v]
  exact hv (σ v)

open Classical in
/-- The automorphisms of `N`, as a finite set of permutations. -/
noncomputable def autSet (N : V → Finset V) : Finset (Equiv.Perm V) :=
  univ.filter (IsAut N)

theorem mem_autSet {N : V → Finset V} {σ : Equiv.Perm V} : σ ∈ autSet N ↔ IsAut N σ := by
  classical
  simp [autSet]

theorem one_mem_autSet (N : V → Finset V) : (1 : Equiv.Perm V) ∈ autSet N := by
  rw [mem_autSet]
  intro v
  have e : (1 : Equiv.Perm V).toEmbedding = Function.Embedding.refl V := by
    ext x
    simp
  rw [e, Finset.map_refl]
  rfl

/-- The average of `h` over all automorphisms of `N`. -/
noncomputable def symmetrize (N : V → Finset V) (h : Finset V → ℝ) (S : Finset V) : ℝ :=
  ((autSet N).card : ℝ)⁻¹ * ∑ σ ∈ autSet N, MotionDepthCodes.relabel σ h S

theorem autSet_card_pos (N : V → Finset V) : (0 : ℝ) < (autSet N).card := by
  exact_mod_cast Finset.card_pos.mpr ⟨1, one_mem_autSet N⟩

theorem IsPolymatroid.symmetrize {h : Finset V → ℝ} (hh : IsPolymatroid h)
    (N : V → Finset V) : IsPolymatroid (MotionDepthCodes.symmetrize N h) where
  empty := by
    simp [MotionDepthCodes.symmetrize, MotionDepthCodes.relabel, hh.empty]
  mono := by
    intro A B hAB
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (autSet_card_pos N).le)
    exact Finset.sum_le_sum fun σ _ => (hh.relabel σ).mono hAB
  submod := by
    intro A B
    simp only [MotionDepthCodes.symmetrize, ← mul_add, ← Finset.sum_add_distrib]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (autSet_card_pos N).le)
    exact Finset.sum_le_sum fun σ _ => (hh.relabel σ).submod A B

theorem IsValid.symmetrize {h : Finset V → ℝ} {N : V → Finset V} (hv : IsValid h N) :
    IsValid (MotionDepthCodes.symmetrize N h) N := by
  intro v
  simp only [MotionDepthCodes.symmetrize]
  congr 1
  apply Finset.sum_congr rfl
  intro σ hσ
  exact (hv.relabel (mem_autSet.mp hσ)) v

theorem symmetrize_invariant (N : V → Finset V) (h : Finset V → ℝ) {τ : Equiv.Perm V}
    (hτ : IsAut N τ) (S : Finset V) :
    MotionDepthCodes.symmetrize N h (S.map τ.toEmbedding) = MotionDepthCodes.symmetrize N h S := by
  simp only [MotionDepthCodes.symmetrize, MotionDepthCodes.relabel]
  congr 1
  have e : ∀ σ : Equiv.Perm V, (S.map τ.toEmbedding).map σ.toEmbedding =
      S.map (σ * τ).toEmbedding := by
    intro σ
    rw [Finset.map_map]
    rfl
  simp only [e]
  apply Finset.sum_nbij' (fun σ => σ * τ) (fun σ => σ * τ⁻¹)
  · intro σ hσ
    exact mem_autSet.mpr ((mem_autSet.mp hσ).mul hτ)
  · intro σ hσ
    exact mem_autSet.mpr ((mem_autSet.mp hσ).mul hτ.inv)
  · intro σ _
    simp
  · intro σ _
    simp
  · intro σ _
    rfl

theorem symmetrize_univ (N : V → Finset V) (h : Finset V → ℝ) :
    MotionDepthCodes.symmetrize N h univ = h univ := by
  simp only [MotionDepthCodes.symmetrize, MotionDepthCodes.relabel, Finset.map_univ_equiv,
    Finset.sum_const, nsmul_eq_mul]
  field_simp [(autSet_card_pos N).ne']

theorem sum_symmetrize_singleton (N : V → Finset V) (h : Finset V → ℝ) :
    ∑ v, MotionDepthCodes.symmetrize N h {v} = ∑ v, h {v} := by
  simp only [MotionDepthCodes.symmetrize, MotionDepthCodes.relabel, Finset.map_singleton,
    ← Finset.mul_sum]
  rw [Finset.sum_comm]
  have e : ∀ σ : Equiv.Perm V, ∑ v, h {σ.toEmbedding v} = ∑ v, h {v} := by
    intro σ
    exact Equiv.sum_comp σ (fun v => h {v})
  simp only [e, Finset.sum_const, nsmul_eq_mul]
  field_simp [(autSet_card_pos N).ne']

/-- **Symmetrization.** A rate bound holds as soon as it holds for valid
polymatroids invariant under every automorphism of `N`. -/
theorem RateBound.of_invariant {N : V → Finset V} {c : ℝ}
    (hsym : ∀ h : Finset V → ℝ, IsPolymatroid h → IsValid h N →
      (∀ σ, IsAut N σ → ∀ S, h (S.map σ.toEmbedding) = h S) → h univ ≤ c * ∑ v, h {v}) :
    RateBound N c := by
  intro h hh hv
  have h1 := hsym (MotionDepthCodes.symmetrize N h) (hh.symmetrize N) hv.symmetrize
    (fun σ hσ S => symmetrize_invariant N h hσ S)
  rwa [symmetrize_univ, sum_symmetrize_singleton] at h1

end MotionDepthCodes
