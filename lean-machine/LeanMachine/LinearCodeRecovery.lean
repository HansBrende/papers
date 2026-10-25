import LeanMachine.SubspaceRecovery
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Pi

/-! Passing from actual linear code equations to intrinsic coordinate-dual
recovery. Local sections are chosen explicitly, so port ranks cannot increase. -/

namespace LeanMachine.SubspaceRecovery

open Module Finset
open scoped BigOperators

variable {ι K W : Type*} [Fintype ι] [Field K]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  {A : ι → Type*} [∀ v, AddCommGroup (A v)] [∀ v, Module K (A v)]
  [∀ v, FiniteDimensional K (A v)]

/-- Recovery identities on possibly redundant coordinate generators give an
intrinsic arrangement, without assuming that any generator map is injective. -/
theorem recovery_of_generators (R : ∀ v, A v →ₗ[K] W)
    (T : ∀ v u, A v →ₗ[K] A u)
    (hrow : ∀ v, ∑ u, (R u).comp (T v u) = R v) :
    ∃ r : Recovery (fun v => LinearMap.range (R v)),
      (∀ v u, T v u = 0 → r.component v u = 0) ∧
      (∀ v u, finrank K (LinearMap.range (r.component v u)) ≤
        finrank K (LinearMap.range (T v u))) := by
  classical
  have hs : ∀ v, ∃ s : LinearMap.range (R v) →ₗ[K] A v,
      (R v).rangeRestrict.comp s = LinearMap.id := fun v =>
    (R v).rangeRestrict.exists_rightInverse_of_surjective
      (R v).range_rangeRestrict
  choose s hs using hs
  let r : Recovery (fun v => LinearMap.range (R v)) :=
    { component := fun v u => (R u).comp ((T v u).comp (s v))
      target := fun v u => LinearMap.range_comp_le_range _ _
      sum_eq := by
        intro v
        ext x
        simp only [LinearMap.sum_apply, LinearMap.comp_apply, Submodule.subtype_apply]
        have h := LinearMap.congr_fun (hrow v) (s v x)
        simp only [LinearMap.sum_apply, LinearMap.comp_apply] at h
        change (∑ u, R u (T v u (s v x))) = (x : W)
        rw [h]
        exact congrArg Subtype.val (LinearMap.congr_fun (hs v) x) }
  refine ⟨r, ?_, ?_⟩
  · intro v u hz
    change (R u).comp ((T v u).comp (s v)) = 0
    simp [hz]
  · intro v u
    change finrank K (LinearMap.range ((R u).comp ((T v u).comp (s v)))) ≤ _
    rw [LinearMap.range_comp]
    exact (Submodule.finrank_map_le _ _).trans
      (Submodule.finrank_mono (LinearMap.range_comp_le_range (s v) (T v u)))

/-- The actual coordinate projection of a code, with its image dimension. -/
def coordinate (C : Submodule K (∀ v, A v)) (v : ι) : C →ₗ[K] A v :=
  (LinearMap.proj v).comp C.subtype

@[simp] theorem coordinate_apply (C : Submodule K (∀ v, A v)) (v : ι) (x : C) :
    coordinate C v x = x.val v := rfl

theorem coordinate_duals_span (C : Submodule K (∀ v, A v)) :
    (⨆ v, LinearMap.range (coordinate C v).dualMap) = ⊤ := by
  simp_rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker]
  rw [← Subspace.dualAnnihilator_iInf_eq]
  have hker : (⨅ v, LinearMap.ker (coordinate C v)) = ⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro x hx
    apply Subtype.ext
    funext v
    exact ((iInf_le (fun v => LinearMap.ker (coordinate C v)) v) hx :
      coordinate C v x = 0)
  rw [hker, Submodule.dualAnnihilator_bot]

/-- Every graph-supported block code gives recoveries on the duals of its
actual coordinate images. This construction preserves zeros and bounds each
intrinsic port rank by the rank of the specified block. -/
theorem code_dual_recovery (C : Submodule K (∀ v, A v))
    (T : ∀ v u, A u →ₗ[K] A v)
    (hrow : ∀ x ∈ C, ∀ v, ∑ u, T v u (x u) = x v) :
    ∃ r : Recovery (fun v => LinearMap.range (coordinate C v).dualMap),
      (∀ v u, T v u = 0 → r.component v u = 0) ∧
      (∀ v u, finrank K (LinearMap.range (r.component v u)) ≤
        finrank K (LinearMap.range (T v u))) := by
  have hid : ∀ v, ∑ u, ((coordinate C u).dualMap).comp (T v u).dualMap =
      (coordinate C v).dualMap := by
    intro v
    ext f x
    simp only [LinearMap.sum_apply, LinearMap.comp_apply]
    change (∑ u, f (T v u (x.val u))) = f (x.val v)
    rw [← map_sum, hrow x.val x.property v]
  obtain ⟨r, hz, hr⟩ := recovery_of_generators
    (fun v => (coordinate C v).dualMap) (fun v u => (T v u).dualMap) hid
  refine ⟨r, ?_, ?_⟩
  · intro v u h
    apply hz v u
    ext f x
    simp [h]
  · intro v u
    simpa only [LinearMap.finrank_range_dualMap_eq_finrank_range] using hr v u

/-- The block operator associated with prescribed local recovery maps. -/
def blockOperator (T : ∀ v u, A u →ₗ[K] A v) :
    (∀ v, A v) →ₗ[K] (∀ v, A v) :=
  LinearMap.pi (fun v => ∑ u, (T v u).comp (LinearMap.proj u))

@[simp] theorem blockOperator_apply (T : ∀ v u, A u →ₗ[K] A v)
    (x : ∀ v, A v) (v : ι) : blockOperator T x v = ∑ u, T v u (x u) := by
  simp [blockOperator]

@[simp] theorem blockOperator_single [DecidableEq ι]
    (T : ∀ v u, A u →ₗ[K] A v) (u v : ι) (x : A u) :
    blockOperator T (LinearMap.single K A u x) v = T v u x := by
  simp only [blockOperator_apply, LinearMap.single_apply, LinearMap.apply_single,
    Fintype.sum_pi_single']

theorem block_kernel_recovery (T : ∀ v u, A u →ₗ[K] A v)
    (x : ∀ v, A v) (hx : x ∈ LinearMap.ker (LinearMap.id - blockOperator T)) (v : ι) :
    ∑ u, T v u (x u) = x v := by
  have h := congrFun (LinearMap.mem_ker.mp hx) v
  have he : x v - ∑ u, T v u (x u) = 0 := by
    simpa only [LinearMap.sub_apply, LinearMap.id_apply, Pi.sub_apply,
      blockOperator_apply, Pi.zero_apply] using h
  exact (sub_eq_zero.mp he).symm

end LeanMachine.SubspaceRecovery
