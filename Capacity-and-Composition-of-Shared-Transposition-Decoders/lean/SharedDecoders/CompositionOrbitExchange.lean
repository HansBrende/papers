import SharedDecoders.Model
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic

/-! # Explicit exchange of two disjoint equivariant orbit families

The completion is an actual permutation of the entire state space. No
equivariant-completion certificate is supplied as a hypothesis.
-/

namespace SharedDecoders

section Exchange

variable {I X : Type*} (u v : I → X)

noncomputable def exchangeFamilies (x : X) : X := by
  classical
  exact if h : ∃ i, u i = x then v h.choose
    else if h : ∃ i, v i = x then u h.choose else x

theorem exchangeFamilies_left (hu : Function.Injective u)
    (i : I) : exchangeFamilies u v (u i) = v i := by
  classical
  unfold exchangeFamilies
  rw [dite_eq_left ⟨i, rfl⟩]
  congr 1
  exact hu (Exists.choose_spec (⟨i, rfl⟩ : ∃ j, u j = u i))

theorem exchangeFamilies_right (hv : Function.Injective v)
    (hdisj : ∀ i j, u i ≠ v j) (i : I) : exchangeFamilies u v (v i) = u i := by
  classical
  unfold exchangeFamilies
  rw [dite_eq_right (by rintro ⟨j, hj⟩; exact hdisj j i hj), dite_eq_left ⟨i, rfl⟩]
  congr 1
  exact hv (Exists.choose_spec (⟨i, rfl⟩ : ∃ j, v j = v i))

theorem exchangeFamilies_outside (x : X)
    (hu : ¬∃ i, u i = x) (hv : ¬∃ i, v i = x) :
    exchangeFamilies u v x = x := by
  classical
  simp [exchangeFamilies, hu, hv]

theorem exchangeFamilies_involutive (hu : Function.Injective u)
    (hv : Function.Injective v) (hdisj : ∀ i j, u i ≠ v j) :
    Function.Involutive (exchangeFamilies u v) := by
  intro x
  by_cases hx : ∃ i, u i = x
  · obtain ⟨i, rfl⟩ := hx
    rw [exchangeFamilies_left u v hu, exchangeFamilies_right u v hv hdisj]
  · by_cases hx' : ∃ i, v i = x
    · obtain ⟨i, rfl⟩ := hx'
      rw [exchangeFamilies_right u v hv hdisj, exchangeFamilies_left u v hu]
    · rw [exchangeFamilies_outside u v x hx hx', exchangeFamilies_outside u v x hx hx']

noncomputable def exchangeEquiv (hu : Function.Injective u)
    (hv : Function.Injective v) (hdisj : ∀ i j, u i ≠ v j) : Equiv.Perm X where
  toFun := exchangeFamilies u v
  invFun := exchangeFamilies u v
  left_inv := exchangeFamilies_involutive u v hu hv hdisj
  right_inv := exchangeFamilies_involutive u v hu hv hdisj

/-- Equivariance follows from the actual two orbit embeddings and their
disjointness, including the complement on which the exchange is the identity. -/
theorem exchangeFamilies_equivariant {G : Type*} [Group G]
    [MulAction G I] [MulAction G X]
    (hu : Function.Injective u) (hv : Function.Injective v)
    (hdisj : ∀ i j, u i ≠ v j)
    (hue : ∀ (g : G) i, u (g • i) = g • u i)
    (hve : ∀ (g : G) i, v (g • i) = g • v i) (g : G) (x : X) :
    exchangeFamilies u v (g • x) = g • exchangeFamilies u v x := by
  by_cases hx : ∃ i, u i = x
  · obtain ⟨i, rfl⟩ := hx
    rw [← hue, exchangeFamilies_left u v hu, exchangeFamilies_left u v hu, hve]
  · by_cases hx' : ∃ i, v i = x
    · obtain ⟨i, rfl⟩ := hx'
      rw [← hve, exchangeFamilies_right u v hv hdisj,
        exchangeFamilies_right u v hv hdisj, hue]
    · have hgu : ¬∃ i, u i = g • x := by
        rintro ⟨i, hi⟩
        apply hx
        refine ⟨g⁻¹ • i, ?_⟩
        rw [hue, hi, inv_smul_smul]
      have hgv : ¬∃ i, v i = g • x := by
        rintro ⟨i, hi⟩
        apply hx'
        refine ⟨g⁻¹ • i, ?_⟩
        rw [hve, hi, inv_smul_smul]
      rw [exchangeFamilies_outside u v _ hgu hgv,
        exchangeFamilies_outside u v _ hx hx']

/-- A permutation of the parameter set transports the exchange through a
permutation of the ambient space. -/
theorem exchangeFamilies_commutes (hu : Function.Injective u)
    (hv : Function.Injective v) (hdisj : ∀ i j, u i ≠ v j)
    (σ : Equiv.Perm X) (τ : Equiv.Perm I)
    (hue : ∀ i, u (τ i) = σ (u i)) (hve : ∀ i, v (τ i) = σ (v i)) (x : X) :
    exchangeFamilies u v (σ x) = σ (exchangeFamilies u v x) := by
  by_cases hx : ∃ i, u i = x
  · obtain ⟨i, rfl⟩ := hx
    rw [← hue, exchangeFamilies_left u v hu, exchangeFamilies_left u v hu, hve]
  · by_cases hx' : ∃ i, v i = x
    · obtain ⟨i, rfl⟩ := hx'
      rw [← hve, exchangeFamilies_right u v hv hdisj,
        exchangeFamilies_right u v hv hdisj, hue]
    · have hgu : ¬∃ i, u i = σ x := by
        rintro ⟨i, hi⟩
        apply hx
        refine ⟨τ.symm i, σ.injective ?_⟩
        rw [← hue, τ.apply_symm_apply, hi]
      have hgv : ¬∃ i, v i = σ x := by
        rintro ⟨i, hi⟩
        apply hx'
        refine ⟨τ.symm i, σ.injective ?_⟩
        rw [← hve, τ.apply_symm_apply, hi]
      rw [exchangeFamilies_outside u v _ hgu hgv,
        exchangeFamilies_outside u v _ hx hx']

/-- The exchange moves exactly two points for each parameter. -/
theorem exchangeFamilies_support_card [Fintype I] [Fintype X]
    (hu : Function.Injective u) (hv : Function.Injective v)
    (hdisj : ∀ i j, u i ≠ v j) :
    Nat.card {x : X // exchangeFamilies u v x ≠ x} = 2 * Fintype.card I := by
  classical
  have hs : Finset.univ.filter (fun x => exchangeFamilies u v x ≠ x) =
      Finset.univ.image u ∪ Finset.univ.image v := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_image]
    constructor
    · intro hx
      by_contra! hn
      exact hx (exchangeFamilies_outside u v x (not_exists.mpr hn.1) (not_exists.mpr hn.2))
    · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · rw [exchangeFamilies_left u v hu]
        exact (hdisj i i).symm
      · rw [exchangeFamilies_right u v hv hdisj]
        exact hdisj i i
  have hd : Disjoint (Finset.univ.image u) (Finset.univ.image v) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hy
    exact hdisj i j hj.symm
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, hs, Finset.card_union_of_disjoint hd,
    Finset.card_image_of_injective _ hu, Finset.card_image_of_injective _ hv,
    Finset.card_univ]
  omega

end Exchange

end SharedDecoders
