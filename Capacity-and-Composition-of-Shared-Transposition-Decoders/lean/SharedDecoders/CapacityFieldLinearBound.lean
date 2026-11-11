import SharedDecoders.CapacityFieldLinearComponents

/-! # The active-row bound for extension-linear sources

Each active receiver contributes an independent extension-linear functional
annihilating the representative view.  The decoders are only binary-linear.
-/

namespace SharedDecoders.CapacityFieldLinear

open Module CapacityIntervals
open scoped BigOperators

variable {d : ℕ} [NeZero d] {I : Type*}

noncomputable def twist (s : ZMod d) (x : I → Extension d) : I → Extension d :=
  fun i => phase d s (x i)

theorem twist_add (s t : ZMod d) (x : I → Extension d) :
    twist s (twist t x) = twist (s+t) x := by
  funext i
  exact (AlgEquiv.mul_apply (phase d s) (phase d t) (x i)).symm.trans
    (by rw [← phase_add]; rfl)

@[simp] theorem twist_zero (x : I → Extension d) : twist (0 : ZMod d) x = x := by
  funext i
  simp [twist]

@[simp] theorem twist_neg_twist (s : ZMod d) (x : I → Extension d) :
    twist (-s) (twist s x) = x := by rw [twist_add, neg_add_cancel, twist_zero]

@[simp] theorem twist_twist_neg (s : ZMod d) (x : I → Extension d) :
    twist s (twist (-s) x) = x := by rw [twist_add, add_neg_cancel, twist_zero]

theorem phase_neg_phase (s : ZMod d) (a : Extension d) :
    phase d (-s) (phase d s a) = a := by
  rw [← AlgEquiv.mul_apply, ← phase_add, neg_add_cancel, phase_zero]
  rfl

theorem phase_phase_neg (s : ZMod d) (a : Extension d) :
    phase d s (phase d (-s) a) = a := by
  rw [← AlgEquiv.mul_apply, ← phase_add, add_neg_cancel, phase_zero]
  rfl

theorem twist_smul (s : ZMod d) (a : Extension d) (x : I → Extension d) :
    twist s (a • x) = phase d s a • twist s x := by
  funext i
  exact map_mul (phase d s) a (x i)

theorem smul_twist (s : ZMod d) (a : Extension d) (x : I → Extension d) :
    a • twist s x = twist s (phase d (-s) a • x) := by
  rw [twist_smul, phase_phase_neg]

noncomputable def twistFunctional (s : ZMod d)
    (f : (I → Extension d) →ₗ[Extension d] Extension d) :
    (I → Extension d) →ₗ[Extension d] Extension d where
  toFun x := (phase d s).symm (f (twist s x))
  map_add' x y := by
    have he : twist s (x+y) = twist s x + twist s y := by ext i; exact map_add _ _ _
    rw [he, map_add, map_add]
  map_smul' a x := by
    rw [twist_smul, map_smul]
    simp only [smul_eq_mul, map_mul, AlgEquiv.symm_apply_apply, RingHom.id_apply]

theorem component_on_view (K : Submodule (Extension d) (I → Extension d))
    (f : (I → Extension d) →ₗ[Bit] Extension d) (c : ZMod d) (i : I)
    (hf : ∀ x ∈ K, f (twist c x) = x i) (x : I → Extension d) (hx : x ∈ K)
    (s : ZMod d) :
    component d f s (twist c x) = if s = -c then (phase d s).symm (x i) else 0 := by
  apply component_of_scalarTest
  intro a
  rw [smul_twist, hf _ (K.smul_mem _ hx)]
  rfl

theorem component_annihilates_view (K : Submodule (Extension d) (I → Extension d))
    (f : (I → Extension d) →ₗ[Bit] Extension d) (r : ZMod d)
    (hf : ∀ x ∈ K, f (twist r x) = 0) (s : ZMod d) :
    twistFunctional r (component d f s) ∈ K.dualAnnihilator := by
  rw [Submodule.mem_dualAnnihilator]
  intro x hx
  change (phase d r).symm (component d f s (twist r x)) = 0
  have hz := component_zero_of_scalarTest_zero d f (twist r x) (fun a => by
    rw [smul_twist]
    exact hf _ (K.smul_mem _ hx)) s
  rw [hz, map_zero]

/-- A single shared class contributes one independent annihilator for every
active row in that class. All data are actual decoder equations on `K`. -/
theorem active_class_finrank_bound [Fintype I]
    (K : Submodule (Extension d) (I → Extension d))
    (f : (I → Extension d) →ₗ[Bit] Extension d) (r : ZMod d)
    (receiver : I → ZMod d) (hinj : Function.Injective receiver) (J : Finset I)
    (hzero : ∀ x ∈ K, f (twist r x) = 0)
    (hcorrect : ∀ i ∈ J, ∀ x ∈ K, f (twist (receiver i) x) = x i)
    (hactive : ∀ i ∈ J, ∃ x ∈ K, x i ≠ 0) :
    J.card + finrank (Extension d) K ≤ Fintype.card I := by
  classical
  let g (i : J) := twistFunctional r (component d f (-receiver i.1))
  have hmem (i : J) : g i ∈ K.dualAnnihilator :=
    component_annihilates_view K f r hzero _
  have hli : LinearIndependent (Extension d) g := by
    rw [Fintype.linearIndependent_iff]
    intro a ha i
    obtain ⟨x, hx, hxi⟩ := hactive i.1 i.2
    let y := twist (-r) (twist (receiver i.1) x)
    have heval (j : J) :
        g j y = if j=i then (phase d r).symm ((phase d (-receiver i.1)).symm (x i.1)) else 0 := by
      change (phase d r).symm (component d f (-receiver j.1)
        (twist r (twist (-r) (twist (receiver i.1) x)))) = _
      rw [twist_twist_neg, component_on_view K f (receiver i.1) i.1
        (hcorrect i.1 i.2) x hx]
      by_cases hji : j=i
      · subst j
        simp
      · have hne : -receiver j.1 ≠ -receiver i.1 := by
          intro hh
          exact hji (Subtype.ext (hinj (neg_inj.mp hh)))
        simp [hji, hne]
    have he := congrArg (fun l : (I → Extension d) →ₗ[Extension d] Extension d => l y) ha
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.zero_apply,
      heval, smul_eq_mul] at he
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at he
    have hn : (phase d r).symm ((phase d (-receiver i.1)).symm (x i.1)) ≠ 0 := by
      intro hh
      apply hxi
      exact (phase d (-receiver i.1)).symm.injective
        ((phase d r).symm.injective (hh.trans (map_zero _).symm) |>.trans (map_zero _).symm)
    exact (mul_eq_zero.mp he).resolve_right hn
  let g' (i : J) : K.dualAnnihilator := ⟨g i, hmem i⟩
  have hli' : LinearIndependent (Extension d) g' :=
    LinearIndependent.of_comp K.dualAnnihilator.subtype hli
  have hcard := hli'.fintype_card_le_finrank
  have hdim := Subspace.finrank_add_finrank_dualAnnihilator_eq K
  simp only [Fintype.card_coe, Module.finrank_fintype_fun_eq_card] at hcard hdim
  omega

end SharedDecoders.CapacityFieldLinear
