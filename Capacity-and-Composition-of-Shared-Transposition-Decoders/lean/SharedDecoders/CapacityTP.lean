import SharedDecoders.Model
import SwapRigidity.Pigeonhole
import SwapRigidity.ClassUniform

/-!
# Translate bounds for deterministic shared decoders

The entry type is an arbitrary finite-dimensional module, so vector lanes may be
coupled. Only the source is linear. The proof reuses the multi-preimage dimension
inequality of `SwapRigidity.Pigeonhole`; decoder linearity is not assumed.
-/

namespace SharedDecoders

open Module

variable {F A κ : Type*} [Field F] [AddCommGroup A] [Module F A]
  {d : ℕ}

abbrev Link (p : ZMod d → κ) (Δ : Finset (ZMod d)) := SwapRigidity.Link p Δ

namespace IsSharedCode

variable {p : ZMod d → κ} {C : Submodule F (State d A)}

theorem row_eq_of_rot_mem (h : IsSharedCode F p C)
    {X : State d A} {c e s t : ZMod d}
    (hs : rot s X ∈ C) (ht : rot t X ∈ C)
    (hp : p c = p e) (hc : c + s = e + t) (j : ZMod d) :
    X e (j + t) = X c (j + s) := by
  obtain ⟨f, hf⟩ := h
  have h₁ := hf _ hs c
  have h₂ := hf _ ht e
  rw [rot_rot, hc] at h₁
  rw [rot_rot, ← hp] at h₂
  exact congrFun (h₂.trans h₁.symm) j

theorem row_eq_zero_iff_of_eqvGen (h : IsSharedCode F p C)
    {Δ : Finset (ZMod d)} {X : State d A}
    (hX : ∀ s ∈ Δ, rot s X ∈ C) {c e : ZMod d}
    (hce : Relation.EqvGen (Link p Δ) c e) : X c = 0 ↔ X e = 0 := by
  induction hce with
  | rel c e hce =>
      obtain ⟨hp, s, hs, t, ht, hsum⟩ := hce
      have key := h.row_eq_of_rot_mem (hX s hs) (hX t ht) hp hsum
      constructor
      · intro hc
        funext j
        have hj := key (j - t)
        rw [sub_add_cancel] at hj
        rw [hj, hc]
        rfl
      · intro he
        funext j
        have hj := key (j - s)
        rw [sub_add_cancel] at hj
        rw [← hj, he]
        rfl
  | refl _ => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

end IsSharedCode

variable [NeZero d] [FiniteDimensional F A]

theorem finrank_state : finrank F (State d A) = d * d * finrank F A := by
  simp [State, Module.finrank_pi_fintype, ZMod.card, mul_assoc]

def commonPreimage (C : Submodule F (State d A)) (Δ : Finset (ZMod d)) :
    Submodule F (State d A) := ⨅ s ∈ Δ, C.comap (rotLinear F s)

omit [NeZero d] [FiniteDimensional F A] in
@[simp] theorem mem_commonPreimage {C : Submodule F (State d A)}
    {Δ : Finset (ZMod d)} {X : State d A} :
    X ∈ commonPreimage C Δ ↔ ∀ s ∈ Δ, rot s X ∈ C := by
  simp [commonPreimage, Submodule.mem_iInf, Submodule.mem_comap]

namespace IsSharedCode

variable {p : ZMod d → κ} {C : Submodule F (State d A)}

/-- The general translate bound for arbitrary deterministic shared decoders. -/
theorem finrank_le (h : IsSharedCode F p C) {Δ : Finset (ZMod d)}
    (hΔ : Δ.Nonempty) {S : Finset (ZMod d)}
    (hS : ∀ c, ∃ s ∈ S, Relation.EqvGen (Link p Δ) c s) :
    Δ.card * finrank F C ≤
      (Δ.card - 1) * (d * d * finrank F A) + d * S.card * finrank F A := by
  classical
  let C' := commonPreimage C Δ
  have hcount : Δ.card * finrank F C + d * d * finrank F A ≤
      Δ.card * (d * d * finrank F A) + finrank F C' := by
    have hh := SwapRigidity.card_mul_finrank_add_le_iInf_comap Δ C
      (fun s => rotLinear F s)
    rw [finrank_state] at hh
    exact hh
  let res : C' →ₗ[F] (S → ZMod d → A) :=
    { toFun := fun X s => (X : State d A) s
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective res := by
    rw [injective_iff_map_eq_zero]
    intro X hX
    apply Subtype.ext
    funext c
    obtain ⟨s, hs, hcs⟩ := hS c
    have hm : ∀ t ∈ Δ, rot t (X : State d A) ∈ C :=
      mem_commonPreimage.mp X.2
    exact (h.row_eq_zero_iff_of_eqvGen hm hcs).2 (congrFun hX ⟨s, hs⟩)
  have hdim : finrank F C' ≤ d * S.card * finrank F A := by
    have hh := LinearMap.finrank_le_finrank_of_injective hinj
    have hpi : finrank F (S → ZMod d → A) = d * S.card * finrank F A := by
      simp [Module.finrank_pi_fintype, ZMod.card, mul_left_comm, mul_assoc]
    rwa [hpi] at hh
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hΔ.card_pos.ne'
  rw [hk, Nat.succ_eq_add_one, add_mul, one_mul] at hcount
  rw [hk, Nat.succ_eq_add_one, Nat.add_sub_cancel]
  nlinarith

end IsSharedCode

end SharedDecoders
