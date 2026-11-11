import SharedDecoders.CapacitySubcodeTransport
import SharedDecoders.ConstructionSymmetric
import Mathlib.Algebra.Field.ZMod

/-! # Repeating actual binary codes and the symmetric good source -/

namespace SharedDecoders.CapacitySubcode

open Module

variable {F A κ : Type*} [Field F] [AddCommGroup A] [Module F A] {d q : ℕ}

noncomputable def repeatMap (C : Submodule F (State d A)) :
    (Fin q → C) →ₗ[F] State d (Fin q → A) where
  toFun x i j l := (x l).val i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem repeatMap_injective (C : Submodule F (State d A)) :
    Function.Injective (repeatMap (q := q) C) := by
  intro x y h
  funext l
  apply Subtype.ext
  exact funext (fun i => funext (fun j => congrFun (congrFun (congrFun h i) j) l))

noncomputable def repeatCode (C : Submodule F (State d A)) (q : ℕ) :
    Submodule F (State d (Fin q → A)) := LinearMap.range (repeatMap C)

theorem finrank_repeatCode [NeZero d] [FiniteDimensional F A]
    (C : Submodule F (State d A)) (q : ℕ) :
    finrank F (repeatCode C q) = q * finrank F C := by
  rw [repeatCode, LinearMap.finrank_range_of_inj (repeatMap_injective C)]
  simp [Module.finrank_pi_fintype]

theorem shared_repeat {p : ZMod d → κ} {C : Submodule F (State d A)}
    (hC : IsSharedCode F p C) (q : ℕ) : IsSharedCode F p (repeatCode C q) := by
  obtain ⟨f, hf⟩ := hC
  refine ⟨fun j X t l => f j (fun r c => X r c l) t, ?_⟩
  rintro X ⟨x, rfl⟩ c
  funext t l
  exact congrFun (hf (x l) (x l).property c) t

/-- Repetition is within the binary code; it never extends a nonlinear rule to
new coefficient-field values. -/
theorem repeat_binary_code [NeZero d] {b : ℕ} {p : ZMod d → κ}
    (C : Submodule (ZMod 2) (State d (Fin b → ZMod 2)))
    (hC : IsSharedCode (ZMod 2) p C) (q : ℕ) :
    ∃ D : Submodule (ZMod 2) (State d (Fin (q * b) → ZMod 2)),
      IsSharedCode (ZMod 2) p D ∧ finrank (ZMod 2) D = q * finrank (ZMod 2) C := by
  let e : (Fin q → Fin b → ZMod 2) ≃ₗ[ZMod 2] (Fin (q * b) → ZMod 2) :=
    LinearEquiv.ofFinrankEq _ _ (by simp [Module.finrank_pi_fintype])
  refine ⟨(repeatCode C q).map (entryEquiv e).toLinearMap,
    shared_map (shared_repeat hC q) e, ?_⟩
  rw [(entryEquiv e).finrank_map_eq, finrank_repeatCode]

theorem symmetric_shared (p : ZMod d → κ) :
    IsSharedCode F p (symmetricSpace (F := F) (A := A) (I := ZMod d)) := by
  refine ⟨fun _ Y j => Y j 0, ?_⟩
  intro X hX c
  funext j
  change X c j = X j (0 + c)
  simpa only [zero_add] using hX c j

end SharedDecoders.CapacitySubcode
