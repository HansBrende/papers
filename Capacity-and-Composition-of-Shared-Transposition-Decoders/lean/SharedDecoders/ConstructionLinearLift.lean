import SharedDecoders.ConstructionCRT
import SharedDecoders.CapacityLinearization

/-! # Preservation of linear class rules by the cyclic lift -/

namespace SharedDecoders

variable {F A G κ : Type*} [Field F] [AddCommGroup A] [Module F A]
  [AddCommGroup G] [Fintype G] {m s : ℕ}

def liftedLinearDecoder (f : κ → State s A →ₗ[F] (ZMod s → A)) (a : κ) :
    LiftState G (ZMod s) A →ₗ[F] (G × ZMod s → A) where
  toFun := liftedDecoder (F := F) (fun j => f j) a
  map_add' X Y := by
    funext ar
    simp only [liftedDecoder, map_add, Pi.add_apply, Pi.sub_apply]
    abel
  map_smul' k X := by
    funext ar
    simp only [liftedDecoder, map_smul, Pi.smul_apply, Pi.sub_apply, smul_sub, smul_add,
      RingHom.id_apply]

variable [NeZero m] [NeZero s]

def cyclicLinearDecoder (hc : m.Coprime s)
    (f : κ → State s A →ₗ[F] (ZMod s → A)) (a : κ) :
    State (m * s) A →ₗ[F] (ZMod (m * s) → A) where
  toFun Y i := liftedLinearDecoder (G := ZMod m) f a
    (crtStateEquiv (F := F) hc Y) (ZMod.chineseRemainder hc i)
  map_add' X Y := by funext i; simp only [map_add, Pi.add_apply]
  map_smul' k X := by funext i; simp only [map_smul, Pi.smul_apply, RingHom.id_apply]

omit [NeZero s] in
theorem IsLinearSharedCode.cyclicLiftCode {p : ZMod s → κ}
    {C : Submodule F (State s A)} (h : IsLinearSharedCode p C)
    (hc : m.Coprime s) (hm : (m : F) ≠ 0) :
    IsLinearSharedCode (liftedPartition hc p) (cyclicLiftCode hc C) := by
  obtain ⟨f, hf⟩ := h
  have hG : (Fintype.card (ZMod m) : F) ≠ 0 := by simpa only [ZMod.card] using hm
  refine ⟨cyclicLinearDecoder hc f, ?_⟩
  intro X hX c
  have hh := liftedDecoder_correct (G := ZMod m) (fun j => f j) hf hG
    (crtStateEquiv (F := F) hc X) hX
    (ZMod.chineseRemainder hc c).1 (ZMod.chineseRemainder hc c).2
  funext i
  have hrow := congrFun hh (ZMod.chineseRemainder hc i)
  change X c i = liftedDecoder (F := F) (fun j => f j) (p (ZMod.chineseRemainder hc c).2)
    (crtStateEquiv (F := F) hc (rot c X)) (ZMod.chineseRemainder hc i)
  rw [crtStateEquiv_rot]
  simpa only [crtStateEquiv_apply, RingEquiv.symm_apply_apply, Prod.mk.eta] using hrow

/-- Complete cyclic-lift endpoint: actual cyclic indices, unchanged nonempty
classes, exact dimension, and preservation of linear class decoders. -/
theorem cyclic_lift [FiniteDimensional F A] {p : ZMod s → κ}
    {C : Submodule F (State s A)} (h : IsSharedCode F p C)
    (hp : Function.Surjective p) (hc : m.Coprime s) (hm : (m : F) ≠ 0) :
    IsSharedCode F (liftedPartition hc p) (cyclicLiftCode hc C) ∧
    Function.Surjective (liftedPartition hc p) ∧
    2 * Module.finrank F (cyclicLiftCode hc C) + m * (s * s * Module.finrank F A) =
      (m * s) * (m * s) * Module.finrank F A + 2 * m * Module.finrank F C ∧
    (IsLinearSharedCode p C →
      IsLinearSharedCode (liftedPartition hc p) (cyclicLiftCode hc C)) :=
  ⟨h.cyclicLiftCode hc hm, liftedPartition_surjective hc hp,
    two_mul_finrank_cyclicLiftCode hc hm C, fun hlin => hlin.cyclicLiftCode hc hm⟩

end SharedDecoders
