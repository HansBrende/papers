import SharedDecoders.ConstructionSpectral
import SharedDecoders.ConstructionLinearLift

/-! # Exact linear capacity of a split periodic lift -/

namespace SharedDecoders

open Module
open scoped BigOperators

variable {F κ : Type*} [Field F] {m s : ℕ} [NeZero m] [NeZero s]

omit [NeZero s] in
theorem diagonalKernel_isLinearSharedCode (χ : AddChar (ZMod m) F)
    (hχ : Function.Injective χ) (p : ZMod s → κ)
    (f : κ → LiftState (ZMod m) (ZMod s) F →ₗ[F] (ZMod m × ZMod s → F))
    (j : Fin m) :
    IsLinearSharedCode p (diagonalKernel seedSwapEquiv (compressedRule χ hχ p f) j) := by
  refine ⟨compressedDecoder χ hχ f j j j, ?_⟩
  intro X hX c
  have hh := LinearMap.mem_ker.mp hX
  have heq : seedSwapEquiv (F := F) X = compressedRule χ hχ p f j j j X := sub_eq_zero.mp hh
  funext r
  exact congrFun (congrFun heq r) c

theorem productLinear_capacity_upper {p : ZMod s → κ}
    {C : Submodule F (LiftState (ZMod m) (ZMod s) F)}
    (hC : IsProductLinearSharedCode p C)
    (χ : AddChar (ZMod m) F) (hχ : Function.Injective χ) :
    2 * finrank F C + m * (s * s) ≤ (m * s) * (m * s) +
      2 * m * dimensionCapacity (IsLinearSharedCode (F := F) (A := F) p) := by
  obtain ⟨f, hf⟩ := hC
  let e := outerFourierEquiv (I := ZMod s) χ hχ
  have hle : C.comap e.toLinearMap ≤ blockAgreement seedSwapEquiv (compressedRule χ hχ p f) := by
    intro X hX
    exact compressedAgreement χ hχ p f X (hf (e X) hX)
  have hdim : finrank F C ≤ Fintype.card (UpperBlocks m) * (s * s) +
      m * dimensionCapacity (IsLinearSharedCode (F := F) (A := F) p) := by
    calc
      _ = finrank F (C.comap e.toLinearMap) := (e.ofSubmodule' C).finrank_eq.symm
      _ ≤ finrank F (blockAgreement seedSwapEquiv (compressedRule χ hχ p f)) := Submodule.finrank_mono hle
      _ ≤ Fintype.card (UpperBlocks m) * finrank F (State s F) +
          ∑ j, finrank F (diagonalKernel seedSwapEquiv (compressedRule χ hχ p f) j) :=
        finrank_blockAgreement_le _ _
      _ ≤ Fintype.card (UpperBlocks m) * (s * s) +
          ∑ _j : Fin m, dimensionCapacity (IsLinearSharedCode (F := F) (A := F) p) := by
        rw [finrank_state, Module.finrank_self, mul_one]
        apply Nat.add_le_add_left
        exact Finset.sum_le_sum (fun j _ => le_dimensionCapacity
          (diagonalKernel_isLinearSharedCode χ hχ p f j))
      _ = _ := by simp
  have hu := two_mul_card_upperBlocks m
  nlinarith

def crtLinearDecoder (hc : m.Coprime s)
    (f : κ → State (m * s) F →ₗ[F] (ZMod (m * s) → F)) (J : κ) :
    LiftState (ZMod m) (ZMod s) F →ₗ[F] (ZMod m × ZMod s → F) where
  toFun Y ar := f J ((crtStateEquiv (F := F) hc).symm Y) ((ZMod.chineseRemainder hc).symm ar)
  map_add' X Y := by funext ar; simp only [map_add, Pi.add_apply]
  map_smul' k X := by funext ar; simp only [map_smul, Pi.smul_apply, RingHom.id_apply]

omit [NeZero m] [NeZero s] in
theorem IsLinearSharedCode.toProduct {p : ZMod s → κ}
    {C : Submodule F (State (m * s) F)} (hc : m.Coprime s)
    (hC : IsLinearSharedCode (liftedPartition hc p) C) :
    IsProductLinearSharedCode p (C.map (crtStateEquiv (F := F) hc).toLinearMap) := by
  obtain ⟨f, hf⟩ := hC
  refine ⟨crtLinearDecoder hc f, ?_⟩
  intro Y hY u v
  obtain ⟨X, hX, rfl⟩ := hY
  let c := (ZMod.chineseRemainder hc).symm (u,v)
  have hrot : crtStateEquiv (F := F) hc (rot c X) =
      liftRot u v (crtStateEquiv (F := F) hc X) := by
    simpa only [c, RingEquiv.apply_symm_apply] using crtStateEquiv_rot (F := F) hc c X
  have hh := hf X hX c
  funext ar
  have hrow := congrFun hh ((ZMod.chineseRemainder hc).symm ar)
  change X c ((ZMod.chineseRemainder hc).symm ar) =
    f (p v) ((crtStateEquiv (F := F) hc).symm (liftRot u v (crtStateEquiv (F := F) hc X)))
      ((ZMod.chineseRemainder hc).symm ar)
  rw [← hrot, LinearEquiv.symm_apply_apply]
  simpa only [liftedPartition, c, RingEquiv.apply_symm_apply] using hrow

theorem periodic_linear_source_upper {p : ZMod s → κ}
    {C : Submodule F (State (m * s) F)} (hc : m.Coprime s)
    (hC : IsLinearSharedCode (liftedPartition hc p) C)
    (χ : AddChar (ZMod m) F) (hχ : Function.Injective χ) :
    2 * finrank F C + m * (s * s) ≤ (m * s) * (m * s) +
      2 * m * dimensionCapacity (IsLinearSharedCode (F := F) (A := F) p) := by
  have hh := productLinear_capacity_upper (hC.toProduct hc) χ hχ
  rwa [(crtStateEquiv (F := F) hc).finrank_map_eq C] at hh

theorem periodic_linear_capacity (p : ZMod s → κ) (hc : m.Coprime s) (hm : (m : F) ≠ 0)
    (χ : AddChar (ZMod m) F) (hχ : Function.Injective χ) :
    2 * dimensionCapacity (IsLinearSharedCode (F := F) (A := F) (liftedPartition hc p)) +
      m * (s * s) = (m * s) * (m * s) +
        2 * m * dimensionCapacity (IsLinearSharedCode (F := F) (A := F) p) := by
  obtain ⟨C, hC, hdimC⟩ := dimensionCapacity_attained
    (IsLinearSharedCode (F := F) (A := F) (liftedPartition hc p)) (isLinearSharedCode_bot _)
  have hu := periodic_linear_source_upper hc hC χ hχ
  obtain ⟨D, hD, hdimD⟩ := dimensionCapacity_attained
    (IsLinearSharedCode (F := F) (A := F) p) (isLinearSharedCode_bot _)
  have hl := le_dimensionCapacity (hD.cyclicLiftCode hc hm)
  have heq := two_mul_finrank_cyclicLiftCode hc hm D
  rw [Module.finrank_self, mul_one, mul_one] at heq
  rw [hdimC] at hu
  rw [hdimD] at heq
  omega

end SharedDecoders
