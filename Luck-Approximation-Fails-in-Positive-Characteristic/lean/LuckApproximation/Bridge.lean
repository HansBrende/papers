import LuckApproximation.CertChecks
import LuckApproximation.ConCache
import LuckApproximation.Operator

/-!
# From the construction to the packed rows

`B0_eq`, `B1_eq`: the matrices `B₀`, `B₁` of `Operator.lean`, defined from the construction, have the entries
`b0Nat`, `b1Nat` that the kernel-checked certificate reads from the packed caches. The step is the cache equalities
of `ConCache.lean`.
-/

namespace Luck.Op

open Luck.Data

theorem entryEdge_eq (i j : Fin 110) :
    entryEdge i j = if h : edgeOfNat (i / 10) (j / 10) < 110 then some ⟨_, h⟩ else none := by
  have h := Con.edgeOfNat_eq_cache (blk i) (blk j)
  simp only [entryEdge, Con.edgeOf, blk] at h ⊢
  simp only [h]

theorem coupling_eq (e : Fin 110) (a b : Fin 10) : coupling e a b = (couplingNat e a b : ZMod 3) := by
  rw [coupling, Con.blockNat_eq_cache]

theorem B0_eq (i j : Fin 110) : B0 i j = (b0Nat i j : ZMod 3) := by
  by_cases h : edgeOfNat (i / 10) (j / 10) < 110
  · simp [B0, entryEdge_eq, h, slot, b0Nat, coupling_eq, ZMod.natCast_mod]
  · simp [B0, entryEdge_eq, h, b0Nat]

theorem voltE_eq (e : Fin 110) : voltE e = (voltEdgeNat e : ZMod 3) := by
  by_cases h : edgeGenNat e < 89
  · simp [voltE, edgeGen, voltEdgeNat, h, volt]
  · simp [voltE, edgeGen, voltEdgeNat, h]

theorem B1_eq (i j : Fin 110) : B1 i j = (b1Nat i j : ZMod 3) := by
  by_cases h : edgeOfNat (i / 10) (j / 10) < 110
  · simp [B1, entryEdge_eq, h, slot, b1Nat, coupling_eq, voltE_eq, ZMod.natCast_mod]
  · simp [B1, entryEdge_eq, h, b1Nat]

end Luck.Op
