import TransposeFollowup.XorComponentCount
import TransposeFollowup.PacketDistanceConsequences

/-! The path/cycle consequence, with an explicit uniform square-root error.
The theorem covers every subgraph of a cycle, so includes the standard path
without needing a separate proof or silently assuming connectedness. -/

namespace TransposeFollowup

open Classical
set_option autoImplicit false

namespace RecodedXorCode

variable {n b B : ℕ} (C : RecodedXorCode n b B)

/-- One radius and one real ball-volume budget suffice. The error coefficient
need not be integral. -/
theorem broadcast_bound_of_ball_budget_real (hc : C.Correct) (G : SimpleGraph (Fin n))
    (hG : C.LocalTo G) (k q : ℕ) (e : ℝ)
    (hballs : ∀ i, (nearVertices G k i).card ≤ q)
    (hbudget : (n : ℝ) + k * q ≤ (k + 1) * e) :
    (n * n * b : ℕ) ≤ (B : ℝ) + (b : ℝ) * n * e :=
  PacketDistanceBudget.broadcast_bound_of_ball_budget_real G
    (C.toRecodedPacketCode.distanceBudget
      (C.toRecodedPacketCode_correct hc) G (C.toRecodedPacketCode_local G hG)) k q e hballs hbudget

/-- Integral specialization of the shared real ball-budget estimate. -/
theorem broadcast_bound_of_ball_budget (hc : C.Correct) (G : SimpleGraph (Fin n))
    (hG : C.LocalTo G) (k q e : ℕ)
    (hballs : ∀ i, (nearVertices G k i).card ≤ q)
    (hbudget : n + k * q ≤ (k + 1) * e) :
    n * n * b ≤ B + b * n * e :=
  PacketDistanceBudget.broadcast_bound_of_ball_budget G
    (C.toRecodedPacketCode.distanceBudget
      (C.toRecodedPacketCode_correct hc) G (C.toRecodedPacketCode_local G hG)) k q e hballs hbudget

theorem linear_ball_broadcast_bound_nat (hc : C.Correct) (G : SimpleGraph (Fin n))
    (hG : C.LocalTo G)
    (hballs : ∀ ell, 1 ≤ ell → ∀ i, (nearVertices G ell i).card ≤ 2 * ell - 1) (hn : 0 < n) :
    n * n * b ≤ B + b * n * (3 * Nat.sqrt n) :=
  PacketDistanceBudget.linear_ball_broadcast_bound_nat G
    (C.toRecodedPacketCode.distanceBudget
      (C.toRecodedPacketCode_correct hc) G (C.toRecodedPacketCode_local G hG)) hballs hn

/-- The shifted square-root error is no larger than the former square-root
error. This certifies that the new finite bound implies the previous one. -/
theorem linear_ball_error_le_sqrt (n : ℕ) (hn : 0 < n) :
    Real.sqrt (8 * ((n : ℝ) + 3)) - 4 ≤ Real.sqrt (8 * (n : ℝ)) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hs : (1 : ℝ) ≤ Real.sqrt (8 * (n : ℝ)) :=
    Real.one_le_sqrt.mpr (by nlinarith)
  have hsq := Real.sq_sqrt (show 0 ≤ 8 * (n : ℝ) by positivity)
  have hle : Real.sqrt (8 * ((n : ℝ) + 3)) ≤ Real.sqrt (8 * (n : ℝ)) + 4 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith
  linarith

/-- Finite path/cycle error bn(sqrt(8(n+3))-4), retaining the exact ball cap
2k-1 and the divisor k+1. All recoding and decoding assumptions are unchanged. -/
theorem linear_ball_broadcast_lower_bound (hc : C.Correct) (G : SimpleGraph (Fin n))
    (hG : C.LocalTo G)
    (hballs : ∀ ell, 1 ≤ ell → ∀ i, (nearVertices G ell i).card ≤ 2 * ell - 1) (hn : 0 < n) :
    (B : ℝ) ≥ (n * n * b : ℕ) -
      (b : ℝ) * n * (Real.sqrt (8 * ((n : ℝ) + 3)) - 4) :=
  PacketDistanceBudget.linear_ball_broadcast_lower_bound G
    (C.toRecodedPacketCode.distanceBudget
      (C.toRecodedPacketCode_correct hc) G (C.toRecodedPacketCode_local G hG)) hballs hn

/-- Includes arbitrary row labels and arbitrary subgraphs of a cycle: the
placement in the cycle need only be an injective graph homomorphism. -/
theorem cycle_embedding_broadcast_lower_bound (hc : C.Correct) (G : SimpleGraph (Fin n))
    (hG : C.LocalTo G) {m : ℕ} [NeZero m]
    (f : G →g SimpleGraph.cycleGraph m) (hf : Function.Injective f) (hn : 0 < n) :
    (B : ℝ) ≥ (n * n * b : ℕ) - (b : ℝ) * n * (Real.sqrt (8 * ((n : ℝ) + 3)) - 4) :=
  PacketDistanceBudget.cycle_embedding_broadcast_lower_bound G
    (C.toRecodedPacketCode.distanceBudget
      (C.toRecodedPacketCode_correct hc) G (C.toRecodedPacketCode_local G hG)) f hf hn

theorem subcycle_broadcast_lower_bound (hc : C.Correct) (G : SimpleGraph (Fin n))
    (hG : C.LocalTo G) (hcycle : G ≤ SimpleGraph.cycleGraph n) (hn : 0 < n) :
    (B : ℝ) ≥ (n * n * b : ℕ) - (b : ℝ) * n * (Real.sqrt (8 * ((n : ℝ) + 3)) - 4) :=
  PacketDistanceBudget.subcycle_broadcast_lower_bound G
    (C.toRecodedPacketCode.distanceBudget
      (C.toRecodedPacketCode_correct hc) G (C.toRecodedPacketCode_local G hG)) hcycle hn

theorem cycle_broadcast_lower_bound (hc : C.Correct)
    (hG : C.LocalTo (SimpleGraph.cycleGraph n)) (hn : 0 < n) :
    (B : ℝ) ≥ (n * n * b : ℕ) - (b : ℝ) * n * (Real.sqrt (8 * ((n : ℝ) + 3)) - 4) :=
  C.toRecodedPacketCode.cycle_broadcast_lower_bound (C.toRecodedPacketCode_correct hc)
    (C.toRecodedPacketCode_local (SimpleGraph.cycleGraph n) hG) hn

theorem path_broadcast_lower_bound (hc : C.Correct)
    (hG : C.LocalTo (SimpleGraph.pathGraph n)) (hn : 0 < n) :
    (B : ℝ) ≥ (n * n * b : ℕ) - (b : ℝ) * n * (Real.sqrt (8 * ((n : ℝ) + 3)) - 4) :=
  C.toRecodedPacketCode.path_broadcast_lower_bound (C.toRecodedPacketCode_correct hc)
    (C.toRecodedPacketCode_local (SimpleGraph.pathGraph n) hG) hn

end RecodedXorCode
end TransposeFollowup
