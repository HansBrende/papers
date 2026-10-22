import TransposeFollowup.XorComponentCount
import TransposeFollowup.PacketDistanceConsequences

/-! An explicit fixed-degree consequence of the recoded-XOR bound. The error
is at most 6 log(max(2,Delta)) P/log n for every n>=2 and every entry width.
This proves the stated one-sided P-O_Delta(P/log n) bound uniformly in b. -/

namespace TransposeFollowup

open scoped BigOperators
open Classical
set_option autoImplicit false

namespace RecodedXorCode

variable {n b B : ℕ} (C : RecodedXorCode n b B)

theorem degree_broadcast_bound_scaled (hc : C.Correct) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hG : C.LocalTo G) (D : ℕ) (hD : 2 ≤ D)
    (hdegree : ∀ i, G.degree i ≤ D) (hn : 0 < n) :
    (Nat.log D n / 2 + 2) * (n * n * b) ≤
      (Nat.log D n / 2 + 2) * B + 3 * (n * n * b) :=
  C.toRecodedPacketCode.degree_broadcast_bound_scaled
    (C.toRecodedPacketCode_correct hc) G (C.toRecodedPacketCode_local G hG) D hD hdegree hn

/-- Explicit fixed-degree theorem. In contrast with a qualitative big-O
statement, this gives a uniform constant and holds for every n>=2 and b>=0. -/
theorem degree_broadcast_lower_bound (hc : C.Correct) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hG : C.LocalTo G) (D : ℕ) (hD : 2 ≤ D)
    (hdegree : ∀ i, G.degree i ≤ D) (hn : 2 ≤ n) :
    (B : ℝ) ≥ (n * n * b : ℕ) -
      6 * Real.log (D : ℝ) * (n * n * b : ℕ) / Real.log (n : ℝ) :=
  C.toRecodedPacketCode.degree_broadcast_lower_bound
    (C.toRecodedPacketCode_correct hc) G (C.toRecodedPacketCode_local G hG) D hD hdegree hn

theorem fixed_degree_broadcast_lower_bound (hc : C.Correct) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hG : C.LocalTo G) (Delta : ℕ)
    (hdegree : ∀ i, G.degree i ≤ Delta) (hn : 2 ≤ n) :
    (B : ℝ) ≥ (n * n * b : ℕ) -
      6 * Real.log (max 2 Delta : ℕ) * (n * n * b : ℕ) / Real.log (n : ℝ) :=
  C.toRecodedPacketCode.fixed_degree_broadcast_lower_bound
    (C.toRecodedPacketCode_correct hc) G (C.toRecodedPacketCode_local G hG) Delta hdegree hn

end RecodedXorCode
end TransposeFollowup
