import LeanMachine.SmithRankLoss

/-!
# The finite algebra in the necessary-torsion corollary

The diagonalization is supplied explicitly. Existence of integer Smith
normal form and the analytic rational-rank lower bound remain outside this
module. Zero invariant factors do not contribute to the count.
-/

namespace DirectedRecovery

open Classical
set_option autoImplicit false

/-- Exact rank loss for a supplied unimodular integer diagonalization. -/
theorem smith_rank_loss {n : ℕ} (p : ℕ) [Fact p.Prime]
    (M U V : Matrix (Fin n) (Fin n) ℤ) (a : Fin n → ℤ)
    (hU : IsUnit U.det) (hV : IsUnit V.det)
    (hdiag : U * M * V = Matrix.diagonal a) :
    (M.map (Int.castRingHom ℚ)).rank - (M.map (Int.castRingHom (ZMod p))).rank =
      (Finset.univ.filter (fun i => a i ≠ 0 ∧ (p : ℤ) ∣ a i)).card :=
  LeanMachine.SmithRankLoss.rank_loss_eq p M U V a hU hV hdiag

/-- The finite numerical implication in the necessary-torsion corollary.
For a matrix of size `n = t*N`, a rational rank of at least `(1/2-δ)n`
and modular nullity of at least `(1/2+ε)n` force `(ε-δ)n` nonzero factors
divisible by `p`. No asymptotic or analytic hypothesis is silently assumed. -/
theorem torsion_count_of_rank_and_nullity {n : ℕ} (p : ℕ) [Fact p.Prime]
    (M U V : Matrix (Fin n) (Fin n) ℤ) (a : Fin n → ℤ)
    (hU : IsUnit U.det) (hV : IsUnit V.det)
    (hdiag : U * M * V = Matrix.diagonal a)
    (ε δ : ℝ)
    (hrank : (1 / 2 - δ) * n ≤ ((M.map (Int.castRingHom ℚ)).rank : ℝ))
    (hnull : (1 / 2 + ε) * n ≤ (Module.finrank (ZMod p)
      (LinearMap.ker (M.map (Int.castRingHom (ZMod p))).mulVecLin) : ℝ)) :
    (ε - δ) * n ≤
      ((Finset.univ.filter (fun i => a i ≠ 0 ∧ (p : ℤ) ∣ a i)).card : ℝ) := by
  have h := LeanMachine.SmithRankLoss.loss_count_lower_bound p M U V a hU hV hdiag
    ((1 / 2 - δ) * n) ((1 / 2 + ε) * n) hrank hnull
  simp only [Fintype.card_fin] at h
  nlinarith

end DirectedRecovery
