import Mathlib

/-!
# Rank loss modulo a prime from an integer diagonalization

An actual unimodular diagonalization is retained as a hypothesis. The
existence of Smith normal form and analytic estimates for rational rank
are separate from the finite algebra proved here. Zero diagonal entries
are explicitly excluded from the loss count.
-/

namespace LeanMachine.SmithRankLoss

open Classical
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Unimodular changes of integer basis stay invertible over every field. -/
theorem rank_map_of_diagonalization {F : Type*} [Field F]
    (f : ℤ →+* F) (M U V : Matrix ι ι ℤ) (a : ι → ℤ)
    (hU : IsUnit U.det) (hV : IsUnit V.det)
    (hdiag : U * M * V = Matrix.diagonal a) :
    (M.map f).rank = (Finset.univ.filter (fun i => f (a i) ≠ 0)).card := by
  classical
  have hU' : IsUnit (U.map f).det := by
    change IsUnit (f.mapMatrix U).det
    rw [← f.map_det]
    exact hU.map f
  have hV' : IsUnit (V.map f).det := by
    change IsUnit (f.mapMatrix V).det
    rw [← f.map_det]
    exact hV.map f
  have hdiag' : U.map f * M.map f * V.map f = Matrix.diagonal (fun i => f (a i)) := by
    have hm : (Matrix.diagonal a).map f = Matrix.diagonal (fun i => f (a i)) := by
      ext i j
      by_cases h : i = j <;> simp [Matrix.diagonal, h]
    simpa only [Matrix.map_mul, hm] using congrArg (fun A => A.map f) hdiag
  calc
    (M.map f).rank = (U.map f * M.map f * V.map f).rank := by
      rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ hV',
        Matrix.rank_mul_eq_right_of_isUnit_det _ _ hU']
    _ = (Matrix.diagonal (fun i => f (a i))).rank := congrArg Matrix.rank hdiag'
    _ = (Finset.univ.filter (fun i => f (a i) ≠ 0)).card := by
      rw [Matrix.rank_diagonal]
      exact Fintype.card_subtype _

/-- The precise rank loss counts nonzero diagonal entries killed modulo `p`.
No divisibility-chain normalization is needed for this identity. -/
theorem rank_loss_eq (p : ℕ) [Fact p.Prime]
    (M U V : Matrix ι ι ℤ) (a : ι → ℤ)
    (hU : IsUnit U.det) (hV : IsUnit V.det)
    (hdiag : U * M * V = Matrix.diagonal a) :
    (M.map (Int.castRingHom ℚ)).rank - (M.map (Int.castRingHom (ZMod p))).rank =
      (Finset.univ.filter (fun i => a i ≠ 0 ∧ (p : ℤ) ∣ a i)).card := by
  classical
  rw [rank_map_of_diagonalization (Int.castRingHom ℚ) M U V a hU hV hdiag,
    rank_map_of_diagonalization (Int.castRingHom (ZMod p)) M U V a hU hV hdiag]
  simp only [Int.coe_castRingHom, Int.cast_ne_zero, ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun i => a i ≠ 0)) (fun i => (p : ℤ) ∣ a i)
  have hfilter : (Finset.univ.filter (fun i => a i ≠ 0)).filter
      (fun i => ¬(p : ℤ) ∣ a i) = Finset.univ.filter (fun i => ¬(p : ℤ) ∣ a i) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨And.right, fun h => ⟨fun hz => h (hz ▸ dvd_zero _), h⟩⟩
  rw [hfilter] at hsplit
  rw [Finset.filter_filter] at hsplit
  simp only [ne_eq] at hsplit
  omega

/-- Modular specialization cannot increase the rational rank of an integer
matrix with the displayed unimodular diagonalization. -/
theorem rank_mod_le_rank_rat (p : ℕ) [Fact p.Prime]
    (M U V : Matrix ι ι ℤ) (a : ι → ℤ)
    (hU : IsUnit U.det) (hV : IsUnit V.det)
    (hdiag : U * M * V = Matrix.diagonal a) :
    (M.map (Int.castRingHom (ZMod p))).rank ≤ (M.map (Int.castRingHom ℚ)).rank := by
  rw [rank_map_of_diagonalization (Int.castRingHom ℚ) M U V a hU hV hdiag,
    rank_map_of_diagonalization (Int.castRingHom (ZMod p)) M U V a hU hV hdiag]
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Int.coe_castRingHom,
    Int.cast_ne_zero, ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd] at hi ⊢
  intro hz
  exact hi (hz ▸ dvd_zero _)

/-- Rational rank and modular nullity lower bounds force at least their
combined excess over the ambient dimension many nonzero diagonal entries
divisible by the prime. The subtraction is over the reals. -/
theorem loss_count_lower_bound (p : ℕ) [Fact p.Prime]
    (M U V : Matrix ι ι ℤ) (a : ι → ℤ)
    (hU : IsUnit U.det) (hV : IsUnit V.det)
    (hdiag : U * M * V = Matrix.diagonal a)
    (R K : ℝ)
    (hrank : R ≤ ((M.map (Int.castRingHom ℚ)).rank : ℝ))
    (hnull : K ≤ (Module.finrank (ZMod p)
      (LinearMap.ker (M.map (Int.castRingHom (ZMod p))).mulVecLin) : ℝ)) :
    R + K - Fintype.card ι ≤
      ((Finset.univ.filter (fun i => a i ≠ 0 ∧ (p : ℤ) ∣ a i)).card : ℝ) := by
  have hle := rank_mod_le_rank_rat p M U V a hU hV hdiag
  have heq := congrArg (fun n : ℕ => (n : ℝ)) (rank_loss_eq p M U V a hU hV hdiag)
  rw [Nat.cast_sub hle] at heq
  have hdim : (M.map (Int.castRingHom (ZMod p))).rank +
      Module.finrank (ZMod p) (LinearMap.ker (M.map (Int.castRingHom (ZMod p))).mulVecLin) =
      Fintype.card ι := by
    simpa only [Matrix.rank, Module.finrank_pi] using
      (M.map (Int.castRingHom (ZMod p))).mulVecLin.finrank_range_add_finrank_ker
  have hdimR := congrArg (fun n : ℕ => (n : ℝ)) hdim
  push_cast at hdimR
  linarith

end LeanMachine.SmithRankLoss
