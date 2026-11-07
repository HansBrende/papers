import TapeStorageRates.MajorityMatrix
import TapeStorageRates.OddProductPaired
import TapeStorageRates.SyndromeFibres

/-! # Geometric guarantees for the majority fitting matrix -/

namespace TapeStorageRates.Majority

open Finset DirectedRecovery

set_option autoImplicit false
noncomputable section

variable {K V : Type*} [Field K] [Fintype V] [DecidableEq V] {m : ℕ}

omit [Fintype V] [DecidableEq V] in
/-- Support on a simple graph entails zero diagonal. -/
theorem diagonal_eq_zero_of_support (G : SimpleGraph V) (A : Matrix V V K)
    (hA : ∀ u v, A u v ≠ 0 → G.Adj u v) (u : V) : A u u = 0 := by
  by_contra h
  exact G.loopless.irrefl u (hA u u h)

/-- Every amplified support edge belongs to the actual odd product graph. -/
theorem matrix_support_oddProduct (G : SimpleGraph V) (A : Matrix V V K)
    (hA : ∀ u v, A u v ≠ 0 → G.Adj u v) (h2 : (2 : K) ≠ 0) (hm : Odd m)
    {u v : Fin m → V} (huv : matrix A m u v ≠ 0) :
    (oddProductGraph G (Fin m)).Adj u v := by
  obtain ⟨ho, hs⟩ := matrix_support A (diagonal_eq_zero_of_support G A hA) h2 hm huv
  refine ⟨fun i => ?_, ho⟩
  by_cases hi : u i = v i
  · exact Or.inl hi
  · exact Or.inr (hA _ _ (hs i hi))

/-- The actual fitting matrix has diagonal one. -/
theorem check_diagonal (A : Matrix V V K) (hdiag : ∀ v, A v v = 0)
    (h2 : (2 : K) ≠ 0) (hm : Odd m) (u : Fin m → V) :
    (1 - matrix A m) u u = 1 := by
  simp [Matrix.sub_apply, matrix_diag A hdiag h2 hm]

/-- The syndrome helpers remain on odd product edges, with no alphabet
blocking or auxiliary coordinates. -/
theorem check_helpers_supported (G : SimpleGraph V) (A : Matrix V V K)
    (hA : ∀ u v, A u v ≠ 0 → G.Adj u v) (h2 : (2 : K) ≠ 0) (hm : Odd m)
    (q p : Fin m → V) (hp : p ∈ matrixHelpers (1 - matrix A m) q) :
    (oddProductGraph G (Fin m)).Adj q p := by
  classical
  obtain ⟨_, hpq, hnonzero⟩ := mem_filter.mp hp
  have hqp : q ≠ p := Ne.symm hpq
  apply matrix_support_oddProduct G A hA h2 hm
  simpa [Matrix.sub_apply, Matrix.one_apply, hqp] using hnonzero

open Classical in
/-- Both incidence ports fit below the product degree bound, with the
stationary tuple excluded. The recovery relation need not be symmetric. -/
theorem check_helpers_degree_add_one_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Matrix V V K) (hA : ∀ u v, A u v ≠ 0 → G.Adj u v)
    (h2 : (2 : K) ≠ 0) (hm : Odd m) {D : ℕ} (hD : ∀ v, G.degree v ≤ D)
    (z : (Fin m → V) ⊕ (Fin m → V)) :
    (pairedIncidenceGraph (matrixHelpers (1 - matrix A m))).degree z + 1 ≤ (D + 1)^m := by
  classical
  have hg (u : Fin m → V) : (oddProductGraph G (Fin m)).degree u ≤ (D + 1)^m - 1 := by
    have h := OddProductGraph.degree_add_one_le_pow hD u
    simp only [Fintype.card_fin] at h
    omega
  have h := paired_degree_le_of_graph hg (matrixHelpers (1 - matrix A m))
    (check_helpers_supported G A hA h2 hm) z
  have hp : 0 < (D + 1)^m := pow_pos (by omega) _
  omega

/-- Every base odd-walk threshold remains a minimum paired-distance
threshold on the same-coordinate syndrome recovery relation. -/
theorem check_helpers_paired_far (G : SimpleGraph V) (A : Matrix V V K)
    (hA : ∀ u v, A u v ≠ 0 → G.Adj u v) (h2 : (2 : K) ≠ 0) (hm : Odd m)
    {r : ℕ} (hG : ∀ v (w : G.Walk v v), Odd w.length → r < w.length)
    (q : Fin m → V) :
    ¬ (pairedIncidenceGraph (matrixHelpers (1 - matrix A m))).edist (Sum.inl q) (Sum.inr q) ≤ r :=
  oddProduct_not_paired_edist_le hG (matrixHelpers (1 - matrix A m))
    (check_helpers_supported G A hA h2 hm) q

end
end TapeStorageRates.Majority
