import SourceCovers.PrefixDeficit
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

set_option autoImplicit false

/-!
# Arithmetic and reciprocal means of complete-bank covers

The two means average the same actual phase-column pairs. The finite
Cauchy inequality bounds the mean reciprocal below by the reciprocal of the
arithmetic mean, then applies to the original selected and protected prefixes.
-/

namespace SourceCovers

open Classical Finset LeanMachine
open scoped BigOperators
noncomputable section

variable {k T : ℕ} {xs : Fin k → ℕ → ℤ} {K : Finset (ActualFamily xs T)}

/-- Arithmetic mean of the actual complete-bank fractional cover weights.
An empty averaging set has value zero. -/
def meanCover (hc : HasSpanColoring K 2) {M : ℕ} (hM : 2 ≤ M)
    (E : Finset (ActualFamily xs T)) (x t : ℕ → ℕ) (d b : ℕ) (A : Finset ℕ) : ℝ :=
  (∑ ρ ∈ A, ∑ j ∈ range d, phaseCoreCover hc hM E x t d b ρ j) / (A.card * d)

private theorem one_le_cover_at_column (hc : HasSpanColoring K 2) {M d b ρ j : ℕ}
    (hM : 2 ≤ M) (E : Finset (ActualFamily xs T)) (x t : ℕ → ℕ)
    (hd : 0 < d) (hb : 0 < b) (hn : ∀ z < d * d * b, t z < T)
    (hρ : ρ < M) (hj : j < d) : 1 ≤ phaseCoreCover hc hM E x t d b ρ j := by
  have htime := hn _ ((column_indices hd hb hj).1.trans_lt (column_indices hd hb hj).2)
  exact (fractionalCoreCover_exactSourceBank_bounds hc hM hρ E x htime).2.1

/-- Every sampled legal complete-bank cover is at least one. -/
theorem one_le_meanCover (hc : HasSpanColoring K 2) {M d b : ℕ}
    (hM : 2 ≤ M) (E : Finset (ActualFamily xs T)) (x t : ℕ → ℕ)
    (hd : 0 < d) (hb : 0 < b) (hn : ∀ z < d * d * b, t z < T)
    (A : Finset ℕ) (hA : A.Nonempty) (hAM : ∀ ρ ∈ A, ρ < M) :
    1 ≤ meanCover hc hM E x t d b A := by
  have hden : (0 : ℝ) < A.card * d := by
    exact mul_pos (by exact_mod_cast card_pos.mpr hA) (by exact_mod_cast hd)
  apply (le_div_iff₀ hden).mpr
  calc
    1 * ((A.card : ℝ) * d) = ∑ ρ ∈ A, ∑ j ∈ range d, (1 : ℝ) := by simp
    _ ≤ _ := sum_le_sum fun ρ hρ => sum_le_sum fun j hj =>
      one_le_cover_at_column hc hM E x t hd hb hn (hAM ρ hρ) (mem_range.mp hj)

/-- Finite Cauchy gives the reciprocal-mean inequality on the actual
phase-column averaging set. -/
theorem one_div_meanCover_le_meanReciprocalCover (hc : HasSpanColoring K 2)
    {M d b : ℕ} (hM : 2 ≤ M) (E : Finset (ActualFamily xs T)) (x t : ℕ → ℕ)
    (hd : 0 < d) (hb : 0 < b) (hn : ∀ z < d * d * b, t z < T)
    (A : Finset ℕ) (hA : A.Nonempty) (hAM : ∀ ρ ∈ A, ρ < M) :
    1 / meanCover hc hM E x t d b A ≤ meanReciprocalCover hc hM E x t d b A := by
  let κ : ℕ × ℕ → ℝ := fun p => phaseCoreCover hc hM E x t d b p.1 p.2
  have hκ : ∀ p ∈ A ×ˢ range d, 0 < κ p := by
    intro p hp
    obtain ⟨hρ, hj⟩ := mem_product.mp hp
    exact zero_lt_one.trans_le
      (one_le_cover_at_column hc hM E x t hd hb hn (hAM p.1 hρ) (mem_range.mp hj))
  have hnonempty : (A ×ˢ range d).Nonempty := by
    obtain ⟨ρ, hρ⟩ := hA
    exact ⟨(ρ, 0), mem_product.mpr ⟨hρ, mem_range.mpr hd⟩⟩
  have hcard : (0 : ℝ) < (A ×ˢ range d).card := by
    exact_mod_cast card_pos.mpr hnonempty
  have hsum : 0 < ∑ p ∈ A ×ˢ range d, κ p := sum_pos hκ hnonempty
  have h := div_le_div_of_nonneg_right
    (sq_sum_div_le_sum_sq_div (A ×ˢ range d) (fun _ => (1 : ℝ)) hκ) hcard.le
  have heq :
      (∑ p ∈ A ×ˢ range d, (1 : ℝ)) ^ 2 /
          (∑ p ∈ A ×ˢ range d, κ p) / (A ×ˢ range d).card =
        1 / ((∑ p ∈ A ×ˢ range d, κ p) / (A ×ˢ range d).card) := by
    simp only [sum_const, nsmul_eq_mul, mul_one]
    field_simp
  rw [heq] at h
  simpa only [one_pow, sum_product, card_product, card_range, Nat.cast_mul,
    meanCover, meanReciprocalCover, κ] using h

namespace AdmissibleGeometry

variable {c β : ℝ} {N q : ℕ} (G : AdmissibleGeometry c β N q)
    (O : SortedCore G.core)

/-- Arithmetic cover mean with the same original selected and protected
prefixes as `prefixMeanReciprocal`. -/
def prefixMeanCover (J R M : ℕ) (hM : 2 ≤ M) : ℝ :=
  meanCover (G.core_coloring.mono (O.selectedPrefix_subset J)) hM
    G.exceptions G.x G.t G.d G.b
    (admissiblePhases (O.selectedPrefix J) (O.subprefix J R) M)

private theorem prefix_phases_nonempty {J R M : ℕ} (hRM : R < M) :
    (admissiblePhases (O.selectedPrefix J) (O.subprefix J R) M).Nonempty := by
  have hA := (protected_phase_average (O.selectedPrefix J) (O.subprefix J R)
    (O.subprefix_card_le J R) hRM).1
  exact card_pos.mp ((Nat.sub_pos_of_lt hRM).trans_le hA)

theorem one_le_prefixMeanCover {J R M : ℕ} (hM : 2 ≤ M) (hRM : R < M) :
    1 ≤ G.prefixMeanCover O J R M hM :=
  one_le_meanCover _ _ _ _ _ G.hd G.hb G.append_lt _
    (G.prefix_phases_nonempty O hRM) (fun _ hρ => admissiblePhase_lt hρ)

/-- Reciprocal Cauchy for the actual prefix geometry, including `R > J`. -/
theorem one_div_prefixMeanCover_le_prefixMeanReciprocal {J R M : ℕ}
    (hM : 2 ≤ M) (hRM : R < M) :
    1 / G.prefixMeanCover O J R M hM ≤ G.prefixMeanReciprocal O J R M hM :=
  one_div_meanCover_le_meanReciprocalCover _ _ _ _ _ G.hd G.hb G.append_lt _
    (G.prefix_phases_nonempty O hRM) (fun _ hρ => admissiblePhase_lt hρ)

/-- A finite upper bound on arithmetic mean cover supplies reciprocal
credit. Its positivity follows from the cover bound itself. -/
theorem one_div_le_prefixMeanReciprocal {J R M : ℕ} {f : ℝ}
    (hM : 2 ≤ M) (hRM : R < M) (hcover : G.prefixMeanCover O J R M hM ≤ f) :
    1 / f ≤ G.prefixMeanReciprocal O J R M hM :=
  (one_div_le_one_div_of_le (zero_lt_one.trans_le (G.one_le_prefixMeanCover O hM hRM))
    hcover).trans (G.one_div_prefixMeanCover_le_prefixMeanReciprocal O hM hRM)

end AdmissibleGeometry
end
end SourceCovers
