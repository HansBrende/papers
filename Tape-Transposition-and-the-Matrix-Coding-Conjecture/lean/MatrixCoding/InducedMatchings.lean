import LeanMachine.WholeRow.InducedMatchings
import MatrixCoding.StatementsRowSpread

/-!
# Induced-matching parity codes at fixed window

The finite counting proof and the arbitrary-syndrome fibre size live in the
shared library. This adapter uses the paper's whole-row predicate literally,
and supplies a uniform integer-power endpoint, without asymptotic analysis.
-/

namespace LeanBacklog.InducedMatchingCodes

open Finset LeanMachine.WholeRow
open scoped Classical
noncomputable section

variable {d : ℕ} {κ A : Type*} [Fintype κ] [AddCommGroup A] [Fintype A]
variable {ρ : Fin d → Finset (Fin d)} (D : InducedMatchingPartition ρ κ)

/-- Every syndrome gives a whole-row code, including the zero-sum parity code. -/
theorem isWholeRowCode (y : κ → A) : RowSpread.IsWholeRowCodeExcept ρ ∅ (D.code y) := by
  rw [RowSpread.wholeRowCode_iff]
  intro x hx z hz j _ hxz i
  exact D.code_recovers y hx hz j hxz i

/-- Exact cardinality: one independent equation for each nonempty block. -/
theorem cardinality (y : κ → A) :
    (D.code y).card = Fintype.card A ^ (d * d - Fintype.card κ) := by
  simpa using D.code_card y

/-- Proposition 10.1's displayed large-block bound. -/
theorem large_cells (w : ℕ) (hf : ∀ j, (ρ j).card ≤ w) :
    (D.largeCells.card : ℝ) ≤ ((w : ℝ)^2 + 3 / 2 * w) * d * Real.sqrt d := by
  simpa using D.largeCells_sqrt w hf

/-- Proposition 10.1's original displayed code bound. -/
theorem cardinality_bound (y : κ → A) (w : ℕ) (hf : ∀ j, (ρ j).card ≤ w) :
    ((D.code y).card : ℝ) ≤ (Fintype.card A : ℝ) ^
      ((d : ℝ)^2 / 2 + w * d / 2 + ((w : ℝ)^2 / 2 + 3 * w / 4) * d * Real.sqrt d) := by
  simpa [pow_two] using D.code_card_le_sqrt y w hf

/-- The improved bound obtained by balancing the two counting charges. -/
theorem cardinality_bound_balanced (y : κ → A) (w : ℕ) (hf : ∀ j, (ρ j).card ≤ w) :
    ((D.code y).card : ℝ) ≤ (Fintype.card A : ℝ) ^
      ((d : ℝ)^2 / 2 + w * d / 2 + 5 / 4 * (w * d : ℝ) * Real.sqrt (w * d)) := by
  simpa [pow_two] using D.code_card_le_balanced y w hf

/-- A completely finite, alphabet-uniform form of the fixed-window half bound.
For n > 0 the rate is at most 1/2 + 1/n once d meets this explicit threshold.
No reverse-degree bound or uniform matching size is required. -/
theorem cardinality_pow_le_half (y : κ → A) (w n : ℕ)
    (hf : ∀ j, (ρ j).card ≤ w) (hd : n * w + 25 * w^3 * n^2 ≤ d) :
    (D.code y).card ^ (2 * n) ≤ Fintype.card A ^ ((n + 2) * d * d) := by
  have ht : (n : ℝ) * w + 25 * (w : ℝ)^3 * (n : ℝ)^2 ≤ d := by exact_mod_cast hd
  have hs := Real.sq_sqrt (show 0 ≤ (w * d : ℝ) by positivity)
  have hs0 := Real.sqrt_nonneg (w * d : ℝ)
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hw0 : (0 : ℝ) ≤ w := by positivity
  have hd0 : (0 : ℝ) ≤ d := by positivity
  have hsmall0 : (n : ℝ) * w ≤ d := by
    exact_mod_cast (show n * w ≤ d from (Nat.le_add_right _ _).trans hd)
  have hlarge0 : 25 * (w : ℝ)^3 * (n : ℝ)^2 ≤ d := by
    exact_mod_cast (show 25 * w^3 * n^2 ≤ d from (Nat.le_add_left _ _).trans hd)
  have hsmall : (n : ℝ) * w * d ≤ (d : ℝ)^2 := by
    nlinarith [mul_le_mul_of_nonneg_right hsmall0 hd0]
  have hsq : (5 * (n : ℝ) * w * Real.sqrt (w * d : ℝ))^2 ≤ (d : ℝ)^2 := by
    calc
      _ = 25 * (n : ℝ)^2 * (w : ℝ)^2 * (Real.sqrt (w * d : ℝ))^2 := by ring
      _ = 25 * (n : ℝ)^2 * (w : ℝ)^2 * (w * d) := by rw [hs]
      _ ≤ (d : ℝ)^2 := by
        nlinarith [mul_le_mul_of_nonneg_right hlarge0 hd0]
  have hroot : 5 * (n : ℝ) * w * Real.sqrt (w * d : ℝ) ≤ d := by
    nlinarith [sq_nonneg (5 * (n : ℝ) * w * Real.sqrt (w * d : ℝ) - d)]
  have hb : (D.largeCells.card : ℝ) ≤
      5 / 2 * (w * d : ℝ) * Real.sqrt (w * d) := by
    simpa using D.largeCells_balanced w hf
  have hdim : 2 * ((d * d - Fintype.card κ : ℕ) : ℝ) ≤
      (d : ℝ)^2 + w * d + D.largeCells.card := by
    exact_mod_cast (by simpa [pow_two] using D.dimension_le w hf)
  have he : ((d * d - Fintype.card κ : ℕ) : ℝ) * (2 * n) ≤
      ((n : ℝ) + 2) * d * d := by
    nlinarith [mul_le_mul_of_nonneg_left hdim hn0,
      mul_le_mul_of_nonneg_left hb hn0,
      mul_le_mul_of_nonneg_right hroot hd0]
  rw [cardinality D y, ← pow_mul]
  apply Nat.pow_le_pow_right Fintype.card_pos
  exact_mod_cast he

end
end LeanBacklog.InducedMatchingCodes
