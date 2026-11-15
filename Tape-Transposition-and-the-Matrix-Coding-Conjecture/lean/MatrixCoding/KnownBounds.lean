import LeanMachine.WholeRow.OrderCode
import LeanMachine.WholeRow.SymmetricCode
import MatrixCoding.StatementsRowSpread

/-!
# The degree baseline for whole-row codes

The finite bound from Proposition 6.24(d) of *Order, Symmetry, and the Swap*,
and Proposition 2.5 of this paper, with an alphabet-uniform asymptotic form.
The sharp limiting bounds at windows one and two are included. The shared
window-two proof uses a rectangular invariant for the least-used-row induction.
-/

namespace LeanBacklog.KnownBounds

open Finset LeanMachine.WholeRow
open scoped Classical
noncomputable section

variable {d : ℕ} {A : Type*} [Fintype A] [Nonempty A]
variable {ρ : Fin d → Finset (Fin d)} {C : Finset (RowSpread.Entry d → A)}

/-- Pairing attains q^(d(d+1)/2) at window one, hence at every positive window.
This lower witness uses no algebraic structure on the alphabet. -/
theorem exists_pairing_code (d : ℕ) (A : Type*) [Fintype A] :
    ∃ C : Finset (RowSpread.Entry d → A),
      RowSpread.IsWholeRowCodeExcept (fun j => {j}) ∅ C ∧
      C.card = Fintype.card A ^ (d * (d + 1) / 2) := by
  refine ⟨SymmetricCode.code (Fin d) A, ?_, ?_⟩
  · apply (RowSpread.wholeRowCode_iff _ _ _).mpr
    intro x hx y hy j _ hxy
    exact SymmetricCode.recovery hx hy j (hxy j (mem_singleton_self _))
  · simpa using (SymmetricCode.card (R := Fin d) (A := A))

/-- A division-free finite form of the degree baseline, over every finite alphabet. -/
theorem cardinality_pow (hC : RowSpread.IsWholeRowCodeExcept ρ ∅ C)
    (w : ℕ) (hw : ∀ j, (ρ j).card ≤ w) :
    C.card ^ (w + 1) ≤ Fintype.card A ^ (w * d * (d + 1)) := by
  have hc := OrderCode.card_pow_le_degree ρ C
    (fun x hx y hy j hxy => (RowSpread.wholeRowCode_iff ρ ∅ C).mp hC x hx y hy j
      (notMem_empty _) hxy) w hw
  simpa using hc

/-- The finite real-exponent bound: rate at most w/(w+1) times (1+1/d). -/
theorem cardinality_bound (hC : RowSpread.IsWholeRowCodeExcept ρ ∅ C)
    (w : ℕ) (hw : ∀ j, (ρ j).card ≤ w) :
    (C.card : ℝ) ≤ (Fintype.card A : ℝ) ^ ((w : ℝ) * d * (d + 1) / (w + 1)) := by
  obtain ⟨o, ho⟩ := OrderAverage.exists_order_degree_bound ρ w hw
  have hc := OrderCode.card_le_order ρ C
    (fun x hx y hy j hxy => (RowSpread.wholeRowCode_iff ρ ∅ C).mp hC x hx y hy j
      (notMem_empty _) hxy) o
  have he : (LiftOrder.cost ρ o : ℝ) ≤ (w : ℝ) * d * (d + 1) / (w + 1) := by
    apply (le_div_iff₀ (by positivity : 0 < (w : ℝ) + 1)).mpr
    have ho' : ((w : ℝ) + 1) * LiftOrder.cost ρ o ≤ w * (d : ℝ) * (d + 1) := by
      exact_mod_cast (by simpa only [Fintype.card_fin] using ho)
    nlinarith
  calc
    (C.card : ℝ) ≤ (Fintype.card A : ℝ) ^ LiftOrder.cost ρ o := by exact_mod_cast hc
    _ = (Fintype.card A : ℝ) ^ (LiftOrder.cost ρ o : ℝ) := (Real.rpow_natCast _ _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Fintype.card_pos (α := A)) he

/-- At window one the finite upper bound is exactly the symmetric-array exponent. -/
theorem window_one (hC : RowSpread.IsWholeRowCodeExcept ρ ∅ C)
    (hw : ∀ j, (ρ j).card ≤ 1) :
    C.card ≤ Fintype.card A ^ (d * (d + 1) / 2) := by
  obtain ⟨o, ho⟩ := OrderAverage.exists_order_degree_bound ρ 1 hw
  have hc := OrderCode.card_le_order ρ C
    (fun x hx y hy j hxy => (RowSpread.wholeRowCode_iff ρ ∅ C).mp hC x hx y hy j
      (notMem_empty _) hxy) o
  apply hc.trans (Nat.pow_le_pow_right Fintype.card_pos ?_)
  simp only [Fintype.card_fin, Nat.one_mul] at ho
  omega

/-- Window two: the finite square bound, including empty helper sets. -/
theorem window_two (hC : RowSpread.IsWholeRowCodeExcept ρ ∅ C)
    (hw : ∀ j, (ρ j).card ≤ 2) :
    C.card ≤ Fintype.card A ^ (d * (d + 1) / 2 + (d - 1)) := by
  have hc := OrderCode.card_le_window_two ρ C
    (fun x hx y hy j hxy => (RowSpread.wholeRowCode_iff ρ ∅ C).mp hC x hx y hy j
      (notMem_empty _) hxy) hw
  simpa [AcyclicOrder.windowTwoBound] using hc

/-- An alphabet-independent finite threshold for the window-two half-rate bound. -/
theorem window_two_pow_threshold (hC : RowSpread.IsWholeRowCodeExcept ρ ∅ C)
    (hw : ∀ j, (ρ j).card ≤ 2) (n : ℕ) (hd : 3 * n ≤ d) :
    C.card ^ (2 * n) ≤ Fintype.card A ^ ((n + 1) * d * d) := by
  have ht : 2 * (d * (d + 1) / 2) ≤ d * (d + 1) := by omega
  calc
    _ ≤ (Fintype.card A ^ (d * (d + 1) / 2 + (d - 1))) ^ (2 * n) :=
      Nat.pow_le_pow_left (window_two hC hw) _
    _ = Fintype.card A ^ ((d * (d + 1) / 2 + (d - 1)) * (2 * n)) := by rw [← pow_mul]
    _ ≤ _ := Nat.pow_le_pow_right Fintype.card_pos (by
      nlinarith [Nat.mul_le_mul_left n ht,
        Nat.mul_le_mul_left (2 * n) (Nat.sub_le d 1), Nat.mul_le_mul_right d hd])

/-- The window-two half-rate upper bound is uniform over all finite alphabets. -/
theorem window_two_uniform_in_alphabet (η : ℝ) (hη : 0 < η) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ (A : Type*) [Fintype A], 2 ≤ Fintype.card A →
      RowSpread.WholeRowCardinalityBound d 2 A ((1 / 2 + η) * (d : ℝ)^2) := by
  obtain ⟨d₀, hd₀⟩ := exists_nat_gt (3 / (2 * η))
  refine ⟨d₀, ?_⟩
  intro d hd A _ hA ρ C hw hC
  have : Nonempty A := Fintype.card_pos_iff.mp (by omega)
  have hc := window_two hC hw
  have hdreal : 3 / (2 * η) < (d : ℝ) := hd₀.trans_le (by exact_mod_cast hd)
  have hηd : 3 ≤ 2 * η * (d : ℝ) := by
    have := (div_lt_iff₀ (by positivity : 0 < 2 * η)).mp hdreal
    nlinarith
  have htN : 2 * (d * (d + 1) / 2 + (d - 1)) ≤ d * (d + 1) + 2 * d := by omega
  have ht : 2 * ((d * (d + 1) / 2 + (d - 1) : ℕ) : ℝ) ≤
      (d : ℝ) * (d + 1) + 2 * d := by exact_mod_cast htN
  calc
    (C.card : ℝ) ≤ (Fintype.card A : ℝ) ^ (d * (d + 1) / 2 + (d - 1)) := by exact_mod_cast hc
    _ = (Fintype.card A : ℝ) ^ ((d * (d + 1) / 2 + (d - 1) : ℕ) : ℝ) :=
      (Real.rpow_natCast _ _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ Fintype.card A by omega))
      (by nlinarith [mul_le_mul_of_nonneg_right hηd (show (0 : ℝ) ≤ d by positivity)])

/-- An explicit finite threshold for the limiting rate, independent of the alphabet.
The error in rate is 1/((w+1)n) when n > 0. -/
theorem cardinality_pow_threshold (hC : RowSpread.IsWholeRowCodeExcept ρ ∅ C)
    (w n : ℕ) (hw : ∀ j, (ρ j).card ≤ w) (hd : n * w ≤ d) :
    C.card ^ (n * (w + 1)) ≤ Fintype.card A ^ ((n * w + 1) * d * d) := by
  calc
    _ = (C.card ^ (w + 1)) ^ n := by rw [← pow_mul, Nat.mul_comm n]
    _ ≤ (Fintype.card A ^ (w * d * (d + 1))) ^ n :=
      Nat.pow_le_pow_left (cardinality_pow hC w hw) _
    _ = Fintype.card A ^ (w * d * (d + 1) * n) := by rw [← pow_mul]
    _ ≤ _ := Nat.pow_le_pow_right Fintype.card_pos (by nlinarith [Nat.mul_le_mul_right d hd])

/-- For each fixed window, the limiting degree bound is uniform over all finite
alphabets, relations and nonlinear recovery codes. -/
theorem uniform_in_alphabet (w : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ (A : Type*) [Fintype A], 2 ≤ Fintype.card A →
      RowSpread.WholeRowCardinalityBound d w A
        (((w : ℝ) / (w + 1) + η) * (d : ℝ)^2) := by
  obtain ⟨d₀, hd₀⟩ := exists_nat_gt (1 / η)
  refine ⟨d₀, ?_⟩
  intro d hd A _ hA ρ C hw hC
  have : Nonempty A := Fintype.card_pos_iff.mp (by omega)
  apply (cardinality_bound hC w hw).trans
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ Fintype.card A by omega))
  have hdreal : 1 / η < (d : ℝ) := hd₀.trans_le (by exact_mod_cast hd)
  have hηd : 1 ≤ η * (d : ℝ) := by
    have := (div_lt_iff₀ hη).mp hdreal
    nlinarith
  have hd0 : (0 : ℝ) ≤ d := by positivity
  have hr : (w : ℝ) / (w + 1) ≤ 1 :=
    (div_le_one (by positivity)).mpr (by linarith)
  calc
    _ = (w : ℝ) / (w + 1) * (d : ℝ)^2 + (w : ℝ) / (w + 1) * d := by ring
    _ ≤ (w : ℝ) / (w + 1) * (d : ℝ)^2 + d := by
      nlinarith [mul_le_mul_of_nonneg_right hr hd0]
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hηd hd0]

end
end LeanBacklog.KnownBounds
