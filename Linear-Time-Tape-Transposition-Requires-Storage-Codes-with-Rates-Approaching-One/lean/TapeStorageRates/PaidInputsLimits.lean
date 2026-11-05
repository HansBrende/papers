import TapeStorageRates.PaidInputsSuccess

/-! # Near-full success at jointly growing dimensions and entry widths -/

namespace TapeStorageRates.PaidInputs

open Finset Filter DirectedRecovery MergeDepth

set_option autoImplicit false

/-- For every accuracy and every size threshold there is a single dimension and width
above that threshold on which the successful binary input set has the stated rate.
No prescribed width function, monotonicity, or divisibility is required. -/
def GrowingWidthSuccess (M : Transpose.TM) (c : ℝ) : Prop :=
  ∀ n : ℕ, ∀ ε : ℝ, 0 < ε → ∃ d ≥ n, ∃ b ≥ n,
    (successfulInputsAt M c d b).Nonempty ∧
      1-ε ≤ storageCodeRate (successfulInputsAt M c d b)

/-- Canonical logarithmic widths tend to infinity with the matrix dimension. -/
theorem tendsto_entryBits : Tendsto Transpose.entryBits atTop atTop := by
  apply tendsto_atTop.2
  intro n
  filter_upwards [eventually_ge_atTop (2^n+1)] with d hd
  have h : n ≤ Nat.log2 (d-1) := (Nat.le_log2 (by have := Nat.two_pow_pos n; omega)).mpr (by omega)
  exact h.trans (Nat.le_succ _)

/-- The canonical near-full success hypothesis specializes the joint-width one. -/
theorem NearFullSuccess.growing_widths {M : Transpose.TM} {c : ℝ} (h : NearFullSuccess M c) :
    GrowingWidthSuccess M c := by
  obtain ⟨D,hD,hgood,hlim⟩ := h
  intro n ε hε
  obtain ⟨i,⟨hd,hb⟩,hε'⟩ := (((hD.tendsto_atTop.eventually_ge_atTop n).and
    ((tendsto_entryBits.comp hD.tendsto_atTop).eventually_ge_atTop n)).and
    (hlim.eventually_lt_const hε)).exists
  exact ⟨D i,hd,Transpose.entryBits (D i),hb,(hgood i).2,by linarith⟩

/-- Failure of near-full success on jointly growing widths bounds the success
probability exponentially, uniformly over all sufficiently large dimensions *and* widths. -/
theorem exponentially_small_of_not_growing_widths {M : Transpose.TM} {c : ℝ}
    (hn : ¬ GrowingWidthSuccess M c) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ n : ℕ, ∀ d ≥ n, ∀ b ≥ n,
      ((successfulInputsAt M c d b).card : ℝ) / (2:ℝ)^(d*d*b) ≤ (2:ℝ)^(-γ*(d*d*b : ℕ)) := by
  unfold GrowingWidthSuccess at hn
  push Not at hn
  obtain ⟨n,γ,hγ,hexcl⟩ := hn
  refine ⟨γ,hγ,max n 1,fun d hd b hb => (uniform_fraction_le_iff γ).mpr ?_⟩
  let G := successfulInputsAt M c d b
  by_cases hG : G.Nonempty
  · have hpos : 0 < ((d*d*b : ℕ):ℝ) := by
      exact_mod_cast Nat.mul_pos (Nat.mul_pos (by omega : 0<d) (by omega)) (by omega : 0<b)
    have hr := hexcl d ((le_max_left _ _).trans hd) b ((le_max_left _ _).trans hb) hG
    have hlog : Real.logb 2 G.card ≤ (1-γ)*(d*d*b : ℕ) :=
      (div_le_iff₀ hpos).mp <| by
        simpa only [storageCodeRate,Raw,Fintype.card_fin,Fintype.card_bool,Nat.cast_ofNat,G] using hr.le
    exact (Real.logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2)
      (by exact_mod_cast hG.card_pos : (0:ℝ)<G.card)).mp hlog
  · change (G.card:ℝ) ≤ _
    rw [not_nonempty_iff_eq_empty.mp hG,card_empty,Nat.cast_zero]
    exact Real.rpow_nonneg (by norm_num) _

end TapeStorageRates.PaidInputs
