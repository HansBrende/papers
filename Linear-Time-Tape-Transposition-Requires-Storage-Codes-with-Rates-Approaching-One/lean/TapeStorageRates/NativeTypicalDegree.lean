import TapeStorageRates.DegreeGenie
import TapeStorageRates.FiniteTransfer
import TapeStorageRates.NativeCompiler
import BoundedStackDepth.LowAdaptivity

/-! # Degree budgets on the physical bit cones of the aligned simulator -/

namespace TapeStorageRates

open Filter Finset Transpose MergeDepth BoundedStackDepth

set_option autoImplicit false

/-- Every scale-one physical record of the simulator has width linear in its batch size,
including its full finite control and its actual work alphabet. -/
theorem native_blockWidth_bound (M : TM) :
    ∃ b : ℕ, ∀ s (hs : 0 < s), blockWidth (Native.machine M hs) 1 ≤ b*s := by
  obtain ⟨K,hK⟩ := Native.control_bits M
  let a := M.k * Nat.clog 2 (M.g+1) + (M.k+1) * Nat.clog 2 3 + 2
  refine ⟨K+a, fun s hs => ?_⟩
  have h := Nat.clog_le_of_le_pow (hK s hs)
  have ha : a ≤ a*s := Nat.le_mul_of_pos_right a hs
  change Nat.clog 2 ((Native.machine M hs).q+1) + M.k*1*Nat.clog 2 (M.g+1) +
    (M.k+1)*Nat.clog 2 3 + 1+1 ≤ (K+a)*s
  rw [Nat.mul_one, Nat.add_mul K a]
  calc
    _ = Nat.clog 2 ((Native.machine M hs).q+1) + a := by simp only [a, Nat.add_assoc]
    _ ≤ _ := Nat.add_le_add h ha

/-- Maximum number of input coordinates in one raw-bit append-time cone with a
genie budget of one bit per batch's worth of input bits. -/
noncomputable def alignedConeFan (M : TM) {s : ℕ} (hs : 0 < s) (C : ℝ) : ℕ :=
  packetFan M.k (genieDepth M.k (blockWidth (Native.machine M hs) 1) C (1/(s:ℝ)))

private theorem genieDepth_rescale (k β s : ℕ) (C : ℝ) :
    genieDepth k β C (1 / (s : ℝ)) = genieDepth k (β*s) C 1 := by
  simp only [genieDepth, Nat.cast_mul, div_div, div_one, div_div_eq_mul_div]
  congr 2 <;> ring_nf

/-- Reserving half the double-logarithmic degree budget bounds the physical fan by
this function. It grows more slowly than every fixed positive power of Δ. -/
noncomputable def nativeFanBound (Δ : ℕ) : ℝ := (2 : ℝ) ^ Real.sqrt (Real.logb 2 (Δ : ℝ))

theorem nativeFanBound_eventually_le_power {a : ℝ} (ha : 0 < a) :
    ∀ᶠ Δ : ℕ in atTop, nativeFanBound Δ ≤ (Δ : ℝ)^a := by
  have ht : Tendsto (fun Δ : ℕ => Real.logb 2 (Δ : ℝ)) atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 2,ht.eventually_ge_atTop ((1/a)^2)] with Δ hΔ hlog
  let x := Real.logb 2 (Δ : ℝ)
  have hx : 0 ≤ x := (sq_nonneg _).trans hlog
  have hroot : 1 ≤ a * Real.sqrt x := by
    have h := (div_le_iff₀ ha).mp (Real.le_sqrt_of_sq_le hlog)
    linarith
  have hd : 0 < (Δ : ℝ) := by exact_mod_cast (by omega : 0 < Δ)
  calc
    nativeFanBound Δ ≤ (2:ℝ)^(x*a) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
      nlinarith only [mul_le_mul_of_nonneg_right hroot (Real.sqrt_nonneg x),
        congrArg (· * a) (Real.sq_sqrt hx)])
    _ = _ := by rw [Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hd]

private theorem le_nativeFanBound {n Δ : ℕ} (hn : 1 < n) (hΔ : 1 < Δ)
    (hg : 2 * degreeLogLog n ≤ degreeLogLog Δ) : (n : ℝ) ≤ nativeFanBound Δ := by
  have h₁ := Real.logb_pos (by norm_num : (1:ℝ)<2) (by exact_mod_cast hn : (1:ℝ)<n)
  have h₂ := Real.logb_pos (by norm_num : (1:ℝ)<2) (by exact_mod_cast hΔ : (1:ℝ)<Δ)
  apply (Real.logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2) (by positivity)).mp
  apply Real.le_sqrt_of_sq_le
  apply (Real.logb_le_logb (by norm_num : (1:ℝ)<2) (sq_pos_of_pos h₁) h₂).mp
  simpa only [Real.logb_pow,Nat.cast_ofNat,degreeLogLog] using hg

/-- At a single batch size chosen before the dimension, both the batch and the fan fit
under the subpower bound. The native inverse-degree exponent is unchanged. -/
theorem native_batch_size_for_cap (M : TM) {C : ℝ} (hC : 1 ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ Δ : ℕ in atTop, ∃ s : ℕ, ∃ hs : 0 < s,
      ((max s (alignedConeFan M hs C) : ℕ) : ℝ) ≤ nativeFanBound Δ ∧
      1 / (s : ℝ) ≤ K * inverseDegreeScale (2*(4*M.k^2+1)) Δ ∧
      inverseDegreeScale (2*(4*M.k^2+1)) Δ ≤ 1 / s := by
  obtain ⟨b,hb⟩ := native_blockWidth_bound M
  obtain ⟨B,hB,hbound⟩ := genie_packet_cap_degree_bound_at M.k b hC
  let p := 4*M.k^2+1
  obtain ⟨K,hK,hchoose⟩ := sizes_for_degree_growth (p := 2*p) (by dsimp [p]; omega)
    (show 0 < 4*B by positivity) 1
  refine ⟨K,hK,?_⟩
  filter_upwards [hchoose,eventually_ge_atTop 2] with Δ h hΔ
  obtain ⟨s,_,hs,hcap,hupper,hlower⟩ := h
  refine ⟨s,hs,?_,hupper,hlower⟩
  let β := blockWidth (Native.machine M hs) 1
  let D := genieDepth M.k (β*s) C 1
  let A := packetIncidenceCap M.k (s^2) D
  have hs2 : 1 ≤ s^2 := Nat.pow_pos hs
  have hw : β*s ≤ b*s^2 := by simpa [sq, Nat.mul_assoc] using Nat.mul_le_mul_right s (hb s hs)
  have hA := hbound (s^2) (β*s) hs2 (Nat.mul_pos (one_le_blockWidth _ 1) hs) hw
  have hfan : 1 ≤ packetFan M.k D := by
    unfold packetFan
    simpa using single_le_sum (fun i (_ : i ∈ range (D+1)) => Nat.zero_le ((M.k+1)^i))
      (show 0 ∈ range (D+1) by simp)
  have hform : A = 2*s^2*packetFan M.k D := rfl
  have hA2 : 1 < A := by rw [hform]; nlinarith [Nat.mul_le_mul hs2 hfan]
  have hlog : Real.logb 2 ((s : ℝ)^2+1) ≤ 2*Real.logb 2 ((s : ℝ)+1) := calc
    _ ≤ Real.logb 2 (((s : ℝ)+1)^2) :=
      Real.logb_le_logb_of_le (by norm_num) (by positivity) (by nlinarith only [Nat.cast_nonneg s (α := ℝ)])
    _ = _ := by rw [Real.logb_pow]; norm_num
  have hd : 2 * degreeLogLog A ≤ degreeLogLog Δ := by
    change degreeLogLog A ≤ _ at hA
    push_cast at hA
    rw [← pow_mul] at hA
    have hmajor := mul_le_mul_of_nonneg_left hlog (show 0 ≤ B*(s : ℝ)^(2*p) by positivity)
    change degreeLogLog A ≤ B*(s : ℝ)^(2*p)*_ at hA
    nlinarith only [hA,hmajor,hcap]
  apply le_trans _ (le_nativeFanBound hA2 (by omega) hd)
  apply Nat.cast_le.mpr
  rw [alignedConeFan,genieDepth_rescale,hform]
  apply max_le
  · calc
      s ≤ s^2 := Nat.le_self_pow (by decide) _
      _ ≤ 2*s^2*packetFan M.k D := by nlinarith [Nat.mul_le_mul_left (s^2) hfan]
  · exact Nat.le_mul_of_pos_left _ (by positivity : 0 < 2*s^2)

end TapeStorageRates
