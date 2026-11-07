import TapeStorageRates.DegreeGenie
import TapeStorageRates.FiniteTransfer

/-! # Degree budgets on the physical bit cones of the aligned simulator -/

namespace TapeStorageRates

open Filter Finset Transpose MergeDepth BoundedStackDepth

set_option autoImplicit false

/-- The physical depth obtained by revealing complete batches of length `10s+1`.
The positive constant `a` pays for each seed and the coarse schedule size. -/
noncomputable def jointPhysicalDepth (k a s : ℕ) : ℕ :=
  (10*s+1) * (genieDepth k (a*s) 1 1 + 1)

/-- The reciprocal cut budget and effective-width forms give exactly the same genie. -/
theorem joint_genie_rescale (k a s : ℕ) :
    genieDepth k 1 1 (1 / ((a:ℝ)*s)) = genieDepth k (a*s) 1 1 := by
  simp only [genieDepth, Nat.cast_one, Nat.cast_mul, mul_one, div_one,
    div_div, div_div_eq_mul_div]
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

/-- One batch size, chosen before the dimension, puts the physical fan under the
subpower bound. Joint batch records give the packet exponent `4k²+1` also for native bits. -/
theorem native_batch_size_for_cap (k a : ℕ) (ha : 0<a) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ Δ : ℕ in atTop, ∃ s : ℕ, ∃ _hs : 0 < s,
      ((max s (packetFan k (jointPhysicalDepth k a s)) : ℕ) : ℝ) ≤ nativeFanBound Δ ∧
      1 / (s : ℝ) ≤ K * inverseDegreeScale (4*k^2+1) Δ ∧
      inverseDegreeScale (4*k^2+1) Δ ≤ 1 / s := by
  obtain ⟨B,hB,hbound⟩ := genie_scaled_cap_degree_bound_at k a 10 (by norm_num : (1:ℝ)≤1)
  let p := 4*k^2+1
  obtain ⟨K,hK,hchoose⟩ := sizes_for_degree_growth (p := p) (by dsimp [p]; omega)
    (show 0 < 2*B by positivity) 1
  refine ⟨K,hK,?_⟩
  filter_upwards [hchoose,eventually_ge_atTop 2] with Δ h hΔ
  obtain ⟨s,_,hs,hcap,hupper,hlower⟩ := h
  refine ⟨s,hs,?_,hupper,hlower⟩
  let D := jointPhysicalDepth k a s
  let A := packetIncidenceCap k s D
  have hA := hbound s (a*s) hs (Nat.mul_pos ha hs) le_rfl
  have hfan : 1 ≤ packetFan k D := by
    unfold packetFan
    simpa using single_le_sum (fun i (_ : i ∈ range (D+1)) => Nat.zero_le ((k+1)^i))
      (show 0 ∈ range (D+1) by simp)
  have hform : A = 2*s*packetFan k D := rfl
  have hA2 : 1 < A := by rw [hform]; nlinarith [Nat.mul_le_mul hs hfan]
  have hd : 2 * degreeLogLog A ≤ degreeLogLog Δ := by
    change degreeLogLog A ≤ B*(s:ℝ)^p*Real.logb 2 ((s:ℝ)+1) at hA
    nlinarith only [hA,hcap]
  apply le_trans _ (le_nativeFanBound hA2 (by omega) hd)
  apply Nat.cast_le.mpr
  rw [hform]
  exact max_le (by nlinarith [Nat.mul_le_mul_left s hfan])
    (Nat.le_mul_of_pos_left _ (by positivity : 0<2*s))

end TapeStorageRates
