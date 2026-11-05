import TapeStorageRates.Statement

/-!
# Inverting the packet-family degree estimate

For each fixed packet size the code lengths already tend to infinity. The inversion chooses a
single such family at each large degree cap and keeps its relation and words.
-/

namespace TapeStorageRates

open Filter DirectedRecovery
open scoped Topology

set_option autoImplicit false

/-- A degree cap may be increased while retaining every code and recovery relation. -/
def SeparatedBinaryFamily.atCap {δ Δ : ℕ} (F : SeparatedBinaryFamily δ) (h : δ ≤ Δ) :
    SeparatedBinaryFamily Δ :=
  { F with degree_le := fun i v => (F.degree_le i v).trans h }

/-- The double logarithm of a degree cap, with logarithms in base two. -/
noncomputable def degreeLogLog (Δ : ℕ) : ℝ := Real.logb 2 (Real.logb 2 (Δ : ℝ))

theorem tendsto_degreeLogLog : Tendsto degreeLogLog atTop atTop := by
  have h : Tendsto (Real.logb 2) atTop atTop := Real.tendsto_logb_atTop (by norm_num)
  exact h.comp (h.comp tendsto_natCast_atTop_atTop)

private theorem le_cap_of_degreeLogLog {δ Δ : ℕ} (hΔ : 2 ≤ Δ)
    (h : degreeLogLog δ ≤ degreeLogLog Δ) : δ ≤ Δ := by
  by_contra! hlt
  have h1 : (1 : ℝ) < Δ := by exact_mod_cast (by omega : 1 < Δ)
  have h2 : (Δ : ℝ) < δ := by exact_mod_cast hlt
  exact (not_lt_of_ge h) (Real.logb_lt_logb (by norm_num) (Real.logb_pos (by norm_num) h1)
    (Real.logb_lt_logb (by norm_num) (by positivity) h2))

/-- Fixed-packet estimates. The binary family at each fixed size `s` has a natural degree cap,
bounded double logarithm of that cap, and limiting lower rate at least `1 - A/s`. -/
def PacketFamilyBounds (k : ℕ) : Prop :=
  ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ᶠ s : ℕ in atTop,
    ∃ δ : ℕ, degreeLogLog δ ≤ B * (s : ℝ) ^ (4 * k ^ 2 + 1) * Real.logb 2 ((s : ℝ) + 1) ∧
      ∃ F : SeparatedBinaryFamily δ, 1 - A / s ≤ liminf (fun i => storageCodeRate (F.code i)) atTop

/-- The inverse scale for degree growth with any positive integer exponent. -/
noncomputable def inverseDegreeScale (p Δ : ℕ) : ℝ :=
  let y := degreeLogLog Δ
  (Real.logb 2 y / y) ^ ((p : ℝ)⁻¹)

theorem tendsto_inverseDegreeScale {p : ℕ} (hp : 0 < p) :
    Tendsto (inverseDegreeScale p) atTop (𝓝 0) := by
  have h := (Real.isLittleO_logb_id_atTop (b := 2)).tendsto_div_nhds_zero
  exact (h.comp tendsto_degreeLogLog).rpow_const_nhds_zero (by positivity : 0 < (p : ℝ)⁻¹)

theorem inverseDegreeScale_tape (k Δ : ℕ) :
    inverseDegreeScale (4*k^2+1) Δ = deficitScale k Δ := by
  simp [inverseDegreeScale, deficitScale, degreeLogLog, one_div]

/-- Choose a batch before the dimension grows. Its reciprocal is within a constant
factor of the inverse scale, and its entire logarithmic degree budget fits the cap. -/
theorem sizes_for_degree_growth {p : ℕ} (hp : 0 < p) {B : ℝ} (hB : 0 < B) (s₀ : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ Δ : ℕ in atTop, ∃ s : ℕ, s₀ ≤ s ∧ 0 < s ∧
      B * (s : ℝ)^p * Real.logb 2 ((s : ℝ)+1) ≤ degreeLogLog Δ ∧
      1 / (s : ℝ) ≤ K * inverseDegreeScale p Δ ∧ inverseDegreeScale p Δ ≤ 1 / s := by
  let D := max 1 (2 * B)
  have hD1 : 1 ≤ D := le_max_left _ _
  have hD : 0 < D := zero_lt_one.trans_le hD1
  have ht : 0 < D * ((s₀ : ℝ) + 1) := by positivity
  refine ⟨2 * D, by positivity, ?_⟩
  filter_upwards [tendsto_degreeLogLog.eventually_ge_atTop 2,
    (tendsto_inverseDegreeScale hp).eventually_lt_const (one_div_pos.2 ht)] with Δ hy hsmall
  let y := degreeLogLog Δ
  have hy2 : (2 : ℝ) ≤ y := hy
  have hypos : 0 < y := by linarith
  have hlog1 : 1 ≤ Real.logb 2 y := by
    simpa using (Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by norm_num) hy2)
  have hlog : 0 < Real.logb 2 y := zero_lt_one.trans_le hlog1
  let x := (y / Real.logb 2 y) ^ (p : ℝ)⁻¹
  have hx : 0 < x := Real.rpow_pos_of_pos (div_pos hypos hlog) _
  have hxp : x ^ p = y / Real.logb 2 y :=
    Real.rpow_inv_natCast_pow (div_nonneg hypos.le hlog.le) hp.ne'
  have hscale : inverseDegreeScale p Δ = x⁻¹ := by
    change (Real.logb 2 y / y) ^ ((p : ℝ)⁻¹) = _
    dsimp only [x]
    rw [← Real.inv_rpow (div_nonneg hypos.le hlog.le), inv_div]
  rw [hscale, ← one_div] at hsmall
  have hlarge : D * ((s₀ : ℝ) + 1) ≤ x := by
    rw [div_lt_div_iff₀ hx ht] at hsmall
    linarith
  let s := ⌊x / D⌋₊
  have hstart : (s₀ : ℝ) + 1 ≤ x / D := (le_div_iff₀ hD).2 (by linarith)
  have hs₀' : s₀ ≤ s := Nat.le_floor (by linarith)
  have hs1n : 1 ≤ s := Nat.le_floor (by push_cast; linarith [show (0 : ℝ) ≤ s₀ from Nat.cast_nonneg _])
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs1n
  have hspos : (0 : ℝ) < s := zero_lt_one.trans_le hs1
  have hsD : (s : ℝ) * D ≤ x := (le_div_iff₀ hD).1 (Nat.floor_le (div_nonneg hx.le hD.le))
  have hxs : x ≤ 2 * D * s := by
    have hfloor : x / D < (s : ℝ) + 1 := Nat.lt_floor_add_one _
    have ht' := (div_lt_iff₀ hD).1 hfloor
    nlinarith [mul_nonneg (sub_nonneg.2 hs1) hD.le]
  have hsx : (s : ℝ) ≤ x := by nlinarith [mul_nonneg hspos.le (sub_nonneg.2 hD1)]
  have hxy : x ≤ y := calc
    x ≤ x ^ p := le_self_pow₀ (hs1.trans hsx) hp.ne'
    _ = y / Real.logb 2 y := hxp
    _ ≤ y := div_le_self hypos.le hlog1
  have hpow : 2 * B * (s : ℝ) ^ p ≤ x ^ p := calc
    2 * B * (s : ℝ) ^ p ≤ D ^ p * (s : ℝ) ^ p :=
      mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_self_pow₀ hD1 hp.ne')) (by positivity)
    _ = ((s : ℝ) * D) ^ p := by rw [mul_pow, mul_comm]
    _ ≤ x ^ p := pow_le_pow_left₀ (by positivity) hsD _
  have hslog : Real.logb 2 ((s : ℝ) + 1) ≤ 2 * Real.logb 2 y := calc
    _ ≤ Real.logb 2 (y ^ 2) := Real.logb_le_logb_of_le (by norm_num) (by positivity)
      (by nlinarith [hsx.trans hxy, mul_nonneg (sub_nonneg.2 hy2) hypos.le])
    _ = _ := by rw [Real.logb_pow]; norm_num
  have hcap : B * (s : ℝ)^p * Real.logb 2 ((s : ℝ)+1) ≤ y := calc
    B * (s : ℝ) ^ p * Real.logb 2 ((s : ℝ) + 1) ≤ B * (s : ℝ) ^ p * (2 * Real.logb 2 y) := by
      gcongr
    _ = (2 * B * (s : ℝ) ^ p) * Real.logb 2 y := by ring
    _ ≤ x ^ p * Real.logb 2 y := mul_le_mul_of_nonneg_right hpow hlog.le
    _ = y := by rw [hxp, div_mul_cancel₀ _ hlog.ne']
  refine ⟨s, hs₀', hs1n, hcap, ?_, ?_⟩
  · rw [hscale, ← div_eq_mul_inv, div_le_div_iff₀ hspos hx]
    linarith
  · rw [hscale, ← one_div]
    exact one_div_le_one_div_of_le hspos hsx

/-- The fixed-packet estimates imply the exact all-cap rate envelope. -/
theorem all_caps_of_packetFamilyBounds {k : ℕ} (h : PacketFamilyBounds k) :
    RateWitnesses k := by
  obtain ⟨A,B,hA,hB,hpacket⟩ := h
  obtain ⟨s₀,hs₀⟩ := eventually_atTop.1 hpacket
  obtain ⟨K,hK,hsize⟩ := sizes_for_degree_growth (p := 4*k^2+1) (Nat.succ_pos _) hB s₀
  refine ⟨A*K, mul_pos hA hK, ?_⟩
  filter_upwards [hsize,eventually_ge_atTop 2] with Δ h hΔ
  obtain ⟨s,hs,_,hcap,hcost,_⟩ := h
  obtain ⟨δ,hδ,F,hF⟩ := hs₀ s hs
  rw [inverseDegreeScale_tape] at hcost
  exact ⟨F.atCap (le_cap_of_degreeLogLog hΔ (hδ.trans hcap)), (sub_le_sub_left (by
    simpa [div_eq_mul_inv, mul_assoc] using mul_le_mul_of_nonneg_left hcost hA.le) 1).trans hF⟩

end TapeStorageRates
