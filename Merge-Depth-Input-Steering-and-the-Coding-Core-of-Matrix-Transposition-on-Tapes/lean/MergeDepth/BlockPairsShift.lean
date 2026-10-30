import MergeDepth.BlockPairsTransfer

/-!
# Block pairs: Conjecture S yields a good odd shift (Proposition 7.5)

The probabilities are over the odd residues `ξ` modulo `P` (`oddRange (dnpPeriod s0 m)`, uniform).

* `integral_perTent_shift`, `profileMean_eq`: every periodic tent has integral `Π̂_κ²/2` over a
  period, so `μ_k = n_κ / (4N)` (for every `k` and `κ ≥ 1`).
* `cantelli_interval`: Cantelli's inequality `Pr[g ≤ μ - λ] ≤ σ²/(σ² + λ²)` for `t` uniform on
  `[0, L)` and continuous `g`.
* `notGoodProb s0 m a k dir`: the probability that `k` is not `a`-good in direction `dir`
  (`β^{(a)}_k` for `dir = true`); `shiftTheta m a k` `= θ_k`; `betaAvg` `= β_a`.
* `notGoodProb_le`: **Proposition 7.5(a)**, `θ_k ≤ 1/2`, the two directions fail with the same
  probability, and `β^{(a)}_k ≤ V^{(a)}_k/(V^{(a)}_k + (1 - θ_k)²) + 2^{κ+2-s₀}`.
* `prob_some_bad_le`: **Proposition 7.5(b)**, the probability that `Γ_{a,±}(ξ) < γ|𝒦|` for some
  `1 ≤ a ≤ a₀` and some sign is at most `2/(1-γ) ∑_{a ≤ a₀} β_a` (for all `m`, `s₀`, `γ < 1`).
* `good_shift_prob`: **Proposition 7.5(c)**, if `ConjectureS a` holds for `a = 1, …, a₀`, then for
  some `m₀` and all `m ≥ m₀`, `(∗)` holds and, for every `s₀ > m`, with probability at least `1/2`
  every `Γ_{a,±}(ξ) ≥ γ|𝒦|` (`γ < 1`).
-/

namespace MergeDepth

open Finset DirectedReciprocity MeasureTheory

theorem integral_tent_half {w N : ℝ} (hw : 0 ≤ w) (hwN : w ≤ N) :
    ∫ y in (0 : ℝ)..(N / 2), tent w y = w ^ 2 / 4 := by
  have h1 : IntervalIntegrable (tent w) volume 0 (w / 2) := (continuous_tent w).intervalIntegrable _ _
  have h2 : IntervalIntegrable (tent w) volume (w / 2) (N / 2) :=
    (continuous_tent w).intervalIntegrable _ _
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2]
  have e1 : ∫ y in (0 : ℝ)..(w / 2), tent w y = ∫ y in (0 : ℝ)..(w / 2), (w - 2 * y) := by
    refine intervalIntegral.integral_congr fun y hy => ?_
    rw [Set.uIcc_of_le (by linarith)] at hy
    unfold tent; rw [abs_of_nonneg hy.1, max_eq_right (by linarith [hy.2])]
  have e2 : ∫ y in (w / 2)..(N / 2), tent w y = ∫ y in (w / 2)..(N / 2), (0 : ℝ) := by
    refine intervalIntegral.integral_congr fun y hy => ?_
    rw [Set.uIcc_of_le (by linarith)] at hy
    unfold tent; rw [abs_of_nonneg (by linarith [hy.1]), max_eq_left (by linarith [hy.1])]
  rw [e1, e2, intervalIntegral.integral_zero, add_zero,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun y => w * y - y ^ 2)]
  · ring
  · intro x _
    have := ((hasDerivAt_id x).const_mul w).sub (hasDerivAt_pow 2 x)
    convert this using 1
    · ext y; simp
    · simp
  · exact (continuous_const.sub (continuous_const.mul continuous_id)).intervalIntegrable _ _

theorem integral_tent_sym {w N : ℝ} (hw : 0 ≤ w) (hwN : w ≤ N) :
    ∫ y in (-(N / 2))..(N / 2), tent w y = w ^ 2 / 2 := by
  have hc := (continuous_tent w)
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0) (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _)]
  have hneg : ∫ y in (-(N / 2))..0, tent w y = ∫ y in (0 : ℝ)..(N / 2), tent w y := by
    have := intervalIntegral.integral_comp_neg (a := 0) (b := N / 2) (tent w)
    rw [neg_zero] at this
    rw [← this]; congr 1; ext x; simp [tent, abs_neg]
  rw [hneg, integral_tent_half hw hwN]; ring

theorem perTent_eq_tent {N w y : ℝ} (hN : 0 < N) (hwN : w ≤ N) (hy : |y| ≤ N / 2) :
    perTent N w y = tent w y := by
  unfold perTent
  rw [tsum_eq_single 0]
  · simp
  · intro l hl
    apply tent_eq_zero
    have hl' : (1 : ℝ) ≤ |(l : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hl
    have : N ≤ |(l : ℝ) * N| := by rw [abs_mul, abs_of_pos hN]; nlinarith
    have := abs_sub_abs_le_abs_sub ((l : ℝ) * N) y
    rw [abs_sub_comm] at this
    linarith

theorem perTent_periodic {N w : ℝ} : Function.Periodic (perTent N w) N := by
  intro y; have := perTent_add_int_mul N w y 1; simpa using this

theorem integral_perTent_shift {N w : ℝ} (hN : 0 < N) (hw : 0 ≤ w) (hwN : w ≤ N) (c : ℝ) :
    ∫ t in (0 : ℝ)..N, perTent N w (t + c) = w ^ 2 / 2 := by
  rw [intervalIntegral.integral_comp_add_right, zero_add, add_comm N c,
    perTent_periodic.intervalIntegral_add_eq c (-(N / 2)),
    show -(N / 2) + N = N / 2 by ring, ← integral_tent_sym hw hwN]
  refine intervalIntegral.integral_congr fun y hy => ?_
  rw [Set.uIcc_of_le (by linarith)] at hy
  exact perTent_eq_tent hN hwN (abs_le.mpr ⟨hy.1, hy.2⟩)

/-- `μ_k = n_κ / (4N)`. -/
theorem profileMean_eq {m k κ : ℕ} (hκ : 1 ≤ κ) :
    profileMean m k κ = ((m - κ + 1 : ℕ) : ℝ) / (4 * ((m : ℝ) + 1)) := by
  unfold profileMean profile
  have hN : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hw : 0 < piHat m κ := piHat_pos
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum]
  · rw [Finset.sum_congr rfl fun S _ => intervalIntegral.integral_finsetSum ?_]
    · have hterm : ∀ S S' : Finset ℕ, ∫ t in (0 : ℝ)..((m : ℝ) + 1),
          perTent ((m : ℝ) + 1) (piHat m κ) (apexHat m k S + t - valleyHat m κ S') =
          piHat m κ ^ 2 / 2 := by
        intro S S'
        rw [← integral_perTent_shift hN hw.le (piHat_le m κ) (apexHat m k S - valleyHat m κ S')]
        congr 1; ext t; congr 1; ring
      simp only [hterm, Finset.sum_const, Finset.card_powerset, Nat.card_Icc, nsmul_eq_mul]
      push_cast
      unfold piHat
      rw [show (2 : ℝ) ^ κ = 2 ^ (κ - 1) * 2 by rw [← pow_succ, Nat.sub_add_cancel hκ]]
      field_simp
      push_cast
      ring
    · intro S' _
      exact ((continuous_perTent hN (piHat_le m κ)).comp (by fun_prop)).intervalIntegrable _ _
  · intro S _
    exact (continuous_finsetSum _ fun S' _ => (continuous_perTent hN (piHat_le m κ)).comp
      (by fun_prop)).intervalIntegrable _ _


/-- **Cantelli's inequality** for `t` uniform on `[0, L)`: with `μ` the mean and `σ²` the variance of
a continuous `g`, the probability that `g(t) ≤ μ - λ` is at most `σ²/(σ² + λ²)` for `λ > 0`. -/
theorem cantelli_interval {g : ℝ → ℝ} (hg : Continuous g) {L lam : ℝ} (hL : 0 < L) (hlam : 0 < lam) :
    L⁻¹ * (volume {t ∈ Set.Ico (0 : ℝ) L | g t ≤ L⁻¹ * (∫ t in (0 : ℝ)..L, g t) - lam}).toReal ≤
      (L⁻¹ * ∫ t in (0 : ℝ)..L, (g t - L⁻¹ * ∫ t in (0 : ℝ)..L, g t) ^ 2) /
        ((L⁻¹ * ∫ t in (0 : ℝ)..L, (g t - L⁻¹ * ∫ t in (0 : ℝ)..L, g t) ^ 2) + lam ^ 2) := by
  set μ := L⁻¹ * ∫ t in (0 : ℝ)..L, g t with hμ
  set σ2 := L⁻¹ * ∫ t in (0 : ℝ)..L, (g t - μ) ^ 2 with hσ2
  have hσ2nn : 0 ≤ σ2 := by
    apply mul_nonneg (inv_nonneg.mpr hL.le)
    exact intervalIntegral.integral_nonneg hL.le fun t _ => sq_nonneg _
  set u := σ2 / lam with hu
  have hu0 : 0 ≤ u := div_nonneg hσ2nn hlam.le
  set hfun : ℝ → ℝ := fun t => (u - (g t - μ)) ^ 2 with hhfun
  have hcont : Continuous hfun := by fun_prop
  -- the integral of `hfun`
  have hint_g : ∫ t in (0 : ℝ)..L, (g t - μ) = 0 := by
    rw [intervalIntegral.integral_sub (hg.intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_const, hμ, sub_zero, smul_eq_mul, ← mul_assoc,
      mul_inv_cancel₀ hL.ne', one_mul, sub_self]
  have hint : ∫ t in (0 : ℝ)..L, hfun t = L * u ^ 2 + L * σ2 := by
    have e : ∀ t, hfun t = u ^ 2 + (-(2 * u)) * (g t - μ) + (g t - μ) ^ 2 := fun t => by
      simp only [hhfun]; ring
    simp only [e]
    have hc1 : Continuous fun t => u ^ 2 + -(2 * u) * (g t - μ) := by fun_prop
    have hc2 : Continuous fun t => (g t - μ) ^ 2 := by fun_prop
    have hc3 : Continuous fun t => -(2 * u) * (g t - μ) := by fun_prop
    have i1 := intervalIntegral.integral_add (μ := volume) (a := 0) (b := L)
      (f := fun t => u ^ 2 + -(2 * u) * (g t - μ)) (g := fun t => (g t - μ) ^ 2)
      (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _)
    have i2 := intervalIntegral.integral_add (μ := volume) (a := 0) (b := L)
      (f := fun _ => u ^ 2) (g := fun t => -(2 * u) * (g t - μ))
      intervalIntegrable_const (hc3.intervalIntegrable _ _)
    have i3 := intervalIntegral.integral_const_mul (μ := volume) (a := 0) (b := L) (-(2 * u))
      (fun t => g t - μ)
    rw [i1, i2, i3, hint_g, intervalIntegral.integral_const, hσ2]
    field_simp; simp
  -- Markov on the bad set
  set B := {t ∈ Set.Ico (0 : ℝ) L | g t ≤ μ - lam} with hB
  set c := (u + lam) ^ 2 with hc
  have hcpos : 0 < c := by positivity
  have hsub : B ⊆ {0} ∪ ({t | c ≤ hfun t} ∩ Set.Ioc 0 L) := by
    rintro t ⟨⟨h0, h1⟩, hgt⟩
    rcases eq_or_lt_of_le h0 with h | h
    · left; exact h.symm
    · right
      refine ⟨?_, h, h1.le⟩
      simp only [Set.mem_ofPred_eq, hhfun, hc]
      exact pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hmeasS : MeasurableSet {t | c ≤ hfun t} := measurableSet_le measurable_const hcont.measurable
  have hvol : (volume B).toReal ≤ (volume.restrict (Set.Ioc 0 L)).real {t | c ≤ hfun t} := by
    rw [Measure.real, Measure.restrict_apply hmeasS]
    refine ENNReal.toReal_mono ?_ ?_
    · exact ne_top_of_le_ne_top (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
        (measure_mono Set.inter_subset_right)
    · calc volume B ≤ volume ({0} ∪ ({t | c ≤ hfun t} ∩ Set.Ioc 0 L)) := measure_mono hsub
        _ ≤ volume ({0} : Set ℝ) + volume ({t | c ≤ hfun t} ∩ Set.Ioc 0 L) := measure_union_le _ _
        _ = volume ({t | c ≤ hfun t} ∩ Set.Ioc 0 L) := by simp
  have hmarkov := mul_meas_ge_le_integral_of_nonneg (μ := volume.restrict (Set.Ioc 0 L))
    (Filter.Eventually.of_forall fun t => sq_nonneg _)
    ((hcont.integrableOn_Icc (a := 0) (b := L)).mono_set Set.Ioc_subset_Icc_self) c
  rw [← intervalIntegral.integral_of_le hL.le, hint] at hmarkov
  have hBc : c * (volume B).toReal ≤ L * u ^ 2 + L * σ2 :=
    le_trans (mul_le_mul_of_nonneg_left hvol hcpos.le) hmarkov
  -- algebra
  have hden : 0 < σ2 + lam ^ 2 := by positivity
  rw [inv_mul_le_iff₀ hL, mul_div_assoc', le_div_iff₀ hden]
  have h1 : c * lam ^ 2 = (σ2 + lam ^ 2) ^ 2 := by rw [hc, hu]; field_simp
  have h2 : (L * u ^ 2 + L * σ2) * lam ^ 2 = L * σ2 * (σ2 + lam ^ 2) := by
    rw [hu]; field_simp
  have h3 := mul_le_mul_of_nonneg_right hBc (sq_nonneg lam)
  have key : (volume B).toReal * (σ2 + lam ^ 2) * (σ2 + lam ^ 2) ≤ L * σ2 * (σ2 + lam ^ 2) := by
    calc (volume B).toReal * (σ2 + lam ^ 2) * (σ2 + lam ^ 2)
        = c * (volume B).toReal * lam ^ 2 := by linear_combination (-(volume B).toReal) * h1
      _ ≤ (L * u ^ 2 + L * σ2) * lam ^ 2 := h3
      _ = L * σ2 * (σ2 + lam ^ 2) := h2
  exact le_of_mul_le_mul_right key hden


/-- The probability, over odd shifts, that the coarse level `k` is not `a`-good in direction `dir`
(for `dir = true` this is `β^{(a)}_k`). -/
noncomputable def notGoodProb (s0 m a k : ℕ) (dir : Bool) : ℝ :=
  (((oddRange (dnpPeriod s0 m)).filter fun ξ =>
      2 ^ (a + 7) * classStraddleCount s0 m k (cancellerBelow m a k) dir ξ <
        2 ^ (k + 2) * scaleR s0 k).card : ℝ) / (oddRange (dnpPeriod s0 m)).card

/-- `θ_k = N 2^{κ-k} / (2^{a+4} n_κ²)`, `κ = κ_a(k)`. -/
noncomputable def shiftTheta (m a k : ℕ) : ℝ :=
  ((m : ℝ) + 1) * 2 ^ (cancellerBelow m a k - k) /
    (2 ^ (a + 4) * ((m - cancellerBelow m a k + 1 : ℕ) : ℝ) ^ 2)

theorem dnpPeriod_even (s0 m : ℕ) : dnpPeriod s0 m % 2 = 0 := by unfold dnpPeriod; omega

/-- The two directions fail with the same probability. -/
theorem notGoodProb_false (s0 m a k : ℕ) : notGoodProb s0 m a k false = notGoodProb s0 m a k true := by
  classical
  unfold notGoodProb
  congr 2
  rw [← card_filter_oddRange_neg (dnpPeriod_even s0 m)]
  congr 1
  refine Finset.filter_congr fun ξ hξ => ?_
  have hξP : ξ ≤ dnpPeriod s0 m := by simp only [oddRange, mem_filter, mem_range] at hξ; omega
  rw [classStraddleCount_false_eq (Nat.sub_le _ _), Nat.sub_sub_self hξP]

/-- Consequences of the size condition `(∗)` for a coarse level. -/
theorem coarse_canceller_props {s0 m a0 a k : ℕ} (ha : 1 ≤ a) (haa0 : a ≤ a0) (hms : m < s0)
    (hsize : 4 * (jZero m + a0) ≤ m + 1) (hk : k ∈ coarseZone m) :
    let κ := cancellerBelow m a k
    1 ≤ k ∧ k < κ ∧ κ ≤ m ∧ isCanceller m a κ = true ∧
    strokeLen s0 m κ ≤ scaleR s0 k ∧ scaleR s0 k ≤ 2 ^ (a + 2) * strokeLen s0 m κ ∧
    m + 1 ≤ 2 * (m - κ + 1) ∧ κ ≤ k + jZero m + a := by
  intro κ
  unfold coarseZone at hk
  unfold jZero at hsize
  rw [mem_Icc] at hk
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := @cancellerBelow_props s0 m a k ha hms.le hk.1 (by omega) (by omega)
  have hκ : κ = k + (Nat.log 2 (m + 1) + 1) +
      ((m - (k + (Nat.log 2 (m + 1) + 1))) % (a + 1) + 1) % (a + 1) := rfl
  have hδ : ((m - (k + (Nat.log 2 (m + 1) + 1))) % (a + 1) + 1) % (a + 1) < a + 1 :=
    Nat.mod_lt _ (by omega)
  refine ⟨hk.1, by omega, h2, h3, h4, h5, h6, ?_⟩
  unfold jZero; omega


theorem profileVariance_nonneg (m k κ : ℕ) : 0 ≤ profileVariance m k κ := by
  unfold profileVariance
  apply mul_nonneg (inv_nonneg.mpr (by positivity))
  exact intervalIntegral.integral_nonneg (by positivity) fun t _ => sq_nonneg _

theorem relVariance_nonneg (m k κ : ℕ) : 0 ≤ relVariance m k κ :=
  div_nonneg (profileVariance_nonneg m k κ) (sq_nonneg _)

/-- **Proposition 7.5(a)**: under the size condition `(∗)`, for `1 ≤ a ≤ a₀` and `k ∈ 𝒦`,
`θ_k ≤ 1/2`, the direction `-` fails with the same probability `β^{(a)}_k` as the direction `+`,
and `β^{(a)}_k ≤ V^{(a)}_k / (V^{(a)}_k + (1 - θ_k)²) + 2^{κ+2-s₀}`. -/
theorem notGoodProb_le {s0 m a0 a k : ℕ} (ha : 1 ≤ a) (haa0 : a ≤ a0) (hms : m < s0)
    (hsize : 4 * (jZero m + a0) ≤ m + 1) (hk : k ∈ coarseZone m) :
    shiftTheta m a k ≤ 1 / 2 ∧
    notGoodProb s0 m a k false = notGoodProb s0 m a k true ∧
    notGoodProb s0 m a k true ≤
      relVarianceA m a k / (relVarianceA m a k + (1 - shiftTheta m a k) ^ 2) +
        2 ^ (cancellerBelow m a k + 2) / 2 ^ s0 := by
  classical
  obtain ⟨hk1, hkκ, hκm, -, hpi, hRk, hhalf, -⟩ := coarse_canceller_props ha haa0 hms hsize hk
  set κ := cancellerBelow m a k with hκdef
  set n : ℝ := ((m - κ + 1 : ℕ) : ℝ) with hndef
  set N : ℝ := (m : ℝ) + 1 with hNdef
  have hn : 0 < n := by positivity
  have hN : 0 < N := by positivity
  have hNn : N ≤ 2 * n := by
    have : ((m + 1 : ℕ) : ℝ) ≤ ((2 * (m - κ + 1) : ℕ) : ℝ) := by exact_mod_cast hhalf
    push_cast at this; rw [hNdef, hndef]; push_cast; linarith
  have hsκ : κ ≤ s0 := by omega
  have hR : (scaleR s0 k : ℝ) = 2 ^ (κ - k) * 2 ^ (s0 - κ) := by
    unfold scaleR; push_cast; rw [← pow_add]; congr 1; omega
  have hP : (strokeLen s0 m κ : ℝ) = n * 2 ^ (s0 - κ) := by
    rw [hndef]; unfold strokeLen scaleR; push_cast; ring
  have hpow : (2 : ℝ) ^ (κ - k) ≤ 2 ^ (a + 2) * n := by
    have h : (scaleR s0 k : ℝ) ≤ 2 ^ (a + 2) * strokeLen s0 m κ := by exact_mod_cast hRk
    rw [hR, hP] at h
    have h2 : (0 : ℝ) < 2 ^ (s0 - κ) := by positivity
    nlinarith
  have hθ : shiftTheta m a k ≤ 1 / 2 := by
    unfold shiftTheta
    rw [← hκdef, ← hndef, ← hNdef, div_le_iff₀ (by positivity)]
    calc N * 2 ^ (κ - k) ≤ N * (2 ^ (a + 2) * n) := mul_le_mul_of_nonneg_left hpow hN.le
      _ ≤ 2 * n * (2 ^ (a + 2) * n) := mul_le_mul_of_nonneg_right hNn (by positivity)
      _ = 1 / 2 * (2 ^ (a + 4) * n ^ 2) := by ring
  refine ⟨hθ, notGoodProb_false s0 m a k, ?_⟩
  -- the threshold `τ_k M_k`
  set τ : ℝ := (scaleR s0 k : ℝ) / (2 ^ (a + 6) * strokeLen s0 m κ) with hτdef
  have hpiPos : (0 : ℝ) < strokeLen s0 m κ := by exact_mod_cast strokeLen_pos s0 m κ
  have hτM : τ * (2 ^ (k + 1) * strokeLen s0 m κ) = (2 ^ (k + 2) * scaleR s0 k : ℝ) / 2 ^ (a + 7) := by
    rw [hτdef]; field_simp; ring
  have hthr : ∀ ξ : ℕ, (2 ^ (a + 7) * classStraddleCount s0 m k κ true ξ < 2 ^ (k + 2) * scaleR s0 k ↔
      (classStraddleCount s0 m k κ true ξ : ℝ) < τ * (2 ^ (k + 1) * strokeLen s0 m κ)) := by
    intro ξ
    rw [hτM, lt_div_iff₀ (by positivity), mul_comm]
    exact_mod_cast Iff.rfl
  have hprob : notGoodProb s0 m a k true =
      (((oddRange (dnpPeriod s0 m)).filter fun ξ =>
        (classStraddleCount s0 m k κ true ξ : ℝ) < τ * (2 ^ (k + 1) * strokeLen s0 m κ)).card : ℝ) /
        (oddRange (dnpPeriod s0 m)).card := by
    unfold notGoodProb
    rw [← hκdef]
    congr 3
    exact Finset.filter_congr fun ξ _ => hthr ξ
  have htrans := prob_straddle_vs_profile hk1 hkκ hκm hms hpi τ true
  rw [← hprob] at htrans
  have hle1 : notGoodProb s0 m a k true ≤ N⁻¹ *
      (volume {t ∈ Set.Ico (0 : ℝ) N | profile m k κ t < τ}).toReal + 2 ^ (κ + 2) / 2 ^ s0 := by
    have := (abs_le.mp htrans).2; linarith
  -- Cantelli
  set μ := profileMean m k κ with hμdef
  have hμ : μ = n / (4 * N) := by rw [hμdef, profileMean_eq (by omega)]
  have hμpos : 0 < μ := by rw [hμ]; positivity
  have hτθ : τ = shiftTheta m a k * μ := by
    rw [hτdef, hμ, hR]
    unfold shiftTheta
    rw [← hκdef, ← hndef, ← hNdef, hP]
    field_simp; ring
  set θ := shiftTheta m a k with hθdef
  set lam := (1 - θ) * μ with hlamdef
  have hlam : 0 < lam := mul_pos (by linarith) hμpos
  have hcant := cantelli_interval (continuous_profile m k κ) hN hlam
  have hμ' : N⁻¹ * ∫ t in (0 : ℝ)..N, profile m k κ t = μ := rfl
  rw [hμ'] at hcant
  have hvar : N⁻¹ * ∫ t in (0 : ℝ)..N, (profile m k κ t - μ) ^ 2 = relVarianceA m a k * μ ^ 2 := by
    unfold relVarianceA relVariance
    rw [← hκdef]
    change profileVariance m k κ = profileVariance m k κ / μ ^ 2 * μ ^ 2
    field_simp
  rw [hvar] at hcant
  have hsub : {t ∈ Set.Ico (0 : ℝ) N | profile m k κ t < τ} ⊆
      {t ∈ Set.Ico (0 : ℝ) N | profile m k κ t ≤ μ - lam} := by
    intro t ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rw [hlamdef]; nlinarith [hτθ]
  have hvolle : (volume {t ∈ Set.Ico (0 : ℝ) N | profile m k κ t < τ}).toReal ≤
      (volume {t ∈ Set.Ico (0 : ℝ) N | profile m k κ t ≤ μ - lam}).toReal :=
    ENNReal.toReal_mono (ne_top_of_le_ne_top (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top)
      (measure_mono fun t ht => ht.1)) (measure_mono hsub)
  have hV := relVariance_nonneg m k κ
  have hfinal : relVarianceA m a k * μ ^ 2 / (relVarianceA m a k * μ ^ 2 + lam ^ 2) =
      relVarianceA m a k / (relVarianceA m a k + (1 - θ) ^ 2) := by
    rw [hlamdef]
    have hden : 0 < relVarianceA m a k + (1 - θ) ^ 2 := by
      have : 0 ≤ relVarianceA m a k := hV
      nlinarith
    field_simp
  rw [hfinal] at hcant
  have hNinv : 0 ≤ N⁻¹ := inv_nonneg.mpr hN.le
  calc notGoodProb s0 m a k true
      ≤ N⁻¹ * (volume {t ∈ Set.Ico (0 : ℝ) N | profile m k κ t < τ}).toReal +
          2 ^ (κ + 2) / 2 ^ s0 := hle1
    _ ≤ N⁻¹ * (volume {t ∈ Set.Ico (0 : ℝ) N | profile m k κ t ≤ μ - lam}).toReal +
          2 ^ (κ + 2) / 2 ^ s0 := by gcongr
    _ ≤ relVarianceA m a k / (relVarianceA m a k + (1 - θ) ^ 2) + 2 ^ (κ + 2) / 2 ^ s0 := by
        gcongr


/-- `β_a = |𝒦|⁻¹ ∑_{k ∈ 𝒦} β^{(a)}_k`. -/
noncomputable def betaAvg (s0 m a : ℕ) : ℝ :=
  ((coarseZone m).card : ℝ)⁻¹ * ∑ k ∈ coarseZone m, notGoodProb s0 m a k true

theorem notGoodProb_nonneg (s0 m a k : ℕ) (dir : Bool) : 0 ≤ notGoodProb s0 m a k dir := by
  unfold notGoodProb; positivity

theorem betaAvg_nonneg (s0 m a : ℕ) : 0 ≤ betaAvg s0 m a := by
  unfold betaAvg
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun k _ => notGoodProb_nonneg _ _ _ _ _)

/-- Markov's inequality for the number of `a`-good levels. -/
theorem card_bad_mul_le (s0 m a : ℕ) (dir : Bool) {γ : ℝ} :
    (1 - γ) * (coarseZone m).card * (((oddRange (dnpPeriod s0 m)).filter fun ξ : ℕ =>
        (goodCount s0 m a dir ξ : ℝ) < γ * ((coarseZone m).card : ℝ)).card : ℝ) ≤
      ∑ k ∈ coarseZone m, (((oddRange (dnpPeriod s0 m)).filter fun ξ =>
        2 ^ (a + 7) * classStraddleCount s0 m k (cancellerBelow m a k) dir ξ <
          2 ^ (k + 2) * scaleR s0 k).card : ℝ) := by
  set Ω := oddRange (dnpPeriod s0 m)
  set K := coarseZone m
  set bad : ℕ → ℕ → Prop := fun k ξ =>
    2 ^ (a + 7) * classStraddleCount s0 m k (cancellerBelow m a k) dir ξ < 2 ^ (k + 2) * scaleR s0 k
  have hcount : ∀ ξ, ((K.filter fun k => bad k ξ).card : ℝ) = K.card - goodCount s0 m a dir ξ := by
    intro ξ
    have h := Finset.card_filter_add_card_filter_not (s := K) (fun k => bad k ξ)
    have hg : goodCount s0 m a dir ξ = (K.filter fun k => ¬ bad k ξ).card := by
      unfold goodCount goodLevels
      congr 1
      exact Finset.filter_congr fun k _ => by simp only [bad, not_lt]
    rw [hg]
    have h' : ((K.filter fun k => bad k ξ).card : ℝ) + (K.filter fun k => ¬ bad k ξ).card = K.card := by
      exact_mod_cast h
    linarith
  have hswap : ∑ k ∈ K, ((Ω.filter fun ξ : ℕ => bad k ξ).card : ℝ) =
      ∑ ξ ∈ Ω, ((K.filter fun k => bad k ξ).card : ℝ) := by
    simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    exact Finset.sum_comm
  change (1 - γ) * K.card * ((Ω.filter fun ξ : ℕ => (goodCount s0 m a dir ξ : ℝ) < γ * (K.card : ℝ)).card : ℝ) ≤
    ∑ k ∈ K, ((Ω.filter fun ξ : ℕ => bad k ξ).card : ℝ)
  rw [hswap, Finset.sum_congr rfl fun ξ _ => hcount ξ]
  have hle : ∀ ξ ∈ Ω, (0 : ℝ) ≤ K.card - goodCount s0 m a dir ξ := by
    intro ξ _
    have : goodCount s0 m a dir ξ ≤ K.card := Finset.card_filter_le _ _
    have : (goodCount s0 m a dir ξ : ℝ) ≤ K.card := by exact_mod_cast this
    linarith
  calc (1 - γ) * K.card * ((Ω.filter fun ξ : ℕ => (goodCount s0 m a dir ξ : ℝ) < γ * (K.card : ℝ)).card : ℝ)
      = ∑ ξ ∈ Ω.filter (fun ξ => (goodCount s0 m a dir ξ : ℝ) < γ * (K.card : ℝ)), (1 - γ) * K.card := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ ∑ ξ ∈ Ω.filter (fun ξ => (goodCount s0 m a dir ξ : ℝ) < γ * (K.card : ℝ)),
          ((K.card : ℝ) - goodCount s0 m a dir ξ) := by
        refine Finset.sum_le_sum fun ξ hξ => ?_
        have := (Finset.mem_filter.mp hξ).2
        linarith
    _ ≤ ∑ ξ ∈ Ω, ((K.card : ℝ) - goodCount s0 m a dir ξ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun ξ hξ _ => hle ξ hξ

/-- **Proposition 7.5(b)**: the probability that `Γ_{a,±}(ξ) < γ|𝒦|` for some `1 ≤ a ≤ a₀` and some
sign is at most `2/(1-γ) ∑_{a ≤ a₀} β_a` (no size condition is needed). -/
theorem prob_some_bad_le (s0 m a0 : ℕ) {γ : ℝ} (hγ1 : γ < 1) :
    (((oddRange (dnpPeriod s0 m)).filter fun ξ : ℕ => ∃ a ∈ Icc (1 : ℕ) a0, ∃ dir : Bool,
        (goodCount s0 m a dir ξ : ℝ) < γ * ((coarseZone m).card : ℝ)).card : ℝ) /
        (oddRange (dnpPeriod s0 m)).card ≤
      2 / (1 - γ) * ∑ a ∈ Icc 1 a0, betaAvg s0 m a := by
  set Ω := oddRange (dnpPeriod s0 m) with hΩdef
  set K := coarseZone m
  have hΩpos : (0 : ℝ) < Ω.card := by
    have : 0 < Ω.card := by
      obtain ⟨M', hM'⟩ : ∃ M', dnpPeriod s0 m = 2 * M' := ⟨dnpPeriod s0 m / 2, by
        have := dnpPeriod_even s0 m; omega⟩
      have hpos : 0 < dnpPeriod s0 m := by
        unfold dnpPeriod; exact Nat.mul_pos (by norm_num) (strokeLen_pos _ _ _)
      change 0 < (oddRange (dnpPeriod s0 m)).card
      rw [hM', card_oddRange_two_mul]; omega
    exact_mod_cast this
  have h1γ : 0 < 1 - γ := by linarith
  rcases Nat.eq_zero_or_pos K.card with hK | hK
  · -- no coarse level: the event is impossible
    have hempty : (Ω.filter fun ξ : ℕ => ∃ a ∈ Icc (1 : ℕ) a0, ∃ dir : Bool,
        (goodCount s0 m a dir ξ : ℝ) < γ * (K.card : ℝ)) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr fun ξ _ => ?_
      push Not
      intro a _ dir
      rw [hK, Nat.cast_zero, mul_zero]; positivity
    rw [hempty, card_empty, Nat.cast_zero, zero_div]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun a _ => betaAvg_nonneg _ _ _)
  have hKpos : (0 : ℝ) < K.card := by exact_mod_cast hK
  -- union bound
  have hsub : (Ω.filter fun ξ : ℕ => ∃ a ∈ Icc (1 : ℕ) a0, ∃ dir : Bool,
      (goodCount s0 m a dir ξ : ℝ) < γ * (K.card : ℝ)) ⊆
      (Icc 1 a0).biUnion fun a => (Finset.univ : Finset Bool).biUnion fun dir =>
        Ω.filter fun ξ : ℕ => (goodCount s0 m a dir ξ : ℝ) < γ * (K.card : ℝ) := by
    intro ξ hξ
    obtain ⟨hξΩ, a, ha, dir, hbad⟩ := Finset.mem_filter.mp hξ
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter]
    exact ⟨a, ha, dir, hξΩ, hbad⟩
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_biUnion_le)
  have hcard' : ((Ω.filter fun ξ : ℕ => ∃ a ∈ Icc (1 : ℕ) a0, ∃ dir : Bool,
      (goodCount s0 m a dir ξ : ℝ) < γ * (K.card : ℝ)).card : ℝ) ≤
      ∑ a ∈ Icc 1 a0, ∑ dir : Bool,
        ((Ω.filter fun ξ : ℕ => (goodCount s0 m a dir ξ : ℝ) < γ * (K.card : ℝ)).card : ℝ) := by
    have h2 : ∀ a ∈ Icc 1 a0, ((Finset.univ : Finset Bool).biUnion fun dir =>
        Ω.filter fun ξ : ℕ => (goodCount s0 m a dir ξ : ℝ) < γ * (K.card : ℝ)).card ≤
        ∑ dir : Bool, (Ω.filter fun ξ : ℕ => (goodCount s0 m a dir ξ : ℝ) < γ * (K.card : ℝ)).card :=
      fun a _ => Finset.card_biUnion_le
    have := hcard.trans (Finset.sum_le_sum h2)
    exact_mod_cast this
  -- each term
  have hterm : ∀ a ∈ Icc 1 a0, ∀ dir : Bool,
      ((Ω.filter fun ξ : ℕ => (goodCount s0 m a dir ξ : ℝ) < γ * (K.card : ℝ)).card : ℝ) ≤
        Ω.card * betaAvg s0 m a / (1 - γ) := by
    intro a _ dir
    have hm := card_bad_mul_le s0 m a dir (γ := γ)
    have hsum : ∑ k ∈ K, (((oddRange (dnpPeriod s0 m)).filter fun ξ =>
        2 ^ (a + 7) * classStraddleCount s0 m k (cancellerBelow m a k) dir ξ <
          2 ^ (k + 2) * scaleR s0 k).card : ℝ) = Ω.card * (K.card * betaAvg s0 m a) := by
      have hK' : ((coarseZone m).card : ℝ) ≠ 0 := hKpos.ne'
      have hbeta : ((coarseZone m).card : ℝ) * betaAvg s0 m a =
          ∑ k ∈ coarseZone m, notGoodProb s0 m a k true := by
        unfold betaAvg; rw [← mul_assoc, mul_inv_cancel₀ hK', one_mul]
      rw [hbeta, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      have : notGoodProb s0 m a k dir = notGoodProb s0 m a k true := by
        cases dir
        · exact notGoodProb_false s0 m a k
        · rfl
      rw [← this]
      unfold notGoodProb
      have hΩne : ((oddRange (dnpPeriod s0 m)).card : ℝ) ≠ 0 := by rw [← hΩdef]; exact hΩpos.ne'
      rw [hΩdef]
      field_simp
    rw [hsum] at hm
    rw [le_div_iff₀ h1γ]
    have : (1 - γ) * K.card * ((Ω.filter fun ξ : ℕ => (goodCount s0 m a dir ξ : ℝ) < γ * (K.card : ℝ)).card : ℝ) ≤
        Ω.card * betaAvg s0 m a * K.card := by linarith
    nlinarith
  rw [div_le_iff₀ hΩpos]
  calc ((Ω.filter fun ξ : ℕ => ∃ a ∈ Icc (1 : ℕ) a0, ∃ dir : Bool,
      (goodCount s0 m a dir ξ : ℝ) < γ * (K.card : ℝ)).card : ℝ)
      ≤ ∑ a ∈ Icc 1 a0, ∑ dir : Bool,
        ((Ω.filter fun ξ : ℕ => (goodCount s0 m a dir ξ : ℝ) < γ * (K.card : ℝ)).card : ℝ) := hcard'
    _ ≤ ∑ a ∈ Icc 1 a0, ∑ _dir : Bool, Ω.card * betaAvg s0 m a / (1 - γ) :=
        Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun dir _ => hterm a ha dir
    _ = 2 / (1 - γ) * (∑ a ∈ Icc 1 a0, betaAvg s0 m a) * Ω.card := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul]
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ => ?_
        push_cast
        field_simp


theorem eight_mul_le_two_pow {L : ℕ} (hL : 8 ≤ L) : 8 * L ≤ 2 ^ L := by
  induction L, hL using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have : 2 ^ 8 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    rw [pow_succ]; omega

/-- `4(⌊log₂ n⌋ + C) ≤ n` for all large `n`. -/
theorem eventually_four_mul_log_add_le (C : ℕ) :
    ∀ᶠ n in Filter.atTop, 4 * (Nat.log 2 n + C) ≤ n := by
  rw [Filter.eventually_atTop]
  refine ⟨4 * (8 + C + C), fun n hn => ?_⟩
  rcases le_or_gt (8 + C) (Nat.log 2 n) with hL | hL
  · have h1 := eight_mul_le_two_pow (by omega : 8 ≤ Nat.log 2 n)
    have h2 : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
    omega
  · omega

/-- **Proposition 7.5(c)**: if Conjecture S holds for `a = 1, …, a₀`, then for some `m₀` and all
`m ≥ m₀` the size condition `(∗)` holds and, for every `s₀ > m`, with probability at least `1/2`
over odd shifts, `Γ_{a,±}(ξ) ≥ γ|𝒦|` for every `1 ≤ a ≤ a₀` and both signs. -/
theorem good_shift_prob (a0 : ℕ) {γ : ℝ} (hγ1 : γ < 1) (hS : ∀ a ∈ Icc 1 a0, ConjectureS a) :
    ∃ m0, ∀ m ≥ m0, 4 * (jZero m + a0) ≤ m + 1 ∧ ∀ s0 > m,
      1 / 2 ≤ (((oddRange (dnpPeriod s0 m)).filter fun ξ : ℕ => ∀ a ∈ Icc (1 : ℕ) a0, ∀ dir : Bool,
        γ * ((coarseZone m).card : ℝ) ≤ goodCount s0 m a dir ξ).card : ℝ) /
        (oddRange (dnpPeriod s0 m)).card := by
  have h1γ : 0 < 1 - γ := by linarith
  -- a power of `1/2` below `(1 - γ) / (8 (a₀ + 1))`
  obtain ⟨D, hD⟩ := exists_pow_lt_of_lt_one (show 0 < (1 - γ) / (8 * (a0 + 1)) by positivity)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  have hDa0 : (a0 : ℝ) * (1 / 2) ^ D ≤ (1 - γ) / 8 := by
    rw [lt_div_iff₀ (by positivity)] at hD
    have : (a0 : ℝ) * (1 / 2) ^ D ≤ (1 / 2) ^ D * (8 * (a0 + 1)) / 8 := by
      have : (0 : ℝ) ≤ (1 / 2) ^ D := by positivity
      nlinarith
    linarith
  -- the variances
  have hV : Filter.Tendsto (fun m => ∑ a ∈ Icc 1 a0, meanRelVariance m a) Filter.atTop (nhds 0) := by
    have := tendsto_finsetSum (Icc 1 a0) fun a ha => hS a ha
    simpa using this
  have hVev : ∀ᶠ m in Filter.atTop, 4 * ∑ a ∈ Icc 1 a0, meanRelVariance m a ≤ (1 - γ) / 8 := by
    have := hV.eventually (gt_mem_nhds (show (0 : ℝ) < (1 - γ) / 32 by positivity))
    filter_upwards [this] with m hm
    linarith
  have hLog : ∀ᶠ m in Filter.atTop, 4 * (jZero m + a0 + 2 + D) ≤ m + 1 := by
    have := (Filter.tendsto_add_atTop_nat 1).eventually
      (eventually_four_mul_log_add_le (1 + a0 + 2 + D))
    filter_upwards [this] with m hm
    unfold jZero; omega
  obtain ⟨m0, hm0⟩ := Filter.eventually_atTop.mp (hVev.and hLog)
  refine ⟨m0, fun m hm => ⟨by have := (hm0 m hm).2; omega, fun s0 hs0 => ?_⟩⟩
  obtain ⟨hVm, hLm⟩ := hm0 m hm
  have hsize : 4 * (jZero m + a0) ≤ m + 1 := by omega
  -- each `β_a ≤ 4 V̄^{(a)}_m + 2^{-D}`
  have hbeta : ∀ a ∈ Icc 1 a0, betaAvg s0 m a ≤ 4 * meanRelVariance m a + (1 / 2) ^ D := by
    intro a ha
    rw [mem_Icc] at ha
    rcases Nat.eq_zero_or_pos (coarseZone m).card with hK | hK
    · unfold betaAvg meanRelVariance
      rw [hK]; simp
    have hKpos : (0 : ℝ) < (coarseZone m).card := by exact_mod_cast hK
    unfold betaAvg meanRelVariance
    have hterm : ∀ k ∈ coarseZone m, notGoodProb s0 m a k true ≤
        4 * relVarianceA m a k + (1 / 2) ^ D := by
      intro k hk
      obtain ⟨hθ, -, hle⟩ := notGoodProb_le ha.1 ha.2 hs0 hsize hk
      have hVk : 0 ≤ relVarianceA m a k := relVariance_nonneg _ _ _
      have h1 : relVarianceA m a k / (relVarianceA m a k + (1 - shiftTheta m a k) ^ 2) ≤
          4 * relVarianceA m a k := by
        have hc : 1 / 4 ≤ (1 - shiftTheta m a k) ^ 2 := by nlinarith
        rw [div_le_iff₀ (by nlinarith)]
        nlinarith
      have h2 : (2 : ℝ) ^ (cancellerBelow m a k + 2) / 2 ^ s0 ≤ (1 / 2) ^ D := by
        obtain ⟨-, -, -, -, -, -, -, hκle⟩ := coarse_canceller_props ha.1 ha.2 hs0 hsize hk
        have hk' : k ≤ (m + 1) / 4 := (mem_Icc.mp hk).2
        have hexp : cancellerBelow m a k + 2 + D ≤ s0 := by omega
        rw [one_div_pow, div_le_div_iff₀ (by positivity) (by positivity), one_mul, ← pow_add]
        exact pow_le_pow_right₀ (by norm_num) hexp
      linarith
    calc ((coarseZone m).card : ℝ)⁻¹ * ∑ k ∈ coarseZone m, notGoodProb s0 m a k true
        ≤ ((coarseZone m).card : ℝ)⁻¹ * ∑ k ∈ coarseZone m, (4 * relVarianceA m a k + (1 / 2) ^ D) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (by positivity)
      _ = ((coarseZone m).card : ℝ)⁻¹ * ∑ k ∈ coarseZone m, 4 * relVarianceA m a k + (1 / 2) ^ D := by
          rw [Finset.sum_add_distrib, mul_add, Finset.sum_const, nsmul_eq_mul, ← mul_assoc,
            inv_mul_cancel₀ hKpos.ne', one_mul]
      _ = 4 * (((coarseZone m).card : ℝ)⁻¹ * ∑ k ∈ coarseZone m, relVarianceA m a k) +
            (1 / 2) ^ D := by rw [← Finset.mul_sum]; ring
  have hsumβ : ∑ a ∈ Icc 1 a0, betaAvg s0 m a ≤ (1 - γ) / 4 := by
    calc ∑ a ∈ Icc 1 a0, betaAvg s0 m a
        ≤ ∑ a ∈ Icc 1 a0, (4 * meanRelVariance m a + (1 / 2) ^ D) := Finset.sum_le_sum hbeta
      _ = 4 * ∑ a ∈ Icc 1 a0, meanRelVariance m a + a0 * (1 / 2) ^ D := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
          simp
      _ ≤ (1 - γ) / 4 := by linarith
  have hbad := prob_some_bad_le s0 m a0 hγ1
  have hbad' : (((oddRange (dnpPeriod s0 m)).filter fun ξ : ℕ => ∃ a ∈ Icc (1 : ℕ) a0, ∃ dir : Bool,
      (goodCount s0 m a dir ξ : ℝ) < γ * ((coarseZone m).card : ℝ)).card : ℝ) /
      (oddRange (dnpPeriod s0 m)).card ≤ 1 / 2 := by
    calc _ ≤ 2 / (1 - γ) * ∑ a ∈ Icc 1 a0, betaAvg s0 m a := hbad
      _ ≤ 2 / (1 - γ) * ((1 - γ) / 4) := by gcongr
      _ = 1 / 2 := by field_simp; ring
  have hΩpos : (0 : ℝ) < (oddRange (dnpPeriod s0 m)).card := by
    obtain ⟨M', hM'⟩ : ∃ M', dnpPeriod s0 m = 2 * M' := ⟨dnpPeriod s0 m / 2, by
      have := dnpPeriod_even s0 m; omega⟩
    have hpos : 0 < dnpPeriod s0 m := by
      unfold dnpPeriod; exact Nat.mul_pos (by norm_num) (strokeLen_pos _ _ _)
    rw [hM', card_oddRange_two_mul]; exact_mod_cast (by omega : 0 < M')
  have hsplit := Finset.card_filter_add_card_filter_not (s := oddRange (dnpPeriod s0 m))
    (fun ξ : ℕ => ∀ a ∈ Icc (1 : ℕ) a0, ∀ dir : Bool,
      γ * ((coarseZone m).card : ℝ) ≤ goodCount s0 m a dir ξ)
  have hneg : ((oddRange (dnpPeriod s0 m)).filter fun ξ : ℕ => ¬ ∀ a ∈ Icc (1 : ℕ) a0, ∀ dir : Bool,
      γ * ((coarseZone m).card : ℝ) ≤ goodCount s0 m a dir ξ) =
      (oddRange (dnpPeriod s0 m)).filter fun ξ : ℕ => ∃ a ∈ Icc (1 : ℕ) a0, ∃ dir : Bool,
        (goodCount s0 m a dir ξ : ℝ) < γ * ((coarseZone m).card : ℝ) :=
    Finset.filter_congr fun ξ _ => by push Not; rfl
  rw [hneg] at hsplit
  have hsplitR : (((oddRange (dnpPeriod s0 m)).filter fun ξ : ℕ => ∀ a ∈ Icc (1 : ℕ) a0,
      ∀ dir : Bool, γ * ((coarseZone m).card : ℝ) ≤ goodCount s0 m a dir ξ).card : ℝ) +
      (((oddRange (dnpPeriod s0 m)).filter fun ξ : ℕ => ∃ a ∈ Icc (1 : ℕ) a0, ∃ dir : Bool,
        (goodCount s0 m a dir ξ : ℝ) < γ * ((coarseZone m).card : ℝ)).card : ℝ) =
      (oddRange (dnpPeriod s0 m)).card := by exact_mod_cast hsplit
  rw [div_le_iff₀ hΩpos] at hbad'
  rw [le_div_iff₀ hΩpos]
  linarith

end MergeDepth
