import Transpose.Tape.DefsM
import Mathlib

/-!
# Theorem M*, analysis: local extremum values and the easy half of Banach's indicatrix

* `countable_localExtr_values`: the values of any `P : ℝ → ℝ` at local extrema form a countable set
  (each is the minimum or maximum of `P` over an interval with rational endpoints).
* the easy half of Banach's indicatrix: for `P` that is `K`-Lipschitz on `[0, c₀]`, the dyadic
  counting functions `N_m(p) = Σ_j 1[p ∈ J_{m,j}]` (with `J_{m,j}` an interval of length
  `K c₀ / 2^m` around the value of `P` at the centre of the `j`-th dyadic subinterval) are
  measurable with integral `K c₀`, and `#Λ(p) ≤ liminf_m N_m(p)` at every `p`. Fatou gives the
  measurable majorant.
-/

namespace Transpose.Tape.Impl

open Transpose MeasureTheory Filter Topology

open scoped ENNReal

/-! ### Positive lower bounds over finite sets -/

theorem exists_pos_le_finset {ι : Type*} (s : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ s, 0 < f i) :
    ∃ δ > 0, ∀ i ∈ s, δ ≤ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert a s ha ih =>
    obtain ⟨δ, hδ, hδs⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    refine ⟨min δ (f a), lt_min hδ (hf a (Finset.mem_insert_self _ _)), ?_⟩
    intro i hi
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact min_le_right _ _
    · exact le_trans (min_le_left _ _) (hδs i hi)

/-! ### Countability of extremal values -/

theorem countable_localExtr_values (P : ℝ → ℝ) :
    {p | ∃ s, P s = p ∧ (IsLocalMin P s ∨ IsLocalMax P s)}.Countable := by
  let f : ℚ × ℚ → ℝ := fun q => sInf (P '' Set.Icc (q.1 : ℝ) q.2)
  let g : ℚ × ℚ → ℝ := fun q => sSup (P '' Set.Icc (q.1 : ℝ) q.2)
  apply ((Set.countable_range f).union (Set.countable_range g)).mono
  rintro p ⟨s, rfl, hext⟩
  -- a rational interval around `s` on which an eventual property holds
  have key : ∀ {q : ℝ → Prop}, (∀ᶠ y in 𝓝 s, q y) →
      ∃ a b : ℚ, s ∈ Set.Icc (a : ℝ) b ∧ ∀ y ∈ Set.Icc (a : ℝ) b, q y := by
    intro q hq
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hq
    obtain ⟨a, ha⟩ := exists_rat_btwn (show s - ε < s by linarith)
    obtain ⟨b, hb⟩ := exists_rat_btwn (show s < s + ε by linarith)
    refine ⟨a, b, ⟨ha.2.le, hb.1.le⟩, fun y hy => hball ?_⟩
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hy.1, hy.2, ha.1, hb.2]
  rcases hext with hmin | hmax
  · obtain ⟨a, b, hs, hab⟩ := key hmin
    refine Or.inl ⟨(a, b), IsLeast.csInf_eq ⟨⟨s, hs, rfl⟩, ?_⟩⟩
    rintro _ ⟨y, hy, rfl⟩; exact hab y hy
  · obtain ⟨a, b, hs, hab⟩ := key hmax
    refine Or.inr ⟨(a, b), IsGreatest.csSup_eq ⟨⟨s, hs, rfl⟩, ?_⟩⟩
    rintro _ ⟨y, hy, rfl⟩; exact hab y hy

/-! ### The easy half of Banach's indicatrix: dyadic counting functions -/

section Dyadic

variable (K : NNReal) (P : ℝ → ℝ) (c₀ : ℝ)

/-- The length `c₀ / 2^m` of the dyadic subintervals of `[0, c₀]` at level `m`. -/
noncomputable def dyLen (m : ℕ) : ℝ := c₀ / 2 ^ m

/-- The centre of the `j`-th dyadic subinterval at level `m`. -/
noncomputable def dyCtr (m j : ℕ) : ℝ := (j + 1 / 2) * dyLen c₀ m

/-- The interval of values around `P` at the centre of the `j`-th subinterval. -/
noncomputable def dyBox (m j : ℕ) : Set ℝ :=
  Set.Icc (P (dyCtr c₀ m j) - K * dyLen c₀ m / 2) (P (dyCtr c₀ m j) + K * dyLen c₀ m / 2)

/-- The dyadic counting function `N_m`. -/
noncomputable def dyCount (m : ℕ) (p : ℝ) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range (2 ^ m), (dyBox K P c₀ m j).indicator (fun _ => (1 : ℝ≥0∞)) p

theorem measurableSet_dyBox (m j : ℕ) : MeasurableSet (dyBox K P c₀ m j) := measurableSet_Icc

theorem measurable_dyCount (m : ℕ) : Measurable (dyCount K P c₀ m) := by
  unfold dyCount
  refine Finset.measurable_sum _ (fun j _ => ?_)
  exact (measurable_const.indicator (measurableSet_dyBox K P c₀ m j))

theorem lintegral_dyCount (m : ℕ) :
    ∫⁻ p, dyCount K P c₀ m p = K * ENNReal.ofReal c₀ := by
  unfold dyCount
  rw [lintegral_finsetSum _
    (fun j _ => measurable_const.indicator (measurableSet_dyBox K P c₀ m j))]
  have h1 : ∀ j ∈ Finset.range (2 ^ m),
      ∫⁻ p, (dyBox K P c₀ m j).indicator (fun _ => (1 : ℝ≥0∞)) p =
        ENNReal.ofReal (K * dyLen c₀ m) := by
    intro j _
    rw [lintegral_indicator_const (measurableSet_dyBox K P c₀ m j), one_mul, dyBox,
      Real.volume_Icc]
    congr 1; ring
  rw [Finset.sum_congr rfl h1, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hpow : (0 : ℝ) < 2 ^ m := by positivity
  rw [dyLen, show ((2 ^ m : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((2 : ℝ) ^ m) by
    rw [ENNReal.ofReal_pow (by norm_num)]; simp]
  rw [← ENNReal.ofReal_mul (by positivity)]
  rw [show (2 : ℝ) ^ m * (K * (c₀ / 2 ^ m)) = K * c₀ by field_simp]
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_coe_nnreal]

/-- At every level `m`, the count `N_m(p)` is at least the size of any finite subset of `Λ(p)`
whose points are more than `c₀ / 2^m` apart. -/
theorem card_le_dyCount (hP : LipschitzOnWith K P (Set.Icc 0 c₀)) (hc₀ : 0 ≤ c₀) {p : ℝ}
    {F : Finset ℝ} (hF : ∀ s ∈ F, s ∈ levelSet P c₀ p) {m : ℕ}
    (hsep : ∀ s ∈ F, ∀ s' ∈ F, s ≠ s' → dyLen c₀ m < |s - s'|) :
    (F.card : ℝ≥0∞) ≤ dyCount K P c₀ m p := by
  classical
  set h := dyLen c₀ m with hh
  have hpow : (0 : ℝ) < 2 ^ m := by positivity
  have hh0 : 0 ≤ h := div_nonneg hc₀ hpow.le
  have hhc : (2 : ℝ) ^ m * h = c₀ := by rw [hh, dyLen]; field_simp
  -- the dyadic index of a point
  let jf : ℝ → ℕ := fun s => min ⌊s / h⌋₊ (2 ^ m - 1)
  have hj_lt : ∀ s, jf s < 2 ^ m := fun s => by
    have : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    simp only [jf]; omega
  -- every point of `[0, c₀]` is within `h/2` of the centre of its subinterval
  have hctr : ∀ s ∈ Set.Icc 0 c₀, |s - dyCtr c₀ m (jf s)| ≤ h / 2 := by
    intro s hs
    rcases eq_or_lt_of_le hh0 with h0 | hpos
    · -- `h = 0`: then `c₀ = 0` and `s = 0`
      have hc : c₀ = 0 := by rw [← hhc, ← h0, mul_zero]
      have hs0 : s = 0 := le_antisymm (hc ▸ hs.2) hs.1
      simp [dyCtr, ← hh, ← h0, hs0]
    · have hjs : (jf s : ℝ) * h ≤ s ∧ s ≤ ((jf s : ℝ) + 1) * h := by
        by_cases hcase : ⌊s / h⌋₊ ≤ 2 ^ m - 1
        · have hj : jf s = ⌊s / h⌋₊ := by simp only [jf]; omega
          rw [hj]
          have h1 := Nat.floor_le (div_nonneg hs.1 hpos.le)
          have h2 := Nat.lt_floor_add_one (s / h)
          constructor
          · rw [← le_div_iff₀ hpos]; exact h1
          · rw [← div_le_iff₀ hpos]; exact le_of_lt h2
        · push Not at hcase
          have hj : jf s = 2 ^ m - 1 := by simp only [jf]; omega
          have h1 : (2 : ℝ) ^ m ≤ s / h := by
            have : (2 ^ m : ℕ) ≤ ⌊s / h⌋₊ := by
              have := Nat.one_le_two_pow (n := m); omega
            have := (Nat.le_floor_iff (div_nonneg hs.1 hpos.le)).1 this
            exact_mod_cast this
          have hsc : s = c₀ := by
            apply le_antisymm hs.2
            rw [← hhc]; rwa [le_div_iff₀ hpos] at h1
          have hcast : ((2 ^ m - 1 : ℕ) : ℝ) = (2 : ℝ) ^ m - 1 := by
            rw [Nat.cast_sub Nat.one_le_two_pow]; simp
          rw [hj, hcast, hsc, ← hhc]
          constructor <;> nlinarith
      rw [dyCtr, ← hh, abs_le]
      constructor <;> nlinarith [hjs.1, hjs.2]
  -- the centres lie in `[0, c₀]`
  have hctr_mem : ∀ j, j < 2 ^ m → dyCtr c₀ m j ∈ Set.Icc 0 c₀ := by
    intro j hj
    rw [dyCtr, ← hh]
    have hj' : (j : ℝ) + 1 ≤ 2 ^ m := by exact_mod_cast hj
    constructor
    · positivity
    · rw [← hhc]; nlinarith
  -- the index map is injective on `F`
  have hinj : Set.InjOn jf F := by
    intro s hs s' hs' hjj
    by_contra hne
    have h1 := hctr s (hF s hs).1
    have h2 := hctr s' (hF s' hs').1
    rw [hjj] at h1
    have := hsep s hs s' hs' hne
    have : |s - s'| ≤ h := by
      calc |s - s'| = |(s - dyCtr c₀ m (jf s')) - (s' - dyCtr c₀ m (jf s'))| := by ring_nf
        _ ≤ |s - dyCtr c₀ m (jf s')| + |s' - dyCtr c₀ m (jf s')| := abs_sub _ _
        _ ≤ h / 2 + h / 2 := add_le_add h1 h2
        _ = h := by ring
    linarith
  -- each index of `F` contributes `1`
  have hone : ∀ j ∈ F.image jf, (dyBox K P c₀ m j).indicator (fun _ => (1 : ℝ≥0∞)) p = 1 := by
    intro j hj
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hj
    apply Set.indicator_of_mem
    have hsΛ := hF s hs
    have hd := hP.dist_le_mul s hsΛ.1 _ (hctr_mem _ (hj_lt s))
    rw [Real.dist_eq, Real.dist_eq] at hd
    have hc := hctr s hsΛ.1
    rw [hsΛ.2] at hd
    have : |p - P (dyCtr c₀ m (jf s))| ≤ K * h / 2 := by
      calc |p - P (dyCtr c₀ m (jf s))| ≤ K * |s - dyCtr c₀ m (jf s)| := hd
        _ ≤ K * (h / 2) := mul_le_mul_of_nonneg_left hc K.2
        _ = K * h / 2 := by ring
    rw [dyBox, ← hh, Set.mem_Icc]
    constructor <;> linarith [(abs_le.1 this).1, (abs_le.1 this).2]
  calc (F.card : ℝ≥0∞) = ((F.image jf).card : ℝ≥0∞) := by
        rw [Finset.card_image_of_injOn hinj]
    _ = ∑ j ∈ F.image jf, (dyBox K P c₀ m j).indicator (fun _ => (1 : ℝ≥0∞)) p := by
        rw [Finset.sum_congr rfl hone]; simp
    _ ≤ dyCount K P c₀ m p := by
        unfold dyCount
        apply Finset.sum_le_sum_of_subset
        intro j hj
        obtain ⟨s, _, rfl⟩ := Finset.mem_image.1 hj
        exact Finset.mem_range.2 (hj_lt s)

/-- `#Λ(p) ≤ liminf_m N_m(p)` at every level `p`. -/
theorem encard_le_liminf_dyCount (hP : LipschitzOnWith K P (Set.Icc 0 c₀)) (hc₀ : 0 ≤ c₀)
    (p : ℝ) :
    ((levelSet P c₀ p).encard : ℝ≥0∞) ≤ liminf (fun m => dyCount K P c₀ m p) atTop := by
  classical
  -- every finite size below `#Λ(p)` is eventually below `N_m(p)`
  have key : ∀ k : ℕ, (k : ℕ∞) ≤ (levelSet P c₀ p).encard →
      (k : ℝ≥0∞) ≤ liminf (fun m => dyCount K P c₀ m p) atTop := by
    intro k hk
    obtain ⟨F, hFsub, hFcard⟩ := Set.exists_subset_encard_eq hk
    have hFfin : F.Finite := Set.finite_of_encard_eq_coe hFcard
    set G := hFfin.toFinset with hG
    have hGcard : G.card = k := by
      have := hFfin.encard_eq_coe_toFinset_card
      rw [hFcard] at this
      exact_mod_cast this.symm
    -- a positive separation of the points of `G`
    obtain ⟨δ, hδ, hδG⟩ := exists_pos_le_finset ((G ×ˢ G).filter (fun q => q.1 ≠ q.2))
      (fun q => |q.1 - q.2|) (fun q hq => by
        rw [Finset.mem_filter] at hq
        exact abs_pos.2 (sub_ne_zero.2 hq.2))
    -- eventually `c₀ / 2^m < δ`
    obtain ⟨m₀, hm₀⟩ := pow_unbounded_of_one_lt (c₀ / δ) (by norm_num : (1 : ℝ) < 2)
    have hev : ∀ᶠ m in atTop, (k : ℝ≥0∞) ≤ dyCount K P c₀ m p := by
      filter_upwards [eventually_ge_atTop m₀] with m hm
      rw [← hGcard]
      apply card_le_dyCount K P c₀ hP hc₀
      · intro s hs; exact hFsub ((Set.Finite.mem_toFinset hFfin).1 hs)
      · intro s hs s' hs' hne
        have h1 := hδG (s, s') (Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hs, hs'⟩, hne⟩)
        have h2 : (2 : ℝ) ^ m₀ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hm
        have h3 : c₀ / δ < 2 ^ m := lt_of_lt_of_le hm₀ h2
        have hpow : (0 : ℝ) < 2 ^ m := by positivity
        have : c₀ / 2 ^ m < δ := by
          rw [div_lt_iff₀ hpow]; rw [div_lt_iff₀ hδ] at h3; linarith
        simp only at h1
        rw [dyLen]; linarith
    exact le_liminf_of_le (by isBoundedDefault) hev
  -- conclude
  induction h : (levelSet P c₀ p).encard using ENat.recTopCoe with
  | top =>
    simp only [ENat.toENNReal_top, top_le_iff]
    apply ENNReal.eq_top_of_forall_nnreal_le
    intro r
    calc (r : ℝ≥0∞) ≤ (⌈(r : ℝ)⌉₊ : ℝ≥0∞) := by
          rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_natCast]
          exact ENNReal.ofReal_le_ofReal (Nat.le_ceil _)
      _ ≤ _ := key _ (by rw [h]; exact le_top)
  | coe k₀ =>
    simp only [ENat.toENNReal_coe]
    exact key k₀ (by rw [h])

/-- The measurable majorant `liminf_m N_m`. -/
theorem majorant_spec (hP : LipschitzOnWith K P (Set.Icc 0 c₀)) (hc₀ : 0 ≤ c₀) :
    Measurable (fun p => liminf (fun m => dyCount K P c₀ m p) atTop) ∧
      (∀ p, ((levelSet P c₀ p).encard : ℝ≥0∞) ≤ liminf (fun m => dyCount K P c₀ m p) atTop) ∧
      ∫⁻ p, liminf (fun m => dyCount K P c₀ m p) atTop ≤ K * ENNReal.ofReal c₀ := by
  refine ⟨Measurable.liminf (fun m => measurable_dyCount K P c₀ m),
    encard_le_liminf_dyCount K P c₀ hP hc₀, ?_⟩
  calc ∫⁻ p, liminf (fun m => dyCount K P c₀ m p) atTop
      ≤ liminf (fun m => ∫⁻ p, dyCount K P c₀ m p) atTop :=
        lintegral_liminf_le (fun m => measurable_dyCount K P c₀ m)
    _ = K * ENNReal.ofReal c₀ := by
        simp only [lintegral_dyCount K P c₀, liminf_const]

end Dyadic

theorem levelSet_eq_empty {P : ℝ → ℝ} {c₀ : ℝ} (hc₀ : c₀ < 0) (p : ℝ) :
    levelSet P c₀ p = ∅ := by
  ext s
  simp only [levelSet, Set.mem_ofPred_eq, Set.mem_Icc, Set.mem_empty_iff_false, iff_false]
  intro h; linarith [h.1.1, h.1.2]

theorem levelSet_encard_majorant {K : NNReal} {P : ℝ → ℝ} {c₀ : ℝ}
    (hP : LipschitzOnWith K P (Set.Icc 0 c₀)) :
    ∃ F : ℝ → ℝ≥0∞, Measurable F ∧ (∀ p, ((levelSet P c₀ p).encard : ℝ≥0∞) ≤ F p) ∧
      ∫⁻ p, F p ≤ K * ENNReal.ofReal c₀ := by
  rcases lt_or_ge c₀ 0 with hc₀ | hc₀
  · refine ⟨fun _ => 0, measurable_const, fun p => ?_, by simp⟩
    rw [levelSet_eq_empty hc₀ p]; simp
  · exact ⟨_, majorant_spec K P c₀ hP hc₀⟩

theorem lintegral_encard_levelSet_le {K : NNReal} {P : ℝ → ℝ} {c₀ : ℝ}
    (hP : LipschitzOnWith K P (Set.Icc 0 c₀)) :
    ∫⁻ p, ((levelSet P c₀ p).encard : ℝ≥0∞) ≤ K * ENNReal.ofReal c₀ := by
  obtain ⟨F, -, hle, hint⟩ := levelSet_encard_majorant hP
  exact le_trans (lintegral_mono hle) hint

theorem ae_finite_levelSet {K : NNReal} {P : ℝ → ℝ} {c₀ : ℝ}
    (hP : LipschitzOnWith K P (Set.Icc 0 c₀)) :
    ∀ᵐ p, (levelSet P c₀ p).Finite := by
  obtain ⟨F, hF, hle, hint⟩ := levelSet_encard_majorant hP
  have hfin : ∫⁻ p, F p ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top) hint
  filter_upwards [ae_lt_top hF hfin] with p hp
  have h1 := lt_of_le_of_lt (hle p) hp
  rw [← Set.encard_lt_top_iff]
  by_contra hc
  rw [not_lt, top_le_iff] at hc
  rw [hc] at h1
  simp at h1

end Transpose.Tape.Impl
