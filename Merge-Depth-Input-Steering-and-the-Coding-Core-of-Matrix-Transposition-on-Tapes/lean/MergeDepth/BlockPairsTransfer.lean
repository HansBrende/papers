import MergeDepth.BlockPairsProfile

/-!
# Block pairs: from straddle counts to the profile at a random odd shift (Lemma 7.4(c))

For `ξ` uniform over the odd residues modulo `P`, the probability that `X^±_{k,κ}(ξ) < τ M_k`
differs from the Lebesgue probability that `x_k(t) < τ` for `t` uniform on `[0, N)` by at most
`2^{κ+2-s₀}` (`prob_straddle_vs_profile`).

* `IsAffineOn`, `IsAffineOn.ordConnected_sublevel`: functions agreeing with an affine map on an
  interval have order-connected sublevel sets there.
* `card_lattice_ordConnected`: an order-connected set `J` contains its length over the spacing, up
  to one, of the points of an arithmetic progression.
* `profile_isAffineOn_grid`: `x_k` is affine on every cell of the grid `2^{-(κ+1)} ℤ` (the tents
  have their corners there); `continuous_profile`; `profile_add_period`: `x_k` is `N`-periodic.
* `count_profile_vs_volume`: the number of odd `ξ < P` with `x_k((ξ + 1/2)/Λ) < τ` is within
  `N 2^{κ+3}` (one per grid cell) of `Λ/2` times the volume of the sublevel set on `[0, 4N)`;
  `volume_sublevel_four`: that volume is four times the volume on `[0, N)`.
* `prob_straddle_vs_profile`: **Lemma 7.4(c)**, for both directions.
-/

namespace MergeDepth

open Finset DirectedReciprocity MeasureTheory

/-- `f` agrees with an affine function on `[a, b]`. -/
def IsAffineOn (f : ℝ → ℝ) (a b : ℝ) : Prop := ∃ α β : ℝ, ∀ t ∈ Set.Icc a b, f t = α * t + β

theorem IsAffineOn.add {f g : ℝ → ℝ} {a b : ℝ} (hf : IsAffineOn f a b) (hg : IsAffineOn g a b) :
    IsAffineOn (fun t => f t + g t) a b := by
  obtain ⟨α, β, h⟩ := hf; obtain ⟨α', β', h'⟩ := hg
  exact ⟨α + α', β + β', fun t ht => by dsimp only; rw [h t ht, h' t ht]; ring⟩

theorem IsAffineOn.const_mul {f : ℝ → ℝ} {a b : ℝ} (hf : IsAffineOn f a b) (c : ℝ) :
    IsAffineOn (fun t => c * f t) a b := by
  obtain ⟨α, β, h⟩ := hf
  exact ⟨c * α, c * β, fun t ht => by dsimp only; rw [h t ht]; ring⟩

theorem IsAffineOn.sum {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℝ} {a b : ℝ}
    (hf : ∀ i ∈ s, IsAffineOn (f i) a b) : IsAffineOn (fun t => ∑ i ∈ s, f i t) a b := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, 0, fun t _ => by simp⟩
  | insert i s hi ih =>
    have h1 := hf i (mem_insert_self _ _)
    have h2 := ih fun j hj => hf j (mem_insert_of_mem hj)
    simpa [Finset.sum_insert hi] using h1.add h2

theorem IsAffineOn.congr {f g : ℝ → ℝ} {a b : ℝ} (hf : IsAffineOn f a b)
    (h : ∀ t ∈ Set.Icc a b, g t = f t) : IsAffineOn g a b := by
  obtain ⟨α, β, hf⟩ := hf
  exact ⟨α, β, fun t ht => by rw [h t ht, hf t ht]⟩

theorem IsAffineOn.comp_add {f : ℝ → ℝ} {a b c : ℝ} (hf : IsAffineOn f (a + c) (b + c)) :
    IsAffineOn (fun t => f (t + c)) a b := by
  obtain ⟨α, β, h⟩ := hf
  refine ⟨α, α * c + β, fun t ht => ?_⟩
  dsimp only
  rw [h (t + c) ⟨by linarith [ht.1], by linarith [ht.2]⟩]; ring

/-- The sublevel set of an affine function on a half-open interval is order-connected. -/
theorem IsAffineOn.ordConnected_sublevel {f : ℝ → ℝ} {a b : ℝ} (hf : IsAffineOn f a b) (τ : ℝ) :
    ({t ∈ Set.Ico a b | f t < τ} : Set ℝ).OrdConnected := by
  obtain ⟨α, β, h⟩ := hf
  refine ⟨fun x hx y hy z hz => ?_⟩
  obtain ⟨⟨hx1, hx2⟩, hfx⟩ := hx
  obtain ⟨⟨hy1, hy2⟩, hfy⟩ := hy
  have hz1 : a ≤ z := le_trans hx1 hz.1
  have hz2 : z < b := lt_of_le_of_lt hz.2 hy2
  refine ⟨⟨hz1, hz2⟩, ?_⟩
  rw [h x ⟨hx1, hx2.le⟩] at hfx
  rw [h y ⟨hy1, hy2.le⟩] at hfy
  rw [h z ⟨hz1, hz2.le⟩]
  rcases le_or_gt 0 α with hα | hα
  · nlinarith [hz.2]
  · nlinarith [hz.1]

/-- The tent of width `2 p h` is affine on every cell `[j h, (j + 1) h]` of the grid `h ℤ`. -/
theorem tent_isAffineOn_cell {h : ℝ} (hh : 0 < h) (p : ℕ) (j : ℤ) :
    IsAffineOn (fun y => max 0 (2 * p * h - 2 * |y|)) (j * h) ((j + 1) * h) := by
  rcases le_or_gt 0 j with hj | hj
  · have hj' : (0 : ℝ) ≤ j := by exact_mod_cast hj
    rcases le_or_gt (j + 1) (p : ℤ) with hjp | hjp
    · have hjp' : (j : ℝ) + 1 ≤ p := by exact_mod_cast hjp
      refine ⟨-2, 2 * p * h, fun y hy => ?_⟩
      have hy0 : 0 ≤ y := le_trans (by positivity) hy.1
      dsimp only
      rw [abs_of_nonneg hy0, max_eq_right (by nlinarith [hy.2])]; ring
    · have hjp' : (p : ℝ) ≤ j := by
        have : (p : ℤ) ≤ j := by omega
        exact_mod_cast this
      refine ⟨0, 0, fun y hy => ?_⟩
      have hy0 : 0 ≤ y := le_trans (by positivity) hy.1
      dsimp only
      rw [abs_of_nonneg hy0, max_eq_left (by nlinarith [hy.1])]; ring
  · have hj' : (j : ℝ) + 1 ≤ 0 := by
      have : j + 1 ≤ 0 := by omega
      exact_mod_cast this
    rcases le_or_gt (-(p : ℤ)) j with hjp | hjp
    · have hjp' : -(p : ℝ) ≤ j := by exact_mod_cast hjp
      refine ⟨2, 2 * p * h, fun y hy => ?_⟩
      have hy0 : y ≤ 0 := le_trans hy.2 (by nlinarith)
      dsimp only
      rw [abs_of_nonpos hy0, max_eq_right (by nlinarith [hy.1])]; ring
    · have hjp' : (j : ℝ) + 1 ≤ -(p : ℝ) := by
        have : j + 1 ≤ -(p : ℤ) := by omega
        exact_mod_cast this
      refine ⟨0, 0, fun y hy => ?_⟩
      have hy0 : y ≤ 0 := le_trans hy.2 (by nlinarith)
      dsimp only
      rw [abs_of_nonpos hy0, max_eq_left (by nlinarith [hy.2])]; ring

/-- Lattice points in an order-connected set: within one of its length over the spacing. -/
theorem card_lattice_ordConnected {J : Set ℝ} [DecidablePred (· ∈ J)] (hJ : J.OrdConnected)
    {o s : ℝ} (hs : 0 < s) {M : ℕ} (hJsub : J ⊆ Set.Ioo (o - s) (o + M * s)) :
    |(((range M).filter fun n : ℕ => o + (n : ℝ) * s ∈ J).card : ℝ) - (volume J).toReal / s| ≤ 1 := by
  set L := (range M).filter fun n : ℕ => o + (n : ℝ) * s ∈ J with hL
  have hfin : volume J ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) (measure_mono hJsub)
  -- a lattice point of `J` has index in `L`
  have hmemL : ∀ n : ℤ, o + n * s ∈ J → 0 ≤ n ∧ n.toNat ∈ L := by
    intro n hn
    have h1 := (hJsub hn).1
    have h2 := (hJsub hn).2
    have hn0 : 0 ≤ n := by
      by_contra hc
      have : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ -1 by omega)
      nlinarith
    have hnM : n < M := by
      by_contra hc
      have : (M : ℝ) ≤ n := by exact_mod_cast (show (M : ℤ) ≤ n by omega)
      nlinarith
    refine ⟨hn0, ?_⟩
    rw [hL, mem_filter, mem_range]
    have hcast : ((n.toNat : ℕ) : ℝ) = (n : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hn0
    exact ⟨by omega, by rwa [hcast]⟩
  rcases L.eq_empty_or_nonempty with hLe | hLne
  · -- no lattice point: `J` lies in one gap
    rw [hLe, card_empty, Nat.cast_zero, zero_sub, abs_neg,
      abs_of_nonneg (div_nonneg ENNReal.toReal_nonneg hs.le)]
    rcases J.eq_empty_or_nonempty with hJe | ⟨t, ht⟩
    · simp [hJe]
    rw [div_le_one hs]
    set n : ℤ := ⌊(t - o) / s⌋
    have hn1 : (n : ℝ) * s ≤ t - o := by
      have := Int.floor_le ((t - o) / s); rwa [le_div_iff₀ hs] at this
    have hn2 : t - o < ((n : ℝ) + 1) * s := by
      have := Int.lt_floor_add_one ((t - o) / s); rwa [div_lt_iff₀ hs] at this
    have hsub : J ⊆ Set.Ioo (o + n * s) (o + (n + 1) * s) := by
      intro t' ht'
      by_contra hc
      rw [Set.mem_Ioo, not_and_or, not_lt, not_lt] at hc
      rcases hc with hc | hc
      · have := hJ.out ht' ht ⟨hc, by linarith⟩
        have := (hmemL n this).2; rw [hLe] at this; simp at this
      · have := hJ.out ht ht' ⟨by linarith, hc⟩
        have := (hmemL (n + 1) (by push_cast; exact this)).2; rw [hLe] at this; simp at this
    have := ENNReal.toReal_mono (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
      (measure_mono hsub)
    rw [Real.volume_Ioo, ENNReal.toReal_ofReal (by nlinarith)] at this
    linarith
  · set n0 := L.min' hLne
    set n1 := L.max' hLne
    have hn0L : n0 ∈ L := L.min'_mem hLne
    have hn1L : n1 ∈ L := L.max'_mem hLne
    have hn01 : n0 ≤ n1 := L.min'_le _ hn1L
    have hp0 : o + n0 * s ∈ J := (mem_filter.mp hn0L).2
    have hp1 : o + n1 * s ∈ J := (mem_filter.mp hn1L).2
    have hLeq : L = Icc n0 n1 := by
      ext n
      constructor
      · intro hn; exact mem_Icc.mpr ⟨L.min'_le _ hn, L.le_max' _ hn⟩
      · intro hn
        rw [mem_Icc] at hn
        have hnR0 : (n0 : ℝ) ≤ n := by exact_mod_cast hn.1
        have hnR1 : (n : ℝ) ≤ n1 := by exact_mod_cast hn.2
        have hJn : o + n * s ∈ J := hJ.out hp0 hp1 ⟨by nlinarith, by nlinarith⟩
        have := (hmemL n (by exact_mod_cast hJn)).2
        simpa using this
    have hcard : (L.card : ℝ) = n1 - n0 + 1 := by
      rw [hLeq, Nat.card_Icc, Nat.cast_sub (by omega : n0 ≤ n1 + 1)]; push_cast; ring
    have hlow : ((n1 : ℝ) - n0) * s ≤ (volume J).toReal := by
      have hsub : Set.Icc (o + n0 * s) (o + n1 * s) ⊆ J := hJ.out hp0 hp1
      have := ENNReal.toReal_mono hfin (measure_mono hsub)
      rw [Real.volume_Icc, ENNReal.toReal_ofReal (by
        have : (n0 : ℝ) ≤ n1 := by exact_mod_cast hn01
        nlinarith)] at this
      linarith
    have hhigh : (volume J).toReal ≤ ((n1 : ℝ) - n0 + 2) * s := by
      have hsub : J ⊆ Set.Ioo (o + ((n0 : ℝ) - 1) * s) (o + ((n1 : ℝ) + 1) * s) := by
        intro t' ht'
        by_contra hc
        rw [Set.mem_Ioo, not_and_or, not_lt, not_lt] at hc
        rcases hc with hc | hc
        · have hJ' := hJ.out ht' hp0 ⟨hc, by nlinarith⟩
          have := hmemL ((n0 : ℤ) - 1) (by push_cast; exact hJ')
          have hlt : ((n0 : ℤ) - 1).toNat < n0 := by omega
          have := L.min'_le _ this.2
          omega
        · have hJ' := hJ.out hp1 ht' ⟨by nlinarith, hc⟩
          have := hmemL ((n1 : ℤ) + 1) (by push_cast; exact hJ')
          have := L.le_max' _ this.2
          omega
      have := ENNReal.toReal_mono (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
        (measure_mono hsub)
      rw [Real.volume_Ioo, ENNReal.toReal_ofReal (by
        have : (n0 : ℝ) ≤ n1 := by exact_mod_cast hn01
        nlinarith)] at this
      linarith
    have h1 : (volume J).toReal / s ≤ n1 - n0 + 2 := by rw [div_le_iff₀ hs]; linarith
    have h2 : (n1 : ℝ) - n0 ≤ (volume J).toReal / s := by rw [le_div_iff₀ hs]; linarith
    rw [hcard, abs_le]
    constructor <;> linarith

theorem tent_isAffineOn_grid {h w : ℝ} (hh : 0 < h) {p : ℕ} (hw : w = 2 * p * h) (j : ℤ) :
    IsAffineOn (tent w) (j * h) ((j + 1) * h) := by
  have := tent_isAffineOn_cell hh p j
  refine this.congr fun y _ => ?_
  unfold tent; rw [hw]

/-- The periodic tent is affine on every grid cell, if `N`, `w/2` lie on the grid `h ℤ`. -/
theorem perTent_isAffineOn_grid {h N w : ℝ} (hh : 0 < h) {M p : ℕ} (hN : N = M * h)
    (hw : w = 2 * p * h) (hhN : 2 * h ≤ N) (hwN : w ≤ N) (j : ℤ) :
    IsAffineOn (perTent N w) (j * h) ((j + 1) * h) := by
  have hNpos : 0 < N := by linarith
  set L0 : ℤ := ⌊(j * h) / N⌋ with hL0
  have hL1 : (L0 : ℝ) * N ≤ j * h := by
    have := Int.floor_le ((j * h) / N); rwa [le_div_iff₀ hNpos] at this
  have hL2 : (j : ℝ) * h < ((L0 : ℝ) + 1) * N := by
    have := Int.lt_floor_add_one ((j * h) / N); rwa [div_lt_iff₀ hNpos] at this
  have hsum : ∀ y ∈ Set.Icc (j * h) ((j + 1) * h),
      perTent N w y = ∑ l ∈ ({L0, L0 + 1} : Finset ℤ), tent w (y - l * N) := by
    intro y hy
    unfold perTent
    refine tsum_eq_sum fun l hl => ?_
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hl
    apply tent_eq_zero
    rcases le_or_gt l (L0 - 1) with hl1 | hl1
    · have : (l : ℝ) ≤ L0 - 1 := by exact_mod_cast hl1
      have hpos : y - l * N ≥ N := by nlinarith [hy.1]
      rw [abs_of_pos (by linarith)]; linarith
    · have hl2 : L0 + 2 ≤ l := by omega
      have : (L0 : ℝ) + 2 ≤ l := by exact_mod_cast hl2
      have hneg : y - l * N ≤ -(N / 2) := by nlinarith [hy.2]
      rw [abs_of_neg (by linarith)]; linarith
  refine IsAffineOn.congr (IsAffineOn.sum _ fun l _ => ?_) hsum
  have hcell := tent_isAffineOn_grid hh hw (j - l * M)
  have : IsAffineOn (tent w) (j * h + -(l * N)) ((j + 1) * h + -(l * N)) := by
    rw [hN]; push_cast at hcell ⊢
    convert hcell using 1 <;> ring
  simpa [sub_eq_add_neg] using this.comp_add

/-- Points of the grid `h ℤ`. -/
def OnGrid (h x : ℝ) : Prop := ∃ n : ℤ, x = n * h

theorem OnGrid.add {h x y : ℝ} (hx : OnGrid h x) (hy : OnGrid h y) : OnGrid h (x + y) := by
  obtain ⟨a, rfl⟩ := hx; obtain ⟨b, rfl⟩ := hy; exact ⟨a + b, by push_cast; ring⟩

theorem OnGrid.sub {h x y : ℝ} (hx : OnGrid h x) (hy : OnGrid h y) : OnGrid h (x - y) := by
  obtain ⟨a, rfl⟩ := hx; obtain ⟨b, rfl⟩ := hy; exact ⟨a - b, by push_cast; ring⟩

theorem OnGrid.sum {ι : Type*} (s : Finset ι) {h : ℝ} {f : ι → ℝ} (hf : ∀ i ∈ s, OnGrid h (f i)) :
    OnGrid h (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hf i (mem_insert_self _ _)).add (ih fun j hj => hf j (mem_insert_of_mem hj))

theorem onGrid_inv_two_pow {e i : ℕ} (hi : i ≤ e) (c : ℕ) :
    OnGrid ((2 : ℝ)⁻¹ ^ e) (c * (2 : ℝ)⁻¹ ^ i) := by
  refine ⟨c * 2 ^ (e - i), ?_⟩
  push_cast
  have he : (2 : ℝ)⁻¹ ^ e = (2 : ℝ)⁻¹ ^ i * (2 : ℝ)⁻¹ ^ (e - i) := by
    rw [← pow_add, Nat.add_sub_cancel' hi]
  rw [he, inv_pow (2 : ℝ) (e - i)]
  field_simp

theorem piHat_eq (m i : ℕ) : piHat m i = ((m - i + 1 : ℕ) : ℝ) * (2 : ℝ)⁻¹ ^ i := by
  unfold piHat; rw [inv_pow, div_eq_mul_inv]

theorem apexHat_onGrid {m k e : ℕ} (hke : k ≤ e) {S : Finset ℕ} (hS : S ⊆ Icc 1 (k - 1)) :
    OnGrid ((2 : ℝ)⁻¹ ^ e) (apexHat m k S) := by
  unfold apexHat
  refine OnGrid.add (OnGrid.sum _ fun i hi => ?_) (OnGrid.sum _ fun i hi => ?_)
  · have := onGrid_inv_two_pow (e := e) (i := i) (by simp at hi; omega) 1
    simpa using this
  · rw [piHat_eq]
    exact onGrid_inv_two_pow (by have := hS hi; simp at this; omega) _

theorem valleyHat_onGrid {m κ e : ℕ} (hκe : κ ≤ e) {S : Finset ℕ} (hS : S ⊆ Icc 1 (κ - 1)) :
    OnGrid ((2 : ℝ)⁻¹ ^ e) (valleyHat m κ S) := by
  unfold valleyHat
  refine OnGrid.add (OnGrid.add (OnGrid.sum _ fun i hi => ?_) ?_) (OnGrid.sum _ fun i hi => ?_)
  · have := onGrid_inv_two_pow (e := e) (i := i) (by simp at hi; omega) 1
    simpa using this
  · rw [piHat_eq]; exact onGrid_inv_two_pow hκe _
  · rw [piHat_eq]
    exact onGrid_inv_two_pow (by have := hS hi; simp at this; omega) _

/-- The straddle profile is affine on every cell of the grid `2^{-(κ+1)} ℤ`. -/
theorem profile_isAffineOn_grid {m k κ : ℕ} (hkκ : k < κ) (hκm : κ ≤ m) (j : ℤ) :
    IsAffineOn (profile m k κ) (j * (2 : ℝ)⁻¹ ^ (κ + 1)) ((j + 1) * (2 : ℝ)⁻¹ ^ (κ + 1)) := by
  set h : ℝ := (2 : ℝ)⁻¹ ^ (κ + 1) with hhdef
  have hh : 0 < h := by positivity
  have hN : ((m : ℝ) + 1) = ((m + 1) * 2 ^ (κ + 1) : ℕ) * h := by
    rw [hhdef]; push_cast; rw [inv_pow, mul_assoc, mul_inv_cancel₀ (by positivity), mul_one]
  have hw : piHat m κ = 2 * ((m - κ + 1 : ℕ) : ℝ) * h := by
    rw [piHat_eq, hhdef, pow_succ]; ring
  have hhN : 2 * h ≤ (m : ℝ) + 1 := by
    have : h ≤ 1 / 2 := by
      rw [hhdef, pow_succ]
      have : (2 : ℝ)⁻¹ ^ κ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      nlinarith
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hwN : piHat m κ ≤ (m : ℝ) + 1 := by
    unfold piHat
    rw [div_le_iff₀ (by positivity)]
    have h1 : ((m - κ + 1 : ℕ) : ℝ) ≤ (m : ℝ) + 1 := by
      have : m - κ + 1 ≤ m + 1 := by omega
      exact_mod_cast this
    have h2 : (1 : ℝ) ≤ 2 ^ κ := one_le_pow₀ (by norm_num)
    nlinarith
  unfold profile
  refine IsAffineOn.const_mul (IsAffineOn.sum _ fun S hS => IsAffineOn.sum _ fun S' hS' => ?_) _
  obtain ⟨c, hc⟩ := (apexHat_onGrid (m := m) (e := κ + 1) (by omega)
    (Finset.mem_powerset.mp hS)).sub (valleyHat_onGrid (m := m) (e := κ + 1) (by omega)
    (Finset.mem_powerset.mp hS'))
  have hcell := perTent_isAffineOn_grid hh hN hw hhN hwN (j + c)
  have : IsAffineOn (perTent ((m : ℝ) + 1) (piHat m κ)) (j * h + (apexHat m k S - valleyHat m κ S'))
      ((j + 1) * h + (apexHat m k S - valleyHat m κ S')) := by
    rw [hc]; push_cast at hcell ⊢; convert hcell using 1 <;> ring
  refine this.comp_add.congr fun t _ => ?_
  congr 1; ring

/-- The straddle profile is `N`-periodic. -/
theorem profile_add_period (m k κ : ℕ) (t : ℝ) :
    profile m k κ (t + (m + 1)) = profile m k κ t := by
  unfold profile
  congr 1
  refine Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun S' _ => ?_
  have := perTent_add_int_mul ((m : ℝ) + 1) (piHat m κ) (apexHat m k S + t - valleyHat m κ S') 1
  rw [← this]; congr 1; push_cast; ring

/-- On a window of length at most `N/2`, the periodic tent is a sum of two tents. -/
theorem perTent_eq_sum_two {N w a d y : ℝ} (hN : 0 < N) (hd : d ≤ N / 2) (hwN : w ≤ N)
    (hy : y ∈ Set.Icc a (a + d)) :
    perTent N w y = ∑ l ∈ ({⌊a / N⌋, ⌊a / N⌋ + 1} : Finset ℤ), tent w (y - l * N) := by
  set L0 : ℤ := ⌊a / N⌋ with hL0
  have hL1 : (L0 : ℝ) * N ≤ a := by
    have := Int.floor_le (a / N); rwa [le_div_iff₀ hN] at this
  have hL2 : a < ((L0 : ℝ) + 1) * N := by
    have := Int.lt_floor_add_one (a / N); rwa [div_lt_iff₀ hN] at this
  unfold perTent
  refine tsum_eq_sum fun l hl => ?_
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hl
  apply tent_eq_zero
  rcases le_or_gt l (L0 - 1) with hl1 | hl1
  · have : (l : ℝ) ≤ L0 - 1 := by exact_mod_cast hl1
    have hpos : y - l * N ≥ N := by nlinarith [hy.1]
    rw [abs_of_pos (by linarith)]; linarith
  · have hl2 : L0 + 2 ≤ l := by omega
    have : (L0 : ℝ) + 2 ≤ l := by exact_mod_cast hl2
    have hneg : y - l * N ≤ -(N / 2) := by nlinarith [hy.2]
    rw [abs_of_neg (by linarith)]; linarith

theorem continuous_tent (w : ℝ) : Continuous (tent w) := by
  unfold tent; fun_prop

theorem continuous_perTent {N w : ℝ} (hN : 0 < N) (hwN : w ≤ N) : Continuous (perTent N w) := by
  rw [continuous_iff_continuousAt]
  intro y0
  have hev : (fun y => ∑ l ∈ ({⌊(y0 - N / 4) / N⌋, ⌊(y0 - N / 4) / N⌋ + 1} : Finset ℤ),
      tent w (y - l * N)) =ᶠ[nhds y0] perTent N w := by
    filter_upwards [Ioo_mem_nhds (show y0 - N / 4 < y0 by linarith)
      (show y0 < y0 + N / 4 by linarith)] with y hy
    exact (perTent_eq_sum_two hN (le_refl _) hwN
      ⟨by linarith [hy.1], by linarith [hy.2]⟩).symm
  refine ContinuousAt.congr ?_ hev
  exact (continuous_finsetSum _ fun l _ => (continuous_tent w).comp
    (continuous_id.sub continuous_const)).continuousAt

theorem piHat_le (m κ : ℕ) : piHat m κ ≤ (m : ℝ) + 1 := by
  unfold piHat
  rw [div_le_iff₀ (by positivity)]
  have h1 : ((m - κ + 1 : ℕ) : ℝ) ≤ (m : ℝ) + 1 := by
    have : m - κ + 1 ≤ m + 1 := by omega
    exact_mod_cast this
  have h2 : (1 : ℝ) ≤ 2 ^ κ := one_le_pow₀ (by norm_num)
  nlinarith

theorem continuous_profile (m k κ : ℕ) : Continuous (profile m k κ) := by
  unfold profile
  refine continuous_const.mul (continuous_finsetSum _ fun S _ => continuous_finsetSum _ fun S' _ => ?_)
  exact (continuous_perTent (by positivity) (piHat_le m κ)).comp (by fun_prop)

theorem dnpPeriod_real (s0 m : ℕ) :
    (dnpPeriod s0 m : ℝ) = 4 * (2 ^ s0 * ((m : ℝ) + 1)) := by
  unfold dnpPeriod; push_cast; rw [strokeLen_real (by omega), piHat_zero]

theorem oddRange_eq_image (M : ℕ) : oddRange (2 * M) = (range M).image (fun n => 2 * n + 1) := by
  ext ξ; simp only [oddRange, mem_filter, mem_range, mem_image]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨ξ / 2, by omega, by omega⟩
  · rintro ⟨n, hn, rfl⟩; omega

/-- The count of odd shifts below a level of the profile, against the volume of the sublevel set on
four periods. -/
theorem count_profile_vs_volume {s0 m k κ : ℕ} (hkκ : k < κ) (hκm : κ ≤ m) (τ : ℝ) :
    |(((oddRange (dnpPeriod s0 m)).filter fun ξ : ℕ =>
        profile m k κ (((ξ : ℝ) + 1 / 2) / 2 ^ s0) < τ).card : ℝ) -
      2 ^ s0 / 2 * (volume {t ∈ Set.Ico (0 : ℝ) (4 * ((m : ℝ) + 1)) | profile m k κ t < τ}).toReal|
    ≤ ((m : ℝ) + 1) * 2 ^ (κ + 3) := by
  classical
  set Λ : ℝ := 2 ^ s0 with hΛdef
  set f := profile m k κ with hfdef
  set h : ℝ := (2 : ℝ)⁻¹ ^ (κ + 1) with hhdef
  set G : ℕ := (m + 1) * 2 ^ (κ + 3) with hGdef
  have hΛ : 0 < Λ := by positivity
  have hh : 0 < h := by positivity
  obtain ⟨M', hM'⟩ : ∃ M', dnpPeriod s0 m = 2 * M' := by
    unfold dnpPeriod; exact ⟨2 * strokeLen s0 m 0, by ring⟩
  have hPR := dnpPeriod_real s0 m
  rw [hM'] at hPR ⊢
  push_cast at hPR
  have hM'R : (M' : ℝ) = 2 * (Λ * ((m : ℝ) + 1)) := by linarith
  have hGh : (G : ℝ) * h = 4 * ((m : ℝ) + 1) := by
    rw [hGdef, hhdef]; push_cast
    rw [show κ + 3 = (κ + 1) + 2 by ring, pow_add, inv_pow]; field_simp; ring
  set o : ℝ := 3 / 2 / Λ with hodef
  set s : ℝ := 2 / Λ with hsdef
  have hs : 0 < s := by positivity
  have hpt : ∀ n : ℕ, (((2 * n + 1 : ℕ) : ℝ) + 1 / 2) / Λ = o + n * s := by
    intro n; rw [hodef, hsdef]; push_cast; field_simp; ring
  -- step 1: odd shifts are `2n + 1`
  have hC : ((oddRange (2 * M')).filter fun ξ : ℕ => f (((ξ : ℝ) + 1 / 2) / Λ) < τ).card =
      ((range M').filter fun n : ℕ => f (o + n * s) < τ).card := by
    rw [oddRange_eq_image, Finset.filter_image, Finset.card_image_of_injective _
      (fun a b hab => by omega)]
    congr 1
    exact Finset.filter_congr fun n _ => by rw [hpt]
  -- the cells
  set J : ℕ → Set ℝ := fun i => {t ∈ Set.Ico (i * h) ((i + 1) * h) | f t < τ} with hJdef
  have hJord : ∀ i : ℕ, (J i).OrdConnected := by
    intro i
    have := (profile_isAffineOn_grid (m := m) hkκ hκm (i : ℤ)).ordConnected_sublevel τ
    rw [Int.cast_natCast] at this
    exact this
  have hJmeas : ∀ i, MeasurableSet (J i) := fun i => (hJord i).measurableSet
  have hpos_pt : ∀ n : ℕ, 0 ≤ o + n * s := fun n => by positivity
  -- step 2: fibres over cells
  have hfib : ((range M').filter fun n : ℕ => f (o + n * s) < τ).card =
      ∑ i ∈ range G, ((range M').filter fun n : ℕ => o + n * s ∈ J i).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun n : ℕ => ⌊(o + n * s) / h⌋₊) (t := range G)]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.filter_filter]
      congr 1
      refine Finset.filter_congr fun n _ => ?_
      rw [Nat.floor_eq_iff (div_nonneg (hpos_pt n) hh.le), le_div_iff₀ hh, div_lt_iff₀ hh]
      simp only [hJdef, Set.mem_ofPred_eq, Set.mem_Ico]
      tauto
    · intro n hn
      simp only [Finset.mem_coe, mem_filter, mem_range] at hn ⊢
      rw [Nat.floor_lt (div_nonneg (hpos_pt n) hh.le), div_lt_iff₀ hh, hGh]
      have hn' : (n : ℝ) + 1 ≤ M' := by exact_mod_cast hn.1
      have h1 : o + n * s = (3 / 2 + 2 * n) / Λ := by rw [hodef, hsdef]; field_simp
      rw [h1, div_lt_iff₀ hΛ]
      nlinarith [hM'R]
  -- step 3: volume over cells
  have hvol : volume {t ∈ Set.Ico (0 : ℝ) (4 * ((m : ℝ) + 1)) | f t < τ} =
      ∑ i ∈ range G, volume (J i) := by
    rw [← measure_biUnion_finset _ fun i _ => hJmeas i]
    · congr 1
      ext t
      simp only [Set.mem_ofPred_eq, Set.mem_Ico, Set.mem_iUnion, mem_range, hJdef]
      constructor
      · rintro ⟨⟨h0, h1⟩, hft⟩
        refine ⟨⌊t / h⌋₊, ?_, ⟨?_, ?_⟩, hft⟩
        · rw [Nat.floor_lt (div_nonneg h0 hh.le), div_lt_iff₀ hh, hGh]; exact h1
        · have := Nat.floor_le (div_nonneg h0 hh.le); rwa [le_div_iff₀ hh] at this
        · have := Nat.lt_floor_add_one (t / h); rwa [div_lt_iff₀ hh] at this
      · rintro ⟨i, hi, ⟨h0, h1⟩, hft⟩
        refine ⟨⟨le_trans (by positivity) h0, ?_⟩, hft⟩
        have : ((i : ℝ) + 1) * h ≤ G * h := by
          have : (i : ℝ) + 1 ≤ G := by exact_mod_cast hi
          nlinarith
        linarith
    · intro i _ j _ hij
      simp only [Function.onFun]
      rw [Set.disjoint_left]
      rintro t ⟨⟨hi0, hi1⟩, -⟩ ⟨⟨hj0, hj1⟩, -⟩
      rcases lt_or_gt_of_ne hij with hlt | hlt
      · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast hlt
        nlinarith
      · have : (j : ℝ) + 1 ≤ i := by exact_mod_cast hlt
        nlinarith
  have hfinJ : ∀ i, volume (J i) ≠ ⊤ := fun i =>
    ne_top_of_le_ne_top (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top)
      (measure_mono (fun t ht => ht.1))
  rw [hC, hfib, hvol, ENNReal.toReal_sum fun i _ => hfinJ i]
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc |∑ i ∈ range G, (((range M').filter fun n : ℕ => o + n * s ∈ J i).card - Λ / 2 *
        (volume (J i)).toReal)|
      ≤ ∑ i ∈ range G, |(((range M').filter fun n : ℕ => o + n * s ∈ J i).card : ℝ) - Λ / 2 *
        (volume (J i)).toReal| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ range G, (1 : ℝ) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hsub : J i ⊆ Set.Ioo (o - s) (o + M' * s) := by
          intro t ht
          obtain ⟨⟨h0, h1⟩, -⟩ := ht
          have hi' : (i : ℝ) + 1 ≤ G := by exact_mod_cast (mem_range.mp hi)
          constructor
          · have : o - s < 0 := by rw [hodef, hsdef]; rw [div_sub_div_same]; apply div_neg_of_neg_of_pos <;> norm_num [hΛ]
            nlinarith [le_trans (by positivity : (0:ℝ) ≤ i * h) h0]
          · have h2 : ((i : ℝ) + 1) * h ≤ G * h := by nlinarith
            have h3 : o + M' * s = (3 / 2 + 2 * M') / Λ := by rw [hodef, hsdef]; field_simp
            rw [h3, lt_div_iff₀ hΛ, hM'R]
            rw [hGh] at h2
            nlinarith
        have := card_lattice_ordConnected (hJord i) hs hsub
        have e : (volume (J i)).toReal / s = Λ / 2 * (volume (J i)).toReal := by
          rw [hsdef]; field_simp
        rwa [e] at this
    _ = ((m : ℝ) + 1) * 2 ^ (κ + 3) := by rw [Finset.sum_const, card_range, hGdef]; simp

/-- The sublevel set of the profile on four periods has four times the volume of one. -/
theorem volume_sublevel_four (m k κ : ℕ) (τ : ℝ) :
    volume {t ∈ Set.Ico (0 : ℝ) (4 * ((m : ℝ) + 1)) | profile m k κ t < τ} =
      4 * volume {t ∈ Set.Ico (0 : ℝ) ((m : ℝ) + 1) | profile m k κ t < τ} := by
  set N : ℝ := (m : ℝ) + 1 with hNdef
  have hN : 0 < N := by positivity
  set f := profile m k κ
  set T : ℕ → Set ℝ := fun j => {t ∈ Set.Ico (j * N) ((j + 1) * N) | f t < τ} with hTdef
  have hfper : ∀ (j : ℕ) (t : ℝ), f (t + j * N) = f t := by
    intro j
    induction j with
    | zero => intro t; simp
    | succ j ih =>
      intro t
      rw [show t + ((j + 1 : ℕ) : ℝ) * N = (t + j * N) + N by push_cast; ring]
      rw [show f (t + j * N + N) = f (t + j * N) from profile_add_period m k κ _, ih]
  have hTj : ∀ j : ℕ, T j = (fun t => t + (-(j * N))) ⁻¹' T 0 := by
    intro j; ext t
    simp only [hTdef, Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_Ico, Nat.cast_zero, zero_mul,
      zero_add, one_mul]
    have := hfper j (t + -(j * N))
    rw [show t + -(j * N) + j * N = t by ring] at this
    rw [this]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨by linarith, by linarith⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨by linarith, by linarith⟩, h3⟩
  have hmeas : ∀ j, MeasurableSet (T j) := fun j =>
    measurableSet_Ico.inter (measurableSet_lt (continuous_profile m k κ).measurable measurable_const)
  have hunion : {t ∈ Set.Ico (0 : ℝ) (4 * N) | f t < τ} = ⋃ j ∈ range 4, T j := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_Ico, Set.mem_iUnion, mem_range, hTdef]
    constructor
    · rintro ⟨⟨h0, h1⟩, hft⟩
      refine ⟨⌊t / N⌋₊, ?_, ⟨?_, ?_⟩, hft⟩
      · rw [Nat.floor_lt (div_nonneg h0 hN.le), div_lt_iff₀ hN]; push_cast; linarith
      · have := Nat.floor_le (div_nonneg h0 hN.le); rwa [le_div_iff₀ hN] at this
      · have := Nat.lt_floor_add_one (t / N); rwa [div_lt_iff₀ hN] at this
    · rintro ⟨j, hj, ⟨h0, h1⟩, hft⟩
      have hj' : (j : ℝ) + 1 ≤ 4 := by exact_mod_cast hj
      exact ⟨⟨le_trans (by positivity) h0, by nlinarith⟩, hft⟩
  rw [hunion, measure_biUnion_finset _ fun j _ => hmeas j]
  · rw [Finset.sum_congr rfl fun j _ => by rw [hTj j, measure_preimage_add_right]]
    simp [hTdef]
  · intro i _ j _ hij
    simp only [Function.onFun]
    rw [Set.disjoint_left]
    rintro t ⟨⟨hi0, hi1⟩, -⟩ ⟨⟨hj0, hj1⟩, -⟩
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast hlt
      nlinarith
    · have : (j : ℝ) + 1 ≤ i := by exact_mod_cast hlt
      nlinarith

/-- `ξ ↦ P - ξ` permutes the odd residues (`P` even). -/
theorem card_filter_oddRange_neg {P : ℕ} (hP : P % 2 = 0) (p : ℕ → Prop) [DecidablePred p] :
    ((oddRange P).filter fun ξ => p (P - ξ)).card = ((oddRange P).filter p).card := by
  refine Finset.card_bij (fun ξ _ => P - ξ) ?_ ?_ ?_
  · intro ξ hξ
    simp only [oddRange, mem_filter, mem_range] at hξ ⊢
    exact ⟨⟨by omega, by omega⟩, hξ.2⟩
  · intro a ha b hb hab
    simp only [oddRange, mem_filter, mem_range] at ha hb
    omega
  · intro y hy
    simp only [oddRange, mem_filter, mem_range] at hy
    refine ⟨P - y, ?_, by omega⟩
    simp only [oddRange, mem_filter, mem_range]
    exact ⟨⟨by omega, by omega⟩, by rw [show P - (P - y) = y by omega]; exact hy.2⟩

/-- **Lemma 7.4(c)**: for `ξ` uniform over the odd residues modulo `P`, the probability that
`X^±_{k,κ}(ξ) < τ M_k` differs from the Lebesgue probability that `x_k(t) < τ` (`t` uniform on
`[0, N)`) by at most `2^{κ+2-s₀}`. -/
theorem prob_straddle_vs_profile {s0 m k κ : ℕ} (hk : 1 ≤ k) (hkκ : k < κ) (hκm : κ ≤ m)
    (hms : m < s0) (hpi : strokeLen s0 m κ ≤ scaleR s0 k) (τ : ℝ) (dir : Bool) :
    |(((oddRange (dnpPeriod s0 m)).filter fun ξ =>
        (classStraddleCount s0 m k κ dir ξ : ℝ) < τ * (2 ^ (k + 1) * strokeLen s0 m κ)).card : ℝ) /
        (oddRange (dnpPeriod s0 m)).card -
      ((m : ℝ) + 1)⁻¹ * (volume {t ∈ Set.Ico (0 : ℝ) ((m : ℝ) + 1) | profile m k κ t < τ}).toReal|
    ≤ 2 ^ (κ + 2) / 2 ^ s0 := by
  classical
  set P := dnpPeriod s0 m with hPdef
  have hPeven : P % 2 = 0 := by rw [hPdef]; unfold dnpPeriod; omega
  have hMpos : (0 : ℝ) < 2 ^ (k + 1) * strokeLen s0 m κ := by
    have := strokeLen_pos s0 m κ; positivity
  -- reduce to the `+` direction and to the profile
  have hcount : ((oddRange P).filter fun ξ =>
        (classStraddleCount s0 m k κ dir ξ : ℝ) < τ * (2 ^ (k + 1) * strokeLen s0 m κ)).card =
      ((oddRange P).filter fun ξ : ℕ => profile m k κ (((ξ : ℝ) + 1 / 2) / 2 ^ s0) < τ).card := by
    have hplus : ∀ ξ : ℕ, ((classStraddleCount s0 m k κ true ξ : ℝ) <
        τ * (2 ^ (k + 1) * strokeLen s0 m κ) ↔ profile m k κ (((ξ : ℝ) + 1 / 2) / 2 ^ s0) < τ) := by
      intro ξ
      rw [classStraddleCount_eq_profile hk hkκ hκm hms hpi ξ, mul_comm τ, mul_lt_mul_iff_right₀ hMpos]
    cases dir
    · calc ((oddRange P).filter fun ξ => (classStraddleCount s0 m k κ false ξ : ℝ) <
              τ * (2 ^ (k + 1) * strokeLen s0 m κ)).card
          = ((oddRange P).filter fun ξ => (classStraddleCount s0 m k κ true (P - ξ) : ℝ) <
              τ * (2 ^ (k + 1) * strokeLen s0 m κ)).card := by
            congr 1
            refine Finset.filter_congr fun ξ hξ => ?_
            have hξP : ξ ≤ P := by simp only [oddRange, mem_filter, mem_range] at hξ; omega
            rw [classStraddleCount_false_eq hξP]
        _ = ((oddRange P).filter fun ξ => (classStraddleCount s0 m k κ true ξ : ℝ) <
              τ * (2 ^ (k + 1) * strokeLen s0 m κ)).card :=
            card_filter_oddRange_neg hPeven (fun ξ => (classStraddleCount s0 m k κ true ξ : ℝ) <
              τ * (2 ^ (k + 1) * strokeLen s0 m κ))
        _ = _ := congrArg Finset.card (Finset.filter_congr fun ξ _ => hplus ξ)
    · exact congrArg Finset.card (Finset.filter_congr fun ξ _ => hplus ξ)
  rw [hcount]
  -- the counting estimate on four periods
  have hcv := count_profile_vs_volume (s0 := s0) hkκ hκm τ
  rw [volume_sublevel_four, ENNReal.toReal_mul] at hcv
  obtain ⟨M', hM'⟩ : ∃ M', P = 2 * M' := ⟨P / 2, by omega⟩
  have hPR := dnpPeriod_real s0 m
  rw [← hPdef, hM'] at hPR
  push_cast at hPR
  rw [hM', card_oddRange_two_mul]
  rw [← hPdef, hM'] at hcv
  have hΛ : (0 : ℝ) < 2 ^ s0 := by positivity
  have hN : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hM'R : (M' : ℝ) = 2 * (2 ^ s0 * ((m : ℝ) + 1)) := by linarith
  set C : ℝ := (((oddRange (2 * M')).filter fun ξ : ℕ =>
    profile m k κ (((ξ : ℝ) + 1 / 2) / 2 ^ s0) < τ).card : ℝ)
  set V : ℝ := (volume {t ∈ Set.Ico (0 : ℝ) ((m : ℝ) + 1) | profile m k κ t < τ}).toReal
  have h4 : ENNReal.toReal 4 = 4 := by norm_num
  rw [h4] at hcv
  have key : C / M' - ((m : ℝ) + 1)⁻¹ * V = (C - 2 ^ s0 / 2 * (4 * V)) / M' := by
    rw [hM'R]; field_simp; ring
  have hM'pos : (0 : ℝ) < M' := by rw [hM'R]; positivity
  rw [key, abs_div, abs_of_pos hM'pos, div_le_div_iff₀ hM'pos hΛ]
  calc |C - 2 ^ s0 / 2 * (4 * V)| * 2 ^ s0 ≤ ((m : ℝ) + 1) * 2 ^ (κ + 3) * 2 ^ s0 :=
        mul_le_mul_of_nonneg_right hcv hΛ.le
    _ = 2 ^ (κ + 2) * M' := by rw [hM'R, pow_succ]; ring

end MergeDepth
