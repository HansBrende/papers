import DirectedReciprocity.DNPConjectureApp

/-!
# Block pairs: straddle counts and the straddle profile (Section 7, Definitions 7.1 and 7.2,
Lemma 7.4(a), (b))

The objects are those of the tenth paper's library (`DirectedReciprocity`): the scales
`R_i = scaleR s0 i`, the stroke lengths `Π_i = strokeLen s0 m i`, the period `P = dnpPeriod s0 m`,
the apex times `𝒜_i = periodVApices s0 m i` of the level-`i` V's in one period, the straddle sets
`Strad(c₀, α, Π, R) = straddleSet c₀ α Π R`, the cancellers `κ_a(k) = cancellerBelow m a k` and
the class straddle counts `X^±_{k,κ}(ξ) = classStraddleCount s0 m k κ dir ξ` (`dir = true` for `+`).

* Definition 7.1: the coarse zone `coarseZone m = {1, …, ⌊N/4⌋}` (`N = m + 1`), `jZero m = j₀`, the
  `a`-good levels `goodLevels` and their number `goodCount` `= Γ_{a,±}(ξ)`.
* Definition 7.2: `piHat` `= Π̂_i`, `apexHat` `= â_S`, `valleyHat` `= v̂_{S'}`, the tent `tent` `= Δ`,
  its `N`-periodization `perTent`, the profile `profile m k κ` `= x_k`, its mean `profileMean`
  `= μ_k`, variance `profileVariance`, `relVariance` `= V_k`, `relVarianceA` `= V^{(a)}_k`,
  `meanRelVariance` `= V̄^{(a)}_m`, and Conjecture S (`ConjectureS a`).
* `sum_periodVApices`: sums over `𝒜_k` are sums over the four level-`0` strokes and the branch sets
  `S ⊆ {1, …, k - 1}` (the offset of the apex with branch set `S` is `apexOffsetFrom s0 m 0 (k - 1) S`).
* `card_straddleSet_eq`: **Lemma 7.4(a)**, `|Strad(c₀, α, Π, R)| = max(0, Π - |2(c₀ - α - Π) + 1|)`
  whenever `Π ≤ R` (no other hypothesis).
* `classStraddleCount_eq_profile`, `classStraddleCount_false_eq`: **Lemma 7.4(b)**,
  `X⁺_{k,κ}(ξ) = M_k x_k((ξ + 1/2)/Λ)` with `M_k = 2^{k+1} Π_κ`, and `X⁻(ξ) = X⁺(P - ξ)`.
-/

namespace MergeDepth

open Finset DirectedReciprocity MeasureTheory

/-! ### Definition 7.1 -/

/-- The coarse zone `𝒦 = {1, …, ⌊N/4⌋}`, `N = m + 1`. -/
def coarseZone (m : ℕ) : Finset ℕ := Icc 1 ((m + 1) / 4)

/-- `j₀ = ⌊log₂ N⌋ + 1`. -/
def jZero (m : ℕ) : ℕ := Nat.log 2 (m + 1) + 1

/-- The coarse levels that are `a`-good in direction `dir` (`true` for `+`) at the shift `ξ`:
`X^±_{k,κ_a(k)}(ξ) ≥ 2^{k+2} R_k / 2^{a+7}`. -/
def goodLevels (s0 m a : ℕ) (dir : Bool) (ξ : ℕ) : Finset ℕ :=
  (coarseZone m).filter fun k =>
    2 ^ (k + 2) * scaleR s0 k ≤ 2 ^ (a + 7) * classStraddleCount s0 m k (cancellerBelow m a k) dir ξ

/-- `Γ_{a,±}(ξ)`, the number of `a`-good coarse levels. -/
def goodCount (s0 m a : ℕ) (dir : Bool) (ξ : ℕ) : ℕ := (goodLevels s0 m a dir ξ).card

/-! ### Apices and branch sets -/

/-- Span bound for the internal apices (a copy of the tenth paper's private lemma). -/
theorem vApicesAux_span {s0 m : ℕ} (hms : m ≤ s0) :
    ∀ (d i : ℕ), i + 1 + d ≤ m →
      ∀ α ∈ vApicesAux s0 m i d,
        scaleR s0 i ≤ α ∧ α + 2 * strokeLen s0 m (i + 1 + d) ≤ strokeLen s0 m i := by
  intro d
  induction d with
  | zero =>
    intro i hi α hα
    rw [vApicesAux, mem_singleton] at hα
    subst hα
    have hsp := strokeLen_succ (by omega : i < m) hms
    exact ⟨le_refl _, by simpa using le_of_eq hsp.symm⟩
  | succ d ih =>
    intro i hi α hα
    have hsp := strokeLen_succ (by omega : i < m) hms
    rw [vApicesAux, mem_union, mem_image, mem_image] at hα
    rcases hα with ⟨β, hβ, rfl⟩ | ⟨β, hβ, rfl⟩
    · obtain ⟨hβ1, hβ2⟩ := ih (i + 1) (by omega) β hβ
      rw [show i + 1 + (d + 1) = i + 1 + 1 + d by omega]
      exact ⟨by omega, by omega⟩
    · obtain ⟨hβ1, hβ2⟩ := ih (i + 1) (by omega) β hβ
      rw [show i + 1 + (d + 1) = i + 1 + 1 + d by omega]
      exact ⟨by omega, by omega⟩

/-- Offset of the apex with branch set `S` of a level-`(i + d + 1)` V inside a level-`i` stroke. -/
def apexOffsetFrom (s0 m i d : ℕ) (S : Finset ℕ) : ℕ :=
  ∑ l ∈ Icc i (i + d), scaleR s0 l + ∑ l ∈ S, strokeLen s0 m l

/-- Sums over the internal apices are sums over branch sets. -/
theorem sum_vApicesAux {M : Type*} [AddCommMonoid M] {s0 m : ℕ} (hms : m ≤ s0) :
    ∀ (d i : ℕ), i + 1 + d ≤ m → ∀ f : ℕ → M,
      ∑ β ∈ vApicesAux s0 m i d, f β =
        ∑ S ∈ (Icc (i + 1) (i + d)).powerset, f (apexOffsetFrom s0 m i d S) := by
  intro d
  induction d with
  | zero =>
    intro i hi f
    have : Icc (i + 1) (i + 0) = ∅ := Icc_eq_empty (by omega)
    simp [vApicesAux, apexOffsetFrom]
  | succ d ih =>
    intro i hi f
    have hspan := vApicesAux_span hms d (i + 1) (by omega)
    have hdisj : Disjoint ((vApicesAux s0 m (i + 1) d).image (fun β => scaleR s0 i + β))
        ((vApicesAux s0 m (i + 1) d).image (fun β => scaleR s0 i + strokeLen s0 m (i + 1) + β)) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      rw [mem_image] at hx1 hx2
      obtain ⟨β₁, hβ₁, rfl⟩ := hx1
      obtain ⟨β₂, hβ₂, heq⟩ := hx2
      have h1 := (hspan β₁ hβ₁).2
      have hp := strokeLen_pos s0 m (i + 1 + 1 + d)
      omega
    rw [vApicesAux, Finset.sum_union hdisj, Finset.sum_image (fun a _ b _ h => by omega),
      Finset.sum_image (fun a _ b _ h => by omega),
      ih (i + 1) (by omega) (fun β => f (scaleR s0 i + β)),
      ih (i + 1) (by omega) (fun β => f (scaleR s0 i + strokeLen s0 m (i + 1) + β))]
    have hins : Icc (i + 1) (i + (d + 1)) = insert (i + 1) (Icc (i + 1 + 1) (i + 1 + d)) := by
      ext x; simp only [mem_Icc, mem_insert]; omega
    have hnot : i + 1 ∉ Icc (i + 1 + 1) (i + 1 + d) := by simp
    rw [hins, Finset.sum_powerset_insert hnot]
    have hR : ∑ l ∈ Icc i (i + (d + 1)), scaleR s0 l =
        scaleR s0 i + ∑ l ∈ Icc (i + 1) (i + 1 + d), scaleR s0 l := by
      have : Icc i (i + (d + 1)) = insert i (Icc (i + 1) (i + 1 + d)) := by
        ext x; simp only [mem_Icc, mem_insert]; omega
      rw [this, Finset.sum_insert (by simp)]
    congr 1
    · refine Finset.sum_congr rfl fun S _ => ?_
      unfold apexOffsetFrom
      rw [hR]; ring_nf
    · refine Finset.sum_congr rfl fun S hS => ?_
      have hS' : i + 1 ∉ S := by
        intro h; have := (Finset.mem_powerset.mp hS) h; simp at this
      unfold apexOffsetFrom
      rw [hR, Finset.sum_insert hS']; ring_nf

theorem sum_periodVApices {M : Type*} [AddCommMonoid M] {s0 m k : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m)
    (hms : m ≤ s0) (f : ℕ → M) :
    ∑ c ∈ periodVApices s0 m k, f c =
      ∑ q ∈ range 4, ∑ S ∈ (Icc 1 (k - 1)).powerset,
        f (q * strokeLen s0 m 0 + apexOffsetFrom s0 m 0 (k - 1) S) := by
  unfold periodVApices
  rw [Finset.sum_biUnion]
  · refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.sum_image (fun a _ b _ h => by omega)]
    have := sum_vApicesAux hms (k - 1) 0 (by omega) (fun β => f (q * strokeLen s0 m 0 + β))
    simpa using this
  · intro q₁ _ q₂ _ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rw [mem_image] at hx1 hx2
    obtain ⟨β₁, hβ₁, rfl⟩ := hx1
    obtain ⟨β₂, hβ₂, heq⟩ := hx2
    have h1 := (vApicesAux_span hms (k - 1) 0 (by omega) β₁ hβ₁).2
    have h2 := (vApicesAux_span hms (k - 1) 0 (by omega) β₂ hβ₂).2
    have hp := strokeLen_pos s0 m (0 + 1 + (k - 1))
    rcases lt_or_gt_of_ne hne with hlt | hlt <;> nlinarith

/-- Properties of all internal apices transfer to all branch sets. -/
theorem forall_apexOffsetFrom {s0 m : ℕ} (hms : m ≤ s0) {d i : ℕ} (hdi : i + 1 + d ≤ m)
    {P : ℕ → Prop} (hP : ∀ β ∈ vApicesAux s0 m i d, P β) :
    ∀ S ∈ (Icc (i + 1) (i + d)).powerset, P (apexOffsetFrom s0 m i d S) := by
  classical
  have h := sum_vApicesAux hms d i hdi (fun β => if P β then 0 else 1)
  have h0 : ∑ β ∈ vApicesAux s0 m i d, (if P β then 0 else 1) = 0 :=
    Finset.sum_eq_zero fun β hβ => by simp [hP β hβ]
  rw [h0, eq_comm, Finset.sum_eq_zero_iff] at h
  intro S hS
  have := h S hS
  by_contra hc
  simp [hc] at this

/-! ### Lemma 7.4(a) -/

/-- **Lemma 7.4(a)**: `|Strad(c₀, α, Π, R)| = max(0, Π - |2(c₀ - α - Π) + 1|)` whenever `Π ≤ R`. -/
theorem card_straddleSet_eq {c0 α : ℤ} {p R : ℕ} (hpR : p ≤ R) :
    ((straddleSet c0 α p R).card : ℤ) = max 0 ((p : ℤ) - |2 * (c0 - α - p) + 1|) := by
  set y : ℤ := c0 - α - p with hy
  rcases le_or_gt 0 y with h0 | h0
  · have key : (straddleSet c0 α p R).map (Nat.castEmbedding : ℕ ↪ ℤ) = Finset.Icc (y + 1) (p - 1 - y) := by
      ext x
      simp only [Finset.mem_map, straddleSet, Finset.mem_filter, Finset.mem_Icc, Nat.castEmbedding_apply]
      constructor
      · rintro ⟨d, ⟨⟨h1, h2⟩, h3, h4, h5, h6⟩, rfl⟩
        constructor <;> omega
      · rintro ⟨h1, h2⟩
        refine ⟨x.toNat, ⟨⟨by omega, by omega⟩, by omega, by omega, by omega, by omega⟩, by omega⟩
    rw [← Finset.card_map (Nat.castEmbedding : ℕ ↪ ℤ), key, Int.card_Icc, Int.toNat_eq_max,
      abs_of_nonneg (by omega : (0:ℤ) ≤ 2 * y + 1)]
    omega
  · have key : (straddleSet c0 α p R).map (Nat.castEmbedding : ℕ ↪ ℤ) = Finset.Icc (-y) (y + p) := by
      ext x
      simp only [Finset.mem_map, straddleSet, Finset.mem_filter, Finset.mem_Icc, Nat.castEmbedding_apply]
      constructor
      · rintro ⟨d, ⟨⟨h1, h2⟩, h3, h4, h5, h6⟩, rfl⟩
        constructor <;> omega
      · rintro ⟨h1, h2⟩
        refine ⟨x.toNat, ⟨⟨by omega, by omega⟩, by omega, by omega, by omega, by omega⟩, by omega⟩
    rw [← Finset.card_map (Nat.castEmbedding : ℕ ↪ ℤ), key, Int.card_Icc, Int.toNat_eq_max,
      abs_of_neg (by omega : 2 * y + 1 < 0)]
    omega


/-! ### The straddle profile -/

/-- `Π̂_i = n_i 2^{-i}`, `n_i = m - i + 1`. -/
noncomputable def piHat (m i : ℕ) : ℝ := ((m - i + 1 : ℕ) : ℝ) / 2 ^ i

/-- `â_S`: the level-`k` apex time of branch set `S` in one level-`0` stroke, in units of `Λ`. -/
noncomputable def apexHat (m k : ℕ) (S : Finset ℕ) : ℝ :=
  ∑ i ∈ range k, (2 : ℝ)⁻¹ ^ i + ∑ i ∈ S, piHat m i

/-- `v̂_{S'}`: the level-`κ` valley time of branch set `S'`, in units of `Λ`. -/
noncomputable def valleyHat (m κ : ℕ) (S : Finset ℕ) : ℝ :=
  ∑ i ∈ range κ, (2 : ℝ)⁻¹ ^ i + piHat m κ + ∑ i ∈ S, piHat m i

/-- The tent `Δ(y) = max(0, w - 2|y|)` (with `w = Π̂_κ`). -/
noncomputable def tent (w y : ℝ) : ℝ := max 0 (w - 2 * |y|)

/-- The `N`-periodization `∑_{l ∈ ℤ} Δ(y - lN)` of the tent. -/
noncomputable def perTent (N w y : ℝ) : ℝ := ∑' l : ℤ, tent w (y - l * N)

/-- **Definition 7.2**: the straddle profile `x_k(t)`. -/
noncomputable def profile (m k κ : ℕ) (t : ℝ) : ℝ :=
  (2 ^ (k - 1) * piHat m κ)⁻¹ *
    ∑ S ∈ (Icc 1 (k - 1)).powerset, ∑ S' ∈ (Icc 1 (κ - 1)).powerset,
      perTent (m + 1) (piHat m κ) (apexHat m k S + t - valleyHat m κ S')

/-- `μ_k`, the mean of `x_k(t)` for `t` uniform on `[0, N)`. -/
noncomputable def profileMean (m k κ : ℕ) : ℝ :=
  ((m : ℝ) + 1)⁻¹ * ∫ t in (0 : ℝ)..((m : ℝ) + 1), profile m k κ t

/-- The variance of `x_k(t)` for `t` uniform on `[0, N)`. -/
noncomputable def profileVariance (m k κ : ℕ) : ℝ :=
  ((m : ℝ) + 1)⁻¹ * ∫ t in (0 : ℝ)..((m : ℝ) + 1), (profile m k κ t - profileMean m k κ) ^ 2

/-- `V_k = Var x_k(t) / μ_k²`. -/
noncomputable def relVariance (m k κ : ℕ) : ℝ := profileVariance m k κ / profileMean m k κ ^ 2

/-- `V^{(a)}_k`, `V_k` at `κ = κ_a(k)`. -/
noncomputable def relVarianceA (m a k : ℕ) : ℝ := relVariance m k (cancellerBelow m a k)

/-- `V̄^{(a)}_m`, the mean of `V^{(a)}_k` over the coarse zone. -/
noncomputable def meanRelVariance (m a : ℕ) : ℝ :=
  ((coarseZone m).card : ℝ)⁻¹ * ∑ k ∈ coarseZone m, relVarianceA m a k

/-- **Conjecture S** (Conjecture 7.3) for one block length `a`: `V̄^{(a)}_m → 0` as `m → ∞`. -/
def ConjectureS (a : ℕ) : Prop :=
  Filter.Tendsto (fun m => meanRelVariance m a) Filter.atTop (nhds 0)

theorem tent_eq_zero {w y : ℝ} (h : w ≤ 2 * |y|) : tent w y = 0 := by
  unfold tent; exact max_eq_left (by linarith)

theorem tent_nonneg (w y : ℝ) : 0 ≤ tent w y := le_max_left _ _

theorem perTent_add_int_mul (N w y : ℝ) (n : ℤ) : perTent N w (y + n * N) = perTent N w y := by
  unfold perTent
  rw [← (Equiv.addRight n).tsum_eq]
  congr 1; ext l
  simp only [Equiv.coe_addRight, Int.cast_add]
  ring_nf

theorem perTent_eq_sum_four {N w y v : ℝ} (hN : 0 < N) (hw : 0 ≤ w) (hy0 : 0 < y) (hy1 : y < 4 * N)
    (hv0 : w ≤ 2 * v) (hv1 : 2 * v + w ≤ 2 * N) :
    perTent N w (y - v) = ∑ j ∈ range 4, tent w (y - v - j * N) := by
  unfold perTent
  rw [tsum_eq_sum (s := ({0, 1, 2, 3} : Finset ℤ))]
  · simp [Finset.sum_range_succ]; ring_nf
  · intro l hl
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hl
    apply tent_eq_zero
    rcases le_or_gt l (-1) with h | h
    · have hl' : (l : ℝ) ≤ -1 := by exact_mod_cast h
      have : y - v - l * N ≥ y - v + N := by nlinarith
      rw [abs_of_pos (by linarith)]; linarith
    · have h4 : 4 ≤ l := by omega
      have hl' : (4 : ℝ) ≤ l := by exact_mod_cast h4
      have : y - v - l * N ≤ y - v - 4 * N := by nlinarith
      rw [abs_of_neg (by linarith)]; linarith

theorem scaleR_real {s0 i : ℕ} (hi : i ≤ s0) : (scaleR s0 i : ℝ) = 2 ^ s0 * (2 : ℝ)⁻¹ ^ i := by
  unfold scaleR
  rw [inv_pow, Nat.cast_pow, Nat.cast_ofNat, pow_sub₀ _ (by norm_num) hi]

theorem strokeLen_real {s0 m i : ℕ} (hi : i ≤ s0) :
    (strokeLen s0 m i : ℝ) = 2 ^ s0 * piHat m i := by
  unfold strokeLen piHat
  rw [Nat.cast_mul, scaleR_real hi, inv_pow]
  field_simp

theorem apexOffsetFrom_real {s0 m k : ℕ} (hk : 1 ≤ k) (hks : k ≤ s0) {S : Finset ℕ}
    (hS : S ⊆ Icc 1 (k - 1)) :
    (apexOffsetFrom s0 m 0 (k - 1) S : ℝ) = 2 ^ s0 * apexHat m k S := by
  unfold apexOffsetFrom apexHat
  have hI : Icc 0 (0 + (k - 1)) = range k := by ext x; simp only [mem_Icc, mem_range]; omega
  rw [hI]
  push_cast
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun i hi => scaleR_real (by simp at hi; omega)
  · exact Finset.sum_congr rfl fun i hi => strokeLen_real (by have := hS hi; simp at this; omega)

theorem valleyOffset_real {s0 m κ : ℕ} (hκ : 1 ≤ κ) (hκs : κ ≤ s0) {S : Finset ℕ}
    (hS : S ⊆ Icc 1 (κ - 1)) :
    ((apexOffsetFrom s0 m 0 (κ - 1) S + strokeLen s0 m κ : ℕ) : ℝ) = 2 ^ s0 * valleyHat m κ S := by
  push_cast
  rw [apexOffsetFrom_real hκ hκs hS, strokeLen_real hκs]
  unfold apexHat valleyHat; ring

theorem piHat_pos {m i : ℕ} : 0 < piHat m i := by unfold piHat; positivity

theorem piHat_zero (m : ℕ) : piHat m 0 = m + 1 := by simp [piHat]

theorem mul_tent_div {Λ w c : ℝ} (hΛ : 0 < Λ) :
    Λ * tent w (c / Λ) = max 0 (Λ * w - 2 * |c|) := by
  unfold tent
  rw [mul_max_of_nonneg _ _ hΛ.le, mul_zero, abs_div, abs_of_pos hΛ]
  congr 1
  field_simp

/-- **Lemma 7.4(b)**, direction `+`: `X⁺_{k,κ}(ξ) = M_k x_k((ξ + 1/2)/Λ)`, `M_k = 2^{k+1} Π_κ`. -/
theorem classStraddleCount_eq_profile {s0 m k κ : ℕ} (hk : 1 ≤ k) (hkκ : k < κ) (hκm : κ ≤ m)
    (hms : m < s0) (hpi : strokeLen s0 m κ ≤ scaleR s0 k) (ξ : ℕ) :
    (classStraddleCount s0 m k κ true ξ : ℝ) =
      (2 ^ (k + 1) * strokeLen s0 m κ : ℝ) * profile m k κ ((ξ + 1 / 2) / 2 ^ s0) := by
  set Λ : ℝ := 2 ^ s0 with hΛdef
  set N : ℝ := (m : ℝ) + 1 with hNdef
  set P := dnpPeriod s0 m with hPdef
  set t : ℝ := (ξ + 1 / 2) / Λ with htdef
  set w : ℝ := piHat m κ with hwdef
  have hΛ : 0 < Λ := by positivity
  have hN : 0 < N := by positivity
  have hw : 0 < w := piHat_pos
  have hPi0 : (strokeLen s0 m 0 : ℝ) = Λ * N := by
    rw [strokeLen_real (by omega), piHat_zero]
  have hP : (P : ℝ) = 4 * (Λ * N) := by
    rw [hPdef]; unfold dnpPeriod; push_cast; rw [hPi0]
  have hpiκ : (strokeLen s0 m κ : ℝ) = Λ * w := strokeLen_real (by omega)
  -- each straddle count is a scaled tent
  have hterm : ∀ c0 α : ℕ,
      ((straddleSet (c0 : ℤ) (α : ℤ) (strokeLen s0 m κ) (scaleR s0 k)).card : ℝ) =
        Λ * tent w (((c0 : ℝ) + 1 / 2 - α - strokeLen s0 m κ) / Λ) := by
    intro c0 α
    have h := congrArg (fun z : ℤ => (z : ℝ)) (card_straddleSet_eq (c0 := (c0 : ℤ)) (α := (α : ℤ)) hpi)
    simp only [Int.cast_natCast, Int.cast_max, Int.cast_zero, Int.cast_sub, Int.cast_abs,
      Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_one] at h
    rw [h, mul_tent_div hΛ, ← hpiκ]
    congr 2
    rw [show (2 : ℝ) * |(c0 : ℝ) + 1 / 2 - α - strokeLen s0 m κ| =
      |2 * ((c0 : ℝ) + 1 / 2 - α - strokeLen s0 m κ)| by rw [abs_mul, abs_two]]
    congr 1; ring
  -- the inner sum at a centre `c0 < P`
  have hinner : ∀ c0 : ℕ, c0 < P →
      ((totalStraddleAtCenter s0 m κ (scaleR s0 k) c0 : ℕ) : ℝ) =
        Λ * ∑ S' ∈ (Icc 1 (κ - 1)).powerset,
          perTent N w (((c0 : ℝ) + 1 / 2) / Λ - valleyHat m κ S') := by
    intro c0 hc0
    unfold totalStraddleAtCenter
    push_cast
    rw [sum_periodVApices (by omega) hκm hms.le, Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun S' hS' => ?_
    have hS'sub : S' ⊆ Icc 1 (κ - 1) := Finset.mem_powerset.mp hS'
    have hspan := forall_apexOffsetFrom hms.le (d := κ - 1) (i := 0) (by omega)
      (P := fun β => β + 2 * strokeLen s0 m (0 + 1 + (κ - 1)) ≤ strokeLen s0 m 0)
      (fun β hβ => (vApicesAux_span hms.le (κ - 1) 0 (by omega) β hβ).2) S' (by simpa using hS')
    rw [show 0 + 1 + (κ - 1) = κ by omega] at hspan
    have hv := valleyOffset_real (m := m) (by omega) (by omega : κ ≤ s0) hS'sub
    rw [← hΛdef] at hv
    push_cast at hv
    have hspanR : ((apexOffsetFrom s0 m 0 (κ - 1) S' : ℕ) : ℝ) + 2 * (strokeLen s0 m κ : ℝ) ≤
        (strokeLen s0 m 0 : ℝ) := by exact_mod_cast hspan
    have hc0R : (c0 : ℝ) + 1 ≤ P := by exact_mod_cast hc0
    have ha0 : (0 : ℝ) ≤ (apexOffsetFrom s0 m 0 (κ - 1) S' : ℕ) := Nat.cast_nonneg _
    rw [hP] at hc0R
    rw [perTent_eq_sum_four hN hw.le (by positivity) (by rw [div_lt_iff₀ hΛ]; nlinarith)
      (by rw [← mul_le_mul_iff_of_pos_left hΛ, show Λ * (2 * valleyHat m κ S') =
            2 * (Λ * valleyHat m κ S') by ring, ← hv]; nlinarith)
      (by rw [← mul_le_mul_iff_of_pos_left hΛ, show Λ * (2 * valleyHat m κ S' + w) =
            2 * (Λ * valleyHat m κ S') + Λ * w by ring, ← hv, ← hpiκ]; nlinarith)]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hterm]
    congr 2
    rw [div_eq_iff hΛ.ne', sub_mul, sub_mul, div_mul_cancel₀ _ hΛ.ne']
    push_cast
    rw [hPi0]
    linear_combination (-1 : ℝ) * hv
  -- the outer sum
  unfold classStraddleCount
  simp only [↓reduceIte]
  push_cast
  rw [sum_periodVApices hk (by omega) hms.le]
  have hP0 : 0 < P := by
    rw [hPdef]; unfold dnpPeriod; exact Nat.mul_pos (by norm_num) (strokeLen_pos _ _ _)
  have hcenter : ∀ q ∈ range 4, ∀ S ∈ (Icc 1 (k - 1)).powerset,
      ((totalStraddleAtCenter s0 m κ (scaleR s0 k)
        ((q * strokeLen s0 m 0 + apexOffsetFrom s0 m 0 (k - 1) S + ξ) % P) : ℕ) : ℝ) =
        Λ * ∑ S' ∈ (Icc 1 (κ - 1)).powerset, perTent N w (apexHat m k S + t - valleyHat m κ S') := by
    intro q _ S hS
    have hSsub : S ⊆ Icc 1 (k - 1) := Finset.mem_powerset.mp hS
    rw [hinner _ (Nat.mod_lt _ hP0)]
    congr 1
    refine Finset.sum_congr rfl fun S' _ => ?_
    set x := q * strokeLen s0 m 0 + apexOffsetFrom s0 m 0 (k - 1) S + ξ with hx
    obtain ⟨n, hn⟩ : ∃ n : ℕ, n = x / P := ⟨_, rfl⟩
    have hdm : ((x % P : ℕ) : ℝ) = x - P * n := by
      have := Nat.mod_add_div x P
      rw [← hn] at this
      have h' : ((x % P : ℕ) : ℝ) + P * (n : ℝ) = x := by exact_mod_cast this
      linarith
    have ha := apexOffsetFrom_real (m := m) hk (by omega : k ≤ s0) hSsub
    rw [← hΛdef] at ha
    have hxR : (x : ℝ) = q * (Λ * N) + Λ * apexHat m k S + ξ := by
      rw [hx]; push_cast; rw [hPi0, ha]
    rw [hdm, hxR, hP]
    have := perTent_add_int_mul N w (apexHat m k S + t - valleyHat m κ S') ((q : ℤ) - 4 * (n : ℤ))
    rw [← this]
    congr 1
    rw [htdef]
    push_cast
    field_simp
    ring
  rw [Finset.sum_congr rfl fun q hq => Finset.sum_congr rfl fun S hS => hcenter q hq S hS]
  rw [Finset.sum_const, card_range, ← Finset.mul_sum]
  have hprof : profile m k κ ((ξ + 1 / 2) / 2 ^ s0) = (2 ^ (k - 1) * w)⁻¹ *
      ∑ S ∈ (Icc 1 (k - 1)).powerset, ∑ S' ∈ (Icc 1 (κ - 1)).powerset,
        perTent N w (apexHat m k S + t - valleyHat m κ S') := rfl
  rw [hprof]
  generalize (∑ S ∈ (Icc 1 (k - 1)).powerset, ∑ S' ∈ (Icc 1 (κ - 1)).powerset,
    perTent N w (apexHat m k S + t - valleyHat m κ S')) = sumP
  rw [hpiκ, show k + 1 = (k - 1) + 2 by omega, pow_add, nsmul_eq_mul]
  field_simp
  ring

/-- **Lemma 7.4(b)**, direction `-`: `X⁻_{k,κ}(ξ) = X⁺_{k,κ}(P - ξ)` for `ξ ≤ P`. -/
theorem classStraddleCount_false_eq {s0 m k κ ξ : ℕ} (hξ : ξ ≤ dnpPeriod s0 m) :
    classStraddleCount s0 m k κ false ξ = classStraddleCount s0 m k κ true (dnpPeriod s0 m - ξ) := by
  unfold classStraddleCount
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Nat.add_sub_assoc hξ]

end MergeDepth
