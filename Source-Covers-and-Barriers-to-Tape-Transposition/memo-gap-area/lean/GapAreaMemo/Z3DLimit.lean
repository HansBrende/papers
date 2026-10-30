import GapAreaMemo.Z3DSharp

set_option autoImplicit false

/-!
# The dyadic sharpness geometry: limit form

The geometries `seq ν` (index `ν + 3`) carry the trivial computation, so they do not form a
near-full sequence. Their frozen gap areas and hop profiles are nevertheless defined exactly as
for one. Along every strictly increasing subsequence on which the normalized hop profiles
converge, the limits of Theorem G, taken in the same order, satisfy `G*_{R,2R+2} ≤ 10^7/R²` and
`τ_R ≥ 1/(32R)`; hence (GA) at `M = 2R+2` holds for every `R` once `β ≥ 10^9`.
-/

namespace SourceCovers.Z3D

open Finset Filter LeanMachine
open scoped Topology

/-- The sharpness sequence. -/
def seq (ν : ℕ) : Index := ⟨ν + 3, by omega⟩

theorem seq_large {φ : ℕ → ℕ} (hφ : StrictMono φ) (R : ℕ) :
    ∀ᶠ ν in atTop, 4 * R ≤ 2 ^ (seq (φ ν)).ν := by
  refine eventually_atTop.2 ⟨4 * R, fun ν hν => ?_⟩
  have h1 : ν ≤ φ ν := hφ.id_le ν
  have h2 : φ ν < 2 ^ φ ν := Nat.lt_two_pow_self
  have h3 : 2 ^ φ ν ≤ 2 ^ (seq (φ ν)).ν := Nat.pow_le_pow_right (by norm_num) (by simp [seq])
  omega

variable (β : ℝ) (hβ : 0 ≤ β)

/-- **Limit form of the sharpness theorem.** For every choice of hop orders, every strictly
increasing subsequence and every limit `h` of the normalized hop profiles along it, every `R ≥ 1`
and every modulus `M > R`, the limiting mean frozen point area is at most `10^7/R²`, and the hop
tail after `R` is at least `1/(32R)`. -/
theorem limit_form (O : ∀ ν, SortedCore (seq ν).core) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (h : ℕ → ℝ)
    (hh : ∀ i, Tendsto (fun ν => (O (φ ν)).hopProfile
      ((seq (φ ν)).geometry β hβ).inputLength i) atTop (𝓝 (h i)))
    {R M : ℕ} (hR : 1 ≤ R) (hRM : R < M) :
    limsup (fun J => limsup (fun ν => ((seq (φ ν)).geometry β hβ).prefixMeanGapArea (O (φ ν)) J R
        M (by omega)) atTop) atTop ≤ 10 ^ 7 / (R : ℝ) ^ 2 ∧
      1 / (32 * (R : ℝ)) ≤ ∑' i, h (i + R) := by
  constructor
  · -- the frozen gap area
    have hb : ∀ J ν, 0 ≤ ((seq (φ ν)).geometry β hβ).prefixMeanGapArea (O (φ ν)) J R
        M (by omega) ∧ ((seq (φ ν)).geometry β hβ).prefixMeanGapArea (O (φ ν)) J R
        M (by omega) ≤ 1 / 2 := fun J ν =>
      ((seq (φ ν)).geometry β hβ).prefixMeanGapArea_bounds (O (φ ν)) (by omega) hRM
    have hinner : ∀ J, R ≤ J → limsup (fun ν => ((seq (φ ν)).geometry β hβ).prefixMeanGapArea
        (O (φ ν)) J R M (by omega)) atTop ≤ 10 ^ 7 / (R : ℝ) ^ 2 := by
      intro J hJ
      apply limsup_le_of_le (IsCoboundedUnder.of_frequently_ge
        (Frequently.of_forall fun ν => (hb J ν).1))
      filter_upwards [seq_large hφ R] with ν hν
      exact (seq (φ ν)).gap_area_le β hβ hR hRM (by omega) (O (φ ν)) hJ
    have hnonneg : ∀ J, 0 ≤ limsup (fun ν => ((seq (φ ν)).geometry β hβ).prefixMeanGapArea
        (O (φ ν)) J R M (by omega)) atTop := fun J =>
      BoundedLimsup.limsup_nonneg (fun ν => (hb J ν).1) (fun ν => (hb J ν).2.trans (by norm_num))
    apply limsup_le_of_le (IsCoboundedUnder.of_frequently_ge
      (Frequently.of_forall hnonneg))
    exact eventually_atTop.2 ⟨R, hinner⟩
  · -- the hop tail
    have hmass : ∀ ν (s : Finset ℕ), ∑ i ∈ s, (O (φ ν)).hopProfile
        ((seq (φ ν)).geometry β hβ).inputLength i ≤ 128 := by
      intro ν s
      refine ((O (φ ν)).profile_mass_bounds ((seq (φ ν)).geometry β hβ).work_walk
        ((seq (φ ν)).geometry β hβ).core_coloring ((seq (φ ν)).geometry β hβ).x
        ((seq (φ ν)).geometry β hβ).inputLength_pos ((seq (φ ν)).geometry β hβ).raw_step ?_ s).1
      exact (seq (φ ν)).runtime_le
    obtain ⟨hh0, -, hsum, -⟩ := ProfileCompactness.limit_mass_of_finite_sums
      (fun ν i => (O (φ ν)).hopProfile_nonneg _ i) hmass hh
    have hlim := tendsto_finsetSum (Ico R (64 * R)) (fun i _ => hh i)
    have hfin : 1 / (32 * (R : ℝ)) ≤ ∑ i ∈ Ico R (64 * R), h i := by
      apply ge_of_tendsto hlim
      filter_upwards [seq_large hφ R] with ν hν
      have hL : ((seq (φ ν)).geometry β hβ).inputLength = (seq (φ ν)).L := (seq (φ ν)).L_eq.symm
      rw [hL]
      exact (seq (φ ν)).hop_tail_ge_of_le hR hν (O (φ ν)) (by omega)
    refine hfin.trans ?_
    rw [sum_Ico_eq_sum_range]
    have hs : Summable (fun i => h (i + R)) := (summable_nat_add_iff R).mpr hsum
    calc ∑ i ∈ range (64 * R - R), h (R + i) = ∑ i ∈ range (64 * R - R), h (i + R) := by
          simp only [add_comm]
      _ ≤ ∑' i, h (i + R) := hs.sum_le_tsum _ (fun i _ => hh0 (i + R))

/-- **The frozen gap-area condition (GA) holds in the limit** for `R ≥ 1` at every modulus `M`
with `32·10^7 (M - R) ≤ β R`; the right-hand side is that of `necessary_gap_area`. -/
theorem limit_GA (O : ∀ ν, SortedCore (seq ν).core) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (h : ℕ → ℝ)
    (hh : ∀ i, Tendsto (fun ν => (O (φ ν)).hopProfile
      ((seq (φ ν)).geometry β hβ).inputLength i) atTop (𝓝 (h i)))
    {R M : ℕ} (hR : 1 ≤ R) (hRM : R < M) (hβM : 32 * 10 ^ 7 * ((M - R : ℕ) : ℝ) ≤ β * R) :
    limsup (fun J => limsup (fun ν => ((seq (φ ν)).geometry β hβ).prefixMeanGapArea
        (O (φ ν)) J R M (by omega)) atTop) atTop ≤
      β * (∑' i, h (i + R)) / ((M - R : ℕ) : ℝ) := by
  obtain ⟨hgap, htail⟩ := limit_form β hβ O φ hφ h hh hR hRM
  refine hgap.trans ?_
  have hRr : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hD : (0 : ℝ) < ((M - R : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < M - R)
  rw [le_div_iff₀ hD]
  have h1 : β * (1 / (32 * (R : ℝ))) ≤ β * ∑' i, h (i + R) :=
    mul_le_mul_of_nonneg_left htail hβ
  have h2 : 10 ^ 7 / (R : ℝ) ^ 2 * ((M - R : ℕ) : ℝ) ≤ β * (1 / (32 * (R : ℝ))) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    field_simp
    nlinarith
  linarith

/-- **(GA) in the limit for `R = 0`** at every modulus `2 ≤ M ≤ β/16`. -/
theorem limit_GA_zero (O : ∀ ν, SortedCore (seq ν).core) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (h : ℕ → ℝ)
    (hh : ∀ i, Tendsto (fun ν => (O (φ ν)).hopProfile
      ((seq (φ ν)).geometry β hβ).inputLength i) atTop (𝓝 (h i)))
    {M : ℕ} (hM : 2 ≤ M) (hβM : 16 * (M : ℝ) ≤ β) :
    limsup (fun J => limsup (fun ν => ((seq (φ ν)).geometry β hβ).prefixMeanGapArea
        (O (φ ν)) J 0 M hM) atTop) atTop ≤ β * (∑' i, h (i + 0)) / ((M - 0 : ℕ) : ℝ) := by
  have hb : ∀ J ν, 0 ≤ ((seq (φ ν)).geometry β hβ).prefixMeanGapArea (O (φ ν)) J 0 M hM ∧
      ((seq (φ ν)).geometry β hβ).prefixMeanGapArea (O (φ ν)) J 0 M hM ≤ 1 / 2 := fun J ν =>
    ((seq (φ ν)).geometry β hβ).prefixMeanGapArea_bounds (O (φ ν)) hM (by omega)
  have hinner : ∀ J, limsup (fun ν => ((seq (φ ν)).geometry β hβ).prefixMeanGapArea
      (O (φ ν)) J 0 M hM) atTop ≤ 1 / 2 := fun J =>
    limsup_le_of_le (IsCoboundedUnder.of_frequently_ge
      (Frequently.of_forall fun ν => (hb J ν).1)) (Eventually.of_forall fun ν => (hb J ν).2)
  have hnonneg : ∀ J, 0 ≤ limsup (fun ν => ((seq (φ ν)).geometry β hβ).prefixMeanGapArea
      (O (φ ν)) J 0 M hM) atTop := fun J =>
    BoundedLimsup.limsup_nonneg (fun ν => (hb J ν).1) (fun ν => (hb J ν).2.trans (by norm_num))
  have hout : limsup (fun J => limsup (fun ν => ((seq (φ ν)).geometry β hβ).prefixMeanGapArea
      (O (φ ν)) J 0 M hM) atTop) atTop ≤ 1 / 2 :=
    limsup_le_of_le (IsCoboundedUnder.of_frequently_ge (Frequently.of_forall hnonneg))
      (Eventually.of_forall hinner)
  obtain ⟨-, htail⟩ := limit_form β hβ O φ hφ h hh (R := 1) (M := 2) le_rfl (by norm_num)
  have hmass : ∀ ν (s : Finset ℕ), ∑ i ∈ s, (O (φ ν)).hopProfile
      ((seq (φ ν)).geometry β hβ).inputLength i ≤ 128 := by
    intro ν s
    refine ((O (φ ν)).profile_mass_bounds ((seq (φ ν)).geometry β hβ).work_walk
      ((seq (φ ν)).geometry β hβ).core_coloring ((seq (φ ν)).geometry β hβ).x
      ((seq (φ ν)).geometry β hβ).inputLength_pos ((seq (φ ν)).geometry β hβ).raw_step ?_ s).1
    exact (seq (φ ν)).runtime_le
  obtain ⟨hh0, -, hsum, -⟩ := ProfileCompactness.limit_mass_of_finite_sums
    (fun ν i => (O (φ ν)).hopProfile_nonneg _ i) hmass hh
  have h01 : ∑' i, h (i + 1) ≤ ∑' i, h (i + 0) := by
    have e : ∑' i, h (i + 0) = h 0 + ∑' i, h (i + 1) := by
      simp only [add_zero]; exact hsum.tsum_eq_zero_add
    rw [e]; linarith [hh0 0]
  have ht1 : (1 : ℝ) / 32 ≤ ∑' i, h (i + 1) := by
    have := htail; norm_num at this; linarith
  have hτ : (1 : ℝ) / 32 ≤ ∑' i, h (i + 0) := le_trans ht1 h01
  have hMr : (2 : ℝ) ≤ ((M - 0 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ M - 0)
  calc _ ≤ (1 : ℝ) / 2 := hout
    _ ≤ β * (∑' i, h (i + 0)) / ((M - 0 : ℕ) : ℝ) := by
      rw [le_div_iff₀ (by linarith)]
      have := mul_le_mul_of_nonneg_left hτ hβ
      simp only [Nat.sub_zero] at hMr ⊢
      nlinarith

/-- **(GA) at `M = 2R+2` in the limit**, for every `R ≥ 0`, once `β ≥ 10^9`. -/
theorem limit_GA_default (β : ℝ) (hβ : 10 ^ 9 ≤ β) (O : ∀ ν, SortedCore (seq ν).core)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (h : ℕ → ℝ)
    (hh : ∀ i, Tendsto (fun ν => (O (φ ν)).hopProfile
      ((seq (φ ν)).geometry β (by linarith)).inputLength i) atTop (𝓝 (h i)))
    (R : ℕ) :
    limsup (fun J => limsup (fun ν => ((seq (φ ν)).geometry β (by linarith)).prefixMeanGapArea
        (O (φ ν)) J R (2 * R + 2) (by omega)) atTop) atTop ≤
      β * (∑' i, h (i + R)) / ((2 * R + 2 - R : ℕ) : ℝ) := by
  rcases Nat.eq_zero_or_pos R with rfl | hR
  · exact limit_GA_zero β (by linarith) O φ hφ h hh (M := 2) (by norm_num) (by norm_num; linarith)
  · have hRr : (1 : ℝ) ≤ R := by exact_mod_cast hR
    apply limit_GA β (by linarith) O φ hφ h hh hR (by omega)
    rw [show 2 * R + 2 - R = R + 2 by omega]
    push_cast
    nlinarith

end SourceCovers.Z3D
