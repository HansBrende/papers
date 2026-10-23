import BitWord.ScanTranspose
import BitWord.ScanThreshold

/-! The checked global record and actual interval geometry exclude the fixed
bounded-state scan grammar at every sufficiently large dyadic dimension. -/
namespace BitWord
open scoped BigOperators
open Classical
set_option autoImplicit false

namespace RawScanProgram
variable {d q L m : ℕ} {State : Type*} [Fintype State]

/-- Exact necessary finite inequality at one scale common to all layers and banks. -/
theorem exists_scale_transpose_bound (C : RawScanProgram (d*d) q L State)
    (s : ℕ) (hstate : Fintype.card State ≤ 2^s) (out : Fin q)
    (hc : C.Transposes out) (B : Fin m → ℕ) (hm : 0<m)
    (hsep : ∀ i j, i<j → Geometry.volume (B i) ≤ B j)
    (hB : ∀ i, 0<B i) (hdvd : ∀ i, B i ∣ d) :
    ∃ i : Fin m, (((d*d:ℕ):ℝ)-((11*q)^L:ℕ)*(d*d:ℕ)/(B i))/
      (((11*q)^L+1:ℕ):ℝ) ≤
      (q:ℝ)*L*(d*d:ℕ)/m+(s:ℝ)*L*(((d*d:ℕ):ℝ)/(B i)) := by
  obtain ⟨i,hi⟩ := C.exists_scale_badVolume hm B hsep
  have hb := C.transpose_bound_of_dvd (hB i) (hdvd i) s hstate out hc
  have hmr : (0:ℝ)<m := by exact_mod_cast hm
  have hi' : (C.badVolume (B i):ℝ) ≤ (q:ℝ)*L*(d*d:ℕ)/m := by
    apply (le_div_iff₀ hmr).mpr
    have h := hi
    exact_mod_cast (by simpa only [Nat.mul_comm] using h)
  have he : (0:ℝ)<(((11*q)^L+1:ℕ):ℝ) := by positivity
  have hnecessary : (((d*d:ℕ):ℝ)-((11*q)^L:ℕ)*(d*d:ℕ)/(B i))/
      (((11*q)^L+1:ℕ):ℝ) ≤
      (q:ℝ)*L*(d*d:ℕ)/m+(s:ℝ)*L*(((d*d:ℕ):ℝ)/(B i)) := by
    have hh : (((d*d:ℕ):ℝ)-((11*q)^L:ℕ)*(d*d:ℕ)/(B i))/
        (((11*q)^L+1:ℕ):ℝ) ≤
        C.badVolume (B i)+(s:ℝ)*L*(((d*d:ℕ):ℝ)/(B i)) :=
      (div_le_iff₀ he).mpr (by nlinarith only [hb])
    linarith
  exact ⟨i,hnecessary⟩

/-- Explicit finite exclusion, with publicly chosen separated bin scales. -/
theorem not_transposes_of_scales (C : RawScanProgram (d*d) q L State)
    (s : ℕ) (hstate : Fintype.card State ≤ 2^s) (out : Fin q)
    (B : Fin m → ℕ) (hm : 0<m)
    (hsep : ∀ i j, i<j → Geometry.volume (B i) ≤ B j)
    (hB : ∀ i, 0<B i) (hdvd : ∀ i, B i ∣ d) (hBd : ∀ i, B i ≤ d)
    (hD : ∀ i, 2*(11*q)^L ≤ B i)
    (hcost : 8*((11*q)^L+1)*q*L ≤ m)
    (hscan : ∀ i, 8*((11*q)^L+1)*s*L ≤ B i) : ¬ C.Transposes out := by
  intro hc
  obtain ⟨i,hnecessary⟩ := C.exists_scale_transpose_bound s hstate out hc B hm hsep hB hdvd
  have hBP : B i ≤ d*d := by
    have hd : 0<d := (hB i).trans_le (hBd i)
    nlinarith [hBd i]
  exact scan_threshold_contradiction (d*d) (B i) m q L s ((11*q)^L)
    (hB i) hm hBP (hD i) hcost (hscan i)
    (by simpa only [Nat.cast_add, Nat.cast_one] using hnecessary)

/-- A concrete dimension threshold, depending only on the fixed grammar resources. -/
def dimensionThreshold (q L s : ℕ) : ℕ :=
  scanScale (scanInitial s L ((11*q)^L)) (scanScaleCount q L ((11*q)^L))

/-- Every positive multiple of the fixed threshold is excluded. The public
stage and transition tables may vary arbitrarily with the chosen dimension. -/
theorem not_transposes_of_threshold_dvd
    (C : RawScanProgram (d*d) q L State)
    (s : ℕ) (hstate : Fintype.card State ≤ 2^s) (out : Fin q)
    (hd : 0 < d) (hdiv : dimensionThreshold q L s ∣ d) : ¬ C.Transposes out := by
  let D := (11*q)^L
  let m := scanScaleCount q L D
  let B₀ := scanInitial s L D
  let B : Fin m → ℕ := fun i => scanScale B₀ i.val
  have hm : 0<m := (scanScaleCount_bounds q L D).1
  have hzero : 0<B₀ := by have := scanInitial_bounds s L D; omega
  have hBthreshold (i : Fin m) : B i ≤ scanScale B₀ m :=
    (scanScale_strictMono hzero).monotone i.isLt.le
  have hBd (i : Fin m) : B i ∣ d := by
    apply dvd_trans _ hdiv
    obtain ⟨v,hv⟩ := scanScale_dyadic (scanInitialExponent s L D) m
    change scanScale B₀ m = 2^v at hv
    change B i ∣ scanScale B₀ m
    rw [hv]
    apply scanScale_dvd_dyadic
    change B i ≤ 2^v
    simpa only [hv] using hBthreshold i
  apply C.not_transposes_of_scales s hstate out B hm
  · intro i j hij
    exact scanScale_separated hzero hij
  · exact fun i => scanScale_pos hzero i.val
  · exact hBd
  · exact fun i => Nat.le_of_dvd hd (hBd i)
  · exact fun i => (scanScale_thresholds s L D i.val).1
  · exact (scanScaleCount_bounds q L D).2
  · exact fun i => (scanScale_thresholds s L D i.val).2.1

/-- No uniformly bounded-resource family in this grammar transposes all large
squares. This is the dyadic specialization of the positive-multiple exclusion. -/
theorem not_transposes_large_dyadic {h : ℕ}
    (C : RawScanProgram ((2^h)*(2^h)) q L State)
    (s : ℕ) (hstate : Fintype.card State ≤ 2^s) (out : Fin q)
    (hlarge : dimensionThreshold q L s ≤ 2^h) : ¬ C.Transposes out := by
  apply C.not_transposes_of_threshold_dvd s hstate out (Nat.pow_pos (by decide))
  exact scanScale_dvd_dyadic hlarge
end RawScanProgram
end BitWord
