import TransposeFollowup.ClippedAffineRamps

/-! A straight outward bank scan, stationary cleanup pause, and rewind.
The local buffer is approximated by a stationary head. -/
namespace TransposeFollowup.RowBankCurve
open AffineMotion
set_option autoImplicit false

noncomputable def curve (P W : ℕ) (h : Fin 2) (t : ℝ) : ℝ :=
  if h=0 then clippedRamp P 0 7 t-clippedRamp P (7*P+2*W : ℕ) 1 t else 0

theorem cover (P W : ℕ) {H : ℝ} (hH : 0≤H) (h : Fin 2) :
    HasAffineIntervalCover 9 (curve P W h) H := by
  change HasAffineIntervalCover 9 (fun x => curve P W h x) H
  by_cases hh : h=0
  · simp only [curve,ite_eq_left hh]
    exact (clippedRamp_cover hH (Nat.cast_nonneg P) le_rfl (by norm_num)).sub
      (clippedRamp_cover hH (Nat.cast_nonneg P) (Nat.cast_nonneg _) (by norm_num))
  · simp only [curve,ite_eq_right hh]
    exact (HasAffineIntervalCover.const hH 0).mono (by norm_num) (by norm_num)

theorem before (P W n : ℕ) (hn : n≤7*P) (h : Fin 2) :
    curve P W h n=if h=0 then (n : ℝ)/7 else 0 := by
  have hn' : (n : ℝ)≤7*P := by exact_mod_cast hn
  have ha : clippedRamp P 0 7 n=(n : ℝ)/7 := by
    rw [clippedRamp,sub_zero,max_eq_left (by positivity),min_eq_left (by linarith)]
  have hb : clippedRamp P (7*P+2*W : ℕ) 1 n=0 := by
    simp only [clippedRamp,div_one,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
    rw [max_eq_right (by nlinarith [Nat.cast_nonneg (α:=ℝ) W]),min_eq_left (Nat.cast_nonneg P)]
  simp only [curve,ha,hb,sub_zero]

theorem cleanup (P W n : ℕ) (hn : n≤2*W+P) (h : Fin 2) :
    curve P W h (7*P+n : ℕ)=if h=0 then (P : ℝ)-(n-2*W : ℕ) else 0 := by
  have ha : clippedRamp P 0 7 (7*P+n : ℕ)=(P : ℝ) := by
    have hl : (P : ℝ)≤(7*P+n : ℕ)/7 := by push_cast; nlinarith [Nat.cast_nonneg (α:=ℝ) n]
    rw [clippedRamp,sub_zero,max_eq_left ((Nat.cast_nonneg P).trans hl),min_eq_right hl]
  have hb : clippedRamp P (7*P+2*W : ℕ) 1 (7*P+n : ℕ)=(n-2*W : ℕ) := by
    by_cases h : 2*W≤n
    · have he : ((7*P+n : ℕ) : ℝ)-(7*P+2*W : ℕ)=(n-2*W : ℕ) := by
        rw [Nat.cast_sub h]
        push_cast
        ring
      have hu : n-2*W≤P := by omega
      rw [clippedRamp,div_one,he,max_eq_left (Nat.cast_nonneg _),min_eq_left (by exact_mod_cast hu)]
    · have he : n-2*W=0 := by omega
      have hl : ((7*P+n : ℕ) : ℝ)-(7*P+2*W : ℕ)≤0 := by
        have hh : n≤2*W := by omega
        exact_mod_cast (show (7*P+n : ℤ)-(7*P+2*W : ℕ)≤0 by omega)
      rw [clippedRamp,div_one,max_eq_right hl,min_eq_left (Nat.cast_nonneg P),he,Nat.cast_zero]
  simp only [curve,ha,hb]

theorem after (P W n : ℕ) (hn : 8*P+2*W≤n) (h : Fin 2) : curve P W h n=0 := by
  have ha : clippedRamp P 0 7 n=(P : ℝ) := by
    have hl : (P : ℝ)≤(n : ℝ)/7 := by
      have hh : 7*P≤n := by omega
      have hr : (7 : ℝ)*P≤n := by exact_mod_cast hh
      linarith
    rw [clippedRamp,sub_zero,max_eq_left ((Nat.cast_nonneg P).trans hl),min_eq_right hl]
  have hb : clippedRamp P (7*P+2*W : ℕ) 1 n=(P : ℝ) := by
    have hl : (P : ℝ)≤(n : ℝ)-(7*P+2*W : ℕ) := by
      have hr : (8 : ℝ)*P+2*W≤n := by exact_mod_cast hn
      push_cast
      linarith
    rw [clippedRamp,div_one,max_eq_left ((Nat.cast_nonneg P).trans hl),min_eq_right hl]
  simp only [curve,ha,hb,sub_self,ite_self]

theorem sample_stability (P W : ℕ) (h : Fin 2) (x : ℝ) :
    |curve P W h (⌊x⌋₊ : ℕ)-curve P W h x|≤4 := by
  have ha := clippedRamp_sample_error P 0 7 x
  have hb := clippedRamp_sample_error P 0 7 (⌊x⌋₊ : ℕ)
  have hc := clippedRamp_sample_error P (7*P+2*W) 1 x
  have hd := clippedRamp_sample_error P (7*P+2*W) 1 (⌊x⌋₊ : ℕ)
  simp only [Nat.floor_natCast] at hb hd
  by_cases hh : h=0
  · simp only [curve,ite_eq_left hh]
    rw [abs_le] at ha hb hc hd ⊢
    constructor <;> linarith
  · simp [curve,hh]

end TransposeFollowup.RowBankCurve
