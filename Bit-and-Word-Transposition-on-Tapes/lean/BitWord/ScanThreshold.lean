import BitWord.GeometryScales
import Mathlib.Data.Nat.Log

namespace BitWord

/-- Scalar contradiction used after the actual program/helper bounds.
The positive lower bound is twice the permitted upper bound. -/
theorem scan_scalar_contradiction {P B m e a c D : ℝ}
    (hB : 0 < B) (hm : 0 < m) (he : 0 < e)
    (hPB : B ≤ P) (hD : 2*D ≤ B) (hcost : 8*e*a ≤ m)
    (hstate : 8*e*c ≤ B)
    (hnecessary : (P-D*P/B)/e ≤ a*P/m+c*(P/B)) : False := by
  have hP : 0 < P := hB.trans_le hPB
  have he8 : 0 < 8*e := by positivity
  have he2 : 0 < 2*e := by positivity
  have he4 : 0 < 4*e := by positivity
  have hbad : a*P/m ≤ P/(8*e) := by
    apply (div_le_div_iff₀ hm he8).mpr
    nlinarith
  have hscan : c*(P/B) ≤ P/(8*e) := by
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ hB he8).mpr
    nlinarith
  have hmiss : D*P/B ≤ P/2 := by
    apply (div_le_iff₀ hB).mpr
    nlinarith
  have hlow : P/(2*e) ≤ (P-D*P/B)/e := by
    apply (div_le_div_iff₀ he2 he).mpr
    nlinarith
  have hupper : a*P/m+c*(P/B) ≤ P/(4*e) := by
    calc
      _ ≤ P/(8*e)+P/(8*e) := add_le_add hbad hscan
      _ = _ := by ring
  have hstrict : P/(4*e) < P/(2*e) := by
    apply (div_lt_div_iff₀ he4 he2).mpr
    nlinarith
  linarith

/-- The explicit natural thresholds in the scan theorem are sufficient. -/
theorem scan_threshold_contradiction (P B m q L s D : ℕ)
    (hB : 0 < B) (hm : 0 < m) (hPB : B ≤ P)
    (hD : 2*D ≤ B) (hcost : 8*(D+1)*q*L ≤ m)
    (hstate : 8*(D+1)*s*L ≤ B)
    (hnecessary : ((P:ℝ)-D*P/B)/((D:ℝ)+1) ≤
      (q:ℝ)*L*P/m+(s:ℝ)*L*((P:ℝ)/B)) : False := by
  apply scan_scalar_contradiction (a := (q:ℝ)*L) (c := (s:ℝ)*L)
    (D := D) (by exact_mod_cast hB) (by exact_mod_cast hm)
    (by positivity) (by exact_mod_cast hPB)
    (by exact_mod_cast hD) _ _ hnecessary
  · exact_mod_cast (by simpa only [Nat.mul_assoc] using hcost)
  · exact_mod_cast (by simpa only [Nat.mul_assoc] using hstate)

/-- Public dyadic scales, used only in the mathematical lower bound. -/
def scanScale (B₀ : ℕ) : ℕ → ℕ
  | 0 => B₀
  | i+1 => Geometry.volume (scanScale B₀ i)

theorem scanScale_pos {B₀ : ℕ} (hB : 0 < B₀) (i : ℕ) : 0 < scanScale B₀ i := by
  induction i with
  | zero => exact hB
  | succ i ih => exact Nat.mul_pos ih (Nat.pow_pos (by decide))

theorem scanScale_strictMono {B₀ : ℕ} (hB : 0 < B₀) : StrictMono (scanScale B₀) := by
  apply strictMono_nat_of_lt_succ
  intro i
  have hi := scanScale_pos hB i
  have hp : 1 < 4 ^ scanScale B₀ i := Nat.one_lt_pow (by omega) (by decide)
  change scanScale B₀ i < scanScale B₀ i * 4^scanScale B₀ i
  nlinarith

theorem scanScale_separated {B₀ : ℕ} (hB : 0 < B₀) {i j : ℕ} (hij : i < j) :
    Geometry.volume (scanScale B₀ i) ≤ scanScale B₀ j :=
  (scanScale_strictMono hB).monotone (by omega : i+1 ≤ j)

theorem scanScale_dyadic (u i : ℕ) : ∃ v, scanScale (2^u) i = 2^v := by
  induction i with
  | zero => exact ⟨u,rfl⟩
  | succ i ih =>
    obtain ⟨v,hv⟩ := ih
    refine ⟨v+2*2^v,?_⟩
    simp only [scanScale, Geometry.volume, hv]
    rw [pow_add, pow_mul]
    rfl

/-- Number of scales sufficient for the bad-volume average. -/
def scanScaleCount (q L D : ℕ) := max 1 (8*(D+1)*q*L)

/-- A dyadic first scale meeting all explicit scalar thresholds. -/
def scanInitialExponent (s L D : ℕ) :=
  Nat.clog 2 (max (2*D) (max (8*(D+1)*s*L) 2))

def scanInitial (s L D : ℕ) := 2 ^ scanInitialExponent s L D

theorem scanInitial_bounds (s L D : ℕ) :
    2*D ≤ scanInitial s L D ∧ 8*(D+1)*s*L ≤ scanInitial s L D ∧
      2 ≤ scanInitial s L D := by
  have hh := Nat.le_pow_clog (b := 2) (by decide)
    (max (2*D) (max (8*(D+1)*s*L) 2))
  change max (2*D) (max (8*(D+1)*s*L) 2) ≤ scanInitial s L D at hh
  omega

theorem scanScaleCount_bounds (q L D : ℕ) :
    0 < scanScaleCount q L D ∧ 8*(D+1)*q*L ≤ scanScaleCount q L D := by
  unfold scanScaleCount
  omega

theorem scanScale_initial_le (s L D i : ℕ) :
    scanInitial s L D ≤ scanScale (scanInitial s L D) i := by
  have hp : 0 < scanInitial s L D := by have := scanInitial_bounds s L D; omega
  exact (scanScale_strictMono hp).monotone (Nat.zero_le i)

theorem scanScale_thresholds (s L D i : ℕ) :
    2*D ≤ scanScale (scanInitial s L D) i ∧
    8*(D+1)*s*L ≤ scanScale (scanInitial s L D) i ∧
    2 ≤ scanScale (scanInitial s L D) i := by
  have := scanScale_initial_le s L D i
  have := scanInitial_bounds s L D
  omega

/-- Every chosen scale divides every sufficiently large dyadic dimension. -/
theorem scanScale_dvd_dyadic {u i h : ℕ} (hh : scanScale (2^u) i ≤ 2^h) :
    scanScale (2^u) i ∣ 2^h := by
  obtain ⟨v,hv⟩ := scanScale_dyadic u i
  rw [hv] at hh ⊢
  exact pow_dvd_pow 2 ((Nat.pow_le_pow_iff_right (by decide)).mp hh)

end BitWord
