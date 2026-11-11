import SharedDecoders.CapacityClosureIteration
import SharedDecoders.CapacityMeans
import Mathlib.Analysis.SpecificLimits.Basic

/-! The actual isolation certificates and a finite doubling telescope. -/

namespace SharedDecoders.CapacityClosure

open Module CapacityIntervals CapacityRuns
open scoped BigOperators

variable {d b : ℕ} [NeZero d]

theorem residual_step_bound {p : ZMod d → Bool} {L : Submodule Bit (BinaryState d b)}
    (hL : IsSharedCode Bit p L) {S : Finset (ZMod d)} (hs : L ≤ rowSpace S)
    (s : ZMod d) :
    10 * finrank Bit L + 2*(d*b)*changeCount p (2 • s) ≤
      5*(d*b)*S.card + (d*b)*d + 2*(d*b)*changeCount p s +
      7*(d*b)*Nat.gcd d s.val + 26*defect L := by
  obtain ⟨hone, htwo⟩ := residual_certificates hL hs s
  have h₁ := Nat.mul_le_mul_left (d*b) (isolatedCount_first_shift p s)
  have h₂ := Nat.mul_le_mul_left (d*b) (isolatedCount_second_shift p s)
  have hweak : changeCount p s + runCount p s 2 + 2*runCount p s 4 ≤ d := by
    have hh := weighted_run_budget p s
    rw [ZMod.card] at hh
    omega
  have hrun := Nat.mul_le_mul_left (d*b) hweak
  have hdouble := congrArg (fun n => d*b*n) (changeCount_double p s)
  nlinarith only [hone, htwo, h₁, h₂, hrun, hdouble]

/-- The exact finite error. The power form equals `2^(R/2)` over the reals. -/
noncomputable def error (d R : ℕ) : ℝ :=
  (d : ℝ)/(10*R) + (7*Real.sqrt d)/(5*R) *
    (((Real.sqrt 2)^R-1)/(Real.sqrt 2-1))

omit [NeZero d] in
theorem finite_doubling_telescope (a g : ℕ → ℝ) (D v A rho : ℝ) (R : ℕ)
    (hR : 0 < R) (hv : 0 ≤ v) (ha : ∀ r, 0 ≤ a r)
    (ha₀ : a 0 ≤ (d : ℝ)/2)
    (hg : ∀ r, g r ≤ 2*Real.sqrt d*(Real.sqrt 2)^r)
    (hstep : ∀ r, D ≤ v*(A/2+(d : ℝ)/10+(a r-a (r+1))/5+7*g r/10)+13*rho/5) :
    D ≤ v*(A/2+(d : ℝ)/10+error d R)+13*rho/5 := by
  have ht (n : ℕ) :
      (n : ℝ)*(D-v*(A/2+(d : ℝ)/10)-13*rho/5) ≤
        v*((a 0-a n)/5+7/10*(∑ r ∈ Finset.range n, g r)) := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hh := hstep n
      rw [Nat.cast_add, Nat.cast_one, Finset.sum_range_succ]
      nlinarith only [ih, hh]
  have hs := Finset.sum_le_sum (s := Finset.range R) (fun r _ => hg r)
  rw [← Finset.mul_sum] at hs
  have hroot : Real.sqrt 2 ≠ 1 := by
    have hh := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    intro he; rw [he] at hh; norm_num at hh
  have hgeom : (∑ r ∈ Finset.range R, (Real.sqrt 2)^r) =
      ((Real.sqrt 2)^R-1)/(Real.sqrt 2-1) := geom_sum_eq hroot R
  rw [hgeom] at hs
  have htot := ht R
  have hsum := mul_le_mul_of_nonneg_left hs (show 0 ≤ v*(7/10) by positivity)
  have hinit := mul_le_mul_of_nonneg_left ha₀ (show 0 ≤ v/5 by positivity)
  have htail := mul_nonneg hv (ha R)
  have hRp : (0 : ℝ) < R := by exact_mod_cast hR
  have hcalc : (R : ℝ)*(v*(A/2+(d : ℝ)/10+error d R)+13*rho/5) =
      (R : ℝ)*(v*(A/2+(d : ℝ)/10)+13*rho/5) +
        v*((d : ℝ)/10+7/5*Real.sqrt d*(((Real.sqrt 2)^R-1)/(Real.sqrt 2-1))) := by
    dsimp [error]
    field_simp [ne_of_gt hRp, sub_ne_zero.mpr hroot]
    ring
  apply (le_of_mul_le_mul_left (a := (R : ℝ)) ?_ hRp)
  rw [hcalc]
  nlinarith only [htot, hsum, hinit, htail]

theorem residual_finite_bound {p : ZMod d → Bool} {L : Submodule Bit (BinaryState d b)}
    (hL : IsSharedCode Bit p L) {S : Finset (ZMod d)} (hs : L ≤ rowSpace S)
    (R : ℕ) (hR : 0 < R) :
    (finrank Bit L : ℝ) ≤ (d*b : ℕ)*((S.card : ℝ)/2+(d : ℝ)/10+error d R)+
      13/5*(defect L : ℝ) := by
  let a (r : ℕ) : ℝ := (∑ s : ZMod d, (changeCount p ((2^r) • s) : ℝ))/d
  let g (r : ℕ) : ℝ := (∑ s : ZMod d, (Nat.gcd d ((2^r) • s).val : ℝ))/d
  have hd : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  have ha : ∀ r, 0 ≤ a r := by intro r; dsimp [a]; positivity
  have ha₀ : a 0 ≤ (d : ℝ)/2 := by
    simpa only [a, pow_zero, one_nsmul] using mean_changeCount_le p
  have hg : ∀ r, g r ≤ 2*Real.sqrt d*(Real.sqrt 2)^r := fun r =>
    mean_doubled_gcd_zmod_le r
  have hstep (r : ℕ) :
      (finrank Bit L : ℝ) ≤ (d*b : ℕ)*((S.card : ℝ)/2+(d : ℝ)/10+
        (a r-a (r+1))/5+7*g r/10)+13*(defect L : ℝ)/5 := by
    have hlocal (s : ZMod d) :
        (finrank Bit L : ℝ) ≤ (d*b : ℕ)*((S.card : ℝ)/2+(d : ℝ)/10+
        ((changeCount p s : ℝ)-changeCount p (2 • s))/5+
        7*(Nat.gcd d s.val : ℝ)/10)+13*(defect L : ℝ)/5 := by
      have hh := (Nat.cast_le (α := ℝ)).2 (residual_step_bound hL hs s)
      push_cast at hh ⊢
      nlinarith only [hh]
    have hn (s : ZMod d) : 2 • ((2^r) • s) = (2^(r+1)) • s := by
      rw [← mul_nsmul, pow_succ]
    have hh := Finset.sum_le_sum (s := Finset.univ)
      (fun s _ => hlocal ((2^r) • s))
    have real_nsmul (n : ℕ) (x : ℝ) : n • x = (n : ℝ)*x := nsmul_eq_mul n x
    simp only [hn, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.sum_div, Finset.sum_const, Finset.card_univ,
      ZMod.card, real_nsmul] at hh
    dsimp [a,g]
    apply (le_of_mul_le_mul_left (a := (d : ℝ)) ?_ hd)
    field_simp
    nlinarith only [hh, hd]
  convert finite_doubling_telescope a g (finrank Bit L) (d*b : ℕ) S.card (defect L)
    R hR (by positivity) ha ha₀ hg hstep using 1
  ring

end SharedDecoders.CapacityClosure
