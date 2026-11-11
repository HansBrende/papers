import AdaptiveTransfer.TransferCrossingLift
import NativeRelations.MacroscopicSkeleton

/-! Uniform numerical budgets for transporting macroscopic crossing cuts.
The constants are chosen before input length, horizon, demands and cuts.
No geometric connector or expansion conclusion is assumed here. -/

namespace AdaptiveTransfer.TransferCrossing
open Finset Filter Transpose MergeDepth NativeRelations

/-- A linear horizon and a macroscopic grid give a fixed bound for every
quantity whose product with the grid width is at most that horizon. -/
theorem scaled_count_le {P U H q : ℕ} {C θ : ℝ}
    (hP : 1 ≤ P) (hθ : 0 < θ)
    (hU : (U : ℝ) ≤ C * ((P : ℝ) + 1))
    (hH : θ * P ≤ 2 * (H : ℝ)) (hq : q * H ≤ U) :
    q ≤ ⌈4 * C / θ⌉₊ := by
  have hPr : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have hPpos : (0 : ℝ) < P := by linarith
  have hUr : (U : ℝ) ≤ 2 * C * P := by nlinarith
  have hqr : (q : ℝ) * H ≤ U := by exact_mod_cast hq
  have hh := mul_le_mul_of_nonneg_left hH (Nat.cast_nonneg q)
  have hprod : ((q : ℝ) * θ) * P ≤ (4 * C) * P := by nlinarith
  have hscale : (q : ℝ) * θ ≤ 4 * C := (mul_le_mul_iff_left₀ hPpos).mp hprod
  have hreal : (q : ℝ) ≤ ⌈4 * C / θ⌉₊ :=
    ((le_div_iff₀ hθ).mpr hscale).trans (Nat.le_ceil _)
  exact_mod_cast hreal

/-- Exact finite lift bills become a constant multiplicative charge plus
at most half the macroscopic expansion budget. The actual traces need only
their standard unit-speed/initial-position properties for the epoch count. -/
theorem exists_uniform_crossing_budgets (k s : ℕ) {C θ e α : ℝ}
    (hθ : 0 < θ) (he : 0 < e) (hα : 0 < α) :
    ∃ K A : ℕ, 0 < K ∧ 0 < A ∧ ∃ lam β : ℝ,
      0 < lam ∧ lam ≤ θ ∧ 0 < β ∧ β = e / (2 * A) ∧
      ∀ᶠ P : ℕ in atTop,
        1 ≤ ⌊lam * P⌋₊ ∧ ⌊lam * P⌋₊ ≤ ⌊θ * P⌋₊ ∧
        (crossingCutError k s K ⌊lam * P⌋₊ : ℝ) ≤ e * α * P / 2 ∧
        ∀ U : ℕ, (U : ℝ) ≤ C * ((P : ℝ) + 1) →
          crossingCutFactor k s U ⌊θ * P⌋₊ ≤ A ∧
          ∀ τ : Trace k, ∀ j : Fin k,
            (tapeSkeleton (τ.work j) U ⌊θ * P⌋₊).length + 1 ≤ K := by
  let K := ⌈4 * C / θ⌉₊ + 1
  let A := 4 * (10 * s + 1) + k * (6 * s + 1) + k * (6 * s + 3) * K + (2 * s - 1)
  let W := 4 * k * K ^ 2
  let F := W * (6 * s + 3) + (2 * s - 1)
  let lam := min θ (e * α / (8 * (W : ℝ) + 4))
  let β := e / (2 * (A : ℝ))
  have hK : 0 < K := by dsimp [K]; omega
  have hA : 0 < A := by dsimp [A]; omega
  have hlam : 0 < lam := lt_min hθ (div_pos (mul_pos he hα) (by positivity))
  have hlamθ : lam ≤ θ := min_le_left _ _
  have hβ : 0 < β := by dsimp [β]; positivity
  have hlambill : (8 * (W : ℝ) + 4) * lam ≤ e * α := by
    have hh := (le_div_iff₀ (show (0 : ℝ) < 8 * (W : ℝ) + 4 by positivity)).mp
      (min_le_right θ (e * α / (8 * (W : ℝ) + 4)))
    dsimp only [lam]
    nlinarith
  obtain ⟨P₀, hP₀⟩ := exists_nat_gt (max (1 : ℝ) (max (1 / lam) (4 * (F : ℝ) / (e * α))))
  refine ⟨K, A, hK, hA, lam, β, hlam, hlamθ, hβ, rfl, ?_⟩
  filter_upwards [eventually_ge_atTop P₀] with P hP₀P
  have hbig : max (1 : ℝ) (max (1 / lam) (4 * (F : ℝ) / (e * α))) ≤ P :=
    hP₀.le.trans (Nat.cast_le.mpr hP₀P)
  have hPr : (1 : ℝ) ≤ P := (le_max_left _ _).trans hbig
  have hP : 1 ≤ P := by exact_mod_cast hPr
  have hlamP : 1 ≤ lam * P := by
    have hh := (le_max_left _ _).trans ((le_max_right _ _).trans hbig)
    have hh' := (div_le_iff₀ hlam).mp hh
    nlinarith
  have hconst : (F : ℝ) ≤ e * α * P / 4 := by
    have hh := (le_max_right _ _).trans ((le_max_right _ _).trans hbig)
    have hh' := (div_le_iff₀ (mul_pos he hα)).mp hh
    nlinarith
  have hθP : 1 ≤ θ * P := hlamP.trans (mul_le_mul_of_nonneg_right hlamθ (Nat.cast_nonneg P))
  have hH : 1 ≤ ⌊θ * P⌋₊ := Nat.le_floor (by simpa only [Nat.cast_one] using hθP)
  have hHhalf : θ * P ≤ 2 * (⌊θ * P⌋₊ : ℝ) := by
    have hh := Nat.lt_floor_add_one (θ * P)
    have hHr : (1 : ℝ) ≤ ⌊θ * P⌋₊ := by exact_mod_cast hH
    linarith
  refine ⟨Nat.le_floor (by simpa only [Nat.cast_one] using hlamP),
    Nat.floor_mono (mul_le_mul_of_nonneg_right hlamθ (Nat.cast_nonneg P)), ?_, ?_⟩
  · have hh := Nat.floor_le (show 0 ≤ lam * (P : ℝ) by positivity)
    have hcoeff : 2 * (W : ℝ) * lam ≤ e * α / 4 := by nlinarith
    have hlinear := mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg P)
    have hfloor := mul_le_mul_of_nonneg_left hh (show 0 ≤ 2 * (W : ℝ) by positivity)
    have herror : (crossingCutError k s K ⌊lam * P⌋₊ : ℝ) =
        2 * (W : ℝ) * ⌊lam * P⌋₊ + F := by
      simp only [crossingCutError, F, W, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
      ring
    rw [herror]
    nlinarith
  · intro U hU
    have hpack : (U - 1) / (4 * ⌊θ * P⌋₊ + 2) ≤ K := by
      apply le_trans (scaled_count_le hP hθ hU hHhalf ?_) (Nat.le_succ _)
      calc
        _ ≤ ((U - 1) / (4 * ⌊θ * P⌋₊ + 2)) * (4 * ⌊θ * P⌋₊ + 2) :=
          Nat.mul_le_mul_left _ (by omega)
        _ ≤ U - 1 := Nat.div_mul_le_self _ _
        _ ≤ U := Nat.sub_le _ _
    refine ⟨?_, fun τ j => ?_⟩
    · dsimp only [crossingCutFactor, A]
      gcongr
    · have hh := scaled_count_le hP hθ hU hHhalf
        (tapeSkeleton_length_mul_le (τ.work_isWalk j) (τ.work_zero j) U hH)
      exact Nat.add_le_add_right hh 1

/-- The additive discard costs half the available expansion, leaving an
explicit positive linear lower bound on the original cut. -/
theorem expansion_after_transport {A : ℕ} {e α P V B F : ℝ}
    (hA : 0 < A) (he : 0 ≤ e) (hV : α * P ≤ V)
    (hbill : e * V ≤ A * B + F) (hF : F ≤ e * α * P / 2) :
    (e / (2 * A)) * V ≤ B := by
  have hcost := mul_le_mul_of_nonneg_left hV he
  have hAr : (0 : ℝ) < A := by exact_mod_cast hA
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * A)]
  nlinarith

end AdaptiveTransfer.TransferCrossing
