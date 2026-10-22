import TransposeFollowup.SL2DiagonalRescale
import TransposeFollowup.SL2UpperApproximation
import TransposeFollowup.SL2BicommutatorError

/-! Small off-diagonal products in a finite family and its two-factor
products force small bicommutator trace tests. The contrapositive gives
an explicit escape estimate without any condition-number assumption. -/
namespace TransposeFollowup.SL2Escape
open Classical Matrix
open scoped commutatorElement
set_option autoImplicit false
local notation "G" => Matrix.SpecialLinearGroup (Fin 2) ℂ
local notation "M" => Matrix (Fin 2) (Fin 2) ℂ

theorem finite_family_trace_bound (S : Finset G) {T ε : ℝ}
    (hT : 0 ≤ T) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2) (hsmall : 16 * (T + 2) ^ 4 * ε ≤ 1)
    (htr : ∀ g ∈ S, ‖Matrix.trace (g : M)‖ ≤ T)
    (hbc : ∀ g ∈ S, ‖g 0 1 * g 1 0‖ ≤ ε)
    (hprod : ∀ g ∈ S, ∀ h ∈ S, ‖(g * h) 0 1 * (g * h) 1 0‖ ≤ ε)
    {a x y g : G} (ha : a ∈ S) (hx : x ∈ S) (hy : y ∈ S) (hg : g ∈ S) :
    ‖Matrix.trace ((⁅⁅a, x⁆, ⁅a, y⁆⁆ * g : G) : M) - Matrix.trace (g : M)‖ ≤
      (2 : ℝ) ^ 43 * (T + 2) ^ 21 * ε := by
  by_cases hn : ∃ u ∈ S, u 0 1 ≠ 0
  · obtain ⟨z, hz, hdata⟩ := finite_family_rescaled_lower_bound S hT hε0 hε htr hbc hprod hn
    let e := diagonalRescale z hz
    have hap (u : G) (hu : u ∈ S) :
        ∃ u' : G, u' 1 0 = 0 ∧ EntryApprox (2 * (T + 2)) (16 * (T + 2) ^ 4 * ε) (e u) u' := by
      have hd := hdata u hu
      exact exists_upper_approximation (by linarith) hε0 hd.1 hd.2.1 hd.2.2.1
        hd.2.2.2.1 hd.2.2.2.2
        (by simpa only [e, diagonalRescale_offDiagonal] using hbc u hu) hsmall
    obtain ⟨a', ha'zero, ha'⟩ := hap a ha
    obtain ⟨x', hx'zero, hx'⟩ := hap x hx
    obtain ⟨y', hy'zero, hy'⟩ := hap y hy
    obtain ⟨g', _, hg'⟩ := hap g hg
    have hh := bicommutator_trace_error (g := e g) (by linarith) (by positivity)
      ha' hx' hy' ha'zero hx'zero hy'zero hg'.1
    calc
      _ = ‖Matrix.trace ((⁅⁅e a, e x⁆, ⁅e a, e y⁆⁆ * e g : G) : M) - Matrix.trace (e g : M)‖ := by
        rw [← diagonalRescale_trace z hz (⁅⁅a, x⁆, ⁅a, y⁆⁆ * g), ← diagonalRescale_trace z hz g]
        simp only [e, map_mul, map_commutatorElement]
      _ ≤ 64 * (2 * (T + 2)) * (2 * (2 * (T + 2))) ^ 16 * (16 * (T + 2) ^ 4 * ε) := hh
      _ = _ := by ring
  · have hz (u : G) (hu : u ∈ S) : u 0 1 = 0 := by
      by_contra h
      exact hn ⟨u, hu, h⟩
    rw [lower_bicommutator_eq_one (hz a ha) (hz x hx) (hz y hy), one_mul, sub_self, norm_zero]
    positivity

theorem offDiagonal_escape_of_trace_gap (S : Finset G) {T L : ℝ}
    (hT : 0 ≤ T) (hL : 0 < L) (htr : ∀ g ∈ S, ‖Matrix.trace (g : M)‖ ≤ T)
    {a x y g : G} (ha : a ∈ S) (hx : x ∈ S) (hy : y ∈ S) (hg : g ∈ S)
    (hgap : L ≤ ‖Matrix.trace ((⁅⁅a, x⁆, ⁅a, y⁆⁆ * g : G) : M) - Matrix.trace (g : M)‖) :
    ∃ h : G, (h ∈ S ∨ ∃ u ∈ S, ∃ v ∈ S, u * v = h) ∧
      min (1 / (32 * (T + 2) ^ 4)) (L / ((2 : ℝ) ^ 44 * (T + 2) ^ 21)) ≤
        ‖h 0 1 * h 1 0‖ := by
  let ε := min (1 / (32 * (T + 2) ^ 4)) (L / ((2 : ℝ) ^ 44 * (T + 2) ^ 21))
  have hpos : 0 < ε := by dsimp [ε]; positivity
  have hl : ε ≤ 1 / (32 * (T + 2) ^ 4) := min_le_left _ _
  have hr : ε ≤ L / ((2 : ℝ) ^ 44 * (T + 2) ^ 21) := min_le_right _ _
  have hM4 : 1 ≤ (T + 2) ^ 4 := one_le_pow₀ (by linarith)
  have hε : ε ≤ 1 / 2 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 32 * (T + 2) ^ 4)).mp hl
    nlinarith [mul_le_mul_of_nonneg_left hM4 hpos.le]
  have hsmall : 16 * (T + 2) ^ 4 * ε ≤ 1 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 32 * (T + 2) ^ 4)).mp hl
    nlinarith
  by_contra hn
  have hbc : ∀ u ∈ S, ‖u 0 1 * u 1 0‖ ≤ ε := by
    intro u hu
    exact le_of_lt (lt_of_not_ge (fun he => hn ⟨u, Or.inl hu, he⟩))
  have hprod : ∀ u ∈ S, ∀ v ∈ S, ‖(u * v) 0 1 * (u * v) 1 0‖ ≤ ε := by
    intro u hu v hv
    exact le_of_lt (lt_of_not_ge (fun he => hn ⟨u * v, Or.inr ⟨u, hu, v, hv, rfl⟩, he⟩))
  have hbound := finite_family_trace_bound S hT hpos.le hε hsmall htr hbc hprod ha hx hy hg
  have hc := (le_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ 44 * (T + 2) ^ 21)).mp hr
  norm_num only [show (2 : ℝ) ^ 44 = 2 * (2 : ℝ) ^ 43 by norm_num] at hc
  nlinarith

end TransposeFollowup.SL2Escape
