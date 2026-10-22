import TransposeFollowup.SL2OffDiagonalBounds

/-! Exact diagonal rescaling on SL2 and normalization of a finite family.
No bound on the rescaling parameter is assumed. -/
namespace TransposeFollowup.SL2Escape
open Classical Matrix
set_option autoImplicit false

variable {K : Type*} [Field K]

def diagonalRescale (z : K) (hz : z ≠ 0) :
    Matrix.SpecialLinearGroup (Fin 2) K →* Matrix.SpecialLinearGroup (Fin 2) K where
  toFun g := ⟨!![g 0 0, g 0 1 / z; z * g 1 0, g 1 1], by
    simp only [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    have hd : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
      simpa only [Matrix.det_fin_two] using g.property
    field_simp
    exact hd⟩
  map_one' := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' g h := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    change (!![((g : Matrix (Fin 2) (Fin 2) K) * (h : Matrix (Fin 2) (Fin 2) K)) 0 0,
        ((g : Matrix (Fin 2) (Fin 2) K) * (h : Matrix (Fin 2) (Fin 2) K)) 0 1 / z;
        z * ((g : Matrix (Fin 2) (Fin 2) K) * (h : Matrix (Fin 2) (Fin 2) K)) 1 0,
        ((g : Matrix (Fin 2) (Fin 2) K) * (h : Matrix (Fin 2) (Fin 2) K)) 1 1] :
      Matrix (Fin 2) (Fin 2) K) i j =
      ((!![g 0 0, g 0 1 / z; z * g 1 0, g 1 1] : Matrix (Fin 2) (Fin 2) K) *
        !![h 0 0, h 0 1 / z; z * h 1 0, h 1 1]) i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp

local notation "G" => Matrix.SpecialLinearGroup (Fin 2) ℂ
local notation "M" => Matrix (Fin 2) (Fin 2) ℂ

theorem diagonalRescale_trace (z : ℂ) (hz : z ≠ 0) (g : G) :
    Matrix.trace (diagonalRescale z hz g : M) = Matrix.trace (g : M) := by
  simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_two]
  rfl

theorem diagonalRescale_offDiagonal (z : ℂ) (hz : z ≠ 0) (g : G) :
    diagonalRescale z hz g 0 1 * diagonalRescale z hz g 1 0 = g 0 1 * g 1 0 := by
  change g 0 1 / z * (z * g 1 0) = _
  field_simp

theorem exists_diagonalRescale_normalization (S : Finset G)
    (hne : ∃ g ∈ S, g 0 1 ≠ 0) :
    ∃ z : ℂ, ∃ hz : z ≠ 0, ∃ u ∈ S,
      ‖diagonalRescale z hz u 0 1‖ = 1 ∧ ∀ g ∈ S, ‖diagonalRescale z hz g 0 1‖ ≤ 1 := by
  obtain ⟨g, hg, hgne⟩ := hne
  obtain ⟨u, hu, hmax⟩ := S.exists_max_image (fun g => ‖g 0 1‖) ⟨g, hg⟩
  have huz : u 0 1 ≠ 0 := by
    have hh := hmax g hg
    have hp := norm_pos_iff.mpr hgne
    intro he
    simp only [he, norm_zero] at hh
    linarith
  refine ⟨u 0 1, huz, u, hu, ?_, ?_⟩
  · change ‖u 0 1 / u 0 1‖ = 1
    simp [huz]
  · intro x hx
    change ‖x 0 1 / u 0 1‖ ≤ 1
    rw [norm_div]
    exact (div_le_one (norm_pos_iff.mpr huz)).mpr (hmax x hx)

theorem finite_family_rescaled_lower_bound (S : Finset G) {T ε : ℝ}
    (hT : 0 ≤ T) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2)
    (htr : ∀ g ∈ S, ‖Matrix.trace (g : M)‖ ≤ T)
    (hbc : ∀ g ∈ S, ‖g 0 1 * g 1 0‖ ≤ ε)
    (hprod : ∀ g ∈ S, ∀ h ∈ S, ‖(g * h) 0 1 * (g * h) 1 0‖ ≤ ε)
    (hne : ∃ g ∈ S, g 0 1 ≠ 0) :
    ∃ z : ℂ, ∃ hz : z ≠ 0, ∀ g ∈ S,
      ‖diagonalRescale z hz g 0 0‖ ≤ T + 2 ∧
      ‖diagonalRescale z hz g 1 1‖ ≤ T + 2 ∧
      1 / (2 * (T + 2)) ≤ ‖diagonalRescale z hz g 0 0‖ ∧
      ‖diagonalRescale z hz g 0 1‖ ≤ 1 ∧
      ‖diagonalRescale z hz g 1 0‖ ≤ 16 * (T + 2) ^ 4 * ε := by
  obtain ⟨z, hz, u, hu, hub, hb⟩ := exists_diagonalRescale_normalization S hne
  let e := diagonalRescale z hz
  have hd (g : G) (hg : g ∈ S) := diagonal_bounds_of_trace_offDiagonal hT
    (by simpa only [e, diagonalRescale_trace] using htr g hg : ‖Matrix.trace (e g : M)‖ ≤ T)
    hε (by simpa only [e, diagonalRescale_offDiagonal] using hbc g hg : ‖e g 0 1 * e g 1 0‖ ≤ ε)
  refine ⟨z, hz, ?_⟩
  intro g hg
  refine ⟨(hd g hg).1, (hd g hg).2.1, (hd g hg).2.2.1, hb g hg, ?_⟩
  apply normalized_lower_entry_bound (u := e u) (x := e g) (by linarith) hε0
    (hd u hu).1 (hd u hu).2.1 (hd g hg).1 (hd g hg).2.1
    (hd u hu).2.2.2 (hd g hg).2.2.2 hub (hb g hg)
  · simpa only [e, diagonalRescale_offDiagonal] using hbc u hu
  · simpa only [e, diagonalRescale_offDiagonal] using hbc g hg
  · rw [← map_mul]
    simpa only [e, diagonalRescale_offDiagonal] using hprod u hu g hg

end TransposeFollowup.SL2Escape
