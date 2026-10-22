import TransposeFollowup.RealDeterminantNormalization
import TransposeFollowup.SL2TraceProjection
import TransposeFollowup.SL2SpanningTrace

/-! Exact determinant-one commuting approximants, with entry and Frobenius
error bounds. A noncentral pivot suffices, including the unipotent case. -/
namespace TransposeFollowup.SL2Projection
open Classical Matrix Set RealMobius
open scoped Matrix.Norms.Frobenius
set_option autoImplicit false
local notation "RMat" => Matrix (Fin 2) (Fin 2) ℝ
local notation "G" => RealMobius.Group

theorem frobenius_dist_le_of_entry_error {x y : RMat} {δ : ℝ} (hδ : 0 ≤ δ)
    (he : ∀ i j, |x i j - y i j| ≤ δ) : dist x y ≤ 2 * δ := by
  apply (frobenius_dist_le_iff (by positivity : 0 ≤ 2 * δ)).mpr
  have hs (i j : Fin 2) : (x i j - y i j) ^ 2 ≤ δ ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hδ).mpr (he i j)
  simp only [Fin.sum_univ_two]
  nlinarith [hs 0 0, hs 0 1, hs 1 0, hs 1 1]

theorem exists_sl2_commuting_approximation (g : RMat) (x : G) {B ρ ε : ℝ}
    (hB : 1 ≤ B) (hρ : 0 < ρ) (hε : 0 ≤ ε)
    (hsmall : 12 * B * (ε / ρ) ≤ 1)
    (hpivot : ∃ i, ρ ≤ |noncentralCoordinates g i|)
    (hx : ∀ i j, |x i j| ≤ B)
    (hc : ∀ i j, |(g * (x : RMat) - (x : RMat) * g) i j| ≤ ε) :
    ∃ (y : G) (s t : ℝ), (y : RMat) = scalarAffine g s t ∧
      (∀ i j, |x i j - y i j| ≤ 25 * B ^ 2 * (ε / ρ)) ∧
      dist (x : RMat) (y : RMat) ≤ 50 * B ^ 2 * (ε / ρ) := by
  obtain ⟨s, t, he⟩ := exists_scalarAffine_approx g (x : RMat) hρ hε hpivot hc
  obtain ⟨r, _hr, _hr2, hdet, hclose⟩ := exists_sl2_scalar_normalization x
    (scalarAffine g s t) hB (div_nonneg hε hρ.le) hsmall hx he
  let y : G := ⟨r • scalarAffine g s t, hdet⟩
  refine ⟨y, r * s, r * t, smul_scalarAffine g s t r, hclose, ?_⟩
  have hh := frobenius_dist_le_of_entry_error (by positivity : 0 ≤ 25 * B ^ 2 * (ε / ρ)) hclose
  convert hh using 1; ring

theorem exists_pairwise_commuting_approximants (g : RMat) {A : Set G} {B ρ ε : ℝ}
    (hB : 1 ≤ B) (hρ : 0 < ρ) (hε : 0 ≤ ε)
    (hsmall : 12 * B * (ε / ρ) ≤ 1)
    (hpivot : ∃ i, ρ ≤ |noncentralCoordinates g i|)
    (hA : ∀ x ∈ A, ∀ i j, |x i j| ≤ B)
    (hc : ∀ x ∈ A, ∀ i j, |(g * (x : RMat) - (x : RMat) * g) i j| ≤ ε) :
    ∃ f : A → G,
      (∀ x : A, ∃ s t : ℝ, (f x : RMat) = scalarAffine g s t) ∧
      (∀ x : A, ∀ i j, |(x : G) i j - f x i j| ≤ 25 * B ^ 2 * (ε / ρ)) ∧
      (∀ x : A, dist ((x : G) : RMat) (f x : RMat) ≤ 50 * B ^ 2 * (ε / ρ)) ∧
      ∀ x y : A, Commute (f x) (f y) := by
  have hex (x : A) := exists_sl2_commuting_approximation g x hB hρ hε hsmall hpivot
    (hA x x.2) (hc x x.2)
  choose f s t hform hentry hdist using hex
  refine ⟨f, fun x => ⟨s x, t x, hform x⟩, hentry, hdist, ?_⟩
  intro x y
  change f x * f y = f y * f x
  apply Subtype.ext
  change (f x : RMat) * (f y : RMat) = (f y : RMat) * (f x : RMat)
  rw [hform x, hform y]
  exact scalarAffine_commute g (s x) (t x) (s y) (t y)

theorem near_identity_dist_le_noncentral (g : G) {α θ : ℝ}
    (hα : 0 < α) (hαhalf : α ≤ 1 / 2) (hg : g ∈ mobiusIdentityBall α)
    (hθ : 0 ≤ θ) (hc : ∀ i, |noncentralCoordinates (g : RMat) i| ≤ θ) :
    dist (g : RMat) 1 ≤ 8 * θ := by
  have hb := mobiusIdentityBall_subset_entryBox_two hα (by linarith) hg
  obtain ⟨ha, _hb, hcc, _hd⟩ := mobiusIdentityBall_entry_bounds hα hg
  have ha0 : 1 / 2 ≤ g 0 0 := by linarith [(abs_lt.mp ha).1]
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using g.property
  have hprod : |g 0 0 ^ 2 - 1| ≤ 3 * θ := by
    rw [show g 0 0 ^ 2 - 1 = g 0 0 * (g 0 0 - g 1 1) + g 0 1 * g 1 0 by
      nlinarith only [hdet]]
    calc
      _ ≤ |g 0 0 * (g 0 0 - g 1 1)| + |g 0 1 * g 1 0| := abs_add_le _ _
      _ = |g 0 0| * |g 0 0 - g 1 1| + |g 0 1| * |g 1 0| := by rw [abs_mul, abs_mul]
      _ ≤ 2 * θ + θ * 1 := add_le_add
        (mul_le_mul (hb 0 0) (hc 0) (abs_nonneg _) (by norm_num))
        (mul_le_mul (hc 1) (by linarith : |g 1 0| ≤ 1) (abs_nonneg _) hθ)
      _ = _ := by ring
  have hae : |g 0 0 - 1| ≤ 3 * θ := by
    calc
      _ ≤ |g 0 0 - 1| * |g 0 0 + 1| :=
        le_mul_of_one_le_right (abs_nonneg _) (by rw [abs_of_pos (by linarith)]; linarith)
      _ = |g 0 0 ^ 2 - 1| := by rw [← abs_mul]; congr 1; ring
      _ ≤ _ := hprod
  have hde : |g 1 1 - 1| ≤ 4 * θ := by
    have hh := abs_add_le (g 1 1 - g 0 0) (g 0 0 - 1)
    rw [sub_add_sub_cancel] at hh
    have hdif := hc 0
    change |g 0 0 - g 1 1| ≤ θ at hdif
    have hda : |g 1 1 - g 0 0| ≤ θ := by rw [abs_sub_comm]; exact hdif
    linarith
  have he : ∀ i j, |g i j - (1 : RMat) i j| ≤ 4 * θ := by
    intro i j
    fin_cases i <;> fin_cases j
    · change |g 0 0 - 1| ≤ _; linarith
    · simpa using (show |g 0 1| ≤ 4 * θ by have hh := hc 1; change |g 0 1| ≤ θ at hh; linarith)
    · simpa using (show |g 1 0| ≤ 4 * θ by have hh := hc 2; change |g 1 0| ≤ θ at hh; linarith)
    · exact hde
  have hh := frobenius_dist_le_of_entry_error (by positivity : 0 ≤ 4 * θ) he
  linarith

theorem exists_near_identity_noncentral_pivot (g : G) {α r : ℝ}
    (hα : 0 < α) (hαhalf : α ≤ 1 / 2) (hg : g ∈ mobiusIdentityBall α)
    (hr : r ≤ dist (g : RMat) 1) :
    ∃ i, r / 8 ≤ |noncentralCoordinates (g : RMat) i| := by
  obtain ⟨i, _hi, hmax⟩ := Finset.univ.exists_max_image
    (fun i : Fin 3 => |noncentralCoordinates (g : RMat) i|) Finset.univ_nonempty
  have hh := near_identity_dist_le_noncentral g hα hαhalf hg (abs_nonneg _)
    (fun j => hmax j (Finset.mem_univ _))
  exact ⟨i, by linarith⟩

theorem exists_near_identity_commuting_approximants (g : G) {A : Set G} {α r B ε : ℝ}
    (hα : 0 < α) (hαhalf : α ≤ 1 / 2) (hg : g ∈ mobiusIdentityBall α)
    (hr : 0 < r) (hfar : r ≤ dist (g : RMat) 1)
    (hB : 1 ≤ B) (hε : 0 ≤ ε) (hsmall : 96 * B * ε ≤ r)
    (hA : ∀ x ∈ A, ∀ i j, |x i j| ≤ B)
    (hc : ∀ x ∈ A, ∀ i j, |((g : RMat) * (x : RMat) - (x : RMat) * (g : RMat)) i j| ≤ ε) :
    ∃ f : A → G,
      (∀ x : A, ∃ s t : ℝ, (f x : RMat) = scalarAffine (g : RMat) s t) ∧
      (∀ x : A, ∀ i j, |(x : G) i j - f x i j| ≤ 200 * B ^ 2 * ε / r) ∧
      (∀ x : A, dist ((x : G) : RMat) (f x : RMat) ≤ 400 * B ^ 2 * ε / r) ∧
      ∀ x y : A, Commute (f x) (f y) := by
  have hpivot := exists_near_identity_noncentral_pivot g hα hαhalf hg hfar
  have hsmall' : 12 * B * (ε / (r / 8)) ≤ 1 := by
    have he : 12 * B * (ε / (r / 8)) = 96 * B * ε / r := by field_simp; ring
    rw [he, div_le_iff₀ hr]
    simpa only [one_mul] using hsmall
  obtain ⟨f, hform, hentry, hdist, hcomm⟩ := exists_pairwise_commuting_approximants
    (g : RMat) hB (by positivity : 0 < r / 8) hε hsmall' hpivot hA hc
  refine ⟨f, hform, ?_, ?_, hcomm⟩
  · intro x i j
    convert hentry x i j using 1
    field_simp
    ring
  · intro x
    convert hdist x using 1
    field_simp
    ring

end TransposeFollowup.SL2Projection
