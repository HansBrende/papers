import TransposeFollowup.PopularRowIntersections
import TransposeFollowup.OverlappingRowRuzsa
import OAI.MeasureTheory.Falconer.Estimates.ScalarDilationBound

/-! A small product cell set gives popular overlaps of rounded dilates.
Combined with small sum cells, those overlaps force many small projections.
All rounding and dilation factors come from the imported scalar library. -/
namespace TransposeFollowup.ScalarMetric
open scoped Pointwise
open Finset OAI.Falconer
set_option autoImplicit false

theorem rounded_dilate_card {δ a : ℝ} (hδ : 0 < δ) (ha : 1 ≤ a)
    (X : Finset ℝ) (hsep : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → δ ≤ |x - y|) :
    (scalarCells δ (X.image (fun x => a * x))).card = X.card := by
  have ha0 : a ≠ 0 := by linarith
  have hsep' : ∀ u ∈ X.image (fun x => a * x),
      ∀ v ∈ X.image (fun x => a * x), u ≠ v → δ ≤ |u - v| := by
    intro u hu v hv hne
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hu
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hv
    have hxy : x ≠ y := fun h => hne (congrArg (fun z => a * z) h)
    calc
      δ ≤ |x - y| := hsep x hx y hy hxy
      _ ≤ a * |x - y| := le_mul_of_one_le_left (abs_nonneg _) ha
      _ = |a * x - a * y| := by rw [← mul_sub, abs_mul, abs_of_pos (by linarith : 0 < a)]
  change (Finset.image (fun x => ⌊x / δ⌋) (X.image (fun x => a * x))).card = X.card
  rw [card_image_of_injOn (scalarCells_injective hδ hsep')]
  exact card_image_of_injective X (fun _ _ h => mul_left_cancel₀ ha0 h)

theorem rounded_dilate_doubling {δ a K : ℝ} (hδ : 0 < δ)
    (ha : |a| ≤ 2) (X : Finset ℝ)
    (hsum : ((scalarCells δ (X + X)).card : ℝ) ≤ K * X.card) :
    (((scalarCells δ (X.image (fun x => a * x))) +
      (scalarCells δ (X.image (fun x => a * x)))).card : ℝ) ≤ 14 * K * X.card := by
  have hround : (((scalarCells δ (X.image (fun x => a * x))) +
      (scalarCells δ (X.image (fun x => a * x)))).card : ℝ) ≤
      2 * (scalarCells δ (X.image (fun x => a * x) + X.image (fun x => a * x))).card := by
    exact_mod_cast add_scalarCells_card δ (X.image (fun x => a * x)) (X.image (fun x => a * x))
  have hdilate : ((scalarCells δ ((X + X).image (fun x => a * x))).card : ℝ) ≤
      7 * (scalarCells δ (X + X)).card := by
    exact_mod_cast scalar_dilation_cells hδ (X + X) 2 (by simpa using ha)
  have heq : (X + X).image (fun x => a * x) =
      X.image (fun x => a * x) + X.image (fun x => a * x) :=
    image_add (AddMonoidHom.mulLeft a)
  rw [heq] at hdilate
  linarith

theorem ratio_projection_cells_le {δ a b : ℝ} (hδ : 0 < δ) (ha : 1 ≤ a)
    (X : Finset ℝ) :
    (scalarCells δ (X + X.image (fun x => (b / a) * x))).card ≤
      10 * ((scalarCells δ (X.image (fun x => a * x))) +
        (scalarCells δ (X.image (fun x => b * x)))).card := by
  have ha0 : a ≠ 0 := by linarith
  have hinv : |a⁻¹| ≤ (1 : ℕ) := by
    rw [abs_of_pos (inv_pos.mpr (by linarith : 0 < a))]
    simpa using (inv_le_one₀ (by linarith : 0 < a)).mpr ha
  have heq : (X.image (fun x => a * x) + X.image (fun x => b * x)).image
      (fun x => a⁻¹ * x) = X + X.image (fun x => (b / a) * x) := by
    have himage : (X.image (fun x => a * x) + X.image (fun x => b * x)).image
        (fun x => a⁻¹ * x) = (X.image (fun x => a * x)).image (fun x => a⁻¹ * x) +
          (X.image (fun x => b * x)).image (fun x => a⁻¹ * x) :=
      image_add (AddMonoidHom.mulLeft a⁻¹)
    rw [himage, image_image, image_image]
    simp only [Function.comp_def]
    have hleft : (fun x : ℝ => a⁻¹ * (a * x)) = id := by
      funext x
      simp only [← mul_assoc, inv_mul_cancel₀ ha0, one_mul, id_eq]
    have hright : (fun x : ℝ => a⁻¹ * (b * x)) = (fun x => (b / a) * x) := by
      funext x
      simp only [div_eq_mul_inv]
      ring
    rw [hleft, hright, image_id]
  have hscale := scalar_dilation_cells hδ
    (X.image (fun x => a * x) + X.image (fun x => b * x)) 1 hinv
  rw [heq] at hscale
  have hround := scalarCells_add_card δ (X.image (fun x => a * x)) (X.image (fun x => b * x))
  omega

/-- The finite counting bridge needed before invoking a projection theorem.
No concentration hypothesis is assumed or manufactured by this statement. -/
theorem small_sum_product_gives_small_projections {δ K : ℝ}
    (hδ : 0 < δ) (hK : 0 < K) (X : Finset ℝ) (hX : X.Nonempty)
    (hbound : ∀ x ∈ X, 1 ≤ x ∧ x ≤ 2)
    (hsep : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → δ ≤ |x - y|)
    (hsum : ((scalarCells δ (X + X)).card : ℝ) ≤ K * X.card)
    (hproduct : ((scalarCells δ (X * X)).card : ℝ) ≤ K * X.card) :
    ∃ a ∈ X, ∃ E : Finset ℝ, E ⊆ X ∧
      (X.card : ℝ) ≤ 2 * K * E.card ∧
      ∀ b ∈ E, ((scalarCells δ (X + X.image (fun x => (b / a) * x))).card : ℝ) ≤
        54880 * K ^ 4 * X.card := by
  classical
  let R : ℝ → Finset ℤ := fun a => scalarCells δ (X.image (fun x => a * x))
  have hsub (a : ℝ) (ha : a ∈ X) : R a ⊆ scalarCells δ (X * X) := by
    apply image_subset_image
    intro z hz
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hz
    exact mul_mem_mul ha hx
  have hcard (a : ℝ) (ha : a ∈ X) : (R a).card = X.card :=
    rounded_dilate_card hδ (hbound a ha).1 X hsep
  have hdouble (a : ℝ) (ha : a ∈ X) : ((R a + R a).card : ℝ) ≤ 14 * K * X.card :=
    rounded_dilate_doubling hδ
      (by rw [abs_of_pos (by linarith [(hbound a ha).1] : 0 < a)]; exact (hbound a ha).2)
      X hsum
  obtain ⟨a, ha, E, hEX, hsize, hover⟩ :=
    exists_popular_row_intersections X (scalarCells δ (X * X)) R hX hK hsub hcard hproduct
  refine ⟨a, ha, E, hEX, hsize, ?_⟩
  intro b hb
  have hRa : (R a).Nonempty := card_pos.mp (by rw [hcard a ha]; exact hX.card_pos)
  have hmix : ((R a + R b).card : ℝ) ≤ 2 * K * (14 * K) ^ 3 * X.card := by
    have h := mixed_sum_le_of_popular_overlap (R a) (R b) hRa hK
      (L := 14 * K) (by rw [hcard a ha]; nlinarith [hdouble a ha])
      (by rw [hcard a ha]; nlinarith [hdouble b (hEX hb)])
      (by rw [hcard a ha]; exact hover b hb)
    simpa only [hcard a ha] using h
  have hround : ((scalarCells δ (X + X.image (fun x => (b / a) * x))).card : ℝ) ≤
      10 * (R a + R b).card := by
    exact_mod_cast ratio_projection_cells_le hδ (hbound a ha).1 X
  calc
    _ ≤ (10 : ℝ) * (R a + R b).card := hround
    _ ≤ 10 * (2 * K * (14 * K) ^ 3 * X.card) := mul_le_mul_of_nonneg_left hmix (by norm_num)
    _ = _ := by ring

end TransposeFollowup.ScalarMetric
