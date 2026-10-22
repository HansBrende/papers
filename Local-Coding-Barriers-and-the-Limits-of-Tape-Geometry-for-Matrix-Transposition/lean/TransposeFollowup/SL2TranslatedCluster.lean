import TransposeFollowup.ConjugacyFiberCovering
import TransposeFollowup.FinitePieceCoverBounds

/-! Small clusters have many separated translates. Both multiplication
distortion and the cover-refinement cost are explicit in the Frobenius
metric. No invariance of that metric under the group action is assumed. -/
namespace TransposeFollowup.SL2Projection
open Classical Matrix Set RealMobius
open scoped Matrix.Norms.Frobenius Pointwise ENNReal NNReal
set_option autoImplicit false
local notation "RMat" => Matrix (Fin 2) (Fin 2) ℝ
local notation "G" => RealMobius.Group

theorem frobenius_dist_right_mul (a b u : RMat) :
    dist (a * u) (b * u) ≤ dist a b * ‖u‖ := by
  rw [dist_eq_norm, ← sub_mul, dist_eq_norm]
  exact norm_mul_le _ _

theorem coveringNumber_le_left_translate (t : G) {S : Set G} {B Q : ℝ} {η : ℝ≥0}
    (hB : 0 ≤ B) (hQ : 0 ≤ Q) (hη : 0 < η)
    (ht : ∀ i j, |t i j| ≤ B) (hS : ∀ x ∈ S, ∀ i j, |x i j| ≤ Q) :
    Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' S) ≠ ⊤ ∧
      Metric.externalCoveringNumber η ((fun x : G => ((t * x : G) : RMat)) '' S) ≠ ⊤ ∧
      (Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' S) : ℝ≥0∞).toReal ≤
        (8 * B + 1) ^ 4 *
          (Metric.externalCoveringNumber η ((fun x : G => ((t * x : G) : RMat)) '' S) : ℝ≥0∞).toReal := by
  let a (x : S) : RMat := ((x : G) : RMat)
  let b (x : S) : RMat := ((t * x : G) : RMat)
  let L (c : RMat) := ((t⁻¹ : G) : RMat) * c
  have hb : ∀ x i j, |b x i j| ≤ 2 * B * Q :=
    fun x => matrixEntryBox_mul ht (hS x x.2)
  have hn := frobenius_norm_le_of_entry_bound hB (matrixEntryBox_inv ht)
  have htrans : ∀ x c, dist (a x) (L c) ≤ (0 : ℝ) + (2 * B) * dist (b x) c := by
    intro x c
    have he : a x = ((t⁻¹ : G) : RMat) * b x := by
      have hh : t⁻¹ * (t * (x : G)) = x := by group
      exact (congrArg (fun z : G => (z : RMat)) hh).symm
    rw [he, zero_add]
    exact (frobenius_dist_left_mul _ _ _).trans
      (mul_le_mul_of_nonneg_right hn dist_nonneg)
  obtain ⟨hafin, hbfin, hbound⟩ := coveringNumber_le_bounded_transport a b L
    (by positivity : 0 ≤ 2 * B * Q) le_rfl (by positivity : 0 ≤ 2 * B) hη hb htrans
  have ha : Set.range a = (fun x : G => (x : RMat)) '' S :=
    (Set.image_eq_range _ _).symm
  have hb' : Set.range b = (fun x : G => ((t * x : G) : RMat)) '' S := by
    simpa only [b] using (Set.image_eq_range (fun x : G => ((t * x : G) : RMat)) S).symm
  rw [ha] at hafin hbound
  rw [hb'] at hbfin hbound
  have hcoef : 4 * ((0 : ℝ) + 2 * B * (η : ℝ)) / (η : ℝ) + 1 = 8 * B + 1 := by
    have hηR : (0 : ℝ) < η := hη
    field_simp
    ring
  rw [hcoef] at hbound
  exact ⟨hafin, hbfin, hbound⟩

theorem translated_clusters_separated (t u h x y : G) {B H r η : ℝ}
    (hB : 0 ≤ B) (hH : 0 ≤ H)
    (ht : ∀ i j, |t i j| ≤ B) (hu : ∀ i j, |u i j| ≤ B)
    (hh : ∀ i j, |h i j| ≤ H)
    (hx : dist (x : RMat) (h : RMat) ≤ r) (hy : dist (y : RMat) (h : RMat) ≤ r)
    (hsep : 8 * B * H * r + 4 * H * η < dist (t : RMat) (u : RMat)) :
    2 * η < dist ((t * x : G) : RMat) ((u * y : G) : RMat) := by
  have hr : 0 ≤ r := dist_nonneg.trans hx
  have htn := frobenius_norm_le_of_entry_bound hB ht
  have hun := frobenius_norm_le_of_entry_bound hB hu
  have hin := frobenius_norm_le_of_entry_bound hH (matrixEntryBox_inv hh)
  have htx : dist ((t * h : G) : RMat) ((t * x : G) : RMat) ≤ 2 * B * r := by
    have hx' : dist (h : RMat) (x : RMat) ≤ r := by rw [dist_comm]; exact hx
    exact (frobenius_dist_left_mul _ _ _).trans (mul_le_mul htn hx' dist_nonneg (by positivity))
  have huy : dist ((u * y : G) : RMat) ((u * h : G) : RMat) ≤ 2 * B * r :=
    (frobenius_dist_left_mul _ _ _).trans (mul_le_mul hun hy dist_nonneg (by positivity))
  have hcenter : dist ((t * h : G) : RMat) ((u * h : G) : RMat) ≤
      dist ((t * x : G) : RMat) ((u * y : G) : RMat) + 4 * B * r := by
    calc
      _ ≤ dist ((t * h : G) : RMat) ((t * x : G) : RMat) +
          dist ((t * x : G) : RMat) ((u * h : G) : RMat) := dist_triangle _ _ _
      _ ≤ dist ((t * h : G) : RMat) ((t * x : G) : RMat) +
          (dist ((t * x : G) : RMat) ((u * y : G) : RMat) +
            dist ((u * y : G) : RMat) ((u * h : G) : RMat)) := add_le_add le_rfl (dist_triangle _ _ _)
      _ ≤ 2 * B * r + (dist ((t * x : G) : RMat) ((u * y : G) : RMat) + 2 * B * r) :=
        add_le_add htx (add_le_add le_rfl huy)
      _ = _ := by ring
  have ht' : ((t * h : G) : RMat) * ((h⁻¹ : G) : RMat) = (t : RMat) := by
    exact congrArg (fun z : G => (z : RMat)) (show t * h * h⁻¹ = t by group)
  have hu' : ((u * h : G) : RMat) * ((h⁻¹ : G) : RMat) = (u : RMat) := by
    exact congrArg (fun z : G => (z : RMat)) (show u * h * h⁻¹ = u by group)
  have hd := frobenius_dist_right_mul ((t * h : G) : RMat) ((u * h : G) : RMat) ((h⁻¹ : G) : RMat)
  rw [ht', hu'] at hd
  have hdist : dist (t : RMat) (u : RMat) ≤
      2 * H * (dist ((t * x : G) : RMat) ((u * y : G) : RMat) + 4 * B * r) := by
    calc
      _ ≤ dist ((t * h : G) : RMat) ((u * h : G) : RMat) * ‖((h⁻¹ : G) : RMat)‖ := hd
      _ ≤ (dist ((t * x : G) : RMat) ((u * y : G) : RMat) + 4 * B * r) * (2 * H) :=
        mul_le_mul hcenter hin (norm_nonneg _) (by positivity)
      _ = _ := mul_comm _ _
  by_contra! hbad
  have hmul := mul_le_mul_of_nonneg_left hbad (by positivity : 0 ≤ 2 * H)
  nlinarith

theorem cluster_coveringNumber_mul_card_le {A : Set G} (T : Finset G) (h : G)
    {B H r ρ : ℝ} {η : ℝ≥0}
    (hB : 0 ≤ B) (hH : 0 ≤ H) (hη : 0 < η)
    (hA : ∀ x ∈ A, ∀ i j, |x i j| ≤ B) (hh : ∀ i j, |h i j| ≤ H)
    (hTA : (T : Set G) ⊆ A)
    (hsep : ∀ t ∈ T, ∀ u ∈ T, t ≠ u → ρ < dist (t : RMat) (u : RMat))
    (hscale : 8 * B * H * r + 4 * H * (η : ℝ) ≤ ρ) :
    let S := {x : G | x ∈ A ∧ dist (x : RMat) (h : RMat) ≤ r}
    Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' S) ≠ ⊤ ∧
      Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' (A ^ 2)) ≠ ⊤ ∧
      (T.card : ℝ) * (Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' S) : ℝ≥0∞).toReal ≤
        (8 * B + 1) ^ 4 *
          (Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' (A ^ 2)) : ℝ≥0∞).toReal := by
  let S := {x : G | x ∈ A ∧ dist (x : RMat) (h : RMat) ≤ r}
  let P (t : G) := (fun x : G => ((t * x : G) : RMat)) '' S
  have hSfin : Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' S) ≠ ⊤ := by
    apply finite_coveringNumber_of_entry_bound hB hη
    rintro z ⟨x, hx, rfl⟩
    exact hA x hx.1
  have hCfin : Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' (A ^ 2)) ≠ ⊤ := by
    apply finite_coveringNumber_of_entry_bound (by positivity : 0 ≤ 2 * B * B) hη
    rintro z ⟨x, hx, rfl⟩
    obtain ⟨u, hu, v, hv, rfl⟩ := (show x ∈ A * A by simpa only [pow_two] using hx)
    exact matrixEntryBox_mul (hA u hu) (hA v hv)
  have hsub : ∀ t ∈ T, P t ⊆ (fun x : G => (x : RMat)) '' (A ^ 2) := by
    intro t ht
    rintro z ⟨x, hx, rfl⟩
    refine ⟨t * x, ?_, rfl⟩
    simpa only [pow_two] using Set.mul_mem_mul (hTA ht) hx.1
  have hpsep : ∀ t ∈ T, ∀ u ∈ T, t ≠ u → ∀ x ∈ P t, ∀ y ∈ P u,
      2 * (η : ℝ) < dist x y := by
    intro t ht u hu hne
    rintro z ⟨x, hx, rfl⟩ w ⟨y, hy, rfl⟩
    exact translated_clusters_separated t u h x y hB hH (hA t (hTA ht)) (hA u (hTA hu)) hh
      hx.2 hy.2 (hscale.trans_lt (hsep t ht u hu hne))
  obtain ⟨_hPfin, hsum⟩ := sum_coveringNumber_le_of_separated T P hCfin hsub hpsep
  have hlocal (t : G) (ht : t ∈ T) :=
    (coveringNumber_le_left_translate t (S := S) hB hB hη (hA t (hTA ht)) (fun x hx => hA x hx.1)).2.2
  refine ⟨hSfin, hCfin, ?_⟩
  calc
    _ = ∑ _t ∈ T, (Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' S) : ℝ≥0∞).toReal := by simp [S]
    _ ≤ ∑ t ∈ T, (8 * B + 1) ^ 4 * (Metric.externalCoveringNumber η (P t) : ℝ≥0∞).toReal :=
      Finset.sum_le_sum hlocal
    _ = (8 * B + 1) ^ 4 * (∑ t ∈ T, (Metric.externalCoveringNumber η (P t) : ℝ≥0∞).toReal) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity)

end TransposeFollowup.SL2Projection
