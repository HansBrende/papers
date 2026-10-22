import TransposeFollowup.CentralizerProductInverse
import TransposeFollowup.SeparatedMatrixSample

/-! Cubic packing of three small centralizer charts under an explicit
quantitative frame hypothesis. This does not select the frame or localize
an arbitrary commuting set. The covering number is mathlib's native one. -/
namespace TransposeFollowup.SL2Projection
open Classical Matrix
open scoped Matrix.Norms.Frobenius ENNReal NNReal
set_option autoImplicit false
local notation "RMat" => Matrix (Fin 2) (Fin 2) ℝ
local notation "G" => Matrix.SpecialLinearGroup (Fin 2) ℝ

theorem centered_triple_product_cubic_packing (F : Finset ℝ)
    (b : Fin 3 → RMat) (u : Fin 3 → ℝ → G) (c : Fin 3 → ℝ → ℝ)
    (T : Matrix (Fin 4) (Fin 4) ℝ) {M r d : ℝ} {η : ℝ≥0}
    (hM : 1 ≤ M) (hr : 0 ≤ r) (hr1 : r ≤ 1) (hd : 0 < d)
    (hsmall : 3 * M * r ≤ 1) (habsorb : 36864 * M ^ 6 * r ≤ d)
    (hT : ∀ i j, |T i j| ≤ M) (hdet : d ≤ |T.det|)
    (hcolumns : ∀ i j, T i j.succ = matrixCoordinates (b j) i)
    (hb : ∀ i, Matrix.trace (b i) = 0)
    (hbn : ∀ i, ‖b i‖ ≤ M) (hbd : ∀ i, |(b i).det| ≤ M)
    (hu : ∀ i x, x ∈ F → (u i x : RMat) = scalarAffine (b i) (c i x) x)
    (hc : ∀ i x, x ∈ F → 1 / 2 ≤ c i x)
    (ht : ∀ x ∈ F, |x| ≤ r)
    (hsep : ∀ x ∈ F, ∀ y ∈ F, x ≠ y →
      384 * M ^ 4 / d * (η : ℝ) < |x - y|) :
    let S := Set.range (fun x : Fin 3 → ↥F =>
      ((u 0 (x 0) * u 1 (x 1) * u 2 (x 2) : G) : RMat))
    Metric.externalCoveringNumber η S ≠ ⊤ ∧
      (F.card : ℝ) ^ 3 ≤ (Metric.externalCoveringNumber η S : ℝ≥0∞).toReal := by
  let f : (Fin 3 → ↥F) → RMat := fun x =>
    ((u 0 (x 0) * u 1 (x 1) * u 2 (x 2) : G) : RMat)
  let K : ℝ := 192 * M ^ 4 / d
  have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hK : 0 < K := by dsimp only [K]; positivity
  have hs (x y : Fin 3 → ↥F) (hxy : x ≠ y) : 2 * (η : ℝ) < dist (f x) (f y) := by
    have hcoord : ∃ i, (x i : ℝ) ≠ (y i : ℝ) := by
      by_contra hn
      push Not at hn
      exact hxy (funext (fun i => Subtype.ext (hn i)))
    obtain ⟨i, hi⟩ := hcoord
    have hn : |(x i : ℝ) - (y i : ℝ)| ≤
        ‖(fun j => (x j : ℝ)) - (fun j => (y j : ℝ))‖ := by
      simpa only [Pi.sub_apply, Real.norm_eq_abs] using
        norm_le_pi_norm ((fun j => (x j : ℝ)) - (fun j => (y j : ℝ))) i
    have hinv := centered_triple_product_inverse b
      (fun j => u j (x j)) (fun j => u j (y j))
      (fun j => c j (x j)) (fun j => c j (y j))
      (fun j => (x j : ℝ)) (fun j => (y j : ℝ)) T
      hM hr hr1 hd hsmall habsorb hT hdet hcolumns hb hbn hbd
      (fun j => hu j _ (x j).property) (fun j => hu j _ (y j).property)
      (fun j => hc j _ (x j).property) (fun j => hc j _ (y j).property)
      (fun j => ht _ (x j).property) (fun j => ht _ (y j).property)
    have hh : K * (2 * (η : ℝ)) < K * dist (f x) (f y) := by
      calc
        _ = 384 * M ^ 4 / d * (η : ℝ) := by dsimp only [K]; ring
        _ < |(x i : ℝ) - (y i : ℝ)| := hsep _ (x i).property _ (y i).property hi
        _ ≤ ‖(fun j => (x j : ℝ)) - (fun j => (y j : ℝ))‖ := hn
        _ ≤ K * dist (f x) (f y) := hinv
    nlinarith only [hh, hK]
  have hinj : Function.Injective f := by
    intro x y he
    by_contra hn
    have hh := hs x y hn
    rw [he, dist_self] at hh
    exact (not_lt_of_ge (by positivity)) hh
  let E : Finset RMat := Finset.univ.image f
  have hE : (E : Set RMat) = Set.range f := by
    ext z
    simp [E]
  have hcard : E.card = F.card ^ 3 := by
    dsimp only [E]
    rw [Finset.card_image_of_injective _ hinj]
    simp
  have hfin : Metric.externalCoveringNumber η (Set.range f) ≠ ⊤ := by
    apply ne_top_of_le_ne_top _ (Metric.externalCoveringNumber_le_encard_self _)
    rw [← hE, Set.encard_coe_eq_coe_finsetCard]
    exact ENat.natCast_ne_top _
  have hcount := separated_matrix_card_le_coveringNumber E (η := η)
    (by rw [hE]) (by
      intro x hx y hy hxy
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hy
      exact hs a b (fun he => hxy (congrArg f he))) hfin
  change Metric.externalCoveringNumber η (Set.range f) ≠ ⊤ ∧ _
  refine ⟨hfin, ?_⟩
  simpa only [hcard, Nat.cast_pow] using hcount

end TransposeFollowup.SL2Projection
