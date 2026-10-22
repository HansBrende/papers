import TransposeFollowup.CoarsenedSourceSample

/-! Resample a finite family without changing its original source indices.
The coarse loss is paid after any restriction already made on the family.
The covering and packing arguments are reused from `CoarsenedSourceSample`. -/
namespace TransposeFollowup.SL2Projection
open Classical Matrix Set
open scoped Matrix.Norms.Frobenius ENNReal NNReal
set_option autoImplicit false
local notation "RMat" => Matrix (Fin 2) (Fin 2) ℝ

theorem exists_coarse_source_subsample {ι : Type*} (g : ι → RMat)
    (T : Finset ι) {B : ℝ} {η σ : ℝ≥0}
    (hB : 0 ≤ B) (hη : 0 < η) (hσ : 0 < σ) (hT : T.Nonempty)
    (hg : ∀ x ∈ T, ∀ i j, |g x i j| ≤ B)
    (hsep : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → 2*(η : ℝ) < dist (g x) (g y)) :
    ∃ S : Finset ι, S ⊆ T ∧ S.Nonempty ∧
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → 2*(σ : ℝ) < dist (g x) (g y)) ∧
      (T.card : ℝ) ≤ 6561*(4*(σ : ℝ)/(η : ℝ)+1)^4*(S.card : ℝ) := by
  classical
  have hgn : (Set.range (fun i : ↥T => g i)).Nonempty := by
    obtain ⟨i, hi⟩ := hT
    exact ⟨g i, ⟨⟨i, hi⟩, rfl⟩⟩
  obtain ⟨F, a, hFn, ha, hFsep, hfin, hretain⟩ :=
    exists_coarse_source_sample (fun i : ↥T => g i) hB hη hσ hgn
      (fun i => hg i i.property)
  let b : ↥F → ι := fun i => a i
  have hbinj : Function.Injective b := by
    intro i j hij
    apply Subtype.ext
    rw [← ha i, ← ha j]
    exact congrArg g hij
  let S := Finset.univ.image b
  have hScard : S.card = F.card := by
    rw [Finset.card_image_of_injective _ hbinj, Finset.card_univ, Fintype.card_coe]
  have hginj : Set.InjOn g (T : Set ι) := by
    intro x hx y hy hxy
    by_contra hne
    have hh := hsep x hx y hy hne
    rw [hxy, dist_self] at hh
    exact (not_lt_of_ge (by positivity : 0 ≤ 2*(η : ℝ))) hh
  have hcard : (T.image g).card = T.card := Finset.card_image_iff.mpr hginj
  have hlower : (T.card : ℝ) ≤
      (Metric.externalCoveringNumber η (Set.range (fun i : ↥T => g i)) : ℝ≥0∞).toReal := by
    rw [← hcard]
    apply separated_matrix_card_le_coveringNumber (T.image g) ?_ ?_ hfin
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact ⟨⟨i, hi⟩, rfl⟩
    · intro x hx y hy hne
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
      exact hsep i hi j hj (fun hij => hne (congrArg g hij))
  refine ⟨S, ?_, ?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    exact (a j).property
  · obtain ⟨i, hi⟩ := hFn
    exact ⟨b ⟨i, hi⟩, Finset.mem_image.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, rfl⟩⟩
  · intro i hi j hj hne
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hj
    change 2*(σ : ℝ) < dist (g (a x)) (g (a y))
    rw [ha x, ha y]
    exact hFsep x x.property y y.property
      (fun hxy => hne (congrArg b (Subtype.ext hxy)))
  · rw [hScard]
    exact hlower.trans hretain

/-- A scalar inverse estimate on an already trimmed family survives
coarsening. The returned set is a subset of the original source indices,
so every earlier unary or pairwise branch condition is preserved. -/
theorem exists_scalar_source_subsample {ι : Type*} (g : ι → RMat) (a : ι → ℝ)
    (T : Finset ι) {B K δ : ℝ} {η σ : ℝ≥0}
    (hB : 0 ≤ B) (hη : 0 < η) (hσ : 0 < σ) (hT : T.Nonempty)
    (hg : ∀ x ∈ T, ∀ i j, |g x i j| ≤ B)
    (hsep : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → 2*(η : ℝ) < dist (g x) (g y))
    (hK : 0 ≤ K) (hδ : 0 ≤ δ) (hspacing : K*δ ≤ 2*(σ : ℝ))
    (hinverse : ∀ x ∈ T, ∀ y ∈ T, dist (g x) (g y) ≤ K*|a x-a y|) :
    ∃ S : Finset ι, S ⊆ T ∧ S.Nonempty ∧
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → 2*(σ : ℝ) < dist (g x) (g y)) ∧
      let Z := S.image a
      Z.Nonempty ∧ Z.card = S.card ∧
      (∀ x ∈ Z, ∀ y ∈ Z, x ≠ y → δ < |x-y|) ∧
      (T.card : ℝ) ≤ 6561*(4*(σ : ℝ)/(η : ℝ)+1)^4*(Z.card : ℝ) := by
  classical
  obtain ⟨S, hST, hSn, hSsep, hretain⟩ :=
    exists_coarse_source_subsample g T hB hη hσ hT hg hsep
  have hscalar : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ < |a x-a y| := by
    intro x hx y hy hne
    by_contra hn
    have hu := mul_le_mul_of_nonneg_left (le_of_not_gt hn) hK
    have hi := hinverse x (hST hx) y (hST hy)
    exact (not_lt_of_ge (hi.trans (hu.trans hspacing))) (hSsep x hx y hy hne)
  have hinj : Set.InjOn a (S : Set ι) := by
    intro x hx y hy heq
    by_contra hne
    have hh := hscalar x hx y hy hne
    rw [heq, sub_self, abs_zero] at hh
    exact (not_lt_of_ge hδ) hh
  have hcard : (S.image a).card = S.card := Finset.card_image_iff.mpr hinj
  refine ⟨S, hST, hSn, hSsep, hSn.image a, hcard, ?_, ?_⟩
  · intro x hx y hy hne
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
    exact hscalar i hi j hj (fun hij => hne (congrArg a hij))
  · rw [hcard]
    exact hretain

end TransposeFollowup.SL2Projection
