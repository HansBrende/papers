import TransposeFollowup.CentralizerClusterSelection

/-! A retained scalar sample with explicit source witnesses. The finite
image and its extension use mathlib; no new choice or packing mechanism
is introduced. -/
namespace TransposeFollowup.SL2Projection
open Classical Matrix BoundedCoordinatePacking
open scoped Matrix.Norms.Frobenius
set_option autoImplicit false
local notation "RMat" => Matrix (Fin 2) (Fin 2) ℝ
local notation "G" => Matrix.SpecialLinearGroup (Fin 2) ℝ

theorem exists_localized_scalar_sample {ι : Type*} [Fintype ι]
    (f : ι → G) (b : RMat) (c t : ι → ℝ) {B M ρ r δ σ : ℝ} {m : ℕ}
    (hB : 1 ≤ B) (hM : 1 ≤ M) (hρ : 0 < ρ) (hδ : 0 < δ) (hσ : 0 ≤ σ)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hm : 0 < m)
    (hb : Matrix.trace b = 0) (hbn : ‖b‖ ≤ M) (hbd : |b.det| ≤ M)
    (hpivot : ∃ i, ρ ≤ |noncentralCoordinates b i|)
    (hf : ∀ x i j, |f x i j| ≤ B)
    (hform : ∀ x, (f x : RMat) = scalarAffine b (c x) (t x))
    (hbranch : 8 * B * δ ≤ 1) (hradius : 8 * B * δ ≤ ρ * r)
    (hcard : binCount B δ ^ 4 * m ≤ Fintype.card ι)
    (hsep : ∀ x y, x ≠ y →
      10 * B * M * σ < dist (f x : RMat) (f y : RMat)) :
    ∃ x₀ : ι, ∃ F : Finset ℝ, ∃ s : ℝ → ι, ∃ a : ℝ → ℝ,
      m ≤ F.card ∧
      (∀ x ∈ F, (((f x₀)⁻¹ * f (s x) : G) : RMat) = scalarAffine b (a x) x) ∧
      (∀ x ∈ F, 1 / 2 ≤ a x ∧ |x| ≤ r) ∧
      (∀ x ∈ F, dist (f (s x) : RMat) (f x₀ : RMat) ≤ 2 * δ) ∧
      (∀ x ∈ F, ∀ y ∈ F, x ≠ y → σ < |x - y|) := by
  obtain ⟨S, hS, x₀, hx₀, p, q, hform', hchart, hclose, hdist⟩ :=
    exists_localized_centered_parameters f b c t hB hM hρ hδ hr hr1 hm
      hb hbn hbd hpivot hf hform hbranch hradius hcard
  have hK : 0 < 10 * B * M := by positivity
  have hqs : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → σ < |q x - q y| := by
    intro x hx y hy hxy
    have hh := (hsep x y hxy).trans_le (hdist x hx y hy)
    nlinarith only [hh, hK]
  have hinj : Set.InjOn q (S : Set ι) := by
    intro x hx y hy he
    by_contra hn
    have hh := hqs x hx y hy hn
    rw [he, sub_self, abs_zero] at hh
    exact (not_lt_of_ge hσ) hh
  let F := S.image q
  let qS : ↥S → ℝ := fun x => q x
  have hi : Function.Injective qS := by
    intro x y he
    exact Subtype.ext (hinj x.property y.property he)
  let s : ℝ → ι := Function.extend qS Subtype.val (fun _ => x₀)
  have hs : ∀ x ∈ F, s x ∈ S ∧ q (s x) = x := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    have he : s (q y) = y := hi.extend_apply Subtype.val (fun _ => x₀) ⟨y, hy⟩
    rw [he]
    exact ⟨hy, rfl⟩
  refine ⟨x₀, F, s, fun x => p (s x), ?_, ?_, ?_, ?_, ?_⟩
  · exact hS.trans_eq (Finset.card_image_of_injOn hinj).symm
  · intro x hx
    simpa only [(hs x hx).2] using hform' (s x)
  · intro x hx
    simpa only [(hs x hx).2] using hchart (s x) (hs x hx).1
  · intro x hx
    exact hclose (s x) (hs x hx).1
  · intro x hx y hy hxy
    have hne : s x ≠ s y := by
      intro he
      apply hxy
      rw [← (hs x hx).2, ← (hs y hy).2, he]
    simpa only [(hs x hx).2, (hs y hy).2] using
      hqs (s x) (hs x hx).1 (s y) (hs y hy).1 hne

end TransposeFollowup.SL2Projection
