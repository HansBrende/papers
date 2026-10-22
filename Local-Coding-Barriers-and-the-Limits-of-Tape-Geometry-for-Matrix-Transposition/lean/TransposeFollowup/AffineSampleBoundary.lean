import TransposeFollowup.PrioritySampleTransfer
import TransposeFollowup.AffineGridCollisions
import TransposeFollowup.AffineFiniteBoundary

/-! The finite affine boundary becomes the boundary of the actual priority
samples off an explicit grid-collision set. Right composition is checked
against affine evaluation, including its orientation and translation term. -/
namespace TransposeFollowup.AffineMotion
open Classical Finset Set
open scoped ENNReal
set_option autoImplicit false

noncomputable def affineGridValue (h x : ℝ) (p : ℝˣ × ℝ) : ℤ :=
  ⌊((p.1 : ℝ)*x+p.2)/h⌋

theorem affineGridValue_right (h x : ℝ) (s : ℝˣ) (b : ℝ) (p : ℝˣ × ℝ) :
    affineGridValue h x (FiniteBoundary.affineRight s b p)=
      affineGridValue h ((s : ℝ)*x+b) p := by
  exact congrArg (fun y : ℝ => ⌊y/h⌋) (FiniteBoundary.affineRight_apply s b p x)

theorem affine_grid_injOn_off_collisions (K : Finset (ℝˣ × ℝ)) (h x : ℝ)
    (hx : x ∉ gridCollisions (fun p : K => (p.val.1 : ℝ)) (fun p : K => p.val.2) h) :
    Set.InjOn (affineGridValue h x) (K : Set (ℝˣ × ℝ)) := by
  have hi := grid_injective_off_collisions
    (fun p : K => (p.val.1 : ℝ)) (fun p : K => p.val.2) h x hx
  intro p hp q hq he
  have he' : (⟨p,hp⟩ : K)=⟨q,hq⟩ := hi he
  exact congrArg Subtype.val he'


theorem exists_small_affine_family_collisions (K : Finset (ℝˣ × ℝ))
    {η : ℝ} (hη : 0 < η) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ h, 0 < h → h ≤ ρ →
      MeasureTheory.volume (gridCollisions (fun p : K => (p.val.1 : ℝ))
        (fun p : K => p.val.2) h) ≤ ENNReal.ofReal η := by
  apply exists_small_grid_collisions _ _ _ hη
  intro p q he
  apply Subtype.ext
  have ha : (p.val.1 : ℝ)=(q.val.1 : ℝ) := congrArg (fun z : ℝ × ℝ => z.1) he
  have hb : p.val.2=q.val.2 := congrArg (fun z : ℝ × ℝ => z.2) he
  exact Prod.ext (Units.ext ha) hb

theorem affine_right_grid_boundary (F : Finset (ℝˣ × ℝ)) (s : ℝˣ) (b h x : ℝ)
    (δ : ℝ≥0∞)
    (hδ : (((F ∪ F.image (FiniteBoundary.affineRight s b)) \
      (F ∩ F.image (FiniteBoundary.affineRight s b))).card : ℝ≥0∞) ≤
      δ*(F ∪ F.image (FiniteBoundary.affineRight s b)).card)
    (hx : x ∉ gridCollisions
      (fun p : ↥(F ∪ F.image (FiniteBoundary.affineRight s b)) => (p.val.1 : ℝ))
      (fun p : ↥(F ∪ F.image (FiniteBoundary.affineRight s b)) => p.val.2) h) :
    (((F.image (affineGridValue h x) ∪ F.image (affineGridValue h ((s : ℝ)*x+b))) \
      (F.image (affineGridValue h x) ∩ F.image (affineGridValue h ((s : ℝ)*x+b)))).card : ℝ≥0∞) ≤
      δ*(F.image (affineGridValue h x) ∪ F.image (affineGridValue h ((s : ℝ)*x+b))).card := by
  have he : (F.image (FiniteBoundary.affineRight s b)).image (affineGridValue h x)=
      F.image (affineGridValue h ((s : ℝ)*x+b)) := by
    simp only [Finset.image_image,Function.comp_def,affineGridValue_right]
  have ht := image_disagreement_ratio_of_injOn F (F.image (FiniteBoundary.affineRight s b))
    (affineGridValue h x) (affine_grid_injOn_off_collisions _ h x hx) δ hδ
  simpa only [he] using ht

theorem affineGridValue_subtype_image (F : Finset (ℝˣ × ℝ)) (h x : ℝ) :
    (Finset.univ.image (fun p : F => affineGridValue h x p.val))=
      F.image (affineGridValue h x) := by
  rw [Finset.univ_eq_attach]
  change F.attach.image ((affineGridValue h x) ∘ Subtype.val)=F.image (affineGridValue h x)
  rw [← Finset.image_image,Finset.attach_image_val]

theorem affine_priority_samples_boundary (F : Finset (ℝˣ × ℝ)) (s : ℝˣ) (b h x : ℝ)
    (C : Finset ℤ)
    (hC : ∀ p : F, affineGridValue h x p.val ∈ C)
    (hCs : ∀ p : F, affineGridValue h ((s : ℝ)*x+b) p.val ∈ C)
    (δ : ℝ≥0∞)
    (hδ : (((F ∪ F.image (FiniteBoundary.affineRight s b)) \
      (F ∩ F.image (FiniteBoundary.affineRight s b))).card : ℝ≥0∞) ≤
      δ*(F ∪ F.image (FiniteBoundary.affineRight s b)).card)
    (hx : x ∉ gridCollisions
      (fun p : ↥(F ∪ F.image (FiniteBoundary.affineRight s b)) => (p.val.1 : ℝ))
      (fun p : ↥(F ∪ F.image (FiniteBoundary.affineRight s b)) => p.val.2) h) :
    let A := gridSample C (fun p : F => affineGridValue h x p.val)
    let B := gridSample C (fun p : F => affineGridValue h ((s : ℝ)*x+b) p.val)
    (((A ∪ B) \ (A ∩ B)).card : ℝ≥0∞) ≤ δ*(A ∪ B).card := by
  apply gridSample_disagreement_ratio C _ _ hC hCs δ
  simpa only [affineGridValue_subtype_image] using affine_right_grid_boundary F s b h x δ hδ hx

end TransposeFollowup.AffineMotion
