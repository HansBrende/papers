import TransposeFollowup.TwoCover
import TransposeFollowup.UniformEntropy

/-! Full rectangular fibers and their possibly correlated correct subsets.
Rectangularity is imposed only on the containing full fiber. -/

namespace TransposeFollowup

open scoped BigOperators
set_option autoImplicit false

def CoordinateRectangle {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    (owner : ι → κ) (R : Finset (ι → Bool)) : Prop :=
  ∀ x, (∀ a, ∃ y ∈ R,
    bitView (ownedCoordinates owner a) x = bitView (ownedCoordinates owner a) y) → x ∈ R

def projectionSet {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    (owner : ι → κ) (R : Finset (ι → Bool)) (a : κ) : Finset (ι → Bool) :=
  R.image (bitView (ownedCoordinates owner a))

def rectangleProjection {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    (owner : ι → κ) (R : Finset (ι → Bool)) (x : R) :
    (a : κ) → projectionSet owner R a :=
  fun a => ⟨bitView (ownedCoordinates owner a) x.val,
    Finset.mem_image.mpr ⟨x.val, x.property, rfl⟩⟩

theorem rectangleProjection_bijective {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    (owner : ι → κ) (R : Finset (ι → Bool)) (hR : CoordinateRectangle owner R) :
    Function.Bijective (rectangleProjection owner R) := by
  classical
  constructor
  · intro x y hxy
    apply Subtype.ext
    funext i
    have h := congrArg (fun z => (z (owner i)).val i) hxy
    simpa [rectangleProjection, bitView, ownedCoordinates] using h
  · intro u
    let x := fun i => (u (owner i)).val i
    have hproj : ∀ a, bitView (ownedCoordinates owner a) x = (u a).val := by
      intro a
      obtain ⟨y, hy, heq⟩ := Finset.mem_image.mp (u a).property
      funext i
      by_cases hi : owner i = a
      · simp only [bitView, ownedCoordinates, Finset.mem_filter, Finset.mem_univ,
          true_and, hi, ite_true, x]
        rw [hi]
      · rw [← heq]
        simp [bitView, ownedCoordinates, hi]
    have hx : x ∈ R := by
      apply hR x
      intro a
      obtain ⟨y, hy, heq⟩ := Finset.mem_image.mp (u a).property
      exact ⟨y, hy, (hproj a).trans heq.symm⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    funext a
    apply Subtype.ext
    exact hproj a

theorem card_coordinateRectangle {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (owner : ι → κ) (R : Finset (ι → Bool)) (hR : CoordinateRectangle owner R) :
    R.card = ∏ a, (projectionSet owner R a).card := by
  have h := Fintype.card_congr (Equiv.ofBijective _ (rectangleProjection_bijective owner R hR))
  simpa only [Fintype.card_coe, Fintype.card_pi] using h

theorem sum_owned_entropy_le_log_rectangle {Ω ι κ : Type*}
    [Fintype Ω] [Nonempty Ω] [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (X : Ω → ι → Bool) (owner : ι → κ)
    (R : Finset (ι → Bool)) (hR : CoordinateRectangle owner R) (hXR : ∀ x, X x ∈ R) :
    (∑ a, coordinateEntropy p X (ownedCoordinates owner a)) ≤ Real.log (R.card : ℝ) := by
  classical
  have hb : ∀ a, coordinateEntropy p X (ownedCoordinates owner a) ≤
      Real.log ((projectionSet owner R a).card : ℝ) := by
    intro a
    exact observationEntropy_le_log_support p hp hp1 _ _
      (fun x => Finset.mem_image.mpr ⟨X x, hXR x, rfl⟩)
  have hpos : ∀ a, (projectionSet owner R a).card ≠ 0 := by
    intro a
    apply Finset.card_ne_zero.mpr
    exact ⟨bitView (ownedCoordinates owner a) (X (Classical.arbitrary Ω)),
      Finset.mem_image.mpr ⟨X (Classical.arbitrary Ω), hXR _, rfl⟩⟩
  calc
    _ ≤ ∑ a, Real.log ((projectionSet owner R a).card : ℝ) :=
      Finset.sum_le_sum (fun a _ => hb a)
    _ = Real.log (∏ a, ((projectionSet owner R a).card : ℝ)) := by
      symm
      apply Real.log_prod
      intro a _
      exact_mod_cast hpos a
    _ = Real.log (R.card : ℝ) := by
      rw [← Nat.cast_prod, ← card_coordinateRectangle owner R hR]

/-- Leaf inequality used by the adaptive protocol argument. It is valid
for every nonempty correlated subfamily of the rectangular virtual fiber. -/
theorem rectangle_decoding_entropy {Ω ι κ : Type*}
    [Fintype Ω] [Nonempty Ω] [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (X : Ω → ι → Bool) (owner demander : ι → κ)
    (R : Finset (ι → Bool)) (hR : CoordinateRectangle owner R) (hXR : ∀ x, X x ∈ R)
    (hdecode : ∀ a,
      (fun x => bitView (ownedCoordinates demander a) (X x)).FactorsThrough
        (fun x => bitView (ownedCoordinates owner a) (X x))) :
    2 * observationEntropy p X ≤ Real.log (R.card : ℝ) +
      coordinateEntropy p X (internalCoordinates owner demander) := by
  exact (two_cover_decoding_entropy p hp hp1 X owner demander hdecode).trans
    (add_le_add (sum_owned_entropy_le_log_rectangle p hp hp1 X owner R hR hXR) le_rfl)

end TransposeFollowup
