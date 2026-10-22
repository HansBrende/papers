import TransposeFollowup.BoundedCoordinatePacking
import Mathlib.Data.Set.Finite.Range

/-! Refine finitely many bounded coordinate patches by choosing one
point of the target set for each occupied finite offset-bin label. -/
namespace TransposeFollowup.BoundedCoordinatePacking
open Classical Set
set_option autoImplicit false

/-- One representative for each attained finite code, without finiteness of the domain. -/
theorem exists_finite_code_representatives {X L : Type*} [Fintype L] (code : X → L) :
    ∃ P : Finset X, P.card ≤ Fintype.card L ∧ ∀ x, ∃ e ∈ P, code e = code x := by
  classical
  let rep : Set.range code → X := fun z => Classical.choose z.property
  have hrep (z : Set.range code) : code (rep z) = z.val := Classical.choose_spec z.property
  refine ⟨Finset.univ.image rep, ?_, ?_⟩
  · exact Finset.card_image_le.trans
      (Fintype.card_le_of_injective Subtype.val Subtype.val_injective)
  · intro x
    exact ⟨rep ⟨code x, ⟨x, rfl⟩⟩,
      Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩, hrep _⟩

theorem exists_coordinate_refinement {X : Type*} (a : X → Fin 2 → Fin 2 → ℝ)
    {A : Set X} (F : Finset X) {N δ : ℝ} (hδ : 0 < δ)
    (hpatch : ∀ x ∈ A, ∃ f ∈ F, ∀ i j, |a x i j - a f i j| ≤ N) :
    ∃ E : Finset X, (E : Set X) ⊆ A ∧ E.card ≤ F.card * binCount N δ ^ 4 ∧
      ∀ x ∈ A, ∃ e ∈ E, ∀ i j, |a x i j - a e i j| < δ := by
  have hc : ∀ x : A, ∃ c : F, ∀ i j, |a x i j - a c i j| ≤ N := by
    intro x
    obtain ⟨c, hc, he⟩ := hpatch x x.2
    exact ⟨⟨c, hc⟩, he⟩
  choose center hcenter using hc
  let K := binCount N δ
  let Label := F × (Fin 2 → Fin 2 → Fin K)
  let code (x : A) : Label := (center x, fun i j =>
    ⟨bin N δ (a x i j - a (center x) i j), bin_lt hδ (hcenter x i j)⟩)
  obtain ⟨P, hcard, hrep⟩ := exists_finite_code_representatives code
  have hsize : Fintype.card Label = F.card * K ^ 4 := by
    simp only [Label, Fintype.card_prod, Fintype.card_coe, Fintype.card_fun,
      Fintype.card_fin, ← pow_mul]
  refine ⟨P.image Subtype.val, ?_, (Finset.card_image_le).trans (hcard.trans_eq hsize), ?_⟩
  · intro x hx
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hx
    exact y.2
  · intro x hx
    obtain ⟨e, he, hcode⟩ := hrep ⟨x, hx⟩
    refine ⟨e, Finset.mem_image.mpr ⟨e, he, rfl⟩, ?_⟩
    intro i j
    have hcent : center e = center ⟨x, hx⟩ := congrArg Prod.fst hcode
    have hbin := congrArg (fun z : Label => (z.2 i j).val) hcode
    have h := same_bin_close hδ (hcenter ⟨x, hx⟩ i j) (hcenter e i j) hbin.symm
    rw [hcent] at h
    convert h using 1
    congr 1
    ring

end TransposeFollowup.BoundedCoordinatePacking
