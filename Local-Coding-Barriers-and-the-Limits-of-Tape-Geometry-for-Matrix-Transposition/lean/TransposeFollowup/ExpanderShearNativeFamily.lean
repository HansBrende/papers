import TransposeFollowup.ExpanderShearFamily
import TransposeFollowup.NativeExpanderShear

/-! One fixed rational family and one fixed native machine simultaneously
realize the expanding shear at every positive half-dimension. -/
namespace TransposeFollowup.ExpanderShear
open Classical
set_option autoImplicit false

/-- The witnesses precede the input dimension. The incidence in the native
output is exactly the matrix for which degree and expansion are proved. -/
theorem exists_fixed_native_shear :
    ∃ (r : ℕ) (F : Fin (r+1) → RationalMobius) (eta : ℝ) (Delta C : ℕ),
      0 < eta ∧ eta ≤ 1 ∧
      ∀ m : ℕ, 1 ≤ m →
        (∀ j : Fin m,
          (Finset.univ.filter (fun i => rationalMatrix F j i ≠ 0)).card ≤ Delta) ∧
        (∀ i : Fin m,
          (Finset.univ.filter (fun j => rationalMatrix F j i ≠ 0)).card ≤ Delta) ∧
        (∀ S : Finset (Row m), 2*S.card ≤ 2*m →
          eta*S.card ≤ (outsideNeighbors (coreGraph (rationalMatrix F)) S).card) ∧
        ∀ x : BoolBank m ((2*m)*Transpose.entryBits (2*m)),
          ∃ t ≤ C * Transpose.inputLength (2*m), ∃ c,
            Transpose.stepN (NativeExpanderShearMachine.nativeMachine F) (rawBank x) t
              (Transpose.init (NativeExpanderShearMachine.nativeMachine F)) = some c ∧
            Transpose.step (NativeExpanderShearMachine.nativeMachine F) (rawBank x) c = none ∧
            c.outRev = (rawBank (boolShear (rationalMatrix F) x)).reverse := by
  obtain ⟨r,F,eta,he,h1,hexp⟩ := exists_rational_shear_family
  refine ⟨r,F,eta,rationalPageCount F,NativeExpanderShearMachine.coefficient F,
    he,h1,?_⟩
  intro m hm
  refine ⟨rationalMatrix_row_support F,rationalMatrix_col_support F,
    hexp m (by omega),?_⟩
  intro x
  have hL : rationalMatrix (m := m) F =
      fun j i => if (i,j) ∈ overlapEdges (rationalFamilyMaps F) m then 1 else 0 := by
    ext j i
    simp only [rationalMatrix,ExpanderShear.incidence]
  simpa only [hL,NativeExpanderShearMachine.outputBank] using
    NativeExpanderShearMachine.native_shear F m hm x

end TransposeFollowup.ExpanderShear
