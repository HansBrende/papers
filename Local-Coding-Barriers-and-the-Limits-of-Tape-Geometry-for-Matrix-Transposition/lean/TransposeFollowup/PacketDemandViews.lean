import TransposeFollowup.InverseLocalPackets
import TransposeFollowup.PacketInformation

/-! Concrete endpoint recovery for the promised-family packet theorem.
The only private observation at receiver j is its original input row. -/

namespace TransposeFollowup.InverseLocalPacketCode

open Classical
set_option autoImplicit false

variable {d b B : ℕ} (C : InverseLocalPacketCode d b B)

noncomputable def latentRowComponents (U : Finset (Finset (MatrixBit d b)))
    (i : Fin d) : Finset U :=
  Finset.univ.filter (fun S => ∃ v ∈ S.val, v.1 ∈ C.bank.support i)

noncomputable def componentVariables {Ω : Type*}
    (U : Finset (Finset (MatrixBit d b))) (X : Ω → FiniteMatrix d b) :=
  coordinateBlockViews U (fun x => C.bank.recode (X x))

noncomputable def publicView {Ω : Type*}
    (U : Finset (Finset (MatrixBit d b))) (X : Ω → FiniteMatrix d b) :=
  fun x => (bitView (CoordinateSystem.outsideCoordinates U) (C.bank.recode (X x)),
    C.broadcast (X x))

theorem originalRow_factors {Ω : Type*}
    (U : Finset (Finset (MatrixBit d b))) (X : Ω → FiniteMatrix d b) (i : Fin d) :
    (fun x => X x i).FactorsThrough (fun x =>
      (C.publicView U X x, finiteView (C.latentRowComponents U i) (C.componentVariables U X x))) := by
  intro x y h
  apply C.row_eq_of_component_views U i
  · intro v hv
    have he := congrArg (fun z :
      ((MatrixBit d b → Bool) × (Fin B → Bool)) × (U → MatrixBit d b → Bool) => z.1.1) h
    have hmem : v ∈ CoordinateSystem.outsideCoordinates U := by
      simp only [CoordinateSystem.outsideCoordinates, Finset.mem_sdiff,
        Finset.mem_univ, true_and, Finset.mem_biUnion, id_eq]
      simpa only [Finset.mem_biUnion, id_eq] using hv
    exact (bitView_eq_iff _ _ _).mp he v hmem
  · intro S hS v hv
    obtain ⟨hSU, w, hw, hwi⟩ := Finset.mem_filter.mp hS
    have he := congrArg (fun z :
      ((MatrixBit d b → Bool) × (Fin B → Bool)) × (U → MatrixBit d b → Bool) => z.2) h
    have hmem : (⟨S, hSU⟩ : U) ∈ C.latentRowComponents U i :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, w, hw, hwi⟩
    have hb := (finiteView_eq_iff _ _ _).mp he ⟨S, hSU⟩ hmem
    exact (@bitView_eq_iff (MatrixBit d b) (Classical.decEq _) S _ _).mp hb v hv

theorem originalColumn_factors {Ω : Type*}
    (U : Finset (Finset (MatrixBit d b))) (X : Ω → FiniteMatrix d b)
    (hc : C.CorrectOn (Set.range X)) (j : Fin d) :
    (fun x => transposed (X x) j).FactorsThrough (fun x =>
      (C.publicView U X x, finiteView (C.latentRowComponents U j) (C.componentVariables U X x))) := by
  intro x y h
  apply C.column_eq_of_same_view hc ⟨x, rfl⟩ ⟨y, rfl⟩
  · exact congrArg (fun z :
      ((MatrixBit d b → Bool) × (Fin B → Bool)) × (U → MatrixBit d b → Bool) => z.1.2) h
  · exact C.originalRow_factors U X j h

theorem latentRowComponents_disjoint
    {G : SimpleGraph (Fin d)} (hG : C.LocalTo G) {ell : ℕ}
    (U : Finset (Finset (MatrixBit d b)))
    (hU : ∀ S ∈ U, S ∈ C.system.components ∧ S.card ≤ ell)
    {i j : Fin d} (hfar : ¬ InverseSupportNear C.bank.support G ell i j) :
    Disjoint (C.latentRowComponents U i) (C.latentRowComponents U j) := by
  apply Finset.disjoint_left.mpr
  intro S hi hj
  obtain ⟨_, v, hv, hvi⟩ := Finset.mem_filter.mp hi
  obtain ⟨_, w, hw, hwj⟩ := Finset.mem_filter.mp hj
  exact hfar ⟨v.1, hvi, w.1, hwj,
    C.component_coordinates_near hG (hU S.val S.property).1
      (hU S.val S.property).2 hv hw⟩

noncomputable def farCoordinates (G : SimpleGraph (Fin d)) (ell : ℕ) :
    Finset (MatrixBit d b) := Finset.univ \ inverseNearBits C.bank.support G ell

theorem far_endpoints {G : SimpleGraph (Fin d)} {ell : ℕ}
    (v : C.farCoordinates G ell) :
    v.val.1 ≠ v.val.2.1 ∧
      ¬ (inverseSupportGraph C.bank.support G ell).Adj v.val.1 v.val.2.1 := by
  have hnot := (Finset.mem_sdiff.mp v.property).2
  have h := fun hn => hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩)
  exact ⟨fun he => h (Or.inl he), fun he => h (Or.inr he.2)⟩

theorem far_source_factors {Ω : Type*}
    (U : Finset (Finset (MatrixBit d b))) (X : Ω → FiniteMatrix d b)
    {G : SimpleGraph (Fin d)} {ell : ℕ} (v : C.farCoordinates G ell) :
    (fun x => matrixBits (X x) v.val).FactorsThrough (fun x =>
      (C.publicView U X x,
        finiteView (C.latentRowComponents U v.val.1) (C.componentVariables U X x))) := by
  intro x y h
  exact congrFun (congrFun (C.originalRow_factors U X v.val.1 h) v.val.2.1) v.val.2.2

theorem far_receiver_factors {Ω : Type*}
    (U : Finset (Finset (MatrixBit d b))) (X : Ω → FiniteMatrix d b)
    (hc : C.CorrectOn (Set.range X))
    {G : SimpleGraph (Fin d)} {ell : ℕ} (v : C.farCoordinates G ell) :
    (fun x => matrixBits (X x) v.val).FactorsThrough (fun x =>
      (C.publicView U X x,
        finiteView (C.latentRowComponents U v.val.2.1) (C.componentVariables U X x))) := by
  intro x y h
  have he := congrFun (congrFun (C.originalColumn_factors U X hc v.val.2.1 h) v.val.1) v.val.2.2
  simpa only [transposed_apply, matrixBits] using he

end TransposeFollowup.InverseLocalPacketCode
