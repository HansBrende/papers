import TransposeFollowup.GapBankBucketEntropy

/-! The leaf bound for the actual public forest refinement. All geometric
premises are obtained from the original leaf graph and its row projection. -/

namespace TransposeFollowup

open Classical
open scoped BigOperators
set_option autoImplicit false

namespace GapBankCode

variable {d b sigma : ℕ} (C : GapBankCode d b sigma)

def LeafLocalTo (m : List Bool) (G : SimpleGraph (Fin d)) : Prop :=
  ∀ {v w : MatrixBit d b}, (C.protocol.interactionGraph m).Adj v w →
    v.1 = w.1 ∨ G.Adj v.1 w.1

theorem forest_leaf_entropy
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (X : Ω → FiniteMatrix d b) (hc : C.CorrectOn (Set.range X))
    (base : FiniteMatrix d b) (R M D : ℕ) (hR : 0 < R) (hM : 0 < M)
    (hd : 0 < d) (hD : 2 ≤ D)
    (hm : ∀ x, (AdaptiveForest.refined C.protocol R hR).run (C.bank.recode (X x)) =
      (AdaptiveForest.refined C.protocol R hR).run (C.bank.recode base))
    (hforest : (C.protocol.interactionGraph (C.transcript base)).IsAcyclic)
    (G : SimpleGraph (Fin d)) (hlocal : C.LeafLocalTo (C.transcript base) G)
    (hdegree : ∀ i, G.degree i ≤ D) {s : ℝ} (hs0 : 0 ≤ s) (hs : C.bank.StateBudget s) :
    observationEntropy p X ≤
      ((d * b * D^(2*R) * (d ⌈/⌉ M + 2 * sigma) : ℕ) +
        ((D^R + 1) * bucketPatternCount M (D^R) : ℕ) * s) * Real.log 2 +
      ((bucketPatternCount M (D^R) : ℝ) - 1) *
        (Real.log (((AdaptiveForest.refined C.protocol R hR).fullFiber
          ((AdaptiveForest.refined C.protocol R hR).run (C.bank.recode base))).card : ℝ) -
          observationEntropy p X) := by
  let B := RowBuckets.balanced d M hd hM
  let H := C.protocol.interactionGraph (C.transcript base)
  let label := AdaptiveForest.owner C.protocol R hR (C.transcript base)
  let r := (AdaptiveForest.residue H R hR).val
  let rows := nearVertices G (2*R)
  have hsize (a : MatrixBit d b) :
      (occupiedBuckets label (fun v => B.bucket v.1) a).card ≤ D^R := by
    have he : occupiedBuckets label (fun v => B.bucket v.1) a =
        (AdaptiveForest.classImage label Prod.fst a).image B.bucket := by
      ext i
      simp only [mem_occupiedBuckets, Finset.mem_image, AdaptiveForest.mem_classImage]
      constructor
      · rintro ⟨v, hv, hi⟩
        exact ⟨v.1, ⟨v, hv, rfl⟩, hi⟩
      · rintro ⟨j, ⟨v, hv, rfl⟩, hi⟩
        exact ⟨v, hv, hi⟩
    rw [he]
    apply Finset.card_image_le.trans
    exact AdaptiveForest.ancestor_class_card_le H G Prod.fst hlocal D hD hdegree hR r a
  have hclass (v w : MatrixBit d b) (he : label v = label w) : w.1 ∈ rows v.1 := by
    obtain ⟨walk, hw⟩ := AdaptiveForest.ancestor_class_rows_near H G Prod.fst hlocal hR he
    apply (mem_nearVertices G (2*R) _ _).mpr
    exact ⟨walk, by omega⟩
  have hballs (i : Fin d) : (rows i).card ≤ D^(2*R) :=
    AdaptiveForest.positive_ball_card_le G D hD hdegree (by omega) i
  have hpad (a : Fin M) : (B.paddedFiber sigma a).card ≤ d ⌈/⌉ M + 2*sigma := by
    dsimp [B, RowBuckets.balanced]
    apply RowBuckets.quotient_paddedFiber_card
  have hm' (x : Ω) : C.transcript (X x) = C.transcript base := by
    exact ((C.protocol.run_appendCoordinates_eq_iff
      (fun m => (AdaptiveForest.selectedPins C.protocol R hR m).toList) [] _ _).mp (hm x)).1
  apply C.bucket_leaf_entropy p hp hp1 X hc (C.transcript base) hm' B label
    hM (pow_pos (by omega) R) hsize
    ((AdaptiveForest.refined C.protocol R hR).fullFiber
      ((AdaptiveForest.refined C.protocol R hR).run (C.bank.recode base)))
  · exact AdaptiveForest.refined_rectangle_of_owner_factors C.protocol R hR
      (C.bank.recode base) hforest (B.groupedOwner label hsize)
      (fun v w he => bucketGroup_eq label (fun v => B.bucket v.1) hsize he)
  · intro x
    exact (PublicProtocol.mem_fullFiber _ _ _).mpr (hm x)
  · exact hballs
  · exact hclass
  · exact hpad
  · exact hs0
  · exact hs

end GapBankCode
end TransposeFollowup
