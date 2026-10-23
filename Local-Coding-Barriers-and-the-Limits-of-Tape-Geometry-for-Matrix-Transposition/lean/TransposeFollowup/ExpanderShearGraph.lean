import TransposeFollowup.ExpanderShearRationalBridge
import TransposeFollowup.ShearGapRecovery
import TransposeFollowup.AllSizeOverlapExpansion

/-! The existing unconditional rational expander supplies the actual incidence
matrices used by the shear. The ordered-graph address reversal is only a
combinatorial equivalence in the expansion proof, not an uncharged data move. -/
namespace TransposeFollowup.ExpanderShear
open Classical MeasureTheory Set
set_option autoImplicit false

noncomputable def incidence {m : ℕ} (edges : Finset (Fin m × Fin m)) :
    Matrix (Fin m) (Fin m) Bit := fun j i => if (i,j) ∈ edges then 1 else 0

noncomputable def rationalMatrix {c m : ℕ} (F : Fin c → RationalMobius) :
    Matrix (Fin m) (Fin m) Bit := incidence (overlapEdges (rationalFamilyMaps F) m)

def rowAddress {m : ℕ} : Row m → Fin (2*m)
  | .inl i => OrderedBipartite.left i
  | .inr j => OrderedBipartite.right j

theorem rowAddress_injective {m : ℕ} : Function.Injective (@rowAddress m) := by
  intro a b h
  cases a with
  | inl i => cases b with
    | inl j => exact congrArg Sum.inl (OrderedBipartite.left_injective h)
    | inr j => exact False.elim (OrderedBipartite.left_ne_right i j h)
  | inr i => cases b with
    | inl j => exact False.elim (OrderedBipartite.left_ne_right j i h.symm)
    | inr j => exact congrArg Sum.inr (OrderedBipartite.right_injective h)

noncomputable def rowAddressEquiv (m : ℕ) : Row m ≃ Fin (2*m) :=
  Equiv.ofBijective rowAddress ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨rowAddress_injective, by simp [Row]; omega⟩)

theorem coreGraph_address {m : ℕ} (edges : Finset (Fin m × Fin m)) (a b : Row m) :
    (coreGraph (incidence edges)).Adj a b ↔
      (OrderedBipartite.graph edges).Adj (rowAddress a) (rowAddress b) := by
  cases a with
  | inl i => cases b with
    | inr j => simp [coreGraph,incidence,rowAddress,OrderedBipartite.adj_left_right]
    | inl j =>
      change False ↔ _
      constructor
      · exact False.elim
      · intro h
        rw [OrderedBipartite.graph,SimpleGraph.fromEdgeSet_adj] at h
        obtain ⟨⟨e,he⟩,_⟩ := h
        rcases Sym2.eq_iff.mp he with h | h
        · exact OrderedBipartite.left_ne_right j e.val.2 h.2.symm
        · exact OrderedBipartite.left_ne_right i e.val.2 h.2.symm
  | inr i => cases b with
    | inl j =>
      calc
        _ ↔ (j,i) ∈ edges := by simp [coreGraph,incidence]
        _ ↔ (OrderedBipartite.graph edges).Adj (OrderedBipartite.left j)
            (OrderedBipartite.right i) := (OrderedBipartite.adj_left_right edges j i).symm
        _ ↔ _ := (OrderedBipartite.graph edges).adj_comm _ _
    | inr j =>
      change False ↔ _
      constructor
      · exact False.elim
      · intro h
        rw [OrderedBipartite.graph,SimpleGraph.fromEdgeSet_adj] at h
        obtain ⟨⟨e,he⟩,_⟩ := h
        rcases Sym2.eq_iff.mp he with h | h
        · exact OrderedBipartite.left_ne_right e.val.1 i h.1
        · exact OrderedBipartite.left_ne_right e.val.1 j h.1

theorem outsideNeighbors_equiv {V V' : Type*} [Fintype V] [Fintype V']
    [DecidableEq V] [DecidableEq V']
    (G : SimpleGraph V) [DecidableRel G.Adj] (G' : SimpleGraph V') [DecidableRel G'.Adj]
    (e : V ≃ V')
    (he : ∀ a b, G.Adj a b ↔ G'.Adj (e a) (e b)) (S : Finset V) :
    outsideNeighbors G' (S.image e) = (outsideNeighbors G S).image e := by
  ext v
  obtain ⟨u,rfl⟩ := e.surjective v
  simp only [outsideNeighbors, Finset.mem_sdiff, Finset.mem_biUnion,
    SimpleGraph.mem_neighborFinset, Finset.mem_image]
  constructor
  · rintro ⟨⟨v,⟨x,hx,rfl⟩,hxu⟩,hu⟩
    exact ⟨u,⟨⟨x,hx,(he x u).mpr hxu⟩,fun h => hu ⟨u,h,rfl⟩⟩,rfl⟩
  · rintro ⟨u',⟨⟨x,hx,hxu⟩,hu⟩,heq⟩
    have huu := e.injective heq
    subst u'
    exact ⟨⟨e x,⟨x,hx,rfl⟩,(he x u).mp hxu⟩,by
      rintro ⟨y,hy,hyu⟩
      exact hu ((e.injective hyu) ▸ hy)⟩

theorem rationalMatrix_row_support {c m : ℕ} (F : Fin c → RationalMobius) (j : Fin m) :
    (Finset.univ.filter (fun i => rationalMatrix F j i ≠ 0)).card ≤ rationalPageCount F := by
  let s := Finset.univ.filter (fun i => rationalMatrix F j i ≠ 0)
  have hs : s.image OrderedBipartite.left ⊆
      (overlapGraph (rationalFamilyMaps F) m).neighborFinset (OrderedBipartite.right j) := by
    intro u hu
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hu
    apply ((overlapGraph (rationalFamilyMaps F) m).mem_neighborFinset _ _).mpr
    apply SimpleGraph.Adj.symm
    apply (OrderedBipartite.adj_left_right _ _ _).mpr
    simpa [s,rationalMatrix,incidence] using hi
  calc
    s.card = (s.image OrderedBipartite.left).card :=
      (Finset.card_image_of_injective _ OrderedBipartite.left_injective).symm
    _ ≤ _ := Finset.card_le_card hs
    _ = _ := SimpleGraph.card_neighborFinset_eq_degree _ _
    _ ≤ rationalPageCount F := overlapGraph_degree_le _ _ _

theorem rationalMatrix_col_support {c m : ℕ} (F : Fin c → RationalMobius) (i : Fin m) :
    (Finset.univ.filter (fun j => rationalMatrix F j i ≠ 0)).card ≤ rationalPageCount F := by
  let s := Finset.univ.filter (fun j => rationalMatrix F j i ≠ 0)
  have hs : s.image OrderedBipartite.right ⊆
      (overlapGraph (rationalFamilyMaps F) m).neighborFinset (OrderedBipartite.left i) := by
    intro u hu
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hu
    apply ((overlapGraph (rationalFamilyMaps F) m).mem_neighborFinset _ _).mpr
    apply (OrderedBipartite.adj_left_right _ _ _).mpr
    simpa [s,rationalMatrix,incidence] using hj
  calc
    s.card = (s.image OrderedBipartite.right).card :=
      (Finset.card_image_of_injective _ OrderedBipartite.right_injective).symm
    _ ≤ _ := Finset.card_le_card hs
    _ = _ := SimpleGraph.card_neighborFinset_eq_degree _ _
    _ ≤ rationalPageCount F := overlapGraph_degree_le _ _ _

theorem rationalSymmetric_core_expansion {c m : ℕ} (F : Fin c → RationalMobius)
    (hm : 0 < m)
    (hmap : ∀ p, MapsTo (rationalFamilyMaps F p).map (rationalFamilyMaps F p).domain (Icc (0:ℝ) 1))
    (eps : ℝ) (heps : 0 ≤ eps)
    (hforward : ∀ A : Set ℝ, MeasurableSet A → A ⊆ Icc (0:ℝ) 1 → volume.real A ≤ 1/2 →
      (1+eps)*volume.real A ≤ volume.real (mapImageUnion (rationalFamilyMaps F) A))
    (S : Finset (Row m)) (hS : 2*S.card ≤ 2*m) :
    eps/2*S.card ≤ (outsideNeighbors (coreGraph (rationalMatrix (rationalSymmetricFamily F))) S).card := by
  let e := rowAddressEquiv m
  have hcard : (S.image e).card = S.card := Finset.card_image_of_injective _ e.injective
  have hs : 2*(S.image e).card ≤ Fintype.card (Fin (2*m)) := by simpa [hcard] using hS
  have h := symmetrizedGraph_vertex_expansion_all_sizes (rationalFamilyMaps F)
    hm hmap eps heps hforward (S.image e) hs
  have hedges : overlapEdges (rationalFamilyMaps (rationalSymmetricFamily F)) m =
      overlapEdges (symmetrizedMaps (rationalFamilyMaps F)) m := by
    rw [←rationalFamilyEdges_eq, rationalSymmetricEdges_eq]
  change eps/2*(S.image e).card ≤
    (outsideNeighbors (OrderedBipartite.graph (overlapEdges (symmetrizedMaps (rationalFamilyMaps F)) m)) (S.image e)).card at h
  rw [←hedges] at h
  have haddress := outsideNeighbors_equiv
    (coreGraph (rationalMatrix (rationalSymmetricFamily F)))
    (OrderedBipartite.graph (overlapEdges (rationalFamilyMaps (rationalSymmetricFamily F)) m)) e
    (coreGraph_address _) S
  have hc : ((outsideNeighbors (coreGraph (rationalMatrix (rationalSymmetricFamily F))) S).image e).card =
      (outsideNeighbors (coreGraph (rationalMatrix (rationalSymmetricFamily F))) S).card :=
    Finset.card_image_of_injective _ e.injective
  have hboundary := (congrArg Finset.card haddress).trans hc
  calc
    _ = eps/2*(S.image e).card := by rw [hcard]
    _ ≤ _ := h
    _ = _ := by exact_mod_cast hboundary

end TransposeFollowup.ExpanderShear
