import TransposeFollowup.ExpanderShearNativeBridge
import TransposeFollowup.RationalPageOpcode
import Mathlib.Data.Finset.Sort

/-! The generated rational page masks select exactly the monotone matching
edges of their page. Hence the actual page stream computes the same shear
whose incidence graph is used by the entropy obstruction. -/
namespace TransposeFollowup.ExpanderShear
open Classical
set_option autoImplicit false

private theorem sorted_matching_masks {E : Type*} [Fintype E] {m : ℕ}
    (f g : E → Fin m) (hf : Function.Injective f) (hg : Function.Injective g)
    (hmono : ∀ e e', f e < f e' → g e < g e') (a b : Fin m → Bool)
    (ha : ∀ i, a i = true ↔ ∃ e, f e = i)
    (hb : ∀ j, b j = true ↔ ∃ e, g e = j) :
    (selectedIndices a).length = (selectedIndices b).length ∧
    ∀ j i, (j,i) ∈ maskEdges a b ↔ ∃ e, g e = j ∧ f e = i := by
  let : LinearOrder E := LinearOrder.lift' f hf
  let es := (Finset.univ : Finset E).sort (· ≤ ·)
  have hes : es.Nodup := Finset.sort_nodup _ _
  have hem (e : E) : e ∈ es := by simp [es]
  have hs : es.Pairwise (· ≤ ·) := Finset.pairwise_sort _ _
  have heq (u : E → Fin m) (hu : Function.Injective u)
      (hord : ∀ e e', f e ≤ f e' → u e ≤ u e')
      (c : Fin m → Bool) (hc : ∀ i, c i = true ↔ ∃ e, u e = i) :
      es.map u = selectedIndices c := by
    apply List.Perm.eq_of_pairwise' (r := (· ≤ ·))
    · rw [List.pairwise_map]
      exact hs.imp (fun {e e'} h => hord e e' h)
    · exact ((List.pairwise_lt_finRange m).filter c).imp le_of_lt
    · apply (List.perm_ext_iff_of_nodup (hes.map hu)
        ((List.nodup_finRange m).filter c)).mpr
      intro i
      simp only [List.mem_filter, List.mem_finRange, true_and]
      constructor
      · intro hmem
        obtain ⟨e, _, h⟩ := List.mem_map.mp hmem
        exact (hc i).mpr ⟨e,h⟩
      · intro h
        obtain ⟨e,he⟩ := (hc i).mp h
        exact List.mem_map.mpr ⟨e,hem e,he⟩
  have he_f := heq f hf (fun _ _ h => h) a ha
  have he_g := heq g hg (fun e e' h => by
    rcases lt_or_eq_of_le h with h | h
    · exact le_of_lt (hmono e e' h)
    · exact le_of_eq (congrArg g (hf h))) b hb
  constructor
  · rw [←he_f,←he_g]; simp
  · intro j i
    have hz : es.zip es = es.map (fun e => (e,e)) := by
      induction es with
      | nil => rfl
      | cons e es ih => simp [ih]
    rw [maskEdges,←he_f,←he_g,List.zip_map,hz,List.map_map]
    simp only [Function.comp_def, Prod.map_apply, List.mem_map]
    constructor
    · rintro ⟨e,_,h⟩; exact ⟨e,congrArg Prod.fst h,congrArg Prod.snd h⟩
    · rintro ⟨e,hg,hf⟩; exact ⟨e,hem e,Prod.ext hg hf⟩

/-- Counts and edge identity for the actual masks emitted by the rational
page generator. The pair convention is (target, source). -/
theorem rational_page_masks {c m : ℕ} (F : Fin c → RationalMobius)
    (p : Fin (rationalPageCount F)) :
    (selectedIndices (fun i : Fin m => rationalOutgoingOn F i p)).length =
      (selectedIndices (fun j : Fin m => rationalIncomingOn F j p)).length ∧
    ∀ j i : Fin m,
      (j,i) ∈ maskEdges (fun i => rationalOutgoingOn F i p)
        (fun j => rationalIncomingOn F j p) ↔ rationalColor F i j = some p := by
  let D := overlapColoring (rationalFamilyMaps F) m
  let E := {e : overlapEdges (rationalFamilyMaps F) m // D.color e = p}
  have hf : Function.Injective (fun e : E => e.val.val.1) := by
    intro e e' h
    apply Subtype.ext
    exact D.same_color_row_injective (e.property.trans e'.property.symm) h
  have hg : Function.Injective (fun e : E => e.val.val.2) := by
    intro e e' h
    apply Subtype.ext
    exact D.same_color_column_injective (e.property.trans e'.property.symm) h
  have hm (e e' : E) (h : e.val.val.1 < e'.val.val.1) :
      e.val.val.2 < e'.val.val.2 :=
    D.same_color_strict (e.property.trans e'.property.symm) h
  have ha (i : Fin m) : rationalOutgoingOn F i p = true ↔ ∃ e : E, e.val.val.1 = i := by
    rw [rationalOutgoingOn_spec]
    change D.nestedPages.SourceEvent _ _ ↔ _
    rw [D.sourceEvent_left]
    constructor
    · rintro ⟨e,he,hp⟩; exact ⟨⟨e,hp⟩,he⟩
    · rintro ⟨e,he⟩; exact ⟨e.val,he,e.property⟩
  have hb (j : Fin m) : rationalIncomingOn F j p = true ↔ ∃ e : E, e.val.val.2 = j := by
    rw [rationalIncomingOn_spec]
    change D.nestedPages.TargetEvent _ _ ↔ _
    rw [D.targetEvent_right]
    constructor
    · rintro ⟨e,he,hp⟩; exact ⟨⟨e,hp⟩,he⟩
    · rintro ⟨e,he⟩; exact ⟨e.val,he,e.property⟩
  obtain ⟨hlen,hedge⟩ := sorted_matching_masks _ _ hf hg hm _ _ ha hb
  refine ⟨hlen,fun j i => ?_⟩
  rw [hedge, rationalColor_some_iff]
  constructor
  · rintro ⟨⟨⟨⟨i',j'⟩,he⟩,hp⟩,hj,hi⟩
    dsimp at hi hj
    subst i'; subst j'
    exact ⟨he,hp⟩
  · rintro ⟨he,hp⟩; exact ⟨⟨⟨(i,j),he⟩,hp⟩,rfl,rfl⟩

theorem rational_maskMatrix {c m : ℕ} (F : Fin c → RationalMobius)
    (p : Fin (rationalPageCount F)) (j i : Fin m) :
    maskMatrix (fun i => rationalOutgoingOn F i p) (fun j => rationalIncomingOn F j p) j i =
      if rationalColor F i j = some p then 1 else 0 := by
  simp only [maskMatrix_eq_incidence, (rational_page_masks F p).2]

/-- The sum of the actual generated page matrices is the simple graph
incidence, since each overlapping pair has one chosen page color. -/
theorem rational_page_matrix_sum {c m : ℕ} (F : Fin c → RationalMobius) :
    (∑ p : Fin (rationalPageCount F),
      maskMatrix (fun i : Fin m => rationalOutgoingOn F i p)
        (fun j : Fin m => rationalIncomingOn F j p)) =
      fun j i => if (i,j) ∈ overlapEdges (rationalFamilyMaps F) m then 1 else 0 := by
  funext j i
  simp only [Matrix.sum_apply, rational_maskMatrix]
  by_cases he : (i,j) ∈ overlapEdges (rationalFamilyMaps F) m
  · rw [rationalColor_eq_some F i j he]
    simp [he, Option.some.injEq]
  · rw [(rationalColor_none_iff F i j).mpr he]
    simp [he]

end TransposeFollowup.ExpanderShear
