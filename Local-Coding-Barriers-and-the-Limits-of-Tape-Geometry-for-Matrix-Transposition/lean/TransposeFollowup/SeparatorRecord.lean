import TransposeFollowup.ProtocolRectangle
import TransposeFollowup.RefinedPrefix
import TransposeFollowup.EntropyFibers

/-! An analysis-only separator record. Its coordinate order is fixed by the
finite set; no algorithmic claim about enumerating it on tapes is made. -/

namespace TransposeFollowup

open scoped Pointwise
set_option autoImplicit false

noncomputable def separatorEncode {n b : ℕ} (S : Finset (Fin n)) (x : FiniteMatrix n b) :
    List Bool := (separatorBits S).toList.map (matrixBits x)

theorem card_separatorBits {n b : ℕ} (S : Finset (Fin n)) :
    (separatorBits (b := b) S).card = n * b * S.card := by
  have heq : separatorBits (b := b) S = S ×ˢ (Finset.univ : Finset (Fin n × Fin b)) := by
    ext i
    simp only [separatorBits, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_product, and_true]
  rw [heq, Finset.card_product]
  simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
  ring

theorem separatorEncode_length {n b : ℕ} (S : Finset (Fin n)) (x : FiniteMatrix n b) :
    (separatorEncode S x).length = n * b * S.card := by
  simp only [separatorEncode, List.length_map, Finset.length_toList, card_separatorBits]

theorem separatorEncode_eq_iff {n b : ℕ} (S : Finset (Fin n)) (x y : FiniteMatrix n b) :
    separatorEncode S x = separatorEncode S y ↔ ∀ i ∈ S, x i = y i := by
  simp only [separatorEncode, List.map_inj_left, Finset.mem_toList,
    separatorBits, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h i hi
    funext j t
    exact h (i, (j, t)) hi
  · intro h i hi
    exact congrFun (congrFun (h i.1 hi) i.2.1) i.2.2

noncomputable def augmentedTranscript {n b : ℕ}
    (p : PublicProtocol (Fin n) (fun _ => Row n b))
    (S : List Bool → Finset (Fin n)) (x : FiniteMatrix n b) : List Bool :=
  p.run x ++ separatorEncode (S (p.run x)) x

theorem augmentedTranscript_length {n b : ℕ}
    (p : PublicProtocol (Fin n) (fun _ => Row n b))
    (S : List Bool → Finset (Fin n)) (x : FiniteMatrix n b) :
    (augmentedTranscript p S x).length = (p.run x).length + n * b * (S (p.run x)).card := by
  simp only [augmentedTranscript, List.length_append, separatorEncode_length]

theorem augmentedTranscript_prefixFree {n b : ℕ}
    (p : PublicProtocol (Fin n) (fun _ => Row n b))
    (S : List Bool → Finset (Fin n)) :
    InformationTheory.IsPrefixFree (Set.range (augmentedTranscript p S)) := by
  apply prefix_refinement p.run (fun x => separatorEncode (S (p.run x)) x) p.run_prefixFree
  intro x y hxy
  simp only [separatorEncode_length, hxy]

theorem augmentedTranscript_eq_iff {n b : ℕ}
    (p : PublicProtocol (Fin n) (fun _ => Row n b))
    (S : List Bool → Finset (Fin n)) (x y : FiniteMatrix n b) :
    augmentedTranscript p S x = augmentedTranscript p S y ↔
      p.run x = p.run y ∧ ∀ i ∈ S (p.run x), x i = y i := by
  constructor
  · intro hxy
    have h := hxy
    change p.run x ++ separatorEncode (S (p.run x)) x =
      p.run y ++ separatorEncode (S (p.run y)) y at h
    have hp : p.run x ++ separatorEncode (S (p.run x)) x <+:
        p.run y ++ separatorEncode (S (p.run y)) y := by rw [h]
    have hm := prefix_refinement_first p.run (fun x => separatorEncode (S (p.run x)) x)
      p.run_prefixFree hp
    refine ⟨hm, ?_⟩
    rw [hm] at h ⊢
    exact (separatorEncode_eq_iff _ x y).mp (List.append_cancel_left h)
  · rintro ⟨hm, hfix⟩
    unfold augmentedTranscript
    have he := (separatorEncode_eq_iff _ x y).mpr hfix
    rw [hm] at he ⊢
    rw [he]

theorem augmentedTranscript_eq_iff_right {n b : ℕ}
    (p : PublicProtocol (Fin n) (fun _ => Row n b))
    (S : List Bool → Finset (Fin n)) (x y : FiniteMatrix n b) :
    augmentedTranscript p S x = augmentedTranscript p S y ↔
      p.run x = p.run y ∧ ∀ i ∈ S (p.run y), x i = y i := by
  rw [augmentedTranscript_eq_iff]
  constructor <;> rintro ⟨hm, hfix⟩ <;> exact ⟨hm, by simpa only [hm] using hfix⟩

theorem card_protocolFiberBits_eq_fiberCard {n b : ℕ}
    (p : PublicProtocol (Fin n) (fun _ => Row n b))
    (S : List Bool → Finset (Fin n)) (base : FiniteMatrix n b) :
    (protocolFiberBits p (p.run base) (S (p.run base)) base).card =
      fiberCard (augmentedTranscript p S) (augmentedTranscript p S base) := by
  classical
  let : DecidablePred (fun x => augmentedTranscript p S x = augmentedTranscript p S base) :=
    fun _ => Classical.propDecidable _
  unfold fiberCard
  apply Finset.card_bij (fun x _ => bitsMatrix x)
  · intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (augmentedTranscript_eq_iff_right p S _ base).mpr (Finset.mem_filter.mp hx).2⟩
  · intro x _ y _ hxy
    exact congrArg matrixBits hxy
  · intro y hy
    refine ⟨matrixBits y, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (augmentedTranscript_eq_iff_right p S y base).mp (Finset.mem_filter.mp hy).2⟩

end TransposeFollowup
