import TransposeFollowup.SeparatorRecord
import TransposeFollowup.SeparatorCount
import TransposeFollowup.FiniteBudgets
import TransposeFollowup.LeafAggregation

/-! Actual finite leaf labels and their virtual full-input fibers. -/

namespace TransposeFollowup.RowCode

open Classical
set_option autoImplicit false

noncomputable def observedKey {n b : ℕ} {H : Type*}
    (C : RowCode n b H) (S : H → List Bool → Finset (Fin n)) (x : FiniteMatrix n b) :
    H × List Bool :=
  (C.helper x, augmentedTranscript (C.protocol (C.helper x)) (S (C.helper x)) x)

open Classical in
noncomputable def leafSet {n b : ℕ} {H : Type*}
    (C : RowCode n b H) (F : Finset (FiniteMatrix n b))
    (S : H → List Bool → Finset (Fin n)) : Finset (H × List Bool) := F.image (C.observedKey S)

abbrev Leaf {n b : ℕ} {H : Type*} (C : RowCode n b H)
    (F : Finset (FiniteMatrix n b)) (S : H → List Bool → Finset (Fin n)) := ↥(C.leafSet F S)

noncomputable def leafOf {n b : ℕ} {H : Type*}
    (C : RowCode n b H) (F : Finset (FiniteMatrix n b))
    (S : H → List Bool → Finset (Fin n)) (x : F) : C.Leaf F S :=
  ⟨C.observedKey S x.val, Finset.mem_image.mpr ⟨x.val, x.property, rfl⟩⟩

noncomputable def leafRepresentative {n b : ℕ} {H : Type*}
    (C : RowCode n b H) (F : Finset (FiniteMatrix n b))
    (S : H → List Bool → Finset (Fin n)) (l : C.Leaf F S) : FiniteMatrix n b :=
  Classical.choose (Finset.mem_image.mp l.property)

theorem leafRepresentative_spec {n b : ℕ} {H : Type*}
    (C : RowCode n b H) (F : Finset (FiniteMatrix n b))
    (S : H → List Bool → Finset (Fin n)) (l : C.Leaf F S) :
    C.leafRepresentative F S l ∈ F ∧ C.observedKey S (C.leafRepresentative F S l) = l.val :=
  Classical.choose_spec (Finset.mem_image.mp l.property)

theorem leafRepresentative_key {n b : ℕ} {H : Type*}
    (C : RowCode n b H) (F : Finset (FiniteMatrix n b))
    (S : H → List Bool → Finset (Fin n)) (l : C.Leaf F S) :
    C.helper (C.leafRepresentative F S l) = l.val.1 ∧
      augmentedTranscript (C.protocol l.val.1) (S l.val.1) (C.leafRepresentative F S l) = l.val.2 := by
  have h := (C.leafRepresentative_spec F S l).2
  have hz := congrArg Prod.fst h
  have hm := congrArg Prod.snd h
  change C.helper (C.leafRepresentative F S l) = l.val.1 at hz
  refine ⟨hz, ?_⟩
  simpa only [observedKey, hz] using hm

theorem leafOf_surjective {n b : ℕ} {H : Type*}
    (C : RowCode n b H) (F : Finset (FiniteMatrix n b))
    (S : H → List Bool → Finset (Fin n)) : Function.Surjective (C.leafOf F S) := by
  intro l
  refine ⟨⟨C.leafRepresentative F S l, (C.leafRepresentative_spec F S l).1⟩, ?_⟩
  apply Subtype.ext
  exact (C.leafRepresentative_spec F S l).2

noncomputable def leafVolume {n b : ℕ} {H : Type*}
    (C : RowCode n b H) (F : Finset (FiniteMatrix n b))
    (S : H → List Bool → Finset (Fin n)) (l : C.Leaf F S) : ℕ :=
  fiberCard (augmentedTranscript (C.protocol l.val.1) (S l.val.1)) l.val.2

theorem leafVolume_pos {n b : ℕ} {H : Type*}
    (C : RowCode n b H) (F : Finset (FiniteMatrix n b))
    (S : H → List Bool → Finset (Fin n)) (l : C.Leaf F S) : 0 < C.leafVolume F S l := by
  classical
  let : DecidablePred (fun x => augmentedTranscript (C.protocol l.val.1) (S l.val.1) x = l.val.2) :=
    fun _ => Classical.propDecidable _
  apply Finset.card_pos.mpr
  refine ⟨C.leafRepresentative F S l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  exact (C.leafRepresentative_key F S l).2

theorem leafVolume_budget {n b : ℕ} {H : Type*}
    (C : RowCode n b H) (F : Finset (FiniteMatrix n b))
    (S : H → List Bool → Finset (Fin n)) (h : H) :
    pushforward (fun l : C.Leaf F S => (C.leafVolume F S l : ℝ) / (2 : ℝ) ^ (n * n * b))
      (fun l => l.val.1) h ≤ 1 := by
  simpa only [leafVolume, card_finiteMatrix, Nat.cast_pow, Nat.cast_ofNat] using
    conditional_fiber_budget (fun l : C.Leaf F S => l.val) Subtype.val_injective
      (fun h => augmentedTranscript (C.protocol h) (S h)) h

theorem leafCode_budget {n b : ℕ} {H : Type*}
    (C : RowCode n b H) (F : Finset (FiniteMatrix n b))
    (S : H → List Bool → Finset (Fin n)) (h : H) :
    pushforward (fun l : C.Leaf F S => (1 / 2 : ℝ) ^ l.val.2.length)
      (fun l => l.val.1) h ≤ 1 := by
  apply conditional_prefix_budget (fun l : C.Leaf F S => l.val) Subtype.val_injective
    (fun h => augmentedTranscript (C.protocol h) (S h))
    (fun h => augmentedTranscript_prefixFree (C.protocol h) (S h)) _ h
  intro l
  exact ⟨C.leafRepresentative F S l, (C.leafRepresentative_key F S l).2⟩

theorem leaf_key_data {n b : ℕ} {H : Type*}
    (C : RowCode n b H) (F : Finset (FiniteMatrix n b))
    (S : H → List Bool → Finset (Fin n)) (l : C.Leaf F S)
    (x : FiniteMatrix n b) (hk : C.observedKey S x = l.val) :
    C.helper x = l.val.1 ∧
      C.transcript x = (C.protocol l.val.1).run (C.leafRepresentative F S l) ∧
      ∀ i ∈ S l.val.1 ((C.protocol l.val.1).run (C.leafRepresentative F S l)),
        x i = C.leafRepresentative F S l i := by
  have hz := congrArg Prod.fst hk
  change C.helper x = l.val.1 at hz
  have he := congrArg Prod.snd hk
  change augmentedTranscript (C.protocol (C.helper x)) (S (C.helper x)) x = l.val.2 at he
  rw [hz, ← (C.leafRepresentative_key F S l).2] at he
  have hdata := (augmentedTranscript_eq_iff_right _ _ _ _).mp he
  exact ⟨hz, by simpa only [transcript, hz] using hdata.1, hdata.2⟩

noncomputable def leafLoss {n b : ℕ} {H κ : Type*} [DecidableEq κ]
    (C : RowCode n b H) (F : Finset (FiniteMatrix n b))
    (S : H → List Bool → Finset (Fin n)) (component : H → List Bool → Fin n → κ)
    (l : C.Leaf F S) : ℕ :=
  let m := (C.protocol l.val.1).run (C.leafRepresentative F S l)
  (internalFreeBits (b := b) (S l.val.1 m) (component l.val.1 m)).card

/-- The actual correct leaf fibers satisfy the hypotheses of aggregation.
Every loss and volume here is derived from the given row protocol. -/
theorem leaf_log_bound {n b : ℕ} {H κ : Type*} [Fintype κ] [DecidableEq κ]
    (C : RowCode n b H) (F : Finset (FiniteMatrix n b)) (hc : C.CorrectOn (F : Set _))
    (S : H → List Bool → Finset (Fin n)) (component : H → List Bool → Fin n → κ)
    (hsep : ∀ x ∈ F, (C.protocol (C.helper x)).Along
      (PublicProtocol.Separated (S (C.helper x) (C.transcript x))
        (component (C.helper x) (C.transcript x))) (C.transcript x))
    (l : C.Leaf F S) (hpos : 0 < fiberCard (C.leafOf F S) l) :
    2 * Real.log (fiberCard (C.leafOf F S) l : ℝ) ≤
      Real.log (C.leafVolume F S l : ℝ) + (C.leafLoss F S component l : ℝ) * Real.log 2 := by
  classical
  let : DecidablePred (fun x : F => C.leafOf F S x = l) := fun _ => Classical.propDecidable _
  let A := Finset.univ.filter (fun x : F => C.leafOf F S x = l)
  have hA : A.Nonempty := Finset.card_pos.mp hpos
  have : Nonempty A := ⟨⟨hA.choose, hA.choose_spec⟩⟩
  let X := fun x : A => x.val.val
  let base := C.leafRepresentative F S l
  let m := (C.protocol l.val.1).run base
  have hdata : ∀ x : A, C.helper (X x) = l.val.1 ∧ C.transcript (X x) = m ∧
      ∀ i ∈ S l.val.1 m, X x i = base i := by
    intro x
    exact C.leaf_key_data F S l (X x)
      (congrArg Subtype.val (Finset.mem_filter.mp x.property).2)
  have hs : (C.protocol l.val.1).Along
      (PublicProtocol.Separated (S l.val.1 m) (component l.val.1 m)) m := by
    have h := hsep base (C.leafRepresentative_spec F S l).1
    have hzb : C.helper base = l.val.1 := (C.leafRepresentative_key F S l).1
    simpa only [transcript, hzb] using h
  have h := C.separator_leaf_log_card (F : Set _) hc X
    (Subtype.val_injective.comp Subtype.val_injective) (fun x => x.val.property)
    l.val.1 m (S l.val.1 m) (component l.val.1 m) base rfl hs
    (fun x => (hdata x).1) (fun x => (hdata x).2.1) (fun x => (hdata x).2.2)
  have hcardA : Fintype.card A = fiberCard (C.leafOf F S) l := by
    exact Fintype.card_coe A
  have hcardR : (protocolFiberBits (C.protocol l.val.1) m (S l.val.1 m) base).card =
      C.leafVolume F S l := by
    rw [card_protocolFiberBits_eq_fiberCard]
    exact congrArg (fiberCard (augmentedTranscript (C.protocol l.val.1) (S l.val.1)))
      (C.leafRepresentative_key F S l).2
  rw [hcardA, hcardR] at h
  exact h

end TransposeFollowup.RowCode
