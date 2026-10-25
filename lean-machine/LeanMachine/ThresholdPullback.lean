import Mathlib
import LeanMachine.BucketChains
import LeanMachine.ThresholdCuts

/-!
# Finite threshold pullback for signed monotone row words

The primitive bands below retain all permitted paths. Their backwards
cardinality bounds are used to pay for ambiguous threshold crossings.
-/

namespace LeanMachine.ThresholdPullback

open Classical Finset
open scoped BigOperators
set_option autoImplicit false

/-- A radius-`r` band on a finite integer row interval. -/
def Band {n : ℕ} (r : ℕ) (x y : Fin n) : Prop :=
  x.val ≤ y.val + r ∧ y.val ≤ x.val + r

/-- All possible starting ancestors of a target set through one band. -/
noncomputable def bandPreimage {n : ℕ} (r : ℕ) (S : Finset (Fin n)) : Finset (Fin n) :=
  univ.filter (fun x => ∃ y ∈ S, Band r x y)

theorem band_single_card {n : ℕ} (r : ℕ) (y : Fin n) :
    (univ.filter (fun x => Band r x y)).card ≤ 2 * r + 1 := by
  have h : (univ.filter (fun x => Band r x y)).card ≤
      (Finset.Icc (y.val - r) (y.val + r)).card := by
    apply Finset.card_le_card_of_injOn Fin.val
    · intro x hx
      have hb := (Finset.mem_filter.mp hx).2
      dsimp [Band] at hb
      apply Finset.mem_Icc.mpr
      omega
    · exact Fin.val_injective.injOn
  rw [Nat.card_Icc] at h
  omega

/-- Each backwards band multiplies the number of possible ancestors by
at most `2*r+1`, including at interval boundaries. -/
theorem bandPreimage_card {n : ℕ} (r : ℕ) (S : Finset (Fin n)) :
    (bandPreimage r S).card ≤ (2 * r + 1) * S.card := by
  have heq : bandPreimage r S = S.biUnion (fun y => univ.filter (fun x => Band r x y)) := by
    ext x
    simp [bandPreimage]
  rw [heq]
  calc
    _ ≤ ∑ y ∈ S, (univ.filter (fun x => Band r x y)).card := Finset.card_biUnion_le
    _ ≤ ∑ _y ∈ S, (2 * r + 1) := Finset.sum_le_sum (fun y _ => band_single_card r y)
    _ = (2 * r + 1) * S.card := by simp [Nat.mul_comm]

/-- Starting values at which a radius-`r` band can cross a threshold. -/
noncomputable def bandAmbiguity (n r θ : ℕ) : Finset (Fin n) :=
  univ.filter (fun x => θ ≤ x.val + r ∧ x.val < θ + r)

theorem bandAmbiguity_card (n r θ : ℕ) : (bandAmbiguity n r θ).card ≤ 2 * r := by
  have h : (bandAmbiguity n r θ).card ≤ (Finset.Ico (θ - r) (θ + r)).card := by
    apply Finset.card_le_card_of_injOn Fin.val
    · intro x hx
      have hb := (Finset.mem_filter.mp hx).2
      apply Finset.mem_Ico.mpr
      omega
    · exact Fin.val_injective.injOn
  rw [Nat.card_Ico] at h
  omega

/-- Outside its charged rows, a band preserves the threshold comparison
simultaneously for every permitted endpoint. -/
theorem band_threshold_iff {n r θ : ℕ} {x y : Fin n}
    (hxy : Band r x y) (hx : x ∉ bandAmbiguity n r θ) :
    (θ ≤ x.val ↔ θ ≤ y.val) := by
  have hnot : ¬(θ ≤ x.val + r ∧ x.val < θ + r) := by
    simpa [bandAmbiguity] using hx
  dsimp [Band] at hxy
  omega

/-- A band preserves either polarity of a threshold outside the same
exceptional rows. -/
theorem band_cut_iff {n r : ℕ} (c : Cut n) {x y : Fin n}
    (hxy : Band r x y) (hx : x ∉ bandAmbiguity n r c.threshold) :
    c.holds x ↔ c.holds y := by
  have h := band_threshold_iff hxy hx
  cases hc : c.positive <;> simp [Cut.holds, hc] at * <;> omega

/-- Backwards image through the actual domain of a partial injection. -/
noncomputable def mapPreimage {n m : ℕ} (f : PartialMap n m)
    (S : Finset (Fin m)) : Finset (Fin n) :=
  (univ.filter (fun x : f.domain => f.toFun x ∈ S)).image Subtype.val

theorem mem_mapPreimage {n m : ℕ} (f : PartialMap n m)
    (S : Finset (Fin m)) (x : f.domain) :
    x.val ∈ mapPreimage f S ↔ f.toFun x ∈ S := by
  simp [mapPreimage]

/-- Strict monotonicity makes the backwards image injective even when
the partial map's domain has arbitrary gaps. -/
theorem mapPreimage_card {n m : ℕ} (f : PartialMap n m)
    (S : Finset (Fin m)) : (mapPreimage f S).card ≤ S.card := by
  apply Finset.card_image_le.trans
  apply Finset.card_le_card_of_injOn f.toFun
  · intro x hx
    exact (Finset.mem_filter.mp hx).2
  · exact f.injective.injOn

/-- A row word has one initial band and one further band after each
partial map. The intermediate row intervals may all differ. -/
inductive Word : ℕ → ℕ → Type
  | band (n : ℕ) : Word n n
  | step {n k m : ℕ} (f : PartialMap n k) (tail : Word k m) : Word n m

def Word.maps {n m : ℕ} : Word n m → ℕ
  | .band _ => 0
  | .step _ w => w.maps + 1

def Word.positive {n m : ℕ} : Word n m → Bool
  | .band _ => true
  | .step f w => f.positive == w.positive

/-- All attained paths through the word, with every radius-`r` band
interpreted as its full relation. -/
def Word.Rel {n m : ℕ} (r : ℕ) : Word n m → Fin n → Fin m → Prop
  | .band _, x, y => Band r x y
  | .step f w, x, y => ∃ z : f.domain, Band r x z.val ∧ w.Rel r (f.toFun z) y

private theorem error_recurrence (r ell : ℕ) :
    (2 * r + 1) * ((2 * r + 1) ^ (ell + 1) - 1) + 2 * r =
      (2 * r + 1) ^ (ell + 2) - 1 := by
  have hp : 1 ≤ (2 * r + 1) ^ (ell + 1) := Nat.one_le_pow _ _ (by omega)
  have heq : (2 * r + 1) * ((2 * r + 1) ^ (ell + 1) - 1) + (2 * r + 1) =
      (2 * r + 1) ^ (ell + 2) := by
    calc
      _ = (2 * r + 1) * (((2 * r + 1) ^ (ell + 1) - 1) + 1) := by ring
      _ = (2 * r + 1) * (2 * r + 1) ^ (ell + 1) := by rw [Nat.sub_add_cancel hp]
      _ = _ := by rw [show ell + 2 = (ell + 1) + 1 by omega, pow_succ]; ring
  omega

/-- Pull one threshold through an entire signed partial monotone word.
The comparison is exact for every attained endpoint of an uncharged row,
not only for one selected path or endpoint. -/
theorem word_threshold_pullback {n m : ℕ} (r : ℕ) (w : Word n m) (c : Cut m) :
    ∃ a : Cut n, ∃ T : Finset (Fin n),
      a.positive = (w.positive == c.positive) ∧
      T.card ≤ (2 * r + 1) ^ (w.maps + 1) - 1 ∧
      ∀ x, x ∉ T → ∀ y, w.Rel r x y → (a.holds x ↔ c.holds y) := by
  induction w with
  | band n =>
    refine ⟨c, bandAmbiguity n r c.threshold, ?_, ?_, ?_⟩
    · cases c.positive <;> rfl
    · simpa [Word.maps] using bandAmbiguity_card n r c.threshold
    · intro x hx y hxy
      exact band_cut_iff c hxy hx
  | @step n k m f w ih =>
    obtain ⟨b, U, hb, hU, hexact⟩ := ih c
    obtain ⟨a, ha, hfa⟩ := exists_pullback_cut f b
    let T := bandPreimage r (mapPreimage f U) ∪ bandAmbiguity n r a.threshold
    refine ⟨a, T, ?_, ?_, ?_⟩
    · rw [ha, hb]
      simp only [Word.positive]
      cases f.positive <;> cases w.positive <;> cases c.positive <;> rfl
    · have hT : T.card ≤ (2 * r + 1) * U.card + 2 * r := by
        calc
          T.card ≤ (bandPreimage r (mapPreimage f U)).card +
              (bandAmbiguity n r a.threshold).card := Finset.card_union_le _ _
          _ ≤ (2 * r + 1) * (mapPreimage f U).card + 2 * r :=
            Nat.add_le_add (bandPreimage_card r _) (bandAmbiguity_card _ _ _)
          _ ≤ (2 * r + 1) * U.card + 2 * r :=
            Nat.add_le_add_right (Nat.mul_le_mul_left _ (mapPreimage_card f U)) _
      have hT' := hT.trans (Nat.add_le_add_right (Nat.mul_le_mul_left (2 * r + 1) hU) (2 * r))
      simpa only [error_recurrence, Word.maps, Nat.add_assoc] using hT'
    · intro x hx y hxy
      obtain ⟨z, hxz, hzy⟩ := hxy
      have hxband : x ∉ bandPreimage r (mapPreimage f U) :=
        fun h => hx (Finset.mem_union_left _ h)
      have hxamb : x ∉ bandAmbiguity n r a.threshold :=
        fun h => hx (Finset.mem_union_right _ h)
      have hz : f.toFun z ∉ U := by
        intro h
        apply hxband
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, z.val,
          (mem_mapPreimage f U z).mpr h, hxz⟩
      exact (band_cut_iff a hxz hxamb).trans ((hfa z).trans (hexact _ hz _ hzy))

end LeanMachine.ThresholdPullback
