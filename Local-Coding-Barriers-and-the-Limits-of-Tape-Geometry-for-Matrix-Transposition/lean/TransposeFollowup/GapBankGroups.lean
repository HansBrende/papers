import TransposeFollowup.AdaptiveForestRows
import Mathlib.Data.Finset.Powerset

/-! Grouping whole coordinate classes by their exact nonempty occupied
bucket set. Empty classes do not create an additional group. -/

namespace TransposeFollowup

open Classical
open scoped BigOperators
set_option autoImplicit false

abbrev BucketPattern (M K : ℕ) :=
  {U : Finset (Fin M) // U.Nonempty ∧ U.card ≤ K}

def bucketPatternCount (M K : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (min K M), M.choose (j + 1)

noncomputable def bucketPatternEquiv (M K : ℕ) :
    BucketPattern M K ≃ Σ j : Fin (min K M), (Finset.univ : Finset (Fin M)).powersetCard (j.val + 1) where
  toFun U :=
    ⟨⟨U.val.card - 1, by
      have hp := Finset.card_pos.mpr U.property.1
      have hc : U.val.card ≤ M := by simpa using Finset.card_le_univ U.val
      omega⟩,
      ⟨U.val, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, by
        have hp := Finset.card_pos.mpr U.property.1
        change U.val.card = (U.val.card - 1) + 1
        omega⟩⟩⟩
  invFun z := ⟨z.2.val, by
    have hc := (Finset.mem_powersetCard.mp z.2.property).2
    constructor
    · apply Finset.card_pos.mp
      omega
    · have hh := z.1.isLt
      omega⟩
  left_inv U := by apply Subtype.ext; rfl
  right_inv z := by
    rcases z with ⟨j, U⟩
    apply Sigma.ext
    · apply Fin.ext
      have hc := (Finset.mem_powersetCard.mp U.property).2
      simp only
      omega
    · change (⟨U.val, _⟩ : ↥((Finset.univ : Finset (Fin M)).powersetCard (U.val.card - 1 + 1))) ≍ U
      apply (Subtype.heq_iff_coe_eq ?_).mpr
      · rfl
      intro S
      have hc := (Finset.mem_powersetCard.mp U.property).2
      simp only [Finset.mem_powersetCard]
      change (S ⊆ Finset.univ ∧ S.card = (U.val.card - 1) + 1) ↔ _
      rw [hc]
      simp

theorem card_bucketPattern (M K : ℕ) :
    Fintype.card (BucketPattern M K) = bucketPatternCount M K := by
  rw [Fintype.card_congr (bucketPatternEquiv M K), Fintype.card_sigma]
  simp only [Fintype.card_coe, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  exact Fin.sum_univ_eq_sum_range (fun j => M.choose (j + 1)) (min K M)

variable {V A : Type*} [Fintype V] [DecidableEq A] {M K : ℕ}

noncomputable def occupiedBuckets (label : V → A) (bucket : V → Fin M) (a : A) :
    Finset (Fin M) := (Finset.univ.filter (fun v => label v = a)).image bucket

@[simp] theorem mem_occupiedBuckets (label : V → A) (bucket : V → Fin M)
    (a : A) (i : Fin M) :
    i ∈ occupiedBuckets label bucket a ↔ ∃ v, label v = a ∧ bucket v = i := by
  simp [occupiedBuckets]

theorem occupiedBuckets_self (label : V → A) (bucket : V → Fin M) (v : V) :
    bucket v ∈ occupiedBuckets label bucket (label v) := by
  exact (mem_occupiedBuckets _ _ _ _).mpr ⟨v, rfl, rfl⟩

noncomputable def bucketGroup (label : V → A) (bucket : V → Fin M)
    (hsize : ∀ a, (occupiedBuckets label bucket a).card ≤ K) (v : V) : BucketPattern M K :=
  ⟨occupiedBuckets label bucket (label v), ⟨⟨bucket v, occupiedBuckets_self _ _ _⟩, hsize _⟩⟩

theorem bucketGroup_eq (label : V → A) (bucket : V → Fin M)
    (hsize : ∀ a, (occupiedBuckets label bucket a).card ≤ K)
    {v w : V} (h : label v = label w) :
    bucketGroup label bucket hsize v = bucketGroup label bucket hsize w := by
  apply Subtype.ext
  simp only [bucketGroup, h]

theorem bucketGroup_contains (label : V → A) (bucket : V → Fin M)
    (hsize : ∀ a, (occupiedBuckets label bucket a).card ≤ K) (v : V) :
    bucket v ∈ (bucketGroup label bucket hsize v).val := occupiedBuckets_self _ _ _

end TransposeFollowup
