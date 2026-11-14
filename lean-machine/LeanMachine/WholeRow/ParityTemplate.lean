import LeanMachine.DisjointSumsPinned

/-! # Whole-row records for disjoint parity templates

Rows and columns may have different finite index types, and each cell may
carry finitely many lanes. Active parity blocks have arbitrary invertible
additive weights; pinned coordinates need only be disjoint from those
blocks. Recovery and invariance force the geometric compatibility used in
the incidence count. No linearity of the code or decoder is assumed.
-/

namespace LeanMachine.WholeRow

open Finset
open scoped BigOperators Classical
noncomputable section

variable {R J Λ κ A : Type*} [Fintype R] [Fintype J] [Fintype Λ] [Fintype κ]

/-- A lane coordinate, with row first and column second. -/
abbrev LaneCell (R J Λ : Type*) := R × J × Λ

/-- Every lane of every column in the selected helper rows. -/
def helperBundle (ρ : J → Finset R) (c : J) : Finset (LaneCell R J Λ) :=
  (ρ c) ×ˢ (univ ×ˢ univ)

/-- Whole-row recovery, stated by agreement rather than chosen decoder functions. -/
def RecoversFromRows (ρ : J → Finset R) (C : Set (LaneCell R J Λ → A)) : Prop :=
  ∀ v, ∀ x ∈ C, ∀ y ∈ C,
    Set.EqOn x y (↑(helperBundle (Λ := Λ) ρ v.2.1)) → x v = y v

/-- Recovery may also use a common raw record of the pinned coordinates. -/
def RecoversFromRowsGiven (ρ : J → Finset R) (E : Set (LaneCell R J Λ))
    (C : Set (LaneCell R J Λ → A)) : Prop :=
  ∀ v, ∀ x ∈ C, ∀ y ∈ C,
    Set.EqOn x y ((↑(helperBundle (Λ := Λ) ρ v.2.1)) ∪ E) → x v = y v

omit [Fintype R] in
/-- Unconditional recovery remains valid when the decoder receives a raw record. -/
theorem RecoversFromRows.given {ρ : J → Finset R} {C : Set (LaneCell R J Λ → A)}
    (h : RecoversFromRows ρ C) (E : Set (LaneCell R J Λ)) :
    RecoversFromRowsGiven ρ E C := by
  intro v x hx y hy hxy
  exact h v x hx y hy (hxy.mono Set.subset_union_left)

/-- Coordinates that are among their own column's helper rows. -/
def incidentCells (ρ : J → Finset R) : Finset (LaneCell R J Λ) :=
  univ.filter (fun v => v.1 ∈ ρ v.2.1)

/-- Columns sharing at least one helper row with column `c`. -/
def overlapColumns (ρ : J → Finset R) (c : J) : Finset J :=
  (ρ c).biUnion (fun r => univ.filter (fun j => r ∈ ρ j))

variable (D : DisjointSums (LaneCell R J Λ) κ) (ρ : J → Finset R)

/-- Active blocks completely visible in the bundle of one column. -/
def internalBlocks (c : J) : Finset κ :=
  univ.filter (fun k => D.support k ⊆ helperBundle ρ c)

/-- Active blocks all of whose coordinates are incident. -/
def incidentBlocks : Finset κ :=
  univ.filter (fun k => D.support k ⊆ incidentCells ρ)

/-- Exact union of the active syndromes that are recorded. -/
def recordBlocks : Finset κ :=
  incidentBlocks D ρ ∪ univ.biUnion (internalBlocks D ρ)

variable [AddCommGroup A] (θ : LaneCell R J Λ → A ≃+ A)
variable (E : Set (LaneCell R J Λ))
variable (hfree : ∀ k, ∀ v ∈ E, v ∉ D.support k)

include hfree in
private theorem internal_enclosure (v : LaneCell R J Λ) (k : κ)
    (h : (↑(D.support k) : Set (LaneCell R J Λ)) ⊆
      (↑(helperBundle (Λ := Λ) ρ v.2.1)) ∪ E) :
    k ∈ recordBlocks D ρ := by
  exact mem_union_right _ (mem_biUnion.mpr
    ⟨v.2.1, mem_univ _, mem_filter.mpr ⟨mem_univ _, fun u hu =>
      (h hu).resolve_right (fun he => hfree k u he hu)⟩⟩)

include hfree in
private theorem incident_enclosure (k : κ)
    (h : ∀ v ∈ D.support k,
      v ∈ (↑(helperBundle (Λ := Λ) ρ v.2.1) : Set (LaneCell R J Λ)) ∪ E) :
    k ∈ recordBlocks D ρ := by
  apply mem_union_left
  apply mem_filter.mpr
  refine ⟨mem_univ _, fun v hv => ?_⟩
  exact mem_filter.mpr ⟨mem_univ _, (mem_product.mp
    ((h v hv).resolve_right (fun he => hfree k v he hv))).1⟩

variable (C : Set (LaneCell R J Λ → A))
variable (hstable : ∀ x ∈ C, ∀ z : LaneCell R J Λ → A,
  D.weightedEncode θ z = 0 → Set.EqOn z 0 E → x + z ∈ C)

include hstable in
/-- The geometrically defined record has the exact attained-image count.
This is the pinned weighted theorem with the whole-row enclosures discharged. -/
theorem parity_record_card_eq (hrec : RecoversFromRowsGiven ρ E C) :
    Nat.card C = Nat.card ((D.withPins E hfree).weightedEncode θ).ker *
      Nat.card (D.pinnedRecord E θ (recordBlocks D ρ) '' C) := by
  exact D.card_eq_pinned_kernel_mul_record_image E hfree θ C hstable
    (fun v => (↑(helperBundle (Λ := Λ) ρ v.2.1)) ∪ E) (recordBlocks D ρ) hrec
    (internal_enclosure D ρ E hfree) (incident_enclosure D ρ E hfree)

include hstable hfree in
/-- Finite exact-record power bound, before replacing the record union by a sum. -/
theorem parity_card_le_record [Fintype A] (hrec : RecoversFromRowsGiven ρ E C) :
    Nat.card C ≤ Fintype.card A ^
      (Fintype.card (LaneCell R J Λ) - Fintype.card κ + (recordBlocks D ρ).card) := by
  simpa using
    D.card_le_pow_of_pinned_invariant_recovery E hfree θ C hstable
      (fun v => (↑(helperBundle (Λ := Λ) ρ v.2.1)) ∪ E) (recordBlocks D ρ) hrec
      (internal_enclosure D ρ E hfree) (incident_enclosure D ρ E hfree)

include hstable hfree in
omit [Fintype R] [Fintype κ] in
private theorem active_compatibility [Nontrivial A] (hC : C.Nonempty)
    (hrec : RecoversFromRowsGiven ρ E C) (v : LaneCell R J Λ)
    (hv : v ∉ helperBundle ρ v.2.1) (k : κ) (hvk : v ∈ D.support k) :
    (↑(D.support k) : Set (LaneCell R J Λ)) ⊆
      insert v (↑(helperBundle (Λ := Λ) ρ v.2.1) : Set (LaneCell R J Λ)) := by
  have h := (D.withPins E hfree).weighted_support_subset_insert_of_recovery θ C
    (fun x hx z hz =>
      let h := (D.withPins_encode_eq_zero_iff E hfree θ z).mp hz
      hstable x hx z h.1 h.2) hC
    ((↑(helperBundle (Λ := Λ) ρ v.2.1)) ∪ E) v (hrec v)
    (by
      rintro (hb | he)
      · exact hv hb
      · exact hfree k v he hvk) (Sum.inl k) hvk
  intro u hu
  rcases Set.mem_insert_iff.mp (h hu) with huv | hub
  · exact Set.mem_insert_iff.mpr (Or.inl huv)
  · exact Set.mem_insert_iff.mpr
      (Or.inr (hub.resolve_right (fun he => hfree k u he hu)))

omit [Fintype R] in
include hstable hfree in
/-- Every non-singleton internal active block lies in the helper-row / shared-column
rectangle. This includes incident coordinates, using their own row as witness. -/
theorem internal_support_subset_rectangle [Nontrivial A] (hC : C.Nonempty)
    (hrec : RecoversFromRowsGiven ρ E C) (c : J) (k : κ)
    (hk : k ∈ internalBlocks D ρ c) (hsize : 2 ≤ (D.support k).card) :
    D.support k ⊆ ((ρ c) ×ˢ ((overlapColumns ρ c) ×ˢ (univ : Finset Λ))) := by
  intro v hv
  have hsub := (mem_filter.mp hk).2
  have hrow : v.1 ∈ ρ c := (mem_product.mp (hsub hv)).1
  apply mem_product.mpr
  refine ⟨hrow, mem_product.mpr ⟨?_, mem_univ _⟩⟩
  apply mem_biUnion.mpr
  by_cases hi : v.1 ∈ ρ v.2.1
  · exact ⟨v.1, hrow, mem_filter.mpr ⟨mem_univ _, hi⟩⟩
  · obtain ⟨u, hu, huv⟩ := exists_mem_ne (by omega : 1 < (D.support k).card) v
    have hcompat := active_compatibility D ρ θ E hfree C hstable hC hrec v
      (by simpa [helperBundle] using hi) k hv hu
    have hub : u ∈ helperBundle ρ v.2.1 :=
      (Set.mem_insert_iff.mp hcompat).resolve_left huv
    exact ⟨u.1, (mem_product.mp (hsub hu)).1,
      mem_filter.mpr ⟨mem_univ _, (mem_product.mp hub).1⟩⟩

omit [Fintype R] [Fintype J] [Fintype Λ] [Fintype κ] in
private theorem block_count (K : Finset κ) (Z : Finset (LaneCell R J Λ))
    (r : ℕ) (hsize : ∀ k ∈ K, r ≤ (D.support k).card)
    (hsub : ∀ k ∈ K, D.support k ⊆ Z) : r * K.card ≤ Z.card := by
  calc
    r * K.card = ∑ _k ∈ K, r := by simp [Nat.mul_comm]
    _ ≤ ∑ k ∈ K, (D.support k).card := sum_le_sum hsize
    _ = (K.biUnion D.support).card :=
      (card_biUnion (fun k _ l _ hkl => D.disjoint hkl)).symm
    _ ≤ Z.card := card_le_card (biUnion_subset.mpr hsub)

/-- Incident lane count, retaining the exact sum of forward degrees. -/
theorem card_incidentCells :
    (incidentCells (Λ := Λ) ρ).card = Fintype.card Λ * ∑ c, (ρ c).card := by
  classical
  simp only [incidentCells, card_filter, Fintype.sum_prod_type]
  change (∑ r : R, ∑ c : J, ∑ _l : Λ, if r ∈ ρ c then 1 else 0) = _
  simp only [sum_const, card_univ, smul_eq_mul]
  rw [sum_comm]
  simp_rw [← mul_sum]
  simp

include hstable hfree in
/-- Exact incidence budget for the selected active blocks, including lanes.
The block size parameter need not be a uniform exact size. -/
theorem recordBlocks_card_bound [Nontrivial A] (hC : C.Nonempty)
    (hrec : RecoversFromRowsGiven ρ E C) (r : ℕ) (hr : 2 ≤ r)
    (hsize : ∀ k, r ≤ (D.support k).card) :
    r * (recordBlocks D ρ).card ≤ Fintype.card Λ *
      ((∑ c, (ρ c).card) + ∑ c, (ρ c).card * (overlapColumns ρ c).card) := by
  have hinc := block_count D (incidentBlocks D ρ) (incidentCells ρ) r
    (fun k _ => hsize k) (fun k hk => (mem_filter.mp hk).2)
  have hint (c : J) : r * (internalBlocks D ρ c).card ≤
      Fintype.card Λ * ((ρ c).card * (overlapColumns ρ c).card) := by
    have h := block_count D (internalBlocks D ρ c)
      (((ρ c) ×ˢ ((overlapColumns ρ c) ×ˢ (univ : Finset Λ)))) r
      (fun k _ => hsize k) (fun k hk =>
        internal_support_subset_rectangle D ρ θ E hfree C hstable hC hrec c k hk
          (hr.trans (hsize k)))
    simpa only [card_product, card_univ, Nat.mul_comm, Nat.mul_left_comm,
      Nat.mul_assoc] using h
  have hrecord : (recordBlocks D ρ).card ≤
      (incidentBlocks D ρ).card + ∑ c, (internalBlocks D ρ c).card :=
    (card_union_le _ _).trans (Nat.add_le_add_left card_biUnion_le _)
  calc
    r * (recordBlocks D ρ).card ≤
        r * ((incidentBlocks D ρ).card + ∑ c, (internalBlocks D ρ c).card) :=
      Nat.mul_le_mul_left r hrecord
    _ = r * (incidentBlocks D ρ).card + ∑ c, r * (internalBlocks D ρ c).card := by
      rw [Nat.mul_add, mul_sum]
    _ ≤ (incidentCells (Λ := Λ) ρ).card +
        ∑ c, Fintype.card Λ * ((ρ c).card * (overlapColumns ρ c).card) :=
      Nat.add_le_add hinc (sum_le_sum fun c _ => hint c)
    _ = _ := by rw [card_incidentCells, ← mul_sum, ← Nat.mul_add]

include hstable hfree in
/-- Finite whole-row parity-template bound with the exact incidence sum.
Empty codes and trivial alphabets are handled without compatibility premises. -/
theorem parity_card_le_incidence [Fintype A] (hrec : RecoversFromRowsGiven ρ E C)
    (r : ℕ) (hr : 2 ≤ r) (hsize : ∀ k, r ≤ (D.support k).card) :
    Nat.card C ≤ Fintype.card A ^ (Fintype.card (LaneCell R J Λ) - Fintype.card κ +
      (Fintype.card Λ * ((∑ c, (ρ c).card) +
        ∑ c, (ρ c).card * (overlapColumns ρ c).card)) / r) := by
  classical
  have hc := parity_card_le_record D ρ θ E hfree C hstable hrec
  cases subsingleton_or_nontrivial A with
  | inl h =>
    have hq : Fintype.card A = 1 := Fintype.card_eq_one_iff.mpr ⟨0, fun _ => Subsingleton.elim _ _⟩
    simpa only [hq, one_pow] using hc
  | inr h =>
    by_cases hC : C.Nonempty
    · apply hc.trans
      apply Nat.pow_le_pow_right Fintype.card_pos
      apply Nat.add_le_add_left
      apply (Nat.le_div_iff_mul_le (by omega : 0 < r)).mpr
      simpa only [Nat.mul_comm] using
        recordBlocks_card_bound D ρ θ E hfree C hstable hC hrec r hr hsize
    · rw [Set.not_nonempty_iff_eq_empty.mp hC]
      simp

omit [Fintype R] in
/-- Reverse degree controls the number of columns overlapping a helper bundle. -/
theorem overlapColumns_card_le (c : J) (Drev : ℕ)
    (hrev : ∀ r, (univ.filter (fun j => r ∈ ρ j)).card ≤ Drev) :
    (overlapColumns ρ c).card ≤ (ρ c).card * Drev :=
  card_biUnion_le_card_mul (ρ c) _ Drev (fun r _ => hrev r)

omit [Fintype R] in
/-- Coarse incidence budget, with the exact number of columns and lanes. -/
theorem incidence_budget_le (w Drev : ℕ)
    (hforward : ∀ c, (ρ c).card ≤ w)
    (hrev : ∀ r, (univ.filter (fun j => r ∈ ρ j)).card ≤ Drev) :
    Fintype.card Λ * ((∑ c, (ρ c).card) +
      ∑ c, (ρ c).card * (overlapColumns ρ c).card) ≤
      Fintype.card Λ * Fintype.card J * (w + w * w * Drev) := by
  have hsum : (∑ c, (ρ c).card) +
      ∑ c, (ρ c).card * (overlapColumns ρ c).card ≤
      Fintype.card J * (w + w * w * Drev) := by
    rw [← sum_add_distrib]
    calc
      _ ≤ ∑ _c : J, (w + w * w * Drev) := by
        apply sum_le_sum
        intro c _
        apply Nat.add_le_add (hforward c)
        have hov := (overlapColumns_card_le ρ c Drev hrev).trans
          (Nat.mul_le_mul_right Drev (hforward c))
        simpa only [Nat.mul_assoc] using Nat.mul_le_mul (hforward c) hov
      _ = _ := by simp
  simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (Fintype.card Λ) hsum

include hstable hfree in
/-- Bounded forward/reverse degree version, uniform in finite alphabet and lanes. -/
theorem parity_card_le_degrees [Fintype A] (hrec : RecoversFromRowsGiven ρ E C)
    (r : ℕ) (hr : 2 ≤ r) (hsize : ∀ k, r ≤ (D.support k).card)
    (w Drev : ℕ) (hforward : ∀ c, (ρ c).card ≤ w)
    (hrev : ∀ r, (univ.filter (fun j => r ∈ ρ j)).card ≤ Drev) :
    Nat.card C ≤ Fintype.card A ^ (Fintype.card (LaneCell R J Λ) - Fintype.card κ +
      (Fintype.card Λ * Fintype.card J * (w + w * w * Drev)) / r) := by
  apply (parity_card_le_incidence D ρ θ E hfree C hstable hrec r hr hsize).trans
  apply Nat.pow_le_pow_right Fintype.card_pos
  exact Nat.add_le_add_left (Nat.div_le_div_right (incidence_budget_le ρ w Drev hforward hrev)) _

end
end LeanMachine.WholeRow
