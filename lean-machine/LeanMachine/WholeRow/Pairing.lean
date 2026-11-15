import LeanMachine.InvolutionOmissions
import LeanMachine.WholeRow.ParityReserved

/-! # Whole-row extensions of partially retained pairing shifts

Select omitted nontrivial orbits explicitly. The original endpoints retain
all fixed-coordinate shifts, forcing those coordinates to be incident. Reserving
them in the original incidence set cancels the fixed-point term even after
heavy-row trimming pins some of them. The `given` variants allow arbitrary
pins outside the active pairs and retain the nonincident fixed-cell charge.
An explicit inactive-fixed-cell endpoint charges only the inactive cells
outside the original incidence set. All bounds allow nonlinear codes.
-/

namespace LeanMachine.WholeRow

open Finset InvolutionSums
open scoped BigOperators Classical
noncomputable section

variable {R J Λ A : Type*} [Fintype R] [Fintype J] [Fintype Λ]
variable (m : LaneCell R J Λ → LaneCell R J Λ) (hm : Function.Involutive m)
variable (O : Finset (representatives m))
variable [AddCommGroup A] (C : Set (LaneCell R J Λ → A))
variable (hstable : ∀ x ∈ C, ∀ z ∈ activeShifts m hm O, x + z ∈ C)
variable (ρ : J → Finset R)

include hstable in
private theorem pairing_kernel_stable : ∀ x ∈ C, ∀ z : LaneCell R J Λ → A,
    (activeBlocks m hm O).weightedEncode (weights m) z = 0 →
    Set.EqOn z 0 (↑(omittedCells m hm O)) → x + z ∈ C := by
  classical
  intro x hx z hz hp
  exact hstable x hx z ((active_kernel_iff m hm O z).mp ⟨hz, hp⟩)

include hstable in
/-- Fixed-coordinate shifts are still active initially, so fixed cells are incident. -/
theorem pairing_fixed_incident [Nontrivial A] (hC : C.Nonempty)
    (hrec : RecoversFromRows ρ C) : fixedCells m ⊆ incidentCells ρ := by
  classical
  intro v hv
  have hmv : m v = v := (mem_fixedCells m v).mp hv
  let D := activeBlocks m hm O
  let E : Set (LaneCell R J Λ) := ↑(omittedCells m hm O)
  have hs : ∀ x ∈ C, ∀ z : LaneCell R J Λ → A,
      (D.withPins E (omitted_free m hm O)).weightedEncode (weights m) z = 0 → x + z ∈ C := by
    intro x hx z hz
    apply hstable x hx z
    rw [← pinned_active_kernel_eq m hm O]
    exact hz
  have hview := (D.withPins E (omitted_free m hm O)).weighted_mem_view_of_free
    (weights m) C hs hC (↑(helperBundle (Λ := Λ) ρ v.2.1)) v (hrec v) (by
      intro p
      cases p with
      | inl p => exact fixed_not_mem_support m hm hmv p.val
      | inr e =>
        change v ∉ ({e.val} : Finset (LaneCell R J Λ))
        simp only [mem_singleton]
        intro he
        exact fixed_not_omitted m hm O hmv (he.symm ▸ e.property))
  exact mem_filter.mpr ⟨mem_univ _, (mem_product.mp hview).1⟩

include hstable in
/-- Exact attained-record count for the explicitly selected active pairing shifts. -/
theorem pairing_record_card_eq (hrec : RecoversFromRows ρ C) :
    Nat.card C = Nat.card (activeShifts (A := A) m hm O) *
      Nat.card ((activeBlocks m hm O).pinnedRecord (↑(omittedCells m hm O))
        (weights m) (recordBlocks (activeBlocks m hm O) ρ) '' C) := by
  classical
  simpa only [pinned_active_kernel_eq] using
    parity_record_card_eq (activeBlocks m hm O) ρ (weights m)
      (↑(omittedCells m hm O)) (omitted_free m hm O) C
      (pairing_kernel_stable m hm O C hstable) (hrec.given _)

/-- A fixed coordinate is incident or pinned. Fixed-coordinate activity is
encoded by the kernel hypothesis, not supplied by recovery alone. -/
theorem pairing_fixed_incident_or_pinned [Nontrivial A] (hC : C.Nonempty)
    (E : Set (LaneCell R J Λ))
    (hfree : ∀ p, ∀ v ∈ E, v ∉ (activeBlocks m hm O).support p)
    (hs : ∀ x ∈ C, ∀ z : LaneCell R J Λ → A,
      (activeBlocks m hm O).weightedEncode (weights m) z = 0 →
      Set.EqOn z 0 E → x + z ∈ C)
    (hrec : RecoversFromRowsGiven ρ E C) {v : LaneCell R J Λ}
    (hv : v ∈ fixedCells m) : v ∈ incidentCells ρ ∨ v ∈ E := by
  classical
  by_cases he : v ∈ E
  · exact Or.inr he
  let D := activeBlocks m hm O
  have hs' : ∀ x ∈ C, ∀ z : LaneCell R J Λ → A,
      (D.withPins E hfree).weightedEncode (weights m) z = 0 → x + z ∈ C := by
    intro x hx z hz
    have h := (D.withPins_encode_eq_zero_iff E hfree (weights m) z).mp hz
    exact hs x hx z h.1 h.2
  have hview := (D.withPins E hfree).weighted_mem_view_of_free (weights m) C hs' hC
    ((↑(helperBundle (Λ := Λ) ρ v.2.1)) ∪ E) v (hrec v) (by
      intro p
      cases p with
      | inl p => exact fixed_not_mem_support m hm ((mem_fixedCells m v).mp hv) p.val
      | inr e =>
        change v ∉ ({e.val} : Finset (LaneCell R J Λ))
        simp only [mem_singleton]
        intro h
        exact he (h.symm ▸ e.property))
  exact Or.inl (mem_filter.mpr ⟨mem_univ _, (mem_product.mp (hview.resolve_right he)).1⟩)

/-- Raw pins may include fixed coordinates. Only nonincident fixed cells remain
as a fixed-cell charge; recovery may also use the pins. -/
theorem pairing_card_sq_le_after_trim_given [Fintype A]
    (E : Set (LaneCell R J Λ))
    (hfree : ∀ p, ∀ v ∈ E, v ∉ (activeBlocks m hm O).support p)
    (hs : ∀ x ∈ C, ∀ z : LaneCell R J Λ → A,
      (activeBlocks m hm O).weightedEncode (weights m) z = 0 →
      Set.EqOn z 0 E → x + z ∈ C)
    (hrec : RecoversFromRowsGiven ρ E C) (H : Finset R) :
    Nat.card C ^ 2 ≤ Fintype.card A ^
      (Fintype.card (LaneCell R J Λ) + 2 * O.card +
        (fixedCells m \ incidentCells ρ).card +
        2 * ((activeBlocks m hm O).touchingBlocks (rowCells H)).card +
        (incidentCells (Λ := Λ) ρ).card + Fintype.card Λ *
          ∑ c, (trimRows ρ H c).card * (overlapColumns (trimRows ρ H) c).card) := by
  classical
  let D := activeBlocks m hm O
  let F := rowCells (J := J) (Λ := Λ) H
  let E' := D.deletionPins F E
  have hrec' : RecoversFromRowsGiven (trimRows ρ H) E' C :=
    hrec.trim H (fun _ he => Or.inl (Or.inl he)) (fun _ hv => Or.inl (Or.inr hv))
  have hs' : ∀ x ∈ C, ∀ z : LaneCell R J Λ → A,
      (D.deleteTouching F).weightedEncode (weights m) z = 0 →
      Set.EqOn z 0 E' → x + z ∈ C := by
    intro x hx z hz hp
    exact hs x hx z (D.deleted_kernel_le F E (weights m) z hz hp)
      (hp.mono (fun _ he => Or.inl (Or.inl he)))
  have hbound := parity_card_sq_le_reserved (D.deleteTouching F) (trimRows ρ H) ρ
    (weights m) E' (D.deletionPins_free F E hfree) C hs' hrec'
    (fun p => by simpa [D, DisjointSums.deleteTouching, DisjointSums.restrictBlocks,
      activeBlocks] using le_of_eq (support_card m hm p.val.val).symm)
    (fun _ => sdiff_subset) (fixedCells m ∩ incidentCells ρ)
    inter_subset_right
    (fun p v hv => fixed_not_mem_support m hm
      ((mem_fixedCells m v).mp (mem_inter.mp hv).1) p.val.val)
  have hpart := active_card_partition m hm O
  have ht := card_le_univ (D.touchingBlocks F)
  have hsplit := card_sdiff_add_card_inter (fixedCells m) (incidentCells (Λ := Λ) ρ)
  rw [D.card_deleteTouching F] at hbound
  simp only [Fintype.card_coe, card_compl] at hpart ht hbound
  have he : 2 * (Fintype.card (LaneCell R J Λ) -
      ((representatives m).card - O.card - (D.touchingBlocks F).card)) -
      (fixedCells m ∩ incidentCells ρ).card =
      Fintype.card (LaneCell R J Λ) + 2 * O.card +
        (fixedCells m \ incidentCells ρ).card + 2 * (D.touchingBlocks F).card := by
    omega
  rw [he] at hbound
  exact hbound

include hstable in
/-- Sharp squared bound after any row deletion. Fixed points are reserved against
the original incidence set, while internal records use the trimmed relation. -/
theorem pairing_card_sq_le_after_trim [Fintype A] (hrec : RecoversFromRows ρ C)
    (H : Finset R) :
    Nat.card C ^ 2 ≤ Fintype.card A ^
      (Fintype.card (LaneCell R J Λ) + 2 * O.card +
        2 * ((activeBlocks m hm O).touchingBlocks (rowCells H)).card +
        (incidentCells (Λ := Λ) ρ).card + Fintype.card Λ *
          ∑ c, (trimRows ρ H c).card * (overlapColumns (trimRows ρ H) c).card) := by
  classical
  cases subsingleton_or_nontrivial A with
  | inl h =>
    have hc := Nat.card_le_card_of_injective (Subtype.val : C → (LaneCell R J Λ → A))
      Subtype.val_injective
    have hq : Fintype.card A = 1 := Fintype.card_eq_one_iff.mpr ⟨0, fun _ => Subsingleton.elim _ _⟩
    simpa [Nat.card_eq_fintype_card, hq] using Nat.pow_le_pow_left hc 2
  | inr h =>
    by_cases hC : C.Nonempty
    · have hi := pairing_fixed_incident m hm O C hstable ρ hC hrec
      simpa [sdiff_eq_empty_iff_subset.mpr hi] using
        pairing_card_sq_le_after_trim_given m hm O C ρ (↑(omittedCells m hm O))
          (omitted_free m hm O) (pairing_kernel_stable m hm O C hstable)
          (hrec.given _) H
    · rw [Set.not_nonempty_iff_eq_empty.mp hC]
      simp

include hstable in
/-- The fixed-cell term cancels exactly, including with omitted pairs. -/
theorem pairing_card_sq_le_incidence [Fintype A] (hrec : RecoversFromRows ρ C) :
    Nat.card C ^ 2 ≤ Fintype.card A ^
      (Fintype.card (LaneCell R J Λ) + 2 * O.card +
        (incidentCells (Λ := Λ) ρ).card +
        Fintype.card Λ * ∑ c, (ρ c).card * (overlapColumns ρ c).card) := by
  classical
  have ht : trimRows ρ ∅ = ρ := by funext c; simp [trimRows]
  simpa [rowCells, ht, DisjointSums.touchingBlocks] using
    pairing_card_sq_le_after_trim m hm O C hstable ρ hrec ∅

include hstable in
/-- Sharp bounded-degree pairing bound, without a leftover fixed-point term. -/
theorem pairing_card_sq_le_degrees [Fintype A] (hrec : RecoversFromRows ρ C)
    (w t : ℕ) (hf : ∀ c, (ρ c).card ≤ w)
    (hrev : ∀ a, (univ.filter (fun c => a ∈ ρ c)).card ≤ t) :
    Nat.card C ^ 2 ≤ Fintype.card A ^
      (Fintype.card (LaneCell R J Λ) + 2 * O.card +
        Fintype.card Λ * Fintype.card J * (w + w * w * t)) := by
  classical
  apply (pairing_card_sq_le_incidence m hm O C hstable ρ hrec).trans
  apply Nat.pow_le_pow_right Fintype.card_pos
  have h := mixed_incidence_budget_le (Λ := Λ) ρ ρ w t hf hf hrev
  omega

include hstable in
/-- Forward width alone suffices, with one symbol per omitted or newly marked pair. -/
theorem pairing_card_sq_le_forward [Fintype A] (hrec : RecoversFromRows ρ C)
    (w t : ℕ) (hf : ∀ c, (ρ c).card ≤ w) :
    Nat.card C ^ 2 ≤ Fintype.card A ^
      (Fintype.card (LaneCell R J Λ) + 2 * O.card +
        2 * (Fintype.card Λ * Fintype.card J * (w * Fintype.card J / (t + 1))) +
        Fintype.card Λ * Fintype.card J * (w + w * w * t)) := by
  classical
  let H := heavyRows ρ t
  have h := pairing_card_sq_le_after_trim m hm O C hstable ρ hrec H
  have hc := mixed_incidence_budget_le (Λ := Λ) (trimRows ρ H) ρ w t
    (fun c => (card_le_card sdiff_subset).trans (hf c)) hf (reverse_trimRows_heavy_le ρ t)
  have ht := (activeBlocks m hm O).touchingBlocks_card_le (rowCells (J := J) (Λ := Λ) H)
  rw [card_rowCells] at ht
  have hH := (Nat.le_div_iff_mul_le (Nat.succ_pos t)).mpr (heavyRows_card_mul_succ_le ρ w t hf)
  have hp : ((activeBlocks m hm O).touchingBlocks (rowCells H)).card ≤
      Fintype.card Λ * Fintype.card J * (w * Fintype.card J / (t + 1)) :=
    ht.trans (Nat.mul_le_mul_left (Fintype.card Λ * Fintype.card J) hH)
  apply h.trans
  apply Nat.pow_le_pow_right Fintype.card_pos
  omega

/-- Forward-width bound with arbitrary raw pins and a nonincident-fixed-cell charge. -/
theorem pairing_card_sq_le_forward_given [Fintype A]
    (E : Set (LaneCell R J Λ))
    (hfree : ∀ p, ∀ v ∈ E, v ∉ (activeBlocks m hm O).support p)
    (hs : ∀ x ∈ C, ∀ z : LaneCell R J Λ → A,
      (activeBlocks m hm O).weightedEncode (weights m) z = 0 →
      Set.EqOn z 0 E → x + z ∈ C)
    (hrec : RecoversFromRowsGiven ρ E C)
    (w t : ℕ) (hf : ∀ c, (ρ c).card ≤ w) :
    Nat.card C ^ 2 ≤ Fintype.card A ^
      (Fintype.card (LaneCell R J Λ) + 2 * O.card +
        (fixedCells m \ incidentCells ρ).card +
        2 * (Fintype.card Λ * Fintype.card J * (w * Fintype.card J / (t + 1))) +
        Fintype.card Λ * Fintype.card J * (w + w * w * t)) := by
  classical
  let H := heavyRows ρ t
  have h := pairing_card_sq_le_after_trim_given m hm O C ρ E hfree hs hrec H
  have hc := mixed_incidence_budget_le (Λ := Λ) (trimRows ρ H) ρ w t
    (fun c => (card_le_card sdiff_subset).trans (hf c)) hf (reverse_trimRows_heavy_le ρ t)
  have ht := (activeBlocks m hm O).touchingBlocks_card_le (rowCells (J := J) (Λ := Λ) H)
  rw [card_rowCells] at ht
  have hH := (Nat.le_div_iff_mul_le (Nat.succ_pos t)).mpr (heavyRows_card_mul_succ_le ρ w t hf)
  have hp : ((activeBlocks m hm O).touchingBlocks (rowCells H)).card ≤
      Fintype.card Λ * Fintype.card J * (w * Fintype.card J / (t + 1)) :=
    ht.trans (Nat.mul_le_mul_left (Fintype.card Λ * Fintype.card J) hH)
  apply h.trans
  apply Nat.pow_le_pow_right Fintype.card_pos
  omega

private theorem pairing_error_precision (b d w n : ℕ)
    (hd : n * (w + w * w * (2 * w * n)) ≤ d) :
    n * (2 * (b * d * (w * d / (2 * w * n + 1))) +
      b * d * (w + w * w * (2 * w * n))) ≤ 2 * (b * d ^ 2) := by
  classical
  by_cases hw : w = 0
  · simp [hw]
  · have hq := Nat.div_mul_le_self (w * d) (2 * w * n + 1)
    have hq' : 2 * n * (w * d / (2 * w * n + 1)) ≤ d := by
      apply le_of_mul_le_mul_left (a := w) ?_ (Nat.pos_of_ne_zero hw)
      calc
        w * (2 * n * (w * d / (2 * w * n + 1))) =
            (w * d / (2 * w * n + 1)) * (2 * w * n) := by ring
        _ ≤ (w * d / (2 * w * n + 1)) * (2 * w * n + 1) :=
          Nat.mul_le_mul_left _ (Nat.le_succ _)
        _ ≤ w * d := hq
    have h₁ := Nat.mul_le_mul_left (b * d) hq'
    have h₂ := Nat.mul_le_mul_left (b * d) hd
    nlinarith

include hstable in
/-- Uniform half-rate plus the omitted-pair density and precision `1/n`.
The finite inequality includes empty codes and trivial alphabets; its rate
reading uses positive `n`, nonzero size, and an alphabet of size at least two. -/
theorem pairing_card_pow_le_half [Fintype A] (hrec : RecoversFromRows ρ C)
    (w n : ℕ) (hf : ∀ c, (ρ c).card ≤ w)
    (hsquare : Fintype.card R = Fintype.card J)
    (hd : n * (w + w * w * (2 * w * n)) ≤ Fintype.card J) :
    Nat.card C ^ (2 * n) ≤ Fintype.card A ^
      (n * (Fintype.card (LaneCell R J Λ) + 2 * O.card) +
        2 * Fintype.card (LaneCell R J Λ)) := by
  classical
  have h := pairing_card_sq_le_forward m hm O C hstable ρ hrec w (2 * w * n) hf
  have he := pairing_error_precision (Fintype.card Λ) (Fintype.card J) w n hd
  have hN : Fintype.card (LaneCell R J Λ) = Fintype.card Λ * Fintype.card J ^ 2 := by
    simp only [LaneCell, Fintype.card_prod, hsquare, pow_two,
      Nat.mul_comm, Nat.mul_left_comm]
  have hp := Nat.pow_le_pow_left h n
  simp only [← pow_mul] at hp
  apply hp.trans
  apply Nat.pow_le_pow_right Fintype.card_pos
  rw [hN] at *
  nlinarith

/-- Uniform rate with a half-symbol charge per nonincident fixed cell. -/
theorem pairing_card_pow_le_half_given [Fintype A]
    (E : Set (LaneCell R J Λ))
    (hfree : ∀ p, ∀ v ∈ E, v ∉ (activeBlocks m hm O).support p)
    (hs : ∀ x ∈ C, ∀ z : LaneCell R J Λ → A,
      (activeBlocks m hm O).weightedEncode (weights m) z = 0 →
      Set.EqOn z 0 E → x + z ∈ C)
    (hrec : RecoversFromRowsGiven ρ E C)
    (w n : ℕ) (hf : ∀ c, (ρ c).card ≤ w)
    (hsquare : Fintype.card R = Fintype.card J)
    (hd : n * (w + w * w * (2 * w * n)) ≤ Fintype.card J) :
    Nat.card C ^ (2 * n) ≤ Fintype.card A ^
      (n * (Fintype.card (LaneCell R J Λ) + 2 * O.card +
          (fixedCells m \ incidentCells ρ).card) +
        2 * Fintype.card (LaneCell R J Λ)) := by
  classical
  have h := pairing_card_sq_le_forward_given m hm O C ρ E hfree hs hrec w (2 * w * n) hf
  have he := pairing_error_precision (Fintype.card Λ) (Fintype.card J) w n hd
  have hN : Fintype.card (LaneCell R J Λ) = Fintype.card Λ * Fintype.card J ^ 2 := by
    simp only [LaneCell, Fintype.card_prod, hsquare, pow_two,
      Nat.mul_comm, Nat.mul_left_comm]
  have hp := Nat.pow_le_pow_left h n
  simp only [← pow_mul] at hp
  apply hp.trans
  apply Nat.pow_le_pow_right Fintype.card_pos
  rw [hN] at *
  nlinarith

/-- Initially inactive fixed coordinates cost only half their nonincident density.
The subgroup premise permits all original active shifts that vanish on `F`. -/
theorem pairing_card_pow_le_half_of_inactive_fixed [Fintype A]
    (F : Finset (LaneCell R J Λ)) (hF : F ⊆ fixedCells m)
    (hs : ∀ x ∈ C, ∀ z ∈ activeShifts m hm O, Set.EqOn z 0 (↑F) → x + z ∈ C)
    (hrec : RecoversFromRows ρ C) (w n : ℕ) (hf : ∀ c, (ρ c).card ≤ w)
    (hsquare : Fintype.card R = Fintype.card J)
    (hd : n * (w + w * w * (2 * w * n)) ≤ Fintype.card J) :
    Nat.card C ^ (2 * n) ≤ Fintype.card A ^
      (n * (Fintype.card (LaneCell R J Λ) + 2 * O.card +
          (F \ incidentCells ρ).card) + 2 * Fintype.card (LaneCell R J Λ)) := by
  classical
  cases subsingleton_or_nontrivial A with
  | inl h =>
    have hc := Nat.card_le_card_of_injective (Subtype.val : C → (LaneCell R J Λ → A))
      Subtype.val_injective
    have hq : Fintype.card A = 1 := Fintype.card_eq_one_iff.mpr ⟨0, fun _ => Subsingleton.elim _ _⟩
    simpa [Nat.card_eq_fintype_card, hq] using Nat.pow_le_pow_left hc (2 * n)
  | inr h =>
    by_cases hC : C.Nonempty
    · let E : Set (LaneCell R J Λ) := (↑(omittedCells m hm O)) ∪ ↑F
      have he : ∀ p, ∀ v ∈ E, v ∉ (activeBlocks m hm O).support p := by
        intro p v hv
        rcases hv with hv | hv
        · exact omitted_free m hm O p v hv
        · exact fixed_not_mem_support m hm ((mem_fixedCells m v).mp (hF hv)) p.val
      have hs' : ∀ x ∈ C, ∀ z : LaneCell R J Λ → A,
          (activeBlocks m hm O).weightedEncode (weights m) z = 0 →
          Set.EqOn z 0 E → x + z ∈ C := by
        intro x hx z hz hp
        exact hs x hx z ((active_kernel_iff m hm O z).mp
          ⟨hz, hp.mono Set.subset_union_left⟩) (hp.mono Set.subset_union_right)
      have hbad : fixedCells m \ incidentCells ρ = F \ incidentCells ρ := by
        ext v
        simp only [mem_sdiff]
        constructor
        · rintro ⟨hv, hi⟩
          have hp := (pairing_fixed_incident_or_pinned m hm O C ρ hC E he hs'
            (hrec.given E) hv).resolve_left hi
          exact ⟨hp.resolve_left (fixed_not_omitted m hm O ((mem_fixedCells m v).mp hv)), hi⟩
        · exact fun ⟨hv, hi⟩ => ⟨hF hv, hi⟩
      simpa only [hbad] using
        pairing_card_pow_le_half_given m hm O C ρ E he hs' (hrec.given E) w n hf hsquare hd
    · rw [Set.not_nonempty_iff_eq_empty.mp hC]
      by_cases hn : n = 0
      · simpa [hn] using (one_le_pow₀ (show 1 ≤ Fintype.card A from Fintype.card_pos)
          (n := 2 * Fintype.card (LaneCell R J Λ)))
      · simp [Nat.mul_ne_zero (by decide : 2 ≠ 0) hn]

end
end LeanMachine.WholeRow
