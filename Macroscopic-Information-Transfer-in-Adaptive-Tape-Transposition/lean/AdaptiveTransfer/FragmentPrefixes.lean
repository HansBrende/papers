import AdaptiveTransfer.Fragments
import LeanMachine.BoundedTuples

/-! Actual fragment prefixes in the gaps between paid cuts. The bounded tuple
is constructed from the retained set and proves that no independent retained
set description is needed. Empty gaps are included in the s+1 coordinates. -/

namespace AdaptiveTransfer
open Finset NativeRelations LeanMachine
open scoped BigOperators

def cutGapStarts (B : Finset ℕ) : Finset ℕ := insert 0 (B.image (fun p => p + 1))

@[simp] theorem cutGapStarts_card (B : Finset ℕ) : (cutGapStarts B).card = B.card + 1 := by
  rw [cutGapStarts, card_insert_of_notMem, card_image_of_injective]
  · exact Nat.succ_injective
  · simp

noncomputable def cutGapStart (B : Finset ℕ) (t : ℕ) : ℕ :=
  if h : (B.filter (fun p => p < t)).Nonempty then (B.filter (fun p => p < t)).max' h + 1 else 0

theorem cutGapStart_le (B : Finset ℕ) (t : ℕ) : cutGapStart B t ≤ t := by
  unfold cutGapStart
  split_ifs with h
  · have hh := (mem_filter.mp (max'_mem (B.filter (fun p => p < t)) h)).2
    omega
  · exact Nat.zero_le _

theorem cutGapStart_mem (B : Finset ℕ) (t : ℕ) : cutGapStart B t ∈ cutGapStarts B := by
  unfold cutGapStart
  split_ifs with h
  · apply mem_insert_of_mem
    exact mem_image.mpr ⟨_, (mem_filter.mp (max'_mem (B.filter (fun p => p < t)) h)).1, rfl⟩
  · exact mem_insert_self _ _

theorem pred_not_cut_inside_gap {B : Finset ℕ} {t : ℕ} (ht : cutGapStart B t < t) : t - 1 ∉ B := by
  intro hp
  have hpos : 0 < t := by omega
  have hm : t - 1 ∈ B.filter (fun p => p < t) := mem_filter.mpr ⟨hp, by omega⟩
  have hne : (B.filter (fun p => p < t)).Nonempty := ⟨t - 1, hm⟩
  have hh := le_max' (B.filter (fun p => p < t)) (t - 1) hm
  simp only [cutGapStart, dite_eq_left hne] at ht
  omega

theorem cutGapStart_pred {B : Finset ℕ} {t : ℕ} (ht : cutGapStart B t < t) :
    cutGapStart B (t - 1) = cutGapStart B t := by
  have hnot := pred_not_cut_inside_gap ht
  have hf : B.filter (fun p => p < t - 1) = B.filter (fun p => p < t) := by
    ext p
    simp only [mem_filter]
    constructor
    · rintro ⟨hp, hpt⟩
      exact ⟨hp, by omega⟩
    · rintro ⟨hp, hpt⟩
      have hpne : p ≠ t - 1 := fun he => hnot (he ▸ hp)
      exact ⟨hp, by omega⟩
  simp only [cutGapStart, hf]

/-- A finite predecessor-closed set bounded below is an initial interval;
its cardinality is its exact prefix length. -/
theorem finite_prefix_eq_Ico (S : Finset ℕ) (a : ℕ)
    (hlower : ∀ t ∈ S, a ≤ t)
    (hprev : ∀ t ∈ S, a < t → t - 1 ∈ S) : S = Ico a (a + S.card) := by
  rcases S.eq_empty_or_nonempty with he | hne
  · simp only [he, card_empty, add_zero, Ico_self]
  · let m := S.max' hne
    have hm : m ∈ S := max'_mem S hne
    have hrec : ∀ n t, m - t = n → a ≤ t → t ≤ m → t ∈ S := by
      intro n
      induction n with
      | zero =>
        intro t hdiff _hat htm
        have ht : t = m := by omega
        exact ht ▸ hm
      | succ n ih =>
        intro t hdiff hat htm
        have ht : t + 1 ∈ S := ih (t + 1) (by omega) (by omega) (by omega)
        simpa only [Nat.add_sub_cancel] using hprev (t + 1) ht (by omega)
    have he : S = Icc a m := by
      ext t
      constructor
      · intro ht
        exact mem_Icc.mpr ⟨hlower t ht, le_max' S t ht⟩
      · intro ht
        exact hrec (m - t) t rfl (mem_Icc.mp ht).1 (mem_Icc.mp ht).2
    have hc : S.card = m + 1 - a := by rw [he, Nat.card_Icc]
    have ha : a ≤ m := hlower m hm
    have hend : a + S.card = m + 1 := by omega
    rw [hend, he]
    ext t
    simp only [mem_Icc, mem_Ico]
    omega

noncomputable def gapPrefix (B K : Finset ℕ) (a : ℕ) : Finset ℕ := K.filter (fun t => cutGapStart B t = a)

theorem gapPrefix_eq_Ico {B K : Finset ℕ} (hclosed : StateClosedExcept K B) (a : ℕ) :
    gapPrefix B K a = Ico a (a + (gapPrefix B K a).card) := by
  apply finite_prefix_eq_Ico
  · intro t ht
    exact (mem_filter.mp ht).2 ▸ cutGapStart_le B t
  · intro t ht hat
    have ht' : cutGapStart B t < t := (mem_filter.mp ht).2 ▸ hat
    exact mem_filter.mpr ⟨hclosed t (mem_filter.mp ht).1 (by omega) (pred_not_cut_inside_gap ht'),
      (cutGapStart_pred ht').trans (mem_filter.mp ht).2⟩

theorem sum_gapPrefix_card (B K : Finset ℕ) :
    ∑ a ∈ cutGapStarts B, (gapPrefix B K a).card = K.card := by
  symm
  exact card_eq_sum_card_fiberwise (fun t _ht => cutGapStart_mem B t)

noncomputable def prefixDescription (B K : Finset ℕ) (T : ℕ) (hKT : ∀ t ∈ K, t < T) :
    BoundedTuple (B.card + 1) T := by
  let e := (cutGapStarts B).equivFinOfCardEq (cutGapStarts_card B)
  refine ⟨fun i => (gapPrefix B K (e.symm i).val).card, ?_⟩
  have he := e.symm.sum_comp (fun a : cutGapStarts B => (gapPrefix B K a.val).card)
  rw [he]
  have hh : (∑ a : cutGapStarts B, (gapPrefix B K a.val).card) = K.card := by
    exact (sum_coe_sort (cutGapStarts B) (fun a => (gapPrefix B K a).card)).trans
      (sum_gapPrefix_card B K)
  rw [hh]
  exact (card_le_card (fun t ht => mem_range.mpr (hKT t ht))).trans (card_range T).le

theorem prefixDescription_recovers {B K K' : Finset ℕ} {T : ℕ}
    (hK : StateClosedExcept K B) (hK' : StateClosedExcept K' B)
    (hKT : ∀ t ∈ K, t < T) (hK'T : ∀ t ∈ K', t < T)
    (he : prefixDescription B K T hKT = prefixDescription B K' T hK'T) : K = K' := by
  let e := (cutGapStarts B).equivFinOfCardEq (cutGapStarts_card B)
  have hlength (a : cutGapStarts B) : (gapPrefix B K a.val).card = (gapPrefix B K' a.val).card := by
    have hh := congrFun (congrArg Subtype.val he) (e a)
    simpa only [prefixDescription, e, Equiv.symm_apply_apply] using hh
  have hgap (a : cutGapStarts B) : gapPrefix B K a.val = gapPrefix B K' a.val := by
    rw [gapPrefix_eq_Ico hK, gapPrefix_eq_Ico hK', hlength a]
  ext t
  constructor
  · intro ht
    have hh : t ∈ gapPrefix B K (cutGapStart B t) := mem_filter.mpr ⟨ht, rfl⟩
    rw [hgap ⟨cutGapStart B t, cutGapStart_mem B t⟩] at hh
    exact (mem_filter.mp hh).1
  · intro ht
    have hh : t ∈ gapPrefix B K' (cutGapStart B t) := mem_filter.mpr ⟨ht, rfl⟩
    rw [← hgap ⟨cutGapStart B t, cutGapStart_mem B t⟩] at hh
    exact (mem_filter.mp hh).1

end AdaptiveTransfer
