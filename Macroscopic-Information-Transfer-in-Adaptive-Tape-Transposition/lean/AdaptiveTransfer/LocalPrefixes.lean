import AdaptiveTransfer.FragmentPrefixes
import AdaptiveTransfer.ReplayGeometry
import LeanMachine.BoundedTuplePadding

/-! Exact retained-prefix descriptions with a public set of possible starts.
For a selected chunk and s cuts there are at most N+s such starts. Zero
padding to that capacity adds no independently encoded retained set. -/

namespace AdaptiveTransfer
open Finset NativeRelations LeanMachine
open scoped BigOperators

def startCuts (A : Finset ℕ) : Finset ℕ := (A.filter fun a => 0 < a).image fun a => a - 1

theorem stateClosedExcept_startCuts {A K : Finset ℕ} (hstarts : runStarts K ⊆ A) :
    StateClosedExcept K (startCuts A) := by
  intro t ht htpos hprev
  by_contra hp
  have hta : t ∈ A := hstarts (mem_filter.mpr ⟨ht, Or.inr hp⟩)
  exact hprev (mem_image.mpr ⟨t, mem_filter.mpr ⟨hta, htpos⟩, rfl⟩)

theorem cutGapStart_mem_starts {A K : Finset ℕ} {T t : ℕ}
    (hstarts : runStarts K ⊆ A) (hKT : ∀ u ∈ K, u < T) (ht : t ∈ K) :
    cutGapStart (startCuts A) t ∈ A := by
  classical
  unfold cutGapStart
  split_ifs with hne
  · let p := ((startCuts A).filter fun p => p < t).max' hne
    have hp := mem_filter.mp (max'_mem ((startCuts A).filter fun p => p < t) hne)
    obtain ⟨a, ha, he⟩ := mem_image.mp hp.1
    have hpvalue : p + 1 = a := by have := (mem_filter.mp ha).2; omega
    change p + 1 ∈ A
    rw [hpvalue]
    exact (mem_filter.mp ha).1
  · obtain ⟨r, hr, hrt, _hre⟩ := exists_run_cover hKT ht
    have hrA := hstarts hr
    by_cases hr0 : r = 0
    · simpa only [hr0] using hrA
    · have hmem : r - 1 ∈ (startCuts A).filter fun p => p < t :=
        mem_filter.mpr ⟨mem_image.mpr ⟨r, mem_filter.mpr ⟨hrA, by omega⟩, rfl⟩, by omega⟩
      exact (hne ⟨r - 1, hmem⟩).elim

theorem sum_startPrefix_card {A K : Finset ℕ} {T : ℕ}
    (hstarts : runStarts K ⊆ A) (hKT : ∀ t ∈ K, t < T) :
    ∑ a ∈ A, (gapPrefix (startCuts A) K a).card = K.card := by
  symm
  exact card_eq_sum_card_fiberwise (fun _ ht => cutGapStart_mem_starts hstarts hKT ht)

noncomputable def startPrefixDescription (A K : Finset ℕ) (T : ℕ)
    (hstarts : runStarts K ⊆ A) (hKT : ∀ t ∈ K, t < T) : BoundedTuple A.card T := by
  let e := A.equivFinOfCardEq rfl
  refine ⟨fun i => (gapPrefix (startCuts A) K (e.symm i).val).card, ?_⟩
  rw [e.symm.sum_comp (fun a : A => (gapPrefix (startCuts A) K a.val).card)]
  calc
    _ = K.card := (sum_coe_sort A _).trans (sum_startPrefix_card hstarts hKT)
    _ ≤ T := (card_le_card (fun t ht => mem_range.mpr (hKT t ht))).trans (card_range T).le

theorem startPrefixDescription_recovers {A K K' : Finset ℕ} {T : ℕ}
    (hstarts : runStarts K ⊆ A) (hstarts' : runStarts K' ⊆ A)
    (hKT : ∀ t ∈ K, t < T) (hK'T : ∀ t ∈ K', t < T)
    (he : startPrefixDescription A K T hstarts hKT = startPrefixDescription A K' T hstarts' hK'T) :
    K = K' := by
  let e := A.equivFinOfCardEq rfl
  have hlength (a : A) : (gapPrefix (startCuts A) K a.val).card =
      (gapPrefix (startCuts A) K' a.val).card := by
    have hh := congrFun (congrArg Subtype.val he) (e a)
    simpa only [startPrefixDescription, e, Equiv.symm_apply_apply] using hh
  have hgap (a : A) : gapPrefix (startCuts A) K a.val = gapPrefix (startCuts A) K' a.val := by
    rw [gapPrefix_eq_Ico (stateClosedExcept_startCuts hstarts),
      gapPrefix_eq_Ico (stateClosedExcept_startCuts hstarts'), hlength a]
  ext t
  constructor
  · intro ht
    have hh : t ∈ gapPrefix (startCuts A) K (cutGapStart (startCuts A) t) := mem_filter.mpr ⟨ht, rfl⟩
    rw [hgap ⟨_, cutGapStart_mem_starts hstarts hKT ht⟩] at hh
    exact (mem_filter.mp hh).1
  · intro ht
    have hh : t ∈ gapPrefix (startCuts A) K' (cutGapStart (startCuts A) t) := mem_filter.mpr ⟨ht, rfl⟩
    rw [← hgap ⟨_, cutGapStart_mem_starts hstarts' hK'T ht⟩] at hh
    exact (mem_filter.mp hh).1

def localGapStarts (C B : Finset ℕ) : Finset ℕ := runStarts C ∪ B.image (fun p => p + 1)

theorem localGapStarts_card_le {C B : Finset ℕ} {N : ℕ} (hN : (runStarts C).card ≤ N) :
    (localGapStarts C B).card ≤ N + B.card :=
  (card_union_le _ _).trans (Nat.add_le_add hN card_image_le)

noncomputable def localPrefixDescription (C K B : Finset ℕ) (T N : ℕ)
    (hlocal : LocallyStateClosedExcept C K B) (hKT : ∀ t ∈ K, t < T)
    (hN : (runStarts C).card ≤ N) : BoundedTuple (N + B.card) T :=
  padBoundedTuple (localGapStarts_card_le hN)
    (startPrefixDescription (localGapStarts C B) K T (local_starts_subset hlocal) hKT)

theorem localPrefixDescription_recovers {C K K' B : Finset ℕ} {T N : ℕ}
    (hlocal : LocallyStateClosedExcept C K B) (hlocal' : LocallyStateClosedExcept C K' B)
    (hKT : ∀ t ∈ K, t < T) (hK'T : ∀ t ∈ K', t < T) (hN : (runStarts C).card ≤ N)
    (he : localPrefixDescription C K B T N hlocal hKT hN =
      localPrefixDescription C K' B T N hlocal' hK'T hN) : K = K' := by
  exact startPrefixDescription_recovers (local_starts_subset hlocal) (local_starts_subset hlocal')
    hKT hK'T (padBoundedTuple_injective (localGapStarts_card_le hN) he)

end AdaptiveTransfer
