import AdaptiveTransfer.LocalPrefixes
import AdaptiveTransfer.FragmentCounters

/-! Exact localized fragment/cut counters. The actual intervals have at most
N+s starts; zero-time padding gives exactly 4s+2N monotone counter samples,
whose multiset recovers all actual labels without an extra ordering field. -/

namespace AdaptiveTransfer
open Finset NativeRelations LeanMachine

abbrev LocalCounterLabel (C B : Finset ℕ) := (localGapStarts C B × Fin 2) ⊕ (B × Fin 2)

noncomputable def localCounterEquiv (C B : Finset ℕ) :
    LocalCounterLabel C B ≃ Fin (Fintype.card (LocalCounterLabel C B)) := Fintype.equivFin _

theorem localCounterCapacity {C B : Finset ℕ} {N : ℕ} (hN : (runStarts C).card ≤ N) :
    Fintype.card (LocalCounterLabel C B) ≤ 4 * B.card + 2 * N := by
  have h := localGapStarts_card_le (B := B) hN
  simp only [LocalCounterLabel, Fintype.card_sum, Fintype.card_prod, Fintype.card_coe,
    Fintype.card_fin]
  omega

noncomputable def localCounterTime (C K B : Finset ℕ) : LocalCounterLabel C B → ℕ
  | .inl (a, i) => if i.val = 0 then a.val
      else a.val + (gapPrefix (startCuts (localGapStarts C B)) K a.val).card
  | .inr (p, i) => p.val + i.val

theorem localGapStarts_le {C B : Finset ℕ} {T : ℕ}
    (hCT : ∀ t ∈ C, t < T) (hBT : ∀ p ∈ B, p < T)
    {a : ℕ} (ha : a ∈ localGapStarts C B) : a ≤ T := by
  rcases mem_union.mp ha with ha | ha
  · exact (hCT a (mem_filter.mp ha).1).le
  · obtain ⟨p, hp, he⟩ := mem_image.mp ha
    have := hBT p hp
    omega

theorem localCounterTime_le {C K B : Finset ℕ} {T : ℕ}
    (hlocal : LocallyStateClosedExcept C K B) (hCT : ∀ t ∈ C, t < T)
    (hBT : ∀ p ∈ B, p < T) (i : LocalCounterLabel C B) : localCounterTime C K B i ≤ T := by
  rcases i with ⟨a, i⟩ | ⟨p, i⟩
  · simp only [localCounterTime]
    split_ifs
    · exact localGapStarts_le hCT hBT a.property
    · exact gapPrefix_end_le (stateClosedExcept_startCuts (local_starts_subset hlocal))
        (fun t ht => hCT t (hlocal.1 ht)) (localGapStarts_le hCT hBT a.property)
  · have := hBT p.val p.property
    have := i.isLt
    simp only [localCounterTime]
    omega

noncomputable def localCounterDescription (C K B : Finset ℕ) (P N : ℕ) (counter : ℕ → ℕ) :
    Sym (Fin (P + 1)) (4 * B.card + 2 * N) :=
  sampledCounterMultiset
    (paddedTupleFunction (fun i => localCounterTime C K B ((localCounterEquiv C B).symm i)))
    (cappedCounter P counter)

theorem localCounterDescription_recovers {C K B : Finset ℕ} {P T N : ℕ}
    (hlocal : LocallyStateClosedExcept C K B) (hCT : ∀ t ∈ C, t < T)
    (hBT : ∀ p ∈ B, p < T) (hN : (runStarts C).card ≤ N)
    {counter counter' : ℕ → ℕ} (hc : Monotone counter) (hc' : Monotone counter')
    (hP : counter T ≤ P) (hP' : counter' T ≤ P)
    (he : localCounterDescription C K B P N counter = localCounterDescription C K B P N counter')
    (i : LocalCounterLabel C B) :
    counter (localCounterTime C K B i) = counter' (localCounterTime C K B i) := by
  let j := localCounterEquiv C B i
  have hh := sampledCounterMultiset_recovers _ (cappedCounter_mono P hc)
    (cappedCounter_mono P hc') he (Fin.castLE (localCounterCapacity hN) j)
  have ht := localCounterTime_le hlocal hCT hBT i
  have hbound := (hc ht).trans hP
  have hbound' := (hc' ht).trans hP'
  have heq := congrArg Fin.val hh
  simpa only [paddedTupleFunction, Fin.val_castLE, dite_eq_left j.isLt,
    Fin.eta, j, Equiv.symm_apply_apply, cappedCounter, min_eq_right hbound, min_eq_right hbound'] using heq

end AdaptiveTransfer
