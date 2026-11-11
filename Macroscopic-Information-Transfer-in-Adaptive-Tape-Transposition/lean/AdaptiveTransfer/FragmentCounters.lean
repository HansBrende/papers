import AdaptiveTransfer.FragmentPrefixes
import LeanMachine.MonotoneSamples

/-! Exact fragment/cut output-counter fields. Every sample time is obtained
from the actual cut set and retained prefixes. The multiset stores exactly
4s+2 bounded counters and recovers them using their known chronology. -/

namespace AdaptiveTransfer
open Finset LeanMachine

abbrev FragmentCounterLabel (B : Finset ℕ) := (cutGapStarts B × Fin 2) ⊕ (B × Fin 2)

noncomputable def fragmentCounterEquiv (B : Finset ℕ) :
    FragmentCounterLabel B ≃ Fin (4 * B.card + 2) :=
  Fintype.equivFinOfCardEq (by simp [FragmentCounterLabel]; omega)

noncomputable def fragmentCounterTime (B K : Finset ℕ) : FragmentCounterLabel B → ℕ
  | .inl (a, i) => if i.val = 0 then a.val else a.val + (gapPrefix B K a.val).card
  | .inr (p, i) => p.val + i.val

theorem cutGapStarts_le {B : Finset ℕ} {T : ℕ} (hBT : ∀ p ∈ B, p < T)
    {a : ℕ} (ha : a ∈ cutGapStarts B) : a ≤ T := by
  rcases mem_insert.mp ha with he | hm
  · omega
  · obtain ⟨p, hp, he⟩ := mem_image.mp hm
    have := hBT p hp
    omega

theorem gapPrefix_end_le {B K : Finset ℕ} {T a : ℕ}
    (hclosed : StateClosedExcept K B) (hKT : ∀ t ∈ K, t < T) (ha : a ≤ T) :
    a + (gapPrefix B K a).card ≤ T := by
  by_cases hn : (gapPrefix B K a).card = 0
  · simpa only [hn, add_zero] using ha
  · have ht : a + (gapPrefix B K a).card - 1 ∈ gapPrefix B K a := by
      have hm : a + (gapPrefix B K a).card - 1 ∈ Ico a (a + (gapPrefix B K a).card) :=
        mem_Ico.mpr ⟨by omega, by omega⟩
      rwa [← gapPrefix_eq_Ico hclosed] at hm
    have hh := hKT _ (mem_filter.mp ht).1
    omega

theorem fragmentCounterTime_le {B K : Finset ℕ} {T : ℕ}
    (hclosed : StateClosedExcept K B) (hKT : ∀ t ∈ K, t < T)
    (hBT : ∀ p ∈ B, p < T) (i : FragmentCounterLabel B) : fragmentCounterTime B K i ≤ T := by
  rcases i with ⟨a, i⟩ | ⟨p, i⟩
  · simp only [fragmentCounterTime]
    split_ifs
    · exact cutGapStarts_le hBT a.property
    · exact gapPrefix_end_le hclosed hKT (cutGapStarts_le hBT a.property)
  · have := hBT p.val p.property
    have := i.isLt
    simp only [fragmentCounterTime]
    omega

def cappedCounter (P : ℕ) (counter : ℕ → ℕ) (t : ℕ) : Fin (P + 1) :=
  ⟨min P (counter t), by omega⟩

theorem cappedCounter_mono (P : ℕ) {counter : ℕ → ℕ} (hc : Monotone counter) :
    Monotone (cappedCounter P counter) := fun _ _ hab => min_le_min_left P (hc hab)

noncomputable def fragmentCounterDescription (B K : Finset ℕ) (P : ℕ) (counter : ℕ → ℕ) :
    Sym (Fin (P + 1)) (4 * B.card + 2) :=
  sampledCounterMultiset (fun i => fragmentCounterTime B K ((fragmentCounterEquiv B).symm i))
    (cappedCounter P counter)

theorem fragmentCounterDescription_recovers {B K : Finset ℕ} {P T : ℕ}
    (hclosed : StateClosedExcept K B) (hKT : ∀ t ∈ K, t < T)
    (hBT : ∀ p ∈ B, p < T) {counter counter' : ℕ → ℕ}
    (hc : Monotone counter) (hc' : Monotone counter')
    (hP : counter T ≤ P) (hP' : counter' T ≤ P)
    (he : fragmentCounterDescription B K P counter = fragmentCounterDescription B K P counter')
    (i : FragmentCounterLabel B) :
    counter (fragmentCounterTime B K i) = counter' (fragmentCounterTime B K i) := by
  have hh := sampledCounterMultiset_recovers _ (cappedCounter_mono P hc)
    (cappedCounter_mono P hc') he (fragmentCounterEquiv B i)
  have ht := fragmentCounterTime_le hclosed hKT hBT i
  have hbound := (hc ht).trans hP
  have hbound' := (hc' ht).trans hP'
  have heq := congrArg Fin.val hh
  simpa only [Equiv.symm_apply_apply, cappedCounter, min_eq_right hbound,
    min_eq_right hbound'] using heq

end AdaptiveTransfer
