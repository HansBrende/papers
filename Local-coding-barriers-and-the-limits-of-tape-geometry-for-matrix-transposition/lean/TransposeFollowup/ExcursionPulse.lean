import Transpose.Tape.Blocks

/-! A literal rise/hold/fall head walk, expressed by two capped ramps.
These are functions of ordinary step time; no movement or reset property is
assumed in their definition. -/

namespace TransposeFollowup

open Transpose.Tape
set_option autoImplicit false

def cappedRamp (L a t : ℕ) : ℤ := ((min (t - a) L : ℕ) : ℤ)

def excursionPulse (L a c t : ℕ) : ℤ := cappedRamp L a t - cappedRamp L c t

theorem cappedRamp_step (L a t : ℕ) :
    0 ≤ cappedRamp L a (t + 1) - cappedRamp L a t ∧
    cappedRamp L a (t + 1) - cappedRamp L a t ≤ 1 := by
  dsimp [cappedRamp]
  omega

theorem cappedRamp_change {L a t : ℕ}
    (hm : cappedRamp L a (t + 1) ≠ cappedRamp L a t) : a ≤ t ∧ t < a + L := by
  dsimp [cappedRamp] at hm
  omega

theorem excursionPulse_before {L a c t : ℕ} (hac : a ≤ c) (ht : t ≤ a) :
    excursionPulse L a c t = 0 := by
  dsimp [excursionPulse, cappedRamp]
  omega

theorem excursionPulse_after {L a c t : ℕ} (hac : a ≤ c) (ht : c + L ≤ t) :
    excursionPulse L a c t = 0 := by
  dsimp [excursionPulse, cappedRamp]
  omega

theorem excursionPulse_nonneg {L a c t : ℕ} (hac : a ≤ c) :
    0 ≤ excursionPulse L a c t := by
  dsimp [excursionPulse, cappedRamp]
  omega

theorem excursionPulse_rise {L a c t : ℕ} (hac : a + L ≤ c)
    (ha : a ≤ t) (ht : t ≤ a + L) : excursionPulse L a c t = (t - a : ℕ) := by
  dsimp [excursionPulse, cappedRamp]
  omega

theorem excursionPulse_plateau {L a c t : ℕ} (ha : a + L ≤ t) (hc : t ≤ c) :
    excursionPulse L a c t = L := by
  dsimp [excursionPulse, cappedRamp]
  omega

theorem excursionPulse_fall {L a c t : ℕ} (hac : a + L ≤ c)
    (hc : c ≤ t) (ht : t ≤ c + L) : excursionPulse L a c t = (L : ℤ) - (t - c : ℕ) := by
  dsimp [excursionPulse, cappedRamp]
  omega

theorem excursionPulse_unitSteps (L a c : ℕ) : UnitSteps (excursionPulse L a c) := by
  intro t
  have ha := cappedRamp_step L a t
  have hc := cappedRamp_step L c t
  rw [abs_le]
  dsimp [excursionPulse]
  omega

theorem excursionPulse_change {L a c t : ℕ}
    (hm : excursionPulse L a c (t + 1) ≠ excursionPulse L a c t) :
    (a ≤ t ∧ t < a + L) ∨ (c ≤ t ∧ t < c + L) := by
  by_cases ha : cappedRamp L a (t + 1) = cappedRamp L a t
  · right
    apply cappedRamp_change
    intro hc
    apply hm
    simp only [excursionPulse, ha, hc]
  · exact Or.inl (cappedRamp_change ha)

end TransposeFollowup
