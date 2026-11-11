import AdaptiveTransfer.TransferCrossingAssignments
import AdaptiveTransfer.TransferCrossingPointed
import AdaptiveTransfer.TransferCrossingPacking
import AdaptiveTransfer.TransferRoutes
import AdaptiveTransfer.TransferClockShadow

/-! A surviving physical crossing target determines an actual source
crossing. The connector uses the interval-shadow theorem to preserve the
target's one-sided segment, then routes through a closed band using actual
last-visit edges. No source crossing or projected route is assumed. -/

namespace AdaptiveTransfer.TransferCrossing
open Finset BoundedNesting NativeRelations MergeDepth
open TransferGuards TransferBandPaths

private theorem signed_mixed_abs (x y : ℕ → ℤ) (sign : Bool) (u r : ℕ) :
    |signed y sign u - signed x sign r| = |y u - x r| := by
  cases sign
  · simp only [signed, Bool.false_eq_true, ↓reduceIte]
    rw [show -y u - -x r = -(y u - x r) by ring, abs_neg]
  · rfl

/-- A good canonical frame forces a literal source crossing lower endpoint
strictly before the target's shadow, at distance R+1 from its physical cell.
The shadow hypotheses concern actual positions and whole time intervals. -/
theorem frame_source_crossing {x y : ℕ → ℤ} {q : ℕ → ℕ}
    {T U H h R v : ℕ} (hx : IsWalk x) (hq : Monotone q)
    (hrange : ∀ u < U, q u < T)
    (hshadow : ∀ u < U, |y u - x (q u)| ≤ (R : ℤ))
    (hinterval : ∀ a b r, a ≤ b → b < U → q a ≤ r → r ≤ q b →
      ∃ z, a ≤ z ∧ z ≤ b ∧ |y z - x r| ≤ (R : ℤ))
    (F : CrossingFrame y U H v)
    (hlo : ((2 * h + 2 * R + 2 : ℕ) : ℤ) < signed y F.sign v -
      overlapLow y U H F.sign F.firstEpoch F.secondEpoch)
    (hhi : ((2 * h + 2 * R + 2 : ℕ) : ℤ) <
      overlapHigh y U H F.sign F.firstEpoch F.secondEpoch - signed y F.sign v) :
    ∃ p, p < q v ∧ p ∈ tapeCrossingLowers x T h ∧ |y v - x p| ≤ (R : ℤ) + 1 := by
  classical
  let A := epochMax y U H F.sign F.firstEpoch
  let B := epochMin y U H F.sign F.secondEpoch
  let t₀ := prefixMin y F.sign A
  let t₃ := suffixMax y U F.sign B
  let X := signed x F.sign
  let Y := signed y F.sign
  have hAB : A < B := F.peak_valley
  have hB₃ : B < t₃ := F.valley_right
  have h₃U : t₃ < U := F.right_lt
  have hAU : A < U := hAB.trans (hB₃.trans h₃U)
  have hBU : B < U := hB₃.trans h₃U
  have h₀A : t₀ ≤ A := by
    have hh := minimizeOn_spec (f := Y) (S := Icc 0 A)
      (show (Icc 0 A).Nonempty from ⟨0, by simp⟩)
    exact (mem_Icc.mp hh.1).2
  have h₀U : t₀ < U := h₀A.trans_lt hAU
  have hvB : v < B := F.target_valley
  have hvU : v < U := hvB.trans hBU
  have hlo' : 2 * (h : ℤ) + 2 * (R : ℤ) + 2 < Y v - max (Y t₀) (Y B) := by
    simpa only [Y, t₀, t₃, A, B, overlapLow, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hlo
  have hhi' : 2 * (h : ℤ) + 2 * (R : ℤ) + 2 < min (Y A) (Y t₃) - Y v := by
    simpa only [Y, t₀, t₃, A, B, overlapHigh, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hhi
  have hlow₀ := le_max_left (Y t₀) (Y B)
  have hlowB := le_max_right (Y t₀) (Y B)
  have hhighA := min_le_left (Y A) (Y t₃)
  have hhigh₃ := min_le_right (Y A) (Y t₃)
  have shadow (u : ℕ) (hu : u < U) :
      -(R : ℤ) ≤ Y u - X (q u) ∧ Y u - X (q u) ≤ R := by
    apply abs_le.mp
    rw [signed_mixed_abs]
    exact hshadow u hu
  have sh₀ := shadow t₀ h₀U
  have shA := shadow A hAU
  have shB := shadow B hBU
  have sh₃ := shadow t₃ h₃U
  have q₀A : q t₀ < q A := by
    have hh := hq h₀A
    by_contra hbad
    have he : q t₀ = q A := by omega
    rw [he] at sh₀
    omega
  have qAB : q A < q B := by
    have hh := hq hAB.le
    by_contra hbad
    have he : q A = q B := by omega
    rw [he] at shA
    omega
  have qB₃ : q B < q t₃ := by
    have hh := hq hB₃.le
    by_contra hbad
    have he : q B = q t₃ := by omega
    rw [he] at shB
    omega
  have hX : IsWalk X := signed_isWalk hx F.sign
  have signed_interval (a b r : ℕ) (hab : a ≤ b) (hb : b < U)
      (har : q a ≤ r) (hrb : r ≤ q b) :
      ∃ z, a ≤ z ∧ z ≤ b ∧ (-(R : ℤ) ≤ Y z - X r ∧ Y z - X r ≤ R) := by
    obtain ⟨z, haz, hzb, hz⟩ := hinterval a b r hab hb har hrb
    refine ⟨z, haz, hzb, abs_le.mp ?_⟩
    rw [signed_mixed_abs]
    exact hz
  cases hrole : F.second
  · have hvA : v < A := by simpa only [hrole, Bool.false_eq_true, ↓reduceIte] using F.role_time
    have hside : ∀ r ∈ Icc (q v) (q A), Y v - (R : ℤ) - 1 < X r := by
      intro r hr
      obtain ⟨z, hvz, hzA, hz⟩ := signed_interval v A r hvA.le hAU
        (mem_Icc.mp hr).1 (mem_Icc.mp hr).2
      have hh := F.one_sided z (by simpa only [hrole, Bool.false_eq_true, ↓reduceIte] using mem_Icc.mpr ⟨hvz, hzA⟩)
      simp only [hrole, Bool.false_eq_true, ↓reduceIte] at hh
      change Y v ≤ Y z at hh
      omega
    obtain ⟨p, hpv, hp, hpcross⟩ := pointed_upper_crossing (H := h) hX q₀A qAB qB₃
      (hrange t₃ h₃U) (ell := Y v - (R : ℤ) - 1)
      (by omega) (by omega) (by omega) (by omega) (hq hvA.le) hside
    refine ⟨p, hpv, (signed_crossingLowers_iff F.sign).mp hpcross, ?_⟩
    rw [← signed_mixed_abs x y F.sign v p]
    change |Y v - X p| ≤ (R : ℤ) + 1
    rw [hp]
    apply abs_le.mpr
    omega
  · have hvB' : v ≤ B := hvB.le
    have hside : ∀ r ∈ Icc (q v) (q B), X r < Y v + (R : ℤ) + 1 := by
      intro r hr
      obtain ⟨z, hvz, hzB, hz⟩ := signed_interval v B r hvB' hBU
        (mem_Icc.mp hr).1 (mem_Icc.mp hr).2
      have hh := F.one_sided z (by simpa only [hrole, ↓reduceIte] using mem_Icc.mpr ⟨hvz, hzB⟩)
      simp only [hrole, ↓reduceIte] at hh
      change Y z ≤ Y v at hh
      omega
    obtain ⟨p, hpv, hp, hpcross⟩ := pointed_lower_crossing (H := h) hX q₀A qAB qB₃
      (hrange t₃ h₃U) (ell := Y v + (R : ℤ) + 1)
      (by omega) (by omega) (by omega) (by omega) (hq hvB') hside
    refine ⟨p, hpv, (signed_crossingLowers_iff F.sign).mp hpcross, ?_⟩
    rw [← signed_mixed_abs x y F.sign v p]
    change |Y v - X p| ≤ (R : ℤ) + 1
    rw [hp]
    apply abs_le.mpr
    omega

/-- If the target is outside the actual long-return guard, the source
crossing constructed from its frame is connected by a cut-free native
dependency path. Both path endpoints are included in cut avoidance. -/
theorem frame_cut_connector {k : ℕ} {xs ys : Fin k → ℕ → ℤ} {q : ℕ → ℕ}
    {T U H h R v : ℕ} (head : Fin k) (hx : IsWalk (xs head)) (hq : Monotone q)
    (hrange : ∀ u < U, q u < T)
    (hshadow : ∀ u < U, |ys head u - xs head (q u)| ≤ (R : ℤ))
    (hinterval : ∀ a b r, a ≤ b → b < U → q a ≤ r → r ≤ q b →
      ∃ z, a ≤ z ∧ z ≤ b ∧ |ys head z - xs head r| ≤ (R : ℤ))
    (F : CrossingFrame (ys head) U H v)
    (hlo : ((2 * h + 2 * R + 2 : ℕ) : ℤ) < signed (ys head) F.sign v -
      overlapLow (ys head) U H F.sign F.firstEpoch F.secondEpoch)
    (hhi : ((2 * h + 2 * R + 2 : ℕ) : ℤ) <
      overlapHigh (ys head) U H F.sign F.firstEpoch F.secondEpoch - signed (ys head) F.sign v)
    (B : Finset ℕ) (hguard : v ∉ crossingTargetGuard ys xs U H R B) :
    ∃ p, p ∈ tapeCrossingLowers (xs head) T h ∧ Route xs T B (q v) p := by
  obtain ⟨p, hpv, hpcross, hpclose⟩ := frame_source_crossing hx hq hrange hshadow hinterval F hlo hhi
  have hvU : v < U := by have hh := F.hop; have := hh.1; have := hh.2.1; omega
  have hvclose := hshadow v hvU
  have hpband : ys head v - (R : ℤ) - 1 ≤ xs head p ∧
      xs head p ≤ ys head v + (R : ℤ) + 1 := by
    have hh := abs_le.mp hpclose
    omega
  have hvband : ys head v - (R : ℤ) - 1 ≤ xs head (q v) ∧
      xs head (q v) ≤ ys head v + (R : ℤ) + 1 := by
    have hh := abs_le.mp hvclose
    omega
  obtain ⟨ρ, hρ, hlast, hband⟩ := exists_band_path head hx p (q v) hpv.le (hrange v hvU) hpband hvband
  refine ⟨p, hpcross, ρ, hρ, hlast, ?_⟩
  intro r hr hc
  apply hguard
  apply mem_crossingTargetGuard_of_close head hc F.hop F.excursion
  have hh := (hband r hr).2.2
  apply abs_le.mpr
  omega

open Transpose Transpose.Tape Transpose.Tape.Impl TapeStorageRates TapeStorageRates.Native
open TransferClock

/-- Actual aligned-machine connector. Every geometric hypothesis of the
generic construction is discharged by native source/compiled executions;
the only selected datum is the given canonical simulator crossing frame. -/
theorem native_frame_cut_connector {M : TM} {s t H h v : ℕ} {w : List Bool}
    (hs : 0 < s) (ht : 1 ≤ t) (halt : HaltsAt M w t) (head : Fin M.k)
    (F : CrossingFrame ((trace (machine M hs) w).work head) (alignedTime s t) H v)
    (hlo : ((2 * h + 2 * (3 * s) + 2 : ℕ) : ℤ) <
      signed ((trace (machine M hs) w).work head) F.sign v -
      overlapLow ((trace (machine M hs) w).work head) (alignedTime s t) H F.sign F.firstEpoch F.secondEpoch)
    (hhi : ((2 * h + 2 * (3 * s) + 2 : ℕ) : ℤ) <
      overlapHigh ((trace (machine M hs) w).work head) (alignedTime s t) H F.sign F.firstEpoch F.secondEpoch -
      signed ((trace (machine M hs) w).work head) F.sign v)
    (B : Finset ℕ) (hguard : v ∉ crossingTargetGuard
      (trace (machine M hs) w).work (trace M w).work (alignedTime s t) H (3 * s) B) :
    ∃ p, p ∈ tapeCrossingLowers ((trace M w).work head) t h ∧
      Route (trace M w).work t B (sourceClock s t v) p := by
  apply frame_cut_connector head ((trace M w).work_isWalk head) (sourceClock_mono s t)
    (fun u _hu => sourceClock_lt ht u) (R := 3 * s) (F := F) ?_ ?_ hlo hhi B hguard
  · intro u hu
    exact actual_head_shadow hs ht halt hu (some head)
  · intro a b r hab hb har hrb
    exact actual_interval_shadow hs ht halt hab hb har hrb (some head)

end AdaptiveTransfer.TransferCrossing
