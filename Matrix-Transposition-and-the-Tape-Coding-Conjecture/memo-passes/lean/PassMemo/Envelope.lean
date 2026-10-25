import PassMemo.RaySimulation
import PassMemo.MonotoneEvents
import Transpose.Tape.Blocks

/-! Relating the old-cell envelope and clean rays to actual native head trajectories. -/

namespace PassMemo

open Finset Transpose Transpose.Tape Transpose.Tape.Impl

def outward (R : ℕ) (p : ℤ) : Dir :=
  if p < -(R : ℤ) then .left else if (R : ℤ) < p then .right else .stay

theorem decreasing_of_below {h : ℕ → ℤ} {a e u R : ℕ}
    (hm : MonoOn h a e) (ha : |h a| ≤ R) (hau : a ≤ u) (hue : u ≤ e)
    (hu : h u < -(R : ℤ)) :
    ∀ x y, a ≤ x → x ≤ y → y ≤ e → h y ≤ h x := by
  rcases monoOn_cases hm with hup | hdn
  · have := hup a u le_rfl hau hue
    have := (abs_le.mp ha).1
    omega
  · exact hdn

theorem increasing_of_above {h : ℕ → ℤ} {a e u R : ℕ}
    (hm : MonoOn h a e) (ha : |h a| ≤ R) (hau : a ≤ u) (hue : u ≤ e)
    (hu : (R : ℤ) < h u) :
    ∀ x y, a ≤ x → x ≤ y → y ≤ e → h x ≤ h y := by
  rcases monoOn_cases hm with hup | hdn
  · exact hup
  · have := hdn a u le_rfl hau hue
    have := (abs_le.mp ha).2
    omega

theorem constant_of_unmarked {h : ℕ → ℤ} {u v R : ℕ}
    (hu : |h u| ≤ R) (hm : ∀ t, u ≤ t → t < v → ¬ Marked h R t) :
    ∀ t, u ≤ t → t ≤ v → h t = h u := by
  intro t hut
  induction t, hut using Nat.le_induction with
  | base => intro _; rfl
  | succ t hut ih =>
    intro htv
    have heq := ih (by omega)
    by_contra hne
    exact hm t hut (by omega) ⟨by omega, Or.inl (heq ▸ hu)⟩

theorem allowed_on_unmarked {h : ℕ → ℤ} {a e u v t R : ℕ} {d : Dir}
    (hm : MonoOn h a e) (ha : |h a| ≤ R) (hau : a ≤ u) (huv : u ≤ v)
    (hve : v ≤ e) (hut : u ≤ t) (htv : t < v)
    (hn : ∀ s, u ≤ s → s < v → ¬ Marked h R s)
    (hs : h (t + 1) = d.shift (h t)) : Allowed (outward R (h u)) d := by
  unfold outward
  split_ifs with hlo hhi
  · have hd := decreasing_of_below hm ha hau (by omega) hlo t (t + 1)
      (by omega) (by omega) (by omega)
    cases d <;> simp_all [Allowed, Dir.shift]
  · have hi := increasing_of_above hm ha hau (by omega) hhi t (t + 1)
      (by omega) (by omega) (by omega)
    cases d <;> simp_all [Allowed, Dir.shift]
  · have hu : |h u| ≤ R := abs_le.mpr ⟨by omega, by omega⟩
    have h1 := constant_of_unmarked hu hn t hut (by omega)
    have h2 := constant_of_unmarked hu hn (t + 1) (by omega) (by omega)
    cases d <;> simp_all [Allowed, Dir.shift]

theorem fresh_below {h : ℕ → ℤ} {a e u P : ℕ} {p : ℤ}
    (hb : ∀ t, |h t| ≤ (t : ℤ)) (hm : MonoOn h a e)
    (hau : a ≤ u) (hue : u ≤ e) (hu : h u < -((P + a : ℕ) : ℤ))
    (hp : p < h u) : ∀ s < u, h s ≠ p := by
  have ha : |h a| ≤ ((P + a : ℕ) : ℤ) := by have := hb a; omega
  have hd := decreasing_of_below hm ha hau hue hu
  intro s hsu heq
  by_cases hsa : s < a
  · have := (abs_le.mp (hb s)).1
    omega
  · have := hd s u (by omega) (by omega) hue
    omega

theorem fresh_above {h : ℕ → ℤ} {a e u P : ℕ} {p : ℤ}
    (hb : ∀ t, |h t| ≤ (t : ℤ)) (hm : MonoOn h a e)
    (hau : a ≤ u) (hue : u ≤ e) (hu : ((P + a : ℕ) : ℤ) < h u)
    (hp : h u < p) : ∀ s < u, h s ≠ p := by
  have ha : |h a| ≤ ((P + a : ℕ) : ℤ) := by have := hb a; omega
  have hi := increasing_of_above hm ha hau hue hu
  intro s hsu heq
  by_cases hsa : s < a
  · have := (abs_le.mp (hb s)).2
    omega
  · have := hi s u (by omega) (by omega) hue
    omega

theorem clean_outward {M : TM} {w : List Bool} {a e u : ℕ}
    (hm : AllMono M w a e) (hau : a ≤ u) (hue : u ≤ e) :
    Clean M w (outward (w.length + a) (inTraj M w u))
      (fun i => outward (w.length + a) (workTraj M w u i)) (run M w u) := by
  constructor
  · unfold outward
    split_ifs with hlo hhi <;> simp only [SafeInput]
    · change (run M w u).inPos < _ at hlo
      omega
    · change _ < (run M w u).inPos at hhi
      omega
  · intro i
    change SafeWork (outward (w.length + a) (workTraj M w u i))
      ((run M w u).work i) ((run M w u).workPos i)
    unfold outward
    split_ifs with hlo hhi <;> simp only [SafeWork]
    · intro p hp
      exact work_eq_blank i p (fresh_below (fun t => abs_workPos_le w t i)
        (hm.2 i) hau hue hlo hp)
    · intro p hp
      exact work_eq_blank i p (fresh_above (fun t => abs_workPos_le w t i)
        (hm.2 i) hau hue hhi hp)

abbrev Head (M : TM) := Option (Fin M.k)

def trajectory (M : TM) (w : List Bool) : Head M → ℕ → ℤ
  | none => inTraj M w
  | some i => fun t => workTraj M w t i

theorem trajectory_mono {M : TM} {w : List Bool} {a e : ℕ}
    (hm : AllMono M w a e) (h : Head M) : MonoOn (trajectory M w h) a e := by
  cases h with | none => exact hm.1 | some i => exact hm.2 i

theorem trajectory_unit (M : TM) (w : List Bool) (h : Head M) :
    UnitSteps (trajectory M w h) := by
  cases h with | none => exact unitSteps_inTraj M w | some i => exact unitSteps_workTraj M w i

/-- Every unmarked subinterval of a pass in a halting native run has bounded length. -/
theorem unmarked_interval_bound {M : TM} {w : List Bool} {a e u v T : ℕ}
    (hm : AllMono M w a e) (hau : a ≤ u) (huv : u ≤ v) (hve : v ≤ e)
    (heT : e ≤ T) (hhalt : HaltsAt M w T)
    (hn : ∀ h : Head M, ∀ t, u ≤ t → t < v →
      ¬ Marked (trajectory M w h) (w.length + a) t) :
    v - u ≤ signatureCount M := by
  apply ray_interval_bound (clean_outward hm hau (by omega)) (by omega) hhalt.2
  intro j hj
  have ht : u + j < T := by omega
  cases hb : transAt M w (u + j) with
  | none => exact False.elim (hhalt.1 _ ht hb)
  | some b =>
    refine ⟨b, rfl, ?_, ?_⟩
    · apply allowed_on_unmarked hm.1 (u := u) (v := v) (t := u + j) (by
        have := abs_inPos_le (M := M) w a
        change |(run M w a).inPos| ≤ _
        omega) hau huv hve (by omega) (by omega) (hn none)
      change (run M w (u + j + 1)).inPos = _
      rw [run_succ_inPos, hb]
      rcases b with ⟨s, d, acts, o⟩
      rfl
    · intro i
      apply allowed_on_unmarked (hm.2 i) (u := u) (v := v) (t := u + j) (by
        have := abs_workPos_le (M := M) w a i
        change |(run M w a).workPos i| ≤ _
        omega) hau huv hve (by omega) (by omega) (hn (some i))
      change (run M w (u + j + 1)).workPos i = _
      rw [run_succ_workPos, hb]
      rcases b with ⟨s, d, acts, o⟩
      rfl

end PassMemo
