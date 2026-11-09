import CascadeObstruction.C5Schedule
import CascadeObstruction.StageClockAssembly

/-! The complete physical C5 clock. Tick ownership is obtained from the
ordered, uniquely labelled finite schedule, not assumed as a premise. -/

namespace CascadeObstruction.C5

open TransposeFollowup.RegularMotion
open scoped BigOperators

set_option autoImplicit false

def clockKey (key : Key) : List (Fin 1) × Fin 2 :=
  (List.replicate key.1 0, key.2)

theorem clockKey_injective : Function.Injective clockKey := by
  intro x y h
  apply Prod.ext
  · have := congrArg (fun p => p.1.length) h
    simpa [clockKey] using this
  · exact congrArg (Prod.snd : List (Fin 1) × Fin 2 → Fin 2) h

theorem clockKey_length (w : List (Fin 1)) (j : Fin 2) :
    clockKey (w.length, j) = (w, j) := by
  apply Prod.ext
  · exact List.length_injective (by simp [clockKey])
  · rfl

def clockStages (K b : ℕ) : List ((List (Fin 1) × Fin 2) × ℕ) :=
  (keys K).map (fun key => (clockKey key, blocksDuration (stage K b key)))

theorem clockStages_nodup (K b : ℕ) : ((clockStages K b).map Prod.fst).Nodup := by
  simpa [clockStages, List.map_map, Function.comp_def] using
    (keys_nodup K).map clockKey_injective

theorem clockStages_total (K b : ℕ) :
    StageClockAssembly.total (clockStages K b) = (trace K b).length := by
  have h (xs : List Key) :
      StageClockAssembly.total (xs.map (fun key =>
        (clockKey key, blocksDuration (stage K b key)))) =
        blocksDuration (xs.flatMap (stage K b)) := by
    induction xs with
    | nil => rfl
    | cons key xs ih =>
      simp only [List.map_cons, StageClockAssembly.total, List.flatMap_cons,
        blocksDuration_append, ih]
  simpa only [clockStages, trace, expand_length, programBlocks] using h (keys K)

theorem clockStages_duration (K b : ℕ) (w : List (Fin 1)) (j : Fin 2) :
    StageClockAssembly.duration (clockStages K b) (w, j) =
      if w.length ≤ K then blocksDuration (stage K b (w.length, j)) else 0 := by
  by_cases hr : w.length ≤ K
  · rw [ite_eq_left hr]
    apply StageClockAssembly.duration_eq_of_mem (clockStages_nodup K b)
    apply List.mem_map.mpr
    exact ⟨(w.length, j), mem_keys_iff.mpr hr, by rw [clockKey_length]⟩
  · rw [ite_eq_right hr]
    apply StageClockAssembly.duration_eq_zero_of_not_mem
    intro hm
    simp only [clockStages, List.map_map, Function.comp_def, List.mem_map] at hm
    obtain ⟨key, hk, he⟩ := hm
    have hl := congrArg (fun p => p.1.length) he
    simp only [clockKey, List.length_replicate] at hl
    apply hr
    simpa only [← hl] using (mem_keys_iff.mp hk)

noncomputable def volume (K b : ℕ) (w : List (Fin 1)) : ℝ :=
  (inputLength K b : ℝ) * (1 / 2 : ℝ) ^ w.length

theorem size_eq_volume {K b r : ℕ} (hr : r ≤ 2 * (K + 1)) :
    (size K b r : ℝ) = (inputLength K b : ℝ) * (1 / 2 : ℝ) ^ r := by
  have he : (inputLength K b : ℝ) = (2 : ℝ) ^ r * (size K b r : ℝ) := by
    exact_mod_cast size_factor (b := b) hr
  rw [he]
  have hp : (2 : ℝ) ^ r * (1 / 2 : ℝ) ^ r = 1 := by rw [← mul_pow]; norm_num
  nlinarith [hp]

theorem clockStages_budget {K b : ℕ} (hb : 0 < b) (w : List (Fin 1)) :
    ((∑ j : Fin 2, StageClockAssembly.duration (clockStages K b) (w, j) : ℕ) : ℝ) ≤
      18 * volume K b w := by
  rw [Fin.sum_univ_two]
  simp only [clockStages_duration]
  by_cases hr : w.length ≤ K
  · simp only [ite_eq_left hr]
    have hh : ((blocksDuration (stage K b (w.length, 0)) +
        blocksDuration (stage K b (w.length, 1)) : ℕ) : ℝ) ≤
        18 * (size K b w.length : ℝ) := by exact_mod_cast stage_pair_budget hb hr
    rw [size_eq_volume (K := K) (b := b) (r := w.length) (by omega)] at hh
    exact hh
  · simp only [ite_eq_right hr, zero_add, Nat.cast_zero]
    unfold volume
    positivity

/-- The actual clock before transporting its total length to `trace.length`. -/
noncomputable def rawClock (K b : ℕ) (hb : 0 < b) :
    DyadicClock 18 (inputLength K b) (StageClockAssembly.total (clockStages K b)) :=
  StageClockAssembly.toClock (clockStages K b) (clockStages_nodup K b)
    (volume K b)
    (fun _ => by unfold volume; positivity)
    (fun w => by
      simp [volume, pow_succ]
      ring_nf
      exact le_rfl)
    (by simp [volume])
    (clockStages_budget hb)

/-- Complete physical stage partition, including root load/reset and output. -/
noncomputable def clock (K b : ℕ) (hb : 0 < b) :
    DyadicClock 18 (inputLength K b) (trace K b).length where
  V := (rawClock K b hb).V
  label := fun t => (rawClock K b hb).label
    ⟨t.val, by simpa only [clockStages_total] using t.isLt⟩
  A := (rawClock K b hb).A
  E := (rawClock K b hb).E
  nonneg := (rawClock K b hb).nonneg
  children := (rawClock K b hb).children
  root := (rawClock K b hb).root
  ordered := (rawClock K b hb).ordered
  bounded := fun w j => by
    simpa only [clockStages_total] using (rawClock K b hb).bounded w j
  partition := fun w j t => (rawClock K b hb).partition w j
    ⟨t.val, by simpa only [clockStages_total] using t.isLt⟩
  budget := (rawClock K b hb).budget

@[simp] theorem clock_volume (K b : ℕ) (hb : 0 < b) (w : List (Fin 1)) :
    (clock K b hb).V w = volume K b w := rfl

@[simp] theorem clock_start (K b : ℕ) (hb : 0 < b) (w : List (Fin 1)) (j : Fin 2) :
    (clock K b hb).A w j = StageClockAssembly.start (clockStages K b) (w, j) := rfl

@[simp] theorem clock_finish (K b : ℕ) (hb : 0 < b) (w : List (Fin 1)) (j : Fin 2) :
    (clock K b hb).E w j = StageClockAssembly.finish (clockStages K b) (w, j) := rfl

theorem clock_duration (K b : ℕ) (hb : 0 < b) (w : List (Fin 1)) (j : Fin 2) :
    (clock K b hb).E w j - (clock K b hb).A w j =
      if w.length ≤ K then blocksDuration (stage K b (w.length, j)) else 0 := by
  rw [clock_finish, clock_start, StageClockAssembly.finish_sub_start, clockStages_duration]

theorem trace_time_bound (K b : ℕ) (hb : 0 < b) :
    ((trace K b).length : ℝ) ≤ 36 * inputLength K b := by
  have h := (clock K b hb).total_time_le (by norm_num)
  norm_num at h
  exact h

end CascadeObstruction.C5
