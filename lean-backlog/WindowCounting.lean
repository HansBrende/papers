import WindowAmortization
import WindowLabels
import Mathlib.Data.Finset.Option

/-!
# Native predecessor-window counts

The clipped native window labels are enumerated on a fixed finite tape span.
The actual updates then instantiate the interval-overwrite amortization.
-/

namespace LeanBacklog.WindowCounting

open Finset BoundedNesting WindowAmortization WindowLabels
open scoped BigOperators

section Packing

variable {α : Type*}

/-- Values on a consecutive finite range of natural indices. -/
def tabulate (start length : ℕ) (f : ℕ → α) : List α :=
  (List.range' start length).map f

theorem mem_range'_iff {start length j : ℕ} :
    j ∈ List.range' start length ↔ start ≤ j ∧ j < start + length := by
  rw [List.mem_range']
  constructor
  · rintro ⟨i, hi, rfl⟩
    omega
  · rintro ⟨hj, hlen⟩
    exact ⟨j - start, by omega, by omega⟩

theorem tabulate_add (start m n : ℕ) (f : ℕ → α) :
    tabulate start (m + n) f = tabulate start m f ++ tabulate (start + m) n f := by
  unfold tabulate
  rw [← List.range'_append (s := start) (m := m) (n := n) (step := 1)]
  simp only [Nat.one_mul, List.map_append]

theorem tabulate_congr {start length : ℕ} {f g : ℕ → α}
    (h : ∀ j, start ≤ j → j < start + length → f j = g j) :
    tabulate start length f = tabulate start length g := by
  apply List.map_congr_left
  intro j hj
  exact h j (mem_range'_iff.mp hj).1 (mem_range'_iff.mp hj).2

theorem tabulate_split (left middle right : ℕ) (f : ℕ → α) :
    tabulate 0 (left + middle + right) f =
      tabulate 0 left f ++ tabulate left middle f ++ tabulate (left + middle) right f := by
  rw [tabulate_add, tabulate_add]
  simp only [Nat.zero_add]

variable [DecidableEq α]

/-- The finite-list representation of a pointwise interval overwrite. -/
theorem intervalOverwrite_tabulate (before after : ℕ → α) (n lo hi : ℕ)
    (hlo : lo ≤ hi) (hhi : hi ≤ n) (value : α) (charged : Finset α)
    (hupdate : ∀ j < n, after j = if lo ≤ j ∧ j < hi then value else before j)
    (hcharge : ∀ a ∈ charged, ∃ j, lo ≤ j ∧ j < hi ∧ before j = a) :
    IntervalOverwrite (tabulate 0 n before) (tabulate 0 n after) charged := by
  have hsplit (f : ℕ → α) : tabulate 0 n f =
      tabulate 0 lo f ++ tabulate lo (hi - lo) f ++ tabulate hi (n - hi) f := by
    simpa only [Nat.add_sub_of_le hlo, Nat.add_sub_of_le hhi] using
      tabulate_split lo (hi - lo) (n - hi) f
  have hleft : tabulate 0 lo after = tabulate 0 lo before := by
    apply tabulate_congr
    intro j _ hj
    rw [hupdate j (by omega)]
    simp [show ¬ (lo ≤ j ∧ j < hi) by omega]
  have hright : tabulate hi (n - hi) after = tabulate hi (n - hi) before := by
    apply tabulate_congr
    intro j hj hjn
    rw [hupdate j (by omega)]
    simp [show ¬ (lo ≤ j ∧ j < hi) by omega]
  have hmiddle : tabulate lo (hi - lo) after = List.replicate (hi - lo) value := by
    calc
      _ = tabulate lo (hi - lo) (fun _ => value) := by
        apply tabulate_congr
        intro j hj hjh
        rw [hupdate j (by omega)]
        simp [show lo ≤ j ∧ j < hi by omega]
      _ = _ := by simp [tabulate]
  refine ⟨tabulate 0 lo before, tabulate lo (hi - lo) before,
    tabulate hi (n - hi) before, value, hsplit before, ?_, ?_⟩
  · rw [hsplit after, hleft, hmiddle, hright]
    simp [tabulate]
  · intro a ha
    obtain ⟨j, hjlo, hjhi, hja⟩ := hcharge a ha
    exact List.mem_toFinset.mpr (List.mem_map.mpr
      ⟨j, mem_range'_iff.mpr ⟨hjlo, by omega⟩, hja⟩)

/-- Integer-indexed interval updates pack into the preceding finite-list
interface. Only the spatial interval and its actual charged labels are used. -/
theorem intervalOverwrite_integer (before after : ℤ → α) (base : ℤ) (n : ℕ)
    (S : Finset ℤ) (value : α) (charged : Finset α)
    (hspan : ∀ z ∈ S, base ≤ z ∧ z < base + n)
    (hinterval : ∀ u ∈ S, ∀ v ∈ S, ∀ z, u ≤ z → z ≤ v → z ∈ S)
    (hupdate : ∀ z, after z = if z ∈ S then value else before z)
    (hcharge : charged ⊆ S.image before) :
    IntervalOverwrite (tabulate 0 n (fun j => before (base + j)))
      (tabulate 0 n (fun j => after (base + j))) charged := by
  classical
  by_cases hne : S.Nonempty
  · let lo := (S.min' hne - base).toNat
    let hi := (S.max' hne - base).toNat + 1
    have hmin := hspan _ (min'_mem S hne)
    have hmax := hspan _ (max'_mem S hne)
    have horder : S.min' hne ≤ S.max' hne := min'_le _ _ (max'_mem _ hne)
    have hlo : lo ≤ hi := by dsimp [lo, hi]; omega
    have hhi : hi ≤ n := by dsimp [hi]; omega
    have hmem (j : ℕ) : base + (j : ℤ) ∈ S ↔ lo ≤ j ∧ j < hi := by
      constructor
      · intro hj
        have h₁ := min'_le _ _ hj
        have h₂ := le_max' _ _ hj
        dsimp [lo, hi]
        omega
      · intro hj
        apply hinterval _ (min'_mem _ hne) _ (max'_mem _ hne)
        · dsimp [lo, hi] at hj
          omega
        · dsimp [lo, hi] at hj
          omega
    apply intervalOverwrite_tabulate _ _ n lo hi hlo hhi value charged
    · intro j _
      rw [hupdate]
      simp only [hmem]
    · intro a ha
      obtain ⟨z, hz, hza⟩ := mem_image.mp (hcharge ha)
      let j := (z - base).toNat
      have hzspan := hspan z hz
      have hjz : base + (j : ℤ) = z := by dsimp [j]; omega
      have hj := (hmem j).mp (by simpa only [hjz] using hz)
      exact ⟨j, hj.1, hj.2, by simpa only [hjz] using hza⟩
  · have hS : S = ∅ := not_nonempty_iff_eq_empty.mp hne
    have hc : charged = ∅ := by simpa [hS] using hcharge
    apply intervalOverwrite_tabulate _ _ n 0 0 (le_refl _) (Nat.zero_le _) value charged
    · intro j _
      simp [hupdate, hS]
    · simp [hc]

end Packing

/-- Actual predecessor-window labels, excluding never-visited cells. -/
noncomputable def predecessorWindows (x : ℕ → ℤ) (h T i : ℕ) : Finset ℕ :=
  (visitedCells x (min T (i * h)) (min T ((i + 1) * h))).biUnion
    (fun z => (windowLabel x h (min T (i * h)) z).toFinset)

theorem mem_predecessorWindows {x : ℕ → ℤ} {h T i j : ℕ} :
    j ∈ predecessorWindows x h T i ↔
      ∃ z ∈ visitedCells x (min T (i * h)) (min T ((i + 1) * h)),
        windowLabel x h (min T (i * h)) z = some j := by
  simp [predecessorWindows, Option.mem_def]

theorem mem_predecessorWindows_iff_lastBefore {x : ℕ → ℤ} {h T i j : ℕ} :
    j ∈ predecessorWindows x h T i ↔
      ∃ z ∈ visitedCells x (min T (i * h)) (min T ((i + 1) * h)),
        ∃ p, lastBefore x (min T (i * h)) z = some p ∧ p / h = j := by
  simp only [mem_predecessorWindows, windowLabel, Option.map_eq_some_iff]

theorem predecessorWindow_lt {x : ℕ → ℤ} {h T i j : ℕ} (hh : 0 < h)
    (hj : j ∈ predecessorWindows x h T i) : j < i := by
  obtain ⟨z, -, p, hp, rfl⟩ := mem_predecessorWindows_iff_lastBefore.mp hj
  have hpc := (lastBefore_eq_some_iff.mp hp).1
  exact (Nat.div_lt_iff_lt_mul hh).mpr (hpc.trans_le (min_le_right _ _))

/-- One finite, nonempty tape span contains every cell relevant before T. -/
noncomputable def labelTape (x : ℕ → ℤ) (h T i : ℕ) : List (Option ℕ) :=
  tabulate 0 (2 * T + 1) (fun j =>
    windowLabel x h (min T (i * h)) (x 0 - T + j))

@[simp] theorem labelTape_zero (x : ℕ → ℤ) (h T : ℕ) :
    labelTape x h T 0 = List.replicate (2 * T + 1) none := by
  simp [labelTape, tabulate]

/-- Every native window gives a genuine finite-list interval overwrite, with
exactly its distinct earlier-window labels charged (never is not charged). -/
theorem native_intervalOverwrite {x : ℕ → ℤ} (hx : IsWalk x) (h T i : ℕ) :
    IntervalOverwrite (labelTape x h T i) (labelTape x h T (i + 1))
      ((predecessorWindows x h T i).image some) := by
  classical
  apply intervalOverwrite_integer
    (windowLabel x h (min T (i * h)))
    (windowLabel x h (min T ((i + 1) * h)))
    (x 0 - T) (2 * T + 1)
    (visitedCells x (min T (i * h)) (min T ((i + 1) * h)))
    (some i) ((predecessorWindows x h T i).image some)
  · intro z hz
    obtain ⟨t, -, ht, htz⟩ := mem_visitedCells.mp hz
    have htT : t < T := ht.trans_le (min_le_left _ _)
    have hzall : z ∈ visitedCells x 0 T :=
      mem_visitedCells.mpr ⟨t, Nat.zero_le _, htT, htz⟩
    have hb := mem_Icc.mp (visitedCells_subset_fixed_span hx T hzall)
    constructor
    · exact hb.1
    · push_cast
      omega
  · intro u hu v hv z huz hzv
    exact visitedCells_between hx hu hv huz hzv
  · exact windowLabel_overwrite_clipped x h T i
  · intro a ha
    obtain ⟨j, hj, rfl⟩ := mem_image.mp ha
    obtain ⟨z, hz, hlabel⟩ := mem_predecessorWindows.mp hj
    exact mem_image.mpr ⟨z, hz, hlabel⟩

/-- Native amortized predecessor-window bound, for any initial number N of
clipped windows. Empty tails beyond T and zero-width windows contribute zero. -/
theorem sum_predecessorWindows_le_three_mul {x : ℕ → ℤ} (hx : IsWalk x)
    (h T N : ℕ) :
    (∑ i ∈ range N, (predecessorWindows x h T i).card) ≤ 3 * N := by
  have hsum := sum_encountered_le_three_mul
    (labelTape x h T) (fun i => (predecessorWindows x h T i).image some)
    N (2 * T + 1) none (by omega) (labelTape_zero x h T)
    (fun i _ => native_intervalOverwrite hx h T i)
  simpa only [card_image_of_injective _ (Option.some_injective ℕ)] using hsum

#print axioms native_intervalOverwrite
#print axioms sum_predecessorWindows_le_three_mul

end LeanBacklog.WindowCounting
