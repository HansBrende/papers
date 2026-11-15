import BoundedStackDepth.Machines
import Transpose.Tape.CECount

/-!
# Constant-length refinement of interval residencies

Each interval has diameter at most two, and successive intervals share an
anchor. A twelve-position walk visits the interval on both sides of a
common pivot. This is a refinement of graph geometry, not of network gates.
-/

namespace LeanBacklog.BlockTCC

open Finset Transpose Transpose.Tape Transpose.Tape.Impl BoundedNesting MergeDepth BoundedStackDepth

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- Interval data and boundary anchors for a finite sequence of slots. -/
structure IntervalData (N : ℕ) where
  lo : ℕ → ℤ
  hi : ℕ → ℤ
  anchor : ℕ → ℤ
  ordered : ∀ y < N, lo y ≤ hi y
  width : ∀ y < N, hi y ≤ lo y + 2
  entry : ∀ y < N, lo y ≤ anchor y ∧ anchor y ≤ hi y
  exit : ∀ y < N, lo y ≤ anchor (y + 1) ∧ anchor (y + 1) ≤ hi y

/-- Two sweeps, with a pivot at position six and boundary padding. -/
def tour (l u a b : ℤ) : ℕ → ℤ
  | 0 => a
  | 1 => (a + l) / 2
  | 2 => l
  | 3 => (l + u) / 2
  | 4 => u
  | 5 => (l + u) / 2
  | 6 => l
  | 7 => (l + u) / 2
  | 8 => u
  | 9 => (u + b) / 2
  | _ => b

theorem tour_bounds {l u a b : ℤ} (hlu : l ≤ u) (hwidth : u ≤ l + 2)
    (ha : l ≤ a ∧ a ≤ u) (hb : l ≤ b ∧ b ≤ u) (j : ℕ) :
    l ≤ tour l u a b j ∧ tour l u a b j ≤ u := by
  by_cases hj : j < 10
  · interval_cases j <;> simp only [tour] <;> omega
  · have : tour l u a b j = b := by
      obtain ⟨n, rfl⟩ : ∃ n, j = n + 10 := ⟨j - 10, by omega⟩
      rfl
    rwa [this]

theorem tour_step {l u a b : ℤ} (hlu : l ≤ u) (hwidth : u ≤ l + 2)
    (ha : l ≤ a ∧ a ≤ u) (hb : l ≤ b ∧ b ≤ u) {j : ℕ} (hj : j < 11) :
    |tour l u a b (j + 1) - tour l u a b j| ≤ 1 := by
  interval_cases j <;> simp only [tour, abs_le] <;> omega

theorem tour_visits {l u a b z : ℤ} (hlu : l ≤ u) (hwidth : u ≤ l + 2)
    (hz : l ≤ z ∧ z ≤ u) :
    (∃ j, 2 ≤ j ∧ j ≤ 4 ∧ tour l u a b j = z) ∧
    (∃ j, 6 ≤ j ∧ j ≤ 8 ∧ tour l u a b j = z) := by
  by_cases hl : z = l
  · subst z; exact ⟨⟨2, by omega, by omega, rfl⟩, ⟨6, by omega, by omega, rfl⟩⟩
  by_cases hu : z = u
  · subst z; exact ⟨⟨4, by omega, by omega, rfl⟩, ⟨8, by omega, by omega, rfl⟩⟩
  have he : (l + u) / 2 = z := by omega
  exact ⟨⟨3, by omega, by omega, he⟩, ⟨7, by omega, by omega, he⟩⟩

namespace IntervalData

variable {N : ℕ} (Q : IntervalData N)

/-- The finite tour padded constantly after the final boundary. -/
def walk (t : ℕ) : ℤ :=
  if t < 12 * N then
    tour (Q.lo (t / 12)) (Q.hi (t / 12)) (Q.anchor (t / 12))
      (Q.anchor (t / 12 + 1)) (t % 12)
  else Q.anchor N

theorem walk_slot {y j : ℕ} (hy : y < N) (hj : j < 12) :
    Q.walk (12 * y + j) = tour (Q.lo y) (Q.hi y) (Q.anchor y) (Q.anchor (y + 1)) j := by
  have ht : 12 * y + j < 12 * N := by omega
  have hq : (12 * y + j) / 12 = y := by omega
  have hm : (12 * y + j) % 12 = j := by omega
  simp [walk, ht, hq, hm]

theorem isWalk : BoundedNesting.IsWalk Q.walk := by
  intro t
  by_cases ht : t < 12 * N
  · have hy : t / 12 < N := by omega
    by_cases hn : t + 1 < 12 * N
    · by_cases hm : t % 12 = 11
      · have hq : (t + 1) / 12 = t / 12 + 1 := by omega
        have hz : (t + 1) % 12 = 0 := by omega
        simp [walk, ht, hn, hm, hq, hz, tour]
      · have hq : (t + 1) / 12 = t / 12 := by omega
        have hz : (t + 1) % 12 = t % 12 + 1 := by omega
        simpa only [walk, ite_eq_left ht, ite_eq_left hn, hq, hz] using
          tour_step (Q.ordered _ hy) (Q.width _ hy) (Q.entry _ hy) (Q.exit _ hy)
            (show t % 12 < 11 by omega)
    · have hm : t % 12 = 11 := by omega
      have hq : t / 12 + 1 = N := by omega
      simp [walk, ht, hn, hm, tour, hq]
  · have hn : ¬ t + 1 < 12 * N := by omega
    simp [walk, ht, hn]

theorem walk_bounds {t : ℕ} (ht : t < 12 * N) :
    Q.lo (t / 12) ≤ Q.walk t ∧ Q.walk t ≤ Q.hi (t / 12) := by
  have hy : t / 12 < N := by omega
  simpa only [walk, ite_eq_left ht] using
    tour_bounds (Q.ordered _ hy) (Q.width _ hy) (Q.entry _ hy) (Q.exit _ hy) (t % 12)

theorem visits {y : ℕ} (hy : y < N) {z : ℤ} (hz : Q.lo y ≤ z ∧ z ≤ Q.hi y) :
    (∃ t, 12 * y + 2 ≤ t ∧ t ≤ 12 * y + 4 ∧ Q.walk t = z) ∧
    (∃ t, 12 * y + 6 ≤ t ∧ t ≤ 12 * y + 8 ∧ Q.walk t = z) := by
  obtain ⟨⟨i, hi, hi', he⟩, ⟨j, hj, hj', hf⟩⟩ := tour_visits
    (a := Q.anchor y) (b := Q.anchor (y + 1)) (Q.ordered y hy) (Q.width y hy) hz
  constructor
  · exact ⟨12 * y + i, by omega, by omega, (Q.walk_slot hy (by omega)).trans he⟩
  · exact ⟨12 * y + j, by omega, by omega, (Q.walk_slot hy (by omega)).trans hf⟩

end IntervalData

open Classical in
def nearLo (S : Finset ℤ) (c : ℤ) : ℤ := if c - 1 ∈ S then c - 1 else c

open Classical in
def nearHi (S : Finset ℤ) (c : ℤ) : ℤ := if c + 1 ∈ S then c + 1 else c

theorem near_ordered (S : Finset ℤ) (c : ℤ) : nearLo S c ≤ nearHi S c := by
  classical
  unfold nearLo nearHi
  split_ifs <;> omega

theorem near_width (S : Finset ℤ) (c : ℤ) : nearHi S c ≤ nearLo S c + 2 := by
  classical
  unfold nearLo nearHi
  split_ifs <;> omega

theorem near_mem_iff {S : Finset ℤ} {c z : ℤ} (hc : c ∈ S)
    (hS : S ⊆ {c - 1, c, c + 1}) : z ∈ S ↔ nearLo S c ≤ z ∧ z ≤ nearHi S c := by
  classical
  constructor
  · intro hz
    have hm := hS hz
    simp only [mem_insert, mem_singleton] at hm
    rcases hm with rfl | rfl | rfl <;> unfold nearLo nearHi <;> split_ifs <;> omega
  · intro hz
    have hcases : z = c - 1 ∨ z = c ∨ z = c + 1 := by
      unfold nearLo nearHi at hz
      split_ifs at hz <;> omega
    rcases hcases with rfl | rfl | rfl
    · by_contra h
      simp only [nearLo, ite_eq_right h] at hz
      omega
    · exact hc
    · by_contra h
      simp only [nearHi, ite_eq_right h] at hz
      omega

theorem slot_start_lt {r T y : ℕ} (hr : 1 ≤ r) (hy : y < numSlots r T) : y * r < T := by
  have hq : y + 1 ≤ (T + r - 1) / r := hy
  have hp := (Nat.le_div_iff_mul_le (show 0 < r by omega)).mp hq
  have he : (y + 1) * r = y * r + r := by ring
  omega

theorem resident_center_mem {r T y : ℕ} {h : ℕ → ℤ}
    (hr : 1 ≤ r) (hy : y < numSlots r T) :
    curBlock r h (y * r) ∈ pairRes r h T y := by
  apply mem_pairRes.mpr
  exact ⟨y * r, le_rfl, by omega, slot_start_lt hr hy, cur_mem_residentPair _⟩

/-- The block just before a boundary belongs to the next resident pair. -/
theorem old_current_mem (r : ℕ) (h : ℕ → ℤ) (t : ℕ) :
    curBlock r h t ∈ residentPair r h (t + 1) := by
  classical
  rw [residentPair_succ]
  split_ifs
  · simp
  · exact cur_mem_residentPair t

/-- Boundary anchors are actual current blocks, clamped at the last step. -/
def residentAnchor (r T : ℕ) (h : ℕ → ℤ) (y : ℕ) : ℤ :=
  curBlock r h (min (y * r) T - 1)

theorem residentAnchor_entry {r T y : ℕ} {h : ℕ → ℤ}
    (hr : 1 ≤ r) (hy : y < numSlots r T) :
    residentAnchor r T h y ∈ pairRes r h T y := by
  have hstart := slot_start_lt hr hy
  rw [residentAnchor, min_eq_left hstart.le]
  by_cases hz : y = 0
  · subst y
    simpa using resident_center_mem (h := h) hr hy
  · have hp : 0 < y * r := Nat.mul_pos (by omega) hr
    apply mem_pairRes.mpr
    refine ⟨y * r, le_rfl, by omega, hstart, ?_⟩
    simpa only [Nat.sub_add_cancel hp] using old_current_mem r h (y * r - 1)

theorem residentAnchor_exit {r T y : ℕ} {h : ℕ → ℤ}
    (hr : 1 ≤ r) (hy : y < numSlots r T) :
    residentAnchor r T h (y + 1) ∈ pairRes r h T y := by
  have hstart := slot_start_lt hr hy
  have he : (y + 1) * r = y * r + r := by ring
  apply mem_pairRes.mpr
  refine ⟨min ((y + 1) * r) T - 1, ?_, ?_, ?_, cur_mem_residentPair _⟩ <;>
    rw [he] <;> omega

open Classical in
/-- The actual pair residencies of one work walk supply the interval data. -/
noncomputable def residentData {r : ℕ} (h : ℕ → ℤ) (T : ℕ)
    (hh : UnitSteps h) (hr : 1 ≤ r) : IntervalData (numSlots r T) where
  lo y := nearLo (pairRes r h T y) (curBlock r h (y * r))
  hi y := nearHi (pairRes r h T y) (curBlock r h (y * r))
  anchor := residentAnchor r T h
  ordered _ _ := near_ordered _ _
  width _ _ := near_width _ _
  entry y hy := (near_mem_iff (resident_center_mem hr hy) (pairRes_subset hh hr T y)).mp
    (residentAnchor_entry hr hy)
  exit y hy := (near_mem_iff (resident_center_mem hr hy) (pairRes_subset hh hr T y)).mp
    (residentAnchor_exit hr hy)

theorem residentData_mem_iff {r T y : ℕ} {h : ℕ → ℤ}
    (hh : UnitSteps h) (hr : 1 ≤ r) (hy : y < numSlots r T) (z : ℤ) :
    z ∈ pairRes r h T y ↔
      (residentData h T hh hr).lo y ≤ z ∧ z ≤ (residentData h T hh hr).hi y :=
  near_mem_iff (resident_center_mem hr hy) (pairRes_subset hh hr T y)

/-- A skipped-slot residency chord becomes one genuine last-visit hop,
with endpoints on the correct sides of the two pivots. -/
theorem IntervalData.chord_hop {N x z : ℕ} (Q : IntervalData N) {β : ℤ}
    (hxz : x + 1 < z) (hz : z < N)
    (hxβ : Q.lo x ≤ β ∧ β ≤ Q.hi x) (hzβ : Q.lo z ≤ β ∧ β ≤ Q.hi z)
    (hgap : ∀ y, x < y → y < z → ¬ (Q.lo y ≤ β ∧ β ≤ Q.hi y)) :
    ∃ p u, 12 * x + 6 ≤ p ∧ p < 12 * (x + 1) ∧
      12 * z ≤ u ∧ u ≤ 12 * z + 4 ∧ IsHop Q.walk (12 * N) p u := by
  classical
  obtain ⟨_, ⟨a, ha, ha', hav⟩⟩ := Q.visits (show x < N by omega) hxβ
  obtain ⟨⟨b, hb, hb', hbv⟩, _⟩ := Q.visits hz hzβ
  let A := (Ico (12 * x) (12 * (x + 1))).filter (fun t => Q.walk t = β)
  let B := (Ico (12 * z) (12 * (z + 1))).filter (fun t => Q.walk t = β)
  have haA : a ∈ A := mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega, by omega⟩, hav⟩
  have hbB : b ∈ B := mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega, by omega⟩, hbv⟩
  let p := A.max' ⟨a, haA⟩
  let u := B.min' ⟨b, hbB⟩
  have hpA : p ∈ A := max'_mem _ _
  have huB : u ∈ B := min'_mem _ _
  obtain ⟨hpI, hpβ⟩ := mem_filter.mp hpA
  obtain ⟨huI, huβ⟩ := mem_filter.mp huB
  obtain ⟨hp0, hp1⟩ := mem_Ico.mp hpI
  obtain ⟨hu0, hu1⟩ := mem_Ico.mp huI
  have hap : a ≤ p := le_max' _ _ haA
  have hub : u ≤ b := min'_le _ _ hbB
  refine ⟨p, u, by omega, hp1, hu0, by omega, by omega, by omega,
    huβ.trans hpβ.symm, ?_⟩
  intro t ht he
  obtain ⟨hpt, htu⟩ := mem_Ioo.mp ht
  have htβ : Q.walk t = β := he.trans hpβ
  by_cases htx : t / 12 = x
  · have htA : t ∈ A := mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega, by omega⟩, htβ⟩
    have := le_max' A t htA
    omega
  by_cases htz : t / 12 = z
  · have htB : t ∈ B := mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega, by omega⟩, htβ⟩
    have := min'_le B t htB
    omega
  have htN : t < 12 * N := by omega
  have hbounds := Q.walk_bounds htN
  rw [htβ] at hbounds
  exact hgap (t / 12) (by omega) (by omega) hbounds

#print axioms IntervalData
#print axioms tour
#print axioms tour_bounds
#print axioms tour_step
#print axioms tour_visits
#print axioms IntervalData.walk
#print axioms IntervalData.walk_slot
#print axioms IntervalData.isWalk
#print axioms IntervalData.walk_bounds
#print axioms IntervalData.visits
#print axioms nearLo
#print axioms nearHi
#print axioms near_ordered
#print axioms near_width
#print axioms near_mem_iff
#print axioms slot_start_lt
#print axioms resident_center_mem
#print axioms old_current_mem
#print axioms residentAnchor
#print axioms residentAnchor_entry
#print axioms residentAnchor_exit
#print axioms residentData
#print axioms residentData_mem_iff
#print axioms IntervalData.chord_hop

end LeanBacklog.BlockTCC
