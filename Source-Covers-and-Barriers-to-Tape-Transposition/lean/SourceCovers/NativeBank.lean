import SourceCovers.FreshSweep

set_option autoImplicit false

/-! A repeated head uses a fresh spatial interval for each bank. The gap
between banks is a pause; all nonadjacent returns belong to one sweep. -/

namespace SourceCovers.NativeBank

open Finset BoundedNesting

def start (h D r : ℕ) : ℕ := D + 4 * r * h

def walk (h D : ℕ) : ℕ → ℕ → ℤ
  | 0 => fun _ => 0
  | n + 1 => FreshSweep.append (walk h D n) (n * h : ℕ) h (start h D n)

theorem separated {h D r n : ℕ} (hr : r < n) : start h D r + 3 * h ≤ start h D n := by
  have hm := Nat.mul_le_mul_right (4 * h) (Nat.succ_le_of_lt hr)
  dsimp only [start]
  nlinarith

/-- By the next bank's start, every preceding bank is parked at its new top. -/
theorem after (h D n : ℕ) {t : ℕ} (ht : start h D n ≤ t) :
    walk h D n t = (n * h : ℕ) := by
  induction n generalizing t with
  | zero => simp [walk]
  | succ n ih =>
    rw [walk, FreshSweep.after (ih (t := start h D n) le_rfl)
      ((separated (show n < n + 1 by omega)).trans ht)]
    push_cast
    ring

theorem bounds (h D n t : ℕ) : 0 ≤ walk h D n t ∧ walk h D n t ≤ (n * h : ℕ) := by
  induction n generalizing t with
  | zero => simp [walk]
  | succ n ih =>
    simpa only [walk, Nat.add_mul, Nat.one_mul, Nat.cast_add] using
      FreshSweep.bounds (show (0 : ℤ) ≤ (n * h : ℕ) by positivity)
        (fun t _ => ih t) (after h D n le_rfl) t

@[simp] theorem zero (h D n : ℕ) : walk h D n 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [walk, FreshSweep.before (Nat.zero_le _), ih]

theorem isWalk (h D n : ℕ) : IsWalk (walk h D n) := by
  induction n with
  | zero => intro t; simp [walk]
  | succ n ih => exact FreshSweep.isWalk ih (after h D n le_rfl)

theorem entries_top_card {h : ℕ} (hh : 0 < h) (D n T : ℕ) :
    (entries (walk h D n) (n * h : ℕ) T).card ≤ 2 := by
  cases n with
  | zero =>
    simpa only [walk, Nat.zero_mul, Nat.cast_zero] using
      (NativeWalkLocal.entries_const_card_le_one 0 0 T).trans (by norm_num : (1 : ℕ) ≤ 2)
  | succ n =>
    simpa only [walk, Nat.add_mul, Nat.one_mul, Nat.cast_add] using
      FreshSweep.entries_top_card (after h D n le_rfl) (fun t _ => (bounds h D n t).2) hh T

theorem entries_card_le_three {h : ℕ} (hh : 0 < h) (D n : ℕ) (c : ℤ) (T : ℕ) :
    (entries (walk h D n) c T).card ≤ 3 := by
  induction n generalizing c T with
  | zero => exact (NativeWalkLocal.entries_const_card_le_one 0 c T).trans (by omega)
  | succ n ih =>
    exact FreshSweep.entries_card_le_three (after h D n le_rfl)
      (fun t _ => (bounds h D n t).2) ih (entries_top_card hh D n) c T

/-- The entire active span of a bank is a spatial translate of one sweep. -/
theorem on_bank {h D n r t : ℕ} (hr : r < n)
    (ht : start h D r ≤ t) (hu : t ≤ start h D r + 3 * h) :
    walk h D n t = (r * h : ℕ) + NativeSweep.walk h (start h D r) t := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases he : r = n
    · subst r
      exact FreshSweep.on_late (after h D n le_rfl) ht
    · have hrn : r < n := by omega
      rw [walk, FreshSweep.before (hu.trans (separated hrn))]
      exact ih hrn

/-- This is an exhaustive union of actual one-sweep return relations.
No return across two banks, or during a pause, is omitted. -/
theorem hop_iff (h D n T p u : ℕ) : IsHop (walk h D n) T p u ↔
    ∃ r < n, IsHop (NativeSweep.walk h (start h D r)) T p u := by
  induction n with
  | zero =>
    constructor
    · intro hh
      exact False.elim (hh.2.2.2 (p + 1)
        (mem_Ioo.mpr ⟨by omega, by have := hh.1; omega⟩) rfl)
    · rintro ⟨r, hr, _⟩
      omega
  | succ n ih =>
    rw [walk, FreshSweep.hop_iff (after h D n le_rfl) (fun t _ => (bounds h D n t).2)]
    constructor
    · rintro (⟨_, hh⟩ | ⟨_, hh⟩)
      · obtain ⟨r, hr, hh⟩ := ih.mp hh
        exact ⟨r, by omega, hh⟩
      · exact ⟨n, by omega, hh⟩
    · rintro ⟨r, hr, hh⟩
      by_cases he : r = n
      · subst r
        exact Or.inr ⟨(NativeSweep.hop_bounds hh).1, hh⟩
      · have hrn : r < n := by omega
        exact Or.inl ⟨(NativeSweep.hop_bounds hh).2.trans (separated hrn), ih.mpr ⟨r, hrn, hh⟩⟩

theorem owner_on_bank {h D n r T p u : ℕ} (hr : r < n)
    (hh : IsHop (NativeSweep.walk h (start h D r)) T p u) :
    hopOwner (walk h D n) p u = hopOwner (NativeSweep.walk h (start h D r)) p u := by
  have hb := NativeSweep.hop_bounds hh
  apply NativeWalkLocal.hopOwner_eq_of_shift_on (r * h : ℕ) hh.1
  intro t ht hu
  exact on_bank hr (hb.1.trans ht) (hu.trans hb.2)

end SourceCovers.NativeBank
