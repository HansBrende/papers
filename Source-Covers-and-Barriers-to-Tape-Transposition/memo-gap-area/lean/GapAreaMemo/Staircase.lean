import GapAreaMemo.Zigzag

set_option autoImplicit false

/-!
# Staircases of segments on fresh cells

A head performs segments one after another, each starting from the level at
which the previous one stopped and never going below it, while the earlier
segments never go above it. No return straddles a splice, so the returns of
the head are exactly the returns of its segments.
-/

namespace SourceCovers.Staircase

open Finset BoundedNesting

/-- Run `x` up to time `s`, then `c + y`. -/
def append (x : ℕ → ℤ) (c : ℤ) (y : ℕ → ℤ) (s t : ℕ) : ℤ :=
  if t ≤ s then x t else c + y t

theorem append_before {x y : ℕ → ℤ} {c : ℤ} {s t : ℕ} (ht : t ≤ s) :
    append x c y s t = x t := by simp only [append, ht, ite_true]

theorem append_on {x y : ℕ → ℤ} {c : ℤ} {s t : ℕ} (hx : x s = c) (hy : y s = 0) (ht : s ≤ t) :
    append x c y s t = c + y t := by
  by_cases he : t ≤ s
  · have : t = s := by omega
    subst this
    rw [append_before le_rfl, hx, hy, add_zero]
  · simp only [append, he, ite_false]

theorem isWalk {x y : ℕ → ℤ} {c : ℤ} {s : ℕ} (hx : IsWalk x) (hy : IsWalk y) (hxs : x s = c)
    (hys : y s = 0) : IsWalk (append x c y s) := by
  intro t
  by_cases ht : t < s
  · rw [append_before (show t + 1 ≤ s by omega), append_before ht.le]; exact hx t
  · rw [append_on hxs hys (show s ≤ t + 1 by omega), append_on hxs hys (show s ≤ t by omega),
      add_sub_add_left_eq_sub]
    exact hy t

/-- **No return straddles a splice.** -/
theorem hop_iff {x y : ℕ → ℤ} {c : ℤ} {s T p u : ℕ} (hxs : x s = c) (hys : y s = 0)
    (hx : ∀ t ≤ s, x t ≤ c) (hy : ∀ t, 0 ≤ y t) :
    IsHop (append x c y s) T p u ↔ (u ≤ s ∧ IsHop x T p u) ∨ (s ≤ p ∧ IsHop y T p u) := by
  constructor
  · intro hh
    by_cases hu : u ≤ s
    · refine Or.inl ⟨hu, (NativeWalkLocal.hop_iff_of_shift_on 0 (fun t _ ht => ?_)).mp hh⟩
      rw [append_before (ht.trans hu), zero_add]
    · have hp : s ≤ p := by
        by_contra! hp
        have hlo : append x c y s p ≤ c := by rw [append_before hp.le]; exact hx p hp.le
        have hhi : c ≤ append x c y s u := by
          rw [append_on hxs hys (by omega)]
          have := hy u
          omega
        have heq := hh.2.2.1
        have he : append x c y s p = c := by omega
        apply hh.2.2.2 s (mem_Ioo.mpr ⟨hp, by omega⟩)
        rw [append_before le_rfl, hxs, he]
      exact Or.inr ⟨hp, (NativeWalkLocal.hop_iff_of_shift_on c (fun t ht _ =>
        append_on hxs hys (hp.trans ht))).mp hh⟩
  · rintro (⟨hu, hh⟩ | ⟨hp, hh⟩)
    · exact (NativeWalkLocal.hop_iff_of_shift_on 0 (fun t _ ht => by
        rw [append_before (ht.trans hu), zero_add])).mpr hh
    · exact (NativeWalkLocal.hop_iff_of_shift_on c (fun t ht _ =>
        append_on hxs hys (hp.trans ht))).mpr hh

/-- A staircase of `n` segments: segment `m` has walk `seg m`, height `ht m` and
splice time `start m`. -/
def walk (seg : ℕ → ℕ → ℤ) (ht start : ℕ → ℕ) : ℕ → ℕ → ℤ
  | 0 => fun _ => 0
  | m + 1 => append (walk seg ht start m) (∑ j ∈ range m, (ht j : ℤ)) (seg m) (start m)

/-- Hypotheses on the segments: each starts at its base at its splice time,
stays within `[0, ht m]`, is a walk, and is parked at its top from the next
splice time on. Splice times increase. -/
structure Valid (seg : ℕ → ℕ → ℤ) (ht start : ℕ → ℕ) : Prop where
  walk : ∀ m, IsWalk (seg m)
  at_start : ∀ m, seg m (start m) = 0
  nonneg : ∀ m t, 0 ≤ seg m t
  le_top : ∀ m t, seg m t ≤ ht m
  parked : ∀ m t, start (m + 1) ≤ t → seg m t = ht m
  start_mono : StrictMono start
  before : ∀ m t, t ≤ start m → seg m t = 0

variable {seg : ℕ → ℕ → ℤ} {ht start : ℕ → ℕ}

theorem walk_le_base (hv : Valid seg ht start) :
    ∀ n t, walk seg ht start n t ≤ ∑ j ∈ range n, (ht j : ℤ)
  | 0, t => by simp [walk]
  | m + 1, t => by
    simp only [walk, append]
    split_ifs with h1
    · have := walk_le_base hv m t
      rw [sum_range_succ]
      have : (0 : ℤ) ≤ ht m := Nat.cast_nonneg _
      linarith
    · rw [sum_range_succ]
      have := hv.le_top m t
      linarith

theorem walk_nonneg (hv : Valid seg ht start) : ∀ n t, 0 ≤ walk seg ht start n t
  | 0, t => by simp [walk]
  | m + 1, t => by
    simp only [walk, append]
    split_ifs
    · exact walk_nonneg hv m t
    · have := hv.nonneg m t
      have : (0 : ℤ) ≤ ∑ j ∈ range m, (ht j : ℤ) := sum_nonneg fun _ _ => Nat.cast_nonneg _
      linarith

/-- From the splice time of segment `n` on, the first `n` segments are parked at their top. -/
theorem walk_parked (hv : Valid seg ht start) :
    ∀ n t, start n ≤ t → walk seg ht start n t = ∑ j ∈ range n, (ht j : ℤ)
  | 0, t, _ => by simp [walk]
  | m + 1, t, h => by
    have hm : start m < start (m + 1) := hv.start_mono (Nat.lt_succ_self m)
    rw [walk, append_on (walk_parked hv m _ le_rfl) (hv.at_start m) (by omega),
      hv.parked m t h, sum_range_succ]

theorem isWalk_walk (hv : Valid seg ht start) : ∀ n, IsWalk (walk seg ht start n)
  | 0 => fun t => by simp [walk]
  | m + 1 => isWalk (isWalk_walk hv m) (hv.walk m) (walk_parked hv m _ le_rfl) (hv.at_start m)

/-- **Returns of a staircase.** Each return is a return of one segment, after its
splice time and, unless it is the last segment, before the next splice time. -/
theorem walk_hop_iff (hv : Valid seg ht start) :
    ∀ n {T p u : ℕ}, IsHop (walk seg ht start n) T p u ↔
      ∃ m < n, start m ≤ p ∧ (m + 1 < n → u ≤ start (m + 1)) ∧ IsHop (seg m) T p u
  | 0, T, p, u => by
    simp only [walk, not_lt_zero, false_and, exists_false, iff_false]
    intro hh
    exact hh.2.2.2 (p + 1) (mem_Ioo.mpr ⟨by omega, by have := hh.1; omega⟩) rfl
  | m + 1, T, p, u => by
    rw [walk, Staircase.hop_iff (walk_parked hv m _ le_rfl) (hv.at_start m)
      (fun t _ => walk_le_base hv m t) (hv.nonneg m), walk_hop_iff hv m]
    constructor
    · rintro (⟨hu, j, hj, h1, h2, h3⟩ | ⟨hp, hh⟩)
      · refine ⟨j, by omega, h1, fun hj' => ?_, h3⟩
        by_cases hjm : j + 1 < m
        · exact h2 hjm
        · have : j + 1 = m := by omega
          rw [this]; exact hu
      · exact ⟨m, by omega, hp, fun h => absurd h (by omega), hh⟩
    · rintro ⟨j, hj, h1, h2, h3⟩
      by_cases hjm : j = m
      · subst hjm
        exact Or.inr ⟨h1, h3⟩
      · have hjm' : j < m := by omega
        have hu : u ≤ start m := by
          have := h2 (by omega)
          exact this.trans (hv.start_mono.monotone (by omega))
        exact Or.inl ⟨hu, j, hjm', h1, fun h => h2 (by omega), h3⟩

/-- On the active range of segment `m`, the staircase is the segment shifted by its base. -/
theorem walk_on (hv : Valid seg ht start) {n m t : ℕ} (hm : m < n) (h1 : start m ≤ t)
    (h2 : m + 1 < n → t ≤ start (m + 1)) :
    walk seg ht start n t = (∑ j ∈ range m, (ht j : ℤ)) + seg m t := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [walk]
    by_cases hmn : m = n
    · subst hmn
      exact append_on (walk_parked hv m _ le_rfl) (hv.at_start m) h1
    · have hmn' : m < n := by omega
      have ht : t ≤ start n := by
        have := h2 (by omega)
        exact this.trans (hv.start_mono.monotone (by omega))
      rw [append_before ht]
      exact ih hmn' (fun h => h2 (by omega))

end SourceCovers.Staircase
