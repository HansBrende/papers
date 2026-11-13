import WindowLabels

/-!
# Exact native guards at bad time windows

For each selected window, reveal its preceding state step and every actual
work predecessor lying before the window. The cut has at most `(k+1)*h`
steps per window. Every dependency path avoiding the cut after its root
stays inside a selected window once it enters one.

No unit-speed, correctness, or assumed predecessor-count hypothesis is used
for the guard statements. `external_prev_windowLabel` links an actual
cross-window work edge to the native last-window labels counted elsewhere.

Check from the Paper 15 Lean package with the backlog build directory on
`LEAN_PATH`, after compiling `WindowLabels.lean` there.
-/

namespace LeanBacklog.WindowGuards

open Finset BoundedNesting MergeDepth WindowLabels
open scoped BigOperators

variable {k : ℕ}

/-- Before-transition times of the possibly shortened window. -/
def windowTimes (T h i : ℕ) : Finset ℕ :=
  Ico (i * h) (min T ((i + 1) * h))

theorem mem_windowTimes {T h i t : ℕ} :
    t ∈ windowTimes T h i ↔ i * h ≤ t ∧ t < T ∧ t < (i + 1) * h := by
  simp [windowTimes]

theorem card_windowTimes_le (T h i : ℕ) : (windowTimes T h i).card ≤ h := by
  simp only [windowTimes, Nat.card_Ico]
  have hb : min T ((i + 1) * h) ≤ i * h + h := by
    simpa only [Nat.add_mul, Nat.one_mul] using (min_le_right T ((i + 1) * h))
  omega

/-- Every actual last work visit before the start of this window. -/
noncomputable def externalWork (xs : Fin k → ℕ → ℤ) (T h i : ℕ) : Finset ℕ :=
  ((windowTimes T h i).biUnion fun t =>
    univ.biUnion fun j : Fin k => (prevS (xs j) t).toFinset).filter (· < i * h)

theorem mem_externalWork {xs : Fin k → ℕ → ℤ} {T h i u : ℕ} :
    u ∈ externalWork xs T h i ↔
      (∃ t ∈ windowTimes T h i, ∃ j, prevS (xs j) t = some u) ∧ u < i * h := by
  classical
  simp [externalWork]

theorem card_externalWork_le (xs : Fin k → ℕ → ℤ) (T h i : ℕ) :
    (externalWork xs T h i).card ≤ k * (windowTimes T h i).card := by
  classical
  refine (card_filter_le _ _).trans (card_biUnion_le.trans ?_)
  calc
    (∑ t ∈ windowTimes T h i,
        (univ.biUnion fun j : Fin k => (prevS (xs j) t).toFinset).card)
        ≤ ∑ _t ∈ windowTimes T h i, k := by
      apply sum_le_sum
      intro t ht
      refine card_biUnion_le.trans ?_
      calc
        (∑ j : Fin k, (prevS (xs j) t).toFinset.card) ≤ ∑ _j : Fin k, 1 :=
          sum_le_sum fun j _ => by cases prevS (xs j) t <;> simp
        _ = k := by simp
    _ = k * (windowTimes T h i).card := by simp [Nat.mul_comm]

/-- The state boundary costs at most one extra step; at the initial
window or past the horizon there is no predecessor to reveal. -/
noncomputable def windowGuard (xs : Fin k → ℕ → ℤ) (T h i : ℕ) : Finset ℕ :=
  (if 0 < i * h ∧ i * h < T then {i * h - 1} else ∅) ∪ externalWork xs T h i

theorem card_windowGuard_le_add_one (xs : Fin k → ℕ → ℤ) (T h i : ℕ) :
    (windowGuard xs T h i).card ≤ k * (windowTimes T h i).card + 1 := by
  classical
  have hs : (if 0 < i * h ∧ i * h < T then ({i * h - 1} : Finset ℕ) else ∅).card ≤ 1 := by
    split_ifs <;> simp
  exact (card_union_le _ _).trans (by have := card_externalWork_le xs T h i; omega)

theorem card_windowGuard_le (xs : Fin k → ℕ → ℤ) (T h i : ℕ) (hh : 0 < h) :
    (windowGuard xs T h i).card ≤ (k + 1) * h := by
  have hc := card_windowGuard_le_add_one xs T h i
  have hw := Nat.mul_le_mul_left k (card_windowTimes_le T h i)
  rw [Nat.add_mul, Nat.one_mul]
  omega

/-- The guard for an arbitrary finite family of bad windows. -/
noncomputable def guards (xs : Fin k → ℕ → ℤ) (T h : ℕ) (bad : Finset ℕ) : Finset ℕ :=
  bad.biUnion (windowGuard xs T h)

theorem windowGuard_subset_guards (xs : Fin k → ℕ → ℤ) (T h : ℕ)
    {bad : Finset ℕ} {i : ℕ} (hi : i ∈ bad) :
    windowGuard xs T h i ⊆ guards xs T h bad := by
  intro u hu
  exact mem_biUnion.mpr ⟨i, hi, hu⟩

theorem card_guards_le (xs : Fin k → ℕ → ℤ) (T h : ℕ) (bad : Finset ℕ)
    (hh : 0 < h) : (guards xs T h bad).card ≤ bad.card * ((k + 1) * h) := by
  classical
  refine card_biUnion_le.trans ?_
  calc
    (∑ i ∈ bad, (windowGuard xs T h i).card) ≤ ∑ _i ∈ bad, (k + 1) * h :=
      sum_le_sum fun i _ => card_windowGuard_le xs T h i hh
    _ = bad.card * ((k + 1) * h) := by simp

theorem windowGuard_subset_range (xs : Fin k → ℕ → ℤ) (T h i : ℕ) :
    windowGuard xs T h i ⊆ range T := by
  classical
  intro u hu
  rcases mem_union.mp hu with hu | hu
  · split_ifs at hu with hi
    · have he : u = i * h - 1 := mem_singleton.mp hu
      exact mem_range.mpr (by omega)
    · simp at hu
  · obtain ⟨⟨t, ht, j, hj⟩, _⟩ := mem_externalWork.mp hu
    exact mem_range.mpr ((prevS_spec.mp hj).1.trans (mem_windowTimes.mp ht).2.1)

theorem guards_subset_range (xs : Fin k → ℕ → ℤ) (T h : ℕ) (bad : Finset ℕ) :
    guards xs T h bad ⊆ range T := by
  intro u hu
  obtain ⟨i, _, hi⟩ := mem_biUnion.mp hu
  exact windowGuard_subset_range xs T h i hi

/-- A dependency edge crossing the beginning of a window hits its guard. -/
theorem external_depStep_mem_guard {xs : Fin k → ℕ → ℤ} {T h i t u : ℕ}
    (ht : t ∈ windowTimes T h i) (hu : u < i * h) (he : DepStep xs T t u) :
    u ∈ windowGuard xs T h i := by
  classical
  obtain ⟨ht₀, htT, ht₁⟩ := mem_windowTimes.mp ht
  rcases (blockStep_iff xs T t u).mpr he with ⟨_, he | ⟨j, hj⟩⟩
  · have hpos : 0 < i * h ∧ i * h < T := by omega
    have heq : u = i * h - 1 := by omega
    exact mem_union_left _ (by simp [hpos, heq])
  · exact mem_union_right _ (mem_externalWork.mpr ⟨⟨t, ht, j, hj⟩, hu⟩)

/-- Only the target must avoid the guard. The source, in particular the
root of a free dependency path, may itself be revealed. -/
theorem depStep_stays_in_window {xs : Fin k → ℕ → ℤ} {T h i t u : ℕ}
    (ht : t ∈ windowTimes T h i) (he : DepStep xs T t u)
    (hfree : u ∉ windowGuard xs T h i) : u ∈ windowTimes T h i := by
  have ht' := mem_windowTimes.mp ht
  have hu := (depStep_lt he).1
  have hlow : i * h ≤ u := by
    by_contra hn
    exact hfree (external_depStep_mem_guard ht (by omega) he)
  exact mem_windowTimes.mpr ⟨hlow, by omega, by omega⟩

/-- Root-exempt free paths cannot leave a guarded window. -/
theorem free_path_stays_in_window (xs : Fin k → ℕ → ℤ) (T h i : ℕ)
    (π : List ℕ) (t : ℕ) (ht : t ∈ windowTimes T h i)
    (hp : IsDepPath xs T (t :: π)) (hf : LinNet.GFree (windowGuard xs T h i) (t :: π)) :
    ∀ u ∈ t :: π, u ∈ windowTimes T h i := by
  induction π generalizing t with
  | nil => simpa only [List.mem_singleton] using fun u (hu : u = t) => hu.symm ▸ ht
  | cons v π ih =>
    obtain ⟨hv, hf'⟩ := gfree_cons_cons.mp hf
    have hwin := depStep_stays_in_window ht hp.1 hv
    intro u hu
    rcases List.mem_cons.mp hu with rfl | hu
    · exact ht
    · exact ih v hwin hp.2 hf' u hu

theorem free_path_stays_in_bad_window (xs : Fin k → ℕ → ℤ) (T h : ℕ)
    {bad : Finset ℕ} {i : ℕ} (hi : i ∈ bad) (π : List ℕ) (t : ℕ)
    (ht : t ∈ windowTimes T h i) (hp : IsDepPath xs T (t :: π))
    (hf : LinNet.GFree (guards xs T h bad) (t :: π)) :
    ∀ u ∈ t :: π, u ∈ windowTimes T h i :=
  free_path_stays_in_window xs T h i π t ht hp
    (gfree_mono (windowGuard_subset_guards xs T h hi) hf)

/-- The last visit of a work edge crossing a window start is also the
last visit before that start. This is the bridge to encountered labels. -/
theorem external_prev_lastBefore {x : ℕ → ℤ} {start t u : ℕ}
    (hst : start ≤ t) (hu : u < start) (he : prevS x t = some u) :
    lastBefore x start (x t) = some u := by
  obtain ⟨_, hx, hgap⟩ := prevS_spec.mp he
  exact lastBefore_eq_some_iff.mpr ⟨hu, hx,
    fun v huv hvs => hgap v huv (lt_of_lt_of_le hvs hst)⟩

theorem external_prev_windowLabel {xs : Fin k → ℕ → ℤ} {T h i t u : ℕ}
    {j : Fin k} (ht : t ∈ windowTimes T h i) (hu : u < i * h)
    (he : prevS (xs j) t = some u) :
    windowLabel (xs j) h (min T (i * h)) (xs j t) = some (u / h) := by
  obtain ⟨hstart, htT, _⟩ := mem_windowTimes.mp ht
  have hcut : min T (i * h) = i * h := min_eq_right (by omega)
  rw [hcut, windowLabel, external_prev_lastBefore hstart hu he]
  rfl

/-- Every external work guard is witnessed by one of the literal old
labels encountered in the clipped window interval. -/
theorem externalWork_label_witness {xs : Fin k → ℕ → ℤ} {T h i u : ℕ}
    (hu : u ∈ externalWork xs T h i) :
    ∃ j : Fin k, ∃ z ∈ visitedCells (xs j) (min T (i * h)) (min T ((i + 1) * h)),
      windowLabel (xs j) h (min T (i * h)) z = some (u / h) := by
  obtain ⟨⟨t, ht, j, hj⟩, hustart⟩ := mem_externalWork.mp hu
  have ht' := mem_windowTimes.mp ht
  refine ⟨j, xs j t, mem_visitedCells.mpr ⟨t, ?_, ?_, rfl⟩,
    external_prev_windowLabel ht hustart hj⟩
  · exact le_trans (min_le_right _ _) ht'.1
  · exact lt_min ht'.2.1 ht'.2.2

#print axioms card_guards_le
#print axioms free_path_stays_in_bad_window
#print axioms external_prev_windowLabel
#print axioms externalWork_label_witness

section FiniteReach

variable {α : Type*} [DecidableEq α]

/-- Exact-length reachability for arbitrary finite neighbor sets. Unlike a
`LinNet`, this interface allows reflexive edges for depth padding. -/
def neighborReach (next : α → Finset α) : ℕ → α → Finset α
  | 0, t => {t}
  | D + 1, t => (next t).biUnion (neighborReach next D)

theorem card_neighborReach_le (next : α → Finset α) {B : ℕ}
    (hB : ∀ t, (next t).card ≤ B) :
    ∀ D t, (neighborReach next D t).card ≤ B ^ D
  | 0, t => by simp [neighborReach]
  | D + 1, t => by
    calc
      (neighborReach next (D + 1) t).card
          ≤ ∑ u ∈ next t, (neighborReach next D u).card := card_biUnion_le
      _ ≤ ∑ _u ∈ next t, B ^ D := sum_le_sum fun u _ => card_neighborReach_le next hB D u
      _ = (next t).card * B ^ D := by simp
      _ ≤ B * B ^ D := Nat.mul_le_mul_right _ (hB t)
      _ = B ^ (D + 1) := by rw [pow_succ, mul_comm]

/-- Reflexive neighbor sets absorb shorter paths into any fixed larger depth. -/
theorem neighborReach_mono (next : α → Finset α) (hself : ∀ t, t ∈ next t)
    {a b : ℕ} (hab : a ≤ b) (t : α) :
    neighborReach next a t ⊆ neighborReach next b t := by
  induction hab with
  | refl => exact Subset.rfl
  | @step b hab ih =>
    intro u hu
    exact mem_biUnion.mpr ⟨t, hself t, ih hu⟩

theorem mem_neighborReach_of_steps (next : α → Finset α) :
    ∀ D (v : ℕ → α), (∀ i < D, v (i + 1) ∈ next (v i)) →
      v D ∈ neighborReach next D (v 0)
  | 0, v, _ => mem_singleton_self _
  | D + 1, v, hv => by
    refine mem_biUnion.mpr ⟨v 1, hv 0 (by omega), ?_⟩
    simpa only [Nat.zero_add] using
      mem_neighborReach_of_steps next D (fun i => v (i + 1))
        (fun i hi => hv (i + 1) (by omega))

theorem mem_neighborReach_of_steps_le (next : α → Finset α) (hself : ∀ t, t ∈ next t)
    {a D : ℕ} (ha : a ≤ D) (v : ℕ → α) (hv : ∀ i < a, v (i + 1) ∈ next (v i)) :
    v a ∈ neighborReach next D (v 0) :=
  neighborReach_mono next hself ha _ (mem_neighborReach_of_steps next a v hv)

#print axioms card_neighborReach_le
#print axioms mem_neighborReach_of_steps_le

end FiniteReach

end LeanBacklog.WindowGuards
