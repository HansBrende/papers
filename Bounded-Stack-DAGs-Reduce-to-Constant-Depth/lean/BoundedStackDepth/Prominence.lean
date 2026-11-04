import BoundedStackDepth.Basic
import BoundedNesting.OwnerLoad
import BoundedNesting.OneWalk

/-!
# Prominence of turning points

For a walk `x : ℕ → ℤ` on the times `[0, T)` and a time `t < T` with `v = x t`:
* `s_L` is the nearest earlier time with `x s_L ≥ v` (an earlier *equal* point counts as higher),
  and `L` is the minimum of `x` over `[s_L, t]` (`colL`);
* `s_R` is the nearest later time `s_R < T` with `x s_R > v` (a later point must be *strictly*
  higher), and `R` is the minimum of `x` over `[t, s_R]` (`colR`);
* the *peak prominence* is `v − max(L, R)`, an absent side being ignored, and `v − min_{[0,T)} x`
  if both sides are absent (`peak`). In the definition an absent side contributes the global
  minimum, which is at most the other side's col, so it is ignored;
* the *valley prominence* is the peak prominence of `−x` (`valley`), and the *prominence* is the
  larger of the two (`prom`).

All three are natural numbers; the peak prominence vanishes at a time with an earlier neighbour at
least as high (`peak_eq_zero_of_left`).

Main results:
* `sub_le_peak`, `sub_le_prom` (P1, the owner lemma): the owner `o` of an upper hop `(p, u)` with
  `u < T` has peak prominence at least `x o − x p`.
* `card_spanning_hops_lt` (P3): for any `x`, `c` and `R ≥ 1`, fewer than `2R` hops
  `(p, u)` with `p < c ≤ u` have extent `< R` (the extent is `max_{p < t < u} |x t − x p|`).
* `sum_peak_le`, `sum_valley_le` (P2, the prominence sum): for a walk, the peak prominences sum to
  at most `U + x 0 − min` and the valley prominences to at most `D + max − x 0`, where `U` and `D`
  count the up- and down-steps among the first `T − 1` steps; hence `sum_prom_le_two_mul`:
  `∑_{t < T} prom x T t ≤ 2 (T − 1)`. The proof is a double count over levels: at each level `y`
  the times `τ` with `x τ − peak τ ≤ y < x τ` lie in distinct maximal runs of `{x > y}`
  (`active_unique`), and these runs start at time `0` or at up-crossings of `y`.
-/

namespace BoundedStackDepth

open BoundedNesting Finset

/-! ### Definitions -/

/-- The minimum of `x` over the times `[a, b]` (the value `x a` if `b < a`). -/
def minOn (x : ℕ → ℤ) (a b : ℕ) : ℤ :=
  (range (b - a + 1)).inf' nonempty_range_add_one (fun i => x (a + i))

/-- The earlier times at which `x` is at least as high as at `t`. -/
def leftHigh (x : ℕ → ℤ) (t : ℕ) : Finset ℕ := (range t).filter (fun s => x t ≤ x s)

/-- The later times before `T` at which `x` is strictly higher than at `t`. -/
def rightHigh (x : ℕ → ℤ) (T t : ℕ) : Finset ℕ := (Ioo t T).filter (fun s => x t < x s)

/-- The minimum of `x` over `[0, T)`. -/
def gmin (x : ℕ → ℤ) (T : ℕ) : ℤ := minOn x 0 (T - 1)

/-- The maximum of `x` over `[0, T)`. -/
def gmax (x : ℕ → ℤ) (T : ℕ) : ℤ := -gmin (fun s => -x s) T

/-- The left col of `t`: the minimum of `x` over `[s_L, t]`, where `s_L` is the nearest earlier
time with `x s_L ≥ x t`; the global minimum if there is none. -/
def colL (x : ℕ → ℤ) (T t : ℕ) : ℤ :=
  if h : (leftHigh x t).Nonempty then minOn x ((leftHigh x t).max' h) t else gmin x T

/-- The right col of `t`: the minimum of `x` over `[t, s_R]`, where `s_R < T` is the nearest later
time with `x s_R > x t`; the global minimum if there is none. -/
def colR (x : ℕ → ℤ) (T t : ℕ) : ℤ :=
  if h : (rightHigh x T t).Nonempty then minOn x t ((rightHigh x T t).min' h) else gmin x T

/-- The peak prominence of `x` at `t`: `x t − max(L, R)`. -/
def peak (x : ℕ → ℤ) (T t : ℕ) : ℕ := (x t - max (colL x T t) (colR x T t)).toNat

/-- The valley prominence of `x` at `t`: the peak prominence of `−x`. -/
def valley (x : ℕ → ℤ) (T t : ℕ) : ℕ := peak (fun s => -x s) T t

/-- The prominence of `x` at `t`: the larger of the peak and valley prominences. -/
def prom (x : ℕ → ℤ) (T t : ℕ) : ℕ := max (peak x T t) (valley x T t)

/-- The extent of a hop `(p, u)`: the largest distance `|x t − x p|` over the times strictly
between. -/
def extent (x : ℕ → ℤ) (p u : ℕ) : ℕ := (Ioo p u).sup (fun t => (x t - x p).natAbs)

/-- The number of up-steps among the first `T − 1` steps. -/
def upSteps (x : ℕ → ℤ) (T : ℕ) : ℕ := ((range (T - 1)).filter (fun t => x t < x (t + 1))).card

/-- The number of down-steps among the first `T − 1` steps. -/
def downSteps (x : ℕ → ℤ) (T : ℕ) : ℕ := ((range (T - 1)).filter (fun t => x (t + 1) < x t)).card

/-! ### Examples (the reference convention)

The definitions agree with the reference implementation of the convention on every walk from `0`
with at most 8 steps in `{-1, 0, 1}`, every pause-free walk with at most 11 steps, and every
sequence of length at most 6 with values in `{0, 1, 2, 3}` (checked by evaluation during
development). The examples below are checked by the kernel. -/

/-- A finite walk as a function, `0` after its end. -/
private def ofList (l : List ℤ) : ℕ → ℤ := fun t => l.getD t 0

example : (List.range 5).map (peak (ofList [0, 1, 0, 1, 0]) 5) = [0, 1, 0, 1, 0] := by decide
example : (List.range 5).map (valley (ofList [0, 1, 0, 1, 0]) 5) = [1, 0, 1, 0, 1] := by decide
example : (List.range 5).map (prom (ofList [0, 1, 0, 1, 0]) 5) = [1, 1, 1, 1, 1] := by decide

example : (List.range 9).map (peak (ofList [0, 1, 2, 1, 2, 3, 2, 1, 0]) 9) =
    [0, 0, 1, 0, 0, 3, 0, 0, 0] := by decide
example : (List.range 9).map (valley (ofList [0, 1, 2, 1, 2, 3, 2, 1, 0]) 9) =
    [3, 0, 0, 1, 0, 0, 0, 0, 3] := by decide

-- ties: an earlier equal point counts as higher, a later equal point does not
example : (List.range 4).map (peak (ofList [0, 1, 1, 0]) 4) = [0, 1, 0, 0] := by decide
example : (List.range 3).map (peak (ofList [1, 0, 1]) 3) = [1, 0, 1] := by decide

/-! ### Minima over intervals -/

theorem minOn_le {x : ℕ → ℤ} {a b s : ℕ} (h1 : a ≤ s) (h2 : s ≤ b) : minOn x a b ≤ x s := by
  have hmem : s - a ∈ range (b - a + 1) := mem_range.mpr (by omega)
  have := inf'_le (fun i => x (a + i)) hmem
  rwa [show a + (s - a) = s by omega] at this

theorem exists_minOn (x : ℕ → ℤ) {a b : ℕ} (h : a ≤ b) :
    ∃ s, a ≤ s ∧ s ≤ b ∧ x s = minOn x a b := by
  obtain ⟨i, hi, he⟩ :=
    exists_mem_eq_inf' (nonempty_range_add_one (n := b - a)) (fun i => x (a + i))
  have hi := mem_range.mp hi
  exact ⟨a + i, by omega, by omega, he.symm⟩

theorem lt_minOn {x : ℕ → ℤ} {a b : ℕ} {y : ℤ} (hab : a ≤ b)
    (h : ∀ s, a ≤ s → s ≤ b → y < x s) : y < minOn x a b := by
  obtain ⟨s, h1, h2, he⟩ := exists_minOn x hab
  rw [← he]; exact h s h1 h2

theorem gmin_le {x : ℕ → ℤ} {T t : ℕ} (ht : t < T) : gmin x T ≤ x t :=
  minOn_le (Nat.zero_le _) (by omega)

theorem gmin_le_zero (x : ℕ → ℤ) (T : ℕ) : gmin x T ≤ x 0 :=
  minOn_le le_rfl (Nat.zero_le _)

theorem exists_gmin (x : ℕ → ℤ) {T : ℕ} (hT : 1 ≤ T) : ∃ t, t < T ∧ x t = gmin x T := by
  obtain ⟨s, -, h2, he⟩ := exists_minOn x (Nat.zero_le (T - 1))
  exact ⟨s, by omega, he⟩

theorem le_gmax {x : ℕ → ℤ} {T t : ℕ} (ht : t < T) : x t ≤ gmax x T := by
  have := gmin_le (x := fun s => -x s) ht
  unfold gmax; linarith

theorem zero_le_gmax (x : ℕ → ℤ) (T : ℕ) : x 0 ≤ gmax x T := by
  have := gmin_le_zero (fun s => -x s) T
  unfold gmax; linarith

theorem exists_gmax (x : ℕ → ℤ) {T : ℕ} (hT : 1 ≤ T) : ∃ t, t < T ∧ x t = gmax x T := by
  obtain ⟨t, ht, he⟩ := exists_gmin (fun s => -x s) hT
  exact ⟨t, ht, by unfold gmax; linarith⟩

/-! ### The cols -/

theorem mem_leftHigh {x : ℕ → ℤ} {t s : ℕ} : s ∈ leftHigh x t ↔ s < t ∧ x t ≤ x s := by
  simp [leftHigh]

theorem mem_rightHigh {x : ℕ → ℤ} {T t s : ℕ} :
    s ∈ rightHigh x T t ↔ (t < s ∧ s < T) ∧ x t < x s := by
  simp [rightHigh]

theorem colL_le_self {x : ℕ → ℤ} {T t : ℕ} (ht : t < T) : colL x T t ≤ x t := by
  unfold colL
  split_ifs with h
  · have := (mem_leftHigh.mp ((leftHigh x t).max'_mem h)).1
    exact minOn_le (by omega) le_rfl
  · exact gmin_le ht

theorem colR_le_self {x : ℕ → ℤ} {T t : ℕ} (ht : t < T) : colR x T t ≤ x t := by
  unfold colR
  split_ifs with h
  · have := (mem_rightHigh.mp ((rightHigh x T t).min'_mem h)).1
    exact minOn_le le_rfl (by omega)
  · exact gmin_le ht

theorem gmin_le_colL {x : ℕ → ℤ} {T t : ℕ} (ht : t < T) : gmin x T ≤ colL x T t := by
  unfold colL
  split_ifs with h
  · have := (mem_leftHigh.mp ((leftHigh x t).max'_mem h)).1
    obtain ⟨s, h1, h2, he⟩ := exists_minOn x (show (leftHigh x t).max' h ≤ t by omega)
    rw [← he]; exact gmin_le (by omega)
  · exact le_rfl

/-- If the walk is strictly below `x t` on `[p, t)`, the left col of `t` is at most `x p`. -/
theorem colL_le_of {x : ℕ → ℤ} {T t p : ℕ} (hpt : p ≤ t) (hpT : p < T)
    (h : ∀ s, p ≤ s → s < t → x s < x t) : colL x T t ≤ x p := by
  unfold colL
  split_ifs with hne
  · obtain ⟨h1, h2⟩ := mem_leftHigh.mp ((leftHigh x t).max'_mem hne)
    have : (leftHigh x t).max' hne < p := by
      by_contra hcon
      have := h _ (by omega) h1
      omega
    exact minOn_le (by omega) hpt
  · exact gmin_le hpT

/-- If the walk is at most `x t` on `(t, u]`, the right col of `t` is at most `x u`. -/
theorem colR_le_of {x : ℕ → ℤ} {T t u : ℕ} (htu : t ≤ u) (huT : u < T)
    (h : ∀ s, t < s → s ≤ u → x s ≤ x t) : colR x T t ≤ x u := by
  unfold colR
  split_ifs with hne
  · obtain ⟨⟨h1, h2⟩, h3⟩ := mem_rightHigh.mp ((rightHigh x T t).min'_mem hne)
    have : u < (rightHigh x T t).min' hne := by
      by_contra hcon
      have := h _ h1 (by omega)
      omega
    exact minOn_le htu (by omega)
  · exact gmin_le huT

/-- **Left blocking.** An earlier point `s` at least as high as `t`, with the walk above `y` on
`[s, t]`, puts the left col of `t` above `y`. -/
theorem lt_colL {x : ℕ → ℤ} {T s t : ℕ} {y : ℤ} (hst : s < t) (hx : x t ≤ x s)
    (h : ∀ r, s ≤ r → r ≤ t → y < x r) : y < colL x T t := by
  have hmem : s ∈ leftHigh x t := mem_leftHigh.mpr ⟨hst, hx⟩
  have hne : (leftHigh x t).Nonempty := ⟨s, hmem⟩
  simp only [colL, hne, ↓reduceDIte]
  have h1 := le_max' _ _ hmem
  have h2 := (mem_leftHigh.mp ((leftHigh x t).max'_mem hne)).1
  exact lt_minOn (by omega) (fun r hr1 hr2 => h r (by omega) hr2)

/-- **Right blocking.** A later point `s < T` strictly higher than `t`, with the walk above `y` on
`[t, s]`, puts the right col of `t` above `y`. -/
theorem lt_colR {x : ℕ → ℤ} {T s t : ℕ} {y : ℤ} (hts : t < s) (hsT : s < T) (hx : x t < x s)
    (h : ∀ r, t ≤ r → r ≤ s → y < x r) : y < colR x T t := by
  have hmem : s ∈ rightHigh x T t := mem_rightHigh.mpr ⟨⟨hts, hsT⟩, hx⟩
  have hne : (rightHigh x T t).Nonempty := ⟨s, hmem⟩
  simp only [colR, hne, ↓reduceDIte]
  have h1 := min'_le _ _ hmem
  have h2 := (mem_rightHigh.mp ((rightHigh x T t).min'_mem hne)).1
  exact lt_minOn (by omega) (fun r hr1 hr2 => h r hr1 (by omega))

/-! ### Peak prominence -/

theorem peak_eq {x : ℕ → ℤ} {T t : ℕ} (ht : t < T) :
    (peak x T t : ℤ) = x t - max (colL x T t) (colR x T t) := by
  have h := max_le (colL_le_self (x := x) ht) (colR_le_self ht)
  exact Int.toNat_of_nonneg (sub_nonneg.mpr h)

/-- The peak prominence vanishes at a time with an earlier neighbour at least as high. -/
theorem peak_eq_zero_of_left {x : ℕ → ℤ} {T t : ℕ} (ht : 1 ≤ t) (hx : x t ≤ x (t - 1)) :
    peak x T t = 0 := by
  have := lt_colL (T := T) (y := x t - 1) (show t - 1 < t by omega) hx (fun r h1 h2 => by
    rcases Nat.eq_or_lt_of_le h2 with h | h
    · rw [h]; omega
    · rw [show r = t - 1 by omega]; omega)
  unfold peak
  have := le_max_left (colL x T t) (colR x T t)
  omega

/-! ### (P1) The owner lemma -/

/-- **(P1) The owner lemma.** The owner `o` of an upper hop `(p, u)` with `u < T` has peak
prominence at least `x o − x p`: the walk is below `x o` on `[p, o)` and at most `x o` on
`(o, u]`, so both cols are at most `x p = x u`. -/
theorem sub_le_peak {x : ℕ → ℤ} {T p u o : ℕ} (hh : IsUpperHop x p u) (ho : IsOwner x p u o)
    (hT : u < T) : x o - x p ≤ peak x T o := by
  have hpo : x p < x o := hh.above o ho.gt ho.lt
  have hpT : p < T := by have := ho.lt; have := ho.gt; omega
  have hL : colL x T o ≤ x p := colL_le_of ho.gt.le hpT (fun s h1 h2 => by
    rcases Nat.eq_or_lt_of_le h1 with h | h
    · rw [← h]; exact hpo
    · exact ho.first s h h2)
  have hR : colR x T o ≤ x u := colR_le_of ho.lt.le hT (fun s h1 h2 => by
    rcases Nat.eq_or_lt_of_le h2 with h | h
    · rw [h, hh.eq]; exact hpo.le
    · exact ho.max s (by have := ho.gt; omega) h)
  rw [peak_eq (show o < T by have := ho.lt; omega)]
  rw [hh.eq] at hR
  have := max_le hL hR
  linarith

/-- **(P1) for the prominence**, upper hops. -/
theorem sub_le_prom {x : ℕ → ℤ} {T p u o : ℕ} (hh : IsUpperHop x p u) (ho : IsOwner x p u o)
    (hT : u < T) : x o - x p ≤ prom x T o := by
  have := sub_le_peak hh ho hT
  have : peak x T o ≤ prom x T o := le_max_left _ _
  omega

/-! ### (P3) Intrinsic F2 -/

/-- **(P3) Intrinsic F2.** For any `x`, any time `c` and `R ≥ 1`, fewer than `2R` hops `(p, u)`
with `p < c ≤ u` have extent `< R`: the cell of each lies within `R − 1` of `x c`, and at most one
hop of each cell spans `c` (`hop_unique`). -/
theorem card_spanning_hops_lt (x : ℕ → ℤ) (T c R : ℕ) (hR : 1 ≤ R) :
    ((hops x T).filter (fun e => e.1 < c ∧ c ≤ e.2 ∧ extent x e.1 e.2 < R)).card < 2 * R := by
  classical
  set H := (hops x T).filter (fun e => e.1 < c ∧ c ≤ e.2 ∧ extent x e.1 e.2 < R)
  have hmem : ∀ e ∈ H, IsHop x T e.1 e.2 ∧ e.1 < c ∧ c ≤ e.2 ∧ extent x e.1 e.2 < R := by
    intro e he
    obtain ⟨h1, h2⟩ := mem_filter.mp he
    exact ⟨mem_hops.mp h1, h2⟩
  have hmaps : Set.MapsTo (fun e : ℕ × ℕ => x e.1) H (Icc (x c - R + 1) (x c + R - 1)) := by
    intro e he
    obtain ⟨hh, h1, h2, h3⟩ := hmem e he
    have hd : (x c - x e.1).natAbs < R := by
      rcases Nat.eq_or_lt_of_le h2 with h | h
      · rw [h, hh.2.2.1]; simp; omega
      · have : (x c - x e.1).natAbs ≤ extent x e.1 e.2 :=
          le_sup (f := fun t => (x t - x e.1).natAbs) (mem_Ioo.mpr ⟨h1, h⟩)
        omega
    simp only [coe_Icc, Set.mem_Icc]
    omega
  have hinj : Set.InjOn (fun e : ℕ × ℕ => x e.1) H := by
    intro e he e' he' heq
    obtain ⟨hh, h1, h2, -⟩ := hmem e he
    obtain ⟨hh', h1', h2', -⟩ := hmem e' he'
    obtain ⟨hp, hu⟩ := hop_unique hh hh' heq ⟨h1, h2⟩ ⟨h1', h2'⟩
    exact Prod.ext hp hu
  have := card_le_card_of_injOn _ hmaps hinj
  rw [Int.card_Icc] at this
  omega

/-! ### (P2) The prominence sum -/

/-- The run starts at level `y`: the times before `T` at which a maximal run of times with the walk
above `y` begins (time `0`, or an up-crossing of `y`). -/
def runStarts (x : ℕ → ℤ) (T : ℕ) (y : ℤ) : Finset ℕ :=
  (range T).filter (fun s => y < x s ∧ (s = 0 ∨ x (s - 1) ≤ y))

/-- **One active time per run.** Two times `τ < τ'` before `T`, both with cols at most `y`, do not
lie in one run of times with the walk above `y`: the lower one (by height, then later time) has a
higher point on the other's side, which blocks its col above `y`. -/
theorem active_unique {x : ℕ → ℤ} {T τ τ' : ℕ} {y : ℤ} (hτ' : τ' < T) (hlt : τ < τ')
    (hact : max (colL x T τ) (colR x T τ) ≤ y) (hact' : max (colL x T τ') (colR x T τ') ≤ y)
    (hrun : ∀ r, τ ≤ r → r ≤ τ' → y < x r) : False := by
  rcases le_or_gt (x τ') (x τ) with h | h
  · have h1 := lt_colL (T := T) hlt h hrun
    have h2 := le_max_left (colL x T τ') (colR x T τ')
    linarith
  · have h1 := lt_colR hlt hτ' h hrun
    have h2 := le_max_right (colL x T τ) (colR x T τ)
    linarith

/-- At each level `y`, the active times (both cols at most `y`, walk above `y`) number at most
the starts of runs above `y`: the start of its run is injective on the active times. -/
theorem card_active_le (x : ℕ → ℤ) (T : ℕ) (y : ℤ) :
    ((range T).filter (fun τ => max (colL x T τ) (colR x T τ) ≤ y ∧ y < x τ)).card ≤
      (runStarts x T y).card := by
  classical
  have hex : ∀ τ : ℕ, ∃ s, ∀ r, s ≤ r → r ≤ τ → y < x r :=
    fun τ => ⟨τ + 1, fun r h1 h2 => by omega⟩
  let f : ℕ → ℕ := fun τ => Nat.find (hex τ)
  have hf1 : ∀ τ, y < x τ → f τ ≤ τ := fun τ h =>
    Nat.find_min' (hex τ) (fun r h1 h2 => by rw [show r = τ by omega]; exact h)
  have hf2 : ∀ τ r, f τ ≤ r → r ≤ τ → y < x r := fun τ => Nat.find_spec (hex τ)
  have hf3 : ∀ τ, f τ = 0 ∨ x (f τ - 1) ≤ y := by
    intro τ
    by_cases h0 : f τ = 0
    · exact Or.inl h0
    · right
      by_contra hcon
      have hmin := Nat.find_min (hex τ) (show f τ - 1 < f τ by omega)
      apply hmin
      intro r h1 h2
      rcases Nat.eq_or_lt_of_le h1 with h | h
      · rw [← h]; exact lt_of_not_ge hcon
      · exact hf2 τ r (by omega) h2
  have hmem : ∀ τ ∈ (range T).filter (fun τ => max (colL x T τ) (colR x T τ) ≤ y ∧ y < x τ),
      τ < T ∧ max (colL x T τ) (colR x T τ) ≤ y ∧ y < x τ := by
    intro τ hτ
    obtain ⟨h1, h2⟩ := mem_filter.mp hτ
    exact ⟨mem_range.mp h1, h2⟩
  refine card_le_card_of_injOn f (fun τ hτ => ?_) (fun τ hτ τ' hτ' he => ?_)
  · obtain ⟨h1, -, h3⟩ := hmem τ (mem_coe.mp hτ)
    have := hf1 τ h3
    exact mem_coe.mpr (mem_filter.mpr ⟨mem_range.mpr (by omega), hf2 τ (f τ) le_rfl this, hf3 τ⟩)
  · obtain ⟨h1, h2, h3⟩ := hmem τ (mem_coe.mp hτ)
    obtain ⟨h1', h2', h3'⟩ := hmem τ' (mem_coe.mp hτ')
    have he : f τ = f τ' := he
    have hfτ := hf1 τ h3
    have hfτ' := hf1 τ' h3'
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact active_unique h1' h h2 h2' (fun r hr1 hr2 => hf2 τ' r (by omega) hr2)
    · exact active_unique h1 h h2' h2 (fun r hr1 hr2 => hf2 τ r (by omega) hr2)

/-- **(P2) The prominence sum, peaks**, in `ℕ`: for a walk, the peak prominences before `T` sum
to at most `U + (x 0 − min)`. -/
theorem sum_peak_le_nat {x : ℕ → ℤ} (hx : IsWalk x) (T : ℕ) :
    ∑ t ∈ range T, peak x T t ≤ upSteps x T + (x 0 - gmin x T).toNat := by
  classical
  rcases Nat.eq_zero_or_pos T with rfl | hT
  · simp
  obtain ⟨n, rfl⟩ : ∃ n, T = n + 1 := ⟨T - 1, by omega⟩
  set Y := Ico (gmin x (n + 1)) (gmax x (n + 1)) with hY
  -- each peak prominence counts its active levels
  have h1 : ∀ τ ∈ range (n + 1), peak x (n + 1) τ =
      (Y.filter (fun y => max (colL x (n + 1) τ) (colR x (n + 1) τ) ≤ y ∧ y < x τ)).card := by
    intro τ hτ
    have hτ := mem_range.mp hτ
    have e : Y.filter (fun y => max (colL x (n + 1) τ) (colR x (n + 1) τ) ≤ y ∧ y < x τ) =
        Ico (max (colL x (n + 1) τ) (colR x (n + 1) τ)) (x τ) := by
      ext y
      have h1 := gmin_le_colL (x := x) hτ
      have h2 := le_max_left (colL x (n + 1) τ) (colR x (n + 1) τ)
      have h3 := le_gmax (x := x) hτ
      simp only [hY, mem_filter, mem_Ico]
      constructor
      · rintro ⟨-, h4, h5⟩; exact ⟨h4, h5⟩
      · rintro ⟨h4, h5⟩; exact ⟨⟨by linarith, by linarith⟩, h4, h5⟩
    rw [e, Int.card_Ico]
    rfl
  -- at each level the active times inject into the run starts
  have h2 : ∑ τ ∈ range (n + 1), peak x (n + 1) τ ≤ ∑ y ∈ Y, (runStarts x (n + 1) y).card := by
    rw [sum_congr rfl h1]
    simp_rw [card_filter]
    rw [sum_comm]
    refine sum_le_sum (fun y _ => ?_)
    rw [← card_filter]
    exact card_active_le x (n + 1) y
  -- each run start is counted at the levels it crosses
  have h3 : ∑ y ∈ Y, (runStarts x (n + 1) y).card =
      ∑ s ∈ range (n + 1), (Y.filter (fun y => y < x s ∧ (s = 0 ∨ x (s - 1) ≤ y))).card := by
    simp only [runStarts]
    simp_rw [card_filter]
    rw [sum_comm]
  have h4 : ∑ s ∈ range (n + 1), (Y.filter (fun y => y < x s ∧ (s = 0 ∨ x (s - 1) ≤ y))).card ≤
      upSteps x (n + 1) + (x 0 - gmin x (n + 1)).toNat := by
    rw [sum_range_succ']
    have g0 : (Y.filter (fun y => y < x 0 ∧ (0 = 0 ∨ x (0 - 1) ≤ y))).card ≤
        (x 0 - gmin x (n + 1)).toNat := by
      rw [← Int.card_Ico]
      apply card_le_card
      intro y hy
      simp only [hY, mem_filter, mem_Ico] at hy ⊢
      exact ⟨hy.1.1, hy.2.1⟩
    have gs : ∀ i ∈ range n,
        (Y.filter (fun y => y < x (i + 1) ∧ (i + 1 = 0 ∨ x (i + 1 - 1) ≤ y))).card ≤
          if x i < x (i + 1) then 1 else 0 := by
      intro i _
      have hsub : Y.filter (fun y => y < x (i + 1) ∧ (i + 1 = 0 ∨ x (i + 1 - 1) ≤ y)) ⊆
          Ico (x i) (x (i + 1)) := by
        intro y hy
        simp only [mem_filter, mem_Ico, Nat.add_sub_cancel] at hy ⊢
        obtain ⟨-, h5, h6⟩ := hy
        rcases h6 with h6 | h6
        · omega
        · exact ⟨h6, h5⟩
      have := card_le_card hsub
      rw [Int.card_Ico] at this
      have := hx.step i
      by_cases h : x i < x (i + 1)
      · simp only [h, ↓reduceIte]; omega
      · simp only [h, ↓reduceIte]; omega
    have hups : upSteps x (n + 1) = ∑ i ∈ range n, if x i < x (i + 1) then 1 else 0 := by
      rw [upSteps, card_filter, Nat.add_sub_cancel]
    rw [hups]
    have := sum_le_sum gs
    omega
  calc ∑ τ ∈ range (n + 1), peak x (n + 1) τ ≤ ∑ y ∈ Y, (runStarts x (n + 1) y).card := h2
    _ = _ := h3
    _ ≤ _ := h4

/-- **(P2) The prominence sum, peaks.** For a walk, `∑_{t < T} peak x T t ≤ U + x 0 − min`, where
`U` counts the up-steps among the first `T − 1` steps and `min` is over `[0, T)`. -/
theorem sum_peak_le {x : ℕ → ℤ} (hx : IsWalk x) (T : ℕ) :
    ∑ t ∈ range T, (peak x T t : ℤ) ≤ upSteps x T + x 0 - gmin x T := by
  have h := sum_peak_le_nat hx T
  have h0 := gmin_le_zero x T
  have h' : ((∑ t ∈ range T, peak x T t : ℕ) : ℤ) ≤
      ((upSteps x T + (x 0 - gmin x T).toNat : ℕ) : ℤ) := by exact_mod_cast h
  push_cast at h'
  rw [Int.toNat_of_nonneg (by linarith)] at h'
  linarith

/-- **(P2) The prominence sum, valleys**, in `ℕ`. -/
theorem sum_valley_le_nat {x : ℕ → ℤ} (hx : IsWalk x) (T : ℕ) :
    ∑ t ∈ range T, valley x T t ≤ downSteps x T + (gmax x T - x 0).toNat := by
  have h := sum_peak_le_nat hx.neg T
  have e1 : upSteps (fun s => -x s) T = downSteps x T := by
    unfold upSteps downSteps
    congr 1
    refine filter_congr (fun t _ => ?_)
    constructor <;> intro h <;> linarith
  have e2 : -x 0 - gmin (fun s => -x s) T = gmax x T - x 0 := by unfold gmax; ring
  rw [e1, e2] at h
  exact h

/-- **(P2) The prominence sum, valleys.** For a walk, `∑_{t < T} valley x T t ≤ D + max − x 0`,
where `D` counts the down-steps among the first `T − 1` steps and `max` is over `[0, T)`. -/
theorem sum_valley_le {x : ℕ → ℤ} (hx : IsWalk x) (T : ℕ) :
    ∑ t ∈ range T, (valley x T t : ℤ) ≤ downSteps x T + gmax x T - x 0 := by
  have h := sum_valley_le_nat hx T
  have h0 := zero_le_gmax x T
  have h' : ((∑ t ∈ range T, valley x T t : ℕ) : ℤ) ≤
      ((downSteps x T + (gmax x T - x 0).toNat : ℕ) : ℤ) := by exact_mod_cast h
  push_cast at h'
  rw [Int.toNat_of_nonneg (by linarith)] at h'
  linarith

/-- **(P2) The prominence sum.** For a walk, the prominences before `T` sum to at most the total
variation plus the range: `∑_{t < T} prom x T t ≤ (U + D) + (max − min)`. -/
theorem sum_prom_le {x : ℕ → ℤ} (hx : IsWalk x) (T : ℕ) :
    ∑ t ∈ range T, (prom x T t : ℤ) ≤
      ((upSteps x T + downSteps x T : ℕ) : ℤ) + (gmax x T - gmin x T) := by
  have h1 := sum_peak_le hx T
  have h2 := sum_valley_le hx T
  have h3 : ∑ t ∈ range T, (prom x T t : ℤ) ≤
      ∑ t ∈ range T, ((peak x T t : ℤ) + (valley x T t : ℤ)) := by
    refine sum_le_sum (fun t _ => ?_)
    have : prom x T t ≤ peak x T t + valley x T t :=
      max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
    exact_mod_cast this
  rw [sum_add_distrib] at h3
  push_cast
  linarith

/-- **(P2) The prominence sum is at most `2(T − 1)`.** -/
theorem sum_prom_le_two_mul {x : ℕ → ℤ} (hx : IsWalk x) (T : ℕ) :
    ∑ t ∈ range T, prom x T t ≤ 2 * (T - 1) := by
  classical
  rcases Nat.eq_zero_or_pos T with rfl | hT
  · simp
  have h := sum_prom_le hx T
  have hud : upSteps x T + downSteps x T ≤ T - 1 := by
    unfold upSteps downSteps
    have h1 := card_filter_add_card_filter_not (s := range (T - 1)) (fun t => x t < x (t + 1))
    have h2 : ((range (T - 1)).filter (fun t => x (t + 1) < x t)).card ≤
        ((range (T - 1)).filter (fun t => ¬ x t < x (t + 1))).card := by
      apply card_le_card
      intro t ht
      simp only [mem_filter] at ht ⊢
      exact ⟨ht.1, by linarith [ht.2]⟩
    rw [card_range] at h1
    omega
  have hrange : gmax x T - gmin x T ≤ ((T - 1 : ℕ) : ℤ) := by
    obtain ⟨a, ha, hea⟩ := exists_gmin x hT
    obtain ⟨b, hb, heb⟩ := exists_gmax x hT
    rw [← hea, ← heb]
    rcases le_total a b with hab | hab
    · have := (hx.lip hab).1
      omega
    · have := (hx.lip hab).2
      omega
  have e := Nat.cast_sum (R := ℤ) (range T) (fun t => prom x T t)
  rw [← e] at h
  omega

end BoundedStackDepth
