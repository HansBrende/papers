import Transpose.Tape.CEMain
import Transpose.Tape.CEHint
import Transpose.Tape.BufTM

/-!
# Coarse traces: `O(1)` bits per slot

The block-level trace (`blockTrace`) records absolute block indices, absolute rows and the output
length at every slot, i.e. `O(log n)` bits per slot, and the popular trace class therefore has
co-entropy `O(n w)` (`traceConst`). Most of this is redundant.
* The head's block at the first step of a slot changes by at most one per slot (`slot_block_step`),
  and the blocks resident at a slot lie within one of it (`pairRes_subset`).
* The same holds for the input head and the rows it touches (`headRow_step`,
  `srcRows_pattern`), since a slot is at most a row long.

So the **coarse trace** (`coarseTrace`) records per slot only moves in `{-1, 0, 1}` and patterns
inside `{-1, 0, 1}`: at most `24^{k+1}` values. Two inputs with the same coarse trace and the same
halting time have the same block-level trace whenever the output schedule is fixed by the halting
time (`sameTrace_of_coarse`): this is the case `OutputAtEnd`, which `bufTM` achieves. The popular
class then has co-entropy `O(n)` (`exists_popular_traceClass_atEnd`, from the generic pigeonhole
`exists_traceClass_of_labels`).

**The one reduction** (`codes_coent_on`): a machine correct within `c L` steps on a set of
co-entropy `m₀` gives, through `bufTM`, a code at co-entropy `m₀ + K n` on a diagram that appends its
output in its last `L` steps. Everything else here is a corollary:
* `codes_coentLinear_at` (all inputs, at one size) and `codes_coentLinear_of_linearTimeTransposable`:
  (T) gives such codes at every large `n`; hence `codes_of_linearTimeTransposable` (co-entropy
  `O(n w)`, the form of `RobustNoCode_TM`);
* the refutations: `not_linearTimeTransposable_of_coentLinear_end_io` (output at the end, infinitely
  many `n`) and its corollaries `…_coentLinear_end`, `…_coentLinear_io`; `linearTime_fails_of_coentLinear`
  and `not_linearTimeTransposable_of_coentLinear` (every large `n`); the single levels
  `…_coent`, `…_coent_nw`;
* the non-uniform forms: `no_fast_transposer_of_coent` (any level), `no_fast_transposer_of_coentLinear`
  and `no_fast_transposer_of_robustNoCode`.
-/

namespace Transpose.Tape.Impl

open Transpose TSDiagram

variable {M : TM}

/-- The output schedule is fixed by the halting time: at time `t ≤ T` the output has
`L - (T - t)` bits, i.e. the output is appended in the last `L` steps. -/
def OutputAtEnd (M : TM) (w : List Bool) (T L : ℕ) : Prop :=
  ∀ t ≤ T, (run M w t).outRev.length = L - (T - t)

/-- The block of work head `t` at the first step of slot `y`. -/
def headBlock (M : TM) (w : List Bool) (r : ℕ) (t : Fin M.k) (y : ℕ) : ℤ :=
  curBlock r (fun τ => workTraj M w τ t) (y * r)

/-- The row `⌊p / (n b)⌋` of the input-head position `p` at the first step of slot `y` (it may lie
outside `[0, n)`). -/
def headRow (M : TM) (w : List Bool) (n b r : ℕ) (y : ℕ) : ℤ :=
  blockOf (n * b) (inTraj M w (y * r))

/-- **The coarse trace at slot `y`**: for each work tape, the move of its block to the next slot
and the resident blocks relative to its block; for the input head, the move of its row and the rows
touched relative to its row. -/
noncomputable def coarseTrace (M : TM) (n b r T : ℕ) (w : List Bool) (y : ℕ) :
    (Fin M.k → ℤ × Finset ℤ) × ℤ × Finset ℤ :=
  (fun t => (headBlock M w r t (y + 1) - headBlock M w r t y,
      (pairRes r (fun τ => workTraj M w τ t) T y).image (· - headBlock M w r t y)),
    headRow M w n b r (y + 1) - headRow M w n b r y,
    (srcRows M w n b (slotOf r T y)).image (fun i : ℕ => (i : ℤ) - headRow M w n b r y))

/-! ### Reconstruction -/

theorem headBlock_zero (w : List Bool) (r : ℕ) (t : Fin M.k) : headBlock M w r t 0 = 0 := by
  simp [headBlock, curBlock, workTraj, run, init, blockOf]

theorem headRow_zero (w : List Bool) (n b r : ℕ) : headRow M w n b r 0 = 0 := by
  simp [headRow, inTraj, run, init, blockOf]

/-- A set is determined by its translate. -/
theorem image_sub_inj {S S' : Finset ℤ} {c : ℤ}
    (h : S.image (· - c) = S'.image (· - c)) : S = S' := by
  have e : ∀ X : Finset ℤ, (X.image (· - c)).image (· + c) = X := by
    intro X
    rw [Finset.image_image]
    convert Finset.image_id (s := X)
    funext x; simp
  rw [← e S, ← e S', h]

/-- A set of naturals is determined by its translate into `ℤ`. -/
theorem image_natSub_inj {S S' : Finset ℕ} {c : ℤ}
    (h : S.image (fun i : ℕ => (i : ℤ) - c) = S'.image (fun i : ℕ => (i : ℤ) - c)) : S = S' := by
  ext i
  have key : ∀ X : Finset ℕ, i ∈ X ↔ (i : ℤ) - c ∈ X.image (fun i : ℕ => (i : ℤ) - c) := by
    intro X
    constructor
    · intro hi; exact Finset.mem_image_of_mem _ hi
    · intro hi
      obtain ⟨i', hi', he⟩ := Finset.mem_image.1 hi
      have : i' = i := by omega
      rwa [← this]
  rw [key S, key S', h]

/-- **Coarse traces determine block positions and rows.** -/
theorem heads_of_coarse {n b r T : ℕ} {w w' : List Bool} {N : ℕ}
    (h : ∀ y ≤ N, coarseTrace M n b r T w y = coarseTrace M n b r T w' y) :
    ∀ y ≤ N + 1, (∀ t, headBlock M w r t y = headBlock M w' r t y) ∧
      headRow M w n b r y = headRow M w' n b r y := by
  intro y
  induction y with
  | zero => intro _; exact ⟨fun t => by rw [headBlock_zero, headBlock_zero],
      by rw [headRow_zero, headRow_zero]⟩
  | succ y ih =>
    intro hy
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have hc := h y (by omega)
    simp only [coarseTrace, Prod.mk.injEq] at hc
    obtain ⟨hc1, hc2, -⟩ := hc
    refine ⟨fun t => ?_, ?_⟩
    · have := (Prod.mk.inj (congrFun hc1 t)).1
      rw [ih1 t] at this
      linarith
    · rw [ih2] at hc2
      linarith

/-- **The coarse trace and the halting time fix the block-level trace**, when the output schedule
is fixed by the halting time. -/
theorem sameTrace_of_coarse {n b r T L : ℕ} {w w' : List Bool} (hT : HaltsAt M w T)
    (hT' : HaltsAt M w' T) (hout : OutputAtEnd M w T L) (hout' : OutputAtEnd M w' T L)
    (h : ∀ y ≤ numSlots r T, coarseTrace M n b r T w y = coarseTrace M n b r T w' y) :
    SameTrace M n b r T w w' := by
  intro y hy
  obtain ⟨hb, hrow⟩ := heads_of_coarse h y (by omega)
  have hc := h y hy
  simp only [coarseTrace, Prod.mk.injEq] at hc
  obtain ⟨hc1, -, hc3⟩ := hc
  simp only [blockTrace, Prod.mk.injEq]
  refine ⟨funext fun t => ?_, ?_, ?_⟩
  · have := (Prod.mk.inj (congrFun hc1 t)).2
    rw [hb t] at this
    exact image_sub_inj this
  · rw [hrow] at hc3
    exact image_natSub_inj hc3
  · by_cases hyT : y * r ≤ T
    · rw [hout _ hyT, hout' _ hyT]
    · rw [run_of_le_of_none hT.2 (by omega), run_of_le_of_none hT'.2 (by omega),
        hout T le_rfl, hout' T le_rfl]

/-! ### The coarse trace takes few values -/

theorem headBlock_step (w : List Bool) {r : ℕ} (hr : 1 ≤ r) (t : Fin M.k) (y : ℕ) :
    headBlock M w r t (y + 1) - headBlock M w r t y ∈ Finset.Icc (-1 : ℤ) 1 := by
  have := slot_block_step (unitSteps_workTraj M w t) hr y
  rw [Finset.mem_Icc]
  exact abs_le.1 this

theorem pairRes_pattern (w : List Bool) {r : ℕ} (hr : 1 ≤ r) (T : ℕ) (t : Fin M.k) (y : ℕ) :
    (pairRes r (fun τ => workTraj M w τ t) T y).image (· - headBlock M w r t y) ⊆
      Finset.Icc (-1 : ℤ) 1 := by
  intro x hx
  obtain ⟨β, hβ, rfl⟩ := Finset.mem_image.1 hx
  have := pairRes_subset (unitSteps_workTraj M w t) hr T y hβ
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  rw [Finset.mem_Icc]
  simp only [headBlock]
  omega

theorem headRow_step (w : List Bool) {n b r : ℕ} (hr : 1 ≤ r) (hrnb : r ≤ n * b) (y : ℕ) :
    headRow M w n b r (y + 1) - headRow M w n b r y ∈ Finset.Icc (-1 : ℤ) 1 := by
  have hnb : 1 ≤ n * b := le_trans hr hrnb
  have hd := unitSteps_dist (unitSteps_inTraj M w) (show y * r ≤ (y + 1) * r by nlinarith)
  have e : (((y + 1) * r : ℕ) : ℤ) - ((y * r : ℕ) : ℤ) = r := by push_cast; ring
  rw [e] at hd
  have := blockOf_close hnb (le_trans hd (by exact_mod_cast hrnb))
  rw [Finset.mem_Icc]
  exact abs_le.1 this

theorem srcRows_pattern (w : List Bool) {n b r : ℕ} (hr : 1 ≤ r) (hrnb : r ≤ n * b) (T y : ℕ) :
    (srcRows M w n b (slotOf r T y)).image (fun i : ℕ => (i : ℤ) - headRow M w n b r y) ⊆
      Finset.Icc (-1 : ℤ) 1 := by
  have hnb : 1 ≤ n * b := le_trans hr hrnb
  intro x hx
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
  simp only [srcRows, Finset.mem_filter] at hi
  obtain ⟨-, τ, hτ, h1, h2⟩ := hi
  rw [mem_slotOf] at hτ
  have hrow : blockOf (n * b) (run M w τ).inPos = i := by
    rw [blockOf_eq_iff hnb]
    constructor
    · have e : ((i * n * b : ℕ) : ℤ) = (i : ℤ) * ((n * b : ℕ) : ℤ) := by push_cast; ring
      rw [e] at h1; exact h1
    · have e : (((i + 1) * n * b : ℕ) : ℤ) = ((i : ℤ) + 1) * ((n * b : ℕ) : ℤ) := by
        push_cast; ring
      rw [e] at h2; exact h2
  have hd := slot_dist (unitSteps_inTraj M w) (le_refl (y * r)) (by omega : y * r < y * r + r)
    hτ.1 hτ.2.1
  have hd' : |(run M w τ).inPos - inTraj M w (y * r)| ≤ ((n * b : ℕ) : ℤ) := by
    have : ((r : ℕ) : ℤ) ≤ ((n * b : ℕ) : ℤ) := by exact_mod_cast hrnb
    simp only [inTraj] at hd ⊢
    linarith
  have := blockOf_close hnb hd'
  rw [hrow] at this
  rw [Finset.mem_Icc]
  simp only [headRow]
  exact abs_le.1 this

/-! ### The popular coarse class -/

/-- **The popular class of a machine with its output at the end.** If every input of a nonempty
set `F₀` of matrix inputs halts within `T_max` steps and has its output appended in its last
`n² b` steps, some trace class `F ⊆ F₀` (halting time `T ≤ T_max`) has
`|F₀| ≤ (T_max + 1) · 24^{(k+1)(N+1)} · |F|` with `N = ⌈T_max / r⌉`: `O(1)` bits per slot. (The labels
of `exists_traceClass_of_labels`: the coarse trace on the slots `y ≤ N`.) -/
theorem exists_popular_traceClass_atEnd {n b r Tmax : ℕ} (hr : 1 ≤ r) (hrnb : r ≤ n * b)
    {F₀ : Set (List Bool)} (hF₀ : F₀ ⊆ matrixInputs n b) (hne : F₀.Nonempty)
    (hrun : ∀ w ∈ F₀, ∃ T ≤ Tmax, HaltsAt M w T ∧ OutputAtEnd M w T (n * n * b)) :
    ∃ T ≤ Tmax, ∃ (F : Set (List Bool)) (w₀ : List Bool), TraceClass M n b r T F w₀ ∧ F ⊆ F₀ ∧
      F₀.ncard ≤ (Tmax + 1) * 24 ^ ((M.k + 1) * (numSlots r Tmax + 1)) * F.ncard := by
  classical
  set N := numSlots r Tmax
  let cell : Finset (ℤ × Finset ℤ) := Finset.Icc (-1 : ℤ) 1 ×ˢ (Finset.Icc (-1 : ℤ) 1).powerset
  have hcell : cell.card = 24 := by
    simp only [cell, Finset.card_product, Finset.card_powerset, Int.card_Icc]; rfl
  have hend : ∀ w ∈ F₀, ∀ T, HaltsAt M w T → OutputAtEnd M w T (n * n * b) := fun w hw T hT => by
    obtain ⟨T', -, hh, ho⟩ := hrun w hw
    rwa [haltsAt_unique hh hT] at ho
  have hB : (Fintype.piFinset fun _ : Fin (N + 1) =>
      Fintype.piFinset (fun _ : Fin M.k => cell) ×ˢ cell).card = 24 ^ ((M.k + 1) * (N + 1)) := by
    rw [Fintype.card_piFinset_const, Finset.card_product, Fintype.card_piFinset_const, hcell,
      ← pow_succ, ← pow_mul]
  rw [← hB]
  exact exists_traceClass_of_labels (r := r) hF₀ hne
    (fun w hw => by obtain ⟨T, hT, hh, -⟩ := hrun w hw; exact ⟨T, hT, hh⟩)
    (fun T w (y : Fin (N + 1)) => coarseTrace M n b r T w y.1) _
    (fun w _ T _ _ => Fintype.mem_piFinset.2 fun y => Finset.mem_product.2
      ⟨Fintype.mem_piFinset.2 fun t => Finset.mem_product.2 ⟨headBlock_step _ hr t y.1,
        Finset.mem_powerset.2 (pairRes_pattern _ hr _ t y.1)⟩,
       Finset.mem_product.2 ⟨headRow_step _ hr hrnb y.1,
        Finset.mem_powerset.2 (srcRows_pattern _ hr hrnb _ y.1)⟩⟩)
    (fun w hw w' hw' T hT hh hh' hκ => sameTrace_of_coarse hh hh' (hend w hw T hh)
      (hend w' hw' T hh') fun y hy =>
        congrFun hκ ⟨y, Nat.lt_succ_of_le (le_trans hy (numSlots_mono r hT))⟩)

/-! ### The count is `2^{O(n)}` -/

/-- The constant of the coarse count (`coarseCount_le`): `k` work tapes, running time `≤ c L`,
`G` bits per cell. -/
def coarseConst (k c G : ℕ) : ℕ := c + 4 + 5 * (k + 1) * (c * G + 2)

/-- **The coarse count is `2^{O(n)}`**: for running time `T_max = c L` and slots of `r` steps with
`n b ≤ r G`, `(T_max + 1) · 24^{(k+1)(N+1)} ≤ 2^{coarseConst k c G · n}`. -/
theorem coarseCount_le {k c G n r : ℕ} (hn : 1 ≤ n) (hr : 1 ≤ r)
    (hrG : n * entryBits n ≤ r * G) :
    (c * (n * n * entryBits n) + 1) *
        24 ^ ((k + 1) * (numSlots r (c * (n * n * entryBits n)) + 1)) ≤
      2 ^ (coarseConst k c G * n) := by
  have hw : entryBits n ≤ n := entryBits_le_self hn
  -- the number of slots
  have hN : numSlots r (c * (n * n * entryBits n)) + 1 ≤ (c * G + 2) * n := by
    have hT : c * (n * n * entryBits n) ≤ c * n * G * r := by
      have : n * n * entryBits n = n * (n * entryBits n) := by ring
      rw [this]
      calc c * (n * (n * entryBits n)) ≤ c * (n * (r * G)) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hrG)
        _ = c * n * G * r := by ring
    have hlt : numSlots r (c * (n * n * entryBits n)) < c * n * G + 1 := by
      unfold numSlots
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      have e : (c * n * G + 1) * r = c * n * G * r + r := by ring
      rw [e]
      generalize c * (n * n * entryBits n) = A at hT ⊢
      generalize c * n * G * r = B at hT ⊢
      omega
    nlinarith
  -- the halting time
  have hT1 : c * (n * n * entryBits n) + 1 ≤ 2 ^ ((c + 4) * n) := by
    calc c * (n * n * entryBits n) + 1 ≤ (c + 1) * (n * n * entryBits n + 1) := by nlinarith
      _ ≤ 2 ^ c * 2 ^ (3 * entryBits n + 1) :=
          Nat.mul_le_mul (Nat.lt_two_pow_self) (inputLength_succ_le n)
      _ = 2 ^ (c + (3 * entryBits n + 1)) := by rw [← pow_add]
      _ ≤ 2 ^ ((c + 4) * n) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  -- the per-slot data
  have h24 : 24 ^ ((k + 1) * (numSlots r (c * (n * n * entryBits n)) + 1)) ≤
      2 ^ (5 * (k + 1) * (c * G + 2) * n) := by
    calc 24 ^ ((k + 1) * (numSlots r (c * (n * n * entryBits n)) + 1))
        ≤ 32 ^ ((k + 1) * (numSlots r (c * (n * n * entryBits n)) + 1)) :=
          Nat.pow_le_pow_left (by norm_num) _
      _ = 2 ^ (5 * ((k + 1) * (numSlots r (c * (n * n * entryBits n)) + 1))) := by
          rw [show (32 : ℕ) = 2 ^ 5 by norm_num, ← pow_mul]
      _ ≤ 2 ^ (5 * (k + 1) * (c * G + 2) * n) := by
          apply Nat.pow_le_pow_right (by norm_num)
          have := Nat.mul_le_mul_left (5 * (k + 1)) hN
          nlinarith
  calc _ ≤ 2 ^ ((c + 4) * n) * 2 ^ (5 * (k + 1) * (c * G + 2) * n) := Nat.mul_le_mul hT1 h24
    _ = 2 ^ (coarseConst k c G * n) := by
        rw [← pow_add]; unfold coarseConst; congr 1; ring

/-! ### The reduction: fast machines give codes at co-entropy `O(n)` with the output at the end -/

theorem clog_add_two_le {a : ℕ} (ha : 1 ≤ a) : Nat.clog 2 (a + 2) ≤ Nat.clog 2 a + 2 := by
  apply Nat.clog_le_of_le_pow
  have := Nat.le_pow_clog (b := 2) (by norm_num) a
  rw [pow_add]
  omega

/-- **A machine fast and correct on a set of co-entropy `≤ m₀` gives a code at co-entropy
`m₀ + K n`, with the output at the end** (`K = coarseConst (M.k + 1) (c + 4) G`, `G = cellBits (bufTM M)`).
Let `M` output the transposed encoding within `c L` steps on every input of a set `F₀` with
`2^L ≤ 2^{m₀} |F₀|`, and have at most `2^{C₁ n w}` states. For `n ≥ slotSize (M.k + 1) (c + 4)`, a valid
`(M.k + 1 + (C₁ + 3))`-tape diagram of length `≤ (c + 4) L` that appends its `L` output bits in its last
`L` steps carries a code at its profile capacities solving complete exchange on a set of co-entropy
`≤ m₀ + K n`. (The buffered machine `bufTM M` outputs at the end; its popular coarse class within `F₀`
is the code; `C₁ + 3` stationary tapes carry its state and head positions.) -/
theorem codes_coent_on {c C₁ n m₀ : ℕ} (hn : slotSize (M.k + 1) (c + 4) ≤ n)
    (hq : Nat.clog 2 (M.q + 1) ≤ C₁ * (n * entryBits n)) {F₀ : Set (List Bool)}
    (hco : 2 ^ (n * n * entryBits n) ≤ 2 ^ m₀ * F₀.ncard)
    (hfast : ∀ w ∈ F₀, ∃ T ≤ c * (n * n * entryBits n), HaltsAt M w T ∧
      ∃ A : Matrix, w = encode n (entryBits n) A ∧
        (run M w T).outRev.reverse = encode n (entryBits n) (transpose A)) :
    ∃ (D : TSDiagram (M.k + 1 + (C₁ + 3))) (F : Set (Fin (n * n * entryBits n) → Bool))
      (code : NetCode),
      D.Valid (n * n * entryBits n) ∧ D.T ≤ (c + 4) * (n * n * entryBits n) ∧
      2 ^ (n * n * entryBits n) ≤
        2 ^ (m₀ + coarseConst (M.k + 1) (c + 4) (cellBits (bufTM M)) * n) * F.ncard ∧
      D.Solves n (cellBits (bufTM M)) (D.profileCap n (cellBits (bufTM M))) F code ∧
      ∀ τ ≤ D.T, D.out τ = n * n * entryBits n - (D.T - τ) := by
  set M' := bufTM M with hM'
  have hn1 : 1 ≤ n := le_trans (le_max_left _ _) hn
  have hb1 : 1 ≤ entryBits n := by unfold entryBits; omega
  have hL1 : 1 ≤ n * n * entryBits n := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hnw : 1 ≤ n * entryBits n := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hr := one_le_slotLen M' hn1
  have hrG := slotLen_mul_ge M' n
  set Tmax := (c + 4) * (n * n * entryBits n) with hTmax
  have hpos := pos_bits_le hn (le_refl Tmax)
  -- the buffered machine on `F₀`
  have hfast' : ∀ w ∈ F₀, ∃ T ≤ Tmax, HaltsAt M' w T ∧
      OutputAtEnd M' w T (n * n * entryBits n) ∧
      ∃ A : Matrix, w = encode n (entryBits n) A ∧
        (run M' w T).outRev.reverse = encode n (entryBits n) (transpose A) := by
    intro w hw
    obtain ⟨T, hT, hh, A, rfl, hout⟩ := hfast w hw
    have hlen : (run M (encode n (entryBits n) A) T).outRev.length = n * n * entryBits n := by
      rw [← List.length_reverse, hout, length_encode]
    obtain ⟨hh', hout', hat⟩ := bufTM_run hh
    rw [hlen] at hh' hout' hat
    refine ⟨T + 2 * (n * n * entryBits n) + 2, ?_, hh', hat, A, rfl, by rw [hout', hout]⟩
    rw [hTmax]
    nlinarith
  -- the popular coarse class within `F₀`
  obtain ⟨T, hTle, F, w₀, hF, hFsub, hcount⟩ := exists_popular_traceClass_atEnd (M := M') hr
    (slotLen_le M' n) (fast_subset_matrixInputs hfast)
    (Set.nonempty_of_ncard_ne_zero (ncard_pos_of_coentropy hco).ne')
    (fun w hw => by obtain ⟨T, hT, hh, hat, -⟩ := hfast' w hw; exact ⟨T, hT, hh, hat⟩)
  have hcorr : ClassCorrect M' n (entryBits n) T F := by
    intro w hw
    obtain ⟨T', -, hh, -, hcw⟩ := hfast' w (hFsub hw)
    rw [haltsAt_unique (hF.2 w hw).2.1 hh]
    exact hcw
  -- the code, with `C₁ + 3` blocks of extra bits
  have hclog : Nat.clog 2 (2 * T + 1) ≤ Nat.clog 2 (2 * Tmax + 1) :=
    Nat.clog_mono_right 2 (by omega)
  have hqM' : Nat.clog 2 (M'.q + 1) ≤ C₁ * (n * entryBits n) + 2 := by
    have := clog_add_two_le (a := M.q + 1) (by omega)
    show Nat.clog 2 (M.q + 2 + 1) ≤ _
    rw [show M.q + 2 + 1 = M.q + 1 + 2 by ring]
    omega
  have hs : Nat.clog 2 (M'.q + 1) + (M'.k + 1) * Nat.clog 2 (2 * T + 1) ≤
      (C₁ + 3) * (slotLen M' n * cellBits M') := by
    have hk' : M'.k = M.k + 1 := rfl
    have h1 := Nat.mul_le_mul_left (M'.k + 1) hclog
    rw [hk'] at h1 ⊢
    have h2 : (C₁ + 3) * (n * entryBits n) ≤ (C₁ + 3) * (slotLen M' n * cellBits M') :=
      Nat.mul_le_mul_left _ hrG
    nlinarith
  obtain ⟨code, hDv, hsol⟩ := code_bits_of_class hn1 hs hF hcorr
  have hFm : F ⊆ matrixInputs n (entryBits n) := fun w hw => (hF.2 w hw).1
  refine ⟨addTapes (runDiagram M' w₀ T) (C₁ + 3), {v | List.ofFn v ∈ F}, code,
    valid_addTapes _ hDv _, by rw [T_addTapes]; exact hTle, ?_,
    solves_profileCap_addTapes hr le_rfl hsol, fun τ hτ => ?_⟩
  · rw [ncard_ofFn_preimage hFm]
    calc 2 ^ (n * n * entryBits n) ≤ 2 ^ m₀ * F₀.ncard := hco
      _ ≤ 2 ^ m₀ * ((Tmax + 1) * 24 ^ ((M'.k + 1) * (numSlots (slotLen M' n) Tmax + 1)) *
            F.ncard) := Nat.mul_le_mul_left _ hcount
      _ ≤ 2 ^ m₀ * (2 ^ (coarseConst M'.k (c + 4) (cellBits M') * n) * F.ncard) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (coarseCount_le hn1 hr hrG))
      _ = 2 ^ (m₀ + coarseConst (M.k + 1) (c + 4) (cellBits M') * n) * F.ncard := by
          rw [← Nat.mul_assoc, ← pow_add]
  · -- the representative's output schedule: at the end
    rw [T_addTapes] at hτ
    rw [out_addTapes, T_addTapes]
    obtain ⟨T', -, hh', hat', -⟩ := hfast' w₀ (hFsub hF.1)
    rw [← haltsAt_unique (hF.2 w₀ hF.1).2.1 hh'] at hat'
    exact hat' τ hτ

/-- The size from which a machine transposing within `c (L + 1)` steps gives codes at co-entropy
`O(n)` (`codes_coentLinear_at`). -/
def coarseSize (M : TM) (c : ℕ) : ℕ := max (slotSize (M.k + 1) (2 * c + 4)) (Nat.clog 2 (M.q + 1))

theorem one_le_of_coarseSize_le {c n : ℕ} (hn : coarseSize M c ≤ n) : 1 ≤ n :=
  le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hn)

/-- **A machine transposing at size `n` gives a code at co-entropy `O(n)`, with the output at the
end.** If `M` transposes every `n × n` matrix within `c (L + 1)` steps and `n ≥ coarseSize M c`, then
a valid `(M.k + 5)`-tape diagram of length `≤ (2c + 4) L` that appends its output in its last `L`
steps carries a code at its profile capacities (`G = cellBits (bufTM M)`) solving complete exchange on
a set of inputs of co-entropy `≤ coarseConst (M.k + 1) (2c + 4) G · n`. -/
theorem codes_coentLinear_at {c n : ℕ} (hn : coarseSize M c ≤ n)
    (hM : ∀ A : Matrix, ComputesWithin M (encode n (entryBits n) A)
      (encode n (entryBits n) (transpose A)) (c * (inputLength n + 1))) :
    ∃ (D : TSDiagram (M.k + 1 + (1 + 3))) (F : Set (Fin (n * n * entryBits n) → Bool))
      (code : NetCode),
      D.Valid (n * n * entryBits n) ∧ D.T ≤ (2 * c + 4) * (n * n * entryBits n) ∧
      2 ^ (n * n * entryBits n) ≤
        2 ^ (coarseConst (M.k + 1) (2 * c + 4) (cellBits (bufTM M)) * n) * F.ncard ∧
      D.Solves n (cellBits (bufTM M)) (D.profileCap n (cellBits (bufTM M))) F code ∧
      ∀ τ ≤ D.T, D.out τ = n * n * entryBits n - (D.T - τ) := by
  have hn1 := one_le_of_coarseSize_le hn
  have hb1 : 1 ≤ entryBits n := by unfold entryBits; omega
  have h := codes_coent_on (C₁ := 1) (m₀ := 0) (le_of_max_le_left hn)
    (by rw [Nat.one_mul]; exact le_trans (le_of_max_le_right hn) (Nat.le_mul_of_pos_right _ hb1))
    (by rw [ncard_matrixInputs]; simp) (fast_of_computesWithin hn1 hM)
  simpa only [Nat.zero_add] using h

/-! ### Linear-time transposers give codes at co-entropy `O(n)` -/

/-- **(T) gives codes on sets of co-entropy `O(n)`, with the output at the end**: constants
`k, G ≥ 1, c, C` such that for all large `n` some valid `k`-tape diagram of length `≤ c L`, appending its
output in its last `L` steps, carries a code at its profile capacities solving complete exchange on a
set of inputs of co-entropy `≤ C n` (not `C n w`). -/
theorem codes_coentLinear_of_linearTimeTransposable (h : LinearTimeTransposable) :
    ∃ (k G c C : ℕ), 1 ≤ G ∧ ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      ∃ (D : TSDiagram k) (F : Set (Fin (n * n * entryBits n) → Bool)) (code : NetCode),
        D.Valid (n * n * entryBits n) ∧ D.T ≤ c * (n * n * entryBits n) ∧
        2 ^ (n * n * entryBits n) ≤ 2 ^ (C * n) * F.ncard ∧
        D.Solves n G (D.profileCap n G) F code ∧
        ∀ τ ≤ D.T, D.out τ = n * n * entryBits n - (D.T - τ) := by
  obtain ⟨M, c, hM⟩ := h
  exact ⟨M.k + 1 + (1 + 3), cellBits (bufTM M), 2 * c + 4,
    coarseConst (M.k + 1) (2 * c + 4) (cellBits (bufTM M)), cellBits_pos _, coarseSize M c,
    fun n hn => codes_coentLinear_at hn (hM n (one_le_of_coarseSize_le hn))⟩

/-- **(T) gives codes** within the block profile on sets of co-entropy `O(n w)` (the form of
`RobustNoCode_TM`): a corollary of `codes_coentLinear_of_linearTimeTransposable`. -/
theorem codes_of_linearTimeTransposable (h : LinearTimeTransposable) :
    ∃ (k G c C : ℕ), 1 ≤ G ∧ ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      ∃ (D : TSDiagram k) (cap : ℕ × ℕ → ℕ) (F : Set (Fin (n * n * entryBits n) → Bool))
        (code : NetCode),
        D.Valid (n * n * entryBits n) ∧ D.T ≤ c * (n * n * entryBits n) ∧ D.CapProfile n G cap ∧
        2 ^ (n * n * entryBits n) ≤ 2 ^ (C * n * entryBits n) * F.ncard ∧
        D.Solves n G cap F code := by
  obtain ⟨k, G, c, C, hG, n₀, h⟩ := codes_coentLinear_of_linearTimeTransposable h
  refine ⟨k, G, c, C, hG, n₀, fun n hn => ?_⟩
  obtain ⟨D, F, code, hD, hT, hco, hs, -⟩ := h n hn
  have hb : 1 ≤ entryBits n := by unfold entryBits; omega
  exact ⟨D, _, F, code, hD, hT, capProfile_profileCap D n G, le_trans hco (Nat.mul_le_mul_right _
    (Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_right _ hb))), hs⟩

/-- **Every machine fails at every large size, under the target at co-entropy `O(n)`.** If for
every `C` no code exists at co-entropy `C n` (for all constants and all large `n`), then for every
machine `M` and constant `c`, for all large `n` some `n × n` matrix is not transposed within
`c (L + 1)` steps. -/
theorem linearTime_fails_of_coentLinear (h : ∀ C : ℕ, NoCode_TM_coent (fun n => C * n))
    (M : TM) (c : ℕ) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ¬ ∀ A : Matrix,
      ComputesWithin M (encode n (entryBits n) A) (encode n (entryBits n) (transpose A))
        (c * (inputLength n + 1)) := by
  obtain ⟨n₁, hn₁⟩ := h (coarseConst (M.k + 1) (2 * c + 4) (cellBits (bufTM M)))
    (M.k + 1 + (1 + 3)) (cellBits (bufTM M)) (2 * c + 4) (cellBits_pos _)
  refine ⟨max (coarseSize M c) n₁, fun n hn hall => ?_⟩
  obtain ⟨D, F, code, hDv, hDT, hco, hsol, -⟩ := codes_coentLinear_at (le_of_max_le_left hn) hall
  exact hn₁ n (le_of_max_le_right hn) D hDv hDT F hco code hsol

/-- **Robust no-code at co-entropy `O(n)` refutes (T).** If for every `C`, for all constants and all
large `n`, no causal code solves complete exchange at the profile capacities on a set of inputs of
co-entropy `≤ C n`, then no machine transposes in linear time. This strengthens
`not_linearTimeTransposable_of_robustNoCode`, whose hypothesis rules out co-entropy `C n w`. -/
theorem not_linearTimeTransposable_of_coentLinear
    (h : ∀ C : ℕ, NoCode_TM_coent (fun n => C * n)) : ¬ LinearTimeTransposable := by
  rintro ⟨M, c, hM⟩
  obtain ⟨n₀, hn₀⟩ := linearTime_fails_of_coentLinear h M c
  exact hn₀ (max n₀ 1) (le_max_left _ _) (hM (max n₀ 1) (le_max_right _ _))

/-- The all-large-`n` target with the output at the end gives its infinitely-often form. -/
theorem coent_end_io_of_coent_end {m : ℕ → ℕ} (h : NoCode_TM_coent_end m) :
    NoCode_TM_coent_end_io m := by
  intro k G c hG n₀
  obtain ⟨n₁, hn₁⟩ := h k G c hG
  exact ⟨max n₀ n₁, le_max_left _ _, hn₁ _ (le_max_right _ _)⟩

/-- The infinitely-often target on all diagrams gives its restriction to the output at the end. -/
theorem coent_end_io_of_coent_io {m : ℕ → ℕ} (h : NoCode_TM_coent_io m) :
    NoCode_TM_coent_end_io m := by
  intro k G c hG n₀
  obtain ⟨n, hn, hno⟩ := h k G c hG n₀
  exact ⟨n, hn, fun D hD hT _ => hno D hD hT⟩

/-- **Output at the end and infinitely many sizes, at co-entropy `O(n)`, refute (T).** If for every
`C` and all constants, arbitrarily large `n` exist at which no causal code solves complete exchange at
the profile capacities on a set of co-entropy `≤ C n`, on diagrams that append their output in their
last `L` steps, then ¬(T): (T) gives such codes at every large `n` (`codes_coentLinear_at`). The
hypothesis is implied by those of `not_linearTimeTransposable_of_coentLinear_end` and of
`not_linearTimeTransposable_of_coentLinear_io`. -/
theorem not_linearTimeTransposable_of_coentLinear_end_io
    (h : ∀ C : ℕ, NoCode_TM_coent_end_io (fun n => C * n)) : ¬ LinearTimeTransposable := by
  rintro ⟨M, c, hM⟩
  obtain ⟨n, hn, hno⟩ := h (coarseConst (M.k + 1) (2 * c + 4) (cellBits (bufTM M)))
    (M.k + 1 + (1 + 3)) (cellBits (bufTM M)) (2 * c + 4) (cellBits_pos _) (coarseSize M c)
  obtain ⟨D, F, code, hDv, hDT, hco, hsol, hend⟩ :=
    codes_coentLinear_at hn (hM n (one_le_of_coarseSize_le hn))
  exact hno D hDv hDT hend F hco code hsol

/-- **The target may assume the output comes at the end.** -/
theorem not_linearTimeTransposable_of_coentLinear_end
    (h : ∀ C : ℕ, NoCode_TM_coent_end (fun n => C * n)) : ¬ LinearTimeTransposable :=
  not_linearTimeTransposable_of_coentLinear_end_io fun C => coent_end_io_of_coent_end (h C)

/-- **Infinitely many sizes suffice at co-entropy `O(n)`.** -/
theorem not_linearTimeTransposable_of_coentLinear_io
    (h : ∀ (k G c C : ℕ), 1 ≤ G → ∀ n₀ : ℕ, ∃ n, n₀ ≤ n ∧
      ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
      ∀ (F : Set (Fin (n * n * entryBits n) → Bool)),
        2 ^ (n * n * entryBits n) ≤ 2 ^ (C * n) * F.ncard →
      ∀ code : NetCode, ¬ D.Solves n G (D.profileCap n G) F code) :
    ¬ LinearTimeTransposable :=
  not_linearTimeTransposable_of_coentLinear_end_io fun C =>
    coent_end_io_of_coent_io fun k G c hG n₀ => h k G c C hG n₀

/-! ### The co-entropy levels -/

/-- **The co-entropy-`C n` target sits between robust and plain.** `RobustNoCode_TM` (co-entropy
`C n w`) implies the target at co-entropy `C n` for every `C`. -/
theorem coentLinear_of_robustNoCode (h : RobustNoCode_TM) :
    ∀ C : ℕ, NoCode_TM_coent (fun n => C * n) := by
  intro C
  refine coent_mono ⟨1, fun n hn => ?_⟩ (robustNoCode_iff_coent.1 h C)
  have hb1 : 1 ≤ entryBits n := by unfold entryBits; omega
  exact Nat.le_mul_of_pos_right _ hb1

/-- **Any superlinear co-entropy level suffices.** If `f n` eventually exceeds `C n` for every `C`
(for instance `f n = n w`, or `n` times any function tending to infinity; an unbounded function
is not enough), the target at co-entropy `f` alone
implies the target at co-entropy `C n` for every `C`. -/
theorem coentLinear_of_coent {f : ℕ → ℕ} (hf : ∀ C : ℕ, ∃ N, ∀ n, N ≤ n → C * n ≤ f n)
    (h : NoCode_TM_coent f) : ∀ C : ℕ, NoCode_TM_coent (fun n => C * n) :=
  fun C => coent_mono (hf C) h

theorem le_entryBits_of_two_pow_le {C n : ℕ} (h : 2 ^ C ≤ n) : C ≤ entryBits n := by
  by_contra hlt
  push Not at hlt
  have h1 := le_two_pow_entryBits n
  have : 2 ^ entryBits n < 2 ^ C := Nat.pow_lt_pow_right (by norm_num) hlt
  omega

/-- **`n w` is superlinear**: it exceeds `C n` from `n ≥ 2^C` on, since then `w = ⌈log₂ n⌉ ≥ C`. -/
theorem superlinear_nw (C : ℕ) : ∃ N, ∀ n, N ≤ n → C * n ≤ n * entryBits n :=
  ⟨2 ^ C, fun n hn => by
    have h1 := Nat.mul_le_mul_right n (le_entryBits_of_two_pow_le hn)
    rwa [Nat.mul_comm (entryBits n) n] at h1⟩

/-- **The single level `n w` suffices**: the robust target with the one constant `C = 1` implies the
target at co-entropy `C n` for every `C` (`superlinear_nw`). -/
theorem coentLinear_of_coent_nw (h : NoCode_TM_coent (fun n => n * entryBits n)) :
    ∀ C : ℕ, NoCode_TM_coent (fun n => C * n) :=
  coentLinear_of_coent superlinear_nw h

/-- **No code at the single co-entropy level `n w` refutes (T).** `RobustNoCode_TM` asks this for
co-entropy `C n w` with every `C`; one level `C = 1` is enough. -/
theorem not_linearTimeTransposable_of_coent_nw
    (h : NoCode_TM_coent (fun n => n * entryBits n)) : ¬ LinearTimeTransposable :=
  not_linearTimeTransposable_of_coentLinear (coentLinear_of_coent_nw h)

/-- **No code at any superlinear co-entropy level refutes (T).** -/
theorem not_linearTimeTransposable_of_coent {f : ℕ → ℕ}
    (hf : ∀ C : ℕ, ∃ N, ∀ n, N ≤ n → C * n ≤ f n) (h : NoCode_TM_coent f) :
    ¬ LinearTimeTransposable :=
  not_linearTimeTransposable_of_coentLinear (coentLinear_of_coent hf h)

/-- The target at co-entropy `C n` (for any one `C`) implies the plain target. -/
theorem noCode_of_coentLinear {C : ℕ} (h : NoCode_TM_coent (fun n => C * n)) : NoCode_TM :=
  noCode_iff_coent_zero.2 (coent_mono ⟨0, fun _ _ => Nat.zero_le _⟩ h)

/-! ### Non-uniform machines on large sets of inputs -/

/-- **No fast transposer at any single co-entropy level** (non-uniform, average-case). Under
`NoCode_TM_coent m`, for all large `n`, no machine (`k` tapes, alphabet `g + 1`, at most `2^{C₁ n w}`
states) outputs the transposed encoding within `c L` steps on every input of a set of co-entropy `m₀`
with `m₀ + K n ≤ m n`, `K = coarseConst (k + 1) (c + 4) G`. -/
theorem no_fast_transposer_of_coent {m : ℕ → ℕ} (h : NoCode_TM_coent m) (k g c C₁ : ℕ) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ M : TM, M.k = k → M.g = g →
      Nat.clog 2 (M.q + 1) ≤ C₁ * (n * entryBits n) →
      ∀ (F₀ : Set (List Bool)) (m₀ : ℕ),
        m₀ + coarseConst (k + 1) (c + 4) (max 1 (Nat.clog 2 (g + 2 + 1))) * n ≤ m n →
        2 ^ (n * n * entryBits n) ≤ 2 ^ m₀ * F₀.ncard →
        ¬ ∀ w ∈ F₀, ∃ T ≤ c * (n * n * entryBits n), HaltsAt M w T ∧
          ∃ A : Matrix, w = encode n (entryBits n) A ∧
            (run M w T).outRev.reverse = encode n (entryBits n) (transpose A) := by
  set Gk := max 1 (Nat.clog 2 (g + 2 + 1)) with hGk
  obtain ⟨n₁, hn₁⟩ := h (k + 1 + (C₁ + 3)) Gk (c + 4) (le_max_left _ _)
  refine ⟨max n₁ (slotSize (k + 1) (c + 4)), fun n hn M hk hg hq F₀ m₀ hm hco hfast => ?_⟩
  subst hk
  have hG : cellBits (bufTM M) = Gk := by
    show max 1 (Nat.clog 2 (M.g + 2 + 1)) = Gk
    rw [hg]
  obtain ⟨D, F, code, hDv, hDT, hcoF, hsol, -⟩ :=
    codes_coent_on (le_trans (le_max_right _ _) hn) hq hco hfast
  rw [hG] at hcoF hsol
  exact hn₁ n (le_trans (le_max_left _ _) hn) D hDv hDT F
    (le_trans hcoF (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hm))) code hsol

/-- **No fast transposer, even non-uniform and on average, at co-entropy `O(n)`.** Under the target
at co-entropy `C n` for every `C`: for all `k`, `g`, `c`, `C₀`, `C₁` and all large `n`, no machine with
`k` work tapes, alphabet `g + 1` and at most `2^{C₁ n w}` states (any transition table, which may
depend on `n`) outputs the transposed encoding within `c L` steps on every input of a set of at least
`2^{L - C₀ n}` matrix inputs. (`no_fast_transposer_of_coent` at the level `(C₀ + K) n`.) -/
theorem no_fast_transposer_of_coentLinear (h : ∀ C : ℕ, NoCode_TM_coent (fun n => C * n))
    (k g c C₀ C₁ : ℕ) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ M : TM, M.k = k → M.g = g →
      Nat.clog 2 (M.q + 1) ≤ C₁ * (n * entryBits n) →
      ∀ F₀ : Set (List Bool),
        2 ^ (n * n * entryBits n) ≤ 2 ^ (C₀ * n) * F₀.ncard →
        ¬ ∀ w ∈ F₀, ∃ T ≤ c * (n * n * entryBits n), HaltsAt M w T ∧
          ∃ A : Matrix, w = encode n (entryBits n) A ∧
            (run M w T).outRev.reverse = encode n (entryBits n) (transpose A) := by
  obtain ⟨n₀, hn₀⟩ := no_fast_transposer_of_coent
    (h (C₀ + coarseConst (k + 1) (c + 4) (max 1 (Nat.clog 2 (g + 2 + 1))))) k g c C₁
  exact ⟨n₀, fun n hn M hk hg hq F₀ hco =>
    hn₀ n hn M hk hg hq F₀ (C₀ * n) (le_of_eq (Nat.add_mul _ _ _).symm) hco⟩

/-- **No fast transposer, even non-uniform and on average**, under `RobustNoCode_TM`: for all `k`,
`g`, `c`, `C₀`, `C₁` and all large `n`, no machine with `k` work tapes, alphabet `g + 1` and at most
`2^{C₁ n w}` states outputs the transposed encoding within `c L` steps on every input of a set of
`≥ 2^{L - C₀ n w}` matrix inputs. (`no_fast_transposer_of_coent` at the level `(C₀ + 1) n w`, which
exceeds `C₀ n w + K n` once `w ≥ K`.) -/
theorem no_fast_transposer_of_robustNoCode (h : RobustNoCode_TM) (k g c C₀ C₁ : ℕ) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ M : TM, M.k = k → M.g = g →
      Nat.clog 2 (M.q + 1) ≤ C₁ * (n * entryBits n) →
      ∀ F₀ : Set (List Bool),
        2 ^ (n * n * entryBits n) ≤ 2 ^ (C₀ * n * entryBits n) * F₀.ncard →
        ¬ ∀ w ∈ F₀, ∃ T ≤ c * (n * n * entryBits n), HaltsAt M w T ∧
          ∃ A : Matrix, w = encode n (entryBits n) A ∧
            (run M w T).outRev.reverse = encode n (entryBits n) (transpose A) := by
  obtain ⟨n₀, hn₀⟩ := no_fast_transposer_of_coent (robustNoCode_iff_coent.1 h (C₀ + 1)) k g c C₁
  obtain ⟨N, hN⟩ := superlinear_nw (coarseConst (k + 1) (c + 4) (max 1 (Nat.clog 2 (g + 2 + 1))))
  refine ⟨max n₀ N, fun n hn M hk hg hq F₀ hco => hn₀ n (le_of_max_le_left hn) M hk hg hq F₀
    (C₀ * n * entryBits n) ?_ hco⟩
  have := hN n (le_of_max_le_right hn)
  show C₀ * n * entryBits n + _ ≤ (C₀ + 1) * n * entryBits n
  nlinarith

end Transpose.Tape.Impl
