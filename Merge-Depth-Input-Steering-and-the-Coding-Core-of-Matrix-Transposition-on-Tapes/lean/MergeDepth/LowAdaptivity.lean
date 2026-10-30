import MergeDepth.Traces

set_option autoImplicit false

/-!
# Theorem LA: low adaptivity

A machine `M` *transposes at dimension `d` within `c (L + 1)` steps* (`TransposesAt`) when it
does so on the encoding of every `d × d` matrix with `b(d)`-bit entries, `L = d² b(d)`. This is the
frozen `TransposesWithin` at the one dimension `d` (`transposesAt_of_transposesWithin`).
`TransposesAtWidth` allows any entry width `b`; `TransposesInput` asks for one input only, and
`OutputsTranspose` asks only that the run on one input halt, at any time, with the transposed
output.

**The frozen-trace adapter.** `frozenGeometry` builds the ninth paper's admissible geometry
(`SourceCovers.AdmissibleGeometry`, Definition 2.2), with runtime constant `2c` and capacity `β`,
from the following data: a trace `τ₀` and a horizon `T ≤ ⌊c (L + 1)⌋` before which `τ₀` appends at
least `L = d² b` bits; a nonempty set `C` of inputs whose traces agree with `τ₀` before `T` and on
which `M` halts with the transposed output; and `capacityBits M ≤ β`.
* walks: the work walks `τ₀.work` up to `T`; the raw path is the input walk `τ₀.input` clamped to
  `[0, L - 1]` (`clampPos`);
* append times: `appendTime τ₀ T r`, the `r`-th step of `τ₀` that appends a bit;
* correctness set `C`, records the step values `v_t` (`stepValue`), output the appended bit;
* local determination by `actualParents` and the clamped direct read is
  `stepValue_eq_of_parents`; correctness (the transpose demand) is `prefix_output`;
* the core, the exceptional families and the outside bound `a₀` are labels supplied by the caller.

`fibreGeometry` is the paper's modelling step: for a transposer and a trace `τ₀` with a nonempty
fibre `W`, the frozen geometry up to the halting time with correctness set exactly `W`;
`fibreGeometry_deficit_le` is its deficit bound `Δ = L - log₂ |W| ≤ ηL` from `(6.1)`.

**Theorem LA.** `low_adaptivity_a` and `low_adaptivity_b` are parts (a) and (b) as stated in the
paper. They take constants `ε, d₀` of the ninth paper's Corollary 4.5 (`IsSkeletonConstant`,
provided by `SourceCovers.finite_skeleton_uniform_deficit`) or Corollary 4.3
(`IsOneExceptionConstant`, provided by `SourceCovers.one_exception_uniform_deficit`) for the
parameters `(2c, β, N, q)` or `(2c, β, N)`, and need `d ≥ 1` besides `d ≥ d₀`. The proofs follow
the paper: the fibre geometry has `Δ ≤ ηL`, the corollary gives `Δ ≥ εL`, and `η < ε`.
`low_adaptivity_a_exists` and `low_adaptivity_b_exists` package the constants, uniformly over all
machines of value width at most `β`.

**Stronger forms.**
* `card_correctSet_le_a`, `card_correctSet_le_b`: for every entry width `b ≥ 1` and every trace
  prefix `(τ₀, T)` with `T ≤ ⌊c (L + 1)⌋`, at least `L` appends before `T`, and the family
  structure of (a) or (b) before `T`: at most `2^{(1-ε)L}` inputs agree with `τ₀` before `T` and
  are transposed. The machine need not transpose any other input; its motion from time `T` on (for
  instance after its last append) and its halting time are unconstrained; and the capacity is the
  exact `log₂ (3 |Q| |Γ|^k)`.
* `card_correctSet_le_of_class`: the transfer of Remark `rem:LA-scope`(3). Any bound
  `|C| ≤ 2^{(1-ε)L}` valid on a class of admissible geometries holds for the transposed inputs
  along a trace prefix whose frozen geometry lies in the class.
* `traceProb_le_a`, `traceProb_le_b`: for a transposer, every trace with the family structure has
  probability at most `2^{-εL}`, which gives (a) and (b) for all `η < ε` at once.
* `card_traces_ge_a`: if all traces of a transposer have the structure of (a), there are at least
  `2^{εL}` distinct traces.
-/

namespace MergeDepth

open Finset Transpose Transpose.Tape Transpose.Tape.Impl SourceCovers BoundedNesting LeanMachine

/-! ### Transposition -/

/-- `M` transposes `d × d` matrices with `b`-bit entries within `c (L + 1)` steps, `L = d² b`: on
the encoding of every such matrix it halts within `⌊c (L + 1)⌋` steps with the encoding of the
transpose. -/
def TransposesAtWidth (M : TM) (d b : ℕ) (c : ℝ) : Prop :=
  ∀ A : Transpose.Matrix, ComputesWithin M (encode d b A) (encode d b (transpose A))
    ⌊c * (((d * d * b : ℕ) : ℝ) + 1)⌋₊

/-- `M` transposes at dimension `d` within `c (L + 1)` steps: entry width `b(d)`,
`L = d² b(d)`. -/
abbrev TransposesAt (M : TM) (d : ℕ) (c : ℝ) : Prop := TransposesAtWidth M d (entryBits d) c

/-- A machine satisfying the frozen `TransposesWithin M (fun L => c (L + 1))` transposes at every
dimension `d ≥ 1` within `c (L + 1)` steps. -/
theorem transposesAt_of_transposesWithin {M : TM} {c : ℕ}
    (h : TransposesWithin M fun L => c * (L + 1)) {d : ℕ} (hd : 1 ≤ d) :
    TransposesAt M d c := by
  intro A
  have e : ⌊(c : ℝ) * (((d * d * entryBits d : ℕ) : ℝ) + 1)⌋₊ = c * (inputLength d + 1) := by
    rw [show (c : ℝ) * (((d * d * entryBits d : ℕ) : ℝ) + 1) =
        ((c * (inputLength d + 1) : ℕ) : ℝ) by push_cast [inputLength]; ring]
    exact Nat.floor_natCast _
  rw [e]
  exact h d hd A

/-- `M` transposes the input `X ∈ {0,1}^{d²b}`, the row-major encoding of a `d × d` matrix with
`b`-bit entries, within `c (L + 1)` steps. -/
def TransposesInput (M : TM) (d b : ℕ) (c : ℝ) (X : Fin (d * d * b) → Bool) : Prop :=
  ∃ A : Transpose.Matrix, encode d b A = List.ofFn X ∧
    ComputesWithin M (List.ofFn X) (encode d b (transpose A)) ⌊c * (((d * d * b : ℕ) : ℝ) + 1)⌋₊

/-- `M` halts on the input `X ∈ {0,1}^{d²b}`, after some number of steps, with the encoding of the
transpose. -/
def OutputsTranspose (M : TM) (d b : ℕ) (X : Fin (d * d * b) → Bool) : Prop :=
  ∃ A : Transpose.Matrix, encode d b A = List.ofFn X ∧
    ∃ s, ComputesWithin M (List.ofFn X) (encode d b (transpose A)) s

theorem TransposesInput.outputsTranspose {M : TM} {d b : ℕ} {c : ℝ} {X : Fin (d * d * b) → Bool}
    (h : TransposesInput M d b c X) : OutputsTranspose M d b X :=
  let ⟨A, hA, hc⟩ := h
  ⟨A, hA, _, hc⟩

theorem TransposesAtWidth.transposesInput {M : TM} {d b : ℕ} {c : ℝ}
    (h : TransposesAtWidth M d b c) (X : Fin (d * d * b) → Bool) : TransposesInput M d b c X := by
  have hX : List.ofFn X ∈ matrixInputs d b := by
    rw [matrixInputs_eq]
    exact List.length_ofFn
  obtain ⟨A, hA⟩ := hX
  exact ⟨A, hA, hA ▸ h A⟩

/-- A transposed input: the run halts with `L` output bits, and output bit `tpos u` is `X u`. -/
theorem OutputsTranspose.output {M : TM} {d b : ℕ} {X : Fin (d * d * b) → Bool}
    (h : OutputsTranspose M d b X) :
    ∃ s, HaltsAt M (List.ofFn X) s ∧
      (run M (List.ofFn X) s).outRev.reverse.length = d * d * b ∧
      ∀ u : Fin (d * d * b),
        (run M (List.ofFn X) s).outRev.reverse[tpos d b u]? = some (X u) := by
  obtain ⟨A, hA, _, hc⟩ := h
  obtain ⟨s, -, hhalt, hout⟩ := (computesWithin_iff _ _).mp hc
  refine ⟨s, hhalt, by rw [hout, length_encode], fun u => ?_⟩
  rw [hout, ← nth_eq_getElem?, nth_encode_transpose_tpos A u.2, hA, nth_eq_getElem?,
    List.getElem?_ofFn, dite_eq_left u.2]

/-- An input transposed within `c (L + 1)` steps halts within `⌊c (L + 1)⌋` steps. -/
theorem TransposesInput.halts {M : TM} {d b : ℕ} {c : ℝ} {X : Fin (d * d * b) → Bool}
    (h : TransposesInput M d b c X) :
    ∃ s ≤ ⌊c * (((d * d * b : ℕ) : ℝ) + 1)⌋₊, HaltsAt M (List.ofFn X) s := by
  obtain ⟨A, -, hc⟩ := h
  obtain ⟨s, hs, hhalt, -⟩ := (computesWithin_iff _ _).mp hc
  exact ⟨s, hs, hhalt⟩

/-! ### Append times of a trace -/

/-- The `r`-th element of `l.filterMap g` is `g` at the `r`-th element of `l` on which `g` is
defined. -/
theorem getElem?_filterMap_eq_bind {α β : Type*} (g : α → Option β) (l : List α) (r : ℕ) :
    (l.filterMap g)[r]? = ((l.filter fun x => (g x).isSome)[r]?).bind g := by
  induction l generalizing r with
  | nil => simp
  | cons a l ih =>
    rcases hg : g a with _ | y
    · simp [hg, ih]
    · rcases r with _ | r
      · simp [hg]
      · simp [hg, ih]

section AppendTimes

variable {k : ℕ}

/-- The steps before `T` at which `τ` appends a bit, in increasing order. -/
def appendList (τ : Trace k) (T : ℕ) : List ℕ := (List.range T).filter τ.appends

/-- The `r`-th append time of `τ` before `T` (`0` if there is none). -/
def appendTime (τ : Trace k) (T r : ℕ) : ℕ := (appendList τ T).getD r 0

theorem appendTime_eq_getElem (τ : Trace k) (T : ℕ) {r : ℕ} (hr : r < (appendList τ T).length) :
    appendTime τ T r = (appendList τ T)[r] :=
  List.getD_eq_getElem _ _ hr

theorem appendTime_strictMonoOn (τ : Trace k) (T : ℕ) :
    StrictMonoOn (appendTime τ T) (Set.Iio (appendList τ T).length) := by
  intro r hr r' hr' hlt
  rw [appendTime_eq_getElem τ T hr, appendTime_eq_getElem τ T hr']
  exact List.pairwise_iff_getElem.mp (List.pairwise_lt_range.filter _) r r' hr hr' hlt

theorem appendTime_lt (τ : Trace k) (T : ℕ) {r : ℕ} (hr : r < (appendList τ T).length) :
    appendTime τ T r < T := by
  rw [appendTime_eq_getElem τ T hr]
  exact List.mem_range.mp (List.mem_filter.mp (List.getElem_mem hr)).1

theorem length_appendList_le (τ : Trace k) (T : ℕ) : (appendList τ T).length ≤ T :=
  (List.length_filter_le _ _).trans List.length_range.le

end AppendTimes

/-! ### Correct inputs along a trace prefix -/

theorem exists_outRev_append {M : TM} (w : List Bool) (T j : ℕ) :
    ∃ l, (run M w (T + j)).outRev.reverse = (run M w T).outRev.reverse ++ l := by
  induction j with
  | zero => exact ⟨[], by simp⟩
  | succ j ih =>
    obtain ⟨l, hl⟩ := ih
    refine ⟨l ++ (outBit M w (T + j)).toList, ?_⟩
    rw [← Nat.add_assoc, run_succ_outRev_reverse, hl, List.append_assoc]

section Prefix

variable {M : TM} {d b : ℕ} {c : ℝ} {τ₀ : Trace M.k} {T : ℕ}

/-- **Output along a trace prefix.** Let `τ₀` append at least `L = d² b` bits before `T`, and let
`M` halt on `X`, at any time, with the transposed output, by a run that agrees with `τ₀` before `T`.
Then `τ₀` appends exactly `L` bits before `T`, and the bit appended at the append time of output
position `tpos u` is `X u` (the transpose demand). -/
theorem prefix_output (happ : d * d * b ≤ (appendList τ₀ T).length) {X : Fin (d * d * b) → Bool}
    (hag : ∀ t < T, trace M (List.ofFn X) t = τ₀ t) (htr : OutputsTranspose M d b X) :
    (appendList τ₀ T).length = d * d * b ∧
      ∀ u : Fin (d * d * b),
        outBit M (List.ofFn X) (appendTime τ₀ T (tpos d b u)) = some (X u) := by
  obtain ⟨s, hhalt, hlen, hout⟩ := htr.output
  have hfilt : (List.range T).filter (fun t => (outBit M (List.ofFn X) t).isSome) =
      appendList τ₀ T := by
    unfold appendList
    exact List.filter_congr fun t ht => outBit_isSome_eq_of_agree hag (List.mem_range.mp ht)
  have hP : (run M (List.ofFn X) T).outRev.reverse.length = (appendList τ₀ T).length := by
    rw [outRev_reverse_eq, List.length_filterMap_eq_countP, List.countP_eq_length_filter, hfilt]
  -- the output at the halting time `s` is the output at time `T`
  have hl : (run M (List.ofFn X) s).outRev.reverse = (run M (List.ofFn X) T).outRev.reverse := by
    rcases le_total T s with hTs | hsT
    · obtain ⟨l, hl⟩ := exists_outRev_append (M := M) (List.ofFn X) T (s - T)
      rw [Nat.add_sub_cancel' hTs] at hl
      have hl0 : l = [] := by
        have := congrArg List.length hl
        rw [List.length_append, hlen, hP] at this
        exact List.eq_nil_of_length_eq_zero (by omega)
      rw [hl, hl0, List.append_nil]
    · rw [run_of_le_of_none hhalt.2 hsT]
  have hlenT : (appendList τ₀ T).length = d * d * b := by rw [← hP, ← hl, hlen]
  refine ⟨hlenT, fun u => ?_⟩
  have hr : tpos d b u < (appendList τ₀ T).length := by
    rw [hlenT]
    exact tpos_lt u.2
  have h := hout u
  rw [hl, outRev_reverse_eq, getElem?_filterMap_eq_bind, hfilt, List.getElem?_eq_getElem hr] at h
  rw [appendTime_eq_getElem τ₀ T hr]
  exact h

/-- The horizon of a prefix that appends `L ≥ 1` bits is positive. -/
theorem prefix_pos (hd : 0 < d) (hb : 0 < b) (happ : d * d * b ≤ (appendList τ₀ T).length) :
    0 < T := by
  have := length_appendList_le τ₀ T
  have := Nat.mul_pos (Nat.mul_pos hd hd) hb
  omega

/-- A horizon through which `τ₀` runs is at most the halting time of every input that agrees with
`τ₀` before it, hence at most `⌊c (L + 1)⌋` for an input transposed within `c (L + 1)` steps. -/
theorem horizon_le_of_run (hrun : ∀ t < T, τ₀ t ≠ none) {X : Fin (d * d * b) → Bool}
    (hag : ∀ t < T, trace M (List.ofFn X) t = τ₀ t) (htr : TransposesInput M d b c X) :
    T ≤ ⌊c * (((d * d * b : ℕ) : ℝ) + 1)⌋₊ := by
  obtain ⟨s, hs, hhalt⟩ := htr.halts
  refine le_trans ?_ hs
  by_contra hlt
  push Not at hlt
  have h2 : trace M (List.ofFn X) s = none := (trace_eq_none_iff s).mpr hhalt.2
  rw [hag s hlt] at h2
  exact hrun s hlt h2

end Prefix

/-- **The runtime bound.** `T ≤ c (L + 1) ≤ 2 c L` for `0 < T` and `0 < L`. -/
theorem runtime_le {c : ℝ} {L T : ℕ} (hL : 0 < L) (hTpos : 0 < T)
    (hT : T ≤ ⌊c * ((L : ℝ) + 1)⌋₊) : (T : ℝ) ≤ 2 * c * L := by
  have h1 : 1 ≤ c * ((L : ℝ) + 1) := Nat.floor_pos.mp (lt_of_lt_of_le hTpos hT)
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hc : 0 < c := by
    by_contra hc
    push Not at hc
    nlinarith
  have h2 : (T : ℝ) ≤ c * ((L : ℝ) + 1) :=
    (Nat.cast_le.mpr hT).trans (Nat.floor_le (by linarith))
  nlinarith

/-! ### The clamped input path -/

/-- An input-head position clamped to `[0, L - 1]`. -/
def clampPos (L : ℕ) (p : ℤ) : ℕ := min p.toNat (L - 1)

theorem clampPos_lt {L : ℕ} (hL : 0 < L) (p : ℤ) : clampPos L p < L := by
  unfold clampPos
  omega

theorem clampPos_natCast {L p : ℕ} (hp : p < L) : clampPos L (p : ℤ) = p := by
  unfold clampPos
  omega

/-- Clamping does not increase distances. -/
theorem dist_clampPos_le {L : ℕ} {p p' : ℤ} (h : |p' - p| ≤ 1) :
    dist (clampPos L p : ℝ) (clampPos L p' : ℝ) ≤ 1 := by
  obtain ⟨h1, h2⟩ := abs_le.mp h
  have e1 : clampPos L p ≤ clampPos L p' + 1 := by
    unfold clampPos
    omega
  have e2 : clampPos L p' ≤ clampPos L p + 1 := by
    unfold clampPos
    omega
  have r1 : (clampPos L p : ℝ) ≤ clampPos L p' + 1 := by exact_mod_cast e1
  have r2 : (clampPos L p' : ℝ) ≤ clampPos L p + 1 := by exact_mod_cast e2
  rw [Real.dist_eq, abs_le]
  constructor <;> linarith

/-! ### The adapter: a frozen trace is an admissible geometry -/

section Adapter

variable {M : TM} {d b : ℕ} {c : ℝ}

/-- **The frozen-trace geometry.** Let `τ₀` append at least `L = d² b` bits before a horizon
`T ≤ ⌊c (L + 1)⌋`, and let `C` be a nonempty set of inputs whose traces agree with `τ₀` before `T`
and on which `M` halts with the transposed output. The walks and append times of `τ₀` before `T`,
the correctness set `C`, the step values as records and the appended bit as output form an
admissible geometry of the ninth paper, with entry width `b`, runtime constant `2c`, capacity
`β ≥ capacityBits M`, the given `N`-class span partition, and the given labels: a Q2 core `K`, at
most `q` exceptional families `E`, and the bound `a₀` on every other family. -/
noncomputable def frozenGeometry (β : ℝ) (N q : ℕ) (hd : 0 < d) (hb : 0 < b) (τ₀ : Trace M.k)
    (T : ℕ) (hT : T ≤ ⌊c * (((d * d * b : ℕ) : ℝ) + 1)⌋₊)
    (happ : d * d * b ≤ (appendList τ₀ T).length)
    (C : Finset (Fin (d * d * b) → Bool)) (hne : C.Nonempty)
    (hC : ∀ X ∈ C, (∀ t < T, trace M (List.ofFn X) t = τ₀ t) ∧ OutputsTranspose M d b X)
    (hβ : capacityBits M ≤ β)
    (hN : HasSpanColoring (univ : Finset (ActualFamily τ₀.work T)) N)
    (K E : Finset (ActualFamily τ₀.work T)) (hK : HasSpanColoring K 2) (hE : E.card ≤ q)
    (hKE : Disjoint K E) (a₀ : ℕ)
    (ha₀ : ∀ F : ActualFamily τ₀.work T, F ∉ K ∪ E → F.hops.card ≤ a₀) :
    AdmissibleGeometry (2 * c) β N q where
  d := d
  b := b
  hd := hd
  hb := hb
  T := T
  k := M.k
  xs := τ₀.work
  work_walk := τ₀.work_isWalk
  x s := clampPos (d * d * b) (τ₀.input s)
  raw_range s _ := clampPos_lt (Nat.mul_pos (Nat.mul_pos hd hd) hb) _
  raw_step e _ := dist_clampPos_le (τ₀.abs_input_succ_sub_le e)
  t := appendTime τ₀ T
  append_strict := by
    obtain ⟨X, hX⟩ := hne
    have := appendTime_strictMonoOn τ₀ T
    rwa [(prefix_output happ (hC X hX).1 (hC X hX).2).1] at this
  append_lt z hz := by
    obtain ⟨X, hX⟩ := hne
    exact appendTime_lt τ₀ T
      (by rw [(prefix_output happ (hC X hX).1 (hC X hX).2).1]; exact hz)
  C := C
  correct_nonempty := hne
  Record := Value M
  recordFintype := inferInstance
  record z t := stepValue M (List.ofFn z) t
  output _ v := v.2.2.getD false
  capacity := hβ
  locally_determined := by
    intro x hx y hy t ht hraw hpar
    have hTpos := prefix_pos hd hb happ
    refine stepValue_eq_of_parents (hC x (mem_coe.mp hx)).1 (hC y (mem_coe.mp hy)).1
      (by omega) ?_ hpar
    intro p hp hpL
    have h := hraw (Set.mem_singleton _)
    simp only [← hp, clampPos_natCast hpL, Transpose.Tape.Impl.zbit] at h
    rwa [dite_eq_left hpL, dite_eq_left hpL] at h
  correct z hz u := congrArg (fun o : Option Bool => o.getD false)
    ((prefix_output happ (hC z hz).1 (hC z hz).2).2 u)
  core := K
  core_coloring := hK
  full_coloring := hN
  exceptions := E
  exceptions_card := hE
  exceptions_disjoint := hKE
  a0 := a₀
  outside_small := ha₀
  runtime := by
    have h := runtime_le (Nat.mul_pos (Nat.mul_pos hd hd) hb) (prefix_pos hd hb happ) hT
    push_cast at h
    exact h

end Adapter

/-! ### The uniform constants of the ninth paper's Corollaries 4.3 and 4.5 -/

/-- `ε, d₀` are constants of the ninth paper's Corollary 4.5 (a fixed finite skeleton) for the
parameters `(c, β, N, q)`: the conclusion of `SourceCovers.finite_skeleton_uniform_deficit`. -/
def IsSkeletonConstant (c β : ℝ) (N q : ℕ) (ε : ℝ) (d₀ : ℕ) : Prop :=
  ∀ {q₀ : ℕ} (G : AdmissibleGeometry c β N q₀) (E : Finset (ActualFamily G.xs G.T)),
    E.card ≤ q → ∀ a : ℕ, (∀ F : ActualFamily G.xs G.T, F ∉ E → F.hops.card ≤ a) →
      d₀ ≤ G.d → (a : ℝ) ≤ ε * G.inputLength →
        ε * G.inputLength ≤ G.deficit ∧ (G.C.card : ℝ) ≤ (2 : ℝ) ^ ((1 - ε) * G.inputLength)

/-- Corollary 4.5 of the ninth paper provides such constants. -/
theorem exists_skeletonConstant (c β : ℝ) (N q : ℕ) :
    ∃ ε > (0 : ℝ), ∃ d₀ : ℕ, IsSkeletonConstant c β N q ε d₀ :=
  finite_skeleton_uniform_deficit c β N q

/-- `ε, d₀` are constants of the ninth paper's Corollary 4.3 (one arbitrary exceptional family)
for the parameters `(c, β, N)`: the conclusion of `SourceCovers.one_exception_uniform_deficit`. -/
def IsOneExceptionConstant (c β : ℝ) (N : ℕ) (ε : ℝ) (d₀ : ℕ) : Prop :=
  ∀ G : AdmissibleGeometry c β N 1, d₀ ≤ G.d → (G.a0 : ℝ) ≤ ε * G.inputLength →
    ε * G.inputLength ≤ G.deficit ∧ (G.C.card : ℝ) ≤ (2 : ℝ) ^ ((1 - ε) * G.inputLength)

/-- Corollary 4.3 of the ninth paper provides such constants. -/
theorem exists_oneExceptionConstant (c β : ℝ) (N : ℕ) :
    ∃ ε > (0 : ℝ), ∃ d₀ : ℕ, IsOneExceptionConstant c β N ε d₀ :=
  one_exception_uniform_deficit c β N

/-! ### Theorem LA, strong form: correct inputs along a trace prefix -/

open Classical in
/-- The inputs `X ∈ {0,1}^{d²b}` whose trace agrees with `τ₀` before `T` and on which `M` halts
with the transposed output. -/
noncomputable def correctSet (M : TM) (d b : ℕ) (τ₀ : Trace M.k) (T : ℕ) :
    Finset (Fin (d * d * b) → Bool) :=
  univ.filter fun X => (∀ t < T, trace M (List.ofFn X) t = τ₀ t) ∧ OutputsTranspose M d b X

theorem mem_correctSet {M : TM} {d b : ℕ} {τ₀ : Trace M.k} {T : ℕ}
    {X : Fin (d * d * b) → Bool} :
    X ∈ correctSet M d b τ₀ T ↔
      (∀ t < T, trace M (List.ofFn X) t = τ₀ t) ∧ OutputsTranspose M d b X := by
  classical
  simp [correctSet]

theorem card_le_two_pow {L : ℕ} (s : Finset (Fin L → Bool)) : s.card ≤ 2 ^ L := by
  simpa using card_le_univ s

/-- For `ε ≤ 0` the bound `2^{(1-ε)L}` holds for every set of inputs. -/
theorem card_le_of_nonpos {L : ℕ} (s : Finset (Fin L → Bool)) {ε : ℝ} (hε : ε ≤ 0) :
    (s.card : ℝ) ≤ (2 : ℝ) ^ ((1 - ε) * (L : ℝ)) := by
  calc (s.card : ℝ) ≤ (2 : ℝ) ^ L := by exact_mod_cast card_le_two_pow s
    _ = (2 : ℝ) ^ ((1 : ℝ) * (L : ℝ)) := by rw [one_mul, Real.rpow_natCast]
    _ ≤ (2 : ℝ) ^ ((1 - ε) * (L : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num)
          (mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _))

/-- **Theorem LA(a), strong form.** Let `ε, d₀` be constants of Corollary 4.5 for the parameters
`(2c, β, N, q)` and `capacityBits M ≤ β`. Let `b ≥ 1`, `d ≥ max(d₀, 1)`, `L = d² b`, and let `τ₀` be
a trace with a horizon `T ≤ ⌊c (L + 1)⌋` before which it appends at least `L` bits, whose complete
families before `T` admit an `N`-class span partition and at most `q` of which have more than
`εL` hops. Then at most `2^{(1-ε)L}` inputs agree with `τ₀` before `T` and are transposed by `M`
(at any halting time). -/
theorem card_correctSet_le_a {c β ε : ℝ} {N q d₀ : ℕ}
    (hcor : IsSkeletonConstant (2 * c) β N q ε d₀) {M : TM} (hβ : capacityBits M ≤ β)
    {d b : ℕ} (hd : 0 < d) (hb : 0 < b) (hd₀ : d₀ ≤ d) {τ₀ : Trace M.k} {T : ℕ}
    (hT : T ≤ ⌊c * (((d * d * b : ℕ) : ℝ) + 1)⌋₊) (happ : d * d * b ≤ (appendList τ₀ T).length)
    (hN : HasSpanColoring (univ : Finset (ActualFamily τ₀.work T)) N)
    (hq : (univ.filter fun F : ActualFamily τ₀.work T =>
      ε * ((d * d * b : ℕ) : ℝ) < (F.hops.card : ℝ)).card ≤ q) :
    ((correctSet M d b τ₀ T).card : ℝ) ≤ (2 : ℝ) ^ ((1 - ε) * ((d * d * b : ℕ) : ℝ)) := by
  rcases (correctSet M d b τ₀ T).eq_empty_or_nonempty with h0 | hne
  · rw [h0, card_empty, Nat.cast_zero]
    positivity
  rcases le_or_gt ε 0 with hε | hε
  · exact card_le_of_nonpos _ hε
  have hεL : 0 ≤ ε * ((d * d * b : ℕ) : ℝ) := by positivity
  have h2 : HasSpanColoring (∅ : Finset (ActualFamily τ₀.work T)) 2 :=
    ⟨fun _ => 0, by simp, by simp⟩
  let G := frozenGeometry β N 0 hd hb τ₀ T hT happ _ hne (fun X hX => mem_correctSet.mp hX) hβ
    hN ∅ ∅ h2 (by simp) (disjoint_empty_left _)
    (univ.sup fun F : ActualFamily τ₀.work T => F.hops.card)
    (fun F _ => le_sup (f := fun F : ActualFamily τ₀.work T => F.hops.card) (mem_univ F))
  have hsize : ∀ F : ActualFamily τ₀.work T,
      F ∉ univ.filter (fun F : ActualFamily τ₀.work T =>
        ε * ((d * d * b : ℕ) : ℝ) < (F.hops.card : ℝ)) →
        F.hops.card ≤ ⌊ε * ((d * d * b : ℕ) : ℝ)⌋₊ := by
    intro F hF
    apply Nat.le_floor
    simpa using hF
  exact (hcor G _ hq _ hsize hd₀ (Nat.floor_le hεL)).2

/-- **Theorem LA(b), strong form.** Let `ε, d₀` be constants of Corollary 4.3 for the parameters
`(2c, β, N)` and `capacityBits M ≤ β`. Let `b ≥ 1`, `d ≥ max(d₀, 1)`, `L = d² b`, and let `τ₀` be a
trace with a horizon `T ≤ ⌊c (L + 1)⌋` before which it appends at least `L` bits, whose complete
families before `T` admit an `N`-class span partition and split into a Q2 core `K`, at most one
further family, and families of at most `εL` hops each. Then at most `2^{(1-ε)L}` inputs agree
with `τ₀` before `T` and are transposed by `M` (at any halting time). -/
theorem card_correctSet_le_b {c β ε : ℝ} {N d₀ : ℕ}
    (hcor : IsOneExceptionConstant (2 * c) β N ε d₀) {M : TM} (hβ : capacityBits M ≤ β)
    {d b : ℕ} (hd : 0 < d) (hb : 0 < b) (hd₀ : d₀ ≤ d) {τ₀ : Trace M.k} {T : ℕ}
    (hT : T ≤ ⌊c * (((d * d * b : ℕ) : ℝ) + 1)⌋₊) (happ : d * d * b ≤ (appendList τ₀ T).length)
    (hN : HasSpanColoring (univ : Finset (ActualFamily τ₀.work T)) N)
    (K E : Finset (ActualFamily τ₀.work T)) (hK : HasSpanColoring K 2) (hE : E.card ≤ 1)
    (hsmall : ∀ F, F ∉ K ∪ E → (F.hops.card : ℝ) ≤ ε * ((d * d * b : ℕ) : ℝ)) :
    ((correctSet M d b τ₀ T).card : ℝ) ≤ (2 : ℝ) ^ ((1 - ε) * ((d * d * b : ℕ) : ℝ)) := by
  rcases (correctSet M d b τ₀ T).eq_empty_or_nonempty with h0 | hne
  · rw [h0, card_empty, Nat.cast_zero]
    positivity
  rcases le_or_gt ε 0 with hε | hε
  · exact card_le_of_nonpos _ hε
  have hεL : 0 ≤ ε * ((d * d * b : ℕ) : ℝ) := by positivity
  have hE' : (E \ K).card ≤ 1 := (card_le_card sdiff_subset).trans hE
  have hsize : ∀ F : ActualFamily τ₀.work T, F ∉ K ∪ E \ K →
      F.hops.card ≤ ⌊ε * ((d * d * b : ℕ) : ℝ)⌋₊ := by
    intro F hF
    rw [union_sdiff_self_eq_union] at hF
    exact Nat.le_floor (hsmall F hF)
  let G := frozenGeometry β N 1 hd hb τ₀ T hT happ _ hne (fun X hX => mem_correctSet.mp hX) hβ
    hN K (E \ K) hK hE' disjoint_sdiff ⌊ε * ((d * d * b : ℕ) : ℝ)⌋₊ hsize
  exact (hcor G hd₀ (Nat.floor_le hεL)).2

/-- **Transfer of class-uniform bounds** (Remark `rem:LA-scope`(3)). Every bound
`|C| ≤ 2^{(1-ε)L}` valid on a class `P` of admissible geometries holds for the inputs that agree
with `τ₀` before `T` and are transposed by `M`, provided the frozen geometry of `(τ₀, T)` with the
labels `K, E, a₀` lies in `P`. This transfers, for instance, the ninth paper's Corollaries 4.4 and
4.7, with their hypotheses imposed on the frozen geometry. -/
theorem card_correctSet_le_of_class {c β ε : ℝ} {N q : ℕ}
    (P : AdmissibleGeometry (2 * c) β N q → Prop)
    (hP : ∀ G, P G → (G.C.card : ℝ) ≤ (2 : ℝ) ^ ((1 - ε) * G.inputLength))
    {M : TM} (hβ : capacityBits M ≤ β) {d b : ℕ} (hd : 0 < d) (hb : 0 < b) {τ₀ : Trace M.k}
    {T : ℕ} (hT : T ≤ ⌊c * (((d * d * b : ℕ) : ℝ) + 1)⌋₊)
    (happ : d * d * b ≤ (appendList τ₀ T).length)
    (hN : HasSpanColoring (univ : Finset (ActualFamily τ₀.work T)) N)
    (K E : Finset (ActualFamily τ₀.work T)) (hK : HasSpanColoring K 2) (hE : E.card ≤ q)
    (hKE : Disjoint K E) (a₀ : ℕ)
    (ha₀ : ∀ F : ActualFamily τ₀.work T, F ∉ K ∪ E → F.hops.card ≤ a₀)
    (hclass : ∀ hne : (correctSet M d b τ₀ T).Nonempty,
      P (frozenGeometry β N q hd hb τ₀ T hT happ _ hne (fun _ hX => mem_correctSet.mp hX) hβ hN
        K E hK hE hKE a₀ ha₀)) :
    ((correctSet M d b τ₀ T).card : ℝ) ≤ (2 : ℝ) ^ ((1 - ε) * ((d * d * b : ℕ) : ℝ)) := by
  rcases (correctSet M d b τ₀ T).eq_empty_or_nonempty with h0 | hne
  · rw [h0, card_empty, Nat.cast_zero]
    positivity
  exact hP _ (hclass hne)

/-! ### Theorem LA, probability form: full traces of a transposer -/

section Full

variable {M : TM} {d b : ℕ} {c : ℝ} {τ₀ : Trace M.k}

/-- A trace with an input transposed within `c (L + 1)` steps in its fibre halts within
`⌊c (L + 1)⌋` steps and appends exactly `L` bits before its halting time. -/
theorem fibre_haltTime {X : Fin (d * d * b) → Bool} (hX : X ∈ fibre M (d * d * b) τ₀)
    (htr : TransposesInput M d b c X) :
    τ₀.haltTime ≤ ⌊c * (((d * d * b : ℕ) : ℝ) + 1)⌋₊ ∧
      (appendList τ₀ τ₀.haltTime).length = d * d * b := by
  obtain ⟨s, hs, hhalt⟩ := htr.halts
  obtain ⟨s', hhalt', hlen, -⟩ := htr.outputsTranspose.output
  have hss' : s' = s := haltsAt_unique hhalt' hhalt
  subst hss'
  have hτs : τ₀.HaltsAt s' := by
    have := (haltsAt_iff_trace s').mp hhalt
    rwa [mem_fibre.mp hX] at this
  have e : τ₀.haltTime = s' := (τ₀.haltsAt_haltTime ⟨s', hτs.2⟩).unique hτs
  rw [e]
  refine ⟨hs, ?_⟩
  have hfilt : (List.range s').filter (fun t => (outBit M (List.ofFn X) t).isSome) =
      appendList τ₀ s' := by
    unfold appendList
    refine List.filter_congr fun t _ => ?_
    rw [outBit_isSome_eq, mem_fibre.mp hX]
  rw [← hlen, outRev_reverse_eq, List.length_filterMap_eq_countP, List.countP_eq_length_filter,
    hfilt]

/-- For a transposer, the fibre of a trace lies in its correct set up to the halting time. -/
theorem fibre_subset_correctSet (htr : TransposesAtWidth M d b c) :
    fibre M (d * d * b) τ₀ ⊆ correctSet M d b τ₀ τ₀.haltTime := fun X hX =>
  mem_correctSet.mpr ⟨fun t _ => by rw [mem_fibre.mp hX],
    (htr.transposesInput X).outputsTranspose⟩

/-- From a bound on the fibre to a bound on the probability. -/
theorem traceProb_le_of_card_le {L : ℕ} {ε : ℝ}
    (h : ((fibre M L τ₀).card : ℝ) ≤ (2 : ℝ) ^ ((1 - ε) * (L : ℝ))) :
    traceProb M L τ₀ ≤ (2 : ℝ) ^ (-ε * (L : ℝ)) := by
  have h2 : (0 : ℝ) < 2 ^ L := by positivity
  rw [card_fibre_eq, show (1 - ε) * (L : ℝ) = L + -ε * L by ring,
    Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_natCast] at h
  exact le_of_mul_le_mul_left h h2

/-- **Theorem LA(a), probability form.** Let `ε, d₀` be constants of Corollary 4.5 for the
parameters `(2c, β, N, q)`, `capacityBits M ≤ β`, and let `M` transpose `d × d` matrices with
`b`-bit entries within `c (L + 1)` steps, `b ≥ 1`, `d ≥ max(d₀, 1)`. Every trace whose complete
families admit an `N`-class span partition, at most `q` of them with more than `εL` hops, has
probability at most `2^{-εL}`. -/
theorem traceProb_le_a {c β ε : ℝ} {N q d₀ : ℕ} (hcor : IsSkeletonConstant (2 * c) β N q ε d₀)
    (hβ : capacityBits M ≤ β) (hd : 0 < d) (hb : 0 < b) (hd₀ : d₀ ≤ d)
    (htr : TransposesAtWidth M d b c)
    (hN : HasSpanColoring (univ : Finset (ActualFamily τ₀.work τ₀.haltTime)) N)
    (hq : (univ.filter fun F : ActualFamily τ₀.work τ₀.haltTime =>
      ε * ((d * d * b : ℕ) : ℝ) < (F.hops.card : ℝ)).card ≤ q) :
    traceProb M (d * d * b) τ₀ ≤ (2 : ℝ) ^ (-ε * ((d * d * b : ℕ) : ℝ)) := by
  apply traceProb_le_of_card_le
  rcases (fibre M (d * d * b) τ₀).eq_empty_or_nonempty with h0 | ⟨X, hX⟩
  · rw [h0, card_empty, Nat.cast_zero]
    positivity
  obtain ⟨hT, happ⟩ := fibre_haltTime hX (htr.transposesInput X)
  calc ((fibre M (d * d * b) τ₀).card : ℝ) ≤ (correctSet M d b τ₀ τ₀.haltTime).card := by
        exact_mod_cast card_le_card (fibre_subset_correctSet htr)
    _ ≤ _ := card_correctSet_le_a hcor hβ hd hb hd₀ hT happ.ge hN hq

/-- **Theorem LA(b), probability form.** As `traceProb_le_a`, for the constants of Corollary 4.3
and traces whose complete families admit an `N`-class span partition and split into a Q2 core, at
most one further family, and families of at most `εL` hops each. -/
theorem traceProb_le_b {c β ε : ℝ} {N d₀ : ℕ} (hcor : IsOneExceptionConstant (2 * c) β N ε d₀)
    (hβ : capacityBits M ≤ β) (hd : 0 < d) (hb : 0 < b) (hd₀ : d₀ ≤ d)
    (htr : TransposesAtWidth M d b c)
    (hN : HasSpanColoring (univ : Finset (ActualFamily τ₀.work τ₀.haltTime)) N)
    (K E : Finset (ActualFamily τ₀.work τ₀.haltTime)) (hK : HasSpanColoring K 2)
    (hE : E.card ≤ 1)
    (hsmall : ∀ F, F ∉ K ∪ E → (F.hops.card : ℝ) ≤ ε * ((d * d * b : ℕ) : ℝ)) :
    traceProb M (d * d * b) τ₀ ≤ (2 : ℝ) ^ (-ε * ((d * d * b : ℕ) : ℝ)) := by
  apply traceProb_le_of_card_le
  rcases (fibre M (d * d * b) τ₀).eq_empty_or_nonempty with h0 | ⟨X, hX⟩
  · rw [h0, card_empty, Nat.cast_zero]
    positivity
  obtain ⟨hT, happ⟩ := fibre_haltTime hX (htr.transposesInput X)
  calc ((fibre M (d * d * b) τ₀).card : ℝ) ≤ (correctSet M d b τ₀ τ₀.haltTime).card := by
        exact_mod_cast card_le_card (fibre_subset_correctSet htr)
    _ ≤ _ := card_correctSet_le_b hcor hβ hd hb hd₀ hT happ.ge hN K E hK hE hsmall

end Full

/-! ### The modelling step: the fibre geometry -/

section FibreGeometry

variable {M : TM} {d b : ℕ} {c : ℝ}

/-- **The fibre geometry (the modelling step).** For a machine that transposes `d × d` matrices
with `b`-bit entries within `c (L + 1)` steps and a trace `τ₀` with a nonempty fibre `W`, the frozen
geometry of `τ₀` up to its halting time, with correctness set exactly `W` and the given labels. -/
noncomputable def fibreGeometry (β : ℝ) (N q : ℕ) (hd : 0 < d) (hb : 0 < b)
    (htr : TransposesAtWidth M d b c) (τ₀ : Trace M.k) (hne : (fibre M (d * d * b) τ₀).Nonempty)
    (hβ : capacityBits M ≤ β)
    (hN : HasSpanColoring (univ : Finset (ActualFamily τ₀.work τ₀.haltTime)) N)
    (K E : Finset (ActualFamily τ₀.work τ₀.haltTime)) (hK : HasSpanColoring K 2)
    (hE : E.card ≤ q) (hKE : Disjoint K E) (a₀ : ℕ)
    (ha₀ : ∀ F : ActualFamily τ₀.work τ₀.haltTime, F ∉ K ∪ E → F.hops.card ≤ a₀) :
    AdmissibleGeometry (2 * c) β N q :=
  frozenGeometry β N q hd hb τ₀ τ₀.haltTime
    (fibre_haltTime hne.choose_spec (htr.transposesInput _)).1
    (fibre_haltTime hne.choose_spec (htr.transposesInput _)).2.ge
    (fibre M (d * d * b) τ₀) hne
    (fun X hX => ⟨fun _ _ => by rw [mem_fibre.mp hX], (htr.transposesInput X).outputsTranspose⟩)
    hβ hN K E hK hE hKE a₀ ha₀

theorem fibreGeometry_C {β : ℝ} {N q : ℕ} {hd : 0 < d} {hb : 0 < b}
    {htr : TransposesAtWidth M d b c} {τ₀ : Trace M.k} {hne : (fibre M (d * d * b) τ₀).Nonempty}
    {hβ : capacityBits M ≤ β}
    {hN : HasSpanColoring (univ : Finset (ActualFamily τ₀.work τ₀.haltTime)) N}
    {K E : Finset (ActualFamily τ₀.work τ₀.haltTime)} {hK : HasSpanColoring K 2}
    {hE : E.card ≤ q} {hKE : Disjoint K E} {a₀ : ℕ}
    {ha₀ : ∀ F : ActualFamily τ₀.work τ₀.haltTime, F ∉ K ∪ E → F.hops.card ≤ a₀} :
    (fibreGeometry β N q hd hb htr τ₀ hne hβ hN K E hK hE hKE a₀ ha₀).C = fibre M (d * d * b) τ₀ :=
  rfl

/-- The correctness deficit of the fibre geometry: `Δ = L - log₂ |W| ≤ ηL` when `τ₀` has
probability at least `2^{-ηL}`. -/
theorem fibreGeometry_deficit_le {β : ℝ} {N q : ℕ} {hd : 0 < d} {hb : 0 < b}
    {htr : TransposesAtWidth M d b c} {τ₀ : Trace M.k} {hne : (fibre M (d * d * b) τ₀).Nonempty}
    {hβ : capacityBits M ≤ β}
    {hN : HasSpanColoring (univ : Finset (ActualFamily τ₀.work τ₀.haltTime)) N}
    {K E : Finset (ActualFamily τ₀.work τ₀.haltTime)} {hK : HasSpanColoring K 2}
    {hE : E.card ≤ q} {hKE : Disjoint K E} {a₀ : ℕ}
    {ha₀ : ∀ F : ActualFamily τ₀.work τ₀.haltTime, F ∉ K ∪ E → F.hops.card ≤ a₀} {η : ℝ}
    (hprob : (2 : ℝ) ^ (-η * ((d * d * b : ℕ) : ℝ)) ≤ traceProb M (d * d * b) τ₀) :
    (fibreGeometry β N q hd hb htr τ₀ hne hβ hN K E hK hE hKE a₀ ha₀).deficit ≤
      η * ((d * d * b : ℕ) : ℝ) := by
  have hW := two_rpow_le_card_fibre hprob
  have hlog := Real.log_le_log (by positivity) hW
  rw [Real.log_rpow (by norm_num)] at hlog
  have hl2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have h : (1 - η) * ((d * d * b : ℕ) : ℝ) ≤
      Real.log ((fibre M (d * d * b) τ₀).card : ℝ) / Real.log 2 := by
    rw [le_div_iff₀ hl2]
    exact hlog
  show ((d * d * b : ℕ) : ℝ) - Real.log ((fibre M (d * d * b) τ₀).card : ℝ) / Real.log 2 ≤ _
  linarith

end FibreGeometry

/-! ### Theorem LA as stated -/

/-- A probability of at least `2^{-ηL}` and at most `2^{-εL}` forces `ε ≤ η`. -/
theorem le_of_prob_bounds {L : ℕ} (hL : 0 < L) {η ε x : ℝ} (h1 : (2 : ℝ) ^ (-η * L) ≤ x)
    (h2 : x ≤ (2 : ℝ) ^ (-ε * L)) : ε ≤ η := by
  have h := (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mp (h1.trans h2)
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  nlinarith

theorem inputLength_pos {d : ℕ} (hd : 0 < d) : 0 < inputLength d :=
  Nat.mul_pos (Nat.mul_pos hd hd) (Nat.succ_pos _)

/-- A trace of probability at least `2^{-ηL}` has a nonempty fibre, and `η ≥ 0`. -/
theorem fibre_facts {M : TM} {L : ℕ} (hL : 0 < L) {τ₀ : Trace M.k} {η : ℝ}
    (h : (2 : ℝ) ^ (-η * L) ≤ traceProb M L τ₀) : 0 ≤ η ∧ (fibre M L τ₀).Nonempty := by
  refine ⟨?_, ?_⟩
  · have hle : traceProb M L τ₀ ≤ (2 : ℝ) ^ (-(0 : ℝ) * L) := by
      rw [neg_zero, zero_mul, Real.rpow_zero]
      unfold traceProb
      rw [div_le_one (by positivity)]
      exact_mod_cast card_le_two_pow _
    exact le_of_prob_bounds hL h hle
  · rw [← card_pos]
    have : (0 : ℝ) < (fibre M L τ₀).card :=
      lt_of_lt_of_le (by positivity) (two_rpow_le_card_fibre h)
    exact_mod_cast this

/-- **Theorem LA(a).** Let `ε, d₀` be constants of the ninth paper's Corollary 4.5 for the
parameters `(2c, β, N, q)`, let `M` have value width at most `β`, and let `η < ε`. At no
dimension `d ≥ max(d₀, 1)` does `M` both (i) transpose at dimension `d` within `c (L + 1)` steps
and (ii) have a trace `τ₀` of probability at least `2^{-ηL}` whose complete families admit an
`N`-class span partition and at most `q` of which have more than `εL` hops. -/
theorem low_adaptivity_a {c β ε : ℝ} {N q d₀ : ℕ} (hcor : IsSkeletonConstant (2 * c) β N q ε d₀)
    {M : TM} (hβ : (valueWidth M : ℝ) ≤ β) {η : ℝ} (hη : η < ε) {d : ℕ} (hd : 0 < d)
    (hd₀ : d₀ ≤ d) :
    ¬ (TransposesAt M d c ∧
      ∃ τ₀ : Trace M.k, (2 : ℝ) ^ (-η * inputLength d) ≤ traceProb M (inputLength d) τ₀ ∧
        HasSpanColoring (univ : Finset (ActualFamily τ₀.work τ₀.haltTime)) N ∧
        (univ.filter fun F : ActualFamily τ₀.work τ₀.haltTime =>
          ε * inputLength d < (F.hops.card : ℝ)).card ≤ q) := by
  rintro ⟨htr, τ₀, hprob, hN, hq⟩
  have hL := inputLength_pos hd
  have hL' : (0 : ℝ) < inputLength d := by exact_mod_cast hL
  -- the fibre `W` of `τ₀` is nonempty, and `η ≥ 0`
  obtain ⟨hη0, hne⟩ := fibre_facts hL hprob
  have hεL : 0 ≤ ε * (inputLength d : ℝ) := by nlinarith
  -- the geometry of `τ₀` and `W`, with empty core and exceptions, and `a₀` the largest hop count
  have h2 : HasSpanColoring (∅ : Finset (ActualFamily τ₀.work τ₀.haltTime)) 2 :=
    ⟨fun _ => 0, by simp, by simp⟩
  let G := fibreGeometry β N 0 hd (Nat.succ_pos _) htr τ₀ hne
    ((capacityBits_le_valueWidth M).trans hβ) hN ∅ ∅ h2 (by simp) (disjoint_empty_left _)
    (univ.sup fun F : ActualFamily τ₀.work τ₀.haltTime => F.hops.card)
    (fun F _ => le_sup (f := fun F : ActualFamily τ₀.work τ₀.haltTime => F.hops.card) (mem_univ F))
  -- its correctness deficit is at most `ηL`
  have hΔ : G.deficit ≤ η * inputLength d := fibreGeometry_deficit_le hprob
  -- Corollary 4.5 with the skeleton of the at most `q` families of more than `εL` hops
  have hsize : ∀ F : ActualFamily τ₀.work τ₀.haltTime,
      F ∉ univ.filter (fun F : ActualFamily τ₀.work τ₀.haltTime =>
        ε * inputLength d < (F.hops.card : ℝ)) → F.hops.card ≤ ⌊ε * inputLength d⌋₊ := by
    intro F hF
    apply Nat.le_floor
    simpa using hF
  have hεΔ : ε * inputLength d ≤ G.deficit := (hcor G _ hq _ hsize hd₀ (Nat.floor_le hεL)).1
  exact absurd (le_of_mul_le_mul_right (hεΔ.trans hΔ) hL') (not_le.mpr hη)

/-- **Theorem LA(b).** Let `ε, d₀` be constants of the ninth paper's Corollary 4.3 for the
parameters `(2c, β, N)`, let `M` have value width at most `β`, and let `η < ε`. At no dimension
`d ≥ max(d₀, 1)` does `M` both (i) transpose at dimension `d` within `c (L + 1)` steps and (ii)
have a trace `τ₀` of probability at least `2^{-ηL}` whose complete families admit an `N`-class span
partition and split into a Q2 core `K`, at most one further family, and families of at most
`εL` hops each. -/
theorem low_adaptivity_b {c β ε : ℝ} {N d₀ : ℕ} (hcor : IsOneExceptionConstant (2 * c) β N ε d₀)
    {M : TM} (hβ : (valueWidth M : ℝ) ≤ β) {η : ℝ} (hη : η < ε) {d : ℕ} (hd : 0 < d)
    (hd₀ : d₀ ≤ d) :
    ¬ (TransposesAt M d c ∧
      ∃ τ₀ : Trace M.k, (2 : ℝ) ^ (-η * inputLength d) ≤ traceProb M (inputLength d) τ₀ ∧
        HasSpanColoring (univ : Finset (ActualFamily τ₀.work τ₀.haltTime)) N ∧
        ∃ K E : Finset (ActualFamily τ₀.work τ₀.haltTime), HasSpanColoring K 2 ∧ E.card ≤ 1 ∧
          ∀ F, F ∉ K ∪ E → (F.hops.card : ℝ) ≤ ε * inputLength d) := by
  rintro ⟨htr, τ₀, hprob, hN, K, E, hK, hE, hsmall⟩
  have hL := inputLength_pos hd
  have hL' : (0 : ℝ) < inputLength d := by exact_mod_cast hL
  obtain ⟨hη0, hne⟩ := fibre_facts hL hprob
  have hεL : 0 ≤ ε * (inputLength d : ℝ) := by nlinarith
  -- the core `K`, the further family as the exceptional set, and `a₀ = ⌊εL⌋`
  have hE' : (E \ K).card ≤ 1 := (card_le_card sdiff_subset).trans hE
  have hsize : ∀ F : ActualFamily τ₀.work τ₀.haltTime, F ∉ K ∪ E \ K →
      F.hops.card ≤ ⌊ε * inputLength d⌋₊ := by
    intro F hF
    rw [union_sdiff_self_eq_union] at hF
    exact Nat.le_floor (hsmall F hF)
  let G := fibreGeometry β N 1 hd (Nat.succ_pos _) htr τ₀ hne
    ((capacityBits_le_valueWidth M).trans hβ) hN K (E \ K) hK hE' disjoint_sdiff
    ⌊ε * inputLength d⌋₊ hsize
  have hΔ : G.deficit ≤ η * inputLength d := fibreGeometry_deficit_le hprob
  -- Corollary 4.3
  have hεΔ : ε * inputLength d ≤ G.deficit := (hcor G hd₀ (Nat.floor_le hεL)).1
  exact absurd (le_of_mul_le_mul_right (hεΔ.trans hΔ) hL') (not_le.mpr hη)

/-- **Theorem LA(a)**, with the constants packaged: uniform constants `ε > 0` and `d₀` depending
only on `(c, β, N, q)`, valid for every machine of value width at most `β`. -/
theorem low_adaptivity_a_exists (c β : ℝ) (N q : ℕ) :
    ∃ ε > (0 : ℝ), ∃ d₀ : ℕ, ∀ M : TM, (valueWidth M : ℝ) ≤ β → ∀ η < ε, ∀ d ≥ d₀,
      ¬ (TransposesAt M d c ∧
        ∃ τ₀ : Trace M.k, (2 : ℝ) ^ (-η * inputLength d) ≤ traceProb M (inputLength d) τ₀ ∧
          HasSpanColoring (univ : Finset (ActualFamily τ₀.work τ₀.haltTime)) N ∧
          (univ.filter fun F : ActualFamily τ₀.work τ₀.haltTime =>
            ε * inputLength d < (F.hops.card : ℝ)).card ≤ q) := by
  obtain ⟨ε, hε, d₀, h⟩ := exists_skeletonConstant (2 * c) β N q
  exact ⟨ε, hε, max d₀ 1, fun M hβ η hη d hd =>
    low_adaptivity_a h hβ hη (by omega) (le_of_max_le_left hd)⟩

/-- **Theorem LA(b)**, with the constants packaged: uniform constants `ε > 0` and `d₀` depending
only on `(c, β, N)`, valid for every machine of value width at most `β`. -/
theorem low_adaptivity_b_exists (c β : ℝ) (N : ℕ) :
    ∃ ε > (0 : ℝ), ∃ d₀ : ℕ, ∀ M : TM, (valueWidth M : ℝ) ≤ β → ∀ η < ε, ∀ d ≥ d₀,
      ¬ (TransposesAt M d c ∧
        ∃ τ₀ : Trace M.k, (2 : ℝ) ^ (-η * inputLength d) ≤ traceProb M (inputLength d) τ₀ ∧
          HasSpanColoring (univ : Finset (ActualFamily τ₀.work τ₀.haltTime)) N ∧
          ∃ K E : Finset (ActualFamily τ₀.work τ₀.haltTime), HasSpanColoring K 2 ∧ E.card ≤ 1 ∧
            ∀ F, F ∉ K ∪ E → (F.hops.card : ℝ) ≤ ε * inputLength d) := by
  obtain ⟨ε, hε, d₀, h⟩ := exists_oneExceptionConstant (2 * c) β N
  exact ⟨ε, hε, max d₀ 1, fun M hβ η hη d hd =>
    low_adaptivity_b h hβ hη (by omega) (le_of_max_le_left hd)⟩

/-! ### Many traces -/

open Classical in
/-- **Many traces.** Let `ε, d₀` be constants of Corollary 4.5 for `(2c, β, N, q)`,
`capacityBits M ≤ β`, and let `M` transpose `d × d` matrices with `b`-bit entries within
`c (L + 1)` steps, `b ≥ 1`, `d ≥ max(d₀, 1)`. If the trace of every input has the family
structure of Theorem LA(a), then the runs have at least `2^{εL}` distinct traces. -/
theorem card_traces_ge_a {c β ε : ℝ} {N q d₀ : ℕ} (hcor : IsSkeletonConstant (2 * c) β N q ε d₀)
    {M : TM} (hβ : capacityBits M ≤ β) {d b : ℕ} (hd : 0 < d) (hb : 0 < b) (hd₀ : d₀ ≤ d)
    (htr : TransposesAtWidth M d b c)
    (hall : ∀ X : Fin (d * d * b) → Bool,
      HasSpanColoring (univ : Finset (ActualFamily (trace M (List.ofFn X)).work
        (trace M (List.ofFn X)).haltTime)) N ∧
      (univ.filter fun F : ActualFamily (trace M (List.ofFn X)).work
        (trace M (List.ofFn X)).haltTime =>
          ε * ((d * d * b : ℕ) : ℝ) < (F.hops.card : ℝ)).card ≤ q) :
    (2 : ℝ) ^ (ε * ((d * d * b : ℕ) : ℝ)) ≤
      ((univ : Finset (Fin (d * d * b) → Bool)).image fun X => trace M (List.ofFn X)).card := by
  classical
  set L := d * d * b
  set I := (univ : Finset (Fin L → Bool)).image fun X => trace M (List.ofFn X)
  have hfib : ∀ τ ∈ I, ((univ.filter fun X : Fin L → Bool => trace M (List.ofFn X) = τ).card : ℝ)
      ≤ (2 : ℝ) ^ L * (2 : ℝ) ^ (-ε * (L : ℝ)) := by
    intro τ hτ
    obtain ⟨X, -, rfl⟩ := mem_image.mp hτ
    have hp := traceProb_le_a hcor hβ hd hb hd₀ htr (hall X).1 (hall X).2
    have e : (univ.filter fun Y : Fin L → Bool =>
        trace M (List.ofFn Y) = trace M (List.ofFn X)) = fibre M L (trace M (List.ofFn X)) := by
      unfold fibre
      congr 1
    rw [e, card_fibre_eq]
    exact mul_le_mul_of_nonneg_left hp (by positivity)
  have hsum : ((univ : Finset (Fin L → Bool)).card : ℝ) ≤
      I.card * ((2 : ℝ) ^ L * (2 : ℝ) ^ (-ε * (L : ℝ))) := by
    rw [card_eq_sum_card_image (fun X : Fin L → Bool => trace M (List.ofFn X)) univ]
    push_cast
    calc (∑ τ ∈ I, ((univ.filter fun X : Fin L → Bool => trace M (List.ofFn X) = τ).card : ℝ))
        ≤ ∑ _τ ∈ I, (2 : ℝ) ^ L * (2 : ℝ) ^ (-ε * (L : ℝ)) := sum_le_sum hfib
      _ = I.card * ((2 : ℝ) ^ L * (2 : ℝ) ^ (-ε * (L : ℝ))) := by
          rw [sum_const, nsmul_eq_mul]
  have hu : ((univ : Finset (Fin L → Bool)).card : ℝ) = (2 : ℝ) ^ L := by
    rw [card_univ]
    simp
  rw [hu] at hsum
  have h2L : (0 : ℝ) < 2 ^ L := by positivity
  have h1 : 1 ≤ (I.card : ℝ) * (2 : ℝ) ^ (-ε * (L : ℝ)) := by
    have : (2 : ℝ) ^ L * 1 ≤ (2 : ℝ) ^ L * ((I.card : ℝ) * (2 : ℝ) ^ (-ε * (L : ℝ))) := by
      calc (2 : ℝ) ^ L * 1 = (2 : ℝ) ^ L := mul_one _
        _ ≤ _ := hsum
        _ = _ := by ring
    exact le_of_mul_le_mul_left this h2L
  have hinv : (2 : ℝ) ^ (ε * (L : ℝ)) * (2 : ℝ) ^ (-ε * (L : ℝ)) = 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    simp
  have hpos : (0 : ℝ) ≤ (2 : ℝ) ^ (ε * (L : ℝ)) := by positivity
  calc (2 : ℝ) ^ (ε * (L : ℝ)) = (2 : ℝ) ^ (ε * (L : ℝ)) * 1 := (mul_one _).symm
    _ ≤ (2 : ℝ) ^ (ε * (L : ℝ)) * ((I.card : ℝ) * (2 : ℝ) ^ (-ε * (L : ℝ))) :=
        mul_le_mul_of_nonneg_left h1 hpos
    _ = I.card * ((2 : ℝ) ^ (ε * (L : ℝ)) * (2 : ℝ) ^ (-ε * (L : ℝ))) := by ring
    _ = I.card := by rw [hinv, mul_one]

end MergeDepth
