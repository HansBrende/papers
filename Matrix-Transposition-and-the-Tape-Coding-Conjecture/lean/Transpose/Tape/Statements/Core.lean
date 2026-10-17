import Transpose.Tape.Defs
import Transpose.Tape.Witness
import Transpose.Tape.Witnesses
import Transpose.Tape.Corollaries
import Transpose.Tape.DefsP
import Transpose.Tape.TheoremP
import Transpose.Tape.DefsM
import Transpose.Tape.MStar

/-!
# Locality, cut bounds, blocks, Theorem P and Theorem M\*

All statements refer to the frozen model of `Transpose/Statement.lean`. Each is proved by the
`Impl` theorem of the same name, except the witnesses `theoremP_hyps_tr2` and `theoremP_hyps_tr2k`,
which are assembled from public lemmas. Definitions are in `Defs.lean` (runs, obliviousness, entry
data, cut sets, blocks, residencies and slot labellings), `DefsP.lean` (passes, addresses and
forests) and `DefsM.lean` (rescaled trajectories, level sets and labellings of `[0, c₀]`), all in
`Transpose/Tape/`.

* **Bridge lemmas:**
  * `run`, `transAt` and `HaltsAt` agree with the frozen `stepN`, `step` and `ComputesWithin`, and
    `TransposesWithin M T` gives `Transposes M n (entryBits n)` for every `n ≥ 1`
    (`transposes_of_transposesWithin`);
  * the output is the list of appended bits, and a work cell holds the symbol written at its last
    visit (`work_eq_written`, `work_eq_blank`);
  * obliviousness plus correctness is satisfiable: the copy machine for `n = 1`, and the
    9-state `Witness.tr2` for `n = 2`, `b = 1`, where cuts are non-trivial.
* **The Locality Lemma:**
  * `locality`: two runs, which need only common work-head positions;
  * `locality_oblivious`;
  * `locality_function`: on an oblivious class, the transitions taken during `J` are a function of
    the entry data of `J`;
  * `locality_core`: arbitrary step sets with data-dependent heads; it contains
    `locality_interval` (intervals, with agreement required only at the start of the interval) and
    the anchored and entry forms `locality_anchored` and `locality_entry` of
    `Statements/Adaptive.lean`.
* **The Cut Lemma:**
  * `cut_bound_pairs`: `2^{b |S_J|} ≤ (q+1)^{e₁} (g+1)^{e₂}`;
  * strengthenings: `cut_bound` (the bit form with `cutSet ⊇ S_J × [b]`), `cut_bound_on`
    (any set on which the machine is oblivious and correct; the counting core of the popular
    trace) and `card_le_entryData` (the abstract injection form);
  * `cut_bound_bits`: the bits form;
  * `cut_bound_on_coentropy`: on a set of co-entropy `m`.
* **The Cut Lemma for families:**
  * `cut_bound_sum` and `cut_bound_sum_bits`, for any finite family of step sets;
    `cut_bound_sum_on`: on a set of co-entropy `m`;
  * `sum_cutPairs_ge`: `(n - σ)(n - ρ)` on the left;
  * `uncovered_cols_le`: `σ ≤ M_b` for parts that are unions of time intervals
    (`uncovered_cols_le_len`: for any run with `n²b` output bits).
* **Blocks:**
  * the Residency Lemma ((V1)): `pairRes_subset` and `pairRes_admissible` (pair residency, at most
    three resident blocks per slot, within `±1` of the head's block); `touchRes_admissible`: the
    touched variant, at most two blocks per slot;
  * (V2): `slot_block_step` and `exists_slot_block_eq`;
  * (P2): `pairRes_begin_unique`, `pairRes_end_unique`, `pairRes_chord_source_unique`,
    `pairRes_chord_target_unique`, and the same four for `touchRes`; its core is
    `pairChange_spacing`;
  * (P1), multi-homed rows: `srcRows_slotSteps_card_le`.
* **The Charging Lemma:** `entryTimes_card_le` (any admissible residency),
  `entryCells_slotSteps_card` (`e₂ = Σ_t e₂ᵗ`), `entryPoints_slotSteps_card` (`e₁ = μ`) and
  `charging_bound` (`e₂ ≤ r χ + c k r μ` for any admissible residency; `c = 3` for pair
  residency); the charging step in containment form: `entryTimes_charged`.
* **The Slot Cut Bound:**
  * `slot_cut_bound`, for a single union of slots;
  * `slot_cut_bound_partition`, the partition form with `M_b`, for any admissible residency;
  * `uncovered_cols_le_slots`: `σ ≤ M_b` (`uncovered_cols_le_slots_len`: for any run with `n²b`
    output bits).
* **Discrete Isoperimetry** (finitary): `isoperimetry_res` (any admissible residency),
  `isoperimetry` (pair residency) and `isoperimetry_touch` (touched residency);
  `isoperimetry_res_on`: on a set of co-entropy `mc` (each label class pays `mc`).
* **Theorem P** (passes of oblivious transposers; section below): `theoremP` and its bits, per-`n`,
  power and greedy forms; Theorem P_γ for groups of `γ` columns (`theoremP_grouped`); their forms
  on a set of inputs; and the lemmas of the proof: the Fresh-Cell Lemma (`pass_fresh`), the Forest
  Lemma (`forest_entryPoints_card_le`, `forest_entryCells_card_le`), the information count
  (`forest_info`) and the Disjointness Lemma (`forestNode_disjoint`, `read_chain`).
* **Theorem M\*** (section below): for oblivious transposers running in time `≤ c L`, every limit
  of the rescaled work-head trajectories satisfies the M\* inequality (★) for interval labellings
  (`theoremMStar_level`, `theoremMStar_level_subseq`); the labelling-free forms of (★) give total
  excess level multiplicity `≥ 1`, a bound on the total range, and limits that are not all monotone
  (`theoremMStar_excess`).

The popular trace and the Block Locality Lemma, which extend the Cut Lemma and Theorem M\* to
adaptive machines, are in `Statements/Adaptive.lean`; the Cut Lemma on a trace class there
(`cut_bound_trace`) shares its counting core `Impl.two_pow_mul_ncard_le` with `cut_bound_on`. The
Block Locality Lemma (`block_locality`) records the full head positions at memory boundaries: its
offsets-only form is false (`block_locality_offsets_counterexample`).

Conventions: `entryPoints` excludes step `0` and `memBoundaries` excludes slot `0`, because the
initial state is a constant; this gives `M_b` (not `M_b + 1`) in the partition forms.
`ObliviousOn M W T` fixes the input-head and work-head positions and the output-append decisions at
every time, including `τ = T`.
-/

namespace Transpose.Tape

open Transpose

/-! ## Bridge lemmas: the total run agrees with the frozen semantics -/

/-- `stepN` from the initial configuration succeeds with `c` exactly when no earlier step halts
and `c` is the configuration of the total run. -/
theorem stepN_init_eq_some_iff (M : TM) (w : List Bool) (τ : ℕ) (c : Config M) :
    stepN M w τ (init M) = some c ↔ (∀ σ < τ, transAt M w σ ≠ none) ∧ run M w τ = c :=
  Impl.stepN_init_eq_some_iff (M := M) (w := w) (τ := τ) (c := c)

/-- `ComputesWithin` in terms of the total run. -/
theorem computesWithin_iff (M : TM) (w out : List Bool) (t : ℕ) :
    ComputesWithin M w out t ↔ ∃ T ≤ t, HaltsAt M w T ∧ (run M w T).outRev.reverse = out :=
  Impl.computesWithin_iff (M := M) (w := w) (out := out) (t := t)

/-- The halting time is unique. -/
theorem haltsAt_unique {M : TM} {w : List Bool} {T T' : ℕ} (h : HaltsAt M w T)
    (h' : HaltsAt M w T') : T = T' :=
  Impl.haltsAt_unique (M := M) (w := w) (T := T) (T' := T') (h := h) (h' := h')

/-- The output so far is the list of bits appended at the steps so far, in order. -/
theorem outRev_reverse_eq (M : TM) (w : List Bool) (τ : ℕ) :
    (run M w τ).outRev.reverse = (List.range τ).filterMap (outBit M w) :=
  Impl.outRev_reverse_eq (M := M) (w := w) (τ := τ)

/-- A work cell holds the symbol written at the last step that visited it. Every step writes the
cell under each work head. -/
theorem work_eq_written (M : TM) (w : List Bool) (t : Fin M.k) (p : ℤ) {τ σ : ℕ} (hστ : σ < τ)
    (hσ : (run M w σ).workPos t = p)
    (hlast : ∀ ρ, σ < ρ → ρ < τ → (run M w ρ).workPos t ≠ p) :
    (run M w τ).work t p = writtenSym M w σ t :=
  Impl.work_eq_written (M := M) (w := w) (t := t) (p := p) (τ := τ) (σ := σ) (hστ := hστ) (hσ := hσ) (hlast := hlast)

/-- A work cell never visited before time `τ` is blank at time `τ`. -/
theorem work_eq_blank (M : TM) (w : List Bool) (t : Fin M.k) (p : ℤ) {τ : ℕ}
    (h : ∀ σ < τ, (run M w σ).workPos t ≠ p) : (run M w τ).work t p = 0 :=
  Impl.work_eq_blank (M := M) (w := w) (t := t) (p := p) (τ := τ) (h := h)

/-- The encodings of `n × n` matrices with `b`-bit entries are exactly the words of length
`n²b`. So `ObliviousOn M (matrixInputs n b) T` is obliviousness at input length `L = n²b`. -/
theorem matrixInputs_eq (n b : ℕ) : matrixInputs n b = inputsOfLength (n * n * b) :=
  Impl.matrixInputs_eq (n := n) (b := b)

/-- `tpos` sends input bit `t` of entry `(i, j)` to output bit `t` of entry `(j, i)`. (No bound on
the row index `i` is needed.) -/
theorem tpos_spec {n b i j t : ℕ} (hj : j < n) (ht : t < b) :
    tpos n b ((i * n + j) * b + t) = (j * n + i) * b + t :=
  Impl.tpos_spec (n := n) (b := b) (i := i) (j := j) (t := t) hj ht

/-- Non-vacuity: the copy machine of `Sanity.lean` is oblivious on the inputs of every length
`ℓ`, with running time `ℓ`. -/
theorem copyTM_obliviousOn (ℓ : ℕ) : ObliviousOn Sanity.copyTM (inputsOfLength ℓ) ℓ :=
  Impl.copyTM_obliviousOn (ℓ := ℓ)

/-- Non-vacuity: the copy machine transposes `1 × 1` matrices with `b`-bit entries. -/
theorem copyTM_transposes (b : ℕ) : Transposes Sanity.copyTM 1 b :=
  Impl.copyTM_transposes (b := b)

/-- Non-vacuity at `n = 2`: `Witness.tr2` is oblivious on the `2 × 2` matrices with 1-bit
entries, with running time `5`. -/
theorem tr2_obliviousOn : ObliviousOn Witness.tr2 (matrixInputs 2 1) 5 :=
  Impl.tr2_obliviousOn

/-- Non-vacuity at `n = 2`: `Witness.tr2` transposes `2 × 2` matrices with 1-bit entries. -/
theorem tr2_transposes : Transposes Witness.tr2 2 1 :=
  Impl.tr2_transposes

/-- Non-vacuity of the Cut Lemma at `n = 2`. For `Witness.tr2`, the all-zero input and
`J = {2, 3, 4}`, the set `S_J = {(0, 1)}` is nonempty; `J` has one entry point and, with no work
tapes, no entry cells. So `cut_bound_pairs` gives the non-trivial bound `2 ≤ 9`. -/
theorem tr2_cutPairs :
    cutPairs Witness.tr2 (encode 2 1 (fun _ _ _ => false)) 2 1 {2, 3, 4} = {(0, 1)} :=
  Impl.tr2_cutPairs

/-- Bridge to the frozen statement: a machine satisfying `TransposesWithin M T` transposes
`n × n` matrices with `entryBits n`-bit entries, for every `n ≥ 1`. -/
theorem transposes_of_transposesWithin {M : TM} {T : ℕ → ℕ} (h : TransposesWithin M T) :
    ∀ n, 1 ≤ n → Transposes M n (entryBits n) :=
  Impl.transposes_of_transposesWithin h

/-! ## The Locality Lemma for arbitrary step sets -/

/-- **Locality Lemma, two-run form.**

Setting: `w'` has the same work-head positions as `w` at all times `< T` (neither run need be
running: a halted run is frozen). Let `J ⊆ [0, T)` be any set of steps.

Suppose the two runs agree on the entry data of `J`:
* (i) the state at every entry point of `J` (the state at time `0` is the initial state in
  both runs, so it is not needed);
* (ii) the symbol under head `t` at time `τ`, for every external read `(t, τ)` of `J` (an entry
  cell);
* (iii) the input symbol read at every step of `J`.

Then at every step of `J` the two runs apply `δ` to identical arguments (the same state, input
symbol and work symbols). Hence they take the same transition: the same symbols written, the
same new state, and the same output bit (if any). -/
theorem locality {M : TM} {w w' : List Bool} {T : ℕ}
    (hwork : ∀ τ < T, (run M w τ).workPos = (run M w' τ).workPos)
    {J : Finset ℕ} (hJ : ∀ τ ∈ J, τ < T)
    (hstate : ∀ τ ∈ entryPoints J, (run M w τ).state = (run M w' τ).state)
    (hcell : ∀ p ∈ entryCells (workTraj M w) J, headSym M w p.2 p.1 = headSym M w' p.2 p.1)
    (hinput : ∀ τ ∈ J, inSym M w τ = inSym M w' τ) :
    ∀ τ ∈ J, (run M w τ).state = (run M w' τ).state ∧ headSym M w τ = headSym M w' τ ∧
      transAt M w τ = transAt M w' τ :=
  Impl.locality (M := M) (w := w) (w' := w') (T := T) (hwork := hwork) (J := J) (hJ := hJ) (hstate := hstate) (hcell := hcell) (hinput := hinput)

/-- **Locality Lemma for an oblivious class.** Suppose two inputs of the class agree on (i) the
states at the entry points of `J`, (ii) the symbols of the external reads of `J`, and (iii) the
input bits at the positions read during `J`. Then they apply `δ` to identical arguments at every
step of `J`. -/
theorem locality_oblivious {M : TM} {W : Set (List Bool)} {T : ℕ} (hobl : ObliviousOn M W T)
    {w w' : List Bool} (hw : w ∈ W) (hw' : w' ∈ W) {J : Finset ℕ} (hJ : ∀ τ ∈ J, τ < T)
    (hstate : ∀ τ ∈ entryPoints J, (run M w τ).state = (run M w' τ).state)
    (hcell : ∀ p ∈ entryCells (workTraj M w) J, headSym M w p.2 p.1 = headSym M w' p.2 p.1)
    (hbits : ∀ τ ∈ J, readInput w (run M w τ).inPos = readInput w' (run M w τ).inPos) :
    ∀ τ ∈ J, (run M w τ).state = (run M w' τ).state ∧ headSym M w τ = headSym M w' τ ∧
      inSym M w τ = inSym M w' τ ∧ transAt M w τ = transAt M w' τ :=
  Impl.locality_oblivious (M := M) (W := W) (T := T) (hobl := hobl) (w := w) (w' := w') (hw := hw) (hw' := hw') (J := J) (hJ := hJ) (hstate := hstate) (hcell := hcell) (hbits := hbits)

/-- **Locality Lemma, functional form.** On an oblivious class, the transitions taken during
`J` are a function of the entry data of `J`. The transitions record everything written and
appended during `J` and the state after every step of `J`. The entry data are the states at the
entry points, the symbols of the external reads, and the input symbols read during `J`. -/
theorem locality_function {M : TM} {W : Set (List Bool)} {T : ℕ} (hobl : ObliviousOn M W T)
    {w₀ : List Bool} (hw₀ : w₀ ∈ W) (J : Finset ℕ) (hJ : ∀ τ ∈ J, τ < T) :
    ∃ F : (entryPoints J → Fin (M.q + 1)) → (entryCells (workTraj M w₀) J → Fin (M.g + 1)) →
        (J → Option Bool) →
        (J → Option (Fin (M.q + 1) × Dir × (Fin M.k → Fin (M.g + 1) × Dir) × Option Bool)),
      ∀ w ∈ W, (fun τ : J => transAt M w τ.1) =
        F (fun τ => (run M w τ.1).state) (fun p => headSym M w p.1.2 p.1.1)
          (fun τ => inSym M w τ.1) :=
  Impl.locality_function (M := M) (W := W) (T := T) (hobl := hobl) (w₀ := w₀) (hw₀ := hw₀) (J := J) (hJ := hJ)

/-- **Locality Lemma, core form (data-dependent heads; arbitrary step sets).** Let `w` and `w'` be
any runs (they may halt), `J` a set of steps and `A` a set of anchors, such that every step of `J`
that is not an anchor has its predecessor in `J`. Suppose:
* at every anchor of `J` the two runs agree on the state, all head positions and the symbols under
  the work heads;
* for every other step `τ ∈ J` at which the work heads agree, and every work tape `t`, there is a
  time `a ≤ τ` at which the cell under head `t` (in `w`) has the same content in both runs, such
  that in each run the last visit of that cell during `[a, τ)` (if any) is a step of `J`;
* the two inputs agree at the position read at any step of `J` at which the input heads agree.

Then at every step of `J` the two runs agree on the state, all head positions and the symbols under
the work heads, and take the same transition. Up to the bookkeeping of the endpoint step and of the
output lengths, this contains `locality_interval` (`J = [a, b)`, anchor `a`), `locality_anchored`
(`a = 0`) and `locality_entry` (`Statements/Adaptive.lean`); the read condition of `locality_entry`
asks that all visits during `[a, τ)`, not only the last ones, lie in `J`. -/
theorem locality_core {M : TM} {w w' : List Bool} {J : Finset ℕ} {A : Set ℕ}
    (hpred : ∀ τ ∈ J, τ ∉ A → 1 ≤ τ ∧ τ - 1 ∈ J)
    (hanchor : ∀ τ ∈ J, τ ∈ A →
      (run M w τ).state = (run M w' τ).state ∧ (run M w τ).inPos = (run M w' τ).inPos ∧
      (run M w τ).workPos = (run M w' τ).workPos ∧ headSym M w τ = headSym M w' τ)
    (hread : ∀ τ ∈ J, τ ∉ A → (run M w τ).workPos = (run M w' τ).workPos → ∀ t : Fin M.k,
      ∃ a ≤ τ, (run M w a).work t (workTraj M w τ t) = (run M w' a).work t (workTraj M w τ t) ∧
      (∀ σ, a ≤ σ → σ < τ → workTraj M w σ t = workTraj M w τ t →
        (∀ ρ, σ < ρ → ρ < τ → workTraj M w ρ t ≠ workTraj M w τ t) → σ ∈ J) ∧
      (∀ σ, a ≤ σ → σ < τ → workTraj M w' σ t = workTraj M w τ t →
        (∀ ρ, σ < ρ → ρ < τ → workTraj M w' ρ t ≠ workTraj M w τ t) → σ ∈ J))
    (hinput : ∀ τ ∈ J, (run M w τ).inPos = (run M w' τ).inPos →
      readInput w (run M w τ).inPos = readInput w' (run M w τ).inPos) :
    ∀ τ ∈ J, (run M w τ).state = (run M w' τ).state ∧ (run M w τ).inPos = (run M w' τ).inPos ∧
      (run M w τ).workPos = (run M w' τ).workPos ∧
      headSym M w τ = headSym M w' τ ∧ transAt M w τ = transAt M w' τ :=
  Impl.locality_core hpred hanchor hread hinput

/-- **Locality Lemma, interval form with data-dependent heads.** Let `w` and `w'` be any runs (they
may halt during `[a, b)`). Suppose `w'` agrees with `w` at time `a` on:
* the state;
* all head positions;
* the contents of every work cell that `w` accesses during `[a, b)`;
* the input symbols at the positions `w` reads during `[a, b)`.

Then the two runs agree on the state and on all head positions at every time in `[a, b]`, and
take the same transition at every step of `[a, b)`. No agreement outside `[a, b]` is assumed. -/
theorem locality_interval {M : TM} {w w' : List Bool} {a b : ℕ}
    (hstate : (run M w a).state = (run M w' a).state)
    (hin : (run M w a).inPos = (run M w' a).inPos)
    (hwork : (run M w a).workPos = (run M w' a).workPos)
    (hcells : ∀ τ, a ≤ τ → τ < b → ∀ t : Fin M.k,
      (run M w a).work t ((run M w τ).workPos t) = (run M w' a).work t ((run M w τ).workPos t))
    (hbits : ∀ τ, a ≤ τ → τ < b →
      readInput w (run M w τ).inPos = readInput w' (run M w τ).inPos) :
    ∀ τ, a ≤ τ → τ ≤ b →
      (run M w τ).state = (run M w' τ).state ∧ (run M w τ).inPos = (run M w' τ).inPos ∧
        (run M w τ).workPos = (run M w' τ).workPos ∧
        (τ < b → transAt M w τ = transAt M w' τ) :=
  Impl.locality_interval (M := M) (w := w) (w' := w') (a := a) (b := b) (hstate := hstate) (hin := hin) (hwork := hwork) (hcells := hcells) (hbits := hbits)

/-! ## The Cut Lemma -/

/-- **Cut Lemma, abstract injection form.** Take a finite family of inputs from an oblivious
class. Suppose the inputs agree at every input position read during `J`, and are told apart by
the bits appended during `J`. Then there are at most `(q+1)^{e₁} (g+1)^{e₂}` of them. -/
theorem card_le_entryData {M : TM} {W : Set (List Bool)} {T : ℕ} (hobl : ObliviousOn M W T)
    {w₀ : List Bool} (hw₀ : w₀ ∈ W) {J : Finset ℕ} (hJ : ∀ τ ∈ J, τ < T)
    {X : Type*} [Fintype X] (f : X → List Bool) (hfW : ∀ x, f x ∈ W)
    (hbits : ∀ x x', ∀ τ ∈ J,
      readInput (f x) (run M w₀ τ).inPos = readInput (f x') (run M w₀ τ).inPos)
    (hinj : ∀ x x', (∀ τ ∈ J, outBit M (f x) τ = outBit M (f x') τ) → x = x') :
    Fintype.card X ≤
      (M.q + 1) ^ (entryPoints J).card * (M.g + 1) ^ (entryCells (workTraj M w₀) J).card :=
  Impl.card_le_entryData (M := M) (W := W) (T := T) (hobl := hobl) (w₀ := w₀) (hw₀ := hw₀) (J := J) (hJ := hJ) (X := X) (f := f) (hfW := hfW) (hbits := hbits) (hinj := hinj)

/-- **Cut Lemma, bit form (a strengthening).** Take an oblivious machine that transposes `n × n`
matrices with `b`-bit entries, and any `J ⊆ [0, T)`. Then
`2^{|cutSet J|} ≤ (q+1)^{e₁} (g+1)^{e₂}`, where `cutSet J` is the set of input bits not read
during `J` whose output copy is appended during `J`. Since `cutSet J ⊇ S_J × [b]`, this implies
`cut_bound_pairs`. -/
theorem cut_bound {M : TM} {n b T : ℕ} (hobl : ObliviousOn M (matrixInputs n b) T)
    (hcorr : Transposes M n b) {w₀ : List Bool} (hw₀ : w₀ ∈ matrixInputs n b)
    {J : Finset ℕ} (hJ : ∀ τ ∈ J, τ < T) :
    2 ^ (cutSet M w₀ n b J).card ≤
      (M.q + 1) ^ (entryPoints J).card * (M.g + 1) ^ (entryCells (workTraj M w₀) J).card :=
  Impl.cut_bound (M := M) (n := n) (b := b) (T := T) (hobl := hobl) (hcorr := hcorr) (w₀ := w₀) (hw₀ := hw₀) (J := J) (hJ := hJ)

/-- **Cut Lemma on a trajectory class (a strengthening).** Take any set `W` of inputs sharing one
cell-level trajectory, i.e. `M` is oblivious on `W` (halting time `T`), on which `M` outputs the
transposed encoding (so `W` consists of matrix inputs; `M` need not be correct elsewhere). Then
`2^{|cutSet J|} · |W| ≤ 2^{n²b} · (q+1)^{e₁} (g+1)^{e₂}`. This is the pigeonhole step of the
popular-trace argument. The popular trace itself needs classes sharing only a *block-level* trace;
that form is `cut_bound_trace` in `Statements/Adaptive.lean`, via the Block Locality Lemma
(`block_locality`). -/
theorem cut_bound_on {M : TM} {n b T : ℕ} {W : Set (List Bool)} (hobl : ObliviousOn M W T)
    (hcorr : ∀ w ∈ W, ∃ A : Matrix, w = encode n b A ∧
      (run M w T).outRev.reverse = encode n b (transpose A))
    {w₀ : List Bool} (hw₀ : w₀ ∈ W) {J : Finset ℕ} (hJ : ∀ τ ∈ J, τ < T) :
    2 ^ (cutSet M w₀ n b J).card * W.ncard ≤
      2 ^ (n * n * b) *
        ((M.q + 1) ^ (entryPoints J).card * (M.g + 1) ^ (entryCells (workTraj M w₀) J).card) :=
  Impl.cut_bound_on hobl hcorr hw₀ hJ

/-- The bits of `S_J × [b]` lie in the cut set: `|S_J| · b ≤ |cutSet J|`. -/
theorem cutPairs_card_mul_le (M : TM) (w₀ : List Bool) (n b : ℕ) (J : Finset ℕ) :
    (cutPairs M w₀ n b J).card * b ≤ (cutSet M w₀ n b J).card :=
  Impl.cutPairs_card_mul_le (M := M) (w₀ := w₀) (n := n) (b := b) (J := J)

/-- **Cut Lemma:** `2^{b |S_J|} ≤ (q+1)^{e₁(J)} (g+1)^{e₂(J)}`. -/
theorem cut_bound_pairs {M : TM} {n b T : ℕ} (hobl : ObliviousOn M (matrixInputs n b) T)
    (hcorr : Transposes M n b) {w₀ : List Bool} (hw₀ : w₀ ∈ matrixInputs n b)
    {J : Finset ℕ} (hJ : ∀ τ ∈ J, τ < T) :
    2 ^ (b * (cutPairs M w₀ n b J).card) ≤
      (M.q + 1) ^ (entryPoints J).card * (M.g + 1) ^ (entryCells (workTraj M w₀) J).card :=
  Impl.cut_bound_pairs (M := M) (n := n) (b := b) (T := T) (hobl := hobl) (hcorr := hcorr) (w₀ := w₀) (hw₀ := hw₀) (J := J) (hJ := hJ)

/-- **Cut Lemma, bits form:** `b |S_J| ≤ e₁ ⌈log₂(q+1)⌉ + e₂ ⌈log₂(g+1)⌉`. -/
theorem cut_bound_bits {M : TM} {n b T : ℕ} (hobl : ObliviousOn M (matrixInputs n b) T)
    (hcorr : Transposes M n b) {w₀ : List Bool} (hw₀ : w₀ ∈ matrixInputs n b)
    {J : Finset ℕ} (hJ : ∀ τ ∈ J, τ < T) :
    b * (cutPairs M w₀ n b J).card ≤
      (entryPoints J).card * Nat.clog 2 (M.q + 1) +
        (entryCells (workTraj M w₀) J).card * Nat.clog 2 (M.g + 1) :=
  Impl.cut_bound_bits (M := M) (n := n) (b := b) (T := T) (hobl := hobl) (hcorr := hcorr) (w₀ := w₀) (hw₀ := hw₀) (J := J) (hJ := hJ)

/-! ## The Cut Lemma for families of step sets -/

/-- **Cut Lemma for families, product form.** This holds for any finite family of step sets
`J u ⊆ [0, T)`; they need not form a partition:
`2^{Σ_u |cutSet (J u)|} ≤ (q+1)^{Σ_u e₁(J u)} (g+1)^{Σ_u e₂(J u)}`. -/
theorem cut_bound_sum {M : TM} {n b T : ℕ} (hobl : ObliviousOn M (matrixInputs n b) T)
    (hcorr : Transposes M n b) {w₀ : List Bool} (hw₀ : w₀ ∈ matrixInputs n b)
    {ι : Type*} (s : Finset ι) (J : ι → Finset ℕ) (hJ : ∀ u ∈ s, ∀ τ ∈ J u, τ < T) :
    2 ^ (∑ u ∈ s, (cutSet M w₀ n b (J u)).card) ≤
      (M.q + 1) ^ (∑ u ∈ s, (entryPoints (J u)).card) *
        (M.g + 1) ^ (∑ u ∈ s, (entryCells (workTraj M w₀) (J u)).card) :=
  Impl.cut_bound_sum (M := M) (n := n) (b := b) (T := T) (hobl := hobl) (hcorr := hcorr) (w₀ := w₀) (hw₀ := hw₀) (ι := ι) (s := s) (J := J) (hJ := hJ)

/-- **Cut Lemma on a set of co-entropy `≤ m`** (robust form): if `M` is oblivious, with halting time
`T`, and correct only on a set `W` with `2^{n²b} ≤ 2^m |W|`, then
`2^{|cutSet J|} ≤ 2^m (q+1)^{e₁} (g+1)^{e₂}`. -/
theorem cut_bound_on_coentropy {M : TM} {n b T : ℕ} {W : Set (List Bool)} (hobl : ObliviousOn M W T)
    (hcorr : ∀ w ∈ W, ∃ A : Matrix, w = encode n b A ∧
      (run M w T).outRev.reverse = encode n b (transpose A))
    {w₀ : List Bool} (hw₀ : w₀ ∈ W) {J : Finset ℕ} (hJ : ∀ τ ∈ J, τ < T) {m : ℕ}
    (hco : 2 ^ (n * n * b) ≤ 2 ^ m * W.ncard) :
    2 ^ (cutSet M w₀ n b J).card ≤
      2 ^ m * ((M.q + 1) ^ (entryPoints J).card *
        (M.g + 1) ^ (entryCells (workTraj M w₀) J).card) :=
  Impl.cut_bound_on_coentropy hobl hcorr hw₀ hJ hco

/-- **Cut Lemma for families on a set of co-entropy `≤ m`** (robust form), for any finite family of
step sets `J u ⊆ [0, T)`: `2^{Σ_u |cutSet (J u)|} ≤ 2^{|s| m} (q+1)^{Σ_u e₁} (g+1)^{Σ_u e₂}`. -/
theorem cut_bound_sum_on {M : TM} {n b T : ℕ} {W : Set (List Bool)} (hobl : ObliviousOn M W T)
    (hcorr : ∀ w ∈ W, ∃ A : Matrix, w = encode n b A ∧
      (run M w T).outRev.reverse = encode n b (transpose A))
    {w₀ : List Bool} (hw₀ : w₀ ∈ W) {m : ℕ} (hco : 2 ^ (n * n * b) ≤ 2 ^ m * W.ncard)
    {ι : Type*} (s : Finset ι) (J : ι → Finset ℕ) (hJ : ∀ u ∈ s, ∀ τ ∈ J u, τ < T) :
    2 ^ (∑ u ∈ s, (cutSet M w₀ n b (J u)).card) ≤
      2 ^ (s.card * m) * ((M.q + 1) ^ (∑ u ∈ s, (entryPoints (J u)).card) *
        (M.g + 1) ^ (∑ u ∈ s, (entryCells (workTraj M w₀) (J u)).card)) :=
  Impl.cut_bound_sum_on hobl hcorr hw₀ hco s J hJ

/-- **Cut Lemma for families, bits form**, again for any finite family:
`Σ_u b |S_{J_u}| ≤ Σ_u (e₁(J_u) ⌈log₂(q+1)⌉ + e₂(J_u) ⌈log₂(g+1)⌉)`. -/
theorem cut_bound_sum_bits {M : TM} {n b T : ℕ} (hobl : ObliviousOn M (matrixInputs n b) T)
    (hcorr : Transposes M n b) {w₀ : List Bool} (hw₀ : w₀ ∈ matrixInputs n b)
    {ι : Type*} (s : Finset ι) (J : ι → Finset ℕ) (hJ : ∀ u ∈ s, ∀ τ ∈ J u, τ < T) :
    b * (∑ u ∈ s, (cutPairs M w₀ n b (J u)).card) ≤
      (∑ u ∈ s, (entryPoints (J u)).card) * Nat.clog 2 (M.q + 1) +
        (∑ u ∈ s, (entryCells (workTraj M w₀) (J u)).card) * Nat.clog 2 (M.g + 1) :=
  Impl.cut_bound_sum_bits (M := M) (n := n) (b := b) (T := T) (hobl := hobl) (hcorr := hcorr) (w₀ := w₀) (hw₀ := hw₀) (ι := ι) (s := s) (J := J) (hJ := hJ)

/-- **Cut Lemma for families, the left side.** If every part reads at most `ρ` rows, then
`Σ_u |S_{J_u}| ≥ (n - σ)(n - ρ)`. Here `n - σ` is the number of columns lying in `snk` of some
part. -/
theorem sum_cutPairs_ge (M : TM) (w₀ : List Bool) (n b : ℕ) {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (J : ι → Finset ℕ) (ρ : ℕ)
    (hρ : ∀ u ∈ s, (srcRows M w₀ n b (J u)).card ≤ ρ) :
    (s.biUnion (fun u => snkCols M w₀ n b (J u))).card * (n - ρ) ≤
      ∑ u ∈ s, (cutPairs M w₀ n b (J u)).card :=
  Impl.sum_cutPairs_ge (M := M) (w₀ := w₀) (n := n) (b := b) (ι := ι) (s := s) (J := J) (ρ := ρ) (hρ := hρ)

/-- **Cut Lemma for families, `σ ≤ M_b`.** Let the parts be the label classes of a labelling of the
steps `< T` by time intervals. Then the number `σ` of columns that do not lie in `snk` of a single
part is at most the number `M_b` of label changes, because the output is appended in column
order. The hypothesis `1 ≤ b` is needed: for `b = 0` and `n ≥ 1` the machine may halt at once
(`T = 0`) and the statement fails. -/
theorem uncovered_cols_le {M : TM} {n b T : ℕ} (hb : 1 ≤ b)
    (hobl : ObliviousOn M (matrixInputs n b) T)
    (hcorr : Transposes M n b) {w₀ : List Bool} (hw₀ : w₀ ∈ matrixInputs n b) (lab : ℕ → ℕ) :
    n - (((Finset.range T).image lab).biUnion (fun ℓ =>
        snkCols M w₀ n b ((Finset.range T).filter (fun τ => lab τ = ℓ)))).card ≤
      ((Finset.range T).filter (fun τ => 1 ≤ τ ∧ lab τ ≠ lab (τ - 1))).card :=
  Impl.uncovered_cols_le (M := M) (n := n) (b := b) (T := T) (hb := hb) (hobl := hobl) (hcorr := hcorr) (w₀ := w₀) (hw₀ := hw₀) (lab := lab)

/-- **Cut Lemma for families, `σ ≤ M_b`, for any run** with at least `n²b` output bits by time `T`:
no obliviousness, correctness or halting is needed. -/
theorem uncovered_cols_le_len {M : TM} {n b T : ℕ} (hb : 1 ≤ b) {w₀ : List Bool}
    (hlenT : n * n * b ≤ (run M w₀ T).outRev.length) (lab : ℕ → ℕ) :
    n - (((Finset.range T).image lab).biUnion (fun ℓ =>
        snkCols M w₀ n b ((Finset.range T).filter (fun τ => lab τ = ℓ)))).card ≤
      ((Finset.range T).filter (fun τ => 1 ≤ τ ∧ lab τ ≠ lab (τ - 1))).card :=
  Impl.uncovered_cols_le_len hb hlenT lab

/-! ## Blocks: the Residency Lemma, (V2), (P2), the Charging Lemma and (P1) -/

/-- Every head of the frozen model moves by at most one cell per step. -/
theorem unitSteps_inTraj (M : TM) (w : List Bool) : UnitSteps (inTraj M w) :=
  Impl.unitSteps_inTraj (M := M) (w := w)

theorem unitSteps_workTraj (M : TM) (w : List Bool) (t : Fin M.k) :
    UnitSteps (fun τ => workTraj M w τ t) :=
  Impl.unitSteps_workTraj (M := M) (w := w) (t := t)

section Blocks

variable {r : ℕ} {h : ℕ → ℤ}

/-- **(V2)** The head's block at the first steps of consecutive slots changes by at most one. -/
theorem slot_block_step (hh : UnitSteps h) (hr : 1 ≤ r) (y : ℕ) :
    |curBlock r h ((y + 1) * r) - curBlock r h (y * r)| ≤ 1 :=
  Impl.slot_block_step (hh := hh) (hr := hr) (y := y)

/-- **(V2), crossing form.** Take two slots and any block between the head's blocks at their
first steps. That block is the head's block at the first step of some slot `y` in between.
When `y r < T`, it is therefore resident at `y` under any admissible residency. -/
theorem exists_slot_block_eq (hh : UnitSteps h) (hr : 1 ≤ r) {y₁ y₂ : ℕ} (hy : y₁ ≤ y₂)
    {β : ℤ}
    (hβ : min (curBlock r h (y₁ * r)) (curBlock r h (y₂ * r)) ≤ β ∧
      β ≤ max (curBlock r h (y₁ * r)) (curBlock r h (y₂ * r))) :
    ∃ y, y₁ ≤ y ∧ y ≤ y₂ ∧ curBlock r h (y * r) = β :=
  Impl.exists_slot_block_eq (hh := hh) (hr := hr) (y₁ := y₁) (y₂ := y₂) (hy := hy) (β := β) (hβ := hβ)

/-- **Residency Lemma ((V1): three resident blocks).** The blocks resident at slot `y` lie within
`±1` of the head's block at the first step of `y`: `R_y ⊆ {β₀ - 1, β₀, β₀ + 1}`. -/
theorem pairRes_subset (hh : UnitSteps h) (hr : 1 ≤ r) (T y : ℕ) :
    pairRes r h T y ⊆
      {curBlock r h (y * r) - 1, curBlock r h (y * r), curBlock r h (y * r) + 1} :=
  Impl.pairRes_subset (hh := hh) (hr := hr) (T := T) (y := y)

/-- Residency Lemma, packaged: pair residency is admissible with constant `3`. -/
theorem pairRes_admissible (hh : UnitSteps h) (hr : 1 ≤ r) (T : ℕ) :
    AdmissibleRes r h T (pairRes r h T) 3 :=
  Impl.pairRes_admissible (hh := hh) (hr := hr) (T := T)

/-- Touched residency is admissible with constant `2`, and its blocks lie within `±1` of the
head's block at the first step of the slot. -/
theorem touchRes_admissible (hh : UnitSteps h) (hr : 1 ≤ r) (T : ℕ) :
    AdmissibleRes r h T (touchRes r h T) 2 ∧
      ∀ y, touchRes r h T y ⊆
        {curBlock r h (y * r) - 1, curBlock r h (y * r), curBlock r h (y * r) + 1} :=
  Impl.touchRes_admissible (hh := hh) (hr := hr) (T := T)

/-- **Pair changes are at least `r` steps apart** (the core of (P2)). -/
theorem pairChange_spacing (hh : UnitSteps h) (hr : 1 ≤ r) {σ₁ σ₂ : ℕ}
    (h₁ : PairChange r h σ₁) (h₂ : PairChange r h σ₂) (hlt : σ₁ < σ₂) : σ₁ + r ≤ σ₂ :=
  Impl.pairChange_spacing (hh := hh) (hr := hr) (h₁ := h₁) (h₂ := h₂) (hlt := hlt)

/-- **(P2)** At most one visit begins at each slot `y + 1` (pair residency). -/
theorem pairRes_begin_unique (hh : UnitSteps h) (hr : 1 ≤ r) (T y : ℕ) {β β' : ℤ}
    (h₁ : β ∈ pairRes r h T (y + 1)) (h₁' : β ∉ pairRes r h T y)
    (h₂ : β' ∈ pairRes r h T (y + 1)) (h₂' : β' ∉ pairRes r h T y) : β = β' :=
  Impl.pairRes_begin_unique (hh := hh) (hr := hr) (T := T) (y := y) (β := β) (β' := β') (h₁ := h₁) (h₁' := h₁') (h₂ := h₂) (h₂' := h₂')

/-- **(P2)** At most one visit ends at each slot `y` that is followed by a nonempty slot (pair
residency). -/
theorem pairRes_end_unique (hh : UnitSteps h) (hr : 1 ≤ r) {T : ℕ} (y : ℕ)
    (hy : (y + 1) * r < T) {β β' : ℤ}
    (h₁ : β ∈ pairRes r h T y) (h₁' : β ∉ pairRes r h T (y + 1))
    (h₂ : β' ∈ pairRes r h T y) (h₂' : β' ∉ pairRes r h T (y + 1)) : β = β' :=
  Impl.pairRes_end_unique (hh := hh) (hr := hr) (T := T) (y := y) (hy := hy) (β := β) (β' := β') (h₁ := h₁) (h₁' := h₁') (h₂ := h₂) (h₂' := h₂')

/-- **(P2)** Each slot is the source of at most one chord (pair residency). -/
theorem pairRes_chord_source_unique (hh : UnitSteps h) (hr : 1 ≤ r) (T : ℕ) {β β' : ℤ}
    {x z z' : ℕ} (he : IsChord (pairRes r h T) β x z) (he' : IsChord (pairRes r h T) β' x z') :
    β = β' ∧ z = z' :=
  Impl.pairRes_chord_source_unique (hh := hh) (hr := hr) (T := T) (β := β) (β' := β') (x := x) (z := z) (z' := z') (he := he) (he' := he')

/-- **(P2)** Each slot is the target of at most one chord (pair residency). -/
theorem pairRes_chord_target_unique (hh : UnitSteps h) (hr : 1 ≤ r) (T : ℕ) {β β' : ℤ}
    {x x' z : ℕ} (he : IsChord (pairRes r h T) β x z) (he' : IsChord (pairRes r h T) β' x' z) :
    β = β' ∧ x = x' :=
  Impl.pairRes_chord_target_unique (hh := hh) (hr := hr) (T := T) (β := β) (β' := β') (x := x) (x' := x') (z := z) (he := he) (he' := he')

/-- **(P2)** for touched residency: at most one visit begins at each slot `y + 1`. -/
theorem touchRes_begin_unique (hh : UnitSteps h) (hr : 1 ≤ r) (T y : ℕ) {β β' : ℤ}
    (h₁ : β ∈ touchRes r h T (y + 1)) (h₁' : β ∉ touchRes r h T y)
    (h₂ : β' ∈ touchRes r h T (y + 1)) (h₂' : β' ∉ touchRes r h T y) : β = β' :=
  Impl.touchRes_begin_unique (hh := hh) (hr := hr) (T := T) (y := y) (β := β) (β' := β') (h₁ := h₁) (h₁' := h₁') (h₂ := h₂) (h₂' := h₂')

/-- **(P2)** for touched residency: at most one visit ends at each slot followed by a nonempty
slot. -/
theorem touchRes_end_unique (hh : UnitSteps h) (hr : 1 ≤ r) {T : ℕ} (y : ℕ)
    (hy : (y + 1) * r < T) {β β' : ℤ}
    (h₁ : β ∈ touchRes r h T y) (h₁' : β ∉ touchRes r h T (y + 1))
    (h₂ : β' ∈ touchRes r h T y) (h₂' : β' ∉ touchRes r h T (y + 1)) : β = β' :=
  Impl.touchRes_end_unique (hh := hh) (hr := hr) (T := T) (y := y) (hy := hy) (β := β) (β' := β') (h₁ := h₁) (h₁' := h₁') (h₂ := h₂) (h₂' := h₂')

/-- **(P2)** for touched residency: each slot is the source of at most one chord. -/
theorem touchRes_chord_source_unique (hh : UnitSteps h) (hr : 1 ≤ r) (T : ℕ) {β β' : ℤ}
    {x z z' : ℕ} (he : IsChord (touchRes r h T) β x z)
    (he' : IsChord (touchRes r h T) β' x z') : β = β' ∧ z = z' :=
  Impl.touchRes_chord_source_unique (hh := hh) (hr := hr) (T := T) (β := β) (β' := β') (x := x) (z := z) (z' := z') (he := he) (he' := he')

/-- **(P2)** for touched residency: each slot is the target of at most one chord. -/
theorem touchRes_chord_target_unique (hh : UnitSteps h) (hr : 1 ≤ r) (T : ℕ) {β β' : ℤ}
    {x x' z : ℕ} (he : IsChord (touchRes r h T) β x z)
    (he' : IsChord (touchRes r h T) β' x' z) : β = β' ∧ x = x' :=
  Impl.touchRes_chord_target_unique (hh := hh) (hr := hr) (T := T) (β := β) (β' := β') (x := x) (x' := x') (z := z) (he := he) (he' := he')

/-- **Charging Lemma, for one tape and any admissible residency.** The external reads of
the union of the slots of `U` number at most `r · (χ + c · μ)`. Here `χ` is the number of chords
entering `U` and `μ` the number of memory boundaries of `U`. -/
theorem entryTimes_card_le (hr : 1 ≤ r) {T c : ℕ} {R : ℕ → Finset ℤ}
    (hR : AdmissibleRes r h T R c) (U : Set ℕ) :
    (entryTimes r h U T).card ≤
      r * ((chordsInto R U (numSlots r T)).card + c * (memBoundaries U (numSlots r T)).card) :=
  Impl.entryTimes_card_le (hr := hr) (T := T) (c := c) (R := R) (hR := hR) (U := U)

/-- **The charging step, containment form.** Every external read at time `τ` of the union of the
slots of `U`, on block `β = cur_τ`, is charged to an event entering `U` no later than its slot. The
event is either:
* a memory boundary `z` of `U` with `β` resident at slots `z - 1` and `z` (it rides on the memory
  edge), or
* a chord of `β` entering `U` at slot `z`.

A chord can enter `U` at any slot of `U`, not only at a memory boundary, so charging only the
visits that start at a memory boundary of `U` would not suffice. Moreover, the read's last write
lies in a slot strictly before `z`, so the read's content is carried into `U` by that memory edge or
chord. -/
theorem entryTimes_charged (hr : 1 ≤ r) {T c : ℕ} {R : ℕ → Finset ℤ}
    (hR : AdmissibleRes r h T R c) (U : Set ℕ) {τ : ℕ} (hτ : τ ∈ entryTimes r h U T) :
    ∃ z, z ≤ τ / r ∧ (∀ σ, IsLastVisit h τ σ → σ / r < z) ∧
      ((z ∈ memBoundaries U (numSlots r T) ∧ curBlock r h τ ∈ R z ∧
          curBlock r h τ ∈ R (z - 1)) ∨
        (z, curBlock r h τ) ∈ chordsInto R U (numSlots r T)) :=
  Impl.entryTimes_charged (hr := hr) (T := T) (c := c) (R := R) (hR := hR) (U := U) (τ := τ) (hτ := hτ)

end Blocks

/-- The external reads of a union of slots, over all tapes: `e₂(J) = Σ_t e₂ᵗ(J)`. -/
theorem entryCells_slotSteps_card (M : TM) (w : List Bool) (r : ℕ) (U : Set ℕ) (T : ℕ) :
    (entryCells (workTraj M w) (slotSteps r U T)).card =
      ∑ t : Fin M.k, (entryTimes r (fun τ => workTraj M w τ t) U T).card :=
  Impl.entryCells_slotSteps_card (M := M) (w := w) (r := r) (U := U) (T := T)

/-- **Charging Lemma, `e₁(J) = μ(J)`.** The entry points of a union of slots are exactly the first
steps of its memory-boundary slots. -/
theorem entryPoints_slotSteps_card {r : ℕ} (hr : 1 ≤ r) (U : Set ℕ) (T : ℕ) :
    (entryPoints (slotSteps r U T)).card = (memBoundaries U (numSlots r T)).card :=
  Impl.entryPoints_slotSteps_card (r := r) (hr := hr) (U := U) (T := T)

/-- **Charging Lemma, any admissible residency:** `e₂(J) ≤ r χ(J) + c k r μ(J)`. Here `J` is the
union of the slots of `U`, the residencies `R t` are admissible with constant `c`, and `χ(J)` counts
their chords entering `J`. With pair residency (`R t = pairRes …`, `c = 3`, by
`pairRes_admissible`) this is `e₂ ≤ r χ + 3 k r μ`. -/
theorem charging_bound (M : TM) (w : List Bool) {r : ℕ} (hr : 1 ≤ r) {T c : ℕ}
    (R : Fin M.k → ℕ → Finset ℤ) (hR : ∀ t, AdmissibleRes r (fun τ => workTraj M w τ t) T (R t) c)
    (U : Set ℕ) :
    (entryCells (workTraj M w) (slotSteps r U T)).card ≤
      r * (∑ t : Fin M.k, (chordsInto (R t) U (numSlots r T)).card) +
      c * M.k * r * (memBoundaries U (numSlots r T)).card :=
  Impl.charging_bound M w hr R hR U

open Classical in
/-- **(P1), multi-homed rows.** If `r ≤ n b`, each slot reads at most two rows. So a union of
slots reads at most twice as many rows as it has slots. -/
theorem srcRows_slotSteps_card_le (M : TM) (w₀ : List Bool) {n b r : ℕ} (hr : 1 ≤ r)
    (hrnb : r ≤ n * b) (U : Set ℕ) (T : ℕ) :
    (srcRows M w₀ n b (slotSteps r U T)).card ≤
      2 * ((Finset.range (numSlots r T)).filter (· ∈ U)).card :=
  Impl.srcRows_slotSteps_card_le (M := M) (w₀ := w₀) (n := n) (b := b) (r := r) (hr := hr) (hrnb := hrnb) (U := U) (T := T)

/-! ## The Slot Cut Bound and Discrete Isoperimetry -/

/-- **Slot Cut Bound.** For every union of slots `J`:
`b |S_J| ≤ μ(J) ⌈log₂(q+1)⌉ + r G (χ(J) + 3 k μ(J))`, where `G = ⌈log₂(g+1)⌉`. -/
theorem slot_cut_bound {M : TM} {n b T r : ℕ} (hobl : ObliviousOn M (matrixInputs n b) T)
    (hcorr : Transposes M n b) {w₀ : List Bool} (hw₀ : w₀ ∈ matrixInputs n b) (hr : 1 ≤ r)
    (U : Set ℕ) :
    b * (cutPairs M w₀ n b (slotSteps r U T)).card ≤
      (memBoundaries U (numSlots r T)).card * Nat.clog 2 (M.q + 1) +
        r * Nat.clog 2 (M.g + 1) *
          ((∑ t : Fin M.k,
            (chordsInto (pairRes r (fun τ => workTraj M w₀ τ t) T) U (numSlots r T)).card) +
            3 * M.k * (memBoundaries U (numSlots r T)).card) :=
  Impl.slot_cut_bound (M := M) (n := n) (b := b) (T := T) (r := r) (hobl := hobl) (hcorr := hcorr) (w₀ := w₀) (hw₀ := hw₀) (hr := hr) (U := U)

/-- **Slot Cut Bound, partition form (with `M_b`), any admissible residency.** The parts are the
label classes of a slot labelling, and the residencies `R t` are admissible with constant `c`. Then

  `Σ_u b |S_{J_u}| ≤ M_b (⌈log₂(q+1)⌉ + c k r G) + r G χ_cross`,

where `M_b` is the number of label changes, `χ_cross` the number of chords of the `R t` joining
different labels, and `G = ⌈log₂(g+1)⌉`. With pair residency (`c = 3`, `pairRes_admissible`) this
gives the bound with `M_b`, which is stronger than the form with `M_b + 1` in place of `M_b`. -/
theorem slot_cut_bound_partition {M : TM} {n b T r c : ℕ}
    (hobl : ObliviousOn M (matrixInputs n b) T) (hcorr : Transposes M n b) {w₀ : List Bool}
    (hw₀ : w₀ ∈ matrixInputs n b) (hr : 1 ≤ r)
    (R : Fin M.k → ℕ → Finset ℤ) (hR : ∀ t, AdmissibleRes r (fun τ => workTraj M w₀ τ t) T (R t) c)
    (lab : ℕ → ℕ) :
    b * (∑ ℓ ∈ (Finset.range (numSlots r T)).image lab,
        (cutPairs M w₀ n b (labelPart r lab T ℓ)).card) ≤
      labelChanges lab (numSlots r T) *
          (Nat.clog 2 (M.q + 1) + c * M.k * r * Nat.clog 2 (M.g + 1)) +
        r * Nat.clog 2 (M.g + 1) * ∑ t : Fin M.k, (crossChords (R t) lab (numSlots r T)).card :=
  Impl.slot_cut_bound_partition hobl hcorr hw₀ hr R hR lab

/-- **Slot Cut Bound, `σ ≤ M_b` for slot labellings.** The columns that do not lie in `snk` of a
single part number at most the label changes. -/
theorem uncovered_cols_le_slots {M : TM} {n b T r : ℕ} (hb : 1 ≤ b)
    (hobl : ObliviousOn M (matrixInputs n b) T) (hcorr : Transposes M n b) {w₀ : List Bool}
    (hw₀ : w₀ ∈ matrixInputs n b) (hr : 1 ≤ r) (lab : ℕ → ℕ) :
    n - (((Finset.range (numSlots r T)).image lab).biUnion (fun ℓ =>
        snkCols M w₀ n b (labelPart r lab T ℓ))).card ≤ labelChanges lab (numSlots r T) :=
  Impl.uncovered_cols_le_slots (M := M) (n := n) (b := b) (T := T) (r := r) (hb := hb) (hobl := hobl) (hcorr := hcorr) (w₀ := w₀) (hw₀ := hw₀) (hr := hr) (lab := lab)

/-- **Slot Cut Bound, `σ ≤ M_b` for slot labellings, for any run** with at least `n²b` output bits
by time `T`. -/
theorem uncovered_cols_le_slots_len {M : TM} {n b T r : ℕ} (hb : 1 ≤ b) {w₀ : List Bool}
    (hlenT : n * n * b ≤ (run M w₀ T).outRev.length) (hr : 1 ≤ r) (lab : ℕ → ℕ) :
    n - (((Finset.range (numSlots r T)).image lab).biUnion (fun ℓ =>
        snkCols M w₀ n b (labelPart r lab T ℓ))).card ≤ labelChanges lab (numSlots r T) :=
  Impl.uncovered_cols_le_slots_len hb hlenT hr lab

/-- **Discrete Isoperimetry (finitary, block form) for any admissible residency.**

Setting:
* an oblivious machine that transposes `n × n` matrices with `b`-bit entries in time `T`;
* slots of length `r` with `1 ≤ r ≤ n b`;
* admissible residencies `R t` (constant `c`) for the work tapes;
* a labelling of the `N = ⌈T/r⌉` slots, every label class having at most `m` slots.

Then

  `2^{(n - M_b)(n - 2m) b} ≤ (q+1)^{M_b} · (g+1)^{r (c k M_b + χ_cross)}`,

where `M_b` is the number of label changes and `χ_cross` the number of chords (over all work
tapes) joining different labels. -/
theorem isoperimetry_res {M : TM} {n b T r c : ℕ}
    (hobl : ObliviousOn M (matrixInputs n b) T) (hcorr : Transposes M n b) {w₀ : List Bool}
    (hw₀ : w₀ ∈ matrixInputs n b) (hr : 1 ≤ r) (hrnb : r ≤ n * b)
    (R : Fin M.k → ℕ → Finset ℤ) (hR : ∀ t, AdmissibleRes r (fun τ => workTraj M w₀ τ t) T (R t) c)
    (lab : ℕ → ℕ) (m : ℕ)
    (hm : ∀ ℓ, ((Finset.range (numSlots r T)).filter (fun y => lab y = ℓ)).card ≤ m) :
    2 ^ ((n - labelChanges lab (numSlots r T)) * (n - 2 * m) * b) ≤
      (M.q + 1) ^ labelChanges lab (numSlots r T) *
        (M.g + 1) ^ (r * (c * M.k * labelChanges lab (numSlots r T) +
          ∑ t : Fin M.k, (crossChords (R t) lab (numSlots r T)).card)) :=
  Impl.isoperimetry_res (M := M) (n := n) (b := b) (T := T) (r := r) (c := c) (hobl := hobl) (hcorr := hcorr) (w₀ := w₀) (hw₀ := hw₀) (hr := hr) (hrnb := hrnb) (R := R) (hR := hR) (lab := lab) (m := m) (hm := hm)

/-- **Discrete Isoperimetry on a set of co-entropy `≤ mc`** (finitary, robust form). Let `M` be
oblivious (time `T`) and correct only on a set `W` with `2^{n²b} ≤ 2^{mc} |W|`. Then, with the
notation of `isoperimetry_res`,

  `2^{(n - M_b)(n - 2m) b} ≤ 2^{(M_b + 1) mc} · (q+1)^{M_b} · (g+1)^{r (c k M_b + χ_cross)}`:

each of the at most `M_b + 1` label classes pays `mc`. Unlike the trace-class form
(`isoperimetry_trace_on`) there is no head-position term. With `W` all matrix inputs and
`mc = 0` this is `isoperimetry_res`. -/
theorem isoperimetry_res_on {M : TM} {n b T r c : ℕ} {W : Set (List Bool)}
    (hobl : ObliviousOn M W T)
    (hcorr : ∀ w ∈ W, ∃ A : Matrix, w = encode n b A ∧
      (run M w T).outRev.reverse = encode n b (transpose A))
    {w₀ : List Bool} (hw₀ : w₀ ∈ W) {mc : ℕ} (hco : 2 ^ (n * n * b) ≤ 2 ^ mc * W.ncard)
    (hr : 1 ≤ r) (hrnb : r ≤ n * b)
    (R : Fin M.k → ℕ → Finset ℤ) (hR : ∀ t, AdmissibleRes r (fun τ => workTraj M w₀ τ t) T (R t) c)
    (lab : ℕ → ℕ) (m : ℕ)
    (hm : ∀ ℓ, ((Finset.range (numSlots r T)).filter (fun y => lab y = ℓ)).card ≤ m) :
    2 ^ ((n - labelChanges lab (numSlots r T)) * (n - 2 * m) * b) ≤
      2 ^ ((labelChanges lab (numSlots r T) + 1) * mc) *
      ((M.q + 1) ^ labelChanges lab (numSlots r T) *
        (M.g + 1) ^ (r * (c * M.k * labelChanges lab (numSlots r T) +
          ∑ t : Fin M.k, (crossChords (R t) lab (numSlots r T)).card))) :=
  Impl.isoperimetry_res_on hobl hcorr hw₀ hco hr hrnb R hR lab m hm

/-- **Discrete Isoperimetry (finitary), pair residency (`c = 3`).** -/
theorem isoperimetry {M : TM} {n b T r : ℕ} (hobl : ObliviousOn M (matrixInputs n b) T)
    (hcorr : Transposes M n b) {w₀ : List Bool} (hw₀ : w₀ ∈ matrixInputs n b)
    (hr : 1 ≤ r) (hrnb : r ≤ n * b) (lab : ℕ → ℕ) (m : ℕ)
    (hm : ∀ ℓ, ((Finset.range (numSlots r T)).filter (fun y => lab y = ℓ)).card ≤ m) :
    2 ^ ((n - labelChanges lab (numSlots r T)) * (n - 2 * m) * b) ≤
      (M.q + 1) ^ labelChanges lab (numSlots r T) *
        (M.g + 1) ^ (r * (3 * M.k * labelChanges lab (numSlots r T) +
          ∑ t : Fin M.k,
            (crossChords (pairRes r (fun τ => workTraj M w₀ τ t) T) lab (numSlots r T)).card)) :=
  Impl.isoperimetry (M := M) (n := n) (b := b) (T := T) (r := r) (hobl := hobl) (hcorr := hcorr) (w₀ := w₀) (hw₀ := hw₀) (hr := hr) (hrnb := hrnb) (lab := lab) (m := m) (hm := hm)

/-- **Discrete Isoperimetry (finitary), touched residency (`c = 2`).** -/
theorem isoperimetry_touch {M : TM} {n b T r : ℕ}
    (hobl : ObliviousOn M (matrixInputs n b) T)
    (hcorr : Transposes M n b) {w₀ : List Bool} (hw₀ : w₀ ∈ matrixInputs n b)
    (hr : 1 ≤ r) (hrnb : r ≤ n * b) (lab : ℕ → ℕ) (m : ℕ)
    (hm : ∀ ℓ, ((Finset.range (numSlots r T)).filter (fun y => lab y = ℓ)).card ≤ m) :
    2 ^ ((n - labelChanges lab (numSlots r T)) * (n - 2 * m) * b) ≤
      (M.q + 1) ^ labelChanges lab (numSlots r T) *
        (M.g + 1) ^ (r * (2 * M.k * labelChanges lab (numSlots r T) +
          ∑ t : Fin M.k,
            (crossChords (touchRes r (fun τ => workTraj M w₀ τ t) T) lab (numSlots r T)).card)) :=
  Impl.isoperimetry_touch (M := M) (n := n) (b := b) (T := T) (r := r) (hobl := hobl) (hcorr := hcorr) (w₀ := w₀) (hw₀ := hw₀) (hr := hr) (hrnb := hrnb) (lab := lab) (m := m) (hm := hm)


/-! # Theorem P: passes of oblivious transposers

A pass is a time interval in which every head (input and work heads) moves monotonically. An
oblivious transposer (heads and output schedule) whose run splits into `r` passes satisfies
`n²b ≤ 𝓗 · n (2b + σ)` (`theoremP_bits`), where `𝓗 = Σ_{i<r} (k+1)^i` bounds the number of
addresses of a dependency forest and `σ = ⌈log₂(q+1)⌉ + k ⌈log₂(g+1)⌉`. Definitions are in
`DefsP.lean`.

* Passes: `greedy_passPartition`, `greedyPasses_le` (the greedy count is optimal) and
  `passPartition_iff`; on an oblivious class they do not depend on the input
  (`passPartition_indep`, `greedyPasses_indep`).
* The Fresh-Cell Lemma: `pass_fresh`.
* Addresses: `card_addresses_le`, `addrCount_mul`.
* The Forest Lemma, in entry-data form: `forest_subset`, the containments
  `forest_entryPoints_subset` and `forest_entryCells_subset`, and the counts
  `forest_entryPoints_card_le` and `forest_entryCells_card_le`. By the Locality Lemma
  (`locality_function`), a segment's output is a function of the forest's entry data and of the
  input bits it reads.
* The information count: `forest_info`.
* The Disjointness Lemma: `forestNode_disjoint`, with its input part `read_chain`.
* The coverage count: `coverage_per_address` and `coverage_grouped`.
* Theorem P: `theoremP` (log-free), `theoremP_bits`, `theoremP_bits_add_one` (the bits form with
  `+1`), `theoremP_div`, `theoremP_pow` and `theoremP_greedy`.
* Theorem P_γ (groups of `γ` columns) in the frozen model: `theoremP_grouped`,
  `theoremP_grouped_bits`.
* Non-vacuity: `theoremP_hyps_tr2` (`k = 0`) and `theoremP_hyps_tr2k` (`k = 1`).
-/

/-- The greedy passes form a pass partition, with `greedyPasses` passes. -/
theorem greedy_passPartition (M : TM) (w : List Bool) (T : ℕ) :
    PassPartition M w T (greedyPasses M w T) (greedyBound M w T) :=
  Impl.greedy_passPartition M w T

/-- **The greedy partition is optimal:** every pass partition has at least `greedyPasses` passes. -/
theorem greedyPasses_le {M : TM} {w : List Bool} {T r : ℕ} {p : ℕ → ℕ}
    (hp : PassPartition M w T r p) : greedyPasses M w T ≤ r :=
  Impl.greedyPasses_le hp

/-- A pass partition with `r` passes exists exactly when the greedy count is at most `r` (pad with
empty passes). -/
theorem passPartition_iff (M : TM) (w : List Bool) (T r : ℕ) :
    (∃ p, PassPartition M w T r p) ↔ greedyPasses M w T ≤ r :=
  Impl.passPartition_iff M w T r

/-- On an oblivious class the pass partitions are those of the common trajectory: they do not
depend on the input. -/
theorem passPartition_indep {M : TM} {W : Set (List Bool)} {T r : ℕ} (hobl : ObliviousOn M W T)
    {w w' : List Bool} (hw : w ∈ W) (hw' : w' ∈ W) (p : ℕ → ℕ) :
    PassPartition M w T r p ↔ PassPartition M w' T r p :=
  Impl.passPartition_indep hobl hw hw' p

/-- On an oblivious class the greedy pass count does not depend on the input. -/
theorem greedyPasses_indep {M : TM} {W : Set (List Bool)} {T : ℕ} (hobl : ObliviousOn M W T)
    {w w' : List Bool} (hw : w ∈ W) (hw' : w' ∈ W) :
    greedyPasses M w T = greedyPasses M w' T :=
  Impl.greedyPasses_indep hobl hw hw'

/-- `k 𝓗 + 1 = (k+1)^r`, i.e. `𝓗 = ((k+1)^r - 1)/k`. -/
theorem addrCount_mul (k r : ℕ) : k * addrCount k r + 1 = (k + 1) ^ r :=
  Impl.addrCount_mul k r

/-- There are at most `𝓗` addresses. -/
theorem card_addresses_le (k r : ℕ) : (addresses k r).card ≤ addrCount k r :=
  Impl.card_addresses_le k r

/-- **Fresh-Cell Lemma (where accessed cells come from).** Let a head be monotone on the pass
`[s, e)`. A cell occupied at a time `τ ∈ [a, e]` that differs from the cell under the head at `a`
was not visited at any step `ρ ∈ [s, a)` of the pass. -/
theorem pass_fresh {h : ℕ → ℤ} {s e a τ ρ : ℕ} (hmono : MonoOn h s e) (hsρ : s ≤ ρ) (hρa : ρ < a)
    (haτ : a ≤ τ) (hτe : τ ≤ e) (hne : h τ ≠ h a) : h ρ ≠ h τ :=
  Impl.pass_fresh hmono hsρ hρa haτ hτe hne

/-- The forest of a segment consists of steps `< T`. -/
theorem forest_subset {M : TM} {w : List Bool} {T r : ℕ} {p : ℕ → ℕ}
    (hp : PassPartition M w T r p) (o₁ o₂ : ℕ) : ∀ τ ∈ forest M w p r o₁ o₂, τ < T :=
  Impl.forest_subset hp o₁ o₂

/-- **Forest Lemma, containment form (entry points).** Every entry point of the forest is the first
step of one of its nodes. -/
theorem forest_entryPoints_subset {M : TM} {w : List Bool} {T r : ℕ} {p : ℕ → ℕ}
    (hp : PassPartition M w T r p) (o₁ o₂ : ℕ) :
    entryPoints (forest M w p r o₁ o₂) ⊆
      (addresses M.k r).image (fun α => firstStep (forestNode M w p o₁ o₂ α.1 α.2)) :=
  Impl.forest_entryPoints_subset hp o₁ o₂

/-- **Forest Lemma, containment form (entry cells).** Every external read of the forest is a read,
at the first step of a node, of the cell under a work head. With `forest_entryPoints_subset`: the
entry data of the forest consist, per node, of at most the state and the `k` head cells at the
node's first step `τ_a`. -/
theorem forest_entryCells_subset {M : TM} {w : List Bool} {T r : ℕ} {p : ℕ → ℕ}
    (hp : PassPartition M w T r p) (o₁ o₂ : ℕ) :
    entryCells (workTraj M w) (forest M w p r o₁ o₂) ⊆
      (Finset.univ ×ˢ addresses M.k r).image
        (fun x => (x.1, firstStep (forestNode M w p o₁ o₂ x.2.1 x.2.2))) :=
  Impl.forest_entryCells_subset hp o₁ o₂

/-- **Forest Lemma, entry-data form (entry points).** The forest of a segment has at most one entry
point per address. -/
theorem forest_entryPoints_card_le {M : TM} {w : List Bool} {T r : ℕ} {p : ℕ → ℕ}
    (hp : PassPartition M w T r p) (o₁ o₂ : ℕ) :
    (entryPoints (forest M w p r o₁ o₂)).card ≤ (addresses M.k r).card :=
  Impl.forest_entryPoints_card_le hp o₁ o₂

/-- **Forest Lemma, entry-data form (entry cells).** Every external read of the forest is a read, at
a node's first step, of the cell under one of the `k` work heads. So the forest has at most
`k · #addresses` entry cells. This is where the Fresh-Cell Lemma and the hull children enter. -/
theorem forest_entryCells_card_le {M : TM} {w : List Bool} {T r : ℕ} {p : ℕ → ℕ}
    (hp : PassPartition M w T r p) (o₁ o₂ : ℕ) :
    (entryCells (workTraj M w) (forest M w p r o₁ o₂)).card ≤ M.k * (addresses M.k r).card :=
  Impl.forest_entryCells_card_le hp o₁ o₂

/-- **Information count for one segment** (the Forest Lemma together with the Cut Lemma). Take an
oblivious transposer and any output segment `[o₁, o₂)` (the comb contains only input bits whose
transposed copy lies below `n²b`, so `o₂` is arbitrary). Then the segment's comb bits that its
forest does not read number at most `log₂((q+1)(g+1)^k)` per address:
`2^{|comb ∖ U|} ≤ ((q+1)(g+1)^k)^{#addresses}`. -/
theorem forest_info {M : TM} {n b T r : ℕ} (hobl : ObliviousOn M (matrixInputs n b) T)
    (hcorr : Transposes M n b) {w₀ : List Bool} (hw₀ : w₀ ∈ matrixInputs n b) {p : ℕ → ℕ}
    (hp : PassPartition M w₀ T r p) {o₁ o₂ : ℕ} :
    2 ^ (combSet n b o₁ o₂ \ readSet (inTraj M w₀) (n * n * b) (forest M w₀ p r o₁ o₂)).card ≤
      ((M.q + 1) * (M.g + 1) ^ M.k) ^ (addresses M.k r).card :=
  Impl.forest_info hobl hcorr hw₀ hp

/-- **Disjointness Lemma.** At a fixed address, the nodes of two disjoint output segments
(the first ending before the second starts) are disjoint step sets. -/
theorem forestNode_disjoint {M : TM} {w : List Bool} {T r : ℕ} {p : ℕ → ℕ}
    (hp : PassPartition M w T r p) {α : ℕ × List (ℕ × Fin M.k)} (hα : α ∈ addresses M.k r)
    {o₁ o₂ o₁' o₂' : ℕ} (h : o₂ ≤ o₁') :
    Disjoint (forestNode M w p o₁ o₂ α.1 α.2) (forestNode M w p o₁' o₂' α.1 α.2) :=
  Impl.forestNode_disjoint hp hα h

/-- **Disjointness Lemma, input part (the time-ordered chain).** At a fixed address, take the nodes
of pairwise disjoint output segments. Their input read sets (in `[0, L)`) satisfy
`Σ_s |I_s| ≤ L + (#segments) - 1`: ordered in time, each meets the union of the earlier ones in at
most one position. -/
theorem read_chain {M : TM} {w : List Bool} {T r L : ℕ} {p : ℕ → ℕ}
    (hp : PassPartition M w T r p) {α : ℕ × List (ℕ × Fin M.k)} (hα : α ∈ addresses M.k r)
    {ι : Type*} (S : Finset ι) (hS : S.Nonempty) (o₁ o₂ : ι → ℕ)
    (hdisj : ∀ s ∈ S, ∀ s' ∈ S, s ≠ s' → o₂ s ≤ o₁ s' ∨ o₂ s' ≤ o₁ s) :
    ∑ s ∈ S, (readSet (inTraj M w) L (forestNode M w p (o₁ s) (o₂ s) α.1 α.2)).card + 1 ≤
      L + S.card :=
  Impl.read_chain hp hα S hS o₁ o₂ hdisj

/-- **Coverage per address (groups of `γ` columns).** At a fixed address, the comb bits read by
the `⌈n/γ⌉` group nodes number at most `(γ+1) n b` (for `γ = 0` there are no groups). -/
theorem coverage_per_address {M : TM} {w : List Bool} {n b T r γ : ℕ} {p : ℕ → ℕ}
    (hp : PassPartition M w T r p) {α : ℕ × List (ℕ × Fin M.k)}
    (hα : α ∈ addresses M.k r) :
    ∑ s ∈ Finset.range (numGroups n γ),
      (combSet n b (segLo n b γ s) (segHi n b γ s) ∩
        readSet (inTraj M w) (n * n * b)
          (forestNode M w p (segLo n b γ s) (segHi n b γ s) α.1 α.2)).card ≤
      (γ + 1) * n * b :=
  Impl.coverage_per_address hp hα

/-- **Coverage count (groups of `γ` columns).** Over the `⌈n/γ⌉` groups, the comb bits read by the
group forests number at most `(γ+1) n b` per address. For `γ = 1` (columns) this is `2 n b` per
address (sharper than `2 n b + 1`). -/
theorem coverage_grouped {M : TM} {w : List Bool} {n b T r γ : ℕ} {p : ℕ → ℕ}
    (hp : PassPartition M w T r p) :
    ∑ s ∈ Finset.range (numGroups n γ),
      (combSet n b (segLo n b γ s) (segHi n b γ s) ∩
        readSet (inTraj M w) (n * n * b) (forest M w p r (segLo n b γ s) (segHi n b γ s))).card ≤
      (addresses M.k r).card * ((γ + 1) * n * b) :=
  Impl.coverage_grouped hp

/-- **Theorem P_γ (grouped columns; frozen model), log-free.** Let `M` be
oblivious (heads and output schedule) and transpose `n × n` matrices with `b`-bit entries using `r`
passes. Then for every `γ ≥ 1`

  `2^{n²b} ≤ 2^{𝓗 (γ+1) n b} · ((q+1)(g+1)^k)^{⌈n/γ⌉ 𝓗}`,

where `𝓗 = Σ_{i<r} (k+1)^i`. -/
theorem theoremP_grouped {M : TM} {n b T r γ : ℕ} (hobl : ObliviousOn M (matrixInputs n b) T)
    (hcorr : Transposes M n b) {w₀ : List Bool} (hw₀ : w₀ ∈ matrixInputs n b) {p : ℕ → ℕ}
    (hp : PassPartition M w₀ T r p) (hγ : 1 ≤ γ) :
    2 ^ (n * n * b) ≤
      2 ^ (addrCount M.k r * ((γ + 1) * n * b)) *
        ((M.q + 1) * (M.g + 1) ^ M.k) ^ (numGroups n γ * addrCount M.k r) :=
  Impl.theoremP_grouped hobl hcorr hw₀ hp hγ

/-- **Theorem P_γ, bits form:** `n²b ≤ 𝓗 ((γ+1) n b + ⌈n/γ⌉ σ)`, with
`σ = ⌈log₂(q+1)⌉ + k ⌈log₂(g+1)⌉`. This is stronger than
`n²b ≤ 𝓗 ((γ+1) n b + 1 + ⌈n/γ⌉ (σ + 1))`. -/
theorem theoremP_grouped_bits {M : TM} {n b T r γ : ℕ}
    (hobl : ObliviousOn M (matrixInputs n b) T)
    (hcorr : Transposes M n b) {w₀ : List Bool} (hw₀ : w₀ ∈ matrixInputs n b) {p : ℕ → ℕ}
    (hp : PassPartition M w₀ T r p) (hγ : 1 ≤ γ) :
    n * n * b ≤ addrCount M.k r * ((γ + 1) * n * b +
      numGroups n γ * (Nat.clog 2 (M.q + 1) + M.k * Nat.clog 2 (M.g + 1))) :=
  Impl.theoremP_grouped_bits hobl hcorr hw₀ hp hγ

/-- **Theorem P, log-free form.** Let `M` be oblivious (heads and output schedule) at length
`L = n²b`, and transpose `n × n` matrices with `b`-bit entries using at most `r` passes. Then

  `2^{n²b} ≤ 2^{2 n b 𝓗} · ((q+1)(g+1)^k)^{n 𝓗}`, where `𝓗 = Σ_{i<r} (k+1)^i`. -/
theorem theoremP {M : TM} {n b T r : ℕ} (hobl : ObliviousOn M (matrixInputs n b) T)
    (hcorr : Transposes M n b) {w₀ : List Bool} (hw₀ : w₀ ∈ matrixInputs n b) {p : ℕ → ℕ}
    (hp : PassPartition M w₀ T r p) :
    2 ^ (n * n * b) ≤
      2 ^ (addrCount M.k r * (2 * n * b)) * ((M.q + 1) * (M.g + 1) ^ M.k) ^ (n * addrCount M.k r) :=
  Impl.theoremP hobl hcorr hw₀ hp

/-- **Theorem P, bits form:** `n²b ≤ 𝓗 · n (2b + σ)`, with `σ = ⌈log₂(q+1)⌉ + k ⌈log₂(g+1)⌉`. -/
theorem theoremP_bits {M : TM} {n b T r : ℕ} (hobl : ObliviousOn M (matrixInputs n b) T)
    (hcorr : Transposes M n b) {w₀ : List Bool} (hw₀ : w₀ ∈ matrixInputs n b) {p : ℕ → ℕ}
    (hp : PassPartition M w₀ T r p) :
    n * n * b ≤
      addrCount M.k r * (n * (2 * b + (Nat.clog 2 (M.q + 1) + M.k * Nat.clog 2 (M.g + 1)))) :=
  Impl.theoremP_bits hobl hcorr hw₀ hp

/-- **Theorem P, bits form with `+1`:** `n²b ≤ 𝓗 · (n (2b + σ) + 1)`. -/
theorem theoremP_bits_add_one {M : TM} {n b T r : ℕ} (hobl : ObliviousOn M (matrixInputs n b) T)
    (hcorr : Transposes M n b) {w₀ : List Bool} (hw₀ : w₀ ∈ matrixInputs n b) {p : ℕ → ℕ}
    (hp : PassPartition M w₀ T r p) :
    n * n * b ≤
      addrCount M.k r * (n * (2 * b + (Nat.clog 2 (M.q + 1) + M.k * Nat.clog 2 (M.g + 1))) + 1) :=
  Impl.theoremP_bits_add_one hobl hcorr hw₀ hp

/-- **Theorem P, per-`n` form:** `n b ≤ 𝓗 (2b + σ)`, i.e. `𝓗 ≥ n / (2 + σ/b)`. This is sharper
than `𝓗 ≥ n / (2 + (σ+1)/b)`. -/
theorem theoremP_div {M : TM} {n b T r : ℕ} (hobl : ObliviousOn M (matrixInputs n b) T)
    (hcorr : Transposes M n b) {w₀ : List Bool} (hw₀ : w₀ ∈ matrixInputs n b) {p : ℕ → ℕ}
    (hp : PassPartition M w₀ T r p) :
    n * b ≤ addrCount M.k r * (2 * b + (Nat.clog 2 (M.q + 1) + M.k * Nat.clog 2 (M.g + 1))) :=
  Impl.theoremP_div hobl hcorr hw₀ hp

/-- **Theorem P, power form:** `k n b ≤ ((k+1)^r - 1)(2b + σ)`. Hence, for `k ≥ 1`,
`(k+1)^r ≥ 1 + k n/(2 + σ/b)` and `r ≥ log_{k+1}(k n / 2) - o(1)` for `b = ⌈log₂ n⌉`. (At `k = 0`
both sides are `0`; `theoremP_div` covers that case.) -/
theorem theoremP_pow {M : TM} {n b T r : ℕ} (hobl : ObliviousOn M (matrixInputs n b) T)
    (hcorr : Transposes M n b) {w₀ : List Bool} (hw₀ : w₀ ∈ matrixInputs n b) {p : ℕ → ℕ}
    (hp : PassPartition M w₀ T r p) :
    M.k * (n * b) ≤
      ((M.k + 1) ^ r - 1) * (2 * b + (Nat.clog 2 (M.q + 1) + M.k * Nat.clog 2 (M.g + 1))) :=
  Impl.theoremP_pow hobl hcorr hw₀ hp

/-- **Theorem P with the greedy pass count.** -/
theorem theoremP_greedy {M : TM} {n b T : ℕ} (hobl : ObliviousOn M (matrixInputs n b) T)
    (hcorr : Transposes M n b) {w₀ : List Bool} (hw₀ : w₀ ∈ matrixInputs n b) :
    n * n * b ≤ addrCount M.k (greedyPasses M w₀ T) *
      (n * (2 * b + (Nat.clog 2 (M.q + 1) + M.k * Nat.clog 2 (M.g + 1)))) :=
  Impl.theoremP_greedy hobl hcorr hw₀

/-! ### Theorem P on a set of inputs (robust form)

The machine need only be oblivious on, and correct on, a set `W` of co-entropy `≤ m`
(`2^{n² b} ≤ 2^m |W|`; correctness forces `W ⊆ matrixInputs n b`, so that is not a hypothesis).
Each group of `γ` columns pays `m` extra bits.
* Per column (`γ = 1`) the pass bound survives co-entropy `O(n)` (`theoremP_on_div`) but says nothing
  from co-entropy `n b` on.
* Per group of `γ = 2C` columns it survives co-entropy `C n b`, the level of the Tape Coding
  Conjecture (`theoremP_on_robust`; any `γ`: `theoremP_on_robust_gamma`).
* `theoremP_grouped` and `theoremP_grouped_bits` are the case `W` = all inputs, `m = 0` of
  `theoremP_grouped_on` and `theoremP_grouped_on_bits` (that is how they are proved, and so are
  `theoremP` and its other forms).
* The Cut Lemma on such a set (`cut_bound_on`, `cut_bound_on_coentropy`) is stated with the Cut
  Lemma above. -/

/-- **Theorem P on a set of co-entropy `≤ m`, log-free form.** Let `M` be oblivious (heads and output
schedule) with halting time `T` on a set `W` of matrix inputs with `2^{n² b} ≤ 2^m |W|`, output the
transposed encoding on every input of `W`, and use `r` passes. Then
`2^{n² b} ≤ 2^{n m} · 2^{2 n b 𝓗} · ((q+1)(g+1)^k)^{n 𝓗}`, with `𝓗 = Σ_{i<r} (k+1)^i`. -/
theorem theoremP_on {M : TM} {n b T r : ℕ} {W : Set (List Bool)} (hobl : ObliviousOn M W T)
    (hcorr : ∀ w ∈ W, ∃ A : Matrix, w = encode n b A ∧
      (run M w T).outRev.reverse = encode n b (transpose A))
    {w₀ : List Bool} (hw₀ : w₀ ∈ W) {p : ℕ → ℕ} (hp : PassPartition M w₀ T r p) {m : ℕ}
    (hco : 2 ^ (n * n * b) ≤ 2 ^ m * W.ncard) :
    2 ^ (n * n * b) ≤
      2 ^ (n * m) * (2 ^ (addrCount M.k r * (2 * n * b)) *
        ((M.q + 1) * (M.g + 1) ^ M.k) ^ (n * addrCount M.k r)) :=
  Impl.theoremP_on hobl hcorr hw₀ hp hco

/-- **Theorem P on a set, bits form:** `n² b ≤ n m + 𝓗 · n (2b + σ)`. -/
theorem theoremP_on_bits {M : TM} {n b T r : ℕ} {W : Set (List Bool)}
    (hobl : ObliviousOn M W T)
    (hcorr : ∀ w ∈ W, ∃ A : Matrix, w = encode n b A ∧
      (run M w T).outRev.reverse = encode n b (transpose A))
    {w₀ : List Bool} (hw₀ : w₀ ∈ W) {p : ℕ → ℕ} (hp : PassPartition M w₀ T r p) {m : ℕ}
    (hco : 2 ^ (n * n * b) ≤ 2 ^ m * W.ncard) :
    n * n * b ≤ n * m +
      addrCount M.k r * (n * (2 * b + (Nat.clog 2 (M.q + 1) + M.k * Nat.clog 2 (M.g + 1)))) :=
  Impl.theoremP_on_bits hobl hcorr hw₀ hp hco

/-- **Theorem P on a set of co-entropy `≤ C n`, per-`n` form:** `n b ≤ C n + 𝓗 (2b + σ)`, i.e.
`𝓗 ≥ n (b − C) / (2b + σ)`. So for `b = ⌈log₂ n⌉ → ∞` and `k ≥ 1` the bound of `theoremP_div`
survives up to a factor `1 − C/b`: co-entropy `O(n)` still forces `log_{k+1} n − O(1)` passes. -/
theorem theoremP_on_div {M : TM} {n b T r : ℕ} {W : Set (List Bool)}
    (hobl : ObliviousOn M W T)
    (hcorr : ∀ w ∈ W, ∃ A : Matrix, w = encode n b A ∧
      (run M w T).outRev.reverse = encode n b (transpose A))
    {w₀ : List Bool} (hw₀ : w₀ ∈ W) {p : ℕ → ℕ} (hp : PassPartition M w₀ T r p) {C : ℕ}
    (hco : 2 ^ (n * n * b) ≤ 2 ^ (C * n) * W.ncard) :
    n * b ≤ C * n +
      addrCount M.k r * (2 * b + (Nat.clog 2 (M.q + 1) + M.k * Nat.clog 2 (M.g + 1))) :=
  Impl.theoremP_on_div hobl hcorr hw₀ hp hco

/-- **Theorem P on a set of co-entropy `≤ C n`, power form:**
`k n b ≤ k C n + ((k+1)^r − 1)(2b + σ)`. -/
theorem theoremP_on_pow {M : TM} {n b T r : ℕ} {W : Set (List Bool)}
    (hobl : ObliviousOn M W T)
    (hcorr : ∀ w ∈ W, ∃ A : Matrix, w = encode n b A ∧
      (run M w T).outRev.reverse = encode n b (transpose A))
    {w₀ : List Bool} (hw₀ : w₀ ∈ W) {p : ℕ → ℕ} (hp : PassPartition M w₀ T r p) {C : ℕ}
    (hco : 2 ^ (n * n * b) ≤ 2 ^ (C * n) * W.ncard) :
    M.k * (n * b) ≤ M.k * (C * n) +
      ((M.k + 1) ^ r - 1) * (2 * b + (Nat.clog 2 (M.q + 1) + M.k * Nat.clog 2 (M.g + 1))) :=
  Impl.theoremP_on_pow hobl hcorr hw₀ hp hco

/-- **Theorem P_γ on a set of co-entropy `≤ m`, log-free form.** Each of the `⌈n/γ⌉` groups of `γ`
columns pays `m` bits:
`2^{n² b} ≤ 2^{⌈n/γ⌉ m} · 2^{𝓗 (γ+1) n b} · ((q+1)(g+1)^k)^{⌈n/γ⌉ 𝓗}`. -/
theorem theoremP_grouped_on {M : TM} {n b T r γ : ℕ} {W : Set (List Bool)}
    (hobl : ObliviousOn M W T)
    (hcorr : ∀ w ∈ W, ∃ A : Matrix, w = encode n b A ∧
      (run M w T).outRev.reverse = encode n b (transpose A))
    {w₀ : List Bool} (hw₀ : w₀ ∈ W) {p : ℕ → ℕ} (hp : PassPartition M w₀ T r p) (hγ : 1 ≤ γ)
    {m : ℕ} (hco : 2 ^ (n * n * b) ≤ 2 ^ m * W.ncard) :
    2 ^ (n * n * b) ≤
      2 ^ (numGroups n γ * m) * (2 ^ (addrCount M.k r * ((γ + 1) * n * b)) *
        ((M.q + 1) * (M.g + 1) ^ M.k) ^ (numGroups n γ * addrCount M.k r)) :=
  Impl.theoremP_grouped_on hobl hcorr hw₀ hp hγ hco

/-- **Theorem P_γ on a set, bits form:** `n² b ≤ ⌈n/γ⌉ m + 𝓗 ((γ+1) n b + ⌈n/γ⌉ σ)`. With `m = 0`
it is `theoremP_grouped_bits`, with `γ = 1` `theoremP_on_bits`. -/
theorem theoremP_grouped_on_bits {M : TM} {n b T r γ : ℕ} {W : Set (List Bool)}
    (hobl : ObliviousOn M W T)
    (hcorr : ∀ w ∈ W, ∃ A : Matrix, w = encode n b A ∧
      (run M w T).outRev.reverse = encode n b (transpose A))
    {w₀ : List Bool} (hw₀ : w₀ ∈ W) {p : ℕ → ℕ} (hp : PassPartition M w₀ T r p) (hγ : 1 ≤ γ)
    {m : ℕ} (hco : 2 ^ (n * n * b) ≤ 2 ^ m * W.ncard) :
    n * n * b ≤ numGroups n γ * m + addrCount M.k r * ((γ + 1) * n * b +
      numGroups n γ * (Nat.clog 2 (M.q + 1) + M.k * Nat.clog 2 (M.g + 1))) :=
  Impl.theoremP_grouped_on_bits hobl hcorr hw₀ hp hγ hco

/-- **Theorem P at the robust co-entropy level `C n b`, any grouping `γ ≥ 1`:**
`(γ − C) n² b ≤ γ C n b + 𝓗 (γ(γ+1) n b + (n + γ) σ)`. (With `γ = 2C`: `theoremP_on_robust`.) -/
theorem theoremP_on_robust_gamma {M : TM} {n b T r : ℕ} {W : Set (List Bool)}
    (hobl : ObliviousOn M W T)
    (hcorr : ∀ w ∈ W, ∃ A : Matrix, w = encode n b A ∧
      (run M w T).outRev.reverse = encode n b (transpose A))
    {w₀ : List Bool} (hw₀ : w₀ ∈ W) {p : ℕ → ℕ} (hp : PassPartition M w₀ T r p) {C γ : ℕ}
    (hγ : 1 ≤ γ) (hco : 2 ^ (n * n * b) ≤ 2 ^ (C * (n * b)) * W.ncard) :
    (γ - C) * (n * n * b) ≤ γ * C * (n * b) + addrCount M.k r * (γ * (γ + 1) * (n * b) +
      (n + γ) * (Nat.clog 2 (M.q + 1) + M.k * Nat.clog 2 (M.g + 1))) :=
  Impl.theoremP_on_robust_gamma hobl hcorr hw₀ hp hγ hco

/-- **Theorem P at the robust co-entropy level `C n b`.** With groups of `2C` columns:
`C n b ≤ 2C² b + 𝓗 (2C(2C+1) b + 2σ)`, so `𝓗 ≳ n / (2(2C+1))`, i.e. still `log_{k+1} n − O(log C)`
passes (for `b = ⌈log₂ n⌉`, `k ≥ 1`). So the pass lower bound is robust at the co-entropy `C n w`
of the Tape Coding Conjecture (`RobustNoCode_TM`), not only at `O(n)`. (The weaker form
`C n b ≤ 2C² b + (2C+1) 𝓗 (2Cb + σ)`, with side term `(2C+1)σ` in place of `2σ`, follows.) -/
theorem theoremP_on_robust {M : TM} {n b T r : ℕ} {W : Set (List Bool)}
    (hobl : ObliviousOn M W T)
    (hcorr : ∀ w ∈ W, ∃ A : Matrix, w = encode n b A ∧
      (run M w T).outRev.reverse = encode n b (transpose A))
    {w₀ : List Bool} (hw₀ : w₀ ∈ W) {p : ℕ → ℕ} (hp : PassPartition M w₀ T r p) {C : ℕ}
    (hco : 2 ^ (n * n * b) ≤ 2 ^ (C * (n * b)) * W.ncard) :
    C * (n * b) ≤ 2 * C * C * b + addrCount M.k r *
      (2 * C * (2 * C + 1) * b + 2 * (Nat.clog 2 (M.q + 1) + M.k * Nat.clog 2 (M.g + 1))) :=
  Impl.theoremP_on_robust hobl hcorr hw₀ hp hco

/-- **Non-vacuity of Theorem P's hypotheses.** `Witness.tr2` (`n = 2`, `b = 1`) is oblivious and
correct, and its greedy passes form a pass partition. It has no work tapes; `theoremP_hyps_tr2k`
gives the same with one (idle) work tape. Neither exercises the hull children. -/
theorem theoremP_hyps_tr2 : ∃ (T r : ℕ) (p : ℕ → ℕ),
    ObliviousOn Witness.tr2 (matrixInputs 2 1) T ∧ Transposes Witness.tr2 2 1 ∧
      encode 2 1 (fun _ _ _ => false) ∈ matrixInputs 2 1 ∧
      PassPartition Witness.tr2 (encode 2 1 (fun _ _ _ => false)) T r p :=
  ⟨5, _, _, tr2_obliviousOn, tr2_transposes, ⟨_, rfl⟩, greedy_passPartition _ _ 5⟩

/-- Non-vacuity with a work tape: `Witness.tr2k` (`tr2` with one idle work tape, `k = 1`) is
oblivious on the `2 × 2` matrices with 1-bit entries, with running time `5`. -/
theorem tr2k_obliviousOn : ObliviousOn Witness.tr2k (matrixInputs 2 1) 5 :=
  Impl.tr2k_obliviousOn

/-- `Witness.tr2k` transposes `2 × 2` matrices with 1-bit entries. -/
theorem tr2k_transposes : Transposes Witness.tr2k 2 1 :=
  Impl.tr2k_transposes

/-- **Non-vacuity of Theorem P's hypotheses with `k = 1`.** -/
theorem theoremP_hyps_tr2k : Witness.tr2k.k = 1 ∧ ∃ (T r : ℕ) (p : ℕ → ℕ),
    ObliviousOn Witness.tr2k (matrixInputs 2 1) T ∧ Transposes Witness.tr2k 2 1 ∧
      encode 2 1 (fun _ _ _ => false) ∈ matrixInputs 2 1 ∧
      PassPartition Witness.tr2k (encode 2 1 (fun _ _ _ => false)) T r p :=
  ⟨rfl, 5, _, _, tr2k_obliviousOn, tr2k_transposes, ⟨_, rfl⟩, greedy_passPartition _ _ 5⟩

/-! # Theorem M\*: level form for interval labellings

Let `M` be oblivious and transpose `n × n` matrices with `entryBits n`-bit entries in time
`T ≤ c L`. The rescaled trajectory `P_t^{(n)}(u)` of work head `t` is its block at the first step of
slot `⌊u n⌋`, divided by `n`. Along every sequence `n_i → ∞` these trajectories have subsequences
converging uniformly on `[0, c₀]` (`c₀ = c G + 1`), and every such limit `(P_t)_t` satisfies the
M\* inequality (★) `1 ≤ Σ_t ∫⁻ κ_t(p) dp + 2θ + 2k |S ∩ [0, c₀]|` for every finite union `S` of
closed intervals and every piecewise-constant labelling of `[0, c₀] ∖ S` whose classes have measure
`≤ θ`. Here `κ_t(p)` counts the consecutive pairs of the level set `P_t⁻¹(p) ∩ [0, c₀]` that lie
off `S` and carry different labels. Definitions are in `DefsM.lean`.

* Countability of extremal values: `countable_localExtr_values`.
* The easy half of Banach's indicatrix (almost every level set is finite):
  `levelSet_encard_majorant`, `lintegral_encard_levelSet_le`, `ae_finite_levelSet`.
* Counting long chords by levels, for abstract integer sequences: `levelChords_limsup_le`.
* The chord split, with the finitary pieces for the machine: `pairRes_V2` ((V2) for the frozen
  walk), `numSlots_le_horizon` (`N ≤ c₀ n`), `crossChords_split` (short chords, chords touching
  `S`, long chords off `S`).
* The limits are 1-Lipschitz: `rescaledTraj_limit_lipschitz`.
* Compactness (Arzelà–Ascoli): `exists_subseq_tendstoUniformlyOn`.
* **Theorem M\*, level form**: `theoremMStar_level` (additive form, any `θ`; along any convergent
  sequence, so for every subsequential limit), `theoremMStar_level_sub` (subtractive notation),
  and `theoremMStar_level_subseq` (a subsequential limit exists, and it satisfies the inequality).
* The conclusion has content: `theoremMStar_conclusion_can_fail`, and the corollary
  `no_stationary_limits` (also a case of `theoremMStar_excess`: the path `0` is monotone).
* **Labelling-free forms**: `κ ≤ #Λ − 1` (`levelCross_le_levelExcess`); (★) for every labelling
  gives total excess level multiplicity `Σ_t ∫⁻ (#Λ_t(p) − 1) dp ≥ 1` (`one_le_excess_of_star`)
  and, with the easy half of Banach's indicatrix (`excess_add_range_le`), total range
  `1 + Σ_t |P_t([0, c₀])| ≤ k c₀` (`range_add_one_le_of_star`); a monotone path has no excess
  (`lintegral_levelExcess_eq_zero_of_monotone`), so the limits are not all monotone
  (`not_all_monotone_of_star`); `theoremMStar_excess` for the oblivious machine.

All these machine forms are instances of Theorem M\* for walks (`theoremMStar_walk`,
`Statements/Coding.lean`), whose generic walk lemmas (`frozen_V2`, `numSlots_le_of`,
`blockTraj_limit_lipschitz`, `exists_subseq_blockTraj`) the machine statements below specialize.
-/

open MeasureTheory Filter Topology

open scoped ENNReal

/-- **Countability of extremal values.** For any function `P : ℝ → ℝ`, the values at local extrema
form a countable set. (Each such value is the minimum or maximum of `P` over an interval with
rational endpoints.) The complementary fact, that at any other level every point of the level set
has points above and below arbitrarily close by, is the negation of being a local extremum and is
used inline in counting long chords by levels (`levelChords_limsup_le`). -/
theorem countable_localExtr_values (P : ℝ → ℝ) :
    {p | ∃ s, P s = p ∧ (IsLocalMin P s ∨ IsLocalMax P s)}.Countable :=
  Impl.countable_localExtr_values P

/-- **The easy half of Banach's indicatrix, with a measurable majorant.** For `P` that is
`K`-Lipschitz on `[0, c₀]`, the number of points of the level set `Λ(p) = P⁻¹(p) ∩ [0, c₀]` is
bounded by a measurable function of `p` whose integral is at most `K c₀`. -/
theorem levelSet_encard_majorant {K : NNReal} {P : ℝ → ℝ} {c₀ : ℝ}
    (hP : LipschitzOnWith K P (Set.Icc 0 c₀)) :
    ∃ F : ℝ → ℝ≥0∞, Measurable F ∧ (∀ p, ((levelSet P c₀ p).encard : ℝ≥0∞) ≤ F p) ∧
      ∫⁻ p, F p ≤ K * ENNReal.ofReal c₀ :=
  Impl.levelSet_encard_majorant hP

/-- **The easy half of Banach's indicatrix.** For `P` that is `K`-Lipschitz on `[0, c₀]`, the
number of points of the level sets `Λ(p) = P⁻¹(p) ∩ [0, c₀]` has integral at most `K c₀`. -/
theorem lintegral_encard_levelSet_le {K : NNReal} {P : ℝ → ℝ} {c₀ : ℝ}
    (hP : LipschitzOnWith K P (Set.Icc 0 c₀)) :
    ∫⁻ p, ((levelSet P c₀ p).encard : ℝ≥0∞) ≤ K * ENNReal.ofReal c₀ :=
  Impl.lintegral_encard_levelSet_le hP

/-- **Almost every level set is finite.** For `P` Lipschitz on `[0, c₀]`, almost every level set
`Λ(p)` is finite. -/
theorem ae_finite_levelSet {K : NNReal} {P : ℝ → ℝ} {c₀ : ℝ}
    (hP : LipschitzOnWith K P (Set.Icc 0 c₀)) :
    ∀ᵐ p, (levelSet P c₀ p).Finite :=
  Impl.ae_finite_levelSet hP

/-- **Counting long chords by levels, for abstract integer sequences.** For each `i` let
`W i : ℕ → ℤ` (in the application, the head's block at the first step of each slot; no step bound
is assumed) and let `R i : ℕ → Finset ℤ` be a residency (the visit slots of block `σ` are
`{y | σ ∈ R i y}`). Assume, for all large `i`:
* `N i ≤ c₀ n_i` (the slots that count are `y < N i`);
* **(V1′)** resident blocks lie within `D` of `W i`;
* **(V2′)** if `W i` passes strictly over `σ` between slots `y₁ ≤ y₂`, then `σ` is resident at some
  slot in `[y₁, y₂]`;
and assume that `u ↦ W_i(⌊u n_i⌋)/n_i` converges uniformly on `[0, c₀]` to a 1-Lipschitz `P`.

Then, for every `η > 0`, every finite union `S` of closed intervals and every piecewise-constant
labelling `β`, the long label-crossing chords off `S` satisfy
`limsup_i |𝒳_i| / n_i ≤ ∫⁻ κ(p) dp`. -/
theorem levelChords_limsup_le {c₀ η : ℝ} (hη : 0 < η) {D : ℕ} {P : ℝ → ℝ}
    (hP : LipschitzOnWith 1 P (Set.Icc 0 c₀)) {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop)
    {W : ℕ → ℕ → ℤ} {R : ℕ → ℕ → Finset ℤ} {N : ℕ → ℕ}
    (hN : ∀ᶠ i in atTop, (N i : ℝ) ≤ c₀ * ns i)
    (hV1 : ∀ᶠ i in atTop, ∀ y σ, σ ∈ R i y → |W i y - σ| ≤ D)
    (hV2 : ∀ᶠ i in atTop, ∀ y₁ y₂ σ, y₁ ≤ y₂ →
      (W i y₁ < σ ∧ σ < W i y₂ ∨ W i y₂ < σ ∧ σ < W i y₁) → ∃ y, y₁ ≤ y ∧ y ≤ y₂ ∧ σ ∈ R i y)
    (hconv : TendstoUniformlyOn (fun i (u : ℝ) => (W i ⌊u * ns i⌋₊ : ℝ) / ns i) P atTop
      (Set.Icc 0 c₀))
    {S : Set ℝ} (hS : FinUnionIcc S) {β : ℝ → ℕ} (hβ : PiecewiseConstOn β S c₀) :
    limsup (fun i => ((longCross (R i) S β (ns i) η (N i)).card : ℝ≥0∞) / ns i) atTop ≤
      ∫⁻ p, levelCross P S β c₀ p :=
  Impl.levelChords_limsup_le hη hP hns hN hV1 hV2 hconv hS hβ

/-- **(V2) for the frozen machine walk.** Let `M` halt on `w` at time `T`, and let `W y` be the
block of work head `t` at the first step of slot `y` (slot length `r ≥ 1`). If `W` passes strictly
over a block `σ` between slots `y₁ ≤ y₂`, then `σ` is resident (pair residency) at some slot in
`[y₁, y₂]`. Slots after halting carry the final block and so never lie strictly between. -/
theorem pairRes_V2 {M : TM} {w : List Bool} {T r : ℕ} (hT : HaltsAt M w T) (hr : 1 ≤ r)
    (t : Fin M.k) {y₁ y₂ : ℕ} (hy : y₁ ≤ y₂) {σ : ℤ}
    (hσ : curBlock r (fun τ => workTraj M w τ t) (y₁ * r) < σ ∧
          σ < curBlock r (fun τ => workTraj M w τ t) (y₂ * r) ∨
        curBlock r (fun τ => workTraj M w τ t) (y₂ * r) < σ ∧
          σ < curBlock r (fun τ => workTraj M w τ t) (y₁ * r)) :
    ∃ y, y₁ ≤ y ∧ y ≤ y₂ ∧ σ ∈ pairRes r (fun τ => workTraj M w τ t) T y :=
  Impl.pairRes_V2 hT hr t hy hσ

/-- **The number of slots is at most `c₀ n`.** If `T ≤ c L` with `L = n² b`, `b = entryBits n` and
`n ≥ 1`, then `⌈T / r⌉ ≤ (c G + 1) n` for `r = ⌈n b / G⌉`. -/
theorem numSlots_le_horizon {M : TM} {n T : ℕ} {c : ℝ} (hn : 1 ≤ n)
    (hT : (T : ℝ) ≤ c * inputLength n) :
    (numSlots (slotLen M n) T : ℝ) ≤ horizon M c * n :=
  Impl.numSlots_le_horizon hn hT

open Classical in
/-- **The chord split.** Let a residency `R` satisfy (P2): each slot is the source of at most one
chord and the target of at most one chord. Let the slot labelling `lab` give different `β`-values
to slots off `S` with different labels. Then the chords crossing labels (target slot `< N`) number
at most
* `M_b · (⌈η n⌉ + 1)` short ones (gap `< η n`; each crosses a label change),
* plus `2 · #{y < N : y/n ∈ S}` touching `S`,
* plus the long label-crossing chords off `S`. -/
theorem crossChords_split {R : ℕ → Finset ℤ}
    (hsrc : ∀ {σ σ' : ℤ} {x z z' : ℕ}, IsChord R σ x z → IsChord R σ' x z' → σ = σ' ∧ z = z')
    (htgt : ∀ {σ σ' : ℤ} {x x' z : ℕ}, IsChord R σ x z → IsChord R σ' x' z → σ = σ' ∧ x = x')
    (lab : ℕ → ℕ) (N n : ℕ) (η : ℝ) (S : Set ℝ) (β : ℝ → ℕ)
    (hlab : ∀ y y' : ℕ, (y : ℝ) / n ∉ S → (y' : ℝ) / n ∉ S → lab y ≠ lab y' →
      β ((y : ℝ) / n) ≠ β ((y' : ℝ) / n)) :
    (crossChords R lab N).card ≤ labelChanges lab N * (⌈η * n⌉₊ + 1) +
      2 * ((Finset.range N).filter (fun y : ℕ => (y : ℝ) / n ∈ S)).card +
      (longCross R S β n η N).card :=
  Impl.crossChords_split hsrc htgt lab N n η S β hlab

/-- **The limits are 1-Lipschitz.** If the rescaled trajectories of a work head converge uniformly
on `[0, c₀]` along `n_i → ∞`, the limit is 1-Lipschitz there (any machine). -/
theorem rescaledTraj_limit_lipschitz {M : TM} {c : ℝ} {ns : ℕ → ℕ}
    (hns : Tendsto ns atTop atTop) {t : Fin M.k} {P : ℝ → ℝ}
    (hconv : TendstoUniformlyOn (fun i => rescaledTraj M (ns i) t) P atTop
      (Set.Icc 0 (horizon M c))) :
    LipschitzOnWith 1 P (Set.Icc 0 (horizon M c)) :=
  Impl.rescaledTraj_limit_lipschitz hns hconv

/-- **Compactness (Arzelà–Ascoli).** For every machine and every sequence `n_i → ∞` there are a
subsequence and limits along which the rescaled work-head trajectories converge uniformly on
`[0, c₀]`. -/
theorem exists_subseq_tendstoUniformlyOn (M : TM) (c : ℝ) {ns : ℕ → ℕ}
    (hns : Tendsto ns atTop atTop) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ P : Fin M.k → ℝ → ℝ, ∀ t,
      TendstoUniformlyOn (fun i => rescaledTraj M (ns (φ i)) t) (P t) atTop
        (Set.Icc 0 (horizon M c)) :=
  Impl.exists_subseq_tendstoUniformlyOn M c hns

/-- **Theorem M\*, level form for interval labellings, additive form.**

Let `M` be oblivious and transpose `n × n` matrices with `entryBits n`-bit entries in time
`T ≤ c L`, for all large `i`, along a sequence `n_i → ∞`; and let the rescaled work-head
trajectories converge uniformly on `[0, c₀]` (`c₀ = c G + 1`) to limits `P_t`. Let `θ` be any
bound, `S` any finite union of closed intervals, and `β` any labelling of `[0, c₀] ∖ S` that is
constant on the intervals avoiding a finite set (`PiecewiseConstOn`; this is "constant on
finitely many intervals", degenerate intervals allowed) and whose classes have Lebesgue measure
`≤ θ`. Then

  `1 ≤ Σ_t ∫⁻ κ_t(p) dp + 2θ + 2k |S ∩ [0, c₀]|`. -/
theorem theoremMStar_level {M : TM} {c : ℝ} {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop)
    {Ts : ℕ → ℕ}
    (hobl : ∀ᶠ i in atTop, ObliviousOn M (matrixInputs (ns i) (entryBits (ns i))) (Ts i))
    (hcorr : ∀ᶠ i in atTop, Transposes M (ns i) (entryBits (ns i)))
    (htime : ∀ᶠ i in atTop, (Ts i : ℝ) ≤ c * inputLength (ns i))
    {P : Fin M.k → ℝ → ℝ}
    (hconv : ∀ t, TendstoUniformlyOn (fun i => rescaledTraj M (ns i) t) (P t) atTop
      (Set.Icc 0 (horizon M c)))
    {θ : ℝ≥0∞} {S : Set ℝ} (hS : FinUnionIcc S) {β : ℝ → ℕ}
    (hβ : PiecewiseConstOn β S (horizon M c))
    (hclass : ∀ ℓ, volume {u | u ∈ Set.Icc 0 (horizon M c) ∧ u ∉ S ∧ β u = ℓ} ≤ θ) :
    1 ≤ (∑ t, ∫⁻ p, levelCross (P t) S β (horizon M c) p) + 2 * θ +
      2 * M.k * volume (S ∩ Set.Icc 0 (horizon M c)) :=
  Impl.theoremMStar_level hns hobl hcorr htime hconv hS hβ hclass

/-- **Theorem M\*, level form, subtractive notation:**
`Σ_t ∫⁻ κ_t(p) dp ≥ 1 − 2θ − 2k |S ∩ [0, c₀]|`, for every `θ ≥ 0` (not only `θ ∈ (0, ½)`). -/
theorem theoremMStar_level_sub {M : TM} {c : ℝ} {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop)
    {Ts : ℕ → ℕ}
    (hobl : ∀ᶠ i in atTop, ObliviousOn M (matrixInputs (ns i) (entryBits (ns i))) (Ts i))
    (hcorr : ∀ᶠ i in atTop, Transposes M (ns i) (entryBits (ns i)))
    (htime : ∀ᶠ i in atTop, (Ts i : ℝ) ≤ c * inputLength (ns i))
    {P : Fin M.k → ℝ → ℝ}
    (hconv : ∀ t, TendstoUniformlyOn (fun i => rescaledTraj M (ns i) t) (P t) atTop
      (Set.Icc 0 (horizon M c)))
    {θ : ℝ} (hθ : 0 ≤ θ) {S : Set ℝ} (hS : FinUnionIcc S) {β : ℝ → ℕ}
    (hβ : PiecewiseConstOn β S (horizon M c))
    (hclass : ∀ ℓ, volume {u | u ∈ Set.Icc 0 (horizon M c) ∧ u ∉ S ∧ β u = ℓ} ≤
      ENNReal.ofReal θ) :
    ENNReal.ofReal (1 - 2 * θ - 2 * M.k * (volume (S ∩ Set.Icc 0 (horizon M c))).toReal) ≤
      ∑ t, ∫⁻ p, levelCross (P t) S β (horizon M c) p :=
  Impl.theoremMStar_level_sub hns hobl hcorr htime hconv hθ hS hβ hclass

/-- **Theorem M\*, every machine has a subsequential limit, and it satisfies the inequality**
(with compactness). For an oblivious transposer with `T ≤ c L` along `n_i → ∞` there are a
subsequence and 1-Lipschitz limits `P_t` of the rescaled work-head trajectories such that the
conclusion of `theoremMStar_level` holds for every `θ`, `S` and `β`. -/
theorem theoremMStar_level_subseq {M : TM} {c : ℝ} {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop)
    {Ts : ℕ → ℕ}
    (hobl : ∀ᶠ i in atTop, ObliviousOn M (matrixInputs (ns i) (entryBits (ns i))) (Ts i))
    (hcorr : ∀ᶠ i in atTop, Transposes M (ns i) (entryBits (ns i)))
    (htime : ∀ᶠ i in atTop, (Ts i : ℝ) ≤ c * inputLength (ns i)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ P : Fin M.k → ℝ → ℝ,
      (∀ t, TendstoUniformlyOn (fun i => rescaledTraj M (ns (φ i)) t) (P t) atTop
        (Set.Icc 0 (horizon M c))) ∧
      (∀ t, LipschitzOnWith 1 (P t) (Set.Icc 0 (horizon M c))) ∧
      ∀ (θ : ℝ≥0∞) (S : Set ℝ) (β : ℝ → ℕ), FinUnionIcc S → PiecewiseConstOn β S (horizon M c) →
        (∀ ℓ, volume {u | u ∈ Set.Icc 0 (horizon M c) ∧ u ∉ S ∧ β u = ℓ} ≤ θ) →
        1 ≤ (∑ t, ∫⁻ p, levelCross (P t) S β (horizon M c) p) + 2 * θ +
          2 * M.k * volume (S ∩ Set.Icc 0 (horizon M c)) :=
  Impl.theoremMStar_level_subseq hns hobl hcorr htime

/-- **The conclusion of Theorem M\* can fail.** For `P = 0` (every work head macroscopically
stationary), `S = ∅`, `β u = ⌊4u⌋` and `θ = 1/4`, the hypotheses on `S`, `β` and `θ` hold and the
inequality of `theoremMStar_level` fails. So the theorem is a genuine constraint on the limits. -/
theorem theoremMStar_conclusion_can_fail (k : ℕ) (c₀ : ℝ) :
    FinUnionIcc (∅ : Set ℝ) ∧ PiecewiseConstOn (fun u : ℝ => ⌊4 * u⌋₊) ∅ c₀ ∧
    (∀ ℓ, volume {u | u ∈ Set.Icc 0 c₀ ∧ u ∉ (∅ : Set ℝ) ∧ (fun u : ℝ => ⌊4 * u⌋₊) u = ℓ} ≤
      ENNReal.ofReal (1 / 4)) ∧
    ¬ (1 ≤ (∑ _t : Fin k, ∫⁻ p, levelCross (fun _ => 0) ∅ (fun u : ℝ => ⌊4 * u⌋₊) c₀ p) +
        2 * ENNReal.ofReal (1 / 4) + 2 * k * volume ((∅ : Set ℝ) ∩ Set.Icc 0 c₀)) :=
  Impl.theoremMStar_conclusion_can_fail k c₀

/-- **Corollary: no stationary limits.** An oblivious linear-time transposer cannot have all of
its rescaled work-head trajectories converging uniformly to `0` along a sequence `n_i → ∞`. -/
theorem no_stationary_limits {M : TM} {c : ℝ} {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop)
    {Ts : ℕ → ℕ}
    (hobl : ∀ᶠ i in atTop, ObliviousOn M (matrixInputs (ns i) (entryBits (ns i))) (Ts i))
    (hcorr : ∀ᶠ i in atTop, Transposes M (ns i) (entryBits (ns i)))
    (htime : ∀ᶠ i in atTop, (Ts i : ℝ) ≤ c * inputLength (ns i)) :
    ¬ ∀ t, TendstoUniformlyOn (fun i => rescaledTraj M (ns i) t) (fun _ => 0) atTop
      (Set.Icc 0 (horizon M c)) :=
  Impl.no_stationary_limits hns hobl hcorr htime


/-! ### Labelling-free forms of (★) -/

/-- **`κ(p) ≤ #Λ(p) − 1`**: at most `#Λ(p) − 1` consecutive pairs of the level set cross labels, for
every excised set `S` and labelling `β`. -/
theorem levelCross_le_levelExcess (P : ℝ → ℝ) (S : Set ℝ) (β : ℝ → ℕ) (c₀ p : ℝ) :
    levelCross P S β c₀ p ≤ levelExcess P c₀ p :=
  Impl.levelCross_le_levelExcess P S β c₀ p

/-- **(★) for every labelling gives total excess multiplicity `≥ 1`** (TM-free). If `P_t` (`t < k`)
satisfy the conclusion of Theorem M\* for every `θ ∈ (0, ½)`, `S` and `β`, then
`Σ_t ∫⁻ (#Λ_t(p) − 1) dp ≥ 1`. (Take `S = ∅`, labels `⌊m u⌋` with `θ = 1/m`, and `m → ∞`.) So the
limit head paths must revisit levels: if every `P_t` were injective, the left side would be `0`. -/
theorem one_le_excess_of_star {k : ℕ} {P : Fin k → ℝ → ℝ} {c₀ : ℝ}
    (hstar : ∀ (θ : ℝ≥0∞), 0 < θ → θ < 1 / 2 → ∀ (S : Set ℝ) (β : ℝ → ℕ), FinUnionIcc S →
      PiecewiseConstOn β S c₀ → (∀ ℓ, volume {u | u ∈ Set.Icc 0 c₀ ∧ u ∉ S ∧ β u = ℓ} ≤ θ) →
      1 ≤ (∑ t, ∫⁻ p, levelCross (P t) S β c₀ p) + 2 * θ + 2 * k * volume (S ∩ Set.Icc 0 c₀)) :
    1 ≤ ∑ t, ∫⁻ p, levelExcess (P t) c₀ p :=
  Impl.one_le_excess_of_star hstar

/-- **The easy half of Banach's indicatrix, with the range split off.** For `P` 1-Lipschitz on
`[0, c₀]`: `∫⁻ (#Λ(p) − 1) dp + |P([0, c₀])| ≤ c₀`. -/
theorem excess_add_range_le {P : ℝ → ℝ} {c₀ : ℝ} (hP : LipschitzOnWith 1 P (Set.Icc 0 c₀)) :
    (∫⁻ p, levelExcess P c₀ p) + volume (P '' Set.Icc 0 c₀) ≤ ENNReal.ofReal c₀ :=
  Impl.excess_add_range_le hP

/-- **(★) for every labelling caps the total range** (TM-free). If `P_t` (`t < k`) are 1-Lipschitz
on `[0, c₀]` and satisfy the conclusion of Theorem M\* for every `θ`, `S` and `β`, then
`1 + Σ_t |P_t([0, c₀])| ≤ k c₀`: the ranges of the `k` paths fall short of their maximum `c₀` by at
least `1` in total. -/
theorem range_add_one_le_of_star {k : ℕ} {P : Fin k → ℝ → ℝ} {c₀ : ℝ}
    (hlip : ∀ t, LipschitzOnWith 1 (P t) (Set.Icc 0 c₀))
    (hstar : ∀ (θ : ℝ≥0∞), 0 < θ → θ < 1 / 2 → ∀ (S : Set ℝ) (β : ℝ → ℕ), FinUnionIcc S →
      PiecewiseConstOn β S c₀ → (∀ ℓ, volume {u | u ∈ Set.Icc 0 c₀ ∧ u ∉ S ∧ β u = ℓ} ≤ θ) →
      1 ≤ (∑ t, ∫⁻ p, levelCross (P t) S β c₀ p) + 2 * θ + 2 * k * volume (S ∩ Set.Icc 0 c₀)) :
    1 + ∑ t, volume (P t '' Set.Icc 0 c₀) ≤ k * ENNReal.ofReal c₀ :=
  Impl.range_add_one_le_of_star hlip hstar

/-- **A monotone path has no excess:** if `P` is monotone or antitone on `[0, c₀]`, then
`∫⁻ (#Λ(p) − 1) dp = 0` (levels with two preimages are values of `P` at rational points). -/
theorem lintegral_levelExcess_eq_zero_of_monotone {P : ℝ → ℝ} {c₀ : ℝ}
    (hmono : MonotoneOn P (Set.Icc 0 c₀) ∨ AntitoneOn P (Set.Icc 0 c₀)) :
    ∫⁻ p, levelExcess P c₀ p = 0 :=
  Impl.lintegral_levelExcess_eq_zero_of_monotone hmono

/-- **(★) for every labelling rules out monotone limits** (TM-free): the `k` paths cannot all be
monotone or antitone on `[0, c₀]`. For a machine: some work head must make a macroscopic U-turn. -/
theorem not_all_monotone_of_star {k : ℕ} {P : Fin k → ℝ → ℝ} {c₀ : ℝ}
    (hstar : ∀ (θ : ℝ≥0∞), 0 < θ → θ < 1 / 2 → ∀ (S : Set ℝ) (β : ℝ → ℕ), FinUnionIcc S →
      PiecewiseConstOn β S c₀ → (∀ ℓ, volume {u | u ∈ Set.Icc 0 c₀ ∧ u ∉ S ∧ β u = ℓ} ≤ θ) →
      1 ≤ (∑ t, ∫⁻ p, levelCross (P t) S β c₀ p) + 2 * θ + 2 * k * volume (S ∩ Set.Icc 0 c₀)) :
    ¬ ∀ t, MonotoneOn (P t) (Set.Icc 0 c₀) ∨ AntitoneOn (P t) (Set.Icc 0 c₀) :=
  Impl.not_all_monotone_of_star hstar

/-- **Theorem M\*, labelling-free form, for oblivious machines.** Under the hypotheses of
`theoremMStar_level`, the limits `P_t` have total excess level multiplicity
`Σ_t ∫⁻ (#Λ_t(p) − 1) dp ≥ 1` and total range `1 + Σ_t |P_t([0, c₀])| ≤ k c₀` (`c₀ = horizon M c`),
and they are not all monotone (this strengthens `no_stationary_limits`). -/
theorem theoremMStar_excess {M : TM} {c : ℝ} {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop)
    {Ts : ℕ → ℕ}
    (hobl : ∀ᶠ i in atTop, ObliviousOn M (matrixInputs (ns i) (entryBits (ns i))) (Ts i))
    (hcorr : ∀ᶠ i in atTop, Transposes M (ns i) (entryBits (ns i)))
    (htime : ∀ᶠ i in atTop, (Ts i : ℝ) ≤ c * inputLength (ns i))
    {P : Fin M.k → ℝ → ℝ}
    (hconv : ∀ t, TendstoUniformlyOn (fun i => rescaledTraj M (ns i) t) (P t) atTop
      (Set.Icc 0 (horizon M c))) :
    1 ≤ ∑ t, ∫⁻ p, levelExcess (P t) (horizon M c) p ∧
      1 + ∑ t, volume (P t '' Set.Icc 0 (horizon M c)) ≤ M.k * ENNReal.ofReal (horizon M c) ∧
      ¬ ∀ t, MonotoneOn (P t) (Set.Icc 0 (horizon M c)) ∨
        AntitoneOn (P t) (Set.Icc 0 (horizon M c)) :=
  Impl.theoremMStar_excess hns hobl hcorr htime hconv

end Transpose.Tape
