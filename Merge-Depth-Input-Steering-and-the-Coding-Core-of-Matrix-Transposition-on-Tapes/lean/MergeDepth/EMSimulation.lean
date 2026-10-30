import MergeDepth.EMModel
import Transpose.Tape.Encode
import Transpose.Tape.Run

/-!
# The windowed simulation of a machine (proof of Theorem EM)

The simulator of Theorem EM for a machine `M` with `k` work tapes, at block size `B` and dimension
`d`, as a step function `inner` on (slots, abstract register) in the sense of `MergeDepth.EM.collapse`.

* **Alphabet** `Sym M`: input symbols (a bit or the end marker) and work symbols; `symAlph M`
  declares `0`, `1` and the blank (the blank of the work alphabet).
* **Layout.** Tape `0` is the input tape, tape `h + 1` the work tape `h`. Block `j` of a tape is
  its cells `jB, …, jB + B - 1`. Row `i` of the input is stored at address `i`, block `j` of work
  tape `h` at `waddr d h j = 2d + k z(j) + h` with `z(j) = 2j` for `j ≥ 0` and `-2j - 1` for `j < 0`,
  and output group `n` at `d + n`.
* **Windows.** Slots `loS τ`, `hiS τ` hold blocks `j_τ`, `j_τ + 1` of tape `τ` (`view` reads cell
  `p`); slot `bufS` is the output buffer. The register (`Reg`) holds the state, the head positions
  `x_τ`, the window indices `j_τ`, the numbers of flushes and of buffered bits, and a phase: `start`
  (before the first I/O), `run`, or `pend h dir` (the second I/O of a shift of work tape `h`).
* **Steps.** `inner` performs at most one I/O per step. In phase `run` it first shifts the first
  tape whose head has left its window (`firstOut`): an input shift reads the entering row if it
  lies in `[0, d)` and otherwise fills end markers internally; a work shift writes back the leaving
  block and enters phase `pend`, whose step reads the entering block. Otherwise it flushes a full
  buffer to `d + nfl`; otherwise it applies the transition function of `M` to the symbols in the
  windows and halts if `M` halts, and else performs the step internally (`tmStep`).
* **Event words.** A `Letter` records a shift (tape, direction) or a flush; `ioWords` gives the
  I/Os of an event word from given window indices and flush count.

The invariant `Inv` relates a simulator state at time `t` to the configuration `run M w t`.
-/

namespace MergeDepth.EM

open Transpose Transpose.Tape Transpose.Tape.Impl

section Defs

variable (M : TM)

/-- The alphabet `Σ_M`: an input symbol (a bit, or `none` for the end marker) or a work symbol. -/
abbrev Sym := Option Bool ⊕ Fin (M.g + 1)

/-- `0`, `1` and the blank of `Σ_M`: the input bits and the blank of the work alphabet. -/
def symAlph : Alphabet (Sym M) where
  zero := .inl (some false)
  one := .inl (some true)
  blank := .inr 0
  zero_ne_one := by simp
  zero_ne_blank := by simp
  one_ne_blank := by simp

theorem symAlph_bit (b : Bool) : (symAlph M).bit b = .inl (some b) := by cases b <;> rfl

/-- The input symbol of a letter (`none` = end marker). -/
def toIn : Sym M → Option Bool
  | .inl o => o
  | .inr _ => none

/-- The work symbol of a letter. -/
def toWork : Sym M → Fin (M.g + 1)
  | .inr a => a
  | .inl _ => 0

/-- The phase of the simulator. -/
inductive Phase (k : ℕ)
  | start
  | run
  | pend (h : Fin k) (right : Bool)
  deriving DecidableEq

/-- Phases as `Option (Option (Fin k × Bool))`. -/
def Phase.equiv (k : ℕ) : Phase k ≃ Option (Option (Fin k × Bool)) where
  toFun
    | .start => none
    | .run => some none
    | .pend h r => some (some (h, r))
  invFun
    | none => .start
    | some none => .run
    | some (some (h, r)) => .pend h r
  left_inv p := by cases p <;> rfl
  right_inv o := by rcases o with _ | _ | ⟨h, r⟩ <;> rfl

instance (k : ℕ) : Fintype (Phase k) := Fintype.ofEquiv _ (Phase.equiv k).symm

theorem Phase.card (k : ℕ) : Fintype.card (Phase k) = 2 * k + 2 := by
  rw [Fintype.card_congr (Phase.equiv k)]
  simp only [Fintype.card_option, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  ring

/-- The abstract register: the state of `M`, the head positions, the window indices, the numbers
of flushes and of buffered bits, and the phase. Tape `0` is the input tape. -/
@[ext] structure Reg where
  st : Fin (M.q + 1)
  x : Fin (M.k + 1) → ℤ
  j : Fin (M.k + 1) → ℤ
  nfl : ℕ
  nbuf : ℕ
  ph : Phase M.k

/-- The slots: `2k + 3` blocks. -/
abbrev Slots (B : ℕ) := Fin (2 * M.k + 3) → Block (Sym M) B

/-- The slot of the lower window block of tape `τ`. -/
def loS (τ : Fin (M.k + 1)) : Fin (2 * M.k + 3) := ⟨2 * τ.val, by omega⟩

/-- The slot of the upper window block of tape `τ`. -/
def hiS (τ : Fin (M.k + 1)) : Fin (2 * M.k + 3) := ⟨2 * τ.val + 1, by omega⟩

/-- The output buffer. -/
def bufS : Fin (2 * M.k + 3) := ⟨2 * M.k + 2, by omega⟩

/-- The tape of a window slot. -/
def tapeOf (i : Fin (2 * M.k + 3)) : Fin (M.k + 1) := ⟨min (i.val / 2) M.k, by omega⟩

variable {M} in
/-- Symbol at offset `o` of a block (the work blank outside `[0, B)`). -/
def getZ {B : ℕ} (b : Block (Sym M) B) (o : ℤ) : Sym M :=
  if h : 0 ≤ o ∧ o < B then b ⟨o.toNat, by omega⟩ else .inr 0

/-- The window of tape `τ` with index `jj`: the symbol at cell `p ∈ [jj B, (jj + 2) B)`. -/
def view {B : ℕ} (sl : Slots M B) (τ : Fin (M.k + 1)) (jj p : ℤ) : Sym M :=
  if p < (jj + 1) * B then getZ (sl (loS M τ)) (p - jj * B) else getZ (sl (hiS M τ)) (p - (jj + 1) * B)

/-- Slots holding the windows `W τ` (with indices `jv τ`) and the buffer `buf`. -/
def pack {B : ℕ} (jv : Fin (M.k + 1) → ℤ) (W : Fin (M.k + 1) → ℤ → Sym M) (buf : Block (Sym M) B) :
    Slots M B :=
  fun i q => if i = bufS M then buf q else
    W (tapeOf M i) ((jv (tapeOf M i) + ((i.val % 2 : ℕ) : ℤ)) * B + q.val)

/-- A block of end markers. -/
def endBlk (B : ℕ) : Block (Sym M) B := fun _ => .inl none

/-- `z(j)`: `2j` for `j ≥ 0`, `-2j - 1` for `j < 0`. -/
def zz (jj : ℤ) : ℤ := if 0 ≤ jj then 2 * jj else -2 * jj - 1

/-- The address of block `jj` of work tape `h`. -/
def waddr (d : ℕ) (h : Fin M.k) (jj : ℤ) : ℤ := 2 * d + M.k * zz jj + h.val

/-- The head of tape `τ` lies outside its window. -/
abbrev Outside (B : ℕ) (ρ : Reg M) (τ : Fin (M.k + 1)) : Prop :=
  ρ.x τ < ρ.j τ * B ∨ (ρ.j τ + 2) * B ≤ ρ.x τ

/-- The first tape whose head lies outside its window. -/
def firstOut (B : ℕ) (ρ : Reg M) : Option (Fin (M.k + 1)) :=
  if h : ∃ τ, Outside M B ρ τ then some (Fin.find _ h) else none

/-- The first step: end markers into the lower input slot, row `0` into the upper one. -/
def startStep {B : ℕ} (s : Slots M B × Reg M) : Micro (Slots M B × Reg M) (2 * M.k + 3) :=
  .io .read (hiS M 0) 0 (Function.update s.1 (loS M 0) (endBlk M B), { s.2 with ph := .run })

/-- The second I/O of a shift of work tape `h` (right if `true`): read the entering block. -/
def pendStep (d : ℕ) {B : ℕ} (s : Slots M B × Reg M) (h : Fin M.k) :
    Bool → Micro (Slots M B × Reg M) (2 * M.k + 3)
  | true => .io .read (hiS M h.succ) (waddr M d h (s.2.j h.succ + 2))
      (Function.update s.1 (loS M h.succ) (s.1 (hiS M h.succ)),
        { s.2 with j := Function.update s.2.j h.succ (s.2.j h.succ + 1), ph := .run })
  | false => .io .read (loS M h.succ) (waddr M d h (s.2.j h.succ - 1))
      (Function.update s.1 (hiS M h.succ) (s.1 (loS M h.succ)),
        { s.2 with j := Function.update s.2.j h.succ (s.2.j h.succ - 1), ph := .run })

/-- A shift of the input tape: the entering row is read if it lies in `[0, d)`, and is a block of
end markers otherwise. -/
def inShift (d : ℕ) {B : ℕ} (s : Slots M B × Reg M) : Micro (Slots M B × Reg M) (2 * M.k + 3) :=
  if (s.2.j 0 + 2) * B ≤ s.2.x 0 then
    if 0 ≤ s.2.j 0 + 2 ∧ s.2.j 0 + 2 < d then
      .io .read (hiS M 0) (s.2.j 0 + 2) (Function.update s.1 (loS M 0) (s.1 (hiS M 0)),
        { s.2 with j := Function.update s.2.j 0 (s.2.j 0 + 1), ph := .run })
    else
      .tau (Function.update (Function.update s.1 (loS M 0) (s.1 (hiS M 0))) (hiS M 0) (endBlk M B),
        { s.2 with j := Function.update s.2.j 0 (s.2.j 0 + 1), ph := .run })
  else
    if 0 ≤ s.2.j 0 - 1 ∧ s.2.j 0 - 1 < d then
      .io .read (loS M 0) (s.2.j 0 - 1) (Function.update s.1 (hiS M 0) (s.1 (loS M 0)),
        { s.2 with j := Function.update s.2.j 0 (s.2.j 0 - 1), ph := .run })
    else
      .tau (Function.update (Function.update s.1 (hiS M 0) (s.1 (loS M 0))) (loS M 0) (endBlk M B),
        { s.2 with j := Function.update s.2.j 0 (s.2.j 0 - 1), ph := .run })

/-- The first I/O of a shift of work tape `h`: write back the leaving block. -/
def workShift (d : ℕ) {B : ℕ} (s : Slots M B × Reg M) (h : Fin M.k) :
    Micro (Slots M B × Reg M) (2 * M.k + 3) :=
  if (s.2.j h.succ + 2) * B ≤ s.2.x h.succ then
    .io .write (loS M h.succ) (waddr M d h (s.2.j h.succ)) (s.1, { s.2 with ph := .pend h true })
  else
    .io .write (hiS M h.succ) (waddr M d h (s.2.j h.succ + 1)) (s.1, { s.2 with ph := .pend h false })

/-- A shift of tape `τ`. -/
def shiftStep (d : ℕ) {B : ℕ} (s : Slots M B × Reg M) (τ : Fin (M.k + 1)) :
    Micro (Slots M B × Reg M) (2 * M.k + 3) :=
  Fin.cases (inShift M d s) (workShift M d s) τ

/-- The symbol written on tape `τ` (the work blank for the input tape). -/
def wsym (acts : Fin M.k → Fin (M.g + 1) × Dir) (τ : Fin (M.k + 1)) : Fin (M.g + 1) :=
  Fin.cases 0 (fun h => (acts h).1) τ

/-- One step of `M` inside the windows. -/
def tmStep {B : ℕ} (s : Slots M B × Reg M) (st' : Fin (M.q + 1)) (dIn : Dir)
    (acts : Fin M.k → Fin (M.g + 1) × Dir) (o : Option Bool) : Slots M B × Reg M :=
  (pack M s.2.j
      (fun τ p => if τ ≠ 0 ∧ p = s.2.x τ then .inr (wsym M acts τ) else view M s.1 τ (s.2.j τ) p)
      (match o with
        | some b => fun q => if q.val = s.2.nbuf then .inl (some b) else s.1 (bufS M) q
        | none => s.1 (bufS M)),
    { s.2 with
      st := st'
      x := Fin.cases (dIn.shift (s.2.x 0)) (fun h => (acts h).2.shift (s.2.x h.succ))
      nbuf := s.2.nbuf + (if o.isSome then 1 else 0) })

/-- The input symbol under the input head, read in its window. -/
def inSymOf {B : ℕ} (s : Slots M B × Reg M) : Option Bool := toIn M (view M s.1 0 (s.2.j 0) (s.2.x 0))

/-- The work symbols under the work heads, read in their windows. -/
def workSymOf {B : ℕ} (s : Slots M B × Reg M) : Fin M.k → Fin (M.g + 1) :=
  fun h => toWork M (view M s.1 h.succ (s.2.j h.succ) (s.2.x h.succ))

/-- A step in phase `run`. -/
def runStep (d : ℕ) {B : ℕ} (s : Slots M B × Reg M) : Micro (Slots M B × Reg M) (2 * M.k + 3) :=
  match firstOut M B s.2 with
  | some τ => shiftStep M d s τ
  | none =>
    if s.2.nbuf = B then
      .io .write (bufS M) ((d : ℤ) + s.2.nfl) (s.1, { s.2 with nfl := s.2.nfl + 1, nbuf := 0 })
    else
      match M.δ s.2.st (inSymOf M s) (workSymOf M s) with
      | none => .halt
      | some (st', dIn, acts, o) => .tau (tmStep M s st' dIn acts o)

/-- **The simulator.** -/
def inner (d B : ℕ) (s : Slots M B × Reg M) : Micro (Slots M B × Reg M) (2 * M.k + 3) :=
  match s.2.ph with
  | .start => startStep M s
  | .run => runStep M d s
  | .pend h r => pendStep M d s h r

/-- The initial register: state `0`, heads at `0`, window indices `-1`, phase `start`. -/
def reg₀ : Reg M where
  st := 0
  x := fun _ => 0
  j := fun _ => -1
  nfl := 0
  nbuf := 0
  ph := .start

/-! ### Event words -/

/-- An event: a shift of tape `τ` (right if `true`) or a flush. -/
inductive Letter (k : ℕ)
  | shift (τ : Fin (k + 1)) (right : Bool)
  | flush
  deriving DecidableEq

/-- Letters as `Option (Fin (k + 1) × Bool)`. -/
def Letter.equiv (k : ℕ) : Letter k ≃ Option (Fin (k + 1) × Bool) where
  toFun
    | .shift τ r => some (τ, r)
    | .flush => none
  invFun
    | some (τ, r) => .shift τ r
    | none => .flush
  left_inv ℓ := by cases ℓ <;> rfl
  right_inv o := by rcases o with _ | ⟨τ, r⟩ <;> rfl

instance (k : ℕ) : Fintype (Letter k) := Fintype.ofEquiv _ (Letter.equiv k).symm

theorem Letter.card (k : ℕ) : Fintype.card (Letter k) = 2 * k + 3 := by
  rw [Fintype.card_congr (Letter.equiv k)]
  simp only [Fintype.card_option, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  ring

/-- The tape of a shift letter. -/
def Letter.tape {k : ℕ} : Letter k → Option (Fin (k + 1))
  | .shift τ _ => some τ
  | .flush => none

/-- The number of shifts of tape `τ` in an event word. -/
def cnt {k : ℕ} (τ : Fin (k + 1)) (ev : List (Letter k)) : ℕ := ev.countP (fun ℓ => ℓ.tape = some τ)

/-- The number of flushes in an event word. -/
def nflush {k : ℕ} (ev : List (Letter k)) : ℕ := ev.countP (fun ℓ => ℓ.tape = none)

/-- The I/Os of one event from window indices `jv` and flush count `n`, and the new indices and
count. -/
def letterIO (d : ℕ) (jv : Fin (M.k + 1) → ℤ) (n : ℕ) :
    Letter M.k → List (IO (2 * M.k + 3)) × (Fin (M.k + 1) → ℤ) × ℕ
  | .shift τ true =>
    (Fin.cases (if 0 ≤ jv 0 + 2 ∧ jv 0 + 2 < d then [(.read, hiS M 0, jv 0 + 2)] else [])
      (fun h => [(.write, loS M h.succ, waddr M d h (jv h.succ)),
        (.read, hiS M h.succ, waddr M d h (jv h.succ + 2))]) τ,
      Function.update jv τ (jv τ + 1), n)
  | .shift τ false =>
    (Fin.cases (if 0 ≤ jv 0 - 1 ∧ jv 0 - 1 < d then [(.read, loS M 0, jv 0 - 1)] else [])
      (fun h => [(.write, hiS M h.succ, waddr M d h (jv h.succ + 1)),
        (.read, loS M h.succ, waddr M d h (jv h.succ - 1))]) τ,
      Function.update jv τ (jv τ - 1), n)
  | .flush => ([(.write, bufS M, (d : ℤ) + n)], jv, n + 1)

/-- The I/O sequence of an event word from window indices `jv` and flush count `n`. -/
def ioWords (d : ℕ) : (Fin (M.k + 1) → ℤ) → ℕ → List (Letter M.k) → List (IO (2 * M.k + 3))
  | _, _, [] => []
  | jv, n, ℓ :: ev =>
    (letterIO M d jv n ℓ).1 ++ ioWords d (letterIO M d jv n ℓ).2.1 (letterIO M d jv n ℓ).2.2 ev

/-! ### Invariant, specification and measure -/

/-- The symbol at cell `p` of tape `τ` in configuration `c` on input `w`. -/
def tsym (w : List Bool) (c : Config M) (τ : Fin (M.k + 1)) (p : ℤ) : Sym M :=
  Fin.cases (.inl (readInput w p)) (fun h => .inr (c.work h p)) τ

/-- The position of head `τ` in configuration `c`. -/
def hpos (c : Config M) (τ : Fin (M.k + 1)) : ℤ := Fin.cases c.inPos (fun h => c.workPos h) τ

/-- Block `jj` of work tape `h` in configuration `c`. -/
def workBlk {B : ℕ} (c : Config M) (h : Fin M.k) (jj : ℤ) : Block (Sym M) B :=
  fun q => .inr (c.work h (jj * B + q.val))

/-- The window indices after the pending shift, if any. -/
def ctrlJ (ρ : Reg M) : Fin (M.k + 1) → ℤ :=
  match ρ.ph with
  | .pend h true => Function.update ρ.j h.succ (ρ.j h.succ + 1)
  | .pend h false => Function.update ρ.j h.succ (ρ.j h.succ - 1)
  | _ => ρ.j

/-- The I/O that the current phase owes: the first read, or the second I/O of a shift. -/
def pendIO (d : ℕ) (ρ : Reg M) : List (IO (2 * M.k + 3)) :=
  match ρ.ph with
  | .start => [(.read, hiS M 0, 0)]
  | .run => []
  | .pend h true => [(.read, hiS M h.succ, waddr M d h (ρ.j h.succ + 2))]
  | .pend h false => [(.read, loS M h.succ, waddr M d h (ρ.j h.succ - 1))]

/-- A shift of tape `τ` is pending. -/
def pendOn (ρ : Reg M) (τ : Fin (M.k + 1)) : Bool :=
  match ρ.ph with
  | .pend h _ => decide (h.succ = τ)
  | _ => false

/-- The distance of head `τ` to the cells just outside its window (`B` if its shift is pending). -/
def dist (B : ℕ) (ρ : Reg M) (τ : Fin (M.k + 1)) : ℤ :=
  if pendOn M ρ τ then B else min (ρ.x τ - ρ.j τ * B + 1) ((ρ.j τ + 2) * B - ρ.x τ)

/-- The number of heads outside their windows. -/
def nOut (B : ℕ) (ρ : Reg M) : ℕ := (Finset.univ.filter (Outside M B ρ)).card

/-- The work left before the next step of `M`. -/
def emeas (B : ℕ) (ρ : Reg M) : ℕ :=
  match ρ.ph with
  | .start => 1
  | .run => 2 * nOut M B ρ + (if ρ.nbuf = B then 1 else 0)
  | .pend _ _ => 2 * nOut M B ρ - 1 + (if ρ.nbuf = B then 1 else 0)

/-- The termination measure at time `t` with halting time `Th`. -/
def meas (B Th t : ℕ) (ρ : Reg M) : ℕ := (Th - t) * (2 * M.k + 6) + emeas M B ρ

/-- Registers whose integers have absolute value at most `R`. -/
def Good (R : ℕ) (ρ : Reg M) : Prop :=
  (∀ τ, |ρ.x τ| ≤ R) ∧ (∀ τ, |ρ.j τ| ≤ R) ∧ ρ.nfl ≤ R ∧ ρ.nbuf ≤ R

/-- **The simulation invariant** at time `t` on input `w`. -/
structure Inv (d B : ℕ) (w : List Bool) (t : ℕ) (s : Slots M B × Reg M) (D : Disk (Sym M) B) :
    Prop where
  ph : s.2.ph ≠ .start
  st : s.2.st = (run M w t).state
  x : ∀ τ, s.2.x τ = hpos M (run M w t) τ
  win : ∀ τ p, s.2.j τ * B ≤ p → p < (s.2.j τ + 2) * B →
    view M s.1 τ (s.2.j τ) p = tsym M w (run M w t) τ p
  near : ∀ τ, s.2.j τ * B - 1 ≤ s.2.x τ ∧ s.2.x τ ≤ (s.2.j τ + 2) * B
  disk : ∀ h jj, jj ≠ s.2.j h.succ → jj ≠ s.2.j h.succ + 1 →
    D (waddr M d h jj) = workBlk M (run M w t) h jj
  rows : ∀ i : ℕ, i < d → D i = inputDisk (symAlph M) d B w i
  outs : ∀ n < s.2.nfl, D ((d : ℤ) + n) = rowBlock (symAlph M) B (run M w t).outRev.reverse n
  len : s.2.nfl * B + s.2.nbuf = (run M w t).outRev.length
  nbuf : s.2.nbuf ≤ B
  buf : ∀ q : Fin B, q.val < s.2.nbuf →
    s.1 (bufS M) q = .inl (some ((run M w t).outRev.reverse.getD (s.2.nfl * B + q.val) false))
  pendR : ∀ h, s.2.ph = .pend h true → s.2.x h.succ = (s.2.j h.succ + 2) * B ∧
    D (waddr M d h (s.2.j h.succ)) = workBlk M (run M w t) h (s.2.j h.succ)
  pendL : ∀ h, s.2.ph = .pend h false → s.2.x h.succ = s.2.j h.succ * B - 1 ∧
    D (waddr M d h (s.2.j h.succ + 1)) = workBlk M (run M w t) h (s.2.j h.succ + 1)

/-- **The specification** of the rest of a run from a state with register `ρ` at time `t`: its
I/O sequence is the owed I/O followed by the I/Os of an event word `ev`, every tape shifts at most
`(Th - t + B - dist)/B` more times, the flushes complete `d`, and the final disk holds the output
rows. -/
def Spec (d B : ℕ) (w : List Bool) (Th t : ℕ) (ρ : Reg M) (ios : List (IO (2 * M.k + 3)))
    (D' : Disk (Sym M) B) : Prop :=
  ∃ ev : List (Letter M.k),
    ios = pendIO M d ρ ++ ioWords M d (ctrlJ M ρ) ρ.nfl ev ∧
    (∀ τ, (B : ℤ) * cnt τ ev + dist M B ρ τ ≤ (Th : ℤ) - t + B) ∧
    nflush ev + ρ.nfl = d ∧
    ∀ n < d, D' ((d : ℤ) + n) = rowBlock (symAlph M) B (run M w Th).outRev.reverse n

end Defs

/-! ## Basic lemmas -/

section Basic

variable {M : TM} {B : ℕ}

@[simp] theorem loS_val (τ : Fin (M.k + 1)) : (loS M τ).val = 2 * τ.val := rfl
@[simp] theorem hiS_val (τ : Fin (M.k + 1)) : (hiS M τ).val = 2 * τ.val + 1 := rfl
@[simp] theorem bufS_val : (bufS M).val = 2 * M.k + 2 := rfl

theorem loS_ne_hiS (τ τ' : Fin (M.k + 1)) : loS M τ ≠ hiS M τ' := by
  intro h; have := congrArg Fin.val h; simp at this; omega

theorem hiS_ne_loS (τ τ' : Fin (M.k + 1)) : hiS M τ ≠ loS M τ' := fun h => loS_ne_hiS τ' τ h.symm

theorem loS_ne_bufS (τ : Fin (M.k + 1)) : loS M τ ≠ bufS M := by
  intro h; have := congrArg Fin.val h; have := τ.isLt; simp at *; omega

theorem hiS_ne_bufS (τ : Fin (M.k + 1)) : hiS M τ ≠ bufS M := by
  intro h; have := congrArg Fin.val h; have := τ.isLt; simp at *; omega

theorem loS_ne_loS {τ τ' : Fin (M.k + 1)} (h : τ ≠ τ') : loS M τ ≠ loS M τ' := by
  intro e; apply h; have := congrArg Fin.val e; simp at this; exact Fin.ext (by omega)

theorem hiS_ne_hiS {τ τ' : Fin (M.k + 1)} (h : τ ≠ τ') : hiS M τ ≠ hiS M τ' := by
  intro e; apply h; have := congrArg Fin.val e; simp at this; exact Fin.ext (by omega)

theorem tapeOf_loS (τ : Fin (M.k + 1)) : tapeOf M (loS M τ) = τ :=
  Fin.ext (by have := τ.isLt; simp [tapeOf]; omega)

theorem tapeOf_hiS (τ : Fin (M.k + 1)) : tapeOf M (hiS M τ) = τ :=
  Fin.ext (by have := τ.isLt; simp [tapeOf]; omega)

theorem getZ_eq (b : Block (Sym M) B) {o : ℤ} (h0 : 0 ≤ o) (h1 : o < B) :
    getZ b o = b ⟨o.toNat, by omega⟩ := by
  rw [getZ, dite_eq_left ⟨h0, h1⟩]

theorem getZ_natCast (b : Block (Sym M) B) (q : Fin B) : getZ b (q.val : ℤ) = b q := by
  rw [getZ_eq b (by omega) (by exact_mod_cast q.isLt)]
  congr 1

/-- The lower block of a window. -/
theorem view_lo (sl : Slots M B) (τ : Fin (M.k + 1)) (jj : ℤ) (q : Fin B) :
    view M sl τ jj (jj * B + q.val) = sl (loS M τ) q := by
  have hq := q.isLt
  have e : (jj + 1) * (B : ℤ) = jj * B + B := by ring
  rw [view, ite_eq_left (by omega), show jj * (B : ℤ) + q.val - jj * B = (q.val : ℤ) by ring,
    getZ_natCast]

/-- The upper block of a window. -/
theorem view_hi (sl : Slots M B) (τ : Fin (M.k + 1)) (jj : ℤ) (q : Fin B) :
    view M sl τ jj ((jj + 1) * B + q.val) = sl (hiS M τ) q := by
  rw [view, ite_eq_right (by omega),
    show (jj + 1) * (B : ℤ) + q.val - (jj + 1) * B = (q.val : ℤ) by ring, getZ_natCast]

/-- A window depends only on its two slots. -/
theorem view_congr {sl sl' : Slots M B} {τ : Fin (M.k + 1)} (h1 : sl' (loS M τ) = sl (loS M τ))
    (h2 : sl' (hiS M τ) = sl (hiS M τ)) (jj p : ℤ) : view M sl' τ jj p = view M sl τ jj p := by
  simp only [view, h1, h2]

/-- Updating another slot leaves a window unchanged. -/
theorem view_update_ne {sl : Slots M B} {τ : Fin (M.k + 1)} {i : Fin (2 * M.k + 3)}
    (h1 : i ≠ loS M τ) (h2 : i ≠ hiS M τ) (b : Block (Sym M) B) (jj p : ℤ) :
    view M (Function.update sl i b) τ jj p = view M sl τ jj p :=
  view_congr (Function.update_of_ne h1.symm _ _) (Function.update_of_ne h2.symm _ _) jj p

/-- The window after a right shift. -/
theorem view_shiftR (sl : Slots M B) (τ : Fin (M.k + 1)) (blk : Block (Sym M) B) (jj p : ℤ)
    (hp : (jj + 1) * B ≤ p) :
    view M (Function.update (Function.update sl (loS M τ) (sl (hiS M τ))) (hiS M τ) blk) τ (jj + 1) p =
      if p < (jj + 2) * B then view M sl τ jj p else getZ blk (p - (jj + 2) * B) := by
  have e1 : (jj + 1 + 1) * (B : ℤ) = (jj + 2) * B := by ring
  simp only [view, e1, Function.update_self, Function.update_of_ne (hiS_ne_loS τ τ).symm]
  split_ifs <;> first | rfl | omega

/-- The window after a left shift. -/
theorem view_shiftL (sl : Slots M B) (τ : Fin (M.k + 1)) (blk : Block (Sym M) B) (jj p : ℤ)
    (hp : p < (jj + 1) * B) :
    view M (Function.update (Function.update sl (hiS M τ) (sl (loS M τ))) (loS M τ) blk) τ (jj - 1) p =
      if p < jj * B then getZ blk (p - (jj - 1) * B) else view M sl τ jj p := by
  have e1 : (jj - 1 + 1) * (B : ℤ) = jj * B := by ring
  simp only [view, e1, Function.update_self, Function.update_of_ne (loS_ne_hiS τ τ).symm]
  split_ifs <;> rfl

/-- Packed windows. -/
theorem view_pack (jv : Fin (M.k + 1) → ℤ) (W : Fin (M.k + 1) → ℤ → Sym M) (buf : Block (Sym M) B)
    (τ : Fin (M.k + 1)) {p : ℤ} (hp0 : jv τ * B ≤ p) (hp1 : p < (jv τ + 2) * B) :
    view M (pack M jv W buf) τ (jv τ) p = W τ p := by
  have e1 : (jv τ + 2) * (B : ℤ) = jv τ * B + B + B := by ring
  have e2 : (jv τ + 1) * (B : ℤ) = jv τ * B + B := by ring
  unfold view
  split_ifs with h
  · rw [getZ_eq _ (by omega) (by omega)]
    simp only [pack, ite_eq_right (loS_ne_bufS τ), tapeOf_loS, loS_val, Nat.mul_mod_right,
      Nat.cast_zero, add_zero]
    congr 1
    omega
  · rw [getZ_eq _ (by omega) (by omega)]
    simp only [pack, ite_eq_right (hiS_ne_bufS τ), tapeOf_hiS, hiS_val]
    congr 1
    have : (2 * τ.val + 1) % 2 = 1 := by omega
    rw [this]
    push_cast
    omega

theorem pack_bufS (jv : Fin (M.k + 1) → ℤ) (W : Fin (M.k + 1) → ℤ → Sym M) (buf : Block (Sym M) B) :
    pack M jv W buf (bufS M) = buf := by
  funext q; simp [pack]

@[simp] theorem tsym_zero (w : List Bool) (c : Config M) (p : ℤ) :
    tsym M w c 0 p = .inl (readInput w p) := rfl

@[simp] theorem tsym_succ (w : List Bool) (c : Config M) (h : Fin M.k) (p : ℤ) :
    tsym M w c h.succ p = .inr (c.work h p) := rfl

@[simp] theorem hpos_zero (c : Config M) : hpos M c 0 = c.inPos := rfl

@[simp] theorem hpos_succ (c : Config M) (h : Fin M.k) : hpos M c h.succ = c.workPos h := rfl

theorem zz_nonneg (jj : ℤ) : 0 ≤ zz jj := by unfold zz; split_ifs <;> omega

theorem zz_inj {a b : ℤ} (h : zz a = zz b) : a = b := by unfold zz at h; split_ifs at h <;> omega

theorem waddr_ge (d : ℕ) (h : Fin M.k) (jj : ℤ) : 2 * (d : ℤ) ≤ waddr M d h jj := by
  have := zz_nonneg jj
  have : 0 ≤ (M.k : ℤ) * zz jj := mul_nonneg (by positivity) this
  unfold waddr; omega

theorem waddr_inj {d : ℕ} {h h' : Fin M.k} {a b : ℤ} (e : waddr M d h a = waddr M d h' b) :
    h = h' ∧ a = b := by
  unfold waddr at e
  have ha := zz_nonneg a
  have hb := zz_nonneg b
  have hh := h.isLt
  have hh' := h'.isLt
  have key : zz a = zz b := by
    rcases lt_trichotomy (zz a) (zz b) with hl | hl | hl
    · have : (M.k : ℤ) * zz a + M.k ≤ M.k * zz b := by nlinarith
      omega
    · exact hl
    · have : (M.k : ℤ) * zz b + M.k ≤ M.k * zz a := by nlinarith
      omega
  rw [key] at e
  exact ⟨Fin.ext (by omega), zz_inj key⟩

theorem waddr_ne_of_lt {d : ℕ} (h : Fin M.k) (jj : ℤ) {a : ℤ} (ha : a < 2 * d) :
    waddr M d h jj ≠ a := by
  have := waddr_ge (M := M) d h jj; omega

theorem firstOut_none {ρ : Reg M} (h : firstOut M B ρ = none) (τ : Fin (M.k + 1)) :
    ¬ Outside M B ρ τ := by
  intro hτ
  unfold firstOut at h
  rw [dite_eq_left ⟨τ, hτ⟩] at h
  cases h

theorem firstOut_some {ρ : Reg M} {τ : Fin (M.k + 1)} (h : firstOut M B ρ = some τ) :
    Outside M B ρ τ := by
  unfold firstOut at h
  split_ifs at h with hex
  cases h
  exact Fin.find_spec hex

end Basic

/-! ## One step of the simulator -/

section Step

variable {M : TM} {d B : ℕ} {w : List Bool} {Th t : ℕ} {s : Slots M B × Reg M}
  {D : Disk (Sym M) B}

theorem readInput_of_lt {p : ℤ} (hp0 : 0 ≤ p) (hp1 : p < w.length) :
    readInput w p = some (w.getD p.toNat false) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, p = n := ⟨p.toNat, by omega⟩
  have hn : n < w.length := by exact_mod_cast hp1
  rw [readInput_natCast, nth_eq_getElem?, List.getElem?_eq_getElem hn]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn]

theorem getZ_workBlk (c : Config M) (h : Fin M.k) (jj : ℤ) {o : ℤ} (h0 : 0 ≤ o) (h1 : o < B) :
    getZ (workBlk M (B := B) c h jj) o = .inr (c.work h (jj * B + o)) := by
  rw [getZ_eq _ h0 h1]
  simp only [workBlk]
  congr 2
  omega

theorem getZ_endBlk {o : ℤ} (h0 : 0 ≤ o) (h1 : o < B) : getZ (endBlk M B) o = .inl none := by
  rw [getZ_eq _ h0 h1]; rfl

theorem getZ_inputDisk {i o : ℤ} (hi0 : 0 ≤ i) (hi1 : i < d) (h0 : 0 ≤ o) (h1 : o < B) :
    getZ (inputDisk (symAlph M) d B w i) o = .inl (some (w.getD (i * B + o).toNat false)) := by
  rw [getZ_eq _ h0 h1]
  simp only [inputDisk, ite_eq_left (show 0 ≤ i ∧ i < d from ⟨hi0, hi1⟩), symAlph_bit]
  congr 3
  have : (0 : ℤ) ≤ i * B := mul_nonneg hi0 (by positivity)
  zify [Int.toNat_of_nonneg hi0, Int.toNat_of_nonneg h0, Int.toNat_of_nonneg this,
    Int.toNat_of_nonneg (add_nonneg this h0)]

theorem shift_sub_le (dr : Dir) (p : ℤ) : dr.shift p - p ≤ 1 ∧ p - dr.shift p ≤ 1 := by
  cases dr <;> simp [Dir.shift]

theorem inner_run (hph : s.2.ph = .run) : inner M d B s = runStep M d s := by
  simp [inner, hph]

theorem nOut_le (ρ : Reg M) : nOut M B ρ ≤ M.k + 1 := by
  unfold nOut
  exact (Finset.card_filter_le _ _).trans (by simp)

theorem nOut_pos {ρ : Reg M} {τ : Fin (M.k + 1)} (h : Outside M B ρ τ) : 0 < nOut M B ρ :=
  Finset.card_pos.mpr ⟨τ, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact h⟩

theorem nOut_congr {ρ ρ' : Reg M} (h : ∀ τ, Outside M B ρ' τ ↔ Outside M B ρ τ) :
    nOut M B ρ' = nOut M B ρ := by
  unfold nOut; congr 1; ext τ; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact h τ

theorem nOut_succ {ρ ρ' : Reg M} {τ : Fin (M.k + 1)} (hτ : Outside M B ρ τ)
    (hτ' : ¬ Outside M B ρ' τ) (h : ∀ τ', τ' ≠ τ → (Outside M B ρ' τ' ↔ Outside M B ρ τ')) :
    nOut M B ρ' + 1 = nOut M B ρ := by
  unfold nOut
  have e : Finset.univ.filter (Outside M B ρ') = (Finset.univ.filter (Outside M B ρ)).erase τ := by
    ext τ'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    by_cases hτ'' : τ' = τ
    · subst hτ''; simp [hτ']
    · simp [hτ'', h τ' hτ'']
  have hmem : τ ∈ Finset.univ.filter (Outside M B ρ) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hτ
  rw [e, Finset.card_erase_of_mem hmem]
  have := Finset.card_pos.mpr ⟨τ, hmem⟩
  omega

theorem emeas_run {ρ : Reg M} (h : ρ.ph = .run) :
    emeas M B ρ = 2 * nOut M B ρ + (if ρ.nbuf = B then 1 else 0) := by
  simp [emeas, h]

theorem emeas_pend {ρ : Reg M} {hh : Fin M.k} {r : Bool} (h : ρ.ph = .pend hh r) :
    emeas M B ρ = 2 * nOut M B ρ - 1 + (if ρ.nbuf = B then 1 else 0) := by
  simp [emeas, h]

theorem emeas_le (ρ : Reg M) : emeas M B ρ ≤ 2 * M.k + 3 := by
  have := nOut_le (B := B) ρ
  unfold emeas
  split <;> (try split_ifs) <;> omega

theorem dist_run {ρ : Reg M} (h : ρ.ph = .run) (τ : Fin (M.k + 1)) :
    dist M B ρ τ = min (ρ.x τ - ρ.j τ * B + 1) ((ρ.j τ + 2) * B - ρ.x τ) := by
  simp [dist, pendOn, h]

theorem Inv.nfl_le (hout : (run M w Th).outRev.length = d * B) (ht : t ≤ Th)
    (hI : Inv M d B w t s D) : s.2.nfl * B + s.2.nbuf ≤ d * B := by
  rw [hI.len, ← hout]; exact outRev_length_mono w ht

theorem Inv.good (hB : 0 < B) (R : ℕ) (hR : Th + 2 ≤ R) (ht : t ≤ Th) (hI : Inv M d B w t s D) :
    Good M R s.2 := by
  have hx : ∀ τ, |s.2.x τ| ≤ t := by
    intro τ
    rw [hI.x τ]
    induction τ using Fin.cases with
    | zero => exact abs_inPos_le w t
    | succ h => exact abs_workPos_le w t h
  have hlen := outLen_le_self (M := M) w t
  refine ⟨fun τ => (hx τ).trans (by omega), fun τ => ?_, ?_, ?_⟩
  · have h1 := hx τ
    obtain ⟨n1, n2⟩ := hI.near τ
    rw [abs_le] at h1 ⊢
    have hB' : (1 : ℤ) ≤ B := by exact_mod_cast hB
    constructor
    · by_contra hc
      have : (s.2.j τ + 2) * B ≤ s.2.j τ + 2 := by nlinarith
      omega
    · by_contra hc
      have : s.2.j τ ≤ s.2.j τ * B := by nlinarith
      omega
  · have := hI.len
    have : s.2.nfl ≤ s.2.nfl * B := Nat.le_mul_of_pos_right _ hB
    omega
  · have := hI.len
    omega

theorem inside_of {ρ : Reg M} {τ : Fin (M.k + 1)} (h : ¬ Outside M B ρ τ) :
    ρ.j τ * B ≤ ρ.x τ ∧ ρ.x τ < (ρ.j τ + 2) * B := by
  simp only [Outside, not_or, not_lt, not_le] at h
  exact ⟨h.1, h.2⟩

/-- With all heads inside their windows, the simulator applies the transition function to the
true configuration. -/
theorem delta_eq (hI : Inv M d B w t s D) (hfo : firstOut M B s.2 = none) :
    M.δ s.2.st (inSymOf M s) (workSymOf M s) = transAt M w t := by
  have hin := fun τ => inside_of (firstOut_none hfo τ)
  unfold transAt inSym headSym
  rw [hI.st]
  congr 1
  · rw [inSymOf, hI.win 0 _ (hin 0).1 (hin 0).2, hI.x 0]
    rfl
  · funext h
    rw [workSymOf, hI.win h.succ _ (hin h.succ).1 (hin h.succ).2, hI.x h.succ]
    rfl

variable (M d B w Th) in
/-- One step of the simulator from a state satisfying the invariant at time `t`: it halts with the
final specification, or it moves (internally or by an I/O) to a state satisfying the invariant
with a smaller measure, and the specification of the rest transfers back. -/
def Next (t : ℕ) (s : Slots M B × Reg M) (D : Disk (Sym M) B) : Prop :=
  (inner M d B s = .halt ∧ Spec M d B w Th t s.2 [] D) ∨
  (∃ s' t', inner M d B s = .tau s' ∧ t' ≤ Th ∧ Inv M d B w t' s' D ∧
    meas M B Th t' s'.2 < meas M B Th t s.2 ∧
    ∀ ios D', Spec M d B w Th t' s'.2 ios D' → Spec M d B w Th t s.2 ios D') ∨
  (∃ i a s', inner M d B s = .io .read i a s' ∧
    Inv M d B w t (Function.update s'.1 i (D a), s'.2) D ∧
    meas M B Th t s'.2 < meas M B Th t s.2 ∧
    ∀ ios D', Spec M d B w Th t s'.2 ios D' → Spec M d B w Th t s.2 ((.read, i, a) :: ios) D') ∨
  (∃ i a s', inner M d B s = .io .write i a s' ∧
    Inv M d B w t s' (Function.update D a (s'.1 i)) ∧
    meas M B Th t s'.2 < meas M B Th t s.2 ∧
    ∀ ios D', Spec M d B w Th t s'.2 ios D' → Spec M d B w Th t s.2 ((.write, i, a) :: ios) D')

/-- `M` halts: so does the simulator, and the specification holds. -/
theorem next_halt (hB : 0 < B) (hout : (run M w Th).outRev.length = d * B)
    (hTh : HaltsAt M w Th) (ht : t ≤ Th) (hI : Inv M d B w t s D) (hph : s.2.ph = .run)
    (hfo : firstOut M B s.2 = none) (hnb : s.2.nbuf ≠ B) (hδ : transAt M w t = none) :
    Next M d B w Th t s D := by
  have htT : t = Th := by
    by_contra hne
    exact hTh.1 t (lt_of_le_of_ne ht hne) hδ
  subst htT
  have hfin : s.2.nfl = d ∧ s.2.nbuf = 0 := by
    have h1 := hI.len
    rw [hout] at h1
    have h2 := hI.nbuf
    have h3 : s.2.nbuf < B := lt_of_le_of_ne h2 hnb
    have h4 : s.2.nfl = d := by
      rcases lt_trichotomy s.2.nfl d with h | h | h
      · have : (s.2.nfl + 1) * B ≤ d * B := Nat.mul_le_mul_right _ h
        nlinarith
      · exact h
      · have : (d + 1) * B ≤ s.2.nfl * B := Nat.mul_le_mul_right _ h
        nlinarith
    subst h4
    exact ⟨rfl, by omega⟩
  left
  refine ⟨?_, [], ?_, ?_, ?_, ?_⟩
  · rw [inner_run hph]
    simp only [runStep, hfo, hnb, ↓reduceIte, delta_eq hI hfo, hδ]
  · simp [pendIO, hph, ioWords]
  · intro τ
    have := hI.near τ
    have e : (s.2.j τ + 2) * (B : ℤ) = s.2.j τ * B + 2 * B := by ring
    simp only [cnt, List.countP_nil, Nat.cast_zero, mul_zero, zero_add, dist_run hph, sub_self]
    omega
  · simp [nflush, hfin.1]
  · intro n hn
    exact hI.outs n (hfin.1 ▸ hn)

/-- The buffer is full: flush it. -/
theorem next_flush (hB : 0 < B) (hout : (run M w Th).outRev.length = d * B) (ht : t ≤ Th)
    (hI : Inv M d B w t s D) (hph : s.2.ph = .run) (hfo : firstOut M B s.2 = none)
    (hnb : s.2.nbuf = B) : Next M d B w Th t s D := by
  have hnfl : s.2.nfl + 1 ≤ d := by
    have h1 := hI.nfl_le hout ht
    rw [hnb] at h1
    by_contra hc
    have : d * B < (s.2.nfl + 1) * B := Nat.mul_lt_mul_of_pos_right (by omega) hB
    nlinarith
  right; right; right
  refine ⟨bufS M, (d : ℤ) + s.2.nfl, (s.1, { s.2 with nfl := s.2.nfl + 1, nbuf := 0 }),
    ?_, ?_, ?_, ?_⟩
  · rw [inner_run hph]
    simp only [runStep, hfo, hnb, ↓reduceIte]
  · exact {
      ph := hI.ph
      st := hI.st
      x := hI.x
      win := hI.win
      near := hI.near
      disk := fun h jj h1 h2 => by
        rw [Function.update_of_ne (waddr_ne_of_lt h jj (by omega)), hI.disk h jj h1 h2]
      rows := fun i hi => by
        rw [Function.update_of_ne (by omega), hI.rows i hi]
      outs := fun n hn => by
        rcases Nat.lt_succ_iff_lt_or_eq.mp hn with hn | rfl
        · rw [Function.update_of_ne (by omega), hI.outs n hn]
        · rw [Function.update_self]
          funext q
          rw [hI.buf q (by rw [hnb]; exact q.isLt)]
          simp [rowBlock, symAlph_bit]
      len := by
        show (s.2.nfl + 1) * B + 0 = _
        rw [← hI.len, hnb]; ring
      nbuf := Nat.zero_le _
      buf := fun q hq => absurd hq (Nat.not_lt_zero _)
      pendR := fun h hh => by simp [hph] at hh
      pendL := fun h hh => by simp [hph] at hh }
  · show meas M B Th t { s.2 with nfl := s.2.nfl + 1, nbuf := 0 } < meas M B Th t s.2
    unfold meas
    rw [emeas_run hph, emeas_run (ρ := { s.2 with nfl := s.2.nfl + 1, nbuf := 0 }) hph,
      nOut_congr (ρ := s.2) (ρ' := { s.2 with nfl := s.2.nfl + 1, nbuf := 0 }) (fun _ => Iff.rfl),
      hnb]
    simp only [↓reduceIte, show (0 : ℕ) ≠ B by omega]
    omega
  · rintro ios D' ⟨ev, hios, hcnt, hfl, hrows⟩
    refine ⟨.flush :: ev, ?_, ?_, ?_, hrows⟩
    · simp only [pendIO, ctrlJ, hph] at hios ⊢
      simp [hios, ioWords, letterIO]
    · intro τ
      have := hcnt τ
      have e : dist M B { s.2 with nfl := s.2.nfl + 1, nbuf := 0 } τ = dist M B s.2 τ := rfl
      rw [e] at this
      simpa [cnt, Letter.tape] using this
    · simp only [nflush, List.countP_cons, Letter.tape] at hfl ⊢
      simp only [decide_true, ↓reduceIte] at *
      omega

theorem block_ne_of_window {jj jw x : ℤ} {q : ℕ} (hB : 0 < B) (hq : q < B) (h1 : jj ≠ jw)
    (h2 : jj ≠ jw + 1) (hx0 : jw * B ≤ x) (hx1 : x < (jw + 2) * B) : jj * B + q ≠ x := by
  have hB' : (0 : ℤ) ≤ B := by positivity
  have hq' : (q : ℤ) < B := by exact_mod_cast hq
  rcases lt_or_gt_of_ne h1 with h | h
  · have : (jj + 1) * (B : ℤ) ≤ jw * B := mul_le_mul_of_nonneg_right (by omega) hB'
    have e : (jj + 1) * (B : ℤ) = jj * B + B := by ring
    omega
  · have : (jw + 2) * (B : ℤ) ≤ jj * B := mul_le_mul_of_nonneg_right (by omega) hB'
    have : (0 : ℤ) ≤ q := by positivity
    omega

/-- All heads inside, buffer not full, `M` steps: the simulator performs the step internally. -/
theorem next_step (hB : 0 < B) (hTh : HaltsAt M w Th) (ht : t ≤ Th) (hI : Inv M d B w t s D)
    (hph : s.2.ph = .run) (hfo : firstOut M B s.2 = none) (hnb : s.2.nbuf ≠ B)
    {st' : Fin (M.q + 1)} {dIn : Dir} {acts : Fin M.k → Fin (M.g + 1) × Dir} {o : Option Bool}
    (hδ : transAt M w t = some (st', dIn, acts, o)) : Next M d B w Th t s D := by
  have htT : t < Th := lt_of_le_of_ne ht (fun e => by rw [e, hTh.2] at hδ; cases hδ)
  have hrun := run_succ_of_some hδ
  have hin := fun τ => inside_of (firstOut_none hfo τ)
  have hout1 : (run M w (t + 1)).outRev.reverse = (run M w t).outRev.reverse ++ o.toList := by
    rw [run_succ_outRev_reverse]; simp [outBit, hδ]
  have hlen1 : (run M w (t + 1)).outRev.length =
      (run M w t).outRev.length + (if o.isSome then 1 else 0) := by
    rw [← List.length_reverse, hout1, List.length_append, List.length_reverse]
    cases o <;> simp
  have hx' : ∀ τ, (tmStep M s st' dIn acts o).2.x τ - s.2.x τ ≤ 1 ∧
      s.2.x τ - (tmStep M s st' dIn acts o).2.x τ ≤ 1 := by
    intro τ
    induction τ using Fin.cases with
    | zero => exact shift_sub_le dIn _
    | succ h => exact shift_sub_le (acts h).2 _
  have hlenR : (run M w t).outRev.reverse.length = s.2.nfl * B + s.2.nbuf := by
    rw [List.length_reverse, hI.len]
  right; left
  refine ⟨tmStep M s st' dIn acts o, t + 1, ?_, htT, ?_, ?_, ?_⟩
  · rw [inner_run hph]
    simp only [runStep, hfo, hnb, ↓reduceIte, delta_eq hI hfo, hδ]
  · exact {
      ph := hI.ph
      st := by rw [hrun]; rfl
      x := fun τ => by
        induction τ using Fin.cases with
        | zero => simp [tmStep, hrun, hI.x 0]
        | succ h => simp [tmStep, hrun, hI.x h.succ]
      win := fun τ p hp0 hp1 => by
        simp only [tmStep] at hp0 hp1 ⊢
        rw [view_pack _ _ _ τ hp0 hp1]
        induction τ using Fin.cases with
        | zero => simp [hI.win 0 p hp0 hp1]
        | succ h =>
          have hxh := hI.x h.succ
          simp only [hpos_succ] at hxh
          simp only [ne_eq, Fin.succ_ne_zero, not_false_eq_true, true_and, tsym_succ, hrun]
          by_cases hp : p = s.2.x h.succ
          · have hp' : p = (run M w t).workPos h := hp.trans hxh
            rw [ite_eq_left hp, ite_eq_left hp']
            simp [wsym]
          · have hp' : p ≠ (run M w t).workPos h := fun e => hp (e.trans hxh.symm)
            rw [ite_eq_right hp, ite_eq_right hp', hI.win h.succ p hp0 hp1]
            rfl
      near := fun τ => by
        have h1 := hx' τ
        have h2 := hin τ
        show s.2.j τ * B - 1 ≤ _ ∧ _ ≤ (s.2.j τ + 2) * B
        omega
      disk := fun h jj h1 h2 => by
        rw [hI.disk h jj h1 h2]
        funext q
        have hxh := hI.x h.succ
        simp only [hpos_succ] at hxh
        have hne := block_ne_of_window hB q.isLt h1 h2 (hin h.succ).1 (hin h.succ).2
        rw [hxh] at hne
        simp only [workBlk, hrun]
        rw [ite_eq_right hne]
      rows := hI.rows
      outs := fun n hn => by
        rw [hI.outs n hn, hout1]
        funext q
        simp only [rowBlock]
        have hq := q.isLt
        have : (n + 1) * B ≤ s.2.nfl * B := Nat.mul_le_mul_right _ hn
        rw [List.getD_append _ _ _ _ (by rw [hlenR]; nlinarith)]
      len := by
        show s.2.nfl * B + (s.2.nbuf + (if o.isSome then 1 else 0)) = _
        rw [hlen1, ← hI.len]; ring
      nbuf := by
        show s.2.nbuf + (if o.isSome then 1 else 0) ≤ B
        have := lt_of_le_of_ne hI.nbuf hnb
        split_ifs <;> omega
      buf := fun q hq => by
        rw [hout1]
        cases o with
        | none =>
          simp only [tmStep, pack_bufS, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
            add_zero] at hq ⊢
          rw [hI.buf q hq, Option.toList_none, List.append_nil]
        | some b =>
          simp only [tmStep, pack_bufS, Option.isSome_some, ↓reduceIte, Option.toList_some] at hq ⊢
          split_ifs with hqe
          · rw [hqe, List.getD_append_right _ _ _ _ (by rw [hlenR]), hlenR]
            simp
          · rw [hI.buf q (by omega), List.getD_append _ _ _ _ (by rw [hlenR]; omega)]
      pendR := fun h hh => by simp [tmStep, hph] at hh
      pendL := fun h hh => by simp [tmStep, hph] at hh }
  · show meas M B Th (t + 1) (tmStep M s st' dIn acts o).2 < meas M B Th t s.2
    unfold meas
    have h1 := emeas_le (B := B) (tmStep M s st' dIn acts o).2
    have h2 : Th - t = (Th - (t + 1)) + 1 := by omega
    rw [h2, add_mul, one_mul]
    omega
  · rintro ios D' ⟨ev, hios, hcnt, hfl, hrows⟩
    refine ⟨ev, ?_, ?_, hfl, hrows⟩
    · rw [hios]; rfl
    · intro τ
      have h1 := hcnt τ
      have h2 := hx' τ
      rw [dist_run (ρ := (tmStep M s st' dIn acts o).2) hph] at h1
      rw [dist_run hph]
      push_cast at h1 ⊢
      have e : (tmStep M s st' dIn acts o).2.j τ = s.2.j τ := rfl
      rw [e] at h1
      omega

theorem mulB (jj : ℤ) (B : ℕ) : (jj + 1) * (B : ℤ) = jj * B + B ∧ (jj + 2) * (B : ℤ) = jj * B + 2 * B ∧
    (jj + 3) * (B : ℤ) = jj * B + 3 * B ∧ (jj - 1) * (B : ℤ) = jj * B - B ∧
    (jj + 1 + 2) * (B : ℤ) = jj * B + 3 * B ∧ (jj - 1 + 2) * (B : ℤ) = jj * B + B := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring

/-- The invariant after a completed right shift of tape `τ`. -/
theorem inv_shiftR (hI : Inv M d B w t s D) {τ : Fin (M.k + 1)}
    (hx : s.2.x τ = (s.2.j τ + 2) * B) (blk : Block (Sym M) B)
    (hblk : ∀ p, (s.2.j τ + 2) * B ≤ p → p < (s.2.j τ + 3) * B →
      getZ blk (p - (s.2.j τ + 2) * B) = tsym M w (run M w t) τ p)
    (hdisk : ∀ h : Fin M.k, h.succ = τ →
      D (waddr M d h (s.2.j τ)) = workBlk M (run M w t) h (s.2.j τ)) :
    Inv M d B w t (Function.update (Function.update s.1 (loS M τ) (s.1 (hiS M τ))) (hiS M τ) blk,
      { s.2 with j := Function.update s.2.j τ (s.2.j τ + 1), ph := .run }) D := by
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := mulB (s.2.j τ) B
  exact {
    ph := by simp
    st := hI.st
    x := hI.x
    win := fun τ' p hp0 hp1 => by
      simp only at hp0 hp1 ⊢
      by_cases hτ : τ' = τ
      · subst hτ
        simp only [Function.update_self] at hp0 hp1 ⊢
        rw [view_shiftR _ _ _ _ _ hp0]
        split_ifs with hp
        · exact hI.win τ' p (by omega) hp
        · exact hblk p (by omega) (by omega)
      · rw [Function.update_of_ne hτ, view_update_ne (hiS_ne_loS τ τ') (hiS_ne_hiS (Ne.symm hτ)),
          view_update_ne (loS_ne_loS (Ne.symm hτ)) (loS_ne_hiS τ τ')]
        rw [Function.update_of_ne hτ] at hp0 hp1
        exact hI.win τ' p hp0 hp1
    near := fun τ' => by
      simp only
      by_cases hτ : τ' = τ
      · subst hτ
        simp only [Function.update_self]
        omega
      · rw [Function.update_of_ne hτ]
        exact hI.near τ'
    disk := fun h jj h1 h2 => by
      simp only at h1 h2
      by_cases e : h.succ = τ
      · subst e
        simp only [Function.update_self] at h1 h2
        by_cases hj : jj = s.2.j h.succ
        · subst hj; exact hdisk h rfl
        · exact hI.disk h jj hj h1
      · rw [Function.update_of_ne e] at h1 h2
        exact hI.disk h jj h1 h2
    rows := hI.rows
    outs := hI.outs
    len := hI.len
    nbuf := hI.nbuf
    buf := fun q hq => by
      simp only
      rw [Function.update_of_ne (hiS_ne_bufS τ).symm, Function.update_of_ne (loS_ne_bufS τ).symm]
      exact hI.buf q hq
    pendR := fun h hh => by simp at hh
    pendL := fun h hh => by simp at hh }

/-- The invariant after a completed left shift of tape `τ`. -/
theorem inv_shiftL (hI : Inv M d B w t s D) {τ : Fin (M.k + 1)}
    (hx : s.2.x τ = s.2.j τ * B - 1) (blk : Block (Sym M) B)
    (hblk : ∀ p, (s.2.j τ - 1) * B ≤ p → p < s.2.j τ * B →
      getZ blk (p - (s.2.j τ - 1) * B) = tsym M w (run M w t) τ p)
    (hdisk : ∀ h : Fin M.k, h.succ = τ →
      D (waddr M d h (s.2.j τ + 1)) = workBlk M (run M w t) h (s.2.j τ + 1)) :
    Inv M d B w t (Function.update (Function.update s.1 (hiS M τ) (s.1 (loS M τ))) (loS M τ) blk,
      { s.2 with j := Function.update s.2.j τ (s.2.j τ - 1), ph := .run }) D := by
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := mulB (s.2.j τ) B
  exact {
    ph := by simp
    st := hI.st
    x := hI.x
    win := fun τ' p hp0 hp1 => by
      simp only at hp0 hp1 ⊢
      by_cases hτ : τ' = τ
      · subst hτ
        simp only [Function.update_self] at hp0 hp1 ⊢
        rw [view_shiftL _ _ _ _ _ (by omega)]
        split_ifs with hp
        · exact hblk p hp0 hp
        · exact hI.win τ' p (by omega) (by omega)
      · rw [Function.update_of_ne hτ, view_update_ne (loS_ne_loS (Ne.symm hτ)) (loS_ne_hiS τ τ'),
          view_update_ne (hiS_ne_loS τ τ') (hiS_ne_hiS (Ne.symm hτ))]
        rw [Function.update_of_ne hτ] at hp0 hp1
        exact hI.win τ' p hp0 hp1
    near := fun τ' => by
      simp only
      by_cases hτ : τ' = τ
      · subst hτ
        simp only [Function.update_self]
        omega
      · rw [Function.update_of_ne hτ]
        exact hI.near τ'
    disk := fun h jj h1 h2 => by
      simp only at h1 h2
      by_cases e : h.succ = τ
      · subst e
        simp only [Function.update_self, sub_add_cancel] at h1 h2
        by_cases hj : jj = s.2.j h.succ + 1
        · subst hj; exact hdisk h rfl
        · exact hI.disk h jj h2 hj
      · rw [Function.update_of_ne e] at h1 h2
        exact hI.disk h jj h1 h2
    rows := hI.rows
    outs := hI.outs
    len := hI.len
    nbuf := hI.nbuf
    buf := fun q hq => by
      simp only
      rw [Function.update_of_ne (loS_ne_bufS τ).symm, Function.update_of_ne (hiS_ne_bufS τ).symm]
      exact hI.buf q hq
    pendR := fun h hh => by simp at hh
    pendL := fun h hh => by simp at hh }

theorem pendOn_run {ρ : Reg M} (h : ρ.ph = .run) (τ : Fin (M.k + 1)) : pendOn M ρ τ = false := by
  simp [pendOn, h]

theorem pendOn_pend {ρ : Reg M} {h : Fin M.k} {r : Bool} (hph : ρ.ph = .pend h r)
    {τ : Fin (M.k + 1)} (hτ : τ ≠ h.succ) : pendOn M ρ τ = false := by
  simp [pendOn, hph, Ne.symm hτ]

theorem dist_shiftR {ρ : Reg M} {τ : Fin (M.k + 1)} (hx : ρ.x τ = (ρ.j τ + 2) * B) :
    dist M B { ρ with j := Function.update ρ.j τ (ρ.j τ + 1), ph := .run } τ = B := by
  rw [dist_run rfl]
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := mulB (ρ.j τ) B
  simp only [Function.update_self, hx]
  omega

theorem dist_shiftL {ρ : Reg M} {τ : Fin (M.k + 1)} (hx : ρ.x τ = ρ.j τ * B - 1) :
    dist M B { ρ with j := Function.update ρ.j τ (ρ.j τ - 1), ph := .run } τ = B := by
  rw [dist_run rfl]
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := mulB (ρ.j τ) B
  simp only [Function.update_self, hx]
  omega

theorem dist_shift_ne {ρ : Reg M} {τ τ' : Fin (M.k + 1)} (hτ : τ' ≠ τ) (v : ℤ)
    (hp : pendOn M ρ τ' = false) :
    dist M B { ρ with j := Function.update ρ.j τ v, ph := .run } τ' = dist M B ρ τ' := by
  rw [dist_run rfl]
  simp [dist, hp, Function.update_of_ne hτ]

theorem dist_outR {ρ : Reg M} (hph : ρ.ph = .run) {τ : Fin (M.k + 1)}
    (hx : ρ.x τ = (ρ.j τ + 2) * B) : dist M B ρ τ = 0 := by
  rw [dist_run hph, hx]
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := mulB (ρ.j τ) B
  omega

theorem dist_outL {ρ : Reg M} (hph : ρ.ph = .run) {τ : Fin (M.k + 1)}
    (hx : ρ.x τ = ρ.j τ * B - 1) : dist M B ρ τ = 0 := by
  rw [dist_run hph, hx]
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := mulB (ρ.j τ) B
  omega

theorem dist_pend {ρ : Reg M} {h : Fin M.k} {r : Bool} (hph : ρ.ph = .pend h r) :
    dist M B ρ h.succ = B := by
  simp [dist, pendOn, hph]

theorem nOut_shiftR (hB : 0 < B) {ρ : Reg M} {τ : Fin (M.k + 1)} (hx : ρ.x τ = (ρ.j τ + 2) * B)
    (ph : Phase M.k) :
    nOut M B { ρ with j := Function.update ρ.j τ (ρ.j τ + 1), ph := ph } + 1 = nOut M B ρ := by
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := mulB (ρ.j τ) B
  have hB' : (0 : ℤ) < B := by exact_mod_cast hB
  refine nOut_succ (τ := τ) (Or.inr hx.ge) ?_ fun τ' hτ' => ?_
  · simp only [Outside, Function.update_self, hx, not_or, not_lt, not_le]
    omega
  · simp only [Outside, Function.update_of_ne hτ']

theorem nOut_shiftL (hB : 0 < B) {ρ : Reg M} {τ : Fin (M.k + 1)} (hx : ρ.x τ = ρ.j τ * B - 1)
    (ph : Phase M.k) :
    nOut M B { ρ with j := Function.update ρ.j τ (ρ.j τ - 1), ph := ph } + 1 = nOut M B ρ := by
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := mulB (ρ.j τ) B
  have hB' : (0 : ℤ) < B := by exact_mod_cast hB
  refine nOut_succ (τ := τ) (Or.inl (by omega)) ?_ fun τ' hτ' => ?_
  · simp only [Outside, Function.update_self, hx, not_or, not_lt, not_le]
    omega
  · simp only [Outside, Function.update_of_ne hτ']

theorem cnt_cons_self {k : ℕ} (τ : Fin (k + 1)) (r : Bool) (ev : List (Letter k)) :
    cnt τ (.shift τ r :: ev) = cnt τ ev + 1 := by
  simp [cnt, Letter.tape]

theorem cnt_cons_ne {k : ℕ} {τ τ' : Fin (k + 1)} (h : τ' ≠ τ) (r : Bool) (ev : List (Letter k)) :
    cnt τ' (.shift τ r :: ev) = cnt τ' ev := by
  simp [cnt, Letter.tape, Ne.symm h]

theorem nflush_cons_shift {k : ℕ} (τ : Fin (k + 1)) (r : Bool) (ev : List (Letter k)) :
    nflush (.shift τ r :: ev) = nflush ev := by
  simp [nflush, Letter.tape]

/-- Counting through a shift of tape `τ` whose letter is added to the event word. -/
theorem count_shift {ρ ρ' : Reg M} {τ : Fin (M.k + 1)} {r : Bool} {ev : List (Letter M.k)}
    (h0 : dist M B ρ τ = 0) (h1 : dist M B ρ' τ = B)
    (hne : ∀ τ', τ' ≠ τ → dist M B ρ' τ' = dist M B ρ τ')
    (hc : ∀ τ', (B : ℤ) * cnt τ' ev + dist M B ρ' τ' ≤ (Th : ℤ) - t + B) (τ' : Fin (M.k + 1)) :
    (B : ℤ) * cnt τ' (.shift τ r :: ev) + dist M B ρ τ' ≤ (Th : ℤ) - t + B := by
  by_cases e : τ' = τ
  · subst e
    have := hc τ'
    rw [cnt_cons_self, h0]
    rw [h1] at this
    push_cast
    linarith
  · rw [cnt_cons_ne e, ← hne τ' e]
    exact hc τ'

/-- The specification through an input shift to the right. -/
theorem spec_inR (hph : s.2.ph = .run) (hx : s.2.x 0 = (s.2.j 0 + 2) * B)
    {ios : List (IO (2 * M.k + 3))} {D' : Disk (Sym M) B}
    (hs : Spec M d B w Th t
      { s.2 with j := Function.update s.2.j 0 (s.2.j 0 + 1), ph := .run } ios D') :
    Spec M d B w Th t s.2 ((if 0 ≤ s.2.j 0 + 2 ∧ s.2.j 0 + 2 < d then
      [(.read, hiS M 0, s.2.j 0 + 2)] else []) ++ ios) D' := by
  obtain ⟨ev, hios, hcnt, hfl, hrows⟩ := hs
  refine ⟨.shift 0 true :: ev, ?_, count_shift (dist_outR hph hx) (dist_shiftR hx)
    (fun τ' h => dist_shift_ne h _ (pendOn_run hph τ')) hcnt, ?_, hrows⟩
  · rw [hios]
    simp [pendIO, ctrlJ, hph, ioWords, letterIO]
  · rw [nflush_cons_shift]; exact hfl

/-- The specification through an input shift to the left. -/
theorem spec_inL (hph : s.2.ph = .run) (hx : s.2.x 0 = s.2.j 0 * B - 1)
    {ios : List (IO (2 * M.k + 3))} {D' : Disk (Sym M) B}
    (hs : Spec M d B w Th t
      { s.2 with j := Function.update s.2.j 0 (s.2.j 0 - 1), ph := .run } ios D') :
    Spec M d B w Th t s.2 ((if 0 ≤ s.2.j 0 - 1 ∧ s.2.j 0 - 1 < d then
      [(.read, loS M 0, s.2.j 0 - 1)] else []) ++ ios) D' := by
  obtain ⟨ev, hios, hcnt, hfl, hrows⟩ := hs
  refine ⟨.shift 0 false :: ev, ?_, count_shift (dist_outL hph hx) (dist_shiftL hx)
    (fun τ' h => dist_shift_ne h _ (pendOn_run hph τ')) hcnt, ?_, hrows⟩
  · rw [hios]
    simp [pendIO, ctrlJ, hph, ioWords, letterIO]
  · rw [nflush_cons_shift]; exact hfl

/-- The specification through the first I/O of a right shift of a work tape. -/
theorem spec_wR (hph : s.2.ph = .run) {h : Fin M.k}
    (hx : s.2.x h.succ = (s.2.j h.succ + 2) * B) {ios : List (IO (2 * M.k + 3))}
    {D' : Disk (Sym M) B} (hs : Spec M d B w Th t { s.2 with ph := .pend h true } ios D') :
    Spec M d B w Th t s.2 ((.write, loS M h.succ, waddr M d h (s.2.j h.succ)) :: ios) D' := by
  obtain ⟨ev, hios, hcnt, hfl, hrows⟩ := hs
  refine ⟨.shift h.succ true :: ev, ?_, count_shift (dist_outR hph hx) (dist_pend rfl)
    (fun τ' hτ' => ?_) hcnt, ?_, hrows⟩
  · rw [hios]
    simp [pendIO, ctrlJ, hph, ioWords, letterIO]
  · simp [dist, pendOn, hph, Ne.symm hτ']
  · rw [nflush_cons_shift]; exact hfl

/-- The specification through the first I/O of a left shift of a work tape. -/
theorem spec_wL (hph : s.2.ph = .run) {h : Fin M.k}
    (hx : s.2.x h.succ = s.2.j h.succ * B - 1) {ios : List (IO (2 * M.k + 3))}
    {D' : Disk (Sym M) B} (hs : Spec M d B w Th t { s.2 with ph := .pend h false } ios D') :
    Spec M d B w Th t s.2 ((.write, hiS M h.succ, waddr M d h (s.2.j h.succ + 1)) :: ios) D' := by
  obtain ⟨ev, hios, hcnt, hfl, hrows⟩ := hs
  refine ⟨.shift h.succ false :: ev, ?_, count_shift (dist_outL hph hx) (dist_pend rfl)
    (fun τ' hτ' => ?_) hcnt, ?_, hrows⟩
  · rw [hios]
    simp [pendIO, ctrlJ, hph, ioWords, letterIO]
  · simp [dist, pendOn, hph, Ne.symm hτ']
  · rw [nflush_cons_shift]; exact hfl

/-- The specification through the second I/O of a right shift of a work tape. -/
theorem spec_pendR {h : Fin M.k} (hph : s.2.ph = .pend h true)
    (hx : s.2.x h.succ = (s.2.j h.succ + 2) * B) {ios : List (IO (2 * M.k + 3))}
    {D' : Disk (Sym M) B}
    (hs : Spec M d B w Th t
      { s.2 with j := Function.update s.2.j h.succ (s.2.j h.succ + 1), ph := .run } ios D') :
    Spec M d B w Th t s.2 ((.read, hiS M h.succ, waddr M d h (s.2.j h.succ + 2)) :: ios) D' := by
  obtain ⟨ev, hios, hcnt, hfl, hrows⟩ := hs
  refine ⟨ev, ?_, fun τ' => ?_, hfl, hrows⟩
  · rw [hios]
    simp [pendIO, ctrlJ, hph]
  · have := hcnt τ'
    by_cases e : τ' = h.succ
    · subst e
      rw [dist_shiftR hx] at this
      rw [dist_pend hph]
      exact this
    · rwa [dist_shift_ne e _ (pendOn_pend hph e)] at this

/-- The specification through the second I/O of a left shift of a work tape. -/
theorem spec_pendL {h : Fin M.k} (hph : s.2.ph = .pend h false)
    (hx : s.2.x h.succ = s.2.j h.succ * B - 1) {ios : List (IO (2 * M.k + 3))}
    {D' : Disk (Sym M) B}
    (hs : Spec M d B w Th t
      { s.2 with j := Function.update s.2.j h.succ (s.2.j h.succ - 1), ph := .run } ios D') :
    Spec M d B w Th t s.2 ((.read, loS M h.succ, waddr M d h (s.2.j h.succ - 1)) :: ios) D' := by
  obtain ⟨ev, hios, hcnt, hfl, hrows⟩ := hs
  refine ⟨ev, ?_, fun τ' => ?_, hfl, hrows⟩
  · rw [hios]
    simp [pendIO, ctrlJ, hph]
  · have := hcnt τ'
    by_cases e : τ' = h.succ
    · subst e
      rw [dist_shiftL hx] at this
      rw [dist_pend hph]
      exact this
    · rwa [dist_shift_ne e _ (pendOn_pend hph e)] at this

theorem meas_lt_shift {ρ ρ' : Reg M} (hph : ρ.ph = .run) (hph' : ρ'.ph = .run)
    (hnb : ρ'.nbuf = ρ.nbuf) (hn : nOut M B ρ' + 1 = nOut M B ρ) :
    meas M B Th t ρ' < meas M B Th t ρ := by
  unfold meas; rw [emeas_run hph, emeas_run hph', hnb, ← hn]; omega

theorem meas_lt_pend_done {ρ ρ' : Reg M} {h : Fin M.k} {r : Bool} (hph : ρ.ph = .pend h r)
    (hph' : ρ'.ph = .run) (hnb : ρ'.nbuf = ρ.nbuf) (hn : nOut M B ρ' + 1 = nOut M B ρ) :
    meas M B Th t ρ' < meas M B Th t ρ := by
  unfold meas; rw [emeas_pend hph, emeas_run hph', hnb, ← hn]; omega

theorem meas_lt_pend_start {ρ ρ' : Reg M} {h : Fin M.k} {r : Bool} (hph : ρ.ph = .run)
    (hph' : ρ'.ph = .pend h r) (hnb : ρ'.nbuf = ρ.nbuf) (hn : nOut M B ρ' = nOut M B ρ)
    (hpos : 0 < nOut M B ρ) : meas M B Th t ρ' < meas M B Th t ρ := by
  unfold meas; rw [emeas_run hph, emeas_pend hph', hnb, hn]; omega

theorem Inv.nfl_le_d (hB : 0 < B) (hout : (run M w Th).outRev.length = d * B) (ht : t ≤ Th)
    (hI : Inv M d B w t s D) : s.2.nfl ≤ d := by
  have := hI.nfl_le hout ht
  by_contra hc
  have : (d + 1) * B ≤ s.2.nfl * B := Nat.mul_le_mul_right _ (by omega)
  nlinarith

/-- The input head leaves its window to the right. -/
theorem next_inR (hB : 0 < B) (hw : w.length = d * B) (ht : t ≤ Th) (hI : Inv M d B w t s D)
    (hph : s.2.ph = .run) (hfo : firstOut M B s.2 = some 0) (hr : (s.2.j 0 + 2) * B ≤ s.2.x 0) :
    Next M d B w Th t s D := by
  have hx : s.2.x 0 = (s.2.j 0 + 2) * B := le_antisymm (hI.near 0).2 hr
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := mulB (s.2.j 0) B
  have hB' : (0 : ℤ) < B := by exact_mod_cast hB
  have hwlen : (w.length : ℤ) = d * B := by exact_mod_cast hw
  have hinner : inner M d B s = inShift M d s := by
    rw [inner_run hph]; simp [runStep, hfo, shiftStep]
  have hm : meas M B Th t { s.2 with j := Function.update s.2.j 0 (s.2.j 0 + 1), ph := .run } <
      meas M B Th t s.2 := meas_lt_shift hph rfl rfl (nOut_shiftR hB hx .run)
  have hdisk : ∀ h : Fin M.k, h.succ = 0 →
      D (waddr M d h (s.2.j 0)) = workBlk M (run M w t) h (s.2.j 0) :=
    fun h e => absurd e (Fin.succ_ne_zero h)
  by_cases hrange : 0 ≤ s.2.j 0 + 2 ∧ s.2.j 0 + 2 < d
  · right; right; left
    refine ⟨hiS M 0, s.2.j 0 + 2, (Function.update s.1 (loS M 0) (s.1 (hiS M 0)),
      { s.2 with j := Function.update s.2.j 0 (s.2.j 0 + 1), ph := .run }), ?_, ?_, hm, ?_⟩
    · rw [hinner, inShift, ite_eq_left hr, ite_eq_left hrange]
    · refine inv_shiftR hI hx _ (fun p hp0 hp1 => ?_) hdisk
      have hrow : D (s.2.j 0 + 2) = inputDisk (symAlph M) d B w (s.2.j 0 + 2) := by
        have := hI.rows (s.2.j 0 + 2).toNat (by omega)
        rwa [Int.toNat_of_nonneg hrange.1] at this
      have h3 : (s.2.j 0 + 3) * (B : ℤ) ≤ d * B := mul_le_mul_of_nonneg_right (by omega) hB'.le
      have h4 : (0 : ℤ) ≤ (s.2.j 0 + 2) * B := mul_nonneg hrange.1 hB'.le
      rw [hrow, getZ_inputDisk hrange.1 hrange.2 (by omega) (by omega), tsym_zero,
        readInput_of_lt (by omega) (by omega),
        show (s.2.j 0 + 2) * (B : ℤ) + (p - (s.2.j 0 + 2) * B) = p by ring]
    · intro ios D' hs
      have := spec_inR hph hx hs
      rwa [ite_eq_left hrange] at this
  · right; left
    refine ⟨(Function.update (Function.update s.1 (loS M 0) (s.1 (hiS M 0))) (hiS M 0)
      (endBlk M B), { s.2 with j := Function.update s.2.j 0 (s.2.j 0 + 1), ph := .run }), t,
      ?_, ht, ?_, hm, ?_⟩
    · rw [hinner, inShift, ite_eq_left hr, ite_eq_right hrange]
    · refine inv_shiftR hI hx _ (fun p hp0 hp1 => ?_) hdisk
      rw [getZ_endBlk (by omega) (by omega), tsym_zero, readInput_eq_none]
      rcases not_and_or.mp hrange with h | h
      · left
        have : (s.2.j 0 + 3) * (B : ℤ) ≤ 0 := by nlinarith
        omega
      · right
        have : (d : ℤ) * B ≤ (s.2.j 0 + 2) * B := mul_le_mul_of_nonneg_right (by omega) hB'.le
        omega
    · intro ios D' hs
      have := spec_inR hph hx hs
      rwa [ite_eq_right hrange, List.nil_append] at this

/-- The input head leaves its window to the left. -/
theorem next_inL (hB : 0 < B) (hw : w.length = d * B) (ht : t ≤ Th) (hI : Inv M d B w t s D)
    (hph : s.2.ph = .run) (hfo : firstOut M B s.2 = some 0) (hr : ¬ (s.2.j 0 + 2) * B ≤ s.2.x 0) :
    Next M d B w Th t s D := by
  have hx : s.2.x 0 = s.2.j 0 * B - 1 := by
    have h1 := firstOut_some hfo
    have h2 := (hI.near 0).1
    simp only [Outside] at h1
    omega
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := mulB (s.2.j 0) B
  have hB' : (0 : ℤ) < B := by exact_mod_cast hB
  have hwlen : (w.length : ℤ) = d * B := by exact_mod_cast hw
  have hinner : inner M d B s = inShift M d s := by
    rw [inner_run hph]; simp [runStep, hfo, shiftStep]
  have hm : meas M B Th t { s.2 with j := Function.update s.2.j 0 (s.2.j 0 - 1), ph := .run } <
      meas M B Th t s.2 := meas_lt_shift hph rfl rfl (nOut_shiftL hB hx .run)
  have hdisk : ∀ h : Fin M.k, h.succ = 0 →
      D (waddr M d h (s.2.j 0 + 1)) = workBlk M (run M w t) h (s.2.j 0 + 1) :=
    fun h e => absurd e (Fin.succ_ne_zero h)
  by_cases hrange : 0 ≤ s.2.j 0 - 1 ∧ s.2.j 0 - 1 < d
  · right; right; left
    refine ⟨loS M 0, s.2.j 0 - 1, (Function.update s.1 (hiS M 0) (s.1 (loS M 0)),
      { s.2 with j := Function.update s.2.j 0 (s.2.j 0 - 1), ph := .run }), ?_, ?_, hm, ?_⟩
    · rw [hinner, inShift, ite_eq_right hr, ite_eq_left hrange]
    · refine inv_shiftL hI hx _ (fun p hp0 hp1 => ?_) hdisk
      have hrow : D (s.2.j 0 - 1) = inputDisk (symAlph M) d B w (s.2.j 0 - 1) := by
        have := hI.rows (s.2.j 0 - 1).toNat (by omega)
        rwa [Int.toNat_of_nonneg hrange.1] at this
      have h3 : s.2.j 0 * (B : ℤ) ≤ d * B := mul_le_mul_of_nonneg_right (by omega) hB'.le
      have h4 : (0 : ℤ) ≤ (s.2.j 0 - 1) * B := mul_nonneg hrange.1 hB'.le
      rw [hrow, getZ_inputDisk hrange.1 hrange.2 (by omega) (by omega), tsym_zero,
        readInput_of_lt (by omega) (by omega),
        show (s.2.j 0 - 1) * (B : ℤ) + (p - (s.2.j 0 - 1) * B) = p by ring]
    · intro ios D' hs
      have := spec_inL hph hx hs
      rwa [ite_eq_left hrange] at this
  · right; left
    refine ⟨(Function.update (Function.update s.1 (hiS M 0) (s.1 (loS M 0))) (loS M 0)
      (endBlk M B), { s.2 with j := Function.update s.2.j 0 (s.2.j 0 - 1), ph := .run }), t,
      ?_, ht, ?_, hm, ?_⟩
    · rw [hinner, inShift, ite_eq_right hr, ite_eq_right hrange]
    · refine inv_shiftL hI hx _ (fun p hp0 hp1 => ?_) hdisk
      rw [getZ_endBlk (by omega) (by omega), tsym_zero, readInput_eq_none]
      rcases not_and_or.mp hrange with h | h
      · left
        have : s.2.j 0 * (B : ℤ) ≤ 0 := by nlinarith
        omega
      · right
        have : (d : ℤ) * B ≤ (s.2.j 0 - 1) * B := mul_le_mul_of_nonneg_right (by omega) hB'.le
        omega
    · intro ios D' hs
      have := spec_inL hph hx hs
      rwa [ite_eq_right hrange, List.nil_append] at this

/-- A work head leaves its window to the right: write back the leaving block. -/
theorem next_wR (hB : 0 < B) (hout : (run M w Th).outRev.length = d * B) (ht : t ≤ Th)
    (hI : Inv M d B w t s D) (hph : s.2.ph = .run) {h : Fin M.k}
    (hfo : firstOut M B s.2 = some h.succ) (hr : (s.2.j h.succ + 2) * B ≤ s.2.x h.succ) :
    Next M d B w Th t s D := by
  have hx : s.2.x h.succ = (s.2.j h.succ + 2) * B := le_antisymm (hI.near h.succ).2 hr
  have hnfl := hI.nfl_le_d hB hout ht
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := mulB (s.2.j h.succ) B
  right; right; right
  refine ⟨loS M h.succ, waddr M d h (s.2.j h.succ), (s.1, { s.2 with ph := .pend h true }),
    ?_, ?_, ?_, ?_⟩
  · rw [inner_run hph]
    simp [runStep, hfo, shiftStep, workShift, hr]
  · exact {
      ph := by simp
      st := hI.st
      x := hI.x
      win := hI.win
      near := hI.near
      disk := fun h' jj h1 h2 => by
        have hne : waddr M d h' jj ≠ waddr M d h (s.2.j h.succ) := fun e => by
          obtain ⟨rfl, rfl⟩ := waddr_inj e; exact h1 rfl
        rw [Function.update_of_ne hne]
        exact hI.disk h' jj h1 h2
      rows := fun i hi => by
        rw [Function.update_of_ne (Ne.symm (waddr_ne_of_lt h _ (by omega)))]
        exact hI.rows i hi
      outs := fun n hn => by
        rw [Function.update_of_ne (Ne.symm (waddr_ne_of_lt h _ (by simp only at hn; omega)))]
        exact hI.outs n hn
      len := hI.len
      nbuf := hI.nbuf
      buf := hI.buf
      pendR := fun h' hh => by
        simp only [Phase.pend.injEq, and_true] at hh
        subst hh
        refine ⟨hx, ?_⟩
        simp only [Function.update_self]
        funext q
        have hq := q.isLt
        rw [← view_lo s.1 h.succ (s.2.j h.succ) q, hI.win h.succ _ (by omega) (by omega),
          tsym_succ]
        rfl
      pendL := fun h' hh => by simp at hh }
  · exact meas_lt_pend_start hph rfl rfl (nOut_congr (fun _ => Iff.rfl))
      (nOut_pos (Or.inr hr : Outside M B s.2 h.succ))
  · exact fun ios D' hs => spec_wR hph hx hs

/-- A work head leaves its window to the left: write back the leaving block. -/
theorem next_wL (hB : 0 < B) (hout : (run M w Th).outRev.length = d * B) (ht : t ≤ Th)
    (hI : Inv M d B w t s D) (hph : s.2.ph = .run) {h : Fin M.k}
    (hfo : firstOut M B s.2 = some h.succ) (hr : ¬ (s.2.j h.succ + 2) * B ≤ s.2.x h.succ) :
    Next M d B w Th t s D := by
  have hout' := firstOut_some hfo
  have hx : s.2.x h.succ = s.2.j h.succ * B - 1 := by
    have h2 := (hI.near h.succ).1
    simp only [Outside] at hout'
    omega
  have hnfl := hI.nfl_le_d hB hout ht
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := mulB (s.2.j h.succ) B
  right; right; right
  refine ⟨hiS M h.succ, waddr M d h (s.2.j h.succ + 1), (s.1, { s.2 with ph := .pend h false }),
    ?_, ?_, ?_, ?_⟩
  · rw [inner_run hph]
    simp [runStep, hfo, shiftStep, workShift, hr]
  · exact {
      ph := by simp
      st := hI.st
      x := hI.x
      win := hI.win
      near := hI.near
      disk := fun h' jj h1 h2 => by
        have hne : waddr M d h' jj ≠ waddr M d h (s.2.j h.succ + 1) := fun e => by
          obtain ⟨rfl, rfl⟩ := waddr_inj e; exact h2 rfl
        rw [Function.update_of_ne hne]
        exact hI.disk h' jj h1 h2
      rows := fun i hi => by
        rw [Function.update_of_ne (Ne.symm (waddr_ne_of_lt h _ (by omega)))]
        exact hI.rows i hi
      outs := fun n hn => by
        rw [Function.update_of_ne (Ne.symm (waddr_ne_of_lt h _ (by simp only at hn; omega)))]
        exact hI.outs n hn
      len := hI.len
      nbuf := hI.nbuf
      buf := hI.buf
      pendR := fun h' hh => by simp at hh
      pendL := fun h' hh => by
        simp only [Phase.pend.injEq, and_true] at hh
        subst hh
        refine ⟨hx, ?_⟩
        simp only [Function.update_self]
        funext q
        have hq := q.isLt
        rw [← view_hi s.1 h.succ (s.2.j h.succ) q, hI.win h.succ _ (by omega) (by omega),
          tsym_succ]
        rfl }
  · exact meas_lt_pend_start hph rfl rfl (nOut_congr (fun _ => Iff.rfl)) (nOut_pos hout')
  · exact fun ios D' hs => spec_wL hph hx hs

/-- The second I/O of a right shift of a work tape: read the entering block. -/
theorem next_pendR (hB : 0 < B) (hI : Inv M d B w t s D) {h : Fin M.k}
    (hph : s.2.ph = .pend h true) : Next M d B w Th t s D := by
  obtain ⟨hx, hD⟩ := hI.pendR h hph
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := mulB (s.2.j h.succ) B
  right; right; left
  refine ⟨hiS M h.succ, waddr M d h (s.2.j h.succ + 2),
    (Function.update s.1 (loS M h.succ) (s.1 (hiS M h.succ)),
      { s.2 with j := Function.update s.2.j h.succ (s.2.j h.succ + 1), ph := .run }),
    ?_, ?_, ?_, ?_⟩
  · simp [inner, hph, pendStep]
  · refine inv_shiftR hI hx _ (fun p hp0 hp1 => ?_) (fun h' e => ?_)
    · rw [hI.disk h (s.2.j h.succ + 2) (by omega) (by omega),
        getZ_workBlk _ _ _ (by omega) (by omega), tsym_succ,
        show (s.2.j h.succ + 2) * (B : ℤ) + (p - (s.2.j h.succ + 2) * B) = p by ring]
    · obtain rfl := Fin.succ_injective _ e
      exact hD
  · exact meas_lt_pend_done hph rfl rfl (nOut_shiftR hB hx .run)
  · exact fun ios D' hs => spec_pendR hph hx hs

/-- The second I/O of a left shift of a work tape: read the entering block. -/
theorem next_pendL (hB : 0 < B) (hI : Inv M d B w t s D) {h : Fin M.k}
    (hph : s.2.ph = .pend h false) : Next M d B w Th t s D := by
  obtain ⟨hx, hD⟩ := hI.pendL h hph
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := mulB (s.2.j h.succ) B
  right; right; left
  refine ⟨loS M h.succ, waddr M d h (s.2.j h.succ - 1),
    (Function.update s.1 (hiS M h.succ) (s.1 (loS M h.succ)),
      { s.2 with j := Function.update s.2.j h.succ (s.2.j h.succ - 1), ph := .run }),
    ?_, ?_, ?_, ?_⟩
  · simp [inner, hph, pendStep]
  · refine inv_shiftL hI hx _ (fun p hp0 hp1 => ?_) (fun h' e => ?_)
    · rw [hI.disk h (s.2.j h.succ - 1) (by omega) (by omega),
        getZ_workBlk _ _ _ (by omega) (by omega), tsym_succ,
        show (s.2.j h.succ - 1) * (B : ℤ) + (p - (s.2.j h.succ - 1) * B) = p by ring]
    · obtain rfl := Fin.succ_injective _ e
      exact hD
  · exact meas_lt_pend_done hph rfl rfl (nOut_shiftL hB hx .run)
  · exact fun ios D' hs => spec_pendL hph hx hs

/-- **One step from the invariant.** -/
theorem next_of_inv (hB : 0 < B) (hw : w.length = d * B) (hTh : HaltsAt M w Th)
    (hout : (run M w Th).outRev.length = d * B) (ht : t ≤ Th) (hI : Inv M d B w t s D) :
    Next M d B w Th t s D := by
  rcases hph : s.2.ph with _ | _ | ⟨h, _ | _⟩
  · exact absurd hph hI.ph
  · rcases hfo : firstOut M B s.2 with _ | τ
    · by_cases hnb : s.2.nbuf = B
      · exact next_flush hB hout ht hI hph hfo hnb
      · rcases hδ : transAt M w t with _ | ⟨st', dIn, acts, o⟩
        · exact next_halt hB hout hTh ht hI hph hfo hnb hδ
        · exact next_step hB hTh ht hI hph hfo hnb hδ
    · induction τ using Fin.cases with
      | zero =>
        by_cases hr : (s.2.j 0 + 2) * B ≤ s.2.x 0
        · exact next_inR hB hw ht hI hph hfo hr
        · exact next_inL hB hw ht hI hph hfo hr
      | succ h =>
        by_cases hr : (s.2.j h.succ + 2) * B ≤ s.2.x h.succ
        · exact next_wR hB hout ht hI hph hfo hr
        · exact next_wL hB hout ht hI hph hfo hr
  · exact next_pendL hB hI hph
  · exact next_pendR hB hI hph

end Step

/-! ## The simulation theorem -/

section Main

variable {M : TM} {d B : ℕ} {w : List Bool} {Th : ℕ}

/-- From any state satisfying the invariant, the simulator halts, through good registers, and the
rest of its run meets the specification. -/
theorem sim_from (hB : 0 < B) (hw : w.length = d * B) (hTh : HaltsAt M w Th)
    (hout : (run M w Th).outRev.length = d * B) (R : ℕ) (hR : Th + 2 ≤ R) :
    ∀ n t (s : Slots M B × Reg M) D, meas M B Th t s.2 = n → t ≤ Th → Inv M d B w t s D →
      ∃ ios D', MRuns (inner M d B) (Good M R) s D ios D' ∧ Spec M d B w Th t s.2 ios D' := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro t s D hn ht hI
    have hg := hI.good hB R hR ht
    rcases next_of_inv hB hw hTh hout ht hI with ⟨h0, hS⟩ | ⟨s', t', h0, ht', hI', hm, hS⟩ |
      ⟨i, a, s', h0, hI', hm, hS⟩ | ⟨i, a, s', h0, hI', hm, hS⟩
    · exact ⟨[], D, .halt hg h0, hS⟩
    · obtain ⟨ios, D', hr, hs⟩ := ih _ (hn ▸ hm) t' s' D rfl ht' hI'
      exact ⟨ios, D', .tau hg h0 hr, hS _ _ hs⟩
    · obtain ⟨ios, D', hr, hs⟩ := ih _ (hn ▸ hm) t _ D rfl ht hI'
      exact ⟨_, D', .read hg h0 hr, hS _ _ hs⟩
    · obtain ⟨ios, D', hr, hs⟩ := ih _ (hn ▸ hm) t _ _ rfl ht hI'
      exact ⟨_, D', .write hg h0 hr, hS _ _ hs⟩

/-- The invariant after the first I/O. -/
theorem inv_start (hB : 0 < B) (hd : 0 < d) (hw : w.length = d * B) :
    Inv M d B w 0 (Function.update (Function.update (fun _ _ => .inr 0) (loS M 0) (endBlk M B))
      (hiS M 0) (inputDisk (symAlph M) d B w 0), { reg₀ M with ph := .run })
      (inputDisk (symAlph M) d B w) := by
  have hB' : (0 : ℤ) < B := by exact_mod_cast hB
  have hdB : (B : ℤ) ≤ d * B := by
    have : (1 : ℤ) ≤ d := by exact_mod_cast hd
    nlinarith
  have hwlen : (w.length : ℤ) = d * B := by exact_mod_cast hw
  exact {
    ph := by simp
    st := rfl
    x := fun τ => by induction τ using Fin.cases <;> rfl
    win := fun τ p hp0 hp1 => by
      simp only [reg₀] at hp0 hp1 ⊢
      unfold view
      induction τ using Fin.cases with
      | zero =>
        simp only [Function.update_self, Function.update_of_ne (loS_ne_hiS 0 0), tsym_zero]
        split_ifs with hp
        · rw [getZ_endBlk (by linarith) (by push_cast at hp ⊢; linarith),
            readInput_eq_none (Or.inl (by push_cast at hp; linarith))]
        · rw [getZ_inputDisk (le_refl 0) (by exact_mod_cast hd) (by push_cast at hp ⊢; linarith)
            (by push_cast at hp1 ⊢; linarith),
            readInput_of_lt (by push_cast at hp ⊢; linarith) (by push_cast at hp1 ⊢; linarith)]
          congr 4
          push_cast
          ring
      | succ h =>
        have h1 : loS M h.succ ≠ hiS M 0 := loS_ne_hiS _ _
        have h2 : loS M h.succ ≠ loS M 0 := loS_ne_loS (Fin.succ_ne_zero h)
        have h3 : hiS M h.succ ≠ hiS M 0 := hiS_ne_hiS (Fin.succ_ne_zero h)
        have h4 : hiS M h.succ ≠ loS M 0 := hiS_ne_loS _ _
        simp only [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3,
          Function.update_of_ne h4, tsym_succ]
        split_ifs <;> simp [getZ, run_zero, init]
    near := fun τ => by
      simp only [reg₀]
      constructor <;> push_cast <;> linarith
    disk := fun h jj _ _ => by
      funext q
      have := waddr_ge (M := M) d h jj
      simp only [inputDisk, workBlk, run_zero, init]
      rw [ite_eq_right (by omega)]
      rfl
    rows := fun _ _ => rfl
    outs := fun n hn => absurd hn (Nat.not_lt_zero _)
    len := by simp [reg₀, run_zero, init]
    nbuf := Nat.zero_le _
    buf := fun q hq => absurd hq (Nat.not_lt_zero _)
    pendR := fun h hh => by simp at hh
    pendL := fun h hh => by simp at hh }

/-- **The simulation theorem.** On an input of length `dB` on which `M` halts at time `Th` with
an output of length `dB`, the simulator, started with blank slots and the initial register, halts
through registers bounded by `R ≥ Th + 2`; its I/O sequence is the first read followed by the I/Os
of an event word with at most `Th / B` shifts of every tape and exactly `d` flushes, and the final
disk holds output row `n` at address `d + n`. -/
theorem simulate (hB : 0 < B) (hd : 0 < d) (hw : w.length = d * B) (hTh : HaltsAt M w Th)
    (hout : (run M w Th).outRev.length = d * B) (R : ℕ) (hR : Th + 2 ≤ R) :
    ∃ ev ios D', MRuns (inner M d B) (Good M R) (fun _ _ => .inr 0, reg₀ M)
        (inputDisk (symAlph M) d B w) ios D' ∧
      ios = (.read, hiS M 0, 0) :: ioWords M d (fun _ => -1) 0 ev ∧
      (∀ τ, B * cnt τ ev ≤ Th) ∧ nflush ev = d ∧
      ∀ n < d, D' ((d : ℤ) + n) = rowBlock (symAlph M) B (run M w Th).outRev.reverse n := by
  obtain ⟨ios, D', hr, ev, hios, hcnt, hfl, hrows⟩ :=
    sim_from hB hw hTh hout R hR _ 0 _ _ rfl (Nat.zero_le _) (inv_start hB hd hw)
  refine ⟨ev, (.read, hiS M 0, 0) :: ios, D', ?_, ?_, fun τ => ?_, ?_, hrows⟩
  · refine .read ?_ rfl hr
    refine ⟨fun _ => by simp [reg₀], fun _ => ?_, by simp [reg₀], by simp [reg₀]⟩
    simp [reg₀]
    omega
  · rw [hios]; rfl
  · have h1 := hcnt τ
    have h2 : dist M B { reg₀ M with ph := .run } τ = B := by
      rw [dist_run rfl]
      simp only [reg₀]
      omega
    rw [h2] at h1
    push_cast at h1
    exact_mod_cast (by linarith : (B : ℤ) * cnt τ ev ≤ Th)
  · simpa [reg₀] using hfl

/-! ### Counting events and I/Os -/

theorem length_eq_sum_cnt {k : ℕ} (ev : List (Letter k)) :
    ev.length = (∑ τ, cnt τ ev) + nflush ev := by
  induction ev with
  | nil => simp [cnt, nflush]
  | cons ℓ ev ih =>
    cases ℓ with
    | shift τ r =>
      have : ∀ τ', cnt τ' (.shift τ r :: ev) = cnt τ' ev + if τ = τ' then 1 else 0 := by
        intro τ'
        by_cases e : τ = τ' <;> simp [cnt, Letter.tape, e]
      simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
        List.length_cons, nflush_cons_shift]
      omega
    | flush =>
      have : ∀ τ', cnt τ' (.flush :: ev) = cnt τ' ev := by intro τ'; simp [cnt, Letter.tape]
      simp only [this, List.length_cons]
      simp [nflush, Letter.tape] at ih ⊢
      omega

theorem ioWords_length_le (jv : Fin (M.k + 1) → ℤ) (n : ℕ) (ev : List (Letter M.k)) :
    (ioWords M d jv n ev).length ≤ cnt 0 ev + 2 * (∑ h : Fin M.k, cnt h.succ ev) + nflush ev := by
  induction ev generalizing jv n with
  | nil => simp [ioWords]
  | cons ℓ ev ih =>
    rw [ioWords, List.length_append]
    have ih' := ih (letterIO M d jv n ℓ).2.1 (letterIO M d jv n ℓ).2.2
    cases ℓ with
    | shift τ r =>
      have hc : ∀ τ', cnt τ' (.shift τ r :: ev) = cnt τ' ev + if τ = τ' then 1 else 0 := by
        intro τ'
        by_cases e : τ = τ' <;> simp [cnt, Letter.tape, e]
      rw [nflush_cons_shift]
      simp only [hc, Finset.sum_add_distrib]
      induction τ using Fin.cases with
      | zero =>
        have hl : (letterIO M d jv n (.shift 0 r)).1.length ≤ 1 := by
          cases r <;> simp only [letterIO, Fin.cases_zero] <;> split_ifs <;> simp
        have hs : (∑ h : Fin M.k, if (0 : Fin (M.k + 1)) = h.succ then 1 else 0) = 0 :=
          Finset.sum_eq_zero fun h _ => by simp [(Fin.succ_ne_zero h).symm]
        simp only [hs, ↓reduceIte]
        omega
      | succ h₀ =>
        have hl : (letterIO M d jv n (.shift h₀.succ r)).1.length = 2 := by
          cases r <;> simp [letterIO]
        have hs : (∑ h : Fin M.k, if h₀.succ = h.succ then 1 else 0) = 1 := by
          simp [Fin.succ_inj]
        simp only [hs, (Fin.succ_ne_zero h₀), ↓reduceIte]
        omega
    | flush =>
      have hc : ∀ τ', cnt τ' (.flush :: ev) = cnt τ' ev := by intro τ'; simp [cnt, Letter.tape]
      have hf : nflush (.flush :: ev : List (Letter M.k)) = nflush ev + 1 := by
        simp [nflush, Letter.tape]
      have hl : (letterIO M d jv n .flush).1.length = 1 := by simp [letterIO]
      simp only [hc, hf, hl]
      omega

end Main

end MergeDepth.EM
