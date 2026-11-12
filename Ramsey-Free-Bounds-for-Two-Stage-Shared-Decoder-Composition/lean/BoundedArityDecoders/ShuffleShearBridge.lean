import Transpose.Statement
import LeanMachine.ShuffleShear.StoneShuffle
import LeanMachine.ShuffleShear.StoneUnshuffle
import LeanMachine.ShuffleShear.RowShear
import BoundedArityDecoders.OperatorDuality

/-!
# Bridge from `LeanMachine.ShuffleShear` to `Transpose.TM` and Grid Operators

This module transports the verified linear-time multitape Turing machines in
`LeanMachine.ShuffleShear` (`stoneShuffleTM`, `stoneUnshuffleTM`, and `rowShearTM`) to the
`Transpose.TM` machine model of the first paper (`Transpose/Statement.lean`), preserving work-tape
count `k`, work alphabet `Fin (g + 1)`, state count `Fin (q + 1)`, and step count identically, and
intertwines their matrix transformations with the `GridState` linear operators of
`BoundedArityDecoders.OperatorDuality`.
-/

namespace BoundedArityDecoders

open LeanMachine

section DetTMToTranspose

/-- Isomorphism of head movement directions between `LeanMachine.ShuffleShear.Dir` and
`Transpose.Dir`. -/
def toTransposeDir : ShuffleShear.Dir → Transpose.Dir
  | .left  => .left
  | .stay  => .stay
  | .right => .right

@[simp]
theorem toTransposeDir_shift (d : ShuffleShear.Dir) (p : Int) :
    (toTransposeDir d).shift p = d.shift p := by
  cases d <;> rfl

/-- Embed a `LeanMachine.ShuffleShear.DetTM` identically into `Transpose.TM`. -/
def toTransposeTM (M : ShuffleShear.DetTM) : Transpose.TM where
  k := M.k
  g := M.g
  q := M.q
  δ := fun s inp w =>
    match M.δ s inp w with
    | none => none
    | some (s', d, acts, o) =>
        some (s', toTransposeDir d, (fun i => ((acts i).1, toTransposeDir (acts i).2)), o)

@[simp] theorem toTransposeTM_k (M : ShuffleShear.DetTM) : (toTransposeTM M).k = M.k := rfl
@[simp] theorem toTransposeTM_g (M : ShuffleShear.DetTM) : (toTransposeTM M).g = M.g := rfl
@[simp] theorem toTransposeTM_q (M : ShuffleShear.DetTM) : (toTransposeTM M).q = M.q := rfl

/-- Map a configuration of `M : ShuffleShear.DetTM` to `Transpose.Config (toTransposeTM M)`. -/
def toTransposeConfig {M : ShuffleShear.DetTM} (c : ShuffleShear.Config M) :
    Transpose.Config (toTransposeTM M) where
  state   := c.state
  inPos   := c.inPos
  work    := c.work
  workPos := c.workPos
  outRev  := c.outRev

@[simp]
theorem toTransposeConfig_init (M : ShuffleShear.DetTM) :
    toTransposeConfig (ShuffleShear.init M) = Transpose.init (toTransposeTM M) := rfl

private theorem nth_eq_transpose :
    ∀ (xs : List Bool) (i : Nat), ShuffleShear.nth xs i = Transpose.nth xs i
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: bs, i + 1 => nth_eq_transpose bs i

private theorem readInput_eq_transpose (w : List Bool) (p : Int) :
    ShuffleShear.readInput w p = Transpose.readInput w p := by
  simp only [ShuffleShear.readInput, Transpose.readInput, nth_eq_transpose]

private theorem step_toTransposeConfig (M : ShuffleShear.DetTM) (w : List Bool)
    (c : ShuffleShear.Config M) :
    (ShuffleShear.step M w c).map toTransposeConfig =
      Transpose.step (toTransposeTM M) w (toTransposeConfig c) := by
  simp only [ShuffleShear.step, Transpose.step, toTransposeTM, toTransposeConfig,
    readInput_eq_transpose]
  cases h : M.δ c.state (Transpose.readInput w c.inPos) (fun i => c.work i (c.workPos i)) with
  | none => rfl
  | some quad =>
    rcases quad with ⟨s', d, acts, o⟩
    dsimp only [Option.map, toTransposeConfig]
    simp only [toTransposeDir_shift]
    cases o <;> rfl

private theorem stepN_toTransposeConfig (M : ShuffleShear.DetTM) (w : List Bool) :
    ∀ (n : Nat) (c : ShuffleShear.Config M),
      (ShuffleShear.stepN M w n c).map toTransposeConfig =
        Transpose.stepN (toTransposeTM M) w n (toTransposeConfig c)
  | 0, _ => rfl
  | n + 1, c => by
      simp only [ShuffleShear.stepN, Transpose.stepN]
      have hstep := step_toTransposeConfig M w c
      cases hs : ShuffleShear.step M w c with
      | none =>
        rw [hs] at hstep
        simp only [Option.map] at hstep ⊢
        rw [← hstep]
      | some c' =>
        rw [hs] at hstep
        simp only [Option.map] at hstep
        rw [← hstep]
        exact stepN_toTransposeConfig M w n c'

/-- Transport `ShuffleShear.ComputesWithin` to `Transpose.ComputesWithin` with identical step bound. -/
theorem computesWithin_toTransposeTM {M : ShuffleShear.DetTM} {w out : List Bool} {t : Nat}
    (h : ShuffleShear.ComputesWithin M w out t) :
    Transpose.ComputesWithin (toTransposeTM M) w out t := by
  rcases h with ⟨s, hst, c, hrun, hhalt, hout⟩
  refine ⟨s, hst, toTransposeConfig c, ?_, ?_, hout⟩
  · have hN := stepN_toTransposeConfig M w s (ShuffleShear.init M)
    rw [hrun, toTransposeConfig_init] at hN
    exact hN.symm
  · have hs := step_toTransposeConfig M w c
    rw [hhalt] at hs
    exact hs.symm

private theorem concatUpTo_eq_transpose (f : Nat → List Bool) :
    ∀ m : Nat, ShuffleShear.concatUpTo f m = Transpose.concatUpTo f m
  | 0 => rfl
  | m + 1 => by simp [ShuffleShear.concatUpTo, Transpose.concatUpTo, concatUpTo_eq_transpose f m]

@[simp]
theorem encode_eq_transpose (d b : Nat) (A : Transpose.Matrix) :
    ShuffleShear.encode d b A = Transpose.encode d b A := by
  unfold ShuffleShear.encode Transpose.encode
  have h1 : (fun i => ShuffleShear.concatUpTo
      (fun j => ShuffleShear.concatUpTo (fun t => [A i j t]) b) d) =
      (fun i => Transpose.concatUpTo
      (fun j => Transpose.concatUpTo (fun t => [A i j t]) b) d) := by
    funext i
    have h2 : (fun j => ShuffleShear.concatUpTo (fun t => [A i j t]) b) =
        (fun j => Transpose.concatUpTo (fun t => [A i j t]) b) := by
      funext j
      exact concatUpTo_eq_transpose _ b
    rw [h2]
    exact concatUpTo_eq_transpose _ d
  rw [h1]
  exact concatUpTo_eq_transpose _ d

@[simp]
theorem entryBits_eq_transpose (d : Nat) :
    ShuffleShear.entryBits d = Transpose.entryBits d := rfl

@[simp]
theorem inputLength_eq_transpose (d : Nat) :
    ShuffleShear.inputLength d = Transpose.inputLength d := rfl

end DetTMToTranspose

/-! ### Verified Linear-Time `Transpose.TM` Realizations -/

/-- Matrix-level Stone shuffle in `Transpose.Matrix` coordinates (`d = 2 ^ m`). -/
abbrev stoneShuffleTMMatrix : ℕ → Transpose.Matrix → Transpose.Matrix :=
  ShuffleShear.stoneShuffleMatrix

/-- Matrix-level Stone unshuffle in `Transpose.Matrix` coordinates (`d = 2 ^ m`). -/
abbrev stoneUnshuffleTMMatrix : ℕ → Transpose.Matrix → Transpose.Matrix :=
  ShuffleShear.stoneUnshuffleMatrix

/-- Matrix-level within-row cyclic shear in `Transpose.Matrix` coordinates. -/
abbrev rowShearTMMatrix : ℕ → Transpose.Matrix → Transpose.Matrix :=
  ShuffleShear.rowShearMatrix

/-- `Transpose.TM` realization of Stone's perfect shuffle on `3` work tapes in `≤ 150 * L` steps. -/
def stoneShuffleTransposeTM : Transpose.TM :=
  toTransposeTM ShuffleShear.stoneShuffleTM

/-- `Transpose.TM` realization of Stone's inverse unshuffle on `2` work tapes in `≤ 150 * L` steps. -/
def stoneUnshuffleTransposeTM : Transpose.TM :=
  toTransposeTM ShuffleShear.stoneUnshuffleTM

/-- `Transpose.TM` realization of within-row cyclic shear on `2` work tapes in `≤ 200 * L` steps. -/
def rowShearTransposeTM : Transpose.TM :=
  toTransposeTM ShuffleShear.rowShearTM

/-- **Three-Work-Tape Linear-Time Stone Shuffle (`Transpose.TM` Transport).** -/
theorem stoneShuffleTM_threeTape_linear :
    stoneShuffleTransposeTM.k = 3 ∧
    ∀ (m : ℕ) (A : Transpose.Matrix), 1 ≤ m →
      let d := 2 ^ m
      Transpose.ComputesWithin stoneShuffleTransposeTM
        (Transpose.encode d (Transpose.entryBits d) A)
        (Transpose.encode d (Transpose.entryBits d) (stoneShuffleTMMatrix m A))
        (150 * Transpose.inputLength d) := by
  refine ⟨ShuffleShear.stoneShuffleTM_threeTape_linear.1, ?_⟩
  intro m A hm
  have h := ShuffleShear.stoneShuffleTM_threeTape_linear.2 m A hm
  dsimp only at h ⊢
  rw [encode_eq_transpose, encode_eq_transpose, entryBits_eq_transpose, inputLength_eq_transpose] at h
  exact computesWithin_toTransposeTM h

/-- **Two-Work-Tape Linear-Time Stone Unshuffle (`Transpose.TM` Transport).** -/
theorem stoneUnshuffleTM_twoTape_linear :
    stoneUnshuffleTransposeTM.k = 2 ∧
    ∀ (m : ℕ) (A : Transpose.Matrix), 1 ≤ m →
      let d := 2 ^ m
      Transpose.ComputesWithin stoneUnshuffleTransposeTM
        (Transpose.encode d (Transpose.entryBits d) A)
        (Transpose.encode d (Transpose.entryBits d) (stoneUnshuffleTMMatrix m A))
        (150 * Transpose.inputLength d) := by
  refine ⟨ShuffleShear.stoneUnshuffleTM_twoTape_linear.1, ?_⟩
  intro m A hm
  have h := ShuffleShear.stoneUnshuffleTM_twoTape_linear.2 m A hm
  dsimp only at h ⊢
  rw [encode_eq_transpose, encode_eq_transpose, entryBits_eq_transpose, inputLength_eq_transpose] at h
  exact computesWithin_toTransposeTM h

/-- **Two-Work-Tape Linear-Time Within-Row Shear (`Transpose.TM` Transport).** -/
theorem rowShearTM_twoTape_linear :
    rowShearTransposeTM.k = 2 ∧
    ∀ (d : ℕ) (A : Transpose.Matrix), 1 ≤ d →
      Transpose.ComputesWithin rowShearTransposeTM
        (Transpose.encode d (Transpose.entryBits d) A)
        (Transpose.encode d (Transpose.entryBits d) (rowShearTMMatrix d A))
        (200 * Transpose.inputLength d) := by
  refine ⟨ShuffleShear.rowShearTM_twoTape_linear.1, ?_⟩
  intro d A hd
  have h := ShuffleShear.rowShearTM_twoTape_linear.2 d A hd
  rw [encode_eq_transpose, encode_eq_transpose, entryBits_eq_transpose, inputLength_eq_transpose] at h
  exact computesWithin_toTransposeTM h

/-! ### Machine-to-Operator Representation Bridges -/

/-- Canonical `0`/`1` embedding of `M : Transpose.Matrix` into `GridState F d (Transpose.entryBits d)`,
mapping cell `(r, c) : Fin d × Fin d` and bit lane `ℓ : Fin (Transpose.entryBits d)` to `1 : F`
when `M r.val c.val ℓ.val = true` and `0 : F` otherwise. -/
def encodeTMMatrixToGrid (F : Type*) [Semiring F] (d : ℕ) (M : Transpose.Matrix) :
    GridState F d (Transpose.entryBits d) :=
  fun r c ℓ => if M r.val c.val ℓ.val then 1 else 0

/-- **Machine-to-Operator Representation Bridges.**
Under `encodeTMMatrixToGrid`, the Turing-machine matrix transformations `stoneShuffleTMMatrix`,
`stoneUnshuffleTMMatrix`, `rowShearTMMatrix`, and `Transpose.transpose` intertwine identically
with `stoneShuffleGridLinear`, `stoneUnshuffleGridLinear`, `rowShearLinear`, and `gridSwapLinear`
over every ring `F`. -/
theorem tmMatrix_gridLinear_bridges (F : Type*) [Ring F] :
    (∀ (m : ℕ) (M : Transpose.Matrix),
      encodeTMMatrixToGrid F (2 ^ m) (stoneShuffleTMMatrix m M) =
        stoneShuffleGridLinear F m (Transpose.entryBits (2 ^ m))
          (encodeTMMatrixToGrid F (2 ^ m) M)) ∧
    (∀ (m : ℕ) (M : Transpose.Matrix),
      encodeTMMatrixToGrid F (2 ^ m) (stoneUnshuffleTMMatrix m M) =
        stoneUnshuffleGridLinear F m (Transpose.entryBits (2 ^ m))
          (encodeTMMatrixToGrid F (2 ^ m) M)) ∧
    (∀ (d : ℕ) [NeZero d] (M : Transpose.Matrix),
      encodeTMMatrixToGrid F d (rowShearTMMatrix d M) =
        rowShearLinear F d (Transpose.entryBits d) (encodeTMMatrixToGrid F d M)) ∧
    (∀ (d : ℕ) (M : Transpose.Matrix),
      encodeTMMatrixToGrid F d (Transpose.transpose M) =
        gridSwapLinear F d (Transpose.entryBits d) (encodeTMMatrixToGrid F d M)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m M
    cases m <;> rfl
  · intro m M
    cases m <;> rfl
  · intro d _ M
    rfl
  · intro d M
    rfl

end BoundedArityDecoders
