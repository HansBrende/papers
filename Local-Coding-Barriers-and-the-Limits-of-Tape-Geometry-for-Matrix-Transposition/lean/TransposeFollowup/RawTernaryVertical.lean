import TransposeFollowup.TernaryBufferCoordinates
import TransposeFollowup.RawRowProgramApproximation
import TransposeFollowup.RawShellResources

/-! The full b-trit-entry vertical F3 prefix/difference P/p. Each of the
b lanes of every column has its own entry in the actual db-trit row buffer.
Internal output is exact in F3; raw output uses the existing Boolean
projection, which preserves binary final endpoints of composed words. -/
namespace TransposeFollowup.RawTernaryVertical
open Classical Filter Topology FixedTapeCompiler ScheduledNativeIO AffineMotion
open CopyMachine (Sym)
open Transpose Transpose.Tape Transpose.Tape.Impl
set_option autoImplicit false

def value (sub : Bool) (b d : ℕ) : (ℕ → Sym Bool) → ℕ → Sym Bool :=
  BufferedRows.bankValue (TernaryBank.bufferRule sub) (d*b) d

theorem value_entry (sub : Bool) (b d : ℕ) (x : ℕ → Sym Bool)
    (i j l : ℕ) (hi : i<d) (hj : j<d) (hl : l<b) :
    value sub b d x (i*(d*b)+j*b+l)=
      TernaryBank.encode ((TernaryBank.rowResult sub 0
        (List.ofFn (fun a : Fin d => TernaryBank.decode (x (a*(d*b)+j*b+l))))).getI i) :=
  TernaryBank.vertical_entry sub b d x i j l hi hj hl

theorem value_congr (sub : Bool) (b d : ℕ) : BankWord.Congruent (d*(d*b)) (value sub b d) :=
  BufferedRows.bankValue_congr (TernaryBank.bufferRule sub) (d*b) d

noncomputable def schedule (sub : Bool) (b d : ℕ) :=
  SharedRowBank.ruleSchedule (TernaryBank.bufferRule sub) (d*b) d

def internalTicks (b d : ℕ) : ℕ := BufferedRows.bankTicks (d*b) d

theorem represents (sub : Bool) (b d : ℕ) (w : List Bool) (c : SharedRowBank.State)
    (hc : BankWord.symbols.clean c) :
    BankWord.Represents BankWord.symbols (d*(d*b)) c
      (trajectory (schedule sub b d) w c (internalTicks b d))
      (value sub b d (BankWord.input BankWord.symbols c)) := by
  unfold schedule internalTicks
  rw [SharedRowBank.rule_exact]
  exact SharedRowBank.rule_represents (TernaryBank.bufferRule sub) (d*b) d w c hc

noncomputable def machine (sub : Bool) (b d : ℕ) :=
  SharedRowBank.rawRuleMachine (TernaryBank.bufferRule sub) (d*b) d

def ticks (b d : ℕ) : ℕ := SharedRowBank.rawTicks (d*b) d

def output (sub : Bool) (b d : ℕ) (w : List Bool) : List Bool :=
  (List.range (d*(d*b))).map (fun j => MaskedStrideCell.bit
    (value sub b d (fun i => .data (ScheduledRawInput.inputBit w i)) j))

theorem ticks_eq (b d : ℕ) (hb : 0<b) (hd : 0<d) :
    ticks b d=15*(d*(d*b))+2*(d*b) :=
  SharedRowBank.raw_ticks_eq (d*b) d (Nat.mul_pos hd hb)

theorem ticks_linear (b d : ℕ) (hb : 0<b) (hd : 0<d) : ticks b d ≤ 17*(d*(d*b)) :=
  SharedRowBank.raw_ticks_linear (d*b) d (Nat.mul_pos hd hb) hd

theorem native_correct (sub : Bool) (b d : ℕ) (w : List Bool) :
    ∃ c : Transpose.Config (machine sub b d),
      Transpose.stepN (machine sub b d) w (ticks b d) (Transpose.init (machine sub b d))=some c ∧
      Transpose.step (machine sub b d) w c=none ∧ c.outRev=(output sub b d w).reverse ∧
      ∀ z, c.work ((RawProgramShell.encoding SharedRowBank.initialRowMode (d*(d*b))
        (RawRowArithmetic.bankTicks (d*b) d)).port 1) z=0 :=
  SharedRowBank.raw_rule_native_correct (TernaryBank.bufferRule sub) (d*b) d w

theorem resources (sub : Bool) (b d : ℕ) :
    (machine sub b d).k=2 ∧ (machine sub b d).g+1=5 ∧
    (machine sub b d).q+1=(ticks b d+1)*200 :=
  SharedRowBank.raw_rule_resources (TernaryBank.bufferRule sub) (d*b) d

theorem curve_error (sub : Bool) (b d : ℕ) (hb : 0<b) (hd : 0<d)
    (w : List Bool) (x : ℝ) (t : Fin 2) :
    |(Transpose.Tape.workTraj (machine sub b d) w ⌊x⌋₊
      ((RawProgramShell.encoding SharedRowBank.initialRowMode (d*(d*b))
        (RawRowArithmetic.bankTicks (d*b) d)).port t) : ℝ)-
      SharedRowBank.rawCurve (d*b) d t x| ≤ 8*(d*b : ℕ)+8 :=
  SharedRowBank.rawRuleCurve_error (TernaryBank.bufferRule sub) (d*b) d (Nat.mul_pos hd hb) w x t

theorem state_bits_vanish {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop)
    (sub : ℕ → Bool) (b d : ℕ → ℕ)
    (hP : ∀ᶠ i in atTop, d i*(d i*b i)=inputLength (ns i)) :
    Tendsto (fun i => (Nat.clog 2 ((machine (sub i) (b i) (d i)).q+1) : ℝ)
      /inputLength (ns i)) atTop (𝓝 0) := by
  have hp : ∀ᶠ i in atTop, 0<d i*(d i*b i) := by
    filter_upwards [hP,(inputLength_tendsto hns).eventually_ge_atTop 1] with i hi hn
    have hn' : 1 ≤ inputLength (ns i) := by exact_mod_cast hn
    omega
  exact SharedRowBank.raw_rule_state_bits_vanish hns (fun i => TernaryBank.bufferRule (sub i))
    (fun i => d i*b i) d hP (hp.mono fun _ hi => Nat.pos_of_mul_pos_left hi)
      (hp.mono fun _ hi => Nat.pos_of_mul_pos_right hi)

end TransposeFollowup.RawTernaryVertical
