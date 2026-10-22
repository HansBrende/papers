import TransposeFollowup.BinaryCarryMachine
import TransposeFollowup.BinaryCompareRun

/-! The shared carry controller uses at most5m+7 original TM transitions.
Both operands survive, the result has width m, and all three absolute heads
return to their initial positions. Preparing the result marker is explicit. -/

namespace TransposeFollowup.BinaryCarry

open FixedTapeCompiler
open CopyMachine (Sym Tape symbols)
open NativeZipper (shiftPositions_add shiftPositions_zero)
set_option autoImplicit false

theorem forward_run (sub c : Bool) (xs ys : List Bool) (h : xs.length = ys.length)
    (la lb lo : List (Sym Bool)) (pos : Fin 3 → ℤ) :
    execute (3 * xs.length)
      (cfg (.scan sub c) ⟨la, symbols xs ++ [.stop]⟩ ⟨lb, symbols ys ++ [.stop]⟩
        ⟨lo, []⟩ pos) =
      cfg (.scan sub (result sub c xs ys).2)
        ⟨(symbols xs).reverse ++ la, [.stop]⟩ ⟨(symbols ys).reverse ++ lb, [.stop]⟩
        ⟨(symbols (result sub c xs ys).1).reverse ++ lo, []⟩ (shifted pos xs.length) := by
  induction xs generalizing ys c la lb lo pos with
  | nil =>
    have hy : ys = [] := List.length_eq_zero_iff.mp h.symm
    subst ys
    simp [result, symbols, execute, NativeZipper.run, OperationalTrace.run]
  | cons a xs ih =>
    cases ys with
    | nil => simp at h
    | cons b ys =>
      have ht : xs.length = ys.length := by simpa using h
      rw [show 3 * (a :: xs).length = 3 + 3 * xs.length by simp; omega, execute_add]
      simp only [symbols, List.map_cons, List.cons_append]
      rw [scan_digit]
      change execute (3 * xs.length)
        (cfg (.scan sub (carry c a (operandBit sub b)))
          ⟨.data a :: la, symbols xs ++ [.stop]⟩
          ⟨.data b :: lb, symbols ys ++ [.stop]⟩
          ⟨.data (digit c a (operandBit sub b)) :: lo, []⟩ (shifted pos 1)) = _
      rw [ih _ _ ht]
      simp [result, symbols, List.reverse_cons, List.append_assoc, shiftPositions_add, add_comm]

theorem backward_run (c : Bool) (xs ys zs : List Bool)
    (hy : xs.length = ys.length) (hz : xs.length = zs.length)
    (ra rb ro : List (Sym Bool)) (hr : ra.headD .blank ≠ .start) (pos : Fin 3 → ℤ) :
    execute (2 * (xs.length + 1))
      (cfg (.back c) ⟨symbols xs ++ [.start], ra⟩ ⟨symbols ys ++ [.start], rb⟩
        ⟨symbols zs ++ [.start], ro⟩ pos) =
      cfg (.back c) ⟨[], .start :: (symbols xs.reverse ++ ra)⟩
        ⟨[], .start :: (symbols ys.reverse ++ rb)⟩
        ⟨[], .start :: (symbols zs.reverse ++ ro)⟩
        (shifted pos (-(xs.length + 1 : ℤ))) := by
  induction xs generalizing ys zs ra rb ro pos with
  | nil =>
    have hy0 : ys = [] := List.length_eq_zero_iff.mp hy.symm
    have hz0 : zs = [] := List.length_eq_zero_iff.mp hz.symm
    subst ys; subst zs
    rw [show 2 * (([] : List Bool).length + 1) = 2 by rfl,
      back_three c (⟨symbols [] ++ [Sym.start], ra⟩ : Tape Bool)
        (⟨symbols [] ++ [Sym.start], rb⟩ : Tape Bool)
        (⟨symbols [] ++ [Sym.start], ro⟩ : Tape Bool) pos hr]
    rfl
  | cons a xs ih =>
    cases ys with
    | nil => simp at hy
    | cons b ys =>
      cases zs with
      | nil => simp at hz
      | cons z zs =>
        have hyt : xs.length = ys.length := by simpa using hy
        have hzt : xs.length = zs.length := by simpa using hz
        rw [show 2 * ((a :: xs).length + 1) = 2 + 2 * (xs.length + 1) by simp; omega,
          execute_add,
          back_three c (⟨symbols (a :: xs) ++ [Sym.start], ra⟩ : Tape Bool)
            (⟨symbols (b :: ys) ++ [Sym.start], rb⟩ : Tape Bool)
            (⟨symbols (z :: zs) ++ [Sym.start], ro⟩ : Tape Bool) pos hr]
        change execute (2 * (xs.length + 1))
          (cfg (.back c) ⟨symbols xs ++ [.start], .data a :: ra⟩
            ⟨symbols ys ++ [.start], .data b :: rb⟩
            ⟨symbols zs ++ [.start], .data z :: ro⟩ (shifted pos (-1))) = _
        rw [ih ys zs hyt hzt _ _ _ (by simp)]
        simp [symbols, List.reverse_cons, List.append_assoc, shiftPositions_add,
          add_comm, add_left_comm]

abbrev marked := BinaryCompare.marked
def preparedOutput : Tape Bool := ⟨[.start], []⟩

theorem arithmetic_run (sub c : Bool) (xs ys : List Bool) (h : xs.length = ys.length)
    (pos : Fin 3 → ℤ) :
    execute (5 * xs.length + 7) (cfg (.scan sub c) (marked xs) (marked ys) preparedOutput pos) =
      cfg (.done (result sub c xs ys).2) (marked xs) (marked ys)
        (marked (result sub c xs ys).1) pos := by
  unfold marked BinaryCompare.marked preparedOutput
  rw [show 5 * xs.length + 7 = 3 * xs.length + (3 + (2 * (xs.length + 1) + 2)) by omega,
    execute_add, forward_run sub c xs ys h, execute_add, at_ends, execute_add]
  have hr := backward_run (result sub c xs ys).2 xs.reverse ys.reverse
    (result sub c xs ys).1.reverse (by simpa using h)
    (by simpa using (result_length sub c xs ys h).symm)
    [Sym.stop] [Sym.stop] [Sym.stop] (by simp) (shifted pos xs.length)
  simp only [List.length_reverse, List.reverse_reverse] at hr
  have hm (ws : List Bool) : symbols ws.reverse = (symbols ws).reverse := by simp [symbols]
  rw [hm xs, hm ys, hm (result sub c xs ys).1] at hr
  rw [hr, return_three]
  simp only [shifted, shiftPositions_add]
  have he : (xs.length : ℤ) + -(xs.length + 1) + 1 = 0 := by omega
  rw [he, shiftPositions_zero]

theorem arithmetic_trace (sub c : Bool) (xs ys : List Bool) (h : xs.length = ys.length)
    (pos : Fin 3 → ℤ) :
    ∃ t ≤ 5 * xs.length + 7,
      OperationalTrace.Trace (NativeMicrocode.step program) (NativeMicrocode.Active program) t
        (cfg (.scan sub c) (marked xs) (marked ys) preparedOutput pos).denote
        (cfg (.done (result sub c xs ys).2) (marked xs) (marked ys)
          (marked (result sub c xs ys).1) pos).denote :=
  NativeZipper.trace_of_run program (arithmetic_run sub c xs ys h pos)

noncomputable def nativeEncoding :
    NativeMicrocode.Encoding (Fin 3) Label 3 (Fintype.card Label - 1) where
  port := Equiv.refl _
  label := (NativeMicrocode.initialEncoding (T := Fin 3) (Label.scan false false)).label

noncomputable def nativeMachine : Transpose.TM := NativeMicrocode.machine nativeEncoding program

theorem native_resources : nativeMachine.k = 3 ∧ nativeMachine.g + 1 = 5 ∧
    nativeMachine.q + 1 = 33 := by
  change 3 = 3 ∧ 4 + 1 = 5 ∧ (Fintype.card Label - 1) + 1 = 33
  rw [fixed_resources.2.2]
  decide

theorem native_start_zero : nativeEncoding.label (.scan false false) = 0 :=
  NativeMicrocode.initialEncoding_start (T := Fin 3) (Label.scan false false)

theorem native_arithmetic {q : ℕ} (e : NativeMicrocode.Encoding (Fin 3) Label 3 q)
    (sub c : Bool) (xs ys : List Bool) (h : xs.length = ys.length) (pos : Fin 3 → ℤ)
    (w : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ 5 * xs.length + 7,
      Transpose.stepN (NativeMicrocode.machine e program) w t
        ((cfg (.scan sub c) (marked xs) (marked ys) preparedOutput pos).denote.denote
          e program inputPos outRev) =
        some ((cfg (.done (result sub c xs ys).2) (marked xs) (marked ys)
          (marked (result sub c xs ys).1) pos).denote.denote e program inputPos outRev) ∧
      Transpose.step (NativeMicrocode.machine e program) w
        ((cfg (.done (result sub c xs ys).2) (marked xs) (marked ys)
          (marked (result sub c xs ys).1) pos).denote.denote e program inputPos outRev) = none := by
  apply NativeZipper.stopped_subroutine e program w inputPos outRev
    (arithmetic_run sub c xs ys h pos)
  simp [NativeMicrocode.Active, NativeZipper.Config.denote, Microcode.Config.denote, cfg, program]

end TransposeFollowup.BinaryCarry
