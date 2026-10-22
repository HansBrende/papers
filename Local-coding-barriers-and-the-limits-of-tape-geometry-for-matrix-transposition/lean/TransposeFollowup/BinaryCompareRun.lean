import TransposeFollowup.BinaryCompareMachine

/-! The finite comparator runs in at most5m+6 native transitions on two
m-bit words. Both tape contents and absolute head positions are restored. -/

namespace TransposeFollowup.BinaryCompare

open FixedTapeCompiler
open CopyMachine (Sym Tape symbols)
open NativeZipper (run)
set_option autoImplicit false

theorem forward_run (r : Result) (xs ys : List Bool) (h : xs.length = ys.length)
    (la lb : List (Sym Bool)) (pos : Fin 2 → ℤ) :
    execute (3 * xs.length)
      (cfg (.scan r) ⟨la, symbols xs ++ [.stop]⟩ ⟨lb, symbols ys ++ [.stop]⟩ pos) =
      cfg (.scan (scan r xs ys)) ⟨(symbols xs).reverse ++ la, [.stop]⟩
        ⟨(symbols ys).reverse ++ lb, [.stop]⟩ (shifted pos xs.length) := by
  induction xs generalizing ys r la lb pos with
  | nil =>
    have hy : ys = [] := List.length_eq_zero_iff.mp h.symm
    subst ys
    simp [symbols, scan, execute, run, OperationalTrace.run]
  | cons a xs ih =>
    cases ys with
    | nil => simp at h
    | cons b ys =>
      have ht : xs.length = ys.length := by simpa using h
      rw [show 3 * (a :: xs).length = 3 + 3 * xs.length by simp; omega,
        execute_add]
      simp only [symbols, List.map_cons, List.cons_append]
      rw [scan_digit]
      change execute (3 * xs.length)
        (cfg (.scan (update r a b)) ⟨.data a :: la, symbols xs ++ [.stop]⟩
          ⟨.data b :: lb, symbols ys ++ [.stop]⟩ (shifted pos 1)) = _
      rw [ih _ _ ht]
      simp [scan, symbols, List.reverse_cons, List.append_assoc, shifted_shifted,
        add_comm]

theorem backward_run (r : Result) (xs ys : List Bool) (h : xs.length = ys.length)
    (ra rb : List (Sym Bool)) (hr : ra.headD .blank ≠ .start) (pos : Fin 2 → ℤ) :
    execute (2 * (xs.length + 1))
      (cfg (.back r) ⟨symbols xs ++ [.start], ra⟩ ⟨symbols ys ++ [.start], rb⟩ pos) =
      cfg (.back r) ⟨[], .start :: (symbols xs.reverse ++ ra)⟩
        ⟨[], .start :: (symbols ys.reverse ++ rb)⟩
        (shifted pos (-(xs.length + 1 : ℤ))) := by
  induction xs generalizing ys ra rb pos with
  | nil =>
    have hy : ys = [] := List.length_eq_zero_iff.mp h.symm
    subst ys
    rw [show 2 * (([] : List Bool).length + 1) = 2 by rfl,
      back_pair r (⟨symbols [] ++ [Sym.start], ra⟩ : Tape Bool) (⟨symbols [] ++ [Sym.start], rb⟩ : Tape Bool) pos hr]
    rfl
  | cons a xs ih =>
    cases ys with
    | nil => simp at h
    | cons b ys =>
      have ht : xs.length = ys.length := by simpa using h
      rw [show 2 * ((a :: xs).length + 1) = 2 + 2 * (xs.length + 1) by simp; omega,
        execute_add,
        back_pair r (⟨symbols (a :: xs) ++ [Sym.start], ra⟩ : Tape Bool)
          (⟨symbols (b :: ys) ++ [Sym.start], rb⟩ : Tape Bool) pos hr]
      change execute (2 * (xs.length + 1))
        (cfg (.back r) ⟨symbols xs ++ [.start], .data a :: ra⟩
          ⟨symbols ys ++ [.start], .data b :: rb⟩ (shifted pos (-1))) = _
      rw [ih _ ht _ _ (by simp)]
      simp [symbols, List.reverse_cons, List.append_assoc, shifted_shifted,
        add_comm, add_left_comm]

def marked (xs : List Bool) : Tape Bool := ⟨[.start], symbols xs ++ [.stop]⟩

theorem comparator_run (r : Result) (xs ys : List Bool) (h : xs.length = ys.length)
    (pos : Fin 2 → ℤ) :
    execute (5 * xs.length + 6) (cfg (.scan r) (marked xs) (marked ys) pos) =
      cfg (.done (numeric r (value xs) (value ys))) (marked xs) (marked ys) pos := by
  unfold marked
  rw [show 5 * xs.length + 6 = 3 * xs.length + (2 + (2 * (xs.length + 1) + 2)) by omega,
    execute_add]
  rw [forward_run r xs ys h, execute_add, at_ends, execute_add]
  have hr := backward_run (scan r xs ys) xs.reverse ys.reverse (by simpa using h)
    [Sym.stop] [Sym.stop] (by simp) (shifted pos xs.length)
  simp only [List.length_reverse, List.reverse_reverse] at hr
  have hm (zs : List Bool) : symbols zs.reverse = (symbols zs).reverse := by
    simp [symbols]
  rw [hm xs, hm ys] at hr
  rw [hr, return_pair, shifted_shifted, shifted_shifted]
  have he : (xs.length : ℤ) + (-(xs.length + 1) + 1) = 0 := by omega
  rw [he, shifted_zero, scan_numeric _ _ _ h]

/-- This active trace can be lifted into a larger caller with return
continuations, without executing the comparator's final halt instruction. -/
theorem comparison_trace (xs ys : List Bool) (h : xs.length = ys.length)
    (pos : Fin 2 → ℤ) :
    ∃ t ≤ 5 * xs.length + 6,
      OperationalTrace.Trace (NativeMicrocode.step program) (NativeMicrocode.Active program) t
        (cfg (.scan .equal) (marked xs) (marked ys) pos).denote
        (cfg (.done (numeric .equal (value xs) (value ys))) (marked xs) (marked ys) pos).denote :=
  NativeZipper.trace_of_run program (comparator_run .equal xs ys h pos)

noncomputable def nativeEncoding :
    NativeMicrocode.Encoding (Fin 2) Label 2 (Fintype.card Label - 1) where
  port := Equiv.refl _
  label := (NativeMicrocode.initialEncoding (T := Fin 2) (Label.scan .equal)).label

noncomputable def nativeMachine : Transpose.TM := NativeMicrocode.machine nativeEncoding program

theorem native_resources : nativeMachine.k = 2 ∧ nativeMachine.g + 1 = 5 ∧
    nativeMachine.q + 1 = 28 := by
  change 2 = 2 ∧ 4 + 1 = 5 ∧ (Fintype.card Label - 1) + 1 = 28
  rw [fixed_resources.2.2]
  decide

theorem native_start_zero : nativeEncoding.label (.scan .equal) = 0 :=
  NativeMicrocode.initialEncoding_start (T := Fin 2) (Label.scan .equal)

/-- Prepared inputs, arbitrary native input/output context and original
absolute head positions. The result is reported in the finite control. -/
theorem native_comparison {q : ℕ} (e : NativeMicrocode.Encoding (Fin 2) Label 2 q)
    (xs ys : List Bool) (h : xs.length = ys.length) (pos : Fin 2 → ℤ)
    (w : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ 5 * xs.length + 6,
      Transpose.stepN (NativeMicrocode.machine e program) w t
        ((cfg (.scan .equal) (marked xs) (marked ys) pos).denote.denote e program
          inputPos outRev) =
        some ((cfg (.done (numeric .equal (value xs) (value ys)))
          (marked xs) (marked ys) pos).denote.denote e program inputPos outRev) ∧
      Transpose.step (NativeMicrocode.machine e program) w
        ((cfg (.done (numeric .equal (value xs) (value ys)))
          (marked xs) (marked ys) pos).denote.denote e program inputPos outRev) = none := by
  apply NativeZipper.stopped_subroutine e program w inputPos outRev
    (comparator_run .equal xs ys h pos)
  simp [NativeMicrocode.Active, NativeZipper.Config.denote, Microcode.Config.denote,
    cfg, program]

end TransposeFollowup.BinaryCompare
