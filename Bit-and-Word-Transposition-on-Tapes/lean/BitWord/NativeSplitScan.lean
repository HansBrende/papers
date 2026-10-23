import TransposeFollowup.NativeSealBack

/-! A fixed three-tape controller separates alternating raw bits.  The scan
has two transitions per bit; tape heads and existing output prefixes are explicit. -/
namespace BitWord.NativeSplitScan
open FixedTapeCompiler CopyMachine TransposeFollowup

inductive Label | scan (odd : Bool) | write (odd bit : Bool) | done | reject
  deriving DecidableEq, Fintype

def target (odd : Bool) : Fin 3 := if odd then 2 else 1

def program : Microcode.Program (Fin 3) Label
  | .scan odd => .read 0 (fun s => match s with
      | .data b => .write odd b | .stop => .done | _ => .reject)
  | .write odd b => .act
      (fun p => if p=0 then ⟨none,.right⟩
        else if p=target odd then ⟨some (.data b),.right⟩ else ⟨none,.stay⟩)
      (.scan (!odd))
  | .done => .halt
  | .reject => .reject

def selected (wanted current : Bool) : List Bool → List Bool
  | [] => []
  | b::xs => if current=wanted then b::selected wanted (!current) xs
    else selected wanted (!current) xs

def bank (src even odd : Tape Bool) : Fin 3 → Tape Bool := ![src,even,odd]

def cfg (pc : Label) (src even odd : Tape Bool) (pos : Fin 3 → ℤ) :
    NativeZipper.Config (Fin 3) Label := ⟨⟨pc,bank src even odd⟩,pos⟩

def positions (pos : Fin 3 → ℤ) (n a b : ℕ) : Fin 3 → ℤ :=
  fun p => pos p + if p=0 then n else if p=1 then a else b

@[simp] theorem positions_zero (pos : Fin 3 → ℤ) : positions pos 0 0 0 = pos := by
  funext p
  simp [positions]

theorem positions_add (pos : Fin 3 → ℤ) (n a b m c d : ℕ) :
    positions (positions pos n a b) m c d = positions pos (n+m) (a+c) (b+d) := by
  funext p
  simp [positions]
  split_ifs <;> ring

theorem scan_bit (p b : Bool) (sl sr : List (Sym Bool)) (a c : List Bool)
    (pos : Fin 3 → ℤ) :
    NativeZipper.run program 2
      (cfg (.scan p) ⟨sl,.data b::sr⟩ (NativeSealBack.openWord a) (NativeSealBack.openWord c) pos) =
      cfg (.scan (!p)) ⟨.data b::sl,sr⟩
        (NativeSealBack.openWord (if p then a else a++[b]))
        (NativeSealBack.openWord (if p then c++[b] else c))
        (positions pos 1 (if p then 0 else 1) (if p then 1 else 0)) := by
  cases p <;>
    simp [NativeZipper.run, OperationalTrace.run, NativeZipper.step, Microcode.step,
      program, target, cfg, bank, Tape.read, Microcode.Action.apply, Tape.write,
      Tape.moveRight, NativeSealBack.openWord, symbols, List.reverse_append,
      NativeMicrocode.direction, Transpose.Dir.shift]
  all_goals constructor <;> funext t <;> fin_cases t <;> simp [positions]

theorem scan_stop (p : Bool) (sl sr : List (Sym Bool)) (a c : Tape Bool)
    (pos : Fin 3 → ℤ) :
    NativeZipper.run program 1 (cfg (.scan p) ⟨sl,.stop::sr⟩ a c pos) =
      cfg .done ⟨sl,.stop::sr⟩ a c pos := by
  simp [NativeZipper.run, OperationalTrace.run, NativeZipper.step, Microcode.step,
    program, cfg, bank, Tape.read]

/-- Exact native execution, with arbitrary origins and pre-existing prefixes. -/
theorem split_run (xs : List Bool) (p : Bool) (sl sr : List (Sym Bool))
    (a c : List Bool) (pos : Fin 3 → ℤ) :
    NativeZipper.run program (2*xs.length+1)
      (cfg (.scan p) ⟨sl,symbols xs++.stop::sr⟩
        (NativeSealBack.openWord a) (NativeSealBack.openWord c) pos) =
      cfg .done ⟨(symbols xs).reverse++sl,.stop::sr⟩
        (NativeSealBack.openWord (a++selected false p xs))
        (NativeSealBack.openWord (c++selected true p xs))
        (positions pos xs.length (selected false p xs).length (selected true p xs).length) := by
  induction xs generalizing p sl a c pos with
  | nil =>
    simpa [selected, symbols] using
      (scan_stop p sl sr (NativeSealBack.openWord a) (NativeSealBack.openWord c) pos)
  | cons b xs ih =>
    rw [show 2*(b::xs).length+1 = 2+(2*xs.length+1) by simp; omega,
      NativeZipper.run_add]
    change NativeZipper.run program (2*xs.length+1)
      (NativeZipper.run program 2 (cfg (.scan p) ⟨sl,.data b::(symbols xs++.stop::sr)⟩
        (NativeSealBack.openWord a) (NativeSealBack.openWord c) pos)) = _
    rw [scan_bit, ih, positions_add]
    cases p <;> simp [selected, symbols, List.reverse_cons, List.append_assoc,
      Nat.add_comm]

abbrev Trace := OperationalTrace.Trace (NativeMicrocode.step program) (NativeMicrocode.Active program)

theorem split_trace (xs : List Bool) (p : Bool) (sl sr : List (Sym Bool))
    (a c : List Bool) (pos : Fin 3 → ℤ) :
    ∃ t ≤ 2*xs.length+1, Trace t
      (cfg (.scan p) ⟨sl,symbols xs++.stop::sr⟩
        (NativeSealBack.openWord a) (NativeSealBack.openWord c) pos).denote
      (cfg .done ⟨(symbols xs).reverse++sl,.stop::sr⟩
        (NativeSealBack.openWord (a++selected false p xs))
        (NativeSealBack.openWord (c++selected true p xs))
        (positions pos xs.length (selected false p xs).length (selected true p xs).length)).denote :=
  NativeZipper.trace_of_run program (split_run xs p sl sr a c pos)

end BitWord.NativeSplitScan
