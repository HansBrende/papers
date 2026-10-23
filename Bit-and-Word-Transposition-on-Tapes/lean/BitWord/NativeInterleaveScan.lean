import BitWord.NativeSplitScan

/-! Literal three-tape interleaving scan. The equal-length hypothesis concerns
its two data streams; the controller and its resources do not depend on length. -/
namespace BitWord.NativeInterleaveScan
open FixedTapeCompiler CopyMachine TransposeFollowup

inductive Label | scan (odd : Bool) | write (odd bit : Bool) | done | reject
  deriving DecidableEq, Fintype

def source (odd : Bool) : Fin 3 := if odd then 2 else 1

def program : Microcode.Program (Fin 3) Label
  | .scan odd => .read (source odd) (fun s => match s with
      | .data b => .write odd b | .stop => if odd then .reject else .done | _ => .reject)
  | .write odd b => .act
      (fun p => if p=0 then ⟨some (.data b),.right⟩
        else if p=source odd then ⟨none,.right⟩ else ⟨none,.stay⟩)
      (.scan (!odd))
  | .done => .halt
  | .reject => .reject

def interleave : List Bool → List Bool → List Bool
  | a::as,b::bs => a::b::interleave as bs
  | _,_ => []

theorem interleave_length (a b : List Bool) (h : a.length=b.length) :
    (interleave a b).length=2*a.length := by
  induction a generalizing b with
  | nil => simp [interleave]
  | cons x xs ih =>
    cases b with
    | nil => simp at h
    | cons y ys =>
      simp only [List.length_cons] at h
      simp [interleave,ih ys (by omega)]
      omega

abbrev positions := NativeSplitScan.positions

def cfg (pc : Label) (out a b : Tape Bool) (pos : Fin 3 → ℤ) :
    NativeZipper.Config (Fin 3) Label := ⟨⟨pc,![out,a,b]⟩,pos⟩

theorem scan_pair (a b : Bool) (al ar bl br : List (Sym Bool))
    (pre : List Bool) (pos : Fin 3 → ℤ) :
    NativeZipper.run program 4
      (cfg (.scan false) (NativeSealBack.openWord pre) ⟨al,.data a::ar⟩ ⟨bl,.data b::br⟩ pos) =
      cfg (.scan false) (NativeSealBack.openWord (pre++[a,b])) ⟨.data a::al,ar⟩ ⟨.data b::bl,br⟩
        (positions pos 2 1 1) := by
  simp [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,
    program,source,cfg,Tape.read,Microcode.Action.apply,Tape.write,Tape.moveRight,
    NativeSealBack.openWord,symbols,List.reverse_append,NativeMicrocode.direction,Transpose.Dir.shift]
  constructor <;> funext t <;> fin_cases t <;> simp [NativeSplitScan.positions] <;> ring

theorem scan_stop (al ar bl br : List (Sym Bool)) (out : Tape Bool) (pos : Fin 3 → ℤ) :
    NativeZipper.run program 1 (cfg (.scan false) out ⟨al,.stop::ar⟩ ⟨bl,.stop::br⟩ pos) =
      cfg .done out ⟨al,.stop::ar⟩ ⟨bl,.stop::br⟩ pos := by
  simp [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,
    program,source,cfg,Tape.read]

theorem interleave_run (a b : List Bool) (h : a.length=b.length)
    (al ar bl br : List (Sym Bool)) (pre : List Bool) (pos : Fin 3 → ℤ) :
    NativeZipper.run program (4*a.length+1)
      (cfg (.scan false) (NativeSealBack.openWord pre)
        ⟨al,symbols a++.stop::ar⟩ ⟨bl,symbols b++.stop::br⟩ pos) =
      cfg .done (NativeSealBack.openWord (pre++interleave a b))
        ⟨(symbols a).reverse++al,.stop::ar⟩ ⟨(symbols b).reverse++bl,.stop::br⟩
        (positions pos (2*a.length) a.length b.length) := by
  induction a generalizing b al bl pre pos with
  | nil =>
    have hb : b=[] := List.length_eq_zero_iff.mp (by simpa using h.symm)
    subst b
    simpa [interleave,symbols,positions] using scan_stop al ar bl br (NativeSealBack.openWord pre) pos
  | cons x xs ih =>
    cases b with
    | nil => simp at h
    | cons y ys =>
      have hxy : xs.length=ys.length := by simpa using h
      rw [show 4*(x::xs).length+1=4+(4*xs.length+1) by simp; omega,NativeZipper.run_add]
      change NativeZipper.run program (4*xs.length+1)
        (NativeZipper.run program 4 (cfg (.scan false) (NativeSealBack.openWord pre)
          ⟨al,.data x::(symbols xs++.stop::ar)⟩ ⟨bl,.data y::(symbols ys++.stop::br)⟩ pos)) = _
      rw [scan_pair,ih ys hxy]
      simp only [positions]
      rw [NativeSplitScan.positions_add]
      simp [interleave,symbols,List.reverse_cons,List.append_assoc,Nat.add_comm,Nat.mul_add]

abbrev Trace := OperationalTrace.Trace (NativeMicrocode.step program) (NativeMicrocode.Active program)

theorem interleave_trace (a b : List Bool) (h : a.length=b.length)
    (al ar bl br : List (Sym Bool)) (pre : List Bool) (pos : Fin 3 → ℤ) :
    ∃ t ≤ 4*a.length+1,Trace t
      (cfg (.scan false) (NativeSealBack.openWord pre)
        ⟨al,symbols a++.stop::ar⟩ ⟨bl,symbols b++.stop::br⟩ pos).denote
      (cfg .done (NativeSealBack.openWord (pre++interleave a b))
        ⟨(symbols a).reverse++al,.stop::ar⟩ ⟨(symbols b).reverse++bl,.stop::br⟩
        (positions pos (2*a.length) a.length b.length)).denote :=
  NativeZipper.trace_of_run program (interleave_run a b h al ar bl br pre pos)

end BitWord.NativeInterleaveScan
