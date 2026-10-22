import TransposeFollowup.PrefixMembershipLoop

/-! Skip a fixed number of STOP-delimited bit batches. Batch lengths and
record coordinates are not control inputs. Both reads and moves are paid. -/
namespace TransposeFollowup.NativeBatchSkip
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

inductive Label (K : ℕ)
  | read (i : Fin K)
  | dataStep (i : Fin K)
  | stopStep (i : Fin K)
  | done
  | reject
  deriving DecidableEq,Fintype
def entry (K k : ℕ) : Label K := if h : k<K then .read ⟨k,h⟩ else .done
def program (K : ℕ) : Microcode.Program (Fin 1) (Label K)
  | .read i => .read 0 (fun s => match s with | .data _ => .dataStep i | .stop => .stopStep i | _ => .reject)
  | .dataStep i => .act (fun _ => ⟨none,.right⟩) (.read i)
  | .stopStep i => .act (fun _ => ⟨none,.right⟩) (entry K (i.val+1))
  | .done => .halt
  | .reject => .reject
def cfg {K : ℕ} (pc : Label K) (word : Tape Bool) (pos : Fin 1 → ℤ) : NativeZipper.Config (Fin 1) (Label K) :=
  ⟨⟨pc,fun _ => word⟩,pos⟩
def block (xs : List Bool) := symbols xs++[Sym.stop]
def stream {K : ℕ} (words : Fin K → List Bool) (k q : ℕ) := PrefixMembership.segments (fun i => block (words i)) k q

theorem data_two {K : ℕ} (i : Fin K) (b : Bool) (left right : List (Sym Bool)) (pos : Fin 1 → ℤ) :
    NativeZipper.run (program K) 2 (cfg (.read i) ⟨left,.data b::right⟩ pos)=
      cfg (.read i) ⟨.data b::left,right⟩ (fun p => pos p+1) := by
  simp [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,program,cfg,Microcode.Action.apply,
    Tape.moveRight,Tape.read,NativeMicrocode.direction,Transpose.Dir.shift]
theorem stop_two {K : ℕ} (i : Fin K) (left right : List (Sym Bool)) (pos : Fin 1 → ℤ) :
    NativeZipper.run (program K) 2 (cfg (.read i) ⟨left,.stop::right⟩ pos)=
      cfg (entry K (i.val+1)) ⟨.stop::left,right⟩ (fun p => pos p+1) := by
  simp [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,program,cfg,Microcode.Action.apply,
    Tape.moveRight,Tape.read,NativeMicrocode.direction,Transpose.Dir.shift]

theorem batch_run {K : ℕ} (i : Fin K) (xs : List Bool) (left suffix : List (Sym Bool)) (pos : Fin 1 → ℤ) :
    NativeZipper.run (program K) (2*(xs.length+1)) (cfg (.read i) ⟨left,block xs++suffix⟩ pos)=
      cfg (entry K (i.val+1)) ⟨(block xs).reverse++left,suffix⟩ (fun p => pos p+(xs.length+1 : ℕ)) := by
  induction xs generalizing left pos with
  | nil => simpa only [List.length_nil,zero_add,mul_one,block,symbols,List.map_nil,List.nil_append,
      List.singleton_append,List.reverse_singleton,Nat.cast_one] using stop_two i left suffix pos
  | cons b xs ih =>
    rw [show 2*((b::xs).length+1)=2+2*(xs.length+1) by simp;omega,NativeZipper.run_add]
    have he : block (b::xs)=Sym.data b::block xs := rfl
    rw [he,List.cons_append,data_two,ih]
    congr 1
    · simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
    · funext p;simp;ring

theorem batch_trace {K : ℕ} (i : Fin K) (xs : List Bool) (left suffix : List (Sym Bool)) (pos : Fin 1 → ℤ) :
    ∃ t ≤ 2*(block xs).length,
      OperationalTrace.Trace (NativeMicrocode.step (program K)) (NativeMicrocode.Active (program K)) t
        (cfg (entry K i.val) ⟨left,block xs++suffix⟩ pos).denote
        (cfg (entry K (i.val+1)) ⟨(block xs).reverse++left,suffix⟩ (fun p => pos p+(block xs).length)).denote := by
  have hi : entry K i.val=.read i := by simp only [entry,dite_eq_left i.isLt]
  simpa only [hi,block,List.length_append,symbols,List.length_map,List.length_singleton]
    using NativeZipper.trace_of_run (program K) (batch_run i xs left suffix pos)

theorem stream_nonblank {K : ℕ} (words : Fin K → List Bool) (k q : ℕ) :
    ∀ s ∈ stream words k q,s≠.blank := by
  induction q generalizing k with
  | zero => simp [stream,PrefixMembership.segments]
  | succ q ih =>
    unfold stream PrefixMembership.segments
    split
    · intro s hs
      rcases List.mem_append.mp hs with hs|hs
      · simp only [block,List.mem_append,List.mem_singleton] at hs
        rcases hs with hs|rfl
        · obtain ⟨b,_,rfl⟩:=List.mem_map.mp hs;simp
        · simp
      · exact ih (k+1) s hs
    · simp

end TransposeFollowup.NativeBatchSkip
