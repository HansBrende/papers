import TransposeFollowup.NativeTrimData

namespace TransposeFollowup.NativeTrim
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

inductive Label
  | scan | right | dropStop | check | dropZero | advance
  | seal (pc : NativeSealBack.Label)
  | done | reject
  deriving DecidableEq,Fintype

def binding : FinitePortBinding (Fin 1) (Fin 1) where
  ports:=Function.Embedding.refl _
  decode:=some
  decode_spec:=by intros; simp [eq_comm]

def program : Microcode.Program (Fin 1) Label
  | .scan => .read 0 (fun s => match s with | .data _ => .right | .stop => .dropStop | _ => .reject)
  | .right => .act (Microcode.single 0 ⟨none,.right⟩) .scan
  | .dropStop => .act (Microcode.single 0 ⟨some .blank,.left⟩) .check
  | .check => .read 0 (fun s => match s with | .data false => .dropZero | .data true | .start => .advance | _ => .reject)
  | .dropZero => .act (Microcode.single 0 ⟨some .blank,.left⟩) .check
  | .advance => .act (Microcode.single 0 ⟨none,.right⟩) (.seal .seal)
  | .seal .done => .jump .done
  | .seal pc => binding.instruction Label.seal (NativeSealBack.program pc)
  | .done => .halt
  | .reject => .reject

def cfg (pc : Label) (word : Tape Bool) (pos : Fin 1 → ℤ) : NativeZipper.Config (Fin 1) Label :=
  ⟨⟨pc,fun _ => word⟩,pos⟩
def cursor (pre rest : List Bool) : Tape Bool := ⟨(symbols pre).reverse++[.start],symbols rest++[.stop]⟩
def endBlank (xs : List Bool) (k : ℕ) : Tape Bool := ⟨(symbols xs).reverse++[.start],List.replicate k .blank⟩
def shift (pos : Fin 1 → ℤ) (d : ℤ) : Fin 1 → ℤ := fun t => pos t+d

theorem shift_zero (pos : Fin 1 → ℤ) : shift pos 0=pos := by funext t;simp [shift]
theorem shift_add (pos : Fin 1 → ℤ) (a b : ℤ) : shift (shift pos a) b=shift pos (a+b) := by
  funext t;simp [shift,add_assoc]

theorem cursor_start (xs : List Bool) : cursor [] xs=Counter.marked xs := rfl

theorem forward_step (pre rest : List Bool) (b : Bool) (pos : Fin 1 → ℤ) :
    NativeZipper.run program 2 (cfg .scan (cursor pre (b::rest)) pos)=
      cfg .scan (cursor (pre++[b]) rest) (shift pos 1) := by
  simp only [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,program,cfg,
    Microcode.single,Microcode.Action.apply,NativeMicrocode.direction,Transpose.Dir.shift,
    cursor,Tape.read,symbols,List.map_cons,List.cons_append,List.headD_cons]
  congr 2
  · funext t;fin_cases t;simp [Tape.moveRight,Tape.read,List.reverse_append]
  · funext t;fin_cases t;rfl

theorem forward_end (pre : List Bool) (pos : Fin 1 → ℤ) :
    NativeZipper.run program 1 (cfg .scan (cursor pre []) pos)=cfg .dropStop (cursor pre []) pos := rfl

theorem forward_run (pre rest : List Bool) (pos : Fin 1 → ℤ) :
    NativeZipper.run program (2*rest.length+1) (cfg .scan (cursor pre rest) pos)=
      cfg .dropStop (cursor (pre++rest) []) (shift pos rest.length) := by
  induction rest generalizing pre pos with
  | nil => simpa only [List.append_nil,List.length_nil,Nat.cast_zero,Nat.mul_zero,Nat.zero_add,shift_zero] using forward_end pre pos
  | cons b rest ih =>
    rw [show 2*(b::rest).length+1=2+(2*rest.length+1) by simp;omega,NativeZipper.run_add,
      forward_step,ih,shift_add]
    congr 2
    · simp [List.append_assoc]
    · simp only [List.length_cons,Nat.cast_add,Nat.cast_one];omega

theorem stop_run (xs : List Bool) (pos : Fin 1 → ℤ) :
    NativeZipper.run program 1 (cfg .dropStop (cursor xs []) pos)=
      cfg .check ((endBlank xs 1).moveLeft) (shift pos (-1)) := by
  simp only [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,program,cfg,
    Microcode.single,Microcode.Action.apply,NativeMicrocode.direction,Transpose.Dir.shift]
  congr 2
  · funext t;fin_cases t;rfl
  · funext t;fin_cases t;dsimp [shift];omega

theorem drop_run (xs : List Bool) (k : ℕ) (pos : Fin 1 → ℤ) :
    NativeZipper.run program 2 (cfg .check ((endBlank (xs++[false]) k).moveLeft) pos)=
      cfg .check ((endBlank xs (k+1)).moveLeft) (shift pos (-1)) := by
  simp only [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,program,cfg,
    Microcode.single,Microcode.Action.apply,NativeMicrocode.direction,Transpose.Dir.shift,
    endBlank,Tape.moveLeft,Tape.read,symbols,List.map_append,List.map_cons,List.map_nil,
    List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,List.cons_append,
    List.tail_cons,List.headD_cons]
  congr 2
  · funext t;fin_cases t;simp [Tape.write,List.replicate_succ]
  · funext t;fin_cases t;dsimp [shift];omega

theorem drop_zeroes_run (xs : List Bool) (k t : ℕ) (pos : Fin 1 → ℤ) :
    NativeZipper.run program (2*k) (cfg .check ((endBlank (xs++List.replicate k false) t).moveLeft) pos)=
      cfg .check ((endBlank xs (t+k)).moveLeft) (shift pos (-(k:ℤ))) := by
  induction k generalizing t pos with
  | zero => simp [List.replicate_zero,shift_zero,NativeZipper.run,OperationalTrace.run]
  | succ k ih =>
    rw [show 2*(k+1)=2+2*k by omega,NativeZipper.run_add,List.replicate_succ',← List.append_assoc,drop_run,ih,shift_add]
    rw [show t+1+k=t+(k+1) by omega,show (-1:ℤ)+ -(k:ℤ)= -((k+1:ℕ):ℤ) by omega]

theorem ready_run (xs : List Bool) (h : Normalized xs) (k : ℕ) (pos : Fin 1 → ℤ) :
    NativeZipper.run program 2 (cfg .check ((endBlank xs k).moveLeft) pos)=
      cfg (.seal .seal) (endBlank xs k) (shift pos 1) := by
  rcases h with rfl | ⟨pre,rfl⟩
  all_goals
    simp only [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,program,cfg,
      Microcode.single,Microcode.Action.apply,NativeMicrocode.direction,Transpose.Dir.shift,
      endBlank,Tape.moveLeft,Tape.read,symbols,List.map_append,List.map_cons,List.map_nil,
      List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,List.cons_append,
      List.tail_cons,List.headD_cons]
    congr 2
    · funext t;fin_cases t;rfl
    · funext t;fin_cases t;rfl

end TransposeFollowup.NativeTrim
