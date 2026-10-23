import BitWord.NativeOracleBlockCalls

namespace BitWord.NativeOracleBlock
open FixedTapeCompiler TransposeFollowup CopyMachine
set_option autoImplicit false
noncomputable section

def layout {A : Type*} (M : Transpose.TM) (z i c : A) (o : Fin 3 → A) : Port M → A
  | .inl (.data .input) => i
  | .inl (.data .capture) => c
  | .inr p => o p
  | _ => z

@[simp] theorem layout_input {A : Type*} (M : Transpose.TM) (z i c : A) (o : Fin 3 → A) :
    layout M z i c o (input M)=i := rfl
@[simp] theorem layout_capture {A : Type*} (M : Transpose.TM) (z i c : A) (o : Fin 3 → A) :
    layout M z i c o (capture M)=c := rfl
@[simp] theorem layout_source {A : Type*} (M : Transpose.TM) (z i c : A) (o : Fin 3 → A) :
    layout M z i c o (source M)=o 0 := rfl
@[simp] theorem layout_target {A : Type*} (M : Transpose.TM) (z i c : A) (o : Fin 3 → A) :
    layout M z i c o (target M)=o 1 := rfl
@[simp] theorem layout_clock {A : Type*} (M : Transpose.TM) (z i c : A) (o : Fin 3 → A) :
    layout M z i c o (clock M)=o 2 := rfl

@[simp] theorem layout_update_input {A : Type*} (M : Transpose.TM) (z i c a : A) (o : Fin 3 → A) :
    Function.update (layout M z i c o) (input M) a=layout M z a c o := by
  funext p
  cases p with
  | inl p => cases p with
    | data p => cases p <;> simp [layout,input,NativeOracleReset.inputPort]
    | log r => simp [layout,input,NativeOracleReset.inputPort]
  | inr p => simp [layout,input,NativeOracleReset.inputPort]
@[simp] theorem layout_update_capture {A : Type*} (M : Transpose.TM) (z i c a : A) (o : Fin 3 → A) :
    Function.update (layout M z i c o) (capture M) a=layout M z i a o := by
  funext p
  cases p with
  | inl p => cases p with
    | data p => cases p <;> simp [layout,capture,NativeOracleReset.capturePort]
    | log r => simp [layout,capture,NativeOracleReset.capturePort]
  | inr p => simp [layout,capture,NativeOracleReset.capturePort]
@[simp] theorem layout_update_source {A : Type*} (M : Transpose.TM) (z i c a x y v : A) :
    Function.update (layout M z i c ![a,x,y]) (source M) v=layout M z i c ![v,x,y] := by
  funext p
  cases p with
  | inl p => cases p with
    | data p => cases p <;> simp [layout,source]
    | log r => simp [layout,source]
  | inr p => fin_cases p <;> simp [layout,source]
@[simp] theorem layout_update_target {A : Type*} (M : Transpose.TM) (z i c a x y v : A) :
    Function.update (layout M z i c ![a,x,y]) (target M) v=layout M z i c ![a,v,y] := by
  funext p
  cases p with
  | inl p => cases p with
    | data p => cases p <;> simp [layout,target]
    | log r => simp [layout,target]
  | inr p => fin_cases p <;> simp [layout,target]

theorem layout_initial_pool (M : Transpose.TM) (xs : List Bool) (o : Fin 3 → Tape Bool) (p : Pool M) :
    layout M ⟨[],[]⟩ (Counter.marked xs) (NativeSealBack.openWord []) o (.inl p)=
      NativeOracleReset.initialBank M xs p := by
  cases p with | data p => cases p <;> rfl | log r => rfl
@[simp] theorem layout_zero_pool (M : Transpose.TM) (o : Fin 3 → ℤ) (p : Pool M) :
    layout M 0 0 0 o (.inl p)=0 := by
  cases p with | data p => cases p <;> rfl | log r => rfl

@[simp] theorem layout_final_pool (M : Transpose.TM) (xs out : List Bool) (z i c : Tape Bool)
    (o : Fin 3 → Tape Bool) :
    poolSet M (NativeOracleReset.finalBank M xs out) (layout M z i c o)=
      layout M ⟨[],[]⟩ (Counter.marked xs) (NativeSealBack.openWord out) o := by
  funext p
  cases p with
  | inl p => cases p with
    | data p => cases p <;> rfl
    | log r => rfl
  | inr p => rfl
@[simp] theorem layout_final_positions (M : Transpose.TM) (out : List Bool) (z i c : ℤ) (o : Fin 3 → ℤ) :
    poolSet M (NativeOracleReset.finalPos M out) (layout M z i c o)=
      layout M (0:ℤ) 0 out.length o := by
  funext p
  cases p with
  | inl p => cases p with
    | data p => cases p <;> rfl
    | log r => rfl
  | inr p => rfl

end
end BitWord.NativeOracleBlock
