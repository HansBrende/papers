import BitWord.NativeReductionMachine
import BitWord.NativeStagesCanonical

namespace BitWord.NativeReductionMachine
open FixedTapeCompiler TransposeFollowup CopyMachine NativeExpanderShearFrames
set_option autoImplicit false
noncomputable section

def blank (M : Transpose.TM) : Bank M := fun _ => ⟨[],[]⟩
def prepared (M : Transpose.TM) (w xs : List Bool) : Bank M
  | .prepare p => NativePrepare.final w xs p
  | _ => ⟨[],[]⟩
def bank (M : Transpose.TM) (w xs raw : List Bool) (clock : Tape Bool) : Bank M :=
  Function.update (Function.update (prepared M w xs) (main M) (Counter.marked raw))
    (.data (NativeGate.halfRuler M)) clock

@[simp] theorem prepared_prepare (M : Transpose.TM) (w xs : List Bool) (p : NativePrepare.Port) :
    prepared M w xs (.prepare p)=NativePrepare.final w xs p := rfl
@[simp] theorem bank_main (M : Transpose.TM) (w xs raw : List Bool) (clock : Tape Bool) :
    bank M w xs raw clock (main M)=Counter.marked raw := by simp [bank,main]
@[simp] theorem bank_clock (M : Transpose.TM) (w xs raw : List Bool) (clock : Tape Bool) :
    bank M w xs raw clock (.data (NativeGate.halfRuler M))=clock := by simp [bank]
@[simp] theorem bank_normalize (M : Transpose.TM) (w xs raw : List Bool) (clock : Tape Bool) (i : Fin 2) :
    bank M w xs raw clock (.normalize i)=⟨[],[]⟩ := by simp [bank,main,prepared]
@[simp] theorem bank_half (M : Transpose.TM) (w xs raw : List Bool) (clock : Tape Bool) (i : Fin 3) :
    bank M w xs raw clock (.half i)=⟨[],[]⟩ := by simp [bank,main,prepared]

theorem bank_prepare (M : Transpose.TM) (w xs raw : List Bool) (clock : Tape Bool)
    (p : NativePrepare.Port) (hp : p≠NativePrepare.mainPort) :
    bank M w xs raw clock (.prepare p)=NativePrepare.final w xs p := by
  simp [bank,main,hp]

theorem bank_data (M : Transpose.TM) (w xs raw : List Bool) (clock : Tape Bool)
    (p : NativeStages.DataPort M) (hp : p≠NativeGate.halfRuler M) :
    bank M w xs raw clock (.data p)=⟨[],[]⟩ := by simp [bank,main,prepared,hp]

@[simp] theorem bank_update_main (M : Transpose.TM) (w xs raw out : List Bool) (clock : Tape Bool) :
    Function.update (bank M w xs raw clock) (main M) (Counter.marked out)=bank M w xs out clock := by
  funext p
  by_cases hp : p=main M <;> by_cases hc : p=.data (NativeGate.halfRuler M) <;>
    simp_all [bank,main]
@[simp] theorem bank_update_clock (M : Transpose.TM) (w xs raw : List Bool) (clock out : Tape Bool) :
    Function.update (bank M w xs raw clock) (.data (NativeGate.halfRuler M)) out=bank M w xs raw out := by
  simp [bank,Function.update_idem]

theorem bank_initial (M : Transpose.TM) (w xs : List Bool) : bank M w xs w ⟨[],[]⟩=prepared M w xs := by
  funext p
  cases p with
  | prepare p =>
    by_cases hp : p=NativePrepare.mainPort
    · subst p; exact (bank_main M w xs w _).trans (NativePrepare.final_payload w xs).symm
    · exact bank_prepare M w xs w _ p hp
  | data p => by_cases hp : p=NativeGate.halfRuler M <;> simp_all [bank,main,prepared]
  | normalize p => exact bank_normalize M w xs w _ p
  | half p => exact bank_half M w xs w _ p

theorem prepare_values (M : Transpose.TM) (w xs : List Bool) :
    (prepareBinding M).values (NativePrepare.final w xs) (blank M)=prepared M w xs := by
  funext p
  cases p with
  | prepare p => exact (prepareBinding M).values_at _ _ p
  | data p => exact fixedBinding_values_outside _ _ _ _ (by simp)
  | normalize p => exact fixedBinding_values_outside _ _ _ _ (by simp)
  | half p => exact fixedBinding_values_outside _ _ _ _ (by simp)

def H (xs : List Bool) := NativePrepare.h xs
def D (xs : List Bool) := 2^H xs
def B (xs : List Bool) := 2^tailBits (H xs)
def nword (xs : List Bool) := NativeCanonicalGenerator.fieldWord (H xs) .n
def params (xs : List Bool) (i : Fin 13) := NativeCanonicalGenerator.fieldWord (H xs) (.parameter i)
def codes (xs : List Bool) (i : Fin 13) := NativeSmallDescriptors.opcodeWord ((canonicalGates (H xs))[i.val]?)

end
end BitWord.NativeReductionMachine
