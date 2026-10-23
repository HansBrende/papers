import BitWord.NativePrepareRun

namespace BitWord.NativePrepare
open FixedTapeCompiler CopyMachine TransposeFollowup

def mainPort : Port := .bootstrap NativeBootstrap.payload
def dimensionPort : Port := .bootstrap NativeBootstrap.dimension

theorem final_payload (w xs : List Bool) : final w xs mainPort=Counter.marked w := rfl

theorem final_rulers (w xs : List Bool) (p : NativeRulers.Port) :
    final w xs (rulerPort p)=NativeRulers.contents xs (hword xs) (wword xs) p := by
  change (rulersBinding.values _ _) (rulersBinding.ports p)=_
  rw [rulersBinding.values_at,NativeRulers.final_contents]

theorem final_dimension (w xs : List Bool) : final w xs dimensionPort=Counter.marked xs := by
  exact final_rulers w xs .dimension

theorem final_generator (w xs : List Bool) (p : NativeCanonicalGenerator.Port) :
    final w xs (generatorPort p)=NativeCanonicalGenerator.final (h xs) p := by
  cases p with
  | work p =>
    cases p with
    | h =>
      change Counter.marked (hword xs)=NativeCanonicalGenerator.final (h xs) (.work .h)
      exact (NativeCanonicalGenerator.final_h _).symm
    | double =>
      change Counter.marked (wword xs)=NativeCanonicalGenerator.final (h xs) (.work .double)
      exact (NativeCanonicalGenerator.final_fields _ .w).symm
    | u => rfl
    | tmpA => rfl
    | tmpB => rfl
    | base => rfl
    | wide => rfl
    | zero => rfl
    | inc => rfl
    | half => rfl
    | total => rfl
    | diff => rfl
  | opcode i => rfl
  | parameter i => rfl

theorem final_field (w xs : List Bool) (p : NativeSmallDescriptors.Port) :
    final w xs (generatorPort (NativeCanonicalGenerator.smallPort p))=
      Counter.marked (NativeCanonicalGenerator.fieldWord (h xs) p) := by
  rw [final_generator]
  exact NativeCanonicalGenerator.final_fields _ p

theorem final_hword (w xs : List Bool) :
    final w xs (.bootstrap .hword)=Counter.marked (hword xs) := by exact final_rulers w xs .hword

end BitWord.NativePrepare
