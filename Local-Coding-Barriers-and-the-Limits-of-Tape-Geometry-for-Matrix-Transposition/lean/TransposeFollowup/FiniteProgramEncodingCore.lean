import TransposeFollowup.NativeMicrocodeRunCore
import Mathlib.Data.Fintype.EquivFin

/-! Every fixed finite port/label system admits the original Fin encodings,
with any chosen start label mapped to native state zero. Choosing this
finite enumeration is part of fixing the machine, not a runtime operation. -/

namespace TransposeFollowup.NativeMicrocode

open FixedTapeCompiler
set_option autoImplicit false
variable {T L : Type*} [Fintype T] [Fintype L]

noncomputable def initialEncoding (start : L) :
    Encoding T L (Fintype.card T) (Fintype.card L - 1) := by
  classical
  letI : Nonempty L := ⟨start⟩
  have h : Fintype.card L = Fintype.card L - 1 + 1 := by
    have := Fintype.card_pos (α := L)
    omega
  let e : L ≃ Fin (Fintype.card L - 1 + 1) := Fintype.equivFinOfCardEq h
  exact ⟨Fintype.equivFin T, e.trans (Equiv.swap (e start) 0)⟩

@[simp] theorem initialEncoding_start (start : L) :
    (initialEncoding (T := T) start).label start = 0 := by
  classical
  simp [initialEncoding]


end TransposeFollowup.NativeMicrocode
