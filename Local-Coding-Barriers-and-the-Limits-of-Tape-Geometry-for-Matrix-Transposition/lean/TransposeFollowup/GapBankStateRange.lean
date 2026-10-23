import TransposeFollowup.AdaptiveBankStrategy

/-! Restrict analytical gap states to their actual full-cube ranges. This
preserves the bank, executions and decoders, and prevents unused state labels
from strengthening the state-budget hypothesis. -/

namespace TransposeFollowup

open Classical
set_option autoImplicit false

namespace GapBank

variable {d b sigma : ℕ} (A : GapBank d b sigma)

noncomputable def reachableStates (I : Finset (Fin d)) : Finset (A.State I) :=
  Finset.univ.image (A.state I)

def StateRangeBudget (s : ℝ) : Prop := ∀ I, IsRowInterval I →
  ((A.reachableStates I).card : ℝ) ≤ (2 : ℝ)^s

noncomputable def restrictStates : GapBank d b sigma where
  recode := A.recode
  State I := {z // z ∈ A.reachableStates I}
  stateFinite _ := inferInstance
  state I x := ⟨A.state I x, Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩⟩
  forward_local := A.forward_local
  gap_inverse I hI x y hrows hs :=
    A.gap_inverse I hI x y hrows (congrArg Subtype.val hs)

@[simp] theorem restrictStates_recode : A.restrictStates.recode = A.recode := rfl

@[simp] theorem restrictStates_state (I : Finset (Fin d)) (x : FiniteMatrix d b) :
    (A.restrictStates.state I x).val = A.state I x := rfl

theorem restrictStates_budget_iff (s : ℝ) :
    A.restrictStates.StateBudget s ↔ A.StateRangeBudget s := by
  have hc (I : Finset (Fin d)) :
      Fintype.card (A.restrictStates.State I) = (A.reachableStates I).card :=
    Fintype.card_of_subtype (A.reachableStates I) (fun _ => Iff.rfl)
  simp only [StateBudget, StateRangeBudget, hc]

end GapBank

namespace GapBankCode

variable {d b sigma : ℕ} (C : GapBankCode d b sigma)

noncomputable def restrictStates : GapBankCode d b sigma :=
  { C with bank := C.bank.restrictStates }

@[simp] theorem restrictStates_transcript (x : FiniteMatrix d b) :
    C.restrictStates.transcript x = C.transcript x := rfl

@[simp] theorem restrictStates_correctOn (F : Set (FiniteMatrix d b)) :
    C.restrictStates.CorrectOn F ↔ C.CorrectOn F := Iff.rfl

end GapBankCode

namespace HelperGapBankStrategy

variable {d b sigma : ℕ} {H : Type*} (C : HelperGapBankStrategy d b sigma H)

noncomputable def restrictStates : HelperGapBankStrategy d b sigma H :=
  { C with bank := fun a => (C.bank a).restrictStates }

@[simp] theorem restrictStates_correctOn (F : Set (FiniteMatrix d b))
    (message : FiniteMatrix d b → List Bool) :
    C.restrictStates.CorrectOn F message ↔ C.CorrectOn F message := Iff.rfl

@[simp] theorem restrictStates_terminatesOn (F : Set (FiniteMatrix d b))
    (message : FiniteMatrix d b → List Bool) :
    C.restrictStates.TerminatesOn F message ↔ C.TerminatesOn F message := Iff.rfl

theorem restrictStates_budget (s : ℝ)
    (h : ∀ a, (C.bank a).StateRangeBudget s) :
    ∀ a, (C.restrictStates.bank a).StateBudget s :=
  fun a => ((C.bank a).restrictStates_budget_iff s).mpr (h a)

end HelperGapBankStrategy
end TransposeFollowup
