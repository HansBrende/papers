import StatementsRowSpread
import MotionDepthCodes.Clebsch

/-!
# A whole-row code above half on the far cells

The existing Clebsch storage code embeds on the diagonal of a 16-by-16
array. Its near cells are precisely the off-diagonal cells and are fixed
to zero. The sixteen far cells carry ten independent binary symbols.
This refutes the conditioned far-half principle; it does not refute an
upper bound charging all near cells of the full array.
-/

namespace LeanBacklog.FarClebsch

open Finset RowSpread MotionDepthCodes

/-- A row/column pair joined by a length-one or length-three walk in the
bipartite incidence graph of the helper-row relation. -/
def NearThree {d : ℕ} (ρ : Fin d → Finset (Fin d)) (i c : Fin d) : Prop :=
  i ∈ ρ c ∨ ∃ a j, a ∈ ρ c ∧ a ∈ ρ j ∧ i ∈ ρ j

instance {d : ℕ} (ρ : Fin d → Finset (Fin d)) (i c : Fin d) :
    Decidable (NearThree ρ i c) := by unfold NearThree; infer_instance

/-- The complement of the near cells, on the entire balanced grid. -/
def farCells {d : ℕ} (ρ : Fin d → Finset (Fin d)) : Finset (Entry d) :=
  univ.filter fun p => ¬ NearThree ρ p.1 p.2

section Placement

variable {d : ℕ} {α : Type*}

/-- Store coordinate `i` at `(i, f i)` and fix other entries. The placement
function need not be injective: different rows already separate its cells. -/
def placedWord (f : Fin d → Fin d) (zero : α) (x : Fin d → α) (p : Entry d) : α :=
  if f p.1 = p.2 then x p.1 else zero

@[simp] theorem placedWord_same (f : Fin d → Fin d) (zero : α)
    (x : Fin d → α) (i : Fin d) :
    placedWord f zero x (i, f i) = x i := by simp [placedWord]

theorem placedWord_injective (f : Fin d → Fin d) (zero : α) :
    Function.Injective (placedWord f zero) := by
  intro x y h
  funext i
  simpa using congrFun h (i, f i)

noncomputable def placedCode (f : Fin d → Fin d) (zero : α) (C : Finset (Fin d → α)) :
    Finset (Entry d → α) := by
  classical
  exact C.image (placedWord f zero)

@[simp] theorem card_placedCode (f : Fin d → Fin d) (zero : α) (C : Finset (Fin d → α)) :
    (placedCode f zero C).card = C.card := by
  classical
  exact card_image_of_injective C (placedWord_injective f zero)

/-- This embedding works for arbitrary alphabets and nonlinear storage
codes and every placement function, not merely permutations. -/
theorem placedCode_isWholeRow (f : Fin d → Fin d) (zero : α)
    (ρ : Fin d → Finset (Fin d)) (C : Finset (Fin d → α))
    (hC : IsStorageCode (fun i => ρ (f i)) C) :
    IsWholeRowCodeExcept ρ ∅ (placedCode f zero C) := by
  classical
  rw [wholeRowCode_iff]
  intro x hx y hy r _ hxy i
  obtain ⟨u, hu, rfl⟩ := mem_image.mp hx
  obtain ⟨v, hv, rfl⟩ := mem_image.mp hy
  by_cases hfi : f i = r
  · simp only [placedWord, hfi, ite_true]
    apply hC u hu v hv i
    intro j hj
    simpa using hxy j (by simpa [hfi] using hj) (f j)
  · simp [placedWord, hfi]

/-- Entries outside the placement stay constant. Keeping this generic
avoids unfolding an enumerated concrete code to extract an image witness. -/
theorem placedCode_offGraph_zero (f : Fin d → Fin d) (zero : α)
    (C : Finset (Fin d → α)) (x : Entry d → α) (hx : x ∈ placedCode f zero C)
    (i c : Fin d) (hfic : f i ≠ c) :
    x (i, c) = zero := by
  classical
  obtain ⟨u, _, rfl⟩ := mem_image.mp hx
  simp [placedWord, hfic]

/-- The former diagonal embedding is exactly identity placement. -/
abbrev diagonalWord (zero : α) := placedWord (d := d) id zero

@[simp] theorem diagonalWord_same (zero : α) (x : Fin d → α) (i : Fin d) :
    diagonalWord zero x (i, i) = x i := placedWord_same id zero x i

theorem diagonalWord_injective (zero : α) : Function.Injective (diagonalWord (d := d) zero) :=
  placedWord_injective id zero

noncomputable abbrev diagonalCode (zero : α) := placedCode (d := d) id zero

@[simp] theorem card_diagonalCode (zero : α) (C : Finset (Fin d → α)) :
    (diagonalCode zero C).card = C.card := card_placedCode id zero C

theorem diagonalCode_isWholeRow (zero : α) (ρ : Fin d → Finset (Fin d))
    (C : Finset (Fin d → α)) (hC : IsStorageCode ρ C) :
    IsWholeRowCodeExcept ρ ∅ (diagonalCode zero C) :=
  placedCode_isWholeRow id zero ρ C hC

theorem diagonalCode_offDiagonal_zero (zero : α) (C : Finset (Fin d → α))
    (x : Entry d → α) (hx : x ∈ diagonalCode zero C) (i c : Fin d) (hic : i ≠ c) :
    x (i, c) = zero := placedCode_offGraph_zero id zero C x hx i c hic

end Placement

/-- In the Clebsch incidence double, exactly the unequal-index cells are
at distance one or three. This is finite kernel-checked computation. -/
theorem clebsch_nearThree_iff (i c : Fin 16) :
    NearThree clebschNbhd i c ↔ i ≠ c := by
  revert i c
  decide

theorem clebsch_farCells_eq :
    farCells clebschNbhd = (univ : Finset (Fin 16)).image (fun i => (i, i)) := by
  ext ⟨i, c⟩
  simp [farCells, clebsch_nearThree_iff]

theorem clebsch_farCells_card : (farCells clebschNbhd).card = 16 := by
  rw [clebsch_farCells_eq, card_image_of_injective _
    (show Function.Injective (fun i : Fin 16 => (i, i)) from
      fun i j h => congrArg Prod.fst h)]
  simp

theorem clebsch_helper_card (c : Fin 16) : (clebschNbhd c).card = 5 := by
  revert c
  decide

noncomputable def farClebschCode : Finset (Entry 16 → ZMod 2) :=
  diagonalCode 0 clebschCode

theorem farClebschCode_isWholeRow :
    IsWholeRowCodeExcept clebschNbhd ∅ farClebschCode := by
  apply diagonalCode_isWholeRow
  simpa only [nbhd_clebschGraph] using clebschCode_isStorageCode

theorem farClebschCode_card : farClebschCode.card = 2 ^ 10 := by
  change (diagonalCode (0 : ZMod 2) clebschCode).card = 2 ^ 10
  rw [card_diagonalCode, clebschCode_card]

theorem farClebschCode_near_zero {x : Entry 16 → ZMod 2}
    (hx : x ∈ farClebschCode) (i c : Fin 16) (hnear : NearThree clebschNbhd i c) :
    x (i, c) = 0 := by
  exact diagonalCode_offDiagonal_zero 0 clebschCode x hx i c
    ((clebsch_nearThree_iff i c).mp hnear)

/-- The entire far set, with every near coordinate frozen, exceeds half.
The denominator counts all sixteen far cells, not only a selected support. -/
theorem farClebschCode_exceeds_half :
    2 ^ ((farCells clebschNbhd).card / 2) < farClebschCode.card := by
  rw [clebsch_farCells_card, farClebschCode_card]
  decide

#print axioms placedCode_isWholeRow
#print axioms card_placedCode
#print axioms diagonalCode_isWholeRow
#print axioms clebsch_nearThree_iff
#print axioms farClebschCode_isWholeRow
#print axioms farClebschCode_near_zero
#print axioms farClebschCode_exceeds_half

end LeanBacklog.FarClebsch
