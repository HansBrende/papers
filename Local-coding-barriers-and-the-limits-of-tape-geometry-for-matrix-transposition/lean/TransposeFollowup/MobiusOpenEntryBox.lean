import TransposeFollowup.MobiusWalkEntrySupport

/-! An explicit open precompact neighborhood of each closed entry box. -/
namespace TransposeFollowup.RealMobius
open Classical Set
set_option autoImplicit false

def matrixOpenEntryBox (B : ℝ) : Set Group := {g | ∀ i j : Fin 2, |g i j| < B}

theorem matrixOpenEntryBox_isOpen (B : ℝ) : IsOpen (matrixOpenEntryBox B) := by
  change IsOpen {g : Group | ∀ i j : Fin 2, |g i j| < B}
  simp only [Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro j
  exact isOpen_lt (by fun_prop) continuous_const

theorem matrixOpenEntryBox_subset (B : ℝ) : matrixOpenEntryBox B ⊆ matrixEntryBox B :=
  fun _ hg i j => (hg i j).le

theorem matrixEntryBox_subset_open_add_one (B : ℝ) : matrixEntryBox B ⊆ matrixOpenEntryBox (B + 1) :=
  fun _ hg i j => lt_of_le_of_lt (hg i j) (by linarith)

theorem matrixEntryBox_inv_iff (B : ℝ) (g : Group) : g⁻¹ ∈ matrixEntryBox B ↔ g ∈ matrixEntryBox B := by
  constructor
  · intro h
    simpa only [inv_inv] using matrixEntryBox_inv h
  · exact matrixEntryBox_inv

end TransposeFollowup.RealMobius
