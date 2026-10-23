import MotionDepthCodes.StorageCode

/-!
# The Clebsch graph carries a binary storage code of dimension 10

The Clebsch graph (the folded 5-cube) has 16 vertices. Over `GF(2)` the matrix
`I + A` has rank 6, so its kernel is a storage code with `2^10` codewords: each
symbol is the sum of its five neighbours. This is the lower bound in
`gn(Clebsch) = 10`; the upper bound is a Shannon certificate for the rate
bound `5/8`.
-/

namespace MotionDepthCodes

open Finset
open scoped BigOperators
set_option autoImplicit false

/-- Neighbourhoods of the Clebsch graph. -/
def clebschNbhd : Fin 16 → Finset (Fin 16) :=
  ![{1, 2, 4, 8, 15}, {0, 3, 5, 9, 14}, {0, 3, 6, 10, 13}, {1, 2, 7, 11, 12},
    {0, 5, 6, 11, 12}, {1, 4, 7, 10, 13}, {2, 4, 7, 9, 14}, {3, 5, 6, 8, 15},
    {0, 7, 9, 10, 12}, {1, 6, 8, 11, 13}, {2, 5, 8, 11, 14}, {3, 4, 9, 10, 15},
    {3, 4, 8, 13, 14}, {2, 5, 9, 12, 15}, {1, 6, 10, 12, 15}, {0, 7, 11, 13, 14}]

/-- The Clebsch graph. -/
def clebschGraph : SimpleGraph (Fin 16) where
  Adj i j := j ∈ clebschNbhd i
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

instance : DecidableRel clebschGraph.Adj :=
  fun i j => inferInstanceAs (Decidable (j ∈ clebschNbhd i))

theorem nbhd_clebschGraph : nbhd clebschGraph = clebschNbhd := by
  decide

/-- The table is the folded 5-cube: `i ~ j` iff `i xor j` is a single bit or `15`. -/
theorem clebschGraph_adj_iff (i j : Fin 16) :
    clebschGraph.Adj i j ↔ (i.val ^^^ j.val) ∈ ({1, 2, 4, 8, 15} : Finset ℕ) := by
  revert i j
  decide

/-- A basis of the binary code `ker (I + A)`, systematic on the coordinates
`5, 6, 7, 9, 10, …, 15`. -/
def clebschBasis : Fin 10 → Fin 16 → ZMod 2 :=
  ![![0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0],
    ![1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0],
    ![0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0],
    ![1, 0, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0],
    ![1, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0],
    ![1, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1]]

/-- The systematic coordinates. -/
def clebschSystematic : Fin 10 → Fin 16 := ![5, 6, 7, 9, 10, 11, 12, 13, 14, 15]

theorem clebschBasis_parity :
    ∀ k v, clebschBasis k v = ∑ u ∈ clebschNbhd v, clebschBasis k u := by
  decide

theorem clebschBasis_systematic :
    ∀ k i, clebschBasis k (clebschSystematic i) = if k = i then 1 else 0 := by
  decide

/-- Encoding a 10-bit message as a codeword. -/
def clebschEncode (b : Fin 10 → ZMod 2) : Fin 16 → ZMod 2 :=
  fun v => ∑ k, b k * clebschBasis k v

theorem clebschEncode_parity (b : Fin 10 → ZMod 2) (v : Fin 16) :
    clebschEncode b v = ∑ u ∈ clebschNbhd v, clebschEncode b u := by
  simp only [clebschEncode]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [clebschBasis_parity k v, Finset.mul_sum]

theorem clebschEncode_injective : Function.Injective clebschEncode := by
  intro b b' h
  funext i
  have h1 := congrFun h (clebschSystematic i)
  simpa [clebschEncode, clebschBasis_systematic] using h1

/-- The binary storage code of the Clebsch graph. -/
def clebschCode : Finset (Fin 16 → ZMod 2) :=
  univ.image clebschEncode

theorem clebschCode_card : clebschCode.card = 2 ^ 10 := by
  rw [clebschCode, Finset.card_image_of_injective _ clebschEncode_injective,
    Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]

theorem clebschCode_isStorageCode : IsStorageCode (nbhd clebschGraph) clebschCode := by
  rw [nbhd_clebschGraph]
  intro x hx y hy v hxy
  obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨b', -, rfl⟩ := Finset.mem_image.mp hy
  rw [clebschEncode_parity b v, clebschEncode_parity b' v]
  exact Finset.sum_congr rfl hxy

/-- **Lower bound for `gn(Clebsch)`.** A binary storage code on the Clebsch
graph has `2^10` codewords. -/
theorem exists_clebsch_storageCode :
    ∃ C : Finset (Fin 16 → ZMod 2), IsStorageCode (nbhd clebschGraph) C ∧ C.card = 2 ^ 10 :=
  ⟨clebschCode, clebschCode_isStorageCode, clebschCode_card⟩

end MotionDepthCodes
