import LeanMachine.InvolutionSums
import LeanMachine.DisjointSumsDeletion

/-! # Omitted individual involution shifts

An arbitrary subset of nontrivial orbits is omitted. Keep the other pair
blocks and pin both coordinates of every omitted orbit. The resulting
weighted kernel is exactly the orbit-constant subgroup with those shifts
set to zero; fixed-coordinate shifts remain available.
-/

namespace LeanMachine.InvolutionSums

open Finset
open scoped Classical
noncomputable section

variable {V A : Type*} [Fintype V] (m : V → V) (hm : Function.Involutive m)
variable (O : Finset (representatives m))

/-- Both endpoints of every omitted nontrivial orbit. -/
def omittedCells : Finset V := O.biUnion (blocks m hm).support

/-- The original active bank, selected from the omitted-orbit list. -/
def activeBlocks : DisjointSums V ↥Oᶜ := (blocks m hm).restrictBlocks (↑Oᶜ)

/-- Omitted coordinates are disjoint from the active bank. -/
theorem omitted_free (p : ↥Oᶜ) (v : V) (hv : v ∈ omittedCells m hm O) :
    v ∉ (activeBlocks m hm O).support p := by
  intro hp
  obtain ⟨q, hq, hvq⟩ := mem_biUnion.mp hv
  have hne : p.val ≠ q := fun he => (mem_compl.mp p.property) (he ▸ hq)
  exact disjoint_left.mp ((blocks m hm).disjoint hne) hp hvq

/-- Exactly two pinned coordinates per omitted orbit. -/
theorem omittedCells_card : (omittedCells m hm O).card = 2 * O.card := by
  rw [omittedCells, card_biUnion (fun p _ q _ h => (blocks m hm).disjoint h)]
  simp [support_card, Nat.mul_comm]

/-- Fixed coordinates are never omitted by an omitted-pair list. -/
theorem fixed_not_omitted {v : V} (hv : m v = v) : v ∉ omittedCells m hm O := by
  intro h
  obtain ⟨p, _, hp⟩ := mem_biUnion.mp h
  exact fixed_not_mem_support m hm hv p hp

include hm in
/-- Exact partition into active pairs, omitted pairs and fixed coordinates. -/
theorem active_card_partition :
    2 * Fintype.card ↥Oᶜ + (fixedCells m).card + 2 * O.card = Fintype.card V := by
  have h := card_partition m hm
  rw [← fixedCells_card m] at h
  have ho := O.card_le_univ
  simp only [Fintype.card_coe] at ho
  simp only [Fintype.card_coe, card_compl]
  omega

variable [AddCommGroup A]

/-- Missing individual shifts mean orbit-constant shifts vanishing on the omitted cells. -/
def activeShifts : AddSubgroup (V → A) :=
  (orbitConstant m) ⊓
  { carrier := {z | Set.EqOn z 0 (↑(omittedCells m hm O))}
    zero_mem' := by intro v _; rfl
    add_mem' := by intro x y hx hy v hv; simp [hx hv, hy hv]
    neg_mem' := by intro x hx v hv; simp [hx hv] }

/-- With no omitted pairs, all orbit-constant shifts are available. -/
@[simp] theorem activeShifts_empty :
    activeShifts (A := A) m hm ∅ = orbitConstant m := by
  ext z
  simp [activeShifts, omittedCells]

/-- The active pinned kernel grants exactly the requested individual shifts. -/
theorem active_kernel_iff (z : V → A) :
    ((activeBlocks m hm O).weightedEncode (weights m) z = 0 ∧
      Set.EqOn z 0 (↑(omittedCells m hm O))) ↔ z ∈ activeShifts m hm O := by
  change _ ↔ z ∈ orbitConstant m ∧ Set.EqOn z 0 (↑(omittedCells m hm O))
  constructor
  · rintro ⟨hz, hp⟩
    refine ⟨?_, hp⟩
    rw [← kernel_eq m hm]
    change (blocks m hm).weightedEncode (weights m) z = 0
    funext p
    by_cases hO : p ∈ O
    · rw [encode_apply]
      have h₁ : z p.val = 0 := hp (mem_biUnion.mpr ⟨p, hO, by simp [blocks]⟩)
      have h₂ : z (m p.val) = 0 := hp (mem_biUnion.mpr ⟨p, hO, by simp [blocks]⟩)
      change z p.val - z (m p.val) = 0
      exact sub_eq_zero.mpr (h₁.trans h₂.symm)
    · exact congrFun hz ⟨p, mem_compl.mpr hO⟩
  · rintro ⟨hz, hp⟩
    rw [← kernel_eq m hm] at hz
    refine ⟨?_, hp⟩
    funext p
    exact congrFun hz p.val

/-- Subgroup form of the active-kernel identification. -/
theorem pinned_active_kernel_eq :
    (((activeBlocks m hm O).withPins (↑(omittedCells m hm O))
      (omitted_free m hm O)).weightedEncode (weights m) (A := A)).ker =
        activeShifts m hm O := by
  ext z
  exact ((activeBlocks m hm O).withPins_encode_eq_zero_iff
    (↑(omittedCells m hm O)) (omitted_free m hm O) (weights m) z).trans
    (active_kernel_iff m hm O z)

/-- Omitted pairs remove exactly one independent orbit shift each. -/
theorem card_activeShifts [Fintype A] :
    Nat.card (activeShifts (A := A) m hm O) =
      Fintype.card A ^ ((Fintype.card V + (fixedCells m).card) / 2 - O.card) := by
  rw [← pinned_active_kernel_eq m hm O]
  rw [(activeBlocks m hm O).card_pinned_kernel]
  have hp : Nat.card (↑(omittedCells m hm O) : Set V) = 2 * O.card := by
    change Nat.card ↥(omittedCells m hm O) = _
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, omittedCells_card]
  rw [hp]
  have h := active_card_partition m hm O
  simp only [Fintype.card_coe] at h
  simp only [Fintype.card_coe]
  congr 1
  omega

end
end LeanMachine.InvolutionSums
