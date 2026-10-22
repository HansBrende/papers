import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

/-! Half-open real regions of actual integer ticks. Finite-union measure and
interval volume are imported from mathlib; endpoints retain exact ownership. -/
namespace TransposeFollowup.RegularMotion
open Classical Set MeasureTheory
open scoped BigOperators
set_option autoImplicit false

def tickCells {T : ℕ} (S : Finset (Fin T)) : Set ℝ :=
  ⋃ t ∈ S, Ico (t.val : ℝ) ((t.val : ℝ)+1)

theorem tickCells_subset_clock {T : ℕ} (S : Finset (Fin T)) :
    tickCells S ⊆ Ico (0 : ℝ) T := by
  intro x hx
  obtain ⟨t,ht⟩ := Set.mem_iUnion.mp hx
  obtain ⟨_,hx⟩ := Set.mem_iUnion.mp ht
  have htT : (t.val : ℝ)+1 ≤ T := by exact_mod_cast Nat.succ_le_of_lt t.isLt
  exact ⟨(Nat.cast_nonneg _).trans hx.1,hx.2.trans_le htT⟩

theorem mem_tickCells_iff {T : ℕ} (S : Finset (Fin T)) {x : ℝ} (hx : x ∈ Ico (0 : ℝ) T) :
    x ∈ tickCells S ↔ (⟨⌊x⌋₊,(Nat.floor_lt hx.1).mpr hx.2⟩ : Fin T) ∈ S := by
  constructor
  · intro hxS
    obtain ⟨t,ht⟩ := Set.mem_iUnion.mp hxS
    obtain ⟨ht,hxt⟩ := Set.mem_iUnion.mp ht
    have he : ⌊x⌋₊=t.val := Nat.floor_eq_on_Ico t.val x hxt
    have ht' : (⟨⌊x⌋₊,(Nat.floor_lt hx.1).mpr hx.2⟩ : Fin T)=t := Fin.ext he
    rw [ht']
    exact ht
  · intro ht
    exact Set.mem_iUnion.mpr ⟨⟨⌊x⌋₊,(Nat.floor_lt hx.1).mpr hx.2⟩,
      Set.mem_iUnion.mpr ⟨ht,Nat.floor_le hx.1,Nat.lt_floor_add_one x⟩⟩

theorem tickCells_measurable {T : ℕ} (S : Finset (Fin T)) : MeasurableSet (tickCells S) :=
  MeasurableSet.biUnion S.countable_toSet (fun _ _ => measurableSet_Ico)

theorem tickCells_volume_real {T : ℕ} (S : Finset (Fin T)) :
    volume.real (tickCells S)=(S.card : ℝ) := by
  have hd : (S : Set (Fin T)).PairwiseDisjoint
      (fun t => Ico (t.val : ℝ) ((t.val : ℝ)+1)) := by
    intro i hi j hj hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    exact hij (Fin.ext ((Nat.floor_eq_on_Ico i.val x hxi).symm.trans
      (Nat.floor_eq_on_Ico j.val x hxj)))
  have hfin : ∀ t ∈ S, volume (Ico (t.val : ℝ) ((t.val : ℝ)+1)) ≠ ⊤ := by
    intro i hi
    rw [Real.volume_Ico]
    exact ENNReal.ofReal_ne_top
  rw [tickCells,measureReal_biUnion_finset hd (fun _ _ => measurableSet_Ico) hfin]
  simp [Real.volume_real_Ico]

theorem tickCells_compl {T : ℕ} (S : Finset (Fin T)) :
    Ico (0 : ℝ) T \ tickCells S=tickCells Sᶜ := by
  ext x
  by_cases hx : x ∈ Ico (0 : ℝ) T
  · simp only [Set.mem_sdiff,hx,true_and,mem_tickCells_iff S hx,mem_tickCells_iff Sᶜ hx,
      Finset.mem_compl]
  · have hxc : x ∉ tickCells Sᶜ := fun h => hx (tickCells_subset_clock Sᶜ h)
    simp only [Set.mem_sdiff,hx,false_and,hxc]

end TransposeFollowup.RegularMotion
