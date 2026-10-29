import SourceCovers.CausalAttachmentPaths
import Mathlib.Algebra.BigOperators.Fin

/-! Uniform allocation of each row's weighted paths among its original
group bits. Actual paths and all physical loads are preserved. -/

namespace SourceCovers.CausalGroups.Network

open LeanMachine Finset
open scoped BigOperators Classical
noncomputable section

variable {d b h n : ℕ} {Edge : Type*} [Fintype Edge] (G : Network d b h n Edge)

abbrev GroupCell (a : Fin h) := G.GroupColumn a × Fin b

def bitAt (a : Fin h) (i : Fin d) (c : G.GroupCell a) : G.GroupBit a :=
  ⟨(i, c.1.val, c.2), c.1.property⟩

def cellOf {a : Fin h} (ξ : G.GroupBit a) : G.GroupCell a :=
  (⟨ξ.val.2.1, ξ.property⟩, ξ.val.2.2)

theorem bitAt_eq_iff (a : Fin h) (i : Fin d) (c : G.GroupCell a) (ξ : G.GroupBit a) :
    G.bitAt a i c = ξ ↔ i = ξ.val.1 ∧ c = G.cellOf ξ := by
  rcases c with ⟨⟨j, hj⟩, t⟩
  rcases ξ with ⟨⟨i', j', t'⟩, hξ⟩
  simp [bitAt, cellOf, Subtype.ext_iff]

theorem card_groupCell (a : Fin h) :
    Fintype.card (G.GroupCell a) = Fintype.card (G.GroupColumn a) * b := by
  simp [GroupCell]

theorem card_groupCell_pos (a : Fin h) [Nonempty (G.GroupBit a)] :
    0 < Fintype.card (G.GroupCell a) := by
  apply Fintype.card_pos_iff.mpr
  exact ⟨G.cellOf (Classical.choice inferInstance)⟩

namespace FibreTyping

variable {G} {C : Set (Input d b)} (F : G.FibreTyping C)
variable (a : Fin h) [Nonempty (G.GroupBit a)]

/-- A bit is assigned a path from an actual attachment of its own row
to the collector sink. Returning to that bit's output is a later step. -/
structure BitPath where
  bit : G.GroupBit a
  attachment : Fin n
  attached : attachment ∈ G.attached bit.val.1
  path : (F.collectedFlow a).Path attachment (G.lastOutput a)

def AttachedPath.toBit (q : F.AttachedPath a) (c : G.GroupCell a) : F.BitPath a where
  bit := G.bitAt a q.attachment.val.1 c
  attachment := q.attachment.val.2
  attached := q.attachment.property
  path := q.path

abbrev AllocatedIndex (Q : List (ℝ × F.AttachedPath a)) := Fin Q.length × G.GroupCell a

def allocatedPath (Q : List (ℝ × F.AttachedPath a)) (i : F.AllocatedIndex a Q) :
    F.BitPath a := AttachedPath.toBit F a Q[i.1.val].2 i.2

def allocatedWeight (Q : List (ℝ × F.AttachedPath a)) (i : F.AllocatedIndex a Q) : ℝ :=
  Q[i.1.val].1 / Fintype.card (G.GroupCell a)

def allocatedMass (Q : List (ℝ × F.AttachedPath a)) : ℝ :=
  ∑ i : F.AllocatedIndex a Q, F.allocatedWeight a Q i

def allocatedLoad (Q : List (ℝ × F.AttachedPath a))
    (e : Edge ⊕ (G.collector a).Link) : ℝ :=
  ∑ i : F.AllocatedIndex a Q,
    F.allocatedWeight a Q i * (F.collectedFlow a).pathFlow (F.allocatedPath a Q i).path e

def allocatedBitMass (Q : List (ℝ × F.AttachedPath a)) (ξ : G.GroupBit a) : ℝ :=
  ∑ i : F.AllocatedIndex a Q,
    if (F.allocatedPath a Q i).bit = ξ then F.allocatedWeight a Q i else 0

theorem allocatedWeight_pos (Q : List (ℝ × F.AttachedPath a))
    (hQ : ∀ q ∈ Q, 0 < q.1) (i : F.AllocatedIndex a Q) :
    0 < F.allocatedWeight a Q i := by
  apply div_pos (hQ _ (List.getElem_mem i.1.isLt))
  exact_mod_cast G.card_groupCell_pos a

private theorem sum_cell_fraction (x : ℝ) :
    (∑ _c : G.GroupCell a, x / Fintype.card (G.GroupCell a)) = x := by
  have hn : (Fintype.card (G.GroupCell a) : ℝ) ≠ 0 :=
    ne_of_gt (by exact_mod_cast G.card_groupCell_pos a)
  simp only [sum_const, card_univ, nsmul_eq_mul]
  field_simp

/-- Equal splitting preserves the entire mass, including empty families. -/
theorem allocatedMass_eq (Q : List (ℝ × F.AttachedPath a)) :
    F.allocatedMass a Q = F.attachedMass a Q := by
  unfold allocatedMass
  rw [Fintype.sum_prod_type]
  simp only [allocatedWeight]
  calc
    _ = ∑ i : Fin Q.length, Q[i.val].1 := by
      apply sum_congr rfl
      intro i _
      exact sum_cell_fraction (G := G) a Q[i.val].1
    _ = _ := Fin.sum_univ_fun_getElem Q Prod.fst

/-- Every retained edge load is unchanged, including repeated traversals. -/
theorem allocatedLoad_eq (Q : List (ℝ × F.AttachedPath a))
    (e : Edge ⊕ (G.collector a).Link) :
    F.allocatedLoad a Q e = F.attachedLoad a Q e := by
  unfold allocatedLoad
  rw [Fintype.sum_prod_type]
  simp only [allocatedWeight, allocatedPath, AttachedPath.toBit]
  calc
    _ = ∑ i : Fin Q.length, Q[i.val].1 * (F.collectedFlow a).pathFlow Q[i.val].2.path e := by
      apply sum_congr rfl
      intro i _
      change (∑ _c : G.GroupCell a, Q[i.val].1 / (Fintype.card (G.GroupCell a) : ℝ) *
        (F.collectedFlow a).pathFlow Q[i.val].2.path e) = _
      rw [← Finset.sum_mul]
      exact congrArg (fun x => x * (F.collectedFlow a).pathFlow Q[i.val].2.path e)
        (sum_cell_fraction (G := G) a Q[i.val].1)
    _ = _ := Fin.sum_univ_fun_getElem Q
      (fun q => q.1 * (F.collectedFlow a).pathFlow q.2.path e)

/-- Each original bit receives exactly its row's total mass divided by
the number of original group bits in that row. -/
theorem allocatedBitMass_eq (Q : List (ℝ × F.AttachedPath a)) (ξ : G.GroupBit a) :
    F.allocatedBitMass a Q ξ =
      F.attachedRowMass a Q ξ.val.1 / Fintype.card (G.GroupCell a) := by
  unfold allocatedBitMass
  rw [Fintype.sum_prod_type]
  simp only [allocatedPath, AttachedPath.toBit, allocatedWeight, G.bitAt_eq_iff]
  calc
    _ = ∑ i : Fin Q.length,
        (if Q[i.val].2.attachment.val.1 = ξ.val.1 then Q[i.val].1 else 0) /
          Fintype.card (G.GroupCell a) := by
      apply sum_congr rfl
      intro i _
      by_cases hi : Q[i.val].2.attachment.val.1 = ξ.val.1 <;> simp [hi]
    _ = _ := by
      rw [← sum_div, Fin.sum_univ_fun_getElem Q
        (fun q => if q.2.attachment.val.1 = ξ.val.1 then q.1 else 0)]
      rfl

theorem allocatedBitMass_bounds (Q : List (ℝ × F.AttachedPath a))
    (hrow : ∀ i : Fin d, 0 ≤ F.attachedRowMass a Q i ∧
      F.attachedRowMass a Q i ≤ (Fintype.card (G.GroupColumn a) * b : ℕ))
    (ξ : G.GroupBit a) : 0 ≤ F.allocatedBitMass a Q ξ ∧ F.allocatedBitMass a Q ξ ≤ 1 := by
  rw [F.allocatedBitMass_eq]
  have hn : (0 : ℝ) < Fintype.card (G.GroupCell a) := by
    exact_mod_cast G.card_groupCell_pos a
  refine ⟨div_nonneg (hrow ξ.val.1).1 hn.le, (div_le_one hn).mpr ?_⟩
  simpa only [G.card_groupCell] using (hrow ξ.val.1).2

/-- Actual bit-labelled paths carry the full projected-support logarithm
without changing any physical load, and each bit's mass is at most one.
The paths end at the collector sink; return walks are not assumed here. -/
theorem exists_allocated_packing [Nonempty C] :
    ∃ Q : List (ℝ × F.AttachedPath a),
      (∀ i : F.AllocatedIndex a Q, 0 < F.allocatedWeight a Q i) ∧
      F.allocatedMass a Q =
        Real.logb 2 (Fintype.card (Set.range (fun x : C => G.projection a x.val))) ∧
      (∀ e, F.allocatedLoad a Q e ≤ F.collectedCost a e) ∧
      (∀ ξ : G.GroupBit a,
        0 ≤ F.allocatedBitMass a Q ξ ∧ F.allocatedBitMass a Q ξ ≤ 1) ∧
      (∀ ξ : G.GroupBit a, G.attached ξ.val.1 = ∅ → F.allocatedBitMass a Q ξ = 0) := by
  obtain ⟨Q, hQ, hm, hl, hr, _⟩ := F.exists_attached_packing a
  refine ⟨Q, F.allocatedWeight_pos a Q hQ, ?_, ?_, ?_, ?_⟩
  · rw [F.allocatedMass_eq]
    exact hm
  · intro e
    rw [F.allocatedLoad_eq]
    exact hl e
  · exact F.allocatedBitMass_bounds a Q (fun i => ⟨(hr i).1, (hr i).2.1⟩)
  · intro ξ hξ
    rw [F.allocatedBitMass_eq, (hr ξ.val.1).2.2 hξ, zero_div]

end FibreTyping
end
end SourceCovers.CausalGroups.Network
