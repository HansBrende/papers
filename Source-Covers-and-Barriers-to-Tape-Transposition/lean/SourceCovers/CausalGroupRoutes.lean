import SourceCovers.CausalReturns

/-! Actual partial routes on one group fibre. Forward collector copies
and backward returns share the original physical edge capacities. -/

namespace SourceCovers.CausalGroups.Network

open LeanMachine FiniteFlow.Network Finset
open scoped BigOperators Classical
noncomputable section

variable {d b h n : ℕ} {Edge : Type*} [Fintype Edge] (G : Network d b h n Edge)

/-- A route ends at its raw bit's own output and begins at an actual
attachment of that bit's row. Both orientations count towards edge load. -/
structure BitRoute where
  bit : Bit d b
  attachment : Fin n
  attached : attachment ∈ G.attached bit.1
  path : G.physicalFlow.bidirected.Path attachment (G.output bit)

namespace FibreTyping

variable {G} {C : Set (Input d b)} (F : G.FibreTyping C)
variable (a : Fin h) [Nonempty (G.GroupBit a)]

def BitPath.forward (p : F.BitPath a) :
    G.physicalFlow.bidirected.Path p.attachment (G.lastOutput a) :=
  G.physicalFlow.forwardMap.path ((F.collectorMap a).path p.path)

theorem BitPath.forward_load (p : F.BitPath a) (e : Edge) :
    G.physicalFlow.walkLoad (p.forward F a) e =
      (F.collectedFlow a).pathFlow p.path (.inl e) +
        ∑ v : (G.collector a).Link, if G.collectorPhysical a (.inr v) = e then
          (F.collectedFlow a).pathFlow p.path (.inr v) else 0 :=
  (G.physicalFlow.walkLoad_forward ((F.collectorMap a).path p.path) e).trans
    (F.collectorMap_load a p.path e)

def BitPath.route (p : F.BitPath a) : G.BitRoute where
  bit := p.bit.val
  attachment := p.attachment
  attached := p.attached
  path := pathComp (p.forward F a) (G.outputReturn a p.bit)

def allocatedRoute (Q : List (ℝ × F.AttachedPath a)) (i : F.AllocatedIndex a Q) :
    G.BitRoute := (F.allocatedPath a Q i).route F a

theorem allocatedRoute_group (Q : List (ℝ × F.AttachedPath a))
    (i : F.AllocatedIndex a Q) : G.partition.group (F.allocatedRoute a Q i).bit.2.1 = a :=
  (F.allocatedPath a Q i).bit.property

def routedBitMass (Q : List (ℝ × F.AttachedPath a)) (ξ : Bit d b) : ℝ :=
  ∑ i : F.AllocatedIndex a Q,
    if (F.allocatedRoute a Q i).bit = ξ then F.allocatedWeight a Q i else 0

theorem routedBitMass_eq (Q : List (ℝ × F.AttachedPath a)) (ξ : G.GroupBit a) :
    F.routedBitMass a Q ξ.val = F.allocatedBitMass a Q ξ := by
  unfold routedBitMass allocatedBitMass
  apply sum_congr rfl
  intro i _
  change (if (F.allocatedPath a Q i).bit.val = ξ.val then F.allocatedWeight a Q i else 0) = _
  simp only [Subtype.ext_iff]

theorem routedBitMass_outside (Q : List (ℝ × F.AttachedPath a)) (ξ : Bit d b)
    (hξ : G.partition.group ξ.2.1 ≠ a) : F.routedBitMass a Q ξ = 0 := by
  apply sum_eq_zero
  intro i _
  apply ite_eq_right
  intro hi
  exact hξ (hi ▸ F.allocatedRoute_group a Q i)

theorem routedBitMass_bounds (Q : List (ℝ × F.AttachedPath a))
    (hb : ∀ ξ : G.GroupBit a,
      0 ≤ F.allocatedBitMass a Q ξ ∧ F.allocatedBitMass a Q ξ ≤ 1) (ξ : Bit d b) :
    0 ≤ F.routedBitMass a Q ξ ∧ F.routedBitMass a Q ξ ≤ 1 := by
  by_cases hξ : G.partition.group ξ.2.1 = a
  · rw [F.routedBitMass_eq a Q ⟨ξ, hξ⟩]
    exact hb ⟨ξ, hξ⟩
  · rw [F.routedBitMass_outside a Q ξ hξ]
    norm_num

theorem routedBitMass_unattached (Q : List (ℝ × F.AttachedPath a)) (ξ : Bit d b)
    (hξ : G.attached ξ.1 = ∅) : F.routedBitMass a Q ξ = 0 := by
  apply sum_eq_zero
  intro i _
  apply ite_eq_right
  intro hi
  have ha := (F.allocatedRoute a Q i).attached
  rw [hi, hξ] at ha
  exact ha

def forwardLoad (Q : List (ℝ × F.AttachedPath a)) (e : Edge) : ℝ :=
  ∑ i : F.AllocatedIndex a Q, F.allocatedWeight a Q i *
    G.physicalFlow.walkLoad ((F.allocatedPath a Q i).forward F a) e

def returnLoad (Q : List (ℝ × F.AttachedPath a)) (e : Edge) : ℝ :=
  ∑ i : F.AllocatedIndex a Q, F.allocatedWeight a Q i *
    G.physicalFlow.walkLoad (G.outputReturn a (F.allocatedPath a Q i).bit) e

def routedLoad (Q : List (ℝ × F.AttachedPath a)) (e : Edge) : ℝ :=
  ∑ i : F.AllocatedIndex a Q, F.allocatedWeight a Q i *
    G.physicalFlow.walkLoad (F.allocatedRoute a Q i).path e

/-- Grouping a weighted family by bit labels retains the exact mass. -/
theorem allocatedWeighted_eq (Q : List (ℝ × F.AttachedPath a)) (f : G.GroupBit a → ℝ) :
    (∑ i : F.AllocatedIndex a Q, F.allocatedWeight a Q i * f (F.allocatedPath a Q i).bit) =
      ∑ ξ : G.GroupBit a, F.allocatedBitMass a Q ξ * f ξ := by
  simp only [allocatedBitMass, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  simp [ite_mul, eq_comm]

/-- Collapsing copies preserves their load as an additional summand on
the matching original edge, even when paths traverse both copies. -/
theorem forwardLoad_eq (Q : List (ℝ × F.AttachedPath a)) (e : Edge) :
    F.forwardLoad a Q e = F.allocatedLoad a Q (.inl e) +
      ∑ v : (G.collector a).Link, if G.collectorPhysical a (.inr v) = e then
        F.allocatedLoad a Q (.inr v) else 0 := by
  simp only [forwardLoad, BitPath.forward_load, mul_add, mul_sum, sum_add_distrib]
  congr 1
  rw [sum_comm]
  apply sum_congr rfl
  intro v _
  by_cases he : G.collectorPhysical a (.inr v) = e <;> simp [he, allocatedLoad]

theorem forwardLoad_le (Q : List (ℝ × F.AttachedPath a))
    (hl : ∀ e, F.allocatedLoad a Q e ≤ F.collectedCost a e) (e : Edge) :
    F.forwardLoad a Q e ≤ F.allocation e a + G.copyCharge a e := by
  rw [F.forwardLoad_eq]
  apply add_le_add (hl (.inl e))
  apply sum_le_sum
  intro v _
  split_ifs <;> [exact hl (.inr v); exact le_rfl]

/-- Each return crossing is charged precisely to its bit's allocated mass. -/
theorem returnLoad_on_link (Q : List (ℝ × F.AttachedPath a)) (v : (G.collector a).Link) :
    F.returnLoad a Q (G.collectorPhysical a (.inr v)) =
      ∑ ξ : G.GroupBit a, if G.output ξ.val ≤ v.val then F.allocatedBitMass a Q ξ else 0 := by
  simp only [returnLoad, G.outputReturn_on_link]
  simpa only [mul_ite, mul_one, mul_zero] using
    F.allocatedWeighted_eq a Q (fun ξ => if G.output ξ.val ≤ v.val then 1 else 0)

theorem returnLoad_outside (Q : List (ℝ × F.AttachedPath a)) (e : Edge)
    (he : e ∉ Set.range (fun v : (G.collector a).Link => G.collectorPhysical a (.inr v))) :
    F.returnLoad a Q e = 0 := by
  simp [returnLoad, G.outputReturn_outside a _ e he]

/-- A unit cap per bit bounds returns by the prefix size, not the whole
group size. The labels may have arbitrary real weights. -/
theorem returnLoad_le (Q : List (ℝ × F.AttachedPath a))
    (hb : ∀ ξ : G.GroupBit a, F.allocatedBitMass a Q ξ ≤ 1) (e : Edge) :
    F.returnLoad a Q e ≤ G.copyCharge a e := by
  by_cases he : e ∈ Set.range (fun v : (G.collector a).Link => G.collectorPhysical a (.inr v))
  · obtain ⟨v, rfl⟩ := he
    rw [F.returnLoad_on_link, G.copyCharge_on_link]
    calc
      _ ≤ ∑ ξ : G.GroupBit a, if G.output ξ.val ≤ v.val then (1 : ℝ) else 0 := by
        apply sum_le_sum
        intro ξ _
        split_ifs <;> [exact hb ξ; exact le_rfl]
      _ = _ := by
        change (∑ ξ : G.GroupBit a, if G.output ξ.val ≤ v.val then (1 : ℝ) else 0) =
          (Fintype.card {ξ : G.GroupBit a // G.output ξ.val ≤ v.val} : ℝ)
        simp only [Fintype.card_subtype, card_eq_sum_ones, sum_filter,
          Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  · rw [F.returnLoad_outside a Q e he, G.copyCharge_outside a e he]

theorem routedLoad_eq (Q : List (ℝ × F.AttachedPath a)) (e : Edge) :
    F.routedLoad a Q e = F.forwardLoad a Q e + F.returnLoad a Q e := by
  simp only [routedLoad, allocatedRoute, BitPath.route, G.physicalFlow.walkLoad_comp,
    mul_add, sum_add_distrib]
  rfl

/-- Original fields, forward copies and backward returns are all charged.
The collector and return budget is twice the exact prefix charge. -/
theorem routedLoad_le (Q : List (ℝ × F.AttachedPath a))
    (hl : ∀ e, F.allocatedLoad a Q e ≤ F.collectedCost a e)
    (hb : ∀ ξ : G.GroupBit a, F.allocatedBitMass a Q ξ ≤ 1) (e : Edge) :
    F.routedLoad a Q e ≤ F.allocation e a + 2 * G.copyCharge a e := by
  rw [F.routedLoad_eq]
  have hf := F.forwardLoad_le a Q hl e
  have hr := F.returnLoad_le a Q hb e
  linarith

/-- The extra volume is twice the sum of the actual output delays. -/
theorem routedVolume_le (Q : List (ℝ × F.AttachedPath a))
    (hl : ∀ e, F.allocatedLoad a Q e ≤ F.collectedCost a e)
    (hb : ∀ ξ : G.GroupBit a, F.allocatedBitMass a Q ξ ≤ 1) :
    ∑ e, F.routedLoad a Q e ≤ (∑ e, F.allocation e a) +
      2 * ∑ ξ : G.GroupBit a, ((G.lastOutput a).val - (G.output ξ.val).val : ℕ) := by
  calc
    _ ≤ ∑ e, (F.allocation e a + 2 * G.copyCharge a e) :=
      sum_le_sum fun e _ => F.routedLoad_le a Q hl hb e
    _ = _ := by rw [sum_add_distrib, ← mul_sum, G.sum_copyCharge]

/-- A complete partial routing on one group fibre: actual endpoints,
positive weights, full support-log mass, unit bit caps, and the sharper
prefix capacity on every original physical edge. -/
theorem exists_group_routes [Nonempty C] :
    ∃ Q : List (ℝ × F.AttachedPath a),
      (∀ i : F.AllocatedIndex a Q, 0 < F.allocatedWeight a Q i) ∧
      F.allocatedMass a Q =
        Real.logb 2 (Fintype.card (Set.range (fun x : C => G.projection a x.val))) ∧
      (∀ ξ : Bit d b, 0 ≤ F.routedBitMass a Q ξ ∧ F.routedBitMass a Q ξ ≤ 1) ∧
      (∀ e, F.routedLoad a Q e ≤ F.allocation e a + 2 * G.copyCharge a e) := by
  obtain ⟨Q, hp, hm, hl, hb, _⟩ := F.exists_allocated_packing a
  exact ⟨Q, hp, hm, F.routedBitMass_bounds a Q hb,
    F.routedLoad_le a Q hl (fun ξ => (hb ξ).2)⟩

end FibreTyping
end
end SourceCovers.CausalGroups.Network
