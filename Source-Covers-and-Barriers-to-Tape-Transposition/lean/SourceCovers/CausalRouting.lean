import SourceCovers.CausalGroupRoutes
import LeanMachine.FiniteWeightedFamily

/-! Combining actual group routes. One common weighted-family interface
retains paths and multiplicity while adding bit masses and edge loads. -/

namespace SourceCovers.CausalGroups.Network

open LeanMachine Finset
open scoped BigOperators Classical
noncomputable section

universe u v w
variable {d b h n : ℕ} {Edge : Type u} [Fintype Edge] (G : Network d b h n Edge)

def routingLoad (R : FiniteWeightedFamily.{u, v} G.BitRoute) (e : Edge) : ℝ :=
  R.sum fun q => G.physicalFlow.walkLoad q.path e

def routingBitMass (R : FiniteWeightedFamily.{u, v} G.BitRoute) (ξ : Bit d b) : ℝ :=
  R.sum fun q => if q.bit = ξ then 1 else 0

/-- Endpoints and actual attachments are already fields of every `BitRoute`.
Here only nonnegative weights and the common unit cap need to be imposed. -/
structure IsPartialRouting (R : FiniteWeightedFamily.{u, v} G.BitRoute) : Prop where
  nonnegative : R.Nonnegative
  bit_cap : ∀ ξ, G.routingBitMass R ξ ≤ 1

theorem routingBitMass_nonneg {R : FiniteWeightedFamily.{u, v} G.BitRoute}
    (hR : G.IsPartialRouting R) (ξ : Bit d b) : 0 ≤ G.routingBitMass R ξ := by
  apply R.sum_nonneg hR.nonnegative
  intro q
  split_ifs <;> norm_num

theorem routingBitMass_unattached (R : FiniteWeightedFamily.{u, v} G.BitRoute)
    (ξ : Bit d b) (hξ : G.attached ξ.1 = ∅) : G.routingBitMass R ξ = 0 := by
  apply sum_eq_zero
  intro i _
  have hn : (R.value i).bit ≠ ξ := by
    intro hi
    have ha := (R.value i).attached
    rw [hi, hξ] at ha
    exact ha
  simp [hn]

theorem mix_isPartialRouting {J : Type w} [Fintype J] (p : J → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hp1 : ∑ j, p j = 1)
    (R : J → FiniteWeightedFamily.{u, v} G.BitRoute)
    (hR : ∀ j, G.IsPartialRouting (R j)) :
    G.IsPartialRouting (FiniteWeightedFamily.mix p R) := by
  refine ⟨FiniteWeightedFamily.mix_nonnegative p hp R (fun j => (hR j).nonnegative), ?_⟩
  intro ξ
  exact FiniteWeightedFamily.sum_mix_le p hp hp1 R _ 1 (fun j => (hR j).bit_cap ξ)

def groupSupportLog (C : Set (Input d b)) (a : Fin h) : ℝ :=
  Real.logb 2 (Fintype.card (Set.range (fun x : C => G.projection a x.val)))

def supportSum (C : Set (Input d b)) : ℝ := ∑ a, G.groupSupportLog C a

variable [∀ a : Fin h, Nonempty (G.GroupBit a)]

/-- All groups share one original capacity; only the paid geometric prefix
charges are added. This bound is independent of the helper fibre. -/
def augmentedCapacity (e : Edge) : ℝ := G.capacity e + 2 * ∑ a, G.copyCharge a e

theorem augmentedCapacity_nonneg (e : Edge) : 0 ≤ G.augmentedCapacity e := by
  exact add_nonneg (G.capacity_nonneg e)
    (mul_nonneg (by norm_num) (sum_nonneg fun a _ => G.copyCharge_nonneg a e))

theorem sum_augmentedCapacity :
    ∑ e, G.augmentedCapacity e = (∑ e, G.capacity e) +
      2 * ∑ a, ∑ ξ : G.GroupBit a,
        ((G.lastOutput a).val - (G.output ξ.val).val : ℕ) := by
  simp only [augmentedCapacity, sum_add_distrib, ← mul_sum]
  rw [sum_comm]
  simp only [G.sum_copyCharge, Nat.cast_sum]

/-- The paper's original whole-group charge, on the actual memory edges
of each collector interval. -/
def intervalCapacity (e : Edge) : ℝ := G.capacity e +
  2 * ∑ a, if e ∈ Set.range (fun v : (G.collector a).Link => G.collectorPhysical a (.inr v))
    then (Fintype.card (G.GroupBit a) : ℝ) else 0

theorem augmentedCapacity_le_interval (e : Edge) :
    G.augmentedCapacity e ≤ G.intervalCapacity e := by
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply sum_le_sum
  intro a _
  split_ifs with he
  · exact G.copyCharge_le a e
  · exact (G.copyCharge_outside a e he).le

def intervalVolume : ℝ := (∑ e, G.capacity e) +
  2 * ∑ a, (Fintype.card (G.GroupBit a) : ℝ) *
    ((G.lastOutput a).val - (G.firstOutput a).val : ℕ)

theorem sum_augmentedCapacity_le_intervalVolume :
    ∑ e, G.augmentedCapacity e ≤ G.intervalVolume := by
  rw [G.sum_augmentedCapacity]
  simp only [Nat.cast_sum]
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply sum_le_sum
  intro a _
  have hb := (G.collector a).sum_prefix_card_le
  rw [(G.collector a).sum_prefix_card] at hb
  exact_mod_cast hb

namespace FibreTyping

variable {G} {C : Set (Input d b)} (F : G.FibreTyping C)

def groupRouteFamily (a : Fin h) (Q : List (ℝ × F.AttachedPath a)) :
    FiniteWeightedFamily.{u, 0} G.BitRoute where
  Index := F.AllocatedIndex a Q
  finiteIndex := inferInstance
  value := F.allocatedRoute a Q
  weight := F.allocatedWeight a Q

theorem groupRouteFamily_mass (a : Fin h) (Q : List (ℝ × F.AttachedPath a)) :
    (F.groupRouteFamily a Q).mass = F.allocatedMass a Q := by
  rw [FiniteWeightedFamily.mass_eq]
  rfl

theorem groupRouteFamily_load (a : Fin h) (Q : List (ℝ × F.AttachedPath a)) (e : Edge) :
    G.routingLoad (F.groupRouteFamily a Q) e = F.routedLoad a Q e := rfl

theorem groupRouteFamily_bitMass (a : Fin h) (Q : List (ℝ × F.AttachedPath a)) (ξ : Bit d b) :
    G.routingBitMass (F.groupRouteFamily a Q) ξ = F.routedBitMass a Q ξ := by
  change (∑ i : F.AllocatedIndex a Q,
    F.allocatedWeight a Q i * (if (F.allocatedRoute a Q i).bit = ξ then 1 else 0)) = _
  simp only [mul_ite, mul_one, mul_zero, routedBitMass]

theorem exists_group_family [Nonempty C] (a : Fin h) :
    ∃ R : FiniteWeightedFamily.{u, 0} G.BitRoute,
      G.IsPartialRouting R ∧ R.mass = G.groupSupportLog C a ∧
      (∀ ξ : Bit d b, G.partition.group ξ.2.1 ≠ a → G.routingBitMass R ξ = 0) ∧
      (∀ e, G.routingLoad R e ≤ F.allocation e a + 2 * G.copyCharge a e) := by
  obtain ⟨Q, hp, hm, hb, hl⟩ := F.exists_group_routes a
  refine ⟨F.groupRouteFamily a Q, ⟨fun i => (hp i).le, ?_⟩, ?_, ?_, ?_⟩
  · intro ξ
    rw [F.groupRouteFamily_bitMass]
    exact (hb ξ).2
  · rw [F.groupRouteFamily_mass]
    exact hm
  · intro ξ hξ
    rw [F.groupRouteFamily_bitMass]
    exact F.routedBitMass_outside a Q ξ hξ
  · intro e
    rw [F.groupRouteFamily_load]
    exact hl e

include F in
/-- The groups' bit sets are disjoint, so unit caps survive their union.
Their original field allocations add only up to the original edge budget. -/
theorem exists_fibre_routing [Nonempty C] :
    ∃ R : FiniteWeightedFamily.{u, 0} G.BitRoute,
      G.IsPartialRouting R ∧ R.mass = G.supportSum C ∧
      ∀ e, G.routingLoad R e ≤ G.augmentedCapacity e := by
  choose R hR hm ho hl using fun a => F.exists_group_family a
  refine ⟨FiniteWeightedFamily.collect R,
    ⟨FiniteWeightedFamily.collect_nonnegative R (fun a => (hR a).nonnegative), ?_⟩, ?_, ?_⟩
  · intro ξ
    change (FiniteWeightedFamily.collect R).sum _ ≤ 1
    rw [FiniteWeightedFamily.sum_collect]
    change (∑ a, G.routingBitMass (R a) ξ) ≤ 1
    rw [sum_eq_single (G.partition.group ξ.2.1)]
    · exact (hR _).bit_cap ξ
    · intro a _ ha
      exact ho a ξ (Ne.symm ha)
    · simp
  · change (FiniteWeightedFamily.collect R).sum (fun _ => 1) = _
    rw [FiniteWeightedFamily.sum_collect]
    change (∑ a, (R a).mass) = _
    simp only [hm, supportSum]
  · intro e
    change (FiniteWeightedFamily.collect R).sum _ ≤ _
    rw [FiniteWeightedFamily.sum_collect]
    calc
      _ ≤ ∑ a, (F.allocation e a + 2 * G.copyCharge a e) := sum_le_sum fun a _ => hl a e
      _ = (∑ a, F.allocation e a) + 2 * ∑ a, G.copyCharge a e := by
        rw [sum_add_distrib, ← mul_sum]
      _ ≤ G.augmentedCapacity e := add_le_add (F.capacity_bound e) le_rfl

end FibreTyping
end
end SourceCovers.CausalGroups.Network
