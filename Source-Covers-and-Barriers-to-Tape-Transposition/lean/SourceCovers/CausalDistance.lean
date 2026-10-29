import SourceCovers.CausalEntropy
import LeanMachine.FlowDistance

/-! The metric bound for the actual partial routing. Distances are ordinary
undirected graph distances from the nearest original row attachment.
Unattached rows have infinite distance and never contribute short bits. -/

namespace SourceCovers.CausalGroups.Network

open LeanMachine Finset
open scoped BigOperators Classical
noncomputable section

universe u v
variable {d b h n : ℕ} {Edge : Type u} [Fintype Edge] (G : Network d b h n Edge)

def rowDistance (ξ : Bit d b) : ℕ∞ :=
  ⨅ s : G.attached ξ.1, G.physicalFlow.graph.edist s.val (G.output ξ)

theorem rowDistance_lt_iff (ξ : Bit d b) (ℓ : ℕ) :
    G.rowDistance ξ < ℓ ↔ ∃ s ∈ G.attached ξ.1,
      G.physicalFlow.graph.edist s (G.output ξ) < ℓ := by
  simp only [rowDistance, iInf_lt_iff, Subtype.exists, exists_prop]

theorem rowDistance_unattached (ξ : Bit d b) (hξ : G.attached ξ.1 = ∅) :
    G.rowDistance ξ = ⊤ := by simp [rowDistance, hξ]

/-- The finite infimum is the nearest-attachment distance, with infinity
for an absent attachment. -/
def shortBits (ℓ : ℕ) : Finset (Bit d b) := univ.filter fun ξ => G.rowDistance ξ < ℓ

theorem mem_shortBits_iff (ξ : Bit d b) (ℓ : ℕ) : ξ ∈ G.shortBits ℓ ↔
    ∃ s ∈ G.attached ξ.1, G.physicalFlow.graph.edist s (G.output ξ) < ℓ := by
  simp only [shortBits, mem_filter, mem_univ, true_and, G.rowDistance_lt_iff]

theorem unattached_not_shortBits (ξ : Bit d b) (hξ : G.attached ξ.1 = ∅) (ℓ : ℕ) :
    ξ ∉ G.shortBits ℓ := by simp [shortBits, G.rowDistance_unattached ξ hξ]

theorem rowDistance_le_route (q : G.BitRoute) :
    G.rowDistance q.bit ≤ (G.physicalFlow.bidirected.pathLength q.path : ℕ∞) :=
  (iInf_le _ ⟨q.attachment, q.attached⟩).trans
    (G.physicalFlow.edist_le_walk_length q.path)

theorem le_length_of_not_short (q : G.BitRoute) (ℓ : ℕ) (hq : q.bit ∉ G.shortBits ℓ) :
    ℓ ≤ G.physicalFlow.bidirected.pathLength q.path := by
  have hn : ¬G.rowDistance q.bit < ℓ := by simpa [shortBits] using hq
  exact_mod_cast (not_lt.mp hn).trans (G.rowDistance_le_route q)

def routingVolume (R : FiniteWeightedFamily.{u, v} G.BitRoute) : ℝ :=
  ∑ e, G.routingLoad R e

theorem routingVolume_eq (R : FiniteWeightedFamily.{u, v} G.BitRoute) :
    G.routingVolume R = R.sum (fun q => (G.physicalFlow.bidirected.pathLength q.path : ℝ)) := by
  unfold routingVolume routingLoad FiniteWeightedFamily.sum
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  rw [← mul_sum, G.physicalFlow.sum_walkLoad]

theorem sum_routingBitMass (R : FiniteWeightedFamily.{u, v} G.BitRoute) (S : Finset (Bit d b)) :
    ∑ ξ ∈ S, G.routingBitMass R ξ = R.sum (fun q => if q.bit ∈ S then 1 else 0) := by
  unfold routingBitMass FiniteWeightedFamily.sum
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  rw [← mul_sum]
  simp

theorem routingMassOn_le_card {R : FiniteWeightedFamily.{u, v} G.BitRoute}
    (hR : G.IsPartialRouting R) (S : Finset (Bit d b)) :
    R.sum (fun q => if q.bit ∈ S then 1 else 0) ≤ S.card := by
  rw [← G.sum_routingBitMass]
  exact (sum_le_sum fun ξ _ => hR.bit_cap ξ).trans_eq (by simp)

/-- Zero radius is allowed in this undivided form. Every original physical
traversal, including a repeated or backward traversal, is paid. -/
theorem routing_distance_volume {R : FiniteWeightedFamily.{u, v} G.BitRoute}
    (hR : G.IsPartialRouting R) (ℓ : ℕ) :
    (ℓ : ℝ) * (R.mass - (G.shortBits ℓ).card) ≤ G.routingVolume R := by
  let S := G.shortBits ℓ
  have hp (q : G.BitRoute) : (ℓ : ℝ) * (1 - if q.bit ∈ S then 1 else 0) ≤
      (G.physicalFlow.bidirected.pathLength q.path : ℝ) := by
    by_cases hq : q.bit ∈ S
    · simp [hq]
    · simp only [hq, ↓reduceIte, sub_zero, mul_one]
      exact_mod_cast G.le_length_of_not_short q ℓ hq
  calc
    _ ≤ (ℓ : ℝ) * (R.mass - R.sum (fun q => if q.bit ∈ S then 1 else 0)) :=
      mul_le_mul_of_nonneg_left (sub_le_sub_left (G.routingMassOn_le_card hR S) _)
        (Nat.cast_nonneg _)
    _ = R.sum (fun q => (ℓ : ℝ) * (1 - if q.bit ∈ S then 1 else 0)) := by
      simp only [FiniteWeightedFamily.mass_eq, FiniteWeightedFamily.sum,
        mul_sub, mul_one, sum_sub_distrib, mul_sum]
      congr 1 <;> apply sum_congr rfl <;> intro i _ <;> ring
    _ ≤ R.sum (fun q => (G.physicalFlow.bidirected.pathLength q.path : ℝ)) :=
      sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hp _) (hR.nonnegative i)
    _ = _ := (G.routingVolume_eq R).symm

theorem routingMass_le_short_add_volume {R : FiniteWeightedFamily.{u, v} G.BitRoute}
    (hR : G.IsPartialRouting R) (ℓ : ℕ) (hℓ : 0 < ℓ) :
    R.mass ≤ (G.shortBits ℓ).card + G.routingVolume R / ℓ := by
  have hp : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have he : R.mass - (G.shortBits ℓ).card ≤ G.routingVolume R / ℓ :=
    (le_div_iff₀ hp).mpr (by simpa [mul_comm] using G.routing_distance_volume hR ℓ)
  linarith

/-- Any common physical capacity budget may be used. -/
theorem routingMass_le_short_add_capacity {R : FiniteWeightedFamily.{u, v} G.BitRoute}
    (hR : G.IsPartialRouting R) (K : Edge → ℝ) (hK : ∀ e, G.routingLoad R e ≤ K e)
    (ℓ : ℕ) (hℓ : 0 < ℓ) :
    R.mass ≤ (G.shortBits ℓ).card + (∑ e, K e) / ℓ := by
  exact (G.routingMass_le_short_add_volume hR ℓ hℓ).trans
    (add_le_add le_rfl (div_le_div_of_nonneg_right (sum_le_sum fun e _ => hK e)
      (Nat.cast_nonneg _)))

end
end SourceCovers.CausalGroups.Network
