import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace BitWord.Geometry
open scoped BigOperators
open Classical

/-- Maximum volume granted to a block with `k`-bit entries. -/
def volume (k : ℕ) := k * 4^k

def BadAt (B k : ℕ) : Prop := k < B ∧ B < volume k

theorem volume_strictMono : StrictMono volume := by
  apply strictMono_nat_of_lt_succ
  intro k
  have hp : 0 < 4^k := Nat.pow_pos (by decide)
  simp only [volume, Nat.pow_succ]
  nlinarith

/-- A width can be bad at only one of the widely separated scales. -/
theorem badAt_unique {m k : ℕ} (B : Fin m → ℕ)
    (hsep : ∀ i j, i < j → volume (B i) ≤ B j)
    {i j : Fin m} (hi : BadAt (B i) k) (hj : BadAt (B j) k) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · have := (volume_strictMono hi.1).trans_le (hsep i j h)
    exact False.elim (by have := hj.2; omega)
  · exact h
  · have := (volume_strictMono hj.1).trans_le (hsep j i h)
    exact False.elim (by have := hi.2; omega)

noncomputable def badBlocks {ι α : Type*} [DecidableEq α]
    (I : Finset ι) (block : ι → Finset α) (width : ι → ℕ) (B : ℕ) : Finset α :=
  (I.filter (fun a => BadAt B (width a))).biUnion block

/-- Each intermediate block occurrence is charged at most once over all scales. -/
theorem total_bad_volume_le {ι α : Type*} [DecidableEq α] {m : ℕ}
    (I : Finset ι) (block : ι → Finset α) (width : ι → ℕ)
    (B : Fin m → ℕ) (hsep : ∀ i j, i < j → volume (B i) ≤ B j)
    (ambient : Finset α) (hsub : ∀ a ∈ I, block a ⊆ ambient)
    (hdis : (I : Set ι).PairwiseDisjoint block) :
    ∑ i, (badBlocks I block width (B i)).card ≤ ambient.card := by
  have hrow (i : Fin m) : (badBlocks I block width (B i)).card ≤
      ∑ a ∈ I, if BadAt (B i) (width a) then (block a).card else 0 := by
    calc
      _ ≤ ∑ a ∈ I.filter (fun a => BadAt (B i) (width a)), (block a).card :=
        Finset.card_biUnion_le
      _ = _ := Finset.sum_filter _ _
  have hcol (a : ι) :
      (∑ i : Fin m, if BadAt (B i) (width a) then (block a).card else 0) ≤ (block a).card := by
    by_cases he : ∃ i : Fin m, BadAt (B i) (width a)
    · obtain ⟨i, hi⟩ := he
      have heq : ∀ j : Fin m, BadAt (B j) (width a) ↔ j = i := by
        intro j
        exact ⟨fun hj => badAt_unique B hsep hj hi, fun h => h ▸ hi⟩
      simp_rw [heq]
      simp
    · have hn : ∀ i : Fin m, ¬ BadAt (B i) (width a) := by simpa using he
      simp [hn]
  calc
    _ ≤ ∑ i : Fin m, ∑ a ∈ I, if BadAt (B i) (width a) then (block a).card else 0 :=
      Finset.sum_le_sum (fun i _ => hrow i)
    _ = ∑ a ∈ I, ∑ i : Fin m, if BadAt (B i) (width a) then (block a).card else 0 :=
      Finset.sum_comm
    _ ≤ ∑ a ∈ I, (block a).card := Finset.sum_le_sum (fun a _ => hcol a)
    _ = (I.biUnion block).card := (Finset.card_biUnion hdis).symm
    _ ≤ ambient.card := Finset.card_le_card (Finset.biUnion_subset.mpr hsub)

end BitWord.Geometry
