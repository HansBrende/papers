import TransposeFollowup.DisjointFlipOrbit
import TransposeFollowup.ComponentDistance

/-! Exact finite broadcast lower bound after arbitrary nonlinear row recoding.
Large unanchored components consume many transformed coordinates; small ones
have a free orbit confined to the near raw coordinates. -/

namespace TransposeFollowup

open scoped BigOperators
open Classical
set_option autoImplicit false
universe u

theorem disjoint_family_size_bound {V : Type u} [Fintype V] [DecidableEq V]
    (U : Finset (Finset V)) (hne : ∀ S ∈ U, S.Nonempty)
    (hdis : (U : Set (Finset V)).PairwiseDisjoint id) (ell : ℕ) :
    (ell + 1) * U.card ≤ Fintype.card V + ell * (U.filter (fun S => S.card ≤ ell)).card := by
  have hpoint (S : Finset V) (hS : S ∈ U) :
      ell + 1 ≤ S.card + if S.card ≤ ell then ell else 0 := by
    have hp := Finset.card_pos.mpr (hne S hS)
    split_ifs <;> omega
  have hsum := Finset.sum_le_sum hpoint
  have hcards : ∑ S ∈ U, S.card ≤ Fintype.card V := by
    calc
      _ = (U.biUnion id).card := by simpa only [id_eq] using (Finset.card_biUnion hdis).symm
      _ ≤ _ := Finset.card_le_univ _
  have hsmall : (∑ S ∈ U, if S.card ≤ ell then ell else 0) =
      ell * (U.filter (fun S => S.card ≤ ell)).card := by
    rw [← Finset.sum_filter]
    simp [Nat.mul_comm]
  simp only [Finset.sum_const, smul_eq_mul, Finset.sum_add_distrib] at hsum
  rw [hsmall] at hsum
  nlinarith

namespace XorSystem

variable {V : Type u} [Fintype V] {B : ℕ} (C : XorSystem V B)

theorem components_disjoint : (C.components : Set (Finset V)).PairwiseDisjoint id :=
  graphComponents_pairwise_disjoint C.graph ∅

theorem unanchored_disjoint : (C.unanchored : Set (Finset V)).PairwiseDisjoint id := by
  intro S hS T hT hne
  exact C.components_disjoint (Finset.mem_filter.mp hS).1 (Finset.mem_filter.mp hT).1 hne

theorem unanchored_nonempty {S : Finset V} (hS : S ∈ C.unanchored) : S.Nonempty :=
  C.component_nonempty (Finset.mem_filter.mp hS).1

noncomputable def smallComponents (ell : ℕ) : Finset (Finset V) :=
  C.unanchored.filter (fun S => S.card ≤ ell)

theorem mem_smallComponents (ell : ℕ) (S : Finset V) :
    S ∈ C.smallComponents ell ↔ S ∈ C.unanchored ∧ S.card ≤ ell := by
  simp only [smallComponents, Finset.mem_filter]

theorem smallComponents_disjoint (ell : ℕ) :
    (C.smallComponents ell : Set (Finset V)).PairwiseDisjoint id := by
  intro S hS T hT hne
  exact C.unanchored_disjoint (Finset.mem_filter.mp hS).1 (Finset.mem_filter.mp hT).1 hne

theorem unanchored_size_bound (ell : ℕ) :
    (ell + 1) * C.unanchored.card ≤ Fintype.card V + ell * (C.smallComponents ell).card :=
  disjoint_family_size_bound C.unanchored (fun _ h => C.unanchored_nonempty h)
    C.unanchored_disjoint ell

end XorSystem

namespace RecodedXorCode

variable {n b B : ℕ} (C : RecodedXorCode n b B)

theorem small_component_count_le_near (hc : C.Correct) (G : SimpleGraph (Fin n))
    (hG : C.LocalTo G) (ell : ℕ) :
    (C.system.smallComponents ell).card ≤ (nearBits (b := b) G ell).card := by
  apply C.flip_orbit_bound (C.system.smallComponents ell)
    (fun S h => C.system.unanchored_nonempty ((C.system.mem_smallComponents ell S).mp h).1)
    (C.system.smallComponents_disjoint ell) (nearBits G ell)
  intro S hS x v hv
  obtain ⟨hu, hs⟩ := (C.system.mem_smallComponents ell S).mp hS
  exact C.small_flip_preserves_far hc G hG hu ell hs x v hv

/-- Integral form of B1. No division, positivity or connectedness assumptions
are needed; ell=0 also gives a valid (though vacuous) inequality. -/
theorem broadcast_lower_bound_scaled (hc : C.Correct) (G : SimpleGraph (Fin n))
    (hG : C.LocalTo G) (ell : ℕ) :
    (ell + 1) * (n * n * b) ≤ (ell + 1) * B + n * n * b +
      ell * (nearBits (b := b) G ell).card := by
  have hcoord := C.system.coordinate_count_le_broadcast_add_unanchored
  have hsize := C.system.unanchored_size_bound ell
  have hsmall := C.small_component_count_le_near hc G hG ell
  simp only [MatrixBit, Fintype.card_prod, Fintype.card_fin, ← Nat.mul_assoc] at hcoord hsize
  have hmul := Nat.mul_le_mul_left (ell + 1) hcoord
  have hmulSmall := Nat.mul_le_mul_left ell hsmall
  nlinarith

/-- B >= P-(P+ell Q_ell)/(ell+1), with Q_ell counted in raw bit coordinates.
The complete decoding and nonlinear recoding assumptions are explicit. -/
theorem broadcast_lower_bound (hc : C.Correct) (G : SimpleGraph (Fin n))
    (hG : C.LocalTo G) (ell : ℕ) :
    (B : ℝ) ≥ (n * n * b : ℕ) -
      (((n * n * b : ℕ) : ℝ) + ell * (nearBits (b := b) G ell).card) / (ell + 1) := by
  have hs : ((ell : ℝ) + 1) * (n * n * b : ℕ) ≤
      ((ell : ℝ) + 1) * B + (n * n * b : ℕ) + ell * (nearBits (b := b) G ell).card := by
    exact_mod_cast C.broadcast_lower_bound_scaled hc G hG ell
  have hd : 0 < (ell : ℝ) + 1 := by positivity
  have hdiv : ((n * n * b : ℕ) : ℝ) - B ≤
      (((n * n * b : ℕ) : ℝ) + ell * (nearBits (b := b) G ell).card) / (ell + 1) := by
    apply (le_div_iff₀ hd).mpr
    nlinarith
  linarith

end RecodedXorCode
end TransposeFollowup
