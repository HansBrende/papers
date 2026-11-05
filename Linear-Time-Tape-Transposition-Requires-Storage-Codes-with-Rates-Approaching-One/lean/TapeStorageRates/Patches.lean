import TapeStorageRates.PatchResidual
import TransposeFollowup.UniformEntropy

/-!
# How many targets can overlapping patches recover?

The target sets may overlap, and recovery is needed only for the targets
served by a patch. This includes a fixed assignment of one patch per target
and a decoder using a specified subset of the permitted helpers.
-/

namespace TapeStorageRates

open Finset TransposeFollowup DirectedRecovery MotionDepthCodes SoftRecovery HalfRate
open scoped BigOperators

set_option autoImplicit false

/-- Finite patch coverage. If each patch scores at most `w` targets and
each coordinate has at most `r` memberships, the patches serve at most twice
`r` times the global deficit in alphabet symbols in targets farther than `2*w-1`.
The patches are indexed, so equal patches have separate memberships.
`A j` lists the targets recovered by the j-th patch on the actual code. -/
theorem recovery_patch_coverage {V J α : Type*} [Fintype V] [DecidableEq V] [Fintype J]
    [Fintype α] [Nontrivial α]
    (N : V → Finset V) (C : Finset (V → α)) (hC : C.Nonempty)
    (S : Finset V) (P A : J → Finset V) (w r : ℕ)
    (hsize : ∀ j, (A j).card ≤ w)
    (hload : ∀ v, (univ.filter fun j => v ∈ P j).card ≤ r)
    (hserves : ∀ q ∈ S, ∃ j, q ∈ A j) (hwithin : ∀ j, A j ⊆ P j)
    (hrec : ∀ j, ∀ q ∈ A j, ∀ x ∈ C, ∀ y ∈ C,
      (∀ u ∈ N q, u ∈ P j → x u = y u) → x q = y q) :
    ((S \ shortPairedCoordinates N (2*w-1)).card : ℝ) ≤
        2 * r * (Fintype.card V - Real.logb (Fintype.card α) C.card) ∧
    (S.card : ℝ) ≤ (shortPairedCoordinates N (2*w-1)).card +
        2 * r * (Fintype.card V - Real.logb (Fintype.card α) C.card) := by
  classical
  let Z := shortPairedCoordinates N (2*w-1)
  let T (j : J) := A j \ Z
  let : Nonempty C := hC.to_subtype
  let p := uniformWeight C
  let X (x : C) := x.val
  let a := Real.log (Fintype.card α)
  have ha : 0 < a := Real.log_pos (by exact_mod_cast Fintype.one_lt_card (α := α))
  let B (j : J) (q : V) := N q ∩ P j
  have hcap := codeEntropy_singleton_le p X (uniformWeight_nonneg C) (sum_uniformWeight C)
  have hs := patch_capacity_of_long_targets (codeEntropy_isPolymatroid p X (uniformWeight_nonneg C)
    (sum_uniformWeight C)) (fun _ => a) hcap N P T B w r
    (fun j => (card_le_card sdiff_subset).trans (hsize j)) hload
    (fun j => sdiff_subset.trans (hwithin j)) (fun _ _ _ => subset_rfl) (fun _ _ hq => (mem_sdiff.mp hq).2)
  have hcredits (j : J) : (∑ q ∈ T j, (a - increment (codeEntropy p X) (B j q) q)) =
      ((T j).card : ℝ) * a := by
    apply Eq.trans (sum_congr rfl fun q hq => ?_) (sum_const _ |>.trans (nsmul_eq_mul _ _))
    rw [entropy_increment_zero_of_recovery p X (uniformWeight_nonneg C) _ _
      (fun x y h => hrec j q (mem_sdiff.mp hq).1 _ x.2 _ y.2 fun u hu huP => h u (mem_inter.mpr ⟨hu,huP⟩)),
      sub_zero]
  have hobs : codeEntropy p X univ = Real.log C.card := by
    change codeEntropy (fun _ : C => (Fintype.card C : ℝ)⁻¹) (fun x : C => x.val) univ = _
    rw [Fintype.card_coe]
    exact codeEntropy_univ_uniform C hC
  simp only [hcredits, hobs, sum_const, card_univ, nsmul_eq_mul, ← sum_mul] at hs
  have hm := mul_le_mul_of_nonneg_left (sum_le_sum (s := univ) fun q _ => hcap q) (Nat.cast_nonneg r (α := ℝ))
  simp only [sum_const, card_univ, nsmul_eq_mul] at hm
  have hlong : (S \ Z).card ≤ ∑ j, (T j).card := by
    apply le_trans (b := (univ.biUnion T).card) _ card_biUnion_le
    apply card_le_card
    intro q hq
    obtain ⟨hqS, hqZ⟩ := mem_sdiff.mp hq
    obtain ⟨j, hj⟩ := hserves q hqS
    exact mem_biUnion.mpr ⟨j, mem_univ _, mem_sdiff.mpr ⟨hj, hqZ⟩⟩
  have hlongR : ((S \ Z).card : ℝ) ≤ ∑ j, ((T j).card : ℝ) := by exact_mod_cast hlong
  have bound : ((S \ Z).card : ℝ) ≤
      2 * r * (Fintype.card V - Real.logb (Fintype.card α) C.card) := by
    apply (mul_le_mul_iff_of_pos_right ha).mp
    calc
      _ ≤ (∑ j, ((T j).card : ℝ)) * a := mul_le_mul_of_nonneg_right hlongR ha.le
      _ ≤ 2*r*(Fintype.card V*a - Real.log C.card) := by
        dsimp only [a] at *
        linarith only [hs, hm]
      _ = _ := by change _ = 2*r*(Fintype.card V-Real.log C.card/a)*a; field_simp
  have hsplit := card_sdiff_add_card_inter S Z
  have hi := card_le_card (inter_subset_right (s₁ := S) (s₂ := Z))
  have hS : (S.card : ℝ) ≤ (S \ Z).card + (Z.card : ℝ) := by
    exact_mod_cast (by omega : S.card ≤ (S \ Z).card + Z.card)
  exact ⟨bound, by change (S.card : ℝ) ≤ (Z.card : ℝ) + _; linarith⟩

end TapeStorageRates
