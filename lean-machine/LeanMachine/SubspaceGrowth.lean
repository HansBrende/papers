import LeanMachine.SubspaceFamilies

/-! Exact dimension accounting when a tight space acquires a new coordinate
line. These lemmas use subspace ranks, not a distributive-lattice assumption. -/

namespace LeanMachine.SubspaceDefect

open Module Finset
open scoped BigOperators Classical

variable {ι K W : Type*} [Fintype ι] [Field K]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]

theorem line_extension_dimension (S L : Submodule K W)
    (hL : finrank K L = 1) (hnot : ¬ L ≤ S) :
    finrank K (S ⊔ L : Submodule K W) = finrank K S + 1 := by
  have hd := (line_le_or_disjoint L S hL).resolve_left hnot
  have hm := Submodule.finrank_sup_add_finrank_inf_eq S L
  rw [hd.symm.eq_bot, finrank_bot, hL] at hm
  omega

theorem line_coordinate_gain (U S L : Submodule K W) (hU : L ≤ U) (hnot : ¬ L ≤ S) :
    finrank K (U ⊓ S : Submodule K W) < finrank K (U ⊓ (S ⊔ L) : Submodule K W) := by
  apply Submodule.finrank_lt_finrank_of_lt
  refine lt_of_le_of_ne (inf_le_inf_left _ le_sup_left) ?_
  intro he
  apply hnot
  have hle : L ≤ U ⊓ (S ⊔ L) := le_inf hU le_sup_right
  rw [← he] at hle
  exact hle.trans inf_le_right

/-- A tight space growing by at most one dimension cannot acquire a disjoint
plane coordinate and also gain a dimension at a different coordinate. -/
theorem plane_gain_forces_intersection (U : ι → Submodule K W)
    (hpos : ∀ S : Submodule K W, S ≠ ⊥ → 1 ≤ defect U S)
    {S T : Submodule K W} (htight : defect U S = 1) (hle : S ≤ T)
    (hdim : finrank K T ≤ finrank K S + 1) {v u : ι} (hvu : v ≠ u)
    (hv : finrank K (U v) = 2) (hvT : U v ≤ T)
    (hu : finrank K (U u ⊓ S : Submodule K W) < finrank K (U u ⊓ T : Submodule K W)) :
    U v ⊓ S ≠ ⊥ := by
  intro hzero
  have hpoint : ∀ w, finrank K (U w ⊓ S : Submodule K W) +
      (if w = v then 2 else 0) + (if w = u then 1 else 0) ≤
        finrank K (U w ⊓ T : Submodule K W) := by
    intro w
    by_cases hwv : w = v
    · subst w
      rw [hzero, finrank_bot, inf_eq_left.mpr hvT, hv]
      simp [hvu]
    by_cases hwu : w = u
    · subst w
      simpa [hwv] using Nat.succ_le_of_lt hu
    · simp only [ite_eq_right hwv, ite_eq_right hwu, add_zero]
      exact Submodule.finrank_mono (inf_le_inf_left _ hle)
  have hsum := sum_le_sum (s := (univ : Finset ι)) (fun w _ => hpoint w)
  simp only [sum_add_distrib, sum_ite_eq', mem_univ, ite_true] at hsum
  have hT0 : T ≠ ⊥ := by
    intro h
    have hz : U v = ⊥ := le_bot_iff.mp (hvT.trans_eq h)
    rw [hz, finrank_bot] at hv
    omega
  have hpositive := hpos T hT0
  unfold defect at htight hpositive
  rw [← Nat.cast_sum] at htight hpositive
  omega

end LeanMachine.SubspaceDefect
