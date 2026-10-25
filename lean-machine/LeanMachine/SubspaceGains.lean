import LeanMachine.SubspaceGrowth

/-! Charging simultaneous coordinate-rank gains in a tight subspace extension. -/

namespace LeanMachine.SubspaceDefect

open Module Finset
open scoped BigOperators Classical

variable {ι K W : Type*} [Fintype ι] [Field K]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]

theorem coordinate_gain_count (U : ι → Submodule K W)
    {S T : Submodule K W} (hle : S ≤ T) (F : Finset ι)
    (hgain : ∀ v ∈ F, finrank K (U v ⊓ S : Submodule K W) <
      finrank K (U v ⊓ T : Submodule K W)) :
    (∑ v, finrank K (U v ⊓ S : Submodule K W)) + F.card ≤
      ∑ v, finrank K (U v ⊓ T : Submodule K W) := by
  let d : ι → ℕ := fun v => finrank K (U v ⊓ T : Submodule K W) -
    finrank K (U v ⊓ S : Submodule K W)
  have hm (v : ι) := Submodule.finrank_mono (inf_le_inf_left (U v) hle)
  have he : (∑ v, d v) + ∑ v, finrank K (U v ⊓ S : Submodule K W) =
      ∑ v, finrank K (U v ⊓ T : Submodule K W) := by
    rw [← sum_add_distrib]
    exact sum_congr rfl (fun v _ => Nat.sub_add_cancel (hm v))
  have hcount : F.card ≤ ∑ v, d v := by
    calc
      _ = ∑ _v ∈ F, 1 := by simp
      _ ≤ ∑ v ∈ F, d v := sum_le_sum (fun v hv => by
        have h := hgain v hv
        dsimp [d]
        omega)
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)
  omega

theorem tight_growth_gain_budget (U : ι → Submodule K W)
    (hpos : ∀ S : Submodule K W, S ≠ ⊥ → 1 ≤ defect U S)
    {S T : Submodule K W} (htight : defect U S = 1) (hle : S ≤ T) (F : Finset ι)
    (hgain : ∀ v ∈ F, finrank K (U v ⊓ S : Submodule K W) <
      finrank K (U v ⊓ T : Submodule K W)) :
    F.card + 2 * finrank K S ≤ 2 * finrank K T := by
  have hT0 : T ≠ ⊥ := by
    intro hz
    have hS0 : S = ⊥ := le_bot_iff.mp (hle.trans_eq hz)
    rw [hS0, defect_bot] at htight
    omega
  have hpositive := hpos T hT0
  have hg := coordinate_gain_count U hle F hgain
  unfold defect at htight hpositive
  rw [← Nat.cast_sum] at htight hpositive
  omega

end LeanMachine.SubspaceDefect
