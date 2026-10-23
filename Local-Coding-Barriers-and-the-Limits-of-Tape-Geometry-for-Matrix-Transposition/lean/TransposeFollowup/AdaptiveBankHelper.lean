import TransposeFollowup.AdaptiveForestLeaf
import TransposeFollowup.HelperPacketAveraging

/-! An arbitrary deterministic helper may choose the entire full-cube bank,
public protocol and row decoder. Only the chosen branch must be correct. -/

namespace TransposeFollowup

open Classical
open scoped BigOperators
set_option autoImplicit false

structure HelperGapBankCode (d b sigma : ℕ) (H : Type*) where
  helper : FiniteMatrix d b → H
  branch : H → GapBankCode d b sigma

namespace HelperGapBankCode

variable {d b sigma : ℕ} {H : Type*} (C : HelperGapBankCode d b sigma H)

def CorrectOn (F : Set (FiniteMatrix d b)) : Prop :=
  ∀ a, (C.branch a).CorrectOn (F ∩ {x | C.helper x = a})

def length (x : FiniteMatrix d b) : ℕ :=
  ((C.branch (C.helper x)).transcript x).length

theorem correctOn_fiber {Ω : Type*} (X : Ω → FiniteMatrix d b)
    (hc : C.CorrectOn (Set.range X)) (a : H) :
    (C.branch a).CorrectOn (Set.range (fun x : HelperFiber (fun z => C.helper (X z)) a => X x)) := by
  intro x hx j
  obtain ⟨z, rfl⟩ := hx
  exact hc a (X z) ⟨⟨z.val, rfl⟩, z.property⟩ j

end HelperGapBankCode

/-- Internal averaging for variable-length branch executions. The final
code theorem supplies the fiber premise from the actual selected protocol. -/
theorem helper_length_bound_of_fiber_bounds
    {Ω H V : Type*} [Fintype Ω] [Fintype H] [Fintype V]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (X : Ω → V) (h : Ω → H) (hh : h.FactorsThrough X)
    (cost : Ω → ℝ) (a P A Q c : ℝ)
    (hf : ∀ z, 0 < helperMass p h z →
      P - A - Q * (P - observationEntropy (helperConditionalWeight p h z)
        (fun x : HelperFiber h z => X x) / c) ≤
      a * ∑ x : HelperFiber h z, helperConditionalWeight p h z x * cost x) :
    P - A - Q * (P - observationEntropy p X / c + observationEntropy p h / c) ≤
      a * ∑ x, p x * cost x := by
  have hs : ∑ z, helperMass p h z = 1 := (sum_helperMass p h).trans hp1
  have hd := sum_helperMass_mul_observation_deficit p hp hp1 X h hh P c
  have hm := sum_helperMass_mul_mean p hp h cost
  have ha := Finset.sum_le_sum (s := Finset.univ) (fun z _ =>
    if hz : 0 < helperMass p h z then
      mul_le_mul_of_nonneg_left (hf z hz) (helperMass_nonneg p hp h z)
    else by
      have hzero : helperMass p h z = 0 := le_antisymm (le_of_not_gt hz) (helperMass_nonneg p hp h z)
      simp [hzero])
  have hl : (∑ z, helperMass p h z * (P - A - Q *
      (P - observationEntropy (helperConditionalWeight p h z)
        (fun x : HelperFiber h z => X x) / c))) =
      P - A - Q * (P - observationEntropy p X / c + observationEntropy p h / c) := by
    calc
      _ = (∑ z, helperMass p h z) * (P - A) - Q *
          (∑ z, helperMass p h z * (P - observationEntropy (helperConditionalWeight p h z)
            (fun x : HelperFiber h z => X x) / c)) := by
        simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum]
        congr 1
        congr 1 <;> apply Finset.sum_congr rfl <;> intro z _ <;> ring
      _ = _ := by rw [hs, one_mul, hd]
  have hr : (∑ z, helperMass p h z *
      (a * ∑ x : HelperFiber h z, helperConditionalWeight p h z x * cost x)) =
      a * ∑ x, p x * cost x := by
    calc
      _ = a * ∑ z, helperMass p h z *
          (∑ x : HelperFiber h z, helperConditionalWeight p h z x * cost x) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro z _
        ring
      _ = _ := by rw [hm]
  rwa [hl, hr] at ha

end TransposeFollowup
