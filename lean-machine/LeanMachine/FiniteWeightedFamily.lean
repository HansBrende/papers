import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.BigOperators

/-! Finite weighted families, retaining multiplicity. The same linear sum
handles mass, labelled demand and physical edge loads under mixtures. -/

namespace LeanMachine

universe u v w

structure FiniteWeightedFamily (α : Type u) where
  Index : Type v
  finiteIndex : Fintype Index
  value : Index → α
  weight : Index → ℝ

attribute [instance] FiniteWeightedFamily.finiteIndex

namespace FiniteWeightedFamily

open Finset
open scoped BigOperators
noncomputable section

variable {α : Type u} (R : FiniteWeightedFamily.{u, v} α)

def sum (f : α → ℝ) : ℝ := ∑ i : R.Index, R.weight i * f (R.value i)

def mass : ℝ := R.sum (fun _ => 1)

def Nonnegative : Prop := ∀ i, 0 ≤ R.weight i

theorem sum_nonneg (hR : R.Nonnegative) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) :
    0 ≤ R.sum f := Finset.sum_nonneg fun i _ => mul_nonneg (hR i) (hf _)

theorem mass_eq : R.mass = ∑ i : R.Index, R.weight i := by
  simp [mass, sum]

/-- Take the disjoint union of the indices; repeated values are retained. -/
def collect {J : Type w} [Fintype J] (R : J → FiniteWeightedFamily.{u, v} α) :
    FiniteWeightedFamily.{u, max w v} α where
  Index := (j : J) × (R j).Index
  finiteIndex := inferInstance
  value := fun i => (R i.1).value i.2
  weight := fun i => (R i.1).weight i.2

theorem sum_collect {J : Type w} [Fintype J] (R : J → FiniteWeightedFamily.{u, v} α)
    (f : α → ℝ) : (collect R).sum f = ∑ j, (R j).sum f := by
  exact Fintype.sum_sigma _

theorem collect_nonnegative {J : Type w} [Fintype J]
    (R : J → FiniteWeightedFamily.{u, v} α) (hR : ∀ j, (R j).Nonnegative) :
    (collect R).Nonnegative := fun i => hR i.1 i.2

def scale (c : ℝ) : FiniteWeightedFamily.{u, v} α where
  Index := R.Index
  finiteIndex := R.finiteIndex
  value := R.value
  weight := fun i => c * R.weight i

theorem sum_scale (c : ℝ) (f : α → ℝ) : (R.scale c).sum f = c * R.sum f := by
  change (∑ i : R.Index, (c * R.weight i) * f (R.value i)) =
    c * ∑ i : R.Index, R.weight i * f (R.value i)
  simp only [mul_assoc, Finset.mul_sum]

theorem scale_nonnegative (hR : R.Nonnegative) {c : ℝ} (hc : 0 ≤ c) :
    (R.scale c).Nonnegative := fun i => mul_nonneg hc (hR i)

def mix {J : Type w} [Fintype J] (p : J → ℝ)
    (R : J → FiniteWeightedFamily.{u, v} α) : FiniteWeightedFamily.{u, max w v} α :=
  collect fun j => (R j).scale (p j)

theorem sum_mix {J : Type w} [Fintype J] (p : J → ℝ)
    (R : J → FiniteWeightedFamily.{u, v} α) (f : α → ℝ) :
    (mix p R).sum f = ∑ j, p j * (R j).sum f := by
  simp only [mix, sum_collect, sum_scale]

theorem mix_nonnegative {J : Type w} [Fintype J] (p : J → ℝ) (hp : ∀ j, 0 ≤ p j)
    (R : J → FiniteWeightedFamily.{u, v} α) (hR : ∀ j, (R j).Nonnegative) :
    (mix p R).Nonnegative := collect_nonnegative _ fun j => (R j).scale_nonnegative (hR j) (hp j)

/-- Any common linear bound survives a probability mixture. No sign
condition on the observable or on the common bound is required. -/
theorem sum_mix_le {J : Type w} [Fintype J] (p : J → ℝ) (hp : ∀ j, 0 ≤ p j)
    (hp1 : ∑ j, p j = 1) (R : J → FiniteWeightedFamily.{u, v} α)
    (f : α → ℝ) (B : ℝ) (hB : ∀ j, (R j).sum f ≤ B) :
    (mix p R).sum f ≤ B := by
  rw [sum_mix]
  calc
    _ ≤ ∑ j, p j * B := Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hB j) (hp j)
    _ = B := by rw [← Finset.sum_mul, hp1, one_mul]

end
end FiniteWeightedFamily
end LeanMachine
