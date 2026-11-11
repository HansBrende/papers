import LeanMachine.FiniteBoundedDifferences
import Mathlib.Logic.Equiv.Set

/-! # Actual coordinate windows under the uniform mask law

Coordinate restriction preserves the exact uniform law. A sum of bounded
local window functions has the coordinate-change bound given by the number
of window positions, whether or not those positions are distinct.
-/

namespace LeanMachine.FiniteProbability

open scoped BigOperators

variable {I J κ : Type*} [Fintype I] [Fintype J] [Fintype κ]
  [DecidableEq I] [DecidableEq J] [Nonempty κ]

theorem avg_restrict (e : J ↪ I) (f : (J → κ) → ℝ) :
    avg (fun p : I → κ => f (fun j => p (e j))) = avg f := by
  classical
  let q : J ≃ Set.range e := Equiv.ofInjective e e.injective
  let E : (I → κ) ≃ ((J → κ) × ({i // i ∉ Set.range e} → κ)) :=
    (Equiv.piEquivPiSubtypeProd (fun i => i ∈ Set.range e) (fun _ => κ)).trans
      (Equiv.prodCongr (Equiv.arrowCongr q.symm (Equiv.refl κ)) (Equiv.refl _))
  have he := avg_equiv E (fun z => f z.1)
  change avg (fun p : I → κ => f (fun j => p (e j))) = _ at he
  rw [avg_product] at he
  simpa only [avg_const] using he

theorem prob_restrict (e : J ↪ I) (P : (J → κ) → Prop) :
    prob (fun p : I → κ => P (fun j => p (e j))) = prob P := by
  classical
  exact avg_restrict e (fun x => if P x then 1 else 0)

theorem prob_eq_value {α : Type*} [Fintype α] (a : α) :
    prob (fun x => x=a) = 1/(Fintype.card α : ℝ) := by
  classical
  simp [prob,avg_eq_sum_div_card]

theorem prob_pattern (e : J ↪ I) (a : J → κ) :
    prob (fun p : I → κ => ∀ j, p (e j)=a j) =
      1/(Fintype.card κ : ℝ)^(Fintype.card J) := by
  classical
  have he : (fun p : I → κ => ∀ j, p (e j)=a j) =
      (fun p : I → κ => (fun j => p (e j))=a) := by
    funext p
    exact propext funext_iff.symm
  rw [he,prob_restrict e (fun x => x=a),prob_eq_value]
  simp

theorem prob_or_of_disjoint {α : Type*} [Fintype α] (P Q : α → Prop)
    (hd : ∀ x, ¬(P x ∧ Q x)) : prob (fun x => P x ∨ Q x) = prob P+prob Q := by
  classical
  rw [prob,prob,prob,← avg_add]
  congr 1
  funext x
  by_cases hp : P x <;> by_cases hq : Q x <;> simp_all

section Windows

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
  {k : ℕ}

noncomputable def windowSum (offset : Fin k → G) (f : (Fin k → κ) → ℝ)
    (p : G → κ) : ℝ := ∑ x : G, f (fun j => p (x+offset j))

theorem windowSum_mean (offset : Fin k → G) (ho : Function.Injective offset)
    (f : (Fin k → κ) → ℝ) :
    avg (windowSum offset f) = (Fintype.card G : ℝ)*avg f := by
  change avg (fun p : G → κ => ∑ x, f (fun j => p (x+offset j))) = _
  rw [avg_sum]
  have he (x : G) : avg (fun p : G → κ => f (fun j => p (x+offset j))) = avg f :=
    avg_restrict ⟨fun j => x+offset j, fun _ _ hh => ho (add_left_cancel hh)⟩ f
  simp_rw [he]
  simp

omit [Fintype κ] [Nonempty κ] in
/-- A changed mask coordinate lies in at most `k` translated windows.
Repeated offsets only reduce this number. -/
theorem windowSum_boundedChanges (offset : Fin k → G) (f : (Fin k → κ) → ℝ)
    (hf : ∀ x, 0≤f x ∧ f x≤1) :
    BoundedChanges (windowSum offset f) (fun _ => (k : ℝ)) := by
  classical
  intro i p q hpq
  let A : Finset G := Finset.univ.image (fun j : Fin k => i-offset j)
  have hsame (x : G) (hx : x ∉ A) :
      f (fun j => p (x+offset j))=f (fun j => q (x+offset j)) := by
    apply congrArg f
    funext j
    apply hpq (x+offset j)
    intro he
    apply hx
    apply Finset.mem_image.mpr
    refine ⟨j,Finset.mem_univ _,?_⟩
    exact (eq_sub_of_add_eq he).symm
  have hterm (x : G) :
      |f (fun j => p (x+offset j))-f (fun j => q (x+offset j))| ≤
        if x∈A then (1 : ℝ) else 0 := by
    by_cases hx : x∈A
    · rw [ite_eq_left hx]
      apply abs_le.mpr
      have hh := hf (fun j => p (x+offset j))
      have hh' := hf (fun j => q (x+offset j))
      constructor <;> linarith
    · rw [ite_eq_right hx,hsame x hx,sub_self,abs_zero]
  change |(∑ x, f (fun j => p (x+offset j)))-∑ x, f (fun j => q (x+offset j))| ≤ _
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ x : G, |f (fun j => p (x+offset j))-f (fun j => q (x+offset j))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x : G, if x∈A then (1 : ℝ) else 0 :=
      Finset.sum_le_sum (fun x _ => hterm x)
    _ = (A.card : ℝ) := by simp
    _ ≤ (k : ℝ) := by
      exact_mod_cast (Finset.card_image_le.trans (by simp :
        (Finset.univ : Finset (Fin k)).card ≤ k))

end Windows

end LeanMachine.FiniteProbability
