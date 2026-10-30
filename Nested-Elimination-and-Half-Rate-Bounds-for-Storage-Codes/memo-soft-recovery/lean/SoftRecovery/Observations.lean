import SoftRecovery.Decomposition

namespace SoftRecovery

open Finset HalfRate MotionDepthCodes TransposeFollowup
open scoped BigOperators
set_option autoImplicit false

variable {V A : Type*} [DecidableEq V] [DecidableEq A]

/-- Restrict a polymatroid along any coordinate map. Injectivity is unnecessary. -/
theorem image_isPolymatroid {h : Finset A → ℝ} (hh : IsPolymatroid h) (f : V → A) :
    IsPolymatroid (fun S => h (S.image f)) := by
  refine ⟨by simpa using hh.empty, fun _ _ hST => hh.mono (image_subset_image hST), ?_⟩
  intro S T
  rw [image_union]
  have hm := hh.mono (image_inter_subset f S T)
  have hs := hh.submod (S.image f) (T.image f)
  linarith

/-- A common context may contain arbitrary additional variables, including
nonlinear functions of the inputs and auxiliary random variables. -/
def conditionalImage (h : Finset A → ℝ) (Z : Finset A) (f : V → A)
    (S : Finset V) : ℝ := contr h Z (S.image f)

theorem conditionalImage_isPolymatroid {h : Finset A → ℝ} (hh : IsPolymatroid h)
    (Z : Finset A) (f : V → A) : IsPolymatroid (conditionalImage h Z f) :=
  image_isPolymatroid (contr_isPolymatroid hh Z) f

theorem conditionalImage_increment (h : Finset A → ℝ) (Z : Finset A) (f : V → A)
    (S : Finset V) (v : V) :
    increment (conditionalImage h Z f) S v = increment h (S.image f ∪ Z) (f v) := by
  simp only [increment, conditionalImage, contr, image_insert, insert_union]
  ring

omit [DecidableEq V] in
theorem conditionalImage_singleton (h : Finset A → ℝ) (Z : Finset A) (f : V → A)
    (v : V) : conditionalImage h Z f {v} = increment h Z (f v) := by
  simp [conditionalImage, contr, increment]

variable [Fintype V]

/-- Soft elimination with any common context, expressed in the ambient variables. -/
theorem conditional_soft {h : Finset A → ℝ} (hh : IsPolymatroid h)
    (Z : Finset A) (f : V → A) {N : V → Finset V} {pcs : List (Finset V)}
    (hD : Decomp N ∅ pcs) :
    2 * (h (univ.image f ∪ Z) - h Z) ≤
      (∑ v, increment h Z (f v)) +
      ∑ v, increment h ((N v).image f ∪ Z) (f v) := by
  have hs := soft_half (conditionalImage_isPolymatroid hh Z f) hD
  simpa [conditionalImage, contr, increment] using hs

/-- Finite Shannon entropy specialization, reusing the earlier arbitrary-alphabet
entropy library. All quantities are in nats; dividing by log 2 gives bits. -/
theorem entropy_conditional_soft {Ω α : Type*} [Fintype A] [Fintype Ω] [Fintype α]
    (p : Ω → ℝ) (X : Ω → A → α) (hp : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1)
    (Z : Finset A) (f : V → A) {N : V → Finset V} {pcs : List (Finset V)}
    (hD : Decomp N ∅ pcs) :
    2 * (codeEntropy p X (univ.image f ∪ Z) - codeEntropy p X Z) ≤
      (∑ v, increment (codeEntropy p X) Z (f v)) +
      ∑ v, increment (codeEntropy p X) ((N v).image f ∪ Z) (f v) :=
  conditional_soft (codeEntropy_isPolymatroid p X hp hp1) Z f hD

omit [DecidableEq V] [Fintype V] in
/-- An actual decoder (agreement on the available variables determines the
output) supplies the zero-increment hypothesis used in the capacity bounds. -/
theorem entropy_increment_zero_of_recovery {Ω α : Type*}
    [Fintype A] [Fintype Ω] [Fintype α]
    (p : Ω → ℝ) (X : Ω → A → α) (hp : ∀ ω, 0 ≤ p ω)
    (S : Finset A) (v : A)
    (hr : ∀ x y, (∀ a ∈ S, X x a = X y a) → X x v = X y v) :
    increment (codeEntropy p X) S v = 0 := by
  have hrec : IsRecoverable (fun a => if a = v then S else {a}) X := by
    intro a x y ha
    by_cases hav : a = v
    · subst a
      exact hr x y (by simpa using ha)
    · exact ha a (by simp [hav])
  have he := codeEntropy_isValid p X hp hrec v
  have he' : codeEntropy p X (insert v S) = codeEntropy p X S := by simpa using he
  exact sub_eq_zero.mpr he'

end SoftRecovery
