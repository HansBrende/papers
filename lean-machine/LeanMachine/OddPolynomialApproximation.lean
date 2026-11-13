import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Odd polynomial approximation on a symmetric interval, by symmetrizing
Mathlib's Weierstrass approximation. -/

namespace LeanMachine

/-- A continuous odd function has odd polynomial approximants on every symmetric
closed interval. This includes the singleton interval and empty intervals. -/
theorem exists_odd_polynomial_near (f : ℝ → ℝ) (γ ε : ℝ)
    (hc : ContinuousOn f (Set.Icc (-γ) γ)) (ho : ∀ x, f (-x) = -f x) (hε : 0 < ε) :
    ∃ q : Polynomial ℝ, (∀ x, q.eval (-x) = -q.eval x) ∧
      ∀ x ∈ Set.Icc (-γ) γ, |q.eval x - f x| < ε := by
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn (-γ) γ f hc ε hε
  let q := Polynomial.C (1 / 2 : ℝ) * (p - p.comp (-Polynomial.X))
  have hq (x : ℝ) : q.eval x = (p.eval x - p.eval (-x)) / 2 := by
    simp [q, div_eq_mul_inv, mul_comm]
  refine ⟨q, ?_, ?_⟩
  · intro x
    rw [hq, hq, neg_neg]
    ring
  · intro x hx
    have hn : -x ∈ Set.Icc (-γ) γ := ⟨neg_le_neg hx.2, by linarith [hx.1]⟩
    have h₁ := abs_lt.mp (hp x hx)
    have h₂ := abs_lt.mp (hp (-x) hn)
    rw [ho] at h₂
    rw [hq, abs_lt]
    constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2]

end LeanMachine
