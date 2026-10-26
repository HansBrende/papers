import MotionDepthCodes.DepthLabels

/-!
# Turn-counting labels

On a cyclic schedule whose hops form closed chains, consider a label `G` with values in `[0, q)`
that advances by `χ t` modulo `q` at every time, with `0 ≤ χ t < q`, and by `k h ≥ 1` modulo `q`
along every hop (the number of turns inside the hop, for the turn counter of the deep-nesting
pair). Then `q · cost(G) ≤ Σ_h k_h + Σ_t χ_t` and `q · #descents = Σ_t χ_t`
(`turnCounter_cost`). This is the label arithmetic of the turn-counter theorem, from Lemma Zq of the
series' fourth paper (`MotionDepthCodes.lemma_Zq`).
-/

namespace BoundedNesting

open Finset MotionDepthCodes

variable {τ H : Type*} [Fintype τ] [Fintype H]

/-- **Turn-counting labels.** -/
theorem turnCounter_cost (q : ℤ) (G : τ → ℤ) (hG : ∀ t, 0 ≤ G t ∧ G t < q) (tprev : τ ≃ τ)
    (p u : H → τ) (succ : H ≃ H) (hsucc : ∀ h, p (succ h) = u h)
    (χ : τ → ℤ) (hχ : ∀ t, 0 ≤ χ t ∧ χ t < q) (hGχ : ∀ t, G t - G (tprev t) ≡ χ t [ZMOD q])
    (k : H → ℤ) (hk : ∀ h, 1 ≤ k h) (hGk : ∀ h, G (u h) - G (p h) ≡ k h [ZMOD q]) :
    q * (((univ.filter fun h => G (u h) ≤ G (p h)).card : ℤ) +
        ((univ.filter fun t => G t < G (tprev t)).card : ℤ)) ≤ ∑ h, k h + ∑ t, χ t ∧
      q * ((univ.filter fun t => G t < G (tprev t)).card : ℤ) = ∑ t, χ t := by
  have htime : ∀ t, (G t - G (tprev t)) % q = χ t := by
    intro t
    rw [hGχ t]
    exact Int.emod_eq_of_lt (hχ t).1 (hχ t).2
  have hhop : ∀ h, (G (u h) - G (p h) - 1) % q ≤ k h - 1 := by
    intro h
    have e : (G (u h) - G (p h) - 1) % q = (k h - 1) % q := Int.ModEq.sub_right 1 (hGk h)
    rw [e]
    have hq : 0 < q := by have := hG (u h); omega
    have ha : 0 ≤ k h - 1 := by have := hk h; omega
    have h1 := Int.emod_add_mul_ediv (k h - 1) q
    have h2 : 0 ≤ q * ((k h - 1) / q) := mul_nonneg hq.le (Int.ediv_nonneg ha hq.le)
    linarith
  refine ⟨?_, ?_⟩
  · rw [lemma_Zq q G hG tprev p u succ hsucc]
    simp only [htime]
    have hsum : ∑ h, (G (u h) - G (p h) - 1) % q ≤ ∑ h, (k h - 1) := sum_le_sum fun h _ => hhop h
    have hcard : ∑ h : H, (k h - 1) = ∑ h, k h - Fintype.card H := by
      rw [sum_sub_distrib]; simp
    linarith
  · rw [card_descents_eq q G hG tprev]
    simp only [htime]

end BoundedNesting
