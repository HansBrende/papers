import MergeDepth.HopRoutingCount
import MergeDepth.HCStarQ91

/-!
# Proposition 3.16 for a trace

`hop_routing_trace`: Proposition 3.16(b) for the trace of a machine. The walks, read steps and
append steps that `hop_routing_count` takes as hypotheses are supplied by `trace_ball_data` for
any trace that appends at least `L` bits before `T`.
-/

namespace MergeDepth

open Finset BoundedNesting

variable {k : ℕ}

open Classical in
/-- **Proposition 3.16(b)** for a trace `τ₀` that appends at least `L = d²b` bits before `T`,
`T ≤ c (L + 1)`, `d ≥ 2`, with a cold genie of depth `D ≥ 1` and `D ≤ D''`: weights on
`Γ_F`-free dependency paths from the append step of each output position to steps that read the
transposed position, of total at most one per position and load at most `c₀` on every deep edge,
have total at most `(2 c K'' (k + 2)(k + 3) + 3) L / log₂ d + c₀ N_R / h`. -/
theorem hop_routing_trace {d b : ℕ} (hd : 2 ≤ d) (hb : 1 ≤ b) {τ₀ : Trace k} {T V β : ℕ}
    (happ : d * d * b ≤ (appendList τ₀ T).length) {ε : ℝ} {D : ℕ} {ΓF : Finset ℕ}
    (hcold : IsColdGenie (L := d * d * b) τ₀.work T V β ε D ΓF) (hD : 1 ≤ D)
    {c : ℝ} (hc : 0 ≤ c) (hT : (T : ℝ) ≤ c * (d * d * b + 1)) (D'' : ℕ) (hD'' : D ≤ D'')
    (P : Fin (d * d * b) → Finset (List ℕ))
    (hP : ∀ ℓ, ∀ π ∈ P ℓ, ∃ π', π = appendTime τ₀ T ℓ :: π' ∧ IsDepPath τ₀.work T π ∧
      LinNet.GFree ΓF π ∧ readPos τ₀ (d * d * b) (π.getLastD (appendTime τ₀ T ℓ)) =
        some (tposF d b hb ℓ))
    (f : Fin (d * d * b) → List ℕ → ℝ) (hf0 : ∀ ℓ π, 0 ≤ f ℓ π)
    (hf1 : ∀ ℓ, ∑ π ∈ P ℓ, f ℓ π ≤ 1) (c₀ : ℝ) (hc₀ : 0 ≤ c₀)
    (hload : ∀ a b', DeepStep τ₀.work T V a b' →
      ∑ ℓ, ∑ π ∈ (P ℓ).filter ((a, b') ∈ edgesOf ·), f ℓ π ≤ c₀) :
    ∑ ℓ, ∑ π ∈ P ℓ, f ℓ π ≤
        (2 * c * (∑ i ∈ range (D'' + 1), (k + 1) ^ i : ℕ) * (k + 2 : ℕ) * ((k + 2 : ℕ) + 1) + 3) *
          ((d : ℝ) ^ 2 * b) / Real.logb 2 d +
        c₀ * (deepHops τ₀.work T V).card / ⌈((D'' + 2 - D : ℕ) : ℝ) / D⌉₊ ∧
      (deepHops τ₀.work T V).card ≤ k * T := by
  obtain ⟨hrd, htout, -⟩ := trace_ball_data hb happ
  exact hop_routing_count hd hb (traceWalks_isWalk τ₀) hcold hD (readPos τ₀ (d * d * b)) hrd
    (appendTime τ₀ T) htout hc hT D'' hD'' P hP f hf0 hf1 c₀ hc₀ hload

end MergeDepth
