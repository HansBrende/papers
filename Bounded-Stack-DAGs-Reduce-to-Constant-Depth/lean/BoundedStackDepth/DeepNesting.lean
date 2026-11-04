import BoundedStackDepth.Main
import MergeDepth.DeepNestingHops

/-!
# Corollary N, first statement: the deep-nesting pairs are cut to bounded depth

The deep-nesting pair of the fourth paper consists of the deep-nesting walk `U = U(s₀, m, 1)` and its
shift `U(· + ξ)`. The eleventh paper's library defines `U` (`MergeDepth.dnpWalk`), the two heads
(`MergeDepth.headWalk`), and proves that `U` moves by `±1` at every step (`MergeDepth.dnpStep_pm`).

* `dnpPair`: the pair on natural times, head `0` is `x₁ = U` and head `1` is `x₂ = U(· + ξ)`.
* `dnpPair_isWalk`: both heads are walks.
* `dnp_cut`: **Corollary N, first statement.** Theorem T for two walks cuts the pair on `[0, T)`, with
  at most `εT` edges, to the depth `K^P − 1` of `k = 2`, which depends on neither `s₀`, `m`, `ξ`
  nor `T`.

The second statement of Corollary N, that Conjectures A′ and A″ are false, rests on Corollary 5.26 of
the eighth paper, a written proof there, and is not formalized.
-/

namespace BoundedStackDepth

open Finset BoundedNesting

/-- **The deep-nesting pair** on natural times: head `0` is `x₁ = U(s₀, m, 1)` and head `1` is
`x₂ = U(· + ξ)`, the heads `true` and `false` of `MergeDepth.headWalk`. -/
def dnpPair (s0 m : ℕ) (ξ : ℤ) (h : Fin 2) (t : ℕ) : ℤ := MergeDepth.headWalk s0 m ξ (h = 0) t

/-- Both heads of the deep-nesting pair are walks: `U` moves by `±1` at every step. -/
theorem dnpPair_isWalk {s0 m : ℕ} (hms : m ≤ s0) (ξ : ℤ) (h : Fin 2) :
    IsWalk (dnpPair s0 m ξ h) := by
  intro t
  simp only [dnpPair, MergeDepth.headWalk]
  generalize MergeDepth.headShift ξ (h = 0) = c
  rcases MergeDepth.dnpStep_pm hms (t + c) with hs | hs <;>
  · unfold MergeDepth.dnpStep at hs
    rw [Nat.cast_add, Nat.cast_one, add_right_comm, hs]
    norm_num

/-- **Corollary N, first statement.** For every `ε > 0`, all `s₀ ≥ m`, every shift `ξ` and every
`T`, the walk DAG of the deep-nesting pair on `[0, T)` has a cut of at most `εT` edges and depth at
most `D(2, ε) = K^P − 1`, which depends on neither `s₀`, `m`, `ξ` nor `T`. -/
theorem dnp_cut {ε : ℝ} (hε : 0 < ε) {s0 m : ℕ} (hms : m ≤ s0) (ξ : ℤ) (T : ℕ) :
    ∃ (cutS : Finset ℕ) (cutH : Finset (ℕ × ℕ)), cutS ⊆ Ico 1 T ∧
      cutH ⊆ hopPairs (allHops (dnpPair s0 m ξ) T) ∧ ((cutS.card + cutH.card : ℕ) : ℝ) ≤ ε * T ∧
      ∀ f n, AvoidPath T (hopPairs (allHops (dnpPair s0 m ξ) T)) cutH cutS f n →
        arcCount (hopPairs (allHops (dnpPair s0 m ξ) T)) f n ≤ parK 2 ε ^ parP 2 ε - 1 :=
  tcpAt_direct 2 hε T (dnpPair s0 m ξ) (dnpPair_isWalk hms ξ)

end BoundedStackDepth
