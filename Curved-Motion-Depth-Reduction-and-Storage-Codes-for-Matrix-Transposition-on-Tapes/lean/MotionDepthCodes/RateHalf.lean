import MotionDepthCodes.StorageCode

/-!
# Corollary H2: rate one half on graphs that map to a good graph

If a graph `G` is good, in particular if it has a homomorphism to a good graph such as `C₅`, the
Petersen graph or a circular clique `K_{p/q}` with `p/q ≤ 14/5` (`IsGood.of_hom`), then every
storage code on `G`, linear or not, over any alphabet, satisfies `|C|² ≤ |α|^|V|`, and every random
word supported on a storage code satisfies `2 H(X) ≤ Σ_v H(X_v)`. There is no degree assumption.
-/

namespace MotionDepthCodes

open Finset
open scoped BigOperators
set_option autoImplicit false

variable {V α : Type*} [Fintype V] [DecidableEq V] [Fintype α]

/-- A rate bound of one half for codes, in integer form: `|C|² ≤ |α|^|V|`. -/
theorem card_sq_le_of_rateBound_half [Nonempty α] {N : V → Finset V}
    (hN : RateBound N (1 / 2)) {C : Finset (V → α)} (hC : IsStorageCode N C) :
    C.card ^ 2 ≤ Fintype.card α ^ Fintype.card V := by
  rcases C.eq_empty_or_nonempty with hCe | hne
  · rw [hCe, Finset.card_empty]
    positivity
  · have h1 := log_card_le_of_rateBound (by norm_num) hN hC
    have hc : (0 : ℝ) < C.card := by exact_mod_cast hne.card_pos
    have hα : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
    have h2 : Real.log ((C.card : ℝ) ^ 2) ≤ Real.log ((Fintype.card α : ℝ) ^ Fintype.card V) := by
      rw [Real.log_pow, Real.log_pow]
      push_cast
      linarith
    have h3 := (Real.log_le_log_iff (by positivity) (by positivity)).mp h2
    exact_mod_cast h3

/-- **Corollary H2, cardinality form.** Every storage code on a good graph satisfies
`|C|² ≤ |α|^|V|`. -/
theorem IsGood.card_sq_le [Nonempty α] {G : SimpleGraph V} [DecidableRel G.Adj] (hG : IsGood G)
    {C : Finset (V → α)} (hC : IsStorageCode (nbhd G) C) :
    C.card ^ 2 ≤ Fintype.card α ^ Fintype.card V :=
  card_sq_le_of_rateBound_half hG hC

/-- **Corollary H2, entropy form.** Every random word recoverable for a good graph satisfies
`2 H(X) ≤ Σ_v H(X_v)`. -/
theorem IsGood.codeEntropy_le {Ω : Type*} [Fintype Ω] {G : SimpleGraph V} [DecidableRel G.Adj]
    (hG : IsGood G) (p : Ω → ℝ) (X : Ω → V → α) (hp : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1)
    (hX : IsRecoverable (nbhd G) X) :
    codeEntropy p X univ ≤ 1 / 2 * ∑ v, codeEntropy p X {v} :=
  codeEntropy_univ_le_of_rateBound p X hG hp hp1 hX

end MotionDepthCodes
