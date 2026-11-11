import BoundedArityDecoders.BoundedAritySetCapacityProofs
import BoundedArityDecoders.NativeSweepInterfaceProofs
import SharedDecoders.CapacitySetRate

/-!
# Unconditional Consequences & Asymptotic Corollaries of Bounded-Arity Set Capacity

This module packages the quantitative, unconditional, and asymptotic consequences of Part I
(`BoundedAritySetCapacity.lean` and `BoundedAritySetCapacityProofs.lean`) together with the
canonical word-width identity (`NativeSweepInterfaceProofs.lean`):

1. `canonicalWordAlphabet_card_and_ge_two`: `2 ≤ |CanonicalWordAlphabet d|` for all `d : ℕ`, and
   `|CanonicalWordAlphabet d| = 2 ^ ⌈log₂ d⌉` (`Nat.clog 2 d`) for all `d ≥ 2`.
2. `arityGainFactor` and `pMin_two_sided_theta_inv_arity`: two-sided `Θ(1 / (Δ + 1))` bounds
   `1 / (e (Δ + 1)) < Δ^Δ / (Δ + 1)^(Δ + 1) ≤ 1 / (2 (Δ + 1)) ≤ 1 / 4` for all `Δ ≥ 1`.
3. `theorem1_BoundedAritySetCapacity_unconditional` and `theorem1_CanonicalWordSetCapacity`:
   Theorem 1 for arbitrary (empty or nonempty) subsets `C ⊆ Σ^{d × d}` and arbitrary `M : ℕ`,
   plus direct instantiation on `CanonicalWordAlphabet d`.
4. `growingClasses_strict_inv_exp_deficit`: strict exponential rate bound
   `< 1 - (1 - δ - η) / (e (Δ + 1))` for arbitrary (empty or nonempty) subsets `C`.
5. `corollary_OneClassArityOneThreeQuarters` and
   `corollary_OneClassArityTwoTwentyThreeTwentySevenths`: explicit finite-`d` one-class (`M = 1`,
   `E = ∅`) rate bounds `3/4 + 1/(4 d)` at `Δ = 1` and `23/27 + 8/(27 d)` at `Δ = 2`.
6. `oneClassCanonicalArityTwo_of_allAlphabetHalfBarrier`: formal reduction from the all-alphabet
   `Δ = 2` half-barrier question to the canonical-word `Δ = 2` half-barrier bound.
7. `wall1_UnrestrictedArityRateLowerBoundAndTendstoOne` and
   `wall1_ExactLogarithmicAsymptoticAllDimensions`: explicit rate lower bounds
   `1 - log_{|Σ|}(2 d) / d^2` (general `d ≥ 2`) and `1 - log_{|Σ|}(d) / d^2` (prime `d`) at
   unrestricted cell arity `Δ = d^2` (`M = 1, E = ∅`), `Filter.Tendsto` convergence to rate `1`,
   and the exact all-dimension logarithmic remainder
   `log_{|Σ|} |Chosen| - (d^2 - log_{|Σ|} d) → 0` along all `d = n + 1` (prime or composite).
8. `asymptotic_SublinearClassesBrokenFractionRefutesRateOne`: for any fixed cell cone arity
   `Δ ≥ 1`, unbroken output fraction `δ ∈ (0, 1]`, and growing class count `M_d = o(d / Δ)`,
   eventual rate bound `≤ 1 - (δ / 2) * arityGainFactor Δ` and refutation of asymptotic rate `1`.
-/

namespace BoundedArityDecoders

open SharedDecoders
open scoped BigOperators

/-! ### 1. Canonical Word Alphabet Cardinality -/

/-- For every dimension `d : ℕ`, `CanonicalWordAlphabet d` has cardinality at least `2`
(since `1 ≤ Transpose.entryBits d`), and for every `d ≥ 2` its cardinality equals `2 ^ Nat.clog 2 d`
(`2 ^ ⌈log₂ d⌉`). -/
theorem canonicalWordAlphabet_card_and_ge_two :
    (∀ d : ℕ, 2 ≤ Fintype.card (CanonicalWordAlphabet d)) ∧
      (∀ d : ℕ, 2 ≤ d → Fintype.card (CanonicalWordAlphabet d) = 2 ^ Nat.clog 2 d) := by
  refine ⟨fun d => ?_, fun d hd => ?_⟩
  · rw [canonicalWordAlphabet_card]
    have hb : 1 ≤ Transpose.entryBits d := by
      unfold Transpose.entryBits
      omega
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ Transpose.entryBits d := Nat.pow_le_pow_right (by decide) hb
  · rw [canonicalWordAlphabet_card, entryBits_eq_clog d hd]

/-! ### 2. Two-Sided `Θ(1 / (Δ + 1))` Bounds on the Arity Gain Factor -/

/-- Per-clean-cell one-hop Bernoulli recovery probability lower bound
`Δ^Δ / (Δ + 1)^(Δ + 1)` appearing in Theorem 1. -/
noncomputable def arityGainFactor (Delta : ℕ) : ℝ :=
  (Delta : ℝ) ^ Delta / ((Delta + 1 : ℝ) ^ (Delta + 1))

private theorem nat_pow_add_mul_pow_le_succ_pow (d : ℕ) :
    ∀ k : ℕ, d ^ (k + 1) + (k + 1) * d ^ k ≤ (d + 1) ^ (k + 1)
  | 0 => by simp
  | k + 1 => by
    have ih := nat_pow_add_mul_pow_le_succ_pow d k
    calc d ^ (k + 2) + (k + 2) * d ^ (k + 1)
        ≤ d ^ (k + 2) + (k + 2) * d ^ (k + 1) + (k + 1) * d ^ k := Nat.le_add_right _ _
      _ = (d ^ (k + 1) + (k + 1) * d ^ k) * (d + 1) := by
          simp only [pow_succ]
          ring
      _ ≤ (d + 1) ^ (k + 1) * (d + 1) := Nat.mul_le_mul_right (d + 1) ih
      _ = (d + 1) ^ (k + 2) := (pow_succ (d + 1) (k + 1)).symm

private theorem two_mul_self_pow_le_succ_pow {Delta : ℕ} (hDelta : 1 ≤ Delta) :
    2 * Delta ^ Delta ≤ (Delta + 1) ^ Delta := by
  cases Delta with
  | zero => omega
  | succ m =>
    have h := nat_pow_add_mul_pow_le_succ_pow (m + 1) m
    have hEq : (m + 1) ^ (m + 1) + (m + 1) * (m + 1) ^ m = 2 * (m + 1) ^ (m + 1) := by
      rw [pow_succ']
      ring
    rwa [hEq] at h

/-- For every cone arity `Delta ≥ 1`, `arityGainFactor Delta = Δ^Δ / (Δ + 1)^(Δ + 1)` satisfies the
two-sided `Θ(1 / (Δ + 1))` bounds
`1 / (e (Δ + 1)) < arityGainFactor Delta ≤ 1 / (2 (Δ + 1)) ≤ 1 / 4`. -/
theorem pMin_two_sided_theta_inv_arity (Delta : ℕ) (hDelta : 1 ≤ Delta) :
    1 / (Real.exp 1 * (Delta + 1 : ℝ)) < arityGainFactor Delta ∧
      arityGainFactor Delta ≤ 1 / (2 * (Delta + 1 : ℝ)) ∧
      arityGainFactor Delta ≤ 1 / 4 := by
  have hLo : 1 / (Real.exp 1 * (Delta + 1 : ℝ)) < arityGainFactor Delta :=
    arityFactor_gt_inv_exp Delta hDelta
  have hNat : 2 * Delta ^ Delta ≤ (Delta + 1) ^ Delta :=
    two_mul_self_pow_le_succ_pow hDelta
  have hReal : 2 * (Delta : ℝ) ^ Delta ≤ ((Delta : ℝ) + 1) ^ Delta := by
    exact_mod_cast hNat
  have hDenPos : (0 : ℝ) < (Delta : ℝ) + 1 := by positivity
  have hProdLe :
      (Delta : ℝ) ^ Delta * (2 * ((Delta : ℝ) + 1)) ≤ ((Delta : ℝ) + 1) ^ (Delta + 1) := by
    calc (Delta : ℝ) ^ Delta * (2 * ((Delta : ℝ) + 1))
        = (2 * (Delta : ℝ) ^ Delta) * ((Delta : ℝ) + 1) := by ring
      _ ≤ ((Delta : ℝ) + 1) ^ Delta * ((Delta : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right hReal hDenPos.le
      _ = ((Delta : ℝ) + 1) ^ (Delta + 1) := (pow_succ _ _).symm
  have hUp : arityGainFactor Delta ≤ 1 / (2 * (Delta + 1 : ℝ)) := by
    unfold arityGainFactor
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  have hDeltaReal : (1 : ℝ) ≤ (Delta : ℝ) := by exact_mod_cast hDelta
  have hQuarter : 1 / (2 * (Delta + 1 : ℝ)) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  exact ⟨hLo, hUp, hUp.trans hQuarter⟩

/-! ### 3. Unconditional Theorem 1 (Empty or Nonempty `C`, Arbitrary `M`, Canonical Alphabet) -/

/-- **Unconditional Theorem 1 (Bounded-Arity Arbitrary-Set Shared-Decoder Capacity).**
Removes both the `C.Nonempty` and `1 ≤ M` hypotheses from `Theorem1_BoundedAritySetCapacitySpec`:
for any finite alphabet `Sigma` (`2 ≤ |Sigma|`), any `[NeZero d]`, any `M : ℕ`, any arity
`Delta ≥ 1`, and any (empty or nonempty) code `C : Set (State d Sigma)` validated by `(p, E, f, Q)`,
`log_{|Sigma|} |C| ≤ d^2 - (d^2 - |E| - d M Delta) * arityGainFactor Delta`. -/
theorem theorem1_BoundedAritySetCapacity_unconditional
    (d M Delta : ℕ) [NeZero d]
    (Sigma : Type*) [Fintype Sigma]
    (p : ZMod d → Fin M)
    (E : Finset (ZMod d × ZMod d))
    (f : Fin M → State d Sigma → (ZMod d → Sigma))
    (Q : Fin M → ZMod d → Finset (ZMod d × ZMod d))
    (C : Set (State d Sigma))
    (hSigma : 2 ≤ Fintype.card Sigma)
    (hDelta : 1 ≤ Delta)
    (hCode : IsBoundedAritySetCode Delta p E f Q C) :
    Real.log (Nat.card C : ℝ) / Real.log (Fintype.card Sigma : ℝ) ≤
      ((d ^ 2 : ℕ) : ℝ) -
        (((d ^ 2 : ℕ) : ℝ) - (E.card : ℝ) - (d : ℝ) * (M : ℝ) * (Delta : ℝ)) *
          arityGainFactor Delta := by
  have hM : 1 ≤ M := by
    have := (p 0).isLt
    omega
  by_cases hCne : C.Nonempty
  · have h :=
      theorem1_BoundedAritySetCapacity.2 d M Delta Sigma p E f Q C hSigma hM hDelta hCne hCode
    simpa only [Nat.cast_pow, arityGainFactor] using h
  · have hEmpty : C = ∅ := Set.not_nonempty_iff_eq_empty.mp hCne
    subst hEmpty
    have hCard0 : Nat.card (∅ : Set (State d Sigma)) = 0 := Nat.card_of_isEmpty
    rw [hCard0]
    simp only [CharP.cast_eq_zero, Real.log_zero, zero_div, Nat.cast_pow]
    have hGainPos : 0 < arityGainFactor Delta := by
      unfold arityGainFactor
      positivity
    have hGainQuarter : arityGainFactor Delta ≤ 1 / 4 :=
      (pMin_two_sided_theta_inv_arity Delta hDelta).2.2
    have hd2 : 0 ≤ (d : ℝ) ^ 2 := by positivity
    have hE0 : 0 ≤ (E.card : ℝ) := Nat.cast_nonneg _
    have hdMDelta : 0 ≤ (d : ℝ) * (M : ℝ) * (Delta : ℝ) := by positivity
    nlinarith

/-- Direct instantiation of unconditional Theorem 1 on the canonical word alphabet
`CanonicalWordAlphabet d = (Fin (Transpose.entryBits d) → Bool)`, valid for all `d ≥ 1`
(`[NeZero d]`) and all (empty or nonempty) subsets `C`. -/
theorem theorem1_CanonicalWordSetCapacity
    (d M Delta : ℕ) [NeZero d]
    (p : ZMod d → Fin M)
    (E : Finset (ZMod d × ZMod d))
    (f : Fin M → State d (CanonicalWordAlphabet d) → (ZMod d → CanonicalWordAlphabet d))
    (Q : Fin M → ZMod d → Finset (ZMod d × ZMod d))
    (C : Set (State d (CanonicalWordAlphabet d)))
    (hDelta : 1 ≤ Delta)
    (hCode : IsBoundedAritySetCode Delta p E f Q C) :
    Real.log (Nat.card C : ℝ) / Real.log (Fintype.card (CanonicalWordAlphabet d) : ℝ) ≤
      ((d ^ 2 : ℕ) : ℝ) -
        (((d ^ 2 : ℕ) : ℝ) - (E.card : ℝ) - (d : ℝ) * (M : ℝ) * (Delta : ℝ)) *
          arityGainFactor Delta :=
  theorem1_BoundedAritySetCapacity_unconditional d M Delta (CanonicalWordAlphabet d) p E f Q C
    (canonicalWordAlphabet_card_and_ge_two.1 d) hDelta hCode

/-! ### 4. Strict Exponential Rate Deficit Under Growing Classes & Broken Outputs -/

/-- Chaining `growingClassesPositiveDeficit` into an explicit strict exponential rate inequality
(`README.md` §II.1 Bullet 2) valid for any (empty or nonempty) `(Delta, p, E)`-bounded-arity code:
if `|E| ≤ δ d^2` and `M ≤ η d / Delta` with `0 ≤ δ`, `0 ≤ η`, and `δ + η < 1`, then
`log_{|Sigma|} |C| / d^2 < 1 - (1 - δ - η) / (e (Delta + 1))`. -/
theorem growingClasses_strict_inv_exp_deficit
    (d M Delta : ℕ) [NeZero d]
    (Sigma : Type*) [Fintype Sigma]
    (δ η : ℝ)
    (p : ZMod d → Fin M)
    (E : Finset (ZMod d × ZMod d))
    (f : Fin M → State d Sigma → (ZMod d → Sigma))
    (Q : Fin M → ZMod d → Finset (ZMod d × ZMod d))
    (C : Set (State d Sigma))
    (hSigma : 2 ≤ Fintype.card Sigma)
    (hDelta : 1 ≤ Delta)
    (hδ : 0 ≤ δ)
    (hη : 0 ≤ η)
    (hsum : δ + η < 1)
    (hE : (E.card : ℝ) ≤ δ * (d : ℝ) ^ 2)
    (hM_le : (M : ℝ) ≤ η * (d : ℝ) / (Delta : ℝ))
    (hCode : IsBoundedAritySetCode Delta p E f Q C) :
    Real.log (Nat.card C : ℝ) / (Real.log (Fintype.card Sigma : ℝ) * (d : ℝ) ^ 2) <
      1 - (1 - δ - η) / (Real.exp 1 * (Delta + 1 : ℝ)) := by
  have hM : 1 ≤ M := by
    have := (p 0).isLt
    omega
  have hPosCoeff : 0 < 1 - δ - η := by linarith
  by_cases hCne : C.Nonempty
  · obtain ⟨hRateLe, hGainGt⟩ :=
      growingClassesPositiveDeficit d M Delta Sigma δ η p E f Q C
        hSigma hM hDelta hδ hη hsum hE hM_le hCne hCode
    have hMulGt :
        (1 - δ - η) * (1 / (Real.exp 1 * (Delta + 1 : ℝ))) <
          (1 - δ - η) * ((Delta : ℝ) ^ Delta / ((Delta + 1 : ℝ) ^ (Delta + 1))) :=
      mul_lt_mul_of_pos_left hGainGt hPosCoeff
    rw [mul_one_div] at hMulGt
    linarith
  · have hEmpty : C = ∅ := Set.not_nonempty_iff_eq_empty.mp hCne
    subst hEmpty
    have hCard0 : Nat.card (∅ : Set (State d Sigma)) = 0 := Nat.card_of_isEmpty
    rw [hCard0]
    simp only [CharP.cast_eq_zero, Real.log_zero, zero_div]
    have hBounds := pMin_two_sided_theta_inv_arity Delta hDelta
    have hInvLtQuarter : 1 / (Real.exp 1 * (Delta + 1 : ℝ)) < 1 / 4 :=
      lt_of_lt_of_le hBounds.1 hBounds.2.2
    have hCoeffLe1 : 1 - δ - η ≤ 1 := by linarith
    have hFracLt : (1 - δ - η) / (Real.exp 1 * (Delta + 1 : ℝ)) < 1 / 4 := by
      calc (1 - δ - η) / (Real.exp 1 * (Delta + 1 : ℝ))
          = (1 - δ - η) * (1 / (Real.exp 1 * (Delta + 1 : ℝ))) := (mul_one_div _ _).symm
        _ ≤ 1 * (1 / (Real.exp 1 * (Delta + 1 : ℝ))) :=
            mul_le_mul_of_nonneg_right hCoeffLe1 (by positivity)
        _ < 1 / 4 := by linarith
    linarith

/-! ### 5. Finite-`d` One-Class (`M = 1, E = ∅`) Corollaries at `Δ = 1` and `Δ = 2` -/

/-- Specialization of unconditional Theorem 1 to `M = 1`, `E = ∅`, and cell arity `Delta = 1`:
every `(1, p, ∅)`-bounded-arity code `C ⊆ Σ^{d × d}` has normalized rate at most
`3 / 4 + 1 / (4 d)`. -/
theorem corollary_OneClassArityOneThreeQuarters
    (d : ℕ) [NeZero d]
    (Sigma : Type*) [Fintype Sigma]
    (p : ZMod d → Fin 1)
    (f : Fin 1 → State d Sigma → (ZMod d → Sigma))
    (Q : Fin 1 → ZMod d → Finset (ZMod d × ZMod d))
    (C : Set (State d Sigma))
    (hSigma : 2 ≤ Fintype.card Sigma)
    (hCode : IsBoundedAritySetCode 1 p ∅ f Q C) :
    Real.log (Nat.card C : ℝ) / (Real.log (Fintype.card Sigma : ℝ) * (d : ℝ) ^ 2) ≤
      3 / 4 + 1 / (4 * (d : ℝ)) := by
  have hThm1 :=
    theorem1_BoundedAritySetCapacity_unconditional d 1 1 Sigma p ∅ f Q C hSigma le_rfl hCode
  have hGain1 : arityGainFactor 1 = 1 / 4 := by
    unfold arityGainFactor
    norm_num
  rw [hGain1] at hThm1
  simp only [Finset.card_empty, CharP.cast_eq_zero, Nat.cast_one, Nat.cast_pow] at hThm1
  have hdPos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast NeZero.pos d
  have hd2Pos : (0 : ℝ) < (d : ℝ) ^ 2 := by positivity
  rw [← div_div, div_le_iff₀ hd2Pos]
  have hId : (3 / 4 + 1 / (4 * (d : ℝ))) * (d : ℝ) ^ 2 =
      (d : ℝ) ^ 2 - ((d : ℝ) ^ 2 - 0 - (d : ℝ) * 1 * 1) * (1 / 4) := by
    field_simp
    ring
  linarith

/-- Specialization of unconditional Theorem 1 to `M = 1`, `E = ∅`, and cell arity `Delta = 2`:
every `(2, p, ∅)`-bounded-arity code `C ⊆ Σ^{d × d}` has normalized rate at most
`23 / 27 + 8 / (27 d)`. -/
theorem corollary_OneClassArityTwoTwentyThreeTwentySevenths
    (d : ℕ) [NeZero d]
    (Sigma : Type*) [Fintype Sigma]
    (p : ZMod d → Fin 1)
    (f : Fin 1 → State d Sigma → (ZMod d → Sigma))
    (Q : Fin 1 → ZMod d → Finset (ZMod d × ZMod d))
    (C : Set (State d Sigma))
    (hSigma : 2 ≤ Fintype.card Sigma)
    (hCode : IsBoundedAritySetCode 2 p ∅ f Q C) :
    Real.log (Nat.card C : ℝ) / (Real.log (Fintype.card Sigma : ℝ) * (d : ℝ) ^ 2) ≤
      23 / 27 + 8 / (27 * (d : ℝ)) := by
  have hThm1 :=
    theorem1_BoundedAritySetCapacity_unconditional d 1 2 Sigma p ∅ f Q C hSigma (by decide) hCode
  have hGain2 : arityGainFactor 2 = 4 / 27 := by
    unfold arityGainFactor
    norm_num
  rw [hGain2] at hThm1
  simp only [Finset.card_empty, CharP.cast_eq_zero, Nat.cast_one, Nat.cast_ofNat,
    Nat.cast_pow] at hThm1
  have hdPos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast NeZero.pos d
  have hd2Pos : (0 : ℝ) < (d : ℝ) ^ 2 := by positivity
  rw [← div_div, div_le_iff₀ hd2Pos]
  have hId : (23 / 27 + 8 / (27 * (d : ℝ))) * (d : ℝ) ^ 2 =
      (d : ℝ) ^ 2 - ((d : ℝ) ^ 2 - 0 - (d : ℝ) * 1 * 2) * (4 / 27) := by
    field_simp
    ring
  linarith

/-! ### 6. Bridge from All-Alphabet `Δ = 2` Half-Barrier to Canonical-Word `Δ = 2` Bound -/

/-- Formal implication from the all-alphabet `Δ = 2` `1/2 + o(1)` rate bound
(`OneClassArityTwoHalfBarrierQuestion`) to the canonical-word `Δ = 2` `1/2 + o(1)` bound over
`CanonicalWordAlphabet d`. -/
theorem oneClassCanonicalArityTwo_of_allAlphabetHalfBarrier.{u} :
    OneClassArityTwoHalfBarrierQuestion.{u} →
      ∀ c : ℝ, 0 < c → ∃ D₀ : ℕ,
        ∀ (d : ℕ) [NeZero d]
          (f : Fin 1 → State d (CanonicalWordAlphabet d) → (ZMod d → CanonicalWordAlphabet d))
          (Q : Fin 1 → ZMod d → Finset (ZMod d × ZMod d))
          (C : Set (State d (CanonicalWordAlphabet d))),
          max D₀ 2 ≤ d →
          C.Nonempty →
          IsBoundedAritySetCode 2 (fun _ => 0) ∅ f Q C →
          Real.log (Nat.card C : ℝ) ≤
            (1 / 2 + c) * (Real.log (Fintype.card (CanonicalWordAlphabet d) : ℝ) * (d : ℝ) ^ 2) := by
  intro hAll c hc
  obtain ⟨D₀, hD₀⟩ := hAll c hc
  refine ⟨D₀, fun d _ f Q C hd hCne hCode => ?_⟩
  have hd0 : D₀ ≤ d := (le_max_left D₀ 2).trans hd
  have hd2 : 2 ≤ d := (le_max_right D₀ 2).trans hd
  let WU : Type u := ULift.{u} (CanonicalWordAlphabet d)
  let toU : State d (CanonicalWordAlphabet d) → State d WU :=
    fun X i j => ULift.up (X i j)
  let ofU : State d WU → State d (CanonicalWordAlphabet d) :=
    fun Y i j => (Y i j).down
  have hToUInj : Function.Injective toU := by
    intro X₁ X₂ hEq
    funext i j
    exact congrArg ULift.down (congrFun (congrFun hEq i) j)
  let fU : Fin 1 → State d WU → (ZMod d → WU) :=
    fun m Y r => ULift.up (f m (ofU Y) r)
  let CU : Set (State d WU) := toU '' C
  have hCodeU : IsBoundedAritySetCode 2 (fun _ => 0) ∅ fU Q CU := by
    refine ⟨⟨hCode.1.1, fun m r Y₁ Y₂ hAgree => ?_⟩, ?_⟩
    · dsimp only [fU]
      congr 1
      refine hCode.1.2 m r (ofU Y₁) (ofU Y₂) fun q hq => ?_
      exact congrArg ULift.down (hAgree q hq)
    · rintro _ ⟨X, hX, rfl⟩ r c hcE
      dsimp only [fU, toU]
      exact congrArg ULift.up (hCode.2 X hX r c hcE)
  have hSigmaBase : 2 ≤ Fintype.card (CanonicalWordAlphabet d) :=
    canonicalWordAlphabet_card_and_ge_two.1 d
  have hSigmaU : 2 ≤ Fintype.card WU := by
    simpa only [WU, Fintype.card_ulift] using hSigmaBase
  have hRate := hD₀ d WU fU Q CU hd0 hSigmaU (hCne.image toU) hCodeU
  have hCardEq : Nat.card CU = Nat.card C :=
    Nat.card_congr (Equiv.Set.image toU C hToUInj).symm
  rw [hCardEq, Fintype.card_ulift] at hRate
  have hGt1 : (1 : ℝ) < (Fintype.card (CanonicalWordAlphabet d) : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by decide : 1 < 2) hSigmaBase
  have hLogPos : 0 < Real.log (Fintype.card (CanonicalWordAlphabet d) : ℝ) :=
    Real.log_pos hGt1
  have hd2Pos : (0 : ℝ) < (d : ℝ) ^ 2 := by
    have : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hd2)
    positivity
  exact (div_le_iff₀ (mul_pos hLogPos hd2Pos)).mp hRate

/-! ### 7. Wall 1 Unrestricted-Arity Rate Lower Bounds & Convergence to Rate `1` -/

private theorem mul_card_ge_pow_imp_rate_lower {d K : ℕ} {Sigma : Type*} [Fintype Sigma]
    {C : Set (State d Sigma)}
    (hd : 2 ≤ d) (hSigma : 2 ≤ Fintype.card Sigma) (hK : 1 ≤ K)
    (hMul : (Fintype.card Sigma) ^ (d ^ 2) ≤ K * Nat.card C) :
    C.Nonempty ∧
      1 - Real.log (K : ℝ) / (Real.log (Fintype.card Sigma : ℝ) * (d : ℝ) ^ 2) ≤
        Real.log (Nat.card C : ℝ) / (Real.log (Fintype.card Sigma : ℝ) * (d : ℝ) ^ 2) := by
  have hPowPos : 1 ≤ (Fintype.card Sigma) ^ (d ^ 2) :=
    Nat.one_le_pow _ _ (by omega)
  have hCne : C.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    rintro rfl
    have hCard0 : Nat.card (∅ : Set (State d Sigma)) = 0 := Nat.card_of_isEmpty
    rw [hCard0, mul_zero] at hMul
    omega
  have hCardPos : 1 ≤ Nat.card C := by
    by_contra h0
    have hEq0 : Nat.card C = 0 := by omega
    rw [hEq0, mul_zero] at hMul
    omega
  refine ⟨hCne, ?_⟩
  have hSigmaGt1 : (1 : ℝ) < (Fintype.card Sigma : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by decide : 1 < 2) hSigma
  have hLogSigmaPos : 0 < Real.log (Fintype.card Sigma : ℝ) := Real.log_pos hSigmaGt1
  have hdPos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hd)
  have hd2Pos : (0 : ℝ) < (d : ℝ) ^ 2 := by positivity
  have hDenPos : 0 < Real.log (Fintype.card Sigma : ℝ) * (d : ℝ) ^ 2 :=
    mul_pos hLogSigmaPos hd2Pos
  have hRealMul :
      ((Fintype.card Sigma : ℝ)) ^ (d ^ 2) ≤ (K : ℝ) * (Nat.card C : ℝ) := by
    exact_mod_cast hMul
  have hKPos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hCPos : (0 : ℝ) < (Nat.card C : ℝ) := by exact_mod_cast hCardPos
  have hLogLe :
      Real.log (Fintype.card Sigma : ℝ) * (d : ℝ) ^ 2 ≤
        Real.log (K : ℝ) + Real.log (Nat.card C : ℝ) := by
    have h := Real.log_le_log (pow_pos (by linarith) _) hRealMul
    rw [Real.log_pow, Nat.cast_pow, Real.log_mul hKPos.ne' hCPos.ne'] at h
    linarith
  have hLHS :
      1 - Real.log (K : ℝ) / (Real.log (Fintype.card Sigma : ℝ) * (d : ℝ) ^ 2) =
        (Real.log (Fintype.card Sigma : ℝ) * (d : ℝ) ^ 2 - Real.log (K : ℝ)) /
          (Real.log (Fintype.card Sigma : ℝ) * (d : ℝ) ^ 2) := by
    rw [sub_div, div_self hDenPos.ne']
  rw [hLHS]
  exact div_le_div_of_nonneg_right (by linarith) hDenPos.le

private theorem tendsto_one_sub_log_mul_div_sq (q : ℕ) (hq : 2 ≤ q) (c : ℝ) (hc : 1 ≤ c) :
    Filter.Tendsto
      (fun d : ℕ => 1 - Real.log (c * (d : ℝ)) / (Real.log (q : ℝ) * (d : ℝ) ^ 2))
      Filter.atTop (nhds 1) := by
  have hqGt1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast lt_of_lt_of_le (by decide : 1 < 2) hq
  have hLogQPos : 0 < Real.log (q : ℝ) := Real.log_pos hqGt1
  have hEvLow : ∀ᶠ d : ℕ in Filter.atTop,
      0 ≤ Real.log (c * (d : ℝ)) / (Real.log (q : ℝ) * (d : ℝ) ^ 2) := by
    refine (Filter.eventually_ge_atTop 1).mono fun d hd => ?_
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have hcd1 : 1 ≤ c * (d : ℝ) := by nlinarith
    exact div_nonneg (Real.log_nonneg hcd1) (by positivity)
  have hEvHigh : ∀ᶠ d : ℕ in Filter.atTop,
      Real.log (c * (d : ℝ)) / (Real.log (q : ℝ) * (d : ℝ) ^ 2) ≤
        (c / Real.log (q : ℝ)) * ((d : ℝ))⁻¹ := by
    refine (Filter.eventually_ge_atTop 1).mono fun d hd => ?_
    have hdPos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    have hcdPos : 0 < c * (d : ℝ) := by positivity
    have hLogLe : Real.log (c * (d : ℝ)) ≤ c * (d : ℝ) := by
      linarith [Real.log_le_sub_one_of_pos hcdPos]
    have hDenPos : 0 < Real.log (q : ℝ) * (d : ℝ) ^ 2 := by positivity
    calc Real.log (c * (d : ℝ)) / (Real.log (q : ℝ) * (d : ℝ) ^ 2)
        ≤ (c * (d : ℝ)) / (Real.log (q : ℝ) * (d : ℝ) ^ 2) :=
          div_le_div_of_nonneg_right hLogLe hDenPos.le
      _ = (c / Real.log (q : ℝ)) * ((d : ℝ))⁻¹ := by field_simp
  have hInvZero : Filter.Tendsto (fun d : ℕ => ((d : ℝ))⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hUpperZero : Filter.Tendsto
      (fun d : ℕ => (c / Real.log (q : ℝ)) * ((d : ℝ))⁻¹) Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using hInvZero.const_mul (c / Real.log (q : ℝ))
  have hQuotZero : Filter.Tendsto
      (fun d : ℕ => Real.log (c * (d : ℝ)) / (Real.log (q : ℝ) * (d : ℝ) ^ 2))
      Filter.atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hUpperZero hEvLow hEvHigh
  simpa only [sub_zero] using tendsto_const_nhds.sub hQuotZero

/-- **Wall 1 Unrestricted-Arity Rate Lower Bound & Convergence to Rate `1`
(`README.md` §I.2 Wall 1 & §II.1).**
1. For every finite alphabet `Sigma` (`2 ≤ |Sigma|`) and every `d ≥ 2` (`[NeZero d]`), unrestricted
   inspection (`SyntacticColumnSupport d`, cell cone arity `d ^ 2`) with a single class (`M = 1`)
   and zero broken outputs (`E = ∅`) yields a nonempty nonlinear code `C ⊆ Σ^{d × d}` achieving
   normalized rate at least `1 - log(2 d) / (log |Sigma| * d^2)`, and at least
   `1 - log d / (log |Sigma| * d^2)` whenever `d` is prime.
2. For every alphabet size `q ≥ 2`, both rate lower-bound sequences converge to `1` as `d → ∞`. -/
theorem wall1_UnrestrictedArityRateLowerBoundAndTendstoOne.{u} :
    (∀ (d : ℕ) [NeZero d] (Sigma : Type u) [Fintype Sigma],
      2 ≤ d → 2 ≤ Fintype.card Sigma →
      ∃ (f : Fin 1 → State d Sigma → (ZMod d → Sigma))
        (Q : Fin 1 → ZMod d → Finset (ZMod d × ZMod d))
        (C : Set (State d Sigma)),
        C.Nonempty ∧
        IsBoundedAritySetCode (d ^ 2) (fun _ => 0) ∅ f Q C ∧
        SyntacticColumnSupport d f (fun _ _ => Finset.univ) ∧
        1 - Real.log (2 * (d : ℝ)) / (Real.log (Fintype.card Sigma : ℝ) * (d : ℝ) ^ 2) ≤
          Real.log (Nat.card C : ℝ) / (Real.log (Fintype.card Sigma : ℝ) * (d : ℝ) ^ 2) ∧
        (Nat.Prime d →
          1 - Real.log (d : ℝ) / (Real.log (Fintype.card Sigma : ℝ) * (d : ℝ) ^ 2) ≤
            Real.log (Nat.card C : ℝ) / (Real.log (Fintype.card Sigma : ℝ) * (d : ℝ) ^ 2))) ∧
    (∀ q : ℕ, 2 ≤ q →
      Filter.Tendsto
        (fun d : ℕ => 1 - Real.log (2 * (d : ℝ)) / (Real.log (q : ℝ) * (d : ℝ) ^ 2))
        Filter.atTop (nhds 1) ∧
      Filter.Tendsto
        (fun d : ℕ => 1 - Real.log (d : ℝ) / (Real.log (q : ℝ) * (d : ℝ) ^ 2))
        Filter.atTop (nhds 1)) := by
  refine ⟨?_, ?_⟩
  · intro d _ Sigma _ hd hSigma
    have hColUniv : ∀ (f : Fin 1 → State d Sigma → (ZMod d → Sigma)),
        SyntacticColumnSupport d f (fun _ _ => Finset.univ) := by
      intro f
      refine ⟨fun _ _ => by simp [ZMod.card], fun _ r Y₁ Y₂ hCol => ?_⟩
      have hEq : Y₁ = Y₂ := funext fun i => funext fun u => hCol i u (Finset.mem_univ u)
      rw [hEq]
    by_cases hp : Nat.Prime d
    · obtain ⟨C, f, Q, hCode, hMulPrime⟩ :=
        boundaryControl_DeficitVanishesAtDeltaEqD.{0, 0, u, 0}.2.2.2.1 d Sigma hp hSigma
      have hMul2d : (Fintype.card Sigma) ^ (d ^ 2) ≤ (2 * d) * Nat.card C :=
        hMulPrime.trans (Nat.mul_le_mul_right _ (by omega))
      obtain ⟨hCne, hRatePrime⟩ := mul_card_ge_pow_imp_rate_lower hd hSigma (by omega) hMulPrime
      obtain ⟨_, hRate2d⟩ := mul_card_ge_pow_imp_rate_lower hd hSigma (by omega) hMul2d
      exact ⟨f, Q, C, hCne, hCode, hColUniv f, by simpa [Nat.cast_mul] using hRate2d,
        fun _ => hRatePrime⟩
    · obtain ⟨C, f, Q, hCode, hMul2d⟩ :=
        boundaryControl_DeficitVanishesAtDeltaEqD.{0, 0, 0, u}.2.2.2.2 d Sigma hd hSigma
      obtain ⟨hCne, hRate2d⟩ := mul_card_ge_pow_imp_rate_lower hd hSigma (by omega) hMul2d
      exact ⟨f, Q, C, hCne, hCode, hColUniv f, by simpa [Nat.cast_mul] using hRate2d,
        fun hp' => absurd hp' hp⟩
  · intro q hq
    refine ⟨tendsto_one_sub_log_mul_div_sq q hq 2 (by norm_num), ?_⟩
    simpa only [one_mul] using tendsto_one_sub_log_mul_div_sq q hq 1 le_rfl

/-- **Exact All-Dimension Wall 1 Logarithmic Remainder (`README.md` §I.2 Wall 1 & §II.1).**
For every finite alphabet `Sigma` with `2 ≤ |Sigma|` and every positive integer dimension
`d = n + 1` (prime or composite, with no factor-of-`2` gap), Paper 17's optimal orbit-cluster code
`SharedDecoders.SetCapacity.Chosen` is a valid `(d^2, fun _ => 0, ∅)`-bounded-arity nonlinear shared
code of full column arity `d`, achieves the exact maximum cardinality among all zero-error
one-class shared codes (`Nat.card Chosen = SharedDecoders.SetCapacity.capacity`), and satisfies
`log_{|Sigma|} |Chosen| - (d^2 - log_{|Sigma|} d) → 0` as `d = n + 1 → ∞` along all positive
integers. -/
theorem wall1_ExactLogarithmicAsymptoticAllDimensions.{u}
    (Sigma : Type u) [Fintype Sigma] (hSigma : 2 ≤ Fintype.card Sigma) :
    (∀ n : ℕ,
      let d := n + 1
      ∃ (f : Fin 1 → State d Sigma → (ZMod d → Sigma))
        (Q : Fin 1 → ZMod d → Finset (ZMod d × ZMod d)),
        IsBoundedAritySetCode (d ^ 2) (fun _ => 0) ∅ f Q
          (SharedDecoders.SetCapacity.Chosen (d := d) (A := Sigma)) ∧
        SyntacticColumnSupport d f (fun _ _ => Finset.univ) ∧
        Nat.card (SharedDecoders.SetCapacity.Chosen (d := d) (A := Sigma)) =
          SharedDecoders.SetCapacity.capacity (d := d) (A := Sigma)) ∧
    Filter.Tendsto
      (fun n : ℕ =>
        Real.logb (Fintype.card Sigma : ℝ)
          (Nat.card (SharedDecoders.SetCapacity.Chosen (d := n + 1) (A := Sigma)) : ℝ) -
        (((n + 1 : ℕ) : ℝ) ^ 2 - Real.logb (Fintype.card Sigma : ℝ) (n + 1)))
      Filter.atTop (nhds 0) := by
  have : Nonempty Sigma := Fintype.card_pos_iff.mp (by omega)
  refine ⟨fun n => ?_, ?_⟩
  · dsimp only
    obtain ⟨f₀, hf₀⟩ :=
      SharedDecoders.SetCapacity.chosen_isCode (d := n + 1) (A := Sigma)
    refine ⟨fun _ => f₀, fun _ _ => Finset.univ, ?_, ?_,
      SharedDecoders.SetCapacity.chosen_card (d := n + 1) (A := Sigma)⟩
    · refine ⟨⟨fun _ _ => ?_, fun _ r Y₁ Y₂ hEq => ?_⟩, fun X hX r c _ => ?_⟩
      · simp [ZMod.card, sq]
      · have hY : Y₁ = Y₂ :=
          funext fun i => funext fun u => hEq (i, u) (Finset.mem_univ (i, u))
        rw [hY]
      · exact congrFun (hf₀ X hX c) r
    · refine ⟨fun _ _ => by simp [ZMod.card], fun _ r Y₁ Y₂ hCol => ?_⟩
      have hY : Y₁ = Y₂ :=
        funext fun i => funext fun u => hCol i u (Finset.mem_univ u)
      rw [hY]
  · simpa only [SharedDecoders.SetCapacity.positiveCapacity,
      SharedDecoders.SetCapacity.chosen_card] using
      SharedDecoders.SetCapacity.logarithmic_rate_tendsto (A := Sigma) hSigma

/-! ### 8. Asymptotic Sublinear-Class Rate Deficit Refuting Rate `1` (`README.md` §III.1) -/

/-- **Asymptotic Positive Rate Deficit Under Sublinear Classes (`README.md` §III.1).**
For any fixed cell cone arity `Delta ≥ 1`, any unbroken output fraction `δ ∈ (0, 1]`, and any
family of `(Delta, p_d, E_d)`-bounded-arity nonlinear shared codes `C_d ⊆ (Sigma d)^{d × d}` with
`M_d = o(d / Delta)` (`M_d * Delta / d → 0`) and `|E_d| ≤ (1 - δ) d^2`:
1. `(δ / 2) * arityGainFactor Delta > 0`;
2. Eventually for all large `d`, the normalized rate satisfies
   `log_{|Sigma d|} |C_d| / d^2 ≤ 1 - (δ / 2) * arityGainFactor Delta`;
3. Consequently, the normalized rate sequence cannot converge to `1` as `d → ∞` (refuting the
   unrestricted-arity rate-`1` phenomenon of Wall 1 for all bounded-cone decoders). -/
theorem asymptotic_SublinearClassesBrokenFractionRefutesRateOne
    (Delta : ℕ) (hDelta : 1 ≤ Delta)
    (δ : ℝ) (hδPos : 0 < δ) (_hδLe : δ ≤ 1)
    (Sigma : ℕ → Type*) [∀ d, Fintype (Sigma d)]
    (hSigma : ∀ d : ℕ, 2 ≤ d → 2 ≤ Fintype.card (Sigma d))
    (M : ℕ → ℕ)
    (p : ∀ d, ZMod d → Fin (M d))
    (E : ∀ d, Finset (ZMod d × ZMod d))
    (f : ∀ d, Fin (M d) → State d (Sigma d) → (ZMod d → Sigma d))
    (Q : ∀ d, Fin (M d) → ZMod d → Finset (ZMod d × ZMod d))
    (C : ∀ d, Set (State d (Sigma d)))
    (hSublinear :
      Filter.Tendsto (fun d : ℕ => (M d : ℝ) * (Delta : ℝ) / (d : ℝ)) Filter.atTop (nhds 0))
    (hBroken : ∀ d : ℕ, 2 ≤ d → ((E d).card : ℝ) ≤ (1 - δ) * (d : ℝ) ^ 2)
    (hCode : ∀ (d : ℕ) [NeZero d], 2 ≤ d →
      IsBoundedAritySetCode Delta (p d) (E d) (f d) (Q d) (C d)) :
    0 < (δ / 2) * arityGainFactor Delta ∧
      (∀ᶠ d in Filter.atTop,
        Real.log (Nat.card (C d) : ℝ) /
            (Real.log (Fintype.card (Sigma d) : ℝ) * (d : ℝ) ^ 2) ≤
          1 - (δ / 2) * arityGainFactor Delta) ∧
      ¬ Filter.Tendsto
          (fun d : ℕ =>
            Real.log (Nat.card (C d) : ℝ) /
              (Real.log (Fintype.card (Sigma d) : ℝ) * (d : ℝ) ^ 2))
          Filter.atTop (nhds 1) := by
  have hGainPos : 0 < arityGainFactor Delta := by
    unfold arityGainFactor
    positivity
  have hDefPos : 0 < (δ / 2) * arityGainFactor Delta := by positivity
  have hEvSmall : ∀ᶠ d in Filter.atTop,
      (M d : ℝ) * (Delta : ℝ) / (d : ℝ) < δ / 2 :=
    (tendsto_order.mp hSublinear).2 (δ / 2) (by linarith)
  have hEvRate : ∀ᶠ d in Filter.atTop,
      Real.log (Nat.card (C d) : ℝ) /
          (Real.log (Fintype.card (Sigma d) : ℝ) * (d : ℝ) ^ 2) ≤
        1 - (δ / 2) * arityGainFactor Delta := by
    refine ((Filter.eventually_ge_atTop 2).and hEvSmall).mono fun d ⟨hd, hMd⟩ => ?_
    have : NeZero d := ⟨by omega⟩
    have hThm1 :=
      theorem1_BoundedAritySetCapacity_unconditional d (M d) Delta (Sigma d)
        (p d) (E d) (f d) (Q d) (C d) (hSigma d hd) hDelta (hCode d hd)
    rw [Nat.cast_pow] at hThm1
    have hdPos : (0 : ℝ) < (d : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hd)
    have hd2Pos : (0 : ℝ) < (d : ℝ) ^ 2 := by positivity
    have hMDeltaLe : (M d : ℝ) * (Delta : ℝ) ≤ (δ / 2) * (d : ℝ) :=
      (div_le_iff₀ hdPos).mp hMd.le
    have hdMDeltaLe : (d : ℝ) * (M d : ℝ) * (Delta : ℝ) ≤ (δ / 2) * (d : ℝ) ^ 2 := by
      nlinarith
    have hEdLe := hBroken d hd
    have hCleanCoeff :
        (δ / 2) * (d : ℝ) ^ 2 ≤
          (d : ℝ) ^ 2 - ((E d).card : ℝ) - (d : ℝ) * (M d : ℝ) * (Delta : ℝ) := by
      linarith
    have hProdLe :
        ((δ / 2) * (d : ℝ) ^ 2) * arityGainFactor Delta ≤
          ((d : ℝ) ^ 2 - ((E d).card : ℝ) - (d : ℝ) * (M d : ℝ) * (Delta : ℝ)) *
            arityGainFactor Delta :=
      mul_le_mul_of_nonneg_right hCleanCoeff hGainPos.le
    rw [← div_div, div_le_iff₀ hd2Pos]
    nlinarith
  refine ⟨hDefPos, hEvRate, ?_⟩
  intro hLim
  have hEvGt : ∀ᶠ d in Filter.atTop,
      1 - (δ / 2) * arityGainFactor Delta <
        Real.log (Nat.card (C d) : ℝ) /
          (Real.log (Fintype.card (Sigma d) : ℝ) * (d : ℝ) ^ 2) :=
    (tendsto_order.mp hLim).1 (1 - (δ / 2) * arityGainFactor Delta) (by linarith)
  rcases (hEvRate.and hEvGt).exists with ⟨_, hLe, hGt⟩
  linarith

end BoundedArityDecoders
