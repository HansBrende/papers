import TransposeFollowup.InverseLocalPackets
import TransposeFollowup.ConditionalEntropyFibers

/-! Helper-selected fixed packet codes and the exact averaging step for their
conditional bounds. The fiber-bound premise below is an internal aggregation
interface, to be discharged by the single-code theorem. -/

namespace TransposeFollowup

open scoped BigOperators
open Classical
set_option autoImplicit false

/-- A deterministic helper selects a fixed bank, packet system, decoder, and
packet length. Each selected bank is a bijection on the full raw cube. -/
structure HelperInverseLocalPacketCode (d b : ℕ) (H : Type*) where
  helper : FiniteMatrix d b → H
  length : H → ℕ
  branch : (a : H) → InverseLocalPacketCode d b (length a)

namespace HelperInverseLocalPacketCode

variable {d b : ℕ} {H : Type*} (C : HelperInverseLocalPacketCode d b H)

/-- Correctness is needed only on the inputs selecting the branch in question. -/
def CorrectOn (F : Set (FiniteMatrix d b)) : Prop :=
  ∀ a, (C.branch a).CorrectOn (F ∩ {x | C.helper x = a})

theorem correctOn_branch {F : Set (FiniteMatrix d b)} (hc : C.CorrectOn F) (a : H) :
    (C.branch a).CorrectOn (F ∩ {x | C.helper x = a}) := hc a

theorem decode_eq_transposed {F : Set (FiniteMatrix d b)} (hc : C.CorrectOn F)
    (x : FiniteMatrix d b) (hx : x ∈ F) (j : Fin d) :
    (C.branch (C.helper x)).decode j (x j)
      ((C.branch (C.helper x)).broadcast x) = transposed x j :=
  hc (C.helper x) x ⟨hx, rfl⟩ j

end HelperInverseLocalPacketCode

/-- Exact deficit averaging for an arbitrary observation. The helper is
assumed determined by that observation; the observation need not be injective.
The divisor is arbitrary, so the bit-entropy choice is obtained with `log 2`. -/
theorem sum_helperMass_mul_observation_deficit
    {Ω H A : Type*} [Fintype Ω] [Fintype H] [Fintype A]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (X : Ω → A) (h : Ω → H) (hh : h.FactorsThrough X) (P c : ℝ) :
    (∑ a, helperMass p h a *
      (P - observationEntropy (helperConditionalWeight p h a)
        (fun x : HelperFiber h a => X x) / c)) =
      P - observationEntropy p X / c + observationEntropy p h / c := by
  have hΩ : Nonempty Ω := by
    obtain ⟨x, _⟩ := Finset.nonempty_of_sum_ne_zero (show (∑ x, p x) ≠ 0 by rw [hp1]; norm_num)
    exact ⟨x⟩
  have hA : Nonempty A := hΩ.map X
  have hH : Nonempty H := hΩ.map h
  have hf := observationEntropy_pair_of_factorsThrough p hp X h hh
  have he := sum_helperMass_mul_observationEntropy p hp h X
  rw [conditionalObservationEntropy, hf] at he
  have hs : ∑ a, helperMass p h a = 1 := (sum_helperMass p h).trans hp1
  calc
    _ = P - (∑ a, helperMass p h a *
        observationEntropy (helperConditionalWeight p h a)
          (fun x : HelperFiber h a => X x)) / c := by
      simp only [mul_sub, ← mul_div_assoc, Finset.sum_sub_distrib,
        ← Finset.sum_mul, ← Finset.sum_div, hs, one_mul]
    _ = _ := by rw [he]; ring

/-- Average a real-valued branch bound. Only positive-mass fibers need to
satisfy the premise; zero-mass fibers vanish. This lemma is algebraic and
therefore imposes no sign restrictions on the common coefficients. -/
theorem helper_entropy_bound_of_fiber_bounds
    {Ω H A : Type*} [Fintype Ω] [Fintype H] [Fintype A]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (X : Ω → A) (h : Ω → H) (hh : h.FactorsThrough X)
    (B Q : H → ℝ) (P a e L c : ℝ)
    (hbound : ∀ z, 0 < helperMass p h z →
      a * (P - B z) ≤ P + e * Q z + e * L *
        (P - observationEntropy (helperConditionalWeight p h z)
          (fun x : HelperFiber h z => X x) / c)) :
    a * (P - ∑ x, p x * B (h x)) ≤
      P + e * (∑ x, p x * Q (h x)) + e * L *
        (P - observationEntropy p X / c + observationEntropy p h / c) := by
  have hs : ∑ z, helperMass p h z = 1 := (sum_helperMass p h).trans hp1
  have hB : (∑ z, helperMass p h z * B z) = ∑ x, p x * B (h x) :=
    sum_pushforward_mul p h B
  have hQ : (∑ z, helperMass p h z * Q z) = ∑ x, p x * Q (h x) :=
    sum_pushforward_mul p h Q
  have hD := sum_helperMass_mul_observation_deficit p hp hp1 X h hh P c
  have hav : (∑ z, helperMass p h z * (a * (P - B z))) ≤
      ∑ z, helperMass p h z * (P + e * Q z + e * L *
        (P - observationEntropy (helperConditionalWeight p h z)
          (fun x : HelperFiber h z => X x) / c)) := by
    apply Finset.sum_le_sum
    intro z _
    by_cases hz : helperMass p h z = 0
    · simp [hz]
    · exact mul_le_mul_of_nonneg_left
        (hbound z (lt_of_le_of_ne (helperMass_nonneg p hp h z) (Ne.symm hz)))
        (helperMass_nonneg p hp h z)
  have hleft : (∑ z, helperMass p h z * (a * (P - B z))) =
      a * (P - ∑ x, p x * B (h x)) := by
    calc
      _ = a * ((∑ z, helperMass p h z) * P - ∑ z, helperMass p h z * B z) := by
        simp_rw [mul_sub]
        simp only [Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]
        congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring
      _ = _ := by rw [hs, hB, one_mul]
  have hright : (∑ z, helperMass p h z * (P + e * Q z + e * L *
        (P - observationEntropy (helperConditionalWeight p h z)
          (fun x : HelperFiber h z => X x) / c))) =
      P + e * (∑ x, p x * Q (h x)) + e * L *
        (P - observationEntropy p X / c + observationEntropy p h / c) := by
    calc
      _ = (∑ z, helperMass p h z) * P + e * (∑ z, helperMass p h z * Q z) +
          e * L * (∑ z, helperMass p h z *
            (P - observationEntropy (helperConditionalWeight p h z)
              (fun x : HelperFiber h z => X x) / c)) := by
        simp_rw [mul_add]
        simp only [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
        congr 1
        · congr 1
          apply Finset.sum_congr rfl
          intros
          ring
        · apply Finset.sum_congr rfl
          intros
          ring
      _ = _ := by rw [hs, one_mul, hQ, hD]
  rwa [hleft, hright] at hav

/-- The packet-budget specialization of the internal averaging lemma. The
input matrix observation may identify different sample points. -/
theorem helper_packet_bound_of_fiber_bounds
    {Ω H : Type*} [Fintype Ω] [Fintype H] {d b : ℕ}
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (X : Ω → FiniteMatrix d b) (h : Ω → H) (hh : h.FactorsThrough X)
    (B Q : H → ℕ) (ell : ℕ) (L : ℝ)
    (hbound : ∀ z, 0 < helperMass p h z →
      ((ell : ℝ) + 1) * ((d * d * b : ℕ) - (B z : ℝ)) ≤
        (d * d * b : ℕ) + (ell : ℝ) * (Q z : ℝ) + (ell : ℝ) * L *
          ((d * d * b : ℕ) - observationEntropy (helperConditionalWeight p h z)
            (fun x : HelperFiber h z => X x) / Real.log 2)) :
    ((ell : ℝ) + 1) * ((d * d * b : ℕ) - ∑ x, p x * (B (h x) : ℝ)) ≤
      (d * d * b : ℕ) + (ell : ℝ) * (∑ x, p x * (Q (h x) : ℝ)) +
        (ell : ℝ) * L * ((d * d * b : ℕ) - observationEntropy p X / Real.log 2 +
          observationEntropy p h / Real.log 2) :=
  helper_entropy_bound_of_fiber_bounds p hp hp1 X h hh
    (fun z => (B z : ℝ)) (fun z => (Q z : ℝ))
    (d * d * b : ℕ) ((ell : ℝ) + 1) ell L (Real.log 2) hbound

end TransposeFollowup
