import TransposeFollowup.HelperRobustPacketBound
import TransposeFollowup.PacketRobustNumerics

/-! Explicit bounded-degree consequences for helper-selected inverse-local
packet codes. All graph-volume budgets are derived from the declared banks
and their actual packet-locality graphs. -/

namespace TransposeFollowup

open Classical
open scoped BigOperators
set_option autoImplicit false

namespace InverseRowBank

variable {d b : ℕ} (A : InverseRowBank d b)

/-- Pulling a bounded-degree row graph back through bounded inverse
incidence controls the conflict degree, including its diagonal. -/
theorem inverseSupportGraph_degree_add_one_le_power
    (G : SimpleGraph (Fin d)) [DecidableRel G.Adj] (c e D k : ℕ)
    (hd : 0 < d) (hb : 0 < b) (hD : 2 ≤ D)
    (hwidth : ∀ i, (A.support i).card ≤ c)
    (hreuse : ∀ v, (Finset.univ.filter (fun j => v ∈ A.support j)).card ≤ e)
    (hdegree : ∀ i, G.degree i ≤ D) (i : Fin d) :
    (inverseSupportGraph A.support G (k+1)).degree i + 1 ≤ 2*c*e*D^k := by
  calc
    _ ≤ c * (2*D^k) * e :=
      inverseSupportGraph_degree_add_one_le A.support G (k+1) c e (2*D^k)
        (by omega) (A.support_nonempty hd hb) hwidth hreuse
        (nearVertices_card_le_power G D hD hdegree k) i
    _ = _ := by ring

/-- The corresponding raw near-coordinate count. -/
theorem inverseNearBits_card_le_power
    (G : SimpleGraph (Fin d)) [DecidableRel G.Adj] (c e D k : ℕ)
    (hd : 0 < d) (hb : 0 < b) (hD : 2 ≤ D)
    (hwidth : ∀ i, (A.support i).card ≤ c)
    (hreuse : ∀ v, (Finset.univ.filter (fun j => v ∈ A.support j)).card ≤ e)
    (hdegree : ∀ i, G.degree i ≤ D) :
    (inverseNearBits (b:=b) A.support G (k+1)).card ≤ 2*c*e*d*b*D^k := by
  calc
    _ ≤ d * (c * (2*D^k) * e) * b :=
      inverseNearBits_card_le A.support G (k+1) c e (2*D^k)
        (by omega) (A.support_nonempty hd hb) hwidth hreuse
        (nearVertices_card_le_power G D hD hdegree k)
    _ = _ := by ring

end InverseRowBank

/-- Exact coefficient conversion for the conflict-degree choice used below. -/
theorem inverse_support_cover_coefficient (c e D k : ℕ)
    (hc : 0 < c) (he : 0 < e) (hD : 0 < D) :
    16 * (((2*c*e*D^k-1 : ℕ) : ℝ)+1)^2 =
      (64*c^2*e^2*D^(2*k) : ℕ) := by
  have hv : 1 ≤ 2*c*e*D^k := by
    have hx : 0 < 2*c*e*D^k := by positivity
    omega
  have ha : (((2*c*e*D^k-1 : ℕ) : ℝ)+1) = (2*c*e*D^k : ℕ) := by
    exact_mod_cast (Nat.sub_add_cancel hv)
  rw [ha]
  push_cast
  rw [mul_comm 2 k, pow_mul]
  ring


/-- A matrix observation loses no more than its finite bit capacity; adding
helper entropy therefore gives a nonnegative aggregate deficit. No
injectivity of the sample-to-matrix observation is assumed. -/
theorem helper_matrix_deficit_nonneg
    {Ω H : Type*} [Fintype Ω] [Fintype H] {d b : ℕ}
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (X : Ω → FiniteMatrix d b) (h : Ω → H) :
    0 ≤ (d*d*b : ℕ) - observationEntropy p X / Real.log 2 +
      observationEntropy p h / Real.log 2 := by
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hdef := InverseLocalPacketCode.input_deficit_nonneg p hp hp1 X
  have hh : 0 ≤ observationEntropy p h :=
    entropy_nonneg (pushforward p h) (pushforward_nonneg p hp h)
      (by rw [sum_pushforward, hp1])
  exact add_nonneg hdef (div_nonneg hh hlog.le)


namespace HelperInverseLocalPacketCode

variable {d b : ℕ} {H Ω : Type*} [Fintype H] [Fintype Ω]
    (C : HelperInverseLocalPacketCode d b H)

/-- Every-radius degree budget for an actual helper-selected code. No small
input-deficit or helper-entropy hypothesis is needed. This finite family also
excludes a fixed fractional saving when their sum is `o(P)` and the incidence
and degree caps are fixed. -/
theorem degree_broadcast_bound_scaled
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (X : Ω → FiniteMatrix d b) (hcorrect : C.CorrectOn (Set.range X))
    (G : H → SimpleGraph (Fin d)) (c e D k : ℕ)
    (hc : 0 < c) (he : 0 < e) (hD : 2 ≤ D) (hd : 0 < d) (hb : 0 < b)
    (hlocal : ∀ a, (C.branch a).LocalTo (G a))
    (hwidth : ∀ a i, ((C.branch a).bank.support i).card ≤ c)
    (hreuse : ∀ a v, (Finset.univ.filter (fun j => v ∈ (C.branch a).bank.support j)).card ≤ e)
    (hdegree : ∀ a i, (G a).degree i ≤ D) :
    ((k : ℝ) + 2) * ((d*d*b : ℕ) -
        ∑ x, p x * (C.length (C.helper (X x)) : ℝ)) ≤
      (d*d*b : ℕ) + ((k : ℝ) + 1) * (2*c*e*d*b*D^k : ℕ) +
        ((k : ℝ) + 1) * (1+64*c^2*e^2*D^(2*k) : ℕ) *
          ((d*d*b : ℕ) - observationEntropy p X / Real.log 2 +
            observationEntropy p (fun x => C.helper (X x)) / Real.log 2) := by
  let L := (d*d*b : ℕ) - observationEntropy p X / Real.log 2 +
    observationEntropy p (fun x => C.helper (X x)) / Real.log 2
  have hL : 0 ≤ L := helper_matrix_deficit_nonneg p hp hp1 X (fun x => C.helper (X x))
  let K := 2*c*e*D^k-1
  have hconflict : ∀ a i,
      (inverseSupportGraph (C.branch a).bank.support (G a) (k+1)).degree i ≤ K := by
    intro a i
    have h := (C.branch a).bank.inverseSupportGraph_degree_add_one_le_power
      (G a) c e D k (by omega) hb hD (hwidth a) (hreuse a) (hdegree a) i
    dsimp [K]
    omega
  have hnear (a : H) :
      (inverseNearBits (b:=b) (C.branch a).bank.support (G a) (k+1)).card ≤
        2*c*e*d*b*D^k :=
    (C.branch a).bank.inverseNearBits_card_le_power
      (G a) c e D k (by omega) hb hD (hwidth a) (hreuse a) (hdegree a)
  have hmean : (∑ x, p x *
      ((inverseNearBits (b:=b) (C.branch (C.helper (X x))).bank.support
        (G (C.helper (X x))) (k+1)).card : ℝ)) ≤ (2*c*e*d*b*D^k : ℕ) := by
    calc
      _ ≤ ∑ x, p x * (2*c*e*d*b*D^k : ℕ) := by
        apply Finset.sum_le_sum
        intro x _
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast hnear (C.helper (X x))) (hp x)
      _ = _ := by rw [← Finset.sum_mul, hp1, one_mul]
  have hcoef : 1 + min (d : ℝ) (16*((K : ℝ)+1)^2) ≤
      (1+64*c^2*e^2*D^(2*k) : ℕ) := by
    calc
      _ ≤ 1 + 16*((K : ℝ)+1)^2 := add_le_add le_rfl (min_le_right _ _)
      _ = _ := by
        rw [show 16*((K : ℝ)+1)^2 = (64*c^2*e^2*D^(2*k) : ℕ) from
          inverse_support_cover_coefficient c e D k hc he (by omega)]
        push_cast
        ring
  have hf := C.robust_broadcast_bound p hp hp1 X hcorrect G (k+1) K
    (by omega) hlocal hconflict
  have hstep : ((k+1 : ℕ) : ℝ) *
      (1 + min (d : ℝ) (16*((K : ℝ)+1)^2)) * L ≤
      ((k+1 : ℕ) : ℝ) * (1+64*c^2*e^2*D^(2*k) : ℕ) * L :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcoef (by positivity)) hL
  have hbnd := hf.trans (add_le_add
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left hmean (by positivity))) hstep)
  dsimp only [L] at hbnd
  convert hbnd using 1 <;> push_cast <;> ring

/-- Actual helper-selected bounded-degree codes broadcast all but an explicit
`O(P/log d)` number of bits in expectation when input deficit plus helper
entropy is `O(d*b)`. The bank may be globally nonlinear and helper dependent;
only its inverse row width and reuse are bounded. -/
theorem degree_expected_length_lower_bound
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (X : Ω → FiniteMatrix d b) (hcorrect : C.CorrectOn (Set.range X))
    (G : H → SimpleGraph (Fin d)) (c e D : ℕ) (A : ℝ)
    (hc : 0 < c) (he : 0 < e) (hD : 2 ≤ D) (hd : 2 ≤ d) (hb : 0 < b)
    (hA : 0 ≤ A)
    (hlocal : ∀ a, (C.branch a).LocalTo (G a))
    (hwidth : ∀ a i, ((C.branch a).bank.support i).card ≤ c)
    (hreuse : ∀ a v, (Finset.univ.filter (fun j => v ∈ (C.branch a).bank.support j)).card ≤ e)
    (hdegree : ∀ a i, (G a).degree i ≤ D)
    (hdeficit : (d*d*b : ℕ) - observationEntropy p X / Real.log 2 +
        observationEntropy p (fun x => C.helper (X x)) / Real.log 2 ≤ A * (d*b : ℕ)) :
    (∑ x, p x * (C.length (C.helper (X x)) : ℝ)) ≥
      (d*d*b : ℕ) -
        4 * (1 + 2*(c : ℝ)*e + A + 64*(c : ℝ)^2*e^2*A) *
          Real.log (D : ℝ) * (d*d*b : ℕ) / Real.log (d : ℝ) := by
  apply robust_packet_lower_bound d b c e D A _ _ hD hd hA hdeficit
  intro k
  exact C.degree_broadcast_bound_scaled p hp hp1 X hcorrect G c e D k
    hc he hD (by omega) hb hlocal hwidth hreuse hdegree

/-- Convenience form for an arbitrary stored-row degree cap, using
`max 2 Delta` in the explicit error constant. -/
theorem fixed_degree_expected_length_lower_bound
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (X : Ω → FiniteMatrix d b) (hcorrect : C.CorrectOn (Set.range X))
    (G : H → SimpleGraph (Fin d)) (c e Delta : ℕ) (A : ℝ)
    (hc : 0 < c) (he : 0 < e) (hd : 2 ≤ d) (hb : 0 < b) (hA : 0 ≤ A)
    (hlocal : ∀ a, (C.branch a).LocalTo (G a))
    (hwidth : ∀ a i, ((C.branch a).bank.support i).card ≤ c)
    (hreuse : ∀ a v, (Finset.univ.filter (fun j => v ∈ (C.branch a).bank.support j)).card ≤ e)
    (hdegree : ∀ a i, (G a).degree i ≤ Delta)
    (hdeficit : (d*d*b : ℕ) - observationEntropy p X / Real.log 2 +
        observationEntropy p (fun x => C.helper (X x)) / Real.log 2 ≤ A * (d*b : ℕ)) :
    (∑ x, p x * (C.length (C.helper (X x)) : ℝ)) ≥
      (d*d*b : ℕ) -
        4 * (1 + 2*(c : ℝ)*e + A + 64*(c : ℝ)^2*e^2*A) *
          Real.log (max 2 Delta : ℕ) * (d*d*b : ℕ) / Real.log (d : ℝ) :=
  C.degree_expected_length_lower_bound p hp hp1 X hcorrect G c e (max 2 Delta) A
    hc he (le_max_left _ _) hd hb hA hlocal hwidth hreuse
    (fun a i => (hdegree a i).trans (le_max_right _ _)) hdeficit

end HelperInverseLocalPacketCode

end TransposeFollowup
