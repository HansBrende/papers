import TransposeFollowup.XorComponentCount
import TransposeFollowup.CyclicNearCount
import Mathlib.Data.Nat.Sqrt
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! The path/cycle consequence, with an explicit uniform square-root error.
The theorem covers every subgraph of a cycle, so includes the standard path
without needing a separate proof or silently assuming connectedness. -/

namespace TransposeFollowup

open Classical
set_option autoImplicit false

namespace RecodedXorCode

variable {n b B : ℕ} (C : RecodedXorCode n b B)

/-- One radius and one real ball-volume budget suffice. The error coefficient
need not be integral. -/
theorem broadcast_bound_of_ball_budget_real (hc : C.Correct) (G : SimpleGraph (Fin n))
    (hG : C.LocalTo G) (k q : ℕ) (e : ℝ)
    (hballs : ∀ i, (nearVertices G k i).card ≤ q)
    (hbudget : (n : ℝ) + k * q ≤ (k + 1) * e) :
    (n * n * b : ℕ) ≤ (B : ℝ) + (b : ℝ) * n * e := by
  have hnear : ((nearBits (b := b) G k).card : ℝ) ≤ (b : ℝ) * n * q := by
    exact_mod_cast card_nearBits_le_of_balls (b := b) G k q hballs
  have hs : ((k : ℝ) + 1) * (n * n * b : ℕ) ≤
      ((k : ℝ) + 1) * B + (n * n * b : ℕ) +
        k * (nearBits (b := b) G k).card := by
    exact_mod_cast C.broadcast_lower_bound_scaled hc G hG k
  have hscaled : ((k : ℝ) + 1) * (n * n * b : ℕ) ≤
      ((k : ℝ) + 1) * ((B : ℝ) + (b : ℝ) * n * e) := by
    push_cast at hs ⊢
    nlinarith [mul_le_mul_of_nonneg_left hbudget
      (by positivity : 0 ≤ (b : ℝ) * n),
      mul_le_mul_of_nonneg_left hnear (by positivity : 0 ≤ (k : ℝ))]
  exact (mul_le_mul_iff_right₀ (by positivity : 0 < (k : ℝ) + 1)).mp hscaled

/-- Integral specialization of the shared real ball-budget estimate. -/
theorem broadcast_bound_of_ball_budget (hc : C.Correct) (G : SimpleGraph (Fin n))
    (hG : C.LocalTo G) (k q e : ℕ)
    (hballs : ∀ i, (nearVertices G k i).card ≤ q)
    (hbudget : n + k * q ≤ (k + 1) * e) :
    n * n * b ≤ B + b * n * e := by
  have h := C.broadcast_bound_of_ball_budget_real hc G hG k q (e : ℝ) hballs
    (by exact_mod_cast hbudget)
  exact_mod_cast h

theorem linear_ball_broadcast_bound_nat (hc : C.Correct) (G : SimpleGraph (Fin n))
    (hG : C.LocalTo G)
    (hballs : ∀ ell, 1 ≤ ell → ∀ i, (nearVertices G ell i).card ≤ 2 * ell - 1) (hn : 0 < n) :
    n * n * b ≤ B + b * n * (3 * Nat.sqrt n) := by
  let k := Nat.sqrt n
  have hk : 1 ≤ k := Nat.sqrt_pos.mpr hn
  apply C.broadcast_bound_of_ball_budget hc G hG k (2 * k) (3 * k)
    (fun i => (hballs k hk i).trans (Nat.sub_le _ _))
  have hnSq : n ≤ (k + 1) * (k + 1) := (Nat.lt_succ_sqrt n).le
  nlinarith

/-- The shifted square-root error is no larger than the former square-root
error. This certifies that the new finite bound implies the previous one. -/
theorem linear_ball_error_le_sqrt (n : ℕ) (hn : 0 < n) :
    Real.sqrt (8 * ((n : ℝ) + 3)) - 4 ≤ Real.sqrt (8 * (n : ℝ)) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hs : (1 : ℝ) ≤ Real.sqrt (8 * (n : ℝ)) :=
    Real.one_le_sqrt.mpr (by nlinarith)
  have hsq := Real.sq_sqrt (show 0 ≤ 8 * (n : ℝ) by positivity)
  have hle : Real.sqrt (8 * ((n : ℝ) + 3)) ≤ Real.sqrt (8 * (n : ℝ)) + 4 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith
  linarith

/-- Finite path/cycle error bn(sqrt(8(n+3))-4), retaining the exact ball cap
2k-1 and the divisor k+1. All recoding and decoding assumptions are unchanged. -/
theorem linear_ball_broadcast_lower_bound (hc : C.Correct) (G : SimpleGraph (Fin n))
    (hG : C.LocalTo G)
    (hballs : ∀ ell, 1 ≤ ell → ∀ i, (nearVertices G ell i).card ≤ 2 * ell - 1) (hn : 0 < n) :
    (B : ℝ) ≥ (n * n * b : ℕ) -
      (b : ℝ) * n * (Real.sqrt (8 * ((n : ℝ) + 3)) - 4) := by
  let k := Nat.sqrt ((n + 3) / 2)
  let t : ℝ := Real.sqrt (((n : ℝ) + 3) / 2)
  have hk : 1 ≤ k := Nat.sqrt_pos.mpr (by omega : 0 < (n + 3) / 2)
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have ht : 0 ≤ t := Real.sqrt_nonneg _
  have ht2 : t ^ 2 = ((n : ℝ) + 3) / 2 := Real.sq_sqrt (by positivity)
  have hlow : 2 * k ^ 2 ≤ n + 3 := by
    have h : k ^ 2 ≤ (n + 3) / 2 := Nat.sqrt_le' ((n + 3) / 2)
    nlinarith [Nat.div_mul_le_self (n + 3) 2]
  have hupper : n + 3 < (k + 1) * (k + 1) * 2 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).mp (Nat.lt_succ_sqrt ((n + 3) / 2))
  have hlowR : 2 * (k : ℝ) ^ 2 ≤ (n : ℝ) + 3 := by exact_mod_cast hlow
  have hupperR : (n : ℝ) + 3 < ((k : ℝ) + 1) * ((k : ℝ) + 1) * 2 := by
    exact_mod_cast hupper
  have hkt : (k : ℝ) ≤ t := Real.le_sqrt_of_sq_le (by nlinarith)
  have htk : t ≤ (k : ℝ) + 1 := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨by positivity, by nlinarith⟩
  have hdelta : ((k : ℝ) + 1 - t) ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr htk) (sub_nonneg.mpr hkt)]
  have hq : (2 * k - 1 : ℕ) + 1 = 2 * k := Nat.sub_add_cancel (by omega)
  have hqR : ((2 * k - 1 : ℕ) : ℝ) + 1 = 2 * (k : ℝ) := by exact_mod_cast hq
  have hbudget : (n : ℝ) + k * (2 * k - 1 : ℕ) ≤ ((k : ℝ) + 1) * (4 * t - 4) := by
    nlinarith
  have hbound := C.broadcast_bound_of_ball_budget_real hc G hG k (2 * k - 1)
    (4 * t - 4) (fun i => hballs k hk i) hbudget
  have hroot : Real.sqrt (8 * ((n : ℝ) + 3)) = 4 * t := by
    apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
    nlinarith
  rw [hroot]
  linarith

/-- Includes arbitrary row labels and arbitrary subgraphs of a cycle: the
placement in the cycle need only be an injective graph homomorphism. -/
theorem cycle_embedding_broadcast_lower_bound (hc : C.Correct) (G : SimpleGraph (Fin n))
    (hG : C.LocalTo G) {m : ℕ} [NeZero m]
    (f : G →g SimpleGraph.cycleGraph m) (hf : Function.Injective f) (hn : 0 < n) :
    (B : ℝ) ≥ (n * n * b : ℕ) - (b : ℝ) * n * (Real.sqrt (8 * ((n : ℝ) + 3)) - 4) := by
  apply C.linear_ball_broadcast_lower_bound hc G hG _ hn
  intro ell hell i
  exact (nearVertices_card_le_of_embedding f hf ell i).trans
    (nearVertices_card_subcycle _ le_rfl ell hell (f i))

theorem subcycle_broadcast_lower_bound (hc : C.Correct) (G : SimpleGraph (Fin n))
    (hG : C.LocalTo G) (hcycle : G ≤ SimpleGraph.cycleGraph n) (hn : 0 < n) :
    (B : ℝ) ≥ (n * n * b : ℕ) - (b : ℝ) * n * (Real.sqrt (8 * ((n : ℝ) + 3)) - 4) := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  exact C.cycle_embedding_broadcast_lower_bound hc G hG (.ofLE hcycle) Function.injective_id hn

theorem cycle_broadcast_lower_bound (hc : C.Correct)
    (hG : C.LocalTo (SimpleGraph.cycleGraph n)) (hn : 0 < n) :
    (B : ℝ) ≥ (n * n * b : ℕ) - (b : ℝ) * n * (Real.sqrt (8 * ((n : ℝ) + 3)) - 4) :=
  C.subcycle_broadcast_lower_bound hc _ hG le_rfl hn

theorem path_broadcast_lower_bound (hc : C.Correct)
    (hG : C.LocalTo (SimpleGraph.pathGraph n)) (hn : 0 < n) :
    (B : ℝ) ≥ (n * n * b : ℕ) - (b : ℝ) * n * (Real.sqrt (8 * ((n : ℝ) + 3)) - 4) :=
  C.subcycle_broadcast_lower_bound hc _ hG SimpleGraph.pathGraph_le_cycleGraph hn

end RecodedXorCode
end TransposeFollowup
