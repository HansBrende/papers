import TransposeFollowup.PacketDistanceBound
import TransposeFollowup.DistanceNumerics
import TransposeFollowup.CyclicNearCount
import Mathlib.Data.Nat.Sqrt
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Numerical consequences of the exact distance inequality, independent
of the packet implementation. Existing graph-ball and numerical lemmas
are reused; these premises also permit reuse by the original XOR family. -/

namespace TransposeFollowup

open Classical
set_option autoImplicit false

def PacketDistanceBudget (n b B : ℕ) (G : SimpleGraph (Fin n)) : Prop :=
  ∀ ell, (ell + 1) * (n * n * b) ≤ (ell + 1) * B + n * n * b +
    ell * (RecodedXorCode.nearBits (b := b) G ell).card

namespace PacketDistanceBudget

variable {n b B : ℕ}

theorem degree_broadcast_bound_scaled (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hbound : PacketDistanceBudget n b B G) (D : ℕ) (hD : 2 ≤ D)
    (hdegree : ∀ i, G.degree i ≤ D) (hn : 0 < n) :
    (Nat.log D n / 2 + 2) * (n * n * b) ≤
      (Nat.log D n / 2 + 2) * B + 3 * (n * n * b) := by
  let k := Nat.log D n / 2
  have hnear : (RecodedXorCode.nearBits (b := b) G (k + 1)).card ≤ b * n * (2 * D ^ k) :=
    card_nearBits_le_of_balls G (k + 1) (2 * D ^ k)
      (nearVertices_card_le_power G D hD hdegree k)
  have hbudget := half_log_power_budget D n hD hn
  change (k + 1) * D ^ k ≤ n at hbudget
  have hterm : (k + 1) * (RecodedXorCode.nearBits (b := b) G (k + 1)).card ≤ 2 * (n * n * b) := by
    calc
      _ ≤ (k + 1) * (b * n * (2 * D ^ k)) := Nat.mul_le_mul_left _ hnear
      _ = (2 * b * n) * ((k + 1) * D ^ k) := by ring
      _ ≤ (2 * b * n) * n := Nat.mul_le_mul_left _ hbudget
      _ = _ := by ring
  have hs := hbound (k + 1)
  change (k + 2) * (n * n * b) ≤ (k + 2) * B + 3 * (n * n * b)
  nlinarith

/-- Explicit fixed-degree theorem. In contrast with a qualitative big-O
statement, this gives a uniform constant and holds for every n>=2 and b>=0. -/
theorem degree_broadcast_lower_bound (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hbound : PacketDistanceBudget n b B G) (D : ℕ) (hD : 2 ≤ D)
    (hdegree : ∀ i, G.degree i ≤ D) (hn : 2 ≤ n) :
    (B : ℝ) ≥ (n * n * b : ℕ) -
      6 * Real.log (D : ℝ) * (n * n * b : ℕ) / Real.log (n : ℝ) := by
  let k := Nat.log D n / 2
  let P : ℝ := (n * n * b : ℕ)
  have hs : ((k : ℝ) + 2) * P ≤ ((k : ℝ) + 2) * B + 3 * P := by
    dsimp [k, P]
    exact_mod_cast degree_broadcast_bound_scaled G hbound D hD hdegree (by omega)
  have hk : 0 < (k : ℝ) + 2 := by positivity
  have hln : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hlog := log_le_twice_half_log D n hD (by omega)
  change Real.log (n : ℝ) ≤ 2 * ((k : ℝ) + 2) * Real.log (D : ℝ) at hlog
  have hratio : (3 : ℝ) / ((k : ℝ) + 2) ≤ 6 * Real.log (D : ℝ) / Real.log (n : ℝ) := by
    apply (div_le_div_iff₀ hk hln).mpr
    nlinarith
  have hgap : P - B ≤ 3 * P / ((k : ℝ) + 2) := by
    apply (le_div_iff₀ hk).mpr
    nlinarith
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hbound : P - B ≤ 6 * Real.log (D : ℝ) * P / Real.log (n : ℝ) := by
    calc
      _ ≤ 3 * P / ((k : ℝ) + 2) := hgap
      _ = P * (3 / ((k : ℝ) + 2)) := by ring
      _ ≤ P * (6 * Real.log (D : ℝ) / Real.log (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hratio hP
      _ = _ := by ring
  change (B : ℝ) ≥ P - _
  linarith

theorem fixed_degree_broadcast_lower_bound (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hbound : PacketDistanceBudget n b B G) (Delta : ℕ)
    (hdegree : ∀ i, G.degree i ≤ Delta) (hn : 2 ≤ n) :
    (B : ℝ) ≥ (n * n * b : ℕ) -
      6 * Real.log (max 2 Delta : ℕ) * (n * n * b : ℕ) / Real.log (n : ℝ) :=
  degree_broadcast_lower_bound G hbound (max 2 Delta) (le_max_left _ _)
    (fun i => (hdegree i).trans (le_max_right _ _)) hn


/-- One radius and one real ball-volume budget suffice. The error coefficient
need not be integral. -/
theorem broadcast_bound_of_ball_budget_real (G : SimpleGraph (Fin n))
    (hbound : PacketDistanceBudget n b B G) (k q : ℕ) (e : ℝ)
    (hballs : ∀ i, (nearVertices G k i).card ≤ q)
    (hbudget : (n : ℝ) + k * q ≤ (k + 1) * e) :
    (n * n * b : ℕ) ≤ (B : ℝ) + (b : ℝ) * n * e := by
  have hnear : ((RecodedXorCode.nearBits (b := b) G k).card : ℝ) ≤ (b : ℝ) * n * q := by
    exact_mod_cast card_nearBits_le_of_balls (b := b) G k q hballs
  have hs : ((k : ℝ) + 1) * (n * n * b : ℕ) ≤
      ((k : ℝ) + 1) * B + (n * n * b : ℕ) +
        k * (RecodedXorCode.nearBits (b := b) G k).card := by
    exact_mod_cast hbound k
  have hscaled : ((k : ℝ) + 1) * (n * n * b : ℕ) ≤
      ((k : ℝ) + 1) * ((B : ℝ) + (b : ℝ) * n * e) := by
    push_cast at hs ⊢
    nlinarith [mul_le_mul_of_nonneg_left hbudget
      (by positivity : 0 ≤ (b : ℝ) * n),
      mul_le_mul_of_nonneg_left hnear (by positivity : 0 ≤ (k : ℝ))]
  exact (mul_le_mul_iff_right₀ (by positivity : 0 < (k : ℝ) + 1)).mp hscaled

/-- Integral specialization of the shared real ball-budget estimate. -/
theorem broadcast_bound_of_ball_budget (G : SimpleGraph (Fin n))
    (hbound : PacketDistanceBudget n b B G) (k q e : ℕ)
    (hballs : ∀ i, (nearVertices G k i).card ≤ q)
    (hbudget : n + k * q ≤ (k + 1) * e) :
    n * n * b ≤ B + b * n * e := by
  have h := broadcast_bound_of_ball_budget_real G hbound k q (e : ℝ) hballs
    (by exact_mod_cast hbudget)
  exact_mod_cast h

theorem linear_ball_broadcast_bound_nat (G : SimpleGraph (Fin n))
    (hbound : PacketDistanceBudget n b B G)
    (hballs : ∀ ell, 1 ≤ ell → ∀ i, (nearVertices G ell i).card ≤ 2 * ell - 1) (hn : 0 < n) :
    n * n * b ≤ B + b * n * (3 * Nat.sqrt n) := by
  let k := Nat.sqrt n
  have hk : 1 ≤ k := Nat.sqrt_pos.mpr hn
  apply broadcast_bound_of_ball_budget G hbound k (2 * k) (3 * k)
    (fun i => (hballs k hk i).trans (Nat.sub_le _ _))
  have hnSq : n ≤ (k + 1) * (k + 1) := (Nat.lt_succ_sqrt n).le
  nlinarith

/-- Finite path/cycle error bn(sqrt(8(n+3))-4), retaining the exact ball cap
2k-1 and the divisor k+1. All recoding and decoding assumptions are unchanged. -/
theorem linear_ball_broadcast_lower_bound (G : SimpleGraph (Fin n))
    (hbound : PacketDistanceBudget n b B G)
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
  have hbound := broadcast_bound_of_ball_budget_real G hbound k (2 * k - 1)
    (4 * t - 4) (fun i => hballs k hk i) hbudget
  have hroot : Real.sqrt (8 * ((n : ℝ) + 3)) = 4 * t := by
    apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
    nlinarith
  rw [hroot]
  linarith

/-- Includes arbitrary row labels and arbitrary subgraphs of a cycle: the
placement in the cycle need only be an injective graph homomorphism. -/
theorem cycle_embedding_broadcast_lower_bound (G : SimpleGraph (Fin n))
    (hbound : PacketDistanceBudget n b B G) {m : ℕ} [NeZero m]
    (f : G →g SimpleGraph.cycleGraph m) (hf : Function.Injective f) (hn : 0 < n) :
    (B : ℝ) ≥ (n * n * b : ℕ) - (b : ℝ) * n * (Real.sqrt (8 * ((n : ℝ) + 3)) - 4) := by
  apply linear_ball_broadcast_lower_bound G hbound _ hn
  intro ell hell i
  exact (nearVertices_card_le_of_embedding f hf ell i).trans
    (nearVertices_card_subcycle _ le_rfl ell hell (f i))

theorem subcycle_broadcast_lower_bound (G : SimpleGraph (Fin n))
    (hbound : PacketDistanceBudget n b B G) (hcycle : G ≤ SimpleGraph.cycleGraph n) (hn : 0 < n) :
    (B : ℝ) ≥ (n * n * b : ℕ) - (b : ℝ) * n * (Real.sqrt (8 * ((n : ℝ) + 3)) - 4) := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  exact cycle_embedding_broadcast_lower_bound G hbound (.ofLE hcycle) Function.injective_id hn

theorem cycle_broadcast_lower_bound
    (hbound : PacketDistanceBudget n b B (SimpleGraph.cycleGraph n)) (hn : 0 < n) :
    (B : ℝ) ≥ (n * n * b : ℕ) - (b : ℝ) * n * (Real.sqrt (8 * ((n : ℝ) + 3)) - 4) :=
  subcycle_broadcast_lower_bound _ hbound le_rfl hn

theorem path_broadcast_lower_bound
    (hbound : PacketDistanceBudget n b B (SimpleGraph.pathGraph n)) (hn : 0 < n) :
    (B : ℝ) ≥ (n * n * b : ℕ) - (b : ℝ) * n * (Real.sqrt (8 * ((n : ℝ) + 3)) - 4) :=
  subcycle_broadcast_lower_bound _ hbound SimpleGraph.pathGraph_le_cycleGraph hn


end PacketDistanceBudget

namespace RecodedPacketCode

variable {n b B : ℕ} (C : RecodedPacketCode n b B)

theorem distanceBudget (hc : C.Correct) (G : SimpleGraph (Fin n)) (hG : C.LocalTo G) :
    PacketDistanceBudget n b B G := C.broadcast_lower_bound_scaled hc G hG

theorem degree_broadcast_bound_scaled (hc : C.Correct) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hG : C.LocalTo G) (D : ℕ) (hD : 2 ≤ D)
    (hdegree : ∀ i, G.degree i ≤ D) (hn : 0 < n) :
    (Nat.log D n / 2 + 2) * (n * n * b) ≤
      (Nat.log D n / 2 + 2) * B + 3 * (n * n * b) :=
  PacketDistanceBudget.degree_broadcast_bound_scaled G (C.distanceBudget hc G hG) D hD hdegree hn

theorem degree_broadcast_lower_bound (hc : C.Correct) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hG : C.LocalTo G) (D : ℕ) (hD : 2 ≤ D)
    (hdegree : ∀ i, G.degree i ≤ D) (hn : 2 ≤ n) :
    (B : ℝ) ≥ (n * n * b : ℕ) -
      6 * Real.log (D : ℝ) * (n * n * b : ℕ) / Real.log (n : ℝ) :=
  PacketDistanceBudget.degree_broadcast_lower_bound G (C.distanceBudget hc G hG) D hD hdegree hn

theorem fixed_degree_broadcast_lower_bound (hc : C.Correct) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hG : C.LocalTo G) (Delta : ℕ)
    (hdegree : ∀ i, G.degree i ≤ Delta) (hn : 2 ≤ n) :
    (B : ℝ) ≥ (n * n * b : ℕ) -
      6 * Real.log (max 2 Delta : ℕ) * (n * n * b : ℕ) / Real.log (n : ℝ) :=
  PacketDistanceBudget.fixed_degree_broadcast_lower_bound G (C.distanceBudget hc G hG)
    Delta hdegree hn

theorem linear_ball_broadcast_lower_bound (hc : C.Correct) (G : SimpleGraph (Fin n))
    (hG : C.LocalTo G)
    (hballs : ∀ ell, 1 ≤ ell → ∀ i, (nearVertices G ell i).card ≤ 2 * ell - 1) (hn : 0 < n) :
    (B : ℝ) ≥ (n * n * b : ℕ) -
      (b : ℝ) * n * (Real.sqrt (8 * ((n : ℝ) + 3)) - 4) :=
  PacketDistanceBudget.linear_ball_broadcast_lower_bound G (C.distanceBudget hc G hG) hballs hn

theorem cycle_embedding_broadcast_lower_bound (hc : C.Correct) (G : SimpleGraph (Fin n))
    (hG : C.LocalTo G) {m : ℕ} [NeZero m]
    (f : G →g SimpleGraph.cycleGraph m) (hf : Function.Injective f) (hn : 0 < n) :
    (B : ℝ) ≥ (n * n * b : ℕ) - (b : ℝ) * n * (Real.sqrt (8 * ((n : ℝ) + 3)) - 4) :=
  PacketDistanceBudget.cycle_embedding_broadcast_lower_bound G (C.distanceBudget hc G hG) f hf hn

theorem subcycle_broadcast_lower_bound (hc : C.Correct) (G : SimpleGraph (Fin n))
    (hG : C.LocalTo G) (hcycle : G ≤ SimpleGraph.cycleGraph n) (hn : 0 < n) :
    (B : ℝ) ≥ (n * n * b : ℕ) - (b : ℝ) * n * (Real.sqrt (8 * ((n : ℝ) + 3)) - 4) :=
  PacketDistanceBudget.subcycle_broadcast_lower_bound G (C.distanceBudget hc G hG) hcycle hn

theorem cycle_broadcast_lower_bound (hc : C.Correct)
    (hG : C.LocalTo (SimpleGraph.cycleGraph n)) (hn : 0 < n) :
    (B : ℝ) ≥ (n * n * b : ℕ) - (b : ℝ) * n * (Real.sqrt (8 * ((n : ℝ) + 3)) - 4) :=
  PacketDistanceBudget.cycle_broadcast_lower_bound (C.distanceBudget hc _ hG) hn

theorem path_broadcast_lower_bound (hc : C.Correct)
    (hG : C.LocalTo (SimpleGraph.pathGraph n)) (hn : 0 < n) :
    (B : ℝ) ≥ (n * n * b : ℕ) - (b : ℝ) * n * (Real.sqrt (8 * ((n : ℝ) + 3)) - 4) :=
  PacketDistanceBudget.path_broadcast_lower_bound (C.distanceBudget hc _ hG) hn

end RecodedPacketCode
end TransposeFollowup
