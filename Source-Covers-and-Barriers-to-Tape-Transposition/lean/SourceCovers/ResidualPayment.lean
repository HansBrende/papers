import SourceCovers.ResidualGeometry
import LeanMachine.GridPayment

/-! Shifted-grid payment for actual residual lower endpoints. -/

namespace SourceCovers

open Classical Finset LeanMachine
open scoped BigOperators

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- Each distinct, initially unpaid residual lower is paid at most once. -/
def residualCut (R : ℕ → Finset ℕ) (n : ℕ) (Γ₀ : Finset ℕ)
    (Y : ι → ℕ → ℕ) (w θ : ℕ) : Finset ℕ :=
  GridPayment.cut (ResidualGeometry.U R n Γ₀) Y id (ResidualGeometry.last R n) w θ

def residualPayment (R : ℕ → Finset ℕ) (n : ℕ) (Γ₀ : Finset ℕ)
    (Y : ι → ℕ → ℕ) (w θ : ℕ) : Finset ℕ := Γ₀ ∪ residualCut R n Γ₀ Y w θ

theorem residualCut_actual {R : ℕ → Finset ℕ} {n : ℕ} {Γ₀ : Finset ℕ}
    {Y : ι → ℕ → ℕ} {w θ u : ℕ} (hu : u ∈ residualCut R n Γ₀ Y w θ) :
    u ∉ Γ₀ ∧ ∃ v ≤ n, u ∈ R v :=
  ResidualGeometry.mem_U.mp (GridPayment.cut_subset _ _ _ _ _ _ hu)

/-- The full payment is a disjoint union: there is no double charge. -/
theorem residualPayment_card (R : ℕ → Finset ℕ) (n : ℕ) (Γ₀ : Finset ℕ)
    (Y : ι → ℕ → ℕ) (w θ : ℕ) :
    (residualPayment R n Γ₀ Y w θ).card = Γ₀.card + (residualCut R n Γ₀ Y w θ).card := by
  apply card_union_of_disjoint
  exact disjoint_left.mpr (fun _ hΓ hcut => (residualCut_actual hcut).1 hΓ)

/-- The manuscript's oscillation sum over every initially unpaid vertex. -/
def residualOscillation (R : ℕ → Finset ℕ) (n : ℕ) (Γ₀ : Finset ℕ)
    (Y : ι → ℕ → ℕ) : ℝ :=
  ∑ u ∈ range (n + 1) \ Γ₀, ∑ i,
    (IntervalOscillation.oscillation (Y i) u (ResidualGeometry.last R n u) : ℝ)

theorem residualOscillation_eq_actual {R : ℕ → Finset ℕ} {n : ℕ} {Γ₀ : Finset ℕ}
    (hR : ∀ v ≤ n, ∀ u ∈ R v, u < v) (Y : ι → ℕ → ℕ) :
    residualOscillation R n Γ₀ Y = ∑ u ∈ ResidualGeometry.U R n Γ₀, ∑ i,
      (IntervalOscillation.oscillation (Y i) u (ResidualGeometry.last R n u) : ℝ) := by
  unfold residualOscillation
  rw [sum_comm, sum_comm (s := ResidualGeometry.U R n Γ₀)]
  apply sum_congr rfl
  intro i _
  exact_mod_cast ResidualGeometry.sum_oscillation_eq hR (Y i)

/-- Both refinements of the original estimate are retained: capped oscillation
and the actual live-boundary profile, before using a uniform bound `H`. -/
theorem residual_payment_bounds {R : ℕ → Finset ℕ} {n : ℕ} {Γ₀ : Finset ℕ}
    (Y : ι → ℕ → ℕ) {w : ℕ} {H : ℝ} (hw : 0 < w)
    (hR : ∀ v ≤ n, ∀ u ∈ R v, u < v)
    (hH : ∀ e < n, ((ResidualGeometry.live R n Γ₀ e).card : ℝ) ≤ H) :
    let cap := ∑ u ∈ ResidualGeometry.U R n Γ₀, ∑ i,
      (min w (IntervalOscillation.oscillation (Y i) u (ResidualGeometry.last R n u)) : ℝ)
    let profile := ∑ e ∈ range n, ((ResidualGeometry.live R n Γ₀ e).card : ℝ) *
      ∑ i, dist (Y i e : ℝ) (Y i (e + 1) : ℝ)
    (∑ θ ∈ range w, ((residualCut R n Γ₀ Y w θ).card : ℝ)) / w ≤ cap / w ∧
    cap / w ≤ residualOscillation R n Γ₀ Y / w ∧
    residualOscillation R n Γ₀ Y / w ≤ profile / w ∧
    profile / w ≤ (H * ∑ i, MonotonePatches.variation (fun t => (Y i t : ℝ)) n) / w := by
  dsimp only
  refine ⟨GridPayment.average_cut_card_le_capped _ _ _ _ hw, ?_, ?_, ?_⟩
  · rw [residualOscillation_eq_actual hR]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg w)
    exact sum_le_sum fun u _ => sum_le_sum fun i _ => by
      exact_mod_cast min_le_right w (IntervalOscillation.oscillation
        (Y i) u (ResidualGeometry.last R n u))
  · rw [residualOscillation_eq_actual hR]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg w)
    calc
      _ = ∑ i, ∑ u ∈ ResidualGeometry.U R n Γ₀,
          (IntervalOscillation.oscillation (Y i) u (ResidualGeometry.last R n u) : ℝ) := sum_comm
      _ ≤ ∑ i, ∑ e ∈ range n, ((ResidualGeometry.live R n Γ₀ e).card : ℝ) *
          dist (Y i e : ℝ) (Y i (e + 1) : ℝ) := by
        apply sum_le_sum
        intro i _
        exact IntervalOscillation.sum_oscillation_le_profile _ (Y i) id _ n
          (fun u _ => ResidualGeometry.le_last R n u)
          (fun _ hu => ResidualGeometry.last_le_of_mem_U hR hu)
      _ = _ := by rw [sum_comm]; simp only [mul_sum]
  · apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg w)
    calc
      _ ≤ ∑ e ∈ range n, (H : ℝ) * ∑ i, dist (Y i e : ℝ) (Y i (e + 1) : ℝ) := by
        apply sum_le_sum
        intro e he
        apply mul_le_mul_of_nonneg_right (hH e (mem_range.mp he))
        exact sum_nonneg (fun _ _ => dist_nonneg)
      _ = _ := by rw [← mul_sum, sum_comm]; rfl

/-- A single shift attains the original `H V / w` bill. -/
theorem exists_residualPayment_le {R : ℕ → Finset ℕ} {n : ℕ} {Γ₀ : Finset ℕ}
    (Y : ι → ℕ → ℕ) {w : ℕ} {H : ℝ} (hw : 0 < w)
    (hR : ∀ v ≤ n, ∀ u ∈ R v, u < v)
    (hH : ∀ e < n, ((ResidualGeometry.live R n Γ₀ e).card : ℝ) ≤ H) :
    ∃ θ < w, ((residualPayment R n Γ₀ Y w θ).card : ℝ) ≤ Γ₀.card +
      (H * ∑ i, MonotonePatches.variation (fun t => (Y i t : ℝ)) n) / w := by
  have hb := residual_payment_bounds Y hw hR hH
  obtain ⟨θ, hθ, hc⟩ := GridPayment.exists_cut_card_le hw
    (hb.1.trans (hb.2.1.trans (hb.2.2.1.trans hb.2.2.2)))
  refine ⟨θ, hθ, ?_⟩
  rw [residualPayment_card, Nat.cast_add]
  exact add_le_add le_rfl hc

end
end SourceCovers
