import SourceCovers.QueryMovement
import LeanMachine.IntervalQueries

/-! The interval-query corollary, including losses from deleting expensive
intervals. The full timeline is charged, and different centres may be served
by different slots at different times inside their interval. -/

namespace SourceCovers.QueryMovement

open Finset LeanMachine.QueryMovement
open scoped BigOperators
noncomputable section

/-- Interval queries obey the stronger maximum-step bound, even for intervals
that share endpoints. The multiplicity lower bound may be any positive real.
An empty interval family and an empty surviving good family are allowed. -/
theorem interval_movement_max {ι τ : Type*} [Fintype ι] [Nonempty ι] [DecidableEq τ]
    {L ρ w r : ℝ} {N n k : ℕ} (hL : 0 < L) (hN : 0 < N)
    (hρ : 0 < ρ) (hr : 0 < r) (hk : 0 < k)
    (T : Finset τ) (S : τ → Finset (Fin N)) (Y : ι → ℕ → AddCircle L)
    (a b : τ → ℕ) (hab : ∀ j ∈ T, a j ≤ b j) (hbn : ∀ j ∈ T, b j ≤ n)
    (hdisj : (T : Set τ).PairwiseDisjoint fun j => Ico (a j) (b j))
    (hsize : ∀ j ∈ T, (S j).card = k)
    (hrepeat : ∀ A ∈ T.image S, r ≤ ((T.filter fun j => S j = A).card : ℝ))
    (hraw : ∀ j ∈ T, ∀ x ∈ S j, ∃ t ∈ Icc (a j) (b j), ∃ i, ∃ z : AddCircle L,
      dist z (centre L N x) ≤ w ∧ dist z (Y i t) ≤ ρ) :
    let F := (T.image S).card
    let C := elapsed (maxStep Y) n
    let lam := ρ / L
    let B := (min N (Fintype.card ι * (⌊3 * lam * N + 2 * w * N / L⌋₊ + 1))).choose k
    C ≤ variation Y n ∧
      (F : ℝ) - 4 * C / (ρ * r) ≤ ((⌊4 * C / ρ⌋₊ : ℝ) + 1) * B ∧
      (F : ℝ) - 4 * (C / L) / (lam * r) ≤ (1 + 4 * (C / L) / lam) * B ∧
      lam / 4 * (((F : ℝ) - B) / (B + 1 / r)) ≤ C / L := by
  classical
  dsimp only
  let F := (T.image S).card
  let C := elapsed (maxStep Y) n
  let B := (min N (Fintype.card ι * (⌊3 * (ρ / L) * N + 2 * w * N / L⌋₊ + 1))).choose k
  change C ≤ variation Y n ∧
    (F : ℝ) - 4 * C / (ρ * r) ≤ ((⌊4 * C / ρ⌋₊ : ℝ) + 1) * B ∧
    (F : ℝ) - 4 * (C / L) / ((ρ / L) * r) ≤ (1 + 4 * (C / L) / (ρ / L)) * B ∧
    (ρ / L) / 4 * (((F : ℝ) - B) / (B + 1 / r)) ≤ C / L
  have hC : 0 ≤ C := elapsed_nonneg (fun e _ => maxStep_nonneg Y e) le_rfl
  have hδ : 0 < ρ / 4 := by positivity
  have hcount : (F : ℝ) ≤ ((⌊C / (ρ / 4)⌋₊ : ℝ) + 1) * B + C / ((ρ / 4) * r) := by
    rcases T.eq_empty_or_nonempty with hT | ⟨j, hj⟩
    · have hF : F = 0 := by simp [F, hT]
      rw [hF, Nat.cast_zero]
      positivity
    · have hw : 0 ≤ w := by
        have hSj : (S j).Nonempty := card_pos.mp (by rw [hsize j hj]; exact hk)
        obtain ⟨x, hx⟩ := hSj
        obtain ⟨_, _, _, z, hz, _⟩ := hraw j hj x hx
        exact dist_nonneg.trans hz
      have h := card_interval_types_le T S (centre L N) Y a b (maxStep Y) n k
        (capacity L (ρ + w + ρ / 4 + ρ / 4) N (Fintype.card ι))
        ρ w (ρ / 4) (ρ / 4) r hδ hδ hr
        (fun e _ => maxStep_nonneg Y e) (fun i e _ => step_le_maxStep Y e i)
        hab hbn hdisj hsize hrepeat hraw ?_
      · have hcap : capacity L (ρ + w + ρ / 4 + ρ / 4) N (Fintype.card ι) =
            min N (Fintype.card ι * (⌊3 * (ρ / L) * N + 2 * w * N / L⌋₊ + 1)) := by
          unfold capacity
          congr 4
          ring
        simpa only [hcap] using h
      · intro y
        rw [centre_eq]
        exact LeanMachine.CircleGridCapacity.card_covered_le L (L / (2 * N)) N hL hN y
          (ρ + w + ρ / 4 + ρ / 4) (by positivity)
  have hid : C / (ρ / 4) = 4 * C / ρ := by ring
  have hcost : C / ((ρ / 4) * r) = 4 * C / (ρ * r) := by ring
  have hnorm : 4 * (C / L) / (ρ / L) = C / (ρ / 4) := by field_simp
  have hnormr : 4 * (C / L) / ((ρ / L) * r) = C / ((ρ / 4) * r) := by field_simp
  obtain ⟨hs, hl⟩ := interval_real_bounds hC hδ hr hcount
  refine ⟨elapsed_maxStep_le_variation Y n, ?_, ?_, ?_⟩
  · rw [hid, hcost] at hcount
    linarith
  · simpa only [hnorm, hnormr] using hs
  · convert div_le_div_of_nonneg_right hl hL.le using 1
    ring

/-- The paper's original summed-movement statement is a direct consequence
of the maximum-step version, with no positivity assumption on the capacity. -/
theorem interval_movement {ι τ : Type*} [Fintype ι] [Nonempty ι] [DecidableEq τ]
    {L ρ w r : ℝ} {N n k : ℕ} (hL : 0 < L) (hN : 0 < N)
    (hρ : 0 < ρ) (hr : 0 < r) (hk : 0 < k)
    (T : Finset τ) (S : τ → Finset (Fin N)) (Y : ι → ℕ → AddCircle L)
    (a b : τ → ℕ) (hab : ∀ j ∈ T, a j ≤ b j) (hbn : ∀ j ∈ T, b j ≤ n)
    (hdisj : (T : Set τ).PairwiseDisjoint fun j => Ico (a j) (b j))
    (hsize : ∀ j ∈ T, (S j).card = k)
    (hrepeat : ∀ A ∈ T.image S, r ≤ ((T.filter fun j => S j = A).card : ℝ))
    (hraw : ∀ j ∈ T, ∀ x ∈ S j, ∃ t ∈ Icc (a j) (b j), ∃ i, ∃ z : AddCircle L,
      dist z (centre L N x) ≤ w ∧ dist z (Y i t) ≤ ρ) :
    let F := (T.image S).card
    let v := variation Y n / L
    let lam := ρ / L
    let B := (min N (Fintype.card ι * (⌊3 * lam * N + 2 * w * N / L⌋₊ + 1))).choose k
    (F : ℝ) - 4 * v / (lam * r) ≤ (1 + 4 * v / lam) * B ∧
      lam / 4 * (((F : ℝ) - B) / (B + 1 / r)) ≤ v := by
  dsimp only
  obtain ⟨he, _, hs, hl⟩ := interval_movement_max hL hN hρ hr hk T S Y a b
    hab hbn hdisj hsize hrepeat hraw
  refine ⟨le_trans ?_ (hs.trans ?_), hl.trans ?_⟩
  · gcongr
  · gcongr
  · exact div_le_div_of_nonneg_right he hL.le

end
end SourceCovers.QueryMovement
