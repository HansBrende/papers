import LeanMachine.CircleGridCapacity

/-! Theorem M: a movement bill for a specified regular-grid query interface.
The stronger bound uses the largest slot movement at each step and retains
the integer part of the resulting movement budget. -/

namespace SourceCovers.QueryMovement

open Finset LeanMachine.QueryMovement
open scoped BigOperators
noncomputable section

/-- The paper's midpoint grid, on the actual metric circle. -/
def centre (L : ℝ) (N : ℕ) (i : Fin N) : AddCircle L :=
  ↑(((i : ℝ) + 1 / 2) * L / N)

theorem centre_eq (L : ℝ) (N : ℕ) :
    centre L N = LeanMachine.CircleGridCapacity.centre L (L / (2 * N)) N := by
  funext i
  unfold centre LeanMachine.CircleGridCapacity.centre
  congr 1
  ring

/-- Uniform capacity of `m` balls enlarged by a partition width. -/
def capacity (L R : ℝ) (N m : ℕ) : ℕ :=
  min N (m * (⌊2 * R * N / L⌋₊ + 1))

/-- Any positive partition width and any nonnegative charge dominating
every slot's step give a valid query-type bound. -/
theorem movement_of_charge {ι : Type*} [Fintype ι]
    {L ρ δ : ℝ} {N n k : ℕ} (hL : 0 < L) (hN : 0 < N)
    (hρ : 0 ≤ ρ) (hδ : 0 < δ)
    (S : ℕ → Finset (Fin N)) (Y : ι → ℕ → AddCircle L) (w : ℕ → ℝ)
    (hw : ∀ e < n, 0 ≤ w e)
    (hstep : ∀ i, ∀ e < n, dist (Y i e) (Y i (e + 1)) ≤ w e)
    (hsize : ∀ t ≤ n, (S t).card = k)
    (hcover : ∀ t ≤ n, ∀ a ∈ S t, ∃ i, dist (centre L N a) (Y i t) ≤ ρ) :
    ((range (n + 1)).image S).card ≤ (⌊elapsed w n / δ⌋₊ + 1) *
      (capacity L (ρ + δ) N (Fintype.card ι)).choose k := by
  apply card_types_le_charge S (centre L N) Y w n k _ ρ δ hδ hw hstep hsize hcover
  intro y
  rw [centre_eq]
  exact LeanMachine.CircleGridCapacity.card_covered_le L (L / (2 * N)) N hL hN y
    (ρ + δ) (by positivity)

/-- The complete finite theorem, with the sharper maximum-slot bill.
`n + 1` is the number of queries, so the sequence is nonempty. The theorem
also allows empty query types (`k = 0`). -/
theorem movement_max {ι : Type*} [Fintype ι] [Nonempty ι]
    {L ρ : ℝ} {N n k : ℕ} (hL : 0 < L) (hN : 0 < N) (hρ : 0 < ρ)
    (S : ℕ → Finset (Fin N)) (Y : ι → ℕ → AddCircle L)
    (hsize : ∀ t ≤ n, (S t).card = k)
    (hcover : ∀ t ≤ n, ∀ a ∈ S t, ∃ i, dist (centre L N a) (Y i t) ≤ ρ) :
    let F := ((range (n + 1)).image S).card
    let C := elapsed (maxStep Y) n
    let lam := ρ / L
    let s := min N (Fintype.card ι * (⌊5 * lam * N / 2⌋₊ + 1))
    let B := s.choose k
    C ≤ variation Y n ∧ F ≤ (⌊4 * C / ρ⌋₊ + 1) * B ∧ 0 < B ∧
      (F : ℝ) ≤ (1 + 4 * (C / L) / lam) * B ∧
      lam / 4 * ((F : ℝ) / B - 1) ≤ C / L := by
  dsimp only
  let F := ((range (n + 1)).image S).card
  let C := elapsed (maxStep Y) n
  let B := (min N (Fintype.card ι * (⌊5 * (ρ / L) * N / 2⌋₊ + 1))).choose k
  change C ≤ variation Y n ∧ F ≤ (⌊4 * C / ρ⌋₊ + 1) * B ∧ 0 < B ∧
    (F : ℝ) ≤ (1 + 4 * (C / L) / (ρ / L)) * B ∧
    (ρ / L) / 4 * ((F : ℝ) / B - 1) ≤ C / L
  have hc : 0 ≤ C := elapsed_nonneg (fun e _ => maxStep_nonneg Y e) le_rfl
  have hf : 0 < F := card_pos.mpr (Nonempty.image
    (show (range (n + 1)).Nonempty from ⟨0, by simp⟩) S)
  have h := movement_of_charge hL hN hρ.le (by positivity : 0 < ρ / 4)
    S Y (maxStep Y) (fun e _ => maxStep_nonneg Y e)
    (fun i e _ => step_le_maxStep Y e i) hsize hcover
  have hcap : capacity L (ρ + ρ / 4) N (Fintype.card ι) =
      min N (Fintype.card ι * (⌊5 * (ρ / L) * N / 2⌋₊ + 1)) := by
    unfold capacity
    congr 4
    ring
  rw [hcap] at h
  change F ≤ (⌊C / (ρ / 4)⌋₊ + 1) * B at h
  have hid : C / (ρ / 4) = 4 * C / ρ := by ring
  have hnorm : 4 * (C / L) / (ρ / L) = C / (ρ / 4) := by
    field_simp
  obtain ⟨hb, hcount, hlower⟩ := real_bounds hf hc (by positivity : 0 < ρ / 4) h
  refine ⟨elapsed_maxStep_le_variation Y n, ?_, hb, ?_, ?_⟩
  · simpa only [hid] using h
  · simpa only [hnorm] using hcount
  · convert div_le_div_of_nonneg_right hlower hL.le using 1
    ring

/-- The original sum-of-all-slots theorem follows directly from the stronger
maximum-slot theorem. No ordering restriction on query types is imposed. -/
theorem movement {ι : Type*} [Fintype ι] [Nonempty ι]
    {L ρ : ℝ} {N n k : ℕ} (hL : 0 < L) (hN : 0 < N) (hρ : 0 < ρ)
    (S : ℕ → Finset (Fin N)) (Y : ι → ℕ → AddCircle L)
    (hsize : ∀ t ≤ n, (S t).card = k)
    (hcover : ∀ t ≤ n, ∀ a ∈ S t, ∃ i, dist (centre L N a) (Y i t) ≤ ρ) :
    let F := ((range (n + 1)).image S).card
    let v := variation Y n / L
    let lam := ρ / L
    let B := (min N (Fintype.card ι * (⌊5 * lam * N / 2⌋₊ + 1))).choose k
    0 < B ∧ (F : ℝ) ≤ (1 + 4 * v / lam) * B ∧
      lam / 4 * ((F : ℝ) / B - 1) ≤ v := by
  dsimp only
  obtain ⟨he, _, hb, hc, hl⟩ := movement_max hL hN hρ S Y hsize hcover
  refine ⟨hb, hc.trans ?_, hl.trans ?_⟩
  · gcongr
  · exact div_le_div_of_nonneg_right he hL.le

/-- Ordinary line movement can replace circle movement for lifted paths. -/
theorem movement_line {ι : Type*} [Fintype ι] [Nonempty ι]
    {L ρ : ℝ} {N n k : ℕ} (hL : 0 < L) (hN : 0 < N) (hρ : 0 < ρ)
    (S : ℕ → Finset (Fin N)) (Y : ι → ℕ → ℝ)
    (hsize : ∀ t ≤ n, (S t).card = k)
    (hcover : ∀ t ≤ n, ∀ a ∈ S t, ∃ i,
      dist (centre L N a) (Y i t : AddCircle L) ≤ ρ) :
    let F := ((range (n + 1)).image S).card
    let v := variation Y n / L
    let lam := ρ / L
    let B := (min N (Fintype.card ι * (⌊5 * lam * N / 2⌋₊ + 1))).choose k
    0 < B ∧ (F : ℝ) ≤ (1 + 4 * v / lam) * B ∧
      lam / 4 * ((F : ℝ) / B - 1) ≤ v := by
  dsimp only
  obtain ⟨hb, hc, hl⟩ := movement hL hN hρ S (fun i t => (Y i t : AddCircle L)) hsize hcover
  have he : variation (fun i t => (Y i t : AddCircle L)) n ≤ variation Y n := by
    apply sum_le_sum
    intro i _
    exact sum_le_sum fun e _ => LeanMachine.CircleGridCapacity.dist_coe_le L _ _
  refine ⟨hb, hc.trans ?_, hl.trans ?_⟩
  · gcongr
  · exact div_le_div_of_nonneg_right he hL.le

end
end SourceCovers.QueryMovement
