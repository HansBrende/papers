import GapAreaMemo.Z3DFamilies

set_option autoImplicit false

/-!
# The dyadic sharpness geometry: span colorings

Bank zigzags occupy global slots in time order: `C_{g+1}` for `g < K`, then
bank B's `Z_k` at slot `2K - k`, then bank A's `Z_k` at slot `3K - k`. The
upper family of slot `g` spans inside `[tP g, tP (g+1))` and the lower family
inside `[tQ g, tQ (g+1))`, for nondecreasing `tP`, `tQ`. Head X holds the slots
of even offset in each bank, head Y those of odd offset.
-/

namespace SourceCovers.Z3D.Index

open Finset Zigzag

variable (P : Index)

def gX (j : ℕ) : ℕ :=
  if j < P.NX then 2 * j else if j < 2 * P.NX then P.K + 2 * (j - P.NX) else 2 * P.K + 2 * (j - 2 * P.NX)

def gY (j : ℕ) : ℕ :=
  if j < P.NY then 2 * j + 1 else if j < 2 * P.NY then P.K + 1 + 2 * (j - P.NY)
  else 2 * P.K + 1 + 2 * (j - 2 * P.NY)

def tP (g : ℕ) : ℕ :=
  if g < P.K then P.U g else if g < 2 * P.K then P.σB (2 * P.K - g) else P.σA (3 * P.K - g)

def tQ (g : ℕ) : ℕ :=
  if g < P.K then P.U g + fC (g + 1) * P.cc (g + 1)
  else if g < 2 * P.K then P.σB (2 * P.K - g) + P.a (2 * P.K - g)
  else if g < 3 * P.K then P.σA (3 * P.K - g) + P.a (3 * P.K - g)
  else P.OA + P.L

theorem gX_ne_gY {j j' : ℕ} (hj : j < P.nX) (_hj' : j' < P.nY) : P.gX j ≠ P.gY j' := by
  have h1 := P.K_eq_NX; have h2 := P.K_eq_NY
  unfold gX gY nX nY at *
  split_ifs <;> omega

theorem gX_inj {j j' : ℕ} (_hj : j < P.nX) (_hj' : j' < P.nX) (h : P.gX j = P.gX j') : j = j' := by
  have h1 := P.K_eq_NX
  unfold gX nX at *
  split_ifs at h <;> omega

theorem gY_inj {j j' : ℕ} (_hj : j < P.nY) (_hj' : j' < P.nY) (h : P.gY j = P.gY j') : j = j' := by
  have h1 := P.K_eq_NY
  unfold gY nY at *
  split_ifs at h <;> omega

theorem tP_succ (g : ℕ) : P.tP g ≤ P.tP (g + 1) := by
  have hK := P.K_pos
  unfold tP
  split_ifs with h1 h2 h3 h4 h5 h6
  all_goals first
    | omega
    | skip
  · exact P.U_mono (by omega)
  · have := P.U_le_endC (j := g) (by omega); have := P.endC_le_σB
    rw [show 2 * P.K - (g + 1) = P.K by omega]; omega
  · rw [show 2 * P.K - g = (2 * P.K - (g + 1)) + 1 by omega]
    have := P.σB_lt_pred (k := 2 * P.K - (g + 1) + 1) (by omega) (by omega)
    simp only [Nat.add_sub_cancel] at this; omega
  · have := P.σB_le_OB (k := 2 * P.K - g)
    have := P.OB_lt_σA (k := 3 * P.K - (g + 1)); omega
  · by_cases h : 3 * P.K - g = 0
    · rw [h, show 3 * P.K - (g + 1) = 0 by omega]
    · rw [show 3 * P.K - g = (3 * P.K - (g + 1)) + 1 by omega]
      have := P.σA_lt_pred (k := 3 * P.K - (g + 1) + 1) (by omega) (by omega)
      simp only [Nat.add_sub_cancel] at this; omega

theorem tP_mono {g g' : ℕ} (h : g ≤ g') : P.tP g ≤ P.tP g' := by
  induction g', h using Nat.le_induction with
  | base => exact le_rfl
  | succ g' _ ih => exact ih.trans (P.tP_succ g')

theorem tQ_succ (g : ℕ) : P.tQ g ≤ P.tQ (g + 1) := by
  have hK := P.K_pos
  have hU : P.U (g + 1) = P.U g + fC (g + 1) * P.cc (g + 1) + P.cc (g + 1) := rfl
  unfold tQ
  by_cases h1 : g + 1 < P.K
  · rw [ite_eq_left (by omega), ite_eq_left h1]
    have := fC_mul P (k := g + 2) (by omega) (by omega)
    simp only [show g + 2 - 1 = g + 1 by omega] at this
    rw [show g + 1 + 1 = g + 2 by ring, this]
    omega
  by_cases h2 : g < P.K
  · rw [ite_eq_left h2, ite_eq_right h1, ite_eq_left (by omega), show 2 * P.K - (g + 1) = P.K by omega]
    have := P.U_le_endC (j := g + 1) (by omega); have := P.endC_le_σB
    omega
  rw [ite_eq_right h2, ite_eq_right h1]
  by_cases h3 : g + 1 < 2 * P.K
  · rw [ite_eq_left (by omega), ite_eq_left h3,
      show 2 * P.K - g = (2 * P.K - (g + 1)) + 1 by omega]
    have := P.σB_pred (k := 2 * P.K - (g + 1) + 1) (by omega) (by omega)
    simp only [Nat.add_sub_cancel] at this
    omega
  by_cases h4 : g < 2 * P.K
  · rw [ite_eq_left h4, ite_eq_right h3, ite_eq_left (by omega), show 2 * P.K - g = 1 by omega,
      show 3 * P.K - (g + 1) = P.K by omega]
    have := P.σB_one_lt_OB; have := P.OB_lt_σA (k := P.K); omega
  rw [ite_eq_right h4, ite_eq_right h3]
  by_cases h5 : g + 1 < 3 * P.K
  · rw [ite_eq_left (by omega), ite_eq_left h5,
      show 3 * P.K - g = (3 * P.K - (g + 1)) + 1 by omega]
    have := P.σA_pred (k := 3 * P.K - (g + 1) + 1) (by omega) (by omega)
    simp only [Nat.add_sub_cancel] at this
    omega
  by_cases h6 : g < 3 * P.K
  · rw [ite_eq_left h6, ite_eq_right h5, show 3 * P.K - g = 1 by omega]
    have := P.σA_one_lt_OA; omega
  rw [ite_eq_right h6, ite_eq_right h5]

theorem tQ_mono {g g' : ℕ} (h : g ≤ g') : P.tQ g ≤ P.tQ g' := by
  induction g', h using Nat.le_induction with
  | base => exact le_rfl
  | succ g' _ ih => exact ih.trans (P.tQ_succ g')

/-! ### Span bounds of the segments -/

theorem segC_trough (j : ℕ) : (P.segC j).Z.trough = P.U (j + 1) := by
  simp only [segC]; rw [early_trough]; rfl
theorem segC_peak (j : ℕ) : (P.segC j).Z.P.peak = P.U j + fC (j + 1) * P.cc (j + 1) := by
  simp only [segC]; rw [early_peak]
theorem segB_trough (k : ℕ) : (P.segB k).Z.trough = P.σB k + 2 * P.a k := by
  simp only [segB]; rw [late_trough]
theorem segB_peak (k : ℕ) : (P.segB k).Z.P.peak = P.σB k + P.a k := by
  simp only [segB]; rw [late_peak]
theorem segA_trough (k : ℕ) : (P.segA k).Z.trough = P.σA k + 2 * P.a k := by
  simp only [segA]; rw [late_trough]
theorem segA_peak (k : ℕ) : (P.segA k).Z.P.peak = P.σA k + P.a k := by
  simp only [segA]; rw [late_peak]

theorem tP_C {g : ℕ} (h : g < P.K) : P.tP g = P.U g := by unfold tP; rw [ite_eq_left h]
theorem tP_B {g : ℕ} (h1 : P.K ≤ g) (h2 : g < 2 * P.K) : P.tP g = P.σB (2 * P.K - g) := by
  unfold tP; rw [ite_eq_right (by omega), ite_eq_left h2]
theorem tP_A {g : ℕ} (h1 : 2 * P.K ≤ g) : P.tP g = P.σA (3 * P.K - g) := by
  unfold tP; rw [ite_eq_right (by omega), ite_eq_right (by omega)]
theorem tQ_C {g : ℕ} (h : g < P.K) : P.tQ g = P.U g + fC (g + 1) * P.cc (g + 1) := by
  unfold tQ; rw [ite_eq_left h]
theorem tQ_B {g : ℕ} (h1 : P.K ≤ g) (h2 : g < 2 * P.K) :
    P.tQ g = P.σB (2 * P.K - g) + P.a (2 * P.K - g) := by
  unfold tQ; rw [ite_eq_right (by omega), ite_eq_left h2]
theorem tQ_A {g : ℕ} (h1 : 2 * P.K ≤ g) (h2 : g < 3 * P.K) :
    P.tQ g = P.σA (3 * P.K - g) + P.a (3 * P.K - g) := by
  unfold tQ; rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left h2]
theorem tQ_end : P.tQ (3 * P.K) = P.OA + P.L := by
  unfold tQ; rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

/-- Bounds of a bank-C segment at slot `i - 1` (zigzag `C_i`). -/
theorem slotC_bounds {i : ℕ} (hi : i + 1 ≤ P.K) :
    P.tP i ≤ P.U i ∧ (P.segC i).Z.trough ≤ P.tP (i + 1) ∧
      P.tQ i ≤ (P.segC i).Z.P.peak ∧ (P.segC i).finish ≤ P.tQ (i + 1) := by
  refine ⟨by rw [P.tP_C (by omega)], ?_, by rw [P.tQ_C (by omega), P.segC_peak], ?_⟩
  · rw [P.segC_trough]
    rcases Nat.lt_or_ge (i + 1) P.K with h | h
    · rw [P.tP_C h]
    · rw [P.tP_B (by omega) (by have := P.K_pos; omega), show 2 * P.K - (i + 1) = P.K by omega]
      have := P.U_le_endC (j := i + 1) (by omega); have := P.endC_le_σB; omega
  · rw [P.segC_finish]
    rcases Nat.lt_or_ge (i + 1) P.K with h | h
    · rw [P.tQ_C h]
      have := fC_mul P (k := i + 2) (by omega) (by omega)
      simp only [show i + 2 - 1 = i + 1 by omega] at this
      rw [show i + 1 + 1 = i + 2 by ring, this]
    · rw [P.tQ_B (by omega) (by have := P.K_pos; omega), show 2 * P.K - (i + 1) = P.K by omega]
      have h1 : i + 1 = P.K := by omega
      rw [h1]
      have := P.endC_le_σB; unfold endC at this; omega

/-- Bounds of a bank-B segment at slot `2K - k`. -/
theorem slotB_bounds {k : ℕ} (hk : 1 ≤ k) (hK : k ≤ P.K) :
    P.tP (2 * P.K - k) ≤ P.σB k ∧ (P.segB k).Z.trough ≤ P.tP (2 * P.K - k + 1) ∧
      P.tQ (2 * P.K - k) ≤ (P.segB k).Z.P.peak ∧ (P.segB k).finish ≤ P.tQ (2 * P.K - k + 1) := by
  refine ⟨by rw [P.tP_B (by omega) (by omega), show 2 * P.K - (2 * P.K - k) = k by omega], ?_,
    by rw [P.tQ_B (by omega) (by omega), show 2 * P.K - (2 * P.K - k) = k by omega, P.segB_peak],
    ?_⟩
  · rw [P.segB_trough]
    rcases Nat.lt_or_ge 1 k with h | h
    · rw [P.tP_B (by omega) (by omega), show 2 * P.K - (2 * P.K - k + 1) = k - 1 by omega,
        P.σB_pred (by omega) hK]
    · rw [P.tP_A (by omega), show k = 1 by omega]
      have := P.σB_pred (k := 1) le_rfl P.K_pos
      simp only [Nat.sub_self] at this
      have := P.OB_lt_σA (k := 3 * P.K - (2 * P.K - 1 + 1)); unfold OB at *; omega
  · rcases Nat.lt_or_ge 1 k with h | h
    · rw [P.tQ_B (by omega) (by omega), show 2 * P.K - (2 * P.K - k + 1) = k - 1 by omega]
      have := P.segB_finish_le (k := k) (by omega) hK
      have := P.σB_pred (k := k) (by omega) hK
      rw [P.segB_finish, P.fB_mul (by omega) hK]; omega
    · rw [show k = 1 by omega, P.segB_one_finish, P.tQ_A (by omega) (by omega),
        show 3 * P.K - (2 * P.K - 1 + 1) = P.K by omega]
      have := P.OB_lt_σA (k := P.K); omega

/-- Bounds of a bank-A segment at slot `3K - k`. -/
theorem slotA_bounds {k : ℕ} (hk : 1 ≤ k) (hK : k ≤ P.K) :
    P.tP (3 * P.K - k) ≤ P.σA k ∧ (P.segA k).Z.trough ≤ P.tP (3 * P.K - k + 1) ∧
      P.tQ (3 * P.K - k) ≤ (P.segA k).Z.P.peak ∧ (P.segA k).finish ≤ P.tQ (3 * P.K - k + 1) := by
  refine ⟨by rw [P.tP_A (by omega), show 3 * P.K - (3 * P.K - k) = k by omega], ?_,
    by rw [P.tQ_A (by omega) (by omega), show 3 * P.K - (3 * P.K - k) = k by omega, P.segA_peak],
    ?_⟩
  · rw [P.segA_trough, P.tP_A (by omega), show 3 * P.K - (3 * P.K - k + 1) = k - 1 by omega,
      P.σA_pred hk hK]
  · rcases Nat.lt_or_ge 1 k with h | h
    · rw [P.tQ_A (by omega) (by omega), show 3 * P.K - (3 * P.K - k + 1) = k - 1 by omega]
      have := P.σA_pred (k := k) (by omega) hK
      rw [P.segA_finish, P.fB_mul (by omega) hK]; omega
    · rw [show k = 1 by omega, P.segA_one_finish, show 3 * P.K - 1 + 1 = 3 * P.K by omega,
        P.tQ_end]

/-- Slot bounds of the segments of head X. -/
theorem slotX_bounds {j : ℕ} (hj : j < P.nX) :
    P.tP (P.gX j) ≤ P.startX j ∧ (P.segX j).Z.trough ≤ P.tP (P.gX j + 1) ∧
      P.tQ (P.gX j) ≤ (P.segX j).Z.P.peak ∧ (P.segX j).finish ≤ P.tQ (P.gX j + 1) := by
  have hK := P.K_eq_NX; have hN := P.NX_pos
  unfold nX at hj
  rcases Nat.lt_or_ge j P.NX with h1 | h1
  · rw [P.segX_C h1, P.startX_C h1, show P.gX j = 2 * j by unfold gX; rw [ite_eq_left h1]]
    exact P.slotC_bounds (by omega)
  rcases Nat.lt_or_ge j (2 * P.NX) with h2 | h2
  · rw [P.segX_B h1 h2, P.startX_B h1 h2, show P.gX j = 2 * P.K - (P.K - 2 * (j - P.NX)) by
      unfold gX; rw [ite_eq_right (by omega), ite_eq_left h2]; omega]
    exact P.slotB_bounds (by omega) (by omega)
  · rw [P.segX_A h2 hj, P.startX_A h2 hj, show P.gX j = 3 * P.K - (P.K - 2 * (j - 2 * P.NX)) by
      unfold gX; rw [ite_eq_right (by omega), ite_eq_right (by omega)]; omega]
    exact P.slotA_bounds (by omega) (by omega)

/-- Slot bounds of the segments of head Y. -/
theorem slotY_bounds {j : ℕ} (hj : j < P.nY) :
    P.tP (P.gY j) ≤ P.startY j ∧ (P.segY j).Z.trough ≤ P.tP (P.gY j + 1) ∧
      P.tQ (P.gY j) ≤ (P.segY j).Z.P.peak ∧ (P.segY j).finish ≤ P.tQ (P.gY j + 1) := by
  have hK := P.K_eq_NY; have hN := P.NY_pos
  unfold nY at hj
  rcases Nat.lt_or_ge j P.NY with h1 | h1
  · rw [P.segY_C h1, P.startY_C h1, show P.gY j = 2 * j + 1 by unfold gY; rw [ite_eq_left h1]]
    exact P.slotC_bounds (by omega)
  rcases Nat.lt_or_ge j (2 * P.NY) with h2 | h2
  · rw [P.segY_B h1 h2, P.startY_B h1 h2, show P.gY j = 2 * P.K - (P.K - 1 - 2 * (j - P.NY)) by
      unfold gY; rw [ite_eq_right (by omega), ite_eq_left h2]; omega]
    exact P.slotB_bounds (by omega) (by omega)
  · rw [P.segY_A h2 hj, P.startY_A h2 hj, show P.gY j = 3 * P.K - (P.K - 1 - 2 * (j - 2 * P.NY)) by
      unfold gY; rw [ite_eq_right (by omega), ite_eq_right (by omega)]; omega]
    exact P.slotA_bounds (by omega) (by omega)

/-! ### The colorings -/

theorem disjoint_of_slots {f : ℕ → ℕ} (hf : Monotone f) {A B : Finset ℕ} {g g' : ℕ}
    (hA : A ⊆ Ico (f g) (f (g + 1))) (hB : B ⊆ Ico (f g') (f (g' + 1))) (hne : g ≠ g') :
    Disjoint A B := by
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · refine Disjoint.mono hA hB ?_
    rw [disjoint_left]; intro e h1 h2
    have := hf (show g + 1 ≤ g' by omega)
    simp only [mem_Ico] at h1 h2; omega
  · refine Disjoint.mono hA hB ?_
    rw [disjoint_left]; intro e h1 h2
    have := hf (show g' + 1 ≤ g by omega)
    simp only [mem_Ico] at h1 h2; omega

theorem upperX_edges {j : ℕ} (hj : j < P.nX) :
    (P.stairX.upper j hj).edges ⊆ Ico (P.tP (P.gX j)) (P.tP (P.gX j + 1)) := by
  have hb := P.slotX_bounds hj
  unfold ActualFamily.edges
  rw [P.stairX.upper_start, P.stairX.upper_stop_eq_trough]
  exact Ico_subset_Ico (hb.1.trans (P.stairX.start_le_depart j _)) hb.2.1

theorem lowerX_edges {j : ℕ} (hj : j < P.nX) :
    (P.stairX.lower j hj).edges ⊆ Ico (P.tQ (P.gX j)) (P.tQ (P.gX j + 1)) := by
  have hb := P.slotX_bounds hj
  unfold ActualFamily.edges
  rw [P.stairX.lower_start_eq_peak, P.stairX.lower_stop_eq_finish]
  exact Ico_subset_Ico hb.2.2.1 hb.2.2.2

theorem upperY_edges {j : ℕ} (hj : j < P.nY) :
    (P.stairY.upper j hj).edges ⊆ Ico (P.tP (P.gY j)) (P.tP (P.gY j + 1)) := by
  have hb := P.slotY_bounds hj
  unfold ActualFamily.edges
  rw [P.stairY.upper_start, P.stairY.upper_stop_eq_trough]
  exact Ico_subset_Ico (hb.1.trans (P.stairY.start_le_depart j _)) hb.2.1

theorem lowerY_edges {j : ℕ} (hj : j < P.nY) :
    (P.stairY.lower j hj).edges ⊆ Ico (P.tQ (P.gY j)) (P.tQ (P.gY j + 1)) := by
  have hb := P.slotY_bounds hj
  unfold ActualFamily.edges
  rw [P.stairY.lower_start_eq_peak, P.stairY.lower_stop_eq_finish]
  exact Ico_subset_Ico hb.2.2.1 hb.2.2.2

theorem core_cases {q : ActualFamily P.heads P.T} (hq : q ∈ P.core) :
    (∃ j, ∃ hj : j < P.nX, q = P.stairX.upper j hj) ∨ (∃ j, ∃ hj : j < P.nX, q = P.stairX.lower j hj) ∨
    (∃ j, ∃ hj : j < P.nY, q = P.stairY.upper j hj) ∨ (∃ j, ∃ hj : j < P.nY, q = P.stairY.lower j hj) := by
  simp only [core, mem_union, mem_image, mem_univ, true_and] at hq
  rcases hq with ((⟨j, rfl⟩ | ⟨j, rfl⟩) | ⟨j, rfl⟩) | ⟨j, rfl⟩
  · exact Or.inl ⟨j, j.isLt, rfl⟩
  · exact Or.inr (Or.inl ⟨j, j.isLt, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨j, j.isLt, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨j, j.isLt, rfl⟩))

/-- The side of a family: upper or lower. -/
def sideColor (q : ActualFamily P.heads P.T) : ℕ := if q.1.2.1 then 0 else 1

theorem core_disjoint_of_color {q q' : ActualFamily P.heads P.T} (hq : q ∈ P.core)
    (hq' : q' ∈ P.core) (hne : q ≠ q') (hc : P.sideColor q = P.sideColor q') :
    Disjoint q.edges q'.edges := by
  have hPm : Monotone P.tP := fun _ _ h => P.tP_mono h
  have hQm : Monotone P.tQ := fun _ _ h => P.tQ_mono h
  rcases P.core_cases hq with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ <;>
  rcases P.core_cases hq' with ⟨j', hj', rfl⟩ | ⟨j', hj', rfl⟩ | ⟨j', hj', rfl⟩ | ⟨j', hj', rfl⟩ <;>
  simp only [sideColor, StairFamilies.Stair.upper_val, StairFamilies.Stair.lower_val] at hc <;>
  (try simp at hc)
  · exact disjoint_of_slots hPm (P.upperX_edges hj) (P.upperX_edges hj') (fun h =>
      hne (by obtain rfl := P.gX_inj hj hj' h; rfl))
  · exact disjoint_of_slots hPm (P.upperX_edges hj) (P.upperY_edges hj') (P.gX_ne_gY hj hj')
  · exact disjoint_of_slots hQm (P.lowerX_edges hj) (P.lowerX_edges hj') (fun h =>
      hne (by obtain rfl := P.gX_inj hj hj' h; rfl))
  · exact disjoint_of_slots hQm (P.lowerX_edges hj) (P.lowerY_edges hj') (P.gX_ne_gY hj hj')
  · exact disjoint_of_slots hPm (P.upperY_edges hj) (P.upperX_edges hj')
      (fun h => P.gX_ne_gY hj' hj h.symm)
  · exact disjoint_of_slots hPm (P.upperY_edges hj) (P.upperY_edges hj') (fun h =>
      hne (by obtain rfl := P.gY_inj hj hj' h; rfl))
  · exact disjoint_of_slots hQm (P.lowerY_edges hj) (P.lowerX_edges hj')
      (fun h => P.gX_ne_gY hj' hj h.symm)
  · exact disjoint_of_slots hQm (P.lowerY_edges hj) (P.lowerY_edges hj') (fun h =>
      hne (by obtain rfl := P.gY_inj hj hj' h; rfl))

theorem core_coloring : HasSpanColoring P.core 2 :=
  ⟨P.sideColor, fun q _ => by unfold sideColor; split_ifs <;> omega,
    fun q hq q' hq' hne hc => P.core_disjoint_of_color hq hq' hne hc⟩

theorem eFam_edges : P.eFam.edges = Ico 0 P.OB := by
  unfold ActualFamily.edges eFam
  rw [SourceCovers.NativeExcursion.family_start, SourceCovers.NativeExcursion.family_stop]
  show Ico (P.eDepart (0 : Fin P.hg).val) (P.OB - (0 : Fin P.hg).val) = Ico 0 P.OB
  simp [eDepart]

theorem gFam_edges : P.gFam.edges = Ico (P.OB + 1) P.OA := by
  unfold ActualFamily.edges gFam
  rw [SourceCovers.NativeExcursion.family_start, SourceCovers.NativeExcursion.family_stop]
  show Ico (P.OB + 1 + (0 : Fin P.hg).val) (P.OA - (0 : Fin P.hg).val) = Ico (P.OB + 1) P.OA
  simp

/-- Colour 2 for the exceptions, the side for bank families. -/
def fullColor (q : ActualFamily P.heads P.T) : ℕ :=
  if q.1.1 = 2 ∨ q.1.1 = 3 then 2 else P.sideColor q

theorem full_coloring : HasSpanColoring (univ : Finset (ActualFamily P.heads P.T)) 3 := by
  refine ⟨P.fullColor, fun q _ => by unfold fullColor sideColor; split_ifs <;> omega, ?_⟩
  intro q _ q' _ hne hc
  have hheadcore : ∀ r ∈ P.core, ¬ (r.1.1 = 2 ∨ r.1.1 = 3) := by
    intro r hr h
    rcases P.mem_core_head hr with h' | h' <;> rw [h'] at h <;> simp at h
  rcases P.family_mem q with hq | rfl | rfl <;> rcases P.family_mem q' with hq' | rfl | rfl
  · unfold fullColor at hc
    rw [ite_eq_right (hheadcore q hq), ite_eq_right (hheadcore q' hq')] at hc
    exact P.core_disjoint_of_color hq hq' hne hc
  · exfalso; unfold fullColor at hc
    rw [ite_eq_right (hheadcore q hq), ite_eq_left (Or.inl P.eFam_head)] at hc
    unfold sideColor at hc; split_ifs at hc; omega
  · exfalso; unfold fullColor at hc
    rw [ite_eq_right (hheadcore q hq), ite_eq_left (Or.inr P.gFam_head)] at hc
    unfold sideColor at hc; split_ifs at hc; omega
  · exfalso; unfold fullColor at hc
    rw [ite_eq_right (hheadcore q' hq'), ite_eq_left (Or.inl P.eFam_head)] at hc
    unfold sideColor at hc; split_ifs at hc; omega
  · exact absurd rfl hne
  · rw [P.eFam_edges, P.gFam_edges, disjoint_left]
    intro e h1 h2; simp only [mem_Ico] at h1 h2; omega
  · exfalso; unfold fullColor at hc
    rw [ite_eq_right (hheadcore q' hq'), ite_eq_left (Or.inr P.gFam_head)] at hc
    unfold sideColor at hc; split_ifs at hc; omega
  · rw [P.eFam_edges, P.gFam_edges, disjoint_left]
    intro e h1 h2; simp only [mem_Ico] at h1 h2; omega
  · exact absurd rfl hne

end SourceCovers.Z3D.Index
