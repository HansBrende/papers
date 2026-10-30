import GapAreaMemo.Z3DGeometry

set_option autoImplicit false

/-!
# The dyadic sharpness geometry: single shadow steps

Each bank zigzag's two families are identified with the explicit schedules of
its shape, and their shadows are evaluated at the times used by the orbit
chains: the lower family maps a second-rise time at cell `c` to the descent
time at cell `c`, the upper family maps a descent time at cell `c` to the
first-rise time at cell `c`. The exceptions reflect the bank-A descent onto
the second rise of bank B's largest zigzag, and the bank-B descent onto the
landing times.
-/

namespace SourceCovers.Z3D.Index

open Finset Zigzag StairFamilies LeanMachine.ScheduledExcursion

variable {k T : ℕ} {xs : Fin k → ℕ → ℤ} {q : ActualFamily xs T} {head : Fin k}

theorem late_lower_step {σ a f : ℕ} (ha : 0 < a) (hf : 0 < f)
    (hq : IsSchedFamily q head (late σ a f ha hf).Q) {c t : ℕ} (hc : 0 < c) (hca : c < a)
    (h1 : σ + 2 * a + f * c ≤ t) (h2 : t < σ + 2 * a + f * (c + 1)) :
    q.shadow t = σ + 2 * a - c := by
  have h := hq.shadow_between ha ⟨a - c, by omega⟩ (by simp only; omega) (t := t)
    (by show σ + 2 * a + f * (a - (a - c)) ≤ t; rw [show a - (a - c) = c by omega]; exact h1)
    (by show t < σ + 2 * a + f * (a - (a - c - 1)); rw [show a - (a - c - 1) = c + 1 by omega]
        exact h2)
  rw [h]; show σ + a + (a - c) = _; omega

theorem late_upper_step {σ a f : ℕ} (ha : 0 < a) (hf : 0 < f)
    (hq : IsSchedFamily q head (late σ a f ha hf).P) {c : ℕ} (hc : 0 < c) (hca : c < a) :
    q.shadow (σ + 2 * a - c) = σ + c :=
  hq.shadow_exact ha (c := ⟨c, hca⟩) hc

theorem early_lower_step {u cc f : ℕ} (hc : 0 < cc) (hf : 0 < f)
    (hq : IsSchedFamily q head (early u cc f hc hf).Q) {η : ℕ} (h0 : 0 < η) (hη : η < cc) :
    q.shadow (u + f * cc + cc + η) = u + f * cc + cc - η := by
  have h := hq.shadow_exact hc (c := ⟨cc - η, by omega⟩) (by simp only; omega)
  have e1 : (early u cc f hc hf).Q.arrive ⟨cc - η, by omega⟩ = u + f * cc + cc + η := by
    show u + f * cc + 2 * cc - (cc - η) = _; omega
  have e2 : (early u cc f hc hf).Q.depart ⟨cc - η, by omega⟩ = u + f * cc + cc - η := by
    show u + f * cc + (cc - η) = _; omega
  rw [e1, e2] at h
  exact h

theorem early_upper_step {u cc f : ℕ} (hc : 0 < cc) (hf : 0 < f)
    (hq : IsSchedFamily q head (early u cc f hc hf).P) {η : ℕ} (h0 : 0 < η) (hη : η < cc) :
    q.shadow (u + f * cc + cc - η) = u + f * (η + 1) - 1 :=
  hq.shadow_exact hc (c := ⟨η, hη⟩) h0

variable (P : Index)

theorem g_step {ι : ℕ} (h1 : 0 < ι) (h2 : ι < P.hg) : P.gFam.shadow (P.OA - ι) = P.OB + 1 + ι :=
  SourceCovers.NativeExcursion.family_shadow_exact P.gSchedule 3 P.heads_G P.gArrive_lt
    (i := ⟨ι, h2⟩) (by intro h; have := congrArg Fin.val h; simp at this; omega)

theorem e_step {ℓ : ℕ} (h1 : 0 < ℓ) (h2 : ℓ < P.hg) : P.eFam.shadow (P.OB - ℓ) = P.eDepart ℓ :=
  SourceCovers.NativeExcursion.family_shadow_exact P.eSchedule 2 P.heads_E P.eArrive_lt
    (i := ⟨ℓ, h2⟩) (by intro h; have := congrArg Fin.val h; simp at this; omega)

/-! ### Bank families with their shapes -/

theorem idxC_odd {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ P.K) (h : i % 2 = 1) : (i - 1) / 2 < P.NX := by
  have := P.K_eq_NX; omega
theorem idxC_even {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ P.K) (h : i % 2 ≠ 1) : (i - 2) / 2 < P.NY := by
  have := P.K_eq_NY; omega

/-- The upper (`true`) or lower family of bank-C zigzag `C_i`. -/
noncomputable def famC (i : ℕ) (up : Bool) : ActualFamily P.heads P.T :=
  if h : 1 ≤ i ∧ i ≤ P.K then
    if hp : i % 2 = 1 then
      (if up then P.stairX.upper ((i - 1) / 2) (by have := P.idxC_odd h.1 h.2 hp; unfold nX; omega)
       else P.stairX.lower ((i - 1) / 2) (by have := P.idxC_odd h.1 h.2 hp; unfold nX; omega))
    else
      (if up then P.stairY.upper ((i - 2) / 2) (by have := P.idxC_even h.1 h.2 hp; unfold nY; omega)
       else P.stairY.lower ((i - 2) / 2) (by have := P.idxC_even h.1 h.2 hp; unfold nY; omega))
  else P.eFam

theorem famC_sched {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ P.K) :
    (∃ hd, IsSchedFamily (P.famC i true) hd (P.segC (i - 1)).Z.P) ∧
      (∃ hd, IsSchedFamily (P.famC i false) hd (P.segC (i - 1)).Z.Q) := by
  unfold famC
  simp only [dite_eq_left (show 1 ≤ i ∧ i ≤ P.K from ⟨h1, h2⟩)]
  by_cases hp : i % 2 = 1
  · simp only [dite_eq_left hp, ite_true, Bool.false_eq_true, ite_false]
    have hj := P.idxC_odd h1 h2 hp
    have e : P.segX ((i - 1) / 2) = P.segC (i - 1) := by
      rw [P.segX_C hj]; congr 1; omega
    refine ⟨⟨0, ?_⟩, ⟨0, ?_⟩⟩
    · have h := P.stairX.upper_sched ((i - 1) / 2) (by unfold nX; omega)
      rw [e] at h; exact h
    · have h := P.stairX.lower_sched ((i - 1) / 2) (by unfold nX; omega)
      rw [e] at h; exact h
  · simp only [dite_eq_right hp, ite_true, Bool.false_eq_true, ite_false]
    have hj := P.idxC_even h1 h2 hp
    have e : P.segY ((i - 2) / 2) = P.segC (i - 1) := by
      rw [P.segY_C hj]; congr 1; omega
    refine ⟨⟨1, ?_⟩, ⟨1, ?_⟩⟩
    · have h := P.stairY.upper_sched ((i - 2) / 2) (by unfold nY; omega)
      rw [e] at h; exact h
    · have h := P.stairY.lower_sched ((i - 2) / 2) (by unfold nY; omega)
      rw [e] at h; exact h

theorem famC_mem {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ P.K) (up : Bool) : P.famC i up ∈ P.core := by
  unfold famC core
  rw [dite_eq_left ⟨h1, h2⟩]
  simp only [mem_union, mem_image, mem_univ, true_and]
  by_cases hp : i % 2 = 1
  · rw [dite_eq_left hp]
    cases up
    · simp only [Bool.false_eq_true, ite_false]
      exact Or.inl (Or.inl (Or.inr ⟨⟨(i - 1) / 2, by have := P.idxC_odd h1 h2 hp; unfold nX; omega⟩,
        rfl⟩))
    · simp only [ite_true]
      exact Or.inl (Or.inl (Or.inl ⟨⟨(i - 1) / 2, by have := P.idxC_odd h1 h2 hp; unfold nX; omega⟩,
        rfl⟩))
  · rw [dite_eq_right hp]
    cases up
    · simp only [Bool.false_eq_true, ite_false]
      exact Or.inr ⟨⟨(i - 2) / 2, by have := P.idxC_even h1 h2 hp; unfold nY; omega⟩, rfl⟩
    · simp only [ite_true]
      exact Or.inl (Or.inr ⟨⟨(i - 2) / 2, by have := P.idxC_even h1 h2 hp; unfold nY; omega⟩, rfl⟩)

theorem idxB_odd {k : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ P.K) (h : k % 2 = 1) :
    P.NX ≤ P.NX + (P.K - k) / 2 ∧ P.NX + (P.K - k) / 2 < 2 * P.NX ∧
      P.K - 2 * (P.NX + (P.K - k) / 2 - P.NX) = k := by
  have := P.K_eq_NX; have := P.NX_pos; have := P.K_odd; omega
theorem idxB_even {k : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ P.K) (h : k % 2 ≠ 1) :
    P.NY ≤ P.NY + (P.K - 1 - k) / 2 ∧ P.NY + (P.K - 1 - k) / 2 < 2 * P.NY ∧
      P.K - 1 - 2 * (P.NY + (P.K - 1 - k) / 2 - P.NY) = k := by
  have := P.K_eq_NY; have := P.NY_pos; have := P.K_odd; omega

/-- The upper or lower family of bank-B zigzag `Z_k`. -/
noncomputable def famB (k : ℕ) (up : Bool) : ActualFamily P.heads P.T :=
  if h : 1 ≤ k ∧ k ≤ P.K then
    if hp : k % 2 = 1 then
      (if up then P.stairX.upper (P.NX + (P.K - k) / 2)
          (by have := P.idxB_odd h.1 h.2 hp; unfold nX; omega)
       else P.stairX.lower (P.NX + (P.K - k) / 2)
          (by have := P.idxB_odd h.1 h.2 hp; unfold nX; omega))
    else
      (if up then P.stairY.upper (P.NY + (P.K - 1 - k) / 2)
          (by have := P.idxB_even h.1 h.2 hp; unfold nY; omega)
       else P.stairY.lower (P.NY + (P.K - 1 - k) / 2)
          (by have := P.idxB_even h.1 h.2 hp; unfold nY; omega))
  else P.eFam

/-- The upper or lower family of bank-A zigzag `Z_k`. -/
noncomputable def famA (k : ℕ) (up : Bool) : ActualFamily P.heads P.T :=
  if h : 1 ≤ k ∧ k ≤ P.K then
    if hp : k % 2 = 1 then
      (if up then P.stairX.upper (P.NX + (P.NX + (P.K - k) / 2))
          (by have := P.idxB_odd h.1 h.2 hp; unfold nX; omega)
       else P.stairX.lower (P.NX + (P.NX + (P.K - k) / 2))
          (by have := P.idxB_odd h.1 h.2 hp; unfold nX; omega))
    else
      (if up then P.stairY.upper (P.NY + (P.NY + (P.K - 1 - k) / 2))
          (by have := P.idxB_even h.1 h.2 hp; unfold nY; omega)
       else P.stairY.lower (P.NY + (P.NY + (P.K - 1 - k) / 2))
          (by have := P.idxB_even h.1 h.2 hp; unfold nY; omega))
  else P.eFam

theorem famB_sched {k : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ P.K) :
    (∃ hd, IsSchedFamily (P.famB k true) hd (P.segB k).Z.P) ∧
      (∃ hd, IsSchedFamily (P.famB k false) hd (P.segB k).Z.Q) := by
  unfold famB
  simp only [dite_eq_left (show 1 ≤ k ∧ k ≤ P.K from ⟨h1, h2⟩)]
  by_cases hp : k % 2 = 1
  · simp only [dite_eq_left hp, ite_true, Bool.false_eq_true, ite_false]
    have hj := P.idxB_odd h1 h2 hp
    have e : P.segX (P.NX + (P.K - k) / 2) = P.segB k := by
      rw [P.segX_B hj.1 hj.2.1, hj.2.2]
    refine ⟨⟨0, ?_⟩, ⟨0, ?_⟩⟩
    · have h := P.stairX.upper_sched (P.NX + (P.K - k) / 2) (by unfold nX; omega)
      rw [e] at h; exact h
    · have h := P.stairX.lower_sched (P.NX + (P.K - k) / 2) (by unfold nX; omega)
      rw [e] at h; exact h
  · simp only [dite_eq_right hp, ite_true, Bool.false_eq_true, ite_false]
    have hj := P.idxB_even h1 h2 hp
    have e : P.segY (P.NY + (P.K - 1 - k) / 2) = P.segB k := by
      rw [P.segY_B hj.1 hj.2.1, hj.2.2]
    refine ⟨⟨1, ?_⟩, ⟨1, ?_⟩⟩
    · have h := P.stairY.upper_sched (P.NY + (P.K - 1 - k) / 2) (by unfold nY; omega)
      rw [e] at h; exact h
    · have h := P.stairY.lower_sched (P.NY + (P.K - 1 - k) / 2) (by unfold nY; omega)
      rw [e] at h; exact h

theorem famA_sched {k : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ P.K) :
    (∃ hd, IsSchedFamily (P.famA k true) hd (P.segA k).Z.P) ∧
      (∃ hd, IsSchedFamily (P.famA k false) hd (P.segA k).Z.Q) := by
  unfold famA
  simp only [dite_eq_left (show 1 ≤ k ∧ k ≤ P.K from ⟨h1, h2⟩)]
  by_cases hp : k % 2 = 1
  · simp only [dite_eq_left hp, ite_true, Bool.false_eq_true, ite_false]
    have hj := P.idxB_odd h1 h2 hp
    have e : P.segX (P.NX + (P.NX + (P.K - k) / 2)) = P.segA k := by
      rw [P.segX_A (by omega) (by omega)]; congr 1; omega
    refine ⟨⟨0, ?_⟩, ⟨0, ?_⟩⟩
    · have h := P.stairX.upper_sched (P.NX + (P.NX + (P.K - k) / 2)) (by unfold nX; omega)
      rw [e] at h; exact h
    · have h := P.stairX.lower_sched (P.NX + (P.NX + (P.K - k) / 2)) (by unfold nX; omega)
      rw [e] at h; exact h
  · simp only [dite_eq_right hp, ite_true, Bool.false_eq_true, ite_false]
    have hj := P.idxB_even h1 h2 hp
    have e : P.segY (P.NY + (P.NY + (P.K - 1 - k) / 2)) = P.segA k := by
      rw [P.segY_A (by omega) (by omega)]; congr 1; omega
    refine ⟨⟨1, ?_⟩, ⟨1, ?_⟩⟩
    · have h := P.stairY.upper_sched (P.NY + (P.NY + (P.K - 1 - k) / 2)) (by unfold nY; omega)
      rw [e] at h; exact h
    · have h := P.stairY.lower_sched (P.NY + (P.NY + (P.K - 1 - k) / 2)) (by unfold nY; omega)
      rw [e] at h; exact h

theorem famB_mem {k : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ P.K) (up : Bool) : P.famB k up ∈ P.core := by
  unfold famB core
  simp only [dite_eq_left (show 1 ≤ k ∧ k ≤ P.K from ⟨h1, h2⟩), mem_union, mem_image, mem_univ, true_and]
  by_cases hp : k % 2 = 1
  · have hj := P.idxB_odd h1 h2 hp
    simp only [dite_eq_left hp]
    cases up
    · exact Or.inl (Or.inl (Or.inr ⟨⟨_, by unfold nX; omega⟩, rfl⟩))
    · exact Or.inl (Or.inl (Or.inl ⟨⟨_, by unfold nX; omega⟩, rfl⟩))
  · have hj := P.idxB_even h1 h2 hp
    simp only [dite_eq_right hp]
    cases up
    · exact Or.inr ⟨⟨_, by unfold nY; omega⟩, rfl⟩
    · exact Or.inl (Or.inr ⟨⟨_, by unfold nY; omega⟩, rfl⟩)

theorem famA_mem {k : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ P.K) (up : Bool) : P.famA k up ∈ P.core := by
  unfold famA core
  simp only [dite_eq_left (show 1 ≤ k ∧ k ≤ P.K from ⟨h1, h2⟩), mem_union, mem_image, mem_univ, true_and]
  by_cases hp : k % 2 = 1
  · have hj := P.idxB_odd h1 h2 hp
    simp only [dite_eq_left hp]
    cases up
    · exact Or.inl (Or.inl (Or.inr ⟨⟨_, by unfold nX; omega⟩, rfl⟩))
    · exact Or.inl (Or.inl (Or.inl ⟨⟨_, by unfold nX; omega⟩, rfl⟩))
  · have hj := P.idxB_even h1 h2 hp
    simp only [dite_eq_right hp]
    cases up
    · exact Or.inr ⟨⟨_, by unfold nY; omega⟩, rfl⟩
    · exact Or.inl (Or.inr ⟨⟨_, by unfold nY; omega⟩, rfl⟩)

end SourceCovers.Z3D.Index
