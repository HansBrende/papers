import Transpose.Tape.PlainRobust.CEVote
import Transpose.Tape.CESweep

/-!
# Selection among candidate codes: the diagram

`selDiagram D K P r L` is built from `K` copies of `D` plus one fresh copy, on `(K + 1) k` tapes.
* **Run 1** (slots `< ⌈T/r⌉`): copies `0, …, K-1` of the work walks follow `D`'s walks, and are parked
  from the end of slot `⌈T/r⌉ - 1` on; the input walk is `D`'s.
* **Epilogue** (slots `⌈T/r⌉ ≤ y < P`): the input head walks to cell `0`, sweeps `[0, L)` and returns
  to `0` (`epiWalk`).
* **Run 2** (slots `≥ P`): copy `K` of the work walks is `D`'s, delayed by `P r` steps (parked at `0`
  before), and so are the input walk and the output schedule. Nothing is output before.

The block network (block size `r`):
* in run 1 every copy has at least `D`'s residencies and chords (`pairRes_sel_run1`, `isChord_sel_run1`),
  so the capacities there are at least `K` times `D`'s;
* run 2 is `D`'s network shifted by `P` (`isChord_sel_run2`, `rowsAt_sel_add`, `outNode_sel`);
* no chord goes from slots `< P` to slots `≥ P` (`sel_edge_into_run2`);
* the epilogue attaches every row (`row_mem_epi`).
-/

namespace Transpose.Tape.Impl

open Transpose TSDiagram

/-! ### Parked walks -/

section Park

variable {r : ℕ}

/-- The walk `h` up to time `T₀`, then parked. -/
def parkWalk (T₀ : ℕ) (h : ℕ → ℤ) (τ : ℕ) : ℤ := h (min τ T₀)

theorem parkWalk_of_le {T₀ : ℕ} (h : ℕ → ℤ) {τ : ℕ} (hτ : τ ≤ T₀) : parkWalk T₀ h τ = h τ := by
  unfold parkWalk; rw [min_eq_left hτ]

theorem parkWalk_of_ge {T₀ : ℕ} (h : ℕ → ℤ) {τ : ℕ} (hτ : T₀ ≤ τ) : parkWalk T₀ h τ = h T₀ := by
  unfold parkWalk; rw [min_eq_right hτ]

theorem unitSteps_parkWalk {T₀ : ℕ} {h : ℕ → ℤ} (hh : UnitSteps h) : UnitSteps (parkWalk T₀ h) := by
  intro τ
  by_cases h1 : τ + 1 ≤ T₀
  · rw [parkWalk_of_le h h1, parkWalk_of_le h (by omega)]; exact hh τ
  · rw [parkWalk_of_ge h (by omega), parkWalk_of_ge h (by omega)]; simp

/-- The resident pair at time `τ` depends only on the walk up to `τ`. -/
theorem residentPair_congr {h h' : ℕ → ℤ} : ∀ τ, (∀ σ ≤ τ, h σ = h' σ) →
    residentPair r h τ = residentPair r h' τ := by
  intro τ
  induction τ with
  | zero =>
    intro hh
    unfold residentPair
    rw [prevBlock_zero, prevBlock_zero]
    simp only [curBlock, hh 0 le_rfl]
  | succ τ ih =>
    intro hh
    have e1 : curBlock r h (τ + 1) = curBlock r h' (τ + 1) := by
      simp only [curBlock, hh (τ + 1) le_rfl]
    have e2 : curBlock r h τ = curBlock r h' τ := by
      simp only [curBlock, hh τ (by omega)]
    rw [residentPair_succ (h := h), residentPair_succ (h := h'), ih (fun σ hσ => hh σ (by omega)),
      e1, e2]

/-- A parked walk keeps its resident pair. -/
theorem residentPair_park {T₀ : ℕ} (h : ℕ → ℤ) : ∀ j,
    residentPair r (parkWalk T₀ h) (T₀ + j) = residentPair r (parkWalk T₀ h) T₀ := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [show T₀ + (j + 1) = T₀ + j + 1 by omega, residentPair_succ]
    have e : curBlock r (parkWalk T₀ h) (T₀ + j + 1) = curBlock r (parkWalk T₀ h) (T₀ + j) := by
      simp only [curBlock, parkWalk_of_ge h (show T₀ ≤ T₀ + j + 1 by omega),
        parkWalk_of_ge h (show T₀ ≤ T₀ + j by omega)]
    rw [ite_eq_right (not_not.2 e), ih]

/-- Residencies agree on a slot if the walks agree up to its end. -/
theorem pairRes_congr {h h' : ℕ → ℤ} {T T' y : ℕ} (hT : y * r + r ≤ T) (hT' : y * r + r ≤ T')
    (hh : ∀ σ < y * r + r, h σ = h' σ) : pairRes r h T y = pairRes r h' T' y := by
  ext β
  rw [mem_pairRes, mem_pairRes]
  constructor
  · rintro ⟨τ, h1, h2, h3, h4⟩
    refine ⟨τ, h1, h2, by omega, ?_⟩
    rwa [← residentPair_congr τ (fun σ hσ => hh σ (by omega))]
  · rintro ⟨τ, h1, h2, h3, h4⟩
    refine ⟨τ, h1, h2, by omega, ?_⟩
    rwa [residentPair_congr τ (fun σ hσ => hh σ (by omega))]

/-- Residencies can only grow when the horizon grows and the walks agree before the old horizon. -/
theorem pairRes_sub_of_agree {h h' : ℕ → ℤ} {T T' : ℕ} (hTT : T ≤ T')
    (hh : ∀ σ < T, h σ = h' σ) (y : ℕ) : pairRes r h T y ⊆ pairRes r h' T' y := by
  intro β hβ
  rw [mem_pairRes] at hβ ⊢
  obtain ⟨τ, h1, h2, h3, h4⟩ := hβ
  refine ⟨τ, h1, h2, by omega, ?_⟩
  rwa [← residentPair_congr τ (fun σ hσ => hh σ (by omega))]

/-- A parked walk has a constant residency after the parking time. -/
theorem pairRes_park {T₀ T y : ℕ} (h : ℕ → ℤ) (hy : T₀ ≤ y * r) (hyT : y * r < T) (hr : 1 ≤ r) :
    pairRes r (parkWalk T₀ h) T y = residentPair r (parkWalk T₀ h) T₀ := by
  ext β
  rw [mem_pairRes]
  constructor
  · rintro ⟨τ, h1, -, -, h4⟩
    have e : τ = T₀ + (τ - T₀) := by omega
    rwa [e, residentPair_park] at h4
  · intro hβ
    refine ⟨y * r, le_rfl, by omega, hyT, ?_⟩
    have e : y * r = T₀ + (y * r - T₀) := by omega
    rwa [e, residentPair_park]

end Park

/-! ### The epilogue walk -/

/-- From `p₀` to cell `0`, then the sweep `0 → L - 1 → 0`, then waiting at `0`. -/
def epiWalk (p₀ : ℤ) (L s : ℕ) : ℤ :=
  if s ≤ p₀.natAbs then (if 0 ≤ p₀ then p₀ - s else p₀ + s) else sweepPos L (s - p₀.natAbs)

theorem epiWalk_zero (p₀ : ℤ) (L : ℕ) : epiWalk p₀ L 0 = p₀ := by
  unfold epiWalk; split_ifs <;> omega

theorem epiWalk_step (p₀ : ℤ) (L s : ℕ) : |epiWalk p₀ L (s + 1) - epiWalk p₀ L s| ≤ 1 := by
  unfold epiWalk
  by_cases h1 : s + 1 ≤ p₀.natAbs
  · rw [ite_eq_left h1, ite_eq_left (show s ≤ p₀.natAbs by omega)]
    rw [abs_le]
    split_ifs <;> constructor <;> omega
  · by_cases h2 : s ≤ p₀.natAbs
    · rw [ite_eq_right h1, ite_eq_left h2]
      have e : s + 1 - p₀.natAbs = 1 := by omega
      rw [e]
      have hs : s = p₀.natAbs := by omega
      have h1' : sweepPos L 1 = 0 ∨ sweepPos L 1 = 1 := by
        unfold sweepPos
        omega
      rw [abs_le]
      split_ifs <;> constructor <;> omega
    · rw [ite_eq_right h1, ite_eq_right h2]
      have e : s + 1 - p₀.natAbs = s - p₀.natAbs + 1 := by omega
      rw [e]
      exact unitSteps_sweepPos L _

theorem epiWalk_visit (p₀ : ℤ) {L q : ℕ} (hq : q < L) : epiWalk p₀ L (p₀.natAbs + q) = q := by
  unfold epiWalk
  by_cases h : q = 0
  · subst h
    rw [ite_eq_left (by omega)]
    split_ifs <;> omega
  · rw [ite_eq_right (by omega), Nat.add_sub_cancel_left, sweepPos_of_lt hq]

theorem epiWalk_end (p₀ : ℤ) {L s : ℕ} (hs : p₀.natAbs + 2 * (L - 1) ≤ s) : epiWalk p₀ L s = 0 := by
  unfold epiWalk
  by_cases h : s ≤ p₀.natAbs
  · rw [ite_eq_left h]
    have : s = p₀.natAbs := by omega
    split_ifs <;> omega
  · rw [ite_eq_right h, sweepPos_eq_zero (by omega)]

/-! ### The selection diagram -/

/-- **The selection diagram**: run 1 (`K` copies of `D`'s work walks, parked after slot `⌈T/r⌉ - 1`),
an input epilogue sweeping `[0, L)`, and run 2 (a fresh copy of `D`, delayed by `P r` steps). Only
run 2 outputs. -/
def selDiagram {k : ℕ} (D : TSDiagram k) (K P r L : ℕ) : TSDiagram ((K + 1) * k) where
  T := P * r + D.T
  work := fun t => if ((finProdFinEquiv.symm t).1 : ℕ) < K
    then parkWalk (D.nodes r * r) (D.work (finProdFinEquiv.symm t).2)
    else delayWalk (P * r) (D.work (finProdFinEquiv.symm t).2)
  inp := fun τ => if τ < D.nodes r * r then D.inp τ
    else if τ < P * r then epiWalk (D.inp (D.nodes r * r)) L (τ - D.nodes r * r)
    else D.inp (τ - P * r)
  out := fun τ => if τ < P * r then 0 else D.out (τ - P * r)

section Sel

variable {k : ℕ} (D : TSDiagram k) {K P r L : ℕ}

/-- The run-1 tape `t` of copy `a`. -/
def runTape (K : ℕ) (a : ℕ) (ha : a < K + 1) (t : Fin k) : Fin ((K + 1) * k) :=
  finProdFinEquiv (⟨a, ha⟩, t)

theorem work_sel_run1 {a : ℕ} (ha : a < K) (t : Fin k) :
    (selDiagram D K P r L).work (runTape K a (by omega) t) = parkWalk (D.nodes r * r) (D.work t) := by
  dsimp only [selDiagram, runTape]
  rw [Equiv.symm_apply_apply]
  exact ite_eq_left ha

theorem work_sel_run2 (t : Fin k) :
    (selDiagram D K P r L).work (runTape K K (by omega) t) = delayWalk (P * r) (D.work t) := by
  dsimp only [selDiagram, runTape]
  rw [Equiv.symm_apply_apply]
  exact ite_eq_right (lt_irrefl K)

/-- Every tape is a run-1 tape or the run-2 tape of its walk. -/
theorem sel_tape_cases (t : Fin ((K + 1) * k)) :
    (((finProdFinEquiv.symm t).1 : ℕ) < K ∧
      (selDiagram D K P r L).work t = parkWalk (D.nodes r * r) (D.work (finProdFinEquiv.symm t).2)) ∨
    (((finProdFinEquiv.symm t).1 : ℕ) = K ∧
      (selDiagram D K P r L).work t = delayWalk (P * r) (D.work (finProdFinEquiv.symm t).2)) := by
  by_cases h : ((finProdFinEquiv.symm t).1 : ℕ) < K
  · exact Or.inl ⟨h, ite_eq_left h⟩
  · have := (finProdFinEquiv.symm t).1.2
    exact Or.inr ⟨by omega, ite_eq_right h⟩

theorem T_sel : (selDiagram D K P r L).T = P * r + D.T := rfl

theorem nodes_sel (hr : 1 ≤ r) : (selDiagram D K P r L).nodes r = P + D.nodes r :=
  nodes_prefix D (L := L) hr

/-- The hypothesis on the length of the first two phases. -/
def SelRoom (D : TSDiagram k) (P r L : ℕ) : Prop :=
  2 * (D.nodes r * r) + 2 * L + 2 * r ≤ P * r

theorem valid_sel (hD : D.Valid L) (hr : 1 ≤ r) (hP : SelRoom D P r L) :
    (selDiagram D K P r L).Valid L := by
  obtain ⟨hwork, hinp0, hinp, hout0, hout, houtT⟩ := hD
  have hT1 : D.T ≤ D.nodes r * r := T_le_nodes_mul (D := D) hr
  -- the input head is within `T₁` of `0` at time `T₁`
  have hp₀ : (D.inp (D.nodes r * r)).natAbs ≤ D.nodes r * r := by
    have := unitSteps_dist hinp (Nat.zero_le (D.nodes r * r))
    rw [hinp0] at this
    simp only [sub_zero, Int.abs_eq_natAbs] at this
    omega
  unfold SelRoom at hP
  refine ⟨fun t => ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rcases sel_tape_cases D (P := P) (r := r) (L := L) t with ⟨-, hw⟩ | ⟨-, hw⟩
    · rw [hw, parkWalk_of_le _ (Nat.zero_le _)]; exact (hwork _).1
    · rw [hw]
      unfold delayWalk
      split_ifs
      · rfl
      · simpa using (hwork _).1
  · rcases sel_tape_cases D (P := P) (r := r) (L := L) t with ⟨-, hw⟩ | ⟨-, hw⟩
    · rw [hw]; exact unitSteps_parkWalk (hwork _).2
    · rw [hw]; exact unitSteps_delayWalk (hwork _).1 (hwork _).2
  · show (if 0 < D.nodes r * r then D.inp 0 else _) = 0
    split_ifs with h1 h2
    · exact hinp0
    · rw [Nat.zero_sub, epiWalk_zero]
      have : D.nodes r * r = 0 := by omega
      rw [this]; exact hinp0
    · omega
  · intro τ
    show |(if τ + 1 < D.nodes r * r then D.inp (τ + 1)
        else if τ + 1 < P * r then epiWalk (D.inp (D.nodes r * r)) L (τ + 1 - D.nodes r * r)
        else D.inp (τ + 1 - P * r)) -
      (if τ < D.nodes r * r then D.inp τ
        else if τ < P * r then epiWalk (D.inp (D.nodes r * r)) L (τ - D.nodes r * r)
        else D.inp (τ - P * r))| ≤ 1
    by_cases h1 : τ + 1 < D.nodes r * r
    · rw [ite_eq_left h1, ite_eq_left (show τ < D.nodes r * r by omega)]
      exact hinp τ
    · by_cases h2 : τ < D.nodes r * r
      · rw [ite_eq_right h1, ite_eq_left h2, ite_eq_left (show τ + 1 < P * r by omega)]
        have e : τ + 1 - D.nodes r * r = 0 := by omega
        have e' : τ + 1 = D.nodes r * r := by omega
        rw [e, epiWalk_zero, ← e']
        exact hinp τ
      · rw [ite_eq_right h1, ite_eq_right h2]
        by_cases h3 : τ + 1 < P * r
        · rw [ite_eq_left h3, ite_eq_left (show τ < P * r by omega)]
          have e : τ + 1 - D.nodes r * r = τ - D.nodes r * r + 1 := by omega
          rw [e]
          exact epiWalk_step _ _ _
        · by_cases h4 : τ < P * r
          · rw [ite_eq_right h3, ite_eq_left h4]
            have e : τ + 1 - P * r = 0 := by omega
            rw [e, hinp0, epiWalk_end _ (by omega)]; simp
          · rw [ite_eq_right h3, ite_eq_right h4]
            have e : τ + 1 - P * r = τ - P * r + 1 := by omega
            rw [e]
            exact hinp _
  · exact (valid_prefix D (P := P) (r := r) ⟨hwork, hinp0, hinp, hout0, hout, houtT⟩
      (by omega)).2.2.2.1
  · exact (valid_prefix D (P := P) (r := r) ⟨hwork, hinp0, hinp, hout0, hout, houtT⟩
      (by omega)).2.2.2.2.1
  · exact (valid_prefix D (P := P) (r := r) ⟨hwork, hinp0, hinp, hout0, hout, houtT⟩
      (by omega)).2.2.2.2.2

/-! #### Residencies and chords of run 1 -/

/-- Run-1 copies have at least `D`'s residencies at the slots of `D`. -/
theorem pairRes_sel_run1 (hr : 1 ≤ r) {a : ℕ} (ha : a < K) (t : Fin k) (y : ℕ) :
    pairRes r (D.work t) D.T y ⊆
      pairRes r ((selDiagram D K P r L).work (runTape K a (by omega) t))
        (selDiagram D K P r L).T y := by
  rw [work_sel_run1 D ha]
  apply pairRes_sub_of_agree (by show D.T ≤ P * r + D.T; omega)
  intro σ hσ
  rw [parkWalk_of_le _ (by have := T_le_nodes_mul (D := D) hr; omega)]

/-- On the complete slots of `D`, run-1 copies have exactly `D`'s residencies. -/
theorem pairRes_sel_run1_eq (hr : 1 ≤ r) {a : ℕ} (ha : a < K) (t : Fin k) {y : ℕ}
    (hy : y + 1 < D.nodes r) :
    pairRes r ((selDiagram D K P r L).work (runTape K a (by omega) t))
      (selDiagram D K P r L).T y = pairRes r (D.work t) D.T y := by
  have hfull := slot_full D hr hy
  have e : (y + 1) * r = y * r + r := by ring
  rw [work_sel_run1 D ha]
  apply pairRes_congr (by show y * r + r ≤ P * r + D.T; omega) (by omega)
  intro σ hσ
  rw [parkWalk_of_le _ (by have := T_le_nodes_mul (D := D) hr; omega)]

/-- `D`'s chords are chords of every run-1 copy. -/
theorem isChord_sel_run1 (hr : 1 ≤ r) {a : ℕ} (ha : a < K) (t : Fin k) {β : ℤ} {x z : ℕ}
    (hz : z < D.nodes r) (hc : IsChord (pairRes r (D.work t) D.T) β x z) :
    IsChord (pairRes r ((selDiagram D K P r L).work (runTape K a (by omega) t))
      (selDiagram D K P r L).T) β x z := by
  obtain ⟨hxz, hx, hz', hbetw⟩ := hc
  refine ⟨hxz, ?_, pairRes_sel_run1 D hr ha t z hz', ?_⟩
  · rw [pairRes_sel_run1_eq D hr ha t (by omega)]; exact hx
  · intro y h1 h2
    rw [pairRes_sel_run1_eq D hr ha t (by omega)]
    exact hbetw y h1 h2

/-- Run-1 copies have no chord into a slot after the first epilogue slot. -/
theorem isChord_sel_run1_le (hr : 1 ≤ r) {a : ℕ} (ha : a < K) (t : Fin k) {β : ℤ} {x z : ℕ}
    (hc : IsChord (pairRes r ((selDiagram D K P r L).work (runTape K a (by omega) t))
      (selDiagram D K P r L).T) β x z) : z ≤ D.nodes r := by
  by_contra hz
  push Not at hz
  obtain ⟨hxz, -, hzR, hbetw⟩ := hc
  rw [work_sel_run1 D ha] at hzR hbetw
  have hzT : z * r < (selDiagram D K P r L).T := by
    by_contra h
    push Not at h
    rw [pairRes_empty h] at hzR
    simp at hzR
  have hz1 : D.nodes r * r ≤ (z - 1) * r := Nat.mul_le_mul_right _ (by omega)
  have hz1T : (z - 1) * r < (selDiagram D K P r L).T :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ (by omega)) hzT
  apply hbetw (z - 1) (by omega) (by omega)
  rw [pairRes_park _ hz1 hz1T hr]
  rwa [pairRes_park _ (le_trans hz1 (Nat.mul_le_mul_right _ (by omega))) hzT hr] at hzR

/-! #### Run 2 -/

theorem pairRes_sel_run2 (hD : D.Valid L) (t : Fin k) (y : ℕ) :
    pairRes r ((selDiagram D K P r L).work (runTape K K (by omega) t)) (selDiagram D K P r L).T
      (P + y) = pairRes r (D.work t) D.T y := by
  rw [work_sel_run2]
  exact pairRes_delayWalk_add ((hD.1 t).1) y

theorem isChord_sel_run2 (hr : 1 ≤ r) (hD : D.Valid L) (t : Fin k) {β : ℤ} {x z : ℕ} :
    IsChord (pairRes r ((selDiagram D K P r L).work (runTape K K (by omega) t))
      (selDiagram D K P r L).T) β x z ↔
      P ≤ x ∧ IsChord (pairRes r (D.work t) D.T) β (x - P) (z - P) := by
  rw [work_sel_run2]
  exact isChord_prefix D (L := L) hr hD t

/-- The chords of the selection diagram. -/
theorem sel_chord_cases (hr : 1 ≤ r) (hD : D.Valid L) {x z : ℕ}
    (h : ∃ (t : Fin ((K + 1) * k)) (β : ℤ),
      IsChord (pairRes r ((selDiagram D K P r L).work t) (selDiagram D K P r L).T) β x z) :
    z ≤ D.nodes r ∨ (P ≤ x ∧ ∃ (t : Fin k) (β : ℤ),
      IsChord (pairRes r (D.work t) D.T) β (x - P) (z - P)) := by
  obtain ⟨t, β, hc⟩ := h
  have ht : t = runTape K (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).1.2
      (finProdFinEquiv.symm t).2 := by
    unfold runTape
    simp only [Fin.eta, Prod.mk.eta, Equiv.apply_symm_apply]
  rcases sel_tape_cases D (P := P) (r := r) (L := L) t with ⟨ha, -⟩ | ⟨ha, -⟩
  · rw [ht] at hc
    exact Or.inl (isChord_sel_run1_le D hr ha _ hc)
  · have ht' : t = runTape K K (by omega) (finProdFinEquiv.symm t).2 :=
      (Equiv.symm_apply_eq finProdFinEquiv).1 (Prod.ext (Fin.ext ha) rfl)
    rw [ht', isChord_sel_run2 D hr hD] at hc
    exact Or.inr ⟨hc.1, _, β, hc.2⟩

theorem mem_chordEdges_sel_run2 (hr : 1 ≤ r) (hD : D.Valid L) {a b : ℕ}
    (h : (a, b) ∈ D.chordEdges r) : (P + a, P + b) ∈ (selDiagram D K P r L).chordEdges r := by
  rw [mem_chordEdges] at h ⊢
  obtain ⟨h1, h2, t, β, hc⟩ := h
  rw [nodes_sel D hr]
  refine ⟨by simp only; omega, by simp only; omega, runTape K K (by omega) t, β, ?_⟩
  rw [isChord_sel_run2 D hr hD]
  simp only [Nat.add_sub_cancel_left]
  exact ⟨Nat.le_add_right _ _, hc⟩

theorem mem_chordEdges_sel_run1 (hr : 1 ≤ r) (hK : 1 ≤ K) {e : ℕ × ℕ}
    (h : e ∈ D.chordEdges r) : e ∈ (selDiagram D K P r L).chordEdges r := by
  rw [mem_chordEdges] at h ⊢
  obtain ⟨h1, h2, t, β, hc⟩ := h
  rw [nodes_sel D hr]
  exact ⟨by omega, by omega, runTape K 0 (by omega) t, β, isChord_sel_run1 D hr hK t h2 hc⟩

/-- Every edge of `D` is an edge of run 1. -/
theorem edges_sel_run1 (hr : 1 ≤ r) (hK : 1 ≤ K) {e : ℕ × ℕ} (h : e ∈ D.edges r) :
    e ∈ (selDiagram D K P r L).edges r := by
  rcases Finset.mem_union.1 h with hm | hc
  · apply Finset.mem_union_left
    rw [mem_memEdges] at hm ⊢
    rw [nodes_sel D hr]
    omega
  · exact Finset.mem_union_right _ (mem_chordEdges_sel_run1 D hr hK hc)

/-- **The edges of run 2 are `D`'s, shifted.** -/
theorem mem_edges_sel_add (hr : 1 ≤ r) (hD : D.Valid L) (hP : D.nodes r < P) (a b : ℕ) :
    (P + a, P + b) ∈ (selDiagram D K P r L).edges r ↔ (a, b) ∈ D.edges r := by
  constructor
  · intro h
    rcases Finset.mem_union.1 h with hm | hc
    · apply Finset.mem_union_left
      rw [mem_memEdges] at hm ⊢
      rw [nodes_sel D hr] at hm
      simp only at hm ⊢
      omega
    · apply Finset.mem_union_right
      rw [mem_chordEdges] at hc
      obtain ⟨h1, h2, hh⟩ := hc
      rcases sel_chord_cases D hr hD hh with hz | ⟨-, t, β, hc'⟩
      · simp only at hz; omega
      · simp only [Nat.add_sub_cancel_left] at hc'
        rw [nodes_sel D hr] at h1 h2
        rw [mem_chordEdges]
        exact ⟨by simp only at h1 ⊢; omega, by simp only at h2 ⊢; omega, t, β, hc'⟩
  · intro h
    rcases Finset.mem_union.1 h with hm | hc
    · apply Finset.mem_union_left
      rw [mem_memEdges] at hm ⊢
      rw [nodes_sel D hr]
      simp only at hm ⊢
      omega
    · exact Finset.mem_union_right _ (mem_chordEdges_sel_run2 D hr hD hc)

/-- **No chord crosses into run 2**: an edge into a node `≥ P` from a node `< P` is the memory edge
`P - 1 → P`. -/
theorem sel_edge_into_run2 (hr : 1 ≤ r) (hD : D.Valid L) (hP : D.nodes r < P) {e : ℕ × ℕ}
    (he : e ∈ (selDiagram D K P r L).edges r) (h1 : e.1 < P) (h2 : P ≤ e.2) :
    e = (P - 1, P) := by
  rcases Finset.mem_union.1 he with hm | hc
  · rw [mem_memEdges] at hm
    obtain ⟨a, b⟩ := e
    simp only at hm h1 h2 ⊢
    ext <;> simp only <;> omega
  · rw [mem_chordEdges] at hc
    obtain ⟨-, -, hh⟩ := hc
    rcases sel_chord_cases D hr hD hh with hz | ⟨hx, -⟩
    · omega
    · omega

/-! #### Capacities -/

/-- A sum over the image of an injection is at most the full sum. -/
theorem sum_comp_le_sum {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] (e : α → β)
    (he : Function.Injective e) (G : β → ℕ) : ∑ a, G (e a) ≤ ∑ b, G b := by
  rw [← Finset.sum_image (fun a _ b _ h => he h)]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

theorem runTape_injective_run1 :
    Function.Injective (fun p : Fin K × Fin k => runTape (k := k) K p.1 (by omega) p.2) := by
  intro p q h
  have := finProdFinEquiv.injective h
  simp only [Prod.mk.injEq, Fin.mk.injEq] at this
  exact Prod.ext (Fin.ext this.1) this.2

theorem runTape_injective_run2 : Function.Injective (fun t : Fin k => runTape K K (by omega) t) := by
  intro p q h
  have := finProdFinEquiv.injective h
  simp only [Prod.mk.injEq] at this
  exact this.2

/-- `K` copies of a sum, each bounded by a sum over the run-1 tapes. -/
theorem sum_run1_le (g : Fin k → ℕ) (G : Fin ((K + 1) * k) → ℕ)
    (hg : ∀ (a : ℕ) (ha : a < K) (t : Fin k), g t ≤ G (runTape K a (by omega) t)) :
    K * ∑ t, g t ≤ ∑ t, G t := by
  calc K * ∑ t, g t = ∑ _a : Fin K, ∑ t, g t := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    _ ≤ ∑ a : Fin K, ∑ t, G (runTape K a (by omega) t) :=
        Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun t _ => hg a a.2 t))
    _ = ∑ p : Fin K × Fin k, G (runTape K p.1 (by omega) p.2) := by
        rw [Fintype.sum_prod_type]
    _ ≤ ∑ t, G t := by
        classical
        exact sum_comp_le_sum _ runTape_injective_run1 G

/-- Run 1 carries at least `K` times `D`'s resident blocks. -/
theorem resSum_sel_run1 (hr : 1 ≤ r) (y : ℕ) :
    K * ∑ t, (pairRes r (D.work t) D.T y).card ≤
      ∑ t, (pairRes r ((selDiagram D K P r L).work t) (selDiagram D K P r L).T y).card :=
  sum_run1_le _ _ (fun _ ha t => Finset.card_le_card (pairRes_sel_run1 D hr ha t y))

/-- Run 1 has at least `K` times `D`'s chord tapes on `D`'s chords. -/
theorem chordTapes_sel_run1 (hr : 1 ≤ r) {e : ℕ × ℕ} (he : e ∈ D.chordEdges r) :
    K * D.chordTapes r e ≤ (selDiagram D K P r L).chordTapes r e := by
  classical
  have he2 := ((mem_chordEdges D).1 he).2.1
  unfold TSDiagram.chordTapes
  rw [Finset.card_filter, Finset.card_filter]
  apply sum_run1_le
  intro a ha t
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd ⟨h1.choose, isChord_sel_run1 D hr ha t he2 h1.choose_spec⟩ h2
  · exact Nat.zero_le _
  · exact le_rfl

/-- Run 2 carries at least `D`'s resident blocks. -/
theorem resSum_sel_run2 (hD : D.Valid L) (y : ℕ) :
    ∑ t, (pairRes r (D.work t) D.T y).card ≤
      ∑ t, (pairRes r ((selDiagram D K P r L).work t) (selDiagram D K P r L).T (P + y)).card := by
  classical
  calc ∑ t, (pairRes r (D.work t) D.T y).card
      = ∑ t : Fin k, (pairRes r ((selDiagram D K P r L).work (runTape K K (by omega) t))
          (selDiagram D K P r L).T (P + y)).card := by
        congr 1; funext t; rw [pairRes_sel_run2 D hD t y]
    _ ≤ _ := sum_comp_le_sum _ runTape_injective_run2
          (fun t => (pairRes r ((selDiagram D K P r L).work t) (selDiagram D K P r L).T (P + y)).card)

/-- Run 2 has at least `D`'s chord tapes on the shifted chords. -/
theorem chordTapes_sel_run2 (hr : 1 ≤ r) (hD : D.Valid L) (a b : ℕ) :
    D.chordTapes r (a, b) ≤ (selDiagram D K P r L).chordTapes r (P + a, P + b) := by
  classical
  unfold TSDiagram.chordTapes
  rw [Finset.card_filter, Finset.card_filter]
  calc ∑ t : Fin k, (if ∃ β, IsChord (pairRes r (D.work t) D.T) β (a, b).1 (a, b).2 then 1 else 0)
      ≤ ∑ t : Fin k, (if ∃ β, IsChord (pairRes r ((selDiagram D K P r L).work
          (runTape K K (by omega) t)) (selDiagram D K P r L).T) β
          (P + a, P + b).1 (P + a, P + b).2 then 1 else 0) := by
        apply Finset.sum_le_sum
        intro t _
        split_ifs with h1 h2
        · exact le_rfl
        · exfalso
          apply h2
          obtain ⟨β, hc⟩ := h1
          refine ⟨β, ?_⟩
          show IsChord (pairRes r ((selDiagram D K P r L).work (runTape K K (by omega) t))
            (selDiagram D K P r L).T) β (P + a) (P + b)
          rw [isChord_sel_run2 D hr hD]
          simp only [Nat.add_sub_cancel_left]
          exact ⟨Nat.le_add_right _ _, hc⟩
        · exact Nat.zero_le _
        · exact le_rfl
    _ ≤ _ := sum_comp_le_sum _ runTape_injective_run2
          (fun t => if ∃ β, IsChord (pairRes r ((selDiagram D K P r L).work t)
            (selDiagram D K P r L).T) β (P + a, P + b).1 (P + a, P + b).2 then 1 else 0)

/-! #### Rows and outputs -/

theorem rowsAt_sel_run1 (hr : 1 ≤ r) {n w : ℕ} {y : ℕ} :
    D.rowsAt n w r y ⊆ (selDiagram D K P r L).rowsAt n w r y := by
  classical
  intro i hi
  simp only [TSDiagram.rowsAt, Finset.mem_filter, Finset.mem_range] at hi ⊢
  obtain ⟨hi, τ, hτ, h1, h2⟩ := hi
  have hτT : τ < D.T := ((mem_slotOf).1 hτ).2.2
  have hT1 : D.T ≤ D.nodes r * r := T_le_nodes_mul (D := D) hr
  have hin : (selDiagram D K P r L).inp τ = D.inp τ := by
    show (if τ < D.nodes r * r then D.inp τ else _) = _
    rw [ite_eq_left (by omega)]
  refine ⟨hi, τ, ?_, by rw [hin]; exact h1, by rw [hin]; exact h2⟩
  rw [mem_slotOf] at hτ ⊢
  exact ⟨hτ.1, hτ.2.1, by show τ < P * r + D.T; omega⟩

theorem rowsAt_sel_add (hr : 1 ≤ r) (hP : SelRoom D P r L) {n w : ℕ} (y : ℕ) :
    (selDiagram D K P r L).rowsAt n w r (P + y) = D.rowsAt n w r y := by
  classical
  unfold SelRoom at hP
  have hin : ∀ τ, (selDiagram D K P r L).inp (P * r + τ) = D.inp τ := by
    intro τ
    show (if P * r + τ < D.nodes r * r then _ else if P * r + τ < P * r then _
      else D.inp (P * r + τ - P * r)) = _
    rw [ite_eq_right (by omega), ite_eq_right (by omega), Nat.add_sub_cancel_left]
  ext i
  simp only [TSDiagram.rowsAt, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hi, τ', hτ', h1, h2⟩
    have hge : P * r ≤ τ' := by
      rw [mem_slotOf] at hτ'
      have : (P + y) * r = P * r + y * r := by ring
      omega
    have e : τ' = P * r + (τ' - P * r) := by omega
    rw [e] at hτ' h1 h2
    rw [hin] at h1 h2
    exact ⟨hi, τ' - P * r, (slotOf_prefix_add (P := P) (r := r)).1 hτ', h1, h2⟩
  · rintro ⟨hi, τ, hτ, h1, h2⟩
    refine ⟨hi, P * r + τ, (slotOf_prefix_add (P := P) (r := r)).2 hτ, ?_, ?_⟩
    · rw [hin]; exact h1
    · rw [hin]; exact h2

theorem visible_sel_add (hr : 1 ≤ r) (hP : SelRoom D P r L) {n w : ℕ} (y : ℕ) {L' : ℕ}
    (x : Fin L' → Bool) :
    (selDiagram D K P r L).visible n w r (P + y) x = D.visible n w r y x := by
  funext d
  simp only [TSDiagram.visible, rowsAt_sel_add D hr hP]

theorem outNode_sel (hr : 1 ≤ r) (hD : D.Valid L) (hT : 1 ≤ D.T) (o : ℕ) :
    (selDiagram D K P r L).outNode r o = P + D.outNode r o :=
  outNode_prefix D (L := L) hr hD hT o

/-- **The epilogue attaches every row.** -/
theorem row_mem_epi (hr : 1 ≤ r) (hD : D.Valid L) (hP : SelRoom D P r L) {n w i : ℕ}
    (hL : L = n * n * w) (hw : 1 ≤ w) (hi : i < n) :
    ∃ y, D.nodes r ≤ y ∧ y < P ∧ i ∈ (selDiagram D K P r L).rowsAt n w r y := by
  classical
  unfold SelRoom at hP
  set T₁ := D.nodes r * r with hT₁
  set p₀ := D.inp T₁ with hp₀def
  have hp₀ : p₀.natAbs ≤ T₁ := by
    have := unitSteps_dist hD.2.2.1 (Nat.zero_le T₁)
    rw [hD.2.1] at this
    simp only [sub_zero, Int.abs_eq_natAbs] at this
    omega
  have hq : i * n * w < L := by
    rw [hL]
    calc i * n * w < (i + 1) * n * w := by
          apply Nat.mul_lt_mul_of_pos_right _ (by omega)
          exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      _ ≤ n * n * w := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hi)
  set τ := T₁ + p₀.natAbs + i * n * w with hτdef
  have hτP : τ < P * r := by omega
  have hin : (selDiagram D K P r L).inp τ = (i * n * w : ℕ) := by
    show (if τ < T₁ then _ else if τ < P * r then epiWalk p₀ L (τ - T₁) else _) = _
    rw [ite_eq_right (by omega), ite_eq_left hτP]
    have e : τ - T₁ = p₀.natAbs + i * n * w := by omega
    rw [e, epiWalk_visit p₀ hq]
  refine ⟨τ / r, ?_, ?_, ?_⟩
  · exact (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
  · exact (Nat.div_lt_iff_lt_mul (by omega)).2 hτP
  · simp only [TSDiagram.rowsAt, Finset.mem_filter, Finset.mem_range]
    refine ⟨hi, τ, mem_slotOf_div hr (by show τ < P * r + D.T; omega), ?_, ?_⟩
    · rw [hin]
    · rw [hin]
      have : i * n * w < (i + 1) * n * w :=
        Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_right (by omega) (by omega)) (by omega)
      exact_mod_cast this

end Sel

end Transpose.Tape.Impl
