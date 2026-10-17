import Transpose.Tape.CEHint

/-!
# Prepending an input sweep: plain ⟹ robust for affine sets

`prefixDiagram D P r L` is the diagram `D` delayed by `P` slots of `r` steps. During the prefix the
work heads are parked at cell `0`, nothing is output, and the input head sweeps the input: it moves
from `0` to `L - 1` and back to `0` (then waits). The original diagram follows unchanged.
* The work walks of the original part are delayed copies, so their residencies and chords are the
  shifted ones (`pairRes_prefix_add`, `isChord_prefix`), and no chord leaves the prefix.
* Every row is read in the prefix, in the slot where it starts (`row_mem_prefix`), and at most one
  row starts per slot (`startSlot_injective`).

**Additive hints can be removed** (`prefix_solves`). If a code solves complete exchange on `F` and an
additive hint `Σ_i g_i(row i)` of `s` bits, with a shift table `z`, puts every input into `F`, then
the prefix computes the hint along its spine, and the original part runs the code shifted by
`z(hint)`, reading the hint from the low `s` bits of its memory edges. Hence:
* `noCode_additive_of_noCode`: `NoCode_TM` rules out codes on every set that such a hint covers;
* `noCode_affine_of_noCode`: in particular on every nonempty affine set of codimension `≤ C n w`, and
  `noCode_of_affine_subset`: on every set containing one.

This is the syndrome trick, in the time–space diagram model.
-/

namespace Transpose.Tape.Impl

open Transpose TSDiagram

/-! ### Shifted walks -/

section Shift

variable {r : ℕ}

/-- A walk delayed by `Q` steps, parked at `0` before. -/
def delayWalk (Q : ℕ) (h : ℕ → ℤ) (τ : ℕ) : ℤ := if τ < Q then 0 else h (τ - Q)

theorem delayWalk_add (Q : ℕ) (h : ℕ → ℤ) (τ : ℕ) : delayWalk Q h (Q + τ) = h τ := by
  unfold delayWalk
  rw [ite_eq_right (by omega), Nat.add_sub_cancel_left]

theorem delayWalk_lt {Q : ℕ} (h : ℕ → ℤ) {τ : ℕ} (hτ : τ < Q) : delayWalk Q h τ = 0 := by
  unfold delayWalk
  rw [ite_eq_left hτ]

theorem unitSteps_delayWalk {Q : ℕ} {h : ℕ → ℤ} (h0 : h 0 = 0) (hh : UnitSteps h) :
    UnitSteps (delayWalk Q h) := by
  intro τ
  unfold delayWalk
  by_cases h1 : τ + 1 < Q
  · rw [ite_eq_left h1, ite_eq_left (show τ < Q by omega)]; simp
  · by_cases h2 : τ < Q
    · rw [ite_eq_right h1, ite_eq_left h2]
      have : τ + 1 - Q = 0 := by omega
      rw [this, h0]; simp
    · rw [ite_eq_right h1, ite_eq_right h2]
      have : τ + 1 - Q = τ - Q + 1 := by omega
      rw [this]
      exact hh (τ - Q)

theorem curBlock_delayWalk_add (Q : ℕ) (h : ℕ → ℤ) (τ : ℕ) :
    curBlock r (delayWalk Q h) (Q + τ) = curBlock r h τ := by
  unfold curBlock
  rw [delayWalk_add]

theorem curBlock_delayWalk_lt {Q : ℕ} (h : ℕ → ℤ) {τ : ℕ} (hτ : τ < Q) :
    curBlock r (delayWalk Q h) τ = 0 := by
  unfold curBlock blockOf
  rw [delayWalk_lt h hτ]
  simp

/-- Before the delay ends there is no previous block. -/
theorem prevBlock_delayWalk_le {Q : ℕ} {h : ℕ → ℤ} (h0 : h 0 = 0) :
    ∀ τ, τ ≤ Q → prevBlock r (delayWalk Q h) τ = none := by
  intro τ
  induction τ with
  | zero => intro _; exact prevBlock_zero
  | succ τ ih =>
    intro hτ
    rw [prevBlock_succ]
    have e1 : curBlock r (delayWalk Q h) (τ + 1) = 0 := by
      by_cases hq : τ + 1 < Q
      · exact curBlock_delayWalk_lt h hq
      · have : τ + 1 = Q + 0 := by omega
        rw [this, curBlock_delayWalk_add]
        unfold curBlock blockOf
        rw [h0]; simp
    have e2 : curBlock r (delayWalk Q h) τ = 0 := curBlock_delayWalk_lt h (by omega)
    rw [e1, e2, ite_eq_right (by simp)]
    exact ih (by omega)

/-- **The resident pair of a delayed walk is the shifted one.** -/
theorem prevBlock_delayWalk_add {Q : ℕ} {h : ℕ → ℤ} (h0 : h 0 = 0) :
    ∀ τ, prevBlock r (delayWalk Q h) (Q + τ) = prevBlock r h τ := by
  intro τ
  induction τ with
  | zero =>
    rw [Nat.add_zero, prevBlock_delayWalk_le h0 Q le_rfl, prevBlock_zero]
  | succ τ ih =>
    rw [show Q + (τ + 1) = Q + τ + 1 by omega, prevBlock_succ, prevBlock_succ, ih,
      show Q + τ + 1 = Q + (τ + 1) by omega, curBlock_delayWalk_add, curBlock_delayWalk_add]

theorem residentPair_delayWalk_add {Q : ℕ} {h : ℕ → ℤ} (h0 : h 0 = 0) (τ : ℕ) :
    residentPair r (delayWalk Q h) (Q + τ) = residentPair r h τ := by
  unfold residentPair
  rw [curBlock_delayWalk_add, prevBlock_delayWalk_add h0]

theorem residentPair_delayWalk_lt {Q : ℕ} {h : ℕ → ℤ} (h0 : h 0 = 0) {τ : ℕ} (hτ : τ < Q) :
    residentPair r (delayWalk Q h) τ = {0} := by
  unfold residentPair
  rw [curBlock_delayWalk_lt h hτ, prevBlock_delayWalk_le h0 τ hτ.le]
  rfl

theorem pairRes_delayWalk_add {P T : ℕ} {h : ℕ → ℤ} (h0 : h 0 = 0) (y : ℕ) :
    pairRes r (delayWalk (P * r) h) (P * r + T) (P + y) = pairRes r h T y := by
  have hy : (P + y) * r = P * r + y * r := by ring
  ext β
  rw [mem_pairRes, mem_pairRes]
  constructor
  · rintro ⟨τ', h1, h2, h3, h4⟩
    refine ⟨τ' - P * r, by omega, by omega, by omega, ?_⟩
    have e : τ' = P * r + (τ' - P * r) := by omega
    rw [e, residentPair_delayWalk_add h0] at h4
    exact h4
  · rintro ⟨τ, h1, h2, h3, h4⟩
    refine ⟨P * r + τ, by omega, by omega, by omega, ?_⟩
    rw [residentPair_delayWalk_add h0]; exact h4

theorem pairRes_delayWalk_lt (hr : 1 ≤ r) {P T : ℕ} {h : ℕ → ℤ} (h0 : h 0 = 0) {y : ℕ}
    (hy : y < P) : pairRes r (delayWalk (P * r) h) (P * r + T) y = {0} := by
  ext β
  rw [mem_pairRes, Finset.mem_singleton]
  constructor
  · rintro ⟨τ, h1, h2, -, h4⟩
    have hτ : τ < P * r := by
      have : (y + 1) * r ≤ P * r := Nat.mul_le_mul_right _ hy
      have : (y + 1) * r = y * r + r := by ring
      omega
    rw [residentPair_delayWalk_lt h0 hτ, Finset.mem_singleton] at h4
    exact h4
  · rintro rfl
    have hτ : y * r < P * r := Nat.mul_lt_mul_of_pos_right hy (by omega)
    refine ⟨y * r, le_rfl, by omega, by omega, ?_⟩
    rw [residentPair_delayWalk_lt h0 hτ, Finset.mem_singleton]

end Shift

/-! ### The prefix diagram -/

/-- The prefix input walk: from `0` up to `L - 1`, back down to `0`, then waiting at `0`. -/
def sweepPos (L τ : ℕ) : ℤ := ((min τ (2 * (L - 1) - τ) : ℕ) : ℤ)

theorem unitSteps_sweepPos (L : ℕ) : UnitSteps (sweepPos L) := by
  intro τ
  unfold sweepPos
  have h : min (τ + 1) (2 * (L - 1) - (τ + 1)) ≤ min τ (2 * (L - 1) - τ) + 1 ∧
      min τ (2 * (L - 1) - τ) ≤ min (τ + 1) (2 * (L - 1) - (τ + 1)) + 1 := by omega
  generalize min (τ + 1) (2 * (L - 1) - (τ + 1)) = a at h ⊢
  generalize min τ (2 * (L - 1) - τ) = b at h ⊢
  rw [abs_le]
  constructor <;> omega

theorem sweepPos_eq_zero {L τ : ℕ} (hτ : 2 * (L - 1) ≤ τ) : sweepPos L τ = 0 := by
  unfold sweepPos
  have : min τ (2 * (L - 1) - τ) = 0 := by omega
  rw [this]; rfl

theorem sweepPos_of_lt {L τ : ℕ} (hτ : τ < L) : sweepPos L τ = τ := by
  unfold sweepPos
  have : min τ (2 * (L - 1) - τ) = τ := by omega
  rw [this]

/-- **`D` with an input sweep prepended**: `P` slots of `r` steps in which the work heads are parked,
nothing is output and the input head sweeps `[0, L)` and returns; then `D`. -/
def prefixDiagram {k : ℕ} (D : TSDiagram k) (P r L : ℕ) : TSDiagram k where
  T := P * r + D.T
  work := fun t => delayWalk (P * r) (D.work t)
  inp := fun τ => if τ < P * r then sweepPos L τ else D.inp (τ - P * r)
  out := fun τ => if τ < P * r then 0 else D.out (τ - P * r)

section Prefix

variable {k : ℕ} (D : TSDiagram k)

theorem valid_prefix {P r L : ℕ} (hD : D.Valid L) (hP : 2 * L ≤ P * r) :
    (prefixDiagram D P r L).Valid L := by
  obtain ⟨hwork, hinp0, hinp, hout0, hout, houtT⟩ := hD
  refine ⟨fun t => ⟨?_, unitSteps_delayWalk (hwork t).1 (hwork t).2⟩, ?_, ?_, ?_, ?_, ?_⟩
  · show delayWalk (P * r) (D.work t) 0 = 0
    by_cases h : 0 < P * r
    · exact delayWalk_lt _ h
    · have : P * r = 0 := by omega
      unfold delayWalk; rw [this]; simp [(hwork t).1]
  · show (if 0 < P * r then sweepPos L 0 else D.inp (0 - P * r)) = 0
    split_ifs
    · unfold sweepPos; simp
    · simpa using hinp0
  · intro τ
    show |(if τ + 1 < P * r then sweepPos L (τ + 1) else D.inp (τ + 1 - P * r)) -
      (if τ < P * r then sweepPos L τ else D.inp (τ - P * r))| ≤ 1
    by_cases h1 : τ + 1 < P * r
    · rw [ite_eq_left h1, ite_eq_left (show τ < P * r by omega)]
      exact unitSteps_sweepPos L τ
    · by_cases h2 : τ < P * r
      · rw [ite_eq_right h1, ite_eq_left h2]
        have e : τ + 1 - P * r = 0 := by omega
        rw [e, hinp0, sweepPos_eq_zero (by omega)]; simp
      · rw [ite_eq_right h1, ite_eq_right h2]
        have e : τ + 1 - P * r = τ - P * r + 1 := by omega
        rw [e]
        exact hinp (τ - P * r)
  · show (if 0 < P * r then 0 else D.out (0 - P * r)) = 0
    split_ifs
    · rfl
    · simpa using hout0
  · intro τ
    show (if τ < P * r then 0 else D.out (τ - P * r)) ≤
        (if τ + 1 < P * r then 0 else D.out (τ + 1 - P * r)) ∧
      (if τ + 1 < P * r then 0 else D.out (τ + 1 - P * r)) ≤
        (if τ < P * r then 0 else D.out (τ - P * r)) + 1
    by_cases h1 : τ + 1 < P * r
    · rw [ite_eq_left h1, ite_eq_left (show τ < P * r by omega)]; omega
    · by_cases h2 : τ < P * r
      · rw [ite_eq_right h1, ite_eq_left h2]
        have e : τ + 1 - P * r = 0 := by omega
        rw [e, hout0]; omega
      · rw [ite_eq_right h1, ite_eq_right h2]
        have e : τ + 1 - P * r = τ - P * r + 1 := by omega
        rw [e]
        exact hout (τ - P * r)
  · intro τ hτ
    show (if τ < P * r then 0 else D.out (τ - P * r)) = L
    have hτ' : P * r + D.T ≤ τ := hτ
    rw [ite_eq_right (show ¬ τ < P * r by omega)]
    exact houtT _ (by omega)

variable {P r L : ℕ}

theorem T_prefix : (prefixDiagram D P r L).T = P * r + D.T := rfl

theorem nodes_prefix (hr : 1 ≤ r) : (prefixDiagram D P r L).nodes r = P + D.nodes r := by
  show (P * r + D.T + r - 1) / r = P + (D.T + r - 1) / r
  have e : P * r + D.T + r - 1 = (D.T + r - 1) + r * P := by
    have : 1 ≤ D.T + r := by omega
    rw [Nat.mul_comm]; omega
  rw [e, Nat.add_mul_div_left _ _ (by omega)]
  ring

theorem work_prefix (t : Fin k) : (prefixDiagram D P r L).work t = delayWalk (P * r) (D.work t) :=
  rfl

theorem pairRes_prefix_add (hD : D.Valid L) (t : Fin k) (y : ℕ) :
    pairRes r ((prefixDiagram D P r L).work t) (prefixDiagram D P r L).T (P + y) =
      pairRes r (D.work t) D.T y :=
  pairRes_delayWalk_add ((hD.1 t).1) y

theorem pairRes_prefix_add' (hD : D.Valid L) (y : ℕ) :
    (∑ t, (pairRes r ((prefixDiagram D P r L).work t) (prefixDiagram D P r L).T (P + y)).card) =
      ∑ t, (pairRes r (D.work t) D.T y).card := by
  congr 1
  funext t
  rw [pairRes_prefix_add D hD t y]

theorem pairRes_prefix_lt (hr : 1 ≤ r) (hD : D.Valid L) (t : Fin k) {y : ℕ} (hy : y < P) :
    pairRes r ((prefixDiagram D P r L).work t) (prefixDiagram D P r L).T y = {0} :=
  pairRes_delayWalk_lt hr ((hD.1 t).1) hy

/-- Block `0` is resident at slot `0` of every nonempty diagram (the walks start at cell `0`). -/
theorem zero_mem_pairRes_zero (hr : 1 ≤ r) {h : ℕ → ℤ} {T : ℕ} (hT : 1 ≤ T) (h0 : h 0 = 0) :
    (0 : ℤ) ∈ pairRes r h T 0 := by
  rw [mem_pairRes]
  refine ⟨0, by simp, by simp; omega, hT, ?_⟩
  rw [mem_residentPair]
  left
  unfold curBlock blockOf
  rw [h0]; simp

/-- **No chord leaves the prefix**, and the chords of the original part are the shifted ones. -/
theorem isChord_prefix (hr : 1 ≤ r) (hD : D.Valid L) (t : Fin k) {β : ℤ} {x z : ℕ} :
    IsChord (pairRes r ((prefixDiagram D P r L).work t) (prefixDiagram D P r L).T) β x z ↔
      P ≤ x ∧ IsChord (pairRes r (D.work t) D.T) β (x - P) (z - P) := by
  have hR : ∀ y, P ≤ y → pairRes r ((prefixDiagram D P r L).work t) (prefixDiagram D P r L).T y =
      pairRes r (D.work t) D.T (y - P) := by
    intro y hy
    have e : y = P + (y - P) := by omega
    conv_lhs => rw [e]
    exact pairRes_prefix_add D hD t _
  constructor
  · rintro ⟨hxz, hx, hz, hbetw⟩
    have hxP : P ≤ x := by
      by_contra hxP
      push Not at hxP
      rw [pairRes_prefix_lt D hr hD t hxP, Finset.mem_singleton] at hx
      subst hx
      by_cases hx1 : x + 1 < P
      · exact hbetw (x + 1) (by omega) hxz (by
          rw [pairRes_prefix_lt D hr hD t hx1]; exact Finset.mem_singleton_self _)
      · -- `x = P - 1`, so slot `P` (the original slot `0`) lies strictly between
        have hzP : P < z := by omega
        by_cases hT : 1 ≤ D.T
        · apply hbetw P (by omega) hzP
          rw [hR P le_rfl, Nat.sub_self]
          exact zero_mem_pairRes_zero hr hT ((hD.1 t).1)
        · rw [hR z (by omega), pairRes_empty (by omega)] at hz
          simp at hz
    refine ⟨hxP, by omega, by rw [← hR x hxP]; exact hx, by rw [← hR z (by omega)]; exact hz, ?_⟩
    intro y h1 h2
    have := hbetw (y + P) (by omega) (by omega)
    rwa [hR _ (by omega), Nat.add_sub_cancel] at this
  · rintro ⟨hxP, hxz, hx, hz, hbetw⟩
    refine ⟨by omega, by rw [hR x hxP]; exact hx, by rw [hR z (by omega)]; exact hz, ?_⟩
    intro y h1 h2
    rw [hR y (by omega)]
    exact hbetw (y - P) (by omega) (by omega)

theorem chordEdges_prefix (hr : 1 ≤ r) (hD : D.Valid L) {e : ℕ × ℕ} :
    e ∈ (prefixDiagram D P r L).chordEdges r ↔
      P ≤ e.1 ∧ P ≤ e.2 ∧ (e.1 - P, e.2 - P) ∈ D.chordEdges r := by
  rw [mem_chordEdges, mem_chordEdges, nodes_prefix D hr]
  constructor
  · rintro ⟨h1, h2, t, β, hc⟩
    rw [isChord_prefix D hr hD] at hc
    have hxz := hc.2.1
    exact ⟨hc.1, by omega, by simp only; omega, by simp only; omega, t, β, hc.2⟩
  · rintro ⟨h1, h2, h3, h4, t, β, hc⟩
    simp only at h3 h4
    refine ⟨by omega, by omega, t, β, ?_⟩
    rw [isChord_prefix D hr hD]
    exact ⟨h1, hc⟩

theorem memEdges_prefix (hr : 1 ≤ r) {e : ℕ × ℕ} :
    e ∈ (prefixDiagram D P r L).memEdges r ↔ e.2 = e.1 + 1 ∧ e.1 + 1 < P + D.nodes r := by
  rw [mem_memEdges, nodes_prefix D hr]

theorem chordTapes_prefix (hr : 1 ≤ r) (hD : D.Valid L) (a b : ℕ) :
    (prefixDiagram D P r L).chordTapes r (P + a, P + b) = D.chordTapes r (a, b) := by
  classical
  unfold TSDiagram.chordTapes
  congr 1
  ext t
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨β, hc⟩
    rw [isChord_prefix D hr hD] at hc
    simp only [Nat.add_sub_cancel_left] at hc
    exact ⟨β, hc.2⟩
  · rintro ⟨β, hc⟩
    refine ⟨β, ?_⟩
    rw [isChord_prefix D hr hD]
    simp only [Nat.add_sub_cancel_left]
    exact ⟨Nat.le_add_right _ _, hc⟩

theorem slotOf_prefix_add {T y τ : ℕ} :
    P * r + τ ∈ slotOf r (P * r + T) (P + y) ↔ τ ∈ slotOf r T y := by
  rw [mem_slotOf, mem_slotOf]
  have : (P + y) * r = P * r + y * r := by ring
  omega

theorem rowsAt_prefix_add {n w : ℕ} (y : ℕ) :
    (prefixDiagram D P r L).rowsAt n w r (P + y) = D.rowsAt n w r y := by
  classical
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
    have hin : (prefixDiagram D P r L).inp (P * r + (τ' - P * r)) = D.inp (τ' - P * r) := by
      show (if P * r + (τ' - P * r) < P * r then _ else D.inp (P * r + (τ' - P * r) - P * r)) = _
      rw [ite_eq_right (by omega), Nat.add_sub_cancel_left]
    rw [hin] at h1 h2
    exact ⟨hi, τ' - P * r, (slotOf_prefix_add (P := P) (r := r)).1 hτ', h1, h2⟩
  · rintro ⟨hi, τ, hτ, h1, h2⟩
    have hin : (prefixDiagram D P r L).inp (P * r + τ) = D.inp τ := by
      show (if P * r + τ < P * r then _ else D.inp (P * r + τ - P * r)) = _
      rw [ite_eq_right (by omega), Nat.add_sub_cancel_left]
    refine ⟨hi, P * r + τ, (slotOf_prefix_add (P := P) (r := r)).2 hτ, ?_, ?_⟩
    · rw [hin]; exact h1
    · rw [hin]; exact h2

theorem visible_prefix_add {n w : ℕ} (y : ℕ) {L' : ℕ} (x : Fin L' → Bool) :
    (prefixDiagram D P r L).visible n w r (P + y) x = D.visible n w r y x := by
  funext d
  simp only [TSDiagram.visible, rowsAt_prefix_add]

theorem outNode_prefix (hr : 1 ≤ r) (hD : D.Valid L) (hT : 1 ≤ D.T) (o : ℕ) :
    (prefixDiagram D P r L).outNode r o = P + D.outNode r o := by
  have hN : 1 ≤ D.nodes r := by
    have := (numSlots_spec hr (T := D.T) (y := 0)).2 (by simp; omega)
    exact this
  have hout : ∀ j, (prefixDiagram D P r L).out ((P + j) * r) = D.out (j * r) := by
    intro j
    show (if (P + j) * r < P * r then 0 else D.out ((P + j) * r - P * r)) = _
    have e : (P + j) * r = P * r + j * r := by ring
    rw [ite_eq_right (by omega), e, Nat.add_sub_cancel_left]
  unfold TSDiagram.outNode
  rw [nodes_prefix D hr]
  set m := Nat.findGreatest (fun y => D.out (y * r) ≤ o) (D.nodes r - 1) with hm
  have hmspec := (Nat.findGreatest_eq_iff (P := fun y => D.out (y * r) ≤ o)).1 hm.symm
  have hqm : D.out (m * r) ≤ o := by
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · rw [h0, Nat.zero_mul, hD.2.2.2.1]; exact Nat.zero_le _
    · exact hmspec.2.1 (by omega)
  rw [Nat.findGreatest_eq_iff]
  refine ⟨by omega, fun _ => by rw [hout]; exact hqm, ?_⟩
  intro j hj1 hj2
  have e : j = P + (j - P) := by omega
  rw [e, hout]
  exact hmspec.2.2 (by omega) (by omega)

/-- The prefix slot in which row `i` starts. -/
def startSlot (n w r i : ℕ) : ℕ := i * n * w / r

theorem startSlot_injective {n w r i j : ℕ} (hr : 1 ≤ r) (hrnw : r ≤ n * w)
    (h : startSlot n w r i = startSlot n w r j) : i = j := by
  unfold startSlot at h
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hij | hij
  · have h1 : i * n * w + r ≤ j * n * w := by
      have : (i + 1) * n * w ≤ j * n * w := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hij)
      have e : (i + 1) * n * w = i * n * w + n * w := by ring
      omega
    have h2 : (i * n * w + r) / r ≤ j * n * w / r := Nat.div_le_div_right h1
    rw [Nat.add_div_right _ (by omega)] at h2
    omega
  · have h1 : j * n * w + r ≤ i * n * w := by
      have : (j + 1) * n * w ≤ i * n * w := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hij)
      have e : (j + 1) * n * w = j * n * w + n * w := by ring
      omega
    have h2 : (j * n * w + r) / r ≤ i * n * w / r := Nat.div_le_div_right h1
    rw [Nat.add_div_right _ (by omega)] at h2
    omega

theorem startSlot_lt {n w r P L i : ℕ} (hr : 1 ≤ r) (hw : 1 ≤ w) (hL : L = n * n * w)
    (hP : 2 * L ≤ P * r) (hi : i < n) : startSlot n w r i < P := by
  have hτL : i * n * w < L := by
    rw [hL]
    calc i * n * w < (i + 1) * n * w := by
          apply Nat.mul_lt_mul_of_pos_right _ hw
          exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      _ ≤ n * n * w := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hi)
  unfold startSlot
  exact (Nat.div_lt_iff_lt_mul (by omega)).2 (by omega)

/-- **Every row is read in the prefix**, in the slot where it starts. -/
theorem row_mem_prefix {n w : ℕ} (hr : 1 ≤ r) (hw : 1 ≤ w) (hL : L = n * n * w)
    (hP : 2 * L ≤ P * r) {i : ℕ} (hi : i < n) :
    startSlot n w r i < P ∧ i ∈ (prefixDiagram D P r L).rowsAt n w r (startSlot n w r i) := by
  classical
  have hτL : i * n * w < L := by
    rw [hL]
    calc i * n * w < (i + 1) * n * w := by
          apply Nat.mul_lt_mul_of_pos_right _ hw
          exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      _ ≤ n * n * w := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hi)
  have hτP : i * n * w < P * r := by omega
  refine ⟨?_, ?_⟩
  · unfold startSlot
    exact (Nat.div_lt_iff_lt_mul (by omega)).2 hτP
  · simp only [TSDiagram.rowsAt, Finset.mem_filter, Finset.mem_range]
    refine ⟨hi, i * n * w, ?_, ?_, ?_⟩
    · have := mem_slotOf_div hr (show i * n * w < (prefixDiagram D P r L).T by
        show i * n * w < P * r + D.T; omega)
      exact this
    · show ((i * n * w : ℕ) : ℤ) ≤
        (if i * n * w < P * r then sweepPos L (i * n * w) else D.inp (i * n * w - P * r))
      rw [ite_eq_left hτP, sweepPos_of_lt hτL]
    · show (if i * n * w < P * r then sweepPos L (i * n * w) else D.inp (i * n * w - P * r)) <
        (((i + 1) * n * w : ℕ) : ℤ)
      rw [ite_eq_left hτP, sweepPos_of_lt hτL]
      have : i * n * w < (i + 1) * n * w := by
        apply Nat.mul_lt_mul_of_pos_right _ hw
        exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      exact_mod_cast this

end Prefix

/-! ### Additive hints -/

section Additive

/-- Encode a vector of `s` bits as a number `< 2^s`. -/
noncomputable def encV {s : ℕ} (v : Fin s → ZMod 2) : ℕ := (Fintype.equivFin (Fin s → ZMod 2) v : ℕ)

theorem card_vec2 (s : ℕ) : Fintype.card (Fin s → ZMod 2) = 2 ^ s := by
  simp [ZMod.card]

theorem encV_lt {s : ℕ} (v : Fin s → ZMod 2) : encV v < 2 ^ s :=
  lt_of_lt_of_eq (Fintype.equivFin (Fin s → ZMod 2) v).2 (card_vec2 s)

/-- Decode a number `< 2^s` (anything else decodes to `0`). -/
noncomputable def decV {s : ℕ} (m : ℕ) : Fin s → ZMod 2 :=
  if h : m < 2 ^ s then (Fintype.equivFin (Fin s → ZMod 2)).symm ⟨m, by rw [card_vec2]; exact h⟩
  else 0

theorem decV_encV {s : ℕ} (v : Fin s → ZMod 2) : decV (encV v) = v := by
  unfold decV
  rw [dite_eq_left (encV_lt v)]
  simp [encV]

theorem decV_pack {s : ℕ} (v : Fin s → ZMod 2) (m : ℕ) : decV ((encV v + 2 ^ s * m) % 2 ^ s) = v := by
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (encV_lt v), decV_encV]

theorem unpack {s : ℕ} (v : Fin s → ZMod 2) (m : ℕ) : (encV v + 2 ^ s * m) / 2 ^ s = m := by
  rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos s), Nat.div_eq_of_lt (encV_lt v), Nat.zero_add]

/-- Row `i` of a bit function (other positions read `false`). -/
def rowOf (n w i : ℕ) (v : ℕ → Bool) : ℕ → Bool := fun d => if d / (n * w) = i then v d else false

/-- The bits of an input, as a function on `ℕ`. -/
def xbits {L : ℕ} (x : Fin L → Bool) : ℕ → Bool := fun d => if h : d < L then x ⟨d, h⟩ else false

/-- **An additive hint**: the sum over the rows of contributions `g i (row i)`. -/
noncomputable def rowSum {s : ℕ} (n w : ℕ) (g : ℕ → (ℕ → Bool) → (Fin s → ZMod 2)) {L : ℕ}
    (x : Fin L → Bool) : Fin s → ZMod 2 :=
  ∑ i ∈ Finset.range n, g i (rowOf n w i (xbits x))

/-- The partial sum over the rows starting in the prefix slots `≤ y`. -/
noncomputable def accRows {s : ℕ} (n w r : ℕ) (g : ℕ → (ℕ → Bool) → (Fin s → ZMod 2)) {L : ℕ}
    (x : Fin L → Bool) (y : ℕ) : Fin s → ZMod 2 :=
  ∑ i ∈ (Finset.range n).filter (fun i => startSlot n w r i ≤ y), g i (rowOf n w i (xbits x))

open Classical in
/-- The contribution added at prefix node `y`: that of the row starting in slot `y`, if any. -/
noncomputable def slotContrib {s : ℕ} (n w r : ℕ) (g : ℕ → (ℕ → Bool) → (Fin s → ZMod 2)) (y : ℕ)
    (v : ℕ → Bool) : Fin s → ZMod 2 :=
  if h : ∃ i < n, startSlot n w r i = y then g (Classical.choose h) (rowOf n w (Classical.choose h) v)
  else 0

/-- **The code on the prefixed diagram.** Prefix nodes pass the running sum of the row contributions
along the spine. A node of the original part reads the hint from the low `s` bits of its incoming
memory edge, unpacks the original in-values, and runs the code shifted by `z hint`; its memory edges
carry `hint + 2^s · value`. -/
noncomputable def prefixCode {k : ℕ} (D : TSDiagram k) (n w r P s : ℕ)
    (g : ℕ → (ℕ → Bool) → (Fin s → ZMod 2)) {L : ℕ} (C : NetCode)
    (z : (Fin s → ZMod 2) → (Fin L → Bool)) : NetCode where
  enc e f v :=
    if e.1 < P then
      encV ((if e.1 = 0 then 0 else decV (f (e.1 - 1, e.1))) + slotContrib n w r g e.1 v)
    else
      (if e.2 = e.1 + 1 then encV (decV (s := s) (f (e.1 - 1, e.1) % 2 ^ s)) else 0) +
        (if e.2 = e.1 + 1 then 2 ^ s else 1) *
          (shiftCode D n w r C (z (decV (f (e.1 - 1, e.1) % 2 ^ s)))).enc (e.1 - P, e.2 - P)
            (fun e' => if e'.1 + 1 = e'.2 then f (P + e'.1, P + e'.2) / 2 ^ s
              else f (P + e'.1, P + e'.2)) v
  dec o f v :=
    (shiftCode D n w r C (z (decV (f (P + D.outNode r o - 1, P + D.outNode r o) % 2 ^ s)))).dec o
      (fun e' => if e'.1 + 1 = e'.2 then f (P + e'.1, P + e'.2) / 2 ^ s
        else f (P + e'.1, P + e'.2)) v

theorem rowOf_visible {k : ℕ} (D : TSDiagram k) {n w r y i : ℕ} {L : ℕ} (x : Fin L → Bool)
    (hi : i ∈ D.rowsAt n w r y) : rowOf n w i (D.visible n w r y x) = rowOf n w i (xbits x) := by
  funext d
  unfold rowOf
  split_ifs with hd
  · simp only [TSDiagram.visible, xbits]
    split_ifs with h1 h2
    · rfl
    · exact absurd (hd ▸ hi) h2
    · rfl
  · rfl

theorem slotContrib_eq {k : ℕ} (D : TSDiagram k) {n w r P y s : ℕ} {L : ℕ}
    (g : ℕ → (ℕ → Bool) → (Fin s → ZMod 2)) (x : Fin L → Bool) (hr : 1 ≤ r) (hw : 1 ≤ w)
    (hrnw : r ≤ n * w) (hL : L = n * n * w) (hP : 2 * L ≤ P * r) :
    slotContrib n w r g y ((prefixDiagram D P r L).visible n w r y x) =
      ∑ i ∈ (Finset.range n).filter (fun i => startSlot n w r i = y),
        g i (rowOf n w i (xbits x)) := by
  classical
  unfold slotContrib
  split_ifs with h
  · have hspec := Classical.choose_spec h
    set i := Classical.choose h with hi
    have hfilter : (Finset.range n).filter (fun j => startSlot n w r j = y) = {i} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      constructor
      · rintro ⟨-, hj⟩
        exact startSlot_injective hr hrnw (hj.trans hspec.2.symm)
      · rintro rfl; exact hspec
    rw [hfilter, Finset.sum_singleton]
    congr 1
    have hmem := (row_mem_prefix D hr hw hL hP hspec.1).2
    rw [hspec.2] at hmem
    exact rowOf_visible _ x hmem
  · have hfilter : (Finset.range n).filter (fun j => startSlot n w r j = y) = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_range] at hj
      exact h ⟨j, hj.1, hj.2⟩
    rw [hfilter, Finset.sum_empty]

theorem accRows_zero {s : ℕ} {n w r : ℕ} (g : ℕ → (ℕ → Bool) → (Fin s → ZMod 2)) {L : ℕ}
    (x : Fin L → Bool) :
    accRows n w r g x 0 = ∑ i ∈ (Finset.range n).filter (fun i => startSlot n w r i = 0),
      g i (rowOf n w i (xbits x)) := by
  unfold accRows
  congr 1
  ext i
  simp

theorem accRows_succ {s : ℕ} {n w r : ℕ} (g : ℕ → (ℕ → Bool) → (Fin s → ZMod 2)) {L : ℕ}
    (x : Fin L → Bool) (y : ℕ) :
    accRows n w r g x (y + 1) = accRows n w r g x y +
      ∑ i ∈ (Finset.range n).filter (fun i => startSlot n w r i = y + 1),
        g i (rowOf n w i (xbits x)) := by
  classical
  unfold accRows
  rw [← Finset.sum_union]
  · congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union]
    omega
  · rw [Finset.disjoint_filter]
    intro i _ h1 h2
    omega

theorem accRows_full {s : ℕ} {n w r P : ℕ} (g : ℕ → (ℕ → Bool) → (Fin s → ZMod 2)) {L : ℕ}
    (x : Fin L → Bool) (hr : 1 ≤ r) (hw : 1 ≤ w) (hL : L = n * n * w) (hP : 2 * L ≤ P * r) :
    accRows n w r g x (P - 1) = rowSum n w g x := by
  classical
  unfold accRows rowSum
  congr 1
  apply Finset.filter_true_of_mem
  intro i hi
  rw [Finset.mem_range] at hi
  have h1 := startSlot_lt (P := P) hr hw hL hP hi
  omega

/-- Edges of the original part. -/
theorem mem_edges_prefix {k : ℕ} (D : TSDiagram k) {P r L : ℕ} (hr : 1 ≤ r) (hD : D.Valid L)
    (a b : ℕ) : (P + a, P + b) ∈ (prefixDiagram D P r L).edges r ↔ (a, b) ∈ D.edges r := by
  unfold TSDiagram.edges
  rw [Finset.mem_union, Finset.mem_union, memEdges_prefix D hr, chordEdges_prefix D hr hD,
    mem_memEdges]
  simp only [Nat.add_sub_cancel_left]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨-, -, h3⟩)
    · left; exact ⟨by omega, by omega⟩
    · right; exact h3
  · rintro (⟨h1, h2⟩ | h3)
    · left; exact ⟨by omega, by omega⟩
    · right; exact ⟨by omega, by omega, h3⟩

end Additive

/-! ### Correctness of the prefix code -/

section Correct

variable {k : ℕ} (D : TSDiagram k) {n w r P s L : ℕ} (g : ℕ → (ℕ → Bool) → (Fin s → ZMod 2))
  (C : NetCode) (z : (Fin s → ZMod 2) → (Fin L → Bool)) (x : Fin L → Bool)

/-- **The prefix spine carries the running sum.** -/
theorem prefix_edgeVal (hr : 1 ≤ r) (hw : 1 ≤ w) (hrnw : r ≤ n * w) (hL : L = n * n * w)
    (hP : 2 * L ≤ P * r) :
    ∀ y, y < P → (prefixCode D n w r P s g C z).edgeVal ((prefixDiagram D P r L).edges r)
      (fun u => (prefixDiagram D P r L).visible n w r u x) (y, y + 1) = encV (accRows n w r g x y) := by
  intro y
  induction y with
  | zero =>
    intro hy
    show (if (0 : ℕ) < P then _ else _) = _
    rw [ite_eq_left hy, ite_eq_left rfl, zero_add, slotContrib_eq D g x hr hw hrnw hL hP,
      accRows_zero]
  | succ y ih =>
    intro hy
    show (if y + 1 < P then _ else _) = _
    rw [ite_eq_left hy, ite_eq_right (by omega)]
    have hin : (prefixCode D n w r P s g C z).inVals ((prefixDiagram D P r L).edges r)
        (fun u => (prefixDiagram D P r L).visible n w r u x) (y + 1) (y + 1 - 1, y + 1) =
        encV (accRows n w r g x y) := by
      rw [inVals_eq, Nat.add_sub_cancel]
      have hmem : (y, y + 1) ∈ (prefixDiagram D P r L).edges r := by
        apply Finset.mem_union_left
        rw [memEdges_prefix D hr]
        exact ⟨rfl, by omega⟩
      rw [ite_eq_left ⟨hmem, rfl, by omega⟩]
      exact ih (by omega)
    rw [hin, decV_encV, slotContrib_eq D g x hr hw hrnw hL hP, accRows_succ]

/-- The edge value of the original part, given the hint and the unpacked in-values at its source. -/
theorem prefix_edgeVal_add {a b : ℕ} (hhint : decV (s := s)
      ((prefixCode D n w r P s g C z).inVals ((prefixDiagram D P r L).edges r)
        (fun u => (prefixDiagram D P r L).visible n w r u x) (P + a) (P + a - 1, P + a) % 2 ^ s) =
      rowSum n w g x)
    (hunpack : (fun e' : ℕ × ℕ => if e'.1 + 1 = e'.2 then
        (prefixCode D n w r P s g C z).inVals ((prefixDiagram D P r L).edges r)
          (fun u => (prefixDiagram D P r L).visible n w r u x) (P + a) (P + e'.1, P + e'.2) / 2 ^ s
      else (prefixCode D n w r P s g C z).inVals ((prefixDiagram D P r L).edges r)
          (fun u => (prefixDiagram D P r L).visible n w r u x) (P + a) (P + e'.1, P + e'.2)) =
      (shiftCode D n w r C (z (rowSum n w g x))).inVals (D.edges r)
        (fun u => D.visible n w r u x) a) :
    (prefixCode D n w r P s g C z).edgeVal ((prefixDiagram D P r L).edges r)
      (fun u => (prefixDiagram D P r L).visible n w r u x) (P + a, P + b) =
    (if b = a + 1 then encV (rowSum n w g x) else 0) + (if b = a + 1 then 2 ^ s else 1) *
      (shiftCode D n w r C (z (rowSum n w g x))).edgeVal (D.edges r)
        (fun u => D.visible n w r u x) (a, b) := by
  show (if P + a < P then _ else _) = _
  rw [ite_eq_right (by omega)]
  simp only [Nat.add_sub_cancel_left]
  have hcond : (P + b = P + a + 1) ↔ (b = a + 1) := by omega
  simp only [hcond]
  rw [hhint, hunpack, visible_prefix_add]
  rfl

/-- **The original part reproduces the shifted code**: at every node `P + a` the hint read from the
spine is the row sum, and the unpacked in-values are those of the code shifted by `z (row sum)`. -/
theorem prefix_main (hr : 1 ≤ r) (hw : 1 ≤ w) (hrnw : r ≤ n * w) (hL : L = n * n * w)
    (hP : 2 * L ≤ P * r) (hP1 : 1 ≤ P) (hD : D.Valid L) :
    ∀ a, a < D.nodes r →
      decV (s := s) ((prefixCode D n w r P s g C z).inVals ((prefixDiagram D P r L).edges r)
        (fun u => (prefixDiagram D P r L).visible n w r u x) (P + a) (P + a - 1, P + a) % 2 ^ s) =
        rowSum n w g x ∧
      (fun e' : ℕ × ℕ => if e'.1 + 1 = e'.2 then
          (prefixCode D n w r P s g C z).inVals ((prefixDiagram D P r L).edges r)
            (fun u => (prefixDiagram D P r L).visible n w r u x) (P + a) (P + e'.1, P + e'.2) / 2 ^ s
        else (prefixCode D n w r P s g C z).inVals ((prefixDiagram D P r L).edges r)
            (fun u => (prefixDiagram D P r L).visible n w r u x) (P + a) (P + e'.1, P + e'.2)) =
        (shiftCode D n w r C (z (rowSum n w g x))).inVals (D.edges r)
          (fun u => D.visible n w r u x) a := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
  intro haN
  refine ⟨?_, ?_⟩
  · -- the hint
    have hmem : (P + a - 1, P + a) ∈ (prefixDiagram D P r L).edges r := by
      apply Finset.mem_union_left
      rw [memEdges_prefix D hr]
      exact ⟨by simp only; omega, by simp only; omega⟩
    rw [inVals_eq, ite_eq_left ⟨hmem, rfl, by simp only; omega⟩]
    rcases Nat.eq_zero_or_pos a with h0 | hpos
    · subst h0
      have e : (P + 0 - 1, P + 0) = (P - 1, P - 1 + 1) := by
        ext <;> simp only <;> omega
      rw [e]
      show decV ((prefixCode D n w r P s g C z).edgeVal _ _ (P - 1, P - 1 + 1) % 2 ^ s) = _
      rw [prefix_edgeVal D g C z x hr hw hrnw hL hP (P - 1) (by omega),
        Nat.mod_eq_of_lt (encV_lt _), decV_encV, accRows_full g x hr hw hL hP]
    · obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
      have e : (P + (a' + 1) - 1, P + (a' + 1)) = (P + a', P + (a' + 1)) := by
        ext
        · simp only; omega
        · rfl
      rw [e]
      obtain ⟨h1, h2⟩ := ih a' (by omega) (by omega)
      show decV ((prefixCode D n w r P s g C z).edgeVal _ _ (P + a', P + (a' + 1)) % 2 ^ s) = _
      rw [prefix_edgeVal_add D g C z x h1 h2, ite_eq_left rfl, ite_eq_left rfl, decV_pack]
  · -- the unpacked in-values
    funext e'
    obtain ⟨a', b'⟩ := e'
    simp only
    rw [inVals_eq, inVals_eq]
    by_cases hc : (a', b') ∈ D.edges r ∧ b' = a ∧ a' < a
    · have hc' : (P + a', P + b') ∈ (prefixDiagram D P r L).edges r ∧ P + b' = P + a ∧
          P + a' < P + a :=
        ⟨(mem_edges_prefix D hr hD a' b').2 hc.1, by omega, by omega⟩
      rw [ite_eq_left hc', ite_eq_left hc]
      have ha'N : a' < D.nodes r := (edges_lt D _ hc.1).1
      obtain ⟨h1, h2⟩ := ih a' hc.2.2 ha'N
      have hev := prefix_edgeVal_add D g C z x (b := b') h1 h2
      simp only [NetCode.edgeVal] at hev
      rw [hev]
      by_cases hb : a' + 1 = b'
      · rw [ite_eq_left hb, ite_eq_left hb.symm, ite_eq_left hb.symm, unpack]
      · rw [ite_eq_right hb, ite_eq_right (Ne.symm hb), ite_eq_right (Ne.symm hb), Nat.zero_add,
          Nat.one_mul]
    · have hc' : ¬ ((P + a', P + b') ∈ (prefixDiagram D P r L).edges r ∧ P + b' = P + a ∧
          P + a' < P + a) := by
        rintro ⟨h1, h2, h3⟩
        exact hc ⟨(mem_edges_prefix D hr hD a' b').1 h1, by omega, by omega⟩
      rw [ite_eq_right hc', ite_eq_right hc]
      split_ifs <;> simp

end Correct

/-! ### The code on the prefixed diagram solves complete exchange on every input -/

/-- **An additive hint can be removed, input by input.** Let `C` solve complete exchange on `F` at
the profile capacities of `D`, and let the row sum of `x` shift it into `F`:
`x ⊕ z (Σ_i g_i(row i)) ∈ F`. Then on the diagram with an input sweep prepended, the prefix code
solves complete exchange on `x`, at the per-node blocks plus `s` bits per memory edge. -/
theorem prefix_solves_at {k : ℕ} (D : TSDiagram k) {n G P s : ℕ} (hG : 1 ≤ G) (hn : 1 ≤ n)
    (hD : D.Valid (n * n * entryBits n))
    (hP : 2 * (n * n * entryBits n) ≤ P * blockSize G n) (hP1 : 1 ≤ P)
    (g : ℕ → (ℕ → Bool) → (Fin s → ZMod 2)) {C : NetCode}
    (z : (Fin s → ZMod 2) → (Fin (n * n * entryBits n) → Bool))
    {F : Set (Fin (n * n * entryBits n) → Bool)} (hsol : D.Solves n G (D.profileCap n G) F C)
    (x₀ : Fin (n * n * entryBits n) → Bool)
    (hzx : xorVec x₀ (z (rowSum n (entryBits n) g x₀)) ∈ F) :
    (prefixDiagram D P (blockSize G n) (n * n * entryBits n)).Solves n G
      ((prefixDiagram D P (blockSize G n) (n * n * entryBits n)).blockCap n G
        (fun y => ∑ t, (pairRes (blockSize G n)
          ((prefixDiagram D P (blockSize G n) (n * n * entryBits n)).work t)
          (prefixDiagram D P (blockSize G n) (n * n * entryBits n)).T y).card) s)
      {x₀} (prefixCode D n (entryBits n) (blockSize G n) P s g C z) := by
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  have hz : ∀ x', x' = x → xorVec x' (z (rowSum n (entryBits n) g x')) ∈ F := by
    intro x' hx'; subst hx'; exact hzx
  have hr : 1 ≤ blockSize G n := one_le_blockSize hG hn
  have hw : 1 ≤ entryBits n := by unfold entryBits; omega
  have hrnw : blockSize G n ≤ n * entryBits n := blockSize_le hG
  have hL1 : 1 ≤ n * n * entryBits n := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hT : 1 ≤ D.T := one_le_T hD hL1
  obtain ⟨hedge, hout⟩ := solves_shiftCode D hsol (z (rowSum n (entryBits n) g x)) x (hz x rfl)
  have hmain := prefix_main D g C z x hr hw hrnw rfl hP hP1 hD
  refine ⟨fun e he => ?_, fun d hd => ?_⟩
  · by_cases he1 : e.1 < P
    · -- a prefix memory edge
      have hm : e ∈ (prefixDiagram D P (blockSize G n) (n * n * entryBits n)).memEdges
          (blockSize G n) := by
        rcases Finset.mem_union.1 he with hm | hc
        · exact hm
        · rw [chordEdges_prefix D hr hD] at hc; omega
      have he2 := ((memEdges_prefix D hr).1 hm).1
      rw [blockCap_mem _ hm]
      obtain ⟨y, b⟩ := e
      simp only at he1 he2
      subst he2
      rw [prefix_edgeVal D g C z x hr hw hrnw rfl hP y he1]
      calc encV (accRows n (entryBits n) (blockSize G n) g x y) < 2 ^ s := encV_lt _
        _ ≤ 2 ^ (_ * (blockSize G n * G) + s) := Nat.pow_le_pow_right (by norm_num) (by omega)
    · -- an edge of the original part
      obtain ⟨a, b⟩ := e
      simp only at he1
      obtain ⟨a', rfl⟩ : ∃ a', a = P + a' := ⟨a - P, by omega⟩
      have hb : P ≤ b := by
        have := edges_fst_lt _ _ he
        simp only at this; omega
      obtain ⟨b', rfl⟩ : ∃ b', b = P + b' := ⟨b - P, by omega⟩
      have heD := (mem_edges_prefix D hr hD a' b').1 he
      have ha'N : a' < D.nodes (blockSize G n) := (edges_lt D _ heD).1
      obtain ⟨h1, h2⟩ := hmain a' ha'N
      rw [prefix_edgeVal_add D g C z x h1 h2]
      have hev := hedge (a', b') heD
      by_cases hmem : b' = a' + 1
      · -- memory edge: hint plus `2^s` times the value
        have hmD : (a', b') ∈ D.memEdges (blockSize G n) := by
          rw [mem_memEdges]; exact ⟨hmem, by have := (edges_lt D _ heD).2; simp only; omega⟩
        have hm' : (P + a', P + b') ∈ (prefixDiagram D P (blockSize G n)
            (n * n * entryBits n)).memEdges (blockSize G n) := by
          rw [memEdges_prefix D hr]
          have := (edges_lt D _ heD).2
          exact ⟨by simp only; omega, by simp only; omega⟩
        rw [ite_eq_left hmem, ite_eq_left hmem, blockCap_mem _ hm']
        unfold TSDiagram.profileCap at hev
        rw [blockCap_mem D hmD, Nat.add_zero] at hev
        simp only at hev ⊢
        rw [pairRes_prefix_add' D hD]
        have h3 := encV_lt (rowSum n (entryBits n) g x)
        set V := (shiftCode D n (entryBits n) (blockSize G n) C
          (z (rowSum n (entryBits n) g x))).edgeVal (D.edges (blockSize G n))
          (fun u => D.visible n (entryBits n) (blockSize G n) u x) (a', b') with hV
        set c := (∑ t, (pairRes (blockSize G n) (D.work t) D.T a').card) *
          (blockSize G n * G) with hc
        calc encV (rowSum n (entryBits n) g x) + 2 ^ s * V
            < 2 ^ s + 2 ^ s * V := by omega
          _ = 2 ^ s * (V + 1) := by ring
          _ ≤ 2 ^ s * 2 ^ c := Nat.mul_le_mul_left _ hev
          _ = 2 ^ (c + s) := by rw [← pow_add, Nat.add_comm]
      · -- chord edge: the value itself
        have hcD : (a', b') ∈ D.chordEdges (blockSize G n) := by
          rcases Finset.mem_union.1 heD with hm | hc
          · rw [mem_memEdges] at hm; exact absurd hm.1 hmem
          · exact hc
        have hc' : (P + a', P + b') ∈ (prefixDiagram D P (blockSize G n)
            (n * n * entryBits n)).chordEdges (blockSize G n) := by
          rw [chordEdges_prefix D hr hD]
          simp only [Nat.add_sub_cancel_left]
          exact ⟨Nat.le_add_right _ _, Nat.le_add_right _ _, hcD⟩
        rw [ite_eq_right hmem, ite_eq_right hmem, Nat.zero_add, Nat.one_mul,
          blockCap_chord _ hc', chordTapes_prefix D hr hD]
        unfold TSDiagram.profileCap at hev
        rw [blockCap_chord D hcD] at hev
        exact hev
  · -- the outputs
    have ho := hout d hd
    have hu : (prefixDiagram D P (blockSize G n) (n * n * entryBits n)).outNode (blockSize G n)
        (tpos n (entryBits n) d) = P + D.outNode (blockSize G n) (tpos n (entryBits n) d) :=
      outNode_prefix D hr hD hT _
    have haN := outNode_lt hD hr hL1 (tpos n (entryBits n) d)
    obtain ⟨h1, h2⟩ := hmain _ haN
    show (prefixCode D n (entryBits n) (blockSize G n) P s g C z).dec _ _ _ = _
    rw [hu]
    show (shiftCode D n (entryBits n) (blockSize G n) C (z (decV (_ % 2 ^ s)))).dec _ _ _ = _
    rw [h1, h2]
    beta_reduce
    rw [visible_prefix_add]
    exact ho

/-! ### Plain ⟹ robust for sets covered by an additive hint, in particular affine sets -/

/-- **An additive hint can be removed.** Let `C` solve complete exchange on `F` at the profile
capacities of `D`, and let `z` shift every input into `F` by its row sum: `x ⊕ z (Σ_i g_i(row i)) ∈ F`.
Then on the diagram with an input sweep prepended, the prefix code solves complete exchange on
**every** input, at the per-node blocks plus `s` bits per memory edge. -/
theorem prefix_solves {k : ℕ} (D : TSDiagram k) {n G P s : ℕ} (hG : 1 ≤ G) (hn : 1 ≤ n)
    (hD : D.Valid (n * n * entryBits n))
    (hP : 2 * (n * n * entryBits n) ≤ P * blockSize G n) (hP1 : 1 ≤ P)
    (g : ℕ → (ℕ → Bool) → (Fin s → ZMod 2)) {C : NetCode}
    (z : (Fin s → ZMod 2) → (Fin (n * n * entryBits n) → Bool))
    {F : Set (Fin (n * n * entryBits n) → Bool)} (hsol : D.Solves n G (D.profileCap n G) F C)
    (hz : ∀ x, xorVec x (z (rowSum n (entryBits n) g x)) ∈ F) :
    (prefixDiagram D P (blockSize G n) (n * n * entryBits n)).Solves n G
      ((prefixDiagram D P (blockSize G n) (n * n * entryBits n)).blockCap n G
        (fun y => ∑ t, (pairRes (blockSize G n)
          ((prefixDiagram D P (blockSize G n) (n * n * entryBits n)).work t)
          (prefixDiagram D P (blockSize G n) (n * n * entryBits n)).T y).card) s)
      Set.univ (prefixCode D n (entryBits n) (blockSize G n) P s g C z) :=
  fun x _ => prefix_solves_at D hG hn hD hP hP1 g z hsol x (hz x) x rfl

/-- **Plain ⟹ no code on any set that an additive hint covers.** Under `NoCode_TM`: for all
constants and all large `n`, no code solves complete exchange at the profile capacities on a set `F`
for which some row-additive hint of `s ≤ C n w` bits and a shift table put every input into `F`. -/
theorem noCode_additive_of_noCode (h : NoCode_TM) (k G c C : ℕ) (hG : 1 ≤ G) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
      ∀ (F : Set (Fin (n * n * entryBits n) → Bool)) (s : ℕ), s ≤ C * (n * entryBits n) →
      ∀ (g : ℕ → (ℕ → Bool) → (Fin s → ZMod 2))
        (z : (Fin s → ZMod 2) → (Fin (n * n * entryBits n) → Bool)),
        (∀ x, xorVec x (z (rowSum n (entryBits n) g x)) ∈ F) →
      ∀ code : NetCode, ¬ D.Solves n G (D.profileCap n G) F code := by
  obtain ⟨n₀, hn₀⟩ := h (k + C) G (c + 2 * G) hG
  refine ⟨max n₀ 1, fun n hn D hD hT F s hs g z hz code hsol => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hr : 1 ≤ blockSize G n := one_le_blockSize hG hn1
  have hrnw : blockSize G n ≤ n * entryBits n := blockSize_le hG
  have hrG : n * entryBits n ≤ blockSize G n * G := blockSize_mul_ge hG
  set P := 2 * n * G with hPdef
  have hP : 2 * (n * n * entryBits n) ≤ P * blockSize G n := by
    calc 2 * (n * n * entryBits n) = 2 * n * (n * entryBits n) := by ring
      _ ≤ 2 * n * (blockSize G n * G) := Nat.mul_le_mul_left _ hrG
      _ = P * blockSize G n := by rw [hPdef]; ring
  have hP1 : 1 ≤ P := by rw [hPdef]; have := Nat.mul_le_mul hn1 hG; nlinarith
  have hsol' := prefix_solves D hG hn1 hD hP hP1 g z hsol hz
  have hsB : s ≤ C * (blockSize G n * G) := le_trans hs (Nat.mul_le_mul_left _ hrG)
  have hsol'' := solves_profileCap_addTapes (a := C) hr hsB hsol'
  refine hn₀ n (le_trans (le_max_left _ _) hn) _ (valid_addTapes _ (valid_prefix D hD hP) C) ?_ _
    hsol''
  rw [T_addTapes]
  show P * blockSize G n + D.T ≤ (c + 2 * G) * (n * n * entryBits n)
  have h1 : P * blockSize G n ≤ 2 * G * (n * n * entryBits n) := by
    calc P * blockSize G n ≤ P * (n * entryBits n) := Nat.mul_le_mul_left _ hrnw
      _ = 2 * G * (n * n * entryBits n) := by rw [hPdef]; ring
  have h2 : (c + 2 * G) * (n * n * entryBits n) =
      c * (n * n * entryBits n) + 2 * G * (n * n * entryBits n) := by ring
  omega

/-- XOR of inputs is additive on row contributions. -/
theorem rowOf_xbits_xorVec {L n w i : ℕ} (x y : Fin L → Bool) :
    rowOf n w i (xbits (xorVec x y)) =
      fun d => xor (rowOf n w i (xbits x) d) (rowOf n w i (xbits y) d) := by
  funext d
  simp only [rowOf, xbits, xorVec]
  split_ifs <;> simp

/-- **Plain ⟹ no code on affine sets** (and on any set containing one). Under `NoCode_TM`: for all
constants and all large `n`, no code solves complete exchange at the profile capacities on a nonempty
affine set `{x | Σ_i g_i(row i of x) = b}` given by additive row maps into `s ≤ C n w` bits (every
affine subspace of codimension `≤ C n w` has this form). -/
theorem noCode_affine_of_noCode (h : NoCode_TM) (k G c C : ℕ) (hG : 1 ≤ G) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
      ∀ (s : ℕ), s ≤ C * (n * entryBits n) →
      ∀ (g : ℕ → (ℕ → Bool) → (Fin s → ZMod 2)),
        (∀ i (u v : ℕ → Bool), g i (fun d => xor (u d) (v d)) = g i u + g i v) →
      ∀ (b : Fin s → ZMod 2), (∃ x₀ : Fin (n * n * entryBits n) → Bool, rowSum n (entryBits n) g x₀ = b) →
      ∀ code : NetCode,
        ¬ D.Solves n G (D.profileCap n G) {x | rowSum n (entryBits n) g x = b} code := by
  classical
  obtain ⟨n₀, hn₀⟩ := noCode_additive_of_noCode h k G c C hG
  refine ⟨n₀, fun n hn D hD hT s hs g hg b ⟨x₀, hx₀⟩ code hsol => ?_⟩
  -- additivity of the row sum
  have hadd : ∀ x y : Fin (n * n * entryBits n) → Bool,
      rowSum n (entryBits n) g (xorVec x y) = rowSum n (entryBits n) g x + rowSum n (entryBits n) g y := by
    intro x y
    unfold rowSum
    rw [← Finset.sum_add_distrib]
    congr 1
    funext i
    rw [rowOf_xbits_xorVec, hg]
  -- the shift table: a preimage of the syndrome, moved by `x₀`
  let z : (Fin s → ZMod 2) → (Fin (n * n * entryBits n) → Bool) := fun σ =>
    if hσ : ∃ y, rowSum n (entryBits n) g y = σ then xorVec (Classical.choose hσ) x₀ else x₀
  refine hn₀ n hn D hD hT _ s hs g z (fun x => ?_) code hsol
  have hσ : ∃ y, rowSum n (entryBits n) g y = rowSum n (entryBits n) g x := ⟨x, rfl⟩
  show rowSum n (entryBits n) g (xorVec x (z (rowSum n (entryBits n) g x))) = b
  simp only [z, dite_eq_left hσ]
  rw [hadd, hadd, Classical.choose_spec hσ, hx₀]
  rw [← add_assoc, ← two_smul (ZMod 2) (rowSum n (entryBits n) g x)]
  have h2 : (2 : ZMod 2) = 0 := rfl
  rw [h2, zero_smul, zero_add]

/-- **Plain ⟹ no code on any set containing a nonempty affine set of codimension `≤ C n w`.** -/
theorem noCode_of_affine_subset (h : NoCode_TM) (k G c C : ℕ) (hG : 1 ≤ G) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
      ∀ (F : Set (Fin (n * n * entryBits n) → Bool)) (s : ℕ), s ≤ C * (n * entryBits n) →
      ∀ (g : ℕ → (ℕ → Bool) → (Fin s → ZMod 2)),
        (∀ i (u v : ℕ → Bool), g i (fun d => xor (u d) (v d)) = g i u + g i v) →
      ∀ (b : Fin s → ZMod 2), (∃ x₀ : Fin (n * n * entryBits n) → Bool, rowSum n (entryBits n) g x₀ = b) →
        {x | rowSum n (entryBits n) g x = b} ⊆ F →
      ∀ code : NetCode, ¬ D.Solves n G (D.profileCap n G) F code := by
  obtain ⟨n₀, hn₀⟩ := noCode_affine_of_noCode h k G c C hG
  exact ⟨n₀, fun n hn D hD hT F s hs g hg b hb hsub code hsol =>
    hn₀ n hn D hD hT s hs g hg b hb code (fun x hx => hsol x (hsub hx))⟩

end Transpose.Tape.Impl
