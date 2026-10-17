import Transpose.Tape.PlainRobust.CESelectNet

/-!
# A prefix computation followed by a diagram: the network

`concatDiagram Pre D P r` runs an arbitrary diagram `Pre` (its own `k₁` tapes) and then `D` (fresh
`k₂` tapes), on `k₁ + k₂` tapes:
* **prefix** (slots `< ⌈T_Pre/r⌉`): `Pre`'s walks, parked afterwards; `Pre`'s input walk;
* **return** (slots up to `P`): the input head walks back to cell `0` (`epiWalk p₀ 1`);
* **main part** (slots `≥ P`): `D`'s walks on the fresh tapes, delayed by `P r` steps (parked at `0`
  before), and `D`'s input walk and output schedule. Nothing is output before.

The block network contains `Pre`'s network in the prefix (`pairRes_concat_left`,
`isChord_concat_left`, `rowsAt_concat_left`) and `D`'s network shifted by `P` in the main part
(`mem_edges_concat_add`, `rowsAt_concat_add`, `outNode_concat`); no chord enters the main part from
before (`concat_edge_into_main`).
-/

namespace Transpose.Tape.Impl

open Transpose TSDiagram

/-- The walks of a diagram start at cell `0` and move by unit steps (no condition on the output). -/
def _root_.Transpose.Tape.TSDiagram.WalksOK {k : ℕ} (D : TSDiagram k) : Prop :=
  (∀ t, D.work t 0 = 0 ∧ UnitSteps (D.work t)) ∧ D.inp 0 = 0 ∧ UnitSteps D.inp

/-- **`Pre` followed by `D`.** -/
def concatDiagram {k₁ k₂ : ℕ} (Pre : TSDiagram k₁) (D : TSDiagram k₂) (P r : ℕ) :
    TSDiagram (k₁ + k₂) where
  T := P * r + D.T
  work := Fin.addCases (motive := fun _ => ℕ → ℤ)
    (fun t => parkWalk (Pre.nodes r * r) (Pre.work t)) (fun t => delayWalk (P * r) (D.work t))
  inp := fun τ => if τ < Pre.nodes r * r then Pre.inp τ
    else if τ < P * r then epiWalk (Pre.inp (Pre.nodes r * r)) 1 (τ - Pre.nodes r * r)
    else D.inp (τ - P * r)
  out := fun τ => if τ < P * r then 0 else D.out (τ - P * r)

/-- Room for the prefix and the return walk. -/
def ConcatRoom {k₁ : ℕ} (Pre : TSDiagram k₁) (P r : ℕ) : Prop :=
  2 * (Pre.nodes r * r) + 2 * r ≤ P * r

section Concat

variable {k₁ k₂ : ℕ} (Pre : TSDiagram k₁) (D : TSDiagram k₂) {P r : ℕ}

theorem work_concat_left (t : Fin k₁) :
    (concatDiagram Pre D P r).work (Fin.castAdd k₂ t) = parkWalk (Pre.nodes r * r) (Pre.work t) := by
  simp only [concatDiagram, Fin.addCases_left]

theorem work_concat_right (t : Fin k₂) :
    (concatDiagram Pre D P r).work (Fin.natAdd k₁ t) = delayWalk (P * r) (D.work t) := by
  simp only [concatDiagram, Fin.addCases_right]

theorem T_concat : (concatDiagram Pre D P r).T = P * r + D.T := rfl

theorem nodes_concat (hr : 1 ≤ r) : (concatDiagram Pre D P r).nodes r = P + D.nodes r :=
  nodes_prefix D (L := 0) hr

theorem concatRoom_nodes {Pre : TSDiagram k₁} (hr : 1 ≤ r) (hP : ConcatRoom Pre P r) :
    Pre.nodes r + 2 ≤ P := by
  unfold ConcatRoom at hP
  have : (Pre.nodes r + 2) * r ≤ P * r := by nlinarith
  exact Nat.le_of_mul_le_mul_right this (by omega)

theorem valid_concat {L : ℕ} (hPre : Pre.WalksOK) (hD : D.Valid L) (hr : 1 ≤ r)
    (hP : ConcatRoom Pre P r) : (concatDiagram Pre D P r).Valid L := by
  obtain ⟨hwork, hinp0, hinp⟩ := hPre
  obtain ⟨hDwork, hDinp0, hDinp, hDout0, hDout, hDoutT⟩ := hD
  have hp₀ : (Pre.inp (Pre.nodes r * r)).natAbs ≤ Pre.nodes r * r := by
    have := unitSteps_dist hinp (Nat.zero_le (Pre.nodes r * r))
    rw [hinp0] at this
    simp only [sub_zero, Int.abs_eq_natAbs] at this
    omega
  unfold ConcatRoom at hP
  refine ⟨fun t => ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · refine Fin.addCases (motive := fun t => (concatDiagram Pre D P r).work t 0 = 0) (fun t => ?_)
      (fun t => ?_) t
    · rw [work_concat_left, parkWalk_of_le _ (Nat.zero_le _)]; exact (hwork t).1
    · rw [work_concat_right]
      unfold delayWalk
      split_ifs
      · rfl
      · simpa using (hDwork t).1
  · refine Fin.addCases (motive := fun t => UnitSteps ((concatDiagram Pre D P r).work t))
      (fun t => ?_) (fun t => ?_) t
    · rw [work_concat_left]; exact unitSteps_parkWalk (hwork t).2
    · rw [work_concat_right]; exact unitSteps_delayWalk (hDwork t).1 (hDwork t).2
  · show (if 0 < Pre.nodes r * r then Pre.inp 0 else _) = 0
    split_ifs with h1 h2
    · exact hinp0
    · rw [Nat.zero_sub, epiWalk_zero]
      have : Pre.nodes r * r = 0 := by omega
      rw [this]; exact hinp0
    · omega
  · intro τ
    show |(if τ + 1 < Pre.nodes r * r then Pre.inp (τ + 1)
        else if τ + 1 < P * r then epiWalk (Pre.inp (Pre.nodes r * r)) 1 (τ + 1 - Pre.nodes r * r)
        else D.inp (τ + 1 - P * r)) -
      (if τ < Pre.nodes r * r then Pre.inp τ
        else if τ < P * r then epiWalk (Pre.inp (Pre.nodes r * r)) 1 (τ - Pre.nodes r * r)
        else D.inp (τ - P * r))| ≤ 1
    by_cases h1 : τ + 1 < Pre.nodes r * r
    · rw [ite_eq_left h1, ite_eq_left (show τ < Pre.nodes r * r by omega)]
      exact hinp τ
    · by_cases h2 : τ < Pre.nodes r * r
      · rw [ite_eq_right h1, ite_eq_left h2, ite_eq_left (show τ + 1 < P * r by omega)]
        have e : τ + 1 - Pre.nodes r * r = 0 := by omega
        have e' : τ + 1 = Pre.nodes r * r := by omega
        rw [e, epiWalk_zero, ← e']
        exact hinp τ
      · rw [ite_eq_right h1, ite_eq_right h2]
        by_cases h3 : τ + 1 < P * r
        · rw [ite_eq_left h3, ite_eq_left (show τ < P * r by omega)]
          have e : τ + 1 - Pre.nodes r * r = τ - Pre.nodes r * r + 1 := by omega
          rw [e]
          exact epiWalk_step _ _ _
        · by_cases h4 : τ < P * r
          · rw [ite_eq_right h3, ite_eq_left h4]
            have e : τ + 1 - P * r = 0 := by omega
            rw [e, hDinp0, epiWalk_end _ (by omega)]; simp
          · rw [ite_eq_right h3, ite_eq_right h4]
            have e : τ + 1 - P * r = τ - P * r + 1 := by omega
            rw [e]
            exact hDinp _
  · show (if 0 < P * r then 0 else D.out (0 - P * r)) = 0
    split_ifs
    · rfl
    · simpa using hDout0
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
        rw [e, hDout0]; omega
      · rw [ite_eq_right h1, ite_eq_right h2]
        have e : τ + 1 - P * r = τ - P * r + 1 := by omega
        rw [e]
        exact hDout (τ - P * r)
  · intro τ hτ
    show (if τ < P * r then 0 else D.out (τ - P * r)) = L
    have hτ' : P * r + D.T ≤ τ := hτ
    rw [ite_eq_right (show ¬ τ < P * r by omega)]
    exact hDoutT _ (by omega)

/-! #### The prefix -/

theorem pairRes_concat_left (hr : 1 ≤ r) (t : Fin k₁) (y : ℕ) (hP : Pre.nodes r * r ≤ P * r) :
    pairRes r (Pre.work t) Pre.T y ⊆
      pairRes r ((concatDiagram Pre D P r).work (Fin.castAdd k₂ t)) (concatDiagram Pre D P r).T y := by
  rw [work_concat_left]
  have hT1 : Pre.T ≤ Pre.nodes r * r := T_le_nodes_mul (D := Pre) hr
  apply pairRes_sub_of_agree (by show Pre.T ≤ P * r + D.T; omega)
  intro σ hσ
  rw [parkWalk_of_le _ (by omega)]

theorem pairRes_concat_left_eq (hr : 1 ≤ r) (t : Fin k₁) {y : ℕ} (hy : y + 1 < Pre.nodes r)
    (hP : Pre.nodes r * r ≤ P * r) :
    pairRes r ((concatDiagram Pre D P r).work (Fin.castAdd k₂ t)) (concatDiagram Pre D P r).T y =
      pairRes r (Pre.work t) Pre.T y := by
  have hfull := slot_full Pre hr hy
  have e : (y + 1) * r = y * r + r := by ring
  have hT1 : Pre.T ≤ Pre.nodes r * r := T_le_nodes_mul (D := Pre) hr
  rw [work_concat_left]
  apply pairRes_congr (by show y * r + r ≤ P * r + D.T; omega) (by omega)
  intro σ hσ
  rw [parkWalk_of_le _ (by omega)]

theorem isChord_concat_left (hr : 1 ≤ r) (t : Fin k₁) {β : ℤ} {x z : ℕ} (hz : z < Pre.nodes r)
    (hP : Pre.nodes r * r ≤ P * r) (hc : IsChord (pairRes r (Pre.work t) Pre.T) β x z) :
    IsChord (pairRes r ((concatDiagram Pre D P r).work (Fin.castAdd k₂ t))
      (concatDiagram Pre D P r).T) β x z := by
  obtain ⟨hxz, hx, hz', hbetw⟩ := hc
  refine ⟨hxz, ?_, pairRes_concat_left Pre D hr t z hP hz', ?_⟩
  · rw [pairRes_concat_left_eq Pre D hr t (by omega) hP]; exact hx
  · intro y h1 h2
    rw [pairRes_concat_left_eq Pre D hr t (by omega) hP]
    exact hbetw y h1 h2

theorem isChord_concat_left_le (hr : 1 ≤ r) (t : Fin k₁) {β : ℤ} {x z : ℕ}
    (hc : IsChord (pairRes r ((concatDiagram Pre D P r).work (Fin.castAdd k₂ t))
      (concatDiagram Pre D P r).T) β x z) : z ≤ Pre.nodes r := by
  by_contra hz
  push Not at hz
  obtain ⟨hxz, -, hzR, hbetw⟩ := hc
  rw [work_concat_left] at hzR hbetw
  have hzT : z * r < (concatDiagram Pre D P r).T := by
    by_contra h
    push Not at h
    rw [pairRes_empty h] at hzR
    simp at hzR
  have hz1 : Pre.nodes r * r ≤ (z - 1) * r := Nat.mul_le_mul_right _ (by omega)
  have hz1T : (z - 1) * r < (concatDiagram Pre D P r).T :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ (by omega)) hzT
  apply hbetw (z - 1) (by omega) (by omega)
  rw [pairRes_park _ hz1 hz1T hr]
  rwa [pairRes_park _ (le_trans hz1 (Nat.mul_le_mul_right _ (by omega))) hzT hr] at hzR

/-! #### The main part -/

theorem pairRes_concat_right (hD : D.Valid L) (t : Fin k₂) (y : ℕ) :
    pairRes r ((concatDiagram Pre D P r).work (Fin.natAdd k₁ t)) (concatDiagram Pre D P r).T
      (P + y) = pairRes r (D.work t) D.T y := by
  rw [work_concat_right]
  exact pairRes_delayWalk_add ((hD.1 t).1) y

theorem isChord_concat_right {L : ℕ} (hr : 1 ≤ r) (hD : D.Valid L) (t : Fin k₂) {β : ℤ} {x z : ℕ} :
    IsChord (pairRes r ((concatDiagram Pre D P r).work (Fin.natAdd k₁ t))
      (concatDiagram Pre D P r).T) β x z ↔
      P ≤ x ∧ IsChord (pairRes r (D.work t) D.T) β (x - P) (z - P) := by
  rw [work_concat_right]
  exact isChord_prefix D (L := L) hr hD t

theorem concat_chord_cases {L : ℕ} (hr : 1 ≤ r) (hD : D.Valid L) {x z : ℕ}
    (h : ∃ (t : Fin (k₁ + k₂)) (β : ℤ),
      IsChord (pairRes r ((concatDiagram Pre D P r).work t) (concatDiagram Pre D P r).T) β x z) :
    z ≤ Pre.nodes r ∨ (P ≤ x ∧ ∃ (t : Fin k₂) (β : ℤ),
      IsChord (pairRes r (D.work t) D.T) β (x - P) (z - P)) := by
  obtain ⟨t, β, hc⟩ := h
  induction t using Fin.addCases with
  | left t => exact Or.inl (isChord_concat_left_le Pre D hr t hc)
  | right t =>
    rw [isChord_concat_right Pre D hr hD] at hc
    exact Or.inr ⟨hc.1, t, β, hc.2⟩

theorem mem_chordEdges_concat_right {L : ℕ} (hr : 1 ≤ r) (hD : D.Valid L) {a b : ℕ}
    (h : (a, b) ∈ D.chordEdges r) : (P + a, P + b) ∈ (concatDiagram Pre D P r).chordEdges r := by
  rw [mem_chordEdges] at h ⊢
  obtain ⟨h1, h2, t, β, hc⟩ := h
  rw [nodes_concat Pre D hr]
  refine ⟨by simp only; omega, by simp only; omega, Fin.natAdd k₁ t, β, ?_⟩
  rw [isChord_concat_right Pre D hr hD]
  simp only [Nat.add_sub_cancel_left]
  exact ⟨Nat.le_add_right _ _, hc⟩

theorem mem_chordEdges_concat_left (hr : 1 ≤ r) (hP : Pre.nodes r * r ≤ P * r) {e : ℕ × ℕ}
    (h : e ∈ Pre.chordEdges r) : e ∈ (concatDiagram Pre D P r).chordEdges r := by
  rw [mem_chordEdges] at h ⊢
  obtain ⟨h1, h2, t, β, hc⟩ := h
  have hPN : Pre.nodes r ≤ P := Nat.le_of_mul_le_mul_right hP (by omega)
  rw [nodes_concat Pre D hr]
  exact ⟨by omega, by omega, Fin.castAdd k₂ t, β, isChord_concat_left Pre D hr t h2 hP hc⟩

/-- Every edge of `Pre` is an edge of the prefix. -/
theorem edges_concat_left (hr : 1 ≤ r) (hP : Pre.nodes r * r ≤ P * r) {e : ℕ × ℕ}
    (h : e ∈ Pre.edges r) : e ∈ (concatDiagram Pre D P r).edges r := by
  have hPN : Pre.nodes r ≤ P := Nat.le_of_mul_le_mul_right hP (by omega)
  rcases Finset.mem_union.1 h with hm | hc
  · apply Finset.mem_union_left
    rw [mem_memEdges] at hm ⊢
    rw [nodes_concat Pre D hr]
    omega
  · exact Finset.mem_union_right _ (mem_chordEdges_concat_left Pre D hr hP hc)

/-- **The edges of the main part are `D`'s, shifted.** -/
theorem mem_edges_concat_add {L : ℕ} (hr : 1 ≤ r) (hD : D.Valid L) (hP : Pre.nodes r < P)
    (a b : ℕ) : (P + a, P + b) ∈ (concatDiagram Pre D P r).edges r ↔ (a, b) ∈ D.edges r := by
  constructor
  · intro h
    rcases Finset.mem_union.1 h with hm | hc
    · apply Finset.mem_union_left
      rw [mem_memEdges] at hm ⊢
      rw [nodes_concat Pre D hr] at hm
      simp only at hm ⊢
      omega
    · apply Finset.mem_union_right
      rw [mem_chordEdges] at hc
      obtain ⟨h1, h2, hh⟩ := hc
      rcases concat_chord_cases Pre D hr hD hh with hz | ⟨-, t, β, hc'⟩
      · simp only at hz; omega
      · simp only [Nat.add_sub_cancel_left] at hc'
        rw [nodes_concat Pre D hr] at h1 h2
        rw [mem_chordEdges]
        exact ⟨by simp only at h1 ⊢; omega, by simp only at h2 ⊢; omega, t, β, hc'⟩
  · intro h
    rcases Finset.mem_union.1 h with hm | hc
    · apply Finset.mem_union_left
      rw [mem_memEdges] at hm ⊢
      rw [nodes_concat Pre D hr]
      simp only at hm ⊢
      omega
    · exact Finset.mem_union_right _ (mem_chordEdges_concat_right Pre D hr hD hc)

/-- **No chord enters the main part**: an edge into a node `≥ P` from a node `< P` is the memory edge
`P - 1 → P`. -/
theorem concat_edge_into_main {L : ℕ} (hr : 1 ≤ r) (hD : D.Valid L) (hP : Pre.nodes r < P)
    {e : ℕ × ℕ} (he : e ∈ (concatDiagram Pre D P r).edges r) (h1 : e.1 < P) (h2 : P ≤ e.2) :
    e = (P - 1, P) := by
  rcases Finset.mem_union.1 he with hm | hc
  · rw [mem_memEdges] at hm
    obtain ⟨a, b⟩ := e
    simp only at hm h1 h2 ⊢
    ext <;> simp only <;> omega
  · rw [mem_chordEdges] at hc
    obtain ⟨-, -, hh⟩ := hc
    rcases concat_chord_cases Pre D hr hD hh with hz | ⟨hx, -⟩
    · omega
    · omega

/-! #### Capacities -/

theorem resSum_concat_left (hr : 1 ≤ r) (hP : Pre.nodes r * r ≤ P * r) (y : ℕ) :
    ∑ t, (pairRes r (Pre.work t) Pre.T y).card ≤
      ∑ t, (pairRes r ((concatDiagram Pre D P r).work t) (concatDiagram Pre D P r).T y).card := by
  rw [Fin.sum_univ_add]
  calc ∑ t, (pairRes r (Pre.work t) Pre.T y).card
      ≤ ∑ t : Fin k₁, (pairRes r ((concatDiagram Pre D P r).work (Fin.castAdd k₂ t))
          (concatDiagram Pre D P r).T y).card :=
        Finset.sum_le_sum (fun t _ => Finset.card_le_card (pairRes_concat_left Pre D hr t y hP))
    _ ≤ _ := Nat.le_add_right _ _

theorem resSum_concat_right {L : ℕ} (hD : D.Valid L) (y : ℕ) :
    ∑ t, (pairRes r (D.work t) D.T y).card ≤
      ∑ t, (pairRes r ((concatDiagram Pre D P r).work t) (concatDiagram Pre D P r).T
        (P + y)).card := by
  rw [Fin.sum_univ_add]
  calc ∑ t, (pairRes r (D.work t) D.T y).card
      = ∑ t : Fin k₂, (pairRes r ((concatDiagram Pre D P r).work (Fin.natAdd k₁ t))
          (concatDiagram Pre D P r).T (P + y)).card := by
        congr 1; funext t; rw [pairRes_concat_right Pre D hD t y]
    _ ≤ _ := Nat.le_add_left _ _

theorem chordTapes_concat_left (hr : 1 ≤ r) (hP : Pre.nodes r * r ≤ P * r) {e : ℕ × ℕ}
    (he : e ∈ Pre.chordEdges r) :
    Pre.chordTapes r e ≤ (concatDiagram Pre D P r).chordTapes r e := by
  classical
  have he2 := ((mem_chordEdges Pre).1 he).2.1
  unfold TSDiagram.chordTapes
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_add]
  refine le_trans ?_ (Nat.le_add_right _ _)
  apply Finset.sum_le_sum
  intro t _
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd ⟨h1.choose, isChord_concat_left Pre D hr t he2 hP h1.choose_spec⟩ h2
  · exact Nat.zero_le _
  · exact le_rfl

theorem chordTapes_concat_right {L : ℕ} (hr : 1 ≤ r) (hD : D.Valid L) (a b : ℕ) :
    D.chordTapes r (a, b) ≤ (concatDiagram Pre D P r).chordTapes r (P + a, P + b) := by
  classical
  unfold TSDiagram.chordTapes
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_add]
  refine le_trans ?_ (Nat.le_add_left _ _)
  apply Finset.sum_le_sum
  intro t _
  split_ifs with h1 h2
  · exact le_rfl
  · exfalso
    apply h2
    obtain ⟨β, hc⟩ := h1
    refine ⟨β, ?_⟩
    show IsChord (pairRes r ((concatDiagram Pre D P r).work (Fin.natAdd k₁ t))
      (concatDiagram Pre D P r).T) β (P + a) (P + b)
    rw [isChord_concat_right Pre D hr hD]
    simp only [Nat.add_sub_cancel_left]
    exact ⟨Nat.le_add_right _ _, hc⟩
  · exact Nat.zero_le _
  · exact le_rfl

/-! #### Rows and outputs -/

theorem rowsAt_concat_left (hr : 1 ≤ r) {n w y : ℕ} (hP : Pre.nodes r * r ≤ P * r) :
    Pre.rowsAt n w r y ⊆ (concatDiagram Pre D P r).rowsAt n w r y := by
  classical
  intro i hi
  simp only [TSDiagram.rowsAt, Finset.mem_filter, Finset.mem_range] at hi ⊢
  obtain ⟨hi, τ, hτ, h1, h2⟩ := hi
  have hτT : τ < Pre.T := ((mem_slotOf).1 hτ).2.2
  have hT1 : Pre.T ≤ Pre.nodes r * r := T_le_nodes_mul (D := Pre) hr
  have hin : (concatDiagram Pre D P r).inp τ = Pre.inp τ := by
    show (if τ < Pre.nodes r * r then Pre.inp τ else _) = _
    rw [ite_eq_left (by omega)]
  refine ⟨hi, τ, ?_, by rw [hin]; exact h1, by rw [hin]; exact h2⟩
  rw [mem_slotOf] at hτ ⊢
  exact ⟨hτ.1, hτ.2.1, by show τ < P * r + D.T; omega⟩

theorem rowsAt_concat_add (hP : Pre.nodes r * r ≤ P * r) {n w : ℕ} (y : ℕ) :
    (concatDiagram Pre D P r).rowsAt n w r (P + y) = D.rowsAt n w r y := by
  classical
  have hin : ∀ τ, (concatDiagram Pre D P r).inp (P * r + τ) = D.inp τ := by
    intro τ
    show (if P * r + τ < Pre.nodes r * r then _ else if P * r + τ < P * r then _
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

theorem visible_concat_add (hP : Pre.nodes r * r ≤ P * r) {n w : ℕ} (y : ℕ) {L' : ℕ}
    (x : Fin L' → Bool) :
    (concatDiagram Pre D P r).visible n w r (P + y) x = D.visible n w r y x := by
  funext d
  simp only [TSDiagram.visible, rowsAt_concat_add Pre D hP]

theorem outNode_concat {L : ℕ} (hr : 1 ≤ r) (hD : D.Valid L) (hT : 1 ≤ D.T) (o : ℕ) :
    (concatDiagram Pre D P r).outNode r o = P + D.outNode r o :=
  outNode_prefix D (L := L) hr hD hT o

end Concat

end Transpose.Tape.Impl
