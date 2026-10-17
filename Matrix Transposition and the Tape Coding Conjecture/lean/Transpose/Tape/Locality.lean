import Transpose.Tape.Run

/-!
# The Locality Lemma

* `locality`: arbitrary step sets, two runs with common work-head positions.
* `locality_oblivious`, `locality_function`: the forms for an oblivious class.
* `locality_core`: arbitrary step sets with data-dependent heads. The runs agree at anchor steps; a
  read elsewhere is justified by a time `a` at which the cell agrees, after which the last visits
  of the cell in both runs lie in the step set. It contains `locality_interval` (the interval
  form, below), `locality_anchored` (`PPrimeLocal.lean`) and `locality_entry`
  (`LemmaOnePrime.lean`).
* `stateHeads_succ`, `CfgAgree`, `cfgAgree_succ`: agreement of the state, head positions (and output
  length) propagates over a step with a common transition.
-/

namespace Transpose.Tape.Impl

open Transpose

variable {M : TM}

theorem transAt_eq_of_args {w w' : List Bool} {τ : ℕ}
    (hs : (run M w τ).state = (run M w' τ).state) (hi : inSym M w τ = inSym M w' τ)
    (hh : headSym M w τ = headSym M w' τ) : transAt M w τ = transAt M w' τ := by
  unfold transAt; rw [hs, hi, hh]

/-- The state after a step agrees when the state and the transition agree (no liveness needed: a
halted run keeps its state). -/
theorem state_succ_eq_of_transAt' {w w' : List Bool} {τ : ℕ}
    (hs : (run M w τ).state = (run M w' τ).state)
    (h : transAt M w τ = transAt M w' τ) :
    (run M w (τ + 1)).state = (run M w' (τ + 1)).state := by
  rcases hx : transAt M w τ with _ | x
  · have hx' : transAt M w' τ = none := h ▸ hx
    rw [run_succ_of_none hx, run_succ_of_none hx']; exact hs
  · have hx' : transAt M w' τ = some x := h ▸ hx
    rw [run_succ_state_of_some hx, run_succ_state_of_some hx']

/-- The written symbols agree when the symbols under the heads and the transition agree (no liveness
needed: a halted run writes nothing). -/
theorem writtenSym_eq_of_transAt' {w w' : List Bool} {τ : ℕ}
    (hh : headSym M w τ = headSym M w' τ)
    (h : transAt M w τ = transAt M w' τ) (t : Fin M.k) :
    writtenSym M w τ t = writtenSym M w' τ t := by
  rcases hx : transAt M w τ with _ | ⟨s, d, acts, o⟩
  · have hx' : transAt M w' τ = none := h ▸ hx
    simp only [writtenSym, hx, hx']; rw [hh]
  · have hx' : transAt M w' τ = some (s, d, acts, o) := h ▸ hx
    simp only [writtenSym, hx, hx']

/-- A last visit to cell `p` inside `[a, τ)`. -/
theorem exists_lastVisit_from {pos : ℕ → ℤ} {a τ : ℕ} {p : ℤ}
    (hex : ∃ σ, a ≤ σ ∧ σ < τ ∧ pos σ = p) :
    ∃ σ, a ≤ σ ∧ σ < τ ∧ pos σ = p ∧ ∀ ρ, σ < ρ → ρ < τ → pos ρ ≠ p := by
  classical
  obtain ⟨σ₀, h₀, h₁, h₂⟩ := hex
  let P : ℕ → Prop := fun σ => a ≤ σ ∧ σ < τ ∧ pos σ = p
  have hP : P (Nat.findGreatest P τ) := Nat.findGreatest_spec (le_of_lt h₁) ⟨h₀, h₁, h₂⟩
  refine ⟨Nat.findGreatest P τ, hP.1, hP.2.1, hP.2.2, fun ρ hρ1 hρ2 hρ3 => ?_⟩
  exact Nat.findGreatest_is_greatest hρ1 (le_of_lt hρ2) ⟨by have := hP.1; omega, hρ2, hρ3⟩

/-- The last visit before `τ` (if any) of the cell under head `t`. -/
theorem exists_lastVisit {pos : ℕ → ℤ} {τ : ℕ} (hex : ∃ σ < τ, pos σ = pos τ) :
    ∃ σ, IsLastVisit pos τ σ := by
  obtain ⟨σ₀, h1, h2⟩ := hex
  obtain ⟨σ, -, h3, h4, h5⟩ := exists_lastVisit_from (a := 0) ⟨σ₀, Nat.zero_le _, h1, h2⟩
  exact ⟨σ, h3, h4, h5⟩

theorem isLastVisit_congr {pos pos' : ℕ → ℤ} {τ σ : ℕ} (h : IsLastVisit pos τ σ)
    (heq : ∀ ρ ≤ τ, pos ρ = pos' ρ) : IsLastVisit pos' τ σ := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, ?_, fun ρ hρ1 hρ2 => ?_⟩
  · rw [← heq σ (le_of_lt h1), ← heq τ le_rfl]; exact h2
  · rw [← heq ρ (le_of_lt hρ2), ← heq τ le_rfl]; exact h3 ρ hρ1 hρ2

theorem mem_entryCells {k : ℕ} {wp : ℕ → Fin k → ℤ} {J : Finset ℕ} {t : Fin k} {τ : ℕ} :
    (t, τ) ∈ entryCells wp J ↔ τ ∈ J ∧ ∃ σ, σ ∉ J ∧ IsLastVisit (fun s => wp s t) τ σ := by
  classical
  simp [entryCells, Finset.mem_filter, Finset.mem_product]

theorem mem_entryPoints {J : Finset ℕ} {τ : ℕ} :
    τ ∈ entryPoints J ↔ τ ∈ J ∧ τ ≠ 0 ∧ τ - 1 ∉ J := by
  simp [entryPoints, Finset.mem_filter]

/-- **The Locality Lemma, two-run form.** -/
theorem locality {w w' : List Bool} {T : ℕ}
    (hwork : ∀ τ < T, (run M w τ).workPos = (run M w' τ).workPos)
    {J : Finset ℕ} (hJ : ∀ τ ∈ J, τ < T)
    (hstate : ∀ τ ∈ entryPoints J, (run M w τ).state = (run M w' τ).state)
    (hcell : ∀ p ∈ entryCells (workTraj M w) J, headSym M w p.2 p.1 = headSym M w' p.2 p.1)
    (hinput : ∀ τ ∈ J, inSym M w τ = inSym M w' τ) :
    ∀ τ ∈ J, (run M w τ).state = (run M w' τ).state ∧ headSym M w τ = headSym M w' τ ∧
      transAt M w τ = transAt M w' τ := by
  intro τ
  induction τ using Nat.strong_induction_on with
  | _ τ ih =>
  intro hτ
  have hτT := hJ τ hτ
  -- the state at time τ
  have hst : (run M w τ).state = (run M w' τ).state := by
    by_cases hep : τ ∈ entryPoints J
    · exact hstate τ hep
    · rw [mem_entryPoints] at hep
      rcases Nat.eq_zero_or_pos τ with h0 | hpos
      · subst h0; rfl
      · have hprev : τ - 1 ∈ J := by
          by_contra hc; exact hep ⟨hτ, by omega, hc⟩
        obtain ⟨hs, -, htr⟩ := ih (τ - 1) (by omega) hprev
        have e : τ = (τ - 1) + 1 := by omega
        rw [e]
        exact state_succ_eq_of_transAt' hs htr
  -- the symbols under the work heads at time τ
  have hhead : headSym M w τ = headSym M w' τ := by
    funext t
    have hpos : ∀ ρ ≤ τ, workTraj M w ρ t = workTraj M w' ρ t := fun ρ hρ => by
      simp only [workTraj]; rw [hwork ρ (by omega)]
    by_cases hex : ∃ σ < τ, workTraj M w σ t = workTraj M w τ t
    · obtain ⟨σ, hlast⟩ := exists_lastVisit hex
      have hlast' : IsLastVisit (fun s => workTraj M w' s t) τ σ := isLastVisit_congr hlast hpos
      by_cases hσJ : σ ∈ J
      · obtain ⟨-, hh, htr⟩ := ih σ hlast.1 hσJ
        rw [headSym_eq_writtenSym t hlast, headSym_eq_writtenSym t hlast']
        exact writtenSym_eq_of_transAt' hh htr t
      · exact hcell (t, τ) (mem_entryCells.2 ⟨hτ, σ, hσJ, hlast⟩)
    · push Not at hex
      rw [headSym_eq_blank t hex, headSym_eq_blank t]
      intro σ hσ
      rw [← hpos σ (le_of_lt hσ), ← hpos τ le_rfl]
      exact hex σ hσ
  exact ⟨hst, hhead, transAt_eq_of_args hst (hinput τ hτ) hhead⟩

theorem oblivious_workTraj {W : Set (List Bool)} {T : ℕ} (hobl : ObliviousOn M W T)
    {w w' : List Bool} (hw : w ∈ W) (hw' : w' ∈ W) : workTraj M w = workTraj M w' := by
  funext τ; exact (hobl.2 w hw w' hw' τ).2.1

/-- **The Locality Lemma for an oblivious class.** -/
theorem locality_oblivious {W : Set (List Bool)} {T : ℕ} (hobl : ObliviousOn M W T)
    {w w' : List Bool} (hw : w ∈ W) (hw' : w' ∈ W) {J : Finset ℕ} (hJ : ∀ τ ∈ J, τ < T)
    (hstate : ∀ τ ∈ entryPoints J, (run M w τ).state = (run M w' τ).state)
    (hcell : ∀ p ∈ entryCells (workTraj M w) J, headSym M w p.2 p.1 = headSym M w' p.2 p.1)
    (hbits : ∀ τ ∈ J, readInput w (run M w τ).inPos = readInput w' (run M w τ).inPos) :
    ∀ τ ∈ J, (run M w τ).state = (run M w' τ).state ∧ headSym M w τ = headSym M w' τ ∧
      inSym M w τ = inSym M w' τ ∧ transAt M w τ = transAt M w' τ := by
  have hinput : ∀ τ ∈ J, inSym M w τ = inSym M w' τ := by
    intro τ hτ
    simp only [inSym]
    rw [← (hobl.2 w hw w' hw' τ).1]
    exact hbits τ hτ
  have hloc := locality (fun τ _ => (hobl.2 w hw w' hw' τ).2.1) hJ hstate hcell
    hinput
  intro τ hτ
  obtain ⟨h1, h2, h3⟩ := hloc τ hτ
  exact ⟨h1, h2, hinput τ hτ, h3⟩

/-- **The Locality Lemma, functional form.** -/
theorem locality_function {W : Set (List Bool)} {T : ℕ} (hobl : ObliviousOn M W T)
    {w₀ : List Bool} (hw₀ : w₀ ∈ W) (J : Finset ℕ) (hJ : ∀ τ ∈ J, τ < T) :
    ∃ F : (entryPoints J → Fin (M.q + 1)) → (entryCells (workTraj M w₀) J → Fin (M.g + 1)) →
        (J → Option Bool) →
        (J → Option (Fin (M.q + 1) × Dir × (Fin M.k → Fin (M.g + 1) × Dir) × Option Bool)),
      ∀ w ∈ W, (fun τ : J => transAt M w τ.1) =
        F (fun τ => (run M w τ.1).state) (fun p => headSym M w p.1.2 p.1.1)
          (fun τ => inSym M w τ.1) := by
  classical
  let D : List Bool → (entryPoints J → Fin (M.q + 1)) ×
      (entryCells (workTraj M w₀) J → Fin (M.g + 1)) × (J → Option Bool) :=
    fun w => (fun τ => (run M w τ.1).state, fun p => headSym M w p.1.2 p.1.1,
      fun τ => inSym M w τ.1)
  refine ⟨fun e c i => if h : ∃ w ∈ W, D w = (e, c, i) then
      (fun τ : J => transAt M h.choose τ.1) else (fun _ => none), ?_⟩
  intro w hw
  have hex : ∃ w' ∈ W, D w' = D w := ⟨w, hw, rfl⟩
  show (fun τ : J => transAt M w τ.1) = (if h : ∃ w' ∈ W, D w' = D w then
      (fun τ : J => transAt M h.choose τ.1) else (fun _ => none))
  rw [dite_eq_left hex]
  obtain ⟨hw', hD⟩ := hex.choose_spec
  set w' := hex.choose
  simp only [D, Prod.mk.injEq] at hD
  obtain ⟨hDs, hDc, hDi⟩ := hD
  have hcells : entryCells (workTraj M w') J = entryCells (workTraj M w₀) J := by
    rw [oblivious_workTraj hobl hw' hw₀]
  have hloc := locality_oblivious hobl hw' hw hJ
    (fun τ hτ => congrFun hDs ⟨τ, hτ⟩)
    (fun p hp => by
      have := congrFun hDc ⟨p, hcells ▸ hp⟩
      exact this)
    (fun τ hτ => by
      have h1 := congrFun hDi ⟨τ, hτ⟩
      simp only [inSym] at h1
      rw [h1, (hobl.2 w hw w' hw' τ).1])
  funext τ
  exact ((hloc τ.1 τ.2).2.2.2).symm

/-! ### The Locality Lemma with data-dependent heads -/

/-- The state and the head positions after a step agree when they agree before it and the
transition agrees. -/
theorem stateHeads_succ {w w' : List Bool} {τ : ℕ}
    (hs : (run M w τ).state = (run M w' τ).state) (hi : (run M w τ).inPos = (run M w' τ).inPos)
    (hwp : (run M w τ).workPos = (run M w' τ).workPos) (htr : transAt M w τ = transAt M w' τ) :
    (run M w (τ + 1)).state = (run M w' (τ + 1)).state ∧
      (run M w (τ + 1)).inPos = (run M w' (τ + 1)).inPos ∧
      (run M w (τ + 1)).workPos = (run M w' (τ + 1)).workPos :=
  ⟨state_succ_eq_of_transAt' hs htr, by rw [run_succ_inPos, run_succ_inPos, ← htr, hi],
    funext fun t => by rw [run_succ_workPos, run_succ_workPos, ← htr, hwp]⟩

/-- The two runs have the same state, head positions and output length at time `τ`. -/
def CfgAgree (M : TM) (w w' : List Bool) (τ : ℕ) : Prop :=
  (run M w τ).state = (run M w' τ).state ∧ (run M w τ).inPos = (run M w' τ).inPos ∧
    (run M w τ).workPos = (run M w' τ).workPos ∧
    (run M w τ).outRev.length = (run M w' τ).outRev.length

/-- Two runs that agree on the state, the head positions and the output length at time `τ`, and
take the same transition there, agree on these at `τ + 1`. -/
theorem cfgAgree_succ {w w' : List Bool} {τ : ℕ} (h : CfgAgree M w w' τ)
    (htr : transAt M w τ = transAt M w' τ) : CfgAgree M w w' (τ + 1) := by
  obtain ⟨hs, hi, hwp, hl⟩ := h
  obtain ⟨h1, h2, h3⟩ := stateHeads_succ hs hi hwp htr
  have hob : outBit M w τ = outBit M w' τ := by simp only [outBit, htr]
  exact ⟨h1, h2, h3, by rw [outRev_length_succ, outRev_length_succ, hl, hob]⟩

/-- **The Locality Lemma, core form (data-dependent heads).** -/
theorem locality_core {w w' : List Bool} {J : Finset ℕ} {A : Set ℕ}
    (hpred : ∀ τ ∈ J, τ ∉ A → 1 ≤ τ ∧ τ - 1 ∈ J)
    (hanchor : ∀ τ ∈ J, τ ∈ A →
      (run M w τ).state = (run M w' τ).state ∧ (run M w τ).inPos = (run M w' τ).inPos ∧
      (run M w τ).workPos = (run M w' τ).workPos ∧ headSym M w τ = headSym M w' τ)
    (hread : ∀ τ ∈ J, τ ∉ A → (run M w τ).workPos = (run M w' τ).workPos → ∀ t : Fin M.k,
      ∃ a ≤ τ, (run M w a).work t (workTraj M w τ t) = (run M w' a).work t (workTraj M w τ t) ∧
      (∀ σ, a ≤ σ → σ < τ → workTraj M w σ t = workTraj M w τ t →
        (∀ ρ, σ < ρ → ρ < τ → workTraj M w ρ t ≠ workTraj M w τ t) → σ ∈ J) ∧
      (∀ σ, a ≤ σ → σ < τ → workTraj M w' σ t = workTraj M w τ t →
        (∀ ρ, σ < ρ → ρ < τ → workTraj M w' ρ t ≠ workTraj M w τ t) → σ ∈ J))
    (hinput : ∀ τ ∈ J, (run M w τ).inPos = (run M w' τ).inPos →
      readInput w (run M w τ).inPos = readInput w' (run M w τ).inPos) :
    ∀ τ ∈ J, (run M w τ).state = (run M w' τ).state ∧ (run M w τ).inPos = (run M w' τ).inPos ∧
      (run M w τ).workPos = (run M w' τ).workPos ∧
      headSym M w τ = headSym M w' τ ∧ transAt M w τ = transAt M w' τ := by
  intro τ
  induction τ using Nat.strong_induction_on with
  | _ τ ih =>
  intro hτ
  -- the state and the head positions at `τ`
  have hcfg : (run M w τ).state = (run M w' τ).state ∧ (run M w τ).inPos = (run M w' τ).inPos ∧
      (run M w τ).workPos = (run M w' τ).workPos := by
    by_cases hA : τ ∈ A
    · exact ⟨(hanchor τ hτ hA).1, (hanchor τ hτ hA).2.1, (hanchor τ hτ hA).2.2.1⟩
    · obtain ⟨h1, hprev⟩ := hpred τ hτ hA
      obtain ⟨hs, hi, hwp, -, htr⟩ := ih (τ - 1) (by omega) hprev
      rw [show τ = (τ - 1) + 1 by omega]
      exact stateHeads_succ hs hi hwp htr
  obtain ⟨hs, hi, hwp⟩ := hcfg
  -- the symbols under the work heads
  have hhead : headSym M w τ = headSym M w' τ := by
    by_cases hA : τ ∈ A
    · exact (hanchor τ hτ hA).2.2.2
    · funext t
      obtain ⟨a, haτ, hcont, hJw, hJw'⟩ := hread τ hτ hA hwp t
      have hposJ : ∀ σ ∈ J, σ < τ → (run M w σ).workPos t = (run M w' σ).workPos t :=
        fun σ hσ hlt => by rw [(ih σ hlt hσ).2.2.1]
      show (run M w τ).work t ((run M w τ).workPos t) =
        (run M w' τ).work t ((run M w' τ).workPos t)
      rw [← hwp]
      by_cases hex : ∃ σ, a ≤ σ ∧ σ < τ ∧ (run M w σ).workPos t = (run M w τ).workPos t
      · -- both runs last visited the cell at the same step of `J`
        obtain ⟨σ, h1, h2, h3, h4⟩ := exists_lastVisit_from (pos := fun s => (run M w s).workPos t)
          (p := (run M w τ).workPos t) hex
        have hσJ : σ ∈ J := hJw σ h1 h2 h3 h4
        obtain ⟨σ', h1', h2', h3', h4'⟩ :=
          exists_lastVisit_from (pos := fun s => (run M w' s).workPos t)
            (p := (run M w τ).workPos t) ⟨σ, h1, h2, (hposJ σ hσJ h2).symm.trans h3⟩
        have hσ'J : σ' ∈ J := hJw' σ' h1' h2' h3' h4'
        have heq : σ = σ' := by
          rcases lt_trichotomy σ σ' with h | h | h
          · exact absurd ((hposJ σ' hσ'J h2').trans h3') (h4 σ' h h2')
          · exact h
          · exact absurd ((hposJ σ hσJ h2).symm.trans h3) (h4' σ h h2)
        subst heq
        obtain ⟨-, -, -, hhσ, htrσ⟩ := ih σ h2 hσJ
        rw [work_eq_written t _ h2 h3 h4, work_eq_written t _ h2 h3' h4']
        exact writtenSym_eq_of_transAt' hhσ htrσ t
      · -- neither run visited the cell during `[a, τ)`
        push Not at hex
        have hex' : ∀ σ, a ≤ σ → σ < τ → (run M w' σ).workPos t ≠ (run M w τ).workPos t := by
          intro σ h1 h2 h3
          obtain ⟨σ', h1', h2', h3', h4'⟩ :=
            exists_lastVisit_from (pos := fun s => (run M w' s).workPos t)
              (p := (run M w τ).workPos t) ⟨σ, h1, h2, h3⟩
          exact hex σ' h1' h2' ((hposJ σ' (hJw' σ' h1' h2' h3' h4') h2').trans h3')
        rw [work_eq_of_no_visit t _ haτ hex, work_eq_of_no_visit t _ haτ hex']
        exact hcont
  -- the input symbol
  have hin : inSym M w τ = inSym M w' τ := by
    simp only [inSym]; rw [← hi]; exact hinput τ hτ hi
  exact ⟨hs, hi, hwp, hhead, transAt_eq_of_args hs hin hhead⟩

/-- **The Locality Lemma, interval form with data-dependent heads**: `locality_core` with
`J = [a, b)` and the single anchor `a`, plus one step to time `b`. -/
theorem locality_interval {w w' : List Bool} {a b : ℕ}
    (hstate : (run M w a).state = (run M w' a).state)
    (hin : (run M w a).inPos = (run M w' a).inPos)
    (hwork : (run M w a).workPos = (run M w' a).workPos)
    (hcells : ∀ τ, a ≤ τ → τ < b → ∀ t : Fin M.k,
      (run M w a).work t ((run M w τ).workPos t) = (run M w' a).work t ((run M w τ).workPos t))
    (hbits : ∀ τ, a ≤ τ → τ < b →
      readInput w (run M w τ).inPos = readInput w' (run M w τ).inPos) :
    ∀ τ, a ≤ τ → τ ≤ b →
      (run M w τ).state = (run M w' τ).state ∧ (run M w τ).inPos = (run M w' τ).inPos ∧
        (run M w τ).workPos = (run M w' τ).workPos ∧
        (τ < b → transAt M w τ = transAt M w' τ) := by
  have hc := locality_core (J := Finset.Ico a b) (A := {a}) (w := w) (w' := w')
    (fun τ hτ hA => by
      rw [Finset.mem_Ico] at hτ ⊢
      have : τ ≠ a := hA
      exact ⟨by omega, by omega, by omega⟩)
    (fun τ hτ hA => by
      rw [Set.mem_singleton_iff] at hA; subst hA
      refine ⟨hstate, hin, hwork, funext fun t => ?_⟩
      show (run M w τ).work t ((run M w τ).workPos t) = (run M w' τ).work t ((run M w' τ).workPos t)
      rw [← hwork]; exact hcells τ le_rfl (Finset.mem_Ico.1 hτ).2 t)
    (fun τ hτ _ _ t => ⟨a, (Finset.mem_Ico.1 hτ).1,
      hcells τ (Finset.mem_Ico.1 hτ).1 (Finset.mem_Ico.1 hτ).2 t,
      fun σ h1 h2 _ _ => Finset.mem_Ico.2 ⟨h1, by have := (Finset.mem_Ico.1 hτ).2; omega⟩,
      fun σ h1 h2 _ _ => Finset.mem_Ico.2 ⟨h1, by have := (Finset.mem_Ico.1 hτ).2; omega⟩⟩)
    (fun τ hτ _ => hbits τ (Finset.mem_Ico.1 hτ).1 (Finset.mem_Ico.1 hτ).2)
  intro τ haτ hτb
  rcases Nat.lt_or_ge τ b with hlt | hge
  · obtain ⟨h1, h2, h3, -, h5⟩ := hc τ (Finset.mem_Ico.2 ⟨haτ, hlt⟩)
    exact ⟨h1, h2, h3, fun _ => h5⟩
  obtain rfl : τ = b := le_antisymm hτb hge
  have key : (run M w τ).state = (run M w' τ).state ∧ (run M w τ).inPos = (run M w' τ).inPos ∧
      (run M w τ).workPos = (run M w' τ).workPos := by
    rcases Nat.eq_or_lt_of_le haτ with rfl | hlt
    · exact ⟨hstate, hin, hwork⟩
    · obtain ⟨h1, h2, h3, -, h5⟩ := hc (τ - 1) (Finset.mem_Ico.2 ⟨by omega, by omega⟩)
      have := stateHeads_succ h1 h2 h3 h5
      rwa [show τ - 1 + 1 = τ by omega] at this
  exact ⟨key.1, key.2.1, key.2.2, fun h => absurd h (lt_irrefl _)⟩

end Transpose.Tape.Impl
