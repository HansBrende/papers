import Transpose.Tape.Defs

/-!
# Run infrastructure

Basic facts about the total run `run M w`:
* one-step lemmas, in terms of `transAt`;
* frozen behaviour after halting;
* the bridge to the frozen `stepN` / `ComputesWithin`;
* the output as a `filterMap`; output lengths (`outRev_length_succ`, `outRev_length_mono`,
  `outLen_le_self`); the bounds `|inPos|, |workPos| ≤ τ` (`abs_inPos_le`, `abs_workPos_le`);
* cell contents: the content of a work cell is the symbol written at its last visit;
* `exists_flip`: a predicate that holds at `a` and fails at `b > a` flips at some step in between.

Everything lives in the namespace `Transpose.Tape.Impl`, so the names in
`Transpose/Tape/Statements/Core.lean` stay free.
-/

namespace Transpose.Tape.Impl

open Transpose

variable {M : TM} {w : List Bool}

/-- The successor configuration (unchanged once halted). -/
def next (M : TM) (w : List Bool) (c : Config M) : Config M := (step M w c).getD c

theorem run_zero : run M w 0 = init M := rfl

theorem run_succ (τ : ℕ) : run M w (τ + 1) = next M w (run M w τ) := rfl

theorem run_eq_iterate (τ : ℕ) : run M w τ = (next M w)^[τ] (init M) := by
  induction τ with
  | zero => rfl
  | succ τ ih => rw [run_succ, ih, Function.iterate_succ_apply']

/-- `step` applied to the run, in terms of `transAt`. -/
theorem step_run (τ : ℕ) : step M w (run M w τ) =
    match transAt M w τ with
    | none => none
    | some (s, d, acts, o) => some
      { state := s
        inPos := d.shift (run M w τ).inPos
        work := fun i p => if p = (run M w τ).workPos i then (acts i).1 else (run M w τ).work i p
        workPos := fun i => (acts i).2.shift ((run M w τ).workPos i)
        outRev := match o with
                  | none => (run M w τ).outRev
                  | some b => b :: (run M w τ).outRev } := rfl

theorem step_run_eq_none_iff (τ : ℕ) : step M w (run M w τ) = none ↔ transAt M w τ = none := by
  rw [step_run]
  rcases h : transAt M w τ with _ | ⟨s, d, acts, o⟩ <;> simp

/-- If step `τ` halts, the configuration does not change. -/
theorem run_succ_of_none {τ : ℕ} (h : transAt M w τ = none) : run M w (τ + 1) = run M w τ := by
  rw [run_succ, next, step_run, h]; rfl

/-- The configuration after a non-halting step. -/
theorem run_succ_of_some {τ : ℕ} {s : Fin (M.q + 1)} {d : Dir}
    {acts : Fin M.k → Fin (M.g + 1) × Dir} {o : Option Bool}
    (h : transAt M w τ = some (s, d, acts, o)) :
    run M w (τ + 1) =
      { state := s
        inPos := d.shift (run M w τ).inPos
        work := fun i p => if p = (run M w τ).workPos i then (acts i).1 else (run M w τ).work i p
        workPos := fun i => (acts i).2.shift ((run M w τ).workPos i)
        outRev := Option.elim o (run M w τ).outRev (fun b => b :: (run M w τ).outRev) } := by
  rw [run_succ, next, step_run, h]; cases o <;> rfl

/-- Once halted, always halted, and the configuration is frozen. -/
theorem run_add_of_none {τ : ℕ} (h : transAt M w τ = none) :
    ∀ j, run M w (τ + j) = run M w τ ∧ transAt M w (τ + j) = none := by
  intro j
  induction j with
  | zero => exact ⟨rfl, h⟩
  | succ j ih =>
    obtain ⟨h1, h2⟩ := ih
    have h3 : run M w (τ + (j + 1)) = run M w τ := by
      rw [← Nat.add_assoc, run_succ_of_none h2, h1]
    refine ⟨h3, ?_⟩
    have : transAt M w (τ + (j + 1)) = transAt M w τ := by
      unfold transAt inSym headSym; rw [h3]
    rw [this, h]

theorem run_of_le_of_none {τ τ' : ℕ} (h : transAt M w τ = none) (hle : τ ≤ τ') :
    run M w τ' = run M w τ := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hle
  exact (run_add_of_none h j).1

theorem transAt_of_le_of_none {τ τ' : ℕ} (h : transAt M w τ = none) (hle : τ ≤ τ') :
    transAt M w τ' = none := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hle
  exact (run_add_of_none h j).2

/-! ### Field lemmas for one step -/

theorem run_succ_state_of_some {τ : ℕ} {x : Fin (M.q + 1) × Dir × (Fin M.k → Fin (M.g + 1) × Dir) ×
    Option Bool} (h : transAt M w τ = some x) : (run M w (τ + 1)).state = x.1 := by
  obtain ⟨s, d, acts, o⟩ := x
  rw [run_succ_of_some h]

/-- The one-step update of a work cell: the cell under head `t` receives `writtenSym`, and every
other cell is unchanged. -/
theorem run_succ_work (τ : ℕ) (t : Fin M.k) (p : ℤ) :
    (run M w (τ + 1)).work t p =
      if p = (run M w τ).workPos t then writtenSym M w τ t else (run M w τ).work t p := by
  rcases h : transAt M w τ with _ | ⟨s, d, acts, o⟩
  · rw [run_succ_of_none h]
    split_ifs with hp
    · simp only [writtenSym, h, headSym, hp]
    · rfl
  · rw [run_succ_of_some h]
    simp only [writtenSym, h]

theorem run_succ_workPos (τ : ℕ) (t : Fin M.k) :
    (run M w (τ + 1)).workPos t =
      match transAt M w τ with
      | none => (run M w τ).workPos t
      | some (_, _, acts, _) => (acts t).2.shift ((run M w τ).workPos t) := by
  rcases h : transAt M w τ with _ | ⟨s, d, acts, o⟩
  · rw [run_succ_of_none h]
  · rw [run_succ_of_some h]

theorem run_succ_inPos (τ : ℕ) :
    (run M w (τ + 1)).inPos =
      match transAt M w τ with
      | none => (run M w τ).inPos
      | some (_, d, _, _) => d.shift (run M w τ).inPos := by
  rcases h : transAt M w τ with _ | ⟨s, d, acts, o⟩
  · rw [run_succ_of_none h]
  · rw [run_succ_of_some h]

theorem run_succ_outRev_reverse (τ : ℕ) :
    (run M w (τ + 1)).outRev.reverse = (run M w τ).outRev.reverse ++ (outBit M w τ).toList := by
  rcases h : transAt M w τ with _ | ⟨s, d, acts, o⟩
  · rw [run_succ_of_none h]; simp [outBit, h]
  · rw [run_succ_of_some h]
    cases o <;> simp [outBit, h]

/-! ### Bridge to the frozen semantics -/

theorem stepN_eq_some_iff (τ : ℕ) (c c' : Config M) :
    stepN M w τ c = some c' ↔
      (∀ σ < τ, step M w ((next M w)^[σ] c) ≠ none) ∧ (next M w)^[τ] c = c' := by
  induction τ generalizing c with
  | zero => simp [stepN]
  | succ τ ih =>
    rcases hs : step M w c with _ | c₁
    · simp only [stepN, hs]
      constructor
      · intro h; exact absurd h (by simp)
      · rintro ⟨h, -⟩
        exact absurd (by simpa using hs) (h 0 (Nat.succ_pos _))
    · have hnext : next M w c = c₁ := by simp [next, hs]
      simp only [stepN, hs, ih, Function.iterate_succ_apply, hnext]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨fun σ hσ => ?_, h2⟩
        rcases σ with _ | σ
        · simp [hs]
        · rw [Function.iterate_succ_apply, hnext]
          exact h1 σ (Nat.lt_of_succ_lt_succ hσ)
      · rintro ⟨h1, h2⟩
        refine ⟨fun σ hσ => ?_, h2⟩
        have := h1 (σ + 1) (Nat.succ_lt_succ hσ)
        rwa [Function.iterate_succ_apply, hnext] at this

theorem stepN_init_eq_some_iff (τ : ℕ) (c : Config M) :
    stepN M w τ (init M) = some c ↔ (∀ σ < τ, transAt M w σ ≠ none) ∧ run M w τ = c := by
  rw [stepN_eq_some_iff, ← run_eq_iterate]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun σ hσ hn => h1 σ hσ ?_, h2⟩
    rw [← run_eq_iterate]; exact (step_run_eq_none_iff σ).2 hn
  · rintro ⟨h1, h2⟩
    refine ⟨fun σ hσ hn => h1 σ hσ ?_, h2⟩
    rw [← run_eq_iterate] at hn; exact (step_run_eq_none_iff σ).1 hn

theorem computesWithin_iff (out : List Bool) (t : ℕ) :
    ComputesWithin M w out t ↔ ∃ T ≤ t, HaltsAt M w T ∧ (run M w T).outRev.reverse = out := by
  constructor
  · rintro ⟨s, hs, c, hc, hstep, hout⟩
    obtain ⟨h1, rfl⟩ := (stepN_init_eq_some_iff s c).1 hc
    exact ⟨s, hs, ⟨h1, (step_run_eq_none_iff s).1 hstep⟩, hout⟩
  · rintro ⟨T, hT, ⟨h1, h2⟩, hout⟩
    exact ⟨T, hT, run M w T, (stepN_init_eq_some_iff T _).2 ⟨h1, rfl⟩,
      (step_run_eq_none_iff T).2 h2, hout⟩

theorem haltsAt_unique {T T' : ℕ} (h : HaltsAt M w T) (h' : HaltsAt M w T') : T = T' := by
  rcases lt_trichotomy T T' with hlt | heq | hgt
  · exact absurd h.2 (h'.1 T hlt)
  · exact heq
  · exact absurd h'.2 (h.1 T' hgt)

/-- The output so far is the list of bits appended so far. -/
theorem outRev_reverse_eq (τ : ℕ) :
    (run M w τ).outRev.reverse = (List.range τ).filterMap (outBit M w) := by
  induction τ with
  | zero => simp [run, init]
  | succ τ ih =>
    rw [run_succ_outRev_reverse, ih, List.range_succ, List.filterMap_append]
    congr 1

/-! ### Output length and head positions -/

/-- Output length after a step. -/
theorem outRev_length_succ (w : List Bool) (τ : ℕ) :
    (run M w (τ + 1)).outRev.length =
      (run M w τ).outRev.length + (if (outBit M w τ).isSome then 1 else 0) := by
  rw [← List.length_reverse, run_succ_outRev_reverse, List.length_append, List.length_reverse]
  cases outBit M w τ <;> simp

theorem outRev_length_mono (w : List Bool) {τ τ' : ℕ} (h : τ ≤ τ') :
    (run M w τ).outRev.length ≤ (run M w τ').outRev.length := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction j with
  | zero => exact le_rfl
  | succ j ih =>
    rw [← Nat.add_assoc, outRev_length_succ]
    exact le_trans ih (Nat.le_add_right _ _)

/-- At most one bit is appended per step. -/
theorem outLen_le_self (w : List Bool) (τ : ℕ) : (run M w τ).outRev.length ≤ τ := by
  rw [← List.length_reverse, outRev_reverse_eq]
  exact (List.length_filterMap_le _ _).trans List.length_range.le

/-- A head move changes the distance to cell `0` by at most one. -/
theorem abs_shift_le (d : Dir) (p : ℤ) : |d.shift p| ≤ |p| + 1 := by
  have h1 := le_abs_self p
  have h2 := neg_abs_le p
  cases d <;> simp only [Dir.shift] <;> rw [abs_le] <;> constructor <;> linarith

/-- The input head is within `τ` cells of cell `0` at time `τ`. -/
theorem abs_inPos_le (w : List Bool) (τ : ℕ) : |(run M w τ).inPos| ≤ τ := by
  induction τ with
  | zero => simp [run_zero, init]
  | succ τ ih =>
    rw [run_succ_inPos]
    push_cast
    rcases transAt M w τ with _ | ⟨-, d, -, -⟩
    · linarith
    · linarith [abs_shift_le d (run M w τ).inPos]

/-- Every work head is within `τ` cells of cell `0` at time `τ`. -/
theorem abs_workPos_le (w : List Bool) (τ : ℕ) (t : Fin M.k) : |(run M w τ).workPos t| ≤ τ := by
  induction τ with
  | zero => simp [run_zero, init]
  | succ τ ih =>
    rw [run_succ_workPos]
    push_cast
    rcases transAt M w τ with _ | ⟨-, -, acts, -⟩
    · linarith
    · linarith [abs_shift_le (acts t).2 ((run M w τ).workPos t)]

/-! ### Cell contents -/

theorem work_eq_written (t : Fin M.k) (p : ℤ) {τ σ : ℕ} (hστ : σ < τ)
    (hσ : (run M w σ).workPos t = p)
    (hlast : ∀ ρ, σ < ρ → ρ < τ → (run M w ρ).workPos t ≠ p) :
    (run M w τ).work t p = writtenSym M w σ t := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hστ
  induction j with
  | zero => rw [run_succ_work, ite_eq_left hσ.symm]
  | succ j ih =>
    have h1 : σ + j + 1 + 1 = (σ + j + 1) + 1 := rfl
    rw [show σ + (j + 1) + 1 = (σ + j + 1) + 1 by omega, run_succ_work,
      ite_eq_right (fun hp => hlast (σ + j + 1) (by omega) (by omega) hp.symm)]
    exact ih (by omega) (fun ρ h1 h2 => hlast ρ h1 (by omega))

theorem work_eq_blank (t : Fin M.k) (p : ℤ) {τ : ℕ}
    (h : ∀ σ < τ, (run M w σ).workPos t ≠ p) : (run M w τ).work t p = 0 := by
  induction τ with
  | zero => rfl
  | succ τ ih =>
    rw [run_succ_work, ite_eq_right (fun hp => h τ (Nat.lt_succ_self τ) hp.symm)]
    exact ih (fun σ hσ => h σ (Nat.lt_succ_of_lt hσ))

/-- Cell contents relative to an earlier time `a`: a cell not visited during `[a, τ)` keeps its
content. -/
theorem work_eq_of_no_visit (t : Fin M.k) (p : ℤ) {a τ : ℕ} (haτ : a ≤ τ)
    (h : ∀ σ, a ≤ σ → σ < τ → (run M w σ).workPos t ≠ p) :
    (run M w τ).work t p = (run M w a).work t p := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le haτ
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [← Nat.add_assoc, run_succ_work, ite_eq_right (fun hp => h (a + j) (by omega) (by omega) hp.symm)]
    exact ih (by omega) (fun σ h1 h2 => h σ h1 (by omega))

/-- The symbol under head `t` at time `τ` is the symbol written at its last visit. -/
theorem headSym_eq_writtenSym (t : Fin M.k) {τ σ : ℕ}
    (hσ : IsLastVisit (fun s => workTraj M w s t) τ σ) :
    headSym M w τ t = writtenSym M w σ t :=
  work_eq_written t _ hσ.1 hσ.2.1 hσ.2.2

/-- The symbol under head `t` at time `τ` is blank if the cell was never visited before. -/
theorem headSym_eq_blank (t : Fin M.k) {τ : ℕ}
    (h : ∀ σ < τ, workTraj M w σ t ≠ workTraj M w τ t) : headSym M w τ t = 0 :=
  work_eq_blank t _ h

/-! ### A discrete flip -/

/-- A step with a flip of a predicate between two times. -/
theorem exists_flip {P : ℕ → Prop} {a b : ℕ} (hab : a < b) (ha : P a) (hb : ¬ P b) :
    ∃ σ, a < σ ∧ σ ≤ b ∧ P (σ - 1) ∧ ¬ P σ := by
  induction b with
  | zero => omega
  | succ b ih =>
    by_cases hPb : P b
    · exact ⟨b + 1, hab, le_rfl, by simpa using hPb, hb⟩
    · have hab' : a < b := by
        rcases Nat.lt_or_ge a b with h' | h'
        · exact h'
        · exfalso; have : a = b := by omega
          subst this; exact hPb ha
      obtain ⟨σ, h1, h2, h3, h4⟩ := ih hab' hPb
      exact ⟨σ, h1, by omega, h3, h4⟩

end Transpose.Tape.Impl
