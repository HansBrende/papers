import SourceCovers.FiniteSkeleton
import Transpose.Tape.Locality
import Transpose.Tape.Encode

set_option autoImplicit false

/-!
# Traces of a run, their fibres, and local determination along a frozen trace

The machine is the frozen `Transpose.TM` of `Transpose/Statement.lean`, run with the first paper's
total run `Transpose.Tape.run` (configurations frozen after halting), its transitions `transAt`,
the written symbols `writtenSym` and the appended bits `outBit`.

* `trace M w`: the trace of the run on `w`. Step `t` contributes its *motion* (the input-head move,
  the work-head moves, and whether it appends a bit); the trace is `none` from the halting time on.
  It therefore records all head moves, the append times and the halting time.
* `Trace.work`, `Trace.input`, `Trace.appends`, `Trace.haltTime`: the work-head walks, the
  input-head walk, the append flags and the halting time read off a trace. `workPos_eq_work`,
  `inPos_eq_input`, `outBit_isSome_eq`, `haltsAt_iff_trace`: every run follows its trace.
  `Trace.work_isWalk`: the work walks are unit-step walks for all times.
* `fibre M L τ₀`: the inputs `X ∈ {0,1}^L` whose run has trace `τ₀`; `traceProb M L τ₀ =
  |fibre| / 2^L` is the probability of `τ₀` for a uniform input. `two_rpow_le_card_fibre` is
  `(6.1)`: probability at least `2^{-ηL}` means a fibre of at least `2^{(1-η)L}` inputs.
* `stepValue M w t`: the value `v_t` of step `t` (the state after the step, the `k` symbols written,
  and the bit appended or `none`). `valueWidth M = ⌈log₂ |Q|⌉ + k ⌈log₂ |Γ|⌉ + 2` is `β(M)`, and
  `card_value_le`, `log_card_value_le`: the values take at most `2^{β(M)}` values.
* `capacityBits M = log₂ (3 |Q| |Γ|^k) ≤ β(M)`: the exact capacity of a step value in bits.
* `stepValue_eq_of_parents`: local determination along a frozen trace. For two inputs whose traces
  agree with `τ` before `T` and a step `t < T`, the value of step `t` agrees if the input bit under
  the input head (when that cell lies in the input) agrees and the values agree at every parent of
  `t` in the ninth paper's `actualParents` of the work walks of `τ` (the state edge and the lower
  ends of all long hops ending at `t`). Only agreement before `T` is used, so the traces may differ
  from time `T` on.
-/

namespace MergeDepth

open Finset Transpose Transpose.Tape Transpose.Tape.Impl SourceCovers BoundedNesting LeanMachine

/-! ### Head moves as integers -/

/-- The displacement of a head move. -/
def moveInt : Dir → ℤ
  | .left => -1
  | .stay => 0
  | .right => 1

theorem shift_eq_add_moveInt (d : Dir) (p : ℤ) : d.shift p = p + moveInt d := by
  cases d <;> simp [Dir.shift, moveInt, sub_eq_add_neg]

theorem abs_moveInt_le (d : Dir) : |moveInt d| ≤ 1 := by
  cases d <;> simp [moveInt]

/-! ### Traces -/

/-- The motion of one step: the input-head move, the work-head moves, and whether a bit is
appended. -/
abbrev Motion (k : ℕ) := Dir × (Fin k → Dir) × Bool

/-- A trace: the motion of every step, `none` from the halting time on. -/
abbrev Trace (k : ℕ) := ℕ → Option (Motion k)

/-- The trace of the run of `M` on `w`: step `t` contributes its input-head move, its work-head
moves and whether it appends a bit, and is `none` exactly when the configuration at time `t` is
halting. -/
def trace (M : TM) (w : List Bool) : Trace M.k := fun t =>
  (transAt M w t).map fun x => (x.2.1, fun h => (x.2.2.1 h).2, x.2.2.2.isSome)

namespace Trace

variable {k : ℕ} (τ : Trace k)

/-- The displacement of work head `h` at step `t`. -/
def workStep (h : Fin k) (t : ℕ) : ℤ := (τ t).elim 0 fun m => moveInt (m.2.1 h)

/-- The displacement of the input head at step `t`. -/
def inStep (t : ℕ) : ℤ := (τ t).elim 0 fun m => moveInt m.1

/-- The walk of work head `h`: its position at time `t`. -/
def work (h : Fin k) (t : ℕ) : ℤ := ∑ s ∈ range t, τ.workStep h s

/-- The walk of the input head: its position at time `t`. -/
def input (t : ℕ) : ℤ := ∑ s ∈ range t, τ.inStep s

/-- Whether step `t` appends a bit. -/
def appends (t : ℕ) : Bool := (τ t).elim false fun m => m.2.2

/-- `τ` halts at time `T`: steps `0, …, T - 1` are executed and time `T` is halting. -/
def HaltsAt (T : ℕ) : Prop := (∀ t < T, τ t ≠ none) ∧ τ T = none

open Classical in
/-- The halting time of `τ`: its first `none` (`0` if it has none). -/
noncomputable def haltTime : ℕ := if h : ∃ t, τ t = none then Nat.find h else 0

theorem haltsAt_haltTime (h : ∃ t, τ t = none) : τ.HaltsAt τ.haltTime := by
  classical
  have e : τ.haltTime = Nat.find h := dite_eq_left h
  rw [e]
  exact ⟨fun t ht => Nat.find_min h ht, Nat.find_spec h⟩

theorem HaltsAt.unique {τ : Trace k} {T T' : ℕ} (h : τ.HaltsAt T) (h' : τ.HaltsAt T') :
    T = T' := by
  rcases lt_trichotomy T T' with hlt | heq | hgt
  · exact absurd h.2 (h'.1 T hlt)
  · exact heq
  · exact absurd h'.2 (h.1 T' hgt)

theorem work_zero (h : Fin k) : τ.work h 0 = 0 := sum_range_zero _

theorem input_zero : τ.input 0 = 0 := sum_range_zero _

theorem work_succ (h : Fin k) (t : ℕ) : τ.work h (t + 1) = τ.work h t + τ.workStep h t :=
  sum_range_succ _ _

theorem input_succ (t : ℕ) : τ.input (t + 1) = τ.input t + τ.inStep t := sum_range_succ _ _

theorem abs_workStep_le (h : Fin k) (t : ℕ) : |τ.workStep h t| ≤ 1 := by
  unfold workStep
  rcases τ t with _ | m
  · simp
  · exact abs_moveInt_le _

theorem abs_inStep_le (t : ℕ) : |τ.inStep t| ≤ 1 := by
  unfold inStep
  rcases τ t with _ | m
  · simp
  · exact abs_moveInt_le _

/-- The work-head walks of a trace are unit-step walks at all times. -/
theorem work_isWalk (h : Fin k) : IsWalk (τ.work h) := fun t => by
  rw [work_succ, add_sub_cancel_left]
  exact τ.abs_workStep_le h t

theorem abs_input_succ_sub_le (t : ℕ) : |τ.input (t + 1) - τ.input t| ≤ 1 := by
  rw [input_succ, add_sub_cancel_left]
  exact τ.abs_inStep_le t

/-- The position at time `t` depends only on the motion before `t`. -/
theorem work_congr {τ τ' : Trace k} {t : ℕ} (hag : ∀ s < t, τ s = τ' s) (h : Fin k) :
    τ.work h t = τ'.work h t :=
  sum_congr rfl fun s hs => by simp only [workStep, hag s (mem_range.mp hs)]

theorem input_congr {τ τ' : Trace k} {t : ℕ} (hag : ∀ s < t, τ s = τ' s) :
    τ.input t = τ'.input t :=
  sum_congr rfl fun s hs => by simp only [inStep, hag s (mem_range.mp hs)]

end Trace

/-! ### Every run follows its trace -/

section Runs

variable {M : TM} {w : List Bool}

theorem trace_eq_none_iff (t : ℕ) : trace M w t = none ↔ transAt M w t = none :=
  Option.map_eq_none_iff

theorem workPos_eq_work (h : Fin M.k) (t : ℕ) : (run M w t).workPos h = (trace M w).work h t := by
  induction t with
  | zero => rw [Trace.work_zero]; rfl
  | succ t ih =>
    rw [run_succ_workPos, Trace.work_succ, ← ih]
    rcases hx : transAt M w t with _ | ⟨s, d, acts, o⟩
    · simp [Trace.workStep, trace, hx]
    · simp [Trace.workStep, trace, hx, shift_eq_add_moveInt]

theorem inPos_eq_input (t : ℕ) : (run M w t).inPos = (trace M w).input t := by
  induction t with
  | zero => rw [Trace.input_zero]; rfl
  | succ t ih =>
    rw [run_succ_inPos, Trace.input_succ, ← ih]
    rcases hx : transAt M w t with _ | ⟨s, d, acts, o⟩
    · simp [Trace.inStep, trace, hx]
    · simp [Trace.inStep, trace, hx, shift_eq_add_moveInt]

theorem workTraj_eq_work (t : ℕ) (h : Fin M.k) : workTraj M w t h = (trace M w).work h t :=
  workPos_eq_work h t

theorem outBit_isSome_eq (t : ℕ) : (outBit M w t).isSome = (trace M w).appends t := by
  rcases hx : transAt M w t with _ | ⟨s, d, acts, o⟩ <;>
    simp [outBit, Trace.appends, trace, hx]

theorem haltsAt_iff_trace (T : ℕ) : HaltsAt M w T ↔ (trace M w).HaltsAt T := by
  simp only [HaltsAt, Trace.HaltsAt, Ne, trace_eq_none_iff]

variable {τ : Trace M.k} {T : ℕ}

/-- A run whose trace agrees with `τ` before `T` follows the work walks of `τ` up to time `T`. -/
theorem workPos_eq_of_agree (hag : ∀ s < T, trace M w s = τ s) {t : ℕ} (ht : t ≤ T)
    (h : Fin M.k) : (run M w t).workPos h = τ.work h t := by
  rw [workPos_eq_work, Trace.work_congr fun s hs => hag s (by omega)]

/-- A run whose trace agrees with `τ` before `T` follows the input walk of `τ` up to time `T`. -/
theorem inPos_eq_of_agree (hag : ∀ s < T, trace M w s = τ s) {t : ℕ} (ht : t ≤ T) :
    (run M w t).inPos = τ.input t := by
  rw [inPos_eq_input, Trace.input_congr fun s hs => hag s (by omega)]

theorem outBit_isSome_eq_of_agree (hag : ∀ s < T, trace M w s = τ s) {t : ℕ} (ht : t < T) :
    (outBit M w t).isSome = τ.appends t := by
  rw [outBit_isSome_eq]
  simp only [Trace.appends, hag t ht]

end Runs

/-! ### Fibres and probabilities -/

open Classical in
/-- The fibre of a trace: the inputs `X ∈ {0,1}^L` whose run has trace `τ₀`. -/
noncomputable def fibre (M : TM) (L : ℕ) (τ₀ : Trace M.k) : Finset (Fin L → Bool) :=
  univ.filter fun X => trace M (List.ofFn X) = τ₀

theorem mem_fibre {M : TM} {L : ℕ} {τ₀ : Trace M.k} {X : Fin L → Bool} :
    X ∈ fibre M L τ₀ ↔ trace M (List.ofFn X) = τ₀ := by
  classical
  simp [fibre]

/-- The probability `Pr[τ(X) = τ₀]` of a trace for `X` uniform on `{0,1}^L`. -/
noncomputable def traceProb (M : TM) (L : ℕ) (τ₀ : Trace M.k) : ℝ :=
  (fibre M L τ₀).card / 2 ^ L

theorem card_fibre_eq (M : TM) (L : ℕ) (τ₀ : Trace M.k) :
    ((fibre M L τ₀).card : ℝ) = 2 ^ L * traceProb M L τ₀ := by
  unfold traceProb
  field_simp

/-- Equation `(6.1)`: a trace of probability at least `2^{-ηL}` has a fibre of at least
`2^{(1-η)L}` inputs. -/
theorem two_rpow_le_card_fibre {M : TM} {L : ℕ} {τ₀ : Trace M.k} {η : ℝ}
    (h : (2 : ℝ) ^ (-η * L) ≤ traceProb M L τ₀) :
    (2 : ℝ) ^ ((1 - η) * L) ≤ (fibre M L τ₀).card := by
  rw [card_fibre_eq, show (1 - η) * (L : ℝ) = L + -η * L by ring,
    Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_natCast]
  exact mul_le_mul_of_nonneg_left h (by positivity)

/-- A fibre has at most `2^L` inputs. -/
theorem card_fibre_le (M : TM) (L : ℕ) (τ₀ : Trace M.k) : (fibre M L τ₀).card ≤ 2 ^ L := by
  simpa using card_le_univ (fibre M L τ₀)

/-! ### Step values and the value width -/

/-- A step value: the state after the step, the `k` symbols written and the bit appended (or
`none`). -/
abbrev Value (M : TM) := Fin (M.q + 1) × (Fin M.k → Fin (M.g + 1)) × Option Bool

/-- The value `v_t` of step `t` of the run of `M` on `w`. -/
def stepValue (M : TM) (w : List Bool) (t : ℕ) : Value M :=
  ((run M w (t + 1)).state, writtenSym M w t, outBit M w t)

/-- The value width `β(M) = ⌈log₂ |Q|⌉ + k ⌈log₂ |Γ|⌉ + 2`, with `|Q| = q + 1` and
`|Γ| = g + 1`. -/
def valueWidth (M : TM) : ℕ := Nat.clog 2 (M.q + 1) + M.k * Nat.clog 2 (M.g + 1) + 2

theorem card_value (M : TM) : Fintype.card (Value M) = (M.q + 1) * ((M.g + 1) ^ M.k * 3) := by
  simp [Fintype.card_prod, Fintype.card_fin, Fintype.card_option]

/-- Step values take at most `2^{β(M)}` values. -/
theorem card_value_le (M : TM) : Fintype.card (Value M) ≤ 2 ^ valueWidth M := by
  rw [card_value, valueWidth, pow_add, pow_add, mul_comm M.k, pow_mul, mul_assoc]
  have h1 := Nat.le_pow_clog (by norm_num : 1 < 2) (M.q + 1)
  have h2 := Nat.le_pow_clog (by norm_num : 1 < 2) (M.g + 1)
  gcongr
  norm_num

theorem log_card_value_le (M : TM) :
    Real.log (Fintype.card (Value M) : ℝ) / Real.log 2 ≤ valueWidth M := by
  have hpos : (0 : ℝ) < Fintype.card (Value M) := by exact_mod_cast Fintype.card_pos
  have hle : (Fintype.card (Value M) : ℝ) ≤ (2 : ℝ) ^ valueWidth M := by
    exact_mod_cast card_value_le M
  rw [div_le_iff₀ (Real.log_pos (by norm_num))]
  calc Real.log (Fintype.card (Value M) : ℝ) ≤ Real.log ((2 : ℝ) ^ valueWidth M) :=
        Real.log_le_log hpos hle
    _ = valueWidth M * Real.log 2 := Real.log_pow _ _

/-- The exact capacity of a step value in bits, `log₂ (3 |Q| |Γ|^k)`. -/
noncomputable def capacityBits (M : TM) : ℝ :=
  Real.log (Fintype.card (Value M) : ℝ) / Real.log 2

theorem capacityBits_le_valueWidth (M : TM) : capacityBits M ≤ valueWidth M :=
  log_card_value_le M

/-! ### Local determination along a frozen trace -/

section Local

variable {M : TM}

/-- The last visit `σ` of a head to its cell at time `t < T` is a parent of `t`: the state edge
if `σ = t - 1`, and otherwise the lower end of a long hop `(σ, t)` of that head. -/
theorem mem_actualParents_of_lastVisit {k : ℕ} {xs : Fin k → ℕ → ℤ} {pos : ℕ → ℤ} {T t σ : ℕ}
    (h : Fin k) (ht : t < T) (hpos : ∀ ρ ≤ t, pos ρ = xs h ρ) (hlast : IsLastVisit pos t σ) :
    σ ∈ actualParents xs T t := by
  obtain ⟨hσt, he, hgap⟩ := hlast
  rw [mem_actualParents]
  by_cases hs : σ + 1 = t
  · exact Or.inl hs
  · refine Or.inr ⟨h, by omega, ht, ?_, fun s hs => ?_⟩
    · rw [← hpos t le_rfl, ← hpos σ hσt.le, he]
    · obtain ⟨h1, h2⟩ := mem_Ioo.mp hs
      rw [← hpos s h2.le, ← hpos σ hσt.le, he]
      exact hgap s h1 h2

/-- **Local determination.** Two inputs `a, b ∈ {0,1}^L` whose traces agree with `τ` before `T`,
and a step `t < T`: if the inputs agree under the input head at time `t` (when that cell lies in
the input) and the step values agree at every parent of `t` in `actualParents τ.work T` (the state
edge and the lower ends of all long hops ending at `t`), then the values of step `t` agree. -/
theorem stepValue_eq_of_parents {L : ℕ} {τ : Trace M.k} {a b : Fin L → Bool} {T t : ℕ}
    (ha : ∀ s < T, trace M (List.ofFn a) s = τ s) (hb : ∀ s < T, trace M (List.ofFn b) s = τ s)
    (ht : t < T) (hread : ∀ p : ℕ, (p : ℤ) = τ.input t → ∀ hp : p < L, a ⟨p, hp⟩ = b ⟨p, hp⟩)
    (hpar : ∀ u ∈ actualParents τ.work T t,
      stepValue M (List.ofFn a) u = stepValue M (List.ofFn b) u) :
    stepValue M (List.ofFn a) t = stepValue M (List.ofFn b) t := by
  have hwa : ∀ ρ ≤ t, ∀ h, workTraj M (List.ofFn a) ρ h = τ.work h ρ :=
    fun ρ hρ h => workPos_eq_of_agree ha (by omega) h
  have hwork : ∀ ρ ≤ t, ∀ h, workTraj M (List.ofFn a) ρ h = workTraj M (List.ofFn b) ρ h :=
    fun ρ hρ h => (hwa ρ hρ h).trans (workPos_eq_of_agree hb (by omega) h).symm
  -- the state at time `t`
  have hstate : (run M (List.ofFn a) t).state = (run M (List.ofFn b) t).state := by
    rcases t with _ | s
    · rfl
    · exact congrArg Prod.fst (hpar s (mem_actualParents.mpr (Or.inl rfl)))
  -- the input symbol at time `t`
  have hin : inSym M (List.ofFn a) t = inSym M (List.ofFn b) t := by
    unfold inSym
    rw [inPos_eq_of_agree ha ht.le, inPos_eq_of_agree hb ht.le]
    refine readInput_eq_of_nth (L := L) List.length_ofFn List.length_ofFn ?_
    intro p hp hpL
    rw [nth_eq_getElem?, nth_eq_getElem?, List.getElem?_ofFn, List.getElem?_ofFn,
      dite_eq_left hpL, dite_eq_left hpL, hread p hp hpL]
  -- the symbols under the work heads at time `t`
  have hhead : headSym M (List.ofFn a) t = headSym M (List.ofFn b) t := by
    funext h
    have hpos : ∀ ρ ≤ t, workTraj M (List.ofFn a) ρ h = workTraj M (List.ofFn b) ρ h :=
      fun ρ hρ => hwork ρ hρ h
    by_cases hex : ∃ σ < t, workTraj M (List.ofFn a) σ h = workTraj M (List.ofFn a) t h
    · obtain ⟨σ, hlast⟩ := exists_lastVisit hex
      have hlast' := isLastVisit_congr hlast hpos
      rw [headSym_eq_writtenSym h hlast, headSym_eq_writtenSym h hlast']
      have hσ : σ ∈ actualParents τ.work T t :=
        mem_actualParents_of_lastVisit h ht (fun ρ hρ => hwa ρ hρ h) hlast
      exact congrFun (congrArg (fun v : Value M => v.2.1) (hpar σ hσ)) h
    · push Not at hex
      rw [headSym_eq_blank h hex, headSym_eq_blank h]
      intro σ hσ
      rw [← hpos σ hσ.le, ← hpos t le_rfl]
      exact hex σ hσ
  have htrans := transAt_eq_of_args hstate hin hhead
  simp only [stepValue, Prod.mk.injEq]
  refine ⟨state_succ_eq_of_transAt' hstate htrans,
    funext fun h => writtenSym_eq_of_transAt' hhead htrans h, ?_⟩
  simp only [outBit, htrans]

end Local

end MergeDepth
