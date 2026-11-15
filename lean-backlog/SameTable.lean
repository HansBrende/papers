import MergeDepth.LinearCrux
import Transpose.Tape.DefsCE

/-!
# Finite same-table tableaux and oblivious transposition

The validator below uses only a finite table, a finite motion prefix and
finite input-dependent payloads. Reads are computed by scanning earlier
writes backwards. No validity premise mentions a run or a machine trace.
The interpreter in the frozen first paper is unchanged.
-/

namespace LeanBacklog.SameTable

open Transpose Transpose.Tape Transpose.Tape.Impl MergeDepth

variable {M : TM} {T : ℕ}

/-- A finite motion prefix, extended by no action from T on. -/
def prefixTrace (μ : Fin T → Motion M.k) : Trace M.k :=
  fun t => if h : t < T then some (μ ⟨t, h⟩) else none

/-- Padding is queried only to simplify natural-number indexing. -/
def valueAt (v : Fin T → Value M) (t : ℕ) : Value M :=
  if h : t < T then v ⟨t, h⟩ else (0, fun _ => 0, none)

/-- State before a step, including the terminal time. -/
def stateBefore (v : Fin T → Value M) : ℕ → Fin (M.q + 1)
  | 0 => 0
  | t + 1 => (valueAt v t).1

/-- The last write before t at a queried position, or the initial blank.
This is a finite backward scan, not an execution of the transition table. -/
def lastWrite {A : Type*} [Zero A] (pos : ℕ → ℤ) (val : ℕ → A) : ℕ → ℤ → A
  | 0, _ => 0
  | t + 1, p => if p = pos t then val t else lastWrite pos val t p

/-- All work reads at a time, computed solely from the supplied finite data. -/
def workRead (μ : Fin T → Motion M.k) (v : Fin T → Value M) (t : ℕ)
    (i : Fin M.k) : Fin (M.g + 1) :=
  lastWrite ((prefixTrace μ).work i) (fun s => (valueAt v s).2.1 i)
    t ((prefixTrace μ).work i t)

/-- Reassemble a supplied step's full transition result. -/
def action (μ : Fin T → Motion M.k) (v : Fin T → Value M) (t : Fin T) :=
  ((v t).1, (μ t).1, fun i => ((v t).2.1 i, (μ t).2.1 i), (v t).2.2)

/-- Ordered output of the finite payload array. -/
def output (v : Fin T → Value M) : List Bool :=
  (List.range T).filterMap (fun t => (valueAt v t).2.2)

/-- Local finite-table validation, with exact terminal halting.
Only μ is shared across inputs; v and the supplied input word may vary. -/
structure Valid (μ : Fin T → Motion M.k) (v : Fin T → Value M) (w : List Bool) : Prop where
  step : ∀ t : Fin T,
    M.δ (stateBefore v t) (readInput w ((prefixTrace μ).input t)) (workRead μ v t) =
      some (action μ v t)
  appends : ∀ t : Fin T, (v t).2.2.isSome = (μ t).2.2
  halt : M.δ (stateBefore v T) (readInput w ((prefixTrace μ).input T))
    (workRead μ v T) = none

/-- Every check is over the supplied finite arrays and finite symbols. -/
instance instDecidableValid (μ : Fin T → Motion M.k) (v : Fin T → Value M) (w : List Bool) :
    Decidable (Valid μ v w) := by
  letI : DecidableEq (Fin M.k → Fin (M.g + 1) × Dir) := fun f g =>
    decidable_of_iff (∀ i, f i = g i)
      ⟨funext, fun h i => congrFun h i⟩
  exact decidable_of_iff
    ((∀ t : Fin T, M.δ (stateBefore v t) (readInput w ((prefixTrace μ).input t))
        (workRead μ v t) = some (action μ v t)) ∧
      (∀ t : Fin T, (v t).2.2.isSome = (μ t).2.2) ∧
      M.δ (stateBefore v T) (readInput w ((prefixTrace μ).input T)) (workRead μ v T) = none)
    ⟨fun h => ⟨h.1, h.2.1, h.2.2⟩, fun h => ⟨h.step, h.appends, h.halt⟩⟩

private theorem lastWrite_eq_run (w : List Bool) (i : Fin M.k)
    (pos : ℕ → ℤ) (val : ℕ → Fin (M.g + 1)) (t : ℕ) (p : ℤ)
    (hp : ∀ s < t, pos s = (run M w s).workPos i)
    (hv : ∀ s < t, val s = writtenSym M w s i) :
    lastWrite pos val t p = (run M w t).work i p := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [lastWrite, run_succ_work, hp t (by omega), hv t (by omega)]
    split_ifs
    · rfl
    · exact ih (fun s hs => hp s (by omega)) (fun s hs => hv s (by omega))

private structure Matches (μ : Fin T → Motion M.k) (v : Fin T → Value M)
    (w : List Bool) (t : ℕ) : Prop where
  state : (run M w t).state = stateBefore v t
  input : (run M w t).inPos = (prefixTrace μ).input t
  position : ∀ i, (run M w t).workPos i = (prefixTrace μ).work i t
  tape : ∀ i p, (run M w t).work i p =
    lastWrite ((prefixTrace μ).work i) (fun s => (valueAt v s).2.1 i) t p

private theorem Matches.reads {μ : Fin T → Motion M.k} {v : Fin T → Value M}
    {w : List Bool} {t : ℕ} (h : Matches μ v w t) :
    headSym M w t = workRead μ v t := by
  funext i
  rw [headSym, h.tape, h.position]
  rfl

private theorem Matches.transition {μ : Fin T → Motion M.k} {v : Fin T → Value M}
    {w : List Bool} {t : ℕ} (h : Matches μ v w t) (hv : Valid μ v w) (ht : t < T) :
    transAt M w t = some (action μ v ⟨t, ht⟩) := by
  unfold transAt inSym
  rw [h.state, h.input, h.reads]
  exact hv.step ⟨t, ht⟩

private theorem replay_matches {μ : Fin T → Motion M.k} {v : Fin T → Value M}
    {w : List Bool} (h : Valid μ v w) (t : ℕ) (ht : t ≤ T) : Matches μ v w t := by
  induction t with
  | zero =>
    refine ⟨rfl, ?_, ?_, fun _ _ => rfl⟩
    · exact (Trace.input_zero _).symm
    · intro i; exact (Trace.work_zero _ i).symm
  | succ t ih =>
    have hlt : t < T := by omega
    have hm := ih (by omega)
    have ha := hm.transition h hlt
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [run_succ_of_some ha]
      simp [stateBefore, valueAt, hlt]
    · rw [run_succ_of_some ha]
      simp [hm.input, Trace.input_succ, Trace.inStep, prefixTrace, hlt,
        shift_eq_add_moveInt]
    · intro i
      rw [run_succ_of_some ha]
      simp [hm.position, Trace.work_succ, Trace.workStep, prefixTrace, hlt,
        shift_eq_add_moveInt]
    · intro i p
      rw [run_succ_of_some ha]
      simp [lastWrite, valueAt, hlt, hm.position, hm.tape]

/-- Local validity determines every transition, the exact halt and the ordered
output. This one-input replay core does not assume obliviousness. -/
theorem replay {μ : Fin T → Motion M.k} {v : Fin T → Value M} {w : List Bool}
    (h : Valid μ v w) :
    (∀ t : Fin T, transAt M w t = some (action μ v t)) ∧
    HaltsAt M w T ∧ (run M w T).outRev.reverse = output v := by
  have hs : ∀ t : Fin T, transAt M w t = some (action μ v t) :=
    fun t => (replay_matches h t (by omega)).transition h t.isLt
  have hn : transAt M w T = none := by
    have hm := replay_matches h T le_rfl
    unfold transAt inSym
    rw [hm.state, hm.input, hm.reads]
    exact h.halt
  refine ⟨hs, ⟨fun t ht => by rw [hs ⟨t, ht⟩]; simp, hn⟩, ?_⟩
  rw [outRev_reverse_eq]
  apply List.filterMap_congr
  intro t ht
  have hlt := List.mem_range.mp ht
  simp [outBit, hs ⟨t, hlt⟩, action, valueAt, hlt]

/-- Direct frozen-model consumer, with exactly the supplied time and output. -/
theorem computesWithin {μ : Fin T → Motion M.k} {v : Fin T → Value M} {w : List Bool}
    (h : Valid μ v w) : ComputesWithin M w (output v) T :=
  (computesWithin_iff _ _).mpr ⟨T, le_rfl, (replay h).2⟩

/-- Shared finite motion forces the first paper's all-time obliviousness,
on any prescribed input set. Only the payloads depend on the input. -/
theorem obliviousOn (μ : Fin T → Motion M.k) (W : Set (List Bool))
    (h : ∀ w ∈ W, ∃ v, Valid μ v w) : ObliviousOn M W T := by
  refine ⟨fun w hw => (replay (h w hw).choose_spec).2.1, ?_⟩
  intro w hw w' hw' t
  obtain ⟨v, hv⟩ := h w hw
  obtain ⟨v', hv'⟩ := h w' hw'
  have freeze {u : List Bool} {z : Fin T → Value M} (hz : Valid μ z u) :
      run M u t = run M u (min t T) := by
    by_cases ht : t ≤ T
    · rw [min_eq_left ht]
    · rw [min_eq_right (by omega : T ≤ t)]
      exact run_of_le_of_none (replay hz).2.1.2 (by omega)
  have hm := replay_matches hv (min t T) (min_le_right _ _)
  have hm' := replay_matches hv' (min t T) (min_le_right _ _)
  refine ⟨?_, ?_, ?_⟩
  · rw [freeze hv, freeze hv', hm.input, hm'.input]
  · ext i
    rw [freeze hv, freeze hv', hm.position, hm'.position]
  · by_cases ht : t < T
    · simp only [outBit, (replay hv).1 ⟨t, ht⟩, (replay hv').1 ⟨t, ht⟩, action]
      exact (hv.appends ⟨t, ht⟩).trans (hv'.appends ⟨t, ht⟩).symm
    · simp [outBit, transAt_of_le_of_none (replay hv).2.1.2 (by omega : T ≤ t),
        transAt_of_le_of_none (replay hv').2.1.2 (by omega : T ≤ t)]

private theorem extracted_matches (μ : Fin T → Motion M.k) (w : List Bool)
    (hag : ∀ s < T, trace M w s = prefixTrace μ s) (t : ℕ) (ht : t ≤ T) :
    Matches μ (fun s : Fin T => stepValue M w s) w t := by
  refine ⟨?_, inPos_eq_of_agree hag ht, fun i => workPos_eq_of_agree hag ht i, ?_⟩
  · cases t with
    | zero => rfl
    | succ t => simp [stateBefore, valueAt, show t < T by omega, stepValue]
  · intro i p
    symm
    apply lastWrite_eq_run
    · intro s hs
      exact (workPos_eq_of_agree hag (by omega : s ≤ T) i).symm
    · intro s hs
      simp [valueAt, show s < T by omega, stepValue]

/-- Forward extraction validates the existing run payloads. Actual-run
premises occur here, never in `Valid` or the tableau-family predicate. -/
theorem valid_of_run (μ : Fin T → Motion M.k) (w : List Bool)
    (hag : ∀ t : Fin T, trace M w t = some (μ t)) (hn : transAt M w T = none) :
    Valid μ (fun t : Fin T => stepValue M w t) w := by
  have hag' : ∀ s < T, trace M w s = prefixTrace μ s := by
    intro s hs
    simpa [prefixTrace, hs] using hag ⟨s, hs⟩
  refine ⟨?_, ?_, ?_⟩
  · intro t
    have hm := extracted_matches μ w hag' t (by omega)
    rw [← hm.state, ← hm.input, ← hm.reads]
    change transAt M w t = _
    have he := hag t
    rcases hx : transAt M w t with _ | ⟨s, d, a, o⟩
    · simp [trace, hx] at he
    · have hμ : μ t = (d, fun i => (a i).2, o.isSome) := by
        simpa [trace, hx] using he.symm
      simp [action, hμ, stepValue, run_succ_state_of_some hx, writtenSym, outBit, hx]
  · intro t
    have he := hag t
    rcases hx : transAt M w t with _ | ⟨s, d, a, o⟩
    · simp [trace, hx] at he
    · have hμ : μ t = (d, fun i => (a i).2, o.isSome) := by
        simpa [trace, hx] using he.symm
      simp [stepValue, outBit, hx, hμ]
  · have hm := extracted_matches μ w hag' T le_rfl
    rw [← hm.state, ← hm.input, ← hm.reads]
    exact hn

/-- All inputs of one size have locally valid tableaux with common motion,
and the payloads append the transpose in order. This mentions no execution. -/
def TransposeTableaux (M : TM) (d b T : ℕ) : Prop :=
  ∃ μ : Fin T → Motion M.k, ∀ A : Matrix, ∃ v : Fin T → Value M,
    Valid μ v (encode d b A) ∧ output v = encode d b (transpose A)

/-- Finite tableau validity implies exactly the native per-size premises. -/
theorem transposeTableaux_sound {d b : ℕ} (h : TransposeTableaux M d b T) :
    ObliviousOn M (inputsOfLength (d * d * b)) T ∧ Transposes M d b := by
  obtain ⟨μ, hμ⟩ := h
  refine ⟨obliviousOn μ _ ?_, ?_⟩
  · intro w hw
    have hw' : w ∈ matrixInputs d b := by rwa [matrixInputs_eq]
    obtain ⟨A, rfl⟩ := hw'
    obtain ⟨v, hv, _⟩ := hμ A
    exact ⟨v, hv⟩
  · intro A
    obtain ⟨v, hv, hout⟩ := hμ A
    exact ⟨T, hout ▸ computesWithin hv⟩

private theorem trace_eq_zero_of_oblivious {L : ℕ}
    (h : ObliviousOn M (inputsOfLength L) T) (w : List Bool) (hw : w.length = L)
    (s : ℕ) (hs : s < T) :
    trace M w s = trace M (List.ofFn (fun _ : Fin L => false)) s := by
  subst L
  simpa using followsTrace_of_obliviousOn h (fun _ => false) w.get s hs

/-- Forward extraction at one size; the common schedule is chosen on the
all-zero input, before the matrix input used for its payloads. -/
theorem transposeTableaux_complete {d b : ℕ}
    (hobl : ObliviousOn M (inputsOfLength (d * d * b)) T) (htr : Transposes M d b) :
    TransposeTableaux M d b T := by
  let w₀ := List.ofFn (fun _ : Fin (d * d * b) => false)
  have hw₀ : w₀ ∈ inputsOfLength (d * d * b) := List.length_ofFn
  let μ : Fin T → Motion M.k := fun t =>
    (trace M w₀ t).getD (.stay, fun _ => .stay, false)
  have hμ : ∀ t : Fin T, trace M w₀ t = some (μ t) := by
    intro t
    have hn := (hobl.1 w₀ hw₀).1 t t.isLt
    rcases hx : transAt M w₀ t with _ | a
    · exact (hn hx).elim
    · simp [μ, trace, hx]
  refine ⟨μ, ?_⟩
  intro A
  have hw : encode d b A ∈ inputsOfLength (d * d * b) := length_encode d b A
  have hv := valid_of_run μ (encode d b A) (fun t =>
    (trace_eq_zero_of_oblivious hobl _ hw t t.isLt).trans (hμ t))
      (hobl.1 _ hw).2
  refine ⟨fun t => stepValue M (encode d b A) t, hv, ?_⟩
  obtain ⟨bound, hb⟩ := htr A
  obtain ⟨s, _, hs, hout⟩ := (computesWithin_iff _ _).mp hb
  have he : s = T := haltsAt_unique hs (hobl.1 _ hw)
  subst s
  exact (replay hv).2.2.symm.trans hout

/-- Exact per-size equivalence, including the terminal-time convention. -/
theorem transposeTableaux_iff {d b : ℕ} : TransposeTableaux M d b T ↔
    ObliviousOn M (inputsOfLength (d * d * b)) T ∧ Transposes M d b :=
  ⟨transposeTableaux_sound, fun h => transposeTableaux_complete h.1 h.2⟩

/-- The precise per-size predicate consumed by B1, with no time overhead. -/
theorem obliviousLinTime_iff {d b : ℕ} {C : ℝ} :
    ObliviousLinTime M d b C T ↔
      TransposeTableaux M d b T ∧ (T : ℝ) ≤ C * ((d * d * b : ℕ) + 1) := by
  rw [transposeTableaux_iff]
  exact ⟨fun h => ⟨⟨h.1, h.2.2⟩, h.2.1⟩,
    fun h => ⟨h.1.1, h.2, h.1.2⟩⟩

/-- Raw finite data for the global tableau condition. The table and natural
time constant precede every size; within a size, `TransposeTableaux` chooses
motion before the input and permits only the payloads to depend on it.
There is no run, trace-of-a-machine or computation predicate in this definition. -/
def UniformTableaux : Prop :=
  ∃ (k g q : ℕ)
    (δ : Fin (q + 1) → Option Bool → (Fin k → Fin (g + 1)) →
      Option (Fin (q + 1) × Dir × (Fin k → Fin (g + 1) × Dir) × Option Bool))
    (c : ℕ), ∀ d, 1 ≤ d → ∃ T, T ≤ c * (inputLength d + 1) ∧
      TransposeTableaux ⟨k, g, q, δ⟩ d (entryBits d) T

/-- Exact top rung for oblivious families, with the existing all-time notion
of obliviousness. This is not an equivalence with the adaptive frozen (T). -/
theorem uniformTableaux_iff : UniformTableaux ↔ ObliviousLinearTimeTransposable := by
  constructor
  · rintro ⟨k, g, q, δ, c, h⟩
    let M : TM := ⟨k, g, q, δ⟩
    refine ⟨M, c, ?_, ?_⟩
    · intro d hd A
      obtain ⟨T, hT, μ, hμ⟩ := h d hd
      obtain ⟨v, hv, hout⟩ := hμ A
      exact (computesWithin_iff _ _).mpr
        ⟨T, hT, (replay hv).2.1, (replay hv).2.2.trans hout⟩
    · intro d hd
      obtain ⟨T, _, hT⟩ := h d hd
      exact ⟨T, by simpa [matrixInputs_eq] using (transposeTableaux_sound hT).1⟩
  · rintro ⟨M, c, htr, hobl⟩
    refine ⟨M.k, M.g, M.q, M.δ, c, ?_⟩
    intro d hd
    obtain ⟨T, hT⟩ := hobl d hd
    have hT' : ObliviousOn M (inputsOfLength (d * d * entryBits d)) T := by
      simpa [matrixInputs_eq] using hT
    obtain ⟨s, hbound, hs, _⟩ := (computesWithin_iff _ _).mp (htr d hd (fun _ _ _ => false))
    have hw : encode d (entryBits d) (fun _ _ _ => false) ∈
        inputsOfLength (d * d * entryBits d) := length_encode _ _ _
    have he : s = T := haltsAt_unique hs (hT'.1 _ hw)
    refine ⟨T, he ▸ hbound, ?_⟩
    exact transposeTableaux_complete hT' (fun A => ⟨_, htr d hd A⟩)

#print axioms prefixTrace
#print axioms valueAt
#print axioms stateBefore
#print axioms lastWrite
#print axioms workRead
#print axioms action
#print axioms output
#print axioms Valid
#print axioms instDecidableValid
#print axioms replay
#print axioms computesWithin
#print axioms obliviousOn
#print axioms valid_of_run
#print axioms TransposeTableaux
#print axioms transposeTableaux_sound
#print axioms transposeTableaux_complete
#print axioms transposeTableaux_iff
#print axioms obliviousLinTime_iff
#print axioms UniformTableaux
#print axioms uniformTableaux_iff

end LeanBacklog.SameTable
