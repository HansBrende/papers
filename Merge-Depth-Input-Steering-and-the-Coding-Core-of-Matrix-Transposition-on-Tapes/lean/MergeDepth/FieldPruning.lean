import MergeDepth.FieldDag
import MergeDepth.LowAdaptivity

set_option autoImplicit false

/-!
# The field DAG of a pruning (Section 3.2, "The field DAG")

The *fields* of step `t` are the state `σ_t` after the step, the symbol `κ_{t,j}` written on work
tape `j < k`, and the output field `o_t` (the appended bit or its absence). Field `i` of step `t` is
the node `t (k + 2) + i`: `i = 0` is the state, `i = j + 1` the symbol of tape `j`, `i = k + 1` the
output field (`stateNode`, `symbolNode`, `outputNode`); `fieldVal M w u` is the value of node `u` on
the input `w`, a function of the step value `stepValue M w t` (`fieldOf`).

The *predecessors* of the fields of step `t < T` (`stepPreds`) are the state node of step `t - 1`
(if `t ≥ 1`) and, for every work head `j` whose cell at time `t` was visited before, the symbol
node `j` of its last visit `prev_j(t)`, along the work walks `τ₀.work` of a trace.

* `stepValue_eq_of_fields`, `stepValue_eq_of_preds`: **the field-level local recursion** (the
  fourth paper's Lemma 4.2 at field level). Two inputs whose traces agree with `τ₀` before `T`
  give step `t < T` the same value, hence the same fields, if they agree on the predecessor fields
  of step `t` and on the input bit read at step `t` (`readPos`).
* `Pruning`: a pruning chooses for every field node `u` a set `P u` of predecessors and a flag
  `keep u` such that, on `{0,1}^L`, the field is a function of the fields in `P u` and of the kept
  input bit. `Pruning.full` (keeping everything) is a pruning when all inputs follow `τ₀` before
  `T` (`FollowsTrace`).
* `Pruning.toFunDag`: the field DAG of a pruning as a function DAG (`FunDag`), with edges
  `u → v` for `v ∈ P u`, input marks at the kept fields of the steps `t < T`, and the field values
  (the constant `0` at steps `t ≥ T`). Its refinement facts, the hypotheses of
  `hop_charging_fields`: `mem_fieldNodesAt`, `card_fieldNodesAt` (width `k + 2`), `toFunDag_edge`
  (edges are dependency steps of `τ₀.work`), `toFunDag_rd` (input marks read the position under
  the input head), `toFunDag_step_card`, `toFunDag_field_card` (at most `2^β` values for
  `β ≥ β(M)`), and, for an oblivious transposer, the output decoding `toFunDag_dec`.
* `toFunDag_deep_edge`: a deep edge leads from step `t` to a symbol field of a step `≤ t - 2`.
* `followsTrace_of_obliviousOn`, `ObliviousTransposer.of_obliviousOn`: a machine oblivious at length
  `L` in the frozen model (`ObliviousOn`) follows the trace of any input, and a transposer appends
  exactly `L` bits before its halting time.
-/

namespace MergeDepth

open Finset Transpose Transpose.Tape Transpose.Tape.Impl SourceCovers BoundedNesting LeanMachine

/-! ### Field nodes -/

theorem node_div {n t i : ℕ} (hi : i < n) : (t * n + i) / n = t := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega : 0 < n), Nat.div_eq_of_lt hi, zero_add]

theorem node_mod {n t i : ℕ} (hi : i < n) : (t * n + i) % n = i := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]

/-- The state node `σ_t` of step `t`. -/
def stateNode (k t : ℕ) : ℕ := t * (k + 2)

/-- The symbol node `κ_{t,j}` of step `t` and work tape `j`. -/
def symbolNode (k t : ℕ) (j : Fin k) : ℕ := t * (k + 2) + (j + 1)

/-- The output node `o_t` of step `t`. -/
def outputNode (k t : ℕ) : ℕ := t * (k + 2) + (k + 1)

/-- The `k + 2` field nodes of step `t`. -/
def fieldNodesAt (k t : ℕ) : Finset ℕ := Ico (t * (k + 2)) ((t + 1) * (k + 2))

theorem mem_fieldNodesAt {k u t : ℕ} : u ∈ fieldNodesAt k t ↔ u / (k + 2) = t := by
  have hn : 0 < k + 2 := by omega
  rw [fieldNodesAt, mem_Ico]
  constructor
  · rintro ⟨h1, h2⟩
    have e1 : t ≤ u / (k + 2) := (Nat.le_div_iff_mul_le hn).mpr h1
    have e2 : u / (k + 2) < t + 1 := (Nat.div_lt_iff_lt_mul hn).mpr h2
    omega
  · rintro rfl
    refine ⟨Nat.div_mul_le_self u (k + 2), ?_⟩
    have := Nat.lt_div_mul_add (a := u) hn
    rw [Nat.add_mul, one_mul]
    omega

theorem card_fieldNodesAt (k t : ℕ) : (fieldNodesAt k t).card = k + 2 := by
  rw [fieldNodesAt, Nat.card_Ico, Nat.add_mul, one_mul, Nat.add_sub_cancel_left]

theorem stateNode_div (k t : ℕ) : stateNode k t / (k + 2) = t :=
  Nat.mul_div_cancel t (by omega)

theorem stateNode_mod (k t : ℕ) : stateNode k t % (k + 2) = 0 := by
  simp [stateNode]

theorem symbolNode_div (k t : ℕ) (j : Fin k) : symbolNode k t j / (k + 2) = t :=
  node_div (by omega)

theorem outputNode_div (k t : ℕ) : outputNode k t / (k + 2) = t := node_div (by omega)

/-! ### Fields of a step -/

/-- The code of an output field: `0` for no bit, `1` for `false`, `2` for `true`. -/
def encOut : Option Bool → ℕ
  | none => 0
  | some false => 1
  | some true => 2

/-- The bit of an output field. -/
def decOut (n : ℕ) : Bool := decide (n = 2)

theorem decOut_encOut (x : Bool) : decOut (encOut (some x)) = x := by
  cases x <;> rfl

theorem encOut_lt (o : Option Bool) : encOut o < 3 := by
  rcases o with _ | _ | _ <;> simp [encOut]

variable (M : TM)

/-- Field `i` of a step value, as a natural number: `i = 0` the state after the step, `i = j + 1`
with `j < k` the symbol written on work tape `j`, and otherwise the output field. -/
def fieldOf (i : ℕ) (v : Value M) : ℕ :=
  if i = 0 then (v.1 : ℕ) else if h : i - 1 < M.k then (v.2.1 ⟨i - 1, h⟩ : ℕ) else encOut v.2.2

/-- The value of the field node `u = t (k + 2) + i` on input `w`: field `i` of step `t`. -/
def fieldVal (w : List Bool) (u : ℕ) : ℕ :=
  fieldOf M (u % (M.k + 2)) (stepValue M w (u / (M.k + 2)))

theorem fieldVal_stateNode (w : List Bool) (t : ℕ) :
    fieldVal M w (stateNode M.k t) = ((run M w (t + 1)).state : ℕ) := by
  rw [fieldVal, stateNode_div, stateNode_mod]
  rfl

theorem fieldVal_symbolNode (w : List Bool) (t : ℕ) (j : Fin M.k) :
    fieldVal M w (symbolNode M.k t j) = (writtenSym M w t j : ℕ) := by
  have h : symbolNode M.k t j % (M.k + 2) = j + 1 := node_mod (by omega)
  have hj : (j : ℕ) + 1 - 1 < M.k := by omega
  simp only [fieldVal, symbolNode_div, h, fieldOf, Nat.add_one_ne_zero, ↓reduceIte, hj,
    ↓reduceDIte, stepValue]
  rfl

theorem fieldVal_outputNode (w : List Bool) (t : ℕ) :
    fieldVal M w (outputNode M.k t) = encOut (outBit M w t) := by
  have h : outputNode M.k t % (M.k + 2) = M.k + 1 := node_mod (by omega)
  have hj : ¬ (M.k + 1 - 1 < M.k) := by omega
  simp only [fieldVal, outputNode_div, h, fieldOf, Nat.add_one_ne_zero, ↓reduceIte, hj,
    ↓reduceDIte, stepValue]

/-- A field is a function of the step value: `fieldVal M w u` depends on `w` only through the value
of the step of `u`. -/
theorem fieldVal_eq_of_stepValue {w w' : List Bool} {u : ℕ}
    (h : stepValue M w (u / (M.k + 2)) = stepValue M w' (u / (M.k + 2))) :
    fieldVal M w u = fieldVal M w' u := by
  simp only [fieldVal, h]

/-! ### Predecessors -/

open Classical in
/-- The predecessors of the fields of step `t`, for `t < T`: the state node of step `t - 1` if
`t ≥ 1`, and, for every work head `j` whose cell at time `t` was visited before, the symbol node `j`
of its last visit `prev_j(t)`. Empty for `t ≥ T`. -/
noncomputable def stepPreds (k : ℕ) (xs : Fin k → ℕ → ℤ) (T t : ℕ) : Finset ℕ :=
  if t < T then
    ((range t).filter fun s => s + 1 = t).image (fun s => stateNode k s) ∪
      univ.biUnion fun j : Fin k =>
        ((range t).filter fun σ => IsLastVisit (xs j) t σ).image fun σ => symbolNode k σ j
  else ∅

theorem mem_stepPreds {k : ℕ} {xs : Fin k → ℕ → ℤ} {T t v : ℕ} :
    v ∈ stepPreds k xs T t ↔ t < T ∧
      ((∃ s, s + 1 = t ∧ v = stateNode k s) ∨
        ∃ (j : Fin k) (σ : ℕ), IsLastVisit (xs j) t σ ∧ v = symbolNode k σ j) := by
  classical
  unfold stepPreds
  split_ifs with ht
  · simp only [mem_union, mem_image, mem_filter, mem_range, mem_biUnion, mem_univ, true_and, ht]
    constructor
    · rintro (⟨s, ⟨-, hs⟩, rfl⟩ | ⟨j, σ, ⟨-, hσ⟩, rfl⟩)
      · exact Or.inl ⟨s, hs, rfl⟩
      · exact Or.inr ⟨j, σ, hσ, rfl⟩
    · rintro (⟨s, hs, rfl⟩ | ⟨j, σ, hσ, rfl⟩)
      · exact Or.inl ⟨s, ⟨by omega, hs⟩, rfl⟩
      · exact Or.inr ⟨j, σ, ⟨hσ.1, hσ⟩, rfl⟩
  · simp [ht]

/-- The predecessors of step `t` lie at earlier steps. -/
theorem stepPreds_step_lt {k : ℕ} {xs : Fin k → ℕ → ℤ} {T t v : ℕ} (hv : v ∈ stepPreds k xs T t) :
    v / (k + 2) < t := by
  rcases (mem_stepPreds.mp hv).2 with ⟨s, hs, rfl⟩ | ⟨j, σ, hσ, rfl⟩
  · rw [stateNode_div]; omega
  · rw [symbolNode_div]; exact hσ.1

/-- The predecessors of step `t` are smaller than the field nodes of step `t`. -/
theorem stepPreds_lt {k : ℕ} {xs : Fin k → ℕ → ℤ} {T t v : ℕ} (hv : v ∈ stepPreds k xs T t) :
    v < t * (k + 2) := by
  have h1 := stepPreds_step_lt hv
  have h2 := Nat.lt_div_mul_add (a := v) (show 0 < k + 2 by omega)
  calc v < (v / (k + 2) + 1) * (k + 2) := by rw [Nat.add_mul, one_mul]; exact h2
    _ ≤ t * (k + 2) := Nat.mul_le_mul_right _ h1

theorem stepPreds_step_lt_T {k : ℕ} {xs : Fin k → ℕ → ℤ} {T t v : ℕ} (hv : v ∈ stepPreds k xs T t) :
    t < T :=
  (mem_stepPreds.mp hv).1

/-- **Edges project to dependency steps.** A predecessor of step `t` lies at step `t - 1` (a state
edge) or at the last visit `σ` of a head to its cell at time `t` (a state edge if `σ = t - 1`, and a
long hop `(σ, t)` of that head otherwise). -/
theorem depStep_of_mem_stepPreds {k : ℕ} {xs : Fin k → ℕ → ℤ} {T t v : ℕ}
    (hv : v ∈ stepPreds k xs T t) : DepStep xs T t (v / (k + 2)) := by
  obtain ⟨ht, h⟩ := mem_stepPreds.mp hv
  rcases h with ⟨s, hs, rfl⟩ | ⟨j, σ, hσ, rfl⟩
  · rw [stateNode_div]
    exact Or.inl ⟨hs, ht⟩
  · rw [symbolNode_div]
    obtain ⟨hσt, he, hgap⟩ := hσ
    by_cases hs : σ + 1 = t
    · exact Or.inl ⟨hs, ht⟩
    · refine Or.inr (mem_image.mpr ⟨(j, σ, t), mem_allHops.mpr
        (show IsHop (xs j) T σ t from ⟨by omega, ht, he.symm, ?_⟩), rfl⟩)
      intro ρ hρ
      obtain ⟨h1, h2⟩ := mem_Ioo.mp hρ
      rw [he]
      exact hgap ρ h1 h2

/-! ### The input position read at a step -/

/-- The input position read at step `t` of the trace `τ₀`: the input-head position, if it lies in
`[0, L)`. -/
def readPos {k : ℕ} (τ₀ : Trace k) (L t : ℕ) : Option (Fin L) :=
  if h : 0 ≤ τ₀.input t ∧ τ₀.input t < L then some ⟨(τ₀.input t).toNat, by omega⟩ else none

theorem readPos_eq_some {k : ℕ} {τ₀ : Trace k} {L t p : ℕ} (hp : (p : ℤ) = τ₀.input t)
    (hpL : p < L) : readPos τ₀ L t = some ⟨p, hpL⟩ := by
  have h : 0 ≤ τ₀.input t ∧ τ₀.input t < L := by omega
  unfold readPos
  split_ifs
  congr
  omega

theorem readPos_eq_some_iff {k : ℕ} {τ₀ : Trace k} {L t : ℕ} {j : Fin L} :
    readPos τ₀ L t = some j ↔ τ₀.input t = (j : ℤ) := by
  constructor
  · intro h
    unfold readPos at h
    split_ifs at h with h'
    obtain rfl := Option.some.inj h
    simp only
    omega
  · intro h
    exact readPos_eq_some h.symm j.2

/-! ### The field-level local recursion -/

section Local

variable {M}

/-- **The local recursion at field level** (the fourth paper's Lemma 4.2, with its fields). Two
inputs `a, b ∈ {0,1}^L` whose traces agree with `τ₀` before `T`, and a step `t < T`: if the inputs
agree under the input head at time `t` (when that cell lies in the input), the states at time `t`
agree (the state field `σ_{t-1}`, for `t ≥ 1`), and for every work head `h` whose cell at time `t`
was visited before, the symbols written on tape `h` at its last visit `σ` agree (the symbol field
`κ_{σ,h}`), then the values of step `t` agree. -/
theorem stepValue_eq_of_fields {L : ℕ} {τ₀ : Trace M.k} {a b : Fin L → Bool} {T t : ℕ}
    (ha : ∀ s < T, trace M (List.ofFn a) s = τ₀ s) (hb : ∀ s < T, trace M (List.ofFn b) s = τ₀ s)
    (ht : t < T) (hread : ∀ p : ℕ, (p : ℤ) = τ₀.input t → ∀ hp : p < L, a ⟨p, hp⟩ = b ⟨p, hp⟩)
    (hstate : 1 ≤ t → (run M (List.ofFn a) t).state = (run M (List.ofFn b) t).state)
    (hsym : ∀ (h : Fin M.k) (σ : ℕ), IsLastVisit (τ₀.work h) t σ →
      writtenSym M (List.ofFn a) σ h = writtenSym M (List.ofFn b) σ h) :
    stepValue M (List.ofFn a) t = stepValue M (List.ofFn b) t := by
  have hwa : ∀ ρ ≤ t, ∀ h, workTraj M (List.ofFn a) ρ h = τ₀.work h ρ :=
    fun ρ hρ h => workPos_eq_of_agree ha (by omega) h
  have hwork : ∀ ρ ≤ t, ∀ h, workTraj M (List.ofFn a) ρ h = workTraj M (List.ofFn b) ρ h :=
    fun ρ hρ h => (hwa ρ hρ h).trans (workPos_eq_of_agree hb (by omega) h).symm
  -- the state at time `t`
  have hst : (run M (List.ofFn a) t).state = (run M (List.ofFn b) t).state := by
    rcases t with _ | s
    · rfl
    · exact hstate (by omega)
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
      exact hsym h σ (isLastVisit_congr hlast fun ρ hρ => hwa ρ hρ h)
    · push Not at hex
      rw [headSym_eq_blank h hex, headSym_eq_blank h]
      intro σ hσ
      rw [← hpos σ hσ.le, ← hpos t le_rfl]
      exact hex σ hσ
  have htrans := transAt_eq_of_args hst hin hhead
  simp only [stepValue, Prod.mk.injEq]
  refine ⟨state_succ_eq_of_transAt' hst htrans,
    funext fun h => writtenSym_eq_of_transAt' hhead htrans h, ?_⟩
  simp only [outBit, htrans]

/-- **The local recursion at field level, node form.** If two inputs whose traces agree with `τ₀`
before `T` agree at the input position read at step `t < T` and at every predecessor node of the
fields of step `t`, the values of step `t` agree; so does every field of step `t`. -/
theorem stepValue_eq_of_preds {L : ℕ} {τ₀ : Trace M.k} {a b : Fin L → Bool} {T t : ℕ}
    (ha : ∀ s < T, trace M (List.ofFn a) s = τ₀ s) (hb : ∀ s < T, trace M (List.ofFn b) s = τ₀ s)
    (ht : t < T) (hread : ∀ j, readPos τ₀ L t = some j → a j = b j)
    (hpred : ∀ v ∈ stepPreds M.k τ₀.work T t,
      fieldVal M (List.ofFn a) v = fieldVal M (List.ofFn b) v) :
    stepValue M (List.ofFn a) t = stepValue M (List.ofFn b) t := by
  refine stepValue_eq_of_fields ha hb ht (fun p hp hpL => hread _ (readPos_eq_some hp hpL)) ?_ ?_
  · intro h1
    have hv : stateNode M.k (t - 1) ∈ stepPreds M.k τ₀.work T t :=
      mem_stepPreds.mpr ⟨ht, Or.inl ⟨t - 1, by omega, rfl⟩⟩
    have := hpred _ hv
    rw [fieldVal_stateNode, fieldVal_stateNode, Nat.sub_add_cancel h1] at this
    exact Fin.ext this
  · intro h σ hσ
    have hv : symbolNode M.k σ h ∈ stepPreds M.k τ₀.work T t :=
      mem_stepPreds.mpr ⟨ht, Or.inr ⟨h, σ, hσ, rfl⟩⟩
    have := hpred _ hv
    rw [fieldVal_symbolNode, fieldVal_symbolNode] at this
    exact Fin.ext this

/-- **The local recursion for one field.** Every field node `u` of a step `t < T` is, on inputs
whose traces agree with `τ₀` before `T`, a function of its predecessor fields and of the input bit
read at its step. -/
theorem fieldVal_eq_of_preds {L : ℕ} {τ₀ : Trace M.k} {a b : Fin L → Bool} {T u : ℕ}
    (ha : ∀ s < T, trace M (List.ofFn a) s = τ₀ s) (hb : ∀ s < T, trace M (List.ofFn b) s = τ₀ s)
    (hu : u / (M.k + 2) < T) (hread : ∀ j, readPos τ₀ L (u / (M.k + 2)) = some j → a j = b j)
    (hpred : ∀ v ∈ stepPreds M.k τ₀.work T (u / (M.k + 2)),
      fieldVal M (List.ofFn a) v = fieldVal M (List.ofFn b) v) :
    fieldVal M (List.ofFn a) u = fieldVal M (List.ofFn b) u :=
  fieldVal_eq_of_stepValue M (stepValue_eq_of_preds ha hb hu hread hpred)

end Local

/-! ### Prunings -/

/-- All inputs of length `L` follow the trace `τ₀` before `T` (the machine is oblivious at length
`L` up to time `T`). -/
def FollowsTrace (M : TM) (L : ℕ) (τ₀ : Trace M.k) (T : ℕ) : Prop :=
  ∀ w : Fin L → Bool, ∀ s < T, trace M (List.ofFn w) s = τ₀ s

/-- A **pruning** of the field DAG of `M` at length `L`, along the trace `τ₀` before `T`: for every
field node `u` a set `P u` of predecessors of the fields of its step and a flag `keep u`, such that,
on `{0,1}^L`, the field `u` of a step `t < T` is a function of the fields in `P u` and, if `u` keeps
it, of the input bit read at step `t`. -/
structure Pruning (M : TM) (L : ℕ) (τ₀ : Trace M.k) (T : ℕ) where
  /-- The kept predecessors of a field. -/
  P : ℕ → Finset ℕ
  /-- Whether a field keeps its input bit. -/
  keep : ℕ → Bool
  P_subset : ∀ u, P u ⊆ stepPreds M.k τ₀.work T (u / (M.k + 2))
  det : ∀ (w w' : Fin L → Bool) (u : ℕ), u / (M.k + 2) < T →
    (∀ v ∈ P u, fieldVal M (List.ofFn w) v = fieldVal M (List.ofFn w') v) →
    (keep u = true → ∀ j, readPos τ₀ L (u / (M.k + 2)) = some j → w j = w' j) →
    fieldVal M (List.ofFn w) u = fieldVal M (List.ofFn w') u

namespace Pruning

variable {M} {L : ℕ} {τ₀ : Trace M.k} {T : ℕ}

/-- **Keeping everything is a pruning**, by the field-level local recursion. -/
noncomputable def full (hobl : FollowsTrace M L τ₀ T) : Pruning M L τ₀ T where
  P u := stepPreds M.k τ₀.work T (u / (M.k + 2))
  keep _ := true
  P_subset _ := subset_rfl
  det w w' _ hu hP hk := fieldVal_eq_of_preds (hobl w) (hobl w') hu (hk rfl) hP

@[simp] theorem full_P (hobl : FollowsTrace M L τ₀ T) (u : ℕ) :
    (full hobl).P u = stepPreds M.k τ₀.work T (u / (M.k + 2)) := rfl

@[simp] theorem full_keep (hobl : FollowsTrace M L τ₀ T) (u : ℕ) : (full hobl).keep u = true :=
  rfl

variable (Pr : Pruning M L τ₀ T)

/-- **The field DAG of a pruning** as a function DAG: its vertices are the field nodes
`t (k + 2) + i`, its edges `u → v` for `v ∈ P u`, its input marks the kept fields of the steps
`t < T`, reading the position `readPos τ₀ L t`, and its values the field values at the steps
`t < T` (the constant `0` from `T` on). -/
noncomputable def toFunDag : FunDag L where
  out := Pr.P
  out_lt u v hv := (stepPreds_lt (Pr.P_subset u hv)).trans_le (Nat.div_mul_le_self u (M.k + 2))
  rd u := if Pr.keep u = true ∧ u / (M.k + 2) < T then readPos τ₀ L (u / (M.k + 2)) else none
  val w u := if u / (M.k + 2) < T then fieldVal M (List.ofFn w) u else 0
  det w w' u hout hrd := by
    by_cases hu : u / (M.k + 2) < T
    · simp only [hu, ↓reduceIte]
      refine Pr.det w w' u hu (fun v hv => ?_) (fun hk j hj => hrd j ?_)
      · have hvT : v / (M.k + 2) < T := (stepPreds_step_lt (Pr.P_subset u hv)).trans hu
        have := hout v hv
        simpa only [hvT, ↓reduceIte] using this
      · simp only [hk, hu, and_self, ↓reduceIte]
        exact hj
    · simp only [hu, ↓reduceIte]

theorem toFunDag_out (u : ℕ) : Pr.toFunDag.out u = Pr.P u := rfl

theorem toFunDag_val_of_lt (w : Fin L → Bool) {u : ℕ} (hu : u / (M.k + 2) < T) :
    Pr.toFunDag.val w u = fieldVal M (List.ofFn w) u := by
  simp only [toFunDag, hu, ↓reduceIte]

theorem toFunDag_val_of_le (w : Fin L → Bool) {u : ℕ} (hu : T ≤ u / (M.k + 2)) :
    Pr.toFunDag.val w u = 0 := by
  simp only [toFunDag, not_lt.mpr hu, ↓reduceIte]

/-- **Edges are dependency steps** of the work walks `τ₀.work`. -/
theorem toFunDag_edge (u : ℕ) :
    ∀ v ∈ Pr.toFunDag.out u, DepStep τ₀.work T (u / (M.k + 2)) (v / (M.k + 2)) :=
  fun _ hv => depStep_of_mem_stepPreds (Pr.P_subset u hv)

/-- **Input marks read the position under the input head** at their step. -/
theorem toFunDag_rd (u : ℕ) (j : Fin L) (h : Pr.toFunDag.rd u = some j) :
    readPos τ₀ L (u / (M.k + 2)) = some j := by
  simp only [toFunDag] at h
  split_ifs at h
  exact h

theorem toFunDag_rd_full (hobl : FollowsTrace M L τ₀ T) (u : ℕ) :
    (full hobl).toFunDag.rd u = if u / (M.k + 2) < T then readPos τ₀ L (u / (M.k + 2)) else none :=
  by simp [toFunDag]

/-- **Whole steps take at most `2^β` values** for `β ≥ β(M)`: the field values of a step are
functions of its step value. -/
theorem toFunDag_step_card {β : ℕ} (hβ : valueWidth M ≤ β) (t : ℕ) :
    (univ.image fun w => fun v : fieldNodesAt M.k t => Pr.toFunDag.val w v).card ≤ 2 ^ β := by
  classical
  let g : Value M → fieldNodesAt M.k t → ℕ := fun x v =>
    if t < T then fieldOf M ((v : ℕ) % (M.k + 2)) x else 0
  calc (univ.image fun w => fun v : fieldNodesAt M.k t => Pr.toFunDag.val w v).card
      ≤ ((univ : Finset (Value M)).image g).card := by
        refine card_le_card fun e he => ?_
        obtain ⟨w, -, rfl⟩ := mem_image.mp he
        refine mem_image.mpr ⟨stepValue M (List.ofFn w) t, mem_univ _, funext fun v => ?_⟩
        have hv : (v : ℕ) / (M.k + 2) = t := mem_fieldNodesAt.mp v.2
        simp only [g, toFunDag, fieldVal, hv]
    _ ≤ Fintype.card (Value M) := card_image_le.trans (by rw [card_univ])
    _ ≤ 2 ^ valueWidth M := card_value_le M
    _ ≤ 2 ^ β := Nat.pow_le_pow_right (by norm_num) hβ

/-- **Fields take at most `2^β` values** for `β ≥ β(M)`. -/
theorem toFunDag_field_card {β : ℕ} (hβ : valueWidth M ≤ β) (u : ℕ) :
    (univ.image fun w => Pr.toFunDag.val w u).card ≤ 2 ^ β := by
  classical
  let g : Value M → ℕ := fun x =>
    if u / (M.k + 2) < T then fieldOf M (u % (M.k + 2)) x else 0
  calc (univ.image fun w => Pr.toFunDag.val w u).card
      ≤ ((univ : Finset (Value M)).image g).card := by
        refine card_le_card fun e he => ?_
        obtain ⟨w, -, rfl⟩ := mem_image.mp he
        exact mem_image.mpr ⟨stepValue M (List.ofFn w) (u / (M.k + 2)), mem_univ _, rfl⟩
    _ ≤ Fintype.card (Value M) := card_image_le.trans (by rw [card_univ])
    _ ≤ 2 ^ valueWidth M := card_value_le M
    _ ≤ 2 ^ β := Nat.pow_le_pow_right (by norm_num) hβ

/-- **A deep edge of the field DAG** leads from a field of step `t` to a symbol field `κ_{t',j}` of
a step `t' ≤ t - 2`. -/
theorem toFunDag_deep_edge {V : ℕ} {u v : ℕ} (hv : v ∈ Pr.toFunDag.out u)
    (hdeep : DeepStep τ₀.work T V (u / (M.k + 2)) (v / (M.k + 2))) :
    v / (M.k + 2) + 2 ≤ u / (M.k + 2) ∧ ∃ j : Fin M.k, v = symbolNode M.k (v / (M.k + 2)) j := by
  obtain ⟨η, hη, he, -⟩ := hdeep
  have hhop := mem_allHops.mp hη
  rw [he] at hhop
  have h2 : v / (M.k + 2) + 2 ≤ u / (M.k + 2) := hhop.1
  refine ⟨h2, ?_⟩
  rcases (mem_stepPreds.mp (Pr.P_subset u hv)).2 with ⟨s, hs, rfl⟩ | ⟨j, σ, -, rfl⟩
  · rw [stateNode_div] at h2
    omega
  · exact ⟨j, by rw [symbolNode_div]⟩

end Pruning

/-! ### Output nodes of a transposer -/

/-- The transposed position, as an element of `Fin (d² b)`. -/
def tposOf (d b : ℕ) (u : Fin (d * d * b)) : Fin (d * d * b) :=
  ⟨Transpose.Tape.tpos d b u, Transpose.Tape.Impl.tpos_lt u.2⟩

theorem tposOf_tposOf (d b : ℕ) (u : Fin (d * d * b)) : tposOf d b (tposOf d b u) = u :=
  Fin.ext (Transpose.Tape.Impl.tpos_tpos u.2)

/-- The output node of output position `ℓ`: the output field of the step `appendTime τ₀ T ℓ` that
appends bit `ℓ`. -/
def outputNodeOf {k : ℕ} (τ₀ : Trace k) (T ℓ : ℕ) : ℕ := outputNode k (appendTime τ₀ T ℓ)

theorem outputNodeOf_div {k : ℕ} (τ₀ : Trace k) (T ℓ : ℕ) :
    outputNodeOf τ₀ T ℓ / (k + 2) = appendTime τ₀ T ℓ :=
  outputNode_div k _

/-- `M` is an **oblivious transposer** at size `(d, b)` along the trace `τ₀` before `T`: every input
of length `L = d² b` follows `τ₀` before `T`, `τ₀` appends at least `L` bits before `T`, and `M`
transposes every input (at any halting time). -/
structure ObliviousTransposer (M : TM) (d b : ℕ) (τ₀ : Trace M.k) (T : ℕ) : Prop where
  follows : FollowsTrace M (d * d * b) τ₀ T
  appends : d * d * b ≤ (appendList τ₀ T).length
  transposes : ∀ X : Fin (d * d * b) → Bool, OutputsTranspose M d b X

namespace Pruning

variable {M} {d b : ℕ} {τ₀ : Trace M.k} {T : ℕ}

/-- The output step of position `ℓ` lies before `T`. -/
theorem appendTime_lt_of_transposer (hM : ObliviousTransposer M d b τ₀ T) (ℓ : Fin (d * d * b)) :
    appendTime τ₀ T ℓ < T := by
  have hlen := (prefix_output hM.appends (hM.follows (fun _ => false))
    (hM.transposes (fun _ => false))).1
  exact appendTime_lt τ₀ T (by rw [hlen]; exact ℓ.2)

/-- **The output decoding.** For an oblivious transposer, the output node of position `ℓ` (the
output field of the step appending bit `ℓ`) carries the input bit at `tpos ℓ`. -/
theorem toFunDag_dec (Pr : Pruning M (d * d * b) τ₀ T) (hM : ObliviousTransposer M d b τ₀ T)
    (w : Fin (d * d * b) → Bool) (ℓ : Fin (d * d * b)) :
    decOut (Pr.toFunDag.val w (outputNodeOf τ₀ T ℓ)) = w (tposOf d b ℓ) := by
  have hlt := appendTime_lt_of_transposer hM ℓ
  have hout := (prefix_output hM.appends (hM.follows w) (hM.transposes w)).2 (tposOf d b ℓ)
  have e : Transpose.Tape.tpos d b ((tposOf d b ℓ : Fin (d * d * b)) : ℕ) = ℓ :=
    Transpose.Tape.Impl.tpos_tpos ℓ.2
  rw [e] at hout
  rw [toFunDag_val_of_lt Pr w (by rw [outputNodeOf_div]; exact hlt), outputNodeOf,
    fieldVal_outputNode, hout, decOut_encOut]

end Pruning

/-! ### Oblivious machines in the frozen model -/

theorem dir_eq_of_shift_eq {d d' : Dir} {p : ℤ} (h : d.shift p = d'.shift p) : d = d' := by
  rw [shift_eq_add_moveInt, shift_eq_add_moveInt] at h
  cases d <;> cases d' <;> simp_all [moveInt]

/-- **A machine oblivious at length `L`** in the frozen model (`ObliviousOn M (inputsOfLength L) T`)
follows the trace of any input of length `L` before `T`. -/
theorem followsTrace_of_obliviousOn {M : TM} {L T : ℕ} (h : ObliviousOn M (inputsOfLength L) T)
    (w₀ : Fin L → Bool) : FollowsTrace M L (trace M (List.ofFn w₀)) T := by
  intro w s hs
  have hw : List.ofFn w ∈ inputsOfLength L := List.length_ofFn
  have hw₀ : List.ofFn w₀ ∈ inputsOfLength L := List.length_ofFn
  obtain ⟨hin, hwp, happ⟩ := h.2 _ hw _ hw₀ s
  obtain ⟨hin', hwp', -⟩ := h.2 _ hw _ hw₀ (s + 1)
  rcases hx : transAt M (List.ofFn w) s with _ | ⟨q, d, acts, o⟩
  · exact absurd hx ((h.1 _ hw).1 s hs)
  rcases hx₀ : transAt M (List.ofFn w₀) s with _ | ⟨q₀, d₀, acts₀, o₀⟩
  · exact absurd hx₀ ((h.1 _ hw₀).1 s hs)
  have hd : d = d₀ := by
    rw [run_succ_inPos, run_succ_inPos, hx, hx₀] at hin'
    simp only at hin'
    rw [hin] at hin'
    exact dir_eq_of_shift_eq hin'
  have hacts : ∀ i, (acts i).2 = (acts₀ i).2 := by
    intro i
    have e := congrFun hwp' i
    rw [run_succ_workPos, run_succ_workPos, hx, hx₀] at e
    simp only at e
    rw [congrFun hwp i] at e
    exact dir_eq_of_shift_eq e
  have ho : o.isSome = o₀.isSome := by
    simpa [outBit, hx, hx₀] using happ
  simp only [trace, hx, hx₀, Option.map_some, hd, ho]
  congr
  funext i
  exact hacts i

/-- The number of appends before the halting time of a transposed input is `L`. -/
theorem appendList_length_of_haltsAt {M : TM} {d b : ℕ} {τ₀ : Trace M.k} {T : ℕ}
    {X : Fin (d * d * b) → Bool} (hag : ∀ t < T, trace M (List.ofFn X) t = τ₀ t)
    (hhalt : HaltsAt M (List.ofFn X) T) (htr : OutputsTranspose M d b X) :
    (appendList τ₀ T).length = d * d * b := by
  obtain ⟨s, hs, hlen, -⟩ := htr.output
  obtain rfl := haltsAt_unique hs hhalt
  have hfilt : (List.range s).filter (fun t => (outBit M (List.ofFn X) t).isSome) =
      appendList τ₀ s := by
    unfold appendList
    exact List.filter_congr fun t ht => outBit_isSome_eq_of_agree hag (List.mem_range.mp ht)
  rw [← hlen, outRev_reverse_eq, List.length_filterMap_eq_countP, List.countP_eq_length_filter,
    hfilt]

/-- **An oblivious transposer in the frozen model.** If `M` is oblivious at length `L = d² b` with
halting time `T` and transposes `d × d` matrices with `b`-bit entries, it is an oblivious
transposer along the trace of any input, before `T`, and `T ≤ ⌊c (L + 1)⌋`. -/
theorem ObliviousTransposer.of_obliviousOn {M : TM} {d b : ℕ} {c : ℝ} {T : ℕ}
    (hobl : ObliviousOn M (inputsOfLength (d * d * b)) T) (htr : TransposesAtWidth M d b c)
    (w₀ : Fin (d * d * b) → Bool) :
    ObliviousTransposer M d b (trace M (List.ofFn w₀)) T ∧
      T ≤ ⌊c * (((d * d * b : ℕ) : ℝ) + 1)⌋₊ := by
  have hf := followsTrace_of_obliviousOn hobl w₀
  have hhalt : HaltsAt M (List.ofFn w₀) T := hobl.1 _ List.length_ofFn
  refine ⟨⟨hf, ?_, fun X => (htr.transposesInput X).outputsTranspose⟩, ?_⟩
  · rw [appendList_length_of_haltsAt (hf w₀) hhalt (htr.transposesInput w₀).outputsTranspose]
  · obtain ⟨s, hs, hs'⟩ := (htr.transposesInput w₀).halts
    rw [haltsAt_unique hhalt hs']
    exact hs

end MergeDepth
