import Transpose.Tape.Run
import Transpose.Tape.Encode

/-!
# Output buffering: a machine that outputs only in its last `L` steps

`bufTM M` runs `M` with one extra work tape, the **buffer**. Every bit that `M` would append to
the output is written on the buffer instead, at cells `0, 1, 2, …`. When `M` halts, the buffer
head walks back to cell `0` (`rewind`) and then copies the buffer to the output, one bit per step
(`copy`), halting at the first blank cell.

If `M` halts at time `T` on `w` with output `out` of length `L`, then `bufTM M` halts at time
`T + 2 L + 2` with the same output, and it appends output bits exactly in its last `L` steps (both
in `bufTM_run`). So the output schedule of `bufTM M` is fixed by its halting
time, which is what makes its block-level traces cheap to count (`CoarseTrace.lean`).
-/

namespace Transpose.Tape.Impl

open Transpose

/-! ### The machine -/

section Machine

variable (M : TM)

/-- `M`'s work symbol in the buffered machine's alphabet `Fin (g + 3)`. -/
def bsym (a : Fin (M.g + 1)) : Fin (M.g + 2 + 1) := ⟨a.val, by omega⟩

/-- Back to `M`'s alphabet (`0` outside its range). -/
def unb (a : Fin (M.g + 2 + 1)) : Fin (M.g + 1) := if h : a.val < M.g + 1 then ⟨a.val, h⟩ else 0

/-- The buffer symbol of a bit: `1` for `false`, `2` for `true` (`0` is blank). -/
def bitSym (b : Bool) : Fin (M.g + 2 + 1) := if b then ⟨2, by omega⟩ else ⟨1, by omega⟩

/-- `M`'s state in the buffered machine. -/
def bst (s : Fin (M.q + 1)) : Fin (M.q + 2 + 1) := ⟨s.val, by omega⟩

/-- The rewind state. -/
def rewindSt : Fin (M.q + 2 + 1) := ⟨M.q + 1, by omega⟩

/-- The copy state. -/
def copySt : Fin (M.q + 2 + 1) := ⟨M.q + 2, by omega⟩

end Machine

/-- `buf` on the buffer tape (the last one), `f j` on `M`'s tape `j`. -/
def tapeSel {k : ℕ} {α : Sort*} (buf : α) (f : Fin k → α) (i : Fin (k + 1)) : α :=
  Fin.lastCases (motive := fun _ => α) buf f i

@[simp] theorem tapeSel_last {k : ℕ} {α : Sort*} (buf : α) (f : Fin k → α) :
    tapeSel buf f (Fin.last k) = buf := Fin.lastCases_last

@[simp] theorem tapeSel_castSucc {k : ℕ} {α : Sort*} (buf : α) (f : Fin k → α) (j : Fin k) :
    tapeSel buf f (Fin.castSucc j) = f j := Fin.lastCases_castSucc j

/-- Keep every tape of `M` in place (rewrite its symbol, stay); act `a` on the buffer. -/
def keepActs {k G : ℕ} (syms : Fin (k + 1) → Fin G) (bufMove : Dir) : Fin (k + 1) → Fin G × Dir :=
  tapeSel (syms (Fin.last k), bufMove) (fun j => (syms (Fin.castSucc j), Dir.stay))

/-- The transition function of `bufTM M`. -/
def bufδ (M : TM) (s : Fin (M.q + 2 + 1)) (inp : Option Bool)
    (syms : Fin (M.k + 1) → Fin (M.g + 2 + 1)) :
    Option (Fin (M.q + 2 + 1) × Dir × (Fin (M.k + 1) → Fin (M.g + 2 + 1) × Dir) × Option Bool) :=
  if hs : s.val < M.q + 1 then
    match M.δ ⟨s.val, hs⟩ inp (fun j => unb M (syms (Fin.castSucc j))) with
    | some (s₁, d, acts, o) =>
      some (bst M s₁, d,
        tapeSel (match o with
            | some b => (bitSym M b, Dir.right)
            | none => (syms (Fin.last M.k), Dir.stay))
          (fun j => (bsym M (acts j).1, (acts j).2)), none)
    | none => some (rewindSt M, Dir.stay, keepActs syms Dir.left, none)
  else if s.val = M.q + 1 then
    if syms (Fin.last M.k) = 0 then some (copySt M, Dir.stay, keepActs syms Dir.right, none)
    else some (rewindSt M, Dir.stay, keepActs syms Dir.left, none)
  else
    if syms (Fin.last M.k) = 0 then none
    else some (copySt M, Dir.stay, keepActs syms Dir.right,
      some (decide ((syms (Fin.last M.k)).val = 2)))

/-- **The buffered machine**: `M` plus a buffer tape; it outputs only after `M` halts. (Reducible,
so that `(bufTM M).g` is `M.g + 2` for `simp`.) -/
abbrev bufTM (M : TM) : TM where
  k := M.k + 1
  g := M.g + 2
  q := M.q + 2
  δ := bufδ M

/-! ### Configurations -/

section Configs

variable (M : TM)

/-- The buffer holding the bits of `out` (oldest first) at cells `0, 1, …` (blank elsewhere). -/
def bufCell (out : List Bool) (p : ℤ) : Fin (M.g + 2 + 1) :=
  match readInput out p with
  | some b => bitSym M b
  | none => 0

/-- The buffered machine's configuration while it simulates `M` at configuration `c`: the output
so far is on the buffer, the buffer head is just after it, the real output is empty. -/
def liftCfg (c : Config M) : Config (bufTM M) where
  state := bst M c.state
  inPos := c.inPos
  work := fun i p => tapeSel (bufCell M c.outRev.reverse p) (fun j => bsym M (c.work j p)) i
  workPos := tapeSel (c.outRev.length : ℤ) (fun j => c.workPos j)
  outRev := []

/-- Rewinding the buffer, with the buffer head at `pos`. -/
def rewCfg (c : Config M) (pos : ℤ) : Config (bufTM M) where
  state := rewindSt M
  inPos := c.inPos
  work := (liftCfg M c).work
  workPos := tapeSel pos (fun j => c.workPos j)
  outRev := []

/-- Copying the buffer, with the buffer head at `pos` and output `acc` (most recent first). -/
def copyCfg (c : Config M) (pos : ℤ) (acc : List Bool) : Config (bufTM M) where
  state := copySt M
  inPos := c.inPos
  work := (liftCfg M c).work
  workPos := tapeSel pos (fun j => c.workPos j)
  outRev := acc

end Configs

/-! ### Basic facts -/

theorem unb_bsym (M : TM) (a : Fin (M.g + 1)) : unb M (bsym M a) = a := by
  unfold unb bsym
  rw [dite_eq_left a.2]

theorem bitSym_ne_zero (M : TM) (b : Bool) : bitSym M b ≠ 0 := by
  unfold bitSym
  cases b <;> simp [Fin.ext_iff]

theorem bitSym_val_eq_two (M : TM) (b : Bool) : decide ((bitSym M b).val = 2) = b := by
  unfold bitSym
  cases b <;> simp

theorem nth_append_single (l : List Bool) (b : Bool) (i : ℕ) :
    nth (l ++ [b]) i = if i = l.length then some b else nth l i := by
  rw [nth_eq_getElem?, nth_eq_getElem?, List.getElem?_append]
  split_ifs with h1 h2 h2 <;> simp_all; omega

theorem readInput_append_single (l : List Bool) (b : Bool) (p : ℤ) :
    readInput (l ++ [b]) p = if p = (l.length : ℤ) then some b else readInput l p := by
  unfold readInput
  by_cases hp : p < 0
  · rw [ite_eq_left hp, ite_eq_left hp, ite_eq_right (by omega)]
  · rw [ite_eq_right hp, ite_eq_right hp, nth_append_single]
    by_cases h : p.toNat = l.length
    · rw [ite_eq_left h, ite_eq_left (by omega)]
    · rw [ite_eq_right h, ite_eq_right (by omega)]

theorem bufCell_length (out : List Bool) (M : TM) : bufCell M out (out.length : ℤ) = 0 := by
  unfold bufCell; rw [readInput_eq_none (Or.inr le_rfl)]

theorem bufCell_neg (out : List Bool) (M : TM) {p : ℤ} (hp : p < 0) : bufCell M out p = 0 := by
  unfold bufCell; rw [readInput_eq_none (Or.inl hp)]

theorem keepActs_fst {k G : ℕ} (syms : Fin (k + 1) → Fin G) (mv : Dir) (i : Fin (k + 1)) :
    (keepActs syms mv i).1 = syms i := by
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [keepActs]

@[simp] theorem keepActs_castSucc {k G : ℕ} (syms : Fin (k + 1) → Fin G) (mv : Dir) (j : Fin k) :
    keepActs syms mv (Fin.castSucc j) = (syms (Fin.castSucc j), Dir.stay) := by
  simp [keepActs]

@[simp] theorem keepActs_last {k G : ℕ} (syms : Fin (k + 1) → Fin G) (mv : Dir) :
    keepActs syms mv (Fin.last k) = (syms (Fin.last k), mv) := by
  simp [keepActs]

/-- Rewriting every head's own symbol leaves the tapes unchanged. -/
theorem work_keep {k G : ℕ} (wk : Fin (k + 1) → ℤ → Fin G) (wp : Fin (k + 1) → ℤ) (mv : Dir) :
    (fun i p => if p = wp i then (keepActs (fun i => wk i (wp i)) mv i).1 else wk i p) = wk := by
  funext i p
  rw [keepActs_fst]
  split_ifs with h
  · rw [h]
  · rfl

/-! ### One step of each phase -/

section Steps

variable {M : TM} {w : List Bool}

theorem bufδ_bst (s : Fin (M.q + 1)) (inp : Option Bool)
    (syms : Fin (M.k + 1) → Fin (M.g + 2 + 1)) :
    bufδ M (bst M s) inp syms =
      match M.δ s inp (fun j => unb M (syms (Fin.castSucc j))) with
      | some (s₁, d, acts, o) =>
        some (bst M s₁, d,
          tapeSel (match o with
              | some b => (bitSym M b, Dir.right)
              | none => (syms (Fin.last M.k), Dir.stay))
            (fun j => (bsym M (acts j).1, (acts j).2)), none)
      | none => some (rewindSt M, Dir.stay, keepActs syms Dir.left, none) := by
  unfold bufδ
  rw [dite_eq_left (show (bst M s).val < M.q + 1 from s.2)]
  rfl

theorem bufδ_rewind (inp : Option Bool) (syms : Fin (M.k + 1) → Fin (M.g + 2 + 1)) :
    bufδ M (rewindSt M) inp syms =
      if syms (Fin.last M.k) = 0 then some (copySt M, Dir.stay, keepActs syms Dir.right, none)
      else some (rewindSt M, Dir.stay, keepActs syms Dir.left, none) := by
  unfold bufδ
  rw [dite_eq_right (show ¬ (rewindSt M).val < M.q + 1 by simp [rewindSt]),
    ite_eq_left (show (rewindSt M).val = M.q + 1 from rfl)]

theorem bufδ_copy (inp : Option Bool) (syms : Fin (M.k + 1) → Fin (M.g + 2 + 1)) :
    bufδ M (copySt M) inp syms =
      if syms (Fin.last M.k) = 0 then none
      else some (copySt M, Dir.stay, keepActs syms Dir.right,
        some (decide ((syms (Fin.last M.k)).val = 2))) := by
  unfold bufδ
  rw [dite_eq_right (show ¬ (copySt M).val < M.q + 1 by simp [copySt]),
    ite_eq_right (show ¬ (copySt M).val = M.q + 1 by simp [copySt])]

/-- The transition of `bufTM M` on a lifted configuration. -/
theorem bufδ_liftCfg (c : Config M) :
    (bufTM M).δ (liftCfg M c).state (readInput w (liftCfg M c).inPos)
        (fun i => (liftCfg M c).work i ((liftCfg M c).workPos i)) =
      match M.δ c.state (readInput w c.inPos) (fun i => c.work i (c.workPos i)) with
      | some (s₁, d, acts, o) =>
        some (bst M s₁, d, tapeSel (match o with
            | some b => (bitSym M b, Dir.right)
            | none => ((0 : Fin (M.g + 2 + 1)), Dir.stay))
          (fun j => (bsym M (acts j).1, (acts j).2)), none)
      | none => some (rewindSt M, Dir.stay,
          keepActs (fun i => (liftCfg M c).work i ((liftCfg M c).workPos i)) Dir.left, none) := by
  have hsyms : (fun j => unb M ((liftCfg M c).work (Fin.castSucc j)
      ((liftCfg M c).workPos (Fin.castSucc j)))) = fun i => c.work i (c.workPos i) := by
    funext j
    simp only [liftCfg, tapeSel_castSucc, unb_bsym]
  have hbuf : (liftCfg M c).work (Fin.last M.k) ((liftCfg M c).workPos (Fin.last M.k)) = 0 := by
    simp only [liftCfg, tapeSel_last]
    rw [← List.length_reverse]
    exact bufCell_length _ M
  have := bufδ_bst (M := M) c.state (readInput w c.inPos)
    (fun i => (liftCfg M c).work i ((liftCfg M c).workPos i))
  simp only [hsyms, hbuf] at this
  exact this

/-- **Simulation.** A step of `M` is a step of `bufTM M` on the lifted configurations. -/
theorem step_liftCfg {c c' : Config M} (h : step M w c = some c') :
    step (bufTM M) w (liftCfg M c) = some (liftCfg M c') := by
  unfold step at h ⊢
  rw [bufδ_liftCfg]
  rcases hδ : M.δ c.state (readInput w c.inPos) (fun i => c.work i (c.workPos i)) with _ |
    ⟨s₁, d, acts, o⟩
  · rw [hδ] at h; exact absurd h (by simp)
  · rw [hδ] at h
    simp only [Option.some.injEq] at h
    subst h
    simp only [Option.some.injEq, liftCfg]
    congr 1
    · funext i p
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [tapeSel_last]
        cases o with
        | none =>
          simp only
          split_ifs with hp
          · rw [hp, ← List.length_reverse, bufCell_length]
          · rfl
        | some b =>
          simp only [List.reverse_cons]
          unfold bufCell
          rw [readInput_append_single]
          split_ifs with hp hp' hp'
          · rfl
          · exact absurd (by rw [hp, List.length_reverse]) hp'
          · exact absurd (by rw [hp', List.length_reverse]) hp
          · rfl
      · simp only [tapeSel_castSucc]
        split_ifs <;> rfl
    · funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [tapeSel_last]
        cases o with
        | none => rfl
        | some b => simp [Dir.shift]
      · simp only [tapeSel_castSucc]

/-- **`M` halts**: `bufTM M` starts rewinding, from the last buffered bit. -/
theorem step_liftCfg_halt {c : Config M} (h : step M w c = none) :
    step (bufTM M) w (liftCfg M c) = some (rewCfg M c ((c.outRev.length : ℤ) - 1)) := by
  unfold step at h ⊢
  rw [bufδ_liftCfg]
  rcases hδ : M.δ c.state (readInput w c.inPos) (fun i => c.work i (c.workPos i)) with _ |
    ⟨s₁, d, acts, o⟩
  · simp only [Option.some.injEq, rewCfg]
    congr 1
    · exact work_keep _ _ _
    · funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [liftCfg, Dir.shift]
      · simp [liftCfg, Dir.shift]
  · rw [hδ] at h; exact absurd h (by simp)

theorem rewCfg_buf (c : Config M) (pos : ℤ) :
    (rewCfg M c pos).work (Fin.last M.k) ((rewCfg M c pos).workPos (Fin.last M.k)) =
      bufCell M c.outRev.reverse pos := by
  simp [rewCfg, liftCfg]

theorem copyCfg_buf (c : Config M) (pos : ℤ) (acc : List Bool) :
    (copyCfg M c pos acc).work (Fin.last M.k) ((copyCfg M c pos acc).workPos (Fin.last M.k)) =
      bufCell M c.outRev.reverse pos := by
  simp [copyCfg, liftCfg]

theorem bufCell_of_some {out : List Bool} {p : ℤ} {b : Bool} (h : readInput out p = some b) :
    bufCell M out p = bitSym M b := by
  unfold bufCell; rw [h]

/-- **A rewind step** over a buffered bit. -/
theorem step_rewCfg {c : Config M} {pos : ℤ} {b : Bool}
    (hb : readInput c.outRev.reverse pos = some b) :
    step (bufTM M) w (rewCfg M c pos) = some (rewCfg M c (pos - 1)) := by
  unfold step
  have hδ : (bufTM M).δ (rewCfg M c pos).state (readInput w (rewCfg M c pos).inPos)
      (fun i => (rewCfg M c pos).work i ((rewCfg M c pos).workPos i)) =
      some (rewindSt M, Dir.stay,
        keepActs (fun i => (rewCfg M c pos).work i ((rewCfg M c pos).workPos i)) Dir.left,
        none) := by
    have h1 := bufδ_rewind (M := M) (readInput w (rewCfg M c pos).inPos)
      (fun i => (rewCfg M c pos).work i ((rewCfg M c pos).workPos i))
    beta_reduce at h1
    rw [ite_eq_right (by rw [rewCfg_buf, bufCell_of_some hb]; exact bitSym_ne_zero M b)] at h1
    exact h1
  rw [hδ]
  simp only [Option.some.injEq, rewCfg]
  congr 1
  · exact work_keep _ _ _
  · funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [Dir.shift]
    · simp [Dir.shift]

/-- **The rewind ends** at the blank cell `-1`: copying starts at cell `0`. -/
theorem step_rewCfg_end (c : Config M) :
    step (bufTM M) w (rewCfg M c (-1)) = some (copyCfg M c 0 []) := by
  unfold step
  have hδ : (bufTM M).δ (rewCfg M c (-1)).state (readInput w (rewCfg M c (-1)).inPos)
      (fun i => (rewCfg M c (-1)).work i ((rewCfg M c (-1)).workPos i)) =
      some (copySt M, Dir.stay,
        keepActs (fun i => (rewCfg M c (-1)).work i ((rewCfg M c (-1)).workPos i)) Dir.right,
        none) := by
    have h1 := bufδ_rewind (M := M) (readInput w (rewCfg M c (-1)).inPos)
      (fun i => (rewCfg M c (-1)).work i ((rewCfg M c (-1)).workPos i))
    beta_reduce at h1
    rw [ite_eq_left (by rw [rewCfg_buf]; exact bufCell_neg _ M (by norm_num))] at h1
    exact h1
  rw [hδ]
  simp only [Option.some.injEq, rewCfg, copyCfg]
  congr 1
  · exact work_keep _ _ _
  · funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [Dir.shift]
    · simp [Dir.shift]

/-- **A copy step**: output the buffered bit and move on. -/
theorem step_copyCfg {c : Config M} {pos : ℤ} {b : Bool} (acc : List Bool)
    (hb : readInput c.outRev.reverse pos = some b) :
    step (bufTM M) w (copyCfg M c pos acc) = some (copyCfg M c (pos + 1) (b :: acc)) := by
  unfold step
  have hδ : (bufTM M).δ (copyCfg M c pos acc).state (readInput w (copyCfg M c pos acc).inPos)
      (fun i => (copyCfg M c pos acc).work i ((copyCfg M c pos acc).workPos i)) =
      some (copySt M, Dir.stay,
        keepActs (fun i => (copyCfg M c pos acc).work i ((copyCfg M c pos acc).workPos i))
          Dir.right, some b) := by
    have h1 := bufδ_copy (M := M) (readInput w (copyCfg M c pos acc).inPos)
      (fun i => (copyCfg M c pos acc).work i ((copyCfg M c pos acc).workPos i))
    beta_reduce at h1
    rw [ite_eq_right (by rw [copyCfg_buf, bufCell_of_some hb]; exact bitSym_ne_zero M b),
      copyCfg_buf, bufCell_of_some hb, bitSym_val_eq_two] at h1
    exact h1
  rw [hδ]
  simp only [Option.some.injEq, copyCfg]
  congr 1
  · exact work_keep _ _ _
  · funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [Dir.shift]
    · simp [Dir.shift]

/-- **The copy ends** at the first blank cell: `bufTM M` halts. -/
theorem step_copyCfg_end (c : Config M) (acc : List Bool) :
    step (bufTM M) w (copyCfg M c (c.outRev.length : ℤ) acc) = none := by
  unfold step
  have hδ : (bufTM M).δ (copyCfg M c (c.outRev.length : ℤ) acc).state
      (readInput w (copyCfg M c (c.outRev.length : ℤ) acc).inPos)
      (fun i => (copyCfg M c (c.outRev.length : ℤ) acc).work i
        ((copyCfg M c (c.outRev.length : ℤ) acc).workPos i)) = none := by
    have h1 := bufδ_copy (M := M) (readInput w (copyCfg M c (c.outRev.length : ℤ) acc).inPos)
      (fun i => (copyCfg M c (c.outRev.length : ℤ) acc).work i
        ((copyCfg M c (c.outRev.length : ℤ) acc).workPos i))
    beta_reduce at h1
    rw [ite_eq_left (by rw [copyCfg_buf, ← List.length_reverse]; exact bufCell_length _ M)] at h1
    exact h1
  rw [hδ]

end Steps

/-! ### The run -/

theorem readInput_eq_getElem {l : List Bool} {i : ℕ} (h : i < l.length) :
    readInput l (i : ℤ) = some l[i] := by
  rw [readInput_natCast, nth_eq_getElem?, List.getElem?_eq_getElem h]

theorem readInput_some_of_lt {l : List Bool} {p : ℤ} (h0 : 0 ≤ p) (h1 : p < l.length) :
    ∃ b, readInput l p = some b := by
  obtain ⟨i, rfl⟩ := Int.eq_ofNat_of_zero_le h0
  exact ⟨_, readInput_eq_getElem (by omega)⟩

section RunLemmas

variable {M : TM} {w : List Bool}

theorem run_succ_of_step {τ : ℕ} {c : Config M} (h : step M w (run M w τ) = some c) :
    run M w (τ + 1) = c := by
  rw [run_succ, next, h]; rfl

theorem step_run_eq_some {τ : ℕ} (h : transAt M w τ ≠ none) :
    step M w (run M w τ) = some (run M w (τ + 1)) := by
  rcases hs : step M w (run M w τ) with _ | c
  · exact absurd ((step_run_eq_none_iff τ).1 hs) h
  · rw [run_succ_of_step hs]

theorem transAt_ne_none_of_step {τ : ℕ} {c : Config M} (h : step M w (run M w τ) = some c) :
    transAt M w τ ≠ none := by
  intro h'
  rw [(step_run_eq_none_iff τ).2 h'] at h
  exact absurd h (by simp)

theorem init_bufTM : init (bufTM M) = liftCfg M (init M) := by
  unfold init liftCfg
  simp only [Config.mk.injEq]
  refine ⟨Fin.ext rfl, trivial, ?_, ?_, trivial⟩
  · funext i p
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [tapeSel_last, List.reverse_nil]
      unfold bufCell readInput
      split_ifs <;> rfl
    · simp only [tapeSel_castSucc]; rfl
  · funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

/-- **Phase 1**: while `M` runs, `bufTM M` is in the lifted configuration. -/
theorem bufTM_run_sim {T : ℕ} (hT : HaltsAt M w T) :
    ∀ τ ≤ T, run (bufTM M) w τ = liftCfg M (run M w τ) := by
  intro τ
  induction τ with
  | zero => intro _; exact init_bufTM
  | succ τ ih =>
    intro hτ
    have h1 := step_liftCfg (w := w) (step_run_eq_some (hT.1 τ (by omega)))
    rw [← ih (by omega)] at h1
    exact run_succ_of_step h1

/-- **Phase 2**: the rewind, `j` steps after `M` halted. -/
theorem bufTM_run_rew {T : ℕ} (hT : HaltsAt M w T) :
    ∀ j ≤ (run M w T).outRev.length, run (bufTM M) w (T + 1 + j) =
      rewCfg M (run M w T) (((run M w T).outRev.length : ℤ) - 1 - j) := by
  intro j
  induction j with
  | zero =>
    intro _
    have hnone : step M w (run M w T) = none := (step_run_eq_none_iff T).2 hT.2
    have h1 := step_liftCfg_halt (w := w) hnone
    rw [← bufTM_run_sim hT T le_rfl] at h1
    rw [run_succ_of_step h1]
    have e : ((run M w T).outRev.length : ℤ) - 1 - ((0 : ℕ) : ℤ) =
        ((run M w T).outRev.length : ℤ) - 1 := by push_cast; ring
    rw [e]
  | succ j ih =>
    intro hj
    have hrw := ih (by omega)
    obtain ⟨b, hb⟩ := readInput_some_of_lt (l := (run M w T).outRev.reverse)
      (p := ((run M w T).outRev.length : ℤ) - 1 - j) (by omega)
      (by rw [List.length_reverse]; omega)
    have h1 := step_rewCfg (w := w) hb
    rw [← hrw] at h1
    rw [show T + 1 + (j + 1) = T + 1 + j + 1 by ring, run_succ_of_step h1]
    have e : ((run M w T).outRev.length : ℤ) - 1 - (j : ℤ) - 1 =
        ((run M w T).outRev.length : ℤ) - 1 - ((j + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [e]

/-- **Phase 3**: the copy, `j` steps after it started. -/
theorem bufTM_run_copy {T : ℕ} (hT : HaltsAt M w T) :
    ∀ j ≤ (run M w T).outRev.length,
      run (bufTM M) w (T + (run M w T).outRev.length + 2 + j) =
        copyCfg M (run M w T) (j : ℤ) ((run M w T).outRev.reverse.take j).reverse := by
  intro j
  induction j with
  | zero =>
    intro _
    have hrw := bufTM_run_rew hT (run M w T).outRev.length le_rfl
    have hm1 : ((run M w T).outRev.length : ℤ) - 1 - ((run M w T).outRev.length : ℤ) = -1 := by
      ring
    rw [hm1] at hrw
    have h1 := step_rewCfg_end (w := w) (run M w T)
    rw [← hrw] at h1
    rw [show T + (run M w T).outRev.length + 2 + 0 = T + 1 + (run M w T).outRev.length + 1 by
      ring, run_succ_of_step h1]
    simp
  | succ j ih =>
    intro hj
    have hrw := ih (by omega)
    have hjl : j < (run M w T).outRev.reverse.length := by rw [List.length_reverse]; omega
    have hb := readInput_eq_getElem hjl
    have h1 := step_copyCfg (w := w) (((run M w T).outRev.reverse.take j).reverse) hb
    rw [← hrw] at h1
    rw [show T + (run M w T).outRev.length + 2 + (j + 1) =
      T + (run M w T).outRev.length + 2 + j + 1 by ring, run_succ_of_step h1]
    have e1 : (j : ℤ) + 1 = ((j + 1 : ℕ) : ℤ) := by push_cast; ring
    have e2 : (run M w T).outRev.reverse[j] :: ((run M w T).outRev.reverse.take j).reverse =
        ((run M w T).outRev.reverse.take (j + 1)).reverse := by
      rw [List.take_add_one, List.getElem?_eq_getElem hjl]
      simp
    rw [e1, e2]

/-- **The buffered machine.** If `M` halts at time `T` on `w` with an output of length `L`, then
`bufTM M` halts at time `T + 2 L + 2` with the same output, and at every time `t` up to then its
output has `L - (T + 2 L + 2 - t)` bits: it appends exactly in its last `L` steps. -/
theorem bufTM_run {T : ℕ} (hT : HaltsAt M w T) :
    HaltsAt (bufTM M) w (T + 2 * (run M w T).outRev.length + 2) ∧
    (run (bufTM M) w (T + 2 * (run M w T).outRev.length + 2)).outRev.reverse =
      (run M w T).outRev.reverse ∧
    ∀ t ≤ T + 2 * (run M w T).outRev.length + 2,
      (run (bufTM M) w t).outRev.length =
        (run M w T).outRev.length - (T + 2 * (run M w T).outRev.length + 2 - t) := by
  set L := (run M w T).outRev.length with hL
  have hlenrev : (run M w T).outRev.reverse.length = L := by rw [List.length_reverse]
  have hfin : run (bufTM M) w (T + 2 * L + 2) =
      copyCfg M (run M w T) (L : ℤ) (run M w T).outRev := by
    have := bufTM_run_copy hT L le_rfl
    rw [show T + L + 2 + L = T + 2 * L + 2 by ring] at this
    rw [this, ← hlenrev, List.take_length, List.reverse_reverse]
  refine ⟨⟨fun τ hτ => ?_, ?_⟩, ?_, fun t ht => ?_⟩
  · -- every step before `T + 2L + 2` is executed
    by_cases h1 : τ < T
    · have h := step_liftCfg (w := w) (step_run_eq_some (hT.1 τ h1))
      rw [← bufTM_run_sim hT τ h1.le] at h
      exact transAt_ne_none_of_step h
    by_cases h2 : τ = T
    · subst h2
      have h := step_liftCfg_halt (w := w) ((step_run_eq_none_iff τ).2 hT.2)
      rw [← bufTM_run_sim hT τ le_rfl] at h
      exact transAt_ne_none_of_step h
    by_cases h3 : τ ≤ T + L
    · obtain ⟨j, rfl⟩ : ∃ j, τ = T + 1 + j := ⟨τ - T - 1, by omega⟩
      obtain ⟨b, hb⟩ := readInput_some_of_lt (l := (run M w T).outRev.reverse)
        (p := (L : ℤ) - 1 - j) (by omega) (by rw [hlenrev]; omega)
      have h := step_rewCfg (w := w) hb
      rw [← bufTM_run_rew hT j (by omega)] at h
      exact transAt_ne_none_of_step h
    by_cases h4 : τ = T + L + 1
    · subst h4
      have hrw := bufTM_run_rew hT L le_rfl
      have hm1 : (L : ℤ) - 1 - (L : ℤ) = -1 := by ring
      rw [hm1] at hrw
      have h := step_rewCfg_end (w := w) (run M w T)
      rw [← hrw] at h
      exact transAt_ne_none_of_step (by rw [show T + L + 1 = T + 1 + L by ring]; exact h)
    · obtain ⟨j, rfl⟩ : ∃ j, τ = T + L + 2 + j := ⟨τ - (T + L + 2), by omega⟩
      have hjl : j < (run M w T).outRev.reverse.length := by rw [hlenrev]; omega
      have h := step_copyCfg (w := w) (((run M w T).outRev.reverse.take j).reverse)
        (readInput_eq_getElem hjl)
      rw [← bufTM_run_copy hT j (by omega)] at h
      exact transAt_ne_none_of_step h
  · -- the final step halts
    rw [← step_run_eq_none_iff, hfin]
    exact step_copyCfg_end (run M w T) _
  · rw [hfin]
    simp [copyCfg]
  · -- the output length
    by_cases h1 : t ≤ T
    · rw [bufTM_run_sim hT t h1]
      simp only [liftCfg, List.length_nil]
      omega
    by_cases h2 : t ≤ T + L + 1
    · obtain ⟨j, rfl⟩ : ∃ j, t = T + 1 + j := ⟨t - T - 1, by omega⟩
      rw [bufTM_run_rew hT j (by omega)]
      simp only [rewCfg, List.length_nil]
      omega
    · obtain ⟨j, rfl⟩ : ∃ j, t = T + L + 2 + j := ⟨t - (T + L + 2), by omega⟩
      rw [bufTM_run_copy hT j (by omega)]
      simp only [copyCfg, List.length_reverse, List.length_take, hlenrev]
      omega

end RunLemmas

end Transpose.Tape.Impl
