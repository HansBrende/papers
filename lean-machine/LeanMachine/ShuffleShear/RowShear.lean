import LeanMachine.ShuffleShear.Model

/-!
# Linear-Time `2`-Work-Tape Turing Machine for Within-Row Cyclic Shear

Constructs an explicit finite transition table `rowShearTM : DetTM` with `k = 2` work tapes over a
`10`-symbol work alphabet (`g = 9`) that computes the within-row cyclic shear
`(rowShearMatrix d A) r c t = A r ((c + r) % d) t` on the row-major encoding of any `d × d` matrix
(`d ≥ 1`) with `max(1, ⌈log₂ d⌉)`-bit (`entryBits d`) entries within `200 · L` steps
(`L = inputLength d`).
-/

namespace LeanMachine.ShuffleShear

private def divAdvanceAct : Action 2 WorkSym :=
  mkAct1 1 (fun _ _ => .right) (fun _ s₁ => (s₁, .right)) (fun _ _ => none)

/-- Divide `w.length = Q * b` by `b` (`unaryTape b` on Tape 1) to write `unaryTape Q` on Tape 0. -/
private def divInputByB : Block 2 WorkSym :=
  ((Block.loop (fun inp _ => inp.isSome)
    (writeDirAct 0 .u .right) actStay
    ((Block.while1 (fun _ sc => sc 1 == .u) divAdvanceAct actStay).seq
      (rewindFromEnd 1))).seq
    rewindInputFromPos).seq
    (rewindFromEnd 0)

private theorem Runs_divInputByB {w : List Bool} (m : Mem 2 WorkSym) (Q b : ℕ)
    (hb1 : 1 ≤ b) (hwLen : w.length = Q * b)
    (hIn : m.inPos = 0)
    (hB0 : m.work 0 = fun _ => .blank) (hP0 : m.workPos 0 = 0)
    (hT1 : m.work 1 = unaryTape b) (hP1 : m.workPos 1 = 0) :
    Runs divInputByB w m
      { m with work := fun i p => if i = 0 then unaryTape Q p else m.work i p }
      (3 * Q * b + 5 * Q + 5) := by
  unfold divInputByB
  let outerInv (q : ℕ) : Mem 2 WorkSym :=
    { m with
      inPos   := ((q * b : ℕ) : Int)
      work    := fun i p => if i = 0 then unaryTape q p else m.work i p
      workPos := fun i => if i = 0 then (q : Int) else m.workPos i }
  have hOuter0 : outerInv 0 = m := by
    refine Mem.eq_of_fields ?_ (fun i p => ?_) (fun i => ?_) rfl
    · dsimp only [outerInv]; simp [hIn]
    · dsimp only [outerInv]
      fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]
      rw [unaryTape_zero, hB0]
    · dsimp only [outerInv]
      fin_cases i <;> simp [hP0, hP1]
  have hLoop := Runs.loop (w := w)
    (fun inp (_ : Fin 2 → WorkSym) => inp.isSome)
    (writeDirAct 0 .u .right) actStay
    ((Block.while1 (fun _ sc => sc 1 == .u) divAdvanceAct actStay).seq (rewindFromEnd 1))
    (2 * b + 3) Q outerInv
    (fun q hq => by
      have hqbLt : q * b < w.length := by
        have : (q + 1) * b ≤ Q * b := Nat.mul_le_mul_right b (by omega)
        have : q * b < (q + 1) * b := by ring_nf; omega
        omega
      have hCond : (readInput w (outerInv q).inPos).isSome = true := by
        dsimp only [outerInv]
        rw [readInput_of_nonneg, List.getElem?_eq_getElem hqbLt]; rfl
      refine ⟨hCond, ?_⟩
      let innerInv (t : ℕ) : Mem 2 WorkSym :=
        { m with
          inPos   := ((q * b + t : ℕ) : Int)
          work    := fun i p => if i = 0 then unaryTape (q + 1) p else m.work i p
          workPos := fun i => if i = 0 then ((q + 1 : ℕ) : Int) else (t : Int) }
      have hEnt : applyAct w (writeDirAct 0 .u .right) (outerInv q) = innerInv 0 := by
        unfold writeDirAct; rw [applyAct_mkAct1]
        refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
        · dsimp only [outerInv, innerInv]
          fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]
          exact congrFun (unaryTape_write_end q) p
        · dsimp only [outerInv, innerInv, Dir.shift]
          fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]
          · omega
          · exact hP1
      rw [hEnt]
      have hW := Runs.while1 (w := w)
        (fun _ (sc : Fin 2 → WorkSym) => sc 1 == .u)
        divAdvanceAct actStay b innerInv
        (fun t ht => by
          have hcell1 : ((innerInv t).work 1 ((innerInv t).workPos 1) == .u) = true := by
            dsimp only [innerInv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
            rw [hT1, unaryTape_lt ht]; rfl
          refine ⟨hcell1, ?_⟩
          unfold divAdvanceAct; rw [applyAct_mkAct1]
          refine Mem.eq_of_fields ?_ (fun i p => ?_) (fun i => ?_) rfl
          · dsimp only [innerInv, Dir.shift]; omega
          · dsimp only [innerInv]
            fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]
            exact congrFun (ite_self_cell (m.work 1) _) p
          · dsimp only [innerInv, Dir.shift]
            fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]; omega)
        (by
          dsimp only [innerInv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
          rw [hT1, unaryTape_ge le_rfl]; rfl)
      rw [applyAct_actStay] at hW
      have hRew1 := Runs_rewindFromEnd (w := w) (1 : Fin 2) (innerInv b) b
        (by dsimp only [innerInv]; simp)
        (fun j hj => by dsimp only [innerInv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]; rw [hT1, unaryTape_lt hj]; decide)
        (by dsimp only [innerInv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]; rw [hT1]; exact unaryTape_neg (by omega))
      have hEndInner :
          { innerInv b with workPos := fun i => if i = 1 then 0 else (innerInv b).workPos i } =
          outerInv (q + 1) := by
        have hmul : q * b + b = (q + 1) * b := by ring
        refine Mem.eq_of_fields ?_ (fun _ _ => rfl) (fun i => ?_) rfl
        · dsimp only [innerInv, outerInv]; exact congrArg Nat.cast hmul
        · dsimp only [innerInv, outerInv]
          fin_cases i <;> simp [hP1]
      rw [hEndInner] at hRew1
      have hTime : (b + 1) + (b + 2) = 2 * b + 3 := by omega
      rw [← hTime]
      exact hW.seq hRew1)
    (by
      dsimp only [outerInv]
      rw [readInput_of_nonneg, List.getElem?_eq_none (by omega)]; rfl)
  rw [hOuter0, applyAct_actStay] at hLoop
  have hRewIn := Runs_rewindInputFromPos (w := w) (outerInv Q) (Q * b) rfl (by omega)
  let mAfterIn : Mem 2 WorkSym := { outerInv Q with inPos := 0 }
  have hInEq : { outerInv Q with inPos := 0 } = mAfterIn := rfl
  rw [hInEq] at hRewIn
  have hRew0 := Runs_rewindFromEnd (w := w) (0 : Fin 2) mAfterIn Q
    (by dsimp only [mAfterIn, outerInv]; simp)
    (fun j hj => by dsimp only [mAfterIn, outerInv]; simp only [Fin.isValue, ↓reduceIte]; rw [unaryTape_lt hj]; decide)
    (by dsimp only [mAfterIn, outerInv]; simp only [Fin.isValue, ↓reduceIte]; exact unaryTape_neg (by omega))
  have hEnd :
      { mAfterIn with workPos := fun i => if i = 0 then 0 else mAfterIn.workPos i } =
      { m with work := fun i p => if i = 0 then unaryTape Q p else m.work i p } := by
    refine Mem.eq_of_fields hIn.symm (fun _ _ => rfl) (fun i => ?_) rfl
    dsimp only [mAfterIn, outerInv]
    fin_cases i <;> simp [hP0, hP1]
  rw [hEnd] at hRew0
  have hTime : ((Q * (1 + (2 * b + 3)) + 1) + (Q * b + 2)) + (Q + 2) =
      3 * Q * b + 5 * Q + 5 := by ring
  rw [← hTime]
  exact (hLoop.seq hRewIn).seq hRew0

/-- Tape 1 scratch layout during `unarySqrt` and `buildRowTemplate`:
for `k = 0`, `oddScratch b 0 = unaryTape b`; for `k ≥ 1`, `-1` holds `.wall`,
`[-2k, -2]` holds `.oddD` at even cells and `.oddAux` at odd cells, `< -2k` is `.blank`,
and `[0, ∞)` holds `unaryTape b`. -/
private def oddScratch (b k : ℕ) : Int → WorkSym :=
  fun p =>
    if 1 ≤ k ∧ p = -1 then .wall
    else if -2 * (k : Int) ≤ p ∧ p ≤ -2 then
      if p % 2 = 0 then .oddD else .oddAux
    else unaryTape b p

private theorem oddScratch_zero (b : ℕ) : oddScratch b 0 = unaryTape b := by
  funext p; unfold oddScratch
  split_ifs <;> first | rfl | omega

private theorem oddScratch_init (b : ℕ) :
    (fun p : Int =>
      if p = -2 then WorkSym.oddD
      else if p = -1 then WorkSym.wall
      else unaryTape b p) = oddScratch b 1 := by
  funext p; unfold oddScratch
  by_cases hp2 : p = -2
  · subst hp2; simp
  · by_cases hp1 : p = -1
    · subst hp1; simp
    · have h1 : ¬ (1 ≤ 1 ∧ p = -1) := by omega
      have h2 : ¬ (-2 * ((1 : ℕ) : Int) ≤ p ∧ p ≤ -2) := by omega
      rw [ite_eq_right hp2, ite_eq_right hp1, ite_eq_right h1, ite_eq_right h2]

private theorem oddScratch_wall {b k : ℕ} (hk : 1 ≤ k) :
    oddScratch b k (-1) = .wall := by
  unfold oddScratch; simp [hk]

private theorem oddScratch_mid_ne_blank {b k : ℕ} {p : Int}
    (hlo : -2 * (k : Int) ≤ p) (hhi : p ≤ -2) :
    oddScratch b k p ≠ .blank := by
  unfold oddScratch
  have hnot1 : ¬ (1 ≤ k ∧ p = -1) := by omega
  have hmid : -2 * (k : Int) ≤ p ∧ p ≤ -2 := ⟨hlo, hhi⟩
  rw [ite_eq_right hnot1, ite_eq_left hmid]
  split_ifs <;> decide

private theorem oddScratch_mid_ne_wall {b k : ℕ} {p : Int}
    (hlo : -2 * (k : Int) ≤ p) (hhi : p ≤ -2) :
    oddScratch b k p ≠ .wall := by
  unfold oddScratch
  have hnot1 : ¬ (1 ≤ k ∧ p = -1) := by omega
  have hmid : -2 * (k : Int) ≤ p ∧ p ≤ -2 := ⟨hlo, hhi⟩
  rw [ite_eq_right hnot1, ite_eq_left hmid]
  split_ifs <;> decide

private theorem oddScratch_lt_blank (b k : ℕ) {p : Int}
    (hlt : p < -2 * (k : Int)) (h1 : ¬ (1 ≤ k ∧ p = -1)) (hneg : p < 0) :
    oddScratch b k p = .blank := by
  unfold oddScratch
  have h2 : ¬ (-2 * (k : Int) ≤ p ∧ p ≤ -2) := by omega
  rw [ite_eq_right h1, ite_eq_right h2]
  exact unaryTape_neg hneg

private theorem oddScratch_nonneg (b k : ℕ) {p : Int} (hp : 0 ≤ p) :
    oddScratch b k p = unaryTape b p := by
  unfold oddScratch
  have h1 : ¬ (1 ≤ k ∧ p = -1) := by omega
  have h2 : ¬ (-2 * (k : Int) ≤ p ∧ p ≤ -2) := by omega
  rw [ite_eq_right h1, ite_eq_right h2]

private theorem oddScratch_left_end {b k : ℕ} (hk : 1 ≤ k) :
    oddScratch b k (-2 * (k : Int)) = .oddD := by
  unfold oddScratch
  have h1 : ¬ (1 ≤ k ∧ -2 * (k : Int) = -1) := by omega
  have h2 : -2 * (k : Int) ≤ -2 * (k : Int) ∧ -2 * (k : Int) ≤ -2 := by omega
  have h3 : (-2 * (k : Int)) % 2 = 0 := by omega
  rw [ite_eq_right h1, ite_eq_left h2, ite_eq_left h3]

private theorem oddScratch_neg_ne_u (b k : ℕ) {p : Int}
    (hlo : -2 * (k : Int) ≤ p) (hneg : p < 0) :
    oddScratch b k p ≠ .u := by
  have hk1 : 1 ≤ k := by omega
  by_cases hp1 : p = -1
  · subst hp1; rw [oddScratch_wall hk1]; decide
  · unfold oddScratch
    have h1 : ¬ (1 ≤ k ∧ p = -1) := by omega
    have h2 : -2 * (k : Int) ≤ p ∧ p ≤ -2 := by omega
    rw [ite_eq_right h1, ite_eq_left h2]
    split_ifs <;> decide

private theorem oddScratch_extend {b k : ℕ} (hk : 1 ≤ k) :
    (fun p : Int =>
      if p = -2 * ((k + 1 : ℕ) : Int) then WorkSym.oddD
      else if p = -2 * (k : Int) - 1 then WorkSym.oddAux
      else oddScratch b k p) = oddScratch b (k + 1) := by
  funext p
  by_cases hpD : p = -2 * ((k + 1 : ℕ) : Int)
  · subst hpD
    simp only [↓reduceIte]
    exact (oddScratch_left_end (by omega : 1 ≤ k + 1)).symm
  · by_cases hpA : p = -2 * (k : Int) - 1
    · subst hpA
      simp only [hpD, ↓reduceIte]
      unfold oddScratch
      have h1 : ¬ (1 ≤ k + 1 ∧ -2 * (k : Int) - 1 = -1) := by omega
      have h2 : -2 * ((k + 1 : ℕ) : Int) ≤ -2 * (k : Int) - 1 ∧ -2 * (k : Int) - 1 ≤ -2 := by omega
      have h3 : ¬ ((-2 * (k : Int) - 1) % 2 = 0) := by omega
      rw [ite_eq_right h1, ite_eq_left h2, ite_eq_right h3]
    · simp only [hpD, hpA, ↓reduceIte]
      unfold oddScratch
      by_cases h1 : p = -1
      · subst h1; simp [hk]
      · have hn1 : ¬ (1 ≤ k ∧ p = -1) := by omega
        have hn2 : ¬ (1 ≤ k + 1 ∧ p = -1) := by omega
        rw [ite_eq_right hn1, ite_eq_right hn2]
        by_cases hm : -2 * (k : Int) ≤ p ∧ p ≤ -2
        · have hm' : -2 * ((k + 1 : ℕ) : Int) ≤ p ∧ p ≤ -2 := by omega
          rw [ite_eq_left hm, ite_eq_left hm']
        · have hm' : ¬ (-2 * ((k + 1 : ℕ) : Int) ≤ p ∧ p ≤ -2) := by omega
          rw [ite_eq_right hm, ite_eq_right hm']

private theorem oddScratch_erase_pair {b m : ℕ} (hm : 1 ≤ m) :
    (fun p : Int =>
      if p = -2 * (m : Int) + 1 then WorkSym.blank
      else if p = -2 * (m : Int) then WorkSym.blank
      else oddScratch b m p) = oddScratch b (m - 1) := by
  funext p
  by_cases hp1 : p = -2 * (m : Int) + 1
  · subst hp1; simp only [↓reduceIte]
    exact (oddScratch_lt_blank b (m - 1) (by omega) (by omega) (by omega)).symm
  · by_cases hp0 : p = -2 * (m : Int)
    · subst hp0; simp only [hp1, ↓reduceIte]
      exact (oddScratch_lt_blank b (m - 1) (by omega) (by omega) (by omega)).symm
    · simp only [hp1, hp0, ↓reduceIte]
      unfold oddScratch
      by_cases hm2 : 2 ≤ m
      · by_cases hwall : p = -1
        · subst hwall
          have ha : 1 ≤ m ∧ (-1 : Int) = -1 := ⟨hm, rfl⟩
          have hb : 1 ≤ m - 1 ∧ (-1 : Int) = -1 := ⟨by omega, rfl⟩
          rw [ite_eq_left ha, ite_eq_left hb]
        · have ha : ¬ (1 ≤ m ∧ p = -1) := by omega
          have hb : ¬ (1 ≤ m - 1 ∧ p = -1) := by omega
          rw [ite_eq_right ha, ite_eq_right hb]
          by_cases hmid : -2 * ((m - 1 : ℕ) : Int) ≤ p ∧ p ≤ -2
          · have hmid' : -2 * (m : Int) ≤ p ∧ p ≤ -2 := by omega
            rw [ite_eq_left hmid', ite_eq_left hmid]
          · have hmid' : ¬ (-2 * (m : Int) ≤ p ∧ p ≤ -2) := by omega
            rw [ite_eq_right hmid', ite_eq_right hmid]
      · have hmEq : m = 1 := by omega
        subst hmEq
        have ha : ¬ (1 ≤ 1 ∧ p = -1) := by omega
        have hb : ¬ (1 ≤ 1 - 1 ∧ p = -1) := by omega
        have hc : ¬ (-2 * ((1 : ℕ) : Int) ≤ p ∧ p ≤ -2) := by omega
        have hd : ¬ (-2 * ((1 - 1 : ℕ) : Int) ≤ p ∧ p ≤ -2) := by omega
        rw [ite_eq_right ha, ite_eq_right hc, ite_eq_right hb, ite_eq_right hd]

private def sqrtInit1 : Action 2 WorkSym :=
  mkAct2 0 1 (fun _ _ _ => .stay)
    (fun _ s₀ _ => (s₀, .right)) (fun _ _ s₁ => (s₁, .left)) (fun _ _ _ => none)

private def sqrtStepBoth : Action 2 WorkSym :=
  mkAct2 0 1 (fun _ _ _ => .stay)
    (fun _ s₀ _ => (s₀, .right)) (fun _ _ s₁ => (s₁, .left)) (fun _ _ _ => none)

private def sqrtWriteAux : Action 2 WorkSym :=
  mkAct2 0 1 (fun _ _ _ => .stay)
    (fun _ s₀ _ => (s₀, .right)) (fun _ _ _ => (.oddAux, .left)) (fun _ _ _ => none)

private def sqrtWriteD : Action 2 WorkSym :=
  mkAct2 0 1 (fun _ _ _ => .stay)
    (fun _ s₀ _ => (s₀, .right)) (fun _ _ _ => (.oddD, .right)) (fun _ _ _ => none)

/-- Extract `d` from `unaryTape (d * d)` on Tape 0 via `1 + 3 + ... + (2d - 1) = d^2`,
erasing Tape 0 (`pos = 0`) and leaving `oddScratch b d` (`pos = -1`) on Tape 1. -/
private def unarySqrtBlock : Block 2 WorkSym :=
  (((((Block.act sqrtInit1).seq (Block.act (writeDirAct 1 .wall .left))).seq
    (Block.act (writeDirAct 1 .oddD .right))).seq
    (Block.loop (fun _ sc => sc 0 == .u)
      (stepDirAct 1 .left) actStay
      (((Block.while1 (fun _ sc => sc 1 != .blank) sqrtStepBoth sqrtWriteAux).seq
        (Block.act sqrtWriteD)).seq
        (Block.while1 (fun _ sc => sc 1 != .wall) (stepDirAct 1 .right) actStay)))).seq
    (eraseFromEnd 0))

private theorem Runs_unarySqrtBlock {w : List Bool} (m : Mem 2 WorkSym) (d b : ℕ)
    (hd1 : 1 ≤ d)
    (hT0 : m.work 0 = unaryTape (d * d)) (hP0 : m.workPos 0 = 0)
    (hT1 : m.work 1 = unaryTape b) (hP1 : m.workPos 1 = 0) :
    ∃ t ≤ 5 * d * d + 6,
      Runs unarySqrtBlock w m
        { m with
          work    := fun i p => if i = 0 then .blank else oddScratch b d p
          workPos := fun i => if i = 0 then 0 else -1 } t := by
  unfold unarySqrtBlock
  let outerInv (idx : ℕ) : Mem 2 WorkSym :=
    let k := idx + 1
    { m with
      work    := fun i p => if i = 1 then oddScratch b k p else m.work i p
      workPos := fun i => if i = 0 then ((k * k : ℕ) : Int) else -1 }
  -- 3-step initialization to `outerInv 0` (`k = 1`)
  let mI1 : Mem 2 WorkSym :=
    { m with workPos := fun i => if i = 0 then 1 else -1 }
  have hI1 : applyAct w sqrtInit1 m = mI1 := by
    unfold sqrtInit1; rw [applyAct_mkAct2 w m (by decide : (0 : Fin 2) ≠ 1)]
    refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
    · dsimp only [mI1]
      fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]
      · exact congrFun (ite_self_cell (m.work 0) _) p
      · exact congrFun (ite_self_cell (m.work 1) _) p
    · dsimp only [mI1, Dir.shift]
      fin_cases i <;> simp [hP0, hP1]
  let mI2 : Mem 2 WorkSym :=
    { m with
      work    := fun i p => if i = 1 then (if p = -1 then .wall else m.work 1 p) else m.work i p
      workPos := fun i => if i = 0 then 1 else -2 }
  have hI2 : applyAct w (writeDirAct 1 .wall .left) mI1 = mI2 := by
    unfold writeDirAct; rw [applyAct_mkAct1]
    refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
    · dsimp only [mI1, mI2]
      fin_cases i <;> simp
    · dsimp only [mI1, mI2, Dir.shift]
      fin_cases i <;> simp
  have hI3 : applyAct w (writeDirAct 1 .oddD .right) mI2 = outerInv 0 := by
    unfold writeDirAct; rw [applyAct_mkAct1]
    refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
    · dsimp only [mI2, outerInv]
      fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]
      rw [hT1]
      exact congrFun (oddScratch_init b) p
    · dsimp only [mI2, outerInv, Dir.shift]
      fin_cases i <;> simp
  have rInit : Runs (((Block.act sqrtInit1).seq (Block.act (writeDirAct 1 .wall .left))).seq
      (Block.act (writeDirAct 1 .oddD .right))) w m (outerInv 0) 3 := by
    have r1 : Runs (Block.act sqrtInit1) w m mI1 1 := by rw [← hI1]; exact Runs.act _ _
    have r2 : Runs (Block.act (writeDirAct 1 .wall .left)) w mI1 mI2 1 := by rw [← hI2]; exact Runs.act _ _
    have r3 : Runs (Block.act (writeDirAct 1 .oddD .right)) w mI2 (outerInv 0) 1 := by rw [← hI3]; exact Runs.act _ _
    simpa using (r1.seq r2).seq r3
  -- Outer loop (`d - 1` iterations, `idx = 0 .. d - 2`, `k = idx + 1`)
  let tBody (idx : ℕ) : ℕ := 4 * (idx + 1) + 2
  have rLoop := Runs.loop_sum (w := w)
    (fun _ (sc : Fin 2 → WorkSym) => sc 0 == .u)
    (stepDirAct 1 .left) actStay
    (((Block.while1 (fun _ sc => sc 1 != .blank) sqrtStepBoth sqrtWriteAux).seq
      (Block.act sqrtWriteD)).seq
      (Block.while1 (fun _ sc => sc 1 != .wall) (stepDirAct 1 .right) actStay))
    (d - 1) tBody outerInv
    (fun idx hidx => by
      set k := idx + 1
      have hk1 : 1 ≤ k := by omega
      have hkd : k < d := by omega
      have hkk_lt : k * k < d * d := Nat.mul_lt_mul_of_lt_of_lt hkd hkd
      have hCond : ((outerInv idx).work 0 ((outerInv idx).workPos 0) == .u) = true := by
        dsimp only [outerInv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
        rw [hT0, unaryTape_lt hkk_lt]; rfl
      refine ⟨hCond, ?_⟩
      -- Part A: scan `2 * k - 1` non-blank cells `-2 .. -2k`, then write `.oddAux` at `-2k - 1`
      let scanInv (j : ℕ) : Mem 2 WorkSym :=
        { m with
          work    := fun i p => if i = 1 then oddScratch b k p else m.work i p
          workPos := fun i =>
            if i = 0 then ((k * k + j : ℕ) : Int)
            else -2 - (j : Int) }
      have hEnt : applyAct w (stepDirAct 1 .left) (outerInv idx) = scanInv 0 := by
        unfold stepDirAct; rw [applyAct_mkAct1]
        refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
        · dsimp only [outerInv, scanInv]
          fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]
          exact congrFun (ite_self_cell (oddScratch b k) _) p
        · dsimp only [outerInv, scanInv, k, Dir.shift]
          fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte, Nat.add_zero]; omega
      rw [hEnt]
      have hWA := Runs.while1 (w := w)
        (fun _ (sc : Fin 2 → WorkSym) => sc 1 != .blank)
        sqrtStepBoth sqrtWriteAux (2 * k - 1) scanInv
        (fun j hj => by
          have hcell : (scanInv j).work 1 ((scanInv j).workPos 1) ≠ .blank := by
            dsimp only [scanInv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
            exact oddScratch_mid_ne_blank (by omega) (by omega)
          refine ⟨bne_blank_of_ne hcell, ?_⟩
          unfold sqrtStepBoth; rw [applyAct_mkAct2 w (scanInv j) (by decide : (0 : Fin 2) ≠ 1)]
          refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
          · dsimp only [scanInv]
            fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]
            · exact congrFun (ite_self_cell (m.work 0) _) p
            · exact congrFun (ite_self_cell (oddScratch b k) _) p
          · dsimp only [scanInv, Dir.shift]
            fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte] <;> omega)
        (by
          dsimp only [scanInv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
          have hpEq : -2 - ((2 * k - 1 : ℕ) : Int) = -2 * (k : Int) - 1 := by omega
          rw [hpEq, oddScratch_lt_blank b k (by omega) (by omega) (by omega)]; rfl)
      let mAfterAux : Mem 2 WorkSym :=
        { m with
          work := fun i p =>
            if i = 1 then (if p = -2 * (k : Int) - 1 then .oddAux else oddScratch b k p)
            else m.work i p
          workPos := fun i =>
            if i = 0 then ((k * k + 2 * k : ℕ) : Int)
            else -2 * ((k + 1 : ℕ) : Int) }
      have hAuxEq : applyAct w sqrtWriteAux (scanInv (2 * k - 1)) = mAfterAux := by
        unfold sqrtWriteAux; rw [applyAct_mkAct2 w _ (by decide : (0 : Fin 2) ≠ 1)]
        refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
        · dsimp only [scanInv, mAfterAux]
          fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]
          · exact congrFun (ite_self_cell (m.work 0) _) p
          · have hpEq : -2 - ((2 * k - 1 : ℕ) : Int) = -2 * (k : Int) - 1 := by omega
            rw [hpEq]
        · dsimp only [scanInv, mAfterAux, Dir.shift]
          fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte] <;> omega
      rw [hAuxEq] at hWA
      have hTimeA : (2 * k - 1) + 1 = 2 * k := by omega
      rw [hTimeA] at hWA
      -- Part B: write `.oddD` at `-2*(k+1)`, advancing `t₀` to `(k+1)^2` and `t₁` to `-2k - 1`
      let backInv (j : ℕ) : Mem 2 WorkSym :=
        { m with
          work    := fun i p => if i = 1 then oddScratch b (k + 1) p else m.work i p
          workPos := fun i =>
            if i = 0 then (((k + 1) * (k + 1) : ℕ) : Int)
            else -2 * (k : Int) - 1 + (j : Int) }
      have hDEq : applyAct w sqrtWriteD mAfterAux = backInv 0 := by
        unfold sqrtWriteD; rw [applyAct_mkAct2 w _ (by decide : (0 : Fin 2) ≠ 1)]
        refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
        · dsimp only [mAfterAux, backInv]
          fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]
          · exact congrFun (ite_self_cell (m.work 0) _) p
          · exact congrFun (oddScratch_extend hk1) p
        · dsimp only [mAfterAux, backInv, Dir.shift]
          have hsq : k * k + 2 * k + 1 = (k + 1) * (k + 1) := by ring
          fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte] <;> omega
      have hWB : Runs (Block.act sqrtWriteD) w mAfterAux (backInv 0) 1 := by
        rw [← hDEq]; exact Runs.act _ _
      -- Part C: return `t₁` right to `.wall` at `-1` (`2 * k` steps)
      have hWC := Runs.while1 (w := w)
        (fun _ (sc : Fin 2 → WorkSym) => sc 1 != .wall)
        (stepDirAct 1 .right) actStay (2 * k) backInv
        (fun j hj => by
          have hneW : (backInv j).work 1 ((backInv j).workPos 1) ≠ .wall := by
            dsimp only [backInv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
            exact oddScratch_mid_ne_wall (by omega) (by omega)
          have hbne : ((backInv j).work 1 ((backInv j).workPos 1) != .wall) = true := by
            cases h : (backInv j).work 1 ((backInv j).workPos 1) <;>
              first | exact absurd h hneW | rfl
          refine ⟨hbne, ?_⟩
          unfold stepDirAct; rw [applyAct_mkAct1]
          refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
          · dsimp only [backInv]
            fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]
            exact congrFun (ite_self_cell (oddScratch b (k + 1)) _) p
          · dsimp only [backInv, Dir.shift]
            fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]; omega)
        (by
          dsimp only [backInv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
          have hm1 : -2 * (k : Int) - 1 + (2 * k : ℕ) = -1 := by omega
          rw [hm1, oddScratch_wall (by omega : 1 ≤ k + 1)]; rfl)
      rw [applyAct_actStay] at hWC
      have hBackEnd : backInv (2 * k) = outerInv (idx + 1) := by
        refine Mem.eq_of_fields rfl (fun _ _ => rfl) (fun i => ?_) rfl
        dsimp only [backInv, outerInv, k]
        fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]; omega
      rw [hBackEnd] at hWC
      have hTime : (2 * k + 1) + (2 * k + 1) = tBody idx := by dsimp [tBody, k]; omega
      rw [← hTime]
      exact (hWA.seq hWB).seq hWC)
    (by
      have hdEq : d - 1 + 1 = d := by omega
      dsimp only [outerInv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte, hdEq]
      rw [hT0, unaryTape_ge le_rfl]; rfl)
  rw [applyAct_actStay] at rLoop
  -- Erase `[0, d * d)` on Tape 0
  have hdEq : d - 1 + 1 = d := by omega
  have hEr0 := Runs_eraseFromEnd (w := w) (0 : Fin 2) (outerInv (d - 1)) (d * d)
    (by dsimp only [outerInv]; simp [hdEq])
    (fun j hj => by dsimp only [outerInv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]; rw [hT0, unaryTape_lt hj]; decide)
    (fun p hp => by
      dsimp only [outerInv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]; rw [hT0]
      rcases hp with hneg | hge
      · exact unaryTape_neg hneg
      · exact unaryTape_ge hge)
  have hFinalEq :
      { outerInv (d - 1) with
        work    := fun i p => if i = 0 then WorkSym.blank else (outerInv (d - 1)).work i p
        workPos := fun i => if i = 0 then 0 else (outerInv (d - 1)).workPos i } =
      { m with
        work    := fun i p => if i = 0 then .blank else oddScratch b d p
        workPos := fun i => if i = 0 then 0 else -1 } := by
    refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
    · dsimp only [outerInv]; fin_cases i <;> simp [hdEq]
    · dsimp only [outerInv]; fin_cases i <;> simp
  rw [hFinalEq] at hEr0
  have hAll := (rInit.seq rLoop).seq hEr0
  refine ⟨_, ?_, hAll⟩
  have hSumLe := natSum_le_of_step (f := fun idx => 1 + tBody idx)
    (g := fun idx => idx * (4 * d)) (N := d - 1)
    (fun idx hidx => by dsimp only [tBody]; nlinarith)
  have hMulLe : (d - 1) * (4 * d) ≤ 4 * d * d := by nlinarith
  nlinarith

/-- Row-template tape prefix on `[0, len)` with `saveCount` leading `.save` cells,
followed by `.emitStart` at multiples of `b` and `.emitCont` elsewhere. -/
private def tplPrefix (len b saveCount : ℕ) : Int → WorkSym :=
  fun p =>
    if 0 ≤ p ∧ p < (len : Int) then
      if p < (saveCount : Int) then .save
      else if p.toNat % b = 0 then .emitStart
      else .emitCont
    else .blank

private theorem tplPrefix_zero (b s : ℕ) : tplPrefix 0 b s = fun _ => .blank := by
  funext p; unfold tplPrefix
  split_ifs <;> first | rfl | omega

private theorem tplPrefix_nonblank {len b s j : ℕ} (hj : j < len) :
    tplPrefix len b s (j : Int) ≠ .blank := by
  unfold tplPrefix
  have h : 0 ≤ (j : Int) ∧ (j : Int) < (len : Int) := by omega
  rw [ite_eq_left h]
  split_ifs <;> decide

private theorem tplPrefix_outside {len b s : ℕ} {p : Int}
    (hp : p < 0 ∨ (len : Int) ≤ p) :
    tplPrefix len b s p = .blank := by
  unfold tplPrefix
  have h : ¬ (0 ≤ p ∧ p < (len : Int)) := by omega
  rw [ite_eq_right h]

private theorem tplPrefix_append_start {len b : ℕ} (hmod : len % b = 0) :
    (fun p : Int => if p = (len : Int) then WorkSym.emitStart else tplPrefix len b 0 p) =
      tplPrefix (len + 1) b 0 := by
  funext p; unfold tplPrefix
  by_cases hp : p = (len : Int)
  · subst hp
    have h1 : 0 ≤ (len : Int) ∧ (len : Int) < ((len + 1 : ℕ) : Int) := by omega
    have h2 : ¬ ((len : Int) < ((0 : ℕ) : Int)) := by omega
    rw [ite_eq_left rfl, ite_eq_left h1, ite_eq_right h2, Int.toNat_natCast, ite_eq_left hmod]
  · rw [ite_eq_right hp]
    by_cases h1 : 0 ≤ p ∧ p < (len : Int)
    · have h2 : 0 ≤ p ∧ p < ((len + 1 : ℕ) : Int) := by omega
      rw [ite_eq_left h1, ite_eq_left h2]
    · have h2 : ¬ (0 ≤ p ∧ p < ((len + 1 : ℕ) : Int)) := by omega
      rw [ite_eq_right h1, ite_eq_right h2]

private theorem tplPrefix_append_cont {len b : ℕ} (hmod : len % b ≠ 0) :
    (fun p : Int => if p = (len : Int) then WorkSym.emitCont else tplPrefix len b 0 p) =
      tplPrefix (len + 1) b 0 := by
  funext p; unfold tplPrefix
  by_cases hp : p = (len : Int)
  · subst hp
    have h1 : 0 ≤ (len : Int) ∧ (len : Int) < ((len + 1 : ℕ) : Int) := by omega
    have h2 : ¬ ((len : Int) < ((0 : ℕ) : Int)) := by omega
    rw [ite_eq_left rfl, ite_eq_left h1, ite_eq_right h2, Int.toNat_natCast, ite_eq_right hmod]
  · rw [ite_eq_right hp]
    by_cases h1 : 0 ≤ p ∧ p < (len : Int)
    · have h2 : 0 ≤ p ∧ p < ((len + 1 : ℕ) : Int) := by omega
      rw [ite_eq_left h1, ite_eq_left h2]
    · have h2 : ¬ (0 ≤ p ∧ p < ((len + 1 : ℕ) : Int)) := by omega
      rw [ite_eq_right h1, ite_eq_right h2]

private theorem tplPrefix_write_save {len b k : ℕ} (hk : k < len) :
    (fun p : Int => if p = (k : Int) then WorkSym.save else tplPrefix len b k p) =
      tplPrefix len b (k + 1) := by
  funext p; unfold tplPrefix
  by_cases hp : p = (k : Int)
  · subst hp
    have h1 : 0 ≤ (k : Int) ∧ (k : Int) < (len : Int) := by omega
    have h2 : (k : Int) < ((k + 1 : ℕ) : Int) := by omega
    rw [ite_eq_left rfl, ite_eq_left h1, ite_eq_left h2]
  · rw [ite_eq_right hp]
    by_cases h1 : 0 ≤ p ∧ p < (len : Int)
    · rw [ite_eq_left h1, ite_eq_left h1]
      by_cases hs : p < (k : Int)
      · have hs' : p < ((k + 1 : ℕ) : Int) := by omega
        rw [ite_eq_left hs, ite_eq_left hs']
      · have hs' : ¬ (p < ((k + 1 : ℕ) : Int)) := by omega
        rw [ite_eq_right hs, ite_eq_right hs']
    · rw [ite_eq_right h1, ite_eq_right h1]

private def tplEmitStartAct : Action 2 WorkSym :=
  mkAct2 0 1 (fun _ _ _ => .stay)
    (fun _ _ _ => (.emitStart, .right)) (fun _ _ s₁ => (s₁, .right)) (fun _ _ _ => none)

private def tplEmitContAct : Action 2 WorkSym :=
  mkAct2 0 1 (fun _ _ _ => .stay)
    (fun _ _ _ => (.emitCont, .right)) (fun _ _ s₁ => (s₁, .right)) (fun _ _ _ => none)

/-- Build `tplPrefix (d * b) b 0` on Tape 0 (`pos = 0`) and clear Tape 1 (`pos = 0`)
from `oddScratch b d` (`pos = -1`) on Tape 1 in `O(d^2 + d * b)` steps. -/
private def buildRowTemplate : Block 2 WorkSym :=
  ((((Block.while1 (fun _ sc => sc 1 != .blank) (stepDirAct 1 .left) (stepDirAct 1 .right)).seq
    (Block.loop (fun _ sc => sc 1 == .oddD)
      (writeDirAct 1 .blank .right) actStay
      ((((Block.act (writeDirAct 1 .blank .right)).seq
        (Block.while1 (fun _ sc => sc 1 != .u) (stepDirAct 1 .right) tplEmitStartAct)).seq
        (Block.while1 (fun _ sc => sc 1 == .u) tplEmitContAct (stepDirAct 1 .left))).seq
        (Block.while1 (fun _ sc => sc 1 != .blank) (stepDirAct 1 .left) (stepDirAct 1 .right))))).seq
    (clearUnary 1)).seq
    (rewindFromEnd 0))

private theorem Runs_buildRowTemplate {w : List Bool} (m : Mem 2 WorkSym) (d b : ℕ)
    (hd1 : 1 ≤ d) (hb1 : 1 ≤ b)
    (hB0 : m.work 0 = fun _ => .blank) (hP0 : m.workPos 0 = 0)
    (hT1 : m.work 1 = oddScratch b d) (hP1 : m.workPos 1 = -1) :
    ∃ t ≤ 4 * d * d + 3 * d * b + 6 * d + 2 * b + 7,
      Runs buildRowTemplate w m
        { m with
          work    := fun i p => if i = 0 then tplPrefix (d * b) b 0 p else .blank
          workPos := fun _ => 0 } t := by
  unfold buildRowTemplate
  let outerInv (q : ℕ) : Mem 2 WorkSym :=
    { m with
      work := fun i p =>
        if i = 0 then tplPrefix (q * b) b 0 p
        else oddScratch b (d - q) p
      workPos := fun i =>
        if i = 0 then ((q * b : ℕ) : Int)
        else -2 * ((d - q : ℕ) : Int) }
  -- Step 1: walk Tape 1 left from `-1` to `-2 * d` (`2 * d + 1` steps)
  let walkInv (j : ℕ) : Mem 2 WorkSym :=
    { m with workPos := fun i => if i = 0 then 0 else -1 - (j : Int) }
  have hWalk0 : walkInv 0 = m := by
    refine Mem.eq_of_fields rfl (fun _ _ => rfl) (fun i => ?_) rfl
    dsimp only [walkInv]; fin_cases i <;> simp [hP0, hP1]
  have hWalk := Runs.while1 (w := w)
    (fun _ (sc : Fin 2 → WorkSym) => sc 1 != .blank)
    (stepDirAct 1 .left) (stepDirAct 1 .right) (2 * d) walkInv
    (fun j hj => by
      have hne : (walkInv j).work 1 ((walkInv j).workPos 1) ≠ .blank := by
        dsimp only [walkInv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
        rw [hT1]
        by_cases hj0 : j = 0
        · subst hj0; simp [oddScratch_wall hd1]
        · exact oddScratch_mid_ne_blank (by omega) (by omega)
      refine ⟨bne_blank_of_ne hne, ?_⟩
      unfold stepDirAct; rw [applyAct_mkAct1]
      refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
      · dsimp only [walkInv]
        fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]
        exact congrFun (ite_self_cell (m.work 1) _) p
      · dsimp only [walkInv, Dir.shift]
        fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]; omega)
    (by
      dsimp only [walkInv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
      rw [hT1, oddScratch_lt_blank b d (by omega) (by omega) (by omega)]; rfl)
  have hWalkExit : applyAct w (stepDirAct 1 .right) (walkInv (2 * d)) = outerInv 0 := by
    unfold stepDirAct; rw [applyAct_mkAct1]
    refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
    · dsimp only [walkInv, outerInv]
      fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte, Nat.zero_mul, Nat.sub_zero]
      · rw [tplPrefix_zero, hB0]
      · rw [congrFun (ite_self_cell (m.work 1) _) p, hT1]
    · dsimp only [walkInv, outerInv, Dir.shift]
      fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte, Nat.zero_mul, Nat.sub_zero] <;> omega
  rw [hWalk0, hWalkExit] at hWalk
  -- Step 2: `d` iterations of `outerInv q → outerInv (q + 1)`
  let tBody (q : ℕ) : ℕ := 4 * (d - 1 - q) + 2 * b + 3
  have hLoop := Runs.loop_sum (w := w)
    (fun _ (sc : Fin 2 → WorkSym) => sc 1 == .oddD)
    (writeDirAct 1 .blank .right) actStay
    ((((Block.act (writeDirAct 1 .blank .right)).seq
      (Block.while1 (fun _ sc => sc 1 != .u) (stepDirAct 1 .right) tplEmitStartAct)).seq
      (Block.while1 (fun _ sc => sc 1 == .u) tplEmitContAct (stepDirAct 1 .left))).seq
      (Block.while1 (fun _ sc => sc 1 != .blank) (stepDirAct 1 .left) (stepDirAct 1 .right)))
    d tBody outerInv
    (fun q hq => by
      set mRem := d - q
      have hm1 : 1 ≤ mRem := by omega
      have hremEq : mRem - 1 = d - (q + 1) := by omega
      have hCond : ((outerInv q).work 1 ((outerInv q).workPos 1) == .oddD) = true := by
        dsimp only [outerInv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
        rw [oddScratch_left_end hm1]; rfl
      refine ⟨hCond, ?_⟩
      -- Enter + erase second cell of pair (`-2 * mRem` and `-2 * mRem + 1`)
      let mEr1 : Mem 2 WorkSym :=
        { m with
          work := fun i p =>
            if i = 0 then tplPrefix (q * b) b 0 p
            else (if p = -2 * (mRem : Int) then .blank else oddScratch b mRem p)
          workPos := fun i =>
            if i = 0 then ((q * b : ℕ) : Int)
            else -2 * (mRem : Int) + 1 }
      have hEnt : applyAct w (writeDirAct 1 .blank .right) (outerInv q) = mEr1 := by
        unfold writeDirAct; rw [applyAct_mkAct1]
        refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
        · dsimp only [outerInv, mEr1, mRem]
          fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]
        · dsimp only [outerInv, mEr1, mRem, Dir.shift]
          fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]
      rw [hEnt]
      set nScan := 2 * (mRem - 1)
      let scanUInv (j : ℕ) : Mem 2 WorkSym :=
        { m with
          work := fun i p =>
            if i = 0 then tplPrefix (q * b) b 0 p
            else oddScratch b (mRem - 1) p
          workPos := fun i =>
            if i = 0 then ((q * b : ℕ) : Int)
            else -(nScan : Int) + (j : Int) }
      have hEr2Eq : applyAct w (writeDirAct 1 .blank .right) mEr1 = scanUInv 0 := by
        unfold writeDirAct; rw [applyAct_mkAct1]
        refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
        · dsimp only [mEr1, scanUInv]
          fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]
          exact congrFun (oddScratch_erase_pair hm1) p
        · dsimp only [mEr1, scanUInv, Dir.shift, nScan]
          fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]; omega
      have rEr2 : Runs (Block.act (writeDirAct 1 .blank .right)) w mEr1 (scanUInv 0) 1 := by
        rw [← hEr2Eq]; exact Runs.act _ _
      -- Scan right to `0` (`sc 1 != .u`), then write `.emitStart` at `q * b` on Tape 0
      have rScanU := Runs.while1 (w := w)
        (fun _ (sc : Fin 2 → WorkSym) => sc 1 != .u)
        (stepDirAct 1 .right) tplEmitStartAct nScan scanUInv
        (fun j hj => by
          have hneU : (scanUInv j).work 1 ((scanUInv j).workPos 1) ≠ .u := by
            dsimp only [scanUInv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
            exact oddScratch_neg_ne_u b (mRem - 1) (by omega) (by omega)
          have hbneU : ((scanUInv j).work 1 ((scanUInv j).workPos 1) != .u) = true := by
            cases h : (scanUInv j).work 1 ((scanUInv j).workPos 1) <;>
              first | exact absurd h hneU | rfl
          refine ⟨hbneU, ?_⟩
          unfold stepDirAct; rw [applyAct_mkAct1]
          refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
          · dsimp only [scanUInv]
            fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]
            exact congrFun (ite_self_cell (oddScratch b (mRem - 1)) _) p
          · dsimp only [scanUInv, Dir.shift]
            fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]; omega)
        (by
          dsimp only [scanUInv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
          have h0 : -(nScan : Int) + (nScan : Int) = (0 : ℕ) := by omega
          rw [h0, oddScratch_nonneg b (mRem - 1) (by omega), unaryTape_lt (by omega : 0 < b)]; rfl)
      -- Emit `b - 1` `.emitCont` cells across `[1, b)` on Tape 1
      let contInv (j : ℕ) : Mem 2 WorkSym :=
        { m with
          work := fun i p =>
            if i = 0 then tplPrefix (q * b + 1 + j) b 0 p
            else oddScratch b (mRem - 1) p
          workPos := fun i =>
            if i = 0 then ((q * b + 1 + j : ℕ) : Int)
            else ((1 + j : ℕ) : Int) }
      have hStartEq : applyAct w tplEmitStartAct (scanUInv nScan) = contInv 0 := by
        unfold tplEmitStartAct; rw [applyAct_mkAct2 w _ (by decide : (0 : Fin 2) ≠ 1)]
        refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
        · dsimp only [scanUInv, contInv, Nat.add_zero]
          fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]
          · exact congrFun (tplPrefix_append_start (Nat.mul_mod_left q b)) p
          · exact congrFun (ite_self_cell (oddScratch b (mRem - 1)) _) p
        · dsimp only [scanUInv, contInv, Dir.shift]
          fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte] <;> omega
      rw [hStartEq] at rScanU
      have rCont := Runs.while1 (w := w)
        (fun _ (sc : Fin 2 → WorkSym) => sc 1 == .u)
        tplEmitContAct (stepDirAct 1 .left) (b - 1) contInv
        (fun j hj => by
          have hcellU : ((contInv j).work 1 ((contInv j).workPos 1) == .u) = true := by
            dsimp only [contInv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
            rw [oddScratch_nonneg b (mRem - 1) (by omega), unaryTape_lt (by omega : 1 + j < b)]; rfl
          refine ⟨hcellU, ?_⟩
          have hmodNe : (q * b + 1 + j) % b ≠ 0 := by
            have h1 : q * b + 1 + j = (1 + j) + q * b := by ring
            rw [h1, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega : 1 + j < b)]
            omega
          unfold tplEmitContAct; rw [applyAct_mkAct2 w _ (by decide : (0 : Fin 2) ≠ 1)]
          refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
          · dsimp only [contInv]
            fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]
            · have hadd : q * b + 1 + (j + 1) = (q * b + 1 + j) + 1 := by omega
              rw [hadd]
              exact congrFun (tplPrefix_append_cont hmodNe) p
            · exact congrFun (ite_self_cell (oddScratch b (mRem - 1)) _) p
          · dsimp only [contInv, Dir.shift]
            fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte] <;> omega)
        (by
          dsimp only [contInv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
          have hbEq : 1 + (b - 1) = b := by omega
          rw [hbEq, oddScratch_nonneg b (mRem - 1) (by omega), unaryTape_ge le_rfl]; rfl)
      have hTimeC : (b - 1) + 1 = b := by omega
      rw [hTimeC] at rCont
      -- Scan left across `[ -nScan, b - 1 ]` back to `-nScan` (`nScan + b + 1` steps)
      let retInv (j : ℕ) : Mem 2 WorkSym :=
        { m with
          work := fun i p =>
            if i = 0 then tplPrefix ((q + 1) * b) b 0 p
            else oddScratch b (mRem - 1) p
          workPos := fun i =>
            if i = 0 then (((q + 1) * b : ℕ) : Int)
            else ((b - 1 : ℕ) : Int) - (j : Int) }
      have hContExit : applyAct w (stepDirAct 1 .left) (contInv (b - 1)) = retInv 0 := by
        unfold stepDirAct; rw [applyAct_mkAct1]
        have hqb : q * b + 1 + (b - 1) = (q + 1) * b := by
          have : 1 + (b - 1) = b := by omega
          calc q * b + 1 + (b - 1) = q * b + (1 + (b - 1)) := by omega
            _ = q * b + b := by rw [this]
            _ = (q + 1) * b := by ring
        refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
        · dsimp only [contInv, retInv]
          fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]
          · rw [hqb]
          · exact congrFun (ite_self_cell (oddScratch b (mRem - 1)) _) p
        · dsimp only [contInv, retInv, Dir.shift]
          fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]
          · exact congrArg Nat.cast hqb
          · omega
      rw [hContExit] at rCont
      have rRet := Runs.while1 (w := w)
        (fun _ (sc : Fin 2 → WorkSym) => sc 1 != .blank)
        (stepDirAct 1 .left) (stepDirAct 1 .right) (nScan + b) retInv
        (fun j hj => by
          have hneB : (retInv j).work 1 ((retInv j).workPos 1) ≠ .blank := by
            dsimp only [retInv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
            set pos1 : Int := ((b - 1 : ℕ) : Int) - (j : Int)
            by_cases hpos0 : 0 ≤ pos1
            · rw [oddScratch_nonneg b (mRem - 1) hpos0]
              have hnat : pos1 = ((pos1.toNat : ℕ) : Int) := (Int.toNat_of_nonneg hpos0).symm
              rw [hnat, unaryTape_lt (by omega : pos1.toNat < b)]; decide
            · by_cases hpos1 : pos1 = -1
              · rw [hpos1, oddScratch_wall (by omega : 1 ≤ mRem - 1)]; decide
              · exact oddScratch_mid_ne_blank (by omega) (by omega)
          refine ⟨bne_blank_of_ne hneB, ?_⟩
          unfold stepDirAct; rw [applyAct_mkAct1]
          refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
          · dsimp only [retInv]
            fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]
            exact congrFun (ite_self_cell (oddScratch b (mRem - 1)) _) p
          · dsimp only [retInv, Dir.shift]
            fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]; omega)
        (by
          dsimp only [retInv, nScan]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
          rw [oddScratch_lt_blank b (mRem - 1) (by omega) (by omega) (by omega)]; rfl)
      have hRetExit : applyAct w (stepDirAct 1 .right) (retInv (nScan + b)) = outerInv (q + 1) := by
        unfold stepDirAct; rw [applyAct_mkAct1]
        refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
        · dsimp only [retInv, outerInv]
          fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]
          rw [congrFun (ite_self_cell (oddScratch b (mRem - 1)) _) p, hremEq]
        · dsimp only [retInv, outerInv, Dir.shift, nScan]
          fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]
          omega
      rw [hRetExit] at rRet
      have hTimeIter : ((1 + (nScan + 1)) + b) + ((nScan + b) + 1) = tBody q := by
        dsimp [tBody, nScan, mRem]; omega
      rw [← hTimeIter]
      exact ((rEr2.seq rScanU).seq rCont).seq rRet)
    (by
      dsimp only [outerInv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte, Nat.sub_self]
      have h0 : -2 * ((0 : ℕ) : Int) = ((0 : ℕ) : Int) := by omega
      rw [oddScratch_zero, h0, unaryTape_lt (by omega : 0 < b)]; rfl)
  rw [applyAct_actStay] at hLoop
  -- Clear `unaryTape b` on Tape 1 and rewind Tape 0 from `d * b` to `0`
  have rClr1 := Runs_clearUnary (w := w) (1 : Fin 2) (outerInv d) b
    (by dsimp only [outerInv]; simp [oddScratch_zero])
    (by dsimp only [outerInv]; simp)
  let mAfterClr : Mem 2 WorkSym :=
    { outerInv d with work := fun i p => if i = 1 then .blank else (outerInv d).work i p }
  have hClrEq : { outerInv d with work := fun i p => if i = 1 then .blank else (outerInv d).work i p } =
      mAfterClr := rfl
  rw [hClrEq] at rClr1
  have rRew0 := Runs_rewindFromEnd (w := w) (0 : Fin 2) mAfterClr (d * b)
    (by dsimp only [mAfterClr, outerInv]; simp)
    (fun j hj => by dsimp only [mAfterClr, outerInv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]; exact tplPrefix_nonblank hj)
    (by dsimp only [mAfterClr, outerInv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]; exact tplPrefix_outside (Or.inl (by omega)))
  have hFinalEq :
      { mAfterClr with workPos := fun i => if i = 0 then 0 else mAfterClr.workPos i } =
      { m with
        work    := fun i p => if i = 0 then tplPrefix (d * b) b 0 p else .blank
        workPos := fun _ => 0 } := by
    refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
    · dsimp only [mAfterClr, outerInv]; fin_cases i <;> simp
    · dsimp only [mAfterClr, outerInv]; fin_cases i <;> simp
  rw [hFinalEq] at rRew0
  have hAll := ((hWalk.seq hLoop).seq rClr1).seq rRew0
  refine ⟨_, ?_, hAll⟩
  have hSumLe := natSum_le_of_step (f := fun q => 1 + tBody q)
    (g := fun q => q * (4 * d + 2 * b + 4)) (N := d)
    (fun q hq => by
      dsimp only [tBody]
      have : d - 1 - q ≤ d := by omega
      nlinarith)
  nlinarith

private theorem tplPrefix_save_lt {len b s j : ℕ} (hj : j < s) (hs : s ≤ len) :
    tplPrefix len b s (j : Int) = .save := by
  unfold tplPrefix
  have h1 : 0 ≤ (j : Int) ∧ (j : Int) < (len : Int) := by omega
  have h2 : (j : Int) < (s : Int) := by omega
  rw [ite_eq_left h1, ite_eq_left h2]

private theorem tplPrefix_emitStart_at {d b r : ℕ} (hr : r < d) (hb1 : 1 ≤ b) :
    tplPrefix (d * b) b (r * b) ((r * b : ℕ) : Int) = .emitStart := by
  unfold tplPrefix
  have hrb_lt : r * b < d * b := by
    calc r * b < r * b + b := by omega
      _ = (r + 1) * b := by ring
      _ ≤ d * b := Nat.mul_le_mul_right b (by omega)
  have h1 : 0 ≤ ((r * b : ℕ) : Int) ∧ ((r * b : ℕ) : Int) < ((d * b : ℕ) : Int) := by omega
  have h2 : ¬ (((r * b : ℕ) : Int) < ((r * b : ℕ) : Int)) := by omega
  rw [ite_eq_left h1, ite_eq_right h2, Int.toNat_natCast, ite_eq_left (Nat.mul_mod_left r b)]

private theorem tplPrefix_emitCont_at {d b r t : ℕ} (hr : r < d) (ht : t < b - 1) :
    tplPrefix (d * b) b (r * b + 1 + t) ((r * b + 1 + t : ℕ) : Int) = .emitCont := by
  unfold tplPrefix
  have hlt : r * b + 1 + t < d * b := by
    have : r * b + 1 + t < (r + 1) * b := by ring_nf; omega
    have : (r + 1) * b ≤ d * b := Nat.mul_le_mul_right b (by omega)
    omega
  have h1 : 0 ≤ ((r * b + 1 + t : ℕ) : Int) ∧
      ((r * b + 1 + t : ℕ) : Int) < ((d * b : ℕ) : Int) := by omega
  have h2 : ¬ (((r * b + 1 + t : ℕ) : Int) < ((r * b + 1 + t : ℕ) : Int)) := by omega
  have hmod : (r * b + 1 + t) % b ≠ 0 := by
    have heq : r * b + 1 + t = (1 + t) + r * b := by ring
    rw [heq, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega : 1 + t < b)]
    omega
  rw [ite_eq_left h1, ite_eq_right h2, Int.toNat_natCast, ite_eq_right hmod]

private theorem tplPrefix_not_emitCont_boundary {d b r : ℕ} :
    (tplPrefix (d * b) b ((r + 1) * b) (((r + 1) * b : ℕ) : Int) == .emitCont) = false := by
  unfold tplPrefix
  by_cases h1 : 0 ≤ (((r + 1) * b : ℕ) : Int) ∧
      (((r + 1) * b : ℕ) : Int) < ((d * b : ℕ) : Int)
  · rw [ite_eq_left h1]
    have h2 : ¬ ((((r + 1) * b : ℕ) : Int) < (((r + 1) * b : ℕ) : Int)) := by omega
    rw [ite_eq_right h2, Int.toNat_natCast, ite_eq_left (Nat.mul_mod_left (r + 1) b)]
    rfl
  · rw [ite_eq_right h1]; rfl

private theorem encode_get_triple {d b : ℕ} (A : Matrix) {r c t : ℕ}
    (hr : r < d) (hc : c < d) (ht : t < b) :
    (encode d b A)[(r * d + c) * b + t]? = some (A r c t) := by
  have hlt : (r * d + c) * b + t < d * d * b := by
    have h1 : r * d + c < d * d := by
      calc r * d + c < r * d + d := by omega
        _ = (r + 1) * d := by ring
        _ ≤ d * d := Nat.mul_le_mul_right d (by omega)
    calc (r * d + c) * b + t < (r * d + c) * b + b := by omega
      _ = (r * d + c + 1) * b := by ring
      _ ≤ (d * d) * b := Nat.mul_le_mul_right b (by omega)
  rw [(encode_len_get d b A).2 _ hlt]
  have heq : (r * d + c) * b + t = r * (d * b) + (c * b + t) := by ring
  have hcb : c * b + t < d * b := by
    calc c * b + t < c * b + b := by omega
      _ = (c + 1) * b := by ring
      _ ≤ d * b := Nat.mul_le_mul_right b (by omega)
  obtain ⟨hd1, hm1⟩ := mul_add_div_mod_tm hcb
  obtain ⟨hd2, hm2⟩ := mul_add_div_mod_tm ht
  rw [heq, hd1, hm1, hd2, hm2]

private theorem rowShear_bit_first {d : ℕ} (A : Matrix) {r k : ℕ}
    (hr : r < d) (hk : k < (d - r) * entryBits d) :
    let b := entryBits d
    (encode d b (rowShearMatrix d A))[r * d * b + k]? =
      (encode d b A)[r * d * b + r * b + k]? := by
  intro b
  have hk' : k < (d - r) * b := hk
  have hbPos : 0 < b := entryBits_pos_tm d
  set c := k / b
  set t := k % b
  have hkt : k = c * b + t := by
    have := Nat.div_add_mod k b; dsimp [c, t]; linarith
  have ht_lt : t < b := Nat.mod_lt k hbPos
  have hc_lt_dr : c < d - r := by
    by_contra hge
    have : (d - r) * b ≤ c * b := Nat.mul_le_mul_right b (Nat.le_of_not_gt hge)
    linarith
  have hc_lt : c < d := by omega
  have hcr_lt : c + r < d := by omega
  have hmod : (c + r) % d = c + r := Nat.mod_eq_of_lt hcr_lt
  have hidx1 : r * d * b + k = (r * d + c) * b + t := by rw [hkt]; ring
  have hidx2 : r * d * b + r * b + k = (r * d + (c + r)) * b + t := by rw [hkt]; ring
  rw [hidx1, hidx2, encode_get_triple (rowShearMatrix d A) hr hc_lt ht_lt,
    encode_get_triple A hr hcr_lt ht_lt]
  unfold rowShearMatrix
  rw [hmod]

private theorem rowShear_bit_wrap {d : ℕ} (A : Matrix) {r j : ℕ}
    (hr : r < d) (hj : j < r * entryBits d) :
    let b := entryBits d
    (encode d b (rowShearMatrix d A))[r * d * b + (d - r) * b + j]? =
      (encode d b A)[r * d * b + j]? := by
  intro b
  have hj' : j < r * b := hj
  have hbPos : 0 < b := entryBits_pos_tm d
  set q := j / b
  set t := j % b
  have hjt : j = q * b + t := by
    have := Nat.div_add_mod j b; dsimp [q, t]; linarith
  have ht_lt : t < b := Nat.mod_lt j hbPos
  have hq_lt : q < r := by
    by_contra hge
    have : r * b ≤ q * b := Nat.mul_le_mul_right b (Nat.le_of_not_gt hge)
    linarith
  set c := d - r + q
  have hc_lt : c < d := by omega
  have hcr : c + r = q + d := by dsimp [c]; omega
  have hmod : (c + r) % d = q := by
    rw [hcr, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : q < d)]
  have hidx1 : r * d * b + (d - r) * b + j = (r * d + c) * b + t := by
    rw [hjt]; dsimp [c]; ring
  have hidx2 : r * d * b + j = (r * d + q) * b + t := by rw [hjt]; ring
  rw [hidx1, hidx2, encode_get_triple (rowShearMatrix d A) hr hc_lt ht_lt,
    encode_get_triple A hr (by omega : q < d) ht_lt]
  unfold rowShearMatrix
  rw [hmod]

private def shearSaveAct : Action 2 WorkSym :=
  mkAct2 0 1 (fun _ _ _ => .right)
    (fun _ s₀ _ => (s₀, .right))
    (fun inp _ _ => (bitSym (inp.getD false), .right))
    (fun _ _ _ => none)

private def shearEmitFlipAct : Action 2 WorkSym :=
  mkAct1 0 (fun _ _ => .right) (fun _ _ => (.save, .right)) (fun inp _ => inp)

private def shearEmitKeepAct : Action 2 WorkSym :=
  mkAct1 0 (fun _ _ => .right) (fun _ s₀ => (s₀, .right)) (fun inp _ => inp)

private def shearEmitSavedAct : Action 2 WorkSym :=
  mkAct1 1 (fun _ _ => .stay) (fun _ s₁ => (s₁, .right)) (fun _ s₁ => symBit s₁)

private def shearRowBody : Block 2 WorkSym :=
  ((((((Block.while1 (fun _ sc => sc 0 == .save) shearSaveAct shearEmitFlipAct).seq
    (Block.while1 (fun _ sc => sc 0 == .emitCont) shearEmitFlipAct actStay)).seq
    (Block.while1 (fun _ sc => sc 0 != .blank) shearEmitKeepAct actStay)).seq
    (rewindFromEnd 0)).seq
    (rewindFromEnd 1)).seq
    (Block.while1 (fun _ sc => sc 1 != .blank) shearEmitSavedAct actStay)).seq
    (eraseFromEnd 1)

private def streamRowShear : Block 2 WorkSym :=
  Block.loop (fun inp _ => inp.isSome) actStay actStay shearRowBody

private theorem Runs_streamRowShear {d : ℕ} (hd1 : 1 ≤ d) (A : Matrix)
    (m : Mem 2 WorkSym) :
    let b := entryBits d
    let w := encode d b A
    let out := encode d b (rowShearMatrix d A)
    m.inPos = 0 →
    m.work 0 = tplPrefix (d * b) b 0 → m.workPos 0 = 0 →
    m.work 1 = (fun _ => .blank) → m.workPos 1 = 0 →
    m.outRev = [] →
    ∃ (t : ℕ) (mHalt : Mem 2 WorkSym),
      t ≤ 5 * d * d * b + 10 * d + 1 ∧
      Runs streamRowShear w m mHalt t ∧
      mHalt.outRev.reverse = out := by
  intro b w out hIn hT0 hP0 hB1 hP1 hOut0
  unfold streamRowShear
  have hb1 : 1 ≤ b := entryBits_pos_tm d
  have hwLen : w.length = d * d * b := (encode_len_get d b A).1
  have houtLen : out.length = d * d * b := (encode_len_get d b (rowShearMatrix d A)).1
  let rowInv (r : ℕ) : Mem 2 WorkSym :=
    { inPos   := ((r * d * b : ℕ) : Int)
      work    := fun i p => if i = 0 then tplPrefix (d * b) b (r * b) p else .blank
      workPos := fun _ => 0
      outRev  := (out.take (r * d * b)).reverse }
  have hRow0 : rowInv 0 = m := by
    refine Mem.eq_of_fields ?_ (fun i p => ?_) (fun i => ?_) ?_
    · dsimp only [rowInv]; simp [hIn]
    · dsimp only [rowInv]; fin_cases i <;> simp [hT0, hB1]
    · dsimp only [rowInv]; fin_cases i <;> simp [hP0, hP1]
    · dsimp only [rowInv]; simp [hOut0]
  let tRow (r : ℕ) : ℕ := 2 * d * b + 3 * r * b + 9
  have hLoop := Runs.loop_sum (w := w)
    (fun inp (_ : Fin 2 → WorkSym) => inp.isSome)
    actStay actStay shearRowBody d tRow rowInv
    (fun r hr => by
      have hrdb_lt : r * d * b < w.length := by
        have h1 : (r + 1) * (d * b) ≤ d * (d * b) := Nat.mul_le_mul_right (d * b) (by omega)
        have h2 : 0 < d * b := Nat.mul_pos (by omega) hb1
        nlinarith
      have hCond : (readInput w (rowInv r).inPos).isSome = true := by
        dsimp only [rowInv]
        rw [readInput_of_nonneg, List.getElem?_eq_getElem hrdb_lt]; rfl
      refine ⟨hCond, ?_⟩
      rw [applyAct_actStay]
      unfold shearRowBody
      set wRow := w.drop (r * d * b)
      have hwRowGet : ∀ idx (hlt : r * d * b + idx < w.length), wRow[idx]? = some w[r * d * b + idx] := by
        intro idx hlt
        dsimp only [wRow]
        rw [List.getElem?_drop, List.getElem?_eq_getElem hlt]
      -- Phase 1: save `r * b` prefix bits onto Tape 1, then on exit emit bit `0` of `A r r`
      let p1Inv (j : ℕ) : Mem 2 WorkSym :=
        { inPos   := ((r * d * b + j : ℕ) : Int)
          work    := fun i p =>
            if i = 0 then tplPrefix (d * b) b (r * b) p
            else wordTape (wRow.take j) p
          workPos := fun _ => (j : Int)
          outRev  := (out.take (r * d * b)).reverse }
      have hP1_0 : p1Inv 0 = rowInv r := by
        refine Mem.eq_of_fields rfl (fun i p => ?_) (fun _ => rfl) rfl
        dsimp only [p1Inv, rowInv]
        fin_cases i <;> simp [wordTape_nil]
      have rP1 := Runs.while1 (w := w)
        (fun _ (sc : Fin 2 → WorkSym) => sc 0 == .save)
        shearSaveAct shearEmitFlipAct (r * b) p1Inv
        (fun j hj => by
          have hrb_le : r * b ≤ d * b := Nat.mul_le_mul_right b (by omega)
          have hcell : ((p1Inv j).work 0 ((p1Inv j).workPos 0) == .save) = true := by
            dsimp only [p1Inv]; simp only [Fin.isValue, ↓reduceIte]
            rw [tplPrefix_save_lt hj hrb_le]; rfl
          refine ⟨hcell, ?_⟩
          have hj_lt_w : r * d * b + j < w.length := by
            have : r * d * b + j < r * d * b + d * b := by omega
            have : (r + 1) * d * b ≤ d * d * b :=
              Nat.mul_le_mul_right b (Nat.mul_le_mul_right d (by omega))
            nlinarith
          have hwGet : w[r * d * b + j]? = some w[r * d * b + j] := List.getElem?_eq_getElem hj_lt_w
          have hDropGet : wRow[j]? = some w[r * d * b + j] := hwRowGet j hj_lt_w
          unfold shearSaveAct; rw [applyAct_mkAct2 w _ (by decide : (0 : Fin 2) ≠ 1)]
          refine Mem.eq_of_fields ?_ (fun i p => ?_) (fun i => ?_) rfl
          · dsimp only [p1Inv, Dir.shift]; omega
          · dsimp only [p1Inv]
            fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]
            · exact congrFun (ite_self_cell (tplPrefix (d * b) b (r * b)) _) p
            · rw [readInput_of_nonneg, hwGet]; dsimp only [Option.getD]
              exact congrFun (wordTape_take_succ hDropGet) p
          · dsimp only [p1Inv, Dir.shift]
            fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte] <;> omega)
        (by
          dsimp only [p1Inv]; simp only [Fin.isValue, ↓reduceIte]
          rw [tplPrefix_emitStart_at hr hb1]; rfl)
      -- Phase 2 invariant (`t = 0 .. b - 1`)
      let savedTape := wordTape (wRow.take (r * b))
      let p2Inv (t : ℕ) : Mem 2 WorkSym :=
        { inPos   := ((r * d * b + r * b + 1 + t : ℕ) : Int)
          work    := fun i p =>
            if i = 0 then tplPrefix (d * b) b (r * b + 1 + t) p
            else savedTape p
          workPos := fun i =>
            if i = 0 then ((r * b + 1 + t : ℕ) : Int)
            else ((r * b : ℕ) : Int)
          outRev  := (out.take (r * d * b + 1 + t)).reverse }
      have hP1Exit : applyAct w shearEmitFlipAct (p1Inv (r * b)) = p2Inv 0 := by
        have hrb_lt : r * b < d * b := by
          calc r * b < r * b + b := by omega
            _ = (r + 1) * b := by ring
            _ ≤ d * b := Nat.mul_le_mul_right b (by omega)
        have hwLt : r * d * b + r * b < w.length := by
          have : (r + 1) * d * b ≤ d * d * b :=
            Nat.mul_le_mul_right b (Nat.mul_le_mul_right d (by omega))
          nlinarith
        have hOutBit : out[r * d * b]? = some w[r * d * b + r * b] := by
          have h := rowShear_bit_first A hr (k := 0) (by
            have : 1 ≤ d - r := by omega
            exact Nat.mul_pos this hb1)
          change out[r * d * b + 0]? = w[r * d * b + r * b + 0]? at h
          rw [Nat.add_zero, Nat.add_zero] at h
          rw [h, List.getElem?_eq_getElem hwLt]
        unfold shearEmitFlipAct; rw [applyAct_mkAct1]
        refine Mem.eq_of_fields ?_ (fun i p => ?_) (fun i => ?_) ?_
        · dsimp only [p1Inv, p2Inv, Dir.shift]; omega
        · dsimp only [p1Inv, p2Inv, savedTape, Nat.add_zero]
          fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]
          exact congrFun (tplPrefix_write_save hrb_lt) p
        · dsimp only [p1Inv, p2Inv, Dir.shift]
          fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]; omega
        · dsimp only [p1Inv, p2Inv, Nat.add_zero]
          rw [readInput_of_nonneg, List.getElem?_eq_getElem hwLt]
          have htk := take_succ_of_getElem?_tm hOutBit
          rw [htk, List.reverse_append, List.reverse_singleton]; rfl
      rw [hP1_0, hP1Exit] at rP1
      -- Phase 2: emit remaining `b - 1` bits of `A r r` while flipping `.emitCont → .save`
      have rP2 := Runs.while1 (w := w)
        (fun _ (sc : Fin 2 → WorkSym) => sc 0 == .emitCont)
        shearEmitFlipAct actStay (b - 1) p2Inv
        (fun t ht => by
          have hcell : ((p2Inv t).work 0 ((p2Inv t).workPos 0) == .emitCont) = true := by
            dsimp only [p2Inv]; simp only [Fin.isValue, ↓reduceIte]
            rw [tplPrefix_emitCont_at hr ht]; rfl
          refine ⟨hcell, ?_⟩
          have hk_lt_dr : 1 + t < (d - r) * b := by
            have : 1 ≤ d - r := by omega
            have : b ≤ (d - r) * b := Nat.le_mul_of_pos_left b this
            omega
          have hpos_lt : r * b + 1 + t < d * b := by
            have : r * b + (d - r) * b = d * b := by
              rw [← Nat.add_mul, Nat.add_sub_of_le (by omega : r ≤ d)]
            omega
          have hwLt : r * d * b + r * b + 1 + t < w.length := by
            have : (r + 1) * d * b ≤ d * d * b :=
              Nat.mul_le_mul_right b (Nat.mul_le_mul_right d (by omega))
            nlinarith
          have hOutBit : out[r * d * b + (1 + t)]? = some w[r * d * b + r * b + 1 + t] := by
            have h := rowShear_bit_first A hr hk_lt_dr
            change out[r * d * b + (1 + t)]? = w[r * d * b + r * b + (1 + t)]? at h
            have heq : r * d * b + r * b + (1 + t) = r * d * b + r * b + 1 + t := by omega
            rw [heq, List.getElem?_eq_getElem hwLt] at h; exact h
          unfold shearEmitFlipAct; rw [applyAct_mkAct1]
          refine Mem.eq_of_fields ?_ (fun i p => ?_) (fun i => ?_) ?_
          · dsimp only [p2Inv, Dir.shift]; omega
          · dsimp only [p2Inv]
            fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]
            have hadd : r * b + 1 + (t + 1) = (r * b + 1 + t) + 1 := by omega
            rw [hadd]
            exact congrFun (tplPrefix_write_save hpos_lt) p
          · dsimp only [p2Inv, Dir.shift]
            fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]; omega
          · dsimp only [p2Inv]
            rw [readInput_of_nonneg, List.getElem?_eq_getElem hwLt]
            have htk := take_succ_of_getElem?_tm hOutBit
            have hidx1 : r * d * b + 1 + (t + 1) = r * d * b + (1 + t) + 1 := by omega
            have hidx2 : r * d * b + (1 + t) = r * d * b + 1 + t := by omega
            rw [hidx1, htk, hidx2, List.reverse_append, List.reverse_singleton]; rfl)
        (by
          dsimp only [p2Inv]; simp only [Fin.isValue, ↓reduceIte]
          have hrb1 : r * b + 1 + (b - 1) = (r + 1) * b := by
            have : 1 + (b - 1) = b := by omega
            calc r * b + 1 + (b - 1) = r * b + (1 + (b - 1)) := by omega
              _ = r * b + b := by rw [this]
              _ = (r + 1) * b := by ring
          rw [hrb1]
          exact tplPrefix_not_emitCont_boundary)
      rw [applyAct_actStay] at rP2
      have hTime2 : (b - 1) + 1 = b := by omega
      rw [hTime2] at rP2
      -- Phase 3: emit remaining `(d - 1 - r) * b` bits while scanning `[(r + 1) * b, d * b)`
      let p3Inv (j : ℕ) : Mem 2 WorkSym :=
        { inPos   := ((r * d * b + (r + 1) * b + j : ℕ) : Int)
          work    := fun i p =>
            if i = 0 then tplPrefix (d * b) b ((r + 1) * b) p
            else savedTape p
          workPos := fun i =>
            if i = 0 then (((r + 1) * b + j : ℕ) : Int)
            else ((r * b : ℕ) : Int)
          outRev  := (out.take (r * d * b + b + j)).reverse }
      have hP2End : p2Inv (b - 1) = p3Inv 0 := by
        have hrb1 : r * b + 1 + (b - 1) = (r + 1) * b := by
          have : 1 + (b - 1) = b := by omega
          calc r * b + 1 + (b - 1) = r * b + (1 + (b - 1)) := by omega
            _ = r * b + b := by rw [this]
            _ = (r + 1) * b := by ring
        refine Mem.eq_of_fields ?_ (fun i p => ?_) (fun i => ?_) ?_
        · dsimp only [p2Inv, p3Inv]; omega
        · dsimp only [p2Inv, p3Inv]; fin_cases i <;> simp [hrb1]
        · dsimp only [p2Inv, p3Inv]; fin_cases i <;> simp [hrb1]
        · dsimp only [p2Inv, p3Inv]
          have : r * d * b + 1 + (b - 1) = r * d * b + b + 0 := by omega
          rw [this]
      rw [hP2End] at rP2
      have rP3 := Runs.while1 (w := w)
        (fun _ (sc : Fin 2 → WorkSym) => sc 0 != .blank)
        shearEmitKeepAct actStay ((d - 1 - r) * b) p3Inv
        (fun j hj => by
          have hpos_lt : (r + 1) * b + j < d * b := by
            have : (r + 1) + (d - 1 - r) = d := by omega
            calc (r + 1) * b + j < (r + 1) * b + (d - 1 - r) * b := by omega
              _ = ((r + 1) + (d - 1 - r)) * b := by ring
              _ = d * b := by rw [this]
          have hneB : (p3Inv j).work 0 ((p3Inv j).workPos 0) ≠ .blank := by
            dsimp only [p3Inv]; simp only [Fin.isValue, ↓reduceIte]
            exact tplPrefix_nonblank hpos_lt
          refine ⟨bne_blank_of_ne hneB, ?_⟩
          have hk_lt_dr : b + j < (d - r) * b := by
            have : 1 + (d - 1 - r) = d - r := by omega
            calc b + j < 1 * b + (d - 1 - r) * b := by omega
              _ = (1 + (d - 1 - r)) * b := by ring
              _ = (d - r) * b := by rw [this]
          have hwLt : r * d * b + (r + 1) * b + j < w.length := by
            have : (r + 1) * d * b ≤ d * d * b :=
              Nat.mul_le_mul_right b (Nat.mul_le_mul_right d (by omega))
            nlinarith
          have hOutBit : out[r * d * b + (b + j)]? = some w[r * d * b + (r + 1) * b + j] := by
            have h := rowShear_bit_first A hr hk_lt_dr
            change out[r * d * b + (b + j)]? = w[r * d * b + r * b + (b + j)]? at h
            have heq : r * d * b + r * b + (b + j) = r * d * b + (r + 1) * b + j := by ring
            rw [heq, List.getElem?_eq_getElem hwLt] at h; exact h
          unfold shearEmitKeepAct; rw [applyAct_mkAct1]
          refine Mem.eq_of_fields ?_ (fun i p => ?_) (fun i => ?_) ?_
          · dsimp only [p3Inv, Dir.shift]; omega
          · dsimp only [p3Inv]
            fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]
            exact congrFun (ite_self_cell (tplPrefix (d * b) b ((r + 1) * b)) _) p
          · dsimp only [p3Inv, Dir.shift]
            fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]; omega
          · dsimp only [p3Inv]
            rw [readInput_of_nonneg, List.getElem?_eq_getElem hwLt]
            have htk := take_succ_of_getElem?_tm hOutBit
            have hidx1 : r * d * b + b + (j + 1) = r * d * b + (b + j) + 1 := by omega
            have hidx2 : r * d * b + (b + j) = r * d * b + b + j := by omega
            rw [hidx1, htk, hidx2, List.reverse_append, List.reverse_singleton]; rfl)
        (by
          dsimp only [p3Inv]; simp only [Fin.isValue, ↓reduceIte]
          have hdb : (r + 1) * b + (d - 1 - r) * b = d * b := by
            have : (r + 1) + (d - 1 - r) = d := by omega
            calc (r + 1) * b + (d - 1 - r) * b = ((r + 1) + (d - 1 - r)) * b := by ring
              _ = d * b := by rw [this]
          rw [hdb, tplPrefix_outside (Or.inr le_rfl)]; rfl)
      rw [applyAct_actStay] at rP3
      -- Phase 4: `rewindFromEnd 0` (`d * b + 2` steps) + `rewindFromEnd 1` (`r * b + 2` steps)
      have hdbEq : (r + 1) * b + (d - 1 - r) * b = d * b := by
        have : (r + 1) + (d - 1 - r) = d := by omega
        calc (r + 1) * b + (d - 1 - r) * b = ((r + 1) + (d - 1 - r)) * b := by ring
          _ = d * b := by rw [this]
      have rRew0 := Runs_rewindFromEnd (w := w) (0 : Fin 2) (p3Inv ((d - 1 - r) * b)) (d * b)
        (by dsimp only [p3Inv]; simp [hdbEq])
        (fun j hj => by dsimp only [p3Inv]; simp only [Fin.isValue, ↓reduceIte]; exact tplPrefix_nonblank hj)
        (by dsimp only [p3Inv]; simp only [Fin.isValue, ↓reduceIte]; exact tplPrefix_outside (Or.inl (by omega)))
      let mAfterR0 : Mem 2 WorkSym :=
        { p3Inv ((d - 1 - r) * b) with
          workPos := fun i => if i = 0 then 0 else (p3Inv ((d - 1 - r) * b)).workPos i }
      have hR0Eq :
          { p3Inv ((d - 1 - r) * b) with
            workPos := fun i => if i = 0 then 0 else (p3Inv ((d - 1 - r) * b)).workPos i } =
          mAfterR0 := rfl
      rw [hR0Eq] at rRew0
      have hwRowTakeLen : (wRow.take (r * b)).length = r * b := by
        dsimp only [wRow]
        rw [List.length_take_of_le]
        rw [List.length_drop, hwLen]
        have h1 : r * d * b + d * b ≤ d * d * b := by
          have : (r + 1) * d * b ≤ d * d * b :=
            Nat.mul_le_mul_right b (Nat.mul_le_mul_right d (by omega))
          linarith
        have h2 : r * b ≤ d * b := Nat.mul_le_mul_right b (by omega)
        omega
      have rRew1 := Runs_rewindFromEnd (w := w) (1 : Fin 2) mAfterR0 (r * b)
        (by dsimp only [mAfterR0, p3Inv]; simp)
        (fun j hj => by
          dsimp only [mAfterR0, p3Inv, savedTape]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
          have hjLen : j < (wRow.take (r * b)).length := by omega
          rw [wordTape_lt (List.getElem?_eq_getElem hjLen)]
          exact bitSym_ne_blank _)
        (by
          dsimp only [mAfterR0, p3Inv, savedTape]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
          exact wordTape_neg (by omega))
      -- Phase 5: emit `r * b` saved bits from Tape 1, then `eraseFromEnd 1`
      let p5Inv (j : ℕ) : Mem 2 WorkSym :=
        { inPos   := (((r + 1) * d * b : ℕ) : Int)
          work    := fun i p =>
            if i = 0 then tplPrefix (d * b) b ((r + 1) * b) p
            else savedTape p
          workPos := fun i => if i = 0 then 0 else (j : Int)
          outRev  := (out.take (r * d * b + (d - r) * b + j)).reverse }
      have hR1End :
          { mAfterR0 with workPos := fun i => if i = 1 then 0 else mAfterR0.workPos i } =
          p5Inv 0 := by
        have hinEq : r * d * b + (r + 1) * b + (d - 1 - r) * b = (r + 1) * d * b := by
          rw [Nat.add_assoc, hdbEq]; ring
        have hdrEq : b + (d - 1 - r) * b = (d - r) * b := by
          have : 1 + (d - 1 - r) = d - r := by omega
          calc b + (d - 1 - r) * b = (1 + (d - 1 - r)) * b := by ring
            _ = (d - r) * b := by rw [this]
        refine Mem.eq_of_fields ?_ (fun _ _ => rfl) (fun i => ?_) ?_
        · dsimp only [mAfterR0, p3Inv, p5Inv]; exact congrArg Nat.cast hinEq
        · dsimp only [mAfterR0, p3Inv, p5Inv]; fin_cases i <;> simp
        · dsimp only [mAfterR0, p3Inv, p5Inv, Nat.add_zero]
          rw [Nat.add_assoc (r * d * b), hdrEq]
      rw [hR1End] at rRew1
      have rP5 := Runs.while1 (w := w)
        (fun _ (sc : Fin 2 → WorkSym) => sc 1 != .blank)
        shearEmitSavedAct actStay (r * b) p5Inv
        (fun j hj => by
          have hj_lt_w : r * d * b + j < w.length := by
            have : (r + 1) * d * b ≤ d * d * b :=
              Nat.mul_le_mul_right b (Nat.mul_le_mul_right d (by omega))
            have : r * b ≤ d * b := Nat.mul_le_mul_right b (by omega)
            nlinarith
          have hSavedGet : (wRow.take (r * b))[j]? = some w[r * d * b + j] := by
            rw [List.getElem?_take_of_lt hj, hwRowGet j hj_lt_w]
          have hcell : (p5Inv j).work 1 ((p5Inv j).workPos 1) ≠ .blank := by
            dsimp only [p5Inv, savedTape]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
            rw [wordTape_lt hSavedGet]; exact bitSym_ne_blank _
          refine ⟨bne_blank_of_ne hcell, ?_⟩
          have hOutBit : out[r * d * b + (d - r) * b + j]? = some w[r * d * b + j] := by
            have h := rowShear_bit_wrap A hr hj
            change out[r * d * b + (d - r) * b + j]? = w[r * d * b + j]? at h
            rw [h, List.getElem?_eq_getElem hj_lt_w]
          unfold shearEmitSavedAct; rw [applyAct_mkAct1]
          refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) ?_
          · dsimp only [p5Inv]
            fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]
            exact congrFun (ite_self_cell savedTape _) p
          · dsimp only [p5Inv, Dir.shift]
            fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]; omega
          · dsimp only [p5Inv, savedTape]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
            rw [wordTape_lt hSavedGet, symBit_bitSym]
            have htk := take_succ_of_getElem?_tm hOutBit
            have hidx : r * d * b + (d - r) * b + (j + 1) = (r * d * b + (d - r) * b + j) + 1 := by omega
            rw [hidx, htk, List.reverse_append, List.reverse_singleton]; rfl)
        (by
          dsimp only [p5Inv, savedTape]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
          rw [wordTape_ge (by rw [hwRowTakeLen])]; rfl)
      rw [applyAct_actStay] at rP5
      have rEr1 := Runs_eraseFromEnd (w := w) (1 : Fin 2) (p5Inv (r * b)) (r * b)
        (by dsimp only [p5Inv]; simp)
        (fun j hj => by
          dsimp only [p5Inv, savedTape]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
          have hjLen : j < (wRow.take (r * b)).length := by omega
          rw [wordTape_lt (List.getElem?_eq_getElem hjLen)]
          exact bitSym_ne_blank _)
        (fun p hp => by
          dsimp only [p5Inv, savedTape]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
          rcases hp with hneg | hge
          · exact wordTape_neg hneg
          · exact wordTape_ge (by rw [hwRowTakeLen]; omega))
      have hErEnd :
          { p5Inv (r * b) with
            work    := fun i p => if i = 1 then WorkSym.blank else (p5Inv (r * b)).work i p
            workPos := fun i => if i = 1 then 0 else (p5Inv (r * b)).workPos i } =
          rowInv (r + 1) := by
        have houtIdx : r * d * b + (d - r) * b + r * b = (r + 1) * d * b := by
          have : (d - r) + r = d := Nat.sub_add_cancel (by omega : r ≤ d)
          calc r * d * b + (d - r) * b + r * b
              = r * d * b + ((d - r) + r) * b := by ring
            _ = r * d * b + d * b := by rw [this]
            _ = (r + 1) * d * b := by ring
        refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) ?_
        · dsimp only [p5Inv, rowInv]; fin_cases i <;> simp
        · dsimp only [p5Inv, rowInv]; fin_cases i <;> simp
        · dsimp only [p5Inv, rowInv]; rw [houtIdx]
      rw [hErEnd] at rEr1
      have hRowTime :
          ((((((r * b + 1) + b) + ((d - 1 - r) * b + 1)) + (d * b + 2)) + (r * b + 2)) +
            (r * b + 1)) + (r * b + 2) = tRow r := by
        dsimp only [tRow]
        have : r * b + b + (d - 1 - r) * b = d * b := by
          have hsum : r + 1 + (d - 1 - r) = d := by omega
          calc r * b + b + (d - 1 - r) * b = (r + 1 + (d - 1 - r)) * b := by ring
            _ = d * b := by rw [hsum]
        linarith
      rw [← hRowTime]
      exact (((((rP1.seq rP2).seq rP3).seq rRew0).seq rRew1).seq rP5).seq rEr1)
    (by
      dsimp only [rowInv]
      rw [readInput_of_nonneg, List.getElem?_eq_none (by omega)]; rfl)
  rw [hRow0, applyAct_actStay] at hLoop
  refine ⟨_, rowInv d, ?_, hLoop, ?_⟩
  · have hSumLe := natSum_le_of_step (f := fun r => 1 + tRow r)
      (g := fun r => r * (5 * d * b + 10)) (N := d)
      (fun r hr => by
        dsimp only [tRow]
        have : r * b ≤ d * b := Nat.mul_le_mul_right b (by omega)
        nlinarith)
    nlinarith
  · dsimp only [rowInv]
    rw [List.reverse_reverse, List.take_of_length_le (by omega)]

private def rowShearProg : Block 2 WorkSym :=
  (((((discoverEntryBits 0 1).seq (clearUnary 0)).seq divInputByB).seq
    unarySqrtBlock).seq buildRowTemplate).seq streamRowShear


/-- Explicit `2`-work-tape transition table computing the within-row cyclic shear in `O(L)` time. -/
def rowShearTM : DetTM :=
  rowShearProg.toTM encWorkSym decWorkSym

/-- `rowShearTM` uses `2` work tapes and computes `rowShearMatrix d A` on every `d × d` matrix
(`d ≥ 1`) within `200 * inputLength d` steps. -/
theorem rowShearTM_twoTape_linear :
    rowShearTM.k = 2 ∧
    ∀ (d : ℕ) (A : Matrix), 1 ≤ d →
      ComputesWithin rowShearTM
        (encode d (entryBits d) A)
        (encode d (entryBits d) (rowShearMatrix d A))
        (200 * inputLength d) := by
  refine ⟨rfl, ?_⟩
  intro d A hd1
  unfold rowShearTM
  set b := entryBits d
  set L := inputLength d
  set w := encode d b A
  have hb1 : 1 ≤ b := entryBits_pos_tm d
  have hL_eq : L = d * d * b := rfl
  have hL1 : 1 ≤ L := inputLength_pos hd1
  have hwLen : w.length = L := (encode_len_get d b A).1
  let m0 : Mem 2 WorkSym :=
    { inPos := 0, work := fun _ _ => .blank, workPos := fun _ => 0, outRev := [] }
  -- 1. `discoverEntryBits 0 1`
  have r1 := Runs_discoverEntryBits (k := 2) (t₀ := 0) (t₁ := 1) (by decide) hd1 hwLen
    m0 rfl rfl rfl rfl rfl
  change Runs (discoverEntryBits 0 1) w m0 _ (120 * L) at r1
  let m1 : Mem 2 WorkSym :=
    { m0 with
      work := fun i p => if i = 0 then unaryTape (4 ^ b) p else unaryTape b p }
  have hm1Eq :
      { m0 with
        work := fun i p =>
          if i = 0 then unaryTape (4 ^ b) p
          else if i = 1 then unaryTape b p
          else m0.work i p } = m1 := by
    refine Mem.eq_of_fields rfl (fun i p => ?_) (fun _ => rfl) rfl
    fin_cases i <;> rfl
  rw [hm1Eq] at r1
  -- 2. `clearUnary 0`
  have r2 := Runs_clearUnary (w := w) (0 : Fin 2) m1 (4 ^ b) rfl rfl
  let m2 : Mem 2 WorkSym :=
    { m0 with work := fun i p => if i = 0 then .blank else unaryTape b p }
  have hm2Eq :
      { m1 with work := fun i p => if i = 0 then .blank else m1.work i p } = m2 := by
    refine Mem.eq_of_fields rfl (fun i p => ?_) (fun _ => rfl) rfl
    fin_cases i <;> rfl
  rw [hm2Eq] at r2
  -- 3. `divInputByB` (`Q = d * d`)
  have r3 := Runs_divInputByB (w := w) m2 (d * d) b hb1 hwLen rfl rfl rfl rfl rfl
  let m3 : Mem 2 WorkSym :=
    { m0 with work := fun i p => if i = 0 then unaryTape (d * d) p else unaryTape b p }
  have hm3Eq :
      { m2 with work := fun i p => if i = 0 then unaryTape (d * d) p else m2.work i p } = m3 := by
    refine Mem.eq_of_fields rfl (fun i p => ?_) (fun _ => rfl) rfl
    fin_cases i <;> rfl
  rw [hm3Eq] at r3
  -- 4. `unarySqrtBlock`
  obtain ⟨t4, ht4, r4⟩ := Runs_unarySqrtBlock (w := w) m3 d b hd1 rfl rfl rfl rfl
  let m4 : Mem 2 WorkSym :=
    { m0 with
      work    := fun i p => if i = 0 then .blank else oddScratch b d p
      workPos := fun i => if i = 0 then 0 else -1 }
  have hm4Eq :
      { m3 with
        work    := fun i p => if i = 0 then .blank else oddScratch b d p
        workPos := fun i => if i = 0 then 0 else -1 } = m4 := rfl
  rw [hm4Eq] at r4
  -- 5. `buildRowTemplate`
  obtain ⟨t5, ht5, r5⟩ := Runs_buildRowTemplate (w := w) m4 d b hd1 hb1 rfl rfl rfl rfl
  let m5 : Mem 2 WorkSym :=
    { m0 with
      work    := fun i p => if i = 0 then tplPrefix (d * b) b 0 p else .blank
      workPos := fun _ => 0 }
  have hm5Eq :
      { m4 with
        work    := fun i p => if i = 0 then tplPrefix (d * b) b 0 p else .blank
        workPos := fun _ => 0 } = m5 := rfl
  rw [hm5Eq] at r5
  -- 6. `streamRowShear`
  obtain ⟨t6, mHalt, ht6, r6, hOut⟩ := Runs_streamRowShear hd1 A m5 rfl rfl rfl rfl rfl rfl
  change mHalt.outRev.reverse = encode d b (rowShearMatrix d A) at hOut
  have rTotal : Runs rowShearProg w m0 mHalt (200 * L) := by
    unfold rowShearProg
    apply (((((r1.seq r2).seq r3).seq r4).seq r5).seq r6).of_le
    have h4bL : 4 ^ b * b ≤ 4 * L := entryBits_quad_le_four_L hd1
    have h4b : 4 ^ b ≤ 4 ^ b * b := Nat.le_mul_of_pos_right (4 ^ b) hb1
    have hddL : d * d ≤ L := by dsimp [L, inputLength]; exact Nat.le_mul_of_pos_right (d * d) hb1
    have hd_le_dd : d ≤ d * d := Nat.le_mul_self d
    have hdbL : d * b ≤ L := by
      have : 1 * (d * b) ≤ d * (d * b) := Nat.mul_le_mul_right (d * b) hd1
      dsimp [L, inputLength]; linarith
    have hb_le_db : b ≤ d * b := Nat.le_mul_of_pos_left b hd1
    nlinarith
  exact Block.computesWithin .blank encWorkSym decWorkSym decWorkSym_encWorkSym encWorkSym_blank
    rowShearProg rTotal hOut


end LeanMachine.ShuffleShear
