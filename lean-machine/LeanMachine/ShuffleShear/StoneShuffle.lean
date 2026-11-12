import LeanMachine.ShuffleShear.Model

/-!
# Linear-Time `3`-Work-Tape Turing Machine for Stone's Perfect Shuffle

Constructs an explicit finite transition table `stoneShuffleTM : DetTM` with `k = 3` work tapes
over a `10`-symbol work alphabet (`g = 9`) that computes one pass of Stone's perfect shuffle
`stoneShuffleMatrix m A` on the row-major encoding of any `2^m × 2^m` matrix (`m ≥ 1`) with
`⌈log₂(2^m)⌉`-bit entries within `150 · L` steps (`L = inputLength (2^m)`).
-/

namespace LeanMachine.ShuffleShear

private theorem stoneShuffle_encode_bit {m' : ℕ} (A : Matrix) :
    let m := m' + 1
    let d := 2 ^ m
    let b := entryBits d
    let H := 2 * 4 ^ m'
    ∀ e < 2 * H, ∀ t < b,
      (encode d b (stoneShuffleMatrix m A))[e * b + t]? =
        (encode d b A)[((e % 2) * H + e / 2) * b + t]? := by
  intro m d b H e he t ht
  have hd_eq : d = 2 * 2 ^ m' := by dsimp [d, m]; rw [pow_succ']
  have hdd_eq : d * d = 2 * H := by
    dsimp [H]; rw [hd_eq]
    calc (2 * 2 ^ m') * (2 * 2 ^ m') = 2 * (2 * (2 ^ m' * 2 ^ m')) := by ring
      _ = 2 * (2 * (2 * 2) ^ m') := by rw [Nat.mul_pow 2 2 m']
      _ = 2 * (2 * 4 ^ m') := rfl
  have he_dd : e < d * d := by omega
  have hsrc_lt : (e % 2) * H + e / 2 < d * d := by
    have h1 : e % 2 ≤ 1 := by omega
    have h2 : (e % 2) * H ≤ 1 * H := Nat.mul_le_mul_right H h1
    omega
  rw [encode_entry_bit d b (stoneShuffleMatrix m A) he_dd ht,
      encode_entry_bit d b A hsrc_lt ht]
  congr 1
  set r' := e / d
  set c' := e % d
  have hd_pos : 0 < d := Nat.two_pow_pos m
  have hr'_lt : r' < d := Nat.div_lt_of_lt_mul (by omega)
  have hc'_lt : c' < d := Nat.mod_lt e hd_pos
  have he_decomp : e = r' * d + c' := by
    dsimp [r', c']; rw [Nat.mul_comm, Nat.div_add_mod]
  have hr'2_lt : r' / 2 < 2 ^ m' := by omega
  have hc'2_lt : c' / 2 < 2 ^ m' := by omega
  have hc'mod : c' % 2 ≤ 1 := by omega
  have hr'mod : r' % 2 ≤ 1 := by omega
  have hsrcR_lt : (c' % 2) * 2 ^ m' + r' / 2 < d := by
    have : (c' % 2) * 2 ^ m' ≤ 1 * 2 ^ m' := Nat.mul_le_mul_right _ hc'mod
    omega
  have hsrcC_lt : (r' % 2) * 2 ^ m' + c' / 2 < d := by
    have : (r' % 2) * 2 ^ m' ≤ 1 * 2 ^ m' := Nat.mul_le_mul_right _ hr'mod
    omega
  let srcR := (c' % 2) * 2 ^ m' + r' / 2
  let srcC := (r' % 2) * 2 ^ m' + c' / 2
  have he_mod2 : e % 2 = c' % 2 := by
    calc e % 2 = (r' * (2 * 2 ^ m') + c') % 2 := by rw [← hd_eq, ← he_decomp]
      _ = (c' + 2 * (r' * 2 ^ m')) % 2 := by ring_nf
      _ = c' % 2 := Nat.add_mul_mod_self_left c' 2 (r' * 2 ^ m')
  have he_div2 : e / 2 = r' * 2 ^ m' + c' / 2 := by
    calc e / 2 = (c' + 2 * (r' * 2 ^ m')) / 2 := by
          have : e = c' + 2 * (r' * 2 ^ m') := by rw [he_decomp, hd_eq]; ring
          rw [this]
      _ = c' / 2 + r' * 2 ^ m' := Nat.add_mul_div_left c' (r' * 2 ^ m') (by decide)
      _ = r' * 2 ^ m' + c' / 2 := Nat.add_comm _ _
  have hflat : (e % 2) * H + e / 2 = srcR * d + srcC := by
    have hr'_split : 2 * (r' / 2) + r' % 2 = r' := Nat.div_add_mod r' 2
    have hH_eq : H = 2 ^ m' * d := by
      dsimp [H]; rw [hd_eq]
      calc 2 * 4 ^ m' = 2 * (2 * 2) ^ m' := rfl
        _ = 2 * (2 ^ m' * 2 ^ m') := by rw [Nat.mul_pow 2 2 m']
        _ = 2 ^ m' * (2 * 2 ^ m') := by ring
    rw [he_mod2, he_div2, hH_eq]
    dsimp [srcR, srcC]
    rw [hd_eq]
    nlinarith [hr'_split]
  obtain ⟨hdiv_src, hmod_src⟩ := mul_add_div_mod_tm hsrcC_lt
  rw [hflat, hdiv_src, hmod_src]
  change A ((c' % 2 * 2 ^ m' + r' / 2) % d) ((r' % 2 * 2 ^ m' + c' / 2) % d) t =
    A srcR srcC t
  rw [Nat.mod_eq_of_lt hsrcR_lt, Nat.mod_eq_of_lt hsrcC_lt]


private def halveEnterAct : Action 3 WorkSym :=
  mkAct2 0 2 (fun _ _ _ => .stay)
    (fun _ s₀ _ => (s₀, .right)) (fun _ _ _ => (.u, .right)) (fun _ _ _ => none)

private def halveUnaryBlock : Block 3 WorkSym :=
  ((Block.loop (fun _ sc => sc 0 == .u)
    halveEnterAct actStay (Block.act (stepDirAct 0 .right))).seq
    (eraseFromEnd 0)).seq
    (rewindFromEnd 2)

private theorem Runs_halveUnaryBlock {w : List Bool} (m : Mem 3 WorkSym) (H : ℕ)
    (hT0 : m.work 0 = unaryTape (2 * H)) (hP0 : m.workPos 0 = 0)
    (hB2 : m.work 2 = fun _ => .blank) (hP2 : m.workPos 2 = 0) :
    Runs halveUnaryBlock w m
      { m with
        work := fun i p =>
          if i = 0 then .blank
          else if i = 2 then unaryTape H p
          else m.work i p }
      (5 * H + 5) := by
  unfold halveUnaryBlock
  let inv (j : ℕ) : Mem 3 WorkSym :=
    { m with
      work    := fun i p => if i = 2 then unaryTape j p else m.work i p
      workPos := fun i =>
        if i = 0 then ((2 * j : ℕ) : Int)
        else if i = 2 then (j : Int)
        else m.workPos i }
  have hInv0 : inv 0 = m := by
    refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
    · dsimp only [inv]
      by_cases hi : i = 2
      · subst hi; simp only [↓reduceIte, unaryTape_zero, hB2]
      · simp [hi]
    · dsimp only [inv]
      fin_cases i <;> simp [hP0, hP2]
  have hLoop := Runs.loop (w := w)
    (fun _ (sc : Fin 3 → WorkSym) => sc 0 == .u)
    halveEnterAct actStay (Block.act (stepDirAct 0 .right)) 1 H inv
    (fun j hj => by
      have hcell : ((inv j).work 0 ((inv j).workPos 0) == .u) = true := by
        dsimp only [inv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
        rw [hT0, unaryTape_lt (by omega : 2 * j < 2 * H)]; rfl
      refine ⟨hcell, ?_⟩
      let mMid : Mem 3 WorkSym :=
        { m with
          work    := fun i p => if i = 2 then unaryTape (j + 1) p else m.work i p
          workPos := fun i =>
            if i = 0 then ((2 * j + 1 : ℕ) : Int)
            else if i = 2 then ((j + 1 : ℕ) : Int)
            else m.workPos i }
      have hEnt : applyAct w halveEnterAct (inv j) = mMid := by
        unfold halveEnterAct
        rw [applyAct_mkAct2 w (inv j) (by decide : (0 : Fin 3) ≠ 2)]
        refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
        · dsimp only [inv, mMid]
          fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Fin.reduceEq, ↓reduceIte]
          · exact congrFun (ite_self_cell (m.work 0) _) p
          · exact congrFun (unaryTape_write_end j) p
        · dsimp only [inv, mMid, Dir.shift]
          fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Fin.reduceEq, ↓reduceIte] <;> omega
      have hBody : applyAct w (stepDirAct 0 .right) mMid = inv (j + 1) := by
        unfold stepDirAct; rw [applyAct_mkAct1]
        refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
        · dsimp only [mMid, inv]
          fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Fin.reduceEq, ↓reduceIte]
          exact congrFun (ite_self_cell (m.work 0) _) p
        · dsimp only [mMid, inv, Dir.shift]
          fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Fin.reduceEq, ↓reduceIte]; omega
      rw [hEnt, ← hBody]; exact Runs.act _ _)
    (by
      dsimp only [inv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
      rw [hT0, unaryTape_ge le_rfl]; rfl)
  rw [hInv0, applyAct_actStay] at hLoop
  have hEr0 := Runs_eraseFromEnd (w := w) (0 : Fin 3) (inv H) (2 * H)
    (by dsimp only [inv]; simp)
    (fun j hj => by dsimp only [inv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]; rw [hT0, unaryTape_lt hj]; decide)
    (fun p hp => by
      dsimp only [inv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]; rw [hT0]
      rcases hp with hneg | hge
      · exact unaryTape_neg hneg
      · exact unaryTape_ge hge)
  let mAfterEr : Mem 3 WorkSym :=
    { inv H with
      work    := fun i p => if i = 0 then WorkSym.blank else (inv H).work i p
      workPos := fun i => if i = 0 then 0 else (inv H).workPos i }
  have hErEq : { inv H with
      work    := fun i p => if i = 0 then WorkSym.blank else (inv H).work i p
      workPos := fun i => if i = 0 then 0 else (inv H).workPos i } = mAfterEr := rfl
  rw [hErEq] at hEr0
  have hRew2 := Runs_rewindFromEnd (w := w) (2 : Fin 3) mAfterEr H
    (by dsimp only [mAfterEr, inv]; simp)
    (fun j hj => by dsimp only [mAfterEr, inv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]; rw [unaryTape_lt hj]; decide)
    (by dsimp only [mAfterEr, inv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]; exact unaryTape_neg (by omega))
  have hEnd : { mAfterEr with workPos := fun i => if i = 2 then 0 else mAfterEr.workPos i } =
      { m with
        work := fun i p =>
          if i = 0 then .blank
          else if i = 2 then unaryTape H p
          else m.work i p } := by
    refine Mem.eq_of_fields rfl (fun _ _ => rfl) (fun i => ?_) rfl
    dsimp only [mAfterEr, inv]
    fin_cases i <;> simp [hP0, hP2]
  rw [hEnd] at hRew2
  have hTime : ((H * (1 + 1) + 1) + (2 * H + 2)) + (H + 2) = 5 * H + 5 := by ring
  rw [← hTime]
  exact (hLoop.seq hEr0).seq hRew2

private def copyBitAct3 : Action 3 WorkSym :=
  mkAct2 0 1 (fun _ _ _ => .right)
    (fun inp _ _ => (bitSym (inp.getD false), .right))
    (fun _ _ s₁ => (s₁, .right))
    (fun _ _ _ => none)

private def copyHalfToTape0Block : Block 3 WorkSym :=
  ((Block.loop (fun _ sc => sc 2 == .u)
    (stepDirAct 2 .right) actStay
    ((Block.while1 (fun _ sc => sc 1 == .u) copyBitAct3 actStay).seq
      (rewindFromEnd 1))).seq
    (rewindFromEnd 0)).seq
    (rewindFromEnd 2)

private theorem Runs_copyHalfToTape0Block {w : List Bool} (m : Mem 3 WorkSym) (H b : ℕ)
    (hwLen : 2 * H * b ≤ w.length)
    (hIn : m.inPos = 0)
    (hB0 : m.work 0 = fun _ => .blank) (hP0 : m.workPos 0 = 0)
    (hT1 : m.work 1 = unaryTape b) (hP1 : m.workPos 1 = 0)
    (hT2 : m.work 2 = unaryTape H) (hP2 : m.workPos 2 = 0) :
    Runs copyHalfToTape0Block w m
      { m with
        inPos := ((H * b : ℕ) : Int)
        work  := fun i p => if i = 0 then wordTape (w.take (H * b)) p else m.work i p }
      (3 * H * b + 5 * H + 5) := by
  unfold copyHalfToTape0Block
  let outerInv (e : ℕ) : Mem 3 WorkSym :=
    { m with
      inPos   := ((e * b : ℕ) : Int)
      work    := fun i p => if i = 0 then wordTape (w.take (e * b)) p else m.work i p
      workPos := fun i =>
        if i = 0 then ((e * b : ℕ) : Int)
        else if i = 2 then (e : Int)
        else m.workPos i }
  have hOuter0 : outerInv 0 = m := by
    refine Mem.eq_of_fields ?_ (fun i p => ?_) (fun i => ?_) rfl
    · dsimp only [outerInv]; simp [hIn]
    · dsimp only [outerInv]
      fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Fin.reduceEq, ↓reduceIte]
      simp [wordTape_nil, hB0]
    · dsimp only [outerInv]
      fin_cases i <;> simp [hP0, hP1, hP2]
  have hLoop := Runs.loop (w := w)
    (fun _ (sc : Fin 3 → WorkSym) => sc 2 == .u)
    (stepDirAct 2 .right) actStay
    ((Block.while1 (fun _ sc => sc 1 == .u) copyBitAct3 actStay).seq (rewindFromEnd 1))
    (2 * b + 3) H outerInv
    (fun e he => by
      have hcell2 : ((outerInv e).work 2 ((outerInv e).workPos 2) == .u) = true := by
        dsimp only [outerInv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
        rw [hT2, unaryTape_lt he]; rfl
      refine ⟨hcell2, ?_⟩
      let innerInv (t : ℕ) : Mem 3 WorkSym :=
        { m with
          inPos   := ((e * b + t : ℕ) : Int)
          work    := fun i p => if i = 0 then wordTape (w.take (e * b + t)) p else m.work i p
          workPos := fun i =>
            if i = 0 then ((e * b + t : ℕ) : Int)
            else if i = 1 then (t : Int)
            else ((e + 1 : ℕ) : Int) }
      have hEnt : applyAct w (stepDirAct 2 .right) (outerInv e) = innerInv 0 := by
        unfold stepDirAct; rw [applyAct_mkAct1]
        refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
        · dsimp only [outerInv, innerInv]
          fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Fin.reduceEq, ↓reduceIte, Nat.add_zero]
          exact congrFun (ite_self_cell (m.work 2) _) p
        · dsimp only [outerInv, innerInv, Dir.shift]
          fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Fin.reduceEq, ↓reduceIte]
          · rfl
          · exact hP1
          · omega
      rw [hEnt]
      have hW := Runs.while1 (w := w)
        (fun _ (sc : Fin 3 → WorkSym) => sc 1 == .u)
        copyBitAct3 actStay b innerInv
        (fun t ht => by
          have hcell1 : ((innerInv t).work 1 ((innerInv t).workPos 1) == .u) = true := by
            dsimp only [innerInv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
            rw [hT1, unaryTape_lt ht]; rfl
          refine ⟨hcell1, ?_⟩
          have hIdxLt : e * b + t < w.length := by
            have : e * b + t < (e + 1) * b := by ring_nf; omega
            have : (e + 1) * b ≤ 2 * H * b := Nat.mul_le_mul_right b (by omega)
            omega
          have hGet : w[e * b + t]? = some w[e * b + t] := List.getElem?_eq_getElem hIdxLt
          unfold copyBitAct3
          rw [applyAct_mkAct2 w (innerInv t) (by decide : (0 : Fin 3) ≠ 1)]
          refine Mem.eq_of_fields ?_ (fun i p => ?_) (fun i => ?_) rfl
          · dsimp only [innerInv, Dir.shift]; omega
          · dsimp only [innerInv]
            fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Fin.reduceEq, ↓reduceIte]
            · rw [readInput_of_nonneg, hGet]
              dsimp only [Option.getD]
              exact congrFun (wordTape_take_succ hGet) p
            · exact congrFun (ite_self_cell (m.work 1) _) p
          · dsimp only [innerInv, Dir.shift]
            fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Fin.reduceEq, ↓reduceIte] <;> omega)
        (by
          dsimp only [innerInv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
          rw [hT1, unaryTape_ge le_rfl]; rfl)
      rw [applyAct_actStay] at hW
      have hRew1 := Runs_rewindFromEnd (w := w) (1 : Fin 3) (innerInv b) b
        (by dsimp only [innerInv]; simp)
        (fun j hj => by dsimp only [innerInv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]; rw [hT1, unaryTape_lt hj]; decide)
        (by dsimp only [innerInv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]; rw [hT1]; exact unaryTape_neg (by omega))
      have hEndInner : { innerInv b with workPos := fun i => if i = 1 then 0 else (innerInv b).workPos i } =
          outerInv (e + 1) := by
        have hmul : e * b + b = (e + 1) * b := by ring
        refine Mem.eq_of_fields ?_ (fun i p => ?_) (fun i => ?_) rfl
        · dsimp only [innerInv, outerInv]; exact congrArg Nat.cast hmul
        · dsimp only [innerInv, outerInv]
          fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Fin.reduceEq, ↓reduceIte]
          rw [hmul]
        · dsimp only [innerInv, outerInv]
          fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Fin.reduceEq, ↓reduceIte]
          · exact congrArg Nat.cast hmul
          · exact hP1.symm
      rw [hEndInner] at hRew1
      have hTime : (b + 1) + (b + 2) = 2 * b + 3 := by omega
      rw [← hTime]
      exact hW.seq hRew1)
    (by
      dsimp only [outerInv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
      rw [hT2, unaryTape_ge le_rfl]; rfl)
  rw [hOuter0, applyAct_actStay] at hLoop
  have hHbLe : H * b ≤ w.length := by nlinarith
  have hHbLen : (w.take (H * b)).length = H * b := List.length_take_of_le hHbLe
  have hRew0 := Runs_rewindFromEnd (w := w) (0 : Fin 3) (outerInv H) (H * b)
    (by dsimp only [outerInv]; simp)
    (fun j hj => by
      dsimp only [outerInv]; simp only [Fin.isValue, ↓reduceIte]
      have hjLen : j < (w.take (H * b)).length := by omega
      rw [wordTape_lt (List.getElem?_eq_getElem hjLen)]
      exact bitSym_ne_blank _)
    (by dsimp only [outerInv]; simp only [Fin.isValue, ↓reduceIte]; exact wordTape_neg (by omega))
  let mAfter0 : Mem 3 WorkSym :=
    { outerInv H with workPos := fun i => if i = 0 then 0 else (outerInv H).workPos i }
  have hRew0Eq : { outerInv H with workPos := fun i => if i = 0 then 0 else (outerInv H).workPos i } =
      mAfter0 := rfl
  rw [hRew0Eq] at hRew0
  have hRew2 := Runs_rewindFromEnd (w := w) (2 : Fin 3) mAfter0 H
    (by dsimp only [mAfter0, outerInv]; simp)
    (fun j hj => by dsimp only [mAfter0, outerInv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]; rw [hT2, unaryTape_lt hj]; decide)
    (by dsimp only [mAfter0, outerInv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]; rw [hT2]; exact unaryTape_neg (by omega))
  have hEnd : { mAfter0 with workPos := fun i => if i = 2 then 0 else mAfter0.workPos i } =
      { m with
        inPos := ((H * b : ℕ) : Int)
        work  := fun i p => if i = 0 then wordTape (w.take (H * b)) p else m.work i p } := by
    refine Mem.eq_of_fields rfl (fun _ _ => rfl) (fun i => ?_) rfl
    dsimp only [mAfter0, outerInv]
    fin_cases i <;> simp [hP0, hP1, hP2]
  rw [hEnd] at hRew2
  have hTime : ((H * (1 + (2 * b + 3)) + 1) + (H * b + 2)) + (H + 2) =
      3 * H * b + 5 * H + 5 := by ring
  rw [← hTime]
  exact (hLoop.seq hRew0).seq hRew2

private def emitTape0Act3 : Action 3 WorkSym :=
  mkAct2 0 1 (fun _ _ _ => .stay)
    (fun _ s₀ _ => (s₀, .right)) (fun _ _ s₁ => (s₁, .right))
    (fun _ s₀ _ => symBit s₀)

private def emitInputAct3 : Action 3 WorkSym :=
  mkAct1 1 (fun _ _ => .right) (fun _ s₁ => (s₁, .right)) (fun inp _ => inp)

private def riffleInterleaveBlock : Block 3 WorkSym :=
  Block.loop (fun _ sc => sc 2 == .u)
    (stepDirAct 2 .right) actStay
    (((Block.while1 (fun _ sc => sc 1 == .u) emitTape0Act3 actStay).seq (rewindFromEnd 1)).seq
      ((Block.while1 (fun _ sc => sc 1 == .u) emitInputAct3 actStay).seq (rewindFromEnd 1)))

private theorem Runs_riffleInterleaveBlock {m' : ℕ} (A : Matrix)
    (m : Mem 3 WorkSym) :
    let mExp := m' + 1
    let d := 2 ^ mExp
    let b := entryBits d
    let H := 2 * 4 ^ m'
    let w := encode d b A
    let out := encode d b (stoneShuffleMatrix mExp A)
    m.inPos = ((H * b : ℕ) : Int) →
    m.work 0 = wordTape (w.take (H * b)) → m.workPos 0 = 0 →
    m.work 1 = unaryTape b → m.workPos 1 = 0 →
    m.work 2 = unaryTape H → m.workPos 2 = 0 →
    m.outRev = [] →
    ∃ mHalt : Mem 3 WorkSym,
      Runs riffleInterleaveBlock w m mHalt (H * (4 * b + 7) + 1) ∧
      mHalt.outRev.reverse = out := by
  intro mExp d b H w out hIn hT0 hP0 hT1 hP1 hT2 hP2 hOut0
  unfold riffleInterleaveBlock
  have hdd : d * d = 2 * H := by
    have hd_eq : d = 2 * 2 ^ m' := by dsimp [d, mExp]; rw [pow_succ']
    dsimp [H]; rw [hd_eq]
    calc (2 * 2 ^ m') * (2 * 2 ^ m') = 2 * (2 * (2 ^ m' * 2 ^ m')) := by ring
      _ = 2 * (2 * (2 * 2) ^ m') := by rw [Nat.mul_pow 2 2 m']
      _ = 2 * (2 * 4 ^ m') := rfl
  have hwLen : w.length = 2 * H * b := by
    rw [(encode_len_get d b A).1, hdd]
  have houtLen : out.length = 2 * H * b := by
    rw [(encode_len_get d b (stoneShuffleMatrix mExp A)).1, hdd]
  let outerInv (q : ℕ) : Mem 3 WorkSym :=
    { m with
      inPos   := (((H + q) * b : ℕ) : Int)
      workPos := fun i =>
        if i = 0 then ((q * b : ℕ) : Int)
        else if i = 2 then (q : Int)
        else m.workPos i
      outRev  := (out.take (2 * q * b)).reverse }
  have hOuter0 : outerInv 0 = m := by
    refine Mem.eq_of_fields ?_ (fun _ _ => rfl) (fun i => ?_) ?_
    · dsimp only [outerInv]; rw [Nat.add_zero, hIn]
    · dsimp only [outerInv]; fin_cases i <;> simp [hP0, hP1, hP2]
    · dsimp only [outerInv]; simp [hOut0]
  have hLoop := Runs.loop (w := w)
    (fun _ (sc : Fin 3 → WorkSym) => sc 2 == .u)
    (stepDirAct 2 .right) actStay _ (4 * b + 6) H outerInv
    (fun q hq => by
      have hcell2 : ((outerInv q).work 2 ((outerInv q).workPos 2) == .u) = true := by
        dsimp only [outerInv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
        rw [hT2, unaryTape_lt hq]; rfl
      refine ⟨hcell2, ?_⟩
      -- Phase A: emit `b` bits from Tape 0 (`e = 2 * q`)
      let invA (t : ℕ) : Mem 3 WorkSym :=
        { m with
          inPos   := (((H + q) * b : ℕ) : Int)
          workPos := fun i =>
            if i = 0 then ((q * b + t : ℕ) : Int)
            else if i = 1 then (t : Int)
            else ((q + 1 : ℕ) : Int)
          outRev  := (out.take ((2 * q) * b + t)).reverse }
      have hEnt : applyAct w (stepDirAct 2 .right) (outerInv q) = invA 0 := by
        unfold stepDirAct; rw [applyAct_mkAct1]
        refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) ?_
        · dsimp only [outerInv, invA]
          fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Fin.reduceEq, ↓reduceIte]
          exact congrFun (ite_self_cell (m.work 2) _) p
        · dsimp only [outerInv, invA, Dir.shift]
          fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Fin.reduceEq, ↓reduceIte]
          · rfl
          · exact hP1
          · omega
        · dsimp only [outerInv, invA, Nat.add_zero]
      rw [hEnt]
      have hWA := Runs.while1 (w := w)
        (fun _ (sc : Fin 3 → WorkSym) => sc 1 == .u)
        emitTape0Act3 actStay b invA
        (fun t ht => by
          have hcell1 : ((invA t).work 1 ((invA t).workPos 1) == .u) = true := by
            dsimp only [invA]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
            rw [hT1, unaryTape_lt ht]; rfl
          refine ⟨hcell1, ?_⟩
          have hqbLt : q * b + t < H * b := by
            calc q * b + t < q * b + b := by omega
              _ = (q + 1) * b := by ring
              _ ≤ H * b := Nat.mul_le_mul_right b (by omega)
          have hwLt : q * b + t < w.length := by nlinarith [hwLen, hqbLt]
          have hTakeGet : (w.take (H * b))[q * b + t]? = some w[q * b + t] := by
            rw [List.getElem?_take_of_lt hqbLt, List.getElem?_eq_getElem hwLt]
          have hShufBit : out[(2 * q) * b + t]? = some w[q * b + t] := by
            have h := stoneShuffle_encode_bit (m' := m') A (2 * q) (by omega) t ht
            have hmod : (2 * q) % 2 = 0 := by omega
            have hdiv : (2 * q) / 2 = q := by omega
            change out[(2 * q) * b + t]? = w[((2 * q) % 2 * H + (2 * q) / 2) * b + t]? at h
            rw [hmod, hdiv, Nat.zero_mul, Nat.zero_add] at h
            rw [h, List.getElem?_eq_getElem hwLt]
          unfold emitTape0Act3
          rw [applyAct_mkAct2 w (invA t) (by decide : (0 : Fin 3) ≠ 1)]
          refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) ?_
          · dsimp only [invA]
            fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Fin.reduceEq, ↓reduceIte]
            · exact congrFun (ite_self_cell (m.work 0) _) p
            · exact congrFun (ite_self_cell (m.work 1) _) p
          · dsimp only [invA, Dir.shift]
            fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Fin.reduceEq, ↓reduceIte] <;> omega
          · dsimp only [invA]
            simp only [Fin.isValue, ↓reduceIte]
            rw [hT0, wordTape_lt hTakeGet, symBit_bitSym]
            have htk := take_succ_of_getElem?_tm hShufBit
            have hidxEq : (2 * q) * b + (t + 1) = (2 * q) * b + t + 1 := by omega
            rw [hidxEq, htk, List.reverse_append, List.reverse_singleton]
            rfl)
        (by
          dsimp only [invA]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
          rw [hT1, unaryTape_ge le_rfl]; rfl)
      rw [applyAct_actStay] at hWA
      have hRewA := Runs_rewindFromEnd (w := w) (1 : Fin 3) (invA b) b
        (by dsimp only [invA]; simp)
        (fun j hj => by dsimp only [invA]; rw [hT1, unaryTape_lt hj]; decide)
        (by dsimp only [invA]; rw [hT1]; exact unaryTape_neg (by omega))
      -- Phase B: emit `b` bits from `inPos` (`e = 2 * q + 1`)
      let invB (t : ℕ) : Mem 3 WorkSym :=
        { m with
          inPos   := (((H + q) * b + t : ℕ) : Int)
          workPos := fun i =>
            if i = 0 then (((q + 1) * b : ℕ) : Int)
            else if i = 1 then (t : Int)
            else ((q + 1 : ℕ) : Int)
          outRev  := (out.take ((2 * q + 1) * b + t)).reverse }
      have hMidAB : { invA b with workPos := fun i => if i = 1 then 0 else (invA b).workPos i } =
          invB 0 := by
        have h1 : q * b + b = (q + 1) * b := by ring
        have h2 : (2 * q) * b + b = (2 * q + 1) * b := by ring
        refine Mem.eq_of_fields rfl (fun _ _ => rfl) (fun i => ?_) ?_
        · dsimp only [invA, invB]
          fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Fin.reduceEq, ↓reduceIte, Nat.cast_zero]
          exact congrArg Nat.cast h1
        · dsimp only [invA, invB, Nat.add_zero]; rw [h2]
      rw [hMidAB] at hRewA
      have hWB := Runs.while1 (w := w)
        (fun _ (sc : Fin 3 → WorkSym) => sc 1 == .u)
        emitInputAct3 actStay b invB
        (fun t ht => by
          have hcell1 : ((invB t).work 1 ((invB t).workPos 1) == .u) = true := by
            dsimp only [invB]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
            rw [hT1, unaryTape_lt ht]; rfl
          refine ⟨hcell1, ?_⟩
          have hwLt : (H + q) * b + t < w.length := by
            have : (H + q) * b + t < (H + q + 1) * b := by ring_nf; omega
            have : (H + q + 1) * b ≤ 2 * H * b := Nat.mul_le_mul_right b (by omega)
            omega
          have hShufBit : out[(2 * q + 1) * b + t]? = some w[(H + q) * b + t] := by
            have h := stoneShuffle_encode_bit (m' := m') A (2 * q + 1) (by omega) t ht
            have hmod : (2 * q + 1) % 2 = 1 := by omega
            have hdiv : (2 * q + 1) / 2 = q := by omega
            change out[(2 * q + 1) * b + t]? = w[((2 * q + 1) % 2 * H + (2 * q + 1) / 2) * b + t]? at h
            rw [hmod, hdiv, Nat.one_mul] at h
            rw [h, List.getElem?_eq_getElem hwLt]
          unfold emitInputAct3
          rw [applyAct_mkAct1]
          refine Mem.eq_of_fields ?_ (fun i p => ?_) (fun i => ?_) ?_
          · dsimp only [invB, Dir.shift]; omega
          · dsimp only [invB]
            fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Fin.reduceEq, ↓reduceIte]
            exact congrFun (ite_self_cell (m.work 1) _) p
          · dsimp only [invB, Dir.shift]
            fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Fin.reduceEq, ↓reduceIte]; omega
          · dsimp only [invB]
            rw [readInput_of_nonneg, List.getElem?_eq_getElem hwLt]
            have htk := take_succ_of_getElem?_tm hShufBit
            have hidxEq : (2 * q + 1) * b + (t + 1) = (2 * q + 1) * b + t + 1 := by omega
            rw [hidxEq, htk, List.reverse_append, List.reverse_singleton]
            rfl)
        (by
          dsimp only [invB]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
          rw [hT1, unaryTape_ge le_rfl]; rfl)
      rw [applyAct_actStay] at hWB
      have hRewB := Runs_rewindFromEnd (w := w) (1 : Fin 3) (invB b) b
        (by dsimp only [invB]; simp)
        (fun j hj => by dsimp only [invB]; rw [hT1, unaryTape_lt hj]; decide)
        (by dsimp only [invB]; rw [hT1]; exact unaryTape_neg (by omega))
      have hEndB : { invB b with workPos := fun i => if i = 1 then 0 else (invB b).workPos i } =
          outerInv (q + 1) := by
        have h1 : (H + q) * b + b = (H + (q + 1)) * b := by ring
        have h2 : (2 * q + 1) * b + b = 2 * (q + 1) * b := by ring
        refine Mem.eq_of_fields ?_ (fun _ _ => rfl) (fun i => ?_) ?_
        · dsimp only [invB, outerInv]; exact congrArg Nat.cast h1
        · dsimp only [invB, outerInv]
          fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Fin.reduceEq, ↓reduceIte]
          exact hP1.symm
        · dsimp only [invB, outerInv]; rw [h2]
      rw [hEndB] at hRewB
      have hTime : ((b + 1) + (b + 2)) + ((b + 1) + (b + 2)) = 4 * b + 6 := by omega
      rw [← hTime]
      exact (hWA.seq hRewA).seq (hWB.seq hRewB))
    (by
      dsimp only [outerInv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
      rw [hT2, unaryTape_ge le_rfl]; rfl)
  rw [hOuter0, applyAct_actStay] at hLoop
  have hTimeEq : H * (1 + (4 * b + 6)) + 1 = H * (4 * b + 7) + 1 := by ring
  rw [hTimeEq] at hLoop
  refine ⟨outerInv H, hLoop, ?_⟩
  dsimp only [outerInv]
  rw [List.reverse_reverse, List.take_of_length_le (by omega)]

private def stoneShuffleProg : Block 3 WorkSym :=
  (((discoverEntryBits 0 1).seq halveUnaryBlock).seq copyHalfToTape0Block).seq
    riffleInterleaveBlock


/-- Explicit `3`-work-tape transition table computing one pass of Stone's perfect shuffle in `O(L)`
time. -/
def stoneShuffleTM : DetTM :=
  stoneShuffleProg.toTM encWorkSym decWorkSym

/-- `stoneShuffleTM` uses `3` work tapes and computes `stoneShuffleMatrix m A` on every `2^m × 2^m`
matrix (`m ≥ 1`) within `150 * inputLength (2^m)` steps. -/
theorem stoneShuffleTM_threeTape_linear :
    stoneShuffleTM.k = 3 ∧
    ∀ (m : ℕ) (A : Matrix), 1 ≤ m →
      let d := 2 ^ m
      ComputesWithin stoneShuffleTM
        (encode d (entryBits d) A)
        (encode d (entryBits d) (stoneShuffleMatrix m A))
        (150 * inputLength d) := by
  refine ⟨rfl, ?_⟩
  intro m A hm
  unfold stoneShuffleTM
  obtain ⟨m', rfl⟩ := Nat.exists_eq_add_of_le' hm
  set mExp := m' + 1
  set d := 2 ^ mExp
  set b := entryBits d
  set H := 2 * 4 ^ m'
  set L := inputLength d
  set w := encode d b A
  have hd1 : 1 ≤ d := Nat.two_pow_pos mExp
  have hbEq : b = mExp := entryBits_two_pow hm
  have hb1 : 1 ≤ b := entryBits_pos_tm d
  have hH1 : 1 ≤ H := by dsimp [H]; have := Nat.one_le_pow m' 4 (by decide); omega
  have h4b : 4 ^ b = 2 * H := by
    rw [hbEq]; dsimp [mExp, H]
    rw [pow_succ']
    ring
  have hdd : d * d = 2 * H := by
    have hd_eq : d = 2 * 2 ^ m' := by dsimp [d, mExp]; rw [pow_succ']
    dsimp [H]; rw [hd_eq]
    calc (2 * 2 ^ m') * (2 * 2 ^ m') = 2 * (2 * (2 ^ m' * 2 ^ m')) := by ring
      _ = 2 * (2 * (2 * 2) ^ m') := by rw [Nat.mul_pow 2 2 m']
      _ = 2 * (2 * 4 ^ m') := rfl
  have hL_eq : L = 2 * H * b := by
    dsimp [L, inputLength, b]; rw [hdd]
  have hL1 : 1 ≤ L := inputLength_pos hd1
  have hwLen : w.length = L := (encode_len_get d b A).1
  let m0 : Mem 3 WorkSym :=
    { inPos := 0, work := fun _ _ => .blank, workPos := fun _ => 0, outRev := [] }
  -- 1. `discoverEntryBits 0 1`
  have r1 := Runs_discoverEntryBits (k := 3) (t₀ := 0) (t₁ := 1) (by decide) hd1 hwLen
    m0 rfl rfl rfl rfl rfl
  change Runs (discoverEntryBits 0 1) w m0 _ (120 * L) at r1
  rw [h4b] at r1
  let m1 : Mem 3 WorkSym :=
    { m0 with
      work := fun i p =>
        if i = 0 then unaryTape (2 * H) p
        else if i = 1 then unaryTape b p
        else .blank }
  have hm1Eq : { m0 with
      work := fun i p =>
        if i = 0 then unaryTape (2 * H) p
        else if i = 1 then unaryTape b p
        else m0.work i p } = m1 := rfl
  rw [hm1Eq] at r1
  -- 2. `halveUnaryBlock`
  have r2 := Runs_halveUnaryBlock (w := w) m1 H rfl rfl rfl rfl
  let m2 : Mem 3 WorkSym :=
    { m0 with
      work := fun i p =>
        if i = 0 then .blank
        else if i = 1 then unaryTape b p
        else unaryTape H p }
  have hm2Eq : { m1 with
      work := fun i p =>
        if i = 0 then .blank
        else if i = 2 then unaryTape H p
        else m1.work i p } = m2 := by
    refine Mem.eq_of_fields rfl (fun i p => ?_) (fun _ => rfl) rfl
    fin_cases i <;> rfl
  rw [hm2Eq] at r2
  -- 3. `copyHalfToTape0Block`
  have h2Hb_le_w : 2 * H * b ≤ w.length := by rw [hwLen, hL_eq]
  have r3 := Runs_copyHalfToTape0Block (w := w) m2 H b h2Hb_le_w rfl rfl rfl rfl rfl rfl rfl
  let m3 : Mem 3 WorkSym :=
    { m0 with
      inPos := ((H * b : ℕ) : Int)
      work  := fun i p =>
        if i = 0 then wordTape (w.take (H * b)) p
        else if i = 1 then unaryTape b p
        else unaryTape H p }
  have hm3Eq : { m2 with
      inPos := ((H * b : ℕ) : Int)
      work  := fun i p => if i = 0 then wordTape (w.take (H * b)) p else m2.work i p } = m3 := by
    refine Mem.eq_of_fields rfl (fun i p => ?_) (fun _ => rfl) rfl
    fin_cases i <;> rfl
  rw [hm3Eq] at r3
  -- 4. `riffleInterleaveBlock`
  obtain ⟨mHalt, r4, hOut⟩ := Runs_riffleInterleaveBlock (m' := m') A m3
    rfl rfl rfl rfl rfl rfl rfl rfl
  change Runs riffleInterleaveBlock w m3 mHalt (H * (4 * b + 7) + 1) at r4
  change mHalt.outRev.reverse = encode d b (stoneShuffleMatrix mExp A) at hOut
  have rTotal : Runs stoneShuffleProg w m0 mHalt (150 * L) := by
    unfold stoneShuffleProg
    apply (((r1.seq r2).seq r3).seq r4).of_le
    have hL2 : L = 2 * (H * b) := by rw [hL_eq]; ring
    have hH_le : H ≤ H * b := Nat.le_mul_of_pos_right H hb1
    nlinarith
  exact Block.computesWithin .blank encWorkSym decWorkSym decWorkSym_encWorkSym encWorkSym_blank
    stoneShuffleProg rTotal hOut


end LeanMachine.ShuffleShear
