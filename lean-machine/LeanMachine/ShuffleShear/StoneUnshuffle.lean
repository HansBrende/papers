import LeanMachine.ShuffleShear.Model

/-!
# Linear-Time `2`-Work-Tape Turing Machine for Stone's Inverse Unshuffle

Constructs an explicit finite transition table `stoneUnshuffleTM : DetTM` with `k = 2` work tapes
over a `10`-symbol work alphabet (`g = 9`) that computes one pass of Stone's inverse unshuffle
`stoneUnshuffleMatrix m A` on the row-major encoding of any `2^m × 2^m` matrix (`m ≥ 1`) with
`⌈log₂(2^m)⌉`-bit entries within `150 · L` steps (`L = inputLength (2^m)`).
-/

namespace LeanMachine.ShuffleShear

private theorem stoneUnshuffle_encode_top {m' : ℕ} (A : Matrix) :
    let m := m' + 1
    let d := 2 ^ m
    let b := entryBits d
    let H := 2 * 4 ^ m'
    ∀ q < H, ∀ t < b,
      (encode d b (stoneUnshuffleMatrix m A))[q * b + t]? =
        (encode d b A)[(2 * q) * b + t]? := by
  intro m d b H q hq t ht
  have hd_eq : d = 2 * 2 ^ m' := by dsimp [d, m]; rw [pow_succ']
  have hH_eq : H = 2 ^ m' * d := by
    dsimp [H]; rw [hd_eq]
    calc 2 * 4 ^ m' = 2 * (2 * 2) ^ m' := rfl
      _ = 2 * (2 ^ m' * 2 ^ m') := by rw [Nat.mul_pow 2 2 m']
      _ = 2 ^ m' * (2 * 2 ^ m') := by ring
  have hdd_eq : d * d = 2 * H := by rw [hH_eq, hd_eq]; ring
  have hq_dd : q < d * d := by omega
  have h2q_dd : 2 * q < d * d := by omega
  rw [encode_entry_bit d b (stoneUnshuffleMatrix m A) hq_dd ht,
      encode_entry_bit d b A h2q_dd ht]
  congr 1
  set r := q / d
  set c := q % d
  have hd_pos : 0 < d := Nat.two_pow_pos m
  have hhm_pos : 0 < 2 ^ m' := Nat.two_pow_pos m'
  have hq_decomp : q = r * d + c := by
    dsimp [r, c]; rw [Nat.mul_comm, Nat.div_add_mod]
  have hc_lt : c < d := Nat.mod_lt q hd_pos
  have hr_lt : r < 2 ^ m' := by
    have : r * d < 2 ^ m' * d := by nlinarith
    exact (Nat.mul_lt_mul_right hd_pos).mp this
  have hr_div : r / 2 ^ m' = 0 := Nat.div_eq_of_lt hr_lt
  have hc_div_le : c / 2 ^ m' ≤ 1 := by
    have : c < 2 * 2 ^ m' := by omega
    have hlt2 : c / 2 ^ m' < 2 := Nat.div_lt_of_lt_mul (by omega)
    omega
  have hc_mod_lt : c % 2 ^ m' < 2 ^ m' := Nat.mod_lt c hhm_pos
  have hc_decomp : c = (c / 2 ^ m') * 2 ^ m' + c % 2 ^ m' := by
    rw [Nat.mul_comm, Nat.div_add_mod]
  let srcR := 2 * r + c / 2 ^ m'
  let srcC := 2 * (c % 2 ^ m')
  have hsrcR_lt : srcR < d := by dsimp [srcR]; omega
  have hsrcC_lt : srcC < d := by dsimp [srcC]; omega
  have hflat : 2 * q = srcR * d + srcC := by
    dsimp [srcR, srcC]
    rw [hq_decomp, hd_eq]
    nlinarith [hc_decomp]
  obtain ⟨hdiv_src, hmod_src⟩ := mul_add_div_mod_tm hsrcC_lt
  rw [hflat, hdiv_src, hmod_src]
  change A ((2 * r + c / 2 ^ m') % d) ((2 * c + r / 2 ^ m') % d) t = A srcR srcC t
  have h2c_eq : 2 * c + r / 2 ^ m' = srcC + d * (c / 2 ^ m') := by
    rw [hr_div, Nat.add_zero]
    dsimp [srcC]
    rw [hd_eq]
    nlinarith [hc_decomp]
  rw [Nat.mod_eq_of_lt hsrcR_lt, h2c_eq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hsrcC_lt]

private theorem stoneUnshuffle_encode_bot {m' : ℕ} (A : Matrix) :
    let m := m' + 1
    let d := 2 ^ m
    let b := entryBits d
    let H := 2 * 4 ^ m'
    ∀ q < H, ∀ t < b,
      (encode d b (stoneUnshuffleMatrix m A))[(H + q) * b + t]? =
        (encode d b A)[(2 * q + 1) * b + t]? := by
  intro m d b H q hq t ht
  have hd_eq : d = 2 * 2 ^ m' := by dsimp [d, m]; rw [pow_succ']
  have hH_eq : H = 2 ^ m' * d := by
    dsimp [H]; rw [hd_eq]
    calc 2 * 4 ^ m' = 2 * (2 * 2) ^ m' := rfl
      _ = 2 * (2 ^ m' * 2 ^ m') := by rw [Nat.mul_pow 2 2 m']
      _ = 2 ^ m' * (2 * 2 ^ m') := by ring
  have hdd_eq : d * d = 2 * H := by rw [hH_eq, hd_eq]; ring
  have hHq_dd : H + q < d * d := by omega
  have h2q1_dd : 2 * q + 1 < d * d := by omega
  rw [encode_entry_bit d b (stoneUnshuffleMatrix m A) hHq_dd ht,
      encode_entry_bit d b A h2q1_dd ht]
  congr 1
  set r₀ := q / d
  set c := q % d
  have hd_pos : 0 < d := Nat.two_pow_pos m
  have hhm_pos : 0 < 2 ^ m' := Nat.two_pow_pos m'
  have hq_decomp : q = r₀ * d + c := by
    dsimp [r₀, c]; rw [Nat.mul_comm, Nat.div_add_mod]
  have hc_lt : c < d := Nat.mod_lt q hd_pos
  have hr₀_lt : r₀ < 2 ^ m' := by
    have : r₀ * d < 2 ^ m' * d := by nlinarith
    exact (Nat.mul_lt_mul_right hd_pos).mp this
  have hHq_div : (H + q) / d = 2 ^ m' + r₀ := by
    have hEq : H + q = c + d * (2 ^ m' + r₀) := by rw [hH_eq, hq_decomp]; ring
    rw [hEq, Nat.add_mul_div_left c _ hd_pos, Nat.div_eq_of_lt hc_lt, zero_add]
  have hHq_mod : (H + q) % d = c := by
    have hEq : H + q = c + d * (2 ^ m' + r₀) := by rw [hH_eq, hq_decomp]; ring
    rw [hEq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc_lt]
  have hr_div : (2 ^ m' + r₀) / 2 ^ m' = 1 := by
    have hEq : 2 ^ m' + r₀ = r₀ + 2 ^ m' * 1 := by ring
    rw [hEq, Nat.add_mul_div_left r₀ 1 hhm_pos, Nat.div_eq_of_lt hr₀_lt, zero_add]
  have hc_div_le : c / 2 ^ m' ≤ 1 := by
    have hlt2 : c / 2 ^ m' < 2 := Nat.div_lt_of_lt_mul (by omega)
    omega
  have hc_mod_lt : c % 2 ^ m' < 2 ^ m' := Nat.mod_lt c hhm_pos
  have hc_decomp : c = (c / 2 ^ m') * 2 ^ m' + c % 2 ^ m' := by
    rw [Nat.mul_comm, Nat.div_add_mod]
  let srcR := 2 * r₀ + c / 2 ^ m'
  let srcC := 2 * (c % 2 ^ m') + 1
  have hsrcR_lt : srcR < d := by dsimp [srcR]; omega
  have hsrcC_lt : srcC < d := by dsimp [srcC]; omega
  have hflat : 2 * q + 1 = srcR * d + srcC := by
    dsimp [srcR, srcC]
    rw [hq_decomp, hd_eq]
    nlinarith [hc_decomp]
  obtain ⟨hdiv_src, hmod_src⟩ := mul_add_div_mod_tm hsrcC_lt
  rw [hflat, hdiv_src, hmod_src, hHq_div, hHq_mod]
  change A ((2 * (2 ^ m' + r₀) + c / 2 ^ m') % d) ((2 * c + (2 ^ m' + r₀) / 2 ^ m') % d) t =
    A srcR srcC t
  have h2r_eq : 2 * (2 ^ m' + r₀) + c / 2 ^ m' = srcR + d * 1 := by
    dsimp [srcR]; rw [hd_eq]; ring
  have h2c_eq : 2 * c + (2 ^ m' + r₀) / 2 ^ m' = srcC + d * (c / 2 ^ m') := by
    rw [hr_div]
    dsimp [srcC]
    rw [hd_eq]
    nlinarith [hc_decomp]
  rw [h2r_eq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hsrcR_lt,
      h2c_eq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hsrcC_lt]

private def emitInputAct2 : Action 2 WorkSym :=
  mkAct1 1 (fun _ _ => .right) (fun _ s₁ => (s₁, .right)) (fun inp _ => inp)

private def copyOddBitAct2 : Action 2 WorkSym :=
  mkAct2 0 1 (fun _ _ _ => .right)
    (fun inp _ _ => (bitSym (inp.getD false), .right))
    (fun _ _ s₁ => (s₁, .right))
    (fun _ _ _ => none)

private def emitSavedTape0Act2 : Action 2 WorkSym :=
  mkAct1 0 (fun _ _ => .stay) (fun _ s₀ => (s₀, .right)) (fun _ s₀ => symBit s₀)

private def streamUnshuffleBlock : Block 2 WorkSym :=
  ((Block.loop (fun inp _ => inp.isSome)
    actStay actStay
    (((Block.while1 (fun _ sc => sc 1 == .u) emitInputAct2 actStay).seq (rewindFromEnd 1)).seq
      ((Block.while1 (fun _ sc => sc 1 == .u) copyOddBitAct2 actStay).seq (rewindFromEnd 1)))).seq
    (rewindFromEnd 0)).seq
    (Block.while1 (fun _ sc => sc 0 != .blank) emitSavedTape0Act2 actStay)

private theorem Runs_streamUnshuffleBlock {m' : ℕ} (A : Matrix)
    (m : Mem 2 WorkSym) :
    let mExp := m' + 1
    let d := 2 ^ mExp
    let b := entryBits d
    let H := 2 * 4 ^ m'
    let w := encode d b A
    let out := encode d b (stoneUnshuffleMatrix mExp A)
    m.inPos = 0 →
    m.work 0 = (fun _ => .blank) → m.workPos 0 = 0 →
    m.work 1 = unaryTape b → m.workPos 1 = 0 →
    m.outRev = [] →
    ∃ mHalt : Mem 2 WorkSym,
      Runs streamUnshuffleBlock w m mHalt ((H * (4 * b + 7) + 1) + (H * b + 2) + (H * b + 1)) ∧
      mHalt.outRev.reverse = out := by
  intro mExp d b H w out hIn hB0 hP0 hT1 hP1 hOut0
  unfold streamUnshuffleBlock
  have hd_eq : d = 2 * 2 ^ m' := by dsimp [d, mExp]; rw [pow_succ']
  have hdd : d * d = 2 * H := by
    dsimp [H]; rw [hd_eq]
    calc (2 * 2 ^ m') * (2 * 2 ^ m') = 2 * (2 * (2 ^ m' * 2 ^ m')) := by ring
      _ = 2 * (2 * (2 * 2) ^ m') := by rw [Nat.mul_pow 2 2 m']
      _ = 2 * (2 * 4 ^ m') := rfl
  have hb1 : 1 ≤ b := entryBits_pos_tm d
  have hwLen : w.length = 2 * H * b := by
    rw [(encode_len_get d b A).1, hdd]
  have houtLen : out.length = 2 * H * b := by
    rw [(encode_len_get d b (stoneUnshuffleMatrix mExp A)).1, hdd]
  let saved := out.drop (H * b)
  have hsavedLen : saved.length = H * b := by
    dsimp [saved]
    rw [List.length_drop, houtLen]
    have hsplit : 2 * H * b = H * b + H * b := by ring
    rw [hsplit, Nat.add_sub_cancel]
  let outerInv (q : ℕ) : Mem 2 WorkSym :=
    { m with
      inPos   := (((2 * q) * b : ℕ) : Int)
      work    := fun i p => if i = 0 then wordTape (saved.take (q * b)) p else m.work i p
      workPos := fun i => if i = 0 then ((q * b : ℕ) : Int) else m.workPos i
      outRev  := (out.take (q * b)).reverse }
  have hOuter0 : outerInv 0 = m := by
    refine Mem.eq_of_fields ?_ (fun i p => ?_) (fun i => ?_) ?_
    · dsimp only [outerInv]; simp [hIn]
    · dsimp only [outerInv]
      fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]
      simp [wordTape_nil, hB0]
    · dsimp only [outerInv]
      fin_cases i <;> simp [hP0, hP1]
    · dsimp only [outerInv]; simp [hOut0]
  have hLoop := Runs.loop (w := w)
    (fun inp (_ : Fin 2 → WorkSym) => inp.isSome)
    actStay actStay _ (4 * b + 6) H outerInv
    (fun q hq => by
      have h2qbLt : (2 * q) * b < w.length := by
        have h1 : 2 * q < 2 * H := by omega
        have h2 : (2 * q) * b < (2 * H) * b := (Nat.mul_lt_mul_right hb1).mpr h1
        omega
      have hcond : (readInput w (outerInv q).inPos).isSome = true := by
        dsimp only [outerInv]
        rw [readInput_of_nonneg, List.getElem?_eq_getElem h2qbLt]; rfl
      refine ⟨hcond, ?_⟩
      rw [applyAct_actStay]
      -- Phase 1: emit `b` bits of even cell `2 * q`
      let invA (t : ℕ) : Mem 2 WorkSym :=
        { m with
          inPos   := (((2 * q) * b + t : ℕ) : Int)
          work    := fun i p => if i = 0 then wordTape (saved.take (q * b)) p else m.work i p
          workPos := fun i => if i = 0 then ((q * b : ℕ) : Int) else (t : Int)
          outRev  := (out.take (q * b + t)).reverse }
      have hInvA0 : outerInv q = invA 0 := by
        refine Mem.eq_of_fields rfl (fun _ _ => rfl) (fun i => ?_) rfl
        dsimp only [outerInv, invA]
        fin_cases i <;> simp [hP1]
      rw [hInvA0]
      have hWA := Runs.while1 (w := w)
        (fun _ (sc : Fin 2 → WorkSym) => sc 1 == .u)
        emitInputAct2 actStay b invA
        (fun t ht => by
          have hcell1 : ((invA t).work 1 ((invA t).workPos 1) == .u) = true := by
            dsimp only [invA]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
            rw [hT1, unaryTape_lt ht]; rfl
          refine ⟨hcell1, ?_⟩
          have hwLt : (2 * q) * b + t < w.length := by
            have : (2 * q) * b + t < (2 * q + 1) * b := by ring_nf; omega
            have : (2 * q + 1) * b ≤ (2 * H) * b := Nat.mul_le_mul_right b (by omega)
            omega
          have hTopBit : out[q * b + t]? = some w[(2 * q) * b + t] := by
            have h := stoneUnshuffle_encode_top (m' := m') A q hq t ht
            change out[q * b + t]? = w[(2 * q) * b + t]? at h
            rw [h, List.getElem?_eq_getElem hwLt]
          unfold emitInputAct2
          rw [applyAct_mkAct1]
          refine Mem.eq_of_fields ?_ (fun i p => ?_) (fun i => ?_) ?_
          · dsimp only [invA, Dir.shift]; omega
          · dsimp only [invA]
            fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]
            exact congrFun (ite_self_cell (m.work 1) _) p
          · dsimp only [invA, Dir.shift]
            fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]; omega
          · dsimp only [invA]
            rw [readInput_of_nonneg, List.getElem?_eq_getElem hwLt]
            have htk := take_succ_of_getElem?_tm hTopBit
            have hidxEq : q * b + (t + 1) = q * b + t + 1 := by omega
            rw [hidxEq, htk, List.reverse_append, List.reverse_singleton]
            rfl)
        (by
          dsimp only [invA]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
          rw [hT1, unaryTape_ge le_rfl]; rfl)
      rw [applyAct_actStay] at hWA
      have hRewA := Runs_rewindFromEnd (w := w) (1 : Fin 2) (invA b) b
        (by dsimp only [invA]; simp)
        (fun j hj => by dsimp only [invA]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]; rw [hT1, unaryTape_lt hj]; decide)
        (by dsimp only [invA]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]; rw [hT1]; exact unaryTape_neg (by omega))
      -- Phase 2: copy `b` bits of odd cell `2 * q + 1` onto Tape 0
      let invB (t : ℕ) : Mem 2 WorkSym :=
        { m with
          inPos   := (((2 * q + 1) * b + t : ℕ) : Int)
          work    := fun i p => if i = 0 then wordTape (saved.take (q * b + t)) p else m.work i p
          workPos := fun i => if i = 0 then ((q * b + t : ℕ) : Int) else (t : Int)
          outRev  := (out.take ((q + 1) * b)).reverse }
      have hMidAB : { invA b with workPos := fun i => if i = 1 then 0 else (invA b).workPos i } =
          invB 0 := by
        have h1 : (2 * q) * b + b = (2 * q + 1) * b := by ring
        have h2 : q * b + b = (q + 1) * b := by ring
        refine Mem.eq_of_fields ?_ (fun _ _ => rfl) (fun i => ?_) ?_
        · dsimp only [invA, invB, Nat.add_zero]; exact congrArg Nat.cast h1
        · dsimp only [invA, invB, Nat.add_zero]
          fin_cases i <;> simp
        · dsimp only [invA, invB]; rw [h2]
      rw [hMidAB] at hRewA
      have hWB := Runs.while1 (w := w)
        (fun _ (sc : Fin 2 → WorkSym) => sc 1 == .u)
        copyOddBitAct2 actStay b invB
        (fun t ht => by
          have hcell1 : ((invB t).work 1 ((invB t).workPos 1) == .u) = true := by
            dsimp only [invB]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
            rw [hT1, unaryTape_lt ht]; rfl
          refine ⟨hcell1, ?_⟩
          have hwLt : (2 * q + 1) * b + t < w.length := by
            have : (2 * q + 1) * b + t < (2 * q + 2) * b := by ring_nf; omega
            have : (2 * q + 2) * b ≤ (2 * H) * b := Nat.mul_le_mul_right b (by omega)
            omega
          have hSavedBit : saved[q * b + t]? = some w[(2 * q + 1) * b + t] := by
            dsimp only [saved]
            rw [List.getElem?_drop]
            have hIdxEq : H * b + (q * b + t) = (H + q) * b + t := by ring
            rw [hIdxEq]
            have h := stoneUnshuffle_encode_bot (m' := m') A q hq t ht
            change out[(H + q) * b + t]? = w[(2 * q + 1) * b + t]? at h
            rw [h, List.getElem?_eq_getElem hwLt]
          unfold copyOddBitAct2
          rw [applyAct_mkAct2 w (invB t) (by decide : (0 : Fin 2) ≠ 1)]
          refine Mem.eq_of_fields ?_ (fun i p => ?_) (fun i => ?_) rfl
          · dsimp only [invB, Dir.shift]; omega
          · dsimp only [invB]
            fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]
            · rw [readInput_of_nonneg, List.getElem?_eq_getElem hwLt]
              simp only [Option.getD_some]
              have hStep := wordTape_take_succ hSavedBit
              have hIdxEq : q * b + (t + 1) = q * b + t + 1 := by omega
              rw [hIdxEq]
              exact congrFun hStep p
            · exact congrFun (ite_self_cell (m.work 1) _) p
          · dsimp only [invB, Dir.shift]
            fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte] <;> omega)
        (by
          dsimp only [invB]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
          rw [hT1, unaryTape_ge le_rfl]; rfl)
      rw [applyAct_actStay] at hWB
      have hRewB := Runs_rewindFromEnd (w := w) (1 : Fin 2) (invB b) b
        (by dsimp only [invB]; simp)
        (fun j hj => by dsimp only [invB]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]; rw [hT1, unaryTape_lt hj]; decide)
        (by dsimp only [invB]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]; rw [hT1]; exact unaryTape_neg (by omega))
      have hEndIter : { invB b with workPos := fun i => if i = 1 then 0 else (invB b).workPos i } =
          outerInv (q + 1) := by
        have h1 : (2 * q + 1) * b + b = (2 * (q + 1)) * b := by ring
        have h2 : q * b + b = (q + 1) * b := by ring
        refine Mem.eq_of_fields ?_ (fun i p => ?_) (fun i => ?_) rfl
        · dsimp only [invB, outerInv]; exact congrArg Nat.cast h1
        · dsimp only [invB, outerInv]
          fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]
          rw [h2]
        · dsimp only [invB, outerInv]
          fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]
          · exact congrArg Nat.cast h2
          · exact hP1.symm
      rw [hEndIter] at hRewB
      have hIterTime : ((b + 1) + (b + 2)) + ((b + 1) + (b + 2)) = 4 * b + 6 := by omega
      rw [← hIterTime]
      exact (hWA.seq hRewA).seq (hWB.seq hRewB))
    (by
      dsimp only [outerInv]
      rw [readInput_of_nonneg, List.getElem?_eq_none (by omega)]; rfl)
  rw [hOuter0, applyAct_actStay] at hLoop
  have hSavedTake : saved.take (H * b) = saved := List.take_of_length_le (by omega)
  have hRew0 := Runs_rewindFromEnd (w := w) (0 : Fin 2) (outerInv H) (H * b)
    (by dsimp only [outerInv]; simp)
    (fun j hj => by
      dsimp only [outerInv]; simp only [Fin.isValue, ↓reduceIte, hSavedTake]
      have hjLen : j < saved.length := by omega
      rw [wordTape_lt (List.getElem?_eq_getElem hjLen)]
      exact bitSym_ne_blank _)
    (by dsimp only [outerInv]; simp only [Fin.isValue, ↓reduceIte]; exact wordTape_neg (by omega))
  -- Phase 3: stream `saved` (`H * b` bits) from Tape 0 to output
  let streamInv (k : ℕ) : Mem 2 WorkSym :=
    { m with
      inPos   := (((2 * H) * b : ℕ) : Int)
      work    := fun i p => if i = 0 then wordTape saved p else m.work i p
      workPos := fun i => if i = 0 then (k : Int) else m.workPos i
      outRev  := (out.take (H * b + k)).reverse }
  have hAfterRew0 : { outerInv H with workPos := fun i => if i = 0 then 0 else (outerInv H).workPos i } =
      streamInv 0 := by
    refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) ?_
    · dsimp only [outerInv, streamInv]
      fin_cases i <;> simp [hSavedTake]
    · dsimp only [outerInv, streamInv]
      fin_cases i <;> simp
    · dsimp only [outerInv, streamInv, Nat.add_zero]
  rw [hAfterRew0] at hRew0
  have hStream := Runs.while1 (w := w)
    (fun _ (sc : Fin 2 → WorkSym) => sc 0 != .blank)
    emitSavedTape0Act2 actStay (H * b) streamInv
    (fun k hk => by
      have hkSaved : k < saved.length := by omega
      have hcell0 : ((streamInv k).work 0 ((streamInv k).workPos 0) != .blank) = true := by
        dsimp only [streamInv]; simp only [Fin.isValue, ↓reduceIte]
        rw [wordTape_lt (List.getElem?_eq_getElem hkSaved)]
        exact bne_blank_of_ne (bitSym_ne_blank _)
      refine ⟨hcell0, ?_⟩
      have hOutBit : out[H * b + k]? = some saved[k] := by
        have hdrop : saved[k]? = out[H * b + k]? := by
          dsimp only [saved]; rw [List.getElem?_drop]
        rw [List.getElem?_eq_getElem hkSaved] at hdrop
        exact hdrop.symm
      unfold emitSavedTape0Act2
      rw [applyAct_mkAct1]
      refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) ?_
      · dsimp only [streamInv]
        fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]
        exact congrFun (ite_self_cell _ _) p
      · dsimp only [streamInv, Dir.shift]
        fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]; omega
      · dsimp only [streamInv]
        simp only [Fin.isValue, ↓reduceIte]
        rw [wordTape_lt (List.getElem?_eq_getElem hkSaved), symBit_bitSym]
        have htk := take_succ_of_getElem?_tm hOutBit
        have hIdxEq : H * b + (k + 1) = H * b + k + 1 := by omega
        rw [hIdxEq, htk, List.reverse_append, List.reverse_singleton]
        rfl)
    (by
      dsimp only [streamInv]; simp only [Fin.isValue, ↓reduceIte]
      rw [wordTape_ge (by omega)]; rfl)
  rw [applyAct_actStay] at hStream
  have hLoopTime : H * (1 + (4 * b + 6)) + 1 = H * (4 * b + 7) + 1 := by ring
  rw [hLoopTime] at hLoop
  refine ⟨streamInv (H * b), (hLoop.seq hRew0).seq hStream, ?_⟩
  dsimp only [streamInv]
  have h2Hb : H * b + H * b = 2 * H * b := by ring
  rw [List.reverse_reverse, h2Hb, List.take_of_length_le (by omega)]

private def stoneUnshuffleProg : Block 2 WorkSym :=
  ((discoverEntryBits 0 1).seq (clearUnary 0)).seq streamUnshuffleBlock


/-- Explicit `2`-work-tape transition table computing one pass of Stone's inverse unshuffle in
`O(L)` time. -/
def stoneUnshuffleTM : DetTM :=
  stoneUnshuffleProg.toTM encWorkSym decWorkSym

/-- `stoneUnshuffleTM` uses `2` work tapes and computes `stoneUnshuffleMatrix m A` on every
`2^m × 2^m` matrix (`m ≥ 1`) within `150 * inputLength (2^m)` steps. -/
theorem stoneUnshuffleTM_twoTape_linear :
    stoneUnshuffleTM.k = 2 ∧
    ∀ (m : ℕ) (A : Matrix), 1 ≤ m →
      let d := 2 ^ m
      ComputesWithin stoneUnshuffleTM
        (encode d (entryBits d) A)
        (encode d (entryBits d) (stoneUnshuffleMatrix m A))
        (150 * inputLength d) := by
  refine ⟨rfl, ?_⟩
  intro m A hm1
  obtain ⟨m', rfl⟩ := Nat.exists_eq_add_of_le' hm1
  unfold stoneUnshuffleTM
  set d := 2 ^ (m' + 1)
  set b := entryBits d
  set L := inputLength d
  set H := 2 * 4 ^ m'
  set w := encode d b A
  have hd1 : 1 ≤ d := Nat.two_pow_pos (m' + 1)
  have hb1 : 1 ≤ b := entryBits_pos_tm d
  have hL1 : 1 ≤ L := inputLength_pos hd1
  have hd_eq : d = 2 * 2 ^ m' := by dsimp [d]; rw [pow_succ']
  have hdd : d * d = 2 * H := by
    dsimp [H]; rw [hd_eq]
    calc (2 * 2 ^ m') * (2 * 2 ^ m') = 2 * (2 * (2 ^ m' * 2 ^ m')) := by ring
      _ = 2 * (2 * (2 * 2) ^ m') := by rw [Nat.mul_pow 2 2 m']
      _ = 2 * (2 * 4 ^ m') := rfl
  have hL_eq : L = 2 * H * b := by unfold L inputLength; rw [hdd]
  have hwLen : w.length = L := (encode_len_get d b A).1
  let m0 : Mem 2 WorkSym :=
    { inPos := 0, work := fun _ _ => .blank, workPos := fun _ => 0, outRev := [] }
  have r1 := Runs_discoverEntryBits (k := 2) (t₀ := 0) (t₁ := 1) (by decide) hd1 hwLen
    m0 rfl rfl rfl rfl rfl
  change Runs (discoverEntryBits 0 1) w m0 _ (120 * L) at r1
  let m1 : Mem 2 WorkSym :=
    { m0 with work := fun i p => if i = 0 then unaryTape (4 ^ b) p else unaryTape b p }
  have hm1Eq :
      { m0 with
        work := fun i p =>
          if i = 0 then unaryTape (4 ^ b) p
          else if i = 1 then unaryTape b p
          else m0.work i p } = m1 := by
    refine Mem.eq_of_fields rfl (fun i p => ?_) (fun _ => rfl) rfl
    fin_cases i <;> rfl
  rw [hm1Eq] at r1
  have r2 := Runs_clearUnary (w := w) (0 : Fin 2) m1 (4 ^ b) rfl rfl
  let m2 : Mem 2 WorkSym :=
    { m0 with work := fun i p => if i = 0 then .blank else unaryTape b p }
  have hm2Eq :
      { m1 with work := fun i p => if i = 0 then .blank else m1.work i p } = m2 := by
    refine Mem.eq_of_fields rfl (fun i p => ?_) (fun _ => rfl) rfl
    fin_cases i <;> rfl
  rw [hm2Eq] at r2
  obtain ⟨mHalt, r3, hOut⟩ := Runs_streamUnshuffleBlock (m' := m') A m2
    rfl (by funext p; rfl) rfl (by funext p; rfl) rfl rfl
  change Runs streamUnshuffleBlock w m2 mHalt
    ((H * (4 * b + 7) + 1) + (H * b + 2) + (H * b + 1)) at r3
  have rTotal : Runs stoneUnshuffleProg w m0 mHalt (150 * L) := by
    unfold stoneUnshuffleProg
    apply ((r1.seq r2).seq r3).of_le
    have h4bL : 4 ^ b * b ≤ 4 * L := entryBits_quad_le_four_L hd1
    have h4b : 4 ^ b ≤ 4 ^ b * b := Nat.le_mul_of_pos_right (4 ^ b) hb1
    have hHL : 2 * H ≤ L := by rw [hL_eq]; exact Nat.le_mul_of_pos_right (2 * H) hb1
    have hHb : 2 * (H * b) = L := by rw [hL_eq]; ring
    have hexp : H * (4 * b + 7) = 4 * (H * b) + 7 * H := by ring
    rw [hexp]
    linarith
  exact Block.computesWithin .blank encWorkSym decWorkSym decWorkSym_encWorkSym encWorkSym_blank
    stoneUnshuffleProg rTotal hOut


end LeanMachine.ShuffleShear
