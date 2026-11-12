import Mathlib.Tactic
import Mathlib.Data.Nat.Log

/-!
# Compositional Transition-Table Compiler and Primitives for Multitape Turing Machines

Self-contained deterministic multitape Turing machine model (`DetTM`, matching the transition-table,
head-shift, row-major binary matrix encoding, and halting conventions of `Transpose.TM` in the first
paper of the series) together with a compositional finite-state block compiler (`Block`, `Runs`) and
shared unary/binary work-tape primitives (`discoverEntryBits`, `rewindFromEnd`, `eraseFromEnd`,
`clearUnary`) used to construct verified linear-time machines for Stone's perfect shuffle, Stone's
inverse unshuffle, and within-row cyclic shear.
-/

namespace LeanMachine.ShuffleShear

/-! ### 1. Deterministic Multitape Turing Machine Model and Row-Major Matrix Encoding -/

/-- Head movement on a two-way tape. -/
inductive Dir where
  | left
  | stay
  | right
  deriving DecidableEq, Repr

/-- Apply a head movement to an integer head position. -/
def Dir.shift : Dir → Int → Int
  | .left,  p => p - 1
  | .stay,  p => p
  | .right, p => p + 1

/-- Finite transition-table deterministic multitape Turing machine with a read-only two-way binary
input tape (`Option Bool`), `k` two-way infinite read/write work tapes over `Fin (g + 1)` (blank `0`),
a one-way write-only binary output tape (`Option Bool`), and state set `Fin (q + 1)` (start `0`). -/
structure DetTM where
  k : Nat
  g : Nat
  q : Nat
  δ : Fin (q + 1) → Option Bool → (Fin k → Fin (g + 1)) →
      Option (Fin (q + 1) × Dir × (Fin k → Fin (g + 1) × Dir) × Option Bool)

/-- Instantaneous machine configuration (`outRev` stores emitted bits, most recent bit first). -/
structure Config (M : DetTM) where
  state   : Fin (M.q + 1)
  inPos   : Int
  work    : Fin M.k → Int → Fin (M.g + 1)
  workPos : Fin M.k → Int
  outRev  : List Bool

/-- The `i`-th element of a boolean list, if any. -/
def nth : List Bool → Nat → Option Bool
  | [],      _     => none
  | b :: _,  0     => some b
  | _ :: bs, i + 1 => nth bs i

/-- Input symbol under the input head at integer position `p` (`none` outside `0 .. |w| - 1`). -/
def readInput (w : List Bool) (p : Int) : Option Bool :=
  if p < 0 then none else nth w p.toNat

/-- Initial configuration: state `0`, all heads at `0`, blank work tapes, empty output. -/
def init (M : DetTM) : Config M where
  state   := 0
  inPos   := 0
  work    := fun _ _ => 0
  workPos := fun _ => 0
  outRev  := []

/-- One transition step on input `w`; `none` when `M` halts in configuration `c`. -/
def step (M : DetTM) (w : List Bool) (c : Config M) : Option (Config M) :=
  match M.δ c.state (readInput w c.inPos) (fun i => c.work i (c.workPos i)) with
  | none => none
  | some (s, d, acts, o) =>
    some
      { state   := s
        inPos   := d.shift c.inPos
        work    := fun i p => if p = c.workPos i then (acts i).1 else c.work i p
        workPos := fun i => (acts i).2.shift (c.workPos i)
        outRev  := match o with
                   | none   => c.outRev
                   | some b => b :: c.outRev }

/-- Execute `n` steps on input `w` (`none` if the machine halts earlier). -/
def stepN (M : DetTM) (w : List Bool) : Nat → Config M → Option (Config M)
  | 0,     c => some c
  | n + 1, c =>
    match step M w c with
    | none    => none
    | some c' => stepN M w n c'

/-- `M` halts on input `w` within at most `t` steps with output `out`. -/
def ComputesWithin (M : DetTM) (w out : List Bool) (t : Nat) : Prop :=
  ∃ s, s ≤ t ∧ ∃ c, stepN M w s (init M) = some c ∧
    step M w c = none ∧ c.outRev.reverse = out

/-- Entry bit-width `b(n) = max(1, ⌈log₂ n⌉) = ⌊log₂(n - 1)⌋ + 1`. -/
def entryBits (n : Nat) : Nat := Nat.log2 (n - 1) + 1

/-- Concatenate `f 0 ++ f 1 ++ ⋯ ++ f (m - 1)`. -/
def concatUpTo (f : Nat → List Bool) : Nat → List Bool
  | 0     => []
  | m + 1 => concatUpTo f m ++ f m

/-- Bit-indexed matrix `A i j t` (`i, j < d`, bit `t < b`). -/
abbrev Matrix := Nat → Nat → Nat → Bool

/-- Row-major binary encoding of a `d × d` matrix `A` with `b`-bit entries. -/
def encode (d b : Nat) (A : Matrix) : List Bool :=
  concatUpTo (fun i => concatUpTo (fun j => concatUpTo (fun t => [A i j t]) b) d) d

/-- Encoded bit length `L(d) = d² · b(d)`. -/
def inputLength (d : Nat) : Nat := d * d * entryBits d

/-- One pass of Stone's perfect shuffle on a `2^m × 2^m` matrix (`d = 2^m`), cyclically rotating the
concatenated `(row, col)` binary address left by `1` bit. -/
def stoneShuffleMatrix (m : ℕ) (A : Matrix) : Matrix :=
  match m with
  | 0 => A
  | m' + 1 =>
      let d := 2 ^ (m' + 1)
      fun r' c' t =>
        let srcR := ((c' % 2) * (2 ^ m') + r' / 2) % d
        let srcC := ((r' % 2) * (2 ^ m') + c' / 2) % d
        A srcR srcC t

/-- One pass of Stone's inverse unshuffle on a `2^m × 2^m` matrix (`d = 2^m`), cyclically rotating
the concatenated `(row, col)` binary address right by `1` bit. -/
def stoneUnshuffleMatrix (m : ℕ) (A : Matrix) : Matrix :=
  match m with
  | 0 => A
  | m' + 1 =>
      let d := 2 ^ (m' + 1)
      fun r c t =>
        A ((2 * r + c / (2 ^ m')) % d) ((2 * c + r / (2 ^ m')) % d) t

/-- Within-row cyclic shear `(rowShearMatrix d A) r c t = A r ((c + r) % d) t`. -/
def rowShearMatrix (d : ℕ) (A : Matrix) : Matrix :=
  fun r c t => A r ((c + r) % d) t

/-! ### 1. Encoding Index Characterization & Entry-Width Bounds -/

theorem nth_eq_getElem?_tm : ∀ (xs : List Bool) (i : ℕ), nth xs i = xs[i]?
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: bs, i + 1 => by
    simpa only [nth, List.getElem?_cons_succ] using nth_eq_getElem?_tm bs i

theorem readInput_of_nonneg (w : List Bool) (n : ℕ) :
    readInput w (n : Int) = w[n]? := by
  unfold readInput
  have h : ¬ ((n : Int) < 0) := by omega
  rw [ite_eq_right h, Int.toNat_natCast, nth_eq_getElem?_tm]

theorem mul_add_div_mod_tm {q s r : ℕ} (hr : r < s) :
    (q * s + r) / s = q ∧ (q * s + r) % s = r := by
  have hs : 0 < s := by omega
  constructor
  · calc (q * s + r) / s = (r + s * q) / s := by rw [Nat.add_comm, Nat.mul_comm]
      _ = r / s + q := Nat.add_mul_div_left r q hs
      _ = q := by rw [Nat.div_eq_zero_iff.mpr (Or.inr hr), Nat.zero_add]
  · calc (q * s + r) % s = (r + s * q) % s := by rw [Nat.add_comm, Nat.mul_comm]
      _ = r % s := Nat.add_mul_mod_self_left r s q
      _ = r := Nat.mod_eq_of_lt hr

theorem concatUpTo_len_get {f : ℕ → List Bool} {m s : ℕ}
    (hlen : ∀ i < m, (f i).length = s) :
    (concatUpTo f m).length = m * s ∧
      ∀ k < m * s, (concatUpTo f m)[k]? = (f (k / s))[k % s]? := by
  induction m with
  | zero =>
    simp [concatUpTo]
  | succ m ih =>
    obtain ⟨ihL, ihG⟩ := ih (fun i hi => hlen i (Nat.lt_succ_of_lt hi))
    have hmL : (f m).length = s := hlen m (Nat.lt_succ_self m)
    refine ⟨?_, ?_⟩
    · simp only [concatUpTo, List.length_append, ihL, hmL]
      ring
    · intro k hk
      simp only [concatUpTo]
      by_cases hk1 : k < m * s
      · have hkLen : k < (concatUpTo f m).length := by omega
        rw [List.getElem?_append_left hkLen]
        exact ihG k hk1
      · have hkGe : m * s ≤ k := Nat.le_of_not_gt hk1
        have hkGeLen : (concatUpTo f m).length ≤ k := by omega
        rw [List.getElem?_append_right hkGeLen, ihL]
        have hrem : k - m * s < s := by
          have : (m + 1) * s = m * s + s := by ring
          omega
        have hkEq : m * s + (k - m * s) = k := Nat.add_sub_of_le hkGe
        obtain ⟨hdiv, hmod⟩ := mul_add_div_mod_tm hrem
        rw [hkEq] at hdiv hmod
        rw [hdiv, hmod]

theorem encode_len_get (d b : ℕ) (A : Matrix) :
    (encode d b A).length = d * d * b ∧
      ∀ idx < d * d * b,
        (encode d b A)[idx]? =
          some (A (idx / (d * b)) ((idx % (d * b)) / b) ((idx % (d * b)) % b)) := by
  let g₃ (i j t : ℕ) : List Bool := [A i j t]
  let g₂ (i j : ℕ) : List Bool := concatUpTo (g₃ i j) b
  have hg₂ : ∀ i j, (g₂ i j).length = b ∧
      ∀ t < b, (g₂ i j)[t]? = some (A i j t) := by
    intro i j
    obtain ⟨hL, hG⟩ := concatUpTo_len_get (f := g₃ i j) (m := b) (s := 1)
      (fun _ _ => rfl)
    refine ⟨by simpa using hL, fun t ht => ?_⟩
    have hGt := hG t (by omega)
    rw [Nat.div_one, Nat.mod_one] at hGt
    exact hGt
  let g₁ (i : ℕ) : List Bool := concatUpTo (g₂ i) d
  have hg₁ : ∀ i, (g₁ i).length = d * b ∧
      ∀ rem < d * b, (g₁ i)[rem]? = some (A i (rem / b) (rem % b)) := by
    intro i
    obtain ⟨hL, hG⟩ := concatUpTo_len_get (f := g₂ i) (m := d) (s := b)
      (fun j _ => (hg₂ i j).1)
    refine ⟨hL, fun rem hrem => ?_⟩
    have hbPos : 0 < b := by
      by_contra hb0
      have hb0' : b = 0 := by omega
      rw [hb0', mul_zero] at hrem
      exact Nat.not_lt_zero rem hrem
    rw [hG rem hrem, (hg₂ i (rem / b)).2 (rem % b) (Nat.mod_lt rem hbPos)]
  obtain ⟨hL, hG⟩ := concatUpTo_len_get (f := g₁) (m := d) (s := d * b)
    (fun i _ => (hg₁ i).1)
  have hAssoc : d * (d * b) = d * d * b := (Nat.mul_assoc d d b).symm
  refine ⟨by simpa only [encode, g₁, g₂, hAssoc] using hL, ?_⟩
  intro idx hidx
  have hidx' : idx < d * (d * b) := by omega
  have hdbPos : 0 < d * b := by
    by_contra h0
    have h0' : d * b = 0 := by omega
    rw [h0', mul_zero] at hidx'
    exact Nat.not_lt_zero idx hidx'
  change (concatUpTo g₁ d)[idx]? = _
  rw [hG idx hidx', (hg₁ (idx / (d * b))).2 (idx % (d * b)) (Nat.mod_lt idx hdbPos)]

theorem encode_entry_bit (d b : ℕ) (A : Matrix)
    {e t : ℕ} (he : e < d * d) (ht : t < b) :
    (encode d b A)[e * b + t]? = some (A (e / d) (e % d) t) := by
  have hd_pos : 0 < d := by
    by_contra h0; have : d = 0 := by omega
    rw [this] at he; simp at he
  have hidx : e * b + t < d * d * b := by
    calc e * b + t < e * b + b := by omega
      _ = (e + 1) * b := by ring
      _ ≤ (d * d) * b := Nat.mul_le_mul_right b (by omega)
  rw [(encode_len_get d b A).2 (e * b + t) hidx]
  have hed : e = (e / d) * d + (e % d) := by
    rw [Nat.mul_comm, Nat.div_add_mod]
  have hrem_lt : (e % d) * b + t < d * b := by
    have : e % d < d := Nat.mod_lt e hd_pos
    calc (e % d) * b + t < (e % d) * b + b := by omega
      _ = (e % d + 1) * b := by ring
      _ ≤ d * b := Nat.mul_le_mul_right b (by omega)
  have hsplit : e * b + t = (e / d) * (d * b) + ((e % d) * b + t) := by
    calc e * b + t = ((e / d) * d + (e % d)) * b + t := by rw [← hed]
      _ = (e / d) * (d * b) + ((e % d) * b + t) := by ring
  obtain ⟨hd1, hm1⟩ := mul_add_div_mod_tm hrem_lt
  obtain ⟨hd2, hm2⟩ := mul_add_div_mod_tm ht
  rw [hsplit, hd1, hm1, hd2, hm2]

theorem entryBits_pos_tm (d : ℕ) : 1 ≤ entryBits d := by
  unfold entryBits; omega

theorem inputLength_pos {d : ℕ} (hd : 1 ≤ d) : 1 ≤ inputLength d := by
  unfold inputLength
  have hb := entryBits_pos_tm d
  nlinarith

theorem entryBits_quad_upper {d : ℕ} (hd : 1 ≤ d) :
    inputLength d ≤ 4 ^ (entryBits d) * entryBits d := by
  unfold inputLength entryBits
  set b := (d - 1).log2 + 1
  have hlt : d - 1 < 2 ^ b := Nat.lt_log2_self
  have hd_le : d ≤ 2 ^ b := by omega
  have hsq : d * d ≤ 4 ^ b := by
    calc d * d ≤ 2 ^ b * 2 ^ b := Nat.mul_le_mul hd_le hd_le
      _ = (2 * 2) ^ b := (Nat.mul_pow 2 2 b).symm
      _ = 4 ^ b := rfl
  exact Nat.mul_le_mul_right b hsq

theorem entryBits_quad_lower {d s : ℕ} (hs1 : 1 ≤ s) (hsb : s < entryBits d) :
    4 ^ s * s < inputLength d := by
  unfold entryBits at hsb
  unfold inputLength entryBits
  set b := (d - 1).log2 + 1
  have hdm1 : d - 1 ≠ 0 := by
    intro h0
    have : (d - 1).log2 = 0 := by rw [h0]; rfl
    omega
  have h2le : 2 ^ (b - 1) ≤ d - 1 := Nat.log2_self_le hdm1
  have hs_le : s ≤ b - 1 := by omega
  have h2s_lt : 2 ^ s < d := by
    have : 2 ^ s ≤ 2 ^ (b - 1) := Nat.pow_le_pow_right (by decide) hs_le
    omega
  have h4s_lt : 4 ^ s < d * d := by
    calc 4 ^ s = (2 * 2) ^ s := rfl
      _ = 2 ^ s * 2 ^ s := Nat.mul_pow 2 2 s
      _ < d * d := Nat.mul_lt_mul_of_lt_of_lt h2s_lt h2s_lt
  exact Nat.mul_lt_mul_of_lt_of_lt h4s_lt hsb

theorem entryBits_quad_le_four_L {d : ℕ} (hd : 1 ≤ d) :
    4 ^ (entryBits d) * entryBits d ≤ 4 * inputLength d := by
  by_cases hd1 : d = 1
  · subst hd1; decide
  · unfold inputLength entryBits
    set k := (d - 1).log2
    have hdm1 : d - 1 ≠ 0 := by omega
    have h2le : 2 ^ k ≤ d - 1 := Nat.log2_self_le hdm1
    have h4k_le : 4 ^ k ≤ d * d := by
      have hk_le : 2 ^ k ≤ d := by omega
      calc 4 ^ k = (2 * 2) ^ k := rfl
        _ = 2 ^ k * 2 ^ k := Nat.mul_pow 2 2 k
        _ ≤ d * d := Nat.mul_le_mul hk_le hk_le
    calc 4 ^ (k + 1) * (k + 1) = (4 * 4 ^ k) * (k + 1) := by rw [pow_succ']
      _ ≤ (4 * (d * d)) * (k + 1) := Nat.mul_le_mul_right (k + 1) (Nat.mul_le_mul_left 4 h4k_le)
      _ = 4 * (d * d * (k + 1)) := by ring

theorem entryBits_two_pow {m : ℕ} (hm : 1 ≤ m) :
    entryBits (2 ^ m) = m := by
  have hd2 : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) hm
  unfold entryBits
  have hm0 : 2 ^ m - 1 ≠ 0 := by omega
  obtain ⟨m', rfl⟩ := Nat.exists_eq_add_of_le' hm
  have hlo : 2 ^ m' ≤ 2 ^ (m' + 1) - 1 := by
    have : 1 ≤ 2 ^ m' := Nat.two_pow_pos m'
    rw [pow_succ]; omega
  have hhi : 2 ^ (m' + 1) - 1 < 2 ^ (m' + 1) := by
    have : 1 ≤ 2 ^ (m' + 1) := Nat.two_pow_pos (m' + 1)
    omega
  have h1 : m' ≤ (2 ^ (m' + 1) - 1).log2 := (Nat.le_log2 hm0).mpr hlo
  have h2 : (2 ^ (m' + 1) - 1).log2 < m' + 1 := (Nat.log2_lt hm0).mpr hhi
  omega


theorem take_succ_of_getElem?_tm {α : Type*} {xs : List α} {i : ℕ} {x : α}
    (h : xs[i]? = some x) :
    xs.take (i + 1) = xs.take i ++ [x] := by
  have hi : i < xs.length := by
    by_contra hge
    rw [List.getElem?_eq_none (Nat.le_of_not_gt hge)] at h
    cases h
  rw [List.take_add_one, h]
  rfl


/-! ### 2. Compositional Block Compiler to `DetTM` -/

structure Mem (k : ℕ) (Sym : Type) where
  inPos   : Int
  work    : Fin k → Int → Sym
  workPos : Fin k → Int
  outRev  : List Bool

theorem Mem.eq_of_fields {k : ℕ} {Sym : Type} {m₁ m₂ : Mem k Sym}
    (hIn : m₁.inPos = m₂.inPos)
    (hWork : ∀ i p, m₁.work i p = m₂.work i p)
    (hPos : ∀ i, m₁.workPos i = m₂.workPos i)
    (hOut : m₁.outRev = m₂.outRev) : m₁ = m₂ := by
  cases m₁; cases m₂
  simp only [Mem.mk.injEq]
  exact ⟨hIn, funext fun i => funext fun p => hWork i p, funext hPos, hOut⟩

abbrev Action (k : ℕ) (Sym : Type) :=
  Option Bool → (Fin k → Sym) → (Dir × (Fin k → Sym × Dir) × Option Bool)

def applyAct {k : ℕ} {Sym : Type} (w : List Bool) (a : Action k Sym) (m : Mem k Sym) :
    Mem k Sym :=
  let res := a (readInput w m.inPos) (fun i => m.work i (m.workPos i))
  { inPos   := res.1.shift m.inPos
    work    := fun i p => if p = m.workPos i then (res.2.1 i).1 else m.work i p
    workPos := fun i => (res.2.1 i).2.shift (m.workPos i)
    outRev  := match res.2.2 with | none => m.outRev | some b => b :: m.outRev }

abbrev GStep (k : ℕ) (Sym : Type) :=
  ℕ → Option Bool → (Fin k → Sym) →
    Option (ℕ × Dir × (Fin k → Sym × Dir) × Option Bool)

def gStepOne {k : ℕ} {Sym : Type} (G : GStep k Sym) (w : List Bool)
    (cm : ℕ × Mem k Sym) : Option (ℕ × Mem k Sym) :=
  match G cm.1 (readInput w cm.2.inPos) (fun i => cm.2.work i (cm.2.workPos i)) with
  | none => none
  | some res =>
    some (res.1,
      { inPos   := res.2.1.shift cm.2.inPos
        work    := fun i p => if p = cm.2.workPos i then (res.2.2.1 i).1 else cm.2.work i p
        workPos := fun i => (res.2.2.1 i).2.shift (cm.2.workPos i)
        outRev  := match res.2.2.2 with | none => cm.2.outRev | some b => b :: cm.2.outRev })

def gStepN {k : ℕ} {Sym : Type} (G : GStep k Sym) (w : List Bool) :
    ℕ → (ℕ × Mem k Sym) → Option (ℕ × Mem k Sym)
  | 0, cm => some cm
  | n + 1, cm =>
    match gStepOne G w cm with
    | none => none
    | some cm' => gStepN G w n cm'

theorem gStepN_add {k : ℕ} {Sym : Type} (G : GStep k Sym) (w : List Bool) :
    ∀ (a b : ℕ) (cm : ℕ × Mem k Sym),
      gStepN G w (a + b) cm =
        match gStepN G w a cm with
        | none => none
        | some cm' => gStepN G w b cm'
  | 0, _, cm => by simp [gStepN]
  | a + 1, b, cm => by
    rw [Nat.succ_add]
    simp only [gStepN]
    cases gStepOne G w cm with
    | none => rfl
    | some cm' => exact gStepN_add G w a b cm'

def GReach {k : ℕ} {Sym : Type} (G : GStep k Sym) (w : List Bool)
    (cm₁ cm₂ : ℕ × Mem k Sym) (t : ℕ) : Prop :=
  ∃ s ≤ t, gStepN G w s cm₁ = some cm₂

theorem GReach.refl {k : ℕ} {Sym : Type} {G : GStep k Sym} {w : List Bool}
    (cm : ℕ × Mem k Sym) : GReach G w cm cm 0 :=
  ⟨0, le_rfl, rfl⟩

theorem GReach.of_le {k : ℕ} {Sym : Type} {G : GStep k Sym} {w : List Bool}
    {cm₁ cm₂ : ℕ × Mem k Sym} {t₁ t₂ : ℕ}
    (h : GReach G w cm₁ cm₂ t₁) (hle : t₁ ≤ t₂) :
    GReach G w cm₁ cm₂ t₂ :=
  let ⟨s, hs, hst⟩ := h
  ⟨s, hs.trans hle, hst⟩

theorem GReach.one {k : ℕ} {Sym : Type} {G : GStep k Sym} {w : List Bool}
    {cm₁ cm₂ : ℕ × Mem k Sym} (h1 : gStepOne G w cm₁ = some cm₂) :
    GReach G w cm₁ cm₂ 1 :=
  ⟨1, le_rfl, by simp [gStepN, h1]⟩

theorem GReach.trans {k : ℕ} {Sym : Type} {G : GStep k Sym} {w : List Bool}
    {cm₀ cm₁ cm₂ : ℕ × Mem k Sym} {t₁ t₂ : ℕ}
    (h1 : GReach G w cm₀ cm₁ t₁) (h2 : GReach G w cm₁ cm₂ t₂) :
    GReach G w cm₀ cm₂ (t₁ + t₂) := by
  obtain ⟨s₁, hs₁, hst₁⟩ := h1
  obtain ⟨s₂, hs₂, hst₂⟩ := h2
  refine ⟨s₁ + s₂, by omega, ?_⟩
  rw [gStepN_add, hst₁]
  exact hst₂

structure Block (k : ℕ) (Sym : Type) where
  n : ℕ
  hn : 1 ≤ n
  step : ℕ → Option Bool → (Fin k → Sym) →
    (ℕ × Dir × (Fin k → Sym × Dir) × Option Bool)
  next_le : ∀ s < n, ∀ inp sc, (step s inp sc).1 ≤ n

def Embeds {k : ℕ} {Sym : Type} (B : Block k Sym) (G : GStep k Sym) (f : ℕ → ℕ) : Prop :=
  ∀ s < B.n, ∀ inp sc,
    let res := B.step s inp sc
    G (f s) inp sc = some (f res.1, res.2)

def Runs {k : ℕ} {Sym : Type} (B : Block k Sym) (w : List Bool)
    (m₀ m₁ : Mem k Sym) (t : ℕ) : Prop :=
  ∀ (G : GStep k Sym) (f : ℕ → ℕ), Embeds B G f →
    GReach G w (f 0, m₀) (f B.n, m₁) t

theorem Runs.of_le {k : ℕ} {Sym : Type} {B : Block k Sym} {w : List Bool}
    {m₀ m₁ : Mem k Sym} {t₁ t₂ : ℕ}
    (h : Runs B w m₀ m₁ t₁) (hle : t₁ ≤ t₂) :
    Runs B w m₀ m₁ t₂ :=
  fun G f hEmb => (h G f hEmb).of_le hle

def Block.act {k : ℕ} {Sym : Type} (a : Action k Sym) : Block k Sym where
  n := 1
  hn := le_rfl
  step := fun _ inp sc => (1, a inp sc)
  next_le := fun _ _ _ _ => le_rfl

theorem Runs.act {k : ℕ} {Sym : Type} {w : List Bool}
    (a : Action k Sym) (m : Mem k Sym) :
    Runs (Block.act a) w m (applyAct w a m) 1 := by
  intro G f hEmb
  apply GReach.one
  have h0 := hEmb 0 (Nat.zero_lt_one) (readInput w m.inPos) (fun i => m.work i (m.workPos i))
  dsimp only [Block.act] at h0
  unfold gStepOne applyAct
  dsimp only [Block.act]
  rw [h0]

def Block.seq {k : ℕ} {Sym : Type} (P Q : Block k Sym) : Block k Sym where
  n := P.n + Q.n
  hn := by have := P.hn; omega
  step := fun s inp sc =>
    if s < P.n then P.step s inp sc
    else
      let res := Q.step (s - P.n) inp sc
      (P.n + res.1, res.2)
  next_le := by
    intro s hs inp sc
    by_cases hlt : s < P.n
    · rw [ite_eq_left hlt]
      have := P.next_le s hlt inp sc
      omega
    · rw [ite_eq_right hlt]
      have hQ := Q.next_le (s - P.n) (by omega) inp sc
      dsimp only
      omega

theorem Runs.seq {k : ℕ} {Sym : Type} {P Q : Block k Sym} {w : List Bool}
    {m₀ m₁ m₂ : Mem k Sym} {t₁ t₂ : ℕ}
    (hP : Runs P w m₀ m₁ t₁) (hQ : Runs Q w m₁ m₂ t₂) :
    Runs (P.seq Q) w m₀ m₂ (t₁ + t₂) := by
  intro G f hEmb
  have hEmbP : Embeds P G f := by
    intro s hs inp sc
    have hsPQ : s < (P.seq Q).n := by dsimp [Block.seq]; omega
    have h := hEmb s hsPQ inp sc
    simpa only [Block.seq, ite_eq_left hs] using h
  have hEmbQ : Embeds Q G (fun s => f (P.n + s)) := by
    intro s hs inp sc
    have hsPQ : P.n + s < (P.seq Q).n := by dsimp [Block.seq]; omega
    have h := hEmb (P.n + s) hsPQ inp sc
    have hnot : ¬ (P.n + s < P.n) := by omega
    simpa only [Block.seq, ite_eq_right hnot, Nat.add_sub_cancel_left] using h
  exact (hP G f hEmbP).trans (hQ G (fun s => f (P.n + s)) hEmbQ)

def Block.while1 {k : ℕ} {Sym : Type}
    (cond : Option Bool → (Fin k → Sym) → Bool)
    (bodyAct exitAct : Action k Sym) : Block k Sym where
  n := 1
  hn := le_rfl
  step := fun _ inp sc =>
    if cond inp sc then (0, bodyAct inp sc)
    else (1, exitAct inp sc)
  next_le := by
    intro _ _ inp sc
    by_cases hc : cond inp sc = true
    · rw [ite_eq_left hc]; exact Nat.zero_le 1
    · rw [ite_eq_right hc]

theorem Runs.while1 {k : ℕ} {Sym : Type} {w : List Bool}
    (cond : Option Bool → (Fin k → Sym) → Bool)
    (bodyAct exitAct : Action k Sym) :
    ∀ (N : ℕ) (inv : ℕ → Mem k Sym),
      (∀ i < N,
        cond (readInput w (inv i).inPos)
          (fun t => (inv i).work t ((inv i).workPos t)) = true ∧
        applyAct w bodyAct (inv i) = inv (i + 1)) →
      cond (readInput w (inv N).inPos)
        (fun t => (inv N).work t ((inv N).workPos t)) = false →
      Runs (Block.while1 cond bodyAct exitAct) w (inv 0) (applyAct w exitAct (inv N)) (N + 1)
  | 0, inv, _, hExit => by
    intro G f hEmb
    apply GReach.one
    have h0 := hEmb 0 Nat.zero_lt_one (readInput w (inv 0).inPos)
      (fun t => (inv 0).work t ((inv 0).workPos t))
    have hnot : ¬ (cond (readInput w (inv 0).inPos)
        (fun t => (inv 0).work t ((inv 0).workPos t)) = true) := by
      rw [hExit]; decide
    dsimp only [Block.while1] at h0
    rw [ite_eq_right hnot] at h0
    unfold gStepOne applyAct
    dsimp only [Block.while1]
    rw [h0]
  | N + 1, inv, hStep, hExit => by
    intro G f hEmb
    obtain ⟨hCond0, hNext0⟩ := hStep 0 (Nat.zero_lt_succ N)
    have h1 : gStepOne G w (f 0, inv 0) = some (f 0, inv 1) := by
      have h0 := hEmb 0 Nat.zero_lt_one (readInput w (inv 0).inPos)
        (fun t => (inv 0).work t ((inv 0).workPos t))
      dsimp only [Block.while1] at h0
      rw [ite_eq_left hCond0] at h0
      unfold gStepOne
      dsimp only
      rw [h0, ← hNext0]
      rfl
    have hRest := Runs.while1 cond bodyAct exitAct N (fun i => inv (i + 1))
      (fun i hi => hStep (i + 1) (Nat.add_lt_add_right hi 1))
      hExit G f hEmb
    simpa only [Nat.add_comm 1 (N + 1)] using (GReach.one h1).trans hRest

def Block.loop {k : ℕ} {Sym : Type}
    (cond : Option Bool → (Fin k → Sym) → Bool)
    (enterAct exitAct : Action k Sym)
    (B : Block k Sym) : Block k Sym where
  n := 1 + B.n
  hn := by omega
  step := fun s inp sc =>
    if s = 0 then
      if cond inp sc then (1, enterAct inp sc)
      else (1 + B.n, exitAct inp sc)
    else
      let res := B.step (s - 1) inp sc
      (if res.1 = B.n then 0 else 1 + res.1, res.2)
  next_le := by
    intro s hs inp sc
    have hBn := B.hn
    by_cases hs0 : s = 0
    · rw [ite_eq_left hs0]
      by_cases hc : cond inp sc = true
      · rw [ite_eq_left hc]; omega
      · rw [ite_eq_right hc]
    · rw [ite_eq_right hs0]
      have hnx := B.next_le (s - 1) (by omega) inp sc
      dsimp only
      split_ifs <;> omega

theorem Runs.loop {k : ℕ} {Sym : Type} {w : List Bool}
    (cond : Option Bool → (Fin k → Sym) → Bool)
    (enterAct exitAct : Action k Sym)
    (B : Block k Sym) (tBody : ℕ) :
    ∀ (N : ℕ) (inv : ℕ → Mem k Sym),
      (∀ i < N,
        cond (readInput w (inv i).inPos)
          (fun t => (inv i).work t ((inv i).workPos t)) = true ∧
        Runs B w (applyAct w enterAct (inv i)) (inv (i + 1)) tBody) →
      cond (readInput w (inv N).inPos)
        (fun t => (inv N).work t ((inv N).workPos t)) = false →
      Runs (Block.loop cond enterAct exitAct B) w
        (inv 0) (applyAct w exitAct (inv N)) (N * (1 + tBody) + 1)
  | 0, inv, _, hExit => by
    intro G f hEmb
    have h0lt : 0 < (Block.loop cond enterAct exitAct B).n := by dsimp [Block.loop]; omega
    have h0 := hEmb 0 h0lt (readInput w (inv 0).inPos)
      (fun t => (inv 0).work t ((inv 0).workPos t))
    have hnot : ¬ (cond (readInput w (inv 0).inPos)
        (fun t => (inv 0).work t ((inv 0).workPos t)) = true) := by
      rw [hExit]; decide
    dsimp only [Block.loop] at h0
    rw [ite_eq_left rfl, ite_eq_right hnot] at h0
    have h1 : gStepOne G w (f 0, inv 0) = some (f (1 + B.n), applyAct w exitAct (inv 0)) := by
      unfold gStepOne applyAct
      dsimp only
      rw [h0]
    simpa [Block.loop] using GReach.one h1
  | N + 1, inv, hStep, hExit => by
    intro G f hEmb
    obtain ⟨hCond0, hBody0⟩ := hStep 0 (Nat.zero_lt_succ N)
    have hBn := B.hn
    have h0lt : 0 < (Block.loop cond enterAct exitAct B).n := by dsimp [Block.loop]; omega
    have hEnter : gStepOne G w (f 0, inv 0) = some (f 1, applyAct w enterAct (inv 0)) := by
      have h0 := hEmb 0 h0lt (readInput w (inv 0).inPos)
        (fun t => (inv 0).work t ((inv 0).workPos t))
      dsimp only [Block.loop] at h0
      rw [ite_eq_left rfl, ite_eq_left hCond0] at h0
      unfold gStepOne applyAct
      dsimp only
      rw [h0]
    let g : ℕ → ℕ := fun s => if s = B.n then f 0 else f (1 + s)
    have hEmbB : Embeds B G g := by
      intro s hs inp sc
      have hs1 : 1 + s < (Block.loop cond enterAct exitAct B).n := by dsimp [Block.loop]; omega
      have h := hEmb (1 + s) hs1 inp sc
      have hne0 : 1 + s ≠ 0 := by omega
      have hsne : s ≠ B.n := by omega
      dsimp only [Block.loop] at h
      rw [ite_eq_right hne0, Nat.add_sub_cancel_left] at h
      dsimp only [g]
      rw [ite_eq_right hsne]
      rw [h]
      congr 1
      split_ifs <;> rfl
    have hB0 : GReach G w (f 1, applyAct w enterAct (inv 0)) (f 0, inv 1) tBody := by
      have hg0 : g 0 = f 1 := by dsimp [g]; rw [ite_eq_right (by omega)]
      have hgN : g B.n = f 0 := by dsimp [g]; rw [ite_eq_left rfl]
      rw [← hg0, ← hgN]
      exact hBody0 G g hEmbB
    have hIter0 : GReach G w (f 0, inv 0) (f 0, inv 1) (1 + tBody) :=
      (GReach.one hEnter).trans hB0
    have hRest := Runs.loop cond enterAct exitAct B tBody N (fun i => inv (i + 1))
      (fun i hi => hStep (i + 1) (Nat.add_lt_add_right hi 1))
      hExit G f hEmb
    have hTime : (1 + tBody) + (N * (1 + tBody) + 1) = (N + 1) * (1 + tBody) + 1 := by ring
    rw [← hTime]
    exact hIter0.trans hRest

def natSum : ℕ → (ℕ → ℕ) → ℕ
  | 0, _ => 0
  | n + 1, f => f 0 + natSum n (fun i => f (i + 1))

theorem Runs.loop_sum {k : ℕ} {Sym : Type} {w : List Bool}
    (cond : Option Bool → (Fin k → Sym) → Bool)
    (enterAct exitAct : Action k Sym)
    (B : Block k Sym) :
    ∀ (N : ℕ) (tBody : ℕ → ℕ) (inv : ℕ → Mem k Sym),
      (∀ i < N,
        cond (readInput w (inv i).inPos)
          (fun t => (inv i).work t ((inv i).workPos t)) = true ∧
        Runs B w (applyAct w enterAct (inv i)) (inv (i + 1)) (tBody i)) →
      cond (readInput w (inv N).inPos)
        (fun t => (inv N).work t ((inv N).workPos t)) = false →
      Runs (Block.loop cond enterAct exitAct B) w
        (inv 0) (applyAct w exitAct (inv N)) (natSum N (fun i => 1 + tBody i) + 1)
  | 0, _, inv, _, hExit => by
    simpa [natSum] using Runs.loop cond enterAct exitAct B 0 0 inv
      (fun _ h => absurd h (Nat.not_lt_zero _)) hExit
  | N + 1, tBody, inv, hStep, hExit => by
    intro G f hEmb
    obtain ⟨hCond0, hBody0⟩ := hStep 0 (Nat.zero_lt_succ N)
    have h0lt : 0 < (Block.loop cond enterAct exitAct B).n := by dsimp [Block.loop]; omega
    have hEnter : gStepOne G w (f 0, inv 0) = some (f 1, applyAct w enterAct (inv 0)) := by
      have h0 := hEmb 0 h0lt (readInput w (inv 0).inPos)
        (fun t => (inv 0).work t ((inv 0).workPos t))
      dsimp only [Block.loop] at h0
      rw [ite_eq_left rfl, ite_eq_left hCond0] at h0
      unfold gStepOne applyAct; dsimp only; rw [h0]
    let g : ℕ → ℕ := fun s => if s = B.n then f 0 else f (1 + s)
    have hEmbB : Embeds B G g := by
      intro s hs inp sc
      have hs1 : 1 + s < (Block.loop cond enterAct exitAct B).n := by dsimp [Block.loop]; omega
      have h := hEmb (1 + s) hs1 inp sc
      have hne0 : 1 + s ≠ 0 := by omega
      have hsne : s ≠ B.n := by omega
      dsimp only [Block.loop] at h
      rw [ite_eq_right hne0, Nat.add_sub_cancel_left] at h
      dsimp only [g]; rw [ite_eq_right hsne, h]
      congr 1; split_ifs <;> rfl
    have hB0 : GReach G w (f 1, applyAct w enterAct (inv 0)) (f 0, inv 1) (tBody 0) := by
      have hg0 : g 0 = f 1 := by dsimp [g]; rw [ite_eq_right (by have := B.hn; omega)]
      have hgN : g B.n = f 0 := by dsimp [g]; rw [ite_eq_left rfl]
      rw [← hg0, ← hgN]
      exact hBody0 G g hEmbB
    have hIter0 : GReach G w (f 0, inv 0) (f 0, inv 1) (1 + tBody 0) :=
      (GReach.one hEnter).trans hB0
    have hRest := Runs.loop_sum cond enterAct exitAct B N (fun i => tBody (i + 1))
      (fun i => inv (i + 1))
      (fun i hi => hStep (i + 1) (Nat.add_lt_add_right hi 1))
      hExit G f hEmb
    simpa only [natSum, Nat.add_assoc] using hIter0.trans hRest

def Block.branch {k : ℕ} {Sym : Type}
    (cond : Option Bool → (Fin k → Sym) → Bool)
    (trueAct falseAct : Action k Sym)
    (T F : Block k Sym) : Block k Sym where
  n := 1 + T.n + F.n
  hn := by omega
  step := fun s inp sc =>
    if s = 0 then
      if cond inp sc then (1, trueAct inp sc)
      else (1 + T.n, falseAct inp sc)
    else if s < 1 + T.n then
      let res := T.step (s - 1) inp sc
      (if res.1 = T.n then 1 + T.n + F.n else 1 + res.1, res.2)
    else
      let res := F.step (s - (1 + T.n)) inp sc
      (1 + T.n + res.1, res.2)
  next_le := by
    intro s hs inp sc
    have hTn := T.hn; have hFn := F.hn
    by_cases hs0 : s = 0
    · rw [ite_eq_left hs0]
      by_cases hc : cond inp sc = true
      · rw [ite_eq_left hc]; dsimp only; omega
      · rw [ite_eq_right hc]; dsimp only; omega
    · rw [ite_eq_right hs0]
      by_cases hltT : s < 1 + T.n
      · rw [ite_eq_left hltT]
        have hnx := T.next_le (s - 1) (by omega) inp sc
        dsimp only; split_ifs <;> omega
      · rw [ite_eq_right hltT]
        have hnx := F.next_le (s - (1 + T.n)) (by omega) inp sc
        dsimp only; omega

theorem Runs.branch_true {k : ℕ} {Sym : Type} {w : List Bool}
    {cond : Option Bool → (Fin k → Sym) → Bool}
    {trueAct falseAct : Action k Sym} {T F : Block k Sym}
    {m₀ m₂ : Mem k Sym} {t : ℕ}
    (hCond : cond (readInput w m₀.inPos) (fun i => m₀.work i (m₀.workPos i)) = true)
    (hT : Runs T w (applyAct w trueAct m₀) m₂ t) :
    Runs (Block.branch cond trueAct falseAct T F) w m₀ m₂ (1 + t) := by
  intro G f hEmb
  have hTn := T.hn; have hFn := F.hn
  have h0lt : 0 < (Block.branch cond trueAct falseAct T F).n := by dsimp [Block.branch]; omega
  have hEnter : gStepOne G w (f 0, m₀) = some (f 1, applyAct w trueAct m₀) := by
    have h0 := hEmb 0 h0lt (readInput w m₀.inPos) (fun i => m₀.work i (m₀.workPos i))
    dsimp only [Block.branch] at h0
    rw [ite_eq_left rfl, ite_eq_left hCond] at h0
    unfold gStepOne applyAct; dsimp only; rw [h0]
  let g : ℕ → ℕ := fun s => if s = T.n then f (1 + T.n + F.n) else f (1 + s)
  have hEmbT : Embeds T G g := by
    intro s hs inp sc
    have hsB : 1 + s < (Block.branch cond trueAct falseAct T F).n := by dsimp [Block.branch]; omega
    have h := hEmb (1 + s) hsB inp sc
    have hne0 : 1 + s ≠ 0 := by omega
    have hltT : 1 + s < 1 + T.n := by omega
    have hsne : s ≠ T.n := by omega
    dsimp only [Block.branch] at h
    rw [ite_eq_right hne0, ite_eq_left hltT, Nat.add_sub_cancel_left] at h
    dsimp only [g]; rw [ite_eq_right hsne, h]
    congr 1; split_ifs <;> rfl
  have hRunT : GReach G w (f 1, applyAct w trueAct m₀) (f (1 + T.n + F.n), m₂) t := by
    have hg0 : g 0 = f 1 := by dsimp [g]; rw [ite_eq_right (by omega)]
    have hgN : g T.n = f (1 + T.n + F.n) := by dsimp [g]; rw [ite_eq_left rfl]
    rw [← hg0, ← hgN]
    exact hT G g hEmbT
  exact (GReach.one hEnter).trans hRunT

theorem Runs.branch_false {k : ℕ} {Sym : Type} {w : List Bool}
    {cond : Option Bool → (Fin k → Sym) → Bool}
    {trueAct falseAct : Action k Sym} {T F : Block k Sym}
    {m₀ m₂ : Mem k Sym} {t : ℕ}
    (hCond : cond (readInput w m₀.inPos) (fun i => m₀.work i (m₀.workPos i)) = false)
    (hF : Runs F w (applyAct w falseAct m₀) m₂ t) :
    Runs (Block.branch cond trueAct falseAct T F) w m₀ m₂ (1 + t) := by
  intro G f hEmb
  have hTn := T.hn; have hFn := F.hn
  have h0lt : 0 < (Block.branch cond trueAct falseAct T F).n := by dsimp [Block.branch]; omega
  have hEnter : gStepOne G w (f 0, m₀) = some (f (1 + T.n), applyAct w falseAct m₀) := by
    have h0 := hEmb 0 h0lt (readInput w m₀.inPos) (fun i => m₀.work i (m₀.workPos i))
    have hnot : ¬ (cond (readInput w m₀.inPos) (fun i => m₀.work i (m₀.workPos i)) = true) := by
      rw [hCond]; decide
    dsimp only [Block.branch] at h0
    rw [ite_eq_left rfl, ite_eq_right hnot] at h0
    unfold gStepOne applyAct; dsimp only; rw [h0]
  let g : ℕ → ℕ := fun s => f (1 + T.n + s)
  have hEmbF : Embeds F G g := by
    intro s hs inp sc
    have hsB : 1 + T.n + s < (Block.branch cond trueAct falseAct T F).n := by
      dsimp [Block.branch]; omega
    have h := hEmb (1 + T.n + s) hsB inp sc
    have hne0 : 1 + T.n + s ≠ 0 := by omega
    have hnltT : ¬ (1 + T.n + s < 1 + T.n) := by omega
    dsimp only [Block.branch] at h
    rw [ite_eq_right hne0, ite_eq_right hnltT, Nat.add_sub_cancel_left] at h
    exact h
  exact (GReach.one hEnter).trans (hF G g hEmbF)

def Block.toTM {k g : ℕ} {Sym : Type}
    (encSym : Sym → Fin (g + 1)) (decSym : Fin (g + 1) → Sym)
    (B : Block k Sym) : DetTM where
  k := k
  g := g
  q := B.n
  δ := fun s inp sc =>
    if hs : s.val < B.n then
      let res := B.step s.val inp (fun i => decSym (sc i))
      have hnx : res.1 < B.n + 1 := Nat.lt_succ_of_le (B.next_le s.val hs inp _)
      some (⟨res.1, hnx⟩, res.2.1, fun i => (encSym (res.2.2.1 i).1, (res.2.2.1 i).2), res.2.2.2)
    else
      none

theorem Block.computesWithin {k g : ℕ} {Sym : Type}
    (blank : Sym)
    (encSym : Sym → Fin (g + 1)) (decSym : Fin (g + 1) → Sym)
    (hSym : ∀ a, decSym (encSym a) = a)
    (hBlank : encSym blank = 0)
    (B : Block k Sym)
    {w out : List Bool} {mHalt : Mem k Sym} {t : ℕ}
    (hRun : Runs B w
      { inPos := 0, work := fun _ _ => blank, workPos := fun _ => 0, outRev := [] }
      mHalt t)
    (hOut : mHalt.outRev.reverse = out) :
    ComputesWithin (B.toTM encSym decSym) w out t := by
  let G : GStep k Sym := fun s inp sc =>
    if s < B.n then some (B.step s inp sc) else none
  have hEmb : Embeds B G id := by
    intro s hs inp sc
    dsimp only [G, id]
    rw [ite_eq_left hs]
  let m0 : Mem k Sym :=
    { inPos := 0, work := fun _ _ => blank, workPos := fun _ => 0, outRev := [] }
  obtain ⟨steps, hsteps_le, hGstepN⟩ := hRun G id hEmb
  let toCfg (s : ℕ) (hs : s < B.n + 1) (m : Mem k Sym) :
      Config (B.toTM encSym decSym) :=
    { state   := ⟨s, hs⟩
      inPos   := m.inPos
      work    := fun i p => encSym (m.work i p)
      workPos := m.workPos
      outRev  := m.outRev }
  have hOne : ∀ (s : ℕ) (hs : s < B.n + 1) (m : Mem k Sym) (s' : ℕ) (m' : Mem k Sym),
      gStepOne G w (s, m) = some (s', m') →
      ∃ hs' : s' < B.n + 1,
        ShuffleShear.step (B.toTM encSym decSym) w (toCfg s hs m) = some (toCfg s' hs' m') := by
    intro s hs m s' m' h1
    unfold gStepOne G at h1
    dsimp only at h1
    by_cases hsB : s < B.n
    · rw [ite_eq_left hsB] at h1
      simp only [Option.some.injEq, Prod.mk.injEq] at h1
      rcases h1 with ⟨rfl, rfl⟩
      have hnx : (B.step s (readInput w m.inPos) (fun i => m.work i (m.workPos i))).1 <
          B.n + 1 :=
        Nat.lt_succ_of_le (B.next_le s hsB _ _)
      refine ⟨hnx, ?_⟩
      unfold ShuffleShear.step toCfg Block.toTM
      dsimp only
      rw [dite_eq_left hsB]
      have hsc : (fun i => decSym (encSym (m.work i (m.workPos i)))) =
          (fun i => m.work i (m.workPos i)) := by
        funext i; exact hSym _
      dsimp only
      congr 1
      rw [Config.mk.injEq]
      refine ⟨Fin.ext (by dsimp only; rw [hsc]), ?_, ?_, ?_, ?_⟩
      · rw [hsc]
      · funext i p
        rw [hsc]
        split_ifs <;> rfl
      · funext i
        rw [hsc]
      · rw [hsc]
    · rw [ite_eq_right hsB] at h1
      cases h1
  have hMany : ∀ (n : ℕ) (s : ℕ) (hs : s < B.n + 1) (m : Mem k Sym) (s' : ℕ) (m' : Mem k Sym),
      gStepN G w n (s, m) = some (s', m') →
      ∃ hs' : s' < B.n + 1,
        ShuffleShear.stepN (B.toTM encSym decSym) w n (toCfg s hs m) = some (toCfg s' hs' m') := by
    intro n
    induction n with
    | zero =>
      intro s hs m s' m' h0
      simp only [gStepN, Option.some.injEq, Prod.mk.injEq] at h0
      rcases h0 with ⟨rfl, rfl⟩
      exact ⟨hs, rfl⟩
    | succ n ih =>
      intro s hs m s' m' hsn
      simp only [gStepN] at hsn
      cases hg1 : gStepOne G w (s, m) with
      | none => rw [hg1] at hsn; cases hsn
      | some cm1 =>
        rw [hg1] at hsn
        rcases cm1 with ⟨s1, m1⟩
        obtain ⟨hs1, htm1⟩ := hOne s hs m s1 m1 hg1
        obtain ⟨hs', htmN⟩ := ih s1 hs1 m1 s' m' hsn
        refine ⟨hs', ?_⟩
        simp only [ShuffleShear.stepN, htm1, htmN]
  have h0lt : 0 < B.n + 1 := Nat.zero_lt_succ B.n
  obtain ⟨hNlt, hStepNM⟩ := hMany steps 0 h0lt m0 B.n mHalt hGstepN
  have hInitEq : toCfg 0 h0lt m0 = ShuffleShear.init (B.toTM encSym decSym) := by
    unfold toCfg m0 ShuffleShear.init Block.toTM
    dsimp only
    rw [Config.mk.injEq]
    refine ⟨rfl, rfl, ?_, rfl, rfl⟩
    funext i p; exact hBlank
  have hHaltEq : ShuffleShear.step (B.toTM encSym decSym) w (toCfg B.n hNlt mHalt) = none := by
    unfold ShuffleShear.step toCfg Block.toTM
    dsimp only
    have hnot : ¬ (B.n < B.n) := lt_irrefl _
    rw [dite_eq_right hnot]
  refine ⟨steps, hsteps_le, toCfg B.n hNlt mHalt, ?_, hHaltEq, hOut⟩
  rw [← hInitEq]
  exact hStepNM

theorem natSum_le_of_step :
    ∀ {N : ℕ} {f g : ℕ → ℕ},
      (∀ i < N, f i + g i ≤ g (i + 1)) →
      natSum N f + g 0 ≤ g N
  | 0, _, _, _ => by simp [natSum]
  | N + 1, f, g, hstep => by
    have h0 := hstep 0 (Nat.zero_lt_succ N)
    have hrest := natSum_le_of_step (N := N) (f := fun i => f (i + 1)) (g := fun i => g (i + 1))
      (fun i hi => hstep (i + 1) (Nat.add_lt_add_right hi 1))
    dsimp only [natSum]
    omega

/-! ### 3. Work Alphabet, Generic Tape Primitives & `discoverEntryBits` -/

inductive WorkSym where
  | blank
  | b0
  | b1
  | u
  | wall
  | oddD
  | oddAux
  | save
  | emitStart
  | emitCont
  deriving DecidableEq, Repr

def encWorkSym : WorkSym → Fin 10
  | .blank     => 0
  | .b0        => 1
  | .b1        => 2
  | .u         => 3
  | .wall      => 4
  | .oddD      => 5
  | .oddAux    => 6
  | .save      => 7
  | .emitStart => 8
  | .emitCont  => 9

def decWorkSym : Fin 10 → WorkSym
  | ⟨0, _⟩ => .blank
  | ⟨1, _⟩ => .b0
  | ⟨2, _⟩ => .b1
  | ⟨3, _⟩ => .u
  | ⟨4, _⟩ => .wall
  | ⟨5, _⟩ => .oddD
  | ⟨6, _⟩ => .oddAux
  | ⟨7, _⟩ => .save
  | ⟨8, _⟩ => .emitStart
  | ⟨9, _⟩ => .emitCont

theorem decWorkSym_encWorkSym (a : WorkSym) : decWorkSym (encWorkSym a) = a := by
  cases a <;> rfl

theorem encWorkSym_blank : encWorkSym .blank = 0 := rfl

def bitSym : Bool → WorkSym
  | false => .b0
  | true  => .b1

def symBit : WorkSym → Option Bool
  | .b0 => some false
  | .b1 => some true
  | _   => none

theorem symBit_bitSym (b : Bool) : symBit (bitSym b) = some b := by
  cases b <;> rfl

theorem bitSym_ne_blank (b : Bool) : bitSym b ≠ .blank := by
  cases b <;> decide

def unaryTape (N : ℕ) : Int → WorkSym :=
  fun p => if 0 ≤ p ∧ p < (N : Int) then .u else .blank

theorem unaryTape_zero : unaryTape 0 = fun _ => .blank := by
  funext p
  unfold unaryTape
  split_ifs with h <;> first | rfl | omega

theorem unaryTape_lt {N i : ℕ} (hi : i < N) : unaryTape N (i : Int) = .u := by
  unfold unaryTape
  have h : 0 ≤ (i : Int) ∧ (i : Int) < (N : Int) := by omega
  rw [ite_eq_left h]

theorem unaryTape_ge {N : ℕ} {p : Int} (hp : (N : Int) ≤ p) : unaryTape N p = .blank := by
  unfold unaryTape
  have h : ¬ (0 ≤ p ∧ p < (N : Int)) := by omega
  rw [ite_eq_right h]

theorem unaryTape_neg {N : ℕ} {p : Int} (hp : p < 0) : unaryTape N p = .blank := by
  unfold unaryTape
  have h : ¬ (0 ≤ p ∧ p < (N : Int)) := by omega
  rw [ite_eq_right h]

theorem unaryTape_write_end (N : ℕ) :
    (fun p : Int => if p = (N : Int) then WorkSym.u else unaryTape N p) = unaryTape (N + 1) := by
  funext p
  unfold unaryTape
  by_cases hp : p = (N : Int)
  · subst hp
    have h2 : 0 ≤ (N : Int) ∧ (N : Int) < ((N + 1 : ℕ) : Int) := by omega
    simp [h2]
  · rw [ite_eq_right hp]
    by_cases h1 : 0 ≤ p ∧ p < (N : Int)
    · have h2 : 0 ≤ p ∧ p < ((N + 1 : ℕ) : Int) := by omega
      rw [ite_eq_left h1, ite_eq_left h2]
    · have h2 : ¬ (0 ≤ p ∧ p < ((N + 1 : ℕ) : Int)) := by omega
      rw [ite_eq_right h1, ite_eq_right h2]

def wordTape (xs : List Bool) : Int → WorkSym :=
  fun p =>
    if 0 ≤ p then
      match xs[p.toNat]? with
      | some b => bitSym b
      | none   => .blank
    else .blank

theorem wordTape_nil : wordTape [] = fun _ => .blank := by
  funext p; unfold wordTape; split_ifs <;> simp

theorem wordTape_lt {xs : List Bool} {i : ℕ} {b : Bool} (hb : xs[i]? = some b) :
    wordTape xs (i : Int) = bitSym b := by
  unfold wordTape
  have h0 : 0 ≤ (i : Int) := by omega
  rw [ite_eq_left h0, Int.toNat_natCast, hb]

theorem wordTape_ge {xs : List Bool} {p : Int} (hp : (xs.length : Int) ≤ p) :
    wordTape xs p = .blank := by
  unfold wordTape
  by_cases h0 : 0 ≤ p
  · rw [ite_eq_left h0]
    have hge : xs.length ≤ p.toNat := by omega
    rw [List.getElem?_eq_none hge]
  · rw [ite_eq_right h0]

theorem wordTape_neg {xs : List Bool} {p : Int} (hp : p < 0) :
    wordTape xs p = .blank := by
  unfold wordTape
  rw [ite_eq_right (by omega)]

theorem wordTape_take_succ {xs : List Bool} {i : ℕ} {b : Bool} (hb : xs[i]? = some b) :
    (fun p : Int => if p = (i : Int) then bitSym b else wordTape (xs.take i) p) =
      wordTape (xs.take (i + 1)) := by
  have hi_lt : i < xs.length := by
    by_contra hge
    rw [List.getElem?_eq_none (Nat.le_of_not_gt hge)] at hb
    cases hb
  funext p
  by_cases hp : p = (i : Int)
  · subst hp
    rw [ite_eq_left rfl]
    have hget : (xs.take (i + 1))[i]? = some b := by
      rw [List.getElem?_take_of_lt (Nat.lt_succ_self i), hb]
    exact (wordTape_lt hget).symm
  · rw [ite_eq_right hp]
    unfold wordTape
    by_cases h0 : 0 ≤ p
    · rw [ite_eq_left h0, ite_eq_left h0]
      by_cases hpi : p.toNat < i
      · rw [List.getElem?_take_of_lt hpi, List.getElem?_take_of_lt (Nat.lt_succ_of_lt hpi)]
      · have hpge : i + 1 ≤ p.toNat := by omega
        have hlen1 : (xs.take i).length ≤ p.toNat := by simp; omega
        have hlen2 : (xs.take (i + 1)).length ≤ p.toNat := by simp; omega
        rw [List.getElem?_eq_none hlen1, List.getElem?_eq_none hlen2]
    · rw [ite_eq_right h0, ite_eq_right h0]

theorem bne_blank_of_ne {a : WorkSym} (h : a ≠ .blank) : (a != .blank) = true := by
  cases a <;> first | exact absurd rfl h | rfl

def actStay {k : ℕ} : Action k WorkSym :=
  fun _ sc => (.stay, fun i => (sc i, .stay), none)

theorem applyAct_actStay {k : ℕ} (w : List Bool) (m : Mem k WorkSym) :
    applyAct w actStay m = m := by
  unfold applyAct actStay
  refine Mem.eq_of_fields rfl (fun i p => ?_) (fun _ => rfl) rfl
  dsimp only
  by_cases hp : p = m.workPos i
  · subst hp; simp
  · rw [ite_eq_right hp]

def mkAct1 {k : ℕ} (t₀ : Fin k)
    (inDir : Option Bool → WorkSym → Dir)
    (wAct : Option Bool → WorkSym → WorkSym × Dir)
    (outBit : Option Bool → WorkSym → Option Bool) : Action k WorkSym :=
  fun inp sc =>
    (inDir inp (sc t₀),
     fun i => if i = t₀ then wAct inp (sc t₀) else (sc i, .stay),
     outBit inp (sc t₀))

theorem applyAct_mkAct1 {k : ℕ} (w : List Bool) (m : Mem k WorkSym) (t₀ : Fin k)
    (inDir : Option Bool → WorkSym → Dir)
    (wAct : Option Bool → WorkSym → WorkSym × Dir)
    (outBit : Option Bool → WorkSym → Option Bool) :
    let inp := readInput w m.inPos
    let s₀ := m.work t₀ (m.workPos t₀)
    applyAct w (mkAct1 t₀ inDir wAct outBit) m =
      { inPos   := (inDir inp s₀).shift m.inPos
        work    := fun i p =>
          if i = t₀ then (if p = m.workPos t₀ then (wAct inp s₀).1 else m.work t₀ p)
          else m.work i p
        workPos := fun i => if i = t₀ then (wAct inp s₀).2.shift (m.workPos t₀) else m.workPos i
        outRev  := match outBit inp s₀ with | none => m.outRev | some b => b :: m.outRev } := by
  dsimp only
  unfold applyAct mkAct1
  refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
  · dsimp only
    by_cases hi : i = t₀
    · subst hi; simp
    · simp only [hi, ↓reduceIte]
      by_cases hp : p = m.workPos i
      · subst hp; simp
      · rw [ite_eq_right hp]
  · dsimp only
    by_cases hi : i = t₀
    · subst hi; simp
    · simp [hi, Dir.shift]

def mkAct2 {k : ℕ} (t₀ t₁ : Fin k)
    (inDir : Option Bool → WorkSym → WorkSym → Dir)
    (wAct₀ wAct₁ : Option Bool → WorkSym → WorkSym → WorkSym × Dir)
    (outBit : Option Bool → WorkSym → WorkSym → Option Bool) : Action k WorkSym :=
  fun inp sc =>
    (inDir inp (sc t₀) (sc t₁),
     fun i =>
       if i = t₀ then wAct₀ inp (sc t₀) (sc t₁)
       else if i = t₁ then wAct₁ inp (sc t₀) (sc t₁)
       else (sc i, .stay),
     outBit inp (sc t₀) (sc t₁))

theorem applyAct_mkAct2 {k : ℕ} (w : List Bool) (m : Mem k WorkSym) {t₀ t₁ : Fin k}
    (hne : t₀ ≠ t₁)
    (inDir : Option Bool → WorkSym → WorkSym → Dir)
    (wAct₀ wAct₁ : Option Bool → WorkSym → WorkSym → WorkSym × Dir)
    (outBit : Option Bool → WorkSym → WorkSym → Option Bool) :
    let inp := readInput w m.inPos
    let s₀ := m.work t₀ (m.workPos t₀)
    let s₁ := m.work t₁ (m.workPos t₁)
    applyAct w (mkAct2 t₀ t₁ inDir wAct₀ wAct₁ outBit) m =
      { inPos   := (inDir inp s₀ s₁).shift m.inPos
        work    := fun i p =>
          if i = t₀ then (if p = m.workPos t₀ then (wAct₀ inp s₀ s₁).1 else m.work t₀ p)
          else if i = t₁ then (if p = m.workPos t₁ then (wAct₁ inp s₀ s₁).1 else m.work t₁ p)
          else m.work i p
        workPos := fun i =>
          if i = t₀ then (wAct₀ inp s₀ s₁).2.shift (m.workPos t₀)
          else if i = t₁ then (wAct₁ inp s₀ s₁).2.shift (m.workPos t₁)
          else m.workPos i
        outRev  := match outBit inp s₀ s₁ with | none => m.outRev | some b => b :: m.outRev } := by
  dsimp only
  unfold applyAct mkAct2
  refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
  · dsimp only
    by_cases hi0 : i = t₀
    · subst hi0; simp
    · by_cases hi1 : i = t₁
      · subst hi1; simp [Ne.symm hne]
      · simp only [hi0, hi1, ↓reduceIte]
        by_cases hp : p = m.workPos i
        · subst hp; simp
        · rw [ite_eq_right hp]
  · dsimp only
    by_cases hi0 : i = t₀
    · subst hi0; simp
    · by_cases hi1 : i = t₁
      · subst hi1; simp [hi0]
      · simp [hi0, hi1, Dir.shift]

theorem ite_self_cell {Sym : Type} (f : Int → Sym) (q : Int) :
    (fun p => if p = q then f q else f p) = f := by
  funext p
  by_cases hp : p = q
  · subst hp; simp
  · rw [ite_eq_right hp]

def stepDirAct {k : ℕ} (t₀ : Fin k) (d : Dir) : Action k WorkSym :=
  mkAct1 t₀ (fun _ _ => .stay) (fun _ s => (s, d)) (fun _ _ => none)

def writeDirAct {k : ℕ} (t₀ : Fin k) (sym : WorkSym) (d : Dir) : Action k WorkSym :=
  mkAct1 t₀ (fun _ _ => .stay) (fun _ _ => (sym, d)) (fun _ _ => none)

def inStepDirAct {k : ℕ} (d : Dir) : Action k WorkSym :=
  fun _ sc => (d, fun i => (sc i, .stay), none)

theorem applyAct_inStepDir {k : ℕ} (w : List Bool) (m : Mem k WorkSym) (d : Dir) :
    applyAct w (inStepDirAct d) m = { m with inPos := d.shift m.inPos } := by
  unfold applyAct inStepDirAct
  refine Mem.eq_of_fields rfl (fun i p => ?_) (fun _ => rfl) rfl
  dsimp only
  by_cases hp : p = m.workPos i
  · subst hp; simp
  · rw [ite_eq_right hp]

/-- Rewind tape `t₀` from `workPos t₀ = N` back to `0` across non-blank `[0, N)` with blank `-1`. -/
def rewindFromEnd {k : ℕ} (t₀ : Fin k) : Block k WorkSym :=
  (Block.act (stepDirAct t₀ .left)).seq
    (Block.while1 (fun _ sc => sc t₀ != .blank)
      (stepDirAct t₀ .left) (stepDirAct t₀ .right))

theorem Runs_rewindFromEnd {k : ℕ} {w : List Bool} (t₀ : Fin k)
    (m : Mem k WorkSym) (N : ℕ)
    (hPos : m.workPos t₀ = (N : Int))
    (hNonBlank : ∀ j < N, m.work t₀ (j : Int) ≠ .blank)
    (hNeg1 : m.work t₀ (-1) = .blank) :
    Runs (rewindFromEnd t₀) w m
      { m with workPos := fun i => if i = t₀ then 0 else m.workPos i } (N + 2) := by
  unfold rewindFromEnd
  let mAt (q : Int) : Mem k WorkSym :=
    { m with workPos := fun i => if i = t₀ then q else m.workPos i }
  have hFirst : applyAct w (stepDirAct t₀ .left) m = mAt ((N : Int) - 1) := by
    unfold stepDirAct
    rw [applyAct_mkAct1]
    refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
    · dsimp only [mAt]
      by_cases hi : i = t₀
      · subst hi; simp only [↓reduceIte]; exact congrFun (ite_self_cell (m.work i) (m.workPos i)) p
      · simp [hi]
    · dsimp only [mAt, Dir.shift]
      by_cases hi : i = t₀
      · subst hi; simp [hPos]
      · simp [hi]
  have h1 : Runs (Block.act (stepDirAct t₀ .left)) w m (mAt ((N : Int) - 1)) 1 := by
    rw [← hFirst]; exact Runs.act _ m
  let inv (j : ℕ) : Mem k WorkSym := mAt ((N : Int) - 1 - (j : Int))
  have hInv0 : mAt ((N : Int) - 1) = inv 0 := by
    refine Mem.eq_of_fields rfl (fun _ _ => rfl) (fun i => ?_) rfl
    dsimp only [inv, mAt]
    by_cases hi : i = t₀
    · subst hi; simp
    · simp [hi]
  have hLoop := Runs.while1 (w := w)
    (fun _ (sc : Fin k → WorkSym) => sc t₀ != .blank)
    (stepDirAct t₀ .left) (stepDirAct t₀ .right) N inv
    (fun j hj => by
      have hidx : (N : Int) - 1 - (j : Int) = ((N - 1 - j : ℕ) : Int) := by omega
      have hcell : (inv j).work t₀ ((inv j).workPos t₀) ≠ .blank := by
        dsimp only [inv, mAt]; simp only [↓reduceIte]
        rw [hidx]
        exact hNonBlank (N - 1 - j) (by omega)
      refine ⟨bne_blank_of_ne hcell, ?_⟩
      unfold stepDirAct
      rw [applyAct_mkAct1]
      refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
      · dsimp only [inv, mAt]
        by_cases hi : i = t₀
        · subst hi; simp only [↓reduceIte]; exact congrFun (ite_self_cell (m.work i) _) p
        · simp [hi]
      · dsimp only [inv, mAt, Dir.shift]
        by_cases hi : i = t₀
        · subst hi; simp only [↓reduceIte]; omega
        · simp [hi])
    (by
      dsimp only [inv, mAt]; simp only [↓reduceIte]
      have hm1 : (N : Int) - 1 - (N : Int) = -1 := by omega
      rw [hm1, hNeg1]; rfl)
  have hExitEq : applyAct w (stepDirAct t₀ .right) (inv N) = mAt 0 := by
    unfold stepDirAct
    rw [applyAct_mkAct1]
    refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
    · dsimp only [inv, mAt]
      by_cases hi : i = t₀
      · subst hi; simp only [↓reduceIte]; exact congrFun (ite_self_cell (m.work i) _) p
      · simp [hi]
    · dsimp only [inv, mAt, Dir.shift]
      by_cases hi : i = t₀
      · subst hi; simp only [↓reduceIte]; omega
      · simp [hi]
  rw [← hInv0, hExitEq] at hLoop
  have hTime : 1 + (N + 1) = N + 2 := by omega
  rw [← hTime]
  exact h1.seq hLoop

/-- Erase `[0, N)` on tape `t₀` starting from `workPos t₀ = N` and return head to `0`. -/
def eraseFromEnd {k : ℕ} (t₀ : Fin k) : Block k WorkSym :=
  (Block.act (stepDirAct t₀ .left)).seq
    (Block.while1 (fun _ sc => sc t₀ != .blank)
      (writeDirAct t₀ .blank .left) (stepDirAct t₀ .right))

theorem Runs_eraseFromEnd {k : ℕ} {w : List Bool} (t₀ : Fin k)
    (m : Mem k WorkSym) (N : ℕ)
    (hPos : m.workPos t₀ = (N : Int))
    (hNonBlank : ∀ j < N, m.work t₀ (j : Int) ≠ .blank)
    (hOutside : ∀ p : Int, (p < 0 ∨ (N : Int) ≤ p) → m.work t₀ p = .blank) :
    Runs (eraseFromEnd t₀) w m
      { m with
        work    := fun i p => if i = t₀ then .blank else m.work i p
        workPos := fun i => if i = t₀ then 0 else m.workPos i } (N + 2) := by
  unfold eraseFromEnd
  let inv (j : ℕ) : Mem k WorkSym :=
    { m with
      work := fun i p =>
        if i = t₀ then
          if (N : Int) - (j : Int) ≤ p then .blank else m.work t₀ p
        else m.work i p
      workPos := fun i => if i = t₀ then (N : Int) - 1 - (j : Int) else m.workPos i }
  have hFirst : applyAct w (stepDirAct t₀ .left) m = inv 0 := by
    unfold stepDirAct
    rw [applyAct_mkAct1]
    refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
    · dsimp only [inv]
      by_cases hi : i = t₀
      · subst hi
        simp only [↓reduceIte]
        rw [congrFun (ite_self_cell (m.work i) (m.workPos i)) p]
        split_ifs with hge
        · exact hOutside p (Or.inr (by omega))
        · rfl
      · simp [hi]
    · dsimp only [inv, Dir.shift]
      by_cases hi : i = t₀
      · subst hi; simp [hPos]
      · simp [hi]
  have h1 : Runs (Block.act (stepDirAct t₀ .left)) w m (inv 0) 1 := by
    rw [← hFirst]; exact Runs.act _ m
  have hLoop := Runs.while1 (w := w)
    (fun _ (sc : Fin k → WorkSym) => sc t₀ != .blank)
    (writeDirAct t₀ .blank .left) (stepDirAct t₀ .right) N inv
    (fun j hj => by
      have hidx : (N : Int) - 1 - (j : Int) = ((N - 1 - j : ℕ) : Int) := by omega
      have hnotge : ¬ ((N : Int) - (j : Int) ≤ (N : Int) - 1 - (j : Int)) := by omega
      have hcell : (inv j).work t₀ ((inv j).workPos t₀) ≠ .blank := by
        dsimp only [inv]; simp only [↓reduceIte]
        rw [ite_eq_right hnotge, hidx]
        exact hNonBlank (N - 1 - j) (by omega)
      refine ⟨bne_blank_of_ne hcell, ?_⟩
      unfold writeDirAct
      rw [applyAct_mkAct1]
      refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
      · dsimp only [inv]
        by_cases hi : i = t₀
        · subst hi
          simp only [↓reduceIte]
          split_ifs <;> first | rfl | omega
        · simp [hi]
      · dsimp only [inv, Dir.shift]
        by_cases hi : i = t₀
        · subst hi; simp only [↓reduceIte]; omega
        · simp [hi])
    (by
      dsimp only [inv]; simp only [↓reduceIte]
      have hnot : ¬ ((N : Int) - (N : Int) ≤ (N : Int) - 1 - (N : Int)) := by omega
      rw [ite_eq_right hnot]
      have hm1 : (N : Int) - 1 - (N : Int) = -1 := by omega
      rw [hm1, hOutside (-1) (Or.inl (by omega))]; rfl)
  have hExit : applyAct w (stepDirAct t₀ .right) (inv N) =
      { m with
        work    := fun i p => if i = t₀ then .blank else m.work i p
        workPos := fun i => if i = t₀ then 0 else m.workPos i } := by
    unfold stepDirAct
    rw [applyAct_mkAct1]
    refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
    · dsimp only [inv]
      by_cases hi : i = t₀
      · subst hi
        simp only [↓reduceIte]
        split_ifs
        · rfl
        · exact hOutside _ (Or.inl (by omega))
        · rfl
        · exact hOutside p (Or.inl (by omega))
      · simp [hi]
    · dsimp only [inv, Dir.shift]
      by_cases hi : i = t₀
      · subst hi; simp only [↓reduceIte]; omega
      · simp [hi]
  rw [hExit] at hLoop
  have hTime : 1 + (N + 1) = N + 2 := by omega
  rw [← hTime]
  exact h1.seq hLoop

/-- Rewind `inPos` from `(P : Int)` (`P ≤ w.length`) back to `0` without touching work tapes. -/
def rewindInputFromPos {k : ℕ} : Block k WorkSym :=
  (Block.act (inStepDirAct .left)).seq
    (Block.while1 (fun inp _ => inp.isSome) (inStepDirAct .left) (inStepDirAct .right))

theorem Runs_rewindInputFromPos {k : ℕ} {w : List Bool}
    (m : Mem k WorkSym) (P : ℕ) (hPos : m.inPos = (P : Int)) (hLe : P ≤ w.length) :
    Runs rewindInputFromPos w m { m with inPos := 0 } (P + 2) := by
  unfold rewindInputFromPos
  let inv (j : ℕ) : Mem k WorkSym := { m with inPos := (P : Int) - 1 - (j : Int) }
  have h1 : Runs (Block.act (inStepDirAct .left)) w m (inv 0) 1 := by
    have heq : applyAct w (inStepDirAct .left) m = inv 0 := by
      rw [applyAct_inStepDir, hPos]
      refine Mem.eq_of_fields ?_ (fun _ _ => rfl) (fun _ => rfl) rfl
      dsimp only [inv, Dir.shift]; omega
    rw [← heq]; exact Runs.act _ m
  have hLoop := Runs.while1 (w := w) (fun inp (_ : Fin k → WorkSym) => inp.isSome)
    (inStepDirAct .left) (inStepDirAct .right) P inv
    (fun j hj => by
      have hidx : (P : Int) - 1 - (j : Int) = ((P - 1 - j : ℕ) : Int) := by omega
      have hlt : P - 1 - j < w.length := by omega
      have hsome : (readInput w (inv j).inPos).isSome = true := by
        dsimp only [inv]
        rw [hidx, readInput_of_nonneg, List.getElem?_eq_getElem hlt]
        rfl
      refine ⟨hsome, ?_⟩
      rw [applyAct_inStepDir]
      refine Mem.eq_of_fields ?_ (fun _ _ => rfl) (fun _ => rfl) rfl
      dsimp only [inv, Dir.shift]; omega)
    (by
      dsimp only [inv]
      have hm1 : (P : Int) - 1 - (P : Int) = -1 := by omega
      rw [hm1]
      unfold readInput
      have hlt : (-1 : Int) < 0 := by omega
      rw [ite_eq_left hlt]; rfl)
  have hExit : applyAct w (inStepDirAct .right) (inv P) = { m with inPos := 0 } := by
    rw [applyAct_inStepDir]
    refine Mem.eq_of_fields ?_ (fun _ _ => rfl) (fun _ => rfl) rfl
    dsimp only [inv, Dir.shift]; omega
  rw [hExit] at hLoop
  have hTime : 1 + (P + 1) = P + 2 := by omega
  rw [← hTime]
  exact h1.seq hLoop

/-- Append one `.u` mark to `unaryTape N` on tape `t₀` (head `0 → 0`) in `2 N + 4` steps. -/
def appendOneUnary {k : ℕ} (t₀ : Fin k) : Block k WorkSym :=
  (Block.while1 (fun _ sc => sc t₀ == .u)
    (stepDirAct t₀ .right) (writeDirAct t₀ .u .right)).seq
    (rewindFromEnd t₀)

theorem Runs_appendOneUnary {k : ℕ} {w : List Bool} (t₀ : Fin k)
    (m : Mem k WorkSym) (N : ℕ)
    (hTape : m.work t₀ = unaryTape N) (hPos : m.workPos t₀ = 0) :
    Runs (appendOneUnary t₀) w m
      { m with work := fun i p => if i = t₀ then unaryTape (N + 1) p else m.work i p }
      (2 * N + 4) := by
  unfold appendOneUnary
  let inv (j : ℕ) : Mem k WorkSym :=
    { m with workPos := fun i => if i = t₀ then (j : Int) else m.workPos i }
  have hInv0 : inv 0 = m := by
    refine Mem.eq_of_fields rfl (fun _ _ => rfl) (fun i => ?_) rfl
    dsimp only [inv]
    by_cases hi : i = t₀ <;> simp [hi, hPos]
  have hScan := Runs.while1 (w := w)
    (fun _ (sc : Fin k → WorkSym) => sc t₀ == .u)
    (stepDirAct t₀ .right) (writeDirAct t₀ .u .right) N inv
    (fun j hj => by
      have hcell : ((inv j).work t₀ ((inv j).workPos t₀) == .u) = true := by
        dsimp only [inv]; simp only [↓reduceIte]; rw [hTape, unaryTape_lt hj]; rfl
      refine ⟨hcell, ?_⟩
      unfold stepDirAct
      rw [applyAct_mkAct1]
      refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
      · dsimp only [inv]
        by_cases hi : i = t₀
        · subst hi; simp only [↓reduceIte]; exact congrFun (ite_self_cell (m.work i) _) p
        · simp [hi]
      · dsimp only [inv, Dir.shift]
        by_cases hi : i = t₀
        · subst hi; simp only [↓reduceIte]; omega
        · simp [hi])
    (by dsimp only [inv]; simp only [↓reduceIte]; rw [hTape, unaryTape_ge le_rfl]; rfl)
  let mMid : Mem k WorkSym :=
    { m with
      work    := fun i p => if i = t₀ then unaryTape (N + 1) p else m.work i p
      workPos := fun i => if i = t₀ then ((N + 1 : ℕ) : Int) else m.workPos i }
  have hMidEq : applyAct w (writeDirAct t₀ .u .right) (inv N) = mMid := by
    unfold writeDirAct
    rw [applyAct_mkAct1]
    refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
    · dsimp only [inv, mMid]
      by_cases hi : i = t₀
      · subst hi
        simp only [↓reduceIte, hTape]
        exact congrFun (unaryTape_write_end N) p
      · simp [hi]
    · dsimp only [inv, mMid, Dir.shift]
      by_cases hi : i = t₀
      · subst hi; simp only [↓reduceIte]; omega
      · simp [hi]
  rw [hInv0, hMidEq] at hScan
  have hRew := Runs_rewindFromEnd (w := w) t₀ mMid (N + 1)
    (by dsimp only [mMid]; simp only [↓reduceIte])
    (fun j hj => by dsimp only [mMid]; simp only [↓reduceIte]; rw [unaryTape_lt hj]; decide)
    (by dsimp only [mMid]; simp only [↓reduceIte]; exact unaryTape_neg (by omega))
  have hFinal : { mMid with workPos := fun i => if i = t₀ then 0 else mMid.workPos i } =
      { m with work := fun i p => if i = t₀ then unaryTape (N + 1) p else m.work i p } := by
    refine Mem.eq_of_fields rfl (fun _ _ => rfl) (fun i => ?_) rfl
    dsimp only [mMid]
    by_cases hi : i = t₀ <;> simp [hi, hPos]
  rw [hFinal] at hRew
  have hTime : (N + 1) + ((N + 1) + 2) = 2 * N + 4 := by omega
  rw [← hTime]
  exact hScan.seq hRew

def clampRightAct {k : ℕ} (t₁ : Fin k) : Action k WorkSym :=
  mkAct1 t₁ (fun inp _ => if inp.isSome then .right else .stay)
    (fun _ sym => (sym, .right)) (fun _ _ => none)

/-- Advance `inPos` from `0` to `min (M * s) w.length` using unary rulers `M` on `t₀` and `s` on `t₁`. -/
def advanceClampedByPair {k : ℕ} (t₀ t₁ : Fin k) : Block k WorkSym :=
  (Block.loop (fun _ sc => sc t₀ == .u)
    (stepDirAct t₀ .right) actStay
    ((Block.while1 (fun _ sc => sc t₁ == .u) (clampRightAct t₁) actStay).seq
      (rewindFromEnd t₁))).seq
    (rewindFromEnd t₀)

theorem Runs_advanceClampedByPair {k : ℕ} {w : List Bool} {t₀ t₁ : Fin k}
    (hne : t₀ ≠ t₁) (m : Mem k WorkSym) (M s : ℕ)
    (hIn : m.inPos = 0)
    (hT0 : m.work t₀ = unaryTape M) (hP0 : m.workPos t₀ = 0)
    (hT1 : m.work t₁ = unaryTape s) (hP1 : m.workPos t₁ = 0) :
    Runs (advanceClampedByPair t₀ t₁) w m
      { m with inPos := ((min (M * s) w.length : ℕ) : Int) }
      (2 * M * s + 5 * M + 3) := by
  unfold advanceClampedByPair
  have hInner : ∀ (base : ℕ) (mB : Mem k WorkSym),
      mB.inPos = ((min base w.length : ℕ) : Int) →
      mB.work t₁ = unaryTape s →
      mB.workPos t₁ = 0 →
      Runs ((Block.while1 (fun _ sc => sc t₁ == .u) (clampRightAct t₁) actStay).seq
        (rewindFromEnd t₁)) w mB
        { mB with inPos := ((min (base + s) w.length : ℕ) : Int) } (2 * s + 3) := by
    intro base mB hBIn hBT1 hBP1
    let inv (j : ℕ) : Mem k WorkSym :=
      { mB with
        inPos   := ((min (base + j) w.length : ℕ) : Int)
        workPos := fun i => if i = t₁ then (j : Int) else mB.workPos i }
    have hInv0 : inv 0 = mB := by
      refine Mem.eq_of_fields ?_ (fun _ _ => rfl) (fun i => ?_) rfl
      · dsimp only [inv]; rw [Nat.add_zero, hBIn]
      · dsimp only [inv]; by_cases hi : i = t₁ <;> simp [hi, hBP1]
    have hW := Runs.while1 (w := w)
      (fun _ (sc : Fin k → WorkSym) => sc t₁ == .u)
      (clampRightAct t₁) actStay s inv
      (fun j hj => by
        have hcell : ((inv j).work t₁ ((inv j).workPos t₁) == .u) = true := by
          dsimp only [inv]; simp only [↓reduceIte]; rw [hBT1, unaryTape_lt hj]; rfl
        refine ⟨hcell, ?_⟩
        unfold clampRightAct
        rw [applyAct_mkAct1]
        refine Mem.eq_of_fields ?_ (fun i p => ?_) (fun i => ?_) rfl
        · dsimp only [inv]
          rw [readInput_of_nonneg]
          by_cases hlt : base + j < w.length
          · have hmin1 : min (base + j) w.length = base + j := Nat.min_eq_left (by omega)
            have hmin2 : min (base + (j + 1)) w.length = base + j + 1 := Nat.min_eq_left (by omega)
            rw [hmin1, hmin2, List.getElem?_eq_getElem hlt]
            simp only [Option.isSome, ↓reduceIte, Dir.shift]; omega
          · have hmin1 : min (base + j) w.length = w.length := Nat.min_eq_right (by omega)
            have hmin2 : min (base + (j + 1)) w.length = w.length := Nat.min_eq_right (by omega)
            rw [hmin1, hmin2, List.getElem?_eq_none le_rfl]
            rfl
        · dsimp only [inv]
          by_cases hi : i = t₁
          · subst hi; simp only [↓reduceIte]; exact congrFun (ite_self_cell (mB.work i) _) p
          · simp [hi]
        · dsimp only [inv, Dir.shift]
          by_cases hi : i = t₁
          · subst hi; simp only [↓reduceIte]; omega
          · simp [hi])
      (by dsimp only [inv]; simp only [↓reduceIte]; rw [hBT1, unaryTape_ge le_rfl]; rfl)
    rw [hInv0, applyAct_actStay] at hW
    have hRew := Runs_rewindFromEnd (w := w) t₁ (inv s) s
      (by dsimp only [inv]; simp only [↓reduceIte])
      (fun j hj => by dsimp only [inv]; rw [hBT1, unaryTape_lt hj]; decide)
      (by dsimp only [inv]; rw [hBT1]; exact unaryTape_neg (by omega))
    have hEnd : { inv s with workPos := fun i => if i = t₁ then 0 else (inv s).workPos i } =
        { mB with inPos := ((min (base + s) w.length : ℕ) : Int) } := by
      refine Mem.eq_of_fields rfl (fun _ _ => rfl) (fun i => ?_) rfl
      dsimp only [inv]
      by_cases hi : i = t₁ <;> simp [hi, hBP1]
    rw [hEnd] at hRew
    have hTime : (s + 1) + (s + 2) = 2 * s + 3 := by omega
    rw [← hTime]
    exact hW.seq hRew
  let outerInv (q : ℕ) : Mem k WorkSym :=
    { m with
      inPos   := ((min (q * s) w.length : ℕ) : Int)
      workPos := fun i => if i = t₀ then (q : Int) else m.workPos i }
  have hOuter0 : outerInv 0 = m := by
    refine Mem.eq_of_fields ?_ (fun _ _ => rfl) (fun i => ?_) rfl
    · dsimp only [outerInv]; simp [hIn]
    · dsimp only [outerInv]; by_cases hi : i = t₀ <;> simp [hi, hP0]
  have hOuter := Runs.loop (w := w)
    (fun _ (sc : Fin k → WorkSym) => sc t₀ == .u)
    (stepDirAct t₀ .right) actStay _ (2 * s + 3) M outerInv
    (fun q hq => by
      have hcell : ((outerInv q).work t₀ ((outerInv q).workPos t₀) == .u) = true := by
        dsimp only [outerInv]; simp only [↓reduceIte]; rw [hT0, unaryTape_lt hq]; rfl
      refine ⟨hcell, ?_⟩
      let mEnter : Mem k WorkSym :=
        { m with
          inPos   := ((min (q * s) w.length : ℕ) : Int)
          workPos := fun i => if i = t₀ then ((q + 1 : ℕ) : Int) else m.workPos i }
      have hEnt : applyAct w (stepDirAct t₀ .right) (outerInv q) = mEnter := by
        unfold stepDirAct
        rw [applyAct_mkAct1]
        refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
        · dsimp only [outerInv, mEnter]
          by_cases hi : i = t₀
          · subst hi; simp only [↓reduceIte]; exact congrFun (ite_self_cell (m.work i) _) p
          · simp [hi]
        · dsimp only [outerInv, mEnter, Dir.shift]
          by_cases hi : i = t₀
          · subst hi; simp only [↓reduceIte]; omega
          · simp [hi]
      rw [hEnt]
      have hInQ := hInner (q * s) mEnter rfl hT1
        (by dsimp only [mEnter]; rw [ite_eq_right (Ne.symm hne), hP1])
      have hMul : q * s + s = (q + 1) * s := by ring
      simpa only [mEnter, outerInv, hMul] using hInQ)
    (by dsimp only [outerInv]; simp only [↓reduceIte]; rw [hT0, unaryTape_ge le_rfl]; rfl)
  rw [hOuter0, applyAct_actStay] at hOuter
  have hRew0 := Runs_rewindFromEnd (w := w) t₀ (outerInv M) M
    (by dsimp only [outerInv]; simp only [↓reduceIte])
    (fun j hj => by dsimp only [outerInv]; rw [hT0, unaryTape_lt hj]; decide)
    (by dsimp only [outerInv]; rw [hT0]; exact unaryTape_neg (by omega))
  have hEnd0 : { outerInv M with workPos := fun i => if i = t₀ then 0 else (outerInv M).workPos i } =
      { m with inPos := ((min (M * s) w.length : ℕ) : Int) } := by
    refine Mem.eq_of_fields rfl (fun _ _ => rfl) (fun i => ?_) rfl
    dsimp only [outerInv]; by_cases hi : i = t₀ <;> simp [hi, hP0]
  rw [hEnd0] at hRew0
  have hTime : (M * (1 + (2 * s + 3)) + 1) + (M + 2) = 2 * M * s + 5 * M + 3 := by ring
  rw [← hTime]
  exact hOuter.seq hRew0

def quadEnterPush {k : ℕ} (t₀ t₁ : Fin k) : Action k WorkSym :=
  mkAct2 t₀ t₁ (fun _ _ _ => .stay)
    (fun _ s₀ _ => (s₀, .right)) (fun _ _ _ => (.u, .left)) (fun _ _ _ => none)

def quadCopyBack {k : ℕ} (t₀ t₁ : Fin k) : Action k WorkSym :=
  mkAct2 t₀ t₁ (fun _ _ _ => .stay)
    (fun _ _ _ => (.u, .right)) (fun _ _ _ => (.blank, .right)) (fun _ _ _ => none)

/-- Quadruple `unaryTape M` on `t₀` to `unaryTape (4 * M)` using negative cells of `t₁` (`10 M + 6` steps). -/
def quadrupleUnary {k : ℕ} (t₀ t₁ : Fin k) : Block k WorkSym :=
  ((((Block.act (stepDirAct t₁ .left)).seq (Block.act (stepDirAct t₁ .left))).seq
    (Block.loop (fun _ sc => sc t₀ == .u)
      (quadEnterPush t₀ t₁) (stepDirAct t₁ .right)
      ((Block.act (writeDirAct t₁ .u .left)).seq (Block.act (writeDirAct t₁ .u .left))))).seq
    (Block.while1 (fun _ sc => sc t₁ == .u)
      (quadCopyBack t₀ t₁) (stepDirAct t₁ .right))).seq
    (rewindFromEnd t₀)

theorem Runs_quadrupleUnary {k : ℕ} {w : List Bool} {t₀ t₁ : Fin k}
    (hne : t₀ ≠ t₁) (m : Mem k WorkSym) (M s : ℕ)
    (hT0 : m.work t₀ = unaryTape M) (hP0 : m.workPos t₀ = 0)
    (hT1 : m.work t₁ = unaryTape s) (hP1 : m.workPos t₁ = 0) :
    Runs (quadrupleUnary t₀ t₁) w m
      { m with work := fun i p => if i = t₀ then unaryTape (4 * M) p else m.work i p }
      (10 * M + 6) := by
  unfold quadrupleUnary
  let negScratch (cnt : ℕ) (p : Int) : WorkSym :=
    if -1 - (cnt : Int) ≤ p ∧ p ≤ -2 then .u else unaryTape s p
  have hScratch0 : negScratch 0 = unaryTape s := by
    funext p; unfold negScratch
    split_ifs <;> first | rfl | omega
  let pushInv (j : ℕ) : Mem k WorkSym :=
    { m with
      work := fun i p => if i = t₁ then negScratch (3 * j) p else m.work i p
      workPos := fun i =>
        if i = t₀ then (j : Int)
        else if i = t₁ then -2 - (3 * (j : Int))
        else m.workPos i }
  -- Step 1: two left steps on `t₁` (`0 → -1 → -2`)
  let mL1 : Mem k WorkSym :=
    { m with workPos := fun i => if i = t₁ then -1 else m.workPos i }
  have hL1 : applyAct w (stepDirAct t₁ .left) m = mL1 := by
    unfold stepDirAct; rw [applyAct_mkAct1]
    refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
    · dsimp only [mL1]
      by_cases hi : i = t₁
      · subst hi; simp only [↓reduceIte]; exact congrFun (ite_self_cell (m.work i) _) p
      · simp [hi]
    · dsimp only [mL1, Dir.shift]
      by_cases hi : i = t₁ <;> simp [hi, hP1]
  have hL2 : applyAct w (stepDirAct t₁ .left) mL1 = pushInv 0 := by
    unfold stepDirAct; rw [applyAct_mkAct1]
    refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
    · dsimp only [mL1, pushInv]
      by_cases hi : i = t₁
      · subst hi
        simp only [↓reduceIte, Nat.mul_zero, hScratch0, ← hT1]
        exact congrFun (ite_self_cell (m.work i) _) p
      · simp [hi]
    · dsimp only [mL1, pushInv, Dir.shift]
      by_cases hi0 : i = t₀
      · subst hi0; simp [hne, hP0]
      · by_cases hi1 : i = t₁
        · subst hi1; simp [hi0]
        · simp [hi0, hi1]
  have hStepTwo : Runs ((Block.act (stepDirAct t₁ .left)).seq (Block.act (stepDirAct t₁ .left)))
      w m (pushInv 0) 2 := by
    have r1 : Runs (Block.act (stepDirAct t₁ .left)) w m mL1 1 := by rw [← hL1]; exact Runs.act _ _
    have r2 : Runs (Block.act (stepDirAct t₁ .left)) w mL1 (pushInv 0) 1 := by
      rw [← hL2]; exact Runs.act _ _
    exact r1.seq r2
  -- Helper for extending `negScratch c` at `-2 - c`
  have hExtendScratch : ∀ (c : ℕ),
      (fun p : Int => if p = -2 - (c : Int) then WorkSym.u else negScratch c p) =
        negScratch (c + 1) := by
    intro c; funext p; unfold negScratch
    by_cases hp : p = -2 - (c : Int)
    · subst hp
      have h : -1 - ((c + 1 : ℕ) : Int) ≤ -2 - (c : Int) ∧ -2 - (c : Int) ≤ -2 := by omega
      rw [ite_eq_left rfl, ite_eq_left h]
    · rw [ite_eq_right hp]
      by_cases h1 : -1 - (c : Int) ≤ p ∧ p ≤ -2
      · have h2 : -1 - ((c + 1 : ℕ) : Int) ≤ p ∧ p ≤ -2 := by omega
        rw [ite_eq_left h1, ite_eq_left h2]
      · have h2 : ¬ (-1 - ((c + 1 : ℕ) : Int) ≤ p ∧ p ≤ -2) := by omega
        rw [ite_eq_right h1, ite_eq_right h2]
  -- Step 2: `pushThreeLoop` (`M` iterations, `3 M + 1` steps)
  have hPush := Runs.loop (w := w)
    (fun _ (sc : Fin k → WorkSym) => sc t₀ == .u)
    (quadEnterPush t₀ t₁) (stepDirAct t₁ .right)
    ((Block.act (writeDirAct t₁ .u .left)).seq (Block.act (writeDirAct t₁ .u .left))) 2 M pushInv
    (fun j hj => by
      have hcell : ((pushInv j).work t₀ ((pushInv j).workPos t₀) == .u) = true := by
        dsimp only [pushInv]
        simp only [hne, ↓reduceIte, hT0, unaryTape_lt hj]; rfl
      refine ⟨hcell, ?_⟩
      let mP1 : Mem k WorkSym :=
        { m with
          work := fun i p => if i = t₁ then negScratch (3 * j + 1) p else m.work i p
          workPos := fun i =>
            if i = t₀ then ((j + 1 : ℕ) : Int)
            else if i = t₁ then -2 - (3 * (j : Int) + 1)
            else m.workPos i }
      let mP2 : Mem k WorkSym :=
        { m with
          work := fun i p => if i = t₁ then negScratch (3 * j + 2) p else m.work i p
          workPos := fun i =>
            if i = t₀ then ((j + 1 : ℕ) : Int)
            else if i = t₁ then -2 - (3 * (j : Int) + 2)
            else m.workPos i }
      have hE1 : applyAct w (quadEnterPush t₀ t₁) (pushInv j) = mP1 := by
        unfold quadEnterPush
        rw [applyAct_mkAct2 w (pushInv j) hne]
        refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
        · dsimp only [pushInv, mP1]
          by_cases hi0 : i = t₀
          · subst hi0
            simp only [hne, ↓reduceIte]
            exact congrFun (ite_self_cell (m.work i) _) p
          · by_cases hi1 : i = t₁
            · subst hi1
              simp only [Ne.symm hne, ↓reduceIte]
              have hc : -2 - 3 * (j : Int) = -2 - ((3 * j : ℕ) : Int) := by omega
              rw [hc]
              exact congrFun (hExtendScratch (3 * j)) p
            · simp [hi0, hi1]
        · dsimp only [pushInv, mP1, Dir.shift]
          by_cases hi0 : i = t₀
          · subst hi0; simp only [↓reduceIte]; omega
          · by_cases hi1 : i = t₁
            · subst hi1; simp only [hi0, ↓reduceIte]; omega
            · simp [hi0, hi1]
      have hE2 : applyAct w (writeDirAct t₁ .u .left) mP1 = mP2 := by
        unfold writeDirAct; rw [applyAct_mkAct1]
        refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
        · dsimp only [mP1, mP2]
          by_cases hi1 : i = t₁
          · subst hi1
            simp only [Ne.symm hne, ↓reduceIte]
            have hc : -2 - (3 * (j : Int) + 1) = -2 - ((3 * j + 1 : ℕ) : Int) := by omega
            rw [hc]
            exact congrFun (hExtendScratch (3 * j + 1)) p
          · simp [hi1]
        · dsimp only [mP1, mP2, Dir.shift]
          by_cases hi0 : i = t₀
          · subst hi0; simp [hne]
          · by_cases hi1 : i = t₁
            · subst hi1; simp only [hi0, ↓reduceIte]; omega
            · simp [hi0, hi1]
      have hE3 : applyAct w (writeDirAct t₁ .u .left) mP2 = pushInv (j + 1) := by
        unfold writeDirAct; rw [applyAct_mkAct1]
        refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
        · dsimp only [mP2, pushInv]
          by_cases hi1 : i = t₁
          · subst hi1
            simp only [Ne.symm hne, ↓reduceIte]
            have hc : -2 - (3 * (j : Int) + 2) = -2 - ((3 * j + 2 : ℕ) : Int) := by omega
            have h3 : 3 * j + 2 + 1 = 3 * (j + 1) := by omega
            rw [hc, ← h3]
            exact congrFun (hExtendScratch (3 * j + 2)) p
          · simp [hi1]
        · dsimp only [mP2, pushInv, Dir.shift]
          by_cases hi0 : i = t₀
          · subst hi0; simp [hne]
          · by_cases hi1 : i = t₁
            · subst hi1; simp only [hi0, ↓reduceIte]; omega
            · simp [hi0, hi1]
      rw [hE1]
      have r1 : Runs (Block.act (writeDirAct t₁ .u .left)) w mP1 mP2 1 := by
        rw [← hE2]; exact Runs.act _ _
      have r2 : Runs (Block.act (writeDirAct t₁ .u .left)) w mP2 (pushInv (j + 1)) 1 := by
        rw [← hE3]; exact Runs.act _ _
      exact r1.seq r2)
    (by
      dsimp only [pushInv]
      simp only [hne, ↓reduceIte, hT0, unaryTape_ge le_rfl]; rfl)
  -- Step 3: `drainLoop` (`3 M` iterations, `3 M + 1` steps)
  let drainInv (r : ℕ) : Mem k WorkSym :=
    { m with
      work := fun i p =>
        if i = t₀ then unaryTape (M + r) p
        else if i = t₁ then negScratch (3 * M - r) p
        else m.work i p
      workPos := fun i =>
        if i = t₀ then ((M + r : ℕ) : Int)
        else if i = t₁ then -1 - (3 * (M : Int)) + (r : Int)
        else m.workPos i }
  have hPushExit : applyAct w (stepDirAct t₁ .right) (pushInv M) = drainInv 0 := by
    unfold stepDirAct; rw [applyAct_mkAct1]
    refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
    · dsimp only [pushInv, drainInv]
      by_cases hi0 : i = t₀
      · subst hi0; simp [hne, hT0]
      · by_cases hi1 : i = t₁
        · subst hi1
          simp only [Ne.symm hne, ↓reduceIte, Nat.sub_zero]
          exact congrFun (ite_self_cell (negScratch (3 * M)) _) p
        · simp [hi0, hi1]
    · dsimp only [pushInv, drainInv, Dir.shift]
      by_cases hi0 : i = t₀
      · subst hi0; simp [hne]
      · by_cases hi1 : i = t₁
        · subst hi1; simp only [hi0, ↓reduceIte]; omega
        · simp [hi0, hi1]
  rw [hPushExit] at hPush
  have hDrain := Runs.while1 (w := w)
    (fun _ (sc : Fin k → WorkSym) => sc t₁ == .u)
    (quadCopyBack t₀ t₁) (stepDirAct t₁ .right) (3 * M) drainInv
    (fun r hr => by
      have hcell : ((drainInv r).work t₁ ((drainInv r).workPos t₁) == .u) = true := by
        dsimp only [drainInv]
        simp only [Ne.symm hne, ↓reduceIte]
        unfold negScratch
        have hcond : -1 - ((3 * M - r : ℕ) : Int) ≤ -1 - 3 * (M : Int) + (r : Int) ∧
            -1 - 3 * (M : Int) + (r : Int) ≤ -2 := by omega
        rw [ite_eq_left hcond]; rfl
      refine ⟨hcell, ?_⟩
      unfold quadCopyBack
      rw [applyAct_mkAct2 w (drainInv r) hne]
      refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
      · dsimp only [drainInv]
        by_cases hi0 : i = t₀
        · subst hi0
          simp only [↓reduceIte]
          have hMR : M + (r + 1) = (M + r) + 1 := by omega
          rw [hMR]
          exact congrFun (unaryTape_write_end (M + r)) p
        · by_cases hi1 : i = t₁
          · subst hi1
            simp only [Ne.symm hne, ↓reduceIte]
            unfold negScratch
            by_cases hp : p = -1 - 3 * (M : Int) + (r : Int)
            · subst hp
              rw [ite_eq_left rfl]
              have hnot : ¬ (-1 - ((3 * M - (r + 1) : ℕ) : Int) ≤ -1 - 3 * (M : Int) + (r : Int) ∧
                  -1 - 3 * (M : Int) + (r : Int) ≤ -2) := by omega
              rw [ite_eq_right hnot, unaryTape_neg (by omega)]
            · rw [ite_eq_right hp]
              by_cases h1 : -1 - ((3 * M - r : ℕ) : Int) ≤ p ∧ p ≤ -2
              · have h2 : -1 - ((3 * M - (r + 1) : ℕ) : Int) ≤ p ∧ p ≤ -2 := by omega
                rw [ite_eq_left h1, ite_eq_left h2]
              · have h2 : ¬ (-1 - ((3 * M - (r + 1) : ℕ) : Int) ≤ p ∧ p ≤ -2) := by omega
                rw [ite_eq_right h1, ite_eq_right h2]
          · simp [hi0, hi1]
      · dsimp only [drainInv, Dir.shift]
        by_cases hi0 : i = t₀
        · subst hi0; simp only [↓reduceIte]; omega
        · by_cases hi1 : i = t₁
          · subst hi1; simp only [hi0, ↓reduceIte]; omega
          · simp [hi0, hi1])
    (by
      dsimp only [drainInv]
      simp only [Ne.symm hne, ↓reduceIte, Nat.sub_self, hScratch0]
      have hm1 : -1 - 3 * (M : Int) + ((3 * M : ℕ) : Int) = -1 := by omega
      rw [hm1, unaryTape_neg (by omega)]; rfl)
  let mBeforeRew : Mem k WorkSym :=
    { m with
      work    := fun i p => if i = t₀ then unaryTape (4 * M) p else m.work i p
      workPos := fun i => if i = t₀ then ((4 * M : ℕ) : Int) else m.workPos i }
  have hDrainExit : applyAct w (stepDirAct t₁ .right) (drainInv (3 * M)) = mBeforeRew := by
    unfold stepDirAct; rw [applyAct_mkAct1]
    refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
    · dsimp only [drainInv, mBeforeRew]
      by_cases hi0 : i = t₀
      · subst hi0
        simp only [hne, ↓reduceIte]
        have h4 : M + 3 * M = 4 * M := by omega
        rw [h4]
      · by_cases hi1 : i = t₁
        · subst hi1
          simp only [Ne.symm hne, ↓reduceIte, Nat.sub_self, hScratch0, ← hT1]
          exact congrFun (ite_self_cell (m.work i) _) p
        · simp [hi0, hi1]
    · dsimp only [drainInv, mBeforeRew, Dir.shift]
      by_cases hi0 : i = t₀
      · subst hi0
        simp only [hne, ↓reduceIte]
        have h4 : M + 3 * M = 4 * M := by omega
        rw [h4]
      · by_cases hi1 : i = t₁
        · subst hi1; simp only [hi0, ↓reduceIte, hP1]; omega
        · simp [hi0, hi1]
  rw [hDrainExit] at hDrain
  have hRew := Runs_rewindFromEnd (w := w) t₀ mBeforeRew (4 * M)
    (by dsimp only [mBeforeRew]; simp only [↓reduceIte])
    (fun j hj => by dsimp only [mBeforeRew]; simp only [↓reduceIte]; rw [unaryTape_lt hj]; decide)
    (by dsimp only [mBeforeRew]; simp only [↓reduceIte]; exact unaryTape_neg (by omega))
  have hFinal : { mBeforeRew with workPos := fun i => if i = t₀ then 0 else mBeforeRew.workPos i } =
      { m with work := fun i p => if i = t₀ then unaryTape (4 * M) p else m.work i p } := by
    refine Mem.eq_of_fields rfl (fun _ _ => rfl) (fun i => ?_) rfl
    dsimp only [mBeforeRew]; by_cases hi : i = t₀ <;> simp [hi, hP0]
  rw [hFinal] at hRew
  have hTime : ((2 + (M * (1 + 2) + 1)) + (3 * M + 1)) + (4 * M + 2) = 10 * M + 6 := by ring
  rw [← hTime]
  exact ((hStepTwo.seq hPush).seq hDrain).seq hRew

/-- Discover `b = entryBits d` on `t₁` and `4 ^ b` on `t₀` in `≤ 120 * L` steps! -/
def discoverEntryBits {k : ℕ} (t₀ t₁ : Fin k) : Block k WorkSym :=
  (((((((appendOneUnary t₀).seq (appendOneUnary t₀)).seq
    (appendOneUnary t₀)).seq (appendOneUnary t₀)).seq
    (appendOneUnary t₁)).seq (advanceClampedByPair t₀ t₁)).seq
    (Block.loop (fun inp _ => inp.isSome) actStay actStay
      (((rewindInputFromPos.seq (appendOneUnary t₁)).seq
        (quadrupleUnary t₀ t₁)).seq (advanceClampedByPair t₀ t₁)))).seq
    rewindInputFromPos

theorem Runs_discoverEntryBits {k : ℕ} {t₀ t₁ : Fin k} (hne : t₀ ≠ t₁)
    {d : ℕ} (hd : 1 ≤ d) {w : List Bool}
    (hwLen : w.length = inputLength d)
    (m : Mem k WorkSym)
    (hIn : m.inPos = 0)
    (hB0 : m.work t₀ = fun _ => .blank) (hP0 : m.workPos t₀ = 0)
    (hB1 : m.work t₁ = fun _ => .blank) (hP1 : m.workPos t₁ = 0) :
    let b := entryBits d
    Runs (discoverEntryBits t₀ t₁) w m
      { m with
        work := fun i p =>
          if i = t₀ then unaryTape (4 ^ b) p
          else if i = t₁ then unaryTape b p
          else m.work i p }
      (120 * inputLength d) := by
  intro b
  unfold discoverEntryBits
  have hb1 : 1 ≤ b := entryBits_pos_tm d
  have hL1 : 1 ≤ inputLength d := inputLength_pos hd
  -- `init4`: 4 marks on `t₀`, 1 mark on `t₁`
  let mkState (s : ℕ) (pos : ℕ) : Mem k WorkSym :=
    { m with
      inPos := (pos : Int)
      work  := fun i p =>
        if i = t₀ then unaryTape (4 ^ s) p
        else if i = t₁ then unaryTape s p
        else m.work i p }
  have hApp0 : ∀ (n : ℕ) (mCur : Mem k WorkSym),
      mCur.work t₀ = unaryTape n →
      mCur.workPos = m.workPos →
      Runs (appendOneUnary t₀) w mCur
        { mCur with work := fun i p => if i = t₀ then unaryTape (n + 1) p else mCur.work i p }
        (2 * n + 4) := fun n mCur hT hP =>
    Runs_appendOneUnary t₀ mCur n hT (by rw [hP, hP0])
  let mU1 : Mem k WorkSym := { m with work := fun i p => if i = t₀ then unaryTape 1 p else m.work i p }
  let mU2 : Mem k WorkSym := { m with work := fun i p => if i = t₀ then unaryTape 2 p else m.work i p }
  let mU3 : Mem k WorkSym := { m with work := fun i p => if i = t₀ then unaryTape 3 p else m.work i p }
  let mU4 : Mem k WorkSym := { m with work := fun i p => if i = t₀ then unaryTape 4 p else m.work i p }
  have rU1 : Runs (appendOneUnary t₀) w m mU1 4 := by
    simpa [mU1] using hApp0 0 m (by rw [hB0, unaryTape_zero]) rfl
  have rU2 : Runs (appendOneUnary t₀) w mU1 mU2 6 := by
    have h := hApp0 1 mU1 (by funext p; dsimp only [mU1]; simp) rfl
    have heq : { mU1 with work := fun i p => if i = t₀ then unaryTape 2 p else mU1.work i p } = mU2 := by
      refine Mem.eq_of_fields rfl (fun i p => ?_) (fun _ => rfl) rfl
      dsimp only [mU1, mU2]; by_cases hi : i = t₀ <;> simp [hi]
    rw [heq] at h; exact h
  have rU3 : Runs (appendOneUnary t₀) w mU2 mU3 8 := by
    have h := hApp0 2 mU2 (by funext p; dsimp only [mU2]; simp) rfl
    have heq : { mU2 with work := fun i p => if i = t₀ then unaryTape 3 p else mU2.work i p } = mU3 := by
      refine Mem.eq_of_fields rfl (fun i p => ?_) (fun _ => rfl) rfl
      dsimp only [mU2, mU3]; by_cases hi : i = t₀ <;> simp [hi]
    rw [heq] at h; exact h
  have rU4 : Runs (appendOneUnary t₀) w mU3 mU4 10 := by
    have h := hApp0 3 mU3 (by funext p; dsimp only [mU3]; simp) rfl
    have heq : { mU3 with work := fun i p => if i = t₀ then unaryTape 4 p else mU3.work i p } = mU4 := by
      refine Mem.eq_of_fields rfl (fun i p => ?_) (fun _ => rfl) rfl
      dsimp only [mU3, mU4]; by_cases hi : i = t₀ <;> simp [hi]
    rw [heq] at h; exact h
  have rS1 : Runs (appendOneUnary t₁) w mU4 (mkState 1 0) 4 := by
    have h := Runs_appendOneUnary (w := w) t₁ mU4 0
      (by funext p; dsimp only [mU4]; simp [Ne.symm hne, hB1, unaryTape_zero]) hP1
    have heq : { mU4 with work := fun i p => if i = t₁ then unaryTape 1 p else mU4.work i p } =
        mkState 1 0 := by
      refine Mem.eq_of_fields hIn (fun i p => ?_) (fun _ => rfl) rfl
      dsimp only [mU4, mkState]
      by_cases hi0 : i = t₀
      · subst hi0; simp [hne]
      · by_cases hi1 : i = t₁
        · subst hi1; simp [hi0]
        · simp [hi0, hi1]
    rw [heq] at h; exact h
  have rInit : Runs (((((appendOneUnary t₀).seq (appendOneUnary t₀)).seq
      (appendOneUnary t₀)).seq (appendOneUnary t₀)).seq (appendOneUnary t₁))
      w m (mkState 1 0) 32 := by
    simpa using (((rU1.seq rU2).seq rU3).seq rU4).seq rS1
  -- Initial `advanceClampedByPair` at `s = 1` (`4^1 * 1 = 4`, `2*4*1 + 5*4 + 3 = 31` steps)
  let loopInv (j : ℕ) : Mem k WorkSym :=
    mkState (j + 1) (min (4 ^ (j + 1) * (j + 1)) w.length)
  have rAdv0 : Runs (advanceClampedByPair t₀ t₁) w (mkState 1 0) (loopInv 0) 31 := by
    have h := Runs_advanceClampedByPair (w := w) hne (mkState 1 0) 4 1 rfl
      (by funext p; dsimp only [mkState]; simp) hP0
      (by funext p; dsimp only [mkState]; simp [Ne.symm hne]) hP1
    simpa [loopInv, mkState] using h
  -- Main geometric loop (`b - 1` iterations, `j = 0 .. b - 2`, `s = j + 1`)
  let tBody (j : ℕ) : ℕ :=
    let s := j + 1
    (min (4 ^ s * s) w.length + 2) + (2 * s + 4) + (10 * 4 ^ s + 6) +
      (2 * 4 ^ (s + 1) * (s + 1) + 5 * 4 ^ (s + 1) + 3)
  have rLoop := Runs.loop_sum (w := w)
    (fun inp (_ : Fin k → WorkSym) => inp.isSome) actStay actStay
    (((rewindInputFromPos.seq (appendOneUnary t₁)).seq
      (quadrupleUnary t₀ t₁)).seq (advanceClampedByPair t₀ t₁))
    (b - 1) tBody loopInv
    (fun j hj => by
      set s := j + 1
      have hsb : s < b := by omega
      have hltL : 4 ^ s * s < w.length := by
        rw [hwLen]; exact entryBits_quad_lower (by omega) hsb
      have hminEq : min (4 ^ s * s) w.length = 4 ^ s * s := Nat.min_eq_left hltL.le
      have hCond : (readInput w (loopInv j).inPos).isSome = true := by
        dsimp only [loopInv, mkState]
        rw [readInput_of_nonneg, hminEq, List.getElem?_eq_getElem hltL]
        rfl
      refine ⟨hCond, ?_⟩
      rw [applyAct_actStay]
      -- 1) `rewindInputFromPos`
      have r1 := Runs_rewindInputFromPos (w := w) (loopInv j) (min (4 ^ s * s) w.length)
        rfl (Nat.min_le_right _ _)
      have hSt1 : { loopInv j with inPos := 0 } = mkState s 0 := rfl
      rw [hSt1] at r1
      -- 2) `appendOneUnary t₁` (`s → s + 1`)
      let mS2 : Mem k WorkSym :=
        { m with
          inPos := 0
          work  := fun i p =>
            if i = t₀ then unaryTape (4 ^ s) p
            else if i = t₁ then unaryTape (s + 1) p
            else m.work i p }
      have r2 := Runs_appendOneUnary (w := w) t₁ (mkState s 0) s
        (by funext p; dsimp only [mkState]; simp [Ne.symm hne]) hP1
      have hSt2 :
          { mkState s 0 with
            work := fun i p =>
              if i = t₁ then unaryTape (s + 1) p else (mkState s 0).work i p } = mS2 := by
        refine Mem.eq_of_fields rfl (fun i p => ?_) (fun _ => rfl) rfl
        dsimp only [mkState, mS2]
        by_cases hi1 : i = t₁
        · subst hi1; simp [Ne.symm hne]
        · by_cases hi0 : i = t₀
          · subst hi0; simp [hi1]
          · simp [hi0, hi1]
      rw [hSt2] at r2
      -- 3) `quadrupleUnary t₀ t₁` (`4 ^ s → 4 ^ (s + 1)`)
      have r3 := Runs_quadrupleUnary (w := w) hne mS2 (4 ^ s) (s + 1)
        (by funext p; dsimp only [mS2]; simp) hP0
        (by funext p; dsimp only [mS2]; simp [Ne.symm hne]) hP1
      have hSt3 :
          { mS2 with
            work := fun i p =>
              if i = t₀ then unaryTape (4 * 4 ^ s) p else mS2.work i p } = mkState (s + 1) 0 := by
        refine Mem.eq_of_fields rfl (fun i p => ?_) (fun _ => rfl) rfl
        dsimp only [mS2, mkState]
        by_cases hi0 : i = t₀
        · subst hi0; simp [pow_succ']
        · simp [hi0]
      rw [hSt3] at r3
      -- 4) `advanceClampedByPair t₀ t₁` at `(4^(s+1), s+1)`
      have r4 := Runs_advanceClampedByPair (w := w) hne (mkState (s + 1) 0) (4 ^ (s + 1)) (s + 1)
        rfl (by funext p; dsimp only [mkState]; simp) hP0
        (by funext p; dsimp only [mkState]; simp [Ne.symm hne]) hP1
      have hSt4 :
          { mkState (s + 1) 0 with
            inPos := ((min (4 ^ (s + 1) * (s + 1)) w.length : ℕ) : Int) } = loopInv (j + 1) := rfl
      rw [hSt4] at r4
      exact ((r1.seq r2).seq r3).seq r4)
    (by
      have hbEq : b - 1 + 1 = b := by omega
      dsimp only [loopInv, mkState]
      rw [hbEq, readInput_of_nonneg]
      have hUpper : w.length ≤ 4 ^ b * b := by
        rw [hwLen]; exact entryBits_quad_upper hd
      rw [Nat.min_eq_right hUpper, List.getElem?_eq_none le_rfl]
      rfl)
  rw [applyAct_actStay] at rLoop
  -- Final `rewindInputFromPos` from `min (4^b * b) w.length = w.length` to `0`
  have hbEq : b - 1 + 1 = b := by omega
  have hUpper : w.length ≤ 4 ^ b * b := by rw [hwLen]; exact entryBits_quad_upper hd
  have hFinalRew := Runs_rewindInputFromPos (w := w) (loopInv (b - 1)) w.length
    (by dsimp only [loopInv, mkState]; rw [hbEq, Nat.min_eq_right hUpper]) le_rfl
  have hFinalEq : { loopInv (b - 1) with inPos := 0 } =
      { m with
        work := fun i p =>
          if i = t₀ then unaryTape (4 ^ b) p
          else if i = t₁ then unaryTape b p
          else m.work i p } := by
    refine Mem.eq_of_fields hIn.symm (fun i p => ?_) (fun _ => rfl) rfl
    dsimp only [loopInv, mkState]; rw [hbEq]
  rw [hFinalEq] at hFinalRew
  have hAll := ((rInit.seq rAdv0).seq rLoop).seq hFinalRew
  -- Bound total time by `120 * inputLength d` via `natSum_le_of_step`
  apply hAll.of_le
  let g (j : ℕ) : ℕ := 14 * (4 ^ (j + 1) * (j + 1))
  have hStepBound : ∀ j < b - 1, (1 + tBody j) + g j ≤ g (j + 1) := by
    intro j _
    dsimp only [tBody, g]
    set s := j + 1
    have hs1 : 1 ≤ s := by omega
    have hpow1 : 1 ≤ 4 ^ s := Nat.one_le_pow s 4 (by decide)
    have hps : s ≤ 4 ^ s * s := by nlinarith
    have hmin_le : min (4 ^ s * s) w.length ≤ 4 ^ s * s := Nat.min_le_left _ _
    have hp4 : 4 ^ (s + 1) = 4 * 4 ^ s := pow_succ' 4 s
    rw [hp4]
    nlinarith
  have hSumLe := natSum_le_of_step hStepBound
  dsimp only [g] at hSumLe
  rw [hbEq] at hSumLe
  have hQuad4L : 4 ^ b * b ≤ 4 * inputLength d := entryBits_quad_le_four_L hd
  rw [hwLen]
  omega


/-- Clear `unaryTape N` on tape `t₀` (`pos = 0 → 0`) in `2 * N + 3` steps. -/
def clearUnary {k : ℕ} (t₀ : Fin k) : Block k WorkSym :=
  (Block.while1 (fun _ sc => sc t₀ == .u) (stepDirAct t₀ .right) actStay).seq
    (eraseFromEnd t₀)

theorem Runs_clearUnary {k : ℕ} {w : List Bool} (t₀ : Fin k)
    (m : Mem k WorkSym) (N : ℕ)
    (hT : m.work t₀ = unaryTape N) (hP : m.workPos t₀ = 0) :
    Runs (clearUnary t₀) w m
      { m with work := fun i p => if i = t₀ then .blank else m.work i p }
      (2 * N + 3) := by
  unfold clearUnary
  let inv (j : ℕ) : Mem k WorkSym :=
    { m with workPos := fun i => if i = t₀ then (j : Int) else m.workPos i }
  have hInv0 : inv 0 = m := by
    refine Mem.eq_of_fields rfl (fun _ _ => rfl) (fun i => ?_) rfl
    dsimp only [inv]; by_cases hi : i = t₀ <;> simp [hi, hP]
  have hW := Runs.while1 (w := w)
    (fun _ (sc : Fin k → WorkSym) => sc t₀ == .u)
    (stepDirAct t₀ .right) actStay N inv
    (fun j hj => by
      have hcell : ((inv j).work t₀ ((inv j).workPos t₀) == .u) = true := by
        dsimp only [inv]; simp only [↓reduceIte]; rw [hT, unaryTape_lt hj]; rfl
      refine ⟨hcell, ?_⟩
      unfold stepDirAct; rw [applyAct_mkAct1]
      refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
      · dsimp only [inv]
        by_cases hi : i = t₀
        · subst hi; simp only [↓reduceIte]; exact congrFun (ite_self_cell (m.work i) _) p
        · simp [hi]
      · dsimp only [inv, Dir.shift]
        by_cases hi : i = t₀
        · subst hi; simp only [↓reduceIte]; omega
        · simp [hi])
    (by dsimp only [inv]; simp only [↓reduceIte]; rw [hT, unaryTape_ge le_rfl]; rfl)
  rw [hInv0, applyAct_actStay] at hW
  have hEr := Runs_eraseFromEnd (w := w) t₀ (inv N) N
    (by dsimp only [inv]; simp only [↓reduceIte])
    (fun j hj => by dsimp only [inv]; rw [hT, unaryTape_lt hj]; decide)
    (fun p hp => by
      dsimp only [inv]; rw [hT]
      rcases hp with hneg | hge
      · exact unaryTape_neg hneg
      · exact unaryTape_ge hge)
  have hEnd :
      { inv N with
        work    := fun i p => if i = t₀ then WorkSym.blank else (inv N).work i p
        workPos := fun i => if i = t₀ then 0 else (inv N).workPos i } =
      { m with work := fun i p => if i = t₀ then .blank else m.work i p } := by
    refine Mem.eq_of_fields rfl (fun _ _ => rfl) (fun i => ?_) rfl
    dsimp only [inv]; by_cases hi : i = t₀ <;> simp [hi, hP]
  rw [hEnd] at hEr
  have hTime : (N + 1) + (N + 2) = 2 * N + 3 := by omega
  rw [← hTime]
  exact hW.seq hEr


end LeanMachine.ShuffleShear
