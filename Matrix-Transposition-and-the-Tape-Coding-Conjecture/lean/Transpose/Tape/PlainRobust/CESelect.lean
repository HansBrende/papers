import Transpose.Tape.PlainRobust.CESelectNet

/-!
# Selection among candidate codes: plain ⟹ no code with an `O(1)`-bit oracle hint

Let `K` codes on a diagram `D` be such that every input is solved by at least one of them. The
**selection code** on `selDiagram D K P r L` solves complete exchange on every input:
* **Run 1.** The `K` codes run side by side (clamped, packed in base `2^c`). Each node compares the
  candidates' would-be output bits at its own output positions, and for every pair of candidates
  without a recorded difference records one position where they differ, with the first one's bit.
  The comparison state travels along the spine (`selBits K L` extra bits per memory edge).
* **Epilogue.** The input sweep fetches the true bit at every recorded position (`updF`).
* **Run 2.** A candidate that never lost a comparison (`winner`) runs on the fresh copy of `D`.

If candidate `c` is correct, every incorrect candidate differs from it at some recorded position,
where `c`'s bit is the truth, so it loses; `c` never loses. Hence the winner is correct
(`select_solves`). This is a discrimination, not a verification: checking a candidate against the
input is as hard as transposing, but telling two candidates apart takes one fetched bit.

Consequences (`noCode_hintConst_of_noCode`): under `NoCode_TM`, no code exists even with an oracle
hint of a constant number of bits.
-/

namespace Transpose.Tape.Impl

open Transpose TSDiagram

/-! ### Packing `K` values -/

/-- `K` values side by side in base `2^p`. -/
def packK (p K : ℕ) (v : ℕ → ℕ) : ℕ := ∑ a ∈ Finset.range K, 2 ^ (a * p) * v a

theorem packK_succ (p K : ℕ) (v : ℕ → ℕ) :
    packK p (K + 1) v = packK p K v + 2 ^ (K * p) * v K := by
  unfold packK; rw [Finset.sum_range_succ]

theorem packK_lt {p : ℕ} {v : ℕ → ℕ} : ∀ {K : ℕ}, (∀ a < K, v a < 2 ^ p) →
    packK p K v < 2 ^ (K * p)
  | 0, _ => by simp [packK]
  | K + 1, hv => by
    rw [packK_succ]
    have h1 := packK_lt (K := K) (fun a ha => hv a (by omega))
    have h2 : v K + 1 ≤ 2 ^ p := hv K (by omega)
    have e : 2 ^ ((K + 1) * p) = 2 ^ (K * p) * 2 ^ p := by rw [← pow_add]; ring_nf
    rw [e]
    calc packK p K v + 2 ^ (K * p) * v K < 2 ^ (K * p) + 2 ^ (K * p) * v K := by omega
      _ = 2 ^ (K * p) * (v K + 1) := by ring
      _ ≤ 2 ^ (K * p) * 2 ^ p := Nat.mul_le_mul_left _ h2

theorem digit_packK {p : ℕ} {v : ℕ → ℕ} : ∀ {K j : ℕ}, (∀ a < K, v a < 2 ^ p) → j < K →
    packK p K v / 2 ^ (j * p) % 2 ^ p = v j
  | 0, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | K + 1, j, hv, hj => by
    rw [packK_succ]
    have hlt := packK_lt (K := K) (fun a ha => hv a (by omega))
    by_cases hjK : j < K
    · have e : 2 ^ (K * p) * v K = 2 ^ (j * p) * (2 ^ p * (2 ^ ((K - j - 1) * p) * v K)) := by
        have : K * p = j * p + p + (K - j - 1) * p := by
          have hK : K = j + 1 + (K - j - 1) := by omega
          conv_lhs => rw [hK]
          ring
        rw [this, pow_add, pow_add]; ring
      rw [e, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.add_mul_mod_self_left]
      exact digit_packK (K := K) (fun a ha => hv a (by omega)) hjK
    · have hj' : j = K := by omega
      subst hj'
      rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hlt, Nat.zero_add,
        Nat.mod_eq_of_lt (hv j (by omega))]

/-! ### The selection state -/

/-- The state carried along the spine: for each ordered pair of candidates, a recorded position where
they differ (with the first candidate's bit there), and the true bit fetched at that position. -/
abbrev SelSt (K L : ℕ) := (Fin K → Fin K → Option (Fin L × Bool)) × (Fin K → Fin K → Bool)

/-- The initial state: nothing recorded, nothing fetched. -/
def selInit (K L : ℕ) : SelSt K L := (fun _ _ => none, fun _ _ => false)

/-- A state as a number below `|SelSt K L|`. -/
noncomputable def encS {K L : ℕ} (σ : SelSt K L) : ℕ := (Fintype.equivFin (SelSt K L) σ : ℕ)

/-- The number of bits of a state. -/
noncomputable def selBits (K L : ℕ) : ℕ := Nat.clog 2 (Fintype.card (SelSt K L))

theorem encS_lt {K L : ℕ} (σ : SelSt K L) : encS σ < 2 ^ selBits K L :=
  lt_of_lt_of_le (Fintype.equivFin (SelSt K L) σ).2 (Nat.le_pow_clog one_lt_two _)

/-- Decoding a state (the initial state on numbers out of range). -/
noncomputable def decS {K L : ℕ} (m : ℕ) : SelSt K L :=
  if h : m < Fintype.card (SelSt K L) then (Fintype.equivFin (SelSt K L)).symm ⟨m, h⟩
  else selInit K L

theorem decS_encS {K L : ℕ} (σ : SelSt K L) : decS (encS σ) = σ := by
  unfold decS encS
  rw [dite_eq_left (Fintype.equivFin (SelSt K L) σ).2]
  simp

theorem decS_pack {K L : ℕ} (σ : SelSt K L) (m : ℕ) :
    decS (K := K) (L := L) ((encS σ + 2 ^ selBits K L * m) % 2 ^ selBits K L) = σ := by
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (encS_lt σ), decS_encS]

theorem decS_mod {K L : ℕ} (σ : SelSt K L) :
    decS (K := K) (L := L) (encS σ % 2 ^ selBits K L) = σ := by
  rw [Nat.mod_eq_of_lt (encS_lt σ), decS_encS]

theorem unpackS {K L : ℕ} (σ : SelSt K L) (m : ℕ) :
    (encS σ + 2 ^ selBits K L * m) / 2 ^ selBits K L = m := by
  rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt (encS_lt σ), Nat.zero_add]

theorem card_selSt (K L : ℕ) :
    Fintype.card (SelSt K L) = (2 * L + 1) ^ (K * K) * 2 ^ (K * K) := by
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_option, Fintype.card_fin,
    Fintype.card_bool]
  rw [← pow_mul, ← pow_mul]
  ring

/-- A state takes at most `6 K² w` bits. -/
theorem selBits_le (K n : ℕ) : selBits K (n * n * entryBits n) ≤ 6 * K ^ 2 * entryBits n := by
  unfold selBits
  rw [Nat.clog_le_iff_le_pow one_lt_two, card_selSt]
  have hw : 1 ≤ entryBits n := by unfold entryBits; omega
  have h1 := inputLength_succ_le n
  have h2 : (2 * (n * n * entryBits n) + 1) * 2 ≤ 2 ^ (6 * entryBits n) := by
    calc (2 * (n * n * entryBits n) + 1) * 2 ≤ 2 ^ (3 * entryBits n + 1) * 2 * 2 := by omega
      _ = 2 ^ (3 * entryBits n + 3) := by rw [pow_add, pow_add]; ring
      _ ≤ 2 ^ (6 * entryBits n) := Nat.pow_le_pow_right (by norm_num) (by omega)
  calc (2 * (n * n * entryBits n) + 1) ^ (K * K) * 2 ^ (K * K)
      = ((2 * (n * n * entryBits n) + 1) * 2) ^ (K * K) := by rw [mul_pow]
    _ ≤ (2 ^ (6 * entryBits n)) ^ (K * K) := Nat.pow_le_pow_left h2 _
    _ = 2 ^ (6 * K ^ 2 * entryBits n) := by rw [← pow_mul]; ring_nf

/-! ### Updates and the winner -/

/-- **Comparison** at node `u`: each pair of candidates without a recorded difference records a
position output at `u` where their bits differ, with the first candidate's bit, if there is one. -/
noncomputable def updC {k : ℕ} (D : TSDiagram k) (r : ℕ) {K L : ℕ} (u : ℕ)
    (outs : Fin K → ℕ → Bool) (σ : SelSt K L) : SelSt K L :=
  (fun a b => if (σ.1 a b).isSome then σ.1 a b else
    if h : ∃ o : Fin L, D.outNode r o = u ∧ outs a o ≠ outs b o
    then some (Classical.choose h, outs a (Classical.choose h : Fin L)) else none, σ.2)

/-- **Fetch**: the visible bits at the recorded positions are `OR`-ed into the fetched bits (a row
that is not visible reads `false`). -/
def updF (n w : ℕ) {K L : ℕ} (v : ℕ → Bool) (σ : SelSt K L) : SelSt K L :=
  (σ.1, fun a b => σ.2 a b || (match σ.1 a b with | some p => v (tpos n w p.1) | none => false))

/-- Candidate `a` never loses: its bit agrees with the fetched bit at every position it recorded. -/
def SelGood {K L : ℕ} (σ : SelSt K L) (a : Fin K) : Prop :=
  ∀ b p, σ.1 a b = some p → p.2 = σ.2 a b

open Classical in
/-- **The winner**: some candidate that never loses (`0` if there is none). -/
noncomputable def winner {K L : ℕ} (σ : SelSt K L) : ℕ :=
  if h : ∃ a, SelGood σ a then ((Classical.choose h : Fin K) : ℕ) else 0

theorem winner_good {K L : ℕ} {σ : SelSt K L} (h : ∃ a, SelGood σ a) :
    ∃ a : Fin K, (a : ℕ) = winner σ ∧ SelGood σ a := by
  classical
  refine ⟨Classical.choose h, ?_, Classical.choose_spec h⟩
  unfold winner
  rw [dite_eq_left h]

/-! ### The selection code -/

section Code

variable {k : ℕ} (D : TSDiagram k) (n G K P : ℕ) (codes : ℕ → NetCode)

/-- The value on an edge with the state stripped off memory edges. -/
noncomputable def selRaw (f : ℕ × ℕ → ℕ) (e : ℕ × ℕ) : ℕ :=
  if e.2 = e.1 + 1 then f e / 2 ^ selBits K (n * n * entryBits n) else f e

/-- Candidate `a`'s values into a run-1 node. -/
noncomputable def inRun1 (a : ℕ) (f : ℕ × ℕ → ℕ) : ℕ × ℕ → ℕ :=
  fun e' => if e' ∈ D.edges (blockSize G n) then digit D n G a e' (selRaw n K f e') else 0

/-- The visible input masked to `D`'s rows at node `u`. -/
noncomputable def maskRows (u : ℕ) (v : ℕ → Bool) : ℕ → Bool :=
  fun d => if d / (n * entryBits n) ∈ D.rowsAt n (entryBits n) (blockSize G n) u then v d else false

/-- The candidates' output bits at run-1 node `u`, at the positions output there. -/
noncomputable def outsRun1 (u : ℕ) (f : ℕ × ℕ → ℕ) (v : ℕ → Bool) : Fin K → ℕ → Bool :=
  fun a o => if D.outNode (blockSize G n) o = u then
    (codes a).dec o (inRun1 D n G K a f) (maskRows D n G u v) else false

/-- The state arriving at node `u` on its memory edge. -/
noncomputable def stIn (u : ℕ) (f : ℕ × ℕ → ℕ) : SelSt K (n * n * entryBits n) :=
  decS (f (u - 1, u) % 2 ^ selBits K (n * n * entryBits n))

/-- The state leaving run-1 node `u`. -/
noncomputable def stRun1 (u : ℕ) (f : ℕ × ℕ → ℕ) (v : ℕ → Bool) : SelSt K (n * n * entryBits n) :=
  updC D (blockSize G n) u (outsRun1 D n G K codes u f v)
    (if u = 0 then selInit K _ else stIn n K u f)

/-- The candidates' packed values on a run-1 edge. -/
noncomputable def valRun1 (e : ℕ × ℕ) (f : ℕ × ℕ → ℕ) (v : ℕ → Bool) : ℕ :=
  packK (D.profileCap n G e) K
    (fun a => (clampCode D n G (codes a)).enc e (inRun1 D n G K a f) (maskRows D n G e.1 v))

/-- The values into a run-2 node, indexed by `D`'s edges. -/
noncomputable def inRun2 (f : ℕ × ℕ → ℕ) : ℕ × ℕ → ℕ :=
  fun e'' => if e'' ∈ D.edges (blockSize G n) then selRaw n K f (P + e''.1, P + e''.2) else 0

/-- **The selection code** on `selDiagram D K P r L`. -/
noncomputable def selCode : NetCode where
  enc e f v :=
    if e.1 < D.nodes (blockSize G n) then
      (if e ∈ D.edges (blockSize G n) then
        (if e.2 = e.1 + 1 then
          encS (stRun1 D n G K codes e.1 f v) +
            2 ^ selBits K (n * n * entryBits n) * valRun1 D n G K codes e f v
        else valRun1 D n G K codes e f v)
      else if e.2 = e.1 + 1 then encS (stRun1 D n G K codes e.1 f v) else 0)
    else if e.1 < P then
      (if e.2 = e.1 + 1 then encS (updF n (entryBits n) v (stIn n K e.1 f)) else 0)
    else
      (if (e.1 - P, e.2 - P) ∈ D.edges (blockSize G n) then
        (if e.2 = e.1 + 1 then
          encS (stIn n K e.1 f) + 2 ^ selBits K (n * n * entryBits n) *
            (clampCode D n G (codes (winner (stIn n K e.1 f)))).enc (e.1 - P, e.2 - P)
              (inRun2 D n G K P f) v
        else (clampCode D n G (codes (winner (stIn n K e.1 f)))).enc (e.1 - P, e.2 - P)
              (inRun2 D n G K P f) v)
      else 0)
  dec o f v :=
    (codes (winner (stIn n K (P + D.outNode (blockSize G n) o) f))).dec o (inRun2 D n G K P f) v

end Code

/-! ### The intended state -/

section State

variable {k : ℕ} (D : TSDiagram k) (n G K P : ℕ) (codes : ℕ → NetCode)
  (x : Fin (n * n * entryBits n) → Bool)

/-- Candidate `a`'s output bit at position `o` in `D` (clamped code), on input `x`. -/
noncomputable def outD (a o : ℕ) : Bool :=
  (clampCode D n G (codes a)).outVal (D.edges (blockSize G n))
    (fun y => D.visible n (entryBits n) (blockSize G n) y x) (D.outNode (blockSize G n) o) o

/-- The candidates' output bits at node `u`, at the positions output there. -/
noncomputable def outsD (u : ℕ) : Fin K → ℕ → Bool :=
  fun a o => if D.outNode (blockSize G n) o = u then outD D n G codes x a o else false

/-- The intended state after node `u`: comparisons in run 1, then fetches in the epilogue. -/
noncomputable def stateAt : ℕ → SelSt K (n * n * entryBits n)
  | 0 => updC D (blockSize G n) 0 (outsD D n G K codes x 0) (selInit K _)
  | u + 1 => if u + 1 < D.nodes (blockSize G n) then
      updC D (blockSize G n) (u + 1) (outsD D n G K codes x (u + 1)) (stateAt u)
    else updF n (entryBits n)
      ((selDiagram D K P (blockSize G n) (n * n * entryBits n)).visible n (entryBits n)
        (blockSize G n) (u + 1) x) (stateAt u)

/-- The run-1 invariant at the nodes `< m`: recorded positions are genuine differences with the
first candidate's bit; pairs with nothing recorded agree on every position output before `m`; nothing
is fetched yet. -/
def RunInv (σ : SelSt K (n * n * entryBits n)) (m : ℕ) : Prop :=
  ∀ a b : Fin K,
    (∀ p, σ.1 a b = some p →
      p.2 = outD D n G codes x a p.1 ∧ outD D n G codes x a p.1 ≠ outD D n G codes x b p.1) ∧
    (σ.1 a b = none → ∀ o : Fin (n * n * entryBits n),
      D.outNode (blockSize G n) o < m → outD D n G codes x a o = outD D n G codes x b o) ∧
    σ.2 a b = false

theorem runInv_init : RunInv D n G K codes x (selInit K _) 0 := by
  intro a b
  refine ⟨fun p hp => by simp [selInit] at hp, fun _ o ho => absurd ho (Nat.not_lt_zero _), rfl⟩

theorem runInv_updC {σ : SelSt K (n * n * entryBits n)} {u : ℕ}
    (hσ : RunInv D n G K codes x σ u) :
    RunInv D n G K codes x (updC D (blockSize G n) u (outsD D n G K codes x u) σ) (u + 1) := by
  intro a b
  obtain ⟨hsome, hnone, hfetch⟩ := hσ a b
  refine ⟨?_, ?_, hfetch⟩
  · intro p hp
    simp only [updC] at hp
    by_cases hs : (σ.1 a b).isSome
    · rw [ite_eq_left hs] at hp
      exact hsome p hp
    · rw [ite_eq_right hs] at hp
      by_cases h : ∃ o : Fin (n * n * entryBits n), D.outNode (blockSize G n) o = u ∧
          outsD D n G K codes x u a o ≠ outsD D n G K codes x u b o
      · rw [dite_eq_left h] at hp
        obtain ⟨hu, hne⟩ := Classical.choose_spec h
        have e1 : ∀ c : Fin K,
            outsD D n G K codes x u c (Classical.choose h : Fin (n * n * entryBits n)) =
            outD D n G codes x c (Classical.choose h : Fin (n * n * entryBits n)) :=
          fun c => ite_eq_left hu
        rw [e1, e1] at hne
        rw [← Option.some_injective _ hp]
        exact ⟨e1 a, hne⟩
      · rw [dite_eq_right h] at hp
        simp at hp
  · intro hn o ho
    simp only [updC] at hn
    by_cases hs : (σ.1 a b).isSome
    · rw [ite_eq_left hs] at hn
      rw [hn] at hs; simp at hs
    · rw [ite_eq_right hs] at hn
      have hnone' : σ.1 a b = none := Option.not_isSome_iff_eq_none.1 hs
      by_cases h : ∃ o : Fin (n * n * entryBits n), D.outNode (blockSize G n) o = u ∧
          outsD D n G K codes x u a o ≠ outsD D n G K codes x u b o
      · rw [dite_eq_left h] at hn; simp at hn
      · rcases Nat.lt_or_ge (D.outNode (blockSize G n) o) u with hlt | hge
        · exact hnone hnone' o hlt
        · have hu : D.outNode (blockSize G n) o = u := by omega
          by_contra hne
          refine h ⟨o, hu, ?_⟩
          have e1 : ∀ c : Fin K, outsD D n G K codes x u c o = outD D n G codes x c o :=
            fun c => ite_eq_left hu
          rw [e1, e1]; exact hne

/-- **The run-1 invariant** holds after every run-1 node. -/
theorem runInv_stateAt : ∀ u, u < D.nodes (blockSize G n) →
    RunInv D n G K codes x (stateAt D n G K P codes x u) (u + 1) := by
  intro u
  induction u with
  | zero => intro _; exact runInv_updC D n G K codes x (runInv_init D n G K codes x)
  | succ u ih =>
    intro hu
    simp only [stateAt, ite_eq_left hu]
    exact runInv_updC D n G K codes x (ih (by omega))

/-- In the epilogue the recorded positions stay, and a fetched bit is set exactly when some epilogue
node so far sees the true bit `1`. -/
theorem stateAt_epi (hN : 1 ≤ D.nodes (blockSize G n)) : ∀ j,
    (stateAt D n G K P codes x (D.nodes (blockSize G n) - 1 + j)).1 =
      (stateAt D n G K P codes x (D.nodes (blockSize G n) - 1)).1 ∧
    ∀ a b p, (stateAt D n G K P codes x (D.nodes (blockSize G n) - 1)).1 a b = some p →
      ((stateAt D n G K P codes x (D.nodes (blockSize G n) - 1 + j)).2 a b = true ↔
        ∃ y, D.nodes (blockSize G n) ≤ y ∧ y ≤ D.nodes (blockSize G n) - 1 + j ∧
          (selDiagram D K P (blockSize G n) (n * n * entryBits n)).visible n (entryBits n)
            (blockSize G n) y x (tpos n (entryBits n) p.1) = true) := by
  intro j
  induction j with
  | zero =>
    refine ⟨rfl, fun a b p _ => ?_⟩
    have hf := ((runInv_stateAt D n G K P codes x (D.nodes (blockSize G n) - 1) (by omega)) a b).2.2
    rw [Nat.add_zero, hf]
    simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
    intro y h1 h2; omega
  | succ j ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hstep : stateAt D n G K P codes x (D.nodes (blockSize G n) - 1 + (j + 1)) =
        updF n (entryBits n)
          ((selDiagram D K P (blockSize G n) (n * n * entryBits n)).visible n (entryBits n)
            (blockSize G n) (D.nodes (blockSize G n) - 1 + j + 1) x)
          (stateAt D n G K P codes x (D.nodes (blockSize G n) - 1 + j)) := by
      rw [show D.nodes (blockSize G n) - 1 + (j + 1) = D.nodes (blockSize G n) - 1 + j + 1 by omega]
      simp only [stateAt]
      rw [ite_eq_right (by omega)]
    refine ⟨by rw [hstep]; exact ih1, fun a b p hp => ?_⟩
    rw [hstep]
    simp only [updF]
    rw [ih1, hp]
    simp only [Bool.or_eq_true]
    rw [ih2 a b p hp]
    constructor
    · rintro (⟨y, h1, h2, h3⟩ | h)
      · exact ⟨y, h1, by omega, h3⟩
      · exact ⟨_, by omega, by omega, h⟩
    · rintro ⟨y, h1, h2, h3⟩
      by_cases hy : y ≤ D.nodes (blockSize G n) - 1 + j
      · exact Or.inl ⟨y, h1, hy, h3⟩
      · right
        have : y = D.nodes (blockSize G n) - 1 + j + 1 := by omega
        rw [← this]; exact h3

end State

/-! ### Unfolding the selection code -/

section Unfold

variable {k : ℕ} (D : TSDiagram k) (n G K P : ℕ) (codes : ℕ → NetCode) (e : ℕ × ℕ)
  (f : ℕ × ℕ → ℕ) (v : ℕ → Bool)

theorem selCode_run1_D (h1 : e.1 < D.nodes (blockSize G n)) (hE : e ∈ D.edges (blockSize G n)) :
    (selCode D n G K P codes).enc e f v =
      if e.2 = e.1 + 1 then encS (stRun1 D n G K codes e.1 f v) +
        2 ^ selBits K (n * n * entryBits n) * valRun1 D n G K codes e f v
      else valRun1 D n G K codes e f v := by
  show (if e.1 < D.nodes (blockSize G n) then _ else _) = _
  rw [ite_eq_left h1, ite_eq_left hE]

theorem selCode_run1_notD (h1 : e.1 < D.nodes (blockSize G n)) (hE : e ∉ D.edges (blockSize G n)) :
    (selCode D n G K P codes).enc e f v =
      if e.2 = e.1 + 1 then encS (stRun1 D n G K codes e.1 f v) else 0 := by
  show (if e.1 < D.nodes (blockSize G n) then _ else _) = _
  rw [ite_eq_left h1, ite_eq_right hE]

theorem selCode_epi (h1 : ¬ e.1 < D.nodes (blockSize G n)) (h2 : e.1 < P) :
    (selCode D n G K P codes).enc e f v =
      if e.2 = e.1 + 1 then encS (updF n (entryBits n) v (stIn n K e.1 f)) else 0 := by
  show (if e.1 < D.nodes (blockSize G n) then _ else _) = _
  rw [ite_eq_right h1, ite_eq_left h2]

theorem selCode_run2 (h1 : ¬ e.1 < D.nodes (blockSize G n)) (h2 : ¬ e.1 < P) :
    (selCode D n G K P codes).enc e f v =
      if (e.1 - P, e.2 - P) ∈ D.edges (blockSize G n) then
        (if e.2 = e.1 + 1 then
          encS (stIn n K e.1 f) + 2 ^ selBits K (n * n * entryBits n) *
            (clampCode D n G (codes (winner (stIn n K e.1 f)))).enc (e.1 - P, e.2 - P)
              (inRun2 D n G K P f) v
        else (clampCode D n G (codes (winner (stIn n K e.1 f)))).enc (e.1 - P, e.2 - P)
              (inRun2 D n G K P f) v)
      else 0 := by
  show (if e.1 < D.nodes (blockSize G n) then _ else _) = _
  rw [ite_eq_right h1, ite_eq_right h2]

end Unfold

theorem maskRows_sel {k : ℕ} (D : TSDiagram k) (n G K P : ℕ) (hr : 1 ≤ blockSize G n) (u : ℕ)
    (x : Fin (n * n * entryBits n) → Bool) :
    maskRows D n G u ((selDiagram D K P (blockSize G n) (n * n * entryBits n)).visible n
      (entryBits n) (blockSize G n) u x) = D.visible n (entryBits n) (blockSize G n) u x := by
  funext d
  simp only [maskRows, TSDiagram.visible]
  by_cases h1 : d / (n * entryBits n) ∈ D.rowsAt n (entryBits n) (blockSize G n) u
  · have h2 := rowsAt_sel_run1 D (K := K) (P := P) (L := n * n * entryBits n) hr h1
    simp [h1, h2]
  · simp [h1]

theorem selRoom_nodes {k : ℕ} {D : TSDiagram k} {P r L : ℕ} (hr : 1 ≤ r) (hP : SelRoom D P r L) :
    D.nodes r + 2 ≤ P := by
  unfold SelRoom at hP
  have : (D.nodes r + 2) * r ≤ P * r := by nlinarith
  exact Nat.le_of_mul_le_mul_right this (by omega)

/-! ### Run 1 and the epilogue -/

/-- **Run 1 and the epilogue.** Into a run-1 node, the digits of the packed values are the clamped
candidates' values in `D`; the memory edge into every node `u ≤ P` carries the intended state of node
`u - 1` in its low bits. -/
theorem sel_main {k : ℕ} (D : TSDiagram k) {n G K P : ℕ} (codes : ℕ → NetCode)
    (x : Fin (n * n * entryBits n) → Bool) (hG : 1 ≤ G) (hn : 1 ≤ n) (hK : 1 ≤ K)
    (hD : D.Valid (n * n * entryBits n))
    (hP : SelRoom D P (blockSize G n) (n * n * entryBits n)) :
    ∀ u, u ≤ P →
      (u < D.nodes (blockSize G n) → ∀ a : Fin K,
        inRun1 D n G K a ((selCode D n G K P codes).inVals
          ((selDiagram D K P (blockSize G n) (n * n * entryBits n)).edges (blockSize G n))
          (fun y => (selDiagram D K P (blockSize G n) (n * n * entryBits n)).visible n
            (entryBits n) (blockSize G n) y x) u) =
        (clampCode D n G (codes a)).inVals (D.edges (blockSize G n))
          (fun y => D.visible n (entryBits n) (blockSize G n) y x) u) ∧
      (1 ≤ u → (selCode D n G K P codes).inVals
          ((selDiagram D K P (blockSize G n) (n * n * entryBits n)).edges (blockSize G n))
          (fun y => (selDiagram D K P (blockSize G n) (n * n * entryBits n)).visible n
            (entryBits n) (blockSize G n) y x) u (u - 1, u) % 2 ^ selBits K (n * n * entryBits n) =
        encS (stateAt D n G K P codes x (u - 1))) := by
  have hr : 1 ≤ blockSize G n := one_le_blockSize hG hn
  have hPN := selRoom_nodes hr hP
  have hL1 : 1 ≤ n * n * entryBits n :=
    Nat.one_le_iff_ne_zero.2 (by unfold entryBits; positivity)
  have hN : 1 ≤ D.nodes (blockSize G n) :=
    (numSlots_spec hr).2 (by have := one_le_T hD hL1; simp only [Nat.zero_mul]; omega)
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
  intro hu
  refine ⟨fun huN a => ?_, fun hu1 => ?_⟩
  · -- the digits into a run-1 node
    funext e'
    show (if e' ∈ D.edges (blockSize G n) then digit D n G a e' (selRaw n K
      ((selCode D n G K P codes).inVals
        ((selDiagram D K P (blockSize G n) (n * n * entryBits n)).edges (blockSize G n))
        (fun y => (selDiagram D K P (blockSize G n) (n * n * entryBits n)).visible n
          (entryBits n) (blockSize G n) y x) u) e') else 0) = _
    rw [inVals_eq (clampCode D n G (codes a))]
    by_cases hc : e' ∈ D.edges (blockSize G n) ∧ e'.2 = u ∧ e'.1 < u
    · rw [ite_eq_left hc.1, ite_eq_left hc]
      have hE : e' ∈ (selDiagram D K P (blockSize G n) (n * n * entryBits n)).edges
          (blockSize G n) := edges_sel_run1 D hr hK hc.1
      have h1 : e'.1 < D.nodes (blockSize G n) := by omega
      have hA := (ih e'.1 (by omega) (by omega)).1 h1
      have hraw : selRaw n K ((selCode D n G K P codes).inVals
          ((selDiagram D K P (blockSize G n) (n * n * entryBits n)).edges (blockSize G n))
          (fun y => (selDiagram D K P (blockSize G n) (n * n * entryBits n)).visible n
            (entryBits n) (blockSize G n) y x) u) e' =
          valRun1 D n G K codes e' ((selCode D n G K P codes).inVals
            ((selDiagram D K P (blockSize G n) (n * n * entryBits n)).edges (blockSize G n))
            (fun y => (selDiagram D K P (blockSize G n) (n * n * entryBits n)).visible n
              (entryBits n) (blockSize G n) y x) e'.1)
            ((selDiagram D K P (blockSize G n) (n * n * entryBits n)).visible n
              (entryBits n) (blockSize G n) e'.1 x) := by
        have hval : (selCode D n G K P codes).inVals
            ((selDiagram D K P (blockSize G n) (n * n * entryBits n)).edges (blockSize G n))
            (fun y => (selDiagram D K P (blockSize G n) (n * n * entryBits n)).visible n
              (entryBits n) (blockSize G n) y x) u e' =
            (selCode D n G K P codes).enc e' ((selCode D n G K P codes).inVals
              ((selDiagram D K P (blockSize G n) (n * n * entryBits n)).edges (blockSize G n))
              (fun y => (selDiagram D K P (blockSize G n) (n * n * entryBits n)).visible n
                (entryBits n) (blockSize G n) y x) e'.1)
              ((selDiagram D K P (blockSize G n) (n * n * entryBits n)).visible n
                (entryBits n) (blockSize G n) e'.1 x) := by
          rw [inVals_eq, ite_eq_left ⟨hE, hc.2⟩]
        unfold selRaw
        rw [hval, selCode_run1_D D n G K P codes e' _ _ h1 hc.1]
        by_cases hm : e'.2 = e'.1 + 1
        · rw [ite_eq_left hm, ite_eq_left hm, unpackS]
        · rw [ite_eq_right hm, ite_eq_right hm]
      rw [hraw]
      unfold digit valRun1
      rw [digit_packK (fun b _ => clamp_lt D n G _ _ _ _) a.2, hA a, maskRows_sel D n G K P hr]
    · by_cases hE' : e' ∈ D.edges (blockSize G n)
      · rw [ite_eq_left hE', ite_eq_right hc]
        have h0 : (selCode D n G K P codes).inVals
            ((selDiagram D K P (blockSize G n) (n * n * entryBits n)).edges (blockSize G n))
            (fun y => (selDiagram D K P (blockSize G n) (n * n * entryBits n)).visible n
              (entryBits n) (blockSize G n) y x) u e' = 0 := by
          rw [inVals_eq, ite_eq_right]
          intro h; exact hc ⟨hE', h.2⟩
        unfold selRaw digit
        rw [h0]
        simp
      · rw [ite_eq_right hE', ite_eq_right (fun h => hE' h.1)]
  · -- the state on the memory edge into `u`
    have hmemE : (u - 1, u) ∈ (selDiagram D K P (blockSize G n) (n * n * entryBits n)).edges
        (blockSize G n) := by
      apply Finset.mem_union_left
      rw [mem_memEdges, nodes_sel D hr]
      simp only
      omega
    rw [inVals_eq, ite_eq_left ⟨hmemE, rfl, by simp only; omega⟩]
    by_cases h1 : u - 1 < D.nodes (blockSize G n)
    · -- from a run-1 node
      obtain ⟨ihA, ihB⟩ := ih (u - 1) (by omega) (by omega)
      have houts : outsRun1 D n G K codes (u - 1) ((selCode D n G K P codes).inVals
          ((selDiagram D K P (blockSize G n) (n * n * entryBits n)).edges (blockSize G n))
          (fun y => (selDiagram D K P (blockSize G n) (n * n * entryBits n)).visible n
            (entryBits n) (blockSize G n) y x) (u - 1))
          ((selDiagram D K P (blockSize G n) (n * n * entryBits n)).visible n
            (entryBits n) (blockSize G n) (u - 1) x) = outsD D n G K codes x (u - 1) := by
        funext a o
        unfold outsRun1 outsD
        by_cases ho : D.outNode (blockSize G n) o = u - 1
        · rw [ite_eq_left ho, ite_eq_left ho, ihA h1 a, maskRows_sel D n G K P hr]
          unfold outD NetCode.outVal
          rw [ho]
          rfl
        · rw [ite_eq_right ho, ite_eq_right ho]
      have hst : stRun1 D n G K codes (u - 1) ((selCode D n G K P codes).inVals
          ((selDiagram D K P (blockSize G n) (n * n * entryBits n)).edges (blockSize G n))
          (fun y => (selDiagram D K P (blockSize G n) (n * n * entryBits n)).visible n
            (entryBits n) (blockSize G n) y x) (u - 1))
          ((selDiagram D K P (blockSize G n) (n * n * entryBits n)).visible n
            (entryBits n) (blockSize G n) (u - 1) x) = stateAt D n G K P codes x (u - 1) := by
        unfold stRun1
        rw [houts]
        rcases Nat.eq_zero_or_pos (u - 1) with h0 | hpos
        · rw [ite_eq_left h0, h0]
          rfl
        · rw [ite_eq_right (by omega)]
          have hin : stIn n K (u - 1) ((selCode D n G K P codes).inVals
              ((selDiagram D K P (blockSize G n) (n * n * entryBits n)).edges (blockSize G n))
              (fun y => (selDiagram D K P (blockSize G n) (n * n * entryBits n)).visible n
                (entryBits n) (blockSize G n) y x) (u - 1)) =
              stateAt D n G K P codes x (u - 1 - 1) := by
            unfold stIn
            rw [ihB (by omega), decS_encS]
          rw [hin]
          obtain ⟨m, hm⟩ : ∃ m, u - 1 = m + 1 := ⟨u - 2, by omega⟩
          rw [hm] at h1 ⊢
          simp only [stateAt, ite_eq_left h1, Nat.add_sub_cancel]
      by_cases hE : (u - 1, u) ∈ D.edges (blockSize G n)
      · rw [selCode_run1_D D n G K P codes _ _ _ h1 hE, ite_eq_left (by simp only; omega),
          Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (encS_lt _), hst]
      · rw [selCode_run1_notD D n G K P codes _ _ _ h1 hE, ite_eq_left (by simp only; omega),
          Nat.mod_eq_of_lt (encS_lt _), hst]
    · -- from an epilogue node
      obtain ⟨-, ihB⟩ := ih (u - 1) (by omega) (by omega)
      rw [selCode_epi D n G K P codes _ _ _ h1 (by simp only; omega),
        ite_eq_left (by simp only; omega), Nat.mod_eq_of_lt (encS_lt _)]
      have hin : stIn n K (u - 1) ((selCode D n G K P codes).inVals
          ((selDiagram D K P (blockSize G n) (n * n * entryBits n)).edges (blockSize G n))
          (fun y => (selDiagram D K P (blockSize G n) (n * n * entryBits n)).visible n
            (entryBits n) (blockSize G n) y x) (u - 1)) =
          stateAt D n G K P codes x (u - 1 - 1) := by
        unfold stIn
        rw [ihB (by omega), decS_encS]
      simp only at hin ⊢
      rw [hin]
      obtain ⟨m, hm⟩ : ∃ m, u - 1 = m + 1 := ⟨u - 2, by omega⟩
      rw [hm] at h1 ⊢
      simp only [stateAt, ite_eq_right h1, Nat.add_sub_cancel]

/-! ### Run 2 -/

/-- **Run 2.** Every memory edge into run 2 carries the final state, and the values into a run-2 node
are the winner's clamped values in `D`. -/
theorem sel_run2 {k : ℕ} (D : TSDiagram k) {n G K P : ℕ} (codes : ℕ → NetCode)
    (x : Fin (n * n * entryBits n) → Bool) (hG : 1 ≤ G) (hn : 1 ≤ n) (hK : 1 ≤ K)
    (hD : D.Valid (n * n * entryBits n))
    (hP : SelRoom D P (blockSize G n) (n * n * entryBits n)) :
    ∀ u', u' < D.nodes (blockSize G n) →
      (selCode D n G K P codes).inVals
          ((selDiagram D K P (blockSize G n) (n * n * entryBits n)).edges (blockSize G n))
          (fun y => (selDiagram D K P (blockSize G n) (n * n * entryBits n)).visible n
            (entryBits n) (blockSize G n) y x) (P + u') (P + u' - 1, P + u') %
          2 ^ selBits K (n * n * entryBits n) = encS (stateAt D n G K P codes x (P - 1)) ∧
      inRun2 D n G K P ((selCode D n G K P codes).inVals
          ((selDiagram D K P (blockSize G n) (n * n * entryBits n)).edges (blockSize G n))
          (fun y => (selDiagram D K P (blockSize G n) (n * n * entryBits n)).visible n
            (entryBits n) (blockSize G n) y x) (P + u')) =
        (clampCode D n G (codes (winner (stateAt D n G K P codes x (P - 1))))).inVals
          (D.edges (blockSize G n)) (fun y => D.visible n (entryBits n) (blockSize G n) y x) u' := by
  have hr : 1 ≤ blockSize G n := one_le_blockSize hG hn
  have hPN := selRoom_nodes hr hP
  intro u'
  induction u' using Nat.strong_induction_on with
  | _ u' ih =>
  intro hu'
  have hstate : (selCode D n G K P codes).inVals
      ((selDiagram D K P (blockSize G n) (n * n * entryBits n)).edges (blockSize G n))
      (fun y => (selDiagram D K P (blockSize G n) (n * n * entryBits n)).visible n
        (entryBits n) (blockSize G n) y x) (P + u') (P + u' - 1, P + u') %
      2 ^ selBits K (n * n * entryBits n) = encS (stateAt D n G K P codes x (P - 1)) := by
    rcases Nat.eq_zero_or_pos u' with h0 | hpos
    · subst h0
      simp only [Nat.add_zero]
      exact (sel_main D codes x hG hn hK hD hP P le_rfl).2 (by omega)
    · have hDmem : (u' - 1, u') ∈ D.edges (blockSize G n) := by
        apply Finset.mem_union_left
        rw [mem_memEdges]
        simp only
        omega
      have hmemE : (P + u' - 1, P + u') ∈
          (selDiagram D K P (blockSize G n) (n * n * entryBits n)).edges (blockSize G n) := by
        have := (mem_edges_sel_add D (K := K) (P := P) hr hD (by omega) (u' - 1) u').2 hDmem
        rwa [show P + (u' - 1) = P + u' - 1 by omega] at this
      rw [inVals_eq, ite_eq_left ⟨hmemE, rfl, by simp only; omega⟩,
        selCode_run2 D n G K P codes _ _ _ (by simp only; omega) (by simp only; omega)]
      simp only
      rw [show P + u' - 1 - P = u' - 1 by omega, Nat.add_sub_cancel_left, ite_eq_left hDmem,
        ite_eq_left (by omega), Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (encS_lt _)]
      congr 1
      unfold stIn
      have h := (ih (u' - 1) (by omega) (by omega)).1
      rw [show P + (u' - 1) = P + u' - 1 by omega] at h
      rw [h, decS_encS]
  refine ⟨hstate, ?_⟩
  funext e''
  show (if e'' ∈ D.edges (blockSize G n) then selRaw n K ((selCode D n G K P codes).inVals
      ((selDiagram D K P (blockSize G n) (n * n * entryBits n)).edges (blockSize G n))
      (fun y => (selDiagram D K P (blockSize G n) (n * n * entryBits n)).visible n
        (entryBits n) (blockSize G n) y x) (P + u')) (P + e''.1, P + e''.2) else 0) = _
  rw [inVals_eq (clampCode D n G (codes _))]
  by_cases hc : e'' ∈ D.edges (blockSize G n) ∧ e''.2 = u' ∧ e''.1 < u'
  · rw [ite_eq_left hc.1, ite_eq_left hc]
    have hE : (P + e''.1, P + e''.2) ∈
        (selDiagram D K P (blockSize G n) (n * n * entryBits n)).edges (blockSize G n) :=
      (mem_edges_sel_add D hr hD (by omega) _ _).2 hc.1
    have hval : (selCode D n G K P codes).inVals
        ((selDiagram D K P (blockSize G n) (n * n * entryBits n)).edges (blockSize G n))
        (fun y => (selDiagram D K P (blockSize G n) (n * n * entryBits n)).visible n
          (entryBits n) (blockSize G n) y x) (P + u') (P + e''.1, P + e''.2) =
        (selCode D n G K P codes).enc (P + e''.1, P + e''.2)
          ((selCode D n G K P codes).inVals
            ((selDiagram D K P (blockSize G n) (n * n * entryBits n)).edges (blockSize G n))
            (fun y => (selDiagram D K P (blockSize G n) (n * n * entryBits n)).visible n
              (entryBits n) (blockSize G n) y x) (P + e''.1))
          ((selDiagram D K P (blockSize G n) (n * n * entryBits n)).visible n
            (entryBits n) (blockSize G n) (P + e''.1) x) := by
      rw [inVals_eq, ite_eq_left ⟨hE, by simp only; omega, by simp only; omega⟩]
    obtain ⟨ihS, ihI⟩ := ih e''.1 hc.2.2 (by omega)
    have hst : stIn n K (P + e''.1) ((selCode D n G K P codes).inVals
        ((selDiagram D K P (blockSize G n) (n * n * entryBits n)).edges (blockSize G n))
        (fun y => (selDiagram D K P (blockSize G n) (n * n * entryBits n)).visible n
          (entryBits n) (blockSize G n) y x) (P + e''.1)) = stateAt D n G K P codes x (P - 1) := by
      unfold stIn
      rw [ihS, decS_encS]
    unfold selRaw
    rw [hval, selCode_run2 D n G K P codes _ _ _ (by simp only; omega) (by simp only; omega)]
    simp only [Nat.add_sub_cancel_left]
    rw [ite_eq_left (hc.1 : (e''.1, e''.2) ∈ D.edges (blockSize G n)), hst, ihI,
      visible_sel_add D hr hP]
    by_cases hm : e''.2 = e''.1 + 1
    · rw [ite_eq_left (show P + e''.2 = P + e''.1 + 1 by omega),
        ite_eq_left (show P + e''.2 = P + e''.1 + 1 by omega), unpackS]
    · rw [ite_eq_right (show ¬ P + e''.2 = P + e''.1 + 1 by omega),
        ite_eq_right (show ¬ P + e''.2 = P + e''.1 + 1 by omega)]
  · by_cases hE' : e'' ∈ D.edges (blockSize G n)
    · rw [ite_eq_left hE', ite_eq_right hc]
      have h0 : (selCode D n G K P codes).inVals
          ((selDiagram D K P (blockSize G n) (n * n * entryBits n)).edges (blockSize G n))
          (fun y => (selDiagram D K P (blockSize G n) (n * n * entryBits n)).visible n
            (entryBits n) (blockSize G n) y x) (P + u') (P + e''.1, P + e''.2) = 0 := by
        rw [inVals_eq, ite_eq_right]
        intro h
        apply hc
        refine ⟨hE', ?_, ?_⟩ <;> simp only at h <;> omega
      unfold selRaw
      rw [h0]
      simp
    · rw [ite_eq_right hE', ite_eq_right (fun h => hE' h.1)]

/-! ### The winner is correct -/

/-- **The winner is correct.** If some candidate solves the input, every candidate that differs from
it loses at a recorded position, and it never loses; so the winner's outputs are the transposed
input. -/
theorem winner_correct {k : ℕ} (D : TSDiagram k) {n G K P : ℕ} (codes : ℕ → NetCode)
    (x : Fin (n * n * entryBits n) → Bool) (hG : 1 ≤ G) (hn : 1 ≤ n)
    (hD : D.Valid (n * n * entryBits n))
    (hP : SelRoom D P (blockSize G n) (n * n * entryBits n))
    (hcov : ∃ c < K, D.Solves n G (D.profileCap n G) {x} (codes c)) :
    ∀ o (ho : o < n * n * entryBits n),
      outD D n G codes x (winner (stateAt D n G K P codes x (P - 1))) o =
        x ⟨tpos n (entryBits n) o, tpos_lt ho⟩ := by
  have hr : 1 ≤ blockSize G n := one_le_blockSize hG hn
  have hPN := selRoom_nodes hr hP
  have hL1 : 1 ≤ n * n * entryBits n :=
    Nat.one_le_iff_ne_zero.2 (by unfold entryBits; positivity)
  have hw : 1 ≤ entryBits n := by unfold entryBits; omega
  have hN : 1 ≤ D.nodes (blockSize G n) :=
    (numSlots_spec hr).2 (by have := one_le_T hD hL1; simp only [Nat.zero_mul]; omega)
  obtain ⟨c, hcK, hsol⟩ := hcov
  obtain ⟨hcap, hout⟩ := hsol x rfl
  -- the correct candidate's outputs
  have hcorr : ∀ o (ho : o < n * n * entryBits n),
      outD D n G codes x c o = x ⟨tpos n (entryBits n) o, tpos_lt ho⟩ := by
    intro o ho
    have h := hout (tpos n (entryBits n) o) (tpos_lt ho)
    rw [tpos_tpos ho] at h
    unfold outD NetCode.outVal
    rw [clamp_inVals D n G (codes c) _ _ hcap]
    exact h
  -- the final state
  have hepi := stateAt_epi D n G K P codes x hN (P - D.nodes (blockSize G n))
  rw [show D.nodes (blockSize G n) - 1 + (P - D.nodes (blockSize G n)) = P - 1 by omega] at hepi
  obtain ⟨h1, h2⟩ := hepi
  have hinv := runInv_stateAt D n G K P codes x (D.nodes (blockSize G n) - 1) (by omega)
  rw [show D.nodes (blockSize G n) - 1 + 1 = D.nodes (blockSize G n) by omega] at hinv
  -- the fetched bits are the true bits
  have hfetch : ∀ a b p, (stateAt D n G K P codes x (P - 1)).1 a b = some p →
      (stateAt D n G K P codes x (P - 1)).2 a b =
        x ⟨tpos n (entryBits n) p.1, tpos_lt p.1.2⟩ := by
    intro a b p hp
    rw [h1] at hp
    have hiff := h2 a b p hp
    have hd : tpos n (entryBits n) p.1 < n * n * entryBits n := tpos_lt p.1.2
    have hi : tpos n (entryBits n) p.1 / (n * entryBits n) < n := by
      rw [Nat.div_lt_iff_lt_mul (by positivity)]
      have : n * n * entryBits n = n * (n * entryBits n) := by ring
      omega
    obtain ⟨y₀, hy₀1, hy₀2, hy₀⟩ := row_mem_epi D (K := K) hr hD hP (n := n) (w := entryBits n) rfl
      hw hi
    have hvis : ∀ y, (selDiagram D K P (blockSize G n) (n * n * entryBits n)).visible n
        (entryBits n) (blockSize G n) y x (tpos n (entryBits n) p.1) = true →
        x ⟨tpos n (entryBits n) p.1, hd⟩ = true := by
      intro y hy
      simp only [TSDiagram.visible, dite_eq_left hd] at hy
      split_ifs at hy
      exact hy
    have hvis0 : (selDiagram D K P (blockSize G n) (n * n * entryBits n)).visible n
        (entryBits n) (blockSize G n) y₀ x (tpos n (entryBits n) p.1) =
        x ⟨tpos n (entryBits n) p.1, hd⟩ := by
      simp only [TSDiagram.visible, dite_eq_left hd, ite_eq_left hy₀]
    cases hx : x ⟨tpos n (entryBits n) p.1, hd⟩
    · cases hσ : (stateAt D n G K P codes x (P - 1)).2 a b
      · rfl
      · exfalso
        obtain ⟨y, -, -, hy⟩ := hiff.1 hσ
        have := hvis y hy
        rw [hx] at this
        exact Bool.false_ne_true this
    · exact hiff.2 ⟨y₀, hy₀1, by omega, by rw [hvis0, hx]⟩
  -- the correct candidate never loses
  have hgood : SelGood (stateAt D n G K P codes x (P - 1)) ⟨c, hcK⟩ := by
    intro b p hp
    rw [hfetch _ _ p hp]
    rw [h1] at hp
    rw [((hinv ⟨c, hcK⟩ b).1 p hp).1]
    exact hcorr p.1 p.1.2
  obtain ⟨a, ha, hga⟩ := winner_good ⟨_, hgood⟩
  intro o ho
  rw [← ha]
  by_contra hne
  have hne' : outD D n G codes x a o ≠ outD D n G codes x c o := by
    rw [hcorr o ho]; exact hne
  cases hσ : (stateAt D n G K P codes x (P - 1)).1 a ⟨c, hcK⟩ with
  | none =>
    rw [h1] at hσ
    exact hne' ((hinv a ⟨c, hcK⟩).2.1 hσ ⟨o, ho⟩ (outNode_lt hD hr hL1 o))
  | some p =>
    have hgp := hga ⟨c, hcK⟩ p hσ
    rw [hfetch _ _ p hσ] at hgp
    rw [h1] at hσ
    obtain ⟨hp1, hp2⟩ := (hinv a ⟨c, hcK⟩).1 p hσ
    apply hp2
    rw [← hp1, hgp, hcorr p.1 p.1.2]

/-! ### Selection solves every input -/

theorem pack_state_lt {s p a b : ℕ} (ha : a < 2 ^ s) (hb : b < 2 ^ p) : a + 2 ^ s * b < 2 ^ (p + s) := by
  calc a + 2 ^ s * b < 2 ^ s + 2 ^ s * b := by omega
    _ = 2 ^ s * (b + 1) := by ring
    _ ≤ 2 ^ s * 2 ^ p := Nat.mul_le_mul_left _ hb
    _ = 2 ^ (p + s) := by rw [← pow_add, Nat.add_comm]

theorem mem_memEdges_of_edges {k : ℕ} (D : TSDiagram k) {r : ℕ} {e : ℕ × ℕ} (he : e ∈ D.edges r)
    (hm : e.2 = e.1 + 1) : e ∈ D.memEdges r := by
  rcases Finset.mem_union.1 he with h | h
  · exact h
  · rw [mem_chordEdges] at h
    obtain ⟨-, -, t, β, hc⟩ := h
    have := hc.1
    omega

theorem mem_chordEdges_of_edges {k : ℕ} (D : TSDiagram k) {r : ℕ} {e : ℕ × ℕ} (he : e ∈ D.edges r)
    (hm : ¬ e.2 = e.1 + 1) : e ∈ D.chordEdges r := by
  rcases Finset.mem_union.1 he with h | h
  · rw [mem_memEdges] at h; exact absurd h.1 hm
  · exact h

/-- **Selection.** If every input is solved (at the profile capacities of `D`) by at least one of `K`
codes, the selection code solves complete exchange on **every** input, on the selection diagram, at
its per-node blocks plus `selBits K L` bits per memory edge. -/
theorem select_solves {k : ℕ} (D : TSDiagram k) {n G K P : ℕ} (hG : 1 ≤ G) (hn : 1 ≤ n)
    (hK : 1 ≤ K) (hD : D.Valid (n * n * entryBits n))
    (hP : SelRoom D P (blockSize G n) (n * n * entryBits n)) (codes : ℕ → NetCode)
    (hcov : ∀ x, ∃ c < K, D.Solves n G (D.profileCap n G) {x} (codes c)) :
    (selDiagram D K P (blockSize G n) (n * n * entryBits n)).Solves n G
      ((selDiagram D K P (blockSize G n) (n * n * entryBits n)).blockCap n G
        (fun y => ∑ t, (pairRes (blockSize G n)
          ((selDiagram D K P (blockSize G n) (n * n * entryBits n)).work t)
          (selDiagram D K P (blockSize G n) (n * n * entryBits n)).T y).card)
        (selBits K (n * n * entryBits n)))
      Set.univ (selCode D n G K P codes) := by
  intro x _
  have hr : 1 ≤ blockSize G n := one_le_blockSize hG hn
  have hPN := selRoom_nodes hr hP
  have hL1 : 1 ≤ n * n * entryBits n :=
    Nat.one_le_iff_ne_zero.2 (by unfold entryBits; positivity)
  have hT : 1 ≤ D.T := one_le_T hD hL1
  refine ⟨fun e he => ?_, fun d hd => ?_⟩
  · -- capacities
    have hlt := edges_fst_lt _ e he
    have hEl := edges_lt _ e he
    rw [nodes_sel D hr] at hEl
    simp only [NetCode.edgeVal]
    by_cases h1 : e.1 < D.nodes (blockSize G n)
    · by_cases hE : e ∈ D.edges (blockSize G n)
      · rw [selCode_run1_D D n G K P codes e _ _ h1 hE]
        have hpack : valRun1 D n G K codes e
            ((selCode D n G K P codes).inVals
              ((selDiagram D K P (blockSize G n) (n * n * entryBits n)).edges (blockSize G n))
              (fun y => (selDiagram D K P (blockSize G n) (n * n * entryBits n)).visible n
                (entryBits n) (blockSize G n) y x) e.1)
            ((selDiagram D K P (blockSize G n) (n * n * entryBits n)).visible n
              (entryBits n) (blockSize G n) e.1 x) < 2 ^ (K * D.profileCap n G e) :=
          packK_lt (fun a _ => clamp_lt D n G _ _ _ _)
        by_cases hm : e.2 = e.1 + 1
        · rw [ite_eq_left hm]
          have hmD := mem_memEdges_of_edges D hE hm
          rw [blockCap_mem _ (mem_memEdges_of_edges _ he hm)]
          have hcap : D.profileCap n G e =
              (∑ t, (pairRes (blockSize G n) (D.work t) D.T e.1).card) * (blockSize G n * G) := by
            unfold TSDiagram.profileCap; rw [blockCap_mem D hmD, Nat.add_zero]
          have hres := resSum_sel_run1 D (K := K) (P := P) (L := n * n * entryBits n) hr e.1
          have hs := encS_lt (stRun1 D n G K codes e.1
            ((selCode D n G K P codes).inVals
              ((selDiagram D K P (blockSize G n) (n * n * entryBits n)).edges (blockSize G n))
              (fun y => (selDiagram D K P (blockSize G n) (n * n * entryBits n)).visible n
                (entryBits n) (blockSize G n) y x) e.1)
            ((selDiagram D K P (blockSize G n) (n * n * entryBits n)).visible n
              (entryBits n) (blockSize G n) e.1 x))
          refine lt_of_lt_of_le (pack_state_lt hs hpack) (Nat.pow_le_pow_right (by norm_num) ?_)
          rw [hcap]
          have := Nat.mul_le_mul_right (blockSize G n * G) hres
          rw [Nat.mul_assoc] at this
          omega
        · rw [ite_eq_right hm]
          have hcD := mem_chordEdges_of_edges D hE hm
          rw [blockCap_chord _ (mem_chordEdges_sel_run1 D hr hK hcD)]
          have hcap : D.profileCap n G e = D.chordTapes (blockSize G n) e * (blockSize G n * G) := by
            unfold TSDiagram.profileCap; rw [blockCap_chord D hcD]
          have hct := chordTapes_sel_run1 D (K := K) (P := P) (L := n * n * entryBits n) hr hcD
          calc _ < 2 ^ (K * D.profileCap n G e) := hpack
            _ ≤ _ := by
                apply Nat.pow_le_pow_right (by norm_num)
                rw [hcap, ← Nat.mul_assoc]
                exact Nat.mul_le_mul_right _ hct
      · rw [selCode_run1_notD D n G K P codes e _ _ h1 hE]
        by_cases hm : e.2 = e.1 + 1
        · rw [ite_eq_left hm, blockCap_mem _ (mem_memEdges_of_edges _ he hm)]
          exact lt_of_lt_of_le (encS_lt _) (Nat.pow_le_pow_right (by norm_num) (by omega))
        · rw [ite_eq_right hm]; exact Nat.two_pow_pos _
    · by_cases h2 : e.1 < P
      · rw [selCode_epi D n G K P codes e _ _ h1 h2]
        by_cases hm : e.2 = e.1 + 1
        · rw [ite_eq_left hm, blockCap_mem _ (mem_memEdges_of_edges _ he hm)]
          exact lt_of_lt_of_le (encS_lt _) (Nat.pow_le_pow_right (by norm_num) (by omega))
        · rw [ite_eq_right hm]; exact Nat.two_pow_pos _
      · rw [selCode_run2 D n G K P codes e _ _ h1 h2]
        obtain ⟨a', b'⟩ := e
        simp only at h1 h2 hlt hEl ⊢
        obtain ⟨a'', rfl⟩ : ∃ a'', a' = P + a'' := ⟨a' - P, by omega⟩
        obtain ⟨b'', rfl⟩ : ∃ b'', b' = P + b'' := ⟨b' - P, by omega⟩
        have hED := (mem_edges_sel_add D (K := K) hr hD (by omega) a'' b'').1 he
        simp only [Nat.add_sub_cancel_left]
        rw [ite_eq_left hED]
        by_cases hm : b'' = a'' + 1
        · rw [ite_eq_left (show P + b'' = P + a'' + 1 by omega),
            blockCap_mem _ (mem_memEdges_of_edges _ he (by simp only; omega))]
          have hmD := mem_memEdges_of_edges D hED (by simp only; omega)
          have hcap : D.profileCap n G (a'', b'') =
              (∑ t, (pairRes (blockSize G n) (D.work t) D.T a'').card) * (blockSize G n * G) := by
            unfold TSDiagram.profileCap; rw [blockCap_mem D hmD, Nat.add_zero]
          have hres := resSum_sel_run2 D (K := K) (P := P) (r := blockSize G n) hD a''
          have hv := clamp_lt D n G (codes (winner (stIn n K (P + a'')
            ((selCode D n G K P codes).inVals
              ((selDiagram D K P (blockSize G n) (n * n * entryBits n)).edges (blockSize G n))
              (fun y => (selDiagram D K P (blockSize G n) (n * n * entryBits n)).visible n
                (entryBits n) (blockSize G n) y x) (P + a''))))) (a'', b'')
            (inRun2 D n G K P ((selCode D n G K P codes).inVals
              ((selDiagram D K P (blockSize G n) (n * n * entryBits n)).edges (blockSize G n))
              (fun y => (selDiagram D K P (blockSize G n) (n * n * entryBits n)).visible n
                (entryBits n) (blockSize G n) y x) (P + a'')))
            ((selDiagram D K P (blockSize G n) (n * n * entryBits n)).visible n
              (entryBits n) (blockSize G n) (P + a'') x)
          have hs := encS_lt (stIn n K (P + a'')
            ((selCode D n G K P codes).inVals
              ((selDiagram D K P (blockSize G n) (n * n * entryBits n)).edges (blockSize G n))
              (fun y => (selDiagram D K P (blockSize G n) (n * n * entryBits n)).visible n
                (entryBits n) (blockSize G n) y x) (P + a'')))
          refine lt_of_lt_of_le (pack_state_lt hs hv) (Nat.pow_le_pow_right (by norm_num) ?_)
          rw [hcap]
          exact Nat.add_le_add_right (Nat.mul_le_mul_right _ hres) _
        · rw [ite_eq_right (show ¬ P + b'' = P + a'' + 1 by omega)]
          have hcD := mem_chordEdges_of_edges D hED (by simp only; omega)
          rw [blockCap_chord _ (mem_chordEdges_of_edges _ he (by simp only; omega))]
          have hcap : D.profileCap n G (a'', b'') =
              D.chordTapes (blockSize G n) (a'', b'') * (blockSize G n * G) := by
            unfold TSDiagram.profileCap; rw [blockCap_chord D hcD]
          have hct := chordTapes_sel_run2 D (K := K) (P := P) (L := n * n * entryBits n) hr hD
            a'' b''
          calc _ < 2 ^ D.profileCap n G (a'', b'') := clamp_lt D n G _ _ _ _
            _ ≤ _ := by
                apply Nat.pow_le_pow_right (by norm_num)
                rw [hcap]
                exact Nat.mul_le_mul_right _ hct
  · -- outputs
    have ho := tpos_lt hd
    have hu' := outNode_lt hD hr hL1 (tpos n (entryBits n) d)
    obtain ⟨hS, hI⟩ := sel_run2 D codes x hG hn hK hD hP
      (D.outNode (blockSize G n) (tpos n (entryBits n) d)) hu'
    show (selCode D n G K P codes).dec _ _ _ = _
    rw [outNode_sel D hr hD hT]
    show (codes (winner (stIn n K (P + D.outNode (blockSize G n) (tpos n (entryBits n) d)) _))).dec
      _ (inRun2 D n G K P _) _ = _
    unfold stIn
    rw [hS, decS_encS, hI]
    beta_reduce
    rw [visible_sel_add D hr hP]
    have hw := winner_correct D codes x hG hn hD hP (hcov x) (tpos n (entryBits n) d) ho
    unfold outD NetCode.outVal at hw
    rw [show (⟨tpos n (entryBits n) (tpos n (entryBits n) d), tpos_lt ho⟩ :
      Fin (n * n * entryBits n)) = ⟨d, hd⟩ from Fin.ext (tpos_tpos hd)] at hw
    exact hw

/-! ### Plain ⟹ no code with a constant-size oracle hint -/

/-- The selection diagram keeps linear time, with room for the epilogue. -/
theorem sel_room_time {k : ℕ} (D : TSDiagram k) {n G c : ℕ} (hG : 1 ≤ G) (hn : 1 ≤ n)
    (hT : D.T ≤ c * (n * n * entryBits n)) :
    SelRoom D ((2 * c + 2) * n * G + 4) (blockSize G n) (n * n * entryBits n) ∧
    ((2 * c + 2) * n * G + 4) * blockSize G n + D.T ≤
      ((2 * c + 2) * G + c + 4) * (n * n * entryBits n) := by
  have hr : 1 ≤ blockSize G n := one_le_blockSize hG hn
  have hrnw : blockSize G n ≤ n * entryBits n := blockSize_le hG
  have hrG : n * entryBits n ≤ blockSize G n * G := blockSize_mul_ge hG
  have hN : D.nodes (blockSize G n) * blockSize G n ≤ D.T + blockSize G n := by
    have := nodes_mul_le (D := D) (blockSize G n); omega
  have hL : n * n * entryBits n = n * (n * entryBits n) := by ring
  have hLr : n * n * entryBits n ≤ n * (blockSize G n * G) := by
    rw [hL]; exact Nat.mul_le_mul_left _ hrG
  have hnr : n * blockSize G n ≤ n * n * entryBits n := by
    rw [hL]; exact Nat.mul_le_mul_left _ hrnw
  have hrL : blockSize G n ≤ n * n * entryBits n := by
    calc blockSize G n ≤ n * entryBits n := hrnw
      _ ≤ n * (n * entryBits n) := Nat.le_mul_of_pos_left _ (by omega)
      _ = n * n * entryBits n := by ring
  constructor
  · unfold SelRoom
    have e : ((2 * c + 2) * n * G + 4) * blockSize G n =
        (2 * c + 2) * (n * (blockSize G n * G)) + 4 * blockSize G n := by ring
    rw [e]
    have := Nat.mul_le_mul_left (2 * c + 2) hLr
    have h2 : 2 * (D.nodes (blockSize G n) * blockSize G n) ≤
        2 * (c * (n * n * entryBits n)) + 2 * blockSize G n := by omega
    nlinarith
  · have e : ((2 * c + 2) * n * G + 4) * blockSize G n =
        (2 * c + 2) * G * (n * blockSize G n) + 4 * blockSize G n := by ring
    rw [e]
    have h1 := Nat.mul_le_mul_left ((2 * c + 2) * G) hnr
    have e2 : ((2 * c + 2) * G + c + 4) * (n * n * entryBits n) =
        (2 * c + 2) * G * (n * n * entryBits n) + c * (n * n * entryBits n) +
          4 * (n * n * entryBits n) := by ring
    rw [e2]
    omega

/-- **Plain ⟹ no code with an `O(1)`-bit oracle hint.** Under `NoCode_TM`, for every constant
`s₀`, no family of codes indexed by an `s₀`-bit oracle hint (any function of the whole input)
solves complete exchange on every input at the profile capacities, for all large `n`. -/
theorem noCode_hintConst_of_noCode (h : NoCode_TM) (s₀ : ℕ) :
    NoCode_TM_hintBits (fun _ => s₀) := by
  intro k G c hG
  have hK : 1 ≤ 2 ^ s₀ := Nat.one_le_two_pow
  obtain ⟨n₀, hn₀⟩ := h ((2 ^ s₀ + 1) * k + 6 * (2 ^ s₀) ^ 2) G ((2 * c + 2) * G + c + 4) hG
  refine ⟨max n₀ 1, fun n hn D hD hT hint codes hhint hall => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hr : 1 ≤ blockSize G n := one_le_blockSize hG hn1
  have hrG : n * entryBits n ≤ blockSize G n * G := blockSize_mul_ge hG
  obtain ⟨hroom, htime⟩ := sel_room_time D hG hn1 hT
  have hsol := select_solves D hG hn1 hK hD hroom codes
    (fun x => ⟨hint x, hhint x, hall x⟩)
  have hs : selBits (2 ^ s₀) (n * n * entryBits n) ≤
      6 * (2 ^ s₀) ^ 2 * (blockSize G n * G) := by
    have h1 := selBits_le (2 ^ s₀) n
    have h2 : entryBits n ≤ blockSize G n * G :=
      le_trans (Nat.le_mul_of_pos_left _ (by omega)) hrG
    exact le_trans h1 (Nat.mul_le_mul_left _ h2)
  have hsol' := solves_profileCap_addTapes (a := 6 * (2 ^ s₀) ^ 2) hr hs hsol
  refine hn₀ n (le_trans (le_max_left _ _) hn) _
    (valid_addTapes _ (valid_sel D hD hr hroom) _) ?_ _ hsol'
  rw [T_addTapes]
  exact htime

/-- **Plain ⟹ no code on any set covered by an additive hint and `K` candidate shifts.** Under
`NoCode_TM`: for all constants and all large `n`, no code solves complete exchange at the profile
capacities on a set `F` for which a row-additive hint of `s ≤ C n w` bits and `K` shift tables put
every input into `F` with at least one of the `K` shifts. The prefix sweep computes the hint, the
`K` shifted codes are the candidates, and selection picks a correct one. -/
theorem noCode_additiveCover_of_noCode (h : NoCode_TM) (k G c C K : ℕ) (hG : 1 ≤ G) (hK : 1 ≤ K) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
      ∀ (F : Set (Fin (n * n * entryBits n) → Bool)) (s : ℕ), s ≤ C * (n * entryBits n) →
      ∀ (g : ℕ → (ℕ → Bool) → (Fin s → ZMod 2))
        (z : ℕ → (Fin s → ZMod 2) → (Fin (n * n * entryBits n) → Bool)),
        (∀ x, ∃ j < K, xorVec x (z j (rowSum n (entryBits n) g x)) ∈ F) →
      ∀ code : NetCode, ¬ D.Solves n G (D.profileCap n G) F code := by
  obtain ⟨n₀, hn₀⟩ := h ((K + 1) * (k + C) + 6 * K ^ 2) G
    ((2 * (c + 2 * G) + 2) * G + (c + 2 * G) + 4) hG
  refine ⟨max n₀ 1, fun n hn D hD hT F s hs g z hz code hsol => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hr : 1 ≤ blockSize G n := one_le_blockSize hG hn1
  have hrnw : blockSize G n ≤ n * entryBits n := blockSize_le hG
  have hrG : n * entryBits n ≤ blockSize G n * G := blockSize_mul_ge hG
  set P := 2 * n * G with hPdef
  have hP : 2 * (n * n * entryBits n) ≤ P * blockSize G n := by
    calc 2 * (n * n * entryBits n) = 2 * n * (n * entryBits n) := by ring
      _ ≤ 2 * n * (blockSize G n * G) := Nat.mul_le_mul_left _ hrG
      _ = P * blockSize G n := by rw [hPdef]; ring
  have hP1 : 1 ≤ P := by rw [hPdef]; have := Nat.mul_le_mul hn1 hG; nlinarith
  have hsB : s ≤ C * (blockSize G n * G) := le_trans hs (Nat.mul_le_mul_left _ hrG)
  -- the candidates: the prefix codes of the `K` shift tables, with `C` stationary tapes
  have hcov : ∀ x, ∃ j < K,
      (addTapes (prefixDiagram D P (blockSize G n) (n * n * entryBits n)) C).Solves n G
        ((addTapes (prefixDiagram D P (blockSize G n) (n * n * entryBits n)) C).profileCap n G) {x}
        (prefixCode D n (entryBits n) (blockSize G n) P s g code (z j)) := by
    intro x
    obtain ⟨j, hj, hjx⟩ := hz x
    exact ⟨j, hj, solves_profileCap_addTapes (a := C) hr hsB
      (prefix_solves_at D hG hn1 hD hP hP1 g (z j) hsol x hjx)⟩
  have hD₂ := valid_addTapes _ (valid_prefix D hD hP) C
  have hT₂ : (addTapes (prefixDiagram D P (blockSize G n) (n * n * entryBits n)) C).T ≤
      (c + 2 * G) * (n * n * entryBits n) := by
    rw [T_addTapes]
    show P * blockSize G n + D.T ≤ (c + 2 * G) * (n * n * entryBits n)
    have h1 : P * blockSize G n ≤ 2 * G * (n * n * entryBits n) := by
      calc P * blockSize G n ≤ P * (n * entryBits n) := Nat.mul_le_mul_left _ hrnw
        _ = 2 * G * (n * n * entryBits n) := by rw [hPdef]; ring
    have h2 : (c + 2 * G) * (n * n * entryBits n) =
        c * (n * n * entryBits n) + 2 * G * (n * n * entryBits n) := by ring
    omega
  obtain ⟨hroom, htime⟩ := sel_room_time _ hG hn1 hT₂
  have hsel := select_solves _ hG hn1 hK hD₂ hroom
    (fun j => prefixCode D n (entryBits n) (blockSize G n) P s g code (z j)) hcov
  have hs' : selBits K (n * n * entryBits n) ≤ 6 * K ^ 2 * (blockSize G n * G) := by
    have h2 : entryBits n ≤ blockSize G n * G :=
      le_trans (Nat.le_mul_of_pos_left _ (by omega)) hrG
    exact le_trans (selBits_le K n) (Nat.mul_le_mul_left _ h2)
  have hsel' := solves_profileCap_addTapes (a := 6 * K ^ 2) hr hs' hsel
  refine hn₀ n (le_trans (le_max_left _ _) hn) _
    (valid_addTapes _ (valid_sel _ hD₂ hr hroom) _) ?_ _ hsel'
  rw [T_addTapes]
  exact htime

/-- A constant-hint "no code" target implies the plain one (take the hint `0`). -/
theorem noCode_of_hintConst (s₀ : ℕ) (h : NoCode_TM_hintBits (fun _ => s₀)) : NoCode_TM := by
  intro k G c hG
  obtain ⟨n₀, hn₀⟩ := h k G c hG
  refine ⟨n₀, fun n hn D hD hT code hsol => ?_⟩
  exact hn₀ n hn D hD hT (fun _ => 0) (fun _ => code) (fun _ => Nat.two_pow_pos _)
    (fun x => (solves_iff_forall_singleton D).1 hsol x (Set.mem_univ x))

/-- **"No code" with a constant-size oracle hint is the plain target.** -/
theorem noCode_iff_hintConst (s₀ : ℕ) : NoCode_TM ↔ NoCode_TM_hintBits (fun _ => s₀) :=
  ⟨fun h => noCode_hintConst_of_noCode h s₀, noCode_of_hintConst s₀⟩

end Transpose.Tape.Impl
