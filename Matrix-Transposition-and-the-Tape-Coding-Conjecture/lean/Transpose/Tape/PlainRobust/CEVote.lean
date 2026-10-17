import Transpose.Tape.PlainRobust.CEPrefix

/-!
# Voting: plain ⟹ no code that fails on few inputs

* `tripleTapes D`: every work walk of `D` three times. The block network is unchanged and every
  capacity at the per-node profile triples (`profileCap_triple`).
* `triCode`: three codes run side by side, their edge values packed in base `2^c`, each clamped to
  its capacity; every output bit is the majority of the three decoded bits.
* `vote_solves`: if a code is correct on every input outside a set `E` with `2 |E|² < 2^L`, three
  shifted copies (shifts `0, z₁, z₂` with `z_i ⊕ z_j ∉ E ⊕ E`) give a code correct on **every** input.
* `noCode_cosmall_of_noCode`: hence `NoCode_TM` rules out every code that fails on fewer than about
  `2^{L/2}` inputs.
-/

namespace Transpose.Tape.Impl

open Transpose TSDiagram

/-! ### Tripled walks -/

/-- Every work walk three times. -/
def tripleTapes {k : ℕ} (D : TSDiagram k) : TSDiagram (3 * k) where
  T := D.T
  work := fun t => D.work (finProdFinEquiv.symm t).2
  inp := D.inp
  out := D.out

section Triple

variable {k : ℕ} (D : TSDiagram k)

theorem valid_triple {L : ℕ} (hD : D.Valid L) : (tripleTapes D).Valid L :=
  ⟨fun _ => hD.1 _, hD.2⟩

theorem nodes_triple (r : ℕ) : (tripleTapes D).nodes r = D.nodes r := rfl

theorem memEdges_triple (r : ℕ) : (tripleTapes D).memEdges r = D.memEdges r := rfl

theorem rowsAt_triple (n w r y : ℕ) : (tripleTapes D).rowsAt n w r y = D.rowsAt n w r y := rfl

theorem outNode_triple (r o : ℕ) : (tripleTapes D).outNode r o = D.outNode r o := rfl

theorem visible_triple (n w r y : ℕ) {L : ℕ} (x : Fin L → Bool) :
    (tripleTapes D).visible n w r y x = D.visible n w r y x := rfl

theorem chordEdges_triple (r : ℕ) : (tripleTapes D).chordEdges r = D.chordEdges r := by
  classical
  ext e
  rw [mem_chordEdges, mem_chordEdges]
  constructor
  · rintro ⟨h1, h2, t, β, hc⟩
    exact ⟨h1, h2, (finProdFinEquiv.symm t).2, β, hc⟩
  · rintro ⟨h1, h2, t, β, hc⟩
    refine ⟨h1, h2, finProdFinEquiv (0, t), β, ?_⟩
    show IsChord (pairRes r (D.work (finProdFinEquiv.symm (finProdFinEquiv (0, t))).2) D.T) β e.1 e.2
    rw [Equiv.symm_apply_apply]
    exact hc

theorem edges_triple (r : ℕ) : (tripleTapes D).edges r = D.edges r := by
  unfold TSDiagram.edges
  rw [memEdges_triple, chordEdges_triple]

/-- Sums over the tripled tapes are three times the sums over the tapes. -/
theorem sum_triple (f : Fin k → ℕ) :
    ∑ t : Fin (3 * k), f (finProdFinEquiv.symm t).2 = 3 * ∑ t, f t := by
  rw [← Equiv.sum_comp finProdFinEquiv]
  simp only [Equiv.symm_apply_apply]
  rw [Fintype.sum_prod_type]
  simp

theorem chordTapes_triple (r : ℕ) (e : ℕ × ℕ) :
    (tripleTapes D).chordTapes r e = 3 * D.chordTapes r e := by
  classical
  unfold TSDiagram.chordTapes
  rw [Finset.card_filter, Finset.card_filter]
  exact sum_triple (k := k) (fun t => if ∃ β : ℤ, IsChord (pairRes r (D.work t) D.T) β e.1 e.2
    then 1 else 0)

theorem resSum_triple (r y : ℕ) :
    ∑ t, (pairRes r ((tripleTapes D).work t) (tripleTapes D).T y).card =
      3 * ∑ t, (pairRes r (D.work t) D.T y).card :=
  sum_triple (k := k) (fun t => (pairRes r (D.work t) D.T y).card)

/-- **Tripling the walks triples every capacity of the profile.** -/
theorem profileCap_triple (n G : ℕ) (e : ℕ × ℕ) :
    (tripleTapes D).profileCap n G e = 3 * D.profileCap n G e := by
  unfold TSDiagram.profileCap TSDiagram.blockCap
  beta_reduce
  rw [memEdges_triple, chordEdges_triple, resSum_triple, chordTapes_triple]
  split_ifs <;> ring

end Triple

/-! ### Three codes side by side -/

section Tri

variable {k : ℕ} (D : TSDiagram k) (n G : ℕ)

/-- A code with every edge value clamped below its capacity at the profile of `D`. -/
noncomputable def clampCode (C : NetCode) : NetCode where
  enc e f v := if C.enc e f v < 2 ^ D.profileCap n G e then C.enc e f v else 0
  dec := C.dec

/-- Digit `j` (base `2^c`, `c` the capacity of `e`) of a packed value on edge `e`. -/
noncomputable def digit (j : ℕ) (e : ℕ × ℕ) (m : ℕ) : ℕ :=
  m / 2 ^ (j * D.profileCap n G e) % 2 ^ D.profileCap n G e

/-- The majority of three bits. -/
def maj3 (a b c : Bool) : Bool := (a && b) || (b && c) || (a && c)

/-- **Three codes side by side**: the clamped values are packed in base `2^c`, and every output bit is
the majority of the three decoded bits. -/
noncomputable def triCode (C₀ C₁ C₂ : NetCode) : NetCode where
  enc e f v :=
    (clampCode D n G C₀).enc e (fun e' => digit D n G 0 e' (f e')) v +
    2 ^ D.profileCap n G e * (clampCode D n G C₁).enc e (fun e' => digit D n G 1 e' (f e')) v +
    2 ^ (2 * D.profileCap n G e) * (clampCode D n G C₂).enc e (fun e' => digit D n G 2 e' (f e')) v
  dec o f v := maj3 (C₀.dec o (fun e' => digit D n G 0 e' (f e')) v)
    (C₁.dec o (fun e' => digit D n G 1 e' (f e')) v) (C₂.dec o (fun e' => digit D n G 2 e' (f e')) v)

theorem clamp_lt (C : NetCode) (e : ℕ × ℕ) (f : ℕ × ℕ → ℕ) (v : ℕ → Bool) :
    (clampCode D n G C).enc e f v < 2 ^ D.profileCap n G e := by
  show (if C.enc e f v < 2 ^ D.profileCap n G e then C.enc e f v else 0) < _
  split_ifs with h
  · exact h
  · exact Nat.two_pow_pos _

theorem pack3_lt {p a b c : ℕ} (ha : a < 2 ^ p) (hb : b < 2 ^ p) (hc : c < 2 ^ p) :
    a + 2 ^ p * b + 2 ^ (2 * p) * c < 2 ^ (3 * p) := by
  have e2 : 2 ^ (2 * p) = 2 ^ p * 2 ^ p := by rw [two_mul, pow_add]
  have e3 : 2 ^ (3 * p) = 2 ^ p * 2 ^ p * 2 ^ p := by
    rw [show 3 * p = p + p + p by ring, pow_add, pow_add]
  rw [e2, e3]
  have h1 : b ≤ 2 ^ p - 1 := by omega
  have h2 : c ≤ 2 ^ p - 1 := by omega
  have hp : 1 ≤ 2 ^ p := Nat.one_le_two_pow
  nlinarith [Nat.mul_le_mul_left (2 ^ p) h1, Nat.mul_le_mul_left (2 ^ p * 2 ^ p) h2]

theorem digit0_pack {p a b c : ℕ} (ha : a < 2 ^ p) :
    (a + 2 ^ p * b + 2 ^ (2 * p) * c) / 2 ^ (0 * p) % 2 ^ p = a := by
  rw [Nat.zero_mul, pow_zero, Nat.div_one]
  have e : a + 2 ^ p * b + 2 ^ (2 * p) * c = a + 2 ^ p * (b + 2 ^ p * c) := by
    rw [two_mul, pow_add]; ring
  rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]

theorem digit1_pack {p a b c : ℕ} (ha : a < 2 ^ p) (hb : b < 2 ^ p) :
    (a + 2 ^ p * b + 2 ^ (2 * p) * c) / 2 ^ (1 * p) % 2 ^ p = b := by
  rw [Nat.one_mul]
  have e : a + 2 ^ p * b + 2 ^ (2 * p) * c = a + 2 ^ p * (b + 2 ^ p * c) := by
    rw [two_mul, pow_add]; ring
  rw [e, Nat.add_mul_div_left _ _ (Nat.two_pow_pos p), Nat.div_eq_of_lt ha, Nat.zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]

theorem digit2_pack {p a b c : ℕ} (ha : a < 2 ^ p) (hb : b < 2 ^ p) (hc : c < 2 ^ p) :
    (a + 2 ^ p * b + 2 ^ (2 * p) * c) / 2 ^ (2 * p) % 2 ^ p = c := by
  have hab : a + 2 ^ p * b < 2 ^ (2 * p) := by
    rw [two_mul, pow_add]
    have : b ≤ 2 ^ p - 1 := by omega
    have hp : 1 ≤ 2 ^ p := Nat.one_le_two_pow
    nlinarith [Nat.mul_le_mul_left (2 ^ p) this]
  rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hab, Nat.zero_add,
    Nat.mod_eq_of_lt hc]

/-- **Each digit carries its own code**: the digits of the side-by-side code's values into a node are
the values of the three clamped codes. -/
theorem triCode_digits (C₀ C₁ C₂ : NetCode) (E : Finset (ℕ × ℕ)) (vis : ℕ → ℕ → Bool) :
    ∀ u, (fun e' => digit D n G 0 e' ((triCode D n G C₀ C₁ C₂).inVals E vis u e')) =
        (clampCode D n G C₀).inVals E vis u ∧
      (fun e' => digit D n G 1 e' ((triCode D n G C₀ C₁ C₂).inVals E vis u e')) =
        (clampCode D n G C₁).inVals E vis u ∧
      (fun e' => digit D n G 2 e' ((triCode D n G C₀ C₁ C₂).inVals E vis u e')) =
        (clampCode D n G C₂).inVals E vis u := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
  have key : ∀ e' : ℕ × ℕ, e' ∈ E ∧ e'.2 = u ∧ e'.1 < u →
      (triCode D n G C₀ C₁ C₂).inVals E vis u e' =
        (clampCode D n G C₀).inVals E vis u e' +
        2 ^ D.profileCap n G e' * (clampCode D n G C₁).inVals E vis u e' +
        2 ^ (2 * D.profileCap n G e') * (clampCode D n G C₂).inVals E vis u e' := by
    intro e' hc
    rw [inVals_eq, inVals_eq, inVals_eq, inVals_eq, ite_eq_left hc, ite_eq_left hc, ite_eq_left hc,
      ite_eq_left hc]
    obtain ⟨h0, h1, h2⟩ := ih e'.1 hc.2.2
    show (clampCode D n G C₀).enc e' (fun e'' => digit D n G 0 e''
        ((triCode D n G C₀ C₁ C₂).inVals E vis e'.1 e'')) (vis e'.1) + _ + _ = _
    rw [h0, h1, h2]
  refine ⟨?_, ?_, ?_⟩ <;> funext e' <;>
    by_cases hc : e' ∈ E ∧ e'.2 = u ∧ e'.1 < u
  · rw [key e' hc]
    unfold digit
    exact digit0_pack (by rw [inVals_eq, ite_eq_left hc]; exact clamp_lt D n G _ _ _ _)
  · simp only [digit]
    rw [inVals_eq, ite_eq_right hc, inVals_eq, ite_eq_right hc]
    simp
  · rw [key e' hc]
    unfold digit
    exact digit1_pack (by rw [inVals_eq, ite_eq_left hc]; exact clamp_lt D n G _ _ _ _)
      (by rw [inVals_eq, ite_eq_left hc]; exact clamp_lt D n G _ _ _ _)
  · simp only [digit]
    rw [inVals_eq, ite_eq_right hc, inVals_eq, ite_eq_right hc]
    simp
  · rw [key e' hc]
    unfold digit
    exact digit2_pack (by rw [inVals_eq, ite_eq_left hc]; exact clamp_lt D n G _ _ _ _)
      (by rw [inVals_eq, ite_eq_left hc]; exact clamp_lt D n G _ _ _ _)
      (by rw [inVals_eq, ite_eq_left hc]; exact clamp_lt D n G _ _ _ _)
  · simp only [digit]
    rw [inVals_eq, ite_eq_right hc, inVals_eq, ite_eq_right hc]
    simp

/-- A code within its capacities on an input is unchanged by clamping, on that input. -/
theorem clamp_inVals (C : NetCode) (E : Finset (ℕ × ℕ)) (vis : ℕ → ℕ → Bool)
    (hcap : ∀ e ∈ E, C.edgeVal E vis e < 2 ^ D.profileCap n G e) :
    ∀ u, (clampCode D n G C).inVals E vis u = C.inVals E vis u := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
  funext e'
  rw [inVals_eq, inVals_eq]
  by_cases hc : e' ∈ E ∧ e'.2 = u ∧ e'.1 < u
  · rw [ite_eq_left hc, ite_eq_left hc]
    show (if C.enc e' _ (vis e'.1) < 2 ^ D.profileCap n G e' then C.enc e' _ (vis e'.1) else 0) = _
    rw [ih e'.1 hc.2.2]
    have := hcap e' hc.1
    simp only [NetCode.edgeVal] at this
    rw [ite_eq_left this]
  · rw [ite_eq_right hc, ite_eq_right hc]

/-- The side-by-side code stays within three times the capacities. -/
theorem triCode_edgeVal_lt (C₀ C₁ C₂ : NetCode) (E : Finset (ℕ × ℕ)) (vis : ℕ → ℕ → Bool)
    (e : ℕ × ℕ) : (triCode D n G C₀ C₁ C₂).edgeVal E vis e < 2 ^ (3 * D.profileCap n G e) :=
  pack3_lt (clamp_lt D n G _ _ _ _) (clamp_lt D n G _ _ _ _) (clamp_lt D n G _ _ _ _)

theorem maj3_of_two {a b c t : Bool} (h : (a = t ∧ b = t) ∨ (b = t ∧ c = t) ∨ (a = t ∧ c = t)) :
    maj3 a b c = t := by
  revert h
  cases a <;> cases b <;> cases c <;> cases t <;> decide

/-- **Voting.** If shifts `z₀, z₁, z₂` put every input into `F` for at least two of them, the three
shifted copies of a code solving complete exchange on `F` give a code on every input, on the diagram
with tripled walks. -/
theorem vote_solves_on {F Y : Set (Fin (n * n * entryBits n) → Bool)} {C : NetCode}
    (hsol : D.Solves n G (D.profileCap n G) F C) (z₀ z₁ z₂ : Fin (n * n * entryBits n) → Bool)
    (hz : ∀ x ∈ Y, (xorVec x z₀ ∈ F ∧ xorVec x z₁ ∈ F) ∨ (xorVec x z₁ ∈ F ∧ xorVec x z₂ ∈ F) ∨
      (xorVec x z₀ ∈ F ∧ xorVec x z₂ ∈ F)) :
    (tripleTapes D).Solves n G ((tripleTapes D).profileCap n G) Y
      (triCode D n G (shiftCode D n (entryBits n) (blockSize G n) C z₀)
        (shiftCode D n (entryBits n) (blockSize G n) C z₁)
        (shiftCode D n (entryBits n) (blockSize G n) C z₂)) := by
  intro x hxY
  set E := D.edges (blockSize G n)
  set vis := fun y => D.visible n (entryBits n) (blockSize G n) y x
  have hE : (tripleTapes D).edges (blockSize G n) = E := edges_triple D _
  have hvis : (fun y => (tripleTapes D).visible n (entryBits n) (blockSize G n) y x) = vis := rfl
  rw [hE, hvis]
  -- each shifted copy, on the inputs it handles
  have good : ∀ z, xorVec x z ∈ F →
      (∀ e ∈ E, (shiftCode D n (entryBits n) (blockSize G n) C z).edgeVal E vis e <
        2 ^ D.profileCap n G e) ∧
      ∀ (d : ℕ) (hd : d < n * n * entryBits n),
        (shiftCode D n (entryBits n) (blockSize G n) C z).outVal E vis
          (D.outNode (blockSize G n) (tpos n (entryBits n) d)) (tpos n (entryBits n) d) = x ⟨d, hd⟩ :=
    fun z hzx => solves_shiftCode D hsol z x hzx
  refine ⟨fun e _ => ?_, fun d hd => ?_⟩
  · rw [profileCap_triple]
    exact triCode_edgeVal_lt D n G _ _ _ E vis e
  · -- the decoded bit of each copy at the sink
    have hdig := triCode_digits D n G (shiftCode D n (entryBits n) (blockSize G n) C z₀)
      (shiftCode D n (entryBits n) (blockSize G n) C z₁)
      (shiftCode D n (entryBits n) (blockSize G n) C z₂) E vis
      (D.outNode (blockSize G n) (tpos n (entryBits n) d))
    obtain ⟨h0, h1, h2⟩ := hdig
    show maj3 _ _ _ = _
    rw [outNode_triple, h0, h1, h2]
    have copy : ∀ z, xorVec x z ∈ F →
        (shiftCode D n (entryBits n) (blockSize G n) C z).dec (tpos n (entryBits n) d)
          ((clampCode D n G (shiftCode D n (entryBits n) (blockSize G n) C z)).inVals E vis
            (D.outNode (blockSize G n) (tpos n (entryBits n) d)))
          (vis (D.outNode (blockSize G n) (tpos n (entryBits n) d))) = x ⟨d, hd⟩ := by
      intro z hzx
      obtain ⟨hc, ho⟩ := good z hzx
      rw [clamp_inVals D n G _ E vis hc]
      exact ho d hd
    apply maj3_of_two
    rcases hz x hxY with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact Or.inl ⟨copy z₀ ha, copy z₁ hb⟩
    · exact Or.inr (Or.inl ⟨copy z₁ ha, copy z₂ hb⟩)
    · exact Or.inr (Or.inr ⟨copy z₀ ha, copy z₂ hb⟩)

theorem vote_solves {F : Set (Fin (n * n * entryBits n) → Bool)} {C : NetCode}
    (hsol : D.Solves n G (D.profileCap n G) F C) (z₀ z₁ z₂ : Fin (n * n * entryBits n) → Bool)
    (hz : ∀ x, (xorVec x z₀ ∈ F ∧ xorVec x z₁ ∈ F) ∨ (xorVec x z₁ ∈ F ∧ xorVec x z₂ ∈ F) ∨
      (xorVec x z₀ ∈ F ∧ xorVec x z₂ ∈ F)) :
    (tripleTapes D).Solves n G ((tripleTapes D).profileCap n G) Set.univ
      (triCode D n G (shiftCode D n (entryBits n) (blockSize G n) C z₀)
        (shiftCode D n (entryBits n) (blockSize G n) C z₁)
        (shiftCode D n (entryBits n) (blockSize G n) C z₂)) :=
  vote_solves_on D n G hsol z₀ z₁ z₂ (fun x _ => hz x)

end Tri

/-! ### Choosing the shifts -/

theorem xorVec_cancel {L : ℕ} (x a b : Fin L → Bool) :
    xorVec (xorVec x a) (xorVec x b) = xorVec a b := by
  funext d; simp only [xorVec]; cases x d <;> cases a d <;> cases b d <;> rfl

theorem xorVec_zero {L : ℕ} (x : Fin L → Bool) : xorVec x (fun _ => false) = x := by
  funext d; simp [xorVec]

/-- **Three shifts with at most one bad.** If the complement `E` of `F` has `2 |E|² < 2^L`, some shifts
`0, z₁, z₂` put every input into `F` for at least two of them. -/
theorem exists_vote_shifts {L : ℕ} (F : Set (Fin L → Bool))
    (hE : 2 * (Fᶜ).ncard ^ 2 < 2 ^ L) :
    ∃ z₁ z₂ : Fin L → Bool, ∀ x,
      (xorVec x (fun _ => false) ∈ F ∧ xorVec x z₁ ∈ F) ∨ (xorVec x z₁ ∈ F ∧ xorVec x z₂ ∈ F) ∨
        (xorVec x (fun _ => false) ∈ F ∧ xorVec x z₂ ∈ F) := by
  classical
  set E : Finset (Fin L → Bool) := Finset.univ.filter (· ∉ F) with hEdef
  have hEcard : E.card = (Fᶜ).ncard := by
    rw [← Set.ncard_coe_finset]; congr 1; ext y; simp [hEdef]
  set S : Finset (Fin L → Bool) := (E ×ˢ E).image (fun p => xorVec p.1 p.2) with hSdef
  have hS : S.card ≤ E.card ^ 2 := by
    calc S.card ≤ (E ×ˢ E).card := Finset.card_image_le
      _ = E.card ^ 2 := by rw [Finset.card_product, sq]
  have huniv : (Finset.univ : Finset (Fin L → Bool)).card = 2 ^ L := by simp
  have hSL : 2 * S.card < 2 ^ L := by
    have : E.card ^ 2 = (Fᶜ).ncard ^ 2 := by rw [hEcard]
    omega
  -- `z₁ ∉ S`
  obtain ⟨z₁, -, hz₁⟩ : ∃ z ∈ (Finset.univ : Finset (Fin L → Bool)), z ∉ S := by
    apply Finset.exists_mem_notMem_of_card_lt_card
    rw [huniv]; omega
  -- `z₂ ∉ S ∪ (z₁ ⊕ S)`
  obtain ⟨z₂, -, hz₂⟩ : ∃ z ∈ (Finset.univ : Finset (Fin L → Bool)),
      z ∉ S ∪ S.image (fun y => xorVec z₁ y) := by
    apply Finset.exists_mem_notMem_of_card_lt_card
    rw [huniv]
    calc (S ∪ S.image (fun y => xorVec z₁ y)).card ≤ S.card + (S.image _).card :=
          Finset.card_union_le _ _
      _ ≤ S.card + S.card := Nat.add_le_add_left Finset.card_image_le _
      _ < 2 ^ L := by omega
  refine ⟨z₁, z₂, fun x => ?_⟩
  rw [xorVec_zero]
  -- two bad shifts would put their difference in `S`
  have bad2 : ∀ a b : Fin L → Bool, xorVec x a ∉ F → xorVec x b ∉ F → xorVec a b ∈ S := by
    intro a b ha hb
    rw [hSdef, Finset.mem_image]
    refine ⟨(xorVec x a, xorVec x b), ?_, xorVec_cancel x a b⟩
    simp [hEdef, ha, hb]
  have zero_xor : ∀ a : Fin L → Bool, xorVec (fun _ => false) a = a := by
    intro a; funext d; simp [xorVec]
  have bad12 : xorVec x z₁ ∉ F → xorVec x z₂ ∉ F → False := by
    intro h1 h2
    apply hz₂
    apply Finset.mem_union_right
    rw [Finset.mem_image]
    exact ⟨xorVec z₁ z₂, bad2 z₁ z₂ h1 h2,
      by funext d; simp only [xorVec]; cases z₁ d <;> cases z₂ d <;> rfl⟩
  by_cases h0 : x ∈ F
  · by_cases h1 : xorVec x z₁ ∈ F
    · exact Or.inl ⟨h0, h1⟩
    · by_cases h2 : xorVec x z₂ ∈ F
      · exact Or.inr (Or.inr ⟨h0, h2⟩)
      · exact absurd (bad12 h1 h2) id
  · have h0' : xorVec x (fun _ => false) ∉ F := by rw [xorVec_zero]; exact h0
    by_cases h1 : xorVec x z₁ ∈ F
    · by_cases h2 : xorVec x z₂ ∈ F
      · exact Or.inr (Or.inl ⟨h1, h2⟩)
      · exfalso
        have := bad2 (fun _ => false) z₂ h0' h2
        rw [zero_xor] at this
        exact hz₂ (Finset.mem_union_left _ this)
    · exfalso
      have := bad2 (fun _ => false) z₁ h0' h1
      rw [zero_xor] at this
      exact hz₁ this

/-! ### Affine sets with sparse exceptions -/

section AffineVote

variable {s : ℕ} {n w L : ℕ} (g : ℕ → (ℕ → Bool) → (Fin s → ZMod 2))

theorem rowSum_xorVec (hg : ∀ i (u v : ℕ → Bool), g i (fun d => xor (u d) (v d)) = g i u + g i v)
    (x y : Fin L → Bool) : rowSum n w g (xorVec x y) = rowSum n w g x + rowSum n w g y := by
  unfold rowSum
  rw [← Finset.sum_add_distrib]
  congr 1
  funext i
  rw [rowOf_xbits_xorVec, hg]

/-- **The kernel of the row sum has at least `2^L / 2^s` elements.** -/
theorem kernel_card (hg : ∀ i (u v : ℕ → Bool), g i (fun d => xor (u d) (v d)) = g i u + g i v) :
    2 ^ L ≤ 2 ^ s * ((Finset.univ : Finset (Fin L → Bool)).filter
      (fun z => rowSum n w g z = 0)).card := by
  classical
  set K := (Finset.univ : Finset (Fin L → Bool)).filter (fun z => rowSum n w g z = 0) with hK
  have hfib : ∀ b : Fin s → ZMod 2,
      ((Finset.univ : Finset (Fin L → Bool)).filter (fun x => rowSum n w g x = b)).card ≤ K.card := by
    intro b
    by_cases hne : ∃ x₀ : Fin L → Bool, rowSum n w g x₀ = b
    · obtain ⟨x₀, hx₀⟩ := hne
      apply Finset.card_le_card_of_injOn (fun x => xorVec x x₀)
      · intro x hx
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hx ⊢
        rw [hK, Finset.coe_filter]
        simp only [Finset.mem_univ, true_and, Set.mem_ofPred_eq]
        rw [rowSum_xorVec g hg, hx, hx₀]
        have h2 : (2 : ZMod 2) = 0 := rfl
        rw [← two_smul (ZMod 2) b, h2, zero_smul]
      · intro x _ y _ hxy
        have := congrArg (fun u => xorVec u x₀) hxy
        simp only at this
        funext d
        have := congrFun this d
        simp only [xorVec] at this
        cases hx : x d <;> cases hy : y d <;> cases x₀ d <;> simp_all
    · have : (Finset.univ : Finset (Fin L → Bool)).filter (fun x => rowSum n w g x = b) = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro x hx
        exact hne ⟨x, (Finset.mem_filter.1 hx).2⟩
      rw [this, Finset.card_empty]; exact Nat.zero_le _
  have hsum := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin L → Bool)))
    (t := (Finset.univ : Finset (Fin s → ZMod 2))) (f := rowSum n w g) (fun _ _ => Finset.mem_univ _)
  have huniv : (Finset.univ : Finset (Fin L → Bool)).card = 2 ^ L := by simp
  rw [huniv] at hsum
  rw [hsum]
  calc ∑ b ∈ (Finset.univ : Finset (Fin s → ZMod 2)),
        ((Finset.univ : Finset (Fin L → Bool)).filter (fun x => rowSum n w g x = b)).card
      ≤ ∑ _b ∈ (Finset.univ : Finset (Fin s → ZMod 2)), K.card := Finset.sum_le_sum (fun b _ => hfib b)
    _ = 2 ^ s * K.card := by
        rw [Finset.sum_const, smul_eq_mul, Finset.card_univ, card_vec2]

/-- **Three shifts from a set `Z` with at most one bad**, for a bad set `E` with `2 |E|² < |Z|`. -/
theorem exists_vote_shifts_in (E : Set (Fin L → Bool)) (Z : Finset (Fin L → Bool))
    (hE : 2 * E.ncard ^ 2 < Z.card) :
    ∃ z₁ ∈ Z, ∃ z₂ ∈ Z, ∀ x,
      (x ∉ E ∧ xorVec x z₁ ∉ E) ∨ (xorVec x z₁ ∉ E ∧ xorVec x z₂ ∉ E) ∨ (x ∉ E ∧ xorVec x z₂ ∉ E) := by
  classical
  set Ef : Finset (Fin L → Bool) := Finset.univ.filter (· ∈ E) with hEf
  have hEcard : Ef.card = E.ncard := by
    rw [← Set.ncard_coe_finset]; congr 1; ext y; simp [hEf]
  set S : Finset (Fin L → Bool) := (Ef ×ˢ Ef).image (fun p => xorVec p.1 p.2) with hSdef
  have hS : S.card ≤ Ef.card ^ 2 := by
    calc S.card ≤ (Ef ×ˢ Ef).card := Finset.card_image_le
      _ = Ef.card ^ 2 := by rw [Finset.card_product, sq]
  have hSZ : 2 * S.card < Z.card := by
    have : Ef.card ^ 2 = E.ncard ^ 2 := by rw [hEcard]
    omega
  obtain ⟨z₁, hz₁Z, hz₁⟩ : ∃ z ∈ Z, z ∉ S := Finset.exists_mem_notMem_of_card_lt_card (by omega)
  obtain ⟨z₂, hz₂Z, hz₂⟩ : ∃ z ∈ Z, z ∉ S ∪ S.image (fun y => xorVec z₁ y) := by
    apply Finset.exists_mem_notMem_of_card_lt_card
    calc (S ∪ S.image (fun y => xorVec z₁ y)).card ≤ S.card + (S.image _).card :=
          Finset.card_union_le _ _
      _ ≤ S.card + S.card := Nat.add_le_add_left Finset.card_image_le _
      _ < Z.card := by omega
  refine ⟨z₁, hz₁Z, z₂, hz₂Z, fun x => ?_⟩
  have bad2 : ∀ a b : Fin L → Bool, xorVec x a ∈ E → xorVec x b ∈ E → xorVec a b ∈ S := by
    intro a b ha hb
    rw [hSdef, Finset.mem_image]
    refine ⟨(xorVec x a, xorVec x b), ?_, xorVec_cancel x a b⟩
    simp [hEf, ha, hb]
  have zero_xor : ∀ a : Fin L → Bool, xorVec (fun _ => false) a = a := by
    intro a; funext d; simp [xorVec]
  have hx0 : ∀ y : Fin L → Bool, xorVec y (fun _ => false) = y := xorVec_zero
  by_cases h0 : x ∈ E
  · have h0' : xorVec x (fun _ => false) ∈ E := by rw [hx0]; exact h0
    by_cases h1 : xorVec x z₁ ∈ E
    · exfalso
      have := bad2 (fun _ => false) z₁ h0' h1
      rw [zero_xor] at this
      exact hz₁ this
    · by_cases h2 : xorVec x z₂ ∈ E
      · exfalso
        have := bad2 (fun _ => false) z₂ h0' h2
        rw [zero_xor] at this
        exact hz₂ (Finset.mem_union_left _ this)
      · exact Or.inr (Or.inl ⟨h1, h2⟩)
  · by_cases h1 : xorVec x z₁ ∈ E
    · by_cases h2 : xorVec x z₂ ∈ E
      · exfalso
        apply hz₂
        apply Finset.mem_union_right
        rw [Finset.mem_image]
        exact ⟨xorVec z₁ z₂, bad2 z₁ z₂ h1 h2,
          by funext d; simp only [xorVec]; cases z₁ d <;> cases z₂ d <;> rfl⟩
      · exact Or.inr (Or.inr ⟨h0, h2⟩)
    · exact Or.inl ⟨h0, h1⟩

end AffineVote

/-- **Plain ⟹ no code that fails on fewer than about `2^{L/2}` inputs.** Under `NoCode_TM`: for all
constants and all large `n`, no code solves complete exchange at the profile capacities on a set `F`
whose complement has `2 |F^c|² < 2^L`. (Three shifted copies on tripled walks, majority vote.) -/
theorem noCode_cosmall_of_noCode (h : NoCode_TM) (k G c : ℕ) (hG : 1 ≤ G) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
      ∀ (F : Set (Fin (n * n * entryBits n) → Bool)), 2 * (Fᶜ).ncard ^ 2 < 2 ^ (n * n * entryBits n) →
      ∀ code : NetCode, ¬ D.Solves n G (D.profileCap n G) F code := by
  obtain ⟨n₀, hn₀⟩ := h (3 * k) G c hG
  refine ⟨n₀, fun n hn D hD hT F hF code hsol => ?_⟩
  obtain ⟨z₁, z₂, hz⟩ := exists_vote_shifts F hF
  exact hn₀ n hn (tripleTapes D) (valid_triple D hD) hT _
    (vote_solves D n G hsol (fun _ => false) z₁ z₂ hz)

/-- **Plain ⟹ no code on an affine set with sparse exceptions.** Under `NoCode_TM`: for all constants
and all large `n`, no code solves complete exchange at the profile capacities on a set `F` that
contains a nonempty affine set `A = {x | Σ_i g_i(row i) = b}` of codimension `s ≤ C n w` except for a
set `E` of exceptions with `2^s · 2 |E|² < 2^L`. (Vote with three shifts in the kernel, which keeps
`A` fixed, to get a code on all of `A`; then `noCode_affine_of_noCode`.) -/
theorem noCode_affine_exc_of_noCode (h : NoCode_TM) (k G c C : ℕ) (hG : 1 ≤ G) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
      ∀ (F : Set (Fin (n * n * entryBits n) → Bool)) (s : ℕ), s ≤ C * (n * entryBits n) →
      ∀ (g : ℕ → (ℕ → Bool) → (Fin s → ZMod 2)),
        (∀ i (u v : ℕ → Bool), g i (fun d => xor (u d) (v d)) = g i u + g i v) →
      ∀ (b : Fin s → ZMod 2),
        (∃ x₀ : Fin (n * n * entryBits n) → Bool, rowSum n (entryBits n) g x₀ = b) →
      ∀ (E : Set (Fin (n * n * entryBits n) → Bool)),
        2 ^ s * (2 * E.ncard ^ 2) < 2 ^ (n * n * entryBits n) →
        {x | rowSum n (entryBits n) g x = b} \ E ⊆ F →
      ∀ code : NetCode, ¬ D.Solves n G (D.profileCap n G) F code := by
  classical
  obtain ⟨n₀, hn₀⟩ := noCode_affine_of_noCode h (3 * k) G c C hG
  refine ⟨n₀, fun n hn D hD hT F s hs g hg b hb E hE hsub code hsol => ?_⟩
  set K := (Finset.univ : Finset (Fin (n * n * entryBits n) → Bool)).filter
    (fun z => rowSum n (entryBits n) g z = 0) with hK
  have hKc : 2 ^ (n * n * entryBits n) ≤ 2 ^ s * K.card :=
    kernel_card (n := n) (w := entryBits n) (L := n * n * entryBits n) g hg
  have hEK : 2 * E.ncard ^ 2 < K.card := by
    by_contra hc
    push Not at hc
    have : 2 ^ s * (2 * E.ncard ^ 2) ≥ 2 ^ s * K.card := Nat.mul_le_mul_left _ hc
    omega
  obtain ⟨z₁, hz₁K, z₂, hz₂K, hz⟩ := exists_vote_shifts_in E K hEK
  have hz₁0 : rowSum n (entryBits n) g z₁ = 0 := (Finset.mem_filter.1 hz₁K).2
  have hz₂0 : rowSum n (entryBits n) g z₂ = 0 := (Finset.mem_filter.1 hz₂K).2
  have hA : ∀ x : Fin (n * n * entryBits n) → Bool, rowSum n (entryBits n) g x = b →
      ∀ z : Fin (n * n * entryBits n) → Bool, rowSum n (entryBits n) g z = 0 →
      rowSum n (entryBits n) g (xorVec x z) = b := by
    intro x hx z hz0
    rw [rowSum_xorVec g hg, hx, hz0, add_zero]
  have hvote := vote_solves_on D n G hsol (fun _ => false) z₁ z₂
    (Y := {x | rowSum n (entryBits n) g x = b}) (fun x hx => by
      have hx' : rowSum n (entryBits n) g x = b := hx
      have mem : ∀ z : Fin (n * n * entryBits n) → Bool, rowSum n (entryBits n) g z = 0 →
          xorVec x z ∉ E → xorVec x z ∈ F :=
        fun z hz0 hzE => hsub ⟨hA x hx' z hz0, hzE⟩
      have m0' : x ∉ E → xorVec x (fun _ => false) ∈ F := fun hxE => by
        rw [xorVec_zero]; exact hsub ⟨hx', hxE⟩
      rcases hz x with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨m0' h1, mem z₁ hz₁0 h2⟩
      · exact Or.inr (Or.inl ⟨mem z₁ hz₁0 h1, mem z₂ hz₂0 h2⟩)
      · exact Or.inr (Or.inr ⟨m0' h1, mem z₂ hz₂0 h2⟩))
  exact hn₀ n hn (tripleTapes D) (valid_triple D hD) hT s hs g hg b hb _ hvote

end Transpose.Tape.Impl
