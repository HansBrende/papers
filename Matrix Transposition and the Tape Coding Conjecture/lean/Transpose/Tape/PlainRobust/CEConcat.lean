import Transpose.Tape.PlainRobust.CEConcatNet
import Transpose.Tape.PlainRobust.CESelect

/-!
# Network-computable hints: plain ⟹ no code on sets with a computable `O(1)`-candidate cover

A **hint computation** is a diagram `Pre` (any walks from cell `0` with unit steps, length `O(L)`)
with a code `C₁` within `Pre`'s profile capacities, and a map `hx` reading a hint off the values into
`Pre`'s last node and its visible input. The concatenation code (`concatCode`) runs `C₁` in the
prefix of `concatDiagram Pre D P r`, carries the hint (`s` bits) along the spine, and runs
`codes hint` in the main part (`concat_solves_at`).

Hence (`noCode_netCover_of_noCode`): under `NoCode_TM`, no code exists on a set `F` for which a
network-computable hint and `K = O(1)` shift tables put every input into `F` with one of the shifts.
This is the general form of the hint method (`noCode_additiveCover_of_noCode` is the special case of
an additive hint computed by an input sweep).
-/

namespace Transpose.Tape.Impl

open Transpose TSDiagram

/-! ### The concatenation code -/

section Code

variable {k₁ k₂ : ℕ} (Pre : TSDiagram k₁) (D : TSDiagram k₂) (n G P s : ℕ)
  (C₁ : NetCode) (hx : (ℕ × ℕ → ℕ) → (ℕ → Bool) → ℕ) (codes : ℕ → NetCode)

/-- `Pre`'s values into a prefix node (other edges read `0`). -/
noncomputable def inPre (f : ℕ × ℕ → ℕ) : ℕ × ℕ → ℕ :=
  fun e' => if e' ∈ Pre.edges (blockSize G n) then f e' else 0

/-- The visible input masked to `Pre`'s rows at node `u`. -/
noncomputable def maskPre (u : ℕ) (v : ℕ → Bool) : ℕ → Bool :=
  fun d => if d / (n * entryBits n) ∈ Pre.rowsAt n (entryBits n) (blockSize G n) u then v d else false

/-- The hint on the memory edge into node `u`. -/
def hintIn (u : ℕ) (f : ℕ × ℕ → ℕ) : ℕ := f (u - 1, u) % 2 ^ s

/-- The values into a main-part node, indexed by `D`'s edges (memory edges stripped of the hint). -/
noncomputable def inMain (f : ℕ × ℕ → ℕ) : ℕ × ℕ → ℕ :=
  fun e'' => if e'' ∈ D.edges (blockSize G n) then
    (if e''.2 = e''.1 + 1 then f (P + e''.1, P + e''.2) / 2 ^ s else f (P + e''.1, P + e''.2))
  else 0

/-- **The concatenation code.** `Pre`'s code runs in the prefix; its last node puts the hint on its
memory edge; the hint travels along the spine; the main part runs `codes hint`, with the hint in the
low `s` bits of its memory edges. -/
noncomputable def concatCode : NetCode where
  enc e f v :=
    if e.1 < Pre.nodes (blockSize G n) then
      (if e ∈ Pre.edges (blockSize G n) then C₁.enc e (inPre Pre n G f) (maskPre Pre n G e.1 v)
       else if e.2 = e.1 + 1 then hx (inPre Pre n G f) (maskPre Pre n G e.1 v) % 2 ^ s else 0)
    else if e.1 < P then
      (if e.2 = e.1 + 1 then hintIn s e.1 f else 0)
    else
      (if (e.1 - P, e.2 - P) ∈ D.edges (blockSize G n) then
        (if e.2 = e.1 + 1 then
          hintIn s e.1 f + 2 ^ s *
            (codes (hintIn s e.1 f)).enc (e.1 - P, e.2 - P) (inMain D n G P s f) v
        else (codes (hintIn s e.1 f)).enc (e.1 - P, e.2 - P) (inMain D n G P s f) v)
      else 0)
  dec o f v := (codes (hintIn s (P + D.outNode (blockSize G n) o) f)).dec o (inMain D n G P s f) v

theorem concatCode_pre (e : ℕ × ℕ) (f : ℕ × ℕ → ℕ) (v : ℕ → Bool)
    (h1 : e.1 < Pre.nodes (blockSize G n)) (hE : e ∈ Pre.edges (blockSize G n)) :
    (concatCode Pre D n G P s C₁ hx codes).enc e f v =
      C₁.enc e (inPre Pre n G f) (maskPre Pre n G e.1 v) := by
  show (if e.1 < Pre.nodes (blockSize G n) then _ else _) = _
  rw [ite_eq_left h1, ite_eq_left hE]

theorem concatCode_junction (e : ℕ × ℕ) (f : ℕ × ℕ → ℕ) (v : ℕ → Bool)
    (h1 : e.1 < Pre.nodes (blockSize G n)) (hE : e ∉ Pre.edges (blockSize G n))
    (hm : e.2 = e.1 + 1) :
    (concatCode Pre D n G P s C₁ hx codes).enc e f v =
      hx (inPre Pre n G f) (maskPre Pre n G e.1 v) % 2 ^ s := by
  show (if e.1 < Pre.nodes (blockSize G n) then _ else _) = _
  rw [ite_eq_left h1, ite_eq_right hE, ite_eq_left hm]

theorem concatCode_pre_other (e : ℕ × ℕ) (f : ℕ × ℕ → ℕ) (v : ℕ → Bool)
    (h1 : e.1 < Pre.nodes (blockSize G n)) (hE : e ∉ Pre.edges (blockSize G n))
    (hm : ¬ e.2 = e.1 + 1) :
    (concatCode Pre D n G P s C₁ hx codes).enc e f v = 0 := by
  show (if e.1 < Pre.nodes (blockSize G n) then _ else _) = _
  rw [ite_eq_left h1, ite_eq_right hE, ite_eq_right hm]

theorem concatCode_ret (e : ℕ × ℕ) (f : ℕ × ℕ → ℕ) (v : ℕ → Bool)
    (h1 : ¬ e.1 < Pre.nodes (blockSize G n)) (h2 : e.1 < P) :
    (concatCode Pre D n G P s C₁ hx codes).enc e f v =
      if e.2 = e.1 + 1 then hintIn s e.1 f else 0 := by
  show (if e.1 < Pre.nodes (blockSize G n) then _ else _) = _
  rw [ite_eq_right h1, ite_eq_left h2]

theorem concatCode_main (e : ℕ × ℕ) (f : ℕ × ℕ → ℕ) (v : ℕ → Bool)
    (h1 : ¬ e.1 < Pre.nodes (blockSize G n)) (h2 : ¬ e.1 < P) :
    (concatCode Pre D n G P s C₁ hx codes).enc e f v =
      if (e.1 - P, e.2 - P) ∈ D.edges (blockSize G n) then
        (if e.2 = e.1 + 1 then
          hintIn s e.1 f + 2 ^ s *
            (codes (hintIn s e.1 f)).enc (e.1 - P, e.2 - P) (inMain D n G P s f) v
        else (codes (hintIn s e.1 f)).enc (e.1 - P, e.2 - P) (inMain D n G P s f) v)
      else 0 := by
  show (if e.1 < Pre.nodes (blockSize G n) then _ else _) = _
  rw [ite_eq_right h1, ite_eq_right h2]

end Code

/-! ### Correctness -/

section Correct

variable {k₁ k₂ : ℕ} (Pre : TSDiagram k₁) (D : TSDiagram k₂) {n G P s : ℕ}
  (C₁ : NetCode) (hx : (ℕ × ℕ → ℕ) → (ℕ → Bool) → ℕ) (codes : ℕ → NetCode)
  (x : Fin (n * n * entryBits n) → Bool)

theorem maskPre_concat (hr : 1 ≤ blockSize G n)
    (hP : Pre.nodes (blockSize G n) * blockSize G n ≤ P * blockSize G n) (u : ℕ) :
    maskPre Pre n G u ((concatDiagram Pre D P (blockSize G n)).visible n (entryBits n)
      (blockSize G n) u x) = Pre.visible n (entryBits n) (blockSize G n) u x := by
  funext d
  simp only [maskPre, TSDiagram.visible]
  by_cases h1 : d / (n * entryBits n) ∈ Pre.rowsAt n (entryBits n) (blockSize G n) u
  · have h2 := rowsAt_concat_left Pre D hr (n := n) (w := entryBits n) (y := u) hP h1
    simp [h1, h2]
  · simp [h1]

/-- **The prefix reproduces `Pre`'s code.** -/
theorem concat_pre (hr : 1 ≤ blockSize G n)
    (hP : Pre.nodes (blockSize G n) * blockSize G n ≤ P * blockSize G n) :
    ∀ u, u < Pre.nodes (blockSize G n) →
      inPre Pre n G ((concatCode Pre D n G P s C₁ hx codes).inVals
        ((concatDiagram Pre D P (blockSize G n)).edges (blockSize G n))
        (fun y => (concatDiagram Pre D P (blockSize G n)).visible n (entryBits n)
          (blockSize G n) y x) u) =
      C₁.inVals (Pre.edges (blockSize G n))
        (fun y => Pre.visible n (entryBits n) (blockSize G n) y x) u := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
  intro hu
  funext e'
  show (if e' ∈ Pre.edges (blockSize G n) then _ else 0) = _
  rw [inVals_eq C₁]
  by_cases hc : e' ∈ Pre.edges (blockSize G n) ∧ e'.2 = u ∧ e'.1 < u
  · rw [ite_eq_left hc.1, ite_eq_left hc]
    have hE := edges_concat_left Pre D hr hP hc.1
    rw [inVals_eq, ite_eq_left ⟨hE, hc.2⟩,
      concatCode_pre Pre D n G P s C₁ hx codes e' _ _ (by omega) hc.1,
      ih e'.1 hc.2.2 (by omega), maskPre_concat Pre D x hr hP]
  · by_cases hE' : e' ∈ Pre.edges (blockSize G n)
    · rw [ite_eq_left hE', ite_eq_right hc, inVals_eq, ite_eq_right]
      intro h; exact hc ⟨hE', h.2⟩
    · rw [ite_eq_right hE', ite_eq_right (fun h => hE' h.1)]

/-- The hint computed at the last prefix node. -/
noncomputable def preHint (n G s : ℕ) : ℕ :=
  hx (C₁.inVals (Pre.edges (blockSize G n))
      (fun y => Pre.visible n (entryBits n) (blockSize G n) y x) (Pre.nodes (blockSize G n) - 1))
    (Pre.visible n (entryBits n) (blockSize G n) (Pre.nodes (blockSize G n) - 1) x) % 2 ^ s

/-- **The hint travels along the spine** to the first node of the main part. -/
theorem concat_ret (hr : 1 ≤ blockSize G n) (hPre : 1 ≤ Pre.nodes (blockSize G n))
    (hP : Pre.nodes (blockSize G n) + 2 ≤ P) (hDN : 1 ≤ D.nodes (blockSize G n)) :
    ∀ j, Pre.nodes (blockSize G n) + j ≤ P →
      (concatCode Pre D n G P s C₁ hx codes).inVals
        ((concatDiagram Pre D P (blockSize G n)).edges (blockSize G n))
        (fun y => (concatDiagram Pre D P (blockSize G n)).visible n (entryBits n)
          (blockSize G n) y x) (Pre.nodes (blockSize G n) + j)
        (Pre.nodes (blockSize G n) + j - 1, Pre.nodes (blockSize G n) + j) % 2 ^ s =
      preHint Pre C₁ hx x n G s := by
  have hPm : Pre.nodes (blockSize G n) * blockSize G n ≤ P * blockSize G n :=
    Nat.mul_le_mul_right _ (by omega)
  intro j
  induction j with
  | zero =>
    intro _
    have hmemE : (Pre.nodes (blockSize G n) + 0 - 1, Pre.nodes (blockSize G n) + 0) ∈
        (concatDiagram Pre D P (blockSize G n)).edges (blockSize G n) := by
      apply Finset.mem_union_left
      rw [mem_memEdges, nodes_concat Pre D hr]
      simp only
      omega
    have hnot : (Pre.nodes (blockSize G n) + 0 - 1, Pre.nodes (blockSize G n) + 0) ∉
        Pre.edges (blockSize G n) := by
      intro h
      have := (edges_lt Pre _ h).2
      simp only at this; omega
    rw [inVals_eq, ite_eq_left ⟨hmemE, rfl, by simp only; omega⟩]
    rw [concatCode_junction Pre D n G P s C₁ hx codes _ _ _ (by simp only; omega) hnot
      (by simp only; omega)]
    simp only [Nat.add_zero]
    rw [concat_pre Pre D C₁ hx codes x hr hPm _ (by omega), maskPre_concat Pre D x hr hPm,
      Nat.mod_mod]
    rfl
  | succ j ih =>
    intro hj
    have hmemE : (Pre.nodes (blockSize G n) + (j + 1) - 1, Pre.nodes (blockSize G n) + (j + 1)) ∈
        (concatDiagram Pre D P (blockSize G n)).edges (blockSize G n) := by
      apply Finset.mem_union_left
      rw [mem_memEdges, nodes_concat Pre D hr]
      simp only
      omega
    rw [inVals_eq, ite_eq_left ⟨hmemE, rfl, by simp only; omega⟩]
    rw [concatCode_ret Pre D n G P s C₁ hx codes _ _ _ (by simp only; omega) (by simp only; omega),
      ite_eq_left (by simp only; omega)]
    unfold hintIn
    rw [show Pre.nodes (blockSize G n) + (j + 1) - 1 = Pre.nodes (blockSize G n) + j by omega,
      ih (by omega)]
    unfold preHint
    rw [Nat.mod_mod]

/-- **The main part runs `codes hint`.** -/
theorem concat_main {L : ℕ} (hr : 1 ≤ blockSize G n) (hD : D.Valid L)
    (hPre : 1 ≤ Pre.nodes (blockSize G n)) (hP : Pre.nodes (blockSize G n) + 2 ≤ P) :
    ∀ u', u' < D.nodes (blockSize G n) →
      (concatCode Pre D n G P s C₁ hx codes).inVals
          ((concatDiagram Pre D P (blockSize G n)).edges (blockSize G n))
          (fun y => (concatDiagram Pre D P (blockSize G n)).visible n (entryBits n)
            (blockSize G n) y x) (P + u') (P + u' - 1, P + u') % 2 ^ s =
        preHint Pre C₁ hx x n G s ∧
      inMain D n G P s ((concatCode Pre D n G P s C₁ hx codes).inVals
          ((concatDiagram Pre D P (blockSize G n)).edges (blockSize G n))
          (fun y => (concatDiagram Pre D P (blockSize G n)).visible n (entryBits n)
            (blockSize G n) y x) (P + u')) =
        (codes (preHint Pre C₁ hx x n G s)).inVals (D.edges (blockSize G n))
          (fun y => D.visible n (entryBits n) (blockSize G n) y x) u' := by
  have hPm : Pre.nodes (blockSize G n) * blockSize G n ≤ P * blockSize G n :=
    Nat.mul_le_mul_right _ (by omega)
  intro u'
  induction u' using Nat.strong_induction_on with
  | _ u' ih =>
  intro hu'
  have hstate : (concatCode Pre D n G P s C₁ hx codes).inVals
      ((concatDiagram Pre D P (blockSize G n)).edges (blockSize G n))
      (fun y => (concatDiagram Pre D P (blockSize G n)).visible n (entryBits n)
        (blockSize G n) y x) (P + u') (P + u' - 1, P + u') % 2 ^ s =
      preHint Pre C₁ hx x n G s := by
    rcases Nat.eq_zero_or_pos u' with h0 | hpos
    · subst h0
      have := concat_ret Pre D (s := s) C₁ hx codes x hr hPre hP (by omega)
        (P - Pre.nodes (blockSize G n)) (by omega)
      rw [show Pre.nodes (blockSize G n) + (P - Pre.nodes (blockSize G n)) = P by omega] at this
      simpa only [Nat.add_zero] using this
    · have hDmem : (u' - 1, u') ∈ D.edges (blockSize G n) := by
        apply Finset.mem_union_left
        rw [mem_memEdges]
        simp only
        omega
      have hmemE : (P + u' - 1, P + u') ∈
          (concatDiagram Pre D P (blockSize G n)).edges (blockSize G n) := by
        have := (mem_edges_concat_add Pre D (P := P) hr hD (by omega) (u' - 1) u').2 hDmem
        rwa [show P + (u' - 1) = P + u' - 1 by omega] at this
      rw [inVals_eq, ite_eq_left ⟨hmemE, rfl, by simp only; omega⟩,
        concatCode_main Pre D n G P s C₁ hx codes _ _ _ (by simp only; omega)
          (by simp only; omega)]
      simp only
      rw [show P + u' - 1 - P = u' - 1 by omega, Nat.add_sub_cancel_left, ite_eq_left hDmem,
        ite_eq_left (by omega), Nat.add_mul_mod_self_left]
      unfold hintIn
      have h := (ih (u' - 1) (by omega) (by omega)).1
      rw [show P + (u' - 1) = P + u' - 1 by omega] at h
      rw [show P + u' - 1 - 1 = P + u' - 1 - 1 from rfl, Nat.mod_mod, h]
  refine ⟨hstate, ?_⟩
  funext e''
  show (if e'' ∈ D.edges (blockSize G n) then _ else 0) = _
  rw [inVals_eq (codes _)]
  by_cases hc : e'' ∈ D.edges (blockSize G n) ∧ e''.2 = u' ∧ e''.1 < u'
  · rw [ite_eq_left hc.1, ite_eq_left hc]
    have hE : (P + e''.1, P + e''.2) ∈
        (concatDiagram Pre D P (blockSize G n)).edges (blockSize G n) :=
      (mem_edges_concat_add Pre D hr hD (by omega) _ _).2 hc.1
    obtain ⟨ihS, ihI⟩ := ih e''.1 hc.2.2 (by omega)
    have hhint : hintIn s (P + e''.1) ((concatCode Pre D n G P s C₁ hx codes).inVals
        ((concatDiagram Pre D P (blockSize G n)).edges (blockSize G n))
        (fun y => (concatDiagram Pre D P (blockSize G n)).visible n (entryBits n)
          (blockSize G n) y x) (P + e''.1)) = preHint Pre C₁ hx x n G s := ihS
    have hval : (concatCode Pre D n G P s C₁ hx codes).inVals
        ((concatDiagram Pre D P (blockSize G n)).edges (blockSize G n))
        (fun y => (concatDiagram Pre D P (blockSize G n)).visible n (entryBits n)
          (blockSize G n) y x) (P + u') (P + e''.1, P + e''.2) =
        (concatCode Pre D n G P s C₁ hx codes).enc (P + e''.1, P + e''.2)
          ((concatCode Pre D n G P s C₁ hx codes).inVals
            ((concatDiagram Pre D P (blockSize G n)).edges (blockSize G n))
            (fun y => (concatDiagram Pre D P (blockSize G n)).visible n (entryBits n)
              (blockSize G n) y x) (P + e''.1))
          ((concatDiagram Pre D P (blockSize G n)).visible n (entryBits n)
            (blockSize G n) (P + e''.1) x) := by
      rw [inVals_eq, ite_eq_left ⟨hE, by simp only; omega, by simp only; omega⟩]
    rw [hval, concatCode_main Pre D n G P s C₁ hx codes _ _ _ (by simp only; omega)
      (by simp only; omega)]
    simp only [Nat.add_sub_cancel_left]
    rw [ite_eq_left (hc.1 : (e''.1, e''.2) ∈ D.edges (blockSize G n)), hhint, ihI,
      visible_concat_add Pre D hPm]
    by_cases hm : e''.2 = e''.1 + 1
    · have hlt : preHint Pre C₁ hx x n G s < 2 ^ s := Nat.mod_lt _ (Nat.two_pow_pos s)
      rw [ite_eq_left hm, ite_eq_left (show P + e''.2 = P + e''.1 + 1 by omega),
        Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hlt, Nat.zero_add]
    · rw [ite_eq_right hm, ite_eq_right (show ¬ P + e''.2 = P + e''.1 + 1 by omega)]
  · by_cases hE' : e'' ∈ D.edges (blockSize G n)
    · rw [ite_eq_left hE', ite_eq_right hc]
      have h0 : (concatCode Pre D n G P s C₁ hx codes).inVals
          ((concatDiagram Pre D P (blockSize G n)).edges (blockSize G n))
          (fun y => (concatDiagram Pre D P (blockSize G n)).visible n (entryBits n)
            (blockSize G n) y x) (P + u') (P + e''.1, P + e''.2) = 0 := by
        rw [inVals_eq, ite_eq_right]
        intro h
        apply hc
        refine ⟨hE', ?_, ?_⟩ <;> simp only at h <;> omega
      rw [h0]
      split_ifs <;> simp
    · rw [ite_eq_right hE', ite_eq_right (fun h => hE' h.1)]

end Correct

/-! ### Removing a network-computed hint -/

/-- **A network-computed hint can be removed, input by input.** If `C₁` stays within `Pre`'s profile
capacities on `x` and `codes hint` solves `x` at the profile capacities of `D`, the concatenation code
solves `x` on `concatDiagram Pre D P r`, at its per-node blocks plus `s` bits per memory edge. -/
theorem concat_solves_at {k₁ k₂ : ℕ} (Pre : TSDiagram k₁) (D : TSDiagram k₂) {n G P s : ℕ}
    (C₁ : NetCode) (hx : (ℕ × ℕ → ℕ) → (ℕ → Bool) → ℕ) (codes : ℕ → NetCode)
    (x : Fin (n * n * entryBits n) → Bool) (hG : 1 ≤ G) (hn : 1 ≤ n) (hPreT : 1 ≤ Pre.T)
    (hD : D.Valid (n * n * entryBits n)) (hroom : ConcatRoom Pre P (blockSize G n))
    (hcap₁ : ∀ e ∈ Pre.edges (blockSize G n), C₁.edgeVal (Pre.edges (blockSize G n))
      (fun y => Pre.visible n (entryBits n) (blockSize G n) y x) e < 2 ^ Pre.profileCap n G e)
    (hsol : D.Solves n G (D.profileCap n G) {x} (codes (preHint Pre C₁ hx x n G s))) :
    (concatDiagram Pre D P (blockSize G n)).Solves n G
      ((concatDiagram Pre D P (blockSize G n)).blockCap n G
        (fun y => ∑ t, (pairRes (blockSize G n) ((concatDiagram Pre D P (blockSize G n)).work t)
          (concatDiagram Pre D P (blockSize G n)).T y).card) s)
      {x} (concatCode Pre D n G P s C₁ hx codes) := by
  intro x' hx'
  rw [Set.mem_singleton_iff] at hx'
  subst hx'
  have hr : 1 ≤ blockSize G n := one_le_blockSize hG hn
  have hPN := concatRoom_nodes hr hroom
  have hPm : Pre.nodes (blockSize G n) * blockSize G n ≤ P * blockSize G n :=
    Nat.mul_le_mul_right _ (by omega)
  have hL1 : 1 ≤ n * n * entryBits n :=
    Nat.one_le_iff_ne_zero.2 (by unfold entryBits; positivity)
  have hT : 1 ≤ D.T := one_le_T hD hL1
  have hDN : 1 ≤ D.nodes (blockSize G n) :=
    (numSlots_spec hr).2 (by simp only [Nat.zero_mul]; omega)
  have hPre1 : 1 ≤ Pre.nodes (blockSize G n) :=
    (numSlots_spec hr).2 (by simp only [Nat.zero_mul]; omega)
  obtain ⟨hcapD, houtD⟩ := hsol x' rfl
  refine ⟨fun e he => ?_, fun d hd => ?_⟩
  · have hlt := edges_fst_lt _ e he
    have hEl := edges_lt _ e he
    rw [nodes_concat Pre D hr] at hEl
    simp only [NetCode.edgeVal]
    by_cases h1 : e.1 < Pre.nodes (blockSize G n)
    · by_cases hE : e ∈ Pre.edges (blockSize G n)
      · rw [concatCode_pre Pre D n G P s C₁ hx codes e _ _ h1 hE,
          concat_pre Pre D C₁ hx codes x' hr hPm e.1 h1, maskPre_concat Pre D x' hr hPm]
        have hv := hcap₁ e hE
        simp only [NetCode.edgeVal] at hv
        refine lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) ?_)
        by_cases hm : e.2 = e.1 + 1
        · have hmP := mem_memEdges_of_edges Pre hE hm
          rw [blockCap_mem _ (mem_memEdges_of_edges _ he hm)]
          unfold TSDiagram.profileCap
          rw [blockCap_mem Pre hmP, Nat.add_zero]
          exact le_trans (Nat.mul_le_mul_right _ (resSum_concat_left Pre D hr hPm e.1))
            (Nat.le_add_right _ _)
        · have hcP := mem_chordEdges_of_edges Pre hE hm
          rw [blockCap_chord _ (mem_chordEdges_concat_left Pre D hr hPm hcP)]
          unfold TSDiagram.profileCap
          rw [blockCap_chord Pre hcP]
          exact Nat.mul_le_mul_right _ (chordTapes_concat_left Pre D hr hPm hcP)
      · by_cases hm : e.2 = e.1 + 1
        · rw [concatCode_junction Pre D n G P s C₁ hx codes e _ _ h1 hE hm,
            blockCap_mem _ (mem_memEdges_of_edges _ he hm)]
          exact lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
            (Nat.pow_le_pow_right (by norm_num) (by omega))
        · rw [concatCode_pre_other Pre D n G P s C₁ hx codes e _ _ h1 hE hm]
          exact Nat.two_pow_pos _
    · by_cases h2 : e.1 < P
      · rw [concatCode_ret Pre D n G P s C₁ hx codes e _ _ h1 h2]
        by_cases hm : e.2 = e.1 + 1
        · rw [ite_eq_left hm, blockCap_mem _ (mem_memEdges_of_edges _ he hm)]
          exact lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
            (Nat.pow_le_pow_right (by norm_num) (by omega))
        · rw [ite_eq_right hm]; exact Nat.two_pow_pos _
      · rw [concatCode_main Pre D n G P s C₁ hx codes e _ _ h1 h2]
        obtain ⟨a', b'⟩ := e
        simp only at h1 h2 hlt hEl ⊢
        obtain ⟨a'', rfl⟩ : ∃ a'', a' = P + a'' := ⟨a' - P, by omega⟩
        obtain ⟨b'', rfl⟩ : ∃ b'', b' = P + b'' := ⟨b' - P, by omega⟩
        have hED := (mem_edges_concat_add Pre D hr hD (by omega) a'' b'').1 he
        simp only [Nat.add_sub_cancel_left]
        rw [ite_eq_left hED]
        obtain ⟨hS, hI⟩ := concat_main Pre D (s := s) C₁ hx codes x' hr hD hPre1 hPN a''
          (edges_lt D _ hED).1
        have hhint : hintIn s (P + a'') ((concatCode Pre D n G P s C₁ hx codes).inVals
            ((concatDiagram Pre D P (blockSize G n)).edges (blockSize G n))
            (fun y => (concatDiagram Pre D P (blockSize G n)).visible n (entryBits n)
              (blockSize G n) y x') (P + a'')) = preHint Pre C₁ hx x' n G s := hS
        rw [hhint, hI, visible_concat_add Pre D hPm]
        have hv := hcapD (a'', b'') hED
        simp only [NetCode.edgeVal] at hv
        by_cases hm : b'' = a'' + 1
        · rw [ite_eq_left (show P + b'' = P + a'' + 1 by omega),
            blockCap_mem _ (mem_memEdges_of_edges _ he (by simp only; omega))]
          have hmD := mem_memEdges_of_edges D hED (by simp only; omega)
          have hcap : D.profileCap n G (a'', b'') =
              (∑ t, (pairRes (blockSize G n) (D.work t) D.T a'').card) * (blockSize G n * G) := by
            unfold TSDiagram.profileCap; rw [blockCap_mem D hmD, Nat.add_zero]
          refine lt_of_lt_of_le (pack_state_lt (Nat.mod_lt _ (Nat.two_pow_pos s)) hv)
            (Nat.pow_le_pow_right (by norm_num) ?_)
          rw [hcap]
          exact Nat.add_le_add_right
            (Nat.mul_le_mul_right _ (resSum_concat_right Pre D (P := P) (r := blockSize G n) hD a''))
            _
        · rw [ite_eq_right (show ¬ P + b'' = P + a'' + 1 by omega)]
          have hcD := mem_chordEdges_of_edges D hED (by simp only; omega)
          rw [blockCap_chord _ (mem_chordEdges_of_edges _ he (by simp only; omega))]
          have hcap : D.profileCap n G (a'', b'') =
              D.chordTapes (blockSize G n) (a'', b'') * (blockSize G n * G) := by
            unfold TSDiagram.profileCap; rw [blockCap_chord D hcD]
          refine lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) ?_)
          rw [hcap]
          exact Nat.mul_le_mul_right _ (chordTapes_concat_right Pre D (P := P) hr hD a'' b'')
  · have ho := tpos_lt hd
    have hu' := outNode_lt hD hr hL1 (tpos n (entryBits n) d)
    obtain ⟨hS, hI⟩ := concat_main Pre D (s := s) C₁ hx codes x' hr hD hPre1 hPN
      (D.outNode (blockSize G n) (tpos n (entryBits n) d)) hu'
    show (concatCode Pre D n G P s C₁ hx codes).dec _ _ _ = _
    rw [outNode_concat Pre D hr hD hT]
    show (codes (hintIn s (P + D.outNode (blockSize G n) (tpos n (entryBits n) d)) _)).dec
      _ (inMain D n G P s _) _ = _
    have hhint : hintIn s (P + D.outNode (blockSize G n) (tpos n (entryBits n) d))
        ((concatCode Pre D n G P s C₁ hx codes).inVals
          ((concatDiagram Pre D P (blockSize G n)).edges (blockSize G n))
          (fun y => (concatDiagram Pre D P (blockSize G n)).visible n (entryBits n)
            (blockSize G n) y x') (P + D.outNode (blockSize G n) (tpos n (entryBits n) d))) =
        preHint Pre C₁ hx x' n G s := hS
    rw [hhint, hI]
    beta_reduce
    rw [visible_concat_add Pre D hPm]
    exact houtD d hd

/-- The concatenated diagram keeps linear time, with room for the return walk. -/
theorem concat_room_time {k₁ k₂ : ℕ} (Pre : TSDiagram k₁) (D : TSDiagram k₂) {n G c c₁ : ℕ}
    (hG : 1 ≤ G) (hn : 1 ≤ n) (hPreT : Pre.T ≤ c₁ * (n * n * entryBits n))
    (hT : D.T ≤ c * (n * n * entryBits n)) :
    ConcatRoom Pre (2 * c₁ * n * G + 4) (blockSize G n) ∧
    (2 * c₁ * n * G + 4) * blockSize G n + D.T ≤ (2 * c₁ * G + c + 4) * (n * n * entryBits n) := by
  have hr : 1 ≤ blockSize G n := one_le_blockSize hG hn
  have hrnw : blockSize G n ≤ n * entryBits n := blockSize_le hG
  have hrG : n * entryBits n ≤ blockSize G n * G := blockSize_mul_ge hG
  have hN : Pre.nodes (blockSize G n) * blockSize G n ≤ Pre.T + blockSize G n := by
    have := nodes_mul_le (D := Pre) (blockSize G n); omega
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
  · unfold ConcatRoom
    have e : (2 * c₁ * n * G + 4) * blockSize G n =
        2 * c₁ * (n * (blockSize G n * G)) + 4 * blockSize G n := by ring
    rw [e]
    have := Nat.mul_le_mul_left (2 * c₁) hLr
    have h2 : 2 * (Pre.nodes (blockSize G n) * blockSize G n) ≤
        2 * (c₁ * (n * n * entryBits n)) + 2 * blockSize G n := by omega
    nlinarith
  · have e : (2 * c₁ * n * G + 4) * blockSize G n =
        2 * c₁ * G * (n * blockSize G n) + 4 * blockSize G n := by ring
    rw [e]
    have h1 := Nat.mul_le_mul_left (2 * c₁ * G) hnr
    have e2 : (2 * c₁ * G + c + 4) * (n * n * entryBits n) =
        2 * c₁ * G * (n * n * entryBits n) + c * (n * n * entryBits n) +
          4 * (n * n * entryBits n) := by ring
    rw [e2]
    omega

/-- **Plain ⟹ no code on any set with a network-computable `O(1)`-candidate cover.** Under
`NoCode_TM`: for all constants and all large `n`, no code solves complete exchange at the profile
capacities on a set `F` for which some hint computation (a diagram `Pre` of length `≤ c₁ L` on `k₁`
tapes, a code `C₁` within its profile capacities on every input, and a map `hx` reading an `s`-bit
hint off its last node, `s ≤ C n w`) and `K` shift tables put every input into `F` with one of the
shifts. -/
theorem noCode_netCover_of_noCode (h : NoCode_TM) (k G c C K k₁ c₁ : ℕ) (hG : 1 ≤ G)
    (hK : 1 ≤ K) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
      ∀ (Pre : TSDiagram k₁), Pre.WalksOK → 1 ≤ Pre.T → Pre.T ≤ c₁ * (n * n * entryBits n) →
      ∀ (C₁ : NetCode) (hx : (ℕ × ℕ → ℕ) → (ℕ → Bool) → ℕ) (s : ℕ), s ≤ C * (n * entryBits n) →
      (∀ (x : Fin (n * n * entryBits n) → Bool), ∀ e ∈ Pre.edges (blockSize G n),
        C₁.edgeVal (Pre.edges (blockSize G n))
          (fun y => Pre.visible n (entryBits n) (blockSize G n) y x) e < 2 ^ Pre.profileCap n G e) →
      ∀ (F : Set (Fin (n * n * entryBits n) → Bool))
        (z : ℕ → ℕ → (Fin (n * n * entryBits n) → Bool)),
        (∀ x, ∃ j < K, xorVec x (z j (hx (C₁.inVals (Pre.edges (blockSize G n))
          (fun y => Pre.visible n (entryBits n) (blockSize G n) y x)
            (Pre.nodes (blockSize G n) - 1))
          (Pre.visible n (entryBits n) (blockSize G n) (Pre.nodes (blockSize G n) - 1) x) %
            2 ^ s)) ∈ F) →
      ∀ code : NetCode, ¬ D.Solves n G (D.profileCap n G) F code := by
  obtain ⟨n₀, hn₀⟩ := h ((K + 1) * (k₁ + k + C) + 6 * K ^ 2) G
    ((2 * (2 * c₁ * G + c + 4) + 2) * G + (2 * c₁ * G + c + 4) + 4) hG
  refine ⟨max n₀ 1, fun n hn D hD hT Pre hPre hPreT1 hPreT C₁ hx s hs hcap₁ F z hz code hsol => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hr : 1 ≤ blockSize G n := one_le_blockSize hG hn1
  have hrG : n * entryBits n ≤ blockSize G n * G := blockSize_mul_ge hG
  have hsB : s ≤ C * (blockSize G n * G) := le_trans hs (Nat.mul_le_mul_left _ hrG)
  obtain ⟨hroom, htime⟩ := concat_room_time Pre D hG hn1 hPreT hT
  -- the candidates: the concatenation codes of the `K` shift tables, with `C` stationary tapes
  have hcov : ∀ x, ∃ j < K,
      (addTapes (concatDiagram Pre D (2 * c₁ * n * G + 4) (blockSize G n)) C).Solves n G
        ((addTapes (concatDiagram Pre D (2 * c₁ * n * G + 4) (blockSize G n)) C).profileCap n G)
        {x} (concatCode Pre D n G (2 * c₁ * n * G + 4) s C₁ hx
          (fun hint => shiftCode D n (entryBits n) (blockSize G n) code (z j hint))) := by
    intro x
    obtain ⟨j, hj, hjx⟩ := hz x
    refine ⟨j, hj, solves_profileCap_addTapes (a := C) hr hsB ?_⟩
    refine concat_solves_at Pre D C₁ hx _ x hG hn1 hPreT1 hD hroom (hcap₁ x) ?_
    intro x' hx'
    rw [Set.mem_singleton_iff] at hx'
    subst hx'
    exact solves_shiftCode D hsol _ x' hjx
  have hD₂ := valid_addTapes _ (valid_concat Pre D hPre hD hr hroom) C
  have hT₂ : (addTapes (concatDiagram Pre D (2 * c₁ * n * G + 4) (blockSize G n)) C).T ≤
      (2 * c₁ * G + c + 4) * (n * n * entryBits n) := by
    rw [T_addTapes]; exact htime
  obtain ⟨hroom₂, htime₂⟩ := sel_room_time _ hG hn1 hT₂
  have hsel := select_solves _ hG hn1 hK hD₂ hroom₂
    (fun j => concatCode Pre D n G (2 * c₁ * n * G + 4) s C₁ hx
      (fun hint => shiftCode D n (entryBits n) (blockSize G n) code (z j hint))) hcov
  have hs' : selBits K (n * n * entryBits n) ≤ 6 * K ^ 2 * (blockSize G n * G) := by
    have h2 : entryBits n ≤ blockSize G n * G :=
      le_trans (Nat.le_mul_of_pos_left _ (by omega)) hrG
    exact le_trans (selBits_le K n) (Nat.mul_le_mul_left _ h2)
  have hsel' := solves_profileCap_addTapes (a := 6 * K ^ 2) hr hs' hsel
  refine hn₀ n (le_trans (le_max_left _ _) hn) _
    (valid_addTapes _ (valid_sel _ hD₂ hr hroom₂) _) ?_ _ hsel'
  rw [T_addTapes]
  exact htime₂

/-- **Plain ⟹ network-computable hints are free.** Under `NoCode_TM`: for all constants and all
large `n`, no family of codes `codes h` solves complete exchange on every input at the profile
capacities of `D` when each input `x` uses the code indexed by a *network-computable* hint of
`s ≤ C n w` bits (computed by a hint computation `Pre`, `C₁`, `hx` as in
`noCode_netCover_of_noCode`). With an oracle hint (any function of the input) this is
`RobustNoCode_TM` (`robustNoCode_iff_hint`); so the gap between the plain and the robust target is
exactly "oracle hint versus network-computed hint". -/
theorem noCode_netHint_of_noCode (h : NoCode_TM) (k G c C k₁ c₁ : ℕ) (hG : 1 ≤ G) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
      ∀ (Pre : TSDiagram k₁), Pre.WalksOK → 1 ≤ Pre.T → Pre.T ≤ c₁ * (n * n * entryBits n) →
      ∀ (C₁ : NetCode) (hx : (ℕ × ℕ → ℕ) → (ℕ → Bool) → ℕ) (s : ℕ), s ≤ C * (n * entryBits n) →
      (∀ (x : Fin (n * n * entryBits n) → Bool), ∀ e ∈ Pre.edges (blockSize G n),
        C₁.edgeVal (Pre.edges (blockSize G n))
          (fun y => Pre.visible n (entryBits n) (blockSize G n) y x) e < 2 ^ Pre.profileCap n G e) →
      ∀ (codes : ℕ → NetCode),
        ¬ ∀ x : Fin (n * n * entryBits n) → Bool, D.Solves n G (D.profileCap n G) {x}
          (codes (hx (C₁.inVals (Pre.edges (blockSize G n))
            (fun y => Pre.visible n (entryBits n) (blockSize G n) y x)
              (Pre.nodes (blockSize G n) - 1))
            (Pre.visible n (entryBits n) (blockSize G n) (Pre.nodes (blockSize G n) - 1) x) %
              2 ^ s)) := by
  obtain ⟨n₀, hn₀⟩ := h (k₁ + k + C) G (2 * c₁ * G + c + 4) hG
  refine ⟨max n₀ 1, fun n hn D hD hT Pre hPre hPreT1 hPreT C₁ hx s hs hcap₁ codes hall => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hr : 1 ≤ blockSize G n := one_le_blockSize hG hn1
  have hrG : n * entryBits n ≤ blockSize G n * G := blockSize_mul_ge hG
  have hsB : s ≤ C * (blockSize G n * G) := le_trans hs (Nat.mul_le_mul_left _ hrG)
  obtain ⟨hroom, htime⟩ := concat_room_time Pre D hG hn1 hPreT hT
  have hsol : (addTapes (concatDiagram Pre D (2 * c₁ * n * G + 4) (blockSize G n)) C).Solves n G
      ((addTapes (concatDiagram Pre D (2 * c₁ * n * G + 4) (blockSize G n)) C).profileCap n G)
      Set.univ (concatCode Pre D n G (2 * c₁ * n * G + 4) s C₁ hx codes) := by
    intro x _
    exact solves_profileCap_addTapes (a := C) hr hsB
      (concat_solves_at Pre D C₁ hx codes x hG hn1 hPreT1 hD hroom (hcap₁ x) (hall x)) x
      (Set.mem_singleton x)
  refine hn₀ n (le_trans (le_max_left _ _) hn) _
    (valid_addTapes _ (valid_concat Pre D hPre hD hr hroom) C) ?_ _ hsol
  rw [T_addTapes]
  exact htime

end Transpose.Tape.Impl
