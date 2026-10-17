import Transpose.Tape.PlainRobust.CESelect

/-!
# Syndrome correction: plain ⟹ every code errs in many different ways

Let a code `C` stay within the profile capacities of `D` on every input. Its **error vector** on `x`
is indexed by input positions: bit `d` is `C`'s output bit at the transposed position `tpos d` XOR the
input bit `d` (so it is `C(x)ᵀ ⊕ x`, and it is `0` exactly when `C` is correct on `x`). Suppose the
error vectors take at most `2^{H n w}` values. Fix a check matrix `Φ` with `t` rows and columns
`Φ_d` (`hcol d`). The network `selDiagram D 1 P r L` (one copy of `D`'s walks for run 1, an input
epilogue, a fresh copy for run 2) then corrects `C`:
* **run 1** runs `C`; every output bit `o` equal to `1` adds the column `Φ_{tpos o}` on the spine,
  so the spine accumulates `Φ · C(x)ᵀ` (`outContrib`);
* the **epilogue** sweep adds `Φ_d` for every input bit `d` equal to `1`, each position once on the
  upward pass (`inContrib`, `upStep`), so the spine carries the syndrome `Φ · e(x)`
  (`synState_final`);
* **run 2** runs `C` again and XORs output bit `o` with bit `tpos o` of the error vector decoded from
  the syndrome (`synCode`; correctness `syn_solves_at`, at the per-node blocks plus `t` bits per
  memory edge).

If `Φ` is injective on the possible error vectors, the outputs are `xᵀ`. A random `Φ` with
`t = 2 H n w + 1` rows is injective on `2^{H n w}` vectors (`exists_injective_synF`). The `t` bits
are paid for by `2 H + 1` stationary tapes, so `NoCode_TM` is applied at `2 k + 2 H + 1` tapes and
time constant `(2 c + 2) G + c + 4`. Hence `NoCode_TM` implies that every code within capacity on
every input has more than `2^{H n w}` error vectors (`noCode_fewErrors_of_noCode`). In particular, no
such code gets all but at most `A n` of the `n² w` output bits right on every input
(`noCode_sparseErrors_of_noCode`): for codes within capacity, transposition with `O(n)` wrong bits is
as hard as exact transposition. The same holds for `O(n)` wrong *entries*
(`noCode_sparseEntryErrors_of_noCode`), and for `O(1)` codes of which each input may pick one
(`noCode_fewErrorsCover_of_noCode`: the syndrome-corrected codes are the candidates of a selection).
-/

namespace Transpose.Tape.Impl

open Transpose TSDiagram

/-! ### The syndrome code -/

section SynCode

variable {k : ℕ} (D : TSDiagram k) (n G P t : ℕ) (C : NetCode)
  (hcol : ℕ → (Fin t → ZMod 2)) (corr : (Fin t → ZMod 2) → ℕ → Bool)

/-- The value on an edge with the syndrome stripped off memory edges. -/
noncomputable def synRaw (f : ℕ × ℕ → ℕ) (e : ℕ × ℕ) : ℕ :=
  if e.2 = e.1 + 1 then f e / 2 ^ t else f e

/-- `C`'s values into a run-1 node. -/
noncomputable def inSyn1 (f : ℕ × ℕ → ℕ) : ℕ × ℕ → ℕ :=
  fun e' => if e' ∈ D.edges (blockSize G n) then synRaw t f e' else 0

/-- `C`'s values into a run-2 node, indexed by `D`'s edges. -/
noncomputable def inSyn2 (f : ℕ × ℕ → ℕ) : ℕ × ℕ → ℕ :=
  fun e'' => if e'' ∈ D.edges (blockSize G n) then synRaw t f (P + e''.1, P + e''.2) else 0

/-- The syndrome arriving at node `u` on its memory edge. -/
noncomputable def synIn (u : ℕ) (f : ℕ × ℕ → ℕ) : Fin t → ZMod 2 :=
  decV (f (u - 1, u) % 2 ^ t)

/-- The contribution of the output bits produced at node `u`. -/
noncomputable def outContrib (u : ℕ) (out : ℕ → Bool) : Fin t → ZMod 2 :=
  ∑ o ∈ (Finset.range (n * n * entryBits n)).filter (fun o => D.outNode (blockSize G n) o = u),
    (if out o then hcol (tpos n (entryBits n) o) else 0)

/-- The step at which the upward pass of the epilogue reads input position `d`. -/
def upStep (d : ℕ) : ℕ :=
  D.nodes (blockSize G n) * blockSize G n +
    (D.inp (D.nodes (blockSize G n) * blockSize G n)).natAbs + d

/-- The contribution of the input positions read upward at node `u`. -/
noncomputable def inContrib (u : ℕ) (v : ℕ → Bool) : Fin t → ZMod 2 :=
  ∑ d ∈ (Finset.range (n * n * entryBits n)).filter
      (fun d => upStep D n G d / blockSize G n = u), (if v d then hcol d else 0)

/-- The syndrome leaving run-1 node `u`. -/
noncomputable def synOut1 (u : ℕ) (f : ℕ × ℕ → ℕ) (v : ℕ → Bool) : Fin t → ZMod 2 :=
  (if u = 0 then 0 else synIn t u f) +
    outContrib D n G t hcol u (fun o => C.dec o (inSyn1 D n G t f) (maskRows D n G u v))

/-- **The syndrome code** on `selDiagram D 1 P r L`. -/
noncomputable def synCode : NetCode where
  enc e f v :=
    if e.1 < D.nodes (blockSize G n) then
      (if e ∈ D.edges (blockSize G n) then
        (if e.2 = e.1 + 1 then
          encV (synOut1 D n G t C hcol e.1 f v) +
            2 ^ t * C.enc e (inSyn1 D n G t f) (maskRows D n G e.1 v)
        else C.enc e (inSyn1 D n G t f) (maskRows D n G e.1 v))
      else if e.2 = e.1 + 1 then encV (synOut1 D n G t C hcol e.1 f v) else 0)
    else if e.1 < P then
      (if e.2 = e.1 + 1 then encV (synIn t e.1 f + inContrib D n G t hcol e.1 v) else 0)
    else
      (if (e.1 - P, e.2 - P) ∈ D.edges (blockSize G n) then
        (if e.2 = e.1 + 1 then
          encV (synIn t e.1 f) + 2 ^ t * C.enc (e.1 - P, e.2 - P) (inSyn2 D n G P t f) v
        else C.enc (e.1 - P, e.2 - P) (inSyn2 D n G P t f) v)
      else 0)
  dec o f v := xor (C.dec o (inSyn2 D n G P t f) v)
    (corr (synIn t (P + D.outNode (blockSize G n) o) f) (tpos n (entryBits n) o))

variable (e : ℕ × ℕ) (f : ℕ × ℕ → ℕ) (v : ℕ → Bool)

theorem synCode_run1_D (h1 : e.1 < D.nodes (blockSize G n)) (hE : e ∈ D.edges (blockSize G n)) :
    (synCode D n G P t C hcol corr).enc e f v =
      if e.2 = e.1 + 1 then encV (synOut1 D n G t C hcol e.1 f v) +
        2 ^ t * C.enc e (inSyn1 D n G t f) (maskRows D n G e.1 v)
      else C.enc e (inSyn1 D n G t f) (maskRows D n G e.1 v) := by
  show (if e.1 < D.nodes (blockSize G n) then _ else _) = _
  rw [ite_eq_left h1, ite_eq_left hE]

theorem synCode_run1_notD (h1 : e.1 < D.nodes (blockSize G n))
    (hE : e ∉ D.edges (blockSize G n)) :
    (synCode D n G P t C hcol corr).enc e f v =
      if e.2 = e.1 + 1 then encV (synOut1 D n G t C hcol e.1 f v) else 0 := by
  show (if e.1 < D.nodes (blockSize G n) then _ else _) = _
  rw [ite_eq_left h1, ite_eq_right hE]

theorem synCode_epi (h1 : ¬ e.1 < D.nodes (blockSize G n)) (h2 : e.1 < P) :
    (synCode D n G P t C hcol corr).enc e f v =
      if e.2 = e.1 + 1 then encV (synIn t e.1 f + inContrib D n G t hcol e.1 v) else 0 := by
  show (if e.1 < D.nodes (blockSize G n) then _ else _) = _
  rw [ite_eq_right h1, ite_eq_left h2]

theorem synCode_run2 (h1 : ¬ e.1 < D.nodes (blockSize G n)) (h2 : ¬ e.1 < P) :
    (synCode D n G P t C hcol corr).enc e f v =
      if (e.1 - P, e.2 - P) ∈ D.edges (blockSize G n) then
        (if e.2 = e.1 + 1 then
          encV (synIn t e.1 f) + 2 ^ t * C.enc (e.1 - P, e.2 - P) (inSyn2 D n G P t f) v
        else C.enc (e.1 - P, e.2 - P) (inSyn2 D n G P t f) v)
      else 0 := by
  show (if e.1 < D.nodes (blockSize G n) then _ else _) = _
  rw [ite_eq_right h1, ite_eq_right h2]

theorem outContrib_congr (u : ℕ) {out out' : ℕ → Bool}
    (h : ∀ o, D.outNode (blockSize G n) o = u → out o = out' o) :
    outContrib D n G t hcol u out = outContrib D n G t hcol u out' := by
  unfold outContrib
  apply Finset.sum_congr rfl
  intro o ho
  rw [Finset.mem_filter] at ho
  rw [h o ho.2]

end SynCode

/-! ### The intended syndrome -/

section SynState

variable {k : ℕ} (D : TSDiagram k) (n G P t : ℕ) (C : NetCode) (hcol : ℕ → (Fin t → ZMod 2))
  (x : Fin (n * n * entryBits n) → Bool)

/-- `C`'s output bit at position `o`, in `D`, on input `x`. -/
noncomputable def outC (o : ℕ) : Bool :=
  C.outVal (D.edges (blockSize G n)) (fun y => D.visible n (entryBits n) (blockSize G n) y x)
    (D.outNode (blockSize G n) o) o

/-- The intended syndrome after node `u`: output contributions in run 1, input contributions in the
epilogue. -/
noncomputable def synState : ℕ → (Fin t → ZMod 2)
  | 0 => outContrib D n G t hcol 0 (outC D n G C x)
  | u + 1 => synState u + (if u + 1 < D.nodes (blockSize G n) then
      outContrib D n G t hcol (u + 1) (outC D n G C x)
    else inContrib D n G t hcol (u + 1)
      ((selDiagram D 1 P (blockSize G n) (n * n * entryBits n)).visible n (entryBits n)
        (blockSize G n) (u + 1) x))

end SynState

/-! ### Run 1 and the epilogue -/

/-- **Run 1 and the epilogue.** Into a run-1 node the values on `D`'s edges are `C`'s; the memory
edge into every node `u ≤ P` carries the intended syndrome of node `u - 1` in its low bits. -/
theorem syn_main {k : ℕ} (D : TSDiagram k) {n G P t : ℕ} (C : NetCode)
    (hcol : ℕ → (Fin t → ZMod 2)) (corr : (Fin t → ZMod 2) → ℕ → Bool)
    (x : Fin (n * n * entryBits n) → Bool) (hG : 1 ≤ G) (hn : 1 ≤ n)
    (hD : D.Valid (n * n * entryBits n))
    (hP : SelRoom D P (blockSize G n) (n * n * entryBits n)) :
    ∀ u, u ≤ P →
      (u < D.nodes (blockSize G n) →
        inSyn1 D n G t ((synCode D n G P t C hcol corr).inVals
          ((selDiagram D 1 P (blockSize G n) (n * n * entryBits n)).edges (blockSize G n))
          (fun y => (selDiagram D 1 P (blockSize G n) (n * n * entryBits n)).visible n
            (entryBits n) (blockSize G n) y x) u) =
        C.inVals (D.edges (blockSize G n))
          (fun y => D.visible n (entryBits n) (blockSize G n) y x) u) ∧
      (1 ≤ u → (synCode D n G P t C hcol corr).inVals
          ((selDiagram D 1 P (blockSize G n) (n * n * entryBits n)).edges (blockSize G n))
          (fun y => (selDiagram D 1 P (blockSize G n) (n * n * entryBits n)).visible n
            (entryBits n) (blockSize G n) y x) u (u - 1, u) % 2 ^ t =
        encV (synState D n G P t C hcol x (u - 1))) := by
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
  refine ⟨fun huN => ?_, fun hu1 => ?_⟩
  · -- the values into a run-1 node
    funext e'
    show (if e' ∈ D.edges (blockSize G n) then synRaw t
      ((synCode D n G P t C hcol corr).inVals
        ((selDiagram D 1 P (blockSize G n) (n * n * entryBits n)).edges (blockSize G n))
        (fun y => (selDiagram D 1 P (blockSize G n) (n * n * entryBits n)).visible n
          (entryBits n) (blockSize G n) y x) u) e' else 0) = _
    rw [inVals_eq C]
    by_cases hc : e' ∈ D.edges (blockSize G n) ∧ e'.2 = u ∧ e'.1 < u
    · rw [ite_eq_left hc.1, ite_eq_left hc]
      have hE : e' ∈ (selDiagram D 1 P (blockSize G n) (n * n * entryBits n)).edges
          (blockSize G n) := edges_sel_run1 D hr le_rfl hc.1
      have h1 : e'.1 < D.nodes (blockSize G n) := by omega
      have hA := (ih e'.1 (by omega) (by omega)).1 h1
      have hval : (synCode D n G P t C hcol corr).inVals
          ((selDiagram D 1 P (blockSize G n) (n * n * entryBits n)).edges (blockSize G n))
          (fun y => (selDiagram D 1 P (blockSize G n) (n * n * entryBits n)).visible n
            (entryBits n) (blockSize G n) y x) u e' =
          (synCode D n G P t C hcol corr).enc e' ((synCode D n G P t C hcol corr).inVals
            ((selDiagram D 1 P (blockSize G n) (n * n * entryBits n)).edges (blockSize G n))
            (fun y => (selDiagram D 1 P (blockSize G n) (n * n * entryBits n)).visible n
              (entryBits n) (blockSize G n) y x) e'.1)
            ((selDiagram D 1 P (blockSize G n) (n * n * entryBits n)).visible n
              (entryBits n) (blockSize G n) e'.1 x) := by
        rw [inVals_eq, ite_eq_left ⟨hE, hc.2⟩]
      unfold synRaw
      rw [hval, synCode_run1_D D n G P t C hcol corr e' _ _ h1 hc.1]
      by_cases hm : e'.2 = e'.1 + 1
      · rw [ite_eq_left hm, ite_eq_left hm, unpack, hA, maskRows_sel D n G 1 P hr]
      · rw [ite_eq_right hm, ite_eq_right hm, hA, maskRows_sel D n G 1 P hr]
    · by_cases hE' : e' ∈ D.edges (blockSize G n)
      · rw [ite_eq_left hE', ite_eq_right hc]
        have h0 : (synCode D n G P t C hcol corr).inVals
            ((selDiagram D 1 P (blockSize G n) (n * n * entryBits n)).edges (blockSize G n))
            (fun y => (selDiagram D 1 P (blockSize G n) (n * n * entryBits n)).visible n
              (entryBits n) (blockSize G n) y x) u e' = 0 := by
          rw [inVals_eq, ite_eq_right]
          intro h; exact hc ⟨hE', h.2⟩
        unfold synRaw
        rw [h0]
        simp
      · rw [ite_eq_right hE', ite_eq_right (fun h => hE' h.1)]
  · -- the syndrome on the memory edge into `u`
    have hmemE : (u - 1, u) ∈ (selDiagram D 1 P (blockSize G n) (n * n * entryBits n)).edges
        (blockSize G n) := by
      apply Finset.mem_union_left
      rw [mem_memEdges, nodes_sel D hr]
      simp only
      omega
    rw [inVals_eq, ite_eq_left ⟨hmemE, rfl, by simp only; omega⟩]
    by_cases h1 : u - 1 < D.nodes (blockSize G n)
    · -- from a run-1 node
      obtain ⟨ihA, ihB⟩ := ih (u - 1) (by omega) (by omega)
      have hout : synOut1 D n G t C hcol (u - 1) ((synCode D n G P t C hcol corr).inVals
          ((selDiagram D 1 P (blockSize G n) (n * n * entryBits n)).edges (blockSize G n))
          (fun y => (selDiagram D 1 P (blockSize G n) (n * n * entryBits n)).visible n
            (entryBits n) (blockSize G n) y x) (u - 1))
          ((selDiagram D 1 P (blockSize G n) (n * n * entryBits n)).visible n
            (entryBits n) (blockSize G n) (u - 1) x) = synState D n G P t C hcol x (u - 1) := by
        unfold synOut1
        rw [ihA h1, maskRows_sel D n G 1 P hr]
        have hcon : outContrib D n G t hcol (u - 1)
            (fun o => C.dec o (C.inVals (D.edges (blockSize G n))
              (fun y => D.visible n (entryBits n) (blockSize G n) y x) (u - 1))
              (D.visible n (entryBits n) (blockSize G n) (u - 1) x)) =
            outContrib D n G t hcol (u - 1) (outC D n G C x) := by
          apply outContrib_congr
          intro o ho
          unfold outC NetCode.outVal
          rw [ho]
        rw [hcon]
        rcases Nat.eq_zero_or_pos (u - 1) with h0 | hpos
        · rw [ite_eq_left h0, h0, zero_add]
          rfl
        · rw [ite_eq_right (by omega)]
          have hin : synIn t (u - 1) ((synCode D n G P t C hcol corr).inVals
              ((selDiagram D 1 P (blockSize G n) (n * n * entryBits n)).edges (blockSize G n))
              (fun y => (selDiagram D 1 P (blockSize G n) (n * n * entryBits n)).visible n
                (entryBits n) (blockSize G n) y x) (u - 1)) =
              synState D n G P t C hcol x (u - 1 - 1) := by
            unfold synIn
            rw [ihB (by omega), decV_encV]
          rw [hin]
          obtain ⟨m, hm⟩ : ∃ m, u - 1 = m + 1 := ⟨u - 2, by omega⟩
          rw [hm] at h1 ⊢
          simp only [synState, ite_eq_left h1, Nat.add_sub_cancel]
      by_cases hE : (u - 1, u) ∈ D.edges (blockSize G n)
      · rw [synCode_run1_D D n G P t C hcol corr _ _ _ h1 hE, ite_eq_left (by simp only; omega),
          Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (encV_lt _), hout]
      · rw [synCode_run1_notD D n G P t C hcol corr _ _ _ h1 hE, ite_eq_left (by simp only; omega),
          Nat.mod_eq_of_lt (encV_lt _), hout]
    · -- from an epilogue node
      obtain ⟨-, ihB⟩ := ih (u - 1) (by omega) (by omega)
      rw [synCode_epi D n G P t C hcol corr _ _ _ h1 (by simp only; omega),
        ite_eq_left (by simp only; omega), Nat.mod_eq_of_lt (encV_lt _)]
      have hin : synIn t (u - 1) ((synCode D n G P t C hcol corr).inVals
          ((selDiagram D 1 P (blockSize G n) (n * n * entryBits n)).edges (blockSize G n))
          (fun y => (selDiagram D 1 P (blockSize G n) (n * n * entryBits n)).visible n
            (entryBits n) (blockSize G n) y x) (u - 1)) =
          synState D n G P t C hcol x (u - 1 - 1) := by
        unfold synIn
        rw [ihB (by omega), decV_encV]
      simp only at hin ⊢
      rw [hin]
      obtain ⟨m, hm⟩ : ∃ m, u - 1 = m + 1 := ⟨u - 2, by omega⟩
      rw [hm] at h1 ⊢
      simp only [synState, ite_eq_right h1, Nat.add_sub_cancel]

/-! ### Run 2 -/

/-- **Run 2.** Every memory edge into run 2 carries the final syndrome, and the values into a run-2
node are `C`'s values in `D`. -/
theorem syn_run2 {k : ℕ} (D : TSDiagram k) {n G P t : ℕ} (C : NetCode)
    (hcol : ℕ → (Fin t → ZMod 2)) (corr : (Fin t → ZMod 2) → ℕ → Bool)
    (x : Fin (n * n * entryBits n) → Bool) (hG : 1 ≤ G) (hn : 1 ≤ n)
    (hD : D.Valid (n * n * entryBits n))
    (hP : SelRoom D P (blockSize G n) (n * n * entryBits n)) :
    ∀ u', u' < D.nodes (blockSize G n) →
      (synCode D n G P t C hcol corr).inVals
          ((selDiagram D 1 P (blockSize G n) (n * n * entryBits n)).edges (blockSize G n))
          (fun y => (selDiagram D 1 P (blockSize G n) (n * n * entryBits n)).visible n
            (entryBits n) (blockSize G n) y x) (P + u') (P + u' - 1, P + u') % 2 ^ t =
        encV (synState D n G P t C hcol x (P - 1)) ∧
      inSyn2 D n G P t ((synCode D n G P t C hcol corr).inVals
          ((selDiagram D 1 P (blockSize G n) (n * n * entryBits n)).edges (blockSize G n))
          (fun y => (selDiagram D 1 P (blockSize G n) (n * n * entryBits n)).visible n
            (entryBits n) (blockSize G n) y x) (P + u')) =
        C.inVals (D.edges (blockSize G n)) (fun y => D.visible n (entryBits n) (blockSize G n) y x)
          u' := by
  have hr : 1 ≤ blockSize G n := one_le_blockSize hG hn
  have hPN := selRoom_nodes hr hP
  intro u'
  induction u' using Nat.strong_induction_on with
  | _ u' ih =>
  intro hu'
  have hstate : (synCode D n G P t C hcol corr).inVals
      ((selDiagram D 1 P (blockSize G n) (n * n * entryBits n)).edges (blockSize G n))
      (fun y => (selDiagram D 1 P (blockSize G n) (n * n * entryBits n)).visible n
        (entryBits n) (blockSize G n) y x) (P + u') (P + u' - 1, P + u') % 2 ^ t =
      encV (synState D n G P t C hcol x (P - 1)) := by
    rcases Nat.eq_zero_or_pos u' with h0 | hpos
    · subst h0
      simp only [Nat.add_zero]
      exact (syn_main D C hcol corr x hG hn hD hP P le_rfl).2 (by omega)
    · have hDmem : (u' - 1, u') ∈ D.edges (blockSize G n) := by
        apply Finset.mem_union_left
        rw [mem_memEdges]
        simp only
        omega
      have hmemE : (P + u' - 1, P + u') ∈
          (selDiagram D 1 P (blockSize G n) (n * n * entryBits n)).edges (blockSize G n) := by
        have := (mem_edges_sel_add D (K := 1) (P := P) hr hD (by omega) (u' - 1) u').2 hDmem
        rwa [show P + (u' - 1) = P + u' - 1 by omega] at this
      rw [inVals_eq, ite_eq_left ⟨hmemE, rfl, by simp only; omega⟩,
        synCode_run2 D n G P t C hcol corr _ _ _ (by simp only; omega) (by simp only; omega)]
      simp only
      rw [show P + u' - 1 - P = u' - 1 by omega, Nat.add_sub_cancel_left, ite_eq_left hDmem,
        ite_eq_left (by omega), Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (encV_lt _)]
      congr 1
      unfold synIn
      have h := (ih (u' - 1) (by omega) (by omega)).1
      rw [show P + (u' - 1) = P + u' - 1 by omega] at h
      rw [h, decV_encV]
  refine ⟨hstate, ?_⟩
  funext e''
  show (if e'' ∈ D.edges (blockSize G n) then synRaw t ((synCode D n G P t C hcol corr).inVals
      ((selDiagram D 1 P (blockSize G n) (n * n * entryBits n)).edges (blockSize G n))
      (fun y => (selDiagram D 1 P (blockSize G n) (n * n * entryBits n)).visible n
        (entryBits n) (blockSize G n) y x) (P + u')) (P + e''.1, P + e''.2) else 0) = _
  rw [inVals_eq C]
  by_cases hc : e'' ∈ D.edges (blockSize G n) ∧ e''.2 = u' ∧ e''.1 < u'
  · rw [ite_eq_left hc.1, ite_eq_left hc]
    have hE : (P + e''.1, P + e''.2) ∈
        (selDiagram D 1 P (blockSize G n) (n * n * entryBits n)).edges (blockSize G n) :=
      (mem_edges_sel_add D hr hD (by omega) _ _).2 hc.1
    have hval : (synCode D n G P t C hcol corr).inVals
        ((selDiagram D 1 P (blockSize G n) (n * n * entryBits n)).edges (blockSize G n))
        (fun y => (selDiagram D 1 P (blockSize G n) (n * n * entryBits n)).visible n
          (entryBits n) (blockSize G n) y x) (P + u') (P + e''.1, P + e''.2) =
        (synCode D n G P t C hcol corr).enc (P + e''.1, P + e''.2)
          ((synCode D n G P t C hcol corr).inVals
            ((selDiagram D 1 P (blockSize G n) (n * n * entryBits n)).edges (blockSize G n))
            (fun y => (selDiagram D 1 P (blockSize G n) (n * n * entryBits n)).visible n
              (entryBits n) (blockSize G n) y x) (P + e''.1))
          ((selDiagram D 1 P (blockSize G n) (n * n * entryBits n)).visible n
            (entryBits n) (blockSize G n) (P + e''.1) x) := by
      rw [inVals_eq, ite_eq_left ⟨hE, by simp only; omega, by simp only; omega⟩]
    obtain ⟨-, ihI⟩ := ih e''.1 hc.2.2 (by omega)
    unfold synRaw
    rw [hval, synCode_run2 D n G P t C hcol corr _ _ _ (by simp only; omega) (by simp only; omega)]
    simp only [Nat.add_sub_cancel_left]
    rw [ite_eq_left (hc.1 : (e''.1, e''.2) ∈ D.edges (blockSize G n)), ihI,
      visible_sel_add D hr hP]
    by_cases hm : e''.2 = e''.1 + 1
    · rw [ite_eq_left (show P + e''.2 = P + e''.1 + 1 by omega),
        ite_eq_left (show P + e''.2 = P + e''.1 + 1 by omega), unpack]
    · rw [ite_eq_right (show ¬ P + e''.2 = P + e''.1 + 1 by omega),
        ite_eq_right (show ¬ P + e''.2 = P + e''.1 + 1 by omega)]
  · by_cases hE' : e'' ∈ D.edges (blockSize G n)
    · rw [ite_eq_left hE', ite_eq_right hc]
      have h0 : (synCode D n G P t C hcol corr).inVals
          ((selDiagram D 1 P (blockSize G n) (n * n * entryBits n)).edges (blockSize G n))
          (fun y => (selDiagram D 1 P (blockSize G n) (n * n * entryBits n)).visible n
            (entryBits n) (blockSize G n) y x) (P + u') (P + e''.1, P + e''.2) = 0 := by
        rw [inVals_eq, ite_eq_right]
        intro h
        apply hc
        refine ⟨hE', ?_, ?_⟩ <;> simp only at h <;> omega
      unfold synRaw
      rw [h0]
      simp
    · rw [ite_eq_right hE', ite_eq_right (fun h => hE' h.1)]

/-! ### The final syndrome -/

/-- The syndrome of a bit vector indexed by input positions `< L`. -/
noncomputable def syndrome (L t : ℕ) (hcol : ℕ → (Fin t → ZMod 2)) (e : ℕ → Bool) : Fin t → ZMod 2 :=
  ∑ d ∈ Finset.range L, (if e d then hcol d else 0)

theorem zmod2_vec_add_self {t : ℕ} (h : Fin t → ZMod 2) : h + h = 0 := by
  funext i
  simp only [Pi.add_apply, Pi.zero_apply]
  generalize h i = a
  fin_cases a <;> decide

theorem ite_add_ite_xor {t : ℕ} (a b : Bool) (h : Fin t → ZMod 2) :
    (if a then h else 0) + (if b then h else 0) = if xor a b then h else 0 := by
  cases a <;> cases b <;> simp [zmod2_vec_add_self]

section Final

variable {k : ℕ} (D : TSDiagram k) {n G P t : ℕ} (C : NetCode) (hcol : ℕ → (Fin t → ZMod 2))
  (x : Fin (n * n * entryBits n) → Bool)

/-- The intended syndrome is the sum of the contributions of the nodes so far. -/
theorem synState_sum (hN : 1 ≤ D.nodes (blockSize G n)) : ∀ u,
    synState D n G P t C hcol x u = ∑ u' ∈ Finset.range (u + 1),
      (if u' < D.nodes (blockSize G n) then outContrib D n G t hcol u' (outC D n G C x)
      else inContrib D n G t hcol u'
        ((selDiagram D 1 P (blockSize G n) (n * n * entryBits n)).visible n (entryBits n)
          (blockSize G n) u' x)) := by
  intro u
  induction u with
  | zero =>
    simp only [synState]
    rw [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, ite_eq_left (by omega)]
  | succ u ih =>
    rw [Finset.sum_range_succ, ← ih]
    rfl

/-- The upward pass reads position `d` at its step. -/
theorem sel_inp_upStep (hr : 1 ≤ blockSize G n) (hD : D.Valid (n * n * entryBits n))
    (hP : SelRoom D P (blockSize G n) (n * n * entryBits n)) {d : ℕ}
    (hd : d < n * n * entryBits n) :
    (selDiagram D 1 P (blockSize G n) (n * n * entryBits n)).inp (upStep D n G d) = d ∧
      D.nodes (blockSize G n) * blockSize G n ≤ upStep D n G d ∧
      upStep D n G d < P * blockSize G n := by
  have hp₀ : (D.inp (D.nodes (blockSize G n) * blockSize G n)).natAbs ≤
      D.nodes (blockSize G n) * blockSize G n := by
    have := unitSteps_dist hD.2.2.1 (Nat.zero_le (D.nodes (blockSize G n) * blockSize G n))
    rw [hD.2.1] at this
    simp only [sub_zero, Int.abs_eq_natAbs] at this
    omega
  unfold SelRoom at hP
  refine ⟨?_, by unfold upStep; omega, by unfold upStep; omega⟩
  show (if upStep D n G d < D.nodes (blockSize G n) * blockSize G n then _
    else if upStep D n G d < P * blockSize G n then epiWalk _ _ (upStep D n G d -
      D.nodes (blockSize G n) * blockSize G n) else _) = _
  rw [ite_eq_right (by unfold upStep; omega), ite_eq_left (by unfold upStep; omega)]
  have e : upStep D n G d - D.nodes (blockSize G n) * blockSize G n =
      (D.inp (D.nodes (blockSize G n) * blockSize G n)).natAbs + d := by unfold upStep; omega
  rw [e, epiWalk_visit _ hd]

/-- At the node where the upward pass reads position `d`, the visible bit at `d` is `x d`. -/
theorem visible_upStep (hr : 1 ≤ blockSize G n) (hD : D.Valid (n * n * entryBits n))
    (hP : SelRoom D P (blockSize G n) (n * n * entryBits n)) {d : ℕ}
    (hd : d < n * n * entryBits n) :
    (selDiagram D 1 P (blockSize G n) (n * n * entryBits n)).visible n (entryBits n)
      (blockSize G n) (upStep D n G d / blockSize G n) x d = x ⟨d, hd⟩ := by
  classical
  obtain ⟨hin, hge, hlt⟩ := sel_inp_upStep D hr hD hP hd
  have hw : 1 ≤ entryBits n := by unfold entryBits; omega
  have hnw : 0 < n * entryBits n := by
    rcases Nat.eq_zero_or_pos (n * entryBits n) with h0 | h0
    · rw [Nat.mul_assoc, h0, Nat.mul_zero] at hd; omega
    · exact h0
  have hrow : d / (n * entryBits n) ∈ (selDiagram D 1 P (blockSize G n)
      (n * n * entryBits n)).rowsAt n (entryBits n) (blockSize G n)
        (upStep D n G d / blockSize G n) := by
    simp only [TSDiagram.rowsAt, Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, upStep D n G d, mem_slotOf_div hr (by show _ < P * blockSize G n + D.T; omega),
      ?_, ?_⟩
    · rw [Nat.div_lt_iff_lt_mul hnw]
      have : n * n * entryBits n = n * (n * entryBits n) := by ring
      omega
    · rw [hin]
      have := Nat.div_mul_le_self d (n * entryBits n)
      have e : d / (n * entryBits n) * n * entryBits n =
          d / (n * entryBits n) * (n * entryBits n) := by ring
      rw [e]; exact_mod_cast this
    · rw [hin]
      have := Nat.lt_div_mul_add hnw (a := d)
      have e : (d / (n * entryBits n) + 1) * n * entryBits n =
          d / (n * entryBits n) * (n * entryBits n) + n * entryBits n := by ring
      rw [e]; exact_mod_cast this
  simp only [TSDiagram.visible, dite_eq_left hd, ite_eq_left hrow]

/-- **The final syndrome is the syndrome of the error vector.** -/
theorem synState_final (hG : 1 ≤ G) (hn : 1 ≤ n) (hD : D.Valid (n * n * entryBits n))
    (hP : SelRoom D P (blockSize G n) (n * n * entryBits n)) :
    synState D n G P t C hcol x (P - 1) = syndrome (n * n * entryBits n) t hcol
      (fun d => xor (outC D n G C x (tpos n (entryBits n) d)) (xbits x d)) := by
  have hr : 1 ≤ blockSize G n := one_le_blockSize hG hn
  have hPN := selRoom_nodes hr hP
  have hL1 : 1 ≤ n * n * entryBits n :=
    Nat.one_le_iff_ne_zero.2 (by unfold entryBits; positivity)
  have hN : 1 ≤ D.nodes (blockSize G n) :=
    (numSlots_spec hr).2 (by have := one_le_T hD hL1; simp only [Nat.zero_mul]; omega)
  rw [synState_sum D C hcol x hN (P - 1), show P - 1 + 1 = P by omega,
    ← Finset.sum_range_add_sum_Ico _ (show D.nodes (blockSize G n) ≤ P by omega)]
  have h1 : ∑ u' ∈ Finset.range (D.nodes (blockSize G n)),
      (if u' < D.nodes (blockSize G n) then outContrib D n G t hcol u' (outC D n G C x)
      else inContrib D n G t hcol u'
        ((selDiagram D 1 P (blockSize G n) (n * n * entryBits n)).visible n (entryBits n)
          (blockSize G n) u' x)) =
      ∑ o ∈ Finset.range (n * n * entryBits n),
        (if outC D n G C x o then hcol (tpos n (entryBits n) o) else 0) := by
    rw [Finset.sum_congr rfl (fun u' hu' => ite_eq_left (Finset.mem_range.1 hu'))]
    unfold outContrib
    exact Finset.sum_fiberwise_of_maps_to (fun o _ => Finset.mem_range.2 (outNode_lt hD hr hL1 o)) _
  have h2 : ∑ u' ∈ Finset.Ico (D.nodes (blockSize G n)) P,
      (if u' < D.nodes (blockSize G n) then outContrib D n G t hcol u' (outC D n G C x)
      else inContrib D n G t hcol u'
        ((selDiagram D 1 P (blockSize G n) (n * n * entryBits n)).visible n (entryBits n)
          (blockSize G n) u' x)) =
      ∑ d ∈ Finset.range (n * n * entryBits n), (if xbits x d then hcol d else 0) := by
    rw [Finset.sum_congr rfl (fun u' hu' => ite_eq_right (by
      have := (Finset.mem_Ico.1 hu').1; omega))]
    unfold inContrib
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.range (n * n * entryBits n))
      (t := Finset.Ico (D.nodes (blockSize G n)) P) (g := fun d => upStep D n G d / blockSize G n)
      (fun d hd => by
        obtain ⟨-, hge, hlt⟩ := sel_inp_upStep D hr hD hP (Finset.mem_range.1 hd)
        rw [Finset.mem_Ico]
        exact ⟨(Nat.le_div_iff_mul_le (by omega)).2 hge, (Nat.div_lt_iff_lt_mul (by omega)).2 hlt⟩)]
    apply Finset.sum_congr rfl
    intro u' _
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.mem_filter] at hd
    rw [← hd.2, visible_upStep D x hr hD hP (Finset.mem_range.1 hd.1)]
    simp only [xbits, dite_eq_left (Finset.mem_range.1 hd.1)]
  rw [h1, h2]
  -- reindex the outputs by input positions, and add
  have h3 : ∑ o ∈ Finset.range (n * n * entryBits n),
      (if outC D n G C x o then hcol (tpos n (entryBits n) o) else 0) =
      ∑ d ∈ Finset.range (n * n * entryBits n),
        (if outC D n G C x (tpos n (entryBits n) d) then hcol d else 0) := by
    apply Finset.sum_nbij' (tpos n (entryBits n)) (tpos n (entryBits n))
    · intro o ho; exact Finset.mem_range.2 (tpos_lt (Finset.mem_range.1 ho))
    · intro d hd; exact Finset.mem_range.2 (tpos_lt (Finset.mem_range.1 hd))
    · intro o ho; exact tpos_tpos (Finset.mem_range.1 ho)
    · intro d hd; exact tpos_tpos (Finset.mem_range.1 hd)
    · intro o ho; rw [tpos_tpos (Finset.mem_range.1 ho)]
  rw [h3, ← Finset.sum_add_distrib]
  unfold syndrome
  apply Finset.sum_congr rfl
  intro d _
  exact ite_add_ite_xor _ _ _

end Final

/-! ### The syndrome network solves the input -/

/-- **Syndrome correction solves the input.** Let `C` stay within the profile capacities of `D` on
`x`, and let `corr` recover the error vector `e(x)` (output position `tpos d` against input bit `d`)
from its syndrome. Then the syndrome code solves complete exchange on `x`, on `selDiagram D 1 P r L`,
at its per-node blocks plus `t` bits per memory edge. -/
theorem syn_solves_at {k : ℕ} (D : TSDiagram k) {n G P t : ℕ} (C : NetCode)
    (hcol : ℕ → (Fin t → ZMod 2)) (corr : (Fin t → ZMod 2) → ℕ → Bool)
    (x : Fin (n * n * entryBits n) → Bool) (hG : 1 ≤ G) (hn : 1 ≤ n)
    (hD : D.Valid (n * n * entryBits n))
    (hP : SelRoom D P (blockSize G n) (n * n * entryBits n))
    (hcap : ∀ e ∈ D.edges (blockSize G n),
      C.edgeVal (D.edges (blockSize G n)) (fun y => D.visible n (entryBits n) (blockSize G n) y x) e <
        2 ^ D.profileCap n G e)
    (hcorr : ∀ d < n * n * entryBits n,
      corr (syndrome (n * n * entryBits n) t hcol
        (fun d => xor (outC D n G C x (tpos n (entryBits n) d)) (xbits x d))) d =
        xor (outC D n G C x (tpos n (entryBits n) d)) (xbits x d)) :
    (selDiagram D 1 P (blockSize G n) (n * n * entryBits n)).Solves n G
      ((selDiagram D 1 P (blockSize G n) (n * n * entryBits n)).blockCap n G
        (fun y => ∑ i, (pairRes (blockSize G n)
          ((selDiagram D 1 P (blockSize G n) (n * n * entryBits n)).work i)
          (selDiagram D 1 P (blockSize G n) (n * n * entryBits n)).T y).card) t)
      {x} (synCode D n G P t C hcol corr) := by
  intro x' hx'
  rw [Set.mem_singleton_iff] at hx'
  subst hx'
  have hr : 1 ≤ blockSize G n := one_le_blockSize hG hn
  have hPN := selRoom_nodes hr hP
  have hL1 : 1 ≤ n * n * entryBits n :=
    Nat.one_le_iff_ne_zero.2 (by unfold entryBits; positivity)
  have hT : 1 ≤ D.T := one_le_T hD hL1
  have hmain := syn_main D C hcol corr x' hG hn hD hP
  have hrun2 := syn_run2 D C hcol corr x' hG hn hD hP
  refine ⟨fun e he => ?_, fun d hd => ?_⟩
  · -- capacities
    have hlt := edges_fst_lt _ e he
    have hEl := edges_lt _ e he
    rw [nodes_sel D hr] at hEl
    simp only [NetCode.edgeVal]
    by_cases h1 : e.1 < D.nodes (blockSize G n)
    · have hin1 := (hmain e.1 (by omega)).1 h1
      by_cases hE : e ∈ D.edges (blockSize G n)
      · rw [synCode_run1_D D n G P t C hcol corr e _ _ h1 hE, hin1,
          maskRows_sel D n G 1 P hr e.1 x']
        have hc := hcap e hE
        simp only [NetCode.edgeVal] at hc
        by_cases hm : e.2 = e.1 + 1
        · rw [ite_eq_left hm, blockCap_mem _ (mem_memEdges_of_edges _ he hm)]
          have hmD := mem_memEdges_of_edges D hE hm
          have hcapD : D.profileCap n G e =
              (∑ i, (pairRes (blockSize G n) (D.work i) D.T e.1).card) * (blockSize G n * G) := by
            unfold TSDiagram.profileCap; rw [blockCap_mem D hmD, Nat.add_zero]
          have hres := resSum_sel_run1 D (K := 1) (P := P) (L := n * n * entryBits n) hr e.1
          rw [one_mul] at hres
          refine lt_of_lt_of_le (pack_state_lt (encV_lt _) hc) (Nat.pow_le_pow_right (by norm_num) ?_)
          rw [hcapD]
          exact Nat.add_le_add_right (Nat.mul_le_mul_right _ hres) _
        · rw [ite_eq_right hm]
          have hcD := mem_chordEdges_of_edges D hE hm
          rw [blockCap_chord _ (mem_chordEdges_sel_run1 D hr (le_refl 1) hcD)]
          have hcapD : D.profileCap n G e =
              D.chordTapes (blockSize G n) e * (blockSize G n * G) := by
            unfold TSDiagram.profileCap; rw [blockCap_chord D hcD]
          have hct := chordTapes_sel_run1 D (K := 1) (P := P) (L := n * n * entryBits n) hr hcD
          rw [one_mul] at hct
          refine lt_of_lt_of_le hc (Nat.pow_le_pow_right (by norm_num) ?_)
          rw [hcapD]
          exact Nat.mul_le_mul_right _ hct
      · rw [synCode_run1_notD D n G P t C hcol corr e _ _ h1 hE]
        by_cases hm : e.2 = e.1 + 1
        · rw [ite_eq_left hm, blockCap_mem _ (mem_memEdges_of_edges _ he hm)]
          exact lt_of_lt_of_le (encV_lt _) (Nat.pow_le_pow_right (by norm_num) (by omega))
        · rw [ite_eq_right hm]; exact Nat.two_pow_pos _
    · by_cases h2 : e.1 < P
      · rw [synCode_epi D n G P t C hcol corr e _ _ h1 h2]
        by_cases hm : e.2 = e.1 + 1
        · rw [ite_eq_left hm, blockCap_mem _ (mem_memEdges_of_edges _ he hm)]
          exact lt_of_lt_of_le (encV_lt _) (Nat.pow_le_pow_right (by norm_num) (by omega))
        · rw [ite_eq_right hm]; exact Nat.two_pow_pos _
      · rw [synCode_run2 D n G P t C hcol corr e _ _ h1 h2]
        obtain ⟨a', b'⟩ := e
        simp only at h1 h2 hlt hEl ⊢
        obtain ⟨a'', rfl⟩ : ∃ a'', a' = P + a'' := ⟨a' - P, by omega⟩
        obtain ⟨b'', rfl⟩ : ∃ b'', b' = P + b'' := ⟨b' - P, by omega⟩
        have hED := (mem_edges_sel_add D (K := 1) hr hD (by omega) a'' b'').1 he
        have ha'' := (edges_lt D _ hED).1
        simp only [Nat.add_sub_cancel_left]
        rw [ite_eq_left hED]
        obtain ⟨-, hI⟩ := hrun2 a'' ha''
        have hc := hcap _ hED
        simp only [NetCode.edgeVal] at hc
        rw [hI, visible_sel_add D hr hP]
        by_cases hm : b'' = a'' + 1
        · rw [ite_eq_left (show P + b'' = P + a'' + 1 by omega),
            blockCap_mem _ (mem_memEdges_of_edges _ he (by simp only; omega))]
          have hmD := mem_memEdges_of_edges D hED (by simp only; omega)
          have hcapD : D.profileCap n G (a'', b'') =
              (∑ i, (pairRes (blockSize G n) (D.work i) D.T a'').card) * (blockSize G n * G) := by
            unfold TSDiagram.profileCap; rw [blockCap_mem D hmD, Nat.add_zero]
          have hres := resSum_sel_run2 D (K := 1) (P := P) (r := blockSize G n) hD a''
          refine lt_of_lt_of_le (pack_state_lt (encV_lt _) hc) (Nat.pow_le_pow_right (by norm_num) ?_)
          rw [hcapD]
          exact Nat.add_le_add_right (Nat.mul_le_mul_right _ hres) _
        · rw [ite_eq_right (show ¬ P + b'' = P + a'' + 1 by omega)]
          have hcD := mem_chordEdges_of_edges D hED (by simp only; omega)
          rw [blockCap_chord _ (mem_chordEdges_of_edges _ he (by simp only; omega))]
          have hcapD : D.profileCap n G (a'', b'') =
              D.chordTapes (blockSize G n) (a'', b'') * (blockSize G n * G) := by
            unfold TSDiagram.profileCap; rw [blockCap_chord D hcD]
          have hct := chordTapes_sel_run2 D (K := 1) (P := P) (L := n * n * entryBits n) hr hD
            a'' b''
          refine lt_of_lt_of_le hc (Nat.pow_le_pow_right (by norm_num) ?_)
          rw [hcapD]
          exact Nat.mul_le_mul_right _ hct
  · -- outputs
    have hu' := outNode_lt hD hr hL1 (tpos n (entryBits n) d)
    obtain ⟨hS, hI⟩ := hrun2 (D.outNode (blockSize G n) (tpos n (entryBits n) d)) hu'
    show (synCode D n G P t C hcol corr).dec _ _ _ = _
    rw [outNode_sel D hr hD hT]
    show xor (C.dec _ (inSyn2 D n G P t _) _)
      (corr (synIn t (P + D.outNode (blockSize G n) (tpos n (entryBits n) d)) _)
        (tpos n (entryBits n) (tpos n (entryBits n) d))) = _
    rw [hI]
    beta_reduce
    rw [visible_sel_add D hr hP]
    unfold synIn
    rw [hS, decV_encV, synState_final D C hcol x' hG hn hD hP, tpos_tpos hd, hcorr d hd]
    show xor (outC D n G C x' (tpos n (entryBits n) d))
      (xor (outC D n G C x' (tpos n (entryBits n) d)) (xbits x' d)) = _
    rw [← Bool.xor_assoc, Bool.xor_self, Bool.false_xor]
    simp only [xbits, dite_eq_left hd]

/-! ### A random check matrix separates few vectors -/

/-- The syndrome of `v : Fin L → Bool` under the check matrix with columns `h d`. -/
noncomputable def synF {L t : ℕ} (h : Fin L → Fin t → ZMod 2) (v : Fin L → Bool) : Fin t → ZMod 2 :=
  ∑ d, (if v d then h d else 0)

theorem zmod2_mat_add_self {L t : ℕ} (h : Fin L → Fin t → ZMod 2) : h + h = 0 := by
  funext d
  simp only [Pi.add_apply, Pi.zero_apply]
  exact zmod2_vec_add_self (h d)

theorem synF_xor {L t : ℕ} (h : Fin L → Fin t → ZMod 2) (v v' : Fin L → Bool) :
    synF h v + synF h v' = synF h (fun d => xor (v d) (v' d)) := by
  unfold synF
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun d _ => ite_add_ite_xor _ _ _)

theorem synF_add {L t : ℕ} (h h' : Fin L → Fin t → ZMod 2) (v : Fin L → Bool) :
    synF (h + h') v = synF h v + synF h' v := by
  unfold synF
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  cases v d <;> simp

theorem synF_single {L t : ℕ} (v : Fin L → Bool) {d₀ : Fin L} (hd₀ : v d₀ = true)
    (a : Fin t → ZMod 2) : synF (Pi.single d₀ a) v = a := by
  unfold synF
  rw [Finset.sum_eq_single d₀ (fun d _ hd => by simp [hd]) (fun h => absurd (Finset.mem_univ _) h)]
  simp [hd₀]

theorem card_mat (L t : ℕ) :
    (Finset.univ : Finset (Fin L → Fin t → ZMod 2)).card = 2 ^ (L * t) := by
  rw [Finset.card_univ, Fintype.card_fun, card_vec2, Fintype.card_fin, ← pow_mul, Nat.mul_comm]

/-- For a nonzero `v`, exactly a `2^{-t}` fraction of the check matrices annihilate it. -/
theorem card_synF_zero {L t : ℕ} (v : Fin L → Bool) {d₀ : Fin L} (hd₀ : v d₀ = true) :
    (Finset.univ.filter (fun h : Fin L → Fin t → ZMod 2 => synF h v = 0)).card * 2 ^ t =
      2 ^ (L * t) := by
  classical
  have hfib : ∀ a : Fin t → ZMod 2,
      (Finset.univ.filter (fun h : Fin L → Fin t → ZMod 2 => synF h v = a)).card =
      (Finset.univ.filter (fun h : Fin L → Fin t → ZMod 2 => synF h v = 0)).card := by
    intro a
    apply Finset.card_nbij' (fun h => h + Pi.single d₀ a) (fun h => h + Pi.single d₀ a)
    · intro h hh
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hh ⊢
      rw [synF_add, synF_single v hd₀, hh, zmod2_vec_add_self]
    · intro h hh
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hh ⊢
      rw [synF_add, synF_single v hd₀, hh, zero_add]
    · intro h _
      simp only [add_assoc, zmod2_mat_add_self, add_zero]
    · intro h _
      simp only [add_assoc, zmod2_mat_add_self, add_zero]
  have hsum := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (Fin L → Fin t → ZMod 2)))
    (t := (Finset.univ : Finset (Fin t → ZMod 2))) (f := fun h => synF h v)
    (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
  have hS : (Finset.univ : Finset (Fin t → ZMod 2)).card = 2 ^ t := by
    rw [Finset.card_univ, card_vec2]
  rw [Finset.sum_congr rfl (fun b _ => hfib b), Finset.sum_const, hS, smul_eq_mul, card_mat] at hsum
  rw [hsum, Nat.mul_comm]

/-- **A random check matrix is injective on few vectors.** If `|V|² < 2^t`, some `t × L` check
matrix gives the vectors of `V` distinct syndromes. -/
theorem exists_injective_synF {L t : ℕ} (V : Finset (Fin L → Bool)) (hV : V.card ^ 2 < 2 ^ t) :
    ∃ h : Fin L → Fin t → ZMod 2, ∀ v ∈ V, ∀ v' ∈ V, synF h v = synF h v' → v = v' := by
  classical
  set Pairs := (V ×ˢ V).filter (fun p => p.1 ≠ p.2) with hPairs
  set Bad := Pairs.biUnion (fun p => Finset.univ.filter
    (fun h : Fin L → Fin t → ZMod 2 => synF h (fun d => xor (p.1 d) (p.2 d)) = 0)) with hBad
  have hB : ∀ p ∈ Pairs, (Finset.univ.filter
      (fun h : Fin L → Fin t → ZMod 2 => synF h (fun d => xor (p.1 d) (p.2 d)) = 0)).card * 2 ^ t
      = 2 ^ (L * t) := by
    intro p hp
    rw [hPairs, Finset.mem_filter] at hp
    obtain ⟨d₀, hd₀⟩ := Function.ne_iff.1 hp.2
    exact card_synF_zero _ (d₀ := d₀) (by cases ha : p.1 d₀ <;> cases hb : p.2 d₀ <;> simp_all)
  have h1 : Bad.card * 2 ^ t ≤ Pairs.card * 2 ^ (L * t) := by
    calc Bad.card * 2 ^ t ≤ (∑ p ∈ Pairs, (Finset.univ.filter (fun h : Fin L → Fin t → ZMod 2 =>
          synF h (fun d => xor (p.1 d) (p.2 d)) = 0)).card) * 2 ^ t :=
          Nat.mul_le_mul_right _ Finset.card_biUnion_le
      _ = ∑ p ∈ Pairs, 2 ^ (L * t) := by rw [Finset.sum_mul]; exact Finset.sum_congr rfl hB
      _ = Pairs.card * 2 ^ (L * t) := by rw [Finset.sum_const, smul_eq_mul]
  have h2 : Pairs.card ≤ V.card ^ 2 := by
    calc Pairs.card ≤ (V ×ˢ V).card := Finset.card_filter_le _ _
      _ = V.card ^ 2 := by rw [Finset.card_product, sq]
  have h3 : Bad.card < (Finset.univ : Finset (Fin L → Fin t → ZMod 2)).card := by
    rw [card_mat]
    have : Bad.card * 2 ^ t < 2 ^ (L * t) * 2 ^ t := by
      calc Bad.card * 2 ^ t ≤ Pairs.card * 2 ^ (L * t) := h1
        _ ≤ V.card ^ 2 * 2 ^ (L * t) := Nat.mul_le_mul_right _ h2
        _ < 2 ^ t * 2 ^ (L * t) := Nat.mul_lt_mul_of_pos_right hV (Nat.two_pow_pos _)
        _ = 2 ^ (L * t) * 2 ^ t := Nat.mul_comm _ _
    exact Nat.lt_of_mul_lt_mul_right this
  obtain ⟨h, -, hh⟩ := Finset.exists_mem_notMem_of_card_lt_card h3
  refine ⟨h, fun v hv v' hv' heq => ?_⟩
  by_contra hne
  apply hh
  rw [hBad, Finset.mem_biUnion]
  refine ⟨(v, v'), by rw [hPairs, Finset.mem_filter]; exact ⟨Finset.mem_product.2 ⟨hv, hv'⟩, hne⟩, ?_⟩
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [← synF_xor, heq, zmod2_vec_add_self]

/-- Extend a check matrix on `Fin L` to `ℕ` (zero columns from `L` on). -/
noncomputable def hcolOf {L t : ℕ} (hm : Fin L → Fin t → ZMod 2) : ℕ → Fin t → ZMod 2 :=
  fun d => if hd : d < L then hm ⟨d, hd⟩ else 0

theorem syndrome_hcolOf {L t : ℕ} (hm : Fin L → Fin t → ZMod 2) (e : ℕ → Bool) (v : Fin L → Bool)
    (hv : ∀ d (hd : d < L), e d = v ⟨d, hd⟩) : syndrome L t (hcolOf hm) e = synF hm v := by
  unfold syndrome synF hcolOf
  rw [Finset.sum_range]
  apply Finset.sum_congr rfl
  intro d _
  rw [dite_eq_left d.2, hv d d.2]

open Classical in
/-- Decode a syndrome to the vector of `V` with that syndrome (`false` if there is none). -/
noncomputable def decodeSyn {L t : ℕ} (V : Finset (Fin L → Bool)) (hm : Fin L → Fin t → ZMod 2)
    (S : Fin t → ZMod 2) (d : ℕ) : Bool :=
  if hS : ∃ v ∈ V, synF hm v = S then (if hd : d < L then hS.choose ⟨d, hd⟩ else false) else false

theorem decodeSyn_eq {L t : ℕ} {V : Finset (Fin L → Bool)} {hm : Fin L → Fin t → ZMod 2}
    (hinj : ∀ v ∈ V, ∀ v' ∈ V, synF hm v = synF hm v' → v = v') {v : Fin L → Bool} (hv : v ∈ V)
    {d : ℕ} (hd : d < L) : decodeSyn V hm (synF hm v) d = v ⟨d, hd⟩ := by
  have hS : ∃ v' ∈ V, synF hm v' = synF hm v := ⟨v, hv, rfl⟩
  unfold decodeSyn
  rw [dite_eq_left hS, dite_eq_left hd, hinj _ hS.choose_spec.1 v hv hS.choose_spec.2]

/-! ### Plain ⟹ every code within capacity errs in many ways -/

/-- **Plain ⟹ every code within capacity has many error patterns.** Under `NoCode_TM`, for all
constants and all large `n`: if a code stays within the profile capacities of `D` on every input,
its error vectors (the output bit at `tpos d` against the input bit `d`) take more than `2^{H n w}`
values. -/
theorem noCode_fewErrors_of_noCode (h : NoCode_TM) (k G c H : ℕ) (hG : 1 ≤ G) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
      ∀ (code : NetCode),
        (∀ x : Fin (n * n * entryBits n) → Bool, ∀ e ∈ D.edges (blockSize G n),
          code.edgeVal (D.edges (blockSize G n))
            (fun y => D.visible n (entryBits n) (blockSize G n) y x) e < 2 ^ D.profileCap n G e) →
      ∀ (V : Finset (Fin (n * n * entryBits n) → Bool)), V.card ≤ 2 ^ (H * n * entryBits n) →
        ¬ ∀ x : Fin (n * n * entryBits n) → Bool, (fun d : Fin (n * n * entryBits n) => xor
            (code.outVal (D.edges (blockSize G n))
              (fun y => D.visible n (entryBits n) (blockSize G n) y x)
              (D.outNode (blockSize G n) (tpos n (entryBits n) d)) (tpos n (entryBits n) d))
            (x d)) ∈ V := by
  obtain ⟨n₀, hn₀⟩ := h ((1 + 1) * k + (2 * H + 1)) G ((2 * c + 2) * G + c + 4) hG
  refine ⟨max n₀ 1, fun n hn D hD hT code hcap V hV hall => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hr : 1 ≤ blockSize G n := one_le_blockSize hG hn1
  have hrG : n * entryBits n ≤ blockSize G n * G := blockSize_mul_ge hG
  have hnw : 1 ≤ n * entryBits n := Nat.one_le_iff_ne_zero.2 (by unfold entryBits; positivity)
  obtain ⟨hroom, htime⟩ := sel_room_time D hG hn1 hT
  have hVt : V.card ^ 2 < 2 ^ (2 * (H * n * entryBits n) + 1) := by
    calc V.card ^ 2 ≤ (2 ^ (H * n * entryBits n)) ^ 2 := Nat.pow_le_pow_left hV 2
      _ = 2 ^ (2 * (H * n * entryBits n)) := by rw [← pow_mul, Nat.mul_comm]
      _ < 2 ^ (2 * (H * n * entryBits n) + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  obtain ⟨hm, hinj⟩ := exists_injective_synF V hVt
  have ht : 2 * (H * n * entryBits n) + 1 ≤ (2 * H + 1) * (blockSize G n * G) := by
    have e : 2 * (H * n * entryBits n) + 1 ≤ (2 * H + 1) * (n * entryBits n) := by
      have : H * n * entryBits n = H * (n * entryBits n) := by ring
      rw [this]; nlinarith
    exact le_trans e (Nat.mul_le_mul_left _ hrG)
  have hsolU : (selDiagram D 1 ((2 * c + 2) * n * G + 4) (blockSize G n)
      (n * n * entryBits n)).Solves n G
      ((selDiagram D 1 ((2 * c + 2) * n * G + 4) (blockSize G n) (n * n * entryBits n)).blockCap n G
        (fun y => ∑ i, (pairRes (blockSize G n)
          ((selDiagram D 1 ((2 * c + 2) * n * G + 4) (blockSize G n) (n * n * entryBits n)).work i)
          (selDiagram D 1 ((2 * c + 2) * n * G + 4) (blockSize G n) (n * n * entryBits n)).T y).card)
        (2 * (H * n * entryBits n) + 1))
      Set.univ (synCode D n G ((2 * c + 2) * n * G + 4) (2 * (H * n * entryBits n) + 1) code
        (hcolOf hm) (decodeSyn V hm)) := by
    intro x _
    refine syn_solves_at D code (hcolOf hm) (decodeSyn V hm) x hG hn1 hD hroom (hcap x)
      (fun d hd => ?_) x (Set.mem_singleton x)
    have hev : (fun d : Fin (n * n * entryBits n) =>
        xor (outC D n G code x (tpos n (entryBits n) d)) (x d)) ∈ V := hall x
    rw [syndrome_hcolOf hm _ (fun d : Fin (n * n * entryBits n) =>
        xor (outC D n G code x (tpos n (entryBits n) d)) (x d))
        (fun d' hd' => by simp only [xbits, dite_eq_left hd']),
      decodeSyn_eq hinj hev hd]
    simp only [xbits, dite_eq_left hd]
  have hsol' := solves_profileCap_addTapes (a := 2 * H + 1) hr ht hsolU
  refine hn₀ n (le_trans (le_max_left _ _) hn) _
    (valid_addTapes _ (valid_sel D hD hr hroom) _) ?_ _ hsol'
  rw [T_addTapes]
  exact htime

/-- The vectors with at most `τ` ones number at most `(L + 1)^τ`. -/
theorem card_sparse_le (L τ : ℕ) :
    ((Finset.univ : Finset (Fin L → Bool)).filter
      (fun v => (Finset.univ.filter (fun d => v d = true)).card ≤ τ)).card ≤ (L + 1) ^ τ := by
  classical
  let g : (Fin τ → Option (Fin L)) → (Fin L → Bool) := fun f d => decide (∃ i, f i = some d)
  have hsub : (Finset.univ : Finset (Fin L → Bool)).filter
      (fun v => (Finset.univ.filter (fun d => v d = true)).card ≤ τ) ⊆ Finset.univ.image g := by
    intro v hv
    rw [Finset.mem_filter] at hv
    rw [Finset.mem_image]
    refine ⟨fun i => if hi : (i : ℕ) < (Finset.univ.filter (fun d => v d = true)).card then
      some ((Finset.univ.filter (fun d => v d = true)).equivFin.symm ⟨i, hi⟩).1 else none,
      Finset.mem_univ _, ?_⟩
    funext d
    simp only [g]
    by_cases hvd : v d = true
    · rw [hvd]
      apply decide_eq_true
      have hdS : d ∈ Finset.univ.filter (fun d => v d = true) :=
        Finset.mem_filter.2 ⟨Finset.mem_univ _, hvd⟩
      refine ⟨⟨(Finset.univ.filter (fun d => v d = true)).equivFin ⟨d, hdS⟩,
        lt_of_lt_of_le ((Finset.univ.filter (fun d => v d = true)).equivFin ⟨d, hdS⟩).2 hv.2⟩, ?_⟩
      simp only [Fin.is_lt, dite_true, Fin.eta, Equiv.symm_apply_apply]
    · have hvf : v d = false := by simpa using hvd
      rw [hvf]
      apply decide_eq_false
      rintro ⟨i, hi⟩
      split_ifs at hi with hlt
      · have hmem := ((Finset.univ.filter (fun d => v d = true)).equivFin.symm ⟨i, hlt⟩).2
        rw [Option.some_inj] at hi
        rw [hi, Finset.mem_filter] at hmem
        exact hvd hmem.2
  calc _ ≤ (Finset.univ.image g).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin τ → Option (Fin L))).card := Finset.card_image_le
    _ = (L + 1) ^ τ := by
        rw [Finset.card_univ, Fintype.card_fun, Fintype.card_option, Fintype.card_fin,
          Fintype.card_fin]

/-- **Plain ⟹ transposition with `O(n)` wrong bits is as hard as exact.** Under `NoCode_TM`, for
all constants and all large `n`: no code within the profile capacities on every input gets all but
at most `A n` of the `n² w` output bits right on every input. -/
theorem noCode_sparseErrors_of_noCode (h : NoCode_TM) (k G c A : ℕ) (hG : 1 ≤ G) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
      ∀ (code : NetCode),
        (∀ x : Fin (n * n * entryBits n) → Bool, ∀ e ∈ D.edges (blockSize G n),
          code.edgeVal (D.edges (blockSize G n))
            (fun y => D.visible n (entryBits n) (blockSize G n) y x) e < 2 ^ D.profileCap n G e) →
        ¬ ∀ x : Fin (n * n * entryBits n) → Bool, (Finset.univ.filter
            (fun d : Fin (n * n * entryBits n) =>
            code.outVal (D.edges (blockSize G n))
              (fun y => D.visible n (entryBits n) (blockSize G n) y x)
              (D.outNode (blockSize G n) (tpos n (entryBits n) d)) (tpos n (entryBits n) d) ≠
            x d)).card ≤ A * n := by
  classical
  obtain ⟨n₀, hn₀⟩ := noCode_fewErrors_of_noCode h k G c (4 * A) hG
  refine ⟨max n₀ 1, fun n hn D hD hT code hcap hall => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hw : 1 ≤ entryBits n := by unfold entryBits; omega
  refine hn₀ n (le_trans (le_max_left _ _) hn) D hD hT code hcap
    ((Finset.univ : Finset (Fin (n * n * entryBits n) → Bool)).filter
      (fun v => (Finset.univ.filter (fun d => v d = true)).card ≤ A * n)) ?_ (fun x => ?_)
  · calc _ ≤ (n * n * entryBits n + 1) ^ (A * n) := card_sparse_le _ _
      _ ≤ (2 ^ (3 * entryBits n + 1)) ^ (A * n) := Nat.pow_le_pow_left (inputLength_succ_le n) _
      _ = 2 ^ ((3 * entryBits n + 1) * (A * n)) := by rw [← pow_mul]
      _ ≤ 2 ^ (4 * A * n * entryBits n) := by
          apply Nat.pow_le_pow_right (by norm_num)
          have e : 4 * A * n * entryBits n = 4 * entryBits n * (A * n) := by ring
          rw [e]
          exact Nat.mul_le_mul_right _ (by omega)
  · rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, le_trans (le_of_eq ?_) (hall x)⟩
    congr 1
    apply Finset.filter_congr
    intro d _
    have key : ∀ a b : Bool, (xor a b = true ↔ a ≠ b) := by decide
    exact key _ _

/-- The vectors whose `true` bits lie in at most `τ` blocks of `w` consecutive positions (the
blocks `d / w`) number at most `(L + 1)^τ · 2^{w τ}`. -/
theorem card_blockSparse_le (L w τ : ℕ) (hw : 0 < w) :
    ((Finset.univ : Finset (Fin L → Bool)).filter
      (fun v => ((Finset.univ.filter (fun d => v d = true)).image
        (fun d : Fin L => (d : ℕ) / w)).card ≤ τ)).card ≤ (L + 1) ^ τ * 2 ^ (w * τ) := by
  classical
  let g : (Fin τ → Option (Fin L)) × (Fin τ → Fin w → Bool) → (Fin L → Bool) :=
    fun p d => decide (∃ i, p.1 i = some ⟨(d : ℕ) / w, lt_of_le_of_lt (Nat.div_le_self _ _) d.2⟩ ∧
      p.2 i ⟨(d : ℕ) % w, Nat.mod_lt _ hw⟩ = true)
  have hsub : (Finset.univ : Finset (Fin L → Bool)).filter
      (fun v => ((Finset.univ.filter (fun d => v d = true)).image
        (fun d : Fin L => (d : ℕ) / w)).card ≤ τ) ⊆ Finset.univ.image g := by
    intro v hv
    rw [Finset.mem_filter] at hv
    set E := (Finset.univ.filter (fun d => v d = true)).image (fun d : Fin L => (d : ℕ) / w)
      with hE
    have hEL : ∀ q ∈ E, q < L := by
      intro q hq
      rw [hE, Finset.mem_image] at hq
      obtain ⟨d, -, rfl⟩ := hq
      exact lt_of_le_of_lt (Nat.div_le_self _ _) d.2
    let ve : ℕ → Bool := fun p => if h : p < L then v ⟨p, h⟩ else false
    rw [Finset.mem_image]
    refine ⟨(fun i => if hi : (i : ℕ) < E.card then
        some ⟨(E.equivFin.symm ⟨i, hi⟩).1, hEL _ (E.equivFin.symm ⟨i, hi⟩).2⟩ else none,
      fun i t => if hi : (i : ℕ) < E.card then ve ((E.equivFin.symm ⟨i, hi⟩).1 * w + t)
        else false), Finset.mem_univ _, ?_⟩
    funext d
    have hdec : (d : ℕ) / w * w + (d : ℕ) % w = d := by
      rw [Nat.mul_comm]; exact Nat.div_add_mod _ _
    have hve : ve ((d : ℕ) / w * w + (d : ℕ) % w) = v d := by
      simp only [ve, hdec, dite_eq_left d.2]
    by_cases hvd : v d = true
    · rw [hvd]
      apply decide_eq_true
      have hq : (d : ℕ) / w ∈ E := by
        rw [hE, Finset.mem_image]
        exact ⟨d, Finset.mem_filter.2 ⟨Finset.mem_univ _, hvd⟩, rfl⟩
      refine ⟨⟨E.equivFin ⟨_, hq⟩, lt_of_lt_of_le (E.equivFin ⟨_, hq⟩).2 hv.2⟩, ?_, ?_⟩
      · simp only [Fin.is_lt, dite_true, Fin.eta, Equiv.symm_apply_apply]
      · simp only [Fin.is_lt, dite_true, Fin.eta, Equiv.symm_apply_apply]
        rw [hve, hvd]
    · have hvf : v d = false := by simpa using hvd
      rw [hvf]
      apply decide_eq_false
      rintro ⟨i, hi1, hi2⟩
      dsimp only at hi1 hi2
      split_ifs at hi1 hi2 with hlt
      · rw [Option.some_inj] at hi1
        have hq : (E.equivFin.symm ⟨i, hlt⟩).1 = (d : ℕ) / w := congrArg Fin.val hi1
        rw [hq, hve] at hi2
        exact hvd hi2
  calc _ ≤ (Finset.univ.image g).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset ((Fin τ → Option (Fin L)) × (Fin τ → Fin w → Bool))).card :=
        Finset.card_image_le
    _ = (L + 1) ^ τ * 2 ^ (w * τ) := by
        rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fun, Fintype.card_option,
          Fintype.card_fin, Fintype.card_fin, Fintype.card_fun, Fintype.card_fun, Fintype.card_bool,
          Fintype.card_fin, Fintype.card_fin, ← pow_mul]

/-- **Plain ⟹ transposition with `O(n)` wrong entries is as hard as exact.** Under `NoCode_TM`, for
all constants and all large `n`: no code within the profile capacities on every input gets all but
at most `A n` of the `n²` matrix entries right on every input (an entry is wrong if any of its `w`
bits is). -/
theorem noCode_sparseEntryErrors_of_noCode (h : NoCode_TM) (k G c A : ℕ) (hG : 1 ≤ G) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
      ∀ (code : NetCode),
        (∀ x : Fin (n * n * entryBits n) → Bool, ∀ e ∈ D.edges (blockSize G n),
          code.edgeVal (D.edges (blockSize G n))
            (fun y => D.visible n (entryBits n) (blockSize G n) y x) e < 2 ^ D.profileCap n G e) →
        ¬ ∀ x : Fin (n * n * entryBits n) → Bool, ((Finset.univ.filter
            (fun d : Fin (n * n * entryBits n) =>
            code.outVal (D.edges (blockSize G n))
              (fun y => D.visible n (entryBits n) (blockSize G n) y x)
              (D.outNode (blockSize G n) (tpos n (entryBits n) d)) (tpos n (entryBits n) d) ≠
            x d)).image (fun d : Fin (n * n * entryBits n) => (d : ℕ) / entryBits n)).card ≤
          A * n := by
  classical
  obtain ⟨n₀, hn₀⟩ := noCode_fewErrors_of_noCode h k G c (5 * A) hG
  refine ⟨max n₀ 1, fun n hn D hD hT code hcap hall => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hw : 1 ≤ entryBits n := by unfold entryBits; omega
  refine hn₀ n (le_trans (le_max_left _ _) hn) D hD hT code hcap
    ((Finset.univ : Finset (Fin (n * n * entryBits n) → Bool)).filter
      (fun v => ((Finset.univ.filter (fun d => v d = true)).image
        (fun d : Fin (n * n * entryBits n) => (d : ℕ) / entryBits n)).card ≤ A * n)) ?_
    (fun x => ?_)
  · calc _ ≤ (n * n * entryBits n + 1) ^ (A * n) * 2 ^ (entryBits n * (A * n)) :=
          card_blockSparse_le _ _ _ (by omega)
      _ ≤ (2 ^ (3 * entryBits n + 1)) ^ (A * n) * 2 ^ (entryBits n * (A * n)) :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (inputLength_succ_le n) _)
      _ = 2 ^ ((3 * entryBits n + 1) * (A * n) + entryBits n * (A * n)) := by
          rw [← pow_mul, ← pow_add]
      _ ≤ 2 ^ (5 * A * n * entryBits n) := by
          apply Nat.pow_le_pow_right (by norm_num)
          have e : 5 * A * n * entryBits n = 5 * entryBits n * (A * n) := by ring
          rw [e, ← Nat.add_mul]
          exact Nat.mul_le_mul_right _ (by omega)
  · rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, le_trans (le_of_eq ?_) (hall x)⟩
    congr 2
    apply Finset.filter_congr
    intro d _
    have key : ∀ a b : Bool, (xor a b = true ↔ a ≠ b) := by decide
    exact key _ _

/-- **Plain ⟹ no `O(1)` codes with few error patterns cover the inputs.** Under `NoCode_TM`, for all
constants and all large `n`: let `K` codes stay within the profile capacities of `D` on every input,
and let `V` be a set of at most `2^{H n w}` vectors. Then some input has none of the `K` error
vectors in `V`. The choice among the `K` codes may be any function of the input (a constant-size
oracle hint). This contains `noCode_fewErrors_of_noCode` (`K = 1`) and, for codes within capacity,
the constant-hint result (`V = {0}`). *Construction:* the syndrome-corrected codes
(`syn_solves_at`) are the candidates of a selection (`select_solves`). -/
theorem noCode_fewErrorsCover_of_noCode (h : NoCode_TM) (k G c H K : ℕ) (hG : 1 ≤ G)
    (hK : 1 ≤ K) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
      ∀ (codes : ℕ → NetCode),
        (∀ j < K, ∀ x : Fin (n * n * entryBits n) → Bool, ∀ e ∈ D.edges (blockSize G n),
          (codes j).edgeVal (D.edges (blockSize G n))
            (fun y => D.visible n (entryBits n) (blockSize G n) y x) e < 2 ^ D.profileCap n G e) →
      ∀ (V : Finset (Fin (n * n * entryBits n) → Bool)), V.card ≤ 2 ^ (H * n * entryBits n) →
        ¬ ∀ x : Fin (n * n * entryBits n) → Bool, ∃ j < K,
          (fun d : Fin (n * n * entryBits n) => xor
            ((codes j).outVal (D.edges (blockSize G n))
              (fun y => D.visible n (entryBits n) (blockSize G n) y x)
              (D.outNode (blockSize G n) (tpos n (entryBits n) d)) (tpos n (entryBits n) d))
            (x d)) ∈ V := by
  obtain ⟨n₀, hn₀⟩ := h ((K + 1) * ((1 + 1) * k + (2 * H + 1)) + 6 * K ^ 2) G
    ((2 * ((2 * c + 2) * G + c + 4) + 2) * G + ((2 * c + 2) * G + c + 4) + 4) hG
  refine ⟨max n₀ 1, fun n hn D hD hT codes hcap V hV hall => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hr : 1 ≤ blockSize G n := one_le_blockSize hG hn1
  have hrG : n * entryBits n ≤ blockSize G n * G := blockSize_mul_ge hG
  obtain ⟨hroom, htime⟩ := sel_room_time D hG hn1 hT
  have hVt : V.card ^ 2 < 2 ^ (2 * (H * n * entryBits n) + 1) := by
    calc V.card ^ 2 ≤ (2 ^ (H * n * entryBits n)) ^ 2 := Nat.pow_le_pow_left hV 2
      _ = 2 ^ (2 * (H * n * entryBits n)) := by rw [← pow_mul, Nat.mul_comm]
      _ < 2 ^ (2 * (H * n * entryBits n) + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  obtain ⟨hm, hinj⟩ := exists_injective_synF V hVt
  have ht : 2 * (H * n * entryBits n) + 1 ≤ (2 * H + 1) * (blockSize G n * G) := by
    have hnw : 1 ≤ n * entryBits n := Nat.one_le_iff_ne_zero.2 (by unfold entryBits; positivity)
    have e : 2 * (H * n * entryBits n) + 1 ≤ (2 * H + 1) * (n * entryBits n) := by
      have : H * n * entryBits n = H * (n * entryBits n) := by ring
      rw [this]; nlinarith
    exact le_trans e (Nat.mul_le_mul_left _ hrG)
  -- the candidates: syndrome-corrected codes on the one-copy selection diagram
  have hcov : ∀ x, ∃ j < K,
      (addTapes (selDiagram D 1 ((2 * c + 2) * n * G + 4) (blockSize G n) (n * n * entryBits n))
        (2 * H + 1)).Solves n G
        ((addTapes (selDiagram D 1 ((2 * c + 2) * n * G + 4) (blockSize G n)
          (n * n * entryBits n)) (2 * H + 1)).profileCap n G) {x}
        (synCode D n G ((2 * c + 2) * n * G + 4) (2 * (H * n * entryBits n) + 1) (codes j)
          (hcolOf hm) (decodeSyn V hm)) := by
    intro x
    obtain ⟨j, hj, hjx⟩ := hall x
    refine ⟨j, hj, solves_profileCap_addTapes (a := 2 * H + 1) hr ht ?_⟩
    refine syn_solves_at D (codes j) (hcolOf hm) (decodeSyn V hm) x hG hn1 hD hroom
      (hcap j hj x) (fun d hd => ?_)
    have hev : (fun d : Fin (n * n * entryBits n) =>
        xor (outC D n G (codes j) x (tpos n (entryBits n) d)) (x d)) ∈ V := hjx
    rw [syndrome_hcolOf hm _ (fun d : Fin (n * n * entryBits n) =>
        xor (outC D n G (codes j) x (tpos n (entryBits n) d)) (x d))
        (fun d' hd' => by simp only [xbits, dite_eq_left hd']),
      decodeSyn_eq hinj hev hd]
    simp only [xbits, dite_eq_left hd]
  have hD₁ : (addTapes (selDiagram D 1 ((2 * c + 2) * n * G + 4) (blockSize G n)
      (n * n * entryBits n)) (2 * H + 1)).Valid (n * n * entryBits n) :=
    valid_addTapes _ (valid_sel D hD hr hroom) (2 * H + 1)
  have hT₁ : (addTapes (selDiagram D 1 ((2 * c + 2) * n * G + 4) (blockSize G n)
      (n * n * entryBits n)) (2 * H + 1)).T ≤
      ((2 * c + 2) * G + c + 4) * (n * n * entryBits n) := by
    rw [T_addTapes]; exact htime
  obtain ⟨hroom₂, htime₂⟩ := sel_room_time _ hG hn1 hT₁
  have hsel := select_solves _ hG hn1 hK hD₁ hroom₂
    (fun j => synCode D n G ((2 * c + 2) * n * G + 4) (2 * (H * n * entryBits n) + 1) (codes j)
      (hcolOf hm) (decodeSyn V hm)) hcov
  have hs' : selBits K (n * n * entryBits n) ≤ 6 * K ^ 2 * (blockSize G n * G) := by
    have h2 : entryBits n ≤ blockSize G n * G :=
      le_trans (Nat.le_mul_of_pos_left _ (by omega)) hrG
    exact le_trans (selBits_le K n) (Nat.mul_le_mul_left _ h2)
  have hsel' := solves_profileCap_addTapes (a := 6 * K ^ 2) hr hs' hsel
  refine hn₀ n (le_trans (le_max_left _ _) hn) _
    (valid_addTapes _ (valid_sel _ hD₁ hr hroom₂) _) ?_ _ hsel'
  rw [T_addTapes]
  exact htime₂

end Transpose.Tape.Impl
