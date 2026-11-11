import BoundedArityDecoders.NativeSweepInterfaceProofs
import BoundedArityDecoders.SumsetRankDeficit

/-!
# Machine-Level `Transpose.TM` Sweep-Cone Extraction & Conditional Reductions to `(T)`

This module establishes:
1. **Non-tautological `Transpose.TM` causal-cone tree extraction (`Problem 9.4`)**:
   Starting from a concrete `q`-state, `k`-work-tape machine `M : Transpose.TM` (`1 ≤ M.k`) and a
   frozen-trace `Γ`-cut fibre `IsFrozenTraceCutFibre M d T inPos workPos emitStep Γ C`, we define
   explicit depth-`D` `(1 + M.k)`-ary causal-cone trees (`ParametricConeTree` / `CausalConeTree` /
   `SlotConeTree`), evaluate them purely via `M.δ` (`evalConeTree`), bound their syntactic cell
   support by `(M.k + 1)^D` (`evalConeTree_cellSupport`), prove exact agreement with `M`'s live
   execution on `C` (`evalConeTree_traceConeTree_eq`), and derive both cut-absorbed (`M₀` classes)
   and cut-label-refined (`M₀ * ((M.q + 1) * (M.g + 1)^M.k)^L_cut` classes) instances of
   `IsBoundedAritySetCode` and Theorem 1 (`tmPeriodicSweepExtraction_cutAbsorbed`,
   `tmPeriodicSweepExtraction_cutLabelRefined`).
2. **Conditional end-to-end reductions to `TapeCodingConjectureNegationSpec` and Open Targets**:
   Work-tape padding (`padDummyWorkTape_transposesWithin`), `Problem 9.4` periodic cell-sweep
   reduction (`PeriodicCellSweepReductionHypothesis` and
   `conditional_TapeCodingConjecture_of_PeriodicCellSweepHypothesis`), the `M = 1` half-barrier
   conditional closure (`conditional_TapeCodingConjecture_of_HalfBarrierAndOneClassFibre`), and
   non-vanishing two-stage linear rank error from the macroscopic rank target
   (`conditional_NoLowErrorTwoStageLinear_of_MacroscopicTarget`).
-/

namespace BoundedArityDecoders

open SharedDecoders Module
open scoped BigOperators

universe u

/-! ### 1. Causal-Cone Trees & Pure `M.δ` Transition Evaluation -/

/-- Rooted `(1 + k)`-ary causal-cone tree of depth at most `D` over state type `Q`, work-tape
alphabet `Γ_sym`, cut-leaf label type `CutLabel`, entry bit-width `b`, and matrix size `d`. -/
inductive ParametricConeTree (CutLabel Q Γ_sym : Type*) (k b d : ℕ) : ℕ → Type _ where
  | leafInit {n : ℕ} : Q → (Fin k → Γ_sym) → ParametricConeTree CutLabel Q Γ_sym k b d n
  | leafCut {n : ℕ} : CutLabel → ParametricConeTree CutLabel Q Γ_sym k b d n
  | stepNode {n : ℕ} :
      Option (ZMod d × ZMod d × Fin b) →
      ParametricConeTree CutLabel Q Γ_sym k b d n →
      (Fin k → ParametricConeTree CutLabel Q Γ_sym k b d n) →
      ParametricConeTree CutLabel Q Γ_sym k b d (n + 1)

/-- Concrete causal-cone tree whose `leafCut` leaves carry frozen post-step `(state, writtenWork)`
pairs in `Q × (Fin k → Γ_sym)`. -/
abbrev CausalConeTree (Q Γ_sym : Type*) (k b d : ℕ) : ℕ → Type _ :=
  ParametricConeTree (Q × (Fin k → Γ_sym)) Q Γ_sym k b d

/-- Symbolic causal-cone skeleton whose `leafCut` leaves reference one of `L_cut` per-column cut
slots `Fin L_cut`. -/
abbrev SlotConeTree (L_cut : ℕ) (Q Γ_sym : Type*) (k b d : ℕ) : ℕ → Type _ :=
  ParametricConeTree (Fin L_cut) Q Γ_sym k b d

/-- Map cut-leaf labels covariantly while preserving the entire step-node and input-read skeleton. -/
def mapCutLabels {Cut₁ Cut₂ Q Γ_sym : Type*} {k b d : ℕ} (f : Cut₁ → Cut₂) :
    ∀ {n : ℕ}, ParametricConeTree Cut₁ Q Γ_sym k b d n → ParametricConeTree Cut₂ Q Γ_sym k b d n
  | _, .leafInit q₀ w₀ => .leafInit q₀ w₀
  | _, .leafCut lbl => .leafCut (f lbl)
  | _, .stepNode readOpt stTree wkTrees =>
      .stepNode readOpt (mapCutLabels f stTree) (fun h => mapCutLabels f (wkTrees h))

/-- Relative `(row, col)` cell read at a single `stepNode`, if within input bounds. -/
def readOptCell {b d : ℕ} : Option (ZMod d × ZMod d × Fin b) → Finset (ZMod d × ZMod d)
  | none => ∅
  | some (r, u, _) => {(r, u)}

/-- Evaluate a relative input-bit specification on a rotated matrix view `Y`. -/
def evalReadOpt {d : ℕ} (Y : State d (CanonicalWordAlphabet d)) :
    Option (ZMod d × ZMod d × Fin (Transpose.entryBits d)) → Option Bool
  | none => none
  | some (r, u, ℓ) => some (Y r u ℓ)

/-- Relative `(row, col)` matrix cells syntactically referenced by a `ParametricConeTree`. -/
def treeCellSupport {CutLabel Q Γ_sym : Type*} {k b d : ℕ} [DecidableEq (ZMod d)] :
    ∀ {n : ℕ}, ParametricConeTree CutLabel Q Γ_sym k b d n → Finset (ZMod d × ZMod d)
  | _, .leafInit _ _ => ∅
  | _, .leafCut _ => ∅
  | _, .stepNode readOpt stTree wkTrees =>
      readOptCell readOpt ∪ treeCellSupport stTree ∪
        Finset.univ.biUnion (fun h => treeCellSupport (wkTrees h))

theorem treeCellSupport_mapCutLabels {Cut₁ Cut₂ Q Γ_sym : Type*} {k b d : ℕ}
    [DecidableEq (ZMod d)] (f : Cut₁ → Cut₂) :
    ∀ {n : ℕ} (tree : ParametricConeTree Cut₁ Q Γ_sym k b d n),
      treeCellSupport (mapCutLabels f tree) = treeCellSupport tree
  | _, .leafInit _ _ => rfl
  | _, .leafCut _ => rfl
  | _, .stepNode _ stTree wkTrees => by
      simp only [mapCutLabels, treeCellSupport, treeCellSupport_mapCutLabels f stTree,
        treeCellSupport_mapCutLabels f (wkTrees _)]

private theorem treeCellSupport_card_succ_le {CutLabel Q Γ_sym : Type*} {k b d : ℕ}
    [DecidableEq (ZMod d)] (hk : 1 ≤ k) :
    ∀ {n : ℕ} (tree : ParametricConeTree CutLabel Q Γ_sym k b d n),
      (treeCellSupport tree).card + 1 ≤ (k + 1) ^ n
  | n, .leafInit _ _ => by
      have : 1 ≤ (k + 1) ^ n := Nat.one_le_pow _ _ (by omega)
      simp [treeCellSupport]; omega
  | n, .leafCut _ => by
      have : 1 ≤ (k + 1) ^ n := Nat.one_le_pow _ _ (by omega)
      simp [treeCellSupport]; omega
  | n + 1, .stepNode readOpt stTree wkTrees => by
      have hPowPos : 1 ≤ (k + 1) ^ n := Nat.one_le_pow _ _ (by omega)
      have hSt := treeCellSupport_card_succ_le hk stTree
      have hWk := fun h => treeCellSupport_card_succ_le hk (wkTrees h)
      have hSelf : (readOptCell readOpt).card ≤ 1 := by
        cases readOpt <;> simp [readOptCell]
      have hBi : (Finset.univ.biUnion (fun h => treeCellSupport (wkTrees h))).card ≤
          k * ((k + 1) ^ n - 1) := by
        calc (Finset.univ.biUnion (fun h => treeCellSupport (wkTrees h))).card
            ≤ ∑ h : Fin k, (treeCellSupport (wkTrees h)).card := Finset.card_biUnion_le
          _ ≤ ∑ _h : Fin k, ((k + 1) ^ n - 1) := by
              refine Finset.sum_le_sum fun h _ => ?_
              have := hWk h; omega
          _ = k * ((k + 1) ^ n - 1) := by simp
      have hUnion : (treeCellSupport (.stepNode readOpt stTree wkTrees)).card ≤
          1 + ((k + 1) ^ n - 1) + k * ((k + 1) ^ n - 1) := by
        simp only [treeCellSupport]
        calc _ ≤ _ + (Finset.univ.biUnion (fun h => treeCellSupport (wkTrees h))).card :=
              Finset.card_union_le _ _
          _ ≤ (_ + (treeCellSupport stTree).card) +
              (Finset.univ.biUnion (fun h => treeCellSupport (wkTrees h))).card :=
              Nat.add_le_add_right (Finset.card_union_le _ _) _
          _ ≤ 1 + ((k + 1) ^ n - 1) + k * ((k + 1) ^ n - 1) := by omega
      have hAlg : (k + 1) + ((k + 1) ^ n - 1) + k * ((k + 1) ^ n - 1) = (k + 1) ^ (n + 1) := by
        calc (k + 1) + ((k + 1) ^ n - 1) + k * ((k + 1) ^ n - 1)
            = (k + 1) * ((k + 1) ^ n - 1 + 1) := by ring
          _ = (k + 1) * (k + 1) ^ n := by rw [Nat.sub_add_cancel hPowPos]
          _ = (k + 1) ^ (n + 1) := (pow_succ' (k + 1) n).symm
      omega

/-- Pure bottom-up evaluator of a `CausalConeTree` for `M : Transpose.TM` on a rotated matrix view
`Y : State d (CanonicalWordAlphabet d)`, applying `M.δ` directly at every `stepNode` and returning
`(postState, writtenWorkSymbols, emittedBitOrFalse)`. -/
def evalConeTree (M : Transpose.TM) {d : ℕ} (Y : State d (CanonicalWordAlphabet d)) :
    ∀ {n : ℕ},
      CausalConeTree (Fin (M.q + 1)) (Fin (M.g + 1)) M.k (Transpose.entryBits d) d n →
      Fin (M.q + 1) × (Fin M.k → Fin (M.g + 1)) × Bool
  | _, .leafInit q₀ w₀ => (q₀, w₀, false)
  | _, .leafCut qw => (qw.1, qw.2, false)
  | _, .stepNode readOpt stTree wkTrees =>
      let st := (evalConeTree M Y stTree).1
      let wk := fun h => (evalConeTree M Y (wkTrees h)).2.1 h
      match M.δ st (evalReadOpt Y readOpt) wk with
      | none => (0, fun _ => 0, false)
      | some (s, _, acts, o) => (s, fun h => (acts h).1, o.getD false)

/-- **Syntactic Cell-Support Bound & Locality of `evalConeTree` (`Problem 9.4`).**
For any `M : Transpose.TM` with `1 ≤ M.k` and any depth-`D` `CausalConeTree`, `treeCellSupport tree`
has at most `(M.k + 1)^D` cells and `evalConeTree M Y tree` depends only on `Y` restricted to
`treeCellSupport tree`. -/
theorem evalConeTree_cellSupport (M : Transpose.TM) {d D : ℕ} [DecidableEq (ZMod d)]
    (hk : 1 ≤ M.k)
    (tree : CausalConeTree (Fin (M.q + 1)) (Fin (M.g + 1)) M.k (Transpose.entryBits d) d D) :
    (treeCellSupport tree).card ≤ (M.k + 1) ^ D ∧
      ∀ Y₁ Y₂ : State d (CanonicalWordAlphabet d),
        (∀ q ∈ treeCellSupport tree, Y₁ q.1 q.2 = Y₂ q.1 q.2) →
        evalConeTree M Y₁ tree = evalConeTree M Y₂ tree := by
  refine ⟨?_, ?_⟩
  · have h := treeCellSupport_card_succ_le hk tree
    omega
  · induction tree with
    | leafInit _ _ => intro _ _ _; rfl
    | leafCut _ => intro _ _ _; rfl
    | stepNode readOpt stTree wkTrees ihSt ihWk =>
      intro Y₁ Y₂ hAgree
      have hStEq : evalConeTree M Y₁ stTree = evalConeTree M Y₂ stTree :=
        ihSt Y₁ Y₂ fun q hq => hAgree q <|
          Finset.mem_union_left _ (Finset.mem_union_right _ hq)
      have hWkEq : ∀ h, evalConeTree M Y₁ (wkTrees h) = evalConeTree M Y₂ (wkTrees h) :=
        fun h => ihWk h Y₁ Y₂ fun q hq => hAgree q <|
          Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨h, Finset.mem_univ h, hq⟩)
      have hInEq : evalReadOpt Y₁ readOpt = evalReadOpt Y₂ readOpt := by
        cases readOpt with
        | none => rfl
        | some ruℓ =>
          rcases ruℓ with ⟨r, u, ℓ⟩
          have hMem : (r, u) ∈ treeCellSupport (.stepNode (some (r, u, ℓ)) stTree wkTrees) :=
            Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton_self _))
          exact congrArg some (congrFun (hAgree (r, u) hMem) ℓ)
      simp only [evalConeTree, hStEq, hWkEq, hInEq]


/-! ### 2. Frozen-Fibre `CausalConeTree` Extraction & Exact `M.δ` Agreement -/

private theorem nth_eq_getElem? : ∀ (xs : List Bool) (i : ℕ), Transpose.nth xs i = xs[i]?
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: bs, i + 1 => by
    simpa only [Transpose.nth, List.getElem?_cons_succ] using nth_eq_getElem? bs i

private theorem mul_add_div_mod {q s r : ℕ} (hr : r < s) :
    (q * s + r) / s = q ∧ (q * s + r) % s = r := by
  have hs : 0 < s := by omega
  have heq : q * s + r = r + s * q := by ring
  rw [heq, Nat.add_mul_div_left r q hs, Nat.div_eq_of_lt hr, zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
  exact ⟨rfl, rfl⟩

private theorem concatUpTo_length_and_getElem? {f : ℕ → List Bool} {m s : ℕ}
    (hlen : ∀ k < m, (f k).length = s) :
    (Transpose.concatUpTo f m).length = m * s ∧
      ∀ idx < m * s, (Transpose.concatUpTo f m)[idx]? = (f (idx / s))[idx % s]? := by
  induction m with
  | zero => exact ⟨by simp [Transpose.concatUpTo], fun _ h => by simp at h⟩
  | succ m ih =>
    obtain ⟨ihLen, ihGet⟩ := ih (fun k hk => hlen k (Nat.lt_succ_of_lt hk))
    have hfmLen : (f m).length = s := hlen m (Nat.lt_succ_self m)
    refine ⟨by simp only [Transpose.concatUpTo, List.length_append, ihLen, hfmLen]; ring, ?_⟩
    intro idx hidx
    simp only [Transpose.concatUpTo]
    by_cases hlt : idx < m * s
    · rw [List.getElem?_append_left (by omega)]; exact ihGet idx hlt
    · rw [List.getElem?_append_right (by omega), ihLen]
      have hremLt : idx - m * s < s := by
        have : (m + 1) * s = m * s + s := by ring
        omega
      have hIdx : idx = m * s + (idx - m * s) := by omega
      obtain ⟨hDivEq, hModEq⟩ := mul_add_div_mod hremLt
      rw [← hIdx] at hDivEq hModEq
      rw [hDivEq, hModEq]

private theorem encode_length_and_getElem? (d b : ℕ) (A : Transpose.Matrix) :
    (Transpose.encode d b A).length = d * d * b ∧
      ∀ idx < d * d * b,
        (Transpose.encode d b A)[idx]? =
          some (A (idx / (d * b)) ((idx % (d * b)) / b) ((idx % (d * b)) % b)) := by
  let g₂ (i j : ℕ) : List Bool := Transpose.concatUpTo (fun t => [A i j t]) b
  have hg₂ : ∀ i j, (g₂ i j).length = b ∧ ∀ t < b, (g₂ i j)[t]? = some (A i j t) := by
    intro i j
    obtain ⟨hL, hG⟩ := concatUpTo_length_and_getElem? (f := fun t => [A i j t]) (m := b) (s := 1)
      (fun _ _ => rfl)
    exact ⟨by simpa using hL, fun t ht => by simpa [g₂, Nat.mod_one] using hG t (by simpa using ht)⟩
  let g₁ (i : ℕ) : List Bool := Transpose.concatUpTo (g₂ i) d
  have hg₁ : ∀ i, (g₁ i).length = d * b ∧
      ∀ rem < d * b, (g₁ i)[rem]? = some (A i (rem / b) (rem % b)) := by
    intro i
    obtain ⟨hL, hG⟩ := concatUpTo_length_and_getElem? (f := g₂ i) (m := d) (s := b)
      (fun j _ => (hg₂ i j).1)
    refine ⟨hL, fun rem hrem => ?_⟩
    have hbPos : 0 < b := by
      by_contra hb0; rw [show b = 0 by omega, mul_zero] at hrem; exact Nat.not_lt_zero rem hrem
    rw [hG rem hrem, (hg₂ i (rem / b)).2 (rem % b) (Nat.mod_lt rem hbPos)]
  obtain ⟨hL, hG⟩ := concatUpTo_length_and_getElem? (f := g₁) (m := d) (s := d * b)
    (fun i _ => (hg₁ i).1)
  refine ⟨by simpa only [Transpose.encode, g₁, g₂, (Nat.mul_assoc d d b).symm] using hL, ?_⟩
  intro idx hidx
  have hidx' : idx < d * (d * b) := by rwa [← Nat.mul_assoc]
  have hdbPos : 0 < d * b := by
    by_contra h0; rw [show d * b = 0 by omega, mul_zero] at hidx'; exact Nat.not_lt_zero idx hidx'
  change (Transpose.concatUpTo g₁ d)[idx]? = _
  rw [hG idx hidx', (hg₁ (idx / (d * b))).2 (idx % (d * b)) (Nat.mod_lt idx hdbPos)]

private theorem stepN_add (M : Transpose.TM) (w : List Bool) :
    ∀ (a b : ℕ) (c : Transpose.Config M),
      Transpose.stepN M w (a + b) c =
        match Transpose.stepN M w a c with
        | none => none
        | some c' => Transpose.stepN M w b c'
  | 0, _, _ => by simp [Transpose.stepN]
  | a + 1, b, c => by
    rw [Nat.succ_add]; simp only [Transpose.stepN]
    cases Transpose.step M w c with
    | none => rfl
    | some c' => exact stepN_add M w a b c'

private theorem tmCfgAt_succ {M : Transpose.TM} {w : List Bool} {t : ℕ} {cfg : Transpose.Config M}
    (h : tmCfgAt M w t = some cfg) :
    tmCfgAt M w (t + 1) = Transpose.step M w cfg := by
  unfold tmCfgAt at h ⊢
  rw [stepN_add M w t 1 (Transpose.init M), h]; simp only [Transpose.stepN]
  cases Transpose.step M w cfg <;> rfl

private theorem outRev_reverse_prefix_of_stepN (M : Transpose.TM) (w : List Bool) :
    ∀ (n : ℕ) (c c' : Transpose.Config M),
      Transpose.stepN M w n c = some c' → c.outRev.reverse <+: c'.outRev.reverse
  | 0, c, c', h => by
    simp only [Transpose.stepN, Option.some.injEq] at h; subst h; exact List.prefix_refl _
  | n + 1, c, c', h => by
    simp only [Transpose.stepN] at h
    cases hs : Transpose.step M w c <;> rw [hs] at h
    · cases h
    · rename_i cmid
      have h1 : c.outRev.reverse <+: cmid.outRev.reverse := by
        unfold Transpose.step at hs
        cases hδ : M.δ c.state (Transpose.readInput w c.inPos) (fun i => c.work i (c.workPos i)) <;>
          rw [hδ] at hs
        · cases hs
        · rename_i val
          rcases val with ⟨_, _, _, o⟩
          simp only [Option.some.injEq] at hs; subst hs
          cases o with
          | none => exact List.prefix_refl _
          | some bit => simp only [List.reverse_cons]; exact ⟨[bit], rfl⟩
      exact h1.trans (outRev_reverse_prefix_of_stepN M w n cmid c' h)

private theorem work_preserved_between {M : Transpose.TM} {d T : ℕ} [NeZero d]
    {inPos : ℕ → Int} {workPos : ℕ → Fin M.k → Int}
    {emitStep : Fin (Transpose.inputLength d) → ℕ} {Γ : Finset ℕ}
    {C : Set (State d (CanonicalWordAlphabet d))}
    (hFibre : IsFrozenTraceCutFibre M d T inPos workPos emitStep Γ C)
    {X : State d (CanonicalWordAlphabet d)} (hX : X ∈ C) (h : Fin M.k) (pos : Int) :
    ∀ {t₁ t₂ : ℕ}, t₁ ≤ t₂ → t₂ ≤ T →
      (∀ w : ℕ, t₁ ≤ w → w < t₂ → workPos w h ≠ pos) →
      ∀ (cfg₁ cfg₂ : Transpose.Config M),
        tmCfgAt M (encodeCanonicalState X) t₁ = some cfg₁ →
        tmCfgAt M (encodeCanonicalState X) t₂ = some cfg₂ →
        cfg₂.work h pos = cfg₁.work h pos := by
  intro t₁ t₂ hle ht₂T hnoVisit cfg₁ cfg₂ hcfg₁ hcfg₂
  induction t₂ generalizing cfg₂ with
  | zero =>
    have ht₁0 : t₁ = 0 := by omega
    subst ht₁0
    rw [hcfg₁] at hcfg₂; injection hcfg₂ with hEq; rw [hEq]
  | succ t₂ ih =>
    by_cases hEqT : t₁ = t₂ + 1
    · subst hEqT; rw [hcfg₁] at hcfg₂; injection hcfg₂ with hEq; rw [hEq]
    · obtain ⟨cfgMid, hcfgMid, _, hworkPosMid⟩ := hFibre.2.2.2.1 X hX t₂ (by omega)
      have hMidEq := ih (by omega) (by omega) (fun w hw₁ hw₂ => hnoVisit w hw₁ (by omega))
        cfgMid hcfgMid
      have hStep : Transpose.step M (encodeCanonicalState X) cfgMid = some cfg₂ := by
        rw [← tmCfgAt_succ hcfgMid]; exact hcfg₂
      unfold Transpose.step at hStep
      cases hδ : M.δ cfgMid.state (Transpose.readInput (encodeCanonicalState X) cfgMid.inPos)
          (fun i => cfgMid.work i (cfgMid.workPos i)) <;> rw [hδ] at hStep
      · cases hStep
      · rename_i val
        rcases val with ⟨_, _, _, _⟩
        simp only [Option.some.injEq] at hStep; subst hStep
        have hne : pos ≠ cfgMid.workPos h := by
          rw [congrFun hworkPosMid h]; exact (hnoVisit t₂ (by omega) (Nat.lt_succ_self t₂)).symm
        simp only [hne, ite_false]; exact hMidEq

/-- Output tape index of bit `ℓ` of transposed matrix entry `(r, c)`. -/
def outputBitIdx (d : ℕ) [NeZero d] (r c : ZMod d) (ℓ : Fin (Transpose.entryBits d)) :
    Fin (Transpose.inputLength d) :=
  let b := Transpose.entryBits d
  ⟨r.val * (d * b) + c.val * b + ℓ.val, by
    have hr : r.val + 1 ≤ d := r.val_lt
    have hc : c.val + 1 ≤ d := c.val_lt
    have hcb : c.val * b + ℓ.val < d * b :=
      calc c.val * b + ℓ.val < c.val * b + b := Nat.add_lt_add_left ℓ.isLt _
        _ = (c.val + 1) * b := by ring
        _ ≤ d * b := Nat.mul_le_mul_right b hc
    unfold Transpose.inputLength
    calc r.val * (d * b) + c.val * b + ℓ.val < r.val * (d * b) + d * b := by omega
      _ = (r.val + 1) * (d * b) := by ring
      _ ≤ d * (d * b) := Nat.mul_le_mul_right (d * b) hr
      _ = d * d * b := (Nat.mul_assoc d d b).symm⟩

/-- Relative `(row, col - c, bit)` input coordinate read at input head position `p : Int` in column
view `rot c X` (`none` if `p` lies on an end-marker outside `[0, L)`). -/
def relInputReadOfPos (d : ℕ) [NeZero d] (c : ZMod d) (p : Int) :
    Option (ZMod d × ZMod d × Fin (Transpose.entryBits d)) :=
  if _hp : 0 ≤ p ∧ p.toNat < Transpose.inputLength d then
    let b := Transpose.entryBits d
    have hb : 0 < b := by dsimp [b, Transpose.entryBits]; omega
    some (((p.toNat / (d * b) : ℕ) : ZMod d),
          (((p.toNat % (d * b)) / b : ℕ) : ZMod d) - c,
          ⟨(p.toNat % (d * b)) % b, Nat.mod_lt _ hb⟩)
  else none

private theorem evalReadOpt_relInputReadOfPos {d : ℕ} [NeZero d]
    (X : State d (CanonicalWordAlphabet d)) (c : ZMod d) (p : Int) :
    evalReadOpt (rot c X) (relInputReadOfPos d c p) =
      Transpose.readInput (encodeCanonicalState X) p := by
  unfold Transpose.readInput relInputReadOfPos
  by_cases hp0 : p < 0
  · have hNot : ¬ (0 ≤ p ∧ p.toNat < Transpose.inputLength d) := fun h => by omega
    simp [hp0, hNot, evalReadOpt]
  · rw [ite_eq_right hp0, nth_eq_getElem?]
    have hpNonneg : 0 ≤ p := Int.le_of_not_gt hp0
    let b := Transpose.entryBits d
    have hLen := (encode_length_and_getElem? d b (stateToTMMatrix X)).1
    by_cases hpL : p.toNat < Transpose.inputLength d
    · rw [dite_eq_left ⟨hpNonneg, hpL⟩]
      have hG := (encode_length_and_getElem? d b (stateToTMMatrix X)).2 p.toNat hpL
      change some ((rot c X) _ _ _) = (Transpose.encode d b (stateToTMMatrix X))[p.toNat]?
      rw [hG]; congr 1
      have hb : 0 < b := by dsimp [b, Transpose.entryBits]; omega
      have htLt : (p.toNat % (d * b)) % b < Transpose.entryBits d := Nat.mod_lt _ hb
      simp only [rot_apply, sub_add_cancel, stateToTMMatrix, dite_eq_left htLt]
      rfl
    · have hNot : ¬ (0 ≤ p ∧ p.toNat < Transpose.inputLength d) := fun h => hpL h.2
      rw [dite_eq_right hNot]
      change none = (Transpose.encode d b (stateToTMMatrix X))[p.toNat]?
      exact (List.getElem?_eq_none (hLen ▸ Nat.le_of_not_gt hpL)).symm

/-- Most recent step `u < v` visiting work-tape cell `workPos v h` on tape `h`, if any. -/
def lastWorkVisitStep {k : ℕ} (workPos : ℕ → Fin k → Int)
    (h : Fin k) (v : ℕ) : Option ℕ :=
  if hS : ((Finset.range v).filter (fun u => workPos u h = workPos v h)).Nonempty then
    some (((Finset.range v).filter (fun u => workPos u h = workPos v h)).max' hS)
  else none

private theorem lastWorkVisitStep_none_iff {k : ℕ} {workPos : ℕ → Fin k → Int}
    {h : Fin k} {v : ℕ} (hNone : lastWorkVisitStep workPos h v = none) :
    ∀ u < v, workPos u h ≠ workPos v h := by
  unfold lastWorkVisitStep at hNone
  by_cases hS : ((Finset.range v).filter (fun u => workPos u h = workPos v h)).Nonempty
  · rw [dite_eq_left hS] at hNone; cases hNone
  · intro u huv hEq
    exact hS ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr huv, hEq⟩⟩

private theorem lastWorkVisitStep_some {k : ℕ} {workPos : ℕ → Fin k → Int}
    {h : Fin k} {v u : ℕ} (hSome : lastWorkVisitStep workPos h v = some u) :
    IsLastWorkVisit workPos h u v := by
  unfold lastWorkVisitStep at hSome
  by_cases hS : ((Finset.range v).filter (fun u => workPos u h = workPos v h)).Nonempty
  · rw [dite_eq_left hS, Option.some.injEq] at hSome; subst hSome
    have hMem := Finset.max'_mem _ hS
    simp only [Finset.mem_filter, Finset.mem_range] at hMem
    refine ⟨hMem.1, hMem.2, fun w hw₁ hw₂ hEq => ?_⟩
    have hwLe := Finset.le_max' ((Finset.range v).filter (fun u => workPos u h = workPos v h)) w
      (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hw₂, hEq⟩)
    omega
  · rw [dite_eq_right hS] at hSome; cases hSome

/-- Extract the depth-`D` `CausalConeTree` of step `v` relative to column `c` from a frozen head
schedule `(inPos, workPos)` and cut label assignment `cutVal`. -/
def traceConeTree (M : Transpose.TM) (d : ℕ) [NeZero d]
    (inPos : ℕ → Int) (workPos : ℕ → Fin M.k → Int) (Γ : Finset ℕ)
    (cutVal : ℕ → Fin (M.q + 1) × (Fin M.k → Fin (M.g + 1))) (c : ZMod d) :
    ∀ (D : ℕ), ℕ →
      CausalConeTree (Fin (M.q + 1)) (Fin (M.g + 1)) M.k (Transpose.entryBits d) d D
  | 0, _ => .leafInit 0 (fun _ => 0)
  | m + 1, v =>
      let stTree :=
        match v with
        | 0 => .leafInit 0 (fun _ => 0)
        | u + 1 =>
            if u ∈ Γ then .leafCut (cutVal u)
            else traceConeTree M d inPos workPos Γ cutVal c m u
      let wkTrees := fun h : Fin M.k =>
        match lastWorkVisitStep workPos h v with
        | none => .leafInit 0 (fun _ => 0)
        | some u =>
            if u ∈ Γ then .leafCut (cutVal u)
            else traceConeTree M d inPos workPos Γ cutVal c m u
      .stepNode (relInputReadOfPos d c (inPos v)) stTree wkTrees


private theorem emittedBit_eq_entry {M : Transpose.TM} {d T : ℕ} [NeZero d]
    {inPos : ℕ → Int} {workPos : ℕ → Fin M.k → Int}
    {emitStep : Fin (Transpose.inputLength d) → ℕ} {Γ : Finset ℕ}
    {C : Set (State d (CanonicalWordAlphabet d))}
    (hFibre : IsFrozenTraceCutFibre M d T inPos workPos emitStep Γ C)
    {X : State d (CanonicalWordAlphabet d)} (hX : X ∈ C)
    (r c : ZMod d) (ℓ : Fin (Transpose.entryBits d))
    (cfgPre : Transpose.Config M)
    (hcfgPre : tmCfgAt M (encodeCanonicalState X) (emitStep (outputBitIdx d r c ℓ)) = some cfgPre) :
    match M.δ cfgPre.state (Transpose.readInput (encodeCanonicalState X) cfgPre.inPos)
        (fun i => cfgPre.work i (cfgPre.workPos i)) with
    | some (_, _, _, some bit) => bit = X c r ℓ
    | _ => False := by
  let idx := outputBitIdx d r c ℓ
  obtain ⟨cEnd, hcEnd, _, houtEnd⟩ := hFibre.2.2.1 X hX
  obtain ⟨cfgPre', cfgPost, hcfgPre', hcfgPost, hlenPre, hlenPost⟩ := hFibre.2.2.2.2.1 X hX idx
  rw [hcfgPre] at hcfgPre'; injection hcfgPre' with hEqPre; subst hEqPre
  have hEmitLtT : emitStep idx < T := hFibre.2.1 idx
  have hStep : Transpose.step M (encodeCanonicalState X) cfgPre = some cfgPost := by
    rw [← tmCfgAt_succ hcfgPre]; exact hcfgPost
  have hStepNRem :
      Transpose.stepN M (encodeCanonicalState X) (T - (emitStep idx + 1)) cfgPost = some cEnd := by
    have hSplit := stepN_add M (encodeCanonicalState X)
      (emitStep idx + 1) (T - (emitStep idx + 1)) (Transpose.init M)
    rw [show (emitStep idx + 1) + (T - (emitStep idx + 1)) = T by omega] at hSplit
    change tmCfgAt M (encodeCanonicalState X) T = _ at hSplit
    rw [hcEnd, show Transpose.stepN M (encodeCanonicalState X) (emitStep idx + 1)
      (Transpose.init M) = some cfgPost from hcfgPost] at hSplit
    exact hSplit.symm
  have hPrefix := outRev_reverse_prefix_of_stepN M (encodeCanonicalState X) _ cfgPost cEnd hStepNRem
  unfold Transpose.step at hStep
  cases hδ : M.δ cfgPre.state (Transpose.readInput (encodeCanonicalState X) cfgPre.inPos)
      (fun i => cfgPre.work i (cfgPre.workPos i)) <;> rw [hδ] at hStep
  · cases hStep
  · rename_i val; rcases val with ⟨_, _, _, o⟩; simp only [Option.some.injEq] at hStep
    cases o with
    | none => subst hStep; simp only at hlenPost; omega
    | some bit =>
      have hOutPost : cfgPost.outRev = bit :: cfgPre.outRev := by rw [← hStep]
      have hPostGet : (cfgPost.outRev.reverse)[idx.val]? = some bit := by
        rw [hOutPost, List.reverse_cons]
        have hRevLen : cfgPre.outRev.reverse.length = idx.val := by
          rw [List.length_reverse]; exact hlenPre
        rw [List.getElem?_append_right (by omega), hRevLen, Nat.sub_self]; rfl
      obtain ⟨_, hTail⟩ := hPrefix
      have hEndGet : (cEnd.outRev.reverse)[idx.val]? = some bit := by
        rw [← hTail, List.getElem?_append_left (by rw [List.length_reverse]; omega)]; exact hPostGet
      rw [houtEnd] at hEndGet
      let b := Transpose.entryBits d
      have hEncGet := (encode_length_and_getElem? d b (Transpose.transpose (stateToTMMatrix X))).2
        idx.val (by simpa [Transpose.inputLength, b] using idx.isLt)
      rw [hEncGet, Option.some.injEq] at hEndGet
      have hcbLt : c.val * b + ℓ.val < d * b :=
        calc c.val * b + ℓ.val < c.val * b + b := Nat.add_lt_add_left ℓ.isLt _
          _ = (c.val + 1) * b := by ring
          _ ≤ d * b := Nat.mul_le_mul_right b c.val_lt
      have hIdxEq : idx.val = r.val * (d * b) + (c.val * b + ℓ.val) := by
        change r.val * (d * b) + c.val * b + ℓ.val = _; ring
      obtain ⟨hDiv₁, hMod₁⟩ := mul_add_div_mod hcbLt
      rw [← hIdxEq] at hDiv₁ hMod₁
      obtain ⟨hDiv₂, hMod₂⟩ := mul_add_div_mod ℓ.isLt
      rw [hDiv₁, hMod₁, hDiv₂, hMod₂] at hEndGet
      simpa only [Transpose.transpose, stateToTMMatrix, dite_eq_left ℓ.isLt,
        ZMod.natCast_zmod_val, Fin.eta] using hEndGet.symm

private theorem pred_depth_pred {k : ℕ} {workPos : ℕ → Fin k → Int} {T : ℕ} {Γ : Finset ℕ}
    {u v n : ℕ} (huT : u < T) (hDep : TMDepStep workPos T u v) (huΓ : u ∉ Γ)
    (hPath : ∀ π : List ℕ, IsCutFreeCausalPath workPos T Γ π → π.head? = some v →
      π.length ≤ n + 1) :
    1 ≤ n ∧ ∀ π : List ℕ, IsCutFreeCausalPath workPos T Γ π → π.head? = some u →
      π.length ≤ n := by
  refine ⟨?_, ?_⟩
  · have h2 := hPath [v, u] ⟨hDep, huΓ, huT⟩ rfl
    simp only [List.length_cons, List.length_nil] at h2; omega
  · intro π hπ hhd
    cases π with
    | nil => simp at hhd
    | cons w rest =>
      simp only [List.head?_cons, Option.some.injEq] at hhd; subst w
      have hlen := hPath (v :: u :: rest) ⟨hDep, huΓ, hπ⟩ rfl
      simp only [List.length_cons] at hlen ⊢; omega

/-- **Exact Agreement Between `evalConeTree` (`M.δ`) and Live `Transpose.TM` Execution.**
On `IsFrozenTraceCutFibre M d T inPos workPos emitStep Γ C`, for every `X ∈ C`, column `c`, and
step `v < T` whose `Γ`-free causal paths have length `≤ D` (`1 ≤ D`), evaluating `traceConeTree`
on `rot c X` via `evalConeTree M` reproduces `M`'s exact post-step `(state, writtenWork)` at `v + 1`
and, when `v = emitStep (outputBitIdx d r c ℓ)`, outputs `X c r ℓ`. -/
theorem evalConeTree_traceConeTree_eq (M : Transpose.TM) {d T : ℕ} [NeZero d]
    {inPos : ℕ → Int} {workPos : ℕ → Fin M.k → Int}
    {emitStep : Fin (Transpose.inputLength d) → ℕ} {Γ : Finset ℕ}
    {C : Set (State d (CanonicalWordAlphabet d))}
    (hFibre : IsFrozenTraceCutFibre M d T inPos workPos emitStep Γ C)
    (cutVal : ℕ → Fin (M.q + 1) × (Fin M.k → Fin (M.g + 1)))
    (hCutVal : ∀ X ∈ C, ∀ u ∈ Γ, ∀ cfg : Transpose.Config M,
      tmCfgAt M (encodeCanonicalState X) (u + 1) = some cfg →
      cfg.state = (cutVal u).1 ∧ ∀ h, cfg.work h (workPos u h) = (cutVal u).2 h)
    {X : State d (CanonicalWordAlphabet d)} (hX : X ∈ C) (c : ZMod d) :
    ∀ {D : ℕ}, 1 ≤ D → ∀ v < T,
      (∀ π : List ℕ, IsCutFreeCausalPath workPos T Γ π → π.head? = some v → π.length ≤ D) →
      (∀ cfgPost : Transpose.Config M,
        tmCfgAt M (encodeCanonicalState X) (v + 1) = some cfgPost →
        (evalConeTree M (rot c X) (traceConeTree M d inPos workPos Γ cutVal c D v)).1 =
          cfgPost.state ∧
        (evalConeTree M (rot c X) (traceConeTree M d inPos workPos Γ cutVal c D v)).2.1 =
          fun h => cfgPost.work h (workPos v h)) ∧
      (∀ (r : ZMod d) (ℓ : Fin (Transpose.entryBits d)),
        v = emitStep (outputBitIdx d r c ℓ) →
        (evalConeTree M (rot c X) (traceConeTree M d inPos workPos Γ cutVal c D v)).2.2 =
          X c r ℓ)
  | 0, hD, _, _, _ => absurd hD (by decide)
  | n + 1, _, v, hvT, hPath => by
    obtain ⟨cfgPre, hcfgPre, hinPre, hwposPre⟩ := hFibre.2.2.2.1 X hX v (Nat.le_of_lt hvT)
    have hStEq : (evalConeTree M (rot c X)
        (match v with
         | 0 => .leafInit 0 (fun _ => 0)
         | u + 1 => if u ∈ Γ then .leafCut (cutVal u)
                    else traceConeTree M d inPos workPos Γ cutVal c n u)).1 = cfgPre.state := by
      cases v with
      | zero =>
        simp only [tmCfgAt, Transpose.stepN, Option.some.injEq] at hcfgPre
        rw [← hcfgPre]; rfl
      | succ u =>
        dsimp only
        by_cases huΓ : u ∈ Γ
        · rw [ite_eq_left huΓ]; exact (hCutVal X hX u huΓ cfgPre hcfgPre).1.symm
        · rw [ite_eq_right huΓ]
          obtain ⟨hn, hPathU⟩ := pred_depth_pred (by omega) ⟨hvT, Or.inl rfl⟩ huΓ hPath
          exact ((evalConeTree_traceConeTree_eq M hFibre cutVal hCutVal hX c hn u
            (by omega) hPathU).1 cfgPre hcfgPre).1
    have hWkEq : (fun h : Fin M.k => (evalConeTree M (rot c X)
        (match lastWorkVisitStep workPos h v with
         | none => .leafInit 0 (fun _ => 0)
         | some u => if u ∈ Γ then .leafCut (cutVal u)
                     else traceConeTree M d inPos workPos Γ cutVal c n u)).2.1 h) =
        fun h => cfgPre.work h (cfgPre.workPos h) := by
      funext h
      rw [congrFun hwposPre h]
      cases hLastOpt : lastWorkVisitStep workPos h v with
      | none =>
        have hw₀ := work_preserved_between hFibre hX h (workPos v h) (Nat.zero_le v)
          (Nat.le_of_lt hvT) (fun w _ hwv => lastWorkVisitStep_none_iff hLastOpt w hwv)
          (Transpose.init M) cfgPre rfl hcfgPre
        exact hw₀.symm
      | some u =>
        dsimp only
        have hLast := lastWorkVisitStep_some hLastOpt
        have huv : u < v := hLast.1
        obtain ⟨cfgPostU, hcfgPostU, _, _⟩ := hFibre.2.2.2.1 X hX (u + 1) (by omega)
        have hwU := work_preserved_between hFibre hX h (workPos v h) hLast.1
          (Nat.le_of_lt hvT) (fun w hw₁ hw₂ => hLast.2.2 w hw₁ hw₂) cfgPostU cfgPre hcfgPostU hcfgPre
        rw [hwU, ← hLast.2.1]
        by_cases huΓ : u ∈ Γ
        · rw [ite_eq_left huΓ]; exact ((hCutVal X hX u huΓ cfgPostU hcfgPostU).2 h).symm
        · rw [ite_eq_right huΓ]
          obtain ⟨hn, hPathU⟩ := pred_depth_pred (Nat.lt_trans huv hvT)
            ⟨hvT, Or.inr ⟨h, hLast⟩⟩ huΓ hPath
          exact congrFun ((evalConeTree_traceConeTree_eq M hFibre cutVal hCutVal hX c hn u
            (Nat.lt_trans huv hvT) hPathU).1 cfgPostU hcfgPostU).2 h
    have hInEq : evalReadOpt (rot c X) (relInputReadOfPos d c (inPos v)) =
        Transpose.readInput (encodeCanonicalState X) cfgPre.inPos := by
      rw [hinPre, evalReadOpt_relInputReadOfPos]
    refine ⟨fun cfgPost hcfgPost => ?_, fun r ℓ hvEmit => ?_⟩
    · have hStep : Transpose.step M (encodeCanonicalState X) cfgPre = some cfgPost := by
        rw [← tmCfgAt_succ hcfgPre]; exact hcfgPost
      simp only [traceConeTree, evalConeTree, hStEq, hInEq, hWkEq]
      unfold Transpose.step at hStep
      cases hδ : M.δ cfgPre.state (Transpose.readInput (encodeCanonicalState X) cfgPre.inPos)
          (fun i => cfgPre.work i (cfgPre.workPos i)) <;> rw [hδ] at hStep
      · cases hStep
      · rename_i val; rcases val with ⟨s, _, acts, _⟩
        simp only [Option.some.injEq] at hStep; subst hStep
        refine ⟨rfl, funext fun h => ?_⟩
        simp [congrFun hwposPre h]
    · subst hvEmit
      simp only [traceConeTree, evalConeTree, hStEq, hInEq, hWkEq]
      have hBit := emittedBit_eq_entry hFibre hX r c ℓ cfgPre hcfgPre
      cases hδ : M.δ cfgPre.state (Transpose.readInput (encodeCanonicalState X) cfgPre.inPos)
          (fun i => cfgPre.work i (cfgPre.workPos i)) <;> rw [hδ] at hBit
      · exact False.elim hBit
      · rename_i val; rcases val with ⟨_, _, _, o⟩
        cases o with
        | none => exact False.elim hBit
        | some bit => exact hBit

/-- Canonical extraction of the frozen post-step `(state, writtenWork)` labels on `Γ` for a
frozen-trace cut fibre `C` (defaulting to `(0, 0)` when `C` is empty). -/
noncomputable def fibreCutLabels (M : Transpose.TM) (d : ℕ) [NeZero d]
    (workPos : ℕ → Fin M.k → Int)
    (C : Set (State d (CanonicalWordAlphabet d))) (u : ℕ) :
    Fin (M.q + 1) × (Fin M.k → Fin (M.g + 1)) :=
  @dite _ C.Nonempty (Classical.propDecidable _)
    (fun hC =>
      match tmCfgAt M (encodeCanonicalState (Classical.choose hC)) (u + 1) with
      | some cfg => (cfg.state, fun h => cfg.work h (workPos u h))
      | none => (0, fun _ => 0))
    (fun _ => (0, fun _ => 0))

private theorem fibreCutLabels_spec {M : Transpose.TM} {d T : ℕ} [NeZero d]
    {inPos : ℕ → Int} {workPos : ℕ → Fin M.k → Int}
    {emitStep : Fin (Transpose.inputLength d) → ℕ} {Γ : Finset ℕ}
    {C : Set (State d (CanonicalWordAlphabet d))}
    (hFibre : IsFrozenTraceCutFibre M d T inPos workPos emitStep Γ C) :
    ∀ X ∈ C, ∀ u ∈ Γ, ∀ cfg : Transpose.Config M,
      tmCfgAt M (encodeCanonicalState X) (u + 1) = some cfg →
      cfg.state = (fibreCutLabels M d workPos C u).1 ∧
        ∀ h, cfg.work h (workPos u h) = (fibreCutLabels M d workPos C u).2 h := by
  intro X hX u huΓ cfg hcfg
  have hC : C.Nonempty := ⟨X, hX⟩
  have hX₀ : Classical.choose hC ∈ C := Classical.choose_spec hC
  have huT : u < T := hFibre.1 u huΓ
  obtain ⟨cfg₀, hcfg₀, _, _⟩ := hFibre.2.2.2.1 _ hX₀ (u + 1) (by omega)
  unfold fibreCutLabels
  split_ifs
  rw [hcfg₀]
  exact hFibre.2.2.2.2.2 X hX _ hX₀ u huΓ cfg cfg₀ hcfg hcfg₀

/-- Cut-free depth-`D` `CausalConeTree` of step `v` relative to column `c`, terminating every leaf
at initial `(0, 0)` values without consulting any cut labels. -/
def cutFreeTraceConeTree (M : Transpose.TM) (d : ℕ) [NeZero d]
    (inPos : ℕ → Int) (workPos : ℕ → Fin M.k → Int) (c : ZMod d) (D v : ℕ) :
    CausalConeTree (Fin (M.q + 1)) (Fin (M.g + 1)) M.k (Transpose.entryBits d) d D :=
  traceConeTree M d inPos workPos ∅ (fun _ => (0, fun _ => 0)) c D v

/-- Output coordinates `(r, c)` whose `Γ`-truncated causal cone touches at least one cut step
`u ∈ Γ` along a direct `TMDepStep`. -/
noncomputable def cutTouchingOutputCells {k : ℕ} (d T : ℕ) [NeZero d]
    (workPos : ℕ → Fin k → Int)
    (emitStep : Fin (Transpose.inputLength d) → ℕ)
    (Γ : Finset ℕ) : Finset (ZMod d × ZMod d) :=
  @Finset.filter (ZMod d × ZMod d)
    (fun rc => ∃ (ℓ : Fin (Transpose.entryBits d)) (w u : ℕ),
      InCutCausalCone workPos T Γ (emitStep (outputBitIdx d rc.1 rc.2 ℓ)) w ∧
      u ∈ Γ ∧ TMDepStep workPos T u w)
    (fun _ => Classical.propDecidable _) Finset.univ

private theorem inCutCausalCone_step {k : ℕ} {workPos : ℕ → Fin k → Int} {T : ℕ} {Γ : Finset ℕ}
    {u v w : ℕ} (hDep : TMDepStep workPos T u v) (huΓ : u ∉ Γ)
    (hIn : InCutCausalCone workPos T Γ u w) :
    InCutCausalCone workPos T Γ v w := by
  rcases hIn with ⟨π, hhd, hlst, hπ⟩
  cases π with
  | nil => simp at hhd
  | cons x rest =>
    simp only [List.head?_cons, Option.some.injEq] at hhd; subst x
    exact ⟨v :: u :: rest, rfl, by simpa only [List.getLast?_cons_cons] using hlst,
      ⟨hDep, huΓ, hπ⟩⟩

private theorem traceConeTree_eq_cutFree (M : Transpose.TM) (d T : ℕ) [NeZero d]
    (inPos : ℕ → Int) (workPos : ℕ → Fin M.k → Int) (Γ : Finset ℕ)
    (cutVal : ℕ → Fin (M.q + 1) × (Fin M.k → Fin (M.g + 1))) (c : ZMod d) :
    ∀ (m v : ℕ), v < T →
      (∀ w u : ℕ, InCutCausalCone workPos T Γ v w → u ∈ Γ → ¬ TMDepStep workPos T u w) →
      traceConeTree M d inPos workPos Γ cutVal c m v =
        cutFreeTraceConeTree M d inPos workPos c m v
  | 0, _, _, _ => rfl
  | m + 1, v, hvT, hNoCut => by
    have hSelf : InCutCausalCone workPos T Γ v v := ⟨[v], rfl, rfl, hvT⟩
    unfold cutFreeTraceConeTree
    simp only [traceConeTree]
    congr 1
    · cases v with
      | zero => rfl
      | succ u =>
        dsimp only
        have hDep : TMDepStep workPos T u (u + 1) := ⟨hvT, Or.inl rfl⟩
        have huΓ : u ∉ Γ := fun hu => hNoCut (u + 1) u hSelf hu hDep
        have huEmpty : u ∉ (∅ : Finset ℕ) := by simp
        rw [ite_eq_right huΓ, ite_eq_right huEmpty]
        exact traceConeTree_eq_cutFree M d T inPos workPos Γ cutVal c m u (by omega)
          fun w u' hIn hu' hDep' => hNoCut w u' (inCutCausalCone_step hDep huΓ hIn) hu' hDep'
    · funext h
      cases hOpt : lastWorkVisitStep workPos h v with
      | none => rfl
      | some u =>
        dsimp only
        have hLast := lastWorkVisitStep_some hOpt
        have huv : u < v := hLast.1
        have hDep : TMDepStep workPos T u v := ⟨hvT, Or.inr ⟨h, hLast⟩⟩
        have huΓ : u ∉ Γ := fun hu => hNoCut v u hSelf hu hDep
        have huEmpty : u ∉ (∅ : Finset ℕ) := by simp
        rw [ite_eq_right huΓ, ite_eq_right huEmpty]
        exact traceConeTree_eq_cutFree M d T inPos workPos Γ cutVal c m u
          (Nat.lt_trans huv hvT)
          fun w u' hIn hu' hDep' => hNoCut w u' (inCutCausalCone_step hDep huΓ hIn) hu' hDep'

private theorem syntacticCellSupport_of_treeTemplates (M : Transpose.TM) {d M_cls D : ℕ}
    [DecidableEq (ZMod d)] (hk : 1 ≤ M.k)
    (tmpl : Fin M_cls → ZMod d → Fin (Transpose.entryBits d) →
      CausalConeTree (Fin (M.q + 1)) (Fin (M.g + 1)) M.k (Transpose.entryBits d) d D) :
    SyntacticCellSupport (Transpose.entryBits d * (M.k + 1) ^ D)
      (fun m Y r ℓ => (evalConeTree M Y (tmpl m r ℓ)).2.2)
      (fun m r => Finset.univ.biUnion (fun ℓ => treeCellSupport (tmpl m r ℓ))) := by
  refine ⟨fun m r => ?_, fun m r Y₁ Y₂ hAgree => funext fun ℓ => ?_⟩
  · calc (Finset.univ.biUnion (fun ℓ => treeCellSupport (tmpl m r ℓ))).card
        ≤ ∑ ℓ : Fin (Transpose.entryBits d), (treeCellSupport (tmpl m r ℓ)).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _ℓ : Fin (Transpose.entryBits d), (M.k + 1) ^ D :=
          Finset.sum_le_sum fun ℓ _ => (evalConeTree_cellSupport M hk (tmpl m r ℓ)).1
      _ = Transpose.entryBits d * (M.k + 1) ^ D := by simp
  · have hEq := (evalConeTree_cellSupport M hk (tmpl m r ℓ)).2 Y₁ Y₂ fun q hq =>
      hAgree q (Finset.mem_biUnion.mpr ⟨ℓ, Finset.mem_univ ℓ, hq⟩)
    exact congrArg (fun x => x.2.2) hEq

private theorem canonicalWord_card_ge_two (d : ℕ) :
    2 ≤ Fintype.card (CanonicalWordAlphabet d) := by
  rw [canonicalWordAlphabet_card]
  have hb : 1 ≤ Transpose.entryBits d := by unfold Transpose.entryBits; omega
  calc 2 = 2 ^ 1 := rfl
    _ ≤ 2 ^ Transpose.entryBits d := Nat.pow_le_pow_right (by decide) hb

/-- **Theorem A (`README.md` §III.3 Line 137 — Cut-Absorbed `Transpose.TM` Periodic Sweep
Extraction, Exact Class Count `M₀`).**
On `IsFrozenTraceCutFibre M d T inPos workPos emitStep Γ C` (`1 ≤ M.k`, `1 ≤ D`) with `Γ`-free
causal path length `≤ D`, if output cells outside `E = E_sched ∪ cutTouchingOutputCells ...` in the
same `p₀ c` class share cut-free relative `CausalConeTree` templates `template (p₀ c) r ℓ`, then
`M.δ` directly induces an `M₀`-class `IsBoundedAritySetCode` of cell cone arity
`Delta = entryBits d * (M.k + 1)^D` on the nonlinear fibre `C`, together with Theorem 1's capacity
upper bound. -/
theorem tmPeriodicSweepExtraction_cutAbsorbed (M : Transpose.TM) (d T M₀ D : ℕ) [NeZero d]
    (inPos : ℕ → Int) (workPos : ℕ → Fin M.k → Int)
    (emitStep : Fin (Transpose.inputLength d) → ℕ) (Γ : Finset ℕ)
    (C : Set (State d (CanonicalWordAlphabet d)))
    (p₀ : ZMod d → Fin M₀) (E_sched : Finset (ZMod d × ZMod d))
    (template : Fin M₀ → ZMod d → Fin (Transpose.entryBits d) →
      CausalConeTree (Fin (M.q + 1)) (Fin (M.g + 1)) M.k (Transpose.entryBits d) d D)
    (hk : 1 ≤ M.k) (hD : 1 ≤ D)
    (hFibre : IsFrozenTraceCutFibre M d T inPos workPos emitStep Γ C)
    (hPathLen : ∀ π : List ℕ, IsCutFreeCausalPath workPos T Γ π → π.length ≤ D)
    (hPeriodic : ∀ (r c : ZMod d),
      (r, c) ∉ E_sched ∪ cutTouchingOutputCells d T workPos emitStep Γ →
      ∀ ℓ : Fin (Transpose.entryBits d),
        cutFreeTraceConeTree M d inPos workPos c D (emitStep (outputBitIdx d r c ℓ)) =
          template (p₀ c) r ℓ) :
    let Delta := Transpose.entryBits d * (M.k + 1) ^ D
    let E := E_sched ∪ cutTouchingOutputCells d T workPos emitStep Γ
    let f : Fin M₀ → State d (CanonicalWordAlphabet d) → (ZMod d → CanonicalWordAlphabet d) :=
      fun m Y r ℓ => (evalConeTree M Y (template m r ℓ)).2.2
    let Q : Fin M₀ → ZMod d → Finset (ZMod d × ZMod d) :=
      fun m r => Finset.univ.biUnion (fun ℓ => treeCellSupport (template m r ℓ))
    IsBoundedAritySetCode Delta p₀ E f Q C ∧
      (1 ≤ M₀ → C.Nonempty →
        Real.log (Nat.card C : ℝ) / Real.log (Fintype.card (CanonicalWordAlphabet d) : ℝ) ≤
          (d : ℝ) ^ 2 -
            ((d : ℝ) ^ 2 - (E.card : ℝ) - (d : ℝ) * (M₀ : ℝ) * (Delta : ℝ)) *
              ((Delta : ℝ) ^ Delta / ((Delta + 1 : ℝ) ^ (Delta + 1)))) := by
  dsimp only
  set Delta := Transpose.entryBits d * (M.k + 1) ^ D
  set E := E_sched ∪ cutTouchingOutputCells d T workPos emitStep Γ
  set f : Fin M₀ → State d (CanonicalWordAlphabet d) → (ZMod d → CanonicalWordAlphabet d) :=
    fun m Y r ℓ => (evalConeTree M Y (template m r ℓ)).2.2
  set Q : Fin M₀ → ZMod d → Finset (ZMod d × ZMod d) :=
    fun m r => Finset.univ.biUnion (fun ℓ => treeCellSupport (template m r ℓ))
  have hCode : IsBoundedAritySetCode Delta p₀ E f Q C := by
    refine ⟨syntacticCellSupport_of_treeTemplates M hk template, ?_⟩
    intro X hX r c hrcNotE
    funext ℓ
    have hNotCut : (r, c) ∉ cutTouchingOutputCells d T workPos emitStep Γ :=
      fun hMem => hrcNotE (Finset.mem_union_right _ hMem)
    have hNoTouch : ∀ w u : ℕ,
        InCutCausalCone workPos T Γ (emitStep (outputBitIdx d r c ℓ)) w →
        u ∈ Γ → ¬ TMDepStep workPos T u w := by
      intro w u hIn huΓ hDep
      apply hNotCut
      unfold cutTouchingOutputCells
      exact (@Finset.mem_filter _ _ (fun _ => Classical.propDecidable _) Finset.univ (r, c)).mpr
        ⟨Finset.mem_univ _, ℓ, w, u, hIn, huΓ, hDep⟩
    have hvT : emitStep (outputBitIdx d r c ℓ) < T := hFibre.2.1 _
    have hEqFree := traceConeTree_eq_cutFree M d T inPos workPos Γ
      (fibreCutLabels M d workPos C) c D (emitStep (outputBitIdx d r c ℓ)) hvT hNoTouch
    have hEval := (evalConeTree_traceConeTree_eq M hFibre (fibreCutLabels M d workPos C)
      (fibreCutLabels_spec hFibre) hX c hD (emitStep (outputBitIdx d r c ℓ)) hvT
      (fun π hπ _ => hPathLen π hπ)).2 r ℓ rfl
    change (evalConeTree M (rot c X) (template (p₀ c) r ℓ)).2.2 = X c r ℓ
    rw [← hPeriodic r c hrcNotE ℓ, ← hEqFree]
    exact hEval
  refine ⟨hCode, fun hM₀ hCne => ?_⟩
  have hDelta : 1 ≤ Delta := by
    have hb : 1 ≤ Transpose.entryBits d := by unfold Transpose.entryBits; omega
    exact Nat.mul_le_mul hb (Nat.one_le_pow _ _ (by omega))
  exact theorem1_BoundedAritySetCapacity.2 d M₀ Delta (CanonicalWordAlphabet d) p₀ E f Q C
    (canonicalWord_card_ge_two d) hM₀ hDelta hCne hCode

/-- Locate the first slot `s : Fin L` where `g s = u`, if any. -/
def findCutSlot : ∀ {L : ℕ}, (Fin L → ℕ) → ℕ → Option (Fin L)
  | 0, _, _ => none
  | _ + 1, g, u =>
      if g 0 = u then some 0
      else (findCutSlot (fun s => g s.succ) u).map Fin.succ

private theorem findCutSlot_spec : ∀ {L : ℕ} (g : Fin L → ℕ) (u : ℕ),
    (∃ s : Fin L, g s = u) → ∃ s₀ : Fin L, findCutSlot g u = some s₀ ∧ g s₀ = u
  | 0, _, _, ⟨s, _⟩ => s.elim0
  | _ + 1, g, u, ⟨s, hs⟩ => by
    by_cases h0 : g 0 = u
    · exact ⟨0, by simp [findCutSlot, h0], h0⟩
    · cases s using Fin.cases with
      | zero => exact absurd hs h0
      | succ s' =>
        obtain ⟨s₀, hs₀, hgs₀⟩ := findCutSlot_spec (fun i => g i.succ) u ⟨s', hs⟩
        exact ⟨s₀.succ, by simp [findCutSlot, h0, hs₀], hgs₀⟩

/-- Extract the symbolic depth-`D` `SlotConeTree` of step `v` relative to column `c`, recording
cut leaves via their local column slot index in `colCutStep c : Fin L_cut → ℕ`. -/
def traceSlotConeTree {L_cut : ℕ} (M : Transpose.TM) (d : ℕ) [NeZero d]
    (inPos : ℕ → Int) (workPos : ℕ → Fin M.k → Int) (Γ : Finset ℕ)
    (colCutStep : ZMod d → Fin L_cut → ℕ) (c : ZMod d) :
    ∀ (D : ℕ), ℕ →
      SlotConeTree L_cut (Fin (M.q + 1)) (Fin (M.g + 1)) M.k (Transpose.entryBits d) d D
  | 0, _ => .leafInit 0 (fun _ => 0)
  | m + 1, v =>
      let cutLeaf (u : ℕ) :
          SlotConeTree L_cut (Fin (M.q + 1)) (Fin (M.g + 1)) M.k (Transpose.entryBits d) d m :=
        match findCutSlot (colCutStep c) u with
        | some s => .leafCut s
        | none => .leafInit 0 (fun _ => 0)
      let stTree :=
        match v with
        | 0 => .leafInit 0 (fun _ => 0)
        | u + 1 =>
            if u ∈ Γ then cutLeaf u
            else traceSlotConeTree M d inPos workPos Γ colCutStep c m u
      let wkTrees := fun h : Fin M.k =>
        match lastWorkVisitStep workPos h v with
        | none => .leafInit 0 (fun _ => 0)
        | some u =>
            if u ∈ Γ then cutLeaf u
            else traceSlotConeTree M d inPos workPos Γ colCutStep c m u
      .stepNode (relInputReadOfPos d c (inPos v)) stTree wkTrees

private theorem mapCutLabels_traceSlotConeTree {L_cut : ℕ} (M : Transpose.TM) (d T : ℕ) [NeZero d]
    (inPos : ℕ → Int) (workPos : ℕ → Fin M.k → Int) (Γ : Finset ℕ)
    (colCutStep : ZMod d → Fin L_cut → ℕ)
    (cutVal : ℕ → Fin (M.q + 1) × (Fin M.k → Fin (M.g + 1))) (c : ZMod d) :
    ∀ (m v : ℕ), v < T →
      (∀ w u : ℕ, InCutCausalCone workPos T Γ v w → u ∈ Γ → TMDepStep workPos T u w →
        ∃ s : Fin L_cut, colCutStep c s = u) →
      mapCutLabels (fun s => cutVal (colCutStep c s))
          (traceSlotConeTree M d inPos workPos Γ colCutStep c m v) =
        traceConeTree M d inPos workPos Γ cutVal c m v
  | 0, _, _, _ => rfl
  | m + 1, v, hvT, hSlot => by
    have hSelf : InCutCausalCone workPos T Γ v v := ⟨[v], rfl, rfl, hvT⟩
    simp only [traceSlotConeTree, traceConeTree, mapCutLabels]
    congr 1
    · cases v with
      | zero => rfl
      | succ u =>
        dsimp only
        by_cases huΓ : u ∈ Γ
        · rw [ite_eq_left huΓ, ite_eq_left huΓ]
          obtain ⟨s₀, hs₀, hEq⟩ := findCutSlot_spec (colCutStep c) u
            (hSlot (u + 1) u hSelf huΓ ⟨hvT, Or.inl rfl⟩)
          simp [hs₀, mapCutLabels, hEq]
        · rw [ite_eq_right huΓ, ite_eq_right huΓ]
          exact mapCutLabels_traceSlotConeTree M d T inPos workPos Γ colCutStep cutVal c m u
            (by omega) fun w u' hIn hu' hDep' =>
              hSlot w u' (inCutCausalCone_step ⟨hvT, Or.inl rfl⟩ huΓ hIn) hu' hDep'
    · funext h
      cases hOpt : lastWorkVisitStep workPos h v with
      | none => rfl
      | some u =>
        dsimp only
        have hLast := lastWorkVisitStep_some hOpt
        have huv : u < v := hLast.1
        by_cases huΓ : u ∈ Γ
        · rw [ite_eq_left huΓ, ite_eq_left huΓ]
          obtain ⟨s₀, hs₀, hEq⟩ := findCutSlot_spec (colCutStep c) u
            (hSlot v u hSelf huΓ ⟨hvT, Or.inr ⟨h, hLast⟩⟩)
          simp [hs₀, mapCutLabels, hEq]
        · rw [ite_eq_right huΓ, ite_eq_right huΓ]
          exact mapCutLabels_traceSlotConeTree M d T inPos workPos Γ colCutStep cutVal c m u
            (Nat.lt_trans huv hvT) fun w u' hIn hu' hDep' =>
              hSlot w u' (inCutCausalCone_step ⟨hvT, Or.inr ⟨h, hLast⟩⟩ huΓ hIn) hu' hDep'

/-- **Theorem B (`README.md` §III.3 Line 137 — Cut-Label-Refined `Transpose.TM` Periodic Sweep
Extraction, Zero Extra Broken Cells `E = E_sched`).**
Even when clean output cones outside `E_sched` touch up to `L_cut` cut steps `colCutStep c` per
column `c`, if columns in the same `p₀ c` class share symbolic `SlotConeTree` skeletons
`slotTemplate (p₀ c) r ℓ`, refining `p₀ : ZMod d → Fin M₀` by column `c`'s tuple of `L_cut` frozen
`(M.q + 1)`-state × `(M.g + 1)^M.k`-work-symbol cut labels inflates the class count to
`M_cls = M₀ * ((M.q + 1) * (M.g + 1)^M.k)^L_cut` with **zero** extra broken cells (`E = E_sched`),
inducing `IsBoundedAritySetCode` and Theorem 1's rate-deficit bound via `M.δ`. -/
theorem tmPeriodicSweepExtraction_cutLabelRefined
    (M : Transpose.TM) (d T M₀ D L_cut : ℕ) [NeZero d]
    (inPos : ℕ → Int) (workPos : ℕ → Fin M.k → Int)
    (emitStep : Fin (Transpose.inputLength d) → ℕ) (Γ : Finset ℕ)
    (C : Set (State d (CanonicalWordAlphabet d)))
    (p₀ : ZMod d → Fin M₀) (E_sched : Finset (ZMod d × ZMod d))
    (colCutStep : ZMod d → Fin L_cut → ℕ)
    (slotTemplate : Fin M₀ → ZMod d → Fin (Transpose.entryBits d) →
      SlotConeTree L_cut (Fin (M.q + 1)) (Fin (M.g + 1)) M.k (Transpose.entryBits d) d D)
    (hk : 1 ≤ M.k) (hD : 1 ≤ D)
    (hFibre : IsFrozenTraceCutFibre M d T inPos workPos emitStep Γ C)
    (hPathLen : ∀ π : List ℕ, IsCutFreeCausalPath workPos T Γ π → π.length ≤ D)
    (hColCutsCover : ∀ (r c : ZMod d), (r, c) ∉ E_sched →
      ∀ (ℓ : Fin (Transpose.entryBits d)) (w u : ℕ),
        InCutCausalCone workPos T Γ (emitStep (outputBitIdx d r c ℓ)) w →
        u ∈ Γ → TMDepStep workPos T u w → ∃ s : Fin L_cut, colCutStep c s = u)
    (hSlotPeriodic : ∀ (r c : ZMod d), (r, c) ∉ E_sched →
      ∀ ℓ : Fin (Transpose.entryBits d),
        traceSlotConeTree M d inPos workPos Γ colCutStep c D
          (emitStep (outputBitIdx d r c ℓ)) = slotTemplate (p₀ c) r ℓ) :
    let Delta := Transpose.entryBits d * (M.k + 1) ^ D
    let M_cls := M₀ * ((M.q + 1) * (M.g + 1) ^ M.k) ^ L_cut
    ∃ (p_ref : ZMod d → Fin M_cls)
      (f_ref : Fin M_cls → State d (CanonicalWordAlphabet d) → (ZMod d → CanonicalWordAlphabet d))
      (Q_ref : Fin M_cls → ZMod d → Finset (ZMod d × ZMod d)),
      IsBoundedAritySetCode Delta p_ref E_sched f_ref Q_ref C ∧
      (1 ≤ M₀ → C.Nonempty →
        Real.log (Nat.card C : ℝ) / Real.log (Fintype.card (CanonicalWordAlphabet d) : ℝ) ≤
          (d : ℝ) ^ 2 -
            ((d : ℝ) ^ 2 - (E_sched.card : ℝ) - (d : ℝ) * (M_cls : ℝ) * (Delta : ℝ)) *
              ((Delta : ℝ) ^ Delta / ((Delta + 1 : ℝ) ^ (Delta + 1)))) := by
  dsimp only
  set Delta := Transpose.entryBits d * (M.k + 1) ^ D
  set M_cls := M₀ * ((M.q + 1) * (M.g + 1) ^ M.k) ^ L_cut
  let CutLabel := Fin (M.q + 1) × (Fin M.k → Fin (M.g + 1))
  have hCardEq : Fintype.card (Fin M₀ × (Fin L_cut → CutLabel)) = M_cls := by
    simp [CutLabel, M_cls, Fintype.card_prod, Fintype.card_fin]
  let eqv := Fintype.equivFinOfCardEq hCardEq
  let cutVal := fibreCutLabels M d workPos C
  let p_ref : ZMod d → Fin M_cls := fun c => eqv (p₀ c, fun s => cutVal (colCutStep c s))
  let tmpl_ref : Fin M_cls → ZMod d → Fin (Transpose.entryBits d) →
      CausalConeTree (Fin (M.q + 1)) (Fin (M.g + 1)) M.k (Transpose.entryBits d) d D :=
    fun m_ref r ℓ =>
      let pair := eqv.symm m_ref
      mapCutLabels pair.2 (slotTemplate pair.1 r ℓ)
  let f_ref : Fin M_cls → State d (CanonicalWordAlphabet d) → (ZMod d → CanonicalWordAlphabet d) :=
    fun m_ref Y r ℓ => (evalConeTree M Y (tmpl_ref m_ref r ℓ)).2.2
  let Q_ref : Fin M_cls → ZMod d → Finset (ZMod d × ZMod d) :=
    fun m_ref r => Finset.univ.biUnion (fun ℓ => treeCellSupport (tmpl_ref m_ref r ℓ))
  have hCode : IsBoundedAritySetCode Delta p_ref E_sched f_ref Q_ref C := by
    refine ⟨syntacticCellSupport_of_treeTemplates M hk tmpl_ref, ?_⟩
    intro X hX r c hrcNotE
    funext ℓ
    have hvT : emitStep (outputBitIdx d r c ℓ) < T := hFibre.2.1 _
    have hMapEq := mapCutLabels_traceSlotConeTree M d T inPos workPos Γ colCutStep cutVal c D
      (emitStep (outputBitIdx d r c ℓ)) hvT (hColCutsCover r c hrcNotE ℓ)
    have hEval := (evalConeTree_traceConeTree_eq M hFibre cutVal
      (fibreCutLabels_spec hFibre) hX c hD (emitStep (outputBitIdx d r c ℓ)) hvT
      (fun π hπ _ => hPathLen π hπ)).2 r ℓ rfl
    change (evalConeTree M (rot c X) (tmpl_ref (p_ref c) r ℓ)).2.2 = X c r ℓ
    have hTmpl : tmpl_ref (p_ref c) r ℓ =
        traceConeTree M d inPos workPos Γ cutVal c D (emitStep (outputBitIdx d r c ℓ)) := by
      dsimp only [tmpl_ref, p_ref]
      rw [Equiv.symm_apply_apply, ← hSlotPeriodic r c hrcNotE ℓ, hMapEq]
    rw [hTmpl]
    exact hEval
  refine ⟨p_ref, f_ref, Q_ref, hCode, fun hM₀ hCne => ?_⟩
  have hDelta : 1 ≤ Delta := by
    have hb : 1 ≤ Transpose.entryBits d := by unfold Transpose.entryBits; omega
    exact Nat.mul_le_mul hb (Nat.one_le_pow _ _ (by omega))
  have hMcls : 1 ≤ M_cls := by
    have hBase : 1 ≤ (M.q + 1) * (M.g + 1) ^ M.k :=
      Nat.mul_le_mul (Nat.succ_pos M.q) (Nat.one_le_pow _ _ (Nat.succ_pos M.g))
    exact Nat.mul_le_mul hM₀ (Nat.one_le_pow _ _ hBase)
  exact theorem1_BoundedAritySetCapacity.2 d M_cls Delta (CanonicalWordAlphabet d)
    p_ref E_sched f_ref Q_ref C (canonicalWord_card_ge_two d) hMcls hDelta hCne hCode

/-! ### 3. Conditional End-to-End Reductions to `(T)` & Open Target Consequences -/

/-- Adding a single stationary dummy work tape when `M₀.k = 0` preserves `Transpose.TransposesWithin`
for every time bound `T` (including `fun L => c * (L + 1)`), ensuring `1 ≤ M.k`. -/
theorem padDummyWorkTape_transposesWithin (M₀ : Transpose.TM) (T : ℕ → ℕ)
    (hTrans : Transpose.TransposesWithin M₀ T) :
    ∃ M : Transpose.TM, 1 ≤ M.k ∧ Transpose.TransposesWithin M T := by
  by_cases hk : 1 ≤ M₀.k
  · exact ⟨M₀, hk, hTrans⟩
  · have hk0 : M₀.k = 0 := by omega
    let M₁ : Transpose.TM :=
      { k := 1
        g := 0
        q := M₀.q
        δ := fun st inp _ =>
          match M₀.δ st inp (fun i => Fin.elim0 (hk0 ▸ i)) with
          | none => none
          | some (s, dir, _, o) => some (s, dir, fun _ => (0, .stay), o) }
    let liftCfg (cfg : Transpose.Config M₀) : Transpose.Config M₁ :=
      { state := cfg.state
        inPos := cfg.inPos
        work := fun _ _ => 0
        workPos := fun _ => 0
        outRev := cfg.outRev }
    have hStep : ∀ (w : List Bool) (cfg : Transpose.Config M₀),
        Transpose.step M₁ w (liftCfg cfg) = (Transpose.step M₀ w cfg).map liftCfg := by
      intro w cfg
      have hEmptyFun : (fun i : Fin M₀.k => Fin.elim0 (hk0 ▸ i)) =
          (fun i => cfg.work i (cfg.workPos i)) := by
        funext i; exact absurd i.isLt (by omega)
      unfold Transpose.step
      dsimp only [M₁, liftCfg]
      rw [hEmptyFun]
      cases M₀.δ cfg.state (Transpose.readInput w cfg.inPos) (fun i => cfg.work i (cfg.workPos i))
        with
      | none => rfl
      | some val =>
        rcases val with ⟨s, dir, _, o⟩
        simp [Transpose.Dir.shift]
    have hStepN : ∀ (w : List Bool) (s : ℕ) (cfg : Transpose.Config M₀),
        Transpose.stepN M₁ w s (liftCfg cfg) = (Transpose.stepN M₀ w s cfg).map liftCfg := by
      intro w s
      induction s with
      | zero => intro _; rfl
      | succ s ih =>
        intro cfg
        simp only [Transpose.stepN, hStep w cfg]
        cases Transpose.step M₀ w cfg with
        | none => rfl
        | some cfg' => exact ih cfg'
    refine ⟨M₁, Nat.le_refl 1, fun n hn A => ?_⟩
    obtain ⟨s, hs, cEnd, hcEnd, hHalt, hOut⟩ := hTrans n hn A
    refine ⟨s, hs, liftCfg cEnd, ?_, ?_, hOut⟩
    · have hInit : liftCfg (Transpose.init M₀) = Transpose.init M₁ := rfl
      rw [← hInit, hStepN, hcEnd]; rfl
    · rw [hStep, hHalt]; rfl

/-- **`Problem 9.4` Periodic Cell-Sweep Fibre Reduction Hypothesis (`README.md` §I & §III.3).**
Every `1 ≤ k`-work-tape linear-time transposer `M` (`Transpose.TransposesWithin M (fun L => c * (L + 1))`,
`1 ≤ c`) admits a constant cell cone arity `Delta ≥ 1`, an unbroken output fraction `δ ∈ (0, 1]`,
a sublinear class-count schedule `M_cls d = o(d / Delta)`, and a cut/advice bit budget
`B_adv d ≤ ε * c * (L(d) + 1)` with `ε < (δ / 2) * (Delta^Delta / (Delta + 1)^(Delta + 1)) / (4 * c)`
whose pigeonhole fibre `C d ⊆ State d (CanonicalWordAlphabet d)` satisfies `IsBoundedAritySetCode`
with `|E d| ≤ (1 - δ) d^2` for infinitely many `d ≥ 2`. -/
def PeriodicCellSweepReductionHypothesis : Prop :=
  ∀ (M : Transpose.TM) (c : ℕ),
    1 ≤ M.k →
    1 ≤ c →
    Transpose.TransposesWithin M (fun L => c * (L + 1)) →
    ∃ (Delta : ℕ) (δ ε : ℝ)
      (M_cls B_adv : ℕ → ℕ)
      (p : ∀ d, ZMod d → Fin (M_cls d))
      (E : ∀ d, Finset (ZMod d × ZMod d))
      (f : ∀ d, Fin (M_cls d) → State d (CanonicalWordAlphabet d) →
        (ZMod d → CanonicalWordAlphabet d))
      (Q : ∀ d, Fin (M_cls d) → ZMod d → Finset (ZMod d × ZMod d))
      (C : ∀ d, Set (State d (CanonicalWordAlphabet d))),
      1 ≤ Delta ∧
      0 < δ ∧ δ ≤ 1 ∧
      0 ≤ ε ∧
      ε < (δ / 2) * ((Delta : ℝ) ^ Delta / ((Delta + 1 : ℝ) ^ (Delta + 1))) / (4 * (c : ℝ)) ∧
      Filter.Tendsto (fun d : ℕ => (M_cls d : ℝ) * (Delta : ℝ) / (d : ℝ))
        Filter.atTop (nhds 0) ∧
      ∀ D₀ : ℕ, ∃ d : ℕ,
        max D₀ 2 ≤ d ∧
        ((E d).card : ℝ) ≤ (1 - δ) * (d : ℝ) ^ 2 ∧
        (B_adv d : ℝ) ≤ ε * (c : ℝ) * ((Transpose.inputLength d : ℝ) + 1) ∧
        (Fintype.card (CanonicalWordAlphabet d)) ^ (d ^ 2) ≤
          2 ^ (B_adv d) * Nat.card (C d) ∧
        ∃ (_ : NeZero d), IsBoundedAritySetCode Delta (p d) (E d) (f d) (Q d) (C d)

private theorem transposesWithin_upgrade_const {M₀ : Transpose.TM} {c₀ : ℕ}
    (hTrans₀ : Transpose.TransposesWithin M₀ (fun L => c₀ * (L + 1))) :
    ∃ (M : Transpose.TM) (c : ℕ),
      1 ≤ M.k ∧ 1 ≤ c ∧ Transpose.TransposesWithin M (fun L => c * (L + 1)) := by
  let c := max c₀ 1
  have hMono : Transpose.TransposesWithin M₀ (fun L => c * (L + 1)) := by
    intro n hn A
    obtain ⟨s, hs, cEnd, hcEnd, hHalt, hOut⟩ := hTrans₀ n hn A
    exact ⟨s, hs.trans (Nat.mul_le_mul_right _ (le_max_left c₀ 1)), cEnd, hcEnd, hHalt, hOut⟩
  obtain ⟨M, hk, hTrans⟩ := padDummyWorkTape_transposesWithin M₀ (fun L => c * (L + 1)) hMono
  exact ⟨M, c, hk, le_max_right c₀ 1, hTrans⟩

/-- **Conditional Closure of `TapeCodingConjectureNegationSpec` from `Problem 9.4`
(`README.md` §I & §III.3).**
`PeriodicCellSweepReductionHypothesis` refutes `Transpose.LinearTimeTransposable` via Theorem 1's
nonlinear set-code rate deficit (`growingClassesPositiveDeficit`) and establishes
`TapeCodingConjectureNegationSpec`. -/
theorem conditional_TapeCodingConjecture_of_PeriodicCellSweepHypothesis
    (hSweep : PeriodicCellSweepReductionHypothesis) :
    TapeCodingConjectureNegationSpec := by
  refine ⟨entryBits_eq_clog, ?_⟩
  rintro ⟨M₀, c₀, hTrans₀⟩
  obtain ⟨M, c, hk, hc, hTrans⟩ := transposesWithin_upgrade_const hTrans₀
  obtain ⟨Delta, δ, ε, M_cls, B_adv, p, E, f, Q, C,
    hDelta, hδPos, hδLe, hεNonneg, hεLt, hSublinear, hInf⟩ := hSweep M c hk hc hTrans
  set gain : ℝ := (Delta : ℝ) ^ Delta / ((Delta + 1 : ℝ) ^ (Delta + 1))
  have hGainPos : 0 < gain := by positivity
  have hEvSmall : ∀ᶠ d in Filter.atTop,
      (M_cls d : ℝ) * (Delta : ℝ) / (d : ℝ) < δ / 2 :=
    (tendsto_order.mp hSublinear).2 (δ / 2) (by linarith)
  obtain ⟨D₀, hD₀⟩ := Filter.eventually_atTop.mp hEvSmall
  obtain ⟨d, hdMax, hEd, hBadv, hPigeon, hNeZero, hCode⟩ := hInf D₀
  have : NeZero d := hNeZero
  have hd2 : 2 ≤ d := (le_max_right D₀ 2).trans hdMax
  have hdD₀ : D₀ ≤ d := (le_max_left D₀ 2).trans hdMax
  have hMpos : 1 ≤ M_cls d := by have := (p d 0).isLt; omega
  have hCardPos : 1 ≤ Nat.card (C d) := by
    have hLhsPos : 1 ≤ (Fintype.card (CanonicalWordAlphabet d)) ^ (d ^ 2) :=
      Nat.one_le_pow _ _ (by have := canonicalWord_card_ge_two d; omega)
    by_contra h0
    have hEq0 : Nat.card (C d) = 0 := by omega
    rw [hEq0, mul_zero] at hPigeon; omega
  have hCne : (C d).Nonempty := by
    by_contra hEmp
    rw [Set.not_nonempty_iff_eq_empty.mp hEmp, Nat.card_of_isEmpty] at hCardPos; omega
  have hdPos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hd2)
  have hDeltaPos : (0 : ℝ) < (Delta : ℝ) := by exact_mod_cast hDelta
  have hMclsLe : (M_cls d : ℝ) ≤ (δ / 2) * (d : ℝ) / (Delta : ℝ) := by
    have hLt := (div_lt_iff₀ hdPos).mp (hD₀ d hdD₀)
    exact (le_div_iff₀ hDeltaPos).mpr (by linarith)
  have hUpper := (growingClassesPositiveDeficit d (M_cls d) Delta (CanonicalWordAlphabet d)
    (1 - δ) (δ / 2) (p d) (E d) (f d) (Q d) (C d) (canonicalWord_card_ge_two d) hMpos hDelta
    (by linarith) (by linarith) (by linarith) hEd hMclsLe hCne hCode).1
  set b := Transpose.entryBits d
  set L := Transpose.inputLength d
  have hb : 1 ≤ b := by dsimp [b, Transpose.entryBits]; omega
  have hLge4 : 4 ≤ L := by
    dsimp [L, Transpose.inputLength]
    calc 4 = 2 * 2 * 1 := rfl
      _ ≤ d * d * b := Nat.mul_le_mul (Nat.mul_le_mul hd2 hd2) hb
  have hPowEq : (Fintype.card (CanonicalWordAlphabet d)) ^ (d ^ 2) = 2 ^ L := by
    rw [canonicalWordAlphabet_card, ← pow_mul]
    congr 1; dsimp [L, Transpose.inputLength, b]; ring
  have hRealPigeon : (2 : ℝ) ^ L ≤ (2 : ℝ) ^ (B_adv d) * (Nat.card (C d) : ℝ) := by
    exact_mod_cast (hPowEq ▸ hPigeon)
  have hLogPigeon := Real.log_le_log (by positivity) hRealPigeon
  rw [Real.log_pow, Real.log_mul (by positivity) (by positivity), Real.log_pow] at hLogPigeon
  have hDenEq : Real.log (Fintype.card (CanonicalWordAlphabet d) : ℝ) * (d : ℝ) ^ 2 =
      (L : ℝ) * Real.log 2 := by
    rw [canonicalWordAlphabet_card, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
    dsimp [L, Transpose.inputLength, b]; push_cast; ring
  have hLog2Pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hLPos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 4) hLge4)
  rw [hDenEq] at hUpper
  have hLogCardLe := (div_le_iff₀ (mul_pos hLPos hLog2Pos)).mp hUpper
  have hGainBound : ((δ / 2) * gain) * (L : ℝ) ≤ (B_adv d : ℝ) := by
    have hMul : (((δ / 2) * gain) * (L : ℝ)) * Real.log 2 ≤ (B_adv d : ℝ) * Real.log 2 := by
      nlinarith
    exact le_of_mul_le_mul_right hMul hLog2Pos
  have hcPos : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have hFourCEps : 4 * (c : ℝ) * ε < (δ / 2) * gain := by
    have h := (lt_div_iff₀ (by positivity : (0 : ℝ) < 4 * (c : ℝ))).mp hεLt
    linarith
  have hLp1 : (L : ℝ) + 1 ≤ 2 * (L : ℝ) := by
    have : (4 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hLge4
    linarith
  have hBadvUpper : (B_adv d : ℝ) ≤ 2 * (c : ℝ) * ε * (L : ℝ) := by
    calc (B_adv d : ℝ) ≤ ε * (c : ℝ) * ((L : ℝ) + 1) := hBadv
      _ ≤ ε * (c : ℝ) * (2 * (L : ℝ)) :=
          mul_le_mul_of_nonneg_left hLp1 (mul_nonneg hεNonneg hcPos.le)
      _ = 2 * (c : ℝ) * ε * (L : ℝ) := by ring
  nlinarith

/-- One-class (`M = 1, E = ∅`) constant-arity fibre extraction hypothesis at rate `≥ 3/4`. -/
def OneClassSweepFibreReductionHypothesis : Prop :=
  ∀ (M : Transpose.TM) (c : ℕ),
    1 ≤ M.k →
    1 ≤ c →
    Transpose.TransposesWithin M (fun L => c * (L + 1)) →
    ∃ Delta : ℕ, 1 ≤ Delta ∧ ∀ D₀ : ℕ,
      ∃ (d : ℕ) (_ : NeZero d)
        (f : Fin 1 → State d (CanonicalWordAlphabet d) → (ZMod d → CanonicalWordAlphabet d))
        (Q : Fin 1 → ZMod d → Finset (ZMod d × ZMod d))
        (C : Set (State d (CanonicalWordAlphabet d))),
        max D₀ 2 ≤ d ∧
        C.Nonempty ∧
        IsBoundedAritySetCode Delta (fun _ => 0) ∅ f Q C ∧
        (3 : ℝ) / 4 ≤
          Real.log (Nat.card C : ℝ) /
            (Real.log (Fintype.card (CanonicalWordAlphabet d) : ℝ) * (d : ℝ) ^ 2)

/-- **Conditional Closure of `(T)` from `OneClassBoundedArityHalfBarrierQuestion` + 1-Class Fibres
(`README.md` §II.1 Bullet 3 & §III.1).**
If `M = 1` constant-arity nonlinear shared codes obey the `1/2 + o(1)` rate barrier and every
`O(L)` transposer (`1 ≤ M.k`) admits 1-class (`M = 1, E = ∅`) constant-arity fibres of rate `≥ 3/4`
for arbitrarily large `d`, then `TapeCodingConjectureNegationSpec` holds. -/
theorem conditional_TapeCodingConjecture_of_HalfBarrierAndOneClassFibre
    (hHalf : OneClassBoundedArityHalfBarrierQuestion)
    (hFibreHyp : OneClassSweepFibreReductionHypothesis) :
    TapeCodingConjectureNegationSpec := by
  refine ⟨entryBits_eq_clog, ?_⟩
  rintro ⟨M₀, c₀, hTrans₀⟩
  obtain ⟨M, c, hk, hc, hTrans⟩ := transposesWithin_upgrade_const hTrans₀
  obtain ⟨Delta, hDelta, hInf⟩ := hFibreHyp M c hk hc hTrans
  obtain ⟨D₀, hHalfBound⟩ := hHalf Delta hDelta ((1 : ℝ) / 8) (by norm_num)
  obtain ⟨d, hNeZero, f, Q, C, hdMax, hCne, hCode, hRateLo⟩ := hInf D₀
  have : NeZero d := hNeZero
  have hRateHi := hHalfBound d f Q C hdMax hCne hCode
  linarith

/-- **Conditional Non-Vanishing Two-Stage Linear Rank Error from Macroscopic Rank Target
(`README.md` §II.2 & §III.2).**
`OpenTarget_MacroscopicTwoStageRankDeficitSpec` implies that for every `M₁, M₂ ≥ 1`, there exists
`ε > 0` such that along every sequence of fields `F d`, lane widths `b d ≥ 1`, partitions
`p₁ d : ZMod d → Fin M₁`, `p₂ d : ZMod d → Fin M₂`, and `ClassUniform` linear stages `K₁ d, K₂ d`,
the normalized rank error `finrank (range (swapLinear - K₂ ∘ K₁)) / (b d * d^2)` does not converge
to `0` as `d → ∞`. -/
theorem conditional_NoLowErrorTwoStageLinear_of_MacroscopicTarget
    (hMacro : OpenTarget_MacroscopicTwoStageRankDeficitSpec.{u})
    (M₁ M₂ : ℕ) (hM₁ : 1 ≤ M₁) (hM₂ : 1 ≤ M₂) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (F : ℕ → Type u) [∀ d, Field (F d)]
        (b : ℕ → ℕ)
        (p₁ : ∀ d, ZMod d → Fin M₁)
        (p₂ : ∀ d, ZMod d → Fin M₂)
        (K₁ K₂ : ∀ d, State d (Fin (b d) → F d) →ₗ[F d] State d (Fin (b d) → F d)),
        (∀ d, 1 ≤ b d) →
        (∀ d, ClassUniform (p₁ d) (K₁ d)) →
        (∀ d, ClassUniform (p₂ d) (K₂ d)) →
        ¬ Filter.Tendsto
            (fun d : ℕ =>
              (finrank (F d)
                (LinearMap.range
                  (swapLinear (F d) (d := d) (A := Fin (b d) → F d) -
                    (K₂ d).comp (K₁ d))) : ℝ) /
                ((b d : ℝ) * (d : ℝ) ^ 2))
            Filter.atTop (nhds 0) := by
  obtain ⟨ε, D₀, hεPos, hBound⟩ := hMacro M₁ M₂ hM₁ hM₂
  refine ⟨ε, hεPos, fun F _ b p₁ p₂ K₁ K₂ hb hU₁ hU₂ hTendsto => ?_⟩
  have hEvLt : ∀ᶠ d in Filter.atTop,
      (finrank (F d)
        (LinearMap.range
          (swapLinear (F d) (d := d) (A := Fin (b d) → F d) -
            (K₂ d).comp (K₁ d))) : ℝ) /
        ((b d : ℝ) * (d : ℝ) ^ 2) < ε :=
    (tendsto_order.mp hTendsto).2 ε hεPos
  obtain ⟨d, hdGe, hLt⟩ := ((Filter.eventually_ge_atTop (max D₀ 1)).and hEvLt).exists
  have hd1 : 1 ≤ d := (le_max_right D₀ 1).trans hdGe
  have hdD₀ : D₀ ≤ d := (le_max_left D₀ 1).trans hdGe
  have : NeZero d := ⟨by omega⟩
  have hDenPos : (0 : ℝ) < (b d : ℝ) * (d : ℝ) ^ 2 := by
    have hbPos : (0 : ℝ) < (b d : ℝ) := by exact_mod_cast (hb d)
    have hdPos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
    positivity
  have hRkLo := hBound (F d) d (b d) (p₁ d) (p₂ d) (K₁ d) (K₂ d) hdD₀ (hb d) (hU₁ d) (hU₂ d)
  have hRkHi := (div_lt_iff₀ hDenPos).mp hLt
  nlinarith

end BoundedArityDecoders
