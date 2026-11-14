import BoundedArityDecoders.NativeSweepInterfaceProofs

/-!
# `Transpose.TM` Causal-Cone Tree Evaluation & Negative Per-Column Cut-Absorption Bounds

This module provides:
1. **Pure `M.δ` causal-cone tree evaluation (`ParametricConeTree`, `CausalConeTree`, `evalConeTree`,
   `evalConeTree_cellSupport`, `traceConeTree`, `evalConeTree_traceConeTree_eq`)**:
   Starting from a `q`-state, `k`-work-tape machine `M : Transpose.TM` (`1 ≤ M.k`) and a frozen-trace
   `Γ`-cut fibre `IsFrozenTraceCutFibre M d T inPos workPos emitStep Γ C`, depth-`D` `(1 + M.k)`-ary
   causal-cone trees evaluate purely via `M.δ`, touch at most `(M.k + 1)^D` input cells, and agree
   with `M`'s live execution on `C`.
2. **Negative brackets for two specific per-column cut-absorption schemes
   (`perColumnCutAbsorption_bracket_neg`)**:
   Along the control-state spine `u → u + 1`, every `Γ`-avoiding causal cone of depth `≤ D` starting
   at step `v ≥ D` touches a cut step `u ∈ Γ` within `[v - D, v)`. Consequently, for two naive
   column-class reductions:
   * Discarding cut-touching outputs leaves at most `D` unbroken entries (`d^2 - |E| ≤ D`), making
     the column-class bracket `d^2 - |E| - d * M₀ * Δ` strictly negative for every `M₀ ≥ 1`;
   * Positing a worst-case full-product class count `M_cls = M₀ * ((M.q + 1) * (M.g + 1)^M.k)^L_cut`
     across `L_cut` cut slots per column covers at most `D + d * L_cut * D` unbroken entries while
     making `d^2 - |E_sched| - d * M_cls * Δ` strictly negative whenever `1 ≤ M₀` and
     `2 ≤ (M.q + 1) * (M.g + 1)^M.k` (using `M_cls ≥ L_cut + 1`).
   This illustrates why those two column-class schemes fail (as noted in the commentary on Paper 17
   Problem 9.4(b), per-entry cut patterns point instead to per-position recovery functions).
3. **Work-tape padding (`padDummyWorkTape_transposesWithin`)**: adding a dummy work tape when
   `M₀.k = 0` preserves `Transpose.TransposesWithin` for every time bound `T`.
-/

namespace BoundedArityDecoders

open SharedDecoders
open scoped BigOperators

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

/-- **Syntactic Cell-Support Bound & Locality of `evalConeTree`.**
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

/-- Combined cell-support bound across all `b = Transpose.entryBits d` bit-lane `CausalConeTree`s
of a single output entry: their union has cardinality at most `b * (M.k + 1)^D`. -/
theorem evalConeTree_entryCellSupport_card_le (M : Transpose.TM) {d D : ℕ} [DecidableEq (ZMod d)]
    (hk : 1 ≤ M.k)
    (trees : Fin (Transpose.entryBits d) →
      CausalConeTree (Fin (M.q + 1)) (Fin (M.g + 1)) M.k (Transpose.entryBits d) d D) :
    (Finset.univ.biUnion (fun ℓ => treeCellSupport (trees ℓ))).card ≤
      Transpose.entryBits d * (M.k + 1) ^ D := by
  calc
    (Finset.univ.biUnion (fun ℓ => treeCellSupport (trees ℓ))).card
        ≤ ∑ ℓ : Fin (Transpose.entryBits d), (treeCellSupport (trees ℓ)).card :=
          Finset.card_biUnion_le
    _ ≤ ∑ _ℓ : Fin (Transpose.entryBits d), (M.k + 1) ^ D :=
          Finset.sum_le_sum fun ℓ _ => (evalConeTree_cellSupport M hk (trees ℓ)).1
    _ = Transpose.entryBits d * (M.k + 1) ^ D := by simp

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

/-! ### 3. Negative Per-Column Cut-Absorption Bounds -/

private def spineList : ℕ → ℕ → List ℕ
  | 0, v => [v]
  | k + 1, v => v :: spineList k (v - 1)

private theorem spineList_cons (k v : ℕ) :
    ∃ rest : List ℕ, spineList k v = v :: rest := by
  cases k with
  | zero => exact ⟨[], rfl⟩
  | succ m => exact ⟨spineList m (v - 1), rfl⟩

private theorem spineList_length : ∀ (k v : ℕ), (spineList k v).length = k + 1
  | 0, _ => rfl
  | k + 1, v => by simp [spineList, spineList_length k (v - 1)]

private theorem spineList_head? (k v : ℕ) : (spineList k v).head? = some v := by
  obtain ⟨rest, hEq⟩ := spineList_cons k v
  rw [hEq]
  rfl

private theorem spineList_getLast? :
    ∀ (k v : ℕ), k ≤ v → (spineList k v).getLast? = some (v - k)
  | 0, v, _ => by simp [spineList]
  | k + 1, v, hkv => by
    obtain ⟨rest, hEq⟩ := spineList_cons k (v - 1)
    have ih := spineList_getLast? k (v - 1) (by omega)
    dsimp only [spineList]
    rw [hEq] at ih ⊢
    rw [List.getLast?_cons_cons, ih]
    congr 1
    omega

private theorem spineList_cutFree {k_tm : ℕ} (workPos : ℕ → Fin k_tm → Int) (T : ℕ)
    (Γ : Finset ℕ) :
    ∀ (k v : ℕ), v < T → k ≤ v →
      (∀ u : ℕ, v - k ≤ u → u < v → u ∉ Γ) →
      IsCutFreeCausalPath workPos T Γ (spineList k v)
  | 0, v, hvT, _, _ => hvT
  | k + 1, v, hvT, hkv, hNoΓ => by
    obtain ⟨rest, hEq⟩ := spineList_cons k (v - 1)
    have ih := spineList_cutFree workPos T Γ k (v - 1) (by omega) (by omega)
      (fun u huLo huHi => hNoΓ u (by omega) (by omega))
    dsimp only [spineList]
    rw [hEq] at ih ⊢
    exact ⟨⟨hvT, Or.inl (by omega)⟩, hNoΓ (v - 1) (by omega) (by omega), ih⟩

private theorem exists_recent_cut_of_ge_depth {k_tm : ℕ} (workPos : ℕ → Fin k_tm → Int)
    (T D : ℕ) (Γ : Finset ℕ)
    (hPathLen : ∀ π : List ℕ, IsCutFreeCausalPath workPos T Γ π → π.length ≤ D)
    {v : ℕ} (hvT : v < T) (hDv : D ≤ v) :
    ∃ u : ℕ, u ∈ Γ ∧ v - D ≤ u ∧ u < v ∧
      InCutCausalCone workPos T Γ v (u + 1) ∧
      TMDepStep workPos T u (u + 1) := by
  classical
  let S : Finset ℕ := (Finset.Ico (v - D) v).filter (· ∈ Γ)
  have hSne : S.Nonempty := by
    by_contra hEmp
    have hNoΓ : ∀ u : ℕ, v - D ≤ u → u < v → u ∉ Γ := by
      intro u huLo huHi huΓ
      exact hEmp ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨huLo, huHi⟩, huΓ⟩⟩
    have hCutFree := spineList_cutFree workPos T Γ D v hvT hDv hNoΓ
    have hLen := hPathLen (spineList D v) hCutFree
    rw [spineList_length] at hLen
    omega
  set u := S.max' hSne with hu_def
  have huMem : u ∈ S := Finset.max'_mem S hSne
  simp only [S, Finset.mem_filter, Finset.mem_Ico] at huMem
  rcases huMem with ⟨⟨huLo, huHi⟩, huΓ⟩
  set k := v - (u + 1) with hk_def
  have hkv : k ≤ v := Nat.sub_le _ _
  have hvSub : v - k = u + 1 := by omega
  have hNoAbove : ∀ w : ℕ, v - k ≤ w → w < v → w ∉ Γ := by
    intro w hwLo hwHi hwΓ
    have hwS : w ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, hwHi⟩, hwΓ⟩
    have hwLe : w ≤ u := Finset.le_max' S w hwS
    omega
  have hCone : InCutCausalCone workPos T Γ v (u + 1) := by
    refine ⟨spineList k v, spineList_head? k v, ?_, spineList_cutFree workPos T Γ k v hvT hkv hNoAbove⟩
    rw [spineList_getLast? k v hkv, hvSub]
  exact ⟨u, huΓ, huLo, huHi, hCone, ⟨by omega, Or.inl rfl⟩⟩

private theorem nat_add_one_le_two_pow : ∀ n : ℕ, n + 1 ≤ 2 ^ n
  | 0 => by decide
  | n + 1 => by
    have ih := nat_add_one_le_two_pow n
    have hPos : 1 ≤ 2 ^ n := Nat.one_le_pow _ _ (by decide)
    rw [pow_succ]
    omega

/-- **Negative Per-Column Cut-Absorption Brackets.**
On any nonempty frozen-trace `Γ`-cut fibre `C` of `M : Transpose.TM` (`1 ≤ M.k`) whose
`Γ`-free causal paths have at most `D` vertices, let `Delta = entryBits d * (M.k + 1)^D`:
1. At least `d^2 - D` output cells touch `Γ`, so discarding cut-touching outputs makes the
   column-class capacity bracket `d^2 - |E| - d * M₀ * Delta` strictly negative for every `M₀ ≥ 1`;
2. Covering all cut steps touched by unbroken outputs outside `E_sched` with `L_cut` cut slots per
   column bounds unbroken outputs by `D + d * L_cut * D`, making the refined column-class bracket
   `d^2 - |E_sched| - d * M_cls * Delta` (`M_cls = M₀ * ((M.q + 1) * (M.g + 1)^M.k)^L_cut`)
   strictly negative whenever `1 ≤ M₀` and `2 ≤ (M.q + 1) * (M.g + 1)^M.k`. -/
theorem perColumnCutAbsorption_bracket_neg
    (M : Transpose.TM) (d T D : ℕ) [NeZero d]
    (inPos : ℕ → Int) (workPos : ℕ → Fin M.k → Int)
    (emitStep : Fin (Transpose.inputLength d) → ℕ) (Γ : Finset ℕ)
    (C : Set (State d (CanonicalWordAlphabet d)))
    (hk : 1 ≤ M.k) (hCne : C.Nonempty)
    (hFibre : IsFrozenTraceCutFibre M d T inPos workPos emitStep Γ C)
    (hPathLen : ∀ π : List ℕ, IsCutFreeCausalPath workPos T Γ π → π.length ≤ D) :
    let Delta := Transpose.entryBits d * (M.k + 1) ^ D
    (d ^ 2 ≤ (cutTouchingOutputCells d T workPos emitStep Γ).card + D ∧
      ∀ (M₀ : ℕ) (E_sched : Finset (ZMod d × ZMod d)), 1 ≤ M₀ →
        (d : ℝ) ^ 2 -
          ((E_sched ∪ cutTouchingOutputCells d T workPos emitStep Γ).card : ℝ) -
          (d : ℝ) * (M₀ : ℝ) * (Delta : ℝ) < 0) ∧
    (∀ (L_cut : ℕ) (E_sched : Finset (ZMod d × ZMod d)) (colCutStep : ZMod d → Fin L_cut → ℕ),
      (∀ (r c : ZMod d), (r, c) ∉ E_sched →
        ∀ (ℓ : Fin (Transpose.entryBits d)) (w u : ℕ),
          InCutCausalCone workPos T Γ (emitStep (outputBitIdx d r c ℓ)) w →
          u ∈ Γ → TMDepStep workPos T u w → ∃ s : Fin L_cut, colCutStep c s = u) →
      d ^ 2 ≤ E_sched.card + D + d * L_cut * D ∧
      ∀ M₀ : ℕ, 1 ≤ M₀ → 2 ≤ (M.q + 1) * (M.g + 1) ^ M.k →
        let M_cls := M₀ * ((M.q + 1) * (M.g + 1) ^ M.k) ^ L_cut
        (d : ℝ) ^ 2 - (E_sched.card : ℝ) - (d : ℝ) * (M_cls : ℝ) * (Delta : ℝ) < 0) := by
  classical
  dsimp only
  set b := Transpose.entryBits d
  have hbPos : 0 < b := by dsimp [b, Transpose.entryBits]; omega
  let ℓ₀ : Fin (Transpose.entryBits d) := ⟨0, hbPos⟩
  let cellEmit (rc : ZMod d × ZMod d) : ℕ := emitStep (outputBitIdx d rc.1 rc.2 ℓ₀)
  obtain ⟨X₀, hX₀⟩ := hCne
  have hCellEmitInj : Function.Injective cellEmit := by
    intro rc₁ rc₂ hEq
    obtain ⟨cfg₁, _, hPre₁, _, hLen₁, _⟩ := hFibre.2.2.2.2.1 X₀ hX₀ (outputBitIdx d rc₁.1 rc₁.2 ℓ₀)
    obtain ⟨cfg₂, _, hPre₂, _, hLen₂, _⟩ := hFibre.2.2.2.2.1 X₀ hX₀ (outputBitIdx d rc₂.1 rc₂.2 ℓ₀)
    change tmCfgAt M (encodeCanonicalState X₀) (cellEmit rc₁) = some cfg₁ at hPre₁
    change tmCfgAt M (encodeCanonicalState X₀) (cellEmit rc₂) = some cfg₂ at hPre₂
    rw [hEq, hPre₂] at hPre₁
    injection hPre₁ with hCfgEq
    subst hCfgEq
    have hValEq : (outputBitIdx d rc₁.1 rc₁.2 ℓ₀).val = (outputBitIdx d rc₂.1 rc₂.2 ℓ₀).val :=
      hLen₁.symm.trans hLen₂
    have hcb₁ : rc₁.2.val * b < d * b := Nat.mul_lt_mul_of_pos_right rc₁.2.val_lt hbPos
    have hcb₂ : rc₂.2.val * b < d * b := Nat.mul_lt_mul_of_pos_right rc₂.2.val_lt hbPos
    have hIdx₁ : (outputBitIdx d rc₁.1 rc₁.2 ℓ₀).val = rc₁.1.val * (d * b) + rc₁.2.val * b := by
      change rc₁.1.val * (d * b) + rc₁.2.val * b + 0 = _; omega
    have hIdx₂ : (outputBitIdx d rc₂.1 rc₂.2 ℓ₀).val = rc₂.1.val * (d * b) + rc₂.2.val * b := by
      change rc₂.1.val * (d * b) + rc₂.2.val * b + 0 = _; omega
    obtain ⟨hDiv₁, hMod₁⟩ := mul_add_div_mod hcb₁
    obtain ⟨hDiv₂, hMod₂⟩ := mul_add_div_mod hcb₂
    rw [← hIdx₁] at hDiv₁ hMod₁
    rw [← hIdx₂, ← hValEq] at hDiv₂ hMod₂
    have hrVal : rc₁.1.val = rc₂.1.val := hDiv₁.symm.trans hDiv₂
    have hcMul : rc₁.2.val * b = rc₂.2.val * b := hMod₁.symm.trans hMod₂
    have hcVal : rc₁.2.val = rc₂.2.val := by
      have h1 := Nat.mul_div_cancel rc₁.2.val hbPos
      have h2 := Nat.mul_div_cancel rc₂.2.val hbPos
      rw [← h1, ← h2, hcMul]
    ext
    · rw [← ZMod.natCast_zmod_val rc₁.1, ← ZMod.natCast_zmod_val rc₂.1, hrVal]
    · rw [← ZMod.natCast_zmod_val rc₁.2, ← ZMod.natCast_zmod_val rc₂.2, hcVal]
  set Delta := b * (M.k + 1) ^ D
  have hDltDelta : D + 1 ≤ Delta := by
    calc D + 1 ≤ 2 ^ D := nat_add_one_le_two_pow D
      _ ≤ (M.k + 1) ^ D := Nat.pow_le_pow_left (by omega) D
      _ = 1 * (M.k + 1) ^ D := (one_mul _).symm
      _ ≤ b * (M.k + 1) ^ D := Nat.mul_le_mul_right _ hbPos
  have hdPos : 1 ≤ d := NeZero.one_le
  have hUnivCard : (Finset.univ : Finset (ZMod d × ZMod d)).card = d ^ 2 := by
    simp [ZMod.card, sq]
  have hCutComplCard :
      (Finset.univ \ cutTouchingOutputCells d T workPos emitStep Γ).card ≤ D := by
    have hSub :
        (Finset.univ \ cutTouchingOutputCells d T workPos emitStep Γ).image cellEmit ⊆
          Finset.range D := by
      intro v hv
      rcases Finset.mem_image.mp hv with ⟨rc, hrc, rfl⟩
      have hNotCut : rc ∉ cutTouchingOutputCells d T workPos emitStep Γ :=
        (Finset.mem_sdiff.mp hrc).2
      rw [Finset.mem_range]
      by_contra hGe
      have hDv : D ≤ cellEmit rc := by omega
      have hvT : cellEmit rc < T := hFibre.2.1 _
      obtain ⟨u, huΓ, _, _, hCone, hDep⟩ :=
        exists_recent_cut_of_ge_depth workPos T D Γ hPathLen hvT hDv
      apply hNotCut
      unfold cutTouchingOutputCells
      exact (@Finset.mem_filter _ _ (fun _ => Classical.propDecidable _) Finset.univ rc).mpr
        ⟨Finset.mem_univ rc, ℓ₀, u + 1, u, hCone, huΓ, hDep⟩
    calc (Finset.univ \ cutTouchingOutputCells d T workPos emitStep Γ).card
        = ((Finset.univ \ cutTouchingOutputCells d T workPos emitStep Γ).image cellEmit).card :=
          (Finset.card_image_of_injective _ hCellEmitInj).symm
      _ ≤ (Finset.range D).card := Finset.card_le_card hSub
      _ = D := Finset.card_range D
  have hPart1Count : d ^ 2 ≤ (cutTouchingOutputCells d T workPos emitStep Γ).card + D := by
    have hSdiff := Finset.card_sdiff_add_card_eq_card
      (Finset.subset_univ (cutTouchingOutputCells d T workPos emitStep Γ))
    rw [hUnivCard] at hSdiff
    omega
  refine ⟨⟨hPart1Count, fun M₀ E_sched hM₀ => ?_⟩, ?_⟩
  · have hCutSub : (cutTouchingOutputCells d T workPos emitStep Γ).card ≤
        (E_sched ∪ cutTouchingOutputCells d T workPos emitStep Γ).card :=
      Finset.card_le_card Finset.subset_union_right
    have hdM₀Pos : 1 ≤ d * M₀ := Nat.mul_le_mul hdPos hM₀
    have hDltProd : D < d * M₀ * Delta := by
      calc D < Delta := by omega
        _ = 1 * Delta := (one_mul _).symm
        _ ≤ (d * M₀) * Delta := Nat.mul_le_mul_right _ hdM₀Pos
    have hStrictNat :
        d ^ 2 < (E_sched ∪ cutTouchingOutputCells d T workPos emitStep Γ).card + d * M₀ * Delta :=
      by omega
    have hStrictReal :
        ((d ^ 2 : ℕ) : ℝ) <
          (((E_sched ∪ cutTouchingOutputCells d T workPos emitStep Γ).card +
            d * M₀ * Delta : ℕ) : ℝ) := by exact_mod_cast hStrictNat
    push_cast at hStrictReal
    linarith
  · intro L_cut E_sched colCutStep hColCutsCover
    let window (cs : ZMod d × Fin L_cut) : Finset ℕ :=
      Finset.Ioc (colCutStep cs.1 cs.2) (colCutStep cs.1 cs.2 + D)
    let targetSteps : Finset ℕ := Finset.range D ∪ Finset.univ.biUnion window
    have hSub : (Finset.univ \ E_sched).image cellEmit ⊆ targetSteps := by
      intro v hv
      rcases Finset.mem_image.mp hv with ⟨⟨r, c⟩, hrc, rfl⟩
      have hNotE : (r, c) ∉ E_sched := (Finset.mem_sdiff.mp hrc).2
      by_cases hLt : cellEmit (r, c) < D
      · exact Finset.mem_union_left _ (Finset.mem_range.mpr hLt)
      · have hDv : D ≤ cellEmit (r, c) := by omega
        have hvT : cellEmit (r, c) < T := hFibre.2.1 _
        obtain ⟨u, huΓ, huLo, huHi, hCone, hDep⟩ :=
          exists_recent_cut_of_ge_depth workPos T D Γ hPathLen hvT hDv
        obtain ⟨s, hs⟩ := hColCutsCover r c hNotE ℓ₀ (u + 1) u hCone huΓ hDep
        refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨(c, s), Finset.mem_univ _, ?_⟩)
        dsimp [window]
        rw [hs, Finset.mem_Ioc]
        omega
    have hTargetCard : targetSteps.card ≤ D + d * L_cut * D := by
      calc targetSteps.card
          ≤ (Finset.range D).card + (Finset.univ.biUnion window).card := Finset.card_union_le _ _
        _ ≤ D + ∑ cs : ZMod d × Fin L_cut, (window cs).card := by
            rw [Finset.card_range]
            exact Nat.add_le_add_left Finset.card_biUnion_le D
        _ = D + ∑ _cs : ZMod d × Fin L_cut, D := by
            congr 1
            refine Finset.sum_congr rfl fun cs _ => ?_
            simp [window]
        _ = D + (d * L_cut) * D := by simp [ZMod.card]
        _ = D + d * L_cut * D := by ring
    have hSdiffLe : (Finset.univ \ E_sched).card ≤ D + d * L_cut * D := by
      calc (Finset.univ \ E_sched).card
          = ((Finset.univ \ E_sched).image cellEmit).card :=
            (Finset.card_image_of_injective _ hCellEmitInj).symm
        _ ≤ targetSteps.card := Finset.card_le_card hSub
        _ ≤ D + d * L_cut * D := hTargetCard
    have hPart2Count : d ^ 2 ≤ E_sched.card + D + d * L_cut * D := by
      have hSdiff := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ E_sched)
      rw [hUnivCard] at hSdiff
      omega
    refine ⟨hPart2Count, fun M₀ hM₀ hAlphabet => ?_⟩
    set M_cls := M₀ * ((M.q + 1) * (M.g + 1) ^ M.k) ^ L_cut
    have hLcutLeMcls : L_cut + 1 ≤ M_cls := by
      calc L_cut + 1 ≤ 2 ^ L_cut := nat_add_one_le_two_pow L_cut
        _ ≤ ((M.q + 1) * (M.g + 1) ^ M.k) ^ L_cut := Nat.pow_le_pow_left hAlphabet L_cut
        _ = 1 * ((M.q + 1) * (M.g + 1) ^ M.k) ^ L_cut := (one_mul _).symm
        _ ≤ M_cls := Nat.mul_le_mul_right _ hM₀
    have hUnbrokenLt : D + d * L_cut * D < d * M_cls * Delta := by
      have h1 : D ≤ d * D := Nat.le_mul_of_pos_left D hdPos
      have h2 : D + d * L_cut * D ≤ (d * (L_cut + 1)) * D := by
        calc D + d * L_cut * D ≤ d * D + d * L_cut * D := Nat.add_le_add_right h1 _
          _ = (d * (L_cut + 1)) * D := by ring
      have hPosCoeff : 0 < d * (L_cut + 1) := Nat.mul_pos hdPos (Nat.succ_pos L_cut)
      have h3 : (d * (L_cut + 1)) * D < (d * (L_cut + 1)) * Delta :=
        Nat.mul_lt_mul_of_pos_left (by omega) hPosCoeff
      have h4 : (d * (L_cut + 1)) * Delta ≤ (d * M_cls) * Delta :=
        Nat.mul_le_mul_right Delta (Nat.mul_le_mul_left d hLcutLeMcls)
      calc D + d * L_cut * D ≤ (d * (L_cut + 1)) * D := h2
        _ < (d * (L_cut + 1)) * Delta := h3
        _ ≤ d * M_cls * Delta := h4
    have hStrictNat : d ^ 2 < E_sched.card + d * M_cls * Delta := by omega
    have hStrictReal :
        ((d ^ 2 : ℕ) : ℝ) < ((E_sched.card + d * M_cls * Delta : ℕ) : ℝ) := by
      exact_mod_cast hStrictNat
    push_cast at hStrictReal
    linarith

/-! ### 4. Work-Tape Padding Utility -/

/-- Adding a single stationary dummy work tape when `M₀.k = 0` preserves `Transpose.TransposesWithin`
for every time bound `T`, ensuring `1 ≤ M.k`. -/
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

end BoundedArityDecoders
