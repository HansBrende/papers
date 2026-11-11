import BoundedArityDecoders.NativeSweepInterface
import BoundedArityDecoders.BoundedAritySetCapacityProofs

/-!
# Kernel-Verified Proofs — Section I & Part III.B: Native Sweep-Cone Interface

Complete proofs for all unconditional claim specifications in `NativeSweepInterface.lean`:

1. `entryBits_eq_clog : ∀ d : ℕ, 2 ≤ d → Transpose.entryBits d = Nat.clog 2 d`
2. `tmTraceCutConeDetermination : TMTraceCutConeDeterminationSpec`
3. `periodicSweepInducesBoundedAritySharedCode : PeriodicSweepInducesBoundedAritySharedCodeSpec`
4. `periodicSweepNonlinearFibreDeficit : PeriodicSweepNonlinearFibreDeficitSpec`
-/

namespace BoundedArityDecoders

open SharedDecoders
open scoped BigOperators

/-! ### 1. Canonical Entry-Width Agreement `entryBits d = ⌈log₂ d⌉` -/

theorem entryBits_eq_clog : ∀ d : ℕ, 2 ≤ d → Transpose.entryBits d = Nat.clog 2 d := by
  intro d hd
  unfold Transpose.entryBits
  have hm0 : d - 1 ≠ 0 := by omega
  have hlo : 2 ^ (d - 1).log2 ≤ d - 1 := Nat.log2_self_le hm0
  have hhi : d - 1 < 2 ^ ((d - 1).log2 + 1) := Nat.lt_log2_self
  apply le_antisymm
  · have hlt : (d - 1).log2 < Nat.clog 2 d :=
      (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).mpr (by omega)
    omega
  · exact (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr (by omega)

/-! ### 2. `Transpose.TM` Encoding, Execution & `Γ`-Cut Cone Fan-In / Determination -/

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
  | zero =>
    refine ⟨by simp [Transpose.concatUpTo], fun idx hidx => ?_⟩
    simp at hidx
  | succ m ih =>
    obtain ⟨ihLen, ihGet⟩ := ih (fun k hk => hlen k (Nat.lt_succ_of_lt hk))
    have hfmLen : (f m).length = s := hlen m (Nat.lt_succ_self m)
    refine ⟨?_, ?_⟩
    · simp only [Transpose.concatUpTo, List.length_append, ihLen, hfmLen]
      ring
    · intro idx hidx
      simp only [Transpose.concatUpTo]
      by_cases hlt : idx < m * s
      · rw [List.getElem?_append_left (by omega)]
        exact ihGet idx hlt
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
  have hg₂ : ∀ i j, (g₂ i j).length = b ∧
      ∀ t < b, (g₂ i j)[t]? = some (A i j t) := by
    intro i j
    obtain ⟨hL, hG⟩ := concatUpTo_length_and_getElem? (f := fun t => [A i j t]) (m := b) (s := 1)
      (fun _ _ => rfl)
    refine ⟨by simpa using hL, fun t ht => ?_⟩
    have h := hG t (by simpa using ht)
    simpa [g₂, Nat.mod_one] using h
  let g₁ (i : ℕ) : List Bool := Transpose.concatUpTo (g₂ i) d
  have hg₁ : ∀ i, (g₁ i).length = d * b ∧
      ∀ rem < d * b, (g₁ i)[rem]? = some (A i (rem / b) (rem % b)) := by
    intro i
    obtain ⟨hL, hG⟩ := concatUpTo_length_and_getElem? (f := g₂ i) (m := d) (s := b)
      (fun j _ => (hg₂ i j).1)
    refine ⟨hL, fun rem hrem => ?_⟩
    have hbPos : 0 < b := by
      by_contra hb0
      have hb0' : b = 0 := by omega
      rw [hb0', mul_zero] at hrem
      exact Nat.not_lt_zero rem hrem
    rw [hG rem hrem, (hg₂ i (rem / b)).2 (rem % b) (Nat.mod_lt rem hbPos)]
  obtain ⟨hL, hG⟩ := concatUpTo_length_and_getElem? (f := g₁) (m := d) (s := d * b)
    (fun i _ => (hg₁ i).1)
  have hAssoc : d * (d * b) = d * d * b := (Nat.mul_assoc d d b).symm
  refine ⟨by simpa only [Transpose.encode, g₁, g₂, hAssoc] using hL, ?_⟩
  intro idx hidx
  have hidx' : idx < d * (d * b) := by omega
  have hdbPos : 0 < d * b := by
    by_contra h0
    have h0' : d * b = 0 := by omega
    rw [h0', mul_zero] at hidx'
    exact Nat.not_lt_zero idx hidx'
  change (Transpose.concatUpTo g₁ d)[idx]? = _
  rw [hG idx hidx', (hg₁ (idx / (d * b))).2 (idx % (d * b)) (Nat.mod_lt idx hdbPos)]

private def inputCellOfPos (d : ℕ) [NeZero d] (p : Int) : Option (ZMod d × ZMod d) :=
  if 0 ≤ p ∧ p.toNat < Transpose.inputLength d then
    let b := Transpose.entryBits d
    some (((p.toNat / (d * b) : ℕ) : ZMod d),
          (((p.toNat % (d * b)) / b : ℕ) : ZMod d))
  else none

private theorem readInput_encodeCanonicalState_eq {d : ℕ} [NeZero d]
    (X₁ X₂ : State d (CanonicalWordAlphabet d)) (p : Int)
    (hAgree : ∀ ij : ZMod d × ZMod d, inputCellOfPos d p = some ij → X₁ ij.1 ij.2 = X₂ ij.1 ij.2) :
    Transpose.readInput (encodeCanonicalState X₁) p =
      Transpose.readInput (encodeCanonicalState X₂) p := by
  unfold Transpose.readInput
  by_cases hp0 : p < 0
  · simp [hp0]
  · rw [ite_eq_right hp0, ite_eq_right hp0, nth_eq_getElem?, nth_eq_getElem?]
    have hpNonneg : 0 ≤ p := Int.le_of_not_gt hp0
    let b := Transpose.entryBits d
    let L := Transpose.inputLength d
    have hLen₁ := (encode_length_and_getElem? d b (stateToTMMatrix X₁)).1
    have hLen₂ := (encode_length_and_getElem? d b (stateToTMMatrix X₂)).1
    by_cases hpL : p.toNat < L
    · have hpL' : p.toNat < d * d * b := hpL
      have hG₁ := (encode_length_and_getElem? d b (stateToTMMatrix X₁)).2 p.toNat hpL'
      have hG₂ := (encode_length_and_getElem? d b (stateToTMMatrix X₂)).2 p.toNat hpL'
      change (Transpose.encode d b (stateToTMMatrix X₁))[p.toNat]? =
        (Transpose.encode d b (stateToTMMatrix X₂))[p.toNat]?
      rw [hG₁, hG₂]
      congr 1
      set iNat := p.toNat / (d * b)
      set jNat := (p.toNat % (d * b)) / b
      set tNat := (p.toNat % (d * b)) % b
      have hbPos : 0 < b := by
        dsimp [b, Transpose.entryBits]
        omega
      have htLt : tNat < Transpose.entryBits d := Nat.mod_lt _ hbPos
      have hCell : inputCellOfPos d p = some ((iNat : ZMod d), (jNat : ZMod d)) := by
        unfold inputCellOfPos
        rw [ite_eq_left ⟨hpNonneg, hpL⟩]
      have hX := hAgree ((iNat : ZMod d), (jNat : ZMod d)) hCell
      unfold stateToTMMatrix
      rw [dite_eq_left htLt, dite_eq_left htLt]
      exact congrFun hX ⟨tNat, htLt⟩
    · have hGe : d * d * b ≤ p.toNat := Nat.le_of_not_gt hpL
      change (Transpose.encode d b (stateToTMMatrix X₁))[p.toNat]? =
        (Transpose.encode d b (stateToTMMatrix X₂))[p.toNat]?
      rw [List.getElem?_eq_none (hLen₁ ▸ hGe), List.getElem?_eq_none (hLen₂ ▸ hGe)]

private theorem stepN_add (M : Transpose.TM) (w : List Bool) :
    ∀ (a b : ℕ) (c : Transpose.Config M),
      Transpose.stepN M w (a + b) c =
        match Transpose.stepN M w a c with
        | none => none
        | some c' => Transpose.stepN M w b c'
  | 0, b, c => by simp [Transpose.stepN]
  | a + 1, b, c => by
    rw [Nat.succ_add]
    simp only [Transpose.stepN]
    cases Transpose.step M w c with
    | none => rfl
    | some c' => exact stepN_add M w a b c'

private theorem tmCfgAt_succ {M : Transpose.TM} {w : List Bool} {t : ℕ} {cfg : Transpose.Config M}
    (h : tmCfgAt M w t = some cfg) :
    tmCfgAt M w (t + 1) = Transpose.step M w cfg := by
  unfold tmCfgAt at h ⊢
  rw [stepN_add M w t 1 (Transpose.init M), h]
  simp only [Transpose.stepN]
  cases Transpose.step M w cfg <;> rfl

private theorem outRev_reverse_prefix_of_step {M : Transpose.TM} {w : List Bool}
    {c c' : Transpose.Config M} (h : Transpose.step M w c = some c') :
    c.outRev.reverse <+: c'.outRev.reverse := by
  unfold Transpose.step at h
  cases hδ : M.δ c.state (Transpose.readInput w c.inPos) (fun i => c.work i (c.workPos i)) <;>
    rw [hδ] at h
  · cases h
  · rename_i val
    rcases val with ⟨s, dir, acts, o⟩
    simp only [Option.some.injEq] at h
    subst h
    cases o with
    | none => exact List.prefix_refl _
    | some bit =>
      simp only [List.reverse_cons]
      exact ⟨[bit], rfl⟩

private theorem outRev_reverse_prefix_of_stepN (M : Transpose.TM) (w : List Bool) :
    ∀ (n : ℕ) (c c' : Transpose.Config M),
      Transpose.stepN M w n c = some c' →
      c.outRev.reverse <+: c'.outRev.reverse
  | 0, c, c', h => by
    simp only [Transpose.stepN, Option.some.injEq] at h
    subst h
    exact List.prefix_refl _
  | n + 1, c, c', h => by
    simp only [Transpose.stepN] at h
    cases hs : Transpose.step M w c <;> rw [hs] at h
    · cases h
    · rename_i cmid
      exact (outRev_reverse_prefix_of_step hs).trans (outRev_reverse_prefix_of_stepN M w n cmid c' h)

private theorem isLastWorkVisit_unique {k : ℕ} {workPos : ℕ → Fin k → Int} {h : Fin k}
    {u₁ u₂ v : ℕ}
    (h₁ : IsLastWorkVisit workPos h u₁ v)
    (h₂ : IsLastWorkVisit workPos h u₂ v) :
    u₁ = u₂ := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact h₁.2.2 u₂ hlt h₂.1 h₂.2.1
  · exact h₂.2.2 u₁ hlt h₁.1 h₁.2.1

private noncomputable def directPreds {k : ℕ} (workPos : ℕ → Fin k → Int) (T : ℕ)
    (Γ : Finset ℕ) (v : ℕ) : Finset ℕ :=
  have := Classical.propDecidable
  (Finset.range T).filter (fun u => TMDepStep workPos T u v ∧ u ∉ Γ)

private theorem directPreds_card_le {k : ℕ} (workPos : ℕ → Fin k → Int) (T : ℕ)
    (Γ : Finset ℕ) (v : ℕ) :
    (directPreds workPos T Γ v).card ≤ k + 1 := by
  classical
  let lastSet (h : Fin k) : Finset ℕ :=
    (Finset.range v).filter (fun u => IsLastWorkVisit workPos h u v)
  have hLastLe1 : ∀ h : Fin k, (lastSet h).card ≤ 1 := by
    intro h
    refine Finset.card_le_one.mpr ?_
    intro u₁ hu₁ u₂ hu₂
    exact isLastWorkVisit_unique (Finset.mem_filter.mp hu₁).2 (Finset.mem_filter.mp hu₂).2
  have hSub : directPreds workPos T Γ v ⊆
      ({v - 1} : Finset ℕ) ∪ Finset.univ.biUnion lastSet := by
    intro u hu
    unfold directPreds at hu
    simp only [Finset.mem_filter] at hu
    rcases hu.2.1.2 with rfl | ⟨h, hLast⟩
    · exact Finset.mem_union_left _ (Finset.mem_singleton.mpr rfl)
    · refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨h, Finset.mem_univ h, ?_⟩)
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hLast.1, hLast⟩
  calc (directPreds workPos T Γ v).card
      ≤ (({v - 1} : Finset ℕ) ∪ Finset.univ.biUnion lastSet).card := Finset.card_le_card hSub
    _ ≤ ({v - 1} : Finset ℕ).card + (Finset.univ.biUnion lastSet).card := Finset.card_union_le _ _
    _ ≤ 1 + ∑ h : Fin k, (lastSet h).card :=
        Nat.add_le_add (Finset.card_singleton _).le Finset.card_biUnion_le
    _ ≤ 1 + ∑ _h : Fin k, 1 := Nat.add_le_add_left (Finset.sum_le_sum fun h _ => hLastLe1 h) 1
    _ = k + 1 := by simp [Nat.add_comm]

private noncomputable def coneAtDepth {k : ℕ} (workPos : ℕ → Fin k → Int) (T : ℕ)
    (Γ : Finset ℕ) : ℕ → ℕ → Finset ℕ
  | 0, _ => ∅
  | m + 1, v => insert v ((directPreds workPos T Γ v).biUnion (coneAtDepth workPos T Γ m))

private theorem coneAtDepth_card_succ_le {k : ℕ} (workPos : ℕ → Fin k → Int) (T : ℕ)
    (Γ : Finset ℕ) (hk : 1 ≤ k) :
    ∀ (m : ℕ), 1 ≤ m → ∀ v : ℕ, (coneAtDepth workPos T Γ m v).card + 1 ≤ (k + 1) ^ m
  | 0, hm, _ => absurd hm (by decide)
  | 1, _, v => by
    have hEmpty : (directPreds workPos T Γ v).biUnion (coneAtDepth workPos T Γ 0) = ∅ := by
      ext x
      simp [coneAtDepth]
    have hCard : (coneAtDepth workPos T Γ 1 v).card = 1 := by
      change (insert v ((directPreds workPos T Γ v).biUnion (coneAtDepth workPos T Γ 0))).card = 1
      rw [hEmpty]
      rfl
    rw [hCard, pow_one]
    omega
  | m + 2, _, v => by
    have ih := fun u => coneAtDepth_card_succ_le workPos T Γ hk (m + 1) (by omega) u
    have hPowPos : 1 ≤ (k + 1) ^ (m + 1) := Nat.one_le_pow _ _ (by omega)
    have hBiUnion :
        ((directPreds workPos T Γ v).biUnion (coneAtDepth workPos T Γ (m + 1))).card ≤
          (k + 1) * ((k + 1) ^ (m + 1) - 1) := by
      calc ((directPreds workPos T Γ v).biUnion (coneAtDepth workPos T Γ (m + 1))).card
          ≤ ∑ u ∈ directPreds workPos T Γ v, (coneAtDepth workPos T Γ (m + 1) u).card :=
            Finset.card_biUnion_le
        _ ≤ ∑ _u ∈ directPreds workPos T Γ v, ((k + 1) ^ (m + 1) - 1) := by
            refine Finset.sum_le_sum fun u _ => ?_
            have hu := ih u
            omega
        _ = (directPreds workPos T Γ v).card * ((k + 1) ^ (m + 1) - 1) := by simp
        _ ≤ (k + 1) * ((k + 1) ^ (m + 1) - 1) :=
            Nat.mul_le_mul_right _ (directPreds_card_le workPos T Γ v)
    have hIns :
        (coneAtDepth workPos T Γ (m + 2) v).card ≤
          1 + ((directPreds workPos T Γ v).biUnion (coneAtDepth workPos T Γ (m + 1))).card := by
      simpa only [coneAtDepth, Nat.add_comm] using
        Finset.card_insert_le v
          ((directPreds workPos T Γ v).biUnion (coneAtDepth workPos T Γ (m + 1)))
    have hExpand :
        (k + 1) * ((k + 1) ^ (m + 1) - 1) + (k + 1) = (k + 1) ^ (m + 2) := by
      calc (k + 1) * ((k + 1) ^ (m + 1) - 1) + (k + 1)
          = (k + 1) * ((k + 1) ^ (m + 1) - 1 + 1) := by ring
        _ = (k + 1) * (k + 1) ^ (m + 1) := by rw [Nat.sub_add_cancel hPowPos]
        _ = (k + 1) ^ (m + 2) := by rw [← pow_succ']
    omega

private theorem mem_coneAtDepth_of_path {k : ℕ} (workPos : ℕ → Fin k → Int) (T : ℕ)
    (Γ : Finset ℕ) :
    ∀ (m : ℕ) (π : List ℕ) (v u : ℕ),
      IsCutFreeCausalPath workPos T Γ π →
      π.head? = some v →
      π.getLast? = some u →
      π.length ≤ m →
      u ∈ coneAtDepth workPos T Γ m v
  | _, [], _, _, _, hhead, _, _ => by simp at hhead
  | 0, _ :: _, _, _, _, _, _, hlen => by simp at hlen
  | m + 1, [w], v, u, _, hhead, hlast, _ => by
    simp only [List.head?_cons, Option.some.injEq] at hhead
    simp only [List.getLast?_singleton, Option.some.injEq] at hlast
    subst hhead; subst hlast
    exact Finset.mem_insert_self _ _
  | 0 + 1, _ :: _ :: _, _, _, _, _, _, hlen => by simp at hlen
  | m + 2, w :: x :: rest, v, u, hpath, hhead, hlast, hlen => by
    simp only [List.head?_cons, Option.some.injEq] at hhead
    subst hhead
    rcases hpath with ⟨hdep, hxNotΓ, hrest⟩
    have hlast' : (x :: rest).getLast? = some u := by
      simpa only [List.getLast?_cons_cons] using hlast
    have hlen' : (x :: rest).length ≤ m + 1 := by
      simp only [List.length_cons] at hlen ⊢
      omega
    have hxLtV : x < w := by
      rcases hdep.2 with hEq | ⟨_, hLast⟩
      · omega
      · exact hLast.1
    have hxLtT : x < T := Nat.lt_trans hxLtV hdep.1
    have hxMemPred : x ∈ directPreds workPos T Γ w := by
      unfold directPreds
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨hxLtT, hdep, hxNotΓ⟩
    have huMem : u ∈ coneAtDepth workPos T Γ (m + 1) x :=
      mem_coneAtDepth_of_path workPos T Γ (m + 1) (x :: rest) x u hrest rfl hlast' hlen'
    exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨x, hxMemPred, huMem⟩)

private noncomputable def trueConeSteps {k : ℕ} (workPos : ℕ → Fin k → Int) (T : ℕ)
    (Γ : Finset ℕ) (v : ℕ) : Finset ℕ :=
  have := Classical.propDecidable
  (Finset.range T).filter (fun u => InCutCausalCone workPos T Γ v u)

private theorem self_mem_trueConeSteps {k : ℕ} (workPos : ℕ → Fin k → Int) (T : ℕ)
    (Γ : Finset ℕ) {v : ℕ} (hv : v < T) :
    v ∈ trueConeSteps workPos T Γ v := by
  unfold trueConeSteps
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨hv, [v], rfl, rfl, hv⟩

private theorem trueConeSteps_subset_of_dep {k : ℕ} (workPos : ℕ → Fin k → Int) (T : ℕ)
    (Γ : Finset ℕ) {u v : ℕ} (hdep : TMDepStep workPos T u v) (huNotΓ : u ∉ Γ) :
    trueConeSteps workPos T Γ u ⊆ trueConeSteps workPos T Γ v := by
  intro w hw
  unfold trueConeSteps at hw ⊢
  simp only [Finset.mem_filter, Finset.mem_range] at hw ⊢
  rcases hw with ⟨hwT, π, hhead, hlast, hpath⟩
  cases π with
  | nil => simp at hhead
  | cons x rest =>
    simp only [List.head?_cons, Option.some.injEq] at hhead
    subst x
    refine ⟨hwT, v :: u :: rest, rfl, ?_, ⟨hdep, huNotΓ, hpath⟩⟩
    simpa only [List.getLast?_cons_cons] using hlast

private theorem work_preserved_between {M : Transpose.TM} {d T : ℕ} [NeZero d]
    {inPos : ℕ → Int} {workPos : ℕ → Fin M.k → Int}
    {emitStep : Fin (Transpose.inputLength d) → ℕ} {Γ : Finset ℕ}
    {C : Set (State d (CanonicalWordAlphabet d))}
    (hFibre : IsFrozenTraceCutFibre M d T inPos workPos emitStep Γ C)
    {X : State d (CanonicalWordAlphabet d)} (hX : X ∈ C)
    (h : Fin M.k) (pos : Int) :
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
    rw [hcfg₁] at hcfg₂
    injection hcfg₂ with hEq
    rw [hEq]
  | succ t₂ ih =>
    by_cases hEqT : t₁ = t₂ + 1
    · subst hEqT
      rw [hcfg₁] at hcfg₂
      injection hcfg₂ with hEq
      rw [hEq]
    · have hle' : t₁ ≤ t₂ := by omega
      obtain ⟨cfgMid, hcfgMid, _, hworkPosMid⟩ := hFibre.2.2.2.1 X hX t₂ (by omega)
      have hMidEq : cfgMid.work h pos = cfg₁.work h pos :=
        ih hle' (by omega) (fun w hw₁ hw₂ => hnoVisit w hw₁ (by omega)) cfgMid hcfgMid
      have hStep : Transpose.step M (encodeCanonicalState X) cfgMid = some cfg₂ := by
        rw [← tmCfgAt_succ hcfgMid]
        exact hcfg₂
      unfold Transpose.step at hStep
      cases hδ : M.δ cfgMid.state
          (Transpose.readInput (encodeCanonicalState X) cfgMid.inPos)
          (fun i => cfgMid.work i (cfgMid.workPos i)) <;> rw [hδ] at hStep
      · cases hStep
      · rename_i val
        rcases val with ⟨s, dir, acts, o⟩
        simp only [Option.some.injEq] at hStep
        subst hStep
        have hne : pos ≠ cfgMid.workPos h := by
          have hw := hnoVisit t₂ hle' (Nat.lt_succ_self t₂)
          have hposEq : cfgMid.workPos h = workPos t₂ h := congrFun hworkPosMid h
          rw [hposEq]
          exact hw.symm
        simp only [hne, ite_false]
        exact hMidEq

private theorem exists_lastWorkVisit_or_never {k : ℕ} (workPos : ℕ → Fin k → Int)
    (h : Fin k) (v : ℕ) :
    (∀ u < v, workPos u h ≠ workPos v h) ∨
      ∃ u : ℕ, IsLastWorkVisit workPos h u v := by
  classical
  let S : Finset ℕ := (Finset.range v).filter (fun u => workPos u h = workPos v h)
  by_cases hSne : S.Nonempty
  · right
    refine ⟨S.max' hSne, ?_⟩
    have hMem := Finset.max'_mem S hSne
    simp only [S, Finset.mem_filter, Finset.mem_range] at hMem
    refine ⟨hMem.1, hMem.2, fun w hw₁ hw₂ hEq => ?_⟩
    have hwMem : w ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hw₂, hEq⟩
    have hwLe : w ≤ S.max' hSne := Finset.le_max' S w hwMem
    omega
  · left
    intro u huv hEq
    exact hSne ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr huv, hEq⟩⟩

private theorem delta_agree_on_trueConeSteps {M : Transpose.TM} {d T : ℕ} [NeZero d]
    {inPos : ℕ → Int} {workPos : ℕ → Fin M.k → Int}
    {emitStep : Fin (Transpose.inputLength d) → ℕ} {Γ : Finset ℕ}
    {C : Set (State d (CanonicalWordAlphabet d))}
    (hFibre : IsFrozenTraceCutFibre M d T inPos workPos emitStep Γ C)
    {X₁ X₂ : State d (CanonicalWordAlphabet d)} (hX₁ : X₁ ∈ C) (hX₂ : X₂ ∈ C) :
    ∀ v < T,
      (∀ w ∈ trueConeSteps workPos T Γ v, ∀ ij : ZMod d × ZMod d,
        inputCellOfPos d (inPos w) = some ij → X₁ ij.1 ij.2 = X₂ ij.1 ij.2) →
      ∀ (cfg₁ cfg₂ : Transpose.Config M),
        tmCfgAt M (encodeCanonicalState X₁) v = some cfg₁ →
        tmCfgAt M (encodeCanonicalState X₂) v = some cfg₂ →
        M.δ cfg₁.state (Transpose.readInput (encodeCanonicalState X₁) cfg₁.inPos)
            (fun i => cfg₁.work i (cfg₁.workPos i)) =
          M.δ cfg₂.state (Transpose.readInput (encodeCanonicalState X₂) cfg₂.inPos)
            (fun i => cfg₂.work i (cfg₂.workPos i)) := by
  intro v
  induction v using Nat.strong_induction_on with
  | h v ih =>
    intro hvT hAgree cfg₁ cfg₂ hcfg₁ hcfg₂
    obtain ⟨cfg₁', hcfg₁', hin₁, hwpos₁⟩ := hFibre.2.2.2.1 X₁ hX₁ v (Nat.le_of_lt hvT)
    obtain ⟨cfg₂', hcfg₂', hin₂, hwpos₂⟩ := hFibre.2.2.2.1 X₂ hX₂ v (Nat.le_of_lt hvT)
    rw [hcfg₁] at hcfg₁'; injection hcfg₁' with hEq₁; subst hEq₁
    rw [hcfg₂] at hcfg₂'; injection hcfg₂' with hEq₂; subst hEq₂
    have hInAgree :
        Transpose.readInput (encodeCanonicalState X₁) cfg₁.inPos =
          Transpose.readInput (encodeCanonicalState X₂) cfg₂.inPos := by
      rw [hin₁, hin₂]
      exact readInput_encodeCanonicalState_eq X₁ X₂ (inPos v)
        (hAgree v (self_mem_trueConeSteps workPos T Γ hvT))
    have hStateAgree : cfg₁.state = cfg₂.state := by
      cases v with
      | zero =>
        simp only [tmCfgAt, Transpose.stepN, Option.some.injEq] at hcfg₁ hcfg₂
        rw [← hcfg₁, ← hcfg₂]
      | succ u =>
        by_cases huΓ : u ∈ Γ
        · exact (hFibre.2.2.2.2.2 X₁ hX₁ X₂ hX₂ u huΓ cfg₁ cfg₂ hcfg₁ hcfg₂).1
        · have hdep : TMDepStep workPos T u (u + 1) := ⟨hvT, Or.inl rfl⟩
          have hSub := trueConeSteps_subset_of_dep workPos T Γ hdep huΓ
          obtain ⟨cU₁, hcU₁, _, _⟩ := hFibre.2.2.2.1 X₁ hX₁ u (by omega)
          obtain ⟨cU₂, hcU₂, _, _⟩ := hFibre.2.2.2.1 X₂ hX₂ u (by omega)
          have hδU := ih u (Nat.lt_succ_self u) (by omega)
            (fun w hw => hAgree w (hSub hw)) cU₁ cU₂ hcU₁ hcU₂
          have hStep₁ : Transpose.step M (encodeCanonicalState X₁) cU₁ = some cfg₁ := by
            rw [← tmCfgAt_succ hcU₁]; exact hcfg₁
          have hStep₂ : Transpose.step M (encodeCanonicalState X₂) cU₂ = some cfg₂ := by
            rw [← tmCfgAt_succ hcU₂]; exact hcfg₂
          unfold Transpose.step at hStep₁ hStep₂
          rw [hδU] at hStep₁
          cases hδVal : M.δ cU₂.state (Transpose.readInput (encodeCanonicalState X₂) cU₂.inPos)
              (fun i => cU₂.work i (cU₂.workPos i)) <;> rw [hδVal] at hStep₁ hStep₂
          · cases hStep₁
          · rename_i val
            rcases val with ⟨s, dir, acts, o⟩
            simp only [Option.some.injEq] at hStep₁ hStep₂
            rw [← hStep₁, ← hStep₂]
    have hWorkAgree :
        (fun i => cfg₁.work i (cfg₁.workPos i)) =
          (fun i => cfg₂.work i (cfg₂.workPos i)) := by
      funext h
      have hwp₁ : cfg₁.workPos h = workPos v h := congrFun hwpos₁ h
      have hwp₂ : cfg₂.workPos h = workPos v h := congrFun hwpos₂ h
      rw [hwp₁, hwp₂]
      rcases exists_lastWorkVisit_or_never workPos h v with hNever | ⟨u, hLast⟩
      · have hc₀₁ : tmCfgAt M (encodeCanonicalState X₁) 0 = some (Transpose.init M) := rfl
        have hc₀₂ : tmCfgAt M (encodeCanonicalState X₂) 0 = some (Transpose.init M) := rfl
        have hw₁ := work_preserved_between hFibre hX₁ h (workPos v h)
          (Nat.zero_le v) (Nat.le_of_lt hvT) (fun w _ hwv => hNever w hwv)
          (Transpose.init M) cfg₁ hc₀₁ hcfg₁
        have hw₂ := work_preserved_between hFibre hX₂ h (workPos v h)
          (Nat.zero_le v) (Nat.le_of_lt hvT) (fun w _ hwv => hNever w hwv)
          (Transpose.init M) cfg₂ hc₀₂ hcfg₂
        rw [hw₁, hw₂]
      · have huv : u + 1 ≤ v := hLast.1
        obtain ⟨cPost₁, hcPost₁, _, _⟩ := hFibre.2.2.2.1 X₁ hX₁ (u + 1) (by omega)
        obtain ⟨cPost₂, hcPost₂, _, _⟩ := hFibre.2.2.2.1 X₂ hX₂ (u + 1) (by omega)
        have hw₁ := work_preserved_between hFibre hX₁ h (workPos v h)
          huv (Nat.le_of_lt hvT) (fun w hw₁ hw₂ => hLast.2.2 w hw₁ hw₂)
          cPost₁ cfg₁ hcPost₁ hcfg₁
        have hw₂ := work_preserved_between hFibre hX₂ h (workPos v h)
          huv (Nat.le_of_lt hvT) (fun w hw₁ hw₂ => hLast.2.2 w hw₁ hw₂)
          cPost₂ cfg₂ hcPost₂ hcfg₂
        rw [hw₁, hw₂, ← hLast.2.1]
        by_cases huΓ : u ∈ Γ
        · exact (hFibre.2.2.2.2.2 X₁ hX₁ X₂ hX₂ u huΓ cPost₁ cPost₂ hcPost₁ hcPost₂).2 h
        · have hdep : TMDepStep workPos T u v := ⟨hvT, Or.inr ⟨h, hLast⟩⟩
          have hSub := trueConeSteps_subset_of_dep workPos T Γ hdep huΓ
          obtain ⟨cU₁, hcU₁, _, hwposU₁⟩ := hFibre.2.2.2.1 X₁ hX₁ u (by omega)
          obtain ⟨cU₂, hcU₂, _, hwposU₂⟩ := hFibre.2.2.2.1 X₂ hX₂ u (by omega)
          have hδU := ih u hLast.1 (Nat.lt_trans hLast.1 hvT)
            (fun w hw => hAgree w (hSub hw)) cU₁ cU₂ hcU₁ hcU₂
          have hStep₁ : Transpose.step M (encodeCanonicalState X₁) cU₁ = some cPost₁ := by
            rw [← tmCfgAt_succ hcU₁]; exact hcPost₁
          have hStep₂ : Transpose.step M (encodeCanonicalState X₂) cU₂ = some cPost₂ := by
            rw [← tmCfgAt_succ hcU₂]; exact hcPost₂
          unfold Transpose.step at hStep₁ hStep₂
          rw [hδU] at hStep₁
          cases hδVal : M.δ cU₂.state (Transpose.readInput (encodeCanonicalState X₂) cU₂.inPos)
              (fun i => cU₂.work i (cU₂.workPos i)) <;> rw [hδVal] at hStep₁ hStep₂
          · cases hStep₁
          · rename_i val
            rcases val with ⟨s, dir, acts, o⟩
            simp only [Option.some.injEq] at hStep₁ hStep₂
            subst hStep₁; subst hStep₂
            have hwpU₁ : cU₁.workPos h = workPos u h := congrFun hwposU₁ h
            have hwpU₂ : cU₂.workPos h = workPos u h := congrFun hwposU₂ h
            simp [hwpU₁, hwpU₂]
    rw [hStateAgree, hInAgree, hWorkAgree]

private theorem emittedBit_eq_entry {M : Transpose.TM} {d T : ℕ} [NeZero d]
    {inPos : ℕ → Int} {workPos : ℕ → Fin M.k → Int}
    {emitStep : Fin (Transpose.inputLength d) → ℕ} {Γ : Finset ℕ}
    {C : Set (State d (CanonicalWordAlphabet d))}
    (hFibre : IsFrozenTraceCutFibre M d T inPos workPos emitStep Γ C)
    {X : State d (CanonicalWordAlphabet d)} (hX : X ∈ C)
    (r c : ZMod d) (ℓ : Fin (Transpose.entryBits d))
    (idx : Fin (Transpose.inputLength d))
    (hIdxVal : idx.val = r.val * (d * Transpose.entryBits d) + c.val * Transpose.entryBits d + ℓ.val)
    (cfgPre : Transpose.Config M)
    (hcfgPre : tmCfgAt M (encodeCanonicalState X) (emitStep idx) = some cfgPre) :
    match M.δ cfgPre.state (Transpose.readInput (encodeCanonicalState X) cfgPre.inPos)
        (fun i => cfgPre.work i (cfgPre.workPos i)) with
    | some (_, _, _, some bit) => bit = X c r ℓ
    | _ => False := by
  obtain ⟨cEnd, hcEnd, _, houtEnd⟩ := hFibre.2.2.1 X hX
  obtain ⟨cfgPre', cfgPost, hcfgPre', hcfgPost, hlenPre, hlenPost⟩ := hFibre.2.2.2.2.1 X hX idx
  rw [hcfgPre] at hcfgPre'; injection hcfgPre' with hEqPre; subst hEqPre
  have hEmitLtT : emitStep idx < T := hFibre.2.1 idx
  have hStep : Transpose.step M (encodeCanonicalState X) cfgPre = some cfgPost := by
    rw [← tmCfgAt_succ hcfgPre]; exact hcfgPost
  have hStepNRem :
      Transpose.stepN M (encodeCanonicalState X) (T - (emitStep idx + 1)) cfgPost = some cEnd := by
    have hAdd : (emitStep idx + 1) + (T - (emitStep idx + 1)) = T := by omega
    have hSplit := stepN_add M (encodeCanonicalState X)
      (emitStep idx + 1) (T - (emitStep idx + 1)) (Transpose.init M)
    rw [hAdd] at hSplit
    change tmCfgAt M (encodeCanonicalState X) T = _ at hSplit
    rw [hcEnd, show Transpose.stepN M (encodeCanonicalState X) (emitStep idx + 1)
      (Transpose.init M) = some cfgPost from hcfgPost] at hSplit
    exact hSplit.symm
  have hPrefix : cfgPost.outRev.reverse <+: cEnd.outRev.reverse :=
    outRev_reverse_prefix_of_stepN M (encodeCanonicalState X) _ cfgPost cEnd hStepNRem
  unfold Transpose.step at hStep
  cases hδ : M.δ cfgPre.state (Transpose.readInput (encodeCanonicalState X) cfgPre.inPos)
      (fun i => cfgPre.work i (cfgPre.workPos i)) <;> rw [hδ] at hStep
  · cases hStep
  · rename_i val
    rcases val with ⟨s, dir, acts, o⟩
    simp only [Option.some.injEq] at hStep
    cases o with
    | none =>
      subst hStep
      simp only at hlenPost
      omega
    | some bit =>
      have hOutPost : cfgPost.outRev = bit :: cfgPre.outRev := by rw [← hStep]
      have hPostGet : (cfgPost.outRev.reverse)[idx.val]? = some bit := by
        rw [hOutPost, List.reverse_cons]
        have hRevLen : cfgPre.outRev.reverse.length = idx.val := by
          rw [List.length_reverse]
          exact hlenPre
        rw [List.getElem?_append_right (by omega), hRevLen, Nat.sub_self]
        rfl
      obtain ⟨tail, hTail⟩ := hPrefix
      have hEndGet : (cEnd.outRev.reverse)[idx.val]? = some bit := by
        rw [← hTail, List.getElem?_append_left (by rw [List.length_reverse]; omega)]
        exact hPostGet
      rw [houtEnd] at hEndGet
      let b := Transpose.entryBits d
      have hEncGet :=
        (encode_length_and_getElem? d b (Transpose.transpose (stateToTMMatrix X))).2 idx.val
          (by simpa [Transpose.inputLength, b] using idx.isLt)
      rw [hEncGet, Option.some.injEq] at hEndGet
      have hcbLt : c.val * b + ℓ.val < d * b := by
        have hc : c.val + 1 ≤ d := c.val_lt
        have hℓ : ℓ.val < b := ℓ.isLt
        calc c.val * b + ℓ.val < c.val * b + b := by omega
          _ = (c.val + 1) * b := by ring
          _ ≤ d * b := Nat.mul_le_mul_right b hc
      have hIdxEq : idx.val = r.val * (d * b) + (c.val * b + ℓ.val) := by
        change idx.val = r.val * (d * Transpose.entryBits d) + (c.val * Transpose.entryBits d + ℓ.val)
        rw [hIdxVal]
        ring
      obtain ⟨hDiv₁, hMod₁⟩ := mul_add_div_mod hcbLt
      rw [← hIdxEq] at hDiv₁ hMod₁
      obtain ⟨hDiv₂, hMod₂⟩ := mul_add_div_mod ℓ.isLt
      rw [hDiv₁, hMod₁, hDiv₂, hMod₂] at hEndGet
      simpa only [Transpose.transpose, stateToTMMatrix, ℓ.isLt, dite_true,
        ZMod.natCast_zmod_val, Fin.eta] using hEndGet.symm

theorem tmTraceCutConeDetermination : TMTraceCutConeDeterminationSpec := by
  classical
  intro M d T D _ inPos workPos emitStep Γ C hk hD hFibre hPathLen
  have hConeBound : ∀ v < T,
      (trueConeSteps workPos T Γ v).card ≤ (M.k + 1) ^ D ∧
        ∀ u < T, InCutCausalCone workPos T Γ v u → u ∈ trueConeSteps workPos T Γ v := by
    intro v _
    refine ⟨?_, ?_⟩
    · have hSub : trueConeSteps workPos T Γ v ⊆ coneAtDepth workPos T Γ D v := by
        intro u hu
        unfold trueConeSteps at hu
        simp only [Finset.mem_filter] at hu
        rcases hu.2 with ⟨π, hhead, hlast, hpath⟩
        exact mem_coneAtDepth_of_path workPos T Γ D π v u hpath hhead hlast (hPathLen π hpath)
      have hSucc := coneAtDepth_card_succ_le workPos T Γ hk D hD v
      have hCardLe := Finset.card_le_card hSub
      omega
    · intro u huT hIn
      unfold trueConeSteps
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr huT, hIn⟩
  refine ⟨fun v hv => ⟨trueConeSteps workPos T Γ v, hConeBound v hv⟩, ?_⟩
  intro r c ℓ
  let b := Transpose.entryBits d
  let idxVal := r.val * (d * b) + c.val * b + ℓ.val
  have hidxLt : idxVal < Transpose.inputLength d := by
    have hr : r.val + 1 ≤ d := r.val_lt
    have hc : c.val + 1 ≤ d := c.val_lt
    have hℓ : ℓ.val < b := ℓ.isLt
    have hcb : c.val * b + ℓ.val < d * b := by
      calc c.val * b + ℓ.val < c.val * b + b := by omega
        _ = (c.val + 1) * b := by ring
        _ ≤ d * b := Nat.mul_le_mul_right b hc
    unfold Transpose.inputLength
    calc r.val * (d * b) + c.val * b + ℓ.val
        < r.val * (d * b) + d * b := by omega
      _ = (r.val + 1) * (d * b) := by ring
      _ ≤ d * (d * b) := Nat.mul_le_mul_right (d * b) hr
      _ = d * d * b := (Nat.mul_assoc d d b).symm
  let idx : Fin (Transpose.inputLength d) := ⟨idxVal, hidxLt⟩
  let v := emitStep idx
  have hvT : v < T := hFibre.2.1 idx
  let S : Finset ℕ := trueConeSteps workPos T Γ v
  let cellSet (w : ℕ) : Finset (ZMod d × ZMod d) :=
    match inputCellOfPos d (inPos w) with
    | none => ∅
    | some ij => {ij}
  let Q_bit : Finset (ZMod d × ZMod d) := S.biUnion cellSet
  have hQcard : Q_bit.card ≤ (M.k + 1) ^ D := by
    calc Q_bit.card ≤ ∑ w ∈ S, (cellSet w).card := Finset.card_biUnion_le
      _ ≤ ∑ _w ∈ S, 1 := by
          refine Finset.sum_le_sum fun w _ => ?_
          dsimp [cellSet]
          cases inputCellOfPos d (inPos w) <;> simp
      _ = S.card := by simp
      _ ≤ (M.k + 1) ^ D := (hConeBound v hvT).1
  refine ⟨Q_bit, hQcard, ?_⟩
  intro X₁ hX₁ X₂ hX₂ hAgreeQ
  obtain ⟨cfgPre₁, _, hPre₁, _, _, _⟩ := hFibre.2.2.2.2.1 X₁ hX₁ idx
  obtain ⟨cfgPre₂, _, hPre₂, _, _, _⟩ := hFibre.2.2.2.2.1 X₂ hX₂ idx
  have hδEq := delta_agree_on_trueConeSteps hFibre hX₁ hX₂ v hvT
    (fun w hw ij hij => by
      refine hAgreeQ ij (Finset.mem_biUnion.mpr ⟨w, hw, ?_⟩)
      simp [cellSet, hij])
    cfgPre₁ cfgPre₂ hPre₁ hPre₂
  have hBit₁ := emittedBit_eq_entry hFibre hX₁ r c ℓ idx rfl cfgPre₁ hPre₁
  have hBit₂ := emittedBit_eq_entry hFibre hX₂ r c ℓ idx rfl cfgPre₂ hPre₂
  rw [hδEq] at hBit₁
  cases hδVal : M.δ cfgPre₂.state (Transpose.readInput (encodeCanonicalState X₂) cfgPre₂.inPos)
      (fun i => cfgPre₂.work i (cfgPre₂.workPos i)) <;> rw [hδVal] at hBit₁ hBit₂
  · exact False.elim hBit₁
  · rename_i val
    rcases val with ⟨s, dir, acts, o⟩
    cases o with
    | none => exact False.elim hBit₁
    | some bit => exact hBit₁.symm.trans hBit₂

/-! ### 3. Periodic Cut-Cone Sweep Induces `IsBoundedAritySetCode` & Rate Deficit -/

theorem periodicSweepInducesBoundedAritySharedCode :
    PeriodicSweepInducesBoundedAritySharedCodeSpec := by
  intro d M_cls Delta _ Sigma S E C hValid
  exact ⟨⟨S.stencil_card_le, S.eval_local⟩, hValid⟩

theorem periodicSweepNonlinearFibreDeficit :
    PeriodicSweepNonlinearFibreDeficitSpec := by
  intro d M_cls Delta _ Sigma _ δ η S E C hSigma hM hDelta hδ hη hsum hE hM_le hCne hValid
  have hCode := periodicSweepInducesBoundedAritySharedCode d M_cls Delta Sigma S E C hValid
  exact (growingClassesPositiveDeficit d M_cls Delta Sigma δ η
    S.p E S.evalCone S.stencil C hSigma hM hDelta hδ hη hsum hE hM_le hCne hCode).1

end BoundedArityDecoders
