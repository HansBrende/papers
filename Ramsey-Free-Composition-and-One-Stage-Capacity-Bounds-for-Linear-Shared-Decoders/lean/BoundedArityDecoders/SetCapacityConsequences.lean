import BoundedArityDecoders.BoundedAritySetCapacityProofs
import BoundedArityDecoders.NativeSweepInterfaceProofs
import SharedDecoders.CapacitySetRate
import Mathlib.GroupTheory.Perm.Basic

/-!
# Random-Order Set-Capacity Bound & Asymptotic Corollaries

This module establishes the `1 / (Δ + 1)` random-order capacity bound for arbitrary
bounded-arity shared-decoder codes (formalizing Proposition 4.14(a)–(b) of *Curved Motion, Depth
Reduction, and Storage Codes for Matrix Transposition on Tapes* in the column-class setting after
Bar-Yossef–Birk–Jayram–Kol) together with unrestricted-arity boundary controls and sublinear-class
corollaries:

1. `canonicalWordAlphabet_card_and_ge_two`: `2 ≤ |CanonicalWordAlphabet d|` for all `d : ℕ`, and
   `|CanonicalWordAlphabet d| = 2 ^ ⌈log₂ d⌉` (`Nat.clog 2 d`) for all `d ≥ 2`.
2. `orderedRecoverableCells`, `orderedRecoverable_injective_and_card_le`,
   `exists_orderedRecoverableCells_bound`, and `randomOrder_BoundedAritySetCapacity`:
   uniform permutation averaging on `(ZMod d × ZMod d)` yields an acyclic ordering in which at
   least `|cleanEntries| / (Δ + 1)` entries follow their entire shifted footprint, proving
   `log_{|Σ|} |C| ≤ d^2 - (d^2 - |E| - d M Δ) / (Δ + 1)` for all `Δ : ℕ` and arbitrary `C`.
3. `arityGainFactor`, `pMin_two_sided_theta_inv_arity`,
   `theorem1_BoundedAritySetCapacity_unconditional`, and `growingClasses_strict_inv_exp_deficit`:
   companion one-hop Bernoulli bounds (`Δ^Δ / (Δ + 1)^(Δ + 1)`).
4. `unrestrictedArity_RateLowerBoundAndTendstoOne` and
   `unrestrictedArity_ExactLogarithmicAsymptoticAllDimensions`: unrestricted-arity (`Δ = d^2`)
   orbit-code lower bounds `≥ |Σ|^{d^2} / (2 d)` and convergence to rate `1`.
5. `asymptotic_SublinearClassesBrokenFractionRefutesRateOne`: positive rate deficit for fixed `Δ`
   and sublinear class count `M_d = o(d / Δ)`.
-/

namespace BoundedArityDecoders

open SharedDecoders
open scoped BigOperators

/-! ### 1. Canonical Word Alphabet Cardinality -/

/-- For every dimension `d : ℕ`, `CanonicalWordAlphabet d` has cardinality at least `2`
(since `1 ≤ Transpose.entryBits d`), and for every `d ≥ 2` its cardinality equals `2 ^ Nat.clog 2 d`
(`2 ^ ⌈log₂ d⌉`). -/
theorem canonicalWordAlphabet_card_and_ge_two :
    (∀ d : ℕ, 2 ≤ Fintype.card (CanonicalWordAlphabet d)) ∧
      (∀ d : ℕ, 2 ≤ d → Fintype.card (CanonicalWordAlphabet d) = 2 ^ Nat.clog 2 d) := by
  refine ⟨fun d => ?_, fun d hd => ?_⟩
  · rw [canonicalWordAlphabet_card]
    have hb : 1 ≤ Transpose.entryBits d := by
      unfold Transpose.entryBits
      omega
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ Transpose.entryBits d := Nat.pow_le_pow_right (by decide) hb
  · rw [canonicalWordAlphabet_card, entryBits_eq_clog d hd]

/-! ### 2. The `1 / (Δ + 1)` Random-Order Capacity Bound (after Paper 4 Prop. 4.14 & BBJK) -/

/-- Clean matrix entries `cr = (c, r)` whose shifted footprint `shiftedFootprint p Q c r` strictly
precedes `cr` under the rank function `rk : ZMod d × ZMod d → ℕ`. -/
def orderedRecoverableCells {d M : ℕ} [NeZero d]
    (p : ZMod d → Fin M)
    (Q : Fin M → ZMod d → Finset (ZMod d × ZMod d))
    (E : Finset (ZMod d × ZMod d))
    (rk : ZMod d × ZMod d → ℕ) : Finset (ZMod d × ZMod d) :=
  (cleanEntries p Q E).filter fun cr =>
    ∀ y ∈ shiftedFootprint p Q cr.1 cr.2, rk y < rk cr

/-- **Acyclic Ordered Determination.**
For any rank function `rk : ZMod d × ZMod d → ℕ` and any `(Delta, p, E)`-bounded-arity code `C`,
every codeword `X ∈ C` is uniquely determined by its entries outside
`orderedRecoverableCells p Q E rk`, giving `|C| ≤ |Σ|^{d^2 - |orderedRecoverableCells p Q E rk|}`. -/
theorem orderedRecoverable_injective_and_card_le
    {d M Delta : ℕ} [NeZero d]
    {Sigma : Type*} [Fintype Sigma]
    (p : ZMod d → Fin M)
    (E : Finset (ZMod d × ZMod d))
    (f : Fin M → State d Sigma → (ZMod d → Sigma))
    (Q : Fin M → ZMod d → Finset (ZMod d × ZMod d))
    (C : Set (State d Sigma))
    (rk : ZMod d × ZMod d → ℕ)
    (hCode : IsBoundedAritySetCode Delta p E f Q C) :
    (∀ X₁ ∈ C, ∀ X₂ ∈ C,
      (∀ cr : ZMod d × ZMod d, cr ∉ orderedRecoverableCells p Q E rk → X₁ cr.1 cr.2 = X₂ cr.1 cr.2) →
      X₁ = X₂) ∧
    Nat.card C ≤ (Fintype.card Sigma) ^ (d ^ 2 - (orderedRecoverableCells p Q E rk).card) := by
  rcases hCode with ⟨⟨_, hQsupp⟩, hValid⟩
  have hDet : ∀ X₁ ∈ C, ∀ X₂ ∈ C,
      (∀ cr : ZMod d × ZMod d, cr ∉ orderedRecoverableCells p Q E rk → X₁ cr.1 cr.2 = X₂ cr.1 cr.2) →
      X₁ = X₂ := by
    intro X₁ hX₁ X₂ hX₂ hAgree
    have hStrong : ∀ (n : ℕ) (cr : ZMod d × ZMod d), rk cr = n → X₁ cr.1 cr.2 = X₂ cr.1 cr.2 := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
        intro cr hRk
        by_cases hMem : cr ∈ orderedRecoverableCells p Q E rk
        · simp only [orderedRecoverableCells, cleanEntries, Finset.mem_filter, Finset.mem_univ,
            true_and] at hMem
          rcases hMem with ⟨⟨hnotE, _⟩, hOrd⟩
          rw [← hValid X₁ hX₁ cr.2 cr.1 hnotE, ← hValid X₂ hX₂ cr.2 cr.1 hnotE]
          refine hQsupp (p cr.1) cr.2 (rot cr.1 X₁) (rot cr.1 X₂) ?_
          intro q hq
          have hyMem : (q.1, cr.1 + q.2) ∈ shiftedFootprint p Q cr.1 cr.2 :=
            Finset.mem_image.mpr ⟨q, hq, rfl⟩
          have hyLt : rk (q.1, cr.1 + q.2) < n := hRk ▸ hOrd (q.1, cr.1 + q.2) hyMem
          have hEqCell := ih (rk (q.1, cr.1 + q.2)) hyLt (q.1, cr.1 + q.2) rfl
          simpa only [rot_apply, add_comm] using hEqCell
        · exact hAgree cr hMem
    funext c r
    exact hStrong (rk (c, r)) (c, r) rfl
  refine ⟨hDet, ?_⟩
  let Rc : Finset (ZMod d × ZMod d) := Finset.univ \ orderedRecoverableCells p Q E rk
  let res : C → (Rc → Sigma) := fun X cr => X.val cr.val.1 cr.val.2
  have hInj : Function.Injective res := by
    intro X₁ X₂ hEq
    apply Subtype.ext
    refine hDet X₁.val X₁.property X₂.val X₂.property fun cr hcr => ?_
    exact congrFun hEq ⟨cr, Finset.mem_sdiff.mpr ⟨Finset.mem_univ cr, hcr⟩⟩
  have hRcCard : Rc.card = d ^ 2 - (orderedRecoverableCells p Q E rk).card := by
    have huniv : (Finset.univ : Finset (ZMod d × ZMod d)).card = d ^ 2 := by
      simp [ZMod.card, sq]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), huniv]
  calc Nat.card C ≤ Nat.card (Rc → Sigma) := Nat.card_le_card_of_injective res hInj
    _ = Fintype.card (Rc → Sigma) := Nat.card_eq_fintype_card
    _ = (Fintype.card Sigma) ^ Rc.card := by simp
    _ = (Fintype.card Sigma) ^ (d ^ 2 - (orderedRecoverableCells p Q E rk).card) := by rw [hRcCard]

/-- **Random-Order Permutation Witness (`|cleanEntries| ≤ (Δ + 1) |orderedRecoverableCells|`).**
Averaging over all permutations `σ : Equiv.Perm (ZMod d × ZMod d)`, each clean entry `cr` has
`|F_{c, r} ∪ {cr}| ≤ Δ + 1` and lies last in `F_{c, r} ∪ {cr}` on at least a `1 / (Δ + 1)` fraction
of permutations, yielding an injective rank `rk_* : ZMod d × ZMod d → ℕ` with
`(cleanEntries p Q E).card ≤ (Delta + 1) * (orderedRecoverableCells p Q E rk_*).card`. -/
theorem exists_orderedRecoverableCells_bound
    (d M Delta : ℕ) [NeZero d]
    (p : ZMod d → Fin M)
    (Q : Fin M → ZMod d → Finset (ZMod d × ZMod d))
    (E : Finset (ZMod d × ZMod d))
    (hQ : ∀ m r, (Q m r).card ≤ Delta) :
    ∃ rk : ZMod d × ZMod d → ℕ,
      Function.Injective rk ∧
      (cleanEntries p Q E).card ≤ (Delta + 1) * (orderedRecoverableCells p Q E rk).card := by
  classical
  have hCardEq : Fintype.card (ZMod d × ZMod d) = d ^ 2 := by
    simp [ZMod.card, sq]
  let e₀ : (ZMod d × ZMod d) ≃ Fin (d ^ 2) := Fintype.equivFinOfCardEq hCardEq
  let rkOf (σ : Equiv.Perm (ZMod d × ZMod d)) (x : ZMod d × ZMod d) : ℕ := (e₀ (σ x)).val
  have hRkInj : ∀ σ, Function.Injective (rkOf σ) := by
    intro σ x y hEq
    exact σ.injective (e₀.injective (Fin.ext hEq))
  let goodPerms (cr : ZMod d × ZMod d) : Finset (Equiv.Perm (ZMod d × ZMod d)) :=
    Finset.univ.filter fun σ => cr ∈ orderedRecoverableCells p Q E (rkOf σ)
  let N := Fintype.card (Equiv.Perm (ZMod d × ZMod d))
  have hNpos : 0 < N := Fintype.card_pos_iff.mpr ⟨1⟩
  have hCleanFoot := ((selfReferentialAndCleanCount d M Delta p Q E).2 hQ).2
  have hPerCell : ∀ cr ∈ cleanEntries p Q E, N ≤ (Delta + 1) * (goodPerms cr).card := by
    intro cr hcr
    have hcr' := hcr
    simp only [cleanEntries, Finset.mem_filter, Finset.mem_univ, true_and] at hcr'
    rcases hcr' with ⟨hnotE, hnotF⟩
    set F := shiftedFootprint p Q cr.1 cr.2
    let S : Finset (ZMod d × ZMod d) := insert cr F
    have hScard : S.card ≤ Delta + 1 := by
      rw [Finset.card_insert_of_notMem hnotF]
      exact Nat.add_le_add_right (hCleanFoot cr hcr) 1
    let maxAt (s : ZMod d × ZMod d) : Finset (Equiv.Perm (ZMod d × ZMod d)) :=
      Finset.univ.filter fun τ => ∀ y ∈ S, rkOf τ y ≤ rkOf τ s
    have hCover : (Finset.univ : Finset (Equiv.Perm (ZMod d × ZMod d))) ⊆ S.biUnion maxAt := by
      intro τ _
      obtain ⟨s, hsS, hsMax⟩ :=
        Finset.exists_max_image S (rkOf τ) ⟨cr, Finset.mem_insert_self cr F⟩
      exact Finset.mem_biUnion.mpr ⟨s, hsS, Finset.mem_filter.mpr ⟨Finset.mem_univ τ, hsMax⟩⟩
    have hMaxLeGood : ∀ s ∈ S, (maxAt s).card ≤ (goodPerms cr).card := by
      intro s hsS
      let φ : Equiv.Perm (ZMod d × ZMod d) → Equiv.Perm (ZMod d × ZMod d) :=
        fun τ => τ * Equiv.swap cr s
      have hφInj : Function.Injective φ := fun τ₁ τ₂ hEq => mul_right_cancel hEq
      have hImgSub : (maxAt s).image φ ⊆ goodPerms cr := by
        intro σ hσ
        rcases Finset.mem_image.mp hσ with ⟨τ, hτ, rfl⟩
        have hτMax : ∀ y ∈ S, rkOf τ y ≤ rkOf τ s := (Finset.mem_filter.mp hτ).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        refine Finset.mem_filter.mpr ⟨hcr, fun y hyF => ?_⟩
        have hyNeCr : y ≠ cr := fun hEq => hnotF (hEq ▸ hyF)
        let z := Equiv.swap cr s y
        have hzMemAndNe : z ∈ S ∧ z ≠ s := by
          by_cases hys : y = s
          · subst hys
            refine ⟨by simp [z, S], ?_⟩
            simpa [z] using hyNeCr.symm
          · have hzEq : z = y := Equiv.swap_apply_of_ne_of_ne hyNeCr hys
            exact ⟨hzEq ▸ Finset.mem_insert_of_mem hyF, hzEq ▸ hys⟩
        have hLe : rkOf τ z ≤ rkOf τ s := hτMax z hzMemAndNe.1
        have hNe : rkOf τ z ≠ rkOf τ s := fun hEq => hzMemAndNe.2 (hRkInj τ hEq)
        have hLt : rkOf τ z < rkOf τ s := lt_of_le_of_ne hLe hNe
        have hValY : rkOf (φ τ) y = rkOf τ z := rfl
        have hValCr : rkOf (φ τ) cr = rkOf τ s := by
          change (e₀ (τ (Equiv.swap cr s cr))).val = (e₀ (τ s)).val
          rw [Equiv.swap_apply_left]
        rw [hValY, hValCr]
        exact hLt
      calc (maxAt s).card = ((maxAt s).image φ).card :=
            (Finset.card_image_of_injective _ hφInj).symm
        _ ≤ (goodPerms cr).card := Finset.card_le_card hImgSub
    calc N = (Finset.univ : Finset (Equiv.Perm (ZMod d × ZMod d))).card := rfl
      _ ≤ (S.biUnion maxAt).card := Finset.card_le_card hCover
      _ ≤ ∑ s ∈ S, (maxAt s).card := Finset.card_biUnion_le
      _ ≤ ∑ _s ∈ S, (goodPerms cr).card := Finset.sum_le_sum hMaxLeGood
      _ = S.card * (goodPerms cr).card := by simp
      _ ≤ (Delta + 1) * (goodPerms cr).card := Nat.mul_le_mul_right _ hScard
  have hDoubleCount :
      ∑ cr ∈ cleanEntries p Q E, (goodPerms cr).card =
        ∑ σ : Equiv.Perm (ZMod d × ZMod d), (orderedRecoverableCells p Q E (rkOf σ)).card := by
    calc ∑ cr ∈ cleanEntries p Q E, (goodPerms cr).card
        = ∑ cr ∈ cleanEntries p Q E, ∑ σ : Equiv.Perm (ZMod d × ZMod d),
            (if cr ∈ orderedRecoverableCells p Q E (rkOf σ) then 1 else 0) := by
          refine Finset.sum_congr rfl fun cr _ => ?_
          rw [Finset.card_filter]
      _ = ∑ σ : Equiv.Perm (ZMod d × ZMod d), ∑ cr ∈ cleanEntries p Q E,
            (if cr ∈ orderedRecoverableCells p Q E (rkOf σ) then 1 else 0) := Finset.sum_comm
      _ = ∑ σ : Equiv.Perm (ZMod d × ZMod d), (orderedRecoverableCells p Q E (rkOf σ)).card := by
          refine Finset.sum_congr rfl fun σ _ => ?_
          rw [← Finset.card_filter]
          congr 1
          ext cr
          simp only [orderedRecoverableCells, Finset.mem_filter]
          tauto
  obtain ⟨σ₀, _, hσ₀Max⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Equiv.Perm (ZMod d × ZMod d)))
    (fun σ => (orderedRecoverableCells p Q E (rkOf σ)).card)
    ⟨1, Finset.mem_univ 1⟩
  have hMulBound :
      N * (cleanEntries p Q E).card ≤
        N * ((Delta + 1) * (orderedRecoverableCells p Q E (rkOf σ₀)).card) := by
    calc N * (cleanEntries p Q E).card
        = ∑ _cr ∈ cleanEntries p Q E, N := by simp [Nat.mul_comm]
      _ ≤ ∑ cr ∈ cleanEntries p Q E, (Delta + 1) * (goodPerms cr).card :=
          Finset.sum_le_sum hPerCell
      _ = (Delta + 1) * ∑ cr ∈ cleanEntries p Q E, (goodPerms cr).card := by
          rw [← Finset.mul_sum]
      _ = (Delta + 1) * ∑ σ : Equiv.Perm (ZMod d × ZMod d),
            (orderedRecoverableCells p Q E (rkOf σ)).card := by rw [hDoubleCount]
      _ ≤ (Delta + 1) * ∑ _σ : Equiv.Perm (ZMod d × ZMod d),
            (orderedRecoverableCells p Q E (rkOf σ₀)).card := by
          refine Nat.mul_le_mul_left _ (Finset.sum_le_sum fun σ _ => hσ₀Max σ (Finset.mem_univ σ))
      _ = (Delta + 1) * (N * (orderedRecoverableCells p Q E (rkOf σ₀)).card) := by simp [N]
      _ = N * ((Delta + 1) * (orderedRecoverableCells p Q E (rkOf σ₀)).card) := by ring
  exact ⟨rkOf σ₀, hRkInj σ₀, Nat.le_of_mul_le_mul_left hMulBound hNpos⟩

/-- **The `1 / (Δ + 1)` Random-Order Set-Capacity Bound (after Proposition 4.14(a)–(b) of
*Curved Motion, Depth Reduction, and Storage Codes for Matrix Transposition on Tapes* and
Bar-Yossef–Birk–Jayram–Kol).**
For every finite alphabet `Sigma` (`2 ≤ |Sigma|`), dimension `d ≥ 1` (`[NeZero d]`), class count
`M : ℕ`, cell cone arity `Delta : ℕ`, and arbitrary (empty or nonempty) subset `C ⊆ Σ^{d × d}`
validated outside `E` by `(p, f, Q)`,
`log_{|Sigma|} |C| ≤ d^2 - (d^2 - |E| - d M Delta) / (Delta + 1)`. -/
theorem randomOrder_BoundedAritySetCapacity
    (d M Delta : ℕ) [NeZero d]
    (Sigma : Type*) [Fintype Sigma]
    (p : ZMod d → Fin M)
    (E : Finset (ZMod d × ZMod d))
    (f : Fin M → State d Sigma → (ZMod d → Sigma))
    (Q : Fin M → ZMod d → Finset (ZMod d × ZMod d))
    (C : Set (State d Sigma))
    (hSigma : 2 ≤ Fintype.card Sigma)
    (hCode : IsBoundedAritySetCode Delta p E f Q C) :
    Real.log (Nat.card C : ℝ) / Real.log (Fintype.card Sigma : ℝ) ≤
      ((d ^ 2 : ℕ) : ℝ) -
        (((d ^ 2 : ℕ) : ℝ) - (E.card : ℝ) - (d : ℝ) * (M : ℝ) * (Delta : ℝ)) /
          ((Delta : ℝ) + 1) := by
  have hDenPos : (0 : ℝ) < (Delta : ℝ) + 1 := by positivity
  by_cases hCne : C.Nonempty
  · obtain ⟨rk, _, hOrdBound⟩ := exists_orderedRecoverableCells_bound d M Delta p Q E hCode.1.1
    have hCardLe := (orderedRecoverable_injective_and_card_le p E f Q C rk hCode).2
    have hCleanLower := ((selfReferentialAndCleanCount d M Delta p Q E).2 hCode.1.1).1
    let A := orderedRecoverableCells p Q E rk
    have hAsub : A ⊆ Finset.univ := Finset.subset_univ A
    have hAleD2 : A.card ≤ d ^ 2 := by
      calc A.card ≤ (Finset.univ : Finset (ZMod d × ZMod d)).card := Finset.card_le_card hAsub
        _ = d ^ 2 := by simp [ZMod.card, sq]
    have hCardPos : 1 ≤ Nat.card C := by
      have : Nonempty C := hCne.to_subtype
      have : Finite C := Set.toFinite C
      exact Nat.succ_le_of_lt Nat.card_pos
    have hSigmaGt1 : (1 : ℝ) < (Fintype.card Sigma : ℝ) := by
      exact_mod_cast lt_of_lt_of_le (by decide : 1 < 2) hSigma
    have hLogPos : 0 < Real.log (Fintype.card Sigma : ℝ) := Real.log_pos hSigmaGt1
    have hRealCard : (Nat.card C : ℝ) ≤ ((Fintype.card Sigma : ℝ)) ^ (d ^ 2 - A.card) := by
      exact_mod_cast hCardLe
    have hLogLe := Real.log_le_log (by exact_mod_cast hCardPos) hRealCard
    rw [Real.log_pow] at hLogLe
    have hDivLe : Real.log (Nat.card C : ℝ) / Real.log (Fintype.card Sigma : ℝ) ≤
        ((d ^ 2 - A.card : ℕ) : ℝ) := (div_le_iff₀ hLogPos).mpr hLogLe
    rw [Nat.cast_sub hAleD2] at hDivLe
    have hCleanReal :
        ((d ^ 2 : ℕ) : ℝ) - (E.card : ℝ) - (d : ℝ) * (M : ℝ) * (Delta : ℝ) ≤
          ((cleanEntries p Q E).card : ℝ) := by
      have hR : ((d ^ 2 : ℕ) : ℝ) ≤
          (((cleanEntries p Q E).card + E.card + d * M * Delta : ℕ) : ℝ) := by
        exact_mod_cast hCleanLower
      push_cast at hR ⊢
      linarith
    have hOrdReal : ((cleanEntries p Q E).card : ℝ) ≤ ((Delta : ℝ) + 1) * (A.card : ℝ) := by
      have hR : ((cleanEntries p Q E).card : ℝ) ≤ (((Delta + 1) * A.card : ℕ) : ℝ) := by
        exact_mod_cast hOrdBound
      push_cast at hR
      exact hR
    have hFracLe :
        (((d ^ 2 : ℕ) : ℝ) - (E.card : ℝ) - (d : ℝ) * (M : ℝ) * (Delta : ℝ)) /
            ((Delta : ℝ) + 1) ≤ (A.card : ℝ) :=
      (div_le_iff₀ hDenPos).mpr (by linarith)
    linarith
  · have hEmpty : C = ∅ := Set.not_nonempty_iff_eq_empty.mp hCne
    subst hEmpty
    rw [Nat.card_of_isEmpty]
    simp only [CharP.cast_eq_zero, Real.log_zero, zero_div]
    have hd2Nonneg : (0 : ℝ) ≤ ((d ^ 2 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hENonneg : (0 : ℝ) ≤ (E.card : ℝ) := Nat.cast_nonneg _
    have hdMDeltaNonneg : (0 : ℝ) ≤ (d : ℝ) * (M : ℝ) * (Delta : ℝ) := by positivity
    have hDeltaNonneg : (0 : ℝ) ≤ (Delta : ℝ) := Nat.cast_nonneg _
    have hNumLe :
        ((d ^ 2 : ℕ) : ℝ) - (E.card : ℝ) - (d : ℝ) * (M : ℝ) * (Delta : ℝ) ≤
          ((d ^ 2 : ℕ) : ℝ) * ((Delta : ℝ) + 1) := by
      nlinarith
    have hDivLe :
        (((d ^ 2 : ℕ) : ℝ) - (E.card : ℝ) - (d : ℝ) * (M : ℝ) * (Delta : ℝ)) /
            ((Delta : ℝ) + 1) ≤ ((d ^ 2 : ℕ) : ℝ) :=
      (div_le_iff₀ hDenPos).mpr hNumLe
    linarith

/-! ### 3. Companion One-Hop Bernoulli Bounds (`Δ^Δ / (Δ + 1)^(Δ + 1)`) -/

/-- Per-clean-cell one-hop Bernoulli recovery probability lower bound
`Δ^Δ / (Δ + 1)^(Δ + 1)`. -/
noncomputable def arityGainFactor (Delta : ℕ) : ℝ :=
  (Delta : ℝ) ^ Delta / ((Delta + 1 : ℝ) ^ (Delta + 1))

private theorem nat_pow_add_mul_pow_le_succ_pow (d : ℕ) :
    ∀ k : ℕ, d ^ (k + 1) + (k + 1) * d ^ k ≤ (d + 1) ^ (k + 1)
  | 0 => by simp
  | k + 1 => by
    have ih := nat_pow_add_mul_pow_le_succ_pow d k
    calc d ^ (k + 2) + (k + 2) * d ^ (k + 1)
        ≤ d ^ (k + 2) + (k + 2) * d ^ (k + 1) + (k + 1) * d ^ k := Nat.le_add_right _ _
      _ = (d ^ (k + 1) + (k + 1) * d ^ k) * (d + 1) := by
          simp only [pow_succ]
          ring
      _ ≤ (d + 1) ^ (k + 1) * (d + 1) := Nat.mul_le_mul_right (d + 1) ih
      _ = (d + 1) ^ (k + 2) := (pow_succ (d + 1) (k + 1)).symm

private theorem two_mul_self_pow_le_succ_pow {Delta : ℕ} (hDelta : 1 ≤ Delta) :
    2 * Delta ^ Delta ≤ (Delta + 1) ^ Delta := by
  cases Delta with
  | zero => omega
  | succ m =>
    have h := nat_pow_add_mul_pow_le_succ_pow (m + 1) m
    have hEq : (m + 1) ^ (m + 1) + (m + 1) * (m + 1) ^ m = 2 * (m + 1) ^ (m + 1) := by
      rw [pow_succ']
      ring
    rwa [hEq] at h

/-- For every cone arity `Delta ≥ 1`, `arityGainFactor Delta = Δ^Δ / (Δ + 1)^(Δ + 1)` satisfies
`1 / (e (Δ + 1)) < arityGainFactor Delta ≤ 1 / (2 (Δ + 1)) ≤ 1 / 4`. -/
theorem pMin_two_sided_theta_inv_arity (Delta : ℕ) (hDelta : 1 ≤ Delta) :
    1 / (Real.exp 1 * (Delta + 1 : ℝ)) < arityGainFactor Delta ∧
      arityGainFactor Delta ≤ 1 / (2 * (Delta + 1 : ℝ)) ∧
      arityGainFactor Delta ≤ 1 / 4 := by
  have hLo : 1 / (Real.exp 1 * (Delta + 1 : ℝ)) < arityGainFactor Delta :=
    arityFactor_gt_inv_exp Delta hDelta
  have hNat : 2 * Delta ^ Delta ≤ (Delta + 1) ^ Delta :=
    two_mul_self_pow_le_succ_pow hDelta
  have hReal : 2 * (Delta : ℝ) ^ Delta ≤ ((Delta : ℝ) + 1) ^ Delta := by
    exact_mod_cast hNat
  have hDenPos : (0 : ℝ) < (Delta : ℝ) + 1 := by positivity
  have hProdLe :
      (Delta : ℝ) ^ Delta * (2 * ((Delta : ℝ) + 1)) ≤ ((Delta : ℝ) + 1) ^ (Delta + 1) := by
    calc (Delta : ℝ) ^ Delta * (2 * ((Delta : ℝ) + 1))
        = (2 * (Delta : ℝ) ^ Delta) * ((Delta : ℝ) + 1) := by ring
      _ ≤ ((Delta : ℝ) + 1) ^ Delta * ((Delta : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right hReal hDenPos.le
      _ = ((Delta : ℝ) + 1) ^ (Delta + 1) := (pow_succ _ _).symm
  have hUp : arityGainFactor Delta ≤ 1 / (2 * (Delta + 1 : ℝ)) := by
    unfold arityGainFactor
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  have hDeltaReal : (1 : ℝ) ≤ (Delta : ℝ) := by exact_mod_cast hDelta
  have hQuarter : 1 / (2 * (Delta + 1 : ℝ)) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  exact ⟨hLo, hUp, hUp.trans hQuarter⟩

/-- Unconditional one-hop Bernoulli capacity bound for arbitrary `M : ℕ` and arbitrary (empty or
nonempty) code `C : Set (State d Sigma)`. -/
theorem theorem1_BoundedAritySetCapacity_unconditional
    (d M Delta : ℕ) [NeZero d]
    (Sigma : Type*) [Fintype Sigma]
    (p : ZMod d → Fin M)
    (E : Finset (ZMod d × ZMod d))
    (f : Fin M → State d Sigma → (ZMod d → Sigma))
    (Q : Fin M → ZMod d → Finset (ZMod d × ZMod d))
    (C : Set (State d Sigma))
    (hSigma : 2 ≤ Fintype.card Sigma)
    (hDelta : 1 ≤ Delta)
    (hCode : IsBoundedAritySetCode Delta p E f Q C) :
    Real.log (Nat.card C : ℝ) / Real.log (Fintype.card Sigma : ℝ) ≤
      ((d ^ 2 : ℕ) : ℝ) -
        (((d ^ 2 : ℕ) : ℝ) - (E.card : ℝ) - (d : ℝ) * (M : ℝ) * (Delta : ℝ)) *
          arityGainFactor Delta := by
  have hM : 1 ≤ M := by
    have := (p 0).isLt
    omega
  by_cases hCne : C.Nonempty
  · have h :=
      theorem1_BoundedAritySetCapacity.2 d M Delta Sigma p E f Q C hSigma hM hDelta hCne hCode
    simpa only [Nat.cast_pow, arityGainFactor] using h
  · have hEmpty : C = ∅ := Set.not_nonempty_iff_eq_empty.mp hCne
    subst hEmpty
    have hCard0 : Nat.card (∅ : Set (State d Sigma)) = 0 := Nat.card_of_isEmpty
    rw [hCard0]
    simp only [CharP.cast_eq_zero, Real.log_zero, zero_div, Nat.cast_pow]
    have hGainPos : 0 < arityGainFactor Delta := by
      unfold arityGainFactor
      positivity
    have hGainQuarter : arityGainFactor Delta ≤ 1 / 4 :=
      (pMin_two_sided_theta_inv_arity Delta hDelta).2.2
    have hd2 : 0 ≤ (d : ℝ) ^ 2 := by positivity
    have hE0 : 0 ≤ (E.card : ℝ) := Nat.cast_nonneg _
    have hdMDelta : 0 ≤ (d : ℝ) * (M : ℝ) * (Delta : ℝ) := by positivity
    nlinarith

/-- Direct instantiation on `CanonicalWordAlphabet d`. -/
theorem theorem1_CanonicalWordSetCapacity
    (d M Delta : ℕ) [NeZero d]
    (p : ZMod d → Fin M)
    (E : Finset (ZMod d × ZMod d))
    (f : Fin M → State d (CanonicalWordAlphabet d) → (ZMod d → CanonicalWordAlphabet d))
    (Q : Fin M → ZMod d → Finset (ZMod d × ZMod d))
    (C : Set (State d (CanonicalWordAlphabet d)))
    (hDelta : 1 ≤ Delta)
    (hCode : IsBoundedAritySetCode Delta p E f Q C) :
    Real.log (Nat.card C : ℝ) / Real.log (Fintype.card (CanonicalWordAlphabet d) : ℝ) ≤
      ((d ^ 2 : ℕ) : ℝ) -
        (((d ^ 2 : ℕ) : ℝ) - (E.card : ℝ) - (d : ℝ) * (M : ℝ) * (Delta : ℝ)) *
          arityGainFactor Delta :=
  theorem1_BoundedAritySetCapacity_unconditional d M Delta (CanonicalWordAlphabet d) p E f Q C
    (canonicalWordAlphabet_card_and_ge_two.1 d) hDelta hCode

/-- Strict exponential rate inequality from `growingClassesPositiveDeficit`: if `|E| ≤ δ d^2` and
`M ≤ η d / Delta` with `δ + η < 1`, then `log_{|Sigma|} |C| / d^2 < 1 - (1 - δ - η) / (e (Delta + 1))`. -/
theorem growingClasses_strict_inv_exp_deficit
    (d M Delta : ℕ) [NeZero d]
    (Sigma : Type*) [Fintype Sigma]
    (δ η : ℝ)
    (p : ZMod d → Fin M)
    (E : Finset (ZMod d × ZMod d))
    (f : Fin M → State d Sigma → (ZMod d → Sigma))
    (Q : Fin M → ZMod d → Finset (ZMod d × ZMod d))
    (C : Set (State d Sigma))
    (hSigma : 2 ≤ Fintype.card Sigma)
    (hDelta : 1 ≤ Delta)
    (hδ : 0 ≤ δ)
    (hη : 0 ≤ η)
    (hsum : δ + η < 1)
    (hE : (E.card : ℝ) ≤ δ * (d : ℝ) ^ 2)
    (hM_le : (M : ℝ) ≤ η * (d : ℝ) / (Delta : ℝ))
    (hCode : IsBoundedAritySetCode Delta p E f Q C) :
    Real.log (Nat.card C : ℝ) / (Real.log (Fintype.card Sigma : ℝ) * (d : ℝ) ^ 2) <
      1 - (1 - δ - η) / (Real.exp 1 * (Delta + 1 : ℝ)) := by
  have hM : 1 ≤ M := by
    have := (p 0).isLt
    omega
  have hPosCoeff : 0 < 1 - δ - η := by linarith
  by_cases hCne : C.Nonempty
  · obtain ⟨hRateLe, hGainGt⟩ :=
      growingClassesPositiveDeficit d M Delta Sigma δ η p E f Q C
        hSigma hM hDelta hδ hη hsum hE hM_le hCne hCode
    have hMulGt :
        (1 - δ - η) * (1 / (Real.exp 1 * (Delta + 1 : ℝ))) <
          (1 - δ - η) * ((Delta : ℝ) ^ Delta / ((Delta + 1 : ℝ) ^ (Delta + 1))) :=
      mul_lt_mul_of_pos_left hGainGt hPosCoeff
    rw [mul_one_div] at hMulGt
    linarith
  · have hEmpty : C = ∅ := Set.not_nonempty_iff_eq_empty.mp hCne
    subst hEmpty
    have hCard0 : Nat.card (∅ : Set (State d Sigma)) = 0 := Nat.card_of_isEmpty
    rw [hCard0]
    simp only [CharP.cast_eq_zero, Real.log_zero, zero_div]
    have hBounds := pMin_two_sided_theta_inv_arity Delta hDelta
    have hInvLtQuarter : 1 / (Real.exp 1 * (Delta + 1 : ℝ)) < 1 / 4 :=
      lt_of_lt_of_le hBounds.1 hBounds.2.2
    have hCoeffLe1 : 1 - δ - η ≤ 1 := by linarith
    have hFracLt : (1 - δ - η) / (Real.exp 1 * (Delta + 1 : ℝ)) < 1 / 4 := by
      calc (1 - δ - η) / (Real.exp 1 * (Delta + 1 : ℝ))
          = (1 - δ - η) * (1 / (Real.exp 1 * (Delta + 1 : ℝ))) := (mul_one_div _ _).symm
        _ ≤ 1 * (1 / (Real.exp 1 * (Delta + 1 : ℝ))) :=
            mul_le_mul_of_nonneg_right hCoeffLe1 (by positivity)
        _ < 1 / 4 := by linarith
    linarith

/-! ### 4. Finite-`d` One-Class (`M = 1, E = ∅`) Corollaries at `Δ = 1` and `Δ = 2` -/

/-- By `randomOrder_BoundedAritySetCapacity`, every `(1, p, ∅)`-bounded-arity code `C ⊆ Σ^{d × d}`
has normalized rate at most `1 / 2 + 1 / (2 d)` (strengthening the one-hop bound `3 / 4 + 1 / (4 d)`). -/
theorem corollary_OneClassArityOneHalf
    (d : ℕ) [NeZero d]
    (Sigma : Type*) [Fintype Sigma]
    (p : ZMod d → Fin 1)
    (f : Fin 1 → State d Sigma → (ZMod d → Sigma))
    (Q : Fin 1 → ZMod d → Finset (ZMod d × ZMod d))
    (C : Set (State d Sigma))
    (hSigma : 2 ≤ Fintype.card Sigma)
    (hCode : IsBoundedAritySetCode 1 p ∅ f Q C) :
    Real.log (Nat.card C : ℝ) / (Real.log (Fintype.card Sigma : ℝ) * (d : ℝ) ^ 2) ≤
      1 / 2 + 1 / (2 * (d : ℝ)) := by
  have hRand := randomOrder_BoundedAritySetCapacity d 1 1 Sigma p ∅ f Q C hSigma hCode
  simp only [Finset.card_empty, CharP.cast_eq_zero, Nat.cast_one, Nat.cast_pow] at hRand
  have hdPos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast NeZero.pos d
  have hd2Pos : (0 : ℝ) < (d : ℝ) ^ 2 := by positivity
  rw [← div_div, div_le_iff₀ hd2Pos]
  have hId : (1 / 2 + 1 / (2 * (d : ℝ))) * (d : ℝ) ^ 2 =
      (d : ℝ) ^ 2 - ((d : ℝ) ^ 2 - 0 - (d : ℝ) * 1 * 1) / (1 + 1) := by
    field_simp
    ring
  linarith

/-- By `randomOrder_BoundedAritySetCapacity`, every `(2, p, ∅)`-bounded-arity code `C ⊆ Σ^{d × d}`
has normalized rate at most `2 / 3 + 2 / (3 d)` (strengthening the one-hop bound
`23 / 27 + 8 / (27 d)`). -/
theorem corollary_OneClassArityTwoTwoThirds
    (d : ℕ) [NeZero d]
    (Sigma : Type*) [Fintype Sigma]
    (p : ZMod d → Fin 1)
    (f : Fin 1 → State d Sigma → (ZMod d → Sigma))
    (Q : Fin 1 → ZMod d → Finset (ZMod d × ZMod d))
    (C : Set (State d Sigma))
    (hSigma : 2 ≤ Fintype.card Sigma)
    (hCode : IsBoundedAritySetCode 2 p ∅ f Q C) :
    Real.log (Nat.card C : ℝ) / (Real.log (Fintype.card Sigma : ℝ) * (d : ℝ) ^ 2) ≤
      2 / 3 + 2 / (3 * (d : ℝ)) := by
  have hRand := randomOrder_BoundedAritySetCapacity d 1 2 Sigma p ∅ f Q C hSigma hCode
  simp only [Finset.card_empty, CharP.cast_eq_zero, Nat.cast_one, Nat.cast_ofNat,
    Nat.cast_pow] at hRand
  have hdPos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast NeZero.pos d
  have hd2Pos : (0 : ℝ) < (d : ℝ) ^ 2 := by positivity
  rw [← div_div, div_le_iff₀ hd2Pos]
  have hId : (2 / 3 + 2 / (3 * (d : ℝ))) * (d : ℝ) ^ 2 =
      (d : ℝ) ^ 2 - ((d : ℝ) ^ 2 - 0 - (d : ℝ) * 1 * 2) / (2 + 1) := by
    field_simp
    ring
  linarith

/-! ### 5. Unrestricted-Arity (`Δ = d^2`) Rate Lower Bounds & Convergence to Rate `1` -/

private theorem mul_card_ge_pow_imp_rate_lower {d K : ℕ} {Sigma : Type*} [Fintype Sigma]
    {C : Set (State d Sigma)}
    (hd : 2 ≤ d) (hSigma : 2 ≤ Fintype.card Sigma) (hK : 1 ≤ K)
    (hMul : (Fintype.card Sigma) ^ (d ^ 2) ≤ K * Nat.card C) :
    C.Nonempty ∧
      1 - Real.log (K : ℝ) / (Real.log (Fintype.card Sigma : ℝ) * (d : ℝ) ^ 2) ≤
        Real.log (Nat.card C : ℝ) / (Real.log (Fintype.card Sigma : ℝ) * (d : ℝ) ^ 2) := by
  have hPowPos : 1 ≤ (Fintype.card Sigma) ^ (d ^ 2) :=
    Nat.one_le_pow _ _ (by omega)
  have hCne : C.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    rintro rfl
    have hCard0 : Nat.card (∅ : Set (State d Sigma)) = 0 := Nat.card_of_isEmpty
    rw [hCard0, mul_zero] at hMul
    omega
  have hCardPos : 1 ≤ Nat.card C := by
    by_contra h0
    have hEq0 : Nat.card C = 0 := by omega
    rw [hEq0, mul_zero] at hMul
    omega
  refine ⟨hCne, ?_⟩
  have hSigmaGt1 : (1 : ℝ) < (Fintype.card Sigma : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by decide : 1 < 2) hSigma
  have hLogSigmaPos : 0 < Real.log (Fintype.card Sigma : ℝ) := Real.log_pos hSigmaGt1
  have hdPos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hd)
  have hd2Pos : (0 : ℝ) < (d : ℝ) ^ 2 := by positivity
  have hDenPos : 0 < Real.log (Fintype.card Sigma : ℝ) * (d : ℝ) ^ 2 :=
    mul_pos hLogSigmaPos hd2Pos
  have hRealMul :
      ((Fintype.card Sigma : ℝ)) ^ (d ^ 2) ≤ (K : ℝ) * (Nat.card C : ℝ) := by
    exact_mod_cast hMul
  have hKPos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hCPos : (0 : ℝ) < (Nat.card C : ℝ) := by exact_mod_cast hCardPos
  have hLogLe :
      Real.log (Fintype.card Sigma : ℝ) * (d : ℝ) ^ 2 ≤
        Real.log (K : ℝ) + Real.log (Nat.card C : ℝ) := by
    have h := Real.log_le_log (pow_pos (by linarith) _) hRealMul
    rw [Real.log_pow, Nat.cast_pow, Real.log_mul hKPos.ne' hCPos.ne'] at h
    linarith
  have hLHS :
      1 - Real.log (K : ℝ) / (Real.log (Fintype.card Sigma : ℝ) * (d : ℝ) ^ 2) =
        (Real.log (Fintype.card Sigma : ℝ) * (d : ℝ) ^ 2 - Real.log (K : ℝ)) /
          (Real.log (Fintype.card Sigma : ℝ) * (d : ℝ) ^ 2) := by
    rw [sub_div, div_self hDenPos.ne']
  rw [hLHS]
  exact div_le_div_of_nonneg_right (by linarith) hDenPos.le

private theorem tendsto_one_sub_log_mul_div_sq (q : ℕ) (hq : 2 ≤ q) (c : ℝ) (hc : 1 ≤ c) :
    Filter.Tendsto
      (fun d : ℕ => 1 - Real.log (c * (d : ℝ)) / (Real.log (q : ℝ) * (d : ℝ) ^ 2))
      Filter.atTop (nhds 1) := by
  have hqGt1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast lt_of_lt_of_le (by decide : 1 < 2) hq
  have hLogQPos : 0 < Real.log (q : ℝ) := Real.log_pos hqGt1
  have hEvLow : ∀ᶠ d : ℕ in Filter.atTop,
      0 ≤ Real.log (c * (d : ℝ)) / (Real.log (q : ℝ) * (d : ℝ) ^ 2) := by
    refine (Filter.eventually_ge_atTop 1).mono fun d hd => ?_
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have hcd1 : 1 ≤ c * (d : ℝ) := by nlinarith
    exact div_nonneg (Real.log_nonneg hcd1) (by positivity)
  have hEvHigh : ∀ᶠ d : ℕ in Filter.atTop,
      Real.log (c * (d : ℝ)) / (Real.log (q : ℝ) * (d : ℝ) ^ 2) ≤
        (c / Real.log (q : ℝ)) * ((d : ℝ))⁻¹ := by
    refine (Filter.eventually_ge_atTop 1).mono fun d hd => ?_
    have hdPos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    have hcdPos : 0 < c * (d : ℝ) := by positivity
    have hLogLe : Real.log (c * (d : ℝ)) ≤ c * (d : ℝ) := by
      linarith [Real.log_le_sub_one_of_pos hcdPos]
    have hDenPos : 0 < Real.log (q : ℝ) * (d : ℝ) ^ 2 := by positivity
    calc Real.log (c * (d : ℝ)) / (Real.log (q : ℝ) * (d : ℝ) ^ 2)
        ≤ (c * (d : ℝ)) / (Real.log (q : ℝ) * (d : ℝ) ^ 2) :=
          div_le_div_of_nonneg_right hLogLe hDenPos.le
      _ = (c / Real.log (q : ℝ)) * ((d : ℝ))⁻¹ := by field_simp
  have hInvZero : Filter.Tendsto (fun d : ℕ => ((d : ℝ))⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hUpperZero : Filter.Tendsto
      (fun d : ℕ => (c / Real.log (q : ℝ)) * ((d : ℝ))⁻¹) Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using hInvZero.const_mul (c / Real.log (q : ℝ))
  have hQuotZero : Filter.Tendsto
      (fun d : ℕ => Real.log (c * (d : ℝ)) / (Real.log (q : ℝ) * (d : ℝ) ^ 2))
      Filter.atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hUpperZero hEvLow hEvHigh
  simpa only [sub_zero] using tendsto_const_nhds.sub hQuotZero

/-- **Unrestricted-Arity (`Δ = d^2`) Rate Lower Bound & Convergence to Rate `1`.**
1. For every finite alphabet `Sigma` (`2 ≤ |Sigma|`) and every `d ≥ 2` (`[NeZero d]`), unrestricted
   inspection (`SyntacticColumnSupport d`, cell cone arity `d ^ 2`) with a single class (`M = 1`)
   and zero broken outputs (`E = ∅`) yields a nonempty nonlinear code `C ⊆ Σ^{d × d}` achieving
   `|C| ≥ |Sigma|^{d^2} / (2 d)` (normalized rate `≥ 1 - log(2 d) / (log |Sigma| * d^2)`), and
   `|C| ≥ |Sigma|^{d^2} / d` whenever `d` is prime (compare Corollary A.2 of *Shared-Decoder
   Capacity for Matrix Transposition*).
2. For every alphabet size `q ≥ 2`, both rate lower-bound sequences converge to `1` as `d → ∞`. -/
theorem unrestrictedArity_RateLowerBoundAndTendstoOne.{u} :
    (∀ (d : ℕ) [NeZero d] (Sigma : Type u) [Fintype Sigma],
      2 ≤ d → 2 ≤ Fintype.card Sigma →
      ∃ (f : Fin 1 → State d Sigma → (ZMod d → Sigma))
        (Q : Fin 1 → ZMod d → Finset (ZMod d × ZMod d))
        (C : Set (State d Sigma)),
        C.Nonempty ∧
        IsBoundedAritySetCode (d ^ 2) (fun _ => 0) ∅ f Q C ∧
        SyntacticColumnSupport d f (fun _ _ => Finset.univ) ∧
        1 - Real.log (2 * (d : ℝ)) / (Real.log (Fintype.card Sigma : ℝ) * (d : ℝ) ^ 2) ≤
          Real.log (Nat.card C : ℝ) / (Real.log (Fintype.card Sigma : ℝ) * (d : ℝ) ^ 2) ∧
        (Nat.Prime d →
          1 - Real.log (d : ℝ) / (Real.log (Fintype.card Sigma : ℝ) * (d : ℝ) ^ 2) ≤
            Real.log (Nat.card C : ℝ) / (Real.log (Fintype.card Sigma : ℝ) * (d : ℝ) ^ 2))) ∧
    (∀ q : ℕ, 2 ≤ q →
      Filter.Tendsto
        (fun d : ℕ => 1 - Real.log (2 * (d : ℝ)) / (Real.log (q : ℝ) * (d : ℝ) ^ 2))
        Filter.atTop (nhds 1) ∧
      Filter.Tendsto
        (fun d : ℕ => 1 - Real.log (d : ℝ) / (Real.log (q : ℝ) * (d : ℝ) ^ 2))
        Filter.atTop (nhds 1)) := by
  refine ⟨?_, ?_⟩
  · intro d _ Sigma _ hd hSigma
    have hColUniv : ∀ (f : Fin 1 → State d Sigma → (ZMod d → Sigma)),
        SyntacticColumnSupport d f (fun _ _ => Finset.univ) := by
      intro f
      refine ⟨fun _ _ => by simp [ZMod.card], fun _ r Y₁ Y₂ hCol => ?_⟩
      have hEq : Y₁ = Y₂ := funext fun i => funext fun u => hCol i u (Finset.mem_univ u)
      rw [hEq]
    by_cases hp : Nat.Prime d
    · obtain ⟨C, f, Q, hCode, hMulPrime⟩ :=
        boundaryControl_DeficitVanishesAtDeltaEqD.{0, 0, u, 0}.2.2.2.1 d Sigma hp hSigma
      have hMul2d : (Fintype.card Sigma) ^ (d ^ 2) ≤ (2 * d) * Nat.card C :=
        hMulPrime.trans (Nat.mul_le_mul_right _ (by omega))
      obtain ⟨hCne, hRatePrime⟩ := mul_card_ge_pow_imp_rate_lower hd hSigma (by omega) hMulPrime
      obtain ⟨_, hRate2d⟩ := mul_card_ge_pow_imp_rate_lower hd hSigma (by omega) hMul2d
      exact ⟨f, Q, C, hCne, hCode, hColUniv f, by simpa [Nat.cast_mul] using hRate2d,
        fun _ => hRatePrime⟩
    · obtain ⟨C, f, Q, hCode, hMul2d⟩ :=
        boundaryControl_DeficitVanishesAtDeltaEqD.{0, 0, 0, u}.2.2.2.2 d Sigma hd hSigma
      obtain ⟨hCne, hRate2d⟩ := mul_card_ge_pow_imp_rate_lower hd hSigma (by omega) hMul2d
      exact ⟨f, Q, C, hCne, hCode, hColUniv f, by simpa [Nat.cast_mul] using hRate2d,
        fun hp' => absurd hp' hp⟩
  · intro q hq
    refine ⟨tendsto_one_sub_log_mul_div_sq q hq 2 (by norm_num), ?_⟩
    simpa only [one_mul] using tendsto_one_sub_log_mul_div_sq q hq 1 le_rfl

/-- **Unrestricted-Arity Logarithmic Remainder Along All Dimensions (wrapping
`SharedDecoders.SetCapacity`).**
For every finite alphabet `Sigma` (`2 ≤ |Sigma|`) and every `d = n + 1`, `SharedDecoders.SetCapacity.Chosen`
is a valid `(d^2, fun _ => 0, ∅)`-bounded-arity nonlinear shared code achieving
`SharedDecoders.SetCapacity.capacity` and satisfying
`log_{|Sigma|} |Chosen| - (d^2 - log_{|Sigma|} d) → 0` as `d → ∞`. -/
theorem unrestrictedArity_ExactLogarithmicAsymptoticAllDimensions.{u}
    (Sigma : Type u) [Fintype Sigma] (hSigma : 2 ≤ Fintype.card Sigma) :
    (∀ n : ℕ,
      let d := n + 1
      ∃ (f : Fin 1 → State d Sigma → (ZMod d → Sigma))
        (Q : Fin 1 → ZMod d → Finset (ZMod d × ZMod d)),
        IsBoundedAritySetCode (d ^ 2) (fun _ => 0) ∅ f Q
          (SharedDecoders.SetCapacity.Chosen (d := d) (A := Sigma)) ∧
        SyntacticColumnSupport d f (fun _ _ => Finset.univ) ∧
        Nat.card (SharedDecoders.SetCapacity.Chosen (d := d) (A := Sigma)) =
          SharedDecoders.SetCapacity.capacity (d := d) (A := Sigma)) ∧
    Filter.Tendsto
      (fun n : ℕ =>
        Real.logb (Fintype.card Sigma : ℝ)
          (Nat.card (SharedDecoders.SetCapacity.Chosen (d := n + 1) (A := Sigma)) : ℝ) -
        (((n + 1 : ℕ) : ℝ) ^ 2 - Real.logb (Fintype.card Sigma : ℝ) (n + 1)))
      Filter.atTop (nhds 0) := by
  have : Nonempty Sigma := Fintype.card_pos_iff.mp (by omega)
  refine ⟨fun n => ?_, ?_⟩
  · dsimp only
    obtain ⟨f₀, hf₀⟩ :=
      SharedDecoders.SetCapacity.chosen_isCode (d := n + 1) (A := Sigma)
    refine ⟨fun _ => f₀, fun _ _ => Finset.univ, ?_, ?_,
      SharedDecoders.SetCapacity.chosen_card (d := n + 1) (A := Sigma)⟩
    · refine ⟨⟨fun _ _ => ?_, fun _ r Y₁ Y₂ hEq => ?_⟩, fun X hX r c _ => ?_⟩
      · simp [ZMod.card, sq]
      · have hY : Y₁ = Y₂ :=
          funext fun i => funext fun u => hEq (i, u) (Finset.mem_univ (i, u))
        rw [hY]
      · exact congrFun (hf₀ X hX c) r
    · refine ⟨fun _ _ => by simp [ZMod.card], fun _ r Y₁ Y₂ hCol => ?_⟩
      have hY : Y₁ = Y₂ :=
        funext fun i => funext fun u => hCol i u (Finset.mem_univ u)
      rw [hY]
  · simpa only [SharedDecoders.SetCapacity.positiveCapacity,
      SharedDecoders.SetCapacity.chosen_card] using
      SharedDecoders.SetCapacity.logarithmic_rate_tendsto (A := Sigma) hSigma

/-! ### 6. Asymptotic Sublinear-Class Rate Deficit (`M_d = o(d / Δ)`) -/

/-- For any fixed cell cone arity `Delta ≥ 1`, any unbroken output fraction `δ ∈ (0, 1]`, and any
family of `(Delta, p_d, E_d)`-bounded-arity nonlinear shared codes `C_d ⊆ (Sigma d)^{d × d}` with
`M_d = o(d / Delta)` and `|E_d| ≤ (1 - δ) d^2`, eventually
`log_{|Sigma d|} |C_d| / d^2 ≤ 1 - δ / (2 * (Delta + 1))`, refuting convergence to rate `1`. -/
theorem asymptotic_SublinearClassesBrokenFractionRefutesRateOne
    (Delta : ℕ) (hDelta : 1 ≤ Delta)
    (δ : ℝ) (hδPos : 0 < δ) (_hδLe : δ ≤ 1)
    (Sigma : ℕ → Type*) [∀ d, Fintype (Sigma d)]
    (hSigma : ∀ d : ℕ, 2 ≤ d → 2 ≤ Fintype.card (Sigma d))
    (M : ℕ → ℕ)
    (p : ∀ d, ZMod d → Fin (M d))
    (E : ∀ d, Finset (ZMod d × ZMod d))
    (f : ∀ d, Fin (M d) → State d (Sigma d) → (ZMod d → Sigma d))
    (Q : ∀ d, Fin (M d) → ZMod d → Finset (ZMod d × ZMod d))
    (C : ∀ d, Set (State d (Sigma d)))
    (hSublinear :
      Filter.Tendsto (fun d : ℕ => (M d : ℝ) * (Delta : ℝ) / (d : ℝ)) Filter.atTop (nhds 0))
    (hBroken : ∀ d : ℕ, 2 ≤ d → ((E d).card : ℝ) ≤ (1 - δ) * (d : ℝ) ^ 2)
    (hCode : ∀ (d : ℕ) [NeZero d], 2 ≤ d →
      IsBoundedAritySetCode Delta (p d) (E d) (f d) (Q d) (C d)) :
    0 < δ / (2 * ((Delta : ℝ) + 1)) ∧
      (∀ᶠ d in Filter.atTop,
        Real.log (Nat.card (C d) : ℝ) /
            (Real.log (Fintype.card (Sigma d) : ℝ) * (d : ℝ) ^ 2) ≤
          1 - δ / (2 * ((Delta : ℝ) + 1))) ∧
      ¬ Filter.Tendsto
          (fun d : ℕ =>
            Real.log (Nat.card (C d) : ℝ) /
              (Real.log (Fintype.card (Sigma d) : ℝ) * (d : ℝ) ^ 2))
          Filter.atTop (nhds 1) := by
  have hDenPos : (0 : ℝ) < (Delta : ℝ) + 1 := by positivity
  have hDefPos : 0 < δ / (2 * ((Delta : ℝ) + 1)) := by positivity
  have hEvSmall : ∀ᶠ d in Filter.atTop,
      (M d : ℝ) * (Delta : ℝ) / (d : ℝ) < δ / 2 :=
    (tendsto_order.mp hSublinear).2 (δ / 2) (by linarith)
  have hEvRate : ∀ᶠ d in Filter.atTop,
      Real.log (Nat.card (C d) : ℝ) /
          (Real.log (Fintype.card (Sigma d) : ℝ) * (d : ℝ) ^ 2) ≤
        1 - δ / (2 * ((Delta : ℝ) + 1)) := by
    refine ((Filter.eventually_ge_atTop 2).and hEvSmall).mono fun d ⟨hd, hMd⟩ => ?_
    have : NeZero d := ⟨by omega⟩
    have hRand :=
      randomOrder_BoundedAritySetCapacity d (M d) Delta (Sigma d)
        (p d) (E d) (f d) (Q d) (C d) (hSigma d hd) (hCode d hd)
    rw [Nat.cast_pow] at hRand
    have hdPos : (0 : ℝ) < (d : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hd)
    have hd2Pos : (0 : ℝ) < (d : ℝ) ^ 2 := by positivity
    have hMDeltaLe : (M d : ℝ) * (Delta : ℝ) ≤ (δ / 2) * (d : ℝ) :=
      (div_le_iff₀ hdPos).mp hMd.le
    have hdMDeltaLe : (d : ℝ) * (M d : ℝ) * (Delta : ℝ) ≤ (δ / 2) * (d : ℝ) ^ 2 := by
      nlinarith
    have hEdLe := hBroken d hd
    have hCleanCoeff :
        (δ / 2) * (d : ℝ) ^ 2 ≤
          (d : ℝ) ^ 2 - ((E d).card : ℝ) - (d : ℝ) * (M d : ℝ) * (Delta : ℝ) := by
      linarith
    have hDivCoeff :
        ((δ / 2) * (d : ℝ) ^ 2) / ((Delta : ℝ) + 1) ≤
          ((d : ℝ) ^ 2 - ((E d).card : ℝ) - (d : ℝ) * (M d : ℝ) * (Delta : ℝ)) /
            ((Delta : ℝ) + 1) :=
      div_le_div_of_nonneg_right hCleanCoeff hDenPos.le
    rw [← div_div, div_le_iff₀ hd2Pos]
    have hEq : (1 - δ / (2 * ((Delta : ℝ) + 1))) * (d : ℝ) ^ 2 =
        (d : ℝ) ^ 2 - ((δ / 2) * (d : ℝ) ^ 2) / ((Delta : ℝ) + 1) := by
      field_simp
    linarith
  refine ⟨hDefPos, hEvRate, ?_⟩
  intro hLim
  have hEvGt : ∀ᶠ d in Filter.atTop,
      1 - δ / (2 * ((Delta : ℝ) + 1)) <
        Real.log (Nat.card (C d) : ℝ) /
          (Real.log (Fintype.card (Sigma d) : ℝ) * (d : ℝ) ^ 2) :=
    (tendsto_order.mp hLim).1 (1 - δ / (2 * ((Delta : ℝ) + 1))) (by linarith)
  rcases (hEvRate.and hEvGt).exists with ⟨_, hLe, hGt⟩
  linarith

end BoundedArityDecoders
