import BoundedArityDecoders.BoundedAritySetCapacity

/-!
# Proofs of Clean-Entry Counting, One-Hop Recovery, and `Δ = d` Boundary Controls

Complete proofs of the bounded-arity set-capacity specifications in
`BoundedArityDecoders.BoundedAritySetCapacity`:

1. `selfReferentialAndCleanCount : SelfReferentialAndCleanCountSpec`
2. `oneHopRecoverableInjective : OneHopRecoverableInjectiveSpec`
3. `existsRecoverableSubsetBound : ExistsRecoverableSubsetBoundSpec`
4. `theorem1_BoundedAritySetCapacity : Theorem1_BoundedAritySetCapacitySpec`
5. `boundaryControl_DeficitVanishesAtDeltaEqD : BoundaryControl_DeficitVanishesAtDeltaEqDSpec`
6. `growingClassesPositiveDeficit : GrowingClassesPositiveDeficitSpec`
-/

namespace BoundedArityDecoders

open SharedDecoders
open scoped BigOperators

/-! ### 1. Self-Referential Equivalence & Clean Entry Count -/

theorem mem_shiftedFootprint_self_iff {d M : ℕ} [DecidableEq (ZMod d)]
    (p : ZMod d → Fin M)
    (Q : Fin M → ZMod d → Finset (ZMod d × ZMod d))
    (c r : ZMod d) :
    (c, r) ∈ shiftedFootprint p Q c r ↔ (c, r - c) ∈ Q (p c) r := by
  unfold shiftedFootprint
  simp only [Finset.mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨u, v⟩, hq, rfl, hcv⟩
    have hv : v = r - u := by
      calc v = (u + v) - u := by abel
        _ = r - u := by rw [hcv]
    rwa [hv] at hq
  · intro hq
    exact ⟨(c, r - c), hq, rfl, add_sub_cancel c r⟩

theorem selfReferentialAndCleanCount : SelfReferentialAndCleanCountSpec := by
  intro d M Delta _ p Q E
  refine ⟨fun c r => mem_shiftedFootprint_self_iff p Q c r, ?_⟩
  intro hQ
  refine ⟨?_, ?_⟩
  · let selfRef : Finset (ZMod d × ZMod d) :=
      Finset.univ.filter (fun cr => cr ∈ shiftedFootprint p Q cr.1 cr.2)
    have hcov : (Finset.univ : Finset (ZMod d × ZMod d)) ⊆
        (cleanEntries p Q E ∪ E.image Prod.swap) ∪ selfRef := by
      intro cr _
      simp only [Finset.mem_union, cleanEntries, selfRef, Finset.mem_filter,
        Finset.mem_univ, true_and, Finset.mem_image]
      by_cases hE : (cr.2, cr.1) ∈ E
      · exact Or.inl (Or.inr ⟨(cr.2, cr.1), hE, Prod.ext rfl rfl⟩)
      · by_cases hS : cr ∈ shiftedFootprint p Q cr.1 cr.2
        · exact Or.inr hS
        · exact Or.inl (Or.inl ⟨hE, hS⟩)
    have huniv : (Finset.univ : Finset (ZMod d × ZMod d)).card = d ^ 2 := by
      simp [ZMod.card, sq]
    have hswap : (E.image Prod.swap).card ≤ E.card := Finset.card_image_le
    let coverSelf : Finset (ZMod d × ZMod d) :=
      (Finset.univ : Finset (Fin M × ZMod d)).biUnion
        (fun mr => (Q mr.1 mr.2).image (fun q => (q.1, mr.2)))
    have hselfSub : selfRef ⊆ coverSelf := by
      intro cr hcr
      simp only [selfRef, Finset.mem_filter, Finset.mem_univ, true_and] at hcr
      have hq : (cr.1, cr.2 - cr.1) ∈ Q (p cr.1) cr.2 :=
        (mem_shiftedFootprint_self_iff p Q cr.1 cr.2).mp hcr
      simp only [coverSelf, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]
      exact ⟨(p cr.1, cr.2), (cr.1, cr.2 - cr.1), hq, Prod.ext rfl rfl⟩
    have hselfCard : selfRef.card ≤ d * M * Delta := by
      calc selfRef.card ≤ coverSelf.card := Finset.card_le_card hselfSub
        _ ≤ ∑ mr : Fin M × ZMod d, ((Q mr.1 mr.2).image (fun q => (q.1, mr.2))).card :=
          Finset.card_biUnion_le
        _ ≤ ∑ _mr : Fin M × ZMod d, Delta := by
          refine Finset.sum_le_sum fun mr _ => ?_
          exact Finset.card_image_le.trans (hQ mr.1 mr.2)
        _ = (M * d) * Delta := by simp [ZMod.card]
        _ = d * M * Delta := by ring
    calc d ^ 2 = (Finset.univ : Finset (ZMod d × ZMod d)).card := huniv.symm
      _ ≤ ((cleanEntries p Q E ∪ E.image Prod.swap) ∪ selfRef).card := Finset.card_le_card hcov
      _ ≤ (cleanEntries p Q E ∪ E.image Prod.swap).card + selfRef.card := Finset.card_union_le _ _
      _ ≤ (cleanEntries p Q E).card + (E.image Prod.swap).card + selfRef.card :=
        Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ ≤ (cleanEntries p Q E).card + E.card + d * M * Delta := by omega
  · intro cr _
    exact Finset.card_image_le.trans (hQ (p cr.1) cr.2)

/-! ### 2. Acyclic One-Hop Determination Outside `Rec(Ω)` -/

theorem oneHopRecoverableInjective : OneHopRecoverableInjectiveSpec := by
  intro d M Delta _ Sigma _ p E f Q C hCode Ω
  rcases hCode with ⟨⟨_, hQsupp⟩, hValid⟩
  have hDet : ∀ X₁ ∈ C, ∀ X₂ ∈ C,
      (∀ cr : ZMod d × ZMod d, cr ∉ recoverableCells p Q E Ω → X₁ cr.1 cr.2 = X₂ cr.1 cr.2) →
      X₁ = X₂ := by
    intro X₁ hX₁ X₂ hX₂ hAgree
    funext c r
    by_cases hcr : (c, r) ∈ recoverableCells p Q E Ω
    · simp only [recoverableCells, Finset.mem_filter, Finset.mem_univ, true_and] at hcr
      rcases hcr with ⟨_, hnotE, hsub⟩
      rw [← hValid X₁ hX₁ r c hnotE, ← hValid X₂ hX₂ r c hnotE]
      refine hQsupp (p c) r (rot c X₁) (rot c X₂) ?_
      intro q hq
      have hqMem : (q.1, c + q.2) ∈ Ω :=
        hsub (Finset.mem_image.mpr ⟨q, hq, rfl⟩)
      have hqNotRec : (q.1, c + q.2) ∉ recoverableCells p Q E Ω := by
        simp [recoverableCells, hqMem]
      simpa only [rot_apply, add_comm] using hAgree (q.1, c + q.2) hqNotRec
    · exact hAgree (c, r) hcr
  refine ⟨hDet, ?_⟩
  let Rc : Finset (ZMod d × ZMod d) := Finset.univ \ recoverableCells p Q E Ω
  let res : C → (Rc → Sigma) := fun X cr => X.val cr.val.1 cr.val.2
  have hInj : Function.Injective res := by
    intro X₁ X₂ hEq
    apply Subtype.ext
    refine hDet X₁.val X₁.property X₂.val X₂.property ?_
    intro cr hcr
    have hmem : cr ∈ Rc := Finset.mem_sdiff.mpr ⟨Finset.mem_univ cr, hcr⟩
    exact congrFun hEq ⟨cr, hmem⟩
  have hRcCard : Rc.card = d ^ 2 - (recoverableCells p Q E Ω).card := by
    have huniv : (Finset.univ : Finset (ZMod d × ZMod d)).card = d ^ 2 := by
      simp [ZMod.card, sq]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), huniv]
  calc Nat.card C ≤ Nat.card (Rc → Sigma) := Nat.card_le_card_of_injective res hInj
    _ = Fintype.card (Rc → Sigma) := Nat.card_eq_fintype_card
    _ = (Fintype.card Sigma) ^ Rc.card := by simp
    _ = (Fintype.card Sigma) ^ (d ^ 2 - (recoverableCells p Q E Ω).card) := by rw [hRcCard]

/-! ### 3. Bernoulli First-Moment Recovery Witness -/

private theorem sum_powerset_binomial {α : Type*} [DecidableEq α]
    (K : Finset α) (a b : ℝ) :
    (∑ S ∈ K.powerset, a ^ S.card * b ^ (K.card - S.card)) = (a + b) ^ K.card := by
  induction K using Finset.induction_on with
  | empty => simp
  | @insert x K hx ih =>
    rw [Finset.card_insert_of_notMem hx, Finset.sum_powerset_insert hx]
    have hL : (∑ S ∈ K.powerset, a ^ S.card * b ^ (K.card + 1 - S.card)) =
        b * (∑ S ∈ K.powerset, a ^ S.card * b ^ (K.card - S.card)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun S hS => ?_
      have hScard : S.card ≤ K.card := Finset.card_le_card (Finset.mem_powerset.mp hS)
      have hsub : K.card + 1 - S.card = (K.card - S.card) + 1 := by omega
      rw [hsub, pow_succ]
      ring
    have hR : (∑ S ∈ K.powerset,
          a ^ (insert x S).card * b ^ (K.card + 1 - (insert x S).card)) =
        a * (∑ S ∈ K.powerset, a ^ S.card * b ^ (K.card - S.card)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun S hS => ?_
      have hxS : x ∉ S := fun h => hx (Finset.mem_powerset.mp hS h)
      rw [Finset.card_insert_of_notMem hxS, Nat.add_sub_add_right, pow_succ]
      ring
    rw [hL, hR, ih, pow_succ]
    ring

private theorem sum_bernoulliSubsetWeight_eq_one (d : ℕ) [NeZero d] (θ : ℝ) :
    (∑ Ω : Finset (ZMod d × ZMod d), bernoulliSubsetWeight d θ Ω) = 1 := by
  let U : Finset (ZMod d × ZMod d) := Finset.univ
  have hUcard : U.card = d ^ 2 := by simp [U, ZMod.card, sq]
  have huniv : (Finset.univ : Finset (Finset (ZMod d × ZMod d))) = U.powerset := by
    ext Ω
    simp [U]
  calc (∑ Ω : Finset (ZMod d × ZMod d), bernoulliSubsetWeight d θ Ω)
      = ∑ Ω ∈ U.powerset, θ ^ Ω.card * (1 - θ) ^ (U.card - Ω.card) := by
        rw [huniv]
        refine Finset.sum_congr rfl fun Ω _ => ?_
        simp [bernoulliSubsetWeight, hUcard]
    _ = (θ + (1 - θ)) ^ U.card := sum_powerset_binomial U θ (1 - θ)
    _ = 1 := by ring

theorem existsRecoverableSubsetBound : ExistsRecoverableSubsetBoundSpec := by
  intro d M Delta _ p Q E hDelta hQ θ p_min
  have hDeltaPos : (0 : ℝ) < (Delta : ℝ) := by exact_mod_cast hDelta
  have hDenPos : (0 : ℝ) < (Delta : ℝ) + 1 := by positivity
  have hθ0 : 0 ≤ θ := by
    dsimp [θ]
    positivity
  have hθ1 : θ ≤ 1 := by
    dsimp [θ]
    rw [div_le_one hDenPos]
    linarith
  have h1mθ : 1 - θ = 1 / ((Delta : ℝ) + 1) := by
    dsimp [θ]
    field_simp
    ring
  have hp_min_eq : p_min = (1 - θ) * θ ^ Delta := by
    dsimp [p_min, θ]
    rw [h1mθ, div_pow, one_div_mul_eq_div, div_div, ← pow_succ]
  have hPerCell : ∀ cr ∈ cleanEntries p Q E,
      (∑ Ω ∈ (Finset.univ : Finset (Finset (ZMod d × ZMod d))).filter
          (fun Ω => cr ∈ recoverableCells p Q E Ω),
        bernoulliSubsetWeight d θ Ω) =
        (1 - θ) * θ ^ (shiftedFootprint p Q cr.1 cr.2).card ∧
      p_min ≤ (1 - θ) * θ ^ (shiftedFootprint p Q cr.1 cr.2).card := by
    intro cr hcr
    have hcr' := hcr
    simp only [cleanEntries, Finset.mem_filter, Finset.mem_univ, true_and] at hcr'
    rcases hcr' with ⟨hnotE, hnotF⟩
    set F := shiftedFootprint p Q cr.1 cr.2
    let U : Finset (ZMod d × ZMod d) := Finset.univ
    let R : Finset (ZMod d × ZMod d) := U.erase cr \ F
    have hUcard : U.card = d ^ 2 := by simp [U, ZMod.card, sq]
    have hFsub : F ⊆ U.erase cr := by
      intro x hx
      exact Finset.mem_erase.mpr ⟨fun hEq => hnotF (hEq ▸ hx), Finset.mem_univ x⟩
    have hEraseCard : (U.erase cr).card = d ^ 2 - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ cr), hUcard]
    have hd2Pos : 1 ≤ d ^ 2 := by
      have hd1 : 1 ≤ d := NeZero.one_le
      nlinarith
    have hFRcard : F.card + R.card + 1 = d ^ 2 := by
      have hsdiff : R.card = (U.erase cr).card - F.card :=
        Finset.card_sdiff_of_subset hFsub
      have hFle : F.card ≤ (U.erase cr).card := Finset.card_le_card hFsub
      omega
    have hDisjFR : Disjoint F R := Finset.disjoint_sdiff
    have hSumEq :
        (∑ Ω ∈ (Finset.univ : Finset (Finset (ZMod d × ZMod d))).filter
            (fun Ω => cr ∈ recoverableCells p Q E Ω),
          bernoulliSubsetWeight d θ Ω) =
        (1 - θ) * θ ^ F.card := by
      let Ev := (Finset.univ : Finset (Finset (ZMod d × ZMod d))).filter
        (fun Ω => cr ∈ recoverableCells p Q E Ω)
      have hBij :
          (∑ Ω ∈ Ev, bernoulliSubsetWeight d θ Ω) =
          ∑ S ∈ R.powerset, bernoulliSubsetWeight d θ (F ∪ S) := by
        symm
        refine Finset.sum_bij (fun S _ => F ∪ S) ?_ ?_ ?_ ?_
        · intro S hS
          have hSsub : S ⊆ R := Finset.mem_powerset.mp hS
          have hcrNotS : cr ∉ S := by
            intro hmem
            have hmemR := hSsub hmem
            exact (Finset.mem_erase.mp (Finset.mem_sdiff.mp hmemR).1).1 rfl
          simp only [Ev, recoverableCells, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_union, not_or]
          exact ⟨⟨hnotF, hcrNotS⟩, hnotE, Finset.subset_union_left⟩
        · intro S₁ hS₁ S₂ hS₂ hEq
          have hS₁R : Disjoint F S₁ :=
            hDisjFR.mono_right (Finset.mem_powerset.mp hS₁)
          have hS₂R : Disjoint F S₂ :=
            hDisjFR.mono_right (Finset.mem_powerset.mp hS₂)
          calc S₁ = (F ∪ S₁) \ F := (Finset.union_sdiff_cancel_left hS₁R).symm
            _ = (F ∪ S₂) \ F := by rw [hEq]
            _ = S₂ := Finset.union_sdiff_cancel_left hS₂R
        · intro Ω hΩ
          simp only [Ev, recoverableCells, Finset.mem_filter, Finset.mem_univ, true_and] at hΩ
          rcases hΩ with ⟨hcrNotΩ, _, hFsubΩ⟩
          refine ⟨Ω \ F, ?_, Finset.union_sdiff_of_subset hFsubΩ⟩
          rw [Finset.mem_powerset]
          intro x hx
          rcases Finset.mem_sdiff.mp hx with ⟨hxΩ, hxNotF⟩
          exact Finset.mem_sdiff.mpr
            ⟨Finset.mem_erase.mpr ⟨fun hEq => hcrNotΩ (hEq ▸ hxΩ), Finset.mem_univ x⟩, hxNotF⟩
        · intro _ _; rfl
      rw [hBij]
      calc (∑ S ∈ R.powerset, bernoulliSubsetWeight d θ (F ∪ S))
          = (1 - θ) * θ ^ F.card *
              (∑ S ∈ R.powerset, θ ^ S.card * (1 - θ) ^ (R.card - S.card)) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun S hS => ?_
            have hSsub : S ⊆ R := Finset.mem_powerset.mp hS
            have hDisjFS : Disjoint F S := hDisjFR.mono_right hSsub
            have hScard : S.card ≤ R.card := Finset.card_le_card hSsub
            have hCardUnion : (F ∪ S).card = F.card + S.card :=
              Finset.card_union_of_disjoint hDisjFS
            have hRem : d ^ 2 - (F ∪ S).card = (R.card - S.card) + 1 := by omega
            unfold bernoulliSubsetWeight
            rw [hRem, hCardUnion, pow_add, pow_succ]
            ring
        _ = (1 - θ) * θ ^ F.card * (θ + (1 - θ)) ^ R.card := by
            rw [sum_powerset_binomial]
        _ = (1 - θ) * θ ^ F.card := by ring
    refine ⟨hSumEq, ?_⟩
    have hFcardLe : F.card ≤ Delta :=
      (selfReferentialAndCleanCount d M Delta p Q E).2 hQ |>.2 cr hcr
    have hk : F.card + (Delta - F.card) = Delta := Nat.add_sub_of_le hFcardLe
    have hPowLe : θ ^ Delta ≤ θ ^ F.card := by
      have hTailLe : θ ^ (Delta - F.card) ≤ (1 : ℝ) ^ (Delta - F.card) :=
        pow_le_pow_left₀ hθ0 hθ1 _
      calc θ ^ Delta = θ ^ F.card * θ ^ (Delta - F.card) := by rw [← pow_add, hk]
        _ ≤ θ ^ F.card * (1 : ℝ) ^ (Delta - F.card) :=
          mul_le_mul_of_nonneg_left hTailLe (pow_nonneg hθ0 _)
        _ = θ ^ F.card := by simp
    rw [hp_min_eq]
    exact mul_le_mul_of_nonneg_left hPowLe (by linarith)
  have hExp :
      ((cleanEntries p Q E).card : ℝ) * p_min ≤
        (∑ Ω : Finset (ZMod d × ZMod d),
          bernoulliSubsetWeight d θ Ω * ((recoverableCells p Q E Ω).card : ℝ)) := by
    have hRecFilter : ∀ Ω : Finset (ZMod d × ZMod d),
        recoverableCells p Q E Ω =
          (cleanEntries p Q E).filter (fun cr => cr ∈ recoverableCells p Q E Ω) := by
      intro Ω
      ext cr
      simp only [recoverableCells, cleanEntries, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hnotΩ, hnotE, hsub⟩
        exact ⟨⟨hnotE, fun hF => hnotΩ (hsub hF)⟩, hnotΩ, hnotE, hsub⟩
      · rintro ⟨_, hrec⟩
        exact hrec
    have hSwap :
        (∑ Ω : Finset (ZMod d × ZMod d),
          bernoulliSubsetWeight d θ Ω * ((recoverableCells p Q E Ω).card : ℝ)) =
        ∑ cr ∈ cleanEntries p Q E,
          ∑ Ω ∈ (Finset.univ : Finset (Finset (ZMod d × ZMod d))).filter
              (fun Ω => cr ∈ recoverableCells p Q E Ω),
            bernoulliSubsetWeight d θ Ω := by
      calc (∑ Ω : Finset (ZMod d × ZMod d),
            bernoulliSubsetWeight d θ Ω * ((recoverableCells p Q E Ω).card : ℝ))
          = ∑ Ω : Finset (ZMod d × ZMod d),
              ∑ cr ∈ cleanEntries p Q E,
                if cr ∈ recoverableCells p Q E Ω then bernoulliSubsetWeight d θ Ω else 0 := by
            refine Finset.sum_congr rfl fun Ω _ => ?_
            conv_lhs => rw [hRecFilter Ω]
            rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun cr _ => ?_
            split_ifs <;> simp
        _ = ∑ cr ∈ cleanEntries p Q E,
              ∑ Ω : Finset (ZMod d × ZMod d),
                if cr ∈ recoverableCells p Q E Ω then bernoulliSubsetWeight d θ Ω else 0 :=
            Finset.sum_comm
        _ = ∑ cr ∈ cleanEntries p Q E,
              ∑ Ω ∈ (Finset.univ : Finset (Finset (ZMod d × ZMod d))).filter
                  (fun Ω => cr ∈ recoverableCells p Q E Ω),
                bernoulliSubsetWeight d θ Ω := by
            refine Finset.sum_congr rfl fun cr _ => ?_
            rw [← Finset.sum_filter]
    rw [hSwap]
    calc ((cleanEntries p Q E).card : ℝ) * p_min
        = ∑ _cr ∈ cleanEntries p Q E, p_min := by simp
      _ ≤ ∑ cr ∈ cleanEntries p Q E,
            ∑ Ω ∈ (Finset.univ : Finset (Finset (ZMod d × ZMod d))).filter
                (fun Ω => cr ∈ recoverableCells p Q E Ω),
              bernoulliSubsetWeight d θ Ω := by
          refine Finset.sum_le_sum fun cr hcr => ?_
          have h := hPerCell cr hcr
          linarith [h.1, h.2]
  refine ⟨hPerCell, hExp, ?_⟩
  have hCleanNat : d ^ 2 ≤ (cleanEntries p Q E).card + E.card + d * M * Delta :=
    (selfReferentialAndCleanCount d M Delta p Q E).2 hQ |>.1
  have hCleanReal :
      (d : ℝ) ^ 2 - (E.card : ℝ) - (d : ℝ) * (M : ℝ) * (Delta : ℝ) ≤
        ((cleanEntries p Q E).card : ℝ) := by
    have hCast : ((d : ℝ) ^ 2) ≤
        ((cleanEntries p Q E).card : ℝ) + (E.card : ℝ) + (d : ℝ) * (M : ℝ) * (Delta : ℝ) := by
      exact_mod_cast hCleanNat
    linarith
  have hp_min_nonneg : 0 ≤ p_min := by
    dsimp [p_min]
    positivity
  have hUnivNe : (Finset.univ : Finset (Finset (ZMod d × ZMod d))).Nonempty :=
    ⟨∅, Finset.mem_univ ∅⟩
  obtain ⟨Ωstar, _, hMax⟩ :=
    Finset.exists_max_image Finset.univ
      (fun Ω : Finset (ZMod d × ZMod d) => ((recoverableCells p Q E Ω).card : ℝ)) hUnivNe
  refine ⟨Ωstar, ?_⟩
  have hWeightNonneg : ∀ Ω : Finset (ZMod d × ZMod d), 0 ≤ bernoulliSubsetWeight d θ Ω := by
    intro Ω
    unfold bernoulliSubsetWeight
    exact mul_nonneg (pow_nonneg hθ0 _) (pow_nonneg (by linarith) _)
  calc ((d : ℝ) ^ 2 - (E.card : ℝ) - (d : ℝ) * (M : ℝ) * (Delta : ℝ)) * p_min
      ≤ ((cleanEntries p Q E).card : ℝ) * p_min :=
        mul_le_mul_of_nonneg_right hCleanReal hp_min_nonneg
    _ ≤ ∑ Ω : Finset (ZMod d × ZMod d),
          bernoulliSubsetWeight d θ Ω * ((recoverableCells p Q E Ω).card : ℝ) := hExp
    _ ≤ ∑ Ω : Finset (ZMod d × ZMod d),
          bernoulliSubsetWeight d θ Ω * ((recoverableCells p Q E Ωstar).card : ℝ) := by
        refine Finset.sum_le_sum fun Ω hΩ => ?_
        exact mul_le_mul_of_nonneg_left (hMax Ω hΩ) (hWeightNonneg Ω)
    _ = (∑ Ω : Finset (ZMod d × ZMod d), bernoulliSubsetWeight d θ Ω) *
          ((recoverableCells p Q E Ωstar).card : ℝ) := (Finset.sum_mul _ _ _).symm
    _ = ((recoverableCells p Q E Ωstar).card : ℝ) := by
        rw [sum_bernoulliSubsetWeight_eq_one d θ, one_mul]

/-! ### 4. Theorem 1 — Bounded-Arity Arbitrary-Set Shared-Decoder Capacity -/

theorem canonicalWordAlphabet_card (d : ℕ) :
    Fintype.card (CanonicalWordAlphabet d) = 2 ^ Transpose.entryBits d := by
  simp [CanonicalWordAlphabet]

theorem theorem1_BoundedAritySetCapacity : Theorem1_BoundedAritySetCapacitySpec := by
  refine ⟨fun d _ => canonicalWordAlphabet_card d, ?_⟩
  intro d M Delta _ Sigma _ p E f Q C hSigma _ hDelta hCne hCode
  obtain ⟨Ω, hΩ⟩ :=
    (existsRecoverableSubsetBound d M Delta p Q E hDelta hCode.1.1).2.2
  have hCardLe :
      Nat.card C ≤ (Fintype.card Sigma) ^ (d ^ 2 - (recoverableCells p Q E Ω).card) :=
    (oneHopRecoverableInjective d M Delta Sigma p E f Q C hCode Ω).2
  have : Nonempty C := hCne.to_subtype
  have hCpos : 0 < (Nat.card C : ℝ) := by exact_mod_cast Nat.card_pos (α := C)
  have hSigmaGt1 : (1 : ℝ) < (Fintype.card Sigma : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by decide : 1 < 2) hSigma
  have hLogSigmaPos : 0 < Real.log (Fintype.card Sigma : ℝ) := Real.log_pos hSigmaGt1
  have hCardReal :
      (Nat.card C : ℝ) ≤
        ((Fintype.card Sigma : ℝ)) ^ (d ^ 2 - (recoverableCells p Q E Ω).card) := by
    exact_mod_cast hCardLe
  have hLogLe :
      Real.log (Nat.card C : ℝ) ≤
        ((d ^ 2 - (recoverableCells p Q E Ω).card : ℕ) : ℝ) *
          Real.log (Fintype.card Sigma : ℝ) := by
    calc Real.log (Nat.card C : ℝ)
        ≤ Real.log (((Fintype.card Sigma : ℝ)) ^ (d ^ 2 - (recoverableCells p Q E Ω).card)) :=
          Real.log_le_log hCpos hCardReal
      _ = ((d ^ 2 - (recoverableCells p Q E Ω).card : ℕ) : ℝ) *
            Real.log (Fintype.card Sigma : ℝ) := Real.log_pow _ _
  have hRecLe : (recoverableCells p Q E Ω).card ≤ d ^ 2 := by
    have huniv : (Finset.univ : Finset (ZMod d × ZMod d)).card = d ^ 2 := by
      simp [ZMod.card, sq]
    rw [← huniv]
    exact Finset.card_le_card (Finset.subset_univ _)
  have hSubCast :
      ((d ^ 2 - (recoverableCells p Q E Ω).card : ℕ) : ℝ) =
        (d : ℝ) ^ 2 - ((recoverableCells p Q E Ω).card : ℝ) := by
    rw [Nat.cast_sub hRecLe, Nat.cast_pow]
  rw [div_le_iff₀ hLogSigmaPos]
  calc Real.log (Nat.card C : ℝ)
      ≤ ((d ^ 2 - (recoverableCells p Q E Ω).card : ℕ) : ℝ) *
          Real.log (Fintype.card Sigma : ℝ) := hLogLe
    _ ≤ ((d : ℝ) ^ 2 -
          ((d : ℝ) ^ 2 - (E.card : ℝ) - (d : ℝ) * (M : ℝ) * (Delta : ℝ)) *
            ((Delta : ℝ) ^ Delta / ((Delta + 1 : ℝ) ^ (Delta + 1)))) *
          Real.log (Fintype.card Sigma : ℝ) := by
        refine mul_le_mul_of_nonneg_right ?_ hLogSigmaPos.le
        rw [hSubCast]
        linarith

/-! ### 5. Boundary Control 1 — Exact `Δ = d` Boundary & Phase-Beacon / Full-Inspection Controls -/

private theorem boundaryControl_part2 (d : ℕ) [NeZero d] (Sigma : Type*) [Fintype Sigma]
    (_hd : 2 ≤ d) (hSigma : 2 ≤ Fintype.card Sigma) :
    ∃ (C : Set (State d Sigma))
      (f : Fin 1 → State d Sigma → (ZMod d → Sigma))
      (Q : Fin 1 → ZMod d → Finset (ZMod d × ZMod d)),
      IsBoundedAritySetCode d (fun _ => 0) ∅ f Q C ∧
      Nat.card C = ((Fintype.card Sigma) ^ d / d) ^ d := by
  classical
  let W := ZMod d → Sigma
  let K := (Fintype.card Sigma) ^ d / d
  have hCardW : Fintype.card W = (Fintype.card Sigma) ^ d := by
    simp [W, ZMod.card]
  let eW : W ≃ Fin ((Fintype.card Sigma) ^ d) :=
    (Fintype.equivFin W).trans (finCongr hCardW)
  have hdK : d * K ≤ (Fintype.card Sigma) ^ d := Nat.mul_div_le _ d
  let emb : ZMod d × Fin K ↪ W :=
    { toFun := fun ak => eW.symm ⟨ak.1.val * K + ak.2.val, by
        have ha : ak.1.val + 1 ≤ d := ak.1.val_lt
        have hk : ak.2.val < K := ak.2.isLt
        calc ak.1.val * K + ak.2.val < ak.1.val * K + K := by omega
          _ = (ak.1.val + 1) * K := by ring
          _ ≤ d * K := Nat.mul_le_mul_right K ha
          _ ≤ (Fintype.card Sigma) ^ d := hdK⟩
      inj' := by
        intro ⟨a₁, k₁⟩ ⟨a₂, k₂⟩ hEq
        have hIdx : a₁.val * K + k₁.val = a₂.val * K + k₂.val :=
          congrArg Fin.val (eW.symm.injective hEq)
        have hk₁ : k₁.val < K := k₁.isLt
        have hk₂ : k₂.val < K := k₂.isLt
        have haEq : a₁.val = a₂.val := by
          by_contra hne
          rcases lt_or_gt_of_ne hne with hlt | hlt <;> nlinarith
        have hkEq : k₁.val = k₂.val := by
          rw [haEq] at hIdx
          omega
        exact Prod.ext (ZMod.val_injective d haEq) (Fin.ext hkEq) }
  let mkMat : (ZMod d → Fin K) → State d Sigma :=
    fun g u v => emb (u + v, g (u + v)) u
  have hMkMatInj : Function.Injective mkMat := by
    intro g₁ g₂ hEq
    funext a
    have hWord : emb (a, g₁ a) = emb (a, g₂ a) := by
      funext u
      have hu := congrFun (congrFun hEq u) (a - u)
      have hab : u + (a - u) = a := by abel
      simpa only [mkMat, hab] using hu
    exact (Prod.mk.inj (emb.injective hWord)).2
  let C : Set (State d Sigma) := Set.range mkMat
  have hNonemptySigma : Nonempty Sigma :=
    Fintype.card_pos_iff.mp (lt_of_lt_of_le (by decide : 0 < 2) hSigma)
  let sDefault : Sigma := Classical.choice hNonemptySigma
  let decodeWord : W → ZMod d → Sigma := fun w r =>
    if h : ∃ ak : ZMod d × Fin K, emb ak = w then
      w ((Classical.choose h).1 - r)
    else sDefault
  let f : Fin 1 → State d Sigma → (ZMod d → Sigma) :=
    fun _ Y r => decodeWord (fun u => Y u (r - u)) r
  let Q : Fin 1 → ZMod d → Finset (ZMod d × ZMod d) :=
    fun _ r => Finset.univ.image (fun u : ZMod d => (u, r - u))
  refine ⟨C, f, Q, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · intro _ r
    calc (Finset.univ.image (fun u : ZMod d => (u, r - u))).card
        ≤ (Finset.univ : Finset (ZMod d)).card := Finset.card_image_le
      _ = d := by simp [ZMod.card]
  · intro _ r Y₁ Y₂ hAgree
    have hw : (fun u : ZMod d => Y₁ u (r - u)) = (fun u : ZMod d => Y₂ u (r - u)) := by
      funext u
      exact hAgree (u, r - u) (Finset.mem_image_of_mem _ (Finset.mem_univ u))
    dsimp [f]
    rw [hw]
  · rintro _ ⟨g, rfl⟩ r c _
    have hw : (fun u : ZMod d => rot c (mkMat g) u (r - u)) = emb (r + c, g (r + c)) := by
      funext u
      have hab : u + (r - u + c) = r + c := by abel
      simp only [rot_apply, mkMat, hab]
    change decodeWord (fun u => rot c (mkMat g) u (r - u)) r = mkMat g c r
    rw [hw]
    have hex : ∃ ak : ZMod d × Fin K, emb ak = emb (r + c, g (r + c)) :=
      ⟨(r + c, g (r + c)), rfl⟩
    dsimp only [decodeWord]
    rw [dite_eq_left hex]
    have hChoose : Classical.choose hex = (r + c, g (r + c)) :=
      emb.injective (Classical.choose_spec hex)
    rw [hChoose]
    have hrc : (r + c) - r = c := by abel
    rw [hrc]
    dsimp only [mkMat]
    rw [add_comm c r]
  · have hEquiv : (ZMod d → Fin K) ≃ C := Equiv.ofInjective mkMat hMkMatInj
    calc Nat.card C = Nat.card (ZMod d → Fin K) := (Nat.card_congr hEquiv).symm
      _ = Fintype.card (ZMod d → Fin K) := Nat.card_eq_fintype_card
      _ = K ^ d := by simp [ZMod.card]

private theorem boundaryControl_part3 (d : ℕ) [NeZero d] (Sigma : Type*) [Fintype Sigma]
    (hd : 2 ≤ d) (hSigma : 2 ≤ Fintype.card Sigma) :
    ∃ (C : Set (State d Sigma))
      (f : Fin 1 → State d Sigma → (ZMod d → Sigma))
      (Q : Fin 1 → ZMod d → Finset (ZMod d × ZMod d))
      (Qcol : Fin 1 → ZMod d → Finset (ZMod d)),
      IsBoundedAritySetCode (2 * d - 1) (fun _ => 0) ∅ f Q C ∧
      SyntacticColumnSupport d f Qcol ∧
      (Fintype.card Sigma) ^ (d * (d - 1)) ≤ Nat.card C := by
  classical
  have hOneLt : 1 < Fintype.card Sigma := lt_of_lt_of_le (by decide : 1 < 2) hSigma
  obtain ⟨s₀, s₁, hsne⟩ := Fintype.exists_pair_of_one_lt_card hOneLt
  let SubRow := {i : ZMod d // i ≠ 0}
  let mkBeacon : (SubRow → ZMod d → Sigma) → State d Sigma :=
    fun B i j => if hi : i = 0 then (if j = 0 then s₁ else s₀) else B ⟨i, hi⟩ j
  have hBeaconInj : Function.Injective mkBeacon := by
    intro B₁ B₂ hEq
    funext i j
    have hij := congrFun (congrFun hEq i.val) j
    simpa [mkBeacon, i.property] using hij
  let C : Set (State d Sigma) := Set.range mkBeacon
  let decodeBeacon : (ZMod d → Sigma) → (ZMod d → Sigma) → Sigma :=
    fun row0 anti =>
      if h : ∃ v : ZMod d, row0 v = s₁ then
        anti (- Classical.choose h)
      else s₀
  let f : Fin 1 → State d Sigma → (ZMod d → Sigma) :=
    fun _ Y r => decodeBeacon (fun v => Y 0 v) (fun u => Y u (r - u))
  let Q : Fin 1 → ZMod d → Finset (ZMod d × ZMod d) :=
    fun _ r =>
      (Finset.univ.image fun v : ZMod d => ((0 : ZMod d), v)) ∪
        (Finset.univ.image fun u : ZMod d => (u, r - u))
  let Qcol : Fin 1 → ZMod d → Finset (ZMod d) := fun _ _ => Finset.univ
  refine ⟨C, f, Q, Qcol, ⟨⟨?_, ?_⟩, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · intro _ r
    let A := Finset.univ.image fun v : ZMod d => ((0 : ZMod d), v)
    let B := Finset.univ.image fun u : ZMod d => (u, r - u)
    have hA : A.card ≤ d := by
      calc A.card ≤ (Finset.univ : Finset (ZMod d)).card := Finset.card_image_le
        _ = d := by simp [ZMod.card]
    have hB : B.card ≤ d := by
      calc B.card ≤ (Finset.univ : Finset (ZMod d)).card := Finset.card_image_le
        _ = d := by simp [ZMod.card]
    have hMemInter : ((0 : ZMod d), r) ∈ A ∩ B := by
      refine Finset.mem_inter.mpr ⟨?_, ?_⟩
      · exact Finset.mem_image_of_mem _ (Finset.mem_univ r)
      · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ 0, by simp⟩
    have hInterPos : 1 ≤ (A ∩ B).card := Finset.one_le_card.mpr ⟨(0, r), hMemInter⟩
    have hUnionInter := Finset.card_union_add_card_inter A B
    change (A ∪ B).card ≤ 2 * d - 1
    omega
  · intro _ r Y₁ Y₂ hAgree
    have hRow0 : (fun v : ZMod d => Y₁ 0 v) = (fun v : ZMod d => Y₂ 0 v) := by
      funext v
      exact hAgree (0, v) (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ v)))
    have hAnti : (fun u : ZMod d => Y₁ u (r - u)) = (fun u : ZMod d => Y₂ u (r - u)) := by
      funext u
      exact hAgree (u, r - u)
        (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ u)))
    dsimp only [f]
    rw [hRow0, hAnti]
  · rintro _ ⟨B, rfl⟩ r c _
    have hex : ∃ v : ZMod d, rot c (mkBeacon B) 0 v = s₁ := by
      refine ⟨-c, ?_⟩
      simp [rot_apply, mkBeacon]
    change (if h : ∃ v : ZMod d, rot c (mkBeacon B) 0 v = s₁ then
      rot c (mkBeacon B) (- Classical.choose h) (r - (- Classical.choose h)) else s₀) =
      mkBeacon B c r
    rw [dite_eq_left hex]
    let v : ZMod d := Classical.choose hex
    have hSpec : rot c (mkBeacon B) 0 v = s₁ := Classical.choose_spec hex
    have hChoose : v = -c := by
      have hSpec' : (if v + c = 0 then s₁ else s₀) = s₁ := by
        simpa only [rot_apply, mkBeacon, dite_true] using hSpec
      by_cases hvc : v + c = 0
      · exact eq_neg_of_add_eq_zero_left hvc
      · rw [ite_eq_right hvc] at hSpec'
        exact absurd hSpec' hsne
    change rot c (mkBeacon B) (-v) (r - -v) = mkBeacon B c r
    rw [hChoose, neg_neg, rot_apply, sub_add_cancel]
  · intro _ _
    simp [Qcol, ZMod.card]
  · intro _ r Y₁ Y₂ hCol
    have hEq : Y₁ = Y₂ := by
      funext i u
      exact hCol i u (Finset.mem_univ u)
    rw [hEq]
  · have hSubRowCard : Fintype.card SubRow = d - 1 := by
      rw [Fintype.card_subtype_compl, ZMod.card, Fintype.card_unique]
    have hEquiv : (SubRow → ZMod d → Sigma) ≃ C := Equiv.ofInjective mkBeacon hBeaconInj
    have hCardC : Nat.card C = (Fintype.card Sigma) ^ (d * (d - 1)) := by
      calc Nat.card C = Nat.card (SubRow → ZMod d → Sigma) := (Nat.card_congr hEquiv).symm
        _ = Fintype.card (SubRow → ZMod d → Sigma) := Nat.card_eq_fintype_card
        _ = ((Fintype.card Sigma) ^ d) ^ (d - 1) := by simp [ZMod.card, hSubRowCard]
        _ = (Fintype.card Sigma) ^ (d * (d - 1)) := (pow_mul _ _ _).symm
    exact le_of_eq hCardC.symm

theorem boundaryControl_DeficitVanishesAtDeltaEqD :
    BoundaryControl_DeficitVanishesAtDeltaEqDSpec := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro d M E hM
    have hM' : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    have hE0 : (0 : ℝ) ≤ (E.card : ℝ) := Nat.cast_nonneg E.card
    nlinarith
  · intro d _ Sigma _ hd hSigma
    exact boundaryControl_part2 d Sigma hd hSigma
  · intro d _ Sigma _ hd hSigma
    exact boundaryControl_part3 d Sigma hd hSigma
  · intro d _ Sigma _ hd hSigma
    have : Nonempty Sigma :=
      Fintype.card_pos_iff.mp (lt_of_lt_of_le (by decide : 0 < 2) hSigma)
    obtain ⟨f₀, hf₀⟩ := SetCapacity.chosen_isCode (d := d) (A := Sigma)
    refine ⟨SetCapacity.Chosen (d := d) (A := Sigma),
      fun _ => f₀, fun _ _ => Finset.univ, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · intro _ _
      simp [ZMod.card, sq]
    · intro _ r Y₁ Y₂ hAgree
      have hEq : Y₁ = Y₂ := funext fun i => funext fun j => hAgree (i, j) (Finset.mem_univ _)
      rw [hEq]
    · intro X hX r c _
      exact congrFun (hf₀ X hX c) r
    · rw [SetCapacity.chosen_card]
      have hPrime := SetCapacity.prime_capacity_mul (A := Sigma) hd
      rw [sq]
      omega
  · intro d _ Sigma _ hd hSigma
    have : Nonempty Sigma :=
      Fintype.card_pos_iff.mp (lt_of_lt_of_le (by decide : 0 < 2) hSigma)
    obtain ⟨f₀, hf₀⟩ := SetCapacity.chosen_isCode (d := d) (A := Sigma)
    refine ⟨SetCapacity.Chosen (d := d) (A := Sigma),
      fun _ => f₀, fun _ _ => Finset.univ, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · intro _ _
      simp [ZMod.card, sq]
    · intro _ r Y₁ Y₂ hAgree
      have hEq : Y₁ = Y₂ := funext fun i => funext fun j => hAgree (i, j) (Finset.mem_univ _)
      rw [hEq]
    · intro X hX r c _
      exact congrFun (hf₀ X hX c) r
    · rw [SetCapacity.chosen_card, sq]
      have hlo := (SetCapacity.capacity_two_sided (d := d) (A := Sigma)).1
      have he := SetCapacity.errorSum_le (d := d) (A := Sigma) (by omega)
      have h2e : 2 * SetCapacity.errorSum (d := d) (A := Sigma) ≤
          (Fintype.card Sigma) ^ (d * d) := by
        have h2d : 2 * (d - 1) ≤ (Fintype.card Sigma) ^ (d * ((d + 1) / 2)) := by
          calc 2 * (d - 1) ≤ 2 * d := by omega
            _ ≤ 2 ^ d := Nat.mul_le_pow (by decide) d
            _ ≤ (Fintype.card Sigma) ^ d := Nat.pow_le_pow_left hSigma d
            _ ≤ (Fintype.card Sigma) ^ (d * ((d + 1) / 2)) :=
              Nat.pow_le_pow_right (by omega) (by
                have : 1 ≤ (d + 1) / 2 := by omega
                nlinarith)
        calc 2 * SetCapacity.errorSum (d := d) (A := Sigma)
            ≤ 2 * ((d - 1) * (Fintype.card Sigma) ^ (d * (d / 2))) := Nat.mul_le_mul_left 2 he
          _ = (2 * (d - 1)) * (Fintype.card Sigma) ^ (d * (d / 2)) := by ring
          _ ≤ (Fintype.card Sigma) ^ (d * ((d + 1) / 2)) *
                (Fintype.card Sigma) ^ (d * (d / 2)) := Nat.mul_le_mul_right _ h2d
          _ = (Fintype.card Sigma) ^ (d * d) := by
            rw [← pow_add]
            congr 1
            have : (d + 1) / 2 + d / 2 = d := by omega
            nlinarith
      nlinarith

/-! ### 6. Growing Classes & Strict `1 / (e (Δ + 1))` Lower Bound -/

theorem arityFactor_gt_inv_exp (Delta : ℕ) (hDelta : 1 ≤ Delta) :
    1 / (Real.exp 1 * (Delta + 1 : ℝ)) <
      (Delta : ℝ) ^ Delta / ((Delta + 1 : ℝ) ^ (Delta + 1)) := by
  have hDeltaPos : (0 : ℝ) < (Delta : ℝ) := by exact_mod_cast hDelta
  have hInvPos : (0 : ℝ) < 1 / (Delta : ℝ) := by positivity
  have hStep : ((Delta : ℝ) + 1) / (Delta : ℝ) < Real.exp (1 / (Delta : ℝ)) := by
    have hEq : 1 / (Delta : ℝ) + 1 = ((Delta : ℝ) + 1) / (Delta : ℝ) := by
      field_simp
      ring
    rw [← hEq]
    exact Real.add_one_lt_exp hInvPos.ne'
  have hPow :
      (((Delta : ℝ) + 1) / (Delta : ℝ)) ^ Delta <
        (Real.exp (1 / (Delta : ℝ))) ^ Delta :=
    pow_lt_pow_left₀ hStep (by positivity) (by omega)
  have hExp1 : (Real.exp (1 / (Delta : ℝ))) ^ Delta = Real.exp 1 := by
    rw [← Real.exp_nat_mul, mul_one_div_cancel hDeltaPos.ne']
  rw [div_pow, hExp1, div_lt_iff₀ (pow_pos hDeltaPos _)] at hPow
  have hMul :
      ((Delta : ℝ) + 1) ^ (Delta + 1) <
        (Delta : ℝ) ^ Delta * (Real.exp 1 * ((Delta : ℝ) + 1)) := by
    have hMul' := mul_lt_mul_of_pos_right hPow (by positivity : (0 : ℝ) < (Delta : ℝ) + 1)
    rw [← pow_succ] at hMul'
    linarith
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  linarith

theorem growingClassesPositiveDeficit : GrowingClassesPositiveDeficitSpec := by
  intro d M Delta _ Sigma _ δ η p E f Q C hSigma hM hDelta _ _ _ hE hM_le hCne hCode
  refine ⟨?_, arityFactor_gt_inv_exp Delta hDelta⟩
  have hThm1 :=
    theorem1_BoundedAritySetCapacity.2 d M Delta Sigma p E f Q C hSigma hM hDelta hCne hCode
  have hDeltaPos : (0 : ℝ) < (Delta : ℝ) := by exact_mod_cast hDelta
  have hMDelta : (M : ℝ) * (Delta : ℝ) ≤ η * (d : ℝ) :=
    (le_div_iff₀ hDeltaPos).mp hM_le
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hdMDelta : (d : ℝ) * (M : ℝ) * (Delta : ℝ) ≤ η * (d : ℝ) ^ 2 := by
    nlinarith
  let p_min : ℝ := (Delta : ℝ) ^ Delta / ((Delta + 1 : ℝ) ^ (Delta + 1))
  have hp_min_nonneg : 0 ≤ p_min := by
    dsimp [p_min]
    positivity
  have hCleanCoeff :
      (1 - δ - η) * (d : ℝ) ^ 2 ≤
        (d : ℝ) ^ 2 - (E.card : ℝ) - (d : ℝ) * (M : ℝ) * (Delta : ℝ) := by
    linarith
  have hLogLe :
      Real.log (Nat.card C : ℝ) / Real.log (Fintype.card Sigma : ℝ) ≤
        (1 - (1 - δ - η) * p_min) * (d : ℝ) ^ 2 := by
    have hProdLe :
        ((1 - δ - η) * (d : ℝ) ^ 2) * p_min ≤
          ((d : ℝ) ^ 2 - (E.card : ℝ) - (d : ℝ) * (M : ℝ) * (Delta : ℝ)) * p_min :=
      mul_le_mul_of_nonneg_right hCleanCoeff hp_min_nonneg
    change Real.log (Nat.card C : ℝ) / Real.log (Fintype.card Sigma : ℝ) ≤
      (d : ℝ) ^ 2 - ((d : ℝ) ^ 2 - (E.card : ℝ) - (d : ℝ) * (M : ℝ) * (Delta : ℝ)) * p_min
      at hThm1
    nlinarith
  have hd2Pos : (0 : ℝ) < (d : ℝ) ^ 2 := by
    have hdPos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast NeZero.pos d
    positivity
  rw [← div_div, div_le_iff₀ hd2Pos]
  exact hLogLe

end BoundedArityDecoders
