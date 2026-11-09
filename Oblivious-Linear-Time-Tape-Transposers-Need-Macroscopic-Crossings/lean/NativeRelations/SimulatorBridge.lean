import NativeRelations.MacroscopicSkeleton

/-!
# Frozen-Trace Cone and Ball-Avoidance Coding Bounds

Proves the direct fibre-pigeonhole deficit bound for any set `S` of correctly transposed inputs
following one trace (`correctSubset_isAcyclicIn_coneSystem_deficit_le_logb`: deficit at most
`L - log₂ |S|`; `correctSubset_isAcyclicIn_coneSystem_deficit_le`: at most `η L` when
`|S| ≥ 2^{(1-η)L}`), its counting form for families of traces with a deficit certificate
(`card_correctInputs_le_of_coneDeficit`), the case of `η`-heavy traces of transposers
(`frozenTrace_isAcyclicIn_coneSystem_deficit_le`), and the ball-avoidance separator lower bound
(`frozenTrace_isAcyclicIn_ballAvoid_separator_card_ge`) on `η`-heavy traces of arbitrary machines.
-/

set_option autoImplicit false

namespace NativeRelations

open Filter Finset Transpose Transpose.Tape Transpose.Tape.Impl BoundedNesting SourceCovers
  MergeDepth MotionDepthCodes BoundedStackDepth TapeStorageRates
open scoped BigOperators Classical

/-! ## §1. Frozen-Trace Acyclic Deficit & Low-Adaptivity Macroscopic Expansion (Lemma 3.6 / Theorem E(a)) -/

/-- **Correct-subset deficit bound (Lemma 3.6 without full correctness):**
For any `M : TM`, `1 ≤ d`, `(valueWidth M : ℝ) ≤ β`, trace `τ₀ : Trace M.k` and nonempty
`S ⊆ fibre M L τ₀` of inputs that `M` transposes within `c (L + 1)` steps
(`L = d * d * entryBits d`, `T = τ₀.haltTime`), `τ₀` has the trace facts of Lemma 3.6 and
every cut `Γ : Finset ℕ` and subset `U : Finset (Fin L)` satisfying
`HalfRate.IsAcyclicIn (fun q => coneSystem τ₀ T Γ d (entryBits d) (tposOf d (entryBits d) q)) U`
satisfy `(U.card : ℝ) - β * (Γ.card : ℝ) ≤ L - log₂ |S|`. Only the inputs of `S` are assumed
correct: for each value word on `Γ`, those of them carrying it form a storage code. -/
theorem correctSubset_isAcyclicIn_coneSystem_deficit_le_logb {M : TM} {β c : ℝ} {d : ℕ}
    (hd : 1 ≤ d) (hvw : (valueWidth M : ℝ) ≤ β) {τ₀ : Trace M.k}
    {S : Finset (Fin (d * d * entryBits d) → Bool)} (hS : S.Nonempty)
    (hS_fib : S ⊆ fibre M (d * d * entryBits d) τ₀)
    (hS_tr : ∀ X ∈ S, TransposesInput M d (entryBits d) c X) :
    let b := entryBits d
    let L := d * d * b
    let T := τ₀.haltTime
    T ≤ ⌊c * ((L : ℝ) + 1)⌋₊ ∧
    0 < T ∧
    (T : ℝ) ≤ 2 * c * (L : ℝ) ∧
    (appendList τ₀ T).length = L ∧
    ∀ (Γ : Finset ℕ) (U : Finset (Fin L)),
      HalfRate.IsAcyclicIn (fun q => coneSystem τ₀ T Γ d b (tposOf d b q)) U →
      (U.card : ℝ) - β * (Γ.card : ℝ) ≤ (L : ℝ) - Real.logb 2 (S.card : ℝ) := by
  let b := entryBits d
  let L := d * d * b
  have hb : 1 ≤ b := one_le_entryBits d
  have hL_pos : 0 < L := Nat.mul_pos (Nat.mul_pos hd hd) hb
  have hS_pos : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast hS.card_pos
  obtain ⟨X₀, hX₀⟩ := hS
  obtain ⟨hT_floor, happ_eq⟩ := fibre_haltTime (hS_fib hX₀) (hS_tr X₀ hX₀)
  let T := τ₀.haltTime
  have hT_pos : 0 < T := prefix_pos hd hb happ_eq.ge
  have hT_real : (T : ℝ) ≤ 2 * c * (L : ℝ) := runtime_le hL_pos hT_pos hT_floor
  let ot : Fin L → ℕ := fun r => appendTime τ₀ T r.1
  have hot_lt : ∀ r : Fin L, ot r < T := fun r => appendTime_lt τ₀ T (happ_eq ▸ r.2)
  refine ⟨hT_floor, hT_pos, hT_real, happ_eq, fun Γ U hU_cone => ?_⟩
  have hS_trace : ∀ X ∈ (S : Set (Fin L → Bool)), trace M (List.ofFn X) = τ₀ :=
    fun _ hX => mem_fibre.mp (hS_fib (Finset.mem_coe.mp hX))
  let dfltVal : Value M := (⟨0, Nat.succ_pos _⟩, fun _ => ⟨0, Nat.succ_pos _⟩, none)
  let G : BlockFunDag L (Value M) :=
    { out := fun t => (Finset.range T).filter fun s => DepStep τ₀.work T t s
      out_lt := fun t s hs => (depStep_lt (Finset.mem_filter.mp hs).2).1
      blk := fun t => if t < T then inCells L τ₀.input {t} else ∅
      S := (S : Set (Fin L → Bool))
      val := fun X t => if t < T then stepValue M (List.ofFn X) t else dfltVal
      det := fun X hX Y hY t hpar hblk => by
        split_ifs with ht
        · refine stepValue_eq_of_parents
            (fun s _ => by rw [hS_trace X hX]) (fun s _ => by rw [hS_trace Y hY]) ht
            (fun p hp hpL => ?_) (fun u hu => ?_)
          · apply hblk ⟨p, hpL⟩
            simp only [ht, ↓reduceIte, inCells, Finset.mem_filter, Finset.mem_univ,
              Finset.mem_singleton, true_and]
            exact ⟨t, rfl, hp.symm⟩
          · have hdep_u : DepStep τ₀.work T t u := by
              rcases mem_actualParents.mp hu with rfl | ⟨h, h1, h2, h3, h4⟩
              · exact Or.inl ⟨rfl, ht⟩
              · exact Or.inr (Finset.mem_image.mpr
                  ⟨(h, u, t), mem_allHops.mpr ⟨h1, h2, h3, h4⟩, rfl⟩)
            have hu_lt : u < T := (depStep_lt hdep_u).1.trans ht
            have hu_out : u ∈ (Finset.range T).filter (fun s => DepStep τ₀.work T t s) :=
              Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hu_lt, hdep_u⟩
            have hp_eq := hpar u hu_out
            simpa only [hu_lt, ↓reduceIte] using hp_eq
        · rfl }
  have hdep_out : ∀ t, ∀ s ∈ G.net.out t, DepStep τ₀.work T t s :=
    fun _ _ hs => (Finset.mem_filter.mp hs).2
  let N_rel : Fin L → Finset (Fin L) := fun q => G.coneJ Γ (ot (tposOf d b q))
  -- Key inclusion: `N_rel q ⊆ coneSystem τ₀ T Γ d b (tposOf d b q)`.
  have hN_sub_cone : ∀ q : Fin L, N_rel q ⊆ coneSystem τ₀ T Γ d b (tposOf d b q) := by
    intro q p hp
    obtain ⟨u, hu_cone, hp_blk⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨π, hπ_path, hπ_free, rfl⟩ := (mem_coneV G.net).mp hu_cone
    obtain ⟨ρ, hπ_eq⟩ := G.net.mem_paths_head hπ_path
    have hπ_dep : IsDepPath τ₀.work T π := isDepPath_of_paths hdep_out π _ hπ_path
    rw [hπ_eq] at hπ_dep hπ_free hp_blk
    dsimp [G] at hp_blk
    split_ifs at hp_blk with hlt_T
    · obtain ⟨_, s, hs_eq, hxs⟩ := Finset.mem_filter.mp hp_blk
      rw [Finset.mem_singleton] at hs_eq
      subst hs_eq
      have hrd : readPos τ₀ L
          ((ot (tposOf d b q) :: ρ).getLastD (ot (tposOf d b q))) = some p :=
        readPos_eq_some_iff.mpr hxs
      simp only [coneSystem, depCone, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨ρ, hπ_dep, hπ_free, hrd⟩
    · simp at hp_blk
  have hU_N : HalfRate.IsAcyclicIn N_rel U :=
    isAcyclicIn_mono_rel (fun q _ => hN_sub_cone q) hU_cone
  have hdec : ∀ X ∈ G.S, ∀ r : Fin L,
      X (tposOf d b r) = (G.val X (ot r)).2.2.getD false := by
    intro X hX r
    have hp_out := (prefix_output happ_eq.ge (fun s _ => by rw [hS_trace X hX])
      (hS_tr X (Finset.mem_coe.mp hX)).outputsTranspose).2 (tposOf d b r)
    have htpos_r : Transpose.Tape.tpos d b (tposOf d b r) = r.1 :=
      congrArg Fin.val (tposOf_tposOf d b r)
    rw [htpos_r] at hp_out
    have hot_r : ot r < T := hot_lt r
    dsimp [G, ot]
    rw [ite_eq_left hot_r]
    change X (tposOf d b r) = (outBit M (List.ofFn X) (appendTime τ₀ T r.1)).getD false
    rw [hp_out]
    rfl
  let evalΓ : (Fin L → Bool) → (Γ → Value M) := fun X u => G.val X u.1
  have hS_sum : S.card =
      ∑ g₀ ∈ (Finset.univ : Finset (Γ → Value M)),
        (S.filter fun X => evalΓ X = g₀).card :=
    Finset.card_eq_sum_card_fiberwise fun _ _ => Finset.mem_univ _
  have hsubfib_le : ∀ g₀ : Γ → Value M,
      (S.filter fun X => evalΓ X = g₀).card ≤ 2 ^ (L - U.card) := by
    intro g₀
    let g_ext : ℕ → Value M := fun v => if hv : v ∈ Γ then g₀ ⟨v, hv⟩ else dfltVal
    have hsub : S.filter (fun X => evalΓ X = g₀) ⊆ G.fibre Γ g_ext := by
      intro X hX
      obtain ⟨hXS, hev⟩ := Finset.mem_filter.mp hX
      simp only [BlockFunDag.fibre, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨Finset.mem_coe.mpr hXS, fun v hv => ?_⟩
      have hv_eq := congrFun hev ⟨v, hv⟩
      simpa only [evalΓ, g_ext, hv, ↓reduceDIte] using hv_eq
    have hSC : MotionDepthCodes.IsStorageCode N_rel (G.fibre Γ g_ext) :=
      G.isStorageCode_fibre Γ ot (tposOf d b) (tposOf_tposOf d b)
        (fun X r => X (tposOf d b r)) (fun _ v => v.2.2.getD false)
        hdec (fun _ _ _ => rfl) g_ext
    have hcard_SC := storageCode_card_le_of_isAcyclicIn hU_N hSC
    simp only [Fintype.card_bool, Fintype.card_fin] at hcard_SC
    exact (Finset.card_le_card hsub).trans hcard_SC
  have hcod_card : (Finset.univ : Finset (Γ → Value M)).card ≤ 2 ^ (valueWidth M * Γ.card) := by
    calc (Finset.univ : Finset (Γ → Value M)).card
        = Fintype.card (Value M) ^ Γ.card := by
          rw [Finset.card_univ, Fintype.card_fun, Fintype.card_coe]
      _ ≤ (2 ^ valueWidth M) ^ Γ.card := Nat.pow_le_pow_left (card_value_le M) Γ.card
      _ = 2 ^ (valueWidth M * Γ.card) := (pow_mul 2 (valueWidth M) Γ.card).symm
  have hS_card_le : S.card ≤ 2 ^ (valueWidth M * Γ.card + (L - U.card)) := by
    calc S.card
        = ∑ g₀ ∈ (Finset.univ : Finset (Γ → Value M)),
            (S.filter fun X => evalΓ X = g₀).card := hS_sum
      _ ≤ ∑ _g₀ ∈ (Finset.univ : Finset (Γ → Value M)), 2 ^ (L - U.card) :=
          Finset.sum_le_sum fun g₀ _ => hsubfib_le g₀
      _ = (Finset.univ : Finset (Γ → Value M)).card * 2 ^ (L - U.card) := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ 2 ^ (valueWidth M * Γ.card) * 2 ^ (L - U.card) :=
          Nat.mul_le_mul_right _ hcod_card
      _ = 2 ^ (valueWidth M * Γ.card + (L - U.card)) := (pow_add 2 _ _).symm
  have hU_le_L : U.card ≤ L := U.card_le_univ.trans_eq (Fintype.card_fin L)
  have hS_rpow_hi : (S.card : ℝ) ≤
      (2 : ℝ) ^ ((valueWidth M : ℝ) * (Γ.card : ℝ) + ((L : ℝ) - (U.card : ℝ))) := by
    calc (S.card : ℝ)
        ≤ ((2 ^ (valueWidth M * Γ.card + (L - U.card)) : ℕ) : ℝ) := by exact_mod_cast hS_card_le
      _ = (2 : ℝ) ^ ((valueWidth M * Γ.card + (L - U.card) : ℕ) : ℝ) := by
          rw [Nat.cast_pow, Nat.cast_ofNat, Real.rpow_natCast]
      _ = (2 : ℝ) ^ ((valueWidth M : ℝ) * (Γ.card : ℝ) + ((L : ℝ) - (U.card : ℝ))) := by
          congr 1
          rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hU_le_L]
  have hlog : Real.logb 2 (S.card : ℝ) ≤
      (valueWidth M : ℝ) * (Γ.card : ℝ) + ((L : ℝ) - (U.card : ℝ)) :=
    (Real.logb_le_iff_le_rpow (by norm_num) hS_pos).mpr hS_rpow_hi
  have hvw_mul : (valueWidth M : ℝ) * (Γ.card : ℝ) ≤ β * (Γ.card : ℝ) :=
    mul_le_mul_of_nonneg_right hvw (Nat.cast_nonneg _)
  linarith

/-- **Correct-subset deficit bound, `η` form:** under the hypotheses of
`correctSubset_isAcyclicIn_coneSystem_deficit_le_logb`, with `2 ^ ((1 - η) L) ≤ |S|` in place of
`S.Nonempty`, the deficit bound reads `(U.card : ℝ) - β * (Γ.card : ℝ) ≤ η * L`. -/
theorem correctSubset_isAcyclicIn_coneSystem_deficit_le {M : TM} {β c η : ℝ} {d : ℕ}
    (hd : 1 ≤ d) (hvw : (valueWidth M : ℝ) ≤ β) {τ₀ : Trace M.k}
    {S : Finset (Fin (d * d * entryBits d) → Bool)}
    (hS_fib : S ⊆ fibre M (d * d * entryBits d) τ₀)
    (hS_tr : ∀ X ∈ S, TransposesInput M d (entryBits d) c X)
    (hS_card : (2 : ℝ) ^ ((1 - η) * ((d * d * entryBits d : ℕ) : ℝ)) ≤ (S.card : ℝ)) :
    let b := entryBits d
    let L := d * d * b
    let T := τ₀.haltTime
    T ≤ ⌊c * ((L : ℝ) + 1)⌋₊ ∧
    0 < T ∧
    (T : ℝ) ≤ 2 * c * (L : ℝ) ∧
    (appendList τ₀ T).length = L ∧
    ∀ (Γ : Finset ℕ) (U : Finset (Fin L)),
      HalfRate.IsAcyclicIn (fun q => coneSystem τ₀ T Γ d b (tposOf d b q)) U →
      (U.card : ℝ) - β * (Γ.card : ℝ) ≤ η * (L : ℝ) := by
  have hS_pos : (0 : ℝ) < (S.card : ℝ) := lt_of_lt_of_le (by positivity) hS_card
  obtain ⟨hT_floor, hT_pos, hT_real, happ_eq, hdef⟩ :=
    correctSubset_isAcyclicIn_coneSystem_deficit_le_logb hd hvw
      (Finset.card_pos.mp (by exact_mod_cast hS_pos)) hS_fib hS_tr
  have hlog : (1 - η) * ((d * d * entryBits d : ℕ) : ℝ) ≤ Real.logb 2 (S.card : ℝ) :=
    (Real.le_logb_iff_rpow_le (by norm_num) hS_pos).mpr hS_card
  exact ⟨hT_floor, hT_pos, hT_real, happ_eq, fun Γ U hU => by linarith [hdef Γ U hU]⟩

/-- **Counting form of the correct-subset deficit bound:** let `𝒯` be a finite set of traces of
`M` at size `d ≥ 1`, each carrying a deficit certificate: a step set `Γ` and a set `U` acyclic in
the cone relation of the trace avoiding `Γ`, with `|U| - valueWidth M * |Γ| ≥ δ L`. Then at most
`|𝒯| 2^{(1-δ)L}` inputs have their trace in `𝒯` and are transposed by `M` within `c (L + 1)`
steps, and if `|𝒯| ≤ 2^{ηL}`, at most `2^{(1-δ+η)L}`, a `2^{-(δ-η)L}` fraction of `{0,1}^L`. -/
theorem card_correctInputs_le_of_coneDeficit {M : TM} {c δ : ℝ} {d : ℕ} (hd : 1 ≤ d)
    (𝒯 : Finset (Trace M.k))
    (hcert : ∀ τ ∈ 𝒯, ∃ (Γ : Finset ℕ) (U : Finset (Fin (d * d * entryBits d))),
      HalfRate.IsAcyclicIn
        (fun q => coneSystem τ τ.haltTime Γ d (entryBits d) (tposOf d (entryBits d) q)) U ∧
      δ * ((d * d * entryBits d : ℕ) : ℝ) ≤ (U.card : ℝ) - (valueWidth M : ℝ) * (Γ.card : ℝ)) :
    let L := d * d * entryBits d
    let correct := (Finset.univ : Finset (Fin L → Bool)).filter fun X =>
      trace M (List.ofFn X) ∈ 𝒯 ∧ TransposesInput M d (entryBits d) c X
    (correct.card : ℝ) ≤ (𝒯.card : ℝ) * (2 : ℝ) ^ ((1 - δ) * (L : ℝ)) ∧
      ∀ η : ℝ, (𝒯.card : ℝ) ≤ (2 : ℝ) ^ (η * (L : ℝ)) →
        (correct.card : ℝ) ≤ (2 : ℝ) ^ ((1 - δ + η) * (L : ℝ)) := by
  intro L correct
  let S : Trace M.k → Finset (Fin L → Bool) := fun τ =>
    (fibre M L τ).filter fun X => TransposesInput M d (entryBits d) c X
  have hS_le : ∀ τ ∈ 𝒯, ((S τ).card : ℝ) ≤ (2 : ℝ) ^ ((1 - δ) * (L : ℝ)) := by
    intro τ hτ
    rcases (S τ).eq_empty_or_nonempty with h0 | hne
    · rw [h0, Finset.card_empty, Nat.cast_zero]
      positivity
    obtain ⟨Γ, U, hU, hδU⟩ := hcert τ hτ
    obtain ⟨-, -, -, -, hdef⟩ := correctSubset_isAcyclicIn_coneSystem_deficit_le_logb hd le_rfl hne
      (Finset.filter_subset _ _) fun _ hX => (Finset.mem_filter.mp hX).2
    have hdefU := hdef Γ U hU
    exact (Real.logb_le_iff_le_rpow (by norm_num) (by exact_mod_cast hne.card_pos)).mp
      (by linarith)
  have hsub : correct ⊆ 𝒯.biUnion S := fun X hX => by
    obtain ⟨hX𝒯, hXtr⟩ := (Finset.mem_filter.mp hX).2
    exact Finset.mem_biUnion.mpr ⟨_, hX𝒯, Finset.mem_filter.mpr ⟨mem_fibre.mpr rfl, hXtr⟩⟩
  have hcard : (correct.card : ℝ) ≤ (𝒯.card : ℝ) * (2 : ℝ) ^ ((1 - δ) * (L : ℝ)) :=
    calc (correct.card : ℝ)
        ≤ ∑ τ ∈ 𝒯, ((S τ).card : ℝ) := by
          exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_biUnion_le
      _ ≤ ∑ _τ ∈ 𝒯, (2 : ℝ) ^ ((1 - δ) * (L : ℝ)) := Finset.sum_le_sum hS_le
      _ = (𝒯.card : ℝ) * (2 : ℝ) ^ ((1 - δ) * (L : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  refine ⟨hcard, fun η h𝒯 => hcard.trans ?_⟩
  calc (𝒯.card : ℝ) * (2 : ℝ) ^ ((1 - δ) * (L : ℝ))
      ≤ (2 : ℝ) ^ (η * (L : ℝ)) * (2 : ℝ) ^ ((1 - δ) * (L : ℝ)) :=
        mul_le_mul_of_nonneg_right h𝒯 (by positivity)
    _ = (2 : ℝ) ^ ((1 - δ + η) * (L : ℝ)) := by
        rw [← Real.rpow_add (by norm_num)]
        ring_nf

/-- **Lemma 3.6 (`Frozen-Trace Acyclic Cone-System Deficit Bound`):**
For any `M : TM`, `1 ≤ d`, `TransposesAt M d c`, `(valueWidth M : ℝ) ≤ β`, and trace `τ₀ : Trace M.k`
with `(2 : ℝ) ^ (-η * L) ≤ traceProb M L τ₀` (`L = d * d * entryBits d`, `T = τ₀.haltTime`),
every cut `Γ : Finset ℕ` and subset `U : Finset (Fin L)` satisfying
`HalfRate.IsAcyclicIn (fun q => coneSystem τ₀ T Γ d (entryBits d) (tposOf d (entryBits d) q)) U`
satisfy `(U.card : ℝ) - β * (Γ.card : ℝ) ≤ η * (L : ℝ)`: the case `S = fibre M L τ₀` of
`correctSubset_isAcyclicIn_coneSystem_deficit_le`. -/
theorem frozenTrace_isAcyclicIn_coneSystem_deficit_le {M : TM} {β c η : ℝ} {d : ℕ} (hd : 1 ≤ d)
    (hvw : (valueWidth M : ℝ) ≤ β) (htr : TransposesAt M d c) {τ₀ : Trace M.k}
    (hprob : (2 : ℝ) ^ (-η * ((d * d * entryBits d : ℕ) : ℝ)) ≤
      traceProb M (d * d * entryBits d) τ₀) :
    let b := entryBits d
    let L := d * d * b
    let T := τ₀.haltTime
    T ≤ ⌊c * ((L : ℝ) + 1)⌋₊ ∧
    0 < T ∧
    (T : ℝ) ≤ 2 * c * (L : ℝ) ∧
    (appendList τ₀ T).length = L ∧
    ∀ (Γ : Finset ℕ) (U : Finset (Fin L)),
      HalfRate.IsAcyclicIn (fun q => coneSystem τ₀ T Γ d b (tposOf d b q)) U →
      (U.card : ℝ) - β * (Γ.card : ℝ) ≤ η * (L : ℝ) :=
  correctSubset_isAcyclicIn_coneSystem_deficit_le hd hvw subset_rfl
    (fun X _ => htr.transposesInput X) (two_rpow_le_card_fibre hprob)

/-- **Frozen-Trace Genie + `B`-Avoiding Acyclic Separator Bound (Lemma 3.6 / Theorem E(a) core):**
On any trace `τ₀` of `TransposesAt M d c` with `(2 : ℝ) ^ (-η * L) ≤ traceProb M L τ₀` (`and C ≥ max c 1`),
every step set `B` and `U` acyclic in `ballAvoidSystem τ₀ τ₀.haltTime (genieDepth M.k (valueWidth M) C ε) B d (entryBits d)`
satisfy `(U.card : ℝ) - (ε + η) * L ≤ valueWidth M * |B|`. -/
theorem frozenTrace_isAcyclicIn_ballAvoid_separator_card_ge {M : TM} {d : ℕ} {c C ε η : ℝ}
    (hd : 1 ≤ d) (hc_le : c ≤ C) (hC1 : 1 ≤ C) (hε : 0 < ε)
    (htr : TransposesAt M d c) {τ₀ : Trace M.k}
    (hprob : (2 : ℝ) ^ (-η * ((d * d * entryBits d : ℕ) : ℝ)) ≤
      traceProb M (d * d * entryBits d) τ₀)
    (B : Finset ℕ) (U : Finset (Fin (d * d * entryBits d)))
    (hU : HalfRate.IsAcyclicIn
      (ballAvoidSystem τ₀ τ₀.haltTime
        (genieDepth M.k (valueWidth M) C ε) B d (entryBits d)) U) :
    (U.card : ℝ) - (ε + η) * ((d * d * entryBits d : ℕ) : ℝ) ≤
      (valueWidth M : ℝ) * (B.card : ℝ) := by
  let b := entryBits d
  let L := d * d * b
  have hb1 : 1 ≤ b := one_le_entryBits d
  have hL1 : 1 ≤ L := Nat.mul_pos (Nat.mul_pos hd hd) hb1
  obtain ⟨hT_floor, hT_pos, _, _, hdef⟩ :=
    frozenTrace_isAcyclicIn_coneSystem_deficit_le hd le_rfl htr hprob
  have hL1_nn : (0 : ℝ) ≤ (L : ℝ) + 1 := by positivity
  have hT_le_C : (τ₀.haltTime : ℝ) ≤ C * ((L : ℝ) + 1) := by
    have hc_nn : 0 ≤ c * ((L : ℝ) + 1) := by
      by_cases hc0 : 0 ≤ c
      · positivity
      · exfalso
        have hneg : c * ((L : ℝ) + 1) < 0 := mul_neg_of_neg_of_pos (lt_of_not_ge hc0) (by positivity)
        have hfl0 : ⌊c * (((d * d * entryBits d : ℕ) : ℝ) + 1)⌋₊ = 0 :=
          Nat.floor_of_nonpos hneg.le
        have hle0 : τ₀.haltTime ≤ 0 := hT_floor.trans_eq hfl0
        exact absurd ( Nat.lt_of_lt_of_le hT_pos hle0 ) (lt_irrefl 0)
    calc (τ₀.haltTime : ℝ)
        ≤ (⌊c * ((L : ℝ) + 1)⌋₊ : ℝ) := by exact_mod_cast hT_floor
      _ ≤ c * ((L : ℝ) + 1) := Nat.floor_le hc_nn
      _ ≤ C * ((L : ℝ) + 1) := mul_le_mul_of_nonneg_right hc_le hL1_nn
  have hβ1 : 1 ≤ valueWidth M := (two_le_valueWidth M).trans' (by omega)
  obtain ⟨Γ, hcost, hpath⟩ := genie_cost hβ1 hL1 hC1 hε hT_le_C τ₀.work τ₀.work_isWalk
  have hU_cone : HalfRate.IsAcyclicIn
      (fun q => coneSystem τ₀ τ₀.haltTime (Γ ∪ B) d b (tposOf d b q)) U :=
    isAcyclicIn_mono_rel
      (fun q _ => coneSystem_subset_ballAvoidSystem τ₀ Γ B
        (fun π h1 h2 => (hpath π h1 h2).trans (Nat.le_succ _)) q) hU
  have hcone_def := hdef (Γ ∪ B) U hU_cone
  have hunion_nat : (Γ ∪ B).card ≤ Γ.card + B.card := card_union_le Γ B
  have hunion_r : ((Γ ∪ B).card : ℝ) ≤ (Γ.card : ℝ) + (B.card : ℝ) := by exact_mod_cast hunion_nat
  have hvw_nn : (0 : ℝ) ≤ (valueWidth M : ℝ) := by positivity
  have hcost_r : (valueWidth M : ℝ) * (Γ.card : ℝ) ≤ ε * (L : ℝ) := by
    simpa [Nat.cast_mul] using hcost
  have htot : (valueWidth M : ℝ) * ((Γ ∪ B).card : ℝ) ≤
      ε * (L : ℝ) + (valueWidth M : ℝ) * (B.card : ℝ) := by
    calc (valueWidth M : ℝ) * ((Γ ∪ B).card : ℝ)
        ≤ (valueWidth M : ℝ) * ((Γ.card : ℝ) + (B.card : ℝ)) :=
          mul_le_mul_of_nonneg_left hunion_r hvw_nn
      _ = (valueWidth M : ℝ) * (Γ.card : ℝ) + (valueWidth M : ℝ) * (B.card : ℝ) := mul_add _ _ _
      _ ≤ ε * (L : ℝ) + (valueWidth M : ℝ) * (B.card : ℝ) := add_le_add hcost_r le_rfl
  linarith

end NativeRelations
