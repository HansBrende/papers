import NativeRelations.SimulatorBridge

/-!
# Direct Rows-to-Columns Cut Lower Bound and Bichromatic Colourings (Lemma R)

Proves Lemma R (`isAcyclicIn_coneSystem_uncutRootedBichromaticRect`,
`frozenTrace_bichromatic_tposOf_cut_ge`, `oblivious_bichromatic_tposOf_cut_ge`) and the bichromatic
colouring criterion (`isMengerVertexCut_of_bichromaticColoring`,
`frozenTrace_bichromaticColoring_wave_cut_ge`).
-/

set_option autoImplicit false

namespace NativeRelations

open Filter Finset Transpose Transpose.Tape Transpose.Tape.Impl BoundedNesting SourceCovers
  MergeDepth MotionDepthCodes BoundedStackDepth TapeStorageRates
open scoped BigOperators Classical

/-! ## §1. Universal Bichromatic Row-to-Column Cut-Set Lemma (Lemma R) -/

/-- Input coordinates `p : Fin (d * d * b)` belonging to raw input rows `A₀ ⊆ Fin d`. -/
def inSlabCoords {d b : ℕ} (A₀ : Finset (Fin d)) : Finset (Fin (d * d * b)) :=
  (Finset.univ : Finset (Fin (d * d * b))).filter fun p => bridgeRawRow p ∈ A₀

/-- Time steps `u < T` at which `τ₀` reads an input cell in `inSlabCoords A₀`. -/
noncomputable def inSlabReadSteps {k : ℕ} (τ₀ : Trace k) (d b T : ℕ)
    (A₀ : Finset (Fin d)) : Finset ℕ :=
  (Finset.range T).filter fun u =>
    ∃ p ∈ inSlabCoords (b := b) A₀, readPos τ₀ (d * d * b) u = some p

/-- Bichromatic query rectangle `Q*(A₀, A₁)` consisting of input coordinates in rows `A₀` whose
transposed copy lies in output rows `A₁`. -/
def bichromaticRect {d b : ℕ} (A₀ A₁ : Finset (Fin d)) : Finset (Fin (d * d * b)) :=
  (Finset.univ : Finset (Fin (d * d * b))).filter fun q =>
    bridgeRawRow q ∈ A₀ ∧ bridgeOutRow q ∈ A₁

/-- Output emission root timestamps `u₀(V) = {appendTime τ₀ T (tposOf d b q).1 | q ∈ V}`. -/
noncomputable def transposedOutputRoots {k : ℕ} (τ₀ : Trace k) (d b T : ℕ)
    (V : Finset (Fin (d * d * b))) : Finset ℕ :=
  V.image fun q => appendTime τ₀ T (tposOf d b q).1

/-- Root-filtered bichromatic rectangle `Q'_Γ(A₀, A₁) = {q ∈ Q*(A₀, A₁) : u₀(q) ∉ Γ}` (
Lemma R), ensuring `LinNet.GFree Γ` blocks root-incident paths as well. -/
noncomputable def uncutRootedBichromaticRect {k : ℕ} (τ₀ : Trace k) (d b T : ℕ)
    (Γ : Finset ℕ) (A₀ A₁ : Finset (Fin d)) : Finset (Fin (d * d * b)) :=
  (bichromaticRect (b := b) A₀ A₁).filter fun q =>
    appendTime τ₀ T (tposOf d b q).1 ∉ Γ

/-- **Lemma R (`Exact Bichromatic Rectangle Cardinality`):**
`|bichromaticRect A₀ A₁| = |A₀| * |A₁| * b` for all `d, b : ℕ` and `A₀, A₁ ⊆ Fin d`. -/
theorem card_bichromaticRect {d b : ℕ} (A₀ A₁ : Finset (Fin d)) :
    (bichromaticRect (b := b) A₀ A₁).card = A₀.card * A₁.card * b := by
  apply le_antisymm (card_filter_bridgeRect_le (b := b) A₀ A₁)
  let f : Fin (d * d * b) → (Fin d × Fin d) × Fin b :=
    fun q => ((bridgeRawRow q, bridgeOutRow q), bridgeBitIdx q)
  have hbij : Function.Bijective f := by
    refine (Fintype.bijective_iff_injective_and_card f).mpr ⟨bridgeCoord_injective d b, ?_⟩
    simp [mul_assoc]
  have hsub : (A₀ ×ˢ A₁) ×ˢ (Finset.univ : Finset (Fin b)) ⊆
      (bichromaticRect (b := b) A₀ A₁).image f := by
    intro x hx
    obtain ⟨hx_pair, _⟩ := Finset.mem_product.mp hx
    obtain ⟨hx₀, hx₁⟩ := Finset.mem_product.mp hx_pair
    obtain ⟨q, hfq⟩ := hbij.2 x
    have hq₀ : bridgeRawRow q ∈ A₀ := by
      have : bridgeRawRow q = x.1.1 := congrArg (fun z => z.1.1) hfq
      rwa [this]
    have hq₁ : bridgeOutRow q ∈ A₁ := by
      have : bridgeOutRow q = x.1.2 := congrArg (fun z => z.1.2) hfq
      rwa [this]
    rw [← hfq]
    exact Finset.mem_image_of_mem f (Finset.mem_filter.mpr ⟨Finset.mem_univ q, hq₀, hq₁⟩)
  calc A₀.card * A₁.card * b
      = ((A₀ ×ˢ A₁) ×ˢ (Finset.univ : Finset (Fin b))).card := by
          simp [Finset.card_product, mul_assoc]
    _ ≤ ((bichromaticRect (b := b) A₀ A₁).image f).card := Finset.card_le_card hsub
    _ = (bichromaticRect (b := b) A₀ A₁).card :=
          Finset.card_image_of_injective _ hbij.1

private theorem getLastD_lt_of_isDepPath {k : ℕ} {work : Fin k → ℕ → ℤ} {T : ℕ} :
    ∀ (ρ : List ℕ) (t₀ : ℕ), t₀ < T → IsDepPath work T (t₀ :: ρ) →
      (t₀ :: ρ).getLastD t₀ < T
  | [], t₀, ht₀, _ => by simpa using ht₀
  | s :: σ, t₀, ht₀, hdep => by
      rw [LinNet.getLastD_cons_cons]
      exact getLastD_lt_of_isDepPath σ s ((depStep_lt hdep.1).1.trans ht₀) hdep.2

/-- **Trace-Level Root-Filtered Bichromatic Acyclicity Lemma (Lemma R core):**
For any `τ₀ : Trace k` with `(appendList τ₀ T).length = d * d * b` and any Menger vertex cut `Γ`
disconnecting `transposedOutputRoots τ₀ d b T (bichromaticRect A₀ A₁)` from
`inSlabReadSteps τ₀ d b T A₀`, the root-filtered rectangle `Q' = uncutRootedBichromaticRect` has:
1. `|A₀| * |A₁| * b ≤ |Q'| + |Γ ∩ u₀(Q*(A₀, A₁))|`,
2. every cone `coneSystem τ₀ T Γ d b (tposOf d b q)` (`q ∈ Q'`) disjoint from `inSlabCoords A₀`, and
3. `HalfRate.IsAcyclicIn (fun q => coneSystem τ₀ T Γ d b (tposOf d b q)) Q'`. -/
theorem isAcyclicIn_coneSystem_uncutRootedBichromaticRect {k d b T : ℕ} (τ₀ : Trace k)
    (hlen : (appendList τ₀ T).length = d * d * b)
    (A₀ A₁ : Finset (Fin d)) (Γ : Finset ℕ)
    (hcut : IsMengerVertexCut τ₀.work T
      (transposedOutputRoots τ₀ d b T (bichromaticRect (b := b) A₀ A₁))
      (inSlabReadSteps τ₀ d b T A₀) Γ) :
    let Q_star := bichromaticRect (b := b) A₀ A₁
    let Q_prime := uncutRootedBichromaticRect τ₀ d b T Γ A₀ A₁
    A₀.card * A₁.card * b ≤ Q_prime.card + (Γ ∩ transposedOutputRoots τ₀ d b T Q_star).card ∧
    (∀ q ∈ Q_prime, Disjoint (coneSystem τ₀ T Γ d b (tposOf d b q)) (inSlabCoords (b := b) A₀)) ∧
    HalfRate.IsAcyclicIn (fun q => coneSystem τ₀ T Γ d b (tposOf d b q)) Q_prime := by
  let Q_star := bichromaticRect (b := b) A₀ A₁
  let Q_prime := uncutRootedBichromaticRect τ₀ d b T Γ A₀ A₁
  let g : Fin (d * d * b) → ℕ := fun q => appendTime τ₀ T (tposOf d b q).1
  have hg_inj : Function.Injective g := appendTime_tposOf_injective τ₀ hlen
  let Q_hit := Q_star.filter fun q => g q ∈ Γ
  have hsub_union : Q_star ⊆ Q_prime ∪ Q_hit := by
    intro q hq
    by_cases hmem : g q ∈ Γ
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hq, hmem⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hq, hmem⟩)
  have hpart : Q_star.card ≤ Q_prime.card + Q_hit.card :=
    (Finset.card_le_card hsub_union).trans (Finset.card_union_le Q_prime Q_hit)
  have hhit_sub : Q_hit.image g ⊆ Γ ∩ transposedOutputRoots τ₀ d b T Q_star := by
    intro u hu
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨hq_star, hq_Γ⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_inter.mpr ⟨hq_Γ, Finset.mem_image_of_mem g hq_star⟩
  have hhit_le : Q_hit.card ≤ (Γ ∩ transposedOutputRoots τ₀ d b T Q_star).card := by
    rw [← Finset.card_image_of_injective Q_hit hg_inj]
    exact Finset.card_le_card hhit_sub
  have hcard_ge :
      A₀.card * A₁.card * b ≤ Q_prime.card + (Γ ∩ transposedOutputRoots τ₀ d b T Q_star).card := by
    rw [← card_bichromaticRect (b := b) A₀ A₁]
    exact hpart.trans (Nat.add_le_add_left hhit_le Q_prime.card)
  have hdisj : ∀ q ∈ Q_prime,
      Disjoint (coneSystem τ₀ T Γ d b (tposOf d b q)) (inSlabCoords (b := b) A₀) := by
    intro q hq
    rw [Finset.disjoint_left]
    intro p hp_cone hp_slab
    obtain ⟨hq_star, hq_notΓ⟩ := Finset.mem_filter.mp hq
    simp only [coneSystem, depCone, Finset.mem_filter, Finset.mem_univ, true_and] at hp_cone
    obtain ⟨ρ, hdep, hfree, hrd⟩ := hp_cone
    have htq_src : g q ∈ transposedOutputRoots τ₀ d b T Q_star :=
      Finset.mem_image_of_mem g hq_star
    have htq_lt : g q < T := by
      apply appendTime_lt τ₀ T
      rw [hlen]
      exact (tposOf d b q).2
    have hu_lt : (g q :: ρ).getLastD (g q) < T :=
      getLastD_lt_of_isDepPath ρ (g q) htq_lt hdep
    have hu_dst : (g q :: ρ).getLastD (g q) ∈ inSlabReadSteps τ₀ d b T A₀ :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hu_lt, p, hp_slab, hrd⟩
    obtain ⟨v, hv_mem, hv_Γ⟩ := hcut ρ (g q) htq_src hdep hu_dst
    rcases List.mem_cons.mp hv_mem with rfl | hv_tail
    · exact hq_notΓ hv_Γ
    · exact hfree v hv_tail hv_Γ
  have hacyc : HalfRate.IsAcyclicIn
      (fun q => coneSystem τ₀ T Γ d b (tposOf d b q)) Q_prime := by
    refine acyclicIn_of_lt_on_nbhd (φ := fun _ : Fin (d * d * b) => (0 : ℕ)) ?_
    intro v hv u hu_cone hu_prime
    have hu_slab : u ∈ inSlabCoords (b := b) A₀ := by
      obtain ⟨hu_star, _⟩ := Finset.mem_filter.mp hu_prime
      obtain ⟨_, hu_A₀, _⟩ := Finset.mem_filter.mp hu_star
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ u, hu_A₀⟩
    exact False.elim (Finset.disjoint_left.mp (hdisj v hv) hu_cone hu_slab)
  exact ⟨hcard_ge, hdisj, hacyc⟩

/-- **Lemma R (`Universal Bichromatic Row-to-Column Cut-Set Lemma`):**
For **every** machine `M : TM`, `1 ≤ d`, `TransposesAt M d c`, `2 ^ (-η * L) ≤ traceProb M L τ₀`
(`b = entryBits d`, `L = d * d * b`, `T = τ₀.haltTime`), **every** pair of row subsets
`A₀, A₁ ⊆ Fin d`, and **every** Menger vertex cut `Γ` from `u₀(Q*(A₀, A₁))` to
`inSlabReadSteps τ₀ d b T A₀`:
1. `HalfRate.IsAcyclicIn (fun q => coneSystem τ₀ T Γ d b (tposOf d b q)) (uncutRootedBichromaticRect τ₀ d b T Γ A₀ A₁)`,
2. `(|A₀| * |A₁| * b : ℝ) - η * L ≤ valueWidth M * |Γ| + |Γ ∩ u₀(Q*(A₀, A₁))|`, and
3. `((|A₀| * |A₁| * b : ℝ) - η * L) / (valueWidth M + 1) ≤ |Γ|`. -/
theorem frozenTrace_bichromatic_tposOf_cut_ge {M : TM} {c η : ℝ} {d : ℕ} (hd : 1 ≤ d)
    (htr : TransposesAt M d c) {τ₀ : Trace M.k}
    (hprob : (2 : ℝ) ^ (-η * ((d * d * entryBits d : ℕ) : ℝ)) ≤
      traceProb M (d * d * entryBits d) τ₀)
    (A₀ A₁ : Finset (Fin d)) (Γ : Finset ℕ)
    (hcut : IsMengerVertexCut τ₀.work τ₀.haltTime
      (transposedOutputRoots τ₀ d (entryBits d) τ₀.haltTime
        (bichromaticRect (b := entryBits d) A₀ A₁))
      (inSlabReadSteps τ₀ d (entryBits d) τ₀.haltTime A₀) Γ) :
    let b := entryBits d
    let L := d * d * b
    let T := τ₀.haltTime
    let Q_star := bichromaticRect (b := b) A₀ A₁
    let Q_prime := uncutRootedBichromaticRect τ₀ d b T Γ A₀ A₁
    HalfRate.IsAcyclicIn (fun q => coneSystem τ₀ T Γ d b (tposOf d b q)) Q_prime ∧
    ((A₀.card * A₁.card * b : ℕ) : ℝ) - η * (L : ℝ) ≤
      (valueWidth M : ℝ) * (Γ.card : ℝ) +
        ((Γ ∩ transposedOutputRoots τ₀ d b T Q_star).card : ℝ) ∧
    (((A₀.card * A₁.card * b : ℕ) : ℝ) - η * (L : ℝ)) / ((valueWidth M : ℝ) + 1) ≤
      (Γ.card : ℝ) := by
  let b := entryBits d
  let L := d * d * b
  let T := τ₀.haltTime
  obtain ⟨_, _, _, hlen, hdef⟩ :=
    frozenTrace_isAcyclicIn_coneSystem_deficit_le hd (le_refl (valueWidth M : ℝ)) htr hprob
  obtain ⟨hcard_ge, _, hacyc⟩ :=
    isAcyclicIn_coneSystem_uncutRootedBichromaticRect τ₀ hlen A₀ A₁ Γ hcut
  let Q_star := bichromaticRect (b := b) A₀ A₁
  let Q_prime := uncutRootedBichromaticRect τ₀ d b T Γ A₀ A₁
  have hdef_Q := hdef Γ Q_prime hacyc
  have hcard_R : ((A₀.card * A₁.card * b : ℕ) : ℝ) ≤
      (Q_prime.card : ℝ) + ((Γ ∩ transposedOutputRoots τ₀ d b T Q_star).card : ℝ) := by
    exact_mod_cast hcard_ge
  have htight : ((A₀.card * A₁.card * b : ℕ) : ℝ) - η * (L : ℝ) ≤
      (valueWidth M : ℝ) * (Γ.card : ℝ) +
        ((Γ ∩ transposedOutputRoots τ₀ d b T Q_star).card : ℝ) := by
    linarith
  have hinter_le : ((Γ ∩ transposedOutputRoots τ₀ d b T Q_star).card : ℝ) ≤ (Γ.card : ℝ) := by
    exact_mod_cast Finset.card_le_card Finset.inter_subset_left
  have hvw_pos : (0 : ℝ) < (valueWidth M : ℝ) + 1 := by
    have h2 : (2 : ℝ) ≤ (valueWidth M : ℝ) := by exact_mod_cast two_le_valueWidth M
    linarith
  have hdiv : (((A₀.card * A₁.card * b : ℕ) : ℝ) - η * (L : ℝ)) / ((valueWidth M : ℝ) + 1) ≤
      (Γ.card : ℝ) := by
    rw [div_le_iff₀ hvw_pos]
    linarith
  exact ⟨hacyc, htight, hdiv⟩

/-- **Oblivious Specialization of Lemma R (`η = 0`):**
On any `ObliviousLinTime M d (entryBits d) C T` (`1 ≤ d`), every Menger vertex cut `Γ` from
`u₀(Q*(A₀, A₁))` to `inSlabReadSteps τ₀ d (entryBits d) T A₀` (`τ₀ = traceAt M L`) satisfies
`(|A₀| * |A₁| * entryBits d : ℝ) / (valueWidth M + 1) ≤ |Γ|`. -/
theorem oblivious_bichromatic_tposOf_cut_ge {M : TM} {C : ℝ} {d T : ℕ} (hd : 1 ≤ d)
    (hobl : ObliviousLinTime M d (entryBits d) C T)
    (A₀ A₁ : Finset (Fin d)) (Γ : Finset ℕ)
    (hcut : IsMengerVertexCut (traceAt M (d * d * entryBits d)).work T
      (transposedOutputRoots (traceAt M (d * d * entryBits d)) d (entryBits d) T
        (bichromaticRect (b := entryBits d) A₀ A₁))
      (inSlabReadSteps (traceAt M (d * d * entryBits d)) d (entryBits d) T A₀) Γ) :
    (((A₀.card * A₁.card * entryBits d : ℕ) : ℝ)) / ((valueWidth M : ℝ) + 1) ≤ (Γ.card : ℝ) := by
  obtain ⟨hoblOn, hT_le, htrWithin⟩ := hobl
  let L := d * d * entryBits d
  let τ₀ : Trace M.k := traceAt M L
  have htrAt : TransposesAt M d C := by
    intro A
    obtain ⟨s, hs⟩ := htrWithin A
    obtain ⟨s', _, hhalt_s', hout_s'⟩ := (computesWithin_iff _ _).mp hs
    have hhalt_T : HaltsAt M (encode d (entryBits d) A) T :=
      hoblOn.1 _ (length_encode d (entryBits d) A)
    have hs'T : s' = T := haltsAt_unique hhalt_s' hhalt_T
    rw [hs'T] at hout_s'
    exact (computesWithin_iff _ _).mpr ⟨T, Nat.le_floor hT_le, hhalt_T, hout_s'⟩
  have hhalt_zero : HaltsAt M (List.ofFn fun _ : Fin L => false) T :=
    hoblOn.1 _ List.length_ofFn
  have hτ₀_halts : τ₀.HaltsAt T := (haltsAt_iff_trace T).mp hhalt_zero
  have hT_eq : τ₀.haltTime = T :=
    (τ₀.haltsAt_haltTime ⟨T, hτ₀_halts.2⟩).unique hτ₀_halts
  have hfib_univ : fibre M L τ₀ = Finset.univ := by
    ext X
    simp only [mem_fibre, Finset.mem_univ, iff_true]
    have hf := followsTrace_of_obliviousOn hoblOn (fun _ : Fin L => false) X
    have hhalt_X : HaltsAt M (List.ofFn X) T := hoblOn.1 _ List.length_ofFn
    funext t
    rcases lt_or_ge t T with ht | ht
    · exact hf t ht
    · have hnone1 : transAt M (List.ofFn X) t = none := transAt_of_le_of_none hhalt_X.2 ht
      have hnone2 : transAt M (List.ofFn fun _ : Fin L => false) t = none :=
        transAt_of_le_of_none hhalt_zero.2 ht
      show trace M (List.ofFn X) t = trace M (List.ofFn fun _ : Fin L => false) t
      rw [(trace_eq_none_iff t).mpr hnone1, (trace_eq_none_iff t).mpr hnone2]
  have hprob : (2 : ℝ) ^ (-(0 : ℝ) * (L : ℝ)) ≤ traceProb M L τ₀ := by
    rw [neg_zero, zero_mul, Real.rpow_zero]
    unfold traceProb
    rw [hfib_univ, Finset.card_univ]
    simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat]
    exact le_of_eq (div_self (by positivity)).symm
  have hcut' : IsMengerVertexCut τ₀.work τ₀.haltTime
      (transposedOutputRoots τ₀ d (entryBits d) τ₀.haltTime
        (bichromaticRect (b := entryBits d) A₀ A₁))
      (inSlabReadSteps τ₀ d (entryBits d) τ₀.haltTime A₀) Γ := by
    simpa only [hT_eq] using hcut
  have hres := (frozenTrace_bichromatic_tposOf_cut_ge hd htrAt hprob A₀ A₁ Γ hcut').2.2
  simpa using hres

/-! ## §2. Bichromatic Step-Colouring Cut Lemma -/

/-- State-carry `false → true` boundary steps `∂_χ` outside an active step set `W`:
`{t ∈ [1, T) \ W : t - 1 ∉ W ∧ χ t = true ∧ χ (t - 1) = false}`. -/
def stateCarryFlipSteps (T : ℕ) (W : Finset ℕ) (χ : ℕ → Bool) : Finset ℕ :=
  (Finset.Ico 1 T \ W).filter fun t => t - 1 ∉ W ∧ χ t = true ∧ χ (t - 1) = false

private theorem depPath_prefix_to_mem {k : ℕ} {xs : Fin k → ℕ → ℤ} {T : ℕ} :
    ∀ (π : List ℕ) (t₀ v : ℕ),
      IsDepPath xs T (t₀ :: π) →
      v ∈ t₀ :: π →
      ∃ ρ₁ : List ℕ,
        IsDepPath xs T (t₀ :: ρ₁) ∧
        (t₀ :: ρ₁).getLastD t₀ = v ∧
        ∀ w ∈ t₀ :: ρ₁, w ∈ t₀ :: π
  | [], t₀, v, hdep, hv => by
      simp only [List.mem_singleton] at hv
      subst hv
      exact ⟨[], hdep, rfl, fun _ hw => hw⟩
  | s :: σ, t₀, v, hdep, hv => by
      rcases List.mem_cons.mp hv with rfl | hv_tail
      · exact ⟨[], trivial, rfl, fun w hw => by
          simp only [List.mem_singleton] at hw
          subst hw
          exact List.mem_cons_self⟩
      · obtain ⟨ρ₁, hdep₁, hlast₁, hsub₁⟩ := depPath_prefix_to_mem σ s v hdep.2 hv_tail
        refine ⟨s :: ρ₁, ⟨hdep.1, hdep₁⟩, ?_, fun w hw => ?_⟩
        · rwa [LinNet.getLastD_cons_cons]
        · rcases List.mem_cons.mp hw with rfl | hw_tail
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem t₀ (hsub₁ w hw_tail)

private theorem color_true_along_depPath {k : ℕ} {xs : Fin k → ℕ → ℤ} {T : ℕ}
    {W : Finset ℕ} {χ : ℕ → Bool}
    (hBC2 : ∀ (h : Fin k) (u t : ℕ), (h, u, t) ∈ allHops xs T →
      u ∉ W → t ∉ W → χ t = true → χ u = true) :
    ∀ (π : List ℕ) (t₀ : ℕ),
      IsDepPath xs T (t₀ :: π) →
      (∀ v ∈ t₀ :: π, v ∉ W) →
      (∀ v ∈ t₀ :: π, v ∉ stateCarryFlipSteps T W χ) →
      χ t₀ = true →
      χ ((t₀ :: π).getLastD t₀) = true
  | [], t₀, _, _, _, hχ₀ => by simpa using hχ₀
  | s :: σ, t₀, hdep, hnoW, hnoFlip, hχ₀ => by
      have ht₀_noW : t₀ ∉ W := hnoW t₀ List.mem_cons_self
      have hs_noW : s ∉ W := hnoW s (List.mem_cons_of_mem t₀ List.mem_cons_self)
      have ht₀_noFlip : t₀ ∉ stateCarryFlipSteps T W χ := hnoFlip t₀ List.mem_cons_self
      have hχ_s : χ s = true := by
        rcases hdep.1 with ⟨hpred, ht₀_lt⟩ | hhop_img
        · have hs_eq : s = t₀ - 1 := by omega
          have ht₀_ge1 : 1 ≤ t₀ := by omega
          by_contra hns
          have hχs_false : χ s = false := Bool.eq_false_iff.mpr hns
          have hmem_flip : t₀ ∈ stateCarryFlipSteps T W χ := by
            refine Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr
              ⟨Finset.mem_Ico.mpr ⟨ht₀_ge1, ht₀_lt⟩, ht₀_noW⟩, ?_, hχ₀, ?_⟩
            · rwa [← hs_eq]
            · rwa [← hs_eq]
          exact ht₀_noFlip hmem_flip
        · obtain ⟨⟨h, u, t⟩, hmem_all, hpair_eq⟩ := Finset.mem_image.mp hhop_img
          dsimp at hpair_eq
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair_eq
          exact hBC2 h u t hmem_all hs_noW ht₀_noW hχ₀
      rw [LinNet.getLastD_cons_cons]
      exact color_true_along_depPath hBC2 σ s hdep.2
        (fun v hv => hnoW v (List.mem_cons_of_mem t₀ hv))
        (fun v hv => hnoFlip v (List.mem_cons_of_mem t₀ hv)) hχ_s

private theorem getLastD_mem_cons_list : ∀ (t : ℕ) (ρ : List ℕ), (t :: ρ).getLastD t ∈ t :: ρ
  | t, [] => by simp
  | t, s :: σ => by
      rw [LinNet.getLastD_cons_cons]
      exact List.mem_cons_of_mem t (getLastD_mem_cons_list s σ)

/-- **Colouring Lemma of Theorem 7.2:**
Suppose `Src ⊆ U_sup`, `B` is a Menger vertex cut from `U_sup` to `W`, and `χ : ℕ → Bool` satisfies:
- `(BC1)` `∀ u ∈ Dst \ W, χ u = false` and `∀ t ∈ Src \ W, χ t = true`,
- `(BC2)` `∀ (h, u, t) ∈ allHops xs T`, if `u ∉ W` and `t ∉ W`, then `χ t = true → χ u = true`.
Then `B ∪ stateCarryFlipSteps T W χ` is a Menger vertex cut from `Src` to `Dst`. -/
theorem isMengerVertexCut_of_bichromaticColoring {k : ℕ} (xs : Fin k → ℕ → ℤ) (T : ℕ)
    {Src Dst U_sup W B : Finset ℕ} (χ : ℕ → Bool)
    (hSrc : Src ⊆ U_sup)
    (hBC1_dst : ∀ u ∈ Dst \ W, χ u = false)
    (hBC1_src : ∀ t ∈ Src \ W, χ t = true)
    (hBC2 : ∀ (h : Fin k) (u t : ℕ), (h, u, t) ∈ allHops xs T →
      u ∉ W → t ∉ W → χ t = true → χ u = true)
    (hcut_W : IsMengerVertexCut xs T U_sup W B) :
    IsMengerVertexCut xs T Src Dst (B ∪ stateCarryFlipSteps T W χ) := by
  intro π t₀ ht₀_src hdep hlast_dst
  by_contra hno_hit
  push Not at hno_hit
  have hno_B : ∀ v ∈ t₀ :: π, v ∉ B :=
    fun v hv hvB => hno_hit v hv (Finset.mem_union_left _ hvB)
  have hno_flip : ∀ v ∈ t₀ :: π, v ∉ stateCarryFlipSteps T W χ :=
    fun v hv hvF => hno_hit v hv (Finset.mem_union_right _ hvF)
  have hno_W : ∀ v ∈ t₀ :: π, v ∉ W := by
    intro v hv hvW
    obtain ⟨ρ₁, hdep₁, hlast₁, hsub₁⟩ := depPath_prefix_to_mem π t₀ v hdep hv
    have hv_dst : (t₀ :: ρ₁).getLastD t₀ ∈ W := hlast₁ ▸ hvW
    obtain ⟨w, hw_mem₁, hw_B⟩ := hcut_W ρ₁ t₀ (hSrc ht₀_src) hdep₁ hv_dst
    exact hno_B w (hsub₁ w hw_mem₁) hw_B
  have ht₀_srcW : t₀ ∈ Src \ W := Finset.mem_sdiff.mpr ⟨ht₀_src, hno_W t₀ List.mem_cons_self⟩
  have hlast_mem : (t₀ :: π).getLastD t₀ ∈ t₀ :: π := getLastD_mem_cons_list t₀ π
  have hlast_dstW : (t₀ :: π).getLastD t₀ ∈ Dst \ W :=
    Finset.mem_sdiff.mpr ⟨hlast_dst, hno_W _ hlast_mem⟩
  have htrue : χ ((t₀ :: π).getLastD t₀) = true :=
    color_true_along_depPath hBC2 π t₀ hdep hno_W hno_flip (hBC1_src t₀ ht₀_srcW)
  have hfalse : χ ((t₀ :: π).getLastD t₀) = false := hBC1_dst _ hlast_dstW
  rw [htrue] at hfalse
  exact Bool.noConfusion hfalse

/-- **Theorem 7.2 (`Bichromatic Colouring Active-Set Menger Lower Bound`):**
Combining `isMengerVertexCut_of_bichromaticColoring` with `frozenTrace_bichromatic_tposOf_cut_ge`,
on any `2 ^ (-η * L)`-heavy trace `τ₀` of `TransposesAt M d c` (`1 ≤ d`, `b = entryBits d`), if a
binary colouring `χ : ℕ → Bool` satisfies `(BC1)` and `(BC2)` for `(A₀, A₁)` outside `W`, then
every Menger vertex cut `B` from `u₀(univ)` to `W` satisfies
`((|A₀| * |A₁| * b : ℝ) - η * L) / (valueWidth M + 1) - |(stateCarryFlipSteps T W χ)| ≤ |B|`. -/
theorem frozenTrace_bichromaticColoring_wave_cut_ge {M : TM} {c η : ℝ} {d : ℕ} (hd : 1 ≤ d)
    (htr : TransposesAt M d c) {τ₀ : Trace M.k}
    (hprob : (2 : ℝ) ^ (-η * ((d * d * entryBits d : ℕ) : ℝ)) ≤
      traceProb M (d * d * entryBits d) τ₀)
    (A₀ A₁ : Finset (Fin d)) (W B : Finset ℕ) (χ : ℕ → Bool)
    (hBC1_in : ∀ u ∈ inSlabReadSteps τ₀ d (entryBits d) τ₀.haltTime A₀ \ W, χ u = false)
    (hBC1_out : ∀ t ∈ transposedOutputRoots τ₀ d (entryBits d) τ₀.haltTime
      (bichromaticRect (b := entryBits d) A₀ A₁) \ W, χ t = true)
    (hBC2 : ∀ (h : Fin M.k) (u t : ℕ), (h, u, t) ∈ allHops τ₀.work τ₀.haltTime →
      u ∉ W → t ∉ W → χ t = true → χ u = true)
    (hcut_W : IsMengerVertexCut τ₀.work τ₀.haltTime
      (transposedOutputRoots τ₀ d (entryBits d) τ₀.haltTime Finset.univ) W B) :
    let b := entryBits d
    let L := d * d * b
    let T := τ₀.haltTime
    (((A₀.card * A₁.card * b : ℕ) : ℝ) - η * (L : ℝ)) / ((valueWidth M : ℝ) + 1) -
      ((stateCarryFlipSteps T W χ).card : ℝ) ≤ (B.card : ℝ) := by
  let b := entryBits d
  let T := τ₀.haltTime
  have hSrc_sub :
      transposedOutputRoots τ₀ d b T (bichromaticRect (b := b) A₀ A₁) ⊆
        transposedOutputRoots τ₀ d b T Finset.univ :=
    Finset.image_subset_image (Finset.subset_univ _)
  have hcut_tot : IsMengerVertexCut τ₀.work T
      (transposedOutputRoots τ₀ d b T (bichromaticRect (b := b) A₀ A₁))
      (inSlabReadSteps τ₀ d b T A₀)
      (B ∪ stateCarryFlipSteps T W χ) :=
    isMengerVertexCut_of_bichromaticColoring τ₀.work T χ hSrc_sub hBC1_in hBC1_out hBC2 hcut_W
  have htot :=
    (frozenTrace_bichromatic_tposOf_cut_ge hd htr hprob A₀ A₁
      (B ∪ stateCarryFlipSteps T W χ) hcut_tot).2.2
  have hunion_le : ((B ∪ stateCarryFlipSteps T W χ).card : ℝ) ≤
      (B.card : ℝ) + ((stateCarryFlipSteps T W χ).card : ℝ) := by
    exact_mod_cast Finset.card_union_le B (stateCarryFlipSteps T W χ)
  linarith

end NativeRelations
