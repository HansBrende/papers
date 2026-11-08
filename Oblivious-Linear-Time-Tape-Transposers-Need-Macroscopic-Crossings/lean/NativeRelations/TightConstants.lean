import NativeRelations.TranspositionCut
import LeanMachine.ThresholdRefinement

/-!
# Polynomial Time Pullback, Genie-Free Bridge, and Tower-Free Macroscopic Crossings

Replaces the uniform block-ranking cut by a single interval of the common refinement of all chain
thresholds (`exists_commonRefinement_cell_core`, `timePullback_commonRefinement_mais_tight`),
counts valid phase-exit chains and single-cell guards sharply (`sharpFamCount`,
`sharpCellGuardThresh`), and proves the genie-free `coneSystem` bridge
(`exists_singleCell_guard_coneSystem_isIndependent_crossingLowerGT2H`), Theorem D
(`linearTimeTrace_crossingLowerGT2H_cone_menger_dichotomy_tight`), Theorem X
(`obliviousLinTime_macroscopicCrossingLowers_menger_lb_tight`), Theorem S
(`obliviousLinTime_reduces_to_crossingCapableSkeleton_and_singleLeg_tight`), and Theorem E
(`frozenTrace_macroscopicCrossingLowers_menger_lb_tight`, `simulator_heavyTrace_expansion_and_skeleton_tight`).
-/

set_option autoImplicit false

namespace NativeRelations

open Filter Finset Transpose Transpose.Tape Transpose.Tape.Impl BoundedNesting SourceCovers
  MergeDepth MotionDepthCodes BoundedStackDepth TapeStorageRates
open scoped BigOperators Classical

/-! ## §1. Sharpness Falsification for Abstract `(a, e)` Set-Pair Cuts -/

section AbstractSetPairSharpness

/-- Complete Johnson family `{S ⊆ Fin (a + e) : |S| = a}` of cardinality `Nat.choose (a + e) a`. -/
def johnsonFamily (a e : ℕ) : Finset (Finset (Fin (a + e))) :=
  (univ : Finset (Finset (Fin (a + e)))).filter fun S => S.card = a

/-- Canonical bidirected set-pair conflict neighborhood `N(S) = {T ∈ johnsonFamily a e : (S ∩ (univ \ T)).Nonempty}`. -/
def johnsonPairNbhd (a e : ℕ) (S : Finset (Fin (a + e))) : Finset (Finset (Fin (a + e))) :=
  (johnsonFamily a e).filter fun T => (S ∩ (univ \ T)).Nonempty

/-- **Sharpness of `Nat.choose (a + e) a⁻¹` for Abstract Set-Pair Cuts:**
On `V := johnsonFamily a e` (`|V| = Nat.choose (a + e) a`), setting `A_blk S := S` and
`E_blk S := univ \ S` satisfies `Disjoint (A_blk S) (E_blk S)`, `|A_blk S| = a`, and `|E_blk S| = e`
for every `S ∈ V`, yet **every** subset `U ⊆ V` satisfying `HalfRate.IsAcyclicIn (johnsonPairNbhd a e) U`
has `U.card ≤ 1` (`because every distinct pair S ≠ T in V forms a directed 2-cycle`). -/
theorem johnsonSetPair_isAcyclicIn_card_le_one (a e : ℕ) :
    (∀ S ∈ johnsonFamily a e,
      Disjoint S ((univ : Finset (Fin (a + e))) \ S) ∧
      S.card = a ∧
      ((univ : Finset (Fin (a + e))) \ S).card = e) ∧
    ∀ U ⊆ johnsonFamily a e,
      HalfRate.IsAcyclicIn (johnsonPairNbhd a e) U → U.card ≤ 1 := by
  refine ⟨fun S hS => ?_, fun U hUV hacyc => ?_⟩
  · have hScard : S.card = a := (mem_filter.mp hS).2
    refine ⟨disjoint_sdiff, hScard, ?_⟩
    have hadd := card_sdiff_add_card_inter (univ : Finset (Fin (a + e))) S
    rw [univ_inter, card_univ, Fintype.card_fin, hScard] at hadd
    omega
  · by_contra hgt1
    push Not at hgt1
    obtain ⟨S₁, hS₁, S₂, hS₂, hne⟩ := one_lt_card.mp hgt1
    have hS₁J : S₁ ∈ johnsonFamily a e := hUV hS₁
    have hS₂J : S₂ ∈ johnsonFamily a e := hUV hS₂
    have hc₁ : S₁.card = a := (mem_filter.mp hS₁J).2
    have hc₂ : S₂.card = a := (mem_filter.mp hS₂J).2
    have hedge : ∀ {X Y : Finset (Fin (a + e))},
        X ∈ johnsonFamily a e → Y ∈ johnsonFamily a e → X ≠ Y → Y ∈ johnsonPairNbhd a e X := by
      intro X Y hXJ hYJ hXY
      have hcX : X.card = a := (mem_filter.mp hXJ).2
      have hcY : Y.card = a := (mem_filter.mp hYJ).2
      have hnsub : ¬ (X ⊆ Y) := fun hsub =>
        hXY (eq_of_subset_of_card_le hsub (by omega))
      obtain ⟨x, hxX, hxY⟩ := not_subset.mp hnsub
      exact mem_filter.mpr ⟨hYJ, ⟨x, mem_inter.mpr ⟨hxX, mem_sdiff.mpr ⟨mem_univ x, hxY⟩⟩⟩⟩
    have h12 : S₂ ∈ johnsonPairNbhd a e S₁ := hedge hS₁J hS₂J hne
    have h21 : S₁ ∈ johnsonPairNbhd a e S₂ := hedge hS₂J hS₁J hne.symm
    have hpair_sub : ({S₁, S₂} : Finset (Finset (Fin (a + e)))) ⊆ U :=
      insert_subset hS₁ (singleton_subset_iff.mpr hS₂)
    obtain ⟨W, hW_mem, hW_src⟩ := hacyc {S₁, S₂} hpair_sub (insert_nonempty S₁ {S₂})
    rcases mem_insert.mp hW_mem with rfl | hW2
    · exact hW_src S₂ h12 (mem_insert_of_mem (mem_singleton_self S₂))
    · rw [mem_singleton.mp hW2] at hW_src
      exact hW_src S₁ h21 (mem_insert_self S₁ {S₂})

end AbstractSetPairSharpness

/-! ## §2. Theorem 5.1 (time pullback) via 1D Timestamp Common Refinement -/

section TightCommonRefinementPullback

/-- Unconditional chronological block coverage (`removing B_time ≤ T` completely from `d₀`!):
for **every** `1 ≤ B_time` and `t < T`, `t` belongs to some `timeBlock T B_time β`. -/
theorem exists_mem_timeBlock_uncond {T B_time t : ℕ} (hB : 1 ≤ B_time) (ht : t < T) :
    ∃ β : Fin B_time, t ∈ timeBlock T B_time β := by
  rcases le_or_gt B_time T with hBT | hlt
  · exact exists_mem_timeBlock hB hBT ht
  · have hdiv0 : T / B_time = 0 := Nat.div_eq_zero_iff.mpr (Or.inr hlt)
    let β : Fin B_time := ⟨B_time - 1, by omega⟩
    refine ⟨β, mem_Ico.mpr ⟨?_, ?_⟩⟩
    · unfold timeBlockLo
      rw [hdiv0, Nat.mul_zero]
      exact Nat.zero_le t
    · unfold timeBlockHi
      dsimp only [β]
      have hnlt : ¬ (B_time - 1 + 1 < B_time) := by omega
      simp only [hnlt, ↓reduceIte]
      exact ht

/-- Any subset `U` with zero internal arcs (`∀ q ∈ U, ∀ p ∈ U, p ∉ N q`) is both
`DirectedRecovery.IsIndependent` and `HalfRate.IsAcyclicIn`. -/
theorem isIndependent_and_isAcyclicIn_of_noArcs {V : Type*} {N : V → Finset V} {U : Finset V}
    (hno : ∀ q ∈ U, ∀ p ∈ U, p ∉ N q) :
    DirectedRecovery.IsIndependent N U ∧ HalfRate.IsAcyclicIn N U := by
  refine ⟨fun q hq p hpN hpU => hno q hq p hpU hpN, fun S hSU ⟨v, hvS⟩ => ?_⟩
  exact ⟨v, hvS, fun u huv huS => hno v (hSU hvS) u (hSU huS) huv⟩

/-- **Common-Refinement Cell Extraction Core (`Step 1 of Tight Theorem 5.1 (time pullback)`):**
Given any threshold set `S_ref ⊆ [0, T]` containing `0` and `T` (`S_ref.card ≤ N_cells + 1`) and
any `ι`-indexed family (`|ι| ≤ m_fam`) of monotone sequences `ξ ν` whose clamped thresholds
`min T (ξ ν s)` (`s ≤ B_time`) lie in `S_ref`, there exists **one single common-refinement interval
`[a_*, b_*) ⊆ [0, T)`** (`with no element of S_ref strictly inside (a_*, b_*)`) and a self-collision-free
subset `U_* ⊆ V₀ \ Z_bad` of outputs `u₀(q) ∈ [a_*, b_*)` satisfying:
1. `V₀.card ≤ N_cells * U_*.card + Z_bad.card + m_fam * (T / B_time) + m_fam * (2 * B_time + 2) * (d * b)`,
2. constant backward block set `A_blk q = A_blk p` across `q, p ∈ U_*`, and
3. `Disjoint (A_blk q) (E_blk q)` for every `q ∈ U_*`! -/
theorem exists_commonRefinement_cell_core {ι : Type*} [Fintype ι] [DecidableEq ι]
    {k T d b B_time m_fam N_cells : ℕ} (τ₀ : Trace k)
    (hd : 1 ≤ d) (hb : 1 ≤ b) (hB : 1 ≤ B_time)
    (hι : Fintype.card ι ≤ m_fam)
    (hlen : (appendList τ₀ T).length = d * d * b)
    (V₀ Z_bad : Finset (Fin (d * d * b)))
    (S_ref : Finset ℕ) (h0_ref : 0 ∈ S_ref) (hT_ref : T ∈ S_ref)
    (hS_le_T : ∀ x ∈ S_ref, x ≤ T)
    (hS_card : S_ref.card ≤ N_cells + 1)
    (ξ : ι → ℕ → ℕ)
    (hξ_mono : ∀ ν : ι, ∀ s₁ s₂ : ℕ, s₁ ≤ s₂ → s₂ ≤ B_time → ξ ν s₁ ≤ ξ ν s₂)
    (hξ_ref : ∀ ν : ι, ∀ s : ℕ, s ≤ B_time → min T (ξ ν s) ∈ S_ref)
    (π_perm : ι → Fin B_time → Fin B_time)
    (hπ_inj : ∀ ν : ι, Function.Injective (π_perm ν)) :
    let L := d * d * b
    let u₀_of : Fin L → ℕ := fun q => appendTime τ₀ T (tposOf d b q).1
    let A_blk : Fin L → Finset (Fin B_time) := fun q =>
      (univ : Finset (Fin B_time)).filter fun β =>
        ∃ ν : ι, u₀_of q ∈ Ico (ξ ν (π_perm ν β).1) (ξ ν ((π_perm ν β).1 + 1))
    let E_blk : Fin L → Finset (Fin B_time) := fun q =>
      (univ : Finset (Fin B_time)).filter fun β =>
        ∃ t ∈ timeBlock T B_time β, τ₀.input t = (q.1 : ℤ)
    ∃ (a_star b_star : ℕ) (U_star : Finset (Fin L)),
      a_star < b_star ∧ b_star ≤ T ∧
      a_star ∈ S_ref ∧ b_star ∈ S_ref ∧
      (∀ x ∈ S_ref, ¬ (a_star < x ∧ x < b_star)) ∧
      U_star ⊆ V₀ \ Z_bad ∧
      (∀ q ∈ U_star, u₀_of q ∈ Ico a_star b_star) ∧
      (∀ q ∈ U_star, Disjoint (A_blk q) (E_blk q)) ∧
      (∀ q ∈ U_star, ∀ p ∈ U_star, A_blk q = A_blk p) ∧
      V₀.card ≤ N_cells * U_star.card + Z_bad.card +
        m_fam * (T / B_time) + m_fam * (2 * B_time + 2) * (d * b) := by
  intro L u₀_of A_blk E_blk
  have hL_pos : 1 ≤ L := Nat.mul_pos (Nat.mul_pos hd hd) hb
  have hu₀_lt_T : ∀ q : Fin L, u₀_of q < T :=
    fun q => appendTime_lt τ₀ T (by rw [hlen]; exact (tposOf d b q).2)
  have hT_pos : 1 ≤ T := by
    have := hu₀_lt_T ⟨0, hL_pos⟩
    omega
  let CollOf : ι → Finset (Fin L) := fun ν =>
    (univ : Finset (Fin L)).filter fun q =>
      ∃ β : Fin B_time,
        u₀_of q ∈ Ico (ξ ν (π_perm ν β).1) (ξ ν ((π_perm ν β).1 + 1)) ∧
        ∃ t ∈ timeBlock T B_time β, τ₀.input t = (q.1 : ℤ)
  let Coll : Finset (Fin L) := (univ : Finset ι).biUnion CollOf
  have hColl_card : Coll.card ≤ m_fam * (T / B_time) + m_fam * (2 * B_time + 2) * (d * b) := by
    calc Coll.card
        ≤ ∑ ν : ι, (CollOf ν).card := card_biUnion_le
      _ ≤ ∑ _ν : ι, (T / B_time + (2 * B_time + 2) * (d * b)) :=
          sum_le_sum fun ν _ => card_selfCollisions_singleFamily_le τ₀ hd hb hB hlen
            (ξ ν) (hξ_mono ν) (π_perm ν) (hπ_inj ν)
      _ = Fintype.card ι * (T / B_time + (2 * B_time + 2) * (d * b)) := by simp
      _ ≤ m_fam * (T / B_time + (2 * B_time + 2) * (d * b)) :=
          Nat.mul_le_mul_right _ hι
      _ = m_fam * (T / B_time) + m_fam * (2 * B_time + 2) * (d * b) := by ring
  let Q_clean : Finset (Fin L) := (V₀ \ Z_bad) \ Coll
  have hQ_disj : ∀ q ∈ Q_clean, Disjoint (A_blk q) (E_blk q) := by
    intro q hq
    have hnotC : q ∉ Coll := (mem_sdiff.mp hq).2
    refine disjoint_left.mpr fun β hA hE => hnotC ?_
    obtain ⟨_, ν, hmem_ico⟩ := mem_filter.mp hA
    obtain ⟨_, t, ht_blk, hxt⟩ := mem_filter.mp hE
    exact mem_biUnion.mpr ⟨ν, mem_univ ν, mem_filter.mpr ⟨mem_univ q, β, hmem_ico, t, ht_blk, hxt⟩⟩
  have hV₀_decomp : V₀.card ≤ Q_clean.card + Z_bad.card + Coll.card := by
    have hcov : V₀ ⊆ Q_clean ∪ (Z_bad ∪ Coll) := by
      intro q hq
      by_cases hZ : q ∈ Z_bad
      · exact mem_union_right _ (mem_union_left _ hZ)
      · by_cases hC : q ∈ Coll
        · exact mem_union_right _ (mem_union_right _ hC)
        · exact mem_union_left _ (mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨hq, hZ⟩, hC⟩)
    calc V₀.card
        ≤ (Q_clean ∪ (Z_bad ∪ Coll)).card := card_le_card hcov
      _ ≤ Q_clean.card + (Z_bad ∪ Coll).card := card_union_le _ _
      _ ≤ Q_clean.card + (Z_bad.card + Coll.card) := Nat.add_le_add_left (card_union_le _ _) _
      _ = Q_clean.card + Z_bad.card + Coll.card := by omega
  obtain ⟨a_star, b_star, hab_lt, hb_le_T, ha_mem, hb_mem, hno_inner, hQ_le_max, hlt_iff_cell⟩ :=
    LeanMachine.ThresholdRefinement.exists_refinement_cell hT_pos S_ref h0_ref hT_ref hS_le_T
      hS_card Q_clean u₀_of (fun q _ => hu₀_lt_T q)
  let U_star := Q_clean.filter fun q => u₀_of q ∈ Ico a_star b_star
  change Q_clean.card ≤ N_cells * U_star.card at hQ_le_max
  have hA_eq : ∀ q ∈ U_star, ∀ p ∈ U_star, A_blk q = A_blk p := by
    intro q hq p hp
    have huq : u₀_of q ∈ Ico a_star b_star := (mem_filter.mp hq).2
    have hup : u₀_of p ∈ Ico a_star b_star := (mem_filter.mp hp).2
    ext β
    simp only [A_blk, mem_filter, mem_univ, true_and, mem_Ico]
    refine exists_congr fun ν => ?_
    have hlo_iff := hlt_iff_cell huq hup (ξ ν (π_perm ν β).1)
      (hξ_ref ν (π_perm ν β).1 (le_of_lt (π_perm ν β).2))
    have hhi_iff := hlt_iff_cell huq hup (ξ ν ((π_perm ν β).1 + 1))
      (hξ_ref ν ((π_perm ν β).1 + 1) (Nat.succ_le_of_lt (π_perm ν β).2))
    omega
  refine ⟨a_star, b_star, U_star, hab_lt, hb_le_T, ha_mem, hb_mem, hno_inner,
    (filter_subset _ Q_clean).trans sdiff_subset,
    fun q hq => (mem_filter.mp hq).2,
    fun q hq => hQ_disj q (mem_filter.mp hq).1,
    hA_eq, ?_⟩
  omega

/-- Time-block count `⌈2 * m₀ * C / α⌉₊` for Theorem 5.1 (time pullback). -/
noncomputable def tightBtime (m₀ : ℕ) (C α : ℝ) : ℕ :=
  ⌈2 * (m₀ : ℝ) * C / α⌉₊

/-- Common-refinement cell cap `m₀ * (tightBtime m₀ C α + 1) + 1` for general `ι` (`|ι| ≤ m₀`). -/
noncomputable def tightRefCells (m₀ : ℕ) (C α : ℝ) : ℕ :=
  m₀ * (tightBtime m₀ C α + 1) + 1

/-- Explicit `(m₀, C, α)`-only dimension threshold for Theorem 5.1 (time pullback) (`with |Z_bad| ≤ |V₀| / 12`,
dropping `K_row * B_time` completely!). -/
noncomputable def tightTimePullback_d0 (m₀ : ℕ) (C α : ℝ) : ℕ :=
  ⌈12 * (m₀ : ℝ) * (2 * (tightBtime m₀ C α : ℝ) + 2) / α + 6⌉₊

/-- **Tightened Theorem 5.1 (time pullback) Density Constant `tightTimePullbackRhoMin m₀ C α`:**
`1 / (3 * (m₀ * (⌈2 * m₀ * C / α⌉₊ + 1) + 1)) = Ω(α / (m₀² * C))`, replacing the exponential
binomial `1 / (3 * C(m₀ + 2⌈24C/α⌉₊, m₀))`! -/
noncomputable def tightTimePullbackRhoMin (m₀ : ℕ) (C α : ℝ) : ℝ :=
  1 / (3 * (tightRefCells m₀ C α : ℝ))

/-- **Tightened General-`Z_bad` Theorem 5.1 (time pullback):**
With the **exact same hypotheses** as `timePullback_blockCut_mais` (`except replacing B_time = ⌈8 m₀ C / α⌉₊`
by `tightBtime m₀ C α = ⌈2 m₀ C / α⌉₊` and `timePullback_gen_d0` by the strictly smaller `tightTimePullback_d0`),
produces `U ⊆ V₀` that is **both `DirectedRecovery.IsIndependent` and `HalfRate.IsAcyclicIn`** in
`ballAvoidSystem τ₀ T D B d b` of size `|U| ≥ tightTimePullbackRhoMin m₀ C α * |V₀|`! -/
theorem timePullback_commonRefinement_mais_tight {ι : Type*} [Fintype ι] [DecidableEq ι]
    {k T d b D m₀ : ℕ} {C α : ℝ} (τ₀ : Trace k)
    (hd : 1 ≤ d) (hb : 1 ≤ b) (hm₀ : 1 ≤ m₀) (hC : 1 ≤ C) (hα0 : 0 < α)
    (hι : Fintype.card ι ≤ m₀)
    (hlen : (appendList τ₀ T).length = d * d * b)
    (hT : (T : ℝ) ≤ C * (((d * d * b : ℕ) : ℝ) + 1))
    (V₀ Z_bad : Finset (Fin (d * d * b))) (B : Finset ℕ)
    (hV₀ : α * ((d * d * b : ℕ) : ℝ) ≤ (V₀.card : ℝ))
    (hZ_bad : (Z_bad.card : ℝ) ≤ (V₀.card : ℝ) / 12)
    (hd_thresh : tightTimePullback_d0 m₀ C α ≤ d)
    (ξ : ι → ℕ → ℕ)
    (hξ_mono : ∀ ν : ι, ∀ s₁ s₂ : ℕ, s₁ ≤ s₂ → s₂ ≤ tightBtime m₀ C α → ξ ν s₁ ≤ ξ ν s₂)
    (π_perm : ι → Fin (tightBtime m₀ C α) → Fin (tightBtime m₀ C α))
    (hπ_inj : ∀ ν : ι, Function.Injective (π_perm ν))
    (hpull : ∀ q ∈ V₀ \ Z_bad, ∀ p ∈ V₀, ∀ ρ : List ℕ,
      ρ.length ≤ D →
      IsDepPath τ₀.work T (appendTime τ₀ T (tposOf d b q).1 :: ρ) →
      LinNet.GFree B (appendTime τ₀ T (tposOf d b q).1 :: ρ) →
      τ₀.input ((appendTime τ₀ T (tposOf d b q).1 :: ρ).getLastD
        (appendTime τ₀ T (tposOf d b q).1)) = (p.1 : ℤ) →
      ∀ β : Fin (tightBtime m₀ C α),
        (appendTime τ₀ T (tposOf d b q).1 :: ρ).getLastD
          (appendTime τ₀ T (tposOf d b q).1) ∈ timeBlock T (tightBtime m₀ C α) β →
        ∃ ν : ι, appendTime τ₀ T (tposOf d b q).1 ∈
          Ico (ξ ν (π_perm ν β).1) (ξ ν ((π_perm ν β).1 + 1))) :
    ∃ U : Finset (Fin (d * d * b)),
      U ⊆ V₀ ∧
      DirectedRecovery.IsIndependent (ballAvoidSystem τ₀ T D B d b) U ∧
      HalfRate.IsAcyclicIn (ballAvoidSystem τ₀ T D B d b) U ∧
      tightTimePullbackRhoMin m₀ C α * (V₀.card : ℝ) ≤ (U.card : ℝ) := by
  let B_time := tightBtime m₀ C α
  let N_cells := tightRefCells m₀ C α
  let W := d * b
  let L := d * d * b
  have hm₀_r : (1 : ℝ) ≤ (m₀ : ℝ) := by exact_mod_cast hm₀
  have hB_pos : 1 ≤ B_time := by
    change 1 ≤ ⌈2 * (m₀ : ℝ) * C / α⌉₊
    exact Nat.ceil_pos.mpr (by positivity)
  let S_ref : Finset ℕ :=
    insert 0 (insert T ((univ : Finset ι).biUnion fun ν =>
      (range (B_time + 1)).image fun s => min T (ξ ν s)))
  have h0_ref : 0 ∈ S_ref := mem_insert_self 0 _
  have hT_ref : T ∈ S_ref := mem_insert_of_mem (mem_insert_self T _)
  have hS_le_T : ∀ x ∈ S_ref, x ≤ T := by
    intro x hx
    rcases mem_insert.mp hx with rfl | hx1
    · omega
    · rcases mem_insert.mp hx1 with rfl | hx2
      · exact le_rfl
      · obtain ⟨ν, _, hx3⟩ := mem_biUnion.mp hx2
        obtain ⟨s, _, rfl⟩ := mem_image.mp hx3
        exact Nat.min_le_left T _
  have hS_card : S_ref.card ≤ N_cells + 1 := by
    have hbi : (((univ : Finset ι).biUnion fun ν =>
        (range (B_time + 1)).image fun s => min T (ξ ν s))).card ≤ m₀ * (B_time + 1) := by
      calc (((univ : Finset ι).biUnion fun ν =>
            (range (B_time + 1)).image fun s => min T (ξ ν s))).card
          ≤ ∑ ν : ι, ((range (B_time + 1)).image fun s => min T (ξ ν s)).card := card_biUnion_le
        _ ≤ ∑ _ν : ι, (B_time + 1) :=
            sum_le_sum fun ν _ => card_image_le.trans (by simp)
        _ = Fintype.card ι * (B_time + 1) := by simp
        _ ≤ m₀ * (B_time + 1) := Nat.mul_le_mul_right _ hι
    have h1 := card_insert_le 0 (insert T ((univ : Finset ι).biUnion fun ν =>
      (range (B_time + 1)).image fun s => min T (ξ ν s)))
    have h2 := card_insert_le T ((univ : Finset ι).biUnion fun ν =>
      (range (B_time + 1)).image fun s => min T (ξ ν s))
    change S_ref.card ≤ (m₀ * (B_time + 1) + 1) + 1
    dsimp only [S_ref]
    omega
  have hξ_ref : ∀ ν : ι, ∀ s : ℕ, s ≤ B_time → min T (ξ ν s) ∈ S_ref := by
    intro ν s hs
    exact mem_insert_of_mem (mem_insert_of_mem
      (mem_biUnion.mpr ⟨ν, mem_univ ν, mem_image_of_mem _ (mem_range.mpr (by omega))⟩))
  obtain ⟨a_star, b_star, U_star, _, _, _, _, _, hU_sub, _, hU_disj, hA_eq, hV_nat⟩ :=
    exists_commonRefinement_cell_core τ₀ hd hb hB_pos hι hlen V₀ Z_bad S_ref
      h0_ref hT_ref hS_le_T hS_card ξ hξ_mono hξ_ref π_perm hπ_inj
  -- Prove zero internal arcs in `ballAvoidSystem τ₀ T D B d b` on `U_star`.
  have hlast_lt_T : ∀ (ρ : List ℕ) (u₀ : ℕ), u₀ < T → IsDepPath τ₀.work T (u₀ :: ρ) →
      (u₀ :: ρ).getLastD u₀ < T := by
    intro ρ
    induction ρ with
    | nil => intro u₀ hu₀ _; exact hu₀
    | cons u₁ ρ' ih =>
      intro u₀ _ ⟨hstep, htail⟩
      rw [LinNet.getLastD_cons_cons]
      exact ih u₁ (lt_trans (depStep_lt hstep).1 (depStep_lt hstep).2) htail
  let A_blk : Fin L → Finset (Fin B_time) := fun q =>
    (univ : Finset (Fin B_time)).filter fun β' =>
      ∃ ν' : ι, appendTime τ₀ T (tposOf d b q).1 ∈
        Ico (ξ ν' (π_perm ν' β').1) (ξ ν' ((π_perm ν' β').1 + 1))
  have hno_arcs : ∀ q ∈ U_star, ∀ p ∈ U_star, p ∉ ballAvoidSystem τ₀ T D B d b q := by
    intro q hq p hp hp_mem
    unfold ballAvoidSystem at hp_mem
    obtain ⟨_, ρ, hdep, hfreeB, hrd, hlen_ρ⟩ := mem_filter.mp hp_mem
    let u₀_q := appendTime τ₀ T (tposOf d b q).1
    let t_end := (u₀_q :: ρ).getLastD u₀_q
    have hu₀_T : u₀_q < T := appendTime_lt τ₀ T (by rw [hlen]; exact (tposOf d b q).2)
    have ht_end_T : t_end < T := hlast_lt_T ρ u₀_q hu₀_T hdep
    have hxt_p : τ₀.input t_end = (p.1 : ℤ) := readPos_eq_some_iff.mp hrd
    obtain ⟨β, hβ_blk⟩ := exists_mem_timeBlock_uncond hB_pos ht_end_T
    obtain ⟨ν, hν_ico⟩ := hpull q (hU_sub hq) p (mem_sdiff.mp (hU_sub hp)).1
      ρ hlen_ρ hdep hfreeB hxt_p β hβ_blk
    have hβ_Aq : β ∈ A_blk q := mem_filter.mpr ⟨mem_univ β, ν, hν_ico⟩
    have hA_qp : A_blk q = A_blk p := hA_eq q hq p hp
    have hβ_Ap : β ∈ A_blk p := hA_qp ▸ hβ_Aq
    have hβ_Ep : β ∈ (univ : Finset (Fin B_time)).filter (fun β' =>
        ∃ t ∈ timeBlock T B_time β', τ₀.input t = (p.1 : ℤ)) :=
      mem_filter.mpr ⟨mem_univ β, t_end, hβ_blk, hxt_p⟩
    exact disjoint_left.mp (hU_disj p hp) hβ_Ap hβ_Ep
  obtain ⟨hind, hacyc⟩ := isIndependent_and_isAcyclicIn_of_noArcs hno_arcs
  refine ⟨U_star, hU_sub.trans sdiff_subset, hind, hacyc, ?_⟩
  -- Arithmetic bound `|U_star| ≥ |V₀| / (3 * N_cells)`.
  have hB_ge : 2 * (m₀ : ℝ) * C / α ≤ (B_time : ℝ) := Nat.le_ceil _
  have hB_r_pos : (0 : ℝ) < (B_time : ℝ) := by exact_mod_cast hB_pos
  have hdiv_B_nat : ((T / B_time : ℕ) : ℝ) * (B_time : ℝ) ≤ (T : ℝ) := by
    have h := Nat.div_mul_le_self T B_time
    have hr : (((T / B_time) * B_time : ℕ) : ℝ) ≤ (T : ℝ) := by exact_mod_cast h
    simpa [Nat.cast_mul] using hr
  have hmT_B : (m₀ : ℝ) * ((T / B_time : ℕ) : ℝ) ≤ (V₀.card : ℝ) / 2 + α / 2 := by
    have h1 : 2 * (m₀ : ℝ) * C ≤ (B_time : ℝ) * α := (div_le_iff₀ hα0).mp hB_ge
    have h2 : (2 * (m₀ : ℝ)) * (((T / B_time : ℕ) : ℝ) * (B_time : ℝ)) ≤
        (2 * (m₀ : ℝ)) * (T : ℝ) :=
      mul_le_mul_of_nonneg_left hdiv_B_nat (by positivity)
    have h3 : (2 * (m₀ : ℝ)) * (T : ℝ) ≤ (2 * (m₀ : ℝ) * C) * ((L : ℝ) + 1) := by
      have : (T : ℝ) ≤ C * ((L : ℝ) + 1) := hT
      nlinarith
    have h4 : (2 * (m₀ : ℝ) * C) * ((L : ℝ) + 1) ≤ ((B_time : ℝ) * α) * ((L : ℝ) + 1) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have h5 : α * (L : ℝ) * (B_time : ℝ) ≤ (V₀.card : ℝ) * (B_time : ℝ) :=
      mul_le_mul_of_nonneg_right hV₀ (by positivity)
    have h6 : (2 * ((m₀ : ℝ) * ((T / B_time : ℕ) : ℝ))) * (B_time : ℝ) ≤
        ((V₀.card : ℝ) + α) * (B_time : ℝ) := by nlinarith
    have h7 := le_of_mul_le_mul_right h6 hB_r_pos
    linarith
  have hd_ge : 12 * (m₀ : ℝ) * (2 * (B_time : ℝ) + 2) / α + 6 ≤ (d : ℝ) := by
    have hd_r : (tightTimePullback_d0 m₀ C α : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd_thresh
    unfold tightTimePullback_d0 at hd_r
    exact (Nat.le_ceil _).trans hd_r
  have hd_mul : 12 * (m₀ : ℝ) * (2 * (B_time : ℝ) + 2) + 6 * α ≤ (d : ℝ) * α := by
    have h1 : 12 * (m₀ : ℝ) * (2 * (B_time : ℝ) + 2) / α ≤ (d : ℝ) - 6 := by linarith
    have h2 := (div_le_iff₀ hα0).mp h1
    linarith
  have hW_pos : (1 : ℝ) ≤ ((W : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos hd hb
  have hW_eq_L : (d : ℝ) * ((W : ℕ) : ℝ) = (L : ℝ) := by dsimp [W, L]; push_cast; ring
  have herr_W : α / 2 + (m₀ : ℝ) * (2 * (B_time : ℝ) + 2) * ((W : ℕ) : ℝ) ≤
      (V₀.card : ℝ) / 12 := by
    have h1 : 12 * (α / 2 + (m₀ : ℝ) * (2 * (B_time : ℝ) + 2) * ((W : ℕ) : ℝ)) ≤
        (12 * (m₀ : ℝ) * (2 * (B_time : ℝ) + 2) + 6 * α) * ((W : ℕ) : ℝ) := by nlinarith
    have h2 : (12 * (m₀ : ℝ) * (2 * (B_time : ℝ) + 2) + 6 * α) * ((W : ℕ) : ℝ) ≤
        ((d : ℝ) * α) * ((W : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_right hd_mul (by positivity)
    have h3 : ((d : ℝ) * α) * ((W : ℕ) : ℝ) = α * (L : ℝ) := by
      calc ((d : ℝ) * α) * ((W : ℕ) : ℝ) = α * ((d : ℝ) * ((W : ℕ) : ℝ)) := by ring
        _ = α * (L : ℝ) := by rw [hW_eq_L]
    linarith
  have hV_r : (V₀.card : ℝ) ≤
      (N_cells : ℝ) * (U_star.card : ℝ) + (Z_bad.card : ℝ) +
        (m₀ : ℝ) * ((T / B_time : ℕ) : ℝ) +
        (m₀ : ℝ) * (2 * (B_time : ℝ) + 2) * ((W : ℕ) : ℝ) := by
    have hr : (V₀.card : ℝ) ≤
        ((N_cells * U_star.card + Z_bad.card + m₀ * (T / B_time) +
          m₀ * (2 * B_time + 2) * W : ℕ) : ℝ) := by exact_mod_cast hV_nat
    push_cast at hr
    linarith
  have hNU_ge : (V₀.card : ℝ) / 3 ≤ (N_cells : ℝ) * (U_star.card : ℝ) := by linarith
  have hN_pos : (0 : ℝ) < 3 * (N_cells : ℝ) := by dsimp [N_cells, tightRefCells]; positivity
  unfold tightTimePullbackRhoMin
  rw [div_mul_eq_mul_div, div_le_iff₀ hN_pos]
  linarith

end TightCommonRefinementPullback

/-! ## §3. Singly-Exponential Cut-Slice Valid-Chain Bound & Zero-Genie Single-Cell Guard (`Targets K.1 & K.2`) -/

section SharpChainsAndSingleCellGuard

private theorem list_range_map_sum_eq_finset_sum (f : ℕ → ℕ) :
    ∀ n : ℕ, ((List.range n).map f).sum = ∑ m ∈ range n, f m
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, Finset.sum_range_succ,
      list_range_map_sum_eq_finset_sum f n]
    simp

/-- Structural prefix table for `chainCapAt k`, avoiding `WellFounded.fix` so small `k` reduce by `rfl`. -/
def chainCapPrefix (k : ℕ) : ℕ → (ℕ → ℕ)
  | 0 => fun _ => 1
  | n + 1 =>
    let f := chainCapPrefix k n
    let v := 1 + ((List.range (n + 1)).map fun m => min k (n + 1 - m) * f m).sum
    fun i => if i ≤ n then f i else v

/-- Maximum number of cut-valid phase-exit chains starting at a phase of cumulative interior cut weight `n`. -/
def chainCapAt (k n : ℕ) : ℕ :=
  chainCapPrefix k n n

private theorem chainCapPrefix_eq_at (k : ℕ) :
    ∀ (n i : ℕ), i ≤ n → chainCapPrefix k n i = chainCapAt k i
  | 0, i, hi => by
    have hi0 : i = 0 := Nat.eq_zero_of_le_zero hi
    subst hi0; rfl
  | n + 1, i, hi => by
    rcases eq_or_lt_of_le hi with rfl | hlt
    · rfl
    · have hi_n : i ≤ n := Nat.lt_succ_iff.mp hlt
      unfold chainCapPrefix
      simp only [hi_n, ↓reduceIte]
      exact chainCapPrefix_eq_at k n i hi_n

@[simp] theorem chainCapAt_zero (k : ℕ) : chainCapAt k 0 = 1 := rfl

theorem chainCapAt_succ (k n : ℕ) :
    chainCapAt k (n + 1) = 1 + ∑ m ∈ range (n + 1), min k (n + 1 - m) * chainCapAt k m := by
  have h1 : chainCapAt k (n + 1) =
      1 + ((List.range (n + 1)).map fun m => min k (n + 1 - m) * chainCapPrefix k n m).sum := by
    unfold chainCapAt
    rw [chainCapPrefix]
    have hn : ¬ (n + 1 ≤ n) := by omega
    simp only [hn, ↓reduceIte]
  rw [h1, list_range_map_sum_eq_finset_sum]
  refine congrArg (1 + ·) (sum_congr rfl fun m hm => ?_)
  rw [chainCapPrefix_eq_at k n m (Nat.lt_succ_iff.mp (mem_range.mp hm))]

/-- Total cut-valid phase-exit chains across all starting phases (`= 7, 49, 352` for `k = 1, 2, 3`). -/
def sharpChainCount (k : ℕ) : ℕ :=
  ((List.range (2 * k + 1)).map (chainCapAt k)).sum

theorem sharpChainCount_eq_sum (k : ℕ) :
    sharpChainCount k = ∑ n ∈ range (2 * k + 1), chainCapAt k n :=
  list_range_map_sum_eq_finset_sum (chainCapAt k) (2 * k + 1)

/-- Total **non-empty** cut-valid phase-exit chains (`= 4, 44, 345` for `k = 1, 2, 3`). -/
def sharpNonEmptyChains (k : ℕ) : ℕ :=
  ((List.range (2 * k + 1)).map fun n => chainCapAt k n - 1).sum

theorem sharpNonEmptyChains_eq_sum (k : ℕ) :
    sharpNonEmptyChains k = ∑ n ∈ range (2 * k + 1), (chainCapAt k n - 1) :=
  list_range_map_sum_eq_finset_sum (fun n => chainCapAt k n - 1) (2 * k + 1)

/-- Total monotone `(ξ, π)` interval families needed in Tight Theorem 5.3 (bridge):
`1` identity family covering all empty chains across all phases + `sharpNonEmptyChains k`
(`= 5, 45, 346` for `k = 1, 2, 3`, vs `12, 405, 28672` previously!). -/
def sharpFamCount (k : ℕ) : ℕ :=
  1 + sharpNonEmptyChains k

/-- Structural prefix table for `nodeCapAt k`, avoiding `WellFounded.fix`. -/
def nodeCapPrefix (k : ℕ) : ℕ → (ℕ → ℕ)
  | 0 => fun _ => 1
  | n + 1 =>
    let f := nodeCapPrefix k n
    let v := 1 + ((List.range (n + 1)).map fun m => min k (n + 1 - m) * (f m + chainCapAt k m)).sum
    fun i => if i ≤ n then f i else v

/-- Maximum sum of `(steps.length + 1)` over all cut-valid chains starting at cumulative cut weight `n`. -/
def nodeCapAt (k n : ℕ) : ℕ :=
  nodeCapPrefix k n n

private theorem nodeCapPrefix_eq_at (k : ℕ) :
    ∀ (n i : ℕ), i ≤ n → nodeCapPrefix k n i = nodeCapAt k i
  | 0, i, hi => by
    have hi0 : i = 0 := Nat.eq_zero_of_le_zero hi
    subst hi0; rfl
  | n + 1, i, hi => by
    rcases eq_or_lt_of_le hi with rfl | hlt
    · rfl
    · have hi_n : i ≤ n := Nat.lt_succ_iff.mp hlt
      unfold nodeCapPrefix
      simp only [hi_n, ↓reduceIte]
      exact nodeCapPrefix_eq_at k n i hi_n

@[simp] theorem nodeCapAt_zero (k : ℕ) : nodeCapAt k 0 = 1 := rfl

theorem nodeCapAt_succ (k n : ℕ) :
    nodeCapAt k (n + 1) =
      1 + ∑ m ∈ range (n + 1), min k (n + 1 - m) * (nodeCapAt k m + chainCapAt k m) := by
  have h1 : nodeCapAt k (n + 1) =
      1 + ((List.range (n + 1)).map fun m =>
        min k (n + 1 - m) * (nodeCapPrefix k n m + chainCapAt k m)).sum := by
    unfold nodeCapAt
    rw [nodeCapPrefix]
    have hn : ¬ (n + 1 ≤ n) := by omega
    simp only [hn, ↓reduceIte]
  rw [h1, list_range_map_sum_eq_finset_sum]
  refine congrArg (1 + ·) (sum_congr rfl fun m hm => ?_)
  rw [nodeCapPrefix_eq_at k n m (Nat.lt_succ_iff.mp (mem_range.mp hm))]

/-- Sum of `(steps.length + 1)` across all cut-valid chains (`= 12, 131, 1263` for `k = 1, 2, 3`). -/
def sharpChainNodeSum (k : ℕ) : ℕ :=
  ((List.range (2 * k + 1)).map (nodeCapAt k)).sum

theorem sharpChainNodeSum_eq_sum (k : ℕ) :
    sharpChainNodeSum k = ∑ n ∈ range (2 * k + 1), nodeCapAt k n :=
  list_range_map_sum_eq_finset_sum (nodeCapAt k) (2 * k + 1)

/-- **Single-cell guarded threshold count `sharpCellGuardThresh k` (`= 26, 266, 2532` for `k = 1, 2, 3`):**
`2 * k` positive phase lower bounds `θ_lo γ > 0` plus `2` cell-endpoint evaluations `(s₁(ν), s₂(ν))`
along every cut-valid chain (`completely independent of D, B_time, C, and α!`). -/
def sharpCellGuardThresh (k : ℕ) : ℕ :=
  2 * k + 2 * sharpChainNodeSum k

theorem sharpFamCount_pos (k : ℕ) : 1 ≤ sharpFamCount k := by
  unfold sharpFamCount; omega

theorem sharpCellGuardThresh_pos (k : ℕ) : 1 ≤ sharpCellGuardThresh k := by
  unfold sharpCellGuardThresh
  rw [sharpChainNodeSum_eq_sum]
  have h0 : 0 ∈ range (2 * k + 1) := mem_range.mpr (by omega)
  have hge1 : 1 ≤ ∑ n ∈ range (2 * k + 1), nodeCapAt k n := by
    calc 1 = nodeCapAt k 0 := rfl
      _ ≤ ∑ n ∈ range (2 * k + 1), nodeCapAt k n := single_le_sum (fun _ _ => Nat.zero_le _) h0
  omega

/-- Exact kernel-reduced benchmark values of `sharpChainCount`, `sharpFamCount`, and
`sharpCellGuardThresh` at `k = 1, 2, 3` (`via pure rfl, zero native_decide`). -/
theorem sharpCounts_small_values :
    (sharpChainCount 1 = 7 ∧ sharpChainCount 2 = 49 ∧ sharpChainCount 3 = 352) ∧
    (sharpFamCount 1 = 5 ∧ sharpFamCount 2 = 45 ∧ sharpFamCount 3 = 346) ∧
    (sharpCellGuardThresh 1 = 26 ∧ sharpCellGuardThresh 2 = 266 ∧ sharpCellGuardThresh 3 = 2532) :=
  ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

/-- Universal singly-exponential upper bound `chainCapAt k n ≤ 3 ^ n` and
`sharpFamCount k ≤ sharpChainCount k ≤ 3 ^ (2 * k + 1)` for **every** `k : ℕ`. -/
theorem sharpChainCount_le_pow_three (k : ℕ) :
    sharpFamCount k ≤ sharpChainCount k ∧ sharpChainCount k ≤ 3 ^ (2 * k + 1) := by
  have hfam : sharpFamCount k ≤ sharpChainCount k := by
    unfold sharpFamCount
    rw [sharpNonEmptyChains_eq_sum, sharpChainCount_eq_sum]
    rw [sum_range_succ']
    have hc0 : chainCapAt k 0 - 1 = 0 := rfl
    rw [hc0, add_zero]
    rw [sum_range_succ' (chainCapAt k) (2 * k)]
    have hc0' : chainCapAt k 0 = 1 := rfl
    rw [hc0', add_comm _ 1]
    exact Nat.add_le_add_left (sum_le_sum fun m _ => Nat.sub_le _ _) 1
  have hpow_id : ∀ n : ℕ, 1 + ∑ m ∈ range (n + 1), (n + 1 - m) * 3 ^ m ≤ 3 ^ (n + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hsplit : ∑ m ∈ range (n + 2), (n + 2 - m) * 3 ^ m =
          (∑ m ∈ range (n + 1), (n + 1 - m) * 3 ^ m) +
          (∑ m ∈ range (n + 1), 3 ^ m) + 3 ^ (n + 1) := by
        rw [sum_range_succ _ (n + 1)]
        have htop : (n + 2 - (n + 1)) * 3 ^ (n + 1) = 3 ^ (n + 1) := by simp
        rw [htop]
        have hterm : ∑ m ∈ range (n + 1), (n + 2 - m) * 3 ^ m =
            ∑ m ∈ range (n + 1), ((n + 1 - m) * 3 ^ m + 3 ^ m) := by
          refine sum_congr rfl fun m hm => ?_
          have hm_le : m ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hm)
          have hsub : n + 2 - m = (n + 1 - m) + 1 := by omega
          rw [hsub, Nat.add_mul, Nat.one_mul]
        rw [hterm, sum_add_distrib]
      have hgeom : 1 + 2 * ∑ m ∈ range (n + 1), 3 ^ m = 3 ^ (n + 1) := by
        clear ih hsplit
        induction n with
        | zero => simp
        | succ r ihr =>
          rw [sum_range_succ, Nat.mul_add, ← add_assoc, ihr]
          ring
      have hsum_3 : ∑ m ∈ range (n + 1), 3 ^ m ≤ 3 ^ (n + 1) := by omega
      rw [hsplit]
      have hpow_succ : 3 ^ (n + 2) = 3 * 3 ^ (n + 1) := by ring
      omega
  have hcap_pow : ∀ n : ℕ, chainCapAt k n ≤ 3 ^ n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      rcases n with _ | n
      · simp
      · rw [chainCapAt_succ]
        have hle_sum : ∑ m ∈ range (n + 1), min k (n + 1 - m) * chainCapAt k m ≤
            ∑ m ∈ range (n + 1), (n + 1 - m) * 3 ^ m := by
          refine sum_le_sum fun m hm => ?_
          have hm_lt : m < n + 1 := mem_range.mp hm
          exact Nat.mul_le_mul (Nat.min_le_right _ _) (ih m hm_lt)
        exact (Nat.add_le_add_left hle_sum 1).trans (hpow_id n)
  refine ⟨hfam, ?_⟩
  rw [sharpChainCount_eq_sum]
  have hgeom2 : ∑ n ∈ range (2 * k + 1), 3 ^ n ≤ 3 ^ (2 * k + 1) := by
    have h2 : ∀ r : ℕ, 1 + 2 * ∑ n ∈ range r, 3 ^ n = 3 ^ r := by
      intro r; induction r with
      | zero => simp
      | succ r ihr => rw [sum_range_succ, Nat.mul_add, ← add_assoc, ihr]; ring
    have := h2 (2 * k + 1)
    omega
  exact (sum_le_sum fun n _ => hcap_pow n).trans hgeom2

/-- Tightened micro-hop step guard cardinality `(microHopStepGuard τ₀ T H ψ).card ≤ 4 * k * H + k + 1`
(`holds for ALL k, H : ℕ without needing 1 ≤ H, improving (5 * k + 1) * H`). -/
theorem card_microHopStepGuard_tight {k : ℕ} (τ₀ : Trace k) (T H ψ : ℕ) :
    (microHopStepGuard τ₀ T H ψ).card ≤ 4 * k * H + k + 1 := by
  unfold microHopStepGuard
  split_ifs with h0
  · simp
  · have hbi : (((univ : Finset (Fin k)).biUnion fun j =>
        smallCrossingLowers (τ₀.work j) T (2 * H) (ψ - 1))).card ≤ k * (4 * H + 1) := by
      calc (((univ : Finset (Fin k)).biUnion fun j =>
            smallCrossingLowers (τ₀.work j) T (2 * H) (ψ - 1))).card
          ≤ ∑ j : Fin k, (smallCrossingLowers (τ₀.work j) T (2 * H) (ψ - 1)).card := card_biUnion_le
        _ ≤ ∑ _j : Fin k, (2 * (2 * H) + 1) :=
            sum_le_sum fun j _ => card_smallCrossingLowers_le (τ₀.work j) T (2 * H) (ψ - 1)
        _ = k * (4 * H + 1) := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]; ring
    have hins := card_insert_le (ψ - 1) ((univ : Finset (Fin k)).biUnion fun j =>
      smallCrossingLowers (τ₀.work j) T (2 * H) (ψ - 1))
    linarith

/-- Every `IsDepPath τ₀.work T (u₀ :: ρ)` starting at `u₀ < T` has `ρ.length ≤ T` (`in fact ≤ u₀`),
giving exact equality `coneSystem τ₀ T Γ d b (tposOf d b q) = ballAvoidSystem τ₀ T T Γ d b q`! -/
theorem isDepPath_length_le_head {k T : ℕ} {xs : Fin k → ℕ → ℤ} :
    ∀ (ρ : List ℕ) (u₀ : ℕ), IsDepPath xs T (u₀ :: ρ) → ρ.length ≤ u₀
  | [], _, _ => Nat.zero_le _
  | u₁ :: ρ₁, u₀, ⟨hstep, htail⟩ => by
    have hlt : u₁ < u₀ := (depStep_lt hstep).1
    have hsub := isDepPath_length_le_head ρ₁ u₁ htail
    simp only [List.length_cons]
    omega

/-- **Zero-Genie Equivalence at `D = T`:**
Whenever `(appendList τ₀ T).length = d * d * b`, every dependency path from `u₀(q) < T` has
`≤ T` hops automatically, so `coneSystem τ₀ T Γ d b (tposOf d b q)` equals `ballAvoidSystem τ₀ T T Γ d b q`
with **zero genie**! -/
theorem coneSystem_eq_ballAvoidSystem_at_T {k T d b : ℕ} (τ₀ : Trace k)
    (hlen : (appendList τ₀ T).length = d * d * b) (Γ : Finset ℕ) (q : Fin (d * d * b)) :
    coneSystem τ₀ T Γ d b (tposOf d b q) = ballAvoidSystem τ₀ T T Γ d b q := by
  ext p
  simp only [coneSystem, depCone, ballAvoidSystem, mem_filter, mem_univ, true_and]
  refine ⟨fun ⟨ρ, hdep, hfree, hrd⟩ => ⟨ρ, hdep, hfree, hrd, ?_⟩,
    fun ⟨ρ, hdep, hfree, hrd, _⟩ => ⟨ρ, hdep, hfree, hrd⟩⟩
  have hu₀_lt : appendTime τ₀ T (tposOf d b q).1 < T :=
    appendTime_lt τ₀ T (by rw [hlen]; exact (tposOf d b q).2)
  exact (isDepPath_length_le_head ρ _ hdep).trans (le_of_lt hu₀_lt)

/-- Cut-aware work-phase partition exposing the sorted boundary map `f : Fin (M_work + 1) → ℕ`
so interior cut weights sum to `≤ 2 * k`. -/
private theorem exists_workPhase_partition_with_cuts {k T : ℕ} (hT : 1 ≤ T)
    (θ_pos θ_neg : Fin k → ℕ) (hθ : ∀ j : Fin k, θ_pos j ≤ T ∧ θ_neg j ≤ T) :
    ∃ (M_work : ℕ) (f : Fin (M_work + 1) → ℕ) (ph : ℕ → Fin M_work),
      let θ_lo : Fin M_work → ℕ := fun γ => f ⟨γ.1, by omega⟩
      let θ_hi : Fin M_work → ℕ := fun γ => f ⟨γ.1 + 1, by omega⟩
      1 ≤ M_work ∧ M_work ≤ 2 * k + 1 ∧
      StrictMono f ∧ f ⟨0, by omega⟩ = 0 ∧ f ⟨M_work, by omega⟩ = T ∧
      (∀ i : Fin (M_work + 1), 0 < i.1 → i.1 < M_work →
        (∃ j : Fin k, θ_pos j = f i) ∨ (∃ j : Fin k, θ_neg j = f i)) ∧
      (∀ x ∈ ((univ : Finset (Fin k)).image θ_pos) ∪ ((univ : Finset (Fin k)).image θ_neg),
        ∃ i : Fin (M_work + 1), f i = x) ∧
      (∀ γ : Fin M_work, θ_lo γ < θ_hi γ ∧ θ_hi γ ≤ T) ∧
      (∀ c₁ c₂ : Fin M_work, c₁.1 < c₂.1 → θ_hi c₁ ≤ θ_lo c₂) ∧
      (∀ (γ : Fin M_work) (j : Fin k),
        ¬ (θ_lo γ < θ_pos j ∧ θ_pos j < θ_hi γ) ∧
        ¬ (θ_lo γ < θ_neg j ∧ θ_neg j < θ_hi γ)) ∧
      (∀ t : ℕ, t < T → t ∈ Ico (θ_lo (ph t)) (θ_hi (ph t))) ∧
      (∀ t₁ t₂ : ℕ, t₁ ≤ t₂ → t₂ < T → (ph t₁).1 ≤ (ph t₂).1) := by
  let S_cuts : Finset ℕ :=
    insert 0 (insert T (((univ : Finset (Fin k)).image θ_pos) ∪ ((univ : Finset (Fin k)).image θ_neg)))
  have h0_mem : 0 ∈ S_cuts := mem_insert_self 0 _
  have hT_mem : T ∈ S_cuts := mem_insert_of_mem (mem_insert_self T _)
  have hS_le_T : ∀ x ∈ S_cuts, x ≤ T := by
    intro x hx
    rcases mem_insert.mp hx with rfl | hx1
    · omega
    · rcases mem_insert.mp hx1 with rfl | hx2
      · exact le_rfl
      · rcases mem_union.mp hx2 with hp | hn
        · obtain ⟨j, _, rfl⟩ := mem_image.mp hp; exact (hθ j).1
        · obtain ⟨j, _, rfl⟩ := mem_image.mp hn; exact (hθ j).2
  have hcard_ge : 2 ≤ S_cuts.card := by
    have hsub : ({0, T} : Finset ℕ) ⊆ S_cuts :=
      insert_subset h0_mem (singleton_subset_iff.mpr hT_mem)
    have hc2 : ({0, T} : Finset ℕ).card = 2 := card_pair (by omega)
    exact hc2 ▸ card_le_card hsub
  have hcard_le : S_cuts.card ≤ 2 * k + 2 := by
    have h1 := card_insert_le 0 (insert T (((univ : Finset (Fin k)).image θ_pos) ∪ ((univ : Finset (Fin k)).image θ_neg)))
    have h2 := card_insert_le T (((univ : Finset (Fin k)).image θ_pos) ∪ ((univ : Finset (Fin k)).image θ_neg))
    have h3 := card_union_le ((univ : Finset (Fin k)).image θ_pos) ((univ : Finset (Fin k)).image θ_neg)
    have h4 : ((univ : Finset (Fin k)).image θ_pos).card ≤ k := card_image_le.trans (by simp)
    have h5 : ((univ : Finset (Fin k)).image θ_neg).card ≤ k := card_image_le.trans (by simp)
    dsimp only [S_cuts]; omega
  let M_work := S_cuts.card - 1
  have hM_ge : 1 ≤ M_work := by omega
  have hM_le : M_work ≤ 2 * k + 1 := by omega
  have hS_card : S_cuts.card = M_work + 1 := by omega
  obtain ⟨f, hf_mono, hf_mem, hf_surj⟩ := LeanMachine.ThresholdRefinement.exists_strictMono_equiv_of_finset (M_work + 1) S_cuts hS_card
  have hf0 : f ⟨0, by omega⟩ = 0 := by
    obtain ⟨i, hi⟩ := hf_surj 0 h0_mem
    rcases Nat.eq_zero_or_pos i.1 with h0 | hpos
    · have : i = ⟨0, by omega⟩ := Fin.ext h0; rwa [this] at hi
    · exfalso; have := hf_mono (show (⟨0, by omega⟩ : Fin (M_work + 1)) < i from hpos); omega
  have hfM : f ⟨M_work, by omega⟩ = T := by
    obtain ⟨i, hi⟩ := hf_surj T hT_mem
    rcases eq_or_lt_of_le (Nat.le_of_lt_succ i.2) with heq | hlt
    · have : i = ⟨M_work, by omega⟩ := Fin.ext heq; rwa [this] at hi
    · exfalso
      have := hf_mono (show i < (⟨M_work, by omega⟩ : Fin (M_work + 1)) from hlt)
      have := hS_le_T _ (hf_mem ⟨M_work, by omega⟩)
      omega
  let θ_lo : Fin M_work → ℕ := fun γ => f ⟨γ.1, by omega⟩
  let θ_hi : Fin M_work → ℕ := fun γ => f ⟨γ.1 + 1, by omega⟩
  have hlo_lt_hi : ∀ γ : Fin M_work, θ_lo γ < θ_hi γ ∧ θ_hi γ ≤ T := fun γ =>
    ⟨hf_mono (show (⟨γ.1, by omega⟩ : Fin (M_work + 1)) < ⟨γ.1 + 1, by omega⟩ by simp),
      hS_le_T _ (hf_mem ⟨γ.1 + 1, by omega⟩)⟩
  have hsep_ph : ∀ c₁ c₂ : Fin M_work, c₁.1 < c₂.1 → θ_hi c₁ ≤ θ_lo c₂ := fun c₁ c₂ hlt =>
    hf_mono.monotone (show (⟨c₁.1 + 1, by omega⟩ : Fin (M_work + 1)) ≤ ⟨c₂.1, by omega⟩ from hlt)
  have hno_inner : ∀ (γ : Fin M_work) (x : ℕ), x ∈ S_cuts → ¬ (θ_lo γ < x ∧ x < θ_hi γ) := by
    intro γ x hx ⟨h1, h2⟩
    obtain ⟨i, rfl⟩ := hf_surj x hx
    have hi1 : γ.1 < i.1 := by
      by_contra hle; push Not at hle
      have := hf_mono.monotone (show i ≤ ⟨γ.1, by omega⟩ from hle); dsimp [θ_lo] at h1; omega
    have hi2 : i.1 < γ.1 + 1 := by
      by_contra hge; push Not at hge
      have := hf_mono.monotone (show (⟨γ.1 + 1, by omega⟩ : Fin (M_work + 1)) ≤ i from hge)
      dsimp [θ_hi] at h2; omega
    omega
  let ph : ℕ → Fin M_work := fun t =>
    if ht : t < T then
      let I_le := (univ : Finset (Fin (M_work + 1))).filter fun i => f i ≤ t
      have hne : I_le.Nonempty := ⟨⟨0, by omega⟩, mem_filter.mpr ⟨mem_univ _, by omega⟩⟩
      let i_max := I_le.max' hne
      have hi_lt : i_max.1 < M_work := by
        rcases eq_or_lt_of_le (Nat.le_of_lt_succ i_max.2) with heq | hlt
        · exfalso
          have hmem : f i_max ≤ t := (mem_filter.mp (I_le.max'_mem hne)).2
          have : i_max = ⟨M_work, by omega⟩ := Fin.ext heq; rw [this, hfM] at hmem; omega
        · exact hlt
      ⟨i_max.1, hi_lt⟩
    else ⟨0, hM_ge⟩
  have hph_mem : ∀ t : ℕ, t < T → t ∈ Ico (θ_lo (ph t)) (θ_hi (ph t)) := by
    intro t ht
    dsimp only [ph]; simp only [ht, ↓reduceDIte]
    let I_le := (univ : Finset (Fin (M_work + 1))).filter fun i => f i ≤ t
    have hne : I_le.Nonempty := ⟨⟨0, by omega⟩, mem_filter.mpr ⟨mem_univ _, by omega⟩⟩
    let i_max := I_le.max' hne
    have hi_le : f i_max ≤ t := (mem_filter.mp (I_le.max'_mem hne)).2
    have hi_lt : i_max.1 < M_work := by
      rcases eq_or_lt_of_le (Nat.le_of_lt_succ i_max.2) with heq | hlt
      · exfalso; have : i_max = ⟨M_work, by omega⟩ := Fin.ext heq; rw [this, hfM] at hi_le; omega
      · exact hlt
    refine mem_Ico.mpr ⟨hi_le, ?_⟩
    dsimp [θ_hi]
    by_contra hge; push Not at hge
    have hmem_s : (⟨i_max.1 + 1, by omega⟩ : Fin (M_work + 1)) ∈ I_le := mem_filter.mpr ⟨mem_univ _, hge⟩
    have hle_max : i_max.1 + 1 ≤ i_max.1 := I_le.le_max' _ hmem_s
    omega
  have hph_mono : ∀ t₁ t₂ : ℕ, t₁ ≤ t₂ → t₂ < T → (ph t₁).1 ≤ (ph t₂).1 := by
    intro t₁ t₂ hle ht₂
    obtain ⟨h1, _⟩ := mem_Ico.mp (hph_mem t₁ (lt_of_le_of_lt hle ht₂))
    obtain ⟨_, h4⟩ := mem_Ico.mp (hph_mem t₂ ht₂)
    by_contra hgt; push Not at hgt
    have := hsep_ph (ph t₂) (ph t₁) hgt; omega
  have hint_mem : ∀ i : Fin (M_work + 1), 0 < i.1 → i.1 < M_work →
      (∃ j : Fin k, θ_pos j = f i) ∨ (∃ j : Fin k, θ_neg j = f i) := by
    intro i hi0 hiM
    have hgt0 : 0 < f i := by
      rw [← hf0]; exact hf_mono (show (⟨0, by omega⟩ : Fin (M_work + 1)) < i from hi0)
    have hltT : f i < T := by
      rw [← hfM]; exact hf_mono (show i < (⟨M_work, by omega⟩ : Fin (M_work + 1)) from hiM)
    rcases mem_insert.mp (hf_mem i) with heq0 | h1
    · omega
    · rcases mem_insert.mp h1 with heqT | h2
      · omega
      · rcases mem_union.mp h2 with hp | hn
        · obtain ⟨j, _, hj⟩ := mem_image.mp hp; exact Or.inl ⟨j, hj⟩
        · obtain ⟨j, _, hj⟩ := mem_image.mp hn; exact Or.inr ⟨j, hj⟩
  refine ⟨M_work, f, ph, hM_ge, hM_le, hf_mono, hf0, hfM, hint_mem,
    fun x hx => hf_surj x (mem_insert_of_mem (mem_insert_of_mem hx)),
    hlo_lt_hi, hsep_ph, fun γ j => ⟨?_, ?_⟩, hph_mem, hph_mono⟩
  · exact hno_inner γ (θ_pos j)
      (mem_insert_of_mem (mem_insert_of_mem (mem_union_left _ (mem_image_of_mem _ (mem_univ j)))))
  · exact hno_inner γ (θ_neg j)
      (mem_insert_of_mem (mem_insert_of_mem (mem_union_right _ (mem_image_of_mem _ (mem_univ j)))))

/-- Recursive `Finset` of cut-valid step lists below phase `n < M_work`. -/
noncomputable def cutValidStepsAux (M_work k : ℕ)
    (validTapes : Fin M_work → Fin M_work → Finset (Fin k)) :
    (n : ℕ) → (hn : n < M_work) → Finset (List (Fin M_work × Fin k))
  | n, hn =>
    insert []
      ((Finset.attach (range n)).biUnion fun ⟨m, hm⟩ =>
        have hm_lt : m < n := mem_range.mp hm
        (validTapes ⟨m, hm_lt.trans hn⟩ ⟨n, hn⟩).biUnion fun j =>
          (cutValidStepsAux M_work k validTapes m (hm_lt.trans hn)).image
            fun rest => (⟨m, hm_lt.trans hn⟩, j) :: rest)
termination_by n _ => n

theorem nil_mem_cutValidStepsAux (M_work k : ℕ)
    (validTapes : Fin M_work → Fin M_work → Finset (Fin k))
    (n : ℕ) (hn : n < M_work) :
    [] ∈ cutValidStepsAux M_work k validTapes n hn := by
  rw [cutValidStepsAux]
  exact mem_insert_self _ _

theorem cons_mem_cutValidStepsAux (M_work k : ℕ)
    (validTapes : Fin M_work → Fin M_work → Finset (Fin k))
    {m n : ℕ} (hmn : m < n) (hn : n < M_work) {j : Fin k}
    (hj : j ∈ validTapes ⟨m, hmn.trans hn⟩ ⟨n, hn⟩)
    {rest : List (Fin M_work × Fin k)}
    (hrest : rest ∈ cutValidStepsAux M_work k validTapes m (hmn.trans hn)) :
    (⟨m, hmn.trans hn⟩, j) :: rest ∈ cutValidStepsAux M_work k validTapes n hn := by
  rw [cutValidStepsAux]
  refine mem_insert_of_mem (mem_biUnion.mpr ⟨⟨m, mem_range.mpr hmn⟩, mem_attach _ _, ?_⟩)
  exact mem_biUnion.mpr ⟨j, hj, mem_image_of_mem _ hrest⟩

private theorem nat_sum_biUnion_le {α β : Type*} [DecidableEq β]
    (s : Finset α) (t : α → Finset β) (f : β → ℕ) :
    (∑ x ∈ s.biUnion t, f x) ≤ ∑ a ∈ s, ∑ x ∈ t a, f x := by
  classical
  refine Finset.induction_on s (by simp) fun a s ha ih => ?_
  rw [biUnion_insert, sum_insert ha]
  have hun : (∑ x ∈ t a ∪ s.biUnion t, f x) ≤ (∑ x ∈ t a, f x) + ∑ x ∈ s.biUnion t, f x := by
    have h1 := sum_union_inter (s₁ := t a) (s₂ := s.biUnion t) (f := f)
    omega
  exact hun.trans (Nat.add_le_add_left ih _)

/-- Cut-slice cardinality and node-sum bounds on `cutValidStepsAux` via strictly-increasing
cumulative cut weight `σ_ph : Fin M_work → ℕ`. -/
private theorem cutValidStepsAux_card_and_nodes_le {M_work k : ℕ}
    (validTapes : Fin M_work → Fin M_work → Finset (Fin k))
    (σ_ph : Fin M_work → ℕ)
    (hσ_mono : ∀ c₁ c₂ : Fin M_work, c₁.1 < c₂.1 → σ_ph c₁ < σ_ph c₂)
    (htapes : ∀ c₁ c₂ : Fin M_work, c₁.1 < c₂.1 →
      (validTapes c₁ c₂).card ≤ min k (σ_ph c₂ - σ_ph c₁)) :
    ∀ (n : ℕ) (hn : n < M_work),
      (cutValidStepsAux M_work k validTapes n hn).card ≤ chainCapAt k (σ_ph ⟨n, hn⟩) ∧
      ((cutValidStepsAux M_work k validTapes n hn).erase []).card ≤ chainCapAt k (σ_ph ⟨n, hn⟩) - 1 ∧
      (∑ steps ∈ cutValidStepsAux M_work k validTapes n hn, (steps.length + 1)) ≤
        nodeCapAt k (σ_ph ⟨n, hn⟩) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    have hnil_mem := nil_mem_cutValidStepsAux M_work k validTapes n hn
    rcases Nat.eq_zero_or_pos (σ_ph ⟨n, hn⟩) with hσ0 | hσ_pos
    · have hn0 : n = 0 := by
        rcases Nat.eq_zero_or_pos n with rfl | hpos
        · rfl
        · exfalso
          have := hσ_mono ⟨0, hpos.trans hn⟩ ⟨n, hn⟩ hpos
          omega
      subst hn0
      have heq : cutValidStepsAux M_work k validTapes 0 hn = {[]} := by
        rw [cutValidStepsAux]; simp
      rw [heq, hσ0]
      simp
    · obtain ⟨s, hs_eq⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hσ_pos)
      let Sub := (Finset.attach (range n)).biUnion fun ⟨m, hm⟩ =>
        have hm_lt : m < n := mem_range.mp hm
        (validTapes ⟨m, hm_lt.trans hn⟩ ⟨n, hn⟩).biUnion fun j =>
          (cutValidStepsAux M_work k validTapes m (hm_lt.trans hn)).image
            fun rest => (⟨m, hm_lt.trans hn⟩, j) :: rest
      have hS_eq : cutValidStepsAux M_work k validTapes n hn = insert [] Sub := by
        rw [cutValidStepsAux]
      have hnil_not_Sub : [] ∉ Sub := by
        intro hmem
        obtain ⟨⟨m, hm⟩, _, hmem2⟩ := mem_biUnion.mp hmem
        obtain ⟨j, _, hmem3⟩ := mem_biUnion.mp hmem2
        obtain ⟨rest, _, heq⟩ := mem_image.mp hmem3
        exact List.cons_ne_nil _ _ heq
      -- Map each `m ∈ attach (range n)` injectively to `σ_ph ⟨m, _⟩ ∈ range (s + 1)`.
      let idxOf : {m // m ∈ range n} → ℕ := fun m => σ_ph ⟨m.1, (mem_range.mp m.2).trans hn⟩
      have hidx_mem : ∀ m ∈ Finset.attach (range n), idxOf m ∈ range (s + 1) := by
        intro m _
        have hlt := hσ_mono ⟨m.1, (mem_range.mp m.2).trans hn⟩ ⟨n, hn⟩ (mem_range.mp m.2)
        rw [mem_range]
        dsimp [idxOf]
        omega
      have hidx_inj : Set.InjOn idxOf (Finset.attach (range n) : Set {m // m ∈ range n}) := by
        intro m₁ _ m₂ _ heq
        rcases lt_trichotomy m₁.1 m₂.1 with hlt | heq_v | hgt
        · exfalso
          have := hσ_mono ⟨m₁.1, (mem_range.mp m₁.2).trans hn⟩ ⟨m₂.1, (mem_range.mp m₂.2).trans hn⟩ hlt
          dsimp [idxOf] at heq; omega
        · exact Subtype.ext heq_v
        · exfalso
          have := hσ_mono ⟨m₂.1, (mem_range.mp m₂.2).trans hn⟩ ⟨m₁.1, (mem_range.mp m₁.2).trans hn⟩ hgt
          dsimp [idxOf] at heq; omega
      -- Card bound on `Sub`:
      have hSub_card : Sub.card ≤ ∑ r ∈ range (s + 1), min k (s + 1 - r) * chainCapAt k r := by
        calc Sub.card
            ≤ ∑ m ∈ Finset.attach (range n),
                ((validTapes ⟨m.1, (mem_range.mp m.2).trans hn⟩ ⟨n, hn⟩).biUnion fun j =>
                  (cutValidStepsAux M_work k validTapes m.1 ((mem_range.mp m.2).trans hn)).image
                    fun rest => (⟨m.1, (mem_range.mp m.2).trans hn⟩, j) :: rest).card := card_biUnion_le
          _ ≤ ∑ m ∈ Finset.attach (range n),
                min k (s + 1 - idxOf m) * chainCapAt k (idxOf m) := by
              refine sum_le_sum fun m _ => ?_
              have hm_lt : m.1 < n := mem_range.mp m.2
              have ht_le := htapes ⟨m.1, hm_lt.trans hn⟩ ⟨n, hn⟩ hm_lt
              rw [hs_eq] at ht_le
              have hih_m := (ih m.1 hm_lt (hm_lt.trans hn)).1
              calc ((validTapes ⟨m.1, hm_lt.trans hn⟩ ⟨n, hn⟩).biUnion fun j =>
                      (cutValidStepsAux M_work k validTapes m.1 (hm_lt.trans hn)).image
                        fun rest => (⟨m.1, hm_lt.trans hn⟩, j) :: rest).card
                  ≤ ∑ j ∈ validTapes ⟨m.1, hm_lt.trans hn⟩ ⟨n, hn⟩,
                      ((cutValidStepsAux M_work k validTapes m.1 (hm_lt.trans hn)).image
                        fun rest => (⟨m.1, hm_lt.trans hn⟩, j) :: rest).card := card_biUnion_le
                _ ≤ ∑ _j ∈ validTapes ⟨m.1, hm_lt.trans hn⟩ ⟨n, hn⟩, chainCapAt k (idxOf m) :=
                    sum_le_sum fun j _ => card_image_le.trans hih_m
                _ = (validTapes ⟨m.1, hm_lt.trans hn⟩ ⟨n, hn⟩).card * chainCapAt k (idxOf m) := by simp
                _ ≤ min k (s + 1 - idxOf m) * chainCapAt k (idxOf m) :=
                    Nat.mul_le_mul ht_le le_rfl
          _ = ∑ r ∈ (Finset.attach (range n)).image idxOf, min k (s + 1 - r) * chainCapAt k r :=
              (sum_image (f := fun r => min k (s + 1 - r) * chainCapAt k r) hidx_inj).symm
          _ ≤ ∑ r ∈ range (s + 1), min k (s + 1 - r) * chainCapAt k r :=
              sum_le_sum_of_subset fun r hr => by
                obtain ⟨m, hm, rfl⟩ := mem_image.mp hr
                exact hidx_mem m hm
      -- Node-sum bound on `Sub`:
      have hSub_nodes : (∑ steps ∈ Sub, (steps.length + 1)) ≤
          ∑ r ∈ range (s + 1), min k (s + 1 - r) * (nodeCapAt k r + chainCapAt k r) := by
        calc (∑ steps ∈ Sub, (steps.length + 1))
            ≤ ∑ m ∈ Finset.attach (range n),
                ∑ steps ∈ ((validTapes ⟨m.1, (mem_range.mp m.2).trans hn⟩ ⟨n, hn⟩).biUnion fun j =>
                  (cutValidStepsAux M_work k validTapes m.1 ((mem_range.mp m.2).trans hn)).image
                    fun rest => (⟨m.1, (mem_range.mp m.2).trans hn⟩, j) :: rest),
                  (steps.length + 1) := nat_sum_biUnion_le _ _ _
          _ ≤ ∑ m ∈ Finset.attach (range n),
                min k (s + 1 - idxOf m) * (nodeCapAt k (idxOf m) + chainCapAt k (idxOf m)) := by
              refine sum_le_sum fun m _ => ?_
              have hm_lt : m.1 < n := mem_range.mp m.2
              have ht_le := htapes ⟨m.1, hm_lt.trans hn⟩ ⟨n, hn⟩ hm_lt
              rw [hs_eq] at ht_le
              obtain ⟨hih_c, _, hih_nd⟩ := ih m.1 hm_lt (hm_lt.trans hn)
              let S_m := cutValidStepsAux M_work k validTapes m.1 (hm_lt.trans hn)
              have himg_sum : ∀ j : Fin k,
                  (∑ steps ∈ S_m.image (fun rest => (⟨m.1, hm_lt.trans hn⟩, j) :: rest),
                    (steps.length + 1)) ≤ nodeCapAt k (idxOf m) + chainCapAt k (idxOf m) := by
                intro j
                have hinj_cons : Function.Injective
                    (fun rest : List (Fin M_work × Fin k) => (⟨m.1, hm_lt.trans hn⟩, j) :: rest) :=
                  fun _ _ h => List.cons.inj h |>.2
                rw [sum_image hinj_cons.injOn]
                have hlen_add : (∑ rest ∈ S_m, (((⟨m.1, hm_lt.trans hn⟩, j) :: rest).length + 1)) =
                    (∑ rest ∈ S_m, (rest.length + 1)) + S_m.card := by
                  simp only [List.length_cons]
                  rw [sum_add_distrib, sum_const, smul_eq_mul, mul_one]
                rw [hlen_add]
                exact Nat.add_le_add hih_nd hih_c
              calc (∑ steps ∈ ((validTapes ⟨m.1, hm_lt.trans hn⟩ ⟨n, hn⟩).biUnion fun j =>
                      S_m.image fun rest => (⟨m.1, hm_lt.trans hn⟩, j) :: rest),
                      (steps.length + 1))
                  ≤ ∑ j ∈ validTapes ⟨m.1, hm_lt.trans hn⟩ ⟨n, hn⟩,
                      ∑ steps ∈ S_m.image (fun rest => (⟨m.1, hm_lt.trans hn⟩, j) :: rest),
                        (steps.length + 1) := nat_sum_biUnion_le _ _ _
                _ ≤ ∑ _j ∈ validTapes ⟨m.1, hm_lt.trans hn⟩ ⟨n, hn⟩,
                      (nodeCapAt k (idxOf m) + chainCapAt k (idxOf m)) :=
                    sum_le_sum fun j _ => himg_sum j
                _ = (validTapes ⟨m.1, hm_lt.trans hn⟩ ⟨n, hn⟩).card *
                      (nodeCapAt k (idxOf m) + chainCapAt k (idxOf m)) := by simp
                _ ≤ min k (s + 1 - idxOf m) * (nodeCapAt k (idxOf m) + chainCapAt k (idxOf m)) :=
                    Nat.mul_le_mul ht_le le_rfl
          _ = ∑ r ∈ (Finset.attach (range n)).image idxOf,
                min k (s + 1 - r) * (nodeCapAt k r + chainCapAt k r) :=
              (sum_image (f := fun r => min k (s + 1 - r) * (nodeCapAt k r + chainCapAt k r)) hidx_inj).symm
          _ ≤ ∑ r ∈ range (s + 1), min k (s + 1 - r) * (nodeCapAt k r + chainCapAt k r) :=
              sum_le_sum_of_subset fun r hr => by
                obtain ⟨m, hm, rfl⟩ := mem_image.mp hr
                exact hidx_mem m hm
      rw [hS_eq, hs_eq]
      refine ⟨?_, ?_, ?_⟩
      · rw [card_insert_of_notMem hnil_not_Sub, chainCapAt_succ]
        omega
      · rw [erase_insert hnil_not_Sub, chainCapAt_succ]
        omega
      · rw [sum_insert hnil_not_Sub, nodeCapAt_succ]
        simp only [List.length_nil, zero_add]
        omega

/-- **`s`-Independent Path-to-Chain Trace (`Step A of Single-Cell Guard`):**
Records that `t₀ :: ρ` stays inside `[θ_lo γ, θ_hi γ)` on intra-phase steps (`u = v + 1` or `≤ 2H`
micro-hop) and exits to `γ' < γ` via `IsNonCrossingLargeHop (τ₀.work j) T (2 * H) v u` along `steps`. -/
inductive FollowsChain {k M_work : ℕ} (τ₀ : Trace k) (T H : ℕ)
    (θ_lo θ_hi : Fin M_work → ℕ) :
    Fin M_work → List (Fin M_work × Fin k) → ℕ → List ℕ → Prop where
  | nil {γ : Fin M_work} {t₀ : ℕ} (ht₀ : t₀ ∈ Ico (θ_lo γ) (θ_hi γ)) :
      FollowsChain τ₀ T H θ_lo θ_hi γ [] t₀ []
  | intra {γ : Fin M_work} {steps : List (Fin M_work × Fin k)} {u v : ℕ} {ρ₁ : List ℕ}
      (hu : u ∈ Ico (θ_lo γ) (θ_hi γ))
      (hv : v ∈ Ico (θ_lo γ) (θ_hi γ))
      (hedge : u = v + 1 ∨
        (∃ j : Fin k, IsHop (τ₀.work j) T v u ∧
          ∀ t ∈ Ioo v u, |τ₀.work j t - τ₀.work j v| ≤ ((2 * H : ℕ) : ℤ)))
      (hrest : FollowsChain τ₀ T H θ_lo θ_hi γ steps v ρ₁) :
      FollowsChain τ₀ T H θ_lo θ_hi γ steps u (v :: ρ₁)
  | inter {γ γ' : Fin M_work} {j : Fin k} {rest : List (Fin M_work × Fin k)} {u v : ℕ} {ρ₁ : List ℕ}
      (hlt : γ'.1 < γ.1)
      (hu : u ∈ Ico (θ_lo γ) (θ_hi γ))
      (hv : v ∈ Ico (θ_lo γ') (θ_hi γ'))
      (hnc : IsNonCrossingLargeHop (τ₀.work j) T (2 * H) v u)
      (hrest : FollowsChain τ₀ T H θ_lo θ_hi γ' rest v ρ₁) :
      FollowsChain τ₀ T H θ_lo θ_hi γ ((γ', j) :: rest) u (v :: ρ₁)

/-- **Single-Parameter Pullback Equivalence along `FollowsChain` (`Step B of Single-Cell Guard`):**
For **any single `s : ℕ`**, if `FollowsChain τ₀ T H θ_lo θ_hi γ steps t₀ ρ_suf` holds and `ρ_suf`
avoids `(chainThresholds τ₀ T H B_time θ_lo θ_hi γ steps s).biUnion (microHopStepGuard τ₀ T H)`,
then `chainPred` at `(γ, steps, s)` on `t₀` is equivalent to `(t₀ :: ρ_suf).getLastD t₀ < timeBlockBound T B_time s`! -/
private theorem followsChain_pullChainPsi_iff {k M_work : ℕ} (τ₀ : Trace k) (T H B_time : ℕ)
    (θ_lo θ_hi : Fin M_work → ℕ)
    {θ_pos θ_neg : Fin k → ℕ}
    (hsep : ∀ c₁ c₂ : Fin M_work, c₁.1 < c₂.1 → θ_hi c₁ ≤ θ_lo c₂)
    (hno_cut : ∀ (γ : Fin M_work) (j : Fin k),
      ¬ (θ_lo γ < θ_pos j ∧ θ_pos j < θ_hi γ) ∧ ¬ (θ_lo γ < θ_neg j ∧ θ_neg j < θ_hi γ))
    {γ : Fin M_work} {steps : List (Fin M_work × Fin k)} {t₀ : ℕ} {ρ_suf : List ℕ}
    (hfol : FollowsChain τ₀ T H θ_lo θ_hi γ steps t₀ ρ_suf) (s : ℕ)
    (hguard : ∀ w ∈ ρ_suf, w ∉ (chainThresholds τ₀ T H B_time θ_lo θ_hi γ steps s).biUnion
      (microHopStepGuard τ₀ T H)) :
    chainPred (chainParity steps) (pullChainPsi τ₀ T H B_time θ_lo θ_hi γ steps s) t₀ ↔
      (t₀ :: ρ_suf).getLastD t₀ < timeBlockBound T B_time s := by
  induction hfol with
  | @nil γ t₀ ht₀ =>
    obtain ⟨hlo, hhi⟩ := mem_Ico.mp ht₀
    have hlast0 : ([t₀]).getLastD t₀ = t₀ := rfl
    rw [hlast0]
    dsimp only [chainParity, chainPred, pullChainPsi]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rcases le_or_gt (timeBlockBound T B_time s) (θ_lo γ) with h1 | h1
    · rw [Nat.max_eq_left h1, Nat.min_eq_right (le_of_lt (lt_of_le_of_lt hlo hhi))]
      omega
    · rw [Nat.max_eq_right (le_of_lt h1)]
      rcases le_or_gt (θ_hi γ) (timeBlockBound T B_time s) with h2 | h2
      · rw [Nat.min_eq_left h2]; omega
      · rw [Nat.min_eq_right (le_of_lt h2)]
  | @intra γ steps u v ρ₁ hu hv hedge _ ih =>
    have hv_guard : v ∉ microHopStepGuard τ₀ T H
        (pullChainPsi τ₀ T H B_time θ_lo θ_hi γ steps s) := fun hg =>
      hguard v List.mem_cons_self
        (mem_biUnion.mpr ⟨_, pullChainPsi_mem_chainThresholds τ₀ T H B_time θ_lo θ_hi γ steps s, hg⟩)
    have hdich : u = v + 1 ∨
        (∃ j : Fin k, IsHop (τ₀.work j) T v u ∧
          ∀ t ∈ Ioo v u, |τ₀.work j t - τ₀.work j v| ≤ ((2 * H : ℕ) : ℤ)) ∨
        (∃ j : Fin k, IsNonCrossingLargeHop (τ₀.work j) T (2 * H) v u ∧
          ((v < θ_pos j ∧ θ_pos j ≤ u) ∨ (v < θ_neg j ∧ θ_neg j ≤ u))) := by
      rcases hedge with h1 | h2
      · exact Or.inl h1
      · exact Or.inr (Or.inl h2)
    have hintra := dichotomy_intraPhase_chainPred_iff (hno_cut γ) hu hv hdich hv_guard (chainParity steps)
    rw [LinNet.getLastD_cons_cons, hintra]
    exact ih fun w hw => hguard w (List.mem_cons_of_mem v hw)
  | @inter γ γ' j rest u v ρ₁ hlt hu hv hnc _ ih =>
    have hinter := pullChainPsi_cons_iff τ₀ T H B_time θ_lo θ_hi hsep hlt j rest s hu hv hnc
    rw [LinNet.getLastD_cons_cons, hinter]
    refine ih fun w hw hmem => hguard w (List.mem_cons_of_mem v hw) ?_
    obtain ⟨ψ, hψ, hg⟩ := mem_biUnion.mp hmem
    exact mem_biUnion.mpr ⟨ψ, mem_insert_of_mem hψ, hg⟩

/-- Common-refinement cell cap `(sharpFamCount k) * B_time + sharpNonEmptyChains k + 2 * k + 1`
for Theorem 5.3 (bridge) (`= 5 B_time + 7, 45 B_time + 49, 346 B_time + 352` at `k = 1, 2, 3`). -/
noncomputable def tightBridgeRefCells (k : ℕ) (C α : ℝ) : ℕ :=
  sharpFamCount k * tightBtime (sharpFamCount k) C α + sharpNonEmptyChains k + 2 * k + 1

/-- **`ρ₀_tight(k, C, α)`:**
`2 / (5 * tightBridgeRefCells k C α) = Ω(α / (sharpFamCount(k)² * C))`, improving `genieBridge_rho0`
at `k = 2, C = α = 1` from `10 ^ (-65.75)` to **`9.76 × 10 ^ (-5)` (`10 ^ (-4.01)`)**! -/
noncomputable def tightBridgeRho0 (k : ℕ) (C α : ℝ) : ℝ :=
  2 / (5 * (tightBridgeRefCells k C α : ℝ))

theorem tightBridgeRho0_pos (k : ℕ) (C α : ℝ) :
    0 < tightBridgeRho0 k C α := by
  unfold tightBridgeRho0 tightBridgeRefCells
  positivity

end SharpChainsAndSingleCellGuard

/-! ## §4. Single-Cell Guard Core & `2 ^ k` Phase-Exit Chain Sharpness (`Targets K.1 & K.2`) -/

section SingleCellGuardBridgeCore

/-- Unit-multiplicity cut-valid tape model on `M_work = k + 1` phases (`σ_ph γ = γ.1`):
crossing boundary `m < k` is witnessed on tape `m : Fin k`. -/
def unitValidTapes (k : ℕ) (γ' _γ : Fin (k + 1)) : Finset (Fin k) :=
  if h : γ'.1 < k then {⟨γ'.1, h⟩} else ∅

/-- **Sharpness Witness for `2 ^ Ω(k)` Phase-Exit Chains:**
Even with `k` simple unit-multiplicity phase boundaries (`M_work = k + 1`, `σ_ph γ = γ.1`),
there are **exactly `2 ^ n`** cut-valid phase-exit chains starting at phase `n < k + 1`
(hence **`2 ^ k`** from the top phase `n = k`, indexed by arbitrary subsets `S ⊆ Fin k` of
visited intermediate phases). Thus singly-exponential `2 ^ Θ(k)` chain multiplicity is intrinsic
to phase-exit pullback. -/
theorem card_cutValidStepsAux_unitValidTapes_eq_pow_two (k : ℕ) :
    ∀ (n : ℕ) (hn : n < k + 1),
      (cutValidStepsAux (k + 1) k (unitValidTapes k) n hn).card = 2 ^ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · rw [cutValidStepsAux]
      simp
    · let stepImg : {m // m ∈ range n} → Finset (List (Fin (k + 1) × Fin k)) := fun ⟨m, hm⟩ =>
        have hm_lt : m < n := mem_range.mp hm
        (unitValidTapes k ⟨m, hm_lt.trans hn⟩ ⟨n, hn⟩).biUnion fun j =>
          (cutValidStepsAux (k + 1) k (unitValidTapes k) m (hm_lt.trans hn)).image
            fun rest => (⟨m, hm_lt.trans hn⟩, j) :: rest
      have hS_eq : cutValidStepsAux (k + 1) k (unitValidTapes k) n hn =
          insert [] ((Finset.attach (range n)).biUnion stepImg) := by
        rw [cutValidStepsAux]
      have hnil_not : [] ∉ (Finset.attach (range n)).biUnion stepImg := by
        intro hmem
        obtain ⟨⟨m, hm⟩, _, hmem2⟩ := mem_biUnion.mp hmem
        obtain ⟨j, _, hmem3⟩ := mem_biUnion.mp hmem2
        obtain ⟨rest, _, heq⟩ := mem_image.mp hmem3
        exact List.cons_ne_nil _ _ heq
      have hdisj : Set.PairwiseDisjoint (Finset.attach (range n) : Set {m // m ∈ range n}) stepImg := by
        intro ⟨m₁, hm₁⟩ _ ⟨m₂, hm₂⟩ _ hne
        refine Finset.disjoint_left.mpr fun l hl₁ hl₂ => hne (Subtype.ext ?_)
        obtain ⟨j₁, _, hr₁⟩ := mem_biUnion.mp hl₁
        obtain ⟨rest₁, _, heq₁⟩ := mem_image.mp hr₁
        obtain ⟨j₂, _, hr₂⟩ := mem_biUnion.mp hl₂
        obtain ⟨rest₂, _, heq₂⟩ := mem_image.mp hr₂
        rw [← heq₂] at heq₁
        injection heq₁ with hhd _
        exact congrArg (fun p : Fin (k + 1) × Fin k => p.1.1) hhd
      have hcard_m : ∀ x ∈ Finset.attach (range n), (stepImg x).card = 2 ^ x.1 := by
        rintro ⟨m, hm⟩ _
        have hm_lt : m < n := mem_range.mp hm
        have hm_k : m < k := by omega
        have hvt : unitValidTapes k ⟨m, hm_lt.trans hn⟩ ⟨n, hn⟩ = {⟨m, hm_k⟩} := by
          unfold unitValidTapes
          simp [hm_k]
        dsimp only [stepImg]
        rw [hvt, Finset.singleton_biUnion]
        have hinj : Function.Injective
            (fun rest : List (Fin (k + 1) × Fin k) => (⟨m, hm_lt.trans hn⟩, ⟨m, hm_k⟩) :: rest) :=
          fun _ _ h => (List.cons.inj h).2
        rw [card_image_of_injective _ hinj]
        exact ih m hm_lt (hm_lt.trans hn)
      have hpow_sum : ∀ r : ℕ, 1 + ∑ m ∈ range r, 2 ^ m = 2 ^ r := by
        intro r
        induction r with
        | zero => simp
        | succ r ihr =>
          rw [sum_range_succ, ← add_assoc, ihr, Nat.pow_succ]
          omega
      rw [hS_eq, card_insert_of_notMem hnil_not, card_biUnion hdisj]
      have hsum_eq : ∑ x ∈ Finset.attach (range n), (stepImg x).card = ∑ m ∈ range n, 2 ^ m := by
        calc ∑ x ∈ Finset.attach (range n), (stepImg x).card
            = ∑ x ∈ Finset.attach (range n), 2 ^ x.1 := sum_congr rfl hcard_m
          _ = ∑ m ∈ range n, 2 ^ m := sum_attach (range n) (fun m => 2 ^ m)
      rw [hsum_eq, Nat.add_comm _ 1, hpow_sum n]

/-- **`s`-Independent Path-to-`FollowsChain` Extraction (`Step A of Single-Cell Guard`):**
Any dependency path avoiding `PhaseGuard := {θ_lo γ : 0 < θ_lo γ}.biUnion (microHopStepGuard τ₀ T H)`
follows a cut-valid phase-exit chain `steps ∈ cutValidStepsAux M_work k validTapes (ph t₀).1 (ph t₀).2`! -/
private theorem exists_followsChain_of_phaseGuardFree {k M_work T H : ℕ} (τ₀ : Trace k)
    {θ_pos θ_neg : Fin k → ℕ}
    (θ_lo θ_hi : Fin M_work → ℕ) (ph : ℕ → Fin M_work)
    (validTapes : Fin M_work → Fin M_work → Finset (Fin k))
    (hsep_ph : ∀ c₁ c₂ : Fin M_work, c₁.1 < c₂.1 → θ_hi c₁ ≤ θ_lo c₂)
    (hno_cut : ∀ (γ : Fin M_work) (j : Fin k),
      ¬ (θ_lo γ < θ_pos j ∧ θ_pos j < θ_hi γ) ∧
      ¬ (θ_lo γ < θ_neg j ∧ θ_neg j < θ_hi γ))
    (hph_mem : ∀ t : ℕ, t < T → t ∈ Ico (θ_lo (ph t)) (θ_hi (ph t)))
    (hph_mono : ∀ t₁ t₂ : ℕ, t₁ ≤ t₂ → t₂ < T → (ph t₁).1 ≤ (ph t₂).1)
    (hvt_mem : ∀ (γ' γ : Fin M_work) (j : Fin k), γ'.1 < γ.1 →
      ((θ_hi γ' ≤ θ_pos j ∧ θ_pos j ≤ θ_lo γ) ∨ (θ_hi γ' ≤ θ_neg j ∧ θ_neg j ≤ θ_lo γ)) →
      j ∈ validTapes γ' γ) :
    ∀ (ρ_suf : List ℕ) (t₀ : ℕ),
      t₀ < T →
      IsDepPath τ₀.work T (t₀ :: ρ_suf) →
      (∀ w ∈ ρ_suf, w ∉
        (((univ : Finset (Fin M_work)).filter fun γ => 0 < θ_lo γ).image θ_lo).biUnion
          (microHopStepGuard τ₀ T H)) →
      (∀ l₁ l₂ : List ℕ, ∀ u v : ℕ, t₀ :: ρ_suf = l₁ ++ u :: v :: l₂ →
        u = v + 1 ∨
        (∃ j : Fin k, IsHop (τ₀.work j) T v u ∧
          ∀ t ∈ Ioo v u, |τ₀.work j t - τ₀.work j v| ≤ ((2 * H : ℕ) : ℤ)) ∨
        (∃ j : Fin k, IsNonCrossingLargeHop (τ₀.work j) T (2 * H) v u ∧
          ((v < θ_pos j ∧ θ_pos j ≤ u) ∨ (v < θ_neg j ∧ θ_neg j ≤ u)))) →
      ∃ steps ∈ cutValidStepsAux M_work k validTapes (ph t₀).1 (ph t₀).2,
        FollowsChain τ₀ T H θ_lo θ_hi (ph t₀) steps t₀ ρ_suf
  | [], t₀, ht₀, _, _, _ =>
    ⟨[], nil_mem_cutValidStepsAux M_work k validTapes (ph t₀).1 (ph t₀).2,
      FollowsChain.nil (hph_mem t₀ ht₀)⟩
  | v :: ρ₁, t₀, ht₀, ⟨hstep, hdep₁⟩, hpguard, hdich_suf => by
    have hv_lt : v < t₀ := (depStep_lt hstep).1
    have hv_T : v < T := lt_trans hv_lt ht₀
    have hdich_0 := hdich_suf [] ρ₁ t₀ v rfl
    have hph_le : (ph v).1 ≤ (ph t₀).1 := hph_mono v t₀ (le_of_lt hv_lt) ht₀
    obtain ⟨rest, hrest_mem, hfol_rest⟩ :=
      exists_followsChain_of_phaseGuardFree τ₀ θ_lo θ_hi ph validTapes
        hsep_ph hno_cut hph_mem hph_mono hvt_mem ρ₁ v hv_T hdep₁
        (fun w hw => hpguard w (List.mem_cons_of_mem v hw))
        (fun l₁ l₂ u' v' hsp => hdich_suf (t₀ :: l₁) l₂ u' v' (by simp [hsp]))
    have ht₀_ico := hph_mem t₀ ht₀
    have hv_ico := hph_mem v hv_T
    rcases eq_or_lt_of_le hph_le with heq_ph | hlt_ph
    · have hph_eq : ph v = ph t₀ := Fin.ext heq_ph
      have hv_ico' : v ∈ Ico (θ_lo (ph t₀)) (θ_hi (ph t₀)) := hph_eq ▸ hv_ico
      have hedge : t₀ = v + 1 ∨
          (∃ j : Fin k, IsHop (τ₀.work j) T v t₀ ∧
            ∀ t ∈ Ioo v t₀, |τ₀.work j t - τ₀.work j v| ≤ ((2 * H : ℕ) : ℤ)) := by
        rcases hdich_0 with h1 | h2 | ⟨j, _, hstrad⟩
        · exact Or.inl h1
        · exact Or.inr h2
        · exfalso
          obtain ⟨h1, h2⟩ := mem_Ico.mp ht₀_ico
          obtain ⟨h3, h4⟩ := mem_Ico.mp hv_ico'
          rcases hstrad with ⟨hs1, hs2⟩ | ⟨hs1, hs2⟩
          · exact (hno_cut (ph t₀) j).1 ⟨by omega, by omega⟩
          · exact (hno_cut (ph t₀) j).2 ⟨by omega, by omega⟩
      have hrest_mem' : rest ∈ cutValidStepsAux M_work k validTapes (ph t₀).1 (ph t₀).2 := by
        simpa [heq_ph] using hrest_mem
      have hfol_rest' : FollowsChain τ₀ T H θ_lo θ_hi (ph t₀) rest v ρ₁ := by
        simpa [hph_eq] using hfol_rest
      exact ⟨rest, hrest_mem', FollowsChain.intra ht₀_ico hv_ico' hedge hfol_rest'⟩
    · have hsep_cur : θ_hi (ph v) ≤ θ_lo (ph t₀) := hsep_ph (ph v) (ph t₀) hlt_ph
      obtain ⟨hlo_v, hhi_v⟩ := mem_Ico.mp hv_ico
      obtain ⟨hlo_t₀, hhi_t₀⟩ := mem_Ico.mp ht₀_ico
      have hlo_pos : 0 < θ_lo (ph t₀) := by omega
      have hv_not_guard : v ∉ microHopStepGuard τ₀ T H (θ_lo (ph t₀)) := by
        intro hg
        refine hpguard v List.mem_cons_self (mem_biUnion.mpr ⟨θ_lo (ph t₀), ?_, hg⟩)
        exact mem_image_of_mem θ_lo (mem_filter.mpr ⟨mem_univ (ph t₀), hlo_pos⟩)
      have hlo_ne : θ_lo (ph t₀) ≠ 0 := by omega
      rcases hdich_0 with heq_t₀ | ⟨j, hhop, hsmall⟩ | ⟨j, hnc, hstrad⟩
      · exfalso
        have hv_eq : v = θ_lo (ph t₀) - 1 := by omega
        apply hv_not_guard
        unfold microHopStepGuard
        simp only [hlo_ne, ↓reduceIte, hv_eq]
        exact mem_insert_self _ _
      · exfalso
        apply hv_not_guard
        unfold microHopStepGuard
        simp only [hlo_ne, ↓reduceIte]
        refine mem_insert_of_mem (mem_biUnion.mpr ⟨j, mem_univ j, ?_⟩)
        unfold smallCrossingLowers
        exact mem_filter.mpr ⟨mem_range.mpr hv_T, by omega, t₀, by omega, hhop, hsmall⟩
      · have hj_vt : j ∈ validTapes (ph v) (ph t₀) := by
          apply hvt_mem (ph v) (ph t₀) j hlt_ph
          rcases hstrad with ⟨hs1, hs2⟩ | ⟨hs1, hs2⟩
          · left
            have hge1 : θ_hi (ph v) ≤ θ_pos j := by
              by_contra hlt1; push Not at hlt1
              exact (hno_cut (ph v) j).1 ⟨by omega, hlt1⟩
            have hle2 : θ_pos j ≤ θ_lo (ph t₀) := by
              by_contra hgt2; push Not at hgt2
              exact (hno_cut (ph t₀) j).1 ⟨hgt2, by omega⟩
            exact ⟨hge1, hle2⟩
          · right
            have hge1 : θ_hi (ph v) ≤ θ_neg j := by
              by_contra hlt1; push Not at hlt1
              exact (hno_cut (ph v) j).2 ⟨by omega, hlt1⟩
            have hle2 : θ_neg j ≤ θ_lo (ph t₀) := by
              by_contra hgt2; push Not at hgt2
              exact (hno_cut (ph t₀) j).2 ⟨hgt2, by omega⟩
            exact ⟨hge1, hle2⟩
        have hcons_mem : (ph v, j) :: rest ∈ cutValidStepsAux M_work k validTapes (ph t₀).1 (ph t₀).2 :=
          cons_mem_cutValidStepsAux M_work k validTapes hlt_ph (ph t₀).2 hj_vt hrest_mem
        exact ⟨(ph v, j) :: rest, hcons_mem, FollowsChain.inter hlt_ph ht₀_ico hv_ico hnc hfol_rest⟩

/-- Explicit small dimension threshold `d₀` for Theorem 5.3 (bridge) (`100%` independent of `D` and `H`!):
`tightBridge_d0(2, 1, 1) = 81905` (`vs tower-type previously`). -/
noncomputable def tightBridge_d0 (k : ℕ) (C α : ℝ) : ℕ :=
  ⌈10 * (sharpFamCount k : ℝ) * (2 * (tightBtime (sharpFamCount k) C α : ℝ) + 2) / α + 5⌉₊

theorem tightBridgeRho0_le_two_fifteenths_of_le_one (k : ℕ) {C α : ℝ}
    (hC : 1 ≤ C) (hα0 : 0 < α) (hα1 : α ≤ 1) :
    tightBridgeRho0 k C α ≤ 2 / 15 := by
  unfold tightBridgeRho0 tightBridgeRefCells
  have hm1 : (1 : ℝ) ≤ (sharpFamCount k : ℝ) := by exact_mod_cast sharpFamCount_pos k
  have hB_ge2 : 2 ≤ tightBtime (sharpFamCount k) C α := by
    unfold tightBtime
    have hge2 : (2 : ℝ) ≤ 2 * (sharpFamCount k : ℝ) * C / α := by
      rw [le_div_iff₀ hα0]
      nlinarith
    exact_mod_cast (hge2.trans (Nat.le_ceil _))
  have hm_nat : 1 ≤ sharpFamCount k := sharpFamCount_pos k
  have hcells_ge3 : 3 ≤ sharpFamCount k * tightBtime (sharpFamCount k) C α +
      sharpNonEmptyChains k + 2 * k + 1 := by
    nlinarith
  have hcells_r : (3 : ℝ) ≤ (sharpFamCount k * tightBtime (sharpFamCount k) C α +
      sharpNonEmptyChains k + 2 * k + 1 : ℕ) := by exact_mod_cast hcells_ge3
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  linarith

private theorem tightBridgeRho0_density_step {k T d b R_cells U_card V_card : ℕ} {C α : ℝ}
    (hd : 1 ≤ d) (hb : 1 ≤ b) (hC : 1 ≤ C) (hα0 : 0 < α)
    (hT : (T : ℝ) ≤ C * (((d * d * b : ℕ) : ℝ) + 1))
    (hV₀ : α * ((d * d * b : ℕ) : ℝ) ≤ (V_card : ℝ))
    (hV_le : V_card ≤ d * d * b)
    (hd_thresh : tightBridge_d0 k C α ≤ d)
    (hR_le : R_cells ≤ tightBridgeRefCells k C α)
    (hV_nat : V_card ≤ R_cells * U_card + 0 +
      sharpFamCount k * (T / tightBtime (sharpFamCount k) C α) +
      sharpFamCount k * (2 * tightBtime (sharpFamCount k) C α + 2) * (d * b)) :
    tightBridgeRho0 k C α * (V_card : ℝ) ≤ (U_card : ℝ) := by
  set m_fam := sharpFamCount k
  set B_time := tightBtime m_fam C α
  have hm_pos : 1 ≤ m_fam := sharpFamCount_pos k
  have hm_r : (1 : ℝ) ≤ (m_fam : ℝ) := by exact_mod_cast hm_pos
  have hL_pos : 1 ≤ d * d * b := Nat.mul_pos (Nat.mul_pos hd hd) hb
  have hW_pos : 1 ≤ d * b := Nat.mul_pos hd hb
  have hW_r : (1 : ℝ) ≤ ((d * b : ℕ) : ℝ) := by exact_mod_cast hW_pos
  have hB_pos : 1 ≤ B_time := Nat.ceil_pos.mpr (by positivity)
  have hB_rpos : (0 : ℝ) < (B_time : ℝ) := by exact_mod_cast hB_pos
  have hα_le_1 : α ≤ 1 := by
    have hVr_le : (V_card : ℝ) ≤ ((d * d * b : ℕ) : ℝ) := by exact_mod_cast hV_le
    have hL_rpos : (0 : ℝ) < ((d * d * b : ℕ) : ℝ) := by exact_mod_cast hL_pos
    exact le_of_mul_le_mul_right (by linarith) hL_rpos
  have hB_ge : 2 * (m_fam : ℝ) * C / α ≤ (B_time : ℝ) := Nat.le_ceil _
  have hB_mul : 2 * (m_fam : ℝ) * C ≤ α * (B_time : ℝ) := by
    have := (div_le_iff₀ hα0).mp hB_ge
    linarith
  have hdiv_le : ((T / B_time : ℕ) : ℝ) ≤ (T : ℝ) / (B_time : ℝ) := by
    rw [le_div_iff₀ hB_rpos]
    exact_mod_cast Nat.div_mul_le_self T B_time
  have hmT_le : (m_fam : ℝ) * ((T / B_time : ℕ) : ℝ) ≤ (V_card : ℝ) / 2 + α / 2 := by
    have h1 : 2 * (m_fam : ℝ) * (T : ℝ) ≤ 2 * (m_fam : ℝ) * C * (((d * d * b : ℕ) : ℝ) + 1) := by
      nlinarith
    have h2 : 2 * (m_fam : ℝ) * C * (((d * d * b : ℕ) : ℝ) + 1) ≤
        α * (B_time : ℝ) * (((d * d * b : ℕ) : ℝ) + 1) :=
      mul_le_mul_of_nonneg_right hB_mul (by positivity)
    have h4 : α * (B_time : ℝ) * (((d * d * b : ℕ) : ℝ) + 1) ≤
        (B_time : ℝ) * (V_card : ℝ) + α * (B_time : ℝ) := by nlinarith
    have h5 : (m_fam : ℝ) * ((T : ℝ) / (B_time : ℝ)) ≤ (V_card : ℝ) / 2 + α / 2 := by
      rw [mul_div_assoc', div_le_iff₀ hB_rpos]
      linarith
    exact (mul_le_mul_of_nonneg_left hdiv_le (by positivity)).trans h5
  have hd_ge_r : 10 * (m_fam : ℝ) * (2 * (B_time : ℝ) + 2) / α + 5 ≤ (d : ℝ) := by
    unfold tightBridge_d0 at hd_thresh
    exact (Nat.le_ceil _).trans (by exact_mod_cast hd_thresh)
  have herr_d : 10 * (m_fam : ℝ) * (2 * (B_time : ℝ) + 2) + 5 * α ≤ α * (d : ℝ) := by
    have hsub : 10 * (m_fam : ℝ) * (2 * (B_time : ℝ) + 2) / α ≤ (d : ℝ) - 5 := by linarith
    have := (div_le_iff₀ hα0).mp hsub
    linarith
  have herr_W : (m_fam : ℝ) * (2 * (B_time : ℝ) + 2) * ((d * b : ℕ) : ℝ) + α / 2 ≤
      (1 / 10 : ℝ) * (V_card : ℝ) := by
    have hα_half_W : α / 2 ≤ (α / 2) * ((d * b : ℕ) : ℝ) := by nlinarith
    have hL_eq : ((d * d * b : ℕ) : ℝ) = (d : ℝ) * ((d * b : ℕ) : ℝ) := by push_cast; ring
    have hmul_W := mul_le_mul_of_nonneg_right herr_d (by positivity : (0 : ℝ) ≤ ((d * b : ℕ) : ℝ))
    have hV_ge : α * ((d : ℝ) * ((d * b : ℕ) : ℝ)) ≤ (V_card : ℝ) := by rw [← hL_eq]; exact hV₀
    nlinarith
  have hV_r : (V_card : ℝ) ≤ (R_cells : ℝ) * (U_card : ℝ) +
      (m_fam : ℝ) * ((T / B_time : ℕ) : ℝ) +
      (m_fam : ℝ) * (2 * (B_time : ℝ) + 2) * ((d * b : ℕ) : ℝ) := by
    have hcast : (V_card : ℝ) ≤ ((R_cells * U_card + 0 +
        m_fam * (T / B_time) + m_fam * (2 * B_time + 2) * (d * b) : ℕ) : ℝ) := by
      exact_mod_cast hV_nat
    simpa [Nat.cast_add, Nat.cast_mul] using hcast
  have htwo_fifths : (2 / 5 : ℝ) * (V_card : ℝ) ≤ (R_cells : ℝ) * (U_card : ℝ) := by linarith
  have hcells_r : (R_cells : ℝ) ≤ (tightBridgeRefCells k C α : ℝ) := by exact_mod_cast hR_le
  have hcells_mul : (2 / 5 : ℝ) * (V_card : ℝ) ≤ (tightBridgeRefCells k C α : ℝ) * (U_card : ℝ) :=
    htwo_fifths.trans (mul_le_mul_of_nonneg_right hcells_r (by positivity))
  have hrc_pos : (0 : ℝ) < 5 * (tightBridgeRefCells k C α : ℝ) := by
    unfold tightBridgeRefCells; positivity
  unfold tightBridgeRho0
  rw [div_mul_eq_mul_div, div_le_iff₀ hrc_pos]
  linarith

/-- **Core Zero-Genie Single-Cell Guard Bridge Theorem (`Targets K.1 & K.2` Main Engine):**
On **any** `k`-tape trace `τ₀` (`zero TransposesAt hypothesis!`), for **any** `D, H, ηInv, L_cap : ℕ`
and `d ≥ tightBridge_d0 k C α` (`completely independent of D and H!`), if `B` `D`-separates `V₀`
(`|V₀| ≥ α * L`) from `crossingLowerEtaSteps τ₀ T H ηInv L_cap` under `ClauseE1H`, then there exist:
1. a **single-cell micro-hop guard** `X_cell : Finset ℕ` of size
   `X_cell.card ≤ sharpCellGuardThresh k * (4 * k * H + k + 1)` (`zero (k + 2)^D blow-up!`), and
2. a subset `U ⊆ V₀` with **zero internal arcs** (`both IsIndependent and IsAcyclicIn`) in
   `ballAvoidSystem τ₀ T D (B ∪ X_cell) d b` of density `|U| ≥ tightBridgeRho0 k C α * |V₀|`! -/
theorem exists_singleCell_guard_isIndependent_crossingLowerH
    {k T d b D H ηInv L_cap : ℕ} {C α : ℝ}
    (τ₀ : Trace k) (hd : 1 ≤ d) (hb : 1 ≤ b) (hC : 1 ≤ C) (hα0 : 0 < α)
    (hlen : (appendList τ₀ T).length = d * d * b)
    (hT : (T : ℝ) ≤ C * (((d * d * b : ℕ) : ℝ) + 1))
    (V₀ : Finset (Fin (d * d * b))) (B : Finset ℕ)
    (hV₀ : α * ((d * d * b : ℕ) : ℝ) ≤ (V₀.card : ℝ))
    (hd_thresh : tightBridge_d0 k C α ≤ d)
    (hsep : IsBallPathSeparator τ₀ T D d b V₀ (crossingLowerEtaSteps τ₀ T H ηInv L_cap) B)
    (hE1 : ClauseE1H τ₀ T D d b H ηInv L_cap V₀ B) :
    ∃ (X_cell : Finset ℕ) (U : Finset (Fin (d * d * b))),
      X_cell.card ≤ sharpCellGuardThresh k * (4 * k * H + k + 1) ∧
      U ⊆ V₀ ∧
      DirectedRecovery.IsIndependent (ballAvoidSystem τ₀ T D (B ∪ X_cell) d b) U ∧
      HalfRate.IsAcyclicIn (ballAvoidSystem τ₀ T D (B ∪ X_cell) d b) U ∧
      tightBridgeRho0 k C α * (V₀.card : ℝ) ≤ (U.card : ℝ) := by
  let L := d * d * b
  let m_fam := sharpFamCount k
  let B_time := tightBtime m_fam C α
  have hm_pos : 1 ≤ m_fam := sharpFamCount_pos k
  have hm_r : (1 : ℝ) ≤ (m_fam : ℝ) := by exact_mod_cast hm_pos
  have hL_pos : 1 ≤ L := Nat.mul_pos (Nat.mul_pos hd hd) hb
  have hT_pos : 1 ≤ T := by
    have hlast_lt : L - 1 < (appendList τ₀ T).length := by rw [hlen]; omega
    have hot_lt : appendTime τ₀ T (L - 1) < T := appendTime_lt τ₀ T hlast_lt
    omega
  have hB_pos : 1 ≤ B_time := by
    change 1 ≤ ⌈2 * (m_fam : ℝ) * C / α⌉₊
    exact Nat.ceil_pos.mpr (by positivity)
  -- Step 1: Dichotomy & cut-weighted work-phase partition.
  obtain ⟨θ_pos, θ_neg, hθ_le, hdich_all⟩ :=
    depPath_nonCrossing_dichotomy_of_isBallPathSeparator_crossingLowerH τ₀ T D d b H ηInv L_cap
      V₀ B hsep hE1
  obtain ⟨M_work, f, ph, hM_ge, hM_le, hf_mono, hf0, hfM, hint_mem, hcut_surj,
      hlo_lt_hi, hsep_ph, hno_cut, hph_mem, hph_mono⟩ :=
    exists_workPhase_partition_with_cuts hT_pos θ_pos θ_neg hθ_le
  let θ_lo : Fin M_work → ℕ := fun γ => f ⟨γ.1, by omega⟩
  let θ_hi : Fin M_work → ℕ := fun γ => f ⟨γ.1 + 1, by omega⟩
  have hlo_le_hi : ∀ c : Fin M_work, θ_lo c ≤ θ_hi c := fun c => le_of_lt (hlo_lt_hi c).1
  -- Step 2: Cumulative signed-cut weights `σ_ph : Fin M_work → ℕ` and `validTapes`.
  let posCutAt : Fin (M_work + 1) → Finset (Fin k) := fun i =>
    (univ : Finset (Fin k)).filter fun j => θ_pos j = f i
  let negCutAt : Fin (M_work + 1) → Finset (Fin k) := fun i =>
    (univ : Finset (Fin k)).filter fun j => θ_neg j = f i
  let w_cut : ℕ → ℕ := fun i =>
    if hi : i < M_work + 1 then (posCutAt ⟨i, hi⟩).card + (negCutAt ⟨i, hi⟩).card else 0
  let σ_ph : Fin M_work → ℕ := fun γ => ∑ i ∈ Ico 1 (γ.1 + 1), w_cut i
  let validTapes : Fin M_work → Fin M_work → Finset (Fin k) := fun γ' γ =>
    (univ : Finset (Fin k)).filter fun j =>
      (θ_hi γ' ≤ θ_pos j ∧ θ_pos j ≤ θ_lo γ) ∨ (θ_hi γ' ≤ θ_neg j ∧ θ_neg j ≤ θ_lo γ)
  have hw_pos : ∀ i : ℕ, 1 ≤ i → i < M_work → 1 ≤ w_cut i := by
    intro i hi1 hiM
    have hi_lt : i < M_work + 1 := by omega
    dsimp only [w_cut]
    simp only [hi_lt, ↓reduceDIte]
    rcases hint_mem ⟨i, hi_lt⟩ hi1 hiM with ⟨j, hj⟩ | ⟨j, hj⟩
    · have hne : (posCutAt ⟨i, hi_lt⟩).Nonempty := ⟨j, mem_filter.mpr ⟨mem_univ j, hj⟩⟩
      have := hne.card_pos; omega
    · have hne : (negCutAt ⟨i, hi_lt⟩).Nonempty := ⟨j, mem_filter.mpr ⟨mem_univ j, hj⟩⟩
      have := hne.card_pos; omega
  have hσ_mono : ∀ c₁ c₂ : Fin M_work, c₁.1 < c₂.1 → σ_ph c₁ < σ_ph c₂ := by
    intro c₁ c₂ hlt
    dsimp only [σ_ph]
    have hsplit : Ico 1 (c₂.1 + 1) = Ico 1 (c₁.1 + 1) ∪ Ico (c₁.1 + 1) (c₂.1 + 1) :=
      (Ico_union_Ico_eq_Ico (by omega) (by omega)).symm
    have hdisj : Disjoint (Ico 1 (c₁.1 + 1)) (Ico (c₁.1 + 1) (c₂.1 + 1)) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2; simp only [mem_Ico] at hx1 hx2; omega
    rw [hsplit, sum_union hdisj]
    have hmem : c₁.1 + 1 ∈ Ico (c₁.1 + 1) (c₂.1 + 1) := mem_Ico.mpr ⟨le_rfl, by omega⟩
    have hge1 : 1 ≤ ∑ i ∈ Ico (c₁.1 + 1) (c₂.1 + 1), w_cut i := by
      calc 1 ≤ w_cut (c₁.1 + 1) := hw_pos (c₁.1 + 1) (by omega) (by omega)
        _ ≤ ∑ i ∈ Ico (c₁.1 + 1) (c₂.1 + 1), w_cut i :=
            single_le_sum (fun _ _ => Nat.zero_le _) hmem
    omega
  have hpos_sum_le : ∑ i : Fin (M_work + 1), (posCutAt i).card ≤ k := by
    have hdisj : Set.PairwiseDisjoint ((univ : Finset (Fin (M_work + 1))) : Set (Fin (M_work + 1))) posCutAt := by
      intro i₁ _ i₂ _ hne
      refine Finset.disjoint_left.mpr fun j hj₁ hj₂ => hne ?_
      exact hf_mono.injective ((mem_filter.mp hj₁).2.symm.trans (mem_filter.mp hj₂).2)
    rw [← card_biUnion hdisj]
    exact (card_le_card (subset_univ _)).trans_eq (by simp)
  have hneg_sum_le : ∑ i : Fin (M_work + 1), (negCutAt i).card ≤ k := by
    have hdisj : Set.PairwiseDisjoint ((univ : Finset (Fin (M_work + 1))) : Set (Fin (M_work + 1))) negCutAt := by
      intro i₁ _ i₂ _ hne
      refine Finset.disjoint_left.mpr fun j hj₁ hj₂ => hne ?_
      exact hf_mono.injective ((mem_filter.mp hj₁).2.symm.trans (mem_filter.mp hj₂).2)
    rw [← card_biUnion hdisj]
    exact (card_le_card (subset_univ _)).trans_eq (by simp)
  have hσ_le : ∀ γ : Fin M_work, σ_ph γ ≤ 2 * k := by
    intro γ
    let emb : {x // x ∈ Ico 1 (γ.1 + 1)} → Fin (M_work + 1) :=
      fun x => ⟨x.1, lt_of_lt_of_le (mem_Ico.mp x.2).2 (by omega)⟩
    have hemb_inj : Set.InjOn emb (Finset.attach (Ico 1 (γ.1 + 1)) : Set _) := by
      intro x₁ _ x₂ _ h; exact Subtype.ext (congrArg Fin.val h)
    have hsum_eq : σ_ph γ = ∑ x ∈ Finset.attach (Ico 1 (γ.1 + 1)),
        ((posCutAt (emb x)).card + (negCutAt (emb x)).card) := by
      dsimp only [σ_ph]
      rw [← sum_attach]
      refine sum_congr rfl fun x _ => ?_
      have hx_lt : x.1 < M_work + 1 := lt_of_lt_of_le (mem_Ico.mp x.2).2 (by omega)
      dsimp only [w_cut, emb]
      simp [hx_lt]
    rw [hsum_eq, ← sum_image (f := fun i => (posCutAt i).card + (negCutAt i).card) hemb_inj]
    calc ∑ i ∈ (Finset.attach (Ico 1 (γ.1 + 1))).image emb, ((posCutAt i).card + (negCutAt i).card)
        ≤ ∑ i : Fin (M_work + 1), ((posCutAt i).card + (negCutAt i).card) :=
          sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _
      _ = (∑ i : Fin (M_work + 1), (posCutAt i).card) +
          (∑ i : Fin (M_work + 1), (negCutAt i).card) := sum_add_distrib
      _ ≤ k + k := Nat.add_le_add hpos_sum_le hneg_sum_le
      _ = 2 * k := by ring
  have hvt_card : ∀ c₁ c₂ : Fin M_work, c₁.1 < c₂.1 →
      (validTapes c₁ c₂).card ≤ min k (σ_ph c₂ - σ_ph c₁) := by
    intro c₁ c₂ hlt
    have hk_le : (validTapes c₁ c₂).card ≤ k :=
      (card_le_card (subset_univ _)).trans_eq (by simp)
    refine le_min hk_le ?_
    have hsplit : Ico 1 (c₂.1 + 1) = Ico 1 (c₁.1 + 1) ∪ Ico (c₁.1 + 1) (c₂.1 + 1) :=
      (Ico_union_Ico_eq_Ico (by omega) (by omega)).symm
    have hdisj : Disjoint (Ico 1 (c₁.1 + 1)) (Ico (c₁.1 + 1) (c₂.1 + 1)) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2; simp only [mem_Ico] at hx1 hx2; omega
    have hdiff_eq : σ_ph c₂ - σ_ph c₁ = ∑ i ∈ Ico (c₁.1 + 1) (c₂.1 + 1), w_cut i := by
      dsimp only [σ_ph]
      rw [hsplit, sum_union hdisj]
      omega
    rw [hdiff_eq]
    have hsub : validTapes c₁ c₂ ⊆
        (Finset.attach (Ico (c₁.1 + 1) (c₂.1 + 1))).biUnion fun x =>
          have hx_lt : x.1 < M_work + 1 := lt_of_lt_of_le (mem_Ico.mp x.2).2 (by omega)
          posCutAt ⟨x.1, hx_lt⟩ ∪ negCutAt ⟨x.1, hx_lt⟩ := by
      intro j hj
      rcases (mem_filter.mp hj).2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · obtain ⟨i_j, hi_eq⟩ := hcut_surj (θ_pos j) (mem_union_left _ (mem_image_of_mem _ (mem_univ j)))
        have hi_lo : c₁.1 + 1 ≤ i_j.1 := by
          by_contra hlt_i; push Not at hlt_i
          have := hf_mono (show i_j < ⟨c₁.1 + 1, by omega⟩ from hlt_i)
          dsimp [θ_hi] at h1; omega
        have hi_hi : i_j.1 < c₂.1 + 1 := by
          by_contra hge_i; push Not at hge_i
          have := hf_mono (show (⟨c₂.1, by omega⟩ : Fin (M_work + 1)) < i_j from hge_i)
          dsimp [θ_lo] at h2; omega
        have hi_ico : i_j.1 ∈ Ico (c₁.1 + 1) (c₂.1 + 1) := mem_Ico.mpr ⟨hi_lo, hi_hi⟩
        refine mem_biUnion.mpr ⟨⟨i_j.1, hi_ico⟩, mem_attach _ _, ?_⟩
        exact mem_union_left _ (mem_filter.mpr ⟨mem_univ j, hi_eq.symm⟩)
      · obtain ⟨i_j, hi_eq⟩ := hcut_surj (θ_neg j) (mem_union_right _ (mem_image_of_mem _ (mem_univ j)))
        have hi_lo : c₁.1 + 1 ≤ i_j.1 := by
          by_contra hlt_i; push Not at hlt_i
          have := hf_mono (show i_j < ⟨c₁.1 + 1, by omega⟩ from hlt_i)
          dsimp [θ_hi] at h1; omega
        have hi_hi : i_j.1 < c₂.1 + 1 := by
          by_contra hge_i; push Not at hge_i
          have := hf_mono (show (⟨c₂.1, by omega⟩ : Fin (M_work + 1)) < i_j from hge_i)
          dsimp [θ_lo] at h2; omega
        have hi_ico : i_j.1 ∈ Ico (c₁.1 + 1) (c₂.1 + 1) := mem_Ico.mpr ⟨hi_lo, hi_hi⟩
        refine mem_biUnion.mpr ⟨⟨i_j.1, hi_ico⟩, mem_attach _ _, ?_⟩
        exact mem_union_right _ (mem_filter.mpr ⟨mem_univ j, hi_eq.symm⟩)
    calc (validTapes c₁ c₂).card
        ≤ ((Finset.attach (Ico (c₁.1 + 1) (c₂.1 + 1))).biUnion fun x =>
            posCutAt ⟨x.1, lt_of_lt_of_le (mem_Ico.mp x.2).2 (by omega)⟩ ∪
            negCutAt ⟨x.1, lt_of_lt_of_le (mem_Ico.mp x.2).2 (by omega)⟩).card := card_le_card hsub
      _ ≤ ∑ x ∈ Finset.attach (Ico (c₁.1 + 1) (c₂.1 + 1)),
            (posCutAt ⟨x.1, lt_of_lt_of_le (mem_Ico.mp x.2).2 (by omega)⟩ ∪
             negCutAt ⟨x.1, lt_of_lt_of_le (mem_Ico.mp x.2).2 (by omega)⟩).card := card_biUnion_le
      _ ≤ ∑ x ∈ Finset.attach (Ico (c₁.1 + 1) (c₂.1 + 1)), w_cut x.1 := by
          refine sum_le_sum fun x _ => ?_
          have hx_lt : x.1 < M_work + 1 := lt_of_lt_of_le (mem_Ico.mp x.2).2 (by omega)
          dsimp only [w_cut]
          simp only [hx_lt, ↓reduceDIte]
          exact card_union_le _ _
      _ = ∑ i ∈ Ico (c₁.1 + 1) (c₂.1 + 1), w_cut i := sum_attach _ w_cut
  have hσ_inj : Set.InjOn σ_ph ((univ : Finset (Fin M_work)) : Set (Fin M_work)) := by
    intro c₁ _ c₂ _ heq
    rcases lt_trichotomy c₁.1 c₂.1 with hlt | hv | hgt
    · exact absurd heq (Nat.ne_of_lt (hσ_mono c₁ c₂ hlt))
    · exact Fin.ext hv
    · exact absurd heq (Nat.ne_of_gt (hσ_mono c₂ c₁ hgt))
  have hσ_mem_range : ∀ γ : Fin M_work, σ_ph γ ∈ range (2 * k + 1) :=
    fun γ => mem_range.mpr (Nat.lt_succ_of_le (hσ_le γ))
  -- Step 3: Non-empty cut-valid chains & `ι := Option {c // c ∈ NEChains}` (`|ι| ≤ sharpFamCount k`).
  let NEChains : Finset (Σ _γ₀ : Fin M_work, List (Fin M_work × Fin k)) :=
    (univ : Finset (Fin M_work)).biUnion fun γ₀ =>
      ((cutValidStepsAux M_work k validTapes γ₀.1 γ₀.2).erase []).image fun steps => ⟨γ₀, steps⟩
  have hNE_card : NEChains.card ≤ sharpNonEmptyChains k := by
    calc NEChains.card
        ≤ ∑ γ₀ : Fin M_work,
            (((cutValidStepsAux M_work k validTapes γ₀.1 γ₀.2).erase []).image
              (fun steps => (⟨γ₀, steps⟩ : Σ _ : Fin M_work, List (Fin M_work × Fin k)))).card :=
          card_biUnion_le
      _ ≤ ∑ γ₀ : Fin M_work, (chainCapAt k (σ_ph γ₀) - 1) := by
          refine sum_le_sum fun γ₀ _ => ?_
          exact card_image_le.trans
            (cutValidStepsAux_card_and_nodes_le validTapes σ_ph hσ_mono hvt_card γ₀.1 γ₀.2).2.1
      _ = ∑ r ∈ (univ : Finset (Fin M_work)).image σ_ph, (chainCapAt k r - 1) :=
          (sum_image (f := fun r => chainCapAt k r - 1) hσ_inj).symm
      _ ≤ ∑ r ∈ range (2 * k + 1), (chainCapAt k r - 1) :=
          sum_le_sum_of_subset (image_subset_iff.mpr fun γ _ => hσ_mem_range γ)
      _ = sharpNonEmptyChains k := (sharpNonEmptyChains_eq_sum k).symm
  let ι := Option {c // c ∈ NEChains}
  have hι_card : Fintype.card ι ≤ m_fam := by
    dsimp [ι, m_fam]
    rw [Fintype.card_option, Fintype.card_coe]
    unfold sharpFamCount
    omega
  let ξ : ι → ℕ → ℕ := fun ν r =>
    match ν with
    | none => timeBlockBound T B_time r
    | some c =>
      if chainParity c.1.2 = false then
        pullChainPsi τ₀ T H B_time θ_lo θ_hi c.1.1 c.1.2 r
      else
        pullChainPsi τ₀ T H B_time θ_lo θ_hi c.1.1 c.1.2 (B_time - r)
  let π_perm : ι → Fin B_time → Fin B_time := fun ν β =>
    match ν with
    | none => β
    | some c =>
      if chainParity c.1.2 = false then β else ⟨B_time - 1 - β.1, by omega⟩
  have hξ_mono : ∀ ν : ι, ∀ r₁ r₂ : ℕ, r₁ ≤ r₂ → r₂ ≤ B_time → ξ ν r₁ ≤ ξ ν r₂ := by
    intro ν r₁ r₂ hr₁₂ hr₂B
    cases ν with
    | none => exact timeBlockBound_mono T B_time hr₁₂
    | some c =>
      dsimp only [ξ]
      have hbm := (pullChainPsi_bounds_and_mono τ₀ T H B_time θ_lo θ_hi hlo_le_hi c.1.2 c.1.1).2
      cases hpar : chainParity c.1.2
      · simp only [↓reduceIte]
        have := hbm r₁ r₂ hr₁₂
        simpa [hpar] using this
      · simp only [Bool.true_eq_false, ↓reduceIte]
        have := hbm (B_time - r₂) (B_time - r₁) (by omega)
        simpa [hpar] using this
  have hπ_inj : ∀ ν : ι, Function.Injective (π_perm ν) := by
    intro ν β₁ β₂ heq
    cases ν with
    | none => exact heq
    | some c =>
      dsimp only [π_perm] at heq
      split_ifs at heq
      · exact heq
      · have hv := congrArg Fin.val heq
        dsimp at hv
        exact Fin.ext (by omega)
  -- Step 4: Common refinement `S_ref` (`|S_ref| - 1 ≤ tightBridgeRefCells k C α`) with `Z_bad = ∅`!
  let S_ref : Finset ℕ :=
    (univ : Finset ι).biUnion fun ν =>
      (range (B_time + 1)).image fun r => min T (ξ ν r)
  have htb_zero : timeBlockBound T B_time 0 = 0 := by
    have hB_gt0 : 0 < B_time := hB_pos
    unfold timeBlockBound
    simp only [hB_gt0, ↓reduceIte, Nat.zero_mul]
  have htb_B : timeBlockBound T B_time B_time = T := by
    unfold timeBlockBound
    simp only [lt_self_iff_false, ↓reduceIte]
  have h0_ref : 0 ∈ S_ref := by
    refine mem_biUnion.mpr ⟨none, mem_univ _, ?_⟩
    have h0_eq : min T (ξ none 0) = 0 := by
      dsimp only [ξ]; rw [htb_zero]; exact Nat.min_eq_right (Nat.zero_le T)
    have h0_mem : min T (ξ none 0) ∈ (range (B_time + 1)).image fun r => min T (ξ none r) :=
      mem_image_of_mem _ (mem_range.mpr (by omega))
    rwa [h0_eq] at h0_mem
  have hT_ref : T ∈ S_ref := by
    refine mem_biUnion.mpr ⟨none, mem_univ _, ?_⟩
    have hT_eq : min T (ξ none B_time) = T := by
      dsimp only [ξ]; rw [htb_B]; exact Nat.min_self T
    have hT_mem : min T (ξ none B_time) ∈ (range (B_time + 1)).image fun r => min T (ξ none r) :=
      mem_image_of_mem _ (mem_range.mpr (by omega))
    rwa [hT_eq] at hT_mem
  have hS_le_T : ∀ x ∈ S_ref, x ≤ T := by
    intro x hx
    obtain ⟨ν, _, hx_img⟩ := mem_biUnion.mp hx
    obtain ⟨r, _, rfl⟩ := mem_image.mp hx_img
    exact Nat.min_le_left T _
  have hS_card : S_ref.card ≤ tightBridgeRefCells k C α + 1 := by
    unfold tightBridgeRefCells
    have h1 : S_ref.card ≤ Fintype.card ι * (B_time + 1) := by
      calc S_ref.card
          ≤ ∑ ν : ι, ((range (B_time + 1)).image fun r => min T (ξ ν r)).card := card_biUnion_le
        _ ≤ ∑ _ν : ι, (B_time + 1) :=
            sum_le_sum fun _ _ => card_image_le.trans (by simp)
        _ = Fintype.card ι * (B_time + 1) := by simp
    have hι_eq : Fintype.card ι = 1 + NEChains.card := by
      dsimp [ι]; rw [Fintype.card_option, Fintype.card_coe]; omega
    have h2 : Fintype.card ι * (B_time + 1) = Fintype.card ι * B_time + 1 + NEChains.card := by
      rw [hι_eq]; ring
    have h3 : Fintype.card ι * B_time ≤ sharpFamCount k * B_time :=
      Nat.mul_le_mul_right B_time hι_card
    dsimp [B_time, m_fam] at h1 h2 h3
    omega
  have hξ_ref : ∀ ν : ι, ∀ r : ℕ, r ≤ B_time → min T (ξ ν r) ∈ S_ref := fun ν r hr =>
    mem_biUnion.mpr ⟨ν, mem_univ ν, mem_image_of_mem _ (mem_range.mpr (by omega))⟩
  obtain ⟨a_star, b_star, U_star, ha_lt_b, hb_le_T, _, _, hno_mid, hU_sub, hU_ico, hU_disj, hA_eq, hV_nat⟩ :=
    exists_commonRefinement_cell_core τ₀ hd hb hB_pos hι_card hlen V₀ ∅ S_ref
      h0_ref hT_ref hS_le_T hS_card ξ hξ_mono hξ_ref π_perm hπ_inj
  -- Step 5: Construct the single-cell guard `X_cell` (`depending ONLY on a_star`, never on `q`!).
  have ha_lt_T : a_star < T := lt_of_lt_of_le ha_lt_b hb_le_T
  obtain ⟨β_id, ha_blk_id⟩ := exists_mem_timeBlock_uncond hB_pos ha_lt_T
  obtain ⟨hid_lo_eq, hid_hi_eq⟩ := timeBlock_eq_Ico_bound T B_time β_id
  obtain ⟨hid_lo_le, ha_lt_id_hi⟩ := mem_Ico.mp ha_blk_id
  rw [hid_lo_eq] at hid_lo_le
  rw [hid_hi_eq] at ha_lt_id_hi
  have hb_le_id : b_star ≤ timeBlockBound T B_time (β_id.1 + 1) := by
    have hmem_hi : min T (timeBlockBound T B_time (β_id.1 + 1)) ∈ S_ref :=
      hξ_ref none (β_id.1 + 1) (Nat.succ_le_of_lt β_id.2)
    have hle_T_id : timeBlockBound T B_time (β_id.1 + 1) ≤ T :=
      (timeBlockBound_mono T B_time (Nat.succ_le_of_lt β_id.2)).trans_eq htb_B
    rw [Nat.min_eq_right hle_T_id] at hmem_hi
    by_contra hgt; push Not at hgt
    exact hno_mid _ hmem_hi ⟨ha_lt_id_hi, hgt⟩
  -- Endpoint parameter selector `(s₁, s₂)` for each `(γ₀, steps)`.
  let pairS_ne : {c // c ∈ NEChains} → ℕ × ℕ := fun c =>
    if a_star < ξ (some c) 0 then
      let s₀ := if chainParity c.1.2 = false then 0 else B_time
      (s₀, s₀)
    else if ξ (some c) B_time ≤ a_star then
      let s₁ := if chainParity c.1.2 = false then B_time else 0
      (s₁, s₁)
    else
      let R_le := (range B_time).filter fun r => ξ (some c) r ≤ a_star
      if hne : R_le.Nonempty then
        let r_c := R_le.max' hne
        let s_idx := if chainParity c.1.2 = false then r_c else B_time - 1 - r_c
        (s_idx, s_idx + 1)
      else
        (0, 0)
  let pairS : Fin M_work → List (Fin M_work × Fin k) → ℕ × ℕ := fun γ₀ steps =>
    if hc : (⟨γ₀, steps⟩ : Σ _ : Fin M_work, List (Fin M_work × Fin k)) ∈ NEChains then
      pairS_ne ⟨⟨γ₀, steps⟩, hc⟩
    else
      (β_id.1, β_id.1 + 1)
  let PhaseThresholds : Finset ℕ :=
    ((univ : Finset (Fin M_work)).filter fun γ => 0 < θ_lo γ).image θ_lo
  let AllChainThresholds : Finset ℕ :=
    (univ : Finset (Fin M_work)).biUnion fun γ₀ =>
      (cutValidStepsAux M_work k validTapes γ₀.1 γ₀.2).biUnion fun steps =>
        chainThresholds τ₀ T H B_time θ_lo θ_hi γ₀ steps (pairS γ₀ steps).1 ∪
        chainThresholds τ₀ T H B_time θ_lo θ_hi γ₀ steps (pairS γ₀ steps).2
  let CellThresholds : Finset ℕ := PhaseThresholds ∪ AllChainThresholds
  let X_cell : Finset ℕ := CellThresholds.biUnion (microHopStepGuard τ₀ T H)
  -- Bound `|CellThresholds| ≤ sharpCellGuardThresh k` and `|X_cell| ≤ sharpCellGuardThresh k * (4kH + k + 1)`.
  have hPT_card : PhaseThresholds.card ≤ 2 * k := by
    have hnot0 : (⟨0, hM_ge⟩ : Fin M_work) ∉ (univ : Finset (Fin M_work)).filter (fun γ => 0 < θ_lo γ) := by
      simp only [mem_filter, mem_univ, true_and, θ_lo, hf0, lt_self_iff_false, not_false_eq_true]
    have hsub : (univ : Finset (Fin M_work)).filter (fun γ => 0 < θ_lo γ) ⊆
        (univ : Finset (Fin M_work)).erase ⟨0, hM_ge⟩ := fun γ hγ =>
      mem_erase.mpr ⟨fun heq => hnot0 (heq ▸ hγ), mem_univ γ⟩
    calc PhaseThresholds.card
        ≤ ((univ : Finset (Fin M_work)).filter fun γ => 0 < θ_lo γ).card := card_image_le
      _ ≤ ((univ : Finset (Fin M_work)).erase ⟨0, hM_ge⟩).card := card_le_card hsub
      _ = M_work - 1 := by rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
      _ ≤ 2 * k := by omega
  have hACT_card : AllChainThresholds.card ≤ 2 * sharpChainNodeSum k := by
    have hγ_le : ∀ γ₀ : Fin M_work,
        ((cutValidStepsAux M_work k validTapes γ₀.1 γ₀.2).biUnion fun steps =>
          chainThresholds τ₀ T H B_time θ_lo θ_hi γ₀ steps (pairS γ₀ steps).1 ∪
          chainThresholds τ₀ T H B_time θ_lo θ_hi γ₀ steps (pairS γ₀ steps).2).card ≤
          2 * nodeCapAt k (σ_ph γ₀) := by
      intro γ₀
      calc ((cutValidStepsAux M_work k validTapes γ₀.1 γ₀.2).biUnion fun steps =>
              chainThresholds τ₀ T H B_time θ_lo θ_hi γ₀ steps (pairS γ₀ steps).1 ∪
              chainThresholds τ₀ T H B_time θ_lo θ_hi γ₀ steps (pairS γ₀ steps).2).card
          ≤ ∑ steps ∈ cutValidStepsAux M_work k validTapes γ₀.1 γ₀.2,
              (chainThresholds τ₀ T H B_time θ_lo θ_hi γ₀ steps (pairS γ₀ steps).1 ∪
               chainThresholds τ₀ T H B_time θ_lo θ_hi γ₀ steps (pairS γ₀ steps).2).card :=
            card_biUnion_le
        _ ≤ ∑ steps ∈ cutValidStepsAux M_work k validTapes γ₀.1 γ₀.2, 2 * (steps.length + 1) := by
            refine sum_le_sum fun steps _ => ?_
            have h1 := card_chainThresholds_le τ₀ T H B_time θ_lo θ_hi γ₀ steps (pairS γ₀ steps).1
            have h2 := card_chainThresholds_le τ₀ T H B_time θ_lo θ_hi γ₀ steps (pairS γ₀ steps).2
            have hun := card_union_le
              (chainThresholds τ₀ T H B_time θ_lo θ_hi γ₀ steps (pairS γ₀ steps).1)
              (chainThresholds τ₀ T H B_time θ_lo θ_hi γ₀ steps (pairS γ₀ steps).2)
            omega
        _ = 2 * ∑ steps ∈ cutValidStepsAux M_work k validTapes γ₀.1 γ₀.2, (steps.length + 1) := by
            rw [mul_sum]
        _ ≤ 2 * nodeCapAt k (σ_ph γ₀) :=
            Nat.mul_le_mul_left 2
              (cutValidStepsAux_card_and_nodes_le validTapes σ_ph hσ_mono hvt_card γ₀.1 γ₀.2).2.2
    calc AllChainThresholds.card
        ≤ ∑ γ₀ : Fin M_work, 2 * nodeCapAt k (σ_ph γ₀) :=
          card_biUnion_le.trans (sum_le_sum fun γ₀ _ => hγ_le γ₀)
      _ = 2 * ∑ γ₀ : Fin M_work, nodeCapAt k (σ_ph γ₀) := by rw [mul_sum]
      _ = 2 * ∑ r ∈ (univ : Finset (Fin M_work)).image σ_ph, nodeCapAt k r := by
          rw [sum_image (f := nodeCapAt k) hσ_inj]
      _ ≤ 2 * ∑ r ∈ range (2 * k + 1), nodeCapAt k r :=
          Nat.mul_le_mul_left 2
            (sum_le_sum_of_subset (image_subset_iff.mpr fun γ _ => hσ_mem_range γ))
      _ = 2 * sharpChainNodeSum k := by rw [sharpChainNodeSum_eq_sum]
  have hCT_card : CellThresholds.card ≤ sharpCellGuardThresh k := by
    unfold sharpCellGuardThresh
    exact (card_union_le _ _).trans (Nat.add_le_add hPT_card hACT_card)
  have hX_card : X_cell.card ≤ sharpCellGuardThresh k * (4 * k * H + k + 1) := by
    calc X_cell.card
        ≤ ∑ ψ ∈ CellThresholds, (microHopStepGuard τ₀ T H ψ).card := card_biUnion_le
      _ ≤ ∑ _ψ ∈ CellThresholds, (4 * k * H + k + 1) :=
          sum_le_sum fun ψ _ => card_microHopStepGuard_tight τ₀ T H ψ
      _ = CellThresholds.card * (4 * k * H + k + 1) := by simp
      _ ≤ sharpCellGuardThresh k * (4 * k * H + k + 1) :=
          Nat.mul_le_mul_right _ hCT_card
  -- Step 6: Prove zero internal arcs in `ballAvoidSystem τ₀ T D (B ∪ X_cell) d b` on `U_star`!
  have hlast_lt_T : ∀ (ρ : List ℕ) (u₀ : ℕ), u₀ < T → IsDepPath τ₀.work T (u₀ :: ρ) →
      (u₀ :: ρ).getLastD u₀ < T := by
    intro ρ
    induction ρ with
    | nil => intro u₀ hu₀ _; exact hu₀
    | cons u₁ ρ' ih =>
      intro u₀ _ ⟨hstep, htail⟩
      rw [LinNet.getLastD_cons_cons]
      exact ih u₁ (lt_trans (depStep_lt hstep).1 (depStep_lt hstep).2) htail
  let A_blk : Fin L → Finset (Fin B_time) := fun q =>
    (univ : Finset (Fin B_time)).filter fun β' =>
      ∃ ν' : ι, appendTime τ₀ T (tposOf d b q).1 ∈
        Ico (ξ ν' (π_perm ν' β').1) (ξ ν' ((π_perm ν' β').1 + 1))
  have hno_arcs : ∀ q ∈ U_star, ∀ p ∈ U_star,
      p ∉ ballAvoidSystem τ₀ T D (B ∪ X_cell) d b q := by
    intro q hq p hp hp_mem
    have hqV : q ∈ V₀ := (mem_sdiff.mp (hU_sub hq)).1
    unfold ballAvoidSystem at hp_mem
    obtain ⟨_, ρ, hdep, hfree_tot, hrd, hlen_ρ⟩ := mem_filter.mp hp_mem
    let u₀_q := appendTime τ₀ T (tposOf d b q).1
    let t_end := (u₀_q :: ρ).getLastD u₀_q
    have hu₀_T : u₀_q < T := appendTime_lt τ₀ T (by rw [hlen]; exact (tposOf d b q).2)
    have ht_end_T : t_end < T := hlast_lt_T ρ u₀_q hu₀_T hdep
    have hxt_p : τ₀.input t_end = (p.1 : ℤ) := readPos_eq_some_iff.mp hrd
    have hfreeB : LinNet.GFree B (u₀_q :: ρ) := fun w hw hb =>
      hfree_tot w hw (mem_union_left X_cell hb)
    have hfreeX : ∀ w ∈ ρ, w ∉ X_cell := fun w hw hx =>
      hfree_tot w hw (mem_union_right B hx)
    have hfree_phase : ∀ w ∈ ρ, w ∉ PhaseThresholds.biUnion (microHopStepGuard τ₀ T H) := by
      intro w hw hmem
      obtain ⟨ψ, hψ, hg⟩ := mem_biUnion.mp hmem
      exact hfreeX w hw (mem_biUnion.mpr ⟨ψ, mem_union_left _ hψ, hg⟩)
    obtain ⟨steps, hsteps_mem, hfol⟩ :=
      exists_followsChain_of_phaseGuardFree τ₀ θ_lo θ_hi ph validTapes
        hsep_ph hno_cut hph_mem hph_mono
        (fun γ' γ j _ h => mem_filter.mpr ⟨mem_univ j, h⟩)
        ρ u₀_q hu₀_T hdep hfree_phase
        (fun l₁ l₂ u' v' hsp => hdich_all q hqV ρ l₁ l₂ u' v' hdep hfreeB hlen_ρ hsp)
    let γ₀ := ph u₀_q
    have hguard_pair :
        (∀ w ∈ ρ, w ∉ (chainThresholds τ₀ T H B_time θ_lo θ_hi γ₀ steps (pairS γ₀ steps).1).biUnion
          (microHopStepGuard τ₀ T H)) ∧
        (∀ w ∈ ρ, w ∉ (chainThresholds τ₀ T H B_time θ_lo θ_hi γ₀ steps (pairS γ₀ steps).2).biUnion
          (microHopStepGuard τ₀ T H)) := by
      refine ⟨fun w hw hmem => ?_, fun w hw hmem => ?_⟩
      · obtain ⟨ψ, hψ, hg⟩ := mem_biUnion.mp hmem
        refine hfreeX w hw (mem_biUnion.mpr ⟨ψ, mem_union_right _ ?_, hg⟩)
        exact mem_biUnion.mpr ⟨γ₀, mem_univ γ₀,
          mem_biUnion.mpr ⟨steps, hsteps_mem, mem_union_left _ hψ⟩⟩
      · obtain ⟨ψ, hψ, hg⟩ := mem_biUnion.mp hmem
        refine hfreeX w hw (mem_biUnion.mpr ⟨ψ, mem_union_right _ ?_, hg⟩)
        exact mem_biUnion.mpr ⟨γ₀, mem_univ γ₀,
          mem_biUnion.mpr ⟨steps, hsteps_mem, mem_union_right _ hψ⟩⟩
    obtain ⟨hu₀_a, hu₀_b⟩ := mem_Ico.mp (hU_ico q hq)
    have hmem_timeBlock_of_bounds : ∀ β : Fin B_time,
        timeBlockBound T B_time β.1 ≤ t_end →
        t_end < timeBlockBound T B_time (β.1 + 1) →
        t_end ∈ timeBlock T B_time β := by
      intro β hlo_b hhi_b
      obtain ⟨hb_lo, hb_hi⟩ := timeBlock_eq_Ico_bound T B_time β
      unfold timeBlock
      rw [hb_lo, hb_hi]
      exact mem_Ico.mpr ⟨hlo_b, hhi_b⟩
    by_cases hne_steps : (⟨γ₀, steps⟩ : Σ _ : Fin M_work, List (Fin M_work × Fin k)) ∈ NEChains
    · -- Non-empty chain `c = ⟨⟨γ₀, steps⟩, hne_steps⟩`:
      let c : {x // x ∈ NEChains} := ⟨⟨γ₀, steps⟩, hne_steps⟩
      have hpair_eq : pairS γ₀ steps = pairS_ne c := by
        dsimp only [pairS, c]; simp only [hne_steps, ↓reduceDIte]
      have hg1 := hpair_eq ▸ hguard_pair.1
      have hg2 := hpair_eq ▸ hguard_pair.2
      have hiff1 := followsChain_pullChainPsi_iff τ₀ T H B_time θ_lo θ_hi hsep_ph hno_cut
        hfol (pairS_ne c).1 hg1
      have hiff2 := followsChain_pullChainPsi_iff τ₀ T H B_time θ_lo θ_hi hsep_ph hno_cut
        hfol (pairS_ne c).2 hg2
      by_cases hlt0 : a_star < ξ (some c) 0
      · -- Subcase 2A: `a_star < ξ (some c) 0`, so `u₀_q < ξ (some c) 0`.
        have hb_le_ξ0 : b_star ≤ ξ (some c) 0 := by
          have hmem0 := hξ_ref (some c) 0 (Nat.zero_le _)
          have ha_min : a_star < min T (ξ (some c) 0) := lt_min ha_lt_T hlt0
          have hb_min : b_star ≤ min T (ξ (some c) 0) := by
            by_contra hgt; push Not at hgt
            exact hno_mid _ hmem0 ⟨ha_min, hgt⟩
          exact hb_min.trans (Nat.min_le_right _ _)
        have hu₀_lt_ξ0 : u₀_q < ξ (some c) 0 := lt_of_lt_of_le hu₀_b hb_le_ξ0
        have hp_ne : pairS_ne c =
            (if chainParity steps = false then 0 else B_time,
             if chainParity steps = false then 0 else B_time) := by
          dsimp only [pairS_ne]; simp only [hlt0, ↓reduceIte]; rfl
        rw [hp_ne] at hiff1
        cases hpar : chainParity steps
        · simp only [hpar, ↓reduceIte, chainPred, Bool.false_eq_true] at hiff1
          dsimp only [ξ, c, γ₀] at hu₀_lt_ξ0
          simp only [hpar, ↓reduceIte] at hu₀_lt_ξ0
          have := hiff1.mp hu₀_lt_ξ0
          rw [htb_zero] at this; omega
        · simp only [hpar, Bool.true_eq_false, ↓reduceIte, chainPred] at hiff1
          dsimp only [ξ, c, γ₀] at hu₀_lt_ξ0
          simp only [hpar, Bool.true_eq_false, ↓reduceIte, Nat.sub_zero] at hu₀_lt_ξ0
          rw [htb_B] at hiff1
          have := hiff1.mpr ht_end_T
          omega
      · push Not at hlt0
        by_cases hgeB : ξ (some c) B_time ≤ a_star
        · -- Subcase 2B: `ξ (some c) B_time ≤ a_star ≤ u₀_q`.
          have hξB_le_u₀ : ξ (some c) B_time ≤ u₀_q := hgeB.trans hu₀_a
          have hnot0 : ¬ (a_star < ξ (some c) 0) := not_lt_of_ge hlt0
          have hp_ne : pairS_ne c =
              (if chainParity steps = false then B_time else 0,
               if chainParity steps = false then B_time else 0) := by
            dsimp only [pairS_ne]; simp only [hnot0, hgeB, ↓reduceIte]; rfl
          rw [hp_ne] at hiff1
          cases hpar : chainParity steps
          · simp only [hpar, ↓reduceIte, chainPred, Bool.false_eq_true] at hiff1
            dsimp only [ξ, c, γ₀] at hξB_le_u₀
            simp only [hpar, ↓reduceIte] at hξB_le_u₀
            rw [htb_B] at hiff1
            have := hiff1.mpr ht_end_T
            omega
          · simp only [hpar, Bool.true_eq_false, ↓reduceIte, chainPred] at hiff1
            dsimp only [ξ, c, γ₀] at hξB_le_u₀
            simp only [hpar, Bool.true_eq_false, ↓reduceIte, Nat.sub_self] at hξB_le_u₀
            have := hiff1.mp hξB_le_u₀
            rw [htb_zero] at this; omega
        · -- Subcase 2C: `ξ (some c) 0 ≤ a_star < ξ (some c) B_time`.
          push Not at hgeB
          have hnot0 : ¬ (a_star < ξ (some c) 0) := not_lt_of_ge hlt0
          have hnotB : ¬ (ξ (some c) B_time ≤ a_star) := not_le_of_gt hgeB
          let R_le := (range B_time).filter fun r => ξ (some c) r ≤ a_star
          have hR_ne : R_le.Nonempty :=
            ⟨0, mem_filter.mpr ⟨mem_range.mpr hB_pos, hlt0⟩⟩
          let r_c := R_le.max' hR_ne
          have hr_mem := R_le.max'_mem hR_ne
          have hr_lt : r_c < B_time := mem_range.mp (mem_filter.mp hr_mem).1
          have hr_le_a : ξ (some c) r_c ≤ a_star := (mem_filter.mp hr_mem).2
          have ha_lt_r1 : a_star < ξ (some c) (r_c + 1) := by
            by_contra hle1; push Not at hle1
            rcases eq_or_lt_of_le (Nat.succ_le_of_lt hr_lt) with heqB | hltB
            · have heqB' : r_c + 1 = B_time := heqB
              rw [heqB'] at hle1; exact hnotB hle1
            · have hmem1 : r_c + 1 ∈ R_le := mem_filter.mpr ⟨mem_range.mpr hltB, hle1⟩
              have hle_m : r_c + 1 ≤ r_c := R_le.le_max' _ hmem1
              omega
          have hb_le_r1 : b_star ≤ ξ (some c) (r_c + 1) := by
            have hmem1 := hξ_ref (some c) (r_c + 1) (Nat.succ_le_of_lt hr_lt)
            have ha_min : a_star < min T (ξ (some c) (r_c + 1)) := lt_min ha_lt_T ha_lt_r1
            have hb_min : b_star ≤ min T (ξ (some c) (r_c + 1)) := by
              by_contra hgt; push Not at hgt
              exact hno_mid _ hmem1 ⟨ha_min, hgt⟩
            exact hb_min.trans (Nat.min_le_right _ _)
          have hu₀_ico_r : u₀_q ∈ Ico (ξ (some c) r_c) (ξ (some c) (r_c + 1)) :=
            mem_Ico.mpr ⟨hr_le_a.trans hu₀_a, lt_of_lt_of_le hu₀_b hb_le_r1⟩
          let s_idx := if chainParity steps = false then r_c else B_time - 1 - r_c
          have hs_lt : s_idx < B_time := by dsimp [s_idx]; split_ifs <;> omega
          let β_c : Fin B_time := ⟨s_idx, hs_lt⟩
          have hπ_eq : (π_perm (some c) β_c).1 = r_c := by
            dsimp only [π_perm, c]
            split_ifs with hpar
            · simp [β_c, s_idx, hpar]
            · simp [β_c, s_idx, hpar]; omega
          have hβ_Aq : β_c ∈ A_blk q := by
            refine mem_filter.mpr ⟨mem_univ β_c, some c, ?_⟩
            simpa [hπ_eq] using hu₀_ico_r
          have hAp_eq : A_blk q = A_blk p := hA_eq q hq p hp
          have hβ_Ap : β_c ∈ A_blk p := hAp_eq ▸ hβ_Aq
          have hp_ne : pairS_ne c = (s_idx, s_idx + 1) := by
            have hR_ne' : ((range B_time).filter fun r => ξ (some c) r ≤ a_star).Nonempty := hR_ne
            dsimp only [pairS_ne]; simp only [hnot0, hnotB, ↓reduceIte, hR_ne', ↓reduceDIte]; rfl
          rw [hp_ne] at hiff1 hiff2
          obtain ⟨hu_lo_r, hu_hi_r⟩ := mem_Ico.mp hu₀_ico_r
          have ht_blk_c : t_end ∈ timeBlock T B_time β_c := by
            apply hmem_timeBlock_of_bounds β_c
            · cases hpar : chainParity steps
              · have hs_eq : s_idx = r_c := by simp [s_idx, hpar]
                dsimp [β_c]
                rw [hs_eq] at hiff1 ⊢
                simp only [hpar, chainPred, Bool.false_eq_true, ↓reduceIte] at hiff1
                dsimp only [ξ, c, γ₀] at hu_lo_r
                simp only [hpar, ↓reduceIte] at hu_lo_r
                by_contra hlt_e
                have hlt_end : (u₀_q :: ρ).getLastD u₀_q < timeBlockBound T B_time r_c :=
                  Nat.lt_of_not_le hlt_e
                have := hiff1.mpr hlt_end
                omega
              · have hs_eq : s_idx = B_time - (r_c + 1) := by simp [s_idx, hpar]; omega
                dsimp [β_c]
                rw [hs_eq] at hiff1 ⊢
                simp only [hpar, chainPred, ↓reduceIte] at hiff1
                dsimp only [ξ, c, γ₀] at hu_hi_r
                simp only [hpar, Bool.true_eq_false, ↓reduceIte] at hu_hi_r
                by_contra hlt_e
                have hlt_end : (u₀_q :: ρ).getLastD u₀_q < timeBlockBound T B_time (B_time - (r_c + 1)) :=
                  Nat.lt_of_not_le hlt_e
                have := hiff1.mpr hlt_end
                omega
            · cases hpar : chainParity steps
              · have hs_eq : s_idx + 1 = r_c + 1 := by simp [s_idx, hpar]
                dsimp [β_c]
                rw [hs_eq] at hiff2 ⊢
                simp only [hpar, chainPred, Bool.false_eq_true, ↓reduceIte] at hiff2
                dsimp only [ξ, c, γ₀] at hu_hi_r
                simp only [hpar, ↓reduceIte] at hu_hi_r
                exact hiff2.mp hu_hi_r
              · have hs_eq : s_idx + 1 = B_time - r_c := by simp [s_idx, hpar]; omega
                dsimp [β_c]
                rw [hs_eq] at hiff2 ⊢
                simp only [hpar, chainPred, ↓reduceIte] at hiff2
                dsimp only [ξ, c, γ₀] at hu_lo_r
                simp only [hpar, Bool.true_eq_false, ↓reduceIte] at hu_lo_r
                exact hiff2.mp hu_lo_r
          have hβ_Ep : β_c ∈ (univ : Finset (Fin B_time)).filter (fun β' =>
              ∃ t ∈ timeBlock T B_time β', τ₀.input t = (p.1 : ℤ)) :=
            mem_filter.mpr ⟨mem_univ β_c, t_end, ht_blk_c, hxt_p⟩
          exact disjoint_left.mp (hU_disj p hp) hβ_Ap hβ_Ep
    · -- Empty chain `steps = []` (`since ⟨γ₀, steps⟩ ∉ NEChains` and `steps ∈ cutValidStepsAux`):
      have hsteps_nil : steps = [] := by
        by_contra hne_nil
        apply hne_steps
        exact mem_biUnion.mpr ⟨γ₀, mem_univ γ₀,
          mem_image_of_mem _ (mem_erase.mpr ⟨hne_nil, hsteps_mem⟩)⟩
      have hpair_eq : pairS γ₀ steps = (β_id.1, β_id.1 + 1) := by
        dsimp only [pairS]; simp only [hne_steps, ↓reduceDIte]
      have hg1 := hpair_eq ▸ hguard_pair.1
      have hg2 := hpair_eq ▸ hguard_pair.2
      subst hsteps_nil
      have hiff1 := followsChain_pullChainPsi_iff τ₀ T H B_time θ_lo θ_hi hsep_ph hno_cut
        hfol β_id.1 hg1
      have hiff2 := followsChain_pullChainPsi_iff τ₀ T H B_time θ_lo θ_hi hsep_ph hno_cut
        hfol (β_id.1 + 1) hg2
      have hu₀_ph := hph_mem u₀_q hu₀_T
      obtain ⟨hu₀_lo_ph, hu₀_hi_ph⟩ := mem_Ico.mp hu₀_ph
      have hu₀_id_lo : timeBlockBound T B_time β_id.1 ≤ u₀_q := hid_lo_le.trans hu₀_a
      have hu₀_id_hi : u₀_q < timeBlockBound T B_time (β_id.1 + 1) := lt_of_lt_of_le hu₀_b hb_le_id
      have hβ_Aq : β_id ∈ A_blk q :=
        mem_filter.mpr ⟨mem_univ β_id, none, mem_Ico.mpr ⟨hu₀_id_lo, hu₀_id_hi⟩⟩
      have hAp_eq : A_blk q = A_blk p := hA_eq q hq p hp
      have hβ_Ap : β_id ∈ A_blk p := hAp_eq ▸ hβ_Aq
      simp only [chainParity, chainPred, Bool.false_eq_true, ↓reduceIte, pullChainPsi] at hiff1 hiff2
      have hpsi1_le : min (θ_hi γ₀) (max (θ_lo γ₀) (timeBlockBound T B_time β_id.1)) ≤ u₀_q :=
        (Nat.min_le_right _ _).trans (max_le hu₀_lo_ph hu₀_id_lo)
      have hu₀_lt_psi2 : u₀_q < min (θ_hi γ₀) (max (θ_lo γ₀) (timeBlockBound T B_time (β_id.1 + 1))) :=
        lt_min hu₀_hi_ph (lt_of_lt_of_le hu₀_id_hi (Nat.le_max_right _ _))
      have ht_lo_id : timeBlockBound T B_time β_id.1 ≤ t_end := by
        by_contra hlt_e
        have hlt_end : (u₀_q :: ρ).getLastD u₀_q < timeBlockBound T B_time β_id.1 :=
          Nat.lt_of_not_le hlt_e
        have hlt_u := hiff1.mpr hlt_end
        dsimp only [γ₀] at hpsi1_le
        omega
      have ht_hi_id : t_end < timeBlockBound T B_time (β_id.1 + 1) :=
        hiff2.mp hu₀_lt_psi2
      have ht_blk_id : t_end ∈ timeBlock T B_time β_id :=
        hmem_timeBlock_of_bounds β_id ht_lo_id ht_hi_id
      have hβ_Ep : β_id ∈ (univ : Finset (Fin B_time)).filter (fun β' =>
          ∃ t ∈ timeBlock T B_time β', τ₀.input t = (p.1 : ℤ)) :=
        mem_filter.mpr ⟨mem_univ β_id, t_end, ht_blk_id, hxt_p⟩
      exact disjoint_left.mp (hU_disj p hp) hβ_Ap hβ_Ep
  obtain ⟨hind, hacyc⟩ := isIndependent_and_isAcyclicIn_of_noArcs hno_arcs
  -- Step 7: Real density bound `tightBridgeRho0 k C α * |V₀| ≤ |U_star|` at `d ≥ tightBridge_d0 k C α`.
  have hV_le : V₀.card ≤ d * d * b :=
    (card_le_card (subset_univ V₀)).trans_eq (by simp)
  refine ⟨X_cell, U_star, hX_card, fun q hq => (mem_sdiff.mp (hU_sub hq)).1, hind, hacyc, ?_⟩
  exact tightBridgeRho0_density_step hd hb hC hα0 hT hV₀ hV_le hd_thresh le_rfl (by simpa using hV_nat)

/-- **Zero-Genie `coneSystem` Single-Cell Guard Theorem:**
Instantiating `D = T` via `coneSystem_eq_ballAvoidSystem_at_T` produces `X_cell` (`|X_cell| ≤
sharpCellGuardThresh k * (5k + 1) * H`) and `U ⊆ V₀` (`|U| ≥ tightBridgeRho0 k C α * |V₀|`) that is
**both `IsIndependent` and `IsAcyclicIn` directly on the full unbounded-depth `coneSystem`**
`fun q => coneSystem τ₀ T (B ∪ X_cell) d b (tposOf d b q)` — using **zero `genieDepth`**! -/
theorem exists_singleCell_guard_coneSystem_isIndependent_crossingLowerH
    {k T d b H ηInv L_cap : ℕ} {C α : ℝ}
    (τ₀ : Trace k) (hd : 1 ≤ d) (hb : 1 ≤ b) (hH : 1 ≤ H) (hC : 1 ≤ C) (hα0 : 0 < α)
    (hlen : (appendList τ₀ T).length = d * d * b)
    (hT : (T : ℝ) ≤ C * (((d * d * b : ℕ) : ℝ) + 1))
    (V₀ : Finset (Fin (d * d * b))) (B : Finset ℕ)
    (hV₀ : α * ((d * d * b : ℕ) : ℝ) ≤ (V₀.card : ℝ))
    (hd_thresh : tightBridge_d0 k C α ≤ d)
    (hsep : IsBallPathSeparator τ₀ T T d b V₀ (crossingLowerEtaSteps τ₀ T H ηInv L_cap) B)
    (hE1 : ClauseE1H τ₀ T T d b H ηInv L_cap V₀ B) :
    ∃ (X_cell : Finset ℕ) (U : Finset (Fin (d * d * b))),
      X_cell.card ≤ sharpCellGuardThresh k * (5 * k + 1) * H ∧
      U ⊆ V₀ ∧
      DirectedRecovery.IsIndependent
        (fun q => coneSystem τ₀ T (B ∪ X_cell) d b (tposOf d b q)) U ∧
      HalfRate.IsAcyclicIn
        (fun q => coneSystem τ₀ T (B ∪ X_cell) d b (tposOf d b q)) U ∧
      tightBridgeRho0 k C α * (V₀.card : ℝ) ≤ (U.card : ℝ) := by
  obtain ⟨X_cell, U, hX, hU_sub, hind, hacyc, hU_ge⟩ :=
    exists_singleCell_guard_isIndependent_crossingLowerH τ₀ hd hb hC hα0 hlen hT V₀ B
      hV₀ hd_thresh hsep hE1
  have h45 : 4 * k * H + k + 1 ≤ (5 * k + 1) * H := by
    have hkH : k ≤ k * H := Nat.le_mul_of_pos_right k hH
    nlinarith
  have hX' : X_cell.card ≤ sharpCellGuardThresh k * (5 * k + 1) * H := by
    calc X_cell.card
        ≤ sharpCellGuardThresh k * (4 * k * H + k + 1) := hX
      _ ≤ sharpCellGuardThresh k * ((5 * k + 1) * H) := Nat.mul_le_mul_left _ h45
      _ = sharpCellGuardThresh k * (5 * k + 1) * H := by ring
  have hsys_eq : (fun q => coneSystem τ₀ T (B ∪ X_cell) d b (tposOf d b q)) =
      ballAvoidSystem τ₀ T T (B ∪ X_cell) d b := by
    funext q
    exact coneSystem_eq_ballAvoidSystem_at_T τ₀ hlen (B ∪ X_cell) q
  refine ⟨X_cell, U, hX', hU_sub, ?_, ?_, hU_ge⟩
  · rw [hsys_eq]; exact hind
  · rw [hsys_eq]; exact hacyc

/-- **Zero-Clause Uncapped `> 2H` `coneSystem` Single-Cell Guard Corollary:**
Discharges `ClauseE1H` unconditionally via `clauseE1H_uncapped` at `D = T`. -/
theorem exists_singleCell_guard_coneSystem_isIndependent_crossingLowerGT2H
    {k T d b H : ℕ} {C α : ℝ}
    (τ₀ : Trace k) (hd : 1 ≤ d) (hb : 1 ≤ b) (hH : 1 ≤ H) (hC : 1 ≤ C) (hα0 : 0 < α)
    (hlen : (appendList τ₀ T).length = d * d * b)
    (hT : (T : ℝ) ≤ C * (((d * d * b : ℕ) : ℝ) + 1))
    (V₀ : Finset (Fin (d * d * b))) (B : Finset ℕ)
    (hV₀ : α * ((d * d * b : ℕ) : ℝ) ≤ (V₀.card : ℝ))
    (hd_thresh : tightBridge_d0 k C α ≤ d)
    (hsep : IsBallPathSeparator τ₀ T T d b V₀ (crossingLowerEtaSteps τ₀ T H 1 T) B) :
    ∃ (X_cell : Finset ℕ) (U : Finset (Fin (d * d * b))),
      X_cell.card ≤ sharpCellGuardThresh k * (5 * k + 1) * H ∧
      U ⊆ V₀ ∧
      DirectedRecovery.IsIndependent
        (fun q => coneSystem τ₀ T (B ∪ X_cell) d b (tposOf d b q)) U ∧
      HalfRate.IsAcyclicIn
        (fun q => coneSystem τ₀ T (B ∪ X_cell) d b (tposOf d b q)) U ∧
      tightBridgeRho0 k C α * (V₀.card : ℝ) ≤ (U.card : ℝ) :=
  exists_singleCell_guard_coneSystem_isIndependent_crossingLowerH τ₀ hd hb hH hC hα0 hlen hT V₀ B
    hV₀ hd_thresh hsep (clauseE1H_uncapped τ₀ T T d b H V₀ B)

end SingleCellGuardBridgeCore

/-! ## §5. Tightened Oblivious Linear-Time Headline Theorems (`Targets K.1, K.2 & K.3`) -/

section TightenedObliviousHeadlines

/-- **Tightened Menger Vertex-Expansion Constant (`Targets K.2 & K.3`):**
`cE_menger_tight M C α = tightBridgeRho0 M.k C ((19 / 20) * α) / (2 * valueWidth M)`,
eliminating **both** the outer `1 / 2` factor (`1 / (4 * w_val)` → `1 / (2 * w_val)`) **and** the
`α / 2` density halving (`α / 2` → `(19 / 20) * α`), improving the `k = 2, C = α = 1` Menger
expansion constant by **+101 orders of magnitude** (`and +353 orders of magnitude at C = 10`)! -/
noncomputable def cE_menger_tight (M : TM) (C α : ℝ) : ℝ :=
  tightBridgeRho0 M.k C ((19 / 20) * α) / (2 * (valueWidth M : ℝ))

theorem cE_menger_tight_pos (M : TM) (C α : ℝ) : 0 < cE_menger_tight M C α := by
  unfold cE_menger_tight
  have hvw : (2 : ℝ) ≤ (valueWidth M : ℝ) := by exact_mod_cast two_le_valueWidth M
  have hrho := tightBridgeRho0_pos M.k C ((19 / 20) * α)
  positivity

theorem cE_menger_tight_le_one_thirtieth (M : TM) {C α : ℝ}
    (hC : 1 ≤ C) (hα0 : 0 < α) (hα1 : α ≤ 1) :
    cE_menger_tight M C α ≤ 1 / 30 := by
  unfold cE_menger_tight
  have hρ : tightBridgeRho0 M.k C ((19 / 20) * α) ≤ 2 / 15 :=
    tightBridgeRho0_le_two_fifteenths_of_le_one M.k hC (by positivity) (by linarith)
  have hvw : (2 : ℝ) ≤ (valueWidth M : ℝ) := by exact_mod_cast two_le_valueWidth M
  rw [div_le_iff₀ (by linarith)]
  linarith

/-- **Tightened Macroscopic Excursion Fraction `θ_macro_tight(M, C, α)`:**
`thetaMacro_tight M C α = (9 / 20) * α * tightBridgeRho0 M.k C ((19 / 20) * α) /
  (valueWidth M * (5k + 1) * sharpCellGuardThresh k)` —
**polynomial in `(α / C, 1 / w_val)`**, singly exponential in `k`, and **completely free of
`genieDepth` and `(k + 2)^D`** (`1.78 × 10⁻⁹` at `k = 2, C = 1, α = 1, w_val = 8` vs tower-type)! -/
noncomputable def thetaMacro_tight (M : TM) (C α : ℝ) : ℝ :=
  (9 / 20) * α * tightBridgeRho0 M.k C ((19 / 20) * α) /
    ((valueWidth M : ℝ) * ((5 * M.k + 1 : ℕ) : ℝ) * (sharpCellGuardThresh M.k : ℝ))

theorem thetaMacro_tight_pos (M : TM) (C : ℝ) {α : ℝ} (hα0 : 0 < α) :
    0 < thetaMacro_tight M C α := by
  unfold thetaMacro_tight
  have hvw : (2 : ℝ) ≤ (valueWidth M : ℝ) := by exact_mod_cast two_le_valueWidth M
  have hrho := tightBridgeRho0_pos M.k C ((19 / 20) * α)
  have hsh : (1 : ℝ) ≤ (sharpCellGuardThresh M.k : ℝ) := by
    exact_mod_cast sharpCellGuardThresh_pos M.k
  positivity

/-- Explicit dimension threshold for Theorem 5.3 (bridge) Menger cuts (`= 90953` at `k = 2, C = α = 1`). -/
noncomputable def bridgeMenger_d0_tight (k : ℕ) (C α : ℝ) : ℕ :=
  max 1 (tightBridge_d0 k C ((19 / 20) * α))

/-- Explicit dimension threshold for Theorem X at row-width scale `W = d * entryBits d`. -/
noncomputable def rowWidthMenger_d0_tight (M : TM) (C α : ℝ) : ℕ :=
  max (bridgeMenger_d0_tight M.k C α) ⌈1 / thetaMacro_tight M C α⌉₊

/-- Explicit dimension threshold for Theorem X (`1.12 × 10⁹` at `k = 2, C = α = 1, w_val = 8`!). -/
noncomputable def d0Macro_tight (M : TM) (C α : ℝ) : ℕ :=
  max (bridgeMenger_d0_tight M.k C α) ⌈2 / thetaMacro_tight M C α⌉₊

/-- Tightened `d`-independent macroscopic skeleton turn/length cap `M_max = ⌊16 * C / θ_macro_tight⌋₊`
(Lemma 6.3 tight; `9.00 × 10⁹` at `k = 2, C = α = 1, w_val = 8` vs tower-type!). -/
noncomputable def skeletonMachineMaxLen_tight (M : TM) (C α : ℝ) : ℕ :=
  skeletonMaxLen C (thetaMacro_tight M C α)

/-- Explicit dimension threshold for Theorem S (`finite crossing-capable skeleton + single leg`). -/
noncomputable def skeleton_d0Macro_tight (M : TM) (C α : ℝ) : ℕ :=
  max (d0Macro_tight M C α) ⌈8 / thetaMacro_tight M C α⌉₊

/-- **Zero-Genie Oblivious `coneSystem` Acyclic Deficit Bound:**
On any `ObliviousLinTime M d b C T` trace, cutting any step set `Γ` yields an `(valueWidth M * |Γ|)`-bit
index code directly on `coneSystem`, so every `U` acyclic in `coneSystem` satisfies
`|U| ≤ valueWidth M * |Γ|` with **zero `genieDepth` and zero `ε * L` genie loss**! -/
theorem obliviousLinTime_coneSystem_isAcyclicIn_card_le {M : TM} {d b T : ℕ} {C : ℝ}
    (hobl_lt : ObliviousLinTime M d b C T)
    (Γ : Finset ℕ) (U : Finset (Fin (d * d * b)))
    (hacyc : HalfRate.IsAcyclicIn
      (fun q => coneSystem (traceAt M (d * d * b)) T Γ d b (tposOf d b q)) U) :
    (U.card : ℝ) ≤ (valueWidth M : ℝ) * (Γ.card : ℝ) := by
  obtain ⟨hobl, _, htr⟩ := hobl_lt
  obtain ⟨hM, _⟩ := obliviousTransposer_of_transposes hobl htr (fun _ => false)
  obtain ⟨E, hE⟩ := exists_indexCode hM le_rfl Γ
  have hbits := indexCode_bits_ge_of_isAcyclicIn hE hacyc
  simpa [Nat.cast_mul] using hbits

/-- **Tightened `S3` Genie-Free Trace-Only Menger Dichotomy on `coneSystem` (`Zero Transposition Hypothesis!`):**
For **every** `k`-tape linear-time trace `τ₀`, **every** `V₀` (`|V₀| ≥ α * L`), **every** `1 ≤ H`
(`with NO upper cap on H!`), **every** `d ≥ bridgeMenger_d0_tight k C α` (`= 90953` at `k = 2, C = α = 1`),
and **every** cut ratio `c ≤ 1 / 20`, EITHER:
1. some Menger vertex cut `B` (`|B| < c * |V₀|`) disconnects `u₀(V₀)` from
   `crossingLowerEtaSteps τ₀ T H 1 T`, and for some single-cell guard `X_cell` (`|X_cell| ≤
   sharpCellGuardThresh k * (5k + 1) * H`), the **full unbounded-depth `coneSystem τ₀ T (B ∪ X_cell)`**
   contains an **independent (`hence acyclic`)** subset `U ⊆ V₀` of size
   `|U| ≥ (19 / 20) * tightBridgeRho0 k C ((19 / 20) * α) * |V₀|`; OR
2. **every** Menger vertex cut `B` disconnecting `u₀(V₀)` from `crossingLowerEtaSteps τ₀ T H 1 T`
   satisfies `|B| ≥ c * |V₀|`. -/
theorem linearTimeTrace_crossingLowerGT2H_cone_menger_dichotomy_tight
    {k T d b H : ℕ} {C α c : ℝ}
    (τ₀ : Trace k) (hd : bridgeMenger_d0_tight k C α ≤ d) (hb : 1 ≤ b) (hH : 1 ≤ H)
    (hC : 1 ≤ C) (hα0 : 0 < α) (hc_cap : c ≤ 1 / 20)
    (hlen : (appendList τ₀ T).length = d * d * b)
    (hT : (T : ℝ) ≤ C * (((d * d * b : ℕ) : ℝ) + 1))
    (V₀ : Finset (Fin (d * d * b)))
    (hV₀ : α * ((d * d * b : ℕ) : ℝ) ≤ (V₀.card : ℝ)) :
    let Src := V₀.image fun q => appendTime τ₀ T (tposOf d b q).1
    (∃ B : Finset ℕ,
      IsMengerVertexCut τ₀.work T Src (crossingLowerEtaSteps τ₀ T H 1 T) B ∧
      (B.card : ℝ) < c * (V₀.card : ℝ) ∧
      ∃ (X_cell : Finset ℕ) (U : Finset (Fin (d * d * b))),
        X_cell.card ≤ sharpCellGuardThresh k * (5 * k + 1) * H ∧
        U ⊆ V₀ ∧
        DirectedRecovery.IsIndependent
          (fun q => coneSystem τ₀ T (B ∪ X_cell) d b (tposOf d b q)) U ∧
        HalfRate.IsAcyclicIn
          (fun q => coneSystem τ₀ T (B ∪ X_cell) d b (tposOf d b q)) U ∧
        (19 / 20 : ℝ) * tightBridgeRho0 k C ((19 / 20) * α) * (V₀.card : ℝ) ≤ (U.card : ℝ)) ∨
    (∀ B : Finset ℕ,
      IsMengerVertexCut τ₀.work T Src (crossingLowerEtaSteps τ₀ T H 1 T) B →
      c * (V₀.card : ℝ) ≤ (B.card : ℝ)) := by
  intro Src
  have hd1 : 1 ≤ d := (le_max_left _ _).trans hd
  have hd0 : tightBridge_d0 k C ((19 / 20) * α) ≤ d := (le_max_right _ _).trans hd
  by_cases hex : ∃ B : Finset ℕ,
      IsMengerVertexCut τ₀.work T Src (crossingLowerEtaSteps τ₀ T H 1 T) B ∧
      (B.card : ℝ) < c * (V₀.card : ℝ)
  · left
    obtain ⟨B, hmenger, hB_lt⟩ := hex
    let V₀' := V₀.filter fun q => appendTime τ₀ T (tposOf d b q).1 ∉ B
    obtain ⟨hcard_split, hsep'⟩ :=
      isBallPathSeparator_of_isMengerVertexCut (D := T) τ₀ hlen V₀ _ B hmenger
    have hcard_r : (V₀.card : ℝ) ≤ (V₀'.card : ℝ) + (B.card : ℝ) := by
      have hr : (V₀.card : ℝ) ≤ ((V₀'.card + B.card : ℕ) : ℝ) := by exact_mod_cast hcard_split
      simpa [Nat.cast_add] using hr
    have hB_tw : (B.card : ℝ) ≤ (1 / 20 : ℝ) * (V₀.card : ℝ) := by
      have hcV : c * (V₀.card : ℝ) ≤ (1 / 20 : ℝ) * (V₀.card : ℝ) :=
        mul_le_mul_of_nonneg_right hc_cap (by positivity)
      linarith
    have hV₀'_ge : (19 / 20 : ℝ) * (V₀.card : ℝ) ≤ (V₀'.card : ℝ) := by linarith
    have hV₀'_dens : ((19 / 20) * α) * ((d * d * b : ℕ) : ℝ) ≤ (V₀'.card : ℝ) := by nlinarith
    obtain ⟨X_cell, U, hX, hUV₀', hind, hacyc, hU_ge⟩ :=
      exists_singleCell_guard_coneSystem_isIndependent_crossingLowerGT2H τ₀ hd1 hb hH hC
        (by positivity) hlen hT V₀' B hV₀'_dens hd0 hsep'
    have hρ_nn : 0 ≤ tightBridgeRho0 k C ((19 / 20) * α) :=
      (tightBridgeRho0_pos k C ((19 / 20) * α)).le
    have hU_lb :
        (19 / 20 : ℝ) * tightBridgeRho0 k C ((19 / 20) * α) * (V₀.card : ℝ) ≤ (U.card : ℝ) := by
      calc (19 / 20 : ℝ) * tightBridgeRho0 k C ((19 / 20) * α) * (V₀.card : ℝ)
          = tightBridgeRho0 k C ((19 / 20) * α) * ((19 / 20 : ℝ) * (V₀.card : ℝ)) := by ring
        _ ≤ tightBridgeRho0 k C ((19 / 20) * α) * (V₀'.card : ℝ) :=
            mul_le_mul_of_nonneg_left hV₀'_ge hρ_nn
        _ ≤ (U.card : ℝ) := hU_ge
    exact ⟨B, hmenger, hB_lt, X_cell, U, hX, hUV₀'.trans (filter_subset _ V₀), hind, hacyc, hU_lb⟩
  · right
    intro B hmenger
    by_contra hnot
    push Not at hnot
    exact hex ⟨B, hmenger, hnot⟩

/-- **Tightened Depth-`∞` Menger Vertex-Separator Lower Bound at Arbitrary `1 ≤ H ≤ thetaMacro_tight * L`:**
Eliminates both the `1 / 2` outer loss and the `α / 2` density halving via the `1 / 20` root-hit split! -/
private theorem clauseE1H_menger_lb_tight
    {M : TM} {d T H ηInv L_cap : ℕ} {C α : ℝ}
    (hC : 1 ≤ C) (hα0 : 0 < α) (hH : 1 ≤ H)
    (hd : bridgeMenger_d0_tight M.k C α ≤ d)
    (hobl_lt : ObliviousLinTime M d (entryBits d) C T)
    (V₀ : Finset (Fin (d * d * entryBits d))) (B : Finset ℕ)
    (hV₀ : α * ((d * d * entryBits d : ℕ) : ℝ) ≤ (V₀.card : ℝ))
    (hH_le : (H : ℝ) ≤ thetaMacro_tight M C α * ((d * d * entryBits d : ℕ) : ℝ))
    (hmenger : IsMengerVertexCut (traceAt M (d * d * entryBits d)).work T
      (V₀.image fun q => appendTime (traceAt M (d * d * entryBits d)) T
        (tposOf d (entryBits d) q).1)
      (crossingLowerEtaSteps (traceAt M (d * d * entryBits d)) T H ηInv L_cap) B)
    (hE1 : ClauseE1H (traceAt M (d * d * entryBits d)) T T
      d (entryBits d) H ηInv L_cap
      (V₀.filter fun q => appendTime (traceAt M (d * d * entryBits d)) T
        (tposOf d (entryBits d) q).1 ∉ B) B) :
    cE_menger_tight M C α * (V₀.card : ℝ) ≤ (B.card : ℝ) := by
  let L := d * d * entryBits d
  have hd1 : 1 ≤ d := (le_max_left _ _).trans hd
  have hd0 : tightBridge_d0 M.k C ((19 / 20) * α) ≤ d := (le_max_right _ _).trans hd
  have hb1 : 1 ≤ entryBits d := one_le_entryBits d
  have hL_pos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.mul_pos (Nat.mul_pos hd1 hd1) hb1
  have hα_le_1 : α ≤ 1 := by
    have hV_le : (V₀.card : ℝ) ≤ (L : ℝ) := by
      exact_mod_cast (card_le_card (subset_univ V₀)).trans_eq (by simp [L])
    have h1 : α * (L : ℝ) ≤ 1 * (L : ℝ) := by
      change α * ((d * d * entryBits d : ℕ) : ℝ) ≤ 1 * (L : ℝ); linarith
    exact le_of_mul_le_mul_right h1 hL_pos
  have hc_le : cE_menger_tight M C α ≤ 1 / 20 :=
    (cE_menger_tight_le_one_thirtieth M hC hα0 hα_le_1).trans (by norm_num)
  rcases le_or_gt ((1 / 20 : ℝ) * (V₀.card : ℝ)) (B.card : ℝ) with hB_big | hB_small
  · calc cE_menger_tight M C α * (V₀.card : ℝ)
        ≤ (1 / 20 : ℝ) * (V₀.card : ℝ) := mul_le_mul_of_nonneg_right hc_le (by positivity)
      _ ≤ (B.card : ℝ) := hB_big
  · obtain ⟨hobl, hT, htr⟩ := hobl_lt
    obtain ⟨_, hlen⟩ := obliviousTransposer_of_transposes hobl htr (fun _ => false)
    let V₀' := V₀.filter fun q => appendTime (traceAt M L) T (tposOf d (entryBits d) q).1 ∉ B
    obtain ⟨hcard_split, hsep'⟩ :=
      isBallPathSeparator_of_isMengerVertexCut (D := T) (traceAt M L) hlen V₀ _ B hmenger
    have hcard_r : (V₀.card : ℝ) ≤ (V₀'.card : ℝ) + (B.card : ℝ) := by
      have hr : (V₀.card : ℝ) ≤ ((V₀'.card + B.card : ℕ) : ℝ) := by exact_mod_cast hcard_split
      simpa [Nat.cast_add] using hr
    have hV₀'_ge : (19 / 20 : ℝ) * (V₀.card : ℝ) ≤ (V₀'.card : ℝ) := by linarith
    have hV₀'_dens : ((19 / 20) * α) * (L : ℝ) ≤ (V₀'.card : ℝ) := by nlinarith
    obtain ⟨X_cell, U, hX_card, _, _, hacyc_cone, hU_ge⟩ :=
      exists_singleCell_guard_coneSystem_isIndependent_crossingLowerH
        (traceAt M L) hd1 hb1 hH hC (by positivity) hlen hT V₀' B hV₀'_dens hd0 hsep' hE1
    have hbits := obliviousLinTime_coneSystem_isAcyclicIn_card_le
      ⟨hobl, hT, htr⟩ (B ∪ X_cell) U hacyc_cone
    have hunion_r : ((B ∪ X_cell).card : ℝ) ≤ (B.card : ℝ) + (X_cell.card : ℝ) := by
      exact_mod_cast card_union_le B X_cell
    have hvw_ge2 : (2 : ℝ) ≤ (valueWidth M : ℝ) := by exact_mod_cast two_le_valueWidth M
    have hvw_pos : (0 : ℝ) < (valueWidth M : ℝ) := by linarith
    have hsh_pos : (0 : ℝ) < (sharpCellGuardThresh M.k : ℝ) := by
      exact_mod_cast sharpCellGuardThresh_pos M.k
    have h5k_pos : (0 : ℝ) < ((5 * M.k + 1 : ℕ) : ℝ) := by positivity
    let ρ' := tightBridgeRho0 M.k C ((19 / 20) * α)
    have hρ'_pos : 0 < ρ' := tightBridgeRho0_pos M.k C ((19 / 20) * α)
    have hX_r : (X_cell.card : ℝ) ≤
        (sharpCellGuardThresh M.k : ℝ) * ((5 * M.k + 1 : ℕ) : ℝ) * (H : ℝ) := by
      have hc : (X_cell.card : ℝ) ≤ ((sharpCellGuardThresh M.k * (5 * M.k + 1) * H : ℕ) : ℝ) := by
        exact_mod_cast hX_card
      simpa [Nat.cast_mul, mul_assoc] using hc
    have hvw_X : (valueWidth M : ℝ) * (X_cell.card : ℝ) ≤ (9 / 20 : ℝ) * ρ' * (V₀.card : ℝ) := by
      calc (valueWidth M : ℝ) * (X_cell.card : ℝ)
          ≤ (valueWidth M : ℝ) *
              ((sharpCellGuardThresh M.k : ℝ) * ((5 * M.k + 1 : ℕ) : ℝ) * (H : ℝ)) :=
            mul_le_mul_of_nonneg_left hX_r hvw_pos.le
        _ ≤ (valueWidth M : ℝ) *
              ((sharpCellGuardThresh M.k : ℝ) * ((5 * M.k + 1 : ℕ) : ℝ) *
                (thetaMacro_tight M C α * (L : ℝ))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hH_le (by positivity)) hvw_pos.le
        _ = (9 / 20 : ℝ) * ρ' * (α * (L : ℝ)) := by
            dsimp [ρ']; unfold thetaMacro_tight; field_simp
        _ ≤ (9 / 20 : ℝ) * ρ' * (V₀.card : ℝ) :=
            mul_le_mul_of_nonneg_left hV₀ (by positivity)
    have hU_lb : (19 / 20 : ℝ) * ρ' * (V₀.card : ℝ) ≤ (U.card : ℝ) := by
      calc (19 / 20 : ℝ) * ρ' * (V₀.card : ℝ)
          = ρ' * ((19 / 20 : ℝ) * (V₀.card : ℝ)) := by ring
        _ ≤ ρ' * (V₀'.card : ℝ) := mul_le_mul_of_nonneg_left hV₀'_ge hρ'_pos.le
        _ ≤ (U.card : ℝ) := hU_ge
    have htot_bits : (U.card : ℝ) ≤
        (valueWidth M : ℝ) * (B.card : ℝ) + (valueWidth M : ℝ) * (X_cell.card : ℝ) := by
      calc (U.card : ℝ) ≤ (valueWidth M : ℝ) * ((B ∪ X_cell).card : ℝ) := hbits
        _ ≤ (valueWidth M : ℝ) * ((B.card : ℝ) + (X_cell.card : ℝ)) :=
            mul_le_mul_of_nonneg_left hunion_r hvw_pos.le
        _ = (valueWidth M : ℝ) * (B.card : ℝ) + (valueWidth M : ℝ) * (X_cell.card : ℝ) :=
            mul_add _ _ _
    have hvw_B : (1 / 2 : ℝ) * ρ' * (V₀.card : ℝ) ≤ (valueWidth M : ℝ) * (B.card : ℝ) := by
      linarith
    unfold cE_menger_tight
    change (ρ' / (2 * (valueWidth M : ℝ))) * (V₀.card : ℝ) ≤ (B.card : ℝ)
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    linarith

/-- **Tightened Zero-Clause Uncapped `> 2H` Menger Expansion Theorem (`S1` All-Thresholds Tight):** -/
theorem obliviousLinTime_crossingLowerGT2H_menger_lb_tight
    {M : TM} {d T H : ℕ} {C α : ℝ}
    (hC : 1 ≤ C) (hα0 : 0 < α) (hH : 1 ≤ H)
    (hd : bridgeMenger_d0_tight M.k C α ≤ d)
    (hobl_lt : ObliviousLinTime M d (entryBits d) C T)
    (V₀ : Finset (Fin (d * d * entryBits d))) (B : Finset ℕ)
    (hV₀ : α * ((d * d * entryBits d : ℕ) : ℝ) ≤ (V₀.card : ℝ))
    (hH_le : (H : ℝ) ≤ thetaMacro_tight M C α * ((d * d * entryBits d : ℕ) : ℝ))
    (hmenger : IsMengerVertexCut (traceAt M (d * d * entryBits d)).work T
      (V₀.image fun q => appendTime (traceAt M (d * d * entryBits d)) T
        (tposOf d (entryBits d) q).1)
      (crossingLowerEtaSteps (traceAt M (d * d * entryBits d)) T H 1 T) B) :
    cE_menger_tight M C α * (V₀.card : ℝ) ≤ (B.card : ℝ) :=
  clauseE1H_menger_lb_tight hC hα0 hH hd hobl_lt V₀ B hV₀ hH_le
    hmenger (clauseE1H_uncapped _ T T d (entryBits d) H _ B)

/-- **Tightened Zero-Clause Row-Width `> 2W` Crossing-Lowers Menger Theorem (Theorem X Tight):** -/
theorem obliviousLinTime_crossingLowerGT2W_menger_lb_tight
    {M : TM} {d T : ℕ} {C α : ℝ}
    (hC : 1 ≤ C) (hα0 : 0 < α)
    (hd : rowWidthMenger_d0_tight M C α ≤ d)
    (hobl_lt : ObliviousLinTime M d (entryBits d) C T)
    (V₀ : Finset (Fin (d * d * entryBits d))) (B : Finset ℕ)
    (hV₀ : α * ((d * d * entryBits d : ℕ) : ℝ) ≤ (V₀.card : ℝ))
    (hmenger : IsMengerVertexCut (traceAt M (d * d * entryBits d)).work T
      (V₀.image fun q => appendTime (traceAt M (d * d * entryBits d)) T
        (tposOf d (entryBits d) q).1)
      (crossingLowerEtaSteps (traceAt M (d * d * entryBits d)) T (d * entryBits d) 1 T) B) :
    cE_menger_tight M C α * (V₀.card : ℝ) ≤ (B.card : ℝ) := by
  have hd_menger : bridgeMenger_d0_tight M.k C α ≤ d := (le_max_left _ _).trans hd
  have hd_1θ : ⌈1 / thetaMacro_tight M C α⌉₊ ≤ d := (le_max_right _ _).trans hd
  have hd1 : 1 ≤ d := (le_max_left _ _).trans hd_menger
  have hb1 : 1 ≤ entryBits d := one_le_entryBits d
  have hθ_pos : 0 < thetaMacro_tight M C α := thetaMacro_tight_pos M C hα0
  have h1_le_θd : 1 ≤ thetaMacro_tight M C α * (d : ℝ) := by
    have hge : 1 / thetaMacro_tight M C α ≤ (d : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hd_1θ)
    have hmul := (div_le_iff₀ hθ_pos).mp hge
    linarith
  have hW_le_θL : ((d * entryBits d : ℕ) : ℝ) ≤
      thetaMacro_tight M C α * ((d * d * entryBits d : ℕ) : ℝ) := by
    have hW_nn : (0 : ℝ) ≤ ((d * entryBits d : ℕ) : ℝ) := by positivity
    calc ((d * entryBits d : ℕ) : ℝ)
        = 1 * ((d * entryBits d : ℕ) : ℝ) := (one_mul _).symm
      _ ≤ (thetaMacro_tight M C α * (d : ℝ)) * ((d * entryBits d : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_right h1_le_θd hW_nn
      _ = thetaMacro_tight M C α * ((d * d * entryBits d : ℕ) : ℝ) := by
          push_cast; ring
  exact obliviousLinTime_crossingLowerGT2H_menger_lb_tight hC hα0
    (Nat.mul_pos hd1 hb1) hd_menger hobl_lt V₀ B hV₀ hW_le_θL hmenger

/-- **Tightened Zero-Clause `Mix_{>2W}` Menger Expansion Theorem (Theorem X Main Corollary Tight):** -/
theorem obliviousLinTime_mixGT2W_menger_lb_tight
    {M : TM} {d T : ℕ} {C α : ℝ}
    (hC : 1 ≤ C) (hα0 : 0 < α)
    (hd : rowWidthMenger_d0_tight M C α ≤ d)
    (hobl_lt : ObliviousLinTime M d (entryBits d) C T)
    (V₀ : Finset (Fin (d * d * entryBits d))) (B : Finset ℕ)
    (hV₀ : α * ((d * d * entryBits d : ℕ) : ℝ) ≤ (V₀.card : ℝ))
    (hmenger : IsMengerVertexCut (traceAt M (d * d * entryBits d)).work T
      (V₀.image fun q => appendTime (traceAt M (d * d * entryBits d)) T
        (tposOf d (entryBits d) q).1)
      (mixEtaSteps (traceAt M (d * d * entryBits d)) T (d * entryBits d) 1 T) B) :
    cE_menger_tight M C α * (V₀.card : ℝ) ≤ (B.card : ℝ) :=
  obliviousLinTime_crossingLowerGT2W_menger_lb_tight hC hα0 hd hobl_lt V₀ B hV₀
    (isMengerVertexCut_mono_dst (crossingLowerEtaSteps_subset_mixEtaSteps _ T _ 1 T) hmenger)

/-- **Tightened Theorem X (Strictly Macroscopic Crossing Expansion, Zero `genieDepth`!):**
For **every** oblivious linear-time transposer `(M, C)` and **every** `d ≥ d0Macro_tight M C α`,
setting `H_* := ⌊thetaMacro_tight M C α * L⌋₊` simultaneously satisfies:
1. `d * entryBits d ≤ H_*`,
2. `thetaMacro_tight M C α * L ≤ 2 * H_*`, and
3. **every** Menger vertex cut `B` from `u₀(V₀)` (`|V₀| ≥ α * L`) to
   `crossingLowerEtaSteps (traceAt M L) T H_* 1 T` satisfies `cE_menger_tight M C α * |V₀| ≤ |B|`! -/
theorem obliviousLinTime_macroscopicCrossingLowers_menger_lb_tight
    {M : TM} {d T : ℕ} {C α : ℝ}
    (hC : 1 ≤ C) (hα0 : 0 < α)
    (hd : d0Macro_tight M C α ≤ d)
    (hobl_lt : ObliviousLinTime M d (entryBits d) C T)
    (V₀ : Finset (Fin (d * d * entryBits d)))
    (hV₀ : α * ((d * d * entryBits d : ℕ) : ℝ) ≤ (V₀.card : ℝ)) :
    let L := d * d * entryBits d
    let H_star := ⌊thetaMacro_tight M C α * (L : ℝ)⌋₊
    d * entryBits d ≤ H_star ∧
      thetaMacro_tight M C α * (L : ℝ) ≤ (2 * H_star : ℕ) ∧
      ∀ B : Finset ℕ,
        IsMengerVertexCut (traceAt M L).work T
          (V₀.image fun q => appendTime (traceAt M L) T (tposOf d (entryBits d) q).1)
          (crossingLowerEtaSteps (traceAt M L) T H_star 1 T) B →
        cE_menger_tight M C α * (V₀.card : ℝ) ≤ (B.card : ℝ) := by
  intro L H_star
  have hd_menger : bridgeMenger_d0_tight M.k C α ≤ d := (le_max_left _ _).trans hd
  have hd_2θ : ⌈2 / thetaMacro_tight M C α⌉₊ ≤ d := (le_max_right _ _).trans hd
  have hd1 : 1 ≤ d := (le_max_left _ _).trans hd_menger
  have hb1 : 1 ≤ entryBits d := one_le_entryBits d
  have hθ_pos : 0 < thetaMacro_tight M C α := thetaMacro_tight_pos M C hα0
  have hW_pos : 1 ≤ d * entryBits d := Nat.mul_pos hd1 hb1
  have h2_le_θd : (2 : ℝ) ≤ thetaMacro_tight M C α * (d : ℝ) := by
    have hge : 2 / thetaMacro_tight M C α ≤ (d : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hd_2θ)
    have hmul := (div_le_iff₀ hθ_pos).mp hge
    linarith
  have hW_le_θL : ((d * entryBits d : ℕ) : ℝ) ≤ thetaMacro_tight M C α * (L : ℝ) := by
    have hW_nn : (0 : ℝ) ≤ ((d * entryBits d : ℕ) : ℝ) := by positivity
    have h1_le : (1 : ℝ) ≤ thetaMacro_tight M C α * (d : ℝ) := by linarith
    calc ((d * entryBits d : ℕ) : ℝ)
        = 1 * ((d * entryBits d : ℕ) : ℝ) := (one_mul _).symm
      _ ≤ (thetaMacro_tight M C α * (d : ℝ)) * ((d * entryBits d : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_right h1_le hW_nn
      _ = thetaMacro_tight M C α * (L : ℝ) := by dsimp [L]; push_cast; ring
  have hW_le_H : d * entryBits d ≤ H_star := Nat.le_floor hW_le_θL
  have hH_pos : 1 ≤ H_star := hW_pos.trans hW_le_H
  have hH_le_θL : (H_star : ℝ) ≤ thetaMacro_tight M C α * (L : ℝ) :=
    Nat.floor_le (by positivity)
  have h2_le_θL : (2 : ℝ) ≤ thetaMacro_tight M C α * (L : ℝ) := by
    have hd_le_L : (d : ℝ) ≤ (L : ℝ) := by
      have : d ≤ d * d * entryBits d := by
        calc d = d * 1 * 1 := by ring
          _ ≤ d * d * entryBits d := Nat.mul_le_mul (Nat.mul_le_mul le_rfl hd1) hb1
      exact_mod_cast this
    exact h2_le_θd.trans (mul_le_mul_of_nonneg_left hd_le_L hθ_pos.le)
  have hθL_le_2H : thetaMacro_tight M C α * (L : ℝ) ≤ ((2 * H_star : ℕ) : ℝ) := by
    have hlt_succ : thetaMacro_tight M C α * (L : ℝ) < (H_star : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    have hH1 : (1 : ℝ) ≤ (H_star : ℝ) := by exact_mod_cast hH_pos
    push_cast
    linarith
  refine ⟨hW_le_H, hθL_le_2H, fun B hmenger => ?_⟩
  exact obliviousLinTime_crossingLowerGT2H_menger_lb_tight hC hα0 hH_pos
    hd_menger hobl_lt V₀ B hV₀ hH_le_θL hmenger

/-- **Tightened `Theorem S(b)` (`Finite Crossing-Capable Skeleton & Single-Leg Localization`, Tower-Free `M_max`!):**
Replaces tower-type `skeletonMachineMaxLen` by polynomial `skeletonMachineMaxLen_tight M C α =
⌊16 * C / thetaMacro_tight M C α⌋₊` (`9.00 × 10⁹` at `k = 2, C = α = 1, w_val = 8`). -/
theorem obliviousLinTime_reduces_to_crossingCapableSkeleton_and_singleLeg_tight
    {M : TM} {d T : ℕ} {C α : ℝ}
    (hC : 1 ≤ C) (hα0 : 0 < α)
    (hd : skeleton_d0Macro_tight M C α ≤ d)
    (hobl_lt : ObliviousLinTime M d (entryBits d) C T)
    (V₀ : Finset (Fin (d * d * entryBits d)))
    (hV₀ : α * ((d * d * entryBits d : ℕ) : ℝ) ≤ (V₀.card : ℝ)) :
    let L := d * d * entryBits d
    let θ_star := thetaMacro_tight M C α
    let H_star := ⌊θ_star * (L : ℝ)⌋₊
    let Λ_star := ⌊(θ_star / 4) * (L : ℝ)⌋₊
    let M_max := skeletonMachineMaxLen_tight M C α
    let τ₀ := traceAt M L
    1 ≤ Λ_star ∧ 2 * Λ_star ≤ H_star ∧
      traceSkeletonTuple τ₀ T Λ_star ∈ CrossingCapableSkeletonTuple M.k M_max ∧
      ∃ (j_star : Fin M.k) (r_star : ℕ),
        IsScaleFreeCrossingCapable (traceSkeletonTuple τ₀ T Λ_star j_star) ∧
        2 ≤ macroTurns (traceSkeletonTuple τ₀ T Λ_star j_star) ∧
        9 ≤ (traceSkeletonTuple τ₀ T Λ_star j_star).length ∧
        r_star ≤ macroTurns (traceSkeletonTuple τ₀ T Λ_star j_star) ∧
        r_star ≤ M_max ∧
        ∀ B : Finset ℕ,
          IsMengerVertexCut τ₀.work T
            (V₀.image fun q => appendTime τ₀ T (tposOf d (entryBits d) q).1)
            (legCrossingLowers τ₀ T H_star Λ_star j_star r_star) B →
          (cE_menger_tight M C α / ((M.k : ℝ) * ((M_max : ℝ) + 1))) *
            (V₀.card : ℝ) ≤ (B.card : ℝ) := by
  intro L θ_star H_star Λ_star M_max τ₀
  have hd_d0 : d0Macro_tight M C α ≤ d := (le_max_left _ _).trans hd
  have hd_8θ : ⌈8 / θ_star⌉₊ ≤ d := (le_max_right _ _).trans hd
  have hd1 : 1 ≤ d := (le_max_left _ _).trans ((le_max_left _ _).trans hd_d0)
  have hb1 : 1 ≤ entryBits d := one_le_entryBits d
  have hθ_pos : 0 < θ_star := thetaMacro_tight_pos M C hα0
  obtain ⟨_, _, hmenger_tot⟩ :=
    obliviousLinTime_macroscopicCrossingLowers_menger_lb_tight hC hα0 hd_d0 hobl_lt V₀ hV₀
  obtain ⟨_, hT, _⟩ := hobl_lt
  obtain ⟨hΛ1, hturns_le, hmem_bdd⟩ :=
    traceSkeletonTuple_mem_boundedSkeletonTuple τ₀ hd1 hb1 hC hθ_pos hd_8θ hT
  have h2Λ_le_H : 2 * Λ_star ≤ H_star := by
    apply Nat.le_floor
    have hΛ_le : (Λ_star : ℝ) ≤ (θ_star / 4) * (L : ℝ) := Nat.floor_le (by positivity)
    push_cast; linarith
  set Src := V₀.image fun q => appendTime τ₀ T (tposOf d (entryBits d) q).1
  set c_tot : ℝ := cE_menger_tight M C α
  have hc_tot_pos : 0 < c_tot := cE_menger_tight_pos M C α
  have hV₀_pos : (0 : ℝ) < (V₀.card : ℝ) := by
    have hL_pos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.mul_pos (Nat.mul_pos hd1 hd1) hb1
    linarith [mul_pos hα0 hL_pos]
  let Slots : Finset (Fin M.k × ℕ) :=
    ((univ : Finset (Fin M.k)) ×ˢ range (M_max + 1)).filter fun jr =>
      IsScaleFreeCrossingCapable (traceSkeletonTuple τ₀ T Λ_star jr.1) ∧
      jr.2 ≤ macroTurns (traceSkeletonTuple τ₀ T Λ_star jr.1)
  have hcover : crossingLowerEtaSteps τ₀ T H_star 1 T ⊆
      Slots.biUnion (fun jr => legCrossingLowers τ₀ T H_star Λ_star jr.1 jr.2) := by
    intro v hv
    rw [crossingLowerEtaSteps_eq_biUnion_tapeCrossingLowers] at hv
    obtain ⟨j, _, hv_tape⟩ := mem_biUnion.mp hv
    have hcap_j : IsCrossingCapableSkeleton H_star Λ_star (tapeSkeleton (τ₀.work j) T Λ_star) :=
      isCrossingCapableSkeleton_of_tapeCrossingLowers_nonempty (τ₀.work_isWalk j)
        (τ₀.work_zero j) hΛ1 ⟨v, hv_tape⟩
    obtain ⟨hsf_j, _⟩ := isScaleFreeCrossingCapable_of_two_mul_le hΛ1 h2Λ_le_H hcap_j
    let r := legOfEpoch (tapeSkeleton (τ₀.work j) T Λ_star) (epochIdx (τ₀.work j) Λ_star v)
    have hr_turns : r ≤ macroTurns (tapeSkeleton (τ₀.work j) T Λ_star) :=
      legOfEpoch_le_macroTurns _ _
    have hr_max : r < M_max + 1 := Nat.lt_succ_of_le (hr_turns.trans (hturns_le j))
    refine mem_biUnion.mpr ⟨(j, r), ?_, mem_filter.mpr ⟨hv_tape, rfl⟩⟩
    exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_univ j, mem_range.mpr hr_max⟩, hsf_j, hr_turns⟩
  have hSlots_ne : Slots.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have hdst_empty : crossingLowerEtaSteps τ₀ T H_star 1 T = ∅ := by
      rw [← subset_empty]; exact hcover.trans (by simp [hemp])
    have h0 := hmenger_tot ∅ (by rw [hdst_empty]; exact isMengerVertexCut_dst_self _ _ ∅)
    simp only [card_empty, Nat.cast_zero] at h0
    linarith [mul_pos hc_tot_pos hV₀_pos]
  obtain ⟨⟨j₀, _⟩, hj₀_mem⟩ := hSlots_ne
  have hmem_cap : traceSkeletonTuple τ₀ T Λ_star ∈ CrossingCapableSkeletonTuple M.k M_max :=
    mem_filter.mpr ⟨hmem_bdd, j₀, (mem_filter.mp hj₀_mem).2.1⟩
  have hk_pos : 0 < M.k := Fin.pos j₀
  have hSlots_card : (Slots.card : ℝ) ≤ (M.k : ℝ) * ((M_max : ℝ) + 1) := by
    have hle : Slots.card ≤ M.k * (M_max + 1) :=
      (card_le_card (filter_subset _ _)).trans (by simp [card_product])
    exact_mod_cast hle
  have hexists_slot : ∃ jr ∈ Slots, ∀ B : Finset ℕ,
      IsMengerVertexCut τ₀.work T Src (legCrossingLowers τ₀ T H_star Λ_star jr.1 jr.2) B →
      (c_tot / ((M.k : ℝ) * ((M_max : ℝ) + 1))) * (V₀.card : ℝ) ≤ (B.card : ℝ) := by
    by_contra hall_cheap
    push Not at hall_cheap
    choose B_of hB_cut hB_lt using fun jr : {x // x ∈ Slots} => hall_cheap jr.1 jr.2
    let B_u := Slots.attach.biUnion fun jr => B_of jr
    have hcut_bu : IsMengerVertexCut τ₀.work T Src
        (Slots.attach.biUnion fun jr => legCrossingLowers τ₀ T H_star Λ_star jr.1.1 jr.1.2) B_u :=
      isMengerVertexCut_biUnion Slots.attach Src
        (fun jr => legCrossingLowers τ₀ T H_star Λ_star jr.1.1 jr.1.2) B_of
        (fun jr _ => hB_cut jr)
    have hcut_tot : IsMengerVertexCut τ₀.work T Src (crossingLowerEtaSteps τ₀ T H_star 1 T) B_u := by
      intro π t₀ hsrc hdep hlast
      have hcov_last := hcover hlast
      obtain ⟨jr, hjrS, hmem_jr⟩ := mem_biUnion.mp hcov_last
      exact hcut_bu π t₀ hsrc hdep (mem_biUnion.mpr ⟨⟨jr, hjrS⟩, mem_attach _ _, hmem_jr⟩)
    have hbu_card_nat : B_u.card ≤ ∑ jr ∈ Slots.attach, (B_of jr).card := card_biUnion_le
    have hbu_card_r : (B_u.card : ℝ) ≤ ∑ jr ∈ Slots.attach, ((B_of jr).card : ℝ) := by
      exact_mod_cast hbu_card_nat
    have hsum_lt : ∑ jr ∈ Slots.attach, ((B_of jr).card : ℝ) <
        ∑ _jr ∈ Slots.attach, (c_tot / ((M.k : ℝ) * ((M_max : ℝ) + 1))) * (V₀.card : ℝ) :=
      sum_lt_sum_of_nonempty (Slots.attach_nonempty_iff.mpr ⟨⟨j₀, _⟩, hj₀_mem⟩)
        (fun jr _ => hB_lt jr)
    have hconst_sum : (∑ _jr ∈ Slots.attach,
        (c_tot / ((M.k : ℝ) * ((M_max : ℝ) + 1))) * (V₀.card : ℝ)) ≤
        c_tot * (V₀.card : ℝ) := by
      rw [sum_const, card_attach, nsmul_eq_mul]
      have hdenom_pos : (0 : ℝ) < (M.k : ℝ) * ((M_max : ℝ) + 1) := by
        have : (0 : ℝ) < (M.k : ℝ) := by exact_mod_cast hk_pos
        positivity
      calc (Slots.card : ℝ) * ((c_tot / ((M.k : ℝ) * ((M_max : ℝ) + 1))) * (V₀.card : ℝ))
          ≤ ((M.k : ℝ) * ((M_max : ℝ) + 1)) *
              ((c_tot / ((M.k : ℝ) * ((M_max : ℝ) + 1))) * (V₀.card : ℝ)) :=
            mul_le_mul_of_nonneg_right hSlots_card (by positivity)
        _ = c_tot * (V₀.card : ℝ) := by field_simp
    have htot_lb := hmenger_tot B_u hcut_tot
    linarith
  obtain ⟨⟨j_star, r_star⟩, hjr_mem, hjr_exp⟩ := hexists_slot
  obtain ⟨hprod_mem, hsf_star, hr_turns⟩ := mem_filter.mp hjr_mem
  have hr_max : r_star ≤ M_max := Nat.le_of_lt_succ (mem_range.mp (mem_product.mp hprod_mem).2)
  have hleg_ne : (legCrossingLowers τ₀ T H_star Λ_star j_star r_star).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have h0 := hjr_exp ∅ (by rw [hemp]; exact isMengerVertexCut_dst_self _ _ ∅)
    simp only [card_empty, Nat.cast_zero] at h0
    have hdenom_pos : (0 : ℝ) < (M.k : ℝ) * ((M_max : ℝ) + 1) := by
      have : (0 : ℝ) < (M.k : ℝ) := by exact_mod_cast hk_pos
      positivity
    linarith [mul_pos (div_pos hc_tot_pos hdenom_pos) hV₀_pos]
  obtain ⟨v_w, hv_w⟩ := hleg_ne
  have hcap_star := isCrossingCapableSkeleton_of_tapeCrossingLowers_nonempty
    (τ₀.work_isWalk j_star) (τ₀.work_zero j_star) hΛ1 ⟨v_w, (mem_filter.mp hv_w).1⟩
  obtain ⟨_, hlen9⟩ := isScaleFreeCrossingCapable_of_two_mul_le hΛ1 h2Λ_le_H hcap_star
  exact ⟨hΛ1, h2Λ_le_H, hmem_cap, j_star, r_star, hsf_star,
    two_le_macroTurns_of_isScaleFreeCrossingCapable hsf_star, hlen9, hr_turns, hr_max, hjr_exp⟩

/-- **Tightened `Theorem S(c)` (`Infinite-Dimension Pinned-Skeleton & Pinned-Leg Reduction`, Tower-Free!):** -/
theorem obliviousLinTime_infinite_pinned_skeleton_and_leg_tight {M : TM} {C : ℝ} (hC : 1 ≤ C)
    {S : Set ℕ} (hS : S.Infinite) (T_of : ℕ → ℕ)
    (hobl : ∀ d ∈ S, ObliviousLinTime M d (entryBits d) C (T_of d)) :
    let M_max := skeletonMachineMaxLen_tight M C 1
    ∃ (sk_star : Fin M.k → List Bool) (j_star : Fin M.k) (r_star : ℕ),
      sk_star ∈ CrossingCapableSkeletonTuple M.k M_max ∧
      IsScaleFreeCrossingCapable (sk_star j_star) ∧
      2 ≤ macroTurns (sk_star j_star) ∧
      9 ≤ (sk_star j_star).length ∧
      r_star ≤ macroTurns (sk_star j_star) ∧
      r_star ≤ M_max ∧
      {d : ℕ | d ∈ S ∧ skeleton_d0Macro_tight M C 1 ≤ d ∧
        let L := d * d * entryBits d
        let θ_star := thetaMacro_tight M C 1
        let H_star := ⌊θ_star * (L : ℝ)⌋₊
        let Λ_star := ⌊(θ_star / 4) * (L : ℝ)⌋₊
        let τ₀ := traceAt M L
        traceSkeletonTuple τ₀ (T_of d) Λ_star = sk_star ∧
        ∀ B : Finset ℕ,
          IsMengerVertexCut τ₀.work (T_of d)
            ((univ : Finset (Fin L)).image fun q => appendTime τ₀ (T_of d) (tposOf d (entryBits d) q).1)
            (legCrossingLowers τ₀ (T_of d) H_star Λ_star j_star r_star) B →
          (cE_menger_tight M C 1 / ((M.k : ℝ) * ((M_max : ℝ) + 1))) * (L : ℝ) ≤ (B.card : ℝ)}.Infinite := by
  intro M_max
  set d₀ := skeleton_d0Macro_tight M C 1
  have hS_high : (S \ (Finset.range d₀ : Set ℕ)).Infinite :=
    hS.sdiff (Finset.finite_toSet (Finset.range d₀))
  have step_at : ∀ d ∈ S \ (Finset.range d₀ : Set ℕ),
      let L := d * d * entryBits d
      let θ_star := thetaMacro_tight M C 1
      let H_star := ⌊θ_star * (L : ℝ)⌋₊
      let Λ_star := ⌊(θ_star / 4) * (L : ℝ)⌋₊
      let τ₀ := traceAt M L
      traceSkeletonTuple τ₀ (T_of d) Λ_star ∈ CrossingCapableSkeletonTuple M.k M_max ∧
      ∃ (j_star : Fin M.k) (r_star : ℕ),
        IsScaleFreeCrossingCapable (traceSkeletonTuple τ₀ (T_of d) Λ_star j_star) ∧
        2 ≤ macroTurns (traceSkeletonTuple τ₀ (T_of d) Λ_star j_star) ∧
        9 ≤ (traceSkeletonTuple τ₀ (T_of d) Λ_star j_star).length ∧
        r_star ≤ macroTurns (traceSkeletonTuple τ₀ (T_of d) Λ_star j_star) ∧
        r_star ≤ M_max ∧
        ∀ B : Finset ℕ,
          IsMengerVertexCut τ₀.work (T_of d)
            ((univ : Finset (Fin L)).image fun q => appendTime τ₀ (T_of d) (tposOf d (entryBits d) q).1)
            (legCrossingLowers τ₀ (T_of d) H_star Λ_star j_star r_star) B →
          (cE_menger_tight M C 1 / ((M.k : ℝ) * ((M_max : ℝ) + 1))) * (L : ℝ) ≤ (B.card : ℝ) := by
    intro d hd
    obtain ⟨hdS, hd_not⟩ := hd
    have hd_ge : d₀ ≤ d := by
      simp only [Finset.mem_coe, Finset.mem_range, not_lt] at hd_not; exact hd_not
    have hV₀_univ : 1 * ((d * d * entryBits d : ℕ) : ℝ) ≤
        ((univ : Finset (Fin (d * d * entryBits d))).card : ℝ) := by simp
    obtain ⟨_, _, hmem, j_s, r_s, hsf, h2, h9, hr_t, hr_m, hexp⟩ :=
      obliviousLinTime_reduces_to_crossingCapableSkeleton_and_singleLeg_tight hC one_pos hd_ge
        (hobl d hdS) univ hV₀_univ
    exact ⟨hmem, j_s, r_s, hsf, h2, h9, hr_t, hr_m, fun B hB => by simpa using hexp B hB⟩
  choose j_of r_of hsf_of h2_of h9_of hrt_of hrm_of hexp_of using
    fun d : {x // x ∈ S \ (Finset.range d₀ : Set ℕ)} => (step_at d.1 d.2).2
  obtain ⟨d_wit, hd_wit⟩ := hS_high.nonempty
  let dflt_skel := traceSkeletonTuple (traceAt M (d_wit * d_wit * entryBits d_wit)) (T_of d_wit)
    ⌊(thetaMacro_tight M C 1 / 4) * ((d_wit * d_wit * entryBits d_wit : ℕ) : ℝ)⌋₊
  let dflt_j := j_of ⟨d_wit, hd_wit⟩
  let dflt_r := r_of ⟨d_wit, hd_wit⟩
  let F_comb : Finset ((Fin M.k → List Bool) × Fin M.k × ℕ) :=
    CrossingCapableSkeletonTuple M.k M_max ×ˢ ((univ : Finset (Fin M.k)) ×ˢ range (M_max + 1))
  let tag : ℕ → (Fin M.k → List Bool) × Fin M.k × ℕ := fun d =>
    if hd : d ∈ S \ (Finset.range d₀ : Set ℕ) then
      let L := d * d * entryBits d
      let Λ_star := ⌊(thetaMacro_tight M C 1 / 4) * (L : ℝ)⌋₊
      (traceSkeletonTuple (traceAt M L) (T_of d) Λ_star, j_of ⟨d, hd⟩, r_of ⟨d, hd⟩)
    else
      (dflt_skel, dflt_j, dflt_r)
  have htag_of : ∀ {d : ℕ} (hd : d ∈ S \ (Finset.range d₀ : Set ℕ)),
      tag d = (traceSkeletonTuple (traceAt M (d * d * entryBits d)) (T_of d)
        ⌊(thetaMacro_tight M C 1 / 4) * ((d * d * entryBits d : ℕ) : ℝ)⌋₊,
        j_of ⟨d, hd⟩, r_of ⟨d, hd⟩) := by
    intro d hd; dsimp [tag]; split_ifs; rfl
  have htag_mem : ∀ d ∈ S \ (Finset.range d₀ : Set ℕ), tag d ∈ F_comb := by
    intro d hd
    rw [htag_of hd]
    simp only [F_comb, mem_product, mem_univ, true_and, mem_range]
    exact ⟨(step_at d hd).1, Nat.lt_succ_of_le (hrm_of ⟨d, hd⟩)⟩
  obtain ⟨⟨sk_star, j_star, r_star⟩, hmem_F, hinf_fib⟩ :=
    exists_infinite_fiber_of_mapsTo_finset hS_high F_comb tag htag_mem
  obtain ⟨d_p, hd_p_high, htag_p⟩ := hinf_fib.nonempty
  rw [htag_of hd_p_high] at htag_p
  simp only [Prod.mk.injEq] at htag_p
  obtain ⟨hsk_eq, hj_eq, hr_eq⟩ := htag_p
  refine ⟨sk_star, j_star, r_star, (mem_product.mp hmem_F).1,
    by rw [← hsk_eq, ← hj_eq]; exact hsf_of ⟨d_p, hd_p_high⟩,
    by rw [← hsk_eq, ← hj_eq]; exact h2_of ⟨d_p, hd_p_high⟩,
    by rw [← hsk_eq, ← hj_eq]; exact h9_of ⟨d_p, hd_p_high⟩,
    by rw [← hsk_eq, ← hj_eq, ← hr_eq]; exact hrt_of ⟨d_p, hd_p_high⟩,
    by rw [← hr_eq]; exact hrm_of ⟨d_p, hd_p_high⟩, ?_⟩
  refine hinf_fib.mono fun d hd => ?_
  obtain ⟨hd_high, htag_d⟩ := hd
  have ⟨hdS, hd_not⟩ := hd_high
  have hd_ge : d₀ ≤ d := by
    simp only [Finset.mem_coe, Finset.mem_range, not_lt] at hd_not; exact hd_not
  rw [htag_of hd_high] at htag_d
  simp only [Prod.mk.injEq] at htag_d
  obtain ⟨hsk_d, hj_d, hr_d⟩ := htag_d
  refine ⟨hdS, hd_ge, hsk_d, fun B hB => ?_⟩
  rw [← hj_d, ← hr_d] at hB
  exact hexp_of ⟨d, hd_high⟩ B hB

end TightenedObliviousHeadlines

/-! ## §6. Tightened Heavy-Trace & Paper 15 Simulator `N_s` Headlines -/

section TightenedFrozenAndSimulatorHeadlines

/-- Tightened heavy-trace Menger expansion constant (`for η ≤ (α / 8) * tightBridgeRho0 M.k C ((19 / 20) * α)`):
`cE_frozen_tight M C α = (3 / 8) * tightBridgeRho0 M.k C ((19 / 20) * α) / valueWidth M`. -/
noncomputable def cE_frozen_tight (M : TM) (C α : ℝ) : ℝ :=
  (3 / 8) * tightBridgeRho0 M.k C ((19 / 20) * α) / (valueWidth M : ℝ)

theorem cE_frozen_tight_pos (M : TM) (C α : ℝ) : 0 < cE_frozen_tight M C α := by
  unfold cE_frozen_tight
  have hvw : (2 : ℝ) ≤ (valueWidth M : ℝ) := by exact_mod_cast two_le_valueWidth M
  have hrho := tightBridgeRho0_pos M.k C ((19 / 20) * α)
  positivity

theorem cE_frozen_tight_le_one_fortieth (M : TM) {C α : ℝ}
    (hC : 1 ≤ C) (hα0 : 0 < α) (hα1 : α ≤ 1) :
    cE_frozen_tight M C α ≤ 1 / 40 := by
  unfold cE_frozen_tight
  have hρ : tightBridgeRho0 M.k C ((19 / 20) * α) ≤ 2 / 15 :=
    tightBridgeRho0_le_two_fifteenths_of_le_one M.k hC (by positivity) (by linarith)
  have hvw : (2 : ℝ) ≤ (valueWidth M : ℝ) := by exact_mod_cast two_le_valueWidth M
  rw [div_le_iff₀ (by linarith)]
  linarith

/-- Tightened `(k, c, α)`-only simulator trace-entropy threshold
`η_*(k, c, α) = (α / 16) * tightBridgeRho0 k (11 * c + 1) ((19 / 20) * α)` (`4.88 × 10⁻⁷` at
`k = 2, c = 1, α = 1` vs `10⁻³⁸⁸` previously — `+381.6` orders of magnitude larger!). -/
noncomputable def adaptiveBridge_etaStar_tight (k : ℕ) (c α : ℝ) : ℝ :=
  (α / 16) * tightBridgeRho0 k (adaptiveBridge_cSim c) ((19 / 20) * α)

theorem adaptiveBridge_etaStar_tight_pos (k : ℕ) {c α : ℝ} (_hc : 0 ≤ c) (hα : 0 < α) :
    0 < adaptiveBridge_etaStar_tight k c α := by
  unfold adaptiveBridge_etaStar_tight
  exact mul_pos (by positivity) (tightBridgeRho0_pos k (adaptiveBridge_cSim c) ((19 / 20) * α))

/-- **Tightened Theorem E(a) (`Heavy-Trace Macroscopic Crossing-Lower Menger Expansion`, Zero `genieDepth`!):**
On `M`'s own heavy traces (`traceProb M L τ₀ ≥ 2 ^ (-η * L)` with `η ≤ (α / 8) * tightBridgeRho0 M.k C ((19 / 20) * α)`),
directly applies `frozenTrace_isAcyclicIn_coneSystem_deficit_le` to `B ∪ X_cell` with **zero `genie_cost`**! -/
theorem frozenTrace_macroscopicCrossingLowers_menger_lb_tight {M : TM} {d : ℕ} {c C α η : ℝ}
    (hc_le : c ≤ C) (hC1 : 1 ≤ C) (hα0 : 0 < α)
    (hd : d0Macro_tight M C α ≤ d)
    (htr : TransposesAt M d c) {τ₀ : Trace M.k}
    (hprob : (2 : ℝ) ^ (-η * ((d * d * entryBits d : ℕ) : ℝ)) ≤
      traceProb M (d * d * entryBits d) τ₀)
    (hη_le : η ≤ (α / 8) * tightBridgeRho0 M.k C ((19 / 20) * α)) :
    let L := d * d * entryBits d
    let T := τ₀.haltTime
    let H_star := ⌊thetaMacro_tight M C α * (L : ℝ)⌋₊
    d * entryBits d ≤ H_star ∧
      thetaMacro_tight M C α * (L : ℝ) ≤ ((2 * H_star : ℕ) : ℝ) ∧
      ∀ V₀ : Finset (Fin L), α * (L : ℝ) ≤ (V₀.card : ℝ) →
        ∀ B : Finset ℕ,
          IsMengerVertexCut τ₀.work T
            (V₀.image fun q => appendTime τ₀ T (tposOf d (entryBits d) q).1)
            (crossingLowerEtaSteps τ₀ T H_star 1 T) B →
          cE_frozen_tight M C α * (V₀.card : ℝ) ≤ (B.card : ℝ) := by
  intro L T H_star
  have hd_menger : bridgeMenger_d0_tight M.k C α ≤ d := (le_max_left _ _).trans hd
  have hd_2θ : ⌈2 / thetaMacro_tight M C α⌉₊ ≤ d := (le_max_right _ _).trans hd
  have hd1 : 1 ≤ d := (le_max_left _ _).trans hd_menger
  have hd0 : tightBridge_d0 M.k C ((19 / 20) * α) ≤ d := (le_max_right _ _).trans hd_menger
  have hb1 : 1 ≤ entryBits d := one_le_entryBits d
  have hθ_pos : 0 < thetaMacro_tight M C α := thetaMacro_tight_pos M C hα0
  have hW_pos : 1 ≤ d * entryBits d := Nat.mul_pos hd1 hb1
  have h2_le_θd : (2 : ℝ) ≤ thetaMacro_tight M C α * (d : ℝ) := by
    have hge : 2 / thetaMacro_tight M C α ≤ (d : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hd_2θ)
    have hmul := (div_le_iff₀ hθ_pos).mp hge
    linarith
  have hW_le_θL : ((d * entryBits d : ℕ) : ℝ) ≤ thetaMacro_tight M C α * (L : ℝ) := by
    have hW_nn : (0 : ℝ) ≤ ((d * entryBits d : ℕ) : ℝ) := by positivity
    have h1_le : (1 : ℝ) ≤ thetaMacro_tight M C α * (d : ℝ) := by linarith
    calc ((d * entryBits d : ℕ) : ℝ)
        = 1 * ((d * entryBits d : ℕ) : ℝ) := (one_mul _).symm
      _ ≤ (thetaMacro_tight M C α * (d : ℝ)) * ((d * entryBits d : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_right h1_le hW_nn
      _ = thetaMacro_tight M C α * (L : ℝ) := by dsimp [L]; push_cast; ring
  have hW_le_H : d * entryBits d ≤ H_star := Nat.le_floor hW_le_θL
  have hH_pos : 1 ≤ H_star := hW_pos.trans hW_le_H
  have hH_le_θL : (H_star : ℝ) ≤ thetaMacro_tight M C α * (L : ℝ) :=
    Nat.floor_le (by positivity)
  have h2_le_θL : (2 : ℝ) ≤ thetaMacro_tight M C α * (L : ℝ) := by
    have hd_le_L : (d : ℝ) ≤ (L : ℝ) := by
      have : d ≤ d * d * entryBits d := by
        calc d = d * 1 * 1 := by ring
          _ ≤ d * d * entryBits d := Nat.mul_le_mul (Nat.mul_le_mul le_rfl hd1) hb1
      exact_mod_cast this
    exact h2_le_θd.trans (mul_le_mul_of_nonneg_left hd_le_L hθ_pos.le)
  have hθL_le_2H : thetaMacro_tight M C α * (L : ℝ) ≤ ((2 * H_star : ℕ) : ℝ) := by
    have hlt_succ : thetaMacro_tight M C α * (L : ℝ) < (H_star : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    have hH1 : (1 : ℝ) ≤ (H_star : ℝ) := by exact_mod_cast hH_pos
    push_cast
    linarith
  obtain ⟨hT_floor, hT_pos, _, happ_eq, hdef⟩ :=
    frozenTrace_isAcyclicIn_coneSystem_deficit_le hd1 le_rfl htr hprob
  have hT_le_C : (T : ℝ) ≤ C * ((L : ℝ) + 1) := by
    have hc_nn : 0 ≤ c * ((L : ℝ) + 1) := by
      by_cases hc0 : 0 ≤ c
      · positivity
      · exfalso
        have hneg : c * ((L : ℝ) + 1) < 0 := mul_neg_of_neg_of_pos (lt_of_not_ge hc0) (by positivity)
        have hfl0 : ⌊c * (((d * d * entryBits d : ℕ) : ℝ) + 1)⌋₊ = 0 :=
          Nat.floor_of_nonpos hneg.le
        have hle0 : T ≤ 0 := hT_floor.trans_eq hfl0
        exact absurd (Nat.lt_of_lt_of_le hT_pos hle0) (lt_irrefl 0)
    calc (T : ℝ)
        ≤ (⌊c * ((L : ℝ) + 1)⌋₊ : ℝ) := by exact_mod_cast hT_floor
      _ ≤ c * ((L : ℝ) + 1) := Nat.floor_le hc_nn
      _ ≤ C * ((L : ℝ) + 1) := mul_le_mul_of_nonneg_right hc_le (by positivity)
  refine ⟨hW_le_H, hθL_le_2H, fun V₀ hV₀ B hmenger => ?_⟩
  have hL_pos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.mul_pos (Nat.mul_pos hd1 hd1) hb1
  have hα_le_1 : α ≤ 1 := by
    have hV_le : (V₀.card : ℝ) ≤ (L : ℝ) := by
      exact_mod_cast (card_le_card (subset_univ V₀)).trans_eq (by simp [L])
    have h1 : α * (L : ℝ) ≤ 1 * (L : ℝ) := by linarith
    exact le_of_mul_le_mul_right h1 hL_pos
  have hc_le_tw : cE_frozen_tight M C α ≤ 1 / 20 :=
    (cE_frozen_tight_le_one_fortieth M hC1 hα0 hα_le_1).trans (by norm_num)
  rcases le_or_gt ((1 / 20 : ℝ) * (V₀.card : ℝ)) (B.card : ℝ) with hB_big | hB_small
  · calc cE_frozen_tight M C α * (V₀.card : ℝ)
        ≤ (1 / 20 : ℝ) * (V₀.card : ℝ) := mul_le_mul_of_nonneg_right hc_le_tw (by positivity)
      _ ≤ (B.card : ℝ) := hB_big
  · let V₀' := V₀.filter fun q => appendTime τ₀ T (tposOf d (entryBits d) q).1 ∉ B
    obtain ⟨hcard_split, hsep'⟩ :=
      isBallPathSeparator_of_isMengerVertexCut (D := T) τ₀ happ_eq V₀ _ B hmenger
    have hcard_r : (V₀.card : ℝ) ≤ (V₀'.card : ℝ) + (B.card : ℝ) := by
      have hr : (V₀.card : ℝ) ≤ ((V₀'.card + B.card : ℕ) : ℝ) := by exact_mod_cast hcard_split
      simpa [Nat.cast_add] using hr
    have hV₀'_ge : (19 / 20 : ℝ) * (V₀.card : ℝ) ≤ (V₀'.card : ℝ) := by linarith
    have hV₀'_dens : ((19 / 20) * α) * (L : ℝ) ≤ (V₀'.card : ℝ) := by nlinarith
    obtain ⟨X_cell, U, hX_card, _, _, hacyc_cone, hU_ge⟩ :=
      exists_singleCell_guard_coneSystem_isIndependent_crossingLowerGT2H τ₀ hd1 hb1 hH_pos hC1
        (by positivity) happ_eq hT_le_C V₀' B hV₀'_dens hd0 hsep'
    have hdef_BX := hdef (B ∪ X_cell) U hacyc_cone
    have hunion_r : ((B ∪ X_cell).card : ℝ) ≤ (B.card : ℝ) + (X_cell.card : ℝ) := by
      exact_mod_cast card_union_le B X_cell
    have hvw_ge2 : (2 : ℝ) ≤ (valueWidth M : ℝ) := by exact_mod_cast two_le_valueWidth M
    have hvw_pos : (0 : ℝ) < (valueWidth M : ℝ) := by linarith
    have hsh_pos : (0 : ℝ) < (sharpCellGuardThresh M.k : ℝ) := by
      exact_mod_cast sharpCellGuardThresh_pos M.k
    have h5k_pos : (0 : ℝ) < ((5 * M.k + 1 : ℕ) : ℝ) := by positivity
    let ρ' := tightBridgeRho0 M.k C ((19 / 20) * α)
    have hρ'_pos : 0 < ρ' := tightBridgeRho0_pos M.k C ((19 / 20) * α)
    have hX_r : (X_cell.card : ℝ) ≤
        (sharpCellGuardThresh M.k : ℝ) * ((5 * M.k + 1 : ℕ) : ℝ) * (H_star : ℝ) := by
      have hc : (X_cell.card : ℝ) ≤
          ((sharpCellGuardThresh M.k * (5 * M.k + 1) * H_star : ℕ) : ℝ) := by
        exact_mod_cast hX_card
      simpa [Nat.cast_mul, mul_assoc] using hc
    have hvw_X : (valueWidth M : ℝ) * (X_cell.card : ℝ) ≤ (9 / 20 : ℝ) * ρ' * (V₀.card : ℝ) := by
      calc (valueWidth M : ℝ) * (X_cell.card : ℝ)
          ≤ (valueWidth M : ℝ) *
              ((sharpCellGuardThresh M.k : ℝ) * ((5 * M.k + 1 : ℕ) : ℝ) * (H_star : ℝ)) :=
            mul_le_mul_of_nonneg_left hX_r hvw_pos.le
        _ ≤ (valueWidth M : ℝ) *
              ((sharpCellGuardThresh M.k : ℝ) * ((5 * M.k + 1 : ℕ) : ℝ) *
                (thetaMacro_tight M C α * (L : ℝ))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hH_le_θL (by positivity)) hvw_pos.le
        _ = (9 / 20 : ℝ) * ρ' * (α * (L : ℝ)) := by
            dsimp [ρ']; unfold thetaMacro_tight; field_simp
        _ ≤ (9 / 20 : ℝ) * ρ' * (V₀.card : ℝ) :=
            mul_le_mul_of_nonneg_left hV₀ (by positivity)
    have hηL_le : η * (L : ℝ) ≤ (1 / 8 : ℝ) * ρ' * (V₀.card : ℝ) := by
      calc η * (L : ℝ)
          ≤ ((α / 8) * ρ') * (L : ℝ) := mul_le_mul_of_nonneg_right hη_le hL_pos.le
        _ = (1 / 8 : ℝ) * ρ' * (α * (L : ℝ)) := by ring
        _ ≤ (1 / 8 : ℝ) * ρ' * (V₀.card : ℝ) :=
            mul_le_mul_of_nonneg_left hV₀ (by positivity)
    have hU_lb : (19 / 20 : ℝ) * ρ' * (V₀.card : ℝ) ≤ (U.card : ℝ) := by
      calc (19 / 20 : ℝ) * ρ' * (V₀.card : ℝ)
          = ρ' * ((19 / 20 : ℝ) * (V₀.card : ℝ)) := by ring
        _ ≤ ρ' * (V₀'.card : ℝ) := mul_le_mul_of_nonneg_left hV₀'_ge hρ'_pos.le
        _ ≤ (U.card : ℝ) := hU_ge
    have htot_def : (U.card : ℝ) - η * (L : ℝ) ≤
        (valueWidth M : ℝ) * (B.card : ℝ) + (valueWidth M : ℝ) * (X_cell.card : ℝ) := by
      calc (U.card : ℝ) - η * (L : ℝ)
          ≤ (valueWidth M : ℝ) * ((B ∪ X_cell).card : ℝ) := by dsimp [L]; linarith [hdef_BX]
        _ ≤ (valueWidth M : ℝ) * ((B.card : ℝ) + (X_cell.card : ℝ)) :=
            mul_le_mul_of_nonneg_left hunion_r hvw_pos.le
        _ = (valueWidth M : ℝ) * (B.card : ℝ) + (valueWidth M : ℝ) * (X_cell.card : ℝ) :=
            mul_add _ _ _
    have hvw_B : (3 / 8 : ℝ) * ρ' * (V₀.card : ℝ) ≤ (valueWidth M : ℝ) * (B.card : ℝ) := by
      linarith
    unfold cE_frozen_tight
    change ((3 / 8) * ρ' / (valueWidth M : ℝ)) * (V₀.card : ℝ) ≤ (B.card : ℝ)
    rw [div_mul_eq_mul_div, div_le_iff₀ hvw_pos]
    linarith

/-- **Tightened Statement of Theorem E(b) (`Explicitly Scoped to Paper 15's Simulator N_s`):** -/
def SimulatorHeavyTraceExpansionStatement_Tight : Prop :=
  ∀ (M : TM) (c α : ℝ), 0 < c → 0 < α →
    let C_sim := adaptiveBridge_cSim c
    let η_star := adaptiveBridge_etaStar_tight M.k c α
    ∃ (s : ℕ) (hs : 0 < s) (d_sim : ℕ),
      let N_s := TapeStorageRates.Native.machine M hs
      ∀ d : ℕ, d_sim ≤ d → TransposesAt M d c →
        let L := d * d * entryBits d
        let 𝒯_heavy := SimulatorHeavyTraces N_s d (2 * η_star)
        TransposesAt N_s d C_sim ∧
        ((SimulatorTraceSupport N_s d).card : ℝ) ≤ (2 : ℝ) ^ (η_star * (L : ℝ)) ∧
        𝒯_heavy.Nonempty ∧
        (1 - (2 : ℝ) ^ (-η_star * (L : ℝ))) * (2 : ℝ) ^ L <
          (∑ τ₀ ∈ 𝒯_heavy, ((fibre N_s L τ₀).card : ℝ)) ∧
        ∀ τ₀ ∈ 𝒯_heavy,
          let T := τ₀.haltTime
          let H_star := ⌊thetaMacro_tight N_s C_sim α * (L : ℝ)⌋₊
          thetaMacro_tight N_s C_sim α * (L : ℝ) ≤ ((2 * H_star : ℕ) : ℝ) ∧
          ∀ V₀ : Finset (Fin L), α * (L : ℝ) ≤ (V₀.card : ℝ) →
            ∀ B : Finset ℕ,
              IsMengerVertexCut τ₀.work T
                (V₀.image fun q => appendTime τ₀ T (tposOf d (entryBits d) q).1)
                (crossingLowerEtaSteps τ₀ T H_star 1 T) B →
              cE_frozen_tight N_s C_sim α * (V₀.card : ℝ) ≤ (B.card : ℝ)

/-- **Tightened Theorem E(b) (`Paper 15 Simulator N_s Heavy-Trace Macroscopic Expansion`, Tower-Free!):** -/
theorem adaptive_simulator_heavyTrace_macroscopicExpansion_tight :
    SimulatorHeavyTraceExpansionStatement_Tight := by
  intro M c α hc hα
  let C_sim := adaptiveBridge_cSim c
  let η_star := adaptiveBridge_etaStar_tight M.k c α
  have hC_sim_ge1 : 1 ≤ C_sim := by dsimp [C_sim, adaptiveBridge_cSim]; linarith
  have hη_pos : 0 < η_star := adaptiveBridge_etaStar_tight_pos M.k hc.le hα
  obtain ⟨s, hs, h_ev⟩ := aligned_low_trace_dimensions M hc.le hη_pos
  obtain ⟨d_al, hd_al⟩ := eventually_atTop.mp h_ev
  let N_s := TapeStorageRates.Native.machine M hs
  let d_sim := max d_al (d0Macro_tight N_s C_sim α)
  refine ⟨s, hs, d_sim, fun d hd htrM => ?_⟩
  let L := d * d * entryBits d
  let 𝒯_heavy := SimulatorHeavyTraces N_s d (2 * η_star)
  have hd_1 : d_al ≤ d := (le_max_left _ _).trans hd
  have hd_macroN : d0Macro_tight N_s C_sim α ≤ d := (le_max_right _ _).trans hd
  have hd1 : 1 ≤ d := (le_max_left _ _).trans ((le_max_left _ _).trans hd_macroN)
  have hb1 : 1 ≤ entryBits d := one_le_entryBits d
  have hL_pos : 0 < L := Nat.mul_pos (Nat.mul_pos hd1 hd1) hb1
  obtain ⟨htrN_w, hlog_sup⟩ := hd_al d hd_1 (entryBits d) hb1 htrM
  have htrN : TransposesAt N_s d C_sim := htrN_w
  have hsup_ne : (SimulatorTraceSupport N_s d).Nonempty :=
    ⟨trace N_s (List.ofFn fun _ : Fin L => false), mem_image_of_mem _ (mem_univ _)⟩
  have hsup_pos : (0 : ℝ) < ((SimulatorTraceSupport N_s d).card : ℝ) := by
    exact_mod_cast hsup_ne.card_pos
  have hsup_le : ((SimulatorTraceSupport N_s d).card : ℝ) ≤ (2 : ℝ) ^ (η_star * (L : ℝ)) :=
    (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hsup_pos).mp hlog_sup
  let 𝒯_light := (SimulatorTraceSupport N_s d).filter fun τ₀ =>
    ¬ ((2 : ℝ) ^ (-(2 * η_star) * (L : ℝ)) ≤ traceProb N_s L τ₀)
  have hpart_cards : (univ : Finset (Fin L → Bool)).card =
      ∑ τ₀ ∈ SimulatorTraceSupport N_s d, (fibre N_s L τ₀).card :=
    card_eq_sum_card_fiberwise
      (f := fun X : Fin L → Bool => trace N_s (List.ofFn X))
      (s := (univ : Finset (Fin L → Bool)))
      (t := SimulatorTraceSupport N_s d)
      (fun X _ => mem_image_of_mem _ (mem_univ X))
  have htot_sum_r : ((2 : ℝ) ^ L) =
      ∑ τ₀ ∈ SimulatorTraceSupport N_s d, ((fibre N_s L τ₀).card : ℝ) := by
    have hcard_univ : (univ : Finset (Fin L → Bool)).card = 2 ^ L := by
      simp [Fintype.card_fin, Fintype.card_bool]
    have hnat : 2 ^ L = ∑ τ₀ ∈ SimulatorTraceSupport N_s d, (fibre N_s L τ₀).card :=
      hcard_univ.symm.trans hpart_cards
    have hcast : ((2 ^ L : ℕ) : ℝ) =
        ((∑ τ₀ ∈ SimulatorTraceSupport N_s d, (fibre N_s L τ₀).card : ℕ) : ℝ) := by
      exact_mod_cast hnat
    simpa [Nat.cast_pow, Nat.cast_sum] using hcast
  have hsplit_sum : (∑ τ₀ ∈ SimulatorTraceSupport N_s d, ((fibre N_s L τ₀).card : ℝ)) =
      (∑ τ₀ ∈ 𝒯_heavy, ((fibre N_s L τ₀).card : ℝ)) +
      (∑ τ₀ ∈ 𝒯_light, ((fibre N_s L τ₀).card : ℝ)) := by
    symm
    exact sum_filter_add_sum_filter_not (SimulatorTraceSupport N_s d)
      (fun τ₀ => (2 : ℝ) ^ (-(2 * η_star) * (L : ℝ)) ≤ traceProb N_s L τ₀)
      (fun τ₀ => ((fibre N_s L τ₀).card : ℝ))
  have hlight_term_lt : ∀ τ₀ ∈ 𝒯_light,
      ((fibre N_s L τ₀).card : ℝ) < (2 : ℝ) ^ (-(2 * η_star) * (L : ℝ)) * (2 : ℝ) ^ L := by
    intro τ₀ hτ
    have hlt_prob : traceProb N_s L τ₀ < (2 : ℝ) ^ (-(2 * η_star) * (L : ℝ)) :=
      lt_of_not_ge (mem_filter.mp hτ).2
    rw [card_fibre_eq]
    have h2L_pos : (0 : ℝ) < (2 : ℝ) ^ L := by positivity
    nlinarith
  have hlight_sum_lt : (∑ τ₀ ∈ 𝒯_light, ((fibre N_s L τ₀).card : ℝ)) <
      (2 : ℝ) ^ (-η_star * (L : ℝ)) * (2 : ℝ) ^ L := by
    by_cases hlight_ne : 𝒯_light.Nonempty
    · have h1 := sum_lt_sum_of_nonempty hlight_ne hlight_term_lt
      have hlight_card_le : (𝒯_light.card : ℝ) ≤ (2 : ℝ) ^ (η_star * (L : ℝ)) := by
        have hsub_nat : 𝒯_light.card ≤ (SimulatorTraceSupport N_s d).card :=
          card_le_card (filter_subset _ _)
        exact (by exact_mod_cast hsub_nat : (𝒯_light.card : ℝ) ≤ _).trans hsup_le
      calc (∑ τ₀ ∈ 𝒯_light, ((fibre N_s L τ₀).card : ℝ))
          < ∑ _τ₀ ∈ 𝒯_light, ((2 : ℝ) ^ (-(2 * η_star) * (L : ℝ)) * (2 : ℝ) ^ L) := h1
        _ = (𝒯_light.card : ℝ) * ((2 : ℝ) ^ (-(2 * η_star) * (L : ℝ)) * (2 : ℝ) ^ L) := by
            rw [sum_const, nsmul_eq_mul]
        _ ≤ (2 : ℝ) ^ (η_star * (L : ℝ)) *
              ((2 : ℝ) ^ (-(2 * η_star) * (L : ℝ)) * (2 : ℝ) ^ L) :=
            mul_le_mul_of_nonneg_right hlight_card_le (by positivity)
        _ = ((2 : ℝ) ^ (η_star * (L : ℝ)) * (2 : ℝ) ^ (-(2 * η_star) * (L : ℝ))) * (2 : ℝ) ^ L := by
            ring
        _ = (2 : ℝ) ^ (-η_star * (L : ℝ)) * (2 : ℝ) ^ L := by
            have hexp_eq : η_star * (L : ℝ) + -(2 * η_star) * (L : ℝ) = -η_star * (L : ℝ) := by
              ring
            rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), hexp_eq]
    · rw [Finset.not_nonempty_iff_eq_empty] at hlight_ne
      rw [hlight_ne, sum_empty]; positivity
  have hheavy_mass : (1 - (2 : ℝ) ^ (-η_star * (L : ℝ))) * (2 : ℝ) ^ L <
      (∑ τ₀ ∈ 𝒯_heavy, ((fibre N_s L τ₀).card : ℝ)) := by
    linarith [htot_sum_r, hsplit_sum, hlight_sum_lt]
  have hheavy_ne : 𝒯_heavy.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    rw [hemp, sum_empty] at hheavy_mass
    have hexp_neg : -η_star * (L : ℝ) < 0 := by
      have hL_rpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL_pos
      nlinarith
    have hrpow_lt1 : (2 : ℝ) ^ (-η_star * (L : ℝ)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 2) hexp_neg
    have h2L_pos : (0 : ℝ) < (2 : ℝ) ^ L := by positivity
    nlinarith
  refine ⟨htrN, hsup_le, hheavy_ne, hheavy_mass, fun τ₀ hτ_heavy => ?_⟩
  have hprob_τ : (2 : ℝ) ^ (-(2 * η_star) * (L : ℝ)) ≤ traceProb N_s L τ₀ :=
    (mem_filter.mp hτ_heavy).2
  have hNk : N_s.k = M.k := Native.machine_tapes M hs
  have h2η_le : 2 * η_star ≤ (α / 8) * tightBridgeRho0 N_s.k C_sim ((19 / 20) * α) := by
    rw [hNk]
    dsimp [η_star, adaptiveBridge_etaStar_tight, C_sim]
    linarith [tightBridgeRho0_pos M.k (adaptiveBridge_cSim c) ((19 / 20) * α)]
  obtain ⟨_, hθ_2H, hmenger_lb⟩ :=
    frozenTrace_macroscopicCrossingLowers_menger_lb_tight le_rfl hC_sim_ge1 hα hd_macroN htrN
      hprob_τ h2η_le
  exact ⟨hθ_2H, hmenger_lb⟩

/-- **Tightened Heavy-Trace `Theorem S(b)` (`Finite Crossing-Capable Skeleton & Single Leg`):** -/
theorem frozenTrace_reduces_to_crossingCapableSkeleton_and_singleLeg_tight
    {M : TM} {d : ℕ} {c C α η : ℝ}
    (hc_le : c ≤ C) (hC1 : 1 ≤ C) (hα0 : 0 < α)
    (hd : skeleton_d0Macro_tight M C α ≤ d)
    (htr : TransposesAt M d c) {τ₀ : Trace M.k}
    (hprob : (2 : ℝ) ^ (-η * ((d * d * entryBits d : ℕ) : ℝ)) ≤
      traceProb M (d * d * entryBits d) τ₀)
    (hη_le : η ≤ (α / 8) * tightBridgeRho0 M.k C ((19 / 20) * α))
    (V₀ : Finset (Fin (d * d * entryBits d)))
    (hV₀ : α * ((d * d * entryBits d : ℕ) : ℝ) ≤ (V₀.card : ℝ)) :
    let L := d * d * entryBits d
    let T := τ₀.haltTime
    let θ_star := thetaMacro_tight M C α
    let H_star := ⌊θ_star * (L : ℝ)⌋₊
    let Λ_star := ⌊(θ_star / 4) * (L : ℝ)⌋₊
    let M_max := skeletonMachineMaxLen_tight M C α
    1 ≤ Λ_star ∧ 2 * Λ_star ≤ H_star ∧
      traceSkeletonTuple τ₀ T Λ_star ∈ CrossingCapableSkeletonTuple M.k M_max ∧
      ∃ (j_star : Fin M.k) (r_star : ℕ),
        IsScaleFreeCrossingCapable (traceSkeletonTuple τ₀ T Λ_star j_star) ∧
        2 ≤ macroTurns (traceSkeletonTuple τ₀ T Λ_star j_star) ∧
        9 ≤ (traceSkeletonTuple τ₀ T Λ_star j_star).length ∧
        r_star ≤ macroTurns (traceSkeletonTuple τ₀ T Λ_star j_star) ∧
        r_star ≤ M_max ∧
        ∀ B : Finset ℕ,
          IsMengerVertexCut τ₀.work T
            (V₀.image fun q => appendTime τ₀ T (tposOf d (entryBits d) q).1)
            (legCrossingLowers τ₀ T H_star Λ_star j_star r_star) B →
          (cE_frozen_tight M C α / ((M.k : ℝ) * ((M_max : ℝ) + 1))) *
            (V₀.card : ℝ) ≤ (B.card : ℝ) := by
  intro L T θ_star H_star Λ_star M_max
  have hd_d0 : d0Macro_tight M C α ≤ d := (le_max_left _ _).trans hd
  have hd_8θ : ⌈8 / θ_star⌉₊ ≤ d := (le_max_right _ _).trans hd
  have hd1 : 1 ≤ d := (le_max_left _ _).trans ((le_max_left _ _).trans hd_d0)
  have hb1 : 1 ≤ entryBits d := one_le_entryBits d
  have hθ_pos : 0 < θ_star := thetaMacro_tight_pos M C hα0
  obtain ⟨_, _, hmenger_all⟩ :=
    frozenTrace_macroscopicCrossingLowers_menger_lb_tight hc_le hC1 hα0 hd_d0 htr hprob hη_le
  have hmenger_tot := hmenger_all V₀ hV₀
  obtain ⟨hT_floor, hT_pos, _, _, _⟩ :=
    frozenTrace_isAcyclicIn_coneSystem_deficit_le hd1 le_rfl htr hprob
  have hT_le_C : (T : ℝ) ≤ C * ((L : ℝ) + 1) := by
    have hc_nn : 0 ≤ c * ((L : ℝ) + 1) := by
      by_cases hc0 : 0 ≤ c
      · positivity
      · exfalso
        have hneg : c * ((L : ℝ) + 1) < 0 := mul_neg_of_neg_of_pos (lt_of_not_ge hc0) (by positivity)
        have hfl0 : ⌊c * (((d * d * entryBits d : ℕ) : ℝ) + 1)⌋₊ = 0 :=
          Nat.floor_of_nonpos hneg.le
        have hle0 : T ≤ 0 := hT_floor.trans_eq hfl0
        exact absurd (Nat.lt_of_lt_of_le hT_pos hle0) (lt_irrefl 0)
    calc (T : ℝ)
        ≤ (⌊c * ((L : ℝ) + 1)⌋₊ : ℝ) := by exact_mod_cast hT_floor
      _ ≤ c * ((L : ℝ) + 1) := Nat.floor_le hc_nn
      _ ≤ C * ((L : ℝ) + 1) := mul_le_mul_of_nonneg_right hc_le (by positivity)
  obtain ⟨hΛ1, hturns_le, hmem_bdd⟩ :=
    traceSkeletonTuple_mem_boundedSkeletonTuple τ₀ hd1 hb1 hC1 hθ_pos hd_8θ hT_le_C
  have h2Λ_le_H : 2 * Λ_star ≤ H_star := by
    apply Nat.le_floor
    have hΛ_le : (Λ_star : ℝ) ≤ (θ_star / 4) * (L : ℝ) := Nat.floor_le (by positivity)
    push_cast; linarith
  set Src := V₀.image fun q => appendTime τ₀ T (tposOf d (entryBits d) q).1
  set c_tot : ℝ := cE_frozen_tight M C α
  have hc_tot_pos : 0 < c_tot := cE_frozen_tight_pos M C α
  have hV₀_pos : (0 : ℝ) < (V₀.card : ℝ) := by
    have hL_pos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.mul_pos (Nat.mul_pos hd1 hd1) hb1
    linarith [mul_pos hα0 hL_pos]
  let Slots : Finset (Fin M.k × ℕ) :=
    ((univ : Finset (Fin M.k)) ×ˢ range (M_max + 1)).filter fun jr =>
      IsScaleFreeCrossingCapable (traceSkeletonTuple τ₀ T Λ_star jr.1) ∧
      jr.2 ≤ macroTurns (traceSkeletonTuple τ₀ T Λ_star jr.1)
  have hcover : crossingLowerEtaSteps τ₀ T H_star 1 T ⊆
      Slots.biUnion (fun jr => legCrossingLowers τ₀ T H_star Λ_star jr.1 jr.2) := by
    intro v hv
    rw [crossingLowerEtaSteps_eq_biUnion_tapeCrossingLowers] at hv
    obtain ⟨j, _, hv_tape⟩ := mem_biUnion.mp hv
    have hcap_j : IsCrossingCapableSkeleton H_star Λ_star (tapeSkeleton (τ₀.work j) T Λ_star) :=
      isCrossingCapableSkeleton_of_tapeCrossingLowers_nonempty (τ₀.work_isWalk j)
        (τ₀.work_zero j) hΛ1 ⟨v, hv_tape⟩
    obtain ⟨hsf_j, _⟩ := isScaleFreeCrossingCapable_of_two_mul_le hΛ1 h2Λ_le_H hcap_j
    let r := legOfEpoch (tapeSkeleton (τ₀.work j) T Λ_star) (epochIdx (τ₀.work j) Λ_star v)
    have hr_turns : r ≤ macroTurns (tapeSkeleton (τ₀.work j) T Λ_star) :=
      legOfEpoch_le_macroTurns _ _
    have hr_max : r < M_max + 1 := Nat.lt_succ_of_le (hr_turns.trans (hturns_le j))
    refine mem_biUnion.mpr ⟨(j, r), ?_, mem_filter.mpr ⟨hv_tape, rfl⟩⟩
    exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_univ j, mem_range.mpr hr_max⟩, hsf_j, hr_turns⟩
  have hSlots_ne : Slots.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have hdst_empty : crossingLowerEtaSteps τ₀ T H_star 1 T = ∅ := by
      rw [← subset_empty]; exact hcover.trans (by simp [hemp])
    have h0 := hmenger_tot ∅ (by rw [hdst_empty]; exact isMengerVertexCut_dst_self _ _ ∅)
    simp only [card_empty, Nat.cast_zero] at h0
    linarith [mul_pos hc_tot_pos hV₀_pos]
  obtain ⟨⟨j₀, _⟩, hj₀_mem⟩ := hSlots_ne
  have hmem_cap : traceSkeletonTuple τ₀ T Λ_star ∈ CrossingCapableSkeletonTuple M.k M_max :=
    mem_filter.mpr ⟨hmem_bdd, j₀, (mem_filter.mp hj₀_mem).2.1⟩
  have hk_pos : 0 < M.k := Fin.pos j₀
  have hSlots_card : (Slots.card : ℝ) ≤ (M.k : ℝ) * ((M_max : ℝ) + 1) := by
    have hle : Slots.card ≤ M.k * (M_max + 1) :=
      (card_le_card (filter_subset _ _)).trans (by simp [card_product])
    exact_mod_cast hle
  have hexists_slot : ∃ jr ∈ Slots, ∀ B : Finset ℕ,
      IsMengerVertexCut τ₀.work T Src (legCrossingLowers τ₀ T H_star Λ_star jr.1 jr.2) B →
      (c_tot / ((M.k : ℝ) * ((M_max : ℝ) + 1))) * (V₀.card : ℝ) ≤ (B.card : ℝ) := by
    by_contra hall_cheap
    push Not at hall_cheap
    choose B_of hB_cut hB_lt using fun jr : {x // x ∈ Slots} => hall_cheap jr.1 jr.2
    let B_u := Slots.attach.biUnion fun jr => B_of jr
    have hcut_bu : IsMengerVertexCut τ₀.work T Src
        (Slots.attach.biUnion fun jr => legCrossingLowers τ₀ T H_star Λ_star jr.1.1 jr.1.2) B_u :=
      isMengerVertexCut_biUnion Slots.attach Src
        (fun jr => legCrossingLowers τ₀ T H_star Λ_star jr.1.1 jr.1.2) B_of
        (fun jr _ => hB_cut jr)
    have hcut_tot : IsMengerVertexCut τ₀.work T Src (crossingLowerEtaSteps τ₀ T H_star 1 T) B_u := by
      intro π t₀ hsrc hdep hlast
      have hcov_last := hcover hlast
      obtain ⟨jr, hjrS, hmem_jr⟩ := mem_biUnion.mp hcov_last
      exact hcut_bu π t₀ hsrc hdep (mem_biUnion.mpr ⟨⟨jr, hjrS⟩, mem_attach _ _, hmem_jr⟩)
    have hbu_card_nat : B_u.card ≤ ∑ jr ∈ Slots.attach, (B_of jr).card := card_biUnion_le
    have hbu_card_r : (B_u.card : ℝ) ≤ ∑ jr ∈ Slots.attach, ((B_of jr).card : ℝ) := by
      exact_mod_cast hbu_card_nat
    have hsum_lt : ∑ jr ∈ Slots.attach, ((B_of jr).card : ℝ) <
        ∑ _jr ∈ Slots.attach, (c_tot / ((M.k : ℝ) * ((M_max : ℝ) + 1))) * (V₀.card : ℝ) :=
      sum_lt_sum_of_nonempty (Slots.attach_nonempty_iff.mpr ⟨⟨j₀, _⟩, hj₀_mem⟩)
        (fun jr _ => hB_lt jr)
    have hconst_sum : (∑ _jr ∈ Slots.attach,
        (c_tot / ((M.k : ℝ) * ((M_max : ℝ) + 1))) * (V₀.card : ℝ)) ≤
        c_tot * (V₀.card : ℝ) := by
      rw [sum_const, card_attach, nsmul_eq_mul]
      have hdenom_pos : (0 : ℝ) < (M.k : ℝ) * ((M_max : ℝ) + 1) := by
        have : (0 : ℝ) < (M.k : ℝ) := by exact_mod_cast hk_pos
        positivity
      calc (Slots.card : ℝ) * ((c_tot / ((M.k : ℝ) * ((M_max : ℝ) + 1))) * (V₀.card : ℝ))
          ≤ ((M.k : ℝ) * ((M_max : ℝ) + 1)) *
              ((c_tot / ((M.k : ℝ) * ((M_max : ℝ) + 1))) * (V₀.card : ℝ)) :=
            mul_le_mul_of_nonneg_right hSlots_card (by positivity)
        _ = c_tot * (V₀.card : ℝ) := by field_simp
    have htot_lb := hmenger_tot B_u hcut_tot
    linarith
  obtain ⟨⟨j_star, r_star⟩, hjr_mem, hjr_exp⟩ := hexists_slot
  obtain ⟨hprod_mem, hsf_star, hr_turns⟩ := mem_filter.mp hjr_mem
  have hr_max : r_star ≤ M_max := Nat.le_of_lt_succ (mem_range.mp (mem_product.mp hprod_mem).2)
  have hleg_ne : (legCrossingLowers τ₀ T H_star Λ_star j_star r_star).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have h0 := hjr_exp ∅ (by rw [hemp]; exact isMengerVertexCut_dst_self _ _ ∅)
    simp only [card_empty, Nat.cast_zero] at h0
    have hdenom_pos : (0 : ℝ) < (M.k : ℝ) * ((M_max : ℝ) + 1) := by
      have : (0 : ℝ) < (M.k : ℝ) := by exact_mod_cast hk_pos
      positivity
    linarith [mul_pos (div_pos hc_tot_pos hdenom_pos) hV₀_pos]
  obtain ⟨v_w, hv_w⟩ := hleg_ne
  have hcap_star := isCrossingCapableSkeleton_of_tapeCrossingLowers_nonempty
    (τ₀.work_isWalk j_star) (τ₀.work_zero j_star) hΛ1 ⟨v_w, (mem_filter.mp hv_w).1⟩
  obtain ⟨_, hlen9⟩ := isScaleFreeCrossingCapable_of_two_mul_le hΛ1 h2Λ_le_H hcap_star
  exact ⟨hΛ1, h2Λ_le_H, hmem_cap, j_star, r_star, hsf_star,
    two_le_macroTurns_of_isScaleFreeCrossingCapable hsf_star, hlen9, hr_turns, hr_max, hjr_exp⟩

/-- **Tightened Heavy-Trace Lift of Theorem S to Paper 15's Aligned Simulator `N_s = Native.machine M hs`:** -/
theorem simulator_heavyTrace_reduces_to_crossingCapableSkeleton_and_singleLeg_tight
    (M : TM) {c α : ℝ} (hc : 0 < c) (hα : 0 < α) :
    let C_sim := adaptiveBridge_cSim c
    let η_star := adaptiveBridge_etaStar_tight M.k c α
    ∃ (s : ℕ) (hs : 0 < s) (d_skel_sim : ℕ),
      let N_s := TapeStorageRates.Native.machine M hs
      let M_max := skeletonMachineMaxLen_tight N_s C_sim α
      ∀ d : ℕ, d_skel_sim ≤ d → TransposesAt M d c →
        let L := d * d * entryBits d
        let 𝒯_heavy := SimulatorHeavyTraces N_s d (2 * η_star)
        TransposesAt N_s d C_sim ∧
        𝒯_heavy.Nonempty ∧
        (1 - (2 : ℝ) ^ (-η_star * (L : ℝ))) * (2 : ℝ) ^ L <
          (∑ τ₀ ∈ 𝒯_heavy, ((fibre N_s L τ₀).card : ℝ)) ∧
        ∀ τ₀ ∈ 𝒯_heavy, ∀ V₀ : Finset (Fin L), α * (L : ℝ) ≤ (V₀.card : ℝ) →
          let T := τ₀.haltTime
          let θ_star := thetaMacro_tight N_s C_sim α
          let H_star := ⌊θ_star * (L : ℝ)⌋₊
          let Λ_star := ⌊(θ_star / 4) * (L : ℝ)⌋₊
          1 ≤ Λ_star ∧ 2 * Λ_star ≤ H_star ∧
            traceSkeletonTuple τ₀ T Λ_star ∈ CrossingCapableSkeletonTuple N_s.k M_max ∧
            ∃ (j_star : Fin N_s.k) (r_star : ℕ),
              IsScaleFreeCrossingCapable (traceSkeletonTuple τ₀ T Λ_star j_star) ∧
              2 ≤ macroTurns (traceSkeletonTuple τ₀ T Λ_star j_star) ∧
              9 ≤ (traceSkeletonTuple τ₀ T Λ_star j_star).length ∧
              r_star ≤ macroTurns (traceSkeletonTuple τ₀ T Λ_star j_star) ∧
              r_star ≤ M_max ∧
              ∀ B : Finset ℕ,
                IsMengerVertexCut τ₀.work T
                  (V₀.image fun q => appendTime τ₀ T (tposOf d (entryBits d) q).1)
                  (legCrossingLowers τ₀ T H_star Λ_star j_star r_star) B →
                (cE_frozen_tight N_s C_sim α /
                    ((N_s.k : ℝ) * ((M_max : ℝ) + 1))) * (V₀.card : ℝ) ≤ (B.card : ℝ) := by
  intro C_sim η_star
  obtain ⟨s, hs, d_sim, hsim⟩ :=
    adaptive_simulator_heavyTrace_macroscopicExpansion_tight M c α hc hα
  let N_s := TapeStorageRates.Native.machine M hs
  have hC_sim_ge1 : 1 ≤ C_sim := by dsimp [C_sim, adaptiveBridge_cSim]; linarith
  refine ⟨s, hs, max d_sim (skeleton_d0Macro_tight N_s C_sim α), fun d hd htrM => ?_⟩
  have hd_sim : d_sim ≤ d := (le_max_left _ _).trans hd
  have hd_skel : skeleton_d0Macro_tight N_s C_sim α ≤ d := (le_max_right _ _).trans hd
  obtain ⟨htrN, _, hne, hmass, _⟩ := hsim d hd_sim htrM
  refine ⟨htrN, hne, hmass, fun τ₀ hτ V₀ hV₀ => ?_⟩
  have hprob_τ : (2 : ℝ) ^ (-(2 * η_star) * ((d * d * entryBits d : ℕ) : ℝ)) ≤
      traceProb N_s (d * d * entryBits d) τ₀ :=
    (mem_filter.mp hτ).2
  have hNk : N_s.k = M.k := Native.machine_tapes M hs
  have h2η_le : 2 * η_star ≤ (α / 8) * tightBridgeRho0 N_s.k C_sim ((19 / 20) * α) := by
    rw [hNk]
    dsimp [η_star, adaptiveBridge_etaStar_tight, C_sim]
    linarith [tightBridgeRho0_pos M.k (adaptiveBridge_cSim c) ((19 / 20) * α)]
  exact frozenTrace_reduces_to_crossingCapableSkeleton_and_singleLeg_tight le_rfl hC_sim_ge1 hα
    hd_skel htrN hprob_τ h2η_le V₀ hV₀

end TightenedFrozenAndSimulatorHeadlines

/-! ## §7. Number-Free Public Names & Explicit `α ≤ 1` `V₀`-Free Corollaries -/

section PublicNamesAndAlphaLeOne

/-- **Number-Free `V₀`-Free Macroscopic Crossings Theorem with Explicit `α ≤ 1`:**
Under `0 < α` and `α ≤ 1`, `V₀ := univ` satisfies `α * L ≤ |univ|`, so `crossingLowerEtaSteps` itself
has cardinality at least `cE_menger_tight M C α * L` (`linearly many macroscopic crossings`), while
every `V₀` with `|V₀| ≥ α * L` has Menger vertex expansion `≥ cE_menger_tight M C α * |V₀|`. -/
theorem obliviousLinTime_macroscopicCrossingLowers_card_and_menger_tight
    {M : TM} {d T : ℕ} {C α : ℝ}
    (hC : 1 ≤ C) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hd : d0Macro_tight M C α ≤ d)
    (hobl_lt : ObliviousLinTime M d (entryBits d) C T) :
    let L := d * d * entryBits d
    let H_star := ⌊thetaMacro_tight M C α * (L : ℝ)⌋₊
    d * entryBits d ≤ H_star ∧
      thetaMacro_tight M C α * (L : ℝ) ≤ ((2 * H_star : ℕ) : ℝ) ∧
      cE_menger_tight M C α * (L : ℝ) ≤
        ((crossingLowerEtaSteps (traceAt M L) T H_star 1 T).card : ℝ) ∧
      ∀ V₀ : Finset (Fin L), α * (L : ℝ) ≤ (V₀.card : ℝ) →
        ∀ B : Finset ℕ,
          IsMengerVertexCut (traceAt M L).work T
            (V₀.image fun q => appendTime (traceAt M L) T (tposOf d (entryBits d) q).1)
            (crossingLowerEtaSteps (traceAt M L) T H_star 1 T) B →
          cE_menger_tight M C α * (V₀.card : ℝ) ≤ (B.card : ℝ) := by
  intro L H_star
  have hV_univ : α * ((d * d * entryBits d : ℕ) : ℝ) ≤
      ((univ : Finset (Fin (d * d * entryBits d))).card : ℝ) := by
    have hcard : ((univ : Finset (Fin (d * d * entryBits d))).card : ℝ) =
        1 * ((d * d * entryBits d : ℕ) : ℝ) := by simp
    rw [hcard]
    exact mul_le_mul_of_nonneg_right hα1 (Nat.cast_nonneg _)
  obtain ⟨hW_le_H, hθ_le_2H, hm_univ⟩ :=
    obliviousLinTime_macroscopicCrossingLowers_menger_lb_tight
      hC hα0 hd hobl_lt univ hV_univ
  have hcard_dst := hm_univ (crossingLowerEtaSteps (traceAt M L) T H_star 1 T)
    (isMengerVertexCut_dst_self _ _ _)
  simp only [card_univ, Fintype.card_fin] at hcard_dst
  refine ⟨hW_le_H, hθ_le_2H, hcard_dst, fun V₀ hV₀ B hmB => ?_⟩
  exact (obliviousLinTime_macroscopicCrossingLowers_menger_lb_tight
    hC hα0 hd hobl_lt V₀ hV₀).2.2 B hmB

/-- **Number-Free `V₀`-Free Crossing-Capable Skeleton Theorem with Explicit `α ≤ 1`:**
Under `0 < α` and `α ≤ 1`, `traceSkeletonTuple τ₀ T Λ_* ∈ CrossingCapableSkeletonTuple M.k M_max` holds
unconditionally (`without quantifying over an external V₀`), and every `V₀` with `|V₀| ≥ α * L` admits
a single `(j_*, r_*)` leg carrying linear Menger expansion. -/
theorem obliviousLinTime_crossingCapableSkeleton_and_singleLeg_of_le_one_tight
    {M : TM} {d T : ℕ} {C α : ℝ}
    (hC : 1 ≤ C) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hd : skeleton_d0Macro_tight M C α ≤ d)
    (hobl_lt : ObliviousLinTime M d (entryBits d) C T) :
    let L := d * d * entryBits d
    let θ_star := thetaMacro_tight M C α
    let H_star := ⌊θ_star * (L : ℝ)⌋₊
    let Λ_star := ⌊(θ_star / 4) * (L : ℝ)⌋₊
    let M_max := skeletonMachineMaxLen_tight M C α
    let τ₀ := traceAt M L
    1 ≤ Λ_star ∧ 2 * Λ_star ≤ H_star ∧
      traceSkeletonTuple τ₀ T Λ_star ∈ CrossingCapableSkeletonTuple M.k M_max ∧
      ∀ V₀ : Finset (Fin L), α * (L : ℝ) ≤ (V₀.card : ℝ) →
        ∃ (j_star : Fin M.k) (r_star : ℕ),
          IsScaleFreeCrossingCapable (traceSkeletonTuple τ₀ T Λ_star j_star) ∧
          2 ≤ macroTurns (traceSkeletonTuple τ₀ T Λ_star j_star) ∧
          9 ≤ (traceSkeletonTuple τ₀ T Λ_star j_star).length ∧
          r_star ≤ macroTurns (traceSkeletonTuple τ₀ T Λ_star j_star) ∧
          r_star ≤ M_max ∧
          ∀ B : Finset ℕ,
            IsMengerVertexCut τ₀.work T
              (V₀.image fun q => appendTime τ₀ T (tposOf d (entryBits d) q).1)
              (legCrossingLowers τ₀ T H_star Λ_star j_star r_star) B →
            (cE_menger_tight M C α / ((M.k : ℝ) * ((M_max : ℝ) + 1))) *
              (V₀.card : ℝ) ≤ (B.card : ℝ) := by
  intro L θ_star H_star Λ_star M_max τ₀
  have hV_univ : α * ((d * d * entryBits d : ℕ) : ℝ) ≤
      ((univ : Finset (Fin (d * d * entryBits d))).card : ℝ) := by
    have hcard : ((univ : Finset (Fin (d * d * entryBits d))).card : ℝ) =
        1 * ((d * d * entryBits d : ℕ) : ℝ) := by simp
    rw [hcard]
    exact mul_le_mul_of_nonneg_right hα1 (Nat.cast_nonneg _)
  obtain ⟨hΛ1, h2Λ_le_H, hmem_cap, _⟩ :=
    obliviousLinTime_reduces_to_crossingCapableSkeleton_and_singleLeg_tight
      hC hα0 hd hobl_lt univ hV_univ
  refine ⟨hΛ1, h2Λ_le_H, hmem_cap, fun V₀ hV₀ => ?_⟩
  exact (obliviousLinTime_reduces_to_crossingCapableSkeleton_and_singleLeg_tight
    hC hα0 hd hobl_lt V₀ hV₀).2.2.2

/-- Unified single-simulator Theorem E(b): for one alignment scale `s > 0` and one threshold `d_sim`,
the simulator `N_s = TapeStorageRates.Native.machine M hs` simultaneously satisfies the trace-count
bound, heavy-trace mass bound, `W ≤ H_*`, `θ_* L ≤ 2 H_*`, macroscopic crossing expansion, and
finite crossing-capable skeleton + single-leg localization on every `2 η_*`-heavy trace. -/
theorem simulator_heavyTrace_expansion_and_skeleton_tight
    (M : TM) {c α : ℝ} (hc : 0 < c) (hα0 : 0 < α) (hα1 : α ≤ 1) :
    let C_sim := adaptiveBridge_cSim c
    let η_star := adaptiveBridge_etaStar_tight M.k c α
    ∃ (s : ℕ) (hs : 0 < s) (d_sim : ℕ),
      let N_s := TapeStorageRates.Native.machine M hs
      let M_max := skeletonMachineMaxLen_tight N_s C_sim α
      ∀ d : ℕ, d_sim ≤ d → TransposesAt M d c →
        let L := d * d * entryBits d
        let 𝒯_heavy := SimulatorHeavyTraces N_s d (2 * η_star)
        TransposesAt N_s d C_sim ∧
        ((SimulatorTraceSupport N_s d).card : ℝ) ≤ (2 : ℝ) ^ (η_star * (L : ℝ)) ∧
        𝒯_heavy.Nonempty ∧
        (1 - (2 : ℝ) ^ (-η_star * (L : ℝ))) * (2 : ℝ) ^ L <
          (∑ τ₀ ∈ 𝒯_heavy, ((fibre N_s L τ₀).card : ℝ)) ∧
        ∀ τ₀ ∈ 𝒯_heavy,
          let T := τ₀.haltTime
          let θ_star := thetaMacro_tight N_s C_sim α
          let H_star := ⌊θ_star * (L : ℝ)⌋₊
          let Λ_star := ⌊(θ_star / 4) * (L : ℝ)⌋₊
          d * entryBits d ≤ H_star ∧
          θ_star * (L : ℝ) ≤ ((2 * H_star : ℕ) : ℝ) ∧
          1 ≤ Λ_star ∧ 2 * Λ_star ≤ H_star ∧
          traceSkeletonTuple τ₀ T Λ_star ∈ CrossingCapableSkeletonTuple N_s.k M_max ∧
          (∀ V₀ : Finset (Fin L), α * (L : ℝ) ≤ (V₀.card : ℝ) →
            (∀ B : Finset ℕ,
              IsMengerVertexCut τ₀.work T
                (V₀.image fun q => appendTime τ₀ T (tposOf d (entryBits d) q).1)
                (crossingLowerEtaSteps τ₀ T H_star 1 T) B →
              cE_frozen_tight N_s C_sim α * (V₀.card : ℝ) ≤ (B.card : ℝ)) ∧
            (∃ (j_star : Fin N_s.k) (r_star : ℕ),
              IsScaleFreeCrossingCapable (traceSkeletonTuple τ₀ T Λ_star j_star) ∧
              2 ≤ macroTurns (traceSkeletonTuple τ₀ T Λ_star j_star) ∧
              9 ≤ (traceSkeletonTuple τ₀ T Λ_star j_star).length ∧
              r_star ≤ macroTurns (traceSkeletonTuple τ₀ T Λ_star j_star) ∧
              r_star ≤ M_max ∧
              ∀ B : Finset ℕ,
                IsMengerVertexCut τ₀.work T
                  (V₀.image fun q => appendTime τ₀ T (tposOf d (entryBits d) q).1)
                  (legCrossingLowers τ₀ T H_star Λ_star j_star r_star) B →
                (cE_frozen_tight N_s C_sim α /
                    ((N_s.k : ℝ) * ((M_max : ℝ) + 1))) * (V₀.card : ℝ) ≤ (B.card : ℝ))) := by
  intro C_sim η_star
  obtain ⟨s, hs, d_sim₀, hsim⟩ :=
    adaptive_simulator_heavyTrace_macroscopicExpansion_tight M c α hc hα0
  let N_s := TapeStorageRates.Native.machine M hs
  have hC_sim_ge1 : 1 ≤ C_sim := by dsimp [C_sim, adaptiveBridge_cSim]; linarith
  refine ⟨s, hs, max d_sim₀ (skeleton_d0Macro_tight N_s C_sim α), fun d hd htrM => ?_⟩
  have hd_sim₀ : d_sim₀ ≤ d := (le_max_left _ _).trans hd
  have hd_skel : skeleton_d0Macro_tight N_s C_sim α ≤ d := (le_max_right _ _).trans hd
  have hd_d0 : d0Macro_tight N_s C_sim α ≤ d := (le_max_left _ _).trans hd_skel
  obtain ⟨htrN, hsup, hne, hmass, hheavy_exp⟩ := hsim d hd_sim₀ htrM
  have hV_univ : α * ((d * d * entryBits d : ℕ) : ℝ) ≤
      ((univ : Finset (Fin (d * d * entryBits d))).card : ℝ) := by
    have hcard : ((univ : Finset (Fin (d * d * entryBits d))).card : ℝ) =
        1 * ((d * d * entryBits d : ℕ) : ℝ) := by simp
    rw [hcard]
    exact mul_le_mul_of_nonneg_right hα1 (Nat.cast_nonneg _)
  refine ⟨htrN, hsup, hne, hmass, fun τ₀ hτ => ?_⟩
  have hprob_τ : (2 : ℝ) ^ (-(2 * η_star) * ((d * d * entryBits d : ℕ) : ℝ)) ≤
      traceProb N_s (d * d * entryBits d) τ₀ :=
    (mem_filter.mp hτ).2
  have hNk : N_s.k = M.k := Native.machine_tapes M hs
  have h2η_le : 2 * η_star ≤ (α / 8) * tightBridgeRho0 N_s.k C_sim ((19 / 20) * α) := by
    rw [hNk]
    dsimp [η_star, adaptiveBridge_etaStar_tight, C_sim]
    linarith [tightBridgeRho0_pos M.k (adaptiveBridge_cSim c) ((19 / 20) * α)]
  obtain ⟨hW_le_H, hθ_2H, hmenger_X⟩ :=
    frozenTrace_macroscopicCrossingLowers_menger_lb_tight le_rfl hC_sim_ge1 hα0 hd_d0 htrN
      hprob_τ h2η_le
  obtain ⟨hΛ1, h2Λ_le_H, hmem_cap, _⟩ :=
    frozenTrace_reduces_to_crossingCapableSkeleton_and_singleLeg_tight le_rfl hC_sim_ge1 hα0
      hd_skel htrN hprob_τ h2η_le univ hV_univ
  refine ⟨hW_le_H, hθ_2H, hΛ1, h2Λ_le_H, hmem_cap, fun V₀ hV₀ => ⟨hmenger_X V₀ hV₀, ?_⟩⟩
  exact (frozenTrace_reduces_to_crossingCapableSkeleton_and_singleLeg_tight le_rfl hC_sim_ge1 hα0
    hd_skel htrN hprob_τ h2η_le V₀ hV₀).2.2.2

end PublicNamesAndAlphaLeOne

end NativeRelations
