import NativeRelations.OneFreeHeadSmallExcursion
import LeanMachine.BlockRanking
import NativeRelations.DichromaticCrux

/-!
# Window, Block-Ranking, and Step-Invariant Certificates; Cut Cruxes

Establishes the trace-level certificate toolkit (`acyclicIn_of_lt_on_nbhd`, `upperEnvelope_isAcyclicIn`,
`oneSidedEnvelope_isAcyclicIn`, `window_isAcyclicIn_of_noFarArcs`, `exists_isAcyclicIn_of_window_maxDeg`,
`cutSet_isAcyclicIn`, `exists_isAcyclicIn_card_ge_of_blockCut` via `LeanMachine.BlockRanking`,
`isAcyclicIn_ballAvoid_window_of_stepInvariant`), defines `MachineCutCruxAt`, `SubpopCutCruxAt`,
`ballAvoidSystem`, and `IsBallPathSeparator`, and proves `subpop_cutcrux_excludes` and the two-cut
covering of non-crossing large revisits (`exists_two_cuts_covering_nonCrossingLargeHops`).
-/

set_option autoImplicit false

namespace NativeRelations

open Filter Finset Transpose Transpose.Tape BoundedNesting MergeDepth MotionDepthCodes
  BoundedStackDepth TapeStorageRates
open scoped BigOperators

/-! ## §1. Strict Potential Orientation & Multi-Branch Footprint Envelopes (Lemma 3.7) -/

section EnvelopeLemmas

variable {V α : Type*}

/-- **Strict potential decrease along arcs implies `HalfRate.IsAcyclicIn`.**
Note that looplessness (`v ∉ N v` for `v ∈ S`) holds automatically from irreflexivity of `<`. -/
theorem acyclicIn_of_lt_on_nbhd [LinearOrder α] {N : V → Finset V} {S : Finset V} {φ : V → α}
    (hlt : ∀ v ∈ S, ∀ u ∈ N v, u ∈ S → φ u < φ v) :
    HalfRate.IsAcyclicIn N S := by
  classical
  intro T hTS hTne
  have himg : (T.image φ).Nonempty := hTne.image φ
  obtain ⟨v, hvT, hφv⟩ := mem_image.mp ((T.image φ).min'_mem himg)
  refine ⟨v, hvT, fun u hu hv_mem => ?_⟩
  have hlt_uv : φ u < φ v := hlt v (hTS hvT) u hu (hTS hv_mem)
  have hle_vu : (T.image φ).min' himg ≤ φ u :=
    (T.image φ).min'_le (φ u) (mem_image_of_mem φ hv_mem)
  rw [← hφv] at hle_vu
  exact not_lt_of_ge hle_vu hlt_uv

/-- **Strict potential increase along arcs implies `HalfRate.IsAcyclicIn`.** -/
theorem acyclicIn_of_gt_on_nbhd [LinearOrder α] {N : V → Finset V} {S : Finset V} {φ : V → α}
    (hgt : ∀ v ∈ S, ∀ u ∈ N v, u ∈ S → φ v < φ u) :
    HalfRate.IsAcyclicIn N S :=
  acyclicIn_of_lt_on_nbhd (α := αᵒᵈ) hgt

/-- Upper footprint-envelope candidate set `U⁺ = {q ∈ V₀ : Ψ_up q < φ q}` (Lemma 3.7). -/
def upperEnvelopeSet [LinearOrder α] (V₀ : Finset V) (φ Ψ_up : V → α) : Finset V :=
  V₀.filter fun q => Ψ_up q < φ q

/-- **Lemma 3.7(a) (Upper Multi-Branch Footprint Envelope Lemma).**
If `Ψ_up p` upper-bounds `φ r` across every in-neighbor `r ∈ V₀` of `p ∈ V₀` (`p ∈ N r`), then
`U⁺ = {q ∈ V₀ : Ψ_up q < φ q}` induces a strictly acyclic sub-relation with zero self-loops. -/
theorem upperEnvelope_isAcyclicIn [DecidableEq V] [LinearOrder α]
    {N : V → Finset V} {V₀ : Finset V} {φ Ψ_up : V → α}
    (henv : ∀ p ∈ V₀, ∀ r ∈ V₀, p ∈ N r → φ r ≤ Ψ_up p) :
    HalfRate.IsAcyclicIn N (upperEnvelopeSet V₀ φ Ψ_up) := by
  refine acyclicIn_of_gt_on_nbhd (φ := φ) fun v hv u huv hu => ?_
  obtain ⟨hv0, _⟩ := mem_filter.mp hv
  obtain ⟨hu0, hlt_u⟩ := mem_filter.mp hu
  exact (henv u hu0 v hv0 huv).trans_lt hlt_u

end EnvelopeLemmas

/-! ## §2. Bounded-Degree Greedy Extraction, Lemma 3.7(b), and the `Window Lemma` -/

section OneSidedAndWindow

variable {V : Type*} [DecidableEq V]

/-- **Greedy conflict-free subset extraction under bounded symmetric conflict degree `≤ β`.**
Given `U : Finset V` and `bad : V → V → Prop`, if every `v ∈ U` participates in at most `β`
conflicts `{w ∈ U \ {v} : bad v w ∨ bad w v}`, then there exists `S ⊆ U` free of internal
conflicts (`∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ bad x y`) with `U.card ≤ (β + 1) * S.card`. -/
theorem exists_conflictFree_card_mul_ge (U : Finset V) (bad : V → V → Prop) [DecidableRel bad] (β : ℕ)
    (hdeg : ∀ v ∈ U, ((U.erase v).filter fun w => bad v w ∨ bad w v).card ≤ β) :
    ∃ S ⊆ U, (∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ bad x y) ∧ U.card ≤ (β + 1) * S.card := by
  revert U
  suffices hmain : ∀ n : ℕ, ∀ U : Finset V, U.card = n →
      (∀ v ∈ U, ((U.erase v).filter fun w => bad v w ∨ bad w v).card ≤ β) →
      ∃ S ⊆ U, (∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ bad x y) ∧ U.card ≤ (β + 1) * S.card by
    intro U hdeg
    exact hmain U.card U rfl hdeg
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro U hcard hdegU
    rcases U.eq_empty_or_nonempty with rfl | ⟨v₀, hv₀⟩
    · exact ⟨∅, Subset.rfl, fun _ hx => absurd hx (notMem_empty _), by simp⟩
    · let B₀ := (U.erase v₀).filter fun w => bad v₀ w ∨ bad w v₀
      let U' := U.erase v₀ \ B₀
      have hB₀_sub : B₀ ⊆ U.erase v₀ := filter_subset _ _
      have hB₀_le : B₀.card ≤ β := hdegU v₀ hv₀
      have herase_card : (U.erase v₀).card + 1 = U.card := card_erase_add_one hv₀
      have hsdiff_card : U'.card + B₀.card = (U.erase v₀).card := by
        have h1 := card_sdiff_add_card_inter (U.erase v₀) B₀
        rwa [inter_eq_right.mpr hB₀_sub] at h1
      have hU'_lt : U'.card < n := by omega
      have hU'_sub : U' ⊆ U := sdiff_subset.trans (erase_subset v₀ U)
      have hdegU' : ∀ v ∈ U', ((U'.erase v).filter fun w => bad v w ∨ bad w v).card ≤ β := by
        intro v hv
        refine (card_le_card ?_).trans (hdegU v (hU'_sub hv))
        intro w hw
        obtain ⟨hw_er, hbad⟩ := mem_filter.mp hw
        obtain ⟨hw_ne, hw_U'⟩ := mem_erase.mp hw_er
        exact mem_filter.mpr ⟨mem_erase.mpr ⟨hw_ne, hU'_sub hw_U'⟩, hbad⟩
      obtain ⟨S', hS'_sub, hS'_cf, hS'_card⟩ := ih U'.card hU'_lt U' rfl hdegU'
      have hv₀_not_U' : v₀ ∉ U' := fun h => (mem_erase.mp (sdiff_subset h)).1 rfl
      have hv₀_not_S' : v₀ ∉ S' := fun h => hv₀_not_U' (hS'_sub h)
      refine ⟨insert v₀ S', insert_subset hv₀ (hS'_sub.trans hU'_sub), ?_, ?_⟩
      · intro x hx y hy hxy hbad_xy
        rcases mem_insert.mp hx with rfl | hxS'
        · rcases mem_insert.mp hy with rfl | hyS'
          · exact hxy rfl
          · have hyU' : y ∈ U' := hS'_sub hyS'
            have hy_not_B₀ : y ∉ B₀ := (mem_sdiff.mp hyU').2
            exact hy_not_B₀ (mem_filter.mpr ⟨(mem_sdiff.mp hyU').1, Or.inl hbad_xy⟩)
        · rcases mem_insert.mp hy with rfl | hyS'
          · have hxU' : x ∈ U' := hS'_sub hxS'
            have hx_not_B₀ : x ∉ B₀ := (mem_sdiff.mp hxU').2
            exact hx_not_B₀ (mem_filter.mpr ⟨(mem_sdiff.mp hxU').1, Or.inr hbad_xy⟩)
          · exact hS'_cf x hxS' y hyS' hxy hbad_xy
      · rw [card_insert_of_notMem hv₀_not_S']
        calc U.card ≤ U'.card + β + 1 := by omega
          _ ≤ (β + 1) * S'.card + (β + 1) := by omega
          _ = (β + 1) * (S'.card + 1) := by ring

/-- One-sided envelope candidate set `U_env = {q ∈ V₀ : q ∉ N q ∧ φ q + w < ψ q}` (Lemma 3.7(b)). -/
noncomputable def oneSidedEnvelopeSet (N : V → Finset V) (V₀ : Finset V) (φ ψ : V → ℝ) (w : ℝ) :
    Finset V :=
  V₀.filter fun q => q ∉ N q ∧ φ q + w < ψ q

/-- **Lemma 3.7(b), Zero-Exception Case (`β = 0`).**
If every arc `p ∈ N q` inside `U_env` satisfies `ψ p ≤ φ q + w`, then `U_env` is strictly acyclic. -/
theorem oneSidedEnvelope_isAcyclicIn {N : V → Finset V} {V₀ : Finset V} {φ ψ : V → ℝ} {w : ℝ}
    (hsub : ∀ q ∈ oneSidedEnvelopeSet N V₀ φ ψ w,
      ∀ p ∈ N q, p ∈ oneSidedEnvelopeSet N V₀ φ ψ w → ψ p ≤ φ q + w) :
    HalfRate.IsAcyclicIn N (oneSidedEnvelopeSet N V₀ φ ψ w) := by
  refine acyclicIn_of_lt_on_nbhd (φ := φ) fun q hq p hpq hp => ?_
  have hsub_qp := hsub q hq p hpq hp
  unfold oneSidedEnvelopeSet at hp
  obtain ⟨-, ⟨-, hlt_p⟩⟩ := mem_filter.mp hp
  linarith

/-- **Lemma 3.7(b) (One-Sided Envelope Lemma under Max Exception Degree `≤ β`).**
If every `q ∈ U_env` has at most `β` incoming+outgoing exception neighbors `p ∈ U_env \ {q}`
violating `ψ p ≤ φ q + w`, then `U_env` contains an acyclic subset `S` with
`U_env.card ≤ (β + 1) * S.card`. -/
theorem exists_isAcyclicIn_of_oneSidedEnvelope_maxDeg
    {N : V → Finset V} {V₀ : Finset V} {φ ψ : V → ℝ} {w : ℝ} {β : ℕ}
    (hdeg : ∀ q ∈ oneSidedEnvelopeSet N V₀ φ ψ w,
      (((oneSidedEnvelopeSet N V₀ φ ψ w).erase q).filter fun p =>
        (p ∈ N q ∧ ¬ ψ p ≤ φ q + w) ∨ (q ∈ N p ∧ ¬ ψ q ≤ φ p + w)).card ≤ β) :
    ∃ S ⊆ oneSidedEnvelopeSet N V₀ φ ψ w,
      HalfRate.IsAcyclicIn N S ∧
      (oneSidedEnvelopeSet N V₀ φ ψ w).card ≤ (β + 1) * S.card := by
  obtain ⟨S, hSU, hcf, hcard⟩ := exists_conflictFree_card_mul_ge
    (oneSidedEnvelopeSet N V₀ φ ψ w) (fun q p => p ∈ N q ∧ ¬ ψ p ≤ φ q + w) β hdeg
  refine ⟨S, hSU, ?_, hcard⟩
  refine acyclicIn_of_lt_on_nbhd (φ := φ) fun q hq p hpq hp => ?_
  have hqU := hSU hq
  have hpU := hSU hp
  unfold oneSidedEnvelopeSet at hqU hpU
  obtain ⟨-, ⟨hq_noloop, -⟩⟩ := mem_filter.mp hqU
  obtain ⟨-, ⟨-, hlt_p⟩⟩ := mem_filter.mp hpU
  have hp_ne_q : p ≠ q := fun heq => hq_noloop (heq ▸ hpq)
  have hnot_bad := hcf q hq p hp hp_ne_q.symm
  have hle : ψ p ≤ φ q + w := by
    by_contra hcon
    exact hnot_bad ⟨hpq, hcon⟩
  linarith

/-- Window candidate set `U_win = {q ∈ V₀ : q ∉ N q ∧ φ q + 2 * w < ψ q}`. -/
noncomputable def windowSet (N : V → Finset V) (V₀ : Finset V) (φ ψ : V → ℝ) (w : ℝ) : Finset V :=
  oneSidedEnvelopeSet N V₀ φ ψ (2 * w)

/-- **Window Lemma, Zero-Far-Arc Case (`β = 0`).**
When `0 ≤ w` and every arc `p ∈ N q` inside `U_win` is a near arc (`|ψ p - φ q| ≤ w`), `U_win`
is strictly acyclic. -/
theorem window_isAcyclicIn_of_noFarArcs {N : V → Finset V} {V₀ : Finset V} {φ ψ : V → ℝ} {w : ℝ}
    (hw : 0 ≤ w)
    (hnear : ∀ q ∈ windowSet N V₀ φ ψ w,
      ∀ p ∈ N q, p ∈ windowSet N V₀ φ ψ w → |ψ p - φ q| ≤ w) :
    HalfRate.IsAcyclicIn N (windowSet N V₀ φ ψ w) := by
  refine oneSidedEnvelope_isAcyclicIn fun q hq p hpq hp => ?_
  have habs := (abs_le.mp (hnear q hq p hpq hp)).2
  linarith

/-- **Window Lemma with Bounded Far-Arc Degree `≤ β`.**
If `0 ≤ w` and every `q ∈ U_win` participates in at most `β` incoming+outgoing far arcs
(`¬ |ψ p - φ q| ≤ w`) inside `U_win`, then `U_win` contains an acyclic subset `S` of size at least
`U_win.card / (β + 1)` (`U_win.card ≤ (β + 1) * S.card`). -/
theorem exists_isAcyclicIn_of_window_maxDeg
    {N : V → Finset V} {V₀ : Finset V} {φ ψ : V → ℝ} {w : ℝ} {β : ℕ} (hw : 0 ≤ w)
    (hdeg : ∀ q ∈ windowSet N V₀ φ ψ w,
      (((windowSet N V₀ φ ψ w).erase q).filter fun p =>
        (p ∈ N q ∧ ¬ |ψ p - φ q| ≤ w) ∨ (q ∈ N p ∧ ¬ |ψ q - φ p| ≤ w)).card ≤ β) :
    ∃ S ⊆ windowSet N V₀ φ ψ w,
      HalfRate.IsAcyclicIn N S ∧ (windowSet N V₀ φ ψ w).card ≤ (β + 1) * S.card := by
  refine exists_isAcyclicIn_of_oneSidedEnvelope_maxDeg (w := 2 * w) fun q hq => ?_
  refine (card_le_card ?_).trans (hdeg q hq)
  intro p hp
  obtain ⟨hp_er, hbad⟩ := mem_filter.mp hp
  refine mem_filter.mpr ⟨hp_er, ?_⟩
  rcases hbad with ⟨hpq, hnle⟩ | ⟨hqp, hnle⟩
  · refine Or.inl ⟨hpq, fun habs => hnle ?_⟩
    have h2 := (abs_le.mp habs).2
    linarith
  · refine Or.inr ⟨hqp, fun habs => hnle ?_⟩
    have h2 := (abs_le.mp habs).2
    linarith

end OneSidedAndWindow

/-! ## §3. The Cut Lemma: Abstract & `coneSystem` Forms -/

section CutLemma

variable {V Γ α : Type*}

/-- **Cut-separated vertex set.**
`q ∈ cutSet V₀ A_cut E_cut f` iff `q ∈ V₀` and every backward cut point `x ∈ A_cut q` has strictly
smaller `f`-value than every forward cut point `y ∈ E_cut q` (`i.e. a(q) < e(q)` with convention
`max ∅ = -∞`, `min ∅ = +∞`). -/
abbrev cutSet [LinearOrder α] (V₀ : Finset V) (A_cut E_cut : V → Finset Γ) (f : Γ → α) : Finset V :=
  LeanMachine.BlockRanking.cutSet V₀ A_cut E_cut f

/-- `cutSet V₀ A_cut E_cut f` is a subset of `V₀`. -/
theorem cutSet_subset [LinearOrder α] {V₀ : Finset V} {A_cut E_cut : V → Finset Γ} {f : Γ → α} :
    cutSet V₀ A_cut E_cut f ⊆ V₀ :=
  LeanMachine.BlockRanking.cutSet_subset

/-- **Cut Lemma.**
Whenever every arc `p ∈ N q` inside `V₀` meets the cut (`(A_cut q ∩ E_cut p).Nonempty`),
`cutSet V₀ A_cut E_cut f` is strictly acyclic with zero self-loops. -/
theorem cutSet_isAcyclicIn [DecidableEq Γ] [LinearOrder α] {N : V → Finset V} {V₀ : Finset V}
    {A_cut E_cut : V → Finset Γ} {f : Γ → α}
    (hcut : ∀ q ∈ V₀, ∀ p ∈ V₀, p ∈ N q → (A_cut q ∩ E_cut p).Nonempty) :
    HalfRate.IsAcyclicIn N (cutSet V₀ A_cut E_cut f) := by
  intro T hTU hTne
  by_cases hemp : ∃ v ∈ T, A_cut v = ∅
  · obtain ⟨v, hvT, hAv⟩ := hemp
    refine ⟨v, hvT, fun u huv huT => ?_⟩
    have hv0 : v ∈ V₀ := (mem_filter.mp (hTU hvT)).1
    have hu0 : u ∈ V₀ := (mem_filter.mp (hTU huT)).1
    obtain ⟨s, hs⟩ := hcut v hv0 u hu0 huv
    rw [hAv, empty_inter] at hs
    exact notMem_empty s hs
  · push Not at hemp
    have hAne : ∀ w : {w // w ∈ T}, (A_cut w.1).Nonempty := fun w => hemp w.1 w.2
    let _ : DecidableEq α := Classical.decEq α
    let aVal : {w // w ∈ T} → α := fun w => ((A_cut w.1).image f).max' ((hAne w).image f)
    have hSubNe : (univ : Finset {w // w ∈ T}).Nonempty := by
      obtain ⟨v₀, hv₀⟩ := hTne
      exact ⟨⟨v₀, hv₀⟩, mem_univ _⟩
    obtain ⟨wMin, -, hwMin_eq⟩ :=
      mem_image.mp (((univ : Finset {w // w ∈ T}).image aVal).min'_mem (hSubNe.image aVal))
    refine ⟨wMin.1, wMin.2, fun u huv huT => ?_⟩
    have hv0 : wMin.1 ∈ V₀ := (mem_filter.mp (hTU wMin.2)).1
    have hu_cut := mem_filter.mp (hTU huT)
    obtain ⟨s, hs⟩ := hcut wMin.1 hv0 u hu_cut.1 huv
    obtain ⟨hsA, hsE⟩ := mem_inter.mp hs
    let uSub : {w // w ∈ T} := ⟨u, huT⟩
    obtain ⟨xMax, hxMaxA, hxMax_eq⟩ :=
      mem_image.mp (((A_cut u).image f).max'_mem ((hAne uSub).image f))
    have hlt_xs : f xMax < f s := hu_cut.2 xMax hxMaxA s hsE
    have hle_sw : f s ≤ aVal wMin :=
      ((A_cut wMin.1).image f).le_max' (f s) (mem_image_of_mem f hsA)
    have ha_lt : aVal uSub < aVal wMin := by
      dsimp [aVal]
      rw [← hxMax_eq]
      exact lt_of_lt_of_le hlt_xs hle_sw
    have ha_ge : ((univ : Finset {w // w ∈ T}).image aVal).min' (hSubNe.image aVal) ≤ aVal uSub :=
      ((univ : Finset {w // w ∈ T}).image aVal).min'_le (aVal uSub) (mem_image_of_mem aVal (mem_univ _))
    rw [← hwMin_eq] at ha_ge
    exact not_lt_of_ge ha_ge ha_lt

/-- **Splitting a `Γ_genie`-free `IsDepPath` at any visited step `s`.** -/
theorem depPath_split_at_mem {k : ℕ} {work : Fin k → ℕ → ℤ} {T : ℕ} {Γ_genie : Finset ℕ} :
    ∀ (ρ : List ℕ) (t₀ s : ℕ),
      IsDepPath work T (t₀ :: ρ) →
      LinNet.GFree Γ_genie (t₀ :: ρ) →
      s ∈ t₀ :: ρ →
      ∃ ρ₁ ρ₂ : List ℕ,
        IsDepPath work T (t₀ :: ρ₁) ∧ LinNet.GFree Γ_genie (t₀ :: ρ₁) ∧
        (t₀ :: ρ₁).getLastD t₀ = s ∧ ρ₁.length ≤ ρ.length ∧
        IsDepPath work T (s :: ρ₂) ∧ LinNet.GFree Γ_genie (s :: ρ₂) ∧
        (s :: ρ₂).getLastD s = (t₀ :: ρ).getLastD t₀ ∧ ρ₂.length ≤ ρ.length
  | [], t₀, s, hdep, hfree, hs => by
    simp only [List.mem_singleton] at hs
    subst hs
    exact ⟨[], [], hdep, hfree, rfl, le_rfl, trivial, hfree, rfl, le_rfl⟩
  | t₁ :: ρ', t₀, s, hdep, hfree, hs => by
    rcases List.mem_cons.mp hs with rfl | hs_tail
    · exact ⟨[], t₁ :: ρ', trivial, by simp [LinNet.GFree], rfl, Nat.zero_le _,
        hdep, hfree, rfl, le_rfl⟩
    · obtain ⟨hstep, hdep_tail⟩ := hdep
      have hfree_tail : LinNet.GFree Γ_genie (t₁ :: ρ') :=
        fun x hx => hfree x (List.mem_cons_of_mem t₁ hx)
      obtain ⟨ρ₁, ρ₂, hd1, hf1, hlast1, hlen1, hd2, hf2, hlast2, hlen2⟩ :=
        depPath_split_at_mem ρ' t₁ s hdep_tail hfree_tail hs_tail
      refine ⟨t₁ :: ρ₁, ρ₂, ⟨hstep, hd1⟩, ?_, ?_, Nat.succ_le_succ hlen1,
        hd2, hf2, ?_, hlen2.trans (Nat.le_succ _)⟩
      · intro x hx
        rcases List.mem_cons.mp hx with hxt | hx1
        · subst hxt
          exact hfree _ List.mem_cons_self
        · exact hf1 x hx1
      · rw [LinNet.getLastD_cons_cons, hlast1]
      · rw [LinNet.getLastD_cons_cons, hlast2]

end CutLemma

/-! ## §4. Random Block-Ranking Separation & Caro–Wei (Lemma 3.8) -/

section RandomBlockRanking

/-- **Random Block-Ranking Separation Theorem.**
Given `V₀ : Finset V` and block footprints `A_blk E_blk : V → Finset (Fin B)` satisfying the
cut-intersection property `∀ q ∈ V₀, ∀ p ∈ V₀, p ∈ N q → (A_blk q ∩ E_blk p).Nonempty`, let
`Q_star := V₀.filter (fun q => Disjoint (A_blk q) (E_blk q))`. Then there exists a block ranking
`σ : Equiv.Perm (Fin B)` such that `cutSet V₀ A_blk E_blk σ` is strictly acyclic in `N` and
`∑ q ∈ Q_star, 1 / C(|A_blk q| + |E_blk q|, |A_blk q|) ≤ (cutSet V₀ A_blk E_blk σ).card`. -/
theorem exists_isAcyclicIn_card_ge_of_blockCut {V : Type*} [DecidableEq V] {B : ℕ}
    {N : V → Finset V} {V₀ : Finset V} {A_blk E_blk : V → Finset (Fin B)}
    (hcut : ∀ q ∈ V₀, ∀ p ∈ V₀, p ∈ N q → (A_blk q ∩ E_blk p).Nonempty) :
    let Q_star := V₀.filter fun q => Disjoint (A_blk q) (E_blk q)
    ∃ σ : Equiv.Perm (Fin B),
      HalfRate.IsAcyclicIn N (cutSet V₀ A_blk E_blk σ) ∧
      cutSet V₀ A_blk E_blk σ ⊆ V₀ ∧
      (∑ q ∈ Q_star,
        (1 : ℝ) / (Nat.choose ((A_blk q).card + (E_blk q).card) (A_blk q).card : ℝ)) ≤
          ((cutSet V₀ A_blk E_blk σ).card : ℝ) := by
  intro Q_star
  obtain ⟨σ, hsum⟩ := LeanMachine.BlockRanking.exists_ranking_card_ge V₀ A_blk E_blk
  exact ⟨σ, cutSet_isAcyclicIn hcut, cutSet_subset, hsum⟩

theorem choose_add_mono {a₁ a₂ e₁ e₂ : ℕ} (ha : a₁ ≤ a₂) (he : e₁ ≤ e₂) :
    Nat.choose (a₁ + e₁) a₁ ≤ Nat.choose (a₂ + e₂) a₂ := LeanMachine.BlockRanking.choose_add_mono ha he

/-- **Uniform Block-Count Corollary ( Class `𝓗(m, K, λ)` core).**
If every `q ∈ Q_star` meets at most `a_max` entry blocks and `e_max` exit blocks, then some
block ranking `σ` yields an acyclic subset of size at least `|Q_star| / C(a_max + e_max, a_max)`. -/
theorem exists_isAcyclicIn_card_ge_of_uniformBlockCut {V : Type*} [DecidableEq V] {B a_max e_max : ℕ}
    {N : V → Finset V} {V₀ : Finset V} {A_blk E_blk : V → Finset (Fin B)}
    (hcut : ∀ q ∈ V₀, ∀ p ∈ V₀, p ∈ N q → (A_blk q ∩ E_blk p).Nonempty)
    (hbound : ∀ q ∈ V₀.filter (fun q => Disjoint (A_blk q) (E_blk q)),
      (A_blk q).card ≤ a_max ∧ (E_blk q).card ≤ e_max) :
    let Q_star := V₀.filter fun q => Disjoint (A_blk q) (E_blk q)
    ∃ σ : Equiv.Perm (Fin B),
      HalfRate.IsAcyclicIn N (cutSet V₀ A_blk E_blk σ) ∧
      cutSet V₀ A_blk E_blk σ ⊆ V₀ ∧
      (Q_star.card : ℝ) / (Nat.choose (a_max + e_max) a_max : ℝ) ≤
        ((cutSet V₀ A_blk E_blk σ).card : ℝ) := by
  intro Q_star
  obtain ⟨σ, hacyc, hsub, hsum⟩ := exists_isAcyclicIn_card_ge_of_blockCut hcut
  refine ⟨σ, hacyc, hsub, ?_⟩
  have hterm : ∀ q ∈ Q_star,
      (1 : ℝ) / (Nat.choose (a_max + e_max) a_max : ℝ) ≤
        (1 : ℝ) / (Nat.choose ((A_blk q).card + (E_blk q).card) (A_blk q).card : ℝ) := by
    intro q hq
    obtain ⟨ha, he⟩ := hbound q hq
    have hm := choose_add_mono ha he
    have hpos : (0 : ℝ) < (Nat.choose ((A_blk q).card + (E_blk q).card) (A_blk q).card : ℝ) := by
      exact_mod_cast Nat.choose_pos (Nat.le_add_right _ _)
    exact one_div_le_one_div_of_le hpos (by exact_mod_cast hm)
  have hconst : (Q_star.card : ℝ) / (Nat.choose (a_max + e_max) a_max : ℝ) =
      ∑ _q ∈ Q_star, (1 : ℝ) / (Nat.choose (a_max + e_max) a_max : ℝ) := by
    rw [sum_const, nsmul_eq_mul, mul_one_div]
  exact (hconst.le.trans (sum_le_sum hterm)).trans hsum

end RandomBlockRanking

/-! ## §5. CutCrux: Genie-Paid Separator Extension -/

section CutCrux

open scoped Classical

/-- **Anti-monotonicity of `HalfRate.IsAcyclicIn` in the relation.**
Any subset `U` that is acyclic in a super-relation `N₂` remains acyclic in every sub-relation `N₁`. -/
theorem isAcyclicIn_mono_rel {V : Type*} {N₁ N₂ : V → Finset V} {U : Finset V}
    (hsub : ∀ q ∈ U, N₁ q ⊆ N₂ q) (hA : HalfRate.IsAcyclicIn N₂ U) :
    HalfRate.IsAcyclicIn N₁ U := by
  intro T hTU hTne
  obtain ⟨v, hvT, hsrc⟩ := hA T hTU hTne
  exact ⟨v, hvT, fun u huv huT => hsrc u (hsub v (hTU hvT) huv) huT⟩

/-- **`MachineCutCruxAt M C D ρ δ`: per-machine cut-crux at depth `D`,
rate `ρ`, and extra genie separator bit-budget `δ`.** -/
def MachineCutCruxAt (M : TM) (C : ℝ) (D : ℕ) (ρ δ : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ T : ℕ,
    ObliviousOn M (inputsOfLength (d * d * entryBits d)) T →
    (T : ℝ) ≤ C * ((d * d * entryBits d : ℕ) + 1) →
    (appendList (traceAt M (d * d * entryBits d)) T).length = d * d * entryBits d →
    ∃ B : Finset ℕ,
      (valueWidth M : ℝ) * (B.card : ℝ) ≤ δ * (d * d * entryBits d : ℕ) ∧
      ∀ Γ : Finset ℕ,
        (∀ π, IsDepPath (traceAt M (d * d * entryBits d)).work T π →
          LinNet.GFree Γ π → π.length ≤ D + 1) →
        ∀ (m : ℕ) (E : (Fin (d * d * entryBits d) → Bool) → (Fin m → Bool)),
          IsIndexCode E (coneSystem (traceAt M (d * d * entryBits d)) T (Γ ∪ B) d (entryBits d))
            (tposOf d (entryBits d)) →
          (ρ - η) * (d * d * entryBits d : ℕ) ≤ m

/-- **`machine_cutcrux_excludes`: paying `δ * L` bits in the
genie for an extra separator `B` excludes oblivious linear-time transposers whenever `ε + δ < ρ`.** -/
theorem machine_cutcrux_excludes {M : TM} {C ε ρ δ : ℝ}
    (hC : 1 ≤ C) (hε : 0 < ε) (hεδρ : ε + δ < ρ)
    (h : MachineCutCruxAt M C (genieDepth M.k (valueWidth M) C ε) ρ δ) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ T : ℕ, ¬ ObliviousLinTime M d (entryBits d) C T := by
  obtain ⟨d₁, hd₁⟩ := h ((ρ - (ε + δ)) / 2) (by linarith)
  refine ⟨max d₁ 1, fun d hd T ⟨hobl, hT, htr⟩ => ?_⟩
  have hd1 : 1 ≤ d := (le_max_right _ _).trans hd
  have hL : 1 ≤ d * d * entryBits d := Nat.mul_pos (Nat.mul_pos hd1 hd1) (one_le_entryBits d)
  obtain ⟨hM, hlen⟩ := obliviousTransposer_of_transposes hobl htr (fun _ => false)
  obtain ⟨B, hBcost, hBcone⟩ := hd₁ d ((le_max_left _ _).trans hd) T hobl hT hlen
  have hβ1 : 1 ≤ valueWidth M := (two_le_valueWidth M).trans' (by omega)
  obtain ⟨Γ, hcost, hpath⟩ := genie_of_trace M
    (List.ofFn fun _ : Fin (d * d * entryBits d) => false) hβ1 hL hC hε hT
  obtain ⟨E, hE⟩ := exists_indexCode hM le_rfl (Γ ∪ B)
  have hbits := hBcone Γ (fun π h1 h2 => (hpath π h1 h2).trans (Nat.le_succ _)) _ E hE
  have hunion_nat : (Γ ∪ B).card ≤ Γ.card + B.card := card_union_le Γ B
  have hunion_r : ((Γ ∪ B).card : ℝ) ≤ (Γ.card : ℝ) + (B.card : ℝ) := by exact_mod_cast hunion_nat
  have hvw_nn : (0 : ℝ) ≤ (valueWidth M : ℝ) := by positivity
  have hcost_r : (valueWidth M : ℝ) * (Γ.card : ℝ) ≤ ε * (d * d * entryBits d : ℕ) := by
    simpa [Nat.cast_mul] using hcost
  have htot_cost : (valueWidth M : ℝ) * ((Γ ∪ B).card : ℝ) ≤
      (ε + δ) * (d * d * entryBits d : ℕ) := by
    calc (valueWidth M : ℝ) * ((Γ ∪ B).card : ℝ)
        ≤ (valueWidth M : ℝ) * ((Γ.card : ℝ) + (B.card : ℝ)) :=
          mul_le_mul_of_nonneg_left hunion_r hvw_nn
      _ = (valueWidth M : ℝ) * (Γ.card : ℝ) + (valueWidth M : ℝ) * (B.card : ℝ) := mul_add _ _ _
      _ ≤ ε * (d * d * entryBits d : ℕ) + δ * (d * d * entryBits d : ℕ) :=
          add_le_add hcost_r hBcost
      _ = (ε + δ) * (d * d * entryBits d : ℕ) := by ring
  have hL' : (1 : ℝ) ≤ (d * d * entryBits d : ℕ) := by exact_mod_cast hL
  have hbits_r : (ρ - (ρ - (ε + δ)) / 2) * (d * d * entryBits d : ℕ) ≤
      (valueWidth M : ℝ) * ((Γ ∪ B).card : ℝ) := by
    simpa [Nat.cast_mul] using hbits
  nlinarith

/-- **`B`-avoiding `D`-ball demand relation**:
`p ∈ ballAvoidSystem τ₀ T D B d b q` iff some `B`-free dependency path of length `≤ D + 1`
(`≤ D` hops) from `appendTime τ₀ T (tposOf d b q).1` ends at a read of `p`. -/
noncomputable def ballAvoidSystem {k : ℕ} (τ₀ : Trace k) (T D : ℕ) (B : Finset ℕ) (d b : ℕ)
    (q : Fin (d * d * b)) : Finset (Fin (d * d * b)) :=
  univ.filter fun p =>
    ∃ ρ : List ℕ, IsDepPath τ₀.work T (appendTime τ₀ T (tposOf d b q).1 :: ρ) ∧
      LinNet.GFree B (appendTime τ₀ T (tposOf d b q).1 :: ρ) ∧
      readPos τ₀ (d * d * b)
        ((appendTime τ₀ T (tposOf d b q).1 :: ρ).getLastD
          (appendTime τ₀ T (tposOf d b q).1)) = some p ∧
      ρ.length ≤ D

/-- Every cone relation `coneSystem τ₀ T (Γ ∪ B) d b (tposOf d b q)` with `Γ` valid at depth `D`
is contained in `ballAvoidSystem τ₀ T D B d b q`. -/
theorem coneSystem_subset_ballAvoidSystem {k T D d b : ℕ} (τ₀ : Trace k) (Γ B : Finset ℕ)
    (hpath : ∀ π, IsDepPath τ₀.work T π → LinNet.GFree Γ π → π.length ≤ D + 1)
    (q : Fin (d * d * b)) :
    coneSystem τ₀ T (Γ ∪ B) d b (tposOf d b q) ⊆ ballAvoidSystem τ₀ T D B d b q := by
  intro p hp
  simp only [coneSystem, depCone, mem_filter, mem_univ, true_and] at hp
  obtain ⟨ρ, hdep, hfree, hrd⟩ := hp
  have hfreeΓ : LinNet.GFree Γ (appendTime τ₀ T (tposOf d b q).1 :: ρ) :=
    fun v hv hvΓ => hfree v hv (mem_union_left B hvΓ)
  have hfreeB : LinNet.GFree B (appendTime τ₀ T (tposOf d b q).1 :: ρ) :=
    fun v hv hvB => hfree v hv (mem_union_right Γ hvB)
  have hlen : ρ.length ≤ D := by
    have h1 := hpath _ hdep hfreeΓ
    simp at h1; omega
  unfold ballAvoidSystem
  exact mem_filter.mpr ⟨mem_univ p, ρ, hdep, hfreeB, hrd, hlen⟩

/-- **`MachineCutCruxAt` from an acyclic subset of the `B`-avoiding `D`-ball relation.** -/
theorem machineCutCruxAt_of_ballAvoid_isAcyclicIn {M : TM} {C ρ δ : ℝ} {D : ℕ}
    (hacyc : ∀ η : ℝ, 0 < η → ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ T : ℕ,
      ObliviousOn M (inputsOfLength (d * d * entryBits d)) T →
      (T : ℝ) ≤ C * ((d * d * entryBits d : ℕ) + 1) →
      (appendList (traceAt M (d * d * entryBits d)) T).length = d * d * entryBits d →
      ∃ (B : Finset ℕ) (A : Finset (Fin (d * d * entryBits d))),
        (valueWidth M : ℝ) * (B.card : ℝ) ≤ δ * (d * d * entryBits d : ℕ) ∧
        HalfRate.IsAcyclicIn
          (ballAvoidSystem (traceAt M (d * d * entryBits d)) T D B d (entryBits d)) A ∧
        (ρ - η) * (d * d * entryBits d : ℕ) ≤ (A.card : ℝ)) :
    MachineCutCruxAt M C D ρ δ := by
  intro η hη
  obtain ⟨d₀, hd₀⟩ := hacyc η hη
  refine ⟨d₀, fun d hd T hobl hT hlen => ?_⟩
  obtain ⟨B, A, hBcost, hA_ball, hA_card⟩ := hd₀ d hd T hobl hT hlen
  refine ⟨B, hBcost, fun Γ hpath m E hE => ?_⟩
  have hA_cone : HalfRate.IsAcyclicIn
      (fun q => coneSystem (traceAt M (d * d * entryBits d)) T (Γ ∪ B) d (entryBits d)
        (tposOf d (entryBits d) q)) A :=
    isAcyclicIn_mono_rel
      (fun q _ => coneSystem_subset_ballAvoidSystem _ Γ B hpath q) hA_ball
  exact hA_card.trans (indexCode_bits_ge_of_isAcyclicIn hE hA_cone)

/-- Along any `B`-free `IsDepPath` `u₀ :: ρ` starting in `R_post`, if every single-step dependency
edge `IsDepPath work T [u, v]` out of `u ∈ R_post` lands in `R_post ∪ B`, then `(u₀ :: ρ).getLastD u₀`
belongs to `R_post`. -/
theorem depPath_getLastD_mem_of_closedPostRegion {k T : ℕ} {work : Fin k → ℕ → ℤ}
    {R_post B : Finset ℕ}
    (hclosed : ∀ u ∈ R_post, ∀ v : ℕ, IsDepPath work T [u, v] → v ∈ R_post ∨ v ∈ B) :
    ∀ (ρ : List ℕ) (u₀ : ℕ),
      u₀ ∈ R_post →
      IsDepPath work T (u₀ :: ρ) →
      LinNet.GFree B (u₀ :: ρ) →
      (u₀ :: ρ).getLastD u₀ ∈ R_post
  | [], u₀, hu₀, _, _ => hu₀
  | u₁ :: ρ', u₀, hu₀, hdep, hfree => by
    obtain ⟨hstep, hdep_tail⟩ := hdep
    have hu₁_notB : u₁ ∉ B := hfree u₁ List.mem_cons_self
    have hu₁_post : u₁ ∈ R_post :=
      (hclosed u₀ hu₀ u₁ ⟨hstep, trivial⟩).resolve_right hu₁_notB
    have hfree_tail : LinNet.GFree B (u₁ :: ρ') :=
      fun x hx => hfree x (List.mem_cons_of_mem u₁ hx)
    rw [LinNet.getLastD_cons_cons]
    exact depPath_getLastD_mem_of_closedPostRegion hclosed ρ' u₁ hu₁_post hdep_tail hfree_tail

/-- **Closed-Post-Region Criterion: Post-Bottleneck Isolation Criterion (`Mesoscopic Bottleneck Theorem`).**
If `R_post` contains all output steps of `V₀`, reads no message in `V₀`, and its outer `DepDag`
boundary is contained in `B`, then `ballAvoidSystem τ₀ T D B d b` has no arcs inside `V₀` and
`HalfRate.IsAcyclicIn (ballAvoidSystem τ₀ T D B d b) V₀` holds unconditionally at **every** `D`. -/
theorem isAcyclicIn_ballAvoidSystem_of_closedPostRegion {k T D d b : ℕ} (τ₀ : Trace k)
    (R_post B : Finset ℕ) (V₀ : Finset (Fin (d * d * b)))
    (hout : ∀ q ∈ V₀, appendTime τ₀ T (tposOf d b q).1 ∈ R_post)
    (hclosed : ∀ u ∈ R_post, ∀ v : ℕ, IsDepPath τ₀.work T [u, v] → v ∈ R_post ∨ v ∈ B)
    (hnoread : ∀ u ∈ R_post, ∀ p ∈ V₀, readPos τ₀ (d * d * b) u ≠ some p) :
    (∀ q ∈ V₀, ∀ p ∈ V₀, p ∉ ballAvoidSystem τ₀ T D B d b q) ∧
    HalfRate.IsAcyclicIn (ballAvoidSystem τ₀ T D B d b) V₀ := by
  have hdisj : ∀ q ∈ V₀, ∀ p ∈ V₀, p ∉ ballAvoidSystem τ₀ T D B d b q := by
    intro q hq p hp hp_mem
    unfold ballAvoidSystem at hp_mem
    obtain ⟨_, ρ, hdep, hfree, hrd, _⟩ := mem_filter.mp hp_mem
    have hlast := depPath_getLastD_mem_of_closedPostRegion hclosed ρ
      (appendTime τ₀ T (tposOf d b q).1) (hout q hq) hdep hfree
    exact hnoread _ hlast p hp hrd
  refine ⟨hdisj, acyclicIn_of_lt_on_nbhd (φ := fun _ => (0 : ℕ)) fun v hv u hu huV => ?_⟩
  exact absurd hu (hdisj v hv u huV)

end CutCrux

/-! ## §7. Absorbing-Sink & Step-Invariant Window Theorem (Lemma 3.9) -/

section StepInvariantWindow

open scoped Classical

/-- If `0 ≤ w` and every `N`-arc inside `V₀` is a near arc (`|ψ p - φ q| ≤ w`), then every
`q ∈ V₀` satisfying `φ q + 2 * w < ψ q` is automatically loop-free (`q ∉ N q`), so
`windowSet N V₀ φ ψ w` equals the pure arithmetic filter `V₀.filter (fun q => φ q + 2 * w < ψ q)`. -/
theorem windowSet_eq_filter_of_nearArcs {V : Type*} [DecidableEq V]
    {N : V → Finset V} {V₀ : Finset V}
    {φ ψ : V → ℝ} {w : ℝ} (hw : 0 ≤ w)
    (hnear : ∀ q ∈ V₀, ∀ p ∈ V₀, p ∈ N q → |ψ p - φ q| ≤ w) :
    windowSet N V₀ φ ψ w = V₀.filter fun q => φ q + 2 * w < ψ q := by
  ext q
  unfold windowSet oneSidedEnvelopeSet
  simp only [mem_filter]
  refine ⟨fun ⟨hq, _, hlt⟩ => ⟨hq, hlt⟩, fun ⟨hq, hlt⟩ => ⟨hq, fun hloop => ?_, hlt⟩⟩
  have habs := (abs_le.mp (hnear q hq q hq hloop)).2
  linarith

/-- **Pure-Filter Window Acyclicity Lemma**: if `0 ≤ w` and every `N`-arc inside `V₀` satisfies
`|ψ p - φ q| ≤ w`, then `V₀.filter (fun q => φ q + 2 * w < ψ q)` is strictly acyclic in `N`. -/
theorem isAcyclicIn_filter_of_nearArcs {V : Type*} [DecidableEq V]
    {N : V → Finset V} {V₀ : Finset V}
    {φ ψ : V → ℝ} {w : ℝ} (hw : 0 ≤ w)
    (hnear : ∀ q ∈ V₀, ∀ p ∈ V₀, p ∈ N q → |ψ p - φ q| ≤ w) :
    HalfRate.IsAcyclicIn N (V₀.filter fun q => φ q + 2 * w < ψ q) := by
  rw [← windowSet_eq_filter_of_nearArcs hw hnear]
  exact window_isAcyclicIn_of_noFarArcs hw fun q hq p hpq hp =>
    hnear q (mem_filter.mp hq).1 p (mem_filter.mp hp).1 hpq

/-- Set-based absorbing-sink persistence along any `B`-free `IsDepPath`. -/
theorem depPath_getLastD_mem_sink {k T : ℕ} {work : Fin k → ℕ → ℤ}
    {A_sink : Set ℕ} {B : Finset ℕ}
    (hsink : ∀ u ∈ A_sink, ∀ v : ℕ, IsDepPath work T [u, v] → v ∉ B → v ∈ A_sink) :
    ∀ (ρ : List ℕ) (u₀ : ℕ),
      u₀ ∈ A_sink →
      IsDepPath work T (u₀ :: ρ) →
      LinNet.GFree B (u₀ :: ρ) →
      (u₀ :: ρ).getLastD u₀ ∈ A_sink
  | [], u₀, hu₀, _, _ => hu₀
  | u₁ :: ρ', u₀, hu₀, hdep, hfree => by
    obtain ⟨hstep, hdep_tail⟩ := hdep
    have hu₁_notB : u₁ ∉ B := hfree u₁ List.mem_cons_self
    have hu₁_sink : u₁ ∈ A_sink := hsink u₀ hu₀ u₁ ⟨hstep, trivial⟩ hu₁_notB
    have hfree_tail : LinNet.GFree B (u₁ :: ρ') :=
      fun x hx => hfree x (List.mem_cons_of_mem u₁ hx)
    rw [LinNet.getLastD_cons_cons]
    exact depPath_getLastD_mem_sink hsink ρ' u₁ hu₁_sink hdep_tail hfree_tail

/-- **Hop-Budget-Indexed Step-Invariant & Absorbing-Sink Path Lemma.**
Starting at `u₀ ∈ R_act K` with hop budget `K`, if each `B`-free single-step edge out of
`R_act (r + 1)` (`r < K`) either enters the `B`-closed absorbing sink `A_sink` or lands in
`R_act r` shifting `μ` by at most `Δ`, then along any `B`-free `IsDepPath` `u₀ :: ρ` of length
`ρ.length ≤ K`, its endpoint either lies in `A_sink` or lies in `R_act (K - ρ.length)` with
`|μ u_last - μ u₀| ≤ (ρ.length : ℝ) * Δ`. -/
theorem depPath_stepInvariant_with_sink {k T : ℕ} {work : Fin k → ℕ → ℤ}
    {B : Finset ℕ} {R_act : ℕ → Set ℕ} {A_sink : Set ℕ} {μ : ℕ → ℝ} {Δ : ℝ}
    (hsink : ∀ u ∈ A_sink, ∀ v : ℕ, IsDepPath work T [u, v] → v ∉ B → v ∈ A_sink) :
    ∀ (ρ : List ℕ) (K : ℕ) (u₀ : ℕ),
      ρ.length ≤ K →
      u₀ ∈ R_act K →
      (∀ r < K, ∀ u ∈ R_act (r + 1), ∀ v : ℕ, IsDepPath work T [u, v] → v ∉ B →
        v ∈ A_sink ∨ (v ∈ R_act r ∧ |μ v - μ u| ≤ Δ)) →
      IsDepPath work T (u₀ :: ρ) →
      LinNet.GFree B (u₀ :: ρ) →
      (u₀ :: ρ).getLastD u₀ ∈ A_sink ∨
        ((u₀ :: ρ).getLastD u₀ ∈ R_act (K - ρ.length) ∧
          |μ ((u₀ :: ρ).getLastD u₀) - μ u₀| ≤ (ρ.length : ℝ) * Δ)
  | [], K, u₀, _, hu₀, _, _, _ => by
    refine Or.inr ⟨by simpa using hu₀, ?_⟩
    simp
  | u₁ :: ρ', 0, _, hlen, _, _, _, _ => by
    simp at hlen
  | u₁ :: ρ', K' + 1, u₀, hlen, hu₀, hstep, hdep, hfree => by
    obtain ⟨hstep0, hdep_tail⟩ := hdep
    have hu₁_notB : u₁ ∉ B := hfree u₁ List.mem_cons_self
    have hfree_tail : LinNet.GFree B (u₁ :: ρ') :=
      fun x hx => hfree x (List.mem_cons_of_mem u₁ hx)
    rw [LinNet.getLastD_cons_cons]
    rcases hstep K' (Nat.lt_succ_self K') u₀ hu₀ u₁ ⟨hstep0, trivial⟩ hu₁_notB with
      hu₁_sink | ⟨hu₁_act, hdrift0⟩
    · exact Or.inl (depPath_getLastD_mem_sink hsink ρ' u₁ hu₁_sink hdep_tail hfree_tail)
    · have hlen' : ρ'.length ≤ K' := by simp at hlen; omega
      have hstep' : ∀ r < K', ∀ u ∈ R_act (r + 1), ∀ v : ℕ, IsDepPath work T [u, v] → v ∉ B →
          v ∈ A_sink ∨ (v ∈ R_act r ∧ |μ v - μ u| ≤ Δ) :=
        fun r hr => hstep r (Nat.lt_succ_of_lt hr)
      rcases depPath_stepInvariant_with_sink hsink ρ' K' u₁ hlen' hu₁_act hstep' hdep_tail hfree_tail with
        hlast_sink | ⟨hlast_act, hdrift_tail⟩
      · exact Or.inl hlast_sink
      · refine Or.inr ⟨by simpa [Nat.succ_sub_succ_eq_sub] using hlast_act, ?_⟩
        have htri : |μ ((u₁ :: ρ').getLastD u₁) - μ u₀| ≤
            |μ ((u₁ :: ρ').getLastD u₁) - μ u₁| + |μ u₁ - μ u₀| := by
          simpa [sub_add_sub_cancel] using
            abs_add_le (μ ((u₁ :: ρ').getLastD u₁) - μ u₁) (μ u₁ - μ u₀)
        have hcast : (((u₁ :: ρ').length : ℕ) : ℝ) * Δ = (ρ'.length : ℝ) * Δ + Δ := by
          simp [List.length_cons, Nat.cast_add]; ring
        linarith

/-- **Shared Absorbing-Sink & Step-Invariant Near-Arc Bound on `ballAvoidSystem`**
(combinatorial core of Lemma 3.9). -/
theorem ballAvoidSystem_nearArcs_of_stepInvariant {k T D d b : ℕ} (τ₀ : Trace k)
    (B : Finset ℕ) (V₀ : Finset (Fin (d * d * b)))
    (R_act : ℕ → Set ℕ) (A_sink : Set ℕ) (μ : ℕ → ℝ)
    (φ ψ : Fin (d * d * b) → ℝ) {c₀ Δ c₁ : ℝ} (hΔ : 0 ≤ Δ)
    (hstart : ∀ q ∈ V₀, appendTime τ₀ T (tposOf d b q).1 ∈ R_act D ∧
      |μ (appendTime τ₀ T (tposOf d b q).1) - φ q| ≤ c₀)
    (hsink : ∀ u ∈ A_sink, ∀ v : ℕ, IsDepPath τ₀.work T [u, v] → v ∉ B → v ∈ A_sink)
    (hsink_noread : ∀ u ∈ A_sink, ∀ p ∈ V₀, readPos τ₀ (d * d * b) u ≠ some p)
    (hstep : ∀ r < D, ∀ u ∈ R_act (r + 1), ∀ v : ℕ, IsDepPath τ₀.work T [u, v] → v ∉ B →
      v ∈ A_sink ∨ (v ∈ R_act r ∧ |μ v - μ u| ≤ Δ))
    (hread : ∀ r ≤ D, ∀ u ∈ R_act r, ∀ p ∈ V₀,
      readPos τ₀ (d * d * b) u = some p → |ψ p - μ u| ≤ c₁) :
    ∀ q ∈ V₀, ∀ p ∈ V₀, p ∈ ballAvoidSystem τ₀ T D B d b q →
      |ψ p - φ q| ≤ c₀ + (D : ℝ) * Δ + c₁ := by
  intro q hq p hp hp_mem
  unfold ballAvoidSystem at hp_mem
  obtain ⟨_, ρ, hdep, hfree, hrd, hlen⟩ := mem_filter.mp hp_mem
  obtain ⟨hu₀_act, hstart_q⟩ := hstart q hq
  rcases depPath_stepInvariant_with_sink hsink ρ D (appendTime τ₀ T (tposOf d b q).1)
      hlen hu₀_act hstep hdep hfree with hlast_sink | ⟨hlast_act, hdrift⟩
  · exact absurd hrd (hsink_noread _ hlast_sink p hp)
  · have hread_p : |ψ p - μ ((appendTime τ₀ T (tposOf d b q).1 :: ρ).getLastD
        (appendTime τ₀ T (tposOf d b q).1))| ≤ c₁ :=
      hread (D - ρ.length) (Nat.sub_le D ρ.length) _ hlast_act p hp hrd
    have hlen_r : (ρ.length : ℝ) ≤ (D : ℝ) := by exact_mod_cast hlen
    have hdrift_D : |μ ((appendTime τ₀ T (tposOf d b q).1 :: ρ).getLastD
        (appendTime τ₀ T (tposOf d b q).1)) - μ (appendTime τ₀ T (tposOf d b q).1)| ≤
        (D : ℝ) * Δ :=
      hdrift.trans (mul_le_mul_of_nonneg_right hlen_r hΔ)
    let u₀ := appendTime τ₀ T (tposOf d b q).1
    let u_end := (u₀ :: ρ).getLastD u₀
    have htri1 : |ψ p - φ q| ≤ |ψ p - μ u_end| + |μ u_end - φ q| := by
      simpa [sub_add_sub_cancel] using abs_add_le (ψ p - μ u_end) (μ u_end - φ q)
    have htri2 : |μ u_end - φ q| ≤ |μ u_end - μ u₀| + |μ u₀ - φ q| := by
      simpa [sub_add_sub_cancel] using abs_add_le (μ u_end - μ u₀) (μ u₀ - φ q)
    linarith

/-- **Shared Absorbing-Sink & Step-Invariant Window Acyclicity Theorem**
(Lemma 3.9 common engine): under a hop-budget-indexed active
region `R_act` with absorbing sink `A_sink` and per-hop `μ`-drift `≤ Δ`, the pure arithmetic
window `{q ∈ V₀ : φ q + 2 * (c₀ + D * Δ + c₁) < ψ q}` equals `windowSet` and is strictly
acyclic in `ballAvoidSystem τ₀ T D B d b`. -/
theorem isAcyclicIn_ballAvoid_window_of_stepInvariant {k T D d b : ℕ} (τ₀ : Trace k)
    (B : Finset ℕ) (V₀ : Finset (Fin (d * d * b)))
    (R_act : ℕ → Set ℕ) (A_sink : Set ℕ) (μ : ℕ → ℝ)
    (φ ψ : Fin (d * d * b) → ℝ) {c₀ Δ c₁ : ℝ}
    (hc₀ : 0 ≤ c₀) (hΔ : 0 ≤ Δ) (hc₁ : 0 ≤ c₁)
    (hstart : ∀ q ∈ V₀, appendTime τ₀ T (tposOf d b q).1 ∈ R_act D ∧
      |μ (appendTime τ₀ T (tposOf d b q).1) - φ q| ≤ c₀)
    (hsink : ∀ u ∈ A_sink, ∀ v : ℕ, IsDepPath τ₀.work T [u, v] → v ∉ B → v ∈ A_sink)
    (hsink_noread : ∀ u ∈ A_sink, ∀ p ∈ V₀, readPos τ₀ (d * d * b) u ≠ some p)
    (hstep : ∀ r < D, ∀ u ∈ R_act (r + 1), ∀ v : ℕ, IsDepPath τ₀.work T [u, v] → v ∉ B →
      v ∈ A_sink ∨ (v ∈ R_act r ∧ |μ v - μ u| ≤ Δ))
    (hread : ∀ r ≤ D, ∀ u ∈ R_act r, ∀ p ∈ V₀,
      readPos τ₀ (d * d * b) u = some p → |ψ p - μ u| ≤ c₁) :
    windowSet (ballAvoidSystem τ₀ T D B d b) V₀ φ ψ (c₀ + (D : ℝ) * Δ + c₁) =
      (V₀.filter fun q => φ q + 2 * (c₀ + (D : ℝ) * Δ + c₁) < ψ q) ∧
    HalfRate.IsAcyclicIn (ballAvoidSystem τ₀ T D B d b)
      (V₀.filter fun q => φ q + 2 * (c₀ + (D : ℝ) * Δ + c₁) < ψ q) := by
  have hw : 0 ≤ c₀ + (D : ℝ) * Δ + c₁ := by positivity
  have hnear := ballAvoidSystem_nearArcs_of_stepInvariant τ₀ B V₀ R_act A_sink μ φ ψ hΔ
    hstart hsink hsink_noread hstep hread
  exact ⟨windowSet_eq_filter_of_nearArcs hw hnear, isAcyclicIn_filter_of_nearArcs hw hnear⟩

/-- **Hop-Independent Active-Region Specialization** (hop-budget-independent active region `R₀` for Lemma 3.9). -/
theorem isAcyclicIn_ballAvoid_window_of_constStepInvariant {k T D d b : ℕ} (τ₀ : Trace k)
    (B : Finset ℕ) (V₀ : Finset (Fin (d * d * b)))
    (R₀ A_sink : Set ℕ) (μ : ℕ → ℝ)
    (φ ψ : Fin (d * d * b) → ℝ) {c₀ Δ c₁ : ℝ}
    (hc₀ : 0 ≤ c₀) (hΔ : 0 ≤ Δ) (hc₁ : 0 ≤ c₁)
    (hstart : ∀ q ∈ V₀, appendTime τ₀ T (tposOf d b q).1 ∈ R₀ ∧
      |μ (appendTime τ₀ T (tposOf d b q).1) - φ q| ≤ c₀)
    (hsink : ∀ u ∈ A_sink, ∀ v : ℕ, IsDepPath τ₀.work T [u, v] → v ∉ B → v ∈ A_sink)
    (hsink_noread : ∀ u ∈ A_sink, ∀ p ∈ V₀, readPos τ₀ (d * d * b) u ≠ some p)
    (hstep : ∀ u ∈ R₀, ∀ v : ℕ, IsDepPath τ₀.work T [u, v] → v ∉ B →
      v ∈ A_sink ∨ (v ∈ R₀ ∧ |μ v - μ u| ≤ Δ))
    (hread : ∀ u ∈ R₀, ∀ p ∈ V₀, readPos τ₀ (d * d * b) u = some p → |ψ p - μ u| ≤ c₁) :
    HalfRate.IsAcyclicIn (ballAvoidSystem τ₀ T D B d b)
      (V₀.filter fun q => φ q + 2 * (c₀ + (D : ℝ) * Δ + c₁) < ψ q) :=
  (isAcyclicIn_ballAvoid_window_of_stepInvariant τ₀ B V₀ (fun _ => R₀) A_sink μ φ ψ hc₀ hΔ hc₁
    hstart hsink hsink_noread (fun _ _ => hstep) (fun _ _ => hread)).2

end StepInvariantWindow

/-! ## §8. Output-Subpopulation CutCrux, Universal Separator Lower Bound, & Path-Separator Transfer -/

section SubpopCutCrux

open scoped Classical

/-- **`SubpopCutCruxAt M C D α₀ ρ₀ δ₀`: output-subpopulation cut-crux at depth `D`,
subpopulation density `α₀`, subpopulation rate `ρ₀`, and subpopulation-relative separator budget `δ₀`.** -/
def SubpopCutCruxAt (M : TM) (C : ℝ) (D : ℕ) (α₀ ρ₀ δ₀ : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ T : ℕ,
    ObliviousOn M (inputsOfLength (d * d * entryBits d)) T →
    (T : ℝ) ≤ C * ((d * d * entryBits d : ℕ) + 1) →
    (appendList (traceAt M (d * d * entryBits d)) T).length = d * d * entryBits d →
    ∃ (V₀ : Finset (Fin (d * d * entryBits d))) (B : Finset ℕ),
      α₀ * (d * d * entryBits d : ℕ) ≤ (V₀.card : ℝ) ∧
      (valueWidth M : ℝ) * (B.card : ℝ) ≤ δ₀ * (V₀.card : ℝ) ∧
      ∀ Γ : Finset ℕ,
        (∀ π, IsDepPath (traceAt M (d * d * entryBits d)).work T π →
          LinNet.GFree Γ π → π.length ≤ D + 1) →
        ∀ (m : ℕ) (E : (Fin (d * d * entryBits d) → Bool) → (Fin m → Bool)),
          IsIndexCode E (coneSystem (traceAt M (d * d * entryBits d)) T (Γ ∪ B) d (entryBits d))
            (tposOf d (entryBits d)) →
          (ρ₀ - η) * (V₀.card : ℝ) ≤ m

/-- **`SubpopCutCrux M C α₀ ρ₀ δ₀`: depth-uniform output-subpopulation cut-crux.** -/
def SubpopCutCrux (M : TM) (C α₀ ρ₀ δ₀ : ℝ) : Prop :=
  ∀ D : ℕ, SubpopCutCruxAt M C D α₀ ρ₀ δ₀

/-- **`subpop_cutcrux_excludes`: an output-subpopulation cut-crux on `|V₀| ≥ α₀ L`
with subpopulation rate `ρ₀` and separator bit-cost `≤ δ₀ |V₀|` excludes oblivious linear-time
transposers whenever `0 < α₀` and `ε < α₀ * (ρ₀ - δ₀)`.** -/
theorem subpop_cutcrux_excludes {M : TM} {C ε α₀ ρ₀ δ₀ : ℝ}
    (hC : 1 ≤ C) (hε : 0 < ε) (hα₀ : 0 < α₀) (hgap : ε < α₀ * (ρ₀ - δ₀))
    (h : SubpopCutCruxAt M C (genieDepth M.k (valueWidth M) C ε) α₀ ρ₀ δ₀) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ T : ℕ, ¬ ObliviousLinTime M d (entryBits d) C T := by
  have hdiv_lt : ε / α₀ < ρ₀ - δ₀ := (div_lt_iff₀ hα₀).mpr (by linarith)
  let η : ℝ := (ρ₀ - δ₀ - ε / α₀) / 2
  have hη : 0 < η := by dsimp [η]; linarith
  obtain ⟨d₁, hd₁⟩ := h η hη
  refine ⟨max d₁ 1, fun d hd T ⟨hobl, hT, htr⟩ => ?_⟩
  have hd1 : 1 ≤ d := (le_max_right _ _).trans hd
  have hL : 1 ≤ d * d * entryBits d := Nat.mul_pos (Nat.mul_pos hd1 hd1) (one_le_entryBits d)
  obtain ⟨hM, hlen⟩ := obliviousTransposer_of_transposes hobl htr (fun _ => false)
  obtain ⟨V₀, B, hV₀_card, hBcost, hBcone⟩ := hd₁ d ((le_max_left _ _).trans hd) T hobl hT hlen
  have hβ1 : 1 ≤ valueWidth M := (two_le_valueWidth M).trans' (by omega)
  obtain ⟨Γ, hcost, hpath⟩ := genie_of_trace M
    (List.ofFn fun _ : Fin (d * d * entryBits d) => false) hβ1 hL hC hε hT
  obtain ⟨E, hE⟩ := exists_indexCode hM le_rfl (Γ ∪ B)
  have hbits := hBcone Γ (fun π h1 h2 => (hpath π h1 h2).trans (Nat.le_succ _)) _ E hE
  have hunion_nat : (Γ ∪ B).card ≤ Γ.card + B.card := card_union_le Γ B
  have hunion_r : ((Γ ∪ B).card : ℝ) ≤ (Γ.card : ℝ) + (B.card : ℝ) := by exact_mod_cast hunion_nat
  have hvw_nn : (0 : ℝ) ≤ (valueWidth M : ℝ) := by positivity
  have hcost_r : (valueWidth M : ℝ) * (Γ.card : ℝ) ≤ ε * (d * d * entryBits d : ℕ) := by
    simpa [Nat.cast_mul] using hcost
  have htot_cost : (valueWidth M : ℝ) * ((Γ ∪ B).card : ℝ) ≤
      ε * (d * d * entryBits d : ℕ) + δ₀ * (V₀.card : ℝ) := by
    calc (valueWidth M : ℝ) * ((Γ ∪ B).card : ℝ)
        ≤ (valueWidth M : ℝ) * ((Γ.card : ℝ) + (B.card : ℝ)) :=
          mul_le_mul_of_nonneg_left hunion_r hvw_nn
      _ = (valueWidth M : ℝ) * (Γ.card : ℝ) + (valueWidth M : ℝ) * (B.card : ℝ) := mul_add _ _ _
      _ ≤ ε * (d * d * entryBits d : ℕ) + δ₀ * (V₀.card : ℝ) :=
          add_le_add hcost_r hBcost
  have hbits_r : (ρ₀ - η) * (V₀.card : ℝ) ≤ (valueWidth M : ℝ) * ((Γ ∪ B).card : ℝ) := by
    simpa [Nat.cast_mul] using hbits
  have hsurplus_le : (ρ₀ - δ₀ - η) * (V₀.card : ℝ) ≤ ε * (d * d * entryBits d : ℕ) := by
    linarith
  have hdiv_pos : 0 < ε / α₀ := div_pos hε hα₀
  have hcoeff_pos : 0 < ρ₀ - δ₀ - η := by dsimp [η]; linarith
  have hsurplus_ge : (ρ₀ - δ₀ - η) * (α₀ * (d * d * entryBits d : ℕ)) ≤
      (ρ₀ - δ₀ - η) * (V₀.card : ℝ) :=
    mul_le_mul_of_nonneg_left hV₀_card hcoeff_pos.le
  have hL_pos : (0 : ℝ) < (d * d * entryBits d : ℕ) := by exact_mod_cast hL
  have hcoeff_gt : ε / α₀ < ρ₀ - δ₀ - η := by dsimp [η]; linarith
  have hmul_gt : (ε / α₀) * (α₀ * (d * d * entryBits d : ℕ)) <
      (ρ₀ - δ₀ - η) * (α₀ * (d * d * entryBits d : ℕ)) :=
    mul_lt_mul_of_pos_right hcoeff_gt (mul_pos hα₀ hL_pos)
  have hcancel : (ε / α₀) * (α₀ * (d * d * entryBits d : ℕ)) =
      ε * (d * d * entryBits d : ℕ) := by
    field_simp [hα₀.ne']
  linarith

/-- **Universal Finite-`d` Separator Lower Bound on Every Oblivious Linear-Time Transposer.**
Note the exact fixed-depth-`D` consequence of transposition used here: `obliviousTransposer_of_transposes`
plus `MergeDepth.exists_indexCode` at `D := genieDepth M.k (valueWidth M) C ε` (no depth-`∞` self-loop
is used). Consequently, for **every** step set `B : Finset ℕ` and **every** subset `U` acyclic in
`ballAvoidSystem (traceAt M L) T D B d (entryBits d)`, `valueWidth M * |B| ≥ |U| - ε L`. -/
theorem obliviousLinTime_separator_card_ge_of_isAcyclicIn {M : TM} {d T : ℕ} {C ε : ℝ}
    (hd : 1 ≤ d) (hC : 1 ≤ C) (hε : 0 < ε)
    (hobl_lt : ObliviousLinTime M d (entryBits d) C T)
    (B : Finset ℕ) (U : Finset (Fin (d * d * entryBits d)))
    (hU : HalfRate.IsAcyclicIn
      (ballAvoidSystem (traceAt M (d * d * entryBits d)) T
        (genieDepth M.k (valueWidth M) C ε) B d (entryBits d)) U) :
    (U.card : ℝ) - ε * ((d * d * entryBits d : ℕ) : ℝ) ≤
      (valueWidth M : ℝ) * (B.card : ℝ) := by
  obtain ⟨hobl, hT, htr⟩ := hobl_lt
  have hL : 1 ≤ d * d * entryBits d := Nat.mul_pos (Nat.mul_pos hd hd) (one_le_entryBits d)
  obtain ⟨hM, _⟩ := obliviousTransposer_of_transposes hobl htr (fun _ => false)
  have hβ1 : 1 ≤ valueWidth M := (two_le_valueWidth M).trans' (by omega)
  obtain ⟨Γ, hcost, hpath⟩ := genie_of_trace M
    (List.ofFn fun _ : Fin (d * d * entryBits d) => false) hβ1 hL hC hε hT
  obtain ⟨E, hE⟩ := exists_indexCode hM le_rfl (Γ ∪ B)
  have hU_cone : HalfRate.IsAcyclicIn
      (fun q => coneSystem (traceAt M (d * d * entryBits d)) T (Γ ∪ B) d (entryBits d)
        (tposOf d (entryBits d) q)) U :=
    isAcyclicIn_mono_rel
      (fun q _ => coneSystem_subset_ballAvoidSystem _ Γ B
        (fun π h1 h2 => (hpath π h1 h2).trans (Nat.le_succ _)) q) hU
  have hbits := indexCode_bits_ge_of_isAcyclicIn hE hU_cone
  have hunion_nat : (Γ ∪ B).card ≤ Γ.card + B.card := card_union_le Γ B
  have hunion_r : ((Γ ∪ B).card : ℝ) ≤ (Γ.card : ℝ) + (B.card : ℝ) := by exact_mod_cast hunion_nat
  have hvw_nn : (0 : ℝ) ≤ (valueWidth M : ℝ) := by positivity
  have hcost_r : (valueWidth M : ℝ) * (Γ.card : ℝ) ≤ ε * ((d * d * entryBits d : ℕ) : ℝ) := by
    simpa [Nat.cast_mul] using hcost
  have hbits_r : (U.card : ℝ) ≤ (valueWidth M : ℝ) * ((Γ ∪ B).card : ℝ) := by
    simpa [Nat.cast_mul] using hbits
  have htot : (valueWidth M : ℝ) * ((Γ ∪ B).card : ℝ) ≤
      ε * ((d * d * entryBits d : ℕ) : ℝ) + (valueWidth M : ℝ) * (B.card : ℝ) := by
    calc (valueWidth M : ℝ) * ((Γ ∪ B).card : ℝ)
        ≤ (valueWidth M : ℝ) * ((Γ.card : ℝ) + (B.card : ℝ)) :=
          mul_le_mul_of_nonneg_left hunion_r hvw_nn
      _ = (valueWidth M : ℝ) * (Γ.card : ℝ) + (valueWidth M : ℝ) * (B.card : ℝ) := mul_add _ _ _
      _ ≤ ε * ((d * d * entryBits d : ℕ) : ℝ) + (valueWidth M : ℝ) * (B.card : ℝ) :=
          add_le_add hcost_r le_rfl
  linarith

/-- **Intrinsic Depth-`D` Vertex-Path Separator Predicate:**
`B` `D`-separates the output roots of `V₀` from an intrinsic step set `S` on `τ₀` if every `B`-free
`IsDepPath` of `≤ D` hops starting from `appendTime τ₀ T (tposOf d b q).1` (`q ∈ V₀`) is also `S`-free
(`no step entered along `ρ` belongs to `S`, matching unit-capacity vertex-split Menger/Dinic cuts). -/
def IsBallPathSeparator {k : ℕ} (τ₀ : Trace k) (T D d b : ℕ)
    (V₀ : Finset (Fin (d * d * b))) (S B : Finset ℕ) : Prop :=
  ∀ q ∈ V₀, ∀ ρ : List ℕ,
    IsDepPath τ₀.work T (appendTime τ₀ T (tposOf d b q).1 :: ρ) →
    LinNet.GFree B (appendTime τ₀ T (tposOf d b q).1 :: ρ) →
    ρ.length ≤ D →
    LinNet.GFree S (appendTime τ₀ T (tposOf d b q).1 :: ρ)

/-- Whenever `B` `D`-separates `V₀` from `S`, every `B`-avoiding `D`-ball neighborhood of `q ∈ V₀`
is contained in the `S`-avoiding `D`-ball neighborhood of `q` (even when `|S| = Θ(L)` is arbitrarily large). -/
theorem ballAvoidSystem_subset_of_isBallPathSeparator {k T D d b : ℕ} (τ₀ : Trace k)
    {V₀ : Finset (Fin (d * d * b))} {S B : Finset ℕ}
    (hsep : IsBallPathSeparator τ₀ T D d b V₀ S B) :
    ∀ q ∈ V₀, ballAvoidSystem τ₀ T D B d b q ⊆ ballAvoidSystem τ₀ T D S d b q := by
  intro q hq p hp
  unfold ballAvoidSystem at hp ⊢
  obtain ⟨hp_univ, ρ, hdep, hfreeB, hrd, hlen⟩ := mem_filter.mp hp
  exact mem_filter.mpr ⟨hp_univ, ρ, hdep, hsep q hq ρ hdep hfreeB hlen, hrd, hlen⟩

/-- **Intrinsic Path-Separator Acyclicity Transfer:**
If deleting an intrinsic bad/non-LIFO step set `S` leaves `U ⊆ V₀` acyclic in
`ballAvoidSystem τ₀ T D S d b`, then **every** separator `B` satisfying
`IsBallPathSeparator τ₀ T D d b V₀ S B` also leaves `U` acyclic in `ballAvoidSystem τ₀ T D B d b`. -/
theorem isAcyclicIn_ballAvoid_of_isBallPathSeparator {k T D d b : ℕ} (τ₀ : Trace k)
    {V₀ U : Finset (Fin (d * d * b))} {S B : Finset ℕ}
    (hUV₀ : U ⊆ V₀)
    (hsep : IsBallPathSeparator τ₀ T D d b V₀ S B)
    (hacycS : HalfRate.IsAcyclicIn (ballAvoidSystem τ₀ T D S d b) U) :
    HalfRate.IsAcyclicIn (ballAvoidSystem τ₀ T D B d b) U :=
  isAcyclicIn_mono_rel
    (fun q hqU => ballAvoidSystem_subset_of_isBallPathSeparator τ₀ hsep q (hUV₀ hqU)) hacycS

/-- **Universal Intrinsic Vertex-Expansion Lower Bound:**
On any oblivious linear-time transposer `(M, d, C, T)`, if deleting an intrinsic trace step set `S`
yields an acyclic subset `U ⊆ V₀` in `ballAvoidSystem (traceAt M L) T D S d (entryBits d)` at
`D := genieDepth M.k (valueWidth M) C ε`, then **every** depth-`D` (and hence every depth-`∞` Dinic)
vertex separator `B` from `V₀` to `S` must satisfy `valueWidth M * |B| ≥ |U| - ε L`. -/
theorem obliviousLinTime_ballSeparator_card_ge {M : TM} {d T : ℕ} {C ε : ℝ}
    (hd : 1 ≤ d) (hC : 1 ≤ C) (hε : 0 < ε)
    (hobl_lt : ObliviousLinTime M d (entryBits d) C T)
    {V₀ U : Finset (Fin (d * d * entryBits d))} {S B : Finset ℕ}
    (hUV₀ : U ⊆ V₀)
    (hsep : IsBallPathSeparator (traceAt M (d * d * entryBits d)) T
      (genieDepth M.k (valueWidth M) C ε) d (entryBits d) V₀ S B)
    (hacycS : HalfRate.IsAcyclicIn
      (ballAvoidSystem (traceAt M (d * d * entryBits d)) T
        (genieDepth M.k (valueWidth M) C ε) S d (entryBits d)) U) :
    (U.card : ℝ) - ε * ((d * d * entryBits d : ℕ) : ℝ) ≤
      (valueWidth M : ℝ) * (B.card : ℝ) :=
  obliviousLinTime_separator_card_ge_of_isAcyclicIn hd hC hε hobl_lt B U
    (isAcyclicIn_ballAvoid_of_isBallPathSeparator _ hUV₀ hsep hacycS)

end SubpopCutCrux

/-! ## §9. Two-Sided Shift-Averaged Block-Cut & Kinematic Input-Row Locality -/

section MinimalLaminarAndKinematicCore

open scoped Classical

/-- **General `(a_max, e_max)` Shift-Averaged Uniform Block-Cut Theorem (Lemma 3.8 Shift-Averaged Core).**
Generalizes `exists_isAcyclicIn_of_shiftBlockCutFamily` from `(1, K_tot)` to arbitrary backward/forward
block multiplicities `(a_max, e_max)`, improving the binomial denominator to `Nat.choose (a_max + e_max) a_max`
(`= e_max + 1` at `a_max = 1`, `= a_max + 1` at `e_max = 1`, and `Ω(e_max^{-a_max})` in general). -/
theorem exists_isAcyclicIn_of_shiftBlockCutFamily_gen {V : Type*} [DecidableEq V]
    {M B a_max e_max S_strad C_coll : ℕ} (hM : 0 < M)
    {N : V → Finset V} {V₀ : Finset V}
    (A_blk E_blk : ℕ → V → Finset (Fin B))
    (hcut : ∀ ω ∈ range M, ∀ q ∈ V₀, ∀ p ∈ V₀, p ∈ N q → (A_blk ω q ∩ E_blk ω p).Nonempty)
    (hstrad : (∑ ω ∈ range M,
      (V₀.filter fun q => ¬ ((A_blk ω q).card ≤ a_max ∧ (E_blk ω q).card ≤ e_max)).card) ≤ S_strad)
    (hcoll : ∀ ω ∈ range M,
      (V₀.filter fun q => ¬ Disjoint (A_blk ω q) (E_blk ω q)).card ≤ C_coll) :
    ∃ ω₀ ∈ range M, ∃ U ⊆ V₀,
      HalfRate.IsAcyclicIn N U ∧
      ((V₀.card : ℝ) - (S_strad : ℝ) / (M : ℝ) - (C_coll : ℝ)) /
        (Nat.choose (a_max + e_max) a_max : ℝ) ≤ (U.card : ℝ) := by
  have hne : (range M).Nonempty := ⟨0, mem_range.mpr hM⟩
  obtain ⟨ω₀, hω₀, hmin⟩ := exists_min_image (range M)
    (fun ω => (V₀.filter fun q => ¬ ((A_blk ω q).card ≤ a_max ∧ (E_blk ω q).card ≤ e_max)).card) hne
  have hω_strad : M * (V₀.filter fun q =>
      ¬ ((A_blk ω₀ q).card ≤ a_max ∧ (E_blk ω₀ q).card ≤ e_max)).card ≤ S_strad := by
    calc M * (V₀.filter fun q => ¬ ((A_blk ω₀ q).card ≤ a_max ∧ (E_blk ω₀ q).card ≤ e_max)).card
        = ∑ _ω ∈ range M, (V₀.filter fun q =>
            ¬ ((A_blk ω₀ q).card ≤ a_max ∧ (E_blk ω₀ q).card ≤ e_max)).card := by
          rw [sum_const, card_range, smul_eq_mul]
      _ ≤ ∑ ω ∈ range M, (V₀.filter fun q =>
            ¬ ((A_blk ω q).card ≤ a_max ∧ (E_blk ω q).card ≤ e_max)).card :=
          sum_le_sum fun ω hω => hmin ω hω
      _ ≤ S_strad := hstrad
  let V₀' := V₀.filter fun q => (A_blk ω₀ q).card ≤ a_max ∧ (E_blk ω₀ q).card ≤ e_max
  have hcut' : ∀ q ∈ V₀', ∀ p ∈ V₀', p ∈ N q → (A_blk ω₀ q ∩ E_blk ω₀ p).Nonempty :=
    fun q hq p hp => hcut ω₀ hω₀ q (mem_filter.mp hq).1 p (mem_filter.mp hp).1
  have hbound' : ∀ q ∈ V₀'.filter (fun q => Disjoint (A_blk ω₀ q) (E_blk ω₀ q)),
      (A_blk ω₀ q).card ≤ a_max ∧ (E_blk ω₀ q).card ≤ e_max :=
    fun q hq => (mem_filter.mp (mem_filter.mp hq).1).2
  obtain ⟨σ, hacyc, hsub, hcard⟩ :=
    exists_isAcyclicIn_card_ge_of_uniformBlockCut hcut' hbound'
  refine ⟨ω₀, hω₀, cutSet V₀' (A_blk ω₀) (E_blk ω₀) σ,
    hsub.trans (filter_subset _ V₀), hacyc, ?_⟩
  let Q_star := V₀'.filter fun q => Disjoint (A_blk ω₀ q) (E_blk ω₀ q)
  let B_strad := V₀.filter fun q => ¬ ((A_blk ω₀ q).card ≤ a_max ∧ (E_blk ω₀ q).card ≤ e_max)
  let B_coll := V₀.filter fun q => ¬ Disjoint (A_blk ω₀ q) (E_blk ω₀ q)
  have hcov_V : V₀ ⊆ Q_star ∪ (B_strad ∪ B_coll) := by
    intro q hq
    by_cases hb : (A_blk ω₀ q).card ≤ a_max ∧ (E_blk ω₀ q).card ≤ e_max
    · by_cases hd : Disjoint (A_blk ω₀ q) (E_blk ω₀ q)
      · exact mem_union_left _ (mem_filter.mpr ⟨mem_filter.mpr ⟨hq, hb⟩, hd⟩)
      · exact mem_union_right _ (mem_union_right _ (mem_filter.mpr ⟨hq, hd⟩))
    · exact mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨hq, hb⟩))
  have hV_le : V₀.card ≤ Q_star.card + B_strad.card + B_coll.card := by
    calc V₀.card
        ≤ (Q_star ∪ (B_strad ∪ B_coll)).card := card_le_card hcov_V
      _ ≤ Q_star.card + (B_strad ∪ B_coll).card := card_union_le _ _
      _ ≤ Q_star.card + (B_strad.card + B_coll.card) := Nat.add_le_add_left (card_union_le _ _) _
      _ = Q_star.card + B_strad.card + B_coll.card := by omega
  have hB_coll_le : B_coll.card ≤ C_coll := hcoll ω₀ hω₀
  have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hchoose_pos : (0 : ℝ) < (Nat.choose (a_max + e_max) a_max : ℝ) := by
    exact_mod_cast Nat.choose_pos (Nat.le_add_right a_max e_max)
  have hstrad_r : (B_strad.card : ℝ) ≤ (S_strad : ℝ) / (M : ℝ) := by
    rw [le_div_iff₀ hM_pos]
    have hc : ((M * B_strad.card : ℕ) : ℝ) ≤ (S_strad : ℝ) := by exact_mod_cast hω_strad
    rw [Nat.cast_mul] at hc
    linarith
  have hV_r : (V₀.card : ℝ) ≤ (Q_star.card : ℝ) + (B_strad.card : ℝ) + (B_coll.card : ℝ) := by
    exact_mod_cast hV_le
  have hcoll_r : (B_coll.card : ℝ) ≤ (C_coll : ℝ) := by exact_mod_cast hB_coll_le
  have hnum_le : (V₀.card : ℝ) - (S_strad : ℝ) / (M : ℝ) - (C_coll : ℝ) ≤ (Q_star.card : ℝ) := by
    linarith
  exact (div_le_div_of_nonneg_right hnum_le hchoose_pos.le).trans hcard

/-- Steps `t < T` at which the input walk `x_in` visits raw input row `i` (`[i W, (i + 1) W)`). -/
def inputRowReads (x_in : ℕ → ℤ) (T W : ℕ) {d : ℕ} (i : Fin d) : Finset ℕ :=
  (range T).filter fun t =>
    ((i.1 : ℤ) * (W : ℤ)) ≤ x_in t ∧ x_in t < (((i.1 : ℤ) + 1) * (W : ℤ))

/-- Steps `t < T` at which `x_in` lies in the `3 W`-buffered band `[(i - 1) W, (i + 2) W)` around row `i`. -/
def inputRowBuf (x_in : ℕ → ℤ) (T W : ℕ) {d : ℕ} (i : Fin d) : Finset ℕ :=
  (range T).filter fun t =>
    (((i.1 : ℤ) - 1) * (W : ℤ)) ≤ x_in t ∧ x_in t < (((i.1 : ℤ) + 2) * (W : ℤ))

/-- Every time step `t < T` belongs to at most `3` buffered row bands `[(i - 1) W, (i + 2) W)` (`W ≥ 1`),
so the total buffered-band residency across all `d` raw rows is at most `3 * T`. -/
theorem sum_card_inputRowBuf_le_three_mul (x_in : ℕ → ℤ) (T W d : ℕ) (hW : 1 ≤ W) :
    (∑ i : Fin d, (inputRowBuf x_in T W i).card) ≤ 3 * T := by
  have hWz : (0 : ℤ) < (W : ℤ) := by exact_mod_cast hW
  have hpt : ∀ t : ℕ,
      ((univ : Finset (Fin d)).filter fun i =>
        (((i.1 : ℤ) - 1) * (W : ℤ)) ≤ x_in t ∧ x_in t < (((i.1 : ℤ) + 2) * (W : ℤ))).card ≤ 3 := by
    intro t
    set S_t := (univ : Finset (Fin d)).filter fun i =>
      (((i.1 : ℤ) - 1) * (W : ℤ)) ≤ x_in t ∧ x_in t < (((i.1 : ℤ) + 2) * (W : ℤ))
    rcases S_t.eq_empty_or_nonempty with hemp | hne
    · rw [hemp, card_empty]; omega
    · let i₀ := S_t.min' hne
      let i₁ := S_t.max' hne
      have hi₀_mem := (mem_filter.mp (S_t.min'_mem hne)).2
      have hi₁_mem := (mem_filter.mp (S_t.max'_mem hne)).2
      have hspan_z : ((i₁.1 : ℤ) - 1) * (W : ℤ) < ((i₀.1 : ℤ) + 2) * (W : ℤ) :=
        lt_of_le_of_lt hi₁_mem.1 hi₀_mem.2
      have hi₁_le : i₁.1 ≤ i₀.1 + 2 := by nlinarith
      have hsub : S_t.image Fin.val ⊆ Icc i₀.1 (i₀.1 + 2) := by
        intro v hv
        obtain ⟨i, hiS, rfl⟩ := mem_image.mp hv
        have h1 : i₀.1 ≤ i.1 := S_t.min'_le i hiS
        have h2 : i.1 ≤ i₁.1 := S_t.le_max' i hiS
        exact mem_Icc.mpr ⟨h1, h2.trans hi₁_le⟩
      calc S_t.card
          = (S_t.image Fin.val).card := (card_image_of_injective S_t Fin.val_injective).symm
        _ ≤ (Icc i₀.1 (i₀.1 + 2)).card := card_le_card hsub
        _ = 3 := by simp [Nat.card_Icc]; omega
  have hswap : (∑ i : Fin d, (inputRowBuf x_in T W i).card) =
      ∑ t ∈ range T, ((univ : Finset (Fin d)).filter fun i =>
        (((i.1 : ℤ) - 1) * (W : ℤ)) ≤ x_in t ∧ x_in t < (((i.1 : ℤ) + 2) * (W : ℤ))).card := by
    simp only [inputRowBuf, card_filter]
    exact sum_comm
  rw [hswap]
  calc (∑ t ∈ range T, ((univ : Finset (Fin d)).filter fun i =>
          (((i.1 : ℤ) - 1) * (W : ℤ)) ≤ x_in t ∧ x_in t < (((i.1 : ℤ) + 2) * (W : ℤ))).card)
      ≤ ∑ _t ∈ range T, 3 := sum_le_sum fun t _ => hpt t
    _ = 3 * T := by rw [sum_const, card_range, smul_eq_mul, mul_comm]

/-- Left endpoints of maximal contiguous runs of `inputRowBuf x_in T W i` that actually visit
raw input row `i` (`inputRowReads x_in T W i`). -/
def inputRowTouchRuns (x_in : ℕ → ℤ) (T W : ℕ) {d : ℕ} (i : Fin d) : Finset ℕ :=
  (runStarts (inputRowBuf x_in T W i)).filter fun a =>
    (Ico a (runEnd (inputRowBuf x_in T W i) T a) ∩ inputRowReads x_in T W i).Nonempty

/-- Every read of raw input row `i` lies in one of the pairwise-disjoint buffered runs indexed by
`inputRowTouchRuns x_in T W i`. -/
theorem inputRowReads_subset_touchRuns_biUnion (x_in : ℕ → ℤ) (T W : ℕ) {d : ℕ} (hW : 1 ≤ W)
    (i : Fin d) :
    inputRowReads x_in T W i ⊆
      (inputRowTouchRuns x_in T W i).biUnion (fun a => Ico a (runEnd (inputRowBuf x_in T W i) T a)) := by
  have hWz : (0 : ℤ) < (W : ℤ) := by exact_mod_cast hW
  have hBT : ∀ t ∈ inputRowBuf x_in T W i, t < T := fun t ht => mem_range.mp (mem_filter.mp ht).1
  intro t htR
  obtain ⟨ht_range, hlo, hhi⟩ := mem_filter.mp htR
  have htB : t ∈ inputRowBuf x_in T W i := mem_filter.mpr ⟨ht_range, by nlinarith, by nlinarith⟩
  have hcov := eq_biUnion_runInterval hBT
  rw [hcov] at htB
  obtain ⟨a, ha_start, ht_ico⟩ := mem_biUnion.mp htB
  refine mem_biUnion.mpr ⟨a, mem_filter.mpr ⟨ha_start, ⟨t, mem_inter.mpr ⟨ht_ico, htR⟩⟩⟩, ht_ico⟩

/-- **Unit-Speed Touching-Run Bound (the touching-run bound Core):**
Because a unit-speed walk `x_in` (`IsWalk x_in`) must travel at least `W` cells from raw row `i`
to exit `[(i - 1) W, (i + 2) W)` before `T`, every touching run ending strictly before `T` has
duration `≥ W + 1`, so `inputRowTouchRuns x_in T W i` has at most `|inputRowBuf| / W + 1` runs
and total run duration at most `|inputRowBuf|`. -/
theorem card_inputRowTouchRuns_le {x_in : ℕ → ℤ} (hx_in : IsWalk x_in) (T W : ℕ) {d : ℕ}
    (hW : 1 ≤ W) (i : Fin d) :
    (inputRowTouchRuns x_in T W i).card ≤ (inputRowBuf x_in T W i).card / W + 1 ∧
    (∑ a ∈ inputRowTouchRuns x_in T W i,
      (runEnd (inputRowBuf x_in T W i) T a - a)) ≤ (inputRowBuf x_in T W i).card := by
  set B_i := inputRowBuf x_in T W i
  set R_i := inputRowReads x_in T W i
  set Touch := inputRowTouchRuns x_in T W i
  have hBT : ∀ t ∈ B_i, t < T := fun t ht => mem_range.mp (mem_filter.mp ht).1
  have hTouch_sub : Touch ⊆ runStarts B_i := filter_subset _ _
  have hdisj : (Touch : Set ℕ).PairwiseDisjoint (fun a => Ico a (runEnd B_i T a)) :=
    fun a₁ ha₁ a₂ ha₂ hne =>
      pairwiseDisjoint_runInterval hBT (coe_subset.mpr hTouch_sub ha₁)
        (coe_subset.mpr hTouch_sub ha₂) hne
  have hbiU_sub : Touch.biUnion (fun a => Ico a (runEnd B_i T a)) ⊆ B_i := by
    intro t ht
    obtain ⟨a, haT, ht_ico⟩ := mem_biUnion.mp ht
    exact (runEnd_spec hBT (hTouch_sub haT)).2.2.2 t ht_ico
  have hsum_len : (∑ a ∈ Touch, (runEnd B_i T a - a)) ≤ B_i.card := by
    calc (∑ a ∈ Touch, (runEnd B_i T a - a))
        = ∑ a ∈ Touch, (Ico a (runEnd B_i T a)).card := by
          refine sum_congr rfl fun a _ => ?_
          simp [Nat.card_Ico]
      _ = (Touch.biUnion (fun a => Ico a (runEnd B_i T a))).card := (card_biUnion hdisj).symm
      _ ≤ B_i.card := card_le_card hbiU_sub
  refine ⟨?_, hsum_len⟩
  let IntRuns := Touch.filter fun a => runEnd B_i T a < T
  let EndRuns := Touch.filter fun a => ¬ runEnd B_i T a < T
  have hpart : Touch = IntRuns ∪ EndRuns := by
    ext a
    simp only [IntRuns, EndRuns, mem_union, mem_filter]
    tauto
  have hInt_len : ∀ a ∈ IntRuns, W ≤ runEnd B_i T a - a := by
    intro a haI
    obtain ⟨haT, hlt_T⟩ := mem_filter.mp haI
    obtain ⟨ha_start, hne_inter⟩ := mem_filter.mp haT
    obtain ⟨t₀, ht₀_mem⟩ := hne_inter
    obtain ⟨ht₀_ico, ht₀_R⟩ := mem_inter.mp ht₀_mem
    obtain ⟨hat₀, ht₀_end⟩ := mem_Ico.mp ht₀_ico
    obtain ⟨_, hxt₀_lo, hxt₀_hi⟩ := mem_filter.mp ht₀_R
    have hspec := runEnd_spec hBT ha_start
    have hend_notB : runEnd B_i T a ∉ B_i := hspec.2.2.1
    have hend_out : ¬ ((((i.1 : ℤ) - 1) * (W : ℤ)) ≤ x_in (runEnd B_i T a) ∧
        x_in (runEnd B_i T a) < (((i.1 : ℤ) + 2) * (W : ℤ))) :=
      fun h => hend_notB (mem_filter.mpr ⟨mem_range.mpr hlt_T, h⟩)
    have hlip := hx_in.lip (le_of_lt ht₀_end)
    have hWz : (1 : ℤ) ≤ (W : ℤ) := by exact_mod_cast hW
    have hdiff_ge : (W : ℤ) ≤ ((runEnd B_i T a - t₀ : ℕ) : ℤ) := by
      by_cases hleft : (((i.1 : ℤ) - 1) * (W : ℤ)) ≤ x_in (runEnd B_i T a)
      · have hright : (((i.1 : ℤ) + 2) * (W : ℤ)) ≤ x_in (runEnd B_i T a) := by
          simp only [not_and, not_lt] at hend_out
          exact hend_out hleft
        have hstep_gap : (W : ℤ) + 1 ≤ x_in (runEnd B_i T a) - x_in t₀ := by nlinarith
        linarith [hlip.2]
      · push Not at hleft
        have hstep_gap : (W : ℤ) + 1 ≤ x_in t₀ - x_in (runEnd B_i T a) := by nlinarith
        linarith [hlip.1]
    have hnat_ge : W ≤ runEnd B_i T a - t₀ := by exact_mod_cast hdiff_ge
    omega
  have hInt_mul : IntRuns.card * W ≤ B_i.card := by
    calc IntRuns.card * W
        = ∑ _a ∈ IntRuns, W := by rw [sum_const, smul_eq_mul]
      _ ≤ ∑ a ∈ IntRuns, (runEnd B_i T a - a) := sum_le_sum hInt_len
      _ ≤ ∑ a ∈ Touch, (runEnd B_i T a - a) :=
          sum_le_sum_of_subset (filter_subset _ Touch)
      _ ≤ B_i.card := hsum_len
  have hInt_div : IntRuns.card ≤ B_i.card / W :=
    (Nat.le_div_iff_mul_le (by omega : 0 < W)).mpr hInt_mul
  have hEnd_le_one : EndRuns.card ≤ 1 := by
    refine card_le_one.mpr fun a₁ ha₁ a₂ ha₂ => ?_
    obtain ⟨ha₁T, hnlt₁⟩ := mem_filter.mp ha₁
    obtain ⟨ha₂T, hnlt₂⟩ := mem_filter.mp ha₂
    have hspec₁ := runEnd_spec hBT (hTouch_sub ha₁T)
    have hspec₂ := runEnd_spec hBT (hTouch_sub ha₂T)
    have heq₁ : runEnd B_i T a₁ = T := by omega
    have heq₂ : runEnd B_i T a₂ = T := by omega
    have hT_pos : 0 < T := by omega
    by_contra hne
    have hdisj12 := hdisj (mem_coe.mpr ha₁T) (mem_coe.mpr ha₂T) hne
    have hm1 : T - 1 ∈ Ico a₁ (runEnd B_i T a₁) := mem_Ico.mpr ⟨by omega, by omega⟩
    have hm2 : T - 1 ∈ Ico a₂ (runEnd B_i T a₂) := mem_Ico.mpr ⟨by omega, by omega⟩
    exact disjoint_left.mp hdisj12 hm1 hm2
  calc Touch.card
      = (IntRuns ∪ EndRuns).card := by rw [← hpart]
    _ ≤ IntRuns.card + EndRuns.card := card_union_le _ _
    _ ≤ B_i.card / W + 1 := Nat.add_le_add hInt_div hEnd_le_one

/-- **Kinematic Input-Row Locality Theorem:**
For **every** unit-speed input walk `x_in` (`IsWalk x_in`), row width `W ≥ 1`, horizon `T`, and
run-budget `K_row ≥ 1`, at least `d - (3 * T) / (K_row * W)` raw input rows `i : Fin d` have
**all** their visits during `[0, T)` covered by at most `K_row` pairwise-disjoint contiguous time
intervals `[a, runEnd ... a)` of total duration strictly less than `K_row * W`. -/
theorem kinematic_goodInputRows_card_ge {x_in : ℕ → ℤ} (hx_in : IsWalk x_in)
    (T W d K_row : ℕ) (hW : 1 ≤ W) (hK : 1 ≤ K_row) :
    let GoodRows := (univ : Finset (Fin d)).filter fun i =>
      (inputRowTouchRuns x_in T W i).card ≤ K_row ∧
      (∑ a ∈ inputRowTouchRuns x_in T W i,
        (runEnd (inputRowBuf x_in T W i) T a - a)) < K_row * W
    d - (3 * T) / (K_row * W) ≤ GoodRows.card := by
  intro GoodRows
  let LightRows := (univ : Finset (Fin d)).filter fun i =>
    (inputRowBuf x_in T W i).card < K_row * W
  let HeavyRows := (univ : Finset (Fin d)).filter fun i =>
    K_row * W ≤ (inputRowBuf x_in T W i).card
  have hHeavy_mul : HeavyRows.card * (K_row * W) ≤ 3 * T := by
    calc HeavyRows.card * (K_row * W)
        = ∑ _i ∈ HeavyRows, (K_row * W) := by rw [sum_const, smul_eq_mul]
      _ ≤ ∑ i ∈ HeavyRows, (inputRowBuf x_in T W i).card :=
          sum_le_sum fun i hi => (mem_filter.mp hi).2
      _ ≤ ∑ i : Fin d, (inputRowBuf x_in T W i).card :=
          sum_le_sum_of_subset (subset_univ HeavyRows)
      _ ≤ 3 * T := sum_card_inputRowBuf_le_three_mul x_in T W d hW
  have hKW_pos : 0 < K_row * W := Nat.mul_pos hK hW
  have hHeavy_le : HeavyRows.card ≤ (3 * T) / (K_row * W) :=
    (Nat.le_div_iff_mul_le hKW_pos).mpr hHeavy_mul
  have hcov : (univ : Finset (Fin d)) ⊆ LightRows ∪ HeavyRows := by
    intro i _
    rcases lt_or_ge (inputRowBuf x_in T W i).card (K_row * W) with hlt | hge
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ i, hlt⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ i, hge⟩)
  have hd_le : d ≤ LightRows.card + HeavyRows.card := by
    calc d = (univ : Finset (Fin d)).card := (Fintype.card_fin d).symm
      _ ≤ (LightRows ∪ HeavyRows).card := card_le_card hcov
      _ ≤ LightRows.card + HeavyRows.card := card_union_le _ _
  have hLight_sub : LightRows ⊆ GoodRows := by
    intro i hiL
    have hlt : (inputRowBuf x_in T W i).card < K_row * W := (mem_filter.mp hiL).2
    obtain ⟨hcard_runs, hsum_runs⟩ := card_inputRowTouchRuns_le hx_in T W hW i
    have hdiv_lt : (inputRowBuf x_in T W i).card / W < K_row :=
      Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hlt)
    exact mem_filter.mpr ⟨mem_univ i, by omega, lt_of_le_of_lt hsum_runs hlt⟩
  have hLight_le : LightRows.card ≤ GoodRows.card := card_le_card hLight_sub
  omega

end MinimalLaminarAndKinematicCore

/-! ## §10. Intrinsic Non-Crossing Cut Antitonicity & `Mix_η` Bridge Spine -/

section NonCrossingCut

open scoped Classical

/-- **Cell-Interface Uniqueness Across Any Chronological Cut:**
On *any* walk `y : ℕ → ℤ` (with arbitrary owner load and arbitrary crossings), at most one `IsHop`
can cross a timestamp `t_cut` (`b < t_cut ≤ a`) at any given tape cell `z = y a`: both its lower
endpoint `b < t_cut` and upper endpoint `a ≥ t_cut` are uniquely determined by `(t_cut, y a)`. -/
theorem hop_crossingCut_unique {y : ℕ → ℤ} {T t_cut b₁ a₁ b₂ a₂ : ℕ}
    (h₁ : IsHop y T b₁ a₁) (h₂ : IsHop y T b₂ a₂)
    (hb₁ : b₁ < t_cut) (ha₁ : t_cut ≤ a₁) (hb₂ : b₂ < t_cut) (ha₂ : t_cut ≤ a₂)
    (hy : y a₁ = y a₂) :
    b₁ = b₂ ∧ a₁ = a₂ := by
  have hyb₁ : y a₁ = y b₁ := h₁.2.2.1
  have hyb₂ : y a₂ = y b₂ := h₂.2.2.1
  have hb_eq : b₁ = b₂ := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact h₁.2.2.2 b₂ (mem_Ioo.mpr ⟨hlt, lt_of_lt_of_le hb₂ ha₁⟩) (by omega)
    · exact h₂.2.2.2 b₁ (mem_Ioo.mpr ⟨hgt, lt_of_lt_of_le hb₁ ha₂⟩) (by omega)
  refine ⟨hb_eq, ?_⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact h₂.2.2.2 a₁ (mem_Ioo.mpr ⟨lt_of_lt_of_le hb₂ ha₁, hlt⟩) (by omega)
  · exact h₁.2.2.2 a₂ (mem_Ioo.mpr ⟨lt_of_lt_of_le hb₁ ha₂, hgt⟩) (by omega)

/-- Two interval pairs `(b₁, a₁)` and `(b₂, a₂)` *cross* (are not nested and not disjoint) iff
`b₁ < b₂ < a₁ < a₂` or `b₂ < b₁ < a₂ < a₁`. -/
def HopsCross (b₁ a₁ b₂ a₂ : ℕ) : Prop :=
  (b₁ < b₂ ∧ b₂ < a₁ ∧ a₁ < a₂) ∨ (b₂ < b₁ ∧ b₁ < a₂ ∧ a₂ < a₁)

/-- **Topological Antitonicity of Non-Crossing Hops Across a Cut:**
Any two `IsHop`s `(b₁, a₁)` and `(b₂, a₂)` crossing `t_cut` (`bᵢ < t_cut ≤ aᵢ`) that do not cross
each other (`¬ HopsCross b₁ a₁ b₂ a₂`) are **strictly antitone** (`a₁ < a₂ → b₂ < b₁`) and visit
**distinct** tape cells (`y a₁ ≠ y a₂`). Thus all non-crossing hops across `t_cut` on a single tape
form a single strictly nested 1-to-1 LIFO chain! -/
theorem crossingCut_nonCrossing_strictAnti {y : ℕ → ℤ} {T t_cut b₁ a₁ b₂ a₂ : ℕ}
    (h₁ : IsHop y T b₁ a₁) (h₂ : IsHop y T b₂ a₂)
    (hb₁ : b₁ < t_cut) (ha₁ : t_cut ≤ a₁) (hb₂ : b₂ < t_cut) (_ha₂ : t_cut ≤ a₂)
    (hnc : ¬ HopsCross b₁ a₁ b₂ a₂) (ha₁₂ : a₁ < a₂) :
    b₂ < b₁ ∧ y a₁ ≠ y a₂ := by
  have hb_ne : b₁ ≠ b₂ := by
    intro heq
    subst heq
    exact h₂.2.2.2 a₁ (mem_Ioo.mpr ⟨lt_of_lt_of_le hb₁ ha₁, ha₁₂⟩) h₁.2.2.1
  have hb₂₁ : b₂ < b₁ := by
    rcases lt_or_gt_of_ne hb_ne with hlt | hgt
    · exfalso
      exact hnc (Or.inl ⟨hlt, lt_of_lt_of_le hb₂ ha₁, ha₁₂⟩)
    · exact hgt
  exact ⟨hb₂₁, fun hy => h₂.2.2.2 a₁ (mem_Ioo.mpr ⟨lt_of_lt_of_le hb₂ ha₁, ha₁₂⟩) (hy.trans h₂.2.2.1)⟩

/-- Revisit hop `(p, u)` on walk `y` whose excursion lies in `(excLo, excHi]`. -/
def HopInBand (y : ℕ → ℤ) (T excLo excHi p u : ℕ) : Prop :=
  IsHop y T p u ∧
  (∃ t ∈ Ioo p u, (excLo : ℤ) < |y t - y p|) ∧
  (∀ t ∈ Ioo p u, |y t - y p| ≤ (excHi : ℤ))

/-- **Intrinsic Mixing Steps `Mix_η(τ₀)`:**
Steps `s < T` taking part (`s = p ∨ s = u`) in a revisit hop on some work tape `j` with excursion in
`(2W, ⌊L / ηInv⌋]` that is non-LIFO (`owner load > 1` on `(2W, ⌊L / ηInv⌋]`, or crossing another hop
in `(2W, ⌊L / ηInv⌋]`). Defined purely from head motion alone. -/
noncomputable def mixEtaSteps {k : ℕ} (τ₀ : Trace k) (T W ηInv L : ℕ) : Finset ℕ :=
  (range T).filter fun s =>
    ∃ (j : Fin k) (p u : ℕ), (s = p ∨ s = u) ∧
      HopInBand (τ₀.work j) T (2 * W) (L / ηInv) p u ∧
      ((∃ p' u' : ℕ, (p', u') ≠ (p, u) ∧
          HopInBand (τ₀.work j) T (2 * W) (L / ηInv) p' u' ∧
          side τ₀.work (j, p', u') = side τ₀.work (j, p, u) ∧
          τ₀.work j p' = τ₀.work j p ∧
          hopOwner (τ₀.work j) p' u' = hopOwner (τ₀.work j) p u) ∨
        (∃ p' u' : ℕ, HopInBand (τ₀.work j) T (2 * W) (L / ηInv) p' u' ∧
          HopsCross p u p' u'))

/-- Revisit hop `(p, u)` attains spatial excursion strictly above `H`. -/
def HasHopExcursionGTAt (y : ℕ → ℤ) (H p u : ℕ) : Prop :=
  ∃ t ∈ Ioo p u, (H : ℤ) < |y t - y p|

/-- Revisit hop `(p, u)` of excursion `> H` on `y` that crosses **no** revisit hop of excursion `> H`. -/
def IsNonCrossingLargeHop (y : ℕ → ℤ) (T H p u : ℕ) : Prop :=
  IsHop y T p u ∧
  HasHopExcursionGTAt y H p u ∧
  ∀ p' u' : ℕ, IsHop y T p' u' → HasHopExcursionGTAt y H p' u' → ¬ HopsCross p u p' u'

/-- **Sharp Valley-to-Hop Crossing Lemma (the valley-to-hop crossing lemma):**
On any unit-speed walk `y` (`IsWalk y`), whenever `s₁ < m < s₂ < T` forms a valley of depth `> H`
below level `R` (`y s₁ ≥ R`, `y m + H < R`, `y s₂ ≥ R`), the last visit `p' ∈ [s₁, m)` to `≥ R` and
the first visit `u' ∈ (m, s₂]` to `≥ R` form a genuine `IsHop y T p' u'` at cell `R` with excursion
`|y m - y p'| > H`. -/
theorem exists_hop_gt_of_valley {y : ℕ → ℤ} (hy : IsWalk y) {T s₁ m s₂ H : ℕ} {R : ℤ}
    (hs₁m : s₁ < m) (hms₂ : m < s₂) (hs₂T : s₂ < T)
    (hys₁ : R ≤ y s₁) (hym : y m + (H : ℤ) < R) (hys₂ : R ≤ y s₂) :
    ∃ p' u' : ℕ, s₁ ≤ p' ∧ p' < m ∧ m < u' ∧ u' ≤ s₂ ∧
      IsHop y T p' u' ∧ HasHopExcursionGTAt y H p' u' := by
  have hH_nn : (0 : ℤ) ≤ (H : ℤ) := Nat.cast_nonneg H
  set S_left := (Ico s₁ m).filter fun t => R ≤ y t
  set S_right := (Ioc m s₂).filter fun t => R ≤ y t
  have hne_l : S_left.Nonempty := ⟨s₁, mem_filter.mpr ⟨mem_Ico.mpr ⟨le_rfl, hs₁m⟩, hys₁⟩⟩
  have hne_r : S_right.Nonempty := ⟨s₂, mem_filter.mpr ⟨mem_Ioc.mpr ⟨hms₂, le_rfl⟩, hys₂⟩⟩
  let p' := S_left.max' hne_l
  let u' := S_right.min' hne_r
  have hp'_mem := mem_filter.mp (S_left.max'_mem hne_l)
  have hu'_mem := mem_filter.mp (S_right.min'_mem hne_r)
  obtain ⟨hs₁p', hp'm⟩ := mem_Ico.mp hp'_mem.1
  obtain ⟨hmu', hu's₂⟩ := mem_Ioc.mp hu'_mem.1
  have hleft_lt : ∀ t, p' < t → t ≤ m → y t < R := by
    intro t hpt htm
    rcases eq_or_lt_of_le htm with rfl | ht_lt_m
    · omega
    · by_contra hge
      push Not at hge
      have ht_in : t ∈ S_left := mem_filter.mpr ⟨mem_Ico.mpr ⟨hs₁p'.trans hpt.le, ht_lt_m⟩, hge⟩
      have := S_left.le_max' t ht_in
      omega
  have hright_lt : ∀ t, m ≤ t → t < u' → y t < R := by
    intro t hmt htu
    rcases eq_or_lt_of_le hmt with rfl | hm_lt_t
    · omega
    · by_contra hge
      push Not at hge
      have ht_in : t ∈ S_right := mem_filter.mpr ⟨mem_Ioc.mpr ⟨hm_lt_t, htu.le.trans hu's₂⟩, hge⟩
      have := S_right.min'_le t ht_in
      omega
  have hp1_lt : y (p' + 1) < R := hleft_lt (p' + 1) (Nat.lt_succ_self p') hp'm
  have hu1_lt : y (u' - 1) < R := hright_lt (u' - 1) (by omega) (by omega)
  have hyp_step := abs_le.mp (hy p')
  have hyu_step := abs_le.mp (hy (u' - 1))
  rw [show u' - 1 + 1 = u' by omega] at hyu_step
  have hyp'_eq : y p' = R := by linarith [hp'_mem.2]
  have hyu'_eq : y u' = R := by linarith [hu'_mem.2]
  have hhop : IsHop y T p' u' := by
    refine ⟨by omega, lt_of_le_of_lt hu's₂ hs₂T, hyu'_eq.trans hyp'_eq.symm, fun t ht => ?_⟩
    obtain ⟨hpt, htu⟩ := mem_Ioo.mp ht
    rcases le_or_gt t m with htm | hmt
    · have := hleft_lt t hpt htm; omega
    · have := hright_lt t hmt.le htu; omega
  have hexc : HasHopExcursionGTAt y H p' u' := by
    refine ⟨m, mem_Ioo.mpr ⟨hp'm, hmu'⟩, ?_⟩
    have hneg : y m - y p' < 0 := by omega
    rw [abs_of_neg hneg]
    omega
  exact ⟨p', u', hs₁p', hp'm, hmu', hu's₂, hhop, hexc⟩

/-- **Same-Side Disjointness Impossibility (the same-side disjointness lemma):**
On *any* unit-speed walk `y` (even with arbitrary mixing elsewhere!), two upper-excursion `IsHop`s
`(b₁, a₁)` and `(b₂, a₂)` of excursion `> H` that are time-disjoint (`a₁ ≤ b₂`) cannot both belong
to `IsNonCrossingLargeHop y T H`. -/
theorem disjoint_upper_nonCrossingLargeHop_false {y : ℕ → ℤ} (hy : IsWalk y) {T H b₁ a₁ b₂ a₂ : ℕ}
    (h₁ : IsNonCrossingLargeHop y T H b₁ a₁) (h₂ : IsNonCrossingLargeHop y T H b₂ a₂)
    (hup₁ : ∃ t ∈ Ioo b₁ a₁, (H : ℤ) < y t - y b₁)
    (hup₂ : ∃ t ∈ Ioo b₂ a₂, (H : ℤ) < y t - y b₂)
    (hdisj : a₁ ≤ b₂) : False := by
  obtain ⟨t₁, ht₁_ioo, hgt₁⟩ := hup₁
  obtain ⟨t₂, ht₂_ioo, hgt₂⟩ := hup₂
  obtain ⟨hb₁t₁, ht₁a₁⟩ := mem_Ioo.mp ht₁_ioo
  obtain ⟨hb₂t₂, ht₂a₂⟩ := mem_Ioo.mp ht₂_ioo
  have ha₁_eq : y a₁ = y b₁ := h₁.1.2.2.1
  have ha₂T : a₂ < T := h₂.1.2.1
  have hyt₂_le : y t₂ ≤ y b₁ + (H : ℤ) := by
    by_contra hlt
    push Not at hlt
    obtain ⟨p', u', ht₁p', hp'a₁, ha₁u', _, hhop', hexc'⟩ :=
      exists_hop_gt_of_valley (T := T) (H := H) (R := y b₁ + (H : ℤ) + 1) hy
        ht₁a₁ (lt_of_le_of_lt hdisj hb₂t₂) (lt_trans ht₂a₂ ha₂T)
        (by omega) (by omega) (by omega)
    exact h₁.2.2 p' u' hhop' hexc' (Or.inl ⟨lt_of_lt_of_le hb₁t₁ ht₁p', hp'a₁, ha₁u'⟩)
  have hyt₁_le : y t₁ ≤ y b₂ + (H : ℤ) := by
    by_contra hlt
    push Not at hlt
    obtain ⟨p'', u'', _, hp''b₂, hb₂u'', hu''t₂, hhop'', hexc''⟩ :=
      exists_hop_gt_of_valley (T := T) (H := H) (R := y b₂ + (H : ℤ) + 1) hy
        (lt_of_lt_of_le ht₁a₁ hdisj) hb₂t₂ (lt_trans ht₂a₂ ha₂T)
        (by omega) (by omega) (by omega)
    exact h₂.2.2 p'' u'' hhop'' hexc'' (Or.inr ⟨hp''b₂, hb₂u'', lt_of_le_of_lt hu''t₂ ht₂a₂⟩)
  omega

/-- Every upper non-crossing `> H` hop on `IsWalk y` straddles a **single** common timestamp
`θ_pos ≤ T` (`p < θ_pos ∧ θ_pos ≤ u`). -/
theorem exists_cut_covering_upper_nonCrossingLargeHops {y : ℕ → ℤ} (hy : IsWalk y) (T H : ℕ) :
    ∃ θ_pos ≤ T, ∀ p u : ℕ,
      IsNonCrossingLargeHop y T H p u →
      (∃ t ∈ Ioo p u, (H : ℤ) < y t - y p) →
      p < θ_pos ∧ θ_pos ≤ u := by
  let P_up : Finset (ℕ × ℕ) :=
    ((range T) ×ˢ (range T)).filter fun x =>
      IsNonCrossingLargeHop y T H x.1 x.2 ∧ ∃ t ∈ Ioo x.1 x.2, (H : ℤ) < y t - y x.1
  rcases P_up.eq_empty_or_nonempty with hemp | hne
  · refine ⟨0, Nat.zero_le T, fun p u hnc hup => ?_⟩
    exfalso
    have hpT : p < T := lt_trans (lt_trans (Nat.lt_succ_self p) hnc.1.1) hnc.1.2.1
    have huT : u < T := hnc.1.2.1
    have hmem : (p, u) ∈ P_up :=
      mem_filter.mpr ⟨mem_product.mpr ⟨mem_range.mpr hpT, mem_range.mpr huT⟩, hnc, hup⟩
    rw [hemp] at hmem
    exact notMem_empty _ hmem
  · let L_starts := P_up.image Prod.fst
    have hL_ne : L_starts.Nonempty := hne.image Prod.fst
    let p_max := L_starts.max' hL_ne
    obtain ⟨⟨p₀, u₀⟩, hpu₀_mem, hp₀_eq⟩ := mem_image.mp (L_starts.max'_mem hL_ne)
    dsimp only at hp₀_eq
    obtain ⟨_, hnc₀, hup₀⟩ := mem_filter.mp hpu₀_mem
    refine ⟨u₀, le_of_lt hnc₀.1.2.1, fun p u hnc hup => ?_⟩
    have hpT : p < T := lt_trans (lt_trans (Nat.lt_succ_self p) hnc.1.1) hnc.1.2.1
    have huT : u < T := hnc.1.2.1
    have hmem : (p, u) ∈ P_up :=
      mem_filter.mpr ⟨mem_product.mpr ⟨mem_range.mpr hpT, mem_range.mpr huT⟩, hnc, hup⟩
    have hp_le : p ≤ p₀ := hp₀_eq.symm ▸ L_starts.le_max' p (mem_image.mpr ⟨(p, u), hmem, rfl⟩)
    have hp₀_lt_u₀ : p₀ < u₀ := lt_trans (Nat.lt_succ_self p₀) hnc₀.1.1
    refine ⟨lt_of_le_of_lt hp_le hp₀_lt_u₀, ?_⟩
    by_contra hu_lt
    push Not at hu_lt
    rcases le_or_gt u p₀ with hdisj | hp₀_lt_u
    · exact disjoint_upper_nonCrossingLargeHop_false hy hnc hnc₀ hup hup₀ hdisj
    · rcases eq_or_lt_of_le hp_le with rfl | hp_lt_p₀
      · exact hnc₀.1.2.2.2 u (mem_Ioo.mpr ⟨hp₀_lt_u, hu_lt⟩) hnc.1.2.2.1
      · exact hnc.2.2 p₀ u₀ hnc₀.1 hnc₀.2.1 (Or.inl ⟨hp_lt_p₀, hp₀_lt_u, hu_lt⟩)

private theorem isWalk_neg' {y : ℕ → ℤ} (hy : IsWalk y) : IsWalk (fun t => -y t) := by
  intro t
  have h := abs_le.mp (hy t)
  change |-y (t + 1) - -y t| ≤ 1
  rw [abs_le]
  omega

private theorem isHop_neg_iff' (y : ℕ → ℤ) (T p u : ℕ) :
    IsHop (fun t => -y t) T p u ↔ IsHop y T p u := by
  unfold IsHop
  simp only [ne_eq, neg_inj]

private theorem hasHopExcursionGTAt_neg_iff (y : ℕ → ℤ) (H p u : ℕ) :
    HasHopExcursionGTAt (fun t => -y t) H p u ↔ HasHopExcursionGTAt y H p u := by
  unfold HasHopExcursionGTAt
  constructor
  · rintro ⟨t, ht, hgt⟩
    refine ⟨t, ht, ?_⟩
    rwa [show -y t - -y p = -(y t - y p) by ring, abs_neg] at hgt
  · rintro ⟨t, ht, hgt⟩
    refine ⟨t, ht, ?_⟩
    rw [show -y t - -y p = -(y t - y p) by ring, abs_neg]
    exact hgt

private theorem isNonCrossingLargeHop_neg_iff (y : ℕ → ℤ) (T H p u : ℕ) :
    IsNonCrossingLargeHop (fun t => -y t) T H p u ↔ IsNonCrossingLargeHop y T H p u := by
  unfold IsNonCrossingLargeHop
  simp only [isHop_neg_iff', hasHopExcursionGTAt_neg_iff]

/-- **Universal 2-Cut LIFO Collapse on Arbitrary Unit-Speed Walks (Theorem 5.3 (bridge) Walk Core):**
On **any** unit-speed walk `y : ℕ → ℤ` (with **no** global assumption on `y` — `y` may perform
arbitrary non-LIFO mixing elsewhere!), there exist at most **two** timestamps `θ_pos, θ_neg ≤ T`
such that **every** revisit hop `(p, u)` of excursion `> H` that crosses no revisit hop of excursion
`> H` straddles either `θ_pos` or `θ_neg` (`p < θ_pos ∧ θ_pos ≤ u` or `p < θ_neg ∧ θ_neg ≤ u`). -/
theorem exists_two_cuts_covering_nonCrossingLargeHops {y : ℕ → ℤ} (hy : IsWalk y) (T H : ℕ) :
    ∃ θ_pos θ_neg : ℕ, θ_pos ≤ T ∧ θ_neg ≤ T ∧
      ∀ p u : ℕ, IsNonCrossingLargeHop y T H p u →
        (p < θ_pos ∧ θ_pos ≤ u) ∨ (p < θ_neg ∧ θ_neg ≤ u) := by
  obtain ⟨θ_pos, hθp_le, hθp⟩ := exists_cut_covering_upper_nonCrossingLargeHops hy T H
  obtain ⟨θ_neg, hθn_le, hθn⟩ := exists_cut_covering_upper_nonCrossingLargeHops (isWalk_neg' hy) T H
  refine ⟨θ_pos, θ_neg, hθp_le, hθn_le, fun p u hnc => ?_⟩
  obtain ⟨t, ht, hgt⟩ := hnc.2.1
  rcases lt_abs.mp hgt with hup | hlow
  · exact Or.inl (hθp p u hnc ⟨t, ht, hup⟩)
  · right
    have hnc_neg : IsNonCrossingLargeHop (fun s => -y s) T H p u :=
      (isNonCrossingLargeHop_neg_iff y T H p u).mpr hnc
    exact hθn p u hnc_neg ⟨t, ht, by omega⟩

end NonCrossingCut

end NativeRelations
