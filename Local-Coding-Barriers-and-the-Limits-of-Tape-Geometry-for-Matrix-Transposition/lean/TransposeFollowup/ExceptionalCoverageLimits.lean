import TransposeFollowup.ExceptionalStageClock
import TransposeFollowup.StageFlagLimits

/-! The global exceptional-tick allowance transfers to limiting regular stage
coverage. Endpoint null sets use mathlib's a.e. interval equalities. -/
namespace TransposeFollowup.RegularMotion
open Classical Set Filter Topology MeasureTheory
set_option autoImplicit false

theorem regular_limit_shallow_omission {B J : ℕ} {T : ℕ → ℕ} {P eps : ℕ → ℝ}
    {rho a C eta H : ℝ} (clocks : ∀ i, ContractingStageClock B J rho a C (P i) (T i))
    (good : ℕ → List (Fin B) × Fin J → Bool) {g : List (Fin B) × Fin J → Bool}
    {l r : List (Fin B) × Fin J → ℝ}
    (hr : 0 ≤ rho) (hr1 : rho < 1) (ha : 0 ≤ a) (hP : ∀ i, 0 < P i)
    (hl : ∀ p, Tendsto (fun i => ((clocks i).A p.1 p.2 : ℝ)/P i) atTop (𝓝 (l p)))
    (he : ∀ p, Tendsto (fun i => ((clocks i).E p.1 p.2 : ℝ)/P i) atTop (𝓝 (r p)))
    (hH : Tendsto (fun i => (T i : ℝ)/P i) atTop (𝓝 H))
    (hg : ∀ p, ∀ᶠ i in atTop, good i p=g p)
    (heps : Tendsto eps atTop (𝓝 0))
    (hbad : ∀ i, (exceptionalTicks (clocks i) (good i) : ℝ)/P i ≤ eta+eps i) (h : ℕ) :
    volume.real (Ico 0 H \ stageRegion l r {p | p.1.length < h ∧ g p=true}) ≤
      eta+a*C*rho^h/(1-rho) := by
  let Q := (finite_shallow_stage_keys B J h).toFinset
  have hQ : (Q : Set (List (Fin B) × Fin J))={p | p.1.length < h} := Set.Finite.coe_toFinset _
  have hfilter (b : List (Fin B) × Fin J → Bool) :
      (Q.filter (fun p => b p=true) : Set (List (Fin B) × Fin J))=
        {p | p.1.length < h ∧ b p=true} := by
    ext p
    simp only [Finset.mem_coe,Finset.mem_filter,Set.mem_ofPred_eq]
    have hp : p ∈ Q ↔ p.1.length < h := by change p ∈ (Q : Set _) ↔ _; rw [hQ]; rfl
    rw [hp]
  have hb : ∀ᶠ i in atTop, 0 ≤ (T i : ℝ)/P i ∧ ∀ p ∈ Q,
      0 ≤ ((clocks i).A p.1 p.2 : ℝ)/P i ∧
      ((clocks i).A p.1 p.2 : ℝ)/P i ≤ ((clocks i).E p.1 p.2 : ℝ)/P i ∧
      ((clocks i).E p.1 p.2 : ℝ)/P i ≤ (T i : ℝ)/P i := by
    apply Eventually.of_forall
    intro i
    refine ⟨div_nonneg (Nat.cast_nonneg _) (hP i).le,fun p _ => ?_⟩
    exact ⟨div_nonneg (Nat.cast_nonneg _) (hP i).le,
      div_le_div_of_nonneg_right (by exact_mod_cast (clocks i).ordered p.1 p.2) (hP i).le,
      div_le_div_of_nonneg_right (by exact_mod_cast (clocks i).bounded p.1 p.2) (hP i).le⟩
  have hd : ∀ᶠ i in atTop, (Q : Set (List (Fin B) × Fin J)).PairwiseDisjoint
      (fun p => Ico (((clocks i).A p.1 p.2 : ℝ)/P i) (((clocks i).E p.1 p.2 : ℝ)/P i)) := by
    apply Eventually.of_forall
    intro i p hp q hq hpq
    exact real_stages_scaled_pairwise_disjoint (hP i) (clocks i).label
      (fun p => (clocks i).A p.1 p.2) (fun p => (clocks i).E p.1 p.2)
      (fun p => (clocks i).bounded p.1 p.2) (fun p t => (clocks i).partition p.1 p.2 t) hpq
  have hlim := finite_flagged_stage_omission_tendsto Q (fun p _ => hl p) (fun p _ => he p)
    hH hb hd (fun p _ => hg p)
  simp only [hfilter] at hlim
  have hupper : Tendsto (fun i => (eta+eps i)+a*C*rho^h/(1-rho)) atTop
      (𝓝 (eta+a*C*rho^h/(1-rho))) := by
    simpa using (tendsto_const_nhds.add heps).add_const (a*C*rho^h/(1-rho))
  apply le_of_tendsto_of_tendsto hlim hupper (Eventually.of_forall ?_)
  intro i
  exact (regular_shallow_stage_omission (clocks i) hr hr1 ha (hP i) (good i) h).trans
    (add_le_add (hbad i) le_rfl)

theorem geometric_regular_stage_open_defect {B J : ℕ}
    {l r : List (Fin B) × Fin J → ℝ} {g : List (Fin B) × Fin J → Bool}
    {H a C rho eta : ℝ} (hr : 0 ≤ rho) (hr1 : rho < 1)
    (hcov : ∀ h : ℕ, volume.real (Ico 0 H \ stageRegion l r {p | p.1.length < h ∧ g p=true}) ≤
      eta+a*C*rho^h/(1-rho)) :
    volume.real (Icc 0 H \ ⋃ p, ⋃ (_ : g p=true), Ioo (l p) (r p)) ≤ eta := by
  have hclock : volume (Ico (0 : ℝ) H) ≠ ⊤ := by
    rw [Real.volume_Ico]
    exact ENNReal.ofReal_ne_top
  have hsmall (h : ℕ) :
      Ico 0 H \ stageRegion l r {p | g p=true} ⊆
        Ico 0 H \ stageRegion l r {p | p.1.length < h ∧ g p=true} := by
    intro x hx
    refine ⟨hx.1,fun hy => hx.2 ?_⟩
    obtain ⟨p,hp⟩ := Set.mem_iUnion.mp hy
    obtain ⟨hp,hxp⟩ := Set.mem_iUnion.mp hp
    exact Set.mem_iUnion.mpr ⟨p,Set.mem_iUnion.mpr ⟨hp.2,hxp⟩⟩
  have hle (h : ℕ) : volume.real (Ico 0 H \ stageRegion l r {p | g p=true}) ≤
      eta+a*C*rho^h/(1-rho) :=
    (measureReal_mono (hsmall h) (measure_ne_top_of_subset Set.sdiff_subset hclock)).trans (hcov h)
  have htail : Tendsto (fun h : ℕ => eta+a*C*rho^h/(1-rho)) atTop (𝓝 eta) := by
    simpa using (((tendsto_pow_atTop_nhds_zero_of_lt_one hr hr1).const_mul (a*C)).div_const
      (1-rho)).const_add eta
  have hbound : volume.real (Ico 0 H \ stageRegion l r {p | g p=true}) ≤ eta :=
    ge_of_tendsto htail (Eventually.of_forall hle)
  have hU : (⋃ p, ⋃ (_ : g p=true), Ioo (l p) (r p)) =ᵐ[volume]
      stageRegion l r {p | g p=true} := by
    change (⋃ p, ⋃ (_ : g p=true), Ioo (l p) (r p)) =ᵐ[volume]
      (⋃ p, ⋃ (_ : g p=true), Ico (l p) (r p))
    exact EventuallyEqSet.countable_iUnion (fun p =>
      EventuallyEqSet.iUnion (fun _ : g p=true => Ioo_ae_eq_Ico))
  have hI : Icc (0 : ℝ) H =ᵐ[volume] Ico 0 H := Ico_ae_eq_Icc.symm
  rw [measureReal_congr (ae_eq_set_sdiff hI hU)]
  exact hbound

theorem exists_exceptional_stage_limit_cover {B J : ℕ} {T : ℕ → ℕ} {P eps : ℕ → ℝ}
    {rho a C eta : ℝ} (clocks : ∀ i, ContractingStageClock B J rho a C (P i) (T i))
    (good : ℕ → List (Fin B) × Fin J → Bool)
    (hr : 0 ≤ rho) (hr1 : rho < 1) (ha : 0 ≤ a) (hP : ∀ i, 0 < P i)
    (heps : Tendsto eps atTop (𝓝 0))
    (hbad : ∀ i, (exceptionalTicks (clocks i) (good i) : ℝ)/P i ≤ eta+eps i) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ (H : ℝ) (l r : List (Fin B) × Fin J → ℝ)
      (v : List (Fin B) → ℝ) (g : List (Fin B) × Fin J → Bool),
      H ∈ Icc 0 (a*C/(1-rho)) ∧ (∀ w, v w ∈ Icc 0 (C/(1-rho))) ∧
      Tendsto (fun i => (T (φ i) : ℝ)/P (φ i)) atTop (𝓝 H) ∧
      (∀ p, Tendsto (fun i => ((clocks (φ i)).A p.1 p.2 : ℝ)/P (φ i)) atTop (𝓝 (l p))) ∧
      (∀ p, Tendsto (fun i => ((clocks (φ i)).E p.1 p.2 : ℝ)/P (φ i)) atTop (𝓝 (r p))) ∧
      (∀ w, Tendsto (fun i => (clocks (φ i)).V w/P (φ i)) atTop (𝓝 (v w))) ∧
      (∀ p, ∀ᶠ i in atTop, good (φ i) p=g p) ∧
      (∀ p, 0 ≤ l p ∧ l p ≤ r p ∧ r p ≤ H) ∧
      volume.real (Icc 0 H \ ⋃ p, ⋃ (_ : g p=true), Ioo (l p) (r p)) ≤ eta := by
  obtain ⟨φ,hφ,H,l,r,v,hHI,hvI,hH,hl,he,hv,hbounds,_,_⟩ :=
    exists_stage_clock_limit_cover (fun i => (clocks i).nonneg) hr hr1 ha hP
      (fun i => (clocks i).children) (fun i => (clocks i).root)
      (fun i => (clocks i).label) (fun i => (clocks i).A) (fun i => (clocks i).E)
      (fun i => (clocks i).ordered) (fun i => (clocks i).bounded)
      (fun i => (clocks i).partition) (fun i => (clocks i).budget)
  obtain ⟨g,ψ,hψ,hg⟩ := exists_stage_flag_subsequence (fun i => good (φ i))
  refine ⟨φ ∘ ψ,hφ.comp hψ,H,l,r,v,g,hHI,hvI,hH.comp hψ.tendsto_atTop,
    (fun p => (hl p).comp hψ.tendsto_atTop),(fun p => (he p).comp hψ.tendsto_atTop),
    (fun w => (hv w).comp hψ.tendsto_atTop),hg,hbounds,?_⟩
  apply geometric_regular_stage_open_defect hr hr1
  intro h
  exact regular_limit_shallow_omission (fun i => clocks (φ (ψ i))) (fun i => good (φ (ψ i)))
    hr hr1 ha (fun i => hP (φ (ψ i))) (fun p => (hl p).comp hψ.tendsto_atTop)
    (fun p => (he p).comp hψ.tendsto_atTop) (hH.comp hψ.tendsto_atTop) hg
    (heps.comp (hφ.comp hψ).tendsto_atTop) (fun i => hbad (φ (ψ i))) h

end TransposeFollowup.RegularMotion
