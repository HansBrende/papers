import TransposeFollowup.FiniteStageLimits
import TransposeFollowup.PhysicalStageCoverage

/-! Actual finite clocks imply almost-everywhere coverage by the interiors of
limiting stage intervals. Countable endpoint sets have measure zero; the work
omitted at depth h is bounded by the already proved geometric tail. -/
namespace TransposeFollowup.RegularMotion
open Classical Set Filter Topology MeasureTheory
open scoped BigOperators
set_option autoImplicit false

theorem geometric_stage_open_cover {B J : ℕ} {l r : List (Fin B) × Fin J → ℝ}
    {H a C rho : ℝ} (hr : 0 ≤ rho) (hr1 : rho < 1)
    (hcov : ∀ h : ℕ, volume.real (Ico 0 H \ stageRegion l r {p | p.1.length < h}) ≤
      a*C*rho^h/(1-rho)) :
    volume (Icc 0 H \ ⋃ p, Ioo (l p) (r p))=0 := by
  have hclock : volume (Ico (0 : ℝ) H) ≠ ⊤ := by
    rw [Real.volume_Ico]
    exact ENNReal.ofReal_ne_top
  have hsmall (h : ℕ) :
      Ico 0 H \ stageRegion l r Set.univ ⊆
        Ico 0 H \ stageRegion l r {p | p.1.length < h} := by
    intro x hx
    refine ⟨hx.1,fun hy => hx.2 ?_⟩
    obtain ⟨p,hp⟩ := Set.mem_iUnion.mp hy
    obtain ⟨_,hxp⟩ := Set.mem_iUnion.mp hp
    exact Set.mem_iUnion.mpr ⟨p,Set.mem_iUnion.mpr ⟨Set.mem_univ _,hxp⟩⟩
  have hle (h : ℕ) : volume.real (Ico 0 H \ stageRegion l r Set.univ) ≤
      a*C*rho^h/(1-rho) :=
    (measureReal_mono (hsmall h) (measure_ne_top_of_subset Set.sdiff_subset hclock)).trans (hcov h)
  have htail : Tendsto (fun h : ℕ => a*C*rho^h/(1-rho)) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hr hr1).const_mul (a*C)).div_const (1-rho)
  have hzero : volume (Ico 0 H \ stageRegion l r Set.univ)=0 :=
    (measureReal_eq_zero_iff (measure_ne_top_of_subset Set.sdiff_subset hclock)).mp
      (le_antisymm (ge_of_tendsto htail (Eventually.of_forall hle)) measureReal_nonneg)
  let Z : Set ℝ := Set.range l ∪ {H}
  have hZ : Z.Countable := (Set.countable_range l).union (Set.countable_singleton H)
  apply measure_mono_null (t:=(Ico 0 H \ stageRegion l r Set.univ) ∪ Z)
  · intro x hx
    by_cases hxH : x=H
    · exact Or.inr (Or.inr (Set.mem_singleton_iff.mpr hxH))
    have hxI : x ∈ Ico 0 H := ⟨hx.1.1,lt_of_le_of_ne hx.1.2 hxH⟩
    by_cases hxs : x ∈ stageRegion l r Set.univ
    · obtain ⟨p,hp⟩ := Set.mem_iUnion.mp hxs
      obtain ⟨_,hxp⟩ := Set.mem_iUnion.mp hp
      have hxl : x=l p := by
        by_contra hne
        exact hx.2 (Set.mem_iUnion.mpr ⟨p,lt_of_le_of_ne hxp.1 (Ne.symm hne),hxp.2⟩)
      exact Or.inr (Or.inl ⟨p,hxl.symm⟩)
    · exact Or.inl ⟨hxI,hxs⟩
  · exact measure_union_null hzero (hZ.measure_zero volume)

theorem stage_clock_limit_shallow_omission
    {B J : ℕ} {T : ℕ → ℕ} {P : ℕ → ℝ} {V : ℕ → List (Fin B) → ℝ}
    {rho a C H : ℝ} {l r : List (Fin B) × Fin J → ℝ}
    (hV : ∀ n w, 0 ≤ V n w) (hr : 0 ≤ rho) (hr1 : rho < 1)
    (ha : 0 ≤ a) (hP : ∀ n, 0 < P n)
    (hc : ∀ n w, ∑ b : Fin B, V n (w++[b]) ≤ rho*V n w)
    (hroot : ∀ n, V n [] ≤ C*P n)
    (label : ∀ n, Fin (T n) → List (Fin B) × Fin J)
    (A E : ℕ → List (Fin B) → Fin J → ℕ)
    (hAE : ∀ n w j, A n w j ≤ E n w j) (hE : ∀ n w j, E n w j ≤ T n)
    (hstage : ∀ n w j (t : Fin (T n)),
      (A n w j ≤ t.val ∧ t.val < E n w j) ↔ label n t=(w,j))
    (hbudget : ∀ n w, ((∑ j : Fin J, (E n w j-A n w j) : ℕ) : ℝ) ≤ a*V n w)
    (hl : ∀ p, Tendsto (fun n => (A n p.1 p.2 : ℝ)/P n) atTop (𝓝 (l p)))
    (he : ∀ p, Tendsto (fun n => (E n p.1 p.2 : ℝ)/P n) atTop (𝓝 (r p)))
    (hH : Tendsto (fun n => (T n : ℝ)/P n) atTop (𝓝 H)) (h : ℕ) :
    volume.real (Ico 0 H \ stageRegion l r {p | p.1.length < h}) ≤ a*C*rho^h/(1-rho) := by
  let Q := (finite_shallow_stage_keys B J h).toFinset
  have hQ : (Q : Set (List (Fin B) × Fin J))={p | p.1.length < h} := Set.Finite.coe_toFinset _
  have hb : ∀ᶠ n in atTop, 0 ≤ (T n : ℝ)/P n ∧ ∀ p ∈ Q,
      0 ≤ (A n p.1 p.2 : ℝ)/P n ∧
      (A n p.1 p.2 : ℝ)/P n ≤ (E n p.1 p.2 : ℝ)/P n ∧
      (E n p.1 p.2 : ℝ)/P n ≤ (T n : ℝ)/P n := by
    apply Eventually.of_forall
    intro n
    refine ⟨div_nonneg (Nat.cast_nonneg _) (hP n).le,?_⟩
    intro p hp
    exact ⟨div_nonneg (Nat.cast_nonneg _) (hP n).le,
      div_le_div_of_nonneg_right (by exact_mod_cast hAE n p.1 p.2) (hP n).le,
      div_le_div_of_nonneg_right (by exact_mod_cast hE n p.1 p.2) (hP n).le⟩
  have hd : ∀ᶠ n in atTop, (Q : Set (List (Fin B) × Fin J)).PairwiseDisjoint
      (fun p => Ico ((A n p.1 p.2 : ℝ)/P n) ((E n p.1 p.2 : ℝ)/P n)) := by
    apply Eventually.of_forall
    intro n p hp q hq hpq
    exact real_stages_scaled_pairwise_disjoint (hP n) (label n)
      (fun p => A n p.1 p.2) (fun p => E n p.1 p.2)
      (fun p => hE n p.1 p.2) (fun p t => hstage n p.1 p.2 t) hpq
  have hlim := finite_stage_omission_tendsto Q (fun p _ => hl p) (fun p _ => he p) hH hb hd
  rw [hQ] at hlim
  apply le_of_tendsto hlim (Eventually.of_forall ?_)
  intro n
  exact stage_clock_physical_omission_of_root_bound (hV n) hr hr1 ha (hP n) (hc n)
    (hroot n) (label n) (A n) (E n) (hE n) (hstage n) (hbudget n) h

end TransposeFollowup.RegularMotion
