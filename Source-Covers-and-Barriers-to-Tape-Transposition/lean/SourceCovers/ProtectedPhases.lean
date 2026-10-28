import SourceCovers.ClippedShadows
import LeanMachine.ThinIntervals
import LeanMachine.FiniteOrbits

/-!
# Protected phases of actual Q2 cores

Use original nonleaf ranks, fixed before deletion. Cutting only nonleaves is
enough: original leaves need not be paid or consume protected residues.
-/

namespace SourceCovers

open Classical Finset LeanMachine LeanMachine.MonotonePatches

noncomputable section

variable {k T : ℕ} {xs : Fin k → ℕ → ℤ}

abbrev CoreFamily (K : Finset (ActualFamily xs T)) := {q // q ∈ K}

def coreModel (K : Finset (ActualFamily xs T)) : ThinIntervals.Model (CoreFamily K) where
  left := fun q => q.val.start
  right := fun q => q.val.stop
  nonempty := fun q => q.val.owner_bounds.1.trans q.val.owner_bounds.2

def coreColor {K : Finset (ActualFamily xs T)} (hc : HasSpanColoring K 2)
    (q : CoreFamily K) : ℕ := hc.choose q.val

theorem coreColor_lt {K : Finset (ActualFamily xs T)} (hc : HasSpanColoring K 2)
    (q : CoreFamily K) : coreColor hc q < 2 := hc.choose_spec.1 q.val q.property

theorem core_eq_of_same_color {K : Finset (ActualFamily xs T)} (hc : HasSpanColoring K 2)
    {a b : CoreFamily K} {t : ℕ} (ha : a.val.start < t ∧ t ≤ a.val.stop)
    (hb : b.val.start < t ∧ t ≤ b.val.stop) (he : coreColor hc a = coreColor hc b) : a = b := by
  apply Subtype.ext
  by_contra hn
  have hd := hc.choose_spec.2 a.val a.property b.val b.property hn he
  apply Finset.disjoint_left.mp hd (by
    simp only [ActualFamily.edges, mem_Ico]
    exact And.intro (show a.val.start ≤ t - 1 by omega) (show t - 1 < a.val.stop by omega))
  simp only [ActualFamily.edges, mem_Ico]; omega

theorem coreColor_ne_of_adj {K : Finset (ActualFamily xs T)} (hc : HasSpanColoring K 2)
    {a b : CoreFamily K} (hab : (coreModel K).graph.Adj a b) :
    coreColor hc a ≠ coreColor hc b := by
  intro he
  have ha := a.val.owner_bounds
  have hb := b.val.owner_bounds
  apply hab.ne
  apply core_eq_of_same_color hc (t := max a.val.start b.val.start + 1) _ _ he
  · change a ≠ b ∧ a.val.start < b.val.stop ∧ b.val.start < a.val.stop at hab
    omega
  · change a ≠ b ∧ a.val.start < b.val.stop ∧ b.val.start < a.val.stop at hab
    omega

theorem core_thin {K : Finset (ActualFamily xs T)} (hc : HasSpanColoring K 2) :
    (coreModel K).Thin := by
  intro a b c hab hbc hac
  have := coreColor_ne_of_adj hc hab
  have := coreColor_ne_of_adj hc hbc
  have := coreColor_ne_of_adj hc hac
  have := coreColor_lt hc a
  have := coreColor_lt hc b
  have := coreColor_lt hc c
  omega

/-- Forest, connected nonleaf parts, and degree at most two in those parts:
the caterpillar property, with component ranks supplied by `coreModel`. -/
theorem q2_caterpillar {K : Finset (ActualFamily xs T)} (hc : HasSpanColoring K 2) :
    (coreModel K).graph.IsAcyclic ∧
    (∀ a b (ha : (coreModel K).Nonleaf a) (hb : (coreModel K).Nonleaf b),
      (coreModel K).graph.Reachable a b →
      ((coreModel K).graph.induce (coreModel K).Nonleaf).Reachable ⟨a, ha⟩ ⟨b, hb⟩) ∧
    (∀ a, (coreModel K).Nonleaf a →
      (univ.filter (fun b => (coreModel K).Nonleaf b ∧ (coreModel K).graph.Adj a b)).card ≤ 2) :=
  ⟨ThinIntervals.Model.isAcyclic (core_thin hc),
    fun _ _ ha hb hr => ThinIntervals.Model.nonleaf_reachable ha hb hr,
    fun _ ha => ThinIntervals.Model.nonleaf_neighbors_card_le_two (core_thin hc) ha⟩

def coreNonleaves (K : Finset (ActualFamily xs T)) : Finset (CoreFamily K) :=
  univ.filter (coreModel K).Nonleaf

def corePhase (K : Finset (ActualFamily xs T)) (M : ℕ) (q : CoreFamily K) : ℕ :=
  (coreModel K).spineRank q % M

def admissiblePhases (K : Finset (ActualFamily xs T)) (P : Finset (CoreFamily K))
    (M : ℕ) : Finset ℕ :=
  PeriodicPhases.available (range M) (P ∩ coreNonleaves K) (corePhase K M)

def phaseSurvivors (K : Finset (ActualFamily xs T)) (M ρ : ℕ) : Finset (CoreFamily K) :=
  univ.filter (fun q => q ∉ coreNonleaves K ∨ corePhase K M q ≠ ρ)

def familyLowers {K : Finset (ActualFamily xs T)} (q : CoreFamily K) : Finset ℕ :=
  q.val.hops.image (fun η => η.2.1)

def phasePayment (K : Finset (ActualFamily xs T)) (M ρ : ℕ) : Finset ℕ :=
  PeriodicPhases.payment (coreNonleaves K) (corePhase K M) familyLowers ρ

theorem protected_survives {K : Finset (ActualFamily xs T)} {P : Finset (CoreFamily K)}
    {M ρ : ℕ} (hρ : ρ ∈ admissiblePhases K P M) {q : CoreFamily K} (hq : q ∈ P) :
    q ∈ phaseSurvivors K M ρ := by
  simp only [phaseSurvivors, mem_filter, mem_univ, true_and]
  by_cases hn : q ∈ coreNonleaves K
  · exact Or.inr (PeriodicPhases.protected_not_deleted hρ (mem_inter.mpr ⟨hq, hn⟩))
  · exact Or.inl hn

/-- Exact forbidden-residue count; protected leaves forbid nothing. -/
theorem admissiblePhases_card (K : Finset (ActualFamily xs T)) (P : Finset (CoreFamily K))
    {M : ℕ} (hM : 0 < M) :
    (admissiblePhases K P M).card = M - ((P ∩ coreNonleaves K).image (corePhase K M)).card := by
  simpa [admissiblePhases] using PeriodicPhases.available_card (range M)
    (P ∩ coreNonleaves K) (corePhase K M) (fun q _ => mem_range.mpr (Nat.mod_lt _ hM))

/-- The sum of actual paid unions is bounded by the actual lower supports
of unprotected nonleaves, then by their hop mass. -/
theorem phase_payment_sum (K : Finset (ActualFamily xs T)) (P : Finset (CoreFamily K)) (M : ℕ) :
    (∑ ρ ∈ admissiblePhases K P M, (phasePayment K M ρ).card) ≤
      ∑ q ∈ coreNonleaves K \ P, (familyLowers q).card := by
  have h := PeriodicPhases.sum_available_payment_le (coreNonleaves K)
    (P ∩ coreNonleaves K) (range M) (corePhase K M) familyLowers
  have he : coreNonleaves K \ (P ∩ coreNonleaves K) = coreNonleaves K \ P := by
    ext q; simp
  simpa only [he, admissiblePhases, phasePayment] using h

theorem phase_payment_sum_hops (K : Finset (ActualFamily xs T))
    (P : Finset (CoreFamily K)) (M : ℕ) :
    (∑ ρ ∈ admissiblePhases K P M, (phasePayment K M ρ).card) ≤
      ∑ q ∈ coreNonleaves K \ P, q.val.hops.card :=
  (phase_payment_sum K P M).trans (sum_le_sum (fun _ _ => card_image_le))

/-- Exact-residue averaging. A protected set may be arbitrarily large,
provided its nonleaves do not use every residue. -/
theorem phase_average_exact (K : Finset (ActualFamily xs T)) (P : Finset (CoreFamily K))
    {M : ℕ}
    (hused : ((P ∩ coreNonleaves K).image (corePhase K M)).card < M) :
    0 < (admissiblePhases K P M).card ∧
    ((∑ ρ ∈ admissiblePhases K P M, (phasePayment K M ρ).card : ℕ) : ℝ) /
        (admissiblePhases K P M).card ≤
      ((∑ q ∈ coreNonleaves K \ P, (familyLowers q).card : ℕ) : ℝ) /
        ((M - ((P ∩ coreNonleaves K).image (corePhase K M)).card : ℕ) : ℝ) := by
  have he := admissiblePhases_card K P (show 0 < M by omega)
  refine ⟨by omega, ?_⟩
  rw [← he]
  exact div_le_div_of_nonneg_right (by exact_mod_cast phase_payment_sum K P M)
    (Nat.cast_nonneg _)

/-- The original budget form follows with the smaller unprotected-nonleaf mass. -/
theorem protected_phase_average (K : Finset (ActualFamily xs T)) (P : Finset (CoreFamily K))
    {M R : ℕ} (hP : P.card ≤ R) (hR : R < M) :
    M - R ≤ (admissiblePhases K P M).card ∧
    ((∑ ρ ∈ admissiblePhases K P M, (phasePayment K M ρ).card : ℕ) : ℝ) /
        (admissiblePhases K P M).card ≤
      ((∑ q ∈ coreNonleaves K \ P, q.val.hops.card : ℕ) : ℝ) /
        (admissiblePhases K P M).card ∧
    ((∑ q ∈ coreNonleaves K \ P, q.val.hops.card : ℕ) : ℝ) /
        (admissiblePhases K P M).card ≤
      ((∑ q ∈ coreNonleaves K \ P, q.val.hops.card : ℕ) : ℝ) / ((M - R : ℕ) : ℝ) := by
  have he := admissiblePhases_card K P (show 0 < M by omega)
  have hb : ((P ∩ coreNonleaves K).image (corePhase K M)).card ≤ R :=
    card_image_le.trans ((card_le_card inter_subset_left).trans hP)
  have hd : M - R ≤ (admissiblePhases K P M).card := by omega
  refine ⟨hd, div_le_div_of_nonneg_right (by exact_mod_cast phase_payment_sum_hops K P M)
    (Nat.cast_nonneg _), ?_⟩
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg _)
    (by exact_mod_cast (show 0 < M - R by omega)) (by exact_mod_cast hd)

theorem nonleaf_mass_le_total (K : Finset (ActualFamily xs T)) (P : Finset (CoreFamily K)) :
    (∑ q ∈ coreNonleaves K \ P, q.val.hops.card) ≤ ∑ q ∈ univ \ P, q.val.hops.card := by
  apply sum_le_sum_of_subset_of_nonneg
  · intro q hq
    exact mem_sdiff.mpr ⟨mem_univ _, (mem_sdiff.mp hq).2⟩
  · intros; exact Nat.zero_le _

theorem phase_path_length {K : Finset (ActualFamily xs T)} (hc : HasSpanColoring K 2)
    {M ρ : ℕ} (hρ : ρ < M) {a b : CoreFamily K} (p : (coreModel K).graph.Walk a b)
    (hp : p.IsPath) (hw : ∀ q ∈ p.support, q ∈ phaseSurvivors K M ρ) :
    p.support.length ≤ M + 1 :=
  ThinIntervals.Model.path_card_le_of_avoids (core_thin hc) hp hρ (fun q hq hn =>
    ((mem_filter.mp (hw q hq)).2).resolve_left
      (not_not.mpr (mem_filter.mpr ⟨mem_univ _, hn⟩)))

abbrev coreAction {K : Finset (ActualFamily xs T)} (q : CoreFamily K) := q.val.shadowAction

/-- Every owner in a successful word precedes its starting time. -/
theorem core_success_owner_lt {K : Finset (ActualFamily xs T)} (w : List (CoreFamily K))
    {t : ℕ} (hs : t ∈ Action.success (w.map coreAction)) : ∀ q ∈ w, q.val.owner < t := by
  induction w generalizing t with
  | nil => simp
  | cons a w ih =>
    have h := (Action.success_cons_iff _ _ t).mp hs
    have ha := a.val.shadow_active_bounds ((a.val.shadow_ne_self_iff t).mp h.1)
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact ha.2.2.1
    · exact (ih h.2 q hq).trans_le (ha.2.1.trans ha.2.2.1.le)

theorem core_success_nodup {K : Finset (ActualFamily xs T)} (w : List (CoreFamily K))
    {t : ℕ} (hs : t ∈ Action.success (w.map coreAction)) : w.Nodup := by
  induction w generalizing t with
  | nil => simp
  | cons a w ih =>
    have h := (Action.success_cons_iff _ _ t).mp hs
    have ha := a.val.shadow_active_bounds ((a.val.shadow_ne_self_iff t).mp h.1)
    refine List.nodup_cons.mpr ⟨?_, ih h.2⟩
    intro hm
    have hb := core_success_owner_lt w h.2 a hm
    exact (not_lt_of_ge ha.2.1) hb

theorem core_success_chain {K : Finset (ActualFamily xs T)} (w : List (CoreFamily K))
    {t : ℕ} (hs : t ∈ Action.success (w.map coreAction)) :
    w.IsChain (coreModel K).graph.Adj := by
  induction w generalizing t with
  | nil => exact .nil
  | cons a w ih =>
    rcases w with _ | ⟨b, w⟩
    · exact .singleton _
    have h := (Action.success_cons_iff _ _ t).mp hs
    have h' := (Action.success_cons_iff _ _ _).mp h.2
    have ha := a.val.shadow_active_bounds ((a.val.shadow_ne_self_iff t).mp h.1)
    have hb := b.val.shadow_active_bounds ((b.val.shadow_ne_self_iff _).mp h'.1)
    have ho := a.val.owner_bounds
    have ho' := b.val.owner_bounds
    apply List.IsChain.cons_cons _ (ih h.2)
    change a ≠ b ∧ a.val.start < b.val.stop ∧ b.val.start < a.val.stop
    refine ⟨?_, ?_, ?_⟩
    · intro he; subst b
      exact (not_lt_of_ge ha.2.1) hb.2.2.1
    · exact ha.1.trans_le hb.2.2.2
    · exact ho'.1.trans (hb.2.2.1.trans_le (ha.2.1.trans ho.2.le))

/-- The strengthened periodic cut bounds every surviving successful word.
No unit-speed walk assumption is needed in this geometric part. -/
theorem phase_success_length {K : Finset (ActualFamily xs T)} (hc : HasSpanColoring K 2)
    {M ρ : ℕ} (hρ : ρ < M) (w : List (CoreFamily K))
    (hw : ∀ q ∈ w, q ∈ phaseSurvivors K M ρ) {t : ℕ}
    (hs : t ∈ Action.success (w.map coreAction)) : w.length ≤ M + 1 := by
  by_cases he : w = []
  · simp [he]
  let p := SimpleGraph.Walk.ofSupport w he (core_success_chain w hs)
  have hpw : p.support = w := SimpleGraph.Walk.support_ofSupport _ _
  have hp : p.IsPath := SimpleGraph.Walk.IsPath.mk' (by rw [hpw]; exact core_success_nodup w hs)
  have h := phase_path_length hc hρ p hp (fun q hq => hw q (hpw ▸ hq))
  simpa only [hpw] using h

theorem core_successors_card {K : Finset (ActualFamily xs T)} (hc : HasSpanColoring K 2)
    (I : Finset (CoreFamily K)) (t : ℕ) :
    (FiniteOrbits.successors I coreAction t).card ≤ 2 := by
  refine card_image_le.trans ?_
  have h := card_le_card_of_injOn (coreColor hc)
    (s := I.filter (fun q => (coreAction q).apply t ≠ t)) (t := range 2)
    (fun q _ => mem_range.mpr (coreColor_lt hc q)) ?_
  · simpa only [card_range] using h
  · intro a ha b hb he
    have ha' := a.val.shadow_active_bounds ((a.val.shadow_ne_self_iff t).mp (mem_filter.mp ha).2)
    have hb' := b.val.shadow_active_bounds ((b.val.shadow_ne_self_iff t).mp (mem_filter.mp hb).2)
    exact core_eq_of_same_color hc
      ⟨a.val.owner_bounds.1.trans ha'.2.2.1, ha'.2.2.2⟩
      ⟨b.val.owner_bounds.1.trans hb'.2.2.1, hb'.2.2.2⟩ he

/-- After any nonidentity action, at most one core family can act next. -/
theorem core_unique_after {K : Finset (ActualFamily xs T)} (hc : HasSpanColoring K 2)
    (q : CoreFamily K) {t : ℕ} (hq : q.val.shadow t ≠ t)
    {a b : CoreFamily K} (ha : a.val.shadow (q.val.shadow t) ≠ q.val.shadow t)
    (hb : b.val.shadow (q.val.shadow t) ≠ q.val.shadow t) : a = b := by
  have hq' := q.val.shadow_active_bounds ((q.val.shadow_ne_self_iff t).mp hq)
  have hspanq : q.val.start < q.val.shadow t ∧ q.val.shadow t ≤ q.val.stop :=
    ⟨hq'.1, hq'.2.1.trans q.val.owner_bounds.2.le⟩
  have next_ne (c : CoreFamily K) (hc' : c.val.shadow (q.val.shadow t) ≠ q.val.shadow t) :
      coreColor hc c ≠ coreColor hc q := by
    intro he
    have hb' := (c.val.shadow_ne_self_iff _).mp hc'
    have hsame := core_eq_of_same_color hc
      ⟨c.val.owner_bounds.1.trans hb'.1, hb'.2⟩ hspanq he
    subst c
    exact (not_lt_of_ge hq'.2.1) hb'.1
  have ha' := (a.val.shadow_ne_self_iff _).mp ha
  have hb' := (b.val.shadow_ne_self_iff _).mp hb
  apply core_eq_of_same_color hc
    ⟨a.val.owner_bounds.1.trans ha'.1, ha'.2⟩
    ⟨b.val.owner_bounds.1.trans hb'.1, hb'.2⟩
  have := next_ne a ha
  have := next_ne b hb
  have := coreColor_lt hc a
  have := coreColor_lt hc b
  have := coreColor_lt hc q
  omega

theorem core_deterministic_after {K : Finset (ActualFamily xs T)} (hc : HasSpanColoring K 2)
    (I : Finset (CoreFamily K)) :
    FiniteOrbits.DeterministicAfterStep (FiniteOrbits.successors I coreAction) := by
  intro t u hu
  obtain ⟨q, hq, rfl⟩ := mem_image.mp hu
  refine card_image_le.trans (card_le_one.mpr ?_)
  intro a ha b hb
  exact core_unique_after hc q (mem_filter.mp hq).2 (mem_filter.mp ha).2 (mem_filter.mp hb).2

/-- A finite set equal to the complete retained core orbit, not just an overcover. -/
def phaseOrbit (K : Finset (ActualFamily xs T)) (M ρ t : ℕ) : Finset ℕ :=
  FiniteOrbits.cloud (FiniteOrbits.successors (phaseSurvivors K M ρ) coreAction) (M + 1) t

theorem phase_orbit_exact {K : Finset (ActualFamily xs T)} (hc : HasSpanColoring K 2)
    {M ρ : ℕ} (hρ : ρ < M) (t : ℕ) :
    FiniteOrbits.wordOrbit (phaseSurvivors K M ρ) coreAction t =
      (phaseOrbit K M ρ t : Set ℕ) :=
  FiniteOrbits.orbit_eq_cloud _ _ _ _ (fun w hw hs => phase_success_length hc hρ w hw hs)

def retainedCore (K : Finset (ActualFamily xs T)) (M ρ : ℕ) : Finset (ActualFamily xs T) :=
  (phaseSurvivors K M ρ).image Subtype.val

/-- Identify the finite construction with the paper's previously defined orbit. -/
theorem phase_shadowOrbit_exact {K : Finset (ActualFamily xs T)} (hc : HasSpanColoring K 2)
    {M ρ : ℕ} (hρ : ρ < M) (t : ℕ) :
    shadowOrbit (retainedCore K M ρ) t = (phaseOrbit K M ρ t : Set ℕ) := by
  simpa only [shadowOrbit, retainedCore, FiniteOrbits.wordOrbit] using
    (FiniteOrbits.wordOrbit_image (phaseSurvivors K M ρ) Subtype.val ActualFamily.shadowAction t).trans
      (phase_orbit_exact hc hρ t)

/-- The complete orbit is the root together with at most two deterministic
continuations, of at most `M+1` values each (including their starting values). -/
theorem phase_orbit_chains {K : Finset (ActualFamily xs T)} (hc : HasSpanColoring K 2)
    (M ρ t : ℕ) :
    let s := FiniteOrbits.successors (phaseSurvivors K M ρ) coreAction
    phaseOrbit K M ρ t = insert t ((s t).biUnion (FiniteOrbits.cloud s M)) ∧
      (s t).card ≤ 2 ∧ FiniteOrbits.DeterministicAfterStep s ∧
      ∀ u ∈ s t, (FiniteOrbits.cloud s M u).card ≤ M + 1 :=
  ⟨rfl, core_successors_card hc _ t, core_deterministic_after hc _,
    fun u hu => FiniteOrbits.cloud_card_le_chain (core_deterministic_after hc _) M u
      (core_deterministic_after hc _ t u hu)⟩

theorem phase_orbit_card {K : Finset (ActualFamily xs T)} (hc : HasSpanColoring K 2)
    (M ρ t : ℕ) : (phaseOrbit K M ρ t).card ≤ 2 * M + 3 := by
  have h := FiniteOrbits.cloud_card_le (core_deterministic_after hc (phaseSurvivors K M ρ))
    (M + 1) t
  have h' := core_successors_card hc (phaseSurvivors K M ρ) t
  change (phaseOrbit K M ρ t).card ≤ _ at h
  nlinarith

end
end SourceCovers
