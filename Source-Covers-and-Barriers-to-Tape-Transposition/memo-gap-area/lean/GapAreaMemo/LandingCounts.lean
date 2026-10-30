import GapAreaMemo.LandingOrbits

set_option autoImplicit false

/-!
# Counts at one selection and phase

For the retained core of a legal phase and one newer family `g`, the newer
closure of a root is covered by at most `2M + 4` core orbits. Points of the
closure in a time region are bounded linearly in `M` once the nonleaf
families whose lower regions meet the region are bounded. Landing times of an
older family `e` that are reached without a core step from another landing
time (the starts) are linear in `M`, and every landing time is reached from a
start by at most `M + 1` core steps between landing times.
-/

namespace SourceCovers

open Classical Finset LeanMachine LeanMachine.MonotonePatches
open scoped BigOperators
noncomputable section

variable {k T : ℕ} {xs : Fin k → ℕ → ℤ} {K : Finset (ActualFamily xs T)}

/-- A successful survivor word reaching any point of the phase orbit. -/
theorem exists_success_word (hc : HasSpanColoring K 2) {M ρ : ℕ} (hρ : ρ < M) {r v : ℕ}
    (hv : v ∈ phaseOrbit K M ρ r) :
    ∃ w : List (CoreFamily K), (∀ a ∈ w, a ∈ phaseSurvivors K M ρ) ∧ CoreSuccess w r ∧
      coreEndpoint w r = v := by
  have hv' : v ∈ FiniteOrbits.wordOrbit (phaseSurvivors K M ρ) coreAction r := by
    rw [phase_orbit_exact hc hρ]; exact_mod_cast hv
  obtain ⟨w, hw, he⟩ := hv'
  obtain ⟨w', hsub, hs, he'⟩ := FiniteOrbits.reduce_word coreAction w r
  exact ⟨w', fun a ha => hw a (hsub.subset ha), hs, he'.trans he⟩

/-- Successful words ending in a prescribed set of families: at most two per family. -/
theorem core_root_count_last (hc : HasSpanColoring K 2) (r : ℕ) (X : Finset ℕ)
    (Λ : Finset (CoreFamily K)) (w : ℕ → List (CoreFamily K))
    (hw : ∀ v ∈ X, w v ≠ [] ∧ CoreSuccess (w v) r ∧ coreEndpoint (w v) r = v)
    (hΛ : ∀ v ∈ X, ∀ G, (w v).getLast? = some G → G ∈ Λ) :
    X.card ≤ 2 * Λ.card := by
  classical
  let f : ℕ → Option (CoreFamily K) × Option (CoreFamily K) :=
    fun v => ((w v).head?, (w v).getLast?)
  have hmaps : ∀ v ∈ X, f v ∈ (activeAt K r).image some ×ˢ Λ.image some := by
    intro v hv
    obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp (by simpa using (hw v hv).1 :
      (w v).head? ≠ none)
    obtain ⟨G, hG⟩ := Option.ne_none_iff_exists'.mp (by simpa using (hw v hv).1 :
      (w v).getLast? ≠ none)
    refine mem_product.mpr ⟨?_, ?_⟩
    · change (w v).head? ∈ _
      rw [hq]
      exact mem_image_of_mem _ (head_mem_activeAt (hw v hv).2.1 hq)
    · change (w v).getLast? ∈ _
      rw [hG]
      exact mem_image_of_mem _ (hΛ v hv G hG)
  have hinj : Set.InjOn f X := by
    intro v hv v' hv' he
    have he' := Prod.ext_iff.mp he
    have heq := coreSuccess_eq_of_head_last hc (hw v hv).2.1 (hw v' hv').2.1 (hw v hv).1
      he'.1 he'.2
    rw [← (hw v hv).2.2, ← (hw v' hv').2.2, heq]
  have := card_le_card_of_injOn f hmaps hinj
  rw [card_product] at this
  have hA := (card_image_le (s := activeAt K r) (f := some)).trans (activeAt_card hc r)
  have hB := card_image_le (s := Λ) (f := some)
  nlinarith

/-- The root and the nonidentity landings of `g` on its core orbit. -/
def newerRoots (K : Finset (ActualFamily xs T)) (M ρ : ℕ) (g : ActualFamily xs T) (s : ℕ) :
    Finset ℕ :=
  insert s (((phaseOrbit K M ρ s).filter (fun u => g.shadow u ≠ u)).image g.shadow)

/-- The union of the core orbits of the newer roots. -/
def newerClosure (K : Finset (ActualFamily xs T)) (M ρ : ℕ) (g : ActualFamily xs T) (s : ℕ) :
    Finset ℕ :=
  (newerRoots K M ρ g s).biUnion (phaseOrbit K M ρ)

theorem newerRoots_card (hc : HasSpanColoring K 2) (M ρ : ℕ) (g : ActualFamily xs T) (s : ℕ) :
    (newerRoots K M ρ g s).card ≤ 2 * M + 4 := by
  have h := phase_orbit_card hc M ρ s
  refine (card_insert_le _ _).trans ?_
  have := (card_image_le (s := (phaseOrbit K M ρ s).filter (fun u => g.shadow u ≠ u))
    (f := g.shadow)).trans (card_filter_le _ _)
  omega

theorem shadowOrbit_newer_subset (hc : HasSpanColoring K 2) {M ρ : ℕ} (hρ : ρ < M)
    (g : ActualFamily xs T) (s : ℕ) :
    shadowOrbit (retainedCore K M ρ ∪ {g}) s ⊆ (newerClosure K M ρ g s : Set ℕ) := by
  intro v hv
  rcases shadowOrbit_insert_newer _ g s v hv with hv | ⟨u, hu, hgu, hv⟩
  · rw [phase_shadowOrbit_exact hc hρ] at hv
    exact mem_biUnion.mpr ⟨s, mem_insert_self _ _, by exact_mod_cast hv⟩
  · rw [phase_shadowOrbit_exact hc hρ] at hu hv
    refine mem_biUnion.mpr ⟨g.shadow u, ?_, by exact_mod_cast hv⟩
    exact mem_insert_of_mem (mem_image_of_mem _ (mem_filter.mpr ⟨by exact_mod_cast hu, hgu⟩))

theorem newerClosure_le (hc : HasSpanColoring K 2) {M ρ : ℕ} (hρ : ρ < M)
    (g : ActualFamily xs T) {s v : ℕ} (hv : v ∈ newerClosure K M ρ g s) : v ≤ s := by
  obtain ⟨r, hr, hv⟩ := mem_biUnion.mp hv
  have hvr : v ≤ r := by
    have : v ∈ shadowOrbit (retainedCore K M ρ) r := by
      rw [phase_shadowOrbit_exact hc hρ]; exact_mod_cast hv
    exact shadowOrbit_le this
  rcases mem_insert.mp hr with rfl | hr
  · exact hvr
  · obtain ⟨u, hu, rfl⟩ := mem_image.mp hr
    have hus : u ≤ s := by
      have : u ∈ shadowOrbit (retainedCore K M ρ) s := by
        rw [phase_shadowOrbit_exact hc hρ]; exact_mod_cast (mem_filter.mp hu).1
      exact shadowOrbit_le this
    exact hvr.trans ((g.shadowAction.apply_le u).trans hus)

/-- **Linear production count.** -/
theorem newerClosure_count (hc : HasSpanColoring K 2) {M ρ : ℕ} (hρ : ρ < M)
    (g : ActualFamily xs T) (s : ℕ) (D : Set ℕ) (Φ : Finset (CoreFamily K))
    (hΦ : ∀ G : CoreFamily K, (coreModel K).Nonleaf G → ∀ t ∈ D,
      G.val.start < t → t ≤ G.val.owner → G ∈ Φ) :
    ((newerClosure K M ρ g s).filter (· ∈ D)).card ≤ (2 * M + 4) * (2 * Φ.card + 5) := by
  classical
  have hsub : (newerClosure K M ρ g s).filter (· ∈ D) ⊆
      (newerRoots K M ρ g s).biUnion (fun r => (phaseOrbit K M ρ r).filter (· ∈ D)) := by
    intro v hv
    obtain ⟨hv, hD⟩ := mem_filter.mp hv
    obtain ⟨r, hr, hvr⟩ := mem_biUnion.mp hv
    exact mem_biUnion.mpr ⟨r, hr, mem_filter.mpr ⟨hvr, hD⟩⟩
  have hroot : ∀ r, ((phaseOrbit K M ρ r).filter (· ∈ D)).card ≤ 2 * Φ.card + 5 := by
    intro r
    let X := ((phaseOrbit K M ρ r).filter (· ∈ D)).erase r
    have hX : X.card ≤ 2 * Φ.card + 4 := by
      let w : ℕ → List (CoreFamily K) := fun v =>
        if h : v ∈ phaseOrbit K M ρ r then (exists_success_word hc hρ h).choose else []
      have hwv : ∀ v ∈ X, w v ≠ [] ∧ CoreSuccess (w v) r ∧ coreEndpoint (w v) r = v := by
        intro v hv
        have hvr : v ≠ r := (mem_erase.mp hv).1
        have hvo : v ∈ phaseOrbit K M ρ r := (mem_filter.mp (mem_erase.mp hv).2).1
        have hspec := (exists_success_word hc hρ hvo).choose_spec
        have hw : w v = (exists_success_word hc hρ hvo).choose := dite_eq_left hvo
        rw [hw]
        refine ⟨?_, hspec.2.1, hspec.2.2⟩
        intro hnil
        have := hspec.2.2
        rw [hnil] at this
        exact hvr this.symm
      apply core_root_count hc r X Φ w hwv
      intro v hv G hG hn
      have hb := coreSuccess_endpoint_lower (hwv v hv).2.1 hG
      rw [(hwv v hv).2.2] at hb
      exact hΦ G hn v (mem_filter.mp (mem_erase.mp hv).2).2 hb.1 hb.2
    have := card_le_card (s := (phaseOrbit K M ρ r).filter (· ∈ D)) (t := insert r X)
      (fun v hv => by
        by_cases h : v = r
        · rw [h]; exact mem_insert_self _ _
        · exact mem_insert_of_mem (mem_erase.mpr ⟨h, hv⟩))
    exact this.trans ((card_insert_le _ _).trans (by omega))
  calc
    _ ≤ _ := card_le_card hsub
    _ ≤ ∑ r ∈ newerRoots K M ρ g s, ((phaseOrbit K M ρ r).filter (· ∈ D)).card :=
      card_biUnion_le
    _ ≤ ∑ _r ∈ newerRoots K M ρ g s, (2 * Φ.card + 5) := sum_le_sum fun r _ => hroot r
    _ = (newerRoots K M ρ g s).card * (2 * Φ.card + 5) := by rw [sum_const, smul_eq_mul]
    _ ≤ _ := Nat.mul_le_mul_right _ (newerRoots_card hc M ρ g s)

/-- Nonleaf families adjacent to a given family: at most two. -/
theorem nonleaf_adj_card_le_two (hc : HasSpanColoring K 2) (b : CoreFamily K) :
    (univ.filter (fun G => (coreModel K).Nonleaf G ∧ (coreModel K).graph.Adj b G)).card ≤ 2 := by
  by_cases hb : (coreModel K).Nonleaf b
  · exact ThinIntervals.Model.nonleaf_neighbors_card_le_two (core_thin hc) hb
  · refine (card_le_card (filter_subset_filter _ (subset_univ _))).trans ?_
    by_contra hlt
    push Not at hlt
    obtain ⟨G, hG, G', hG', hne⟩ := one_lt_card.mp (by omega :
      1 < (univ.filter (fun G => (coreModel K).Nonleaf G ∧ (coreModel K).graph.Adj b G)).card)
    exact hb ⟨G, G', (mem_filter.mp hG).2.2, (mem_filter.mp hG').2.2, hne⟩

/-- Points of the newer closure strictly between two times inside one core span. -/
theorem newerClosure_count_span (hc : HasSpanColoring K 2) {M ρ : ℕ} (hρ : ρ < M)
    (g : ActualFamily xs T) (s : ℕ) (b : CoreFamily K) {a v : ℕ}
    (ha : b.val.start < a) (hv : v ≤ b.val.stop) :
    ((newerClosure K M ρ g s).filter (· ∈ Set.Ioo a v)).card ≤ (2 * M + 4) * 11 := by
  let Φ := insert b (univ.filter (fun G => (coreModel K).Nonleaf G ∧ (coreModel K).graph.Adj b G))
  have hΦ : Φ.card ≤ 3 := (card_insert_le _ _).trans (by
    have := nonleaf_adj_card_le_two hc b; omega)
  have h := newerClosure_count hc hρ g s (Set.Ioo a v) Φ (by
    intro G hn t ht hGt htG
    by_cases hGb : G = b
    · rw [hGb]; exact mem_insert_self _ _
    · refine mem_insert_of_mem (mem_filter.mpr ⟨mem_univ _, hn, ?_⟩)
      have hGo := G.val.owner_bounds
      have ht1 := ht.1
      have ht2 := ht.2
      exact ⟨Ne.symm hGb, show b.val.start < G.val.stop by omega,
        show G.val.start < b.val.stop by omega⟩)
  calc
    ((newerClosure K M ρ g s).filter (· ∈ Set.Ioo a v)).card ≤ (2 * M + 4) * (2 * Φ.card + 5) := by
      refine (card_le_card (fun x hx => ?_)).trans h
      simp only [mem_filter] at hx ⊢
      exact hx
    _ ≤ (2 * M + 4) * (2 * 3 + 5) := Nat.mul_le_mul_left _ (by omega)
    _ = _ := by ring

section Landings

variable (K) (M ρ : ℕ) (g e : ActualFamily xs T)

/-- Times of the newer closure in the active interval of `e`. -/
def landingSet (s : ℕ) : Finset ℕ :=
  (newerClosure K M ρ g s).filter (fun v => e.owner < v ∧ v ≤ e.stop)

/-- A core step between two landing times. -/
def IsLandingStep (v : ℕ) (b : CoreFamily K) : Prop :=
  b.val.shadow v ≠ v ∧ e.owner < b.val.shadow v ∧ b.val.shadow v ≤ e.stop

def stepJump (x : ℕ → ℕ) (v : ℕ) (b : CoreFamily K) : ℕ :=
  x (e.shadow (b.val.shadow v)) - x (e.shadow v)

/-- The largest raw jump of a core step between landing times. -/
def stepMax (x : ℕ → ℕ) (s : ℕ) : ℕ :=
  (((landingSet K M ρ g e s) ×ˢ (phaseSurvivors K M ρ)).filter
    (fun p => IsLandingStep K e p.1 p.2)).sup (fun p => stepJump K e x p.1 p.2)

/-- Landing times not reached by a core step from another landing time. -/
def landingStarts (s : ℕ) : Finset ℕ :=
  (landingSet K M ρ g e s).filter (fun v => ¬ ∃ u ∈ landingSet K M ρ g e s,
    ∃ b ∈ phaseSurvivors K M ρ, b.val.shadow u ≠ u ∧ b.val.shadow u = v)

theorem stepJump_le_stepMax (x : ℕ → ℕ) {s u : ℕ} {b : CoreFamily K}
    (hu : u ∈ landingSet K M ρ g e s) (hb : b ∈ phaseSurvivors K M ρ)
    (hstep : IsLandingStep K e u b) :
    stepJump K e x u b ≤ stepMax K M ρ g e x s := by
  have hmem : (u, b) ∈ ((landingSet K M ρ g e s) ×ˢ (phaseSurvivors K M ρ)).filter
      (fun p => IsLandingStep K e p.1 p.2) := by
    simp only [mem_filter, mem_product]
    exact ⟨⟨hu, hb⟩, hstep⟩
  have h := Finset.le_sup (f := fun p : ℕ × CoreFamily K => stepJump K e x p.1 p.2) hmem
  exact h

end Landings

/-- Core families whose spans contain the edge after the stop of `e`: at most two. -/
theorem crossing_card (hc : HasSpanColoring K 2) (e : ActualFamily xs T) :
    (univ.filter (fun G : CoreFamily K => G.val.start < e.stop ∧ e.stop < G.val.stop)).card ≤ 2 := by
  have h := card_le_card_of_injOn (coreColor hc)
    (s := univ.filter (fun G : CoreFamily K => G.val.start < e.stop ∧ e.stop < G.val.stop))
    (t := range 2) (fun q _ => mem_range.mpr (coreColor_lt hc q)) ?_
  · simpa only [card_range] using h
  · intro a ha b hb he
    have ha' := (mem_filter.mp ha).2
    have hb' := (mem_filter.mp hb).2
    exact core_eq_of_same_color hc (t := e.stop + 1) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ he

theorem landingStarts_card (hc : HasSpanColoring K 2) {M ρ : ℕ} (hρ : ρ < M)
    (g e : ActualFamily xs T) (s : ℕ) :
    (landingStarts K M ρ g e s).card ≤ 5 * (2 * M + 4) := by
  classical
  set P := landingSet K M ρ g e s with hPdef
  set R := newerRoots K M ρ g s with hRdef
  let Cross := univ.filter (fun G : CoreFamily K => G.val.start < e.stop ∧ e.stop < G.val.stop)
  have hentry : ∀ r ∈ R, ((landingStarts K M ρ g e s).filter
      (fun v => v ∈ phaseOrbit K M ρ r ∧ v ≠ r)).card ≤ 4 := by
    intro r hr
    let X := (landingStarts K M ρ g e s).filter (fun v => v ∈ phaseOrbit K M ρ r ∧ v ≠ r)
    let w : ℕ → List (CoreFamily K) := fun v =>
      if h : v ∈ phaseOrbit K M ρ r then (exists_success_word hc hρ h).choose else []
    have hwv : ∀ v ∈ X, w v ≠ [] ∧ CoreSuccess (w v) r ∧ coreEndpoint (w v) r = v ∧
        ∀ a ∈ w v, a ∈ phaseSurvivors K M ρ := by
      intro v hv
      have hvo := ((mem_filter.mp hv).2).1
      have hvr := ((mem_filter.mp hv).2).2
      have hspec := (exists_success_word hc hρ hvo).choose_spec
      have hw : w v = (exists_success_word hc hρ hvo).choose := dite_eq_left hvo
      rw [hw]
      refine ⟨?_, hspec.2.1, hspec.2.2, hspec.1⟩
      intro hnil
      have := hspec.2.2
      rw [hnil] at this
      exact hvr this.symm
    have hlast : ∀ v ∈ X, ∀ G, (w v).getLast? = some G → G ∈ Cross := by
      intro v hv G hG
      obtain ⟨p, hp⟩ : ∃ p, w v = p ++ [G] := by
        obtain ⟨p, a, hpa⟩ := exists_eq_append_singleton (hwv v hv).1
        rw [hpa] at hG
        simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or,
          Option.some_inj] at hG
        exact ⟨p, by rw [hpa, hG]⟩
      have hs := (hwv v hv).2.1
      rw [hp] at hs
      have hstep := (coreSuccess_append_singleton p G r).mp hs
      have hend := (hwv v hv).2.2.1
      rw [hp, coreEndpoint_append_singleton] at hend
      have hbG := G.val.shadow_active_bounds
        ((G.val.shadow_ne_self_iff (coreEndpoint p r)).mp hstep.2)
      have hstart := (mem_filter.mp hv).1
      have hvP : v ∈ P := (mem_filter.mp hstart).1
      have hvact := (mem_filter.mp hvP).2
      have huo : coreEndpoint p r ∈ phaseOrbit K M ρ r := by
        have : coreEndpoint p r ∈ FiniteOrbits.wordOrbit (phaseSurvivors K M ρ) coreAction r :=
          ⟨p, fun a ha => (hwv v hv).2.2.2 a (by rw [hp]; exact List.mem_append_left _ ha),
            rfl⟩
        rw [phase_orbit_exact hc hρ] at this
        exact_mod_cast this
      have huV : coreEndpoint p r ∈ newerClosure K M ρ g s := mem_biUnion.mpr ⟨r, hr, huo⟩
      have hnotact : ¬ (e.owner < coreEndpoint p r ∧ coreEndpoint p r ≤ e.stop) := by
        intro hact
        apply (mem_filter.mp hstart).2
        refine ⟨coreEndpoint p r, mem_filter.mpr ⟨huV, hact⟩, G, ?_, hstep.2, hend⟩
        exact (hwv v hv).2.2.2 G (by rw [hp]; simp)
      rw [hend] at hbG
      refine mem_filter.mpr ⟨mem_univ _, by omega, ?_⟩
      have hvu : v < coreEndpoint p r := by
        rw [← hend]
        exact (G.val.shadowAction.apply_le _).lt_of_ne (by
          simpa [ActualFamily.shadow] using hstep.2)
      omega
    have h := core_root_count_last hc r X Cross w
      (fun v hv => ⟨(hwv v hv).1, (hwv v hv).2.1, (hwv v hv).2.2.1⟩) hlast
    calc
      _ ≤ 2 * Cross.card := h
      _ ≤ 2 * 2 := Nat.mul_le_mul_left _ (crossing_card hc e)
      _ = 4 := by norm_num
  have hsub : landingStarts K M ρ g e s ⊆
      R ∪ R.biUnion (fun r => (landingStarts K M ρ g e s).filter
        (fun v => v ∈ phaseOrbit K M ρ r ∧ v ≠ r)) := by
    intro v hv
    have hvP : v ∈ P := (mem_filter.mp hv).1
    obtain ⟨r, hr, hvr⟩ := mem_biUnion.mp (mem_filter.mp hvP).1
    by_cases h : v = r
    · exact mem_union_left _ (h ▸ hr)
    · exact mem_union_right _ (mem_biUnion.mpr ⟨r, hr, mem_filter.mpr ⟨hv, hvr, h⟩⟩)
  calc
    _ ≤ _ := card_le_card hsub
    _ ≤ R.card + ∑ r ∈ R, ((landingStarts K M ρ g e s).filter
          (fun v => v ∈ phaseOrbit K M ρ r ∧ v ≠ r)).card :=
      (card_union_le _ _).trans (Nat.add_le_add_left card_biUnion_le _)
    _ ≤ R.card + ∑ _r ∈ R, 4 := Nat.add_le_add_left (sum_le_sum hentry) _
    _ = 5 * R.card := by rw [sum_const, smul_eq_mul]; ring
    _ ≤ 5 * (2 * M + 4) := Nat.mul_le_mul_left _ (newerRoots_card hc M ρ g s)

/-- **Chains of landings.** Every landing time is reached from a start by a
successful survivor word through landing times, each step adding at most the
largest raw jump. -/
theorem landing_cover (hc : HasSpanColoring K 2) {M ρ : ℕ} (hρ : ρ < M)
    (g e : ActualFamily xs T) (x : ℕ → ℕ) (hx : MonotoneOn x (Set.Ioc e.start e.owner))
    (s : ℕ) :
    ∀ v ∈ landingSet K M ρ g e s, ∃ s₀ ∈ landingStarts K M ρ g e s,
      x (e.shadow s₀) ≤ x (e.shadow v) ∧
        x (e.shadow v) ≤ x (e.shadow s₀) + (M + 1) * stepMax K M ρ g e x s := by
  classical
  set P := landingSet K M ρ g e s
  set Γ := stepMax K M ρ g e x s
  have chain : ∀ n, ∀ v ∈ P, e.stop - v = n → ∃ s₀ ∈ landingStarts K M ρ g e s,
      ∃ w : List (CoreFamily K), (∀ a ∈ w, a ∈ phaseSurvivors K M ρ) ∧ CoreSuccess w s₀ ∧
        coreEndpoint w s₀ = v ∧ x (e.shadow v) ≤ x (e.shadow s₀) + w.length * Γ := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro v hv hn
      by_cases hst : v ∈ landingStarts K M ρ g e s
      · exact ⟨v, hst, [], by simp, by simp [CoreSuccess, Action.success], rfl, by simp⟩
      · have hpred : ∃ u ∈ P, ∃ b ∈ phaseSurvivors K M ρ, b.val.shadow u ≠ u ∧
            b.val.shadow u = v := by
          by_contra hno
          exact hst (mem_filter.mpr ⟨hv, hno⟩)
        obtain ⟨u, hu, b, hb, hbu, rfl⟩ := hpred
        have hlt : b.val.shadow u < u := (b.val.shadowAction.apply_le u).lt_of_ne hbu
        have huact := (mem_filter.mp hu).2
        have hvact := (mem_filter.mp hv).2
        obtain ⟨s₀, hs₀, w, hw, hsw, hew, hraw⟩ := ih (e.stop - u) (by omega) u hu rfl
        refine ⟨s₀, hs₀, w ++ [b], ?_, ?_, ?_, ?_⟩
        · intro a ha
          rcases List.mem_append.mp ha with h | h
          · exact hw a h
          · simp only [List.mem_singleton] at h; exact h ▸ hb
        · exact (coreSuccess_append_singleton w b s₀).mpr ⟨hsw, by rw [hew]; exact hbu⟩
        · rw [coreEndpoint_append_singleton, hew]
        · have hjump : stepJump K e x u b ≤ Γ :=
            stepJump_le_stepMax K M ρ g e x hu hb ⟨hbu, hvact.1, hvact.2⟩
          have hsplit : x (e.shadow (b.val.shadow u)) ≤ x (e.shadow u) + stepJump K e x u b := by
            unfold stepJump; omega
          rw [List.length_append, List.length_singleton, Nat.add_mul, Nat.one_mul]
          omega
  intro v hv
  obtain ⟨s₀, hs₀, w, hw, hsw, hew, hraw⟩ := chain _ v hv rfl
  have hlen := phase_success_length hc hρ w hw hsw
  have hs₀P := (mem_filter.mp hs₀).1
  have hvs : v ≤ s₀ := by rw [← hew]; exact Action.endpoint_le _ _
  refine ⟨s₀, hs₀, raw_landing_antitone e x hx (mem_filter.mp hv).2 (mem_filter.mp hs₀P).2 hvs,
    hraw.trans ?_⟩
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hlen) _

end
end SourceCovers
