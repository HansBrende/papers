import SourceCovers.ClippedShadows
import LeanMachine.SourceBank

/-! Ordered exceptional shadows and covers by complete core orbits.
The core bank is used only through its exact value set. Its slots need not
represent the same core word at different times. Exceptions may overlap the
core and repeat in the list; a successful word nevertheless has strictly
decreasing owners. -/

namespace SourceCovers

open Classical Finset LeanMachine.MonotonePatches LeanMachine.SourceBank

noncomputable section

variable {k T : ℕ} {xs : Fin k → ℕ → ℤ}

/-- A geometry-fixed decreasing-owner enumeration; ties retain the order
chosen for the finite list. -/
def orderedExceptions (E : Finset (ActualFamily xs T)) : List (ActualFamily xs T) :=
  E.toList.mergeSort (fun a b => decide (b.owner ≤ a.owner))

theorem orderedExceptions_toFinset (E : Finset (ActualFamily xs T)) :
    (orderedExceptions E).toFinset = E := by
  unfold orderedExceptions
  ext q
  simp only [List.mem_toFinset, List.mem_mergeSort, mem_toList]

theorem orderedExceptions_length (E : Finset (ActualFamily xs T)) :
    (orderedExceptions E).length = E.card := by simp [orderedExceptions]

theorem orderedExceptions_pairwise (E : Finset (ActualFamily xs T)) :
    (orderedExceptions E).Pairwise (fun a b => b.owner ≤ a.owner) := by
  simpa only [orderedExceptions, decide_eq_true_eq] using
    List.pairwise_mergeSort (le := fun a b : ActualFamily xs T => decide (b.owner ≤ a.owner))
      (fun _ _ _ => by simp only [decide_eq_true_eq]; omega)
      (fun _ _ => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) E.toList

/-- Every owner used successfully precedes the starting time. -/
theorem shadow_success_owner_lt (w : List (ActualFamily xs T)) {t : ℕ}
    (hs : t ∈ shadowSuccess w) : ∀ q ∈ w, q.owner < t := by
  induction w generalizing t with
  | nil => simp
  | cons a w ih =>
    have h := (shadow_success_cons_iff a w t).mp hs
    have ha := a.shadow_active_bounds ((a.shadow_ne_self_iff t).mp h.1)
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact ha.2.2.1
    · exact (ih h.2 q hq).trans_le (ha.2.1.trans ha.2.2.1.le)

/-- Successful exceptions follow decreasing owners, without any chosen order
being imposed on the original word. Equal-owner actions cannot both act. -/
theorem shadow_success_owner_pairwise (w : List (ActualFamily xs T)) {t : ℕ}
    (hs : t ∈ shadowSuccess w) : w.Pairwise (fun a b => b.owner < a.owner) := by
  induction w generalizing t with
  | nil => simp
  | cons a w ih =>
    have h := (shadow_success_cons_iff a w t).mp hs
    have ha := a.shadow_active_bounds ((a.shadow_ne_self_iff t).mp h.1)
    exact List.pairwise_cons.mpr
      ⟨fun q hq => (shadow_success_owner_lt w h.2 q hq).trans_le ha.2.1, ih h.2⟩

theorem shadowOrbit_mono {K L : Finset (ActualFamily xs T)} (h : K ⊆ L) (t : ℕ) :
    shadowOrbit K t ⊆ shadowOrbit L t :=
  fun _ hu => LeanMachine.FiniteOrbits.wordOrbit_mono ActualFamily.shadowAction h hu

theorem shadowOrbit_trans {K : Finset (ActualFamily xs T)} {t u v : ℕ}
    (hu : u ∈ shadowOrbit K t) (hv : v ∈ shadowOrbit K u) :
    v ∈ shadowOrbit K t := LeanMachine.FiniteOrbits.wordOrbit_trans hu hv

/-- A bank represents a core exactly, including every stopping point. -/
def ExactCoreBank (K : Finset (ActualFamily xs T)) (B : Bank) : Prop :=
  ∀ t, (values B t : Set ℕ) = shadowOrbit K t

theorem ordered_values_cons (B : Bank) (f : Action) (fs : List Action) (t u : ℕ) :
    u ∈ values (ordered B (f :: fs)) t ↔
      u ∈ values (ordered B fs) t ∨
        ∃ v ∈ values B t, u ∈ values (ordered B fs) (f.apply v) := by
  simp only [mem_values, ordered, List.mem_append, mem_compose]
  constructor
  · rintro ⟨a, ha, he⟩
    rcases ha with ha | ⟨b, hb, c, ⟨d, hd, e, heB, rfl⟩, rfl⟩
    · exact Or.inl ⟨a, ha, he⟩
    · have hd' : d = f.apply := by simpa using hd
      subst d
      exact Or.inr ⟨e t, ⟨e, heB, rfl⟩, b, hb, he⟩
  · rintro (⟨a, ha, he⟩ | ⟨v, ⟨a, ha, rfl⟩, b, hb, he⟩)
    · exact ⟨a, Or.inl ha, he⟩
    · exact ⟨b ∘ (f.apply ∘ a),
        Or.inr ⟨b, hb, f.apply ∘ a, ⟨f.apply, by simp, a, ha, rfl⟩, rfl⟩, he⟩

/-- Every ordered-bank value is genuinely reached by a word of shadows. -/
theorem ordered_values_sound {K : Finset (ActualFamily xs T)} {B : Bank}
    (hB : ExactCoreBank K B) (E : List (ActualFamily xs T)) (t : ℕ) :
    (values (ordered B (E.map ActualFamily.shadowAction)) t : Set ℕ) ⊆
      shadowOrbit (K ∪ E.toFinset) t := by
  induction E generalizing t with
  | nil => simpa [ordered] using (hB t).subset
  | cons e E ih =>
    intro u hu
    rcases (ordered_values_cons B e.shadowAction _ t u).mp hu with hu | ⟨v, hv, hu⟩
    · exact shadowOrbit_mono (by simp) t (ih t hu)
    · have hv' : v ∈ shadowOrbit (K ∪ (e :: E).toFinset) t :=
        shadowOrbit_mono subset_union_left t ((hB t).subset hv)
      have he : e.shadow v ∈ shadowOrbit (K ∪ (e :: E).toFinset) v :=
        ⟨[e], by simp, rfl⟩
      exact shadowOrbit_trans (shadowOrbit_trans hv' he)
        (shadowOrbit_mono (by simp) _ (ih _ hu))

/-- A successful word can be represented using any decreasing enumeration of
the exceptions. Only its core segments are replaced by bank slots. -/
theorem successful_endpoint_mem_ordered {K : Finset (ActualFamily xs T)} {B : Bank}
    (hB : ExactCoreBank K B) (E : List (ActualFamily xs T))
    (hE : E.Pairwise (fun a b => b.owner ≤ a.owner))
    (w : List (ActualFamily xs T)) (hw : ∀ q ∈ w, q ∈ K ∪ E.toFinset)
    (t : ℕ) (hs : t ∈ shadowSuccess w) :
    shadowEndpoint w t ∈ values (ordered B (E.map ActualFamily.shadowAction)) t := by
  induction E generalizing w t with
  | nil =>
    apply (hB t).superset
    exact ⟨w, by simpa using hw, rfl⟩
  | cons e E ih =>
    have hE' := List.pairwise_cons.mp hE
    apply (ordered_values_cons B e.shadowAction _ t _).mpr
    by_cases he : e ∈ w
    · obtain ⟨a, b, rfl⟩ := List.mem_iff_append.mp he
      have hp := List.pairwise_append.mp (shadow_success_owner_pairwise _ hs)
      have hb := List.pairwise_cons.mp hp.2.1
      have haK : ∀ q ∈ a, q ∈ K := by
        intro q hq
        rcases mem_union.mp (hw q (List.mem_append_left _ hq)) with hqK | hqE
        · exact hqK
        · have hlt := hp.2.2 q hq e (List.mem_cons_self ..)
          rcases List.mem_cons.mp (List.mem_toFinset.mp hqE) with rfl | hqE
          · exact (Nat.lt_irrefl _ hlt).elim
          · exact (not_lt_of_ge (hE'.1 q hqE) hlt).elim
      have hbK : ∀ q ∈ b, q ∈ K ∪ E.toFinset := by
        intro q hq
        rcases mem_union.mp (hw q (List.mem_append_right _ (List.mem_cons_of_mem _ hq))) with hqK | hqE
        · exact mem_union_left _ hqK
        · rcases List.mem_cons.mp (List.mem_toFinset.mp hqE) with rfl | hqE
          · exact (Nat.lt_irrefl _ (hb.1 q hq)).elim
          · exact mem_union_right _ (List.mem_toFinset.mpr hqE)
      have hs' := (Action.success_append (a.map ActualFamily.shadowAction)
        ((e :: b).map ActualFamily.shadowAction) t).mp
          (by simpa only [shadowSuccess, List.map_append] using hs)
      have hsb := (shadow_success_cons_iff e b (shadowEndpoint a t)).mp hs'.2
      refine Or.inr ⟨shadowEndpoint a t, (hB t).superset ⟨a, haK, rfl⟩, ?_⟩
      have hbmem := ih hE'.2 b hbK (e.shadow (shadowEndpoint a t)) hsb.2
      simpa only [shadowEndpoint, List.map_append, Action.endpoint_append,
        List.map_cons, Action.endpoint, ActualFamily.shadow] using hbmem
    · apply Or.inl
      apply ih hE'.2 w _ t hs
      intro q hq
      rcases mem_union.mp (hw q hq) with hqK | hqE
      · exact mem_union_left _ hqK
      · rcases List.mem_cons.mp (List.mem_toFinset.mp hqE) with rfl | hqE
        · exact (he hq).elim
        · exact mem_union_right _ (List.mem_toFinset.mpr hqE)

/-- Exactness for arbitrary words, including inactive actions and repeated
stops. No disjointness between the core and exception list is needed. -/
theorem ordered_values_exact {K : Finset (ActualFamily xs T)} {B : Bank}
    (hB : ExactCoreBank K B) (E : List (ActualFamily xs T))
    (hE : E.Pairwise (fun a b => b.owner ≤ a.owner)) (t : ℕ) :
    (values (ordered B (E.map ActualFamily.shadowAction)) t : Set ℕ) =
      shadowOrbit (K ∪ E.toFinset) t := by
  apply Set.Subset.antisymm (ordered_values_sound hB E t)
  rintro u ⟨w, hw, rfl⟩
  obtain ⟨v, hv, hs, he⟩ := LeanMachine.FiniteOrbits.reduce_word ActualFamily.shadowAction w t
  change shadowEndpoint v t = shadowEndpoint w t at he
  rw [← he]
  exact successful_endpoint_mem_ordered hB E hE v (fun q hq => hw q (hv.subset hq)) t hs

/-- Starting vertices of the final complete core orbits. The recurrence
retains all core choices before the next exceptional step. -/
def terminalCoreRoots (B : Bank) : List (ActualFamily xs T) → ℕ → Finset ℕ
  | [], t => {t}
  | e :: E, t => terminalCoreRoots B E t ∪
      (values B t).biUnion (fun v => terminalCoreRoots B E (e.shadow v))

theorem ordered_values_terminal_cover (B : Bank) (E : List (ActualFamily xs T)) (t : ℕ) :
    values (ordered B (E.map ActualFamily.shadowAction)) t =
      (terminalCoreRoots B E t).biUnion (values B) := by
  induction E generalizing t with
  | nil => simp [ordered, terminalCoreRoots]
  | cons e E ih =>
    have hcons : values (ordered B ((e :: E).map ActualFamily.shadowAction)) t =
        values (ordered B (E.map ActualFamily.shadowAction)) t ∪
          (values B t).biUnion (fun v => values (ordered B (E.map ActualFamily.shadowAction)) (e.shadow v)) := by
      ext u
      simp only [List.map_cons, ordered_values_cons, mem_union, mem_biUnion,
        ActualFamily.shadow]
    rw [hcons]
    simp_rw [ih]
    simp only [terminalCoreRoots, union_biUnion, biUnion_biUnion]

theorem terminalCoreRoots_card {B : Bank} {ell : ℕ}
    (hB : ∀ t, (values B t).card ≤ ell) (E : List (ActualFamily xs T)) (t : ℕ) :
    (terminalCoreRoots B E t).card ≤ (ell + 1) ^ E.length := by
  induction E generalizing t with
  | nil => simp [terminalCoreRoots]
  | cons e E ih =>
    calc
      _ ≤ (terminalCoreRoots B E t).card +
          ∑ v ∈ values B t, (terminalCoreRoots B E (e.shadow v)).card :=
        (card_union_le ..).trans (Nat.add_le_add_left (card_biUnion_le) _)
      _ ≤ (ell + 1) ^ E.length + ∑ _v ∈ values B t, (ell + 1) ^ E.length := by
        exact Nat.add_le_add (ih t) (sum_le_sum (fun v _ => ih (e.shadow v)))
      _ ≤ (ell + 1) ^ (e :: E).length := by
        simp only [sum_const, smul_eq_mul, List.length_cons, pow_succ]
        calc
          _ ≤ (ell + 1) ^ E.length + ell * (ell + 1) ^ E.length :=
            Nat.add_le_add_left (Nat.mul_le_mul_right _ (hB t)) _
          _ = _ := by ring

/-- The complete enlarged orbit is a union of at most `(ell + 1)^q`
complete core orbits, with no truncation of any core continuation. -/
theorem exceptional_orbit_core_cover {K : Finset (ActualFamily xs T)} {B : Bank}
    (hB : ExactCoreBank K B) (E : List (ActualFamily xs T))
    (hE : E.Pairwise (fun a b => b.owner ≤ a.owner)) {ell : ℕ}
    (hcard : ∀ t, (values B t).card ≤ ell) (t : ℕ) :
    ∃ R : Finset ℕ, R.card ≤ (ell + 1) ^ E.length ∧
      shadowOrbit (K ∪ E.toFinset) t = ⋃ r ∈ R, shadowOrbit K r := by
  refine ⟨terminalCoreRoots B E t, terminalCoreRoots_card hcard E t, ?_⟩
  rw [← ordered_values_exact hB E hE t, ordered_values_terminal_cover]
  ext u
  simp only [mem_coe, mem_biUnion, Set.mem_iUnion, exists_prop]
  exact exists_congr (fun r => and_congr_right (fun _ => Set.ext_iff.mp (hB r) u))

theorem ordered_values_card {B : Bank} {ell : ℕ}
    (hB : ∀ t, (values B t).card ≤ ell) (E : List (ActualFamily xs T)) (t : ℕ) :
    (values (ordered B (E.map ActualFamily.shadowAction)) t).card ≤
      ell * (ell + 1) ^ E.length := by
  rw [ordered_values_terminal_cover]
  calc
    _ ≤ ∑ r ∈ terminalCoreRoots B E t, (values B r).card := card_biUnion_le
    _ ≤ ∑ _r ∈ terminalCoreRoots B E t, ell := sum_le_sum (fun r _ => hB r)
    _ ≤ ell * (ell + 1) ^ E.length := by
      simp only [sum_const, smul_eq_mul]
      exact (Nat.mul_le_mul_right ell (terminalCoreRoots_card hB E t)).trans_eq (Nat.mul_comm ..)

end
end SourceCovers
