import SourceCovers.FamilyAccounting
import LeanMachine.MonotonePatches

/-!
# Actual clipped shadows and their variation

The held value is the owner's time until the first hop end, then the start
of the latest ended hop. Clipping at `start + 1` removes only the paid outer
lower endpoint. Reuse the shared monotone-patch bounds for words and packings.
-/

namespace SourceCovers

open Classical Finset BoundedNesting LeanMachine.MonotonePatches

export LeanMachine.MonotonePatches (variation_comp_le_crossings exists_sharp_patch)

noncomputable section

variable {k T : ℕ} {xs : Fin k → ℕ → ℤ}

namespace ActualFamily

theorem nonempty (q : ActualFamily xs T) : q.hops.Nonempty := fam_nonempty _ _ _ q

theorem owner_bounds (q : ActualFamily xs T) : q.start < q.owner ∧ q.owner < q.stop := by
  obtain ⟨η, hη⟩ := q.nonempty
  have ho := family_owner_inside q hη
  have hb := fam_bounds hη
  exact ⟨hb.1.trans_lt ho.1, ho.2.trans_le hb.2⟩

/-- Earlier hop ends have larger starts; unfinished hops contribute the owner. -/
def held (q : ActualFamily xs T) (t : ℕ) : ℕ :=
  q.hops.inf' q.nonempty (fun η => if η.2.2 ≤ t then η.2.1 else q.owner)

theorem held_le_owner (q : ActualFamily xs T) (t : ℕ) : q.held t ≤ q.owner := by
  obtain ⟨η, hη⟩ := q.nonempty
  have h := inf'_le (fun η => if η.2.2 ≤ t then η.2.1 else q.owner) hη
  have ho := family_owner_inside q hη
  change q.held t ≤ _ at h
  split_ifs at h <;> omega

theorem held_antitone (q : ActualFamily xs T) : Antitone q.held := by
  intro s t hst
  apply le_inf'
  intro η hη
  have h := inf'_le (fun η => if η.2.2 ≤ t then η.2.1 else q.owner) hη
  have ho := family_owner_inside q hη
  change q.held t ≤ _ at h
  split_ifs at h ⊢ <;> omega

theorem held_initial (q : ActualFamily xs T) (t : ℕ)
    (ht : ∀ η ∈ q.hops, t < η.2.2) : q.held t = q.owner := by
  apply inf'_eq_of_forall
  intro η hη
  simp [not_le.mpr (ht η hη)]

theorem held_constant (q : ActualFamily xs T) (s t : ℕ)
    (h : ∀ η ∈ q.hops, η.2.2 ≤ s ↔ η.2.2 ≤ t) : q.held s = q.held t := by
  apply inf'_congr q.nonempty rfl
  intro η hη
  simp only [h η hη]

/-- Nesting identifies the infimum with the actual hop start at every hop end. -/
theorem held_at_hop (hx : ∀ h, IsWalk (xs h)) (q : ActualFamily xs T)
    {η : Fin k × ℕ × ℕ} (hη : η ∈ q.hops) : q.held η.2.2 = η.2.1 := by
  apply le_antisymm
  · have h := inf'_le (fun η' => if η'.2.2 ≤ η.2.2 then η'.2.1 else q.owner) hη
    change q.held η.2.2 ≤ _ at h
    simpa only [ite_eq_left le_rfl] using h
  · apply le_inf'
    intro η' hη'
    by_cases he : η'.2.2 ≤ η.2.2
    · simp only [ite_eq_left he]
      by_cases hsame : η' = η
      · subst η'; exact le_rfl
      · have := family_hops_nested hx q hη' hη hsame
        omega
    · simp only [ite_eq_right he]
      exact (family_owner_inside q hη).1.le

/-- The held value clipped strictly above the paid outer lower endpoint. -/
def clipped (q : ActualFamily xs T) (t : ℕ) : ℕ := max (q.start + 1) (q.held t)

theorem clipped_bounds (q : ActualFamily xs T) (t : ℕ) :
    q.start < q.clipped t ∧ q.clipped t ≤ q.owner := by
  have h := q.held_le_owner t
  have ho := q.owner_bounds
  unfold clipped
  omega

theorem clipped_antitone (q : ActualFamily xs T) : Antitone q.clipped :=
  fun _ _ h => max_le_max_left _ (q.held_antitone h)

/-- The concrete shadow, viewed as an interval action. -/
def shadowAction (q : ActualFamily xs T) : Action where
  domain := Set.Ioc q.owner q.stop
  map := q.clipped
  connected := Set.ordConnected_Ioc
  monotone := Or.inr (q.clipped_antitone.antitoneOn _)
  decreases := fun t ht => (q.clipped_bounds t).2.trans_lt ht.1

def shadow (q : ActualFamily xs T) : ℕ → ℕ := q.shadowAction.apply

/-- The active interval is exactly the nonidentity set, not merely an overcover. -/
theorem shadow_ne_self_iff (q : ActualFamily xs T) (t : ℕ) :
    q.shadow t ≠ t ↔ q.owner < t ∧ t ≤ q.stop :=
  q.shadowAction.apply_ne_self_iff t

theorem shadow_active_bounds (q : ActualFamily xs T) {t : ℕ}
    (ht : q.owner < t ∧ t ≤ q.stop) :
    q.start < q.shadow t ∧ q.shadow t ≤ q.owner ∧ q.owner < t ∧ t ≤ q.stop := by
  simp only [shadow, q.shadowAction.apply_eq ht]
  exact ⟨(q.clipped_bounds t).1, (q.clipped_bounds t).2, ht⟩

theorem shadow_at_hop (hx : ∀ h, IsWalk (xs h)) (q : ActualFamily xs T)
    {η : Fin k × ℕ × ℕ} (hη : η ∈ q.hops) :
    q.shadow η.2.2 = max (q.start + 1) η.2.1 := by
  have ht : η.2.2 ∈ q.shadowAction.domain :=
    ⟨(family_owner_inside q hη).2, (fam_bounds hη).2⟩
  rw [shadow, q.shadowAction.apply_eq ht]
  change max _ (q.held _) = _
  rw [q.held_at_hop hx hη]

/-- Every actual hop with unpaid outer lower is represented exactly. -/
theorem shadow_exact (hx : ∀ h, IsWalk (xs h)) (q : ActualFamily xs T)
    {η : Fin k × ℕ × ℕ} (hη : η ∈ q.hops) (hunpaid : η.2.1 ≠ q.start) :
    q.shadow η.2.2 = η.2.1 := by
  rw [q.shadow_at_hop hx hη]
  have : q.start ≤ η.2.1 := (fam_bounds hη).1
  exact max_eq_right (by omega)

def shadowPatch (q : ActualFamily xs T) : Patch where
  left := q.start
  right := q.stop
  action := q.shadowAction
  domain_subset := fun _ ht => ⟨q.owner_bounds.1.trans ht.1, ht.2⟩
  mapsTo := fun t _ => ⟨(q.clipped_bounds t).1,
    (q.clipped_bounds t).2.trans q.owner_bounds.2.le⟩

end ActualFamily

def jointShadow (K : Finset (ActualFamily xs T)) : ℕ → ℕ :=
  Patch.pack K ActualFamily.shadowPatch

theorem jointShadow_eq_on (K : Finset (ActualFamily xs T))
    (hd : ∀ q ∈ K, ∀ q' ∈ K, q ≠ q' → Disjoint q.edges q'.edges)
    {q : ActualFamily xs T} (hq : q ∈ K) {t : ℕ} (ht : q.start < t ∧ t ≤ q.stop) :
    jointShadow K t = q.shadow t :=
  Patch.pack_eq_on K ActualFamily.shadowPatch hd hq ht

/-- The joint shadow costs at most three times any metric-valued path's variation. -/
theorem jointShadow_variation {X : Type*} [PseudoMetricSpace X]
    (Y : ℕ → X) (K : Finset (ActualFamily xs T))
    (hd : ∀ q ∈ K, ∀ q' ∈ K, q ≠ q' → Disjoint q.edges q'.edges) (n : ℕ) :
    variation (Y ∘ jointShadow K) n ≤ 3 * variation Y n :=
  variation_pack Y K ActualFamily.shadowPatch hd n

abbrev shadowEndpoint (w : List (ActualFamily xs T)) : ℕ → ℕ :=
  Action.endpoint (w.map ActualFamily.shadowAction)

/-- Complete closure under finite words, including the empty word. -/
def shadowOrbit (K : Finset (ActualFamily xs T)) (t : ℕ) : Set ℕ :=
  {u | ∃ w : List (ActualFamily xs T), (∀ q ∈ w, q ∈ K) ∧ shadowEndpoint w t = u}

theorem mem_shadowOrbit_self (K : Finset (ActualFamily xs T)) (t : ℕ) :
    t ∈ shadowOrbit K t := ⟨[], by simp, rfl⟩

abbrev shadowSuccess (w : List (ActualFamily xs T)) : Set ℕ :=
  Action.success (w.map ActualFamily.shadowAction)

/-- Success means every concrete shadow acts nontrivially, in the specified order. -/
theorem shadow_success_cons_iff (q : ActualFamily xs T) (w : List (ActualFamily xs T)) (t : ℕ) :
    t ∈ shadowSuccess (q :: w) ↔ q.shadow t ≠ t ∧ q.shadow t ∈ shadowSuccess w :=
  Action.success_cons_iff q.shadowAction (w.map ActualFamily.shadowAction) t

theorem shadow_word_structure (w : List (ActualFamily xs T)) :
    (shadowSuccess w).OrdConnected ∧ SignedMonotoneOn (shadowEndpoint w) (shadowSuccess w) ∧
      ∀ t, shadowEndpoint w t ≤ t :=
  ⟨(Action.success_structure _).1, (Action.success_structure _).2, Action.endpoint_le _⟩

abbrev successfulShadowWord (w : List (ActualFamily xs T)) : ℕ → ℕ :=
  Action.successfulMap (w.map ActualFamily.shadowAction)

/-- A whole successful word has factor three, independently of its length. -/
theorem shadow_word_variation {X : Type*} [PseudoMetricSpace X]
    (Y : ℕ → X) (w : List (ActualFamily xs T)) (n : ℕ) :
    variation (Y ∘ successfulShadowWord w) n ≤ 3 * variation Y n :=
  Action.variation_successfulMap Y _ n

end
end SourceCovers
