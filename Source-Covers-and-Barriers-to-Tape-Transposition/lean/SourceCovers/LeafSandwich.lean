import SourceCovers.SpineGeometry
import LeanMachine.SourceBank

/-! Four maps per spine slot suffice for the complete retained-core orbit:
an original packing leaf can occur only at either end of a successful word.
-/

namespace SourceCovers

open Classical Finset LeanMachine LeanMachine.MonotonePatches

noncomputable section

variable {k T : ℕ} {xs : Fin k → ℕ → ℤ}
variable {K : Finset (ActualFamily xs T)}

def packingSpines (hc : HasSpanColoring K 2) (M ρ : ℕ) : Finset (CoreFamily K) :=
  (phaseSurvivors K M ρ).filter (packingSpine hc)

theorem survivingSpine_image_univ (hc : HasSpanColoring K 2) (M ρ : ℕ) :
    (univ : Finset (SurvivingSpine hc M ρ)).image Subtype.val = packingSpines hc M ρ := by
  ext q
  simp only [mem_image, mem_univ, true_and, packingSpines, mem_filter]
  exact ⟨fun ⟨a, ha⟩ => ha ▸ a.property, fun h => ⟨⟨q, h⟩, rfl⟩⟩

theorem spine_orbit_subtype (hc : HasSpanColoring K 2) (M ρ t : ℕ) :
    FiniteOrbits.wordOrbit (packingSpines hc M ρ) coreAction t =
      FiniteOrbits.wordOrbit (univ : Finset (SurvivingSpine hc M ρ))
        (fun q => coreAction q.val) t := by
  simpa only [survivingSpine_image_univ, Function.comp_def] using
    FiniteOrbits.wordOrbit_image (univ : Finset (SurvivingSpine hc M ρ)) Subtype.val coreAction t

def packingLeafMap (hc : HasSpanColoring K 2) (M ρ : ℕ) : ℕ → ℕ :=
  Patch.pack (packingLeaves hc M ρ) (fun q => q.val.shadowPatch)

theorem packingLeafMap_eq (hc : HasSpanColoring K 2) {M ρ : ℕ}
    {q : CoreFamily K} (hq : q ∈ packingLeaves hc M ρ) {t : ℕ}
    (ht : t ∈ (coreAction q).domain) :
    packingLeafMap hc M ρ t = (coreAction q).apply t :=
  Patch.pack_eq_on _ _ (packing_leaves_separated hc M ρ) hq (q.val.shadowPatch.domain_subset ht)

theorem packingLeafMap_bounded (hc : HasSpanColoring K 2) (M ρ : ℕ) :
    SourceBank.Bounded [packingLeafMap hc M ρ] 3 := by
  intro X _ Y n
  simpa only [SourceBank.cost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero, packingLeafMap] using
    variation_pack Y _ _ (packing_leaves_separated hc M ρ) n

/-- Every internal member of a successful core word lies on the packing spine. -/
theorem core_success_middle_spine (hc : HasSpanColoring K 2) (w : List (CoreFamily K))
    {t : ℕ} (hs : t ∈ Action.success (w.map coreAction)) :
    ∀ q ∈ w.tail.dropLast, packingSpine hc q := by
  induction w generalizing t with
  | nil => simp
  | cons a w ih =>
    rcases w with _ | ⟨b, w⟩
    · simp
    rcases w with _ | ⟨c, w⟩
    · simp
    have hchain := core_success_chain (a :: b :: c :: w) hs
    have hn := core_success_nodup (a :: b :: c :: w) hs
    have hab := (List.isChain_cons_cons.mp hchain).1
    have hbc := (List.isChain_cons_cons.mp (List.isChain_cons_cons.mp hchain).2).1
    have hba : (coreModel K).Nonleaf b := ⟨a, c, hab.symm, hbc, by
      intro he; exact (List.nodup_cons.mp hn).1 (by simp [he])⟩
    have hi := ih hs.2
    simpa only [List.tail_cons, List.dropLast_cons_cons, List.mem_cons, forall_eq_or_imp] using
      And.intro (packingSpine_of_nonleaf hc hba) hi

def leafSandwich (B : SourceBank.Bank) (s : ℕ → ℕ) : SourceBank.Bank :=
  B ++ SourceBank.compose B [s] ++ SourceBank.compose [s] B ++
    SourceBank.compose [s] (SourceBank.compose B [s])

theorem mem_leafSandwich_values {B : SourceBank.Bank} {s : ℕ → ℕ} {t u : ℕ} :
    u ∈ SourceBank.values (leafSandwich B s) t ↔
      ∃ a ∈ B, u = a t ∨ u = a (s t) ∨ u = s (a t) ∨ u = s (a (s t)) := by
  simp only [SourceBank.mem_values, leafSandwich, List.mem_append,
    SourceBank.mem_compose, List.mem_singleton, exists_eq_left]
  aesop

theorem leafSandwich_length (B : SourceBank.Bank) (s : ℕ → ℕ) :
    (leafSandwich B s).length = 4 * B.length := by
  simp only [leafSandwich, List.length_append, SourceBank.compose_length,
    List.length_singleton, mul_one, one_mul]
  omega

theorem leafSandwich_bounded {B : SourceBank.Bank} {C : ℝ} {s : ℕ → ℕ}
    (hB : SourceBank.Bounded B C) (hs : SourceBank.Bounded [s] 3) (hC : 0 ≤ C) :
    SourceBank.Bounded (leafSandwich B s) (16 * C) := by
  have hBs : SourceBank.Bounded (SourceBank.compose B [s]) (3 * C) :=
    SourceBank.bounded_compose hs hB (by norm_num)
  have hsB : SourceBank.Bounded (SourceBank.compose [s] B) (C * 3) :=
    SourceBank.bounded_compose hB hs hC
  have hsBs : SourceBank.Bounded (SourceBank.compose [s] (SourceBank.compose B [s]))
      ((3 * C) * 3) :=
    SourceBank.bounded_compose hBs hs (mul_nonneg (by norm_num) hC)
  have h : SourceBank.Bounded (leafSandwich B s) (C + 3 * C + C * 3 + (3 * C) * 3) :=
    SourceBank.bounded_append
    (SourceBank.bounded_append (SourceBank.bounded_append hB hBs) hsB) hsBs
  have he : C + 3 * C + C * 3 + (3 * C) * 3 = 16 * C := by ring
  intro X _ Y n
  simpa only [he] using h Y n

open LeanMachine.FiniteOrbits (wordOrbit_mono wordOrbit_trans)

theorem packingLeafMap_mem_orbit (hc : HasSpanColoring K 2) (M ρ t : ℕ) :
    packingLeafMap hc M ρ t ∈ FiniteOrbits.wordOrbit (phaseSurvivors K M ρ) coreAction t := by
  rcases Patch.pack_cases (packingLeaves hc M ρ) (fun q => q.val.shadowPatch) t with
    he | ⟨q, hq, _, he⟩
  · exact ⟨[], by simp, he.symm⟩
  · exact ⟨[q], by simpa using (mem_filter.mp hq).1, he.symm⟩

variable {B : SourceBank.Bank} {hc : HasSpanColoring K 2} {M ρ : ℕ}

private theorem endpoint_dropLast_spine
    (hB : ∀ t u, u ∈ SourceBank.values B t ↔
      u ∈ FiniteOrbits.wordOrbit (packingSpines hc M ρ) coreAction t)
    (w : List (CoreFamily K)) (hw : ∀ q ∈ w, q ∈ phaseSurvivors K M ρ)
    (hm : ∀ q ∈ w.dropLast, packingSpine hc q) {t : ℕ}
    (hs : t ∈ Action.success (w.map coreAction)) :
    ∃ a ∈ B, Action.endpoint (w.map coreAction) t = a t ∨
      Action.endpoint (w.map coreAction) t = packingLeafMap hc M ρ (a t) := by
  by_cases he : w = []
  · subst w
    have hroot : t ∈ FiniteOrbits.wordOrbit (packingSpines hc M ρ) coreAction t :=
      ⟨[], by simp, rfl⟩
    obtain ⟨a, ha, hat⟩ := SourceBank.mem_values.mp ((hB t t).mpr hroot)
    exact ⟨a, ha, Or.inl hat.symm⟩
  let q := w.getLast he
  have hq : q ∈ w := List.getLast_mem he
  have hwq : w.dropLast ++ [q] = w := List.dropLast_append_getLast he
  by_cases hp : packingSpine hc q
  · have hall : ∀ a ∈ w, a ∈ packingSpines hc M ρ := by
      intro a ha
      refine mem_filter.mpr ⟨hw a ha, ?_⟩
      rw [← hwq] at ha
      rcases List.mem_append.mp ha with ha | ha
      · exact hm a ha
      · simpa only [List.mem_singleton.mp ha] using hp
    obtain ⟨a, ha, hat⟩ := SourceBank.mem_values.mp ((hB t _).mpr ⟨w, hall, rfl⟩)
    exact ⟨a, ha, Or.inl hat.symm⟩
  · have hprefix : Action.endpoint (w.dropLast.map coreAction) t ∈
        FiniteOrbits.wordOrbit (packingSpines hc M ρ) coreAction t :=
      ⟨w.dropLast, fun a ha => mem_filter.mpr ⟨hw a (List.mem_of_mem_dropLast ha), hm a ha⟩, rfl⟩
    obtain ⟨a, ha, hat⟩ := SourceBank.mem_values.mp ((hB t _).mpr hprefix)
    have hs' : t ∈ Action.success (w.dropLast.map coreAction ++ [coreAction q]) := by
      rw [← hwq, List.map_append] at hs
      exact hs
    have hlast := (Action.success_append _ _ _).mp hs'
    have hleaf := packingLeafMap_eq hc (mem_filter.mpr ⟨hw q hq, hp⟩) hlast.2.1
    refine ⟨a, ha, Or.inr ?_⟩
    calc
      _ = Action.endpoint ((w.dropLast ++ [q]).map coreAction) t := by rw [hwq]
      _ = (coreAction q).apply (Action.endpoint (w.dropLast.map coreAction) t) := by
        rw [List.map_append, Action.endpoint_append]; rfl
      _ = packingLeafMap hc M ρ (a t) := by rw [hat, hleaf]

/-- Exactness is pointwise. Spine slots need not be represented by one word
independent of the starting time. -/
theorem leafSandwich_exact
    (hB : ∀ t u, u ∈ SourceBank.values B t ↔
      u ∈ FiniteOrbits.wordOrbit (packingSpines hc M ρ) coreAction t) (t u : ℕ) :
    u ∈ SourceBank.values (leafSandwich B (packingLeafMap hc M ρ)) t ↔
      u ∈ FiniteOrbits.wordOrbit (phaseSurvivors K M ρ) coreAction t := by
  constructor
  · intro hu
    obtain ⟨a, ha, he⟩ := mem_leafSandwich_values.mp hu
    have hsp (v : ℕ) : a v ∈ FiniteOrbits.wordOrbit (phaseSurvivors K M ρ) coreAction v :=
      wordOrbit_mono _ (filter_subset _ _) ((hB v _).mp
        (SourceBank.mem_values.mpr ⟨a, ha, rfl⟩))
    rcases he with rfl | rfl | rfl | rfl
    · exact hsp t
    · exact wordOrbit_trans (packingLeafMap_mem_orbit hc M ρ t) (hsp _)
    · exact wordOrbit_trans (hsp t) (packingLeafMap_mem_orbit hc M ρ _)
    · exact wordOrbit_trans (wordOrbit_trans (packingLeafMap_mem_orbit hc M ρ t) (hsp _))
        (packingLeafMap_mem_orbit hc M ρ _)
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨v, hv, hs, he⟩ := FiniteOrbits.reduce_word coreAction w t
    have hv' : ∀ q ∈ v, q ∈ phaseSurvivors K M ρ := fun q hq => hw q (hv.subset hq)
    rw [← he]
    apply mem_leafSandwich_values.mpr
    rcases v with _ | ⟨q, v⟩
    · obtain ⟨a, ha, hat | hat⟩ := endpoint_dropLast_spine hB [] hv' (by simp) hs
      · exact ⟨a, ha, Or.inl hat⟩
      · exact ⟨a, ha, Or.inr (Or.inr (Or.inl hat))⟩
    have hmiddle := core_success_middle_spine hc (q :: v) hs
    by_cases hq : packingSpine hc q
    · have hall : ∀ a ∈ (q :: v).dropLast, packingSpine hc a := by
        rcases v with _ | ⟨r, v⟩
        · simp
        · simpa only [List.tail_cons, List.dropLast_cons_cons, List.mem_cons, forall_eq_or_imp] using
            And.intro hq hmiddle
      obtain ⟨a, ha, hat | hat⟩ := endpoint_dropLast_spine hB (q :: v) hv' hall hs
      · exact ⟨a, ha, Or.inl hat⟩
      · exact ⟨a, ha, Or.inr (Or.inr (Or.inl hat))⟩
    · have hleaf := packingLeafMap_eq hc
        (mem_filter.mpr ⟨hv' q (List.mem_cons_self ..), hq⟩) hs.1
      obtain ⟨a, ha, hat | hat⟩ := endpoint_dropLast_spine hB v
        (fun r hr => hv' r (List.mem_cons_of_mem q hr)) hmiddle hs.2
      · exact ⟨a, ha, Or.inr (Or.inl (by simpa only [hleaf, List.map_cons, Action.endpoint] using hat))⟩
      · exact ⟨a, ha, Or.inr (Or.inr (Or.inr (by
          simpa only [hleaf, List.map_cons, Action.endpoint] using hat)))⟩

end
end SourceCovers
