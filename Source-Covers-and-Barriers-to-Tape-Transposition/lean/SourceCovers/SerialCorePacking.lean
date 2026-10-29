import SourceCovers.SerialParameters
import LeanMachine.FractionalCover

set_option autoImplicit false

/-! Every complete core orbit meets at most one nonzero target other than
the early held-owner value. This applies to arbitrary seeds and arbitrary
later families, without a span coloring or a phase hypothesis. -/

namespace SourceCovers.SerialGeometry.Parameters

open Classical Finset LeanMachine LeanMachine.ScheduledExcursion
noncomputable section

variable (P : Parameters) {k T : ℕ} {xs : Fin k → ℕ → ℤ}
  (head : Fin k) (hx : xs head = NativeExcursion.walk P.early)
  (hT : P.early.arrive 0 < T)

local notation "H" => NativeExcursion.family P.early head hx hT

theorem raw_owner : P.raw P.length = P.length - 2 := by
  have := P.length_pos
  dsimp [raw]
  omega

theorem early_shadow_held {t : ℕ} (ht : P.length < t) (hu : t ≤ 2 * P.length) :
    (H).shadow t = P.length := by
  have hh := NativeExcursion.family_shadow_held P.early head hx hT
    (show P.early.peak < t by simpa using ht) (fun i => by
      rw [P.early_arrive]
      have := i.isLt
      omega)
  simpa using hh

theorem early_shadow_return {t : ℕ} (ht : 2 * P.length < t) (hu : t ≤ 3 * P.length) :
    (H).shadow t = max 1 (3 * P.length - t) := by
  let i : Fin P.length := ⟨3 * P.length - t, by omega⟩
  have he : P.early.arrive i = t := by rw [P.early_arrive]; dsimp [i]; omega
  simpa only [he, P.early_depart, Fin.val_zero, zero_add, i] using
    NativeExcursion.family_shadow_arrive P.early head hx hT i

/-- Apart from the root's value, the only possible competing nonzero
read before the late region is the fixed held-owner value. -/
theorem early_pair_sparsity (t : ℕ) :
    (H).shadow t = t ∨ P.raw t = 0 ∨ P.raw ((H).shadow t) = P.length - 2 := by
  by_cases he : (H).shadow t = t
  · exact Or.inl he
  have ha := ((H).shadow_ne_self_iff t).mp he
  have ht : P.length < t := by simpa only [NativeExcursion.family_owner, early_peak] using ha.1
  by_cases hu : t ≤ 2 * P.length
  · exact Or.inr (Or.inr (by rw [P.early_shadow_held head hx hT ht hu, P.raw_owner]))
  · exact Or.inr (Or.inl (P.raw_after (by omega)))

theorem early_core_orbit_pair (K : Finset (ActualFamily xs T))
    (hK : ∀ F ∈ K, F = H ∨ 3 * P.length ≤ F.start)
    {t : ℕ} (ht : t ≤ 3 * P.length) :
    shadowOrbit K t ⊆ ({t, (H).shadow t} : Set ℕ) := by
  apply shadowOrbit_subset_of_closed K _ (by simp)
  intro F hF u hu
  have hHt : (H).shadow t ≤ t := (H).shadowAction.apply_le t
  rcases hK F hF with rfl | hFstart
  · rcases Set.mem_insert_iff.mp hu with rfl | hu
    · simp
    · have he : u = (H).shadow t := Set.mem_singleton_iff.mp hu
      simp [he, (H).shadow_idempotent t]
  · have hut : u ≤ t := by
      rcases Set.mem_insert_iff.mp hu with rfl | hu
      · exact le_rfl
      · simpa only [Set.mem_singleton_iff.mp hu] using hHt
    rw [F.shadow_eq_self_of_le_owner
      (hut.trans (ht.trans (hFstart.trans F.owner_bounds.1.le)))]
    exact hu

theorem late_core_orbit_zero (K : Finset (ActualFamily xs T))
    (hK : ∀ F ∈ K, F = H ∨ 3 * P.length ≤ F.start)
    {t u : ℕ} (ht : 3 * P.length < t) (hu : u ∈ shadowOrbit K t) : P.raw u = 0 := by
  have hInv : shadowOrbit K t ⊆ Set.Ioi (3 * P.length) := by
    apply shadowOrbit_subset_of_closed K _ ht
    intro F hF v hv
    rcases hK F hF with rfl | hFstart
    · have he : (H).shadow v = v := by
        by_contra hn
        have hh := (((H).shadow_ne_self_iff v).mp hn).2
        rw [NativeExcursion.family_stop, P.early_arrive] at hh
        simp only [Fin.val_zero, Nat.sub_zero] at hh
        exact (not_le_of_gt hv) hh
      simpa only [he] using hv
    · by_cases he : F.shadow v = v
      · simpa only [he] using hv
      · exact hFstart.trans_lt
          (F.shadow_active_bounds ((F.shadow_ne_self_iff v).mp he)).1
  exact P.raw_after (by have := hInv hu; change 3 * P.length < u at this; omega)

/-- The packing condition holds for every computation seed, not only for
seeds reached from the chosen output root. -/
theorem isolated_core_packing (K : Finset (ActualFamily xs T))
    (hK : ∀ F ∈ K, F = H ∨ 3 * P.length ≤ F.start)
    (D : Finset ℕ) (hD : ∀ a ∈ D, a ≠ 0 ∧ a ≠ P.length - 2) (t : ℕ) :
    (D.filter (fun a => a ∈ P.raw '' shadowOrbit K t)).card ≤ 1 := by
  apply card_le_one.mpr
  intro a ha b hb
  obtain ⟨haD, u, hu, hua⟩ := mem_filter.mp ha
  obtain ⟨hbD, v, hv, hvb⟩ := mem_filter.mp hb
  have ha' := hD a haD
  have hb' := hD b hbD
  by_cases ht : t ≤ 3 * P.length
  · have hp := P.early_core_orbit_pair head hx hT K hK ht
    have hap : a = P.raw t ∨ a = P.raw ((H).shadow t) := by
      rcases Set.mem_insert_iff.mp (hp hu) with rfl | he
      · exact Or.inl hua.symm
      · exact Or.inr (hua.symm.trans (congrArg P.raw (Set.mem_singleton_iff.mp he)))
    have hbp : b = P.raw t ∨ b = P.raw ((H).shadow t) := by
      rcases Set.mem_insert_iff.mp (hp hv) with rfl | he
      · exact Or.inl hvb.symm
      · exact Or.inr (hvb.symm.trans (congrArg P.raw (Set.mem_singleton_iff.mp he)))
    rcases P.early_pair_sparsity head hx hT t with he | he | he
    · rw [he] at hap hbp
      omega
    · omega
    · omega
  · exact False.elim (ha'.1 (hua.symm.trans
      (P.late_core_orbit_zero head hx hT K hK (Nat.lt_of_not_ge ht) hu)))

/-- Summing the original fractional-cover constraints over the packing
gives the lower bound. The targets may be a subset of the covered raw set. -/
theorem isolated_core_cover_lower (K : Finset (ActualFamily xs T))
    (hK : ∀ F ∈ K, F = H ∨ 3 * P.length ≤ F.start)
    (D S : Finset ℕ) (hDS : D ⊆ S)
    (hD : ∀ a ∈ D, a ≠ 0 ∧ a ≠ P.length - 2)
    {ι : Type*} [Fintype ι] (seed : ι → ℕ) (w : ι → ℝ)
    (hw : FractionalCover.Covers S (fun i => P.raw '' shadowOrbit K (seed i)) w) :
    (D.card : ℝ) ≤ FractionalCover.cost w := by
  exact IntervalCover.packing_le_fractional_cover D univ _ w (fun i _ => hw.1 i)
    (fun a ha => hw.2 a (hDS ha))
    (fun i _ => P.isolated_core_packing head hx hT K hK D hD (seed i))

/-- Any number of exceptional families with outer lowers at or after 2L
preserves the zero-read region under every finite word, including the
empty word. The argument does not need disjoint exceptional spans. -/
theorem exceptional_word_zero (E : Finset (ActualFamily xs T))
    (hE : ∀ F ∈ E, 2 * P.length ≤ F.start)
    {t : ℕ} (ht : 2 * P.length ≤ t) (w : List (ActualFamily xs T))
    (hw : ∀ F ∈ w, F ∈ E) : P.raw (shadowEndpoint w t) = 0 := by
  have hInv := shadowOrbit_subset_of_closed E (Set.Ici (2 * P.length)) ht
    (fun F hF _ hu => F.shadow_preserves_lower (hE F hF) hu)
  have htime : 2 * P.length ≤ shadowEndpoint w t := hInv ⟨w, hw, rfl⟩
  exact P.raw_after (by omega)

theorem exceptional_profile_zero (E : Finset (ActualFamily xs T))
    (hE : ∀ F ∈ E, 2 * P.length ≤ F.start)
    (F : ActualFamily xs T) (hF : 2 * P.length ≤ F.start)
    (w : List (ActualFamily xs T)) (hw : ∀ G ∈ w, G ∈ E)
    {t : ℕ} (ht : F.start ≤ t ∧ t ≤ F.stop) : P.raw (shadowEndpoint w t) = 0 :=
  P.exceptional_word_zero E hE (hF.trans ht.1) w hw

end
end SourceCovers.SerialGeometry.Parameters
