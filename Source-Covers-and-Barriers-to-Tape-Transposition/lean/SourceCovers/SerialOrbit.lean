import SourceCovers.SerialBankClosure

set_option autoImplicit false

/-! The complete ordinary orbit has exactly the six displayed groups.
The closure check uses every retained family, not only the path witnesses. -/

namespace SourceCovers.SerialGeometry.Parameters

open Classical Finset BoundedNesting
noncomputable section

variable (P : Parameters)

def serialCloud : Finset ℕ :=
  univ.image P.lateTime ∪ univ.image (fun k : Fin (P.m - 1) => P.bridgeReturn k) ∪
    univ.image P.bridgeExit ∪ P.olderGrid ∪ univ.image P.coverSeed ∪ univ.image P.coverTarget

theorem mem_serialCloud (t : ℕ) : t ∈ P.serialCloud ↔
    (∃ k, P.lateTime k = t) ∨ (∃ k : Fin (P.m - 1), P.bridgeReturn k = t) ∨
    (∃ k, P.bridgeExit k = t) ∨ (∃ i, P.olderTime i = t) ∨
    (∃ i, P.coverSeed i = t) ∨ (∃ i, P.coverTarget i = t) := by
  simp only [serialCloud, olderGrid, mem_union, mem_image, mem_univ, true_and, or_assoc]

theorem lateTime_mem_serialCloud (k : Fin (P.m - 1)) : P.lateTime k ∈ P.serialCloud :=
  (P.mem_serialCloud _).mpr (Or.inl ⟨k, rfl⟩)

theorem bridgeReturn_mem_serialCloud (k : Fin (P.m - 1)) : P.bridgeReturn k ∈ P.serialCloud :=
  (P.mem_serialCloud _).mpr (Or.inr (Or.inl ⟨k, rfl⟩))

theorem bridgeExit_mem_serialCloud (k : Fin (P.m - 1)) : P.bridgeExit k ∈ P.serialCloud :=
  (P.mem_serialCloud _).mpr (Or.inr (Or.inr (Or.inl ⟨k, rfl⟩)))

theorem olderTime_mem_serialCloud (i : P.GridIndex) : P.olderTime i ∈ P.serialCloud :=
  (P.mem_serialCloud _).mpr (Or.inr (Or.inr (Or.inr (Or.inl ⟨i, rfl⟩))))

theorem coverSeed_mem_serialCloud (i : Fin P.targets) : P.coverSeed i ∈ P.serialCloud :=
  (P.mem_serialCloud _).mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨i, rfl⟩)))))

theorem coverTarget_mem_serialCloud (i : Fin P.targets) : P.coverTarget i ∈ P.serialCloud :=
  (P.mem_serialCloud _).mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨i, rfl⟩)))))

private theorem shadow_fixed (F : ActualFamily P.heads P.horizon) {t : ℕ}
    (ht : t ≤ F.owner ∨ F.stop < t) : F.shadow t = t := by
  by_contra h
  have ha := (F.shadow_ne_self_iff t).mp h
  omega

theorem bank_cloud_closed (c : Fin 2) (j : Fin P.bankCount)
    (hj : P.bankFamily c j ∈ P.retainedCore) {t : ℕ} (ht : t ∈ P.serialCloud) :
    (P.bankFamily c j).shadow t ∈ P.serialCloud := by
  rcases (P.mem_serialCloud t).mp ht with
    ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · obtain ⟨k', he⟩ := P.late_shadow_step c j hj k
    exact he ▸ P.lateTime_mem_serialCloud k'
  · rw [P.bank_shadow_fixed_away c j (Or.inr (by have := P.bridgeReturn_bounds k; omega))]
    exact P.bridgeReturn_mem_serialCloud k
  · rcases P.bridgeExit_shadow_step c j k with he | he
    · rw [he]
      exact P.bridgeExit_mem_serialCloud k
    · exact he ▸ P.olderTime_mem_serialCloud (k, 0)
  · obtain ⟨i', he⟩ := P.older_shadow_step c j hj i
    exact he ▸ P.olderTime_mem_serialCloud i'
  · rw [P.bank_shadow_fixed_away c j (Or.inl (P.coverSeed_bounds i).2.le)]
    exact P.coverSeed_mem_serialCloud i
  · rw [P.bank_shadow_fixed_away c j (Or.inl (by have := P.coverTarget_bounds i; omega))]
    exact P.coverTarget_mem_serialCloud i

theorem newer_cloud_closed {t : ℕ} (ht : t ∈ P.serialCloud) :
    P.newerFamily.shadow t ∈ P.serialCloud := by
  have ho : P.newerFamily.owner = 8 * P.length := by
    rw [newerFamily, NativeExcursion.family_owner, newer_peak]
  rcases (P.mem_serialCloud t).mp ht with
    ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · rw [P.newer_serial_shadow]
    exact P.bridgeReturn_mem_serialCloud k
  · rw [shadow_fixed P _ (Or.inl (by rw [ho]; exact (P.bridgeReturn_bounds k).2.le))]
    exact P.bridgeReturn_mem_serialCloud k
  · rw [shadow_fixed P _ (Or.inl (by rw [ho]; have := P.bridgeExit_bounds k; omega))]
    exact P.bridgeExit_mem_serialCloud k
  · rw [shadow_fixed P _ (Or.inl (by rw [ho]; have := P.olderTime_bounds i; omega))]
    exact P.olderTime_mem_serialCloud i
  · rw [shadow_fixed P _ (Or.inl (by rw [ho]; have := P.coverSeed_bounds i; omega))]
    exact P.coverSeed_mem_serialCloud i
  · rw [shadow_fixed P _ (Or.inl (by rw [ho]; have := P.coverTarget_bounds i; omega))]
    exact P.coverTarget_mem_serialCloud i

theorem bridge_cloud_closed {t : ℕ} (ht : t ∈ P.serialCloud) :
    P.bridgeFamily.shadow t ∈ P.serialCloud := by
  have ho : P.bridgeFamily.owner = 6 * P.length := by
    rw [bridgeFamily, NativeExcursion.family_owner, bridge_peak]
  have hs := P.bridgeFamily_stop_bounds
  rcases (P.mem_serialCloud t).mp ht with
    ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · rw [shadow_fixed P _ (Or.inr (by have := P.lateTime_bounds k; omega))]
    exact P.lateTime_mem_serialCloud k
  · rw [P.bridge_serial_shadow]
    exact P.bridgeExit_mem_serialCloud k
  · rw [shadow_fixed P _ (Or.inl (by rw [ho]; exact (P.bridgeExit_bounds k).2.le))]
    exact P.bridgeExit_mem_serialCloud k
  · rw [shadow_fixed P _ (Or.inl (by rw [ho]; have := P.olderTime_bounds i; omega))]
    exact P.olderTime_mem_serialCloud i
  · rw [shadow_fixed P _ (Or.inl (by rw [ho]; have := P.coverSeed_bounds i; omega))]
    exact P.coverSeed_mem_serialCloud i
  · rw [shadow_fixed P _ (Or.inl (by rw [ho]; have := P.coverTarget_bounds i; omega))]
    exact P.coverTarget_mem_serialCloud i

theorem early_cloud_closed {t : ℕ} (ht : t ∈ P.serialCloud) :
    P.earlyFamily.shadow t ∈ P.serialCloud := by
  have ho : P.earlyFamily.owner = P.length := by
    rw [earlyFamily, NativeExcursion.family_owner, early_peak]
  rcases (P.mem_serialCloud t).mp ht with
    ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · rw [shadow_fixed P _ (Or.inr (by rw [P.earlyFamily_stop]; have := P.lateTime_bounds k; omega))]
    exact P.lateTime_mem_serialCloud k
  · rw [shadow_fixed P _ (Or.inr (by rw [P.earlyFamily_stop]; have := P.bridgeReturn_bounds k; omega))]
    exact P.bridgeReturn_mem_serialCloud k
  · rw [shadow_fixed P _ (Or.inr (by rw [P.earlyFamily_stop]; have := P.bridgeExit_bounds k; omega))]
    exact P.bridgeExit_mem_serialCloud k
  · rw [shadow_fixed P _ (Or.inr (by rw [P.earlyFamily_stop]; have := P.olderTime_bounds i; omega))]
    exact P.olderTime_mem_serialCloud i
  · rw [P.early_serial_shadow]
    exact P.coverTarget_mem_serialCloud i
  · rw [shadow_fixed P _ (Or.inl (by rw [ho]; exact (P.coverTarget_bounds i).2.le))]
    exact P.coverTarget_mem_serialCloud i

theorem older_cloud_closed {t : ℕ} (ht : t ∈ P.serialCloud) :
    P.olderFamily.shadow t ∈ P.serialCloud := by
  have hs := P.olderFamily_stop_lt
  rcases (P.mem_serialCloud t).mp ht with
    ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · rw [shadow_fixed P _ (Or.inr (by have := P.lateTime_bounds k; omega))]
    exact P.lateTime_mem_serialCloud k
  · rw [shadow_fixed P _ (Or.inr (by have := P.bridgeReturn_bounds k; omega))]
    exact P.bridgeReturn_mem_serialCloud k
  · rw [shadow_fixed P _ (Or.inr (by have := P.bridgeExit_bounds k; omega))]
    exact P.bridgeExit_mem_serialCloud k
  · have hm : P.olderTime i ∈ P.olderGrid := mem_image_of_mem _ (mem_univ i)
    rw [← P.sparseArrival_image] at hm
    obtain ⟨a, _, he⟩ := mem_image.mp hm
    rw [← he, P.older_serial_shadow]
    exact P.coverSeed_mem_serialCloud a
  · have hh := P.older_serial_hop i
    have hb := P.olderFamily.shadow_active_bounds
      ⟨(family_owner_inside P.olderFamily hh).2, (fam_bounds hh).2⟩
    rw [P.older_serial_shadow] at hb
    rw [shadow_fixed P _ (Or.inl hb.2.1)]
    exact P.coverSeed_mem_serialCloud i
  · have hb := P.olderFamily.owner_bounds.1
    rw [P.olderFamily_start] at hb
    rw [shadow_fixed P _ (Or.inl (by have := P.coverTarget_bounds i; omega))]
    exact P.coverTarget_mem_serialCloud i

theorem serialCloud_closed {F : ActualFamily P.heads P.horizon}
    (hF : F ∈ P.jointFamilies) {t : ℕ} (ht : t ∈ P.serialCloud) : F.shadow t ∈ P.serialCloud := by
  rcases mem_union.mp hF with hF | hF
  · rcases (P.mem_retainedCore F).mp hF with ⟨c, j, rfl, hj⟩ | rfl | rfl
    · exact P.bank_cloud_closed c j (P.bankFamily_retained c j hj) ht
    · exact P.early_cloud_closed ht
    · exact P.bridge_cloud_closed ht
  · rcases (P.mem_exceptionalFamilies F).mp hF with rfl | rfl
    · exact P.newer_cloud_closed ht
    · exact P.older_cloud_closed ht

/-- An equality of complete time orbits, not merely a list of witnessed paths. -/
theorem jointOrbit_eq : P.jointOrbit = (P.serialCloud : Set ℕ) := by
  apply Set.Subset.antisymm
  · exact shadowOrbit_subset_of_closed _ _ (P.lateTime_mem_serialCloud 0)
      (fun _ hF _ ht => P.serialCloud_closed hF ht)
  · intro t ht
    rcases (P.mem_serialCloud t).mp ht with
      ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact (P.lateTime_reached k).2
    · exact (P.bridgeReturn_reached k).2
    · exact (P.bridgeExit_reached k).2
    · exact (P.olderTime_reached i).2
    · exact P.coverSeed_joint i
    · exact P.coverTarget_joint i

theorem jointRaw_eq : P.raw '' P.jointOrbit = (P.completeRaw : Set ℕ) := by
  apply Set.Subset.antisymm ?_ P.completeRaw_subset_joint
  rintro _ ⟨t, ht, rfl⟩
  rw [P.jointOrbit_eq] at ht
  have hz : (0 : ℕ) ∈ P.completeRaw := mem_insert_self _ _
  rcases (P.mem_serialCloud t).mp ht with
    ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · rw [P.raw_after (by have := P.lateTime_bounds k; omega)]
    exact hz
  · rw [P.raw_after (by have := P.bridgeReturn_bounds k; omega)]
    exact hz
  · rw [P.raw_after (by have := P.bridgeExit_bounds k; omega)]
    exact hz
  · rw [P.raw_after (by have := P.olderTime_bounds i; omega)]
    exact hz
  · rw [P.raw_coverSeed]
    exact hz
  · rw [P.raw_initial (P.coverTarget_bounds i).2]
    exact mem_insert_of_mem (mem_image_of_mem _ (mem_univ i))

end
end SourceCovers.SerialGeometry.Parameters
