import SourceCovers.SerialBankSteps

set_option autoImplicit false

/-! The displayed serial paths live in the full paid causal graph as well
as the ordinary joint orbit. Only the first sparse return needs clipping. -/

namespace SourceCovers.SerialGeometry.Parameters

open Classical Finset BoundedNesting LeanMachine.CausalRecovery
noncomputable section

variable (P : Parameters)

def jointFamilies : Finset (ActualFamily P.heads P.horizon) :=
  P.retainedCore ∪ P.exceptionalFamilies

def jointOrbit : Set ℕ := shadowOrbit P.jointFamilies P.root

def physicalCone : Set ℕ := sourceCone (actualParents P.heads P.horizon)
  (fun t => {P.raw t}) (P.payment : Set ℕ) P.root

/-- A common path witness keeps the physical and ordinary meanings explicit. -/
def Reached (t : ℕ) : Prop :=
  Ancestor (actualParents P.heads P.horizon) (P.payment : Set ℕ) P.root t ∧ t ∈ P.jointOrbit

theorem reached_root : P.Reached P.root := ⟨.root, mem_shadowOrbit_self _ _⟩

theorem joint_core {F : ActualFamily P.heads P.horizon} (hF : F ∈ P.retainedCore) :
    F ∈ P.jointFamilies := mem_union_left _ hF

theorem joint_newer : P.newerFamily ∈ P.jointFamilies :=
  mem_union_right _ ((P.mem_exceptionalFamilies _).mpr (Or.inl rfl))

theorem joint_older : P.olderFamily ∈ P.jointFamilies :=
  mem_union_right _ ((P.mem_exceptionalFamilies _).mpr (Or.inr rfl))

theorem joint_shadow {t : ℕ} (ht : t ∈ P.jointOrbit)
    {F : ActualFamily P.heads P.horizon} (hF : F ∈ P.jointFamilies) :
    F.shadow t ∈ P.jointOrbit :=
  shadowOrbit_trans ht ⟨[F], by simpa using hF, rfl⟩

/-- A retained complete-family hop to an unpaid lower is exact in both
relations. The physical relation still includes every state and work edge. -/
theorem reached_hop {t u : ℕ} (ht : P.Reached t)
    {F : ActualFamily P.heads P.horizon} (hF : F ∈ P.jointFamilies) {head : Fin 8}
    (hh : (head, u, t) ∈ F.hops) (hu : u ∉ P.payment) : P.Reached u := by
  have hsel : F ∈ P.coreFamilies ∪ P.exceptionalFamilies := by
    rcases mem_union.mp hF with hc | he
    · exact mem_union_left _ (P.retainedCore_subset hc)
    · exact mem_union_right _ he
  have he : F.shadow t = u := F.shadow_exact P.heads_isWalk hh (by
    change u ≠ F.start
    intro h
    exact hu (h ▸ outer_mem_initialPayment (M := P.m) (ρ := 0) hsel))
  refine ⟨ht.1.step ?_ hu, he ▸ P.joint_shadow ht.2 hF⟩
  exact mem_actualParents.mpr (Or.inr ⟨head, mem_allHops.mp (mem_fam.mp hh).1⟩)

theorem lateTime_reached (k : Fin (P.m - 1)) : P.Reached (P.lateTime k) := by
  obtain ⟨k, hk⟩ := k
  induction k with
  | zero => exact P.reached_root
  | succ k ih =>
    let prev : Fin (P.m - 1) := ⟨k, by omega⟩
    let next : Fin (P.m - 1) := ⟨k + 1, hk⟩
    obtain ⟨j, hj, hh⟩ := P.late_bank_step prev next rfl
    exact P.reached_hop (ih prev.isLt) (P.joint_core hj) hh (P.lateTime_unpaid next)

theorem bridgeReturn_reached (k : Fin (P.m - 1)) : P.Reached (P.bridgeReturn k) :=
  P.reached_hop (P.lateTime_reached k) P.joint_newer (P.newer_serial_hop k)
    (P.bridgeReturn_unpaid k)

theorem bridgeExit_reached (k : Fin (P.m - 1)) : P.Reached (P.bridgeExit k) :=
  P.reached_hop (P.bridgeReturn_reached k) (P.joint_core P.bridgeFamily_retained)
    (P.bridge_serial_hop k) (P.bridgeExit_unpaid k)

theorem olderTime_reached (i : P.GridIndex) : P.Reached (P.olderTime i) := by
  obtain ⟨k, ⟨l, hl⟩⟩ := i
  induction l with
  | zero =>
    obtain ⟨j, hj, hh⟩ := P.bridge_exit_bank_step k
    exact P.reached_hop (P.bridgeExit_reached k) (P.joint_core hj) hh
      (P.olderTime_unpaid (k, 0))
  | succ l ih =>
    let prev : Fin (P.m - 1) := ⟨l, by omega⟩
    let next : Fin (P.m - 1) := ⟨l + 1, hl⟩
    obtain ⟨j, hj, hh⟩ := P.older_bank_step k prev next rfl
    exact P.reached_hop (ih prev.isLt) (P.joint_core hj) hh
      (P.olderTime_unpaid (k, next))

theorem sparseArrival_reached (i : Fin P.targets) : P.Reached (P.sparseArrival i) := by
  obtain ⟨j, _, hj⟩ := mem_image.mp (P.sparseArrival_mem i)
  exact hj ▸ P.olderTime_reached j

theorem coverSeed_reached {i : Fin P.targets} (hi : i ≠ 0) : P.Reached (P.coverSeed i) := by
  have hh := P.older_serial_hop i
  have he : P.coverSeed i = P.sparseDeparture i := by simp only [coverSeed, ite_eq_right hi]
  rw [← he] at hh
  exact P.reached_hop (P.sparseArrival_reached i) P.joint_older hh (P.coverSeed_unpaid i)

theorem coverTarget_reached {i : Fin P.targets} (hi : i ≠ 0) : P.Reached (P.coverTarget i) :=
  P.reached_hop (P.coverSeed_reached hi) (P.joint_core P.earlyFamily_retained)
    (P.early_serial_hop i) (P.coverTarget_unpaid i)

/-- Ordinary shadows retain the clipped first seed, without asserting a
physical unpaid path to it. -/
theorem coverSeed_joint (i : Fin P.targets) : P.coverSeed i ∈ P.jointOrbit := by
  rw [← P.older_serial_shadow i]
  exact P.joint_shadow (P.sparseArrival_reached i).2 P.joint_older

theorem coverTarget_joint (i : Fin P.targets) : P.coverTarget i ∈ P.jointOrbit := by
  rw [← P.early_serial_shadow i]
  exact P.joint_shadow (P.coverSeed_joint i) (P.joint_core P.earlyFamily_retained)

theorem raw_root : P.raw P.root = 0 :=
  P.raw_after (by have := (P.lateTime_bounds 0).1; change _ ≤ P.lateTime 0; omega)

theorem completeRaw_subset_joint : (P.completeRaw : Set ℕ) ⊆ P.raw '' P.jointOrbit := by
  intro a ha
  rcases mem_insert.mp ha with rfl | ha
  · exact ⟨P.root, P.reached_root.2, P.raw_root⟩
  · obtain ⟨i, _, rfl⟩ := mem_image.mp ha
    exact ⟨P.coverTarget i, P.coverTarget_joint i, P.raw_initial (P.coverTarget_bounds i).2⟩

def physicalGrid : Finset ℕ :=
  insert 0 ((univ.erase (0 : Fin P.targets)).image P.coverTarget)

theorem physicalGrid_card : P.physicalGrid.card = P.targets := by
  have hzero : 0 ∉ (univ.erase (0 : Fin P.targets)).image P.coverTarget := by
    rintro ha
    obtain ⟨i, _, he⟩ := mem_image.mp ha
    exact (P.coverTarget_bounds i).1.ne' he
  rw [physicalGrid, card_insert_of_notMem hzero,
    card_image_of_injective _ P.coverTarget_injective, card_erase_of_mem (mem_univ _), card_univ]
  simp only [Fintype.card_fin]
  have := P.targets_pos
  omega

theorem physicalGrid_subset_cone : (P.physicalGrid : Set ℕ) ⊆ P.physicalCone := by
  intro a ha
  rcases mem_insert.mp ha with rfl | ha
  · exact ⟨P.root, .root, P.raw_root.symm⟩
  · obtain ⟨i, hi, rfl⟩ := mem_image.mp ha
    exact ⟨P.coverTarget i, (P.coverTarget_reached (mem_erase.mp hi).1).1,
      (P.raw_initial (P.coverTarget_bounds i).2).symm⟩

end
end SourceCovers.SerialGeometry.Parameters
