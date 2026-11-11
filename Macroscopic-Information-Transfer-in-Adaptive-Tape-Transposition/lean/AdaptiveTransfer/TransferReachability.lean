import AdaptiveTransfer.ReplayGeometry

/-! Exact activation counts for cut-avoiding source reachability. The
reachable set is defined from literal dependency paths, including endpoints;
its chronological runs are charged to the next cut or to the horizon. -/

namespace AdaptiveTransfer.TransferReachability
open Finset MergeDepth NativeRelations BoundedNesting

attribute [local instance] Classical.propDecidable

theorem runEnd_injective {R : Finset ℕ} {T : ℕ} (hRT : ∀ t ∈ R, t < T) :
    Set.InjOn (runEnd R T) (runStarts R) := by
  intro a ha b hb he
  have hA := runEnd_spec hRT ha
  have hB := runEnd_spec hRT hb
  rcases lt_trichotomy a b with hab | hab | hab
  · have hn := (mem_filter.mp hb).2.resolve_left (by omega)
    exact (hn (hA.2.2.2 (b - 1) (mem_Ico.mpr ⟨by omega, by omega⟩))).elim
  · exact hab
  · have hn := (mem_filter.mp ha).2.resolve_left (by omega)
    exact (hn (hB.2.2.2 (a - 1) (mem_Ico.mpr ⟨by omega, by omega⟩))).elim

/-- Within each interval not meeting B, reachability can only turn on once.
The proof counts actual run endpoints; B need not be contained in [0,T). -/
theorem activation_count {R B : Finset ℕ} {T : ℕ} (hRT : ∀ t ∈ R, t < T)
    (hup : ∀ t ∈ R, t + 1 < T → t + 1 ∉ B → t + 1 ∈ R) :
    (runStarts R).card ≤ B.card + 1 := by
  have hmap : ∀ a ∈ runStarts R, runEnd R T a ∈ insert T B := by
    intro a ha
    have hs := runEnd_spec hRT ha
    by_cases he : runEnd R T a = T
    · exact mem_insert.mpr (Or.inl he)
    · apply mem_insert_of_mem
      by_contra hB
      have hp : runEnd R T a - 1 ∈ R :=
        hs.2.2.2 _ (mem_Ico.mpr ⟨by omega, by omega⟩)
      have hu := hup _ hp (by omega) (by simpa only [Nat.sub_add_cancel (by omega : 1 ≤ runEnd R T a)] using hB)
      exact hs.2.2.1 (by simpa only [Nat.sub_add_cancel (by omega : 1 ≤ runEnd R T a)] using hu)
  exact (card_le_card_of_injOn (runEnd R T) hmap (runEnd_injective hRT)).trans (card_insert_le _ _)

/-- A change from unreachable to reachable crosses an actual activation. -/
theorem activation_between {R : Finset ℕ} {T u v : ℕ}
    (hRT : ∀ t ∈ R, t < T) (huv : u ≤ v) (hu : u ∉ R) (hv : v ∈ R) :
    ∃ a ∈ runStarts R, u < a ∧ a ≤ v := by
  obtain ⟨a, ha, hav, hve⟩ := exists_run_cover hRT hv
  have hlt : u < a := by
    by_contra hn
    exact hu ((runEnd_spec hRT ha).2.2.2 u (mem_Ico.mpr ⟨by omega, by omega⟩))
  exact ⟨a, ha, hlt, hav⟩

noncomputable def reaches {k : ℕ} (xs : Fin k → ℕ → ℤ) (T : ℕ)
    (B targets : Finset ℕ) : Finset ℕ :=
  (range T).filter fun t => ∃ ρ : List ℕ,
    IsDepPath xs T (t :: ρ) ∧ (t :: ρ).getLastD t ∈ targets ∧
      ∀ u ∈ t :: ρ, u ∉ B

theorem reaches_before {k T : ℕ} {xs : Fin k → ℕ → ℤ} {B targets : Finset ℕ}
    {t : ℕ} (ht : t ∈ reaches xs T B targets) : t < T :=
  mem_range.mp (mem_filter.mp ht).1

theorem reaches_uncut {k T : ℕ} {xs : Fin k → ℕ → ℤ} {B targets : Finset ℕ}
    {t : ℕ} (ht : t ∈ reaches xs T B targets) : t ∉ B := by
  obtain ⟨ρ, _, _, hfree⟩ := (mem_filter.mp ht).2
  exact hfree t (List.mem_cons_self ..)

theorem reaches_of_step {k T u v : ℕ} {xs : Fin k → ℕ → ℤ} {B targets : Finset ℕ}
    (hstep : DepStep xs T u v) (hu : u ∉ B) (hv : v ∈ reaches xs T B targets) :
    u ∈ reaches xs T B targets := by
  obtain ⟨ρ, hp, ht, hfree⟩ := (mem_filter.mp hv).2
  refine mem_filter.mpr ⟨mem_range.mpr (depStep_lt hstep).2, v :: ρ, ⟨hstep, hp⟩, ?_, ?_⟩
  · simpa only [LinNet.getLastD_cons_cons] using ht
  · intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hu
    · exact hfree z hz

theorem reaches_activations {k T : ℕ} (xs : Fin k → ℕ → ℤ) (B targets : Finset ℕ) :
    (runStarts (reaches xs T B targets)).card ≤ B.card + 1 := by
  apply activation_count (fun _ ht => reaches_before ht)
  intro t ht hT hB
  exact reaches_of_step (Or.inl ⟨rfl, hT⟩) hB ht

theorem cut_excludes_reaches {k T : ℕ} {xs : Fin k → ℕ → ℤ} {B targets roots : Finset ℕ}
    (hcut : IsMengerVertexCut xs T roots targets B) {t : ℕ} (ht : t ∈ roots) :
    t ∉ reaches xs T B targets := by
  intro hreach
  obtain ⟨ρ, hp, hend, hfree⟩ := (mem_filter.mp hreach).2
  obtain ⟨u, hu, hB⟩ := hcut ρ t ht hp hend
  exact hfree u hu hB

end AdaptiveTransfer.TransferReachability
