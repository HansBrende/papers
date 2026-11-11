import AdaptiveTransfer.CurrentVersion

/-! Chronological dictionaries with true pre-step snapshot overlays. Skipped
writes need not preserve the entire dictionary: a requested current read is
correct when its actual latest visit is retained or followed by an overlay.
Snapshots at a step occur before that step's write. -/

namespace AdaptiveTransfer
variable {Cell Symbol : Type*} [DecidableEq Cell]

def snapshotMemory (initial : Cell → Symbol) (address : ℕ → Cell)
    (value : ℕ → Symbol) (keep : ℕ → Bool) (snapshot : ℕ → Cell → Option Symbol) : ℕ → Cell → Symbol
  | 0 => fun z => (snapshot 0 z).getD (initial z)
  | t + 1 => fun z => (snapshot (t + 1) z).getD
      (if keep t && decide (z = address t) then value t
       else snapshotMemory initial address value keep snapshot t z)

theorem snapshotMemory_overlay (initial : Cell → Symbol) (address : ℕ → Cell)
    (value : ℕ → Symbol) (keep : ℕ → Bool) (snapshot : ℕ → Cell → Option Symbol)
    {s : ℕ} {z : Cell} {v : Symbol} (hs : snapshot s z = some v) :
    snapshotMemory initial address value keep snapshot s z = v := by
  cases s <;> simp only [snapshotMemory, hs, Option.getD_some]

theorem snapshotMemory_initial (initial : Cell → Symbol) (address : ℕ → Cell)
    (value : ℕ → Symbol) (keep : ℕ → Bool) (snapshot : ℕ → Cell → Option Symbol)
    (z : Cell) (hsound : ∀ v, snapshot 0 z = some v → v = initial z) :
    snapshotMemory initial address value keep snapshot 0 z = initial z := by
  cases hs : snapshot 0 z with
  | none => simp only [snapshotMemory, hs, Option.getD_none]
  | some v => simpa only [snapshotMemory, hs, Option.getD_some] using hsound v hs

theorem snapshotMemory_kept_write (initial : Cell → Symbol) (address : ℕ → Cell)
    (value : ℕ → Symbol) (keep : ℕ → Bool) (snapshot : ℕ → Cell → Option Symbol)
    {p : ℕ} {z : Cell} (hp : z = address p) (hk : keep p = true)
    (hsound : ∀ v, snapshot (p + 1) z = some v →
      v = memoryAfter initial address value (fun _ => true) (p + 1) z) :
    snapshotMemory initial address value keep snapshot (p + 1) z =
      memoryAfter initial address value (fun _ => true) (p + 1) z := by
  cases hs : snapshot (p + 1) z with
  | none =>
    simp only [snapshotMemory, hs, Option.getD_none]
    simp only [hk, hp, decide_true, Bool.and_self, ite_true, memoryAfter]
  | some v => exact (snapshotMemory_overlay _ _ _ _ _ hs).trans (hsound v hs)

/-- True overlays cannot spoil a cell between actual visits. -/
theorem snapshotMemory_no_write_correct (initial : Cell → Symbol) (address : ℕ → Cell)
    (value : ℕ → Symbol) (keep : ℕ → Bool) (snapshot : ℕ → Cell → Option Symbol)
    {s t : ℕ} {z : Cell} (hst : s ≤ t)
    (hstart : snapshotMemory initial address value keep snapshot s z =
      memoryAfter initial address value (fun _ => true) s z)
    (hsound : ∀ u ≤ t, ∀ v, snapshot u z = some v →
      v = memoryAfter initial address value (fun _ => true) u z)
    (hgap : ∀ u, s ≤ u → u < t → z ≠ address u) :
    snapshotMemory initial address value keep snapshot t z =
      memoryAfter initial address value (fun _ => true) t z := by
  have hrec : ∀ v, s ≤ v → v ≤ t →
      snapshotMemory initial address value keep snapshot v z =
        memoryAfter initial address value (fun _ => true) v z := by
    intro v hsv
    induction v, hsv using Nat.le_induction with
    | base => exact fun _ => hstart
    | succ v hsv ih =>
      intro hvt
      cases hs : snapshot (v + 1) z with
      | some a => exact (snapshotMemory_overlay _ _ _ _ _ hs).trans (hsound _ hvt a hs)
      | none =>
        have hne := hgap v hsv (by omega)
        simpa only [snapshotMemory, hs, Option.getD_none, hne, decide_false, Bool.and_false,
          Bool.false_eq_true, ite_false, memoryAfter] using ih (by omega)
  exact hrec t hst le_rfl

/-- The precise current-read obligation for a filtered dictionary with true
snapshots: retain the actual latest visit or overlay the cell after it. -/
theorem snapshot_filtered_read_correct (initial : Cell → Symbol) (address : ℕ → Cell)
    (value : ℕ → Symbol) (keep : ℕ → Bool) (snapshot : ℕ → Cell → Option Symbol)
    (t : ℕ) (z : Cell)
    (hsound : ∀ u ≤ t, ∀ v, snapshot u z = some v →
      v = memoryAfter initial address value (fun _ => true) u z)
    (hparent : ∀ p < t, z = address p →
      (∀ u, p < u → u < t → z ≠ address u) →
      keep p = true ∨ ∃ s, p < s ∧ s ≤ t ∧ (snapshot s z).isSome) :
    snapshotMemory initial address value keep snapshot t z =
      memoryAfter initial address value (fun _ => true) t z := by
  classical
  let visits := (Finset.range t).filter fun p => z = address p
  by_cases hne : visits.Nonempty
  · let p := visits.max' hne
    have hp := Finset.mem_filter.mp (Finset.max'_mem visits hne)
    have hpt := Finset.mem_range.mp hp.1
    have hlast : ∀ u, p < u → u < t → z ≠ address u := by
      intro u hpu hut he
      have hu : u ∈ visits := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hut, he⟩
      have := Finset.le_max' visits u hu
      omega
    rcases hparent p hpt hp.2 hlast with hk | ⟨s, hps, hst, hs⟩
    · exact snapshotMemory_no_write_correct _ _ _ _ _ (by omega : p + 1 ≤ t)
        (snapshotMemory_kept_write _ _ _ _ _ hp.2 hk (hsound _ (by omega)))
        hsound (fun u hpu hut => hlast u (by omega) hut)
    · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hs
      exact snapshotMemory_no_write_correct _ _ _ _ _ hst
        ((snapshotMemory_overlay _ _ _ _ _ hv).trans (hsound s hst v hv))
        hsound (fun u hsu hut => hlast u (hps.trans_le hsu) hut)
  · have hnovisit : ∀ u < t, z ≠ address u := by
      intro u hut he
      exact hne ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hut, he⟩⟩
    apply snapshotMemory_no_write_correct _ _ _ _ _ (Nat.zero_le t)
      (snapshotMemory_initial _ _ _ _ _ z (hsound 0 (Nat.zero_le t))) hsound
    exact fun u _ hut => hnovisit u hut

/-- Equal paid overlays and kept events give equal filtered dictionaries.
The proof uses only earlier kept events and overlays through the read time. -/
theorem snapshotMemory_congr (initial : Cell → Symbol)
    (address address' : ℕ → Cell) (value value' : ℕ → Symbol) (keep : ℕ → Bool)
    (snapshot snapshot' : ℕ → Cell → Option Symbol) (t : ℕ)
    (hsnapshot : ∀ u ≤ t, snapshot u = snapshot' u)
    (hevents : ∀ u < t, keep u = true → address u = address' u ∧ value u = value' u) :
    snapshotMemory initial address value keep snapshot t =
      snapshotMemory initial address' value' keep snapshot' t := by
  induction t with
  | zero => simp only [snapshotMemory, hsnapshot 0 le_rfl]
  | succ t ih =>
    have hp := ih (fun u hu => hsnapshot u (by omega)) (fun u hu hk => hevents u (by omega) hk)
    funext z
    by_cases hk : keep t = true
    · have hh := hevents t (by omega) hk
      simp only [snapshotMemory, hsnapshot (t + 1) le_rfl, hk, hh.1, hh.2, hp]
    · have hk' : keep t = false := Bool.eq_false_iff.mpr hk
      simp only [snapshotMemory, hsnapshot (t + 1) le_rfl, hk', Bool.false_and,
        Bool.false_eq_true, ite_false, hp]

open Transpose
namespace ExecutionPrefix
variable {M : TM} {w : List Bool} {T : ℕ} (E : ExecutionPrefix M w T)

theorem snapshot_native_read (keep : ℕ → Bool) (snapshot : ℕ → ℤ → Option (Fin (M.g + 1)))
    (h : Fin M.k) {t : ℕ} (ht : t ≤ T)
    (hsound : ∀ u ≤ t, ∀ z v, snapshot u z = some v → v = (E.config u).work h z)
    (hparent : ∀ p < t, (E.config t).workPos h = (E.config p).workPos h →
      (∀ u, p < u → u < t → (E.config t).workPos h ≠ (E.config u).workPos h) →
      keep p = true ∨ ∃ s, p < s ∧ s ≤ t ∧ (snapshot s ((E.config t).workPos h)).isSome) :
    snapshotMemory (fun _ => 0) (fun u => (E.config u).workPos h) (E.written h) keep snapshot t
      ((E.config t).workPos h) = (E.config t).work h ((E.config t).workPos h) := by
  rw [E.work_eq_memoryAfter h ht]
  apply snapshot_filtered_read_correct _ _ _ _ _ _ _ _ hparent
  intro u hu v hv
  rw [← E.work_eq_memoryAfter h (hu.trans ht)]
  exact hsound u hu _ v hv

end ExecutionPrefix
end AdaptiveTransfer
