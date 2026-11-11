import AdaptiveTransfer.NativeWrites
import Mathlib.Data.Finset.Max

/-! A chronological dictionary may skip obsolete writes. At a requested read,
retaining its actual last visit is sufficient. This is a current-read theorem;
it deliberately makes no claim of equality on unobserved cells. -/

namespace AdaptiveTransfer

variable {Cell Symbol : Type*} [DecidableEq Cell]

def memoryAfter (initial : Cell → Symbol) (address : ℕ → Cell)
    (value : ℕ → Symbol) (keep : ℕ → Bool) : ℕ → Cell → Symbol
  | 0 => initial
  | t + 1 => fun z => if keep t && decide (z = address t) then value t
      else memoryAfter initial address value keep t z

theorem memoryAfter_no_write (initial : Cell → Symbol) (address : ℕ → Cell)
    (value : ℕ → Symbol) (keep : ℕ → Bool) {u v : ℕ} {z : Cell}
    (huv : u ≤ v) (hgap : ∀ t, u ≤ t → t < v → keep t = true → z ≠ address t) :
    memoryAfter initial address value keep v z =
      memoryAfter initial address value keep u z := by
  induction v, huv using Nat.le_induction with
  | base => rfl
  | succ v huv ih =>
    have hlast : ¬ (keep v = true ∧ z = address v) := by
      rintro ⟨hk, hz⟩
      exact hgap v huv (by omega) hk hz
    have hprefix : ∀ t, u ≤ t → t < v → keep t = true → z ≠ address t := by
      intro t hut htv hk
      exact hgap t hut (by omega) hk
    simpa [memoryAfter, hlast] using ih hprefix

theorem memoryAfter_last_write (initial : Cell → Symbol) (address : ℕ → Cell)
    (value : ℕ → Symbol) (keep : ℕ → Bool) {p t : ℕ} {z : Cell}
    (hpt : p < t) (hp : z = address p) (hk : keep p = true)
    (hlast : ∀ u, p < u → u < t → z ≠ address u) :
    memoryAfter initial address value keep t z = value p := by
  rw [memoryAfter_no_write initial address value keep (by omega : p + 1 ≤ t)
    (fun u hpu hut _ => hlast u (by omega) hut)]
  simp [memoryAfter, hp, hk]

/-- The sole required retained write is the actual last write to this cell. -/
theorem filtered_read_correct (initial : Cell → Symbol) (address : ℕ → Cell)
    (value : ℕ → Symbol) (keep : ℕ → Bool) (t : ℕ) (z : Cell)
    (hparent : ∀ p < t, z = address p →
      (∀ u, p < u → u < t → z ≠ address u) → keep p = true) :
    memoryAfter initial address value keep t z =
      memoryAfter initial address value (fun _ => true) t z := by
  classical
  let visits := (Finset.range t).filter fun p => z = address p
  by_cases hne : visits.Nonempty
  · let p := visits.max' hne
    have hp := Finset.mem_filter.mp (Finset.max'_mem visits hne)
    have hpt : p < t := Finset.mem_range.mp hp.1
    have hlast : ∀ u, p < u → u < t → z ≠ address u := by
      intro u hpu hut hzu
      have hu : u ∈ visits := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hut, hzu⟩
      have := Finset.le_max' visits u hu
      omega
    rw [memoryAfter_last_write initial address value keep hpt hp.2
      (hparent p hpt hp.2 hlast) hlast,
      memoryAfter_last_write initial address value (fun _ => true) hpt hp.2 rfl hlast]
  · have hnone : ∀ u < t, z ≠ address u := by
      intro u hut hzu
      exact hne ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hut, hzu⟩⟩
    rw [memoryAfter_no_write initial address value keep (Nat.zero_le t)
      (fun u _ hut _ => hnone u hut),
      memoryAfter_no_write initial address value (fun _ => true) (Nat.zero_le t)
      (fun u _ hut _ => hnone u hut)]
    rfl

open Transpose

namespace ExecutionPrefix

variable {M : TM} {w : List Bool} {T : ℕ} (E : ExecutionPrefix M w T)

def written (h : Fin M.k) (t : ℕ) : Fin (M.g + 1) :=
  (E.config (t + 1)).work h ((E.config t).workPos h)

theorem work_eq_memoryAfter (h : Fin M.k) {t : ℕ} (ht : t ≤ T) (z : ℤ) :
    (E.config t).work h z = memoryAfter (fun _ => 0)
      (fun u => (E.config u).workPos h) (E.written h) (fun _ => true) t z := by
  induction t with
  | zero => simp [E.initial, init, memoryAfter]
  | succ t ih =>
    rw [step_work_update (E.successful t (by omega)) h z]
    simp only [memoryAfter, Bool.true_and, decide_eq_true_eq]
    split_ifs with hz
    · rfl
    · exact ih (by omega)

/-- Actual native last-visit closure validates the filtered dictionary at a read. -/
theorem filtered_native_read (keep : ℕ → Bool) (h : Fin M.k) {t : ℕ} (ht : t ≤ T)
    (hparent : ∀ p < t, (E.config t).workPos h = (E.config p).workPos h →
      (∀ u, p < u → u < t → (E.config t).workPos h ≠ (E.config u).workPos h) →
      keep p = true) :
    memoryAfter (fun _ => 0) (fun u => (E.config u).workPos h)
      (E.written h) keep t ((E.config t).workPos h) =
      (E.config t).work h ((E.config t).workPos h) := by
  rw [E.work_eq_memoryAfter h ht]
  exact filtered_read_correct _ _ _ _ _ _ hparent

end ExecutionPrefix
end AdaptiveTransfer
