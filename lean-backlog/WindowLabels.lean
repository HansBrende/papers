import MergeDepth.BlockDag
import Transpose.Tape.DefsP
import Transpose.Tape.Locality

/-!
# Native visits, intervals, and last-window labels

These adapters use actual unit-speed head trajectories and the existing native
last-visit/dependency definitions.  Packing the resulting integer-indexed
labels into the finite list of `WindowAmortization.lean` is not yet done here.

Check from `High-Rate-Separated-Storage-Codes-and-Tape-Transposition/lean/`:
`lake env lean ../../lean-backlog/WindowLabels.lean`.
-/

namespace LeanBacklog.WindowLabels

open Finset BoundedNesting MergeDepth Transpose.Tape Transpose.Tape.Impl

/-- Cells scanned at the before-transition times in `[a,b)`. -/
def visitedCells (x : ℕ → ℤ) (a b : ℕ) : Finset ℤ := (Ico a b).image x

theorem mem_visitedCells {x : ℕ → ℤ} {a b : ℕ} {z : ℤ} :
    z ∈ visitedCells x a b ↔ ∃ t, a ≤ t ∧ t < b ∧ x t = z := by
  simp [visitedCells, and_assoc]

/-- The existing crossing theorem gives the discrete intermediate-value
property, including either direction of motion. -/
theorem exists_visit_between {x : ℕ → ℤ} (hx : IsWalk x) {a b : ℕ}
    (hab : a ≤ b) {z : ℤ}
    (hz : (x a ≤ z ∧ z ≤ x b) ∨ (x b ≤ z ∧ z ≤ x a)) :
    ∃ t, a ≤ t ∧ t ≤ b ∧ x t = z := by
  rcases hz with ⟨ha, hb⟩ | ⟨hb, ha⟩
  · by_cases he : z = x b
    · exact ⟨b, hab, le_rfl, he.symm⟩
    obtain ⟨t, ht₁, ht₂, ht₃, -⟩ := exists_up_crossing hx (c := z)
      (b - a) a ha (by rw [Nat.add_sub_of_le hab]; omega)
    exact ⟨t, ht₁, by omega, ht₃⟩
  · by_cases he : z = x a
    · exact ⟨a, le_rfl, hab, he.symm⟩
    obtain ⟨t, ht₁, ht₂, -, ht₄⟩ := exists_down_crossing hx (c := z)
      (b - a) a (by omega) (by rwa [Nat.add_sub_of_le hab])
    exact ⟨t + 1, by omega, by omega, ht₄⟩

/-- The actual visited set of one consecutive window is an interval. -/
theorem visitedCells_between {x : ℕ → ℤ} (hx : IsWalk x) {a b : ℕ}
    {u v z : ℤ} (hu : u ∈ visitedCells x a b) (hv : v ∈ visitedCells x a b)
    (huz : u ≤ z) (hzv : z ≤ v) : z ∈ visitedCells x a b := by
  obtain ⟨p, hpa, hpb, rfl⟩ := mem_visitedCells.mp hu
  obtain ⟨q, hqa, hqb, rfl⟩ := mem_visitedCells.mp hv
  rcases le_total p q with hpq | hqp
  · obtain ⟨t, hpt, htq, htz⟩ := exists_visit_between hx hpq (Or.inl ⟨huz, hzv⟩)
    exact mem_visitedCells.mpr ⟨t, by omega, by omega, htz⟩
  · obtain ⟨t, hqt, htp, htz⟩ := exists_visit_between hx hqp (Or.inr ⟨huz, hzv⟩)
    exact mem_visitedCells.mpr ⟨t, by omega, by omega, htz⟩

theorem visitedCells_eq_Icc {x : ℕ → ℤ} (hx : IsWalk x) {a b : ℕ}
    (hne : (visitedCells x a b).Nonempty) :
    visitedCells x a b = Icc ((visitedCells x a b).min' hne)
      ((visitedCells x a b).max' hne) := by
  ext z
  constructor
  · intro hz
    exact mem_Icc.mpr ⟨min'_le _ _ hz, le_max' _ _ hz⟩
  · intro hz
    exact visitedCells_between hx (min'_mem _ hne) (max'_mem _ hne)
      (mem_Icc.mp hz).1 (mem_Icc.mp hz).2

/-- Every finite native walk fits in this fixed nonempty spatial interval. -/
theorem visitedCells_subset_fixed_span {x : ℕ → ℤ} (hx : IsWalk x) (T : ℕ) :
    visitedCells x 0 T ⊆ Icc (x 0 - T) (x 0 + T) := by
  intro z hz
  obtain ⟨t, -, ht, rfl⟩ := mem_visitedCells.mp hz
  have h := hx.lip (Nat.zero_le t)
  simp only [Nat.sub_zero] at h
  exact mem_Icc.mpr ⟨by omega, by omega⟩

/-- Reuse `prevS` by replacing only the queried endpoint with the requested
cell. Every earlier position is unchanged. -/
noncomputable def lastBefore (x : ℕ → ℤ) (cut : ℕ) (z : ℤ) : Option ℕ :=
  prevS (Function.update x cut z) cut

theorem lastBefore_eq_some_iff {x : ℕ → ℤ} {cut p : ℕ} {z : ℤ} :
    lastBefore x cut z = some p ↔ IsLastVisitTo x z cut p := by
  rw [lastBefore, prevS_spec]
  simp only [Function.update_self, IsLastVisitTo]
  constructor
  · rintro ⟨hp, heq, hgap⟩
    refine ⟨hp, ?_, fun r hpr hrc => ?_⟩
    · simpa [Function.update_of_ne (ne_of_lt hp)] using heq
    · simpa [Function.update_of_ne (ne_of_lt hrc)] using hgap r hpr hrc
  · rintro ⟨hp, heq, hgap⟩
    refine ⟨hp, ?_, fun r hpr hrc => ?_⟩
    · simpa [Function.update_of_ne (ne_of_lt hp)] using heq
    · simpa [Function.update_of_ne (ne_of_lt hrc)] using hgap r hpr hrc

theorem lastBefore_eq_none_iff {x : ℕ → ℤ} {cut : ℕ} {z : ℤ} :
    lastBefore x cut z = none ↔ ∀ p < cut, x p ≠ z := by
  constructor
  · intro hnone p hp hpz
    obtain ⟨u, -, hu, huz, hgap⟩ := exists_lastVisit_from
      (a := 0) ⟨p, Nat.zero_le _, hp, hpz⟩
    have := lastBefore_eq_some_iff.mpr (show IsLastVisitTo x z cut u from ⟨hu, huz, hgap⟩)
    simp [hnone] at this
  · intro h
    cases he : lastBefore x cut z with
    | none => rfl
    | some p =>
      have hp := lastBefore_eq_some_iff.mp he
      exact (h p hp.1 hp.2.1).elim

theorem lastBefore_unchanged {x : ℕ → ℤ} {a b : ℕ} {z : ℤ}
    (hab : a ≤ b) (hno : z ∉ visitedCells x a b) :
    lastBefore x b z = lastBefore x a z := by
  have hn : ∀ p, a ≤ p → p < b → x p ≠ z := by
    intro p hpa hpb hpz
    exact hno (mem_visitedCells.mpr ⟨p, hpa, hpb, hpz⟩)
  apply Option.ext
  intro p
  simp only [lastBefore_eq_some_iff]
  constructor
  · rintro ⟨hp, hpz, hgap⟩
    have hpa : p < a := by
      by_contra h
      exact hn p (by omega) hp hpz
    exact ⟨hpa, hpz, fun r hpr hra => hgap r hpr (lt_of_lt_of_le hra hab)⟩
  · rintro ⟨hp, hpz, hgap⟩
    refine ⟨lt_of_lt_of_le hp hab, hpz, fun r hpr hrb => ?_⟩
    by_cases hra : r < a
    · exact hgap r hpr hra
    · exact hn r (by omega) hrb

/-- The last scanned WINDOW label before a cut; `none` means never visited. -/
noncomputable def windowLabel (x : ℕ → ℤ) (h cut : ℕ) (z : ℤ) : Option ℕ :=
  (lastBefore x cut z).map (fun p => p / h)

theorem windowLabel_eq_some_iff {x : ℕ → ℤ} {h cut j : ℕ} {z : ℤ} :
    windowLabel x h cut z = some j ↔
      ∃ p, IsLastVisitTo x z cut p ∧ p / h = j := by
  simp only [windowLabel, Option.map_eq_some_iff, lastBefore_eq_some_iff]

@[simp] theorem windowLabel_zero (x : ℕ → ℤ) (h : ℕ) (z : ℤ) :
    windowLabel x h 0 z = none := by
  rw [windowLabel, lastBefore_eq_none_iff.mpr (by omega)]
  rfl

/-- Exact pointwise overwrite on an actual time window, including a shortened
last window. No unit-speed assumption is needed for this label identity. -/
theorem windowLabel_overwrite {x : ℕ → ℤ} {h i b : ℕ}
    (hstart : i * h ≤ b) (hend : b ≤ (i + 1) * h) (z : ℤ) :
    windowLabel x h b z =
      if z ∈ visitedCells x (i * h) b then some i else windowLabel x h (i * h) z := by
  classical
  split_ifs with hz
  · obtain ⟨p, hpa, hpb, hpz, hgap⟩ := exists_lastVisit_from (mem_visitedCells.mp hz)
    have hp : lastBefore x b z = some p :=
      lastBefore_eq_some_iff.mpr ⟨hpb, hpz, hgap⟩
    have hdiv : p / h = i := by
      apply Nat.div_eq_of_lt_le
      · exact hpa
      · omega
    simp [windowLabel, hp, hdiv]
  · simp only [windowLabel, lastBefore_unchanged hstart hz]

/-- The clipped boundaries used for a finite horizon satisfy the same exact
update, including zero-length windows beyond the horizon. -/
theorem windowLabel_overwrite_clipped (x : ℕ → ℤ) (h T i : ℕ) (z : ℤ) :
    windowLabel x h (min T ((i + 1) * h)) z =
      if z ∈ visitedCells x (min T (i * h)) (min T ((i + 1) * h)) then some i
      else windowLabel x h (min T (i * h)) z := by
  by_cases hi : i * h ≤ T
  · rw [min_eq_right hi]
    apply windowLabel_overwrite
    · exact le_min hi (Nat.mul_le_mul_right h (by omega))
    · exact min_le_right _ _
  · have hi' : T ≤ i * h := by omega
    have hj : T ≤ (i + 1) * h := hi'.trans (Nat.mul_le_mul_right h (by omega))
    simp [min_eq_left hi', min_eq_left hj, visitedCells]

/-- A nonempty native window literally overwrites the integer interval
between its extremal visited cells. No interval premise is assumed. -/
theorem windowLabel_interval_overwrite {x : ℕ → ℤ} (hx : IsWalk x)
    {h i b : ℕ} (hstart : i * h ≤ b) (hend : b ≤ (i + 1) * h)
    (hne : (visitedCells x (i * h) b).Nonempty) (z : ℤ) :
    windowLabel x h b z =
      if z ∈ Icc ((visitedCells x (i * h) b).min' hne)
        ((visitedCells x (i * h) b).max' hne) then some i
      else windowLabel x h (i * h) z := by
  rw [windowLabel_overwrite hstart hend]
  exact congrArg (fun S : Finset ℤ =>
    if z ∈ S then some i else windowLabel x h (i * h) z) (visitedCells_eq_Icc hx hne)

/-- A last pre-window visit is the actual previous visit at the first
occurrence of that cell in the window, including the window's first step. -/
theorem exists_first_visit_with_predecessor {x : ℕ → ℤ} {a b p : ℕ} {z : ℤ}
    (hprev : lastBefore x a z = some p) (hz : z ∈ visitedCells x a b) :
    ∃ q, a ≤ q ∧ q < b ∧ x q = z ∧ IsLastVisit x q p := by
  classical
  have hex := mem_visitedCells.mp hz
  let q := Nat.find hex
  have hq : a ≤ q ∧ q < b ∧ x q = z := Nat.find_spec hex
  obtain ⟨hp, hpz, hgap⟩ := lastBefore_eq_some_iff.mp hprev
  refine ⟨q, hq.1, hq.2.1, hq.2.2, by omega, hpz.trans hq.2.2.symm, ?_⟩
  intro r hpr hrq hreq
  have hrz : x r = z := hreq.trans hq.2.2
  by_cases hra : r < a
  · exact hgap r hpr hra hrz
  · exact Nat.find_min hex hrq ⟨by omega, by omega, hrz⟩

/-- The predecessor is an edge of the existing native dependency relation;
the result includes pauses via the state-edge case in `blockStep_iff`. -/
theorem exists_native_predecessor {k : ℕ} (xs : Fin k → ℕ → ℤ) (head : Fin k)
    {a b T p : ℕ} {z : ℤ} (hbT : b ≤ T)
    (hprev : lastBefore (xs head) a z = some p)
    (hz : z ∈ visitedCells (xs head) a b) :
    ∃ q, a ≤ q ∧ q < b ∧ xs head q = z ∧ DepStep xs T q p := by
  obtain ⟨q, hqa, hqb, hqz, hlast⟩ := exists_first_visit_with_predecessor hprev hz
  refine ⟨q, hqa, hqb, hqz, (blockStep_iff xs T q p).mp ?_⟩
  exact ⟨lt_of_lt_of_le hqb hbT, Or.inr ⟨head, prevS_spec.mpr hlast⟩⟩

#print axioms visitedCells_eq_Icc
#print axioms windowLabel_eq_some_iff
#print axioms windowLabel_interval_overwrite
#print axioms windowLabel_overwrite_clipped
#print axioms exists_native_predecessor

end LeanBacklog.WindowLabels
