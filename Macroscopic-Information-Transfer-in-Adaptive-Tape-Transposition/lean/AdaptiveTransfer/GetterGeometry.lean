import AdaptiveTransfer.GetterCounting
import AdaptiveTransfer.SlabGeometryAdapters

/-! Literal multiport extremum and pre-entry visit-interval metadata for getter
replay. Output coverage and raw-window inclusion are derived from those actual
records, rather than being supplied as reconstruction certificates.
-/

namespace AdaptiveTransfer.Getter

open Transpose Transpose.Tape Transpose.Tape.Impl Finset NativeRelations MergeDepth BoundedNesting
open LeanMachine
open scoped BigOperators

noncomputable def visitInterval (x : ℕ → ℤ) (a : ℕ) : Option (ℤ × ℤ) :=
  if h : ((range a).image x).Nonempty then
    some (((range a).image x).min' h, ((range a).image x).max' h) else none

def intervalCells : Option (ℤ × ℤ) → Finset ℤ
  | none => ∅
  | some (lo, hi) => Icc lo hi

/-- A successful unit walk's strictly pre-entry visit set is exactly empty or
one integer interval; the arrival position is not added. -/
theorem intervalCells_visitInterval {x : ℕ → ℤ} (hx : IsWalk x) (a : ℕ) :
    intervalCells (visitInterval x a) = (range a).image x := by
  by_cases ha : a = 0
  · subst a; simp [visitInterval, intervalCells]
  · have hne : ((range a).image x).Nonempty :=
      ⟨x 0, mem_image.mpr ⟨0, mem_range.mpr (by omega), rfl⟩⟩
    simp only [visitInterval, dite_eq_left hne, intervalCells]
    simpa only [Nat.Ico_zero_eq_range] using (walk_image_Ico_eq_Icc hx (show 0 < a by omega)).symm

theorem visitedBefore_eq_interval {M : TM} {w : List Bool} {T a : ℕ}
    (E : ExecutionPrefix M w T) (ha : a ≤ T) (h : Fin M.k) :
    visitedBefore E a h = intervalCells (visitInterval (fun t => (Transpose.Tape.run M w t).workPos h) a) := by
  have hx : IsWalk (fun t => (Transpose.Tape.run M w t).workPos h) := by
    simpa only [workPos_eq_work] using (trace M w).work_isWalk h
  rw [intervalCells_visitInterval hx]
  unfold visitedBefore
  apply image_congr
  intro u hu
  dsimp only
  rw [E.config_eq_run ((mem_range.mp hu).le.trans ha)]

def portExtent {p : ℕ} (C : Finset ℕ) (lo hi : ℕ → Fin p → ℤ) (R : ℕ) : Set ℤ :=
  {z | ∃ r ∈ runStarts C, ∃ j, lo r j - R ≤ z ∧ z ≤ hi r j + R}

noncomputable def omittedByExtent {P : ℕ} (π : Fin P → Fin P) (C : Finset ℕ)
    (outLo outHi : ℕ → ℕ) (I : Set ℤ) : Finset (Fin P) := by
  classical
  exact (recordedOrdinals P C outLo outHi).image π \ univ.filter (fun q => (q.val : ℤ) ∈ I)

theorem omittedByExtent_disjoint {P : ℕ} (π : Fin P → Fin P) (C : Finset ℕ)
    (outLo outHi : ℕ → ℕ) (I : Set ℤ) :
    ∀ q : Fin P, (q.val : ℤ) ∈ I → q ∉ omittedByExtent π C outLo outHi I := by
  classical
  intro q hq hu
  exact (mem_sdiff.mp hu).2 (mem_filter.mpr ⟨mem_univ _, hq⟩)

theorem portExtent_contains_windows {p T : ℕ} (ports : ℕ → Fin p → ℤ)
    (C : Finset ℕ) (hCT : ∀ t ∈ C, t < T) (lo hi : ℕ → Fin p → ℤ) (R : ℕ)
    (hextrema : ∀ r ∈ runStarts C, ∀ t ∈ Ico r (runEnd C T r), ∀ j,
      lo r j ≤ ports t j ∧ ports t j ≤ hi r j) :
    ∀ t ∈ C, ∀ j i, windowAddress (ports t j) R i ∈ portExtent C lo hi R := by
  intro t ht j i
  obtain ⟨r, hr, hrt, hte⟩ := exists_run_cover hCT ht
  have hx := hextrema r hr t (mem_Ico.mpr ⟨hrt, hte⟩) j
  refine ⟨r, hr, j, ?_⟩
  have hi' := i.isLt
  dsimp [windowAddress]
  constructor <;> omega

/-- The demanded set is outputs minus the entire declared raw-window extent.
Actual append witnesses follow from entry/exit counters. -/
theorem omittedByExtent_output_cover {M : TM} {P T : ℕ} {X : Fin P → Bool}
    (E : ExecutionPrefix M (List.ofFn X) T) (π : Fin P → Fin P) (C : Finset ℕ)
    (hCT : ∀ t ∈ C, t < T) (outLo outHi : ℕ → ℕ) (I : Set ℤ)
    (hlo : ∀ r ∈ runStarts C, (E.config r).outRev.length = outLo r)
    (hhi : ∀ r ∈ runStarts C, (E.config (runEnd C T r)).outRev.length = outHi r) :
    ∀ q ∈ omittedByExtent π C outLo outHi I, ∃ t ∈ C, ∃ j : Fin P,
      π j = q ∧ (E.config t).outRev.length = j.val ∧ (E.emitted t).isSome := by
  classical
  intro q hq
  obtain ⟨j, hj, hjq⟩ := mem_image.mp (mem_sdiff.mp hq).1
  obtain ⟨r, hr, hj⟩ := mem_biUnion.mp hj
  have hj' := (mem_filter.mp hj).2
  have hrend := runEnd_spec hCT hr
  obtain ⟨t, hat, hte, hc, ho⟩ := E.exists_append_between hrend.1.le hrend.2.1
    (by simpa only [hlo r hr] using hj'.1) (by simpa only [hhi r hr] using hj'.2)
  exact ⟨t, hrend.2.2.2 t (mem_Ico.mpr ⟨hat, hte⟩), j, hjq, hc, ho⟩

variable {M : TM} {U Λ : Type*} [Fintype U] [Fintype Λ] {v R P T : ℕ}

/-- Complete fixed-geometry bound for actual native getters. Raw inclusion,
output witnesses, retained prefixes, and the exact past-visit sets are derived.
The only sparse budget is on the actual computed correction records. -/
theorem native_fixed_geometry_bound
    (D : Finset (Fin P → Bool)) (E : ∀ X : D, ExecutionPrefix M (List.ofFn X.val) T)
    (A : Observer M U v R) (G : Getters M U Λ v R) (labels : D → Λ)
    (π : Fin P → Fin P) (hπ : Function.Injective π) (C : Finset ℕ) (slab : Finset ℤ)
    (a H N J : ℕ) (f : Fin M.k) (hCT : ∀ t ∈ C, t < T) (hCa : ∀ t ∈ C, a ≤ t) (hN : T ≤ N)
    (hcarrier : ∀ X : D, ∀ t, a ≤ t → t < T →
      (t ∈ C ↔ ((E X).config t).workPos f ∈ slab))
    (workEntry : ℕ → Fin M.k → ℤ) (portEntry portLo portHi : ℕ → Fin (v + 1) → ℤ)
    (past : ℕ → Fin M.k → Option (ℤ × ℤ)) (outLo outHi : ℕ → ℕ)
    (hwork : ∀ X : D, ∀ r ∈ runStarts C, ((E X).config r).workPos = workEntry r)
    (hportEntry : ∀ X : D, ∀ r ∈ runStarts C, A.allPorts (List.ofFn X.val) r = portEntry r)
    (hpast : ∀ X : D, ∀ r ∈ runStarts C, ∀ h, h ≠ f →
      visitInterval (fun t => (Transpose.Tape.run M (List.ofFn X.val) t).workPos h) r = past r h)
    (houtLo : ∀ X : D, ∀ r ∈ runStarts C, ((E X).config r).outRev.length = outLo r)
    (houtHi : ∀ X : D, ∀ r ∈ runStarts C, ((E X).config (runEnd C T r)).outRev.length = outHi r)
    (hextrema : ∀ X : D, ∀ r ∈ runStarts C, ∀ t ∈ Ico r (runEnd C T r), ∀ j,
      portLo r j ≤ A.allPorts (List.ofFn X.val) t j ∧ A.allPorts (List.ofFn X.val) t j ≤ portHi r j)
    (htag : ∀ X, (recordSupport (fun _ => none)
      (errorFields (E X) A G (labels X) N H C (replayEntry C T hCT) f)).card ≤ J)
    (finish : D → ℕ) (hfinish : ∀ X, T ≤ finish X)
    (houtput : ∀ X : D,
      (Transpose.Tape.run M (List.ofFn X.val) (finish X)).outRev.reverse = List.ofFn (fun j => X.val (π j))) :
    D.card ≤ 2 ^ (P - (omittedByExtent π C outLo outHi (portExtent C portLo portHi R)).card) *
      Fintype.card Λ * ((M.q + 1) * Fintype.card U) ^ (runStarts C).card *
      (M.g + 1) ^ ((if a = 0 then 0 else slab.card) + (M.k - 1) * (runStarts C).card * (2 * H + 1)) *
      ∑ j ∈ range (min ((M.k - 1) * N) J + 1), ((M.k - 1) * N).choose j * (M.g + 1) ^ j := by
  rw [← sparseMenu_truncate]
  apply card_bound D E A G labels
    (omittedByExtent π C outLo outHi (portExtent C portLo portHi R)) (runStarts C) C slab a H N J f
    (replayEntry C T hCT) workEntry htag π hπ (fun r => portEntry r 0)
    (fun r j => portEntry r j.succ) (fun r h => intervalCells (past r h)) outLo finish
    (portExtent C portLo portHi R) (fun t ht => ⟨hCa t ht, hCT t ht⟩) hN hcarrier
  · intro t ht
    have he := replayEntry_spec hCT ht
    exact ⟨hCa _ (mem_filter.mp he.1).1, he.2.1⟩
  · intro t ht u heu hut
    have he := replayEntry_spec hCT ht
    exact (runEnd_spec hCT he.1).2.2.2 u (mem_Ico.mpr ⟨heu, hut.trans_lt he.2.2⟩)
  · exact fun t ht => (replayEntry_spec hCT ht).1
  · exact hwork
  · intro X r hr
    have hh := congrFun (hportEntry X r hr) 0
    simpa only [Observer.allPorts_zero, ← (E X).config_eq_run (hCT r (mem_filter.mp hr).1).le] using hh
  · intro X r hr
    funext j
    exact congrFun (hportEntry X r hr) j.succ
  · intro X r hr h hh
    rw [visitedBefore_eq_interval (E X) (hCT r (mem_filter.mp hr).1).le h, hpast X r hr h hh]
  · exact houtLo
  · exact fun X => portExtent_contains_windows (A.allPorts (List.ofFn X.val)) C hCT portLo portHi R (hextrema X)
  · exact omittedByExtent_disjoint π C outLo outHi _
  · exact fun X => omittedByExtent_output_cover (E X) π C hCT outLo outHi _ (houtLo X) (houtHi X)
  · exact hfinish
  · exact houtput

/-- The manuscript's literal bit exponent. Virtual-port positions remain
geometry; only native/observer finite state is charged to q, and the label is
charged exactly once. -/
theorem native_fixed_geometry_bits_bound
    (D : Finset (Fin P → Bool)) (E : ∀ X : D, ExecutionPrefix M (List.ofFn X.val) T)
    (A : Observer M U v R) (G : Getters M U Λ v R) (labels : D → Λ)
    (π : Fin P → Fin P) (hπ : Function.Injective π) (C : Finset ℕ) (slab : Finset ℤ)
    (a H N J q z : ℕ) (f : Fin M.k) (hCT : ∀ t ∈ C, t < T) (hCa : ∀ t ∈ C, a ≤ t) (hN : T ≤ N)
    (hcarrier : ∀ X : D, ∀ t, a ≤ t → t < T →
      (t ∈ C ↔ ((E X).config t).workPos f ∈ slab))
    (workEntry : ℕ → Fin M.k → ℤ) (portEntry portLo portHi : ℕ → Fin (v + 1) → ℤ)
    (past : ℕ → Fin M.k → Option (ℤ × ℤ)) (outLo outHi : ℕ → ℕ)
    (hwork : ∀ X : D, ∀ r ∈ runStarts C, ((E X).config r).workPos = workEntry r)
    (hportEntry : ∀ X : D, ∀ r ∈ runStarts C, A.allPorts (List.ofFn X.val) r = portEntry r)
    (hpast : ∀ X : D, ∀ r ∈ runStarts C, ∀ h, h ≠ f →
      visitInterval (fun t => (Transpose.Tape.run M (List.ofFn X.val) t).workPos h) r = past r h)
    (houtLo : ∀ X : D, ∀ r ∈ runStarts C, ((E X).config r).outRev.length = outLo r)
    (houtHi : ∀ X : D, ∀ r ∈ runStarts C, ((E X).config (runEnd C T r)).outRev.length = outHi r)
    (hextrema : ∀ X : D, ∀ r ∈ runStarts C, ∀ t ∈ Ico r (runEnd C T r), ∀ j,
      portLo r j ≤ A.allPorts (List.ofFn X.val) t j ∧ A.allPorts (List.ofFn X.val) t j ≤ portHi r j)
    (htag : ∀ X, (recordSupport (fun _ => none)
      (errorFields (E X) A G (labels X) N H C (replayEntry C T hCT) f)).card ≤ J)
    (finish : D → ℕ) (hfinish : ∀ X, T ≤ finish X)
    (houtput : ∀ X : D,
      (Transpose.Tape.run M (List.ofFn X.val) (finish X)).outRev.reverse = List.ofFn (fun j => X.val (π j)))
    (hq : (M.q + 1) * Fintype.card U ≤ 2 ^ q) (hz : Fintype.card Λ ≤ 2 ^ z) :
    D.card ≤ 2 ^ (P - (omittedByExtent π C outLo outHi (portExtent C portLo portHi R)).card +
      z + (runStarts C).card * q) *
      (M.g + 1) ^ ((if a = 0 then 0 else slab.card) + (M.k - 1) * (runStarts C).card * (2 * H + 1)) *
      ∑ j ∈ range (min ((M.k - 1) * N) J + 1), ((M.k - 1) * N).choose j * (M.g + 1) ^ j := by
  have hc := native_fixed_geometry_bound D E A G labels π hπ C slab a H N J f hCT hCa hN
    hcarrier workEntry portEntry portLo portHi past outLo outHi hwork hportEntry hpast
    houtLo houtHi hextrema htag finish hfinish houtput
  let u := (omittedByExtent π C outLo outHi (portExtent C portLo portHi R)).card
  let r := (runStarts C).card
  have hp : (2 : ℕ) ^ (P - u) * 2 ^ z * (2 ^ q) ^ r = 2 ^ (P - u + z + r * q) := by
    rw [← pow_add, ← pow_mul, ← pow_add, Nat.mul_comm q r]
  calc
    D.card ≤ _ := hc
    _ ≤ (2 ^ (P - u) * 2 ^ z * (2 ^ q) ^ r) *
        (M.g + 1) ^ ((if a = 0 then 0 else slab.card) + (M.k - 1) * r * (2 * H + 1)) *
        ∑ j ∈ range (min ((M.k - 1) * N) J + 1), ((M.k - 1) * N).choose j * (M.g + 1) ^ j := by
      gcongr
    _ = _ := by rw [hp]

end AdaptiveTransfer.Getter
