import AdaptiveTransfer.ReplayCounting
import NativeRelations.OneFreeHeadSmallExcursion
import LeanMachine.SparseBinomial

/-! Canonical finite run geometry for native adaptive replay. Output coverage
is derived from recorded entry/exit counters, and raw inclusion from the
recorded extrema. No omitted-coordinate recovery certificate is supplied. -/

namespace AdaptiveTransfer

open Transpose Finset NativeRelations LeanMachine
open scoped BigOperators

theorem exists_run_cover {C : Finset ℕ} {T : ℕ}
    (hCT : ∀ t ∈ C, t < T) {t : ℕ} (ht : t ∈ C) :
    ∃ r ∈ runStarts C, r ≤ t ∧ t < runEnd C T r := by
  have hh : t ∈ (runStarts C).biUnion (fun r => Ico r (runEnd C T r)) := by
    rw [← eq_biUnion_runInterval hCT]
    exact ht
  obtain ⟨r, hr, ht⟩ := mem_biUnion.mp hh
  exact ⟨r, hr, mem_Ico.mp ht⟩

noncomputable def replayEntry (C : Finset ℕ) (T : ℕ)
    (hCT : ∀ t ∈ C, t < T) (t : ℕ) : ℕ :=
  if ht : t ∈ C then (exists_run_cover hCT ht).choose else 0

theorem replayEntry_spec {C : Finset ℕ} {T : ℕ}
    (hCT : ∀ t ∈ C, t < T) {t : ℕ} (ht : t ∈ C) :
    replayEntry C T hCT t ∈ runStarts C ∧ replayEntry C T hCT t ≤ t ∧
      t < runEnd C T (replayEntry C T hCT t) := by
  simpa only [replayEntry, dite_eq_left ht] using (exists_run_cover hCT ht).choose_spec

def rawExtent (C : Finset ℕ) (lo hi : ℕ → ℤ) : Set ℤ :=
  {z | ∃ r ∈ runStarts C, lo r ≤ z ∧ z ≤ hi r}

noncomputable def recordedOrdinals (P : ℕ) (C : Finset ℕ) (lo hi : ℕ → ℕ) :
    Finset (Fin P) :=
  (runStarts C).biUnion fun r => univ.filter fun j => lo r ≤ j.val ∧ j.val < hi r

noncomputable def geometryOmitted {P : ℕ} (π : Fin P → Fin P) (C : Finset ℕ)
    (outLo outHi : ℕ → ℕ) (rawLo rawHi : ℕ → ℤ) : Finset (Fin P) := by
  classical
  exact (recordedOrdinals P C outLo outHi).image π \
    univ.filter (fun p => (p.val : ℤ) ∈ rawExtent C rawLo rawHi)

theorem geometryOmitted_raw_disjoint {P : ℕ} (π : Fin P → Fin P) (C : Finset ℕ)
    (outLo outHi : ℕ → ℕ) (rawLo rawHi : ℕ → ℤ) :
    ∀ p : Fin P, (p.val : ℤ) ∈ rawExtent C rawLo rawHi →
      p ∉ geometryOmitted π C outLo outHi rawLo rawHi := by
  classical
  intro p hp hu
  exact (mem_sdiff.mp hu).2 (mem_filter.mpr ⟨mem_univ _, hp⟩)

/-- Counter intervals provide actual append witnesses inside the literal
maximal runs. The witness may be at a different time in different inputs. -/
theorem geometryOmitted_output_cover {M : TM} {P T : ℕ} {X : Fin P → Bool}
    (E : ExecutionPrefix M (List.ofFn X) T) (π : Fin P → Fin P) (C : Finset ℕ)
    (hCT : ∀ t ∈ C, t < T) (outLo outHi : ℕ → ℕ) (rawLo rawHi : ℕ → ℤ)
    (hlo : ∀ r ∈ runStarts C, (E.config r).outRev.length = outLo r)
    (hhi : ∀ r ∈ runStarts C, (E.config (runEnd C T r)).outRev.length = outHi r) :
    ∀ p ∈ geometryOmitted π C outLo outHi rawLo rawHi, ∃ t ∈ C, ∃ j : Fin P,
      π j = p ∧ (E.config t).outRev.length = j.val ∧ (E.emitted t).isSome := by
  classical
  intro p hp
  obtain ⟨j, hj, hjp⟩ := mem_image.mp (mem_sdiff.mp hp).1
  obtain ⟨r, hr, hj⟩ := mem_biUnion.mp hj
  have hj' := (mem_filter.mp hj).2
  have hrend := runEnd_spec hCT hr
  obtain ⟨t, hat, hte, hc, ho⟩ := E.exists_append_between hrend.1.le hrend.2.1
    (by simpa only [hlo r hr] using hj'.1) (by simpa only [hhi r hr] using hj'.2)
  exact ⟨t, hrend.2.2.2 t (mem_Ico.mpr ⟨hat, hte⟩), j, hjp, hc, ho⟩

theorem rawExtent_contains_reads {M : TM} {P T : ℕ} {X : Fin P → Bool}
    (E : ExecutionPrefix M (List.ofFn X) T) (C : Finset ℕ)
    (hCT : ∀ t ∈ C, t < T) (rawLo rawHi : ℕ → ℤ)
    (hextrema : ∀ r ∈ runStarts C, ∀ t ∈ Ico r (runEnd C T r),
      rawLo r ≤ (E.config t).inPos ∧ (E.config t).inPos ≤ rawHi r) :
    ∀ t ∈ C, (E.config t).inPos ∈ rawExtent C rawLo rawHi := by
  intro t ht
  obtain ⟨r, hr, hrt, hte⟩ := exists_run_cover hCT ht
  exact ⟨r, hr, hextrema r hr t (mem_Ico.mpr ⟨hrt, hte⟩)⟩

theorem integerSlab_card (ell : ℤ) (W : ℕ) :
    (Ico ell (ell + (W : ℤ))).card = W := by
  simp

/-- The finite adaptive replay bound with canonical maximal-run geometry.
Demanded coordinates are literally outputs minus the raw-extrema union.
Output coverage, raw inclusion, entry membership and retained prefixes are
proved here, rather than being supplied as reconstruction hypotheses. -/
theorem native_fixed_geometry_replay_bound {M : TM} {P T : ℕ}
    (D : Finset (Fin P → Bool)) (E : ∀ X : D, ExecutionPrefix M (List.ofFn X.val) T)
    (π : Fin P → Fin P) (C : Finset ℕ) (S : Finset ℤ) (a H N J : ℕ) (f : Fin M.k)
    (hCT : ∀ t ∈ C, t < T) (hCa : ∀ t ∈ C, a ≤ t) (hN : T ≤ N)
    (hcarrier : ∀ X : D, ∀ t, a ≤ t → t < T →
      (t ∈ C ↔ ((E X).config t).workPos f ∈ S))
    (workEntry : ℕ → Fin M.k → ℤ) (rawEntry rawLo rawHi : ℕ → ℤ)
    (outLo outHi : ℕ → ℕ)
    (hwork : ∀ X : D, ∀ r ∈ runStarts C, ((E X).config r).workPos = workEntry r)
    (hrawEntry : ∀ X : D, ∀ r ∈ runStarts C, ((E X).config r).inPos = rawEntry r)
    (houtLo : ∀ X : D, ∀ r ∈ runStarts C, ((E X).config r).outRev.length = outLo r)
    (houtHi : ∀ X : D, ∀ r ∈ runStarts C,
      ((E X).config (runEnd C T r)).outRev.length = outHi r)
    (hextrema : ∀ X : D, ∀ r ∈ runStarts C, ∀ t ∈ Ico r (runEnd C T r),
      rawLo r ≤ ((E X).config t).inPos ∧ ((E X).config t).inPos ≤ rawHi r)
    (htag : ∀ X, (recordSupport (fun _ => none)
      (incomingFields (E X) N H C (replayEntry C T hCT) f)).card ≤ J)
    (finish : D → ℕ) (hfinish : ∀ X, T ≤ finish X)
    (houtput : ∀ X : D,
      (Transpose.Tape.run M (List.ofFn X.val) (finish X)).outRev.reverse =
        List.ofFn (fun j => X.val (π j))) :
    D.card ≤ 2 ^ (P - (geometryOmitted π C outLo outHi rawLo rawHi).card) *
      (M.q + 1) ^ (runStarts C).card *
      (M.g + 1) ^ ((if a = 0 then 0 else S.card) +
        (M.k - 1) * (runStarts C).card * (2 * H + 1)) *
      ∑ j ∈ range (min ((M.k - 1) * N) J + 1),
        ((M.k - 1) * N).choose j * (M.g + 1) ^ j := by
  rw [← sparseMenu_truncate]
  apply adaptive_replay_card_bound D E
    (geometryOmitted π C outLo outHi rawLo rawHi) (runStarts C) C S a H N J f
    (replayEntry C T hCT) workEntry htag π rawEntry outLo finish
    (rawExtent C rawLo rawHi) (fun t ht => ⟨hCa t ht, hCT t ht⟩) hN hcarrier
  · intro t ht
    have he := replayEntry_spec hCT ht
    exact ⟨hCa _ (mem_filter.mp he.1).1, he.2.1⟩
  · intro t ht u heu hut
    have he := replayEntry_spec hCT ht
    exact (runEnd_spec hCT he.1).2.2.2 u (mem_Ico.mpr ⟨heu, hut.trans_lt he.2.2⟩)
  · exact fun t ht => (replayEntry_spec hCT ht).1
  · exact hwork
  · exact hrawEntry
  · exact houtLo
  · exact fun X => rawExtent_contains_reads (E X) C hCT rawLo rawHi (hextrema X)
  · exact geometryOmitted_raw_disjoint π C outLo outHi rawLo rawHi
  · exact fun X => geometryOmitted_output_cover (E X) π C hCT outLo outHi rawLo rawHi
      (houtLo X) (houtHi X)
  · exact hfinish
  · exact houtput

end AdaptiveTransfer
