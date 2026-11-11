import AdaptiveTransfer.MultiCoreReplay
import AdaptiveTransfer.ClusterImports
import AdaptiveTransfer.ReplayGeometry

/-! Actual native replay classes with multiple protected cores. Every message
field is a native state, symbol or exterior bit. The structural core/fringe
premises are local ownership observations, never an assumed input injection. -/

namespace AdaptiveTransfer
open Transpose Finset NativeRelations LeanMachine
open scoped BigOperators

structure CoreReplayClass (M : TM) (P : ℕ) (π : Fin P → Fin P) where
  inputs : Finset (Fin P → Bool)
  horizon : ℕ
  exec : ∀ X : inputs, ExecutionPrefix M (List.ofFn X.val) horizon
  times : Finset ℕ
  cluster : Finset (Fin M.k)
  core : Fin M.k → Finset ℤ
  fringe : Fin M.k → Finset ℤ
  start : ℕ
  radius : ℕ
  limit : ℕ
  tags : ℕ
  time_lt : ∀ t ∈ times, t < horizon
  time_start : ∀ t ∈ times, start ≤ t
  horizon_le : horizon ≤ limit
  outside : ∀ X : inputs, ∀ t, start ≤ t → t < horizon → t ∉ times →
    ∀ h ∈ cluster, ((exec X).config t).workPos h ∉ core h
  selected : ∀ X : inputs, ∀ t ∈ times, ∀ h ∈ cluster,
    ((exec X).config t).workPos h ∈ core h ∪ fringe h
  workEntry : ℕ → Fin M.k → ℤ
  rawEntry : ℕ → ℤ
  rawLo : ℕ → ℤ
  rawHi : ℕ → ℤ
  outLo : ℕ → ℕ
  outHi : ℕ → ℕ
  work_entry : ∀ X : inputs, ∀ r ∈ runStarts times, ((exec X).config r).workPos = workEntry r
  raw_entry : ∀ X : inputs, ∀ r ∈ runStarts times, ((exec X).config r).inPos = rawEntry r
  out_lo : ∀ X : inputs, ∀ r ∈ runStarts times, ((exec X).config r).outRev.length = outLo r
  out_hi : ∀ X : inputs, ∀ r ∈ runStarts times,
    ((exec X).config (runEnd times horizon r)).outRev.length = outHi r
  extrema : ∀ X : inputs, ∀ r ∈ runStarts times, ∀ t ∈ Ico r (runEnd times horizon r),
    rawLo r ≤ ((exec X).config t).inPos ∧ ((exec X).config t).inPos ≤ rawHi r
  tag_bound : ∀ X, (recordSupport (fun _ => none)
    (clusterIncomingFields (exec X) limit radius times (replayEntry times horizon time_lt) cluster)).card ≤ tags
  finish : inputs → ℕ
  finish_ge : ∀ X, horizon ≤ finish X
  output : ∀ X : inputs,
    (Transpose.Tape.run M (List.ofFn X.val) (finish X)).outRev.reverse = List.ofFn (fun j => X.val (π j))

namespace CoreReplayClass
variable {M : TM} {P : ℕ} {π : Fin P → Fin P} (g : CoreReplayClass M P π)

noncomputable def omitted : Finset (Fin P) :=
  geometryOmitted π g.times g.outLo g.outHi g.rawLo g.rawHi

noncomputable def entryCells (r : ℕ) (h : Fin M.k) : Finset ℤ :=
  if h ∈ g.cluster then g.fringe h else Icc (g.workEntry r h - g.radius) (g.workEntry r h + g.radius)

abbrev Exterior := ↑g.omittedᶜ → Bool
abbrev SnapshotDomain := Σ h : Fin M.k, snapshotCells g.start (g.core h)
abbrev EntryDomain := Σ r : runStarts g.times, Σ h : Fin M.k, g.entryCells r.val h
abbrev Ordinary := (runStarts g.times → Fin (M.q + 1)) ×
  (g.SnapshotDomain → Fin (M.g + 1)) × (g.EntryDomain → Fin (M.g + 1))
abbrev Imports := {v : Fin g.limit × Fin M.k → Option (Fin (M.g + 1)) //
  (recordSupport (fun _ => none) v).card ≤ g.tags}

noncomputable instance : Fintype g.Imports := Fintype.ofFinite _

noncomputable def exterior (X : g.inputs) : g.Exterior := fun p => X.val p.val
noncomputable def ordinary (X : g.inputs) : g.Ordinary :=
  ((fun r => ((g.exec X).config r.val).state),
    (fun z => ((g.exec X).config g.start).work z.1 z.2.val),
    (fun z => ((g.exec X).config z.1.val).work z.2.1 z.2.2.val))
noncomputable def imports (X : g.inputs) : g.Imports :=
  ⟨clusterIncomingFields (g.exec X) g.limit g.radius g.times
    (replayEntry g.times g.horizon g.time_lt) g.cluster, g.tag_bound X⟩

variable {g} {X Y : g.inputs}

theorem ordinary_controls (he : g.ordinary X = g.ordinary Y) {r : ℕ} (hr : r ∈ runStarts g.times) :
    SameControl ((g.exec X).config r) ((g.exec Y).config r) :=
  ⟨congrFun (congrArg Prod.fst he) ⟨r, hr⟩,
    (g.raw_entry X r hr).trans (g.raw_entry Y r hr).symm,
    (g.work_entry X r hr).trans (g.work_entry Y r hr).symm⟩

theorem ordinary_cores (he : g.ordinary X = g.ordinary Y) (h : Fin M.k)
    {z : ℤ} (hz : z ∈ g.core h) :
    ((g.exec X).config g.start).work h z = ((g.exec Y).config g.start).work h z := by
  by_cases ha : g.start = 0
  · rw [ha, (g.exec X).initial, (g.exec Y).initial]
  · have hz' : z ∈ snapshotCells g.start (g.core h) := by simp only [snapshotCells, ha, ite_false]; exact hz
    exact congrFun (congrArg (fun o => o.2.1) he) ⟨h, z, hz'⟩

theorem ordinary_entry (he : g.ordinary X = g.ordinary Y) {r : ℕ} (hr : r ∈ runStarts g.times)
    (h : Fin M.k) {z : ℤ} (hz : z ∈ g.entryCells r h) :
    ((g.exec X).config r).work h z = ((g.exec Y).config r).work h z :=
  congrFun (congrArg (fun o => o.2.2) he) ⟨⟨r, hr⟩, h, z, hz⟩

/-- Derived source recovery for actual multi-core class records. -/
theorem records_recover (hext : g.exterior X = g.exterior Y)
    (ho : g.ordinary X = g.ordinary Y) (hi : g.imports X = g.imports Y) : X = Y := by
  classical
  let entry := replayEntry g.times g.horizon g.time_lt
  have hentry (t : ℕ) (ht : t ∈ g.times) : g.start ≤ entry t ∧ entry t ≤ t := by
    have he := replayEntry_spec g.time_lt ht
    exact ⟨g.time_start _ (mem_filter.mp he.1).1, he.2.1⟩
  have hfill (t : ℕ) (ht : t ∈ g.times) (u : ℕ) (heu : entry t ≤ u) (hut : u ≤ t) : u ∈ g.times := by
    have he := replayEntry_spec g.time_lt ht
    exact (runEnd_spec g.time_lt he.1).2.2.2 u (mem_Ico.mpr ⟨heu, hut.trans_lt he.2.2⟩)
  have hentryR (t : ℕ) (ht : t ∈ g.times) : entry t ∈ runStarts g.times := (replayEntry_spec g.time_lt ht).1
  have hext' : ∀ p ∉ g.omitted, X.val p = Y.val p := fun p hp => congrFun hext ⟨p, mem_compl.mpr hp⟩
  have hreplay := (g.exec X).multicore_replay_agreement (g.exec Y)
    (a := g.start) (b := g.horizon) (H := g.radius) le_rfl g.cluster
    (fun h => g.core h) (fun h => g.fringe h) g.times entry
    (fun t ht => ⟨g.time_start t ht, g.time_lt t ht⟩) (g.outside X) (g.outside Y)
    (fun t ht h hh => by simpa only [Finset.mem_union, Set.mem_union, Finset.mem_coe] using g.selected X t ht h hh) hentry hfill (fun t ht => ordinary_controls ho (hentryR t ht))
    (fun t ht h hh z hz => by
      change z ∈ g.fringe h at hz
      exact ordinary_entry ho (hentryR t ht) h (by simpa only [entryCells, hh, ite_true] using hz))
    (fun t ht h hh z hz => ordinary_entry ho (hentryR t ht) h (by
      rw [g.work_entry X _ (hentryR t ht)] at hz
      have ha : |z - g.workEntry (entry t) h| ≤ (g.radius : ℤ) := by
        rw [← Int.natCast_natAbs]; exact_mod_cast hz
      simp only [entryCells, hh, ite_false, mem_Icc]
      obtain ⟨h₁, h₂⟩ := abs_le.mp ha
      constructor <;> omega))
    (fun t ht h hh => by
      have htN := (g.time_lt t ht).trans_le g.horizon_le
      have hv := congrFun (congrArg Subtype.val hi) (⟨t, htN⟩, h)
      simpa [imports, clusterIncomingFields, ht, hh, entry] using hv)
    (fun h _ z hz => ordinary_cores ho h hz)
    (rawExtent g.times g.rawLo g.rawHi)
    (rawExtent_contains_reads (g.exec X) g.times g.time_lt g.rawLo g.rawHi (g.extrema X))
    (fun _ hz => readInput_eq_of_exterior g.omitted _ hext'
      (geometryOmitted_raw_disjoint π g.times g.outLo g.outHi g.rawLo g.rawHi) hz)
  have hcount := (g.exec X).replay_output_count_agreement (g.exec Y) g.times entry g.time_lt
    (fun t ht => (hentry t ht).2) hfill
    (fun t ht => (g.out_lo X _ (hentryR t ht)).trans (g.out_lo Y _ (hentryR t ht)).symm)
    (fun t ht => (hreplay.2 t ht).2)
  apply Subtype.ext
  apply (g.exec X).replay_recovers_input (g.exec Y) π g.times g.omitted g.time_lt
    (geometryOmitted_output_cover (g.exec X) π g.times g.time_lt g.outLo g.outHi g.rawLo g.rawHi
      (g.out_lo X) (g.out_hi X)) hcount (fun t ht => (hreplay.2 t ht).2)
  · intro t ht j bit hc hb
    exact (g.exec X).output_correct π (g.finish_ge X) (g.output X) ht j bit hc hb
  · intro t ht j bit hc hb
    exact (g.exec Y).output_correct π (g.finish_ge Y) (g.output Y) ht j bit hc hb
  · exact hext'

variable (g)

noncomputable def ordinaryBits (q a : ℕ) : ℕ :=
  q * (runStarts g.times).card + a * (Fintype.card g.SnapshotDomain + Fintype.card g.EntryDomain)

theorem exterior_card : Fintype.card g.Exterior = 2 ^ (P - g.omitted.card) := by
  simp only [Exterior, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe, card_compl, Fintype.card_fin]

theorem ordinary_card_le (q a : ℕ) (hq : M.q + 1 ≤ 2 ^ q) (ha : M.g + 1 ≤ 2 ^ a) :
    Fintype.card g.Ordinary ≤ 2 ^ g.ordinaryBits q a := by
  simp only [Ordinary, Fintype.card_prod, Fintype.card_fun, Fintype.card_coe, Fintype.card_fin]
  calc
    _ ≤ (2 ^ q) ^ (runStarts g.times).card *
      ((2 ^ a) ^ Fintype.card g.SnapshotDomain * (2 ^ a) ^ Fintype.card g.EntryDomain) := by gcongr
    _ = _ := by simp only [ordinaryBits, ← pow_mul, pow_add, Nat.mul_add]

/-- The joint all-head/time slot menu remains sparse; excluded cluster heads
have literal none fields, so this safe k*T menu introduces no hidden imports. -/
theorem imports_card_le : Fintype.card g.Imports ≤
    ∑ j ∈ range (g.tags + 1), (M.k * g.limit).choose j * (M.g + 1) ^ j := by
  have hc := sparse_record_card_le (I := Fin g.limit × Fin M.k)
    (A := fun _ => Option (Fin (M.g + 1))) (fun _ => none) (M.g + 1) g.tags
    (fun _ => by simp [Fintype.card_subtype_compl])
  simpa only [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fin, Nat.mul_comm g.limit] using hc

theorem records_injective : Function.Injective (fun X => ((g.exterior X, g.ordinary X), g.imports X)) := by
  intro X Y he
  exact records_recover (congrArg (fun v => v.1.1) he) (congrArg (fun v => v.1.2) he)
    (congrArg Prod.snd he)

end CoreReplayClass
end AdaptiveTransfer
