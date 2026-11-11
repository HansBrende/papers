import AdaptiveTransfer.ReplayGeometry
import AdaptiveTransfer.ConditionalSupport

/-! Native joint import information with input-dependent finite geometry.
The class data below contain actual execution observations only. Injectivity
is a theorem of the native replay construction, never a field of the data. -/

namespace AdaptiveTransfer

open Transpose Finset NativeRelations LeanMachine TransposeFollowup
open scoped BigOperators

structure NativeReplayClass (M : TM) (P : ℕ) (π : Fin P → Fin P) where
  inputs : Finset (Fin P → Bool)
  horizon : ℕ
  exec : ∀ X : inputs, ExecutionPrefix M (List.ofFn X.val) horizon
  times : Finset ℕ
  cells : Finset ℤ
  start : ℕ
  radius : ℕ
  limit : ℕ
  tags : ℕ
  free : Fin M.k
  time_lt : ∀ t ∈ times, t < horizon
  time_start : ∀ t ∈ times, start ≤ t
  horizon_le : horizon ≤ limit
  carrier : ∀ X : inputs, ∀ t, start ≤ t → t < horizon →
    (t ∈ times ↔ ((exec X).config t).workPos free ∈ cells)
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
    (incomingFields (exec X) limit radius times (replayEntry times horizon time_lt) free)).card ≤ tags
  finish : inputs → ℕ
  finish_ge : ∀ X, horizon ≤ finish X
  output : ∀ X : inputs,
    (Transpose.Tape.run M (List.ofFn X.val) (finish X)).outRev.reverse =
      List.ofFn (fun j => X.val (π j))

namespace NativeReplayClass

variable {M : TM} {P : ℕ} {π : Fin P → Fin P} (g : NativeReplayClass M P π)

noncomputable def omitted : Finset (Fin P) :=
  geometryOmitted π g.times g.outLo g.outHi g.rawLo g.rawHi

abbrev Exterior := ↑g.omittedᶜ → Bool

abbrev Ordinary :=
  (runStarts g.times → Fin (M.q + 1)) ×
    (snapshotCells g.start g.cells → Fin (M.g + 1)) ×
    (runStarts g.times → OtherHeads g.free → Fin (2 * g.radius + 1) → Fin (M.g + 1))

abbrev Imports := ReplayImports M g.limit g.free g.tags

noncomputable instance : Nonempty g.Imports := by
  classical
  exact ⟨⟨fun _ => none, by simp [recordSupport]⟩⟩

noncomputable def code (X : g.inputs) :
    ReplayMessage M P g.omitted (runStarts g.times) g.cells g.start g.radius g.limit g.free g.tags :=
  encodeReplay g.inputs g.exec g.omitted (runStarts g.times) g.times g.cells
    g.start g.radius g.limit g.tags g.free (replayEntry g.times g.horizon g.time_lt)
    g.workEntry g.tag_bound X

theorem code_injective : Function.Injective g.code := by
  apply encodeReplay_injective g.inputs g.exec g.omitted (runStarts g.times) g.times g.cells
    g.start g.radius g.limit g.tags g.free (replayEntry g.times g.horizon g.time_lt)
    g.workEntry g.tag_bound π g.rawEntry g.outLo g.finish (rawExtent g.times g.rawLo g.rawHi)
    (fun t ht => ⟨g.time_start t ht, g.time_lt t ht⟩) g.horizon_le g.carrier
  · intro t ht
    have he := replayEntry_spec g.time_lt ht
    exact ⟨g.time_start _ (mem_filter.mp he.1).1, he.2.1⟩
  · intro t ht u heu hut
    have he := replayEntry_spec g.time_lt ht
    exact (runEnd_spec g.time_lt he.1).2.2.2 u
      (mem_Ico.mpr ⟨heu, hut.trans_lt he.2.2⟩)
  · exact fun t ht => (replayEntry_spec g.time_lt ht).1
  · exact g.work_entry
  · exact g.raw_entry
  · exact g.out_lo
  · exact fun X => rawExtent_contains_reads (g.exec X) g.times g.time_lt g.rawLo g.rawHi (g.extrema X)
  · exact geometryOmitted_raw_disjoint π g.times g.outLo g.outHi g.rawLo g.rawHi
  · exact fun X => geometryOmitted_output_cover (g.exec X) π g.times g.time_lt
      g.outLo g.outHi g.rawLo g.rawHi (g.out_lo X) (g.out_hi X)
  · exact g.finish_ge
  · exact g.output

noncomputable def exterior (X : g.inputs) : g.Exterior := (g.code X).1

noncomputable def ordinary (X : g.inputs) : g.Ordinary :=
  ((g.code X).2.1, (g.code X).2.2.1, (g.code X).2.2.2.1)

noncomputable def imports (X : g.inputs) : g.Imports := (g.code X).2.2.2.2

theorem records_injective : Function.Injective
    (fun X => ((g.exterior X, g.ordinary X), g.imports X)) := by
  intro X Y he
  apply g.code_injective
  have hext := congrArg (fun v => v.1.1) he
  have hstate := congrArg (fun v => v.1.2.1) he
  have hsnap := congrArg (fun v => v.1.2.2.1) he
  have hwindow := congrArg (fun v => v.1.2.2.2) he
  have himport := congrArg Prod.snd he
  exact Prod.ext hext (Prod.ext hstate (Prod.ext hsnap (Prod.ext hwindow himport)))

def ordinaryBits (q a : ℕ) : ℕ :=
  q * (runStarts g.times).card + a *
    ((if g.start = 0 then 0 else g.cells.card) +
      (M.k - 1) * (runStarts g.times).card * (2 * g.radius + 1))

theorem exterior_card : Fintype.card g.Exterior = 2 ^ (P - g.omitted.card) := by
  simp only [Exterior, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe,
    card_compl, Fintype.card_fin]

theorem ordinary_card : Fintype.card g.Ordinary =
    (M.q + 1) ^ (runStarts g.times).card *
      (M.g + 1) ^ ((if g.start = 0 then 0 else g.cells.card) +
        (M.k - 1) * (runStarts g.times).card * (2 * g.radius + 1)) := by
  simp only [Ordinary, Fintype.card_prod, Fintype.card_fun, Fintype.card_coe,
    Fintype.card_fin, otherHeads_card, snapshotCells_card]
  rw [← pow_mul, ← pow_mul,
    show (2 * g.radius + 1) * ((M.k - 1) * (runStarts g.times).card) =
      (M.k - 1) * (runStarts g.times).card * (2 * g.radius + 1) by ring,
    pow_add]

theorem ordinary_card_le (q a : ℕ) (hq : M.q + 1 ≤ 2 ^ q) (ha : M.g + 1 ≤ 2 ^ a) :
    Fintype.card g.Ordinary ≤ 2 ^ g.ordinaryBits q a := by
  calc
    _ ≤ (2 ^ q) ^ (runStarts g.times).card *
        (2 ^ a) ^ ((if g.start = 0 then 0 else g.cells.card) +
          (M.k - 1) * (runStarts g.times).card * (2 * g.radius + 1)) := by
      rw [g.ordinary_card]
      exact Nat.mul_le_mul (Nat.pow_le_pow_left hq _) (Nat.pow_le_pow_left ha _)
    _ = _ := by rw [← pow_mul, ← pow_mul, ← pow_add]; rfl

end NativeReplayClass

namespace NativeReplayFamily

variable {M : TM} {P : ℕ} {π : Fin P → Fin P} {G : Type*}
  (family : G → NativeReplayClass M P π)

abbrev Domain := Σ g, (family g).inputs
abbrev Exterior := Σ g, (family g).Exterior
abbrev Ordinary := Σ g, (family g).Ordinary
abbrev Imports := Σ g, (family g).Imports

def source (x : Domain family) : Fin P → Bool := x.2.val

noncomputable def exterior (x : Domain family) : Exterior family :=
  ⟨x.1, (family x.1).exterior x.2⟩

noncomputable def ordinary (x : Domain family) : Ordinary family :=
  ⟨x.1, (family x.1).ordinary x.2⟩

noncomputable def imports (x : Domain family) : Imports family :=
  ⟨x.1, (family x.1).imports x.2⟩

instance [Nonempty (Domain family)] : Nonempty (Exterior family) :=
  Nonempty.map (exterior family) inferInstance

instance [Nonempty (Domain family)] : Nonempty (Ordinary family) :=
  Nonempty.map (ordinary family) inferInstance

instance [Nonempty (Domain family)] : Nonempty (Imports family) :=
  Nonempty.map (imports family) inferInstance

theorem records_injective : Function.Injective
    (fun x : Domain family => (((x.1, exterior family x), ordinary family x), imports family x)) := by
  rintro ⟨g, X⟩ ⟨h, Y⟩ hxy
  have hgh : g = h := congrArg (fun v => v.1.1.1) hxy
  subst h
  have he : (family g).exterior X = (family g).exterior Y := by
    have hh := congrArg (fun v => v.1.1.2) hxy
    simpa only [exterior, Sigma.mk.inj_iff, heq_eq_eq, true_and] using hh
  have hr : (family g).ordinary X = (family g).ordinary Y := by
    have hh := congrArg (fun v => v.1.2) hxy
    simpa only [ordinary, Sigma.mk.inj_iff, heq_eq_eq, true_and] using hh
  have hi : (family g).imports X = (family g).imports Y := by
    have hh := congrArg Prod.snd hxy
    simpa only [imports, Sigma.mk.inj_iff, heq_eq_eq, true_and] using hh
  have hXY := (family g).records_injective (Prod.ext (Prod.ext he hr) hi)
  cases hXY
  rfl

noncomputable def exteriorMenu (g : G) : Finset (Exterior family) := by
  classical
  exact univ.image (fun e : (family g).Exterior => (⟨g, e⟩ : Exterior family))

noncomputable def ordinaryMenu (g : G) : Finset (Ordinary family) := by
  classical
  exact univ.image (fun r : (family g).Ordinary => (⟨g, r⟩ : Ordinary family))

theorem exterior_mem (x : Domain family) : exterior family x ∈ exteriorMenu family x.1 := by
  classical
  exact mem_image_of_mem _ (mem_univ _)

theorem ordinary_mem (x : Domain family) : ordinary family x ∈ ordinaryMenu family x.1 := by
  classical
  exact mem_image_of_mem _ (mem_univ _)

theorem exteriorMenu_card (g : G) :
    (exteriorMenu family g).card = 2 ^ (P - (family g).omitted.card) := by
  classical
  rw [exteriorMenu, card_image_of_injective]
  · simpa only [card_univ] using (family g).exterior_card
  · intro x y h
    simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using h

theorem ordinaryMenu_card_le (q a : ℕ) (hq : M.q + 1 ≤ 2 ^ q) (ha : M.g + 1 ≤ 2 ^ a)
    (g : G) : (ordinaryMenu family g).card ≤ 2 ^ (family g).ordinaryBits q a := by
  classical
  calc
    _ ≤ Fintype.card (family g).Ordinary := card_image_le.trans_eq card_univ
    _ ≤ _ := (family g).ordinary_card_le q a hq ha

/-- Native import information under any law on a finite family of actual
geometry classes. Metadata-dependent records are embedded into disjoint
finite menus; their tags do not incur an extra address charge. The source
observation may have overlapping classes, making this scope stronger than
one deterministic geometry choice per input. -/
theorem native_import_information [Fintype G]
    (p : Domain family → ℝ) (hp : ∀ x, 0 ≤ p x)
    (q a : ℕ) (hq : M.q + 1 ≤ 2 ^ q) (ha : M.g + 1 ≤ 2 ^ a) :
    observationEntropy p (source family) - observationEntropy p (fun x => x.1) -
      (∑ x, p x * (((P - (family x.1).omitted.card : ℕ) : ℝ) +
        (family x.1).ordinaryBits q a)) * Real.log 2 ≤
      conditionalObservationEntropy p (imports family)
        (fun x => ((x.1, exterior family x), ordinary family x)) := by
  classical
  have hh := joint_import_information_from_support p hp (fun x => x.1)
    (exterior family) (ordinary family) (imports family) (records_injective family)
    (exteriorMenu family) (fun m => ordinaryMenu family m.1)
    (exterior_mem family) (ordinary_mem family)
    (fun g => P - (family g).omitted.card) (fun m => (family m.1).ordinaryBits q a)
    (fun g => (exteriorMenu_card family g).le) (fun m => ordinaryMenu_card_le family q a hq ha m.1)
  have hs : observationEntropy p (source family) ≤ entropy p :=
    entropy_pushforward_le p hp (source family)
  linarith

/-- The first, sharper invoice retains the actual conditional entropy of the
ordinary native record instead of replacing it by a support bound. -/
theorem native_import_information_ordinary [Fintype G]
    (p : Domain family → ℝ) (hp : ∀ x, 0 ≤ p x) :
    observationEntropy p (source family) - observationEntropy p (fun x => x.1) -
      (∑ x, p x * ((P - (family x.1).omitted.card : ℕ) : ℝ)) * Real.log 2 -
      conditionalObservationEntropy p (ordinary family) (fun x => (x.1, exterior family x)) ≤
      conditionalObservationEntropy p (imports family)
        (fun x => ((x.1, exterior family x), ordinary family x)) := by
  classical
  have hi := joint_record_entropy_identity p hp (fun x => x.1)
    (exterior family) (ordinary family) (imports family) (records_injective family)
  have he := conditional_entropy_le_mean_bits p hp (fun x => x.1) (exterior family)
    (exteriorMenu family) (exterior_mem family) (fun g => P - (family g).omitted.card)
    (fun g => (exteriorMenu_card family g).le)
  have hs : observationEntropy p (source family) ≤ entropy p :=
    entropy_pushforward_le p hp (source family)
  linarith

theorem mean_exterior_length [Fintype G]
    (p : Domain family → ℝ) (hp1 : ∑ x, p x = 1) :
    (∑ x, p x * ((P - (family x.1).omitted.card : ℕ) : ℝ)) =
      (P : ℝ) - ∑ x, p x * ((family x.1).omitted.card : ℝ) := by
  have hc (g : G) : (family g).omitted.card ≤ P := by
    simpa only [Fintype.card_fin] using card_le_univ (family g).omitted
  simp only [Nat.cast_sub (hc _), mul_sub, sum_sub_distrib, ← sum_mul, hp1, one_mul]

/-- The two native import inequalities in saving/deficit form, under one
normalized law. Natural logarithms are used; dividing by `log 2` gives bits. -/
theorem native_import_information_saving [Fintype G]
    (p : Domain family → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (q a : ℕ) (hq : M.q + 1 ≤ 2 ^ q) (ha : M.g + 1 ≤ 2 ^ a) :
    ((∑ x, p x * ((family x.1).omitted.card : ℝ)) * Real.log 2 -
        ((P : ℝ) * Real.log 2 - observationEntropy p (source family)) -
        observationEntropy p (fun x => x.1) -
        conditionalObservationEntropy p (ordinary family) (fun x => (x.1, exterior family x)) ≤
      conditionalObservationEntropy p (imports family)
        (fun x => ((x.1, exterior family x), ordinary family x))) ∧
    ((∑ x, p x * (((family x.1).omitted.card : ℝ) - (family x.1).ordinaryBits q a)) *
        Real.log 2 - ((P : ℝ) * Real.log 2 - observationEntropy p (source family)) -
        observationEntropy p (fun x => x.1) ≤
      conditionalObservationEntropy p (imports family)
        (fun x => ((x.1, exterior family x), ordinary family x))) := by
  have hext := mean_exterior_length family p hp1
  constructor
  · have hh := native_import_information_ordinary family p hp
    rw [hext] at hh
    nlinarith
  · have hh := native_import_information family p hp q a hq ha
    simp only [mul_add, sum_add_distrib] at hh
    rw [hext] at hh
    simp only [mul_sub, sum_sub_distrib]
    nlinarith

end NativeReplayFamily

end AdaptiveTransfer
