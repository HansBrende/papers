import AdaptiveTransfer.FragmentGeometry

/-! Actual ordinal and raw-coordinate sets recovered by the fragment record.
Coverage follows from native zero/one output increments, not a supplied
certificate about demanded bits. -/

namespace AdaptiveTransfer
open Transpose Transpose.Tape MergeDepth Finset LeanMachine BoundedNesting

abbrev FragmentIntervalLabel (B : Finset ℕ) := cutGapStarts B ⊕ B

def fragmentIntervalLabel {B : Finset ℕ} : FragmentIntervalLabel B → Fin 2 → FragmentCounterLabel B
  | .inl a, i => .inl (a, i)
  | .inr p, i => .inr (p, i)

namespace FragmentObservation
variable {M : TM} {P T : ℕ} {X Y : Fin P → Bool} {B : Finset ℕ}

def counter (_g : FragmentObservation M P T X B) (t : ℕ) : ℕ :=
  (run M (List.ofFn X) t).outRev.length

noncomputable def ordinals (g : FragmentObservation M P T X B) : Finset (Fin P) :=
  univ.filter fun j => ∃ a : FragmentIntervalLabel B,
    g.counter (fragmentCounterTime B g.kept (fragmentIntervalLabel a 0)) ≤ j.val ∧
      j.val < g.counter (fragmentCounterTime B g.kept (fragmentIntervalLabel a 1))

noncomputable def rawCells (g : FragmentObservation M P T X B) : Finset ℤ :=
  g.kept.image (trace M (List.ofFn X)).input

noncomputable def omitted (g : FragmentObservation M P T X B) (π : Fin P → Fin P) : Finset (Fin P) :=
  (g.ordinals.image π).filter fun p => (p.val : ℤ) ∉ g.rawCells

theorem counter_mono (g : FragmentObservation M P T X B) : Monotone g.counter := by
  intro u v huv
  change (run M (List.ofFn X) u).outRev.length ≤ (run M (List.ofFn X) v).outRev.length
  simpa only [native_output_count] using append_length_mono (trace M (List.ofFn X)) huv

theorem encode_ordinals {g : FragmentObservation M P T X B} {h : FragmentObservation M P T Y B}
    (he : g.encode = h.encode) : g.ordinals = h.ordinals := by
  have hK := encode_kept he
  have hc (i : FragmentCounterLabel B) :
      g.counter (fragmentCounterTime B g.kept i) = h.counter (fragmentCounterTime B g.kept i) := by
    simpa only [counter, native_output_count] using encode_counter he i
  ext j
  simp only [ordinals, mem_filter, mem_univ, true_and, ← hK, hc]

theorem encode_omitted {g : FragmentObservation M P T X B} {h : FragmentObservation M P T Y B}
    (he : g.encode = h.encode) (π : Fin P → Fin P) : g.omitted π = h.omitted π := by
  simp only [omitted, encode_ordinals he, rawCells, encode_raw_image he]
  rfl

/-- Every recorded output ordinal is realized by an actual retained or cut
instruction. Empty prefix intervals contribute no ordinals. -/
theorem ordinal_cover (g : FragmentObservation M P T X B) {j : Fin P} (hj : j ∈ g.ordinals) :
    ∃ t ∈ g.kept ∪ B, (g.exec.config t).outRev.length = j.val ∧ (g.exec.emitted t).isSome := by
  obtain ⟨a, hlo, hhi⟩ := (mem_filter.mp hj).2
  rcases a with a | p
  · change g.counter a.val ≤ j.val at hlo
    change j.val < g.counter (a.val + (gapPrefix B g.kept a.val).card) at hhi
    have hend := gapPrefix_end_le g.closed g.kept_lt (cutGapStarts_le g.cut_lt a.property)
    obtain ⟨t, hat, hte, hc, ho⟩ := g.exec.exists_append_between
      (Nat.le_add_right _ _) hend hlo hhi
    refine ⟨t, mem_union_left _ ?_, hc, ho⟩
    have ht : t ∈ gapPrefix B g.kept a.val := by
      rw [gapPrefix_eq_Ico g.closed]
      exact mem_Ico.mpr ⟨hat, hte⟩
    exact (mem_filter.mp ht).1
  · change g.counter p.val ≤ j.val at hlo
    change j.val < g.counter (p.val + 1) at hhi
    obtain ⟨t, hat, hte, hc, ho⟩ := g.exec.exists_append_between
      (Nat.le_add_right _ _) (by have := g.cut_lt p.val p.property; omega) hlo hhi
    have ht : t = p.val := by omega
    subst t
    exact ⟨p.val, mem_union_right _ p.property, hc, ho⟩

theorem omitted_cover (g : FragmentObservation M P T X B) (π : Fin P → Fin P)
    {p : Fin P} (hp : p ∈ g.omitted π) :
    ∃ t ∈ g.kept ∪ B, ∃ j : Fin P,
      π j = p ∧ (g.exec.config t).outRev.length = j.val ∧ (g.exec.emitted t).isSome := by
  obtain ⟨j, hj, he⟩ := mem_image.mp (mem_filter.mp hp).1
  obtain ⟨t, ht, hc, ho⟩ := g.ordinal_cover hj
  exact ⟨t, ht, j, he, hc, ho⟩

theorem raw_disjoint (g : FragmentObservation M P T X B) (π : Fin P → Fin P)
    (p : Fin P) (hp : (p.val : ℤ) ∈ g.rawCells) : p ∉ g.omitted π := by
  intro h
  exact (mem_filter.mp h).2 hp

/-- Conversely, every actual append at a retained or cut step lies in the
recorded ordinal set; this is the bridge for actual desired output roots. -/
theorem ordinal_mem_of_append (g : FragmentObservation M P T X B) {t : ℕ}
    (ht : t ∈ g.kept ∪ B) (j : Fin P) (hc : g.counter t = j.val) (ho : (g.exec.emitted t).isSome) :
    j ∈ g.ordinals := by
  apply mem_filter.mpr
  refine ⟨mem_univ _, ?_⟩
  have htT : t < g.finish := by
    rcases mem_union.mp ht with htK | htB
    · exact g.kept_lt t htK
    · exact g.cut_lt t htB
  have hn : g.counter (t + 1) = j.val + 1 := by
    have hh := g.exec.output_count_next htT
    change g.counter (t + 1) = g.counter t + if (g.exec.emitted t).isSome then 1 else 0 at hh
    simpa only [ho, ite_true, hc] using hh
  rcases mem_union.mp ht with htK | htB
  · let a : cutGapStarts B := ⟨cutGapStart B t, cutGapStart_mem B t⟩
    refine ⟨.inl a, ?_, ?_⟩
    · exact (g.counter_mono (cutGapStart_le B t)).trans hc.le
    · have hm : t ∈ gapPrefix B g.kept a.val := mem_filter.mpr ⟨htK, rfl⟩
      rw [gapPrefix_eq_Ico g.closed] at hm
      have hend : t + 1 ≤ a.val + (gapPrefix B g.kept a.val).card := by
        have := (mem_Ico.mp hm).2
        omega
      have hh := g.counter_mono hend
      change j.val < g.counter (a.val + (gapPrefix B g.kept a.val).card)
      omega
  · refine ⟨.inr ⟨t, htB⟩, hc.le, ?_⟩
    change j.val < g.counter (t + 1)
    rw [hn]
    omega

end FragmentObservation
end AdaptiveTransfer
