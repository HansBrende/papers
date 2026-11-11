import AdaptiveTransfer.SlabGeometryAdapters

/-! Canonical successful prefixes and output words of one timely correct
native input, plus monotonicity of actual off-carrier return records. -/

namespace AdaptiveTransfer
open Transpose Transpose.Tape Transpose.Tape.Impl MergeDepth BoundedNesting Finset

/-- The native timely-input predicate supplies the exact final word and the
successful prefix up to its own first halt, without a shared trace. -/
theorem timely_native_data {M : TM} {d b : ℕ} {c : ℝ} {X : Fin (d * d * b) → Bool}
    (htr : TransposesInput M d b c X) :
    let T := (trace M (List.ofFn X)).haltTime
    T ≤ ⌊c * (((d * d * b : ℕ) : ℝ) + 1)⌋₊ ∧
    (∀ t < T, transAt M (List.ofFn X) t ≠ none) ∧
    (run M (List.ofFn X) T).outRev.reverse = List.ofFn (fun j => X (tposOf d b j)) := by
  obtain ⟨s, hs, hhalt⟩ := htr.halts
  have hτ := (haltsAt_iff_trace s).mp hhalt
  have he : (trace M (List.ofFn X)).haltTime = s :=
    ((trace M (List.ofFn X)).haltsAt_haltTime ⟨s, hτ.2⟩).unique hτ
  dsimp only
  rw [he]
  refine ⟨hs, hhalt.1, ?_⟩
  obtain ⟨s', hhalt', hlen, hout⟩ := htr.outputsTranspose.output
  have he' : s' = s := haltsAt_unique hhalt' hhalt
  subst s'
  apply List.ext_getElem?
  intro n
  by_cases hn : n < d * d * b
  · have hh := hout (tposOf d b ⟨n, hn⟩)
    have ht : Transpose.Tape.tpos d b (tposOf d b ⟨n, hn⟩) = n :=
      congrArg Fin.val (tposOf_tposOf d b ⟨n, hn⟩)
    rw [ht] at hh
    simpa only [List.getElem?_ofFn, dite_eq_left hn] using hh
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]

/-- Enlarging the completed native horizon can only add long returns. -/
theorem offCarrierReturns_mono {k : ℕ} (y : Fin k → ℕ → ℤ) (f : Fin k) (H : ℕ)
    {T U : ℕ} (hTU : T ≤ U) : offCarrierReturns y f T H ⊆ offCarrierReturns y f U H := by
  intro e he
  obtain ⟨hh, hfree, hfar⟩ := mem_filter.mp he
  have hop := mem_allHops.mp hh
  exact mem_filter.mpr ⟨mem_allHops.mpr ⟨hop.1, hop.2.1.trans_le hTU, hop.2.2⟩,
    hfree, hfar⟩

end AdaptiveTransfer
