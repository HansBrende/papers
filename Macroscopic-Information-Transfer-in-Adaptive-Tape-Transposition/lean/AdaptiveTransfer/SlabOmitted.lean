import AdaptiveTransfer.NativeSlabClasses

/-! The actual omitted set is determined by computed slab metadata, even
when different inputs halt at different later times. -/

namespace AdaptiveTransfer
open Finset NativeRelations BoundedNesting MergeDepth

theorem geometryOmitted_congr_records {P : ℕ} (π : Fin P → Fin P) (C : Finset ℕ)
    {lo hi lo' hi' : ℕ → ℕ} {left right left' right' : ℕ → ℤ}
    (he : ∀ r ∈ runStarts C, lo r = lo' r ∧ hi r = hi' r ∧ left r = left' r ∧ right r = right' r) :
    geometryOmitted π C lo hi left right = geometryOmitted π C lo' hi' left' right' := by
  classical
  have hout : recordedOrdinals P C lo hi = recordedOrdinals P C lo' hi' := by
    apply biUnion_congr rfl
    intro r hr
    simp only [(he r hr).1, (he r hr).2.1]
  have hraw : rawExtent C left right = rawExtent C left' right' := by
    ext z
    constructor
    · rintro ⟨r, hr, h₁, h₂⟩
      exact ⟨r, hr, (he r hr).2.2.1 ▸ h₁, (he r hr).2.2.2 ▸ h₂⟩
    · rintro ⟨r, hr, h₁, h₂⟩
      exact ⟨r, hr, (he r hr).2.2.1.symm ▸ h₁, (he r hr).2.2.2.symm ▸ h₂⟩
  simp only [geometryOmitted, hout, hraw]

theorem runEnd_eq_of_time_bounds {C : Finset ℕ} {T U r : ℕ}
    (hT : ∀ t ∈ C, t < T) (hU : ∀ t ∈ C, t < U) (hr : r ∈ runStarts C) :
    runEnd C T r = runEnd C U r := by
  have h₁ := runEnd_spec hT hr
  have h₂ := runEnd_spec hU hr
  rcases lt_trichotomy (runEnd C T r) (runEnd C U r) with hlt | heq | hgt
  · exact (h₁.2.2.1 (h₂.2.2.2 _ (mem_Ico.mpr ⟨h₁.1.le, hlt⟩))).elim
  · exact heq
  · exact (h₂.2.2.1 (h₁.2.2.2 _ (mem_Ico.mpr ⟨h₂.1.le, hgt⟩))).elim

namespace SlabObservation
variable {k T W N : ℕ} {τ τ' : Trace k}

noncomputable def omittedGeometry {P : ℕ} (g : SlabObservation τ T W N) (π : Fin P → Fin P) : Finset (Fin P) :=
  geometryOmitted π g.times (fun r => (appendList τ r).length)
    (fun r => (appendList τ (runEnd g.times g.finish r)).length)
    (runRawLo τ.input g.times g.finish) (runRawHi τ.input g.times g.finish)

theorem omittedGeometry_eq_of_encode_eq {P : ℕ} (π : Fin P → Fin P)
    {g : SlabObservation τ T W N} {h : SlabObservation τ' T W N}
    (he : g.encode = h.encode) : g.omittedGeometry π = h.omittedGeometry π := by
  have hC := g.times_eq_of_encode_eq he
  have hfinish := finish_eq_of_encode_eq he
  unfold omittedGeometry
  rw [← hC, ← hfinish]
  apply geometryOmitted_congr_records
  intro r hr
  have hh := g.runRecord_eq_of_encode_eq he hr
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact congrArg (fun v : RunMetadata k T => v.outLo.val) hh
  · simpa only [runRecord, ← hC, ← hfinish] using congrArg (fun v : RunMetadata k T => v.outHi.val) hh
  · simpa only [runRecord, ← hC, ← hfinish] using congrArg (fun v : RunMetadata k T => v.rawLo.val) hh
  · simpa only [runRecord, ← hC, ← hfinish] using congrArg (fun v : RunMetadata k T => v.rawHi.val) hh

/-- The metadata formula equals the literal full-run omitted raw set. -/
theorem omittedGeometry_eq_literal {d b finish : ℕ} (g : SlabObservation τ T W N)
    (hfinish : g.finish ≤ finish) (hP : d * d * b ≤ (appendList τ finish).length) :
    g.omittedGeometry (tposOf d b) =
      omittedSlabBits d b τ.input (fun j => appendTime τ finish j.val) g.times := by
  have hCT : ∀ t ∈ g.times, t < finish := fun t ht => (g.time_finish ht).trans_le hfinish
  have he : g.omittedGeometry (tposOf d b) =
      geometryOmitted (tposOf d b) g.times (fun r => (appendList τ r).length)
        (fun r => (appendList τ (runEnd g.times finish r)).length)
        (runRawLo τ.input g.times finish) (runRawHi τ.input g.times finish) := by
    apply geometryOmitted_congr_records
    intro r hr
    have he := runEnd_eq_of_time_bounds (fun _t ht => g.time_finish ht) hCT hr
    exact ⟨rfl, by rw [he], by simp only [runRawLo, he], by simp only [runRawHi, he]⟩
  exact he.trans (geometryOmitted_eq_omittedSlabBits τ hP hCT)

end SlabObservation
end AdaptiveTransfer
