import AdaptiveTransfer.NativeReturnCounting
import AdaptiveTransfer.SlabOmitted
import AdaptiveTransfer.LocalClassData

/-! Literal native slab geometry and the original full-graph localized cut
event. The geometric selection theorem proves existence for every free head;
the bad event quantifies over all valid computed chunks. -/

namespace AdaptiveTransfer
open Transpose MergeDepth BoundedNesting NativeRelations Finset

structure NativeValidSlab (M : TM) (d b a : ℕ) (c : ℝ) (X : Fin (d * d * b) → Bool) where
  obs : SlabObservation (trace M (List.ofFn X)) (returnTime (d * d * b) c)
    (slabWidth (d * d * b) a c) (slabRunCap a c)
  finish_le : obs.finish ≤ (trace M (List.ofFn X)).haltTime
  half : obs.times.card ≤ (d * d * b) / 2
  margin : slabSaving d b a c ≤ ((obs.omittedGeometry (tposOf d b)).card : ℝ) -
    (a : ℝ) * (if obs.start = 0 then 0 else (slabWidth (d * d * b) a c : ℝ))

/-- Every free head has an actual valid chunk; nonemptiness follows from the
positive proved geometric saving, not from a supplied selection certificate. -/
theorem native_valid_slab_exists {M : TM} {d b a : ℕ} {c : ℝ}
    (hd : 1 ≤ d) (hb : 1 ≤ b) (hP : 2 ≤ d * d * b) (ha : 1 ≤ a) (hc : 1 ≤ c)
    {X : Fin (d * d * b) → Bool} (hcorrect : TransposesInput M d b c X)
    (hsaving : 0 < slabSaving d b a c) (f : Fin M.k) :
    ∃ g : NativeValidSlab M d b a c X, g.obs.free = f := by
  obtain ⟨ell, s, e, hse, he, hhalf, hruns, hmargin⟩ :=
    native_slab_geometry (a := (a : ℝ)) hd hb hP (by exact_mod_cast ha) hc hcorrect f
  have hne : (selectedSlab ((trace M (List.ofFn X)).work f)
      (slabWidth (d * d * b) a c) ell s e).Nonempty := by
    by_contra hn
    have hemp := not_nonempty_iff_eq_empty.mp hn
    have hU : omittedSlabBits d b (trace M (List.ofFn X)).input
        (fun j => appendTime (trace M (List.ofFn X)) (trace M (List.ofFn X)).haltTime j.val)
        (selectedSlab ((trace M (List.ofFn X)).work f) (slabWidth (d * d * b) a c) ell s e) = ∅ := by
      simp [omittedSlabBits, outIn, hemp]
    change slabSaving d b a c ≤ _ at hmargin
    rw [hU, card_empty, Nat.cast_zero] at hmargin
    have hcost : 0 ≤ (a : ℝ) * (if s = 0 then 0 else (slabWidth (d * d * b) a c : ℝ)) := by
      split_ifs <;> positivity
    linarith
  let o : SlabObservation (trace M (List.ofFn X)) (returnTime (d * d * b) c)
      (slabWidth (d * d * b) a c) (slabRunCap a c) :=
    ⟨f, ell, s, e, hse, he.trans (timely_native_data hcorrect).1, hne, hruns⟩
  refine ⟨⟨o, he, hhalf, ?_⟩, rfl⟩
  rw [o.omittedGeometry_eq_literal he (fibre_haltTime (mem_fibre.mpr rfl) hcorrect).2.ge]
  exact hmargin

structure NativeSlabCutWitness (M : TM) (d b a : ℕ) (c : ℝ) (H : ℕ)
    (X : Fin (d * d * b) → Bool) where
  slab : NativeValidSlab M d b a c X
  cut : Finset ℕ
  cut_lt : ∀ t ∈ cut, t < (trace M (List.ofFn X)).haltTime
  separates : IsMengerVertexCut (trace M (List.ofFn X)).work (trace M (List.ofFn X)).haltTime
    (nativeDemandedOutputSteps M X (trace M (List.ofFn X)).haltTime (tposOf d b)
      (slab.obs.omittedGeometry (tposOf d b)))
    (offCarrierLowerEndpoints (trace M (List.ofFn X)).work slab.obs.free
      (trace M (List.ofFn X)).haltTime H) cut

noncomputable def nativeBadSlabCuts (M : TM) (d b a : ℕ) (c : ℝ) (H r : ℕ) :
    Finset (Fin (d * d * b) → Bool) := by
  classical
  exact univ.filter fun X => TransposesInput M d b c X ∧
    ∃ w : NativeSlabCutWitness M d b a c H X, w.cut.card ≤ r

end AdaptiveTransfer
