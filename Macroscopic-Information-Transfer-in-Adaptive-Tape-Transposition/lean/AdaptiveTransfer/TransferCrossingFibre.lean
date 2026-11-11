import AdaptiveTransfer.TransferCrossingNative
import AdaptiveTransfer.TransferCorrectOutputs
import TapeStorageRates.NativeTypicalResources
import NativeRelations.TightConstants

/-! A finite successful-fibre crossing invoice on the original execution.
Only the complete simulator trace is shared. Correctness, append ordinals,
and its exact horizon are derived from actual native computations. -/

namespace AdaptiveTransfer.TransferCrossing
open Finset Transpose Transpose.Tape Transpose.Tape.Impl MergeDepth NativeRelations
open TapeStorageRates TapeStorageRates.Native
open AdaptiveTransfer.TransferFIFO AdaptiveTransfer.TransferRoots AdaptiveTransfer.TransferCorrect

/-- A successful common simulator fibre supplies the crossing expansion
budget. The original separator may contain arbitrary natural-number vertices;
trimming it to the actual source horizon can only reduce its finite bill.
There is no source-trace agreement assumption or cap on the entropy deficit. -/
theorem native_crossing_fibre_bound {M : TM} {d s t H h K : ℕ} {c α δ : ℝ}
    (hs : 0 < s) (hc : 0 ≤ c) (hstartup : 11 * s + 1 ≤ d * d * entryBits d + 1)
    (S : Finset (Fin (d * d * entryBits d) → Bool))
    (X : Fin (d * d * entryBits d) → Bool) (hX : X ∈ S)
    (halt : HaltsAt M (List.ofFn X) t)
    (hcorrect : ∀ Y ∈ S, TransposesInput M d (entryBits d) c Y)
    (htrace : ∀ Y ∈ S, trace (machine M hs) (List.ofFn Y) = trace (machine M hs) (List.ofFn X))
    (hcard : (2 : ℝ) ^ ((1 - δ) * (d * d * entryBits d : ℕ)) ≤ S.card)
    (hd : bridgeMenger_d0_tight (machine M hs).k (11 * c + 1) α ≤ d)
    (hα : 0 < α) (hH : 1 ≤ H)
    (hH_le : (H : ℝ) ≤ thetaMacro_tight (machine M hs) (11 * c + 1) α * (d * d * entryBits d : ℕ))
    (hK : ∀ j, (tapeSkeleton ((trace (machine M hs) (List.ofFn X)).work j)
      (alignedTime s t) H).length + 1 ≤ K)
    (V : Finset (Fin (d * d * entryBits d)))
    (hV : α * (d * d * entryBits d : ℕ) ≤ V.card) (B : Finset ℕ)
    (hcut : IsMengerVertexCut (trace M (List.ofFn X)).work t
      (V.image fun p => sourceOrdinal M (List.ofFn X) t (d * d * entryBits d) (tposOf d (entryBits d) p))
      (crossingLowerEtaSteps (trace M (List.ofFn X)) t h 1 t) B) :
    cE_frozen_eta_tight (machine M hs) (11 * c + 1) α δ * V.card ≤
      (crossingCutFactor M.k s (alignedTime s t) H * B.card + crossingCutError M.k s K h : ℕ) := by
  classical
  let P := d * d * entryBits d
  let I := V.image (tposOf d (entryBits d))
  let B' := B ∩ range t
  have hcount : P ≤ outputCount M (List.ofFn X) t :=
    (correct_source_count halt (hcorrect X hX).outputsTranspose).ge
  have hroots : I.image (sourceOrdinal M (List.ofFn X) t P) =
      V.image (fun p => sourceOrdinal M (List.ofFn X) t P (tposOf d (entryBits d) p)) := by
    rw [Finset.image_image]
    rfl
  have hrootlive : ∀ u ∈ I.image (sourceOrdinal M (List.ofFn X) t P), u < t := by
    intro u hu
    obtain ⟨i, _, rfl⟩ := mem_image.mp hu
    exact (sourceRoot_counts M (List.ofFn X) (i.isLt.trans_le hcount)).1
  have htrim : IsMengerVertexCut (trace M (List.ofFn X)).work t
      (I.image (sourceOrdinal M (List.ofFn X) t P))
      (crossingLowerEtaSteps (trace M (List.ofFn X)) t h 1 t) B' := by
    intro ρ u hu hpath hend
    obtain ⟨v, hv, hvB⟩ := hcut ρ u (hroots ▸ hu) hpath hend
    have hvT : v < t := by
      rcases List.mem_cons.mp hv with rfl | hv
      · exact hrootlive _ hu
      · exact (isDepPath_lt u ρ hpath v hv).trans (hrootlive u hu)
    exact ⟨v, hv, mem_inter.mpr ⟨hvB, mem_range.mpr hvT⟩⟩
  obtain ⟨Γ, hΓcard, _hΓlive, hΓcut⟩ := native_crossing_cut_lift hs halt hcount hH hK I B'
    (fun _ hb => mem_range.mp (mem_inter.mp hb).2) htrim
  have hhalt : (trace (machine M hs) (List.ofFn X)).haltTime = alignedTime s t :=
    haltTime_eq_of_haltsAt (simulates_halt M hs _ halt).1
  have hsimcut : IsMengerVertexCut (trace (machine M hs) (List.ofFn X)).work
      (trace (machine M hs) (List.ofFn X)).haltTime
      (V.image fun p => appendTime (trace (machine M hs) (List.ofFn X))
        (trace (machine M hs) (List.ofFn X)).haltTime (tposOf d (entryBits d) p).val)
      (crossingLowerEtaSteps (trace (machine M hs) (List.ofFn X))
        (trace (machine M hs) (List.ofFn X)).haltTime H 1
        (trace (machine M hs) (List.ofFn X)).haltTime) Γ := by
    rw [hhalt]
    simpa only [I, Finset.image_image, simulatorOrdinal, simulatorRoot, sourceRoot,
      Function.comp_def] using hΓcut
  have hsimcorrect := (native_success_resources M hs hc hstartup S hcorrect).1
  have hsfib : S ⊆ fibre (machine M hs) (d * d * entryBits d)
      (trace (machine M hs) (List.ofFn X)) := fun Y hY => mem_fibre.mpr (htrace Y hY)
  have hbudget := correctSubset_crossingLowerGT2H_menger_lb_tight
    (by linarith : 1 ≤ 11 * c + 1) hα hH hd hsfib hsimcorrect hcard hH_le V hV Γ hsimcut
  have hΓreal : (Γ.card : ℝ) ≤
      (crossingCutFactor M.k s (alignedTime s t) H * B'.card + crossingCutError M.k s K h : ℕ) := by
    exact_mod_cast hΓcard
  have hBcard : B'.card ≤ B.card := card_le_card inter_subset_left
  exact hbudget.trans (hΓreal.trans (Nat.cast_le.mpr
    (Nat.add_le_add_right (Nat.mul_le_mul_left _ hBcard) _)))

end AdaptiveTransfer.TransferCrossing
