import AdaptiveTransfer.TransferErodedCuts
import AdaptiveTransfer.TransferCorrectOutputs
import AdaptiveTransfer.FrozenCutInvoice

/-! The actual frozen-simulator invoice for a cut on any reference source
run. Only the simulator trace is shared. The complete step-value record
already includes the output field, so there is no extra root surcharge. -/
namespace AdaptiveTransfer.TransferEroded
open Finset Transpose Transpose.Tape Transpose.Tape.Impl MergeDepth NativeRelations
open TapeStorageRates TapeStorageRates.Native
open AdaptiveTransfer.TransferFIFO AdaptiveTransfer.TransferRoots AdaptiveTransfer.TransferCorrect
attribute [local instance] Classical.propDecidable

noncomputable def erodedDemand {P : ℕ} (V : Finset (Fin P)) (U : Finset ℤ) (R : ℕ) : Finset (Fin P) :=
  V.filter fun p => (p.val : ℤ) ∈ inputErosion U R

theorem demandedReadSteps_subset_inputReadSteps {k P T : ℕ} (τ : Trace k)
    (Q : Finset (Fin P)) (U : Finset ℤ) (hQU : ∀ p ∈ Q, (p.val : ℤ) ∈ U) :
    demandedReadSteps τ P T Q ⊆ inputReadSteps τ T U := by
  intro u hu
  obtain ⟨huT, p, hp, hread⟩ := mem_filter.mp hu
  exact mem_filter.mpr ⟨huT, (readPos_eq_some_iff.mp hread).symm ▸ hQU p hp⟩

/-- The complete all-width finite invoice. The source cut is supplied only
on reference X; every other correct Y is used solely through its common
complete simulator trace and its own actual output correctness. -/
theorem native_eroded_fibre_invoice {M : TM} {d b s t : ℕ}
    (hs : 0 < s) (S : Finset (Fin (d * d * b) → Bool))
    (X : Fin (d * d * b) → Bool) (hX : X ∈ S) (H : HaltsAt M (List.ofFn X) t)
    (correct : ∀ Y ∈ S, OutputsTranspose M d b Y)
    (common : ∀ Y ∈ S, trace (machine M hs) (List.ofFn Y) = trace (machine M hs) (List.ofFn X))
    (V : Finset (Fin (d * d * b))) (U : Finset ℤ) (B : Finset ℕ)
    (hB : ∀ u ∈ B, u < t)
    (hcut : IsMengerVertexCut (trace M (List.ofFn X)).work t
      (V.image fun p => sourceOrdinal M (List.ofFn X) t (d * d * b) (tposOf d b p))
      (inputReadSteps (trace M (List.ofFn X)) t U) B) :
    ((erodedDemand V U (3 * s)).card : ℝ) ≤
      ((d * d * b : ℕ) : ℝ) - Real.logb 2 (S.card : ℝ) +
        (valueWidth (machine M hs) : ℝ) *
          (erodedCutFactor M.k s * B.card + (2 * s - 1) : ℕ) := by
  classical
  let P := d * d * b
  let Q := erodedDemand V U (3 * s)
  let I := Q.image (tposOf d b)
  let root (p : Fin P) := simulatorOrdinal M hs (List.ofFn X) t P (tposOf d b p)
  have hcount : P ≤ outputCount M (List.ofFn X) t := (correct_source_count H (correct X hX)).ge
  have hsource : IsMengerVertexCut (trace M (List.ofFn X)).work t
      (I.image (sourceOrdinal M (List.ofFn X) t P))
      (inputReadSteps (trace M (List.ofFn X)) t U) B := by
    intro ρ u hu hp hend
    apply hcut ρ u _ hp hend
    obtain ⟨i, hi, he⟩ := mem_image.mp hu
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hi
    exact mem_image.mpr ⟨p, (mem_filter.mp hp).1, he⟩
  obtain ⟨Γ, hΓcard, _hΓtime, hΓcut⟩ := native_eroded_cut_lift hs H hcount I U B hB hsource
  have hroot : ∀ p ∈ Q, root p < alignedTime s t := fun p _ =>
    (correct_simulator_root hs H (correct X hX) p).1
  have htrace : ∀ Y ∈ S, ∀ u < alignedTime s t,
      trace (machine M hs) (List.ofFn Y) u = trace (machine M hs) (List.ofFn X) u :=
    fun Y hY u _ => congrArg (fun τ => τ u) (common Y hY)
  have hcorrect : ∀ Y ∈ S, ∀ p ∈ Q,
      (outBit (machine M hs) (List.ofFn Y) (root p)).getD false = Y p := fun Y hY p _ =>
    common_simulator_root hs H (correct Y hY) (common Y hY) p
  have htarget : demandedReadSteps (trace (machine M hs) (List.ofFn X)) P (alignedTime s t) Q ⊆
      inputReadSteps (trace (machine M hs) (List.ofFn X)) (alignedTime s t) (inputErosion U (3 * s)) :=
    demandedReadSteps_subset_inputReadSteps _ Q _ (fun _p hp => (mem_filter.mp hp).2)
  have hroots : Q.image root = I.image (simulatorOrdinal M hs (List.ofFn X) t P) := by
    rw [Finset.image_image]
    rfl
  have hcut' : IsMengerVertexCut (trace (machine M hs) (List.ofFn X)).work (alignedTime s t)
      (Q.image root) (demandedReadSteps (trace (machine M hs) (List.ofFn X)) P (alignedTime s t) Q) Γ := by
    intro ρ u hu hp hend
    exact hΓcut ρ u (hroots ▸ hu) hp (htarget hend)
  have hinvoice := native_frozen_full_invoice S ⟨X, hX⟩ Q Γ root hroot htrace hcorrect hcut'
  have hcard : (Γ.card : ℝ) ≤ (erodedCutFactor M.k s * B.card + (2 * s - 1) : ℕ) := by
    exact_mod_cast hΓcard
  have hwidth := mul_le_mul_of_nonneg_left hcard (Nat.cast_nonneg (valueWidth (machine M hs)))
  have hh := hinvoice.1.trans (hinvoice.2.trans hwidth)
  dsimp only [P, Q] at hh
  linarith

/-- Any finite integer interval cover pays its two radius strips. Raw-bit
coordinates are injected into the integer line, so no endpoint or fragmented
component is lost when passing to the finite Boolean cube. -/
theorem erodedDemand_loss {P : ℕ} {ι : Type*} (I : Finset ι) (left right : ι → ℤ)
    (R : ℕ) (V : Finset (Fin P))
    (hV : ∀ p ∈ V, (p.val : ℤ) ∈ I.biUnion fun i => Icc (left i) (right i)) :
    V.card ≤ (erodedDemand V (I.biUnion fun i => Icc (left i) (right i)) R).card + 2 * R * I.card := by
  classical
  let f : Fin P → ℤ := fun p => p.val
  have hf : Function.Injective f := by
    intro p q he
    apply Fin.ext
    change (p.val : ℤ) = (q.val : ℤ) at he
    exact_mod_cast he
  let U := I.biUnion fun i => Icc (left i) (right i)
  have hsub : V.image f ⊆ U := by
    intro z hz
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hz
    exact hV p hp
  have hi : V.image f ∩ inputErosion U R = (erodedDemand V U R).image f := by
    ext z
    constructor
    · intro hz
      obtain ⟨hv, he⟩ := mem_inter.mp hz
      obtain ⟨p, hp, rfl⟩ := mem_image.mp hv
      exact mem_image.mpr ⟨p, mem_filter.mpr ⟨hp, he⟩, rfl⟩
    · intro hz
      obtain ⟨p, hp, rfl⟩ := mem_image.mp hz
      exact mem_inter.mpr ⟨mem_image_of_mem f (mem_filter.mp hp).1, (mem_filter.mp hp).2⟩
  have hh := demanded_erosion_loss I left right R (V.image f) hsub
  change (V.image f).card ≤ (V.image f ∩ inputErosion U R).card + 2 * R * I.card at hh
  rw [hi, card_image_of_injective _ hf, card_image_of_injective _ hf] at hh
  exact hh

/-- The displayed |V|−6sr consequence for any r-interval cover, including
the maximal components as a special case. The finite result has no
canonical-width or asymptotic assumption. -/
theorem native_eroded_fibre_invoice_cover {M : TM} {d b s t : ℕ} {ι : Type*}
    (hs : 0 < s) (S : Finset (Fin (d * d * b) → Bool))
    (X : Fin (d * d * b) → Bool) (hX : X ∈ S) (H : HaltsAt M (List.ofFn X) t)
    (correct : ∀ Y ∈ S, OutputsTranspose M d b Y)
    (common : ∀ Y ∈ S, trace (machine M hs) (List.ofFn Y) = trace (machine M hs) (List.ofFn X))
    (V : Finset (Fin (d * d * b))) (I : Finset ι) (left right : ι → ℤ)
    (hV : ∀ p ∈ V, (p.val : ℤ) ∈ I.biUnion fun i => Icc (left i) (right i))
    (B : Finset ℕ) (hB : ∀ u ∈ B, u < t)
    (hcut : IsMengerVertexCut (trace M (List.ofFn X)).work t
      (V.image fun p => sourceOrdinal M (List.ofFn X) t (d * d * b) (tposOf d b p))
      (inputReadSteps (trace M (List.ofFn X)) t (I.biUnion fun i => Icc (left i) (right i))) B) :
    (V.card : ℝ) - (6 * s * I.card : ℕ) ≤
      ((d * d * b : ℕ) : ℝ) - Real.logb 2 (S.card : ℝ) +
        (valueWidth (machine M hs) : ℝ) *
          (erodedCutFactor M.k s * B.card + (2 * s - 1) : ℕ) := by
  have hc := native_eroded_fibre_invoice hs S X hX H correct common V _ B hB hcut
  have hl := erodedDemand_loss I left right (3 * s) V hV
  have hl' : (V.card : ℝ) ≤
      ((erodedDemand V (I.biUnion fun i => Icc (left i) (right i)) (3 * s)).card : ℝ) +
        (6 * s * I.card : ℕ) := by
    have he : 2 * (3 * s) * I.card = 6 * s * I.card := by ring
    rw [he] at hl
    exact_mod_cast hl
  linarith

end AdaptiveTransfer.TransferEroded
