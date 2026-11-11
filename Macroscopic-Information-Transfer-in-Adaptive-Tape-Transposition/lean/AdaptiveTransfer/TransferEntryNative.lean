import AdaptiveTransfer.TransferEntryCapacity
import AdaptiveTransfer.TransferEntryTraceTail
import AdaptiveTransfer.TransferNativeCones
import AdaptiveTransfer.TransferCorrectOutputs

/-! The finite original-entry capacity theorem on actual source runs and
actual aligned native simulators. A single reference input fixes the source
relation and guard; all code inputs share only the simulator trace. -/

namespace AdaptiveTransfer.TransferEntry
open Finset Transpose Transpose.Tape MergeDepth DirectedRecovery
open TapeStorageRates TransferFIFO TransferRoots TransferCones TransferCorrect
attribute [local instance] Classical.propDecidable

noncomputable def originalCones {d b : ℕ} (M : TM) (X : Fin (d * d * b) → Bool)
    (t : ℕ) (B : Finset ℕ) (p : Fin (d * d * b)) : Finset (Fin (d * d * b)) :=
  nativeInputCone (trace M (List.ofFn X)) (d * d * b) t B
    (sourceRoot M (List.ofFn X) t (tposOf d b p).val)

noncomputable def originalRelation {d b : ℕ} (M : TM) (X : Fin (d * d * b) → Bool)
    (t : ℕ) (B : Finset ℕ) : Fin (d * d) → Finset (Fin (d * d)) :=
  entryQuotient (originalCones M X t B)

/-- Actual finite Theorem Q. No source-trace fibre, linearity, acyclicity,
missing self-edge, positive retained width, or chosen code containing X is
required. The only shared trace is that of the actual aligned simulator. -/
theorem native_original_entry_capacity {M : TM} {d b s t : ℕ}
    (hs : 0 < s) (hd : 0 < d) (hb : 0 < b)
    (S : Finset (Fin (d * d * b) → Bool)) {X : Fin (d * d * b) → Bool} (hX : X ∈ S)
    (H : HaltsAt M (List.ofFn X) t)
    (hcorrect : ∀ Y ∈ S, OutputsTranspose M d b Y)
    (htrace : ∀ Y ∈ S, trace (Native.machine M hs) (List.ofFn Y) =
      trace (Native.machine M hs) (List.ofFn X))
    (B : Finset ℕ) (hB : ∀ u ∈ B, u < t) (J : Finset (Fin (d * d))) :
    deficit (inducedNeighborhood (originalRelation M X t B) J) (b - 6 * s) ≤
      (d * d * b : ℕ) - Real.logb 2 (S.card : ℝ) +
        (valueWidth (Native.machine M hs) : ℝ) * guardCoefficient M.k s * B.card := by
  have hcount := correct_source_count H (hcorrect X hX)
  have ht : 1 ≤ t := by
    have hp := Nat.mul_pos (Nat.mul_pos hd hd) hb
    have hh := outputCount_add_le M (List.ofFn X) 0 t
    simp only [Nat.zero_add] at hh
    have hz : outputCount M (List.ofFn X) 0 = 0 := rfl
    rw [hz, hcount, Nat.zero_add] at hh
    omega
  obtain ⟨Γ, hΓ, _, hcone⟩ := native_cone_transport_interior
    (L := d * d * b) (P := d * d * b) hs ht H hcount.ge B hB
  have hfinite := entry_capacity_of_cone_containment
    (M := Native.machine M hs) (T := alignedTime s t)
    (τ := trace (Native.machine M hs) (List.ofFn X)) S J Γ
    (fun p => simulatorRoot M hs (List.ofFn X) t (tposOf d b p).val)
    (originalCones M X t B) (futureTarget s)
    (fun p _ => (correct_simulator_root hs H (hcorrect X hX) p).1)
    (fun Y hY u _ => congrFun (htrace Y hY) u)
    (fun Y hY p _ => common_simulator_root hs H (hcorrect Y hY) (htrace Y hY) p)
    (fun p hp => entry_futureTarget (mem_retainedBits.mp hp).2.2)
    (fun p hp hroot => ?_) ⟨X, hX⟩
  · change deficit (inducedNeighborhood (originalRelation M X t B) J) (b - 6 * s) ≤ _ at hfinite
    apply hfinite.trans
    have hc : (Γ.card : ℝ) ≤ (guardCoefficient M.k s : ℝ) * B.card := by exact_mod_cast hΓ
    nlinarith [mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg (valueWidth (Native.machine M hs)))]
  · have hfuture := (interior_output_lookahead (mem_retainedBits.mp hp).2.2).1
    have hh := hcone (tposOf d b p) hfuture hroot
    simpa only [originalCones, futureTarget, dite_eq_left hfuture, tposOf_tposOf,
      simulatorOrdinal] using hh

/-- Every source cut and entry set is certified on the same good complete
simulator fibre; the quantified source execution belongs to the reference
input only. -/
def EntryCertificates {d b s : ℕ} (M : TM) (hs : 0 < s) (δ : ℝ)
    (X : Fin (d * d * b) → Bool) : Prop :=
  ∀ t, HaltsAt M (List.ofFn X) t → ∀ B : Finset ℕ, (∀ u ∈ B, u < t) →
    ∀ J : Finset (Fin (d * d)),
      deficit (inducedNeighborhood (originalRelation M X t B) J) (b - 6 * s) ≤
        δ * (d * d * b : ℕ) +
          (valueWidth (Native.machine M hs) : ℝ) * guardCoefficient M.k s * B.card

theorem good_trace_certificates {M : TM} {d b s : ℕ} {δ : ℝ}
    (hs : 0 < s) (hd : 0 < d) (hb : 0 < b)
    (G : Finset (Fin (d * d * b) → Bool))
    (hG : ∀ Y ∈ G, OutputsTranspose M d b Y) {X : Fin (d * d * b) → Bool}
    (hX : X ∈ G) (hgood : X ∉ smallTrace (Native.machine M hs) G δ) :
    EntryCertificates M hs δ X := by
  obtain ⟨hXF, hdef⟩ := good_trace_fibre hX hgood
  intro t H B hB J
  have hh := native_original_entry_capacity hs hd hb _ hXF H
    (fun Y hY => hG Y (mem_filter.mp hY).1)
    (fun _ hY => (mem_filter.mp hY).2) B hB J
  linarith

/-- The actual set violating any certificate is contained in one small-fibre
set. There is no union over cuts, entry sets, or reference runs. -/
theorem violations_subset_smallTrace {M : TM} {d b s : ℕ} {δ : ℝ}
    (hs : 0 < s) (hd : 0 < d) (hb : 0 < b)
    (G : Finset (Fin (d * d * b) → Bool)) (hG : ∀ Y ∈ G, OutputsTranspose M d b Y) :
    (G.filter fun X => ¬ EntryCertificates M hs δ X) ⊆ smallTrace (Native.machine M hs) G δ := by
  intro X hX
  by_contra hgood
  exact (mem_filter.mp hX).2
    (good_trace_certificates hs hd hb G hG (mem_filter.mp hX).1 hgood)

/-- Uniform actual success tail for all original entry certificates. Batch
size and dimension threshold precede the successful set and every cut/index.
The result is slightly stronger than the stated 0<delta<1 regime. -/
theorem uniform_entry_success_tail (M : TM) {c δ : ℝ} (hc : 0 ≤ c) (hδ : 0 < δ) :
    ∃ s : ℕ, ∃ hs : 0 < s, ∃ d₀ : ℕ, ∀ d ≥ d₀,
      24 * s ≤ entryBits d ∧
      ∀ G : Finset (Fin (d * d * entryBits d) → Bool),
        (∀ X ∈ G, TransposesInput M d (entryBits d) c X) →
        ((G.filter fun X => ¬ EntryCertificates M hs δ X).card : ℝ) <
          (2 : ℝ) ^ ((1 - δ / 2) * (d * d * entryBits d : ℕ)) := by
  obtain ⟨s, hs, d₀, hd₀⟩ := exists_uniform_trace_event M hc hδ
  refine ⟨s, hs, max d₀ 1, fun d hd => ?_⟩
  obtain ⟨hb, htail⟩ := hd₀ d ((le_max_left _ _).trans hd)
  refine ⟨hb, fun G hG => ?_⟩
  have hsub := violations_subset_smallTrace hs
    ((le_max_right _ _).trans hd) (one_le_entryBits d) G
    (fun Y hY => (hG Y hY).outputsTranspose) (δ := δ)
  exact lt_of_le_of_lt (by exact_mod_cast card_le_card hsub) (htail G hG)

/-- The quantitative cut consequence on that same event, with the literal
complete simulator width and the exact native guard coefficient. -/
theorem certified_original_cut_lower_bound {M : TM} {d b s t : ℕ} {ρ α : ℝ}
    (hs : 0 < s) (hρ : 0 ≤ ρ) (hb : 24 * s ≤ b)
    {X : Fin (d * d * b) → Bool} (hcert : EntryCertificates M hs (ρ * α / 4) X)
    (H : HaltsAt M (List.ofFn X) t) (B : Finset ℕ) (hB : ∀ u ∈ B, u < t)
    (J : Finset (Fin (d * d))) (hsize : α * (d : ℝ) ^ 2 ≤ J.card)
    (hcap : capacity (inducedNeighborhood (originalRelation M X t B) J) (b - 6 * s) ≤
      (1 - ρ) * (b - 6 * s : ℕ) * J.card) :
    ρ * b * J.card /
      (2 * (valueWidth (Native.machine M hs) * guardCoefficient M.k s : ℕ)) ≤ (B.card : ℝ) := by
  have hden : 0 < valueWidth (Native.machine M hs) * guardCoefficient M.k s := by
    apply Nat.mul_pos
    · unfold valueWidth
      omega
    · unfold guardCoefficient
      omega
  simpa only [Fintype.card_coe] using original_cut_lower_bound
    (inducedNeighborhood (originalRelation M X t B) J) (d := d) (B := B.card)
    hρ hb hden (by simpa only [Fintype.card_coe] using hsize)
    (by simpa only [Fintype.card_coe] using hcap)
    (by simpa only [Nat.cast_mul] using hcert t H B hB J)

end AdaptiveTransfer.TransferEntry
