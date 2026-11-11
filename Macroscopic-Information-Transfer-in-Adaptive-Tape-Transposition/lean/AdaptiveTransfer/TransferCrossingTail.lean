import AdaptiveTransfer.TransferCrossingFibre
import AdaptiveTransfer.TransferCrossingRates
import AdaptiveTransfer.TransferEntryTraceTail

/-! Original-execution macroscopic crossing expansion on one actual good
event. Successful-subset simulator traces are used only internally; original
traces, append roots, and crossing targets remain those of each reference run.
-/

namespace AdaptiveTransfer.TransferCrossing
open Finset Filter Transpose Transpose.Tape Transpose.Tape.Impl MergeDepth NativeRelations
open TapeStorageRates TransferFIFO TransferRoots TransferCorrect TransferEntry
attribute [local instance] Classical.propDecidable

/-- All large demand sets and all source cuts on the actual original run.
The source cut may contain irrelevant vertices outside the live horizon;
the finite transfer trims them, so they require no extra premise here. -/
def OriginalCrossingExpansion (M : TM) (d : ℕ) (α lam β : ℝ)
    (X : Fin (d * d * entryBits d) → Bool) : Prop :=
  ∀ t, HaltsAt M (List.ofFn X) t →
    ∀ V : Finset (Fin (d * d * entryBits d)),
      α * (d * d * entryBits d : ℕ) ≤ V.card → ∀ B : Finset ℕ,
      IsMengerVertexCut (trace M (List.ofFn X)).work t
        (V.image fun p => sourceOrdinal M (List.ofFn X) t
          (d * d * entryBits d) (tposOf d (entryBits d) p))
        (crossingLowerEtaSteps (trace M (List.ofFn X)) t
          ⌊lam * (d * d * entryBits d : ℕ)⌋₊ 1 t) B →
      β * V.card ≤ (B.card : ℝ)

/-- The complete original-execution crossing theorem. Its constants precede
dimension, the successful set, all original runs, demand sets and cuts. No
original-trace heaviness, all-input correctness, or geometric certificate is
assumed. It also covers zero work tapes and nonnegative time constants. -/
theorem uniform_original_crossing_expansion (M : TM) {c α : ℝ}
    (hc : 0 ≤ c) (hα : 0 < α) :
    ∃ η lam β : ℝ, 0 < η ∧ 0 < lam ∧ 0 < β ∧ ∃ d₀ : ℕ,
      ∀ d ≥ d₀, ∀ G : Finset (Fin (d * d * entryBits d) → Bool),
        (∀ X ∈ G, TransposesInput M d (entryBits d) c X) →
        ((G.filter fun X => ¬ OriginalCrossingExpansion M d α lam β X).card : ℝ) <
          (2 : ℝ) ^ ((1 - η) * (d * d * entryBits d : ℕ)) := by
  let η := adaptiveBridge_etaStar_tight M.k c α
  have hη : 0 < η := adaptiveBridge_etaStar_tight_pos M.k hc hα
  obtain ⟨s, hs, dtrace, htraceEvent⟩ := exists_uniform_trace_event M hc
    (show 0 < 2 * η by positivity)
  let N := Native.machine M hs
  let C := 11 * c + 1
  let θ := thetaMacro_tight N C α
  let e := cE_frozen_tight N C α
  have hθ : 0 < θ := thetaMacro_tight_pos N C hα
  have he : 0 < e := cE_frozen_tight_pos N C α
  obtain ⟨K, A, _hK, hA, lam, β, hlam, _hlamθ, hβ, hβeq, hbudgets⟩ :=
    exists_uniform_crossing_budgets M.k s (C := C) hθ he hα
  obtain ⟨P₀, hbudgets⟩ := eventually_atTop.mp hbudgets
  let d₀ := max (max dtrace (bridgeMenger_d0_tight N.k C α)) (max 1 P₀)
  refine ⟨η, lam, β, hη, hlam, hβ, d₀, fun d hd G hG => ?_⟩
  have hdtrace : dtrace ≤ d := (le_max_left _ _).trans ((le_max_left _ _).trans hd)
  have hdbridge : bridgeMenger_d0_tight N.k C α ≤ d :=
    (le_max_right _ _).trans ((le_max_left _ _).trans hd)
  have hd1 : 1 ≤ d := (le_max_left _ _).trans ((le_max_right _ _).trans hd)
  have hdP₀ : P₀ ≤ d := (le_max_right _ _).trans ((le_max_right _ _).trans hd)
  let P := d * d * entryBits d
  have hdP : d ≤ P := by
    dsimp [P]
    exact (Nat.le_mul_of_pos_left d hd1).trans
      (Nat.le_mul_of_pos_right _ (one_le_entryBits d))
  obtain ⟨hb24, hsmall⟩ := htraceEvent d hdtrace
  have hstartup : 11 * s + 1 ≤ P + 1 := by
    have hbP : entryBits d ≤ P := Nat.le_mul_of_pos_left _ (Nat.mul_pos hd1 hd1)
    omega
  obtain ⟨hh1, hhH, herror, hphysical⟩ := hbudgets P (hdP₀.trans hdP)
  have hH1 : 1 ≤ ⌊θ * P⌋₊ := hh1.trans hhH
  have hHθ : (⌊θ * P⌋₊ : ℝ) ≤ thetaMacro_tight N C α * P :=
    Nat.floor_le (show 0 ≤ θ * (P : ℝ) by positivity)
  have hηcap : 2 * η ≤ (α / 8) * tightBridgeRho0 N.k C ((19 / 20) * α) := by
    have hNk : N.k = M.k := Native.machine_tapes M hs
    have heq : 2 * η = (α / 8) * tightBridgeRho0 N.k C ((19 / 20) * α) := by
      rw [hNk]
      dsimp [η, adaptiveBridge_etaStar_tight, C, adaptiveBridge_cSim]
      ring
    exact heq.le
  have he_eta : e ≤ cE_frozen_eta_tight N C α (2 * η) :=
    cE_frozen_tight_le_cE_frozen_eta_tight N hα hηcap
  have hNG := (native_success_resources M hs hc hstartup G hG).1
  have hsub : (G.filter fun X => ¬ OriginalCrossingExpansion M d α lam β X) ⊆
      smallTrace N G (2 * η) := by
    intro X hXbad
    have hX := (mem_filter.mp hXbad).1
    by_contra hgood
    apply (mem_filter.mp hXbad).2
    intro t halt V hV B hcut
    let S := traceFibre N G X
    have hXS : X ∈ S := mem_filter.mpr ⟨hX, rfl⟩
    have hcard : (2 : ℝ) ^ ((1 - 2 * η) * P) ≤ (S.card : ℝ) := by
      by_contra hn
      exact hgood (mem_filter.mpr ⟨hX, lt_of_not_ge hn⟩)
    have hcorrect : ∀ Y ∈ S, TransposesInput M d (entryBits d) c Y :=
      fun Y hY => hG Y (mem_filter.mp hY).1
    have hcommon : ∀ Y ∈ S, trace N (List.ofFn Y) = trace N (List.ofFn X) :=
      fun _ hY => (mem_filter.mp hY).2
    let U := alignedTime s t
    have hU : (U : ℝ) ≤ C * ((P : ℝ) + 1) := by
      obtain ⟨u, hu, hhalt⟩ := (hNG X hX).halts
      have heq : u = U := haltsAt_unique hhalt (Native.simulates_halt M hs _ halt).1
      have hh := (Nat.cast_le.mpr hu).trans
        (Nat.floor_le (show 0 ≤ (11 * c + 1) * ((P : ℝ) + 1) by positivity))
      simpa only [heq] using hh
    obtain ⟨hfactor, hepoch⟩ := hphysical U hU
    have hfibre := native_crossing_fibre_bound hs hc hstartup S X hXS halt
      hcorrect hcommon hcard hdbridge hα hH1 hHθ
      (hepoch (trace N (List.ofFn X))) V hV B hcut
    have hbill : e * V.card ≤ A * (B.card : ℝ) + (crossingCutError M.k s K ⌊lam * P⌋₊ : ℝ) := by
      have hlo := mul_le_mul_of_nonneg_right he_eta (Nat.cast_nonneg V.card)
      have hfactorR : (crossingCutFactor M.k s U ⌊θ * P⌋₊ : ℝ) ≤ A := by exact_mod_cast hfactor
      have hhi := mul_le_mul_of_nonneg_right hfactorR (Nat.cast_nonneg B.card)
      change cE_frozen_eta_tight N C α (2 * η) * V.card ≤
        (crossingCutFactor M.k s U ⌊θ * P⌋₊ * B.card +
          crossingCutError M.k s K ⌊lam * P⌋₊ : ℕ) at hfibre
      rw [Nat.cast_add, Nat.cast_mul] at hfibre
      linarith
    rw [hβeq]
    exact expansion_after_transport hA he.le hV hbill herror
  have hcount := lt_of_le_of_lt (show ((G.filter fun X => ¬ OriginalCrossingExpansion M d α lam β X).card : ℝ) ≤
      (smallTrace N G (2 * η)).card by exact_mod_cast card_le_card hsub) (hsmall G hG)
  have heq : 1 - (2 * η) / 2 = 1 - η := by ring
  simpa only [heq] using hcount

end AdaptiveTransfer.TransferCrossing
