import AdaptiveTransfer.TransferEntryMaximum
import TapeStorageRates.NativeTypicalResources
import TapeStorageRates.PaidInputsLimits
import LeanMachine.FiniteSmallFibres

/-! One actual complete-trace event controls every certificate valid on each
large frozen fibre. The trace support is the published native simulator bound
on the indicated successful subset, not an entropy hypothesis. -/

namespace AdaptiveTransfer.TransferEntry
open Finset Transpose MergeDepth TapeStorageRates Filter
attribute [local instance] Classical.propDecidable

noncomputable def traceFibre {L : ℕ} (N : TM) (G : Finset (Fin L → Bool))
    (X : Fin L → Bool) : Finset (Fin L → Bool) :=
  G.filter fun Y => trace N (List.ofFn Y) = trace N (List.ofFn X)

noncomputable def smallTrace {L : ℕ} (N : TM) (G : Finset (Fin L → Bool))
    (δ : ℝ) : Finset (Fin L → Bool) :=
  LeanMachine.FiniteSmallFibres.small G (fun X => trace N (List.ofFn X))
    ((2 : ℝ) ^ ((1 - δ) * L))

theorem good_trace_fibre {L : ℕ} {N : TM} {G : Finset (Fin L → Bool)} {δ : ℝ}
    {X : Fin L → Bool} (hx : X ∈ G) (hgood : X ∉ smallTrace N G δ) :
    X ∈ traceFibre N G X ∧
      (L : ℝ) - Real.logb 2 ((traceFibre N G X).card : ℝ) ≤ δ * L := by
  have hX : X ∈ traceFibre N G X := mem_filter.mpr ⟨hx, rfl⟩
  have hsize : (2 : ℝ) ^ ((1 - δ) * L) ≤ (traceFibre N G X).card := by
    by_contra hn
    exact hgood (mem_filter.mpr ⟨hx, lt_of_not_ge hn⟩)
  have hlog := (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2)
    (by exact_mod_cast (show (traceFibre N G X).Nonempty from ⟨X, hX⟩).card_pos)).mpr hsize
  exact ⟨hX, by linarith⟩

noncomputable def traceRateNumerator (M : TM) (c : ℝ) : ℝ :=
  (2 * c + 1) * Real.logb 2 (1 + 2 * 3 ^ (M.k + 1) : ℕ)

/-- Strict count, including the empty successful subset. Only the source
machine's actual timely correctness is assumed. -/
theorem native_smallTrace_card {M : TM} {s d b : ℕ} (hs : 0 < s) {c δ : ℝ}
    (hc : 0 ≤ c) (hL : 11 * s + 1 ≤ d * d * b + 1)
    (hbudget : traceRateNumerator M c / s ≤ δ / 2)
    (G : Finset (Fin (d * d * b) → Bool))
    (hG : ∀ X ∈ G, TransposesInput M d b c X) :
    ((smallTrace (Native.machine M hs) G δ).card : ℝ) <
      (2 : ℝ) ^ ((1 - δ / 2) * (d * d * b : ℕ)) := by
  let N := Native.machine M hs
  have hcount : ((G.image (fun X => trace N (List.ofFn X))).card : ℝ) ≤
      (2 : ℝ) ^ ((δ / 2) * (d * d * b : ℕ)) := by
    by_cases hne : G.Nonempty
    · have hres := (native_success_resources M hs hc hL G hG).2
      have hl : Real.logb 2 ((G.image (fun X => trace N (List.ofFn X))).card : ℝ) ≤
          (δ / 2) * (d * d * b : ℕ) := by
        apply hres.trans
        calc
          _ = (traceRateNumerator M c / s) * (d * d * b : ℕ) := by
            unfold traceRateNumerator
            ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hbudget (by positivity)
      exact (Real.logb_le_iff_le_rpow (by norm_num)
        (by exact_mod_cast (hne.image (fun X => trace N (List.ofFn X))).card_pos)).mp hl
    · have he : G = ∅ := not_nonempty_iff_eq_empty.mp hne
      simp only [he, image_empty, card_empty, Nat.cast_zero]
      positivity
  have hh := LeanMachine.FiniteSmallFibres.small_exponential_card G
    (fun X => trace N (List.ofFn X)) (r := (1 - δ) * (d * d * b : ℕ))
    (by norm_num : (0 : ℝ) < 2) hcount
  have he : (δ / 2) * (d * d * b : ℕ) + (1 - δ) * (d * d * b : ℕ) =
      (1 - δ / 2) * (d * d * b : ℕ) := by ring
  simpa only [smallTrace, N, he] using hh

/-- Choose the batch size before dimension, the successful subset, any cut,
and any entry set. The threshold also ensures b>=24s for the final cut bound. -/
theorem exists_uniform_trace_event (M : TM) {c δ : ℝ} (hc : 0 ≤ c) (hδ : 0 < δ) :
    ∃ s : ℕ, ∃ hs : 0 < s, ∃ d₀ : ℕ, ∀ d ≥ d₀,
      24 * s ≤ entryBits d ∧
      ∀ G : Finset (Fin (d * d * entryBits d) → Bool),
        (∀ X ∈ G, TransposesInput M d (entryBits d) c X) →
        ((smallTrace (Native.machine M hs) G δ).card : ℝ) <
          (2 : ℝ) ^ ((1 - δ / 2) * (d * d * entryBits d : ℕ)) := by
  let s := ⌈2 * traceRateNumerator M c / δ⌉₊ + 1
  have hs : 0 < s := by dsimp [s]; omega
  have hsR : 0 < (s : ℝ) := by exact_mod_cast hs
  have hnum : 2 * traceRateNumerator M c / δ ≤ (s : ℝ) := by
    have hh := Nat.le_ceil (2 * traceRateNumerator M c / δ)
    dsimp [s]
    push_cast
    linarith
  have hbudget : traceRateNumerator M c / s ≤ δ / 2 := by
    have hh := (div_le_iff₀ hδ).mp hnum
    apply (div_le_iff₀ hsR).mpr
    nlinarith
  obtain ⟨d₀, hd₀⟩ := eventually_atTop.mp
    ((eventually_ge_atTop 1).and (PaidInputs.tendsto_entryBits.eventually_ge_atTop (24 * s)))
  refine ⟨s, hs, d₀, fun d hd => ?_⟩
  obtain ⟨hd1, hb⟩ := hd₀ d hd
  refine ⟨hb, fun G hG => native_smallTrace_card hs hc ?_ hbudget G hG⟩
  have hbP : entryBits d ≤ d * d * entryBits d := by
    exact Nat.le_mul_of_pos_left _ (Nat.mul_pos hd1 hd1)
  omega

/-- The final arithmetic: a fractional capacity loss on at least alpha of
the entries gives the stated source-cut lower bound. -/
theorem original_cut_lower_bound {V : Type*} [Fintype V] [DecidableEq V]
    (Q : V → Finset V) {d b s v G B : ℕ} {ρ α : ℝ}
    (hρ : 0 ≤ ρ) (hb : 24 * s ≤ b) (hden : 0 < v * G)
    (hsize : α * (d : ℝ) ^ 2 ≤ Fintype.card V)
    (hcap : capacity Q (b - 6 * s) ≤ (1 - ρ) * (b - 6 * s : ℕ) * Fintype.card V)
    (hdef : deficit Q (b - 6 * s) ≤ (ρ * α / 4) * (d * d * b : ℕ) + (v * G : ℕ) * B) :
    ρ * b * Fintype.card V / (2 * (v * G : ℕ)) ≤ (B : ℝ) := by
  have hm : 6 * s ≤ b := by omega
  have hbR : 24 * (s : ℝ) ≤ b := by exact_mod_cast hb
  have hmargin : 3 * (b : ℝ) / 4 ≤ (b - 6 * s : ℕ) := by
    rw [Nat.cast_sub hm]
    push_cast
    linarith
  have hdeflo : ρ * (b - 6 * s : ℕ) * Fintype.card V ≤ deficit Q (b - 6 * s) := by
    unfold deficit
    nlinarith
  have hlo := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmargin hρ)
    (Nat.cast_nonneg (Fintype.card V))
  have hcharge := mul_le_mul_of_nonneg_left hsize (show 0 ≤ ρ * (b : ℝ) / 4 by positivity)
  have hdenR : (0 : ℝ) < v * G := by exact_mod_cast hden
  rw [div_le_iff₀ (show (0 : ℝ) < 2 * (v * G : ℕ) by exact mul_pos (by norm_num) (by exact_mod_cast hden))]
  push_cast at hdef ⊢
  nlinarith

end AdaptiveTransfer.TransferEntry
