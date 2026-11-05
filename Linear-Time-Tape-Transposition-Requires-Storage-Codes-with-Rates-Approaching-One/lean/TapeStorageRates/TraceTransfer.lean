import TapeStorageRates.NativeTypicalResources
import TapeStorageRates.TraceCriterion
import TapeStorageRates.Statement

/-! # Transferring Paper 14's native criterion through the aligned simulator -/

namespace TapeStorageRates

open Filter Finset Transpose Transpose.Tape Transpose.Tape.Impl MergeDepth BoundedStackDepth

set_option autoImplicit false

open Classical in
/-- One batch size and the physical coefficient 11c+1 work at every positive entry
width once the dimension is sufficiently large. -/
theorem aligned_low_trace_dimensions (M : TM) {c η : ℝ} (hc : 0 ≤ c) (hη : 0 < η) :
    ∃ s : ℕ, ∃ hs : 0 < s, ∀ᶠ d : ℕ in atTop, ∀ b : ℕ, 1 ≤ b →
      TransposesAtWidth M d b c →
      TransposesAtWidth (Native.machine M hs) d b (11*c+1) ∧
      Real.logb 2 (univ.image (fun x : Fin (d*d*b) → Bool =>
        trace (Native.machine M hs) (List.ofFn x))).card ≤ η*(d*d*b : ℕ) := by
  let a := (2*c+1) * Real.logb 2 (1+2*3^(M.k+1) : ℕ)
  obtain ⟨s,hs⟩ := exists_nat_gt (max 0 (a/η))
  have hs0 : 0 < s := by exact_mod_cast (le_max_left _ _).trans_lt hs
  have hcoef := (div_lt_iff₀ hη).mp ((le_max_right _ _).trans_lt hs)
  refine ⟨s,hs0,(eventually_ge_atTop (11*s+1)).mono fun d hd b hb hgood => ?_⟩
  have hL : 11*s+1 ≤ d*d*b+1 :=
    hd.trans (((Nat.le_mul_self d).trans (Nat.le_mul_of_pos_right _ hb)).trans (Nat.le_succ _))
  refine ⟨fun A => aligned_computesWithin_large hs0 hc hL (hgood A), ?_⟩
  have hcount := (native_success_resources M hs0 hc hL univ (fun x _ => hgood.transposesInput x)).2
  apply hcount.trans ((div_le_iff₀ (Nat.cast_pos.mpr hs0 : 0 < (s:ℝ))).mpr ?_)
  change a*(d*d*b : ℕ) ≤ _
  nlinarith only [mul_le_mul_of_nonneg_right hcoef.le (Nat.cast_nonneg (d*d*b) (α := ℝ))]

/-- A single fixed aligned simulator suffices for the native coding test of each fixed source.
The theorem is independent of the original machine's trace entropy. -/
theorem native_frozen_trace_exclusion (M : TM) {c η : ℝ} (hc : 0 < c)
    (hη : 0 < η) (hhalf : η < 1/2) :
    ∃ s : ℕ, ∃ hs : 0 < s, ∃ c' : ℝ, 0 < c' ∧
      let N := Native.machine M hs
      NativeBound (fun d b => b = entryBits d) N 1
        (genieDepth N.k (blockWidth N 1) (max c' 1) ((1/2-η)/2)) c' →
      ∀ᶠ d in atTop, ¬ TransposesAt M d c := by
  obtain ⟨s,hs,h⟩ := aligned_low_trace_dimensions M hc.le hη
  have ht : 0 < 11*c+1 := by positivity
  refine ⟨s,hs,11*c+1,ht,fun hnative => ?_⟩
  apply native_exclusion_of_trace_support (Native.machine M hs) ht hhalf hnative (fun d => TransposesAt M d c)
  exact h.mono fun d hd => hd (entryBits d) (one_le_entryBits d)

/-- Fix one valid simulator and time coefficient for each source test. A native coding bound
for those chosen simulators suffices to rule out the frozen all-dimensions statement (T). -/
theorem native_tests_exclude_linear {η : ℝ} (hη : 0 < η) (hhalf : η < 1/2) :
    ∃ (s : TM → {c : ℝ // 0 < c} → ℕ)
      (hs : ∀ M c, 0 < s M c) (t : TM → {c : ℝ // 0 < c} → ℝ),
      (∀ M c, 0 < t M c) ∧
      ((∀ M c, let N := Native.machine M (hs M c)
              NativeBound (fun d b => b = entryBits d) N 1
                (genieDepth N.k (blockWidth N 1) (max (t M c) 1) ((1/2-η)/2)) (t M c)) →
        ¬ LinearTimeTransposable) := by
  classical
  have tests (M : TM) (c : {c : ℝ // 0 < c}) := native_frozen_trace_exclusion M c.2 hη hhalf
  choose s hs t ht htest using tests
  refine ⟨s, hs, t, ht, ?_⟩
  intro hbound hlinear
  obtain ⟨M, c, hc, hgood⟩ := unbounded_success_of_linear hlinear
  obtain ⟨d₀, h₀⟩ := eventually_atTop.mp (htest M ⟨c,hc⟩ (hbound M ⟨c,hc⟩))
  obtain ⟨d, hd, htr⟩ := hgood d₀
  exact h₀ d hd htr

end TapeStorageRates
