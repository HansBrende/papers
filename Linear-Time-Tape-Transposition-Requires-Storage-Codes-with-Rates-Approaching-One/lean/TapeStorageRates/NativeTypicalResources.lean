import TapeStorageRates.NativeSupportRate
import MergeDepth.LowAdaptivity
import Transpose.Eventually

/-! # Uniform physical clock and trace budget on the successful inputs -/

namespace TapeStorageRates

open Finset Transpose Transpose.Tape Transpose.Tape.Impl MergeDepth

set_option autoImplicit false

/-- The physical clock of the unprefixed aligned simulator. -/
def alignedTime (s t : ℕ) : ℕ := (10*s+1)*(t/s+1)+s

theorem alignedTime_le_affine (s t : ℕ) :
    alignedTime s t ≤ 11*t + (11*s+1) := by
  dsimp [alignedTime]
  nlinarith [Nat.div_mul_le_self t s, Nat.div_le_self t s]

/-- Transfer any input/output computation to the exact batched clock, including small
inputs. The bound is monotone in the source deadline. -/
theorem aligned_computesWithin {M : TM} {s T : ℕ} (hs : 0 < s) {w out : List Bool}
    (h : ComputesWithin M w out T) :
    ComputesWithin (Native.machine M hs) w out (alignedTime s T) := by
  obtain ⟨t,ht,halt,hw⟩ := (computesWithin_iff _ _).mp h
  obtain ⟨hh,ho⟩ := Native.simulates_halt M hs _ halt
  refine (computesWithin_iff _ _).mpr ⟨alignedTime s t,?_,hh,(congrArg List.reverse ho).trans hw⟩
  unfold alignedTime
  gcongr

/-- On sufficiently long inputs the same time coefficient works for all batch sizes. -/
theorem aligned_computesWithin_large {M : TM} {s L : ℕ} (hs : 0 < s) {c : ℝ} (hc : 0 ≤ c)
    (hL : 11*s+1 ≤ L+1) {w out : List Bool} (h : ComputesWithin M w out ⌊c*((L:ℝ)+1)⌋₊) :
    ComputesWithin (Native.machine M hs) w out ⌊(11*c+1)*((L:ℝ)+1)⌋₊ := by
  let U := ⌊c*((L:ℝ)+1)⌋₊
  have hu : (U:ℝ) ≤ c*((L:ℝ)+1) := Nat.floor_le (by positivity)
  have ht : (alignedTime s U : ℝ) ≤ 11*(U:ℝ)+(11*(s:ℝ)+1) := by exact_mod_cast alignedTime_le_affine s U
  have hstart : 11*(s:ℝ)+1 ≤ (L:ℝ)+1 := by exact_mod_cast hL
  exact (aligned_computesWithin hs h).mono (Nat.le_floor (by nlinarith only [hu,ht,hstart]))

open Classical in
/-- Count the complete simulator traces on any set of timely correct inputs. The
common output length follows from transposition. -/
theorem native_correct_trace_count (M : TM) {s d b : ℕ} (hs : 0 < s) (c : ℝ)
    (G : Finset (Fin (d*d*b) → Bool)) (hG : ∀ x ∈ G, TransposesInput M d b c x) :
    let U := ⌊c * ((d*d*b : ℕ) + 1)⌋₊
    Real.logb 2 (G.image (fun x => trace (Native.machine M hs) (List.ofFn x))).card ≤
      (((U / s + 1 : ℕ) : ℝ)) * Real.logb 2 (1+2*3^(M.k+1) : ℕ) := by
  apply Native.source_trace_log_count M hs (d*d*b) _ (d*d*b) G
  intro x hx
  obtain ⟨t,ht,hhalt⟩ := (hG x hx).halts
  obtain ⟨u,hu,hlen,_⟩ := (hG x hx).outputsTranspose.output
  obtain rfl := haltsAt_unique hhalt hu
  exact ⟨t,ht,hhalt,by simpa using hlen⟩

open Classical in
/-- The simulator coefficient is independent of its batch size once the large input
absorbs the fixed startup time. The only correctness assumption is on the indicated set. -/
theorem native_success_resources (M : TM) {s d b : ℕ} (hs : 0 < s) {c : ℝ} (hc : 0 ≤ c)
    (hL : 11*s+1 ≤ d*d*b+1) (G : Finset (Fin (d*d*b) → Bool))
    (hG : ∀ x ∈ G, TransposesInput M d b c x) :
    (∀ x ∈ G, TransposesInput (Native.machine M hs) d b (11*c+1) x) ∧
      Real.logb 2 (G.image (fun x => trace (Native.machine M hs) (List.ofFn x))).card ≤
        (2*c+1) * Real.logb 2 (1+2*3^(M.k+1) : ℕ) * (d*d*b : ℕ) / s := by
  let L := d*d*b
  let U := ⌊c*((L:ℝ)+1)⌋₊
  have hU : (U:ℝ) ≤ c*((L:ℝ)+1) := Nat.floor_le (by positivity)
  constructor
  · intro x hx
    obtain ⟨A,hA,hcA⟩ := hG x hx
    exact ⟨A,hA,aligned_computesWithin_large hs hc hL hcA⟩
  · have hcount := native_correct_trace_count M hs c G hG
    have hsR : 0 < (s : ℝ) := by exact_mod_cast hs
    have hsmall : s ≤ L := by dsimp [L]; omega
    have hL1 : 1 ≤ (L:ℝ) := by exact_mod_cast hs.trans_le hsmall
    have hdiv : ((U/s : ℕ):ℝ)*s ≤ U := by exact_mod_cast Nat.div_mul_le_self U s
    have hsteps : (((U/s+1 : ℕ):ℝ)) * s ≤ (2*c+1)*L := by
      push_cast
      nlinarith only [hdiv,hU, (Nat.cast_le.mpr hsmall : (s:ℝ) ≤ L), mul_nonneg hc (sub_nonneg.mpr hL1)]
    have hh : 0 ≤ Real.logb 2 (1+2*3^(M.k+1) : ℕ) :=
      Real.logb_nonneg (by norm_num) (by exact_mod_cast Nat.le_add_right 1 _)
    apply hcount.trans ((le_div_iff₀ hsR).mpr ?_)
    calc
      _ = ((((U/s+1 : ℕ):ℝ))*s) * Real.logb 2 (1+2*3^(M.k+1) : ℕ) := by ring
      _ ≤ _ := (mul_le_mul_of_nonneg_right hsteps hh).trans_eq (by dsimp [L]; ring)

end TapeStorageRates
