import TapeStorageRates.NativeCompiler
import Mathlib.Analysis.SpecificLimits.Basic

/-! # The leading term in full native motion-trace support -/

namespace TapeStorageRates.Native

open Filter Finset Transpose Transpose.Tape MergeDepth
open scoped Topology

set_option autoImplicit false

open Classical in
/-- A pointwise bound on complete physical traces for any subset of timely inputs
with one output length. The simulator's source clock supplies the batch count. -/
theorem source_trace_log_count (M : TM) {s : ℕ} (hs : 0 < s) (L U outLen : ℕ)
    (W : Finset (Fin L → Bool))
    (htime : ∀ x ∈ W, ∃ t ≤ U, HaltsAt M (List.ofFn x) t ∧
      (run M (List.ofFn x) t).outRev.length = outLen) :
    Real.logb 2 (W.image (fun x => trace (machine M hs) (List.ofFn x))).card ≤
      (((U / s + 1 : ℕ) : ℝ)) * Real.logb 2 (1+2*3^(M.k+1) : ℕ) := by
  obtain ⟨S,hS,hall⟩ := source_support_fixed M hs U outLen
  let words := W.image (fun x => trace (machine M hs) (List.ofFn x))
  have hsub : words ⊆ S := by
    rintro τ hτ
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hτ
    obtain ⟨t,ht,hh,hlen⟩ := htime x hx
    exact hall _ _ hh ht hlen
  change Real.logb 2 (words.card : ℝ) ≤ _
  rcases Nat.eq_zero_or_pos words.card with he | hp
  · rw [he,Nat.cast_zero,Real.logb_zero]
    apply mul_nonneg (by positivity) (Real.logb_nonneg (by norm_num) (by exact_mod_cast Nat.le_add_right 1 _))
  · have hle : (words.card : ℝ) ≤ (((1+2*3^(M.k+1))^(U/s+1) : ℕ) : ℝ) := by
      exact_mod_cast (card_le_card hsub).trans hS
    simpa only [Nat.cast_pow, Real.logb_pow] using
      Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) (by exact_mod_cast hp) hle

open Classical in
/-- Fix the batch size before taking the limit. At each input length the set of timely
halting words and their common output length may vary. The support counts the full physical
move, append and halt traces of the actual aligned simulator. -/
theorem trace_support_rate_limsup (M : TM) {s : ℕ} (hs : 0<s) {c : ℝ} (hc : 0≤c)
    (L : ℕ → ℕ) (hL : Tendsto L atTop atTop) (outLen : ℕ → ℕ)
    (W : (i : ℕ) → Finset (Fin (L i) → Bool))
    (htime : ∀ i, ∀ x ∈ W i, ∃ t : ℕ, HaltsAt M (List.ofFn x) t ∧
      (t : ℝ) ≤ c * ((L i : ℝ) + 1) ∧ (run M (List.ofFn x) t).outRev.length = outLen i) :
    limsup (fun i => Real.logb 2 ((W i).image (fun x => trace (machine M hs) (List.ofFn x))).card /
      (L i : ℝ)) atTop ≤ c * Real.logb 2 (1 + 2*3^(M.k+1) : ℕ) / s := by
  let H := 1 + 2 * 3^(M.k+1)
  let h := Real.logb 2 (H : ℝ)
  let U (i : ℕ) := ⌊c*((L i : ℝ) + 1)⌋₊
  let words (i : ℕ) := (W i).image (fun x => trace (machine M hs) (List.ofFn x))
  let B := c*h/s
  have hH : 1 ≤ H := by dsimp [H]; omega
  have hh : 0 ≤ h := Real.logb_nonneg (by norm_num) (by exact_mod_cast hH)
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have count (i : ℕ) : Real.logb 2 (words i).card ≤ (((U i / s : ℕ) : ℝ) + 1) * h := by
    simpa only [Nat.cast_add, Nat.cast_one, words, h, H] using
      source_trace_log_count M hs (L i) (U i) (outLen i) (W i) (fun x hx => by
        obtain ⟨t,ht,hbound,hlen⟩ := htime i x hx
        exact ⟨t,Nat.le_floor hbound,ht,hlen⟩)
  have rate (i : ℕ) (hi : 0 < L i) :
      Real.logb 2 (words i).card / L i ≤ B + (B+h) / L i := by
    have hLi : (0 : ℝ) < L i := by exact_mod_cast hi
    have hU : ((U i : ℕ) : ℝ) ≤ c*((L i : ℝ)+1) := Nat.floor_le (by positivity)
    have htime' : ((U i / s : ℕ) : ℝ) * s ≤ U i := by exact_mod_cast Nat.div_mul_le_self (U i) s
    have hplus : ((U i / s : ℕ) : ℝ) + 1 ≤ c*((L i : ℝ)+1)/s + 1 := by
      linarith only [(le_div_iff₀ hs').2 (htime'.trans hU)]
    have hmul := mul_le_mul_of_nonneg_right hplus hh
    apply (div_le_iff₀ hLi).2
    apply (count i).trans (hmul.trans_eq ?_)
    dsimp [B]
    field_simp
    ring_nf
  have hn (i : ℕ) : 0 ≤ Real.logb 2 (words i).card / L i := by
    apply div_nonneg _ (by positivity)
    rcases Nat.eq_zero_or_pos (words i).card with he | hp
    · simp [he]
    · exact Real.logb_nonneg (by norm_num) (by exact_mod_cast hp)
  change limsup (fun i => Real.logb 2 (words i).card / L i) atTop ≤ B
  apply le_of_forall_pos_le_add
  intro ε hε
  apply limsup_le_of_le (isCoboundedUnder_le_of_le atTop hn)
  have ht := (tendsto_const_div_atTop_nhds_zero_nat (B+h)).comp hL
  filter_upwards [hL.eventually_gt_atTop 0, ht.eventually_lt_const hε] with i hi hsmall
  have he : (B+h)/(L i : ℝ) < ε := hsmall
  exact (rate i hi).trans (by linarith)

end TapeStorageRates.Native
