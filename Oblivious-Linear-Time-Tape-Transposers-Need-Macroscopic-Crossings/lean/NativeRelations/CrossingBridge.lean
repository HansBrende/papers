import NativeRelations.EnvelopeCrux
import LeanMachine.ThresholdRefinement

/-!
# Crossing Steps, Phase-Exit Chains, and Time-Block Self-Collisions

Defines `crossingLowerEtaSteps`, partitions `[0, T)` into `B_time` chronological blocks, bounds
single-family self-collisions (`card_selfCollisions_singleFamily_le`), and develops the non-crossing
path dichotomy (`depPath_nonCrossing_dichotomy_of_isBallPathSeparator_crossingLowerH`) and antitone
phase-exit chain pullback (`crossingCut_nonCrossing_strictAnti`) used by both forms of the bridge.
-/

set_option autoImplicit false

namespace NativeRelations

open Filter Finset Transpose Transpose.Tape BoundedNesting MergeDepth MotionDepthCodes
  BoundedStackDepth TapeStorageRates
open scoped BigOperators

/-! ## §1. Transpose Coordinate Bijection & Stripe-Discrepancy Self-Collision Helpers -/

section TransposeStripeHelpers

/-- Raw input row `i = q / b / d ∈ Fin d` of `q : Fin (d * d * b)`. -/
def bridgeRawRow {d b : ℕ} (q : Fin (d * d * b)) : Fin d :=
  ⟨q.1 / b / d, (Transpose.Tape.Impl.pos_decomp q.2).1⟩

/-- Transposed output row `j = q / b % d ∈ Fin d` of `q : Fin (d * d * b)`. -/
def bridgeOutRow {d b : ℕ} (q : Fin (d * d * b)) : Fin d :=
  ⟨q.1 / b % d, (Transpose.Tape.Impl.pos_decomp q.2).2.1⟩

/-- Entry bit offset `γ = q % b ∈ Fin b` of `q : Fin (d * d * b)`. -/
def bridgeBitIdx {d b : ℕ} (q : Fin (d * d * b)) : Fin b :=
  ⟨q.1 % b, (Transpose.Tape.Impl.pos_decomp q.2).2.2.1⟩

/-- Exact injectivity of `q ↦ ((bridgeRawRow q, bridgeOutRow q), bridgeBitIdx q)` on `Fin (d * d * b)`. -/
theorem bridgeCoord_injective (d b : ℕ) :
    Function.Injective (fun q : Fin (d * d * b) =>
      ((bridgeRawRow q, bridgeOutRow q), bridgeBitIdx q)) := by
  intro q₁ q₂ heq
  have hraw : (bridgeRawRow q₁).1 = (bridgeRawRow q₂).1 :=
    congrArg Fin.val (congrArg Prod.fst (congrArg Prod.fst heq))
  have hout : (bridgeOutRow q₁).1 = (bridgeOutRow q₂).1 :=
    congrArg Fin.val (congrArg Prod.snd (congrArg Prod.fst heq))
  have hbit : (bridgeBitIdx q₁).1 = (bridgeBitIdx q₂).1 :=
    congrArg Fin.val (congrArg Prod.snd heq)
  dsimp [bridgeRawRow, bridgeOutRow, bridgeBitIdx] at hraw hout hbit
  have hdec₁ := (Transpose.Tape.Impl.pos_decomp q₁.2).2.2.2
  have hdec₂ := (Transpose.Tape.Impl.pos_decomp q₂.2).2.2.2
  apply Fin.ext
  rw [hdec₁, hdec₂, hraw, hout, hbit]

/-- Any combinatorial rectangle `{q : bridgeRawRow q ∈ I_set ∧ bridgeOutRow q ∈ J_set}` in
`Fin (d * d * b)` has cardinality at most `I_set.card * J_set.card * b`. -/
theorem card_filter_bridgeRect_le {d b : ℕ} (I_set J_set : Finset (Fin d)) :
    ((univ : Finset (Fin (d * d * b))).filter fun q =>
      bridgeRawRow q ∈ I_set ∧ bridgeOutRow q ∈ J_set).card ≤
      I_set.card * J_set.card * b := by
  let S := (univ : Finset (Fin (d * d * b))).filter fun q =>
    bridgeRawRow q ∈ I_set ∧ bridgeOutRow q ∈ J_set
  let f : Fin (d * d * b) → (Fin d × Fin d) × Fin b :=
    fun q => ((bridgeRawRow q, bridgeOutRow q), bridgeBitIdx q)
  have hsub : S.image f ⊆ (I_set ×ˢ J_set) ×ˢ (univ : Finset (Fin b)) := by
    intro x hx
    obtain ⟨q, hqS, rfl⟩ := mem_image.mp hx
    obtain ⟨_, hI, hJ⟩ := mem_filter.mp hqS
    exact mem_product.mpr ⟨mem_product.mpr ⟨hI, hJ⟩, mem_univ _⟩
  calc S.card
      = (S.image f).card := (card_image_of_injective S (bridgeCoord_injective d b)).symm
    _ ≤ ((I_set ×ˢ J_set) ×ˢ (univ : Finset (Fin b))).card := card_le_card hsub
    _ = I_set.card * J_set.card * b := by simp [card_product, mul_assoc]

theorem card_filter_bridgeRawRow_le {d b : ℕ} (I_set : Finset (Fin d)) :
    ((univ : Finset (Fin (d * d * b))).filter fun q => bridgeRawRow q ∈ I_set).card ≤
      I_set.card * (d * b) := by
  have h := card_filter_bridgeRect_le (b := b) I_set (univ : Finset (Fin d))
  simpa [mul_assoc] using h

theorem card_filter_bridgeOutRow_le {d b : ℕ} (J_set : Finset (Fin d)) :
    ((univ : Finset (Fin (d * d * b))).filter fun q => bridgeOutRow q ∈ J_set).card ≤
      J_set.card * (d * b) := by
  have h := card_filter_bridgeRect_le (b := b) (univ : Finset (Fin d)) J_set
  have heq : d * J_set.card * b = J_set.card * (d * b) := by ring
  simpa [heq] using h

theorem bridgeRawRow_bounds {d b : ℕ} (q : Fin (d * d * b)) :
    (bridgeRawRow q).1 * (d * b) ≤ q.1 ∧ q.1 < ((bridgeRawRow q).1 + 1) * (d * b) := by
  have hc := (coord_row_bounds q).1
  refine ⟨?_, ?_⟩
  · by_contra hlt
    push Not at hlt
    have := (hc (bridgeRawRow q).1).mpr hlt
    dsimp [bridgeRawRow] at this
    omega
  · exact (hc ((bridgeRawRow q).1 + 1)).mp (by dsimp [bridgeRawRow]; omega)

theorem bridgeOutRow_bounds {d b : ℕ} (q : Fin (d * d * b)) :
    (bridgeOutRow q).1 * (d * b) ≤ (tposOf d b q).1 ∧
      (tposOf d b q).1 ≤ ((bridgeOutRow q).1 + 1) * (d * b) - 1 :=
  (coord_row_bounds q).2

/-- Output root timestamp `u₀(q) = appendTime τ₀ T (tposOf d b q).1` is injective on `Fin (d * d * b)`
whenever `(appendList τ₀ T).length = d * d * b`. -/
theorem appendTime_tposOf_injective {k T d b : ℕ} (τ₀ : Trace k)
    (hlen : (appendList τ₀ T).length = d * d * b) :
    Function.Injective (fun q : Fin (d * d * b) => appendTime τ₀ T (tposOf d b q).1) := by
  intro q₁ q₂ heq
  have h1 : (tposOf d b q₁).1 < (appendList τ₀ T).length := by rw [hlen]; exact (tposOf d b q₁).2
  have h2 : (tposOf d b q₂).1 < (appendList τ₀ T).length := by rw [hlen]; exact (tposOf d b q₂).2
  have htp : tposOf d b q₁ = tposOf d b q₂ :=
    Fin.ext ((appendTime_strictMonoOn τ₀ T).injOn h1 h2 heq)
  calc q₁ = tposOf d b (tposOf d b q₁) := (tposOf_tposOf d b q₁).symm
    _ = tposOf d b (tposOf d b q₂) := by rw [htp]
    _ = q₂ := tposOf_tposOf d b q₂

end TransposeStripeHelpers

/-! ## §2. Minimal-Clause Arbitrary-Trace Time-Pullback `MAIS` Theorem (Theorem 5.1 (time pullback)) -/

section MinimalTimePullbackMAIS

/-- Lower endpoint `τ_β = β * ⌊T / B_time⌋` of chronological block `β : Fin B_time`. -/
def timeBlockLo (T B_time : ℕ) (β : Fin B_time) : ℕ :=
  β.1 * (T / B_time)

/-- Upper endpoint `τ_{β+1}` (`(β + 1) * ⌊T / B_time⌋` for `β + 1 < B_time`, and `T` at the last block). -/
def timeBlockHi (T B_time : ℕ) (β : Fin B_time) : ℕ :=
  if β.1 + 1 < B_time then (β.1 + 1) * (T / B_time) else T

/-- Contiguous half-open chronological block `T_β = [timeBlockLo, timeBlockHi)`. -/
def timeBlock (T B_time : ℕ) (β : Fin B_time) : Finset ℕ :=
  Ico (timeBlockLo T B_time β) (timeBlockHi T B_time β)

/-- Boundary sequence `timeBlockBound T B_time s` (`0 ≤ s ≤ B_time`) with `0` at `s = 0` and `T` at `s ≥ B_time`. -/
def timeBlockBound (T B_time s : ℕ) : ℕ :=
  if s < B_time then s * (T / B_time) else T

theorem timeBlockBound_mono (T B_time : ℕ) {s₁ s₂ : ℕ} (hs : s₁ ≤ s₂) :
    timeBlockBound T B_time s₁ ≤ timeBlockBound T B_time s₂ := by
  unfold timeBlockBound
  split_ifs with h₁ h₂ h₂
  · exact Nat.mul_le_mul_right _ hs
  · calc s₁ * (T / B_time) ≤ B_time * (T / B_time) := Nat.mul_le_mul_right _ (le_of_lt h₁)
      _ ≤ T := Nat.mul_div_le T B_time
  · omega
  · exact le_rfl

theorem timeBlock_eq_Ico_bound (T B_time : ℕ) (β : Fin B_time) :
    timeBlockLo T B_time β = timeBlockBound T B_time β.1 ∧
    timeBlockHi T B_time β = timeBlockBound T B_time (β.1 + 1) := by
  refine ⟨?_, rfl⟩
  unfold timeBlockLo timeBlockBound
  simp [β.2]

theorem timeBlock_len_bounds {T B_time : ℕ} (hB : 1 ≤ B_time) (β : Fin B_time) :
    T / B_time ≤ timeBlockHi T B_time β - timeBlockLo T B_time β ∧
    timeBlockHi T B_time β - timeBlockLo T B_time β < T / B_time + B_time := by
  unfold timeBlockLo timeBlockHi
  split_ifs with hlt
  · have hsub : (β.1 + 1) * (T / B_time) - β.1 * (T / B_time) = T / B_time := by
      rw [Nat.add_mul, Nat.one_mul, Nat.add_sub_cancel_left]
    rw [hsub]
    exact ⟨le_rfl, by omega⟩
  · have hlast : β.1 + 1 = B_time := by omega
    have hdiv_mod : B_time * (T / B_time) + T % B_time = T := Nat.div_add_mod T B_time
    have hmod_lt : T % B_time < B_time := Nat.mod_lt T (by omega)
    have h1 : β.1 * (T / B_time) + (T / B_time) = B_time * (T / B_time) := by
      calc β.1 * (T / B_time) + (T / B_time) = (β.1 + 1) * (T / B_time) := by ring
        _ = B_time * (T / B_time) := by rw [hlast]
    have hsub2 : T - β.1 * (T / B_time) = T / B_time + T % B_time := by
      conv_lhs => arg 1; rw [← hdiv_mod, ← h1]
      rw [add_assoc, Nat.add_sub_cancel_left]
    rw [hsub2]
    exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hmod_lt _⟩

theorem exists_mem_timeBlock {T B_time t : ℕ} (hB : 1 ≤ B_time) (hBT : B_time ≤ T) (ht : t < T) :
    ∃ β : Fin B_time, t ∈ timeBlock T B_time β := by
  let Q := T / B_time
  have hQ_pos : 0 < Q := Nat.div_pos hBT hB
  let idx := min (B_time - 1) (t / Q)
  have hidx_def : idx = min (B_time - 1) (t / Q) := rfl
  let β : Fin B_time := ⟨idx, by omega⟩
  refine ⟨β, mem_Ico.mpr ⟨?_, ?_⟩⟩
  · unfold timeBlockLo
    change idx * Q ≤ t
    have h1 : idx * Q ≤ (t / Q) * Q := Nat.mul_le_mul_right Q (Nat.min_le_right _ _)
    have h2 : (t / Q) * Q ≤ t := Nat.div_mul_le_self t Q
    exact h1.trans h2
  · unfold timeBlockHi
    dsimp only [β]
    split_ifs with hlt
    · have hidx_eq : idx = t / Q := by omega
      have hdiv_mod := Nat.div_add_mod t Q
      have hmod_lt := Nat.mod_lt t hQ_pos
      change t < (idx + 1) * Q
      rw [hidx_eq]
      nlinarith
    · exact ht

/-- Any contiguous interval `[a, b_end)` of length strictly below `T / B_time` intersects at most
**two** chronological blocks `timeBlock T B_time β`. -/
theorem card_timeBlocks_inter_ico_le_two {T B_time a b_end : ℕ}
    (hlen : b_end - a < T / B_time) :
    ((univ : Finset (Fin B_time)).filter fun β =>
      (timeBlock T B_time β ∩ Ico a b_end).Nonempty).card ≤ 2 := by
  set S_hit := (univ : Finset (Fin B_time)).filter fun β =>
    (timeBlock T B_time β ∩ Ico a b_end).Nonempty
  rcases S_hit.eq_empty_or_nonempty with hemp | hne
  · rw [hemp, card_empty]; exact Nat.zero_le _
  · let β₀ := S_hit.min' hne
    let β₁ := S_hit.max' hne
    have hβ₀_mem : β₀ ∈ S_hit := S_hit.min'_mem hne
    have hβ₁_mem : β₁ ∈ S_hit := S_hit.max'_mem hne
    obtain ⟨t₀, ht₀⟩ := (mem_filter.mp hβ₀_mem).2
    obtain ⟨t₁, ht₁⟩ := (mem_filter.mp hβ₁_mem).2
    obtain ⟨ht₀_blk, ht₀_ab⟩ := mem_inter.mp ht₀
    obtain ⟨ht₁_blk, ht₁_ab⟩ := mem_inter.mp ht₁
    obtain ⟨_, ht₀_hi⟩ := mem_Ico.mp ht₀_blk
    obtain ⟨hat₀, _⟩ := mem_Ico.mp ht₀_ab
    obtain ⟨ht₁_lo, _⟩ := mem_Ico.mp ht₁_blk
    obtain ⟨_, ht₁b⟩ := mem_Ico.mp ht₁_ab
    have hgap : β₁.1 ≤ β₀.1 + 1 := by
      by_contra hgt
      push Not at hgt
      have hβ₀_lt : β₀.1 + 1 < B_time := by have := β₁.2; omega
      have hhi₀ : timeBlockHi T B_time β₀ = (β₀.1 + 1) * (T / B_time) := by
        unfold timeBlockHi; simp [hβ₀_lt]
      have hlo₁ : (β₀.1 + 2) * (T / B_time) ≤ timeBlockLo T B_time β₁ := by
        unfold timeBlockLo; exact Nat.mul_le_mul_right (T / B_time) hgt
      have hmul2 : (β₀.1 + 2) * (T / B_time) = (β₀.1 + 1) * (T / B_time) + (T / B_time) := by ring
      omega
    have hsub : S_hit.image Fin.val ⊆ Icc β₀.1 (β₀.1 + 1) := by
      intro v hv
      obtain ⟨β, hβS, rfl⟩ := mem_image.mp hv
      have hmin_le : β₀.1 ≤ β.1 := S_hit.min'_le β hβS
      have hmax_le : β.1 ≤ β₁.1 := S_hit.le_max' β hβS
      exact mem_Icc.mpr ⟨hmin_le, hmax_le.trans hgap⟩
    calc S_hit.card
        = (S_hit.image Fin.val).card := (card_image_of_injective S_hit Fin.val_injective).symm
      _ ≤ (Icc β₀.1 (β₀.1 + 1)).card := card_le_card hsub
      _ = 2 := by rw [Nat.card_Icc]; omega

/-- Elementary natural-number division bound `(A + K) / W ≤ A / W + K` for `1 ≤ W`. -/
private lemma add_div_le_div_add {A K W : ℕ} (hW : 1 ≤ W) :
    (A + K) / W ≤ A / W + K := by
  have h1 : A < (A / W + 1) * W := by
    have hd := Nat.div_add_mod A W
    have hm := Nat.mod_lt A hW
    nlinarith
  have h2 : K ≤ K * W := Nat.le_mul_of_pos_right K hW
  have h3 : A + K < (A / W + K + 1) * W := by nlinarith
  have h4 : (A + K) / W < A / W + K + 1 := Nat.div_lt_of_lt_mul (by nlinarith)
  omega

/-- Raw input rows visited during `[lo, hi)` on a unit-speed input walk `x_in` number at most
`(hi - lo) / W + 2` (`W ≥ 1`). -/
theorem card_rawRows_visited_in_interval_le {x_in : ℕ → ℤ} (hx_in : IsWalk x_in)
    {d W lo hi : ℕ} (hW : 1 ≤ W) :
    ((univ : Finset (Fin d)).filter fun i =>
      ∃ t ∈ Ico lo hi, ((i.1 * W : ℕ) : ℤ) ≤ x_in t ∧ x_in t < (((i.1 + 1) * W : ℕ) : ℤ)).card ≤
      (hi - lo) / W + 2 := by
  set I_raw := (univ : Finset (Fin d)).filter fun i =>
    ∃ t ∈ Ico lo hi, ((i.1 * W : ℕ) : ℤ) ≤ x_in t ∧ x_in t < (((i.1 + 1) * W : ℕ) : ℤ)
  rcases I_raw.eq_empty_or_nonempty with hemp | hne
  · rw [hemp, card_empty]; exact Nat.zero_le _
  · set i₀ := I_raw.min' hne
    set i₁ := I_raw.max' hne
    obtain ⟨t₀, ht₀_ico, hxt₀_lo, hxt₀_hi⟩ := (mem_filter.mp (I_raw.min'_mem hne)).2
    obtain ⟨t₁, ht₁_ico, hxt₁_lo, _⟩ := (mem_filter.mp (I_raw.max'_mem hne)).2
    obtain ⟨hlo₀, hhi₀⟩ := mem_Ico.mp ht₀_ico
    obtain ⟨hlo₁, hhi₁⟩ := mem_Ico.mp ht₁_ico
    have hdiff_x : x_in t₁ - x_in t₀ ≤ ((hi - lo - 1 : ℕ) : ℤ) := by
      rcases le_total t₀ t₁ with hle | hle
      · have hlip := (hx_in.lip hle).1
        have hdt : t₁ - t₀ ≤ hi - lo - 1 := by omega
        exact hlip.trans (Nat.cast_le.mpr hdt)
      · have hlip := (hx_in.lip hle).2
        have hdt : t₀ - t₁ ≤ hi - lo - 1 := by omega
        have hcast : ((t₀ - t₁ : ℕ) : ℤ) ≤ ((hi - lo - 1 : ℕ) : ℤ) := Nat.cast_le.mpr hdt
        linarith
    have hWz : (1 : ℤ) ≤ (W : ℤ) := by exact_mod_cast hW
    have hgap_z : (((i₁.1 : ℤ) - (i₀.1 : ℤ) - 1) * (W : ℤ)) + 1 ≤ x_in t₁ - x_in t₀ := by
      push_cast at hxt₀_hi hxt₁_lo
      nlinarith
    have hspan_nat : (i₁.1 - (i₀.1 + 1)) * W ≤ hi - lo - 1 := by
      rcases le_or_gt i₁.1 (i₀.1 + 1) with hle | hgt
      · have : i₁.1 - (i₀.1 + 1) = 0 := by omega
        rw [this, zero_mul]; omega
      · have hz : (((i₁.1 - (i₀.1 + 1)) * W : ℕ) : ℤ) ≤ ((hi - lo - 1 : ℕ) : ℤ) := by
          have hsub_eq : ((i₁.1 - (i₀.1 + 1) : ℕ) : ℤ) = (i₁.1 : ℤ) - (i₀.1 : ℤ) - 1 := by omega
          push_cast [hsub_eq]
          linarith
        exact Nat.cast_le.mp hz
    have hdiv_span : i₁.1 - (i₀.1 + 1) ≤ (hi - lo) / W := by
      have hle1 : (i₁.1 - (i₀.1 + 1)) * W ≤ hi - lo := hspan_nat.trans (Nat.sub_le _ _)
      exact (Nat.le_div_iff_mul_le hW).mpr hle1
    have hsub : I_raw.image Fin.val ⊆ Icc i₀.1 i₁.1 := by
      intro v hv
      obtain ⟨i, hiS, rfl⟩ := mem_image.mp hv
      have hmin_le : i₀.1 ≤ i.1 := I_raw.min'_le i hiS
      have hmax_le : i.1 ≤ i₁.1 := I_raw.le_max' i hiS
      exact mem_Icc.mpr ⟨hmin_le, hmax_le⟩
    have hi₀₁ : i₀.1 ≤ i₁.1 := I_raw.min'_le i₁ (I_raw.max'_mem hne)
    calc I_raw.card
        = (I_raw.image Fin.val).card := (card_image_of_injective I_raw Fin.val_injective).symm
      _ ≤ (Icc i₀.1 i₁.1).card := card_le_card hsub
      _ = i₁.1 + 1 - i₀.1 := by rw [Nat.card_Icc]
      _ ≤ (hi - lo) / W + 2 := by omega

/-- **Single-Family Transpose Stripe-Discrepancy Lemma (`Step 3 of Theorem 5.1 (time pullback)`):**
For any monotone timestamp sequence `ξ 0 ≤ ξ 1 ≤ ... ≤ ξ B_time` and injection `π : Fin B_time → Fin B_time`
defining pairwise-disjoint root intervals `I_β = [ξ (π β), ξ (π β + 1))`, the number of `q : Fin (d * d * b)`
such that `∃ β, u₀(q) ∈ I_β ∧ (∃ t ∈ timeBlock T B_time β, τ₀.input t = q.1)` is at most
`T / B_time + (2 * B_time + 2) * (d * b)`. -/
theorem card_selfCollisions_singleFamily_le {k T d b B_time : ℕ} (τ₀ : Trace k)
    (hd : 1 ≤ d) (hb : 1 ≤ b) (hB : 1 ≤ B_time)
    (hlen : (appendList τ₀ T).length = d * d * b)
    (ξ : ℕ → ℕ) (hξ_mono : ∀ s₁ s₂ : ℕ, s₁ ≤ s₂ → s₂ ≤ B_time → ξ s₁ ≤ ξ s₂)
    (π_perm : Fin B_time → Fin B_time) (hπ_inj : Function.Injective π_perm) :
    ((univ : Finset (Fin (d * d * b))).filter fun q =>
      ∃ β : Fin B_time,
        appendTime τ₀ T (tposOf d b q).1 ∈ Ico (ξ (π_perm β).1) (ξ ((π_perm β).1 + 1)) ∧
        ∃ t ∈ timeBlock T B_time β, τ₀.input t = (q.1 : ℤ)).card ≤
      T / B_time + (2 * B_time + 2) * (d * b) := by
  set W := d * b
  set L := d * d * b
  have hW : 1 ≤ W := Nat.mul_pos hd hb
  have hx_in : IsWalk τ₀.input := τ₀.abs_input_succ_sub_le
  let loOut : Fin d → ℕ := fun j => j.1 * W
  let hiOut : Fin d → ℕ := fun j => (j.1 + 1) * W - 1
  have hlo_hi_lt : ∀ j : Fin d, loOut j ≤ hiOut j ∧ hiOut j < L := by
    intro j
    have h1 : j.1 * W + 1 ≤ (j.1 + 1) * W := by rw [Nat.add_mul, Nat.one_mul]; omega
    have h2 : (j.1 + 1) * W ≤ L := by
      show (j.1 + 1) * (d * b) ≤ d * d * b
      calc (j.1 + 1) * (d * b) ≤ d * (d * b) := Nat.mul_le_mul_right _ (by omega)
        _ = d * d * b := by ring
    exact ⟨by dsimp [loOut, hiOut]; omega, by dsimp [hiOut]; omega⟩
  have happ_mono : ∀ {x y : ℕ}, x ≤ y → y < L → appendTime τ₀ T x ≤ appendTime τ₀ T y := by
    intro x y hxy hyL
    rcases eq_or_lt_of_le hxy with rfl | hlt
    · exact le_rfl
    · exact ((appendTime_strictMonoOn τ₀ T)
        (Set.mem_Iio.mpr (by rw [hlen]; omega))
        (Set.mem_Iio.mpr (by rw [hlen]; exact hyL)) hlt).le
  let SplitsOutRow : ℕ → Fin d → Prop := fun θ j =>
    appendTime τ₀ T (loOut j) < θ ∧ θ ≤ appendTime τ₀ T (hiOut j)
  have hSplits_le_one : ∀ θ : ℕ, ((univ : Finset (Fin d)).filter (SplitsOutRow θ)).card ≤ 1 := by
    intro θ
    refine card_le_one.mpr fun j₁ hj₁ j₂ hj₂ => ?_
    have hs1 := (mem_filter.mp hj₁).2
    have hs2 := (mem_filter.mp hj₂).2
    by_contra hne
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
    · have hlt_idx : hiOut j₁ < loOut j₂ := by
        dsimp [loOut, hiOut]
        have h1 : (j₁.1 + 1) * W ≤ j₂.1 * W := Nat.mul_le_mul_right W (by omega)
        have h2 : 1 ≤ (j₁.1 + 1) * W := Nat.mul_pos (by omega) hW
        omega
      have hlt_app : appendTime τ₀ T (hiOut j₁) < appendTime τ₀ T (loOut j₂) :=
        (appendTime_strictMonoOn τ₀ T) (by rw [hlen]; exact (hlo_hi_lt j₁).2)
          (by rw [hlen]; exact (hlo_hi_lt j₂).1.trans_lt (hlo_hi_lt j₂).2) hlt_idx
      omega
    · have hlt_idx : hiOut j₂ < loOut j₁ := by
        dsimp [loOut, hiOut]
        have h1 : (j₂.1 + 1) * W ≤ j₁.1 * W := Nat.mul_le_mul_right W (by omega)
        have h2 : 1 ≤ (j₂.1 + 1) * W := Nat.mul_pos (by omega) hW
        omega
      have hlt_app : appendTime τ₀ T (hiOut j₂) < appendTime τ₀ T (loOut j₁) :=
        (appendTime_strictMonoOn τ₀ T) (by rw [hlen]; exact (hlo_hi_lt j₂).2)
          (by rw [hlen]; exact (hlo_hi_lt j₁).1.trans_lt (hlo_hi_lt j₁).2) hlt_idx
      omega
  let J_split : Finset (Fin d) :=
    (range (B_time + 1)).biUnion fun s => (univ : Finset (Fin d)).filter (SplitsOutRow (ξ s))
  have hJ_split_card : J_split.card ≤ B_time + 1 := by
    calc J_split.card
        ≤ ∑ s ∈ range (B_time + 1), ((univ : Finset (Fin d)).filter (SplitsOutRow (ξ s))).card :=
          card_biUnion_le
      _ ≤ ∑ _s ∈ range (B_time + 1), 1 := sum_le_sum fun s _ => hSplits_le_one (ξ s)
      _ = B_time + 1 := by simp
  let J_unsplit : Fin B_time → Finset (Fin d) := fun β =>
    (univ \ J_split).filter fun j =>
      ∃ q : Fin L, bridgeOutRow q = j ∧
        appendTime τ₀ T (tposOf d b q).1 ∈ Ico (ξ (π_perm β).1) (ξ ((π_perm β).1 + 1))
  have hJ_disj : ((univ : Finset (Fin B_time)) : Set (Fin B_time)).PairwiseDisjoint J_unsplit := by
    intro β₁ _ β₂ _ hne
    refine disjoint_left.mpr fun j hj₁ hj₂ => ?_
    obtain ⟨hj_notS, q₁, hq₁_row, hq₁_ico⟩ := mem_filter.mp hj₁
    obtain ⟨_, q₂, hq₂_row, hq₂_ico⟩ := mem_filter.mp hj₂
    have hj_notSplit : j ∉ J_split := (mem_sdiff.mp hj_notS).2
    obtain ⟨hlo₁, hhi₁⟩ := mem_Ico.mp hq₁_ico
    obtain ⟨hlo₂, hhi₂⟩ := mem_Ico.mp hq₂_ico
    have hb₁ := bridgeOutRow_bounds q₁
    have hb₂ := bridgeOutRow_bounds q₂
    rw [hq₁_row] at hb₁
    rw [hq₂_row] at hb₂
    have hq₁_lo : appendTime τ₀ T (loOut j) ≤ appendTime τ₀ T (tposOf d b q₁).1 :=
      happ_mono hb₁.1 (tposOf d b q₁).2
    have hq₁_hi : appendTime τ₀ T (tposOf d b q₁).1 ≤ appendTime τ₀ T (hiOut j) :=
      happ_mono hb₁.2 (hlo_hi_lt j).2
    have hq₂_lo : appendTime τ₀ T (loOut j) ≤ appendTime τ₀ T (tposOf d b q₂).1 :=
      happ_mono hb₂.1 (tposOf d b q₂).2
    have hq₂_hi : appendTime τ₀ T (tposOf d b q₂).1 ≤ appendTime τ₀ T (hiOut j) :=
      happ_mono hb₂.2 (hlo_hi_lt j).2
    have hs_ne : (π_perm β₁).1 ≠ (π_perm β₂).1 := fun h => hne (hπ_inj (Fin.ext h))
    rcases lt_or_gt_of_ne hs_ne with hlt | hgt
    · have hmid : ξ ((π_perm β₁).1 + 1) ≤ ξ (π_perm β₂).1 :=
        hξ_mono _ _ (by omega) (le_of_lt (π_perm β₂).2)
      have hsp : SplitsOutRow (ξ ((π_perm β₁).1 + 1)) j := ⟨by omega, by omega⟩
      exact hj_notSplit (mem_biUnion.mpr ⟨(π_perm β₁).1 + 1,
        mem_range.mpr (by have := (π_perm β₁).2; omega), mem_filter.mpr ⟨mem_univ j, hsp⟩⟩)
    · have hmid : ξ ((π_perm β₂).1 + 1) ≤ ξ (π_perm β₁).1 :=
        hξ_mono _ _ (by omega) (le_of_lt (π_perm β₁).2)
      have hsp : SplitsOutRow (ξ ((π_perm β₂).1 + 1)) j := ⟨by omega, by omega⟩
      exact hj_notSplit (mem_biUnion.mpr ⟨(π_perm β₂).1 + 1,
        mem_range.mpr (by have := (π_perm β₂).2; omega), mem_filter.mpr ⟨mem_univ j, hsp⟩⟩)
  have hsum_Junsplit : (∑ β : Fin B_time, (J_unsplit β).card) ≤ d := by
    calc (∑ β : Fin B_time, (J_unsplit β).card)
        = ((univ : Finset (Fin B_time)).biUnion J_unsplit).card := (card_biUnion hJ_disj).symm
      _ ≤ (univ : Finset (Fin d)).card := card_le_card (subset_univ _)
      _ = d := by simp
  let I_raw : Fin B_time → Finset (Fin d) := fun β =>
    (univ : Finset (Fin d)).filter fun i =>
      ∃ t ∈ timeBlock T B_time β,
        ((i.1 * W : ℕ) : ℤ) ≤ τ₀.input t ∧ τ₀.input t < (((i.1 + 1) * W : ℕ) : ℤ)
  have hI_raw_card : ∀ β : Fin B_time, (I_raw β).card ≤ T / (B_time * W) + B_time + 1 := by
    intro β
    have hc1 := card_rawRows_visited_in_interval_le hx_in (d := d)
      (lo := timeBlockLo T B_time β) (hi := timeBlockHi T B_time β) hW
    have hlen_hi := (timeBlock_len_bounds (T := T) hB β).2
    have hle_len : timeBlockHi T B_time β - timeBlockLo T B_time β ≤ T / B_time + (B_time - 1) := by
      omega
    have hdiv1 : (timeBlockHi T B_time β - timeBlockLo T B_time β) / W ≤
        (T / B_time + (B_time - 1)) / W := Nat.div_le_div_right hle_len
    have hdiv2 : (T / B_time + (B_time - 1)) / W ≤ T / B_time / W + (B_time - 1) :=
      add_div_le_div_add hW
    rw [Nat.div_div_eq_div_mul] at hdiv2
    calc (I_raw β).card
        ≤ (timeBlockHi T B_time β - timeBlockLo T B_time β) / W + 2 := hc1
      _ ≤ (T / (B_time * W) + (B_time - 1)) + 2 := Nat.add_le_add_right (hdiv1.trans hdiv2) 2
      _ = T / (B_time * W) + B_time + 1 := by omega
  set Coll := (univ : Finset (Fin L)).filter fun q =>
    ∃ β : Fin B_time,
      appendTime τ₀ T (tposOf d b q).1 ∈ Ico (ξ (π_perm β).1) (ξ ((π_perm β).1 + 1)) ∧
      ∃ t ∈ timeBlock T B_time β, τ₀.input t = (q.1 : ℤ)
  let SplitSet := (univ : Finset (Fin L)).filter fun q => bridgeOutRow q ∈ J_split
  let RectOf : Fin B_time → Finset (Fin L) := fun β =>
    (univ : Finset (Fin L)).filter fun q => bridgeRawRow q ∈ I_raw β ∧ bridgeOutRow q ∈ J_unsplit β
  have hColl_sub : Coll ⊆ SplitSet ∪ (univ : Finset (Fin B_time)).biUnion RectOf := by
    intro q hq
    obtain ⟨_, β, hq_ico, t, ht_blk, hxt⟩ := mem_filter.mp hq
    by_cases hjS : bridgeOutRow q ∈ J_split
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ q, hjS⟩)
    · refine mem_union_right _ (mem_biUnion.mpr ⟨β, mem_univ β, mem_filter.mpr ⟨mem_univ q, ?_, ?_⟩⟩)
      · refine mem_filter.mpr ⟨mem_univ _, t, ht_blk, ?_⟩
        have hqb := bridgeRawRow_bounds q
        rw [hxt]
        exact ⟨Nat.cast_le.mpr hqb.1, Nat.cast_lt.mpr hqb.2⟩
      · exact mem_filter.mpr ⟨mem_sdiff.mpr ⟨mem_univ _, hjS⟩, q, rfl, hq_ico⟩
  have hSplit_card : SplitSet.card ≤ (B_time + 1) * W :=
    (card_filter_bridgeOutRow_le J_split).trans (Nat.mul_le_mul_right W hJ_split_card)
  have hUnsplit_card : ((univ : Finset (Fin B_time)).biUnion RectOf).card ≤
      T / B_time + (B_time + 1) * W := by
    set K_i := T / (B_time * W) + B_time + 1
    have hsum_rect : ∑ β : Fin B_time, (RectOf β).card ≤ K_i * d * b := by
      calc ∑ β : Fin B_time, (RectOf β).card
          ≤ ∑ β : Fin B_time, ((I_raw β).card * (J_unsplit β).card * b) :=
            sum_le_sum fun β _ => card_filter_bridgeRect_le (I_raw β) (J_unsplit β)
        _ ≤ ∑ β : Fin B_time, (K_i * (J_unsplit β).card * b) :=
            sum_le_sum fun β _ => Nat.mul_le_mul_right b
              (Nat.mul_le_mul_right _ (hI_raw_card β))
        _ = K_i * b * (∑ β : Fin B_time, (J_unsplit β).card) := by
            rw [mul_sum]
            refine sum_congr rfl fun β _ => by ring
        _ ≤ K_i * b * d := Nat.mul_le_mul_left _ hsum_Junsplit
        _ = K_i * d * b := by ring
    have hK_expand : K_i * d * b ≤ T / B_time + (B_time + 1) * W := by
      dsimp [K_i, W]
      have h1 : (T / (B_time * (d * b)) + B_time + 1) * d * b =
          (T / B_time / (d * b)) * (d * b) + (B_time + 1) * (d * b) := by
        rw [← Nat.div_div_eq_div_mul]
        ring
      rw [h1]
      have h2 : (T / B_time / (d * b)) * (d * b) ≤ T / B_time :=
        Nat.div_mul_le_self (T / B_time) (d * b)
      omega
    exact card_biUnion_le.trans (hsum_rect.trans hK_expand)
  calc Coll.card
      ≤ (SplitSet ∪ (univ : Finset (Fin B_time)).biUnion RectOf).card := card_le_card hColl_sub
    _ ≤ SplitSet.card + ((univ : Finset (Fin B_time)).biUnion RectOf).card := card_union_le _ _
    _ ≤ (B_time + 1) * W + (T / B_time + (B_time + 1) * W) :=
        Nat.add_le_add hSplit_card hUnsplit_card
    _ = T / B_time + (2 * B_time + 2) * W := by ring

/-- **Natural-Number Core of Minimal Time-Pullback `MAIS` (Theorem 5.1 (time pullback) Core):**
Given any finite index type `ι` (`Fintype.card ι ≤ m₀`) of pairwise-disjoint half-open root intervals
covering `u₀(q)` whenever a `B`-free `D`-path from `q ∈ V₀ \ Z_bad` reads `p ∈ V₀` in `timeBlock T B_time β`,
`ballAvoidSystem τ₀ T D B d b` admits an acyclic subset `U ⊆ V₀` with exact combinatorial lower bound! -/
theorem exists_isAcyclicIn_of_timePullback_core {ι : Type*} [Fintype ι] [DecidableEq ι]
    {k T d b D m₀ K_row B_time : ℕ} (τ₀ : Trace k)
    (hd : 1 ≤ d) (hb : 1 ≤ b) (hK_row : 1 ≤ K_row) (hB_time : 1 ≤ B_time)
    (hd_big : K_row * B_time ≤ d) (hι : Fintype.card ι ≤ m₀)
    (hlen : (appendList τ₀ T).length = d * d * b)
    (V₀ Z_bad : Finset (Fin (d * d * b))) (B : Finset ℕ)
    (ξ : ι → ℕ → ℕ)
    (hξ_mono : ∀ ν : ι, ∀ s₁ s₂ : ℕ, s₁ ≤ s₂ → s₂ ≤ B_time → ξ ν s₁ ≤ ξ ν s₂)
    (π_perm : ι → Fin B_time → Fin B_time)
    (hπ_inj : ∀ ν : ι, Function.Injective (π_perm ν))
    (hpull : ∀ q ∈ V₀ \ Z_bad, ∀ p ∈ V₀, ∀ ρ : List ℕ,
      ρ.length ≤ D →
      IsDepPath τ₀.work T (appendTime τ₀ T (tposOf d b q).1 :: ρ) →
      LinNet.GFree B (appendTime τ₀ T (tposOf d b q).1 :: ρ) →
      τ₀.input ((appendTime τ₀ T (tposOf d b q).1 :: ρ).getLastD
        (appendTime τ₀ T (tposOf d b q).1)) = (p.1 : ℤ) →
      ∀ β : Fin B_time,
        (appendTime τ₀ T (tposOf d b q).1 :: ρ).getLastD
          (appendTime τ₀ T (tposOf d b q).1) ∈ timeBlock T B_time β →
        ∃ ν : ι, appendTime τ₀ T (tposOf d b q).1 ∈
          Ico (ξ ν (π_perm ν β).1) (ξ ν ((π_perm ν β).1 + 1))) :
    ∃ (U : Finset (Fin (d * d * b))) (N_surv : ℕ),
      U ⊆ V₀ ∧
      HalfRate.IsAcyclicIn (ballAvoidSystem τ₀ T D B d b) U ∧
      V₀.card ≤ N_surv + Z_bad.card + 3 * T / K_row +
        m₀ * (T / B_time) + m₀ * (2 * B_time + 2) * (d * b) ∧
      (N_surv : ℝ) / (Nat.choose (m₀ + 2 * K_row) m₀ : ℝ) ≤ (U.card : ℝ) := by
  classical
  let W := d * b
  let L := d * d * b
  have hW : 1 ≤ W := Nat.mul_pos hd hb
  have hL_pos : 1 ≤ L := Nat.mul_pos (Nat.mul_pos hd hd) hb
  have hL_le_T : L ≤ T := by
    have hlast_lt : L - 1 < (appendList τ₀ T).length := by rw [hlen]; omega
    have hot_lt : appendTime τ₀ T (L - 1) < T := appendTime_lt τ₀ T hlast_lt
    have hid_le : L - 1 ≤ appendTime τ₀ T (L - 1) := by
      clear hot_lt hlast_lt
      suffices ∀ r < L, r ≤ appendTime τ₀ T r from this (L - 1) (by omega)
      intro r hr
      induction r with
      | zero => omega
      | succ r ih =>
        have hrL : r < (appendList τ₀ T).length := by rw [hlen]; omega
        have hrsL : r + 1 < (appendList τ₀ T).length := by rw [hlen]; exact hr
        have hlt := (appendTime_strictMonoOn τ₀ T) hrL hrsL (Nat.lt_succ_self r)
        have := ih (by omega)
        omega
    omega
  have hKW_le_Q : K_row * W ≤ T / B_time := by
    refine (Nat.le_div_iff_mul_le hB_time).mpr ?_
    calc (K_row * W) * B_time
        = (K_row * B_time) * W := by ring
      _ ≤ d * W := Nat.mul_le_mul_right W hd_big
      _ = L := by dsimp [L, W]; ring
      _ ≤ T := hL_le_T
  have hBT : B_time ≤ T := by
    calc B_time = 1 * B_time := (Nat.one_mul _).symm
      _ ≤ (K_row * W) * B_time := Nat.mul_le_mul_right B_time (Nat.mul_pos hK_row hW)
      _ ≤ d * W := by
          calc (K_row * W) * B_time = (K_row * B_time) * W := by ring
            _ ≤ d * W := Nat.mul_le_mul_right W hd_big
      _ = L := by dsimp [L, W]; ring
      _ ≤ T := hL_le_T
  -- Define `A_blk` and `E_blk`.
  let A_blk : Fin L → Finset (Fin B_time) := fun q =>
    (univ : Finset (Fin B_time)).filter fun β =>
      ∃ ν : ι, appendTime τ₀ T (tposOf d b q).1 ∈
        Ico (ξ ν (π_perm ν β).1) (ξ ν ((π_perm ν β).1 + 1))
  let E_blk : Fin L → Finset (Fin B_time) := fun q =>
    (univ : Finset (Fin B_time)).filter fun β =>
      ∃ t ∈ timeBlock T B_time β, τ₀.input t = (q.1 : ℤ)
  -- `|A_blk q| ≤ m₀` for every `q`.
  have hA_card : ∀ q : Fin L, (A_blk q).card ≤ m₀ := by
    intro q
    let A_of : ι → Finset (Fin B_time) := fun ν =>
      (univ : Finset (Fin B_time)).filter fun β =>
        appendTime τ₀ T (tposOf d b q).1 ∈ Ico (ξ ν (π_perm ν β).1) (ξ ν ((π_perm ν β).1 + 1))
    have hA_one : ∀ ν : ι, (A_of ν).card ≤ 1 := by
      intro ν
      refine card_le_one.mpr fun β₁ h₁ β₂ h₂ => ?_
      obtain ⟨hlo₁, hhi₁⟩ := mem_Ico.mp (mem_filter.mp h₁).2
      obtain ⟨hlo₂, hhi₂⟩ := mem_Ico.mp (mem_filter.mp h₂).2
      by_contra hne
      have hs_ne : (π_perm ν β₁).1 ≠ (π_perm ν β₂).1 := fun h => hne (hπ_inj ν (Fin.ext h))
      rcases lt_or_gt_of_ne hs_ne with hlt | hgt
      · have := hξ_mono ν ((π_perm ν β₁).1 + 1) (π_perm ν β₂).1 (by omega) (le_of_lt (π_perm ν β₂).2)
        omega
      · have := hξ_mono ν ((π_perm ν β₂).1 + 1) (π_perm ν β₁).1 (by omega) (le_of_lt (π_perm ν β₁).2)
        omega
    have hsub : A_blk q ⊆ (univ : Finset ι).biUnion A_of := by
      intro β hβ
      obtain ⟨_, ν, hmem⟩ := mem_filter.mp hβ
      exact mem_biUnion.mpr ⟨ν, mem_univ ν, mem_filter.mpr ⟨mem_univ β, hmem⟩⟩
    calc (A_blk q).card
        ≤ ((univ : Finset ι).biUnion A_of).card := card_le_card hsub
      _ ≤ ∑ ν : ι, (A_of ν).card := card_biUnion_le
      _ ≤ ∑ _ν : ι, 1 := sum_le_sum fun ν _ => hA_one ν
      _ = Fintype.card ι := by simp
      _ ≤ m₀ := hι
  -- Kinematic good input rows (the touching-run bound).
  have hx_in : IsWalk τ₀.input := τ₀.abs_input_succ_sub_le
  let GoodRows : Finset (Fin d) := (univ : Finset (Fin d)).filter fun i =>
    (inputRowTouchRuns τ₀.input T W i).card ≤ K_row ∧
    (∑ a ∈ inputRowTouchRuns τ₀.input T W i,
      (runEnd (inputRowBuf τ₀.input T W i) T a - a)) < K_row * W
  have hGood_ge : d - (3 * T) / (K_row * W) ≤ GoodRows.card :=
    kinematic_goodInputRows_card_ge hx_in T W d K_row hW hK_row
  let Z_heavy : Finset (Fin L) := V₀.filter fun q => bridgeRawRow q ∉ GoodRows
  have hZ_heavy_card : Z_heavy.card ≤ 3 * T / K_row := by
    have hBadRows : (univ \ GoodRows).card ≤ (3 * T) / (K_row * W) := by
      have hadd := card_sdiff_add_card_inter (univ : Finset (Fin d)) GoodRows
      have hinter : ((univ : Finset (Fin d)) ∩ GoodRows).card = GoodRows.card := by simp
      have huniv : (univ : Finset (Fin d)).card = d := by simp
      omega
    have hsub : Z_heavy ⊆ (univ : Finset (Fin L)).filter fun q =>
        bridgeRawRow q ∈ univ \ GoodRows := by
      intro q hq
      obtain ⟨_, hnotG⟩ := mem_filter.mp hq
      exact mem_filter.mpr ⟨mem_univ q, mem_sdiff.mpr ⟨mem_univ _, hnotG⟩⟩
    calc Z_heavy.card
        ≤ ((univ : Finset (Fin L)).filter fun q => bridgeRawRow q ∈ univ \ GoodRows).card :=
          card_le_card hsub
      _ ≤ (univ \ GoodRows).card * W := card_filter_bridgeRawRow_le (univ \ GoodRows)
      _ ≤ ((3 * T) / (K_row * W)) * W := Nat.mul_le_mul_right W hBadRows
      _ = ((3 * T / K_row) / W) * W := by rw [Nat.div_div_eq_div_mul]
      _ ≤ 3 * T / K_row := Nat.div_mul_le_self (3 * T / K_row) W
  -- Forward block bound `|E_blk p| ≤ 2 * K_row` whenever `bridgeRawRow p ∈ GoodRows`.
  have hE_card : ∀ p : Fin L, bridgeRawRow p ∈ GoodRows → (E_blk p).card ≤ 2 * K_row := by
    intro p hpG
    let i := bridgeRawRow p
    let B_i := inputRowBuf τ₀.input T W i
    let Touch := inputRowTouchRuns τ₀.input T W i
    obtain ⟨_, hTouch_card, hTouch_sum⟩ := mem_filter.mp hpG
    let HitBlocks : ℕ → Finset (Fin B_time) := fun a =>
      (univ : Finset (Fin B_time)).filter fun β =>
        (timeBlock T B_time β ∩ Ico a (runEnd B_i T a)).Nonempty
    have hsub_E : E_blk p ⊆ Touch.biUnion HitBlocks := by
      intro β hβ
      obtain ⟨_, t, ht_blk, hxt⟩ := mem_filter.mp hβ
      have ht_lt_T : t < T := by
        obtain ⟨_, ht_hi⟩ := mem_Ico.mp ht_blk
        unfold timeBlockHi at ht_hi
        split_ifs at ht_hi with hlt
        · exact lt_of_lt_of_le ht_hi
            ((Nat.mul_le_mul_right _ (le_of_lt hlt)).trans (Nat.mul_div_le T B_time))
        · exact ht_hi
      have hpb := bridgeRawRow_bounds p
      have ht_reads : t ∈ inputRowReads τ₀.input T W i := by
        unfold inputRowReads
        refine mem_filter.mpr ⟨mem_range.mpr ht_lt_T, ?_, ?_⟩
        · rw [hxt]; exact_mod_cast hpb.1
        · rw [hxt]; exact_mod_cast hpb.2
      have ht_touch := inputRowReads_subset_touchRuns_biUnion τ₀.input T W hW i ht_reads
      obtain ⟨a, haT, ht_ico⟩ := mem_biUnion.mp ht_touch
      exact mem_biUnion.mpr ⟨a, haT, mem_filter.mpr ⟨mem_univ β, t, mem_inter.mpr ⟨ht_blk, ht_ico⟩⟩⟩
    have hHit_le : ∀ a ∈ Touch, (HitBlocks a).card ≤ 2 := by
      intro a haT
      have hsingle : runEnd B_i T a - a ≤ ∑ a' ∈ Touch, (runEnd B_i T a' - a') :=
        single_le_sum (f := fun a' => runEnd B_i T a' - a') (fun _ _ => Nat.zero_le _) haT
      exact card_timeBlocks_inter_ico_le_two (lt_of_le_of_lt hsingle (lt_of_lt_of_le hTouch_sum hKW_le_Q))
    calc (E_blk p).card
        ≤ (Touch.biUnion HitBlocks).card := card_le_card hsub_E
      _ ≤ ∑ a ∈ Touch, (HitBlocks a).card := card_biUnion_le
      _ ≤ ∑ _a ∈ Touch, 2 := sum_le_sum hHit_le
      _ = 2 * Touch.card := by simp [Nat.mul_comm]
      _ ≤ 2 * K_row := Nat.mul_le_mul_left 2 hTouch_card
  -- Helper: `getLastD` of an `IsDepPath` from `u₀ < T` stays `< T`.
  have hlast_lt_T : ∀ (ρ : List ℕ) (u₀ : ℕ), u₀ < T →
      IsDepPath τ₀.work T (u₀ :: ρ) → (u₀ :: ρ).getLastD u₀ < T := by
    intro ρ
    induction ρ with
    | nil => intro u₀ hu₀ _; exact hu₀
    | cons u₁ ρ' ih =>
      intro u₀ _ ⟨hstep, htail⟩
      rw [LinNet.getLastD_cons_cons]
      exact ih u₁ (lt_trans (depStep_lt hstep).1 (depStep_lt hstep).2) htail
  -- Prune `Z_bad` and `Z_heavy`, verify `hcut` and self-collision bound, and apply `uniformBlockCut`.
  let V₀' : Finset (Fin L) := (V₀ \ Z_bad) \ Z_heavy
  have hcut' : ∀ q ∈ V₀', ∀ p ∈ V₀',
      p ∈ ballAvoidSystem τ₀ T D B d b q → (A_blk q ∩ E_blk p).Nonempty := by
    intro q hq' p hp' hp_mem
    have hq_VZ : q ∈ V₀ \ Z_bad := (Finset.mem_sdiff.mp hq').1
    have hp_V₀ : p ∈ V₀ := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hp').1).1
    unfold ballAvoidSystem at hp_mem
    obtain ⟨_, ρ, hdep, hfree, hrd, hlen_ρ⟩ := mem_filter.mp hp_mem
    let u₀ := appendTime τ₀ T (tposOf d b q).1
    have hu₀_lt_T : u₀ < T := appendTime_lt τ₀ T (by rw [hlen]; exact (tposOf d b q).2)
    let t_m := (u₀ :: ρ).getLastD u₀
    have ht_m_lt_T : t_m < T := hlast_lt_T ρ u₀ hu₀_lt_T hdep
    obtain ⟨β, ht_m_blk⟩ := exists_mem_timeBlock hB_time hBT ht_m_lt_T
    have hxt_m : τ₀.input t_m = (p.1 : ℤ) := readPos_eq_some_iff.mp hrd
    obtain ⟨ν, hu₀_ico⟩ := hpull q hq_VZ p hp_V₀ ρ hlen_ρ hdep hfree hxt_m β ht_m_blk
    refine ⟨β, mem_inter.mpr ⟨?_, ?_⟩⟩
    · exact mem_filter.mpr ⟨mem_univ β, ν, hu₀_ico⟩
    · exact mem_filter.mpr ⟨mem_univ β, t_m, ht_m_blk, hxt_m⟩
  let Q_star : Finset (Fin L) := V₀'.filter fun q => Disjoint (A_blk q) (E_blk q)
  have hbound' : ∀ q ∈ Q_star, (A_blk q).card ≤ m₀ ∧ (E_blk q).card ≤ 2 * K_row := by
    intro q hqQ
    have hq' := (mem_filter.mp hqQ).1
    obtain ⟨hqVZ, hqNotH⟩ := mem_sdiff.mp hq'
    have hqV := (mem_sdiff.mp hqVZ).1
    have hpG : bridgeRawRow q ∈ GoodRows := by
      by_contra hnotG
      exact hqNotH (mem_filter.mpr ⟨hqV, hnotG⟩)
    exact ⟨hA_card q, hE_card q hpG⟩
  -- Bound self-collisions `V₀' \ Q_star`.
  let CollOf : ι → Finset (Fin L) := fun ν =>
    (univ : Finset (Fin L)).filter fun q =>
      ∃ β : Fin B_time,
        appendTime τ₀ T (tposOf d b q).1 ∈ Ico (ξ ν (π_perm ν β).1) (ξ ν ((π_perm ν β).1 + 1)) ∧
        ∃ t ∈ timeBlock T B_time β, τ₀.input t = (q.1 : ℤ)
  have hColl_sub : V₀' \ Q_star ⊆ (univ : Finset ι).biUnion CollOf := by
    intro q hq
    obtain ⟨hq', hqNotQ⟩ := mem_sdiff.mp hq
    have hnot_disj : ¬ Disjoint (A_blk q) (E_blk q) :=
      fun hd_q => hqNotQ (mem_filter.mpr ⟨hq', hd_q⟩)
    rw [Finset.not_disjoint_iff] at hnot_disj
    obtain ⟨β, hβA, hβE⟩ := hnot_disj
    obtain ⟨_, ν, hu₀_ico⟩ := mem_filter.mp hβA
    obtain ⟨_, t, ht_blk, hxt⟩ := mem_filter.mp hβE
    exact mem_biUnion.mpr ⟨ν, mem_univ ν, mem_filter.mpr ⟨mem_univ q, β, hu₀_ico, t, ht_blk, hxt⟩⟩
  have hColl_card : (V₀' \ Q_star).card ≤ m₀ * (T / B_time) + m₀ * (2 * B_time + 2) * W := by
    calc (V₀' \ Q_star).card
        ≤ ((univ : Finset ι).biUnion CollOf).card := card_le_card hColl_sub
      _ ≤ ∑ ν : ι, (CollOf ν).card := card_biUnion_le
      _ ≤ ∑ _ν : ι, (T / B_time + (2 * B_time + 2) * W) :=
          sum_le_sum fun ν _ =>
            card_selfCollisions_singleFamily_le τ₀ hd hb hB_time hlen (ξ ν) (hξ_mono ν)
              (π_perm ν) (hπ_inj ν)
      _ = Fintype.card ι * (T / B_time + (2 * B_time + 2) * W) := by simp
      _ ≤ m₀ * (T / B_time + (2 * B_time + 2) * W) := Nat.mul_le_mul_right _ hι
      _ = m₀ * (T / B_time) + m₀ * (2 * B_time + 2) * W := by ring
  have hV₀_le : V₀.card ≤ Q_star.card + Z_bad.card + 3 * T / K_row +
      m₀ * (T / B_time) + m₀ * (2 * B_time + 2) * W := by
    have h1 : V₀.card ≤ (V₀ \ Z_bad).card + Z_bad.card := by
      have := card_sdiff_add_card_inter V₀ Z_bad
      have := card_le_card (inter_subset_right (s₁ := V₀) (s₂ := Z_bad))
      omega
    have h2 : (V₀ \ Z_bad).card ≤ V₀'.card + Z_heavy.card := by
      dsimp only [V₀']
      have := card_sdiff_add_card_inter (V₀ \ Z_bad) Z_heavy
      have := card_le_card (inter_subset_right (s₁ := V₀ \ Z_bad) (s₂ := Z_heavy))
      omega
    have h3 : V₀'.card ≤ Q_star.card + (V₀' \ Q_star).card := by
      have hsubQ : Q_star ⊆ V₀' := filter_subset _ _
      have := card_sdiff_add_card_eq_card hsubQ
      omega
    omega
  obtain ⟨σ, hacyc, hsubU, hU_card⟩ :=
    exists_isAcyclicIn_card_ge_of_uniformBlockCut hcut' hbound'
  have hV₀'_sub : V₀' ⊆ V₀ := sdiff_subset.trans sdiff_subset
  exact ⟨cutSet V₀' A_blk E_blk σ, Q_star.card, hsubU.trans hV₀'_sub, hacyc, hV₀_le, hU_card⟩

/-- Depth-independent density constant `ρ_min(m₀, C, α) = 1 / (3 * C(m₀ + 2⌈24C/α⌉, m₀))` of Theorem 5.1 (time pullback). -/
noncomputable def timePullbackRhoMin (m₀ : ℕ) (C α : ℝ) : ℝ :=
  1 / (3 * (Nat.choose (m₀ + 2 * ⌈24 * C / α⌉₊) m₀ : ℝ))

theorem timePullbackRhoMin_pos (m₀ : ℕ) (C α : ℝ) : 0 < timePullbackRhoMin m₀ C α := by
  unfold timePullbackRhoMin
  have hch : (0 : ℝ) < (Nat.choose (m₀ + 2 * ⌈24 * C / α⌉₊) m₀ : ℝ) := by
    exact_mod_cast Nat.choose_pos (Nat.le_add_right _ _)
  positivity

end MinimalTimePullbackMAIS

/-! ## §3. Work-Phase Partition, Micro-Hop Threshold Guard, & Phase-Exit Chain Pullback (Theorem 5.3 (bridge) Core) -/

section PhaseExitChainPullback

open scoped Classical

/-- **Strictly Smaller Crossing-Lower Step Set:**
Steps `v < T` that are the **lower endpoint** of an in-band `(> 2W)` revisit hop `(v, u)`
(`excursion in (2W, ⌊L / ηInv⌋]`) crossing another in-band `(> 2W)` revisit hop on the same work tape
(`no owner-load clause and no upper endpoints`). Since `crossingLowerEtaSteps ⊆ mixEtaSteps`, any
vertex-expansion lower bound into `crossingLowerEtaSteps` is **strictly stronger** than into `mixEtaSteps`. -/
noncomputable def crossingLowerEtaSteps {k : ℕ} (τ₀ : Trace k) (T W ηInv L : ℕ) : Finset ℕ :=
  (range T).filter fun v =>
    ∃ (j : Fin k) (u : ℕ),
      HopInBand (τ₀.work j) T (2 * W) (L / ηInv) v u ∧
      ∃ p' u' : ℕ, HopInBand (τ₀.work j) T (2 * W) (L / ηInv) p' u' ∧ HopsCross v u p' u'

theorem crossingLowerEtaSteps_subset_mixEtaSteps {k : ℕ} (τ₀ : Trace k) (T W ηInv L : ℕ) :
    crossingLowerEtaSteps τ₀ T W ηInv L ⊆ mixEtaSteps τ₀ T W ηInv L := by
  intro v hv
  obtain ⟨hvT, j, u, hband, p', u', hband', hcross⟩ := mem_filter.mp hv
  exact mem_filter.mpr ⟨hvT, j, v, u, Or.inl rfl, hband, Or.inr ⟨p', u', hband', hcross⟩⟩

theorem isMengerVertexCut_mono_dst {k T : ℕ} {xs : Fin k → ℕ → ℤ} {Src Dst₁ Dst₂ B : Finset ℕ}
    (hsub : Dst₁ ⊆ Dst₂) (hcut : IsMengerVertexCut xs T Src Dst₂ B) :
    IsMengerVertexCut xs T Src Dst₁ B :=
  fun π t₀ hsrc hdep hdst => hcut π t₀ hsrc hdep (hsub hdst)

/-- **Work-Phase Partition Lemma (`Step 1 of Theorem 5.3 (bridge)`):**
Given `θ_pos, θ_neg : Fin k → ℕ` (`≤ T`) and `1 ≤ T`, sorting `{0, T} ∪ im(θ_pos) ∪ im(θ_neg)` yields
`1 ≤ M_work ≤ 2 * k + 1` non-empty contiguous phases `[θ_lo γ, θ_hi γ)` partitioning `[0, T)` such that
no cut `θ_pos j` or `θ_neg j` lies strictly inside any phase! -/
theorem exists_workPhase_partition {k T : ℕ} (hT : 1 ≤ T)
    (θ_pos θ_neg : Fin k → ℕ) (hθ : ∀ j : Fin k, θ_pos j ≤ T ∧ θ_neg j ≤ T) :
    ∃ (M_work : ℕ) (θ_lo θ_hi : Fin M_work → ℕ) (ph : ℕ → Fin M_work),
      1 ≤ M_work ∧ M_work ≤ 2 * k + 1 ∧
      (∀ γ : Fin M_work, θ_lo γ < θ_hi γ ∧ θ_hi γ ≤ T) ∧
      (∀ c₁ c₂ : Fin M_work, c₁.1 < c₂.1 → θ_hi c₁ ≤ θ_lo c₂) ∧
      (∀ (γ : Fin M_work) (j : Fin k),
        ¬ (θ_lo γ < θ_pos j ∧ θ_pos j < θ_hi γ) ∧
        ¬ (θ_lo γ < θ_neg j ∧ θ_neg j < θ_hi γ)) ∧
      (∀ t : ℕ, t < T → t ∈ Ico (θ_lo (ph t)) (θ_hi (ph t))) ∧
      (∀ (t : ℕ) (γ : Fin M_work), t ∈ Ico (θ_lo γ) (θ_hi γ) → ph t = γ) ∧
      (∀ t₁ t₂ : ℕ, t₁ ≤ t₂ → t₂ < T → (ph t₁).1 ≤ (ph t₂).1) := by
  let S_cuts : Finset ℕ :=
    insert 0 (insert T (((univ : Finset (Fin k)).image θ_pos) ∪ ((univ : Finset (Fin k)).image θ_neg)))
  have h0_mem : 0 ∈ S_cuts := mem_insert_self 0 _
  have hT_mem : T ∈ S_cuts := mem_insert_of_mem (mem_insert_self T _)
  have hS_le_T : ∀ x ∈ S_cuts, x ≤ T := by
    intro x hx
    rcases mem_insert.mp hx with rfl | hx1
    · omega
    · rcases mem_insert.mp hx1 with rfl | hx2
      · exact le_rfl
      · rcases mem_union.mp hx2 with hp | hn
        · obtain ⟨j, _, rfl⟩ := mem_image.mp hp; exact (hθ j).1
        · obtain ⟨j, _, rfl⟩ := mem_image.mp hn; exact (hθ j).2
  have hcard_ge : 2 ≤ S_cuts.card := by
    have hsub : ({0, T} : Finset ℕ) ⊆ S_cuts :=
      insert_subset h0_mem (singleton_subset_iff.mpr hT_mem)
    have hc2 : ({0, T} : Finset ℕ).card = 2 := card_pair (by omega)
    exact hc2 ▸ card_le_card hsub
  have hcard_le : S_cuts.card ≤ 2 * k + 2 := by
    have h1 := card_insert_le 0 (insert T (((univ : Finset (Fin k)).image θ_pos) ∪ ((univ : Finset (Fin k)).image θ_neg)))
    have h2 := card_insert_le T (((univ : Finset (Fin k)).image θ_pos) ∪ ((univ : Finset (Fin k)).image θ_neg))
    have h3 := card_union_le ((univ : Finset (Fin k)).image θ_pos) ((univ : Finset (Fin k)).image θ_neg)
    have h4 : ((univ : Finset (Fin k)).image θ_pos).card ≤ k := card_image_le.trans (by simp)
    have h5 : ((univ : Finset (Fin k)).image θ_neg).card ≤ k := card_image_le.trans (by simp)
    dsimp only [S_cuts]
    omega
  let M_work := S_cuts.card - 1
  have hM_ge : 1 ≤ M_work := by omega
  have hM_le : M_work ≤ 2 * k + 1 := by omega
  have hS_card : S_cuts.card = M_work + 1 := by omega
  obtain ⟨f, hf_mono, hf_mem, hf_surj⟩ := LeanMachine.ThresholdRefinement.exists_strictMono_equiv_of_finset (M_work + 1) S_cuts hS_card
  have hf0 : f ⟨0, by omega⟩ = 0 := by
    obtain ⟨i, hi⟩ := hf_surj 0 h0_mem
    rcases Nat.eq_zero_or_pos i.1 with h0 | hpos
    · have : i = ⟨0, by omega⟩ := Fin.ext h0
      rwa [this] at hi
    · exfalso
      have hlt := hf_mono (show (⟨0, by omega⟩ : Fin (M_work + 1)) < i from hpos)
      omega
  have hfM : f ⟨M_work, by omega⟩ = T := by
    obtain ⟨i, hi⟩ := hf_surj T hT_mem
    rcases eq_or_lt_of_le (Nat.le_of_lt_succ i.2) with heq | hlt
    · have : i = ⟨M_work, by omega⟩ := Fin.ext heq
      rwa [this] at hi
    · exfalso
      have hlt_f := hf_mono (show i < (⟨M_work, by omega⟩ : Fin (M_work + 1)) from hlt)
      have hle_T := hS_le_T _ (hf_mem ⟨M_work, by omega⟩)
      omega
  let θ_lo : Fin M_work → ℕ := fun γ => f ⟨γ.1, by omega⟩
  let θ_hi : Fin M_work → ℕ := fun γ => f ⟨γ.1 + 1, by omega⟩
  have hlo_lt_hi : ∀ γ : Fin M_work, θ_lo γ < θ_hi γ ∧ θ_hi γ ≤ T := by
    intro γ
    exact ⟨hf_mono (show (⟨γ.1, by omega⟩ : Fin (M_work + 1)) < ⟨γ.1 + 1, by omega⟩ by simp),
      hS_le_T _ (hf_mem ⟨γ.1 + 1, by omega⟩)⟩
  have hsep_ph : ∀ c₁ c₂ : Fin M_work, c₁.1 < c₂.1 → θ_hi c₁ ≤ θ_lo c₂ := by
    intro c₁ c₂ hlt
    exact hf_mono.monotone (show (⟨c₁.1 + 1, by omega⟩ : Fin (M_work + 1)) ≤ ⟨c₂.1, by omega⟩ from hlt)
  have hno_inner : ∀ (γ : Fin M_work) (x : ℕ), x ∈ S_cuts → ¬ (θ_lo γ < x ∧ x < θ_hi γ) := by
    intro γ x hx ⟨h1, h2⟩
    obtain ⟨i, rfl⟩ := hf_surj x hx
    have hi1 : γ.1 < i.1 := by
      by_contra hle; push Not at hle
      have := hf_mono.monotone (show i ≤ ⟨γ.1, by omega⟩ from hle)
      dsimp [θ_lo] at h1; omega
    have hi2 : i.1 < γ.1 + 1 := by
      by_contra hge; push Not at hge
      have := hf_mono.monotone (show (⟨γ.1 + 1, by omega⟩ : Fin (M_work + 1)) ≤ i from hge)
      dsimp [θ_hi] at h2; omega
    omega
  let ph : ℕ → Fin M_work := fun t =>
    if ht : t < T then
      let I_le := (univ : Finset (Fin (M_work + 1))).filter fun i => f i ≤ t
      have hne : I_le.Nonempty := ⟨⟨0, by omega⟩, mem_filter.mpr ⟨mem_univ _, by omega⟩⟩
      let i_max := I_le.max' hne
      have hi_lt : i_max.1 < M_work := by
        rcases eq_or_lt_of_le (Nat.le_of_lt_succ i_max.2) with heq | hlt
        · exfalso
          have hmem : f i_max ≤ t := (mem_filter.mp (I_le.max'_mem hne)).2
          have : i_max = ⟨M_work, by omega⟩ := Fin.ext heq
          rw [this, hfM] at hmem; omega
        · exact hlt
      ⟨i_max.1, hi_lt⟩
    else ⟨0, hM_ge⟩
  have hph_mem : ∀ t : ℕ, t < T → t ∈ Ico (θ_lo (ph t)) (θ_hi (ph t)) := by
    intro t ht
    dsimp only [ph]
    simp only [ht, ↓reduceDIte]
    let I_le := (univ : Finset (Fin (M_work + 1))).filter fun i => f i ≤ t
    have hne : I_le.Nonempty := ⟨⟨0, by omega⟩, mem_filter.mpr ⟨mem_univ _, by omega⟩⟩
    let i_max := I_le.max' hne
    have hi_le : f i_max ≤ t := (mem_filter.mp (I_le.max'_mem hne)).2
    have hi_lt : i_max.1 < M_work := by
      rcases eq_or_lt_of_le (Nat.le_of_lt_succ i_max.2) with heq | hlt
      · exfalso; have : i_max = ⟨M_work, by omega⟩ := Fin.ext heq; rw [this, hfM] at hi_le; omega
      · exact hlt
    have hlo_t : θ_lo ⟨i_max.1, hi_lt⟩ ≤ t := hi_le
    have ht_hi : t < θ_hi ⟨i_max.1, hi_lt⟩ := by
      dsimp [θ_hi]
      by_contra hge; push Not at hge
      have hmem_s : (⟨i_max.1 + 1, by omega⟩ : Fin (M_work + 1)) ∈ I_le :=
        mem_filter.mpr ⟨mem_univ _, hge⟩
      have hle_max : i_max.1 + 1 ≤ i_max.1 := I_le.le_max' _ hmem_s
      omega
    exact mem_Ico.mpr ⟨hlo_t, ht_hi⟩
  have hph_uniq : ∀ (t : ℕ) (γ : Fin M_work), t ∈ Ico (θ_lo γ) (θ_hi γ) → ph t = γ := by
    intro t γ ht_γ
    obtain ⟨h1, h2⟩ := mem_Ico.mp ht_γ
    have htT : t < T := lt_of_lt_of_le h2 (hlo_lt_hi γ).2
    obtain ⟨h3, h4⟩ := mem_Ico.mp (hph_mem t htT)
    by_contra hne
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
    · have := hsep_ph (ph t) γ hlt; omega
    · have := hsep_ph γ (ph t) hgt; omega
  have hph_mono : ∀ t₁ t₂ : ℕ, t₁ ≤ t₂ → t₂ < T → (ph t₁).1 ≤ (ph t₂).1 := by
    intro t₁ t₂ hle ht₂
    obtain ⟨h1, _⟩ := mem_Ico.mp (hph_mem t₁ (lt_of_le_of_lt hle ht₂))
    obtain ⟨_, h4⟩ := mem_Ico.mp (hph_mem t₂ ht₂)
    by_contra hgt; push Not at hgt
    have := hsep_ph (ph t₂) (ph t₁) hgt
    omega
  refine ⟨M_work, θ_lo, θ_hi, ph, hM_ge, hM_le, hlo_lt_hi, hsep_ph, fun γ j => ⟨?_, ?_⟩,
    hph_mem, hph_uniq, hph_mono⟩
  · exact hno_inner γ (θ_pos j)
      (mem_insert_of_mem (mem_insert_of_mem (mem_union_left _ (mem_image_of_mem _ (mem_univ j)))))
  · exact hno_inner γ (θ_neg j)
      (mem_insert_of_mem (mem_insert_of_mem (mem_union_right _ (mem_image_of_mem _ (mem_univ j)))))

/-- **Micro-Hop Threshold Guard `Γ_step(ψ)` (`Step 2 of Theorem 5.3 (bridge)`):**
Guards `ψ - 1` together with all lower endpoints `p ≤ ψ - 1` of revisit hops `(p, u)` (`ψ ≤ u`)
whose excursion on any tape `j` is at most `2 * W`. -/
noncomputable def microHopStepGuard {k : ℕ} (τ₀ : Trace k) (T W ψ : ℕ) : Finset ℕ :=
  if ψ = 0 then ∅
  else insert (ψ - 1) ((univ : Finset (Fin k)).biUnion fun j =>
    smallCrossingLowers (τ₀.work j) T (2 * W) (ψ - 1))

theorem card_microHopStepGuard_le {k : ℕ} (τ₀ : Trace k) (T : ℕ) {W : ℕ} (hW : 1 ≤ W) (ψ : ℕ) :
    (microHopStepGuard τ₀ T W ψ).card ≤ (5 * k + 1) * W := by
  unfold microHopStepGuard
  split_ifs with h0
  · simp
  · have hbi : (((univ : Finset (Fin k)).biUnion fun j =>
        smallCrossingLowers (τ₀.work j) T (2 * W) (ψ - 1))).card ≤ k * (4 * W + 1) := by
      calc (((univ : Finset (Fin k)).biUnion fun j =>
            smallCrossingLowers (τ₀.work j) T (2 * W) (ψ - 1))).card
          ≤ ∑ j : Fin k, (smallCrossingLowers (τ₀.work j) T (2 * W) (ψ - 1)).card := card_biUnion_le
        _ ≤ ∑ _j : Fin k, (2 * (2 * W) + 1) :=
            sum_le_sum fun j _ => card_smallCrossingLowers_le (τ₀.work j) T (2 * W) (ψ - 1)
        _ = k * (4 * W + 1) := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]; ring
    have hins := card_insert_le (ψ - 1) ((univ : Finset (Fin k)).biUnion fun j =>
      smallCrossingLowers (τ₀.work j) T (2 * W) (ψ - 1))
    have hkW : k ≤ k * W := Nat.le_mul_of_pos_right k hW
    nlinarith

/-- Parity of a phase-exit chain (`false` = even length, tracking `< ψ`; `true` = odd length, tracking `ψ ≤ ·`). -/
def chainParity {α : Type*} : List α → Bool
  | [] => false
  | _ :: rest => !chainParity rest

/-- Parity-indexed threshold predicate (`t < ψ` when `b_par = false`, `ψ ≤ t` when `b_par = true`). -/
def chainPred (b_par : Bool) (ψ t : ℕ) : Prop :=
  if b_par then ψ ≤ t else t < ψ

/-- **Intra-Phase `< ψ` / `chainPred` Invariance (`Step 2a of Theorem 5.3 (bridge)`):**
When an edge `u → v` stays inside `[θ_lo, θ_hi)` (where neither `θ_pos j` nor `θ_neg j` lies strictly
inside) and `v ∉ microHopStepGuard τ₀ T W ψ`, the threshold predicate `chainPred b_par ψ` is **invariant**
across `u → v`! -/
theorem dichotomy_intraPhase_chainPred_iff {k T W θ_lo θ_hi : ℕ} {τ₀ : Trace k}
    {θ_pos θ_neg : Fin k → ℕ}
    (hno_cut : ∀ j : Fin k, ¬ (θ_lo < θ_pos j ∧ θ_pos j < θ_hi) ∧ ¬ (θ_lo < θ_neg j ∧ θ_neg j < θ_hi))
    {u v : ℕ} (hu : u ∈ Ico θ_lo θ_hi) (hv : v ∈ Ico θ_lo θ_hi)
    (hdich : u = v + 1 ∨
      (∃ j : Fin k, IsHop (τ₀.work j) T v u ∧
        ∀ t ∈ Ioo v u, |τ₀.work j t - τ₀.work j v| ≤ ((2 * W : ℕ) : ℤ)) ∨
      (∃ j : Fin k, IsNonCrossingLargeHop (τ₀.work j) T (2 * W) v u ∧
        ((v < θ_pos j ∧ θ_pos j ≤ u) ∨ (v < θ_neg j ∧ θ_neg j ≤ u))))
    {ψ : ℕ} (hv_guard : v ∉ microHopStepGuard τ₀ T W ψ) (b_par : Bool) :
    chainPred b_par ψ u ↔ chainPred b_par ψ v := by
  obtain ⟨hu_lo, hu_hi⟩ := mem_Ico.mp hu
  obtain ⟨hv_lo, hv_hi⟩ := mem_Ico.mp hv
  suffices hlt_iff : u < ψ ↔ v < ψ by
    cases b_par
    · simp only [chainPred, Bool.false_eq_true, ↓reduceIte]; exact hlt_iff
    · simp only [chainPred, ↓reduceIte]; omega
  rcases hdich with rfl | ⟨j, hhop, hsmall⟩ | ⟨j, _, hstrad⟩
  · constructor
    · intro h; omega
    · intro hv_lt
      by_contra hge; push Not at hge
      have hψ_pos : ψ ≠ 0 := by omega
      have hv_eq : v = ψ - 1 := by omega
      apply hv_guard
      unfold microHopStepGuard
      simp only [hψ_pos, ↓reduceIte, hv_eq]
      exact mem_insert_self _ _
  · have hvu : v < u := lt_trans (Nat.lt_succ_self v) hhop.1
    constructor
    · intro hu_lt; exact lt_trans hvu hu_lt
    · intro hv_lt
      by_contra hge; push Not at hge
      have hψ_pos : ψ ≠ 0 := by omega
      have hvT : v < T := lt_trans hvu hhop.2.1
      apply hv_guard
      unfold microHopStepGuard
      simp only [hψ_pos, ↓reduceIte]
      refine mem_insert_of_mem (mem_biUnion.mpr ⟨j, mem_univ j, ?_⟩)
      unfold smallCrossingLowers
      exact mem_filter.mpr ⟨mem_range.mpr hvT, by omega, u, by omega, hhop, hsmall⟩
  · exfalso
    rcases hstrad with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact (hno_cut j).1 ⟨by omega, by omega⟩
    · exact (hno_cut j).2 ⟨by omega, by omega⟩

/-- **Forced Inter-Phase Non-Crossing Hop (`Step 2b of Theorem 5.3 (bridge)`):**
When an edge `u → v` exits phase `[θ_lo, θ_hi)` (`v < θ_lo ≤ u`) and `v ∉ microHopStepGuard τ₀ T W θ_lo`,
it **must** traverse an `IsNonCrossingLargeHop (τ₀.work j) T (2 * W) v u` for some tape `j`! -/
theorem dichotomy_interPhase_exists_hop {k T W θ_lo : ℕ} {τ₀ : Trace k}
    {θ_pos θ_neg : Fin k → ℕ} {u v : ℕ}
    (hlo_u : θ_lo ≤ u) (hv_lt : v < θ_lo)
    (hdich : u = v + 1 ∨
      (∃ j : Fin k, IsHop (τ₀.work j) T v u ∧
        ∀ t ∈ Ioo v u, |τ₀.work j t - τ₀.work j v| ≤ ((2 * W : ℕ) : ℤ)) ∨
      (∃ j : Fin k, IsNonCrossingLargeHop (τ₀.work j) T (2 * W) v u ∧
        ((v < θ_pos j ∧ θ_pos j ≤ u) ∨ (v < θ_neg j ∧ θ_neg j ≤ u))))
    (hv_guard : v ∉ microHopStepGuard τ₀ T W θ_lo) :
    ∃ j : Fin k, IsNonCrossingLargeHop (τ₀.work j) T (2 * W) v u := by
  have hθ_pos : θ_lo ≠ 0 := by omega
  rcases hdich with rfl | ⟨j, hhop, hsmall⟩ | ⟨j, hnc, _⟩
  · exfalso
    have hv_eq : v = θ_lo - 1 := by omega
    apply hv_guard
    unfold microHopStepGuard
    simp only [hθ_pos, ↓reduceIte, hv_eq]
    exact mem_insert_self _ _
  · exfalso
    have hvT : v < T := lt_trans (lt_trans (Nat.lt_succ_self v) hhop.1) hhop.2.1
    apply hv_guard
    unfold microHopStepGuard
    simp only [hθ_pos, ↓reduceIte]
    refine mem_insert_of_mem (mem_biUnion.mpr ⟨j, mem_univ j, ?_⟩)
    unfold smallCrossingLowers
    exact mem_filter.mpr ⟨mem_range.mpr hvT, by omega, u, by omega, hhop, hsmall⟩
  · exact ⟨j, hnc⟩

/-- **Strict Antitonicity of Inter-Phase Non-Crossing Hops (`Step 3a of Theorem 5.3 (bridge)`):**
Across any phase boundary `θ_hi_nxt ≤ θ_lo_cur`, `IsNonCrossingLargeHop y T (2 * W)` defines a
1-to-1 antitone partial map: `u₁ ≤ u₂ → v₂ ≤ v₁`! -/
theorem interPhase_nonCrossing_antitone {y : ℕ → ℤ} {T W lo_cur hi_cur lo_nxt hi_nxt u₁ v₁ u₂ v₂ : ℕ}
    (hsep : hi_nxt ≤ lo_cur)
    (hu₁ : u₁ ∈ Ico lo_cur hi_cur) (hv₁ : v₁ ∈ Ico lo_nxt hi_nxt)
    (h₁ : IsNonCrossingLargeHop y T (2 * W) v₁ u₁)
    (hu₂ : u₂ ∈ Ico lo_cur hi_cur) (hv₂ : v₂ ∈ Ico lo_nxt hi_nxt)
    (h₂ : IsNonCrossingLargeHop y T (2 * W) v₂ u₂)
    (hu₁₂ : u₁ ≤ u₂) :
    v₂ ≤ v₁ := by
  have hv₁_cut : v₁ < lo_cur := lt_of_lt_of_le (mem_Ico.mp hv₁).2 hsep
  have hu₁_cut : lo_cur ≤ u₁ := (mem_Ico.mp hu₁).1
  have hv₂_cut : v₂ < lo_cur := lt_of_lt_of_le (mem_Ico.mp hv₂).2 hsep
  have hu₂_cut : lo_cur ≤ u₂ := (mem_Ico.mp hu₂).1
  rcases eq_or_lt_of_le hu₁₂ with rfl | hlt
  · have heq := hop_crossingCut_unique h₁.1 h₂.1 hv₁_cut hu₁_cut hv₂_cut hu₂_cut rfl
    omega
  · have hnc : ¬ HopsCross v₁ u₁ v₂ u₂ := h₁.2.2 v₂ u₂ h₂.1 h₂.2.1
    exact le_of_lt (crossingCut_nonCrossing_strictAnti h₁.1 h₂.1 hv₁_cut hu₁_cut hv₂_cut hu₂_cut hnc hlt).1

/-- Valid strictly-decreasing phase-exit step list below phase index `n`. -/
def ValidStepsBelow {M_work k : ℕ} : ℕ → List (Fin M_work × Fin k) → Prop
  | _, [] => True
  | n, (γ', _) :: rest => γ'.1 < n ∧ ValidStepsBelow γ'.1 rest

theorem validStepsBelow_mono {M_work k : ℕ} {n₁ n₂ : ℕ} (hle : n₁ ≤ n₂)
    {steps : List (Fin M_work × Fin k)} (hv : ValidStepsBelow n₁ steps) :
    ValidStepsBelow n₂ steps := by
  cases steps with
  | nil => trivial
  | cons hd tl => exact ⟨lt_of_lt_of_le hv.1 hle, hv.2⟩

/-- Decoding `f : Fin n → Option (Fin k)` (`n ≤ M_work`) into a strictly decreasing list of phase exits. -/
def decodeSteps (M_work k : ℕ) :
    (n : ℕ) → (n ≤ M_work) → (Fin n → Option (Fin k)) → List (Fin M_work × Fin k)
  | 0, _, _ => []
  | n + 1, hn, f =>
    match f ⟨n, Nat.lt_succ_self n⟩ with
    | none => decodeSteps M_work k n (by omega) (fun i => f i.castSucc)
    | some j => (⟨n, hn⟩, j) :: decodeSteps M_work k n (by omega) (fun i => f i.castSucc)

theorem decodeSteps_validStepsBelow (M_work k : ℕ) :
    ∀ (n : ℕ) (hn : n ≤ M_work) (f : Fin n → Option (Fin k)),
      ValidStepsBelow n (decodeSteps M_work k n hn f) ∧
      (decodeSteps M_work k n hn f).length ≤ n
  | 0, _, _ => ⟨trivial, le_rfl⟩
  | n + 1, hn, f => by
    obtain ⟨hv_sub, hlen_sub⟩ := decodeSteps_validStepsBelow M_work k n (by omega) (fun i => f i.castSucc)
    unfold decodeSteps
    cases f ⟨n, Nat.lt_succ_self n⟩ with
    | none =>
      exact ⟨validStepsBelow_mono (Nat.le_succ n) hv_sub, hlen_sub.trans (Nat.le_succ n)⟩
    | some j =>
      exact ⟨⟨Nat.lt_succ_self n, hv_sub⟩, Nat.succ_le_succ hlen_sub⟩

/-- Every valid phase-exit step list below `n` (`n ≤ M_work`) is `decodeSteps M_work k n hn f` for some `f`. -/
theorem exists_decodeSteps_of_validStepsBelow (M_work k : ℕ) :
    ∀ (n : ℕ) (hn : n ≤ M_work) (steps : List (Fin M_work × Fin k)),
      ValidStepsBelow n steps →
      ∃ f : Fin n → Option (Fin k), decodeSteps M_work k n hn f = steps
  | 0, _, [], _ => ⟨fun i => Fin.elim0 i, rfl⟩
  | 0, _, (γ', _) :: _, hv => absurd hv.1 (Nat.not_lt_zero _)
  | n + 1, hn, [], _ => by
    obtain ⟨f₀, hf₀⟩ := exists_decodeSteps_of_validStepsBelow M_work k n (by omega) [] trivial
    let f : Fin (n + 1) → Option (Fin k) := fun i =>
      if h : i.1 < n then f₀ ⟨i.1, h⟩ else none
    refine ⟨f, ?_⟩
    have htop : f ⟨n, Nat.lt_succ_self n⟩ = none := by simp [f]
    have hcast : (fun i : Fin n => f i.castSucc) = f₀ := by
      funext i; simp [f, i.2]
    unfold decodeSteps
    rw [htop, hcast, hf₀]
  | n + 1, hn, (γ', j) :: rest, ⟨hγ_lt, hrest⟩ => by
    rcases eq_or_lt_of_le (Nat.le_of_lt_succ hγ_lt) with heq | hlt_n
    · obtain ⟨f₀, hf₀⟩ := exists_decodeSteps_of_validStepsBelow M_work k n (by omega) rest (heq ▸ hrest)
      let f : Fin (n + 1) → Option (Fin k) := fun i =>
        if h : i.1 < n then f₀ ⟨i.1, h⟩ else some j
      refine ⟨f, ?_⟩
      have htop : f ⟨n, Nat.lt_succ_self n⟩ = some j := by simp [f]
      have hcast : (fun i : Fin n => f i.castSucc) = f₀ := by
        funext i; simp [f, i.2]
      have hγ_eq : (⟨n, hn⟩ : Fin M_work) = γ' := Fin.ext heq.symm
      unfold decodeSteps
      rw [htop, hcast, hf₀, hγ_eq]
    · obtain ⟨f₀, hf₀⟩ := exists_decodeSteps_of_validStepsBelow M_work k n (by omega) ((γ', j) :: rest)
        ⟨hlt_n, hrest⟩
      let f : Fin (n + 1) → Option (Fin k) := fun i =>
        if h : i.1 < n then f₀ ⟨i.1, h⟩ else none
      refine ⟨f, ?_⟩
      have htop : f ⟨n, Nat.lt_succ_self n⟩ = none := by simp [f]
      have hcast : (fun i : Fin n => f i.castSucc) = f₀ := by
        funext i; simp [f, i.2]
      unfold decodeSteps
      rw [htop, hcast, hf₀]

/-- Finite index type of all phase-exit chains starting at any phase `γ₀ : Fin M_work`. -/
abbrev ChainIdx (M_work k : ℕ) : Type :=
  Σ γ₀ : Fin M_work, (Fin γ₀.1 → Option (Fin k))

/-- Exact combinatorial bound `|ChainIdx M_work k| ≤ (2k + 1) * (k + 1)^(2k)` whenever `M_work ≤ 2k + 1`. -/
theorem card_chainIdx_le {M_work k : ℕ} (hM : M_work ≤ 2 * k + 1) :
    Fintype.card (ChainIdx M_work k) ≤ (2 * k + 1) * (k + 1) ^ (2 * k) := by
  rw [Fintype.card_sigma]
  have hterm : ∀ γ₀ : Fin M_work,
      Fintype.card (Fin γ₀.1 → Option (Fin k)) ≤ (k + 1) ^ (2 * k) := by
    intro γ₀
    rw [Fintype.card_fun, Fintype.card_option, Fintype.card_fin, Fintype.card_fin]
    exact Nat.pow_le_pow_right (by omega) (by have := γ₀.2; omega)
  calc ∑ γ₀ : Fin M_work, Fintype.card (Fin γ₀.1 → Option (Fin k))
      ≤ ∑ _γ₀ : Fin M_work, (k + 1) ^ (2 * k) := sum_le_sum fun γ₀ _ => hterm γ₀
    _ = M_work * (k + 1) ^ (2 * k) := by simp
    _ ≤ (2 * k + 1) * (k + 1) ^ (2 * k) := Nat.mul_le_mul_right _ hM

/-- **Exact Zero-Jitter Phase-Exit Chain Threshold Pullback (`Step 3b of Theorem 5.3 (bridge)`):**
Pulls chronological block boundary `timeBlockBound T B_time s` back from the terminal phase along `steps`
to a single timestamp `ψ ∈ [θ_lo γ, θ_hi γ]`. -/
noncomputable def pullChainPsi {k M_work : ℕ} (τ₀ : Trace k) (T W B_time : ℕ)
    (θ_lo θ_hi : Fin M_work → ℕ) :
    Fin M_work → List (Fin M_work × Fin k) → ℕ → ℕ
  | γ, [], s => min (θ_hi γ) (max (θ_lo γ) (timeBlockBound T B_time s))
  | γ, (γ', j) :: rest, s =>
    if chainParity rest = false then
      (insert (θ_hi γ) ((Ico (θ_lo γ) (θ_hi γ)).filter fun u =>
        ∃ v ∈ Ico (θ_lo γ') (θ_hi γ'),
          IsNonCrossingLargeHop (τ₀.work j) T (2 * W) v u ∧
          v < pullChainPsi τ₀ T W B_time θ_lo θ_hi γ' rest s)).min'
        (insert_nonempty _ _)
    else
      (insert (θ_lo γ) (((Ico (θ_lo γ) (θ_hi γ)).filter fun u =>
        ∃ v ∈ Ico (θ_lo γ') (θ_hi γ'),
          IsNonCrossingLargeHop (τ₀.work j) T (2 * W) v u ∧
          pullChainPsi τ₀ T W B_time θ_lo θ_hi γ' rest s ≤ v).image (· + 1))).max'
        (insert_nonempty _ _)

/-- Set of all intermediate thresholds `ψ` encountered along `steps` at parameter `s`. -/
noncomputable def chainThresholds {k M_work : ℕ} (τ₀ : Trace k) (T W B_time : ℕ)
    (θ_lo θ_hi : Fin M_work → ℕ) :
    Fin M_work → List (Fin M_work × Fin k) → ℕ → Finset ℕ
  | γ, [], s => {pullChainPsi τ₀ T W B_time θ_lo θ_hi γ [] s}
  | γ, (γ', j) :: rest, s =>
    insert (pullChainPsi τ₀ T W B_time θ_lo θ_hi γ ((γ', j) :: rest) s)
      (chainThresholds τ₀ T W B_time θ_lo θ_hi γ' rest s)

theorem pullChainPsi_mem_chainThresholds {k M_work : ℕ} (τ₀ : Trace k) (T W B_time : ℕ)
    (θ_lo θ_hi : Fin M_work → ℕ) (γ : Fin M_work) (steps : List (Fin M_work × Fin k)) (s : ℕ) :
    pullChainPsi τ₀ T W B_time θ_lo θ_hi γ steps s ∈
      chainThresholds τ₀ T W B_time θ_lo θ_hi γ steps s := by
  cases steps with
  | nil => exact mem_singleton_self _
  | cons hd tl => exact mem_insert_self _ _

theorem card_chainThresholds_le {k M_work : ℕ} (τ₀ : Trace k) (T W B_time : ℕ)
    (θ_lo θ_hi : Fin M_work → ℕ) :
    ∀ (γ : Fin M_work) (steps : List (Fin M_work × Fin k)) (s : ℕ),
      (chainThresholds τ₀ T W B_time θ_lo θ_hi γ steps s).card ≤ steps.length + 1
  | γ, [], s => by simp [chainThresholds]
  | γ, (γ', j) :: rest, s => by
    unfold chainThresholds
    exact (card_insert_le _ _).trans
      (Nat.add_le_add_right (card_chainThresholds_le τ₀ T W B_time θ_lo θ_hi γ' rest s) 1)

/-- Bounds `[θ_lo γ, θ_hi γ]` and parity-alternating monotonicity/antitonicity of `pullChainPsi` in `s`. -/
theorem pullChainPsi_bounds_and_mono {k M_work : ℕ} (τ₀ : Trace k) (T W B_time : ℕ)
    (θ_lo θ_hi : Fin M_work → ℕ) (hlo_hi : ∀ c : Fin M_work, θ_lo c ≤ θ_hi c) :
    ∀ (steps : List (Fin M_work × Fin k)) (γ : Fin M_work),
      (∀ s : ℕ, θ_lo γ ≤ pullChainPsi τ₀ T W B_time θ_lo θ_hi γ steps s ∧
        pullChainPsi τ₀ T W B_time θ_lo θ_hi γ steps s ≤ θ_hi γ) ∧
      (∀ s₁ s₂ : ℕ, s₁ ≤ s₂ →
        if chainParity steps = false then
          pullChainPsi τ₀ T W B_time θ_lo θ_hi γ steps s₁ ≤
            pullChainPsi τ₀ T W B_time θ_lo θ_hi γ steps s₂
        else
          pullChainPsi τ₀ T W B_time θ_lo θ_hi γ steps s₂ ≤
            pullChainPsi τ₀ T W B_time θ_lo θ_hi γ steps s₁)
  | [], γ => by
    refine ⟨fun s => ?_, fun s₁ s₂ hs => ?_⟩
    · have := hlo_hi γ
      unfold pullChainPsi
      omega
    · have hbm := timeBlockBound_mono T B_time hs
      simp only [chainParity, ↓reduceIte, pullChainPsi]
      omega
  | (γ', j) :: rest, γ => by
    obtain ⟨_, ih_mono⟩ := pullChainPsi_bounds_and_mono τ₀ T W B_time θ_lo θ_hi hlo_hi rest γ'
    have hlo_le := hlo_hi γ
    refine ⟨fun s => ?_, fun s₁ s₂ hs => ?_⟩
    · rw [pullChainPsi]
      cases hpar : chainParity rest
      · simp only [↓reduceIte]
        refine ⟨Finset.le_min' _ (insert_nonempty _ _) _ fun x hx => ?_,
          Finset.min'_le _ _ (mem_insert_self _ _)⟩
        rcases mem_insert.mp hx with rfl | hflt
        · exact hlo_le
        · exact (mem_Ico.mp (mem_filter.mp hflt).1).1
      · simp only [Bool.true_eq_false, ↓reduceIte]
        refine ⟨Finset.le_max' _ _ (mem_insert_self _ _),
          Finset.max'_le _ (insert_nonempty _ _) _ fun x hx => ?_⟩
        rcases mem_insert.mp hx with rfl | himg
        · exact hlo_le
        · obtain ⟨u, hu_flt, rfl⟩ := mem_image.mp himg
          exact Nat.succ_le_of_lt (mem_Ico.mp (mem_filter.mp hu_flt).1).2
    · have ih_s := ih_mono s₁ s₂ hs
      cases hpar : chainParity rest
      · rw [hpar] at ih_s
        simp only [↓reduceIte] at ih_s
        have hpar_cur : chainParity ((γ', j) :: rest) = true := by simp [chainParity, hpar]
        rw [hpar_cur]
        simp only [Bool.true_eq_false, ↓reduceIte]
        rw [pullChainPsi, pullChainPsi]
        simp only [hpar, ↓reduceIte]
        refine Finset.le_min' _ (insert_nonempty _ _) _ fun x hx => Finset.min'_le _ x ?_
        rcases mem_insert.mp hx with rfl | hflt
        · exact mem_insert_self _ _
        · obtain ⟨hu_cur, v, hv_nxt, hnc, hv_lt⟩ := mem_filter.mp hflt
          exact mem_insert_of_mem (mem_filter.mpr ⟨hu_cur, v, hv_nxt, hnc, lt_of_lt_of_le hv_lt ih_s⟩)
      · rw [hpar] at ih_s
        simp only [Bool.true_eq_false, ↓reduceIte] at ih_s
        have hpar_cur : chainParity ((γ', j) :: rest) = false := by simp [chainParity, hpar]
        rw [hpar_cur]
        simp only [↓reduceIte]
        rw [pullChainPsi, pullChainPsi]
        simp only [hpar, Bool.true_eq_false, ↓reduceIte]
        refine Finset.max'_le _ (insert_nonempty _ _) _ fun x hx => Finset.le_max' _ x ?_
        rcases mem_insert.mp hx with rfl | himg
        · exact mem_insert_self _ _
        · obtain ⟨u, hu_flt, rfl⟩ := mem_image.mp himg
          obtain ⟨hu_cur, v, hv_nxt, hnc, hv_ge⟩ := mem_filter.mp hu_flt
          exact mem_insert_of_mem (mem_image_of_mem _ (mem_filter.mpr
            ⟨hu_cur, v, hv_nxt, hnc, ih_s.trans hv_ge⟩))

/-- **Exact Inter-Phase Pullback Equivalence (`Step 3c of Theorem 5.3 (bridge)`):**
Across any inter-phase step `(γ', j)` (`γ'.1 < γ.1`) and any `IsNonCrossingLargeHop` `(v, u)` between
`P_nxt` and `P_cur`, `chainPred` at `(γ, (γ', j) :: rest)` on `u` is **equivalent** to `chainPred` at
`(γ', rest)` on `v`! -/
theorem pullChainPsi_cons_iff {k M_work : ℕ} (τ₀ : Trace k) (T W B_time : ℕ)
    (θ_lo θ_hi : Fin M_work → ℕ)
    (hsep : ∀ c₁ c₂ : Fin M_work, c₁.1 < c₂.1 → θ_hi c₁ ≤ θ_lo c₂)
    {γ γ' : Fin M_work} (hlt : γ'.1 < γ.1) (j : Fin k)
    (rest : List (Fin M_work × Fin k)) (s : ℕ)
    {u v : ℕ} (hu : u ∈ Ico (θ_lo γ) (θ_hi γ)) (hv : v ∈ Ico (θ_lo γ') (θ_hi γ'))
    (hnc : IsNonCrossingLargeHop (τ₀.work j) T (2 * W) v u) :
    chainPred (chainParity ((γ', j) :: rest))
      (pullChainPsi τ₀ T W B_time θ_lo θ_hi γ ((γ', j) :: rest) s) u ↔
    chainPred (chainParity rest)
      (pullChainPsi τ₀ T W B_time θ_lo θ_hi γ' rest s) v := by
  have hsep_cur := hsep γ' γ hlt
  obtain ⟨hu_lo, hu_hi⟩ := mem_Ico.mp hu
  cases hpar : chainParity rest
  · have hpar_cur : chainParity ((γ', j) :: rest) = true := by simp [chainParity, hpar]
    conv_lhs => rw [hpar_cur]; unfold chainPred; rw [pullChainPsi]
    conv_rhs => unfold chainPred
    simp only [hpar, Bool.false_eq_true, ↓reduceIte]
    let ψ' := pullChainPsi τ₀ T W B_time θ_lo θ_hi γ' rest s
    let S := (Ico (θ_lo γ) (θ_hi γ)).filter fun u' =>
      ∃ v' ∈ Ico (θ_lo γ') (θ_hi γ'), IsNonCrossingLargeHop (τ₀.work j) T (2 * W) v' u' ∧ v' < ψ'
    change (insert (θ_hi γ) S).min' (insert_nonempty _ _) ≤ u ↔ v < ψ'
    constructor
    · intro hmin_le
      have hmem := (insert (θ_hi γ) S).min'_mem (insert_nonempty _ _)
      rcases mem_insert.mp hmem with heq_hi | hmem_S
      · omega
      · obtain ⟨hu₀, v₀, hv₀, hnc₀, hv₀_lt⟩ := mem_filter.mp hmem_S
        have hv_le_v₀ := interPhase_nonCrossing_antitone hsep_cur hu₀ hv₀ hnc₀ hu hv hnc hmin_le
        exact lt_of_le_of_lt hv_le_v₀ hv₀_lt
    · intro hv_lt
      exact Finset.min'_le _ u (mem_insert_of_mem (mem_filter.mpr ⟨hu, v, hv, hnc, hv_lt⟩))
  · have hpar_cur : chainParity ((γ', j) :: rest) = false := by simp [chainParity, hpar]
    conv_lhs => rw [hpar_cur]; unfold chainPred; rw [pullChainPsi]
    conv_rhs => unfold chainPred
    simp only [hpar, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
    let ψ' := pullChainPsi τ₀ T W B_time θ_lo θ_hi γ' rest s
    let S := (Ico (θ_lo γ) (θ_hi γ)).filter fun u' =>
      ∃ v' ∈ Ico (θ_lo γ') (θ_hi γ'), IsNonCrossingLargeHop (τ₀.work j) T (2 * W) v' u' ∧ ψ' ≤ v'
    change u < (insert (θ_lo γ) (S.image (· + 1))).max' (insert_nonempty _ _) ↔ ψ' ≤ v
    constructor
    · intro hu_lt_max
      have hmem := (insert (θ_lo γ) (S.image (· + 1))).max'_mem (insert_nonempty _ _)
      rcases mem_insert.mp hmem with heq_lo | himg
      · omega
      · obtain ⟨u₀, hu₀_S, heq_u₀⟩ := mem_image.mp himg
        obtain ⟨hu₀, v₀, hv₀, hnc₀, hv₀_ge⟩ := mem_filter.mp hu₀_S
        have hu_le_u₀ : u ≤ u₀ := by omega
        have hv₀_le_v := interPhase_nonCrossing_antitone hsep_cur hu hv hnc hu₀ hv₀ hnc₀ hu_le_u₀
        exact hv₀_ge.trans hv₀_le_v
    · intro hv_ge
      have hmem_img : u + 1 ∈ insert (θ_lo γ) (S.image (· + 1)) :=
        mem_insert_of_mem (mem_image_of_mem (· + 1) (mem_filter.mpr ⟨hu, v, hv, hnc, hv_ge⟩))
      have hle := Finset.le_max' _ (u + 1) hmem_img
      omega

end PhaseExitChainPullback

/-! ## §4. Theorem 5.3 (bridge) (The Genie-Based Bridge Theorem & All-Machines Expansion Corollaries) -/

section CrossingBridgeTheorem

open scoped Classical

/-- Number of valid phase-exit chains `m₀(k) = (2k + 1)(k + 1)^(2k)`. -/
def bridgeChainCap (k : ℕ) : ℕ :=
  (2 * k + 1) * (k + 1) ^ (2 * k)

theorem bridgeChainCap_pos (k : ℕ) : 1 ≤ bridgeChainCap k := by
  unfold bridgeChainCap
  exact Nat.mul_pos (by omega) (Nat.pow_pos (by omega))

/-- Total guarded threshold count `N_thresh(k, C, α)`. -/
noncomputable def bridgeThreshCount (k : ℕ) (C α : ℝ) : ℕ :=
  (2 * k + 1) + bridgeChainCap k * (2 * k + 1) * (⌈8 * (bridgeChainCap k : ℝ) * C / α⌉₊ + 1)

/-- Exceptional ancestor-row multiplier `E₀(k, D, C, α) = (k + 2)^D * N_thresh * (5k + 1)`. -/
noncomputable def bridgeGenieFactor (k D : ℕ) (C α : ℝ) : ℕ :=
  (k + 2) ^ D * bridgeThreshCount k C α * (5 * k + 1)

/-- **Depth-independent bridge density constant `ρ₀(k, C, α)`:**
`ρ₀(k, C, α) = 1 / (3 * C(m₀ + 2⌈24C/α⌉, m₀)) > 0` where `m₀ = (2k + 1)(k + 1)^(2k)`. -/
noncomputable def genieBridge_rho0 (k : ℕ) (C α : ℝ) : ℝ :=
  timePullbackRhoMin (bridgeChainCap k) C α

theorem genieBridge_rho0_pos (k : ℕ) (C α : ℝ) : 0 < genieBridge_rho0 k C α :=
  timePullbackRhoMin_pos (bridgeChainCap k) C α

theorem genieBridge_rho0_le_third (k : ℕ) (C α : ℝ) :
    genieBridge_rho0 k C α ≤ 1 / 3 := by
  unfold genieBridge_rho0 timePullbackRhoMin
  have hch_ge_1 : (1 : ℝ) ≤ (Nat.choose (bridgeChainCap k + 2 * ⌈24 * C / α⌉₊) (bridgeChainCap k) : ℝ) := by
    exact_mod_cast Nat.choose_pos (Nat.le_add_right _ _)
  have hden : (3 : ℝ) ≤ 3 * (Nat.choose (bridgeChainCap k + 2 * ⌈24 * C / α⌉₊) (bridgeChainCap k) : ℝ) := by
    linarith
  exact one_div_le_one_div_of_le (by positivity) hden

/-- Explicit macroscopic-crossing separator expansion constant `c_E(M, C, α) = ρ₀(M.k, C, α) / (2 * valueWidth M) > 0`. -/
noncomputable def cE_genie (M : TM) (C α : ℝ) : ℝ :=
  genieBridge_rho0 M.k C α / (2 * (valueWidth M : ℝ))

theorem cE_genie_pos (M : TM) (C α : ℝ) : 0 < cE_genie M C α := by
  unfold cE_genie
  have hvw : (2 : ℝ) ≤ (valueWidth M : ℝ) := by exact_mod_cast two_le_valueWidth M
  have hrho := genieBridge_rho0_pos M.k C α
  positivity

/-- Fixed genie depth `D_E(M, C, α)` used in Theorem X. -/
noncomputable def genieBridgeDepth (M : TM) (C α : ℝ) : ℕ :=
  genieDepth M.k (valueWidth M) C (α * genieBridge_rho0 M.k C α / 4)

/-- Reduction from arbitrary depth-`∞` Menger vertex cuts (`allowing root hits B ∩ u₀(V₀) ≠ ∅`) to
`IsBallPathSeparator` on `V₀' = {q ∈ V₀ : u₀(q) ∉ B}` (`Step 3 of Theorem X`). -/
theorem isBallPathSeparator_of_isMengerVertexCut {k T D d b : ℕ} (τ₀ : Trace k)
    (hlen : (appendList τ₀ T).length = d * d * b)
    (V₀ : Finset (Fin (d * d * b))) (Dst B : Finset ℕ)
    (hmenger : IsMengerVertexCut τ₀.work T
      (V₀.image fun q => appendTime τ₀ T (tposOf d b q).1) Dst B) :
    let V₀' := V₀.filter fun q => appendTime τ₀ T (tposOf d b q).1 ∉ B
    V₀.card ≤ V₀'.card + B.card ∧
      IsBallPathSeparator τ₀ T D d b V₀' Dst B := by
  intro V₀'
  let u₀_of : Fin (d * d * b) → ℕ := fun q => appendTime τ₀ T (tposOf d b q).1
  have hinj := appendTime_tposOf_injective τ₀ hlen
  refine ⟨?_, ?_⟩
  · let V_hit := V₀.filter fun q => u₀_of q ∈ B
    have hcov : V₀ ⊆ V₀' ∪ V_hit := by
      intro q hq
      by_cases hB : u₀_of q ∈ B
      · exact mem_union_right _ (mem_filter.mpr ⟨hq, hB⟩)
      · exact mem_union_left _ (mem_filter.mpr ⟨hq, hB⟩)
    have hhit_le : V_hit.card ≤ B.card := by
      have hsub : V_hit.image u₀_of ⊆ B := by
        intro x hx
        obtain ⟨q, hq, rfl⟩ := mem_image.mp hx
        exact (mem_filter.mp hq).2
      calc V_hit.card = (V_hit.image u₀_of).card := (card_image_of_injective V_hit hinj).symm
        _ ≤ B.card := card_le_card hsub
    calc V₀.card ≤ (V₀' ∪ V_hit).card := card_le_card hcov
      _ ≤ V₀'.card + V_hit.card := card_union_le _ _
      _ ≤ V₀'.card + B.card := Nat.add_le_add_left hhit_le _
  · intro q hq' ρ hdep hfreeB _ s hs_ρ hs_Dst
    obtain ⟨hqV, hq_notB⟩ := mem_filter.mp hq'
    obtain ⟨ρ₁, _, hdep₁, hfree₁, hlast₁, _, _, _, _, _⟩ :=
      depPath_split_at_mem (Γ_genie := B) ρ (u₀_of q) s hdep hfreeB
        (List.mem_cons_of_mem _ hs_ρ)
    have hsrc : u₀_of q ∈ V₀.image u₀_of := mem_image_of_mem u₀_of hqV
    obtain ⟨v, hv_mem, hvB⟩ := hmenger ρ₁ (u₀_of q) hsrc hdep₁ (hlast₁.symm ▸ hs_Dst)
    rcases List.mem_cons.mp hv_mem with rfl | hv_tail
    · exact hq_notB hvB
    · exact hfree₁ v hv_tail hvB

end CrossingBridgeTheorem
end NativeRelations
