import NativeRelations.JitterMacroBank
import BoundedNesting.CorM
import MergeDepth.LinearCrux

/-!
# Scale-Gap Pigeonhole for Bounded Owner Load and Few Scale Windows (Theorem Q)

Proves Theorem Q (`zeroFreeHead_qWindow_excludes`, `zeroFreeHead_entries_qWindow_excludes`,
`zeroFreeHead_qWindow_oblivious_excludes`): no linear-time transposer has a heavy trace on which
every work head has bounded owner load and all family heights lie in boundedly many logarithmic
windows, whatever the input head does.
-/

set_option autoImplicit false

namespace NativeRelations

open Filter Finset Transpose Transpose.Tape Transpose.Tape.Impl BoundedNesting SourceCovers MergeDepth
open scoped BigOperators Topology

/-! ## §1. Constant-`1` Max-Hop Jitter Equivalence -/

/-- Every long hop `(p, u)` of `y` strictly inside `[lo, hi)` (`lo ≤ p < u < hi`) has spatial
excursion `|y t - y p| ≤ H` at all interior times `t ∈ (p, u)`. -/
def HopExcursionLEOn (y : ℕ → ℤ) (lo hi H : ℕ) : Prop :=
  ∀ p u : ℕ, lo ≤ p → u < hi → IsHop y hi p u → ∀ t : ℕ, p < t → t < u → |y t - y p| ≤ (H : ℤ)

/-- **Same-side complete-hop containment**: every hop `η` belonging to a `BoundedNesting` complete
family `F` (with `owners xs`) has interior excursion at most `famd xs (allHops xs T) (owners xs) F`. -/
theorem hop_excursion_le_famd {k T : ℕ} {xs : Fin k → ℕ → ℤ} (hx : ∀ h, IsWalk (xs h))
    (F : Keys xs (allHops xs T) (owners xs)) {η : Fin k × ℕ × ℕ}
    (hη : η ∈ fam xs (allHops xs T) (owners xs) F.1) {t : ℕ} (ht1 : η.2.1 < t) (ht2 : t < η.2.2) :
    |xs η.1 t - xs η.1 η.2.1| ≤ (famd xs (allHops xs T) (owners xs) F : ℤ) := by
  have hH : ∀ η' ∈ allHops xs T, IsHop (xs η'.1) T η'.2.1 η'.2.2 :=
    fun _ h => mem_allHops.mp h
  have hown : ∀ η' ∈ allHops xs T, η'.2.1 < owners xs η' ∧ owners xs η' < η'.2.2 := by
    intro η' h
    have hs := hopOwner_spec (xs η'.1) (hH η' h).1
    exact ⟨hs.1, hs.2.1⟩
  obtain ⟨hηH, hh1, hh2, hh3⟩ := mem_fam.mp hη
  have hhop := hH η hηH
  have hab := sw_above hx hhop t ht1 ht2
  have hmax := (isOwner_hopOwner hx hhop).max t ht1 ht2
  have hcell := (fam_cell_mem hx hH hown F hη).1
  have hpos_d := (fam_owner hx hH hown F).2.2
  rw [← abs_sw_sub xs η.1 (side xs η) η.2.1 t, abs_of_pos (by linarith)]
  change hopOwner (xs η.1) η.2.1 η.2.2 = F.1.2.2 at hh3
  rw [hh3] at hmax
  rw [hh2, hh1] at hmax ⊢
  unfold famd
  have hnn : 0 ≤ sw xs F.1.1 F.1.2.1 F.1.2.2 - sw xs F.1.1 F.1.2.1 (famP xs (allHops xs T) (owners xs) F) :=
    by linarith
  omega

/-! ## §2. Span Partition and Family Height Accounting from `OwnerLoadLE` -/

theorem hasSpanColoring_mono_colors {k T N₁ N₂ : ℕ} {xs : Fin k → ℕ → ℤ}
    {K : Finset (ActualFamily xs T)} (h : HasSpanColoring K N₁) (hle : N₁ ≤ N₂) :
    HasSpanColoring K N₂ := by
  obtain ⟨color, hb, hd⟩ := h
  exact ⟨color, fun q hq => (hb q hq).trans_le hle, hd⟩

/-- Owner-load at most `ℓ` on `allHops xs T` yields an explicit `(2 * k * ℓ)`-class span partition
of all complete families (`BoundedNesting.famData_valid` + `Fam.Valid.unique_span`). -/
theorem hasSpanColoring_of_ownerLoadLE {k T ℓ : ℕ} {xs : Fin k → ℕ → ℤ}
    (hx : ∀ h, IsWalk (xs h))
    (hload : OwnerLoadLE xs (allHops xs T) (owners xs) ℓ) :
    HasSpanColoring (univ : Finset (ActualFamily xs T)) (2 * k * ℓ) := by
  have hH : ∀ η ∈ allHops xs T, IsHop (xs η.1) T η.2.1 η.2.2 :=
    fun _ h => mem_allHops.mp h
  have hown : ∀ η ∈ allHops xs T, η.2.1 < actualOwner xs η ∧ actualOwner xs η < η.2.2 := by
    intro η h
    have hs := hopOwner_spec (xs η.1) (hH η h).1
    exact ⟨hs.1, hs.2.1⟩
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
  · refine ⟨fun _ => 0, fun F _ => ?_, fun F _ _ _ _ _ => ?_⟩
    · exfalso
      have hpos := famDepth_pos F
      have hle := famDepth_le hx hH hown hload F
      omega
    · exfalso
      have hpos := famDepth_pos F
      have hle := famDepth_le hx hH hown hload F
      omega
  · have hA := famData_valid (T := T) hx hH hown hℓ hload
    refine ⟨fun F => vcode xs (allHops xs T) (actualOwner xs) ℓ F,
      fun F _ => vcode_lt F (famDepth_le hx hH hown hload F),
      fun F _ F' _ hne hcol => ?_⟩
    have hv : (famData xs (allHops xs T) (actualOwner xs) ℓ hℓ).vh F =
        (famData xs (allHops xs T) (actualOwner xs) ℓ hℓ).vh F' := by
      apply Fin.ext
      simp only [famData]
      rw [Nat.mod_eq_of_lt (vcode_lt F (famDepth_le hx hH hown hload F)),
        Nat.mod_eq_of_lt (vcode_lt F' (famDepth_le hx hH hown hload F'))]
      exact hcol
    rw [Finset.disjoint_left]
    intro e heF heF'
    have h1 := (mem_family_edges_iff F e).mp heF
    have h2 := (mem_family_edges_iff F' e).mp heF'
    exact hA.unique_span hne hv h1 h2

/-- Owner-load at most `ℓ` bounds twice the sum of all complete-family heights by
`(2 * k * ℓ) * (T - 1)` (`BoundedNesting.Fam.Valid.sum_d_le` summed across virtual heads). -/
theorem two_mul_sum_famd_le_of_ownerLoadLE {k T ℓ : ℕ} {xs : Fin k → ℕ → ℤ}
    (hx : ∀ h, IsWalk (xs h))
    (hload : OwnerLoadLE xs (allHops xs T) (owners xs) ℓ) :
    2 * ∑ F : ActualFamily xs T, famd xs (allHops xs T) (actualOwner xs) F ≤
      (2 * k * ℓ) * (T - 1) := by
  classical
  have hH : ∀ η ∈ allHops xs T, IsHop (xs η.1) T η.2.1 η.2.2 :=
    fun _ h => mem_allHops.mp h
  have hown : ∀ η ∈ allHops xs T, η.2.1 < actualOwner xs η ∧ actualOwner xs η < η.2.2 := by
    intro η h
    have hs := hopOwner_spec (xs η.1) (hH η h).1
    exact ⟨hs.1, hs.2.1⟩
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
  · have hemp : (univ : Finset (ActualFamily xs T)) = ∅ := by
      ext F
      simp only [mem_univ, notMem_empty, iff_false]
      have hpos := famDepth_pos F
      have hle := famDepth_le hx hH hown hload F
      omega
    simp [hemp]
  · set A := famData xs (allHops xs T) (actualOwner xs) ℓ hℓ
    have hA : A.Valid T := famData_valid (T := T) hx hH hown hℓ hload
    change 2 * ∑ F ∈ (univ : Finset (ActualFamily xs T)), A.d F ≤ (2 * k * ℓ) * (T - 1)
    rw [← sum_fiberwise univ A.vh A.d, mul_sum]
    calc ∑ v : Fin (2 * k * ℓ), 2 * ∑ F ∈ univ.filter (fun F => A.vh F = v), A.d F
        ≤ ∑ _v : Fin (2 * k * ℓ), (T - 1) := sum_le_sum fun v _ => hA.sum_d_le v
      _ = (2 * k * ℓ) * (T - 1) := by simp

/-! ## §3. Theorem 9.7 (Theorem Q): Unconditional Zero-Free-Head `q`-Window Exclusion -/

/-- **Theorem 9.7 (Theorem Q)**:
Uniform over all `M : TM` with `M.k ≤ k` and `valueWidth M ≤ β`, there exist `ε > 0` and `d₀ : ℕ`
such that for all `η < ε` and all `d ≥ d₀`, `M` cannot both transpose at dimension `d` within
`c (L + 1)` steps and possess a trace `τ₀` of probability `≥ 2^{-η L}` whose work walks have
owner-load at most `ℓ` and complete-family bands covered by at most `q` windows of width `h`
(`BoundedNesting.BandsCovered`). Both the window centres and the input walk `τ₀.input` may vary
arbitrarily with `d` and `τ₀`. -/
theorem zeroFreeHead_qWindow_excludes (c β : ℝ) (k ℓ q h : ℕ) :
    ∃ ε > (0 : ℝ), ∃ d₀ : ℕ,
      ∀ M : TM, M.k ≤ k → (valueWidth M : ℝ) ≤ β → ∀ η < ε, ∀ d ≥ d₀,
        ¬ (TransposesAt M d c ∧
          ∃ τ₀ : Trace M.k,
            (2 : ℝ) ^ (-η * inputLength d) ≤ traceProb M (inputLength d) τ₀ ∧
            OwnerLoadLE τ₀.work (allHops τ₀.work τ₀.haltTime) (owners τ₀.work) ℓ ∧
            BandsCovered τ₀.work τ₀.haltTime h q) := by
  classical
  set N : ℕ := 2 * k * max ℓ 1
  -- Extract raw constants `(ε_raw Q, d₀_raw Q)` from `MergeDepth.low_adaptivity_a_exists`
  let hLA := fun Q : ℕ => MergeDepth.low_adaptivity_a_exists c β N Q
  let ε_raw : ℕ → ℝ := fun Q => Classical.choose (hLA Q)
  have hLA_spec : ∀ Q : ℕ, 0 < ε_raw Q ∧ ∃ d₀ : ℕ,
      ∀ M : TM, (valueWidth M : ℝ) ≤ β → ∀ η < ε_raw Q, ∀ d ≥ d₀,
        ¬ (TransposesAt M d c ∧
          ∃ τ₀ : Trace M.k, (2 : ℝ) ^ (-η * inputLength d) ≤ traceProb M (inputLength d) τ₀ ∧
            HasSpanColoring (univ : Finset (ActualFamily τ₀.work τ₀.haltTime)) N ∧
            (univ.filter fun F : ActualFamily τ₀.work τ₀.haltTime =>
              ε_raw Q * inputLength d < (F.hops.card : ℝ)).card ≤ Q) :=
    fun Q => Classical.choose_spec (hLA Q)
  let d₀_raw : ℕ → ℕ := fun Q => Classical.choose (hLA_spec Q).2
  have hd₀_spec : ∀ (Q : ℕ) (M : TM), (valueWidth M : ℝ) ≤ β → ∀ η < ε_raw Q, ∀ d ≥ d₀_raw Q,
      ¬ (TransposesAt M d c ∧
        ∃ τ₀ : Trace M.k, (2 : ℝ) ^ (-η * inputLength d) ≤ traceProb M (inputLength d) τ₀ ∧
          HasSpanColoring (univ : Finset (ActualFamily τ₀.work τ₀.haltTime)) N ∧
          (univ.filter fun F : ActualFamily τ₀.work τ₀.haltTime =>
            ε_raw Q * inputLength d < (F.hops.card : ℝ)).card ≤ Q) :=
    fun Q => Classical.choose_spec (hLA_spec Q).2
  -- Running minimum `ε_tilde Q = min_{j ≤ Q} ε_raw j`
  let ε_tilde : ℕ → ℝ := fun Q =>
    ((range (Q + 1)).image ε_raw).min' (by simp)
  have hε_tilde_pos : ∀ Q : ℕ, 0 < ε_tilde Q := by
    intro Q
    obtain ⟨j, _, heq⟩ := mem_image.mp (min'_mem ((range (Q + 1)).image ε_raw) (by simp))
    dsimp only [ε_tilde]
    rw [← heq]
    exact (hLA_spec j).1
  have hε_tilde_le_raw : ∀ Q : ℕ, ε_tilde Q ≤ ε_raw Q := by
    intro Q
    exact min'_le _ _ (mem_image.mpr ⟨Q, mem_range.mpr (Nat.lt_succ_self Q), rfl⟩)
  have hε_tilde_anti : Antitone ε_tilde := by
    intro Q₁ Q₂ h12
    refine Finset.le_min' _ _ _ fun x hx => ?_
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hx
    exact min'_le _ _ (mem_image.mpr ⟨j, mem_range.mpr (by have := mem_range.mp hj; omega), rfl⟩)
  -- Recursive scale thresholds `Q_seq 0 = 0`, `Q_seq (m + 1) = ⌊2 N (max c 0) 2^(h+1) / ε_tilde (Q_seq m)⌋₊ + 1`
  let num : ℝ := 2 * (N : ℝ) * max c 0 * (2 : ℝ) ^ (h + 1)
  have hnum_nn : 0 ≤ num := by positivity
  let Q_seq : ℕ → ℕ := fun m =>
    Nat.rec 0 (fun _ Q_prev => ⌊num / ε_tilde Q_prev⌋₊ + 1) m
  have hQ_zero : Q_seq 0 = 0 := rfl
  have hQ_succ : ∀ m : ℕ, Q_seq (m + 1) = ⌊num / ε_tilde (Q_seq m)⌋₊ + 1 := fun _ => rfl
  have hQ_mono_step : ∀ m : ℕ, Q_seq m ≤ Q_seq (m + 1) := by
    intro m
    induction m with
    | zero => exact Nat.zero_le _
    | succ m ih =>
      refine Nat.add_le_add_right (Nat.floor_mono ?_) 1
      exact div_le_div_of_nonneg_left hnum_nn (hε_tilde_pos _) (hε_tilde_anti ih)
  have hQ_mono : Monotone Q_seq := monotone_nat_of_le_succ hQ_mono_step
  set ε_star : ℝ := ε_tilde (Q_seq q)
  set D_star : ℕ := max 1 (((range (q + 1)).image (fun m => d₀_raw (Q_seq m))).max' (by simp))
  refine ⟨ε_star, hε_tilde_pos (Q_seq q), D_star, fun M hMk hβ η hη d hd => ?_⟩
  rintro ⟨htr, τ₀, hprob, hload, hbands⟩
  have hd_pos : 0 < d := lt_of_lt_of_le Nat.one_pos ((le_max_left _ _).trans hd)
  have hL_pos : 0 < inputLength d := inputLength_pos hd_pos
  have hL_posR : (0 : ℝ) < inputLength d := by exact_mod_cast hL_pos
  -- Span coloring for `N = 2 * k * max ℓ 1`
  have hload' : OwnerLoadLE τ₀.work (allHops τ₀.work τ₀.haltTime) (owners τ₀.work) (max ℓ 1) :=
    hload.mono (le_max_left ℓ 1)
  have hN_M : HasSpanColoring (univ : Finset (ActualFamily τ₀.work τ₀.haltTime))
      (2 * M.k * max ℓ 1) :=
    hasSpanColoring_of_ownerLoadLE τ₀.work_isWalk hload'
  have hN : HasSpanColoring (univ : Finset (ActualFamily τ₀.work τ₀.haltTime)) N :=
    hasSpanColoring_mono_colors hN_M (Nat.mul_le_mul_right (max ℓ 1) (Nat.mul_le_mul_left 2 hMk))
  -- Handle `k = 0` (`ActualFamily` empty) directly
  rcases Nat.eq_zero_or_pos k with rfl | hk_pos
  · have hMk0 : M.k = 0 := Nat.eq_zero_of_le_zero hMk
    have hemp : (univ.filter fun F : ActualFamily τ₀.work τ₀.haltTime =>
        ε_raw (Q_seq 0) * inputLength d < (F.hops.card : ℝ)).card ≤ Q_seq 0 := by
      have h0 : (univ : Finset (ActualFamily τ₀.work τ₀.haltTime)) = ∅ := by
        ext F
        simp only [mem_univ, notMem_empty, iff_false]
        exact Fin.elim0 (hMk0 ▸ F.1.1)
      simp [h0, hQ_zero]
    have hη0 : η < ε_raw (Q_seq 0) :=
      hη.trans_le ((hε_tilde_anti (hQ_mono (Nat.zero_le q))).trans (hε_tilde_le_raw (Q_seq 0)))
    have hd0 : d₀_raw (Q_seq 0) ≤ d := by
      have hmem : d₀_raw (Q_seq 0) ∈ (range (q + 1)).image (fun m => d₀_raw (Q_seq m)) :=
        mem_image.mpr ⟨0, mem_range.mpr (Nat.zero_lt_succ q), rfl⟩
      exact (le_max' _ _ hmem).trans ((le_max_right _ _).trans hd)
    exact hd₀_spec (Q_seq 0) M hβ η hη0 d hd0 ⟨htr, τ₀, hprob, hN, hemp⟩
  -- Now `0 < k`, so `0 < N`. Extract `0 < τ₀.haltTime ≤ 2 * c * L` and `0 < c`.
  have hN_pos : 0 < N := Nat.mul_pos (Nat.mul_pos two_pos hk_pos) (lt_max_of_lt_right Nat.one_pos)
  have hN_posR : (0 : ℝ) < N := by exact_mod_cast hN_pos
  obtain ⟨_, hne_fib⟩ := fibre_facts hL_pos hprob
  obtain ⟨X₀, hX₀⟩ := hne_fib
  obtain ⟨hT_floor, happ_len⟩ := fibre_haltTime hX₀ (htr.transposesInput X₀)
  have hT_pos : 0 < τ₀.haltTime :=
    prefix_pos hd_pos (one_le_entryBits d) happ_len.ge
  have hT_le : (τ₀.haltTime : ℝ) ≤ 2 * c * (inputLength d : ℝ) :=
    runtime_le hL_pos hT_pos hT_floor
  have hc_pos : 0 < c := by
    have hT1 : (1 : ℝ) ≤ τ₀.haltTime := by exact_mod_cast hT_pos
    by_contra hc_le
    push Not at hc_le
    have : 2 * c * (inputLength d : ℝ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) hL_posR.le
    linarith
  have hmax_c : max c 0 = c := max_eq_left hc_pos.le
  -- Sum of complete-family heights `< N * c * L`
  have hsum_nat : 2 * ∑ F : ActualFamily τ₀.work τ₀.haltTime,
      famd τ₀.work (allHops τ₀.work τ₀.haltTime) (actualOwner τ₀.work) F ≤
        N * (τ₀.haltTime - 1) := by
    calc 2 * ∑ F : ActualFamily τ₀.work τ₀.haltTime,
          famd τ₀.work (allHops τ₀.work τ₀.haltTime) (actualOwner τ₀.work) F
        ≤ (2 * M.k * max ℓ 1) * (τ₀.haltTime - 1) :=
          two_mul_sum_famd_le_of_ownerLoadLE τ₀.work_isWalk hload'
      _ ≤ N * (τ₀.haltTime - 1) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hMk))
  have hsum_real : (∑ F : ActualFamily τ₀.work τ₀.haltTime,
      (famd τ₀.work (allHops τ₀.work τ₀.haltTime) (actualOwner τ₀.work) F : ℝ)) <
        (N : ℝ) * c * (inputLength d : ℝ) := by
    have hsum_cast : 2 * (∑ F : ActualFamily τ₀.work τ₀.haltTime,
        (famd τ₀.work (allHops τ₀.work τ₀.haltTime) (actualOwner τ₀.work) F : ℝ)) ≤
          (N : ℝ) * ((τ₀.haltTime - 1 : ℕ) : ℝ) := by exact_mod_cast hsum_nat
    have hsub_lt : ((τ₀.haltTime - 1 : ℕ) : ℝ) < (τ₀.haltTime : ℝ) := by
      exact_mod_cast Nat.sub_lt hT_pos Nat.one_pos
    have hN_lt : (N : ℝ) * ((τ₀.haltTime - 1 : ℕ) : ℝ) < (N : ℝ) * (2 * c * (inputLength d : ℝ)) :=
      mul_lt_mul_of_pos_left (hsub_lt.trans_le hT_le) hN_posR
    linarith
  -- Disjoint scale-gap pigeonhole across `m ∈ range (q + 1)`
  obtain ⟨B, hBq, hB_cov⟩ := hbands
  let InGapBad : ℕ → ℕ → Prop := fun m b =>
    ε_tilde (Q_seq m) * (inputLength d : ℝ) < ((2 ^ (b + h + 1) : ℕ) : ℝ) ∧
      ((2 ^ b : ℕ) : ℝ) ≤ (N : ℝ) * c * (inputLength d : ℝ) / (Nat.cast (Q_seq m) + 1)
  have hGap_disj : ∀ {m m' b : ℕ}, m < m' → InGapBad m b → ¬ InGapBad m' b := by
    intro m m' b hmm' hm1 hm2
    have hQm_le : Q_seq (m + 1) ≤ Q_seq m' := hQ_mono (Nat.succ_le_of_lt hmm')
    have hQm_leR : (Nat.cast (Q_seq (m + 1)) : ℝ) + 1 ≤ Nat.cast (Q_seq m') + 1 := by
      exact_mod_cast Nat.add_le_add_right hQm_le 1
    have hNCL_pos : 0 < (N : ℝ) * c * (inputLength d : ℝ) := by positivity
    have hb_le : ((2 ^ b : ℕ) : ℝ) ≤
        (N : ℝ) * c * (inputLength d : ℝ) / (Nat.cast (Q_seq (m + 1)) + 1) :=
      hm2.2.trans (div_le_div_of_nonneg_left hNCL_pos.le (by positivity) hQm_leR)
    have hfloor_lt : num / ε_tilde (Q_seq m) < Nat.cast (Q_seq (m + 1)) := by
      rw [hQ_succ]
      push_cast
      exact Nat.lt_floor_add_one _
    have hεm_pos := hε_tilde_pos (Q_seq m)
    have hQ1_pos : (0 : ℝ) < Nat.cast (Q_seq (m + 1)) + 1 := by positivity
    have hnum_eq : num = 2 * (N : ℝ) * c * (2 : ℝ) ^ (h + 1) := by
      dsimp [num]; rw [hmax_c]
    have hmul1 : 2 * (N : ℝ) * c * (2 : ℝ) ^ (h + 1) <
        ε_tilde (Q_seq m) * (Nat.cast (Q_seq (m + 1)) + 1) := by
      have := (div_lt_iff₀ hεm_pos).mp (hfloor_lt.trans (lt_add_one _))
      linarith [hnum_eq]
    have h2pow_split : ((2 ^ (b + h + 1) : ℕ) : ℝ) = (2 : ℝ) ^ (h + 1) * ((2 ^ b : ℕ) : ℝ) := by
      push_cast
      ring
    have hprod_le : (2 : ℝ) ^ (h + 1) * ((2 ^ b : ℕ) : ℝ) ≤
        (2 : ℝ) ^ (h + 1) * ((N : ℝ) * c * (inputLength d : ℝ) / (Nat.cast (Q_seq (m + 1)) + 1)) :=
      mul_le_mul_of_nonneg_left hb_le (by positivity)
    have hprod_lt : (2 : ℝ) ^ (h + 1) * ((N : ℝ) * c * (inputLength d : ℝ) / (Nat.cast (Q_seq (m + 1)) + 1)) <
        ε_tilde (Q_seq m) * (inputLength d : ℝ) := by
      rw [← mul_div_assoc, div_lt_iff₀ hQ1_pos]
      have hmulL := mul_lt_mul_of_pos_right hmul1 hL_posR
      have hpos_lhs : 0 < (N : ℝ) * c * (2 : ℝ) ^ (h + 1) * (inputLength d : ℝ) := by positivity
      linarith
    linarith [hm1.1]
  let badM : Finset ℕ := B.biUnion (fun b => (range (q + 1)).filter (fun m => InGapBad m b))
  have hbadM_lt : badM.card < (range (q + 1)).card := by
    have hcard_each : ∀ b ∈ B, ((range (q + 1)).filter (fun m => InGapBad m b)).card ≤ 1 := by
      intro b _
      refine card_le_one.mpr fun m₁ hm₁ m₂ hm₂ => ?_
      have h1 := (mem_filter.mp hm₁).2
      have h2 := (mem_filter.mp hm₂).2
      rcases lt_trichotomy m₁ m₂ with hlt | heq | hgt
      · exact absurd h2 (hGap_disj hlt h1)
      · exact heq
      · exact absurd h1 (hGap_disj hgt h2)
    calc badM.card ≤ ∑ b ∈ B, ((range (q + 1)).filter (fun m => InGapBad m b)).card := card_biUnion_le
      _ ≤ ∑ _b ∈ B, 1 := sum_le_sum hcard_each
      _ = B.card := by simp
      _ ≤ q := hBq
      _ < (range (q + 1)).card := by simp
  obtain ⟨m_star, hm_star_mem, hm_star_good⟩ := exists_mem_notMem_of_card_lt_card hbadM_lt
  have hm_star_le : m_star ≤ q := Nat.lt_succ_iff.mp (mem_range.mp hm_star_mem)
  have hno_bad : ∀ b ∈ B, ¬ InGapBad m_star b := by
    intro b hb hbad
    exact hm_star_good (mem_biUnion.mpr ⟨b, hb, mem_filter.mpr ⟨hm_star_mem, hbad⟩⟩)
  -- Bound the number of families with `> ε_raw (Q_seq m_star) * L` hops by `Q_seq m_star`
  set E_big := univ.filter fun F : ActualFamily τ₀.work τ₀.haltTime =>
    ε_raw (Q_seq m_star) * (inputLength d : ℝ) < (F.hops.card : ℝ)
  have hH_all : ∀ η' ∈ allHops τ₀.work τ₀.haltTime,
      IsHop (τ₀.work η'.1) τ₀.haltTime η'.2.1 η'.2.2 :=
    fun _ h => mem_allHops.mp h
  have hown_all : ∀ η' ∈ allHops τ₀.work τ₀.haltTime,
      η'.2.1 < actualOwner τ₀.work η' ∧ actualOwner τ₀.work η' < η'.2.2 := by
    intro η' h
    have hs := hopOwner_spec (τ₀.work η'.1) (hH_all η' h).1
    exact ⟨hs.1, hs.2.1⟩
  have hA_val := famData_valid (T := τ₀.haltTime) τ₀.work_isWalk hH_all hown_all
    (lt_max_of_lt_right Nat.one_pos : 0 < max ℓ 1) hload'
  have hE_lower : ∀ F ∈ E_big,
      (N : ℝ) * c * (inputLength d : ℝ) / (Nat.cast (Q_seq m_star) + 1) <
        (famd τ₀.work (allHops τ₀.work τ₀.haltTime) (actualOwner τ₀.work) F : ℝ) := by
    intro F hF
    have hF_gt : ε_raw (Q_seq m_star) * (inputLength d : ℝ) < (F.hops.card : ℝ) :=
      (mem_filter.mp hF).2
    have hF_gt_tilde : ε_tilde (Q_seq m_star) * (inputLength d : ℝ) < (F.hops.card : ℝ) :=
      (mul_le_mul_of_nonneg_right (hε_tilde_le_raw (Q_seq m_star)) hL_posR.le).trans_lt hF_gt
    set dF : ℕ := famd τ₀.work (allHops τ₀.work τ₀.haltTime) (actualOwner τ₀.work) F
    have hcard_le_dF : F.hops.card ≤ dF := card_fam_le τ₀.work_isWalk hH_all hown_all F
    have hdF_pos : 1 ≤ dF := hA_val.d_pos F
    obtain ⟨b, hbB, hb_lo, hb_hi⟩ := hB_cov F
    change b ≤ lam dF at hb_lo
    change lam dF ≤ b + h at hb_hi
    have hdF_lt : dF < 2 ^ (b + h + 1) := by
      calc dF < 2 ^ (lam dF + 1) := Nat.lt_pow_succ_log_self (by norm_num) dF
        _ ≤ 2 ^ (b + h + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hdF_ge : 2 ^ b ≤ dF := by
      calc 2 ^ b ≤ 2 ^ lam dF := Nat.pow_le_pow_right (by norm_num) hb_lo
        _ ≤ dF := Nat.pow_log_le_self 2 (by omega)
    have h1_bad : ε_tilde (Q_seq m_star) * (inputLength d : ℝ) < ((2 ^ (b + h + 1) : ℕ) : ℝ) := by
      have hcast1 : (F.hops.card : ℝ) ≤ (dF : ℝ) := by exact_mod_cast hcard_le_dF
      have hcast2 : (dF : ℝ) < ((2 ^ (b + h + 1) : ℕ) : ℝ) := by exact_mod_cast hdF_lt
      linarith
    have hnot2 : ¬ ((2 ^ b : ℕ) : ℝ) ≤
        (N : ℝ) * c * (inputLength d : ℝ) / (Nat.cast (Q_seq m_star) + 1) :=
      fun h2 => hno_bad b hbB ⟨h1_bad, h2⟩
    push Not at hnot2
    exact hnot2.trans_le (by exact_mod_cast hdF_ge)
  have hE_card_le : E_big.card ≤ Q_seq m_star := by
    have hNCL_pos : 0 < (N : ℝ) * c * (inputLength d : ℝ) := by positivity
    have hQ_pos : (0 : ℝ) < Nat.cast (Q_seq m_star) + 1 := by positivity
    have hsum_E : (E_big.card : ℝ) *
        ((N : ℝ) * c * (inputLength d : ℝ) / (Nat.cast (Q_seq m_star) + 1)) ≤
          ∑ F ∈ E_big, (famd τ₀.work (allHops τ₀.work τ₀.haltTime) (actualOwner τ₀.work) F : ℝ) := by
      calc (E_big.card : ℝ) * ((N : ℝ) * c * (inputLength d : ℝ) / (Nat.cast (Q_seq m_star) + 1))
          = ∑ _F ∈ E_big, ((N : ℝ) * c * (inputLength d : ℝ) / (Nat.cast (Q_seq m_star) + 1)) := by
            rw [sum_const, nsmul_eq_mul]
        _ ≤ ∑ F ∈ E_big, (famd τ₀.work (allHops τ₀.work τ₀.haltTime) (actualOwner τ₀.work) F : ℝ) :=
            sum_le_sum fun F hF => (hE_lower F hF).le
    have hsum_sub : (∑ F ∈ E_big,
        (famd τ₀.work (allHops τ₀.work τ₀.haltTime) (actualOwner τ₀.work) F : ℝ)) ≤
          ∑ F : ActualFamily τ₀.work τ₀.haltTime,
            (famd τ₀.work (allHops τ₀.work τ₀.haltTime) (actualOwner τ₀.work) F : ℝ) :=
      sum_le_sum_of_subset_of_nonneg (subset_univ E_big) (fun _ _ _ => Nat.cast_nonneg _)
    have hlt_prod : (E_big.card : ℝ) *
        ((N : ℝ) * c * (inputLength d : ℝ) / (Nat.cast (Q_seq m_star) + 1)) <
          (N : ℝ) * c * (inputLength d : ℝ) :=
      (hsum_E.trans hsum_sub).trans_lt hsum_real
    have hlt_card : (E_big.card : ℝ) < Nat.cast (Q_seq m_star) + 1 := by
      rw [← mul_div_assoc, div_lt_iff₀ hQ_pos] at hlt_prod
      exact lt_of_mul_lt_mul_left (by linarith) hNCL_pos.le
    have hnat_lt : E_big.card < Q_seq m_star + 1 := by exact_mod_cast hlt_card
    omega
  -- Contradiction with `MergeDepth.low_adaptivity_a_exists` at `Q_seq m_star`
  have hη_m : η < ε_raw (Q_seq m_star) :=
    hη.trans_le ((hε_tilde_anti (hQ_mono hm_star_le)).trans (hε_tilde_le_raw (Q_seq m_star)))
  have hd_m : d₀_raw (Q_seq m_star) ≤ d := by
    have hmem : d₀_raw (Q_seq m_star) ∈ (range (q + 1)).image (fun m => d₀_raw (Q_seq m)) :=
      mem_image.mpr ⟨m_star, hm_star_mem, rfl⟩
    exact (le_max' _ _ hmem).trans ((le_max_right _ _).trans hd)
  exact hd₀_spec (Q_seq m_star) M hβ η hη_m d hd_m ⟨htr, τ₀, hprob, hN, hE_card_le⟩

/-- **Bounded-entry specialization of Theorem 9.7 (Theorem Q)**: if every work-tape cell is entered at most
`V` times (`BoundedNesting.ownerLoad_le_of_entries`, giving owner-load `≤ 2V - 1`) and work-family
bands lie in `q` windows of width `h`, transposition fails at low adaptivity (`η < ε`). -/
theorem zeroFreeHead_entries_qWindow_excludes (c β : ℝ) (k V q h : ℕ) :
    ∃ ε > (0 : ℝ), ∃ d₀ : ℕ,
      ∀ M : TM, M.k ≤ k → (valueWidth M : ℝ) ≤ β → ∀ η < ε, ∀ d ≥ d₀,
        ¬ (TransposesAt M d c ∧
          ∃ τ₀ : Trace M.k,
            (2 : ℝ) ^ (-η * inputLength d) ≤ traceProb M (inputLength d) τ₀ ∧
            (∀ (j : Fin M.k) (cell : ℤ),
              (entries (τ₀.work j) cell (τ₀.haltTime - 1)).card ≤ V) ∧
            BandsCovered τ₀.work τ₀.haltTime h q) := by
  obtain ⟨ε, hε, d₀, hexcl⟩ := zeroFreeHead_qWindow_excludes c β k (2 * V - 1) q h
  refine ⟨ε, hε, d₀, fun M hMk hβ η hη d hd ⟨htr, τ₀, hprob, hent, hbands⟩ => ?_⟩
  have hload : OwnerLoadLE τ₀.work (allHops τ₀.work τ₀.haltTime) (owners τ₀.work) (2 * V - 1) :=
    ownerLoad_le_of_entries τ₀.work_isWalk (fun _ h => mem_allHops.mp h) (fun _ _ => hent _ _)
  exact hexcl M hMk hβ η hη d hd ⟨htr, τ₀, hprob, hload, hbands⟩

/-- **Oblivious specialization of Theorem 9.7 (Theorem Q)** (the unconditional zero-free-work-head case of
Paper 8's `Corollary M-machine`): for any oblivious machine `M` (`ObliviousLinTime`), bounded
work-head owner-load `≤ ℓ` and `q`-window family bands exclude linear-time transposition for all
`d ≥ d₀`, with no assumption on the input walk. -/
theorem zeroFreeHead_qWindow_oblivious_excludes (c β : ℝ) (k ℓ q h : ℕ) :
    ∃ d₀ : ℕ,
      ∀ M : TM, M.k ≤ k → (valueWidth M : ℝ) ≤ β → ∀ d ≥ d₀, ∀ T : ℕ,
        ¬ (ObliviousLinTime M d (entryBits d) c T ∧
          OwnerLoadLE (traceAt M (d * d * entryBits d)).work
            (allHops (traceAt M (d * d * entryBits d)).work T)
            (owners (traceAt M (d * d * entryBits d)).work) ℓ ∧
          BandsCovered (traceAt M (d * d * entryBits d)).work T h q) := by
  obtain ⟨ε, hε, d₀, hexcl⟩ := zeroFreeHead_qWindow_excludes c β k ℓ q h
  refine ⟨max d₀ 1, fun M hMk hβ d hd T ⟨⟨hobl, hT, htr⟩, hload, hbands⟩ => ?_⟩
  set L : ℕ := inputLength d
  have hL_eq : d * d * entryBits d = L := rfl
  -- `TransposesAt M d c`
  have htrAt : TransposesAt M d c := by
    intro A
    obtain ⟨s, hs⟩ := htr A
    obtain ⟨s', _, hhalt_s', hout_s'⟩ := (computesWithin_iff _ _).mp hs
    have hhalt_T : HaltsAt M (encode d (entryBits d) A) T :=
      hobl.1 _ (length_encode d (entryBits d) A)
    have hs'T : s' = T := haltsAt_unique hhalt_s' hhalt_T
    rw [hs'T] at hout_s'
    exact (computesWithin_iff _ _).mpr
      ⟨T, Nat.le_floor hT, hhalt_T, hout_s'⟩
  -- Every input of length `L` has exact full trace `traceAt M L`, with `haltTime = T`
  set τ₀ : Trace M.k := traceAt M L
  have hhalt_zero : HaltsAt M (List.ofFn fun _ : Fin L => false) T :=
    hobl.1 _ List.length_ofFn
  have hτ₀_halts : τ₀.HaltsAt T := (haltsAt_iff_trace T).mp hhalt_zero
  have hT_eq : τ₀.haltTime = T :=
    (τ₀.haltsAt_haltTime ⟨T, hτ₀_halts.2⟩).unique hτ₀_halts
  have hfib_univ : fibre M L τ₀ = univ := by
    ext X
    simp only [mem_fibre, mem_univ, iff_true]
    have hf := followsTrace_of_obliviousOn (hL_eq ▸ hobl) (fun _ : Fin L => false) X
    have hhalt_X : HaltsAt M (List.ofFn X) T := hobl.1 _ List.length_ofFn
    funext t
    rcases lt_or_ge t T with ht | ht
    · exact hf t ht
    · have hnone1 : transAt M (List.ofFn X) t = none :=
        transAt_of_le_of_none hhalt_X.2 ht
      have hnone2 : transAt M (List.ofFn fun _ : Fin L => false) t = none :=
        transAt_of_le_of_none hhalt_zero.2 ht
      show trace M (List.ofFn X) t = trace M (List.ofFn fun _ : Fin L => false) t
      rw [(trace_eq_none_iff t).mpr hnone1, (trace_eq_none_iff t).mpr hnone2]
  have hprob1 : (2 : ℝ) ^ (-(0 : ℝ) * L) ≤ traceProb M L τ₀ := by
    rw [neg_zero, zero_mul, Real.rpow_zero]
    unfold traceProb
    rw [hfib_univ, card_univ]
    simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat]
    exact le_of_eq (div_self (by positivity)).symm
  have hload' : OwnerLoadLE τ₀.work (allHops τ₀.work τ₀.haltTime) (owners τ₀.work) ℓ := by
    rw [hT_eq]
    exact hload
  have hbands' : BandsCovered τ₀.work τ₀.haltTime h q := by
    rw [hT_eq]
    exact hbands
  exact hexcl M hMk hβ 0 hε d (le_of_max_le_left hd) ⟨htrAt, τ₀, hprob1, hload', hbands'⟩

end NativeRelations
