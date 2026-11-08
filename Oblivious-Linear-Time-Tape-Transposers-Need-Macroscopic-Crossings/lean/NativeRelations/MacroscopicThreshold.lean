import NativeRelations.ScaleProfile

/-!
# First-Form Time Pullback, Bridge, Dichotomy, and Macroscopic Crossings

Proves the uniform-block-cut first form of the time pullback (`timePullback_blockCut_mais`), the
depth-`D` genie-based bridge (`bridge_exists_isAcyclicIn_crossingLowerH`), the depth-`D` trace
dichotomies (`linearTimeTrace_crossingLowerGT2H_ballSep_dichotomy`,
`linearTimeTrace_crossingLowerGT2H_menger_dichotomy`), and the first-form macroscopic crossing
bound (`obliviousLinTime_macroscopicCrossingLowers_menger_lb_genie`).
-/

set_option autoImplicit false

namespace NativeRelations

open Filter Finset Transpose Transpose.Tape BoundedNesting MergeDepth MotionDepthCodes
  BoundedStackDepth TapeStorageRates
open scoped BigOperators

/-! ## §1. General-`Z_bad` Arbitrary-Trace Time-Pullback `MAIS` (Theorem 5.1 (time pullback) General Budget) -/

section GeneralZBadTimePullback

/-- `(m₀, C, α)`-only dimension threshold for the general-`Z_bad` form of Theorem 5.1 (time pullback)
(completely independent of `D`, `E₀`, and `H`). -/
noncomputable def timePullback_gen_d0 (m₀ : ℕ) (C α : ℝ) : ℕ :=
  max (⌈24 * C / α⌉₊ * ⌈8 * (m₀ : ℝ) * C / α⌉₊)
    ⌈12 * (m₀ : ℝ) * (2 * (⌈8 * (m₀ : ℝ) * C / α⌉₊ : ℝ) + 3) / α⌉₊

/-- **General-`Z_bad` Minimal-Clause Arbitrary-Trace Time-Pullback `MAIS` Theorem:**
Strengthens the linear-budget time pullback (`CrossingBridge.lean`) by replacing `Z_bad.card ≤ E₀ * (d * b)` with
the macroscopic budget `(Z_bad.card : ℝ) ≤ (V₀.card : ℝ) / 12`, keeping `W = d * b` strictly in the
row-kinematic and time-block boundary terms (`d ≥ timePullback_gen_d0 m₀ C α`). -/
theorem timePullback_blockCut_mais {ι : Type*} [Fintype ι] [DecidableEq ι]
    {k T d b D m₀ : ℕ} {C α : ℝ} (τ₀ : Trace k)
    (hd : 1 ≤ d) (hb : 1 ≤ b) (hm₀ : 1 ≤ m₀) (hC : 1 ≤ C) (hα0 : 0 < α)
    (hι : Fintype.card ι ≤ m₀)
    (hlen : (appendList τ₀ T).length = d * d * b)
    (hT : (T : ℝ) ≤ C * (((d * d * b : ℕ) : ℝ) + 1))
    (V₀ Z_bad : Finset (Fin (d * d * b))) (B : Finset ℕ)
    (hV₀ : α * ((d * d * b : ℕ) : ℝ) ≤ (V₀.card : ℝ))
    (hZ_bad : (Z_bad.card : ℝ) ≤ (V₀.card : ℝ) / 12)
    (hd_thresh : timePullback_gen_d0 m₀ C α ≤ d)
    (ξ : ι → ℕ → ℕ)
    (hξ_mono : ∀ ν : ι, ∀ s₁ s₂ : ℕ, s₁ ≤ s₂ → s₂ ≤ ⌈8 * (m₀ : ℝ) * C / α⌉₊ → ξ ν s₁ ≤ ξ ν s₂)
    (π_perm : ι → Fin ⌈8 * (m₀ : ℝ) * C / α⌉₊ → Fin ⌈8 * (m₀ : ℝ) * C / α⌉₊)
    (hπ_inj : ∀ ν : ι, Function.Injective (π_perm ν))
    (hpull : ∀ q ∈ V₀ \ Z_bad, ∀ p ∈ V₀, ∀ ρ : List ℕ,
      ρ.length ≤ D →
      IsDepPath τ₀.work T (appendTime τ₀ T (tposOf d b q).1 :: ρ) →
      LinNet.GFree B (appendTime τ₀ T (tposOf d b q).1 :: ρ) →
      τ₀.input ((appendTime τ₀ T (tposOf d b q).1 :: ρ).getLastD
        (appendTime τ₀ T (tposOf d b q).1)) = (p.1 : ℤ) →
      ∀ β : Fin ⌈8 * (m₀ : ℝ) * C / α⌉₊,
        (appendTime τ₀ T (tposOf d b q).1 :: ρ).getLastD
          (appendTime τ₀ T (tposOf d b q).1) ∈ timeBlock T ⌈8 * (m₀ : ℝ) * C / α⌉₊ β →
        ∃ ν : ι, appendTime τ₀ T (tposOf d b q).1 ∈
          Ico (ξ ν (π_perm ν β).1) (ξ ν ((π_perm ν β).1 + 1))) :
    ∃ U : Finset (Fin (d * d * b)),
      U ⊆ V₀ ∧
      HalfRate.IsAcyclicIn (ballAvoidSystem τ₀ T D B d b) U ∧
      timePullbackRhoMin m₀ C α * (V₀.card : ℝ) ≤ (U.card : ℝ) := by
  let K_row := ⌈24 * C / α⌉₊
  let B_time := ⌈8 * (m₀ : ℝ) * C / α⌉₊
  let W := d * b
  let L := d * d * b
  have hL_pos : (1 : ℝ) ≤ (L : ℝ) := by
    exact_mod_cast Nat.mul_pos (Nat.mul_pos hd hd) hb
  have hm₀_r : (1 : ℝ) ≤ (m₀ : ℝ) := by exact_mod_cast hm₀
  have hK_pos : 1 ≤ K_row := Nat.ceil_pos.mpr (by positivity)
  have hB_pos : 1 ≤ B_time := Nat.ceil_pos.mpr (by positivity)
  have hd_big : K_row * B_time ≤ d := (le_max_left _ _).trans hd_thresh
  have hd_err : ⌈12 * (m₀ : ℝ) * (2 * (B_time : ℝ) + 3) / α⌉₊ ≤ d :=
    (le_max_right _ _).trans hd_thresh
  obtain ⟨U, N_surv, hUV₀, hacyc, hV₀_nat, hU_div⟩ :=
    exists_isAcyclicIn_of_timePullback_core τ₀ hd hb hK_pos hB_pos hd_big hι hlen
      V₀ Z_bad B ξ hξ_mono π_perm hπ_inj hpull
  refine ⟨U, hUV₀, hacyc, ?_⟩
  have hT_2CL : (T : ℝ) ≤ 2 * C * (L : ℝ) := by
    have hCL : C ≤ C * (L : ℝ) := by simpa using mul_le_mul_of_nonneg_left hL_pos (by linarith)
    change (T : ℝ) ≤ 2 * C * ((d * d * b : ℕ) : ℝ)
    change C ≤ C * ((d * d * b : ℕ) : ℝ) at hCL
    linarith
  -- Bound `3 * T / K_row ≤ |V₀| / 4`.
  have hK_ge : 24 * C / α ≤ (K_row : ℝ) := Nat.le_ceil _
  have hK_r_pos : (0 : ℝ) < (K_row : ℝ) := by exact_mod_cast hK_pos
  have hdiv_K_nat : ((3 * T / K_row : ℕ) : ℝ) * (K_row : ℝ) ≤ 3 * (T : ℝ) := by
    have h := Nat.div_mul_le_self (3 * T) K_row
    have hr : (((3 * T / K_row) * K_row : ℕ) : ℝ) ≤ ((3 * T : ℕ) : ℝ) := by exact_mod_cast h
    simpa [Nat.cast_mul] using hr
  have h3T_K : ((3 * T / K_row : ℕ) : ℝ) ≤ (V₀.card : ℝ) / 4 := by
    have h1 : 24 * C ≤ (K_row : ℝ) * α := (div_le_iff₀ hα0).mp hK_ge
    have h2 : 4 * (((3 * T / K_row : ℕ) : ℝ) * (K_row : ℝ)) ≤ 12 * (T : ℝ) := by linarith
    have h3 : 12 * (T : ℝ) ≤ 24 * C * (L : ℝ) := by linarith
    have h4 : 24 * C * (L : ℝ) ≤ ((K_row : ℝ) * α) * (L : ℝ) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have h5 : α * (L : ℝ) * (K_row : ℝ) ≤ (V₀.card : ℝ) * (K_row : ℝ) :=
      mul_le_mul_of_nonneg_right hV₀ (by positivity)
    have h5' : ((K_row : ℝ) * α) * (L : ℝ) = α * (L : ℝ) * (K_row : ℝ) := by ring
    have h6 : (4 * ((3 * T / K_row : ℕ) : ℝ)) * (K_row : ℝ) ≤ (V₀.card : ℝ) * (K_row : ℝ) := by
      linarith
    have h7 := le_of_mul_le_mul_right h6 hK_r_pos
    linarith
  -- Bound `m₀ * (T / B_time) ≤ |V₀| / 4`.
  have hB_ge : 8 * (m₀ : ℝ) * C / α ≤ (B_time : ℝ) := Nat.le_ceil _
  have hB_r_pos : (0 : ℝ) < (B_time : ℝ) := by exact_mod_cast hB_pos
  have hdiv_B_nat : ((T / B_time : ℕ) : ℝ) * (B_time : ℝ) ≤ (T : ℝ) := by
    have h := Nat.div_mul_le_self T B_time
    have hr : (((T / B_time) * B_time : ℕ) : ℝ) ≤ (T : ℝ) := by exact_mod_cast h
    simpa [Nat.cast_mul] using hr
  have hmT_B : (m₀ : ℝ) * ((T / B_time : ℕ) : ℝ) ≤ (V₀.card : ℝ) / 4 := by
    have h1 : 8 * (m₀ : ℝ) * C ≤ (B_time : ℝ) * α := (div_le_iff₀ hα0).mp hB_ge
    have h2 : (4 * (m₀ : ℝ)) * (((T / B_time : ℕ) : ℝ) * (B_time : ℝ)) ≤
        (4 * (m₀ : ℝ)) * (T : ℝ) :=
      mul_le_mul_of_nonneg_left hdiv_B_nat (by positivity)
    have h3 : (4 * (m₀ : ℝ)) * (T : ℝ) ≤ 8 * (m₀ : ℝ) * C * (L : ℝ) := by nlinarith
    have h4 : 8 * (m₀ : ℝ) * C * (L : ℝ) ≤ ((B_time : ℝ) * α) * (L : ℝ) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have h5 : α * (L : ℝ) * (B_time : ℝ) ≤ (V₀.card : ℝ) * (B_time : ℝ) :=
      mul_le_mul_of_nonneg_right hV₀ (by positivity)
    have h5' : ((B_time : ℝ) * α) * (L : ℝ) = α * (L : ℝ) * (B_time : ℝ) := by ring
    have h2' : (4 * (m₀ : ℝ)) * (((T / B_time : ℕ) : ℝ) * (B_time : ℝ)) =
        (4 * ((m₀ : ℝ) * ((T / B_time : ℕ) : ℝ))) * (B_time : ℝ) := by ring
    have h6 : (4 * ((m₀ : ℝ) * ((T / B_time : ℕ) : ℝ))) * (B_time : ℝ) ≤
        (V₀.card : ℝ) * (B_time : ℝ) := by linarith
    have h7 := le_of_mul_le_mul_right h6 hB_r_pos
    linarith
  -- Bound boundary error `m₀ * (2 * B_time + 2) * W ≤ |V₀| / 12`.
  have herr_ge : 12 * (m₀ : ℝ) * (2 * (B_time : ℝ) + 3) / α ≤ (d : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hd_err)
  have herr_mul : 12 * (m₀ : ℝ) * (2 * (B_time : ℝ) + 3) ≤ (d : ℝ) * α :=
    (div_le_iff₀ hα0).mp herr_ge
  have hW_eq_L : (d : ℝ) * ((W : ℕ) : ℝ) = (L : ℝ) := by
    dsimp [W, L]; push_cast; ring
  have herr_W : 12 * ((m₀ : ℝ) * (2 * (B_time : ℝ) + 2) * ((W : ℕ) : ℝ)) ≤
      (V₀.card : ℝ) := by
    have hstep1 : 12 * (m₀ : ℝ) * (2 * (B_time : ℝ) + 2) ≤
        12 * (m₀ : ℝ) * (2 * (B_time : ℝ) + 3) := by nlinarith
    have hstep2 : (12 * (m₀ : ℝ) * (2 * (B_time : ℝ) + 2)) * ((W : ℕ) : ℝ) ≤
        ((d : ℝ) * α) * ((W : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_right (hstep1.trans herr_mul) (by positivity)
    have hstep3 : ((d : ℝ) * α) * ((W : ℕ) : ℝ) = α * ((d * d * b : ℕ) : ℝ) := by
      calc ((d : ℝ) * α) * ((W : ℕ) : ℝ) = α * ((d : ℝ) * ((W : ℕ) : ℝ)) := by ring
        _ = α * (L : ℝ) := by rw [hW_eq_L]
        _ = α * ((d * d * b : ℕ) : ℝ) := rfl
    linarith
  have hN_ge : (V₀.card : ℝ) / 3 ≤ (N_surv : ℝ) := by
    have hV_r : (V₀.card : ℝ) ≤
        (N_surv : ℝ) + (Z_bad.card : ℝ) + ((3 * T / K_row : ℕ) : ℝ) +
          (m₀ : ℝ) * ((T / B_time : ℕ) : ℝ) +
          (m₀ : ℝ) * (2 * (B_time : ℝ) + 2) * ((W : ℕ) : ℝ) := by
      have hr : (V₀.card : ℝ) ≤
          ((N_surv + Z_bad.card + 3 * T / K_row +
            m₀ * (T / B_time) + m₀ * (2 * B_time + 2) * (d * b) : ℕ) : ℝ) := by
        exact_mod_cast hV₀_nat
      change (V₀.card : ℝ) ≤
        ((N_surv + Z_bad.card + 3 * T / K_row +
          m₀ * (T / B_time) + m₀ * (2 * B_time + 2) * W : ℕ) : ℝ) at hr
      push_cast at hr
      linarith
    linarith
  have hch_pos : (0 : ℝ) < (Nat.choose (m₀ + 2 * K_row) m₀ : ℝ) := by
    exact_mod_cast Nat.choose_pos (Nat.le_add_right _ _)
  have hdiv_le : ((V₀.card : ℝ) / 3) / (Nat.choose (m₀ + 2 * K_row) m₀ : ℝ) ≤
      (N_surv : ℝ) / (Nat.choose (m₀ + 2 * K_row) m₀ : ℝ) :=
    div_le_div_of_nonneg_right hN_ge hch_pos.le
  have hrho_eq : timePullbackRhoMin m₀ C α * (V₀.card : ℝ) =
      ((V₀.card : ℝ) / 3) / (Nat.choose (m₀ + 2 * K_row) m₀ : ℝ) := by
    unfold timePullbackRhoMin
    dsimp [K_row]
    ring
  exact hrho_eq.le.trans (hdiv_le.trans hU_div)

end GeneralZBadTimePullback

/-! ## §2. Arbitrary Hop-Threshold Bridge up to `θ_E(k, D, C, α) * L` -/

section MacroscopicThresholdBridge

open scoped Classical

/-- Generalized Clause `(E1)` at arbitrary hop threshold `2 * H` (`decoupled from W = d * b`). -/
def ClauseE1H {k : ℕ} (τ₀ : Trace k) (T D d b H ηInv L_cap : ℕ)
    (V₀ : Finset (Fin (d * d * b))) (B : Finset ℕ) : Prop :=
  ∀ q ∈ V₀, ∀ ρ : List ℕ,
    IsDepPath τ₀.work T (appendTime τ₀ T (tposOf d b q).1 :: ρ) →
    LinNet.GFree B (appendTime τ₀ T (tposOf d b q).1 :: ρ) → ρ.length ≤ D →
    ∀ (j : Fin k) (v u : ℕ), v ∈ ρ → IsHop (τ₀.work j) T v u →
      HasHopExcursionGTAt (τ₀.work j) (2 * H) v u →
      (∀ t ∈ Ioo v u, |τ₀.work j t - τ₀.work j v| ≤ ((L_cap / ηInv : ℕ) : ℤ)) ∧
      (∀ p' u' : ℕ, IsHop (τ₀.work j) T p' u' →
        HasHopExcursionGTAt (τ₀.work j) (2 * H) p' u' → HopsCross v u p' u' →
        ∀ t ∈ Ioo p' u', |τ₀.work j t - τ₀.work j p'| ≤ ((L_cap / ηInv : ℕ) : ℤ))

/-- **Unconditional Vacuity of `ClauseE1H` for Uncapped `L_cap = T, ηInv = 1` at Every Threshold `H`:** -/
theorem clauseE1H_uncapped {k : ℕ} (τ₀ : Trace k) (T D d b H : ℕ)
    (V₀ : Finset (Fin (d * d * b))) (B : Finset ℕ) :
    ClauseE1H τ₀ T D d b H 1 T V₀ B := by
  intro _ _ _ _ _ _ j v u _ hhop _
  have h1 : ∀ {p' u' : ℕ}, IsHop (τ₀.work j) T p' u' →
      ∀ t ∈ Ioo p' u', |τ₀.work j t - τ₀.work j p'| ≤ ((T / 1 : ℕ) : ℤ) := by
    intro p' u' hh t ht
    rw [Nat.div_one]
    exact hop_excursion_le_T τ₀ j hh t ht
  exact ⟨h1 hhop, fun _ _ hhop' _ _ => h1 hhop'⟩

/-- **Target-Shrinking Antitonicity:**
Raising the excursion threshold `H₁ ≤ H₂` shrinks `crossingLowerEtaSteps`, so any separator or Menger
expansion lower bound into `crossingLowerEtaSteps τ₀ T H₂ ηInv L_cap` strictly strengthens `H₁`. -/
theorem crossingLowerEtaSteps_anti_H {k : ℕ} (τ₀ : Trace k) (T : ℕ) {H₁ H₂ : ℕ} (hle : H₁ ≤ H₂)
    (ηInv L_cap : ℕ) :
    crossingLowerEtaSteps τ₀ T H₂ ηInv L_cap ⊆ crossingLowerEtaSteps τ₀ T H₁ ηInv L_cap := by
  have hle_z : ((2 * H₁ : ℕ) : ℤ) ≤ ((2 * H₂ : ℕ) : ℤ) := by exact_mod_cast Nat.mul_le_mul_left 2 hle
  have hband_mono : ∀ {y : ℕ → ℤ} {p u : ℕ},
      HopInBand y T (2 * H₂) (L_cap / ηInv) p u → HopInBand y T (2 * H₁) (L_cap / ηInv) p u := by
    rintro y p u ⟨hhop, ⟨t, ht, hgt⟩, hhi⟩
    exact ⟨hhop, ⟨t, ht, lt_of_le_of_lt hle_z hgt⟩, hhi⟩
  intro v hv
  obtain ⟨hvT, j, u, hb, p', u', hb', hcr⟩ := mem_filter.mp hv
  exact mem_filter.mpr ⟨hvT, j, u, hband_mono hb, p', u', hband_mono hb', hcr⟩

private theorem depStep_of_split_isDepPath_H {k : ℕ} {xs : Fin k → ℕ → ℤ} {T : ℕ} :
    ∀ (l₁ : List ℕ) {u v : ℕ} (l₂ : List ℕ),
      IsDepPath xs T (l₁ ++ u :: v :: l₂) → DepStep xs T u v
  | [], _, _, _, hdep => hdep.1
  | [_], _, _, _, hdep => hdep.2.1
  | _ :: b :: rest, _, _, l₂, hdep => depStep_of_split_isDepPath_H (b :: rest) l₂ hdep.2

private theorem mem_tail_of_split_cons_H {α : Type*} {head u v : α} :
    ∀ (l₁ l₂ ρ : List α), head :: ρ = l₁ ++ u :: v :: l₂ → v ∈ ρ
  | [], _, ρ, heq => by
    injection heq with _ htail
    rw [htail]
    exact List.mem_cons_self
  | _ :: rest, _, ρ, heq => by
    injection heq with _ htail
    rw [htail]
    exact List.mem_append_right rest (List.mem_cons_of_mem u List.mem_cons_self)

/-- **`B`-Avoiding Step-Dichotomy at Arbitrary Hop Threshold `2 * H`:**
Separating `V₀` from `crossingLowerEtaSteps τ₀ T H ηInv L_cap` under `ClauseE1H` collapses every
dependency edge along any `B`-avoiding `D`-path from `V₀` into `u = v + 1`, a `≤ 2H` hop, or a
non-crossing `> 2H` hop straddling one of at most `2` cut timestamps `(θ_pos j, θ_neg j)` per tape. -/
theorem depPath_nonCrossing_dichotomy_of_isBallPathSeparator_crossingLowerH {k : ℕ} (τ₀ : Trace k)
    (T D d b H ηInv L_cap : ℕ) (V₀ : Finset (Fin (d * d * b))) (B : Finset ℕ)
    (hsep : IsBallPathSeparator τ₀ T D d b V₀ (crossingLowerEtaSteps τ₀ T H ηInv L_cap) B)
    (hE1 : ClauseE1H τ₀ T D d b H ηInv L_cap V₀ B) :
    ∃ θ_pos θ_neg : Fin k → ℕ, (∀ j, θ_pos j ≤ T ∧ θ_neg j ≤ T) ∧
      ∀ q ∈ V₀, ∀ ρ l₁ l₂ : List ℕ, ∀ u v : ℕ,
        IsDepPath τ₀.work T (appendTime τ₀ T (tposOf d b q).1 :: ρ) →
        LinNet.GFree B (appendTime τ₀ T (tposOf d b q).1 :: ρ) → ρ.length ≤ D →
        appendTime τ₀ T (tposOf d b q).1 :: ρ = l₁ ++ u :: v :: l₂ →
        u = v + 1 ∨
        (∃ j : Fin k, IsHop (τ₀.work j) T v u ∧
          ∀ t ∈ Ioo v u, |τ₀.work j t - τ₀.work j v| ≤ ((2 * H : ℕ) : ℤ)) ∨
        (∃ j : Fin k, IsNonCrossingLargeHop (τ₀.work j) T (2 * H) v u ∧
          ((v < θ_pos j ∧ θ_pos j ≤ u) ∨ (v < θ_neg j ∧ θ_neg j ≤ u))) := by
  have hex_j : ∀ j : Fin k, ∃ tp tn : ℕ, tp ≤ T ∧ tn ≤ T ∧
      ∀ p u : ℕ, IsNonCrossingLargeHop (τ₀.work j) T (2 * H) p u →
        (p < tp ∧ tp ≤ u) ∨ (p < tn ∧ tn ≤ u) :=
    fun j => exists_two_cuts_covering_nonCrossingLargeHops (τ₀.work_isWalk j) T (2 * H)
  choose θ_pos θ_neg hθ_spec using hex_j
  refine ⟨θ_pos, θ_neg, fun j => ⟨(hθ_spec j).1, (hθ_spec j).2.1⟩, ?_⟩
  intro q hq ρ l₁ l₂ u v hdep hfreeB hlen hsplit
  have hstep : DepStep τ₀.work T u v :=
    depStep_of_split_isDepPath_H l₁ l₂ (hsplit ▸ hdep)
  have hv_mem : v ∈ ρ := mem_tail_of_split_cons_H l₁ l₂ ρ hsplit
  have hfree_cr := hsep q hq ρ hdep hfreeB hlen
  have hv_not_cr : v ∉ crossingLowerEtaSteps τ₀ T H ηInv L_cap :=
    hfree_cr v hv_mem
  rcases hstep with ⟨hchron, _⟩ | hhop_mem
  · exact Or.inl hchron.symm
  · obtain ⟨⟨j, v', u'⟩, hη, heq⟩ := mem_image.mp hhop_mem
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    have hhop : IsHop (τ₀.work j) T v' u' := mem_allHops.mp hη
    by_cases hgt : HasHopExcursionGTAt (τ₀.work j) (2 * H) v' u'
    · right; right
      obtain ⟨hband_vu, hband_cr⟩ := hE1 q hq ρ hdep hfreeB hlen j v' u' hv_mem hhop hgt
      have hnc : IsNonCrossingLargeHop (τ₀.work j) T (2 * H) v' u' := by
        refine ⟨hhop, hgt, fun p' u'' hhop' hgt' hcross => hv_not_cr ?_⟩
        have hv'T : v' < T := lt_trans (lt_trans (Nat.lt_succ_self v') hhop.1) hhop.2.1
        unfold crossingLowerEtaSteps
        refine mem_filter.mpr ⟨mem_range.mpr hv'T, j, u', ⟨hhop, hgt, hband_vu⟩,
          p', u'', ⟨hhop', hgt', hband_cr p' u'' hhop' hgt' hcross⟩, hcross⟩
      exact ⟨j, hnc, (hθ_spec j).2.2 v' u' hnc⟩
    · right; left
      refine ⟨j, hhop, fun t ht => ?_⟩
      by_contra hnot
      push Not at hnot
      exact hgt ⟨t, ht, hnot⟩

/-- Positivity `1 ≤ bridgeGenieFactor k D C α`. -/
theorem bridgeGenieFactor_pos (k D : ℕ) (C α : ℝ) : 1 ≤ bridgeGenieFactor k D C α := by
  unfold bridgeGenieFactor bridgeThreshCount
  have hpow : 1 ≤ (k + 2) ^ D := Nat.pow_pos (by omega)
  have hnth : 1 ≤ (2 * k + 1) + bridgeChainCap k * (2 * k + 1) *
      (⌈8 * (bridgeChainCap k : ℝ) * C / α⌉₊ + 1) := by omega
  have h5k : 1 ≤ 5 * k + 1 := by omega
  exact Nat.mul_pos (Nat.mul_pos hpow hnth) h5k

/-- **Macroscopic Hop-Threshold Coefficient `θ_E(k, D, C, α) = α / (12 * E₀(k, D, C, α)) > 0`:** -/
noncomputable def thetaBridge_genie (k D : ℕ) (C α : ℝ) : ℝ :=
  α / (12 * (bridgeGenieFactor k D C α : ℝ))

theorem thetaBridge_genie_pos (k D : ℕ) (C : ℝ) {α : ℝ} (hα0 : 0 < α) :
    0 < thetaBridge_genie k D C α := by
  unfold thetaBridge_genie
  have hE0 : (1 : ℝ) ≤ (bridgeGenieFactor k D C α : ℝ) := by exact_mod_cast bridgeGenieFactor_pos k D C α
  positivity

/-- Combined dimension threshold ensuring BOTH `d ≥ timePullback_gen_d0 (bridgeChainCap k) C α` AND
`W = d * b ≤ ⌊thetaBridge_genie k D C α * L⌋₊` (so `[W, ⌊θ_E L⌋₊]` is non-empty). -/
noncomputable def macroBridge_d0_genie (k D : ℕ) (C α : ℝ) : ℕ :=
  max (timePullback_gen_d0 (bridgeChainCap k) C α)
    ⌈12 * (bridgeGenieFactor k D C α : ℝ) / α⌉₊

/-- Above `macroBridge_d0_genie k D C α`, row width `W = d * b` lies below `thetaBridge_genie k D C α * L`. -/
theorem rowWidth_le_theta_mul_L {k D d b : ℕ} {C α : ℝ} (hα0 : 0 < α)
    (hd : macroBridge_d0_genie k D C α ≤ d) :
    ((d * b : ℕ) : ℝ) ≤ thetaBridge_genie k D C α * ((d * d * b : ℕ) : ℝ) := by
  have hd_e0 : ⌈12 * (bridgeGenieFactor k D C α : ℝ) / α⌉₊ ≤ d := (le_max_right _ _).trans hd
  have hge : 12 * (bridgeGenieFactor k D C α : ℝ) / α ≤ (d : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hd_e0)
  have hmul : 12 * (bridgeGenieFactor k D C α : ℝ) ≤ (d : ℝ) * α := (div_le_iff₀ hα0).mp hge
  have hE0_pos : (0 : ℝ) < 12 * (bridgeGenieFactor k D C α : ℝ) := by
    have : (1 : ℝ) ≤ (bridgeGenieFactor k D C α : ℝ) := by exact_mod_cast bridgeGenieFactor_pos k D C α
    linarith
  unfold thetaBridge_genie
  rw [div_mul_eq_mul_div, le_div_iff₀ hE0_pos]
  calc ((d * b : ℕ) : ℝ) * (12 * (bridgeGenieFactor k D C α : ℝ))
      ≤ ((d * b : ℕ) : ℝ) * ((d : ℝ) * α) :=
        mul_le_mul_of_nonneg_left hmul (by positivity)
    _ = α * ((d * d * b : ℕ) : ℝ) := by push_cast; ring

/-- **Macroscopic-Threshold Bridge Theorem:**
On **any** `k`-tape trace `τ₀` (`zero TransposesAt hypothesis!`), for **every** `1 ≤ H` with
`(H : ℝ) ≤ thetaBridge_genie k D C α * L` and `d ≥ timePullback_gen_d0 (bridgeChainCap k) C α`,
if `B` `D`-separates `V₀` (`|V₀| ≥ α L`) from `crossingLowerEtaSteps τ₀ T H ηInv L_cap` under
`ClauseE1H`, then `ballAvoidSystem τ₀ T D B d b` contains an acyclic subset `U ⊆ V₀` of size
`|U| ≥ ρ₀(k, C, α) * |V₀|`! -/
theorem bridge_exists_isAcyclicIn_crossingLowerH {k T d b D H ηInv L_cap : ℕ} {C α : ℝ}
    (τ₀ : Trace k) (hd : 1 ≤ d) (hb : 1 ≤ b) (hH : 1 ≤ H) (hC : 1 ≤ C) (hα0 : 0 < α)
    (hlen : (appendList τ₀ T).length = d * d * b)
    (hT : (T : ℝ) ≤ C * (((d * d * b : ℕ) : ℝ) + 1))
    (V₀ : Finset (Fin (d * d * b))) (B : Finset ℕ)
    (hV₀ : α * ((d * d * b : ℕ) : ℝ) ≤ (V₀.card : ℝ))
    (hH_le : (H : ℝ) ≤ thetaBridge_genie k D C α * ((d * d * b : ℕ) : ℝ))
    (hd_thresh : timePullback_gen_d0 (bridgeChainCap k) C α ≤ d)
    (hsep : IsBallPathSeparator τ₀ T D d b V₀ (crossingLowerEtaSteps τ₀ T H ηInv L_cap) B)
    (hE1 : ClauseE1H τ₀ T D d b H ηInv L_cap V₀ B) :
    ∃ U : Finset (Fin (d * d * b)),
      U ⊆ V₀ ∧
      HalfRate.IsAcyclicIn (ballAvoidSystem τ₀ T D B d b) U ∧
      genieBridge_rho0 k C α * (V₀.card : ℝ) ≤ (U.card : ℝ) := by
  let L := d * d * b
  let m₀ := bridgeChainCap k
  let B_time := ⌈8 * (m₀ : ℝ) * C / α⌉₊
  have hm₀ : 1 ≤ m₀ := bridgeChainCap_pos k
  have hT_pos : 1 ≤ T := by
    have hL_pos : 1 ≤ L := Nat.mul_pos (Nat.mul_pos hd hd) hb
    have hlast_lt : L - 1 < (appendList τ₀ T).length := by rw [hlen]; omega
    have hot_lt : appendTime τ₀ T (L - 1) < T := appendTime_lt τ₀ T hlast_lt
    omega
  -- Step 1: Dichotomy & work-phase partition at threshold `2 * H`.
  obtain ⟨θ_pos, θ_neg, hθ_le, hdich_all⟩ :=
    depPath_nonCrossing_dichotomy_of_isBallPathSeparator_crossingLowerH τ₀ T D d b H ηInv L_cap
      V₀ B hsep hE1
  obtain ⟨M_work, θ_lo, θ_hi, ph, _, hM_le, hlo_lt_hi, hsep_ph, hno_cut, hph_mem, _, hph_mono⟩ :=
    exists_workPhase_partition hT_pos θ_pos θ_neg hθ_le
  have hlo_le_hi : ∀ c : Fin M_work, θ_lo c ≤ θ_hi c := fun c => le_of_lt (hlo_lt_hi c).1
  -- Step 2: Threshold guard set `X_bad` at scale `H` (`|Z_bad| ≤ E₀ * H ≤ (α / 12) * L`).
  let PhaseThresh : Finset ℕ := (univ : Finset (Fin M_work)).image θ_lo
  let stepsOf : ChainIdx M_work k → List (Fin M_work × Fin k) :=
    fun ν => decodeSteps M_work k ν.1.1 (le_of_lt ν.1.2) ν.2
  let ChainThresh : Finset ℕ :=
    (univ : Finset (ChainIdx M_work k)).biUnion fun ν =>
      (range (B_time + 1)).biUnion fun s =>
        chainThresholds τ₀ T H B_time θ_lo θ_hi ν.1 (stepsOf ν) s
  let AllThresh : Finset ℕ := PhaseThresh ∪ ChainThresh
  have hcard_chainIdx : Fintype.card (ChainIdx M_work k) ≤ m₀ := card_chainIdx_le hM_le
  have hAllThresh_card : AllThresh.card ≤ bridgeThreshCount k C α := by
    have hPT : PhaseThresh.card ≤ 2 * k + 1 := by
      calc PhaseThresh.card ≤ (univ : Finset (Fin M_work)).card := card_image_le
        _ = M_work := by simp
        _ ≤ 2 * k + 1 := hM_le
    have hCT_each : ∀ ν : ChainIdx M_work k,
        ((range (B_time + 1)).biUnion fun s =>
          chainThresholds τ₀ T H B_time θ_lo θ_hi ν.1 (stepsOf ν) s).card ≤
          (2 * k + 1) * (B_time + 1) := by
      intro ν
      have hlen_le : (stepsOf ν).length ≤ ν.1.1 :=
        (decodeSteps_validStepsBelow M_work k ν.1.1 (le_of_lt ν.1.2) ν.2).2
      have hcard_s : ∀ s ∈ range (B_time + 1),
          (chainThresholds τ₀ T H B_time θ_lo θ_hi ν.1 (stepsOf ν) s).card ≤ 2 * k + 1 := by
        intro s _
        calc (chainThresholds τ₀ T H B_time θ_lo θ_hi ν.1 (stepsOf ν) s).card
            ≤ (stepsOf ν).length + 1 := card_chainThresholds_le τ₀ T H B_time θ_lo θ_hi ν.1 (stepsOf ν) s
          _ ≤ ν.1.1 + 1 := Nat.add_le_add_right hlen_le 1
          _ ≤ 2 * k + 1 := by have := ν.1.2; omega
      calc ((range (B_time + 1)).biUnion fun s =>
            chainThresholds τ₀ T H B_time θ_lo θ_hi ν.1 (stepsOf ν) s).card
          ≤ ∑ s ∈ range (B_time + 1),
              (chainThresholds τ₀ T H B_time θ_lo θ_hi ν.1 (stepsOf ν) s).card := card_biUnion_le
        _ ≤ ∑ _s ∈ range (B_time + 1), (2 * k + 1) := sum_le_sum hcard_s
        _ = (2 * k + 1) * (B_time + 1) := by simp [Nat.mul_comm]
    have hCT : ChainThresh.card ≤ m₀ * (2 * k + 1) * (B_time + 1) := by
      calc ChainThresh.card
          ≤ ∑ ν : ChainIdx M_work k,
              ((range (B_time + 1)).biUnion fun s =>
                chainThresholds τ₀ T H B_time θ_lo θ_hi ν.1 (stepsOf ν) s).card := card_biUnion_le
        _ ≤ ∑ _ν : ChainIdx M_work k, (2 * k + 1) * (B_time + 1) :=
            sum_le_sum fun ν _ => hCT_each ν
        _ = Fintype.card (ChainIdx M_work k) * ((2 * k + 1) * (B_time + 1)) := by simp
        _ ≤ m₀ * ((2 * k + 1) * (B_time + 1)) := Nat.mul_le_mul_right _ hcard_chainIdx
        _ = m₀ * (2 * k + 1) * (B_time + 1) := by ring
    calc AllThresh.card
        ≤ PhaseThresh.card + ChainThresh.card := card_union_le _ _
      _ ≤ (2 * k + 1) + m₀ * (2 * k + 1) * (B_time + 1) := Nat.add_le_add hPT hCT
      _ = bridgeThreshCount k C α := rfl
  let X_bad : Finset ℕ := AllThresh.biUnion (microHopStepGuard τ₀ T H)
  have hX_bad_card : X_bad.card ≤ bridgeThreshCount k C α * (5 * k + 1) * H := by
    calc X_bad.card
        ≤ ∑ ψ ∈ AllThresh, (microHopStepGuard τ₀ T H ψ).card := card_biUnion_le
      _ ≤ ∑ _ψ ∈ AllThresh, (5 * k + 1) * H :=
          sum_le_sum fun ψ _ => card_microHopStepGuard_le τ₀ T hH ψ
      _ = AllThresh.card * ((5 * k + 1) * H) := by simp
      _ ≤ bridgeThreshCount k C α * ((5 * k + 1) * H) := Nat.mul_le_mul_right _ hAllThresh_card
      _ = bridgeThreshCount k C α * (5 * k + 1) * H := by ring
  let Anc_bad : Finset ℕ := ancestors τ₀.work T X_bad D
  let u₀_of : Fin L → ℕ := fun q => appendTime τ₀ T (tposOf d b q).1
  let Z_bad : Finset (Fin L) := V₀.filter fun q => u₀_of q ∈ Anc_bad
  have hZ_bad_nat : Z_bad.card ≤ bridgeGenieFactor k D C α * H := by
    have hinj := appendTime_tposOf_injective τ₀ hlen
    have hsub_img : Z_bad.image u₀_of ⊆ Anc_bad := by
      intro x hx
      obtain ⟨q, hqZ, rfl⟩ := mem_image.mp hx
      exact (mem_filter.mp hqZ).2
    calc Z_bad.card
        = (Z_bad.image u₀_of).card := (card_image_of_injective Z_bad hinj).symm
      _ ≤ Anc_bad.card := card_le_card hsub_img
      _ ≤ (k + 2) ^ D * X_bad.card := card_ancestors_le τ₀.work T X_bad D
      _ ≤ (k + 2) ^ D * (bridgeThreshCount k C α * (5 * k + 1) * H) :=
          Nat.mul_le_mul_left _ hX_bad_card
      _ = bridgeGenieFactor k D C α * H := by unfold bridgeGenieFactor; ring
  have hZ_bad_alpha : (Z_bad.card : ℝ) ≤ (α / 12) * ((d * d * b : ℕ) : ℝ) := by
    have hZr : (Z_bad.card : ℝ) ≤ (bridgeGenieFactor k D C α : ℝ) * (H : ℝ) := by
      have hr : (Z_bad.card : ℝ) ≤ ((bridgeGenieFactor k D C α * H : ℕ) : ℝ) := by
        exact_mod_cast hZ_bad_nat
      simpa [Nat.cast_mul] using hr
    have hE0_ne : (bridgeGenieFactor k D C α : ℝ) ≠ 0 := by
      have : (1 : ℝ) ≤ (bridgeGenieFactor k D C α : ℝ) := by exact_mod_cast bridgeGenieFactor_pos k D C α
      linarith
    calc (Z_bad.card : ℝ)
        ≤ (bridgeGenieFactor k D C α : ℝ) * (H : ℝ) := hZr
      _ ≤ (bridgeGenieFactor k D C α : ℝ) *
            (thetaBridge_genie k D C α * ((d * d * b : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hH_le (by positivity)
      _ = (α / 12) * ((d * d * b : ℕ) : ℝ) := by
          unfold thetaBridge_genie
          field_simp [hE0_ne]
  have hθ_lo_mem_All : ∀ γ : Fin M_work, θ_lo γ ∈ AllThresh :=
    fun γ => mem_union_left _ (mem_image_of_mem θ_lo (mem_univ γ))
  have hpsi_mem_All : ∀ (γ : Fin M_work) (steps : List (Fin M_work × Fin k)),
      ValidStepsBelow γ.1 steps → ∀ s ≤ B_time,
      pullChainPsi τ₀ T H B_time θ_lo θ_hi γ steps s ∈ AllThresh := by
    intro γ steps hvalid s hs
    obtain ⟨f, hf⟩ := exists_decodeSteps_of_validStepsBelow M_work k γ.1 (le_of_lt γ.2) steps hvalid
    let ν : ChainIdx M_work k := ⟨γ, f⟩
    have hsteps_eq : stepsOf ν = steps := hf
    refine mem_union_right _ (mem_biUnion.mpr ⟨ν, mem_univ ν, mem_biUnion.mpr ⟨s, mem_range.mpr (by omega), ?_⟩⟩)
    rw [hsteps_eq]
    exact pullChainPsi_mem_chainThresholds τ₀ T H B_time θ_lo θ_hi γ steps s
  -- Step 3: `(ξ, π_perm)` at scale `H`.
  let ξ : ChainIdx M_work k → ℕ → ℕ := fun ν s =>
    if chainParity (stepsOf ν) = false then
      pullChainPsi τ₀ T H B_time θ_lo θ_hi ν.1 (stepsOf ν) s
    else
      pullChainPsi τ₀ T H B_time θ_lo θ_hi ν.1 (stepsOf ν) (B_time - s)
  let π_perm : ChainIdx M_work k → Fin B_time → Fin B_time := fun ν β =>
    if chainParity (stepsOf ν) = false then β
    else ⟨B_time - 1 - β.1, by omega⟩
  have hξ_mono : ∀ ν : ChainIdx M_work k, ∀ s₁ s₂ : ℕ, s₁ ≤ s₂ → s₂ ≤ B_time → ξ ν s₁ ≤ ξ ν s₂ := by
    intro ν s₁ s₂ hs₁₂ hs₂B
    have hsp := (pullChainPsi_bounds_and_mono τ₀ T H B_time θ_lo θ_hi hlo_le_hi (stepsOf ν) ν.1).2
    dsimp only [ξ]
    cases hpar : chainParity (stepsOf ν)
    · simp only [↓reduceIte]
      have hm := hsp s₁ s₂ hs₁₂
      simp only [hpar, ↓reduceIte] at hm
      exact hm
    · simp only [Bool.true_eq_false, ↓reduceIte]
      have hm := hsp (B_time - s₂) (B_time - s₁) (by omega)
      simp only [hpar, Bool.true_eq_false, ↓reduceIte] at hm
      exact hm
  have hπ_inj : ∀ ν : ChainIdx M_work k, Function.Injective (π_perm ν) := by
    intro ν β₁ β₂ heq
    dsimp only [π_perm] at heq
    split_ifs at heq with hpar
    · exact heq
    · have hv : B_time - 1 - β₁.1 = B_time - 1 - β₂.1 := congrArg Fin.val heq
      have h1 := β₁.2
      have h2 := β₂.2
      exact Fin.ext (by omega)
  -- Step 4: Path-to-chain pullback induction at scale `H`.
  have hpull : ∀ q ∈ V₀ \ Z_bad, ∀ p ∈ V₀, ∀ ρ : List ℕ,
      ρ.length ≤ D →
      IsDepPath τ₀.work T (u₀_of q :: ρ) →
      LinNet.GFree B (u₀_of q :: ρ) →
      τ₀.input ((u₀_of q :: ρ).getLastD (u₀_of q)) = (p.1 : ℤ) →
      ∀ β : Fin B_time,
        (u₀_of q :: ρ).getLastD (u₀_of q) ∈ timeBlock T B_time β →
        ∃ ν : ChainIdx M_work k, u₀_of q ∈ Ico (ξ ν (π_perm ν β).1) (ξ ν ((π_perm ν β).1 + 1)) := by
    intro q hqVZ _ _ ρ hlen_ρ hdep_full hfree_full _ β ht_m_blk
    obtain ⟨hqV, hqNotZ⟩ := Finset.mem_sdiff.mp hqVZ
    have hnot_Anc : u₀_of q ∉ Anc_bad := fun hA => hqNotZ (mem_filter.mpr ⟨hqV, hA⟩)
    have hpath_no_X : ∀ x ∈ (u₀_of q :: ρ), x ∉ X_bad := by
      intro x hx_mem hx_bad
      have hanc_len := head_mem_ancestors_of_mem_path ρ (u₀_of q) hdep_full hx_mem hx_bad
      exact hnot_Anc (ancestors_mono τ₀.work T X_bad hlen_ρ hanc_len)
    have hsuf_pull : ∀ (ρ_suf : List ℕ) (t₀ : ℕ) (pref : List ℕ),
        u₀_of q :: ρ = pref ++ (t₀ :: ρ_suf) →
        t₀ < T →
        IsDepPath τ₀.work T (t₀ :: ρ_suf) →
        ∃ steps : List (Fin M_work × Fin k),
          ValidStepsBelow (ph t₀).1 steps ∧
          ∀ s ≤ B_time,
            (chainPred (chainParity steps) (pullChainPsi τ₀ T H B_time θ_lo θ_hi (ph t₀) steps s) t₀ ↔
              (t₀ :: ρ_suf).getLastD t₀ < timeBlockBound T B_time s) := by
      intro ρ_suf
      induction ρ_suf with
      | nil =>
        intro t₀ _ _ ht₀_T _
        refine ⟨[], trivial, fun s _ => ?_⟩
        obtain ⟨hlo, hhi⟩ := mem_Ico.mp (hph_mem t₀ ht₀_T)
        have hlast0 : ([t₀]).getLastD t₀ = t₀ := rfl
        rw [hlast0]
        dsimp only [chainParity, chainPred, pullChainPsi]
        simp only [Bool.false_eq_true, ↓reduceIte]
        rcases le_or_gt (timeBlockBound T B_time s) (θ_lo (ph t₀)) with h1 | h1
        · rw [Nat.max_eq_left h1, Nat.min_eq_right (le_of_lt (hlo_lt_hi (ph t₀)).1)]
          omega
        · rw [Nat.max_eq_right (le_of_lt h1)]
          rcases le_or_gt (θ_hi (ph t₀)) (timeBlockBound T B_time s) with h2 | h2
          · rw [Nat.min_eq_left h2]
            omega
          · rw [Nat.min_eq_right (le_of_lt h2)]
      | cons t₁ ρ₁ ih =>
        intro t₀ pref hsplit ht₀_T ⟨hstep, htail⟩
        have ht₁_lt_t₀ : t₁ < t₀ := (depStep_lt hstep).1
        have ht₁_T : t₁ < T := lt_trans ht₁_lt_t₀ ht₀_T
        have hsplit' : u₀_of q :: ρ = (pref ++ [t₀]) ++ (t₁ :: ρ₁) := by
          simpa [List.append_assoc] using hsplit
        obtain ⟨steps₁, hvalid₁, hiff₁⟩ := ih t₁ (pref ++ [t₀]) hsplit' ht₁_T htail
        have hdich_edge := hdich_all q hqV ρ pref ρ₁ t₀ t₁ hdep_full hfree_full hlen_ρ hsplit
        have ht₁_mem_full : t₁ ∈ u₀_of q :: ρ := by
          rw [hsplit]
          exact List.mem_append_right pref (List.mem_cons_of_mem t₀ List.mem_cons_self)
        have ht₁_no_X : t₁ ∉ X_bad := hpath_no_X t₁ ht₁_mem_full
        have hph_le : (ph t₁).1 ≤ (ph t₀).1 := hph_mono t₁ t₀ (le_of_lt ht₁_lt_t₀) ht₀_T
        have hlast_eq : (t₀ :: t₁ :: ρ₁).getLastD t₀ = (t₁ :: ρ₁).getLastD t₁ :=
          LinNet.getLastD_cons_cons t₀ t₁ ρ₁
        rcases eq_or_lt_of_le hph_le with heq_val | hlt_ph
        · have heq_ph : ph t₁ = ph t₀ := Fin.ext heq_val
          refine ⟨steps₁, heq_ph ▸ hvalid₁, fun s hsB => ?_⟩
          let ψ := pullChainPsi τ₀ T H B_time θ_lo θ_hi (ph t₀) steps₁ s
          have hψ_All : ψ ∈ AllThresh := hpsi_mem_All (ph t₀) steps₁ (heq_ph ▸ hvalid₁) s hsB
          have ht₁_guard : t₁ ∉ microHopStepGuard τ₀ T H ψ :=
            fun hg => ht₁_no_X (mem_biUnion.mpr ⟨ψ, hψ_All, hg⟩)
          have ht₀_in : t₀ ∈ Ico (θ_lo (ph t₀)) (θ_hi (ph t₀)) := hph_mem t₀ ht₀_T
          have ht₁_in : t₁ ∈ Ico (θ_lo (ph t₀)) (θ_hi (ph t₀)) := heq_ph ▸ hph_mem t₁ ht₁_T
          have hintra := dichotomy_intraPhase_chainPred_iff (hno_cut (ph t₀))
            ht₀_in ht₁_in hdich_edge ht₁_guard (chainParity steps₁)
          rw [hlast_eq, hintra]
          simpa [ψ, heq_ph] using hiff₁ s hsB
        · have ht₀_in : t₀ ∈ Ico (θ_lo (ph t₀)) (θ_hi (ph t₀)) := hph_mem t₀ ht₀_T
          have ht₁_in : t₁ ∈ Ico (θ_lo (ph t₁)) (θ_hi (ph t₁)) := hph_mem t₁ ht₁_T
          have ht₁_lt_lo : t₁ < θ_lo (ph t₀) :=
            lt_of_lt_of_le (mem_Ico.mp ht₁_in).2 (hsep_ph (ph t₁) (ph t₀) hlt_ph)
          have ht₁_guard_lo : t₁ ∉ microHopStepGuard τ₀ T H (θ_lo (ph t₀)) :=
            fun hg => ht₁_no_X (mem_biUnion.mpr ⟨θ_lo (ph t₀), hθ_lo_mem_All (ph t₀), hg⟩)
          obtain ⟨j₁, hnc₁⟩ := dichotomy_interPhase_exists_hop
            (mem_Ico.mp ht₀_in).1 ht₁_lt_lo hdich_edge ht₁_guard_lo
          refine ⟨(ph t₁, j₁) :: steps₁, ⟨hlt_ph, hvalid₁⟩, fun s hsB => ?_⟩
          have hinter := pullChainPsi_cons_iff τ₀ T H B_time θ_lo θ_hi hsep_ph
            hlt_ph j₁ steps₁ s ht₀_in ht₁_in hnc₁
          rw [hlast_eq, hinter]
          exact hiff₁ s hsB
    have hu₀_T : u₀_of q < T := appendTime_lt τ₀ T (by rw [hlen]; exact (tposOf d b q).2)
    obtain ⟨steps, hvalid, hiff⟩ := hsuf_pull ρ (u₀_of q) [] rfl hu₀_T hdep_full
    obtain ⟨f, hf⟩ := exists_decodeSteps_of_validStepsBelow M_work k (ph (u₀_of q)).1
      (le_of_lt (ph (u₀_of q)).2) steps hvalid
    let ν : ChainIdx M_work k := ⟨ph (u₀_of q), f⟩
    have hsteps_eq : stepsOf ν = steps := hf
    refine ⟨ν, ?_⟩
    obtain ⟨hb_lo, hb_hi⟩ := timeBlock_eq_Ico_bound T B_time β
    obtain ⟨htm_ge, htm_lt⟩ := mem_Ico.mp ht_m_blk
    rw [hb_lo] at htm_ge
    rw [hb_hi] at htm_lt
    have hnot_lo : ¬ chainPred (chainParity (stepsOf ν))
        (pullChainPsi τ₀ T H B_time θ_lo θ_hi ν.1 (stepsOf ν) β.1) (u₀_of q) := by
      dsimp only [ν]
      rw [hsteps_eq, hiff β.1 (le_of_lt β.2)]
      omega
    have hyes_hi : chainPred (chainParity (stepsOf ν))
        (pullChainPsi τ₀ T H B_time θ_lo θ_hi ν.1 (stepsOf ν) (β.1 + 1)) (u₀_of q) := by
      dsimp only [ν]
      rw [hsteps_eq, hiff (β.1 + 1) (Nat.succ_le_of_lt β.2)]
      exact htm_lt
    dsimp only [ξ, π_perm]
    cases hpar : chainParity (stepsOf ν)
    · simp only [↓reduceIte]
      rw [hpar] at hnot_lo hyes_hi
      simp only [chainPred, Bool.false_eq_true, ↓reduceIte, not_lt] at hnot_lo hyes_hi
      exact mem_Ico.mpr ⟨hnot_lo, hyes_hi⟩
    · simp only [Bool.true_eq_false, ↓reduceIte]
      rw [hpar] at hnot_lo hyes_hi
      simp only [chainPred, ↓reduceIte, not_le] at hnot_lo hyes_hi
      have hsub1 : B_time - (B_time - 1 - β.1) = β.1 + 1 := by have := β.2; omega
      have hsub2 : B_time - (B_time - 1 - β.1 + 1) = β.1 := by have := β.2; omega
      rw [hsub1, hsub2]
      exact mem_Ico.mpr ⟨hyes_hi, hnot_lo⟩
  -- Step 5: Invoke general-budget Theorem 5.1 (time pullback) (`timePullback_blockCut_mais`).
  have hZ_v0 : (Z_bad.card : ℝ) ≤ (V₀.card : ℝ) / 12 := by linarith
  exact timePullback_blockCut_mais τ₀ hd hb hm₀ hC hα0 hcard_chainIdx
    hlen hT V₀ Z_bad B hV₀ hZ_v0 hd_thresh ξ hξ_mono π_perm hπ_inj hpull

/-- **Uncapped Zero-Clause Macroscopic-Threshold Bridge:** -/
theorem bridge_exists_isAcyclicIn_crossingLowerGT2H {k T d b D H : ℕ} {C α : ℝ}
    (τ₀ : Trace k) (hd : 1 ≤ d) (hb : 1 ≤ b) (hH : 1 ≤ H) (hC : 1 ≤ C) (hα0 : 0 < α)
    (hlen : (appendList τ₀ T).length = d * d * b)
    (hT : (T : ℝ) ≤ C * (((d * d * b : ℕ) : ℝ) + 1))
    (V₀ : Finset (Fin (d * d * b))) (B : Finset ℕ)
    (hV₀ : α * ((d * d * b : ℕ) : ℝ) ≤ (V₀.card : ℝ))
    (hH_le : (H : ℝ) ≤ thetaBridge_genie k D C α * ((d * d * b : ℕ) : ℝ))
    (hd_thresh : timePullback_gen_d0 (bridgeChainCap k) C α ≤ d)
    (hsep : IsBallPathSeparator τ₀ T D d b V₀ (crossingLowerEtaSteps τ₀ T H 1 T) B) :
    ∃ U : Finset (Fin (d * d * b)),
      U ⊆ V₀ ∧
      HalfRate.IsAcyclicIn (ballAvoidSystem τ₀ T D B d b) U ∧
      genieBridge_rho0 k C α * (V₀.card : ℝ) ≤ (U.card : ℝ) :=
  bridge_exists_isAcyclicIn_crossingLowerH τ₀ hd hb hH hC hα0 hlen hT V₀ B
    hV₀ hH_le hd_thresh hsep (clauseE1H_uncapped τ₀ T D d b H V₀ B)

end MacroscopicThresholdBridge

/-! ## §3. Pure Trace-Only Dichotomy for Every Linear-Time Trace -/

section TraceOnlyDichotomy

open scoped Classical

/-- **`S3` Trace-Only Dichotomy (`IsBallPathSeparator` Form — Zero Transposition Hypothesis!):**
For **every** `k`-tape linear-time trace `τ₀` (`(appendList τ₀ T).length = L`, `T ≤ C(L + 1)`),
**every** macroscopic set `V₀` (`|V₀| ≥ α L`), **every** threshold `1 ≤ H` with
`(H : ℝ) ≤ thetaBridge_genie k D C α * L`, and **every** cut ratio `c`, EITHER:
1. some `B` with `|B| < c |V₀|` `D`-separates `V₀` from `crossingLowerEtaSteps τ₀ T H 1 T` **and**
   `ballAvoidSystem τ₀ T D B d b` contains an acyclic `U ⊆ V₀` of size `≥ ρ₀(k, C, α) * |V₀|`; OR
2. **every** `D`-ball separator `B` from `V₀` to `crossingLowerEtaSteps τ₀ T H 1 T` has size `≥ c |V₀|`. -/
theorem linearTimeTrace_crossingLowerGT2H_ballSep_dichotomy {k T d b D H : ℕ} {C α c : ℝ}
    (τ₀ : Trace k) (hd : 1 ≤ d) (hb : 1 ≤ b) (hH : 1 ≤ H) (hC : 1 ≤ C) (hα0 : 0 < α)
    (hlen : (appendList τ₀ T).length = d * d * b)
    (hT : (T : ℝ) ≤ C * (((d * d * b : ℕ) : ℝ) + 1))
    (V₀ : Finset (Fin (d * d * b)))
    (hV₀ : α * ((d * d * b : ℕ) : ℝ) ≤ (V₀.card : ℝ))
    (hH_le : (H : ℝ) ≤ thetaBridge_genie k D C α * ((d * d * b : ℕ) : ℝ))
    (hd_thresh : timePullback_gen_d0 (bridgeChainCap k) C α ≤ d) :
    (∃ B : Finset ℕ,
      IsBallPathSeparator τ₀ T D d b V₀ (crossingLowerEtaSteps τ₀ T H 1 T) B ∧
      (B.card : ℝ) < c * (V₀.card : ℝ) ∧
      ∃ U : Finset (Fin (d * d * b)),
        U ⊆ V₀ ∧
        HalfRate.IsAcyclicIn (ballAvoidSystem τ₀ T D B d b) U ∧
        genieBridge_rho0 k C α * (V₀.card : ℝ) ≤ (U.card : ℝ)) ∨
    (∀ B : Finset ℕ,
      IsBallPathSeparator τ₀ T D d b V₀ (crossingLowerEtaSteps τ₀ T H 1 T) B →
      c * (V₀.card : ℝ) ≤ (B.card : ℝ)) := by
  by_cases hex : ∃ B : Finset ℕ,
      IsBallPathSeparator τ₀ T D d b V₀ (crossingLowerEtaSteps τ₀ T H 1 T) B ∧
      (B.card : ℝ) < c * (V₀.card : ℝ)
  · left
    obtain ⟨B, hsep, hlt⟩ := hex
    exact ⟨B, hsep, hlt,
      bridge_exists_isAcyclicIn_crossingLowerGT2H τ₀ hd hb hH hC hα0
        hlen hT V₀ B hV₀ hH_le hd_thresh hsep⟩
  · right
    intro B hsep
    by_contra hnot
    push Not at hnot
    exact hex ⟨B, hsep, hnot⟩

/-- **`S3` Trace-Only Dichotomy (`IsMengerVertexCut` Form — Zero Transposition Hypothesis!):**
For **every** `k`-tape linear-time trace `τ₀`, **every** `V₀` (`|V₀| ≥ α L`), **every** `1 ≤ H` with
`(H : ℝ) ≤ thetaBridge_genie k D C (α / 2) * L`, and **every** cut ratio `c ≤ 1 / 2`, EITHER:
1. some Menger vertex cut `B` (`allowing root hits`) of size `|B| < c |V₀|` disconnects `u₀(V₀)`
   from `crossingLowerEtaSteps τ₀ T H 1 T` **and** `ballAvoidSystem τ₀ T D B d b` contains an acyclic
   `U ⊆ V₀` of size `|U| ≥ (1 / 2) * ρ₀(k, C, α / 2) * |V₀|`; OR
2. **every** Menger vertex cut `B` disconnecting `u₀(V₀)` from `crossingLowerEtaSteps τ₀ T H 1 T`
   satisfies `|B| ≥ c |V₀|`. -/
theorem linearTimeTrace_crossingLowerGT2H_menger_dichotomy {k T d b D H : ℕ} {C α c : ℝ}
    (τ₀ : Trace k) (hd : 1 ≤ d) (hb : 1 ≤ b) (hH : 1 ≤ H) (hC : 1 ≤ C) (hα0 : 0 < α)
    (hc_half : c ≤ 1 / 2)
    (hlen : (appendList τ₀ T).length = d * d * b)
    (hT : (T : ℝ) ≤ C * (((d * d * b : ℕ) : ℝ) + 1))
    (V₀ : Finset (Fin (d * d * b)))
    (hV₀ : α * ((d * d * b : ℕ) : ℝ) ≤ (V₀.card : ℝ))
    (hH_le : (H : ℝ) ≤ thetaBridge_genie k D C (α / 2) * ((d * d * b : ℕ) : ℝ))
    (hd_thresh : timePullback_gen_d0 (bridgeChainCap k) C (α / 2) ≤ d) :
    let Src := V₀.image fun q => appendTime τ₀ T (tposOf d b q).1
    (∃ B : Finset ℕ,
      IsMengerVertexCut τ₀.work T Src (crossingLowerEtaSteps τ₀ T H 1 T) B ∧
      (B.card : ℝ) < c * (V₀.card : ℝ) ∧
      ∃ U : Finset (Fin (d * d * b)),
        U ⊆ V₀ ∧
        HalfRate.IsAcyclicIn (ballAvoidSystem τ₀ T D B d b) U ∧
        (1 / 2 : ℝ) * genieBridge_rho0 k C (α / 2) * (V₀.card : ℝ) ≤ (U.card : ℝ)) ∨
    (∀ B : Finset ℕ,
      IsMengerVertexCut τ₀.work T Src (crossingLowerEtaSteps τ₀ T H 1 T) B →
      c * (V₀.card : ℝ) ≤ (B.card : ℝ)) := by
  intro Src
  by_cases hex : ∃ B : Finset ℕ,
      IsMengerVertexCut τ₀.work T Src (crossingLowerEtaSteps τ₀ T H 1 T) B ∧
      (B.card : ℝ) < c * (V₀.card : ℝ)
  · left
    obtain ⟨B, hmenger, hB_lt⟩ := hex
    let V₀' := V₀.filter fun q => appendTime τ₀ T (tposOf d b q).1 ∉ B
    obtain ⟨hcard_split, hsep'⟩ :=
      isBallPathSeparator_of_isMengerVertexCut (D := D) τ₀ hlen V₀ _ B hmenger
    have hcard_r : (V₀.card : ℝ) ≤ (V₀'.card : ℝ) + (B.card : ℝ) := by
      have hr : (V₀.card : ℝ) ≤ ((V₀'.card + B.card : ℕ) : ℝ) := by exact_mod_cast hcard_split
      simpa [Nat.cast_add] using hr
    have hB_half : (B.card : ℝ) ≤ (V₀.card : ℝ) / 2 := by
      have hcV : c * (V₀.card : ℝ) ≤ (1 / 2 : ℝ) * (V₀.card : ℝ) :=
        mul_le_mul_of_nonneg_right hc_half (by positivity)
      linarith
    have hV₀'_half : (V₀.card : ℝ) / 2 ≤ (V₀'.card : ℝ) := by linarith
    have hV₀'_dens : (α / 2) * ((d * d * b : ℕ) : ℝ) ≤ (V₀'.card : ℝ) := by linarith
    obtain ⟨U, hUV₀', hacyc, hU_ge⟩ :=
      bridge_exists_isAcyclicIn_crossingLowerGT2H τ₀ hd hb hH hC (by positivity)
        hlen hT V₀' B hV₀'_dens hH_le hd_thresh hsep'
    have hUV₀ : U ⊆ V₀ := hUV₀'.trans (filter_subset _ V₀)
    have hρ_pos : 0 ≤ genieBridge_rho0 k C (α / 2) :=
      (genieBridge_rho0_pos k C (α / 2)).le
    have hU_half :
        (1 / 2 : ℝ) * genieBridge_rho0 k C (α / 2) * (V₀.card : ℝ) ≤ (U.card : ℝ) := by
      calc (1 / 2 : ℝ) * genieBridge_rho0 k C (α / 2) * (V₀.card : ℝ)
          = genieBridge_rho0 k C (α / 2) * ((V₀.card : ℝ) / 2) := by ring
        _ ≤ genieBridge_rho0 k C (α / 2) * (V₀'.card : ℝ) :=
            mul_le_mul_of_nonneg_left hV₀'_half hρ_pos
        _ ≤ (U.card : ℝ) := hU_ge
    exact ⟨B, hmenger, hB_lt, U, hUV₀, hacyc, hU_half⟩
  · right
    intro B hmenger
    by_contra hnot
    push Not at hnot
    exact hex ⟨B, hmenger, hnot⟩

end TraceOnlyDichotomy

/-! ## §4. Machine-Level Macroscopic Threshold Lift -/

section MacroscopicMachineLift

open scoped Classical

/-- Machine-level macroscopic excursion fraction `θ_macro(M, C, α) > 0` for Theorem X. -/
noncomputable def thetaMacro_genie (M : TM) (C α : ℝ) : ℝ :=
  thetaBridge_genie M.k (genieBridgeDepth M C (α / 2)) C (α / 2)

theorem thetaMacro_genie_pos (M : TM) (C : ℝ) {α : ℝ} (hα0 : 0 < α) :
    0 < thetaMacro_genie M C α :=
  thetaBridge_genie_pos M.k (genieBridgeDepth M C (α / 2)) C (by positivity)

/-- Machine-level dimension threshold for `S1` (`ensuring d ≥ 2 / θ_macro`, so `H_* = ⌊θ_macro L⌋₊ ≥ 1`
satisfies `θ_macro * L ≤ 2 * H_*` AND `W = d * entryBits d ≤ H_*`!). -/
noncomputable def d0Macro_genie (M : TM) (C α : ℝ) : ℕ :=
  max (max 1 (macroBridge_d0_genie M.k (genieBridgeDepth M C (α / 2)) C (α / 2)))
    ⌈2 / thetaMacro_genie M C α⌉₊

/-- **`D_E`-Path Separator Lower Bound at Arbitrary Threshold `1 ≤ H ≤ θ_E * L`:** -/
private theorem genie_obliviousLinTime_crossingLowerH_separator_lb {M : TM} {d T H ηInv L_cap : ℕ}
    {C α : ℝ} (hC : 1 ≤ C) (hα0 : 0 < α) (hH : 1 ≤ H)
    (hd : max 1 (timePullback_gen_d0 (bridgeChainCap M.k) C α) ≤ d)
    (hobl_lt : ObliviousLinTime M d (entryBits d) C T)
    (V₀ : Finset (Fin (d * d * entryBits d))) (B : Finset ℕ)
    (hV₀ : α * ((d * d * entryBits d : ℕ) : ℝ) ≤ (V₀.card : ℝ))
    (hH_le : (H : ℝ) ≤ thetaBridge_genie M.k (genieBridgeDepth M C α) C α *
      ((d * d * entryBits d : ℕ) : ℝ))
    (hsep : IsBallPathSeparator (traceAt M (d * d * entryBits d)) T (genieBridgeDepth M C α)
      d (entryBits d) V₀
      (crossingLowerEtaSteps (traceAt M (d * d * entryBits d)) T H ηInv L_cap) B)
    (hE1 : ClauseE1H (traceAt M (d * d * entryBits d)) T (genieBridgeDepth M C α)
      d (entryBits d) H ηInv L_cap V₀ B) :
    cE_genie M C α * (V₀.card : ℝ) ≤ (B.card : ℝ) := by
  have hd1 : 1 ≤ d := (le_max_left _ _).trans hd
  have hd_gen : timePullback_gen_d0 (bridgeChainCap M.k) C α ≤ d := (le_max_right _ _).trans hd
  obtain ⟨hobl, hT, htr⟩ := hobl_lt
  obtain ⟨_, hlen⟩ := obliviousTransposer_of_transposes hobl htr (fun _ => false)
  obtain ⟨U, _, hacyc, hU_ge⟩ :=
    bridge_exists_isAcyclicIn_crossingLowerH (traceAt M (d * d * entryBits d))
      hd1 (one_le_entryBits d) hH hC hα0 hlen hT V₀ B hV₀ hH_le hd_gen hsep hE1
  let ρ₀ := genieBridge_rho0 M.k C α
  let ε := α * ρ₀ / 4
  have hρ₀_pos : 0 < ρ₀ := genieBridge_rho0_pos M.k C α
  have hε_pos : 0 < ε := by dsimp [ε]; positivity
  have hsep_lb := obliviousLinTime_separator_card_ge_of_isAcyclicIn hd1 hC hε_pos
    ⟨hobl, hT, htr⟩ B U hacyc
  have hεL_le : ε * ((d * d * entryBits d : ℕ) : ℝ) ≤ (ρ₀ / 4) * (V₀.card : ℝ) := by
    calc ε * ((d * d * entryBits d : ℕ) : ℝ)
        = (ρ₀ / 4) * (α * ((d * d * entryBits d : ℕ) : ℝ)) := by dsimp [ε]; ring
      _ ≤ (ρ₀ / 4) * (V₀.card : ℝ) := mul_le_mul_of_nonneg_left hV₀ (by positivity)
  have hvw_ge : (ρ₀ / 2) * (V₀.card : ℝ) ≤ (valueWidth M : ℝ) * (B.card : ℝ) := by
    have : ρ₀ * (V₀.card : ℝ) ≤ (U.card : ℝ) := hU_ge
    linarith
  have hvw_pos : (0 : ℝ) < (valueWidth M : ℝ) := by
    have : (2 : ℝ) ≤ (valueWidth M : ℝ) := by exact_mod_cast two_le_valueWidth M
    linarith
  unfold cE_genie
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  calc ρ₀ * (V₀.card : ℝ)
      = 2 * ((ρ₀ / 2) * (V₀.card : ℝ)) := by ring
    _ ≤ 2 * ((valueWidth M : ℝ) * (B.card : ℝ)) := mul_le_mul_of_nonneg_left hvw_ge (by positivity)
    _ = (B.card : ℝ) * (2 * (valueWidth M : ℝ)) := by ring

/-- **Depth-`∞` Menger Vertex-Separator Lower Bound at Arbitrary Threshold `1 ≤ H ≤ θ_macro * L`:** -/
private theorem genie_obliviousLinTime_crossingLowerH_menger_lb {M : TM} {d T H ηInv L_cap : ℕ}
    {C α : ℝ} (hC : 1 ≤ C) (hα0 : 0 < α) (hH : 1 ≤ H)
    (hd : max 1 (timePullback_gen_d0 (bridgeChainCap M.k) C (α / 2)) ≤ d)
    (hobl_lt : ObliviousLinTime M d (entryBits d) C T)
    (V₀ : Finset (Fin (d * d * entryBits d))) (B : Finset ℕ)
    (hV₀ : α * ((d * d * entryBits d : ℕ) : ℝ) ≤ (V₀.card : ℝ))
    (hH_le : (H : ℝ) ≤ thetaMacro_genie M C α * ((d * d * entryBits d : ℕ) : ℝ))
    (hmenger : IsMengerVertexCut (traceAt M (d * d * entryBits d)).work T
      (V₀.image fun q => appendTime (traceAt M (d * d * entryBits d)) T
        (tposOf d (entryBits d) q).1)
      (crossingLowerEtaSteps (traceAt M (d * d * entryBits d)) T H ηInv L_cap) B)
    (hE1 : ClauseE1H (traceAt M (d * d * entryBits d)) T (genieBridgeDepth M C (α / 2))
      d (entryBits d) H ηInv L_cap
      (V₀.filter fun q => appendTime (traceAt M (d * d * entryBits d)) T
        (tposOf d (entryBits d) q).1 ∉ B) B) :
    (1 / 2 : ℝ) * cE_genie M C (α / 2) * (V₀.card : ℝ) ≤ (B.card : ℝ) := by
  let c_half := cE_genie M C (α / 2)
  have hc_pos : 0 < c_half := cE_genie_pos M C (α / 2)
  have hc_le_one : c_half ≤ 1 := by
    dsimp [c_half]
    unfold cE_genie
    have hrho_le := genieBridge_rho0_le_third M.k C (α / 2)
    have hvw : (2 : ℝ) ≤ (valueWidth M : ℝ) := by exact_mod_cast two_le_valueWidth M
    rw [div_le_iff₀ (by linarith)]
    linarith
  rcases le_or_gt ((V₀.card : ℝ) / 2) (B.card : ℝ) with hB_big | hB_small
  · have h1 : (1 / 2 : ℝ) * c_half * (V₀.card : ℝ) ≤ (1 / 2 : ℝ) * 1 * (V₀.card : ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc_le_one (by positivity)) (by positivity)
    linarith
  · obtain ⟨hobl, hT, htr⟩ := hobl_lt
    obtain ⟨_, hlen⟩ := obliviousTransposer_of_transposes hobl htr (fun _ => false)
    let V₀' := V₀.filter fun q => appendTime (traceAt M (d * d * entryBits d)) T
      (tposOf d (entryBits d) q).1 ∉ B
    obtain ⟨hcard_split, hsep'⟩ :=
      isBallPathSeparator_of_isMengerVertexCut (D := genieBridgeDepth M C (α / 2))
        (traceAt M (d * d * entryBits d)) hlen V₀ _ B hmenger
    have hcard_r : (V₀.card : ℝ) ≤ (V₀'.card : ℝ) + (B.card : ℝ) := by
      have hr : (V₀.card : ℝ) ≤ ((V₀'.card + B.card : ℕ) : ℝ) := by exact_mod_cast hcard_split
      simpa [Nat.cast_add] using hr
    have hV₀'_half : (V₀.card : ℝ) / 2 ≤ (V₀'.card : ℝ) := by linarith
    have hV₀'_dens : (α / 2) * ((d * d * entryBits d : ℕ) : ℝ) ≤ (V₀'.card : ℝ) := by linarith
    have hlb' := genie_obliviousLinTime_crossingLowerH_separator_lb hC (by positivity) hH hd
      ⟨hobl, hT, htr⟩ V₀' B hV₀'_dens hH_le hsep' hE1
    calc (1 / 2 : ℝ) * c_half * (V₀.card : ℝ)
        = c_half * ((V₀.card : ℝ) / 2) := by ring
      _ ≤ c_half * (V₀'.card : ℝ) := mul_le_mul_of_nonneg_left hV₀'_half hc_pos.le
      _ ≤ (B.card : ℝ) := hlb'

/-- **`S1` Main All-Thresholds Theorem (`Zero Extra Clauses`, Uncapped `> 2H` Crossing Lowers):**
For **every** oblivious linear-time transposer `(M, C)`, **every** `V₀` (`|V₀| ≥ α L`), **every**
hop threshold `1 ≤ H` with `(H : ℝ) ≤ thetaMacro_genie M C α * L` (`including H = W = d * b`
AND `H = ⌊thetaMacro_genie M C α * L⌋₊`), and **every** Menger vertex cut `B` disconnecting
`u₀(V₀)` from `crossingLowerEtaSteps τ₀ T H 1 T`,
`|B| ≥ (1 / 2) * cE_genie M C (α / 2) * |V₀|`! -/
private theorem genie_obliviousLinTime_crossingLowerGT2H_menger_lb {M : TM} {d T H : ℕ} {C α : ℝ}
    (hC : 1 ≤ C) (hα0 : 0 < α) (hH : 1 ≤ H)
    (hd : max 1 (timePullback_gen_d0 (bridgeChainCap M.k) C (α / 2)) ≤ d)
    (hobl_lt : ObliviousLinTime M d (entryBits d) C T)
    (V₀ : Finset (Fin (d * d * entryBits d))) (B : Finset ℕ)
    (hV₀ : α * ((d * d * entryBits d : ℕ) : ℝ) ≤ (V₀.card : ℝ))
    (hH_le : (H : ℝ) ≤ thetaMacro_genie M C α * ((d * d * entryBits d : ℕ) : ℝ))
    (hmenger : IsMengerVertexCut (traceAt M (d * d * entryBits d)).work T
      (V₀.image fun q => appendTime (traceAt M (d * d * entryBits d)) T
        (tposOf d (entryBits d) q).1)
      (crossingLowerEtaSteps (traceAt M (d * d * entryBits d)) T H 1 T) B) :
    (1 / 2 : ℝ) * cE_genie M C (α / 2) * (V₀.card : ℝ) ≤ (B.card : ℝ) :=
  genie_obliviousLinTime_crossingLowerH_menger_lb hC hα0 hH hd hobl_lt V₀ B hV₀ hH_le hmenger
    (clauseE1H_uncapped _ T _ d (entryBits d) H _ B)

/-- **`S1` Headline Payoff (`Linear Menger Expansion into Strictly Macroscopic Crossing Excursions`):**
For **every** oblivious linear-time transposer `(M, C)` and **every** `d ≥ d0Macro_genie M C α`,
setting `H_* := ⌊thetaMacro_genie M C α * L⌋₊` simultaneously satisfies:
1. `W = d * entryBits d ≤ H_*`,
2. `thetaMacro_genie M C α * L ≤ 2 * H_*` (`so every hop in crossingLowerEtaSteps τ₀ T H_* 1 T`
   has spatial excursion **strictly exceeding `thetaMacro_genie M C α * L`**!), and
3. **every** Menger vertex cut `B` from `u₀(V₀)` (`|V₀| ≥ α L`) to
   `crossingLowerEtaSteps τ₀ T H_* 1 T` satisfies `|B| ≥ (1 / 2) * c_E(M, C, α / 2) * |V₀|`! -/
theorem obliviousLinTime_macroscopicCrossingLowers_menger_lb_genie {M : TM} {d T : ℕ}
    {C α : ℝ} (hC : 1 ≤ C) (hα0 : 0 < α)
    (hd : d0Macro_genie M C α ≤ d)
    (hobl_lt : ObliviousLinTime M d (entryBits d) C T)
    (V₀ : Finset (Fin (d * d * entryBits d)))
    (hV₀ : α * ((d * d * entryBits d : ℕ) : ℝ) ≤ (V₀.card : ℝ)) :
    let L := d * d * entryBits d
    let H_star := ⌊thetaMacro_genie M C α * (L : ℝ)⌋₊
    d * entryBits d ≤ H_star ∧
      thetaMacro_genie M C α * (L : ℝ) ≤ (2 * H_star : ℕ) ∧
      ∀ B : Finset ℕ,
        IsMengerVertexCut (traceAt M L).work T
          (V₀.image fun q => appendTime (traceAt M L) T (tposOf d (entryBits d) q).1)
          (crossingLowerEtaSteps (traceAt M L) T H_star 1 T) B →
        (1 / 2 : ℝ) * cE_genie M C (α / 2) * (V₀.card : ℝ) ≤ (B.card : ℝ) := by
  intro L H_star
  have hd_left : max 1 (macroBridge_d0_genie M.k (genieBridgeDepth M C (α / 2)) C (α / 2)) ≤ d :=
    (le_max_left _ _).trans hd
  have hd1 : 1 ≤ d := (le_max_left _ _).trans hd_left
  have hd_macro : macroBridge_d0_genie M.k (genieBridgeDepth M C (α / 2)) C (α / 2) ≤ d :=
    (le_max_right _ _).trans hd_left
  have hd_gen : timePullback_gen_d0 (bridgeChainCap M.k) C (α / 2) ≤ d :=
    (le_max_left _ _).trans hd_macro
  have hd_2theta : ⌈2 / thetaMacro_genie M C α⌉₊ ≤ d := (le_max_right _ _).trans hd
  have hθ_pos : 0 < thetaMacro_genie M C α := thetaMacro_genie_pos M C hα0
  have hb1 : 1 ≤ entryBits d := one_le_entryBits d
  have hW_pos : 1 ≤ d * entryBits d := Nat.mul_pos hd1 hb1
  have hW_le_θL : ((d * entryBits d : ℕ) : ℝ) ≤ thetaMacro_genie M C α * (L : ℝ) :=
    rowWidth_le_theta_mul_L (by positivity) hd_macro
  have hW_le_H : d * entryBits d ≤ H_star :=
    Nat.le_floor hW_le_θL
  have hH_pos : 1 ≤ H_star := hW_pos.trans hW_le_H
  have hH_le_θL : (H_star : ℝ) ≤ thetaMacro_genie M C α * (L : ℝ) :=
    Nat.floor_le (by positivity)
  have h2_le_θL : (2 : ℝ) ≤ thetaMacro_genie M C α * (L : ℝ) := by
    have hge : 2 / thetaMacro_genie M C α ≤ (d : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hd_2theta)
    have hmul : 2 ≤ (d : ℝ) * thetaMacro_genie M C α := (div_le_iff₀ hθ_pos).mp hge
    have hd_le_L : (d : ℝ) ≤ (L : ℝ) := by
      have : d ≤ d * d * entryBits d := by
        calc d = d * 1 * 1 := by ring
          _ ≤ d * d * entryBits d := Nat.mul_le_mul (Nat.mul_le_mul le_rfl hd1) hb1
      exact_mod_cast this
    calc (2 : ℝ) ≤ (d : ℝ) * thetaMacro_genie M C α := hmul
      _ ≤ (L : ℝ) * thetaMacro_genie M C α :=
          mul_le_mul_of_nonneg_right hd_le_L hθ_pos.le
      _ = thetaMacro_genie M C α * (L : ℝ) := by ring
  have hθL_le_2H : thetaMacro_genie M C α * (L : ℝ) ≤ ((2 * H_star : ℕ) : ℝ) := by
    have hlt_succ : thetaMacro_genie M C α * (L : ℝ) < (H_star : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    have hH1 : (1 : ℝ) ≤ (H_star : ℝ) := by exact_mod_cast hH_pos
    push_cast
    linarith
  refine ⟨hW_le_H, hθL_le_2H, fun B hmenger => ?_⟩
  exact genie_obliviousLinTime_crossingLowerGT2H_menger_lb hC hα0 hH_pos
    (max_le hd1 hd_gen) hobl_lt V₀ B hV₀ hH_le_θL hmenger

end MacroscopicMachineLift

end NativeRelations
