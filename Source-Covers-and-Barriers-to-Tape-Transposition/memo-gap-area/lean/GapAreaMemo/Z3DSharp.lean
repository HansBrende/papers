import GapAreaMemo.Z3DCover
import GapAreaMemo.Z3DProtected

set_option autoImplicit false

/-!
# The dyadic sharpness geometry: the frozen gap area

At every admissible phase whose protected prefix has at least `16·2^ℓ`
families, the retained core contains every bank zigzag below `2^(ℓ+1)` (and
`C_i` below `2^(ℓ+2)`), so the time cover of `Z3DCover` applies to the root of
every column `j ≥ 1`. Its raw values are dense up to `rawX`, and the gap
bound of `GapBound` turns this into a bound on the frozen point area.
-/

namespace SourceCovers.Z3D.Index

open Finset Zigzag StairFamilies LeanMachine LeanMachine.SourceBank

variable (P : Index)

/-- The end of the covered time range. -/
def coverEnd (ℓ : ℕ) : ℕ := P.segStart (2 * 2 ^ ℓ - 1)

/-- The covered raw range. -/
def rawX (ℓ : ℕ) : ℕ := min ((P.coverEnd ℓ - 1) / P.slope) (P.L - 1)

theorem endC_le_OA : P.endC ≤ P.OA := by
  have h1 : P.endC ≤ P.σB P.K := by unfold σB; omega
  have h2 := P.σB_le_OB (k := P.K)
  have h3 := P.OB_lt_σA (k := 0)
  unfold OA; omega

theorem raw_root {j : ℕ} : P.raw (P.root j) = P.L - 1 := by
  have hs := P.slope_pos
  have hmul : P.slope * P.L ≤ P.endC - 1 := by
    unfold slope; exact Nat.div_mul_le_self _ _
  have hle : P.L ≤ (P.root j - 1) / P.slope := by
    rw [Nat.le_div_iff_mul_le hs]
    have := P.endC_le_OA
    unfold root out
    rw [mul_comm]; omega
  unfold raw; omega

theorem lev_lt_of_lt {ℓ i : ℕ} (hi : i < 2 * 2 ^ ℓ) : lev i ≤ ℓ := by
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · simp [lev]
  · have := Nat.log_lt_of_lt_pow (b := 2) (by omega) (show i < 2 ^ (ℓ + 1) by rw [pow_succ]; omega)
    unfold lev; omega

/-- The retained core at an admissible phase contains the families of block `ℓ`. -/
theorem needs_retained {ℓ R J M ρ : ℕ} (O : SortedCore P.core) (hR : 16 * 2 ^ ℓ ≤ R)
    (hRJ : R ≤ J) (hℓν : ℓ ≤ P.ν)
    (hρ : ρ ∈ admissiblePhases (O.selectedPrefix J) (O.subprefix J R) M) :
    P.Needs (retainedCore (O.selectedPrefix J) M ρ ∪ P.exceptions) ℓ := by
  refine ⟨fun i up h1 h2 => ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · exact mem_union_left _ (O.prefix_retained hRJ hρ
      (P.famA_protected hR O h1 (P.block_le_K hℓν h2) up (lev_lt_of_lt h2)))
  · exact mem_union_left _ (O.prefix_retained hRJ hρ
      (P.famB_protected hR O h1 (P.block_le_K hℓν h2) up (lev_lt_of_lt h2)))
  · exact mem_union_left _ (O.prefix_retained hRJ hρ
      (P.famC_protected hR O h1 (P.block_le_K hℓν h2) up (by have := lev_lt_of_lt h2; omega)))
  · exact mem_union_right _ (by simp [exceptions])
  · exact mem_union_right _ (by simp [exceptions])

theorem U_pos (k : ℕ) : 1 ≤ P.U k := by
  have := P.U_mono (Nat.zero_le k); simp only [U] at this ⊢; omega

theorem coverEnd_pos (ℓ : ℕ) : 1 ≤ P.coverEnd ℓ := by
  unfold coverEnd segStart
  have := P.U_pos ((2 * 2 ^ ℓ - 1) / 2)
  split_ifs <;> omega

/-- **The frozen point area at one admissible phase and one column `j ≥ 1`.** -/
theorem phase_bound {ℓ R J M ρ j : ℕ} (O : SortedCore P.core) (hM : 2 ≤ M)
    (hR : 16 * 2 ^ ℓ ≤ R) (hRJ : R ≤ J)
    (hρ : ρ ∈ admissiblePhases (O.selectedPrefix J) (O.subprefix J R) M)
    (hℓ6 : 6 ≤ ℓ) (hℓν : ℓ ≤ P.ν) (hα : 16 ≤ P.a (2 ^ ℓ)) (hj1 : 1 ≤ j) (hjd : j < P.d)
    (hgX : P.capG ℓ ≤ P.rawX ℓ) :
    phaseGapArea (P.core_coloring.mono (O.selectedPrefix_subset J)) hM P.exceptions P.raw P.out
        P.d P.b ρ j ≤
      (((P.capG ℓ + 1) * P.L + (P.L - P.rawX ℓ + P.capG ℓ + 1) ^ 2 : ℕ) : ℝ) /
        (2 * (P.L : ℝ) ^ 2) := by
  have hρM := admissiblePhase_lt hρ
  have hF := P.needs_retained O hR hRJ hℓν hρ
  have hex := exactSourceBank_exact (P.core_coloring.mono (O.selectedPrefix_subset J)) hM hρM
    P.exceptions
  rw [phaseGapArea_eq _ hM hρM]
  rw [← P.L_eq]
  have hroot : columnFirst P.out (P.d * P.b) j = P.root j := rfl
  simp only [hroot]
  have hmem : ∀ u ∈ shadowOrbit (retainedCore (O.selectedPrefix J) M ρ ∪ P.exceptions) (P.root j),
      P.raw u ∈ rawBankValues (exactSourceBank (ρ := ρ)
        (P.core_coloring.mono (O.selectedPrefix_subset J)) hM P.exceptions) P.raw (P.root j) := by
    intro u hu
    have : u ∈ (values (exactSourceBank (ρ := ρ)
        (P.core_coloring.mono (O.selectedPrefix_subset J)) hM P.exceptions) (P.root j) :
          Set ℕ) := by rw [hex]; exact hu
    exact mem_image_of_mem _ this
  apply SourceCovers.GapBound.pointArea_le_of_dense'
  · intro y hy
    obtain ⟨u, -, rfl⟩ := mem_image.mp hy
    exact mem_range.mpr (P.raw_lt u)
  · rw [← P.raw_root (j := j)]
    exact hmem _ (mem_shadowOrbit_self _ _)
  · exact hgX
  · intro u hu
    have hs := P.slope_pos
    have hX1 : P.rawX ℓ ≤ (P.coverEnd ℓ - 1) / P.slope := min_le_left _ _
    have hX2 : P.rawX ℓ ≤ P.L - 1 := min_le_right _ _
    have hmul : P.slope * ((P.coverEnd ℓ - 1) / P.slope) ≤ P.coverEnd ℓ - 1 := Nat.mul_div_le _ _
    have hcap : P.capG ℓ ≤ P.slope * P.capG ℓ := Nat.le_mul_of_pos_left _ hs
    have hce := P.coverEnd_pos ℓ
    have hz : 1 + P.slope * u + P.capG ℓ ≤ P.coverEnd ℓ := by
      have : P.slope * (u + P.capG ℓ) ≤ P.slope * ((P.coverEnd ℓ - 1) / P.slope) :=
        Nat.mul_le_mul_left _ (hu.trans hX1)
      rw [mul_add] at this
      omega
    obtain ⟨t, ht, ht1, ht2⟩ := P.time_cover _ hF hℓ6 hℓν hj1 hjd hα (1 + P.slope * u) (by omega)
      (by unfold coverEnd at hz; exact hz)
    refine ⟨P.raw t, hmem t ht, ?_, ?_⟩
    · unfold raw
      apply le_min
      · rw [Nat.le_div_iff_mul_le hs, mul_comm]; omega
      · omega
    · unfold raw
      apply (min_le_left _ _).trans
      apply Nat.div_le_of_le_mul
      rw [mul_add]
      omega

/-! ### Sizes -/

theorem a_anti {i k : ℕ} (hik : i ≤ k) (hkK : k ≤ P.K) : P.a k ≤ P.a i := by
  have he := P.exponent_ok hkK
  have hl := lev_mono hik
  unfold a
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem U_sub_le {W : ℕ} : ∀ k, W ≤ k → P.U k ≤ P.U W + 5 * ∑ i ∈ Ioc W k, P.cc i := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => simp
  | succ k hWk ih =>
    show P.U k + fC (k + 1) * P.cc (k + 1) + P.cc (k + 1) ≤ _
    rw [show Ioc W (k + 1) = insert (k + 1) (Ioc W k) by
      ext i; simp only [mem_Ioc, mem_insert]; omega, sum_insert (by simp)]
    have := Nat.mul_le_mul_right (P.cc (k + 1)) (fC_le_four (k + 1))
    omega

theorem sum_cc_Ioc (W : ℕ) : ∑ i ∈ Ioc W P.K, P.cc i = 8 * P.sumA W := by
  unfold cc sumA; rw [mul_sum]

theorem L_eq_alpha {ℓ : ℕ} (hℓν : ℓ ≤ P.ν) : P.L = 4 * 4 ^ ℓ * P.a (2 ^ ℓ) := by
  have h := P.L_eq_a (k := 2 ^ ℓ) (P.block_le_K hℓν (by have := Nat.one_le_two_pow (n := ℓ); omega))
  rwa [show lev (2 ^ ℓ) = ℓ from Nat.log_pow (by norm_num) ℓ] at h

theorem capG_eq {ℓ : ℕ} (hℓν : ℓ ≤ P.ν) :
    P.capG ℓ = 18432 * P.a (2 ^ ℓ) + 64 * 4 ^ ℓ + 6 := by
  have hL := P.L_eq_alpha hℓν
  have hα := P.a_pos (2 ^ ℓ)
  have hp : 0 < 4 ^ ℓ := by positivity
  unfold capG
  rw [hL]
  have e1 : 2 * (4 * 4 ^ ℓ * P.a (2 ^ ℓ)) * 1152 / 4 ^ ℓ = 9216 * P.a (2 ^ ℓ) := by
    rw [show 2 * (4 * 4 ^ ℓ * P.a (2 ^ ℓ)) * 1152 = 4 ^ ℓ * (9216 * P.a (2 ^ ℓ)) by ring,
      Nat.mul_div_cancel_left _ hp]
  have e2 : 2 * (4 * 4 ^ ℓ * P.a (2 ^ ℓ)) * 4 / P.a (2 ^ ℓ) = 32 * 4 ^ ℓ := by
    rw [show 2 * (4 * 4 ^ ℓ * P.a (2 ^ ℓ)) * 4 = P.a (2 ^ ℓ) * (32 * 4 ^ ℓ) by ring,
      Nat.mul_div_cancel_left _ hα]
  rw [e1, e2]
  ring

theorem endC_le : P.endC ≤ 1 + 22 * P.L := by
  have hU := P.U_le P.K
  rw [P.sum_cc] at hU
  have hhg : 2 * P.sumA 0 + 2 ≤ P.L := P.hg_add_le
  have hc := P.cc_le_two_L P.K
  unfold endC
  omega

theorem slope_le : P.slope ≤ 22 := by
  unfold slope
  apply Nat.div_le_of_le_mul
  have := P.endC_le
  rw [mul_comm]; omega

theorem slope_two : 2 ≤ P.slope := by
  unfold slope
  rw [Nat.le_div_iff_mul_le P.L_pos]
  have := P.endC_ge; omega

theorem coverEnd_eq (ℓ : ℕ) : P.coverEnd ℓ = P.U (2 ^ ℓ) - P.cc (2 ^ ℓ) := by
  have h2l := Nat.one_le_two_pow (n := ℓ)
  unfold coverEnd segStart
  rw [ite_eq_right (by omega), show (2 * 2 ^ ℓ - 1) / 2 = 2 ^ ℓ - 1 by omega,
    show 2 ^ ℓ - 1 + 1 = 2 ^ ℓ by omega]
  have : P.U (2 ^ ℓ) = P.U (2 ^ ℓ - 1) + fC (2 ^ ℓ) * P.cc (2 ^ ℓ) + P.cc (2 ^ ℓ) := by
    rw [P.U_eq _ h2l]
  omega

theorem coverEnd_ge {ℓ : ℕ} (hℓ : 1 ≤ ℓ) : 4 * P.L + 1 ≤ P.coverEnd ℓ := by
  have h2 : 2 ≤ 2 ^ ℓ := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ ℓ := Nat.pow_le_pow_right (by norm_num) hℓ
  unfold coverEnd segStart
  rw [ite_eq_right (by omega)]
  have h1 := P.U_mono (show 1 ≤ (2 * 2 ^ ℓ - 1) / 2 by omega)
  have hU1 : P.U 1 = 1 + fC 1 * P.cc 1 + P.cc 1 := rfl
  have hf1 : fC 1 = 1 := by unfold fC; simp
  have hc1 : P.cc 1 = 2 * P.L := by unfold cc; have := P.a_one; omega
  rw [hf1, hc1] at hU1
  omega

/-- The uncovered top of the raw range: `2 (L - rawX) ≤ endC - coverEnd + 22`. -/
theorem rawX_gap (ℓ : ℕ) : 2 * (P.L - P.rawX ℓ) ≤ P.endC - P.coverEnd ℓ + 22 := by
  have hs2 := P.slope_two
  have hs22 := P.slope_le
  have hmul : P.slope * P.L ≤ P.endC - 1 := by unfold slope; exact Nat.div_mul_le_self _ _
  have hlt := Nat.lt_div_mul_add (a := P.coverEnd ℓ - 1) (show 0 < P.slope by omega)
  have hce := P.coverEnd_pos ℓ
  unfold rawX
  generalize (P.coverEnd ℓ - 1) / P.slope = A at hlt ⊢
  rcases le_or_gt (P.L - 1) A with h | h
  · rw [min_eq_right h]; have := P.L_pos; omega
  · rw [min_eq_left h.le]
    obtain ⟨D, hD⟩ : ∃ D, P.L = A + D := ⟨P.L - A, by omega⟩
    rw [hD, mul_add] at hmul
    have h2D : 2 * D ≤ P.slope * D := Nat.mul_le_mul_right D hs2
    have hAs : A * P.slope = P.slope * A := mul_comm _ _
    rw [hD]
    generalize P.slope * A = SA at hmul hAs
    generalize P.slope * D = SD at hmul h2D
    omega

/-- The sizes in real form. -/
theorem endC_sub_cover {ℓ : ℕ} (hℓν : ℓ ≤ P.ν) :
    ((P.endC - P.coverEnd ℓ : ℕ) : ℝ) ≤ 80 * P.L / 2 ^ ℓ + 16 * P.a (2 ^ ℓ) := by
  have h2l := Nat.one_le_two_pow (n := ℓ)
  have hWK : 2 ^ ℓ ≤ P.K := P.block_le_K hℓν (by omega)
  have hUK := P.U_sub_le P.K hWK
  rw [P.sum_cc_Ioc] at hUK
  have hcK : P.cc P.K ≤ P.cc (2 ^ ℓ) := by
    unfold cc; have := P.a_anti hWK le_rfl; omega
  have hce := P.coverEnd_eq ℓ
  have hUge := P.U_ge (2 ^ ℓ) h2l
  have hnat : P.endC - P.coverEnd ℓ ≤ 40 * P.sumA (2 ^ ℓ) + 16 * P.a (2 ^ ℓ) := by
    unfold endC; rw [hce]; unfold cc at hcK hUge ⊢; omega
  have hs := P.sumA_le (2 ^ ℓ)
  have hW : (0 : ℝ) < 2 ^ ℓ := by positivity
  have hs' : (P.sumA (2 ^ ℓ) : ℝ) ≤ 2 * P.L / 2 ^ ℓ := by
    refine hs.trans ?_
    push_cast
    apply div_le_div_of_nonneg_left (by positivity) hW (by linarith)
  have : ((P.endC - P.coverEnd ℓ : ℕ) : ℝ) ≤ 40 * (P.sumA (2 ^ ℓ) : ℝ) + 16 * P.a (2 ^ ℓ) := by
    exact_mod_cast hnat
  have e : 40 * (2 * (P.L : ℝ) / 2 ^ ℓ) = 80 * P.L / 2 ^ ℓ := by ring
  linarith

/-- The final arithmetic, with `L = 4 W² α`. -/
theorem final_arith {W α g Q : ℝ} (hW : 256 ≤ W) (hα : W ^ 2 ≤ α)
    (hg : g ≤ 18432 * α + 64 * W ^ 2 + 6) (hQ : Q ≤ 160 * W * α + 18440 * α + 64 * W ^ 2 + 18)
    (hQ0 : 0 ≤ Q) :
    ((g + 1) * (4 * W ^ 2 * α) + Q ^ 2) / (2 * (4 * W ^ 2 * α) ^ 2) ≤ 4010 / W ^ 2 := by
  have hW0 : 0 < W := by linarith
  have hW2 : 65536 ≤ W ^ 2 := by nlinarith
  have hα0 : 0 < α := by nlinarith
  have hg' : g + 1 ≤ 18497 * α := by nlinarith
  have hQ' : Q ≤ 233 * W * α := by nlinarith
  have hQ2 : Q ^ 2 ≤ (233 * W * α) ^ 2 := by
    exact pow_le_pow_left₀ hQ0 hQ' 2
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : (g + 1) * (4 * W ^ 2 * α) ≤ 18497 * α * (4 * W ^ 2 * α) :=
    mul_le_mul_of_nonneg_right hg' (by positivity)
  nlinarith [sq_nonneg (W * α)]

/-! ### The bound at one phase and its mean -/

theorem two_nu_le_m : 2 * P.ν ≤ P.m := by
  unfold m
  have : ∀ j, 2 * j ≤ 2 ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ]
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · norm_num
      · have : 1 ≤ 2 ^ j := Nat.one_le_two_pow
        omega
  exact this _

theorem phase_le {ℓ R J M ρ j : ℕ} (O : SortedCore P.core) (hM : 2 ≤ M)
    (hR : 16 * 2 ^ ℓ ≤ R) (hRJ : R ≤ J)
    (hρ : ρ ∈ admissiblePhases (O.selectedPrefix J) (O.subprefix J R) M)
    (hℓ8 : 8 ≤ ℓ) (hℓν : ℓ ≤ P.ν) (hα : 4 ^ ℓ ≤ P.a (2 ^ ℓ)) (hj1 : 1 ≤ j) (hjd : j < P.d) :
    phaseGapArea (P.core_coloring.mono (O.selectedPrefix_subset J)) hM P.exceptions P.raw P.out
        P.d P.b ρ j ≤ 4010 / ((2 : ℝ) ^ ℓ) ^ 2 := by
  have hF : 65536 ≤ 4 ^ ℓ := by
    calc 65536 = 4 ^ 8 := by norm_num
      _ ≤ 4 ^ ℓ := Nat.pow_le_pow_right (by norm_num) hℓ8
  have hL := P.L_eq_alpha hℓν
  have hcap := P.capG_eq hℓν
  have hce := P.coverEnd_ge (ℓ := ℓ) (by omega)
  have hs22 := P.slope_le
  have hs2 := P.slope_two
  have hgX : P.capG ℓ ≤ P.rawX ℓ := by
    unfold rawX
    apply le_min
    · have h1 : 4 * P.L / 22 ≤ (P.coverEnd ℓ - 1) / P.slope :=
        (Nat.div_le_div_left hs22 (by omega)).trans (Nat.div_le_div_right (by omega))
      refine le_trans ?_ h1
      rw [Nat.le_div_iff_mul_le (by norm_num), hcap, hL]
      generalize 4 ^ ℓ = F at hF hα
      generalize P.a (2 ^ ℓ) = α at hα
      nlinarith
    · rw [hcap, hL]
      generalize 4 ^ ℓ = F at hF hα
      generalize P.a (2 ^ ℓ) = α at hα
      have h1 : 65536 * α ≤ F * α := Nat.mul_le_mul_right α hF
      have h2 : 18432 * α + 64 * F + 7 ≤ 4 * F * α := by nlinarith
      omega
  have hpb := P.phase_bound O hM hR hRJ hρ (by omega) hℓν (by omega) hj1 hjd hgX
  refine hpb.trans ?_
  -- real forms
  have hgap := P.rawX_gap ℓ
  have hes := P.endC_sub_cover hℓν
  have hW : (256 : ℝ) ≤ 2 ^ ℓ := by
    calc (256 : ℝ) = 2 ^ 8 := by norm_num
      _ ≤ 2 ^ ℓ := pow_le_pow_right₀ (by norm_num) hℓ8
  have h4 : ((4 : ℝ) ^ ℓ) = ((2 : ℝ) ^ ℓ) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hαr : ((2 : ℝ) ^ ℓ) ^ 2 ≤ (P.a (2 ^ ℓ) : ℝ) := by rw [← h4]; exact_mod_cast hα
  have hLr : (P.L : ℝ) = 4 * ((2 : ℝ) ^ ℓ) ^ 2 * P.a (2 ^ ℓ) := by
    rw [← h4]; exact_mod_cast hL
  have hcapr : (P.capG ℓ : ℝ) ≤ 18432 * P.a (2 ^ ℓ) + 64 * ((2 : ℝ) ^ ℓ) ^ 2 + 6 := by
    rw [← h4]; exact_mod_cast hcap.le
  have hgapr : 2 * ((P.L - P.rawX ℓ : ℕ) : ℝ) ≤ ((P.endC - P.coverEnd ℓ : ℕ) : ℝ) + 22 := by
    exact_mod_cast hgap
  have hQ : ((P.L - P.rawX ℓ + P.capG ℓ + 1 : ℕ) : ℝ) ≤
      160 * 2 ^ ℓ * P.a (2 ^ ℓ) + 18440 * P.a (2 ^ ℓ) + 64 * ((2 : ℝ) ^ ℓ) ^ 2 + 18 := by
    push_cast
    have e : 80 * (P.L : ℝ) / 2 ^ ℓ = 320 * 2 ^ ℓ * P.a (2 ^ ℓ) := by
      rw [hLr]; field_simp; ring
    rw [e] at hes
    linarith
  have hfin := final_arith hW hαr hcapr hQ (by positivity)
  rw [← hLr] at hfin
  have e : (((P.capG ℓ + 1) * P.L + (P.L - P.rawX ℓ + P.capG ℓ + 1) ^ 2 : ℕ) : ℝ) =
      ((P.capG ℓ : ℝ) + 1) * P.L + ((P.L - P.rawX ℓ + P.capG ℓ + 1 : ℕ) : ℝ) ^ 2 := by
    push_cast; ring
  rw [e]
  exact hfin

theorem mean_le_aux {A : Finset ℕ} {d : ℕ} (hd : 0 < d) (φ : ℕ → ℕ → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (h0 : ∀ ρ ∈ A, φ ρ 0 ≤ 1 / 2) (h1 : ∀ ρ ∈ A, ∀ j, 1 ≤ j → j < d → φ ρ j ≤ B) :
    (∑ ρ ∈ A, ∑ j ∈ range d, φ ρ j) / (A.card * d) ≤ 1 / (2 * d) + B := by
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  have hrow : ∀ ρ ∈ A, ∑ j ∈ range (d' + 1), φ ρ j ≤ 1 / 2 + ((d' + 1 : ℕ) : ℝ) * B := by
    intro ρ hρ
    rw [sum_range_succ']
    have hs : ∑ j ∈ range d', φ ρ (j + 1) ≤ ∑ _j ∈ range d', B :=
      sum_le_sum (fun j hj => h1 ρ hρ (j + 1) (by omega) (by simp only [mem_range] at hj; omega))
    simp only [sum_const, card_range, nsmul_eq_mul] at hs
    have := h0 ρ hρ
    push_cast
    nlinarith
  have hsum : ∑ ρ ∈ A, ∑ j ∈ range (d' + 1), φ ρ j ≤ A.card * (1 / 2 + ((d' + 1 : ℕ) : ℝ) * B) := by
    calc _ ≤ ∑ _ρ ∈ A, (1 / 2 + ((d' + 1 : ℕ) : ℝ) * B) := sum_le_sum hrow
      _ = _ := by simp only [sum_const, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos A.card with h | h
  · rw [h]; simp only [Nat.cast_zero, zero_mul, div_zero]; positivity
  · have hA : (0 : ℝ) < A.card := by exact_mod_cast h
    have hd' : (0 : ℝ) < ((d' + 1 : ℕ) : ℝ) := by positivity
    rw [div_le_iff₀ (by positivity)]
    calc _ ≤ (A.card : ℝ) * (1 / 2 + ((d' + 1 : ℕ) : ℝ) * B) := hsum
      _ = (1 / (2 * ((d' + 1 : ℕ) : ℝ)) + B) * (A.card * ((d' + 1 : ℕ) : ℝ)) := by
        field_simp

/-- **The mean frozen point area of the sharpness geometry.** -/
theorem mean_le (β : ℝ) (hβ : 0 ≤ β) {ℓ R J M : ℕ} (O : SortedCore P.core) (hM : 2 ≤ M)
    (hR : 16 * 2 ^ ℓ ≤ R) (hRJ : R ≤ J) (hℓ8 : 8 ≤ ℓ) (hℓν : ℓ ≤ P.ν)
    (hα : 4 ^ ℓ ≤ P.a (2 ^ ℓ)) :
    (P.geometry β hβ).prefixMeanGapArea O J R M hM ≤ 1 / (2 * P.d) + 4010 / ((2 : ℝ) ^ ℓ) ^ 2 := by
  have hd := P.d_pos'
  show (∑ ρ ∈ admissiblePhases (O.selectedPrefix J) (O.subprefix J R) M, ∑ j ∈ range P.d,
      phaseGapArea (P.core_coloring.mono (O.selectedPrefix_subset J)) hM P.exceptions P.raw P.out
        P.d P.b ρ j) / ((admissiblePhases (O.selectedPrefix J) (O.subprefix J R) M).card * P.d) ≤ _
  apply mean_le_aux hd _ (by positivity)
  · intro ρ hρ
    exact (phaseGapArea_bounds (P.core_coloring.mono (O.selectedPrefix_subset J)) hM
      (admissiblePhase_lt hρ) P.exceptions P.raw P.out hd P.b_pos hd
      (fun z hz => P.out_lt (by rw [P.L_eq]; exact hz))
      (fun s _ => by rw [← P.L_eq]; exact P.raw_lt s)).2
  · intro ρ hρ j hj1 hjd
    exact P.phase_le O hM hR hRJ hρ hℓ8 hℓν hα hj1 hjd

/-- **Theorem (sharpness of Theorem G at `M = 2R+2`).** For every `R ≥ 1` and every geometry of
the sequence with `R ≤ 2^ν`, in every hop order and at every prefix `J ≥ R`, the mean frozen point
area of the protected prefix is at most `10^7 / R²`. -/
theorem gap_area_le (β : ℝ) (hβ : 0 ≤ β) {R M : ℕ} (hR1 : 1 ≤ R) (hRM : R < M)
    (hν : R ≤ 2 ^ P.ν) (O : SortedCore P.core) {J : ℕ} (hRJ : R ≤ J) :
    (P.geometry β hβ).prefixMeanGapArea O J R M (by omega) ≤ 10 ^ 7 / (R : ℝ) ^ 2 := by
  have hb := (P.geometry β hβ).prefixMeanGapArea_bounds O (J := J) (R := R) (M := M)
    (by omega) hRM
  have hRr : (1 : ℝ) ≤ R := by exact_mod_cast hR1
  by_cases hs : (R : ℝ) ^ 2 ≤ 2 * 10 ^ 7
  · refine hb.2.trans ?_
    rw [le_div_iff₀ (by positivity)]
    linarith
  · replace hs := not_le.mp hs
    have hR4096 : 4096 ≤ R := by
      by_contra h
      have : (R : ℝ) ≤ 4095 := by exact_mod_cast (by omega : R ≤ 4095)
      nlinarith
    have hlog : 12 ≤ Nat.log 2 R := Nat.le_log_of_pow_le (by norm_num) (by norm_num; omega)
    set ℓ := Nat.log 2 R - 4 with hℓ
    have hpow : 2 ^ Nat.log 2 R = 16 * 2 ^ ℓ := by
      rw [show Nat.log 2 R = ℓ + 4 by omega, pow_add]; ring
    have h16 : 16 * 2 ^ ℓ ≤ R := by rw [← hpow]; exact Nat.pow_log_le_self 2 (by omega)
    have h32 : R < 32 * 2 ^ ℓ := by
      have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) R
      rw [pow_succ, hpow] at this; omega
    have hℓ8 : 8 ≤ ℓ := by omega
    have hℓν : ℓ ≤ P.ν := by
      have := Nat.log_mono_right (b := 2) hν
      rw [Nat.log_pow (by norm_num)] at this; omega
    have hmν := P.two_nu_le_m
    have hα : 4 ^ ℓ ≤ P.a (2 ^ ℓ) := by
      unfold a
      rw [show lev (2 ^ ℓ) = ℓ from Nat.log_pow (by norm_num) ℓ,
        show (4 : ℕ) ^ ℓ = 2 ^ (2 * ℓ) by rw [pow_mul]; norm_num]
      exact Nat.pow_le_pow_right (by norm_num) (by unfold n; have := P.hν; omega)
    have hdW : ((2 : ℝ) ^ ℓ) ^ 2 ≤ P.d := by
      have : (2 : ℕ) ^ (2 * ℓ) ≤ P.d := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [← pow_mul, mul_comm]; exact_mod_cast this
    have hmean := P.mean_le β hβ (M := M) O (by omega) h16 hRJ hℓ8 hℓν hα
    have hW0 : (0 : ℝ) < ((2 : ℝ) ^ ℓ) ^ 2 := by positivity
    have hd1 : 1 / (2 * (P.d : ℝ)) ≤ 1 / ((2 : ℝ) ^ ℓ) ^ 2 := by
      apply one_div_le_one_div_of_le hW0; linarith
    have hR32 : (R : ℝ) < 32 * 2 ^ ℓ := by exact_mod_cast h32
    have hW2 : (R : ℝ) ^ 2 < 1024 * ((2 : ℝ) ^ ℓ) ^ 2 := by nlinarith
    have hfin : 4011 / ((2 : ℝ) ^ ℓ) ^ 2 ≤ 10 ^ 7 / (R : ℝ) ^ 2 := by
      rw [div_le_div_iff₀ hW0 (by positivity)]
      nlinarith
    have e : 1 / ((2 : ℝ) ^ ℓ) ^ 2 + 4010 / ((2 : ℝ) ^ ℓ) ^ 2 = 4011 / ((2 : ℝ) ^ ℓ) ^ 2 := by ring
    linarith

/-- **The paid hop tail of the sharpness geometry.** -/
theorem hop_tail (β : ℝ) (hβ : 0 ≤ β) {R : ℕ} (hR1 : 1 ≤ R) (hν : 4 * R ≤ 2 ^ P.ν)
    (O : SortedCore P.core) {J : ℕ} (hJ : 64 * R ≤ J) :
    (1 : ℝ) / (32 * R) ≤ ∑ i ∈ Ico R J, O.hopProfile (P.geometry β hβ).inputLength i := by
  have h : (P.geometry β hβ).inputLength = P.L := P.L_eq.symm
  rw [h]
  exact P.hop_tail_ge_of_le hR1 hν O hJ

/-- **Corollary: the frozen gap-area condition (GA) holds on the sharpness geometry**, at every
finite stage, at every modulus `M` with `32·10^7 (M - R) ≤ β R`. -/
theorem gap_area_condition (β : ℝ) (hβ : 0 ≤ β) {R M : ℕ} (hR1 : 1 ≤ R) (hRM : R < M)
    (hβM : 32 * 10 ^ 7 * ((M - R : ℕ) : ℝ) ≤ β * R) (hν : 4 * R ≤ 2 ^ P.ν)
    (O : SortedCore P.core) {J : ℕ} (hJ : 64 * R ≤ J) :
    (P.geometry β hβ).prefixMeanGapArea O J R M (by omega) ≤
      β * (∑ i ∈ Ico R J, O.hopProfile (P.geometry β hβ).inputLength i) / ((M - R : ℕ) : ℝ) := by
  have hg := P.gap_area_le β hβ hR1 hRM (by omega) O (J := J) (by omega)
  have ht := P.hop_tail β hβ hR1 hν O hJ
  have hRr : (1 : ℝ) ≤ R := by exact_mod_cast hR1
  have hD : (0 : ℝ) < ((M - R : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < M - R)
  refine hg.trans ?_
  rw [le_div_iff₀ hD]
  have h1 : β * (1 / (32 * (R : ℝ))) ≤
      β * ∑ i ∈ Ico R J, O.hopProfile (P.geometry β hβ).inputLength i :=
    mul_le_mul_of_nonneg_left ht hβ
  have h2 : 10 ^ 7 / (R : ℝ) ^ 2 * ((M - R : ℕ) : ℝ) ≤ β * (1 / (32 * (R : ℝ))) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    field_simp
    nlinarith
  linarith

/-- The case `M = 2R+2` with `β ≥ 10^9`. -/
theorem gap_area_condition_default (β : ℝ) (hβ : 10 ^ 9 ≤ β) {R : ℕ} (hR1 : 1 ≤ R)
    (hν : 4 * R ≤ 2 ^ P.ν) (O : SortedCore P.core) {J : ℕ} (hJ : 64 * R ≤ J) :
    (P.geometry β (by linarith)).prefixMeanGapArea O J R (2 * R + 2) (by omega) ≤
      β * (∑ i ∈ Ico R J, O.hopProfile (P.geometry β (by linarith)).inputLength i) / (R + 2) := by
  have hRr : (1 : ℝ) ≤ R := by exact_mod_cast hR1
  have e : ((2 * R + 2 - R : ℕ) : ℝ) = R + 2 := by
    rw [show 2 * R + 2 - R = R + 2 by omega]; push_cast; ring
  have h := P.gap_area_condition β (by linarith) hR1 (M := 2 * R + 2) (by omega)
    (by rw [e]; nlinarith) hν O hJ
  rwa [e] at h

end SourceCovers.Z3D.Index
