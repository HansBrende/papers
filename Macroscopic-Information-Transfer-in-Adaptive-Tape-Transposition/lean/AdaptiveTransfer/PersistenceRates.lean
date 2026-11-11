import LeanMachine.PolynomialMenus
import LeanMachine.FiniteTimeGrid
import AdaptiveTransfer.SparseRates
import Mathlib

/-! Quantitative persistence rates for the literal floor/ceiling menus.
These estimates assemble finite catalogue escape arguments. They do not
assert the separate native catalogue or future-readable eraser theorem.
-/

namespace AdaptiveTransfer.PersistenceRates

open LeanMachine Finset

noncomputable def alpha (h₀ : ℝ) : ℝ := h₀ / 4
noncomputable def beta (h₀ : ℝ) (A : ℕ) : ℝ := h₀ / (4 * Real.logb 2 (6 * A))
noncomputable def topSize (α : ℝ) (P : ℕ) : ℕ := ⌈(2 : ℝ) ^ (α * P)⌉₊
noncomputable def radius (β : ℝ) (P : ℕ) : ℕ := ⌊β * P⌋₊
noncomputable def intervalLength (β : ℝ) (P : ℕ) : ℕ := radius β P / 2
noncomputable def catalogue (h₀ : ℝ) (A P : ℕ) : ℕ :=
  (radius (beta h₀ A) P + 1) ^ 2 * topSize (alpha h₀) P *
    (6 * A) ^ (radius (beta h₀ A) P + 1)

theorem alpha_pos {h₀ : ℝ} (hh : 0 < h₀) : 0 < alpha h₀ := by unfold alpha; positivity

theorem log_degree_pos {A : ℕ} (hA : 1 ≤ A) : 0 < Real.logb 2 (6 * A) := by
  apply Real.logb_pos (by norm_num)
  have ha : (1 : ℝ) ≤ A := by exact_mod_cast hA
  linarith

theorem beta_pos {h₀ : ℝ} {A : ℕ} (hh : 0 < h₀) (hA : 1 ≤ A) : 0 < beta h₀ A := by
  unfold beta
  exact div_pos hh (mul_pos (by norm_num) (log_degree_pos hA))

theorem topSize_pos (α : ℝ) (P : ℕ) : 0 < topSize α P :=
  Nat.ceil_pos.mpr (Real.rpow_pos_of_pos (by norm_num) _)

theorem topSize_lower (α : ℝ) (P : ℕ) : (2 : ℝ) ^ (α * P) ≤ topSize α P := Nat.le_ceil _

theorem topSize_upper {α : ℝ} (hα : 0 ≤ α) (P : ℕ) :
    (topSize α P : ℝ) ≤ 2 * (2 : ℝ) ^ (α * P) := by
  have hp : (1 : ℝ) ≤ (2 : ℝ) ^ (α * P) := Real.one_le_rpow (by norm_num) (by positivity)
  have hc := Nat.ceil_lt_add_one (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (α * P))
  change (topSize α P : ℝ) < (2 : ℝ) ^ (α * P) + 1 at hc
  linarith

theorem topSize_log_upper {α : ℝ} (hα : 0 ≤ α) (P : ℕ) :
    Real.logb 2 (topSize α P) ≤ α * P + 1 := by
  apply (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2)
    (by exact_mod_cast topSize_pos α P)).mpr
  rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one, mul_comm]
  exact topSize_upper hα P

theorem topSize_log_lower (α : ℝ) (P : ℕ) : α * P ≤ Real.logb 2 (topSize α P + 1) := by
  apply (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) (by positivity)).mpr
  exact (topSize_lower α P).trans (le_add_of_nonneg_right (by norm_num))

theorem radius_le_linear {β : ℝ} (hβ : 0 ≤ β) (P : ℕ) : (radius β P : ℝ) ≤ β * P :=
  Nat.floor_le (by positivity)

theorem radius_add_one_polynomial {β : ℝ} (hβ : 0 ≤ β) (P : ℕ) :
    radius β P + 1 ≤ (⌈β⌉₊ + 1) * (P + 1) := by
  have hr := radius_le_linear hβ P
  have hc := mul_le_mul_of_nonneg_right (Nat.le_ceil β) (Nat.cast_nonneg (α := ℝ) P)
  have hh : radius β P ≤ ⌈β⌉₊ * P := by exact_mod_cast hr.trans hc
  nlinarith

theorem radius_log_budget {h₀ : ℝ} {A : ℕ} (hh : 0 < h₀) (hA : 1 ≤ A) (P : ℕ) :
    (radius (beta h₀ A) P : ℝ) * Real.logb 2 (6 * A) ≤ alpha h₀ * P := by
  have hl := log_degree_pos hA
  have hr := mul_le_mul_of_nonneg_right (radius_le_linear (beta_pos hh hA).le P) hl.le
  have he : beta h₀ A * P * Real.logb 2 (6 * A) = alpha h₀ * P := by
    unfold beta alpha
    field_simp
  exact hr.trans_eq he

noncomputable def catalogueOverhead (h₀ : ℝ) (A P : ℕ) : ℕ :=
  2 * (6 * A) * (radius (beta h₀ A) P + 1) ^ 2

theorem catalogue_pos {h₀ : ℝ} {A : ℕ} (hA : 1 ≤ A) (P : ℕ) : 0 < catalogue h₀ A P := by
  unfold catalogue
  exact mul_pos (mul_pos (by positivity) (topSize_pos _ _)) (pow_pos (by omega) _)

theorem catalogue_log_overhead {h₀ : ℝ} {A : ℕ} (hh : 0 < h₀) (hA : 1 ≤ A) (P : ℕ) :
    Real.logb 2 (catalogue h₀ A P) ≤ Real.logb 2 (catalogueOverhead h₀ A P) + h₀ / 2 * P := by
  have hk := topSize_log_upper (alpha_pos hh).le P
  have hr := radius_log_budget hh hA P
  have hp : (0 : ℝ) < topSize (alpha h₀) P := by exact_mod_cast topSize_pos (alpha h₀) P
  have hAp : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
  have hcat : Real.logb 2 (catalogue h₀ A P) =
      2 * Real.logb 2 (radius (beta h₀ A) P + 1) + Real.logb 2 (topSize (alpha h₀) P) +
        ((radius (beta h₀ A) P : ℝ) + 1) * Real.logb 2 (6 * A) := by
    unfold catalogue
    push_cast
    rw [Real.logb_mul (by positivity) (by positivity), Real.logb_mul (by positivity) hp.ne',
      Real.logb_pow, Real.logb_pow]
    norm_num
  have hover : Real.logb 2 (catalogueOverhead h₀ A P) =
      1 + Real.logb 2 (6 * A) + 2 * Real.logb 2 (radius (beta h₀ A) P + 1) := by
    unfold catalogueOverhead
    push_cast
    rw [Real.logb_mul (by positivity) (by positivity),
      Real.logb_mul (by norm_num) (by positivity), Real.logb_pow]
    norm_num
  rw [hcat, hover]
  unfold alpha at hk hr ⊢
  nlinarith

/-- The literal catalogue, including the top-set ceiling and the graph-ball
constant, fits the desired integer bit budget beyond one finite threshold. -/
theorem catalogue_bits_small {h₀ : ℝ} {A : ℕ} (hh : 0 < h₀) (hA : 1 ≤ A) :
    ∃ P₀ : ℕ, ∀ P, P₀ ≤ P → (⌈Real.logb 2 (catalogue h₀ A P)⌉₊ : ℝ) ≤ h₀ * P := by
  obtain ⟨P₁, hpoly⟩ := polynomial_menu_logb_small
    (show 1 ≤ 2 * (6 * A) by omega)
    (show 1 ≤ ⌈beta h₀ A⌉₊ + 1 by omega) (e := 2)
    (show 0 < h₀ / 4 by positivity)
  refine ⟨max P₁ ⌈4 / h₀⌉₊, ?_⟩
  intro P hP
  have hover : Real.logb 2 (catalogueOverhead h₀ A P) ≤ h₀ / 4 * P := by
    apply hpoly P ((le_max_left _ _).trans hP) _ (by
      have hp : 0 < catalogueOverhead h₀ A P := by unfold catalogueOverhead; positivity
      omega)
    unfold catalogueOverhead
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
      (radius_add_one_polynomial (beta_pos hh hA).le P) _)
  have hlarge : 4 ≤ h₀ * P := by
    have hc := (Nat.le_ceil (4 / h₀)).trans
      (show (⌈4 / h₀⌉₊ : ℝ) ≤ P by exact_mod_cast (le_max_right _ _).trans hP)
    have hd := (div_le_iff₀ hh).mp hc
    nlinarith
  have hlog := catalogue_log_overhead hh hA P
  have hnonneg : 0 ≤ Real.logb 2 (catalogue h₀ A P) := by
    apply Real.logb_nonneg (by norm_num)
    exact_mod_cast catalogue_pos hA P
  have hceil := Nat.ceil_lt_add_one hnonneg
  nlinarith

noncomputable def choiceMenu (k m : ℕ) (C β : ℝ) : ℕ :=
  k.choose m * (⌈8 * C / β⌉₊ + 1)

noncomputable def selectionMass (k m : ℕ) (C β : ℝ) : ℝ :=
  1 / (2 * choiceMenu k m C β)

theorem choiceMenu_pos {k m : ℕ} (hm : m ≤ k) (C β : ℝ) :
    0 < choiceMenu k m C β := Nat.mul_pos (Nat.choose_pos hm) (Nat.succ_pos _)

theorem selectionMass_pos {k m : ℕ} (hm : m ≤ k) (C β : ℝ) :
    0 < selectionMass k m C β := by
  unfold selectionMass
  have hp : (0 : ℝ) < choiceMenu k m C β := by exact_mod_cast choiceMenu_pos hm C β
  positivity

/-- Literal floor radii give linear-length intervals and a constant number
of unordered tape-set/grid choices at every sufficiently large length. -/
theorem grid_rates {β C : ℝ} (hβ : 0 < β) (hC : 0 ≤ C) (k m : ℕ) :
    ∃ P₀ : ℕ, ∀ P, P₀ ≤ P → ∀ T : ℕ, (T : ℝ) ≤ C * (P + 1) →
      2 ≤ radius β P ∧ 0 < intervalLength β P ∧
      β * P / 4 ≤ intervalLength β P ∧
      k.choose m * (T / intervalLength β P + 1) ≤ choiceMenu k m C β := by
  refine ⟨max 1 ⌈4 / β⌉₊, ?_⟩
  intro P hP T hT
  have hP1 : 1 ≤ P := (le_max_left _ _).trans hP
  have hPr : (1 : ℝ) ≤ P := by exact_mod_cast hP1
  have hlarge : 4 ≤ β * P := by
    have hc := (Nat.le_ceil (4 / β)).trans
      (show (⌈4 / β⌉₊ : ℝ) ≤ P by exact_mod_cast (le_max_right _ _).trans hP)
    have hd := (div_le_iff₀ hβ).mp hc
    nlinarith
  have hR : 4 ≤ radius β P := Nat.le_floor hlarge
  have hell : 0 < intervalLength β P := by unfold intervalLength; omega
  have hlen : β * P / 4 ≤ intervalLength β P := FiniteTimeGrid.floor_half_length hlarge
  refine ⟨by omega, hell, hlen, ?_⟩
  apply Nat.mul_le_mul_left
  apply FiniteTimeGrid.grid_count_le hell hβ (by linarith) hlen
  calc
    (T : ℝ) ≤ C * (P + 1) := hT
    _ ≤ 2 * C * P := by nlinarith

private theorem polynomial_rpow_small {A B e : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ P₀ : ℕ, ∀ P, P₀ ≤ P → ((A * (B * (P + 1)) ^ e : ℕ) : ℝ) ≤ (2 : ℝ) ^ (ε * P) := by
  obtain ⟨P₀, hh⟩ := polynomial_menu_logb_small hA hB (e := e) hε
  refine ⟨P₀, fun P hP => ?_⟩
  have hp : 0 < A * (B * (P + 1)) ^ e := by positivity
  exact (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2)
    (by exact_mod_cast hp)).mp (hh P hP _ (by omega) le_rfl)

noncomputable def atomPolynomialScale (C β : ℝ) : ℕ := 2 * ⌈C⌉₊ + ⌈β⌉₊ + 2

theorem time_factor_polynomial {β C : ℝ} {P T : ℕ}
    (hT : (T : ℝ) ≤ C * (P + 1)) :
    2 * T + 1 ≤ atomPolynomialScale C β * (P + 1) := by
  have ht : T ≤ ⌈C⌉₊ * (P + 1) := by
    exact_mod_cast hT.trans (mul_le_mul_of_nonneg_right (Nat.le_ceil C) (by positivity))
  unfold atomPolynomialScale
  nlinarith

theorem interval_factor_polynomial {β C : ℝ} (hβ : 0 ≤ β) (P : ℕ) :
    intervalLength β P ≤ atomPolynomialScale C β * (P + 1) := by
  have hi : intervalLength β P ≤ radius β P + 1 := by unfold intervalLength; omega
  apply hi.trans ((radius_add_one_polynomial hβ P).trans ?_)
  unfold atomPolynomialScale
  exact Nat.mul_le_mul_right _ (by omega)

/-- The actual conditional-atom factor, including the head fibre, interval
length, top-set ceiling and fixed selected-cell mass, is exponentially small. -/
theorem conditional_atom_rate {α β C : ℝ} {M : ℕ}
    (hα : 0 < α) (hβ : 0 ≤ β) (hM : 1 ≤ M) :
    ∃ P₀ : ℕ, ∀ P, P₀ ≤ P → ∀ T : ℕ, (T : ℝ) ≤ C * (P + 1) →
      2 * (2 * T + 1 : ℕ) * (intervalLength β P : ℝ) /
        ((topSize α P + 1) * (1 / (2 * (M : ℝ)))) ≤ (2 : ℝ) ^ (-α * P / 2) := by
  obtain ⟨P₀, hpoly⟩ := polynomial_rpow_small
    (show 1 ≤ 4 * M by omega) (show 1 ≤ atomPolynomialScale C β by unfold atomPolynomialScale; omega)
    (e := 2) (show 0 < α / 2 by positivity)
  refine ⟨P₀, ?_⟩
  intro P hP T hT
  have hMr : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hK : (0 : ℝ) < topSize α P + 1 := by positivity
  have hnum : ((4 * M * (2 * T + 1) * intervalLength β P : ℕ) : ℝ) ≤
      (2 : ℝ) ^ (α / 2 * P) := by
    apply le_trans _ (hpoly P hP)
    exact_mod_cast (show 4 * M * (2 * T + 1) * intervalLength β P ≤
        4 * M * (atomPolynomialScale C β * (P + 1)) ^ 2 by
      have ht := time_factor_polynomial (β := β) hT
      have hi := interval_factor_polynomial (C := C) hβ P
      calc
        _ ≤ 4 * M * (atomPolynomialScale C β * (P + 1)) *
            (atomPolynomialScale C β * (P + 1)) := by gcongr
        _ = _ := by ring)
  have hden : (2 : ℝ) ^ (α * P) ≤ topSize α P + 1 :=
    (topSize_lower α P).trans (le_add_of_nonneg_right (by norm_num))
  calc
    _ = ((4 * M * (2 * T + 1) * intervalLength β P : ℕ) : ℝ) /
        (topSize α P + 1) := by push_cast; field_simp; ring
    _ ≤ (2 : ℝ) ^ (α / 2 * P) / (2 : ℝ) ^ (α * P) :=
      div_le_div₀ (by positivity) hnum (by positivity) hden
    _ = (2 : ℝ) ^ (-α * P / 2) := by
      rw [← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring

/-- Complete ordinary rate assembly for the literal escape-selection
construction. The variable `p` is the mass of the original escape event;
the separate native catalogue theorem is needed to supply `p ≥ 1/2`. -/
theorem persistence_rates {h₀ C : ℝ} {A k m : ℕ}
    (hh : 0 < h₀) (hA : 1 ≤ A) (hC : 0 ≤ C) (hm : m ≤ k) :
    ∃ P₀ : ℕ, ∀ P, P₀ ≤ P → ∀ T : ℕ, (T : ℝ) ≤ C * (P + 1) →
      (⌈Real.logb 2 (catalogue h₀ A P)⌉₊ : ℝ) ≤ h₀ * P ∧
      2 ≤ radius (beta h₀ A) P ∧ 0 < intervalLength (beta h₀ A) P ∧
      beta h₀ A * P / 4 ≤ intervalLength (beta h₀ A) P ∧
      k.choose m * (T / intervalLength (beta h₀ A) P + 1) ≤ choiceMenu k m C (beta h₀ A) ∧
      ∀ p : ℝ, 1 / 2 ≤ p →
        selectionMass k m C (beta h₀ A) / 2 ≤
          p / (2 * (k.choose m * (T / intervalLength (beta h₀ A) P + 1) : ℕ)) ∧
        2 * (2 * T + 1 : ℕ) * (intervalLength (beta h₀ A) P : ℝ) *
            (k.choose m * (T / intervalLength (beta h₀ A) P + 1) : ℕ) /
          ((topSize (alpha h₀) P + 1) * p) ≤ (2 : ℝ) ^ (-alpha h₀ * P / 2) := by
  obtain ⟨P₁, hcat⟩ := catalogue_bits_small hh hA
  obtain ⟨P₂, hgrid⟩ := grid_rates (beta_pos hh hA) hC k m
  obtain ⟨P₃, hatom⟩ := conditional_atom_rate (C := C) (alpha_pos hh)
    (beta_pos hh hA).le (show 1 ≤ choiceMenu k m C (beta h₀ A) from choiceMenu_pos hm _ _)
  refine ⟨max P₁ (max P₂ P₃), ?_⟩
  intro P hP T hT
  have hP₁ := (le_max_left _ _).trans hP
  have hP₂ := (le_max_left P₂ P₃).trans ((le_max_right _ _).trans hP)
  have hP₃ := (le_max_right P₂ P₃).trans ((le_max_right _ _).trans hP)
  obtain ⟨hR, hell, hlen, hmenu⟩ := hgrid P hP₂ T hT
  refine ⟨hcat P hP₁, hR, hell, hlen, hmenu, ?_⟩
  intro p hp
  let L := k.choose m * (T / intervalLength (beta h₀ A) P + 1)
  let M := choiceMenu k m C (beta h₀ A)
  have hL : (0 : ℝ) < L := by
    exact_mod_cast Nat.mul_pos (Nat.choose_pos hm) (Nat.succ_pos _)
  have hM : (0 : ℝ) < M := by exact_mod_cast choiceMenu_pos hm C (beta h₀ A)
  have hLM : (L : ℝ) ≤ M := by exact_mod_cast hmenu
  have hpp : 0 < p := by linarith
  have hK : (0 : ℝ) < topSize (alpha h₀) P + 1 := by positivity
  constructor
  · change (1 / (2 * (M : ℝ))) / 2 ≤ p / (2 * (L : ℝ))
    calc
      _ = (1 / 2) / (2 * (M : ℝ)) := by ring
      _ ≤ p / (2 * (L : ℝ)) := div_le_div₀ hpp.le hp (by positivity) (by gcongr)
  · change 2 * (2 * T + 1 : ℕ) * (intervalLength (beta h₀ A) P : ℝ) * L /
        ((topSize (alpha h₀) P + 1) * p) ≤ _
    calc
      _ ≤ 2 * (2 * T + 1 : ℕ) * (intervalLength (beta h₀ A) P : ℝ) * M /
          ((topSize (alpha h₀) P + 1) * (1 / 2)) :=
        div_le_div₀ (by positivity) (by gcongr) (by positivity) (by gcongr)
      _ = 2 * (2 * T + 1 : ℕ) * (intervalLength (beta h₀ A) P : ℝ) /
          ((topSize (alpha h₀) P + 1) * (1 / (2 * (M : ℝ)))) := by field_simp
      _ ≤ _ := hatom P hP₃ T hT

/-- The length threshold is uniform over every positive matrix width. -/
theorem persistence_rates_all_widths {h₀ C : ℝ} {A k m : ℕ}
    (hh : 0 < h₀) (hA : 1 ≤ A) (hC : 0 ≤ C) (hm : m ≤ k) :
    ∃ d₀ : ℕ, ∀ d, d₀ ≤ d → ∀ b, 1 ≤ b → ∀ T : ℕ,
      (T : ℝ) ≤ C * ((d * d * b : ℕ) + 1) →
      (⌈Real.logb 2 (catalogue h₀ A (d * d * b))⌉₊ : ℝ) ≤ h₀ * (d * d * b : ℕ) ∧
      2 ≤ radius (beta h₀ A) (d * d * b) ∧
      0 < intervalLength (beta h₀ A) (d * d * b) ∧
      beta h₀ A * (d * d * b : ℕ) / 4 ≤ intervalLength (beta h₀ A) (d * d * b) ∧
      k.choose m * (T / intervalLength (beta h₀ A) (d * d * b) + 1) ≤
        choiceMenu k m C (beta h₀ A) ∧
      ∀ p : ℝ, 1 / 2 ≤ p →
        selectionMass k m C (beta h₀ A) / 2 ≤
          p / (2 * (k.choose m * (T / intervalLength (beta h₀ A) (d * d * b) + 1) : ℕ)) ∧
        2 * (2 * T + 1 : ℕ) * (intervalLength (beta h₀ A) (d * d * b) : ℝ) *
            (k.choose m * (T / intervalLength (beta h₀ A) (d * d * b) + 1) : ℕ) /
          ((topSize (alpha h₀) (d * d * b) + 1) * p) ≤
          (2 : ℝ) ^ (-alpha h₀ * (d * d * b : ℕ) / 2) := by
  obtain ⟨P₀, hh⟩ := persistence_rates hh hA hC hm
  exact AdaptiveTransfer.uniform_positive_width_threshold _ P₀ hh

noncomputable def futureCatalogue (h₀ : ℝ) (A P : ℕ) : ℕ :=
  (2 * radius (beta h₀ A) P + 1) * topSize (alpha h₀) P *
    (6 * A) ^ (radius (beta h₀ A) P + 1)

/-- The symmetric time-only catalogue has no larger menu than the
history-and-prefix catalogue already budgeted above. -/
theorem futureCatalogue_le (h₀ : ℝ) (A P : ℕ) :
    futureCatalogue h₀ A P ≤ catalogue h₀ A P := by
  unfold futureCatalogue catalogue
  gcongr
  nlinarith

theorem future_catalogue_bits_small {h₀ : ℝ} {A : ℕ} (hh : 0 < h₀) (hA : 1 ≤ A) :
    ∃ P₀ : ℕ, ∀ P, P₀ ≤ P → (⌈Real.logb 2 (futureCatalogue h₀ A P)⌉₊ : ℝ) ≤ h₀ * P := by
  obtain ⟨P₀, hcat⟩ := catalogue_bits_small hh hA
  refine ⟨P₀, fun P hP => le_trans ?_ (hcat P hP)⟩
  have hp : 0 < futureCatalogue h₀ A P := by
    unfold futureCatalogue
    have hk := topSize_pos (alpha h₀) P
    have ha : 0 < A := by omega
    positivity
  have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by exact_mod_cast hp) (show (futureCatalogue h₀ A P : ℝ) ≤ catalogue h₀ A P by
      exact_mod_cast futureCatalogue_le h₀ A P)
  exact_mod_cast Nat.ceil_mono hl

noncomputable def remoteRadius (α : ℝ) (A P : ℕ) : ℕ :=
  radius (α / (8 * Real.logb 2 (6 * A))) P

/-- The literal erased head window has `2H+1` possible cells. Its alphabet
factor consumes at most a quarter of the top-set exponent, apart from the
single fixed graph-degree factor. -/
theorem remote_mask_power_le {α : ℝ} {A : ℕ} (hα : 0 ≤ α) (hA : 1 ≤ A) (P : ℕ) :
    (A : ℝ) ^ (2 * remoteRadius α A P + 1) ≤ (6 * A) * (2 : ℝ) ^ (α * P / 4) := by
  have hl := log_degree_pos hA
  have hAp : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
  have hγ : 0 ≤ α / (8 * Real.logb 2 (6 * A)) := by positivity
  have hr := mul_le_mul_of_nonneg_right (radius_le_linear hγ P) hl.le
  have he : α / (8 * Real.logb 2 (6 * A)) * P * Real.logb 2 (6 * A) = α * P / 8 := by
    field_simp
  rw [he] at hr
  change (remoteRadius α A P : ℝ) * Real.logb 2 (6 * A) ≤ α * P / 8 at hr
  have hpow : (6 * (A : ℝ)) ^ (2 * remoteRadius α A P) ≤ (2 : ℝ) ^ (α * P / 4) := by
    apply (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) (by positivity)).mp
    rw [Real.logb_pow]
    push_cast
    nlinarith
  calc
    _ ≤ (6 * (A : ℝ)) ^ (2 * remoteRadius α A P + 1) := by gcongr; linarith
    _ = (6 * A) * (6 * (A : ℝ)) ^ (2 * remoteRadius α A P) := by rw [pow_succ]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)

/-- A literal head-window mask still has an exponential marginal atom
bound. Its fibre is the actual `(2T+1) A^(2H+1)` count, and the fixed
selection mass is `1/(2M)`. -/
theorem remote_mask_atom_rate {α C : ℝ} {A M : ℕ}
    (hα : 0 < α) (hA : 1 ≤ A) (hM : 1 ≤ M) :
    ∃ P₀ : ℕ, ∀ P, P₀ ≤ P → ∀ T : ℕ, (T : ℝ) ≤ C * (P + 1) →
      (2 * T + 1 : ℕ) * (A : ℝ) ^ (2 * remoteRadius α A P + 1) /
        ((topSize α P : ℝ) * (1 / (2 * (M : ℝ)))) ≤ (2 : ℝ) ^ (-α * P / 2) := by
  obtain ⟨P₀, hpoly⟩ := polynomial_rpow_small
    (show 1 ≤ 2 * M * (6 * A) by
      have hp : 0 < 2 * M * (6 * A) := by positivity
      omega)
    (show 1 ≤ atomPolynomialScale C 0 by unfold atomPolynomialScale; omega)
    (e := 1) (show 0 < α / 4 by positivity)
  refine ⟨P₀, ?_⟩
  intro P hP T hT
  have hMr : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hK : (0 : ℝ) < topSize α P := by exact_mod_cast topSize_pos α P
  have hhead : ((2 * M * (6 * A) * (2 * T + 1) : ℕ) : ℝ) ≤
      (2 : ℝ) ^ (α / 4 * P) := by
    apply le_trans _ (hpoly P hP)
    exact_mod_cast (show 2 * M * (6 * A) * (2 * T + 1) ≤
        2 * M * (6 * A) * (atomPolynomialScale C 0 * (P + 1)) ^ 1 by
      rw [pow_one]
      exact Nat.mul_le_mul_left _ (time_factor_polynomial hT))
  have hpow := remote_mask_power_le hα.le hA P
  have hnum : 2 * (M : ℝ) * (2 * T + 1 : ℕ) * (A : ℝ) ^ (2 * remoteRadius α A P + 1) ≤
      (2 : ℝ) ^ (α / 2 * P) := by
    calc
      _ ≤ 2 * (M : ℝ) * (2 * T + 1 : ℕ) * ((6 * A) * (2 : ℝ) ^ (α * P / 4)) := by gcongr
      _ = ((2 * M * (6 * A) * (2 * T + 1) : ℕ) : ℝ) * (2 : ℝ) ^ (α * P / 4) := by
        push_cast
        ring
      _ ≤ (2 : ℝ) ^ (α / 4 * P) * (2 : ℝ) ^ (α * P / 4) := by gcongr
      _ = (2 : ℝ) ^ (α / 2 * P) := by rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; congr 1; ring
  calc
    _ = (2 * (M : ℝ) * (2 * T + 1 : ℕ) * (A : ℝ) ^ (2 * remoteRadius α A P + 1)) /
        topSize α P := by field_simp
    _ ≤ (2 : ℝ) ^ (α / 2 * P) / (2 : ℝ) ^ (α * P) :=
      div_le_div₀ (by positivity) hnum (by positivity) (topSize_lower α P)
    _ = (2 : ℝ) ^ (-α * P / 2) := by
      rw [← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring

/-- The remote-mask estimate also has one threshold for all positive
matrix widths; the fixed constants are independent of the width. -/
theorem remote_mask_atom_rate_all_widths {α C : ℝ} {A M : ℕ}
    (hα : 0 < α) (hA : 1 ≤ A) (hM : 1 ≤ M) :
    ∃ d₀ : ℕ, ∀ d, d₀ ≤ d → ∀ b, 1 ≤ b → ∀ T : ℕ,
      (T : ℝ) ≤ C * ((d * d * b : ℕ) + 1) →
      (2 * T + 1 : ℕ) * (A : ℝ) ^ (2 * remoteRadius α A (d * d * b) + 1) /
        ((topSize α (d * d * b) : ℝ) * (1 / (2 * (M : ℝ)))) ≤
        (2 : ℝ) ^ (-α * (d * d * b : ℕ) / 2) := by
  obtain ⟨P₀, hh⟩ := remote_mask_atom_rate (C := C) hα hA hM
  exact AdaptiveTransfer.uniform_positive_width_threshold _ P₀ hh

end AdaptiveTransfer.PersistenceRates
