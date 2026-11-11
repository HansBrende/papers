import AdaptiveTransfer.NativeInputCutEndpoint
import AdaptiveTransfer.GeometryMenuRates
import AdaptiveTransfer.MetadataRates

/-! Simultaneous source-input expansion on actual adaptive native runs.
The exact finite cut menu is subexponential at a small fixed density. The
threshold is uniform in every positive transposition block width. -/

namespace AdaptiveTransfer
open Transpose Finset
open scoped BigOperators

theorem globalCutMenu_pos (k β P T r : ℕ) : 0 < globalCutMenu k β P T r := by
  have h₁ : 0 < (T + 1).choose 1 := Nat.choose_pos (by omega)
  have h₂ : 0 < (T + 2).choose 2 := Nat.choose_pos (by omega)
  have h₃ : 0 < (P + 2).choose 2 := Nat.choose_pos (by omega)
  have hs : 0 < globalGeometryMenuSize k P T 0 * 2 ^ (β * 0) := by
    simp only [globalGeometryMenuSize, zero_add, add_zero, Nat.choose_zero_right,
      pow_zero, mul_one, mul_zero, one_pow]
    positivity
  exact hs.trans_le (single_le_sum (f := fun s => globalGeometryMenuSize k P T s * 2 ^ (β * s))
    (fun _ _ => Nat.zero_le _)
    (mem_range.mpr (by omega : 0 < min r T + 1)))

theorem globalCutMenu_mono_width {k P T r β β' : ℕ} (hβ : β ≤ β') :
    globalCutMenu k β P T r ≤ globalCutMenu k β' P T r := by
  apply sum_le_sum
  intro s _hs
  apply Nat.mul_le_mul_left
  exact Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right s hβ)

/-- The quantitative simultaneous cut tail. The only graph premises are
inside the literal bad-input event already checked by the finite theorem. -/
theorem native_input_cut_tail (k β K : ℕ) (hK : 1 ≤ K) {α : ℝ} (hα : 0 < α) :
    ∃ lam : ℝ, 0 < lam ∧ ∃ P₀ : ℕ, ∀ (P T q a : ℕ) (M : TM) (π : Equiv.Perm (Fin P)),
      P₀ ≤ P → T ≤ K * (P + 1) → M.k = k → q + k * a + 2 ≤ β →
      M.q + 1 ≤ 2 ^ q → M.g + 1 ≤ 2 ^ a →
      ((nativeBadInputCuts M P T π (α * P) ⌊lam * P⌋₊).card : ℝ) <
        (2 : ℝ) ^ ((1 - α / 3) * P) := by
  obtain ⟨lam, hlam, P₁, hmenu⟩ := geometry_cut_menus_logb_small k β 0 K hK
    (show 0 < α / 2 by positivity)
  refine ⟨lam, hlam, max P₁ 1, ?_⟩
  intro P T q a M π hP hT hk hβ hq ha
  have hP₁ : P₁ ≤ P := (le_max_left _ _).trans hP
  have hPpos : 0 < P := (le_max_right _ _).trans hP
  have hPr : (0 : ℝ) < P := by exact_mod_cast hPpos
  let r := ⌊lam * (P : ℝ)⌋₊
  have hr : (r : ℝ) ≤ lam * P := Nat.floor_le (by positivity)
  have hcost := (hmenu P T r hP₁ hT hr).1
  have hfinite := native_bad_input_cut_bound M P T r q a π (α * P) hq ha
  change ((nativeBadInputCuts M P T π (α * P) r).card : ℝ) ≤
    (2 : ℝ) ^ ((P : ℝ) - α * P) * (globalCutMenu M.k (q + M.k * a + 2) P T r : ℕ) at hfinite
  rw [hk] at hfinite
  have hwide : (globalCutMenu k (q + k * a + 2) P T r : ℝ) ≤
      (globalCutMenu k β P T r : ℝ) := by exact_mod_cast globalCutMenu_mono_width hβ
  have hmpos : (0 : ℝ) < (globalCutMenu k β P T r : ℕ) := by
    exact_mod_cast globalCutMenu_pos k β P T r
  have hm : (globalCutMenu k β P T r : ℝ) ≤ (2 : ℝ) ^ ((α / 2) * P) := by
    rw [← Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num) hmpos]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hcost
  have hbound := hfinite.trans (mul_le_mul_of_nonneg_left (hwide.trans hm) (by positivity))
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)] at hbound
  apply hbound.trans_lt
  apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
  nlinarith

/-- One threshold works for every b≥1. This endpoint even permits an
arbitrary fixed permutation at each length and any resource-bounded table. -/
theorem native_input_cut_tail_all_width (k β : ℕ) {c α : ℝ} (hc : 0 ≤ c) (hα : 0 < α) :
    ∃ lam : ℝ, 0 < lam ∧ ∃ d₀ : ℕ, ∀ (d b q a : ℕ) (M : TM)
      (π : Equiv.Perm (Fin (d * d * b))),
      d₀ ≤ d → 1 ≤ b → M.k = k → q + k * a + 2 ≤ β →
      M.q + 1 ≤ 2 ^ q → M.g + 1 ≤ 2 ^ a →
      ((nativeBadInputCuts M (d * d * b) (returnTime (d * d * b) c) π
        (α * (d * d * b : ℕ)) ⌊lam * (d * d * b : ℕ)⌋₊).card : ℝ) <
        (2 : ℝ) ^ ((1 - α / 3) * (d * d * b : ℕ)) := by
  obtain ⟨lam, hlam, P₀, htail⟩ := native_input_cut_tail k β (max 1 ⌈c⌉₊) (le_max_left _ _) hα
  refine ⟨lam, hlam, P₀ + 1, ?_⟩
  intro d b q a M π hd hb hk hβ hq ha
  have hlength : P₀ ≤ d * d * b := by nlinarith
  have htime : returnTime (d * d * b) c ≤ max 1 ⌈c⌉₊ * (d * d * b + 1) :=
    (returnTime_le_integer_linear hc).trans
      (Nat.mul_le_mul_right _ (le_max_right _ _))
  exact htail (d * d * b) _ q a M π hlength htime hk hβ hq ha

end AdaptiveTransfer
