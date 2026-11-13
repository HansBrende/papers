import BoundedArityDecoders.ExtensionAperiodicSix
import BoundedArityDecoders.ExtensionFieldTransfer
import ClassUniformMemo.Fields

/-!
# Formal Proofs for Extension Result 2 (`Problem 9.1(b)` in Characteristic `∉ {2, 3}`)

Complete kernel-verified proofs of:
* `extension_Theorem2_Preliminaries : Extension_Theorem2_PreliminariesSpec`
* `aperiodicSix_shift_inf_finrank_le_14`
* `aperiodicSix_finrank_le_25`
* `aperiodicSix_maxDim_eq_25`
* `extension_Theorem2_AperiodicSixExact : Extension_Theorem2_AperiodicSixExactSpec`
-/

namespace BoundedArityDecoders

open Module
open scoped BigOperators

/-! ### Section 1: Characteristic & Primitive Sixth Root Preliminaries -/

private theorem ringChar_ne_two_three_iff_ne_zero (F : Type*) [Field F] :
    (ringChar F ≠ 2 ∧ ringChar F ≠ 3) ↔ ((2 : F) ≠ 0 ∧ (3 : F) ≠ 0) := by
  have h2_zero : ((2 : F) = 0) ↔ ringChar F = 2 := by
    have hcast : (((2 : ℕ) : F) = 0) ↔ ringChar F ∣ 2 :=
      CharP.cast_eq_zero_iff F (ringChar F) 2
    rcases eq_or_ne (ringChar F) 0 with h0 | hpos
    · constructor
      · intro h
        have hdvd : (0 : ℕ) ∣ 2 := h0 ▸ hcast.mp (by exact_mod_cast h)
        omega
      · intro h; omega
    · have hp : Nat.Prime (ringChar F) :=
        (CharP.char_is_prime_or_zero F (ringChar F)).resolve_right hpos
      calc ((2 : F) = 0) ↔ (((2 : ℕ) : F) = 0) := by norm_num
        _ ↔ ringChar F ∣ 2 := hcast
        _ ↔ ringChar F = 2 := Nat.prime_dvd_prime_iff_eq hp Nat.prime_two
  have h3_zero : ((3 : F) = 0) ↔ ringChar F = 3 := by
    have hcast : (((3 : ℕ) : F) = 0) ↔ ringChar F ∣ 3 :=
      CharP.cast_eq_zero_iff F (ringChar F) 3
    rcases eq_or_ne (ringChar F) 0 with h0 | hpos
    · constructor
      · intro h
        have hdvd : (0 : ℕ) ∣ 3 := h0 ▸ hcast.mp (by exact_mod_cast h)
        omega
      · intro h; omega
    · have hp : Nat.Prime (ringChar F) :=
        (CharP.char_is_prime_or_zero F (ringChar F)).resolve_right hpos
      calc ((3 : F) = 0) ↔ (((3 : ℕ) : F) = 0) := by norm_num
        _ ↔ ringChar F ∣ 3 := hcast
        _ ↔ ringChar F = 3 := Nat.prime_dvd_prime_iff_eq hp Nat.prime_three
  exact and_congr h2_zero.not.symm h3_zero.not.symm

private theorem ringChar_ne_two_three_iff_coprimeSix (F : Type*) [Field F] :
    (ringChar F ≠ 2 ∧ ringChar F ≠ 3) ↔ CoprimeToChar F 6 := by
  rw [ringChar_ne_two_three_iff_ne_zero, coprimeToChar_iff_natCast_ne_zero F 6]
  have h6 : ((6 : ℕ) : F) = (2 : F) * (3 : F) := by norm_num
  rw [h6, mul_ne_zero_iff]

/-- **Result 2 Preliminaries**: fiber characterization of `SwapRigidity.aperiodicCls` and
equivalence of `ringChar F ≠ 2 ∧ ringChar F ≠ 3`, `(2 : F) ≠ 0 ∧ (3 : F) ≠ 0`, and
`CoprimeToChar F 6`. -/
theorem extension_Theorem2_Preliminaries : Extension_Theorem2_PreliminariesSpec := by
  refine ⟨⟨SwapRigidity.aperiodicCls_eq_true_iff, SwapRigidity.aperiodicCls_eq_false_iff,
    fun _ _ => Iff.rfl⟩, ?_⟩
  intro F _
  exact ⟨ringChar_ne_two_three_iff_ne_zero F, ringChar_ne_two_three_iff_coprimeSix F⟩

private theorem isPrimitiveRoot_six_rel {K : Type*} [Field K] {ζ : K}
    (hprim : IsPrimitiveRoot ζ 6) : ζ ^ 2 = ζ - 1 := by
  have h6 : ζ ^ 6 = 1 := hprim.pow_eq_one
  have h3_ne : ζ ^ 3 ≠ 1 := hprim.pow_ne_one_of_pos_of_lt (by decide) (by decide)
  have h2_ne : ζ ^ 2 ≠ 1 := hprim.pow_ne_one_of_pos_of_lt (by decide) (by decide)
  have hfac6 : (ζ ^ 3 - 1) * (ζ ^ 3 + 1) = 0 := by
    calc (ζ ^ 3 - 1) * (ζ ^ 3 + 1) = ζ ^ 6 - 1 := by ring
      _ = 0 := sub_eq_zero.mpr h6
  have h3_eq : ζ ^ 3 + 1 = 0 :=
    (mul_eq_zero.mp hfac6).resolve_left (sub_ne_zero.mpr h3_ne)
  have hadd1_ne : ζ + 1 ≠ 0 := by
    intro h0
    have hneg : ζ = -1 := eq_neg_of_add_eq_zero_left h0
    apply h2_ne
    rw [hneg]
    ring
  have hfac3 : (ζ + 1) * (ζ ^ 2 - ζ + 1) = 0 := by
    calc (ζ + 1) * (ζ ^ 2 - ζ + 1) = ζ ^ 3 + 1 := by ring
      _ = 0 := h3_eq
  have hquad : ζ ^ 2 - ζ + 1 = 0 :=
    (mul_eq_zero.mp hfac3).resolve_left hadd1_ne
  linear_combination hquad

/-! ### Section 2: `ZMod 6` Powers of `ζ` and Abstract Fourier Code System -/

section FourierSystem

variable {K : Type*} [Field K]

private lemma zmod6_cases (a : ZMod 6) :
    a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 := by
  revert a; decide

private lemma sum_zmod6 {M : Type*} [AddCommMonoid M] (f : ZMod 6 → M) :
    ∑ c : ZMod 6, f c = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
  have huniv : (Finset.univ : Finset (ZMod 6)) = {0, 1, 2, 3, 4, 5} := by decide
  rw [huniv]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  abel

private def zpow (ζ : K) (a : ZMod 6) : K := ζ ^ a.val

private lemma zeta_pow_three {ζ : K} (hζ : ζ ^ 2 = ζ - 1) : ζ ^ 3 = -1 := by
  linear_combination (ζ + 1) * hζ

private lemma zeta_pow_four {ζ : K} (hζ : ζ ^ 2 = ζ - 1) : ζ ^ 4 = -ζ := by
  linear_combination (ζ ^ 2 + ζ) * hζ

private lemma zeta_pow_five {ζ : K} (hζ : ζ ^ 2 = ζ - 1) : ζ ^ 5 = 1 - ζ := by
  linear_combination (ζ ^ 3 + ζ ^ 2 - 1) * hζ

private lemma zeta_pow_six {ζ : K} (hζ : ζ ^ 2 = ζ - 1) : ζ ^ 6 = 1 := by
  linear_combination (ζ ^ 4 + ζ ^ 3 - ζ - 1) * hζ

private lemma zpow_zero (ζ : K) : zpow ζ 0 = 1 := by
  change ζ ^ 0 = 1
  exact pow_zero ζ

private lemma zpow_eval {ζ : K} (hζ : ζ ^ 2 = ζ - 1) (a : ZMod 6) :
    zpow ζ a =
      if a = 0 then 1
      else if a = 1 then ζ
      else if a = 2 then ζ - 1
      else if a = 3 then -1
      else if a = 4 then -ζ
      else 1 - ζ := by
  have h2 := hζ
  have h3 := zeta_pow_three hζ
  have h4 := zeta_pow_four hζ
  have h5 := zeta_pow_five hζ
  rcases zmod6_cases a with rfl | rfl | rfl | rfl | rfl | rfl
  · simp (config := { decide := true }) only [↓reduceIte]; exact zpow_zero ζ
  · simp (config := { decide := true }) only [↓reduceIte]; change ζ ^ 1 = ζ; exact pow_one ζ
  · simp (config := { decide := true }) only [↓reduceIte]; exact h2
  · simp (config := { decide := true }) only [↓reduceIte]; exact h3
  · simp (config := { decide := true }) only [↓reduceIte]; exact h4
  · simp (config := { decide := true }) only [↓reduceIte]; exact h5

private lemma zpow_add {ζ : K} (hζ : ζ ^ 2 = ζ - 1) (a b : ZMod 6) :
    zpow ζ (a + b) = zpow ζ a * zpow ζ b := by
  dsimp [zpow]
  have hval : (a + b).val = (a.val + b.val) % 6 := ZMod.val_add a b
  have hdiv : 6 * ((a.val + b.val) / 6) + (a.val + b.val) % 6 = a.val + b.val :=
    Nat.div_add_mod _ 6
  calc ζ ^ (a + b).val
      = (ζ ^ 6) ^ ((a.val + b.val) / 6) * ζ ^ ((a.val + b.val) % 6) := by
          rw [zeta_pow_six hζ, one_pow, one_mul, hval]
    _ = ζ ^ (a.val + b.val) := by rw [← pow_mul, ← pow_add, hdiv]
    _ = ζ ^ a.val * ζ ^ b.val := pow_add _ _ _

private lemma zpow_three {ζ : K} (hζ : ζ ^ 2 = ζ - 1) : zpow ζ 3 = -1 :=
  zeta_pow_three hζ

private lemma zpow_add_three {ζ : K} (hζ : ζ ^ 2 = ζ - 1) (a : ZMod 6) :
    zpow ζ (a + 3) = - zpow ζ a := by
  rw [zpow_add hζ, zpow_three hζ, mul_neg_one]

private lemma zpow_sub_three {ζ : K} (hζ : ζ ^ 2 = ζ - 1) (a : ZMod 6) :
    zpow ζ (a - 3) = - zpow ζ a := by
  have h3 : (a - 3 : ZMod 6) = a + 3 := by
    rcases zmod6_cases a with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  rw [h3, zpow_add_three hζ]

private lemma zpow_neg_mul_self {ζ : K} (hζ : ζ ^ 2 = ζ - 1) (a : ZMod 6) :
    zpow ζ (-a) * zpow ζ a = 1 := by
  rw [← zpow_add hζ, neg_add_cancel, zpow_zero]

private lemma zpow_ne_zero {ζ : K} (hζ : ζ ^ 2 = ζ - 1) (a : ZMod 6) :
    zpow ζ a ≠ 0 :=
  right_ne_zero_of_mul_eq_one (zpow_neg_mul_self hζ a)

private lemma sum_zpow {ζ : K} (hζ : ζ ^ 2 = ζ - 1) (a : ZMod 6) :
    ∑ c : ZMod 6, zpow ζ (c * a) = if a = 0 then 6 else 0 := by
  rw [sum_zmod6]
  rcases zmod6_cases a with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (config := { decide := true }) only [zpow_eval hζ, ↓reduceIte] <;>
    ring

/-- Discrepancy coordinate `d₀_ξ(u) = u 2 - ζ^(3ξ) u 0` on `Fin 4 → K`. -/
private def d0Form (ζ : K) (ξ : ZMod 6) : (Fin 4 → K) →ₗ[K] K where
  toFun u := u 2 - zpow ζ (3 * ξ) * u 0
  map_add' u v := by simp; ring
  map_smul' c u := by simp; ring

/-- Discrepancy coordinate `d₁_ξ(u) = u 3 - ζ^(2ξ) u 1` on `Fin 4 → K`. -/
private def d1Form (ζ : K) (ξ : ZMod 6) : (Fin 4 → K) →ₗ[K] K where
  toFun u := u 3 - zpow ζ (2 * ξ) * u 1
  map_add' u v := by simp; ring
  map_smul' c u := by simp; ring

/-- Single-mode subspace `L_η = ker (d₀_η, d₁_η)` of dimension `2` inside `Fin 4 → K`. -/
private def LSub (ζ : K) (η : ZMod 6) : Submodule K (Fin 4 → K) :=
  LinearMap.ker ((d0Form ζ η).prod (d1Form ζ η))

private lemma finrank_fin4 (K : Type*) [Field K] : finrank K (Fin 4 → K) = 4 := by
  simp

private lemma finrank_LSub (ζ : K) (η : ZMod 6) : finrank K (LSub ζ η) = 2 := by
  let f := (d0Form ζ η).prod (d1Form ζ η)
  have hsurj : Function.Surjective f := by
    rintro ⟨x, y⟩
    refine ⟨![0, 0, x, y], ?_⟩
    simp [f, d0Form, d1Form]
  have hrk := LinearMap.finrank_range_add_finrank_ker f
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_prod, finrank_self,
    finrank_fin4] at hrk
  change finrank K (LinearMap.ker f) = 2
  omega

/-- Abstract Fourier-mode code space cut out by the `10` run equations per output mode `ξ`. -/
private def FourierCodeSpace (ζ : K)
    (L0 L1 : ZMod 6 → ZMod 6 → ((Fin 4 → K) →ₗ[K] K)) :
    Submodule K (ZMod 6 → Fin 4 → K) where
  carrier := {v | ∀ ξ : ZMod 6,
    (∑ μ : ZMod 6, zpow ζ (0 * μ) * L0 ξ μ (v μ) = 0) ∧
    (∑ μ : ZMod 6, zpow ζ (1 * μ) * L0 ξ μ (v μ) = 0) ∧
    (∑ μ : ZMod 6, zpow ζ (2 * μ) * L0 ξ μ (v μ) = 0) ∧
    (∑ μ : ZMod 6, zpow ζ (3 * μ) * L0 ξ μ (v μ) = d0Form ζ ξ (v ξ)) ∧
    (∑ μ : ZMod 6, zpow ζ (4 * μ) * L0 ξ μ (v μ) = zpow ζ ξ * d0Form ζ ξ (v ξ)) ∧
    (∑ μ : ZMod 6, zpow ζ (2 * μ) * L1 ξ μ (v μ) = 0) ∧
    (∑ μ : ZMod 6, zpow ζ (3 * μ) * L1 ξ μ (v μ) = 0) ∧
    (∑ μ : ZMod 6, zpow ζ (4 * μ) * L1 ξ μ (v μ) = d1Form ζ ξ (v ξ)) ∧
    (∑ μ : ZMod 6, zpow ζ (5 * μ) * L1 ξ μ (v μ) = zpow ζ ξ * d1Form ζ ξ (v ξ)) ∧
    (∑ μ : ZMod 6, zpow ζ (0 * μ) * L1 ξ μ (v μ) = zpow ζ (2 * ξ) * d1Form ζ ξ (v ξ))}
  zero_mem' ξ := by simp
  add_mem' {v₁ v₂} hv₁ hv₂ ξ := by
    obtain ⟨h0₁, h1₁, h2₁, h3₁, h4₁, g2₁, g3₁, g4₁, g5₁, g0₁⟩ := hv₁ ξ
    obtain ⟨h0₂, h1₂, h2₂, h3₂, h4₂, g2₂, g3₂, g4₂, g5₂, g0₂⟩ := hv₂ ξ
    simp only [Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]
    refine ⟨by rw [h0₁, h0₂, add_zero], by rw [h1₁, h1₂, add_zero],
      by rw [h2₁, h2₂, add_zero], by rw [h3₁, h3₂],
      by rw [h4₁, h4₂], by rw [g2₁, g2₂, add_zero],
      by rw [g3₁, g3₂, add_zero], by rw [g4₁, g4₂],
      by rw [g5₁, g5₂], by rw [g0₁, g0₂]⟩
  smul_mem' c {v} hv ξ := by
    obtain ⟨h0, h1, h2, h3, h4, g2, g3, g4, g5, g0⟩ := hv ξ
    have hfactor : ∀ (f : ZMod 6 → K) (g : ZMod 6 → K),
        (∑ μ : ZMod 6, f μ * (c * g μ)) = c * ∑ μ : ZMod 6, f μ * g μ := by
      intro f g
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun μ _ => by ring
    simp only [Pi.smul_apply, map_smul, smul_eq_mul, hfactor]
    refine ⟨by rw [h0, mul_zero], by rw [h1, mul_zero], by rw [h2, mul_zero],
      by rw [h3], by rw [h4]; ring, by rw [g2, mul_zero], by rw [g3, mul_zero],
      by rw [g4], by rw [g5]; ring, by rw [g0]; ring⟩

private abbrev singleMode (K : Type*) [Field K] (η : ZMod 6) :
    (Fin 4 → K) →ₗ[K] (ZMod 6 → Fin 4 → K) :=
  LinearMap.single K (fun _ : ZMod 6 => Fin 4 → K) η

/-- Single-mode intersection `K_η = {u | singleMode η u ∈ W}`. -/
private def KSub (ζ : K) (L0 L1 : ZMod 6 → ZMod 6 → ((Fin 4 → K) →ₗ[K] K)) (η : ZMod 6) :
    Submodule K (Fin 4 → K) :=
  (FourierCodeSpace ζ L0 L1).comap (singleMode K η)

private lemma mem_KSub_iff {ζ : K} (hζ : ζ ^ 2 = ζ - 1)
    {L0 L1 : ZMod 6 → ZMod 6 → ((Fin 4 → K) →ₗ[K] K)} {η : ZMod 6} {u : Fin 4 → K} :
    u ∈ KSub ζ L0 L1 η ↔
      d0Form ζ η u = 0 ∧ d1Form ζ η u = 0 ∧ ∀ ξ : ZMod 6, L0 ξ η u = 0 ∧ L1 ξ η u = 0 := by
  have hsum0 : ∀ (ξ c : ZMod 6),
      ∑ μ : ZMod 6, zpow ζ (c * μ) * L0 ξ μ (singleMode K η u μ) =
        zpow ζ (c * η) * L0 ξ η u := by
    intro ξ c
    rw [Fintype.sum_eq_single η]
    · simp [singleMode]
    · intro μ hμ
      simp [singleMode, Pi.single_eq_of_ne hμ]
  have hsum1 : ∀ (ξ c : ZMod 6),
      ∑ μ : ZMod 6, zpow ζ (c * μ) * L1 ξ μ (singleMode K η u μ) =
        zpow ζ (c * η) * L1 ξ η u := by
    intro ξ c
    rw [Fintype.sum_eq_single η]
    · simp [singleMode]
    · intro μ hμ
      simp [singleMode, Pi.single_eq_of_ne hμ]
  constructor
  · intro hu
    have hL0 : ∀ ξ, L0 ξ η u = 0 := by
      intro ξ
      have h0 := (hu ξ).1
      rw [hsum0, zero_mul, zpow_zero, one_mul] at h0
      exact h0
    have hL1 : ∀ ξ, L1 ξ η u = 0 := by
      intro ξ
      have g2 := (hu ξ).2.2.2.2.2.1
      rw [hsum1] at g2
      exact (mul_eq_zero.mp g2).resolve_left (zpow_ne_zero hζ _)
    have hd0 : d0Form ζ η u = 0 := by
      have h3 := (hu η).2.2.2.1
      rw [hsum0, hL0 η, mul_zero] at h3
      simpa [singleMode] using h3.symm
    have hd1 : d1Form ζ η u = 0 := by
      have g4 := (hu η).2.2.2.2.2.2.2.1
      rw [hsum1, hL1 η, mul_zero] at g4
      simpa [singleMode] using g4.symm
    exact ⟨hd0, hd1, fun ξ => ⟨hL0 ξ, hL1 ξ⟩⟩
  · rintro ⟨hd0, hd1, hL⟩ ξ
    have hd0_ξ : d0Form ζ ξ (singleMode K η u ξ) = 0 := by
      by_cases h : ξ = η
      · subst h; simpa [singleMode] using hd0
      · simp [singleMode, Pi.single_eq_of_ne h]
    have hd1_ξ : d1Form ζ ξ (singleMode K η u ξ) = 0 := by
      by_cases h : ξ = η
      · subst h; simpa [singleMode] using hd1
      · simp [singleMode, Pi.single_eq_of_ne h]
    simp only [hsum0, hsum1, (hL ξ).1, (hL ξ).2, hd0_ξ, hd1_ξ, mul_zero]
    exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

private lemma KSub_le_LSub {ζ : K} (hζ : ζ ^ 2 = ζ - 1)
    (L0 L1 : ZMod 6 → ZMod 6 → ((Fin 4 → K) →ₗ[K] K)) (η : ZMod 6) :
    KSub ζ L0 L1 η ≤ LSub ζ η := by
  intro u hu
  rw [mem_KSub_iff hζ] at hu
  simp [LSub, hu.1, hu.2.1]

private lemma finrank_KSub_le_two {ζ : K} (hζ : ζ ^ 2 = ζ - 1)
    (L0 L1 : ZMod 6 → ZMod 6 → ((Fin 4 → K) →ₗ[K] K)) (η : ZMod 6) :
    finrank K (KSub ζ L0 L1 η) ≤ 2 := by
  calc finrank K (KSub ζ L0 L1 η) ≤ finrank K (LSub ζ η) :=
        Submodule.finrank_mono (KSub_le_LSub hζ L0 L1 η)
    _ = 2 := finrank_LSub ζ η

private lemma KSub_eq_LSub_of_finrank_eq_two {ζ : K} (hζ : ζ ^ 2 = ζ - 1)
    {L0 L1 : ZMod 6 → ZMod 6 → ((Fin 4 → K) →ₗ[K] K)} {η : ZMod 6}
    (hdim : finrank K (KSub ζ L0 L1 η) = 2) :
    KSub ζ L0 L1 η = LSub ζ η :=
  Submodule.eq_of_le_of_finrank_eq (KSub_le_LSub hζ L0 L1 η)
    (hdim.trans (finrank_LSub ζ η).symm)

/-! ### Eliminating Missing Shift Points `c = 5` (Color 0) and `c = 1` (Color 1) -/

private def w0 (ζ : K) (ξ η c : ZMod 6) : K :=
  zpow ζ (- (c * η)) + zpow ζ (η - ξ) * zpow ζ (- (c * (ξ + 3)))

private def w1 (ζ : K) (ξ η c : ZMod 6) : K :=
  zpow ζ (- (c * η)) + zpow ζ (ξ - η) * zpow ζ (- (c * (ξ + 3)))

private def rho0_6 (ζ : K) (ξ η : ZMod 6) : K :=
  w0 ζ ξ η 3 + w0 ζ ξ η 4 * zpow ζ ξ

private def rho1_6 (ζ : K) (ξ η : ZMod 6) : K :=
  w1 ζ ξ η 4 + w1 ζ ξ η 5 * zpow ζ ξ + w1 ζ ξ η 0 * zpow ζ (2 * ξ)

private lemma w0_five {ζ : K} (hζ : ζ ^ 2 = ζ - 1) (ξ η : ZMod 6) :
    w0 ζ ξ η 5 = 0 := by
  dsimp [w0]
  have h1 : (- ((5 : ZMod 6) * η)) = η := by
    rcases zmod6_cases η with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have h2 : (η - ξ) + (- ((5 : ZMod 6) * (ξ + 3))) = η + 3 := by
    rcases zmod6_cases ξ with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases zmod6_cases η with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  rw [← zpow_add hζ, h1, h2, zpow_add_three hζ]
  ring

private lemma w1_one {ζ : K} (hζ : ζ ^ 2 = ζ - 1) (ξ η : ZMod 6) :
    w1 ζ ξ η 1 = 0 := by
  dsimp [w1]
  have h1 : (- ((1 : ZMod 6) * η)) = -η := by ring
  have h2 : (ξ - η) + (- ((1 : ZMod 6) * (ξ + 3))) = (-η) + 3 := by
    rcases zmod6_cases ξ with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases zmod6_cases η with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  rw [← zpow_add hζ, h1, h2, zpow_add_three hζ]
  ring

private lemma sum_w0_zpow {ζ : K} (hζ : ζ ^ 2 = ζ - 1) (ξ η μ : ZMod 6) :
    ∑ c : ZMod 6, w0 ζ ξ η c * zpow ζ (c * μ) =
      (if μ = η then 6 else 0) + zpow ζ (η - ξ) * (if μ = ξ + 3 then 6 else 0) := by
  have hterm : ∀ c : ZMod 6,
      w0 ζ ξ η c * zpow ζ (c * μ) =
        zpow ζ (c * (μ - η)) + zpow ζ (η - ξ) * zpow ζ (c * (μ - (ξ + 3))) := by
    intro c
    dsimp [w0]
    rw [add_mul, mul_assoc, ← zpow_add hζ, ← zpow_add hζ]
    have e1 : - (c * η) + c * μ = c * (μ - η) := by ring
    have e2 : - (c * (ξ + 3)) + c * μ = c * (μ - (ξ + 3)) := by ring
    rw [e1, e2]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_zpow hζ, sum_zpow hζ]
  simp only [sub_eq_zero]

private lemma sum_w1_zpow {ζ : K} (hζ : ζ ^ 2 = ζ - 1) (ξ η μ : ZMod 6) :
    ∑ c : ZMod 6, w1 ζ ξ η c * zpow ζ (c * μ) =
      (if μ = η then 6 else 0) + zpow ζ (ξ - η) * (if μ = ξ + 3 then 6 else 0) := by
  have hterm : ∀ c : ZMod 6,
      w1 ζ ξ η c * zpow ζ (c * μ) =
        zpow ζ (c * (μ - η)) + zpow ζ (ξ - η) * zpow ζ (c * (μ - (ξ + 3))) := by
    intro c
    dsimp [w1]
    rw [add_mul, mul_assoc, ← zpow_add hζ, ← zpow_add hζ]
    have e1 : - (c * η) + c * μ = c * (μ - η) := by ring
    have e2 : - (c * (ξ + 3)) + c * μ = c * (μ - (ξ + 3)) := by ring
    rw [e1, e2]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_zpow hζ, sum_zpow hζ]
  simp only [sub_eq_zero]

private theorem elim_color0 {ζ : K} (hζ : ζ ^ 2 = ζ - 1)
    {L0 L1 : ZMod 6 → ZMod 6 → ((Fin 4 → K) →ₗ[K] K)}
    {v : ZMod 6 → Fin 4 → K} (hv : v ∈ FourierCodeSpace ζ L0 L1) (ξ η : ZMod 6) :
    6 * L0 ξ η (v η) + 6 * zpow ζ (η - ξ) * L0 ξ (ξ + 3) (v (ξ + 3)) =
      rho0_6 ζ ξ η * d0Form ζ ξ (v ξ) := by
  obtain ⟨h0, h1, h2, h3, h4, -⟩ := hv ξ
  let S : ZMod 6 → K := fun c => ∑ μ : ZMod 6, zpow ζ (c * μ) * L0 ξ μ (v μ)
  have hrhs : ∑ c : ZMod 6, w0 ζ ξ η c * S c = rho0_6 ζ ξ η * d0Form ζ ξ (v ξ) := by
    rw [sum_zmod6]
    dsimp only [S]
    rw [h0, h1, h2, h3, h4, w0_five hζ]
    dsimp [rho0_6]
    ring
  have hlhs : ∑ c : ZMod 6, w0 ζ ξ η c * S c =
      6 * L0 ξ η (v η) + 6 * zpow ζ (η - ξ) * L0 ξ (ξ + 3) (v (ξ + 3)) := by
    dsimp [S]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    have hinner : ∀ μ : ZMod 6,
        (∑ c : ZMod 6, w0 ζ ξ η c * (zpow ζ (c * μ) * L0 ξ μ (v μ))) =
          ((if μ = η then (6 : K) else 0) +
            zpow ζ (η - ξ) * (if μ = ξ + 3 then (6 : K) else 0)) * L0 ξ μ (v μ) := by
      intro μ
      rw [← sum_w0_zpow hζ ξ η μ, Finset.sum_mul]
      refine Finset.sum_congr rfl fun c _ => by ring
    simp_rw [hinner, add_mul]
    rw [Finset.sum_add_distrib]
    simp only [ite_mul, zero_mul, mul_assoc, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    ring
  exact hlhs.symm.trans hrhs

private theorem elim_color1 {ζ : K} (hζ : ζ ^ 2 = ζ - 1)
    {L0 L1 : ZMod 6 → ZMod 6 → ((Fin 4 → K) →ₗ[K] K)}
    {v : ZMod 6 → Fin 4 → K} (hv : v ∈ FourierCodeSpace ζ L0 L1) (ξ η : ZMod 6) :
    6 * L1 ξ η (v η) + 6 * zpow ζ (ξ - η) * L1 ξ (ξ + 3) (v (ξ + 3)) =
      rho1_6 ζ ξ η * d1Form ζ ξ (v ξ) := by
  obtain ⟨-, -, -, -, -, g2, g3, g4, g5, g0⟩ := hv ξ
  let S : ZMod 6 → K := fun c => ∑ μ : ZMod 6, zpow ζ (c * μ) * L1 ξ μ (v μ)
  have hrhs : ∑ c : ZMod 6, w1 ζ ξ η c * S c = rho1_6 ζ ξ η * d1Form ζ ξ (v ξ) := by
    rw [sum_zmod6]
    dsimp only [S]
    rw [g0, w1_one hζ, g2, g3, g4, g5]
    dsimp [rho1_6]
    ring
  have hlhs : ∑ c : ZMod 6, w1 ζ ξ η c * S c =
      6 * L1 ξ η (v η) + 6 * zpow ζ (ξ - η) * L1 ξ (ξ + 3) (v (ξ + 3)) := by
    dsimp [S]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    have hinner : ∀ μ : ZMod 6,
        (∑ c : ZMod 6, w1 ζ ξ η c * (zpow ζ (c * μ) * L1 ξ μ (v μ))) =
          ((if μ = η then (6 : K) else 0) +
            zpow ζ (ξ - η) * (if μ = ξ + 3 then (6 : K) else 0)) * L1 ξ μ (v μ) := by
      intro μ
      rw [← sum_w1_zpow hζ ξ η μ, Finset.sum_mul]
      refine Finset.sum_congr rfl fun c _ => by ring
    simp_rw [hinner, add_mul]
    rw [Finset.sum_add_distrib]
    simp only [ite_mul, zero_mul, mul_assoc, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    ring
  exact hlhs.symm.trans hrhs

/-! ### Scalar Identities & Nonvanishing in `ℤ[ζ]` -/

private lemma six_ne_zero {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) :
    (6 : K) ≠ 0 := by
  have h6 : (6 : K) = 2 * 3 := by norm_num
  rw [h6]
  exact mul_ne_zero h2 h3

private lemma w0_shift {ζ : K} (hζ : ζ ^ 2 = ζ - 1) (a δ ε c : ZMod 6) :
    w0 ζ (a + δ) (a + ε) c = zpow ζ (- (c * a)) * w0 ζ δ ε c := by
  dsimp [w0]
  have e1 : - (c * (a + ε)) = - (c * a) + (- (c * ε)) := by ring
  have e2 : (a + ε) - (a + δ) = ε - δ := by ring
  have e3 : - (c * (a + δ + 3)) = - (c * a) + (- (c * (δ + 3))) := by ring
  rw [e1, e2, e3, zpow_add hζ, zpow_add hζ]
  ring

private lemma w1_shift {ζ : K} (hζ : ζ ^ 2 = ζ - 1) (a δ ε c : ZMod 6) :
    w1 ζ (a + δ) (a + ε) c = zpow ζ (- (c * a)) * w1 ζ δ ε c := by
  dsimp [w1]
  have e1 : - (c * (a + ε)) = - (c * a) + (- (c * ε)) := by ring
  have e2 : (a + δ) - (a + ε) = δ - ε := by ring
  have e3 : - (c * (a + δ + 3)) = - (c * a) + (- (c * (δ + 3))) := by ring
  rw [e1, e2, e3, zpow_add hζ, zpow_add hζ]
  ring

private lemma rho0_shift {ζ : K} (hζ : ζ ^ 2 = ζ - 1) (a δ ε : ZMod 6) :
    rho0_6 ζ (a + δ) (a + ε) = zpow ζ (3 * a) * rho0_6 ζ δ ε := by
  dsimp [rho0_6]
  rw [w0_shift hζ, w0_shift hζ, zpow_add hζ a δ]
  have h1 : (- ((3 : ZMod 6) * a)) = 3 * a := by
    rcases zmod6_cases a with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have h2 : (- ((4 : ZMod 6) * a)) + a = 3 * a := by
    rcases zmod6_cases a with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  calc zpow ζ (- (3 * a)) * w0 ζ δ ε 3 + zpow ζ (- (4 * a)) * w0 ζ δ ε 4 * (zpow ζ a * zpow ζ δ)
      = zpow ζ (- (3 * a)) * w0 ζ δ ε 3 +
          (zpow ζ (- (4 * a)) * zpow ζ a) * (w0 ζ δ ε 4 * zpow ζ δ) := by ring
    _ = zpow ζ (3 * a) * w0 ζ δ ε 3 +
          zpow ζ (3 * a) * (w0 ζ δ ε 4 * zpow ζ δ) := by rw [← zpow_add hζ, h1, h2]
    _ = zpow ζ (3 * a) * (w0 ζ δ ε 3 + w0 ζ δ ε 4 * zpow ζ δ) := by ring

private lemma rho1_shift {ζ : K} (hζ : ζ ^ 2 = ζ - 1) (a δ ε : ZMod 6) :
    rho1_6 ζ (a + δ) (a + ε) = zpow ζ (2 * a) * rho1_6 ζ δ ε := by
  dsimp [rho1_6]
  rw [w1_shift hζ, w1_shift hζ, w1_shift hζ, zpow_add hζ a δ,
    show 2 * (a + δ) = 2 * a + 2 * δ by ring, zpow_add hζ (2 * a) (2 * δ)]
  have h1 : (- ((4 : ZMod 6) * a)) = 2 * a := by
    rcases zmod6_cases a with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have h2 : (- ((5 : ZMod 6) * a)) + a = 2 * a := by
    rcases zmod6_cases a with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have h3 : (- ((0 : ZMod 6) * a)) + 2 * a = 2 * a := by ring
  calc zpow ζ (- (4 * a)) * w1 ζ δ ε 4 + zpow ζ (- (5 * a)) * w1 ζ δ ε 5 * (zpow ζ a * zpow ζ δ) +
          zpow ζ (- (0 * a)) * w1 ζ δ ε 0 * (zpow ζ (2 * a) * zpow ζ (2 * δ))
      = zpow ζ (- (4 * a)) * w1 ζ δ ε 4 +
          (zpow ζ (- (5 * a)) * zpow ζ a) * (w1 ζ δ ε 5 * zpow ζ δ) +
          (zpow ζ (- (0 * a)) * zpow ζ (2 * a)) * (w1 ζ δ ε 0 * zpow ζ (2 * δ)) := by ring
    _ = zpow ζ (2 * a) * w1 ζ δ ε 4 +
          zpow ζ (2 * a) * (w1 ζ δ ε 5 * zpow ζ δ) +
          zpow ζ (2 * a) * (w1 ζ δ ε 0 * zpow ζ (2 * δ)) := by
            rw [← zpow_add hζ, ← zpow_add hζ, h1, h2, h3]
    _ = zpow ζ (2 * a) * (w1 ζ δ ε 4 + w1 ζ δ ε 5 * zpow ζ δ + w1 ζ δ ε 0 * zpow ζ (2 * δ)) := by
          ring

private lemma rho0_antipodal_sum {ζ : K} (hζ : ζ ^ 2 = ζ - 1) (ξ a : ZMod 6) :
    rho0_6 ζ ξ a + rho0_6 ζ ξ (a + 3) = 2 * zpow ζ (ξ + 2 * a) := by
  have hbase : ∀ d : ZMod 6, rho0_6 ζ 0 d + rho0_6 ζ 0 (d + 3) = 2 * zpow ζ (2 * d) := by
    intro d
    rcases zmod6_cases d with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := { decide := true }) only [rho0_6, w0, zpow_eval hζ, ↓reduceIte] <;>
      ring
  let d : ZMod 6 := a - ξ
  have ha1 : rho0_6 ζ ξ a = zpow ζ (3 * ξ) * rho0_6 ζ 0 d := by
    simpa [d] using rho0_shift hζ ξ 0 (a - ξ)
  have ha2 : rho0_6 ζ ξ (a + 3) = zpow ζ (3 * ξ) * rho0_6 ζ 0 (d + 3) := by
    have := rho0_shift hζ ξ 0 (d + 3)
    have heq : ξ + (d + 3) = a + 3 := by dsimp [d]; ring
    rw [add_zero, heq] at this
    exact this
  have hexp : 3 * ξ + 2 * d = ξ + 2 * a := by dsimp [d]; ring
  calc rho0_6 ζ ξ a + rho0_6 ζ ξ (a + 3)
      = zpow ζ (3 * ξ) * (rho0_6 ζ 0 d + rho0_6 ζ 0 (d + 3)) := by rw [ha1, ha2]; ring
    _ = 2 * (zpow ζ (3 * ξ) * zpow ζ (2 * d)) := by rw [hbase d]; ring
    _ = 2 * zpow ζ (ξ + 2 * a) := by rw [← zpow_add hζ, hexp]

private lemma rho1_antipodal_sum {ζ : K} (hζ : ζ ^ 2 = ζ - 1) {ξ a : ZMod 6}
    (h1 : ξ ≠ a) (h2_ne : ξ ≠ a + 3) :
    rho1_6 ζ ξ a + rho1_6 ζ ξ (a + 3) = -2 * zpow ζ (4 * a - 2 * ξ) := by
  have hbase : ∀ d : ZMod 6, d ≠ 0 → d ≠ 3 →
      rho1_6 ζ 0 d + rho1_6 ζ 0 (d + 3) = -2 * zpow ζ (4 * d) := by
    intro d hd0 hd3
    rcases zmod6_cases d with rfl | rfl | rfl | rfl | rfl | rfl
    · exact False.elim (hd0 rfl)
    · simp (config := { decide := true }) only [rho1_6, w1, zpow_eval hζ, ↓reduceIte]; ring
    · simp (config := { decide := true }) only [rho1_6, w1, zpow_eval hζ, ↓reduceIte]; ring
    · exact False.elim (hd3 rfl)
    · simp (config := { decide := true }) only [rho1_6, w1, zpow_eval hζ, ↓reduceIte]; ring
    · simp (config := { decide := true }) only [rho1_6, w1, zpow_eval hζ, ↓reduceIte]; ring
  let d : ZMod 6 := a - ξ
  have hd0 : d ≠ 0 := fun h => h1 (sub_eq_zero.mp h).symm
  have hd3 : d ≠ 3 := by
    intro h
    apply h2_ne
    have h6z : (6 : ZMod 6) = 0 := by decide
    calc ξ = a - d := by dsimp [d]; ring
      _ = a - 3 := by rw [h]
      _ = a + 3 - 6 := by ring
      _ = a + 3 := by rw [h6z, sub_zero]
  have ha1 : rho1_6 ζ ξ a = zpow ζ (2 * ξ) * rho1_6 ζ 0 d := by
    simpa [d] using rho1_shift hζ ξ 0 (a - ξ)
  have ha2 : rho1_6 ζ ξ (a + 3) = zpow ζ (2 * ξ) * rho1_6 ζ 0 (d + 3) := by
    have := rho1_shift hζ ξ 0 (d + 3)
    have heq : ξ + (d + 3) = a + 3 := by dsimp [d]; ring
    rw [add_zero, heq] at this
    exact this
  have hexp : 2 * ξ + 4 * d = 4 * a - 2 * ξ := by dsimp [d]; ring
  calc rho1_6 ζ ξ a + rho1_6 ζ ξ (a + 3)
      = zpow ζ (2 * ξ) * (rho1_6 ζ 0 d + rho1_6 ζ 0 (d + 3)) := by rw [ha1, ha2]; ring
    _ = -2 * (zpow ζ (2 * ξ) * zpow ζ (4 * d)) := by rw [hbase d hd0 hd3]; ring
    _ = -2 * zpow ζ (4 * a - 2 * ξ) := by rw [← zpow_add hζ, hexp]

private lemma rho_shift1_ne_zero (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    {ζ : K} (hζ : ζ ^ 2 = ζ - 1) (a : ZMod 6) :
    rho0_6 ζ a (a + 1) ≠ 0 ∧ rho1_6 ζ a (a + 1) ≠ 0 ∧
      rho0_6 ζ a (a + 4) ≠ 0 ∧ rho1_6 ζ a (a + 4) ≠ 0 := by
  have hr0_1 : rho0_6 ζ 0 1 * (-1 - ζ) = 3 := by
    simp (config := { decide := true }) only [rho0_6, w0, zpow_eval hζ, ↓reduceIte]
    linear_combination -hζ
  have hr1_1 : rho1_6 ζ 0 1 * (2 - ζ) = 3 := by
    simp (config := { decide := true }) only [rho1_6, w1, zpow_eval hζ, ↓reduceIte]
    linear_combination -hζ
  have hr0_4 : rho0_6 ζ 0 4 * (1 - ζ) = 1 := by
    simp (config := { decide := true }) only [rho0_6, w0, zpow_eval hζ, ↓reduceIte]
    linear_combination -hζ
  have hr1_4 : rho1_6 ζ 0 4 * (-ζ) = 1 := by
    simp (config := { decide := true }) only [rho1_6, w1, zpow_eval hζ, ↓reduceIte]
    linear_combination -hζ
  have h01_ne : rho0_6 ζ 0 1 ≠ 0 := left_ne_zero_of_mul (hr0_1.symm ▸ h3)
  have h11_ne : rho1_6 ζ 0 1 ≠ 0 := left_ne_zero_of_mul (hr1_1.symm ▸ h3)
  have h04_ne : rho0_6 ζ 0 4 ≠ 0 := left_ne_zero_of_mul (hr0_4.symm ▸ one_ne_zero)
  have h14_ne : rho1_6 ζ 0 4 ≠ 0 := left_ne_zero_of_mul (hr1_4.symm ▸ one_ne_zero)
  have eq1 : rho0_6 ζ a (a + 1) = zpow ζ (3 * a) * rho0_6 ζ 0 1 := by
    simpa using rho0_shift hζ a 0 1
  have eq2 : rho1_6 ζ a (a + 1) = zpow ζ (2 * a) * rho1_6 ζ 0 1 := by
    simpa using rho1_shift hζ a 0 1
  have eq3 : rho0_6 ζ a (a + 4) = zpow ζ (3 * a) * rho0_6 ζ 0 4 := by
    simpa using rho0_shift hζ a 0 4
  have eq4 : rho1_6 ζ a (a + 4) = zpow ζ (2 * a) * rho1_6 ζ 0 4 := by
    simpa using rho1_shift hζ a 0 4
  have _ := h2
  exact ⟨eq1 ▸ mul_ne_zero (zpow_ne_zero hζ _) h01_ne,
    eq2 ▸ mul_ne_zero (zpow_ne_zero hζ _) h11_ne,
    eq3 ▸ mul_ne_zero (zpow_ne_zero hζ _) h04_ne,
    eq4 ▸ mul_ne_zero (zpow_ne_zero hζ _) h14_ne⟩

private lemma nonantipodal_diffs_ne_zero (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    {ζ : K} (hζ : ζ ^ 2 = ζ - 1) (a : ZMod 6) :
    (zpow ζ (-a) * rho0_6 ζ (a + 2) a - zpow ζ (- (a + 1)) * rho0_6 ζ (a + 2) (a + 1) ≠ 0) ∧
    (zpow ζ a * rho1_6 ζ (a + 2) a - zpow ζ (a + 1) * rho1_6 ζ (a + 2) (a + 1) ≠ 0) ∧
    (zpow ζ (-a) * rho0_6 ζ (a + 5) a - zpow ζ (- (a + 1)) * rho0_6 ζ (a + 5) (a + 1) ≠ 0) ∧
    (zpow ζ a * rho1_6 ζ (a + 5) a - zpow ζ (a + 1) * rho1_6 ζ (a + 5) (a + 1) ≠ 0) ∧
    (zpow ζ (-a) * rho0_6 ζ (a + 1) a - zpow ζ (- (a + 2)) * rho0_6 ζ (a + 1) (a + 2) ≠ 0) ∧
    (zpow ζ a * rho1_6 ζ (a + 1) a - zpow ζ (a + 2) * rho1_6 ζ (a + 1) (a + 2) ≠ 0) := by
  have h4_ne : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    exact this ▸ mul_ne_zero h2 h2
  have h12_ne : (12 : K) ≠ 0 := by
    have : (12 : K) = 4 * 3 := by norm_num
    exact this ▸ mul_ne_zero h4_ne h3
  let d0_2 := rho0_6 ζ 2 0 - zpow ζ (-1) * rho0_6 ζ 2 1
  let d1_2 := rho1_6 ζ 2 0 - zpow ζ 1 * rho1_6 ζ 2 1
  let d0_5 := rho0_6 ζ 5 0 - zpow ζ (-1) * rho0_6 ζ 5 1
  let d1_5 := rho1_6 ζ 5 0 - zpow ζ 1 * rho1_6 ζ 5 1
  let d0_1 := rho0_6 ζ 1 0 - zpow ζ (-2) * rho0_6 ζ 1 2
  let d1_1 := rho1_6 ζ 1 0 - zpow ζ 2 * rho1_6 ζ 1 2
  have p1 : d0_2 * 2 = 4 := by
    dsimp only [d0_2]
    simp (config := { decide := true }) only [rho0_6, w0, zpow_eval hζ, ↓reduceIte]
    linear_combination (2 * ζ ^ 2 - 2) * hζ
  have p2 : d1_2 * (2 - 2 * ζ) = 4 := by
    dsimp only [d1_2]
    simp (config := { decide := true }) only [rho1_6, w1, zpow_eval hζ, ↓reduceIte]
    linear_combination (-2 * ζ ^ 3 + 4 * ζ ^ 2 - 4 * ζ - 2) * hζ
  have p3 : d0_5 * (2 * ζ) = 4 := by
    dsimp only [d0_5]
    simp (config := { decide := true }) only [rho0_6, w0, zpow_eval hζ, ↓reduceIte]
    linear_combination (2 * ζ ^ 3 - 4 * ζ ^ 2 + 6 * ζ - 4) * hζ
  have p4 : d1_5 * (2 * ζ) = 4 := by
    dsimp only [d1_5]
    simp (config := { decide := true }) only [rho1_6, w1, zpow_eval hζ, ↓reduceIte]
    linear_combination (-2 * ζ ^ 3 + 2 * ζ ^ 2 - 2 * ζ - 4) * hζ
  have p5 : d0_1 * (4 - 2 * ζ) = 12 := by
    dsimp only [d0_1]
    simp (config := { decide := true }) only [rho0_6, w0, zpow_eval hζ, ↓reduceIte]
    linear_combination (-2 * ζ ^ 3 + 8 * ζ ^ 2 - 8 * ζ - 4) * hζ
  have p6 : d1_1 * (2 - 4 * ζ) = 12 := by
    dsimp only [d1_1]
    simp (config := { decide := true }) only [rho1_6, w1, zpow_eval hζ, ↓reduceIte]
    linear_combination (4 * ζ ^ 3 - 6 * ζ ^ 2 + 6 * ζ - 18) * hζ
  have cov0 : ∀ δ ε : ZMod 6,
      zpow ζ (-a) * rho0_6 ζ (a + δ) a - zpow ζ (- (a + ε)) * rho0_6 ζ (a + δ) (a + ε) =
        zpow ζ (2 * a) * (rho0_6 ζ δ 0 - zpow ζ (-ε) * rho0_6 ζ δ ε) := by
    intro δ ε
    have s0 : rho0_6 ζ (a + δ) a = zpow ζ (3 * a) * rho0_6 ζ δ 0 := by
      simpa using rho0_shift hζ a δ 0
    have s1 : rho0_6 ζ (a + δ) (a + ε) = zpow ζ (3 * a) * rho0_6 ζ δ ε :=
      rho0_shift hζ a δ ε
    have hneg : zpow ζ (- (a + ε)) = zpow ζ (-a) * zpow ζ (-ε) := by
      rw [show - (a + ε) = (-a) + (-ε) by ring, zpow_add hζ]
    have hexp : zpow ζ (-a) * zpow ζ (3 * a) = zpow ζ (2 * a) := by
      rw [← zpow_add hζ, show (-a) + 3 * a = 2 * a by ring]
    rw [s0, s1, hneg]
    calc zpow ζ (-a) * (zpow ζ (3 * a) * rho0_6 ζ δ 0) -
            zpow ζ (-a) * zpow ζ (-ε) * (zpow ζ (3 * a) * rho0_6 ζ δ ε)
        = (zpow ζ (-a) * zpow ζ (3 * a)) * (rho0_6 ζ δ 0 - zpow ζ (-ε) * rho0_6 ζ δ ε) := by ring
      _ = zpow ζ (2 * a) * (rho0_6 ζ δ 0 - zpow ζ (-ε) * rho0_6 ζ δ ε) := by rw [hexp]
  have cov1 : ∀ δ ε : ZMod 6,
      zpow ζ a * rho1_6 ζ (a + δ) a - zpow ζ (a + ε) * rho1_6 ζ (a + δ) (a + ε) =
        zpow ζ (3 * a) * (rho1_6 ζ δ 0 - zpow ζ ε * rho1_6 ζ δ ε) := by
    intro δ ε
    have s0 : rho1_6 ζ (a + δ) a = zpow ζ (2 * a) * rho1_6 ζ δ 0 := by
      simpa using rho1_shift hζ a δ 0
    have s1 : rho1_6 ζ (a + δ) (a + ε) = zpow ζ (2 * a) * rho1_6 ζ δ ε :=
      rho1_shift hζ a δ ε
    have hexp : zpow ζ a * zpow ζ (2 * a) = zpow ζ (3 * a) := by
      rw [← zpow_add hζ, show a + 2 * a = 3 * a by ring]
    rw [s0, s1, zpow_add hζ a ε]
    calc zpow ζ a * (zpow ζ (2 * a) * rho1_6 ζ δ 0) -
            zpow ζ a * zpow ζ ε * (zpow ζ (2 * a) * rho1_6 ζ δ ε)
        = (zpow ζ a * zpow ζ (2 * a)) * (rho1_6 ζ δ 0 - zpow ζ ε * rho1_6 ζ δ ε) := by ring
      _ = zpow ζ (3 * a) * (rho1_6 ζ δ 0 - zpow ζ ε * rho1_6 ζ δ ε) := by rw [hexp]
  exact ⟨(cov0 2 1) ▸ mul_ne_zero (zpow_ne_zero hζ _) (left_ne_zero_of_mul (p1.symm ▸ h4_ne)),
    (cov1 2 1) ▸ mul_ne_zero (zpow_ne_zero hζ _) (left_ne_zero_of_mul (p2.symm ▸ h4_ne)),
    (cov0 5 1) ▸ mul_ne_zero (zpow_ne_zero hζ _) (left_ne_zero_of_mul (p3.symm ▸ h4_ne)),
    (cov1 5 1) ▸ mul_ne_zero (zpow_ne_zero hζ _) (left_ne_zero_of_mul (p4.symm ▸ h4_ne)),
    (cov0 1 2) ▸ mul_ne_zero (zpow_ne_zero hζ _) (left_ne_zero_of_mul (p5.symm ▸ h12_ne)),
    (cov1 1 2) ▸ mul_ne_zero (zpow_ne_zero hζ _) (left_ne_zero_of_mul (p6.symm ▸ h12_ne))⟩

/-! ### Step A: Antipodal Cancellation & Direct-Sum Subspace `KSum` -/

private theorem mem_KSub_of_antipodal_zero (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    {ζ : K} (hζ : ζ ^ 2 = ζ - 1)
    {L0 L1 : ZMod 6 → ZMod 6 → ((Fin 4 → K) →ₗ[K] K)}
    {w : ZMod 6 → Fin 4 → K} (hw : w ∈ FourierCodeSpace ζ L0 L1)
    {a : ZMod 6} (hwa : w a = 0) (hwa3 : w (a + 3) = 0) (η : ZMod 6) :
    w η ∈ KSub ζ L0 L1 η := by
  have h6 : (6 : K) ≠ 0 := six_ne_zero h2 h3
  have hd0_all : ∀ ξ : ZMod 6, d0Form ζ ξ (w ξ) = 0 := by
    intro ξ
    by_cases hξa : ξ = a
    · subst hξa; simp [hwa]
    · by_cases hξa3 : ξ = a + 3
      · subst hξa3; simp [hwa3]
      · have e1 := elim_color0 hζ hw ξ a
        have e2 := elim_color0 hζ hw ξ (a + 3)
        have hadd : a + 3 - ξ = (a - ξ) + 3 := by ring
        rw [hwa, map_zero, mul_zero, zero_add] at e1
        rw [hwa3, map_zero, mul_zero, zero_add, hadd, zpow_add_three hζ] at e2
        have hsum : (rho0_6 ζ ξ a + rho0_6 ζ ξ (a + 3)) * d0Form ζ ξ (w ξ) = 0 := by
          linear_combination -e1 - e2
        rw [rho0_antipodal_sum hζ] at hsum
        exact (mul_eq_zero.mp hsum).resolve_left (mul_ne_zero h2 (zpow_ne_zero hζ _))
  have hd1_all : ∀ ξ : ZMod 6, d1Form ζ ξ (w ξ) = 0 := by
    intro ξ
    by_cases hξa : ξ = a
    · subst hξa; simp [hwa]
    · by_cases hξa3 : ξ = a + 3
      · subst hξa3; simp [hwa3]
      · have e1 := elim_color1 hζ hw ξ a
        have e2 := elim_color1 hζ hw ξ (a + 3)
        have hsub : ξ - (a + 3) = (ξ - a) - 3 := by ring
        rw [hwa, map_zero, mul_zero, zero_add] at e1
        rw [hwa3, map_zero, mul_zero, zero_add, hsub, zpow_sub_three hζ] at e2
        have hsum : (rho1_6 ζ ξ a + rho1_6 ζ ξ (a + 3)) * d1Form ζ ξ (w ξ) = 0 := by
          linear_combination -e1 - e2
        rw [rho1_antipodal_sum hζ hξa hξa3] at hsum
        have hne : (-2 : K) * zpow ζ (4 * a - 2 * ξ) ≠ 0 :=
          mul_ne_zero (neg_ne_zero.mpr h2) (zpow_ne_zero hζ _)
        exact (mul_eq_zero.mp hsum).resolve_left hne
  rw [mem_KSub_iff hζ]
  refine ⟨hd0_all η, hd1_all η, fun ξ => ?_⟩
  have hL0_3 : L0 ξ (ξ + 3) (w (ξ + 3)) = 0 := by
    by_cases h : ξ + 3 = a
    · rw [h, hwa, map_zero]
    · have ea := elim_color0 hζ hw ξ a
      rw [hwa, map_zero, mul_zero, zero_add, hd0_all ξ, mul_zero] at ea
      exact (mul_eq_zero.mp ea).resolve_left (mul_ne_zero h6 (zpow_ne_zero hζ _))
  have hL1_3 : L1 ξ (ξ + 3) (w (ξ + 3)) = 0 := by
    by_cases h : ξ + 3 = a
    · rw [h, hwa, map_zero]
    · have ea := elim_color1 hζ hw ξ a
      rw [hwa, map_zero, mul_zero, zero_add, hd1_all ξ, mul_zero] at ea
      exact (mul_eq_zero.mp ea).resolve_left (mul_ne_zero h6 (zpow_ne_zero hζ _))
  have e0 := elim_color0 hζ hw ξ η
  rw [hL0_3, mul_zero, add_zero, hd0_all ξ, mul_zero] at e0
  have e1 := elim_color1 hζ hw ξ η
  rw [hL1_3, mul_zero, add_zero, hd1_all ξ, mul_zero] at e1
  exact ⟨(mul_eq_zero.mp e0).resolve_left h6, (mul_eq_zero.mp e1).resolve_left h6⟩

/-- Direct sum `KSum = ⨁_η K_η` viewed inside `FourierCodeSpace ζ L0 L1`. -/
private def KSumSub (ζ : K) (L0 L1 : ZMod 6 → ZMod 6 → ((Fin 4 → K) →ₗ[K] K)) :
    Submodule K (FourierCodeSpace ζ L0 L1) where
  carrier := {v | ∀ η : ZMod 6, v.1 η ∈ KSub ζ L0 L1 η}
  zero_mem' _ := Submodule.zero_mem _
  add_mem' ha hb η := Submodule.add_mem _ (ha η) (hb η)
  smul_mem' c _ ha η := Submodule.smul_mem _ c (ha η)

private lemma sum_singleMode_mem {ζ : K} {L0 L1 : ZMod 6 → ZMod 6 → ((Fin 4 → K) →ₗ[K] K)}
    (f : ∀ η : ZMod 6, KSub ζ L0 L1 η) :
    (fun η => (f η).1) ∈ FourierCodeSpace ζ L0 L1 := by
  have heq : (fun η => (f η).1) = ∑ η : ZMod 6, singleMode K η (f η).1 := by
    funext μ
    simp [singleMode, Pi.single_apply]
  rw [heq]
  exact Submodule.sum_mem _ fun η _ => (f η).2

private lemma finrank_KSumSub (ζ : K) (L0 L1 : ZMod 6 → ZMod 6 → ((Fin 4 → K) →ₗ[K] K)) :
    finrank K (KSumSub ζ L0 L1) = ∑ η : ZMod 6, finrank K (KSub ζ L0 L1 η) := by
  let e : KSumSub ζ L0 L1 ≃ₗ[K] (∀ η : ZMod 6, KSub ζ L0 L1 η) :=
    { toFun := fun v η => ⟨v.1.1 η, v.2 η⟩
      invFun := fun f => ⟨⟨fun η => (f η).1, sum_singleMode_mem f⟩, fun η => (f η).2⟩
      left_inv := fun v => by ext η i; rfl
      right_inv := fun f => by ext η i; rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  rw [e.finrank_eq, Module.finrank_pi_fintype]

/-! ### Section 3: Quotient Analysis & Master `≤ 14` Bound (`S_K ≤ 10`, `S_K = 11`, `S_K = 12`) -/

section QuotientAnalysis

variable (ζ : K) (L0 L1 : ZMod 6 → ZMod 6 → ((Fin 4 → K) →ₗ[K] K))

private abbrev QMod := (FourierCodeSpace ζ L0 L1) ⧸ (KSumSub ζ L0 L1)

private def projQ (a : ZMod 6) : QMod ζ L0 L1 →ₗ[K] ((Fin 4 → K) ⧸ KSub ζ L0 L1 a) :=
  (KSumSub ζ L0 L1).liftQ
    ((Submodule.mkQ (KSub ζ L0 L1 a)).comp
      ((LinearMap.proj a).comp (FourierCodeSpace ζ L0 L1).subtype))
    (fun v hv => by
      simp only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.coe_subtype,
        LinearMap.proj_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hv a)

private def NSub (a : ZMod 6) : Submodule K (QMod ζ L0 L1) :=
  LinearMap.ker (projQ ζ L0 L1 a)

private def L0Q (hζ : ζ ^ 2 = ζ - 1) (ξ η : ZMod 6) : QMod ζ L0 L1 →ₗ[K] K :=
  (KSumSub ζ L0 L1).liftQ
    ((L0 ξ η).comp ((LinearMap.proj η).comp (FourierCodeSpace ζ L0 L1).subtype))
    (fun _ hv => ((mem_KSub_iff hζ).mp (hv η)).2.2 ξ |>.1)

private def L1Q (hζ : ζ ^ 2 = ζ - 1) (ξ η : ZMod 6) : QMod ζ L0 L1 →ₗ[K] K :=
  (KSumSub ζ L0 L1).liftQ
    ((L1 ξ η).comp ((LinearMap.proj η).comp (FourierCodeSpace ζ L0 L1).subtype))
    (fun _ hv => ((mem_KSub_iff hζ).mp (hv η)).2.2 ξ |>.2)

private def d0Q (hζ : ζ ^ 2 = ζ - 1) (η : ZMod 6) : QMod ζ L0 L1 →ₗ[K] K :=
  (KSumSub ζ L0 L1).liftQ
    ((d0Form ζ η).comp ((LinearMap.proj η).comp (FourierCodeSpace ζ L0 L1).subtype))
    (fun _ hv => ((mem_KSub_iff hζ).mp (hv η)).1)

private def d1Q (hζ : ζ ^ 2 = ζ - 1) (η : ZMod 6) : QMod ζ L0 L1 →ₗ[K] K :=
  (KSumSub ζ L0 L1).liftQ
    ((d1Form ζ η).comp ((LinearMap.proj η).comp (FourierCodeSpace ζ L0 L1).subtype))
    (fun _ hv => ((mem_KSub_iff hζ).mp (hv η)).2.1)

private lemma elim_color0_Q {ζ : K} (hζ : ζ ^ 2 = ζ - 1)
    {L0 L1 : ZMod 6 → ZMod 6 → ((Fin 4 → K) →ₗ[K] K)}
    (q : QMod ζ L0 L1) (ξ η : ZMod 6) :
    6 * L0Q ζ L0 L1 hζ ξ η q + 6 * zpow ζ (η - ξ) * L0Q ζ L0 L1 hζ ξ (ξ + 3) q =
      rho0_6 ζ ξ η * d0Q ζ L0 L1 hζ ξ q := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective (KSumSub ζ L0 L1) q
  exact elim_color0 hζ v.2 ξ η

private lemma elim_color1_Q {ζ : K} (hζ : ζ ^ 2 = ζ - 1)
    {L0 L1 : ZMod 6 → ZMod 6 → ((Fin 4 → K) →ₗ[K] K)}
    (q : QMod ζ L0 L1) (ξ η : ZMod 6) :
    6 * L1Q ζ L0 L1 hζ ξ η q + 6 * zpow ζ (ξ - η) * L1Q ζ L0 L1 hζ ξ (ξ + 3) q =
      rho1_6 ζ ξ η * d1Q ζ L0 L1 hζ ξ q := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective (KSumSub ζ L0 L1) q
  exact elim_color1 hζ v.2 ξ η

private lemma forms_zero_of_mem_NSub {ζ : K} (hζ : ζ ^ 2 = ζ - 1)
    {L0 L1 : ZMod 6 → ZMod 6 → ((Fin 4 → K) →ₗ[K] K)}
    {a : ZMod 6} {q : QMod ζ L0 L1} (hq : q ∈ NSub ζ L0 L1 a) :
    d0Q ζ L0 L1 hζ a q = 0 ∧ d1Q ζ L0 L1 hζ a q = 0 ∧
      ∀ ξ : ZMod 6, L0Q ζ L0 L1 hζ ξ a q = 0 ∧ L1Q ζ L0 L1 hζ ξ a q = 0 := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective (KSumSub ζ L0 L1) q
  have hva : v.1 a ∈ KSub ζ L0 L1 a := by
    simpa [NSub, projQ, Submodule.Quotient.mk_eq_zero] using hq
  exact (mem_KSub_iff hζ).mp hva

private lemma mem_NSub_iff_of_finrank_eq_two {ζ : K} (hζ : ζ ^ 2 = ζ - 1)
    {L0 L1 : ZMod 6 → ZMod 6 → ((Fin 4 → K) →ₗ[K] K)}
    {a : ZMod 6} (hdim : finrank K (KSub ζ L0 L1 a) = 2) (q : QMod ζ L0 L1) :
    q ∈ NSub ζ L0 L1 a ↔ d0Q ζ L0 L1 hζ a q = 0 ∧ d1Q ζ L0 L1 hζ a q = 0 := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective (KSumSub ζ L0 L1) q
  have hKL := KSub_eq_LSub_of_finrank_eq_two hζ hdim
  change Submodule.mkQ (KSub ζ L0 L1 a) (v.1 a) = 0 ↔
    d0Form ζ a (v.1 a) = 0 ∧ d1Form ζ a (v.1 a) = 0
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hKL]
  exact Prod.ext_iff

private lemma finrank_QMod_le_add_NSub (a : ZMod 6) :
    finrank K (QMod ζ L0 L1) ≤
      (4 - finrank K (KSub ζ L0 L1 a)) + finrank K (NSub ζ L0 L1 a) := by
  have hrk := LinearMap.finrank_range_add_finrank_ker (projQ ζ L0 L1 a)
  have hle : finrank K (LinearMap.range (projQ ζ L0 L1 a)) ≤
      finrank K ((Fin 4 → K) ⧸ KSub ζ L0 L1 a) :=
    Submodule.finrank_le _
  have hquot := Submodule.finrank_quotient_add_finrank (KSub ζ L0 L1 a)
  rw [finrank_fin4] at hquot
  change _ ≤ _ + finrank K (LinearMap.ker (projQ ζ L0 L1 a))
  omega

private lemma antipodal_inf_eq_bot (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    {ζ : K} (hζ : ζ ^ 2 = ζ - 1)
    {L0 L1 : ZMod 6 → ZMod 6 → ((Fin 4 → K) →ₗ[K] K)} (a : ZMod 6) :
    NSub ζ L0 L1 a ⊓ NSub ζ L0 L1 (a + 3) = ⊥ := by
  rw [eq_bot_iff]
  intro q ⟨hqa, hqa3⟩
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective (KSumSub ζ L0 L1) q
  have hva : v.1 a ∈ KSub ζ L0 L1 a := by
    simpa [NSub, projQ, Submodule.Quotient.mk_eq_zero] using hqa
  have hva3 : v.1 (a + 3) ∈ KSub ζ L0 L1 (a + 3) := by
    simpa [NSub, projQ, Submodule.Quotient.mk_eq_zero] using hqa3
  have hne : a ≠ a + 3 := by
    rcases zmod6_cases a with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  let s1 : FourierCodeSpace ζ L0 L1 := ⟨singleMode K a (v.1 a), hva⟩
  let s2 : FourierCodeSpace ζ L0 L1 := ⟨singleMode K (a + 3) (v.1 (a + 3)), hva3⟩
  have hs1_K : s1 ∈ KSumSub ζ L0 L1 := by
    intro η
    by_cases h : η = a
    · subst h; simpa [s1, singleMode] using hva
    · simp [s1, singleMode, Pi.single_eq_of_ne h]
  have hs2_K : s2 ∈ KSumSub ζ L0 L1 := by
    intro η
    by_cases h : η = a + 3
    · subst h; simpa [s2, singleMode] using hva3
    · simp [s2, singleMode, Pi.single_eq_of_ne h]
  let w : FourierCodeSpace ζ L0 L1 := v - s1 - s2
  have hwa : w.1 a = 0 := by
    simp [w, s1, s2, singleMode, Pi.single_eq_of_ne hne]
  have hwa3 : w.1 (a + 3) = 0 := by
    simp [w, s1, s2, singleMode, Pi.single_eq_of_ne hne.symm]
  have hw_K : w ∈ KSumSub ζ L0 L1 := fun η =>
    mem_KSub_of_antipodal_zero h2 h3 hζ w.2 hwa hwa3 η
  have hv_K : v ∈ KSumSub ζ L0 L1 := by
    have heq : v = w + s1 + s2 := by dsimp only [w]; abel
    rw [heq]
    exact Submodule.add_mem _ (Submodule.add_mem _ hw_K hs1_K) hs2_K
  exact (Submodule.Quotient.mk_eq_zero _).mpr hv_K

private lemma finrank_QMod_le_antipodal (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    {ζ : K} (hζ : ζ ^ 2 = ζ - 1)
    {L0 L1 : ZMod 6 → ZMod 6 → ((Fin 4 → K) →ₗ[K] K)} (a : ZMod 6) :
    finrank K (QMod ζ L0 L1) ≤
      (4 - finrank K (KSub ζ L0 L1 a)) + (4 - finrank K (KSub ζ L0 L1 (a + 3))) := by
  let f := (projQ ζ L0 L1 a).prod (projQ ζ L0 L1 (a + 3))
  have hker : LinearMap.ker f = NSub ζ L0 L1 a ⊓ NSub ζ L0 L1 (a + 3) :=
    LinearMap.ker_prod _ _
  rw [antipodal_inf_eq_bot h2 h3 hζ a] at hker
  have hinj : Function.Injective f := LinearMap.ker_eq_bot.mp hker
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_prod] at hle
  have hq1 := Submodule.finrank_quotient_add_finrank (KSub ζ L0 L1 a)
  have hq2 := Submodule.finrank_quotient_add_finrank (KSub ζ L0 L1 (a + 3))
  rw [finrank_fin4] at hq1 hq2
  omega

private lemma sup_antipodal_eq_top_imp_le (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    {ζ : K} (hζ : ζ ^ 2 = ζ - 1)
    {L0 L1 : ZMod 6 → ZMod 6 → ((Fin 4 → K) →ₗ[K] K)}
    {a b : ZMod 6} (hdim_a : finrank K (KSub ζ L0 L1 a) = 2)
    (hsup : NSub ζ L0 L1 a ⊔ NSub ζ L0 L1 (a + 3) = ⊤)
    (hr0 : rho0_6 ζ a b ≠ 0) (hr1 : rho1_6 ζ a b ≠ 0) :
    NSub ζ L0 L1 b ≤ NSub ζ L0 L1 a := by
  have h6 : (6 : K) ≠ 0 := six_ne_zero h2 h3
  have hL_vanish : ∀ q : QMod ζ L0 L1,
      L0Q ζ L0 L1 hζ a (a + 3) q = 0 ∧ L1Q ζ L0 L1 hζ a (a + 3) q = 0 := by
    intro q
    have hmem : q ∈ NSub ζ L0 L1 a ⊔ NSub ζ L0 L1 (a + 3) := hsup ▸ Submodule.mem_top
    obtain ⟨q1, hq1, q2, hq2, rfl⟩ := Submodule.mem_sup.mp hmem
    obtain ⟨hd0_1, hd1_1, hL_1⟩ := forms_zero_of_mem_NSub hζ hq1
    obtain ⟨-, -, hL_2⟩ := forms_zero_of_mem_NSub hζ hq2
    have e0 := elim_color0_Q hζ q1 a a
    rw [(hL_1 a).1, hd0_1, sub_self, zpow_zero, mul_zero, zero_add, mul_one, mul_zero] at e0
    have e1 := elim_color1_Q hζ q1 a a
    rw [(hL_1 a).2, hd1_1, sub_self, zpow_zero, mul_zero, zero_add, mul_one, mul_zero] at e1
    have h0_q1 : L0Q ζ L0 L1 hζ a (a + 3) q1 = 0 := (mul_eq_zero.mp e0).resolve_left h6
    have h1_q1 : L1Q ζ L0 L1 hζ a (a + 3) q1 = 0 := (mul_eq_zero.mp e1).resolve_left h6
    simp [map_add, h0_q1, h1_q1, (hL_2 a).1, (hL_2 a).2]
  intro q hqb
  obtain ⟨-, -, hLb⟩ := forms_zero_of_mem_NSub hζ hqb
  have e0 := elim_color0_Q hζ q a b
  rw [(hLb a).1, (hL_vanish q).1, mul_zero, mul_zero, add_zero] at e0
  have e1 := elim_color1_Q hζ q a b
  rw [(hLb a).2, (hL_vanish q).2, mul_zero, mul_zero, add_zero] at e1
  rw [mem_NSub_iff_of_finrank_eq_two hζ hdim_a]
  exact ⟨(mul_eq_zero.mp e0.symm).resolve_left hr0,
    (mul_eq_zero.mp e1.symm).resolve_left hr1⟩

private lemma not_four_le_finrank_QMod (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    {ζ : K} (hζ : ζ ^ 2 = ζ - 1)
    {L0 L1 : ZMod 6 → ZMod 6 → ((Fin 4 → K) →ₗ[K] K)}
    (η₀ : ZMod 6) (h5 : ∀ η : ZMod 6, η ≠ η₀ → finrank K (KSub ζ L0 L1 η) = 2) :
    ¬ 4 ≤ finrank K (QMod ζ L0 L1) := by
  intro h4
  let a1 := η₀ + 1
  let a2 := η₀ + 2
  have ha1_ne : a1 ≠ η₀ := by
    dsimp [a1]; rcases zmod6_cases η₀ with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have ha1_3_ne : a1 + 3 ≠ η₀ := by
    dsimp [a1]; rcases zmod6_cases η₀ with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have ha2_ne : a2 ≠ η₀ := by
    dsimp [a2]; rcases zmod6_cases η₀ with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have ha2_3_ne : a2 + 3 ≠ η₀ := by
    dsimp [a2]; rcases zmod6_cases η₀ with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hd_a1 := h5 a1 ha1_ne
  have hd_a1_3 := h5 (a1 + 3) ha1_3_ne
  have hd_a2 := h5 a2 ha2_ne
  have hd_a2_3 := h5 (a2 + 3) ha2_3_ne
  have hle4 : finrank K (QMod ζ L0 L1) ≤ 4 := by
    have := finrank_QMod_le_antipodal h2 h3 hζ (L0 := L0) (L1 := L1) a1
    omega
  have hQ4 : finrank K (QMod ζ L0 L1) = 4 := le_antisymm hle4 h4
  have hN_a1 : 2 ≤ finrank K (NSub ζ L0 L1 a1) := by
    have := finrank_QMod_le_add_NSub ζ L0 L1 a1; omega
  have hN_a1_3 : 2 ≤ finrank K (NSub ζ L0 L1 (a1 + 3)) := by
    have := finrank_QMod_le_add_NSub ζ L0 L1 (a1 + 3); omega
  have hN_a2 : 2 ≤ finrank K (NSub ζ L0 L1 a2) := by
    have := finrank_QMod_le_add_NSub ζ L0 L1 a2; omega
  have hN_a2_3 : 2 ≤ finrank K (NSub ζ L0 L1 (a2 + 3)) := by
    have := finrank_QMod_le_add_NSub ζ L0 L1 (a2 + 3); omega
  have hgrass1 := Submodule.finrank_sup_add_finrank_inf_eq
    (NSub ζ L0 L1 a1) (NSub ζ L0 L1 (a1 + 3))
  rw [antipodal_inf_eq_bot h2 h3 hζ a1, finrank_bot, add_zero] at hgrass1
  have hsup1_le : finrank K ↥(NSub ζ L0 L1 a1 ⊔ NSub ζ L0 L1 (a1 + 3)) ≤ 4 :=
    (Submodule.finrank_le _).trans_eq hQ4
  have hN_a1_eq : finrank K (NSub ζ L0 L1 a1) = 2 := by omega
  have hsup1_eq : finrank K ↥(NSub ζ L0 L1 a1 ⊔ NSub ζ L0 L1 (a1 + 3)) =
      finrank K (QMod ζ L0 L1) := by omega
  have htop1 : NSub ζ L0 L1 a1 ⊔ NSub ζ L0 L1 (a1 + 3) = ⊤ :=
    Submodule.eq_top_of_finrank_eq hsup1_eq
  obtain ⟨hr0_1, hr1_1, hr0_4, hr1_4⟩ := rho_shift1_ne_zero h2 h3 hζ a1
  have heq_a2 : a2 = a1 + 1 := by dsimp [a1, a2]; ring
  have heq_a2_3 : a2 + 3 = a1 + 4 := by dsimp [a1, a2]; ring
  have hle_a2 : NSub ζ L0 L1 a2 ≤ NSub ζ L0 L1 a1 := by
    rw [heq_a2]
    exact sup_antipodal_eq_top_imp_le h2 h3 hζ hd_a1 htop1 hr0_1 hr1_1
  have hle_a2_3 : NSub ζ L0 L1 (a2 + 3) ≤ NSub ζ L0 L1 a1 := by
    rw [heq_a2_3]
    exact sup_antipodal_eq_top_imp_le h2 h3 hζ hd_a1 htop1 hr0_4 hr1_4
  have hsup2_le : NSub ζ L0 L1 a2 ⊔ NSub ζ L0 L1 (a2 + 3) ≤ NSub ζ L0 L1 a1 :=
    sup_le hle_a2 hle_a2_3
  have hgrass2 := Submodule.finrank_sup_add_finrank_inf_eq
    (NSub ζ L0 L1 a2) (NSub ζ L0 L1 (a2 + 3))
  rw [antipodal_inf_eq_bot h2 h3 hζ a2, finrank_bot, add_zero] at hgrass2
  have hmono := Submodule.finrank_mono hsup2_le
  omega

/-! ### Pairwise Disjointness & Exact `4 × 4` Elimination for `S_K = 12` -/

private lemma pairwise_NSub_inf_eq_bot (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    {ζ : K} (hζ : ζ ^ 2 = ζ - 1)
    {L0 L1 : ZMod 6 → ZMod 6 → ((Fin 4 → K) →ₗ[K] K)}
    (hall : ∀ η : ZMod 6, finrank K (KSub ζ L0 L1 η) = 2)
    {a b : ZMod 6} (hab : a ≠ b) :
    NSub ζ L0 L1 a ⊓ NSub ζ L0 L1 b = ⊥ := by
  have hdist1 : ∀ x : ZMod 6, NSub ζ L0 L1 x ⊓ NSub ζ L0 L1 (x + 1) = ⊥ := by
    intro x
    rw [eq_bot_iff]
    intro q ⟨hqx, hqx1⟩
    obtain ⟨-, -, hLx⟩ := forms_zero_of_mem_NSub hζ hqx
    obtain ⟨-, -, hLx1⟩ := forms_zero_of_mem_NSub hζ hqx1
    obtain ⟨hn1, hn2, hn3, hn4, -, -⟩ := nonantipodal_diffs_ne_zero h2 h3 hζ x
    have hmem_xi : ∀ ξ : ZMod 6,
        zpow ζ (-x) * rho0_6 ζ ξ x - zpow ζ (- (x + 1)) * rho0_6 ζ ξ (x + 1) ≠ 0 →
        zpow ζ x * rho1_6 ζ ξ x - zpow ζ (x + 1) * rho1_6 ζ ξ (x + 1) ≠ 0 →
        q ∈ NSub ζ L0 L1 ξ := by
      intro ξ hd0_ne hd1_ne
      have e0x := elim_color0_Q hζ q ξ x
      have e0x1 := elim_color0_Q hζ q ξ (x + 1)
      rw [(hLx ξ).1, mul_zero, zero_add] at e0x
      rw [(hLx1 ξ).1, mul_zero, zero_add] at e0x1
      have hcomb0 :
          (zpow ζ (-x) * rho0_6 ζ ξ x - zpow ζ (- (x + 1)) * rho0_6 ζ ξ (x + 1)) *
            d0Q ζ L0 L1 hζ ξ q =
          6 * ((zpow ζ (-x) * zpow ζ (x - ξ) - zpow ζ (- (x + 1)) * zpow ζ (x + 1 - ξ)) *
            L0Q ζ L0 L1 hζ ξ (ξ + 3) q) := by
        linear_combination - zpow ζ (-x) * e0x + zpow ζ (- (x + 1)) * e0x1
      have hzero0 : zpow ζ (-x) * zpow ζ (x - ξ) -
          zpow ζ (- (x + 1)) * zpow ζ (x + 1 - ξ) = 0 := by
        rw [← zpow_add hζ, ← zpow_add hζ]
        have heq : -x + (x - ξ) = - (x + 1) + (x + 1 - ξ) := by ring
        rw [heq, sub_self]
      rw [hzero0, zero_mul, mul_zero] at hcomb0
      have e1x := elim_color1_Q hζ q ξ x
      have e1x1 := elim_color1_Q hζ q ξ (x + 1)
      rw [(hLx ξ).2, mul_zero, zero_add] at e1x
      rw [(hLx1 ξ).2, mul_zero, zero_add] at e1x1
      have hcomb1 :
          (zpow ζ x * rho1_6 ζ ξ x - zpow ζ (x + 1) * rho1_6 ζ ξ (x + 1)) *
            d1Q ζ L0 L1 hζ ξ q =
          6 * ((zpow ζ x * zpow ζ (ξ - x) - zpow ζ (x + 1) * zpow ζ (ξ - (x + 1))) *
            L1Q ζ L0 L1 hζ ξ (ξ + 3) q) := by
        linear_combination - zpow ζ x * e1x + zpow ζ (x + 1) * e1x1
      have hzero1 : zpow ζ x * zpow ζ (ξ - x) -
          zpow ζ (x + 1) * zpow ζ (ξ - (x + 1)) = 0 := by
        rw [← zpow_add hζ, ← zpow_add hζ]
        have heq : x + (ξ - x) = (x + 1) + (ξ - (x + 1)) := by ring
        rw [heq, sub_self]
      rw [hzero1, zero_mul, mul_zero] at hcomb1
      rw [mem_NSub_iff_of_finrank_eq_two hζ (hall ξ)]
      exact ⟨(mul_eq_zero.mp hcomb0).resolve_left hd0_ne,
        (mul_eq_zero.mp hcomb1).resolve_left hd1_ne⟩
    have hq2 : q ∈ NSub ζ L0 L1 (x + 2) := hmem_xi (x + 2) hn1 hn2
    have hq5 : q ∈ NSub ζ L0 L1 ((x + 2) + 3) := by
      have heq : (x + 2) + 3 = x + 5 := by ring
      rw [heq]
      exact hmem_xi (x + 5) hn3 hn4
    have hbot := antipodal_inf_eq_bot h2 h3 hζ (L0 := L0) (L1 := L1) (x + 2)
    have hmem_bot : q ∈ (⊥ : Submodule K (QMod ζ L0 L1)) := hbot ▸ ⟨hq2, hq5⟩
    exact hmem_bot
  have hdist2 : ∀ x : ZMod 6, NSub ζ L0 L1 x ⊓ NSub ζ L0 L1 (x + 2) = ⊥ := by
    intro x
    rw [eq_bot_iff]
    intro q ⟨hqx, hqx2⟩
    obtain ⟨-, -, hLx⟩ := forms_zero_of_mem_NSub hζ hqx
    obtain ⟨-, -, hLx2⟩ := forms_zero_of_mem_NSub hζ hqx2
    obtain ⟨-, -, -, -, hn5, hn6⟩ := nonantipodal_diffs_ne_zero h2 h3 hζ x
    have e0x := elim_color0_Q hζ q (x + 1) x
    have e0x2 := elim_color0_Q hζ q (x + 1) (x + 2)
    rw [(hLx (x + 1)).1, mul_zero, zero_add] at e0x
    rw [(hLx2 (x + 1)).1, mul_zero, zero_add] at e0x2
    have hcomb0 :
        (zpow ζ (-x) * rho0_6 ζ (x + 1) x - zpow ζ (- (x + 2)) * rho0_6 ζ (x + 1) (x + 2)) *
          d0Q ζ L0 L1 hζ (x + 1) q =
        6 * ((zpow ζ (-x) * zpow ζ (x - (x + 1)) -
          zpow ζ (- (x + 2)) * zpow ζ (x + 2 - (x + 1))) *
            L0Q ζ L0 L1 hζ (x + 1) ((x + 1) + 3) q) := by
      linear_combination - zpow ζ (-x) * e0x + zpow ζ (- (x + 2)) * e0x2
    have hzero0 : zpow ζ (-x) * zpow ζ (x - (x + 1)) -
        zpow ζ (- (x + 2)) * zpow ζ (x + 2 - (x + 1)) = 0 := by
      rw [← zpow_add hζ, ← zpow_add hζ]
      have heq : -x + (x - (x + 1)) = - (x + 2) + (x + 2 - (x + 1)) := by ring
      rw [heq, sub_self]
    rw [hzero0, zero_mul, mul_zero] at hcomb0
    have e1x := elim_color1_Q hζ q (x + 1) x
    have e1x2 := elim_color1_Q hζ q (x + 1) (x + 2)
    rw [(hLx (x + 1)).2, mul_zero, zero_add] at e1x
    rw [(hLx2 (x + 1)).2, mul_zero, zero_add] at e1x2
    have hcomb1 :
        (zpow ζ x * rho1_6 ζ (x + 1) x - zpow ζ (x + 2) * rho1_6 ζ (x + 1) (x + 2)) *
          d1Q ζ L0 L1 hζ (x + 1) q =
        6 * ((zpow ζ x * zpow ζ ((x + 1) - x) -
          zpow ζ (x + 2) * zpow ζ ((x + 1) - (x + 2))) *
            L1Q ζ L0 L1 hζ (x + 1) ((x + 1) + 3) q) := by
      linear_combination - zpow ζ x * e1x + zpow ζ (x + 2) * e1x2
    have hzero1 : zpow ζ x * zpow ζ ((x + 1) - x) -
        zpow ζ (x + 2) * zpow ζ ((x + 1) - (x + 2)) = 0 := by
      rw [← zpow_add hζ, ← zpow_add hζ]
      have heq : x + ((x + 1) - x) = (x + 2) + ((x + 1) - (x + 2)) := by ring
      rw [heq, sub_self]
    rw [hzero1, zero_mul, mul_zero] at hcomb1
    have hqx1 : q ∈ NSub ζ L0 L1 (x + 1) := by
      rw [mem_NSub_iff_of_finrank_eq_two hζ (hall (x + 1))]
      exact ⟨(mul_eq_zero.mp hcomb0).resolve_left hn5,
        (mul_eq_zero.mp hcomb1).resolve_left hn6⟩
    have hmem_bot : q ∈ (⊥ : Submodule K (QMod ζ L0 L1)) := hdist1 x ▸ ⟨hqx, hqx1⟩
    exact hmem_bot
  rcases zmod6_cases (b - a) with h | h | h | h | h | h
  · exfalso; exact hab (sub_eq_zero.mp h).symm
  · have hb : b = a + 1 := by linear_combination h
    rw [hb]; exact hdist1 a
  · have hb : b = a + 2 := by linear_combination h
    rw [hb]; exact hdist2 a
  · have hb : b = a + 3 := by linear_combination h
    rw [hb]; exact antipodal_inf_eq_bot h2 h3 hζ a
  · have ha : a = b + 2 := by
      have h6z : (6 : ZMod 6) = 0 := by decide
      calc a = b - (b - a) := by ring
        _ = b - 4 := by rw [h]
        _ = b + 2 - 6 := by ring
        _ = b + 2 := by rw [h6z, sub_zero]
    rw [inf_comm, ha]; exact hdist2 b
  · have ha : a = b + 1 := by
      have h6z : (6 : ZMod 6) = 0 := by decide
      calc a = b - (b - a) := by ring
        _ = b - 5 := by rw [h]
        _ = b + 1 - 6 := by ring
        _ = b + 1 := by rw [h6z, sub_zero]
    rw [inf_comm, ha]; exact hdist1 b

private lemma eq_on_ker_of_finrank_ker_pair_one {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {φ₀ φ₁ γ : V →ₗ[K] K} {N : Submodule K V}
    (hN_iff : ∀ q : V, q ∈ N ↔ φ₀ q = 0 ∧ φ₁ q = 0)
    (hN_dim : finrank K N = 1)
    (hN_γ : ∀ q ∈ N, γ q = 0)
    {q₁ q₂ : V} (hq1 : φ₁ q₁ = 0) (hq2 : φ₁ q₂ = 0)
    (hγ1 : γ q₁ = 1) (hγ2 : γ q₂ = 1) :
    φ₀ q₁ = φ₀ q₂ := by
  let H : Submodule K V := LinearMap.ker φ₁
  let f₀ : H →ₗ[K] K := φ₀.comp H.subtype
  have hN_le_H : N ≤ H := fun q hq => (hN_iff q).mp hq |>.2
  let NH : Submodule K H := N.comap H.subtype
  have hNH_eq_ker : LinearMap.ker f₀ = NH := by
    ext ⟨q, hqH⟩
    simp only [LinearMap.mem_ker, f₀, LinearMap.comp_apply, Submodule.coe_subtype,
      NH, Submodule.mem_comap]
    exact ⟨fun h0 => (hN_iff q).mpr ⟨h0, hqH⟩, fun hN => (hN_iff q).mp hN |>.1⟩
  have hNH_dim : finrank K NH = 1 := by
    let e : NH ≃ₗ[K] N :=
      { toFun := fun x => ⟨x.1.1, x.2⟩
        invFun := fun y => ⟨⟨y.1, hN_le_H y.2⟩, y.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    exact e.finrank_eq.trans hN_dim
  have hH_le : finrank K H ≤ 2 := by
    have hrk := LinearMap.finrank_range_add_finrank_ker f₀
    have hr_le : finrank K (LinearMap.range f₀) ≤ finrank K K := Submodule.finrank_le _
    rw [finrank_self] at hr_le
    rw [hNH_eq_ker, hNH_dim] at hrk
    omega
  let g : H →ₗ[K] K × K := f₀.prod (γ.comp H.subtype)
  have hNH_le_ker_g : NH ≤ LinearMap.ker g := by
    intro ⟨q, hqH⟩ hqN
    rw [LinearMap.mem_ker]
    exact Prod.ext ((hN_iff q).mp hqN |>.1) (hN_γ q hqN)
  have hker_g_ge : 1 ≤ finrank K (LinearMap.ker g) :=
    hNH_dim ▸ Submodule.finrank_mono hNH_le_ker_g
  have hrg_le : finrank K (LinearMap.range g) ≤ 1 := by
    have hrk := LinearMap.finrank_range_add_finrank_ker g
    omega
  by_contra hne
  let v : Fin 2 → LinearMap.range g :=
    ![⟨(φ₀ q₁, 1), ⟨⟨q₁, hq1⟩, by simp [g, f₀, hγ1]⟩⟩,
      ⟨(φ₀ q₂, 1), ⟨⟨q₂, hq2⟩, by simp [g, f₀, hγ2]⟩⟩]
  have hlin : LinearIndependent K v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hc_fst : c 0 * φ₀ q₁ + c 1 * φ₀ q₂ = 0 := by
      have h := congrArg (fun x : LinearMap.range g => x.1.1) hc
      rw [Fin.sum_univ_two] at h
      simpa [v] using h
    have hc_snd : c 0 + c 1 = 0 := by
      have h := congrArg (fun x : LinearMap.range g => x.1.2) hc
      rw [Fin.sum_univ_two] at h
      simpa [v] using h
    have hc1 : c 1 = - c 0 := by linear_combination hc_snd
    have hdiff : c 0 * (φ₀ q₁ - φ₀ q₂) = 0 := by
      calc c 0 * (φ₀ q₁ - φ₀ q₂) = c 0 * φ₀ q₁ + (- c 0) * φ₀ q₂ := by ring
        _ = c 0 * φ₀ q₁ + c 1 * φ₀ q₂ := by rw [← hc1]
        _ = 0 := hc_fst
    have hc0 : c 0 = 0 := (mul_eq_zero.mp hdiff).resolve_right (sub_ne_zero.mpr hne)
    intro i
    fin_cases i
    · exact hc0
    · simp [hc1, hc0]
  have h2_le := hlin.fintype_card_le_finrank
  rw [Fintype.card_fin] at h2_le
  omega

private lemma exists_dual_S03 (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    {ζ : K} (hζ : ζ ^ 2 = ζ - 1)
    {L0 L1 : ZMod 6 → ZMod 6 → ((Fin 4 → K) →ₗ[K] K)}
    (hQ3 : finrank K (QMod ζ L0 L1) = 3)
    (hN0 : finrank K (NSub ζ L0 L1 0) = 1)
    (hN3 : finrank K (NSub ζ L0 L1 3) = 1) :
    ∃ (γ : QMod ζ L0 L1 →ₗ[K] K) (C0 C1 C2 C3 : K),
      (∀ q ∈ NSub ζ L0 L1 0, γ q = 0) ∧
      (∀ q ∈ NSub ζ L0 L1 3, γ q = 0) ∧
      (∀ q, L0Q ζ L0 L1 hζ 0 3 q = C0 * γ q) ∧
      (∀ q, L1Q ζ L0 L1 hζ 0 3 q = C1 * γ q) ∧
      (∀ q, L0Q ζ L0 L1 hζ 3 0 q = (- C2) * γ q) ∧
      (∀ q, L1Q ζ L0 L1 hζ 3 0 q = (- C3) * γ q) := by
  have h6 : (6 : K) ≠ 0 := six_ne_zero h2 h3
  let S03 : Submodule K (QMod ζ L0 L1) := NSub ζ L0 L1 0 ⊔ NSub ζ L0 L1 3
  have hS03_dim : finrank K S03 = 2 := by
    have hgrass := Submodule.finrank_sup_add_finrank_inf_eq
      (NSub ζ L0 L1 0) (NSub ζ L0 L1 3)
    have h03 := antipodal_inf_eq_bot h2 h3 hζ (L0 := L0) (L1 := L1) 0
    rw [show (0 + 3 : ZMod 6) = 3 by decide] at h03
    rw [h03, finrank_bot, add_zero, hN0, hN3] at hgrass
    exact hgrass
  have hquot_dim : finrank K (QMod ζ L0 L1 ⧸ S03) = 1 := by
    have := Submodule.finrank_quotient_add_finrank S03
    omega
  let b1 := Module.finBasisOfFinrankEq K (QMod ζ L0 L1 ⧸ S03) hquot_dim
  let coord0 : (QMod ζ L0 L1 ⧸ S03) →ₗ[K] K :=
    { toFun := fun x => b1.equivFun x 0
      map_add' := fun x y => by simp
      map_smul' := fun c x => by simp }
  let γ : QMod ζ L0 L1 →ₗ[K] K := coord0.comp (Submodule.mkQ S03)
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective S03 (b1 0)
  have hγ_y : γ y = 1 := by
    simp [γ, coord0, hy]
  have hker_γ : LinearMap.ker γ = S03 := by
    ext q
    simp only [LinearMap.mem_ker, γ, coord0, LinearMap.comp_apply]
    constructor
    · intro h0
      have hfun0 : b1.equivFun (Submodule.mkQ S03 q) = 0 := by
        ext i; fin_cases i; exact h0
      have hmk0 : Submodule.mkQ S03 q = 0 := b1.equivFun.injective (by simpa using hfun0)
      exact (Submodule.Quotient.mk_eq_zero S03).mp hmk0
    · intro hmem
      have hmk0 : Submodule.mkQ S03 q = 0 := (Submodule.Quotient.mk_eq_zero S03).mpr hmem
      simp [hmk0]
  have hprop_γ : ∀ (φ : QMod ζ L0 L1 →ₗ[K] K),
      (∀ q ∈ NSub ζ L0 L1 0, φ q = 0) →
      (∀ q ∈ NSub ζ L0 L1 3, φ q = 0) →
      ∀ q : QMod ζ L0 L1, φ q = φ y * γ q := by
    intro φ h0 h3_z q
    have hS03_ker : S03 ≤ LinearMap.ker φ :=
      sup_le (fun x hx => h0 x hx) (fun x hx => h3_z x hx)
    have hdiff_ker : q - (γ q) • y ∈ LinearMap.ker γ := by
      simp [LinearMap.mem_ker, map_sub, map_smul, hγ_y]
    have hφ0 : φ (q - (γ q) • y) = 0 := hS03_ker (hker_γ ▸ hdiff_ker)
    simp only [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at hφ0
    rw [mul_comm]
    exact hφ0
  refine ⟨γ, L0Q ζ L0 L1 hζ 0 3 y, L1Q ζ L0 L1 hζ 0 3 y,
    - L0Q ζ L0 L1 hζ 3 0 y, - L1Q ζ L0 L1 hζ 3 0 y, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun q hq => LinearMap.mem_ker.mp (hker_γ.symm ▸ Submodule.mem_sup_left hq)
  · exact fun q hq => LinearMap.mem_ker.mp (hker_γ.symm ▸ Submodule.mem_sup_right hq)
  · refine hprop_γ _ (fun q hq => ?_) (fun q hq => ((forms_zero_of_mem_NSub hζ hq).2.2 0).1)
    obtain ⟨hd0, -, hLq⟩ := forms_zero_of_mem_NSub hζ hq
    have e := elim_color0_Q hζ q 0 0
    rw [(hLq 0).1, hd0, sub_self, zpow_zero, mul_zero, zero_add, mul_one, mul_zero] at e
    exact (mul_eq_zero.mp e).resolve_left h6
  · refine hprop_γ _ (fun q hq => ?_) (fun q hq => ((forms_zero_of_mem_NSub hζ hq).2.2 0).2)
    obtain ⟨-, hd1, hLq⟩ := forms_zero_of_mem_NSub hζ hq
    have e := elim_color1_Q hζ q 0 0
    rw [(hLq 0).2, hd1, sub_self, zpow_zero, mul_zero, zero_add, mul_one, mul_zero] at e
    exact (mul_eq_zero.mp e).resolve_left h6
  · have := hprop_γ (L0Q ζ L0 L1 hζ 3 0)
      (fun q hq => ((forms_zero_of_mem_NSub hζ hq).2.2 3).1) (fun q hq => ?_)
    · intro q; rw [neg_neg]; exact this q
    · obtain ⟨hd0, -, hLq⟩ := forms_zero_of_mem_NSub hζ hq
      have e := elim_color0_Q hζ q 3 3
      rw [show (3 + 3 : ZMod 6) = 0 by decide, (hLq 3).1, hd0, sub_self, zpow_zero,
        mul_zero, zero_add, mul_one, mul_zero] at e
      exact (mul_eq_zero.mp e).resolve_left h6
  · have := hprop_γ (L1Q ζ L0 L1 hζ 3 0)
      (fun q hq => ((forms_zero_of_mem_NSub hζ hq).2.2 3).2) (fun q hq => ?_)
    · intro q; rw [neg_neg]; exact this q
    · obtain ⟨-, hd1, hLq⟩ := forms_zero_of_mem_NSub hζ hq
      have e := elim_color1_Q hζ q 3 3
      rw [show (3 + 3 : ZMod 6) = 0 by decide, (hLq 3).2, hd1, sub_self, zpow_zero,
        mul_zero, zero_add, mul_one, mul_zero] at e
      exact (mul_eq_zero.mp e).resolve_left h6

private lemma four_by_four_null_zero (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    {τ : K} (hτ_ne : τ ≠ 0) {g : Fin 4 → K}
    (eq0 : (-τ) * g 0 + (-3) * g 1 + (-3) * g 2 + τ * g 3 = 0)
    (eq1 : (-τ) * g 0 + 3 * g 1 + 3 * g 2 + τ * g 3 = 0)
    (eq2 : (-3) * g 0 + τ * g 1 + (-τ) * g 2 + (-3) * g 3 = 0)
    (eq3 : (-3) * g 0 + (-τ) * g 1 + τ * g 2 + (-3) * g 3 = 0) :
    ∀ i : Fin 4, g i = 0 := by
  have h6 : (6 : K) ≠ 0 := six_ne_zero h2 h3
  have hg12_add : g 1 + g 2 = 0 :=
    (mul_eq_zero.mp (show (6 : K) * (g 1 + g 2) = 0 by linear_combination eq1 - eq0)).resolve_left h6
  have hg12_sub : g 1 - g 2 = 0 :=
    (mul_eq_zero.mp (show (2 * τ) * (g 1 - g 2) = 0 by linear_combination eq2 - eq3)).resolve_left
      (mul_ne_zero h2 hτ_ne)
  have hg1 : g 1 = 0 :=
    (mul_eq_zero.mp (show (2 : K) * g 1 = 0 by linear_combination hg12_add + hg12_sub)).resolve_left h2
  have hg2 : g 2 = 0 := by linear_combination hg12_add - hg1
  have hg03_sub : g 0 - g 3 = 0 :=
    (mul_eq_zero.mp (show (-τ) * (g 0 - g 3) = 0 by
      linear_combination eq0 + 3 * hg1 + 3 * hg2)).resolve_left (neg_ne_zero.mpr hτ_ne)
  have hg03_add : g 0 + g 3 = 0 :=
    (mul_eq_zero.mp (show (-3 : K) * (g 0 + g 3) = 0 by
      linear_combination eq2 - τ * hg1 + τ * hg2)).resolve_left (neg_ne_zero.mpr h3)
  have hg0 : g 0 = 0 :=
    (mul_eq_zero.mp (show (2 : K) * g 0 = 0 by linear_combination hg03_add + hg03_sub)).resolve_left h2
  have hg3 : g 3 = 0 := by linear_combination hg03_add - hg0
  intro i
  fin_cases i <;> assumption

private lemma not_three_le_finrank_QMod_of_all_two (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    {ζ : K} (hζ : ζ ^ 2 = ζ - 1)
    {L0 L1 : ZMod 6 → ZMod 6 → ((Fin 4 → K) →ₗ[K] K)}
    (hall : ∀ η : ZMod 6, finrank K (KSub ζ L0 L1 η) = 2) :
    ¬ 3 ≤ finrank K (QMod ζ L0 L1) := by
  intro h3_le
  have h6 : (6 : K) ≠ 0 := six_ne_zero h2 h3
  have hnot4 : ¬ 4 ≤ finrank K (QMod ζ L0 L1) :=
    not_four_le_finrank_QMod h2 h3 hζ 0 (fun η _ => hall η)
  have hQ3 : finrank K (QMod ζ L0 L1) = 3 := by omega
  have hN_dim : ∀ a : ZMod 6, finrank K (NSub ζ L0 L1 a) = 1 := by
    intro a
    have hge1 : 1 ≤ finrank K (NSub ζ L0 L1 a) := by
      have := finrank_QMod_le_add_NSub ζ L0 L1 a
      have := hall a; omega
    have hge1_3 : 1 ≤ finrank K (NSub ζ L0 L1 (a + 3)) := by
      have := finrank_QMod_le_add_NSub ζ L0 L1 (a + 3)
      have := hall (a + 3); omega
    by_contra hne1
    have hge2 : 2 ≤ finrank K (NSub ζ L0 L1 a) := by omega
    have hgrass := Submodule.finrank_sup_add_finrank_inf_eq
      (NSub ζ L0 L1 a) (NSub ζ L0 L1 (a + 3))
    rw [antipodal_inf_eq_bot h2 h3 hζ a, finrank_bot, add_zero] at hgrass
    have hsup_le : finrank K ↥(NSub ζ L0 L1 a ⊔ NSub ζ L0 L1 (a + 3)) ≤ 3 :=
      (Submodule.finrank_le _).trans_eq hQ3
    have hsup_eq : finrank K ↥(NSub ζ L0 L1 a ⊔ NSub ζ L0 L1 (a + 3)) =
        finrank K (QMod ζ L0 L1) := by omega
    have htop := Submodule.eq_top_of_finrank_eq hsup_eq
    obtain ⟨hr0_1, hr1_1, -, -⟩ := rho_shift1_ne_zero h2 h3 hζ a
    have hle1 := sup_antipodal_eq_top_imp_le h2 h3 hζ (hall a) htop hr0_1 hr1_1
    have hbot : NSub ζ L0 L1 (a + 1) = ⊥ := by
      rw [← inf_eq_right.mpr hle1]
      exact pairwise_NSub_inf_eq_bot h2 h3 hζ hall (by
        rcases zmod6_cases a with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    have h1_dim : finrank K (NSub ζ L0 L1 (a + 1)) = 0 := by rw [hbot, finrank_bot]
    have hge1_1 : 1 ≤ finrank K (NSub ζ L0 L1 (a + 1)) := by
      have := finrank_QMod_le_add_NSub ζ L0 L1 (a + 1)
      have := hall (a + 1); omega
    omega
  obtain ⟨γ, C0, C1, C2, C3, hN0_γ, hN3_γ, hL0_03, hL1_03, hL0_30, hL1_30⟩ :=
    exists_dual_S03 h2 h3 hζ hQ3 (hN_dim 0) (hN_dim 3)
  -- Normalized generators x_η ∈ NSub η with γ x_η = 1 for η ∈ {1, 2, 4, 5}
  obtain ⟨τ, hτ_def⟩ : ∃ τ : K, τ = 2 * ζ - 1 := ⟨_, rfl⟩
  have hτ_sq : τ ^ 2 = -3 := by rw [hτ_def]; linear_combination 4 * hζ
  have hτ_ne : τ ≠ 0 := by
    intro h0
    have : (-3 : K) = 0 := by rw [← hτ_sq, h0, sq, mul_zero]
    exact neg_ne_zero.mpr h3 this
  let m0 : ZMod 6 → K := fun η =>
    if η = 1 then -τ else if η = 2 then -3 else if η = 4 then -3 else τ
  let m1 : ZMod 6 → K := fun η =>
    if η = 1 then -τ else if η = 2 then 3 else if η = 4 then 3 else τ
  let m2 : ZMod 6 → K := fun η =>
    if η = 1 then -3 else if η = 2 then τ else if η = 4 then -τ else -3
  let m3 : ZMod 6 → K := fun η =>
    if η = 1 then -3 else if η = 2 then -τ else if η = 4 then τ else -3
  have hex_norm : ∀ η : ZMod 6, η ∈ ({1, 2, 4, 5} : Finset (ZMod 6)) →
      ∃ x : QMod ζ L0 L1, x ∈ NSub ζ L0 L1 η ∧ x ≠ 0 ∧ γ x = 1 ∧
        d0Q ζ L0 L1 hζ 0 x = 2 * m0 η * C0 ∧
        d1Q ζ L0 L1 hζ 0 x = 2 * m1 η * C1 ∧
        d0Q ζ L0 L1 hζ 3 x = 2 * m2 η * C2 ∧
        d1Q ζ L0 L1 hζ 3 x = 2 * m3 η * C3 := by
    intro η hη
    have hη_ne0 : (0 : ZMod 6) ≠ η := by
      intro h0; subst h0; revert hη; decide
    have hne_bot : NSub ζ L0 L1 η ≠ ⊥ := by
      intro hb
      have hd := hN_dim η
      rw [hb, finrank_bot] at hd
      omega
    obtain ⟨x', hx'N, hx'0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne_bot
    have hm_id :
        6 * zpow ζ η = rho0_6 ζ 0 η * (2 * m0 η) ∧
        6 * zpow ζ (-η) = rho1_6 ζ 0 η * (2 * m1 η) ∧
        6 * zpow ζ η = rho0_6 ζ 3 η * (2 * m2 η) ∧
        6 * zpow ζ (-η) = rho1_6 ζ 3 η * (2 * m3 η) := by
      rcases zmod6_cases η with rfl | rfl | rfl | rfl | rfl | rfl
      · exfalso; revert hη; decide
      · dsimp only [m0, m1, m2, m3]; rw [hτ_def]
        simp (config := { decide := true }) only [rho0_6, rho1_6, w0, w1, zpow_eval hζ, ↓reduceIte]
        exact ⟨by linear_combination 4 * hζ, by linear_combination 4 * hζ, by ring, by ring⟩
      · dsimp only [m0, m1, m2, m3]; rw [hτ_def]
        simp (config := { decide := true }) only [rho0_6, rho1_6, w0, w1, zpow_eval hζ, ↓reduceIte]
        exact ⟨by ring, by ring, by linear_combination -4 * hζ, by linear_combination -4 * hζ⟩
      · exfalso; revert hη; decide
      · dsimp only [m0, m1, m2, m3]; rw [hτ_def]
        simp (config := { decide := true }) only [rho0_6, rho1_6, w0, w1, zpow_eval hζ, ↓reduceIte]
        exact ⟨by ring, by ring, by linear_combination -4 * hζ, by linear_combination -4 * hζ⟩
      · dsimp only [m0, m1, m2, m3]; rw [hτ_def]
        simp (config := { decide := true }) only [rho0_6, rho1_6, w0, w1, zpow_eval hζ, ↓reduceIte]
        exact ⟨by linear_combination 4 * hζ, by linear_combination 4 * hζ, by ring, by ring⟩
    have hr0_0_ne : rho0_6 ζ 0 η ≠ 0 :=
      left_ne_zero_of_mul (hm_id.1 ▸ mul_ne_zero h6 (zpow_ne_zero hζ η))
    have hr1_0_ne : rho1_6 ζ 0 η ≠ 0 :=
      left_ne_zero_of_mul (hm_id.2.1 ▸ mul_ne_zero h6 (zpow_ne_zero hζ (-η)))
    have hr0_3_ne : rho0_6 ζ 3 η ≠ 0 :=
      left_ne_zero_of_mul (hm_id.2.2.1 ▸ mul_ne_zero h6 (zpow_ne_zero hζ η))
    have hr1_3_ne : rho1_6 ζ 3 η ≠ 0 :=
      left_ne_zero_of_mul (hm_id.2.2.2 ▸ mul_ne_zero h6 (zpow_ne_zero hζ (-η)))
    have heq_vals : ∀ z : QMod ζ L0 L1, z ∈ NSub ζ L0 L1 η →
        d0Q ζ L0 L1 hζ 0 z = 2 * m0 η * C0 * γ z ∧
        d1Q ζ L0 L1 hζ 0 z = 2 * m1 η * C1 * γ z ∧
        d0Q ζ L0 L1 hζ 3 z = 2 * m2 η * C2 * γ z ∧
        d1Q ζ L0 L1 hζ 3 z = 2 * m3 η * C3 * γ z := by
      intro z hzN
      obtain ⟨-, -, hLz⟩ := forms_zero_of_mem_NSub hζ hzN
      have e00 := elim_color0_Q hζ z 0 η
      rw [(hLz 0).1, show (0 + 3 : ZMod 6) = 3 by decide, sub_zero, hL0_03 z,
        mul_zero, zero_add, ← mul_assoc, hm_id.1] at e00
      have e10 := elim_color1_Q hζ z 0 η
      rw [(hLz 0).2, show (0 + 3 : ZMod 6) = 3 by decide, zero_sub, hL1_03 z,
        mul_zero, zero_add, ← mul_assoc, hm_id.2.1] at e10
      have e03 := elim_color0_Q hζ z 3 η
      rw [(hLz 3).1, show (3 + 3 : ZMod 6) = 0 by decide, zpow_sub_three hζ, hL0_30 z,
        mul_zero, zero_add] at e03
      have e03' : rho0_6 ζ 3 η * (2 * m2 η * C2 * γ z) = rho0_6 ζ 3 η * d0Q ζ L0 L1 hζ 3 z := by
        calc rho0_6 ζ 3 η * (2 * m2 η * C2 * γ z)
            = (rho0_6 ζ 3 η * (2 * m2 η)) * (C2 * γ z) := by ring
          _ = (6 * zpow ζ η) * (C2 * γ z) := by rw [← hm_id.2.2.1]
          _ = 6 * (- zpow ζ η) * ((- C2) * γ z) := by ring
          _ = rho0_6 ζ 3 η * d0Q ζ L0 L1 hζ 3 z := e03
      have e13 := elim_color1_Q hζ z 3 η
      have h3_sub : (3 - η : ZMod 6) = (-η) - 3 := by
        rcases zmod6_cases η with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      rw [(hLz 3).2, show (3 + 3 : ZMod 6) = 0 by decide, h3_sub, zpow_sub_three hζ, hL1_30 z,
        mul_zero, zero_add] at e13
      have e13' : rho1_6 ζ 3 η * (2 * m3 η * C3 * γ z) = rho1_6 ζ 3 η * d1Q ζ L0 L1 hζ 3 z := by
        calc rho1_6 ζ 3 η * (2 * m3 η * C3 * γ z)
            = (rho1_6 ζ 3 η * (2 * m3 η)) * (C3 * γ z) := by ring
          _ = (6 * zpow ζ (-η)) * (C3 * γ z) := by rw [← hm_id.2.2.2]
          _ = 6 * (- zpow ζ (-η)) * ((- C3) * γ z) := by ring
          _ = rho1_6 ζ 3 η * d1Q ζ L0 L1 hζ 3 z := e13
      exact ⟨mul_left_cancel₀ hr0_0_ne (by linear_combination -e00),
        mul_left_cancel₀ hr1_0_ne (by linear_combination -e10),
        mul_left_cancel₀ hr0_3_ne e03'.symm,
        mul_left_cancel₀ hr1_3_ne e13'.symm⟩
    have hγ_ne : γ x' ≠ 0 := by
      intro hγ0
      obtain ⟨ed0, ed1, -, -⟩ := heq_vals x' hx'N
      rw [hγ0, mul_zero] at ed0 ed1
      have hx'0N : x' ∈ NSub ζ L0 L1 0 :=
        (mem_NSub_iff_of_finrank_eq_two hζ (hall 0) x').mpr ⟨ed0, ed1⟩
      have hbot := pairwise_NSub_inf_eq_bot h2 h3 hζ hall hη_ne0
      have hmem : x' ∈ (⊥ : Submodule K (QMod ζ L0 L1)) :=
        hbot ▸ show x' ∈ NSub ζ L0 L1 0 ⊓ NSub ζ L0 L1 η from ⟨hx'0N, hx'N⟩
      exact hx'0 ((Submodule.mem_bot K).mp hmem)
    let x := (γ x')⁻¹ • x'
    have hxN : x ∈ NSub ζ L0 L1 η := Submodule.smul_mem _ _ hx'N
    have hγx : γ x = 1 := by simp [x, inv_mul_cancel₀ hγ_ne]
    have hx_ne0 : x ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hγx
      exact zero_ne_one hγx
    obtain ⟨ed0, ed1, ed2, ed3⟩ := heq_vals x hxN
    rw [hγx, mul_one] at ed0 ed1 ed2 ed3
    exact ⟨x, hxN, hx_ne0, hγx, ed0, ed1, ed2, ed3⟩
  obtain ⟨x1, hx1N, hx1_0, hγ1, d0_1, d1_1, d2_1, d3_1⟩ := hex_norm 1 (by decide)
  obtain ⟨x2, _, _, hγ2, d0_2, d1_2, d2_2, d3_2⟩ := hex_norm 2 (by decide)
  obtain ⟨x4, _, _, _, d0_4, d1_4, d2_4, d3_4⟩ := hex_norm 4 (by decide)
  obtain ⟨x5, _, _, _, d0_5, d1_5, d2_5, d3_5⟩ := hex_norm 5 (by decide)
  have hnot_C01 : ¬ (C0 = 0 ∧ C1 = 0) := by
    rintro ⟨hC0, hC1⟩
    rw [hC0, mul_zero] at d0_1
    rw [hC1, mul_zero] at d1_1
    have hx1_N0 : x1 ∈ NSub ζ L0 L1 0 :=
      (mem_NSub_iff_of_finrank_eq_two hζ (hall 0) x1).mpr ⟨d0_1, d1_1⟩
    have hbot := pairwise_NSub_inf_eq_bot h2 h3 hζ hall (show (0 : ZMod 6) ≠ 1 by decide)
    have hmem : x1 ∈ (⊥ : Submodule K (QMod ζ L0 L1)) :=
      hbot ▸ show x1 ∈ NSub ζ L0 L1 0 ⊓ NSub ζ L0 L1 1 from ⟨hx1_N0, hx1N⟩
    exact hx1_0 ((Submodule.mem_bot K).mp hmem)
  have hnot_C23 : ¬ (C2 = 0 ∧ C3 = 0) := by
    rintro ⟨hC2, hC3⟩
    rw [hC2, mul_zero] at d2_1
    rw [hC3, mul_zero] at d3_1
    have hx1_N3 : x1 ∈ NSub ζ L0 L1 3 :=
      (mem_NSub_iff_of_finrank_eq_two hζ (hall 3) x1).mpr ⟨d2_1, d3_1⟩
    have hbot := pairwise_NSub_inf_eq_bot h2 h3 hζ hall (show (3 : ZMod 6) ≠ 1 by decide)
    have hmem : x1 ∈ (⊥ : Submodule K (QMod ζ L0 L1)) :=
      hbot ▸ show x1 ∈ NSub ζ L0 L1 3 ⊓ NSub ζ L0 L1 1 from ⟨hx1_N3, hx1N⟩
    exact hx1_0 ((Submodule.mem_bot K).mp hmem)
  have h3_sub_τ_ne : (3 - τ : K) ≠ 0 := by
    have hp : (3 - τ) * (3 + τ) = 12 := by
      calc (3 - τ) * (3 + τ) = 9 - τ ^ 2 := by ring
        _ = 12 := by rw [hτ_sq]; norm_num
    have h12 : (12 : K) ≠ 0 := by
      have : (12 : K) = 2 * (2 * 3) := by norm_num
      exact this ▸ mul_ne_zero h2 (mul_ne_zero h2 h3)
    exact left_ne_zero_of_mul (hp.symm ▸ h12)
  have h3_add_τ_ne : (3 + τ : K) ≠ 0 := by
    have hp : (3 - τ) * (3 + τ) = 12 := by
      calc (3 - τ) * (3 + τ) = 9 - τ ^ 2 := by ring
        _ = 12 := by rw [hτ_sq]; norm_num
    have h12 : (12 : K) ≠ 0 := by
      have : (12 : K) = 2 * (2 * 3) := by norm_num
      exact this ▸ mul_ne_zero h2 (mul_ne_zero h2 h3)
    exact right_ne_zero_of_mul (hp.symm ▸ h12)
  have hC1_ne : C1 ≠ 0 := by
    intro hC1
    have hq1 : d1Q ζ L0 L1 hζ 0 x1 = 0 := by rw [d1_1, hC1, mul_zero]
    have hq2 : d1Q ζ L0 L1 hζ 0 x2 = 0 := by rw [d1_2, hC1, mul_zero]
    have heq := eq_on_ker_of_finrank_ker_pair_one
      (mem_NSub_iff_of_finrank_eq_two hζ (hall 0)) (hN_dim 0) hN0_γ hq1 hq2 hγ1 hγ2
    rw [d0_1, d0_2] at heq
    dsimp only [m0] at heq
    simp (config := { decide := true }) only [↓reduceIte] at heq
    have hdiff : 2 * (3 - τ) * C0 = 0 := by linear_combination heq
    have hC0 : C0 = 0 := (mul_eq_zero.mp hdiff).resolve_left (mul_ne_zero h2 h3_sub_τ_ne)
    exact hnot_C01 ⟨hC0, hC1⟩
  have hC0_ne : C0 ≠ 0 := by
    intro hC0
    have hq1 : d0Q ζ L0 L1 hζ 0 x1 = 0 := by rw [d0_1, hC0, mul_zero]
    have hq2 : d0Q ζ L0 L1 hζ 0 x2 = 0 := by rw [d0_2, hC0, mul_zero]
    have hiff' : ∀ q, q ∈ NSub ζ L0 L1 0 ↔ d1Q ζ L0 L1 hζ 0 q = 0 ∧ d0Q ζ L0 L1 hζ 0 q = 0 :=
      fun q => (mem_NSub_iff_of_finrank_eq_two hζ (hall 0) q).trans and_comm
    have heq := eq_on_ker_of_finrank_ker_pair_one hiff' (hN_dim 0) hN0_γ hq1 hq2 hγ1 hγ2
    rw [d1_1, d1_2] at heq
    dsimp only [m1] at heq
    simp (config := { decide := true }) only [↓reduceIte] at heq
    have hdiff : 2 * (3 + τ) * C1 = 0 := by linear_combination -heq
    exact hC1_ne ((mul_eq_zero.mp hdiff).resolve_left (mul_ne_zero h2 h3_add_τ_ne))
  have hC3_ne : C3 ≠ 0 := by
    intro hC3
    have hq1 : d1Q ζ L0 L1 hζ 3 x1 = 0 := by rw [d3_1, hC3, mul_zero]
    have hq2 : d1Q ζ L0 L1 hζ 3 x2 = 0 := by rw [d3_2, hC3, mul_zero]
    have heq := eq_on_ker_of_finrank_ker_pair_one
      (mem_NSub_iff_of_finrank_eq_two hζ (hall 3)) (hN_dim 3) hN3_γ hq1 hq2 hγ1 hγ2
    rw [d2_1, d2_2] at heq
    dsimp only [m2] at heq
    simp (config := { decide := true }) only [↓reduceIte] at heq
    have hdiff : 2 * (3 + τ) * C2 = 0 := by linear_combination -heq
    have hC2 : C2 = 0 := (mul_eq_zero.mp hdiff).resolve_left (mul_ne_zero h2 h3_add_τ_ne)
    exact hnot_C23 ⟨hC2, hC3⟩
  have hC2_ne : C2 ≠ 0 := by
    intro hC2
    have hq1 : d0Q ζ L0 L1 hζ 3 x1 = 0 := by rw [d2_1, hC2, mul_zero]
    have hq2 : d0Q ζ L0 L1 hζ 3 x2 = 0 := by rw [d2_2, hC2, mul_zero]
    have hiff' : ∀ q, q ∈ NSub ζ L0 L1 3 ↔ d1Q ζ L0 L1 hζ 3 q = 0 ∧ d0Q ζ L0 L1 hζ 3 q = 0 :=
      fun q => (mem_NSub_iff_of_finrank_eq_two hζ (hall 3) q).trans and_comm
    have heq := eq_on_ker_of_finrank_ker_pair_one hiff' (hN_dim 3) hN3_γ hq1 hq2 hγ1 hγ2
    rw [d3_1, d3_2] at heq
    dsimp only [m3] at heq
    simp (config := { decide := true }) only [↓reduceIte] at heq
    have hdiff : 2 * (3 - τ) * C3 = 0 := by linear_combination -heq
    exact hC3_ne ((mul_eq_zero.mp hdiff).resolve_left (mul_ne_zero h2 h3_sub_τ_ne))
  -- Four vectors in 3-dimensional QMod must satisfy a nontrivial linear relation
  let vec : Fin 4 → QMod ζ L0 L1 := ![x1, x2, x4, x5]
  have hnot_lin : ¬ LinearIndependent K vec := by
    intro hlin
    have hle := hlin.fintype_card_le_finrank
    rw [Fintype.card_fin, hQ3] at hle
    omega
  obtain ⟨g, hg_sum, i₀, hgi0⟩ := Fintype.not_linearIndependent_iff.mp hnot_lin
  rw [Fin.sum_univ_four] at hg_sum
  dsimp [vec] at hg_sum
  have apply_form : ∀ (φ : QMod ζ L0 L1 →ₗ[K] K),
      g 0 * φ x1 + g 1 * φ x2 + g 2 * φ x4 + g 3 * φ x5 = 0 := by
    intro φ
    have hφ := congrArg φ hg_sum
    simpa [map_add, map_smul, smul_eq_mul] using hφ
  have r0 := apply_form (d0Q ζ L0 L1 hζ 0)
  have r1 := apply_form (d1Q ζ L0 L1 hζ 0)
  have r2 := apply_form (d0Q ζ L0 L1 hζ 3)
  have r3 := apply_form (d1Q ζ L0 L1 hζ 3)
  rw [d0_1, d0_2, d0_4, d0_5] at r0
  rw [d1_1, d1_2, d1_4, d1_5] at r1
  rw [d2_1, d2_2, d2_4, d2_5] at r2
  rw [d3_1, d3_2, d3_4, d3_5] at r3
  dsimp only [m0] at r0
  dsimp only [m1] at r1
  dsimp only [m2] at r2
  dsimp only [m3] at r3
  simp (config := { decide := true }) only [↓reduceIte] at r0 r1 r2 r3
  have eq0 : (-τ) * g 0 + (-3) * g 1 + (-3) * g 2 + τ * g 3 = 0 :=
    (mul_eq_zero.mp (show (2 * C0) * ((-τ) * g 0 + (-3) * g 1 + (-3) * g 2 + τ * g 3) = 0 by
      linear_combination r0)).resolve_left (mul_ne_zero h2 hC0_ne)
  have eq1 : (-τ) * g 0 + 3 * g 1 + 3 * g 2 + τ * g 3 = 0 :=
    (mul_eq_zero.mp (show (2 * C1) * ((-τ) * g 0 + 3 * g 1 + 3 * g 2 + τ * g 3) = 0 by
      linear_combination r1)).resolve_left (mul_ne_zero h2 hC1_ne)
  have eq2 : (-3) * g 0 + τ * g 1 + (-τ) * g 2 + (-3) * g 3 = 0 :=
    (mul_eq_zero.mp (show (2 * C2) * ((-3) * g 0 + τ * g 1 + (-τ) * g 2 + (-3) * g 3) = 0 by
      linear_combination r2)).resolve_left (mul_ne_zero h2 hC2_ne)
  have eq3 : (-3) * g 0 + (-τ) * g 1 + τ * g 2 + (-3) * g 3 = 0 :=
    (mul_eq_zero.mp (show (2 * C3) * ((-3) * g 0 + (-τ) * g 1 + τ * g 2 + (-3) * g 3) = 0 by
      linear_combination r3)).resolve_left (mul_ne_zero h2 hC3_ne)
  exact hgi0 (four_by_four_null_zero h2 h3 hτ_ne eq0 eq1 eq2 eq3 i₀)

/-- Master dimension bound `≤ 14` on `FourierCodeSpace ζ L0 L1` over any field `K` with
`(2 : K) ≠ 0`, `(3 : K) ≠ 0`, and `ζ ^ 2 = ζ - 1`. -/
private theorem finrank_fourierCodeSpace_le_14 (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    {ζ : K} (hζ : ζ ^ 2 = ζ - 1)
    (L0 L1 : ZMod 6 → ZMod 6 → ((Fin 4 → K) →ₗ[K] K)) :
    finrank K (FourierCodeSpace ζ L0 L1) ≤ 14 := by
  have htot := Submodule.finrank_quotient_add_finrank (KSumSub ζ L0 L1)
  rw [finrank_KSumSub] at htot
  let k : ZMod 6 → ℕ := fun η => finrank K (KSub ζ L0 L1 η)
  have hk_le : ∀ η : ZMod 6, k η ≤ 2 := fun η => finrank_KSub_le_two hζ L0 L1 η
  let SK : ℕ := ∑ η : ZMod 6, k η
  have hSK_sum : SK = k 0 + k 1 + k 2 + k 3 + k 4 + k 5 := sum_zmod6 k
  have h0 := hk_le 0; have h1 := hk_le 1; have h2' := hk_le 2
  have h3' := hk_le 3; have h4 := hk_le 4; have h5 := hk_le 5
  have ha0 := finrank_QMod_le_antipodal h2 h3 hζ (L0 := L0) (L1 := L1) 0
  have ha1 := finrank_QMod_le_antipodal h2 h3 hζ (L0 := L0) (L1 := L1) 1
  have ha2 := finrank_QMod_le_antipodal h2 h3 hζ (L0 := L0) (L1 := L1) 2
  rw [show (0 + 3 : ZMod 6) = 3 by decide] at ha0
  rw [show (1 + 3 : ZMod 6) = 4 by decide] at ha1
  rw [show (2 + 3 : ZMod 6) = 5 by decide] at ha2
  change finrank K (QMod ζ L0 L1) + SK = finrank K (FourierCodeSpace ζ L0 L1) at htot
  change finrank K (QMod ζ L0 L1) ≤ (4 - k 0) + (4 - k 3) at ha0
  change finrank K (QMod ζ L0 L1) ≤ (4 - k 1) + (4 - k 4) at ha1
  change finrank K (QMod ζ L0 L1) ≤ (4 - k 2) + (4 - k 5) at ha2
  by_cases hSK10 : SK ≤ 10
  · omega
  · by_cases hSK11 : SK = 11
    · have hex_one : ∃ η₀ : ZMod 6, ∀ η : ZMod 6, η ≠ η₀ → k η = 2 := by
        by_cases hc0 : k 0 < 2
        · refine ⟨0, fun η hη => ?_⟩
          rcases zmod6_cases η with rfl | rfl | rfl | rfl | rfl | rfl <;>
            first | exact absurd rfl hη | omega
        · by_cases hc1 : k 1 < 2
          · refine ⟨1, fun η hη => ?_⟩
            rcases zmod6_cases η with rfl | rfl | rfl | rfl | rfl | rfl <;>
              first | exact absurd rfl hη | omega
          · by_cases hc2 : k 2 < 2
            · refine ⟨2, fun η hη => ?_⟩
              rcases zmod6_cases η with rfl | rfl | rfl | rfl | rfl | rfl <;>
                first | exact absurd rfl hη | omega
            · by_cases hc3 : k 3 < 2
              · refine ⟨3, fun η hη => ?_⟩
                rcases zmod6_cases η with rfl | rfl | rfl | rfl | rfl | rfl <;>
                  first | exact absurd rfl hη | omega
              · by_cases hc4 : k 4 < 2
                · refine ⟨4, fun η hη => ?_⟩
                  rcases zmod6_cases η with rfl | rfl | rfl | rfl | rfl | rfl <;>
                    first | exact absurd rfl hη | omega
                · refine ⟨5, fun η hη => ?_⟩
                  rcases zmod6_cases η with rfl | rfl | rfl | rfl | rfl | rfl <;>
                    first | exact absurd rfl hη | omega
      obtain ⟨η₀, h5_eq⟩ := hex_one
      have hQ_lt4 : ¬ 4 ≤ finrank K (QMod ζ L0 L1) :=
        not_four_le_finrank_QMod h2 h3 hζ η₀ h5_eq
      omega
    · have hSK12 : SK = 12 := by omega
      have hall2 : ∀ η : ZMod 6, k η = 2 := by
        intro η
        rcases zmod6_cases η with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      have hQ_lt3 : ¬ 3 ≤ finrank K (QMod ζ L0 L1) :=
        not_three_le_finrank_QMod_of_all_two h2 h3 hζ hall2
      omega

end QuotientAnalysis

/-! ### Section 4: Fourier Bridge on `Matrix (ZMod 6) (ZMod 6) K` and Field Transfer -/

section FourierBridge

/-- 6-point column Fourier analysis `r ↦ (η ↦ 6⁻¹ ∑_j ζ^(-η j) r j)`. -/
private def fCoeff (ζ : K) : (ZMod 6 → K) →ₗ[K] (ZMod 6 → K) where
  toFun r η := (6 : K)⁻¹ * ∑ j : ZMod 6, zpow ζ (- (η * j)) * r j
  map_add' r₁ r₂ := by
    funext η
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c r := by
    funext η
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring

private lemma synth_fCoeff (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    {ζ : K} (hζ : ζ ^ 2 = ζ - 1) (r : ZMod 6 → K) (j : ZMod 6) :
    ∑ η : ZMod 6, zpow ζ (η * j) * fCoeff ζ r η = r j := by
  have h6 : (6 : K) ≠ 0 := six_ne_zero h2 h3
  have hinner : ∀ k : ZMod 6,
      (∑ η : ZMod 6, zpow ζ (η * j) * (zpow ζ (- (η * k)) * r k)) =
        (if k = j then (6 : K) else 0) * r k := by
    intro k
    have hterm : ∀ η : ZMod 6,
        zpow ζ (η * j) * (zpow ζ (- (η * k)) * r k) = zpow ζ (η * (j - k)) * r k := by
      intro η
      rw [← mul_assoc, ← zpow_add hζ, show η * j + (- (η * k)) = η * (j - k) by ring]
    simp_rw [hterm, ← Finset.sum_mul, sum_zpow hζ (j - k)]
    by_cases hkj : k = j
    · subst hkj; simp
    · have hjk : j - k ≠ 0 := sub_ne_zero.mpr (Ne.symm hkj)
      simp [hkj, hjk]
  calc ∑ η : ZMod 6, zpow ζ (η * j) * fCoeff ζ r η
      = ∑ η : ZMod 6, ∑ k : ZMod 6,
          (6 : K)⁻¹ * (zpow ζ (η * j) * (zpow ζ (- (η * k)) * r k)) := by
        refine Finset.sum_congr rfl fun η _ => ?_
        dsimp [fCoeff]
        rw [← mul_assoc, mul_comm (zpow ζ _) (6 : K)⁻¹, mul_assoc, Finset.mul_sum, Finset.mul_sum]
    _ = ∑ k : ZMod 6, (6 : K)⁻¹ *
          ∑ η : ZMod 6, zpow ζ (η * j) * (zpow ζ (- (η * k)) * r k) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => (Finset.mul_sum _ _ _).symm
    _ = ∑ k : ZMod 6, if k = j then r k else 0 := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hinner]
        by_cases hkj : k = j
        · simp [hkj, inv_mul_cancel_left₀ h6]
        · simp [hkj]
    _ = r j := by
        rw [Finset.sum_ite_eq' Finset.univ j]
        simp

private lemma fCoeff_shift {ζ : K} (hζ : ζ ^ 2 = ζ - 1)
    (r : ZMod 6 → K) (s η : ZMod 6) :
    fCoeff ζ (fun j => r (j + s)) η = zpow ζ (s * η) * fCoeff ζ r η := by
  dsimp [fCoeff]
  have hsum : ∑ j : ZMod 6, zpow ζ (- (η * j)) * r (j + s) =
      ∑ k : ZMod 6, zpow ζ (s * η) * (zpow ζ (- (η * k)) * r k) := by
    refine Fintype.sum_equiv (Equiv.addRight s) _ _ fun j => ?_
    simp only [Equiv.coe_addRight]
    rw [← mul_assoc, ← zpow_add hζ, show s * η + (- (η * (j + s))) = - (η * j) by ring]
  rw [hsum, ← Finset.mul_sum]
  ring

/-- Maximal class-uniform subspace cut out over `K` by a pair of `K`-linear decoders `decK`. -/
private def codeOfDec (decK : Bool → (Matrix (ZMod 6) (ZMod 6) K →ₗ[K] (ZMod 6 → K))) :
    Submodule K (Matrix (ZMod 6) (ZMod 6) K) where
  carrier := {X | ∀ c : ZMod 6, X c = decK (SwapRigidity.aperiodicCls c) (SwapRigidity.rot c X)}
  zero_mem' c := by
    funext j
    have h0 : SwapRigidity.rot c (0 : Matrix (ZMod 6) (ZMod 6) K) = 0 := map_zero _
    rw [h0, map_zero]
    rfl
  add_mem' {X Y} hX hY c := by
    funext j
    have hXc := congrFun (hX c) j
    have hYc := congrFun (hY c) j
    simp only [Matrix.add_apply, map_add, Pi.add_apply] at hXc hYc ⊢
    exact congrArg₂ (· + ·) hXc hYc
  smul_mem' a {X} hX c := by
    funext j
    have hXc := congrFun (hX c) j
    simp only [Matrix.smul_apply, map_smul, Pi.smul_apply] at hXc ⊢
    exact congrArg (a • ·) hXc

/-- Single-shift intersection `W_K = codeOfDec decK ⊓ (codeOfDec decK).comap (rot 1)`. -/
private def WKSub (decK : Bool → (Matrix (ZMod 6) (ZMod 6) K →ₗ[K] (ZMod 6 → K))) :
    Submodule K (Matrix (ZMod 6) (ZMod 6) K) :=
  codeOfDec decK ⊓ (codeOfDec decK).comap (SwapRigidity.rot 1)

/-- Synthesis map from 4-run Fourier coordinates `ZMod 6 → Fin 4 → K` into `6 × 6` matrices. -/
private def synthMat (ζ : K) : (ZMod 6 → Fin 4 → K) →ₗ[K] Matrix (ZMod 6) (ZMod 6) K where
  toFun v := Matrix.of fun i j =>
    if i = 0 then ∑ μ : ZMod 6, zpow ζ (μ * j) * v μ 0
    else if i = 1 then ∑ μ : ZMod 6, zpow ζ (μ * (j + 1)) * v μ 0
    else if i = 2 then ∑ μ : ZMod 6, zpow ζ (μ * j) * v μ 1
    else if i = 3 then ∑ μ : ZMod 6, zpow ζ (μ * j) * v μ 2
    else if i = 4 then ∑ μ : ZMod 6, zpow ζ (μ * j) * v μ 3
    else ∑ μ : ZMod 6, zpow ζ (μ * (j + 1)) * v μ 3
  map_add' v₁ v₂ := by
    ext i j
    rcases zmod6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := { decide := true }) only [Matrix.of_apply, Matrix.add_apply, ↓reduceIte,
        Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a v := by
    ext i j
    have hfac : ∀ (f g : ZMod 6 → K),
        (∑ μ : ZMod 6, f μ * (a * g μ)) = a * ∑ μ : ZMod 6, f μ * g μ := by
      intro f g; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun μ _ => by ring
    rcases zmod6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := { decide := true }) only [Matrix.of_apply, Matrix.smul_apply, ↓reduceIte,
        Pi.smul_apply, smul_eq_mul, RingHom.id_apply, hfac]

/-- Run-head Fourier analysis reading rows `0, 2, 3, 4` of a `6 × 6` matrix. -/
private def analyzeMat (ζ : K) : Matrix (ZMod 6) (ZMod 6) K →ₗ[K] (ZMod 6 → Fin 4 → K) where
  toFun X μ := ![fCoeff ζ (X 0) μ, fCoeff ζ (X 2) μ, fCoeff ζ (X 3) μ, fCoeff ζ (X 4) μ]
  map_add' X Y := by
    funext μ k
    have hrow : ∀ i : ZMod 6, (X + Y) i = X i + Y i := fun i => by ext j; rfl
    fin_cases k <;> simp [hrow, map_add]
  map_smul' a X := by
    funext μ k
    have hrow : ∀ i : ZMod 6, (a • X) i = a • (X i) := fun i => by ext j; rfl
    fin_cases k <;> simp [hrow, map_smul]

private lemma row1_and_row5_of_mem_WKSub
    {decK : Bool → (Matrix (ZMod 6) (ZMod 6) K →ₗ[K] (ZMod 6 → K))}
    {X : Matrix (ZMod 6) (ZMod 6) K} (hX : X ∈ WKSub decK) :
    (∀ j : ZMod 6, X 1 j = X 0 (j + 1)) ∧ (∀ j : ZMod 6, X 5 j = X 4 (j + 1)) := by
  obtain ⟨hX0, hX1⟩ := hX
  have heq1 : X 1 = (SwapRigidity.rot 1 X) 0 := by
    have e1 := hX0 1
    have e0 := hX1 0
    rw [SwapRigidity.rot_rot, show (0 + 1 : ZMod 6) = 1 by decide] at e0
    have hcls : SwapRigidity.aperiodicCls 1 = SwapRigidity.aperiodicCls 0 := by decide
    exact e1.trans (hcls ▸ e0.symm)
  have heq5 : X 5 = (SwapRigidity.rot 1 X) 4 := by
    have e5 := hX0 5
    have e4 := hX1 4
    rw [SwapRigidity.rot_rot, show (4 + 1 : ZMod 6) = 5 by decide] at e4
    have hcls : SwapRigidity.aperiodicCls 5 = SwapRigidity.aperiodicCls 4 := by decide
    exact e5.trans (hcls ▸ e4.symm)
  exact ⟨fun j => congrFun heq1 j, fun j => congrFun heq5 j⟩

private lemma synthMat_analyzeMat_eq (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    {ζ : K} (hζ : ζ ^ 2 = ζ - 1)
    {decK : Bool → (Matrix (ZMod 6) (ZMod 6) K →ₗ[K] (ZMod 6 → K))}
    {X : Matrix (ZMod 6) (ZMod 6) K} (hX : X ∈ WKSub decK) :
    synthMat ζ (analyzeMat ζ X) = X := by
  obtain ⟨hrow1, hrow5⟩ := row1_and_row5_of_mem_WKSub hX
  ext i j
  rcases zmod6_cases i with rfl | rfl | rfl | rfl | rfl | rfl
  · exact synth_fCoeff h2 h3 hζ (X 0) j
  · simp (config := { decide := true }) only [synthMat, analyzeMat, LinearMap.coe_mk,
      AddHom.coe_mk, Matrix.of_apply, ↓reduceIte, Matrix.cons_val_zero]
    exact (synth_fCoeff h2 h3 hζ (X 0) (j + 1)).trans (hrow1 j).symm
  · simp (config := { decide := true }) only [synthMat, analyzeMat, LinearMap.coe_mk,
      AddHom.coe_mk, Matrix.of_apply, ↓reduceIte, Matrix.cons_val_one, Matrix.cons_val_zero]
    exact synth_fCoeff h2 h3 hζ (X 2) j
  · simp (config := { decide := true }) only [synthMat, analyzeMat, LinearMap.coe_mk,
      AddHom.coe_mk, Matrix.of_apply, ↓reduceIte, Matrix.cons_val_zero]
    exact synth_fCoeff h2 h3 hζ (X 3) j
  · simp (config := { decide := true }) only [synthMat, analyzeMat, LinearMap.coe_mk,
      AddHom.coe_mk, Matrix.of_apply, ↓reduceIte, Matrix.cons_val_zero]
    exact synth_fCoeff h2 h3 hζ (X 4) j
  · simp (config := { decide := true }) only [synthMat, analyzeMat, LinearMap.coe_mk,
      AddHom.coe_mk, Matrix.of_apply, ↓reduceIte, Matrix.cons_val_zero]
    exact (synth_fCoeff h2 h3 hζ (X 4) (j + 1)).trans (hrow5 j).symm

private lemma rot_synthMat_singleMode {ζ : K} (hζ : ζ ^ 2 = ζ - 1)
    (c μ : ZMod 6) (u : Fin 4 → K) :
    SwapRigidity.rot c (synthMat ζ (singleMode K μ u)) =
      zpow ζ (c * μ) • synthMat ζ (singleMode K μ u) := by
  have hsingle : ∀ (a : ZMod 6) (k : Fin 4),
      (∑ η : ZMod 6, zpow ζ (η * a) * singleMode K μ u η k) = zpow ζ (μ * a) * u k := by
    intro a k
    rw [Fintype.sum_eq_single μ]
    · simp [singleMode]
    · intro η hη; simp [singleMode, Pi.single_eq_of_ne hη]
  ext i j
  rcases zmod6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;> (
    simp (config := { decide := true }) only [SwapRigidity.rot_apply, Matrix.smul_apply,
      synthMat, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply, ↓reduceIte, smul_eq_mul, hsingle]
    first
    | (rw [show μ * (j + c) = c * μ + μ * j by ring, zpow_add hζ]; ring)
    | (rw [show μ * (j + c + 1) = c * μ + μ * (j + 1) by ring, zpow_add hζ]; ring))

private lemma sum_singleMode_eq (v : ZMod 6 → Fin 4 → K) :
    ∑ μ : ZMod 6, singleMode K μ (v μ) = v := by
  funext η
  simp [singleMode, Pi.single_apply]

private def ellForm (ζ : K) (decK : Bool → (Matrix (ZMod 6) (ZMod 6) K →ₗ[K] (ZMod 6 → K)))
    (b : Bool) (ξ μ : ZMod 6) : (Fin 4 → K) →ₗ[K] K :=
  ((LinearMap.proj ξ).comp (fCoeff ζ)).comp ((decK b).comp ((synthMat ζ).comp (singleMode K μ)))

private lemma fCoeff_decK_rot_synthMat {ζ : K} (hζ : ζ ^ 2 = ζ - 1)
    (decK : Bool → (Matrix (ZMod 6) (ZMod 6) K →ₗ[K] (ZMod 6 → K)))
    (v : ZMod 6 → Fin 4 → K) (b : Bool) (c ξ : ZMod 6) :
    fCoeff ζ (decK b (SwapRigidity.rot c (synthMat ζ v))) ξ =
      ∑ μ : ZMod 6, zpow ζ (c * μ) * ellForm ζ decK b ξ μ (v μ) := by
  conv_lhs => rw [← sum_singleMode_eq v, map_sum, map_sum]
  simp_rw [rot_synthMat_singleMode hζ]
  rw [map_sum, map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [map_smul, map_smul, Pi.smul_apply, smul_eq_mul]
  rfl

private def decL0 (ζ : K) (decK : Bool → (Matrix (ZMod 6) (ZMod 6) K →ₗ[K] (ZMod 6 → K)))
    (ξ μ : ZMod 6) : (Fin 4 → K) →ₗ[K] K :=
  ellForm ζ decK true ξ μ - if μ = ξ then LinearMap.proj (0 : Fin 4) else 0

private def decL1 (ζ : K) (decK : Bool → (Matrix (ZMod 6) (ZMod 6) K →ₗ[K] (ZMod 6 → K)))
    (ξ μ : ZMod 6) : (Fin 4 → K) →ₗ[K] K :=
  ellForm ζ decK false ξ μ -
    if μ = ξ then zpow ζ (- (2 * ξ)) • LinearMap.proj (1 : Fin 4) else 0

private lemma sum_decL0 {ζ : K} (hζ : ζ ^ 2 = ζ - 1)
    (decK : Bool → (Matrix (ZMod 6) (ZMod 6) K →ₗ[K] (ZMod 6 → K)))
    (v : ZMod 6 → Fin 4 → K) (c ξ : ZMod 6) :
    ∑ μ : ZMod 6, zpow ζ (c * μ) * decL0 ζ decK ξ μ (v μ) =
      fCoeff ζ (decK true (SwapRigidity.rot c (synthMat ζ v))) ξ -
        zpow ζ (c * ξ) * v ξ 0 := by
  simp only [decL0, LinearMap.sub_apply, mul_sub, Finset.sum_sub_distrib,
    ← fCoeff_decK_rot_synthMat hζ]
  congr 1
  rw [Fintype.sum_eq_single ξ]
  · simp
  · intro μ hμ; simp [hμ]

private lemma sum_decL1 {ζ : K} (hζ : ζ ^ 2 = ζ - 1)
    (decK : Bool → (Matrix (ZMod 6) (ZMod 6) K →ₗ[K] (ZMod 6 → K)))
    (v : ZMod 6 → Fin 4 → K) (c ξ : ZMod 6) :
    ∑ μ : ZMod 6, zpow ζ (c * μ) * decL1 ζ decK ξ μ (v μ) =
      fCoeff ζ (decK false (SwapRigidity.rot c (synthMat ζ v))) ξ -
        zpow ζ ((c - 2) * ξ) * v ξ 1 := by
  simp only [decL1, LinearMap.sub_apply, mul_sub, Finset.sum_sub_distrib,
    ← fCoeff_decK_rot_synthMat hζ]
  congr 1
  rw [Fintype.sum_eq_single ξ]
  · simp only [↓reduceIte, LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]
    rw [← mul_assoc, ← zpow_add hζ, show c * ξ + (- (2 * ξ)) = (c - 2) * ξ by ring]
  · intro μ hμ; simp [hμ]

private lemma analyzeMat_mem_fourierCodeSpace (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    {ζ : K} (hζ : ζ ^ 2 = ζ - 1)
    (decK : Bool → (Matrix (ZMod 6) (ZMod 6) K →ₗ[K] (ZMod 6 → K)))
    {X : Matrix (ZMod 6) (ZMod 6) K} (hX : X ∈ WKSub decK) :
    analyzeMat ζ X ∈ FourierCodeSpace ζ (decL0 ζ decK) (decL1 ζ decK) := by
  intro ξ
  have hsynth : synthMat ζ (analyzeMat ζ X) = X := synthMat_analyzeMat_eq h2 h3 hζ hX
  obtain ⟨hrow1, hrow5⟩ := row1_and_row5_of_mem_WKSub hX
  obtain ⟨hX0, hX1⟩ := hX
  have hv0 : analyzeMat ζ X ξ 0 = fCoeff ζ (X 0) ξ := rfl
  have hv1 : analyzeMat ζ X ξ 1 = fCoeff ζ (X 2) ξ := rfl
  have hv2 : analyzeMat ζ X ξ 2 = fCoeff ζ (X 3) ξ := rfl
  have hv3 : analyzeMat ζ X ξ 3 = fCoeff ζ (X 4) ξ := rfl
  -- Color true equations (c = 0, 1, 2, 3, 4)
  have eq_c0 : ∑ μ : ZMod 6, zpow ζ (0 * μ) * decL0 ζ decK ξ μ (analyzeMat ζ X μ) = 0 := by
    rw [sum_decL0 hζ, hsynth]
    have hd : decK true (SwapRigidity.rot 0 X) = X 0 := (hX0 0).symm
    rw [hd, hv0, zero_mul, zpow_zero, one_mul, sub_self]
  have eq_c1 : ∑ μ : ZMod 6, zpow ζ (1 * μ) * decL0 ζ decK ξ μ (analyzeMat ζ X μ) = 0 := by
    rw [sum_decL0 hζ, hsynth]
    have hd : decK true (SwapRigidity.rot 1 X) = fun j => X 0 (j + 1) := by
      have e := hX0 1
      rw [show SwapRigidity.aperiodicCls 1 = true by decide] at e
      exact e.symm.trans (funext hrow1)
    rw [hd, fCoeff_shift hζ, hv0, sub_self]
  have eq_c2 : ∑ μ : ZMod 6, zpow ζ (2 * μ) * decL0 ζ decK ξ μ (analyzeMat ζ X μ) = 0 := by
    rw [sum_decL0 hζ, hsynth]
    have hd : decK true (SwapRigidity.rot 2 X) = fun j => X 0 (j + 2) := by
      have e := hX1 1
      rw [SwapRigidity.rot_rot, show (1 + 1 : ZMod 6) = 2 by decide] at e
      rw [show SwapRigidity.aperiodicCls 1 = true by decide] at e
      rw [← e]
      funext j
      change X 1 (j + 1) = X 0 (j + 2)
      rw [hrow1 (j + 1), add_assoc, show (1 + 1 : ZMod 6) = 2 by decide]
    rw [hd, fCoeff_shift hζ, hv0, sub_self]
  have eq_c3 : ∑ μ : ZMod 6, zpow ζ (3 * μ) * decL0 ζ decK ξ μ (analyzeMat ζ X μ) =
      d0Form ζ ξ (analyzeMat ζ X ξ) := by
    rw [sum_decL0 hζ, hsynth]
    have hd : decK true (SwapRigidity.rot 3 X) = X 3 := (hX0 3).symm
    rw [hd, ← hv2]
    rfl
  have eq_c4 : ∑ μ : ZMod 6, zpow ζ (4 * μ) * decL0 ζ decK ξ μ (analyzeMat ζ X μ) =
      zpow ζ ξ * d0Form ζ ξ (analyzeMat ζ X ξ) := by
    rw [sum_decL0 hζ, hsynth]
    have hd : decK true (SwapRigidity.rot 4 X) = fun j => X 3 (j + 1) := by
      have e := hX1 3
      rw [SwapRigidity.rot_rot, show (3 + 1 : ZMod 6) = 4 by decide] at e
      rw [show SwapRigidity.aperiodicCls 3 = true by decide] at e
      rw [← e]; rfl
    rw [hd, fCoeff_shift hζ, ← hv2, one_mul,
      show (4 : ZMod 6) * ξ = ξ + 3 * ξ by ring, zpow_add hζ]
    dsimp [d0Form]
    ring
  -- Color false equations (c = 2, 3, 4, 5, 0)
  have eq_g2 : ∑ μ : ZMod 6, zpow ζ (2 * μ) * decL1 ζ decK ξ μ (analyzeMat ζ X μ) = 0 := by
    rw [sum_decL1 hζ, hsynth]
    have hd : decK false (SwapRigidity.rot 2 X) = X 2 := (hX0 2).symm
    rw [hd, hv1, sub_self, zero_mul, zpow_zero, one_mul, sub_self]
  have eq_g3 : ∑ μ : ZMod 6, zpow ζ (3 * μ) * decL1 ζ decK ξ μ (analyzeMat ζ X μ) = 0 := by
    rw [sum_decL1 hζ, hsynth]
    have hd : decK false (SwapRigidity.rot 3 X) = fun j => X 2 (j + 1) := by
      have e := hX1 2
      rw [SwapRigidity.rot_rot, show (2 + 1 : ZMod 6) = 3 by decide] at e
      rw [show SwapRigidity.aperiodicCls 2 = false by decide] at e
      rw [← e]; rfl
    rw [hd, fCoeff_shift hζ, hv1, show (3 - 2 : ZMod 6) = 1 by decide, sub_self]
  have eq_g4 : ∑ μ : ZMod 6, zpow ζ (4 * μ) * decL1 ζ decK ξ μ (analyzeMat ζ X μ) =
      d1Form ζ ξ (analyzeMat ζ X ξ) := by
    rw [sum_decL1 hζ, hsynth]
    have hd : decK false (SwapRigidity.rot 4 X) = X 4 := (hX0 4).symm
    rw [hd, ← hv3, show (4 - 2 : ZMod 6) = 2 by decide]
    rfl
  have eq_g5 : ∑ μ : ZMod 6, zpow ζ (5 * μ) * decL1 ζ decK ξ μ (analyzeMat ζ X μ) =
      zpow ζ ξ * d1Form ζ ξ (analyzeMat ζ X ξ) := by
    rw [sum_decL1 hζ, hsynth]
    have hd : decK false (SwapRigidity.rot 5 X) = fun j => X 4 (j + 1) := by
      have e := hX0 5
      rw [show SwapRigidity.aperiodicCls 5 = false by decide] at e
      exact e.symm.trans (funext hrow5)
    rw [hd, fCoeff_shift hζ, ← hv3, one_mul,
      show (5 - 2 : ZMod 6) * ξ = ξ + 2 * ξ by ring, zpow_add hζ]
    dsimp [d1Form]
    ring
  have eq_g0 : ∑ μ : ZMod 6, zpow ζ (0 * μ) * decL1 ζ decK ξ μ (analyzeMat ζ X μ) =
      zpow ζ (2 * ξ) * d1Form ζ ξ (analyzeMat ζ X ξ) := by
    rw [sum_decL1 hζ, hsynth]
    have hd : decK false (SwapRigidity.rot 0 X) = fun j => X 4 (j + 2) := by
      have e := hX1 5
      rw [SwapRigidity.rot_rot, show (5 + 1 : ZMod 6) = 0 by decide] at e
      rw [show SwapRigidity.aperiodicCls 5 = false by decide] at e
      rw [← e]
      funext j
      change X 5 (j + 1) = X 4 (j + 2)
      rw [hrow5 (j + 1), add_assoc, show (1 + 1 : ZMod 6) = 2 by decide]
    have hexp : (0 - 2 : ZMod 6) * ξ = 2 * ξ + 2 * ξ := by
      rw [show (0 - 2 : ZMod 6) = 2 + 2 by decide]
      ring
    rw [hd, fCoeff_shift hζ, ← hv3, hexp, zpow_add hζ]
    dsimp [d1Form]
    ring
  exact ⟨eq_c0, eq_c1, eq_c2, eq_c3, eq_c4, eq_g2, eq_g3, eq_g4, eq_g5, eq_g0⟩

private theorem finrank_WKSub_le_14 (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    {ζ : K} (hζ : ζ ^ 2 = ζ - 1)
    (decK : Bool → (Matrix (ZMod 6) (ZMod 6) K →ₗ[K] (ZMod 6 → K))) :
    finrank K (WKSub decK) ≤ 14 := by
  let emb : WKSub decK →ₗ[K] FourierCodeSpace ζ (decL0 ζ decK) (decL1 ζ decK) :=
    { toFun := fun X => ⟨analyzeMat ζ X.1, analyzeMat_mem_fourierCodeSpace h2 h3 hζ decK X.2⟩
      map_add' := fun X Y => Subtype.ext (map_add (analyzeMat ζ) X.1 Y.1)
      map_smul' := fun a X => Subtype.ext (map_smul (analyzeMat ζ) a X.1) }
  have hinj : Function.Injective emb := by
    intro X Y hXY
    apply Subtype.ext
    have hval : analyzeMat ζ X.1 = analyzeMat ζ Y.1 := congrArg Subtype.val hXY
    calc X.1 = synthMat ζ (analyzeMat ζ X.1) := (synthMat_analyzeMat_eq h2 h3 hζ X.2).symm
      _ = synthMat ζ (analyzeMat ζ Y.1) := congrArg (synthMat ζ) hval
      _ = Y.1 := synthMat_analyzeMat_eq h2 h3 hζ Y.2
  exact (LinearMap.finrank_le_finrank_of_injective hinj).trans
    (finrank_fourierCodeSpace_le_14 h2 h3 hζ _ _)

end FourierBridge

end FourierSystem

/-! ### Field Extension `F → AlgebraicClosure F` and Main Exported Theorems -/

private def matPiEquiv (R : Type*) [Semiring R] :
    Matrix (ZMod 6) (ZMod 6) R ≃ₗ[R] (ZMod 6 × ZMod 6 → R) where
  toFun M p := M p.1 p.2
  invFun f := Matrix.of fun i j => f (i, j)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def extendMatDecoder {F K : Type*} [Field F] [Field K]
    (φ : F →+* K) (L : Matrix (ZMod 6) (ZMod 6) F →ₗ[F] (ZMod 6 → F)) :
    Matrix (ZMod 6) (ZMod 6) K →ₗ[K] (ZMod 6 → K) :=
  (extendLinearMapPi φ (L.comp (matPiEquiv F).symm.toLinearMap)).comp (matPiEquiv K).toLinearMap

private lemma extendMatDecoder_map {F K : Type*} [Field F] [Field K]
    (φ : F →+* K) (L : Matrix (ZMod 6) (ZMod 6) F →ₗ[F] (ZMod 6 → F))
    (M : Matrix (ZMod 6) (ZMod 6) F) :
    extendMatDecoder φ L (Matrix.of fun i j => φ (M i j)) = fun j => φ (L M j) := by
  dsimp [extendMatDecoder]
  have harg : matPiEquiv K (Matrix.of fun i j => φ (M i j)) = fun p => φ (matPiEquiv F M p) := rfl
  rw [harg, extendLinearMapPi_comp_map]
  rfl

/-- **Single-shift intersection ceiling `≤ 14`** for `SwapRigidity.aperiodicCls` over every field
`F` with `ringChar F ≠ 2` and `ringChar F ≠ 3`. -/
theorem aperiodicSix_shift_inf_finrank_le_14
    (F : Type*) [Field F] (hchar2 : ringChar F ≠ 2) (hchar3 : ringChar F ≠ 3)
    (𝒳 : Submodule F (Matrix (ZMod 6) (ZMod 6) F))
    (h𝒳 : SwapRigidity.IsClassUniformCode SwapRigidity.aperiodicCls 𝒳) :
    finrank F ↥(𝒳 ⊓ 𝒳.comap (SwapRigidity.rot 1)) ≤ 14 := by
  obtain ⟨h2F, h3F⟩ := (ringChar_ne_two_three_iff_ne_zero F).mp ⟨hchar2, hchar3⟩
  have hcop : CoprimeToChar F 6 := (ringChar_ne_two_three_iff_coprimeSix F).mp ⟨hchar2, hchar3⟩
  let K := AlgebraicClosure F
  let φ : F →+* K := algebraMap F K
  have h2K : (2 : K) ≠ 0 := fun h0 =>
    h2F (φ.injective (by rw [map_ofNat, map_zero]; exact h0))
  have h3K : (3 : K) ≠ 0 := fun h0 =>
    h3F (φ.injective (by rw [map_ofNat, map_zero]; exact h0))
  obtain ⟨ζ, hprim⟩ := exists_isPrimitiveRoot_algebraicClosure F 6 hcop
  have hζ : ζ ^ 2 = ζ - 1 := isPrimitiveRoot_six_rel hprim
  obtain ⟨dec, hdec⟩ := h𝒳
  let decK : Bool → (Matrix (ZMod 6) (ZMod 6) K →ₗ[K] (ZMod 6 → K)) :=
    fun b => extendMatDecoder φ (dec b)
  have hpush_code : ∀ Y ∈ 𝒳, (Matrix.of fun i j => φ (Y i j)) ∈ codeOfDec decK := by
    intro Y hY c
    funext j
    have hrot : SwapRigidity.rot c (Matrix.of fun i' j' => φ (Y i' j')) =
        Matrix.of fun i' j' => φ ((SwapRigidity.rot c Y) i' j') := by
      ext i' j'; rfl
    dsimp [decK]
    rw [hrot, extendMatDecoder_map]
    exact congrArg φ (congrFun (hdec Y hY c) j)
  let U : Submodule F (ZMod 6 × ZMod 6 → F) :=
    (𝒳 ⊓ 𝒳.comap (SwapRigidity.rot 1)).map (matPiEquiv F).toLinearMap
  let W : Submodule K (ZMod 6 × ZMod 6 → K) :=
    (WKSub decK).map (matPiEquiv K).toLinearMap
  have hUW : ∀ x ∈ U, (fun p => φ (x p)) ∈ W := by
    rintro x ⟨X, ⟨hX0, hX1⟩, rfl⟩
    refine ⟨Matrix.of fun i j => φ (X i j), ⟨hpush_code X hX0, ?_⟩, rfl⟩
    change SwapRigidity.rot 1 (Matrix.of fun i j => φ (X i j)) ∈ codeOfDec decK
    have hrot1 : SwapRigidity.rot 1 (Matrix.of fun i j => φ (X i j)) =
        Matrix.of fun i j => φ ((SwapRigidity.rot 1 X) i j) := by
      ext i j; rfl
    rw [hrot1]
    exact hpush_code (SwapRigidity.rot 1 X) hX1
  have hU_dim : finrank F U = finrank F ↥(𝒳 ⊓ 𝒳.comap (SwapRigidity.rot 1)) :=
    LinearEquiv.finrank_map_eq (matPiEquiv F) _
  have hW_dim : finrank K W = finrank K (WKSub decK) :=
    LinearEquiv.finrank_map_eq (matPiEquiv K) _
  calc finrank F ↥(𝒳 ⊓ 𝒳.comap (SwapRigidity.rot 1))
      = finrank F U := hU_dim.symm
    _ ≤ finrank K W := finrank_le_of_pi_ringHom φ U W hUW
    _ = finrank K (WKSub decK) := hW_dim
    _ ≤ 14 := finrank_WKSub_le_14 h2K h3K hζ decK

/-! ### Section 5: Grassmann `≤ 25`, Exactness `= 25`, Partition Transfer & Exports -/

private def rotEquiv (F : Type*) [Field F] {n : ℕ} (c : ZMod n) :
    Matrix (ZMod n) (ZMod n) F ≃ₗ[F] Matrix (ZMod n) (ZMod n) F where
  toLinearMap := SwapRigidity.rot c
  invFun := SwapRigidity.rot (-c)
  left_inv X := by
    change SwapRigidity.rot (-c) (SwapRigidity.rot c X) = X
    rw [SwapRigidity.rot_rot, neg_add_cancel]
    ext i j; simp
  right_inv X := by
    change SwapRigidity.rot c (SwapRigidity.rot (-c) X) = X
    rw [SwapRigidity.rot_rot, add_neg_cancel]
    ext i j; simp

private lemma comap_rot_eq_map (F : Type*) [Field F] {n : ℕ} (c : ZMod n)
    (𝒳 : Submodule F (Matrix (ZMod n) (ZMod n) F)) :
    𝒳.comap (SwapRigidity.rot c) = 𝒳.map (rotEquiv F (-c)).toLinearMap := by
  ext X
  simp only [Submodule.mem_comap, Submodule.mem_map]
  constructor
  · intro hX
    refine ⟨SwapRigidity.rot c X, hX, ?_⟩
    change SwapRigidity.rot (-c) (SwapRigidity.rot c X) = X
    rw [SwapRigidity.rot_rot, neg_add_cancel]
    ext i j; simp
  · rintro ⟨Y, hY, rfl⟩
    change SwapRigidity.rot c (SwapRigidity.rot (-c) Y) ∈ 𝒳
    rw [SwapRigidity.rot_rot, add_neg_cancel]
    have h0 : SwapRigidity.rot 0 Y = Y := by ext i j; simp
    rw [h0]
    exact hY

private lemma aperiodicSix_two_mul_finrank_le_50
    (F : Type*) [Field F] (hchar2 : ringChar F ≠ 2) (hchar3 : ringChar F ≠ 3)
    (𝒳 : Submodule F (Matrix (ZMod 6) (ZMod 6) F))
    (h𝒳 : SwapRigidity.IsClassUniformCode SwapRigidity.aperiodicCls 𝒳) :
    2 * finrank F 𝒳 ≤ 36 + 14 := by
  have hinf := aperiodicSix_shift_inf_finrank_le_14 F hchar2 hchar3 𝒳 h𝒳
  have hgrass := Submodule.finrank_sup_add_finrank_inf_eq 𝒳 (𝒳.comap (SwapRigidity.rot 1))
  have hcomap : finrank F ↥(𝒳.comap (SwapRigidity.rot 1)) = finrank F 𝒳 := by
    rw [comap_rot_eq_map F 1 𝒳]
    exact LinearEquiv.finrank_map_eq (rotEquiv F (-1)) 𝒳
  have hsup : finrank F ↥(𝒳 ⊔ 𝒳.comap (SwapRigidity.rot 1)) ≤ 36 := by
    have hle := Submodule.finrank_le (𝒳 ⊔ 𝒳.comap (SwapRigidity.rot 1))
    rw [SwapRigidity.finrank_matrix_zmod] at hle
    exact hle
  omega

/-- **Code dimension ceiling `≤ 25`** for `SwapRigidity.aperiodicCls` over every field `F` with
`ringChar F ≠ 2` and `ringChar F ≠ 3`. -/
theorem aperiodicSix_finrank_le_25
    (F : Type*) [Field F] (hchar2 : ringChar F ≠ 2) (hchar3 : ringChar F ≠ 3)
    (𝒳 : Submodule F (Matrix (ZMod 6) (ZMod 6) F))
    (h𝒳 : SwapRigidity.IsClassUniformCode SwapRigidity.aperiodicCls 𝒳) :
    finrank F 𝒳 ≤ 25 := by
  have := aperiodicSix_two_mul_finrank_le_50 F hchar2 hchar3 𝒳 h𝒳
  omega

private def laneOneRowEquiv (F : Type*) [Semiring F] (d : ℕ) :
    (ZMod d → Fin 1 → F) ≃ₗ[F] (ZMod d → F) where
  toFun r j := r j 0
  invFun r j _ := r j
  left_inv r := by ext j u; fin_cases u; rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private lemma dim_set_linearOne_eq_classUniform (F : Type*) [Field F] {κ : Type*}
    (p : ZMod 6 → κ) :
    {k : ℕ | ∃ 𝒴 : Submodule F (Matrix (ZMod 6) (ZMod 6) (Fin 1 → F)),
      IsLinearClassUniformCode p 𝒴 ∧ finrank F 𝒴 = k} =
    {k : ℕ | ∃ 𝒳 : Submodule F (Matrix (ZMod 6) (ZMod 6) F),
      SwapRigidity.IsClassUniformCode p 𝒳 ∧ finrank F 𝒳 = k} := by
  let eM := laneOneMatrixEquiv F 6
  let eR := laneOneRowEquiv F 6
  ext k
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨𝒴, ⟨dec, hdec⟩, rfl⟩
    refine ⟨𝒴.map eM.toLinearMap, ⟨fun m => eR.toLinearMap.comp ((dec m).comp eM.symm.toLinearMap),
      ?_⟩, LinearEquiv.finrank_map_eq eM 𝒴⟩
    rintro _ ⟨Y, hY, rfl⟩ c
    funext j
    have hrot : eM.symm (SwapRigidity.rot c (eM Y)) = laneRot c Y := by
      ext i' j' u; fin_cases u; rfl
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hrot]
    exact congrFun (congrFun (hdec Y hY c) j) 0
  · rintro ⟨𝒳, ⟨dec, hdec⟩, rfl⟩
    refine ⟨𝒳.map eM.symm.toLinearMap, ⟨fun m => eR.symm.toLinearMap.comp ((dec m).comp eM.toLinearMap),
      ?_⟩, LinearEquiv.finrank_map_eq eM.symm 𝒳⟩
    rintro _ ⟨X, hX, rfl⟩ c
    funext j u
    fin_cases u
    have hrot : eM (laneRot c (eM.symm X)) = SwapRigidity.rot c X := by
      ext i' j'; rfl
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hrot]
    exact congrFun (hdec X hX c) j

private lemma isClassUniformCode_iff_of_isAperiodicSixPartition
    {F : Type*} [Field F] {κ : Type*} {cls : ZMod 6 → κ} (hcls : IsAperiodicSixPartition cls)
    (𝒳 : Submodule F (Matrix (ZMod 6) (ZMod 6) F)) :
    SwapRigidity.IsClassUniformCode cls 𝒳 ↔
      SwapRigidity.IsClassUniformCode SwapRigidity.aperiodicCls 𝒳 := by
  constructor
  · rintro ⟨dec, hdec⟩
    refine ⟨fun b => if b then dec (cls 0) else dec (cls 2), fun X hX c => ?_⟩
    cases hb : SwapRigidity.aperiodicCls c
    · have hc2 : cls c = cls 2 :=
        (hcls c 2).mpr (hb.trans (show false = SwapRigidity.aperiodicCls 2 by decide))
      simpa [hc2] using hdec X hX c
    · have hc0 : cls c = cls 0 :=
        (hcls c 0).mpr (hb.trans (show true = SwapRigidity.aperiodicCls 0 by decide))
      simpa [hc0] using hdec X hX c
  · rintro ⟨decB, hdecB⟩
    classical
    refine ⟨fun m => if m = cls 0 then decB true else decB false, fun X hX c => ?_⟩
    cases hb : SwapRigidity.aperiodicCls c
    · have hc2 : cls c = cls 2 :=
        (hcls c 2).mpr (hb.trans (show false = SwapRigidity.aperiodicCls 2 by decide))
      have hne : cls 2 ≠ cls 0 := by
        intro heq
        have hfalse_true := (hcls 2 0).mp heq
        revert hfalse_true; decide
      simpa [hc2, hne, hb] using hdecB X hX c
    · have hc0 : cls c = cls 0 :=
        (hcls c 0).mpr (hb.trans (show true = SwapRigidity.aperiodicCls 0 by decide))
      simpa [hc0, hb] using hdecB X hX c

/-- **Exact maximum dimension `= 25`** (`IsGreatest ... 25` and
`linearClassUniformMaxDim F 1 SwapRigidity.aperiodicCls = 25`) over every field `F` with
`ringChar F ≠ 2` and `ringChar F ≠ 3`. -/
theorem aperiodicSix_maxDim_eq_25
    (F : Type*) [Field F] (hchar2 : ringChar F ≠ 2) (hchar3 : ringChar F ≠ 3) :
    IsGreatest
      {k : ℕ | ∃ 𝒳 : Submodule F (Matrix (ZMod 6) (ZMod 6) F),
        SwapRigidity.IsClassUniformCode SwapRigidity.aperiodicCls 𝒳 ∧ finrank F 𝒳 = k}
      25 ∧
    linearClassUniformMaxDim F 1 SwapRigidity.aperiodicCls = 25 := by
  obtain ⟨_, h3F⟩ := (ringChar_ne_two_three_iff_ne_zero F).mp ⟨hchar2, hchar3⟩
  obtain ⟨𝒳₀, h𝒳₀_cu, h𝒳₀_dim⟩ := ClassUniformMemo.exists_code_of_three_ne_zero F h3F
  have hmem : 25 ∈ {k : ℕ | ∃ 𝒳 : Submodule F (Matrix (ZMod 6) (ZMod 6) F),
      SwapRigidity.IsClassUniformCode SwapRigidity.aperiodicCls 𝒳 ∧ finrank F 𝒳 = k} :=
    ⟨𝒳₀, h𝒳₀_cu, h𝒳₀_dim⟩
  have hub : ∀ k ∈ {k : ℕ | ∃ 𝒳 : Submodule F (Matrix (ZMod 6) (ZMod 6) F),
      SwapRigidity.IsClassUniformCode SwapRigidity.aperiodicCls 𝒳 ∧ finrank F 𝒳 = k},
      k ≤ 25 := by
    rintro k ⟨𝒳, h𝒳, rfl⟩
    exact aperiodicSix_finrank_le_25 F hchar2 hchar3 𝒳 h𝒳
  have hgreat : IsGreatest
      {k : ℕ | ∃ 𝒳 : Submodule F (Matrix (ZMod 6) (ZMod 6) F),
        SwapRigidity.IsClassUniformCode SwapRigidity.aperiodicCls 𝒳 ∧ finrank F 𝒳 = k}
      25 := ⟨hmem, hub⟩
  refine ⟨hgreat, ?_⟩
  unfold linearClassUniformMaxDim
  rw [dim_set_linearOne_eq_classUniform F SwapRigidity.aperiodicCls]
  exact le_antisymm (csSup_le ⟨25, hmem⟩ hub) (le_csSup ⟨25, hub⟩ hmem)

/-- **`Theorem 2` (`Extension_Theorem2_AperiodicSixExactSpec`)**: complete solution
`D({0, 1, 3}, {2, 4, 5}) = 25` over every field `F` with `ringChar F ≠ 2` and `ringChar F ≠ 3`. -/
theorem extension_Theorem2_AperiodicSixExact : Extension_Theorem2_AperiodicSixExactSpec := by
  intro F _ hchar2 hchar3
  obtain ⟨hgreat_ap, hmax_ap⟩ := aperiodicSix_maxDim_eq_25 F hchar2 hchar3
  refine ⟨?_, hgreat_ap, hmax_ap, ?_⟩
  · intro 𝒳 h𝒳
    exact ⟨aperiodicSix_shift_inf_finrank_le_14 F hchar2 hchar3 𝒳 h𝒳,
      aperiodicSix_two_mul_finrank_le_50 F hchar2 hchar3 𝒳 h𝒳,
      aperiodicSix_finrank_le_25 F hchar2 hchar3 𝒳 h𝒳⟩
  · intro κ cls hcls
    have hset_eq :
        {k : ℕ | ∃ 𝒳 : Submodule F (Matrix (ZMod 6) (ZMod 6) F),
          SwapRigidity.IsClassUniformCode cls 𝒳 ∧ finrank F 𝒳 = k} =
        {k : ℕ | ∃ 𝒳 : Submodule F (Matrix (ZMod 6) (ZMod 6) F),
          SwapRigidity.IsClassUniformCode SwapRigidity.aperiodicCls 𝒳 ∧ finrank F 𝒳 = k} := by
      ext k
      simp only [Set.mem_ofPred_eq]
      exact exists_congr fun 𝒳 => and_congr_left fun _ =>
        isClassUniformCode_iff_of_isAperiodicSixPartition hcls 𝒳
    refine ⟨?_, hset_eq ▸ hgreat_ap, ?_⟩
    · intro 𝒳 h𝒳
      have h𝒳' := (isClassUniformCode_iff_of_isAperiodicSixPartition hcls 𝒳).mp h𝒳
      exact ⟨aperiodicSix_shift_inf_finrank_le_14 F hchar2 hchar3 𝒳 h𝒳',
        aperiodicSix_finrank_le_25 F hchar2 hchar3 𝒳 h𝒳'⟩
    · unfold linearClassUniformMaxDim
      rw [dim_set_linearOne_eq_classUniform F cls, hset_eq,
        ← dim_set_linearOne_eq_classUniform F SwapRigidity.aperiodicCls]
      exact hmax_ap

end BoundedArityDecoders
