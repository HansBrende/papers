import BoundedArityDecoders.SumsetRankDeficit
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Proofs — Part II.B: Sumset Polynomial Recurrence & Log-Power Rank Deficit

Complete kernel-verified proofs of all unconditional claim specifications and
open-target bridge implications in `BoundedArityDecoders.SumsetRankDeficit`.
-/

namespace BoundedArityDecoders

open SharedDecoders Module Polynomial
open scoped BigOperators

/-! ### Step 1: Shifting Unshifted Sumsets so `0 ∈ B̃_t` -/

/-- Proof of `UnshiftedToShiftedSumsetSpec`: shifting each `B t` by its minimum `b₀ t`
places `0 ∈ B̃_t` while preserving cardinality `k + 1`, diameter `≤ L₀`, and all subset sums. -/
theorem unshiftedToShiftedSumset : UnshiftedToShiftedSumsetSpec := by
  intro d M₁ nSteps k L₀ _ p₁ m₁ J₀ B h
  rcases h with ⟨hJ₀, hB, hsum⟩
  have hBne : ∀ t : Fin nSteps, (B t).Nonempty := fun t =>
    Finset.card_pos.mp (by rw [(hB t).1]; omega)
  let b₀ : Fin nSteps → ℕ := fun t => (B t).min' (hBne t)
  have hb₀_mem : ∀ t, b₀ t ∈ B t := fun t => Finset.min'_mem (B t) (hBne t)
  have hb₀_le : ∀ t, ∀ x ∈ B t, b₀ t ≤ x := fun t x hx => Finset.min'_le (B t) x hx
  let B_tilde : Fin nSteps → Finset ℕ := fun t => (B t).image (fun x => x - b₀ t)
  let shiftSum : ZMod d := ∑ t : Fin nSteps, (b₀ t : ZMod d)
  let J₀_tilde : Finset (ZMod d) := J₀.image (fun c => c + shiftSum)
  have hJ₀_tilde_card : J₀_tilde.card = k := by
    rw [Finset.card_image_of_injective _ (add_left_injective shiftSum), hJ₀]
  have hB_tilde : ∀ t : Fin nSteps,
      0 ∈ B_tilde t ∧ (B_tilde t).card = k + 1 ∧ ∀ y ∈ B_tilde t, y ≤ L₀ := by
    intro t
    refine ⟨?_, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨b₀ t, hb₀_mem t, Nat.sub_self _⟩
    · have hinj : Set.InjOn (fun x => x - b₀ t) (B t : Set ℕ) := by
        intro x hx y hy hxy
        dsimp at hxy
        have hxl := hb₀_le t x hx
        have hyl := hb₀_le t y hy
        omega
      rw [Finset.card_image_of_injOn hinj, (hB t).1]
    · intro y hy
      rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
      exact (Nat.sub_le _ _).trans ((hB t).2 x hx)
  have hsub : ∀ (S : Finset (Fin nSteps)) (c₀' : ZMod d), c₀' ∈ J₀_tilde →
      ∀ b : Fin nSteps → ℕ, (∀ t ∈ S, b t ∈ B_tilde t) →
        p₁ (c₀' + ∑ t ∈ S, (b t : ZMod d)) = m₁ := by
    intro S c₀' hc₀' b hb
    rcases Finset.mem_image.mp hc₀' with ⟨c₀, hc₀, rfl⟩
    let b_orig : Fin nSteps → ℕ := fun t => (if t ∈ S then b t else 0) + b₀ t
    have hb_orig : ∀ t : Fin nSteps, b_orig t ∈ B t := by
      intro t
      dsimp [b_orig]
      by_cases ht : t ∈ S
      · simp only [ht, ↓reduceIte]
        rcases Finset.mem_image.mp (hb t ht) with ⟨x, hx, hxb⟩
        rw [← hxb, Nat.sub_add_cancel (hb₀_le t x hx)]
        exact hx
      · simp only [ht, ↓reduceIte, zero_add]
        exact hb₀_mem t
    have heq : c₀ + shiftSum + ∑ t ∈ S, (b t : ZMod d) =
        c₀ + ∑ t : Fin nSteps, (b_orig t : ZMod d) := by
      have hS : (∑ t ∈ S, (b t : ZMod d)) =
          ∑ t : Fin nSteps, (if t ∈ S then (b t : ZMod d) else 0) := by
        rw [← Finset.sum_filter]
        congr 1
        ext t
        simp
      rw [hS, add_assoc]
      congr 1
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro t _
      dsimp [b_orig]
      by_cases ht : t ∈ S <;> simp [ht, add_comm]
    rw [heq]
    exact hsum c₀ hc₀ b_orig hb_orig
  refine ⟨J₀_tilde, B_tilde, ⟨hJ₀_tilde_card, hB_tilde, ?_⟩, hsub⟩
  intro c₀' hc₀' b hb
  exact hsub Finset.univ c₀' hc₀' b (fun t _ => hb t)

/-! ### Step 2a: Arbitrary-Subset Vandermonde Injectivity -/

/-- Proof of `VandermondeArbitrarySubsetInjectiveSpec` over any field `E` and `E`-module `V`,
using the nonsingular inverse of `Matrix.vandermonde` on the distinct character values `χ c`. -/
theorem vandermondeArbitrarySubsetInjective : VandermondeArbitrarySubsetInjectiveSpec := by
  intro d k _ E V _ _ _ χ J₀ hχ hcard a₁ a₂ heval
  classical
  let e : Fin k ≃ J₀ := (Fintype.equivFinOfCardEq (by simp [hcard])).symm
  let pts : Fin k → E := fun i => χ (e i).1
  have hpts : Function.Injective pts := by
    intro i j hij
    exact e.injective (Subtype.ext (hχ hij))
  let M : Matrix (Fin k) (Fin k) E := Matrix.vandermonde pts
  have hdet : M.det ≠ 0 := by
    rw [Matrix.det_vandermonde]
    rw [Finset.prod_ne_zero_iff]
    intro i _
    rw [Finset.prod_ne_zero_iff]
    intro j hj
    have hij : i ≠ j := ne_of_lt (Finset.mem_Ioi.mp hj)
    exact sub_ne_zero.mpr (hpts.ne hij.symm)
  have hinv : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr hdet)
  have hrow : ∀ i : Fin k, ∑ ν : Fin k, M i ν • (a₁ ν - a₂ ν) = 0 := by
    intro i
    have hi := congrFun heval (e i)
    have hsub : charBandEval χ J₀ a₁ (e i) - charBandEval χ J₀ a₂ (e i) = 0 :=
      sub_eq_zero.mpr hi
    rw [charBandEval, charBandEval, ← Finset.sum_sub_distrib] at hsub
    refine Eq.trans ?_ hsub
    apply Finset.sum_congr rfl
    intro ν _
    have hpow : M i ν = χ ((ν.val : ZMod d) * (e i).1) := by
      change pts i ^ ν.val = _
      rw [mul_comm, character_nat_mul]
    rw [hpow, smul_sub]
  funext μ
  have hzero : ∑ i : Fin k, M⁻¹ μ i • (∑ ν : Fin k, M i ν • (a₁ ν - a₂ ν)) = 0 := by
    simp [hrow]
  have hcalc : ∑ i : Fin k, M⁻¹ μ i • (∑ ν : Fin k, M i ν • (a₁ ν - a₂ ν)) = a₁ μ - a₂ μ := by
    simp_rw [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    calc
      ∑ ν : Fin k, ∑ i : Fin k, (M⁻¹ μ i * M i ν) • (a₁ ν - a₂ ν)
          = ∑ ν : Fin k, (∑ i : Fin k, M⁻¹ μ i * M i ν) • (a₁ ν - a₂ ν) := by
            apply Finset.sum_congr rfl
            intro ν _
            rw [Finset.sum_smul]
      _ = ∑ ν : Fin k, (M⁻¹ * M) μ ν • (a₁ ν - a₂ ν) := rfl
      _ = ∑ ν : Fin k, (1 : Matrix (Fin k) (Fin k) E) μ ν • (a₁ ν - a₂ ν) := by rw [hinv]
      _ = a₁ μ - a₂ μ := by
            rw [Finset.sum_eq_single μ]
            · simp
            · intro ν _ hνμ
              simp [Matrix.one_apply_ne' hνμ]
            · intro hμ
              exact False.elim (hμ (Finset.mem_univ μ))
  exact sub_eq_zero.mp (hcalc.symm.trans hzero)

/-! ### Step 2b: Pullback Subspace `W` with Witness & Arbitrary-Subset Injectivity -/

/-- Strengthened pullback construction returning both the dimension/injectivity properties of
`StackedBandPullbackInjectiveSpec` and the exact intermediate band witness `K₁ (embed x) = bandMap u`. -/
lemma stackedBandPullbackData
    (E : Type*) [Field E] (d b M₁ M₂ k : ℕ) [NeZero d]
    (χ : AddChar (ZMod d) E)
    (p₁ : ZMod d → Fin M₁) (p₂ : ZMod d → Fin M₂) (m₁ : Fin M₁)
    (J₀ : Finset (ZMod d))
    (K₁ K₂ : State d (Fin b → E) →ₗ[E] State d (Fin b → E))
    (f₁ : Fin M₁ → State d (Fin b → E) →ₗ[E] (ZMod d → Fin b → E))
    (hχ : Function.Injective χ)
    (hkd : k ≤ d)
    (hJ₀ : J₀.card = k)
    (hmono : ∀ c ∈ J₀, p₁ c = m₁)
    (hf₁ : ∀ X c i, K₁ X i c = f₁ (p₁ c) (rot c X) i)
    (hK₂ : ClassUniform p₂ K₂) :
    ∃ W : Submodule E (ColumnAmbient (bandRowSpace (b := b) χ p₂ k)),
      b * k * d ≤
        finrank E W +
          finrank E (LinearMap.range (swapLinear E (d := d) (A := Fin b → E) - K₂.comp K₁)) ∧
      (∀ x ∈ W,
        (∀ c ∈ J₀, f₁ m₁ (rot c (columnAmbientEmbed (bandRowSpace (b := b) χ p₂ k) x)) = 0) →
          x = 0) ∧
      (∀ x ∈ W, ∃ u : Fin k → ZMod d → Fin b → E,
        K₁ (columnAmbientEmbed (bandRowSpace (b := b) χ p₂ k) x) = bandMap χ k u) := by
  classical
  have hK₂_lin : LinearClassUniform p₂ K₂ := linearClassUniform_of_classUniform p₂ K₂ hK₂
  let H := bandRowSpace (b := b) χ p₂ k
  let V := ColumnAmbient H
  let E_map := bandMap (b := b) χ k
  let B_map := (swapLinear E (d := d) (A := Fin b → E)).comp K₂
  let Q := LinearMap.ker ((LinearMap.id - K₁.comp B_map).comp E_map)
  let P : Q →ₗ[E] V := (bandPull χ p₂ K₂ hK₂_lin).comp Q.subtype
  let W := LinearMap.range P
  have hP : Function.Injective P := by
    intro x y h
    apply band_correct_map_injective K₁ B_map E_map (bandMap_injective χ hχ hkd)
    exact congrArg (columnAmbientEmbed H) h
  have hdim := band_correct_dimension K₁ B_map E_map
  have hdimW : b * k * d ≤ finrank E W +
      finrank E (LinearMap.range (swapLinear E (d := d) (A := Fin b → E) - K₂.comp K₁)) := by
    rw [LinearMap.finrank_range_of_inj hP]
    have he : (LinearMap.id - B_map.comp K₁) =
        LinearMap.id - (swapLinear E).comp (K₂.comp K₁) := rfl
    rw [he, swap_error_rank] at hdim
    have hdom : finrank E (Fin k → ZMod d → Fin b → E) = b * k * d := by
      simp [Module.finrank_pi_fintype, ZMod.card]
      ring
    rwa [hdom] at hdim
  have hwitness : ∀ x ∈ W, ∃ u : Fin k → ZMod d → Fin b → E,
      K₁ (columnAmbientEmbed H x) = E_map u ∧ columnAmbientEmbed H x = B_map (E_map u) := by
    rintro x ⟨u, rfl⟩
    exact ⟨u.val, (sub_eq_zero.mp u.property).symm, rfl⟩
  refine ⟨W, hdimW, ?_, fun x hx => let ⟨u, hu, _⟩ := hwitness x hx; ⟨u, hu⟩⟩
  intro x hx hz
  obtain ⟨u, hu, hxu⟩ := hwitness x hx
  have heval : charBandEval (k := k) (V := ZMod d → Fin b → E) χ J₀ u =
      charBandEval (k := k) (V := ZMod d → Fin b → E) χ J₀ 0 := by
    funext c i l
    have hc : p₁ c.1 = m₁ := hmono c.1 c.2
    have h0 : f₁ m₁ (rot c.1 (columnAmbientEmbed H x)) i l = 0 := by
      simpa using congrFun (congrFun (hz c.1 c.2) i) l
    have hK := congrFun (congrFun (congrFun hu i) c.1) l
    rw [hf₁, hc] at hK
    have hlhs : charBandEval (k := k) χ J₀ u c i l = E_map u i c.1 l := by
      simp [charBandEval, E_map, Finset.sum_apply]
    have hrhs : charBandEval (k := k) (V := ZMod d → Fin b → E) χ J₀ 0 c i l = 0 := by
      simp [charBandEval]
    rw [hlhs, ← hK, h0, hrhs]
  have hu0 : u = 0 :=
    vandermondeArbitrarySubsetInjective d k E (ZMod d → Fin b → E) χ J₀ hχ hJ₀ heval
  apply columnAmbientEmbed_injective H
  rw [hxu, hu0, map_zero, map_zero, map_zero]

/-- Proof of `StackedBandPullbackInjectiveSpec`. -/
theorem stackedBandPullbackInjective : StackedBandPullbackInjectiveSpec := by
  intro E _ d b M₁ M₂ k _ χ p₁ p₂ m₁ J₀ K₁ K₂ f₁ hχ hkd hJ₀ hmono hf₁ hK₂
  obtain ⟨W, hdimW, hinj, _⟩ :=
    stackedBandPullbackData E d b M₁ M₂ k χ p₁ p₂ m₁ J₀ K₁ K₂ f₁ hχ hkd hJ₀ hmono hf₁ hK₂
  exact ⟨W, hdimW, hinj⟩

/-! ### Step 3: Sparse Sumset Annihilating Polynomial & Cyclic Kernel Bound -/

lemma cyclicChannelShift_pow_apply {R : Type*} [Semiring R] (d q : ℕ) (s : ZMod d)
    (j : ℕ) (w : ZMod d → Fin q → R) (u : ZMod d) (ch : Fin q) :
    ((cyclicChannelShift R d q s ^ j) w) u ch = w (u + (j : ZMod d) * s) ch := by
  induction j generalizing u with
  | zero => simp
  | succ j ih =>
      rw [pow_succ', Module.End.mul_apply]
      change ((cyclicChannelShift R d q s ^ j) w) (u + s) ch = _
      rw [ih (u + s)]
      have hidx : u + s + (j : ZMod d) * s = u + ((j + 1 : ℕ) : ZMod d) * s := by
        push_cast
        ring
      rw [hidx]

/-- Kernel dimension bound `finrank E (ker P(T)) ≤ q * P.natDegree` for any nonzero polynomial
`P : Polynomial E` acting by `cyclicChannelShift E d q 1`. -/
lemma cyclicChannelShift_aeval_ker_finrank_le
    {d q : ℕ} [NeZero d] {E : Type*} [Field E] {P : Polynomial E} (hP : P ≠ 0) :
    finrank E (LinearMap.ker (Polynomial.aeval (cyclicChannelShift E d q 1) P)) ≤
      q * P.natDegree := by
  let m := P.natDegree
  let T := cyclicChannelShift E d q 1
  let res : LinearMap.ker (Polynomial.aeval T P) →ₗ[E] (Fin m → Fin q → E) :=
    { toFun := fun w j ch => w.1 (j.val : ZMod d) ch
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hlead : P.coeff m ≠ 0 := by
    change P.leadingCoeff ≠ 0
    exact Polynomial.leadingCoeff_ne_zero.mpr hP
  have hinj : Function.Injective res := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    apply Subtype.ext
    let v : ZMod d → Fin q → E := w.1
    have hker : Polynomial.aeval T P v = 0 := w.2
    have hn : ∀ n : ℕ, ∀ ch : Fin q, v (n : ZMod d) ch = 0 := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
        intro ch
        by_cases hnm : n < m
        · exact congrFun (congrFun hw ⟨n, hnm⟩) ch
        · have hle : m ≤ n := by omega
          have he := congrFun (congrFun hker ((n - m : ℕ) : ZMod d)) ch
          rw [Polynomial.aeval_eq_sum_range] at he
          simp only [LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply,
            Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at he
          have hstep : ∀ j : ℕ, ((T ^ j) v) ((n - m : ℕ) : ZMod d) ch =
              v (((n - m + j : ℕ) : ZMod d)) ch := by
            intro j
            rw [cyclicChannelShift_pow_apply]
            have hidx : ((n - m : ℕ) : ZMod d) + (j : ZMod d) * 1 =
                ((n - m + j : ℕ) : ZMod d) := by
              simp [Nat.cast_add]
            rw [hidx]
          simp_rw [hstep] at he
          rw [Finset.sum_range_succ] at he
          have hpref : ∑ x ∈ Finset.range m,
              P.coeff x * v (((n - m + x : ℕ) : ZMod d)) ch = 0 := by
            apply Finset.sum_eq_zero
            intro x hx
            have hxm : x < m := Finset.mem_range.mp hx
            rw [ih (n - m + x) (by omega) ch, mul_zero]
          rw [hpref, zero_add, Nat.sub_add_cancel hle] at he
          exact (mul_eq_zero.mp he).resolve_left hlead
    funext u ch
    simpa [v] using hn u.val ch
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  simpa [Module.finrank_pi_fintype, mul_comm] using hle

/-- Proof of `SumsetAnnihilatingPolynomialSpec`. -/
theorem sumsetAnnihilatingPolynomial : SumsetAnnihilatingPolynomialSpec := by
  intro d k q L₀ _ E _ χ B_t _ _ hcard hB_le
  classical
  let evalMap : (B_t → E) →ₗ[E] (Fin k → E) :=
    { toFun := fun α ν => ∑ x : B_t, α x * χ (((ν.val * x.1 : ℕ) : ZMod d))
      map_add' := fun α β => by
        funext ν
        simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun c α => by
        funext ν
        simp [Finset.mul_sum, mul_assoc] }
  have hnotinj : ¬ Function.Injective evalMap := by
    intro hinj
    have hle := LinearMap.finrank_le_finrank_of_injective hinj
    have hdom : finrank E (B_t → E) = k + 1 := by simp [hcard]
    have hcod : finrank E (Fin k → E) = k := by simp
    omega
  have hker_ne : LinearMap.ker evalMap ≠ ⊥ := by
    intro hbot
    exact hnotinj ((LinearMap.ker_eq_bot).mp hbot)
  obtain ⟨α, hα_ker, hα_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker_ne
  let P : Polynomial E := ∑ x : B_t, Polynomial.monomial x.1 (α x)
  have hcoeff_mem : ∀ x : B_t, P.coeff x.1 = α x := by
    intro x
    simp only [P, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
    rw [Finset.sum_eq_single x]
    · simp
    · intro y _ hyx
      have hval : y.1 ≠ x.1 := fun h => hyx (Subtype.ext h)
      simp [hval]
    · intro hx
      exact False.elim (hx (Finset.mem_univ x))
  have hcoeff_not_mem : ∀ n : ℕ, n ∉ B_t → P.coeff n = 0 := by
    intro n hn
    simp only [P, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
    apply Finset.sum_eq_zero
    intro x _
    have hne : x.1 ≠ n := fun h => hn (h ▸ x.2)
    simp [hne]
  have hP_ne : P ≠ 0 := by
    have hα_ex : ∃ x : B_t, α x ≠ 0 := by
      by_contra hall
      apply hα_ne
      funext x
      by_contra hx
      exact hall ⟨x, hx⟩
    obtain ⟨x, hx⟩ := hα_ex
    intro hP0
    apply hx
    rw [← hcoeff_mem x, hP0, Polynomial.coeff_zero]
  have hsupp : ∀ n ∈ P.support, n ∈ B_t := by
    intro n hn
    by_contra hnot
    exact (Polynomial.mem_support_iff.mp hn) (hcoeff_not_mem n hnot)
  have hdeg : P.natDegree ≤ L₀ := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    apply hcoeff_not_mem N
    intro hmem
    exact Nat.not_le_of_gt hN (hB_le N hmem)
  have hann : ∀ ν : Fin k, ∑ x ∈ B_t, P.coeff x * χ (((ν.val * x : ℕ) : ZMod d)) = 0 := by
    intro ν
    have h0 := congrFun hα_ker ν
    change ∑ x : B_t, α x * χ (((ν.val * x.1 : ℕ) : ZMod d)) = 0 at h0
    rw [← Finset.sum_coe_sort B_t]
    refine Eq.trans ?_ h0
    apply Finset.sum_congr rfl
    intro x _
    rw [hcoeff_mem x]
  have hker_dim :
      finrank E (LinearMap.ker (Polynomial.aeval (cyclicChannelShift E d q 1) P)) ≤ q * L₀ :=
    (cyclicChannelShift_aeval_ker_finrank_le hP_ne).trans (Nat.mul_le_mul_left q hdeg)
  exact ⟨P, hP_ne, hdeg, hsupp, hann, hker_dim⟩

/-! ### Step 4: Two-Stage Sumset Recurrence Rank Bound -/

/-- Rewriting `Polynomial.aeval R P` as a sum over any finite superset `S` of `P.support`. -/
lemma aeval_endomorphism_eq_sum_of_support_subset
    {E V : Type*} [Field E] [AddCommGroup V] [Module E V]
    (R : V →ₗ[E] V) (P : Polynomial E) (S : Finset ℕ)
    (hsupp : ∀ n ∈ P.support, n ∈ S) :
    Polynomial.aeval R P = ∑ x ∈ S, P.coeff x • (R ^ x) := by
  let N := max (P.natDegree + 1) (S.sup id + 1)
  have hdegN : P.natDegree < N := lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
  rw [Polynomial.aeval_eq_sum_range' hdegN]
  symm
  apply Finset.sum_subset
  · intro x hx
    rw [Finset.mem_range]
    have hle : x ≤ S.sup id := Finset.le_sup (f := id) hx
    omega
  · intro x _ hxS
    have hc0 : P.coeff x = 0 := by
      by_contra hne
      exact hxS (hsupp x (Polynomial.mem_support_iff.mpr hne))
    rw [hc0, zero_smul]

/-- Transporting the cyclic polynomial kernel bound from `ZMod d → Fin q → E` to `ColumnAmbient H`. -/
lemma columnAmbient_aeval_ker_finrank_le
    {E A : Type*} [Field E] [AddCommGroup A] [Module E A] [FiniteDimensional E A]
    {d : ℕ} [NeZero d] (H : Submodule E (ZMod d → A))
    {P : Polynomial E} (hP : P ≠ 0) :
    finrank E (LinearMap.ker
      (Polynomial.aeval (channelRotation (F := E) (I := Unit) (A := H) (1 : ZMod d)) P)) ≤
      finrank E H * P.natDegree := by
  let q := finrank E H
  let bH := Module.finBasis E H
  let Φ : ColumnAmbient H ≃ₗ[E] (ZMod d → Fin q → E) :=
    { toFun := fun x u => bH.equivFun (x () u)
      invFun := fun y _ u => bH.equivFun.symm (y u)
      left_inv := fun x => by funext u c; exact bH.equivFun.symm_apply_apply (x u c)
      right_inv := fun y => by funext c; exact bH.equivFun.apply_symm_apply (y c)
      map_add' := fun x y => by funext c; exact map_add bH.equivFun (x () c) (y () c)
      map_smul' := fun r x => by funext c; exact map_smul bH.equivFun r (x () c) }
  let R := channelRotation (F := E) (I := Unit) (A := H) (1 : ZMod d)
  let T := cyclicChannelShift E d q 1
  have hstep1 : ∀ x : ColumnAmbient H, Φ (R x) = T (Φ x) := fun _ => rfl
  have hpow : ∀ (j : ℕ) (x : ColumnAmbient H), Φ ((R ^ j) x) = (T ^ j) (Φ x) := by
    intro j
    induction j with
    | zero => intro x; rfl
    | succ j ih =>
        intro x
        rw [pow_succ, Module.End.mul_apply, ih (R x), hstep1, pow_succ, Module.End.mul_apply]
  have haeval : ∀ x : ColumnAmbient H,
      Φ (Polynomial.aeval R P x) = Polynomial.aeval T P (Φ x) := by
    intro x
    rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, hpow]
  let kerMap : LinearMap.ker (Polynomial.aeval R P) →ₗ[E] LinearMap.ker (Polynomial.aeval T P) :=
    { toFun := fun x => ⟨Φ x.1, by rw [LinearMap.mem_ker, ← haeval, x.2, map_zero]⟩
      map_add' := fun x y => by apply Subtype.ext; exact map_add Φ x.1 y.1
      map_smul' := fun r x => by apply Subtype.ext; exact map_smul Φ r x.1 }
  have hker_inj : Function.Injective kerMap := by
    intro x y hxy
    apply Subtype.ext
    exact Φ.injective (congrArg Subtype.val hxy)
  exact (LinearMap.finrank_le_finrank_of_injective hker_inj).trans
    (cyclicChannelShift_aeval_ker_finrank_le hP)

/-- Iterated subspace sequence `V_0 = W`, `V_{j + 1} = W ⊔ Q_j(V_j)` for a sequence of operators. -/
def sumsetIterSpan {E V : Type*} [Field E] [AddCommGroup V] [Module E V]
    {nS : ℕ} (W : Submodule E V) (Q : Fin nS → (V →ₗ[E] V)) : ℕ → Submodule E V
  | 0 => W
  | j + 1 =>
      if hj : j < nS then W ⊔ (sumsetIterSpan W Q j).map (Q ⟨j, hj⟩)
      else sumsetIterSpan W Q j

/-- Splitting-field core of `SumsetTwoHopRankBoundSpec` given an injective character `χ`. -/
lemma sumsetTwoHopRankBound_splitting
    (E : Type*) [Field E] (d b M₁ M₂ k : ℕ) [NeZero d]
    (χ : AddChar (ZMod d) E) (hχ : Function.Injective χ)
    (p₁ : ZMod d → Fin M₁) (p₂ : ZMod d → Fin M₂)
    (m₁ : Fin M₁) (J₀ : Finset (ZMod d))
    (B : Fin (2 * M₂ - 1) → Finset ℕ)
    (diamB : Fin (2 * M₂ - 1) → ℕ)
    (K₁ K₂ : State d (Fin b → E) →ₗ[E] State d (Fin b → E))
    (hM₂ : 1 ≤ M₂) (hkd : k ≤ d)
    (hdiam_sum : ∑ t : Fin (2 * M₂ - 1), diamB t ≤ d)
    (hshift : HasShiftedMonochromaticSumset p₁ m₁ k J₀ B diamB)
    (hK₁ : ClassUniform p₁ K₁) (hK₂ : ClassUniform p₂ K₂) :
    b * k * (d - ∑ t : Fin (2 * M₂ - 1), diamB t) ≤
      2 * finrank E (LinearMap.range (swapLinear E (d := d) (A := Fin b → E) - K₂.comp K₁)) := by
  classical
  rcases hshift with ⟨hJ₀, hB, hsum⟩
  obtain ⟨f₁, hf₁⟩ := linearClassUniform_of_classUniform p₁ K₁ hK₁
  have hmono_J₀ : ∀ c ∈ J₀, p₁ c = m₁ := by
    intro c hc
    have h0 := hsum c hc (fun _ => 0) (fun t => (hB t).1)
    simpa using h0
  obtain ⟨W, hdimW, hinjW, hwitW⟩ :=
    stackedBandPullbackData E d b M₁ M₂ k χ p₁ p₂ m₁ J₀ K₁ K₂ f₁
      hχ hkd hJ₀ hmono_J₀ hf₁ hK₂
  let nS := 2 * M₂ - 1
  let H := bandRowSpace (b := b) χ p₂ k
  let q := finrank E H
  let R : ColumnAmbient H →ₗ[E] ColumnAmbient H :=
    channelRotation (F := E) (I := Unit) (A := H) (1 : ZMod d)
  have hexP : ∀ t : Fin nS, ∃ P : Polynomial E,
      P ≠ 0 ∧ P.natDegree ≤ diamB t ∧ (∀ n ∈ P.support, n ∈ B t) ∧
      (∀ ν : Fin k, ∑ x ∈ B t, P.coeff x * χ (((ν.val * x : ℕ) : ZMod d)) = 0) := by
    intro t
    obtain ⟨P, hP0, hdeg, hsupp, hann, _⟩ :=
      sumsetAnnihilatingPolynomial d k q (diamB t) E χ (B t) hχ
        (hB t).1 (hB t).2.1 (hB t).2.2
    exact ⟨P, hP0, hdeg, hsupp, hann⟩
  let P : Fin nS → Polynomial E := fun t => (hexP t).choose
  have hP_spec : ∀ t : Fin nS,
      P t ≠ 0 ∧ (P t).natDegree ≤ diamB t ∧ (∀ n ∈ (P t).support, n ∈ B t) ∧
      (∀ ν : Fin k, ∑ x ∈ B t, (P t).coeff x * χ (((ν.val * x : ℕ) : ZMod d)) = 0) :=
    fun t => (hexP t).choose_spec
  let Q : Fin nS → (ColumnAmbient H →ₗ[E] ColumnAmbient H) := fun t => Polynomial.aeval R (P t)
  have hQ_sum : ∀ t : Fin nS, Q t = ∑ x ∈ B t, (P t).coeff x • (R ^ x) :=
    fun t => aeval_endomorphism_eq_sum_of_support_subset R (P t) (B t) (hP_spec t).2.2.1
  have hQ_ker : ∀ t : Fin nS, finrank E (LinearMap.ker (Q t)) ≤ q * diamB t := by
    intro t
    exact (columnAmbient_aeval_ker_finrank_le H (hP_spec t).1).trans
      (Nat.mul_le_mul_left q (hP_spec t).2.1)
  let G : ColumnAmbient H →ₗ[E] (J₀ → ZMod d → Fin b → E) :=
    LinearMap.pi fun c => (f₁ m₁).comp ((rotLinear E c.1).comp (columnAmbientEmbed H))
  have hinjG : ∀ w ∈ W, G w = 0 → w = 0 := by
    intro w hw hGw
    apply hinjW w hw
    intro c hc
    exact congrFun hGw ⟨c, hc⟩
  let SpanShifts : ℕ → Submodule E (ColumnAmbient H) := fun j =>
    Submodule.span E { y : ColumnAmbient H | ∃ w ∈ W, ∃ bvec : Fin nS → ℕ,
      (∀ i, bvec i ∈ B i) ∧
      (∀ i : Fin nS, j ≤ i.val → bvec i = 0) ∧
      y = channelRotation (F := E) (∑ i : Fin nS, (bvec i : ZMod d)) w }
  have hW_le : ∀ j : ℕ, W ≤ SpanShifts j := by
    intro j w hw
    apply Submodule.subset_span
    refine ⟨w, hw, fun _ => 0, fun i => (hB i).1, fun _ _ => rfl, ?_⟩
    funext u c
    simp [channelRotation]
  have hmap_le : ∀ {j : ℕ} (hj : j < nS),
      (SpanShifts j).map (Q ⟨j, hj⟩) ≤ SpanShifts (j + 1) := by
    intro j hj
    let t0 : Fin nS := ⟨j, hj⟩
    rw [Submodule.map_le_iff_le_comap]
    apply Submodule.span_le.mpr
    rintro y ⟨w, hw, bvec, hb_mem, hb_zero, rfl⟩
    change Q t0 _ ∈ SpanShifts (j + 1)
    rw [hQ_sum t0, LinearMap.sum_apply]
    apply Submodule.sum_mem
    intro x hx
    rw [LinearMap.smul_apply]
    apply Submodule.smul_mem
    apply Submodule.subset_span
    let bvec' : Fin nS → ℕ := Function.update bvec t0 x
    refine ⟨w, hw, bvec', ?_, ?_, ?_⟩
    · intro i
      by_cases hi : i = t0
      · subst hi; simpa [bvec'] using hx
      · simp [bvec', hi, hb_mem i]
    · intro i hi
      have hne : i ≠ t0 := by
        intro heq
        have : i.val = j := congrArg Fin.val heq
        omega
      simp only [bvec', Function.update_of_ne hne]
      exact hb_zero i (by omega)
    · rw [channelRotation_pow, channelRotation_add]
      congr 1
      have hbt0 : bvec t0 = 0 := hb_zero t0 (le_refl j)
      have hsum_upd : ∑ i : Fin nS, (bvec' i : ZMod d) =
          (x : ZMod d) + ∑ i : Fin nS, (bvec i : ZMod d) := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ t0)]
        conv_rhs => rw [← Finset.add_sum_erase _ _ (Finset.mem_univ t0)]
        simp only [bvec', Function.update_self, hbt0, Nat.cast_zero, zero_add]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        have hne : i ≠ t0 := Finset.ne_of_mem_erase hi
        simp [hne]
      rw [hsum_upd, mul_one]
  have hker_le : ∀ {j : ℕ} (hj : j < nS),
      (SpanShifts j).map (Q ⟨j, hj⟩) ≤ LinearMap.ker G := by
    intro j hj
    let t0 : Fin nS := ⟨j, hj⟩
    have hle : SpanShifts j ≤ LinearMap.ker (G.comp (Q t0)) := by
      apply Submodule.span_le.mpr
      rintro y ⟨w, hw, bvec, hb_mem, hb_zero, rfl⟩
      change G (Q t0 (channelRotation (F := E) (∑ i : Fin nS, (bvec i : ZMod d)) w)) = 0
      obtain ⟨u, hu⟩ := hwitW w hw
      let s : ZMod d := ∑ i : Fin nS, (bvec i : ZMod d)
      ext c row l
      rw [hQ_sum t0]
      simp only [G, LinearMap.pi_apply, LinearMap.comp_apply, rotLinear_apply,
        LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      have hterm : ∀ x ∈ B t0,
          f₁ m₁ (rot c.1 (columnAmbientEmbed H
            ((R ^ x) (channelRotation (F := E) s w)))) row l =
          ∑ ν : Fin k, χ (((ν.val * x : ℕ) : ZMod d)) *
            (χ ((ν.val : ZMod d) * (c.1 + s)) * u ν row l) := by
        intro x hx
        rw [channelRotation_pow, channelRotation_add, columnAmbientEmbed_rotation, rot_rot]
        let bvec' : Fin nS → ℕ := Function.update bvec t0 x
        have hb'_mem : ∀ i, bvec' i ∈ B i := by
          intro i
          by_cases hi : i = t0
          · subst hi; simpa [bvec'] using hx
          · simp [bvec', hi, hb_mem i]
        have hbt0 : bvec t0 = 0 := hb_zero t0 (le_refl j)
        have hsum_upd : ∑ i : Fin nS, (bvec' i : ZMod d) = (x : ZMod d) + s := by
          dsimp [s]
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ t0)]
          conv_rhs => rw [← Finset.add_sum_erase _ _ (Finset.mem_univ t0)]
          simp only [bvec', Function.update_self, hbt0, Nat.cast_zero, zero_add]
          congr 1
          apply Finset.sum_congr rfl
          intro i hi
          simp [Finset.ne_of_mem_erase hi]
        have hcol_eq : c.1 + ((x : ZMod d) * 1 + s) =
            c.1 + ∑ i : Fin nS, (bvec' i : ZMod d) := by
          rw [hsum_upd, mul_one]
        have hp₁_eq : p₁ (c.1 + ((x : ZMod d) * 1 + s)) = m₁ := by
          rw [hcol_eq]
          exact hsum c.1 c.2 bvec' hb'_mem
        have hK := congrFun (congrFun (congrFun hu row) (c.1 + ((x : ZMod d) * 1 + s))) l
        rw [hf₁, hp₁_eq] at hK
        change f₁ m₁ (rot (c.1 + ((x : ZMod d) * 1 + s)) (columnAmbientEmbed H w)) row l = _
        rw [hK]
        simp only [bandMap_apply]
        apply Finset.sum_congr rfl
        intro ν _
        have hexp : (ν.val : ZMod d) * (c.1 + ((x : ZMod d) * 1 + s)) =
            ((ν.val * x : ℕ) : ZMod d) + (ν.val : ZMod d) * (c.1 + s) := by
          push_cast
          ring
        rw [hexp, χ.map_add_eq_mul, mul_assoc]
      have hsum_rw : ∑ x ∈ B t0, (P t0).coeff x *
          f₁ m₁ (rot c.1 (columnAmbientEmbed H
            ((R ^ x) (channelRotation (F := E) s w)))) row l =
          ∑ x ∈ B t0, (P t0).coeff x *
            (∑ ν : Fin k, χ (((ν.val * x : ℕ) : ZMod d)) *
              (χ ((ν.val : ZMod d) * (c.1 + s)) * u ν row l)) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [hterm x hx]
      rw [hsum_rw]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_eq_zero
      intro ν _
      have hfactor : ∑ x ∈ B t0,
          (P t0).coeff x * (χ (((ν.val * x : ℕ) : ZMod d)) *
            (χ ((ν.val : ZMod d) * (c.1 + s)) * u ν row l)) =
          (∑ x ∈ B t0, (P t0).coeff x * χ (((ν.val * x : ℕ) : ZMod d))) *
            (χ ((ν.val : ZMod d) * (c.1 + s)) * u ν row l) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro x _
        ring
      rw [hfactor, (hP_spec t0).2.2.2 ν, zero_mul]
    rintro _ ⟨y, hy, rfl⟩
    exact hle hy
  have hV_le_span : ∀ j : ℕ, j ≤ nS → sumsetIterSpan W Q j ≤ SpanShifts j := by
    intro j
    induction j with
    | zero => intro _; exact hW_le 0
    | succ j ih =>
        intro hj
        have hj' : j < nS := by omega
        simp only [sumsetIterSpan, hj', ↓reduceDIte]
        exact sup_le (hW_le (j + 1)) ((Submodule.map_mono (ih (by omega))).trans (hmap_le hj'))
  let kerTerm : ℕ → ℕ := fun i =>
    if hi : i < nS then finrank E (LinearMap.ker (Q ⟨i, hi⟩)) else 0
  have hgrow : ∀ j : ℕ, j ≤ nS →
      (j + 1) * finrank E W ≤
        finrank E (sumsetIterSpan W Q j) + ∑ i ∈ Finset.range j, kerTerm i := by
    intro j
    induction j with
    | zero =>
        intro _
        simp only [sumsetIterSpan, zero_add, one_mul, Finset.range_zero, Finset.sum_empty, add_zero]
        exact le_rfl
    | succ j ih =>
        intro hj
        have hj' : j < nS := by omega
        have hprev := ih (by omega)
        have hVnext : sumsetIterSpan W Q (j + 1) =
            W ⊔ (sumsetIterSpan W Q j).map (Q ⟨j, hj'⟩) := by
          simp [sumsetIterSpan, hj']
        have hzero : (sumsetIterSpan W Q j).map (Q ⟨j, hj'⟩) ≤ LinearMap.ker G :=
          (Submodule.map_mono (hV_le_span j (by omega))).trans (hker_le hj')
        have hstep := finrank_growth W (sumsetIterSpan W Q j) (sumsetIterSpan W Q (j + 1))
          (Q ⟨j, hj'⟩) G (hVnext ▸ le_sup_left) (hVnext ▸ le_sup_right) hzero hinjG
        have hkrw : kerTerm j = finrank E (LinearMap.ker (Q ⟨j, hj'⟩)) := by
          simp [kerTerm, hj']
        rw [Finset.sum_range_succ, hkrw]
        nlinarith
  have hg_end := hgrow nS (le_refl nS)
  have hsum_ker : ∑ i ∈ Finset.range nS, kerTerm i ≤ q * ∑ t : Fin nS, diamB t := by
    have heq : ∑ i ∈ Finset.range nS, kerTerm i =
        ∑ t : Fin nS, finrank E (LinearMap.ker (Q t)) := by
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro t _
      simp [kerTerm, t.isLt]
    rw [heq, Finset.mul_sum]
    exact Finset.sum_le_sum fun t _ => hQ_ker t
  have hVnS_le : finrank E (sumsetIterSpan W Q nS) ≤ d * q :=
    (sumsetIterSpan W Q nS).finrank_le.trans_eq (columnAmbient_finrank H)
  have hnS_succ : nS + 1 = 2 * M₂ := by omega
  have hcomb1 : (2 * M₂) * finrank E W ≤ q * (d + ∑ t : Fin nS, diamB t) := by
    have h1 : (nS + 1) * finrank E W ≤ d * q + q * ∑ t : Fin nS, diamB t :=
      hg_end.trans (Nat.add_le_add hVnS_le hsum_ker)
    rw [hnS_succ] at h1
    nlinarith
  have hq_le : q ≤ M₂ * k * b := by
    have h := bandRowSpace_finrank_le (b := b) χ p₂ k
    simpa [q, H] using h
  have hcomb2 : M₂ * (2 * finrank E W) ≤ M₂ * (b * k * (d + ∑ t : Fin nS, diamB t)) := by
    have hmul := Nat.mul_le_mul_right (d + ∑ t : Fin nS, diamB t) hq_le
    have h2 := hcomb1.trans hmul
    nlinarith
  have h2W : 2 * finrank E W ≤ b * k * (d + ∑ t : Fin nS, diamB t) :=
    Nat.le_of_mul_le_mul_left hcomb2 (by omega : 0 < M₂)
  let rE := finrank E (LinearMap.range (swapLinear E (d := d) (A := Fin b → E) - K₂.comp K₁))
  change b * k * (d - ∑ t : Fin nS, diamB t) ≤ 2 * rE
  change b * k * d ≤ finrank E W + rE at hdimW
  have hsplit : d - ∑ t : Fin nS, diamB t + ∑ t : Fin nS, diamB t = d :=
    Nat.sub_add_cancel hdiam_sum
  have hsplit_mul : b * k * (d - ∑ t : Fin nS, diamB t) + b * k * ∑ t : Fin nS, diamB t =
      b * k * d := by
    rw [← Nat.mul_add, hsplit]
  have hadd : b * k * (d + ∑ t : Fin nS, diamB t) =
      b * k * d + b * k * ∑ t : Fin nS, diamB t := Nat.mul_add _ _ _
  nlinarith

/-- Proof of `SumsetTwoHopRankBoundSpec` over any field `F` with `(d : F) ≠ 0`. -/
theorem sumsetTwoHopRankBound : SumsetTwoHopRankBoundSpec := by
  intro F _ d b M₁ M₂ k _ p₁ p₂ m₁ J₀ B diamB K₁ K₂ hd _ hM₂ _ hkd hdiam_sum hshift hK₁ hK₂
  let r := finrank F (LinearMap.range (swapLinear F (d := d) (A := Fin b → F) - K₂.comp K₁))
  have hpart1 : b * k * (d - ∑ t : Fin (2 * M₂ - 1), diamB t) ≤ 2 * r := by
    let dn : ℕ+ := ⟨d, NeZero.pos d⟩
    let ψ := AddChar.primitiveZModChar dn F hd
    let E := CyclotomicField ψ.n F
    let χ : AddChar (ZMod d) E := ψ.char
    have hχ : Function.Injective χ := by
      intro a c hac
      have hz : χ (a - c) = 1 := by
        calc
          χ (a - c) = χ a * χ (-c) := by rw [sub_eq_add_neg, χ.map_add_eq_mul]
          _ = χ c * χ (-c) := by rw [hac]
          _ = 1 := by rw [← χ.map_add_eq_mul, add_neg_cancel, χ.map_zero_eq_one]
      exact sub_eq_zero.mp ((ψ.prim.zmod_char_eq_one_iff d (a - c)).mp hz)
    let K₁' := stateExtension E K₁
    let K₂' := stateExtension E K₂
    have hE := sumsetTwoHopRankBound_splitting E d b M₁ M₂ k χ hχ p₁ p₂ m₁ J₀ B diamB K₁' K₂'
      hM₂ hkd hdiam_sum hshift
      (stateExtension_classUniform p₁ K₁ hK₁)
      (stateExtension_classUniform p₂ K₂ hK₂)
    have hr := stateExtension_rank_le (E := E)
      (swapLinear F (d := d) (A := Fin b → F) - K₂.comp K₁)
    rw [stateExtension_sub, stateExtension_swap, stateExtension_comp] at hr
    exact hE.trans (Nat.mul_le_mul_left 2 hr)
  refine ⟨hpart1, ?_⟩
  intro hdiam_bound
  have hsum_le : ∑ t : Fin (2 * M₂ - 1), diamB t ≤ (2 * M₂ - 1) * (d / (4 * M₂)) := by
    have h := Finset.sum_le_sum fun t (_ : t ∈ Finset.univ) => hdiam_bound t
    simpa using h
  have h2sum_le : 2 * ∑ t : Fin (2 * M₂ - 1), diamB t ≤ d := by
    have h1 : 2 * ((2 * M₂ - 1) * (d / (4 * M₂))) ≤ (4 * M₂) * (d / (4 * M₂)) := by
      rw [← mul_assoc]
      exact Nat.mul_le_mul_right (d / (4 * M₂)) (by omega : 2 * (2 * M₂ - 1) ≤ 4 * M₂)
    exact (Nat.mul_le_mul_left 2 hsum_le).trans (h1.trans (Nat.mul_div_le d (4 * M₂)))
  have hd_le : d ≤ 2 * (d - ∑ t : Fin (2 * M₂ - 1), diamB t) := by omega
  have hmul := Nat.mul_le_mul_left (b * k) hd_le
  nlinarith

/-! ### Step 5: Iterated Kővári–Sós–Turán Sumset Extraction & Theorem 2B -/

lemma descFactorial_le_pow_nat (W m : ℕ) : W.descFactorial m ≤ W ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Nat.descFactorial_succ, pow_succ']
      exact Nat.mul_le_mul (Nat.sub_le W m) ih

lemma pow_sub_le_descFactorial_nat (h k m : ℕ) (hm : m ≤ k + 1) :
    (h - k) ^ m ≤ h.descFactorial m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Nat.descFactorial_succ, pow_succ']
      exact Nat.mul_le_mul (by omega : h - k ≤ h - m) (ih (by omega))

/-- One-step Kővári–Sós–Turán / interval-splitting shift-subset extraction in `ℕ`. -/
lemma single_step_sumset_extract
    {d M₂ k : ℕ} (hM₂ : 1 ≤ M₂) (hk : 1 ≤ k) (hd4 : 4 * M₂ ≤ d)
    (A : Finset ℕ) (hA_range : ∀ x ∈ A, x < d)
    (hA_large : 16 * M₂ * (k + 1) ≤ A.card) :
    ∃ (B₀ : Finset ℕ) (A' : Finset ℕ),
      B₀.card = k + 1 ∧
      (∀ b ∈ B₀, b ≤ d / (4 * M₂)) ∧
      A' ⊆ A ∧
      (∀ x ∈ A', ∀ b ∈ B₀, x + b ∈ A) ∧
      A.card ^ (k + 2) ≤ (16 * M₂) ^ (k + 2) * d ^ (k + 1) * A'.card := by
  classical
  let L₀ := d / (4 * M₂)
  let W := L₀ + 1
  have hW_pos : 0 < W := Nat.succ_pos L₀
  have hW_le_d : W ≤ d := by
    have h4L : 4 * L₀ ≤ d :=
      (Nat.mul_le_mul_right L₀ (by omega : 4 ≤ 4 * M₂)).trans (Nat.mul_div_le d (4 * M₂))
    omega
  have hd_lt_mulW : d < (4 * M₂) * W := by
    have hdiv := Nat.div_add_mod d (4 * M₂)
    have hmod := Nat.mod_lt d (by omega : 0 < 4 * M₂)
    dsimp [W, L₀]
    nlinarith
  let I : ℕ → Finset ℕ := fun q => A.filter (fun x => x / W = q)
  have hA_part : A.card = ∑ q ∈ Finset.range (4 * M₂), (I q).card := by
    have hmaps : ∀ x ∈ A, x / W ∈ Finset.range (4 * M₂) := by
      intro x hx
      rw [Finset.mem_range]
      have hxd : x < (4 * M₂) * W := (hA_range x hx).trans hd_lt_mulW
      by_contra hge
      have hmul : (4 * M₂) * W ≤ (x / W) * W := Nat.mul_le_mul_right W (by omega)
      have hle : (x / W) * W ≤ x := by
        rw [mul_comm]
        exact Nat.mul_div_le x W
      omega
    exact Finset.card_eq_sum_card_fiberwise hmaps
  have hex_q : ∃ q₀ ∈ Finset.range (4 * M₂), A.card ≤ (4 * M₂) * (I q₀).card := by
    by_contra hall
    have hlt : ∀ q ∈ Finset.range (4 * M₂), (4 * M₂) * (I q).card < A.card := by
      intro q hq
      by_contra hge
      exact hall ⟨q, hq, by omega⟩
    have hne : (Finset.range (4 * M₂)).Nonempty := ⟨0, Finset.mem_range.mpr (by omega)⟩
    have hsum_lt := Finset.sum_lt_sum_of_nonempty hne hlt
    rw [← Finset.mul_sum, ← hA_part, Finset.sum_const, Finset.card_range, smul_eq_mul] at hsum_lt
    omega
  obtain ⟨q₀, _, hIq₀⟩ := hex_q
  let I₀ := I q₀
  let a := I₀.card
  have ha_ge : 4 * (k + 1) ≤ a := by
    have : 4 * M₂ * (4 * (k + 1)) ≤ 4 * M₂ * a := by
      calc
        4 * M₂ * (4 * (k + 1)) = 16 * M₂ * (k + 1) := by ring
        _ ≤ A.card := hA_large
        _ ≤ 4 * M₂ * a := hIq₀
    exact Nat.le_of_mul_le_mul_left this (by omega : 0 < 4 * M₂)
  let h := a / 2
  have hk1_le_h : k + 1 ≤ h := by omega
  have ha_le_4h : a ≤ 4 * h := by omega
  have ha_le_4sub : a ≤ 4 * (h - k) := by omega
  let e : Fin a ↪o ℕ := I₀.orderEmbOfFin rfl
  have he_mem_I₀ : ∀ u : Fin a, e u ∈ I₀ := fun u => Finset.orderEmbOfFin_mem I₀ rfl u
  have he_mem_A : ∀ u : Fin a, e u ∈ A := fun u => (Finset.mem_filter.mp (he_mem_I₀ u)).1
  have he_div : ∀ u : Fin a, (e u) / W = q₀ := fun u => (Finset.mem_filter.mp (he_mem_I₀ u)).2
  have hdiff_lt_W : ∀ u v : Fin a, u ≤ v → e v - e u < W := by
    intro u v huv
    have he_le : e u ≤ e v := e.monotone huv
    have hdu := Nat.div_add_mod (e u) W
    have hdv := Nat.div_add_mod (e v) W
    have hmv := Nat.mod_lt (e v) hW_pos
    rw [he_div u] at hdu
    rw [he_div v] at hdv
    omega
  let loIdx : Fin (a - h) → Fin a := fun i => ⟨i.val, by omega⟩
  let hiIdx : Fin h → Fin a := fun j => ⟨a - h + j.val, by omega⟩
  let g : Fin (a - h) → Fin h → ℕ := fun i j => e (hiIdx j) - e (loIdx i)
  have hg_inj : ∀ i : Fin (a - h), Function.Injective (g i) := by
    intro i j₁ j₂ hj
    dsimp [g] at hj
    have hle₁ : e (loIdx i) ≤ e (hiIdx j₁) := e.monotone (by change i.val ≤ a - h + j₁.val; omega)
    have hle₂ : e (loIdx i) ≤ e (hiIdx j₂) := e.monotone (by change i.val ≤ a - h + j₂.val; omega)
    have he_eq : e (hiIdx j₁) = e (hiIdx j₂) := by omega
    have hidx_eq : hiIdx j₁ = hiIdx j₂ := e.injective he_eq
    have hval_eq : a - h + j₁.val = a - h + j₂.val := congrArg Fin.val hidx_eq
    exact Fin.ext (by omega)
  let U : Fin (a - h) → Finset ℕ := fun i => Finset.univ.image (g i)
  have hU_card : ∀ i : Fin (a - h), (U i).card = h := by
    intro i
    rw [Finset.card_image_of_injective _ (hg_inj i), Finset.card_fin]
  have hU_sub : ∀ i : Fin (a - h), U i ⊆ Finset.range W := by
    intro i b hb
    rcases Finset.mem_image.mp hb with ⟨j, _, rfl⟩
    rw [Finset.mem_range]
    exact hdiff_lt_W (loIdx i) (hiIdx j) (by change i.val ≤ a - h + j.val; omega)
  have hU_add_mem : ∀ i : Fin (a - h), ∀ b ∈ U i, e (loIdx i) + b ∈ A := by
    intro i b hb
    rcases Finset.mem_image.mp hb with ⟨j, _, rfl⟩
    dsimp [g]
    have hle : e (loIdx i) ≤ e (hiIdx j) := e.monotone (by change i.val ≤ a - h + j.val; omega)
    rw [Nat.add_sub_cancel' hle]
    exact he_mem_A (hiIdx j)
  let P_set : Finset (Finset ℕ) := (Finset.range W).powersetCard (k + 1)
  have hP_card : P_set.card = W.choose (k + 1) := by
    rw [Finset.card_powersetCard, Finset.card_range]
  let A_B : Finset ℕ → Finset ℕ := fun B₀ => A.filter (fun x => ∀ b ∈ B₀, x + b ∈ A)
  let N_pairs : ℕ := ∑ i : Fin (a - h),
    (P_set.filter (fun B₀ => ∀ b ∈ B₀, e (loIdx i) + b ∈ A)).card
  have hN_lower : h * h.choose (k + 1) ≤ N_pairs := by
    have h_each : ∀ i : Fin (a - h),
        h.choose (k + 1) ≤ (P_set.filter (fun B₀ => ∀ b ∈ B₀, e (loIdx i) + b ∈ A)).card := by
      intro i
      have hsub_p : (U i).powersetCard (k + 1) ⊆
          P_set.filter (fun B₀ => ∀ b ∈ B₀, e (loIdx i) + b ∈ A) := by
        intro B₀ hB₀
        rw [Finset.mem_powersetCard] at hB₀
        rw [Finset.mem_filter, Finset.mem_powersetCard]
        exact ⟨⟨hB₀.1.trans (hU_sub i), hB₀.2⟩, fun b hb => hU_add_mem i b (hB₀.1 hb)⟩
      calc
        h.choose (k + 1) = ((U i).powersetCard (k + 1)).card := by
          rw [Finset.card_powersetCard, hU_card i]
        _ ≤ (P_set.filter (fun B₀ => ∀ b ∈ B₀, e (loIdx i) + b ∈ A)).card :=
          Finset.card_le_card hsub_p
    have hsum1 : (a - h) * h.choose (k + 1) ≤ N_pairs := by
      have hs := Finset.sum_le_sum (s := Finset.univ) fun (i : Fin (a - h)) _ => h_each i
      simpa using hs
    exact (Nat.mul_le_mul_right _ (by omega : h ≤ a - h)).trans hsum1
  have hN_upper : N_pairs ≤ ∑ B₀ ∈ P_set, (A_B B₀).card := by
    have hrw : N_pairs = ∑ B₀ ∈ P_set,
        (Finset.univ.filter (fun i : Fin (a - h) => ∀ b ∈ B₀, e (loIdx i) + b ∈ A)).card := by
      dsimp [N_pairs]
      simp_rw [Finset.card_filter]
      exact Finset.sum_comm
    rw [hrw]
    apply Finset.sum_le_sum
    intro B₀ _
    let f_emb : Fin (a - h) → ℕ := fun i => e (loIdx i)
    have hf_inj : Function.Injective f_emb := by
      intro i₁ i₂ hi
      have h1 := e.injective hi
      exact Fin.ext (by simpa [loIdx] using congrArg Fin.val h1)
    have himg_sub : (Finset.univ.filter
        (fun i : Fin (a - h) => ∀ b ∈ B₀, e (loIdx i) + b ∈ A)).image f_emb ⊆ A_B B₀ := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
      rw [Finset.mem_filter] at hi ⊢
      exact ⟨he_mem_A (loIdx i), hi.2⟩
    rw [← Finset.card_image_of_injective _ hf_inj]
    exact Finset.card_le_card himg_sub
  have hchoose_pos : 0 < h * h.choose (k + 1) :=
    Nat.mul_pos (by omega) (Nat.choose_pos hk1_le_h)
  have hP_ne : P_set.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have h0 : ∑ B₀ ∈ P_set, (A_B B₀).card = 0 := by simp [hemp]
    have := hN_lower.trans hN_upper
    omega
  have hex_B₀ : ∃ B₀ ∈ P_set, h * h.choose (k + 1) ≤ P_set.card * (A_B B₀).card := by
    by_contra hall
    have hall' : ∀ B₀ ∈ P_set, P_set.card * (A_B B₀).card < h * h.choose (k + 1) := by
      intro B₀ hB₀
      by_contra hge
      exact hall ⟨B₀, hB₀, by omega⟩
    have hsum_lt := Finset.sum_lt_sum_of_nonempty hP_ne hall'
    rw [← Finset.mul_sum, Finset.sum_const, smul_eq_mul] at hsum_lt
    have hcomb := hN_lower.trans hN_upper
    have hmul := Nat.mul_le_mul_left P_set.card hcomb
    omega
  obtain ⟨B₀, hB₀_mem, hB₀_bound⟩ := hex_B₀
  rw [hP_card] at hB₀_bound
  rw [Finset.mem_powersetCard] at hB₀_mem
  have hB₀_le : ∀ b ∈ B₀, b ≤ L₀ := by
    intro b hb
    have hbr := Finset.mem_range.mp (hB₀_mem.1 hb)
    omega
  refine ⟨B₀, A_B B₀, hB₀_mem.2, hB₀_le, Finset.filter_subset _ _, ?_, ?_⟩
  · intro x hx
    exact (Finset.mem_filter.mp hx).2
  · have h1 : (h - k) ^ (k + 1) ≤ (k + 1).factorial * h.choose (k + 1) := by
      rw [← Nat.descFactorial_eq_factorial_mul_choose]
      exact pow_sub_le_descFactorial_nat h k (k + 1) le_rfl
    have h2 : (k + 1).factorial * W.choose (k + 1) ≤ d ^ (k + 1) := by
      rw [← Nat.descFactorial_eq_factorial_mul_choose]
      exact (descFactorial_le_pow_nat W (k + 1)).trans (Nat.pow_le_pow_left hW_le_d (k + 1))
    have hstep_nat : h * (h - k) ^ (k + 1) ≤ d ^ (k + 1) * (A_B B₀).card := by
      calc
        h * (h - k) ^ (k + 1)
            ≤ h * ((k + 1).factorial * h.choose (k + 1)) := Nat.mul_le_mul_left h h1
        _ = (k + 1).factorial * (h * h.choose (k + 1)) := by ring
        _ ≤ (k + 1).factorial * (W.choose (k + 1) * (A_B B₀).card) :=
            Nat.mul_le_mul_left _ hB₀_bound
        _ = ((k + 1).factorial * W.choose (k + 1)) * (A_B B₀).card := by ring
        _ ≤ d ^ (k + 1) * (A_B B₀).card := Nat.mul_le_mul_right _ h2
    have hAh : A.card ≤ 16 * M₂ * h := by
      calc
        A.card ≤ 4 * M₂ * a := hIq₀
        _ ≤ 4 * M₂ * (4 * h) := Nat.mul_le_mul_left _ ha_le_4h
        _ = 16 * M₂ * h := by ring
    have hAsub : A.card ≤ 16 * M₂ * (h - k) := by
      calc
        A.card ≤ 4 * M₂ * a := hIq₀
        _ ≤ 4 * M₂ * (4 * (h - k)) := Nat.mul_le_mul_left _ ha_le_4sub
        _ = 16 * M₂ * (h - k) := by ring
    calc
      A.card ^ (k + 2)
          = A.card * A.card ^ (k + 1) := by rw [pow_succ']
      _ ≤ (16 * M₂ * h) * (16 * M₂ * (h - k)) ^ (k + 1) :=
          Nat.mul_le_mul hAh (Nat.pow_le_pow_left hAsub (k + 1))
      _ = (16 * M₂) ^ (k + 2) * (h * (h - k) ^ (k + 1)) := by
          rw [mul_pow, pow_succ']
          ring
      _ ≤ (16 * M₂) ^ (k + 2) * (d ^ (k + 1) * (A_B B₀).card) :=
          Nat.mul_le_mul_left _ hstep_nat
      _ = (16 * M₂) ^ (k + 2) * d ^ (k + 1) * (A_B B₀).card := by ring

/-- Recurrence factor `R_0 = M₁`, `R_{t + 1} = (16 M₂ R_t)^(k + 2)` governing iterated sumset size. -/
def sumsetRecFactor (M₁ M₂ k : ℕ) : ℕ → ℕ
  | 0 => M₁
  | t + 1 => (16 * M₂ * sumsetRecFactor M₁ M₂ k t) ^ (k + 2)

lemma sumsetRecFactor_pos {M₁ M₂ k : ℕ} (hM₁ : 1 ≤ M₁) (hM₂ : 1 ≤ M₂) (t : ℕ) :
    0 < sumsetRecFactor M₁ M₂ k t := by
  induction t with
  | zero => exact hM₁
  | succ t ih =>
      simp only [sumsetRecFactor]
      exact Nat.pow_pos (by nlinarith)

lemma sumsetRecFactor_mono {M₁ M₂ k : ℕ} (hM₁ : 1 ≤ M₁) (hM₂ : 1 ≤ M₂) :
    Monotone (sumsetRecFactor M₁ M₂ k) := by
  apply monotone_nat_of_le_succ
  intro t
  simp only [sumsetRecFactor]
  have hpos := sumsetRecFactor_pos (k := k) hM₁ hM₂ t
  have hbase : 1 ≤ 16 * M₂ * sumsetRecFactor M₁ M₂ k t := by nlinarith
  calc
    sumsetRecFactor M₁ M₂ k t ≤ 16 * M₂ * sumsetRecFactor M₁ M₂ k t := by nlinarith
    _ = (16 * M₂ * sumsetRecFactor M₁ M₂ k t) ^ 1 := (pow_one _).symm
    _ ≤ (16 * M₂ * sumsetRecFactor M₁ M₂ k t) ^ (k + 2) :=
        Nat.pow_le_pow_right hbase (by omega)

lemma sumsetRecFactor_upper {M₁ M₂ k : ℕ} (hM₁ : 1 ≤ M₁) (hM₂ : 1 ≤ M₂) (t : ℕ) :
    sumsetRecFactor M₁ M₂ k t ≤ (16 * M₁ * M₂) ^ (3 ^ t * (k + 2) ^ t) := by
  let M₀ := 16 * M₁ * M₂
  have hM₀_ge : 1 ≤ M₀ := by dsimp [M₀]; nlinarith
  induction t with
  | zero =>
      simp only [sumsetRecFactor, pow_zero, mul_one, pow_one]
      nlinarith
  | succ t ih =>
      simp only [sumsetRecFactor]
      have h16 : 16 * M₂ ≤ M₀ := by dsimp [M₀]; nlinarith
      have hprod : 16 * M₂ * sumsetRecFactor M₁ M₂ k t ≤
          M₀ ^ (1 + 3 ^ t * (k + 2) ^ t) := by
        calc
          16 * M₂ * sumsetRecFactor M₁ M₂ k t
              ≤ M₀ ^ 1 * M₀ ^ (3 ^ t * (k + 2) ^ t) := by
                rw [pow_one]
                exact Nat.mul_le_mul h16 ih
          _ = M₀ ^ (1 + 3 ^ t * (k + 2) ^ t) := (pow_add M₀ 1 _).symm
      have hexp : (1 + 3 ^ t * (k + 2) ^ t) * (k + 2) ≤
          3 ^ (t + 1) * (k + 2) ^ (t + 1) := by
        have hpos : 1 ≤ 3 ^ t * (k + 2) ^ t :=
          Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.pow_pos (by omega))
        calc
          (1 + 3 ^ t * (k + 2) ^ t) * (k + 2)
              ≤ (3 * (3 ^ t * (k + 2) ^ t)) * (k + 2) :=
                Nat.mul_le_mul_right _ (by omega)
          _ = 3 ^ (t + 1) * (k + 2) ^ (t + 1) := by
                rw [pow_succ', pow_succ']
                ring
      calc
        (16 * M₂ * sumsetRecFactor M₁ M₂ k t) ^ (k + 2)
            ≤ (M₀ ^ (1 + 3 ^ t * (k + 2) ^ t)) ^ (k + 2) := Nat.pow_le_pow_left hprod (k + 2)
        _ = M₀ ^ ((1 + 3 ^ t * (k + 2) ^ t) * (k + 2)) := (pow_mul M₀ _ _).symm
        _ ≤ M₀ ^ (3 ^ (t + 1) * (k + 2) ^ (t + 1)) := Nat.pow_le_pow_right hM₀_ge hexp

/-- `n`-step iterated extraction in `ℕ` starting from a subset `A₀ ⊆ Finset.range d`. -/
lemma iterated_sumset_extract_from_finset
    {d M₁ M₂ k : ℕ} (hM₁ : 1 ≤ M₁) (hM₂ : 1 ≤ M₂) (hk : 1 ≤ k) (hd4 : 4 * M₂ ≤ d)
    (A₀ : Finset ℕ) (hA₀_range : ∀ x ∈ A₀, x < d)
    (hA₀_card : d ≤ M₁ * A₀.card) :
    ∀ n : ℕ,
      16 * M₂ * (k + 1) * sumsetRecFactor M₁ M₂ k n ≤ d →
      ∃ (A_n : Finset ℕ) (B : Fin n → Finset ℕ),
        A_n ⊆ A₀ ∧
        d ≤ sumsetRecFactor M₁ M₂ k n * A_n.card ∧
        (∀ t : Fin n, (B t).card = k + 1 ∧ ∀ b ∈ B t, b ≤ d / (4 * M₂)) ∧
        (∀ x ∈ A_n, ∀ b : Fin n → ℕ, (∀ t, b t ∈ B t) → x + ∑ t : Fin n, b t ∈ A₀) := by
  intro n
  induction n with
  | zero =>
      intro _
      refine ⟨A₀, Fin.elim0, Finset.Subset.refl A₀, hA₀_card, fun t => Fin.elim0 t, ?_⟩
      intro x hx _ _
      simpa using hx
  | succ n ih =>
      intro hbound
      have hmon := sumsetRecFactor_mono (k := k) hM₁ hM₂ (Nat.le_succ n)
      have hbound_prev : 16 * M₂ * (k + 1) * sumsetRecFactor M₁ M₂ k n ≤ d :=
        (Nat.mul_le_mul_left _ hmon).trans hbound
      obtain ⟨A_n, B_prev, hA_sub, hA_card, hB_prev, hsum_prev⟩ := ih hbound_prev
      have hRn_pos : 0 < sumsetRecFactor M₁ M₂ k n := sumsetRecFactor_pos hM₁ hM₂ n
      have hA_large : 16 * M₂ * (k + 1) ≤ A_n.card := by
        have hmul : sumsetRecFactor M₁ M₂ k n * (16 * M₂ * (k + 1)) ≤
            sumsetRecFactor M₁ M₂ k n * A_n.card := by
          calc
            sumsetRecFactor M₁ M₂ k n * (16 * M₂ * (k + 1))
                = 16 * M₂ * (k + 1) * sumsetRecFactor M₁ M₂ k n := by ring
            _ ≤ d := hbound_prev
            _ ≤ sumsetRecFactor M₁ M₂ k n * A_n.card := hA_card
        exact Nat.le_of_mul_le_mul_left hmul hRn_pos
      obtain ⟨B_last, A_next, hBlast_card, hBlast_le, hAnext_sub, hAnext_add, hAnext_card⟩ :=
        single_step_sumset_extract hM₂ hk hd4 A_n
          (fun x hx => hA₀_range x (hA_sub hx)) hA_large
      have hd_pos : 0 < d := by omega
      have hd_next : d ≤ sumsetRecFactor M₁ M₂ k (n + 1) * A_next.card := by
        have hpow_le : d ^ (k + 1) * d ≤
            d ^ (k + 1) * (sumsetRecFactor M₁ M₂ k (n + 1) * A_next.card) := by
          calc
            d ^ (k + 1) * d = d ^ (k + 2) := (pow_succ d (k + 1)).symm
            _ ≤ (sumsetRecFactor M₁ M₂ k n * A_n.card) ^ (k + 2) :=
                Nat.pow_le_pow_left hA_card (k + 2)
            _ = sumsetRecFactor M₁ M₂ k n ^ (k + 2) * A_n.card ^ (k + 2) := mul_pow _ _ _
            _ ≤ sumsetRecFactor M₁ M₂ k n ^ (k + 2) *
                  ((16 * M₂) ^ (k + 2) * d ^ (k + 1) * A_next.card) :=
                Nat.mul_le_mul_left _ hAnext_card
            _ = d ^ (k + 1) *
                  ((16 * M₂ * sumsetRecFactor M₁ M₂ k n) ^ (k + 2) * A_next.card) := by
                rw [mul_pow]
                ring
            _ = d ^ (k + 1) * (sumsetRecFactor M₁ M₂ k (n + 1) * A_next.card) := rfl
        exact Nat.le_of_mul_le_mul_left hpow_le (Nat.pow_pos hd_pos)
      let B_all : Fin (n + 1) → Finset ℕ := Fin.snoc B_prev B_last
      refine ⟨A_next, B_all, hAnext_sub.trans hA_sub, hd_next, ?_, ?_⟩
      · intro t
        refine Fin.lastCases ?_ ?_ t
        · simpa [B_all] using ⟨hBlast_card, hBlast_le⟩
        · intro i
          simpa [B_all] using hB_prev i
      · intro x hx b hb
        rw [Fin.sum_univ_castSucc]
        have hx_add : x + b (Fin.last n) ∈ A_n := by
          apply hAnext_add x hx
          simpa [B_all] using hb (Fin.last n)
        have h_prev_mem : (x + b (Fin.last n)) + ∑ i : Fin n, b i.castSucc ∈ A₀ := by
          apply hsum_prev (x + b (Fin.last n)) hx_add (fun i => b i.castSucc)
          intro i
          simpa [B_all] using hb i.castSucc
        have hcomm : x + (∑ i : Fin n, b i.castSucc + b (Fin.last n)) =
            (x + b (Fin.last n)) + ∑ i : Fin n, b i.castSucc := by ring
        rwa [hcomm]

/-- Proof of `IteratedKovariSosTuranSumsetSpec`. -/
theorem iteratedKovariSosTuranSumset : IteratedKovariSosTuranSumsetSpec := by
  intro M₁ M₂ hM₁ hM₂
  classical
  let n : ℕ := 2 * M₂ - 1
  have hn_pos : 1 ≤ n := by omega
  have hn_cast : (n : ℝ) = 2 * (M₂ : ℝ) - 1 := by
    dsimp [n]
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * M₂)]
    push_cast
    ring
  let M₀ : ℕ := 16 * M₁ * M₂
  have hM₀_ge16 : 16 ≤ M₀ := by dsimp [M₀]; nlinarith
  have hM₀_gt1 : (1 : ℝ) < (M₀ : ℝ) := by exact_mod_cast (by omega : 1 < M₀)
  have hlogM₀_pos : 0 < Real.log (M₀ : ℝ) := Real.log_pos hM₀_gt1
  let A_exp : ℝ := ((18 ^ n : ℕ) : ℝ) * Real.log (M₀ : ℝ)
  have h18_pos : (0 : ℝ) < ((18 ^ n : ℕ) : ℝ) := by exact_mod_cast (Nat.pow_pos (by omega))
  have hA_pos : 0 < A_exp := mul_pos h18_pos hlogM₀_pos
  let α : ℝ := (1 : ℝ) / (2 * (M₂ : ℝ) - 1)
  have hn_real_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
  have hα_eq : α = (1 : ℝ) / (n : ℝ) := by dsimp [α]; rw [← hn_cast]
  have hα_pos : 0 < α := by rw [hα_eq]; exact div_pos one_pos hn_real_pos
  let C_hi : ℝ := (1 / A_exp) ^ α
  have hChi_pos : 0 < C_hi := Real.rpow_pos_of_pos (div_pos one_pos hA_pos) α
  let c_lo : ℝ := C_hi / 2
  have hclo_pos : 0 < c_lo := half_pos hChi_pos
  have hclo_le : c_lo ≤ C_hi := half_le_self hChi_pos.le
  let D₀ : ℕ := max (4 * M₂) (Nat.ceil (Real.exp (((2 ^ n : ℕ) : ℝ) * A_exp)) + 2)
  refine ⟨c_lo, C_hi, D₀, hclo_pos, hclo_le, ?_⟩
  intro d _ p₁ hdD₀
  have hd4 : 4 * M₂ ≤ d := (le_max_left _ _).trans hdD₀
  have hd_ceil : Nat.ceil (Real.exp (((2 ^ n : ℕ) : ℝ) * A_exp)) + 2 ≤ d :=
    (le_max_right _ _).trans hdD₀
  have hd_exp : Real.exp (((2 ^ n : ℕ) : ℝ) * A_exp) ≤ (d : ℝ) := by
    calc
      Real.exp (((2 ^ n : ℕ) : ℝ) * A_exp)
          ≤ (Nat.ceil (Real.exp (((2 ^ n : ℕ) : ℝ) * A_exp)) : ℝ) :=
            Nat.le_ceil _
      _ ≤ (d : ℝ) := by exact_mod_cast (by omega : Nat.ceil _ ≤ d)
  have hd_real_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  let L : ℝ := Real.log (d : ℝ)
  have hL_ge : ((2 ^ n : ℕ) : ℝ) * A_exp ≤ L := by
    rw [← Real.log_exp (((2 ^ n : ℕ) : ℝ) * A_exp)]
    exact Real.log_le_log (Real.exp_pos _) hd_exp
  have h2n_pos : (0 : ℝ) < ((2 ^ n : ℕ) : ℝ) := by exact_mod_cast (Nat.pow_pos (by omega))
  have hL_pos : 0 < L := lt_of_lt_of_le (mul_pos h2n_pos hA_pos) hL_ge
  have hdiv_ge : (2 : ℝ) ^ n ≤ L / A_exp := by
    rw [le_div_iff₀ hA_pos]
    simpa using hL_ge
  let x : ℝ := C_hi * L ^ α
  have hx_eq : x = (L / A_exp) ^ α := by
    dsimp [x, C_hi]
    rw [← Real.mul_rpow (div_pos one_pos hA_pos).le hL_pos.le, one_div_mul_eq_div]
  have hx_ge2 : 2 ≤ x := by
    rw [hx_eq]
    have hrpow := Real.rpow_le_rpow (by positivity) hdiv_ge hα_pos.le
    have h2 : ((2 : ℝ) ^ n) ^ α = 2 := by
      rw [hα_eq, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
        mul_one_div_cancel hn_real_pos.ne', Real.rpow_one]
    rwa [h2] at hrpow
  let k : ℕ := Nat.floor x
  have hk_pos : 1 ≤ k := Nat.le_floor (by norm_num; linarith)
  have hk_upper : (k : ℝ) ≤ C_hi * L ^ α := Nat.floor_le (by linarith)
  have hk_lower : c_lo * L ^ α ≤ (k : ℝ) := by
    have h1 : x - 1 ≤ (k : ℝ) := (Nat.sub_one_lt_floor x).le
    change (C_hi / 2) * L ^ α ≤ (k : ℝ)
    have h2 : (C_hi / 2) * L ^ α = x / 2 := by dsimp [x]; ring
    linarith
  have hk_pow_le : A_exp * (k : ℝ) ^ n ≤ L := by
    have hkn : (k : ℝ) ^ n ≤ L / A_exp := by
      calc
        (k : ℝ) ^ n ≤ x ^ n := pow_le_pow_left₀ (Nat.cast_nonneg k) (Nat.floor_le (by linarith)) n
        _ = ((L / A_exp) ^ α) ^ n := by rw [hx_eq]
        _ = (L / A_exp) ^ (α * (n : ℝ)) := by
            rw [← Real.rpow_natCast ((L / A_exp) ^ α), ← Real.rpow_mul (div_pos hL_pos hA_pos).le]
        _ = L / A_exp := by rw [hα_eq, one_div_mul_cancel hn_real_pos.ne', Real.rpow_one]
    calc
      A_exp * (k : ℝ) ^ n ≤ A_exp * (L / A_exp) :=
        mul_le_mul_of_nonneg_left hkn hA_pos.le
      _ = L := mul_div_cancel₀ L hA_pos.ne'
  have hM₀_pow_le_d : M₀ ^ (18 ^ n * k ^ n) ≤ d := by
    have hreal : ((M₀ ^ (18 ^ n * k ^ n) : ℕ) : ℝ) ≤ (d : ℝ) := by
      calc
        ((M₀ ^ (18 ^ n * k ^ n) : ℕ) : ℝ)
            = (M₀ : ℝ) ^ (18 ^ n * k ^ n) := by norm_cast
        _ = Real.exp (((18 ^ n * k ^ n : ℕ) : ℝ) * Real.log (M₀ : ℝ)) := by
            rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by positivity), mul_comm]
        _ = Real.exp (A_exp * (k : ℝ) ^ n) := by
            congr 1
            dsimp [A_exp]
            push_cast
            ring
        _ ≤ Real.exp L := Real.exp_le_exp.mpr hk_pow_le
        _ = (d : ℝ) := Real.exp_log hd_real_pos
    exact_mod_cast hreal
  have hrec_bound : 16 * M₂ * (k + 1) * sumsetRecFactor M₁ M₂ k n ≤ d := by
    have hk_add_le : k + 1 ≤ M₀ ^ (k ^ n) := by
      have h2k : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
      have hkn_ge : k ≤ k ^ n := Nat.le_self_pow (by omega : n ≠ 0) k
      calc
        k + 1 ≤ 2 ^ k := h2k
        _ ≤ M₀ ^ k := Nat.pow_le_pow_left (by omega : 2 ≤ M₀) k
        _ ≤ M₀ ^ (k ^ n) := Nat.pow_le_pow_right (by omega : 1 ≤ M₀) hkn_ge
    have hR_le : sumsetRecFactor M₁ M₂ k n ≤ M₀ ^ (9 ^ n * k ^ n) := by
      have h1 := sumsetRecFactor_upper (k := k) hM₁ hM₂ n
      have hk2 : k + 2 ≤ 3 * k := by omega
      have hexp : 3 ^ n * (k + 2) ^ n ≤ 9 ^ n * k ^ n := by
        calc
          3 ^ n * (k + 2) ^ n ≤ 3 ^ n * (3 * k) ^ n :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hk2 n)
          _ = (3 * 3) ^ n * k ^ n := by rw [mul_pow, ← mul_assoc, ← mul_pow]
          _ = 9 ^ n * k ^ n := by norm_num
      exact h1.trans (Nat.pow_le_pow_right (by omega : 1 ≤ M₀) hexp)
    have h16_le : 16 * M₂ ≤ M₀ ^ 1 := by rw [pow_one]; dsimp [M₀]; nlinarith
    have hexp_sum : 1 + k ^ n + 9 ^ n * k ^ n ≤ 18 ^ n * k ^ n := by
      have hkn1 : 1 ≤ k ^ n := Nat.one_le_pow n k hk_pos
      have h9ge : 9 ≤ 9 ^ n := by
        calc
          9 = 9 ^ 1 := (pow_one 9).symm
          _ ≤ 9 ^ n := Nat.pow_le_pow_right (by omega) hn_pos
      have h2ge : 2 ≤ 2 ^ n := by
        calc
          2 = 2 ^ 1 := (pow_one 2).symm
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn_pos
      have h2_9 : 2 + 9 ^ n ≤ 18 ^ n := by
        calc
          2 + 9 ^ n ≤ 2 * 9 ^ n := by omega
          _ ≤ 2 ^ n * 9 ^ n := Nat.mul_le_mul_right _ h2ge
          _ = (2 * 9) ^ n := (mul_pow 2 9 n).symm
          _ = 18 ^ n := by norm_num
      calc
        1 + k ^ n + 9 ^ n * k ^ n
            ≤ k ^ n + k ^ n + 9 ^ n * k ^ n := by omega
        _ = (2 + 9 ^ n) * k ^ n := by ring
        _ ≤ 18 ^ n * k ^ n := Nat.mul_le_mul_right _ h2_9
    calc
      16 * M₂ * (k + 1) * sumsetRecFactor M₁ M₂ k n
          ≤ M₀ ^ 1 * M₀ ^ (k ^ n) * M₀ ^ (9 ^ n * k ^ n) :=
            Nat.mul_le_mul (Nat.mul_le_mul h16_le hk_add_le) hR_le
      _ = M₀ ^ (1 + k ^ n + 9 ^ n * k ^ n) := by rw [← pow_add, ← pow_add]
      _ ≤ M₀ ^ (18 ^ n * k ^ n) := Nat.pow_le_pow_right (by omega : 1 ≤ M₀) hexp_sum
      _ ≤ d := hM₀_pow_le_d
  let fiber : Fin M₁ → Finset ℕ := fun m =>
    (Finset.range d).filter (fun c => p₁ (c : ZMod d) = m)
  have hfiber_sum : d = ∑ m : Fin M₁, (fiber m).card := by
    have hs := Finset.card_eq_sum_card_fiberwise
      (f := fun c : ℕ => p₁ (c : ZMod d))
      (s := Finset.range d) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)
    simpa [fiber] using hs
  have hex_m₁ : ∃ m₁ : Fin M₁, d ≤ M₁ * (fiber m₁).card := by
    by_contra hall
    have hall' : ∀ m ∈ (Finset.univ : Finset (Fin M₁)), M₁ * (fiber m).card < d := by
      intro m _
      by_contra hge
      exact hall ⟨m, by omega⟩
    have hne : (Finset.univ : Finset (Fin M₁)).Nonempty := ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
    have hsum_lt := Finset.sum_lt_sum_of_nonempty hne hall'
    rw [← Finset.mul_sum, ← hfiber_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul] at hsum_lt
    omega
  obtain ⟨m₁, hm₁_card⟩ := hex_m₁
  obtain ⟨A_n, B, hAn_sub, hAn_card, hB_props, hAn_sum⟩ :=
    iterated_sumset_extract_from_finset hM₁ hM₂ hk_pos hd4 (fiber m₁)
      (fun u hu => Finset.mem_range.mp (Finset.mem_filter.mp hu).1)
      hm₁_card n hrec_bound
  have hRn_pos : 0 < sumsetRecFactor M₁ M₂ k n := sumsetRecFactor_pos hM₁ hM₂ n
  have hk_le_rec : sumsetRecFactor M₁ M₂ k n * k ≤
      16 * M₂ * (k + 1) * sumsetRecFactor M₁ M₂ k n := by
    calc
      sumsetRecFactor M₁ M₂ k n * k
          ≤ sumsetRecFactor M₁ M₂ k n * (k + 1) := Nat.mul_le_mul_left _ (by omega)
      _ = 1 * ((k + 1) * sumsetRecFactor M₁ M₂ k n) := by ring
      _ ≤ (16 * M₂) * ((k + 1) * sumsetRecFactor M₁ M₂ k n) :=
          Nat.mul_le_mul_right _ (by omega : 1 ≤ 16 * M₂)
      _ = 16 * M₂ * (k + 1) * sumsetRecFactor M₁ M₂ k n := by ring
  have hk_le_d : k ≤ d := by
    calc
      k = 1 * k := (one_mul k).symm
      _ ≤ sumsetRecFactor M₁ M₂ k n * k := Nat.mul_le_mul_right k hRn_pos
      _ ≤ 16 * M₂ * (k + 1) * sumsetRecFactor M₁ M₂ k n := hk_le_rec
      _ ≤ d := hrec_bound
  have hk_le_An : k ≤ A_n.card := by
    have hmul : sumsetRecFactor M₁ M₂ k n * k ≤ sumsetRecFactor M₁ M₂ k n * A_n.card :=
      hk_le_rec.trans (hrec_bound.trans hAn_card)
    exact Nat.le_of_mul_le_mul_left hmul hRn_pos
  obtain ⟨J_nat, hJ_sub, hJ_card⟩ := Finset.exists_subset_card_eq hk_le_An
  let J₀ : Finset (ZMod d) := J_nat.image (fun u : ℕ => (u : ZMod d))
  have hJ_inj : Set.InjOn (fun u : ℕ => (u : ZMod d)) (J_nat : Set ℕ) := by
    intro u₁ hu₁ u₂ hu₂ heq
    have hlt₁ : u₁ < d := Finset.mem_range.mp (Finset.mem_filter.mp (hAn_sub (hJ_sub hu₁))).1
    have hlt₂ : u₂ < d := Finset.mem_range.mp (Finset.mem_filter.mp (hAn_sub (hJ_sub hu₂))).1
    have hval := congrArg ZMod.val heq
    simpa [ZMod.val_natCast, Nat.mod_eq_of_lt hlt₁, Nat.mod_eq_of_lt hlt₂] using hval
  have hJ₀_card : J₀.card = k := by
    rw [Finset.card_image_of_injOn hJ_inj, hJ_card]
  have hunshift : HasUnshiftedMonochromaticSumset p₁ m₁ k (d / (4 * M₂)) J₀ B := by
    refine ⟨hJ₀_card, hB_props, ?_⟩
    intro c₀ hc₀ b hb
    rcases Finset.mem_image.mp hc₀ with ⟨u₀, hu₀, rfl⟩
    have hmem := hAn_sum u₀ (hJ_sub hu₀) b hb
    have hp := (Finset.mem_filter.mp hmem).2
    have hcast : ((u₀ + ∑ t : Fin n, b t : ℕ) : ZMod d) =
        (u₀ : ZMod d) + ∑ t : Fin n, (b t : ZMod d) := by
      push_cast
      rfl
    rwa [← hcast]
  obtain ⟨J₀', B', hshift, _⟩ :=
    unshiftedToShiftedSumset d M₁ n k (d / (4 * M₂)) p₁ m₁ J₀ B hunshift
  exact ⟨m₁, k, J₀, B, hk_pos, hk_le_d, hk_lower, hk_upper, hunshift, ⟨J₀', B', hshift⟩⟩

/-- Proof of `Theorem2B_TwoStageLogPowerRankDeficitSpec`. -/
theorem theorem2B_TwoStageLogPowerRankDeficit : Theorem2B_TwoStageLogPowerRankDeficitSpec := by
  intro M₁ M₂ hM₁ hM₂
  obtain ⟨c_lo, C_hi, D₀, hclo_pos, _, hextract⟩ :=
    iteratedKovariSosTuranSumset M₁ M₂ hM₁ hM₂
  refine ⟨c_lo / 4, D₀, by linarith, ?_⟩
  intro F _ d b _ p₁ p₂ K₁ K₂ hd hdD₀ _ hK₁ hK₂
  obtain ⟨m₁, k, _, _, hk_pos, hk_le_d, hk_lower, _, _, ⟨J₀', B', hshift⟩⟩ :=
    hextract d p₁ hdD₀
  have hdiam_sum : ∑ _t : Fin (2 * M₂ - 1), (d / (4 * M₂)) ≤ d := by
    calc
      ∑ _t : Fin (2 * M₂ - 1), (d / (4 * M₂))
          = (2 * M₂ - 1) * (d / (4 * M₂)) := by simp
      _ ≤ (4 * M₂) * (d / (4 * M₂)) :=
          Nat.mul_le_mul_right _ (by omega : 2 * M₂ - 1 ≤ 4 * M₂)
      _ ≤ d := Nat.mul_div_le d (4 * M₂)
  have hbound := (sumsetTwoHopRankBound F d b M₁ M₂ k p₁ p₂ m₁ J₀' B'
    (fun _ => d / (4 * M₂)) K₁ K₂ hd hM₁ hM₂ hk_pos hk_le_d hdiam_sum hshift hK₁ hK₂).2
    (fun _ => le_rfl)
  let r := finrank F (LinearMap.range (swapLinear F (d := d) (A := Fin b → F) - K₂.comp K₁))
  have hr_real : (b : ℝ) * (k : ℝ) * (d : ℝ) ≤ 4 * (r : ℝ) := by
    have hnat : b * k * d ≤ 4 * r := hbound
    exact_mod_cast hnat
  have hbd_nonneg : 0 ≤ (b : ℝ) * (d : ℝ) := by positivity
  let α : ℝ := (1 : ℝ) / (2 * (M₂ : ℝ) - 1)
  have hmul := mul_le_mul_of_nonneg_left hk_lower hbd_nonneg
  calc
    (c_lo / 4) * (b : ℝ) * (d : ℝ) * (Real.log (d : ℝ)) ^ α
        = ((b : ℝ) * (d : ℝ) * (c_lo * (Real.log (d : ℝ)) ^ α)) / 4 := by ring
    _ ≤ ((b : ℝ) * (d : ℝ) * (k : ℝ)) / 4 := by linarith
    _ = ((b : ℝ) * (k : ℝ) * (d : ℝ)) / 4 := by ring
    _ ≤ (4 * (r : ℝ)) / 4 := by linarith
    _ = (r : ℝ) := by ring

/-! ### Single-Class Abstract Band Control (`d = 12, M₂ = 2, k = 2`) -/

private def d12SetJ : Finset (ZMod 12) := {0, 1, 3, 4, 7, 9}

private def d12Shift1 (c : ZMod 12) : (ZMod 12 → ℂ) →ₗ[ℂ] (ZMod 12 → ℂ) where
  toFun w u := w (u + c)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def d12Mode (ζ : ℂ) (m : ℕ) : ZMod 12 → ℂ :=
  fun u => ζ ^ (m * u.val)

private noncomputable def d12Dual (ζ : ℂ) (m : ℕ) : (ZMod 12 → ℂ) →ₗ[ℂ] ℂ where
  toFun w := (12 : ℂ)⁻¹ * ∑ u : ZMod 12, ζ ^ ((12 - m % 12) * u.val) * w u
  map_add' w₁ w₂ := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' r w := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    have hsum_r : (∑ u : ZMod 12, ζ ^ ((12 - m % 12) * u.val) * (r * w u)) =
        r * ∑ u : ZMod 12, ζ ^ ((12 - m % 12) * u.val) * w u := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      ring
    rw [hsum_r]
    ring

private noncomputable def d12Readout1 (ζ : ℂ) : (ZMod 12 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) :=
  LinearMap.pi fun s =>
    match s with
    | ⟨0, _⟩ => d12Dual ζ 0 + d12Dual ζ 1
    | ⟨1, _⟩ => d12Dual ζ 3 + d12Dual ζ 5 + d12Dual ζ 6 + d12Dual ζ 9
    | ⟨2, _⟩ => d12Dual ζ 4 + d12Dual ζ 7 + d12Dual ζ 8 + d12Dual ζ 10

private def d12Gen (ζ : ℂ) : Fin 2 → Fin 3 → (ZMod 12 → ℂ)
  | ⟨0, _⟩, ⟨0, _⟩ => d12Mode ζ 0
  | ⟨1, _⟩, ⟨0, _⟩ => d12Mode ζ 1
  | ⟨0, _⟩, ⟨1, _⟩ => d12Mode ζ 3 - d12Mode ζ 6 + d12Mode ζ 9
  | ⟨1, _⟩, ⟨1, _⟩ => (1 - ζ ^ 2) • d12Mode ζ 5 + (ζ ^ 2) • d12Mode ζ 9
  | ⟨0, _⟩, ⟨2, _⟩ => (1 - ζ ^ 2) • d12Mode ζ 4 + (ζ ^ 2) • d12Mode ζ 8
  | ⟨1, _⟩, ⟨2, _⟩ => d12Mode ζ 4 - d12Mode ζ 7 + d12Mode ζ 10

private def d12ProjCh (ch : Fin 4) : (ZMod 12 → Fin 4 → ℂ) →ₗ[ℂ] (ZMod 12 → ℂ) where
  toFun w u := w u ch
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable def d12Readout4 (ζ : ℂ) : (ZMod 12 → Fin 4 → ℂ) →ₗ[ℂ] (Fin 12 → ℂ) :=
  LinearMap.pi fun idx =>
    (LinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => ℂ) ⟨idx.val % 3, by omega⟩).comp
      ((d12Readout1 ζ).comp (d12ProjCh ⟨idx.val / 3, by omega⟩))

private def d12Embed4 (ζ : ℂ) :
    ((Fin 12 → ℂ) × (Fin 12 → ℂ)) →ₗ[ℂ] (ZMod 12 → Fin 4 → ℂ) where
  toFun p u ch :=
    ∑ r : Fin 3,
      (p.1 ⟨3 * ch.val + r.val, by omega⟩ * d12Gen ζ 0 r u +
       p.2 ⟨3 * ch.val + r.val, by omega⟩ * d12Gen ζ 1 r u)
  map_add' p q := by
    funext u ch
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r _
    ring
  map_smul' c p := by
    funext u ch
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    ring

private lemma d12_pow_mod {ζ : ℂ} (hζ12 : ζ ^ 12 = 1) (n : ℕ) : ζ ^ n = ζ ^ (n % 12) := by
  conv_lhs => rw [← Nat.div_add_mod n 12]
  rw [pow_add, pow_mul, hζ12, one_pow, one_mul]

private lemma d12Dual_shift_mode {ζ : ℂ} (hζ12 : ζ ^ 12 = 1)
    (hprim : ∀ m : ℕ, 1 ≤ m → m < 12 → ζ ^ m ≠ 1) (m m' : ℕ) (c : ZMod 12) :
    d12Dual ζ m (d12Shift1 c (d12Mode ζ m')) =
      if m % 12 = m' % 12 then ζ ^ (m' * c.val) else 0 := by
  have h_shift : d12Shift1 c (d12Mode ζ m') = (ζ ^ (m' * c.val)) • d12Mode ζ m' := by
    funext u
    change ζ ^ (m' * (u + c).val) = ζ ^ (m' * c.val) * ζ ^ (m' * u.val)
    have hmod_eq : (m' * (u + c).val) % 12 = (m' * (u.val + c.val)) % 12 := by
      rw [ZMod.val_add, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
    rw [d12_pow_mod hζ12, hmod_eq, ← d12_pow_mod hζ12, mul_add, pow_add, mul_comm]
  have hsum_zmod12 : ∀ g : ℕ → ℂ, (∑ u : ZMod 12, g u.val) = ∑ k ∈ Finset.range 12, g k := by
    intro g
    refine Finset.sum_bij (fun (u : ZMod 12) _ => u.val) ?_ ?_ ?_ ?_
    · intro u _
      exact Finset.mem_range.mpr (ZMod.val_lt u)
    · intro u₁ _ u₂ _ hval
      exact ZMod.val_injective 12 hval
    · intro k hk
      refine ⟨(k : ZMod 12), Finset.mem_univ _, ?_⟩
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp hk)]
    · intro _ _
      rfl
  have φ_h : d12Dual ζ m (d12Mode ζ m') = if m % 12 = m' % 12 then 1 else 0 := by
    change (12 : ℂ)⁻¹ * ∑ u : ZMod 12, ζ ^ ((12 - m % 12) * u.val) * ζ ^ (m' * u.val) = _
    rw [hsum_zmod12 (fun k => ζ ^ ((12 - m % 12) * k) * ζ ^ (m' * k))]
    let rem := (12 - m % 12 + m' % 12) % 12
    let z : ℂ := ζ ^ rem
    have hterm_z : ∀ k : ℕ, ζ ^ ((12 - m % 12) * k) * ζ ^ (m' * k) = z ^ k := by
      intro k
      have hmod_m : (12 - m % 12 + m') % 12 = rem := by
        dsimp [rem]
        omega
      rw [← pow_add, ← add_mul, pow_mul, d12_pow_mod hζ12 (12 - m % 12 + m'), hmod_m, ← pow_mul]
    simp_rw [hterm_z]
    by_cases hmm : m % 12 = m' % 12
    · simp only [hmm, ↓reduceIte]
      have hrem0 : rem = 0 := by dsimp [rem]; omega
      have hz1 : z = 1 := by simp [z, hrem0]
      simp [hz1]
    · simp only [hmm, ↓reduceIte]
      have hrem_bounds : 1 ≤ rem ∧ rem < 12 := by
        dsimp [rem]
        omega
      have hz_ne1 : z - 1 ≠ 0 := sub_ne_zero.mpr (hprim rem hrem_bounds.1 hrem_bounds.2)
      have hz12 : z ^ 12 - 1 = 0 := by
        dsimp [z]
        rw [← pow_mul, mul_comm, pow_mul, hζ12, one_pow, sub_self]
      have hgeom : (∑ k ∈ Finset.range 12, z ^ k) * (z - 1) = z ^ 12 - 1 := by
        simp [Finset.sum_range_succ]
        ring
      rw [hz12] at hgeom
      have hsum0 : ∑ k ∈ Finset.range 12, z ^ k = 0 :=
        (mul_eq_zero.mp hgeom).resolve_right hz_ne1
      rw [hsum0, mul_zero]
  rw [h_shift, map_smul, φ_h, smul_eq_mul]
  by_cases hmm : m % 12 = m' % 12 <;> simp [hmm]

private lemma d12_cyclotomic_identities {ζ : ℂ} (hζ12 : ζ ^ 12 = 1)
    (hprim : ∀ m : ℕ, 1 ≤ m → m < 12 → ζ ^ m ≠ 1) {c : ZMod 12} (hc : c ∈ d12SetJ) :
    (ζ ^ (3 * c.val) - ζ ^ (6 * c.val) + ζ ^ (9 * c.val) = 1) ∧
    ((1 - ζ ^ 2) * ζ ^ (5 * c.val) + ζ ^ 2 * ζ ^ (9 * c.val) = ζ ^ c.val) ∧
    ((1 - ζ ^ 2) * ζ ^ (4 * c.val) + ζ ^ 2 * ζ ^ (8 * c.val) = 1) ∧
    (ζ ^ (4 * c.val) - ζ ^ (7 * c.val) + ζ ^ (10 * c.val) = ζ ^ c.val) := by
  have hfac6 : (ζ ^ 6 - 1) * (ζ ^ 6 + 1) = 0 := by
    calc
      (ζ ^ 6 - 1) * (ζ ^ 6 + 1) = ζ ^ 12 - 1 := by ring
      _ = 0 := by rw [hζ12, sub_self]
  have hζ6 : ζ ^ 6 = -1 := by
    have hne : ζ ^ 6 - 1 ≠ 0 := sub_ne_zero.mpr (hprim 6 (by omega) (by omega))
    exact eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp hfac6).resolve_left hne)
  have hfac2 : (ζ ^ 2 + 1) * (ζ ^ 4 - ζ ^ 2 + 1) = 0 := by
    calc
      (ζ ^ 2 + 1) * (ζ ^ 4 - ζ ^ 2 + 1) = ζ ^ 6 + 1 := by ring
      _ = 0 := by rw [hζ6]; ring
  have hΦ : ζ ^ 4 - ζ ^ 2 + 1 = 0 := by
    have hne2 : ζ ^ 2 + 1 ≠ 0 := by
      intro h0
      have hz2 : ζ ^ 2 = -1 := eq_neg_of_add_eq_zero_left h0
      have hz4 : ζ ^ 4 = 1 := by
        calc
          ζ ^ 4 = (ζ ^ 2) ^ 2 := by ring
          _ = 1 := by rw [hz2]; ring
      exact hprim 4 (by omega) (by omega) hz4
    exact (mul_eq_zero.mp hfac2).resolve_left hne2
  have h4 : ζ ^ 4 = ζ ^ 2 - 1 := by linear_combination hΦ
  have h5 : ζ ^ 5 = ζ ^ 3 - ζ := by linear_combination ζ * hΦ
  have h7 : ζ ^ 7 = -ζ := by calc ζ ^ 7 = ζ ^ 6 * ζ := by ring
    _ = -ζ := by rw [hζ6]; ring
  have h8 : ζ ^ 8 = -ζ ^ 2 := by calc ζ ^ 8 = ζ ^ 6 * ζ ^ 2 := by ring
    _ = -ζ ^ 2 := by rw [hζ6]; ring
  have h9 : ζ ^ 9 = -ζ ^ 3 := by calc ζ ^ 9 = ζ ^ 6 * ζ ^ 3 := by ring
    _ = -ζ ^ 3 := by rw [hζ6]; ring
  have h10 : ζ ^ 10 = 1 - ζ ^ 2 := by calc ζ ^ 10 = ζ ^ 6 * ζ ^ 4 := by ring
    _ = 1 - ζ ^ 2 := by rw [hζ6, h4]; ring
  have h11 : ζ ^ 11 = ζ - ζ ^ 3 := by calc ζ ^ 11 = ζ ^ 6 * ζ ^ 5 := by ring
    _ = ζ - ζ ^ 3 := by rw [hζ6, h5]; ring
  have hval_J12 : ∀ x ∈ d12SetJ,
      x.val = 0 ∨ x.val = 1 ∨ x.val = 3 ∨ x.val = 4 ∨ x.val = 7 ∨ x.val = 9 := by
    decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [d12_pow_mod hζ12 (3 * c.val), d12_pow_mod hζ12 (6 * c.val), d12_pow_mod hζ12 (9 * c.val)]
    rcases hval_J12 c hc with hcv | hcv | hcv | hcv | hcv | hcv
    all_goals
      rw [hcv]
      norm_num
      try repeat first
        | rw [h4] | rw [h5] | rw [hζ6] | rw [h7] | rw [h8] | rw [h9] | rw [h10] | rw [h11]
      try ring
  · rw [d12_pow_mod hζ12 (5 * c.val), d12_pow_mod hζ12 (9 * c.val)]
    rcases hval_J12 c hc with hcv | hcv | hcv | hcv | hcv | hcv
    all_goals
      rw [hcv]
      norm_num
      try repeat first
        | rw [h4] | rw [h5] | rw [hζ6] | rw [h7] | rw [h8] | rw [h9] | rw [h10] | rw [h11]
      try ring_nf
      try rw [h4]
      try rw [h5]
      try ring
  · rw [d12_pow_mod hζ12 (4 * c.val), d12_pow_mod hζ12 (8 * c.val)]
    rcases hval_J12 c hc with hcv | hcv | hcv | hcv | hcv | hcv
    all_goals
      rw [hcv]
      norm_num
      try repeat first
        | rw [h4] | rw [h5] | rw [hζ6] | rw [h7] | rw [h8] | rw [h9] | rw [h10] | rw [h11]
      try ring_nf
      try rw [h4]
      try rw [h5]
      try ring
  · rw [d12_pow_mod hζ12 (4 * c.val), d12_pow_mod hζ12 (7 * c.val), d12_pow_mod hζ12 (10 * c.val)]
    rcases hval_J12 c hc with hcv | hcv | hcv | hcv | hcv | hcv
    all_goals
      rw [hcv]
      norm_num
      try repeat first
        | rw [h4] | rw [h5] | rw [hζ6] | rw [h7] | rw [h8] | rw [h9] | rw [h10] | rw [h11]
      try ring

private lemma d12Readout1_gen {ζ : ℂ} (hζ12 : ζ ^ 12 = 1)
    (hprim : ∀ m : ℕ, 1 ≤ m → m < 12 → ζ ^ m ≠ 1) {c : ZMod 12} (hc : c ∈ d12SetJ)
    (ν : Fin 2) (r s : Fin 3) :
    d12Readout1 ζ (d12Shift1 c (d12Gen ζ ν r)) s =
      if r = s then (ζ ^ c.val) ^ ν.val else 0 := by
  obtain ⟨hidA, hidB, hidC, hidD⟩ := d12_cyclotomic_identities hζ12 hprim hc
  fin_cases ν <;> fin_cases r <;> fin_cases s
  all_goals
    simp [d12Readout1, d12Gen, d12Dual_shift_mode hζ12 hprim]
  · linear_combination hidA
  · linear_combination hidC
  · linear_combination hidB
  · linear_combination hidD

private lemma d12Readout4_embed4 {ζ : ℂ} (hζ12 : ζ ^ 12 = 1)
    (hprim : ∀ m : ℕ, 1 ≤ m → m < 12 → ζ ^ m ≠ 1)
    (a₀ a₁ : Fin 12 → ℂ) {c : ZMod 12} (hc : c ∈ d12SetJ) :
    d12Readout4 ζ (cyclicChannelShift ℂ 12 4 c (d12Embed4 ζ (a₀, a₁))) =
      a₀ + (ζ ^ c.val) • a₁ := by
  funext idx
  let ch : Fin 4 := ⟨idx.val / 3, by omega⟩
  let r₀ : Fin 3 := ⟨idx.val % 3, by omega⟩
  have hch_eq : d12ProjCh ch (cyclicChannelShift ℂ 12 4 c (d12Embed4 ζ (a₀, a₁))) =
      ∑ r : Fin 3,
        (a₀ ⟨3 * ch.val + r.val, by omega⟩ • d12Shift1 c (d12Gen ζ 0 r) +
         a₁ ⟨3 * ch.val + r.val, by omega⟩ • d12Shift1 c (d12Gen ζ 1 r)) := by
    funext u
    simp [d12ProjCh, cyclicChannelShift, d12Embed4, d12Shift1, Finset.sum_apply, smul_eq_mul]
  change d12Readout1 ζ (d12ProjCh ch (cyclicChannelShift ℂ 12 4 c (d12Embed4 ζ (a₀, a₁)))) r₀ =
    a₀ idx + ζ ^ c.val * a₁ idx
  rw [hch_eq, map_sum, Finset.sum_apply]
  have hterm : ∀ r : Fin 3,
      d12Readout1 ζ (a₀ ⟨3 * ch.val + r.val, by omega⟩ • d12Shift1 c (d12Gen ζ 0 r) +
          a₁ ⟨3 * ch.val + r.val, by omega⟩ • d12Shift1 c (d12Gen ζ 1 r)) r₀ =
      if r = r₀ then
        a₀ ⟨3 * ch.val + r.val, by omega⟩ + ζ ^ c.val * a₁ ⟨3 * ch.val + r.val, by omega⟩
      else 0 := by
    intro r
    rw [map_add, map_smul, map_smul, Pi.add_apply, Pi.smul_apply, Pi.smul_apply,
      smul_eq_mul, smul_eq_mul, d12Readout1_gen hζ12 hprim hc 0 r r₀,
      d12Readout1_gen hζ12 hprim hc 1 r r₀]
    by_cases hr : r = r₀ <;> simp [hr, mul_comm]
  simp_rw [hterm]
  rw [Finset.sum_eq_single r₀]
  · simp only [↓reduceIte]
    have hidx : (⟨3 * ch.val + r₀.val, by omega⟩ : Fin 12) = idx := by
      apply Fin.ext
      dsimp [ch, r₀]
      omega
    rw [hidx]
  · intro r _ hne
    simp [hne]
  · intro hmem
    exact False.elim (hmem (Finset.mem_univ r₀))

/-- Proof of `Control_D12SingleClassAbstractBandSpec`: explicit Fourier mode-partition
realization of a 24-dimensional abstract `k = 2` band subspace on `J = {0, 1, 3, 4, 7, 9} ⊆ ZMod 12`. -/
theorem control_D12SingleClassAbstractBand : Control_D12SingleClassAbstractBandSpec := by
  intro ζ hζ12 hprim
  have hv0 : (0 : ZMod 12).val = 0 := by decide
  have hv1 : (1 : ZMod 12).val = 1 := by decide
  have hc0 : (0 : ZMod 12) ∈ d12SetJ := by decide
  have hc1 : (1 : ZMod 12) ∈ d12SetJ := by decide
  have hζ_ne1 : ζ - 1 ≠ 0 := sub_ne_zero.mpr (by simpa [pow_one] using hprim 1 (by omega) (by omega))
  have hembed4_inj : Function.Injective (d12Embed4 ζ) := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨a₀, a₁⟩ hp0
    have he0 : a₀ + (ζ ^ (0 : ZMod 12).val) • a₁ = 0 := by
      rw [← d12Readout4_embed4 hζ12 hprim a₀ a₁ hc0, hp0, map_zero, map_zero]
    have he1 : a₀ + (ζ ^ (1 : ZMod 12).val) • a₁ = 0 := by
      rw [← d12Readout4_embed4 hζ12 hprim a₀ a₁ hc1, hp0, map_zero, map_zero]
    rw [hv0, pow_zero, one_smul] at he0
    rw [hv1, pow_one] at he1
    have hdiff : (ζ - 1) • a₁ = 0 := by
      calc
        (ζ - 1) • a₁ = (a₀ + ζ • a₁) - (a₀ + a₁) := by
          rw [sub_smul, one_smul]
          abel
        _ = 0 := by rw [he1, he0, sub_self]
    have ha₁ : a₁ = 0 := (smul_eq_zero.mp hdiff).resolve_left hζ_ne1
    have ha₀ : a₀ = 0 := by simpa [ha₁] using he0
    exact Prod.ext ha₀ ha₁
  let W : Submodule ℂ (ZMod 12 → Fin 4 → ℂ) := LinearMap.range (d12Embed4 ζ)
  have hdimW : finrank ℂ W = 24 := by
    rw [LinearMap.finrank_range_of_inj hembed4_inj]
    simp [Module.finrank_prod]
  refine ⟨W, d12Readout4 ζ, hdimW, ?_, ?_⟩
  · rintro w ⟨⟨a₀, a₁⟩, rfl⟩ hz
    have he0 : a₀ + (ζ ^ (0 : ZMod 12).val) • a₁ = 0 := by
      rw [← d12Readout4_embed4 hζ12 hprim a₀ a₁ hc0]
      exact hz 0 hc0
    have he1 : a₀ + (ζ ^ (1 : ZMod 12).val) • a₁ = 0 := by
      rw [← d12Readout4_embed4 hζ12 hprim a₀ a₁ hc1]
      exact hz 1 hc1
    rw [hv0, pow_zero, one_smul] at he0
    rw [hv1, pow_one] at he1
    have hdiff : (ζ - 1) • a₁ = 0 := by
      calc
        (ζ - 1) • a₁ = (a₀ + ζ • a₁) - (a₀ + a₁) := by
          rw [sub_smul, one_smul]
          abel
        _ = 0 := by rw [he1, he0, sub_self]
    have ha₁ : a₁ = 0 := (smul_eq_zero.mp hdiff).resolve_left hζ_ne1
    have ha₀ : a₀ = 0 := by simpa [ha₁] using he0
    change d12Embed4 ζ (a₀, a₁) = 0
    rw [ha₀, ha₁]
    exact map_zero (d12Embed4 ζ)
  · intro a₀ a₁
    exact ⟨d12Embed4 ζ (a₀, a₁), ⟨(a₀, a₁), rfl⟩,
      fun c hc => d12Readout4_embed4 hζ12 hprim a₀ a₁ hc⟩

/-! ### Open-Target Bridge Implication -/

/-- Any unrestricted-field macroscopic rank deficit bound immediately implies the
admissible-field (`(d : F) ≠ 0`) macroscopic rank deficit bound. -/
theorem openTarget_admissible_of_unrestricted :
    OpenTarget_MacroscopicTwoStageRankDeficitSpec.{u} →
      OpenTarget_MacroscopicTwoStageRankDeficitAdmissibleFieldSpec.{u} := by
  intro h M₁ M₂ hM₁ hM₂
  obtain ⟨ε, D₀, hε, hbound⟩ := h M₁ M₂ hM₁ hM₂
  exact ⟨ε, D₀, hε, fun F _ d b _ p₁ p₂ K₁ K₂ _ hdD₀ hb hK₁ hK₂ =>
    hbound F d b p₁ p₂ K₁ K₂ hdD₀ hb hK₁ hK₂⟩

end BoundedArityDecoders
