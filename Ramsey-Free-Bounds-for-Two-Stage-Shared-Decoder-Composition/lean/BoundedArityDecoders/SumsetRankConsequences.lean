import BoundedArityDecoders.SumsetRankDeficitProofs

/-!
# Consequences & Quantitative Refinements — Part II.B: Sumset Rank Deficit

Kernel-verified refinements and direct consequences of Theorem 2B
(`BoundedArityDecoders.SumsetRankDeficit` and `BoundedArityDecoders.SumsetRankDeficitProofs`):

1. **Intrinsic Set Diameter (`finsetNatDiam`)**:
   Exact diameter invariance `finsetNatDiam (B̃ t) = finsetNatDiam (B t)` under minimum-shifting and direct two-stage rank bound in terms of
   `∑ t, finsetNatDiam (B̃ t)` (`unshiftedToShiftedSumset_intrinsicDiam`).
2. **Direct `bandRowSpace` Annihilating-Polynomial Kernel Bound**:
   Public Step 3 bound `finrank E (ker P(T_band)) ≤ b * M₂ * k * L₀` directly on
   `SharedDecoders.ColumnAmbient (SharedDecoders.bandRowSpace χ p₂ k)`
   (`sumsetAnnihilatingPolynomial_bandRowSpace`).
3. **Single-Class Second Stage (`M₂ = 1`, `Ω(b d log d)`) & Explicit Constants**:
   Clean `M₂ = 1` specialization (`theorem2B_OneSecondStage_OmegaLog`) and explicit quantitative
   formulas `theorem2BExplicitConst` and `theorem2BExplicitThreshold` (`theorem2B_ExplicitConstant`).
4. **Unconditional `d = 12` Primitive Root Witness & `bandRowSpace` Channel Equivalence**:
   Unconditional primitive 12th root `zeta12 ∈ ℂ` (`exists_primitive_twelfth_root_complex`),
   unconditional 24-dimensional realization (`control_D12_UnconditionalExists`), and explicit
   shift-intertwining `LinearEquiv` with `ColumnAmbient (bandRowSpace ...)` establishing the
   single-class relaxation barrier (`control_D12_BandRowSpaceChannelEquiv`).
-/

namespace BoundedArityDecoders

open SharedDecoders Module Polynomial
open scoped BigOperators

/-! ### 1. Intrinsic Set Diameter in Theorem 2B Step 1 & Step 4 -/

/-- Intrinsic diameter `max S - min S` of a finite set of natural numbers (`0` if empty). -/
def finsetNatDiam (S : Finset ℕ) : ℕ :=
  if h : S.Nonempty then S.max' h - S.min' h else 0

/-- `finsetNatDiam S ≤ L₀` holds if and only if every pair `x, y ∈ S` satisfies `x ≤ y + L₀`. -/
theorem finsetNatDiam_le_iff (S : Finset ℕ) (L₀ : ℕ) :
    finsetNatDiam S ≤ L₀ ↔ ∀ x ∈ S, ∀ y ∈ S, x ≤ y + L₀ := by
  unfold finsetNatDiam
  split_ifs with h
  · constructor
    · intro hle x hx y hy
      have hxmax : x ≤ S.max' h := Finset.le_max' S x hx
      have hminy : S.min' h ≤ y := Finset.min'_le S y hy
      omega
    · intro hpairs
      have hpair := hpairs (S.max' h) (Finset.max'_mem S h) (S.min' h) (Finset.min'_mem S h)
      omega
  · simp only [Finset.not_nonempty_iff_eq_empty] at h
    subst h
    simp

/-- When `0 ∈ S`, `S.min'` vanishes so every element of `S` is bounded by `finsetNatDiam S`. -/
theorem le_finsetNatDiam_of_zero_mem {S : Finset ℕ} (h0 : 0 ∈ S) {x : ℕ} (hx : x ∈ S) :
    x ≤ finsetNatDiam S := by
  have hne : S.Nonempty := ⟨0, h0⟩
  have hmin0 : S.min' hne = 0 := Nat.eq_zero_of_le_zero (Finset.min'_le S 0 h0)
  have hxmax : x ≤ S.max' hne := Finset.le_max' S x hx
  simp [finsetNatDiam, hne, hmin0, hxmax]

/-- Shifting a nonempty finite set `S ⊆ ℕ` down by `S.min'` preserves `finsetNatDiam`. -/
theorem finsetNatDiam_shift_min {S : Finset ℕ} (hS : S.Nonempty) :
    finsetNatDiam (S.image (fun x => x - S.min' hS)) = finsetNatDiam S := by
  let b₀ := S.min' hS
  let S' := S.image (fun x => x - b₀)
  have h0 : 0 ∈ S' := Finset.mem_image.mpr ⟨b₀, Finset.min'_mem S hS, Nat.sub_self b₀⟩
  have hS' : S'.Nonempty := ⟨0, h0⟩
  have hmin' : S'.min' hS' = 0 := Nat.eq_zero_of_le_zero (Finset.min'_le S' 0 h0)
  have hmax_mem : S.max' hS - b₀ ∈ S' :=
    Finset.mem_image.mpr ⟨S.max' hS, Finset.max'_mem S hS, rfl⟩
  have hmax_le : S'.max' hS' ≤ S.max' hS - b₀ := by
    apply Finset.max'_le
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
    exact Nat.sub_le_sub_right (Finset.le_max' S x hx) b₀
  have hle_max : S.max' hS - b₀ ≤ S'.max' hS' := Finset.le_max' S' _ hmax_mem
  have hmax' : S'.max' hS' = S.max' hS - b₀ := le_antisymm hmax_le hle_max
  simp [S', b₀, finsetNatDiam, hS, hS', hmin', hmax']

/-- **Theorem 2B Step 1 & Step 4 with Intrinsic Set Diameter.**
Shifting each `B t` by its minimum produces `J̃₀` and `B̃` with `0 ∈ B̃ t`,
`|B̃ t| = k + 1`, `finsetNatDiam (B̃ t) = finsetNatDiam (B t) ≤ L₀`, and
`HasShiftedMonochromaticSumset p₁ m₁ k J̃₀ B̃ (fun t => finsetNatDiam (B̃ t))`, yielding the
two-stage rank bound directly in terms of `∑ t, finsetNatDiam (B̃ t)`. -/
theorem unshiftedToShiftedSumset_intrinsicDiam
    {d M₁ M₂ k L₀ : ℕ} [NeZero d] (hM₂ : 1 ≤ M₂)
    (p₁ : ZMod d → Fin M₁) (m₁ : Fin M₁)
    (J₀ : Finset (ZMod d)) (B : Fin (2 * M₂ - 1) → Finset ℕ)
    (h : HasUnshiftedMonochromaticSumset p₁ m₁ k L₀ J₀ B) :
    ∃ (J₀_tilde : Finset (ZMod d)) (B_tilde : Fin (2 * M₂ - 1) → Finset ℕ),
      (∀ t : Fin (2 * M₂ - 1),
        0 ∈ B_tilde t ∧
        (B_tilde t).card = k + 1 ∧
        finsetNatDiam (B_tilde t) = finsetNatDiam (B t) ∧
        finsetNatDiam (B_tilde t) ≤ L₀) ∧
      (∀ (S : Finset (Fin (2 * M₂ - 1))) (c₀ : ZMod d), c₀ ∈ J₀_tilde →
        ∀ b : Fin (2 * M₂ - 1) → ℕ, (∀ t ∈ S, b t ∈ B_tilde t) →
          p₁ (c₀ + ∑ t ∈ S, (b t : ZMod d)) = m₁) ∧
      HasShiftedMonochromaticSumset p₁ m₁ k J₀_tilde B_tilde
        (fun t => finsetNatDiam (B_tilde t)) ∧
      ∀ (F : Type*) [Field F] (b : ℕ) (p₂ : ZMod d → Fin M₂)
        (K₁ K₂ : State d (Fin b → F) →ₗ[F] State d (Fin b → F)),
        (d : F) ≠ 0 →
        1 ≤ b →
        ClassUniform p₁ K₁ →
        ClassUniform p₂ K₂ →
        let r := finrank F
          (LinearMap.range (swapLinear F (d := d) (A := Fin b → F) - K₂.comp K₁))
        b * k * (d - ∑ t : Fin (2 * M₂ - 1), finsetNatDiam (B_tilde t)) ≤ 2 * r ∧
        ((∀ t : Fin (2 * M₂ - 1), finsetNatDiam (B_tilde t) ≤ d / (4 * M₂)) →
          b * k * d ≤ 4 * r) := by
  rcases h with ⟨hJ₀, hB, hsum⟩
  have hBne : ∀ t : Fin (2 * M₂ - 1), (B t).Nonempty := fun t =>
    Finset.card_pos.mp (by rw [(hB t).1]; omega)
  let b₀ : Fin (2 * M₂ - 1) → ℕ := fun t => (B t).min' (hBne t)
  let B_tilde : Fin (2 * M₂ - 1) → Finset ℕ := fun t => (B t).image (fun x => x - b₀ t)
  let shiftSum : ZMod d := ∑ t : Fin (2 * M₂ - 1), (b₀ t : ZMod d)
  let J₀_tilde : Finset (ZMod d) := J₀.image (fun c => c + shiftSum)
  have hJ₀_tilde_card : J₀_tilde.card = k := by
    rw [Finset.card_image_of_injective _ (add_left_injective shiftSum), hJ₀]
  have hBt_props : ∀ t : Fin (2 * M₂ - 1),
      0 ∈ B_tilde t ∧ (B_tilde t).card = k + 1 ∧
      finsetNatDiam (B_tilde t) = finsetNatDiam (B t) ∧ finsetNatDiam (B_tilde t) ≤ L₀ := by
    intro t
    have h0 : 0 ∈ B_tilde t :=
      Finset.mem_image.mpr ⟨b₀ t, Finset.min'_mem (B t) (hBne t), Nat.sub_self _⟩
    have hinj : Set.InjOn (fun x => x - b₀ t) (B t : Set ℕ) := by
      intro x hx y hy hxy
      dsimp at hxy
      have hxl : b₀ t ≤ x := Finset.min'_le (B t) x hx
      have hyl : b₀ t ≤ y := Finset.min'_le (B t) y hy
      omega
    have hcard : (B_tilde t).card = k + 1 := by
      rw [Finset.card_image_of_injOn hinj, (hB t).1]
    have hdiam_eq : finsetNatDiam (B_tilde t) = finsetNatDiam (B t) :=
      finsetNatDiam_shift_min (hBne t)
    have hdiam_le : finsetNatDiam (B_tilde t) ≤ L₀ := by
      rw [hdiam_eq, finsetNatDiam_le_iff]
      intro x hx y _
      exact ((hB t).2 x hx).trans (Nat.le_add_left L₀ y)
    exact ⟨h0, hcard, hdiam_eq, hdiam_le⟩
  have hsub : ∀ (S : Finset (Fin (2 * M₂ - 1))) (c₀' : ZMod d), c₀' ∈ J₀_tilde →
      ∀ b : Fin (2 * M₂ - 1) → ℕ, (∀ t ∈ S, b t ∈ B_tilde t) →
        p₁ (c₀' + ∑ t ∈ S, (b t : ZMod d)) = m₁ := by
    intro S c₀' hc₀' b hb
    rcases Finset.mem_image.mp hc₀' with ⟨c₀, hc₀, rfl⟩
    let b_orig : Fin (2 * M₂ - 1) → ℕ := fun t => (if t ∈ S then b t else 0) + b₀ t
    have hb_orig : ∀ t : Fin (2 * M₂ - 1), b_orig t ∈ B t := by
      intro t
      dsimp [b_orig]
      by_cases ht : t ∈ S
      · simp only [ht, ↓reduceIte]
        rcases Finset.mem_image.mp (hb t ht) with ⟨x, hx, hxb⟩
        rw [← hxb, Nat.sub_add_cancel (Finset.min'_le (B t) x hx)]
        exact hx
      · simp only [ht, ↓reduceIte, zero_add]
        exact Finset.min'_mem (B t) (hBne t)
    have heq : c₀ + shiftSum + ∑ t ∈ S, (b t : ZMod d) =
        c₀ + ∑ t : Fin (2 * M₂ - 1), (b_orig t : ZMod d) := by
      have hS : (∑ t ∈ S, (b t : ZMod d)) =
          ∑ t : Fin (2 * M₂ - 1), (if t ∈ S then (b t : ZMod d) else 0) := by
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
  have hshift : HasShiftedMonochromaticSumset p₁ m₁ k J₀_tilde B_tilde
      (fun t => finsetNatDiam (B_tilde t)) := by
    refine ⟨hJ₀_tilde_card, ?_, fun c₀' hc₀' b hb => hsub Finset.univ c₀' hc₀' b (fun t _ => hb t)⟩
    intro t
    exact ⟨(hBt_props t).1, (hBt_props t).2.1,
      fun x hx => le_finsetNatDiam_of_zero_mem (hBt_props t).1 hx⟩
  refine ⟨J₀_tilde, B_tilde, hBt_props, hsub, hshift, ?_⟩
  intro F _ b p₂ K₁ K₂ hd _ hK₁ hK₂
  have hM₁ : 1 ≤ M₁ := by have := m₁.isLt; omega
  have hkd : k ≤ d := by
    have hle : J₀.card ≤ Fintype.card (ZMod d) := Finset.card_le_univ J₀
    simpa [hJ₀, ZMod.card] using hle
  by_cases hk0 : k = 0
  · subst hk0
    simp
  · have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hk0
    constructor
    · by_cases hsum_le : ∑ t : Fin (2 * M₂ - 1), finsetNatDiam (B_tilde t) ≤ d
      · exact (sumsetTwoHopRankBound F d b M₁ M₂ k p₁ p₂ m₁ J₀_tilde B_tilde
          (fun t => finsetNatDiam (B_tilde t)) K₁ K₂ hd hM₁ hM₂ hk1 hkd hsum_le hshift hK₁ hK₂).1
      · have hzero : d - ∑ t : Fin (2 * M₂ - 1), finsetNatDiam (B_tilde t) = 0 := by omega
        simp [hzero]
    · intro hdiam_quarter
      have hsum_le : ∑ t : Fin (2 * M₂ - 1), finsetNatDiam (B_tilde t) ≤ d := by
        have h1 : ∑ t : Fin (2 * M₂ - 1), finsetNatDiam (B_tilde t) ≤
            (2 * M₂ - 1) * (d / (4 * M₂)) := by
          have hs := Finset.sum_le_sum fun t (_ : t ∈ Finset.univ) => hdiam_quarter t
          simpa using hs
        have h2 : (2 * M₂ - 1) * (d / (4 * M₂)) ≤ (4 * M₂) * (d / (4 * M₂)) :=
          Nat.mul_le_mul_right _ (by omega : 2 * M₂ - 1 ≤ 4 * M₂)
        exact h1.trans (h2.trans (Nat.mul_div_le d (4 * M₂)))
      exact (sumsetTwoHopRankBound F d b M₁ M₂ k p₁ p₂ m₁ J₀_tilde B_tilde
        (fun t => finsetNatDiam (B_tilde t)) K₁ K₂ hd hM₁ hM₂ hk1 hkd hsum_le hshift hK₁ hK₂).2
        hdiam_quarter

/-! ### 2. Public Step 3 Kernel Dimension Bound on `ColumnAmbient (bandRowSpace χ p₂ k)` -/

/-- **Theorem 2B Step 3 Directly on `ColumnAmbient (bandRowSpace χ p₂ k)`.**
For any finite subset `B_set ⊆ ℕ` with `0 ∈ B_set`, `B_set.card = k + 1`, and `∀ x ∈ B_set, x ≤ L₀`
(equivalently `finsetNatDiam B_set ≤ L₀`), there exists a nonzero sparse polynomial `P ∈ E[X]`
supported on `B_set` of degree `≤ finsetNatDiam B_set ≤ L₀` vanishing on `{χ r : 0 ≤ r < k}`, whose
induced operator `Polynomial.aeval T_band P` on `ColumnAmbient (bandRowSpace (b := b) χ p₂ k)` has
kernel dimension at most `b * M₂ * k * L₀`. -/
theorem sumsetAnnihilatingPolynomial_bandRowSpace
    {E : Type*} [Field E] {d b M₂ k L₀ : ℕ} [NeZero d]
    (χ : AddChar (ZMod d) E) (p₂ : ZMod d → Fin M₂)
    (B_set : Finset ℕ)
    (h0 : 0 ∈ B_set) (hcard : B_set.card = k + 1) (hB_le : ∀ x ∈ B_set, x ≤ L₀) :
    let T_band := SharedDecoders.channelRotation (F := E) (I := Unit)
      (A := SharedDecoders.bandRowSpace (b := b) χ p₂ k) (1 : ZMod d)
    ∃ P : Polynomial E,
      P ≠ 0 ∧
      P.natDegree ≤ finsetNatDiam B_set ∧
      P.natDegree ≤ L₀ ∧
      (∀ i ∈ P.support, i ∈ B_set) ∧
      (∀ r : Fin k, P.eval (χ (r.val : ZMod d)) = 0) ∧
      (∀ r : Fin k, ∑ x ∈ B_set, P.coeff x * χ (((r.val * x : ℕ) : ZMod d)) = 0) ∧
      finrank E (LinearMap.ker (Polynomial.aeval T_band P)) ≤ b * M₂ * k * L₀ := by
  classical
  let evalMap : (B_set → E) →ₗ[E] (Fin k → E) :=
    { toFun := fun α r => ∑ x : B_set, α x * χ (((r.val * x.1 : ℕ) : ZMod d))
      map_add' := fun α β => by funext r; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun c α => by funext r; simp [Finset.mul_sum, mul_assoc] }
  have hker_ne : LinearMap.ker evalMap ≠ ⊥ := by
    intro hbot
    have hle := LinearMap.finrank_le_finrank_of_injective ((LinearMap.ker_eq_bot).mp hbot)
    have hdom : finrank E (B_set → E) = k + 1 := by simp [hcard]
    have hcod : finrank E (Fin k → E) = k := by simp
    omega
  obtain ⟨α, hα_ker, hα_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker_ne
  let P : Polynomial E := ∑ x : B_set, Polynomial.monomial x.1 (α x)
  have hcoeff_mem : ∀ x : B_set, P.coeff x.1 = α x := by
    intro x
    simp only [P, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
    rw [Finset.sum_eq_single x]
    · simp
    · intro y _ hyx
      have hval : y.1 ≠ x.1 := fun h => hyx (Subtype.ext h)
      simp [hval]
    · intro hx; exact False.elim (hx (Finset.mem_univ x))
  have hcoeff_not_mem : ∀ n : ℕ, n ∉ B_set → P.coeff n = 0 := by
    intro n hn
    simp only [P, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
    apply Finset.sum_eq_zero
    intro x _
    have hne : x.1 ≠ n := fun h => hn (h ▸ x.2)
    simp [hne]
  have hP_ne : P ≠ 0 := by
    have hα_ex : ∃ x : B_set, α x ≠ 0 := by
      by_contra hall; apply hα_ne; funext x; by_contra hx; exact hall ⟨x, hx⟩
    obtain ⟨x, hx⟩ := hα_ex
    intro hP0; apply hx; rw [← hcoeff_mem x, hP0, Polynomial.coeff_zero]
  have hsupp : ∀ i ∈ P.support, i ∈ B_set := by
    intro i hi; by_contra hnot
    exact (Polynomial.mem_support_iff.mp hi) (hcoeff_not_mem i hnot)
  have hdeg_diam : P.natDegree ≤ finsetNatDiam B_set := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    apply hcoeff_not_mem N
    intro hmem
    exact Nat.not_le_of_gt hN (le_finsetNatDiam_of_zero_mem h0 hmem)
  have hdiam_le : finsetNatDiam B_set ≤ L₀ := by
    rw [finsetNatDiam_le_iff]
    intro x hx y _
    exact (hB_le x hx).trans (Nat.le_add_left L₀ y)
  have hdeg_L₀ : P.natDegree ≤ L₀ := hdeg_diam.trans hdiam_le
  have hann : ∀ r : Fin k, ∑ x ∈ B_set, P.coeff x * χ (((r.val * x : ℕ) : ZMod d)) = 0 := by
    intro r
    have hr := congrFun hα_ker r
    change ∑ x : B_set, α x * χ (((r.val * x.1 : ℕ) : ZMod d)) = 0 at hr
    rw [← Finset.sum_coe_sort B_set]
    refine Eq.trans ?_ hr
    apply Finset.sum_congr rfl
    intro x _; rw [hcoeff_mem x]
  have heval : ∀ r : Fin k, P.eval (χ (r.val : ZMod d)) = 0 := by
    intro r
    rw [Polynomial.eval_eq_sum]
    change ∑ x ∈ P.support, P.coeff x * (χ (r.val : ZMod d)) ^ x = 0
    have hsub_sum : (∑ x ∈ P.support, P.coeff x * (χ (r.val : ZMod d)) ^ x) =
        ∑ x ∈ B_set, P.coeff x * (χ (r.val : ZMod d)) ^ x := by
      apply Finset.sum_subset hsupp
      intro x _ hxnot
      rw [Polynomial.notMem_support_iff.mp hxnot, zero_mul]
    rw [hsub_sum, ← hann r]
    apply Finset.sum_congr rfl
    intro x _
    have hpow : (χ (r.val : ZMod d)) ^ x = χ (((r.val * x : ℕ) : ZMod d)) := by
      rw [← SharedDecoders.character_nat_mul χ (r.val : ZMod d) x, Nat.cast_mul]
    rw [hpow]
  let H := SharedDecoders.bandRowSpace (b := b) χ p₂ k
  have hker_H := columnAmbient_aeval_ker_finrank_le H hP_ne
  have hdim_H : finrank E H ≤ b * M₂ * k := by
    have h := SharedDecoders.bandRowSpace_finrank_le (b := b) χ p₂ k
    have hcard_fin : Fintype.card (Fin M₂) * k * b = b * M₂ * k := by
      simp [Fintype.card_fin]; ring
    exact h.trans_eq hcard_fin
  exact ⟨P, hP_ne, hdeg_diam, hdeg_L₀, hsupp, heval, hann,
    hker_H.trans (Nat.mul_le_mul hdim_H hdeg_L₀)⟩

/-! ### 3. Single-Class Second Stage (`M₂ = 1`) & Explicit Quantitative Constants -/

/-- **Specialization of Theorem 2B to `M₂ = 1` (`Ω(b d log d)`).**
When the second stage uses a single shared decoder (`M₂ = 1`, so `2 M₂ - 1 = 1`), any two-stage
linear class-uniform approximation to `swapLinear F` over an admissible field (`(d : F) ≠ 0`)
suffers rank error at least `c * b * d * log d`. -/
theorem theorem2B_OneSecondStage_OmegaLog (M₁ : ℕ) (hM₁ : 1 ≤ M₁) :
    ∃ (c : ℝ) (D₀ : ℕ), 0 < c ∧ 2 ≤ D₀ ∧
      ∀ (F : Type*) [Field F] (d b : ℕ) [NeZero d]
        (p₁ : ZMod d → Fin M₁) (p₂ : ZMod d → Fin 1)
        (K₁ K₂ : State d (Fin b → F) →ₗ[F] State d (Fin b → F)),
        (d : F) ≠ 0 →
        D₀ ≤ d →
        1 ≤ b →
        ClassUniform p₁ K₁ →
        ClassUniform p₂ K₂ →
        c * (b : ℝ) * (d : ℝ) * Real.log (d : ℝ) ≤
          (finrank F (LinearMap.range (swapLinear F (d := d) (A := Fin b → F) - K₂.comp K₁)) : ℝ) := by
  obtain ⟨c, D₀', hc_pos, hbound⟩ := theorem2B_TwoStageLogPowerRankDeficit M₁ 1 hM₁ le_rfl
  refine ⟨c, max D₀' 2, hc_pos, le_max_right D₀' 2, ?_⟩
  intro F _ d b _ p₁ p₂ K₁ K₂ hd hdD₀ hb hK₁ hK₂
  have h := hbound F d b p₁ p₂ K₁ K₂ hd ((le_max_left D₀' 2).trans hdD₀) hb hK₁ hK₂
  have hexp : ((1 : ℝ) / (2 * ((1 : ℕ) : ℝ) - 1)) = 1 := by norm_num
  rwa [hexp, Real.rpow_one] at h

/-- Explicit quantitative constant `c(M₁, M₂)` for Theorem 2B extracted from the iterated
Kővári–Sós–Turán recurrence:
`c(M₁, M₂) = 1 / (144 * (log (16 M₁ M₂))^(1 / (2 M₂ - 1)))`. -/
noncomputable def theorem2BExplicitConst (M₁ M₂ : ℕ) : ℝ :=
  1 / (144 * (Real.log (16 * (M₁ : ℝ) * (M₂ : ℝ))) ^ ((1 : ℝ) / (2 * (M₂ : ℝ) - 1)))

/-- Explicit quantitative dimension threshold `D₀(M₁, M₂)` for Theorem 2B:
`D₀(M₁, M₂) = max (4 * M₂) (⌈exp(36^(2 M₂ - 1) * log(16 M₁ M₂))⌉ + 2)`. -/
noncomputable def theorem2BExplicitThreshold (M₁ M₂ : ℕ) : ℕ :=
  max (4 * M₂)
    (Nat.ceil (Real.exp (((36 ^ (2 * M₂ - 1) : ℕ) : ℝ) *
      Real.log (16 * (M₁ : ℝ) * (M₂ : ℝ)))) + 2)

/-- Exact integer-power simplification of `theorem2BExplicitThreshold M₁ M₂` for `1 ≤ M₁` and `1 ≤ M₂`. -/
theorem theorem2BExplicitThreshold_eq_pow {M₁ M₂ : ℕ} (hM₁ : 1 ≤ M₁) (hM₂ : 1 ≤ M₂) :
    theorem2BExplicitThreshold M₁ M₂ =
      max (4 * M₂) ((16 * M₁ * M₂) ^ (36 ^ (2 * M₂ - 1)) + 2) := by
  unfold theorem2BExplicitThreshold
  have hpos : (0 : ℝ) < ((16 * M₁ * M₂ : ℕ) : ℝ) := by
    exact_mod_cast (by nlinarith : 0 < 16 * M₁ * M₂)
  have hexp :
      Real.exp (((36 ^ (2 * M₂ - 1) : ℕ) : ℝ) * Real.log (16 * (M₁ : ℝ) * (M₂ : ℝ))) =
        (((16 * M₁ * M₂) ^ (36 ^ (2 * M₂ - 1)) : ℕ) : ℝ) := by
    have hcast : (16 : ℝ) * (M₁ : ℝ) * (M₂ : ℝ) = ((16 * M₁ * M₂ : ℕ) : ℝ) := by push_cast; ring
    rw [hcast, ← Real.log_pow, Real.exp_log (pow_pos hpos _)]
    push_cast
    rfl
  rw [hexp, Nat.ceil_natCast]

/-- Strict positivity of `theorem2BExplicitConst M₁ M₂` for `1 ≤ M₁` and `1 ≤ M₂`. -/
theorem theorem2BExplicitConst_pos {M₁ M₂ : ℕ} (hM₁ : 1 ≤ M₁) (hM₂ : 1 ≤ M₂) :
    0 < theorem2BExplicitConst M₁ M₂ := by
  unfold theorem2BExplicitConst
  have hM₀_gt1 : (1 : ℝ) < 16 * (M₁ : ℝ) * (M₂ : ℝ) := by
    have hnat : 1 < 16 * M₁ * M₂ := by nlinarith
    exact_mod_cast hnat
  have hlog_pos : 0 < Real.log (16 * (M₁ : ℝ) * (M₂ : ℝ)) := Real.log_pos hM₀_gt1
  have hrpow_pos : 0 < (Real.log (16 * (M₁ : ℝ) * (M₂ : ℝ))) ^
      ((1 : ℝ) / (2 * (M₂ : ℝ) - 1)) :=
    Real.rpow_pos_of_pos hlog_pos _
  positivity

/-- **Theorem 2B with Explicit `(M₁, M₂)` Constant & Threshold.** -/
theorem theorem2B_ExplicitConstant
    (M₁ M₂ : ℕ) (hM₁ : 1 ≤ M₁) (hM₂ : 1 ≤ M₂)
    (F : Type*) [Field F] (d b : ℕ) [NeZero d]
    (p₁ : ZMod d → Fin M₁) (p₂ : ZMod d → Fin M₂)
    (K₁ K₂ : State d (Fin b → F) →ₗ[F] State d (Fin b → F))
    (hd : (d : F) ≠ 0)
    (hdD₀ : theorem2BExplicitThreshold M₁ M₂ ≤ d)
    (hb : 1 ≤ b)
    (hK₁ : ClassUniform p₁ K₁)
    (hK₂ : ClassUniform p₂ K₂) :
    theorem2BExplicitConst M₁ M₂ * (b : ℝ) * (d : ℝ) *
        (Real.log (d : ℝ)) ^ ((1 : ℝ) / (2 * (M₂ : ℝ) - 1)) ≤
      (finrank F (LinearMap.range (swapLinear F (d := d) (A := Fin b → F) - K₂.comp K₁)) : ℝ) := by
  classical
  let n : ℕ := 2 * M₂ - 1
  have hn_pos : 1 ≤ n := by omega
  have hn_cast : (n : ℝ) = 2 * (M₂ : ℝ) - 1 := by
    dsimp [n]; rw [Nat.cast_sub (by omega : 1 ≤ 2 * M₂)]; push_cast; ring
  let M₀ : ℕ := 16 * M₁ * M₂
  have hM₀_cast : (M₀ : ℝ) = 16 * (M₁ : ℝ) * (M₂ : ℝ) := by dsimp [M₀]; push_cast; ring
  have hM₀_gt1 : (1 : ℝ) < (M₀ : ℝ) := by exact_mod_cast (by dsimp [M₀]; nlinarith : 1 < M₀)
  have hlogM₀_pos : 0 < Real.log (M₀ : ℝ) := Real.log_pos hM₀_gt1
  let A_exp : ℝ := ((18 ^ n : ℕ) : ℝ) * Real.log (M₀ : ℝ)
  have h18_pos : (0 : ℝ) < ((18 ^ n : ℕ) : ℝ) := by exact_mod_cast (Nat.pow_pos (by omega))
  have hA_pos : 0 < A_exp := mul_pos h18_pos hlogM₀_pos
  let α : ℝ := (1 : ℝ) / (2 * (M₂ : ℝ) - 1)
  have hn_real_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
  have hα_eq : α = (1 : ℝ) / (n : ℝ) := by dsimp [α]; rw [← hn_cast]
  have hα_pos : 0 < α := by rw [hα_eq]; exact div_pos one_pos hn_real_pos
  have hd4 : 4 * M₂ ≤ d := (le_max_left _ _).trans hdD₀
  have hd_ceil : Nat.ceil (Real.exp (((36 ^ n : ℕ) : ℝ) * Real.log (M₀ : ℝ))) + 2 ≤ d := by
    have hthr := (le_max_right (4 * M₂) _).trans hdD₀
    simpa [n, hM₀_cast] using hthr
  have h36_eq : ((2 ^ n : ℕ) : ℝ) * A_exp = ((36 ^ n : ℕ) : ℝ) * Real.log (M₀ : ℝ) := by
    dsimp [A_exp]
    have hpow : (2 ^ n) * (18 ^ n) = 36 ^ n := by rw [← mul_pow]; norm_num
    calc
      ((2 ^ n : ℕ) : ℝ) * (((18 ^ n : ℕ) : ℝ) * Real.log (M₀ : ℝ))
          = (((2 ^ n * 18 ^ n : ℕ) : ℝ)) * Real.log (M₀ : ℝ) := by push_cast; ring
      _ = ((36 ^ n : ℕ) : ℝ) * Real.log (M₀ : ℝ) := by rw [hpow]
  have hd_exp : Real.exp (((2 ^ n : ℕ) : ℝ) * A_exp) ≤ (d : ℝ) := by
    rw [h36_eq]
    exact (Nat.le_ceil _).trans (by exact_mod_cast (by omega : Nat.ceil _ ≤ d))
  have hd_real_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  let L : ℝ := Real.log (d : ℝ)
  have hL_ge : ((2 ^ n : ℕ) : ℝ) * A_exp ≤ L := by
    rw [← Real.log_exp (((2 ^ n : ℕ) : ℝ) * A_exp)]
    exact Real.log_le_log (Real.exp_pos _) hd_exp
  have h2n_pos : (0 : ℝ) < ((2 ^ n : ℕ) : ℝ) := by exact_mod_cast (Nat.pow_pos (by omega))
  have hL_pos : 0 < L := lt_of_lt_of_le (mul_pos h2n_pos hA_pos) hL_ge
  have hdiv_ge : (2 : ℝ) ^ n ≤ L / A_exp := by rw [le_div_iff₀ hA_pos]; simpa using hL_ge
  let x : ℝ := (L / A_exp) ^ α
  have hx_ge2 : 2 ≤ x := by
    have hrpow := Real.rpow_le_rpow (by positivity) hdiv_ge hα_pos.le
    have h2 : ((2 : ℝ) ^ n) ^ α = 2 := by
      rw [hα_eq, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
        mul_one_div_cancel hn_real_pos.ne', Real.rpow_one]
    rwa [h2] at hrpow
  let k : ℕ := Nat.floor x
  have hk_pos : 1 ≤ k := Nat.le_floor (by norm_num; linarith)
  have hk_half : x / 2 ≤ (k : ℝ) := by
    have h1 : x - 1 ≤ (k : ℝ) := (Nat.sub_one_lt_floor x).le
    linarith
  have hk_pow_le : A_exp * (k : ℝ) ^ n ≤ L := by
    have hkn : (k : ℝ) ^ n ≤ L / A_exp := by
      calc
        (k : ℝ) ^ n ≤ x ^ n := pow_le_pow_left₀ (Nat.cast_nonneg k) (Nat.floor_le (by linarith)) n
        _ = (L / A_exp) ^ (α * (n : ℝ)) := by
            rw [← Real.rpow_natCast x, ← Real.rpow_mul (div_pos hL_pos hA_pos).le]
        _ = L / A_exp := by rw [hα_eq, one_div_mul_cancel hn_real_pos.ne', Real.rpow_one]
    exact (mul_le_mul_of_nonneg_left hkn hA_pos.le).trans_eq (mul_div_cancel₀ L hA_pos.ne')
  have hM₀_pow_le_d : M₀ ^ (18 ^ n * k ^ n) ≤ d := by
    have hreal : ((M₀ ^ (18 ^ n * k ^ n) : ℕ) : ℝ) ≤ (d : ℝ) := by
      calc
        ((M₀ ^ (18 ^ n * k ^ n) : ℕ) : ℝ) = (M₀ : ℝ) ^ (18 ^ n * k ^ n) := by norm_cast
        _ = Real.exp (((18 ^ n * k ^ n : ℕ) : ℝ) * Real.log (M₀ : ℝ)) := by
            rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by positivity), mul_comm]
        _ = Real.exp (A_exp * (k : ℝ) ^ n) := by congr 1; dsimp [A_exp]; push_cast; ring
        _ ≤ Real.exp L := Real.exp_le_exp.mpr hk_pow_le
        _ = (d : ℝ) := Real.exp_log hd_real_pos
    exact_mod_cast hreal
  have hrec_bound : 16 * M₂ * (k + 1) * sumsetRecFactor M₁ M₂ k n ≤ d := by
    have hk_add_le : k + 1 ≤ M₀ ^ (k ^ n) :=
      LE.le.trans (Nat.lt_two_pow_self : k + 1 ≤ 2 ^ k)
        ((Nat.pow_le_pow_left (by dsimp [M₀]; nlinarith : 2 ≤ M₀) k).trans
          (Nat.pow_le_pow_right (by dsimp [M₀]; nlinarith : 1 ≤ M₀)
            (Nat.le_self_pow (by omega : n ≠ 0) k)))
    have hR_le : sumsetRecFactor M₁ M₂ k n ≤ M₀ ^ (9 ^ n * k ^ n) := by
      have hexp : 3 ^ n * (k + 2) ^ n ≤ 9 ^ n * k ^ n := by
        calc
          3 ^ n * (k + 2) ^ n ≤ 3 ^ n * (3 * k) ^ n :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega : k + 2 ≤ 3 * k) n)
          _ = (3 * 3) ^ n * k ^ n := by rw [mul_pow, ← mul_assoc, ← mul_pow]
          _ = 9 ^ n * k ^ n := by norm_num
      exact (sumsetRecFactor_upper (k := k) hM₁ hM₂ n).trans
        (Nat.pow_le_pow_right (by dsimp [M₀]; nlinarith : 1 ≤ M₀) hexp)
    have h16_le : 16 * M₂ ≤ M₀ ^ 1 := by rw [pow_one]; dsimp [M₀]; nlinarith
    have hexp_sum : 1 + k ^ n + 9 ^ n * k ^ n ≤ 18 ^ n * k ^ n := by
      have hkn1 : 1 ≤ k ^ n := Nat.one_le_pow n k hk_pos
      have h9ge : 9 ≤ 9 ^ n := (pow_one 9).symm.le.trans (Nat.pow_le_pow_right (by omega) hn_pos)
      have h2ge : 2 ≤ 2 ^ n := (pow_one 2).symm.le.trans (Nat.pow_le_pow_right (by omega) hn_pos)
      have h2_9 : 2 + 9 ^ n ≤ 18 ^ n := by
        calc
          2 + 9 ^ n ≤ 2 * 9 ^ n := by omega
          _ ≤ 2 ^ n * 9 ^ n := Nat.mul_le_mul_right _ h2ge
          _ = 18 ^ n := by rw [← mul_pow]; norm_num
      calc
        1 + k ^ n + 9 ^ n * k ^ n ≤ (2 + 9 ^ n) * k ^ n := by nlinarith
        _ ≤ 18 ^ n * k ^ n := Nat.mul_le_mul_right _ h2_9
    calc
      16 * M₂ * (k + 1) * sumsetRecFactor M₁ M₂ k n
          ≤ M₀ ^ 1 * M₀ ^ (k ^ n) * M₀ ^ (9 ^ n * k ^ n) :=
            Nat.mul_le_mul (Nat.mul_le_mul h16_le hk_add_le) hR_le
      _ = M₀ ^ (1 + k ^ n + 9 ^ n * k ^ n) := by rw [← pow_add, ← pow_add]
      _ ≤ M₀ ^ (18 ^ n * k ^ n) := Nat.pow_le_pow_right (by dsimp [M₀]; nlinarith) hexp_sum
      _ ≤ d := hM₀_pow_le_d
  let fiber : Fin M₁ → Finset ℕ := fun m =>
    (Finset.range d).filter (fun c => p₁ (c : ZMod d) = m)
  have hex_m₁ : ∃ m₁ : Fin M₁, d ≤ M₁ * (fiber m₁).card := by
    by_contra hall
    have hall' : ∀ m ∈ (Finset.univ : Finset (Fin M₁)), M₁ * (fiber m).card < d := by
      intro m _; by_contra hge; exact hall ⟨m, by omega⟩
    have hsum_lt := Finset.sum_lt_sum_of_nonempty ⟨⟨0, by omega⟩, Finset.mem_univ _⟩ hall'
    have hfiber_sum : d = ∑ m : Fin M₁, (fiber m).card := by
      simpa [fiber] using Finset.card_eq_sum_card_fiberwise
        (f := fun c : ℕ => p₁ (c : ZMod d)) (s := Finset.range d) (t := Finset.univ)
        (fun _ _ => Finset.mem_univ _)
    rw [← Finset.mul_sum, ← hfiber_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul] at hsum_lt
    omega
  obtain ⟨m₁, hm₁_card⟩ := hex_m₁
  obtain ⟨A_n, B, hAn_sub, hAn_card, hB_props, hAn_sum⟩ :=
    iterated_sumset_extract_from_finset hM₁ hM₂ hk_pos hd4 (fiber m₁)
      (fun u hu => Finset.mem_range.mp (Finset.mem_filter.mp hu).1) hm₁_card n hrec_bound
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
  have hk_le_An : k ≤ A_n.card :=
    Nat.le_of_mul_le_mul_left (hk_le_rec.trans (hrec_bound.trans hAn_card)) hRn_pos
  obtain ⟨J_nat, hJ_sub, hJ_card⟩ := Finset.exists_subset_card_eq hk_le_An
  let J₀ : Finset (ZMod d) := J_nat.image (fun u : ℕ => (u : ZMod d))
  have hJ_inj : Set.InjOn (fun u : ℕ => (u : ZMod d)) (J_nat : Set ℕ) := by
    intro u₁ hu₁ u₂ hu₂ heq
    have hlt₁ : u₁ < d := Finset.mem_range.mp (Finset.mem_filter.mp (hAn_sub (hJ_sub hu₁))).1
    have hlt₂ : u₂ < d := Finset.mem_range.mp (Finset.mem_filter.mp (hAn_sub (hJ_sub hu₂))).1
    simpa [ZMod.val_natCast, Nat.mod_eq_of_lt hlt₁, Nat.mod_eq_of_lt hlt₂] using
      congrArg ZMod.val heq
  have hunshift : HasUnshiftedMonochromaticSumset p₁ m₁ k (d / (4 * M₂)) J₀ B := by
    refine ⟨by rw [Finset.card_image_of_injOn hJ_inj, hJ_card], hB_props, ?_⟩
    intro c₀ hc₀ bvec hbvec
    rcases Finset.mem_image.mp hc₀ with ⟨u₀, hu₀, rfl⟩
    have hp := (Finset.mem_filter.mp (hAn_sum u₀ (hJ_sub hu₀) bvec hbvec)).2
    have hcast : ((u₀ + ∑ t : Fin n, bvec t : ℕ) : ZMod d) =
        (u₀ : ZMod d) + ∑ t : Fin n, (bvec t : ZMod d) := by push_cast; rfl
    rwa [← hcast]
  obtain ⟨J₀_tilde, B_tilde, hBt, _, _, hrank⟩ :=
    unshiftedToShiftedSumset_intrinsicDiam hM₂ p₁ m₁ J₀ B hunshift
  have h4r : b * k * d ≤ 4 * finrank F
      (LinearMap.range (swapLinear F (d := d) (A := Fin b → F) - K₂.comp K₁)) :=
    (hrank F b p₂ K₁ K₂ hd hb hK₁ hK₂).2 (fun t => (hBt t).2.2.2)
  have hA_rpow : A_exp ^ α = 18 * (Real.log (M₀ : ℝ)) ^ α := by
    dsimp [A_exp]
    rw [Real.mul_rpow h18_pos.le hlogM₀_pos.le]
    have h18_rpow : (((18 ^ n : ℕ) : ℝ)) ^ α = 18 := by
      push_cast
      rw [hα_eq, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
        mul_one_div_cancel hn_real_pos.ne', Real.rpow_one]
    rw [h18_rpow]
  have hx_div8 : x / 8 = theorem2BExplicitConst M₁ M₂ * L ^ α := by
    dsimp [x, theorem2BExplicitConst]
    rw [Real.div_rpow hL_pos.le hA_pos.le, hA_rpow, ← hM₀_cast]
    change L ^ α / (18 * Real.log (M₀ : ℝ) ^ α) / 8 =
      1 / (144 * Real.log (M₀ : ℝ) ^ α) * L ^ α
    ring
  have h4r_real : (b : ℝ) * (k : ℝ) * (d : ℝ) ≤
      4 * (finrank F (LinearMap.range (swapLinear F (d := d) (A := Fin b → F) - K₂.comp K₁)) : ℝ) :=
    by exact_mod_cast h4r
  have hbd_nonneg : 0 ≤ (b : ℝ) * (d : ℝ) := by positivity
  have hmul_k := mul_le_mul_of_nonneg_left hk_half hbd_nonneg
  calc
    theorem2BExplicitConst M₁ M₂ * (b : ℝ) * (d : ℝ) * L ^ α
        = (b : ℝ) * (d : ℝ) * (theorem2BExplicitConst M₁ M₂ * L ^ α) := by ring
    _ = ((b : ℝ) * (d : ℝ) * (x / 2)) / 4 := by
          rw [← hx_div8]
          ring
    _ ≤ ((b : ℝ) * (d : ℝ) * (k : ℝ)) / 4 := by linarith
    _ = ((b : ℝ) * (k : ℝ) * (d : ℝ)) / 4 := by ring
    _ ≤ (finrank F (LinearMap.range (swapLinear F (d := d) (A := Fin b → F) - K₂.comp K₁)) : ℝ) :=
          by linarith

/-! ### 4. Unconditional `d = 12` Primitive Root Witness & `bandRowSpace` Embedding -/

/-- Explicit primitive `12`-th root of unity `exp(2πi / 12) ∈ ℂ`. -/
noncomputable def zeta12 : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / 12)

/-- **Unconditional Primitive `12`-th Root Witness.** -/
theorem exists_primitive_twelfth_root_complex :
    zeta12 ^ 12 = 1 ∧ ∀ m : ℕ, 1 ≤ m → m < 12 → zeta12 ^ m ≠ 1 := by
  constructor
  · unfold zeta12
    rw [← Complex.exp_nat_mul]
    push_cast
    have h12 : (12 : ℂ) * (2 * Real.pi * Complex.I / 12) = 2 * Real.pi * Complex.I := by ring
    rw [h12, Complex.exp_two_pi_mul_I]
  · intro m hm1 hm12 hpow
    unfold zeta12 at hpow
    rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff] at hpow
    obtain ⟨n, hn⟩ := hpow
    let w : ℂ := 2 * Real.pi * Complex.I
    have hw : w ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
        Complex.I_ne_zero
    have hmul : ((m : ℂ) - 12 * (n : ℂ)) * w = 0 := by
      dsimp [w]
      linear_combination 12 * hn
    have hmn_c : (m : ℂ) = 12 * (n : ℂ) :=
      sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right hw)
    have hmn_z : (m : ℤ) = 12 * n := by exact_mod_cast hmn_c
    omega

/-- Explicit additive character `x ↦ zeta12 ^ x.val` on `ZMod 12`. -/
noncomputable def d12AddChar : AddChar (ZMod 12) ℂ where
  toFun x := zeta12 ^ x.val
  map_zero_eq_one' := by
    have hv : (0 : ZMod 12).val = 0 := by decide
    simp [hv]
  map_add_eq_mul' a b := by
    have hζ12 := exists_primitive_twelfth_root_complex.1
    have hmod : ∀ N : ℕ, zeta12 ^ N = zeta12 ^ (N % 12) := by
      intro N
      conv_lhs => rw [← Nat.div_add_mod N 12]
      rw [pow_add, pow_mul, hζ12, one_pow, one_mul]
    rw [ZMod.val_add, ← hmod (a.val + b.val), pow_add]

/-- `d12AddChar` is injective and primitive on `ZMod 12`. -/
theorem d12AddChar_injective_and_primitive :
    Function.Injective d12AddChar ∧ d12AddChar.IsPrimitive := by
  have hprim12 := exists_primitive_twelfth_root_complex.2
  have hne1 : ∀ x : ZMod 12, x ≠ 0 → d12AddChar x ≠ 1 := by
    intro x hx0
    have hv_pos : 1 ≤ x.val :=
      Nat.pos_of_ne_zero (fun hv0 => hx0 (ZMod.val_injective 12 (by simpa using hv0)))
    exact hprim12 x.val hv_pos (ZMod.val_lt x)
  refine ⟨?_, ?_⟩
  · intro a b hab
    by_contra hne
    have hsub_ne : a - b ≠ 0 := sub_ne_zero.mpr hne
    have h1 : d12AddChar (a - b) = 1 := by
      calc
        d12AddChar (a - b) = d12AddChar a * d12AddChar (-b) := by
          rw [sub_eq_add_neg, d12AddChar.map_add_eq_mul]
        _ = d12AddChar b * d12AddChar (-b) := by rw [hab]
        _ = 1 := by rw [← d12AddChar.map_add_eq_mul, add_neg_cancel, d12AddChar.map_zero_eq_one]
    exact hne1 (a - b) hsub_ne h1
  · intro a ha0 hshift
    have heval := congrArg (fun ψ : AddChar (ZMod 12) ℂ => ψ 1) hshift
    simp only [AddChar.mulShift_apply, mul_one, AddChar.one_apply] at heval
    exact hne1 a ha0 heval

/-- **Unconditional `d = 12` Single-Class Band Realization.**
Unconditional witness combining `exists_primitive_twelfth_root_complex` with
`control_D12SingleClassAbstractBand` on the half-density set `J12 = {0, 1, 3, 4, 7, 9}`
(`J12.card = 6`). -/
theorem control_D12_UnconditionalExists :
    let J12 : Finset (ZMod 12) := {0, 1, 3, 4, 7, 9}
    J12.card = 6 ∧
    ∃ (W : Submodule ℂ (ZMod 12 → Fin 4 → ℂ))
      (L : (ZMod 12 → Fin 4 → ℂ) →ₗ[ℂ] (Fin 12 → ℂ)),
      finrank ℂ W = 24 ∧
      (∀ w ∈ W, (∀ c ∈ J12, L (cyclicChannelShift ℂ 12 4 c w) = 0) → w = 0) ∧
      ∀ a₀ a₁ : Fin 12 → ℂ,
        ∃ w ∈ W, ∀ c ∈ J12, L (cyclicChannelShift ℂ 12 4 c w) = a₀ + (zeta12 ^ c.val) • a₁ := by
  refine ⟨by decide, control_D12SingleClassAbstractBand zeta12
    exists_primitive_twelfth_root_complex.1 exists_primitive_twelfth_root_complex.2⟩

/-- Explicit shift-intertwining `ℂ`-linear equivalence between
`ColumnAmbient (bandRowSpace (b := 2) d12AddChar (fun _ => 0) 2)` and `ZMod 12 → Fin 4 → ℂ`,
together with the transported `24`-dimensional single-class band subspace on `J12`. -/
noncomputable def d12BandRowSpaceEquiv :
    SharedDecoders.ColumnAmbient
      (SharedDecoders.bandRowSpace (b := 2) d12AddChar (fun _ : ZMod 12 => (0 : Fin 1)) 2) ≃ₗ[ℂ]
      (ZMod 12 → Fin 4 → ℂ) := by
  let p0 : ZMod 12 → Fin 1 := fun _ => 0
  let PMap := SharedDecoders.bandPatternMap (b := 2) d12AddChar p0 2
  have hPMap_inj : Function.Injective PMap := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have hζ_ne1 : zeta12 - 1 ≠ 0 :=
      sub_ne_zero.mpr (by simpa [pow_one] using exists_primitive_twelfth_root_complex.2 1 le_rfl (by omega))
    funext j ν l
    have hj : j = 0 := Subsingleton.elim j 0
    subst hj
    have h0 := congrFun (congrFun ha 0) l
    have h1 := congrFun (congrFun ha 1) l
    change (∑ ν : Fin 2, d12AddChar ((ν.val : ZMod 12) * 0) * a 0 ν l) = 0 at h0
    change (∑ ν : Fin 2, d12AddChar ((ν.val : ZMod 12) * 1) * a 0 ν l) = 0 at h1
    simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one,
      zero_mul, one_mul, mul_one, d12AddChar.map_zero_eq_one] at h0 h1
    have hv1 : d12AddChar 1 = zeta12 := by
      change zeta12 ^ (1 : ZMod 12).val = zeta12
      have hv : (1 : ZMod 12).val = 1 := by decide
      rw [hv, pow_one]
    rw [hv1] at h1
    have hdiff : (zeta12 - 1) * a 0 1 l = 0 := by linear_combination h1 - h0
    have ha1 : a 0 1 l = 0 := (mul_eq_zero.mp hdiff).resolve_left hζ_ne1
    have ha0 : a 0 0 l = 0 := by linear_combination h0 - ha1
    fin_cases ν
    · exact ha0
    · exact ha1
  let eRange : (Fin 1 → Fin 2 → Fin 2 → ℂ) ≃ₗ[ℂ]
      SharedDecoders.bandRowSpace (b := 2) d12AddChar p0 2 :=
    LinearEquiv.ofInjective PMap hPMap_inj
  let eFin4 : (Fin 1 → Fin 2 → Fin 2 → ℂ) ≃ₗ[ℂ] (Fin 4 → ℂ) :=
    { toFun := fun g ch => g 0 ⟨ch.val / 2, by omega⟩ ⟨ch.val % 2, by omega⟩
      invFun := fun v _ ν l => v ⟨2 * ν.val + l.val, by omega⟩
      left_inv := fun g => by
        funext j ν l
        have hj : j = 0 := Subsingleton.elim j 0; subst hj
        fin_cases ν <;> fin_cases l <;> rfl
      right_inv := fun v => by
        funext ch
        fin_cases ch <;> rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let φ := eRange.symm.trans eFin4
  exact
    { toFun := fun x u => φ (x () u)
      invFun := fun y _ u => φ.symm (y u)
      left_inv := fun x => by funext u c; exact φ.symm_apply_apply (x u c)
      right_inv := fun y => by funext c; exact φ.apply_symm_apply (y c)
      map_add' := fun x y => by funext c; exact map_add φ (x () c) (y () c)
      map_smul' := fun r x => by funext c; exact map_smul φ r (x () c) }

/-- **Explicit `bandRowSpace` 4-Channel Equivalence & Relaxation Barrier.**
`d12BandRowSpaceEquiv` intertwines `SharedDecoders.channelRotation` with `cyclicChannelShift ℂ 12 4`
for every shift `c : ZMod 12`, transporting `control_D12_UnconditionalExists` directly into
`ColumnAmbient (bandRowSpace (b := 2) d12AddChar (fun _ => 0) 2)`. -/
theorem control_D12_BandRowSpaceChannelEquiv :
    let H := SharedDecoders.bandRowSpace (b := 2) d12AddChar (fun _ : ZMod 12 => (0 : Fin 1)) 2
    let J12 : Finset (ZMod 12) := {0, 1, 3, 4, 7, 9}
    (∀ (c : ZMod 12) (x : SharedDecoders.ColumnAmbient H),
      d12BandRowSpaceEquiv
        (SharedDecoders.channelRotation (F := ℂ) (I := Unit) (A := H) c x) =
        cyclicChannelShift ℂ 12 4 c (d12BandRowSpaceEquiv x)) ∧
    ∃ (W_band : Submodule ℂ (SharedDecoders.ColumnAmbient H))
      (L_band : SharedDecoders.ColumnAmbient H →ₗ[ℂ] (Fin 12 → ℂ)),
      finrank ℂ W_band = 24 ∧
      (∀ w ∈ W_band,
        (∀ c ∈ J12, L_band (SharedDecoders.channelRotation (F := ℂ) (I := Unit) (A := H) c w) = 0) →
          w = 0) ∧
      ∀ a₀ a₁ : Fin 12 → ℂ,
        ∃ w ∈ W_band, ∀ c ∈ J12,
          L_band (SharedDecoders.channelRotation (F := ℂ) (I := Unit) (A := H) c w) =
            a₀ + (d12AddChar c) • a₁ := by
  intro H J12
  have hintertwine : ∀ (c : ZMod 12) (x : SharedDecoders.ColumnAmbient H),
      d12BandRowSpaceEquiv
        (SharedDecoders.channelRotation (F := ℂ) (I := Unit) (A := H) c x) =
        cyclicChannelShift ℂ 12 4 c (d12BandRowSpaceEquiv x) := fun _ _ => rfl
  obtain ⟨_, W, L, hdimW, hinjW, hrealW⟩ := control_D12_UnconditionalExists
  let W_band : Submodule ℂ (SharedDecoders.ColumnAmbient H) :=
    W.map d12BandRowSpaceEquiv.symm.toLinearMap
  let L_band : SharedDecoders.ColumnAmbient H →ₗ[ℂ] (Fin 12 → ℂ) :=
    L.comp d12BandRowSpaceEquiv.toLinearMap
  have hdim_band : finrank ℂ W_band = 24 := by
    rw [d12BandRowSpaceEquiv.symm.finrank_map_eq W, hdimW]
  refine ⟨hintertwine, W_band, L_band, hdim_band, ?_, ?_⟩
  · rintro w ⟨y, hyW, rfl⟩ hz
    have hy0 : y = 0 := by
      apply hinjW y hyW
      intro c hc
      have hzc := hz c hc
      change L (d12BandRowSpaceEquiv
        (SharedDecoders.channelRotation (F := ℂ) (I := Unit) (A := H) c
          (d12BandRowSpaceEquiv.symm y))) = 0 at hzc
      rwa [hintertwine, d12BandRowSpaceEquiv.apply_symm_apply] at hzc
    simp [hy0]
  · intro a₀ a₁
    obtain ⟨y, hyW, hy_eval⟩ := hrealW a₀ a₁
    refine ⟨d12BandRowSpaceEquiv.symm y, ⟨y, hyW, rfl⟩, ?_⟩
    intro c hc
    change L (d12BandRowSpaceEquiv
      (SharedDecoders.channelRotation (F := ℂ) (I := Unit) (A := H) c
        (d12BandRowSpaceEquiv.symm y))) = a₀ + (d12AddChar c) • a₁
    rw [hintertwine, d12BandRowSpaceEquiv.apply_symm_apply, hy_eval c hc]
    rfl

end BoundedArityDecoders
