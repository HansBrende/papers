import BoundedArityDecoders.OperatorDuality
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Proofs — Part III.A: Anti-Diagonal Untwisting & Operator Entanglement Duality

Complete kernel-verified proofs for all eight claim specifications in
`BoundedArityDecoders.OperatorDuality`:
* `pairwiseShiftCollisionCharacterization`
* `antiDiagonalTensorSeparation`
* `operatorSchmidtRankSubmultiplicative`
* `operatorSchmidtRankSwap`
* `operatorSchmidtRankStoneShuffle`
* `stoneShufflePipelinePassLowerBound`
* `control_RowShearAndRowDiagonalAlternation`
* `control_SkewOneTimePadInformationTrap`
-/

namespace BoundedArityDecoders

open SharedDecoders Module
open scoped BigOperators

/-! ### 1. Pairwise Shift-Collision Characterization & Anti-Diagonal Tensor Separation -/

@[simp]
theorem antiDiagLinear_apply (F : Type*) [Semiring F] (d : ℕ) (A : Type*)
    [AddCommMonoid A] [Module F A] (X : State d A) (c a : ZMod d) :
    antiDiagLinear F d A X c a = X c (a - c) :=
  rfl

@[simp]
theorem fromAntiDiagLinear_apply (F : Type*) [Semiring F] (d : ℕ) (A : Type*)
    [AddCommMonoid A] [Module F A] (Z : State d A) (c j : ZMod d) :
    fromAntiDiagLinear F d A Z c j = Z c (j + c) :=
  rfl

@[simp]
theorem antiDiagRightShiftLinear_apply (F : Type*) [Semiring F] (d : ℕ) (A : Type*)
    [AddCommMonoid A] [Module F A] (t : ZMod d) (Z : State d A) (c a : ZMod d) :
    antiDiagRightShiftLinear F d A t Z c a = Z c (a + t) :=
  rfl

/-- Proof of `PairwiseShiftCollisionCharacterizationSpec`. -/
theorem pairwiseShiftCollisionCharacterization : PairwiseShiftCollisionCharacterizationSpec := by
  intro F _ d κ A _ _ p C
  constructor
  · rintro ⟨f, hf⟩ s Y hY hrotY c hp j
    have h1 := hf Y hY (c + s)
    have h2 := hf (rot s Y) hrotY c
    rw [rot_rot] at h2
    rw [← hp] at h1
    exact congrFun (h1.trans h2.symm) j
  · intro hcov
    classical
    let P (k : κ) (Z : State d A) : Prop :=
      ∃ X ∈ C, ∃ c : ZMod d, p c = k ∧ rot c X = Z
    let f : κ → State d A → (ZMod d → A) := fun k Z =>
      if h : P k Z then
        let X₀ := Classical.choose h
        let c₀ := Classical.choose (Classical.choose_spec h).2
        X₀ c₀
      else 0
    refine ⟨f, ?_⟩
    intro X₁ hX₁ c₁
    have hP : P (p c₁) (rot c₁ X₁) := ⟨X₁, hX₁, c₁, rfl, rfl⟩
    show X₁ c₁ = (if h : P (p c₁) (rot c₁ X₁) then _ else 0)
    rw [dite_eq_left hP]
    set X₂ := Classical.choose hP
    have hX₂_spec := Classical.choose_spec hP
    have hX₂ : X₂ ∈ C := hX₂_spec.1
    set c₂ := Classical.choose hX₂_spec.2
    obtain ⟨hp₂, hrot₂⟩ := Classical.choose_spec hX₂_spec.2
    have hshift : rot (-c₁ + c₂) X₂ = X₁ := by
      rw [← rot_rot, hrot₂, rot_neg_rot]
    have hrot_mem : rot (-c₁ + c₂) X₂ ∈ C := by
      rwa [hshift]
    have hc_sum : c₁ + (-c₁ + c₂) = c₂ := by abel
    have hp_eq : p c₁ = p (c₁ + (-c₁ + c₂)) := by rw [hc_sum, hp₂]
    funext j
    have hj := hcov (-c₁ + c₂) X₂ hX₂ hrot_mem c₁ hp_eq j
    rw [hc_sum] at hj
    have hj' : rot (-c₁ + c₂) X₂ c₁ j = X₂ c₁ (j + (-c₁ + c₂)) := rfl
    rw [← hj', hshift] at hj
    exact hj.symm

/-- Proof of `AntiDiagonalTensorSeparationSpec`. -/
theorem antiDiagonalTensorSeparation : AntiDiagonalTensorSeparationSpec := by
  intro F _ d κ A _ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext Z c a
    simp [sub_add_cancel]
  · ext X c j
    simp [add_sub_cancel_right]
  · intro t
    ext X c a
    simp [sub_add_eq_add_sub]
  · intro p E X
    constructor
    · intro hcov c c' a hrel
      induction hrel with
      | rel x y hxy =>
        obtain ⟨hp, δ, hδ, δ', hδ', hsum⟩ := hxy
        have hj := hcov x y δ δ' hδ hδ' hp hsum (a - x - δ)
        have e1 : a - x - δ + δ = a - x := by abel
        have e2 : a - x - δ + δ' = a - y := by
          have hsub : δ' - δ = x - y := by
            calc δ' - δ = (y + δ') - y - δ := by abel
              _ = (x + δ) - y - δ := by rw [hsum]
              _ = x - y := by abel
          calc a - x - δ + δ' = a - x + (δ' - δ) := by abel
            _ = a - x + (x - y) := by rw [hsub]
            _ = a - y := by abel
        simp only [antiDiagLinear_apply]
        rw [e1, e2] at hj
        exact hj.symm
      | refl _ => rfl
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
    · intro hconst c c' δ δ' hδ hδ' hp hsum j
      have hlink : SwapRigidity.Link p E c c' := ⟨hp, δ, hδ, δ', hδ', hsum⟩
      have h := hconst c c' (j + c + δ) (Relation.EqvGen.rel _ _ hlink)
      simp only [antiDiagLinear_apply] at h
      have e1 : j + c + δ - c = j + δ := by abel
      have e2 : j + c + δ - c' = j + δ' := by
        calc j + c + δ - c' = j + (c + δ) - c' := by abel
          _ = j + (c' + δ') - c' := by rw [hsum]
          _ = j + δ' := by abel
      rw [e1, e2] at h
      exact h.symm

/-! ### 2. Operator Schmidt Rank Infrastructure & Realignment Lower Bound -/

section SchmidtInfra

@[simp]
theorem gridSwapLinear_apply (F : Type*) [Semiring F] (d b : ℕ)
    (X : GridState F d b) (r c : Fin d) (ℓ : Fin b) :
    gridSwapLinear F d b X r c ℓ = X c r ℓ :=
  rfl

@[simp]
theorem rowShearLinear_apply (F : Type*) [Semiring F] (d b : ℕ) [NeZero d]
    (X : GridState F d b) (r c : Fin d) (ℓ : Fin b) :
    rowShearLinear F d b X r c ℓ = X r ⟨(c.val + r.val) % d, Nat.mod_lt _ (NeZero.pos d)⟩ ℓ :=
  rfl

@[simp]
theorem stoneShuffleGridLinear_succ_apply (F : Type*) [Semiring F] (m b : ℕ)
    (X : GridState F (2 ^ (m + 1)) b) (r' c' : Fin (2 ^ (m + 1))) (ℓ : Fin b) :
    stoneShuffleGridLinear F (m + 1) b X r' c' ℓ =
      X ⟨((c'.val % 2) * (2 ^ m) + r'.val / 2) % (2 ^ (m + 1)),
          Nat.mod_lt _ (Nat.two_pow_pos (m + 1))⟩
        ⟨((r'.val % 2) * (2 ^ m) + c'.val / 2) % (2 ^ (m + 1)),
          Nat.mod_lt _ (Nat.two_pow_pos (m + 1))⟩ ℓ :=
  rfl

@[simp]
theorem stoneUnshuffleGridLinear_succ_apply (F : Type*) [Semiring F] (m b : ℕ)
    (X : GridState F (2 ^ (m + 1)) b) (r c : Fin (2 ^ (m + 1))) (ℓ : Fin b) :
    stoneUnshuffleGridLinear F (m + 1) b X r c ℓ =
      X ⟨(2 * r.val + c.val / (2 ^ m)) % (2 ^ (m + 1)),
          Nat.mod_lt _ (Nat.two_pow_pos (m + 1))⟩
        ⟨(2 * c.val + r.val / (2 ^ m)) % (2 ^ (m + 1)),
          Nat.mod_lt _ (Nat.two_pow_pos (m + 1))⟩ ℓ :=
  rfl

/-- Monotonicity of `HasOperatorSchmidtRankLe` in `R`. -/
theorem HasOperatorSchmidtRankLe.mono {F : Type*} [Semiring F] {d b : ℕ}
    {K : GridState F d b →ₗ[F] GridState F d b} {R₁ R₂ : ℕ}
    (h : HasOperatorSchmidtRankLe K R₁) (hle : R₁ ≤ R₂) :
    HasOperatorSchmidtRankLe K R₂ := by
  obtain ⟨A, B, hAB⟩ := h
  refine ⟨fun i => if hi : i.val < R₁ then A ⟨i.val, hi⟩ else 0,
          fun i => if hi : i.val < R₁ then B ⟨i.val, hi⟩ else 0, ?_⟩
  intro X r c ℓ
  rw [hAB X r c ℓ]
  refine Finset.sum_of_injOn
    (fun i : Fin R₁ => (⟨i.val, lt_of_lt_of_le i.isLt hle⟩ : Fin R₂))
    (fun _ _ _ _ hEq => Fin.ext (congrArg (Fin.val (n := R₂)) hEq))
    (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) ?_ ?_
  · intro j _ hj
    have hnot : ¬ j.val < R₁ := by
      intro hlt
      exact hj ⟨⟨j.val, hlt⟩, Finset.mem_coe.2 (Finset.mem_univ _), Fin.ext rfl⟩
    simp [hnot]
  · intro i _
    simp [i.isLt]

/-- Embedding a single row vector `v` into row `r'` of `GridState F d b` (zeros elsewhere). -/
def singleRowLinear (F : Type*) [Semiring F] (d b : ℕ) (r' : Fin d) :
    (Fin d → Fin b → F) →ₗ[F] GridState F d b where
  toFun v r := if r = r' then v else 0
  map_add' u v := by
    funext r c ℓ
    by_cases h : r = r' <;> simp [h]
  map_smul' a v := by
    funext r c ℓ
    by_cases h : r = r' <;> simp [h]

@[simp]
theorem singleRowLinear_apply (F : Type*) [Semiring F] (d b : ℕ) (r' : Fin d)
    (v : Fin d → Fin b → F) (r : Fin d) :
    singleRowLinear F d b r' v r = if r = r' then v else 0 :=
  rfl

/-- The `(r, r')` operator block `v ↦ (K (singleRowLinear r' v)) r` in `End_F(F^d_col ⊗ F^b)`. -/
def rowBlockOp {F : Type*} [Semiring F] {d b : ℕ}
    (K : GridState F d b →ₗ[F] GridState F d b) (r r' : Fin d) :
    (Fin d → Fin b → F) →ₗ[F] (Fin d → Fin b → F) :=
  (LinearMap.proj (R := F) (φ := fun _ : Fin d => Fin d → Fin b → F) r).comp
    (K.comp (singleRowLinear F d b r'))

@[simp]
theorem rowBlockOp_apply {F : Type*} [Semiring F] {d b : ℕ}
    (K : GridState F d b →ₗ[F] GridState F d b) (r r' : Fin d)
    (v : Fin d → Fin b → F) (c : Fin d) (ℓ : Fin b) :
    rowBlockOp K r r' v c ℓ = K (singleRowLinear F d b r' v) r c ℓ :=
  rfl

theorem sum_smul_rowBlockOp_apply {F : Type*} [CommSemiring F] {d b : ℕ}
    (K : GridState F d b →ₗ[F] GridState F d b) {ι : Type*} [Fintype ι]
    (p : ι → Fin d × Fin d) (coeff : ι → F)
    (v : Fin d → Fin b → F) (c : Fin d) (ℓ : Fin b) :
    (∑ idx : ι, coeff idx • rowBlockOp K (p idx).1 (p idx).2) v c ℓ =
      ∑ idx : ι, coeff idx * K (singleRowLinear F d b (p idx).2 v) (p idx).1 c ℓ := by
  simp [LinearMap.sum_apply, Finset.sum_apply]

/-- **General Realignment Lower-Bound Lemma.**
If `ι` indexes a linearly independent family of `(r, r')` row-block operators of `K`, then
any Operator Schmidt Rank bound `R` for `K` satisfies `Fintype.card ι ≤ R`. -/
theorem card_le_of_hasOperatorSchmidtRankLe {F : Type*} [Field F] {d b R : ℕ}
    {K : GridState F d b →ₗ[F] GridState F d b}
    (hK : HasOperatorSchmidtRankLe K R)
    {ι : Type*} [Fintype ι] (p : ι → Fin d × Fin d)
    (hinj : ∀ coeff : ι → F,
      (∑ idx : ι, coeff idx • rowBlockOp K (p idx).1 (p idx).2) = 0 →
      ∀ idx : ι, coeff idx = 0) :
    Fintype.card ι ≤ R := by
  obtain ⟨A, B, hAB⟩ := hK
  let W := (Fin d → Fin b → F) →ₗ[F] (Fin d → Fin b → F)
  let Φ : (Fin R → F) →ₗ[F] W :=
    { toFun := fun w => ∑ i : Fin R, w i • B i
      map_add' := fun u v => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun a u => by simp [Finset.smul_sum, smul_smul] }
  have hmem : ∀ r r' : Fin d, rowBlockOp K r r' ∈ LinearMap.range Φ := by
    intro r r'
    refine ⟨fun i => A i r r', ?_⟩
    apply LinearMap.ext
    intro v
    funext c ℓ
    change (∑ i : Fin R, A i r r' • B i) v c ℓ = K (singleRowLinear F d b r' v) r c ℓ
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul]
    rw [hAB (singleRowLinear F d b r' v) r c ℓ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single r']
    · simp
    · intro r'' _ hr''
      have h0 : singleRowLinear F d b r' v r'' = 0 := ite_eq_right hr''
      rw [h0, map_zero]
      simp
    · intro h
      exact absurd (Finset.mem_univ r') h
  let Ψ : (ι → F) →ₗ[F] LinearMap.range Φ :=
    { toFun := fun coeff =>
        ⟨∑ idx : ι, coeff idx • rowBlockOp K (p idx).1 (p idx).2,
         Submodule.sum_mem _ fun idx _ => Submodule.smul_mem _ _ (hmem _ _)⟩
      map_add' := fun u v => Subtype.ext (by simp [add_smul, Finset.sum_add_distrib])
      map_smul' := fun a u => Subtype.ext (by simp [Finset.smul_sum, smul_smul]) }
  have hΨ_inj : Function.Injective Ψ := by
    rw [injective_iff_map_eq_zero]
    intro coeff h0
    have h0' : (∑ idx : ι, coeff idx • rowBlockOp K (p idx).1 (p idx).2) = 0 :=
      congrArg Subtype.val h0
    funext idx
    exact hinj coeff h0' idx
  have h1 : finrank F (ι → F) ≤ finrank F (LinearMap.range Φ) :=
    LinearMap.finrank_le_finrank_of_injective hΨ_inj
  have h2 := LinearMap.finrank_range_add_finrank_ker Φ
  rw [Module.finrank_fintype_fun_eq_card] at h1
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h2
  omega

end SchmidtInfra

/-! ### 3. Submultiplicativity & Unit-Rank Primitives -/

theorem isRowUniformColOp_rankLe_one {F : Type*} [Semiring F] {d b : ℕ}
    {K : GridState F d b →ₗ[F] GridState F d b} (hK : IsRowUniformColOp K) :
    HasOperatorSchmidtRankLe K 1 := by
  obtain ⟨B₀, hB₀⟩ := hK
  refine ⟨fun _ => 1, fun _ => B₀, ?_⟩
  intro X r c ℓ
  rw [Fin.sum_univ_one, Finset.sum_eq_single r]
  · simp [hB₀]
  · intro r' _ hr'
    simp [Matrix.one_apply_ne hr'.symm]
  · intro h
    exact absurd (Finset.mem_univ r) h

theorem isColUniformRowOp_rankLe_one {F : Type*} [Semiring F] {d b : ℕ}
    {K : GridState F d b →ₗ[F] GridState F d b} (hK : IsColUniformRowOp K) :
    HasOperatorSchmidtRankLe K 1 := by
  obtain ⟨A₀, hA₀⟩ := hK
  refine ⟨fun _ => A₀, fun _ => LinearMap.id, ?_⟩
  intro X r c ℓ
  rw [Fin.sum_univ_one, hA₀]
  rfl

theorem hasOperatorSchmidtRankLe_comp {F : Type*} [CommSemiring F] {d b R₁ R₂ : ℕ}
    {K₁ K₂ : GridState F d b →ₗ[F] GridState F d b}
    (h₁ : HasOperatorSchmidtRankLe K₁ R₁) (h₂ : HasOperatorSchmidtRankLe K₂ R₂) :
    HasOperatorSchmidtRankLe (K₂.comp K₁) (R₂ * R₁) := by
  obtain ⟨A₁, B₁, hAB₁⟩ := h₁
  obtain ⟨A₂, B₂, hAB₂⟩ := h₂
  let e := finProdFinEquiv (m := R₂) (n := R₁)
  refine ⟨fun k => A₂ (e.symm k).1 * A₁ (e.symm k).2,
          fun k => (B₂ (e.symm k).1).comp (B₁ (e.symm k).2), ?_⟩
  intro X r c ℓ
  have hrow₁ : ∀ r' : Fin d,
      K₁ X r' = ∑ j : Fin R₁, ∑ r'' : Fin d, A₁ j r' r'' • B₁ j (X r'') := by
    intro r'
    funext c' ℓ'
    rw [hAB₁ X r' c' ℓ']
    simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change K₂ (K₁ X) r c ℓ = _
  rw [hAB₂ (K₁ X) r c ℓ]
  have hreindex :
      (∑ k : Fin (R₂ * R₁), ∑ r'' : Fin d,
          (A₂ (e.symm k).1 * A₁ (e.symm k).2) r r'' *
            (((B₂ (e.symm k).1).comp (B₁ (e.symm k).2)) (X r'') c ℓ)) =
      ∑ i : Fin R₂, ∑ j : Fin R₁, ∑ r'' : Fin d,
          (A₂ i * A₁ j) r r'' * (((B₂ i).comp (B₁ j)) (X r'') c ℓ) :=
    (Fintype.sum_equiv e.symm
      (fun k : Fin (R₂ * R₁) => ∑ r'' : Fin d,
        (A₂ (e.symm k).1 * A₁ (e.symm k).2) r r'' *
          (((B₂ (e.symm k).1).comp (B₁ (e.symm k).2)) (X r'') c ℓ))
      (fun q : Fin R₂ × Fin R₁ => ∑ r'' : Fin d,
        (A₂ q.1 * A₁ q.2) r r'' * (((B₂ q.1).comp (B₁ q.2)) (X r'') c ℓ))
      (fun _ => rfl)).trans (Fintype.sum_prod_type _)
  rw [hreindex]
  refine Finset.sum_congr rfl fun i _ => ?_
  calc ∑ r' : Fin d, A₂ i r r' * (B₂ i (K₁ X r') c ℓ)
      = ∑ r' : Fin d, A₂ i r r' *
          (∑ j : Fin R₁, ∑ r'' : Fin d, A₁ j r' r'' * (B₂ i (B₁ j (X r'')) c ℓ)) := by
          refine Finset.sum_congr rfl fun r' _ => ?_
          rw [hrow₁ r', map_sum]
          simp [map_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    _ = ∑ r' : Fin d, ∑ j : Fin R₁, ∑ r'' : Fin d,
          A₂ i r r' * A₁ j r' r'' * (B₂ i (B₁ j (X r'')) c ℓ) := by
          refine Finset.sum_congr rfl fun r' _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun r'' _ => ?_
          ring
    _ = ∑ j : Fin R₁, ∑ r' : Fin d, ∑ r'' : Fin d,
          A₂ i r r' * A₁ j r' r'' * (B₂ i (B₁ j (X r'')) c ℓ) := Finset.sum_comm
    _ = ∑ j : Fin R₁, ∑ r'' : Fin d,
          (∑ r' : Fin d, A₂ i r r' * A₁ j r' r'') * (B₂ i (B₁ j (X r'')) c ℓ) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun r'' _ => ?_
          rw [Finset.sum_mul]
    _ = ∑ j : Fin R₁, ∑ r'' : Fin d,
          (A₂ i * A₁ j) r r'' * (((B₂ i).comp (B₁ j)) (X r'') c ℓ) := rfl

/-- Proof of `OperatorSchmidtRankSubmultiplicativeSpec`. -/
theorem operatorSchmidtRankSubmultiplicative : OperatorSchmidtRankSubmultiplicativeSpec := by
  intro F _ d b
  exact ⟨fun _ h => isRowUniformColOp_rankLe_one h,
         fun _ h => isColUniformRowOp_rankLe_one h,
         fun _ _ _ _ h₁ h₂ => hasOperatorSchmidtRankLe_comp h₁ h₂⟩

/-! ### 4. Exact Operator Schmidt Rank of Transpose `τ` -/

/-- Proof of `OperatorSchmidtRankSwapSpec`. -/
theorem operatorSchmidtRankSwap : OperatorSchmidtRankSwapSpec := by
  intro F _ d b _hd hb
  have hUpper : HasOperatorSchmidtRankLe (gridSwapLinear F d b) (d ^ 2) := by
    rw [sq]
    let e := finProdFinEquiv (m := d) (n := d)
    let Apair : Fin d × Fin d → Matrix (Fin d) (Fin d) F := fun p =>
      Matrix.of fun r r' => if r = p.1 ∧ r' = p.2 then 1 else 0
    let Bpair : Fin d × Fin d → ((Fin d → Fin b → F) →ₗ[F] (Fin d → Fin b → F)) :=
      fun p =>
        { toFun := fun v c ℓ => if c = p.2 then v p.1 ℓ else 0
          map_add' := fun u v => by
            funext c ℓ
            by_cases hc : c = p.2 <;> simp [hc]
          map_smul' := fun a v => by
            funext c ℓ
            by_cases hc : c = p.2 <;> simp [hc] }
    refine ⟨fun k => Apair (e.symm k), fun k => Bpair (e.symm k), ?_⟩
    intro X r c ℓ
    have hreindex :
        (∑ k : Fin (d * d), ∑ r' : Fin d,
            Apair (e.symm k) r r' * (Bpair (e.symm k) (X r') c ℓ)) =
        ∑ r₀ : Fin d, ∑ c₀ : Fin d, ∑ r' : Fin d,
            Apair (r₀, c₀) r r' * (Bpair (r₀, c₀) (X r') c ℓ) :=
      (Fintype.sum_equiv e.symm
        (fun k : Fin (d * d) => ∑ r' : Fin d,
          Apair (e.symm k) r r' * (Bpair (e.symm k) (X r') c ℓ))
        (fun p : Fin d × Fin d => ∑ r' : Fin d,
          Apair p r r' * (Bpair p (X r') c ℓ))
        (fun _ => rfl)).trans (Fintype.sum_prod_type _)
    rw [hreindex]
    rw [Finset.sum_eq_single r]
    · rw [Finset.sum_eq_single c]
      · rw [Finset.sum_eq_single c]
        · simp [Apair, Bpair]
        · intro r' _ hr'
          simp [Apair, hr']
        · intro h
          exact absurd (Finset.mem_univ c) h
      · intro c₀ _ hc₀
        refine Finset.sum_eq_zero fun r' _ => ?_
        simp [Bpair, hc₀.symm]
      · intro h
        exact absurd (Finset.mem_univ c) h
    · intro r₀ _ hr₀
      refine Finset.sum_eq_zero fun c₀ _ => Finset.sum_eq_zero fun r' _ => ?_
      simp [Apair, hr₀.symm]
    · intro h
      exact absurd (Finset.mem_univ r) h
  refine ⟨hUpper, ?_⟩
  intro R' hlt hR'
  let ℓ₀ : Fin b := ⟨0, hb⟩
  have hle : Fintype.card (Fin d × Fin d) ≤ R' := by
    refine card_le_of_hasOperatorSchmidtRankLe hR' (fun p => p) ?_
    intro coeff hsum idx₀
    let v : Fin d → Fin b → F := fun col ℓ => if col = idx₀.1 ∧ ℓ = ℓ₀ then 1 else 0
    have heval : (∑ idx : Fin d × Fin d,
        coeff idx • rowBlockOp (gridSwapLinear F d b) idx.1 idx.2) v idx₀.2 ℓ₀ = 0 := by
      rw [hsum]
      rfl
    rw [sum_smul_rowBlockOp_apply (gridSwapLinear F d b) (fun p => p)] at heval
    rw [Finset.sum_eq_single idx₀] at heval
    · simpa [v] using heval
    · intro idx _ hne
      simp only [gridSwapLinear_apply, singleRowLinear_apply]
      by_cases h2 : idx₀.2 = idx.2
      · have h1 : idx.1 ≠ idx₀.1 := by
          intro h1
          exact hne (Prod.ext h1 h2.symm)
        simp [h2, v, h1]
      · simp [h2]
    · intro h
      exact absurd (Finset.mem_univ idx₀) h
  rw [Fintype.card_prod, Fintype.card_fin, ← sq] at hle
  omega

/-! ### 5. Exact Operator Schmidt Rank of Stone's Shuffle `S` and Unshuffle `S⁻¹` -/

section StoneShuffleProofs

private lemma unshuffle_after_shuffle_idx {K r' c' : ℕ} (hK : 0 < K)
    (hr' : r' < 2 * K) (hc' : c' < 2 * K) :
    let r := ((c' % 2) * K + r' / 2) % (2 * K)
    let c := ((r' % 2) * K + c' / 2) % (2 * K)
    (2 * r + c / K) % (2 * K) = r' ∧ (2 * c + r / K) % (2 * K) = c' := by
  have hr'_div : r' / 2 < K := by omega
  have hc'_div : c' / 2 < K := by omega
  have aux : ∀ x y : ℕ, x < 2 * K → y < 2 * K → x / 2 < K → y / 2 < K →
      (2 * (((y % 2) * K + x / 2) % (2 * K)) + (((x % 2) * K + y / 2) % (2 * K)) / K) %
        (2 * K) = x := by
    intro x y hx _hy hx_div hy_div
    have hx_lt2K : x / 2 < 2 * K := by omega
    have hy_lt2K : y / 2 < 2 * K := by omega
    have hKx_lt2K : K + x / 2 < 2 * K := by omega
    have hKy_lt2K : K + y / 2 < 2 * K := by omega
    have hKy_div : (K + y / 2) / K = 1 := by
      rw [show K + y / 2 = y / 2 + 1 * K by ring,
          Nat.add_mul_div_right _ _ hK, Nat.div_eq_of_lt hy_div, zero_add]
    rcases Nat.mod_two_eq_zero_or_one x with hx2 | hx2 <;>
      rcases Nat.mod_two_eq_zero_or_one y with hy2 | hy2
    · rw [hx2, hy2]
      simp only [zero_mul, zero_add]
      rw [Nat.mod_eq_of_lt hx_lt2K, Nat.mod_eq_of_lt hy_lt2K,
          Nat.div_eq_of_lt hy_div, add_zero]
      have hx_eq : 2 * (x / 2) = x := by omega
      rw [hx_eq, Nat.mod_eq_of_lt hx]
    · rw [hx2, hy2]
      simp only [zero_mul, one_mul, zero_add]
      rw [Nat.mod_eq_of_lt hKx_lt2K, Nat.mod_eq_of_lt hy_lt2K,
          Nat.div_eq_of_lt hy_div, add_zero]
      have hx_eq : 2 * (K + x / 2) = x + 1 * (2 * K) := by omega
      rw [hx_eq, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx]
    · rw [hx2, hy2]
      simp only [zero_mul, one_mul, zero_add]
      rw [Nat.mod_eq_of_lt hx_lt2K, Nat.mod_eq_of_lt hKy_lt2K, hKy_div]
      have hx_eq : 2 * (x / 2) + 1 = x := by omega
      rw [hx_eq, Nat.mod_eq_of_lt hx]
    · rw [hx2, hy2]
      simp only [one_mul]
      rw [Nat.mod_eq_of_lt hKx_lt2K, Nat.mod_eq_of_lt hKy_lt2K, hKy_div]
      have hx_eq : 2 * (K + x / 2) + 1 = x + 1 * (2 * K) := by omega
      rw [hx_eq, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx]
  exact ⟨aux r' c' hr' hc' hr'_div hc'_div, aux c' r' hc' hr' hc'_div hr'_div⟩

private lemma two_mul_add_div_mod {u q : ℕ} (hq : q < 2) :
    (2 * u + q) % 2 = q ∧ (2 * u + q) / 2 = u := by
  omega

private lemma shuffle_after_unshuffle_idx {K r c : ℕ} (hK : 0 < K)
    (hr : r < 2 * K) (hc : c < 2 * K) :
    let r' := (2 * r + c / K) % (2 * K)
    let c' := (2 * c + r / K) % (2 * K)
    ((c' % 2) * K + r' / 2) % (2 * K) = r ∧ ((r' % 2) * K + c' / 2) % (2 * K) = c := by
  have aux : ∀ x y : ℕ, x < 2 * K → y < 2 * K →
      ((((2 * y + x / K) % (2 * K)) % 2) * K + ((2 * x + y / K) % (2 * K)) / 2) %
        (2 * K) = x := by
    intro x y hx hy
    set qx := x / K
    set rx := x % K
    set qy := y / K
    set ry := y % K
    have hqx : qx < 2 := Nat.div_lt_of_lt_mul (by omega)
    have hqy : qy < 2 := Nat.div_lt_of_lt_mul (by omega)
    have hrx : rx < K := Nat.mod_lt x hK
    have hry : ry < K := Nat.mod_lt y hK
    have hx_decomp : x = qx * K + rx := (Nat.div_add_mod' x K).symm
    have hy_decomp : y = qy * K + ry := (Nat.div_add_mod' y K).symm
    have h2x_lt : 2 * rx + qy < 2 * K := by omega
    have h2y_lt : 2 * ry + qx < 2 * K := by omega
    have h2x_mod : (2 * x + qy) % (2 * K) = 2 * rx + qy := by
      have e : 2 * x + qy = (2 * rx + qy) + qx * (2 * K) := by
        calc 2 * x + qy = 2 * (qx * K + rx) + qy := by rw [← hx_decomp]
          _ = (2 * rx + qy) + qx * (2 * K) := by ring
      rw [e, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h2x_lt]
    have h2y_mod : (2 * y + qx) % (2 * K) = 2 * ry + qx := by
      have e : 2 * y + qx = (2 * ry + qx) + qy * (2 * K) := by
        calc 2 * y + qx = 2 * (qy * K + ry) + qx := by rw [← hy_decomp]
          _ = (2 * ry + qx) + qy * (2 * K) := by ring
      rw [e, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h2y_lt]
    rw [h2x_mod, h2y_mod, (two_mul_add_div_mod hqx).1, (two_mul_add_div_mod hqy).2,
        ← hx_decomp, Nat.mod_eq_of_lt hx]
  exact ⟨aux r c hr hc, aux c r hc hr⟩

private lemma mul_two_pow_lt_succ {a m : ℕ} (ha : a < 2) :
    a * (2 ^ m) < 2 ^ (m + 1) := by
  have hK : 0 < 2 ^ m := Nat.two_pow_pos m
  have hd : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
  rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl <;> omega

/-- Proof of `OperatorSchmidtRankStoneShuffleSpec`. -/
theorem operatorSchmidtRankStoneShuffle : OperatorSchmidtRankStoneShuffleSpec := by
  intro F _ m b hb
  have hInv :
      (stoneShuffleGridLinear F m b).comp (stoneUnshuffleGridLinear F m b) = LinearMap.id ∧
      (stoneUnshuffleGridLinear F m b).comp (stoneShuffleGridLinear F m b) = LinearMap.id := by
    cases m with
    | zero =>
      exact ⟨rfl, rfl⟩
    | succ m' =>
      have hK : 0 < 2 ^ m' := Nat.two_pow_pos m'
      have hd_eq : 2 ^ (m' + 1) = 2 * 2 ^ m' := by ring
      constructor
      · apply LinearMap.ext
        intro X
        funext r' c' ℓ
        simp only [LinearMap.comp_apply, LinearMap.id_apply,
          stoneShuffleGridLinear_succ_apply, stoneUnshuffleGridLinear_succ_apply]
        have hr' : r'.val < 2 * 2 ^ m' := hd_eq ▸ r'.isLt
        have hc' : c'.val < 2 * 2 ^ m' := hd_eq ▸ c'.isLt
        obtain ⟨e1, e2⟩ := unshuffle_after_shuffle_idx hK hr' hc'
        have hF1 : (⟨(2 * (((c'.val % 2) * (2 ^ m') + r'.val / 2) % (2 ^ (m' + 1))) +
            (((r'.val % 2) * (2 ^ m') + c'.val / 2) % (2 ^ (m' + 1))) / (2 ^ m')) % (2 ^ (m' + 1)),
            Nat.mod_lt _ (Nat.two_pow_pos (m' + 1))⟩ : Fin (2 ^ (m' + 1))) = r' := by
          apply Fin.ext
          simpa [hd_eq] using e1
        have hF2 : (⟨(2 * (((r'.val % 2) * (2 ^ m') + c'.val / 2) % (2 ^ (m' + 1))) +
            (((c'.val % 2) * (2 ^ m') + r'.val / 2) % (2 ^ (m' + 1))) / (2 ^ m')) % (2 ^ (m' + 1)),
            Nat.mod_lt _ (Nat.two_pow_pos (m' + 1))⟩ : Fin (2 ^ (m' + 1))) = c' := by
          apply Fin.ext
          simpa [hd_eq] using e2
        rw [hF1, hF2]
      · apply LinearMap.ext
        intro X
        funext r c ℓ
        simp only [LinearMap.comp_apply, LinearMap.id_apply,
          stoneShuffleGridLinear_succ_apply, stoneUnshuffleGridLinear_succ_apply]
        have hr : r.val < 2 * 2 ^ m' := hd_eq ▸ r.isLt
        have hc : c.val < 2 * 2 ^ m' := hd_eq ▸ c.isLt
        obtain ⟨e1, e2⟩ := shuffle_after_unshuffle_idx hK hr hc
        have hF1 : (⟨(((2 * c.val + r.val / (2 ^ m')) % (2 ^ (m' + 1)) % 2) * (2 ^ m') +
            (2 * r.val + c.val / (2 ^ m')) % (2 ^ (m' + 1)) / 2) % (2 ^ (m' + 1)),
            Nat.mod_lt _ (Nat.two_pow_pos (m' + 1))⟩ : Fin (2 ^ (m' + 1))) = r := by
          apply Fin.ext
          simpa [hd_eq] using e1
        have hF2 : (⟨(((2 * r.val + c.val / (2 ^ m')) % (2 ^ (m' + 1)) % 2) * (2 ^ m') +
            (2 * c.val + r.val / (2 ^ m')) % (2 ^ (m' + 1)) / 2) % (2 ^ (m' + 1)),
            Nat.mod_lt _ (Nat.two_pow_pos (m' + 1))⟩ : Fin (2 ^ (m' + 1))) = c := by
          apply Fin.ext
          simpa [hd_eq] using e2
        rw [hF1, hF2]
  have hShuffleLe4 : HasOperatorSchmidtRankLe (stoneShuffleGridLinear F m b) 4 := by
    cases m with
    | zero =>
      have h1 : HasOperatorSchmidtRankLe (stoneShuffleGridLinear F 0 b) 1 :=
        isRowUniformColOp_rankLe_one ⟨LinearMap.id, fun _ _ => rfl⟩
      exact h1.mono (by omega)
    | succ m' =>
      have hd : 0 < 2 ^ (m' + 1) := Nat.two_pow_pos (m' + 1)
      let B : Fin 4 → ((Fin (2 ^ (m' + 1)) → Fin b → F) →ₗ[F] (Fin (2 ^ (m' + 1)) → Fin b → F)) :=
        fun i =>
          { toFun := fun v c' ℓ =>
              if c'.val % 2 = i.val % 2 then
                v ⟨((i.val / 2) * (2 ^ m') + c'.val / 2) % (2 ^ (m' + 1)), Nat.mod_lt _ hd⟩ ℓ
              else 0
            map_add' := fun u v => by
              funext c' ℓ
              by_cases hc : c'.val % 2 = i.val % 2 <;> simp [hc]
            map_smul' := fun a v => by
              funext c' ℓ
              by_cases hc : c'.val % 2 = i.val % 2 <;> simp [hc] }
      let A : Fin 4 → Matrix (Fin (2 ^ (m' + 1))) (Fin (2 ^ (m' + 1))) F := fun i =>
        Matrix.of fun r' r =>
          if r'.val % 2 = i.val / 2 ∧
             r.val = ((i.val % 2) * (2 ^ m') + r'.val / 2) % (2 ^ (m' + 1)) then 1 else 0
      refine ⟨A, B, ?_⟩
      intro X r' c' ℓ
      let i₀ : Fin 4 := ⟨2 * (r'.val % 2) + c'.val % 2, by omega⟩
      let r₀ : Fin (2 ^ (m' + 1)) :=
        ⟨((c'.val % 2) * (2 ^ m') + r'.val / 2) % (2 ^ (m' + 1)), Nat.mod_lt _ hd⟩
      have hi_div : i₀.val / 2 = r'.val % 2 := by
        show (2 * (r'.val % 2) + c'.val % 2) / 2 = r'.val % 2
        omega
      have hi_mod : i₀.val % 2 = c'.val % 2 := by
        show (2 * (r'.val % 2) + c'.val % 2) % 2 = c'.val % 2
        omega
      rw [Finset.sum_eq_single i₀]
      · rw [Finset.sum_eq_single r₀]
        · simp [A, B, r₀, hi_div, hi_mod]
        · intro r _ hr
          have hr_val : r.val ≠ ((i₀.val % 2) * (2 ^ m') + r'.val / 2) % (2 ^ (m' + 1)) := by
            rw [hi_mod]
            exact fun h => hr (Fin.ext h)
          simp [A, hr_val]
        · intro h
          exact absurd (Finset.mem_univ r₀) h
      · intro i _ hi
        refine Finset.sum_eq_zero fun r _ => ?_
        by_cases ha : r'.val % 2 = i.val / 2
        · have hb_ne : c'.val % 2 ≠ i.val % 2 := by
            intro hb_eq
            apply hi
            apply Fin.ext
            show i.val = 2 * (r'.val % 2) + c'.val % 2
            have := i.isLt
            omega
          simp [B, hb_ne]
        · simp [A, ha]
      · intro h
        exact absurd (Finset.mem_univ i₀) h
  have hUnshuffleLe4 : HasOperatorSchmidtRankLe (stoneUnshuffleGridLinear F m b) 4 := by
    cases m with
    | zero =>
      have h1 : HasOperatorSchmidtRankLe (stoneUnshuffleGridLinear F 0 b) 1 :=
        isRowUniformColOp_rankLe_one ⟨LinearMap.id, fun _ _ => rfl⟩
      exact h1.mono (by omega)
    | succ m' =>
      have hd : 0 < 2 ^ (m' + 1) := Nat.two_pow_pos (m' + 1)
      have hd_eq : 2 ^ (m' + 1) = 2 * 2 ^ m' := by ring
      let B : Fin 4 → ((Fin (2 ^ (m' + 1)) → Fin b → F) →ₗ[F] (Fin (2 ^ (m' + 1)) → Fin b → F)) :=
        fun i =>
          { toFun := fun v c ℓ =>
              if c.val / (2 ^ m') = i.val % 2 then
                v ⟨(2 * c.val + i.val / 2) % (2 ^ (m' + 1)), Nat.mod_lt _ hd⟩ ℓ
              else 0
            map_add' := fun u v => by
              funext c ℓ
              by_cases hc : c.val / (2 ^ m') = i.val % 2 <;> simp [hc]
            map_smul' := fun a v => by
              funext c ℓ
              by_cases hc : c.val / (2 ^ m') = i.val % 2 <;> simp [hc] }
      let A : Fin 4 → Matrix (Fin (2 ^ (m' + 1))) (Fin (2 ^ (m' + 1))) F := fun i =>
        Matrix.of fun r r' =>
          if r.val / (2 ^ m') = i.val / 2 ∧
             r'.val = (2 * r.val + i.val % 2) % (2 ^ (m' + 1)) then 1 else 0
      refine ⟨A, B, ?_⟩
      intro X r c ℓ
      set qr := r.val / (2 ^ m')
      set qc := c.val / (2 ^ m')
      have hqr : qr < 2 := Nat.div_lt_of_lt_mul
        (calc r.val < 2 ^ (m' + 1) := r.isLt
          _ = (2 ^ m') * 2 := by ring)
      have hqc : qc < 2 := Nat.div_lt_of_lt_mul
        (calc c.val < 2 ^ (m' + 1) := c.isLt
          _ = (2 ^ m') * 2 := by ring)
      let i₀ : Fin 4 := ⟨2 * qr + qc, by omega⟩
      let r'₀ : Fin (2 ^ (m' + 1)) := ⟨(2 * r.val + qc) % (2 ^ (m' + 1)), Nat.mod_lt _ hd⟩
      have hi_div : i₀.val / 2 = qr := (two_mul_add_div_mod hqc).2
      have hi_mod : i₀.val % 2 = qc := (two_mul_add_div_mod hqc).1
      rw [Finset.sum_eq_single i₀]
      · rw [Finset.sum_eq_single r'₀]
        · simp [A, B, r'₀, qr, qc, hi_div, hi_mod]
        · intro r' _ hr'
          have hr'_val : r'.val ≠ (2 * r.val + i₀.val % 2) % (2 ^ (m' + 1)) := by
            rw [hi_mod]
            exact fun h => hr' (Fin.ext h)
          simp [A, hr'_val]
        · intro h
          exact absurd (Finset.mem_univ r'₀) h
      · intro i _ hi
        refine Finset.sum_eq_zero fun r' _ => ?_
        by_cases ha : qr = i.val / 2
        · have hb_ne : qc ≠ i.val % 2 := by
            intro hb_eq
            apply hi
            apply Fin.ext
            show i.val = 2 * qr + qc
            have := i.isLt
            omega
          simp [B, qc, hb_ne]
        · simp [A, qr, ha]
      · intro h
        exact absurd (Finset.mem_univ i₀) h
  refine ⟨hInv.1, hInv.2, hShuffleLe4, hUnshuffleLe4, ?_⟩
  intro hm
  cases m with
  | zero => omega
  | succ m' =>
    have hK : 0 < 2 ^ m' := Nat.two_pow_pos m'
    have hd_pos : 0 < 2 ^ (m' + 1) := Nat.two_pow_pos (m' + 1)
    let ℓ₀ : Fin b := ⟨0, hb⟩
    refine ⟨⟨hShuffleLe4, ?_⟩, ⟨hUnshuffleLe4, ?_⟩⟩
    · intro R' hlt hR'
      let p : Fin 4 → Fin (2 ^ (m' + 1)) × Fin (2 ^ (m' + 1)) := fun k =>
        (⟨k.val / 2, by have := k.isLt; omega⟩,
         ⟨(k.val % 2) * (2 ^ m'), mul_two_pow_lt_succ (by omega)⟩)
      have hle : Fintype.card (Fin 4) ≤ R' := by
        refine card_le_of_hasOperatorSchmidtRankLe hR' p ?_
        intro coeff hsum k₀
        have hk₀_div_lt : k₀.val / 2 < 2 := by have := k₀.isLt; omega
        have hk₀_mod_lt : k₀.val % 2 < 2 := by omega
        let v : Fin (2 ^ (m' + 1)) → Fin b → F := fun col ℓ =>
          if col.val = (k₀.val / 2) * (2 ^ m') ∧ ℓ = ℓ₀ then 1 else 0
        let c'₀ : Fin (2 ^ (m' + 1)) := ⟨k₀.val % 2, by omega⟩
        have heval : (∑ k : Fin 4,
            coeff k • rowBlockOp (stoneShuffleGridLinear F (m' + 1) b) (p k).1 (p k).2)
              v c'₀ ℓ₀ = 0 := by
          rw [hsum]
          rfl
        rw [sum_smul_rowBlockOp_apply (stoneShuffleGridLinear F (m' + 1) b) p] at heval
        have hsrcR_val : ∀ k : Fin 4,
            ((c'₀.val % 2) * (2 ^ m') + (p k).1.val / 2) % (2 ^ (m' + 1)) =
              (k₀.val % 2) * (2 ^ m') := by
          intro k
          have hk_lt := k.isLt
          show (((k₀.val % 2) % 2) * (2 ^ m') + (k.val / 2) / 2) % (2 ^ (m' + 1)) =
            (k₀.val % 2) * (2 ^ m')
          have hb2 : (k₀.val % 2) % 2 = k₀.val % 2 := by omega
          have ha2 : (k.val / 2) / 2 = 0 := by omega
          rw [hb2, ha2, add_zero, Nat.mod_eq_of_lt (mul_two_pow_lt_succ hk₀_mod_lt)]
        have hsrcC_val : ∀ k : Fin 4,
            (((p k).1.val % 2) * (2 ^ m') + c'₀.val / 2) % (2 ^ (m' + 1)) =
              (k.val / 2) * (2 ^ m') := by
          intro k
          have hk_div_lt : k.val / 2 < 2 := by have := k.isLt; omega
          show (((k.val / 2) % 2) * (2 ^ m') + (k₀.val % 2) / 2) % (2 ^ (m' + 1)) =
            (k.val / 2) * (2 ^ m')
          have ha2 : (k.val / 2) % 2 = k.val / 2 := by omega
          have hb2 : (k₀.val % 2) / 2 = 0 := by omega
          rw [ha2, hb2, add_zero, Nat.mod_eq_of_lt (mul_two_pow_lt_succ hk_div_lt)]
        rw [Finset.sum_eq_single k₀] at heval
        · have hFinR : (⟨((c'₀.val % 2) * (2 ^ m') + (p k₀).1.val / 2) % (2 ^ (m' + 1)),
              Nat.mod_lt _ hd_pos⟩ : Fin (2 ^ (m' + 1))) = (p k₀).2 :=
            Fin.ext (hsrcR_val k₀)
          simp only [stoneShuffleGridLinear_succ_apply, hFinR, singleRowLinear_apply, ite_true]
            at heval
          simpa [v, hsrcC_val k₀] using heval
        · intro k _ hne
          simp only [stoneShuffleGridLinear_succ_apply, singleRowLinear_apply]
          by_cases hbeta : k₀.val % 2 = k.val % 2
          · have ha_ne : k.val / 2 ≠ k₀.val / 2 := by
              intro ha_eq
              apply hne
              apply Fin.ext
              have := k.isLt
              have := k₀.isLt
              omega
            have ha_mul_ne : (k.val / 2) * (2 ^ m') ≠ (k₀.val / 2) * (2 ^ m') :=
              fun hmul => ha_ne (Nat.eq_of_mul_eq_mul_right hK hmul)
            by_cases hR : (⟨((c'₀.val % 2) * (2 ^ m') + (p k).1.val / 2) % (2 ^ (m' + 1)),
                Nat.mod_lt _ hd_pos⟩ : Fin (2 ^ (m' + 1))) = (p k).2
            · simp [hR, v, hsrcC_val k, ha_mul_ne]
            · simp [hR]
          · have hR_ne : (⟨((c'₀.val % 2) * (2 ^ m') + (p k).1.val / 2) % (2 ^ (m' + 1)),
                Nat.mod_lt _ hd_pos⟩ : Fin (2 ^ (m' + 1))) ≠ (p k).2 := by
              intro hEq
              have hval : ((c'₀.val % 2) * (2 ^ m') + (p k).1.val / 2) % (2 ^ (m' + 1)) =
                  (k.val % 2) * (2 ^ m') := congrArg Fin.val hEq
              rw [hsrcR_val k] at hval
              exact hbeta (Nat.eq_of_mul_eq_mul_right hK hval)
            simp [hR_ne]
        · intro h
          exact absurd (Finset.mem_univ k₀) h
      rw [Fintype.card_fin] at hle
      omega
    · intro R' hlt hR'
      let p : Fin 4 → Fin (2 ^ (m' + 1)) × Fin (2 ^ (m' + 1)) := fun k =>
        (⟨(k.val / 2) * (2 ^ m'), mul_two_pow_lt_succ (by have := k.isLt; omega)⟩,
         ⟨k.val % 2, by omega⟩)
      have hle : Fintype.card (Fin 4) ≤ R' := by
        refine card_le_of_hasOperatorSchmidtRankLe hR' p ?_
        intro coeff hsum k₀
        have hk₀_mod_lt : k₀.val % 2 < 2 := by omega
        let v : Fin (2 ^ (m' + 1)) → Fin b → F := fun col ℓ =>
          if col.val = k₀.val / 2 ∧ ℓ = ℓ₀ then 1 else 0
        let c₀ : Fin (2 ^ (m' + 1)) := ⟨(k₀.val % 2) * (2 ^ m'), mul_two_pow_lt_succ hk₀_mod_lt⟩
        have heval : (∑ k : Fin 4,
            coeff k • rowBlockOp (stoneUnshuffleGridLinear F (m' + 1) b) (p k).1 (p k).2)
              v c₀ ℓ₀ = 0 := by
          rw [hsum]
          rfl
        rw [sum_smul_rowBlockOp_apply (stoneUnshuffleGridLinear F (m' + 1) b) p] at heval
        have hc₀_div : c₀.val / (2 ^ m') = k₀.val % 2 := Nat.mul_div_left (k₀.val % 2) hK
        have hp_srcR : ∀ k : Fin 4,
            (2 * (p k).1.val + c₀.val / (2 ^ m')) % (2 ^ (m' + 1)) = k₀.val % 2 := by
          intro k
          rw [hc₀_div]
          show (2 * ((k.val / 2) * (2 ^ m')) + k₀.val % 2) % (2 ^ (m' + 1)) = k₀.val % 2
          have e : 2 * ((k.val / 2) * (2 ^ m')) + k₀.val % 2 =
              k₀.val % 2 + (k.val / 2) * (2 ^ (m' + 1)) := by ring
          rw [e, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
        have hp_srcC : ∀ k : Fin 4,
            (2 * c₀.val + (p k).1.val / (2 ^ m')) % (2 ^ (m' + 1)) = k.val / 2 := by
          intro k
          have hk_lt := k.isLt
          have hpk_div : (p k).1.val / (2 ^ m') = k.val / 2 :=
            Nat.mul_div_left (k.val / 2) hK
          rw [hpk_div]
          show (2 * ((k₀.val % 2) * (2 ^ m')) + k.val / 2) % (2 ^ (m' + 1)) = k.val / 2
          have e : 2 * ((k₀.val % 2) * (2 ^ m')) + k.val / 2 =
              k.val / 2 + (k₀.val % 2) * (2 ^ (m' + 1)) := by ring
          rw [e, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
        rw [Finset.sum_eq_single k₀] at heval
        · have hFinR : (⟨(2 * (p k₀).1.val + c₀.val / (2 ^ m')) % (2 ^ (m' + 1)),
              Nat.mod_lt _ hd_pos⟩ : Fin (2 ^ (m' + 1))) = (p k₀).2 :=
            Fin.ext (hp_srcR k₀)
          simp only [stoneUnshuffleGridLinear_succ_apply, hFinR, singleRowLinear_apply, ite_true]
            at heval
          simpa [v, hp_srcC k₀] using heval
        · intro k _ hne
          simp only [stoneUnshuffleGridLinear_succ_apply, singleRowLinear_apply]
          by_cases hbeta : k₀.val % 2 = k.val % 2
          · have ha_ne : k.val / 2 ≠ k₀.val / 2 := by
              intro ha_eq
              apply hne
              apply Fin.ext
              have := k.isLt
              have := k₀.isLt
              omega
            by_cases hR : (⟨(2 * (p k).1.val + c₀.val / (2 ^ m')) % (2 ^ (m' + 1)),
                Nat.mod_lt _ hd_pos⟩ : Fin (2 ^ (m' + 1))) = (p k).2
            · simp [hR, v, hp_srcC k, ha_ne]
            · simp [hR]
          · have hR_ne : (⟨(2 * (p k).1.val + c₀.val / (2 ^ m')) % (2 ^ (m' + 1)),
                Nat.mod_lt _ hd_pos⟩ : Fin (2 ^ (m' + 1))) ≠ (p k).2 := by
              intro hEq
              have hval : (2 * (p k).1.val + c₀.val / (2 ^ m')) % (2 ^ (m' + 1)) = k.val % 2 :=
                congrArg Fin.val hEq
              rw [hp_srcR k] at hval
              exact hbeta hval
            simp [hR_ne]
        · intro h
          exact absurd (Finset.mem_univ k₀) h
      rw [Fintype.card_fin] at hle
      omega

end StoneShuffleProofs

/-! ### 6. Tight `log₂ d` Pass Lower Bound for Stone Shuffle Pipelines -/

private theorem composeGridOps_rank_le {F : Type*} [Field F] {m b : ℕ} (hb : 1 ≤ b)
    (Ks : List (GridState F (2 ^ m) b →ₗ[F] GridState F (2 ^ m) b))
    (shuffleIndices : Finset (Fin Ks.length))
    (hKs : ∀ i : Fin Ks.length,
      if i ∈ shuffleIndices then
        Ks.get i = stoneShuffleGridLinear F m b ∨ Ks.get i = stoneUnshuffleGridLinear F m b
      else
        IsRowUniformColOp (Ks.get i) ∨ IsColUniformRowOp (Ks.get i)) :
    HasOperatorSchmidtRankLe (composeGridOps Ks) (4 ^ shuffleIndices.card) := by
  induction Ks with
  | nil =>
    have hcard : shuffleIndices.card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro i
      exact Fin.elim0 i
    rw [hcard, pow_zero]
    exact isRowUniformColOp_rankLe_one ⟨LinearMap.id, fun _ _ => rfl⟩
  | cons K Ks' ih =>
    let tailIndices : Finset (Fin Ks'.length) :=
      Finset.univ.filter fun j : Fin Ks'.length => j.succ ∈ shuffleIndices
    have htail_prop : ∀ j : Fin Ks'.length,
        if j ∈ tailIndices then
          Ks'.get j = stoneShuffleGridLinear F m b ∨ Ks'.get j = stoneUnshuffleGridLinear F m b
        else
          IsRowUniformColOp (Ks'.get j) ∨ IsColUniformRowOp (Ks'.get j) := by
      intro j
      have hj := hKs j.succ
      have hmem : (j ∈ tailIndices) ↔ (j.succ ∈ shuffleIndices) := by
        simp [tailIndices]
      by_cases hjs : j.succ ∈ shuffleIndices
      · rw [ite_eq_left (hmem.mpr hjs)]
        rw [ite_eq_left hjs] at hj
        exact hj
      · rw [ite_eq_right (mt hmem.mp hjs)]
        rw [ite_eq_right hjs] at hj
        exact hj
    have hTailRank := ih tailIndices htail_prop
    let idx0 : Fin (K :: Ks').length := 0
    have h0 := hKs idx0
    obtain ⟨_, _, hS4, hU4, _⟩ := operatorSchmidtRankStoneShuffle F m b hb
    by_cases h0_mem : idx0 ∈ shuffleIndices
    · rw [ite_eq_left h0_mem] at h0
      change K = stoneShuffleGridLinear F m b ∨ K = stoneUnshuffleGridLinear F m b at h0
      have hK4 : HasOperatorSchmidtRankLe K 4 := by
        rcases h0 with rfl | rfl
        · exact hS4
        · exact hU4
      have hcard : shuffleIndices.card = tailIndices.card + 1 := by
        have hEq : shuffleIndices = insert idx0 (tailIndices.image Fin.succ) := by
          ext i
          refine Fin.cases ?_ ?_ i
          · simp [idx0, h0_mem]
          · intro j
            simp [idx0, tailIndices]
        have hnotMem : idx0 ∉ tailIndices.image Fin.succ := by
          simp [idx0]
        rw [hEq, Finset.card_insert_of_notMem hnotMem,
            Finset.card_image_of_injective _ (Fin.succ_injective _), add_comm]
      rw [hcard, pow_succ]
      exact hasOperatorSchmidtRankLe_comp hK4 hTailRank
    · rw [ite_eq_right h0_mem] at h0
      change IsRowUniformColOp K ∨ IsColUniformRowOp K at h0
      have hK1 : HasOperatorSchmidtRankLe K 1 := by
        rcases h0 with hRow | hCol
        · exact isRowUniformColOp_rankLe_one hRow
        · exact isColUniformRowOp_rankLe_one hCol
      have hcard : shuffleIndices.card = tailIndices.card := by
        have hEq : shuffleIndices = tailIndices.image Fin.succ := by
          ext i
          refine Fin.cases ?_ ?_ i
          · simp [idx0, h0_mem]
          · intro j
            simp [tailIndices]
        rw [hEq, Finset.card_image_of_injective _ (Fin.succ_injective _)]
      have hComp := hasOperatorSchmidtRankLe_comp hK1 hTailRank
      rw [mul_one, ← hcard] at hComp
      exact hComp

/-- Proof of `StoneShufflePipelinePassLowerBoundSpec`. -/
theorem stoneShufflePipelinePassLowerBound : StoneShufflePipelinePassLowerBoundSpec := by
  intro F _ m b Ks shuffleIndices hb hKs hEq
  have hRank := composeGridOps_rank_le hb Ks shuffleIndices hKs
  rw [hEq] at hRank
  have hExact := operatorSchmidtRankSwap F (2 ^ m) b (Nat.one_le_two_pow) hb
  have hPowLe : (2 ^ m) ^ 2 ≤ 4 ^ shuffleIndices.card := by
    by_contra hlt
    exact hExact.2 (4 ^ shuffleIndices.card) (Nat.lt_of_not_ge hlt) hRank
  have hmLe : m ≤ shuffleIndices.card := by
    have h4m : 4 ^ m ≤ 4 ^ shuffleIndices.card := by
      have e : (2 ^ m) ^ 2 = 4 ^ m := by
        calc (2 ^ m) ^ 2 = (2 ^ 2) ^ m := by rw [← pow_mul, mul_comm, pow_mul]
          _ = 4 ^ m := rfl
      rwa [← e]
    exact (Nat.pow_le_pow_iff_right (by omega : 1 < 4)).mp h4m
  exact ⟨hPowLe, hmLe⟩

/-! ### 7. Adversarial Control 1: Row Shear & Row-Diagonal Alternation -/

section RowShearControl

private theorem isRowDiagonalOp_sourceArity_one {F : Type*} [Semiring F] {d b : ℕ}
    {D : GridState F d b →ₗ[F] GridState F d b} (hD : IsRowDiagonalOp D) :
    HasOutputRowSourceArityLe D 1 := by
  obtain ⟨B, hB⟩ := hD
  refine ⟨fun r => {r}, fun _ => (Finset.card_singleton _).le, ?_⟩
  intro r X₁ X₂ hEq
  rw [hB, hB, hEq r (Finset.mem_singleton_self r)]

private theorem isRowDiagonalOp_comp_sourceArity {F : Type*} [Semiring F] {d b R : ℕ}
    {D K : GridState F d b →ₗ[F] GridState F d b}
    (hD : IsRowDiagonalOp D) (hK : HasOutputRowSourceArityLe K R) :
    HasOutputRowSourceArityLe (D.comp K) R := by
  obtain ⟨B, hB⟩ := hD
  obtain ⟨srcRows, hcard, hdep⟩ := hK
  refine ⟨srcRows, hcard, ?_⟩
  intro r X₁ X₂ hEq
  change D (K X₁) r = D (K X₂) r
  rw [hB, hB, hdep r X₁ X₂ hEq]

private theorem comp_sourceArity_mul {F : Type*} [Semiring F] {d b R₁ R₂ : ℕ}
    {U K : GridState F d b →ₗ[F] GridState F d b}
    (hU : HasOutputRowSourceArityLe U R₁) (hK : HasOutputRowSourceArityLe K R₂) :
    HasOutputRowSourceArityLe (U.comp K) (R₁ * R₂) := by
  classical
  obtain ⟨srcU, hcardU, hdepU⟩ := hU
  obtain ⟨srcK, hcardK, hdepK⟩ := hK
  refine ⟨fun r => (srcU r).biUnion srcK, ?_, ?_⟩
  · intro r
    calc ((srcU r).biUnion srcK).card
        ≤ ∑ r' ∈ srcU r, (srcK r').card := Finset.card_biUnion_le
      _ ≤ ∑ _r' ∈ srcU r, R₂ := Finset.sum_le_sum fun r' _ => hcardK r'
      _ = (srcU r).card * R₂ := by simp
      _ ≤ R₁ * R₂ := Nat.mul_le_mul_right R₂ (hcardU r)
  · intro r X₁ X₂ hEq
    change U (K X₁) r = U (K X₂) r
    refine hdepU r (K X₁) (K X₂) fun r' hr' => ?_
    refine hdepK r' X₁ X₂ fun r'' hr'' => ?_
    exact hEq r'' (Finset.mem_biUnion.mpr ⟨r', hr', hr''⟩)

private theorem stoneShuffle_sourceArity_two (F : Type*) [Semiring F] (m b : ℕ) :
    HasOutputRowSourceArityLe (stoneShuffleGridLinear F m b) 2 ∧
    HasOutputRowSourceArityLe (stoneUnshuffleGridLinear F m b) 2 := by
  classical
  cases m with
  | zero =>
    have hid : HasOutputRowSourceArityLe (LinearMap.id : GridState F 1 b →ₗ[F] GridState F 1 b) 2 :=
      ⟨fun r => {r}, fun _ => by simp, fun r _ _ h => h r (Finset.mem_singleton_self r)⟩
    exact ⟨hid, hid⟩
  | succ m' =>
    have hd : 0 < 2 ^ (m' + 1) := Nat.two_pow_pos (m' + 1)
    have hd_eq : 2 ^ (m' + 1) = 2 * 2 ^ m' := by ring
    constructor
    · refine ⟨fun r' =>
          {⟨(0 * (2 ^ m') + r'.val / 2) % (2 ^ (m' + 1)), Nat.mod_lt _ hd⟩,
           ⟨(1 * (2 ^ m') + r'.val / 2) % (2 ^ (m' + 1)), Nat.mod_lt _ hd⟩},
        fun _ => Finset.card_le_two, ?_⟩
      intro r' X₁ X₂ hEq
      funext c' ℓ
      simp only [stoneShuffleGridLinear_succ_apply]
      have hmem : (⟨((c'.val % 2) * (2 ^ m') + r'.val / 2) % (2 ^ (m' + 1)),
            Nat.mod_lt _ hd⟩ : Fin (2 ^ (m' + 1))) ∈
          ({⟨(0 * (2 ^ m') + r'.val / 2) % (2 ^ (m' + 1)), Nat.mod_lt _ hd⟩,
            ⟨(1 * (2 ^ m') + r'.val / 2) % (2 ^ (m' + 1)), Nat.mod_lt _ hd⟩} :
              Finset (Fin (2 ^ (m' + 1)))) := by
        rcases Nat.mod_two_eq_zero_or_one c'.val with h0 | h1
        · simp [h0]
        · simp [h1]
      exact congrFun (congrFun (hEq _ hmem) _) ℓ
    · refine ⟨fun r =>
          {⟨(2 * r.val + 0) % (2 ^ (m' + 1)), Nat.mod_lt _ hd⟩,
           ⟨(2 * r.val + 1) % (2 ^ (m' + 1)), Nat.mod_lt _ hd⟩},
        fun _ => Finset.card_le_two, ?_⟩
      intro r X₁ X₂ hEq
      funext c ℓ
      simp only [stoneUnshuffleGridLinear_succ_apply]
      have hc_div : c.val / (2 ^ m') < 2 := Nat.div_lt_of_lt_mul
        (calc c.val < 2 ^ (m' + 1) := c.isLt
          _ = (2 ^ m') * 2 := by ring)
      have hmem : (⟨(2 * r.val + c.val / (2 ^ m')) % (2 ^ (m' + 1)),
            Nat.mod_lt _ hd⟩ : Fin (2 ^ (m' + 1))) ∈
          ({⟨(2 * r.val + 0) % (2 ^ (m' + 1)), Nat.mod_lt _ hd⟩,
            ⟨(2 * r.val + 1) % (2 ^ (m' + 1)), Nat.mod_lt _ hd⟩} :
              Finset (Fin (2 ^ (m' + 1)))) := by
        have h01 : ∀ q : ℕ, q < 2 → q = 0 ∨ q = 1 := by omega
        rcases h01 _ hc_div with h0 | h1
        · simp [h0]
        · simp [h1]
      exact congrFun (congrFun (hEq _ hmem) _) ℓ

/-- Proof of `Control_RowShearAndRowDiagonalAlternationSpec`. -/
theorem control_RowShearAndRowDiagonalAlternation :
    Control_RowShearAndRowDiagonalAlternationSpec := by
  constructor
  · intro F _ d b _ hb
    let Bdiag : Fin d → ((Fin d → Fin b → F) →ₗ[F] (Fin d → Fin b → F)) := fun r =>
      { toFun := fun v c ℓ => v ⟨(c.val + r.val) % d, Nat.mod_lt _ (NeZero.pos d)⟩ ℓ
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hDiag : IsRowDiagonalOp (rowShearLinear F d b) := ⟨Bdiag, fun _ _ => rfl⟩
    have hUpper : HasOperatorSchmidtRankLe (rowShearLinear F d b) d := by
      refine ⟨fun i => Matrix.of fun r r' => if r = i ∧ r' = i then 1 else 0, Bdiag, ?_⟩
      intro X r c ℓ
      rw [Finset.sum_eq_single r]
      · rw [Finset.sum_eq_single r]
        · simp [Bdiag]
        · intro r' _ hr'
          simp [hr']
        · intro h
          exact absurd (Finset.mem_univ r) h
      · intro i _ hi
        refine Finset.sum_eq_zero fun r' _ => ?_
        simp [hi.symm]
      · intro h
        exact absurd (Finset.mem_univ r) h
    refine ⟨hDiag, hUpper, ?_⟩
    intro R' hlt hR'
    let ℓ₀ : Fin b := ⟨0, hb⟩
    let c₀ : Fin d := ⟨0, NeZero.pos d⟩
    have hle : Fintype.card (Fin d) ≤ R' := by
      refine card_le_of_hasOperatorSchmidtRankLe hR' (fun r => (r, r)) ?_
      intro coeff hsum r₀
      let v : Fin d → Fin b → F := fun col ℓ => if col = r₀ ∧ ℓ = ℓ₀ then 1 else 0
      have heval : (∑ r : Fin d,
          coeff r • rowBlockOp (rowShearLinear F d b) r r) v c₀ ℓ₀ = 0 := by
        rw [hsum]
        rfl
      rw [sum_smul_rowBlockOp_apply (rowShearLinear F d b) (fun r => (r, r))] at heval
      have hshift : ∀ r : Fin d,
          (⟨(c₀.val + r.val) % d, Nat.mod_lt _ (NeZero.pos d)⟩ : Fin d) = r := by
        intro r
        apply Fin.ext
        show (0 + r.val) % d = r.val
        rw [zero_add, Nat.mod_eq_of_lt r.isLt]
      rw [Finset.sum_eq_single r₀] at heval
      · simp only [rowShearLinear_apply, hshift r₀, singleRowLinear_apply, ite_true] at heval
        simpa [v] using heval
      · intro r _ hr
        simp [rowShearLinear_apply, hshift r, v, hr]
      · intro h
        exact absurd (Finset.mem_univ r₀) h
    rw [Fintype.card_fin] at hle
    omega
  · intro F _ m b s D U hb hD hU
    have hArity : HasOutputRowSourceArityLe (alternatingRowDiagProduct D U) (2 ^ s) := by
      induction s with
      | zero =>
        simpa [alternatingRowDiagProduct] using isRowDiagonalOp_sourceArity_one (hD 0)
      | succ s' ih =>
        have hPref := ih
          (fun i => D i.castSucc) (fun j => U j.castSucc)
          (fun i => hD i.castSucc) (fun j => hU j.castSucc)
        have hU_last : HasOutputRowSourceArityLe (U (Fin.last s')) 2 := by
          obtain ⟨hS2, hU2⟩ := stoneShuffle_sourceArity_two F m b
          rcases hU (Fin.last s') with hEq | hEq <;> rwa [hEq]
        have hStep := comp_sourceArity_mul hU_last hPref
        rw [pow_succ']
        exact isRowDiagonalOp_comp_sourceArity (hD (Fin.last (s' + 1))) hStep
    refine ⟨hArity, ?_⟩
    intro hEq
    rw [hEq] at hArity
    obtain ⟨srcRows, hcard, hdep⟩ := hArity
    let r₀ : Fin (2 ^ m) := ⟨0, Nat.two_pow_pos m⟩
    let ℓ₀ : Fin b := ⟨0, hb⟩
    have huniv : srcRows r₀ = Finset.univ := by
      ext c
      simp only [Finset.mem_univ, iff_true]
      by_contra hc
      let X₂ : GridState F (2 ^ m) b := singleRowLinear F (2 ^ m) b c (fun _ _ => 1)
      have hAgree : ∀ r' ∈ srcRows r₀, (0 : GridState F (2 ^ m) b) r' = X₂ r' := by
        intro r' hr'
        have hne : r' ≠ c := fun h => hc (h ▸ hr')
        simp [X₂, hne]
      have hRowEq := hdep r₀ 0 X₂ hAgree
      have hCell := congrFun (congrFun hRowEq c) ℓ₀
      simp [gridSwapLinear_apply, X₂] at hCell
    have h2m_le : 2 ^ m ≤ 2 ^ s := by
      have hcard₀ := hcard r₀
      rwa [huniv, Finset.card_univ, Fintype.card_fin] at hcard₀
    exact ⟨h2m_le, (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp h2m_le⟩

end RowShearControl

/-! ### 8. Adversarial Control 2: Skew One-Time-Pad Information Trap -/

section SkewPadControl

private def vecXor {b : ℕ} (x y : Fin b → Bool) : Fin b → Bool :=
  fun ℓ => xor (x ℓ) (y ℓ)

private lemma vecXor_comm {b : ℕ} (x y : Fin b → Bool) : vecXor x y = vecXor y x := by
  funext ℓ
  unfold vecXor
  cases x ℓ <;> cases y ℓ <;> rfl

private lemma vecXor_cancel_right {b : ℕ} (x y : Fin b → Bool) :
    vecXor (vecXor x y) y = x := by
  funext ℓ
  unfold vecXor
  cases x ℓ <;> cases y ℓ <;> rfl

/-- Coordinate-swap equivalence establishing independence of cell `(i₀, j₀)` from column `c'`
whenever `j₀ ≠ c'`. -/
private def cellColIndepEquiv {d b : ℕ} (i₀ j₀ c' : ZMod d) (hne : j₀ ≠ c')
    (v : Fin b → Bool) (u : ZMod d → Fin b → Bool) :
    State d (Fin b → Bool) ×
      {Y : State d (Fin b → Bool) // Y i₀ j₀ = v ∧ (fun i => Y i c') = u} ≃
    {P : State d (Fin b → Bool) // P i₀ j₀ = v} ×
      {Q : State d (Fin b → Bool) // (fun i => Q i c') = u} where
  toFun ZY :=
    (⟨fun i j => if i = i₀ ∧ j = j₀ then ZY.2.1 i₀ j₀ else ZY.1 i j, by
       simp only [and_self, ite_true]
       exact ZY.2.2.1⟩,
     ⟨fun i j => if i = i₀ ∧ j = j₀ then ZY.1 i₀ j₀ else ZY.2.1 i j, by
       funext i
       have hj : c' ≠ j₀ := hne.symm
       simp only [hj, and_false, ite_false]
       exact congrFun ZY.2.2.2 i⟩)
  invFun PQ :=
    (fun i j => if i = i₀ ∧ j = j₀ then PQ.2.1 i₀ j₀ else PQ.1.1 i j,
     ⟨fun i j => if i = i₀ ∧ j = j₀ then PQ.1.1 i₀ j₀ else PQ.2.1 i j,
      ⟨by
        simp only [and_self, ite_true]
        exact PQ.1.2,
       by
        funext i
        have hj : c' ≠ j₀ := hne.symm
        simp only [hj, and_false, ite_false]
        exact congrFun PQ.2.2 i⟩⟩)
  left_inv := by
    rintro ⟨Z, ⟨Y, hY1, hY2⟩⟩
    apply Prod.ext
    · funext i j
      by_cases h : i = i₀ ∧ j = j₀
      · rcases h with ⟨rfl, rfl⟩
        simp
      · simp [h]
    · apply Subtype.ext
      funext i j
      by_cases h : i = i₀ ∧ j = j₀
      · rcases h with ⟨rfl, rfl⟩
        simp
      · simp [h]
  right_inv := by
    rintro ⟨⟨P, hP⟩, ⟨Q, hQ⟩⟩
    apply Prod.ext
    · apply Subtype.ext
      funext i j
      by_cases h : i = i₀ ∧ j = j₀
      · rcases h with ⟨rfl, rfl⟩
        simp
      · simp [h]
    · apply Subtype.ext
      funext i j
      by_cases h : i = i₀ ∧ j = j₀
      · rcases h with ⟨rfl, rfl⟩
        simp
      · simp [h]

/-- Self-inverse shear bijection replacing `X i₀ j₀` with `vecXor (X i₀ j₀) (X i₁ j₁)` when
`(i₀, j₀) ≠ (i₁, j₁)`. -/
private def cellXorShearEquiv {d b : ℕ} (i₀ j₀ i₁ j₁ : ZMod d)
    (hp : ¬ (i₁ = i₀ ∧ j₁ = j₀)) :
    State d (Fin b → Bool) ≃ State d (Fin b → Bool) where
  toFun X i j := if i = i₀ ∧ j = j₀ then vecXor (X i₀ j₀) (X i₁ j₁) else X i j
  invFun Y i j := if i = i₀ ∧ j = j₀ then vecXor (Y i₀ j₀) (Y i₁ j₁) else Y i j
  left_inv X := by
    funext i j
    by_cases h : i = i₀ ∧ j = j₀
    · rcases h with ⟨rfl, rfl⟩
      simp [hp, vecXor_cancel_right]
    · simp [h]
  right_inv Y := by
    funext i j
    by_cases h : i = i₀ ∧ j = j₀
    · rcases h with ⟨rfl, rfl⟩
      simp [hp, vecXor_cancel_right]
    · simp [h]

/-- Proof of `Control_SkewOneTimePadInformationTrapSpec`. -/
theorem control_SkewOneTimePadInformationTrap : Control_SkewOneTimePadInformationTrapSpec := by
  intro d b _ _hb
  constructor
  · intro X r c ℓ
    show xor (xor (X c r ℓ) (X r c ℓ)) (X r c ℓ) = X c r ℓ
    cases X c r ℓ <;> cases X r c ℓ <;> rfl
  · intro r c c' v u
    by_cases hrc : r = c
    · subst hrc
      have hdiag : ∀ X : State d (Fin b → Bool), skewXorPad X r r = fun _ => false := by
        intro X
        funext ℓ
        show xor (X r r ℓ) (X r r ℓ) = false
        cases X r r ℓ <;> rfl
      by_cases hv : (fun _ : Fin b => false) = v
      · have hfilt1 : (Finset.univ.filter fun X : State d (Fin b → Bool) =>
            skewXorPad X r r = v ∧ (fun i => X i c') = u) =
            (Finset.univ.filter fun X : State d (Fin b → Bool) => (fun i => X i c') = u) := by
          ext X
          simp [hdiag X, hv]
        have hfilt2 : (Finset.univ.filter fun X : State d (Fin b → Bool) =>
            skewXorPad X r r = v) = Finset.univ := by
          ext X
          simp [hdiag X, hv]
        rw [hfilt1, hfilt2, Finset.card_univ]
      · have hfilt1 : (Finset.univ.filter fun X : State d (Fin b → Bool) =>
            skewXorPad X r r = v ∧ (fun i => X i c') = u) = ∅ := by
          ext X
          simp [hdiag X, hv]
        have hfilt2 : (Finset.univ.filter fun X : State d (Fin b → Bool) =>
            skewXorPad X r r = v) = ∅ := by
          ext X
          simp [hdiag X, hv]
        rw [hfilt1, hfilt2, Finset.card_empty, mul_zero, zero_mul]
    · have hChoice : ∃ i₀ j₀ i₁ j₁ : ZMod d,
          j₀ ≠ c' ∧ ¬ (i₁ = i₀ ∧ j₁ = j₀) ∧
          ∀ X : State d (Fin b → Bool), skewXorPad X r c = vecXor (X i₀ j₀) (X i₁ j₁) := by
        by_cases hcc' : c = c'
        · refine ⟨c, r, r, c, ?_, ?_, ?_⟩
          · rw [← hcc']
            exact hrc
          · rintro ⟨h1, _⟩
            exact hrc h1
          · intro X
            rfl
        · refine ⟨r, c, c, r, hcc', ?_, ?_⟩
          · rintro ⟨h1, _⟩
            exact hrc h1.symm
          · intro X
            exact vecXor_comm (X c r) (X r c)
      obtain ⟨i₀, j₀, i₁, j₁, hj₀, hp, hSkewEq⟩ := hChoice
      let Φ := cellXorShearEquiv (b := b) i₀ j₀ i₁ j₁ hp
      have hΦ_cell : ∀ X : State d (Fin b → Bool), (Φ X) i₀ j₀ = skewXorPad X r c := by
        intro X
        simp [Φ, cellXorShearEquiv, hSkewEq X]
      have hΦ_col : ∀ X : State d (Fin b → Bool),
          (fun i => (Φ X) i c') = (fun i => X i c') := by
        intro X
        funext i
        have hne : c' ≠ j₀ := hj₀.symm
        simp [Φ, cellXorShearEquiv, hne]
      have hBoth : (Finset.univ.filter fun X : State d (Fin b → Bool) =>
            skewXorPad X r c = v ∧ (fun i => X i c') = u).card =
          Fintype.card {Y : State d (Fin b → Bool) // Y i₀ j₀ = v ∧ (fun i => Y i c') = u} := by
        rw [← Fintype.card_subtype]
        refine Fintype.card_congr
          { toFun := fun X => ⟨Φ X.1, by rw [hΦ_cell, hΦ_col]; exact X.2⟩
            invFun := fun Y => ⟨Φ.symm Y.1, by
              have hY : Φ (Φ.symm Y.1) = Y.1 := Φ.apply_symm_apply Y.1
              have hc1 := hΦ_cell (Φ.symm Y.1)
              have hc2 := hΦ_col (Φ.symm Y.1)
              rw [hY] at hc1 hc2
              exact ⟨hc1.symm.trans Y.2.1, hc2.symm.trans Y.2.2⟩⟩
            left_inv := fun X => Subtype.ext (Φ.symm_apply_apply X.1)
            right_inv := fun Y => Subtype.ext (Φ.apply_symm_apply Y.1) }
      have hLeft : (Finset.univ.filter fun X : State d (Fin b → Bool) =>
            skewXorPad X r c = v).card =
          Fintype.card {P : State d (Fin b → Bool) // P i₀ j₀ = v} := by
        rw [← Fintype.card_subtype]
        refine Fintype.card_congr
          { toFun := fun X => ⟨Φ X.1, by rw [hΦ_cell]; exact X.2⟩
            invFun := fun P => ⟨Φ.symm P.1, by
              have hP : Φ (Φ.symm P.1) = P.1 := Φ.apply_symm_apply P.1
              have hc1 := hΦ_cell (Φ.symm P.1)
              rw [hP] at hc1
              exact hc1.symm.trans P.2⟩
            left_inv := fun X => Subtype.ext (Φ.symm_apply_apply X.1)
            right_inv := fun P => Subtype.ext (Φ.apply_symm_apply P.1) }
      have hRight : (Finset.univ.filter fun X : State d (Fin b → Bool) =>
            (fun i => X i c') = u).card =
          Fintype.card {Q : State d (Fin b → Bool) // (fun i => Q i c') = u} :=
        (Fintype.card_subtype _).symm
      rw [hBoth, hLeft, hRight, ← Fintype.card_prod, ← Fintype.card_prod]
      exact Fintype.card_congr (cellColIndepEquiv i₀ j₀ c' hj₀ v u)

end SkewPadControl

end BoundedArityDecoders
