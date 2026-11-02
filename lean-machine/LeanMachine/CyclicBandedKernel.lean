import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.LinearAlgebra.Dimension.OrzechProperty

/-!
# `K[C_N]` with `uᴺ = 0`: the basis `1, u, …, u^{N−1}` and banded kernels

`K` is a field (of characteristic 3 where stated), `R = K[C_N]`, `T` the generator of `C_N`, `u = T − 1`. For `N = 3^j`,
`uᴺ = Tᴺ − 1 = 0`. If `uᴺ = 0`, the powers `u^k`, `k < N`, span `R` (because `T = 1 + u`), so they
form a `K`-basis (`dim R = N`). In these coordinates right multiplication by
`B₀ + u B₁ + u² B₂` on `Rⁿ` is the banded map `y_k = x_k B₀ + x_{k−1} B₁ + x_{k−2} B₂`, and
injectivity of the connecting map gives `dim ker ≤ dim ker (x ↦ x B₀)` (`finrank_ker_le`).
-/

namespace LeanMachine.CyclicAlg

open Matrix

variable (K : Type*) [Field K] (N : ℕ)

/-- The cyclic group of order `N`, written multiplicatively. -/
abbrev Cyc := Multiplicative (ZMod N)

/-- `K[C_N]`. -/
abbrev RN := MonoidAlgebra K (Cyc N)

/-- The generator `T` and `u = T − 1`. -/
noncomputable def T : RN K N := MonoidAlgebra.single (Multiplicative.ofAdd 1) 1
noncomputable def u : RN K N := T K N - 1

theorem T_eq : T K N = u K N + 1 := by simp [u]

theorem T_pow_N : T K N ^ N = 1 := by
  rw [T, MonoidAlgebra.single_pow, one_pow, ← ofAdd_nsmul, nsmul_one, ZMod.natCast_self,
    ofAdd_zero, MonoidAlgebra.one_def]

theorem charP_RN [CharP K 3] : CharP (RN K N) 3 := charP_of_injective_algebraMap' K 3

/-- `u^{3^j} = 0` in `K[C_{3^j}]`. -/
theorem u_pow_eq_zero [CharP K 3] (j : ℕ) : u K (3 ^ j) ^ (3 ^ j) = 0 := by
  have := charP_RN K (3 ^ j)
  rw [u, sub_pow_char_pow, T_pow_N, one_pow, sub_self]

variable [NeZero N]

instance moduleFinite : Module.Finite K (RN K N) :=
  Module.Finite.of_basis (MonoidAlgebra.basis (Cyc N) K)

theorem finrank_RN : Module.finrank K (RN K N) = N := by
  rw [Module.finrank_eq_nat_card_basis (MonoidAlgebra.basis (Cyc N) K)]
  simp

/-- The span of `u^k`, `k < N`. -/
noncomputable abbrev Vspan : Submodule K (RN K N) :=
  Submodule.span K (Set.range fun k : Fin N => u K N ^ (k : ℕ))

variable {K N}

omit [NeZero N] in
theorem u_pow_mem (hu : u K N ^ N = 0) (i : ℕ) : u K N ^ i ∈ Vspan K N := by
  by_cases h : i < N
  · exact Submodule.subset_span ⟨⟨i, h⟩, rfl⟩
  · rw [show i = N + (i - N) by omega, pow_add, hu, zero_mul]
    exact Submodule.zero_mem _

omit [NeZero N] in
theorem T_pow_mem (hu : u K N ^ N = 0) (m : ℕ) : T K N ^ m ∈ Vspan K N := by
  rw [T_eq, add_pow]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [one_pow, mul_one, ← nsmul_eq_mul']
  exact nsmul_mem (u_pow_mem hu i) _

theorem single_eq (g : Cyc N) (c : K) :
    MonoidAlgebra.single g c = c • T K N ^ (Multiplicative.toAdd g).val := by
  rw [T, MonoidAlgebra.single_pow, one_pow, MonoidAlgebra.smul_single', mul_one, ← ofAdd_nsmul,
    nsmul_one, ZMod.natCast_zmod_val, ofAdd_toAdd]

theorem mem_Vspan (hu : u K N ^ N = 0) (r : RN K N) : r ∈ Vspan K N := by
  induction r using MonoidAlgebra.induction_on with
  | of m =>
    rw [MonoidAlgebra.of_apply, single_eq, one_smul]
    exact T_pow_mem hu _
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | smul r x hx => exact Submodule.smul_mem _ r hx

theorem span_eq_top (hu : u K N ^ N = 0) : Vspan K N = ⊤ :=
  eq_top_iff.mpr fun r _ => mem_Vspan hu r

theorem linIndep (hu : u K N ^ N = 0) :
    LinearIndependent (K) (fun k : Fin N => u K N ^ (k : ℕ)) :=
  linearIndependent_of_top_le_span_of_card_eq_finrank (span_eq_top hu).ge
    (by rw [Fintype.card_fin, finrank_RN])

variable (K N) in
/-- `E c = Σ_{k < N} c_k u^k`. -/
noncomputable def E : (ℕ → K) →ₗ[K] RN K N where
  toFun c := ∑ k ∈ Finset.range N, c k • u K N ^ k
  map_add' c d := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a c := by simp [Finset.smul_sum, smul_smul]

omit [NeZero N] in
theorem E_apply (c : ℕ → K) : E K N c = ∑ k ∈ Finset.range N, c k • u K N ^ k := rfl

/-- Every element of `R` has coordinates. -/
theorem exists_E (hu : u K N ^ N = 0) (r : RN K N) : ∃ c : ℕ → K, E K N c = r := by
  have hr : r ∈ Vspan K N := by rw [span_eq_top hu]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hr
  refine ⟨fun k => if h : k < N then c ⟨k, h⟩ else 0, ?_⟩
  rw [E_apply, Finset.sum_range, ← hc]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [dite_eq_left k.2]

/-- The coordinates are unique. -/
theorem E_eq_zero (hu : u K N ^ N = 0) (c : ℕ → K) (h : E K N c = 0) (k : ℕ) (hk : k < N) :
    c k = 0 := by
  have h' : ∑ i : Fin N, c i • u K N ^ (i : ℕ) = 0 := by
    rw [← Finset.sum_range (fun i => c i • u K N ^ i)]
    exact h
  exact Fintype.linearIndependent_iff.mp (linIndep hu) (fun i : Fin N => c i) h' ⟨k, hk⟩

/-- Shift of a sequence: `(sh x)₀ = 0`, `(sh x)_{k+1} = x_k`. -/
def sh {M : Type*} [Zero M] (x : ℕ → M) : ℕ → M
  | 0 => 0
  | k + 1 => x k

theorem sh_apply {M ι : Type*} [Zero M] (x : ℕ → ι → M) (i : ι) :
    sh (fun k => x k i) = fun k => sh x k i := by
  funext k
  cases k <;> rfl

theorem E_mul_u (hu : u K N ^ N = 0) (c : ℕ → K) : E K N c * u K N = E K N (sh c) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by have := NeZero.pos N; omega⟩
  have lhs : E K (M + 1) c * u K (M + 1) = ∑ k ∈ Finset.range M, c k • u K (M + 1) ^ (k + 1) := by
    rw [E_apply, Finset.sum_mul, Finset.sum_range_succ]
    simp only [smul_mul_assoc, ← pow_succ, hu, smul_zero, add_zero]
  have rhs : E K (M + 1) (sh c) = ∑ k ∈ Finset.range M, c k • u K (M + 1) ^ (k + 1) := by
    rw [E_apply, Finset.sum_range_succ']
    simp only [sh, zero_smul, add_zero]
  rw [lhs, rhs]

variable {n : ℕ}

/-- Coordinates of a vector: `w_i = E (x · i)`. -/
theorem exists_coords (hu : u K N ^ N = 0) (w : Fin n → RN K N) :
    ∃ x : ℕ → Fin n → K, ∀ i, w i = E K N (fun k => x k i) := by
  choose c hc using fun i => exists_E hu (w i)
  exact ⟨fun k i => c i k, fun i => (hc i).symm⟩

/-- In coordinates, right multiplication by `B₀ + u B₁ + u² B₂` is banded. -/
theorem vecMul_coords (hu : u K N ^ N = 0) (B₀ B₁ B₂ : Matrix (Fin n) (Fin n) (K))
    (A : Matrix (Fin n) (Fin n) (RN K N))
    (hA : ∀ i k, A i k = B₀ i k • (1 : RN K N) + B₁ i k • u K N + B₂ i k • u K N ^ 2)
    (x : ℕ → Fin n → K) (k : Fin n) :
    ((fun i => E K N (fun m => x m i)) ᵥ* A) k =
      E K N (fun m => (x m ᵥ* B₀ + sh x m ᵥ* B₁ + sh (sh x) m ᵥ* B₂) k) := by
  have h1 : ∀ i, E K N (fun m => x m i) * A i k =
      E K N (fun m => x m i * B₀ i k + sh x m i * B₁ i k + sh (sh x) m i * B₂ i k) := by
    intro i
    rw [hA, mul_add, mul_add, mul_smul_comm, mul_smul_comm, mul_smul_comm, mul_one, pow_two,
      ← mul_assoc, E_mul_u hu, E_mul_u hu, sh_apply, sh_apply, ← map_smul, ← map_smul, ← map_smul,
      ← map_add, ← map_add]
    congr 1
    funext m
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  simp only [Matrix.vecMul, dotProduct, h1, ← map_sum]
  congr 1
  funext m
  simp only [Finset.sum_apply, Pi.add_apply, Finset.sum_add_distrib, Matrix.vecMul, dotProduct]

/-- The kernel equations force `x_k = 0` for `k < N − 1` and `x_{N−1} B₀ = 0`. -/
theorem ker_coords (B₀ B₁ B₂ : Matrix (Fin n) (Fin n) (K))
    (hδ : ∀ x : Fin n → K, x ᵥ* B₀ = 0 → ∀ z, x ᵥ* B₁ = z ᵥ* B₀ → x = 0)
    (x : ℕ → Fin n → K)
    (hy : ∀ m < N, x m ᵥ* B₀ + sh x m ᵥ* B₁ + sh (sh x) m ᵥ* B₂ = 0) :
    (∀ m, m + 1 < N → x m = 0) ∧ x (N - 1) ᵥ* B₀ = 0 := by
  have hlow : ∀ m, m + 1 < N → x m = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hm
      have hsh : sh x m = 0 := by
        cases m with
        | zero => rfl
        | succ m' => exact ih m' (by omega) (by omega)
      have hsh2 : sh (sh x) m = 0 := by
        cases m with
        | zero => rfl
        | succ m' =>
          cases m' with
          | zero => rfl
          | succ m'' => exact ih m'' (by omega) (by omega)
      have h0 : x m ᵥ* B₀ = 0 := by
        have := hy m (by omega)
        rwa [hsh, hsh2, zero_vecMul, zero_vecMul, add_zero, add_zero] at this
      have h1 : x m ᵥ* B₁ = (-x (m + 1)) ᵥ* B₀ := by
        have := hy (m + 1) hm
        have e1 : sh x (m + 1) = x m := rfl
        have e2 : sh (sh x) (m + 1) = sh x m := rfl
        rw [e1, e2, hsh, zero_vecMul, add_zero] at this
        rw [Matrix.neg_vecMul]
        exact eq_neg_of_add_eq_zero_right this
      exact hδ _ h0 _ h1
  refine ⟨hlow, ?_⟩
  have hsh : ∀ m, m < N → sh x m = 0 := by
    intro m hm
    cases m with
    | zero => rfl
    | succ m' => exact hlow m' hm
  have hsh2 : ∀ m, m < N → sh (sh x) m = 0 := by
    intro m hm
    cases m with
    | zero => rfl
    | succ m' => exact hsh m' (by omega)
  have hN := NeZero.pos N
  have := hy (N - 1) (by omega)
  rwa [hsh _ (by omega), hsh2 _ (by omega), zero_vecMul, zero_vecMul, add_zero, add_zero] at this

/-- **The banded kernel bound**: if `A = B₀ + u B₁ + u² B₂` over `K[C_N]` with `uᴺ = 0` and the
connecting map of `(B₀, B₁)` is injective, then `dim ker (w ↦ w A) ≤ dim ker (x ↦ x B₀)`. -/
theorem finrank_ker_le (hu : u K N ^ N = 0) (B₀ B₁ B₂ : Matrix (Fin n) (Fin n) (K))
    (A : Matrix (Fin n) (Fin n) (RN K N))
    (hA : ∀ i k, A i k = B₀ i k • (1 : RN K N) + B₁ i k • u K N + B₂ i k • u K N ^ 2)
    (hδ : ∀ x : Fin n → K, x ᵥ* B₀ = 0 → ∀ z, x ᵥ* B₁ = z ᵥ* B₀ → x = 0)
    (φ : (Fin n → RN K N) →ₗ[K] (Fin n → RN K N)) (hφ : ∀ w, φ w = w ᵥ* A) :
    Module.finrank (K) (LinearMap.ker φ) ≤
      Module.finrank (K) (LinearMap.ker (Matrix.vecMulLinear B₀)) := by
  let g : (Fin n → K) →ₗ[K] (Fin n → RN K N) :=
    { toFun := fun b i => b i • u K N ^ (N - 1)
      map_add' := fun b c => by funext i; simp [add_smul]
      map_smul' := fun a b => by funext i; simp [smul_smul] }
  calc Module.finrank (K) (LinearMap.ker φ)
      ≤ Module.finrank (K) ((LinearMap.ker (Matrix.vecMulLinear B₀)).map g) := by
        apply Submodule.finrank_mono
        intro w hw
        obtain ⟨x, hx⟩ := exists_coords hu w
        have hwx : w = fun i => E K N (fun m => x m i) := funext hx
        have hw' : w ᵥ* A = 0 := by rw [← hφ]; exact hw
        have hy : ∀ m < N, x m ᵥ* B₀ + sh x m ᵥ* B₁ + sh (sh x) m ᵥ* B₂ = 0 := by
          intro m hm
          funext k
          have hk := congrFun hw' k
          rw [hwx, vecMul_coords hu B₀ B₁ B₂ A hA x k] at hk
          exact E_eq_zero hu _ hk m hm
        obtain ⟨hlow, htop⟩ := ker_coords B₀ B₁ B₂ hδ x hy
        refine ⟨x (N - 1), htop, ?_⟩
        funext i
        rw [hx i, E_apply]
        have hN := NeZero.pos N
        rw [Finset.sum_eq_single (N - 1)]
        · rfl
        · intro b hb hbN
          rw [Finset.mem_range] at hb
          rw [hlow b (by omega)]
          simp
        · intro h
          exact absurd (Finset.mem_range.mpr (by omega)) h
    _ ≤ Module.finrank (K) (LinearMap.ker (Matrix.vecMulLinear B₀)) :=
        Submodule.finrank_map_le _ _

end LeanMachine.CyclicAlg
