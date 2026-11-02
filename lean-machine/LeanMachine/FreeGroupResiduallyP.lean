import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Matrix.Basic
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.GroupTheory.PGroup

/-!
# Free groups are residually `p`-finite

* `LeanMachine.freeGroup_residually_pGroup`: every nontrivial element of `FreeGroup (Fin r)` survives in
  some finite `p`-group quotient (Magnus, Iwasawa).
* `LeanMachine.ResidualP.exists_goodP_lt`: below every normal subgroup of finite index with `p`-group quotient
  there is a strictly smaller one. Iterating this gives chains of normal subgroups with `p`-group quotients
  and trivial intersection.

## Proof of residual `p`-finiteness (a matrix form of the Magnus embedding)

Write `g ≠ 1` in syllable form `g = x_{a₁}^{e₁} ⋯ x_{a_s}^{e_s}` with `a_t ≠ a_{t+1}` and `e_t ≠ 0`
(`exists_sylList`). Over `R = ZMod (p^k)` let `N_a` be the `(s+1) × (s+1)` matrix with a `1` at
`(t, t+1)` whenever the `t`-th syllable (counting from `0`) is a power of `x_a`. Since consecutive
syllables have distinct letters, `N_a² = 0`, so `x_a ↦ 1 + N_a` (inverse `1 - N_a`) defines a
homomorphism `ρ` into the unit group with `ρ(x_a^e) = 1 + e N_a`. The `(0, s)` entry of `ρ(g)` is
`e₁ ⋯ e_s` (`corner_take`), which is nonzero once `p^k > |e₁ ⋯ e_s|`. Every `ρ(h)` is
unitriangular, and a unitriangular `d × d` matrix over `ZMod (p^k)` satisfies `U^((p^k)^d) = 1`
(`pow_eq_one_of_lowBand`), so `G ⧸ ker ρ` is a finite `p`-group.

## Strictly smaller subgroups

A normal subgroup `X` of finite index contains `x₀ ^ |G : X| ≠ 1`, which residual `p`-finiteness separates
from `1` (`exists_goodP_lt`).

Helper definitions and lemmas live in the namespace `LeanMachine.ResidualP`.
-/

namespace LeanMachine

namespace ResidualP

/-! ### Band conditions on square matrices -/

section Bands

variable {R : Type*} [CommRing R] {d : ℕ}

/-- `A i j = 0` whenever `j > i + m`. -/
def UpperBand (A : Matrix (Fin d) (Fin d) R) (m : ℕ) : Prop :=
  ∀ i j : Fin d, (i : ℕ) + m < j → A i j = 0

/-- `A i j = 0` whenever `j < i + m`; `LowBand A 1` means that `A` is strictly upper triangular. -/
def LowBand (A : Matrix (Fin d) (Fin d) R) (m : ℕ) : Prop :=
  ∀ i j : Fin d, (j : ℕ) < i + m → A i j = 0

theorem UpperBand.mul {A B : Matrix (Fin d) (Fin d) R} {a b : ℕ} (hA : UpperBand A a)
    (hB : UpperBand B b) : UpperBand (A * B) (a + b) := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases h : (i : ℕ) + a < l
  · rw [hA i l h, zero_mul]
  · rw [hB l j (by omega), mul_zero]

theorem upperBand_one : UpperBand (1 : Matrix (Fin d) (Fin d) R) 0 := by
  intro i j h
  rw [Matrix.one_apply_ne]
  rintro rfl
  omega

theorem LowBand.mul {A B : Matrix (Fin d) (Fin d) R} {a b : ℕ} (hA : LowBand A a)
    (hB : LowBand B b) : LowBand (A * B) (a + b) := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases h : (l : ℕ) < i + a
  · rw [hA i l h, zero_mul]
  · rw [hB l j (by omega), mul_zero]

theorem LowBand.mono {A : Matrix (Fin d) (Fin d) R} {a b : ℕ} (hA : LowBand A a) (h : b ≤ a) :
    LowBand A b := fun i j hij => hA i j (by omega)

theorem LowBand.add {A B : Matrix (Fin d) (Fin d) R} {a : ℕ} (hA : LowBand A a)
    (hB : LowBand B a) : LowBand (A + B) a := by
  intro i j hij
  rw [Matrix.add_apply, hA i j hij, hB i j hij, add_zero]

theorem LowBand.smul {A : Matrix (Fin d) (Fin d) R} {a : ℕ} (hA : LowBand A a) (c : R) :
    LowBand (c • A) a := by
  intro i j hij
  rw [Matrix.smul_apply, hA i j hij, smul_zero]

theorem LowBand.neg {A : Matrix (Fin d) (Fin d) R} {a : ℕ} (hA : LowBand A a) :
    LowBand (-A) a := by
  intro i j hij
  rw [Matrix.neg_apply, hA i j hij, neg_zero]

theorem lowBand_zero (a : ℕ) : LowBand (0 : Matrix (Fin d) (Fin d) R) a :=
  fun _ _ _ => rfl

theorem LowBand.eq_zero {A : Matrix (Fin d) (Fin d) R} {a : ℕ} (hA : LowBand A a) (h : d ≤ a) :
    A = 0 := by
  ext i j
  have := j.isLt
  exact hA i j (by omega)

/-- `(1 + M)^q ≡ 1 + q M` modulo matrices with `LowBand (l + 1)`, when `LowBand M l`, `l ≥ 1`. -/
theorem pow_one_add_of_lowBand {M : Matrix (Fin d) (Fin d) R} {l : ℕ} (hl : 1 ≤ l)
    (hM : LowBand M l) (q : ℕ) :
    ∃ M', LowBand M' (l + 1) ∧ (1 + M) ^ q = 1 + (q : R) • M + M' := by
  induction q with
  | zero => exact ⟨0, lowBand_zero _, by simp⟩
  | succ q ih =>
    obtain ⟨M', hM', h⟩ := ih
    refine ⟨(q : R) • (M * M) + (M' + M' * M), ?_, ?_⟩
    · refine LowBand.add ?_ (hM'.add ?_)
      · exact ((hM.mul hM).mono (by omega)).smul _
      · exact (hM'.mul hM).mono (by omega)
    · rw [pow_succ, h]
      push_cast
      simp only [add_mul, mul_add, mul_one, one_mul, smul_mul_assoc, add_smul, one_smul]
      abel

theorem pow_pow_one_add_of_lowBand {q : ℕ} (hq : (q : R) = 0) {M : Matrix (Fin d) (Fin d) R}
    (hM : LowBand M 1) (m : ℕ) : ∃ M', LowBand M' (m + 1) ∧ (1 + M) ^ (q ^ m) = 1 + M' := by
  induction m with
  | zero => exact ⟨M, hM, by simp⟩
  | succ m ih =>
    obtain ⟨M', hM', h⟩ := ih
    obtain ⟨M'', hM'', h'⟩ := pow_one_add_of_lowBand (by omega) hM' q
    refine ⟨M'', hM'', ?_⟩
    rw [pow_succ, pow_mul, h, h', hq, zero_smul, add_zero]

/-- A unitriangular `d × d` matrix over a ring in which `q = 0` satisfies `U ^ (q ^ d) = 1`. -/
theorem pow_eq_one_of_lowBand {q : ℕ} (hq : (q : R) = 0) {M : Matrix (Fin d) (Fin d) R}
    (hM : LowBand M 1) : (1 + M) ^ (q ^ d) = 1 := by
  obtain ⟨M', hM', h⟩ := pow_pow_one_add_of_lowBand hq hM d
  rw [h, hM'.eq_zero (by omega), add_zero]

end Bands

/-! ### Syllable form of free group elements -/

section Syllables

variable {r : ℕ}

/-- A valid syllable list: all exponents are nonzero and consecutive letters differ. -/
def SylValid (S : List (Fin r × ℤ)) : Prop :=
  (∀ x ∈ S, x.2 ≠ 0) ∧ S.IsChain (fun x y => x.1 ≠ y.1)

/-- The element `x_{a₁}^{e₁} ⋯ x_{a_s}^{e_s}` of the syllable list `[(a₁, e₁), …, (a_s, e_s)]`. -/
def sylProd (S : List (Fin r × ℤ)) : FreeGroup (Fin r) :=
  (S.map fun x => FreeGroup.of x.1 ^ x.2).prod

/-- Every element of the free group has a valid syllable form. -/
theorem exists_sylList (L : List (Fin r × Bool)) :
    ∃ S, SylValid S ∧ FreeGroup.mk L = sylProd S := by
  induction L with
  | nil => exact ⟨[], ⟨by simp, List.isChain_nil⟩, rfl⟩
  | cons x L ih =>
    obtain ⟨S, ⟨hS0, hSc⟩, hL⟩ := ih
    obtain ⟨ε, hε0, hx⟩ : ∃ ε : ℤ, ε ≠ 0 ∧ FreeGroup.mk [x] = FreeGroup.of x.1 ^ ε := by
      obtain ⟨a, b⟩ := x
      cases b
      · refine ⟨-1, by decide, ?_⟩
        rw [zpow_neg_one, FreeGroup.of, FreeGroup.inv_mk]
        rfl
      · exact ⟨1, one_ne_zero, by rw [zpow_one]; rfl⟩
    have hmk : FreeGroup.mk (x :: L) = FreeGroup.of x.1 ^ ε * FreeGroup.mk L := by
      rw [← hx, FreeGroup.mul_mk]
      rfl
    rw [hmk, hL]
    cases S with
    | nil =>
      refine ⟨[(x.1, ε)], ⟨by simpa using hε0, List.isChain_singleton _⟩, ?_⟩
      simp [sylProd]
    | cons y S =>
      by_cases hxy : y.1 = x.1
      · by_cases he : ε + y.2 = 0
        · refine ⟨S, ⟨fun z hz => hS0 z (List.mem_cons_of_mem _ hz), hSc.tail⟩, ?_⟩
          simp only [sylProd, List.map_cons, List.prod_cons]
          rw [hxy, ← mul_assoc, ← zpow_add, he, zpow_zero, one_mul]
        · refine ⟨(x.1, ε + y.2) :: S, ⟨?_, ?_⟩, ?_⟩
          · rw [List.forall_mem_cons]
            exact ⟨he, fun z hz => hS0 z (List.mem_cons_of_mem _ hz)⟩
          · rw [List.isChain_cons] at hSc ⊢
            refine ⟨fun z hz => ?_, hSc.2⟩
            show x.1 ≠ z.1
            rw [← hxy]
            exact hSc.1 z hz
          · simp only [sylProd, List.map_cons, List.prod_cons]
            rw [hxy, ← mul_assoc, ← zpow_add]
      · refine ⟨(x.1, ε) :: y :: S, ⟨?_, ?_⟩, ?_⟩
        · rw [List.forall_mem_cons]
          exact ⟨hε0, hS0⟩
        · rw [List.isChain_cons_cons]
          exact ⟨Ne.symm hxy, hSc⟩
        · simp only [sylProd, List.map_cons, List.prod_cons]

end Syllables

/-! ### The matrix representation attached to a syllable list -/

section Rep

variable {r : ℕ} {R : Type*} [CommRing R] (S : List (Fin r × ℤ))

/-- The letter of the `i`-th syllable, if there is one. -/
def letterAt (i : ℕ) : Option (Fin r) := (S[i]?).map Prod.fst

/-- The `(s+1) × (s+1)` matrix with a `1` at `(i, i+1)` whenever the `i`-th syllable is a power
of `x_a`. -/
def stepMat (a : Fin r) : Matrix (Fin (S.length + 1)) (Fin (S.length + 1)) R :=
  Matrix.of fun i j => if (j : ℕ) = i + 1 ∧ letterAt S i = some a then 1 else 0

theorem stepMat_apply (a : Fin r) (i j : Fin (S.length + 1)) :
    stepMat (R := R) S a i j = if (j : ℕ) = i + 1 ∧ letterAt S i = some a then 1 else 0 := rfl

theorem stepMat_mul_self (hS : S.IsChain (fun x y => x.1 ≠ y.1)) (a : Fin r) :
    stepMat (R := R) S a * stepMat S a = 0 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [stepMat_apply, stepMat_apply]
  by_cases h1 : (l : ℕ) = i + 1 ∧ letterAt S i = some a
  · by_cases h2 : (j : ℕ) = l + 1 ∧ letterAt S l = some a
    · exfalso
      obtain ⟨hl, hi⟩ := h1
      obtain ⟨-, hl'⟩ := h2
      rw [hl] at hl'
      simp only [letterAt, Option.map_eq_some_iff, List.getElem?_eq_some_iff] at hi hl'
      obtain ⟨x, ⟨hi1, hx⟩, hxa⟩ := hi
      obtain ⟨y, ⟨hi2, hy⟩, hya⟩ := hl'
      have := hS.getElem _ hi2
      rw [hx, hy, hxa, hya] at this
      exact this rfl
    · rw [ite_eq_right h2, mul_zero]
  · rw [ite_eq_right h1, zero_mul]

theorem lowBand_stepMat (a : Fin r) : LowBand (stepMat (R := R) S a) 1 := by
  intro i j hij
  rw [stepMat_apply, ite_eq_right]
  rintro ⟨h, -⟩
  omega

theorem upperBand_stepFactor (c : R) (a : Fin r) :
    UpperBand (1 + c • stepMat (R := R) S a) 1 := by
  intro i j hij
  rw [Matrix.add_apply, Matrix.one_apply_ne, Matrix.smul_apply, stepMat_apply, ite_eq_right,
    smul_zero, add_zero]
  · rintro ⟨h, -⟩
    omega
  · rintro rfl
    omega

/-- The entry `(l, j+1)` of `N_{a_j}`, where `a_j` is the letter of the `j`-th syllable. -/
theorem stepMat_apply_succ (j : ℕ) (hj : j < S.length) (l : Fin (S.length + 1)) :
    stepMat (R := R) S (S[j]).1 l ⟨j + 1, by omega⟩ = if (l : ℕ) = j then 1 else 0 := by
  rw [stepMat_apply]
  by_cases hl : (l : ℕ) = j
  · rw [ite_eq_left, ite_eq_left hl]
    refine ⟨by simp [hl], ?_⟩
    simp [letterAt, hl, List.getElem?_eq_getElem hj]
  · rw [ite_eq_right, ite_eq_right hl]
    rintro ⟨h, -⟩
    simp only at h
    omega

/-- The unit `1 + N_a`, with inverse `1 - N_a`. -/
def stepUnit (hS : S.IsChain (fun x y => x.1 ≠ y.1)) (a : Fin r) :
    (Matrix (Fin (S.length + 1)) (Fin (S.length + 1)) R)ˣ where
  val := 1 + stepMat S a
  inv := 1 - stepMat S a
  val_inv := by
    rw [add_mul, one_mul, mul_sub, mul_one, stepMat_mul_self S hS, sub_zero, sub_add_cancel]
  inv_val := by
    rw [sub_mul, one_mul, mul_add, mul_one, stepMat_mul_self S hS, add_zero, add_sub_cancel_right]

theorem stepUnit_zpow (hS : S.IsChain (fun x y => x.1 ≠ y.1)) (a : Fin r) (e : ℤ) :
    ((stepUnit (R := R) S hS a ^ e : (Matrix (Fin (S.length + 1)) (Fin (S.length + 1)) R)ˣ) :
      Matrix (Fin (S.length + 1)) (Fin (S.length + 1)) R) = 1 + (e : R) • stepMat S a := by
  induction e with
  | zero => simp
  | succ n ih =>
    rw [zpow_add_one, Units.val_mul, ih]
    show (1 + ((n : ℤ) : R) • stepMat S a) * (1 + stepMat S a) = _
    rw [mul_add, mul_one, add_mul, one_mul, smul_mul_assoc, stepMat_mul_self S hS, smul_zero,
      add_zero]
    push_cast
    rw [add_smul, one_smul]
    abel
  | pred n ih =>
    rw [zpow_sub_one, Units.val_mul, ih]
    show (1 + ((-(n : ℤ) : ℤ) : R) • stepMat S a) * (1 - stepMat S a) = _
    rw [mul_sub, mul_one, add_mul, one_mul, smul_mul_assoc, stepMat_mul_self S hS, smul_zero,
      add_zero]
    push_cast
    rw [sub_smul, one_smul]
    abel

/-- The image of the syllable product. -/
theorem lift_sylProd (hS : S.IsChain (fun x y => x.1 ≠ y.1)) :
    ((FreeGroup.lift (stepUnit (R := R) S hS) (sylProd S) :
        (Matrix (Fin (S.length + 1)) (Fin (S.length + 1)) R)ˣ) :
      Matrix (Fin (S.length + 1)) (Fin (S.length + 1)) R) =
      (S.map fun x => (1 + (x.2 : R) • stepMat (R := R) S x.1 :
        Matrix (Fin (S.length + 1)) (Fin (S.length + 1)) R)).prod := by
  rw [sylProd, map_list_prod, ← Units.coeHom_apply, map_list_prod, List.map_map, List.map_map]
  congr 1
  refine List.map_congr_left fun x _ => ?_
  simp only [Function.comp_apply, map_zpow, FreeGroup.lift_apply_of, Units.coeHom_apply]
  exact stepUnit_zpow S hS x.1 x.2

/-- Band and corner entry of the partial products `∏_{t < j} (1 + e_t N_{a_t})`. -/
theorem corner_take (j : ℕ) (hj : j ≤ S.length) :
    UpperBand ((S.take j).map fun x =>
        (1 + (x.2 : R) • stepMat (R := R) S x.1 :
          Matrix (Fin (S.length + 1)) (Fin (S.length + 1)) R)).prod j ∧
      ((S.take j).map fun x =>
        (1 + (x.2 : R) • stepMat (R := R) S x.1 :
          Matrix (Fin (S.length + 1)) (Fin (S.length + 1)) R)).prod 0 ⟨j, by omega⟩ =
        ((S.take j).map fun x => (x.2 : R)).prod := by
  induction j with
  | zero =>
    simp only [List.take_zero, List.map_nil, List.prod_nil]
    exact ⟨upperBand_one, Matrix.one_apply_eq _⟩
  | succ j ih =>
    obtain ⟨hband, hcorner⟩ := ih (by omega)
    have hjS : j < S.length := by omega
    rw [List.take_succ_eq_append_getElem hjS, List.map_append, List.prod_append, List.map_append,
      List.prod_append]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    refine ⟨hband.mul (upperBand_stepFactor S _ _), ?_⟩
    rw [Matrix.mul_apply, Finset.sum_eq_single ⟨j, by omega⟩]
    · rw [Matrix.add_apply, Matrix.one_apply_ne, Matrix.smul_apply, stepMat_apply_succ S j hjS,
        ite_eq_left rfl, smul_eq_mul, mul_one, zero_add]
      · exact congrArg (· * _) hcorner
      · intro h
        have := congrArg Fin.val h
        simp at this
    · intro l _ hl
      by_cases hl1 : (l : ℕ) = j + 1
      · rw [hband 0 l (by simp [hl1]), zero_mul]
      · rw [Matrix.add_apply, Matrix.one_apply_ne, Matrix.smul_apply, stepMat_apply_succ S j hjS,
          ite_eq_right, smul_zero, add_zero, mul_zero]
        · intro h
          exact hl (Fin.ext h)
        · intro h
          exact hl1 (congrArg Fin.val h)
    · intro h
      exact absurd (Finset.mem_univ _) h

theorem corner (hS : S.IsChain (fun x y => x.1 ≠ y.1)) :
    ((FreeGroup.lift (stepUnit (R := R) S hS) (sylProd S) :
        (Matrix (Fin (S.length + 1)) (Fin (S.length + 1)) R)ˣ) :
      Matrix (Fin (S.length + 1)) (Fin (S.length + 1)) R) 0 ⟨S.length, by omega⟩ =
      (((S.map Prod.snd).prod : ℤ) : R) := by
  rw [lift_sylProd S hS]
  have h := (corner_take (R := R) S S.length le_rfl).2
  rw [List.take_length] at h
  rw [h, Int.cast_list_prod, List.map_map]
  rfl

/-- Every element of the image is unitriangular. -/
theorem lift_unitriangular (hS : S.IsChain (fun x y => x.1 ≠ y.1)) (g : FreeGroup (Fin r)) :
    ∃ M, LowBand M 1 ∧ ((FreeGroup.lift (stepUnit (R := R) S hS) g :
        (Matrix (Fin (S.length + 1)) (Fin (S.length + 1)) R)ˣ) :
      Matrix (Fin (S.length + 1)) (Fin (S.length + 1)) R) = 1 + M := by
  induction g with
  | one => exact ⟨0, lowBand_zero _, by simp⟩
  | of a =>
    refine ⟨stepMat S a, lowBand_stepMat S a, ?_⟩
    rw [FreeGroup.lift_apply_of]
    rfl
  | inv_of a _ =>
    refine ⟨-stepMat S a, (lowBand_stepMat S a).neg, ?_⟩
    rw [map_inv, FreeGroup.lift_apply_of, ← sub_eq_add_neg]
    rfl
  | mul x y hx hy =>
    obtain ⟨M₁, h₁, e₁⟩ := hx
    obtain ⟨M₂, h₂, e₂⟩ := hy
    refine ⟨M₁ + M₂ + M₁ * M₂, (h₁.add h₂).add ((h₁.mul h₂).mono (by omega)), ?_⟩
    rw [map_mul, Units.val_mul, e₁, e₂]
    simp only [add_mul, mul_add, one_mul, mul_one]
    abel

end Rep

/-! ### Residual `p`-finiteness -/

/-- `G ⧸ H` is a `p`-group iff every element of `G` has a `p`-power power in `H`. -/
theorem isPGroup_quotient_iff {G : Type*} [Group G] (p : ℕ) (H : Subgroup G) [H.Normal] :
    IsPGroup p (G ⧸ H) ↔ ∀ g : G, ∃ k : ℕ, g ^ p ^ k ∈ H := by
  constructor
  · intro h g
    obtain ⟨k, hk⟩ := h (g : G ⧸ H)
    exact ⟨k, by rwa [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hk⟩
  · intro h x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨k, hk⟩ := h g
    exact ⟨k, by rwa [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]⟩

end ResidualP

open ResidualP

/-- Free groups of finite rank are residually finite `p`-groups. -/
theorem freeGroup_residually_pGroup (p : ℕ) [Fact p.Prime] (r : ℕ) (g : FreeGroup (Fin r))
    (hg : g ≠ 1) :
    ∃ (N : Subgroup (FreeGroup (Fin r))) (_ : N.Normal), N.FiniteIndex ∧
      IsPGroup p (FreeGroup (Fin r) ⧸ N) ∧ g ∉ N := by
  have hp : p.Prime := Fact.out
  obtain ⟨S, ⟨hS0, hS⟩, hgS⟩ := exists_sylList g.toWord
  rw [FreeGroup.mk_toWord] at hgS
  have hSne : S ≠ [] := by
    rintro rfl
    exact hg hgS
  have hE : (S.map Prod.snd).prod ≠ 0 := by
    refine List.prod_ne_zero ?_
    simp only [List.mem_map, not_exists, not_and]
    intro x hx h0
    exact hS0 x hx h0
  set k := ((S.map Prod.snd).prod).natAbs with hk
  have : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  set ρ := FreeGroup.lift (stepUnit (R := ZMod (p ^ k)) S hS) with hρ
  refine ⟨ρ.ker, inferInstance, inferInstance, ?_, ?_⟩
  · rw [isPGroup_quotient_iff]
    intro h
    refine ⟨k * (S.length + 1), ?_⟩
    rw [MonoidHom.mem_ker, map_pow]
    obtain ⟨M, hM, hρh⟩ := lift_unitriangular (R := ZMod (p ^ k)) S hS h
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hρh, pow_mul, Units.val_one]
    exact pow_eq_one_of_lowBand (by exact_mod_cast ZMod.natCast_self (p ^ k)) hM
  · rw [MonoidHom.mem_ker]
    intro h1
    have h2 : ((ρ g : (Matrix (Fin (S.length + 1)) (Fin (S.length + 1)) (ZMod (p ^ k)))ˣ) :
        Matrix (Fin (S.length + 1)) (Fin (S.length + 1)) (ZMod (p ^ k))) 0 ⟨S.length, by omega⟩ =
        ((1 : (Matrix (Fin (S.length + 1)) (Fin (S.length + 1)) (ZMod (p ^ k)))ˣ) :
          Matrix (Fin (S.length + 1)) (Fin (S.length + 1)) (ZMod (p ^ k))) 0
            ⟨S.length, by omega⟩ := by
      rw [h1]
    rw [hgS, hρ, corner S hS, Units.val_one, Matrix.one_apply_ne] at h2
    · rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h2
      have h3 : p ^ k ∣ k := by
        rw [hk]
        exact Int.natCast_dvd.mp (by exact_mod_cast h2)
      have h4 : k < p ^ k := Nat.lt_pow_self hp.one_lt
      have h5 : 0 < k := Int.natAbs_pos.mpr hE
      exact absurd (Nat.le_of_dvd h5 h3) (not_le.mpr h4)
    · intro h
      have := congrArg Fin.val h
      simp only [Fin.val_zero] at this
      exact hSne (List.length_eq_zero_iff.mp this.symm)

/-! ### `p`-chains -/

namespace ResidualP

/-- Normal subgroups of finite index modulo which every element has `p`-power order. -/
def GoodP (p : ℕ) {G : Type*} [Group G] (H : Subgroup G) : Prop :=
  H.Normal ∧ H.FiniteIndex ∧ ∀ g : G, ∃ k : ℕ, g ^ p ^ k ∈ H

theorem goodP_top (p : ℕ) {G : Type*} [Group G] : GoodP p (⊤ : Subgroup G) :=
  ⟨inferInstance, inferInstance, fun _ => ⟨0, Subgroup.mem_top _⟩⟩

theorem GoodP.inf {p : ℕ} {G : Type*} [Group G] {A B : Subgroup G} (hA : GoodP p A)
    (hB : GoodP p B) : GoodP p (A ⊓ B) := by
  obtain ⟨hA1, hA2, hA3⟩ := hA
  obtain ⟨hB1, hB2, hB3⟩ := hB
  refine ⟨inferInstance, inferInstance, fun g => ?_⟩
  obtain ⟨a, ha⟩ := hA3 g
  obtain ⟨b, hb⟩ := hB3 g
  refine ⟨a + b, Subgroup.mem_inf.mpr ⟨?_, ?_⟩⟩
  · rw [pow_add, pow_mul]
    exact A.pow_mem ha _
  · rw [pow_add, mul_comm, pow_mul]
    exact B.pow_mem hb _

theorem goodP_of_residual {p : ℕ} {G : Type*} [Group G] {N : Subgroup G} (hN : N.Normal)
    (hF : N.FiniteIndex) (hP : IsPGroup p (G ⧸ N)) : GoodP p N :=
  ⟨hN, hF, (isPGroup_quotient_iff p N).mp hP⟩

/-- Below every `GoodP` subgroup of `FreeGroup (Fin r)`, `r > 0`, there is a strictly smaller
one. -/
theorem exists_goodP_lt (p : ℕ) [Fact p.Prime] {r : ℕ} (hr : 0 < r)
    {X : Subgroup (FreeGroup (Fin r))} (hX : GoodP p X) : ∃ Y, GoodP p Y ∧ Y < X := by
  obtain ⟨hX1, hX2, hX3⟩ := hX
  have hgX : FreeGroup.of (⟨0, hr⟩ : Fin r) ^ X.index ∈ X := X.pow_index_mem _
  have hg1 : FreeGroup.of (⟨0, hr⟩ : Fin r) ^ X.index ≠ 1 := by
    rw [Ne, ← FreeGroup.norm_eq_zero, FreeGroup.norm_of_pow]
    exact hX2.index_ne_zero
  obtain ⟨K, hK1, hK2, hK3, hgK⟩ := freeGroup_residually_pGroup p r _ hg1
  refine ⟨X ⊓ K, GoodP.inf ⟨hX1, hX2, hX3⟩ (goodP_of_residual hK1 hK2 hK3), ?_⟩
  refine lt_of_le_of_ne inf_le_left fun h => hgK ?_
  have : FreeGroup.of (⟨0, hr⟩ : Fin r) ^ X.index ∈ X ⊓ K := by
    rw [h]
    exact hgX
  exact (Subgroup.mem_inf.mp this).2

end ResidualP

end LeanMachine
