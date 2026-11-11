import BoundedArityDecoders.SwapCodeAnswers
import Mathlib.Data.Sym.Card
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Proofs — Two Bonus Answers to Concrete Questions in Paper 17

Complete kernel-verified proofs for all four unconditional claim specifications in
`BoundedArityDecoders.SwapCodeAnswers` together with two structural Walsh-mask bridge theorems:
* `bonus1_ThreeTermBlockSwapCodeDim`
* `bonus1_ThreeTermPaddedSevenAndFive`
* `bonus2_MultiscaleIntervalBothSides`
* `bonus2_MultiscaleFullProfileAttainsFullSwap`
* `walshDigitMask_in_periodicDyadicSpan`
* `openTarget_walsh_of_periodicProfile`
-/

namespace BoundedArityDecoders

open Module Matrix
open scoped BigOperators

/-! ### 1. Bonus 1: Unified Padded & Unpadded 3-Term Block Swap Codes -/

section Bonus1Proofs

/-- Embedding of `3 × m` block-offset coordinates `(i, u)` into `Fin d` when `3 * m ≤ d`. -/
private def padIdx {m d : ℕ} (hd : 3 * m ≤ d) (i : Fin 3) (u : Fin m) : Fin d :=
  ⟨i.val * m + u.val, by
    have hi := i.isLt
    have hu := u.isLt
    nlinarith⟩

private lemma padIdx_val_lt {m d : ℕ} (hd : 3 * m ≤ d) (i : Fin 3) (u : Fin m) :
    (padIdx hd i u).val < 3 * m := by
  show i.val * m + u.val < 3 * m
  have hi := i.isLt
  have hu := u.isLt
  nlinarith

private lemma padIdx_div {m d : ℕ} [NeZero m] (hd : 3 * m ≤ d) (i : Fin 3) (u : Fin m) :
    (padIdx hd i u).val / m = i.val := by
  have hm : 0 < m := NeZero.pos m
  show (i.val * m + u.val) / m = i.val
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt u.isLt, zero_add]

private lemma padIdx_mod {m d : ℕ} [NeZero m] (hd : 3 * m ≤ d) (i : Fin 3) (u : Fin m) :
    (padIdx hd i u).val % m = u.val := by
  show (i.val * m + u.val) % m = u.val
  exact Nat.mul_add_mod_of_lt u.isLt

private def blkOf {m d : ℕ} {r : Fin d} (hr : r.val < 3 * m) : Fin 3 :=
  ⟨r.val / m, Nat.div_lt_of_lt_mul (by omega)⟩

private def offOf {m d : ℕ} [NeZero m] (r : Fin d) : Fin m :=
  ⟨r.val % m, Nat.mod_lt _ (NeZero.pos m)⟩

private lemma padIdx_blkOf_offOf {m d : ℕ} [NeZero m] (hd : 3 * m ≤ d)
    {r : Fin d} (hr : r.val < 3 * m) :
    padIdx hd (blkOf hr) (offOf r) = r := by
  apply Fin.ext
  show (r.val / m) * m + r.val % m = r.val
  exact Nat.div_add_mod' r.val m

private lemma blkOf_padIdx {m d : ℕ} [NeZero m] (hd : 3 * m ≤ d) (i : Fin 3) (u : Fin m) :
    blkOf (padIdx_val_lt hd i u) = i :=
  Fin.ext (padIdx_div hd i u)

private lemma offOf_padIdx {m d : ℕ} [NeZero m] (hd : 3 * m ≤ d) (i : Fin 3) (u : Fin m) :
    offOf (padIdx hd i u) = u :=
  Fin.ext (padIdx_mod hd i u)

private lemma exists_eq_padIdx {m d : ℕ} [NeZero m] (hd : 3 * m ≤ d)
    {r : Fin d} (hr : r.val < 3 * m) :
    ∃ (i : Fin 3) (u : Fin m), r = padIdx hd i u :=
  ⟨blkOf hr, offOf r, (padIdx_blkOf_offOf hd hr).symm⟩

private lemma skew_ite_neg {F : Type*} [Ring F] (P Q R : Prop)
    [Decidable P] [Decidable Q] [Decidable R] (hQR : ¬ (Q ∧ R)) :
    (if P then (if R then (1 : F) else if Q then -1 else 0) else 0) =
      - (if P then (if Q then (1 : F) else if R then -1 else 0) else 0) := by
  by_cases hP : P
  · by_cases hQ : Q
    · have hR : ¬ R := fun hr => hQR ⟨hQ, hr⟩
      simp [hP, hQ, hR]
    · by_cases hR : R <;> simp [hP, hQ, hR]
  · simp [hP]

private lemma fin2_eq (b : Fin 2) : b = 0 ∨ b = 1 := by
  rcases b with ⟨v, hv⟩
  have h : v = 0 ∨ v = 1 := by omega
  rcases h with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

private lemma fin3_eq (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
  rcases i with ⟨v, hv⟩
  have h : v = 0 ∨ v = 1 ∨ v = 2 := by omega
  rcases h with rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

private lemma fin8_eq (k : Fin 8) :
    k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by
  rcases k with ⟨v, hv⟩
  have h : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5 ∨ v = 6 ∨ v = 7 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))

/-- When `d = 3 * m`, `threeTermPaddedA` and `threeTermPaddedB` coincide with
`threeTermBlockA` and `threeTermBlockB`. -/
private lemma threeTermPadded_eq_block (F : Type*) [Ring F] (m : ℕ) [NeZero m] :
    threeTermPaddedA F m (3 * m) = threeTermBlockA F m ∧
    threeTermPaddedB F m (3 * m) = threeTermBlockB F m := by
  constructor
  · funext t
    ext r c
    simp [threeTermPaddedA, threeTermBlockA]
  · funext t
    ext r c
    rcases fin3_eq t with rfl | rfl | rfl
    · dsimp only [threeTermPaddedB, threeTermBlockB, threeTermBlockA, threeTermPair]
      simp only [r.isLt, c.isLt, and_self, ite_true, Matrix.neg_apply, Matrix.of_apply]
      exact skew_ite_neg _ _ _ (by omega)
    · dsimp only [threeTermPaddedB, threeTermBlockB, threeTermBlockA, threeTermPair]
      simp only [r.isLt, c.isLt, and_self, ite_true, Matrix.neg_apply, Matrix.of_apply]
      exact skew_ite_neg _ _ _ (by omega)
    · dsimp only [threeTermPaddedB, threeTermBlockB, threeTermBlockA, threeTermPair]
      simp only [r.isLt, c.isLt, and_self, ite_true, Matrix.neg_apply, Matrix.of_apply]
      exact skew_ite_neg _ _ _ (by omega)

/-- Relation between `threeTermPaddedB` and `threeTermPaddedA` by row region. -/
private lemma threeTermPaddedB_eq_of_region (F : Type*) [Ring F] (m d : ℕ) [NeZero m]
    (t : Fin 3) (c c' : Fin d) :
    threeTermPaddedB F m d t c c' =
      if c.val < 3 * m then - threeTermPaddedA F m d t c c'
      else threeTermPaddedA F m d t c c' := by
  by_cases hc : c.val < 3 * m
  · rw [ite_eq_left hc]
    by_cases hc' : c'.val < 3 * m
    · rcases fin3_eq t with rfl | rfl | rfl
      · dsimp only [threeTermPaddedB, threeTermPaddedA, threeTermPair]
        simp only [hc, hc', and_self, ite_true, Matrix.of_apply]
        exact skew_ite_neg _ _ _ (by omega)
      · dsimp only [threeTermPaddedB, threeTermPaddedA, threeTermPair]
        simp only [hc, hc', and_self, ite_true, Matrix.of_apply]
        exact skew_ite_neg _ _ _ (by omega)
      · dsimp only [threeTermPaddedB, threeTermPaddedA, threeTermPair]
        simp only [hc, hc', and_self, ite_true, Matrix.of_apply]
        exact skew_ite_neg _ _ _ (by omega)
    · have hge : ¬ 3 * m ≤ c.val := by omega
      simp [threeTermPaddedB, threeTermPaddedA, hc', hge]
  · rw [ite_eq_right hc]
    simp [threeTermPaddedB, threeTermPaddedA, hc]

/-- Row-sum evaluation of `threeTermPaddedA` on tail rows `3 * m ≤ r.val`. -/
private lemma sum_threeTermPaddedA_tail {F : Type*} [Ring F] {m d : ℕ} [NeZero m]
    (t : Fin 3) {r : Fin d} (hr : 3 * m ≤ r.val) (f : Fin d → F) :
    (∑ r' : Fin d, threeTermPaddedA F m d t r r' * f r') =
      if t.val = 2 then f r else 0 := by
  have hlt : ¬ r.val < 3 * m := by omega
  by_cases ht : t.val = 2
  · rw [ite_eq_left ht, Finset.sum_eq_single r]
    · simp [threeTermPaddedA, hlt, hr, ht]
    · intro r' _ hr'
      have hval : r.val ≠ r'.val := fun h => hr' (Fin.ext h.symm)
      simp [threeTermPaddedA, hlt, hval]
    · intro h
      exact absurd (Finset.mem_univ r) h
  · rw [ite_eq_right ht]
    refine Finset.sum_eq_zero fun r' _ => ?_
    simp [threeTermPaddedA, hlt, ht]

/-- Row-sum evaluation of `threeTermPaddedA` on block rows `padIdx hd i u`. -/
private lemma sum_threeTermPaddedA_padIdx {F : Type*} [Ring F] {m d : ℕ} [NeZero m]
    (hd : 3 * m ≤ d) (t : Fin 3) (i : Fin 3) (u : Fin m) (f : Fin d → F) :
    (∑ r' : Fin d, threeTermPaddedA F m d t (padIdx hd i u) r' * f r') =
      if hj₀ : i.val = (threeTermPair t).1 ∧ (threeTermPair t).2 < 3 then
        f (padIdx hd ⟨(threeTermPair t).2, hj₀.2⟩ u)
      else if hi₀ : i.val = (threeTermPair t).2 ∧ (threeTermPair t).1 < 3 then
        - f (padIdx hd ⟨(threeTermPair t).1, hi₀.2⟩ u)
      else 0 := by
  have hr_lt : (padIdx hd i u).val < 3 * m := padIdx_val_lt hd i u
  have hr_ge : ¬ 3 * m ≤ (padIdx hd i u).val := by omega
  have hr_div : (padIdx hd i u).val / m = i.val := padIdx_div hd i u
  have hr_mod : (padIdx hd i u).val % m = u.val := padIdx_mod hd i u
  have hp_lt : (threeTermPair t).1 < 3 ∧ (threeTermPair t).2 < 3 ∧
      (threeTermPair t).1 ≠ (threeTermPair t).2 := by
    rcases fin3_eq t with rfl | rfl | rfl <;> simp [threeTermPair]
  set i₀ := (threeTermPair t).1
  set j₀ := (threeTermPair t).2
  by_cases h1 : i.val = i₀
  · have hj₀_cond : i.val = i₀ ∧ j₀ < 3 := ⟨h1, hp_lt.2.1⟩
    rw [dite_eq_left hj₀_cond]
    let r'₀ := padIdx hd ⟨j₀, hp_lt.2.1⟩ u
    rw [Finset.sum_eq_single r'₀]
    · have hr'₀_lt := padIdx_val_lt hd ⟨j₀, hp_lt.2.1⟩ u
      have hr'₀_div := padIdx_div hd ⟨j₀, hp_lt.2.1⟩ u
      have hr'₀_mod := padIdx_mod hd ⟨j₀, hp_lt.2.1⟩ u
      simp [threeTermPaddedA, r'₀, i₀, j₀, hr_lt, hr'₀_lt, hr_div, hr_mod, hr'₀_div, hr'₀_mod, h1]
    · intro r' _ hr'
      by_cases hc' : r'.val < 3 * m
      · by_cases hm_eq : u.val = r'.val % m
        · have hdiv_ne : r'.val / m ≠ j₀ := by
            intro hdiv_eq
            apply hr'
            rw [← padIdx_blkOf_offOf hd hc']
            congr 1
            · exact Fin.ext hdiv_eq
            · exact Fin.ext hm_eq.symm
          have hne_ji : ¬ (i.val = j₀ ∧ r'.val / m = i₀) := fun h => hp_lt.2.2 (h1.symm.trans h.1)
          simp [threeTermPaddedA, i₀, j₀, hr_lt, hc', hr_div, hr_mod, hm_eq, hdiv_ne, hne_ji]
        · simp [threeTermPaddedA, hr_lt, hc', hr_mod, hm_eq]
      · simp [threeTermPaddedA, hc', hr_ge]
    · intro h
      exact absurd (Finset.mem_univ r'₀) h
  · have hj₀_not : ¬ (i.val = i₀ ∧ j₀ < 3) := fun h => h1 h.1
    rw [dite_eq_right hj₀_not]
    by_cases h2 : i.val = j₀
    · have hi₀_cond : i.val = j₀ ∧ i₀ < 3 := ⟨h2, hp_lt.1⟩
      rw [dite_eq_left hi₀_cond]
      let r'₀ := padIdx hd ⟨i₀, hp_lt.1⟩ u
      rw [Finset.sum_eq_single r'₀]
      · have hr'₀_lt := padIdx_val_lt hd ⟨i₀, hp_lt.1⟩ u
        have hr'₀_div := padIdx_div hd ⟨i₀, hp_lt.1⟩ u
        have hr'₀_mod := padIdx_mod hd ⟨i₀, hp_lt.1⟩ u
        have hji : j₀ ≠ i₀ := hp_lt.2.2.symm
        simp [threeTermPaddedA, r'₀, i₀, j₀, hr_lt, hr'₀_lt, hr_div, hr_mod,
          hr'₀_div, hr'₀_mod, h2, hji]
      · intro r' _ hr'
        by_cases hc' : r'.val < 3 * m
        · by_cases hm_eq : u.val = r'.val % m
          · have hdiv_ne : r'.val / m ≠ i₀ := by
              intro hdiv_eq
              apply hr'
              rw [← padIdx_blkOf_offOf hd hc']
              congr 1
              · exact Fin.ext hdiv_eq
              · exact Fin.ext hm_eq.symm
            simp [threeTermPaddedA, i₀, hr_lt, hc', hr_div, hr_mod, hm_eq, h1, hdiv_ne]
          · simp [threeTermPaddedA, hr_lt, hc', hr_mod, hm_eq]
        · simp [threeTermPaddedA, hc', hr_ge]
      · intro h
        exact absurd (Finset.mem_univ r'₀) h
    · have hi₀_not : ¬ (i.val = j₀ ∧ i₀ < 3) := fun h => h2 h.1
      rw [dite_eq_right hi₀_not]
      refine Finset.sum_eq_zero fun r' _ => ?_
      by_cases hc' : r'.val < 3 * m
      · simp [threeTermPaddedA, i₀, j₀, hr_lt, hc', hr_div, h1, h2]
      · simp [threeTermPaddedA, hc', hr_ge]

/-- Explicit structural predicate characterizing `swapCode (threeTermPaddedA F m d) (threeTermPaddedB F m d)`
whenever `3 * m ≤ d`. -/
private def IsPaddedThreeTermCode (m d : ℕ) [NeZero m] (hd : 3 * m ≤ d) {F : Type*} [Ring F]
    (X : Matrix (Fin d) (Fin d) F) : Prop :=
  (∀ (i j : Fin 3) (u v : Fin m),
    X (padIdx hd i u) (padIdx hd j v) = X (padIdx hd i v) (padIdx hd j u)) ∧
  (∀ u v : Fin m,
    X (padIdx hd 0 u) (padIdx hd 0 v) +
      X (padIdx hd 1 u) (padIdx hd 1 v) +
      X (padIdx hd 2 u) (padIdx hd 2 v) = 0) ∧
  (∀ r : Fin d, 3 * m ≤ r.val → ∀ u : Fin m,
    X r (padIdx hd 0 u) = 0 ∧
    X (padIdx hd 0 u) r = 0 ∧
    X (padIdx hd 1 u) r = - X r (padIdx hd 2 u) ∧
    X (padIdx hd 2 u) r = X r (padIdx hd 1 u)) ∧
  (∀ r c : Fin d, 3 * m ≤ r.val → 3 * m ≤ c.val → X c r = X r c)

private lemma mem_swapCode_padded_iff {F : Type*} [Field F] {m d : ℕ} [NeZero m]
    (hd : 3 * m ≤ d) (X : Matrix (Fin d) (Fin d) F) :
    X ∈ SwapRigidity.swapCode (threeTermPaddedA F m d) (threeTermPaddedB F m d) ↔
      IsPaddedThreeTermCode m d hd X := by
  have col_padIdx : ∀ (t : Fin 3) (j : Fin 3) (v : Fin m) (r' : Fin d),
      (∑ c' : Fin d, X r' c' * threeTermPaddedB F m d t (padIdx hd j v) c') =
        - ∑ c' : Fin d, threeTermPaddedA F m d t (padIdx hd j v) c' * X r' c' := by
    intro t j v r'
    have hj_lt := padIdx_val_lt hd j v
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c' _ => ?_
    rw [threeTermPaddedB_eq_of_region, ite_eq_left hj_lt]
    ring
  have col_tail : ∀ (t : Fin 3) {c : Fin d} (hc : 3 * m ≤ c.val) (r' : Fin d),
      (∑ c' : Fin d, X r' c' * threeTermPaddedB F m d t c c') =
        if t.val = 2 then X r' c else 0 := by
    intro t c hc r'
    have hc_not : ¬ c.val < 3 * m := by omega
    calc (∑ c' : Fin d, X r' c' * threeTermPaddedB F m d t c c')
        = ∑ c' : Fin d, threeTermPaddedA F m d t c c' * X r' c' := by
            refine Finset.sum_congr rfl fun c' _ => ?_
            rw [threeTermPaddedB_eq_of_region, ite_eq_right hc_not, mul_comm]
      _ = if t.val = 2 then X r' c else 0 := sum_threeTermPaddedA_tail t hc _
  have eval_rhs_blk_blk : ∀ (i j : Fin 3) (u v : Fin m),
      (∑ t : Fin 3, ∑ r' : Fin d, ∑ c' : Fin d,
          threeTermPaddedA F m d t (padIdx hd i u) r' * X r' c' *
            threeTermPaddedB F m d t (padIdx hd j v) c') =
        if i = j then
          if i.val = 0 then
            - X (padIdx hd 1 u) (padIdx hd 1 v) - X (padIdx hd 2 u) (padIdx hd 2 v)
          else if i.val = 1 then
            - X (padIdx hd 0 u) (padIdx hd 0 v) - X (padIdx hd 2 u) (padIdx hd 2 v)
          else
            - X (padIdx hd 0 u) (padIdx hd 0 v) - X (padIdx hd 1 u) (padIdx hd 1 v)
        else X (padIdx hd j u) (padIdx hd i v) := by
    intro i j u v
    have factor : ∀ t : Fin 3,
        (∑ r' : Fin d, ∑ c' : Fin d,
            threeTermPaddedA F m d t (padIdx hd i u) r' * X r' c' *
              threeTermPaddedB F m d t (padIdx hd j v) c') =
        ∑ r' : Fin d, threeTermPaddedA F m d t (padIdx hd i u) r' *
          (- ∑ c' : Fin d, threeTermPaddedA F m d t (padIdx hd j v) c' * X r' c') := by
      intro t
      refine Finset.sum_congr rfl fun r' _ => ?_
      rw [← col_padIdx, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c' _ => ?_
      ring
    simp only [factor, Fin.sum_univ_three]
    rcases fin3_eq i with rfl | rfl | rfl <;> rcases fin3_eq j with rfl | rfl | rfl <;>
      simp only [sum_threeTermPaddedA_padIdx, threeTermPair] <;>
      simp <;> ring
  have eval_rhs_blk_tail : ∀ (i : Fin 3) (u : Fin m) {c : Fin d} (hc : 3 * m ≤ c.val),
      (∑ t : Fin 3, ∑ r' : Fin d, ∑ c' : Fin d,
          threeTermPaddedA F m d t (padIdx hd i u) r' * X r' c' *
            threeTermPaddedB F m d t c c') =
        if i.val = 0 then 0
        else if i.val = 1 then X (padIdx hd 2 u) c
        else - X (padIdx hd 1 u) c := by
    intro i u c hc
    have factor : ∀ t : Fin 3,
        (∑ r' : Fin d, ∑ c' : Fin d,
            threeTermPaddedA F m d t (padIdx hd i u) r' * X r' c' *
              threeTermPaddedB F m d t c c') =
        ∑ r' : Fin d, threeTermPaddedA F m d t (padIdx hd i u) r' *
          (if t.val = 2 then X r' c else 0) := by
      intro t
      refine Finset.sum_congr rfl fun r' _ => ?_
      rw [← col_tail t hc r', Finset.mul_sum]
      refine Finset.sum_congr rfl fun c' _ => ?_
      ring
    simp only [factor, Fin.sum_univ_three]
    rcases fin3_eq i with rfl | rfl | rfl <;>
      simp only [sum_threeTermPaddedA_padIdx, threeTermPair] <;>
      simp
  have eval_rhs_tail_blk : ∀ {r : Fin d} (hr : 3 * m ≤ r.val) (j : Fin 3) (v : Fin m),
      (∑ t : Fin 3, ∑ r' : Fin d, ∑ c' : Fin d,
          threeTermPaddedA F m d t r r' * X r' c' *
            threeTermPaddedB F m d t (padIdx hd j v) c') =
        if j.val = 0 then 0
        else if j.val = 1 then - X r (padIdx hd 2 v)
        else X r (padIdx hd 1 v) := by
    intro r hr j v
    have factor : ∀ t : Fin 3,
        (∑ r' : Fin d, ∑ c' : Fin d,
            threeTermPaddedA F m d t r r' * X r' c' *
              threeTermPaddedB F m d t (padIdx hd j v) c') =
        ∑ r' : Fin d, threeTermPaddedA F m d t r r' *
          (- ∑ c' : Fin d, threeTermPaddedA F m d t (padIdx hd j v) c' * X r' c') := by
      intro t
      refine Finset.sum_congr rfl fun r' _ => ?_
      rw [← col_padIdx, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c' _ => ?_
      ring
    simp only [factor, Fin.sum_univ_three, sum_threeTermPaddedA_tail _ hr]
    rcases fin3_eq j with rfl | rfl | rfl <;>
      simp only [sum_threeTermPaddedA_padIdx, threeTermPair] <;>
      simp
  have eval_rhs_tail_tail : ∀ {r c : Fin d} (hr : 3 * m ≤ r.val) (hc : 3 * m ≤ c.val),
      (∑ t : Fin 3, ∑ r' : Fin d, ∑ c' : Fin d,
          threeTermPaddedA F m d t r r' * X r' c' *
            threeTermPaddedB F m d t c c') = X r c := by
    intro r c hr hc
    have factor : ∀ t : Fin 3,
        (∑ r' : Fin d, ∑ c' : Fin d,
            threeTermPaddedA F m d t r r' * X r' c' *
              threeTermPaddedB F m d t c c') =
        ∑ r' : Fin d, threeTermPaddedA F m d t r r' *
          (if t.val = 2 then X r' c else 0) := by
      intro t
      refine Finset.sum_congr rfl fun r' _ => ?_
      rw [← col_tail t hc r', Finset.mul_sum]
      refine Finset.sum_congr rfl fun c' _ => ?_
      ring
    simp [factor, Fin.sum_univ_three, sum_threeTermPaddedA_tail _ hr]
  rw [SwapRigidity.mem_swapCode_iff_apply]
  constructor
  · intro hX
    have hdiag0 : ∀ u v : Fin m,
        X (padIdx hd 0 v) (padIdx hd 0 u) =
          - X (padIdx hd 1 u) (padIdx hd 1 v) - X (padIdx hd 2 u) (padIdx hd 2 v) := by
      intro u v
      have h := hX (padIdx hd 0 v) (padIdx hd 0 u)
      rw [eval_rhs_blk_blk] at h
      simpa using h
    have hdiag1 : ∀ u v : Fin m,
        X (padIdx hd 1 v) (padIdx hd 1 u) =
          - X (padIdx hd 0 u) (padIdx hd 0 v) - X (padIdx hd 2 u) (padIdx hd 2 v) := by
      intro u v
      have h := hX (padIdx hd 1 v) (padIdx hd 1 u)
      rw [eval_rhs_blk_blk] at h
      simpa using h
    have hdiag2 : ∀ u v : Fin m,
        X (padIdx hd 2 v) (padIdx hd 2 u) =
          - X (padIdx hd 0 u) (padIdx hd 0 v) - X (padIdx hd 1 u) (padIdx hd 1 v) := by
      intro u v
      have h := hX (padIdx hd 2 v) (padIdx hd 2 u)
      rw [eval_rhs_blk_blk] at h
      simpa using h
    have htrace : ∀ u v : Fin m,
        X (padIdx hd 0 u) (padIdx hd 0 v) +
          X (padIdx hd 1 u) (padIdx hd 1 v) +
          X (padIdx hd 2 u) (padIdx hd 2 v) = 0 := by
      intro u v
      have e0 := hdiag0 v u
      have e1 := hdiag1 u v
      have e2 := hdiag2 u v
      rw [e1, e2] at e0
      calc X (padIdx hd 0 u) (padIdx hd 0 v) +
            X (padIdx hd 1 u) (padIdx hd 1 v) +
            X (padIdx hd 2 u) (padIdx hd 2 v)
          = (-(- X (padIdx hd 0 u) (padIdx hd 0 v) - X (padIdx hd 2 u) (padIdx hd 2 v)) -
             (- X (padIdx hd 0 u) (padIdx hd 0 v) - X (padIdx hd 1 u) (padIdx hd 1 v))) -
            X (padIdx hd 0 u) (padIdx hd 0 v) := by abel
        _ = X (padIdx hd 0 u) (padIdx hd 0 v) - X (padIdx hd 0 u) (padIdx hd 0 v) := by rw [← e0]
        _ = 0 := sub_self _
    refine ⟨?_, htrace, ?_, ?_⟩
    · intro i j u v
      by_cases hij : j = i
      · subst hij
        rcases fin3_eq j with rfl | rfl | rfl
        · have e0 := hdiag0 v u
          have ht := htrace v u
          rw [e0]
          calc - X (padIdx hd 1 v) (padIdx hd 1 u) - X (padIdx hd 2 v) (padIdx hd 2 u)
              = X (padIdx hd 0 v) (padIdx hd 0 u) -
                (X (padIdx hd 0 v) (padIdx hd 0 u) +
                  X (padIdx hd 1 v) (padIdx hd 1 u) +
                  X (padIdx hd 2 v) (padIdx hd 2 u)) := by abel
            _ = X (padIdx hd 0 v) (padIdx hd 0 u) := by rw [ht, sub_zero]
        · have e1 := hdiag1 v u
          have ht := htrace v u
          rw [e1]
          calc - X (padIdx hd 0 v) (padIdx hd 0 u) - X (padIdx hd 2 v) (padIdx hd 2 u)
              = X (padIdx hd 1 v) (padIdx hd 1 u) -
                (X (padIdx hd 0 v) (padIdx hd 0 u) +
                  X (padIdx hd 1 v) (padIdx hd 1 u) +
                  X (padIdx hd 2 v) (padIdx hd 2 u)) := by abel
            _ = X (padIdx hd 1 v) (padIdx hd 1 u) := by rw [ht, sub_zero]
        · have e2 := hdiag2 v u
          have ht := htrace v u
          rw [e2]
          calc - X (padIdx hd 0 v) (padIdx hd 0 u) - X (padIdx hd 1 v) (padIdx hd 1 u)
              = X (padIdx hd 2 v) (padIdx hd 2 u) -
                (X (padIdx hd 0 v) (padIdx hd 0 u) +
                  X (padIdx hd 1 v) (padIdx hd 1 u) +
                  X (padIdx hd 2 v) (padIdx hd 2 u)) := by abel
            _ = X (padIdx hd 2 v) (padIdx hd 2 u) := by rw [ht, sub_zero]
      · have h := hX (padIdx hd i u) (padIdx hd j v)
        rw [eval_rhs_blk_blk, ite_eq_right hij] at h
        exact h
    · intro r hr u
      have h_r0 := hX r (padIdx hd 0 u)
      rw [eval_rhs_blk_tail 0 u hr] at h_r0
      have h_0r := hX (padIdx hd 0 u) r
      rw [eval_rhs_tail_blk hr 0 u] at h_0r
      have h_1r := hX (padIdx hd 1 u) r
      rw [eval_rhs_tail_blk hr 1 u] at h_1r
      have h_2r := hX (padIdx hd 2 u) r
      rw [eval_rhs_tail_blk hr 2 u] at h_2r
      exact ⟨by simpa using h_r0, by simpa using h_0r,
             by simpa using h_1r, by simpa using h_2r⟩
    · intro r c hr hc
      have h := hX c r
      rwa [eval_rhs_tail_tail hr hc] at h
  · rintro ⟨hsymm, htrace, hcross, htail⟩ c r
    by_cases hr : r.val < 3 * m
    · obtain ⟨i, u, rfl⟩ := exists_eq_padIdx hd hr
      by_cases hc : c.val < 3 * m
      · obtain ⟨j, v, rfl⟩ := exists_eq_padIdx hd hc
        rw [eval_rhs_blk_blk]
        by_cases hij : i = j
        · subst hij
          rcases fin3_eq i with rfl | rfl | rfl
          · simp only [ite_true, Fin.val_zero]
            rw [hsymm 0 0 v u]
            have ht := htrace u v
            calc X (padIdx hd 0 u) (padIdx hd 0 v)
                = (X (padIdx hd 0 u) (padIdx hd 0 v) +
                    X (padIdx hd 1 u) (padIdx hd 1 v) +
                    X (padIdx hd 2 u) (padIdx hd 2 v)) -
                  X (padIdx hd 1 u) (padIdx hd 1 v) -
                  X (padIdx hd 2 u) (padIdx hd 2 v) := by abel
              _ = - X (padIdx hd 1 u) (padIdx hd 1 v) - X (padIdx hd 2 u) (padIdx hd 2 v) := by
                  rw [ht, zero_sub]
          · simp only [ite_true, Fin.val_one, show ¬ (1 : ℕ) = 0 by omega, ite_false]
            rw [hsymm 1 1 v u]
            have ht := htrace u v
            calc X (padIdx hd 1 u) (padIdx hd 1 v)
                = (X (padIdx hd 0 u) (padIdx hd 0 v) +
                    X (padIdx hd 1 u) (padIdx hd 1 v) +
                    X (padIdx hd 2 u) (padIdx hd 2 v)) -
                  X (padIdx hd 0 u) (padIdx hd 0 v) -
                  X (padIdx hd 2 u) (padIdx hd 2 v) := by abel
              _ = - X (padIdx hd 0 u) (padIdx hd 0 v) - X (padIdx hd 2 u) (padIdx hd 2 v) := by
                  rw [ht, zero_sub]
          · simp only [ite_true, Fin.val_two, show ¬ (2 : ℕ) = 0 by omega,
              show ¬ (2 : ℕ) = 1 by omega, ite_false]
            rw [hsymm 2 2 v u]
            have ht := htrace u v
            calc X (padIdx hd 2 u) (padIdx hd 2 v)
                = (X (padIdx hd 0 u) (padIdx hd 0 v) +
                    X (padIdx hd 1 u) (padIdx hd 1 v) +
                    X (padIdx hd 2 u) (padIdx hd 2 v)) -
                  X (padIdx hd 0 u) (padIdx hd 0 v) -
                  X (padIdx hd 1 u) (padIdx hd 1 v) := by abel
              _ = - X (padIdx hd 0 u) (padIdx hd 0 v) - X (padIdx hd 1 u) (padIdx hd 1 v) := by
                  rw [ht, zero_sub]
        · rw [ite_eq_right hij]
          exact hsymm j i v u
      · have hc_ge : 3 * m ≤ c.val := by omega
        rw [eval_rhs_blk_tail i u hc_ge]
        obtain ⟨hc0, _, hc1, hc2⟩ := hcross c hc_ge u
        rcases fin3_eq i with rfl | rfl | rfl
        · simp only [Fin.val_zero, ite_true]
          exact hc0
        · simp only [Fin.val_one, show ¬ (1 : ℕ) = 0 by omega, ite_false, ite_true]
          exact hc2.symm
        · simp only [Fin.val_two, show ¬ (2 : ℕ) = 0 by omega,
            show ¬ (2 : ℕ) = 1 by omega, ite_false]
          calc X c (padIdx hd 2 u)
              = - (- X c (padIdx hd 2 u)) := (neg_neg _).symm
            _ = - X (padIdx hd 1 u) c := by rw [hc1]
    · have hr_ge : 3 * m ≤ r.val := by omega
      by_cases hc : c.val < 3 * m
      · obtain ⟨j, v, rfl⟩ := exists_eq_padIdx hd hc
        rw [eval_rhs_tail_blk hr_ge]
        obtain ⟨_, hr0, hr1, hr2⟩ := hcross r hr_ge v
        rcases fin3_eq j with rfl | rfl | rfl
        · simp only [Fin.val_zero, ite_true]
          exact hr0
        · simp only [Fin.val_one, show ¬ (1 : ℕ) = 0 by omega, ite_false, ite_true]
          exact hr1
        · simp only [Fin.val_two, show ¬ (2 : ℕ) = 0 by omega,
            show ¬ (2 : ℕ) = 1 by omega, ite_false]
          exact hr2
      · have hc_ge : 3 * m ≤ c.val := by omega
        rw [eval_rhs_tail_tail hr_ge hc_ge]
        exact htail r c hr_ge hc_ge

/-- Tail subtype `{r : Fin d // 3 * m ≤ r.val}` and its cardinality `d - 3 * m`. -/
private abbrev PaddedTail (m d : ℕ) := {r : Fin d // 3 * m ≤ r.val}

private lemma card_paddedTail {m d : ℕ} (hd : 3 * m ≤ d) :
    Fintype.card (PaddedTail m d) = d - 3 * m := by
  rw [← Fintype.card_fin (d - 3 * m)]
  refine Fintype.card_congr
    { toFun := fun t => ⟨t.1.val - 3 * m, by have := t.1.isLt; have := t.2; omega⟩
      invFun := fun k => ⟨⟨3 * m + k.val, by have := k.isLt; omega⟩, by simp⟩
      left_inv := fun t => Subtype.ext (Fin.ext (by have := t.2; simp; omega))
      right_inv := fun k => Fin.ext (by simp) }

/-- Free coordinate parameterization of `IsPaddedThreeTermCode m d hd`. -/
private abbrev PaddedCoord (F : Type*) (m d : ℕ) :=
  (Fin 8 × Sym2 (Fin m) → F) ×
  (PaddedTail m d × Fin 2 × Fin m → F) ×
  (Sym2 (PaddedTail m d) → F)

private def blkCoordVal {F : Type*} [Ring F] {m : ℕ}
    (f : Fin 8 × Sym2 (Fin m) → F) (i j : Fin 3) (z : Sym2 (Fin m)) : F :=
  if i.val = 0 ∧ j.val = 1 then f (0, z)
  else if i.val = 1 ∧ j.val = 0 then f (1, z)
  else if i.val = 0 ∧ j.val = 2 then f (2, z)
  else if i.val = 2 ∧ j.val = 0 then f (3, z)
  else if i.val = 1 ∧ j.val = 2 then f (4, z)
  else if i.val = 2 ∧ j.val = 1 then f (5, z)
  else if i.val = 0 ∧ j.val = 0 then f (6, z)
  else if i.val = 1 ∧ j.val = 1 then f (7, z)
  else - (f (6, z) + f (7, z))

private lemma blkCoordVal_add {F : Type*} [Ring F] {m : ℕ}
    (f₁ f₂ : Fin 8 × Sym2 (Fin m) → F) (i j : Fin 3) (z : Sym2 (Fin m)) :
    blkCoordVal (f₁ + f₂) i j z = blkCoordVal f₁ i j z + blkCoordVal f₂ i j z := by
  (rcases fin3_eq i with rfl | rfl | rfl <;> rcases fin3_eq j with rfl | rfl | rfl <;>
    simp [blkCoordVal]); abel

private lemma blkCoordVal_smul {F : Type*} [Ring F] {m : ℕ}
    (a : F) (f : Fin 8 × Sym2 (Fin m) → F) (i j : Fin 3) (z : Sym2 (Fin m)) :
    blkCoordVal (a • f) i j z = a * blkCoordVal f i j z := by
  rcases fin3_eq i with rfl | rfl | rfl <;> rcases fin3_eq j with rfl | rfl | rfl <;>
    simp [blkCoordVal, mul_add]

private def crossColVal {F : Type*} [Ring F] {m d : ℕ}
    (g : PaddedTail m d × Fin 2 × Fin m → F) (i : Fin 3) (cTail : PaddedTail m d) (u : Fin m) : F :=
  if i.val = 0 then 0
  else if i.val = 1 then - g (cTail, 1, u)
  else g (cTail, 0, u)

private lemma crossColVal_add {F : Type*} [Ring F] {m d : ℕ}
    (g₁ g₂ : PaddedTail m d × Fin 2 × Fin m → F) (i : Fin 3) (cTail : PaddedTail m d) (u : Fin m) :
    crossColVal (g₁ + g₂) i cTail u = crossColVal g₁ i cTail u + crossColVal g₂ i cTail u := by
  (rcases fin3_eq i with rfl | rfl | rfl <;> simp [crossColVal]); abel

private lemma crossColVal_smul {F : Type*} [Ring F] {m d : ℕ}
    (a : F) (g : PaddedTail m d × Fin 2 × Fin m → F) (i : Fin 3) (cTail : PaddedTail m d) (u : Fin m) :
    crossColVal (a • g) i cTail u = a * crossColVal g i cTail u := by
  rcases fin3_eq i with rfl | rfl | rfl <;> simp [crossColVal]

private def crossRowVal {F : Type*} [Ring F] {m d : ℕ}
    (g : PaddedTail m d × Fin 2 × Fin m → F) (rTail : PaddedTail m d) (j : Fin 3) (v : Fin m) : F :=
  if j.val = 0 then 0
  else if j.val = 1 then g (rTail, 0, v)
  else g (rTail, 1, v)

private lemma crossRowVal_add {F : Type*} [Ring F] {m d : ℕ}
    (g₁ g₂ : PaddedTail m d × Fin 2 × Fin m → F) (rTail : PaddedTail m d) (j : Fin 3) (v : Fin m) :
    crossRowVal (g₁ + g₂) rTail j v = crossRowVal g₁ rTail j v + crossRowVal g₂ rTail j v := by
  rcases fin3_eq j with rfl | rfl | rfl <;> simp [crossRowVal]

private lemma crossRowVal_smul {F : Type*} [Ring F] {m d : ℕ}
    (a : F) (g : PaddedTail m d × Fin 2 × Fin m → F) (rTail : PaddedTail m d) (j : Fin 3) (v : Fin m) :
    crossRowVal (a • g) rTail j v = a * crossRowVal g rTail j v := by
  rcases fin3_eq j with rfl | rfl | rfl <;> simp [crossRowVal]

private def paddedCoordToMatrix (F : Type*) [Ring F] (m d : ℕ) [NeZero m] :
    PaddedCoord F m d →ₗ[F] Matrix (Fin d) (Fin d) F where
  toFun coord :=
    Matrix.of fun r c =>
      if hr : r.val < 3 * m then
        if hc : c.val < 3 * m then
          blkCoordVal coord.1 (blkOf hr) (blkOf hc) s(offOf r, offOf c)
        else
          crossColVal coord.2.1 (blkOf hr) ⟨c, Nat.le_of_not_lt hc⟩ (offOf r)
      else
        if hc : c.val < 3 * m then
          crossRowVal coord.2.1 ⟨r, Nat.le_of_not_lt hr⟩ (blkOf hc) (offOf c)
        else
          coord.2.2 s(⟨r, Nat.le_of_not_lt hr⟩, ⟨c, Nat.le_of_not_lt hc⟩)
  map_add' x y := by
    ext r c
    simp only [Matrix.of_apply, Matrix.add_apply]
    by_cases hr : r.val < 3 * m <;> by_cases hc : c.val < 3 * m <;>
      simp [hr, hc, blkCoordVal_add, crossColVal_add, crossRowVal_add]
  map_smul' a x := by
    ext r c
    simp only [Matrix.of_apply, Matrix.smul_apply, RingHom.id_apply]
    by_cases hr : r.val < 3 * m <;> by_cases hc : c.val < 3 * m <;>
      simp [hr, hc, blkCoordVal_smul, crossColVal_smul, crossRowVal_smul]

private lemma paddedCoordToMatrix_injective (F : Type*) [Ring F] {m d : ℕ} [NeZero m]
    (hd : 3 * m ≤ d) :
    Function.Injective (paddedCoordToMatrix F m d) := by
  rw [injective_iff_map_eq_zero]
  intro coord h0
  have hEntry : ∀ r c : Fin d, paddedCoordToMatrix F m d coord r c = 0 := fun r c =>
    congrFun (congrFun h0 r) c
  rcases coord with ⟨f_blk, f_cross, f_tail⟩
  apply Prod.ext
  · funext ⟨k, z⟩
    induction z using Sym2.ind with
    | _ u v =>
      have eval_ij : ∀ i j : Fin 3,
          paddedCoordToMatrix F m d (f_blk, f_cross, f_tail) (padIdx hd i u) (padIdx hd j v) = 0 :=
        fun i j => hEntry (padIdx hd i u) (padIdx hd j v)
      rcases fin8_eq k with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · have h := eval_ij 0 1
        simpa [paddedCoordToMatrix, blkCoordVal, padIdx_val_lt, blkOf_padIdx, offOf_padIdx] using h
      · have h := eval_ij 1 0
        simpa [paddedCoordToMatrix, blkCoordVal, padIdx_val_lt, blkOf_padIdx, offOf_padIdx] using h
      · have h := eval_ij 0 2
        simpa [paddedCoordToMatrix, blkCoordVal, padIdx_val_lt, blkOf_padIdx, offOf_padIdx] using h
      · have h := eval_ij 2 0
        simpa [paddedCoordToMatrix, blkCoordVal, padIdx_val_lt, blkOf_padIdx, offOf_padIdx] using h
      · have h := eval_ij 1 2
        simpa [paddedCoordToMatrix, blkCoordVal, padIdx_val_lt, blkOf_padIdx, offOf_padIdx] using h
      · have h := eval_ij 2 1
        simpa [paddedCoordToMatrix, blkCoordVal, padIdx_val_lt, blkOf_padIdx, offOf_padIdx] using h
      · have h := eval_ij 0 0
        simpa [paddedCoordToMatrix, blkCoordVal, padIdx_val_lt, blkOf_padIdx, offOf_padIdx] using h
      · have h := eval_ij 1 1
        simpa [paddedCoordToMatrix, blkCoordVal, padIdx_val_lt, blkOf_padIdx, offOf_padIdx] using h
  · apply Prod.ext
    · funext ⟨rTail, b, v⟩
      have hr_not : ¬ rTail.1.val < 3 * m := Nat.not_lt.mpr rTail.2
      rcases fin2_eq b with rfl | rfl
      · have h := hEntry rTail.1 (padIdx hd 1 v)
        simpa [paddedCoordToMatrix, crossRowVal, hr_not, padIdx_val_lt, blkOf_padIdx, offOf_padIdx]
          using h
      · have h := hEntry rTail.1 (padIdx hd 2 v)
        simpa [paddedCoordToMatrix, crossRowVal, hr_not, padIdx_val_lt, blkOf_padIdx, offOf_padIdx]
          using h
    · funext z
      induction z using Sym2.ind with
      | _ rTail cTail =>
        have hr_not : ¬ rTail.1.val < 3 * m := Nat.not_lt.mpr rTail.2
        have hc_not : ¬ cTail.1.val < 3 * m := Nat.not_lt.mpr cTail.2
        have h := hEntry rTail.1 cTail.1
        simpa [paddedCoordToMatrix, hr_not, hc_not] using h

private lemma range_paddedCoordToMatrix {F : Type*} [Field F] {m d : ℕ} [NeZero m]
    (hd : 3 * m ≤ d) :
    LinearMap.range (paddedCoordToMatrix F m d) =
      SwapRigidity.swapCode (threeTermPaddedA F m d) (threeTermPaddedB F m d) := by
  ext X
  rw [LinearMap.mem_range, mem_swapCode_padded_iff hd]
  constructor
  · rintro ⟨coord, rfl⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i j u v
      simp only [paddedCoordToMatrix, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply,
        padIdx_val_lt, dite_true, blkOf_padIdx, offOf_padIdx, Sym2.eq_swap (a := u) (b := v)]
    · intro u v
      simp [paddedCoordToMatrix, padIdx_val_lt, blkOf_padIdx, offOf_padIdx, blkCoordVal]
    · intro r hr u
      have hr_not : ¬ r.val < 3 * m := by omega
      simp only [paddedCoordToMatrix, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply,
        padIdx_val_lt, hr_not, dite_true, dite_false, blkOf_padIdx, offOf_padIdx,
        crossColVal, crossRowVal]
      simp
    · intro r c hr hc
      have hr_not : ¬ r.val < 3 * m := by omega
      have hc_not : ¬ c.val < 3 * m := by omega
      simp [paddedCoordToMatrix, hr_not, hc_not, Sym2.eq_swap]
  · rintro ⟨hsymm, htrace, hcross, htail⟩
    let blkPair : Fin 8 → Fin 3 × Fin 3
      | ⟨0, _⟩ => (0, 1)
      | ⟨1, _⟩ => (1, 0)
      | ⟨2, _⟩ => (0, 2)
      | ⟨3, _⟩ => (2, 0)
      | ⟨4, _⟩ => (1, 2)
      | ⟨5, _⟩ => (2, 1)
      | ⟨6, _⟩ => (0, 0)
      | ⟨7, _⟩ => (1, 1)
    let f_blk : Fin 8 × Sym2 (Fin m) → F := fun kz =>
      let pq := blkPair kz.1
      Sym2.lift ⟨fun u v => X (padIdx hd pq.1 u) (padIdx hd pq.2 v),
        fun u v => hsymm pq.1 pq.2 u v⟩ kz.2
    let f_cross : PaddedTail m d × Fin 2 × Fin m → F := fun rbv =>
      if rbv.2.1.val = 0 then X rbv.1.1 (padIdx hd 1 rbv.2.2)
      else X rbv.1.1 (padIdx hd 2 rbv.2.2)
    let f_tail : Sym2 (PaddedTail m d) → F :=
      Sym2.lift ⟨fun rTail cTail => X rTail.1 cTail.1,
        fun rTail cTail => (htail rTail.1 cTail.1 rTail.2 cTail.2).symm⟩
    refine ⟨(f_blk, f_cross, f_tail), ?_⟩
    ext r c
    by_cases hr : r.val < 3 * m
    · obtain ⟨i, u, rfl⟩ := exists_eq_padIdx hd hr
      by_cases hc : c.val < 3 * m
      · obtain ⟨j, v, rfl⟩ := exists_eq_padIdx hd hc
        simp only [paddedCoordToMatrix, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply,
          padIdx_val_lt, dite_true, blkOf_padIdx, offOf_padIdx]
        rcases fin3_eq i with rfl | rfl | rfl <;> rcases fin3_eq j with rfl | rfl | rfl
        · simp [blkCoordVal, f_blk, blkPair]
        · simp [blkCoordVal, f_blk, blkPair]
        · simp [blkCoordVal, f_blk, blkPair]
        · simp [blkCoordVal, f_blk, blkPair]
        · simp [blkCoordVal, f_blk, blkPair]
        · simp [blkCoordVal, f_blk, blkPair]
        · simp [blkCoordVal, f_blk, blkPair]
        · simp [blkCoordVal, f_blk, blkPair]
        · have ht := htrace u v
          simp only [blkCoordVal, Fin.val_two, show ¬ (2 : ℕ) = 0 by omega,
            show ¬ (2 : ℕ) = 1 by omega, and_false, false_and, ite_false,
            f_blk, blkPair, Sym2.lift_mk]
          calc - (X (padIdx hd 0 u) (padIdx hd 0 v) + X (padIdx hd 1 u) (padIdx hd 1 v))
              = X (padIdx hd 2 u) (padIdx hd 2 v) -
                (X (padIdx hd 0 u) (padIdx hd 0 v) +
                  X (padIdx hd 1 u) (padIdx hd 1 v) +
                  X (padIdx hd 2 u) (padIdx hd 2 v)) := by abel
            _ = X (padIdx hd 2 u) (padIdx hd 2 v) := by rw [ht, sub_zero]
      · have hc_ge : 3 * m ≤ c.val := by omega
        simp only [paddedCoordToMatrix, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply,
          padIdx_val_lt, hc, dite_true, dite_false, blkOf_padIdx, offOf_padIdx]
        obtain ⟨_, hc0, hc1, hc2⟩ := hcross c hc_ge u
        rcases fin3_eq i with rfl | rfl | rfl
        · simp [crossColVal, hc0]
        · simp [crossColVal, f_cross, hc1]
        · simp [crossColVal, f_cross, hc2]
    · have hr_ge : 3 * m ≤ r.val := by omega
      by_cases hc : c.val < 3 * m
      · obtain ⟨j, v, rfl⟩ := exists_eq_padIdx hd hc
        simp only [paddedCoordToMatrix, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply,
          hr, padIdx_val_lt, dite_true, dite_false, blkOf_padIdx, offOf_padIdx]
        obtain ⟨hr0, _, _, _⟩ := hcross r hr_ge v
        rcases fin3_eq j with rfl | rfl | rfl
        · simp [crossRowVal, hr0]
        · simp [crossRowVal, f_cross]
        · simp [crossRowVal, f_cross]
      · simp [paddedCoordToMatrix, hr, hc, f_tail]

/-- Master dimension formula for `swapCode (threeTermPaddedA F m d) (threeTermPaddedB F m d)`
over **every** field `F` whenever `3 * m ≤ d`. -/
private theorem finrank_swapCode_padded (F : Type*) [Field F] (m d : ℕ) [NeZero m]
    (hd : 3 * m ≤ d) :
    let k := d - 3 * m
    finrank F (SwapRigidity.swapCode (threeTermPaddedA F m d) (threeTermPaddedB F m d)) =
      4 * m * (m + 1) + 2 * m * k + k * (k + 1) / 2 := by
  intro k
  rw [← range_paddedCoordToMatrix hd,
      LinearMap.finrank_range_of_inj (paddedCoordToMatrix_injective F hd),
      Module.finrank_prod, Module.finrank_prod,
      Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
      Module.finrank_fintype_fun_eq_card]
  simp only [Fintype.card_prod, Fintype.card_fin, Sym2.card, card_paddedTail hd]
  have hm_sym : 2 * Nat.choose (m + 1) 2 = m * (m + 1) := by
    rw [Nat.choose_two_right,
        Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self (m + 1)),
        Nat.add_sub_cancel, mul_comm]
  have hm8 : 8 * Nat.choose (m + 1) 2 = 4 * m * (m + 1) := by
    calc 8 * Nat.choose (m + 1) 2
        = 4 * (2 * Nat.choose (m + 1) 2) := by ring
      _ = 4 * (m * (m + 1)) := by rw [hm_sym]
      _ = 4 * m * (m + 1) := by ring
  have hk_sym : Nat.choose (k + 1) 2 = k * (k + 1) / 2 := by
    rw [Nat.choose_two_right, Nat.add_sub_cancel, mul_comm]
  rw [show d - 3 * m = k from rfl, hm8, hk_sym]
  ring

/-- Proof of `Bonus1_ThreeTermBlockSwapCodeDimSpec`. -/
theorem bonus1_ThreeTermBlockSwapCodeDim : Bonus1_ThreeTermBlockSwapCodeDimSpec := by
  constructor
  · intro F _ m _
    obtain ⟨hA, hB⟩ := threeTermPadded_eq_block F m
    rw [← hA, ← hB]
    refine ⟨?_, ?_⟩
    · intro X
      rw [mem_swapCode_padded_iff (le_rfl : 3 * m ≤ 3 * m)]
      have h3m_pos : 0 < 3 * m := Nat.mul_pos (Nat.succ_pos 2) (NeZero.pos m)
      have blk_eq : ∀ (i : Fin 3) (u : Fin m),
          (⟨(i.val * m + u.val) % (3 * m), Nat.mod_lt _ h3m_pos⟩ : Fin (3 * m)) =
            padIdx le_rfl i u := by
        intro i u
        apply Fin.ext
        exact Nat.mod_eq_of_lt (padIdx_val_lt le_rfl i u)
      dsimp only [IsThreeByThreeSymmetricZeroTraceBlocks]
      constructor
      · rintro ⟨hsymm, htrace, _, _⟩
        refine ⟨fun i j u v => ?_, fun u v => ?_⟩
        · simpa only [blk_eq] using hsymm i j u v
        · have h := htrace u v
          rw [← blk_eq 0 u, ← blk_eq 0 v, ← blk_eq 1 u, ← blk_eq 1 v, ← blk_eq 2 u, ← blk_eq 2 v]
            at h
          simpa only [Fin.val_zero, Fin.val_one, Fin.val_two] using h
      · rintro ⟨hsymm, htrace⟩
        refine ⟨fun i j u v => ?_, fun u v => ?_, fun r hr => ?_, fun r _ hr _ => ?_⟩
        · simpa only [blk_eq] using hsymm i j u v
        · have h0 := blk_eq 0 u
          have h0' := blk_eq 0 v
          have h1 := blk_eq 1 u
          have h1' := blk_eq 1 v
          have h2 := blk_eq 2 u
          have h2' := blk_eq 2 v
          simp only [Fin.val_zero, Fin.val_one, Fin.val_two] at h0 h0' h1 h1' h2 h2'
          have h := htrace u v
          rwa [h0, h0', h1, h1', h2, h2'] at h
        · exact absurd r.isLt (Nat.not_lt.mpr hr)
        · exact absurd r.isLt (Nat.not_lt.mpr hr)
    · have hdim := finrank_swapCode_padded F m (3 * m) le_rfl
      simpa using hdim
  · intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl | rfl <;> omega

/-- Proof of `Bonus1_ThreeTermPaddedSevenAndFiveSpec`. -/
theorem bonus1_ThreeTermPaddedSevenAndFive : Bonus1_ThreeTermPaddedSevenAndFiveSpec := by
  intro F _
  refine ⟨?_, ?_, ?_⟩
  · have h := finrank_swapCode_padded F 2 7 (by omega)
    simpa using h
  · have h := finrank_swapCode_padded F 1 4 (by omega)
    simpa using h
  · have h := finrank_swapCode_padded F 1 5 (by omega)
    simpa using h

end Bonus1Proofs

/-! ### 2. Bonus 2: Multi-Scale Cyclic Intervals on Both Sides (`Problem 9.3`) -/

section Bonus2Proofs

private def zmodToFin {d : ℕ} [NeZero d] (x : ZMod d) : Fin d :=
  ⟨x.val, x.val_lt⟩

private def finToZMod {d : ℕ} (r : Fin d) : ZMod d :=
  (r.val : ZMod d)

private lemma zmodToFin_finToZMod {d : ℕ} [NeZero d] (r : Fin d) :
    zmodToFin (finToZMod r) = r :=
  Fin.ext (ZMod.val_cast_of_lt r.isLt)

private lemma finToZMod_zmodToFin {d : ℕ} [NeZero d] (x : ZMod d) :
    finToZMod (zmodToFin x) = x :=
  ZMod.natCast_zmod_val x

private def zmodEquivFin (d : ℕ) [NeZero d] : ZMod d ≃ Fin d where
  toFun := zmodToFin
  invFun := finToZMod
  left_inv := finToZMod_zmodToFin
  right_inv := zmodToFin_finToZMod

private lemma zmodToFin_add_val {d : ℕ} [NeZero d] (x y : ZMod d) :
    (zmodToFin (x + y)).val = ((zmodToFin x).val + (zmodToFin y).val) % d :=
  ZMod.val_add x y

/-- A single cyclic interval `I` on `Fin d` changes membership across `c - 1 → c` at most at two
cyclic boundary points `{start, start + len}` in `ZMod d`. -/
private lemma exists_boundary_pair_of_isCyclicInterval {d : ℕ} [NeZero d]
    {len : ℕ} {I : Finset (Fin d)} (hI : IsCyclicInterval len I) :
    ∃ B : Finset (ZMod d),
      B.card ≤ 2 ∧
      ∀ c : ZMod d, c ∉ B → (zmodToFin (c - 1) ∈ I ↔ zmodToFin c ∈ I) := by
  classical
  obtain ⟨start, rfl⟩ := hI
  let a : ZMod d := finToZMod start
  have ha_val : a.val = start.val := ZMod.val_cast_of_lt start.isLt
  by_cases hlen0 : len = 0
  · subst hlen0
    exact ⟨∅, by simp, fun _ _ => by simp⟩
  · by_cases hd_le : d ≤ len
    · have huniv : ∀ x : ZMod d,
          zmodToFin x ∈ (Finset.range len).image
            (fun u => (⟨(start.val + u) % d, Nat.mod_lt _ (NeZero.pos d)⟩ : Fin d)) := by
        intro x
        rw [Finset.mem_image]
        refine ⟨(x - a).val, Finset.mem_range.mpr (lt_of_lt_of_le (ZMod.val_lt _) hd_le), ?_⟩
        apply Fin.ext
        show (start.val + (x - a).val) % d = x.val
        have hval := congrArg ZMod.val (add_sub_cancel a x)
        rwa [ZMod.val_add, ha_val] at hval
      exact ⟨∅, by simp, fun c _ => by simp [huniv]⟩
    · have hlen_lt : len < d := Nat.lt_of_not_ge hd_le
      have mem_iff : ∀ x : ZMod d,
          zmodToFin x ∈ (Finset.range len).image
            (fun u => (⟨(start.val + u) % d, Nat.mod_lt _ (NeZero.pos d)⟩ : Fin d)) ↔
            (x - a).val < len := by
        intro x
        rw [Finset.mem_image]
        constructor
        · rintro ⟨u, hu, hEq⟩
          have hu_lt : u < len := Finset.mem_range.mp hu
          have hval : (start.val + u) % d = x.val := congrArg Fin.val hEq
          have hcast : a + (u : ZMod d) = x := by
            calc a + (u : ZMod d) = ((start.val + u : ℕ) : ZMod d) := by
                  simp [a, finToZMod, Nat.cast_add]
              _ = (((start.val + u) % d : ℕ) : ZMod d) := (ZMod.natCast_mod _ _).symm
              _ = (x.val : ZMod d) := by rw [hval]
              _ = x := ZMod.natCast_zmod_val x
          have hsub : x - a = (u : ZMod d) := by
            rw [← hcast, add_sub_cancel_left]
          rw [hsub, ZMod.val_cast_of_lt (lt_trans hu_lt hlen_lt)]
          exact hu_lt
        · intro hx_lt
          refine ⟨(x - a).val, Finset.mem_range.mpr hx_lt, ?_⟩
          apply Fin.ext
          show (start.val + (x - a).val) % d = x.val
          have hval := congrArg ZMod.val (add_sub_cancel a x)
          rwa [ZMod.val_add, ha_val] at hval
      refine ⟨{a, a + (len : ZMod d)}, Finset.card_le_two, ?_⟩
      intro c hc
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
      obtain ⟨hca, hcb⟩ := hc
      rw [mem_iff, mem_iff]
      have hne0 : c - a ≠ 0 := sub_ne_zero.mpr hca
      have hpos : 1 ≤ (c - a).val := by
        rcases Nat.eq_zero_or_pos (c - a).val with h0 | hpos
        · exact absurd ((ZMod.val_eq_zero _).mp h0) hne0
        · exact hpos
      have hprev_val : (c - 1 - a).val = (c - a).val - 1 := by
        have e1 : c - 1 - a = ((c - a).val - 1 : ℕ) := by
          rw [Nat.cast_sub hpos, ZMod.natCast_zmod_val, Nat.cast_one]
          abel
        rw [e1]
        exact ZMod.val_cast_of_lt (lt_of_le_of_lt (Nat.sub_le _ _) (ZMod.val_lt _))
      have hne_len : (c - a).val ≠ len := by
        intro hEq
        apply hcb
        calc c = a + ((c - a).val : ZMod d) := by
              rw [ZMod.natCast_zmod_val, add_sub_cancel]
          _ = a + (len : ZMod d) := by rw [hEq]
      rw [hprev_val]
      omega

/-- One-sided class-uniform swap-code bound for a multi-scale cyclic-interval family `A`
against an **arbitrary** matrix family `B`. -/
private theorem one_sided_multiscale_interval_bound
    {F : Type*} [Field F] {m : ℕ} {α : Type*} [Fintype α]
    (M_A : Fin m → ℕ)
    (A B : α → Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) F)
    (hA : InMultiscaleIntervalRotSpan M_A A) :
    2 * finrank F (SwapRigidity.swapCode A B) ≤
      (2 ^ m) ^ 2 + (2 ^ m) * max 1 (2 * ∑ j : Fin m, M_A j) := by
  classical
  let d := 2 ^ m
  have : NeZero d := ⟨(Nat.two_pow_pos m).ne'⟩
  obtain ⟨intervals, hIntervals, hSpan⟩ := hA
  let κ := ∀ j : Fin m, Fin (M_A j) → Bool
  let cls : ZMod d → κ := fun r j i => decide (zmodToFin r ∈ intervals j i)
  -- Subspace of matrices whose row entries in shift coordinates depend only on `cls r`.
  let PSub : Submodule F (Matrix (Fin d) (Fin d) F) :=
    { carrier := {M | ∀ r₁ r₂ s : ZMod d, cls r₁ = cls r₂ →
        M (zmodToFin r₁) (zmodToFin (r₁ + s)) = M (zmodToFin r₂) (zmodToFin (r₂ + s))}
      add_mem' := fun {M₁ M₂} h₁ h₂ r₁ r₂ s hcls => by
        simp [h₁ r₁ r₂ s hcls, h₂ r₁ r₂ s hcls]
      zero_mem' := fun _ _ _ _ => rfl
      smul_mem' := fun c {M} hM r₁ r₂ s hcls => by
        simp [hM r₁ r₂ s hcls] }
  have shift_cond_eq : ∀ (r s : ZMod d) (s₀ : Fin d),
      ((zmodToFin (r + s)).val = ((zmodToFin r).val + s₀.val) % (2 ^ m)) ↔
        s = finToZMod s₀ := by
    intro r s s₀
    change ((zmodToFin (r + s)).val = ((zmodToFin r).val + s₀.val) % d) ↔ s = finToZMod s₀
    rw [zmodToFin_add_val]
    constructor
    · intro hmod
      have hcast : (((zmodToFin r).val + (zmodToFin s).val : ℕ) : ZMod d) =
          (((zmodToFin r).val + s₀.val : ℕ) : ZMod d) := by
        rw [← ZMod.natCast_mod, hmod, ZMod.natCast_mod]
      simp only [Nat.cast_add] at hcast
      have hr_cast : (((zmodToFin r).val : ℕ) : ZMod d) = r := ZMod.natCast_zmod_val r
      have hs_cast : (((zmodToFin s).val : ℕ) : ZMod d) = s := ZMod.natCast_zmod_val s
      rw [hr_cast, hs_cast] at hcast
      exact add_left_cancel hcast
    · rintro rfl
      rw [zmodToFin_finToZMod]
  have hSpanLe : Submodule.span F
      ({X | ∃ s : Fin d, X = intervalMaskRotMatrix F Finset.univ s} ∪
       {X | ∃ (j : Fin m) (i : Fin (M_A j)) (s : Fin d),
              X = intervalMaskRotMatrix F (intervals j i) s}) ≤ PSub := by
    rw [Submodule.span_le]
    rintro M (⟨s₀, rfl⟩ | ⟨j, i, s₀, rfl⟩) r₁ r₂ s hcls
    · dsimp only [intervalMaskRotMatrix, d]
      simp [shift_cond_eq]
    · have hmem_eq : (zmodToFin r₁ ∈ intervals j i) ↔ (zmodToFin r₂ ∈ intervals j i) := by
        have h := congrFun (congrFun hcls j) i
        simpa [cls] using h
      simp [intervalMaskRotMatrix, shift_cond_eq, hmem_eq]
  have hA_cls : ∀ a : α, A a ∈ PSub := fun a => hSpanLe (hSpan a)
  let coeffA : α → κ → ZMod d → F := fun a k s =>
    if h : ∃ r₀ : ZMod d, cls r₀ = k then
      A a (zmodToFin (Classical.choose h)) (zmodToFin (Classical.choose h + s))
    else 0
  have hcoeffA : ∀ (a : α) (r s : ZMod d),
      A a (zmodToFin r) (zmodToFin (r + s)) = coeffA a (cls r) s := by
    intro a r s
    have hex : ∃ r₀ : ZMod d, cls r₀ = cls r := ⟨r, rfl⟩
    simp only [coeffA, dite_eq_left hex]
    exact hA_cls a r (Classical.choose hex) s (Classical.choose_spec hex).symm
  -- Transfer `swapCode A B` to `Matrix (ZMod d) (ZMod d) F` via `X ↦ Xᵀ` composed with `zmodToFin`.
  let toTransZMod : Matrix (Fin d) (Fin d) F ≃ₗ[F] Matrix (ZMod d) (ZMod d) F :=
    { toFun := fun X => Matrix.of fun r c => X (zmodToFin c) (zmodToFin r)
      invFun := fun Y => Matrix.of fun r c => Y (finToZMod c) (finToZMod r)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun X => by ext r c; simp [zmodToFin_finToZMod]
      right_inv := fun Y => by ext r c; simp [finToZMod_zmodToFin] }
  let 𝒳 : Submodule F (Matrix (ZMod d) (ZMod d) F) :=
    (SwapRigidity.swapCode A B).map toTransZMod.toLinearMap
  have hClassUnif : SwapRigidity.IsClassUniformCode cls 𝒳 := by
    let dec : κ → (Matrix (ZMod d) (ZMod d) F →ₗ[F] (ZMod d → F)) := fun k =>
      { toFun := fun Z c =>
          ∑ a : α, ∑ s : ZMod d, ∑ c' : ZMod d,
            coeffA a k s * Z c' s * B a (zmodToFin c) (zmodToFin c')
        map_add' := fun Z₁ Z₂ => by
          funext c
          simp only [Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib, Pi.add_apply]
        map_smul' := fun x Z => by
          funext c
          simp only [Matrix.smul_apply, smul_eq_mul, RingHom.id_apply, Pi.smul_apply,
            Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ =>
            Finset.sum_congr rfl fun s _ =>
              Finset.sum_congr rfl fun c' _ => by ring }
    refine ⟨dec, ?_⟩
    rintro _ ⟨X, hX, rfl⟩ r
    funext c
    have hEntry := (SwapRigidity.mem_swapCode_iff_apply.mp hX) (zmodToFin c) (zmodToFin r)
    show X (zmodToFin c) (zmodToFin r) =
      ∑ a : α, ∑ s : ZMod d, ∑ c' : ZMod d,
        coeffA a (cls r) s * X (zmodToFin (s + r)) (zmodToFin c') *
          B a (zmodToFin c) (zmodToFin c')
    rw [hEntry]
    refine Finset.sum_congr rfl fun a _ => ?_
    let shiftEquiv : ZMod d ≃ Fin d := (Equiv.addRight r).trans (zmodEquivFin d)
    rw [← shiftEquiv.sum_comp (fun a' : Fin d =>
          ∑ b' : Fin d, A a (zmodToFin r) a' * X a' b' * B a (zmodToFin c) b')]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← (zmodEquivFin d).sum_comp (fun b' : Fin d =>
          A a (zmodToFin r) (shiftEquiv s) * X (shiftEquiv s) b' * B a (zmodToFin c) b')]
    refine Finset.sum_congr rfl fun c' _ => ?_
    have hs' : shiftEquiv s = zmodToFin (s + r) := rfl
    rw [hs', show zmodEquivFin d c' = zmodToFin c' from rfl]
    congr 2
    rw [add_comm s r, hcoeffA a r s]
  -- Assemble boundary set `B_all` of cardinality at most `2 * ∑ j, M_A j`.
  let pairIdx := Σ j : Fin m, Fin (M_A j)
  have hbnd : ∀ p : pairIdx, ∃ B_p : Finset (ZMod d),
      B_p.card ≤ 2 ∧
      ∀ c : ZMod d, c ∉ B_p →
        (zmodToFin (c - 1) ∈ intervals p.1 p.2 ↔ zmodToFin c ∈ intervals p.1 p.2) :=
    fun p => exists_boundary_pair_of_isCyclicInterval (hIntervals p.1 p.2)
  let B_of : pairIdx → Finset (ZMod d) := fun p => Classical.choose (hbnd p)
  have hB_card : ∀ p : pairIdx, (B_of p).card ≤ 2 :=
    fun p => (Classical.choose_spec (hbnd p)).1
  have hB_mem : ∀ (p : pairIdx) (c : ZMod d), c ∉ B_of p →
      (zmodToFin (c - 1) ∈ intervals p.1 p.2 ↔ zmodToFin c ∈ intervals p.1 p.2) :=
    fun p => (Classical.choose_spec (hbnd p)).2
  let B_all : Finset (ZMod d) := Finset.univ.biUnion B_of
  have hB_all_card : B_all.card ≤ 2 * ∑ j : Fin m, M_A j := by
    calc B_all.card
        ≤ ∑ p : pairIdx, (B_of p).card := Finset.card_biUnion_le
      _ ≤ ∑ _p : pairIdx, 2 := Finset.sum_le_sum fun p _ => hB_card p
      _ = Fintype.card pairIdx * 2 := by simp
      _ = (∑ j : Fin m, M_A j) * 2 := by simp [pairIdx, Fintype.card_sigma]
      _ = 2 * ∑ j : Fin m, M_A j := by ring
  let S : Finset (ZMod d) := if B_all.Nonempty then B_all else {0}
  have hS_nonempty : S.Nonempty := by
    by_cases hne : B_all.Nonempty
    · simp [S, hne]
    · simp [S, hne]
  have hS_cls : ∀ c ∉ S, cls (c - 1) = cls c := by
    intro c hcS
    have hcB : c ∉ B_all := by
      by_cases hne : B_all.Nonempty
      · simpa [S, hne] using hcS
      · rw [Finset.not_nonempty_iff_eq_empty] at hne
        simp [hne]
    funext j i
    have hp : (⟨j, i⟩ : pairIdx) ∈ (Finset.univ : Finset pairIdx) := Finset.mem_univ _
    have hc_not_p : c ∉ B_of ⟨j, i⟩ := fun h => hcB (Finset.mem_biUnion.mpr ⟨⟨j, i⟩, hp, h⟩)
    simp [cls, hB_mem ⟨j, i⟩ c hc_not_p]
  have hS_card : S.card ≤ max 1 (2 * ∑ j : Fin m, M_A j) := by
    by_cases hne : B_all.Nonempty
    · simp only [S, ite_eq_left hne]
      exact le_trans hB_all_card (le_max_right _ _)
    · simp only [S, ite_eq_right hne, Finset.card_singleton]
      exact le_max_left _ _
  have hMain := hClassUnif.two_mul_finrank_le hS_nonempty hS_cls
  have hFinrankEq : finrank F 𝒳 = finrank F (SwapRigidity.swapCode A B) :=
    LinearEquiv.finrank_map_eq toTransZMod (SwapRigidity.swapCode A B)
  rw [hFinrankEq] at hMain
  calc 2 * finrank F (SwapRigidity.swapCode A B)
      ≤ d ^ 2 + d * S.card := hMain
    _ ≤ d ^ 2 + d * max 1 (2 * ∑ j : Fin m, M_A j) :=
        Nat.add_le_add_left (Nat.mul_le_mul_left d hS_card) _

/-- Proof of `Bonus2_MultiscaleIntervalBothSidesSpec`. -/
theorem bonus2_MultiscaleIntervalBothSides : Bonus2_MultiscaleIntervalBothSidesSpec := by
  intro F _ m α _ M_A M_B A B
  constructor
  · rintro ⟨intervals, hAligned, hSpan⟩
    refine ⟨intervals, ?_, hSpan⟩
    intro j i
    obtain ⟨blk, hI⟩ := hAligned j i
    let len := 2 ^ (m - 1 - j.val)
    refine ⟨⟨(blk.val * len) % (2 ^ m), Nat.mod_lt _ (Nat.two_pow_pos m)⟩, ?_⟩
    rw [hI]
    ext r
    simp only [Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u, hu, Fin.ext (by simp [len, Nat.mod_add_mod])⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u, hu, Fin.ext (by simp [len, Nat.mod_add_mod])⟩
  · intro hA hB
    have hBoundA := one_sided_multiscale_interval_bound M_A A B hA
    have hBoundB := one_sided_multiscale_interval_bound M_B B A hB
    rw [← SwapRigidity.finrank_swapCode_swap A B] at hBoundB
    rcases le_total
        (max 1 (2 * ∑ j : Fin m, M_A j))
        (max 1 (2 * ∑ j : Fin m, M_B j)) with hle | hle
    · rw [min_eq_left hle]
      exact hBoundA
    · rw [min_eq_right hle]
      exact hBoundB

/-! ### 3. Bonus 2B: Full Aligned Dyadic Profile Attains Full Swap `(2^m)^2` -/

/-- Proof of `Bonus2_MultiscaleFullProfileAttainsFullSwapSpec`. -/
theorem bonus2_MultiscaleFullProfileAttainsFullSwap :
    Bonus2_MultiscaleFullProfileAttainsFullSwapSpec := by
  intro F _ m
  let fullProfile : Fin m → ℕ := fun j => 2 ^ (j.val + 1)
  constructor
  · intro hm
    let j₀ : Fin m := ⟨m - 1, by omega⟩
    have hj₀ : fullProfile j₀ = 2 ^ m := by
      show 2 ^ ((m - 1) + 1) = 2 ^ m
      congr 1
      omega
    rw [← hj₀]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j₀)
  · cases m with
    | zero =>
      have : NeZero (2 ^ 0) := ⟨by decide⟩
      let A : Unit → Matrix (Fin (2 ^ 0)) (Fin (2 ^ 0)) F :=
        fun _ => intervalMaskRotMatrix F Finset.univ 0
      refine ⟨Unit, inferInstance, A, A, ?_, ?_, ?_⟩
      · refine ⟨fun j => Fin.elim0 j, fun j => Fin.elim0 j, fun _ => ?_⟩
        exact Submodule.subset_span (Set.mem_union_left _ ⟨0, rfl⟩)
      · refine ⟨fun j => Fin.elim0 j, fun j => Fin.elim0 j, fun _ => ?_⟩
        exact Submodule.subset_span (Set.mem_union_left _ ⟨0, rfl⟩)
      · have hTop : SwapRigidity.swapCode A A = ⊤ := by
          rw [eq_top_iff]
          intro X _
          rw [SwapRigidity.mem_swapCode_iff_apply]
          intro b a
          have hb0 : b = 0 := Fin.ext (by have := b.isLt; omega)
          have ha0 : a = 0 := Fin.ext (by have := a.isLt; omega)
          subst hb0 ha0
          simp [A, intervalMaskRotMatrix]
        rw [hTop, finrank_top, Module.finrank_matrix, Fintype.card_fin, finrank_self]
        simp
    | succ m' =>
      let d := 2 ^ (m' + 1)
      have hd_pos : 0 < d := Nat.two_pow_pos (m' + 1)
      have : NeZero d := ⟨hd_pos.ne'⟩
      let intervals : ∀ j : Fin (m' + 1), Fin (fullProfile j) → Finset (Fin d) :=
        fun j blk =>
          let len := 2 ^ (m' + 1 - 1 - j.val)
          (Finset.range len).image fun u =>
            ⟨(blk.val * len + u) % d, Nat.mod_lt _ hd_pos⟩
      have hAligned : ∀ (j : Fin (m' + 1)) (blk : Fin (fullProfile j)),
          IsAlignedDyadicInterval j (intervals j blk) :=
        fun j blk => ⟨blk, rfl⟩
      let jLast : Fin (m' + 1) := Fin.last m'
      have hSingleton : ∀ r₀ : Fin d, intervals jLast r₀ = {r₀} := by
        intro r₀
        have hlen1 : 2 ^ (m' + 1 - 1 - jLast.val) = 1 := by
          show 2 ^ (m' + 1 - 1 - m') = 1
          simp
        ext r
        simp only [intervals, hlen1, Finset.range_one, Finset.image_singleton,
          Finset.mem_singleton]
        constructor
        · rintro rfl
          apply Fin.ext
          show ((r₀.val * 1 + 0) % d) = r₀.val
          rw [mul_one, add_zero, Nat.mod_eq_of_lt r₀.isLt]
        · intro hEq
          rw [hEq]
          apply Fin.ext
          show r₀.val = (r₀.val * 1 + 0) % d
          rw [mul_one, add_zero, Nat.mod_eq_of_lt r₀.isLt]
      let shiftBetween (r₀ c₀ : Fin d) : Fin d :=
        ⟨(d + c₀.val - r₀.val) % d, Nat.mod_lt _ hd_pos⟩
      have hShiftMod : ∀ r₀ c₀ : Fin d,
          (r₀.val + (shiftBetween r₀ c₀).val) % d = c₀.val := by
        intro r₀ c₀
        show (r₀.val + (d + c₀.val - r₀.val) % d) % d = c₀.val
        rw [Nat.add_mod_mod]
        have e : r₀.val + (d + c₀.val - r₀.val) = c₀.val + 1 * d := by
          have := r₀.isLt
          omega
        rw [e, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt c₀.isLt]
      let unitMat (r₀ c₀ : Fin d) : Matrix (Fin d) (Fin d) F :=
        intervalMaskRotMatrix F {r₀} (shiftBetween r₀ c₀)
      have hUnitApply : ∀ r₀ c₀ r c : Fin d,
          unitMat r₀ c₀ r c = if r = r₀ ∧ c = c₀ then 1 else 0 := by
        intro r₀ c₀ r c
        simp only [unitMat, intervalMaskRotMatrix, Matrix.of_apply, Finset.mem_singleton]
        by_cases hr : r = r₀
        · subst hr
          rw [hShiftMod r c₀]
          by_cases hc : c = c₀
          · subst hc
            simp
          · have hval : c.val ≠ c₀.val := fun h => hc (Fin.ext h)
            simp [hc, hval]
        · simp [hr]
      let A : Fin d × Fin d → Matrix (Fin d) (Fin d) F := fun p => unitMat p.1 p.2
      let B : Fin d × Fin d → Matrix (Fin d) (Fin d) F := fun p => unitMat p.2 p.1
      have hInSpan : ∀ M : Fin d × Fin d → Matrix (Fin d) (Fin d) F,
          (∀ p, ∃ r₀ c₀ : Fin d, M p = unitMat r₀ c₀) →
          InAlignedDyadicIntervalRotSpan fullProfile M := by
        intro M hM
        refine ⟨intervals, hAligned, fun p => ?_⟩
        obtain ⟨r₀, c₀, hp⟩ := hM p
        rw [hp]
        refine Submodule.subset_span (Set.mem_union_right _ ?_)
        refine ⟨jLast, r₀, shiftBetween r₀ c₀, ?_⟩
        dsimp only [unitMat]
        rw [← hSingleton r₀]
      refine ⟨Fin d × Fin d, inferInstance, A, B,
        hInSpan A (fun p => ⟨p.1, p.2, rfl⟩),
        hInSpan B (fun p => ⟨p.2, p.1, rfl⟩), ?_⟩
      have hTop : SwapRigidity.swapCode A B = ⊤ := by
        rw [eq_top_iff]
        intro X _
        rw [SwapRigidity.mem_swapCode_iff_apply]
        intro b a
        rw [Fintype.sum_prod_type]
        rw [Finset.sum_eq_single a]
        · rw [Finset.sum_eq_single b]
          · rw [Finset.sum_eq_single b]
            · rw [Finset.sum_eq_single a]
              · simp [A, B, hUnitApply]
              · intro b' _ hb'
                simp [B, hUnitApply, hb']
              · intro h
                exact absurd (Finset.mem_univ a) h
            · intro a' _ ha'
              refine Finset.sum_eq_zero fun b' _ => ?_
              simp [A, hUnitApply, ha']
            · intro h
              exact absurd (Finset.mem_univ b) h
          · intro c₀ _ hc₀
            refine Finset.sum_eq_zero fun a' _ => Finset.sum_eq_zero fun b' _ => ?_
            simp [B, hUnitApply, hc₀.symm]
          · intro h
            exact absurd (Finset.mem_univ b) h
        · intro r₀ _ hr₀
          refine Finset.sum_eq_zero fun c₀ _ =>
            Finset.sum_eq_zero fun a' _ =>
              Finset.sum_eq_zero fun b' _ => ?_
          simp [A, hUnitApply, hr₀.symm]
        · intro h
          exact absurd (Finset.mem_univ a) h
      rw [hTop, finrank_top, Module.finrank_matrix, Fintype.card_fin, finrank_self, mul_one, ← sq]

/-! ### 4. Walsh-to-Periodic-Profile Bridge Lemmas -/

private lemma walsh_bit_false_iff_mod {h x : ℕ} (hh : 0 < h) :
    (((x / h) % 2 == 1) = false) ↔ x % (2 * h) < h := by
  set q := x / h
  set rem := x % h
  have hrem : rem < h := Nat.mod_lt x hh
  have hx_eq : x = q * h + rem := (Nat.div_add_mod' x h).symm
  rcases Nat.mod_two_eq_zero_or_one q with hq0 | hq1
  · have hq_even : q = 2 * (q / 2) := by omega
    have hx_mod : x % (2 * h) = rem := by
      have e : x = rem + (q / 2) * (2 * h) := by
        calc x = (2 * (q / 2)) * h + rem := by rw [hx_eq, ← hq_even]
          _ = rem + (q / 2) * (2 * h) := by ring
      rw [e, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    simp [hq0, hx_mod, hrem]
  · have hq_odd : q = 2 * (q / 2) + 1 := by omega
    have hx_mod : x % (2 * h) = h + rem := by
      have e : x = (h + rem) + (q / 2) * (2 * h) := by
        calc x = (2 * (q / 2) + 1) * h + rem := by rw [hx_eq, ← hq_odd]
          _ = (h + rem) + (q / 2) * (2 * h) := by ring
      rw [e, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    simp [hq1, hx_mod, show ¬ h + rem < h by omega]

private lemma walsh_bit_true_iff_mod {h x : ℕ} (hh : 0 < h) :
    (((x / h) % 2 == 1) = true) ↔ (x + h) % (2 * h) < h := by
  set q := x / h
  set rem := x % h
  have hrem : rem < h := Nat.mod_lt x hh
  have hx_eq : x = q * h + rem := (Nat.div_add_mod' x h).symm
  rcases Nat.mod_two_eq_zero_or_one q with hq0 | hq1
  · have hq_even : q = 2 * (q / 2) := by omega
    have hx_mod : (x + h) % (2 * h) = h + rem := by
      have e : x + h = (h + rem) + (q / 2) * (2 * h) := by
        calc x + h = (2 * (q / 2)) * h + rem + h := by rw [hx_eq, ← hq_even]
          _ = (h + rem) + (q / 2) * (2 * h) := by ring
      rw [e, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    simp [hq0, hx_mod, show ¬ h + rem < h by omega]
  · have hq_odd : q = 2 * (q / 2) + 1 := by omega
    have hx_mod : (x + h) % (2 * h) = rem := by
      have e : x + h = rem + (q / 2 + 1) * (2 * h) := by
        calc x + h = (2 * (q / 2) + 1) * h + rem + h := by rw [hx_eq, ← hq_odd]
          _ = rem + (q / 2 + 1) * (2 * h) := by ring
      rw [e, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    simp [hq1, hx_mod, hrem]

/-- Every family in the span of `walshDigitMaskRotMatrix` lies in
`InMultiscalePeriodicDyadicRotSpan (fun _ => 2)`. -/
theorem walshDigitMask_in_periodicDyadicSpan
    (F : Type*) [Field F] {m : ℕ} {α : Type*}
    (M : α → Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) F)
    (hM : ∀ a, M a ∈ Submodule.span F
      {X | ∃ (j : Fin m) (bit : Bool) (sh : Fin (2 ^ m)),
            X = walshDigitMaskRotMatrix F j bit sh}) :
    InMultiscalePeriodicDyadicRotSpan (fun _ : Fin m => 2) M := by
  have : NeZero (2 ^ m) := ⟨(Nat.two_pow_pos m).ne'⟩
  let masks : ∀ j : Fin m, Fin 2 → Finset (Fin (2 ^ m)) := fun j i =>
    let halfPeriod := 2 ^ (m - 1 - j.val)
    Finset.univ.filter fun r : Fin (2 ^ m) =>
      ((r.val / halfPeriod) % 2 == 1) = (i.val == 1)
  refine ⟨masks, ?_, ?_⟩
  · intro j i
    let halfPeriod := 2 ^ (m - 1 - j.val)
    have hhalf_pos : 0 < halfPeriod := Nat.two_pow_pos _
    have hperiod_eq : 2 ^ (m - j.val) = 2 * halfPeriod := by
      have hexp : m - j.val = (m - 1 - j.val) + 1 := by
        have := j.isLt
        omega
      rw [hexp, pow_succ']
    rcases fin2_eq i with rfl | rfl
    · refine ⟨⟨0, Nat.two_pow_pos m⟩, ?_⟩
      intro r
      simp only [masks, Finset.mem_filter, Finset.mem_univ, true_and, hperiod_eq]
      simpa [halfPeriod] using walsh_bit_false_iff_mod hhalf_pos (x := r.val)
    · have hhalf_lt : halfPeriod < 2 ^ m :=
        Nat.pow_lt_pow_right (by omega : 1 < 2) (by have := j.isLt; omega)
      refine ⟨⟨halfPeriod, hhalf_lt⟩, ?_⟩
      intro r
      simp only [masks, Finset.mem_filter, Finset.mem_univ, true_and, hperiod_eq]
      simpa [halfPeriod] using walsh_bit_true_iff_mod hhalf_pos (x := r.val)
  · intro a
    refine Submodule.span_mono ?_ (hM a)
    rintro X ⟨j, bit, sh, rfl⟩
    refine Set.mem_union_right _ ?_
    cases bit
    · refine ⟨j, 0, sh, ?_⟩
      ext r c
      simp [walshDigitMaskRotMatrix, intervalMaskRotMatrix, masks]
    · refine ⟨j, 1, sh, ?_⟩
      ext r c
      simp [walshDigitMaskRotMatrix, intervalMaskRotMatrix, masks]

private lemma sq_le_two_pow {n : ℕ} (hn : 4 ≤ n) : n * n ≤ 2 ^ n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  clear hn
  induction k with
  | zero => decide
  | succ k ih =>
    have hstep : 2 * (4 + k) + 1 ≤ (4 + k) * (4 + k) := by nlinarith
    calc (4 + (k + 1)) * (4 + (k + 1))
        = (4 + k) * (4 + k) + (2 * (4 + k) + 1) := by ring
      _ ≤ (4 + k) * (4 + k) + (4 + k) * (4 + k) := Nat.add_le_add_left hstep _
      _ = 2 * ((4 + k) * (4 + k)) := by ring
      _ ≤ 2 * 2 ^ (4 + k) := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (4 + (k + 1)) := by ring

/-- Sublinear periodic dyadic mask rigidity (`OpenTarget_MultiscalePeriodicWalshProfileSpec`)
implies the all-scale Walsh swap-code bound (`OpenTarget_MultiscalePeriodicWalshSwapCodeSpec`),
since `2 m ≤ δ * 2^m` for all sufficiently large `m` whenever `δ > 0`. -/
theorem openTarget_walsh_of_periodicProfile.{u, v} :
    OpenTarget_MultiscalePeriodicWalshProfileSpec.{u, v} →
      OpenTarget_MultiscalePeriodicWalshSwapCodeSpec.{u, v} := by
  rintro ⟨c_walsh, δ, M₀, hc, hδ, hProfile⟩
  obtain ⟨K, hK⟩ := exists_nat_gt (2 / δ)
  let M₁ := max M₀ (max 4 K)
  refine ⟨c_walsh, M₁, hc, ?_⟩
  intro F _ m α _ A B hm hA hB
  have hm₀ : M₀ ≤ m := le_trans (le_max_left _ _) hm
  have hm_ge_max : max 4 K ≤ m := le_trans (le_max_right _ _) hm
  have hm4 : 4 ≤ m := le_trans (le_max_left _ _) hm_ge_max
  have hmK : K ≤ m := le_trans (le_max_right _ _) hm_ge_max
  have hAPer := walshDigitMask_in_periodicDyadicSpan F A hA
  have hBPer := walshDigitMask_in_periodicDyadicSpan F B hB
  refine hProfile F m α (fun _ => 2) (fun _ => 2) A B hm₀ hAPer hBPer ?_
  have hsum : (min (∑ _j : Fin m, 2) (∑ _j : Fin m, 2) : ℕ) = 2 * m := by
    simp [mul_comm]
  rw [hsum]
  have hKm_nat : K * m ≤ 2 ^ m :=
    le_trans (Nat.mul_le_mul_right m hmK) (sq_le_two_pow hm4)
  have hKm_real : (K : ℝ) * (m : ℝ) ≤ ((2 ^ m : ℕ) : ℝ) := by
    exact_mod_cast hKm_nat
  have h2_le_dK : (2 : ℝ) ≤ δ * (K : ℝ) := by
    have hlt : 2 / δ < (K : ℝ) := hK
    have hmul := mul_lt_mul_of_pos_left hlt hδ
    have hdiv : δ * (2 / δ) = 2 := mul_div_cancel₀ 2 (ne_of_gt hδ)
    linarith
  have hm_nonneg : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  calc (((2 * m : ℕ) : ℝ))
      = (2 : ℝ) * (m : ℝ) := by push_cast; ring
    _ ≤ (δ * (K : ℝ)) * (m : ℝ) := mul_le_mul_of_nonneg_right h2_le_dK hm_nonneg
    _ = δ * ((K : ℝ) * (m : ℝ)) := by ring
    _ ≤ δ * ((2 ^ m : ℕ) : ℝ) := mul_le_mul_of_nonneg_left hKm_real (le_of_lt hδ)

end Bonus2Proofs

end BoundedArityDecoders
