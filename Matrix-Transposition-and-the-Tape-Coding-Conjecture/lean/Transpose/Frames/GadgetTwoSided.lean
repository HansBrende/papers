import Transpose.Frames.GadgetOneSided

/-!
# The two-sided mod-2 bound for `m × m` integer frames (every `m`)

For every pair `(l, u) ∈ F₂^m × F₂^m` with `l ⬝ᵥ u = 1` the coarsening `M ↦ l ⬝ᵥ ((M mod 2) *ᵥ u)`
separates every source `S u` from its target `S u + 1` (the difference is `l ⬝ᵥ u = 1`), so by
the coarsening lemma (`visible_ge_W_of_coarse`) it sees at least `W` of the jumps of a valid run
realising the permutation.  There are `2^{m−1} (2^m − 1)` such pairs (`card_fam`).

A jump `J` (reduced mod 2, of rank `r` over `F₂`) is seen by the pair `(l, u)` iff
`(l ᵥ* J) ⬝ᵥ u ≠ 0`.  For fixed `l`, with `b := l ᵥ* J`, the number of `u` with `l ⬝ᵥ u = 1` and
`b ⬝ᵥ u ≠ 0` is `0` if `b = 0`, `2^{m−1}` if `b = l`, and `2^{m−2}` if `b ∉ {0, l}` (then `l, b` are
linearly independent and `u ↦ (l ⬝ᵥ u, b ⬝ᵥ u)` is onto `F₂²`): `cnt_le`.  Hence
`vis J ≤ 2^{m−1} E + 2^{m−2} D` with `E = #{l : l ᵥ* J = l ≠ 0}` and `D = #{l : l ᵥ* J ∉ {0, l}}`,
where `2^{m−r} + E + D = 2^m` (the left kernel has `2^{m−r}` elements) and `E + 1 ≤ 2^r` (the fixed
vectors of `l ↦ l ᵥ* J` lie in the row space).  The elementary inequality
`2^m − 2^{m−r} + 2^r − 1 ≤ (2^{m−1} + 1) r` then gives the per-jump bound

  `2 · vis J ≤ (2^{m−1} + 1) · 2^{m−1} · r`  (`two_mul_vis_le`),

and since `r ≤ rank_ℚ J` (`RankMod.lean`), summing over the family gives

  `2 (2^m − 1) W ≤ (2^{m−1} + 1) · Σ_jumps rank_ℚ (jump)`,

i.e. the gadget cost `s = Σ rank` satisfies `s ≥ 2 (2^m − 1) W / (2^{m−1} + 1)`: `two_sided_bound`
(`2W` for `m = 2`, `2.8W` for `m = 3`, `→ 4W` as `m → ∞`).
-/

namespace Transpose.ShearFrame

open Module Submodule Matrix

variable {W : ℕ}

/-! ### Arithmetic in `F₂` -/

theorem zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x; decide

theorem zmod2_ne_zero_iff {x : ZMod 2} : x ≠ 0 ↔ x = 1 := by
  revert x; decide

theorem zmod2_add_eq_zero_iff {x y : ZMod 2} : x + y = 0 ↔ x = y := by
  revert x y; decide

/-- Over `F₂`, `a + b = 0 ↔ a = b` for vectors. -/
theorem vec_add_eq_zero_iff {m : ℕ} {a b : Fin m → ZMod 2} : a + b = 0 ↔ a = b := by
  rw [funext_iff, funext_iff]
  apply forall_congr'
  intro i
  simp only [Pi.add_apply, Pi.zero_apply]
  exact zmod2_add_eq_zero_iff

/-! ### Fibres of a surjective linear map `F₂^m → F₂^d` -/

/-- If `M : Matrix (Fin d) (Fin m) F₂` has rank `d`, every fibre of `u ↦ M *ᵥ u` has `2^(m-d)`
elements. -/
theorem card_mulVec_eq_of_rank {m d : ℕ} (M : Matrix (Fin d) (Fin m) (ZMod 2)) (hM : M.rank = d)
    (y : Fin d → ZMod 2) :
    (Finset.univ.filter (fun u : Fin m → ZMod 2 => M *ᵥ u = y)).card = 2 ^ (m - d) := by
  classical
  let f : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin d → ZMod 2) := M.mulVecLin
  have hrange : finrank (ZMod 2) (LinearMap.range f) = d := hM
  have htop : LinearMap.range f = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [hrange, Module.finrank_fin_fun]
  obtain ⟨u₀, hu₀⟩ : ∃ u₀, M *ᵥ u₀ = y := LinearMap.range_eq_top.mp htop y
  have hfib : (Finset.univ.filter (fun u : Fin m → ZMod 2 => M *ᵥ u = y)).card =
      (Finset.univ.filter (fun u : Fin m → ZMod 2 => M *ᵥ u = 0)).card := by
    apply Finset.card_nbij' (fun u => u - u₀) (fun u => u + u₀)
    · intro u hu
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
      rw [Matrix.mulVec_sub, hu, hu₀, sub_self]
    · intro u hu
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
      rw [Matrix.mulVec_add, hu, hu₀, zero_add]
    · intro u _
      simp
    · intro u _
      simp
  rw [hfib]
  have hker : ∀ u, u ∈ LinearMap.ker f ↔ M *ᵥ u = 0 := by
    intro u
    rw [LinearMap.mem_ker]
    rfl
  have hcard : Fintype.card (LinearMap.ker f) = 2 ^ finrank (ZMod 2) (LinearMap.ker f) := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2) (V := LinearMap.ker f), ZMod.card]
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  rw [Module.finrank_fin_fun, hrange] at hrn
  have hfilter : Fintype.card (LinearMap.ker f) =
      (Finset.univ.filter (fun u : Fin m → ZMod 2 => M *ᵥ u = 0)).card :=
    Fintype.card_of_subtype _ (fun u => by rw [Finset.mem_filter, hker]; simp)
  rw [← hfilter, hcard]
  congr 1
  omega

/-- For `a ≠ 0`, exactly `2^(m-1)` vectors `u` have `a ⬝ᵥ u = 1`. -/
theorem card_dot_eq_one {m : ℕ} {a : Fin m → ZMod 2} (ha : a ≠ 0) :
    (Finset.univ.filter (fun u : Fin m → ZMod 2 => a ⬝ᵥ u = 1)).card = 2 ^ (m - 1) := by
  have hrank : (Matrix.of ![a]).rank = 1 := by
    have hli : LinearIndependent (ZMod 2) (Matrix.of ![a]).row := by
      rw [linearIndependent_unique_iff]
      exact ha
    rw [LinearIndependent.rank_matrix hli, Fintype.card_fin]
  rw [← card_mulVec_eq_of_rank (Matrix.of ![a]) hrank ![1]]
  congr 1
  apply Finset.filter_congr
  intro u _
  rw [funext_iff, Fin.forall_fin_one]
  simp [Matrix.mulVec]

/-- For `a, b` linearly independent over `F₂` (`a ≠ 0`, `b ≠ 0`, `a ≠ b`), exactly `2^(m-2)`
vectors `u` have `a ⬝ᵥ u = 1` and `b ⬝ᵥ u = 1`. -/
theorem card_dot_eq_one_pair {m : ℕ} {a b : Fin m → ZMod 2} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a ≠ b) :
    (Finset.univ.filter (fun u : Fin m → ZMod 2 => a ⬝ᵥ u = 1 ∧ b ⬝ᵥ u = 1)).card =
      2 ^ (m - 2) := by
  have hrank : (Matrix.of ![a, b]).rank = 2 := by
    have hli : LinearIndependent (ZMod 2) (Matrix.of ![a, b]).row := by
      show LinearIndependent (ZMod 2) ![a, b]
      rw [LinearIndependent.pair_iff]
      intro s t hst
      rcases zmod2_cases s with rfl | rfl <;> rcases zmod2_cases t with rfl | rfl
      · exact ⟨rfl, rfl⟩
      · rw [zero_smul, one_smul, zero_add] at hst
        exact absurd hst hb
      · rw [one_smul, zero_smul, add_zero] at hst
        exact absurd hst ha
      · rw [one_smul, one_smul] at hst
        exact absurd (vec_add_eq_zero_iff.mp hst) hab
    rw [LinearIndependent.rank_matrix hli, Fintype.card_fin]
  rw [← card_mulVec_eq_of_rank (Matrix.of ![a, b]) hrank ![1, 1]]
  congr 1
  apply Finset.filter_congr
  intro u _
  rw [funext_iff, Fin.forall_fin_two]
  simp [Matrix.mulVec]

/-! ### The family of pairs `(l, u)` with `l ⬝ᵥ u = 1` -/

/-- The pairs `(l, u) ∈ F₂^m × F₂^m` with `l ⬝ᵥ u = 1`. -/
def fam (m : ℕ) : Finset ((Fin m → ZMod 2) × (Fin m → ZMod 2)) :=
  Finset.univ.filter (fun q => q.1 ⬝ᵥ q.2 = 1)

theorem mem_fam {m : ℕ} {q : (Fin m → ZMod 2) × (Fin m → ZMod 2)} :
    q ∈ fam m ↔ q.1 ⬝ᵥ q.2 = 1 := by
  simp [fam]

/-- The number of `u` with `l ⬝ᵥ u = 1`: `0` for `l = 0`, `2^(m-1)` otherwise. -/
theorem card_dot_eq_one' {m : ℕ} (l : Fin m → ZMod 2) :
    (Finset.univ.filter (fun u : Fin m → ZMod 2 => l ⬝ᵥ u = 1)).card =
      if l = 0 then 0 else 2 ^ (m - 1) := by
  split_ifs with hl
  · subst hl
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro u _
    rw [zero_dotProduct]
    exact zero_ne_one
  · exact card_dot_eq_one hl

/-- `|fam m| = 2^(m-1) (2^m − 1)`. -/
theorem card_fam (m : ℕ) : (fam m).card = 2 ^ (m - 1) * (2 ^ m - 1) := by
  have h1 : (fam m).card =
      ∑ l : Fin m → ZMod 2, (Finset.univ.filter (fun u : Fin m → ZMod 2 => l ⬝ᵥ u = 1)).card := by
    unfold fam
    rw [Finset.card_filter, ← Finset.univ_product_univ, Finset.sum_product]
    simp only [Finset.card_filter]
  rw [h1, Finset.sum_congr rfl (fun l _ => card_dot_eq_one' l), Finset.sum_ite,
    Finset.sum_const_zero, zero_add, Finset.sum_const, smul_eq_mul]
  have h2 : (Finset.univ.filter (fun l : Fin m → ZMod 2 => ¬ l = 0)).card = 2 ^ m - 1 := card_nz m
  rw [h2, mul_comm]

/-! ### Counting the pairs that see a jump -/

/-- The number of pairs of the family that see `J` (mod 2). -/
def vis {m : ℕ} (J : Matrix (Fin m) (Fin m) (ZMod 2)) : ℕ :=
  ((fam m).filter (fun q => q.1 ⬝ᵥ (J *ᵥ q.2) ≠ 0)).card

theorem sum_indicator_eq_vis {m : ℕ} (J : Matrix (Fin m) (Fin m) (ZMod 2)) :
    ∑ q ∈ fam m, (if q.1 ⬝ᵥ (J *ᵥ q.2) = 0 then 0 else 1) = vis J := by
  unfold vis
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro q _
  by_cases h : q.1 ⬝ᵥ (J *ᵥ q.2) = 0 <;> simp [h]

/-- For fixed `l`, the number of `u` with `l ⬝ᵥ u = 1` seeing `J`. -/
def cnt {m : ℕ} (J : Matrix (Fin m) (Fin m) (ZMod 2)) (l : Fin m → ZMod 2) : ℕ :=
  (Finset.univ.filter (fun u : Fin m → ZMod 2 => l ⬝ᵥ u = 1 ∧ (l ᵥ* J) ⬝ᵥ u ≠ 0)).card

theorem vis_eq_sum_cnt {m : ℕ} (J : Matrix (Fin m) (Fin m) (ZMod 2)) :
    vis J = ∑ l : Fin m → ZMod 2, cnt J l := by
  unfold vis fam cnt
  rw [Finset.filter_filter, Finset.card_filter, ← Finset.univ_product_univ, Finset.sum_product]
  simp only [Finset.card_filter, Matrix.dotProduct_mulVec]

/-- The three cases for a fixed `l`: `l ᵥ* J = 0` (nothing seen), `l ᵥ* J = l ≠ 0` (`2^(m-1)`),
`l ᵥ* J ∉ {0, l}` (`2^(m-2)`). -/
theorem cnt_le {m : ℕ} (J : Matrix (Fin m) (Fin m) (ZMod 2)) (l : Fin m → ZMod 2) :
    cnt J l ≤ 2 ^ (m - 1) * (if l ᵥ* J ≠ 0 ∧ l ᵥ* J = l then 1 else 0) +
      2 ^ (m - 2) * (if l ᵥ* J ≠ 0 ∧ l ᵥ* J ≠ l then 1 else 0) := by
  unfold cnt
  by_cases h0 : l ᵥ* J = 0
  · have hempty : (Finset.univ.filter
        (fun u : Fin m → ZMod 2 => l ⬝ᵥ u = 1 ∧ (l ᵥ* J) ⬝ᵥ u ≠ 0)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro u _ h
      exact h.2 (by rw [h0, zero_dotProduct])
    rw [hempty]
    exact Nat.zero_le _
  by_cases h1 : l ᵥ* J = l
  · rw [ite_eq_left ⟨h0, h1⟩, ite_eq_right (fun h => h.2 h1), mul_one, mul_zero, add_zero]
    have hl : l ≠ 0 := fun h => h0 (h1.trans h)
    rw [h1]
    have heq : (Finset.univ.filter (fun u : Fin m → ZMod 2 => l ⬝ᵥ u = 1 ∧ l ⬝ᵥ u ≠ 0)) =
        Finset.univ.filter (fun u : Fin m → ZMod 2 => l ⬝ᵥ u = 1) := by
      apply Finset.filter_congr
      intro u _
      constructor
      · exact fun h => h.1
      · intro h
        exact ⟨h, by rw [h]; exact one_ne_zero⟩
    rw [heq, card_dot_eq_one hl]
  · rw [ite_eq_right (fun h => h1 h.2), ite_eq_left ⟨h0, h1⟩, mul_zero, zero_add, mul_one]
    have hl : l ≠ 0 := fun h => h0 (by rw [h, Matrix.zero_vecMul])
    have hsub : (Finset.univ.filter
        (fun u : Fin m → ZMod 2 => l ⬝ᵥ u = 1 ∧ (l ᵥ* J) ⬝ᵥ u ≠ 0)) ⊆
        Finset.univ.filter (fun u : Fin m → ZMod 2 => l ⬝ᵥ u = 1 ∧ (l ᵥ* J) ⬝ᵥ u = 1) := by
      intro u hu
      rw [Finset.mem_filter] at hu ⊢
      exact ⟨hu.1, hu.2.1, zmod2_ne_zero_iff.mp hu.2.2⟩
    exact (Finset.card_le_card hsub).trans (card_dot_eq_one_pair hl h0 (Ne.symm h1)).le

/-- `E J`: the number of `l` with `l ᵥ* J = l ≠ 0`. -/
def cE {m : ℕ} (J : Matrix (Fin m) (Fin m) (ZMod 2)) : ℕ :=
  (Finset.univ.filter (fun l : Fin m → ZMod 2 => l ᵥ* J ≠ 0 ∧ l ᵥ* J = l)).card

/-- `D J`: the number of `l` with `l ᵥ* J ∉ {0, l}`. -/
def cD {m : ℕ} (J : Matrix (Fin m) (Fin m) (ZMod 2)) : ℕ :=
  (Finset.univ.filter (fun l : Fin m → ZMod 2 => l ᵥ* J ≠ 0 ∧ l ᵥ* J ≠ l)).card

theorem vis_le {m : ℕ} (J : Matrix (Fin m) (Fin m) (ZMod 2)) :
    vis J ≤ 2 ^ (m - 1) * cE J + 2 ^ (m - 2) * cD J := by
  rw [vis_eq_sum_cnt]
  calc ∑ l, cnt J l
      ≤ ∑ l : Fin m → ZMod 2, (2 ^ (m - 1) * (if l ᵥ* J ≠ 0 ∧ l ᵥ* J = l then 1 else 0) +
          2 ^ (m - 2) * (if l ᵥ* J ≠ 0 ∧ l ᵥ* J ≠ l then 1 else 0)) :=
        Finset.sum_le_sum (fun l _ => cnt_le J l)
    _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        unfold cE cD
        rw [Finset.card_filter, Finset.card_filter]

theorem indicator_partition {m : ℕ} (J : Matrix (Fin m) (Fin m) (ZMod 2)) (l : Fin m → ZMod 2) :
    (if l ᵥ* J = 0 then 1 else 0) + (if l ᵥ* J ≠ 0 ∧ l ᵥ* J = l then 1 else 0) +
      (if l ᵥ* J ≠ 0 ∧ l ᵥ* J ≠ l then 1 else 0) = 1 := by
  by_cases h0 : l ᵥ* J = 0
  · rw [ite_eq_left h0, ite_eq_right (fun h => h.1 h0), ite_eq_right (fun h => h.1 h0)]
  · by_cases h1 : l ᵥ* J = l
    · rw [ite_eq_right h0, ite_eq_left ⟨h0, h1⟩, ite_eq_right (fun h => h.2 h1)]
    · rw [ite_eq_right h0, ite_eq_right (fun h => h1 h.2), ite_eq_left ⟨h0, h1⟩]

/-- The left kernel, the nonzero fixed vectors and the rest partition `F₂^m`. -/
theorem card_partition {m : ℕ} (J : Matrix (Fin m) (Fin m) (ZMod 2)) :
    2 ^ (m - J.rank) + cE J + cD J = 2 ^ m := by
  rw [← card_vecMul_eq_zero J]
  unfold cE cD
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, Finset.sum_congr rfl (fun l _ => indicator_partition J l),
    Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ, Fintype.card_fun, ZMod.card,
    Fintype.card_fin]

/-- The vectors fixed by `l ↦ l ᵥ* J` lie in the row space of `J`, which has `2^rank J` elements. -/
theorem cE_add_one_le {m : ℕ} (J : Matrix (Fin m) (Fin m) (ZMod 2)) : cE J + 1 ≤ 2 ^ J.rank := by
  classical
  let f : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2) := Jᵀ.mulVecLin
  have hcard : Fintype.card (LinearMap.range f) = 2 ^ J.rank := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2) (V := LinearMap.range f), ZMod.card,
      ← Matrix.rank_transpose J]
    rfl
  have hfilter : Fintype.card (LinearMap.range f) =
      (Finset.univ.filter (fun l : Fin m → ZMod 2 => l ∈ LinearMap.range f)).card :=
    Fintype.card_of_subtype _ (fun l => by simp)
  have hsub : insert 0 (Finset.univ.filter
      (fun l : Fin m → ZMod 2 => l ᵥ* J ≠ 0 ∧ l ᵥ* J = l)) ⊆
      Finset.univ.filter (fun l : Fin m → ZMod 2 => l ∈ LinearMap.range f) := by
    intro l hl
    rw [Finset.mem_insert, Finset.mem_filter] at hl
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases hl with rfl | ⟨_, _, h⟩
    · exact zero_mem _
    · refine ⟨l, ?_⟩
      show Jᵀ *ᵥ l = l
      rw [Matrix.mulVec_transpose]
      exact h
  have h0 : (0 : Fin m → ZMod 2) ∉ Finset.univ.filter
      (fun l : Fin m → ZMod 2 => l ᵥ* J ≠ 0 ∧ l ᵥ* J = l) := by
    rw [Finset.mem_filter]
    rintro ⟨_, h, _⟩
    exact h (Matrix.zero_vecMul J)
  have hle := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem h0, ← hfilter, hcard] at hle
  exact hle

/-! ### The numeric inequality `2^m − 2^{m−r} + 2^r − 1 ≤ (2^{m−1} + 1) r` -/

theorem two_pow_ineq_two_sided (m : ℕ) :
    ∀ r, r + 1 ≤ m →
      2 ^ m + 2 ^ (r + 1) ≤ (2 ^ (m - 1) + 1) * (r + 1) + 2 ^ (m - (r + 1)) + 1
  | 0, hm => by
      have h1 : 2 ^ m = 2 * 2 ^ (m - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      rw [h1]
      generalize 2 ^ (m - 1) = a
      omega
  | r + 1, hm => by
      have ih := two_pow_ineq_two_sided m r (by omega)
      have h1 : 2 ^ (m - (r + 1)) = 2 * 2 ^ (m - (r + 1 + 1)) := by
        rw [← pow_succ']
        congr 1
        omega
      have h2 : 2 ^ (r + 1 + 1) = 2 * 2 ^ (r + 1) := by rw [pow_succ']
      have h3 : 2 ^ (r + 1) * 2 ^ (m - (r + 1 + 1)) = 2 ^ (m - 1) := by
        rw [← pow_add]
        congr 1
        omega
      have h4 : 1 ≤ 2 ^ (r + 1) := Nat.one_le_two_pow
      have h5 : 1 ≤ 2 ^ (m - (r + 1 + 1)) := Nat.one_le_two_pow
      have hc : (2 ^ (m - 1) + 1) * (r + 1 + 1) =
          (2 ^ (m - 1) + 1) * (r + 1) + (2 ^ (m - 1) + 1) := by ring
      rw [h1] at ih
      rw [h2, hc]
      generalize 2 ^ (m - 1) = A at *
      generalize 2 ^ (r + 1) = x at *
      generalize 2 ^ (m - (r + 1 + 1)) = y at *
      generalize (A + 1) * (r + 1) = c at *
      have h6 : x + y ≤ x * y + 1 := by
        obtain ⟨x', rfl⟩ := Nat.exists_eq_add_of_le h4
        obtain ⟨y', rfl⟩ := Nat.exists_eq_add_of_le h5
        nlinarith [Nat.zero_le (x' * y')]
      omega

/-- The per-jump arithmetic: from `K = 2^{m−r}`, `K + E + D = 2^m` and `E + 1 ≤ 2^r` deduce
`2 (2^{m−1} E + 2^{m−2} D) ≤ (2^{m−1} + 1) 2^{m−1} r`. -/
theorem key_numeric {m r K E D : ℕ} (hr : r ≤ m) (hK : K = 2 ^ (m - r))
    (hsum : K + E + D = 2 ^ m) (hE : E + 1 ≤ 2 ^ r) :
    2 * (2 ^ (m - 1) * E + 2 ^ (m - 2) * D) ≤ (2 ^ (m - 1) + 1) * 2 ^ (m - 1) * r := by
  rcases Nat.lt_or_ge m 2 with hm | hm
  · interval_cases m
    · have hr0 : r = 0 := by omega
      subst hr0
      simp at hK hsum hE ⊢
      omega
    · interval_cases r
      · simp at hK hsum hE ⊢
        omega
      · simp at hK hsum hE ⊢
        omega
  · have h1 : 2 ^ (m - 1) = 2 * 2 ^ (m - 2) := by
      rw [← pow_succ']
      congr 1
      omega
    have h2 : 2 ^ m = 2 * 2 ^ (m - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rcases Nat.eq_zero_or_pos r with hr0 | hr0
    · subst hr0
      rw [Nat.sub_zero] at hK
      have hE0 : E = 0 := by
        rw [pow_zero] at hE
        omega
      subst hE0
      have hD : D = 0 := by omega
      subst hD
      simp
    · obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
      have hnum := two_pow_ineq_two_sided m r' (by omega)
      rw [← hK] at hnum
      rw [h2, h1] at hsum
      rw [h1] at hnum ⊢
      generalize 2 ^ (m - 2) = a at *
      generalize 2 ^ (r' + 1) = x at *
      generalize hc : (2 * a + 1) * (r' + 1) = c at *
      have hgoal : (2 * a + 1) * (2 * a) * (r' + 1) = 2 * a * c := by
        rw [← hc]
        ring
      rw [hgoal]
      have hlin : 2 * E + D ≤ c := by omega
      calc 2 * (2 * a * E + a * D) = 2 * a * (2 * E + D) := by ring
        _ ≤ 2 * a * c := Nat.mul_le_mul_left _ hlin

/-- **Per-jump bound.** `2 · vis J ≤ (2^{m−1} + 1) · 2^{m−1} · rank J`. -/
theorem two_mul_vis_le {m : ℕ} (J : Matrix (Fin m) (Fin m) (ZMod 2)) :
    2 * vis J ≤ (2 ^ (m - 1) + 1) * 2 ^ (m - 1) * J.rank := by
  have hr : J.rank ≤ m := Matrix.rank_le_height J
  have h := key_numeric hr rfl (card_partition J) (cE_add_one_le J)
  exact (Nat.mul_le_mul_left 2 (vis_le J)).trans h

/-! ### The coarsenings `M ↦ l ⬝ᵥ ((M mod 2) *ᵥ u)` -/

/-- The coarsening attached to a pair `q = (l, u)`: `M ↦ l ⬝ᵥ ((M mod 2) *ᵥ u)`. -/
def coarsePair {m : ℕ} (q : (Fin m → ZMod 2) × (Fin m → ZMod 2))
    (M : Matrix (Fin m) (Fin m) ℤ) : ZMod 2 :=
  q.1 ⬝ᵥ ((M.map (Int.cast : ℤ → ZMod 2)) *ᵥ q.2)

theorem coarsePair_sub {m : ℕ} (q : (Fin m → ZMod 2) × (Fin m → ZMod 2))
    (A B : Matrix (Fin m) (Fin m) ℤ) :
    coarsePair q B - coarsePair q A =
      q.1 ⬝ᵥ (((B - A).map (Int.cast : ℤ → ZMod 2)) *ᵥ q.2) := by
  unfold coarsePair
  rw [Matrix.map_sub Int.cast Int.cast_sub, Matrix.sub_mulVec, dotProduct_sub]

/-- For `l ⬝ᵥ u = 1` the coarsening separates `M + 1` from `M`. -/
theorem coarsePair_shift {m : ℕ} (q : (Fin m → ZMod 2) × (Fin m → ZMod 2))
    (hq : q.1 ⬝ᵥ q.2 = 1) (M : Matrix (Fin m) (Fin m) ℤ) :
    coarsePair q (M + 1) ≠ coarsePair q M := by
  intro h
  have h1 : coarsePair q (M + 1) - coarsePair q M = 1 := by
    rw [coarsePair_sub, add_sub_cancel_left, Matrix.map_one Int.cast Int.cast_zero Int.cast_one,
      Matrix.one_mulVec, hq]
  rw [h, sub_self] at h1
  exact zero_ne_one h1

/-- A jump `(A, B)` is invisible to `(l, u)` iff `l ⬝ᵥ (((B − A) mod 2) *ᵥ u) = 0`. -/
theorem coarsePair_eq_iff {m : ℕ} (q : (Fin m → ZMod 2) × (Fin m → ZMod 2))
    (p : Matrix (Fin m) (Fin m) ℤ × Matrix (Fin m) (Fin m) ℤ) :
    coarsePair q p.1 = coarsePair q p.2 ↔
      q.1 ⬝ᵥ (((p.2 - p.1).map (Int.cast : ℤ → ZMod 2)) *ᵥ q.2) = 0 := by
  rw [← coarsePair_sub, sub_eq_zero, eq_comm]

/-! ### The theorem -/

/-- **Two-sided mod-2 bound, every m.**  For integer `m × m` frames and targets
`S u + 1`, the total rank over `ℚ` of the jumps of a valid run realising `ρ` satisfies
`2 (2^m − 1) W ≤ (2^{m−1} + 1) · Σ rank`, i.e. `s ≥ 2 (2^m − 1) W / (2^{m−1} + 1)`. -/
theorem two_sided_bound {m : ℕ} (S : Fin W → Matrix (Fin m) (Fin m) ℤ) (ρ : Equiv.Perm (Fin W))
    (evs : List (Event W (Matrix (Fin m) (Fin m) ℤ))) (hv : (init S).allValid evs)
    (hframe : ∀ u, ((init S).run evs).frame (ρ u) = S u + 1)
    (hvec : ∀ u, ((init S).run evs).vec (ρ u) = e u) :
    2 * (2 ^ m - 1) * W ≤
      (2 ^ (m - 1) + 1) *
        ((jumps evs (init S)).map (fun p => ((p.2 - p.1).map (Int.cast : ℤ → ℚ)).rank)).sum := by
  set J := jumps evs (init S) with hJ
  -- each coarsening of the family sees at least `W` jumps (the coarsening lemma)
  have hq : ∀ q ∈ fam m,
      W ≤ (J.map (fun p => if coarsePair q p.1 = coarsePair q p.2 then 0 else 1)).sum := by
    intro q hqmem
    rw [hJ, ← vmoves_map_eq]
    exact visible_ge_W_of_coarse S (fun u => S u + 1) ρ evs hv hframe hvec (coarsePair q)
      (fun u => coarsePair_shift q (mem_fam.mp hqmem) (S u))
  -- sum over the `2^(m-1) (2^m - 1)` coarsenings
  have hsum : 2 ^ (m - 1) * (2 ^ m - 1) * W ≤
      ∑ q ∈ fam m, (J.map (fun p => if coarsePair q p.1 = coarsePair q p.2 then 0 else 1)).sum := by
    have h := Finset.sum_le_sum hq
    rw [Finset.sum_const, smul_eq_mul, card_fam] at h
    exact h
  rw [finset_sum_list_sum_comm] at hsum
  -- per jump: the number of coarsenings that see it is `vis` of its reduction
  have hjump : ∀ p ∈ J, ∑ q ∈ fam m, (if coarsePair q p.1 = coarsePair q p.2 then 0 else 1) =
      vis ((p.2 - p.1).map (Int.cast : ℤ → ZMod 2)) := by
    intro p _
    rw [← sum_indicator_eq_vis]
    apply Finset.sum_congr rfl
    intro q _
    exact if_congr (coarsePair_eq_iff q p) rfl rfl
  rw [List.map_congr_left hjump] at hsum
  -- and twice that is at most `(2^(m-1) + 1) 2^(m-1) × rank`
  have hle : (J.map (fun p => 2 * vis ((p.2 - p.1).map (Int.cast : ℤ → ZMod 2)))).sum ≤
      (J.map (fun p => (2 ^ (m - 1) + 1) * 2 ^ (m - 1) *
        ((p.2 - p.1).map (Int.cast : ℤ → ℚ)).rank)).sum := by
    apply List.sum_le_sum
    intro p _
    have hrb := rank_map_zmod_le_rank_map_rat (p.2 - p.1)
    exact (two_mul_vis_le _).trans (Nat.mul_le_mul_left _ hrb)
  rw [List.sum_map_mul_left, List.sum_map_mul_left] at hle
  have hpos : 0 < 2 ^ (m - 1) := Nat.two_pow_pos _
  apply Nat.le_of_mul_le_mul_left _ hpos
  generalize 2 ^ (m - 1) = A at *
  generalize 2 ^ m - 1 = T at *
  generalize (J.map (fun p => vis ((p.2 - p.1).map (Int.cast : ℤ → ZMod 2)))).sum = V at *
  generalize (J.map (fun p => ((p.2 - p.1).map (Int.cast : ℤ → ℚ)).rank)).sum = R at *
  nlinarith

end Transpose.ShearFrame
