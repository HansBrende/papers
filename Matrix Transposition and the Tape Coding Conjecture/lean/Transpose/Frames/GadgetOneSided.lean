import Transpose.Frames.GadgetMod2
import Transpose.Frames.RankMod

/-!
# The one-sided mod-2 bound for `m × m` integer frames

For every nonzero row vector `l ∈ F₂^m` the coarsening `M ↦ l ᵥ* (M mod 2)` separates every source
`S u` from its target `S u + 1` (the difference is `l ≠ 0`), so by the coarsening lemma
(`visible_ge_W_of_coarse`) it sees at least `W` of the jumps of a valid run realising the
permutation.  A jump `J` (reduced mod 2, of rank `r̄` over `F₂`) is seen by exactly
`2^m − 2^{m − r̄}` of the `2^m − 1` nonzero vectors: the invisible ones form the left kernel of `J`,
a subspace of dimension `m − r̄` (rank–nullity).  Since `2 (2^m − 2^{m−r̄}) ≤ 2^m r̄` and
`r̄ ≤ rank_ℚ J` (`RankMod.lean`), summing over the family gives

  `2 (2^m − 1) W ≤ 2^m · Σ_jumps rank_ℚ (jump)`,

i.e. the gadget cost `s = Σ rank` satisfies `s ≥ 2 (1 − 2^{−m}) W`: `one_sided_bound`.
-/

namespace Transpose.ShearFrame

open Module Submodule Matrix

variable {W : ℕ}

/-! ### The coarsenings `M ↦ l ᵥ* (M mod 2)` -/

/-- The coarsening attached to a row vector `l ∈ F₂^m`: `M ↦ l ᵥ* (M mod 2)`. -/
def coarseRow {m : ℕ} (l : Fin m → ZMod 2) (M : Matrix (Fin m) (Fin m) ℤ) : Fin m → ZMod 2 :=
  Matrix.vecMul l (M.map (Int.cast : ℤ → ZMod 2))

theorem coarseRow_sub {m : ℕ} (l : Fin m → ZMod 2) (A B : Matrix (Fin m) (Fin m) ℤ) :
    coarseRow l B - coarseRow l A = Matrix.vecMul l ((B - A).map (Int.cast : ℤ → ZMod 2)) := by
  unfold coarseRow
  rw [Matrix.map_sub Int.cast Int.cast_sub, Matrix.vecMul_sub]

theorem coarseRow_add_one {m : ℕ} (l : Fin m → ZMod 2) (M : Matrix (Fin m) (Fin m) ℤ) :
    coarseRow l (M + 1) = coarseRow l M + l := by
  unfold coarseRow
  rw [Matrix.map_add Int.cast Int.cast_add, Matrix.map_one Int.cast Int.cast_zero Int.cast_one,
    Matrix.vecMul_add, Matrix.vecMul_one]

/-- For `l ≠ 0` the coarsening separates `M + 1` from `M`. -/
theorem coarseRow_shift {m : ℕ} {l : Fin m → ZMod 2} (hl : l ≠ 0) (M : Matrix (Fin m) (Fin m) ℤ) :
    coarseRow l (M + 1) ≠ coarseRow l M := by
  intro h
  apply hl
  rw [coarseRow_add_one] at h
  have h' : coarseRow l M + l = coarseRow l M + 0 := by rw [add_zero]; exact h
  exact add_left_cancel h'

/-- A jump `(A, B)` is invisible to `l` iff `l` is in the left kernel of `(B − A) mod 2`. -/
theorem coarseRow_eq_iff {m : ℕ} (l : Fin m → ZMod 2)
    (p : Matrix (Fin m) (Fin m) ℤ × Matrix (Fin m) (Fin m) ℤ) :
    coarseRow l p.1 = coarseRow l p.2 ↔
      Matrix.vecMul l ((p.2 - p.1).map (Int.cast : ℤ → ZMod 2)) = 0 := by
  rw [← coarseRow_sub, sub_eq_zero, eq_comm]

/-! ### Exchanging a `Finset` sum with a list sum -/

theorem finset_sum_list_sum_comm {α β : Type} (s : Finset β) (g : β → α → ℕ) :
    ∀ (l : List α), ∑ q ∈ s, (l.map (g q)).sum = (l.map (fun p => ∑ q ∈ s, g q p)).sum
  | [] => by simp
  | p :: l => by
      simp only [List.map_cons, List.sum_cons]
      rw [Finset.sum_add_distrib, finset_sum_list_sum_comm s g l]

/-! ### Counting the vectors that see a jump -/

/-- The nonzero row vectors of `F₂^m`. -/
def nz (m : ℕ) : Finset (Fin m → ZMod 2) := Finset.univ.filter (fun l => l ≠ 0)

theorem mem_nz {m : ℕ} {l : Fin m → ZMod 2} : l ∈ nz m ↔ l ≠ 0 := by
  simp [nz]

theorem card_nz (m : ℕ) : (nz m).card = 2 ^ m - 1 := by
  unfold nz
  rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fun, ZMod.card, Fintype.card_fin]

/-- The left kernel of `J` over `F₂` has `2 ^ (m − rank J)` elements. -/
theorem card_vecMul_eq_zero {m : ℕ} (J : Matrix (Fin m) (Fin m) (ZMod 2)) :
    (Finset.univ.filter (fun l : Fin m → ZMod 2 => Matrix.vecMul l J = 0)).card =
      2 ^ (m - J.rank) := by
  classical
  let f : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2) := Jᵀ.mulVecLin
  have hker : ∀ l, l ∈ LinearMap.ker f ↔ Matrix.vecMul l J = 0 := by
    intro l
    rw [LinearMap.mem_ker]
    show Jᵀ *ᵥ l = 0 ↔ _
    rw [Matrix.mulVec_transpose]
  have hcard : Fintype.card (LinearMap.ker f) = 2 ^ finrank (ZMod 2) (LinearMap.ker f) := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2) (V := LinearMap.ker f), ZMod.card]
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  rw [Module.finrank_fin_fun] at hrn
  have hrange : finrank (ZMod 2) (LinearMap.range f) = J.rank := by
    rw [← Matrix.rank_transpose J]
    rfl
  have hfilter : Fintype.card (LinearMap.ker f) =
      (Finset.univ.filter (fun l : Fin m → ZMod 2 => Matrix.vecMul l J = 0)).card :=
    Fintype.card_of_subtype _ (fun l => by rw [Finset.mem_filter, hker]; simp)
  rw [← hfilter, hcard]
  congr 1
  omega

/-- Exactly `2^m − 2^(m − rank J)` nonzero row vectors see `J`. -/
theorem card_nz_vecMul_ne_zero {m : ℕ} (J : Matrix (Fin m) (Fin m) (ZMod 2)) :
    ((nz m).filter (fun l => Matrix.vecMul l J ≠ 0)).card = 2 ^ m - 2 ^ (m - J.rank) := by
  have h1 := Finset.card_filter_add_card_filter_not (s := nz m)
    (fun l => Matrix.vecMul l J ≠ 0)
  have h2 : ((nz m).filter (fun l => ¬ Matrix.vecMul l J ≠ 0)).card = 2 ^ (m - J.rank) - 1 := by
    have heq : (nz m).filter (fun l => ¬ Matrix.vecMul l J ≠ 0) =
        (Finset.univ.filter (fun l : Fin m → ZMod 2 => Matrix.vecMul l J = 0)).erase 0 := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_erase, mem_nz, Finset.mem_univ, true_and, not_not]
    rw [heq, Finset.card_erase_of_mem (by simp [Matrix.zero_vecMul]), card_vecMul_eq_zero]
  have h3 := card_nz m
  have h4 : 2 ^ (m - J.rank) ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)
  have h5 : 1 ≤ 2 ^ (m - J.rank) := Nat.one_le_two_pow
  omega

/-- The indicator sum over the family is the number of vectors that see `J`. -/
theorem sum_indicator_eq_card {m : ℕ} (J : Matrix (Fin m) (Fin m) (ZMod 2)) :
    ∑ l ∈ nz m, (if Matrix.vecMul l J = 0 then 0 else 1) =
      ((nz m).filter (fun l => Matrix.vecMul l J ≠ 0)).card := by
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro l _
  by_cases h : Matrix.vecMul l J = 0 <;> simp [h]

/-! ### The numeric inequality `2 (2^m − 2^{m−r}) ≤ 2^m r` -/

theorem two_pow_ineq (m : ℕ) : ∀ r, r ≤ m → 2 * 2 ^ m ≤ 2 * 2 ^ (m - r) + 2 ^ m * r
  | 0, _ => by simp
  | r + 1, hr => by
      have ih := two_pow_ineq m r (by omega)
      have h1 : 2 ^ (m - r) = 2 * 2 ^ (m - (r + 1)) := by
        rw [← pow_succ']
        congr 1
        omega
      have h2 : 2 ^ (m - r) ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)
      rw [h1] at ih h2
      rw [Nat.mul_succ]
      generalize 2 ^ m = a at *
      generalize 2 ^ (m - (r + 1)) = b at *
      generalize a * r = c at *
      omega

theorem two_mul_sub_le {m r : ℕ} (hr : r ≤ m) : 2 * (2 ^ m - 2 ^ (m - r)) ≤ 2 ^ m * r := by
  have h := two_pow_ineq m r hr
  have h2 : 2 ^ (m - r) ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)
  generalize 2 ^ m = a at *
  generalize 2 ^ (m - r) = b at *
  generalize a * r = c at *
  omega

/-! ### The theorem -/

/-- One-sided mod-2 bound, any m: for integer m×m frames and targets `S u + 1`, the total rank
over ℚ of the jumps of a valid run realising `ρ` satisfies
`2 (2^m − 1) W ≤ 2^m · Σ rank`, i.e. `s ≥ 2(1 − 2^{−m}) W`. -/
theorem one_sided_bound {m : ℕ} (S : Fin W → Matrix (Fin m) (Fin m) ℤ) (ρ : Equiv.Perm (Fin W))
    (evs : List (Event W (Matrix (Fin m) (Fin m) ℤ))) (hv : (init S).allValid evs)
    (hframe : ∀ u, ((init S).run evs).frame (ρ u) = S u + 1)
    (hvec : ∀ u, ((init S).run evs).vec (ρ u) = e u) :
    2 * (2 ^ m - 1) * W ≤
      2 ^ m * ((jumps evs (init S)).map (fun p => ((p.2 - p.1).map (Int.cast : ℤ → ℚ)).rank)).sum := by
  set J := jumps evs (init S) with hJ
  -- each nonzero coarsening sees at least `W` jumps (the coarsening lemma)
  have hl : ∀ l ∈ nz m,
      W ≤ (J.map (fun p => if coarseRow l p.1 = coarseRow l p.2 then 0 else 1)).sum := by
    intro l hlmem
    have hl0 : l ≠ 0 := mem_nz.mp hlmem
    rw [hJ, ← vmoves_map_eq]
    exact visible_ge_W_of_coarse S (fun u => S u + 1) ρ evs hv hframe hvec (coarseRow l)
      (fun u => coarseRow_shift hl0 (S u))
  -- sum over the `2^m − 1` coarsenings
  have hsum : (2 ^ m - 1) * W ≤
      ∑ l ∈ nz m, (J.map (fun p => if coarseRow l p.1 = coarseRow l p.2 then 0 else 1)).sum := by
    have h := Finset.sum_le_sum hl
    rw [Finset.sum_const, smul_eq_mul, card_nz] at h
    exact h
  rw [finset_sum_list_sum_comm] at hsum
  -- per jump: the number of coarsenings that see it
  have hjump : ∀ p ∈ J, ∑ l ∈ nz m, (if coarseRow l p.1 = coarseRow l p.2 then 0 else 1) =
      2 ^ m - 2 ^ (m - ((p.2 - p.1).map (Int.cast : ℤ → ZMod 2)).rank) := by
    intro p _
    rw [← card_nz_vecMul_ne_zero, ← sum_indicator_eq_card]
    apply Finset.sum_congr rfl
    intro l _
    exact if_congr (coarseRow_eq_iff l p) rfl rfl
  rw [List.map_congr_left hjump] at hsum
  -- and that is at most `2^(m-1) × rank`
  have hle : (J.map (fun p =>
      2 * (2 ^ m - 2 ^ (m - ((p.2 - p.1).map (Int.cast : ℤ → ZMod 2)).rank)))).sum ≤
      (J.map (fun p => 2 ^ m * ((p.2 - p.1).map (Int.cast : ℤ → ℚ)).rank)).sum := by
    apply List.sum_le_sum
    intro p _
    have hrb := rank_map_zmod_le_rank_map_rat (p.2 - p.1)
    have hm : ((p.2 - p.1).map (Int.cast : ℤ → ZMod 2)).rank ≤ m := Matrix.rank_le_height _
    exact (two_mul_sub_le hm).trans (Nat.mul_le_mul_left _ hrb)
  rw [List.sum_map_mul_left, List.sum_map_mul_left] at hle
  calc 2 * (2 ^ m - 1) * W = 2 * ((2 ^ m - 1) * W) := mul_assoc _ _ _
    _ ≤ 2 * (J.map (fun p =>
          2 ^ m - 2 ^ (m - ((p.2 - p.1).map (Int.cast : ℤ → ZMod 2)).rank))).sum :=
        Nat.mul_le_mul_left 2 hsum
    _ ≤ _ := hle

end Transpose.ShearFrame
