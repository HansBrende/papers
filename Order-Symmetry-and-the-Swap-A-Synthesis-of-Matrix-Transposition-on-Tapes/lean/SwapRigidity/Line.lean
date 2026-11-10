import SwapRigidity.Swap
import Mathlib.Data.Int.Interval

/-!
# Class-uniform rules on a line (the line form of Theorem TP)

A tape is a line, not a cycle.  Matrices are indexed by `Fin n`, and a row is read through a
window that is shifted *without* wrap-around: `lineView c X i d` is `X i (d + c)` if the
column `d + c` exists and `0` otherwise, for every integer offset `d`.

A subspace `𝒳` of matrices is a *line-uniform code* for a colouring `cls` of the rows if row
`c` of every `X ∈ 𝒳` is a fixed linear function of `lineView c X` that depends only on the
class of `c` (`IsLineUniformCode`).  This is the two-sided rule
`X c r = ∑ i, ∑ j, A (cls c) i r (j - c) * X i j` of the paper (`isLineUniformCode_of_coeff`).

The main result, `IsLineUniformCode.two_mul_finrank_le`, is the bound
`2 * dim 𝒳 ≤ n ^ 2 + n * |S|`, where `S` contains row `0` and every row whose class differs
from that of the row before it.  For `M` interval classes `|S| = M`.
-/

namespace SwapRigidity

open Module

variable {F : Type*} [Field F] {n : ℕ} {κ : Type*}

/-- The rows of a matrix seen through a window shifted by `c`, without wrap-around:
`lineView c X i d = X i (d + c)` if `0 ≤ d + c < n`, and `0` otherwise. -/
def lineView (c : ℤ) : Matrix (Fin n) (Fin n) F →ₗ[F] (Fin n → ℤ → F) where
  toFun X i d := if h : 0 ≤ d + c ∧ d + c < n then X i ⟨(d + c).toNat, by omega⟩ else 0
  map_add' X Y := by
    funext i d
    by_cases h : 0 ≤ d + c ∧ d + c < n <;> simp [h]
  map_smul' a X := by
    funext i d
    by_cases h : 0 ≤ d + c ∧ d + c < n <;> simp [h]

/-- Entries of the window `lineView c X`, unfolded. -/
theorem lineView_apply (c : ℤ) (X : Matrix (Fin n) (Fin n) F) (i : Fin n) (d : ℤ) :
    lineView c X i d = if h : 0 ≤ d + c ∧ d + c < n then X i ⟨(d + c).toNat, by omega⟩ else 0 :=
  rfl

/-- The shift of the columns by one place with a zero last column:
`truncShift X i j = X i (j + 1)` if `j + 1 < n`, and `0` otherwise. -/
def truncShift : Matrix (Fin n) (Fin n) F →ₗ[F] Matrix (Fin n) (Fin n) F where
  toFun X := Matrix.of fun i j => if h : j.val + 1 < n then X i ⟨j.val + 1, h⟩ else 0
  map_add' X Y := by
    ext i j
    by_cases h : j.val + 1 < n <;> simp [h]
  map_smul' a X := by
    ext i j
    by_cases h : j.val + 1 < n <;> simp [h]

/-- Entries of the truncated shift, unfolded. -/
theorem truncShift_apply (X : Matrix (Fin n) (Fin n) F) (i j : Fin n) :
    truncShift X i j = if h : j.val + 1 < n then X i ⟨j.val + 1, h⟩ else 0 :=
  rfl

/-- If column `0` of `X` vanishes, the window at `c` of the shifted matrix is the window at
`c + 1` of `X`. -/
theorem lineView_truncShift {X : Matrix (Fin n) (Fin n) F}
    (hX : ∀ i j : Fin n, j.val = 0 → X i j = 0) (c : ℕ) :
    lineView (c : ℤ) (truncShift X) = lineView ((c + 1 : ℕ) : ℤ) X := by
  funext i d
  rw [lineView_apply, lineView_apply]
  by_cases h1 : 0 ≤ d + (c : ℤ) ∧ d + (c : ℤ) < n
  · rw [dite_eq_left h1, truncShift_apply]
    by_cases h2 : (d + (c : ℤ)).toNat + 1 < n
    · have h3 : 0 ≤ d + ((c + 1 : ℕ) : ℤ) ∧ d + ((c + 1 : ℕ) : ℤ) < n := by
        push_cast
        omega
      rw [dite_eq_left h2, dite_eq_left h3]
      congr 1
      apply Fin.ext
      show (d + (c : ℤ)).toNat + 1 = (d + ((c + 1 : ℕ) : ℤ)).toNat
      push_cast
      omega
    · have h3 : ¬ (0 ≤ d + ((c + 1 : ℕ) : ℤ) ∧ d + ((c + 1 : ℕ) : ℤ) < n) := by
        push_cast
        omega
      rw [dite_eq_right h2, dite_eq_right h3]
  · rw [dite_eq_right h1]
    by_cases h3 : 0 ≤ d + ((c + 1 : ℕ) : ℤ) ∧ d + ((c + 1 : ℕ) : ℤ) < n
    · rw [dite_eq_left h3]
      symm
      apply hX
      show (d + ((c + 1 : ℕ) : ℤ)).toNat = 0
      push_cast at h3 ⊢
      omega
    · rw [dite_eq_right h3]

/-- A subspace `𝒳` of matrices is a *line-uniform code* for the row colouring `cls` if there
are linear decoders `dec k`, one for each class `k`, such that row `c` of every `X ∈ 𝒳` is
`dec (cls c)` applied to the window `lineView c X` of `X` at `c`. -/
def IsLineUniformCode (cls : Fin n → κ) (𝒳 : Submodule F (Matrix (Fin n) (Fin n) F)) : Prop :=
  ∃ dec : κ → ((Fin n → ℤ → F) →ₗ[F] (Fin n → F)),
    ∀ X ∈ 𝒳, ∀ c : Fin n, X c = dec (cls c) (lineView (c.val : ℤ) X)

/-- **The two-sided rule of the paper is a line-uniform code.**  Suppose every `X ∈ 𝒳` satisfies
`X c r = ∑ i, ∑ j, A (cls c) i r (j - c) * X i j`, with coefficients that depend on the class
of the output row `c`, the source row `i`, the output position `r` and the offset `j - c`
(an integer in `(-n, n)`; there is no wrap-around).  Then `𝒳` is a line-uniform code. -/
theorem isLineUniformCode_of_coeff {cls : Fin n → κ}
    {𝒳 : Submodule F (Matrix (Fin n) (Fin n) F)} (A : κ → Fin n → Fin n → ℤ → F)
    (hA : ∀ X ∈ 𝒳, ∀ c r : Fin n,
      X c r = ∑ i : Fin n, ∑ j : Fin n, A (cls c) i r ((j.val : ℤ) - (c.val : ℤ)) * X i j) :
    IsLineUniformCode cls 𝒳 := by
  refine ⟨fun k =>
    { toFun := fun Y r => ∑ i : Fin n, ∑ d ∈ Finset.Ioo (-(n : ℤ)) n, A k i r d * Y i d
      map_add' := ?_
      map_smul' := ?_ }, ?_⟩
  · intro Y Z
    funext r
    simp [mul_add, Finset.sum_add_distrib]
  · intro a Y
    funext r
    simp [Finset.mul_sum, mul_left_comm]
  · intro X hX c
    funext r
    rw [hA X hX c r]
    show _ = ∑ i : Fin n, ∑ d ∈ Finset.Ioo (-(n : ℤ)) n,
      A (cls c) i r d * lineView (c.val : ℤ) X i d
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_of_injOn (fun j : Fin n => (j.val : ℤ) - (c.val : ℤ)) ?_ ?_ ?_ ?_
    · intro j _ j' _ hjj'
      apply Fin.ext
      simp only at hjj'
      omega
    · intro j _
      simp only [Finset.mem_coe, Finset.mem_Ioo]
      omega
    · intro d _ hnot
      rw [lineView_apply, dite_eq_right, mul_zero]
      rintro ⟨h1, h2⟩
      refine hnot ⟨⟨(d + (c.val : ℤ)).toNat, by omega⟩, Finset.mem_coe.2 (Finset.mem_univ _), ?_⟩
      simp only
      omega
    · intro j _
      have hj : 0 ≤ (j.val : ℤ) - (c.val : ℤ) + (c.val : ℤ) ∧
          (j.val : ℤ) - (c.val : ℤ) + (c.val : ℤ) < n := by omega
      rw [lineView_apply, dite_eq_left hj]
      congr 2
      apply Fin.ext
      simp

/-- **Symmetric matrices are a line-uniform code** for every colouring: entry `r` of row `c` is
the entry at offset `0` of row `r` in the window at `c`.  With one class and `S = {0}` the
bound `IsLineUniformCode.two_mul_finrank_le` reads `2 * dim 𝒳 ≤ n ^ 2 + n`, which the symmetric
matrices attain by `two_mul_finrank_ker_swap_sub_one`. -/
theorem isLineUniformCode_symmetric (cls : Fin n → κ) :
    IsLineUniformCode cls (LinearMap.ker (swap F (Fin n) - 1)) := by
  refine ⟨fun _ =>
    { toFun := fun Y r => Y r 0
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }, ?_⟩
  intro X hX c
  funext r
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, swap_apply,
    Module.End.one_apply] at hX
  have hc : 0 ≤ (0 : ℤ) + (c.val : ℤ) ∧ (0 : ℤ) + (c.val : ℤ) < n := by omega
  have hsymm : X c r = X r c := congrFun (congrFun hX r) c
  show X c r = lineView (c.val : ℤ) X r 0
  rw [lineView_apply, dite_eq_left hc, hsymm]
  congr 1
  apply Fin.ext
  simp

namespace IsLineUniformCode

variable {cls : Fin n → κ} {𝒳 : Submodule F (Matrix (Fin n) (Fin n) F)}

/-- **Covariance on a line.**  If `X` and its truncated shift lie in a line-uniform code, column
`0` of `X` vanishes, and the consecutive rows `c`, `c + 1` have one class, then row `c + 1` of
`X` is row `c` shifted by one place. -/
theorem row_succ_eq (h : IsLineUniformCode cls 𝒳) {X : Matrix (Fin n) (Fin n) F} (hX : X ∈ 𝒳)
    (hTX : truncShift X ∈ 𝒳) (h0 : ∀ i j : Fin n, j.val = 0 → X i j = 0) {c c' : Fin n}
    (hcc' : c'.val = c.val + 1) (hcls : cls c = cls c') : X c' = truncShift X c := by
  obtain ⟨dec, hdec⟩ := h
  calc X c' = dec (cls c') (lineView (c'.val : ℤ) X) := hdec X hX c'
    _ = dec (cls c) (lineView (c.val : ℤ) (truncShift X)) := by
        rw [lineView_truncShift h0, hcls, hcc']
    _ = truncShift X c := (hdec _ hTX c).symm

/-- **Class-uniform bound on a line (the line form of Theorem TP).**  Let `S` be a set of rows that contains row `0`
and every row whose class differs from that of the row before it (for interval classes: the
first row of each interval).  Then every line-uniform code satisfies
`2 * dim 𝒳 ≤ n ^ 2 + n * |S|`. -/
theorem two_mul_finrank_le (h : IsLineUniformCode cls 𝒳) {S : Finset (Fin n)}
    (hS0 : ∀ c : Fin n, c.val = 0 → c ∈ S)
    (hS : ∀ c c' : Fin n, c'.val = c.val + 1 → c' ∉ S → cls c = cls c') :
    2 * finrank F 𝒳 ≤ n ^ 2 + n * S.card := by
  classical
  -- the code meets its own translate in a large subspace
  set 𝒳' : Submodule F (Matrix (Fin n) (Fin n) F) := 𝒳 ⊓ 𝒳.comap truncShift with h𝒳'
  have hcount : 2 * finrank F 𝒳 ≤ n * n + finrank F 𝒳' := by
    have h1 := finrank_le_finrank_comap 𝒳 truncShift
    have h2 : finrank F 𝒳 + finrank F (𝒳.comap truncShift) ≤
        finrank F (Matrix (Fin n) (Fin n) F) + finrank F 𝒳' :=
      finrank_add_finrank_le_add_finrank_inf 𝒳 (𝒳.comap truncShift)
    rw [Module.finrank_matrix, Fintype.card_fin, finrank_self, mul_one] at h2
    omega
  -- `Q`: the entries `(c, r)` of the first row `c` of a band whose anti-diagonal reaches
  -- column `0` inside the band
  let Q : Finset (Fin n × Fin n) := (S ×ˢ Finset.univ).filter fun p =>
    p.1.val + p.2.val < n ∧ ∀ k : Fin n, p.1 < k → k.val ≤ p.1.val + p.2.val → k ∉ S
  -- `P`: the remaining entries of the first rows of the bands
  let P : Finset (Fin n × Fin n) := (S ×ˢ Finset.univ) \ Q
  -- every row lies in exactly one band, so `Q` has at least `n` elements
  have hex : ∀ x : ℕ, ∀ hx : x < n,
      ∃ c ∈ S, c.val ≤ x ∧ ∀ k : Fin n, c < k → k.val ≤ x → k ∉ S := by
    intro x
    induction x with
    | zero =>
      intro hx
      refine ⟨⟨0, hx⟩, hS0 _ rfl, le_rfl, fun k hk hk' => ?_⟩
      rw [Fin.lt_def] at hk
      simp only at hk
      omega
    | succ x ih =>
      intro hx
      by_cases hmem : (⟨x + 1, hx⟩ : Fin n) ∈ S
      · refine ⟨⟨x + 1, hx⟩, hmem, le_rfl, fun k hk hk' => ?_⟩
        rw [Fin.lt_def] at hk
        simp only at hk
        omega
      · obtain ⟨c, hc, hcx, hck⟩ := ih (by omega)
        refine ⟨c, hc, by omega, fun k hk hk' => ?_⟩
        by_cases hkx : k.val ≤ x
        · exact hck k hk hkx
        · have hk1 : k = ⟨x + 1, hx⟩ := Fin.ext (by simp only; omega)
          rw [hk1]
          exact hmem
  have hQcard : n ≤ Q.card := by
    have hsurj : Set.SurjOn (fun p : Fin n × Fin n => p.1.val + p.2.val) Q
        (Finset.range n : Finset ℕ) := by
      intro x hx
      have hx : x < n := Finset.mem_range.mp hx
      obtain ⟨c, hc, hcx, hck⟩ := hex x hx
      have hsum : c.val + (x - c.val) = x := by omega
      refine ⟨(c, ⟨x - c.val, by omega⟩), ?_, hsum⟩
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨hc, Finset.mem_univ _⟩, by simp only; omega,
        fun k hk hk' => hck k hk (by simp only at hk'; omega)⟩
    have hle := Finset.card_le_card_of_surjOn _ hsurj
    rwa [Finset.card_range] at hle
  have hPcard : P.card + n ≤ n * S.card := by
    have hsub : Q ⊆ S ×ˢ Finset.univ := Finset.filter_subset _ _
    have hadd : P.card + Q.card = (S ×ˢ (Finset.univ : Finset (Fin n))).card :=
      Finset.card_sdiff_add_card_eq_card hsub
    rw [Finset.card_product, Finset.card_univ, Fintype.card_fin, mul_comm] at hadd
    omega
  -- an element of `𝒳'` is determined by its column `0` and its entries in `P`
  let Ψ : 𝒳' →ₗ[F] (Fin n → F) × (P → F) :=
    { toFun := fun X => (fun i => (X : Matrix (Fin n) (Fin n) F) i ⟨0, i.pos⟩,
        fun p => (X : Matrix (Fin n) (Fin n) F) p.1.1 p.1.2)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective Ψ := by
    rw [injective_iff_map_eq_zero]
    intro X hΨ
    obtain ⟨hX𝒳, hTX⟩ := Submodule.mem_inf.mp X.2
    have hTX' : truncShift (X : Matrix (Fin n) (Fin n) F) ∈ 𝒳 := hTX
    have hcol : ∀ i j : Fin n, j.val = 0 → (X : Matrix (Fin n) (Fin n) F) i j = 0 := by
      intro i j hj
      have h1 : (X : Matrix (Fin n) (Fin n) F) i ⟨0, i.pos⟩ = 0 :=
        congrFun (congrArg Prod.fst hΨ) i
      rwa [show (⟨0, i.pos⟩ : Fin n) = j from Fin.ext hj.symm] at h1
    have hP : ∀ p ∈ P, (X : Matrix (Fin n) (Fin n) F) p.1 p.2 = 0 := fun p hp =>
      congrFun (congrArg Prod.snd hΨ) ⟨p, hp⟩
    -- consecutive rows of one band are shifts of one another
    have hA : ∀ c c' : Fin n, c'.val = c.val + 1 → c' ∉ S → ∀ r : Fin n,
        (X : Matrix (Fin n) (Fin n) F) c' r =
          if hr : r.val + 1 < n then (X : Matrix (Fin n) (Fin n) F) c ⟨r.val + 1, hr⟩ else 0 :=
      fun c c' hcc' hc' r =>
        congrFun (h.row_succ_eq hX𝒳 hTX' hcol hcc' (hS c c' hcc' hc')) r
    -- the entries in `Q` vanish: walk down the anti-diagonal to column `0`
    have hB : ∀ t : ℕ, ∀ c r : Fin n, r.val = t → c.val + t < n →
        (∀ k : Fin n, c < k → k.val ≤ c.val + t → k ∉ S) →
        (X : Matrix (Fin n) (Fin n) F) c r = 0 := by
      intro t
      induction t with
      | zero => exact fun c r hr _ _ => hcol c r hr
      | succ t ih =>
        intro c r hr hlt hk
        have hc'lt : c.val + 1 < n := by omega
        have hc'S : (⟨c.val + 1, hc'lt⟩ : Fin n) ∉ S :=
          hk _ (by rw [Fin.lt_def]; simp only; omega) (by simp only; omega)
        have hrt : t < n := by omega
        have hstep := hA c ⟨c.val + 1, hc'lt⟩ rfl hc'S ⟨t, hrt⟩
        have ht1 : t + 1 < n := by omega
        rw [dite_eq_left ht1, show (⟨t + 1, ht1⟩ : Fin n) = r from Fin.ext hr.symm] at hstep
        rw [← hstep]
        refine ih ⟨c.val + 1, hc'lt⟩ ⟨t, hrt⟩ rfl (by simp only; omega) fun k hk1 hk2 => ?_
        rw [Fin.lt_def] at hk1
        simp only at hk1 hk2
        exact hk k (by rw [Fin.lt_def]; omega) (by omega)
    -- the first row of every band vanishes
    have hC : ∀ c ∈ S, ∀ r : Fin n, (X : Matrix (Fin n) (Fin n) F) c r = 0 := by
      intro c hc r
      by_cases hq : (c, r) ∈ Q
      · obtain ⟨-, hlt, hk⟩ := Finset.mem_filter.mp hq
        exact hB r.val c r rfl hlt hk
      · exact hP (c, r) (Finset.mem_sdiff.mpr
          ⟨Finset.mem_product.mpr ⟨hc, Finset.mem_univ _⟩, hq⟩)
    -- every row vanishes
    have hD : ∀ t : ℕ, ∀ c : Fin n, c.val = t → (X : Matrix (Fin n) (Fin n) F) c = 0 := by
      intro t
      induction t with
      | zero => exact fun c hc => funext (hC c (hS0 c hc))
      | succ t ih =>
        intro c hc
        by_cases hcS : c ∈ S
        · exact funext (hC c hcS)
        · have htn : t < n := by omega
          funext r
          rw [hA ⟨t, htn⟩ c hc hcS r]
          by_cases hr : r.val + 1 < n
          · rw [dite_eq_left hr, ih ⟨t, htn⟩ rfl]
            rfl
          · rw [dite_eq_right hr]
            rfl
    apply Subtype.ext
    funext c
    exact hD c.val c rfl
  have hdim : finrank F 𝒳' ≤ n + P.card := by
    have hle := LinearMap.finrank_le_finrank_of_injective hinj
    rwa [Module.finrank_prod, Module.finrank_fintype_fun_eq_card,
      Module.finrank_fintype_fun_eq_card, Fintype.card_fin, Fintype.card_coe] at hle
  rw [pow_two]
  omega

end IsLineUniformCode

end SwapRigidity
