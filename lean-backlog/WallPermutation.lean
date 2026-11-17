import WallBipartite

/-!
# Permutation hosts

On a square index set the helper rows of the columns may be taken to be `w` permutations:
column `a` reads rows `σ i a` (`i < w`), row `b` reads columns `(σ i).symm b`. Every symmetric
host of degree at most `w` is contained in such a permutation host (`exists_perm_cover`, via the
regular completion of a bipartite multigraph and an integer form of Birkhoff's theorem), so the
bipartite bound and the permutation bound are the same statement
(`bipartiteBoundAt_iff_permutationBoundAt`), and so are the three criteria built from them.
-/

namespace LeanBacklog.WallPermutation

open Finset Transpose Transpose.Tape Transpose.Tape.Impl
open LeanBacklog.RowSpread LeanBacklog.BlockTCC LeanBacklog.WallFarCells
open LeanBacklog.WallBipartite

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Matrices with bounded line sums -/

/-- If all row sums and all column sums of `M` equal `w`, there are `w` permutations whose
graphs cover the support of `M` (integer Birkhoff theorem). -/
theorem exists_perms_of_regular {N : ℕ} :
    ∀ (w : ℕ) (M : Fin N → Fin N → ℕ), (∀ a, ∑ b, M a b = w) → (∀ b, ∑ a, M a b = w) →
      ∃ σ : Fin w → Equiv.Perm (Fin N), ∀ a b, 0 < M a b → ∃ i, σ i a = b := by
  intro w
  induction w with
  | zero =>
    intro M hrow _
    refine ⟨fun i => i.elim0, fun a b hab => ?_⟩
    have h0 := (Finset.sum_eq_zero_iff.mp (hrow a)) b (mem_univ b)
    omega
  | succ w ih =>
    intro M hrow hcol
    classical
    let t : Fin N → Finset (Fin N) := fun a => univ.filter fun b => 0 < M a b
    have hhall : ∀ S : Finset (Fin N), S.card ≤ (S.biUnion t).card := by
      intro S
      set U := S.biUnion t with hU
      have h1 : ∀ a ∈ S, ∑ b ∈ U, M a b = w + 1 := by
        intro a ha
        rw [← hrow a]
        apply Finset.sum_subset (subset_univ U)
        intro b _ hb
        by_contra hne
        apply hb
        exact mem_biUnion.mpr ⟨a, ha, by simp [t]; omega⟩
      have h2 : (w + 1) * S.card ≤ (w + 1) * U.card := by
        calc (w + 1) * S.card = ∑ a ∈ S, ∑ b ∈ U, M a b := by
              rw [Finset.sum_congr rfl h1]; simp [mul_comm]
          _ ≤ ∑ a, ∑ b ∈ U, M a b :=
              Finset.sum_le_sum_of_subset_of_nonneg (subset_univ S) (fun _ _ _ => Nat.zero_le _)
          _ = ∑ b ∈ U, ∑ a, M a b := Finset.sum_comm
          _ = (w + 1) * U.card := by
              rw [Finset.sum_congr rfl (fun b _ => hcol b)]; simp [mul_comm]
      exact Nat.le_of_mul_le_mul_left h2 (Nat.succ_pos w)
    obtain ⟨f, hf, hft⟩ := (all_card_le_biUnion_card_iff_exists_injective t).1 hhall
    have hbij : Function.Bijective f := Finite.injective_iff_bijective.mp hf
    let π : Equiv.Perm (Fin N) := Equiv.ofBijective f hbij
    have hπ : ∀ a, π a = f a := fun a => rfl
    have hpos : ∀ a, 0 < M a (π a) := by
      intro a
      have := hft a
      simp only [t, mem_filter, mem_univ, true_and] at this
      rw [hπ]; exact this
    let M₂ : Fin N → Fin N → ℕ := fun a b => M a b - (if π a = b then 1 else 0)
    have hsplit : ∀ a b, M₂ a b + (if π a = b then 1 else 0) = M a b := by
      intro a b
      simp only [M₂]
      split_ifs with h
      · have := hpos a; rw [h] at this; omega
      · omega
    have hrow₂ : ∀ a, ∑ b, M₂ a b = w := by
      intro a
      have hs : ∑ b, (M₂ a b + (if π a = b then 1 else 0)) = w + 1 := by
        rw [← hrow a]; exact Finset.sum_congr rfl (fun b _ => hsplit a b)
      rw [Finset.sum_add_distrib] at hs
      simp only [Finset.sum_ite_eq, mem_univ, ↓reduceIte] at hs
      omega
    have hcol₂ : ∀ b, ∑ a, M₂ a b = w := by
      intro b
      have hs : ∑ a, (M₂ a b + (if π a = b then 1 else 0)) = w + 1 := by
        rw [← hcol b]; exact Finset.sum_congr rfl (fun a _ => hsplit a b)
      rw [Finset.sum_add_distrib] at hs
      have hind : ∑ a, (if π a = b then 1 else 0 : ℕ) = 1 := by
        have : ∀ a, (π a = b) ↔ (a = π.symm b) := fun a => (Equiv.eq_symm_apply π).symm
        simp only [this, Finset.sum_ite_eq', mem_univ, ↓reduceIte]
      rw [hind] at hs
      omega
    obtain ⟨σ', hσ'⟩ := ih M₂ hrow₂ hcol₂
    refine ⟨Fin.cons (α := fun _ => Equiv.Perm (Fin N)) π σ', fun a b hab => ?_⟩
    by_cases h : π a = b
    · exact ⟨0, by simpa using h⟩
    · have hM₂ : 0 < M₂ a b := by
        have := hsplit a b
        simp only [h, ↓reduceIte] at this
        omega
      obtain ⟨i, hi⟩ := hσ' a b hM₂
      exact ⟨i.succ, by simpa using hi⟩

/-- Regular completion: a matrix with all line sums at most `w` lies below one with all line sums
equal to `w`. The argument `t` bounds the missing total mass. -/
theorem exists_regular_above {N w : ℕ} :
    ∀ (t : ℕ) (M : Fin N → Fin N → ℕ), (∀ a, ∑ b, M a b ≤ w) → (∀ b, ∑ a, M a b ≤ w) →
      N * w ≤ (∑ a, ∑ b, M a b) + t →
      ∃ M' : Fin N → Fin N → ℕ, (∀ a b, M a b ≤ M' a b) ∧
        (∀ a, ∑ b, M' a b = w) ∧ (∀ b, ∑ a, M' a b = w) := by
  classical
  -- If all lines are full on one side, they are full on both.
  have htotal_rows : ∀ M : Fin N → Fin N → ℕ, (∀ a, ∑ b, M a b ≤ w) →
      (∃ a, ∑ b, M a b < w) → (∑ a, ∑ b, M a b) < N * w := by
    intro M hle ⟨a, ha⟩
    calc (∑ a, ∑ b, M a b) < ∑ _a : Fin N, w :=
          Finset.sum_lt_sum (fun a _ => hle a) ⟨a, mem_univ a, ha⟩
      _ = N * w := by simp
  have htotal_cols : ∀ M : Fin N → Fin N → ℕ, (∀ b, ∑ a, M a b ≤ w) →
      (∃ b, ∑ a, M a b < w) → (∑ a, ∑ b, M a b) < N * w := by
    intro M hle ⟨b, hb⟩
    rw [Finset.sum_comm]
    calc (∑ b, ∑ a, M a b) < ∑ _b : Fin N, w :=
          Finset.sum_lt_sum (fun b _ => hle b) ⟨b, mem_univ b, hb⟩
      _ = N * w := by simp
  intro t
  induction t with
  | zero =>
    intro M hrow hcol htot
    refine ⟨M, fun _ _ => le_rfl, fun a => ?_, fun b => ?_⟩
    · by_contra hne
      have := htotal_rows M hrow ⟨a, lt_of_le_of_ne (hrow a) hne⟩
      omega
    · by_contra hne
      have := htotal_cols M hcol ⟨b, lt_of_le_of_ne (hcol b) hne⟩
      omega
  | succ t ih =>
    intro M hrow hcol htot
    by_cases hfull : (∀ a, ∑ b, M a b = w) ∧ (∀ b, ∑ a, M a b = w)
    · exact ⟨M, fun _ _ => le_rfl, hfull.1, hfull.2⟩
    have hlt : (∑ a, ∑ b, M a b) < N * w := by
      rcases not_and_or.mp hfull with h | h
      · push Not at h
        obtain ⟨a, ha⟩ := h
        exact htotal_rows M hrow ⟨a, lt_of_le_of_ne (hrow a) ha⟩
      · push Not at h
        obtain ⟨b, hb⟩ := h
        exact htotal_cols M hcol ⟨b, lt_of_le_of_ne (hcol b) hb⟩
    have hra : ∃ a, ∑ b, M a b < w := by
      by_contra hno
      push Not at hno
      have : ∀ a, ∑ b, M a b = w := fun a => le_antisymm (hrow a) (hno a)
      have heq : (∑ a, ∑ b, M a b) = N * w := by simp [this]
      omega
    have hcb : ∃ b, ∑ a, M a b < w := by
      by_contra hno
      push Not at hno
      have : ∀ b, ∑ a, M a b = w := fun b => le_antisymm (hcol b) (hno b)
      have heq : (∑ a, ∑ b, M a b) = N * w := by rw [Finset.sum_comm]; simp [this]
      omega
    obtain ⟨a₀, ha₀⟩ := hra
    obtain ⟨b₀, hb₀⟩ := hcb
    let M₁ : Fin N → Fin N → ℕ := fun a b => M a b + (if a = a₀ ∧ b = b₀ then 1 else 0)
    have hrow₁ : ∀ a, ∑ b, M₁ a b = ∑ b, M a b + (if a = a₀ then 1 else 0) := by
      intro a
      simp only [M₁, Finset.sum_add_distrib]
      congr 1
      by_cases h : a = a₀
      · simp [h]
      · simp [h]
    have hcol₁ : ∀ b, ∑ a, M₁ a b = ∑ a, M a b + (if b = b₀ then 1 else 0) := by
      intro b
      simp only [M₁, Finset.sum_add_distrib]
      congr 1
      by_cases h : b = b₀
      · simp [h]
      · simp [h]
    have htot₁ : (∑ a, ∑ b, M₁ a b) = (∑ a, ∑ b, M a b) + 1 := by
      rw [Finset.sum_congr rfl (fun a _ => hrow₁ a), Finset.sum_add_distrib]
      simp
    obtain ⟨M', hle, hr', hc'⟩ := ih M₁
      (fun a => by
        rw [hrow₁]
        by_cases h : a = a₀
        · simp only [h, ↓reduceIte]; subst h; omega
        · simp only [h, ↓reduceIte, Nat.add_zero]; exact hrow a)
      (fun b => by
        rw [hcol₁]
        by_cases h : b = b₀
        · simp only [h, ↓reduceIte]; subst h; omega
        · simp only [h, ↓reduceIte, Nat.add_zero]; exact hcol b)
      (by rw [htot₁]; omega)
    exact ⟨M', fun a b => le_trans (Nat.le_add_right _ _) (hle a b), hr', hc'⟩

/-! ## Permutation hosts -/

/-- The host given by `w` permutations: column `a` reads rows `σ i a`. -/
def permCol {N w : ℕ} (σ : Fin w → Equiv.Perm (Fin N)) (a : Fin N) : Finset (Fin N) :=
  univ.image fun i => σ i a

/-- The host given by `w` permutations: row `b` reads columns `(σ i).symm b`. -/
def permRow {N w : ℕ} (σ : Fin w → Equiv.Perm (Fin N)) (b : Fin N) : Finset (Fin N) :=
  univ.image fun i => (σ i).symm b

theorem card_permCol_le {N w : ℕ} (σ : Fin w → Equiv.Perm (Fin N)) (a : Fin N) :
    (permCol σ a).card ≤ w := by
  unfold permCol
  exact card_image_le.trans (by simp)

theorem card_permRow_le {N w : ℕ} (σ : Fin w → Equiv.Perm (Fin N)) (b : Fin N) :
    (permRow σ b).card ≤ w := by
  unfold permRow
  exact card_image_le.trans (by simp)

theorem mem_permCol_iff_mem_permRow {N w : ℕ} (σ : Fin w → Equiv.Perm (Fin N)) (a b : Fin N) :
    b ∈ permCol σ a ↔ a ∈ permRow σ b := by
  simp only [permCol, permRow, mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩; exact ⟨i, by simp⟩
  · rintro ⟨i, rfl⟩; exact ⟨i, by simp⟩

/-- **Covering lemma.** Every symmetric host on `Fin N × Fin N` with all degrees at most `w` is
contained in a host given by `w` permutations. -/
theorem exists_perm_cover {N w : ℕ} (H_col H_row : Fin N → Finset (Fin N))
    (hcol : ∀ a, (H_col a).card ≤ w) (hrow : ∀ b, (H_row b).card ≤ w)
    (hsym : ∀ a b, b ∈ H_col a ↔ a ∈ H_row b) :
    ∃ σ : Fin w → Equiv.Perm (Fin N),
      (∀ a, H_col a ⊆ permCol σ a) ∧ (∀ b, H_row b ⊆ permRow σ b) := by
  classical
  let M : Fin N → Fin N → ℕ := fun a b => if b ∈ H_col a then 1 else 0
  have hrowM : ∀ a, ∑ b, M a b ≤ w := by
    intro a
    have : ∑ b, M a b = (H_col a).card := by
      simp only [M, Finset.sum_boole, Nat.cast_id]
      congr 1; ext b; simp
    rw [this]; exact hcol a
  have hcolM : ∀ b, ∑ a, M a b ≤ w := by
    intro b
    have : ∑ a, M a b = (H_row b).card := by
      simp only [M, Finset.sum_boole, Nat.cast_id, hsym]
      congr 1; ext a; simp
    rw [this]; exact hrow b
  obtain ⟨M', hle, hr', hc'⟩ := exists_regular_above (N * w) M hrowM hcolM (by omega)
  obtain ⟨σ, hσ⟩ := exists_perms_of_regular w M' hr' hc'
  have hcov : ∀ a, H_col a ⊆ permCol σ a := by
    intro a b hb
    have h1 : 0 < M a b := by simp [M, hb]
    obtain ⟨i, hi⟩ := hσ a b (lt_of_lt_of_le h1 (hle a b))
    simp only [permCol, mem_image, mem_univ, true_and]
    exact ⟨i, hi⟩
  refine ⟨σ, hcov, fun b a ha => ?_⟩
  rw [← mem_permCol_iff_mem_permRow]
  exact hcov a ((hsym a b).mpr ha)

/-! ## The permutation bound -/

/-- Every two-sided code on every host given by `w` permutations of `Fin N` has at most
`|α| ^ v` words. -/
def PermutationBoundAt (α : Type*) [Fintype α] (N w : ℕ) (v : ℝ) : Prop :=
  ∀ (σ : Fin w → Equiv.Perm (Fin N)) (D : Finset (Fin N × Fin N → α)),
    IsBipartiteTwoSidedCode (permCol σ) (permRow σ) D →
      (D.card : ℝ) ≤ (Fintype.card α : ℝ) ^ v

theorem permutationBoundAt_of_bipartiteBoundAt {α : Type*} [Fintype α] {N w : ℕ} {v : ℝ}
    (h : BipartiteBoundAt α N N w v) : PermutationBoundAt α N w v :=
  fun σ D hD => h (permCol σ) (permRow σ) D (card_permCol_le σ) (card_permRow_le σ)
    (mem_permCol_iff_mem_permRow σ) hD

theorem bipartiteBoundAt_of_permutationBoundAt {α : Type*} [Fintype α] {N w : ℕ} {v : ℝ}
    (h : PermutationBoundAt α N w v) : BipartiteBoundAt α N N w v := by
  intro H_col H_row D hcol hrow hsym hD
  obtain ⟨σ, hc, hr⟩ := exists_perm_cover H_col H_row hcol hrow hsym
  exact h σ D (IsBipartiteTwoSidedCode.mono_host hD hc hr)

/-- **The bipartite bound and the permutation bound are the same statement.** -/
theorem bipartiteBoundAt_iff_permutationBoundAt {α : Type*} [Fintype α] {N w : ℕ} {v : ℝ} :
    BipartiteBoundAt α N N w v ↔ PermutationBoundAt α N w v :=
  ⟨permutationBoundAt_of_bipartiteBoundAt, bipartiteBoundAt_of_permutationBoundAt⟩

/-- The licences on permutation hosts: the prover may assume no sparse cut and pin at most `e`
cells. -/
theorem permutationBoundAt_of_licences {α : Type*} [Fintype α] [Nonempty α] {N w e : ℕ}
    {v Δ₀ : ℝ}
    (h : ∀ σ : Fin w → Equiv.Perm (Fin N), NoSparseCut Δ₀ (permCol σ) (permRow σ) →
      ∃ E : Finset (Fin N × Fin N), E.card ≤ e ∧
        ∀ D : Finset (Fin N × Fin N → α), IsPinnedBipartiteTwoSidedCode (permCol σ) (permRow σ) E D →
          (D.card : ℝ) ≤ (Fintype.card α : ℝ) ^ v) :
    PermutationBoundAt α N w (max (v + e) ((N * N : ℝ) - Δ₀)) :=
  fun σ D hD => bipartite_card_le_of_licence_host (permCol σ) (permRow σ) (h σ) D hD

/-! ## The criteria in permutation form -/

def PermutationCriterion : Prop :=
  ∀ k G c : ℕ, 5 ≤ k → 1 ≤ G → 4 ≤ c → ∀ d₀ : ℕ,
    ∃ (d R : ℕ) (θ δ : ℝ), max d₀ 1 ≤ d ∧ 0 < θ ∧
      PermutationBoundAt (Fin (entryBits d) → Bool) d (endWindow k G θ+R+1) ((1-δ)*(d:ℝ)^2) ∧
      (2*(adaptiveAllowance k G c*d+cutBudget k G c d θ):ℕ) +
        (entryBits d*crossBudget d (endWindow k G θ) R:ℕ) <
          δ*(d*d*entryBits d:ℕ)

def WindowwisePermutationCriterion : Prop :=
  ∀ k G c : ℕ, 5 ≤ k → 1 ≤ G → 4 ≤ c →
    ∃ (R : ℕ) (θ δ : ℝ), 0 < θ ∧ budgetRate k G c θ R < δ ∧
      ∀ d₀ : ℕ, ∃ d ≥ d₀,
        PermutationBoundAt (Fin (entryBits d) → Bool) d (endWindow k G θ+R+1) ((1-δ)*(d:ℝ)^2)

def UniformPermutationRateCanonicalBits (rate : ℝ) : Prop :=
  ∀ (w : ℕ) (η : ℝ), 0 < η → ∃ d₀ : ℕ, ∀ d ≥ d₀,
    PermutationBoundAt (Fin (entryBits d) → Bool) d w ((rate + η) * (d : ℝ) ^ 2)

def PermutationCommonDeficit : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ UniformPermutationRateCanonicalBits (1 - δ)

theorem permutationCriterion_iff : PermutationCriterion ↔ BipartiteCriterion := by
  unfold PermutationCriterion BipartiteCriterion
  simp only [bipartiteBoundAt_iff_permutationBoundAt]

theorem windowwisePermutationCriterion_iff :
    WindowwisePermutationCriterion ↔ WindowwiseBipartiteCriterion := by
  unfold WindowwisePermutationCriterion WindowwiseBipartiteCriterion
  simp only [bipartiteBoundAt_iff_permutationBoundAt]

theorem uniformPermutationRate_iff (rate : ℝ) :
    UniformPermutationRateCanonicalBits rate ↔ UniformBipartiteRateCanonicalBits rate := by
  unfold UniformPermutationRateCanonicalBits UniformBipartiteRateCanonicalBits
  simp only [bipartiteBoundAt_iff_permutationBoundAt]

theorem permutationCommonDeficit_iff_bipartite :
    PermutationCommonDeficit ↔ BipartiteCommonDeficit := by
  unfold PermutationCommonDeficit BipartiteCommonDeficit
  simp only [uniformPermutationRate_iff]

/-- **The permutation common deficit is the common deficit.** -/
theorem permutationCommonDeficit_iff_commonDeficit :
    PermutationCommonDeficit ↔ LeanBacklog.Wall.CommonDeficit :=
  permutationCommonDeficit_iff_bipartite.trans bipartiteCommonDeficit_iff_commonDeficit

theorem conjecture_of_permutationCriterion (h : PermutationCriterion) :
    LeanBacklog.Wall.Conjecture :=
  conjecture_of_bipartiteCriterion (permutationCriterion_iff.mp h)

theorem conjecture_of_windowwisePermutationCriterion (h : WindowwisePermutationCriterion) :
    LeanBacklog.Wall.Conjecture :=
  conjecture_of_windowwiseBipartiteCriterion (windowwisePermutationCriterion_iff.mp h)

theorem conjecture_of_permutationCommonDeficit (h : PermutationCommonDeficit) :
    LeanBacklog.Wall.Conjecture :=
  LeanBacklog.Wall.of_commonDeficit (permutationCommonDeficit_iff_commonDeficit.mp h)

#print axioms exists_perms_of_regular
#print axioms exists_regular_above
#print axioms card_permCol_le
#print axioms card_permRow_le
#print axioms mem_permCol_iff_mem_permRow
#print axioms exists_perm_cover
#print axioms bipartiteBoundAt_iff_permutationBoundAt
#print axioms permutationBoundAt_of_licences
#print axioms permutationCriterion_iff
#print axioms windowwisePermutationCriterion_iff
#print axioms uniformPermutationRate_iff
#print axioms permutationCommonDeficit_iff_bipartite
#print axioms permutationCommonDeficit_iff_commonDeficit
#print axioms conjecture_of_permutationCriterion
#print axioms conjecture_of_windowwisePermutationCriterion
#print axioms conjecture_of_permutationCommonDeficit

end LeanBacklog.WallPermutation
