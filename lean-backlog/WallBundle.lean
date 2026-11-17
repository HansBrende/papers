import WallPermutation
import WallFarShannon
import MotionDepthCodes.StorageCode

/-!
# The bundle form of the bipartite bound

The vertices of a bipartite host between `n` rows and `m` columns are `Fin m ⊕ Fin n`
(`Sum.inl a` is column `a`, `Sum.inr b` is row `b`). For a code `D` and a set `S` of vertices,
let `g S` be the entropy, in units of `log |α|`, of all cells that lie in a column of `S` or
in a row of `S`. Then `g` is a polymatroid on the vertices, adding a vertex gains at most its
new cells, and a vertex adds nothing to its own neighbourhood (`IsBundleAdmissible`). So a
bound on all such functions bounds every code (`bipartiteBoundAt_of_bundleBoundAt`), and one
deficit for all such functions implies the conjecture (`conjecture_of_bundleCommonDeficit`).

On permutation hosts the bound is the same statement (`bundleBoundAt_iff_permutation`). On the
complete host the cell count is admissible and has full value, so a bound below `n ^ 2` needs
the size to exceed the degree (`sq_le_of_bundleBoundAt_of_le`).

Nothing here asserts any of these hypotheses.
-/

namespace LeanBacklog.WallBundle

open Finset Transpose Transpose.Tape Transpose.Tape.Impl
open LeanBacklog.RowSpread LeanBacklog.BlockTCC LeanBacklog.WallFarCells
open LeanBacklog.WallBipartite LeanBacklog.WallPermutation LeanBacklog.WallFarShannon

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Definitions -/

/-- The neighbours of a vertex, as a set of vertices: a column's helper rows, a row's helper
columns. -/
def nbrs {n m : ℕ} (H_col : Fin m → Finset (Fin n)) (H_row : Fin n → Finset (Fin m)) :
    Fin m ⊕ Fin n → Finset (Fin m ⊕ Fin n)
  | Sum.inl a => (H_col a).map ⟨Sum.inr, Sum.inr_injective⟩
  | Sum.inr b => (H_row b).map ⟨Sum.inl, Sum.inl_injective⟩

/-- The number of cells of the vertex `v` that touch no vertex of `K`: a column has `n` cells,
one in each row; a row has `m` cells, one in each column. -/
def newCells {n m : ℕ} (K : Finset (Fin m ⊕ Fin n)) : Fin m ⊕ Fin n → ℕ
  | Sum.inl _ => n - (K.filter fun u => u.isRight).card
  | Sum.inr _ => m - (K.filter fun u => u.isLeft).card

/-- Admissible functions on the vertex sets of a host. -/
structure IsBundleAdmissible {n m : ℕ} (H_col : Fin m → Finset (Fin n))
    (H_row : Fin n → Finset (Fin m)) (g : Finset (Fin m ⊕ Fin n) → ℝ) : Prop where
  poly : MotionDepthCodes.IsPolymatroid g
  cap : ∀ (K : Finset (Fin m ⊕ Fin n)) (v : Fin m ⊕ Fin n), v ∉ K →
    g (insert v K) - g K ≤ (newCells K v : ℝ)
  recover : MotionDepthCodes.IsValid g (nbrs H_col H_row)

/-- Every admissible function on every host of maximum degree `w` has total value at most
`v`. -/
def BundleBoundAt (n m w : ℕ) (v : ℝ) : Prop :=
  ∀ (H_col : Fin m → Finset (Fin n)) (H_row : Fin n → Finset (Fin m)),
    (∀ a, (H_col a).card ≤ w) → (∀ b, (H_row b).card ≤ w) →
    (∀ a b, b ∈ H_col a ↔ a ∈ H_row b) →
    ∀ g, IsBundleAdmissible H_col H_row g → g univ ≤ v

/-- **The bundle hypothesis.** One deficit `δ` for every degree bound and all large sizes. -/
def BundleCommonDeficit : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ w : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀, BundleBoundAt n n w ((1 - δ) * (n : ℝ) ^ 2)

/-- The cells that lie in a column of `S` or in a row of `S`. -/
def cellsOf {n m : ℕ} (S : Finset (Fin m ⊕ Fin n)) : Finset (Fin n × Fin m) :=
  univ.filter fun p => Sum.inr p.1 ∈ S ∨ Sum.inl p.2 ∈ S

/-- Helper cells of the cell `p = (b, a)` for its column: the cells of the helper rows of
`a`. -/
def colHelpers {n m : ℕ} (H_col : Fin m → Finset (Fin n)) (p : Fin n × Fin m) :
    Finset (Fin n × Fin m) :=
  univ.filter fun c => c.1 ∈ H_col p.2

/-- Helper cells of the cell `p = (b, a)` for its row: the cells of the helper columns of
`b`. -/
def rowHelpers {n m : ℕ} (H_row : Fin n → Finset (Fin m)) (p : Fin n × Fin m) :
    Finset (Fin n × Fin m) :=
  univ.filter fun c => c.2 ∈ H_row p.1

/-! ## Cells of vertex sets -/

section Cells

variable {n m : ℕ}

theorem mem_cellsOf {S : Finset (Fin m ⊕ Fin n)} {p : Fin n × Fin m} :
    p ∈ cellsOf S ↔ Sum.inr p.1 ∈ S ∨ Sum.inl p.2 ∈ S := by
  simp [cellsOf]

theorem cellsOf_union (S T : Finset (Fin m ⊕ Fin n)) :
    cellsOf (S ∪ T) = cellsOf S ∪ cellsOf T := by
  ext p
  simp only [mem_cellsOf, mem_union]
  tauto

theorem cellsOf_inter_subset (S T : Finset (Fin m ⊕ Fin n)) :
    cellsOf (S ∩ T) ⊆ cellsOf S ∩ cellsOf T := by
  intro p hp
  simp only [mem_cellsOf, mem_inter] at hp ⊢
  tauto

theorem cellsOf_mono {S T : Finset (Fin m ⊕ Fin n)} (h : S ⊆ T) : cellsOf S ⊆ cellsOf T := by
  intro p hp
  rw [mem_cellsOf] at hp ⊢
  rcases hp with hp | hp
  · exact Or.inl (h hp)
  · exact Or.inr (h hp)

theorem cellsOf_empty : cellsOf (∅ : Finset (Fin m ⊕ Fin n)) = ∅ := by
  ext p
  simp [mem_cellsOf]

theorem cellsOf_univ : cellsOf (univ : Finset (Fin m ⊕ Fin n)) = univ := by
  ext p
  simp [mem_cellsOf]

theorem card_filter_inr (K : Finset (Fin m ⊕ Fin n)) :
    (univ.filter fun b : Fin n => (Sum.inr b : Fin m ⊕ Fin n) ∈ K).card =
      (K.filter fun u => u.isRight).card := by
  rw [← card_map ⟨Sum.inr, Sum.inr_injective⟩]
  congr 1
  ext u
  cases u <;> simp

theorem card_filter_inl (K : Finset (Fin m ⊕ Fin n)) :
    (univ.filter fun a : Fin m => (Sum.inl a : Fin m ⊕ Fin n) ∈ K).card =
      (K.filter fun u => u.isLeft).card := by
  rw [← card_map ⟨Sum.inl, Sum.inl_injective⟩]
  congr 1
  ext u
  cases u <;> simp

/-- The cells of `v` outside the cells of `K` number at most `newCells K v`. -/
theorem card_sdiff_cellsOf_le (K : Finset (Fin m ⊕ Fin n)) (v : Fin m ⊕ Fin n) :
    (cellsOf {v} \ cellsOf K).card ≤ newCells K v := by
  cases v with
  | inl a =>
    have hsub : cellsOf {Sum.inl a} \ cellsOf K ⊆
        (univ.filter fun b : Fin n => (Sum.inr b : Fin m ⊕ Fin n) ∉ K).image
          (fun b => (b, a)) := by
      intro p hp
      simp only [mem_sdiff, mem_cellsOf, mem_singleton, Sum.inr_ne_inl, false_or,
        Sum.inl.injEq, not_or] at hp
      simp only [mem_image, mem_filter, mem_univ, true_and]
      exact ⟨p.1, hp.2.1, by rw [← hp.1]⟩
    have hc := card_filter_add_card_filter_not
      (s := (univ : Finset (Fin n))) (fun b : Fin n => (Sum.inr b : Fin m ⊕ Fin n) ∈ K)
    rw [card_filter_inr, card_univ, Fintype.card_fin] at hc
    calc (cellsOf {Sum.inl a} \ cellsOf K).card
        ≤ ((univ.filter fun b : Fin n => (Sum.inr b : Fin m ⊕ Fin n) ∉ K).image
            (fun b => (b, a))).card := card_le_card hsub
      _ ≤ (univ.filter fun b : Fin n => (Sum.inr b : Fin m ⊕ Fin n) ∉ K).card := card_image_le
      _ = newCells K (Sum.inl a) := by simp only [newCells]; omega
  | inr b =>
    have hsub : cellsOf {Sum.inr b} \ cellsOf K ⊆
        (univ.filter fun a : Fin m => (Sum.inl a : Fin m ⊕ Fin n) ∉ K).image
          (fun a => (b, a)) := by
      intro p hp
      simp only [mem_sdiff, mem_cellsOf, mem_singleton, Sum.inl_ne_inr, or_false,
        Sum.inr.injEq, not_or] at hp
      simp only [mem_image, mem_filter, mem_univ, true_and]
      exact ⟨p.2, hp.2.2, by rw [← hp.1]⟩
    have hc := card_filter_add_card_filter_not
      (s := (univ : Finset (Fin m))) (fun a : Fin m => (Sum.inl a : Fin m ⊕ Fin n) ∈ K)
    rw [card_filter_inl, card_univ, Fintype.card_fin] at hc
    calc (cellsOf {Sum.inr b} \ cellsOf K).card
        ≤ ((univ.filter fun a : Fin m => (Sum.inl a : Fin m ⊕ Fin n) ∉ K).image
            (fun a => (b, a))).card := card_le_card hsub
      _ ≤ (univ.filter fun a : Fin m => (Sum.inl a : Fin m ⊕ Fin n) ∉ K).card := card_image_le
      _ = newCells K (Sum.inr b) := by simp only [newCells]; omega

theorem newCells_le_empty (K : Finset (Fin m ⊕ Fin n)) (v : Fin m ⊕ Fin n) :
    newCells K v ≤ newCells (∅ : Finset (Fin m ⊕ Fin n)) v := by
  cases v <;> simp only [newCells, filter_empty, card_empty, Nat.sub_zero] <;> omega

theorem nbrs_mono {H_col H_col' : Fin m → Finset (Fin n)} {H_row H_row' : Fin n → Finset (Fin m)}
    (hc : ∀ a, H_col a ⊆ H_col' a) (hr : ∀ b, H_row b ⊆ H_row' b) (v : Fin m ⊕ Fin n) :
    nbrs H_col H_row v ⊆ nbrs H_col' H_row' v := by
  cases v with
  | inl a => exact map_subset_map.mpr (hc a)
  | inr b => exact map_subset_map.mpr (hr b)

theorem mem_cellsOf_nbrs_inl {H_col : Fin m → Finset (Fin n)} {H_row : Fin n → Finset (Fin m)}
    (a : Fin m) (p : Fin n × Fin m) :
    p ∈ cellsOf (nbrs H_col H_row (Sum.inl a)) ↔ p.1 ∈ H_col a := by
  simp [mem_cellsOf, nbrs]

theorem mem_cellsOf_insert_nbrs_inl {H_col : Fin m → Finset (Fin n)}
    {H_row : Fin n → Finset (Fin m)} (a : Fin m) (p : Fin n × Fin m) :
    p ∈ cellsOf (insert (Sum.inl a) (nbrs H_col H_row (Sum.inl a))) ↔
      p.2 = a ∨ p.1 ∈ H_col a := by
  simp [mem_cellsOf, nbrs]
  tauto

theorem mem_cellsOf_nbrs_inr {H_col : Fin m → Finset (Fin n)} {H_row : Fin n → Finset (Fin m)}
    (b : Fin n) (p : Fin n × Fin m) :
    p ∈ cellsOf (nbrs H_col H_row (Sum.inr b)) ↔ p.2 ∈ H_row b := by
  simp [mem_cellsOf, nbrs]

theorem mem_cellsOf_insert_nbrs_inr {H_col : Fin m → Finset (Fin n)}
    {H_row : Fin n → Finset (Fin m)} (b : Fin n) (p : Fin n × Fin m) :
    p ∈ cellsOf (insert (Sum.inr b) (nbrs H_col H_row (Sum.inr b))) ↔
      p.1 = b ∨ p.2 ∈ H_row b := by
  simp [mem_cellsOf, nbrs]

end Cells

/-! ## Sanity -/

/-- Sanity: the zero function is admissible. -/
theorem isBundleAdmissible_zero {n m : ℕ} (H_col : Fin m → Finset (Fin n))
    (H_row : Fin n → Finset (Fin m)) : IsBundleAdmissible H_col H_row (fun _ => 0) where
  poly := ⟨rfl, fun _ _ _ => le_refl _, fun _ _ => by norm_num⟩
  cap := fun _ _ _ => by simp
  recover := fun _ => rfl

/-- An admissible function grows at most by the new cells along any set. -/
theorem IsBundleAdmissible.le_sum_newCells {n m : ℕ} {H_col : Fin m → Finset (Fin n)}
    {H_row : Fin n → Finset (Fin m)} {g : Finset (Fin m ⊕ Fin n) → ℝ}
    (hg : IsBundleAdmissible H_col H_row g) (K : Finset (Fin m ⊕ Fin n)) :
    g K ≤ ∑ v ∈ K, (newCells (∅ : Finset (Fin m ⊕ Fin n)) v : ℝ) := by
  induction K using Finset.induction_on with
  | empty => simp [hg.poly.empty]
  | insert a K ha ih =>
    rw [sum_insert ha]
    have h1 := hg.cap K a ha
    have h2 : (newCells K a : ℝ) ≤ newCells (∅ : Finset (Fin m ⊕ Fin n)) a := by
      exact_mod_cast newCells_le_empty K a
    linarith

/-- Sanity: an admissible function has total value at most `n m`. -/
theorem IsBundleAdmissible.univ_le {n m : ℕ} {H_col : Fin m → Finset (Fin n)}
    {H_row : Fin n → Finset (Fin m)} {g : Finset (Fin m ⊕ Fin n) → ℝ}
    (hg : IsBundleAdmissible H_col H_row g) : g univ ≤ ((n * m : ℕ) : ℝ) := by
  set C : Finset (Fin m ⊕ Fin n) := univ.map ⟨Sum.inl, Sum.inl_injective⟩ with hC
  have hcl : g univ = g C := by
    apply hg.poly.eq_of_closure hg.recover (subset_univ C)
    intro v _ hv
    cases v with
    | inl a => exact absurd (by simp [hC]) hv
    | inr b =>
      intro u hu
      simp only [nbrs, mem_map] at hu
      obtain ⟨a, _, rfl⟩ := hu
      simp [hC]
  rw [hcl]
  calc g C ≤ ∑ v ∈ C, (newCells (∅ : Finset (Fin m ⊕ Fin n)) v : ℝ) := hg.le_sum_newCells C
    _ = ((n * m : ℕ) : ℝ) := by
      rw [hC, sum_map]
      simp [newCells, mul_comm]

/-- Sanity: an admissible function for a host is admissible for every larger host. -/
theorem IsBundleAdmissible.mono_host {n m : ℕ}
    {H_col H_col' : Fin m → Finset (Fin n)} {H_row H_row' : Fin n → Finset (Fin m)}
    {g : Finset (Fin m ⊕ Fin n) → ℝ} (hg : IsBundleAdmissible H_col H_row g)
    (hc : ∀ a, H_col a ⊆ H_col' a) (hr : ∀ b, H_row b ⊆ H_row' b) :
    IsBundleAdmissible H_col' H_row' g where
  poly := hg.poly
  cap := hg.cap
  recover := fun v => hg.poly.insert_eq_of_subset (nbrs_mono hc hr v) (hg.recover v)

/-! ## From cell polymatroids to bundle functions -/

theorem pinnedColHelpers_empty {n m : ℕ} (H_col : Fin m → Finset (Fin n)) :
    pinnedColHelpers H_col ∅ = colHelpers H_col := by
  funext p
  simp [pinnedColHelpers, colHelpers]

theorem pinnedRowHelpers_empty {n m : ℕ} (H_row : Fin n → Finset (Fin m)) :
    pinnedRowHelpers H_row ∅ = rowHelpers H_row := by
  funext p
  simp [pinnedRowHelpers, rowHelpers]

/-- A feasible cell polymatroid with no pinned cells, composed with `cellsOf`, is
admissible. -/
theorem isBundleAdmissible_of_farFeasible {n m : ℕ} {H_col : Fin m → Finset (Fin n)}
    {H_row : Fin n → Finset (Fin m)} {h : Finset (Fin n × Fin m) → ℝ}
    (hf : IsFarFeasible H_col H_row ∅ h) :
    IsBundleAdmissible H_col H_row (fun S => h (cellsOf S)) := by
  have hh := hf.poly
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · simp only [cellsOf_empty, hh.empty]
  · intro S T hST
    exact hh.mono (cellsOf_mono hST)
  · intro S T
    simp only [cellsOf_union]
    have h1 := hh.submod (cellsOf S) (cellsOf T)
    have h2 := hh.mono (cellsOf_inter_subset S T)
    linarith
  · intro K v _
    show h (cellsOf (insert v K)) - h (cellsOf K) ≤ _
    have hins : cellsOf (insert v K) = cellsOf K ∪ (cellsOf {v} \ cellsOf K) := by
      rw [insert_eq, cellsOf_union, union_sdiff_self_eq_union, union_comm]
    rw [hins]
    have h1 := hh.union_le (cellsOf K) (cellsOf {v} \ cellsOf K)
    have h2 := hh.le_sum_singleton (cellsOf {v} \ cellsOf K)
    have h3 : ∑ p ∈ cellsOf {v} \ cellsOf K, h {p} ≤
        ∑ _p ∈ cellsOf {v} \ cellsOf K, (1 : ℝ) := sum_le_sum fun p _ => hf.cap p
    have h4 : ((cellsOf {v} \ cellsOf K).card : ℝ) ≤ newCells K v := by
      exact_mod_cast card_sdiff_cellsOf_le K v
    simp only [sum_const, nsmul_eq_mul, mul_one] at h3
    linarith
  · intro v
    show h (cellsOf (insert v (nbrs H_col H_row v))) = h (cellsOf (nbrs H_col H_row v))
    cases v with
    | inl a =>
      apply hh.eq_of_closure hf.col (cellsOf_mono (subset_insert _ _))
      intro p hpT hpS c hc
      rw [pinnedColHelpers_empty] at hc
      simp only [colHelpers, mem_filter, mem_univ, true_and] at hc
      rw [mem_cellsOf_insert_nbrs_inl] at hpT
      rw [mem_cellsOf_nbrs_inl] at hpS ⊢
      rcases hpT with hpT | hpT
      · rw [← hpT]; exact hc
      · exact absurd hpT hpS
    | inr b =>
      apply hh.eq_of_closure hf.row (cellsOf_mono (subset_insert _ _))
      intro p hpT hpS c hc
      rw [pinnedRowHelpers_empty] at hc
      simp only [rowHelpers, mem_filter, mem_univ, true_and] at hc
      rw [mem_cellsOf_insert_nbrs_inr] at hpT
      rw [mem_cellsOf_nbrs_inr] at hpS ⊢
      rcases hpT with hpT | hpT
      · rw [← hpT]; exact hc
      · exact absurd hpT hpS


/-! ## The bridge from codes -/

/-- A bipartite two-sided code is a pinned code with no pinned cells. -/
theorem isPinned_empty_of_bipartite {n m : ℕ} {α : Type*}
    {H_col : Fin m → Finset (Fin n)} {H_row : Fin n → Finset (Fin m)}
    {D : Finset (Fin n × Fin m → α)} (hD : IsBipartiteTwoSidedCode H_col H_row D) :
    IsPinnedBipartiteTwoSidedCode H_col H_row ∅ D :=
  ⟨fun _ _ _ _ p hp => absurd hp (notMem_empty p),
    fun x hx y hy a hagree b => hD.1 x hx y hy a (fun b' hb' a' => hagree b' hb' a' (by simp)) b,
    fun x hx y hy b hagree a => hD.2 x hx y hy b (fun a' ha' b' => hagree a' ha' b' (by simp)) a⟩

/-- For any law on words recoverable from both helper maps, the bundle function of the
entropy, normalised by `log |α|`, is admissible. -/
theorem isBundleAdmissible_of_recoverable {n m : ℕ} {α : Type*} [Fintype α]
    (hα : 2 ≤ Fintype.card α)
    (H_col : Fin m → Finset (Fin n)) (H_row : Fin n → Finset (Fin m))
    {Ω : Type*} [Fintype Ω] (p : Ω → ℝ)
    (hp : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1) (X : Ω → Fin n × Fin m → α)
    (hcol : MotionDepthCodes.IsRecoverable (colHelpers H_col) X)
    (hrow : MotionDepthCodes.IsRecoverable (rowHelpers H_row) X) :
    IsBundleAdmissible H_col H_row (fun S =>
      MotionDepthCodes.codeEntropy p X (cellsOf S) / Real.log (Fintype.card α)) := by
  rw [← pinnedColHelpers_empty] at hcol
  rw [← pinnedRowHelpers_empty] at hrow
  exact isBundleAdmissible_of_farFeasible
    (isFarFeasible_of_recoverable hα H_col H_row ∅ p hp hp1 X hcol hrow)

/-- **The entropy of a code is admissible.** For a nonempty bipartite two-sided code over an
alphabet with at least two symbols, the entropy of the cells of a vertex set under the uniform
law, normalised by `log |α|`, is an admissible function. -/
theorem isBundleAdmissible_normalizedEntropy {n m : ℕ} {α : Type*} [Fintype α]
    (hα : 2 ≤ Fintype.card α)
    (H_col : Fin m → Finset (Fin n)) (H_row : Fin n → Finset (Fin m))
    (D : Finset (Fin n × Fin m → α)) (hD : IsBipartiteTwoSidedCode H_col H_row D)
    (hne : D.Nonempty) :
    IsBundleAdmissible H_col H_row (fun S =>
      MotionDepthCodes.codeEntropy (fun _ : D => ((D.card : ℝ))⁻¹)
        (fun x => (x : Fin n × Fin m → α)) (cellsOf S) / Real.log (Fintype.card α)) :=
  isBundleAdmissible_of_farFeasible
    (isFarFeasible_normalizedEntropy hα H_col H_row ∅ D (isPinned_empty_of_bipartite hD) hne)

/-- **Per-host bridge.** A bound `t` on every admissible function bounds every bipartite
two-sided code by `|α| ^ t`, over every nonempty finite alphabet. -/
theorem bipartite_card_le_of_bundle_bound {n m : ℕ} {α : Type*} [Fintype α] [Nonempty α]
    (H_col : Fin m → Finset (Fin n)) (H_row : Fin n → Finset (Fin m)) (t : ℝ)
    (hbound : ∀ g, IsBundleAdmissible H_col H_row g → g univ ≤ t)
    (D : Finset (Fin n × Fin m → α)) (hD : IsBipartiteTwoSidedCode H_col H_row D) :
    (D.card : ℝ) ≤ (Fintype.card α : ℝ) ^ t := by
  refine pinned_card_le_of_polymatroid_bound H_col H_row ∅ t (fun h hf => ?_) D
    (isPinned_empty_of_bipartite hD)
  have hb := hbound _ (isBundleAdmissible_of_farFeasible hf)
  rwa [cellsOf_univ] at hb

/-- **The bundle bound implies the bipartite bound** over every nonempty finite alphabet. -/
theorem bipartiteBoundAt_of_bundleBoundAt {n m w : ℕ} {v : ℝ} {α : Type*} [Fintype α]
    [Nonempty α] (h : BundleBoundAt n m w v) : BipartiteBoundAt α n m w v :=
  fun H_col H_row D hcol hrow hsym hD =>
    bipartite_card_le_of_bundle_bound H_col H_row v (h H_col H_row hcol hrow hsym) D hD

/-! ## The implications -/

/-- **The bundle hypothesis implies the bipartite common deficit.** -/
theorem bipartiteCommonDeficit_of_bundle (h : BundleCommonDeficit) : BipartiteCommonDeficit := by
  obtain ⟨δ, hδ, hb⟩ := h
  refine ⟨δ, hδ, fun w η hη => ?_⟩
  obtain ⟨n₀, hn₀⟩ := hb w
  refine ⟨n₀, fun d hd => ?_⟩
  refine (bipartiteBoundAt_of_bundleBoundAt (hn₀ d hd)).mono_v ?_
  have hd2 : (0 : ℝ) ≤ (d : ℝ) ^ 2 := by positivity
  nlinarith

theorem commonDeficit_of_bundle (h : BundleCommonDeficit) : LeanBacklog.Wall.CommonDeficit :=
  bipartiteCommonDeficit_iff_commonDeficit.mp (bipartiteCommonDeficit_of_bundle h)

/-- **The bundle hypothesis implies the conjecture.** -/
theorem conjecture_of_bundleCommonDeficit (h : BundleCommonDeficit) :
    LeanBacklog.Wall.Conjecture :=
  conjecture_of_bipartiteCommonDeficit (bipartiteCommonDeficit_of_bundle h)

/-- The conjecture's quantifiers with the bundle bound on `d × d`. -/
def BundleCriterion : Prop :=
  ∀ k G c : ℕ, 5 ≤ k → 1 ≤ G → 4 ≤ c → ∀ d₀ : ℕ,
    ∃ (d R : ℕ) (θ δ : ℝ), max d₀ 1 ≤ d ∧ 0 < θ ∧
      BundleBoundAt d d (endWindow k G θ+R+1) ((1-δ)*(d:ℝ)^2) ∧
      (2*(adaptiveAllowance k G c*d+cutBudget k G c d θ):ℕ) +
        (entryBits d*crossBudget d (endWindow k G θ) R:ℕ) <
          δ*(d*d*entryBits d:ℕ)

/-- One window per resource triple, cofinally many dimensions, in bundle form. -/
def WindowwiseBundleCriterion : Prop :=
  ∀ k G c : ℕ, 5 ≤ k → 1 ≤ G → 4 ≤ c →
    ∃ (R : ℕ) (θ δ : ℝ), 0 < θ ∧ budgetRate k G c θ R < δ ∧
      ∀ d₀ : ℕ, ∃ d ≥ d₀,
        BundleBoundAt d d (endWindow k G θ+R+1) ((1-δ)*(d:ℝ)^2)

theorem bipartiteCriterion_of_bundleCriterion (h : BundleCriterion) : BipartiteCriterion := by
  intro k G c hk hG hc d₀
  obtain ⟨d, R, θ, δ, hd, hθ, hb, hgap⟩ := h k G c hk hG hc d₀
  exact ⟨d, R, θ, δ, hd, hθ, bipartiteBoundAt_of_bundleBoundAt hb, hgap⟩

theorem windowwiseBipartite_of_windowwiseBundle (h : WindowwiseBundleCriterion) :
    WindowwiseBipartiteCriterion := by
  intro k G c hk hG hc
  obtain ⟨R, θ, δ, hθ, hT, hcof⟩ := h k G c hk hG hc
  refine ⟨R, θ, δ, hθ, hT, fun d₀ => ?_⟩
  obtain ⟨d, hd, hb⟩ := hcof d₀
  exact ⟨d, hd, bipartiteBoundAt_of_bundleBoundAt hb⟩

theorem conjecture_of_bundleCriterion (h : BundleCriterion) : LeanBacklog.Wall.Conjecture :=
  conjecture_of_bipartiteCriterion (bipartiteCriterion_of_bundleCriterion h)

theorem conjecture_of_windowwiseBundleCriterion (h : WindowwiseBundleCriterion) :
    LeanBacklog.Wall.Conjecture :=
  conjecture_of_windowwiseBipartiteCriterion (windowwiseBipartite_of_windowwiseBundle h)

/-! ## The permutation form -/

/-- Every admissible function on every host given by `w` permutations of `Fin N` has total
value at most `v`. -/
def PermutationBundleBoundAt (N w : ℕ) (v : ℝ) : Prop :=
  ∀ (σ : Fin w → Equiv.Perm (Fin N)) (g : Finset (Fin N ⊕ Fin N) → ℝ),
    IsBundleAdmissible (permCol σ) (permRow σ) g → g univ ≤ v

/-- **The bundle bound and its permutation form are the same statement.** -/
theorem bundleBoundAt_iff_permutation {N w : ℕ} {v : ℝ} :
    BundleBoundAt N N w v ↔ PermutationBundleBoundAt N w v := by
  constructor
  · intro h σ g hg
    exact h (permCol σ) (permRow σ) (card_permCol_le σ) (card_permRow_le σ)
      (mem_permCol_iff_mem_permRow σ) g hg
  · intro h H_col H_row hcol hrow hsym g hg
    obtain ⟨σ, hc, hr⟩ := exists_perm_cover H_col H_row hcol hrow hsym
    exact h σ g (hg.mono_host hc hr)

/-! ## The complete host -/

/-- On the complete host the number of cells of a vertex set is admissible. -/
theorem isBundleAdmissible_card_complete (n m : ℕ) :
    IsBundleAdmissible (fun _ : Fin m => (univ : Finset (Fin n)))
      (fun _ : Fin n => (univ : Finset (Fin m))) (fun S => ((cellsOf S).card : ℝ)) := by
  apply isBundleAdmissible_of_farFeasible (h := fun T => (T.card : ℝ))
  refine ⟨⟨by simp, ?_, ?_⟩, fun p => by simp, fun p => ?_, fun p => ?_⟩
  · intro S T hST
    show ((S.card : ℕ) : ℝ) ≤ ((T.card : ℕ) : ℝ)
    exact_mod_cast card_le_card hST
  · intro S T
    show (((S ∪ T).card : ℕ) : ℝ) + (((S ∩ T).card : ℕ) : ℝ) ≤ ((S.card : ℕ) : ℝ) + ((T.card : ℕ) : ℝ)
    have := card_union_add_card_inter S T
    exact le_of_eq (by exact_mod_cast this)
  · show ((insert p (pinnedColHelpers _ ∅ p)).card : ℝ) = (pinnedColHelpers _ ∅ p).card
    rw [pinnedColHelpers_empty]
    have : colHelpers (fun _ : Fin m => (univ : Finset (Fin n))) p = univ := by
      ext c; simp [colHelpers]
    rw [this, insert_eq_of_mem (mem_univ p)]
  · show ((insert p (pinnedRowHelpers _ ∅ p)).card : ℝ) = (pinnedRowHelpers _ ∅ p).card
    rw [pinnedRowHelpers_empty]
    have : rowHelpers (fun _ : Fin n => (univ : Finset (Fin m))) p = univ := by
      ext c; simp [rowHelpers]
    rw [this, insert_eq_of_mem (mem_univ p)]

/-- On the complete host the cell count has full value `n m`. -/
theorem card_cellsOf_univ (n m : ℕ) :
    (((cellsOf (univ : Finset (Fin m ⊕ Fin n))).card : ℕ) : ℝ) = ((n * m : ℕ) : ℝ) := by
  rw [cellsOf_univ, card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]

/-- A bundle bound at a size not above the degree is at least `n ^ 2`: the size threshold must
come after the degree bound. -/
theorem sq_le_of_bundleBoundAt_of_le {n w : ℕ} {v : ℝ} (hnw : n ≤ w)
    (h : BundleBoundAt n n w v) : (n : ℝ) ^ 2 ≤ v := by
  have hb := h (fun _ => univ) (fun _ => univ) (fun _ => by simpa using hnw)
    (fun _ => by simpa using hnw) (fun _ _ => by simp) _ (isBundleAdmissible_card_complete n n)
  have hc := card_cellsOf_univ n n
  push_cast at hc
  rw [hc] at hb
  nlinarith

#print axioms isBundleAdmissible_zero
#print axioms IsBundleAdmissible.univ_le
#print axioms IsBundleAdmissible.mono_host
#print axioms isBundleAdmissible_of_farFeasible
#print axioms isBundleAdmissible_of_recoverable
#print axioms isBundleAdmissible_normalizedEntropy
#print axioms bipartite_card_le_of_bundle_bound
#print axioms bipartiteBoundAt_of_bundleBoundAt
#print axioms bipartiteCommonDeficit_of_bundle
#print axioms commonDeficit_of_bundle
#print axioms conjecture_of_bundleCommonDeficit
#print axioms bipartiteCriterion_of_bundleCriterion
#print axioms windowwiseBipartite_of_windowwiseBundle
#print axioms conjecture_of_bundleCriterion
#print axioms conjecture_of_windowwiseBundleCriterion
#print axioms bundleBoundAt_iff_permutation
#print axioms isBundleAdmissible_card_complete
#print axioms sq_le_of_bundleBoundAt_of_le

end LeanBacklog.WallBundle
