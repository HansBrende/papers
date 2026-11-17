import MatrixCoding.Wall

/-!
# Far-cell criteria for the whole-row conjecture

The reduction steps used here (restriction to a bipartite quadrant, the expansion
dichotomy, pinning of close cells, the two-copy intersection) are due to
Gemini 4 Carbon (Google DeepMind); this file restates them at a single dimension
and derives cofinal, budgeted criteria.

Contents.
* Bipartite two-sided codes on a quadrant `Fin (d - m) × Fin m` and the transfer of
  a quadrant bound to the full `d × d` array.
* `IsTwoSidedExpander q`: every `1/q` fraction of one side reaches more than a
  `1 - 1/q` fraction of the other. A host that is not an expander already carries a
  deficit of `n m / q²` cells.
* `FarCellBoundAt`: a bound at one size, after pinning a set of at most `e` cells.
  `normalized_bound_of_farCellBoundAt` converts it into a normalized two-sided bound
  on the full array with deficit `farDeficit`.
* `FarCellCriterion`: the conjecture with the full-array bound replaced by a far-cell
  bound on one quadrant at one dimension; it implies `LeanBacklog.Wall.Conjecture`.
* `WindowwiseFarCellCriterion`: one window per resource triple, cofinally many
  dimensions, a deficit compared with the limiting budget `budgetRate`.
* `UniformFarCellDeficit`: one deficit for all windows and all large dimensions,
  with the close cells pinned; it implies the window-wise criterion.
* `TwoCopyFarCellBoundAt`: the prover may also choose row and column permutations and
  bound only codes that are two-sided for both the host and its conjugate; a pinned code
  `D` then has `|D|² ≤ |α| ^ (n m) · |α| ^ v`, and `TwoCopyFarCellCriterion` implies
  the conjecture with deficit `twoCopyDeficit`.

Nothing here asserts any of these hypotheses.
-/

namespace LeanBacklog.WallFarCells

open Finset Transpose Transpose.Tape Transpose.Tape.Impl
open LeanBacklog.RowSpread LeanBacklog.BlockTCC

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Quadrant restriction, pinning and close cells -/

def IsBipartiteTwoSidedCode {n m : ℕ} {α : Type*}
    (H_col : Fin m → Finset (Fin n)) (H_row : Fin n → Finset (Fin m))
    (D : Finset (Fin n × Fin m → α)) : Prop :=
  (∀ x ∈ D, ∀ y ∈ D, ∀ a : Fin m,
    (∀ b ∈ H_col a, ∀ a' : Fin m, x (b, a') = y (b, a')) →
    ∀ b : Fin n, x (b, a) = y (b, a)) ∧
  (∀ x ∈ D, ∀ y ∈ D, ∀ b : Fin n,
    (∀ a ∈ H_row b, ∀ b' : Fin n, x (b', a) = y (b', a)) →
    ∀ a : Fin m, x (b, a) = y (b, a))

/-- Embed `Fin (d - m) × Fin m` as the bottom-left quadrant `{i ≥ m} × {j < m}` of `Entry d`. -/
def blEntry {d m : ℕ} (hm : m ≤ d) (p : Fin (d - m) × Fin m) : Entry d :=
  (⟨m + p.1.1, by omega⟩, ⟨p.2.1, by omega⟩)

theorem blEntry_injective {d m : ℕ} (hm : m ≤ d) :
    Function.Injective (blEntry hm) := by
  intro p q h
  simp only [blEntry, Prod.mk.injEq, Fin.mk.injEq] at h
  ext
  · omega
  · exact h.2

/-- Complement of the bottom-left quadrant `{i ≥ m} × {j < m}` in `Entry d`. -/
def outsideBL (d m : ℕ) : Finset (Entry d) :=
  univ.filter fun p : Entry d => p.1.1 < m ∨ m ≤ p.2.1

theorem card_outsideBL {d m : ℕ} (hm : m ≤ d) :
    (outsideBL d m).card + (d - m) * m = d * d := by
  let blSet : Finset (Entry d) :=
    univ.map ⟨blEntry hm, blEntry_injective hm⟩
  have hdisj : Disjoint (outsideBL d m) blSet := by
    rw [disjoint_left]
    intro p hp1 hp2
    simp only [outsideBL, mem_filter, mem_univ, true_and] at hp1
    simp only [blSet, mem_map, mem_univ, Function.Embedding.coeFn_mk, true_and] at hp2
    rcases hp2 with ⟨⟨b, a⟩, rfl⟩
    simp only [blEntry] at hp1
    omega
  have hunion : outsideBL d m ∪ blSet = univ := by
    ext ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    simp only [mem_union, outsideBL, mem_filter, mem_univ, true_and,
      blSet, mem_map, Function.Embedding.coeFn_mk, iff_true]
    by_cases h : i < m ∨ m ≤ j
    · exact Or.inl h
    · have hge : m ≤ i := by omega
      refine Or.inr ⟨(⟨i - m, by omega⟩, ⟨j, by omega⟩), ?_⟩
      ext <;> simp [blEntry, Nat.add_sub_of_le hge]
  have hcard := card_union_of_disjoint hdisj
  rw [hunion] at hcard
  have hbl : blSet.card = (d - m) * m := by
    simp [blSet]
  have huniv : (univ : Finset (Entry d)).card = d * d := by
    simp [Entry]
  omega

/-- Induced helper rows in `Fin (d - m)` for column `a : Fin m`. -/
def inducedColHelpers {d m : ℕ} (hm : m ≤ d) (ρ : Fin d → Finset (Fin d))
    (a : Fin m) : Finset (Fin (d - m)) :=
  univ.filter fun b : Fin (d - m) => (⟨m + b.1, by omega⟩ : Fin d) ∈ ρ ⟨a.1, by omega⟩

/-- Induced helper columns in `Fin m` for row `b : Fin (d - m)`. -/
def inducedRowHelpers {d m : ℕ} (hm : m ≤ d) (ρ : Fin d → Finset (Fin d))
    (b : Fin (d - m)) : Finset (Fin m) :=
  univ.filter fun a : Fin m => (⟨a.1, by omega⟩ : Fin d) ∈ ρ ⟨m + b.1, by omega⟩

theorem card_inducedColHelpers_le {d m w : ℕ} (hm : m ≤ d)
    (ρ : Fin d → Finset (Fin d)) (hρ : ∀ r, (ρ r).card ≤ w) (a : Fin m) :
    (inducedColHelpers hm ρ a).card ≤ w := by
  have hmap : (inducedColHelpers hm ρ a).map
      ⟨fun b : Fin (d - m) => (⟨m + b.1, by omega⟩ : Fin d),
        fun x y h => by simp only [Fin.mk.injEq] at h; ext; omega⟩ ⊆
      ρ ⟨a.1, by omega⟩ := by
    intro x hx
    simp only [mem_map, inducedColHelpers, mem_filter, mem_univ, true_and] at hx
    rcases hx with ⟨b, hb, rfl⟩
    exact hb
  exact (card_map _).symm.le.trans ((card_le_card hmap).trans (hρ _))

theorem card_inducedRowHelpers_le {d m w : ℕ} (hm : m ≤ d)
    (ρ : Fin d → Finset (Fin d)) (hρ : ∀ r, (ρ r).card ≤ w) (b : Fin (d - m)) :
    (inducedRowHelpers hm ρ b).card ≤ w := by
  have hmap : (inducedRowHelpers hm ρ b).map
      ⟨fun a : Fin m => (⟨a.1, by omega⟩ : Fin d),
        fun x y h => by simp only [Fin.mk.injEq] at h; ext; omega⟩ ⊆
      ρ ⟨m + b.1, by omega⟩ := by
    intro x hx
    simp only [mem_map, inducedRowHelpers, mem_filter, mem_univ, true_and] at hx
    rcases hx with ⟨a, ha, rfl⟩
    exact ha
  exact (card_map _).symm.le.trans ((card_le_card hmap).trans (hρ _))

/-- Restricting any `outsideBL`-fibre of a two-sided whole-row code to the bottom-left
quadrant produces a valid `IsBipartiteTwoSidedCode` of identical cardinality. -/
theorem isBipartiteTwoSidedCode_of_outsideBL_fibre {d m : ℕ} {α : Type*} [DecidableEq α]
    (hm : m ≤ d) (ρ : Fin d → Finset (Fin d)) (C : Finset (Entry d → α))
    (hC : IsTwoSidedWholeRowCode ρ C) (z : outsideBL d m → α) :
    let F := C.filter fun x => (fun p : outsideBL d m => x p) = z
    let D := F.image fun x => fun q : Fin (d - m) × Fin m => x (blEntry hm q)
    D.card = F.card ∧
      IsBipartiteTwoSidedCode (inducedColHelpers hm ρ) (inducedRowHelpers hm ρ) D := by
  intro F D
  have hinj : Set.InjOn (fun x : Entry d → α => fun q : Fin (d - m) × Fin m => x (blEntry hm q)) F := by
    intro x hx y hy hxy
    simp only [F, Finset.mem_coe, mem_filter] at hx hy
    funext ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    by_cases hout : i < m ∨ m ≤ j
    · have hp : ((⟨i, hi⟩, ⟨j, hj⟩) : Entry d) ∈ outsideBL d m := by
        simp [outsideBL, hout]
      exact congrFun (hx.2.trans hy.2.symm) ⟨_, hp⟩
    · have hge : m ≤ i := by omega
      have hlt : j < m := by omega
      have hq := congrFun hxy (⟨i - m, by omega⟩, ⟨j, hlt⟩)
      simpa only [blEntry, Nat.add_sub_of_le hge] using hq
  refine ⟨card_image_of_injOn hinj, ?_, ?_⟩
  · intro x' hx' y' hy' a hagree b
    obtain ⟨x, hxF, rfl⟩ := mem_image.mp hx'
    obtain ⟨y, hyF, rfl⟩ := mem_image.mp hy'
    obtain ⟨hxC, hxz⟩ := mem_filter.mp hxF
    obtain ⟨hyC, hyz⟩ := mem_filter.mp hyF
    apply (wholeRowCode_iff ρ ∅ C).mp hC.1 x hxC y hyC ⟨a.1, by omega⟩ (by simp)
    intro s hs j
    by_cases hout : s.1 < m ∨ m ≤ j.1
    · have hp : (s, j) ∈ outsideBL d m := by simp [outsideBL, hout]
      exact congrFun (hxz.trans hyz.symm) ⟨(s, j), hp⟩
    · have hge : m ≤ s.1 := by omega
      have hlt : j.1 < m := by omega
      have hb_mem : (⟨s.1 - m, by omega⟩ : Fin (d - m)) ∈ inducedColHelpers hm ρ a := by
        simp only [inducedColHelpers, mem_filter, mem_univ, true_and]
        convert hs using 1
        ext; simp; omega
      have hq := hagree ⟨s.1 - m, by omega⟩ hb_mem ⟨j.1, hlt⟩
      simpa only [blEntry, Nat.add_sub_of_le hge] using hq
  · intro x' hx' y' hy' b hagree a
    obtain ⟨x, hxF, rfl⟩ := mem_image.mp hx'
    obtain ⟨y, hyF, rfl⟩ := mem_image.mp hy'
    obtain ⟨hxC, hxz⟩ := mem_filter.mp hxF
    obtain ⟨hyC, hyz⟩ := mem_filter.mp hyF
    apply hC.2 x hxC y hyC ⟨m + b.1, by omega⟩
    intro s hs j
    by_cases hout : j.1 < m ∨ m ≤ s.1
    · have hp : (j, s) ∈ outsideBL d m := by simp [outsideBL, hout]
      exact congrFun (hxz.trans hyz.symm) ⟨(j, s), hp⟩
    · have hge : m ≤ j.1 := by omega
      have hlt : s.1 < m := by omega
      have ha_mem : (⟨s.1, hlt⟩ : Fin m) ∈ inducedRowHelpers hm ρ b := by
        simp only [inducedRowHelpers, mem_filter, mem_univ, true_and]
        exact hs
      have hq := hagree ⟨s.1, hlt⟩ ha_mem ⟨j.1 - m, by omega⟩
      simpa only [blEntry, Nat.add_sub_of_le hge] using hq

/-- Universal nonlinear 3-quadrant reduction: any upper bound `A` on `IsBipartiteTwoSidedCode`
for `(d - m) × m` yields `|C| ≤ |α|^{d^2 - (d - m) * m} * A` on `Entry d`. -/
theorem twoSided_card_le_of_bipartite_quadrant {d m : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (hm : m ≤ d) (ρ : Fin d → Finset (Fin d)) (C : Finset (Entry d → α))
    (hC : IsTwoSidedWholeRowCode ρ C) (A : ℝ)
    (hbound : ∀ D : Finset (Fin (d - m) × Fin m → α),
      IsBipartiteTwoSidedCode (inducedColHelpers hm ρ) (inducedRowHelpers hm ρ) D →
      (D.card : ℝ) ≤ A) :
    (C.card : ℝ) ≤ (Fintype.card α : ℝ) ^ (d * d - (d - m) * m) * A := by
  let obs : (Entry d → α) → (outsideBL d m → α) := fun x p => x p
  have hcount := card_le_of_real_fibre_bound C obs A (fun z => ?_)
  · have hsub : (outsideBL d m).card = d * d - (d - m) * m := by
      have hc := card_outsideBL hm
      omega
    simpa only [Fintype.card_fun, Fintype.card_coe, Nat.cast_pow, hsub] using hcount
  · obtain ⟨hcard, hbip⟩ := isBipartiteTwoSidedCode_of_outsideBL_fibre hm ρ C hC z
    rw [← hcard]
    exact hbound _ hbip

def IsPinnedBipartiteTwoSidedCode {n m : ℕ} {α : Type*}
    (H_col : Fin m → Finset (Fin n)) (H_row : Fin n → Finset (Fin m))
    (E : Finset (Fin n × Fin m)) (D : Finset (Fin n × Fin m → α)) : Prop :=
  (∀ x ∈ D, ∀ y ∈ D, ∀ p ∈ E, x p = y p) ∧
  (∀ x ∈ D, ∀ y ∈ D, ∀ a : Fin m,
    (∀ b ∈ H_col a, ∀ a' : Fin m, (b, a') ∉ E → x (b, a') = y (b, a')) →
    ∀ b : Fin n, x (b, a) = y (b, a)) ∧
  (∀ x ∈ D, ∀ y ∈ D, ∀ b : Fin n,
    (∀ a ∈ H_row b, ∀ b' : Fin n, (b', a) ∉ E → x (b', a) = y (b', a)) →
    ∀ a : Fin m, x (b, a) = y (b, a))

/-- Every `E`-fibre of an `IsBipartiteTwoSidedCode` is an `IsPinnedBipartiteTwoSidedCode`. -/
theorem isPinnedBipartiteTwoSidedCode_of_fibre {n m : ℕ} {α : Type*} [DecidableEq α]
    (H_col : Fin m → Finset (Fin n)) (H_row : Fin n → Finset (Fin m))
    (D : Finset (Fin n × Fin m → α)) (hD : IsBipartiteTwoSidedCode H_col H_row D)
    (E : Finset (Fin n × Fin m)) (z : E → α) :
    IsPinnedBipartiteTwoSidedCode H_col H_row E
      (D.filter fun x => (fun p : E => x p) = z) := by
  have hpin : ∀ x ∈ D.filter (fun x => (fun p : E => x p) = z),
      ∀ y ∈ D.filter (fun x => (fun p : E => x p) = z),
      ∀ p ∈ E, x p = y p := by
    intro x hx y hy p hp
    exact congrFun ((mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm) ⟨p, hp⟩
  refine ⟨hpin, ?_, ?_⟩
  · intro x hx y hy a hagree b
    apply hD.1 x (mem_filter.mp hx).1 y (mem_filter.mp hy).1 a
    intro b' hb' a'
    by_cases hp : (b', a') ∈ E
    · exact hpin x hx y hy (b', a') hp
    · exact hagree b' hb' a' hp
  · intro x hx y hy b hagree a
    apply hD.2 x (mem_filter.mp hx).1 y (mem_filter.mp hy).1 b
    intro a' ha' b'
    by_cases hp : (b', a') ∈ E
    · exact hpin x hx y hy (b', a') hp
    · exact hagree a' ha' b' hp

/-- Universal nonlinear far-zone pinning lemma on `Fin n × Fin m`:
pinning any subset `E` of cells (e.g., distance-`≤ 2L + 1` cells of size `O_w(n + m)`)
multiplies the cardinality bound by at most `|α|^{|E|}`. -/
theorem bipartite_card_le_of_pin_set {n m : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (H_col : Fin m → Finset (Fin n)) (H_row : Fin n → Finset (Fin m))
    (D : Finset (Fin n × Fin m → α)) (hD : IsBipartiteTwoSidedCode H_col H_row D)
    (E : Finset (Fin n × Fin m)) (A : ℝ)
    (hbound : ∀ F : Finset (Fin n × Fin m → α),
      IsPinnedBipartiteTwoSidedCode H_col H_row E F → (F.card : ℝ) ≤ A) :
    (D.card : ℝ) ≤ (Fintype.card α : ℝ) ^ E.card * A := by
  let obs : (Fin n × Fin m → α) → (E → α) := fun x p => x p
  have hcount := card_le_of_real_fibre_bound D obs A (fun z =>
    hbound _ (isPinnedBipartiteTwoSidedCode_of_fibre H_col H_row D hD E z))
  simpa only [Fintype.card_fun, Fintype.card_coe, Nat.cast_pow] using hcount

#print axioms bipartite_card_le_of_pin_set

/-- Rectangle complement `{(b, a) | b ∈ B₁ ∨ a ∉ A₁}` used in the 1-step column-subset bound. -/
def colSubsetObs {n m : ℕ} (B₁ : Finset (Fin n)) (A₁ : Finset (Fin m)) :
    Finset (Fin n × Fin m) :=
  univ.filter fun p : Fin n × Fin m => p.1 ∈ B₁ ∨ p.2 ∉ A₁

theorem card_colSubsetObs {n m : ℕ} (B₁ : Finset (Fin n)) (A₁ : Finset (Fin m)) :
    (colSubsetObs B₁ A₁).card + (n - B₁.card) * A₁.card = n * m := by
  let comp : Finset (Fin n × Fin m) := (univ \ B₁) ×ˢ A₁
  have hdisj : Disjoint (colSubsetObs B₁ A₁) comp := by
    rw [disjoint_left]
    intro p hp1 hp2
    simp only [colSubsetObs, mem_filter, mem_univ, true_and] at hp1
    simp only [comp, mem_product, mem_sdiff, mem_univ, true_and] at hp2
    tauto
  have hunion : colSubsetObs B₁ A₁ ∪ comp = univ := by
    ext ⟨b, a⟩
    simp only [mem_union, colSubsetObs, mem_filter, mem_univ, true_and,
      comp, mem_product, mem_sdiff, iff_true]
    tauto
  have hcard := card_union_of_disjoint hdisj
  rw [hunion] at hcard
  have hcomp : comp.card = (n - B₁.card) * A₁.card := by
    simp [comp, card_sdiff]
  have huniv : (univ : Finset (Fin n × Fin m)).card = n * m := by simp
  omega

/-- Universal 1-step Hall / non-expansion bound for `IsBipartiteTwoSidedCode`:
for any subset of columns `A₁ ⊆ Fin m`, revealing all helper rows `B₁ = A₁.biUnion H_col`
and all remaining cells outside `(univ \ B₁) × A₁` uniquely determines every codeword,
saving `(n - |B₁|) * |A₁|` cells with zero pinning overhead. -/
theorem bipartite_card_le_of_col_subset {n m : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (H_col : Fin m → Finset (Fin n)) (H_row : Fin n → Finset (Fin m))
    (D : Finset (Fin n × Fin m → α)) (hD : IsBipartiteTwoSidedCode H_col H_row D)
    (A₁ : Finset (Fin m)) :
    let B₁ := A₁.biUnion H_col
    D.card ≤ (Fintype.card α) ^ (n * m - (n - B₁.card) * A₁.card) := by
  intro B₁
  let P := colSubsetObs B₁ A₁
  have hinj : Set.InjOn (fun x : Fin n × Fin m → α => fun p : P => x p) D := by
    intro x hx y hy hxy
    funext ⟨b, a⟩
    by_cases ha : a ∈ A₁
    · apply hD.1 x hx y hy a
      intro b' hb' a'
      have hb1 : b' ∈ B₁ := mem_biUnion.mpr ⟨a, ha, hb'⟩
      have hp : (b', a') ∈ P := by simp [P, colSubsetObs, hb1]
      exact congrFun hxy ⟨(b', a'), hp⟩
    · have hp : (b, a) ∈ P := by simp [P, colSubsetObs, ha]
      exact congrFun hxy ⟨(b, a), hp⟩
  have hle : D.card ≤ Fintype.card (P → α) := by
    rw [← card_image_of_injOn hinj]
    exact card_le_univ _
  have hP : P.card = n * m - (n - B₁.card) * A₁.card := by
    have hc := card_colSubsetObs B₁ A₁
    change P.card + (n - B₁.card) * A₁.card = n * m at hc
    omega
  rw [Fintype.card_fun, Fintype.card_coe, hP] at hle
  exact hle

/-- Symmetric 1-step Hall / non-expansion bound for any subset of rows `B₁ ⊆ Fin n`. -/
theorem bipartite_card_le_of_row_subset {n m : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (H_col : Fin m → Finset (Fin n)) (H_row : Fin n → Finset (Fin m))
    (D : Finset (Fin n × Fin m → α)) (hD : IsBipartiteTwoSidedCode H_col H_row D)
    (B₁ : Finset (Fin n)) :
    let A₁ := B₁.biUnion H_row
    D.card ≤ (Fintype.card α) ^ (n * m - B₁.card * (m - A₁.card)) := by
  intro A₁
  let D_swap : Finset (Fin m × Fin n → α) :=
    D.image fun x => fun p : Fin m × Fin n => x (p.2, p.1)
  have hswap_inj : Set.InjOn (fun x : Fin n × Fin m → α => fun p : Fin m × Fin n => x (p.2, p.1)) D := by
    intro x _ y _ hxy
    funext ⟨b, a⟩
    exact congrFun hxy (a, b)
  have hswap_code : IsBipartiteTwoSidedCode H_row H_col D_swap := by
    refine ⟨?_, ?_⟩
    · intro x' hx' y' hy' b hagree a
      obtain ⟨x, hxD, rfl⟩ := mem_image.mp hx'
      obtain ⟨y, hyD, rfl⟩ := mem_image.mp hy'
      exact hD.2 x hxD y hyD b hagree a
    · intro x' hx' y' hy' a hagree b
      obtain ⟨x, hxD, rfl⟩ := mem_image.mp hx'
      obtain ⟨y, hyD, rfl⟩ := mem_image.mp hy'
      exact hD.1 x hxD y hyD a hagree b
  have hbound := bipartite_card_le_of_col_subset H_row H_col D_swap hswap_code B₁
  rw [card_image_of_injOn hswap_inj] at hbound
  simpa only [Nat.mul_comm] using hbound
/-- Rows reachable from column `a` in `2 * k + 1` bipartite steps of `(H_col, H_row)`. -/
def reachRow {n m : ℕ}
    (H_col : Fin m → Finset (Fin n)) (H_row : Fin n → Finset (Fin m)) :
    ℕ → Fin m → Finset (Fin n)
  | 0, a => H_col a
  | k + 1, a => ((reachRow H_col H_row k a).biUnion H_row).biUnion H_col

theorem card_reachRow_le {n m w : ℕ}
    (H_col : Fin m → Finset (Fin n)) (H_row : Fin n → Finset (Fin m))
    (hcol : ∀ a, (H_col a).card ≤ w) (hrow : ∀ b, (H_row b).card ≤ w) :
    ∀ k (a : Fin m), (reachRow H_col H_row k a).card ≤ w ^ (2 * k + 1)
  | 0, a => by simpa [reachRow] using hcol a
  | k + 1, a => by
    let Rk := reachRow H_col H_row k a
    have h1 : (Rk.biUnion H_row).card ≤ Rk.card * w := by
      calc (Rk.biUnion H_row).card
          ≤ ∑ b ∈ Rk, (H_row b).card := card_biUnion_le
        _ ≤ ∑ _b ∈ Rk, w := sum_le_sum fun b _ => hrow b
        _ = Rk.card * w := by simp
    have h2 : (((Rk.biUnion H_row).biUnion H_col)).card ≤ (Rk.biUnion H_row).card * w := by
      calc ((Rk.biUnion H_row).biUnion H_col).card
          ≤ ∑ a' ∈ Rk.biUnion H_row, (H_col a').card := card_biUnion_le
        _ ≤ ∑ _a' ∈ Rk.biUnion H_row, w := sum_le_sum fun a' _ => hcol a'
        _ = (Rk.biUnion H_row).card * w := by simp
    have ih := card_reachRow_le H_col H_row hcol hrow k a
    calc (reachRow H_col H_row (k + 1) a).card
        ≤ (Rk.biUnion H_row).card * w := h2
      _ ≤ (Rk.card * w) * w := Nat.mul_le_mul_right w h1
      _ ≤ (w ^ (2 * k + 1) * w) * w :=
          Nat.mul_le_mul_right w (Nat.mul_le_mul_right w ih)
      _ = w ^ (2 * (k + 1) + 1) := by ring

/-- All cells `(b, a)` within bipartite graph distance `≤ 2 * L + 1` in `(H_col, H_row)`. -/
def closeBall {n m : ℕ}
    (H_col : Fin m → Finset (Fin n)) (H_row : Fin n → Finset (Fin m)) (L : ℕ) :
    Finset (Fin n × Fin m) :=
  univ.filter fun p : Fin n × Fin m => p.1 ∈ reachRow H_col H_row L p.2

theorem card_closeBall_le {n m w : ℕ}
    (H_col : Fin m → Finset (Fin n)) (H_row : Fin n → Finset (Fin m))
    (hcol : ∀ a, (H_col a).card ≤ w) (hrow : ∀ b, (H_row b).card ≤ w) (L : ℕ) :
    (closeBall H_col H_row L).card ≤ m * w ^ (2 * L + 1) := by
  have hsub : closeBall H_col H_row L ⊆
      univ.biUnion (fun a : Fin m => (reachRow H_col H_row L a).image (fun b => (b, a))) := by
    intro ⟨b, a⟩ hp
    simp only [closeBall, mem_filter, mem_univ, true_and] at hp
    exact mem_biUnion.mpr ⟨a, mem_univ a, mem_image.mpr ⟨b, hp, rfl⟩⟩
  calc (closeBall H_col H_row L).card
      ≤ (univ.biUnion (fun a : Fin m => (reachRow H_col H_row L a).image (fun b => (b, a)))).card :=
        card_le_card hsub
    _ ≤ ∑ a : Fin m, ((reachRow H_col H_row L a).image (fun b => (b, a))).card := card_biUnion_le
    _ ≤ ∑ a : Fin m, (reachRow H_col H_row L a).card :=
        sum_le_sum fun a _ => card_image_le
    _ ≤ ∑ _a : Fin m, w ^ (2 * L + 1) :=
        sum_le_sum fun a _ => card_reachRow_le H_col H_row hcol hrow L a
    _ = m * w ^ (2 * L + 1) := by simp

/-! ## Expansion and the far-cell bound -/

/-- `q`-expansion in both directions: every `1/q` fraction of one side reaches more than a
`1 - 1/q` fraction of the other. (`q = 10` is the constant of the original reduction.) -/
def IsTwoSidedExpander {n m : ℕ} (q : ℕ)
    (H_col : Fin m → Finset (Fin n)) (H_row : Fin n → Finset (Fin m)) : Prop :=
  (∀ A₁ : Finset (Fin m), m ≤ q * A₁.card → (q - 1) * n < q * (A₁.biUnion H_col).card) ∧
  (∀ B₁ : Finset (Fin n), n ≤ q * B₁.card → (q - 1) * m < q * (B₁.biUnion H_row).card)

/-- At `q = 10` the predicate is the `(1/10 → 9/10)` expansion of the original reduction. -/
theorem isTwoSidedExpander_ten_iff {n m : ℕ}
    (H_col : Fin m → Finset (Fin n)) (H_row : Fin n → Finset (Fin m)) :
    IsTwoSidedExpander 10 H_col H_row ↔
      (∀ A₁ : Finset (Fin m), m ≤ 10 * A₁.card → 9 * n < 10 * (A₁.biUnion H_col).card) ∧
      (∀ B₁ : Finset (Fin n), n ≤ 10 * B₁.card → 9 * m < 10 * (B₁.biUnion H_row).card) :=
  Iff.rfl

/-- The far-cell bound at one size. For every symmetric host of degree at most `w` that is a
`q`-expander, the prover may choose a set `E` of at most `e` cells; every two-sided code whose
words agree on `E` then has at most `|α| ^ v` words. -/
def FarCellBoundAt (α : Type*) [Fintype α] (n m w q e : ℕ) (v : ℝ) : Prop :=
  ∀ (H_col : Fin m → Finset (Fin n)) (H_row : Fin n → Finset (Fin m)),
    (∀ a, (H_col a).card ≤ w) → (∀ b, (H_row b).card ≤ w) →
    (∀ a b, b ∈ H_col a ↔ a ∈ H_row b) →
    IsTwoSidedExpander q H_col H_row →
    ∃ E : Finset (Fin n × Fin m), E.card ≤ e ∧
      ∀ D : Finset (Fin n × Fin m → α),
        IsPinnedBipartiteTwoSidedCode H_col H_row E D →
          (D.card : ℝ) ≤ (Fintype.card α : ℝ) ^ v

/-- Cells saved on the full `d × d` array by a far-cell bound on an `n × m` quadrant. -/
noncomputable def farDeficit (n m q e : ℕ) (v : ℝ) : ℝ :=
  min ((n * m : ℝ) - v - e) ((n * m : ℝ) / (q : ℝ) ^ 2)

/-- Sanity: the bound holds with no pinned cells and the trivial exponent `n m`. -/
theorem farCellBoundAt_trivial (α : Type*) [Fintype α] (n m w q : ℕ) :
    FarCellBoundAt α n m w q 0 ((n * m : ℕ) : ℝ) := by
  classical
  intro H_col H_row _ _ _ _
  refine ⟨∅, by simp, fun D _ => ?_⟩
  have h := card_le_univ D
  rw [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at h
  rw [Real.rpow_natCast]
  exact_mod_cast h

/-- Sanity: a larger pin budget is a weaker requirement. -/
theorem FarCellBoundAt.mono_e {α : Type*} [Fintype α] {n m w q e e' : ℕ} {v : ℝ}
    (h : FarCellBoundAt α n m w q e v) (hee : e ≤ e') : FarCellBoundAt α n m w q e' v := by
  intro H_col H_row hcol hrow hsym hE
  obtain ⟨E, hEc, hb⟩ := h H_col H_row hcol hrow hsym hE
  exact ⟨E, hEc.trans hee, hb⟩

/-- Sanity: a larger exponent is a weaker requirement (nonempty alphabet). -/
theorem FarCellBoundAt.mono_v {α : Type*} [Fintype α] [Nonempty α] {n m w q e : ℕ}
    {v v' : ℝ} (h : FarCellBoundAt α n m w q e v) (hvv : v ≤ v') :
    FarCellBoundAt α n m w q e v' := by
  intro H_col H_row hcol hrow hsym hE
  obtain ⟨E, hEc, hb⟩ := h H_col H_row hcol hrow hsym hE
  have h1 : (1 : ℝ) ≤ Fintype.card α := by exact_mod_cast Fintype.card_pos
  exact ⟨E, hEc, fun D hD => (hb D hD).trans (Real.rpow_le_rpow_of_exponent_le h1 hvv)⟩

/-- Sanity: a bound for the close-cell pin set `closeBall H_col H_row L` on every admissible
host is a far-cell bound with pin budget `m * w ^ (2 * L + 1)`. -/
theorem farCellBoundAt_of_closeBall {α : Type*} [Fintype α] {n m w q : ℕ} {v : ℝ} (L : ℕ)
    (h : ∀ (H_col : Fin m → Finset (Fin n)) (H_row : Fin n → Finset (Fin m)),
      (∀ a, (H_col a).card ≤ w) → (∀ b, (H_row b).card ≤ w) →
      (∀ a b, b ∈ H_col a ↔ a ∈ H_row b) →
      IsTwoSidedExpander q H_col H_row →
      ∀ D : Finset (Fin n × Fin m → α),
        IsPinnedBipartiteTwoSidedCode H_col H_row (closeBall H_col H_row L) D →
          (D.card : ℝ) ≤ (Fintype.card α : ℝ) ^ v) :
    FarCellBoundAt α n m w q (m * w ^ (2 * L + 1)) v := by
  intro H_col H_row hcol hrow hsym hE
  exact ⟨closeBall H_col H_row L, card_closeBall_le H_col H_row hcol hrow L,
    h H_col H_row hcol hrow hsym hE⟩

/-- Arithmetic of a failed expansion clause: `m ≤ q a` and `q N ≤ (q - 1) n` give
`n m / q² ≤ (n - N) a`. No condition on `q` is needed (`q = 0` makes the left side `0`). -/
theorem div_sq_le_of_nonexpand {n m q N a : ℕ} (hN : N ≤ n) (ha : m ≤ q * a)
    (hq : q * N ≤ (q - 1) * n) :
    (n * m : ℝ) / (q : ℝ) ^ 2 ≤ (((n - N) * a : ℕ) : ℝ) := by
  rcases Nat.eq_zero_or_pos q with rfl | hqpos
  · simp only [Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      div_zero]
    positivity
  · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hN
    have hsub : N + t - N = t := by omega
    rw [hsub]
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    have hq' : (q' + 1) * N ≤ q' * (N + t) := by simpa using hq
    have h1 : N + t ≤ (q' + 1) * t := by nlinarith [hq']
    have h2 : (N + t) * m ≤ (q' + 1) ^ 2 * (t * a) := by
      calc (N + t) * m ≤ ((q' + 1) * t) * ((q' + 1) * a) := Nat.mul_le_mul h1 ha
        _ = (q' + 1) ^ 2 * (t * a) := by ring
    have hpos : (0:ℝ) < ((q' + 1 : ℕ) : ℝ) ^ 2 := by positivity
    rw [div_le_iff₀ hpos]
    have h3 : (((N + t) * m : ℕ) : ℝ) ≤ (((q' + 1) ^ 2 * (t * a) : ℕ) : ℝ) := by
      exact_mod_cast h2
    push_cast at h3 ⊢
    linarith

/-- A host that is not a `q`-expander forces a deficit of `n m / q²` cells on every
bipartite two-sided code. -/
theorem bipartite_card_le_of_not_expander {n m q : ℕ} {α : Type*} [Fintype α] [Nonempty α]
    (H_col : Fin m → Finset (Fin n)) (H_row : Fin n → Finset (Fin m))
    (D : Finset (Fin n × Fin m → α)) (hD : IsBipartiteTwoSidedCode H_col H_row D)
    (hE : ¬ IsTwoSidedExpander q H_col H_row) :
    (D.card : ℝ) ≤ (Fintype.card α : ℝ) ^ ((n * m : ℝ) - (n * m : ℝ) / (q : ℝ) ^ 2) := by
  classical
  have hge1α : (1 : ℝ) ≤ Fintype.card α := by exact_mod_cast Fintype.card_pos
  simp only [IsTwoSidedExpander, not_and_or, not_forall, not_lt] at hE
  rcases hE with ⟨A₁, hA₁, hB₁⟩ | ⟨B₁, hB₁, hA₁⟩
  · have hnat := bipartite_card_le_of_col_subset H_col H_row D hD A₁
    have hb_le : (A₁.biUnion H_col).card ≤ n := by
      simpa using card_le_univ (A₁.biUnion H_col)
    have hle_prod : (n - (A₁.biUnion H_col).card) * A₁.card ≤ n * m :=
      Nat.mul_le_mul (Nat.sub_le _ _) (by simpa using card_le_univ A₁)
    have hcast : (D.card : ℝ) ≤ (Fintype.card α : ℝ) ^
        ((n * m - (n - (A₁.biUnion H_col).card) * A₁.card : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]
      exact_mod_cast hnat
    apply hcast.trans (Real.rpow_le_rpow_of_exponent_le hge1α ?_)
    have hkey := div_sq_le_of_nonexpand hb_le hA₁ hB₁
    rw [Nat.cast_sub hle_prod]
    push_cast at hkey ⊢
    linarith
  · have hnat := bipartite_card_le_of_row_subset H_col H_row D hD B₁
    have ha_le : (B₁.biUnion H_row).card ≤ m := by
      simpa using card_le_univ (B₁.biUnion H_row)
    have hle_prod : B₁.card * (m - (B₁.biUnion H_row).card) ≤ n * m :=
      Nat.mul_le_mul (by simpa using card_le_univ B₁) (Nat.sub_le _ _)
    have hcast : (D.card : ℝ) ≤ (Fintype.card α : ℝ) ^
        ((n * m - B₁.card * (m - (B₁.biUnion H_row).card) : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]
      exact_mod_cast hnat
    apply hcast.trans (Real.rpow_le_rpow_of_exponent_le hge1α ?_)
    have hkey := div_sq_le_of_nonexpand ha_le hB₁ hA₁
    rw [Nat.cast_sub hle_prod]
    push_cast at hkey ⊢
    have hcomm : (m : ℝ) * n = n * m := by ring
    rw [hcomm] at hkey
    linarith

/-- The per-host form: on a symmetric host of degree at most `w`, a far-cell bound gives
every bipartite two-sided code at most `|α| ^ (n m - farDeficit)` words. -/
theorem bipartite_card_le_of_farCellBoundAt {n m w q e : ℕ} {v : ℝ}
    {α : Type*} [Fintype α] [Nonempty α] (hfar : FarCellBoundAt α n m w q e v)
    (H_col : Fin m → Finset (Fin n)) (H_row : Fin n → Finset (Fin m))
    (hcol : ∀ a, (H_col a).card ≤ w) (hrow : ∀ b, (H_row b).card ≤ w)
    (hsym : ∀ a b, b ∈ H_col a ↔ a ∈ H_row b)
    (D : Finset (Fin n × Fin m → α)) (hD : IsBipartiteTwoSidedCode H_col H_row D) :
    (D.card : ℝ) ≤ (Fintype.card α : ℝ) ^ ((n * m : ℝ) - farDeficit n m q e v) := by
  classical
  have hge1α : (1 : ℝ) ≤ Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hposα : (0 : ℝ) < Fintype.card α := by linarith
  by_cases hE : IsTwoSidedExpander q H_col H_row
  · obtain ⟨E, hEc, hEb⟩ := hfar H_col H_row hcol hrow hsym hE
    have hpin := bipartite_card_le_of_pin_set H_col H_row D hD E
      ((Fintype.card α : ℝ) ^ v) hEb
    rw [← Real.rpow_natCast, ← Real.rpow_add hposα] at hpin
    apply hpin.trans (Real.rpow_le_rpow_of_exponent_le hge1α ?_)
    have h1 : farDeficit n m q e v ≤ (n * m : ℝ) - v - e := min_le_left _ _
    have h2 : (E.card : ℝ) ≤ e := by exact_mod_cast hEc
    linarith
  · apply (bipartite_card_le_of_not_expander H_col H_row D hD hE).trans
      (Real.rpow_le_rpow_of_exponent_le hge1α ?_)
    have h1 : farDeficit n m q e v ≤ (n * m : ℝ) / (q : ℝ) ^ 2 := min_le_right _ _
    linarith

/-- **Pointwise transfer.** A far-cell bound on the quadrant `(d - m) × m` gives a normalized
two-sided bound on the full `d × d` array with deficit `farDeficit`. -/
theorem normalized_bound_of_farCellBoundAt {d m w q e : ℕ} {v : ℝ}
    {α : Type*} [Fintype α] [Nonempty α] (hm : m ≤ d)
    (hfar : FarCellBoundAt α (d - m) m w q e v) :
    NormalizedTwoSidedWholeRowCardinalityBound d w α
      ((d:ℝ)^2 - farDeficit (d - m) m q e v) := by
  classical
  intro ρ C hρ hρ_sym _ hC
  have hge1α : (1 : ℝ) ≤ Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hposα : (0 : ℝ) < Fintype.card α := by linarith
  have hsym_ind : ∀ (a : Fin m) (b : Fin (d - m)),
      b ∈ inducedColHelpers hm ρ a ↔ a ∈ inducedRowHelpers hm ρ b := by
    intro a b
    simp only [inducedColHelpers, inducedRowHelpers, mem_filter, mem_univ, true_and]
    exact hρ_sym ⟨a.1, by omega⟩ ⟨m + b.1, by omega⟩
  have hstep := twoSided_card_le_of_bipartite_quadrant hm ρ C hC
    ((Fintype.card α : ℝ) ^ ((((d - m : ℕ) : ℝ) * (m : ℝ)) - farDeficit (d - m) m q e v))
    (fun D hD => bipartite_card_le_of_farCellBoundAt hfar _ _
      (card_inducedColHelpers_le hm ρ hρ) (card_inducedRowHelpers_le hm ρ hρ) hsym_ind D hD)
  rw [← Real.rpow_natCast, ← Real.rpow_add hposα] at hstep
  apply hstep.trans (le_of_eq ?_)
  congr 1
  have hsub_nat : (d - m) * m ≤ d * d := Nat.mul_le_mul (Nat.sub_le d m) hm
  rw [Nat.cast_sub hsub_nat]
  push_cast
  ring

/-! ## The criterion -/

/-- The conjecture with the full-array bound replaced by a far-cell bound on one quadrant.
All parameters, including the split `m`, the expansion parameter `q`, the pin budget `e` and
the exponent `v`, are chosen by the prover together with `d`, `R` and `θ`. -/
def FarCellCriterion : Prop :=
  ∀ k G c : ℕ, 5 ≤ k → 1 ≤ G → 4 ≤ c → ∀ d₀ : ℕ,
    ∃ (d R m q e : ℕ) (θ v : ℝ), max d₀ 1 ≤ d ∧ 0 < θ ∧ m ≤ d ∧ 1 ≤ q ∧
      FarCellBoundAt (Fin (entryBits d) → Bool) (d - m) m (endWindow k G θ + R + 1) q e v ∧
      (2*(adaptiveAllowance k G c*d+cutBudget k G c d θ):ℕ) +
        (entryBits d*crossBudget d (endWindow k G θ) R:ℕ) <
          farDeficit (d - m) m q e v * (entryBits d : ℝ)

/-- **The far-cell criterion implies the conjecture**, with `δ = farDeficit / d²`. -/
theorem conjecture_of_farCellCriterion (h : FarCellCriterion) : LeanBacklog.Wall.Conjecture := by
  intro k G c hk hG hc d₀
  obtain ⟨d, R, m, q, e, θ, v, hd, hθ, hm, _, hfar, hgap⟩ := h k G c hk hG hc d₀
  have hd1 : 1 ≤ d := (le_max_right _ _).trans hd
  have hdpos : (0:ℝ) < d := by exact_mod_cast hd1
  have hd2 : (d:ℝ)^2 ≠ 0 := by positivity
  refine ⟨d, R, θ, farDeficit (d - m) m q e v / (d:ℝ)^2, hd, hθ, ?_, ?_⟩
  · have hb := normalized_bound_of_farCellBoundAt hm hfar
    have heq : (1 - farDeficit (d - m) m q e v / (d:ℝ)^2) * (d:ℝ)^2 =
        (d:ℝ)^2 - farDeficit (d - m) m q e v := by
      field_simp
    rw [heq]
    exact hb
  · have heq : farDeficit (d - m) m q e v / (d:ℝ)^2 * ((d*d*entryBits d:ℕ):ℝ) =
        farDeficit (d - m) m q e v * (entryBits d : ℝ) := by
      push_cast
      field_simp
    rw [heq]
    exact hgap

/-! ## The limiting budget -/

/-- The limiting budget per cell of the full array, as `d → ∞`: twice the cut envelope
`(4kG+1) c θ` plus the symmetry payment `2w/(R+1)` at the end window. -/
noncomputable def budgetRate (k G c : ℕ) (θ : ℝ) (R : ℕ) : ℝ :=
  2 * ((4*k*G+1 : ℕ) : ℝ) * (c : ℝ) * θ + symmetryPayment (endWindow k G θ) R

/-- If the limiting budget is below `δ`, the finite budget of the conjecture is below
`δ d² b(d)` for all large `d`. -/
theorem budget_lt_of_budgetRate_lt {k G c R : ℕ} {θ δ : ℝ} (hG : 1 ≤ G) (hθ : 0 < θ)
    (hT : budgetRate k G c θ R < δ) :
    ∃ d₁ : ℕ, ∀ d ≥ d₁,
      (2*(adaptiveAllowance k G c*d+cutBudget k G c d θ):ℕ) +
        (entryBits d*crossBudget d (endWindow k G θ) R:ℕ) <
          δ*(d*d*entryBits d:ℕ) := by
  set B : ℝ := ((4*k*G+1 : ℕ) : ℝ) with hBdef
  set K : ℝ := (adaptiveAllowance k G c : ℝ) with hKdef
  set sP : ℝ := symmetryPayment (endWindow k G θ) R with hsP
  have hB : 0 ≤ B := by positivity
  have hK : 0 ≤ K := by positivity
  set γ : ℝ := δ - budgetRate k G c θ R with hγdef
  have hγ : 0 < γ := by linarith
  obtain ⟨N, hN⟩ := exists_nat_gt ((2*K + 2*B*θ)/γ)
  refine ⟨N, fun d hd => ?_⟩
  have hdN : (N:ℝ) ≤ d := by exact_mod_cast hd
  have hratio : (2*K + 2*B*θ) < γ * d := by
    have := (div_lt_iff₀ hγ).mp (lt_of_lt_of_le hN hdN)
    linarith
  have hratio0 : 0 ≤ (2*K + 2*B*θ)/γ := by positivity
  have hdpos : (0:ℝ) < d := by linarith [lt_of_le_of_lt hratio0 (lt_of_lt_of_le hN hdN)]
  have hbits : (1:ℝ) ≤ entryBits d := by
    exact_mod_cast (show 1 ≤ entryBits d by unfold entryBits; omega)
  have hm := cutBudget_le_envelope (k := k) (c := c) (d := d) hG hθ.le
  have hx := crossBudget_le_envelope d (endWindow k G θ) R
  have hx' := mul_le_mul_of_nonneg_left hx (show (0:ℝ) ≤ entryBits d by positivity)
  have hdb : (0:ℝ) < d * entryBits d := by positivity
  have h1 := mul_lt_mul_of_pos_right hratio hdb
  have h2 : K * d ≤ K * d * entryBits d := by
    have : 0 ≤ K * d := by positivity
    nlinarith
  have hTdef : budgetRate k G c θ R = 2 * B * c * θ + sP := rfl
  have hδ : δ = 2 * B * c * θ + sP + γ := by linarith
  rw [← hBdef] at hm
  rw [← hsP] at hx'
  push_cast at hm hx' ⊢
  rw [← hKdef, hδ]
  nlinarith [hm, hx', h1, h2]

/-- For every `δ > 0` there are a density `θ > 0` and a cutoff `R` with limiting budget
below `δ`. -/
theorem exists_budgetRate_lt (k G c : ℕ) (hc : 1 ≤ c) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (θ : ℝ) (R : ℕ), 0 < θ ∧ budgetRate k G c θ R < δ := by
  set B : ℝ := ((4*k*G+1 : ℕ) : ℝ) with hBdef
  have hcpos : (0:ℝ) < c := by exact_mod_cast (show 0 < c by omega)
  have hB : 0 < B := by positivity
  set θ : ℝ := δ / (4 * (B * c)) with hθdef
  have hθ : 0 < θ := by positivity
  have hθeq : 2 * B * c * θ = δ / 2 := by
    rw [hθdef]
    field_simp
    ring
  obtain ⟨R, hR⟩ := exists_symmetryPayment_lt (endWindow k G θ) (show 0 < δ / 2 by positivity)
  refine ⟨θ, R, hθ, ?_⟩
  change 2 * B * (c : ℝ) * θ + symmetryPayment (endWindow k G θ) R < δ
  linarith

/-! ## One window per resource triple -/

/-- `d² ≤ 4 (d - d/2)(d/2) + 1`: the quadrant at the split `d/2` holds about a quarter of
the array. -/
theorem sq_le_four_mul_half (d : ℕ) : d * d ≤ 4 * ((d - d / 2) * (d / 2)) + 1 := by
  rcases Nat.even_or_odd' d with ⟨j, rfl | rfl⟩
  · have h1 : 2 * j / 2 = j := by omega
    have h2 : 2 * j - j = j := by omega
    rw [h1, h2]
    nlinarith
  · have h1 : (2 * j + 1) / 2 = j := by omega
    have h2 : 2 * j + 1 - j = j + 1 := by omega
    rw [h1, h2]
    nlinarith

/-- One window per `(k, G, c)`: a far-cell deficit `δ₁` at the single window
`endWindow k G θ + R + 1`, for cofinally many `d`, large enough against the limiting budget. -/
def WindowwiseFarCellCriterion : Prop :=
  ∀ k G c : ℕ, 5 ≤ k → 1 ≤ G → 4 ≤ c →
    ∃ (R q : ℕ) (θ δ₁ : ℝ), 0 < θ ∧ 2 ≤ q ∧ 0 < δ₁ ∧
      budgetRate k G c θ R < min δ₁ (1 / (q:ℝ)^2) / 4 ∧
      ∀ d₀ : ℕ, ∃ d ≥ d₀, ∃ (e : ℕ) (v : ℝ),
        FarCellBoundAt (Fin (entryBits d) → Bool) (d - d / 2) (d / 2)
          (endWindow k G θ + R + 1) q e v ∧
        v + e ≤ (1 - δ₁) * (((d - d / 2) * (d / 2) : ℕ) : ℝ)

/-- **The window-wise criterion implies the far-cell criterion.** -/
theorem farCellCriterion_of_windowwise (h : WindowwiseFarCellCriterion) : FarCellCriterion := by
  intro k G c hk hG hc d₀
  obtain ⟨R, q, θ, δ₁, hθ, hq, hδ₁, hT, hcof⟩ := h k G c hk hG hc
  set μ : ℝ := min δ₁ (1 / (q:ℝ)^2) with hμdef
  have hqpos : (0:ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hμ : 0 < μ := lt_min hδ₁ (by positivity)
  set δ' : ℝ := (budgetRate k G c θ R + μ / 4) / 2 with hδ'def
  have hδ'1 : budgetRate k G c θ R < δ' := by linarith
  have hδ'2 : δ' < μ / 4 := by linarith
  obtain ⟨d₁, hd₁⟩ := budget_lt_of_budgetRate_lt hG hθ hδ'1
  have hgap : 0 < μ - 4 * δ' := by linarith
  obtain ⟨N, hN⟩ := exists_nat_gt (μ / (μ - 4 * δ'))
  obtain ⟨d, hd, e, v, hfar, hve⟩ := hcof (max (max d₀ 1) (max d₁ N))
  have hd0 : max d₀ 1 ≤ d := (le_max_left _ _).trans hd
  have hd1 : 1 ≤ d := (le_max_right _ _).trans hd0
  have hdd₁ : d₁ ≤ d := (le_max_left _ _).trans ((le_max_right _ _).trans hd)
  have hdN : N ≤ d := (le_max_right _ _).trans ((le_max_right _ _).trans hd)
  refine ⟨d, R, d / 2, q, e, θ, v, hd0, hθ, Nat.div_le_self d 2, by omega, hfar, ?_⟩
  have hbudget := hd₁ d hdd₁
  -- quadrant area
  have harea_nat := sq_le_four_mul_half d
  set n : ℕ := d - d / 2 with hn
  set m : ℕ := d / 2 with hm
  have harea : (d:ℝ)^2 ≤ 4 * ((n:ℝ) * m) + 1 := by
    have : ((d * d : ℕ) : ℝ) ≤ ((4 * (n * m) + 1 : ℕ) : ℝ) := by exact_mod_cast harea_nat
    push_cast at this
    nlinarith
  have hve' : v + e ≤ (1 - δ₁) * ((n:ℝ) * m) := by
    have := hve
    push_cast at this
    exact this
  have hnm : 0 ≤ (n:ℝ) * m := by positivity
  -- the deficit is at least μ n m
  have hF : μ * ((n:ℝ) * m) ≤ farDeficit n m q e v := by
    unfold farDeficit
    apply le_min
    · have : μ ≤ δ₁ := min_le_left _ _
      nlinarith
    · have : μ ≤ 1 / (q:ℝ)^2 := min_le_right _ _
      have h2 : ((n:ℝ) * m) / (q:ℝ)^2 = (1 / (q:ℝ)^2) * ((n:ℝ) * m) := by ring
      rw [h2]
      nlinarith
  -- d large: δ' d² ≤ μ (d² - 1)/4
  have hdNr : (N:ℝ) ≤ d := by exact_mod_cast hdN
  have hd1r : (1:ℝ) ≤ d := by exact_mod_cast hd1
  have hlarge : μ < (μ - 4 * δ') * (d:ℝ)^2 := by
    have h1 := (div_lt_iff₀ hgap).mp (lt_of_lt_of_le hN hdNr)
    have h2 : (d:ℝ) ≤ (d:ℝ)^2 := by nlinarith
    nlinarith
  have hδd : δ' * (d:ℝ)^2 ≤ farDeficit n m q e v := by nlinarith
  have hbits : (0:ℝ) ≤ entryBits d := by positivity
  have hfin : δ' * ((d*d*entryBits d : ℕ) : ℝ) ≤ farDeficit n m q e v * (entryBits d : ℝ) := by
    push_cast
    have := mul_le_mul_of_nonneg_right hδd hbits
    nlinarith
  exact lt_of_lt_of_le hbudget hfin

/-! ## The uniform hypothesis of the original reduction -/

/-- One deficit `δ₁` for every window and all large `d`, after pinning the cells within
bipartite distance `2 L(w) + 1`, on `q`-expanding hosts. At `q = 10` this is the uniform
far-expander hypothesis of the original reduction (`isTwoSidedExpander_ten_iff`). -/
def UniformFarCellDeficit (L : ℕ → ℕ) (q : ℕ) : Prop :=
  ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∀ w : ℕ, ∃ d₀ : ℕ, ∀ d ≥ d₀,
    ∀ (H_col : Fin (d / 2) → Finset (Fin (d - d / 2)))
      (H_row : Fin (d - d / 2) → Finset (Fin (d / 2)))
      (D : Finset (Fin (d - d / 2) × Fin (d / 2) → (Fin (entryBits d) → Bool))),
      (∀ a, (H_col a).card ≤ w) → (∀ b, (H_row b).card ≤ w) →
      (∀ a b, b ∈ H_col a ↔ a ∈ H_row b) →
      IsTwoSidedExpander q H_col H_row →
      IsPinnedBipartiteTwoSidedCode H_col H_row (closeBall H_col H_row (L w)) D →
        (D.card : ℝ) ≤ (Fintype.card (Fin (entryBits d) → Bool) : ℝ) ^
          ((1 - δ₁) * (((d - d / 2) * (d / 2) : ℕ) : ℝ))

/-- **The uniform hypothesis implies the window-wise criterion**, with deficit `δ₁ / 2`. -/
theorem windowwise_of_uniformFarCellDeficit (L : ℕ → ℕ) (q : ℕ) (hq : 2 ≤ q) :
    UniformFarCellDeficit L q → WindowwiseFarCellCriterion := by
  rintro ⟨δ₁, hδ₁, hU⟩ k G c _ _ hc
  have hqpos : (0:ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  set μ : ℝ := min (δ₁ / 2) (1 / (q:ℝ)^2) with hμdef
  have hμ : 0 < μ := lt_min (by positivity) (by positivity)
  obtain ⟨θ, R, hθ, hT⟩ := exists_budgetRate_lt k G c (by omega) (show 0 < μ / 4 by positivity)
  set w : ℕ := endWindow k G θ + R + 1 with hw
  obtain ⟨d₂, hd₂⟩ := hU w
  refine ⟨R, q, θ, δ₁ / 2, hθ, hq, by positivity, hT, ?_⟩
  intro d₀
  set P : ℕ := w ^ (2 * L w + 1) with hP
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * (P:ℝ) / δ₁)
  refine ⟨max (max d₀ d₂) (2 * N + 4), (le_max_left _ _).trans (le_max_left _ _), ?_⟩
  set d : ℕ := max (max d₀ d₂) (2 * N + 4) with hd
  have hdd₂ : d₂ ≤ d := (le_max_right _ _).trans (le_max_left _ _)
  have hdN : 2 * N + 4 ≤ d := le_max_right _ _
  refine ⟨d / 2 * P, (1 - δ₁) * (((d - d / 2) * (d / 2) : ℕ) : ℝ), ?_, ?_⟩
  · exact farCellBoundAt_of_closeBall (L w)
      (fun H_col H_row hcol hrow hsym hE D hD => hd₂ d hdd₂ H_col H_row D hcol hrow hsym hE hD)
  · set n : ℕ := d - d / 2 with hn
    set m : ℕ := d / 2 with hm
    have hnN : N ≤ n := by omega
    have hNr : (N:ℝ) ≤ n := by exact_mod_cast hnN
    have hPn : 2 * (P:ℝ) < δ₁ * n := by
      have := (div_lt_iff₀ hδ₁).mp hN
      nlinarith
    have hm0 : (0:ℝ) ≤ m := by positivity
    have hmul : (m:ℝ) * (2 * P) ≤ (m:ℝ) * (δ₁ * n) := mul_le_mul_of_nonneg_left hPn.le hm0
    push_cast
    nlinarith

/-- **The uniform hypothesis implies the conjecture** (for every `q ≥ 2`). -/
theorem conjecture_of_uniformFarCellDeficit (L : ℕ → ℕ) (q : ℕ) (hq : 2 ≤ q) :
    UniformFarCellDeficit L q → LeanBacklog.Wall.Conjecture := fun h =>
  conjecture_of_farCellCriterion
    (farCellCriterion_of_windowwise (windowwise_of_uniformFarCellDeficit L q hq h))

#print axioms isTwoSidedExpander_ten_iff
#print axioms farCellBoundAt_trivial
#print axioms FarCellBoundAt.mono_e
#print axioms FarCellBoundAt.mono_v
#print axioms farCellBoundAt_of_closeBall
#print axioms bipartite_card_le_of_not_expander
#print axioms bipartite_card_le_of_farCellBoundAt
#print axioms normalized_bound_of_farCellBoundAt
#print axioms conjecture_of_farCellCriterion
#print axioms budget_lt_of_budgetRate_lt
#print axioms exists_budgetRate_lt
#print axioms farCellCriterion_of_windowwise
#print axioms windowwise_of_uniformFarCellDeficit
#print axioms conjecture_of_uniformFarCellDeficit

/-! ## The two-copy form -/

/-- Coordinatewise bitwise XOR on arrays of `k`-bit vectors. -/
def xorArr {n m k : ℕ}
    (x y : Fin n × Fin m → (Fin k → Bool)) : Fin n × Fin m → (Fin k → Bool) :=
  fun p t => Bool.xor (x p t) (y p t)

lemma xorArr_cancel_left {n m k : ℕ}
    (x y : Fin n × Fin m → (Fin k → Bool)) :
    xorArr x (xorArr x y) = y := by
  funext p t
  dsimp [xorArr]
  cases x p t <;> cases y p t <;> rfl

lemma xorArr_cancel_right {n m k : ℕ}
    (x y : Fin n × Fin m → (Fin k → Bool)) :
    xorArr (xorArr x y) y = x := by
  funext p t
  dsimp [xorArr]
  cases x p t <;> cases y p t <;> rfl

/-- Row-and-column permutation action `(σ, τ)` on rectangular arrays. -/
def permArr {n m : ℕ} {α : Type*}
    (σ : Equiv.Perm (Fin n)) (τ : Equiv.Perm (Fin m))
    (x : Fin n × Fin m → α) : Fin n × Fin m → α :=
  fun p => x (σ.symm p.1, τ.symm p.2)

lemma permArr_injective {n m : ℕ} {α : Type*}
    (σ : Equiv.Perm (Fin n)) (τ : Equiv.Perm (Fin m)) :
    Function.Injective (permArr σ τ : (Fin n × Fin m → α) → (Fin n × Fin m → α)) := by
  intro y₁ y₂ h
  funext ⟨b, a⟩
  have hba := congrFun h (σ b, τ a)
  simpa [permArr] using hba

/-- Conjugated column helper neighborhoods under `(σ, τ)`. -/
def conjCol {n m : ℕ}
    (σ : Equiv.Perm (Fin n)) (τ : Equiv.Perm (Fin m))
    (H_col : Fin m → Finset (Fin n)) : Fin m → Finset (Fin n) :=
  fun a => (H_col (τ.symm a)).image σ

/-- Conjugated row helper neighborhoods under `(σ, τ)`. -/
def conjRow {n m : ℕ}
    (σ : Equiv.Perm (Fin n)) (τ : Equiv.Perm (Fin m))
    (H_row : Fin n → Finset (Fin m)) : Fin n → Finset (Fin m) :=
  fun b => (H_row (σ.symm b)).image τ

/-- Two-copy nonlinear shifted-conjugation existence theorem:
for *any* bipartite two-sided code `D` over `k`-bit vectors and *any* chosen row/column
permutations `(σ, τ)`, there exists a translated intersection subcode `D' ⊆ D` that is
simultaneously two-sided whole-row for *both* `(H_col, H_row)` and `(conjCol σ τ H_col, conjRow σ τ H_row)`
satisfying `D.card ^ 2 ≤ (Fintype.card (Fin k → Bool)) ^ (n * m) * D'.card`. -/
theorem exists_shifted_conjugate_subcode {n m k : ℕ}
    (H_col : Fin m → Finset (Fin n)) (H_row : Fin n → Finset (Fin m))
    (D : Finset (Fin n × Fin m → (Fin k → Bool)))
    (hD : IsBipartiteTwoSidedCode H_col H_row D)
    (σ : Equiv.Perm (Fin n)) (τ : Equiv.Perm (Fin m)) :
    ∃ D' : Finset (Fin n × Fin m → (Fin k → Bool)),
      D' ⊆ D ∧
      IsBipartiteTwoSidedCode H_col H_row D' ∧
      IsBipartiteTwoSidedCode (conjCol σ τ H_col) (conjRow σ τ H_row) D' ∧
      D.card ^ 2 ≤ (Fintype.card (Fin k → Bool)) ^ (n * m) * D'.card := by
  let β := Fin k → Bool
  let diff : (Fin n × Fin m → β) × (Fin n × Fin m → β) → (Fin n × Fin m → β) :=
    fun xy => xorArr xy.1 (permArr σ τ xy.2)
  let pairFib : (Fin n × Fin m → β) → Finset ((Fin n × Fin m → β) × (Fin n × Fin m → β)) :=
    fun u => (D ×ˢ D).filter fun xy => diff xy = u
  let subCode : (Fin n × Fin m → β) → Finset (Fin n × Fin m → β) :=
    fun u => D.filter fun x => ∃ y ∈ D, diff (x, y) = u
  -- 1. Partition `D ×ˢ D` across offsets `u`
  have hpart : (D ×ˢ D).card = ∑ u : Fin n × Fin m → β, (pairFib u).card := by
    have hbij : D ×ˢ D = univ.biUnion pairFib := by
      ext xy; simp [pairFib]
    conv_lhs => rw [hbij]
    rw [card_biUnion]
    intro u₁ _ u₂ _ hne
    dsimp [Function.onFun]
    rw [disjoint_left]
    intro xy h₁ h₂
    simp only [pairFib, mem_filter] at h₁ h₂
    exact hne (h₁.2.symm.trans h₂.2)
  -- 2. For each `u`, `Prod.fst` maps `pairFib u` injectively into `subCode u`
  have hfib_le_sub : ∀ u, (pairFib u).card ≤ (subCode u).card := by
    intro u
    let fstMap : (Fin n × Fin m → β) × (Fin n × Fin m → β) → (Fin n × Fin m → β) := Prod.fst
    have hinj : Set.InjOn fstMap (pairFib u) := by
      intro ⟨x₁, y₁⟩ h₁ ⟨x₂, y₂⟩ h₂ hx_eq
      dsimp [fstMap] at hx_eq
      rw [mem_coe, mem_filter] at h₁ h₂
      have hd_eq : xorArr x₁ (permArr σ τ y₁) = xorArr x₁ (permArr σ τ y₂) := by
        have h1 := h₁.2
        have h2 := h₂.2
        dsimp [diff] at h1 h2
        rw [← hx_eq] at h2
        exact h1.trans h2.symm
      have hp_eq : permArr σ τ y₁ = permArr σ τ y₂ := by
        calc permArr σ τ y₁
            = xorArr x₁ (xorArr x₁ (permArr σ τ y₁)) := (xorArr_cancel_left _ _).symm
          _ = xorArr x₁ (xorArr x₁ (permArr σ τ y₂)) := by rw [hd_eq]
          _ = permArr σ τ y₂ := xorArr_cancel_left _ _
      exact Prod.ext hx_eq (permArr_injective σ τ hp_eq)
    have hsub : (pairFib u).image fstMap ⊆ subCode u := by
      intro x hx
      rcases mem_image.mp hx with ⟨⟨x', y'⟩, hxy, rfl⟩
      simp only [pairFib, mem_filter, mem_product] at hxy
      simp only [subCode, mem_filter]
      exact ⟨hxy.1.1, y', hxy.1.2, hxy.2⟩
    rw [← card_image_of_injOn hinj]
    exact card_le_card hsub
  -- 3. Every `subCode u` is two-sided whole-row for BOTH `(H_col, H_row)` and `(conjCol, conjRow)`!
  have hsub_valid : ∀ u,
      subCode u ⊆ D ∧
      IsBipartiteTwoSidedCode H_col H_row (subCode u) ∧
      IsBipartiteTwoSidedCode (conjCol σ τ H_col) (conjRow σ τ H_row) (subCode u) := by
    intro u
    refine ⟨filter_subset _ _, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · intro x₁ hx₁ x₂ hx₂ a hagree b
        exact hD.1 x₁ (mem_filter.mp hx₁).1 x₂ (mem_filter.mp hx₂).1 a hagree b
      · intro x₁ hx₁ x₂ hx₂ b hagree a
        exact hD.2 x₁ (mem_filter.mp hx₁).1 x₂ (mem_filter.mp hx₂).1 b hagree a
    · have hx_rep : ∀ x ∈ subCode u, ∃ y ∈ D, x = xorArr (permArr σ τ y) u := by
        intro x hx
        rcases (mem_filter.mp hx).2 with ⟨y, hy, hdiff⟩
        refine ⟨y, hy, ?_⟩
        dsimp [diff] at hdiff
        calc x = xorArr (xorArr x (permArr σ τ y)) (permArr σ τ y) := (xorArr_cancel_right _ _).symm
          _ = xorArr u (permArr σ τ y) := by rw [hdiff]
          _ = xorArr (permArr σ τ y) u := by
              funext p t; dsimp [xorArr]; exact Bool.xor_comm _ _
      refine ⟨?_, ?_⟩
      · intro x₁ hx₁ x₂ hx₂ a hagree b
        obtain ⟨y₁, hy₁, rfl⟩ := hx_rep x₁ hx₁
        obtain ⟨y₂, hy₂, rfl⟩ := hx_rep x₂ hx₂
        have hy_eq : y₁ (σ.symm b, τ.symm a) = y₂ (σ.symm b, τ.symm a) := by
          apply hD.1 y₁ hy₁ y₂ hy₂ (τ.symm a)
          intro b₀ hb₀ a₀
          have hmem : σ b₀ ∈ conjCol σ τ H_col a := mem_image_of_mem σ hb₀
          have hag := hagree (σ b₀) hmem (τ a₀)
          have hcan : permArr σ τ y₁ (σ b₀, τ a₀) = permArr σ τ y₂ (σ b₀, τ a₀) := by
            calc permArr σ τ y₁ (σ b₀, τ a₀)
                = xorArr (xorArr (permArr σ τ y₁) u) u (σ b₀, τ a₀) := by
                    rw [xorArr_cancel_right]
              _ = xorArr (xorArr (permArr σ τ y₂) u) u (σ b₀, τ a₀) := by
                    funext t
                    have ht := congrFun hag t
                    dsimp [xorArr] at ht ⊢
                    rw [ht]
              _ = permArr σ τ y₂ (σ b₀, τ a₀) := by rw [xorArr_cancel_right]
          simpa [permArr] using hcan
        funext t
        dsimp [xorArr, permArr]
        rw [hy_eq]
      · intro x₁ hx₁ x₂ hx₂ b hagree a
        obtain ⟨y₁, hy₁, rfl⟩ := hx_rep x₁ hx₁
        obtain ⟨y₂, hy₂, rfl⟩ := hx_rep x₂ hx₂
        have hy_eq : y₁ (σ.symm b, τ.symm a) = y₂ (σ.symm b, τ.symm a) := by
          apply hD.2 y₁ hy₁ y₂ hy₂ (σ.symm b)
          intro a₀ ha₀ b₀
          have hmem : τ a₀ ∈ conjRow σ τ H_row b := mem_image_of_mem τ ha₀
          have hag := hagree (τ a₀) hmem (σ b₀)
          have hcan : permArr σ τ y₁ (σ b₀, τ a₀) = permArr σ τ y₂ (σ b₀, τ a₀) := by
            calc permArr σ τ y₁ (σ b₀, τ a₀)
                = xorArr (xorArr (permArr σ τ y₁) u) u (σ b₀, τ a₀) := by
                    rw [xorArr_cancel_right]
              _ = xorArr (xorArr (permArr σ τ y₂) u) u (σ b₀, τ a₀) := by
                    funext t
                    have ht := congrFun hag t
                    dsimp [xorArr] at ht ⊢
                    rw [ht]
              _ = permArr σ τ y₂ (σ b₀, τ a₀) := by rw [xorArr_cancel_right]
          simpa [permArr] using hcan
        funext t
        dsimp [xorArr, permArr]
        rw [hy_eq]
  -- 4. Pick `u₀` maximizing `(subCode u).card` over the nonempty finite type `Fin n × Fin m → β`
  have hne : (univ : Finset (Fin n × Fin m → β)).Nonempty :=
    ⟨fun _ _ => false, mem_univ _⟩
  obtain ⟨u₀, _, hu₀_max⟩ := univ.exists_max_image (fun u => (subCode u).card) hne
  rcases hsub_valid u₀ with ⟨hsub₀, hvalid₁, hvalid₂⟩
  refine ⟨subCode u₀, hsub₀, hvalid₁, hvalid₂, ?_⟩
  have hsq : D.card ^ 2 = (D ×ˢ D).card := by simp [card_product, sq]
  rw [hsq, hpart]
  calc ∑ u : Fin n × Fin m → β, (pairFib u).card
      ≤ ∑ _u : Fin n × Fin m → β, (subCode u₀).card :=
        sum_le_sum fun u hu => (hfib_le_sub u).trans (hu₀_max u hu)
    _ = (univ : Finset (Fin n × Fin m → β)).card * (subCode u₀).card := by simp
    _ = (Fintype.card β) ^ (n * m) * (subCode u₀).card := by simp


/-- A pinned code is a bipartite two-sided code. -/
theorem IsPinnedBipartiteTwoSidedCode.toBipartite {n m : ℕ} {α : Type*}
    {H_col : Fin m → Finset (Fin n)} {H_row : Fin n → Finset (Fin m)}
    {E : Finset (Fin n × Fin m)} {D : Finset (Fin n × Fin m → α)}
    (hD : IsPinnedBipartiteTwoSidedCode H_col H_row E D) :
    IsBipartiteTwoSidedCode H_col H_row D := by
  refine ⟨?_, ?_⟩
  · intro x hx y hy a hagree b
    apply hD.2.1 x hx y hy a ?_ b
    intro b' hb' a' _
    exact hagree b' hb' a'
  · intro x hx y hy b hagree a
    apply hD.2.2 x hx y hy b ?_ a
    intro a' ha' b' _
    exact hagree a' ha' b'

/-- Subcodes of pinned codes are pinned codes. -/
theorem IsPinnedBipartiteTwoSidedCode.mono {n m : ℕ} {α : Type*}
    {H_col : Fin m → Finset (Fin n)} {H_row : Fin n → Finset (Fin m)}
    {E : Finset (Fin n × Fin m)} {D D' : Finset (Fin n × Fin m → α)}
    (hD : IsPinnedBipartiteTwoSidedCode H_col H_row E D) (hsub : D' ⊆ D) :
    IsPinnedBipartiteTwoSidedCode H_col H_row E D' :=
  ⟨fun x hx y hy => hD.1 x (hsub hx) y (hsub hy),
    fun x hx y hy => hD.2.1 x (hsub hx) y (hsub hy),
    fun x hx y hy => hD.2.2 x (hsub hx) y (hsub hy)⟩

/-- The two-copy far-cell bound at one size, over the alphabet `Fin b → Bool`. For every
admissible `q`-expanding host the prover may choose row and column permutations `σ`, `τ`
and a pin set `E` of at most `e` cells; codes that are pinned two-sided codes for the host
and two-sided codes for the conjugated host then have at most `|α| ^ v` words. -/
def TwoCopyFarCellBoundAt (b n m w q e : ℕ) (v : ℝ) : Prop :=
  ∀ (H_col : Fin m → Finset (Fin n)) (H_row : Fin n → Finset (Fin m)),
    (∀ a, (H_col a).card ≤ w) → (∀ b, (H_row b).card ≤ w) →
    (∀ a b, b ∈ H_col a ↔ a ∈ H_row b) →
    IsTwoSidedExpander q H_col H_row →
    ∃ (σ : Equiv.Perm (Fin n)) (τ : Equiv.Perm (Fin m)) (E : Finset (Fin n × Fin m)),
      E.card ≤ e ∧
      ∀ F : Finset (Fin n × Fin m → (Fin b → Bool)),
        IsPinnedBipartiteTwoSidedCode H_col H_row E F →
        IsBipartiteTwoSidedCode (conjCol σ τ H_col) (conjRow σ τ H_row) F →
          (F.card : ℝ) ≤ (Fintype.card (Fin b → Bool) : ℝ) ^ v

/-- Cells saved on the full array by a two-copy far-cell bound on an `n × m` quadrant. -/
noncomputable def twoCopyDeficit (n m q e : ℕ) (v : ℝ) : ℝ :=
  min (((n * m : ℝ) - v) / 2 - e) ((n * m : ℝ) / (q : ℝ) ^ 2)

/-- With `σ = τ = 1` the two-copy bound follows from the single-copy bound. -/
theorem twoCopyFarCellBoundAt_of_farCellBoundAt {b n m w q e : ℕ} {v : ℝ}
    (h : FarCellBoundAt (Fin b → Bool) n m w q e v) : TwoCopyFarCellBoundAt b n m w q e v := by
  intro H_col H_row hcol hrow hsym hE
  obtain ⟨E, hEc, hb⟩ := h H_col H_row hcol hrow hsym hE
  exact ⟨1, 1, E, hEc, fun F hF _ => hb F hF⟩

/-- Pointwise consequence for single codes: a pinned code `D` satisfies
`|D|² ≤ |α| ^ (n m) · |α| ^ v`. -/
theorem pinned_card_sq_le_of_twoCopy {b n m : ℕ} {v : ℝ}
    {H_col : Fin m → Finset (Fin n)} {H_row : Fin n → Finset (Fin m)}
    {E : Finset (Fin n × Fin m)} (σ : Equiv.Perm (Fin n)) (τ : Equiv.Perm (Fin m))
    (hb : ∀ F : Finset (Fin n × Fin m → (Fin b → Bool)),
        IsPinnedBipartiteTwoSidedCode H_col H_row E F →
        IsBipartiteTwoSidedCode (conjCol σ τ H_col) (conjRow σ τ H_row) F →
          (F.card : ℝ) ≤ (Fintype.card (Fin b → Bool) : ℝ) ^ v)
    (D : Finset (Fin n × Fin m → (Fin b → Bool)))
    (hD : IsPinnedBipartiteTwoSidedCode H_col H_row E D) :
    (D.card : ℝ) ^ 2 ≤ (Fintype.card (Fin b → Bool) : ℝ) ^ ((n * m : ℕ) : ℝ) *
      (Fintype.card (Fin b → Bool) : ℝ) ^ v := by
  obtain ⟨D', hsub, _, hD'₂, hsq⟩ :=
    exists_shifted_conjugate_subcode H_col H_row D hD.toBipartite σ τ
  have hF := hb D' (hD.mono hsub) hD'₂
  have hsq' : (D.card : ℝ) ^ 2 ≤
      (Fintype.card (Fin b → Bool) : ℝ) ^ (n * m) * (D'.card : ℝ) := by
    exact_mod_cast hsq
  rw [Real.rpow_natCast]
  exact hsq'.trans (mul_le_mul_of_nonneg_left hF (by positivity))

/-- The per-host form of the two-copy bound. -/
theorem bipartite_card_le_of_twoCopy {b n m w q e : ℕ} {v : ℝ}
    (hfar : TwoCopyFarCellBoundAt b n m w q e v)
    (H_col : Fin m → Finset (Fin n)) (H_row : Fin n → Finset (Fin m))
    (hcol : ∀ a, (H_col a).card ≤ w) (hrow : ∀ b, (H_row b).card ≤ w)
    (hsym : ∀ a b, b ∈ H_col a ↔ a ∈ H_row b)
    (D : Finset (Fin n × Fin m → (Fin b → Bool)))
    (hD : IsBipartiteTwoSidedCode H_col H_row D) :
    (D.card : ℝ) ≤ (Fintype.card (Fin b → Bool) : ℝ) ^
      ((n * m : ℝ) - twoCopyDeficit n m q e v) := by
  classical
  have hge1α : (1 : ℝ) ≤ (Fintype.card (Fin b → Bool) : ℝ) := by exact_mod_cast Fintype.card_pos
  set A : ℝ := (Fintype.card (Fin b → Bool) : ℝ) with hA
  have hposα : (0 : ℝ) < A := by linarith
  by_cases hE : IsTwoSidedExpander q H_col H_row
  · obtain ⟨σ, τ, E, hEc, hEb⟩ := hfar H_col H_row hcol hrow hsym hE
    have hhalf : ∀ F : Finset (Fin n × Fin m → (Fin b → Bool)),
        IsPinnedBipartiteTwoSidedCode H_col H_row E F →
          (F.card : ℝ) ≤ A ^ ((((n * m : ℕ) : ℝ) + v) / 2) := by
      intro F hF
      have hsq := pinned_card_sq_le_of_twoCopy σ τ hEb F hF
      rw [← Real.rpow_add hposα] at hsq
      have heq : A ^ (((n * m : ℕ) : ℝ) + v) = (A ^ ((((n * m : ℕ) : ℝ) + v) / 2)) ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hposα.le]
        norm_num
      rw [heq] at hsq
      have hnn : (0:ℝ) ≤ A ^ ((((n * m : ℕ) : ℝ) + v) / 2) := by positivity
      have hF0 : (0:ℝ) ≤ F.card := by positivity
      nlinarith [sq_nonneg ((F.card : ℝ) - A ^ ((((n * m : ℕ) : ℝ) + v) / 2))]
    have hpin := bipartite_card_le_of_pin_set H_col H_row D hD E _ hhalf
    rw [← Real.rpow_natCast, ← Real.rpow_add hposα] at hpin
    apply hpin.trans (Real.rpow_le_rpow_of_exponent_le hge1α ?_)
    have h1 : twoCopyDeficit n m q e v ≤ ((n * m : ℝ) - v) / 2 - e := min_le_left _ _
    have h2 : (E.card : ℝ) ≤ e := by exact_mod_cast hEc
    push_cast
    linarith
  · apply (bipartite_card_le_of_not_expander H_col H_row D hD hE).trans
      (Real.rpow_le_rpow_of_exponent_le hge1α ?_)
    have h1 : twoCopyDeficit n m q e v ≤ (n * m : ℝ) / (q : ℝ) ^ 2 := min_le_right _ _
    linarith

/-- Pointwise transfer of the two-copy bound to the full array. -/
theorem normalized_bound_of_twoCopy {b d m w q e : ℕ} {v : ℝ} (hm : m ≤ d)
    (hfar : TwoCopyFarCellBoundAt b (d - m) m w q e v) :
    NormalizedTwoSidedWholeRowCardinalityBound d w (Fin b → Bool)
      ((d:ℝ)^2 - twoCopyDeficit (d - m) m q e v) := by
  classical
  intro ρ C hρ hρ_sym _ hC
  have hge1α : (1 : ℝ) ≤ Fintype.card (Fin b → Bool) := by exact_mod_cast Fintype.card_pos
  have hposα : (0 : ℝ) < Fintype.card (Fin b → Bool) := by linarith
  have hsym_ind : ∀ (a : Fin m) (b : Fin (d - m)),
      b ∈ inducedColHelpers hm ρ a ↔ a ∈ inducedRowHelpers hm ρ b := by
    intro a b
    simp only [inducedColHelpers, inducedRowHelpers, mem_filter, mem_univ, true_and]
    exact hρ_sym ⟨a.1, by omega⟩ ⟨m + b.1, by omega⟩
  have hstep := twoSided_card_le_of_bipartite_quadrant hm ρ C hC
    ((Fintype.card (Fin b → Bool) : ℝ) ^
      ((((d - m : ℕ) : ℝ) * (m : ℝ)) - twoCopyDeficit (d - m) m q e v))
    (fun D hD => bipartite_card_le_of_twoCopy hfar _ _
      (card_inducedColHelpers_le hm ρ hρ) (card_inducedRowHelpers_le hm ρ hρ) hsym_ind D hD)
  rw [← Real.rpow_natCast, ← Real.rpow_add hposα] at hstep
  apply hstep.trans (le_of_eq ?_)
  congr 1
  have hsub_nat : (d - m) * m ≤ d * d := Nat.mul_le_mul (Nat.sub_le d m) hm
  rw [Nat.cast_sub hsub_nat]
  push_cast
  ring

/-- The far-cell criterion in two-copy form. -/
def TwoCopyFarCellCriterion : Prop :=
  ∀ k G c : ℕ, 5 ≤ k → 1 ≤ G → 4 ≤ c → ∀ d₀ : ℕ,
    ∃ (d R m q e : ℕ) (θ v : ℝ), max d₀ 1 ≤ d ∧ 0 < θ ∧ m ≤ d ∧ 1 ≤ q ∧
      TwoCopyFarCellBoundAt (entryBits d) (d - m) m (endWindow k G θ + R + 1) q e v ∧
      (2*(adaptiveAllowance k G c*d+cutBudget k G c d θ):ℕ) +
        (entryBits d*crossBudget d (endWindow k G θ) R:ℕ) <
          twoCopyDeficit (d - m) m q e v * (entryBits d : ℝ)

/-- **The two-copy criterion implies the conjecture.** -/
theorem conjecture_of_twoCopyFarCellCriterion (h : TwoCopyFarCellCriterion) :
    LeanBacklog.Wall.Conjecture := by
  intro k G c hk hG hc d₀
  obtain ⟨d, R, m, q, e, θ, v, hd, hθ, hm, _, hfar, hgap⟩ := h k G c hk hG hc d₀
  have hd1 : 1 ≤ d := (le_max_right _ _).trans hd
  have hdpos : (0:ℝ) < d := by exact_mod_cast hd1
  have hd2 : (d:ℝ)^2 ≠ 0 := by positivity
  refine ⟨d, R, θ, twoCopyDeficit (d - m) m q e v / (d:ℝ)^2, hd, hθ, ?_, ?_⟩
  · have hb := normalized_bound_of_twoCopy hm hfar
    have heq : (1 - twoCopyDeficit (d - m) m q e v / (d:ℝ)^2) * (d:ℝ)^2 =
        (d:ℝ)^2 - twoCopyDeficit (d - m) m q e v := by
      field_simp
    rw [heq]
    exact hb
  · have heq : twoCopyDeficit (d - m) m q e v / (d:ℝ)^2 * ((d*d*entryBits d:ℕ):ℝ) =
        twoCopyDeficit (d - m) m q e v * (entryBits d : ℝ) := by
      push_cast
      field_simp
    rw [heq]
    exact hgap

#print axioms exists_shifted_conjugate_subcode
#print axioms twoCopyFarCellBoundAt_of_farCellBoundAt
#print axioms pinned_card_sq_le_of_twoCopy
#print axioms bipartite_card_le_of_twoCopy
#print axioms normalized_bound_of_twoCopy
#print axioms conjecture_of_twoCopyFarCellCriterion

end LeanBacklog.WallFarCells
