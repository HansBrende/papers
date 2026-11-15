import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.Order.Ring.Finset
import Mathlib.Tactic

/-!
# Row-order costs of rectangle-mixing lifts

Positions are numbered from one; an empty helper set has cost zero. This
module is finite and deterministic. It does not assert the existence of
mixing lifts. The companion `AcyclicOrder` module identifies the minimum
row-order cost with the best induced acyclic-set invoice.
-/

namespace LeanMachine.WholeRow.LiftOrder

open Finset
open scoped BigOperators Classical
noncomputable section

variable {R J B K : Type*} [Fintype R] [Fintype J] [Fintype B] [Fintype K]

/-- The sum of the last helper positions, with one-based positions. -/
def cost (ρ : J → Finset R) (o : R ≃ Fin (Fintype.card R)) : ℕ :=
  ∑ j, (ρ j).sup (fun x => (o x).val + 1)

/-- Every rectangle of at least `r` rows and `r` columns above a base
incidence contains a fine helper edge. No helper-containment premise is used. -/
def RectangleMixing (πR : R → B) (πJ : J → K)
    (ρ : J → Finset R) (ρ₀ : K → Finset B) (r : ℕ) : Prop :=
  ∀ b k, b ∈ ρ₀ k → ∀ X : Finset R, ∀ Y : Finset J,
    (∀ x ∈ X, πR x = b) → (∀ y ∈ Y, πJ y = k) →
    r ≤ X.card → r ≤ Y.card → ∃ x ∈ X, ∃ y ∈ Y, x ∈ ρ y

omit [Fintype R] [Fintype J] [Fintype B] [Fintype K] in
/-- It suffices to check rectangles of size exactly `r` on each side. -/
theorem rectangleMixing_iff_exact (πR : R → B) (πJ : J → K)
    (ρ : J → Finset R) (ρ₀ : K → Finset B) (r : ℕ) :
    RectangleMixing πR πJ ρ ρ₀ r ↔
      ∀ b k, b ∈ ρ₀ k → ∀ X : Finset R, ∀ Y : Finset J,
        (∀ x ∈ X, πR x = b) → (∀ y ∈ Y, πJ y = k) →
        X.card = r → Y.card = r → ∃ x ∈ X, ∃ y ∈ Y, x ∈ ρ y := by
  constructor
  · intro h b k hb X Y hX hY hcX hcY
    exact h b k hb X Y hX hY hcX.ge hcY.ge
  · intro h b k hb X Y hX hY hcX hcY
    obtain ⟨X', hX', heX⟩ := exists_subset_card_eq hcX
    obtain ⟨Y', hY', heY⟩ := exists_subset_card_eq hcY
    obtain ⟨x, hx, y, hy, hxy⟩ := h b k hb X' Y'
      (fun x hx => hX x (hX' hx)) (fun y hy => hY y (hY' hy)) heX heY
    exact ⟨x, hX' hx, y, hY' hy, hxy⟩

/-- The projection from a clone group has the advertised fibre cardinality. -/
theorem clone_group_card (n : ℕ) (b : B) :
    (univ.filter (fun x : B × Fin n => x.1 = b)).card = n := by
  have he : univ.filter (fun x : B × Fin n => x.1 = b) = ({b} : Finset B).product univ := by
    ext ⟨x, i⟩
    simp [Prod.ext_iff, eq_comm]
  rw [he]
  simp

omit [Fintype B] in
private theorem exists_arrival (π : R → B) (o : R ≃ Fin (Fintype.card R))
    (b : B) (a : ℕ) (ha : 0 < a)
    (hsize : a ≤ (univ.filter (fun x => π x = b)).card) :
    ∃ t : ℕ,
      a ≤ (univ.filter (fun x => π x = b ∧ (o x).val + 1 ≤ t)).card ∧
      (univ.filter (fun x => π x = b ∧ (o x).val + 1 < t)).card < a ∧
      ∃ x, π x = b ∧ (o x).val + 1 = t := by
  have hex : ∃ t : ℕ,
      a ≤ (univ.filter (fun x => π x = b ∧ (o x).val + 1 ≤ t)).card := by
    refine ⟨Fintype.card R, ?_⟩
    simpa only [Nat.add_one_le_iff, Fin.is_lt, and_true] using hsize
  let t := Nat.find hex
  have ht := Nat.find_spec hex
  change a ≤ (univ.filter (fun x => π x = b ∧ (o x).val + 1 ≤ t)).card at ht
  have hpos : 0 < t := by
    by_contra hn
    have hz : t = 0 := by omega
    simp [hz] at ht
    omega
  have hbefore : (univ.filter (fun x => π x = b ∧ (o x).val + 1 < t)).card < a := by
    have hmin := Nat.find_min hex (show t - 1 < t by omega)
    have he : (univ.filter (fun x => π x = b ∧ (o x).val + 1 ≤ t - 1)) =
        univ.filter (fun x => π x = b ∧ (o x).val + 1 < t) := by
      ext x
      simp only [mem_filter, mem_univ, true_and]
      exact and_congr_right (fun _ => by omega)
    rw [he] at hmin
    omega
  refine ⟨t, ht, hbefore, ?_⟩
  have hnot : ¬ (univ.filter (fun x => π x = b ∧ (o x).val + 1 ≤ t)) ⊆
      univ.filter (fun x => π x = b ∧ (o x).val + 1 < t) := by
    intro hs
    have := card_le_card hs
    omega
  obtain ⟨x, hx, hn⟩ := not_subset.mp hnot
  simp only [mem_filter, mem_univ, true_and] at hx hn
  have hn' : ¬ (o x).val + 1 < t := fun h => hn ⟨hx.1, h⟩
  exact ⟨x, hx.1, by omega⟩

private theorem ordered_thresholds (τ : B → ℕ) (hi : Function.Injective τ) :
    ∃ p : B ≃ Fin (Fintype.card B), ∀ b,
      (univ.filter (fun c => τ c ≤ τ b)).card = (p b).val + 1 := by
  let s := fun b => univ.filter (fun c => τ c < τ b)
  have hlt (b : B) : (s b).card < Fintype.card B := by
    have hs : s b ⊂ univ := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨subset_univ _, ?_⟩
      intro he
      have hb : b ∈ s b := he.symm ▸ mem_univ b
      simp [s] at hb
    simpa using card_lt_card hs
  let f : B → Fin (Fintype.card B) := fun b => ⟨(s b).card, hlt b⟩
  have hslt {b c : B} (h : τ b < τ c) : (s b).card < (s c).card := by
    apply card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
    · intro x hx
      exact mem_filter.mpr ⟨mem_univ _, lt_trans (mem_filter.mp hx).2 h⟩
    · intro he
      have hb : b ∈ s c := mem_filter.mpr ⟨mem_univ _, h⟩
      rw [← he] at hb
      simp [s] at hb
  have hf : Function.Injective f := by
    intro b c h
    have he : (s b).card = (s c).card := congrArg Fin.val h
    apply hi
    rcases lt_trichotomy (τ b) (τ c) with hlt | heq | hgt
    · have := hslt hlt; omega
    · exact heq
    · have := hslt hgt; omega
  let p : B ≃ Fin (Fintype.card B) := Equiv.ofBijective f
    ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, by simp⟩)
  refine ⟨p, fun b => ?_⟩
  have he : univ.filter (fun c => τ c ≤ τ b) = insert b (s b) := by
    ext c
    simp only [mem_filter, mem_univ, true_and, mem_insert, s]
    constructor
    · intro h
      rcases lt_or_eq_of_le h with hlt | heq
      · exact Or.inr hlt
      · exact Or.inl (hi heq)
    · rintro (rfl | h)
      · exact le_rfl
      · exact h.le
  rw [he, card_insert_of_notMem (by simp [s])]
  rfl

private theorem prefix_card_le (o : R ≃ Fin (Fintype.card R)) (t : ℕ) :
    (univ.filter (fun x => (o x).val + 1 ≤ t)).card ≤ t := by
  let S := univ.filter (fun x => (o x).val + 1 ≤ t)
  have hi : Function.Injective (fun x => (o x).val) := by
    intro x y h
    exact o.injective (Fin.ext h)
  calc
    S.card = (S.image (fun x => (o x).val)).card := (card_image_of_injective S hi).symm
    _ ≤ (range t).card := by
      apply card_le_card
      intro z hz
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hz
      exact mem_range.mpr (by have := (mem_filter.mp hx).2; omega)
    _ = t := card_range t

private theorem arrival_rank_bound (π : R → B) (o : R ≃ Fin (Fintype.card R))
    (a : ℕ) (τ : B → ℕ)
    (hτ : ∀ b, a ≤ (univ.filter (fun x => π x = b ∧ (o x).val + 1 ≤ τ b)).card)
    (p : B ≃ Fin (Fintype.card B))
    (hp : ∀ b, (univ.filter (fun c => τ c ≤ τ b)).card = (p b).val + 1) (b : B) :
    a * ((p b).val + 1) ≤ τ b := by
  let S := univ.filter (fun c => τ c ≤ τ b)
  let P := univ.filter (fun x => (o x).val + 1 ≤ τ b)
  have hc : ∀ c ∈ S, a ≤ (P.filter (fun x => π x = c)).card := by
    intro c hc
    apply (hτ c).trans
    apply card_le_card
    intro x hx
    obtain ⟨_, hx₁, hx₂⟩ := mem_filter.mp hx
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,
      hx₂.trans (mem_filter.mp hc).2⟩, hx₁⟩
  calc
    a * ((p b).val + 1) = ∑ _c ∈ S, a := by simp [S, hp, mul_comm]
    _ ≤ ∑ c ∈ S, (P.filter (fun x => π x = c)).card := sum_le_sum hc
    _ = (P.filter (fun x => π x ∈ S)).card := sum_card_fiberwise_eq_card_filter P S π
    _ ≤ P.card := card_le_card (filter_subset _ _)
    _ ≤ τ b := prefix_card_le o _

omit [Fintype B] [Fintype K] in
private theorem group_cost_ge_arrival
    (πR : R → B) (πJ : J → K) (ρ : J → Finset R) (ρ₀ : K → Finset B)
    (n r : ℕ) (hrn : r ≤ n)
    (hR : ∀ b, (univ.filter (fun x => πR x = b)).card = n)
    (hJ : ∀ k, (univ.filter (fun j => πJ j = k)).card = n)
    (hmix : RectangleMixing πR πJ ρ ρ₀ r)
    (o : R ≃ Fin (Fintype.card R)) (b : B) (k : K) (hb : b ∈ ρ₀ k) (t : ℕ)
    (hbefore : (univ.filter (fun x => πR x = b ∧ (o x).val + 1 < t)).card < n - r + 1) :
    (n - r + 1) * t ≤
      ∑ j ∈ univ.filter (fun j => πJ j = k), (ρ j).sup (fun x => (o x).val + 1) := by
  let X := univ.filter (fun x => πR x = b ∧ t ≤ (o x).val + 1)
  let F := univ.filter (fun j => πJ j = k)
  let f := fun j => (ρ j).sup (fun x => (o x).val + 1)
  let Y := F.filter (fun j => f j < t)
  let Z := F.filter (fun j => t ≤ f j)
  have hX : r ≤ X.card := by
    have hs := card_filter_add_card_filter_not (s := univ.filter (fun x => πR x = b))
      (fun x => (o x).val + 1 < t)
    simp only [filter_filter, not_lt, hR] at hs
    change (univ.filter (fun x => πR x = b ∧ (o x).val + 1 < t)).card + X.card = n at hs
    omega
  have hY : Y.card < r := by
    by_contra hn
    obtain ⟨x, hx, y, hy, hxy⟩ := hmix b k hb X Y
      (fun x hx => (mem_filter.mp hx).2.1)
      (fun y hy => (mem_filter.mp (mem_filter.mp hy).1).2) hX (by omega)
    have hx' := (mem_filter.mp hx).2.2
    have hy' := (mem_filter.mp hy).2
    have hf : (o x).val + 1 ≤ f y := Finset.le_sup (f := fun x => (o x).val + 1) hxy
    omega
  have hZ : n - r + 1 ≤ Z.card := by
    have hs := card_filter_add_card_filter_not (s := F) (fun j => f j < t)
    simp only [not_lt] at hs
    change Y.card + Z.card = F.card at hs
    have hF : F.card = n := hJ k
    omega
  calc
    (n - r + 1) * t ≤ Z.card * t := Nat.mul_le_mul_right _ hZ
    _ = ∑ _j ∈ Z, t := by simp
    _ ≤ ∑ j ∈ Z, f j := sum_le_sum (fun j hj => (mem_filter.mp hj).2)
    _ ≤ ∑ j ∈ F, f j := sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      (fun _ _ _ => Nat.zero_le _)

/-- Every fine row order induces a base row order with the stated cost lower
bound. The mixing is required separately above every base incidence. -/
theorem cost_ge_base_order
    (πR : R → B) (πJ : J → K) (ρ : J → Finset R) (ρ₀ : K → Finset B)
    (n r : ℕ) (hr : 1 ≤ r) (hrn : r ≤ n)
    (hR : ∀ b, (univ.filter (fun x => πR x = b)).card = n)
    (hJ : ∀ k, (univ.filter (fun j => πJ j = k)).card = n)
    (hmix : RectangleMixing πR πJ ρ ρ₀ r)
    (o : R ≃ Fin (Fintype.card R)) :
    ∃ p : B ≃ Fin (Fintype.card B), (n - r + 1)^2 * cost ρ₀ p ≤ cost ρ o := by
  let a := n - r + 1
  have ha : 0 < a := by dsimp [a]; omega
  have hex : ∀ b, ∃ t : ℕ,
      a ≤ (univ.filter (fun x => πR x = b ∧ (o x).val + 1 ≤ t)).card ∧
      (univ.filter (fun x => πR x = b ∧ (o x).val + 1 < t)).card < a ∧
      ∃ x, πR x = b ∧ (o x).val + 1 = t := by
    intro b
    exact exists_arrival πR o b a ha (by rw [hR]; dsimp [a]; omega)
  choose τ hτ hbefore hw using hex
  have hi : Function.Injective τ := by
    intro b c he
    obtain ⟨x, hx, hxt⟩ := hw b
    obtain ⟨y, hy, hyt⟩ := hw c
    have hxy : x = y := o.injective (Fin.ext (by omega))
    simpa [hxy, hy] using hx.symm
  obtain ⟨p, hp⟩ := ordered_thresholds τ hi
  refine ⟨p, ?_⟩
  have hgroup (k : K) : a^2 * (ρ₀ k).sup (fun b => (p b).val + 1) ≤
      ∑ j ∈ univ.filter (fun j => πJ j = k), (ρ j).sup (fun x => (o x).val + 1) := by
    rw [Finset.mul_sup₀]
    apply Finset.sup_le
    intro b hb
    have h₁ := arrival_rank_bound πR o a τ hτ p hp b
    have h₂ := group_cost_ge_arrival πR πJ ρ ρ₀ n r hrn hR hJ hmix o b k hb
      (τ b) (hbefore b)
    calc
      a^2 * ((p b).val + 1) = a * (a * ((p b).val + 1)) := by ring
      _ ≤ a * τ b := Nat.mul_le_mul_left a h₁
      _ ≤ _ := h₂
  calc
    (n - r + 1)^2 * cost ρ₀ p = ∑ k, a^2 * (ρ₀ k).sup (fun b => (p b).val + 1) := by
      simp only [cost, a, mul_sum]
    _ ≤ ∑ k, ∑ j ∈ univ.filter (fun j => πJ j = k),
        (ρ j).sup (fun x => (o x).val + 1) := sum_le_sum (fun k _ => hgroup k)
    _ = cost ρ o := by
      simpa only [cost] using sum_fiberwise_of_maps_to
        (s := (univ : Finset J)) (t := (univ : Finset K))
        (g := πJ) (f := fun j => (ρ j).sup (fun x => (o x).val + 1))
        (fun j _ => mem_univ (πJ j))

/-- A uniform base row-order lower bound transfers to every fine row order. -/
theorem cost_ge_of_base_bound
    (πR : R → B) (πJ : J → K) (ρ : J → Finset R) (ρ₀ : K → Finset B)
    (n r S : ℕ) (hr : 1 ≤ r) (hrn : r ≤ n)
    (hR : ∀ b, (univ.filter (fun x => πR x = b)).card = n)
    (hJ : ∀ k, (univ.filter (fun j => πJ j = k)).card = n)
    (hmix : RectangleMixing πR πJ ρ ρ₀ r)
    (hS : ∀ p : B ≃ Fin (Fintype.card B), S ≤ cost ρ₀ p)
    (o : R ≃ Fin (Fintype.card R)) : (n - r + 1)^2 * S ≤ cost ρ o := by
  obtain ⟨p, hp⟩ := cost_ge_base_order πR πJ ρ ρ₀ n r hr hrn hR hJ hmix o
  exact (Nat.mul_le_mul_left _ (hS p)).trans hp

/-- Visit whole clone groups contiguously in the supplied base order. -/
def cloneOrder (n : ℕ) (p : B ≃ Fin (Fintype.card B)) :
    (B × Fin n) ≃ Fin (Fintype.card (B × Fin n)) :=
  ((p.prodCongr (Equiv.refl (Fin n))).trans finProdFinEquiv).trans
    (finCongr (by simp))

private theorem cloneOrder_pos_le (n : ℕ) (p : B ≃ Fin (Fintype.card B))
    (x : B × Fin n) : (cloneOrder n p x).val + 1 ≤ n * ((p x.1).val + 1) := by
  change x.2.val + n * (p x.1).val + 1 ≤ n * ((p x.1).val + 1)
  have hx := x.2.isLt
  rw [Nat.mul_add, Nat.mul_one]
  omega

/-- Helper containment alone gives the matching upper comparison by ordering
clone groups contiguously. Mixing is unnecessary, and empty clones are allowed. -/
theorem cost_clone_order_le (n : ℕ) (ρ : (K × Fin n) → Finset (B × Fin n))
    (ρ₀ : K → Finset B) (hρ : ∀ j x, x ∈ ρ j → x.1 ∈ ρ₀ j.1)
    (p : B ≃ Fin (Fintype.card B)) : cost ρ (cloneOrder n p) ≤ n^2 * cost ρ₀ p := by
  have hb (j : K × Fin n) : (ρ j).sup (fun x => (cloneOrder n p x).val + 1) ≤
      n * (ρ₀ j.1).sup (fun b => (p b).val + 1) := by
    apply Finset.sup_le
    intro x hx
    exact (cloneOrder_pos_le n p x).trans (Nat.mul_le_mul_left n
      (Finset.le_sup (f := fun b => (p b).val + 1) (hρ j x hx)))
  calc
    cost ρ (cloneOrder n p) ≤ ∑ j : K × Fin n,
        n * (ρ₀ j.1).sup (fun b => (p b).val + 1) := sum_le_sum (fun j _ => hb j)
    _ = n^2 * cost ρ₀ p := by
      simp [Fintype.sum_prod_type, cost, pow_two, mul_sum, mul_assoc]

end
end LeanMachine.WholeRow.LiftOrder
