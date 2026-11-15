import LeanMachine.WholeRow.AcyclicOrder

/-!
# Averaging whole-row order bounds

The degree bound for arbitrary finite rectangular whole-row hosts. We count
orders in which a specified element is last in a finite set by exchanging
two labels. No probability, asymptotic limit, or alphabet assumption enters
the order theorem. Positions in `LiftOrder.cost` are one-based.
-/

namespace LeanMachine.WholeRow.OrderAverage

open Finset LiftOrder AcyclicOrder
open scoped BigOperators Classical
noncomputable section

variable {R J : Type*} [Fintype R] [Fintype J]

private abbrev Orders (R : Type*) [Fintype R] := R ≃ Fin (Fintype.card R)

private def lastOrders (S : Finset R) (x : R) : Finset (Orders R) :=
  univ.filter fun o => ∀ y ∈ S, (o y).val ≤ (o x).val

omit [Fintype R] in
private theorem swap_mem (S : Finset R) {x y z : R}
    (hx : x ∈ S) (hy : y ∈ S) (hz : z ∈ S) : Equiv.swap x y z ∈ S := by
  by_cases hzx : z = x
  · subst z; simpa using hy
  by_cases hzy : z = y
  · subst z; simpa using hx
  simpa [Equiv.swap_apply_of_ne_of_ne hzx hzy] using hz

private theorem lastOrders_card_eq (S : Finset R) {x y : R}
    (hx : x ∈ S) (hy : y ∈ S) : (lastOrders S x).card = (lastOrders S y).card := by
  have step : ∀ {x y : R}, x ∈ S → y ∈ S →
      (lastOrders S x).card ≤ (lastOrders S y).card := by
    intro x y hx hy
    apply card_le_card_of_injOn (fun o => (Equiv.swap x y).trans o)
    · intro o ho
      apply mem_filter.mpr
      refine ⟨mem_univ _, ?_⟩
      intro z hz
      simpa using (mem_filter.mp ho).2 _ (swap_mem S hx hy hz)
    · intro o _ p _ h
      apply Equiv.ext
      intro z
      have := congrArg (fun e : Orders R => e (Equiv.swap x y z)) h
      simpa using this
  exact le_antisymm (step hx hy) (step hy hx)

private theorem last_count (S : Finset R) {x : R} (hx : x ∈ S) :
    S.card * (lastOrders S x).card = Fintype.card (Orders R) := by
  have hmax (o : Orders R) :
      (S.filter fun z => ∀ y ∈ S, (o y).val ≤ (o z).val).card = 1 := by
    obtain ⟨z, hz, htop⟩ := S.exists_max_image (fun y => (o y).val) ⟨x, hx⟩
    apply card_eq_one.mpr
    refine ⟨z, ?_⟩
    ext y
    simp only [mem_filter, mem_singleton]
    constructor
    · rintro ⟨hy, h⟩
      exact o.injective (Fin.ext (le_antisymm (htop y hy) (h z hz)))
    · rintro rfl
      exact ⟨hz, htop⟩
  calc
    S.card * (lastOrders S x).card = ∑ y ∈ S, (lastOrders S y).card := by
      calc
        _ = ∑ _y ∈ S, (lastOrders S x).card := by simp
        _ = _ := sum_congr rfl fun y hy => lastOrders_card_eq S hx hy
    _ = ∑ o : Orders R, (S.filter fun z => ∀ y ∈ S, (o y).val ≤ (o z).val).card := by
      simp only [lastOrders, card_filter]
      rw [sum_comm]
    _ = Fintype.card (Orders R) := by
      simp only [hmax, sum_const, card_univ, smul_eq_mul, mul_one]

private def afterOrders (S : Finset R) (x : R) : Finset (Orders R) :=
  univ.filter fun o => S.sup (fun y => (o y).val + 1) < (o x).val + 1

private theorem after_count (S : Finset R) {x : R} (hx : x ∉ S) :
    (S.card + 1) * (afterOrders S x).card = Fintype.card (Orders R) := by
  have he : afterOrders S x = lastOrders (insert x S) x := by
    ext o
    simp only [afterOrders, lastOrders, mem_filter, mem_univ, true_and]
    constructor
    · intro h y hy
      rcases mem_insert.mp hy with rfl | hy
      · exact le_rfl
      · have := Finset.le_sup (f := fun y => (o y).val + 1) hy
        omega
    · intro h
      have hs : S.sup (fun y => (o y).val + 1) ≤ (o x).val := by
        apply Finset.sup_le
        intro y hy
        have hle := h y (mem_insert_of_mem hy)
        have hne : (o y).val ≠ (o x).val := by
          intro heq
          exact hx (o.injective (Fin.ext heq) ▸ hy)
        omega
      omega
  rw [he, ← card_insert_of_notMem hx]
  exact last_count _ (mem_insert_self _ _)

/-- A row order with the degree bound, retaining the actual incidence count.
The statement allows rectangular arrays, empty helper sets, and width zero. -/
theorem exists_order_incidence_bound (ρ : J → Finset R) (w : ℕ)
    (hw : ∀ j, (ρ j).card ≤ w) :
    ∃ o : R ≃ Fin (Fintype.card R),
      (w + 1) * cost ρ o ≤ w * Fintype.card R * Fintype.card J + ∑ j, (ρ j).card := by
  let M := Fintype.card (Orders R)
  have hcell (x : R × J) :
      M ≤ (w + 1) * (afterOrders (ρ x.2) x.1).card + if x.1 ∈ ρ x.2 then M else 0 := by
    by_cases hx : x.1 ∈ ρ x.2
    · simp only [hx, ↓reduceIte]
      omega
    · simp only [hx, ↓reduceIte, add_zero]
      exact (after_count (ρ x.2) hx).symm.le.trans
        (Nat.mul_le_mul_right _ (Nat.add_le_add_right (hw x.2) 1))
  have hsum := sum_le_sum (s := (univ : Finset (R × J))) (fun x _ => hcell x)
  have ha : ∑ x : R × J, (afterOrders (ρ x.2) x.1).card =
      ∑ o : Orders R, (rowSet ρ o).card := by
    simp only [afterOrders, rowSet, card_filter]
    rw [sum_comm]
  have hi : ∑ x : R × J, (if x.1 ∈ ρ x.2 then M else 0) = M * ∑ j, (ρ j).card := by
    rw [Fintype.sum_prod_type, sum_comm, mul_sum]
    apply sum_congr rfl
    intro j _
    simp [mul_comm]
  simp only [sum_add_distrib, ← mul_sum, sum_const, card_univ, Fintype.card_prod,
    smul_eq_mul, ha, hi] at hsum
  have hp : (∑ o : Orders R, (rowSet ρ o).card) + (∑ o : Orders R, cost ρ o) =
      M * (Fintype.card R * Fintype.card J) := by
    rw [← sum_add_distrib]
    simp only [rowSet_card_add_cost, sum_const, card_univ, smul_eq_mul, M]
  have hc : ∑ o : Orders R, (w + 1) * cost ρ o ≤
      ∑ _o : Orders R, (w * Fintype.card R * Fintype.card J + ∑ j, (ρ j).card) := by
    simp only [← mul_sum, sum_const, card_univ, smul_eq_mul]
    dsimp [M] at hsum hp ⊢
    nlinarith
  have : Nonempty (Orders R) := ⟨Fintype.equivFin R⟩
  obtain ⟨o, _, ho⟩ := exists_le_of_sum_le (s := univ) univ_nonempty hc
  exact ⟨o, ho⟩

/-- The degree bound in its usual form, for arbitrary rectangular arrays. -/
theorem exists_order_degree_bound (ρ : J → Finset R) (w : ℕ)
    (hw : ∀ j, (ρ j).card ≤ w) :
    ∃ o : R ≃ Fin (Fintype.card R),
      (w + 1) * cost ρ o ≤ w * Fintype.card J * (Fintype.card R + 1) := by
  obtain ⟨o, ho⟩ := exists_order_incidence_bound ρ w hw
  refine ⟨o, ho.trans ?_⟩
  have hs : ∑ j, (ρ j).card ≤ Fintype.card J * w := by
    simpa using sum_le_sum (s := univ) (fun j _ => hw j)
  nlinarith

/-- The same bound for the minimum order cost (the exact acyclic invoice). -/
theorem minimumCost_degree_bound (ρ : J → Finset R) (w : ℕ)
    (hw : ∀ j, (ρ j).card ≤ w) :
    (w + 1) * minimumCost ρ ≤ w * Fintype.card J * (Fintype.card R + 1) := by
  obtain ⟨o, ho⟩ := exists_order_degree_bound ρ w hw
  exact (Nat.mul_le_mul_left _ (minimumCost_le ρ o)).trans ho

end
end LeanMachine.WholeRow.OrderAverage

namespace LeanMachine.WholeRow.AcyclicOrder

/- Compatibility names for the formerly open `StatementsOrderWindow` targets. -/
alias exists_cost_window_le := OrderAverage.exists_order_degree_bound
alias minimumCost_window_le := OrderAverage.minimumCost_degree_bound

end LeanMachine.WholeRow.AcyclicOrder
