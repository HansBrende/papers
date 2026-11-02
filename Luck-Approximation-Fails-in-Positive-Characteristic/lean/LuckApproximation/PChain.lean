import LeanMachine.FreeGroupResiduallyP
import LuckApproximation.Statement
import Mathlib.Order.CompletePartialOrder
import Mathlib.SetTheory.Cardinal.Free

/-!
# A `p`-chain below a given sequence of normal subgroups of `p`-power index

`Luck.exists_pChain_le`: for `r > 0` and any sequence `M 0, M 1, …` of normal subgroups of
`FreeGroup (Fin r)` of finite index with `p`-group quotients, there is a chain (strictly
decreasing, normal, finite index, trivial intersection) all of whose quotients are `p`-groups and
whose `j`-th term lies in `M j`.

## Construction

Enumerate the group as `e 0, e 1, …` and let `K n` be a normal subgroup of `p`-power index missing
`e n` when `e n ≠ 1` (residual `p`-finiteness; `K n = ⊤` when `e n = 1`). Put `A 0 = M 0` and let
`A (n+1)` be a normal subgroup of `p`-power index strictly below `A n ⊓ M (n+1) ⊓ K n`
(`LeanMachine.ResidualP.exists_goodP_lt`). Then `A` is strictly decreasing, `A j ≤ M j`, and every nontrivial
`g = e n` lies outside `A (n+1)`, so the intersection is trivial.
-/

namespace Luck

open LeanMachine LeanMachine.ResidualP

theorem exists_pChain_le (p : ℕ) [Fact p.Prime] (r : ℕ) (hr : 0 < r)
    (M : ℕ → Subgroup (FreeGroup (Fin r))) [∀ j, (M j).Normal] [∀ j, (M j).FiniteIndex]
    (hMp : ∀ j, IsPGroup p (FreeGroup (Fin r) ⧸ M j)) :
    ∃ c : Chain (FreeGroup (Fin r)),
      (∀ i, haveI := c.normal i; IsPGroup p (FreeGroup (Fin r) ⧸ c.N i)) ∧ ∀ j, c.N j ≤ M j := by
  classical
  obtain ⟨e, he⟩ := exists_surjective_nat (FreeGroup (Fin r))
  have hMgood : ∀ j, GoodP p (M j) := fun j =>
    goodP_of_residual inferInstance inferInstance (hMp j)
  have hK : ∀ n, ∃ K : Subgroup (FreeGroup (Fin r)), GoodP p K ∧ (e n ≠ 1 → e n ∉ K) := by
    intro n
    by_cases h : e n = 1
    · exact ⟨⊤, goodP_top p, fun h' => absurd h h'⟩
    · obtain ⟨K, hK1, hK2, hK3, hK4⟩ := freeGroup_residually_pGroup p r (e n) h
      exact ⟨K, goodP_of_residual hK1 hK2 hK3, fun _ => hK4⟩
  choose K hKgood hKe using hK
  have hstep : ∀ (n : ℕ) (X : {H : Subgroup (FreeGroup (Fin r)) // GoodP p H}),
      ∃ Y : {H : Subgroup (FreeGroup (Fin r)) // GoodP p H},
        Y.1 < X.1 ∧ Y.1 ≤ M (n + 1) ∧ Y.1 ≤ K n := by
    intro n X
    obtain ⟨Y, hY, hYlt⟩ := exists_goodP_lt p hr ((X.2.inf (hMgood (n + 1))).inf (hKgood n))
    exact ⟨⟨Y, hY⟩, lt_of_lt_of_le hYlt (inf_le_left.trans inf_le_left),
      hYlt.le.trans (inf_le_left.trans inf_le_right), hYlt.le.trans inf_le_right⟩
  choose f hf using hstep
  let A : ℕ → {H : Subgroup (FreeGroup (Fin r)) // GoodP p H} := fun m =>
    Nat.rec ⟨M 0, hMgood 0⟩ (fun m X => f m X) m
  have hA : ∀ m, (A (m + 1)).1 < (A m).1 ∧ (A (m + 1)).1 ≤ M (m + 1) ∧ (A (m + 1)).1 ≤ K m :=
    fun m => hf m (A m)
  refine ⟨⟨fun i => (A i).1, fun i => (A i).2.1, fun i => (A i).2.2.1, ?_, ?_⟩, ?_, ?_⟩
  · exact strictAnti_nat_of_succ_lt fun i => (hA i).1
  · rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_iInf] at hg
    rw [Subgroup.mem_bot]
    by_contra hg1
    obtain ⟨n, rfl⟩ := he g
    exact hKe n hg1 ((hA n).2.2 (hg (n + 1)))
  · intro i
    exact (@isPGroup_quotient_iff _ _ p (A i).1 (A i).2.1).mpr (A i).2.2.2
  · intro j
    cases j with
    | zero => exact le_rfl
    | succ m => exact (hA m).2.1

end Luck
