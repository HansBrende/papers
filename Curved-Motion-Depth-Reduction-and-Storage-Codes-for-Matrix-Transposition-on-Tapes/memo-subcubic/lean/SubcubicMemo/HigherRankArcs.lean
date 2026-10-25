import SubcubicMemo.HigherRankCore

/-! High-rank arcs cannot terminate or branch in a positive-deficit core. -/

namespace SubcubicMemo.LowRank

open Module Finset LeanMachine.SubspaceRecovery LeanMachine.SubspaceDefect
open scoped BigOperators Classical

variable {V K W : Type*} [Fintype V] [DecidableEq V] [Field K]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  {G : SimpleGraph V} [DecidableRel G.Adj] {U : V → Submodule K W}
  {r : Recovery U} (c : HighCore G U r)
include c

/-- Every high port forces a non-reciprocal high successor. Four exterior
lines are counted at four distinct vertices, not assumed independent. -/
theorem HighCore.high_successor {v u : V} (hh : High r v u) :
    ∃ w, w ≠ v ∧ High r u w := by
  by_contra hn
  have hlow : ∀ w, w ≠ v → finrank K (LinearMap.range (r.component u w)) ≤ 1 := by
    intro w hw
    exact Nat.le_of_not_gt (fun h => hn ⟨w, hw, h⟩)
  obtain ⟨hv, hu, _, _⟩ := c.high_dimensions hh
  have hadj := c.high_adj hh
  obtain ⟨hvd, hvr⟩ := c.pair_row hv hadj (fun w hw => c.other_low hh hw)
  obtain ⟨hud, hur⟩ := c.pair_row hu hadj.symm hlow
  let S := U v ⊔ U u
  let A := (G.neighborFinset v).erase u
  let B := (G.neighborFinset u).erase v
  have hA : A.card = 2 := by
    simp [A, card_erase_of_mem ((G.mem_neighborFinset v u).mpr hadj), hvd]
  have hB : B.card = 2 := by
    simp [B, card_erase_of_mem ((G.mem_neighborFinset u v).mpr hadj.symm), hud]
  have hab : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro w hwA hwB
    have hvw := (G.mem_neighborFinset v w).mp (mem_erase.mp hwA).2
    have huw := (G.mem_neighborFinset u w).mp (mem_erase.mp hwB).2
    exact c.triangle {v, u, w}
      (SimpleGraph.is3Clique_triple_iff.mpr ⟨hadj, hvw, huw⟩)
  have hdim : finrank K S = 4 := by
    have hm := Submodule.finrank_sup_add_finrank_inf_eq (U v) (U u)
    rw [(c.disjoint hadj.ne).eq_bot, finrank_bot, hv, hu] at hm
    change finrank K (U v ⊔ U u : Submodule K W) = 4
    omega
  have hS : S ≠ ⊥ := by intro h; rw [h, finrank_bot] at hdim; omega
  let m : V → ℕ := fun w => (if w = v then 2 else 0) +
    (if w = u then 2 else 0) + (if w ∈ A then 1 else 0) + (if w ∈ B then 1 else 0)
  have hm : ∀ w, m w ≤ finrank K (U w ⊓ S : Submodule K W) := by
    intro w
    by_cases hwv : w = v
    · subst w
      rw [inf_eq_left.mpr (show U v ≤ S from le_sup_left), hv]
      simp [m, A, B, hadj.ne]
    by_cases hwu : w = u
    · subst w
      rw [inf_eq_left.mpr (show U u ≤ S from le_sup_right), hu]
      simp [m, A, B, hadj.ne.symm]
    by_cases hwA : w ∈ A
    · have hwB : w ∉ B := fun h => Finset.disjoint_left.mp hab hwA h
      have hi : LinearMap.range (r.component v w) ≤ U w ⊓ S :=
        le_inf (r.target v w) (hvr w hwA).2
      have hd := Submodule.finrank_mono hi
      rw [(hvr w hwA).1] at hd
      simpa only [m, ite_eq_right hwv, ite_eq_right hwu, ite_eq_left hwA,
        ite_eq_right hwB, zero_add, add_zero] using hd
    by_cases hwB : w ∈ B
    · have hi : LinearMap.range (r.component u w) ≤ U w ⊓ S :=
        le_inf (r.target u w) ((hur w hwB).2.trans_eq (sup_comm _ _))
      have hd := Submodule.finrank_mono hi
      rw [(hur w hwB).1] at hd
      simpa only [m, ite_eq_right hwv, ite_eq_right hwu, ite_eq_right hwA,
        ite_eq_left hwB, zero_add] using hd
    · simp [m, hwv, hwu, hwA, hwB]
  have hsum : ∑ w, m w = 8 := by
    have hAf : univ.filter (fun w => w ∈ A) = A := by ext; simp
    have hBf : univ.filter (fun w => w ∈ B) = B := by ext; simp
    simp only [m, sum_add_distrib, sum_ite_eq', mem_univ, ite_true,
      sum_boole, hAf, hBf, hA, hB]
    norm_num
  have hle := sum_le_sum (s := (univ : Finset V)) (fun w _ => hm w)
  have hmass := c.mass_bound hS
  rw [hsum] at hle
  rw [hdim] at hmass
  omega

end SubcubicMemo.LowRank
