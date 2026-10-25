import SubcubicMemo.HigherRankExclusion
import SubcubicMemo.RankOneBound

/-! The arbitrary-width half theorem with at most one high port per row. -/

namespace SubcubicMemo.LowRank

open Module Finset LeanMachine.SubspaceRecovery LeanMachine.SubspaceDefect
open scoped BigOperators Classical

universe uV uK uW

variable {V : Type uV} {K : Type uK} {W : Type uW}
  [Fintype V] [DecidableEq V] [Field K]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  {G : SimpleGraph V} [DecidableRel G.Adj] {U : V → Submodule K W}

/-- Each row may contain one component of arbitrarily large rank, and the
original coordinate widths may be arbitrary and unequal. -/
theorem one_high_arrangement_half (r : Recovery U) (hs : Supported r G)
    (hr : AtMostOneHigh r) (hspan : (⨆ v, U v) = ⊤)
    (htri : G.CliqueFree 3) (hdeg : ∀ v, G.degree v ≤ 3) :
    2 * finrank K W ≤ ∑ v, finrank K (U v) := by
  suffices hall : ∀ (n : ℕ) (Z : Type uW) [AddCommGroup Z] [Module K Z]
      [FiniteDimensional K Z], finrank K Z = n →
      ∀ (A : V → Submodule K Z) (s : Recovery A),
        Supported s G → AtMostOneHigh s → (⨆ v, A v) = ⊤ →
          2 * finrank K Z ≤ ∑ v, finrank K (A v) by
    exact hall (finrank K W) W rfl U r hs hr hspan
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro Z _ _ _ hn A s hs hr hspan
    by_contra hbad
    have htop : 1 ≤ defect A ⊤ := by
      rw [defect_top, ← Nat.cast_sum]
      omega
    have hpos : ∀ S : Submodule K Z, S ≠ ⊥ → 1 ≤ defect A S := by
      intro S hS
      have hdim : 0 < finrank K S := by
        have hnz : finrank K S ≠ 0 := fun h => hS (Submodule.finrank_eq_zero.mp h)
        omega
      have hquotdim := S.finrank_quotient_add_finrank
      have hlt : finrank K (Z ⧸ S) < n := by omega
      obtain ⟨s', hs', hr'⟩ := image_one_high s hs hr S.mkQ
      have hspan' := image_span A S.mkQ S.mkQ_surjective hspan
      have hh := ih (finrank K (Z ⧸ S)) hlt (Z ⧸ S) rfl
        (fun v => (A v).map S.mkQ) s' hs' hr' hspan'
      exact htop.trans (deficit_of_quotient_half A S hh)
    let c : HighCore G A s := ⟨hs, hr, hdeg, htri, hpos⟩
    have hone : RankOne s := fun v u => Nat.le_of_not_gt (fun h => c.no_high h)
    exact hbad (rank_one_arrangement_half s hs hone hspan htri hdeg)

end SubcubicMemo.LowRank
