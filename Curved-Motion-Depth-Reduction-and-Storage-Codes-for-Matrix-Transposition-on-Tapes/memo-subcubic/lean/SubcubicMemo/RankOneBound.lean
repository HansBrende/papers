import SubcubicMemo.RankOneTerminal
import SubcubicMemo.ScalarArrangement

/-! The half bound for arbitrary-width rank-one recovery. Quotient induction
discharges the positive-deficit hypotheses of the geometric argument. -/

namespace SubcubicMemo.LowRank

open Module Finset LeanMachine.SubspaceRecovery LeanMachine.SubspaceDefect
open scoped BigOperators Classical

universe uV uK uW

variable {V : Type uV} {K : Type uK} {W : Type uW}
  [Fintype V] [DecidableEq V] [Field K]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  {G : SimpleGraph V} [DecidableRel G.Adj] {U : V → Submodule K W}
  {r : Recovery U}

/-- A positive-deficit core containing a plane has a strictly smaller tight
subspace on which the actual supplied recovery maps restrict. -/
theorem Core.exists_smaller_closed (c : Core G U r)
    (hplane : ∃ v, finrank K (U v) = 2) :
    ∃ S : Submodule K W, finrank K S < finrank K W ∧ Good G U r S ∧
      ∀ v u (x : U v), (x : W) ∈ S → r.component v u x ∈ S := by
  obtain ⟨S, hS, hmax⟩ := c.exists_maximal_reachable hplane
  by_cases htop : S = ⊤
  · cases hS with
    | star hv => exact False.elim (c.star_ne_top hv htop)
    | pair hprev hstep => exact False.elim (c.pair_ne_top hstep htop)
    | @absorb T v p hprev hv hp hmeet =>
      have hg := c.reachable_good hprev
      have hdim := (c.good_absorb hg hv hp hmeet).2
      rw [htop, finrank_top] at hdim
      exact ⟨T, by omega, hg, c.closed_before_final_absorption hg hv hp hmeet htop⟩
  · exact ⟨S, Submodule.finrank_lt htop, c.reachable_good hS,
      c.maximal_closed hS hmax⟩

/-- Rank-one ports suffice for the weighted half bound, over every field and
with arbitrary finite coordinate dimensions, including zero coordinates. -/
theorem rank_one_arrangement_half (r : Recovery U) (hs : Supported r G)
    (hr : RankOne r) (hspan : (⨆ v, U v) = ⊤)
    (htri : G.CliqueFree 3) (hdeg : ∀ v, G.degree v ≤ 3) :
    2 * finrank K W ≤ ∑ v, finrank K (U v) := by
  suffices hall : ∀ (n : ℕ) (Z : Type uW) [AddCommGroup Z] [Module K Z]
      [FiniteDimensional K Z], finrank K Z = n →
      ∀ (A : V → Submodule K Z) (s : Recovery A),
        Supported s G → RankOne s → (⨆ v, A v) = ⊤ →
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
      obtain ⟨s', hs', hr'⟩ := image_rank_one s hs hr S.mkQ
      have hspan' := image_span A S.mkQ S.mkQ_surjective hspan
      have hh := ih (finrank K (Z ⧸ S)) hlt (Z ⧸ S) rfl
        (fun v => (A v).map S.mkQ) s' hs' hr' hspan'
      exact htop.trans (deficit_of_quotient_half A S hh)
    let c : Core G A s := ⟨hs, hr, hdeg, htri, hpos⟩
    by_cases hplane : ∃ v, finrank K (A v) = 2
    · obtain ⟨S, hlt, hg, hclosed⟩ := c.exists_smaller_closed hplane
      obtain ⟨s', hz, hdim⟩ := s.restrict S hclosed
      have hs' : Supported s' G := fun v u h => hz v u (hs v u h)
      have hr' : RankOne s' := fun v u => (hdim v u).trans (hr v u)
      have hspan' := restricted_span A S (tight_spanned A hpos hg.tight)
      have hh := ih (finrank K S) (by omega) S rfl
        (fun v => (A v).comap S.subtype) s' hs' hr' hspan'
      simp_rw [restriction_dimension] at hh
      have ht := hg.tight
      unfold defect at ht
      rw [← Nat.cast_sum] at ht
      omega
    · have hlines : ∀ v, finrank K (A v) ≤ 1 := by
        intro v
        have hd := c.dim_le_two v
        have hne : finrank K (A v) ≠ 2 := fun h => hplane ⟨v, h⟩
        omega
      exact hbad (scalar_arrangement_half s hs hspan hlines htri hdeg)

end SubcubicMemo.LowRank
