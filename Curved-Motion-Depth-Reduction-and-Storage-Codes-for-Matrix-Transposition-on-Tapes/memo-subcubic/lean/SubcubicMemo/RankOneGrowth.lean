import SubcubicMemo.RankOneGeometry

/-! Finite growth by exact pair extensions and plane-star absorptions. -/

namespace SubcubicMemo.LowRank

open Module Finset LeanMachine.SubspaceRecovery LeanMachine.SubspaceDefect
open scoped BigOperators Classical

variable {V K W : Type*} [Fintype V] [DecidableEq V] [Field K]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  {G : SimpleGraph V} [DecidableRel G.Adj] {U : V → Submodule K W}
  {r : Recovery U}

inductive Reachable (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : V → Submodule K W) (r : Recovery U) : Submodule K W → Prop
  | star {v : V} : finrank K (U v) = 2 → Reachable G U r (rowSpan r G v)
  | pair {S T} : Reachable G U r S → PairStep G U S T → Reachable G U r T
  | absorb {S v p} : Reachable G U r S → finrank K (U v) = 2 → G.Adj v p →
      S ⊓ rowSpan r G v = U p → Reachable G U r (S ⊔ rowSpan r G v)

variable (c : Core G U r)
include c

theorem Core.reachable_good {S : Submodule K W} (h : Reachable G U r S) : Good G U r S := by
  induction h with
  | star hv => exact c.good_star hv
  | pair _ h ih => exact c.good_pair ih h
  | absorb _ hv hp hmeet ih => exact (c.good_absorb ih hv hp hmeet).1

theorem Core.exists_maximal_reachable (hplane : ∃ v, finrank K (U v) = 2) :
    ∃ S : Submodule K W, Reachable G U r S ∧
      ∀ T : Submodule K W, Reachable G U r T → finrank K T ≤ finrank K S := by
  classical
  obtain ⟨v, hv⟩ := hplane
  let P : ℕ → Prop := fun n => ∃ S : Submodule K W, Reachable G U r S ∧ finrank K S = n
  have hex : P (finrank K (rowSpan r G v)) := ⟨_, .star hv, rfl⟩
  obtain ⟨S, hS, hdim⟩ := Nat.findGreatest_spec (P := P) (Submodule.finrank_le _) hex
  refine ⟨S, hS, ?_⟩
  intro T hT
  rw [hdim]
  exact Nat.le_findGreatest (P := P) (Submodule.finrank_le T) ⟨T, hT, rfl⟩

theorem Core.maximal_stars {S : Submodule K W} (hS : Reachable G U r S)
    (hmax : ∀ T : Submodule K W, Reachable G U r T → finrank K T ≤ finrank K S)
    {v : V} (hv : finrank K (U v) = 2) :
    rowSpan r G v ≤ S ∨ Disjoint S (rowSpan r G v) := by
  by_cases hle : rowSpan r G v ≤ S
  · exact Or.inl hle
  apply Or.inr
  by_contra hn
  have hmeet : S ⊓ rowSpan r G v ≠ ⊥ := fun h => hn (disjoint_iff.mpr h)
  obtain ⟨p, hp, heq⟩ := c.star_meet_axis (c.reachable_good hS) hv hle hmeet
  have hnew : Reachable G U r (S ⊔ rowSpan r G v) := .absorb hS hv hp heq
  have hdim := (c.good_absorb (c.reachable_good hS) hv hp heq).2
  have hm := hmax _ hnew
  omega

theorem Core.outside_neighbors_le_two {S : Submodule K W} (hS : Good G U r S)
    {v : V} (hv : finrank K (U v) = 1) (hknown : U v ≤ S) :
    ((G.neighborFinset v).filter (fun u => ¬ U u ≤ S)).card ≤ 2 := by
  classical
  obtain ⟨p, hp, hpS⟩ := hS.parent v hv hknown
  have hpN : p ∈ G.neighborFinset v := (G.mem_neighborFinset v p).mpr hp
  have hle : (G.neighborFinset v).filter (fun u => ¬ U u ≤ S) ⊆ (G.neighborFinset v).erase p := by
    intro u hu
    obtain ⟨huN, huS⟩ := mem_filter.mp hu
    exact mem_erase.mpr ⟨fun h => huS (h ▸ hpS), huN⟩
  have hcard := card_le_card hle
  rw [card_erase_of_mem hpN, SimpleGraph.card_neighborFinset_eq_degree] at hcard
  have hd := c.degree v
  omega

theorem Core.maximal_outside_line {S : Submodule K W} (hS : Reachable G U r S)
    (hmax : ∀ T : Submodule K W, Reachable G U r T → finrank K T ≤ finrank K S)
    {v u : V} (hv : finrank K (U v) = 1) (hknown : U v ≤ S)
    (hadj : G.Adj v u) (huS : ¬ U u ≤ S) (hu0 : U u ≠ ⊥) :
    finrank K (U u) = 1 := by
  have hd := c.dim_le_two u
  have hp : finrank K (U u) ≠ 0 := fun h => hu0 (Submodule.finrank_eq_zero.mp h)
  have hn : finrank K (U u) ≠ 2 := by
    intro htwo
    rcases c.maximal_stars hS hmax htwo with hle | hdisj
    · exact huS ((coordinate_le_rowSpan r c.support u).trans hle)
    · have hU : U v ≤ (⊥ : Submodule K W) :=
        (le_inf hknown (c.neighbor_le_star htwo hadj.symm)).trans_eq hdisj.eq_bot
      have hz := le_bot_iff.mp hU
      rw [hz, finrank_bot] at hv
      omega
  omega

/-- A maximal reachable subspace is closed under every supplied component
map. The proof uses actual row values, not only an entropy or support inequality. -/
theorem Core.maximal_closed {S : Submodule K W} (hS : Reachable G U r S)
    (hmax : ∀ T : Submodule K W, Reachable G U r T → finrank K T ≤ finrank K S) :
    ∀ v u (x : U v), (x : W) ∈ S → r.component v u x ∈ S := by
  have hg := c.reachable_good hS
  intro v u x hx
  by_cases hx0 : x = 0
  · rw [hx0, map_zero]; exact S.zero_mem
  have hv0 : U v ≠ ⊥ := by
    intro h
    have hz : (x : W) = 0 := by simpa only [h, Submodule.mem_bot] using x.property
    exact hx0 (Subtype.ext hz)
  have hvS : U v ≤ S := (hg.whole v).resolve_right (fun h => by
    apply hx0
    apply Subtype.ext
    change (x : W) = 0
    simpa only [h.eq_bot, Submodule.mem_bot] using
      (show (x : W) ∈ U v ⊓ S from ⟨x.property, hx⟩))
  have hd := c.dim_le_two v
  have hp : finrank K (U v) ≠ 0 := fun h => hv0 (Submodule.finrank_eq_zero.mp h)
  have hcases : finrank K (U v) = 1 ∨ finrank K (U v) = 2 := by omega
  rcases hcases with hv | hv
  · let F := (G.neighborFinset v).filter
      (fun w => ¬ U w ≤ S ∧ r.component v w x ≠ 0)
    have hF : F.card ≤ 2 := (card_le_card (show F ⊆
        (G.neighborFinset v).filter (fun w => ¬ U w ≤ S) from
      fun w hw => mem_filter.mpr ⟨(mem_filter.mp hw).1, (mem_filter.mp hw).2.1⟩)).trans
        (c.outside_neighbors_le_two hg hv hvS)
    have hrest : ∀ w ∉ F, r.component v w x ∈ S := by
      intro w hw
      by_cases ha : G.Adj v w
      · by_cases hknown : U w ≤ S
        · exact hknown (r.target v w (LinearMap.mem_range_self _ _))
        · have hz : r.component v w x = 0 := by
            by_contra hz
            exact hw (mem_filter.mpr ⟨(G.mem_neighborFinset v w).mpr ha, hknown, hz⟩)
          rw [hz]; exact S.zero_mem
      · rw [c.support v w ha, LinearMap.zero_apply]; exact S.zero_mem
    have hsum := r.partial_sum_mem v x S hx F hrest
    have hempty : F = ∅ := by
      by_contra hn
      have hcard : F.card = 1 ∨ F.card = 2 := by
        have hpos := card_pos.mpr (nonempty_iff_ne_empty.mpr hn)
        omega
      rcases hcard with hcard | hcard
      · obtain ⟨p, hFp⟩ := card_eq_one.mp hcard
        have hpF : p ∈ F := by rw [hFp]; simp
        obtain ⟨_, hpS, hp0⟩ := mem_filter.mp hpF
        have hmem : r.component v p x ∈ S := by simpa only [hFp, sum_singleton] using hsum
        have hdisj := (hg.whole p).resolve_left hpS
        apply hp0
        simpa only [hdisj.eq_bot, Submodule.mem_bot] using
          (show r.component v p x ∈ U p ⊓ S from
            ⟨r.target v p (LinearMap.mem_range_self _ _), hmem⟩)
      · obtain ⟨p, q, hpq, hFpq⟩ := card_eq_two.mp hcard
        have hpF : p ∈ F := by rw [hFpq]; simp
        have hqF : q ∈ F := by rw [hFpq]; simp
        obtain ⟨hpN, hpS, hp0⟩ := mem_filter.mp hpF
        obtain ⟨hqN, hqS, hq0⟩ := mem_filter.mp hqF
        have hvp := (G.mem_neighborFinset v p).mp hpN
        have hvq := (G.mem_neighborFinset v q).mp hqN
        have hUp0 : U p ≠ ⊥ := by
          intro h
          apply hp0
          simpa only [h, Submodule.mem_bot] using r.target v p (LinearMap.mem_range_self _ x)
        have hUq0 : U q ≠ ⊥ := by
          intro h
          apply hq0
          simpa only [h, Submodule.mem_bot] using r.target v q (LinearMap.mem_range_self _ x)
        have hdp := c.maximal_outside_line hS hmax hv hvS hvp hpS hUp0
        have hdq := c.maximal_outside_line hS hmax hv hvS hvq hqS hUq0
        have hab : r.component v p x + r.component v q x ∈ S := by
          simpa only [hFpq, sum_pair hpq] using hsum
        have hstep := c.make_pair hg hv hvS hvp hvq hpq hdp hdq hpS hqS
          (r.target v p (LinearMap.mem_range_self _ _))
          (r.target v q (LinearMap.mem_range_self _ _)) hq0 hab
        have hnew : Reachable G U r (S ⊔ U p) := .pair hS hstep
        have hmax' := hmax _ hnew
        have hdim := hstep.dimension
        omega
    exact hrest u (by rw [hempty]; simp)
  · by_cases hadj : G.Adj v u
    · exact (c.neighbor_le_star hv hadj).trans (hg.planes v hv hvS)
        (r.target v u (LinearMap.mem_range_self _ _))
    · rw [c.support v u hadj, LinearMap.zero_apply]; exact S.zero_mem

end SubcubicMemo.LowRank
