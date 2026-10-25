import SubcubicMemo.RankOneGrowth

/-! Excluding a growth sequence that first finishes at the entire ambient space. -/

namespace SubcubicMemo.LowRank

open Module Finset LeanMachine.SubspaceRecovery LeanMachine.SubspaceDefect
open scoped BigOperators Classical

variable {V K W : Type*} [Fintype V] [DecidableEq V] [Field K]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  {G : SimpleGraph V} [DecidableRel G.Adj] {U : V → Submodule K W}
  {r : Recovery U} (c : Core G U r)
include c

theorem Core.star_ne_top {v : V} (hv : finrank K (U v) = 2) :
    rowSpan r G v ≠ ⊤ := by
  intro htop
  have hdegree := (plane_row_dimensions r c.support c.one c.degree c.positive hv).1
  have hcard : (G.neighborFinset v).card = 3 := by simpa using hdegree
  obtain ⟨p, hpN⟩ := card_pos.mp (by omega : 0 < (G.neighborFinset v).card)
  have hp := (G.mem_neighborFinset v p).mp hpN
  have hd := c.plane_neighbor_line hv hp
  have hle : U p ≤ U v := by
    apply r.row_le p (U v)
    intro u
    by_cases huv : u = v
    · subst u
      exact r.target p v
    by_cases hadj : G.Adj p u
    · have hnot : ¬ G.Adj v u := by
        intro h
        exact c.triangle {v, p, u} (SimpleGraph.is3Clique_triple_iff.mpr ⟨hp, h, hadj⟩)
      have hz := c.star_intersection hv u
      rw [htop, inf_top_eq, ite_eq_right (not_or.mpr ⟨huv, hnot⟩)] at hz
      exact (r.target p u).trans (hz.le.trans bot_le)
    · rw [c.support p u hadj, LinearMap.range_zero]
      exact bot_le
  have hz : U p = ⊥ := (inf_eq_left.mpr hle).symm.trans (c.disjoint hp.ne.symm).eq_bot
  rw [hz, finrank_bot] at hd
  omega

theorem Core.pair_ne_top {S T : Submodule K W} (h : PairStep G U S T) : T ≠ ⊤ := by
  intro htop
  obtain ⟨v, p, q, hpq, hv, hvS, hvp, hvq, hp, hq, hpS, hqS, hi⟩ := h.witnesses
  have hpqNot : ¬ G.Adj p q := by
    intro h
    exact c.triangle {v, p, q} (SimpleGraph.is3Clique_triple_iff.mpr ⟨hvp, hvq, h⟩)
  apply hpS
  apply r.row_le p S
  intro u
  by_cases hup : u = p
  · subst u
    rw [c.support.diagonal, LinearMap.range_zero]
    exact bot_le
  by_cases huq : u = q
  · subst u
    rw [c.support p q hpqNot, LinearMap.range_zero]
    exact bot_le
  have heq := hi u
  rw [htop, inf_top_eq, ite_eq_right (not_or.mpr ⟨hup, huq⟩)] at heq
  exact (r.target p u).trans (inf_eq_left.mp heq.symm)

/-- The two unshared axes of an absorbed star are independent modulo the old
space. This is derived from the exact three-dimensional star, not assumed. -/
theorem Core.absorption_axes {S : Submodule K W} {v p : V}
    (hv : finrank K (U v) = 2) (hp : G.Adj v p)
    (hmeet : S ⊓ rowSpan r G v = U p) :
    ∃ q t, q ≠ p ∧ t ≠ p ∧ q ≠ t ∧ G.neighborFinset v = {p, q, t} ∧
      Disjoint S (U q ⊔ U t) := by
  have hdegree := (plane_row_dimensions r c.support c.one c.degree c.positive hv).1
  have hcard : (G.neighborFinset v).card = 3 := by simpa using hdegree
  have hpN : p ∈ G.neighborFinset v := (G.mem_neighborFinset v p).mpr hp
  have herase : ((G.neighborFinset v).erase p).card = 2 := by
    rw [card_erase_of_mem hpN, hcard]
  obtain ⟨q, t, hqt, hF⟩ := card_eq_two.mp herase
  have hqN : q ∈ (G.neighborFinset v).erase p := by rw [hF]; simp
  have htN : t ∈ (G.neighborFinset v).erase p := by rw [hF]; simp
  obtain ⟨hqp, hq⟩ := mem_erase.mp hqN
  obtain ⟨htp, ht⟩ := mem_erase.mp htN
  have hN : G.neighborFinset v = {p, q, t} := by
    rw [← insert_erase hpN, hF]
  have hqAdj := (G.mem_neighborFinset v q).mp hq
  have htAdj := (G.mem_neighborFinset v t).mp ht
  let D := U q ⊔ U t
  have hK : rowSpan r G v = U p ⊔ D := by
    change (G.neighborFinset v).sup (fun u => LinearMap.range (r.component v u)) = _
    calc
      _ = (G.neighborFinset v).sup U := Finset.sup_congr rfl
        (fun u hu => c.plane_port_eq hv ((G.mem_neighborFinset v u).mp hu))
      _ = _ := by rw [hN]; simp [D]
  have hD : finrank K D ≤ 2 := by
    have h := Submodule.finrank_add_le_finrank_add_finrank (U q) (U t)
    rw [c.plane_neighbor_line hv hqAdj, c.plane_neighbor_line hv htAdj] at h
    exact h
  have hm := Submodule.finrank_sup_add_finrank_inf_eq (U p) D
  rw [← hK, c.star_dimension hv, c.plane_neighbor_line hv hp] at hm
  have hz : U p ⊓ D = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
  have hDle : D ≤ rowSpan r G v := by rw [hK]; exact le_sup_right
  refine ⟨q, t, hqp, htp, hqt, hN, disjoint_iff.mpr ?_⟩
  apply le_bot_iff.mp
  calc
    S ⊓ D ≤ (S ⊓ rowSpan r G v) ⊓ D :=
      le_inf (inf_le_inf_left _ hDle) inf_le_right
    _ = ⊥ := by rw [hmeet, hz]

/-- If an absorption finishes the ambient space, the previous space was already
closed. This is the terminal obstruction used by dimension induction. -/
theorem Core.closed_before_final_absorption {S : Submodule K W} (hS : Good G U r S)
    {v p : V} (hv : finrank K (U v) = 2) (hp : G.Adj v p)
    (hmeet : S ⊓ rowSpan r G v = U p) (htop : S ⊔ rowSpan r G v = ⊤) :
    ∀ w u (x : U w), (x : W) ∈ S → r.component w u x ∈ S := by
  obtain ⟨q, t, hqp, htp, hqt, hN, hdisj⟩ := c.absorption_axes hv hp hmeet
  have hqN : q ∈ G.neighborFinset v := by rw [hN]; simp
  have htN : t ∈ G.neighborFinset v := by rw [hN]; simp
  have hqAdj := (G.mem_neighborFinset v q).mp hqN
  have htAdj := (G.mem_neighborFinset v t).mp htN
  have hqDim := c.plane_neighbor_line hv hqAdj
  have htDim := c.plane_neighbor_line hv htAdj
  have hpS : U p ≤ S := by rw [← hmeet]; exact inf_le_left
  have hqS : ¬ U q ≤ S := by
    intro h
    have hz : U q ≤ (⊥ : Submodule K W) := (le_inf h le_sup_left).trans_eq hdisj.eq_bot
    rw [le_bot_iff.mp hz, finrank_bot] at hqDim
    omega
  have htS : ¬ U t ≤ S := by
    intro h
    have hz : U t ≤ (⊥ : Submodule K W) := (le_inf h le_sup_right).trans_eq hdisj.eq_bot
    rw [le_bot_iff.mp hz, finrank_bot] at htDim
    omega
  have hmeet0 : S ⊓ rowSpan r G v ≠ ⊥ := by
    rw [hmeet]
    intro hz
    have hdim := c.plane_neighbor_line hv hp
    rw [hz, finrank_bot] at hdim
    omega
  have hjoin := (c.whole_tight_join hS.whole (c.star_whole hv)
    hS.tight (c.star_tight hv) hmeet0).2
  have hout : ∀ u, ¬ U u ≤ S → u = v ∨ u = q ∨ u = t := by
    intro u hu
    have hU : U u ≤ S ⊔ rowSpan r G v := by rw [htop]; exact le_top
    have hstar := ((hjoin u).mp hU).resolve_left hu
    have heq := c.star_intersection hv u
    rw [inf_eq_left.mpr hstar] at heq
    by_cases hwhich : u = v ∨ G.Adj v u
    · rcases hwhich with h | h
      · exact Or.inl h
      · have hmem := (G.mem_neighborFinset v u).mpr h
        rw [hN] at hmem
        simp only [mem_insert, mem_singleton] at hmem
        rcases hmem with rfl | hq | ht
        · exact False.elim (hu hpS)
        · exact Or.inr (Or.inl hq)
        · exact Or.inr (Or.inr ht)
    · rw [ite_eq_right hwhich] at heq
      exact False.elim (hu (heq.le.trans bot_le))
  intro w u x hx
  by_cases hx0 : x = 0
  · rw [hx0, map_zero]; exact S.zero_mem
  have hwS : U w ≤ S := (hS.whole w).resolve_right (fun h => by
    apply hx0
    apply Subtype.ext
    change (x : W) = 0
    simpa only [h.eq_bot, Submodule.mem_bot] using
      (show (x : W) ∈ U w ⊓ S from ⟨x.property, hx⟩))
  have hw0 : U w ≠ ⊥ := by
    intro hz
    apply hx0
    apply Subtype.ext
    change (x : W) = 0
    simpa only [hz, Submodule.mem_bot] using x.property
  have hd := c.dim_le_two w
  have hn : finrank K (U w) ≠ 0 := fun h => hw0 (Submodule.finrank_eq_zero.mp h)
  have hcases : finrank K (U w) = 1 ∨ finrank K (U w) = 2 := by omega
  rcases hcases with hw | hw
  · by_cases hwp : w = p
    · subst w
      have hrest : ∀ j, j ≠ v → r.component p j x ∈ S := by
        intro j hjv
        by_cases hjS : U j ≤ S
        · exact hjS (r.target p j (LinearMap.mem_range_self _ _))
        · rcases hout j hjS with hj | hj | hj
          · exact False.elim (hjv hj)
          · subst j
            have hnot : ¬ G.Adj p q := fun h => c.triangle {v, p, q}
              (SimpleGraph.is3Clique_triple_iff.mpr ⟨hp, hqAdj, h⟩)
            rw [c.support p q hnot, LinearMap.zero_apply]; exact S.zero_mem
          · subst j
            have hnot : ¬ G.Adj p t := fun h => c.triangle {v, p, t}
              (SimpleGraph.is3Clique_triple_iff.mpr ⟨hp, htAdj, h⟩)
            rw [c.support p t hnot, LinearMap.zero_apply]; exact S.zero_mem
      by_cases huv : u = v
      · subst u
        simpa only [sum_singleton] using r.partial_sum_mem p x S hx {v}
          (fun j hj => hrest j (by simpa using hj))
      · exact hrest u huv
    · have hwv : ¬ G.Adj w v := by
        intro h
        have hmem := (G.mem_neighborFinset v w).mpr h.symm
        rw [hN] at hmem
        simp only [mem_insert, mem_singleton] at hmem
        rcases hmem with h | rfl | rfl
        · exact hwp h
        · exact hqS hwS
        · exact htS hwS
      have hrest : ∀ j ∉ ({q, t} : Finset V), r.component w j x ∈ S := by
        intro j hj
        by_cases hjS : U j ≤ S
        · exact hjS (r.target w j (LinearMap.mem_range_self _ _))
        · rcases hout j hjS with hjv | hjq | hjt
          · subst j
            rw [c.support w v hwv, LinearMap.zero_apply]; exact S.zero_mem
          · exact False.elim (hj (by simp [hjq]))
          · exact False.elim (hj (by simp [hjt]))
      have hsum : r.component w q x + r.component w t x ∈ S := by
        simpa only [sum_pair hqt] using r.partial_sum_mem w x S hx {q, t} hrest
      have ha := r.target w q (LinearMap.mem_range_self _ x)
      have hb := r.target w t (LinearMap.mem_range_self _ x)
      have hD : r.component w q x + r.component w t x ∈ U q ⊔ U t :=
        Submodule.add_mem_sup ha hb
      have hzero : r.component w q x + r.component w t x = 0 := by
        simpa only [hdisj.eq_bot, Submodule.mem_bot] using
          (show r.component w q x + r.component w t x ∈ S ⊓ (U q ⊔ U t) from ⟨hsum, hD⟩)
      have haT : r.component w q x ∈ U t := by
        rw [eq_neg_of_add_eq_zero_left hzero]
        exact (U t).neg_mem hb
      have ha0 : r.component w q x = 0 := by
        simpa only [(c.disjoint hqt).eq_bot, Submodule.mem_bot] using
          (show r.component w q x ∈ U q ⊓ U t from ⟨ha, haT⟩)
      have hb0 : r.component w t x = 0 := by simpa only [ha0, zero_add] using hzero
      by_cases huq : u = q
      · subst u; rw [ha0]; exact S.zero_mem
      by_cases hut : u = t
      · subst u; rw [hb0]; exact S.zero_mem
      exact hrest u (by simp [huq, hut])
  · by_cases hadj : G.Adj w u
    · exact (c.neighbor_le_star hw hadj).trans (hS.planes w hw hwS)
        (r.target w u (LinearMap.mem_range_self _ _))
    · rw [c.support w u hadj, LinearMap.zero_apply]; exact S.zero_mem

end SubcubicMemo.LowRank
