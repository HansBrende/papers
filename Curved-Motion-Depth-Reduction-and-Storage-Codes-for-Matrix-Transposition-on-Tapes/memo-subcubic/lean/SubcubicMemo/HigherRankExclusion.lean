import SubcubicMemo.HigherRankFourCycle

/-! A bounded high-rank path forces a closed K3,3 configuration. This avoids
classifying the whole high-arc graph, or assuming that it has no entering tails. -/

namespace SubcubicMemo.LowRank

open Module Finset LeanMachine.SubspaceRecovery LeanMachine.SubspaceDefect
open scoped BigOperators Classical

variable {V K W : Type*} [Fintype V] [DecidableEq V] [Field K]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  {G : SimpleGraph V} [DecidableRel G.Adj] {U : V → Submodule K W}
  {r : Recovery U} (c : HighCore G U r)
include c

theorem HighCore.path_four_ne {a b d e f : V}
    (hab : High r a b) (hbd : High r b d) (hde : High r d e) (hef : High r e f) : a ≠ f := by
  intro he
  exact c.no_high_four_cycle hab hbd hde (he.symm ▸ hef)

theorem HighCore.path_chord {p a b d e : V}
    (hpa : High r p a) (hab : High r a b) (hbd : High r b d) (hde : High r d e) :
    G.Adj a e :=
  (c.path_chord_or_four hpa hab hbd hde).resolve_left
    (fun he => c.path_four_ne hpa hab hbd hde he.symm)

theorem HighCore.neighbors_eq_three {v a b d : V}
    (ha : G.Adj v a) (hb : G.Adj v b) (hd : G.Adj v d)
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) :
    G.neighborFinset v = {a, b, d} := by
  have hsub : ({a, b, d} : Finset V) ⊆ G.neighborFinset v := by
    intro w hw
    simp only [mem_insert, mem_singleton] at hw
    rcases hw with hw | hw | hw
    · subst w; exact (G.mem_neighborFinset v a).mpr ha
    · subst w; exact (G.mem_neighborFinset v b).mpr hb
    · subst w; exact (G.mem_neighborFinset v d).mpr hd
  have hc : ({a, b, d} : Finset V).card = 3 := by simp [hab, had, hbd]
  exact (Finset.eq_of_subset_of_card_le hsub (by
    rw [hc, SimpleGraph.card_neighborFinset_eq_degree]
    exact c.degree v)).symm

/-- Seven consecutive high arcs already contradict positive deficit. -/
theorem HighCore.no_seven_path {a0 a1 a2 a3 a4 a5 a6 a7 : V}
    (h01 : High r a0 a1) (h12 : High r a1 a2) (h23 : High r a2 a3)
    (h34 : High r a3 a4) (h45 : High r a4 a5) (h56 : High r a5 a6)
    (h67 : High r a6 a7) : False := by
  have h14 := c.path_chord h01 h12 h23 h34
  have h25 := c.path_chord h12 h23 h34 h45
  have h36 := c.path_chord h23 h34 h45 h56
  have h47 := c.path_chord h34 h45 h56 h67
  have n13 := c.path_two_ne h12 h23
  have n15 := c.path_four_ne h12 h23 h34 h45
  have n35 := c.path_two_ne h34 h45
  have hN4 := c.neighbors_eq_three h14.symm (c.high_adj h34).symm
    (c.high_adj h45) n13 n15 n35
  have hclose : a7 = a1 := by
    have hm := (G.mem_neighborFinset a4 a7).mpr h47
    rw [hN4] at hm
    simp only [mem_insert, mem_singleton] at hm
    rcases hm with h | h | h
    · exact h
    · exact False.elim (c.path_four_ne h34 h45 h56 h67 h.symm)
    · exact False.elim (c.path_two_ne h56 h67 h.symm)
  have h61 : High r a6 a1 := hclose ▸ h67
  have n12 := (c.high_adj h12).ne
  have n14 := c.path_three_ne h12 h23 h34
  have n16 := (c.high_adj h61).ne.symm
  have n23 := (c.high_adj h23).ne
  have n24 := c.path_two_ne h23 h34
  have n25 := c.path_three_ne h23 h34 h45
  have n26 := c.path_four_ne h23 h34 h45 h56
  have n34 := (c.high_adj h34).ne
  have n36 := c.path_three_ne h34 h45 h56
  have n45 := (c.high_adj h45).ne
  have n46 := c.path_two_ne h45 h56
  have n56 := (c.high_adj h56).ne
  have hN2 := c.neighbors_eq_three (c.high_adj h12).symm (c.high_adj h23)
    h25 n13 n15 n35
  have hN6 := c.neighbors_eq_three (c.high_adj h61) h36.symm (c.high_adj h56).symm
    n13 n15 n35
  let S := (U a1 ⊔ U a3) ⊔ U a5
  have h1S : U a1 ≤ S := le_sup_left.trans le_sup_left
  have h3S : U a3 ≤ S := le_sup_right.trans le_sup_left
  have h5S : U a5 ≤ S := le_sup_right
  have hrow : ∀ v, G.neighborFinset v = {a1, a3, a5} → U v ≤ S := by
    intro v hv
    apply r.row_le v S
    intro w
    by_cases hw : G.Adj v w
    · have hm := (G.mem_neighborFinset v w).mpr hw
      rw [hv] at hm
      simp only [mem_insert, mem_singleton] at hm
      rcases hm with h | h | h
      · subst w; exact (r.target v a1).trans h1S
      · subst w; exact (r.target v a3).trans h3S
      · subst w; exact (r.target v a5).trans h5S
    · rw [c.support v w hw, LinearMap.range_zero]; exact bot_le
  have h2S := hrow a2 hN2
  have h4S := hrow a4 hN4
  have h6S := hrow a6 hN6
  let f : Fin 6 → V := ![a1, a2, a3, a4, a5, a6]
  have hf : Function.Injective f := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [f, Ne.symm]
  have hUS : ∀ i, U (f i) ≤ S := by
    intro i
    fin_cases i
    · exact h1S
    · exact h2S
    · exact h3S
    · exact h4S
    · exact h5S
    · exact h6S
  have hdim : ∀ i, finrank K (U (f i)) = 2 := by
    intro i
    fin_cases i
    · exact (c.high_dimensions h12).1
    · exact (c.high_dimensions h23).1
    · exact (c.high_dimensions h34).1
    · exact (c.high_dimensions h45).1
    · exact (c.high_dimensions h56).1
    · exact (c.high_dimensions h61).1
  have hmass := family_mass_le U S f hf (fun i => U (f i))
    (fun i => le_inf le_rfl (hUS i))
  simp_rw [hdim] at hmass
  have hmass12 : 12 ≤ ∑ v, finrank K (U v ⊓ S : Submodule K W) := by
    simpa using hmass
  have hSdim : finrank K S ≤ 6 := by
    have h1 := Submodule.finrank_add_le_finrank_add_finrank (U a1) (U a3)
    have h2 := Submodule.finrank_add_le_finrank_add_finrank (U a1 ⊔ U a3) (U a5)
    rw [(c.high_dimensions h12).1, (c.high_dimensions h34).1] at h1
    rw [(c.high_dimensions h56).1] at h2
    change finrank K ((U a1 ⊔ U a3) ⊔ U a5 : Submodule K W) ≤ 6
    omega
  have hS0 : S ≠ ⊥ := by
    intro hz
    have hbot : U a1 = ⊥ := le_bot_iff.mp (h1S.trans_eq hz)
    have hd := (c.high_dimensions h12).1
    rw [hbot, finrank_bot] at hd
    omega
  have hbudget := c.mass_bound hS0
  omega

/-- A positive-deficit one-high core has no high components at all. -/
theorem HighCore.no_high {a0 a1 : V} (h01 : High r a0 a1) : False := by
  obtain ⟨a2, _, h12⟩ := c.high_successor h01
  obtain ⟨a3, _, h23⟩ := c.high_successor h12
  obtain ⟨a4, _, h34⟩ := c.high_successor h23
  obtain ⟨a5, _, h45⟩ := c.high_successor h34
  obtain ⟨a6, _, h56⟩ := c.high_successor h45
  obtain ⟨a7, _, h67⟩ := c.high_successor h56
  exact c.no_seven_path h01 h12 h23 h34 h45 h56 h67

end SubcubicMemo.LowRank
