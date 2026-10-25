import SubcubicMemo.HigherRankPropagation
import LeanMachine.SubspaceGains

/-! Four-cycle exclusion, allowing repeated external vertices. Three distinct
coordinate gains already contradict the tight one-dimensional extension. -/

namespace SubcubicMemo.LowRank

open Module Finset LeanMachine.SubspaceRecovery LeanMachine.SubspaceDefect
open scoped BigOperators Classical

variable {V K W : Type*} [Fintype V] [DecidableEq V] [Field K]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  {G : SimpleGraph V} [DecidableRel G.Adj] {U : V → Submodule K W}
  {r : Recovery U} (c : HighCore G U r)
include c

theorem HighCore.no_high_four_cycle {a b d e : V}
    (hab : High r a b) (hbd : High r b d) (hde : High r d e) (hea : High r e a) : False := by
  obtain ⟨z0, h0e, h0b, h0a, hN0⟩ := c.third_neighbor hea hab
  obtain ⟨z1, h1a, h1d, h1b, hN1⟩ := c.third_neighbor hab hbd
  obtain ⟨z2, h2b, h2e, h2d, hN2⟩ := c.third_neighbor hbd hde
  obtain ⟨z3, h3d, h3a, h3e, hN3⟩ := c.third_neighbor hde hea
  have hA0 : G.Adj a z0 := (G.mem_neighborFinset a z0).mp (by rw [hN0]; simp)
  have hA1 : G.Adj b z1 := (G.mem_neighborFinset b z1).mp (by rw [hN1]; simp)
  have hA2 : G.Adj d z2 := (G.mem_neighborFinset d z2).mp (by rw [hN2]; simp)
  have hA3 : G.Adj e z3 := (G.mem_neighborFinset e z3).mp (by rw [hN3]; simp)
  let L1 := LinearMap.range (r.component b z1)
  let L2 := LinearMap.range (r.component d z2)
  let L3 := LinearMap.range (r.component e z3)
  let S0 := (U a ⊔ U b) ⊔ L1
  let S1 := (U b ⊔ U d) ⊔ L2
  let T := S0 ⊔ L2
  have hs0 : TripleSupport U r e a b d z0 z1 S0 :=
    c.triple_support hea hab hbd h0e h0b h0a hN0 h1a h1d h1b hN1
  have hs1 : TripleSupport U r a b d e z1 z2 S1 :=
    c.triple_support hab hbd hde h1a h1d h1b hN1 h2b h2e h2d hN2
  have hnot2 : ¬ L2 ≤ S0 := (c.triple_extension hs0 hab hbd hde hA1 h2e hN2).1
  have hnot31 : ¬ L3 ≤ S1 := (c.triple_extension hs1 hbd hde hea hA2 h3a hN3).1
  have hL2 : finrank K L2 = 1 := (c.high_remainder hde).2.2 z2 (by simp [hN2, h2e])
  have hL3 : finrank K L3 = 1 := (c.high_remainder hea).2.2 z3 (by simp [hN3, h3a])
  have hback : finrank K (LinearMap.range (r.component a e)) = 1 :=
    (c.high_remainder hab).2.2 e (by simp [hN0, c.path_two_ne hea hab])
  have haT : U a ≤ T := (inf_eq_left.mp hs0.left).trans le_sup_left
  have hbT : U b ≤ T := (inf_eq_left.mp hs0.middle).trans le_sup_left
  have hdT : U d ≤ T := (inf_eq_left.mp hs0.right).trans le_sup_left
  have heT : U e ≤ T := by
    apply c.high_target_le hde T hdT
    intro w hwe
    by_cases hw : G.Adj d w
    · have hmem := (G.mem_neighborFinset d w).mpr hw
      rw [hN2] at hmem
      simp only [mem_insert, mem_singleton] at hmem
      rcases hmem with hwb | hwe' | hwz
      · subst w; exact (r.target d b).trans hbT
      · exact False.elim (hwe hwe')
      · subst w; exact le_sup_right
    · rw [c.support d w hw, LinearMap.range_zero]; exact bot_le
  have hL3T : L3 ≤ T := by
    apply r.component_range_le_of_rest e z3 T heT
    intro w hwz
    by_cases hw : G.Adj e w
    · have hmem := (G.mem_neighborFinset e w).mpr hw
      rw [hN3] at hmem
      simp only [mem_insert, mem_singleton] at hmem
      rcases hmem with hwd | hwa | hwz'
      · subst w; exact (r.target e d).trans hdT
      · subst w; exact (r.target e a).trans haT
      · exact False.elim (hwz hwz')
    · rw [c.support e w hw, LinearMap.range_zero]; exact bot_le
  have h3b : z3 ≠ b := by
    intro he
    subst z3
    exact c.triangle {e, a, b} (SimpleGraph.is3Clique_triple_iff.mpr
      ⟨c.high_adj hea, hA3, c.high_adj hab⟩)
  have h30 : z3 ≠ z0 := by
    intro he
    have hE0 : G.Adj e z0 := he ▸ hA3
    exact c.triangle {e, a, z0} (SimpleGraph.is3Clique_triple_iff.mpr
      ⟨c.high_adj hea, hE0, hA0⟩)
  have hnot30 : ¬ L3 ≤ S0 := by
    intro h
    apply hnot31
    have hpart : L3 ≤ U z3 ⊓ S0 := le_inf (r.target e z3) h
    by_cases h31 : z3 = z1
    · subst z3
      rw [hs0.side_right] at hpart
      exact hpart.trans ((c.other_image_le_pair hbd hA1 h1d).trans le_sup_left)
    · rw [hs0.outside z3 h3a h3b h3d h3e h30 h31] at hpart
      exact hpart.trans bot_le
  have h23 : z2 ≠ z3 := by
    intro he
    have hD3 : G.Adj d z3 := he ▸ hA2
    exact c.triangle {d, e, z3} (SimpleGraph.is3Clique_triple_iff.mpr
      ⟨c.high_adj hde, hD3, hA3⟩)
  have hgainE : finrank K (U e ⊓ S0 : Submodule K W) <
      finrank K (U e ⊓ T : Submodule K W) := by
    rw [hs0.back, hback, inf_eq_left.mpr heT, (c.high_dimensions hde).2.1]
    omega
  have hgain2 := line_coordinate_gain (U z2) S0 L2 (r.target d z2) hnot2
  have hgain3 : finrank K (U z3 ⊓ S0 : Submodule K W) <
      finrank K (U z3 ⊓ T : Submodule K W) :=
    (line_coordinate_gain (U z3) S0 L3 (r.target e z3) hnot30).trans_le
      (Submodule.finrank_mono (inf_le_inf_left _ (sup_le le_sup_left hL3T)))
  have hbudget := tight_growth_gain_budget U c.positive hs0.tight
    (show S0 ≤ T from le_sup_left) ({e, z2, z3} : Finset V) (by
      intro w hw
      simp only [mem_insert, mem_singleton] at hw
      rcases hw with hw | hw | hw
      · subst w; exact hgainE
      · subst w; exact hgain2
      · subst w; exact hgain3)
  have hc : ({e, z2, z3} : Finset V).card = 3 := by
    simp [h2e.symm, h3e.symm, h23]
  have hdTdim : finrank K T = 6 := by
    rw [line_extension_dimension S0 L2 hL2 hnot2, hs0.dimension]
  rw [hc, hs0.dimension, hdTdim] at hbudget
  omega

end SubcubicMemo.LowRank
