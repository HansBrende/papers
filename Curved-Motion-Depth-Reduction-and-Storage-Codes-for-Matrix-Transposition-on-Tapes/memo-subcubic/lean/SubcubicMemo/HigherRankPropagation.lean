import SubcubicMemo.HigherRankTriples
import LeanMachine.SubspaceGrowth

/-! A tight triple forces the next plane to reuse its back or side coordinate. -/

namespace SubcubicMemo.LowRank

open Module Finset LeanMachine.SubspaceRecovery LeanMachine.SubspaceDefect
open scoped BigOperators Classical

variable {V K W : Type*} [Fintype V] [DecidableEq V] [Field K]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  {G : SimpleGraph V} [DecidableRel G.Adj] {U : V → Submodule K W}
  {r : Recovery U} (c : HighCore G U r)
include c

theorem HighCore.triple_extension {p a b d z y e t : V} {S : Submodule K W}
    (hS : TripleSupport U r p a b d z y S)
    (hab : High r a b) (hbd : High r b d) (hde : High r d e)
    (hby : G.Adj b y) (hte : t ≠ e)
    (hdN : G.neighborFinset d = {b, e, t}) :
    ¬ LinearMap.range (r.component d t) ≤ S ∧ (e = p ∨ e = z) := by
  let L := LinearMap.range (r.component d t)
  have hline : finrank K L = 1 := (c.high_remainder hde).2.2 t (by simp [hdN, hte])
  have heDim := (c.high_dimensions hde).2.1
  have hea : e ≠ a := (c.path_three_ne hab hbd hde).symm
  have heb : e ≠ b := (c.path_two_ne hbd hde).symm
  have hed : e ≠ d := (c.high_adj hde).ne.symm
  have heNot : ¬ U e ≤ S := by
    intro he
    rcases (hS.full_plane_iff heDim).mp he with he | he | he
    · exact hea he
    · exact heb he
    · exact hed he
  have heT : U e ≤ S ⊔ L := by
    apply c.high_target_le hde (S ⊔ L) ((inf_eq_left.mp hS.right).trans le_sup_left)
    intro w hwe
    by_cases hw : G.Adj d w
    · have hmem := (G.mem_neighborFinset d w).mpr hw
      rw [hdN] at hmem
      simp only [mem_insert, mem_singleton] at hmem
      rcases hmem with hwb | hwe' | hwt
      · subst w
        exact (r.target d b).trans ((inf_eq_left.mp hS.middle).trans le_sup_left)
      · exact False.elim (hwe hwe')
      · subst w; exact le_sup_right
    · rw [c.support d w hw, LinearMap.range_zero]; exact bot_le
  have hnot : ¬ L ≤ S := fun h => heNot (heT.trans (sup_le le_rfl h))
  have hdim := line_extension_dimension S L hline hnot
  have hgain := line_coordinate_gain (U t) S L (r.target d t) hnot
  have hI := plane_gain_forces_intersection U c.positive hS.tight le_sup_left
    hdim.le hte.symm heDim heT hgain
  have hey : e ≠ y := by
    intro he
    have hbe : G.Adj b e := he.symm ▸ hby
    exact c.triangle {b, d, e} (SimpleGraph.is3Clique_triple_iff.mpr
      ⟨c.high_adj hbd, hbe, c.high_adj hde⟩)
  refine ⟨hnot, ?_⟩
  by_cases hep : e = p
  · exact Or.inl hep
  by_cases hez : e = z
  · exact Or.inr hez
  exact False.elim (hI (hS.outside e hea heb hed hep hez hey))

/-- A four-step high path either closes a four-cycle or has the forced
distance-three chord at its second vertex. -/
theorem HighCore.path_chord_or_four {p a b d e : V}
    (hpa : High r p a) (hab : High r a b) (hbd : High r b d) (hde : High r d e) :
    e = p ∨ G.Adj a e := by
  obtain ⟨z, hzp, hzb, hza, haN⟩ := c.third_neighbor hpa hab
  obtain ⟨y, hya, hyd, hyb, hbN⟩ := c.third_neighbor hab hbd
  obtain ⟨t, htb, hte, htd, hdN⟩ := c.third_neighbor hbd hde
  have hS := c.triple_support hpa hab hbd hzp hzb hza haN hya hyd hyb hbN
  have hby : G.Adj b y := (G.mem_neighborFinset b y).mp (by rw [hbN]; simp)
  have he := (c.triple_extension hS hab hbd hde hby hte hdN).2
  rcases he with he | he
  · exact Or.inl he
  · apply Or.inr
    rw [he]
    exact (G.mem_neighborFinset a z).mp (by rw [haN]; simp)

end SubcubicMemo.LowRank
