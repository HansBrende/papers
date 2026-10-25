import SubcubicMemo.RankOneCore

/-! Geometry used in the global rank-one growth argument. -/

namespace SubcubicMemo.LowRank

open Module Finset LeanMachine.SubspaceRecovery LeanMachine.SubspaceDefect
open scoped BigOperators

variable {V K W : Type*} [Fintype V] [DecidableEq V] [Field K]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  {G : SimpleGraph V} [DecidableRel G.Adj] {U : V → Submodule K W}

/-- Local hypotheses forced by quotient induction in a putative counterexample. -/
structure Core (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : V → Submodule K W) (r : Recovery U) : Prop where
  support : Supported r G
  one : RankOne r
  degree : ∀ v, G.degree v ≤ 3
  triangle : G.CliqueFree 3
  positive : ∀ S : Submodule K W, S ≠ ⊥ → 1 ≤ defect U S

variable {r : Recovery U} (c : Core G U r)

def Whole (U : V → Submodule K W) (S : Submodule K W) : Prop :=
  ∀ v, U v ≤ S ∨ Disjoint (U v) S

include c

theorem Core.dim_le_two (v : V) : finrank K (U v) ≤ 2 :=
  coordinate_dimension_le_two r c.support c.one c.degree c.positive v

theorem Core.disjoint : Pairwise (fun u v => Disjoint (U u) (U v)) :=
  pairwise_disjoint_of_positive U c.positive

theorem Core.plane_neighbor_line {v u : V} (hv : finrank K (U v) = 2)
    (hu : G.Adj v u) : finrank K (U u) = 1 := by
  have hp := (plane_row_dimensions r c.support c.one c.degree c.positive hv).2.2 u
    ((G.mem_neighborFinset v u).mpr hu)
  have hle := Submodule.finrank_mono (r.target v u)
  have htwo := c.dim_le_two u
  have hn : finrank K (U u) ≠ 2 := fun h =>
    no_adjacent_planes r c.support c.one c.degree c.triangle c.positive hv h hu
  omega

theorem Core.plane_port_eq {v u : V} (hv : finrank K (U v) = 2)
    (hu : G.Adj v u) : LinearMap.range (r.component v u) = U u := by
  apply Submodule.eq_of_le_of_finrank_eq (r.target v u)
  rw [c.plane_neighbor_line hv hu]
  exact (plane_row_dimensions r c.support c.one c.degree c.positive hv).2.2 u
    ((G.mem_neighborFinset v u).mpr hu)

theorem Core.star_intersection {v : V} (hv : finrank K (U v) = 2) (u : V) :
    U u ⊓ rowSpan r G v = if u = v ∨ G.Adj v u then U u else ⊥ := by
  have h := (plane_star_exact r c.support c.one c.degree c.positive hv).2 u
  by_cases huv : u = v
  · subst u
    simpa only [ite_eq_left rfl, true_or, ite_true] using h
  · by_cases hadj : G.Adj v u
    · rw [ite_eq_left (Or.inr hadj)]
      rw [ite_eq_right huv, c.plane_port_eq hv hadj] at h
      exact h
    · rw [ite_eq_right (not_or.mpr ⟨huv, hadj⟩)]
      rw [ite_eq_right huv, c.support v u hadj, LinearMap.range_zero] at h
      exact h

theorem Core.star_whole {v : V} (hv : finrank K (U v) = 2) : Whole U (rowSpan r G v) := by
  intro u
  have h := c.star_intersection hv u
  by_cases hu : u = v ∨ G.Adj v u
  · rw [ite_eq_left hu] at h
    exact Or.inl (inf_eq_left.mp h)
  · rw [ite_eq_right hu] at h
    exact Or.inr (disjoint_iff.mpr h)

theorem Core.star_tight {v : V} (hv : finrank K (U v) = 2) :
    defect U (rowSpan r G v) = 1 :=
  (plane_star_exact r c.support c.one c.degree c.positive hv).1

theorem Core.star_dimension {v : V} (hv : finrank K (U v) = 2) :
    finrank K (rowSpan r G v) = 3 :=
  (plane_row_dimensions r c.support c.one c.degree c.positive hv).2.1

theorem Core.neighbor_le_star {v u : V} (hv : finrank K (U v) = 2)
    (hu : G.Adj v u) : U u ≤ rowSpan r G v := by
  have h := c.star_intersection hv u
  rw [ite_eq_left (Or.inr hu)] at h
  exact inf_eq_left.mp h

theorem Core.plane_le_star_iff {v u : V} (hv : finrank K (U v) = 2)
    (hu : finrank K (U u) = 2) : U u ≤ rowSpan r G v ↔ u = v := by
  constructor
  · intro hle
    have h := c.star_intersection hv u
    rw [inf_eq_left.mpr hle] at h
    by_cases he : u = v ∨ G.Adj v u
    · rcases he with he | ha
      · exact he
      · have hl := c.plane_neighbor_line hv ha
        omega
    · rw [ite_eq_right he] at h
      rw [h, finrank_bot] at hu
      omega
  · rintro rfl
    exact coordinate_le_rowSpan r c.support _

/-- The finite-growth invariants. Every known line has a known graph neighbor;
this is the source of the at-most-two outside-neighbor bound. -/
structure Good (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : V → Submodule K W) (r : Recovery U) (S : Submodule K W) : Prop where
  tight : defect U S = 1
  whole : Whole U S
  planes : ∀ v, finrank K (U v) = 2 → U v ≤ S → rowSpan r G v ≤ S
  parent : ∀ v, finrank K (U v) = 1 → U v ≤ S →
    ∃ u, G.Adj v u ∧ U u ≤ S

theorem Core.good_star {v : V} (hv : finrank K (U v) = 2) :
    Good G U r (rowSpan r G v) := by
  refine ⟨c.star_tight hv, c.star_whole hv, ?_, ?_⟩
  · intro u hu hle
    obtain rfl := (c.plane_le_star_iff hv hu).mp hle
    exact le_rfl
  · intro u hu hle
    have h := c.star_intersection hv u
    rw [inf_eq_left.mpr hle] at h
    have hadj : G.Adj v u := by
      by_cases he : u = v ∨ G.Adj v u
      · rcases he with rfl | he
        · omega
        · exact he
      · rw [ite_eq_right he] at h
        rw [h, finrank_bot] at hu
        omega
    exact ⟨v, hadj.symm, coordinate_le_rowSpan r c.support v⟩

/-- A newly met plane star always meets a good space in exactly one of its
input lines. Thus maximal growth needs no simultaneous-star bookkeeping. -/
theorem Core.star_meet_axis {S : Submodule K W} (hS : Good G U r S)
    {v : V} (hv : finrank K (U v) = 2)
    (hnot : ¬ rowSpan r G v ≤ S) (hmeet : S ⊓ rowSpan r G v ≠ ⊥) :
    ∃ p, G.Adj v p ∧ S ⊓ rowSpan r G v = U p := by
  let I := S ⊓ rowSpan r G v
  have hplane : Disjoint (U v) S := (hS.whole v).resolve_left
    (fun h => hnot (hS.planes v hv h))
  have hi : Disjoint I (U v) := hplane.symm.mono_left inf_le_left
  have hle : I ⊔ U v ≤ rowSpan r G v :=
    sup_le inf_le_right (coordinate_le_rowSpan r c.support v)
  have hn := Submodule.finrank_mono hle
  have hm := Submodule.finrank_sup_add_finrank_inf_eq I (U v)
  rw [hi.eq_bot, finrank_bot, hv] at hm
  rw [c.star_dimension hv] at hn
  have hI : finrank K I = 1 := by
    have hpositive : finrank K I ≠ 0 := fun h => hmeet (Submodule.finrank_eq_zero.mp h)
    omega
  have ht : defect U I = 1 := (tight_inf_sup U c.positive hS.tight (c.star_tight hv) hmeet).1
  obtain ⟨p, hp⟩ : ∃ p, U p ⊓ I ≠ ⊥ := by
    by_contra h
    push_neg at h
    have hmass : (∑ p, (finrank K (U p ⊓ I : Submodule K W) : ℤ)) = 0 := by
      apply sum_eq_zero
      intro p _
      rw [h p, finrank_bot, Nat.cast_zero]
    unfold defect at ht
    rw [hmass, hI] at ht
    norm_num at ht
  have hsmall := Submodule.finrank_mono (inf_le_right : U p ⊓ I ≤ I)
  have hnonzero : finrank K (U p ⊓ I : Submodule K W) ≠ 0 :=
    fun h => hp (Submodule.finrank_eq_zero.mp h)
  have heq : U p ⊓ I = I := Submodule.eq_of_le_of_finrank_eq inf_le_right (by omega)
  have hIp : I ≤ U p := by rw [← heq]; exact inf_le_left
  have hadj : G.Adj v p := by
    have hstar := c.star_intersection hv p
    by_cases h : p = v ∨ G.Adj v p
    · rcases h with rfl | h
      · have hz : I ≤ (⊥ : Submodule K W) :=
          (le_inf hIp inf_le_left).trans_eq hplane.eq_bot
        exact False.elim (hmeet (le_bot_iff.mp hz))
      · exact h
    · rw [ite_eq_right h] at hstar
      have hz : I ≤ (⊥ : Submodule K W) :=
        (le_inf hIp inf_le_right).trans_eq hstar
      exact False.elim (hmeet (le_bot_iff.mp hz))
  exact ⟨p, hadj, Submodule.eq_of_le_of_finrank_eq hIp
    (hI.trans (c.plane_neighbor_line hv hadj).symm)⟩

theorem Core.whole_tight_join {S T : Submodule K W}
    (hS : Whole U S) (hT : Whole U T) (htS : defect U S = 1) (htT : defect U T = 1)
    (hne : S ⊓ T ≠ ⊥) :
    Whole U (S ⊔ T) ∧ ∀ v, U v ≤ S ⊔ T ↔ U v ≤ S ∨ U v ≤ T := by
  have hexact := tight_exact_join U c.positive htS htT hne
  have hor : ∀ v, U v ≤ S ⊔ T → U v ≤ S ∨ U v ≤ T := by
    intro v hle
    by_cases hs : U v ≤ S
    · exact Or.inl hs
    by_cases ht : U v ≤ T
    · exact Or.inr ht
    have h := hexact v
    rw [inf_eq_left.mpr hle, ((hS v).resolve_left hs).eq_bot,
      ((hT v).resolve_left ht).eq_bot, bot_sup_eq] at h
    exact False.elim (hs (h.le.trans bot_le))
  refine ⟨?_, fun v => ⟨hor v, fun h => h.elim
    (fun h => h.trans le_sup_left) (fun h => h.trans le_sup_right)⟩⟩
  intro v
  rcases hS v with hs | hs
  · exact Or.inl (hs.trans le_sup_left)
  rcases hT v with ht | ht
  · exact Or.inl (ht.trans le_sup_right)
  · apply Or.inr
    apply disjoint_iff.mpr
    rw [hexact v, hs.eq_bot, ht.eq_bot, bot_sup_eq]

theorem Core.good_absorb {S : Submodule K W} (hS : Good G U r S)
    {v p : V} (hv : finrank K (U v) = 2) (hp : G.Adj v p)
    (hmeet : S ⊓ rowSpan r G v = U p) :
    Good G U r (S ⊔ rowSpan r G v) ∧
      finrank K (S ⊔ rowSpan r G v : Submodule K W) = finrank K S + 2 := by
  have hne : S ⊓ rowSpan r G v ≠ ⊥ := by
    rw [hmeet]
    intro hz
    have hd := c.plane_neighbor_line hv hp
    rw [hz, finrank_bot] at hd
    omega
  obtain ⟨hwhole, hle⟩ := c.whole_tight_join hS.whole (c.star_whole hv)
    hS.tight (c.star_tight hv) hne
  refine ⟨⟨(tight_inf_sup U c.positive hS.tight (c.star_tight hv) hne).2,
    hwhole, ?_, ?_⟩, ?_⟩
  · intro u hu hU
    rcases (hle u).mp hU with hOld | hStar
    · exact (hS.planes u hu hOld).trans le_sup_left
    · obtain rfl := (c.plane_le_star_iff hv hu).mp hStar
      exact le_sup_right
  · intro u hu hU
    rcases (hle u).mp hU with hOld | hStar
    · obtain ⟨w, hw, hW⟩ := hS.parent u hu hOld
      exact ⟨w, hw, hW.trans le_sup_left⟩
    · obtain ⟨w, hw, hW⟩ := (c.good_star hv).parent u hu hStar
      exact ⟨w, hw, hW.trans le_sup_right⟩
  · have hm := Submodule.finrank_sup_add_finrank_inf_eq S (rowSpan r G v)
    rw [hmeet, c.plane_neighbor_line hv hp, c.star_dimension hv] at hm
    omega

/-- Exact geometric record of a pair extension. The two new lines have a
common known parent; every other coordinate intersection is unchanged. -/
structure PairStep (G : SimpleGraph V) (U : V → Submodule K W)
    (S T : Submodule K W) : Prop where
  witnesses : ∃ v p q, p ≠ q ∧ finrank K (U v) = 1 ∧ U v ≤ S ∧
    G.Adj v p ∧ G.Adj v q ∧ finrank K (U p) = 1 ∧ finrank K (U q) = 1 ∧
    ¬ U p ≤ S ∧ ¬ U q ≤ S ∧
    (∀ u, U u ⊓ T = if u = p ∨ u = q then U u else U u ⊓ S)
  le : S ≤ T
  dimension : finrank K T = finrank K S + 1
  tight : defect U T = 1

theorem Core.good_pair {S T : Submodule K W} (hS : Good G U r S)
    (h : PairStep G U S T) : Good G U r T := by
  obtain ⟨v, p, q, hpq, hv, hvS, hvp, hvq, hp, hq, hpS, hqS, hi⟩ := h.witnesses
  have hknown : ∀ u, U u ≤ T → (u = p ∨ u = q) ∨ U u ≤ S := by
    intro u hu
    by_cases hnew : u = p ∨ u = q
    · exact Or.inl hnew
    · have heq := hi u
      rw [ite_eq_right hnew, inf_eq_left.mpr hu] at heq
      exact Or.inr (inf_eq_left.mp heq.symm)
  refine ⟨h.tight, ?_, ?_, ?_⟩
  · intro u
    by_cases hnew : u = p ∨ u = q
    · have heq := hi u
      rw [ite_eq_left hnew] at heq
      exact Or.inl (inf_eq_left.mp heq)
    · rcases hS.whole u with hu | hu
      · exact Or.inl (hu.trans h.le)
      · exact Or.inr (disjoint_iff.mpr (by rw [hi u, ite_eq_right hnew, hu.eq_bot]))
  · intro u hu hU
    rcases hknown u hU with hnew | hOld
    · rcases hnew with rfl | rfl <;> omega
    · exact (hS.planes u hu hOld).trans h.le
  · intro u hu hU
    rcases hknown u hU with hnew | hOld
    · rcases hnew with rfl | rfl
      · exact ⟨v, hvp.symm, hvS.trans h.le⟩
      · exact ⟨v, hvq.symm, hvS.trans h.le⟩
    · obtain ⟨w, hw, hW⟩ := hS.parent u hu hOld
      exact ⟨w, hw, hW.trans h.le⟩

/-- Two nonzero outside line contributions whose sum is already known give
an exact pair step. The positive-deficit condition forbids any hidden new
coordinate intersection. -/
theorem Core.make_pair {S : Submodule K W} (hS : Good G U r S)
    {v p q : V} (hv : finrank K (U v) = 1) (hvS : U v ≤ S)
    (hvp : G.Adj v p) (hvq : G.Adj v q) (hpq : p ≠ q)
    (hp : finrank K (U p) = 1) (hq : finrank K (U q) = 1)
    (hpS : ¬ U p ≤ S) (hqS : ¬ U q ≤ S)
    {a b : W} (ha : a ∈ U p) (hb : b ∈ U q) (hb0 : b ≠ 0) (hab : a + b ∈ S) :
    PairStep G U S (S ⊔ U p) := by
  let T := S ⊔ U p
  have hUp : U p ≤ T := le_sup_right
  have hUq : U q ≤ T := by
    rw [eq_span_singleton_of_mem_of_finrank_eq_one hq hb hb0]
    apply Submodule.span_le.mpr
    simp only [Set.singleton_subset_iff, SetLike.mem_coe]
    exact (T.add_mem_iff_right (hUp ha)).mp ((show S ≤ T from le_sup_left) hab)
  have hiP : U p ⊓ S = ⊥ := ((hS.whole p).resolve_left hpS).eq_bot
  have hiQ : U q ⊓ S = ⊥ := ((hS.whole q).resolve_left hqS).eq_bot
  have hdim : finrank K T = finrank K S + 1 := by
    have hm := Submodule.finrank_sup_add_finrank_inf_eq S (U p)
    rw [inf_comm S, hiP, finrank_bot, hp] at hm
    exact (Nat.add_zero _).symm.trans hm
  let m : V → ℕ := fun u => finrank K (U u ⊓ S : Submodule K W) +
    if u = p ∨ u = q then 1 else 0
  have hm : ∀ u, m u ≤ finrank K (U u ⊓ T : Submodule K W) := by
    intro u
    by_cases hnew : u = p ∨ u = q
    · rcases hnew with rfl | rfl
      · simp only [m, true_or, ite_true]
        rw [hiP, inf_eq_left.mpr hUp, finrank_bot, hp]
      · simp only [m, or_true, ite_true]
        rw [hiQ, inf_eq_left.mpr hUq, finrank_bot, hq]
    · simp only [m, ite_eq_right hnew, add_zero]
      exact Submodule.finrank_mono (inf_le_inf_left _ le_sup_left)
  have hbudgetS : (∑ u, finrank K (U u ⊓ S : Submodule K W)) + 1 = 2 * finrank K S := by
    have ht := hS.tight
    unfold defect at ht
    push_cast [← Nat.cast_sum] at ht
    omega
  have hfilter : univ.filter (fun u => u = p ∨ u = q) = ({p, q} : Finset V) := by ext; simp
  have hbudget : (∑ u, m u) + 1 = 2 * finrank K T := by
    simp only [m, sum_add_distrib, sum_boole, hfilter, card_pair hpq, Nat.cast_id, hdim]
    omega
  have hT0 : T ≠ ⊥ := by intro hz; rw [hz, finrank_bot] at hdim; omega
  obtain ⟨htight, hexact⟩ := exact_intersections U T (c.positive T hT0) m hm hbudget
  refine ⟨⟨v, p, q, hpq, hv, hvS, hvp, hvq, hp, hq, hpS, hqS, ?_⟩,
    le_sup_left, hdim, htight⟩
  intro u
  by_cases hnew : u = p ∨ u = q
  · rw [ite_eq_left hnew]
    rcases hnew with rfl | rfl
    · exact inf_eq_left.mpr hUp
    · exact inf_eq_left.mpr hUq
  · rw [ite_eq_right hnew]
    apply Eq.symm
    apply Submodule.eq_of_le_of_finrank_eq (inf_le_inf_left _ le_sup_left)
    rw [hexact u]
    simp only [m, ite_eq_right hnew, add_zero]

end SubcubicMemo.LowRank
