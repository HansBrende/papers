import MotionDepthCodes.Subcubic
import LeanMachine.SubspaceDefect
import LeanMachine.SubspaceRecovery

/-! Local structure of a positive-deficit rank-one recovery arrangement.
The positivity premise is discharged by quotient induction in the global proof;
none of the lemmas in this file is itself the global half theorem. -/

namespace SubcubicMemo.LowRank

open Module Finset LeanMachine.SubspaceRecovery LeanMachine.SubspaceDefect
open scoped BigOperators

variable {V K W : Type*} [Fintype V] [DecidableEq V] [Field K]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  {G : SimpleGraph V} [DecidableRel G.Adj] {U : V → Submodule K W}

def Supported (r : Recovery U) (G : SimpleGraph V) : Prop :=
  ∀ v u, ¬ G.Adj v u → r.component v u = 0

def RankOne (r : Recovery U) : Prop :=
  ∀ v u, finrank K (LinearMap.range (r.component v u)) ≤ 1

def AtMostOneHigh (r : Recovery U) : Prop :=
  ∀ v u w, 1 < finrank K (LinearMap.range (r.component v u)) →
    1 < finrank K (LinearMap.range (r.component v w)) → u = w

omit [DecidableEq V] [FiniteDimensional K W] [DecidableRel G.Adj] in
theorem Supported.diagonal {r : Recovery U} (h : Supported r G) (v : V) :
    r.component v v = 0 := h v v (G.loopless.irrefl v)

omit [DecidableEq V] [FiniteDimensional K W] in
theorem Supported.outside {r : Recovery U} (h : Supported r G) (v u : V)
    (hu : u ∉ G.neighborFinset v) : r.component v u = 0 := by
  exact h v u (by simpa using hu)

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- The row conditions survive every linear image, with newly chosen components. -/
theorem image_rank_one {Z : Type*} [AddCommGroup Z] [Module K Z]
    (r : Recovery U) (hs : Supported r G) (hr : RankOne r) (f : W →ₗ[K] Z) :
    ∃ r' : Recovery (fun v => (U v).map f), Supported r' G ∧ RankOne r' := by
  obtain ⟨r', hzero, hrank⟩ := r.image f
  exact ⟨r', fun v u h => hzero v u (hs v u h), fun v u => (hrank v u).trans (hr v u)⟩

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem image_one_high {Z : Type*} [AddCommGroup Z] [Module K Z]
    (r : Recovery U) (hs : Supported r G) (hr : AtMostOneHigh r) (f : W →ₗ[K] Z) :
    ∃ r' : Recovery (fun v => (U v).map f), Supported r' G ∧ AtMostOneHigh r' := by
  obtain ⟨r', hzero, hrank⟩ := r.image f
  exact ⟨r', fun v u h => hzero v u (hs v u h),
    fun v u w hu hw => hr v u w (hu.trans_le (hrank v u)) (hw.trans_le (hrank v w))⟩

noncomputable def rowSpan (r : Recovery U) (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) : Submodule K W :=
  (G.neighborFinset v).sup (fun u => LinearMap.range (r.component v u))

omit [DecidableEq V] [FiniteDimensional K W] in
theorem coordinate_le_rowSpan (r : Recovery U) (hs : Supported r G) (v : V) :
    U v ≤ rowSpan r G v := r.le_row_span v _ (hs.outside v)

omit [DecidableEq V] in
theorem rowSpan_dimension_le_of_row (r : Recovery U) {v : V}
    (hr : ∀ u, finrank K (LinearMap.range (r.component v u)) ≤ 1) :
    finrank K (rowSpan r G v) ≤ G.degree v := by
  calc
    _ ≤ ∑ u ∈ G.neighborFinset v, finrank K (LinearMap.range (r.component v u)) :=
      finrank_finset_sup_le _ _
    _ ≤ ∑ _u ∈ G.neighborFinset v, 1 := sum_le_sum (fun u _ => hr u)
    _ = G.degree v := by simp

omit [DecidableEq V] in
theorem coordinate_dimension_le_two_of_row (r : Recovery U) (hs : Supported r G) {v : V}
    (hr : ∀ u, finrank K (LinearMap.range (r.component v u)) ≤ 1)
    (hdeg : ∀ v, G.degree v ≤ 3)
    (hpos : ∀ S : Submodule K W, S ≠ ⊥ → 1 ≤ defect U S) :
    finrank K (U v) ≤ 2 := by
  by_cases hv : U v = ⊥
  · rw [hv, finrank_bot]; omega
  have hstrict := r.strict_row_span (pairwise_disjoint_of_positive U hpos)
    hs.diagonal v hv (G.neighborFinset v) (hs.outside v)
  change finrank K (U v) < finrank K (rowSpan r G v) at hstrict
  have hbound := (rowSpan_dimension_le_of_row (G := G) r hr).trans (hdeg v)
  omega

omit [DecidableEq V] in
/-- A plane row has three nonzero image lines spanning a three-dimensional space. -/
theorem plane_row_dimensions_of_row (r : Recovery U) (hs : Supported r G) {v : V}
    (hr : ∀ u, finrank K (LinearMap.range (r.component v u)) ≤ 1)
    (hdeg : ∀ v, G.degree v ≤ 3)
    (hpos : ∀ S : Submodule K W, S ≠ ⊥ → 1 ≤ defect U S)
    (hv : finrank K (U v) = 2) :
    G.degree v = 3 ∧ finrank K (rowSpan r G v) = 3 ∧
      ∀ u ∈ G.neighborFinset v, finrank K (LinearMap.range (r.component v u)) = 1 := by
  have hv0 : U v ≠ ⊥ := by intro h; rw [h, finrank_bot] at hv; omega
  have hstrict := r.strict_row_span (pairwise_disjoint_of_positive U hpos)
    hs.diagonal v hv0 (G.neighborFinset v) (hs.outside v)
  change finrank K (U v) < finrank K (rowSpan r G v) at hstrict
  have hbound := rowSpan_dimension_le_of_row (G := G) r hr
  have hd := hdeg v
  have hdim : finrank K (rowSpan r G v) = 3 := by omega
  have hdegree : G.degree v = 3 := by omega
  refine ⟨hdegree, hdim, ?_⟩
  have hlower := finrank_finset_sup_le (G.neighborFinset v)
    (fun u => LinearMap.range (r.component v u))
  change finrank K (rowSpan r G v) ≤ _ at hlower
  have hupper := sum_le_sum (s := G.neighborFinset v) (fun u _ => hr u)
  have heq : (∑ u ∈ G.neighborFinset v, finrank K (LinearMap.range (r.component v u))) =
      ∑ _u ∈ G.neighborFinset v, 1 := by
    apply le_antisymm hupper
    simpa [hdim, hdegree] using hlower
  exact (sum_eq_sum_iff_of_le (fun u (_ : u ∈ G.neighborFinset v) => hr u)).mp heq

/-- A plane star meets only its center and its three named input lines.
This is an exact coordinate statement, including vertices outside the star. -/
theorem plane_star_exact_of_row (r : Recovery U) (hs : Supported r G) {v : V}
    (hr : ∀ u, finrank K (LinearMap.range (r.component v u)) ≤ 1)
    (hdeg : ∀ v, G.degree v ≤ 3)
    (hpos : ∀ S : Submodule K W, S ≠ ⊥ → 1 ≤ defect U S)
    (hv : finrank K (U v) = 2) :
    defect U (rowSpan r G v) = 1 ∧
      ∀ u, U u ⊓ rowSpan r G v =
        if u = v then U v else LinearMap.range (r.component v u) := by
  obtain ⟨hdegree, hdim, hports⟩ := plane_row_dimensions_of_row r hs hr hdeg hpos hv
  let P := rowSpan r G v
  have hP0 : P ≠ ⊥ := by intro h; change finrank K P = 3 at hdim; rw [h, finrank_bot] at hdim; omega
  have hP : U v ≤ P := coordinate_le_rowSpan r hs v
  let m : V → ℕ := fun u => (if u = v then 2 else 0) + (if u ∈ G.neighborFinset v then 1 else 0)
  have hm : ∀ u, m u ≤ finrank K (U u ⊓ P : Submodule K W) := by
    intro u
    by_cases huv : u = v
    · subst u
      rw [inf_eq_left.mpr hP, hv]
      simp [m]
    · by_cases hu : u ∈ G.neighborFinset v
      · have hi : LinearMap.range (r.component v u) ≤ U u ⊓ P :=
          le_inf (r.target v u) (Finset.le_sup (f := fun u => LinearMap.range (r.component v u)) hu)
        have hn := Submodule.finrank_mono hi
        rw [hports u hu] at hn
        simpa only [m, ite_eq_right huv, ite_eq_left hu, zero_add] using hn
      · simp only [m, ite_eq_right huv, ite_eq_right hu, zero_add, Nat.zero_le]
  have hbudget : (∑ u, m u) + 1 = 2 * finrank K P := by
    change (∑ u, m u) + 1 = 2 * finrank K (rowSpan r G v)
    have hc : (G.neighborFinset v).card = 3 := by simpa using hdegree
    have hfilter : (univ.filter (fun u => u ∈ G.neighborFinset v)) = G.neighborFinset v := by ext; simp
    simp only [m, sum_add_distrib, hdim, sum_ite_eq', mem_univ, ite_true,
      sum_boole, hfilter, hc]
    norm_num
  obtain ⟨htight, hexact⟩ := exact_intersections U P (hpos P hP0) m hm hbudget
  refine ⟨htight, ?_⟩
  intro u
  by_cases huv : u = v
  · subst u
    rw [ite_eq_left rfl, inf_eq_left.mpr hP]
  · rw [ite_eq_right huv]
    by_cases hu : u ∈ G.neighborFinset v
    · have hi : LinearMap.range (r.component v u) ≤ U u ⊓ P :=
        le_inf (r.target v u) (Finset.le_sup (f := fun u => LinearMap.range (r.component v u)) hu)
      apply Eq.symm
      apply Submodule.eq_of_le_of_finrank_eq hi
      rw [hports u hu, hexact u]
      simp only [m, ite_eq_right huv, ite_eq_left hu, zero_add]
    · rw [hs.outside v u hu, LinearMap.range_zero]
      exact Submodule.finrank_eq_zero.mp (by
        simpa only [m, ite_eq_right huv, ite_eq_right hu, zero_add] using hexact u)

omit [DecidableEq V] in
theorem coordinate_dimension_le_two (r : Recovery U) (hs : Supported r G) (hr : RankOne r)
    (hdeg : ∀ v, G.degree v ≤ 3)
    (hpos : ∀ S : Submodule K W, S ≠ ⊥ → 1 ≤ defect U S) (v : V) :
    finrank K (U v) ≤ 2 := coordinate_dimension_le_two_of_row r hs (hr v) hdeg hpos

omit [DecidableEq V] in
theorem plane_row_dimensions (r : Recovery U) (hs : Supported r G) (hr : RankOne r)
    (hdeg : ∀ v, G.degree v ≤ 3)
    (hpos : ∀ S : Submodule K W, S ≠ ⊥ → 1 ≤ defect U S)
    {v : V} (hv : finrank K (U v) = 2) :
    G.degree v = 3 ∧ finrank K (rowSpan r G v) = 3 ∧
      ∀ u ∈ G.neighborFinset v, finrank K (LinearMap.range (r.component v u)) = 1 :=
  plane_row_dimensions_of_row r hs (hr v) hdeg hpos hv

theorem plane_star_exact (r : Recovery U) (hs : Supported r G) (hr : RankOne r)
    (hdeg : ∀ v, G.degree v ≤ 3)
    (hpos : ∀ S : Submodule K W, S ≠ ⊥ → 1 ≤ defect U S)
    {v : V} (hv : finrank K (U v) = 2) :
    defect U (rowSpan r G v) = 1 ∧
      ∀ u, U u ⊓ rowSpan r G v =
        if u = v then U v else LinearMap.range (r.component v u) :=
  plane_star_exact_of_row r hs (hr v) hdeg hpos hv

/-- Adjacent plane stars would have a tight intersection supported on two
one-dimensional coordinate intersections, giving an impossible odd deficit. -/
theorem no_adjacent_planes (r : Recovery U) (hs : Supported r G) (hr : RankOne r)
    (hdeg : ∀ v, G.degree v ≤ 3) (htri : G.CliqueFree 3)
    (hpos : ∀ S : Submodule K W, S ≠ ⊥ → 1 ≤ defect U S)
    {v u : V} (hv : finrank K (U v) = 2) (hu : finrank K (U u) = 2) : ¬ G.Adj v u := by
  intro hadj
  have hvu := hadj.ne
  obtain ⟨htv, hev⟩ := plane_star_exact r hs hr hdeg hpos hv
  obtain ⟨htu, heu⟩ := plane_star_exact r hs hr hdeg hpos hu
  have hrv := (plane_row_dimensions r hs hr hdeg hpos hv).2.2 u
    ((G.mem_neighborFinset v u).mpr hadj)
  have hru := (plane_row_dimensions r hs hr hdeg hpos hu).2.2 v
    ((G.mem_neighborFinset u v).mpr hadj.symm)
  let I := rowSpan r G v ⊓ rowSpan r G u
  have hiv : U v ⊓ I = LinearMap.range (r.component u v) := by
    change U v ⊓ (rowSpan r G v ⊓ rowSpan r G u) = _
    rw [← inf_assoc, hev v, ite_eq_left rfl, heu v, ite_eq_right hvu]
  have hiu : U u ⊓ I = LinearMap.range (r.component v u) := by
    change U u ⊓ (rowSpan r G v ⊓ rowSpan r G u) = _
    rw [inf_comm (rowSpan r G v), ← inf_assoc, heu u, ite_eq_left rfl,
      hev u, ite_eq_right (Ne.symm hvu)]
  have hi0 : I ≠ ⊥ := by
    intro hz
    have hx := hiv
    rw [hz, inf_bot_eq] at hx
    rw [← hx, finrank_bot] at hru
    omega
  have htight : defect U I = 1 := (tight_inf_sup U hpos htv htu hi0).1
  have hout : ∀ w, w ≠ v → w ≠ u → U w ⊓ I = ⊥ := by
    intro w hwv hwu
    by_cases hvw : G.Adj v w
    · have huw : ¬ G.Adj u w := by
        intro h
        exact htri {v, u, w} (SimpleGraph.is3Clique_triple_iff.mpr ⟨hadj, hvw, h⟩)
      have hz : U w ⊓ rowSpan r G u = ⊥ := by
        rw [heu w, ite_eq_right hwu, hs u w huw, LinearMap.range_zero]
      exact le_bot_iff.mp ((inf_le_inf_left _ inf_le_right).trans_eq hz)
    · have hz : U w ⊓ rowSpan r G v = ⊥ := by
        rw [hev w, ite_eq_right hwv, hs v w hvw, LinearMap.range_zero]
      exact le_bot_iff.mp ((inf_le_inf_left _ inf_le_left).trans_eq hz)
  have hsum : (∑ w, (finrank K (U w ⊓ I : Submodule K W) : ℤ)) = 2 := by
    calc
      _ = ∑ w ∈ ({v, u} : Finset V), (finrank K (U w ⊓ I : Submodule K W) : ℤ) := by
        symm
        apply sum_subset (subset_univ _)
        intro w _ hw
        have hne : w ≠ v ∧ w ≠ u := by simpa using hw
        rw [hout w hne.1 hne.2, finrank_bot, Nat.cast_zero]
      _ = 2 := by rw [sum_pair hvu, hiv, hiu, hru, hrv]; norm_num
  unfold defect at htight
  rw [hsum] at htight
  omega

end SubcubicMemo.LowRank
