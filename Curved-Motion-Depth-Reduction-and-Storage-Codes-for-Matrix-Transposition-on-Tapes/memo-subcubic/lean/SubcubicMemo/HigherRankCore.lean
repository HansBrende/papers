import SubcubicMemo.RankOneCore

/-! The local core when each row has at most one component of rank above one.
Original coordinate widths are unrestricted; the two-dimensional core is a
consequence of positive deficit, not an additional theorem hypothesis. -/

namespace SubcubicMemo.LowRank

open Module Finset LeanMachine.SubspaceRecovery LeanMachine.SubspaceDefect
open scoped BigOperators Classical

variable {V K W : Type*} [Fintype V] [DecidableEq V] [Field K]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  {G : SimpleGraph V} [DecidableRel G.Adj] {U : V → Submodule K W}

structure HighCore (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : V → Submodule K W) (r : Recovery U) : Prop where
  support : Supported r G
  oneHigh : AtMostOneHigh r
  degree : ∀ v, G.degree v ≤ 3
  triangle : G.CliqueFree 3
  positive : ∀ S : Submodule K W, S ≠ ⊥ → 1 ≤ defect U S

def High (r : Recovery U) (v u : V) : Prop :=
  1 < finrank K (LinearMap.range (r.component v u))

def remainder (r : Recovery U) (v u : V) : U v →ₗ[K] W :=
  (U v).subtype - r.component v u

variable {r : Recovery U} (c : HighCore G U r)
include c

theorem HighCore.disjoint : Pairwise (fun u v => Disjoint (U u) (U v)) :=
  pairwise_disjoint_of_positive U c.positive

theorem HighCore.high_adj {v u : V} (h : High r v u) : G.Adj v u := by
  by_contra hn
  unfold High at h
  rw [c.support v u hn, LinearMap.range_zero, finrank_bot] at h
  omega

theorem HighCore.other_low {v u : V} (h : High r v u) {w : V} (hwu : w ≠ u) :
    finrank K (LinearMap.range (r.component v w)) ≤ 1 := by
  by_contra hn
  exact hwu (c.oneHigh v w u (by omega) h)

theorem HighCore.remainder_injective {v u : V} (hvu : v ≠ u) :
    Function.Injective (remainder r v u) := by
  apply LinearMap.ker_eq_bot.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  have he : (x : W) = r.component v u x := sub_eq_zero.mp hx
  apply Subtype.ext
  change (x : W) = 0
  have hu : (x : W) ∈ U u := he ▸ r.target v u (LinearMap.mem_range_self _ _)
  simpa only [(c.disjoint hvu).eq_bot, Submodule.mem_bot] using
    (show (x : W) ∈ U v ⊓ U u from ⟨x.property, hu⟩)

theorem HighCore.row_sum (v : V) :
    ∑ u ∈ G.neighborFinset v, r.component v u = (U v).subtype := by
  rw [← r.sum_eq v]
  exact sum_subset (subset_univ _) (fun u _ hu => c.support.outside v u hu)

theorem HighCore.remainder_eq_sum {v u : V} (hvu : G.Adj v u) :
    remainder r v u = ∑ w ∈ (G.neighborFinset v).erase u, r.component v w := by
  have h := sum_erase_add (G.neighborFinset v) (fun w => r.component v w)
    ((G.mem_neighborFinset v u).mpr hvu)
  rw [c.row_sum] at h
  exact (eq_sub_of_add_eq h).symm

theorem HighCore.remainder_range_le {v u : V} (hvu : G.Adj v u) :
    LinearMap.range (remainder r v u) ≤
      ((G.neighborFinset v).erase u).sup (fun w => LinearMap.range (r.component v w)) := by
  rintro _ ⟨x, rfl⟩
  rw [c.remainder_eq_sum hvu, LinearMap.sum_apply]
  exact Submodule.sum_mem _ (fun w hw =>
    (Finset.le_sup (f := fun w => LinearMap.range (r.component v w)) hw)
      (LinearMap.mem_range_self _ _))

theorem HighCore.other_sum_le_two {v u : V} (h : High r v u) :
    (∑ w ∈ (G.neighborFinset v).erase u,
      finrank K (LinearMap.range (r.component v w))) ≤ 2 := by
  have hp := (G.mem_neighborFinset v u).mpr (c.high_adj h)
  calc
    _ ≤ ∑ _w ∈ (G.neighborFinset v).erase u, 1 :=
      sum_le_sum (fun w hw => c.other_low h (mem_erase.mp hw).1)
    _ = G.degree v - 1 := by simp [card_erase_of_mem hp]
    _ ≤ 2 := by have hd := c.degree v; omega

theorem HighCore.dim_le_two (v : V) : finrank K (U v) ≤ 2 := by
  by_cases hh : ∃ u, High r v u
  · obtain ⟨u, hu⟩ := hh
    have hadj := c.high_adj hu
    have hdim := LinearMap.finrank_range_of_inj (c.remainder_injective hadj.ne)
    calc
      _ = finrank K (LinearMap.range (remainder r v u)) := hdim.symm
      _ ≤ finrank K (((G.neighborFinset v).erase u).sup
          (fun w => LinearMap.range (r.component v w)) : Submodule K W) :=
        Submodule.finrank_mono (c.remainder_range_le hadj)
      _ ≤ _ := finrank_finset_sup_le _ _
      _ ≤ 2 := c.other_sum_le_two hu
  · apply coordinate_dimension_le_two_of_row r c.support _ c.degree c.positive
    intro u
    have hn : ¬ High r v u := fun h => hh ⟨u, h⟩
    exact Nat.le_of_not_gt hn

theorem HighCore.high_dimensions {v u : V} (h : High r v u) :
    finrank K (U v) = 2 ∧ finrank K (U u) = 2 ∧
      finrank K (LinearMap.range (r.component v u)) = 2 ∧
      LinearMap.range (r.component v u) = U u := by
  have hv := c.dim_le_two v
  have hu := c.dim_le_two u
  have hs := LinearMap.finrank_range_le (r.component v u)
  have ht := Submodule.finrank_mono (r.target v u)
  have hdim : finrank K (LinearMap.range (r.component v u)) = 2 := by
    unfold High at h
    omega
  have huv : finrank K (U v) = 2 := by omega
  have huu : finrank K (U u) = 2 := by omega
  exact ⟨huv, huu, hdim, Submodule.eq_of_le_of_finrank_eq (r.target v u) (by omega)⟩

/-- Removing the high component leaves exactly two independent image lines.
Their entire span is the image of the injective remainder. -/
theorem HighCore.high_remainder {v u : V} (h : High r v u) :
    G.degree v = 3 ∧
      LinearMap.range (remainder r v u) =
        ((G.neighborFinset v).erase u).sup (fun w => LinearMap.range (r.component v w)) ∧
      ∀ w ∈ (G.neighborFinset v).erase u,
        finrank K (LinearMap.range (r.component v w)) = 1 := by
  have hadj := c.high_adj h
  have hd := (c.high_dimensions h).1
  have hD := LinearMap.finrank_range_of_inj (c.remainder_injective hadj.ne)
  rw [hd] at hD
  have hlo := Submodule.finrank_mono (c.remainder_range_le hadj)
  have hsum := finrank_finset_sup_le ((G.neighborFinset v).erase u)
    (fun w => LinearMap.range (r.component v w))
  have hup := c.other_sum_le_two h
  have heq : (∑ w ∈ (G.neighborFinset v).erase u,
      finrank K (LinearMap.range (r.component v w))) = 2 := by omega
  have hones := sum_le_sum (s := (G.neighborFinset v).erase u)
    (fun w hw => c.other_low h (mem_erase.mp hw).1)
  have hcard : ((G.neighborFinset v).erase u).card = G.degree v - 1 := by
    simp [card_erase_of_mem ((G.mem_neighborFinset v u).mpr hadj)]
  simp only [sum_const, smul_eq_mul, mul_one, hcard] at hones
  have hdeg : G.degree v = 3 := by have hh := c.degree v; omega
  refine ⟨hdeg, ?_, ?_⟩
  · apply Submodule.eq_of_le_of_finrank_eq (c.remainder_range_le hadj)
    omega
  · apply (sum_eq_sum_iff_of_le (fun w (hw : w ∈ (G.neighborFinset v).erase u) =>
      c.other_low h (mem_erase.mp hw).1)).mp
    simpa [heq, hcard, hdeg]

theorem HighCore.other_image_le_pair {v u : V} (h : High r v u) {w : V}
    (hw : G.Adj v w) (hwu : w ≠ u) :
    LinearMap.range (r.component v w) ≤ U v ⊔ U u := by
  have hle : LinearMap.range (remainder r v u) ≤ U v ⊔ U u := by
    rintro _ ⟨x, rfl⟩
    exact Submodule.sub_mem _ (show (x : W) ∈ U v ⊔ U u from
      (show U v ≤ U v ⊔ U u from le_sup_left) x.property)
      (show r.component v u x ∈ U v ⊔ U u from
        (show U u ≤ U v ⊔ U u from le_sup_right)
          (r.target v u (LinearMap.mem_range_self _ _)))
  rw [(c.high_remainder h).2.1] at hle
  exact (Finset.le_sup (f := fun w => LinearMap.range (r.component v w))
    (mem_erase.mpr ⟨hwu, (G.mem_neighborFinset v w).mpr hw⟩)).trans hle

/-- If the only possible high port in a plane row points across a named edge,
its other two ports are lines inside the sum of the endpoint planes. This
also covers a low-rank or zero reverse port, without a reciprocity premise. -/
theorem HighCore.pair_row {v u : V} (hv : finrank K (U v) = 2)
    (hadj : G.Adj v u)
    (hlow : ∀ w, w ≠ u → finrank K (LinearMap.range (r.component v w)) ≤ 1) :
    G.degree v = 3 ∧ ∀ w ∈ (G.neighborFinset v).erase u,
      finrank K (LinearMap.range (r.component v w)) = 1 ∧
        LinearMap.range (r.component v w) ≤ U v ⊔ U u := by
  by_cases hh : High r v u
  · have h := c.high_remainder hh
    exact ⟨h.1, fun w hw => ⟨h.2.2 w hw, c.other_image_le_pair hh
      ((G.mem_neighborFinset v w).mp (mem_erase.mp hw).2) (mem_erase.mp hw).1⟩⟩
  · have hrow : ∀ w, finrank K (LinearMap.range (r.component v w)) ≤ 1 := by
      intro w
      by_cases hwu : w = u
      · subst w; exact Nat.le_of_not_gt hh
      · exact hlow w hwu
    obtain ⟨hd, hK, hports⟩ :=
      plane_row_dimensions_of_row r c.support hrow c.degree c.positive hv
    have hL : finrank K (LinearMap.range (r.component v u)) = 1 :=
      hports u ((G.mem_neighborFinset v u).mpr hadj)
    have hdisj : Disjoint (U v) (LinearMap.range (r.component v u)) :=
      (c.disjoint hadj.ne).mono_right (r.target v u)
    have hm := Submodule.finrank_sup_add_finrank_inf_eq
      (U v) (LinearMap.range (r.component v u))
    rw [hdisj.eq_bot, finrank_bot, hv, hL] at hm
    have hsub : U v ⊔ LinearMap.range (r.component v u) ≤ rowSpan r G v :=
      sup_le (coordinate_le_rowSpan r c.support v)
        (Finset.le_sup (f := fun w => LinearMap.range (r.component v w))
          ((G.mem_neighborFinset v u).mpr hadj))
    have heq : U v ⊔ LinearMap.range (r.component v u) = rowSpan r G v :=
      Submodule.eq_of_le_of_finrank_eq hsub (by omega)
    refine ⟨hd, fun w hw => ⟨hports w (mem_erase.mp hw).2, ?_⟩⟩
    calc
      _ ≤ rowSpan r G v := Finset.le_sup (f := fun w => LinearMap.range (r.component v w))
        (mem_erase.mp hw).2
      _ = U v ⊔ LinearMap.range (r.component v u) := heq.symm
      _ ≤ U v ⊔ U u := sup_le_sup_left (r.target v u) _

theorem HighCore.mass_bound {S : Submodule K W} (hS : S ≠ ⊥) :
    (∑ v, finrank K (U v ⊓ S : Submodule K W)) + 1 ≤ 2 * finrank K S := by
  have h := c.positive S hS
  unfold defect at h
  rw [← Nat.cast_sum] at h
  omega

end SubcubicMemo.LowRank
