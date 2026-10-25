import SubcubicMemo.RankOneBound
import LeanMachine.LinearCodeRecovery

/-! Intrinsic code capacities, ambient capacities, and paid exceptional rows. -/

namespace SubcubicMemo.LowRank

open Module Finset LeanMachine.SubspaceRecovery LeanMachine.SubspaceDefect
open scoped BigOperators Classical

variable {V K W : Type*} [Fintype V] [DecidableEq V] [Field K]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  {G : SimpleGraph V} [DecidableRel G.Adj] {U : V → Submodule K W}

/-- Removing exceptional coordinate spaces pays their exact intersection
deficit. The exceptional components can have unrestricted rank. -/
theorem rank_one_exception_defect (r : Recovery U) (hs : Supported r G)
    (E : Finset V) (hr : ∀ v ∉ E, ∀ u,
      finrank K (LinearMap.range (r.component v u)) ≤ 1)
    (hspan : (⨆ v, U v) = ⊤) (htri : G.CliqueFree 3)
    (hdeg : ∀ v, G.degree v ≤ 3) :
    defect U ⊤ ≤ defect U (E.sup U) := by
  let S := E.sup U
  obtain ⟨r', hz, hd⟩ := r.image S.mkQ
  have hs' : Supported r' G := fun v u h => hz v u (hs v u h)
  have hr' : RankOne r' := by
    intro v u
    by_cases hv : v ∈ E
    · have hzero : (U v).map S.mkQ = ⊥ := by
        apply (Submodule.eq_bot_iff _).mpr
        rintro y ⟨x, hx, rfl⟩
        change S.mkQ x = 0
        simpa only [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using
          (Finset.le_sup (f := U) hv hx : x ∈ S)
      have hdim : finrank K ((U v).map S.mkQ) = 0 := by rw [hzero, finrank_bot]
      exact (LinearMap.finrank_range_le (r'.component v u)).trans (by omega)
    · exact (hd v u).trans (hr v hv u)
  exact deficit_of_quotient_half U S (rank_one_arrangement_half r' hs' hr'
    (image_span U S.mkQ S.mkQ_surjective hspan) htri hdeg)

/-- The exact payment is at most the dimension of the exceptional span, hence
at most the sum of its coordinate dimensions. -/
theorem exceptional_span_defect (E : Finset V) :
    defect U (E.sup U) ≤ (finrank K (E.sup U : Submodule K W) : ℤ) ∧
      finrank K (E.sup U : Submodule K W) ≤ ∑ v ∈ E, finrank K (U v) := by
  have hdim := finrank_finset_sup_le E U
  have hmass : (∑ v ∈ E, (finrank K (U v) : ℤ)) ≤
      ∑ v, (finrank K (U v ⊓ E.sup U : Submodule K W) : ℤ) := by
    calc
      _ = ∑ v ∈ E, (finrank K (U v ⊓ E.sup U : Submodule K W) : ℤ) := by
        apply sum_congr rfl
        intro v hv
        rw [inf_eq_left.mpr (Finset.le_sup hv)]
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ E)
        (fun _ _ _ => Int.natCast_nonneg _)
  refine ⟨?_, hdim⟩
  unfold defect
  rw [← Nat.cast_sum] at hmass
  omega

section Codes

variable {A : V → Type*} [∀ v, AddCommGroup (A v)] [∀ v, Module K (A v)]
  [∀ v, FiniteDimensional K (A v)]

/-- The half theorem measures actual coordinate images, allowing redundant
ambient slots and unequal block dimensions. -/
theorem rank_one_code_half (C : Submodule K (∀ v, A v))
    (T : ∀ v u, A u →ₗ[K] A v)
    (hrow : ∀ x ∈ C, ∀ v, ∑ u, T v u (x u) = x v)
    (hs : ∀ v u, ¬ G.Adj v u → T v u = 0)
    (hr : ∀ v u, finrank K (LinearMap.range (T v u)) ≤ 1)
    (htri : G.CliqueFree 3) (hdeg : ∀ v, G.degree v ≤ 3) :
    2 * finrank K C ≤ ∑ v, finrank K (LinearMap.range (coordinate C v)) := by
  obtain ⟨r, hz, hd⟩ := code_dual_recovery C T hrow
  have hh := rank_one_arrangement_half r (fun v u h => hz v u (hs v u h))
    (fun v u => (hd v u).trans (hr v u)) (coordinate_duals_span C) htri hdeg
  simpa only [Subspace.dual_finrank_eq,
    LinearMap.finrank_range_dualMap_eq_finrank_range] using hh

theorem rank_one_code_capacity (C : Submodule K (∀ v, A v))
    (T : ∀ v u, A u →ₗ[K] A v)
    (hrow : ∀ x ∈ C, ∀ v, ∑ u, T v u (x u) = x v)
    (hs : ∀ v u, ¬ G.Adj v u → T v u = 0)
    (hr : ∀ v u, finrank K (LinearMap.range (T v u)) ≤ 1)
    (htri : G.CliqueFree 3) (hdeg : ∀ v, G.degree v ≤ 3) :
    2 * finrank K C ≤ ∑ v, finrank K (A v) :=
  (rank_one_code_half C T hrow hs hr htri hdeg).trans
    (sum_le_sum (fun v _ => Submodule.finrank_le _))

end Codes

section Matrix

variable {A : V → Type*} [∀ v, AddCommGroup (A v)] [∀ v, Module K (A v)]
  [∀ v, FiniteDimensional K (A v)]

/-- An identity-diagonal fitting block operator has at least half the total
scalar rank when every off-diagonal block has rank at most one. -/
theorem rank_one_block_rank (T : ∀ v u, A u →ₗ[K] A v)
    (hs : ∀ v u, ¬ G.Adj v u → T v u = 0)
    (hr : ∀ v u, finrank K (LinearMap.range (T v u)) ≤ 1)
    (htri : G.CliqueFree 3) (hdeg : ∀ v, G.degree v ≤ 3) :
    (∑ v, finrank K (A v)) ≤
      2 * finrank K (LinearMap.range (LinearMap.id - blockOperator T)) := by
  have hh := rank_one_code_capacity (LinearMap.ker (LinearMap.id - blockOperator T))
    T (block_kernel_recovery T) hs hr htri hdeg
  have hn := LinearMap.finrank_range_add_finrank_ker (LinearMap.id - blockOperator T)
  rw [Module.finrank_pi_fintype] at hn
  omega

end Matrix

/-- The scalar graph half bound is the width-one specialization. -/
theorem scalar_recovery_half (C : Submodule K (V → K))
    (T : V → V → K →ₗ[K] K)
    (hrow : ∀ x ∈ C, ∀ v, ∑ u, T v u (x u) = x v)
    (hs : ∀ v u, ¬ G.Adj v u → T v u = 0)
    (htri : G.CliqueFree 3) (hdeg : ∀ v, G.degree v ≤ 3) :
    2 * finrank K C ≤ Fintype.card V := by
  have hr : ∀ v u, finrank K (LinearMap.range (T v u)) ≤ 1 := fun v u => by
    simpa using Submodule.finrank_le (LinearMap.range (T v u))
  simpa using rank_one_code_capacity C T hrow hs hr htri hdeg

end SubcubicMemo.LowRank
