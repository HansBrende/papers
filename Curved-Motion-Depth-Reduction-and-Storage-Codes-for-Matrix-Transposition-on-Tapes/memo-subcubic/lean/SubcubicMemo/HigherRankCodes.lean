import SubcubicMemo.HigherRankBound
import SubcubicMemo.RankOneCodes

/-! Actual storage-code capacities and exact exceptional-row payment for the
one-higher-rank theorem. No intrinsic normalization of general codes is claimed. -/

namespace SubcubicMemo.LowRank

open Module Finset LeanMachine.SubspaceRecovery LeanMachine.SubspaceDefect
open scoped BigOperators Classical

variable {V K W : Type*} [Fintype V] [DecidableEq V] [Field K]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  {G : SimpleGraph V} [DecidableRel G.Adj] {U : V → Submodule K W}

theorem one_high_exception_defect (r : Recovery U) (hs : Supported r G)
    (E : Finset V) (hr : ∀ v ∉ E, ∀ u w,
      1 < finrank K (LinearMap.range (r.component v u)) →
      1 < finrank K (LinearMap.range (r.component v w)) → u = w)
    (hspan : (⨆ v, U v) = ⊤) (htri : G.CliqueFree 3)
    (hdeg : ∀ v, G.degree v ≤ 3) :
    defect U ⊤ ≤ defect U (E.sup U) := by
  let S := E.sup U
  obtain ⟨r', hz, hd⟩ := r.image S.mkQ
  have hs' : Supported r' G := fun v u h => hz v u (hs v u h)
  have hr' : AtMostOneHigh r' := by
    intro v u w hu hw
    by_cases hv : v ∈ E
    · have hzero : (U v).map S.mkQ = ⊥ := by
        apply (Submodule.eq_bot_iff _).mpr
        rintro y ⟨x, hx, rfl⟩
        change S.mkQ x = 0
        simpa only [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using
          (Finset.le_sup (f := U) hv hx : x ∈ S)
      have hdim : finrank K ((U v).map S.mkQ) = 0 := by rw [hzero, finrank_bot]
      have hle := LinearMap.finrank_range_le (r'.component v u)
      omega
    · exact hr v hv u w (hu.trans_le (hd v u)) (hw.trans_le (hd v w))
  exact deficit_of_quotient_half U S (one_high_arrangement_half r' hs' hr'
    (image_span U S.mkQ S.mkQ_surjective hspan) htri hdeg)

section Codes

variable {A : V → Type*} [∀ v, AddCommGroup (A v)] [∀ v, Module K (A v)]
  [∀ v, FiniteDimensional K (A v)]

theorem one_high_code_half (C : Submodule K (∀ v, A v))
    (T : ∀ v u, A u →ₗ[K] A v)
    (hrow : ∀ x ∈ C, ∀ v, ∑ u, T v u (x u) = x v)
    (hs : ∀ v u, ¬ G.Adj v u → T v u = 0)
    (hr : ∀ v u w, 1 < finrank K (LinearMap.range (T v u)) →
      1 < finrank K (LinearMap.range (T v w)) → u = w)
    (htri : G.CliqueFree 3) (hdeg : ∀ v, G.degree v ≤ 3) :
    2 * finrank K C ≤ ∑ v, finrank K (LinearMap.range (coordinate C v)) := by
  obtain ⟨r, hz, hd⟩ := code_dual_recovery C T hrow
  have hh := one_high_arrangement_half r (fun v u h => hz v u (hs v u h))
    (fun v u w hu hw => hr v u w (hu.trans_le (hd v u)) (hw.trans_le (hd v w)))
    (coordinate_duals_span C) htri hdeg
  simpa only [Subspace.dual_finrank_eq,
    LinearMap.finrank_range_dualMap_eq_finrank_range] using hh

theorem one_high_code_capacity (C : Submodule K (∀ v, A v))
    (T : ∀ v u, A u →ₗ[K] A v)
    (hrow : ∀ x ∈ C, ∀ v, ∑ u, T v u (x u) = x v)
    (hs : ∀ v u, ¬ G.Adj v u → T v u = 0)
    (hr : ∀ v u w, 1 < finrank K (LinearMap.range (T v u)) →
      1 < finrank K (LinearMap.range (T v w)) → u = w)
    (htri : G.CliqueFree 3) (hdeg : ∀ v, G.degree v ≤ 3) :
    2 * finrank K C ≤ ∑ v, finrank K (A v) :=
  (one_high_code_half C T hrow hs hr htri hdeg).trans
    (sum_le_sum (fun _ _ => Submodule.finrank_le _))

theorem one_high_block_rank (T : ∀ v u, A u →ₗ[K] A v)
    (hs : ∀ v u, ¬ G.Adj v u → T v u = 0)
    (hr : ∀ v u w, 1 < finrank K (LinearMap.range (T v u)) →
      1 < finrank K (LinearMap.range (T v w)) → u = w)
    (htri : G.CliqueFree 3) (hdeg : ∀ v, G.degree v ≤ 3) :
    (∑ v, finrank K (A v)) ≤
      2 * finrank K (LinearMap.range (LinearMap.id - blockOperator T)) := by
  have hh := one_high_code_capacity (LinearMap.ker (LinearMap.id - blockOperator T))
    T (block_kernel_recovery T) hs hr htri hdeg
  have hn := LinearMap.finrank_range_add_finrank_ker (LinearMap.id - blockOperator T)
  rw [Module.finrank_pi_fintype] at hn
  omega

end Codes

end SubcubicMemo.LowRank
