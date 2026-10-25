import SubcubicMemo.EdgeFactors
import LeanMachine.ProjectionFamilies

/-! The edge factors are projections on the full constrained code. Their
outgoing maps prove the coordinate capacity identities. -/

namespace SubcubicMemo

open Module Finset LeanMachine.SubspaceRecovery LeanMachine.CoordinateSplitting
open scoped BigOperators Classical

variable {V K : Type*} [Fintype V] [DecidableEq V] [Field K]
  {A : V → Type*} [∀ v, AddCommGroup (A v)] [∀ v, Module K (A v)]
  [∀ v, FiniteDimensional K (A v)]
  (T : ∀ v u, A u →ₗ[K] A v) (G : SimpleGraph V) [DecidableRel G.Adj]
  (hs : ∀ v u, ¬ G.Adj v u → T v u = 0)

noncomputable def edgeProjection {u v : V} (hf : (offSquare G).Adj u v) :
    constrainedCode T G →ₗ[K] constrainedCode T G :=
  ((edgeMap T u v).domRestrict (constrainedCode T G)).codRestrict (constrainedCode T G)
    (fun x => (edgeMap_isolated T G hs x.property hf).mem_constrained T G hf.1.ne)

theorem edgeProjection_val {u v : V} (hf : (offSquare G).Adj u v)
    (x : constrainedCode T G) :
    (edgeProjection T G hs hf x).val = edgeMap T u v x.val := rfl

theorem edgeProjection_isolated {u v : V} (hf : (offSquare G).Adj u v)
    (x : constrainedCode T G) :
    IsolatedEdge T u v (edgeProjection T G hs hf x).val :=
  edgeMap_isolated T G hs x.property hf

theorem edgeProjection_idempotent {u v : V} (hf : (offSquare G).Adj u v) :
    (edgeProjection T G hs hf).comp (edgeProjection T G hs hf) =
      edgeProjection T G hs hf := by
  ext x : 1
  apply Subtype.ext
  exact (edgeProjection_isolated T G hs hf x).fixed T hf.1.ne

theorem edgeProjection_annihilate {u v a b : V}
    (hf : (offSquare G).Adj u v) (hg : (offSquare G).Adj a b)
    (hneq : ¬ (a = u ∧ b = v)) (hrev : ¬ (a = v ∧ b = u)) :
    (edgeProjection T G hs hg).comp (edgeProjection T G hs hf) = 0 := by
  ext x : 1
  apply Subtype.ext
  exact (edgeProjection_isolated T G hs hf x).killed_by_other T hneq hrev

def endpointOperator (u v a : V) : A a →ₗ[K] A a :=
  if a = u then (T a v).comp (T v a) else
    if a = v then (T a u).comp (T u a) else 0

theorem edgeProjection_coordinatewise {u v : V} (hf : (offSquare G).Adj u v) (a : V) :
    (endpointOperator T u v a).comp (coordinate (constrainedCode T G) a) =
      (coordinate (constrainedCode T G) a).comp (edgeProjection T G hs hf) := by
  ext x
  change endpointOperator T u v a (x.val a) = edgeMap T u v x.val a
  by_cases hau : a = u
  · subst a
    rw [endpointOperator, if_pos rfl, LinearMap.comp_apply, edgeMap_left T hf.1.ne]
    exact (edge_endpoint_identity T G hs x.property hf).symm
  by_cases hav : a = v
  · subst a
    rw [endpointOperator, if_neg hau, if_pos rfl, LinearMap.comp_apply,
      edgeMap_right T hf.1.ne]
    exact (edge_endpoint_identity T G hs x.property hf.symm).symm
  rw [endpointOperator, if_neg hau, if_neg hav, LinearMap.zero_apply,
    edgeMap_outside T hau hav]

theorem edgeProjection_endpoint_rank {u v : V} (hf : (offSquare G).Adj u v) :
    finrank K (LinearMap.range ((coordinate (constrainedCode T G) u).comp
      (edgeProjection T G hs hf))) =
        finrank K (LinearMap.range (edgeProjection T G hs hf)) := by
  apply rank_factor_eq
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  obtain ⟨x', hx'⟩ := x.property
  obtain ⟨y', hy'⟩ := y.property
  have hxi : IsolatedEdge T u v x.val.val := by
    rw [← hx']; exact edgeProjection_isolated T G hs hf x'
  have hyi : IsolatedEdge T u v y.val.val := by
    rw [← hy']; exact edgeProjection_isolated T G hs hf y'
  exact hxi.eq_of_left T hyi hxy

theorem edgeProjection_symm {u v : V} (hf : (offSquare G).Adj u v) :
    edgeProjection T G hs hf = edgeProjection T G hs hf.symm := by
  ext x : 1
  apply Subtype.ext
  exact LinearMap.congr_fun (edgeMap_symm T u v) x.val

theorem edgeProjection_outside {u v a : V} (hf : (offSquare G).Adj u v)
    (hau : a ≠ u) (hav : a ≠ v) :
    (coordinate (constrainedCode T G) a).comp (edgeProjection T G hs hf) = 0 := by
  ext x
  exact edgeMap_outside T hau hav x.val

theorem edgeProjection_balanced {u v : V} (hf : (offSquare G).Adj u v) :
    (∑ a, finrank K (LinearMap.range ((coordinate (constrainedCode T G) a).comp
      (edgeProjection T G hs hf)))) =
        2 * finrank K (LinearMap.range (edgeProjection T G hs hf)) := by
  let t := finrank K (LinearMap.range (edgeProjection T G hs hf))
  have hl := edgeProjection_endpoint_rank T G hs hf
  have hr : finrank K (LinearMap.range ((coordinate (constrainedCode T G) v).comp
      (edgeProjection T G hs hf))) = t := by
    dsimp [t]
    rw [edgeProjection_symm T G hs hf]
    exact edgeProjection_endpoint_rank T G hs hf.symm
  calc
    _ = ∑ a, ((if a = u then t else 0) + (if a = v then t else 0)) := by
      apply sum_congr rfl
      intro a _
      by_cases hau : a = u
      · subst a; simpa only [ite_true, if_neg hf.1.ne, add_zero] using hl
      by_cases hav : a = v
      · subst a; simpa only [ite_true, if_neg (Ne.symm hf.1.ne), zero_add] using hr
      rw [edgeProjection_outside T G hs hf hau hav, LinearMap.range_zero, finrank_bot]
      simp [hau, hav]
    _ = _ := by rw [sum_add_distrib]; simp [two_mul, t]

end SubcubicMemo
