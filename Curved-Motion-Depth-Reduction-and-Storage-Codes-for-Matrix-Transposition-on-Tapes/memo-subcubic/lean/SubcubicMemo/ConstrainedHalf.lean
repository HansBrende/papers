import SubcubicMemo.EdgeProjections
import SubcubicMemo.LinearPolymatroid

/-! The actual constrained kernel inherits the weighted half bound from
the original square-edge graph. All off-square factors are accounted for. -/

namespace SubcubicMemo

open Module Finset LeanMachine.SubspaceRecovery LeanMachine.CoordinateSplitting MotionDepthCodes
open scoped BigOperators Classical

variable {V K : Type*} [Fintype V] [DecidableEq V] [Field K]
  {A : V → Type*} [∀ v, AddCommGroup (A v)] [∀ v, Module K (A v)]
  [∀ v, FiniteDimensional K (A v)]
  (T : ∀ v u, A u →ₗ[K] A v) (G : SimpleGraph V) [DecidableRel G.Adj]
  (hs : ∀ v u, ¬ G.Adj v u → T v u = 0)

def OrientedOffEdge := {e : V × V // (offSquare G).Adj e.1 e.2 ∧
  Fintype.equivFin V e.1 < Fintype.equivFin V e.2}

noncomputable instance : Fintype (OrientedOffEdge G) := by
  unfold OrientedOffEdge
  infer_instance

noncomputable def offProjections (e : OrientedOffEdge G) :
    constrainedCode T G →ₗ[K] constrainedCode T G :=
  edgeProjection T G hs e.property.1

theorem offProjections_orthogonal (e f : OrientedOffEdge G) :
    (offProjections T G hs e).comp (offProjections T G hs f) =
      if e = f then offProjections T G hs e else 0 := by
  by_cases hef : e = f
  · subst f
    rw [if_pos rfl]
    exact edgeProjection_idempotent T G hs e.property.1
  rw [if_neg hef]
  apply edgeProjection_annihilate
  · intro h
    exact hef (Subtype.ext (Prod.ext h.1 h.2))
  · rintro ⟨h1, h2⟩
    have he := e.property.2
    have hf := f.property.2
    rw [h1, h2] at he
    exact (lt_asymm he hf)

theorem offProjections_zero {x : constrainedCode T G}
    (hx : ∀ e : OrientedOffEdge G, offProjections T G hs e x = 0)
    {u v : V} (huv : (offSquare G).Adj u v) : T u v (x.val v) = 0 := by
  have hne : Fintype.equivFin V u ≠ Fintype.equivFin V v :=
    fun h => huv.1.ne ((Fintype.equivFin V).injective h)
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · let e : OrientedOffEdge G := ⟨(u, v), huv, hlt⟩
    have he := congrFun (congrArg Subtype.val (hx e)) u
    change edgeMap T u v x.val u = 0 at he
    rwa [edgeMap_left T huv.1.ne] at he
  · let e : OrientedOffEdge G := ⟨(v, u), huv.symm, hlt⟩
    have he := congrFun (congrArg Subtype.val (hx e)) u
    change edgeMap T v u x.val u = 0 at he
    rwa [edgeMap_right T huv.1.ne.symm] at he

include hs in
set_option maxHeartbeats 1200000 in
theorem constrained_half_of_squareCore_good
    (hgood : RateBound (nbhd (squareCore G)) (1 / 2)) :
    2 * finrank K (constrainedCode T G) ≤
      ∑ v, finrank K (LinearMap.range (coordinate (constrainedCode T G) v)) := by
  let p := offProjections T G hs
  have hp : ∀ e f, (p e).comp (p f) = if e = f then p e else 0 :=
    offProjections_orthogonal T G hs
  let S := LinearMap.ker (∑ e, p e)
  let R : ∀ v, S →ₗ[K] A v := fun v =>
    (coordinate (constrainedCode T G) v).domRestrict S
  let T' : ∀ v u, A u →ₗ[K] A v := fun v u =>
    if (squareCore G).Adj v u then T v u else 0
  have hz (x : S) {u v : V} (huv : (offSquare G).Adj u v) :
      T u v (x.val.val v) = 0 := by
    apply offProjections_zero T G hs
      ((projection_sum_ker p hp x.val).mp x.property) huv
  have hrow (x : S) (v : V) : ∑ u, T' v u (R u x) = R v x := by
    change (∑ u, T' v u (x.val.val u)) = x.val.val v
    rw [← constrained_recovery T G x.val.property v]
    apply sum_congr rfl
    intro u _
    by_cases hsq : (squareCore G).Adj v u
    · simp only [T', if_pos hsq]
    simp only [T', if_neg hsq, LinearMap.zero_apply]
    by_cases hadj : G.Adj v u
    · exact (hz x ⟨hadj, hsq⟩).symm
    · rw [hs v u hadj, LinearMap.zero_apply]
  have hsep (x : S) (hx : ∀ v, R v x = 0) : x = 0 := by
    apply Subtype.ext
    apply Subtype.ext
    exact funext hx
  have hres := observation_half_of_rateBound (W := S) R T' hrow hsep
    (G := squareCore G) (fun v u h => by simp [T', h]) hgood
  apply half_of_residual p hp (coordinate (constrainedCode T G))
    (fun e v => endpointOperator T e.val.1 e.val.2 v)
    (fun e v => edgeProjection_coordinatewise T G hs e.property.1 v)
    (fun e => edgeProjection_balanced T G hs e.property.1)
  exact hres

end SubcubicMemo
