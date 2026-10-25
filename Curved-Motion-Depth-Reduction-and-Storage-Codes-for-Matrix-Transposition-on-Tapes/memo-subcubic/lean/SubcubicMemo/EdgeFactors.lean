import SubcubicMemo.TwoStepDefect

/-! Actual isolated edge codewords obtained inside the constrained full
kernel. Closure in an arbitrarily chosen subcode is not assumed. -/

namespace SubcubicMemo

open Module Finset LeanMachine.SubspaceRecovery
open scoped BigOperators Classical

variable {V K : Type*} [Fintype V] [DecidableEq V] [Field K]
  {A : V → Type*} [∀ v, AddCommGroup (A v)] [∀ v, Module K (A v)]
  [∀ v, FiniteDimensional K (A v)]
  (T : ∀ v u, A u →ₗ[K] A v) (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def constrainedCode : Submodule K (∀ v, A v) :=
  LinearMap.ker (LinearMap.id - blockOperator T) ⊓
    LinearMap.ker (separatedConstraint T G)

theorem constrained_recovery {x : ∀ v, A v} (hx : x ∈ constrainedCode T G) (v : V) :
    ∑ u, T v u (x u) = x v := block_kernel_recovery T x hx.1 v

theorem constrained_twoStep (hs : ∀ v u, ¬ G.Adj v u → T v u = 0)
    {x : ∀ v, A v} (hx : x ∈ constrainedCode T G)
    {a b c : V} (hab : G.Adj a b) (hbc : G.Adj b c) (hac : a ≠ c)
    (hf : (offSquare G).Adj a b ∨ (offSquare G).Adj b c) :
    T a b (T b c (x c)) = 0 := by
  have h := congrFun (congrFun (LinearMap.mem_ker.mp hx.2) c) a
  have hz : touchedPair G a c := ⟨hac, b, hab, hbc, hf⟩
  rw [separatedConstraint_apply, if_pos hz,
    defectBlock_unique T G hs hab hbc hac hf] at h
  exact h

def edgeMap (u v : V) : (∀ v, A v) →ₗ[K] (∀ v, A v) :=
  (LinearMap.single K A u).comp ((T u v).comp (LinearMap.proj v)) +
  (LinearMap.single K A v).comp ((T v u).comp (LinearMap.proj u))

theorem edgeMap_symm (u v : V) : edgeMap T u v = edgeMap T v u := by
  unfold edgeMap
  exact add_comm _ _

theorem edgeMap_left {u v : V} (huv : u ≠ v) (x : ∀ v, A v) :
    edgeMap T u v x u = T u v (x v) := by
  simp [edgeMap, LinearMap.single_apply, Pi.single_eq_of_ne huv]

theorem edgeMap_right {u v : V} (huv : u ≠ v) (x : ∀ v, A v) :
    edgeMap T u v x v = T v u (x u) := by
  rw [edgeMap_symm]
  exact edgeMap_left T huv.symm x

theorem edgeMap_outside {u v a : V} (hau : a ≠ u) (hav : a ≠ v) (x : ∀ v, A v) :
    edgeMap T u v x a = 0 := by
  simp [edgeMap, LinearMap.single_apply, Pi.single_eq_of_ne hau, Pi.single_eq_of_ne hav]

/-- The two endpoint equations, zero coordinates elsewhere, and no outgoing
transmission away from the edge. -/
structure IsolatedEdge (u v : V) (y : ∀ v, A v) : Prop where
  left : T u v (y v) = y u
  right : T v u (y u) = y v
  outside : ∀ a, a ≠ u → a ≠ v → y a = 0
  leave_left : ∀ a, a ≠ v → T a u (y u) = 0
  leave_right : ∀ a, a ≠ u → T a v (y v) = 0

namespace IsolatedEdge

theorem eq_of_left {u v : V} {y z : ∀ v, A v}
    (hy : IsolatedEdge T u v y) (hz : IsolatedEdge T u v z) (h : y u = z u) : y = z := by
  funext a
  by_cases hau : a = u
  · subst a; exact h
  by_cases hav : a = v
  · subst a
    rw [← hy.right, ← hz.right, h]
  rw [hy.outside a hau hav, hz.outside a hau hav]

theorem symm {u v : V} {y : ∀ v, A v} (h : IsolatedEdge T u v y) :
    IsolatedEdge T v u y :=
  ⟨h.right, h.left, fun a hav hau => h.outside a hau hav, h.leave_right, h.leave_left⟩

theorem fixed {u v : V} (huv : u ≠ v) {y : ∀ v, A v} (h : IsolatedEdge T u v y) :
    edgeMap T u v y = y := by
  funext a
  by_cases hau : a = u
  · subst a
    rw [edgeMap_left T huv]
    exact h.left
  by_cases hav : a = v
  · subst a
    rw [edgeMap_right T huv]
    exact h.right
  rw [edgeMap_outside T hau hav, h.outside a hau hav]

theorem recovery {u v : V} (huv : u ≠ v) {y : ∀ v, A v} (h : IsolatedEdge T u v y)
    (a : V) : ∑ b, T a b (y b) = y a := by
  by_cases hau : a = u
  · subst a
    calc
      _ = T u v (y v) := sum_eq_single v (by
        intro b _ hb
        by_cases hbu : b = u
        · subst b; exact h.leave_left u huv
        · rw [h.outside b hbu hb, map_zero]) (by simp)
      _ = _ := h.left
  by_cases hav : a = v
  · subst a
    calc
      _ = T v u (y u) := sum_eq_single u (by
        intro b _ hb
        by_cases hbv : b = v
        · subst b; exact h.leave_right v huv.symm
        · rw [h.outside b hb hbv, map_zero]) (by simp)
      _ = _ := h.right
  rw [h.outside a hau hav]
  apply sum_eq_zero
  intro b _
  by_cases hbu : b = u
  · subst b; exact h.leave_left a hav
  by_cases hbv : b = v
  · subst b; exact h.leave_right a hau
  rw [h.outside b hbu hbv, map_zero]

theorem twoStep_zero {u v : V} {y : ∀ v, A v} (h : IsolatedEdge T u v y)
    {a b c : V} (hac : a ≠ c) : T a b (T b c (y c)) = 0 := by
  by_cases hcu : c = u
  · subst c
    by_cases hbv : b = v
    · subst b; rw [h.right]; exact h.leave_right a hac
    · rw [h.leave_left b hbv, map_zero]
  by_cases hcv : c = v
  · subst c
    by_cases hbu : b = u
    · subst b; rw [h.left]; exact h.leave_left a hac
    · rw [h.leave_right b hbu, map_zero]
  rw [h.outside c hcu hcv, map_zero, map_zero]

theorem mem_constrained {u v : V} (huv : u ≠ v) {y : ∀ v, A v}
    (h : IsolatedEdge T u v y) : y ∈ constrainedCode T G := by
  constructor
  · change y - blockOperator T y = 0
    funext a
    change y a - blockOperator T y a = 0
    rw [blockOperator_apply, h.recovery T huv, sub_self]
  · change separatedConstraint T G y = 0
    funext c a
    rw [separatedConstraint_apply]
    by_cases hac : touchedPair G a c
    · rw [if_pos hac, defectBlock, if_neg hac.1, squareBlock, LinearMap.sum_apply]
      exact sum_eq_zero fun b _ => h.twoStep_zero T hac.1
    · simp [hac]

theorem killed_by_other {u v a b : V} {y : ∀ v, A v}
    (h : IsolatedEdge T u v y)
    (hneq : ¬ (a = u ∧ b = v)) (hrev : ¬ (a = v ∧ b = u)) :
    edgeMap T a b y = 0 := by
  have h0 : T a b (y b) = 0 := by
    by_cases hbu : b = u
    · subst b
      exact h.leave_left a (fun hav => hrev ⟨hav, rfl⟩)
    by_cases hbv : b = v
    · subst b
      exact h.leave_right a (fun hau => hneq ⟨hau, rfl⟩)
    rw [h.outside b hbu hbv, map_zero]
  have h1 : T b a (y a) = 0 := by
    by_cases hau : a = u
    · subst a
      exact h.leave_left b (fun hbv => hneq ⟨rfl, hbv⟩)
    by_cases hav : a = v
    · subst a
      exact h.leave_right b (fun hbu => hrev ⟨rfl, hbu⟩)
    rw [h.outside a hau hav, map_zero]
  ext c
  simp [edgeMap, h0, h1]

end IsolatedEdge

variable (hs : ∀ v u, ¬ G.Adj v u → T v u = 0)

include hs in
theorem edge_endpoint_identity {x : ∀ v, A v} (hx : x ∈ constrainedCode T G)
    {u v : V} (hf : (offSquare G).Adj u v) :
    T u v (x v) = T u v (T v u (x u)) := by
  calc
    _ = ∑ b, T u v (T v b (x b)) := by rw [← constrained_recovery T G hx v, map_sum]
    _ = _ := sum_eq_single u (by
      intro b _ hbu
      by_cases hvb : G.Adj v b
      · exact constrained_twoStep T G hs hx hf.1 hvb hbu.symm (Or.inl hf)
      · rw [hs v b hvb, LinearMap.zero_apply, map_zero]) (by simp)

include hs in
theorem edgeMap_isolated {x : ∀ v, A v} (hx : x ∈ constrainedCode T G)
    {u v : V} (hf : (offSquare G).Adj u v) :
    IsolatedEdge T u v (edgeMap T u v x) := by
  have huv := hf.1.ne
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [edgeMap_left T huv, edgeMap_right T huv]
    exact (edge_endpoint_identity T G hs hx hf).symm
  · rw [edgeMap_left T huv, edgeMap_right T huv]
    exact (edge_endpoint_identity T G hs hx hf.symm).symm
  · intro a hau hav
    exact edgeMap_outside T hau hav x
  · intro a hav
    rw [edgeMap_left T huv]
    by_cases hau : G.Adj a u
    · exact constrained_twoStep T G hs hx hau hf.1 hav (Or.inr hf)
    · rw [hs a u hau, LinearMap.zero_apply]
  · intro a hau
    rw [edgeMap_right T huv]
    by_cases hav : G.Adj a v
    · exact constrained_twoStep T G hs hx hav hf.1.symm hau (Or.inr hf.symm)
    · rw [hs a v hav, LinearMap.zero_apply]

end SubcubicMemo
