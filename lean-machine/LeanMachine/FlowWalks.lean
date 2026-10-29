import LeanMachine.FlowPathMap

/-! Undirected walks with original edge identities. The two orientations
are explicit, and the charged load adds both rather than cancelling them. -/

namespace LeanMachine.FiniteFlow.Network

open Finset
open scoped BigOperators Classical
noncomputable section

variable {V E : Type*} (G : Network V E)

/-- Orientation copies are only a representation of walks. A physical
capacity bound must use `walkLoad`, not two independent capacities. -/
def bidirected : Network V (E ⊕ E) where
  source := Sum.elim G.source G.target
  target := Sum.elim G.target G.source
  capacity := Sum.elim G.capacity G.capacity
  capacity_nonneg := by rintro (e | e) <;> exact G.capacity_nonneg e

def forwardMap : G.Map G.bidirected where
  node := id
  edge := Sum.inl
  source := fun _ => rfl
  target := fun _ => rfl

def walkLoad {s t : V} (p : G.bidirected.Path s t) (e : E) : ℝ :=
  G.bidirected.pathFlow p (.inl e) + G.bidirected.pathFlow p (.inr e)

theorem walkLoad_nonneg {s t : V} (p : G.bidirected.Path s t) (e : E) :
    0 ≤ G.walkLoad p e :=
  add_nonneg (G.bidirected.pathFlow_nonneg p _) (G.bidirected.pathFlow_nonneg p _)

theorem walkLoad_comp {s u t : V} (p : G.bidirected.Path s u)
    (q : G.bidirected.Path u t) (e : E) :
    G.walkLoad (pathComp p q) e = G.walkLoad p e + G.walkLoad q e := by
  simp only [walkLoad, pathFlow_comp, Pi.add_apply]
  ring

theorem walkLoad_forward {s t : V} (p : G.Path s t) (e : E) :
    G.walkLoad (G.forwardMap.path p) e = G.pathFlow p e := by
  have hf := G.forwardMap.pathFlow_map_of_injective Sum.inl_injective p e
  have hb := G.forwardMap.pathFlow_map_outside p (.inr e)
    (by simp [forwardMap])
  exact (congrArg₂ (· + ·) hf hb).trans (add_zero _)

variable {n : ℕ}

/-- An actual memory spine in a network. Other edges may be arbitrary. -/
structure Spine (G : Network (Fin n) E) where
  edge : Fin (n - 1) → E
  source : ∀ v, (G.source (edge v)).val = v.val
  target : ∀ v, (G.target (edge v)).val = v.val + 1

namespace Spine

variable {G : Network (Fin n) E} (S : G.Spine)

theorem edge_injective : Function.Injective S.edge := by
  intro u v he
  apply Fin.ext
  simpa only [S.source] using congrArg (fun e => (G.source e).val) he

/-- The backward spine walk crosses exactly the indicated half-open
interval, once per edge. No graph acyclicity assumption is needed. -/
theorem exists_return (s t : Fin n) (hts : t ≤ s) :
    ∃ p : G.bidirected.Path s t,
      (∀ v : Fin (n - 1), G.walkLoad p (S.edge v) =
        if t.val ≤ v.val ∧ v.val < s.val then 1 else 0) ∧
      (∀ e, e ∉ Set.range S.edge → G.walkLoad p e = 0) := by
  generalize hk : s.val = k
  induction k using Nat.strong_induction_on generalizing s with
  | h k ih =>
    subst k
    by_cases hst : s = t
    · subst t
      refine ⟨@Quiver.Path.nil _ G.bidirected.quiver s, ?_, ?_⟩
      · intro v
        simp only [walkLoad, pathFlow, Pi.zero_apply, add_zero]
        split_ifs <;> first | omega | norm_num
      · intro e _
        simp [walkLoad, pathFlow]
    · have hlt : t < s := lt_of_le_of_ne hts (Ne.symm hst)
      let u : Fin n := ⟨s.val - 1, by omega⟩
      let v : Fin (n - 1) := ⟨s.val - 1, by omega⟩
      have hus : u.val < s.val := by dsimp [u]; omega
      have htu : t ≤ u := by change t.val ≤ s.val - 1; omega
      obtain ⟨q, hq, hqout⟩ := ih u.val hus u htu rfl
      have hs : G.target (S.edge v) = s := by
        apply Fin.ext
        rw [S.target]
        dsimp [v]
        omega
      have hu : G.source (S.edge v) = u := by
        apply Fin.ext
        exact S.source v
      let step : G.bidirected.Path s u :=
        @Quiver.Hom.toPath _ G.bidirected.quiver s u ⟨.inr (S.edge v), hs, hu⟩
      have hstep (e : E) : G.walkLoad step e = if e = S.edge v then 1 else 0 := by
        simp [step, walkLoad, Quiver.Hom.toPath, pathFlow, unit]
      refine ⟨pathComp step q, ?_, ?_⟩
      · intro w
        rw [G.walkLoad_comp, hstep, hq, S.edge_injective.eq_iff]
        have hv : v.val = s.val - 1 := rfl
        have hu : u.val = s.val - 1 := rfl
        by_cases hw : w = v
        · subst w
          simp only [↓reduceIte, hu, hv]
          split_ifs <;> first | omega | norm_num
        · have hne : w.val ≠ s.val - 1 := fun he => hw (Fin.ext (he.trans hv.symm))
          simp only [hw, ↓reduceIte, zero_add, hu]
          have hc : (t.val ≤ w.val ∧ w.val < s.val - 1) ↔
              (t.val ≤ w.val ∧ w.val < s.val) := by omega
          simp only [hc]
      · intro e he
        rw [G.walkLoad_comp, hstep, hqout e he]
        have hn : e ≠ S.edge v := fun h => he ⟨v, h.symm⟩
        simp [hn]

end Spine
end
end LeanMachine.FiniteFlow.Network
