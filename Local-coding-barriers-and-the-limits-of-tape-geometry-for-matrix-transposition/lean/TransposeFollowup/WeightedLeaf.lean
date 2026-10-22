import TransposeFollowup.WeightedFragmentation

/-! The two leaf operations used by weighted tree fragmentation: delete an
overweight leaf, or accumulate a light leaf's weight at its unique neighbor.
All component mass and separator cardinality accounting is explicit. -/

namespace TransposeFollowup

open scoped BigOperators
open Classical
set_option autoImplicit false
universe u

namespace WeightedFragmentation

variable {V : Type u} [Fintype V] {G : SimpleGraph V} {w : V → ℕ} {L : ℕ}

noncomputable def deleteVertex (v : V)
    (F : WeightedFragmentation (withoutVertex G v) (fun x => w x.val) L) :
    WeightedFragmentation G w L where
  removed := insert v (liftRemoved v F.removed)
  Label := Option F.Label
  label := extendLabel v F.label none
  edge_same := by
    intro x y hx hy hxy
    have hxv : x ≠ v := fun h => hx (Finset.mem_insert.mpr (Or.inl h))
    have hyv : y ≠ v := fun h => hy (Finset.mem_insert.mpr (Or.inl h))
    have hxs : (⟨x, hxv⟩ : {x // x ≠ v}) ∉ F.removed := by
      intro hs
      exact hx (Finset.mem_insert_of_mem ((mem_liftRemoved v F.removed _).mpr hs))
    have hys : (⟨y, hyv⟩ : {x // x ≠ v}) ∉ F.removed := by
      intro hs
      exact hy (Finset.mem_insert_of_mem ((mem_liftRemoved v F.removed _).mpr hs))
    simpa [extendLabel, hxv, hyv] using congrArg some (F.edge_same hxs hys hxy)
  mass_le := by
    intro a
    rw [labelMass_extend_removed]
    cases a with
    | none => simp
    | some a => simpa using F.mass_le a

@[simp] theorem deleteVertex_card (v : V)
    (F : WeightedFragmentation (withoutVertex G v) (fun x => w x.val) L) :
    (F.deleteVertex v).removed.card = F.removed.card + 1 := by
  simp [deleteVertex]

/-- A light leaf may be retained. If its neighbor is deleted, the leaf becomes
an isolated label. Otherwise it joins its neighbor's label, and its weight
was already charged to that label in the smaller weighted tree. -/
noncomputable def attachLeaf (v : V) (u : {x // x ≠ v})
    (hneighbor : ∀ x, G.Adj v x → x = u.val) (hw : w v ≤ L)
    (F : WeightedFragmentation (withoutVertex G v)
      (addWeight (fun x => w x.val) u (w v)) L) : WeightedFragmentation G w L where
  removed := liftRemoved v F.removed
  Label := Option F.Label
  label := extendLabel v F.label (if u ∈ F.removed then none else some (F.label u))
  edge_same := by
    intro x y hx hy hxy
    by_cases hxv : x = v
    · subst x
      have hyu := hneighbor y hxy
      subst y
      have hu : u ∉ F.removed := by simpa using hy
      simp [hu]
    · by_cases hyv : y = v
      · subst y
        have hxu := hneighbor x hxy.symm
        subst x
        have hu : u ∉ F.removed := by simpa using hx
        simp [hu]
      · have hxs : (⟨x, hxv⟩ : {x // x ≠ v}) ∉ F.removed := by
          intro hs
          exact hx ((mem_liftRemoved v F.removed _).mpr hs)
        have hys : (⟨y, hyv⟩ : {x // x ≠ v}) ∉ F.removed := by
          intro hs
          exact hy ((mem_liftRemoved v F.removed _).mpr hs)
        simpa [extendLabel, hxv, hyv] using congrArg some (F.edge_same hxs hys hxy)
  mass_le := by
    intro a
    rw [labelMass_extend]
    cases a with
    | none =>
        rw [labelMass_none, add_zero]
        by_cases hu : u ∈ F.removed
        · simpa [hu] using hw
        · simp [hu]
    | some a =>
        rw [labelMass_some]
        have h := F.mass_le a
        rw [labelMass_addWeight] at h
        by_cases hu : u ∈ F.removed
        · simpa [hu] using h
        · simpa [hu, Nat.add_comm] using h

@[simp] theorem attachLeaf_card (v : V) (u : {x // x ≠ v})
    (hneighbor : ∀ x, G.Adj v x → x = u.val) (hw : w v ≤ L)
    (F : WeightedFragmentation (withoutVertex G v)
      (addWeight (fun x => w x.val) u (w v)) L) :
    (F.attachLeaf v u hneighbor hw).removed.card = F.removed.card := by
  simp [attachLeaf]

end WeightedFragmentation
end TransposeFollowup
