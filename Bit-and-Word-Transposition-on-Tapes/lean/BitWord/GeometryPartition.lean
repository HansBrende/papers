import BitWord.GeometryOperations

namespace BitWord.Geometry

/-- An exact public heterogeneous partition endpoint. The laws give the raw
forward and inverse action of the declared operations, not a geometric or
complexity certificate. Different blocks may have different operation kinds.
This also admits mixed stages, a harmless enlargement of the grammar. -/
structure PartitionStage (P : ℕ) where
  count : ℕ
  intervals : IntervalFamily (Fin count)
  operation : Fin count → BlockOperation
  length_eq : ∀ i, intervals.length i = (operation i).length
  admissible : ∀ i, (operation i).Admissible
  bounded : ∀ i, intervals.start i + intervals.length i ≤ P
  endpoint : Equiv.Perm (Fin P)
  action : ∀ (back : Bool) i x, intervals.contains i x →
    finiteAct (oriented endpoint back) x =
      intervals.start i + (operation i).act back (x - intervals.start i)
  outside : ∀ (back : Bool) x, (∀ i, ¬ intervals.contains i x) →
    finiteAct (oriented endpoint back) x = x

namespace PartitionStage
variable {P : ℕ} (T : PartitionStage P)

 def act (back : Bool) : ℕ → ℕ := finiteAct (oriented T.endpoint back)
 def bad (B : ℕ) : Finset ℕ :=
   (Finset.univ.filter (fun i => (T.operation i).bad B)).biUnion T.intervals.points

 @[simp] theorem mem_bad {B x : ℕ} : x ∈ T.bad B ↔
     ∃ i, (T.operation i).bad B ∧ T.intervals.contains i x := by
   simp [bad]

 theorem bad_subset_range (B : ℕ) : T.bad B ⊆ Finset.range P := by
   intro x hx
   obtain ⟨i, hi, hx⟩ := T.mem_bad.mp hx
   exact Finset.mem_range.mpr (lt_of_lt_of_le hx.2 (T.bounded i))

 theorem act_inside (back : Bool) (i : Fin T.count) (x : ℕ)
     (hx : T.intervals.contains i x) : T.intervals.contains i (T.act back x) := by
   have hs := Nat.sub_add_cancel hx.1
   have hlocal : x - T.intervals.start i < (T.operation i).length := by
     rw [← T.length_eq]
     have := hx.2
     omega
   have ho := (T.operation i).act_lt back hlocal
   rw [show T.act back x = _ from T.action back i x hx]
   constructor
   · omega
   · rw [T.length_eq]
     omega

 @[simp] theorem act_inverse (back : Bool) (x : ℕ) :
     T.act (!back) (T.act back x) = x := by
   cases back
   · exact finiteAct_symm_apply T.endpoint x
   · simpa [act, oriented] using finiteAct_symm_apply T.endpoint.symm x

 theorem bad_invariant (back : Bool) {B x : ℕ} :
     T.act back x ∈ T.bad B ↔ x ∈ T.bad B := by
   constructor
   · intro h
     obtain ⟨i, hi, hx⟩ := T.mem_bad.mp h
     have hr := T.act_inside (!back) i _ hx
     rw [T.act_inverse] at hr
     exact T.mem_bad.mpr ⟨i, hi, hr⟩
   · intro h
     obtain ⟨i, hi, hx⟩ := T.mem_bad.mp h
     exact T.mem_bad.mpr ⟨i, hi, T.act_inside back i x hx⟩

 /-- The checked one-stage geometry, in both directions, for arbitrary subsets
 of a source bin avoiding that stage's bad blocks. -/
 theorem good_image_bins_le (back : Bool) {B j : ℕ} (hB : 0 < B)
     (S : Finset ℕ)
     (hS : ∀ x ∈ S, j * B ≤ x ∧ x < (j + 1) * B)
     (hgood : ∀ x ∈ S, x ∉ T.bad B) :
     (bins B (S.image (T.act back))).card ≤ 11 := by
   apply T.intervals.good_image_bins_le (T.act back)
     (fun i => (T.operation i).bad B) hB S hS
   · intro x hx i hi hb
     exact hgood x hx (T.mem_bad.mpr ⟨i, hb, hi⟩)
   · exact T.act_inside back
   · exact T.outside back
   · intro i hi hl
     apply (T.operation i).good_large_image (a := T.intervals.start i) (T.admissible i) back hB hi
       (by simpa [T.length_eq] using hl) (S.filter (T.intervals.contains i))
       (T.act back)
     · intro x hx
       exact hS x (Finset.mem_filter.mp hx).1
     · intro x hx
       simpa only [IntervalFamily.contains, T.length_eq] using (Finset.mem_filter.mp hx).2
     · intro x hx
       exact T.action back i x (Finset.mem_filter.mp hx).2

end PartitionStage
end BitWord.Geometry
