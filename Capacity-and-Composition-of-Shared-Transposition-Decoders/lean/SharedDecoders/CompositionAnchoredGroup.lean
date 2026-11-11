import SharedDecoders.CompositionAnchoredLocal

/-! # Transitivity of the actual anchored adjacent-pair group -/

namespace SharedDecoders

open scoped CharTwo

variable {d : ℕ} [NeZero d]

def wordConjugation {X : Type*} (L : Equiv.Perm X) :
    Equiv.Perm X →* Equiv.Perm X where
  toFun g := L*g*L⁻¹
  map_one' := by group
  map_mul' g h := by group

noncomputable def anchoredPullGroup (d : ℕ) [NeZero d] : Subgroup (Equiv.Perm (BitWord d)) :=
  (conjugatePairGroup (anchoredDifference (ZMod 2) d) 0 1).comap
    (wordConjugation (anchoredDifference (ZMod 2) d))

lemma anchoredPullGroup_rotation (s : ZMod d) : scalarRotation s ∈ anchoredPullGroup d := by
  have h : scalarRotation (1 : ZMod d) ∈ anchoredPullGroup d := by
    change anchoredDifference (ZMod 2) d * scalarRotation 1 *
      (anchoredDifference (ZMod 2) d)⁻¹ ∈ conjugatePairGroup (anchoredDifference (ZMod 2) d) 0 1
    rw [← conjugateWordRotation_zero]
    exact Subgroup.subset_closure (by simp)
  have hp := (anchoredPullGroup d).pow_mem h s.val
  simpa only [scalarRotation_pow, ZMod.natCast_zmod_val] using hp

lemma anchoredPullGroup_local : anchoredLocalPerm d ∈ anchoredPullGroup d := by
  let L := anchoredDifference (ZMod 2) d
  let Q0 := conjugateWordRotation L 0
  let Q1 := conjugateWordRotation L 1
  have h0 : Q0 ∈ conjugatePairGroup L 0 1 := Subgroup.subset_closure (by simp [Q0])
  have h1 : Q1 ∈ conjugatePairGroup L 0 1 := Subgroup.subset_closure (by simp [Q1])
  change L * anchoredLocalPerm d * L⁻¹ ∈ conjugatePairGroup L 0 1
  have he : L * anchoredLocalPerm d * L⁻¹ = Q0⁻¹ * Q1 := by
    dsimp [Q0, Q1, L, anchoredLocalPerm]
    rw [conjugateWordRotation_zero]
    group
  rw [he]
  exact (conjugatePairGroup L 0 1).mul_mem
    ((conjugatePairGroup L 0 1).inv_mem h0) h1

lemma anchoredPullGroup_fixes (g : anchoredPullGroup d) : g.val 0 = 0 := by
  have hL0 : anchoredDifference (ZMod 2) d (0 : BitWord d) = 0 := anchoredDifference_zero
  have hh : wordConjugation (anchoredDifference (ZMod 2) d) g.val ∈
      conjugatePairGroup (anchoredDifference (ZMod 2) d) 0 1 := g.property
  have hz := conjugatePairGroup_fixes (anchoredDifference (ZMod 2) d) 0
    anchoredDifference_zero 0 1 ⟨_,hh⟩
  have hLi : (anchoredDifference (ZMod 2) d)⁻¹ (0 : BitWord d) = 0 := by
    change (anchoredDifference (ZMod 2) d).symm 0 = 0
    apply (anchoredDifference (ZMod 2) d).injective
    rw [Equiv.apply_symm_apply,hL0]
  change anchoredDifference (ZMod 2) d (g.val ((anchoredDifference (ZMod 2) d)⁻¹ 0)) = 0 at hz
  rw [hLi] at hz
  exact (anchoredDifference (ZMod 2) d).injective (hz.trans hL0.symm)

lemma anchored_local_reachable (hd : 3 ≤ d) (x : BitWord d) :
    wordReach (anchoredPullGroup d) x (anchoredLocal x) :=
  ⟨⟨anchoredLocalPerm d,anchoredPullGroup_local⟩,anchoredLocalPerm_apply hd x⟩

lemma anchored_local_three_reachable (hd : 3 ≤ d) (x : BitWord d) :
    wordReach (anchoredPullGroup d) x (anchoredLocal (anchoredLocal (anchoredLocal x))) :=
  wordReach_trans (anchored_local_reachable hd x)
    (wordReach_trans (anchored_local_reachable hd _) (anchored_local_reachable hd _))

lemma anchored_move (hd : 3 ≤ d) (x : BitWord d)
    (h0 : x 0 = 1) (h1 : x 1 = 0) (h2 : x 2 = 0) :
    ∃ y, wordReach (anchoredPullGroup d) x y ∧ y 0 = 0 ∧ y 1 = 1 ∧
      ∀ i, i ≠ 0 → i ≠ 1 → y i = x i := by
  refine ⟨anchoredLocal (anchoredLocal (anchoredLocal x)),
    anchored_local_three_reachable hd x, ?_, ?_, ?_⟩
  · simp [anchoredLocal_zero hd, anchoredLocal_one hd, anchoredLocal_two hd,h1,h2]
  · simp [anchoredLocal_zero hd, anchoredLocal_one hd, anchoredLocal_two hd,h0,h1,h2]
  · intro i hi0 hi1
    simp [anchoredLocal_out _ i hi0 hi1, anchoredLocal_zero hd,
      anchoredLocal_one hd, anchoredLocal_two hd,h0,h1,h2]

lemma bitSupport_drop_zero (x y : BitWord d) (hx : x 0 = 1) (hy : y 0 = 0)
    (hsub : ∀ i, y i = 1 → x i = 1) : (bitSupport y).card < (bitSupport x).card := by
  classical
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro i hi
    exact (mem_bitSupport x i).mpr (hsub i ((mem_bitSupport y i).mp hi))
  · intro he
    have h0 : 0 ∈ bitSupport y := he.symm ▸ (mem_bitSupport x 0).mpr hx
    have hh := (mem_bitSupport y 0).mp h0
    simp [hy] at hh

lemma anchored_merge (hd : 3 ≤ d) (x : BitWord d)
    (h0 : x 0 = 1) (hne : x 1 = 1 ∨ x 2 = 1) :
    ∃ y, wordReach (anchoredPullGroup d) x y ∧ (bitSupport y).card < (bitSupport x).card := by
  by_cases h1 : x 1 = 1
  · by_cases h2 : x 2 = 1
    · let y := anchoredLocal (anchoredLocal x)
      refine ⟨y,wordReach_trans (anchored_local_reachable hd _) (anchored_local_reachable hd _),
        bitSupport_drop_zero x y h0 ?_ ?_⟩
      · simp [y,anchoredLocal_zero hd,anchoredLocal_two hd,h0,h1]
      · intro i hi
        by_cases hi0 : i=0
        · simpa [hi0] using h0
        by_cases hi1 : i=1
        · simpa [hi1] using h1
        have he : y i = x i := by
          simp [y,anchoredLocal_out _ i hi0 hi1,anchoredLocal_zero hd,
            anchoredLocal_one hd,anchoredLocal_two hd,h0,h1,h2]
        exact he ▸ hi
    · have h2z : x 2 = 0 := by by_contra h; exact h2 (bit_eq_one_of_ne_zero h)
      refine ⟨anchoredLocal x,anchored_local_reachable hd _,
        bitSupport_drop_zero x _ h0 ?_ ?_⟩
      · simp [anchoredLocal_zero hd,h2z]
      · intro i hi
        by_cases hi0 : i=0
        · simpa [hi0] using h0
        by_cases hi1 : i=1
        · simpa [hi1] using h1
        simpa [anchoredLocal_out _ i hi0 hi1,h0,h1,h2z] using hi
  · have h1z : x 1 = 0 := by by_contra h; exact h1 (bit_eq_one_of_ne_zero h)
    have h2 : x 2 = 1 := hne.resolve_left h1
    let y := anchoredLocal (anchoredLocal (anchoredLocal x))
    refine ⟨y,anchored_local_three_reachable hd _, bitSupport_drop_zero x y h0 ?_ ?_⟩
    · simp [y,anchoredLocal_zero hd,anchoredLocal_one hd,anchoredLocal_two hd,h1z,h2]
    · intro i hi
      by_cases hi0 : i=0
      · simpa [hi0] using h0
      by_cases hi1 : i=1
      · have hy1 : y 1 = 0 := by
          simp [y,anchoredLocal_zero hd,anchoredLocal_one hd,anchoredLocal_two hd,h0,h1z,h2]
        simp [hi1,hy1] at hi
      have he : y i = x i := by
        simp [y,anchoredLocal_out _ i hi0 hi1,anchoredLocal_zero hd,
          anchoredLocal_one hd,anchoredLocal_two hd,h0,h1z,h2]
      exact he ▸ hi

theorem anchored_pull_transitive (hd : 3 ≤ d) (x y : BitWord d) (hx : x ≠ 0) (hy : y ≠ 0) :
    wordReach (anchoredPullGroup d) x y :=
  local_moves_transitive hd (anchoredPullGroup d) anchoredPullGroup_fixes
    anchoredPullGroup_rotation (anchored_move hd) (anchored_merge hd) x y hx hy

theorem anchored_pair_zero_one_transitive (hd : 3 ≤ d) (x y : BitWord d)
    (hx : x ≠ 0) (hy : y ≠ 0) :
    wordReach (conjugatePairGroup (anchoredDifference (ZMod 2) d) 0 1) x y := by
  let L := anchoredDifference (ZMod 2) d
  have hL0 : L (0 : BitWord d) = 0 := anchoredDifference_zero
  have hx' : L.symm x ≠ 0 := by
    intro h
    apply hx
    exact (L.apply_symm_apply x).symm.trans ((congrArg L h).trans hL0)
  have hy' : L.symm y ≠ 0 := by
    intro h
    apply hy
    exact (L.apply_symm_apply y).symm.trans ((congrArg L h).trans hL0)
  obtain ⟨g,hg⟩ := anchored_pull_transitive hd (L.symm x) (L.symm y) hx' hy'
  refine ⟨⟨wordConjugation L g.val,g.property⟩,?_⟩
  change L (g.val (L.symm x)) = y
  rw [hg,L.apply_symm_apply]

omit [NeZero d] in
lemma conjugateWordRotation_add {S : Type*} (L : Equiv.Perm (ScalarWord d S))
    (c e : ZMod d) : conjugateWordRotation L (c+e) =
      wordConjugation (scalarRotation c) (conjugateWordRotation L e) := by
  change _ = scalarRotation c * conjugateWordRotation L e * (scalarRotation c)⁻¹
  rw [conjugateWordRotation_from_zero L (c+e),conjugateWordRotation_from_zero L e]
  simp only [scalarRotation_inv,neg_add_rev,← scalarRotation_mul]
  group

omit [NeZero d] in
lemma translated_pair_member {S : Type*} (L : Equiv.Perm (ScalarWord d S))
    (c : ZMod d) (g : conjugatePairGroup L 0 1) :
    wordConjugation (scalarRotation c) g.val ∈ conjugatePairGroup L c (c+1) := by
  have hle : conjugatePairGroup L 0 1 ≤
      (conjugatePairGroup L c (c+1)).comap (wordConjugation (scalarRotation c)) := by
    apply (Subgroup.closure_le _).mpr
    intro g hg
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
    change wordConjugation (scalarRotation c) g ∈ conjugatePairGroup L c (c+1)
    rcases hg with rfl | rfl
    · rw [← conjugateWordRotation_add,add_zero]
      exact Subgroup.subset_closure (by simp)
    · rw [← conjugateWordRotation_add]
      exact Subgroup.subset_closure (by simp)
  exact hle g.property

/-- The actual adjacent conjugate group is transitive on nonzero binary words. -/
theorem anchored_adjacent_pair_transitive (hd : 3 ≤ d) (c : ZMod d)
    (x y : BitWord d) (hx : x ≠ 0) (hy : y ≠ 0) :
    wordReach (conjugatePairGroup (anchoredDifference (ZMod 2) d) c (c+1)) x y := by
  let S := (scalarRotation c : Equiv.Perm (BitWord d))
  have hS0 : S (0 : BitWord d) = 0 := rfl
  have hx' : S.symm x ≠ 0 := by
    intro h
    apply hx
    exact (S.apply_symm_apply x).symm.trans ((congrArg S h).trans hS0)
  have hy' : S.symm y ≠ 0 := by
    intro h
    apply hy
    exact (S.apply_symm_apply y).symm.trans ((congrArg S h).trans hS0)
  obtain ⟨g,hg⟩ := anchored_pair_zero_one_transitive hd (S.symm x) (S.symm y) hx' hy'
  refine ⟨⟨wordConjugation S g.val,translated_pair_member _ c g⟩,?_⟩
  change S (g.val (S.symm x)) = y
  rw [hg,S.apply_symm_apply]

end SharedDecoders
