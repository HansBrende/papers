import SharedDecoders.CompositionSingleSiteLocal

/-! # Concrete cyclic transvection generation for a single-site update -/

namespace SharedDecoders

variable {d : ℕ} [NeZero d]

def singlePullGroup (hd : 2 ≤ d) : Subgroup (Equiv.Perm (BitWord d)) :=
  (conjugatePairGroup (singleSite hd) 0 1).comap (wordConjugation (singleSite hd))

lemma singlePullGroup_rotation (hd : 2 ≤ d) (s : ZMod d) :
    scalarRotation s ∈ singlePullGroup hd := by
  have h : scalarRotation (1 : ZMod d) ∈ singlePullGroup hd := by
    change singleSite hd * scalarRotation 1 * (singleSite hd)⁻¹ ∈ conjugatePairGroup (singleSite hd) 0 1
    rw [← conjugateWordRotation_zero]
    exact Subgroup.subset_closure (by simp)
  have hp := (singlePullGroup hd).pow_mem h s.val
  simpa only [scalarRotation_pow,ZMod.natCast_zmod_val] using hp

omit [NeZero d] in
lemma singlePullGroup_local (hd : 2 ≤ d) : singleLocal hd ∈ singlePullGroup hd := by
  let L := singleSite hd
  have h0 : conjugateWordRotation L 0 ∈ conjugatePairGroup L 0 1 := Subgroup.subset_closure (by simp)
  have h1 : conjugateWordRotation L 1 ∈ conjugatePairGroup L 0 1 := Subgroup.subset_closure (by simp)
  change L * singleLocal hd * L⁻¹ ∈ conjugatePairGroup L 0 1
  have he : L * singleLocal hd * L⁻¹ = (conjugateWordRotation L 0)⁻¹ * conjugateWordRotation L 1 := by
    rw [singleLocal_ratio,conjugateWordRotation_zero]
    dsimp [L]
    group
  rw [he]
  exact (conjugatePairGroup L 0 1).mul_mem ((conjugatePairGroup L 0 1).inv_mem h0) h1

omit [NeZero d] in
lemma singlePullGroup_fixes (hd : 2 ≤ d) (g : singlePullGroup hd) : g.val 0=0 := by
  have hh : wordConjugation (singleSite hd) g.val ∈ conjugatePairGroup (singleSite hd) 0 1 := g.property
  have hz := conjugatePairGroup_fixes (singleSite hd) 0 (singleSite_zero hd) 0 1 ⟨_,hh⟩
  have hL0 : singleSite hd (0 : BitWord d)=0 := singleSite_zero hd
  have hLi : (singleSite hd)⁻¹ (0 : BitWord d)=0 := by
    change (singleSite hd).symm 0=0
    apply (singleSite hd).injective
    rw [Equiv.apply_symm_apply,hL0]
  change singleSite hd (g.val ((singleSite hd)⁻¹ 0))=0 at hz
  rw [hLi] at hz
  exact (singleSite hd).injective (hz.trans hL0.symm)

omit [NeZero d] in
lemma translated_transvection_mem (G : Subgroup (Equiv.Perm (BitWord d)))
    (hrot : ∀s, scalarRotation s ∈ G) (i j : ZMod d) (hij : i ≠ j)
    (hmem : binaryTransvection i j hij ∈ G) (k : ZMod d) (hk : k ≠ k+(j-i)) :
    binaryTransvection k (k+(j-i)) hk ∈ G := by
  have ht : wordConjugation (scalarRotation (i-k)) (binaryTransvection i j hij) ∈ G :=
    G.mul_mem (G.mul_mem (hrot _) hmem) (G.inv_mem (hrot _))
  rw [binaryTransvection_rotate] at ht
  exact (binaryTransvection_congr (i := i-(i-k)) (j := j-(i-k)) _ hk (by ring) (by ring)) ▸ ht

lemma single_step_three (hd : 4 ≤ d) (i : ZMod d) (hi : i ≠ i+3) :
    binaryTransvection i (i+3) hi ∈ singlePullGroup (by omega : 2 ≤ d) := by
  have hs := (singlePullGroup (by omega : 2 ≤ d)).pow_mem (singlePullGroup_local _) 2
  rw [singleLocal_square hd] at hs
  have h := translated_transvection_mem _ (singlePullGroup_rotation _) (-1) 2 _ hs i
  have he : (2 : ZMod d)-(-1)=3 := by ring
  have hi' : i ≠ i+(2-(-1)) := by simpa only [he] using hi
  exact (binaryTransvection_congr (i := i) (j := i+(2-(-1))) _ hi rfl (by rw [he])) ▸ h hi'

lemma single_step_four (hd : 5 ≤ d) (i : ZMod d) (hi : i ≠ i+4) :
    binaryTransvection i (i+4) hi ∈ singlePullGroup (by omega : 2 ≤ d) := by
  let G := singlePullGroup (by omega : 2 ≤ d)
  have h03 : (0 : ZMod d) ≠ 3 := by simpa using small_index_ne (d := d) 0 3 (by omega) (by omega) (by omega)
  have hm3 : (-1 : ZMod d) ≠ 3 := by
    have h4 : (4 : ZMod d) ≠ 0 := by simpa using small_index_ne (d := d) 4 0 (by omega) (by omega) (by omega)
    intro h; apply h4; linear_combination -h
  have hE : binaryTransvection 0 3 h03 ∈ G := by
    have hh : (0 : ZMod d) ≠ 0+3 := by simpa only [zero_add] using h03
    simpa only [zero_add] using single_step_three (d := d) (by omega) 0 hh
  have hA : singleLocal (by omega : 2 ≤ d) ∈ G := singlePullGroup_local _
  have hV := G.mul_mem (G.mul_mem (G.mul_mem hA hE) (G.inv_mem hA)) (G.inv_mem hE)
  rw [singleLocal_step_four hd h03 hm3] at hV
  have h := translated_transvection_mem G (singlePullGroup_rotation _) (-1) 3 hm3 hV i
  have he : (3 : ZMod d)-(-1)=4 := by ring
  have hi' : i ≠ i+(3-(-1)) := by simpa only [he] using hi
  exact (binaryTransvection_congr (i := i) (j := i+(3-(-1))) _ hi rfl (by rw [he])) ▸ h hi'

lemma single_step_neg_three (hd : 4 ≤ d) (i : ZMod d) (hi : i ≠ i-3) :
    binaryTransvection i (i-3) hi ∈ singlePullGroup (by omega : 2 ≤ d) := by
  have h3 : (3 : ZMod d) ≠ 0 := by simpa using small_index_ne (d := d) 3 0 (by omega) (by omega) (by omega)
  have hn : ((d-1 : ℕ) : ZMod d) = -1 := by
    have h := congrArg (fun n : ℕ => (n : ZMod d)) (Nat.sub_add_cancel (show 1≤d by omega))
    push_cast at h
    simp only [ZMod.natCast_self] at h
    linear_combination h
  have hns : (((d-1 : ℕ) : ZMod d)*3) ≠ 0 := by rw [hn]; simpa using h3
  have h := transvection_chain_mem (singlePullGroup (by omega : 2 ≤ d)) 3 h3
    (single_step_three hd) (d-1) i hns
  exact (binaryTransvection_congr (i := i) (j := i+((d-1 : ℕ) : ZMod d)*3) _ hi rfl (by rw [hn]; ring)) ▸ h

lemma single_all_transvections (hd : 4 ≤ d) (i j : ZMod d) (hij : i ≠ j) :
    binaryTransvection i j hij ∈ singlePullGroup (by omega : 2 ≤ d) := by
  apply all_transvections_of_step_one _ (by omega) ?_ i j hij
  intro a ha
  by_cases hd4 : d=4
  · subst d
    have he : a-3=a+1 := by
      have hh : (-3 : ZMod 4)=1 := by decide
      rw [sub_eq_add_neg,hh]
    have h := single_step_neg_three hd a (by simpa only [he] using ha)
    exact (binaryTransvection_congr (i := a) (j := a-3) _ ha rfl he) ▸ h
  · have hd5 : 5≤d := by omega
    have h4 : (4 : ZMod d) ≠ 0 := by simpa using small_index_ne (d := d) 4 0 (by omega) (by omega) (by omega)
    have h3 : (3 : ZMod d) ≠ 0 := by simpa using small_index_ne (d := d) 3 0 (by omega) (by omega) (by omega)
    have hab : a ≠ a+4 := by simpa using h4
    have hbc : a+4 ≠ a+1 := by intro h; apply h3; linear_combination h
    have h1 := single_step_four hd5 a hab
    have h2 := single_step_neg_three hd (a+4) (by
      have hh : a+4-3=a+1 := by ring
      simpa only [hh] using hbc)
    have h2' : binaryTransvection (a+4) (a+1) hbc ∈ singlePullGroup (by omega : 2 ≤ d) :=
      (binaryTransvection_congr (i := a+4) (j := a+4-3) _ hbc rfl (by ring)) ▸ h2
    rw [← binaryTransvection_commutator a (a+4) (a+1) hab hbc ha]
    exact (singlePullGroup (by omega : 2 ≤ d)).mul_mem
      ((singlePullGroup (by omega : 2 ≤ d)).mul_mem
        ((singlePullGroup (by omega : 2 ≤ d)).mul_mem h1 h2') h1) h2'

theorem single_pull_transitive_ge_four (hd : 4 ≤ d) (x y : BitWord d) (hx : x ≠ 0) (hy : y ≠ 0) :
    wordReach (singlePullGroup (by omega : 2 ≤ d)) x y :=
  all_transvections_transitive _ (singlePullGroup_fixes _) (singlePullGroup_rotation _)
    (single_all_transvections hd) x y hx hy

/-- The only coincident-index case is a kernel-checked eight-word calculation.
The displayed orbit contains units, the all-one word and all weight-two words. -/
theorem single_three_orbit : ∀ x : BitWord 3, x ≠ 0 →
    ∃ n k : Fin 3, scalarRotation (n.val : ZMod 3)
      (((singleLocal (by decide : 2 ≤ 3))^k.val) (Pi.single 0 1)) = x := by
  decide +kernel

theorem single_pull_transitive_three (x y : BitWord 3) (hx : x ≠ 0) (hy : y ≠ 0) :
    wordReach (singlePullGroup (by decide : 2 ≤ 3)) x y := by
  have hu (z : BitWord 3) (hz : z ≠ 0) :
      wordReach (singlePullGroup (by decide : 2 ≤ 3)) (Pi.single 0 1) z := by
    obtain ⟨n,k,h⟩ := single_three_orbit z hz
    refine ⟨⟨scalarRotation (n.val : ZMod 3) * (singleLocal (by decide : 2 ≤ 3))^k.val,
      (singlePullGroup (by decide : 2 ≤ 3)).mul_mem (singlePullGroup_rotation _ _)
        ((singlePullGroup (by decide : 2 ≤ 3)).pow_mem (singlePullGroup_local _) _)⟩,h⟩
  exact wordReach_trans (wordReach_symm (hu x hx)) (hu y hy)

theorem single_pull_transitive (hd : 3 ≤ d) (x y : BitWord d) (hx : x ≠ 0) (hy : y ≠ 0) :
    wordReach (singlePullGroup (by omega : 2 ≤ d)) x y := by
  by_cases he : d=3
  · subst d
    exact single_pull_transitive_three x y hx hy
  · exact single_pull_transitive_ge_four (by omega) x y hx hy

theorem single_pair_zero_one_transitive (hd : 3 ≤ d) (x y : BitWord d)
    (hx : x ≠ 0) (hy : y ≠ 0) :
    wordReach (conjugatePairGroup (singleSite (by omega : 2 ≤ d)) 0 1) x y := by
  let L := singleSite (by omega : 2 ≤ d)
  have hL0 : L (0 : BitWord d)=0 := singleSite_zero _
  have hx' : L.symm x ≠ 0 := by
    intro h
    exact hx ((L.apply_symm_apply x).symm.trans ((congrArg L h).trans hL0))
  have hy' : L.symm y ≠ 0 := by
    intro h
    exact hy ((L.apply_symm_apply y).symm.trans ((congrArg L h).trans hL0))
  obtain ⟨g,hg⟩ := single_pull_transitive hd (L.symm x) (L.symm y) hx' hy'
  refine ⟨⟨wordConjugation L g.val,g.property⟩,?_⟩
  change L (g.val (L.symm x)) = y
  rw [hg,L.apply_symm_apply]

theorem single_adjacent_pair_transitive (hd : 3 ≤ d) (c : ZMod d)
    (x y : BitWord d) (hx : x ≠ 0) (hy : y ≠ 0) :
    wordReach (conjugatePairGroup (singleSite (by omega : 2 ≤ d)) c (c+1)) x y := by
  let S := (scalarRotation c : Equiv.Perm (BitWord d))
  have hS0 : S (0 : BitWord d)=0 := rfl
  have hx' : S.symm x ≠ 0 := by
    intro h
    exact hx ((S.apply_symm_apply x).symm.trans ((congrArg S h).trans hS0))
  have hy' : S.symm y ≠ 0 := by
    intro h
    exact hy ((S.apply_symm_apply y).symm.trans ((congrArg S h).trans hS0))
  obtain ⟨g,hg⟩ := single_pair_zero_one_transitive hd (S.symm x) (S.symm y) hx' hy'
  refine ⟨⟨wordConjugation S g.val,translated_pair_member _ c g⟩,?_⟩
  change S (g.val (S.symm x)) = y
  rw [hg,S.apply_symm_apply]

end SharedDecoders
