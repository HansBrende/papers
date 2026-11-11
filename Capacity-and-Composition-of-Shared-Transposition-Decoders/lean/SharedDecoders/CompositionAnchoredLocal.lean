import SharedDecoders.CompositionLocalDescent

/-! # Literal local moves of the anchored conjugated shift -/

namespace SharedDecoders

open scoped CharTwo

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
lemma small_index_ne (a b : ℕ) (ha : a < d) (hb : b < d) (hab : a ≠ b) :
    (a : ZMod d) ≠ (b : ZMod d) := by
  intro h
  have hv := congrArg ZMod.val h
  rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hv
  exact hab hv

lemma anchored_sum (x : BitWord d) :
    ∑ i, anchoredDifference (ZMod 2) d x i = x 1 := by
  have he (i : ZMod d) : anchoredDifference (ZMod 2) d x i =
      x i + x (i+1) + if i=0 then x 1 else 0 := by
    by_cases hi : i=0
    · simp [hi]
    · simp [hi]
  simp_rw [he]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hs : ∑ i : ZMod d, x (i+1) = ∑ i : ZMod d, x i :=
    Equiv.sum_comp (Equiv.addRight (1 : ZMod d)) x
  rw [hs, CharTwo.add_self_eq_zero]
  simp

lemma anchored_Q_apply (x : BitWord d) (i : ZMod d) :
    conjugateWordRotation (anchoredDifference (ZMod 2) d) 0 x i =
      if i=0 then ∑ j, x j else if i=-1 then (∑ j,x j)+x 0 else x (i+1) := by
  obtain ⟨y,rfl⟩ := (anchoredDifference (ZMod 2) d).surjective x
  have he : conjugateWordRotation (anchoredDifference (ZMod 2) d) 0
      (anchoredDifference (ZMod 2) d y) =
        anchoredDifference (ZMod 2) d (scalarRotation 1 y) := by
    simp only [conjugateWordRotation, neg_zero, Equiv.Perm.mul_apply]
    have h0 (z : BitWord d) : scalarRotation 0 z = z := by funext j; simp [scalarRotation]
    rw [h0, h0]
    change anchoredDifference (ZMod 2) d (scalarRotation 1
      ((anchoredDifference (ZMod 2) d).symm (anchoredDifference (ZMod 2) d y))) = _
    rw [Equiv.symm_apply_apply]
  rw [he, anchored_sum]
  by_cases hi : i=0
  · simp [hi, scalarRotation]
  · by_cases hj : i=-1
    · simp [hj, scalarRotation, add_comm]
    · have hp : i+1 ≠ 0 := by intro h; apply hj; linear_combination h
      simp [hi, hj, hp, scalarRotation]

/-- The conjugate ratio acts on three coordinates and one common tail bit. -/
def anchoredLocal (x : BitWord d) : BitWord d := fun i =>
  x i + (x 0+x 1+x 2) + (if i=0 then x 1 else 0) +
    (if i=1 then x 0+x 1 else 0)

omit [NeZero d] in
lemma anchoredLocal_zero (hd : 3 ≤ d) (x : BitWord d) : anchoredLocal x 0 = x 2 := by
  have h : (0 : ZMod d) ≠ 1 := by simpa using small_index_ne (d := d) 0 1 (by omega) (by omega) (by omega)
  simp only [anchoredLocal, h, ite_false, ite_true, add_zero]
  abel_nf
  simp

omit [NeZero d] in
lemma anchoredLocal_one (hd : 3 ≤ d) (x : BitWord d) : anchoredLocal x 1 = x 1+x 2 := by
  have h : (1 : ZMod d) ≠ 0 := by simpa using small_index_ne (d := d) 1 0 (by omega) (by omega) (by omega)
  simp only [anchoredLocal, h, ite_false, ite_true, add_zero]
  abel_nf
  simp

omit [NeZero d] in
lemma anchoredLocal_two (hd : 3 ≤ d) (x : BitWord d) : anchoredLocal x 2 = x 0+x 1 := by
  have h0 : (2 : ZMod d) ≠ 0 := by simpa using small_index_ne (d := d) 2 0 (by omega) (by omega) (by omega)
  have h1 : (2 : ZMod d) ≠ 1 := by simpa using small_index_ne (d := d) 2 1 (by omega) (by omega) (by omega)
  simp only [anchoredLocal, h0, h1, ite_false, add_zero]
  abel_nf
  simp

omit [NeZero d] in
lemma anchoredLocal_out (x : BitWord d) (i : ZMod d) (h0 : i ≠ 0) (h1 : i ≠ 1) :
    anchoredLocal x i = x i+(x 0+x 1+x 2) := by
  simp [anchoredLocal,h0,h1]

lemma anchoredLocal_relation (hd : 3 ≤ d) (x : BitWord d) :
    anchoredDifference (ZMod 2) d (scalarRotation 1 (anchoredLocal x)) =
      scalarRotation 1 (conjugateWordRotation (anchoredDifference (ZMod 2) d) 0
        (scalarRotation (-1) (anchoredDifference (ZMod 2) d x))) := by
  have h10 : (1 : ZMod d) ≠ 0 := by simpa using small_index_ne (d := d) 1 0 (by omega) (by omega) (by omega)
  have h20 : (2 : ZMod d) ≠ 0 := by simpa using small_index_ne (d := d) 2 0 (by omega) (by omega) (by omega)
  have hn10 : (-1 : ZMod d) ≠ 0 := neg_ne_zero.mpr h10
  have hn11 : (-1 : ZMod d) ≠ 1 := by intro h; apply h20; linear_combination -h
  have h1n1 : (1 : ZMod d) ≠ -1 := Ne.symm hn11
  have hs : ∑j : ZMod d, scalarRotation (-1) (anchoredDifference (ZMod 2) d x) j = x 1 := by
    calc
      _ = ∑j, anchoredDifference (ZMod 2) d x j :=
        Equiv.sum_comp (Equiv.addRight (-1 : ZMod d)) _
      _ = x 1 := anchored_sum x
  funext i
  change (if i=0 then anchoredLocal x (0+1) else anchoredLocal x (i+1)+anchoredLocal x (i+1+1)) =
    conjugateWordRotation (anchoredDifference (ZMod 2) d) 0
      (scalarRotation (-1) (anchoredDifference (ZMod 2) d x)) (i+1)
  simp only [zero_add]
  rw [anchored_Q_apply, hs]
  by_cases hi0 : i=0
  · subst i
    have he : (2 : ZMod d)+(-1) = 1 := by ring
    simp [anchoredLocal_one hd, h10, h1n1, scalarRotation, one_add_one_eq_two, he]
  · simp only [hi0, ite_false]
    by_cases hi1 : i=-1
    · subst i
      simp [anchoredLocal_zero hd, anchoredLocal_one hd]
      abel_nf
      simp
    · by_cases hi2 : i=-2
      · subst i
        have he : (-2 : ZMod d)+1 = -1 := by ring
        simp only [he, hn10, ite_false, ite_true, scalarRotation]
        have he2 : (-1 : ZMod d)+1 = 0 := by ring
        rw [he2, anchoredLocal_zero hd, anchoredLocal_out x (-1) hn10 hn11]
        simp [anchoredDifference_apply, hn10]
        abel_nf
        simp
      · have h10' : i+1 ≠ 0 := by intro h; apply hi1; linear_combination h
        have h11' : i+1 ≠ 1 := by intro h; apply hi0; linear_combination h
        have h1n1' : i+1 ≠ -1 := by intro h; apply hi2; linear_combination h
        have h20' : i+1+1 ≠ 0 := by intro h; apply hi2; linear_combination h
        have h21' : i+1+1 ≠ 1 := by intro h; apply hi1; linear_combination h
        simp only [h10', h1n1', ite_false, scalarRotation]
        rw [anchoredLocal_out x _ h10' h11', anchoredLocal_out x _ h20' h21']
        have he : i+1+1+(-1) = i+1 := by ring
        try simp only [he, anchoredDifference_apply, h10', ite_false]
        abel_nf
        have he' : (-1 : ZMod d)+(i+2) = i+1 := by ring
        simp [he',h10',add_assoc,one_add_one_eq_two]

omit [NeZero d] in
@[simp] lemma scalarRotation_zero_eq {S : Type*} :
    (scalarRotation (0 : ZMod d) : Equiv.Perm (ScalarWord d S)) = 1 := by
  ext x i
  simp [scalarRotation]

omit [NeZero d] in
lemma scalarRotation_mul {S : Type*} (s t : ZMod d) :
    (scalarRotation s : Equiv.Perm (ScalarWord d S)) * scalarRotation t = scalarRotation (s+t) := by
  ext x i
  simp [scalarRotation, Equiv.Perm.mul_apply, add_comm, add_left_comm]

omit [NeZero d] in
@[simp] lemma scalarRotation_inv {S : Type*} (s : ZMod d) :
    (scalarRotation s : Equiv.Perm (ScalarWord d S))⁻¹ = scalarRotation (-s) := by
  apply inv_eq_of_mul_eq_one_right
  rw [scalarRotation_mul, add_neg_cancel, scalarRotation_zero_eq]

omit [NeZero d] in
lemma scalarRotation_pow {S : Type*} (n : ℕ) :
    (scalarRotation (1 : ZMod d) : Equiv.Perm (ScalarWord d S))^n = scalarRotation n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, scalarRotation_mul]; simp

omit [NeZero d] in
lemma conjugateWordRotation_zero {S : Type*} (L : Equiv.Perm (ScalarWord d S)) :
    conjugateWordRotation L 0 = L * scalarRotation 1 * L⁻¹ := by
  simp [conjugateWordRotation]

omit [NeZero d] in
lemma conjugateWordRotation_from_zero {S : Type*}
    (L : Equiv.Perm (ScalarWord d S)) (c : ZMod d) :
    conjugateWordRotation L c =
      scalarRotation c * conjugateWordRotation L 0 * scalarRotation (-c) := by
  rw [conjugateWordRotation_zero]
  simp only [conjugateWordRotation]
  group

noncomputable def anchoredLocalPerm (d : ℕ) [NeZero d] : Equiv.Perm (BitWord d) :=
  (scalarRotation 1)⁻¹ * (anchoredDifference (ZMod 2) d)⁻¹ *
    conjugateWordRotation (anchoredDifference (ZMod 2) d) 1 * anchoredDifference (ZMod 2) d

lemma anchoredLocalPerm_apply (hd : 3 ≤ d) (x : BitWord d) :
    anchoredLocalPerm d x = anchoredLocal x := by
  apply (scalarRotation (1 : ZMod d)).injective
  apply (anchoredDifference (ZMod 2) d).injective
  -- Cancel in the actual word permutation, then use the coordinate identity.
  have he : anchoredDifference (ZMod 2) d * scalarRotation 1 * anchoredLocalPerm d =
      conjugateWordRotation (anchoredDifference (ZMod 2) d) 1 * anchoredDifference (ZMod 2) d := by
    unfold anchoredLocalPerm
    group
  have h := congrArg (fun g : Equiv.Perm (BitWord d) => g x) he
  change anchoredDifference (ZMod 2) d (scalarRotation 1 (anchoredLocalPerm d x)) = _ at h
  have hr := anchoredLocal_relation hd x
  rw [conjugateWordRotation_from_zero] at h
  exact h.trans hr.symm

end SharedDecoders
