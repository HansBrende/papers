import SharedDecoders.CompositionTransvection

/-! # The literal single-site update and its local conjugate ratio -/

namespace SharedDecoders

open scoped CharTwo

variable {d : ℕ} [NeZero d]

def neighborUpdate (hd : 2 ≤ d) (i : ZMod d) : Equiv.Perm (BitWord d) :=
  binaryTransvection i (i+1) (by
    have h1 : (1 : ZMod d) ≠ 0 := by
      simpa using small_index_ne (d := d) 1 0 (by omega) (by omega) (by omega)
    simpa using h1)

def singleSite (hd : 2 ≤ d) : Equiv.Perm (BitWord d) := neighborUpdate hd 0

def singleLocal (hd : 2 ≤ d) : Equiv.Perm (BitWord d) :=
  neighborUpdate hd 1 * neighborUpdate hd 0 * neighborUpdate hd (-1) * neighborUpdate hd 0

omit [NeZero d] in
@[simp] lemma neighborUpdate_apply (hd : 2 ≤ d) (i : ZMod d) (x : BitWord d) (k : ZMod d) :
    neighborUpdate hd i x k = if k=i then x i+x (i+1) else x k := rfl

omit [NeZero d] in
@[simp] lemma neighborUpdate_inv (hd : 2 ≤ d) (i : ZMod d) :
    (neighborUpdate hd i)⁻¹ = neighborUpdate hd i := rfl

omit [NeZero d] in
@[simp] lemma singleSite_zero (hd : 2 ≤ d) : singleSite hd (0 : BitWord d) = 0 := by
  ext k
  simp [singleSite]

omit [NeZero d] in
lemma neighborUpdate_rotate (hd : 2 ≤ d) (s i : ZMod d) :
    wordConjugation (scalarRotation s) (neighborUpdate hd i) = neighborUpdate hd (i-s) := by
  dsimp [neighborUpdate]
  rw [binaryTransvection_rotate]
  congr 1
  ring

omit [NeZero d] in
lemma singleLocal_ratio (hd : 2 ≤ d) :
    singleLocal hd = (scalarRotation 1)⁻¹ * (singleSite hd)⁻¹ *
      conjugateWordRotation (singleSite hd) 1 * singleSite hd := by
  have h1 := neighborUpdate_rotate hd (-1) 0
  have hm := neighborUpdate_rotate hd 1 0
  change scalarRotation (-1) * neighborUpdate hd 0 * (scalarRotation (-1))⁻¹ = _ at h1
  change scalarRotation 1 * neighborUpdate hd 0 * (scalarRotation 1)⁻¹ = _ at hm
  simp only [scalarRotation_inv,neg_neg,zero_sub,neg_neg] at h1 hm
  rw [conjugateWordRotation_from_zero,conjugateWordRotation_zero]
  change neighborUpdate hd 1 * neighborUpdate hd 0 * neighborUpdate hd (-1) * neighborUpdate hd 0 = _
  simp only [singleSite,neighborUpdate_inv,scalarRotation_inv]
  rw [← h1,← hm]
  group

omit [NeZero d] in
lemma singleLocal_apply (hd : 4 ≤ d) (x : BitWord d) (i : ZMod d) :
    singleLocal (by omega : 2 ≤ d) x i =
      if i=1 then x 1+x 2 else if i=-1 then x (-1)+x 0+x 1 else x i := by
  have h10 : (1 : ZMod d) ≠ 0 := by simpa using small_index_ne (d := d) 1 0 (by omega) (by omega) (by omega)
  have h20 : (2 : ZMod d) ≠ 0 := by simpa using small_index_ne (d := d) 2 0 (by omega) (by omega) (by omega)
  have h21 : (2 : ZMod d) ≠ 1 := by simpa using small_index_ne (d := d) 2 1 (by omega) (by omega) (by omega)
  have h30 : (3 : ZMod d) ≠ 0 := by simpa using small_index_ne (d := d) 3 0 (by omega) (by omega) (by omega)
  have hn10 : (-1 : ZMod d) ≠ 0 := neg_ne_zero.mpr h10
  have hn11 : (-1 : ZMod d) ≠ 1 := by intro h; apply h20; linear_combination -h
  have h2n1 : (2 : ZMod d) ≠ -1 := by intro h; apply h30; linear_combination h
  by_cases hi1 : i=1
  · simp [singleLocal,Equiv.Perm.mul_apply,hi1,h10,Ne.symm hn11,h20,h2n1,
      one_add_one_eq_two]
  · by_cases him : i=-1
    · simp [singleLocal,Equiv.Perm.mul_apply,him,hn10,hn11]
      abel
    · by_cases hi0 : i=0
      · simp [singleLocal,Equiv.Perm.mul_apply,hi0,h10,Ne.symm h10,Ne.symm hn10,Ne.symm hn11]
      · simp [singleLocal,Equiv.Perm.mul_apply,hi0,hi1,him]

omit [NeZero d] in
lemma singleLocal_square (hd : 4 ≤ d) :
    singleLocal (by omega : 2 ≤ d) ^ 2 = binaryTransvection (-1) 2 (by
      have h3 : (3 : ZMod d) ≠ 0 := by
        simpa using small_index_ne (d := d) 3 0 (by omega) (by omega) (by omega)
      intro h; apply h3; linear_combination -h) := by
  have h10 : (1 : ZMod d) ≠ 0 := by simpa using small_index_ne (d := d) 1 0 (by omega) (by omega) (by omega)
  have h20 : (2 : ZMod d) ≠ 0 := by simpa using small_index_ne (d := d) 2 0 (by omega) (by omega) (by omega)
  have h21 : (2 : ZMod d) ≠ 1 := by simpa using small_index_ne (d := d) 2 1 (by omega) (by omega) (by omega)
  have h30 : (3 : ZMod d) ≠ 0 := by simpa using small_index_ne (d := d) 3 0 (by omega) (by omega) (by omega)
  have hn11 : (-1 : ZMod d) ≠ 1 := by intro h; apply h20; linear_combination -h
  have h2n1 : (2 : ZMod d) ≠ -1 := by intro h; apply h30; linear_combination h
  ext x i
  simp only [pow_two,Equiv.Perm.mul_apply,binaryTransvection_apply,singleLocal_apply hd]
  by_cases hi1 : i=1
  · simp [hi1,Ne.symm hn11,h21,h2n1]
  · by_cases him : i=-1
    · simp [him,hn11,Ne.symm h10,Ne.symm (neg_ne_zero.mpr h10)]
      abel_nf
      simp
    · simp [hi1,him]

omit [NeZero d] in
lemma singleLocal_step_four (hd : 5 ≤ d)
    (h03 : (0 : ZMod d) ≠ 3) (hm3 : (-1 : ZMod d) ≠ 3) :
    singleLocal (by omega : 2 ≤ d) * binaryTransvection 0 3 h03 *
      (singleLocal (by omega : 2 ≤ d))⁻¹ * (binaryTransvection 0 3 h03)⁻¹ =
        binaryTransvection (-1) 3 hm3 := by
  let A := singleLocal (by omega : 2 ≤ d)
  let E := binaryTransvection 0 3 h03
  let V := binaryTransvection (-1) 3 hm3
  have h10 : (1 : ZMod d) ≠ 0 := by simpa using small_index_ne (d := d) 1 0 (by omega) (by omega) (by omega)
  have h20 : (2 : ZMod d) ≠ 0 := by simpa using small_index_ne (d := d) 2 0 (by omega) (by omega) (by omega)
  have h21 : (2 : ZMod d) ≠ 1 := by simpa using small_index_ne (d := d) 2 1 (by omega) (by omega) (by omega)
  have h31 : (3 : ZMod d) ≠ 1 := by simpa using small_index_ne (d := d) 3 1 (by omega) (by omega) (by omega)
  have hn10 : (-1 : ZMod d) ≠ 0 := neg_ne_zero.mpr h10
  have hn11 : (-1 : ZMod d) ≠ 1 := by intro h; apply h20; linear_combination -h
  have he : A*E = V*E*A := by
    ext x i
    simp only [A,E,V,Equiv.Perm.mul_apply,binaryTransvection_apply,singleLocal_apply (by omega : 4 ≤ d)]
    by_cases hi1 : i=1
    · simp [hi1,h10,h20,Ne.symm hn11]
    · by_cases him : i=-1
      · simp [him,hn11,hn10,h10,h31,Ne.symm hm3,Ne.symm h03]
        abel
      · by_cases hi0 : i=0
        · simp [hi0,Ne.symm h10,Ne.symm hn10,h31,Ne.symm hm3]
        · simp [hi1,him,hi0]
  change A*E*A⁻¹*E⁻¹ = V
  rw [he]
  group

end SharedDecoders
