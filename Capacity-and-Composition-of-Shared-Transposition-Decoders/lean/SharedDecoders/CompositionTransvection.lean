import SharedDecoders.CompositionAnchoredGroup

/-! # Literal binary transvections and cyclic generation -/

namespace SharedDecoders

open scoped CharTwo

variable {d : ℕ} [NeZero d]

def binaryTransvection (i j : ZMod d) (hij : i ≠ j) : Equiv.Perm (BitWord d) where
  toFun x k := if k=i then x i+x j else x k
  invFun x k := if k=i then x i+x j else x k
  left_inv x := by
    funext k
    by_cases hk : k=i <;> simp [hk,Ne.symm hij]
  right_inv x := by
    funext k
    by_cases hk : k=i <;> simp [hk,Ne.symm hij]

omit [NeZero d] in
@[simp] lemma binaryTransvection_apply (i j : ZMod d) (hij : i ≠ j)
    (x : BitWord d) (k : ZMod d) : binaryTransvection i j hij x k =
      if k=i then x i+x j else x k := rfl

omit [NeZero d] in
@[simp] lemma binaryTransvection_inv (i j : ZMod d) (hij : i ≠ j) :
    (binaryTransvection i j hij)⁻¹ = binaryTransvection i j hij := rfl

omit [NeZero d] in
@[simp] lemma binaryTransvection_zero (i j : ZMod d) (hij : i ≠ j) :
    binaryTransvection i j hij (0 : BitWord d) = 0 := by ext k; simp

omit [NeZero d] in
lemma binaryTransvection_congr {i j k l : ZMod d} (hij : i ≠ j) (hkl : k ≠ l)
    (hi : i=k) (hj : j=l) : binaryTransvection i j hij = binaryTransvection k l hkl := by
  subst k
  subst l
  rfl

omit [NeZero d] in
lemma binaryTransvection_commutator (i j k : ZMod d)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    binaryTransvection i j hij * binaryTransvection j k hjk *
      binaryTransvection i j hij * binaryTransvection j k hjk = binaryTransvection i k hik := by
  ext x l
  by_cases hli : l=i
  · simp [Equiv.Perm.mul_apply,hli,hij,Ne.symm hij,Ne.symm hjk,Ne.symm hik]
    abel_nf
    simp
  · by_cases hlj : l=j
    · simp [Equiv.Perm.mul_apply,hlj,Ne.symm hij,Ne.symm hjk,Ne.symm hik]
    · simp [Equiv.Perm.mul_apply,hli,hlj]

omit [NeZero d] in
lemma binaryTransvection_rotate (s i j : ZMod d) (hij : i ≠ j) :
    wordConjugation (scalarRotation s) (binaryTransvection i j hij) =
      binaryTransvection (i-s) (j-s) (sub_left_inj.not.mpr hij) := by
  ext x k
  change (if k+s=i then x (i-s)+x (j-s) else x (k+s-s)) = _
  simp only [binaryTransvection_apply,add_sub_cancel_right]
  simp only [show (k+s=i) ↔ k=i-s by exact eq_sub_iff_add_eq.symm]

omit [NeZero d] in
lemma transvection_chain_mem (G : Subgroup (Equiv.Perm (BitWord d)))
    (s : ZMod d) (hs : s ≠ 0)
    (hstep : ∀ i (h : i ≠ i+s), binaryTransvection i (i+s) h ∈ G)
    (n : ℕ) (i : ZMod d) (hn : (n : ZMod d)*s ≠ 0) :
    binaryTransvection i (i+(n : ZMod d)*s) (by simpa using hn) ∈ G := by
  induction n with
  | zero => simp at hn
  | succ n ih =>
    by_cases hz : (n : ZMod d)*s = 0
    · have he : ((n+1 : ℕ) : ZMod d)*s = s := by push_cast; rw [add_mul,hz]; simp
      have hi : i ≠ i+s := by simpa using hs
      rw [binaryTransvection_congr _ hi rfl (congrArg (i+·) he)]
      exact hstep i hi
    · have hij : i ≠ i+(n : ZMod d)*s := by simpa using hz
      have hjk : i+(n : ZMod d)*s ≠ i+((n+1 : ℕ) : ZMod d)*s := by
        intro h
        apply hs
        push_cast at h
        linear_combination -h
      have hik : i ≠ i+((n+1 : ℕ) : ZMod d)*s := by simpa using hn
      have h1 := ih hz
      have h2 := hstep (i+(n : ZMod d)*s) (by simpa using hs)
      have he : i+(n : ZMod d)*s+s = i+((n+1 : ℕ) : ZMod d)*s := by push_cast; ring
      have h2' := (binaryTransvection_congr _ hjk rfl he) ▸ h2
      rw [← binaryTransvection_commutator i _ _ hij hjk hik]
      exact G.mul_mem (G.mul_mem (G.mul_mem h1 h2') h1) h2'

lemma all_transvections_of_step_one (G : Subgroup (Equiv.Perm (BitWord d)))
    (hd : 2 ≤ d)
    (hstep : ∀ i (h : i ≠ i+1), binaryTransvection i (i+1) h ∈ G)
    (i j : ZMod d) (hij : i ≠ j) : binaryTransvection i j hij ∈ G := by
  have h1 : (1 : ZMod d) ≠ 0 := by
    simpa using small_index_ne (d := d) 1 0 (by omega) (by omega) (by omega)
  have hn : (((j-i).val : ℕ) : ZMod d)*1 ≠ 0 := by simpa using sub_ne_zero.mpr hij.symm
  have h := transvection_chain_mem G 1 h1 hstep (j-i).val i hn
  simpa using h

/-- A complete set of literal row additions clears a word to a single bit. -/
theorem all_transvections_transitive (G : Subgroup (Equiv.Perm (BitWord d)))
    (hzero : ∀ g : G, g.val 0 = 0)
    (hrot : ∀s, scalarRotation s ∈ G)
    (hall : ∀ i j (hij : i ≠ j), binaryTransvection i j hij ∈ G)
    (x y : BitWord d) (hx : x ≠ 0) (hy : y ≠ 0) : wordReach G x y := by
  classical
  have hun (z : BitWord d) (hz : z ≠ 0) : wordReach G z (Pi.single 0 1) := by
    let O : Set (BitWord d) := {w | wordReach G z w}
    obtain ⟨w,hw,hmin⟩ := Set.exists_min_image O (fun w => (bitSupport w).card)
      O.toFinite ⟨z,wordReach_refl G z⟩
    have hwn := wordReach_nonzero hzero hz hw
    obtain ⟨a,ha⟩ := bitSupport_nonempty hwn
    have hwa : w a=1 := (mem_bitSupport w a).mp ha
    have hc : (bitSupport w).card ≤ 1 := by
      by_contra hc
      obtain ⟨j,hj,hja⟩ := Finset.exists_mem_ne (by omega : 1 < (bitSupport w).card) a
      have hwj : w j=1 := (mem_bitSupport w j).mp hj
      let g := binaryTransvection j a hja
      have hgw : wordReach G w (g w) := ⟨⟨g,hall j a hja⟩,rfl⟩
      have hlt : (bitSupport (g w)).card < (bitSupport w).card := by
        apply Finset.card_lt_card
        refine Finset.ssubset_iff_subset_ne.mpr ⟨?_,?_⟩
        · intro i hi
          have hi' := (mem_bitSupport (g w) i).mp hi
          by_cases hij : i=j
          · simp [g,hij,hwa,hwj] at hi'
          · exact (mem_bitSupport w i).mpr (by simpa [g,hij] using hi')
        · intro he
          have hh : j ∈ bitSupport (g w) := he.symm ▸ hj
          have hh' := (mem_bitSupport (g w) j).mp hh
          simp [g,hwa,hwj] at hh'
      have hm := hmin (g w) (wordReach_trans hw hgw)
      omega
    have hwr : wordReach G w (scalarRotation a w) := ⟨⟨_,hrot a⟩,rfl⟩
    have hr0 : scalarRotation a w 0 = 1 := by simpa [scalarRotation] using hwa
    have hrc : (bitSupport (scalarRotation a w)).card ≤ 1 := by
      rw [bitSupport_rotation_card]; exact hc
    exact (bitSupport_unit_of_card_le_one _ hr0 hrc) ▸ (wordReach_trans hw hwr)
  exact wordReach_trans (hun x hx) (wordReach_symm (hun y hy))

end SharedDecoders
