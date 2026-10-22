import TransposeFollowup.RecodedXor

/-! Counting free component-flip orbits through nonlinear row recodings.
The key invariant is pointwise preservation of far raw coordinates at every
basepoint. It therefore survives compositions of flips. -/

namespace TransposeFollowup

open Classical
set_option autoImplicit false
universe u

theorem disjoint_family_member_of_union {V : Type u} [DecidableEq V]
    (U : Finset (Finset V)) (hdis : (U : Set (Finset V)).PairwiseDisjoint id)
    {K : Finset (Finset V)} (hK : K ⊆ U) {S : Finset V} (hS : S ∈ U)
    {v : V} (hvS : v ∈ S) (hvK : v ∈ K.biUnion id) : S ∈ K := by
  obtain ⟨T, hT, hvT⟩ := Finset.mem_biUnion.mp hvK
  by_cases heq : S = T
  · exact heq.symm ▸ hT
  · exact False.elim (Finset.disjoint_left.mp (hdis hS (hK hT) heq) hvS hvT)

theorem disjoint_family_union_injective {V : Type u} [DecidableEq V]
    (U : Finset (Finset V)) (hne : ∀ S ∈ U, S.Nonempty)
    (hdis : (U : Set (Finset V)).PairwiseDisjoint id)
    {K K' : Finset (Finset V)} (hK : K ⊆ U) (hK' : K' ⊆ U)
    (heq : K.biUnion id = K'.biUnion id) : K = K' := by
  apply Finset.Subset.antisymm
  · intro S hS
    obtain ⟨v, hv⟩ := hne S (hK hS)
    apply disjoint_family_member_of_union U hdis hK' (hK hS) hv
    rw [← heq]
    exact Finset.mem_biUnion.mpr ⟨S, hS, hv⟩
  · intro S hS
    obtain ⟨v, hv⟩ := hne S (hK' hS)
    apply disjoint_family_member_of_union U hdis hK (hK' hS) hv
    rw [heq]
    exact Finset.mem_biUnion.mpr ⟨S, hS, hv⟩

theorem disjoint_family_disjoint_union {V : Type u} [DecidableEq V]
    (U : Finset (Finset V)) (hdis : (U : Set (Finset V)).PairwiseDisjoint id)
    {K : Finset (Finset V)} (hK : K ⊆ U) {S : Finset V}
    (hS : S ∈ U) (hSK : S ∉ K) : Disjoint S (K.biUnion id) := by
  apply (Finset.disjoint_biUnion_right S K id).mpr
  intro T hT
  exact hdis hS (hK hT) (fun he => hSK (he.symm ▸ hT))

namespace RecodedXorCode

variable {n b B : ℕ} (C : RecodedXorCode n b B)

/-- Preservation at all basepoints is essential: preservation only at the
original input would not justify this induction through nonlinear recodings. -/
theorem flip_union_preserves (U : Finset (Finset (MatrixBit n b)))
    (hdis : (U : Set (Finset (MatrixBit n b))).PairwiseDisjoint id)
    (Q : Finset (MatrixBit n b))
    (hfix : ∀ S ∈ U, ∀ x v, v ∉ Q → matrixBits (C.flip S x) v = matrixBits x v)
    (K : Finset (Finset (MatrixBit n b))) (hK : K ⊆ U)
    (x : FiniteMatrix n b) (v : MatrixBit n b) (hv : v ∉ Q) :
    matrixBits (C.flip (K.biUnion id) x) v = matrixBits x v := by
  induction K using Finset.induction_on with
  | empty => simp
  | @insert S K hSK ih =>
    have hS := hK (Finset.mem_insert_self S K)
    have hKU : K ⊆ U := fun T hT => hK (Finset.mem_insert_of_mem hT)
    rw [Finset.biUnion_insert, id_eq,
      C.flip_union S (K.biUnion id) (disjoint_family_disjoint_union U hdis hKU hS hSK)]
    rw [hfix S hS _ v hv]
    exact ih hKU

/-- A family of disjoint nonempty transformed-coordinate flips gives a free
2^|U| orbit. If all flips preserve the complement of Q in raw coordinates at
every basepoint, the orbit fits into Q and hence |U|<=|Q|. -/
theorem flip_orbit_bound (U : Finset (Finset (MatrixBit n b)))
    (hne : ∀ S ∈ U, S.Nonempty)
    (hdis : (U : Set (Finset (MatrixBit n b))).PairwiseDisjoint id)
    (Q : Finset (MatrixBit n b))
    (hfix : ∀ S ∈ U, ∀ x v, v ∉ Q → matrixBits (C.flip S x) v = matrixBits x v) :
    U.card ≤ Q.card := by
  let base : FiniteMatrix n b := fun _ _ _ => false
  let view : U.powerset → (Q → Bool) := fun K v =>
    matrixBits (C.flip (K.val.biUnion id) base) v.val
  have hinj : Function.Injective view := by
    intro K K' heq
    have hK : K.val ⊆ U := Finset.mem_powerset.mp K.property
    have hK' : K'.val ⊆ U := Finset.mem_powerset.mp K'.property
    have hbits : matrixBits (C.flip (K.val.biUnion id) base) =
        matrixBits (C.flip (K'.val.biUnion id) base) := by
      funext v
      by_cases hv : v ∈ Q
      · exact congrFun heq ⟨v, hv⟩
      · rw [C.flip_union_preserves U hdis Q hfix K.val hK base v hv,
          C.flip_union_preserves U hdis Q hfix K'.val hK' base v hv]
    have hraw := matrixBits_injective n b hbits
    have hunion := C.flip_set_injective base hraw
    exact Subtype.ext (disjoint_family_union_injective U hne hdis hK hK' hunion)
  have hcard := Fintype.card_le_of_injective view hinj
  simp only [Fintype.card_coe, Finset.card_powerset, Fintype.card_fun,
    Fintype.card_bool] at hcard
  exact (pow_le_pow_iff_right₀ (by decide : 1 < (2 : ℕ))).mp hcard

end RecodedXorCode
end TransposeFollowup
