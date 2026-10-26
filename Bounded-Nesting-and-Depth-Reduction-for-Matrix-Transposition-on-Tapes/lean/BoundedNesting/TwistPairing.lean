import Mathlib

/-!
# The twist-pairing recursion for binary lifts (the equivariant crux, part (c))

Let `M` be a square matrix over a field `F` of characteristic `2`, indexed by the vertices `V` of
a graph, and let `tw` mark the twisted pairs of a double cover. The lift of `M` (`lift2`) acts on
`V × Bool`: an entry on an untwisted pair connects equal sheets, an entry on a twisted pair connects
opposite sheets. The twisted entries form `twistPart M tw`.

`finrank_ker_lift2`: `dim ker (lift2 M tw) = 2 dim ker M - r`, where `r` is the rank of the twist
pairing `ker Mᵀ × ker M → F`, `(y, x) ↦ yᵀ M^tw x` (`twistPairing`). Hence the excess
`dim ker - N/2` satisfies `e' = 2e - r` (`excess_lift2`) and the rate does not increase
(`rate_lift2_le`).

The proof changes coordinates to `a = x₀ + x₁`, `b = x₁`, in which the lift becomes the map
`(a, b) ↦ (M a, M b + M^tw a)`: in characteristic `2` the group algebra of `ℤ/2` is `F[t]/(t²)`
and the lift is `M + t M^tw`. The admissible `a` are those with `M^tw a ∈ range M`, which by the
Fredholm alternative for matrices (`mem_range_iff_dotProduct_ker_transpose`) is the kernel of the
twist pairing on `ker M`.
-/

namespace BoundedNesting

open Module Matrix

variable {V F : Type*} [Fintype V] [DecidableEq V] [Field F]

/-! ### The Fredholm alternative for matrices -/

/-- The dot-product pairing of vectors with the elements of a subspace. -/
def dotDual (W : Submodule F (V → F)) : (V → F) →ₗ[F] Module.Dual F W where
  toFun z :=
    { toFun := fun y => (y : V → F) ⬝ᵥ z
      map_add' := fun y y' => by simp [add_dotProduct]
      map_smul' := fun c y => by simp [smul_dotProduct] }
  map_add' z z' := by ext y; simp [dotProduct_add]
  map_smul' c z := by ext y; simp [dotProduct_smul]

omit [DecidableEq V] in
theorem dotDual_apply (W : Submodule F (V → F)) (z : V → F) (y : W) :
    dotDual W z y = (y : V → F) ⬝ᵥ z := rfl

theorem dotDual_surjective (W : Submodule F (V → F)) : Function.Surjective (dotDual W) := by
  intro f
  obtain ⟨g, hg⟩ := LinearMap.exists_extend f
  refine ⟨fun i => g (fun j => if i = j then 1 else 0), ?_⟩
  ext y
  rw [dotDual_apply, ← hg, LinearMap.comp_apply, Submodule.subtype_apply,
    LinearMap.pi_apply_eq_sum_univ g (y : V → F)]
  simp [dotProduct, smul_eq_mul]

/-- **Fredholm alternative.** A vector lies in the range of `M` if and only if it is orthogonal to
the kernel of `Mᵀ`. -/
theorem mem_range_iff_dotProduct_ker_transpose (M : Matrix V V F) (z : V → F) :
    z ∈ LinearMap.range M.mulVecLin ↔ ∀ y, Mᵀ *ᵥ y = 0 → y ⬝ᵥ z = 0 := by
  constructor
  · rintro ⟨w, rfl⟩ y hy
    rw [Matrix.mulVecLin_apply, dotProduct_mulVec, ← Matrix.mulVec_transpose, hy, zero_dotProduct]
  · intro hz
    have hmemW : ∀ x, x ∈ LinearMap.ker (dotDual (LinearMap.ker Mᵀ.mulVecLin)) ↔
        ∀ y, Mᵀ *ᵥ y = 0 → y ⬝ᵥ x = 0 := by
      intro x
      constructor
      · intro hx y hy
        have := congrArg (fun φ => φ ⟨y, LinearMap.mem_ker.mpr hy⟩) (LinearMap.mem_ker.mp hx)
        simpa [dotDual_apply] using this
      · intro hx
        refine LinearMap.mem_ker.mpr (LinearMap.ext fun y => ?_)
        rw [dotDual_apply, LinearMap.zero_apply]
        exact hx y (LinearMap.mem_ker.mp y.2)
    have hle : LinearMap.range M.mulVecLin ≤ LinearMap.ker (dotDual (LinearMap.ker Mᵀ.mulVecLin)) := by
      rintro x ⟨w, rfl⟩
      refine (hmemW _).mpr fun y hy => ?_
      rw [Matrix.mulVecLin_apply, dotProduct_mulVec, ← Matrix.mulVec_transpose, hy,
        zero_dotProduct]
    have h1 := LinearMap.finrank_range_add_finrank_ker (dotDual (LinearMap.ker Mᵀ.mulVecLin))
    rw [LinearMap.range_eq_top.mpr (dotDual_surjective _), finrank_top,
      Subspace.dual_finrank_eq, Module.finrank_fintype_fun_eq_card] at h1
    have h2 := LinearMap.finrank_range_add_finrank_ker Mᵀ.mulVecLin
    rw [Module.finrank_fintype_fun_eq_card] at h2
    have h3 : finrank F (LinearMap.range Mᵀ.mulVecLin) = finrank F (LinearMap.range M.mulVecLin) :=
      Matrix.rank_transpose M
    have hdim : finrank F (LinearMap.range M.mulVecLin) =
        finrank F (LinearMap.ker (dotDual (LinearMap.ker Mᵀ.mulVecLin))) := by
      omega
    rw [Submodule.eq_of_le_of_finrank_eq hle hdim]
    exact (hmemW z).mpr hz

/-! ### Lifts along a double cover -/

/-- The entries of `M` on the twisted pairs. -/
def twistPart (M : Matrix V V F) (tw : V → V → Prop) [DecidableRel tw] : Matrix V V F :=
  Matrix.of fun u v => if tw u v then M u v else 0

/-- The lift of `M` to the double cover with vertex set `V × Bool` in which the pairs `tw` are
twisted: untwisted entries connect equal sheets, twisted entries connect opposite sheets. -/
def lift2 (M : Matrix V V F) (tw : V → V → Prop) [DecidableRel tw] :
    Matrix (V × Bool) (V × Bool) F :=
  Matrix.of fun x y => if tw x.1 y.1 then (if x.2 = y.2 then 0 else M x.1 y.1)
    else (if x.2 = y.2 then M x.1 y.1 else 0)

/-- **The twist pairing** `ker Mᵀ × ker M → F`, `(y, x) ↦ yᵀ M^tw x`, as a map from `ker M` to the
dual of `ker Mᵀ`. -/
def twistPairing (M : Matrix V V F) (tw : V → V → Prop) [DecidableRel tw] :
    LinearMap.ker M.mulVecLin →ₗ[F] Module.Dual F (LinearMap.ker Mᵀ.mulVecLin) :=
  (dotDual (LinearMap.ker Mᵀ.mulVecLin)).comp
    ((twistPart M tw).mulVecLin.comp (LinearMap.ker M.mulVecLin).subtype)

omit [DecidableEq V] in
theorem twistPairing_apply (M : Matrix V V F) (tw : V → V → Prop) [DecidableRel tw]
    (x : LinearMap.ker M.mulVecLin) (y : LinearMap.ker Mᵀ.mulVecLin) :
    twistPairing M tw x y = (y : V → F) ⬝ᵥ (twistPart M tw *ᵥ (x : V → F)) := rfl

/-- The block map `(a, b) ↦ (M a, M b + M^tw a)`. -/
def blockMap (M : Matrix V V F) (tw : V → V → Prop) [DecidableRel tw] :
    ((V → F) × (V → F)) →ₗ[F] ((V → F) × (V → F)) :=
  LinearMap.prod (M.mulVecLin.comp (LinearMap.fst F _ _))
    (M.mulVecLin.comp (LinearMap.snd F _ _) + (twistPart M tw).mulVecLin.comp (LinearMap.fst F _ _))

omit [DecidableEq V] in
theorem blockMap_apply (M : Matrix V V F) (tw : V → V → Prop) [DecidableRel tw]
    (p : (V → F) × (V → F)) :
    blockMap M tw p = (M *ᵥ p.1, M *ᵥ p.2 + twistPart M tw *ᵥ p.1) := rfl

/-- The change of coordinates `x ↦ (x₀ + x₁, x₁)`. -/
def sheetEquiv : (V × Bool → F) ≃ₗ[F] (V → F) × (V → F) where
  toFun x := (fun v => x (v, false) + x (v, true), fun v => x (v, true))
  invFun p := fun x => if x.2 then p.2 x.1 else p.1 x.1 - p.2 x.1
  left_inv x := by
    funext ⟨v, i⟩
    cases i <;> simp
  right_inv p := by
    ext v <;> simp
  map_add' x y := by
    refine Prod.ext ?_ ?_
    · funext v
      simp only [Pi.add_apply, Prod.fst_add]
      ring
    · funext v
      simp only [Pi.add_apply, Prod.snd_add]
  map_smul' c x := by
    refine Prod.ext ?_ ?_
    · funext v
      simp only [Pi.smul_apply, smul_eq_mul, Prod.smul_fst, RingHom.id_apply]
      ring
    · funext v
      simp only [Pi.smul_apply, smul_eq_mul, Prod.smul_snd, RingHom.id_apply]

omit [Fintype V] [DecidableEq V] in
theorem sheetEquiv_apply (x : V × Bool → F) :
    sheetEquiv x = (fun v => x (v, false) + x (v, true), fun v => x (v, true)) := rfl

variable [CharP F 2]

omit [DecidableEq V] in
/-- In the coordinates `(x₀ + x₁, x₁)`, the lift is the block map. -/
theorem blockMap_sheetEquiv (M : Matrix V V F) (tw : V → V → Prop) [DecidableRel tw]
    (x : V × Bool → F) :
    blockMap M tw (sheetEquiv x) = sheetEquiv (lift2 M tw *ᵥ x) := by
  have hsum : ∀ u : V, (lift2 M tw *ᵥ x) (u, false) =
      ∑ v, (if tw u v then M u v * x (v, true) else M u v * x (v, false)) := by
    intro u
    simp only [mulVec, dotProduct, lift2, Matrix.of_apply, Fintype.sum_prod_type, Fintype.sum_bool]
    refine Finset.sum_congr rfl fun v _ => ?_
    split_ifs <;> simp_all
  have hsum' : ∀ u : V, (lift2 M tw *ᵥ x) (u, true) =
      ∑ v, (if tw u v then M u v * x (v, false) else M u v * x (v, true)) := by
    intro u
    simp only [mulVec, dotProduct, lift2, Matrix.of_apply, Fintype.sum_prod_type, Fintype.sum_bool]
    refine Finset.sum_congr rfl fun v _ => ?_
    split_ifs <;> simp_all
  rw [blockMap_apply, sheetEquiv_apply, sheetEquiv_apply]
  refine Prod.ext (funext fun u => ?_) (funext fun u => ?_)
  · show (M *ᵥ fun v => x (v, false) + x (v, true)) u =
      (lift2 M tw *ᵥ x) (u, false) + (lift2 M tw *ᵥ x) (u, true)
    rw [hsum u, hsum' u]
    simp only [mulVec, dotProduct, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    split_ifs <;> ring
  · show (M *ᵥ (fun v => x (v, true)) + twistPart M tw *ᵥ (fun v => x (v, false) + x (v, true))) u =
      (lift2 M tw *ᵥ x) (u, true)
    rw [hsum' u]
    simp only [Pi.add_apply, mulVec, dotProduct, twistPart, Matrix.of_apply,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    split_ifs with h
    · have := CharTwo.add_self_eq_zero (M u v * x (v, true))
      linear_combination this
    · ring

omit [DecidableEq V] in
theorem mem_ker_lift2_iff (M : Matrix V V F) (tw : V → V → Prop) [DecidableRel tw]
    (x : V × Bool → F) :
    x ∈ LinearMap.ker (lift2 M tw).mulVecLin ↔ sheetEquiv x ∈ LinearMap.ker (blockMap M tw) := by
  rw [LinearMap.mem_ker, LinearMap.mem_ker, blockMap_sheetEquiv, Matrix.mulVecLin_apply]
  constructor
  · intro h; rw [h, map_zero]
  · intro h; exact sheetEquiv.injective (h.trans (map_zero _).symm)

omit [DecidableEq V] in
theorem finrank_ker_lift2_eq (M : Matrix V V F) (tw : V → V → Prop) [DecidableRel tw] :
    finrank F (LinearMap.ker (lift2 M tw).mulVecLin) =
      finrank F (LinearMap.ker (blockMap M tw)) := by
  have hmap : (LinearMap.ker (lift2 M tw).mulVecLin).map
      (sheetEquiv : (V × Bool → F) ≃ₗ[F] (V → F) × (V → F)).toLinearMap =
      LinearMap.ker (blockMap M tw) := by
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (mem_ker_lift2_iff M tw x).mp hx
    · intro hp
      refine ⟨sheetEquiv.symm p, (mem_ker_lift2_iff M tw _).mpr (by simpa using hp), by simp⟩
  rw [← hmap, LinearEquiv.finrank_map_eq]

omit [DecidableEq V] [CharP F 2] in
/-- **The dimension count.** The kernel of the block map projects onto the `a` with
`M^tw a ∈ range M`, the kernel of the twist pairing on `ker M`, with fibres `ker M`. -/
theorem finrank_ker_blockMap (M : Matrix V V F) (tw : V → V → Prop) [DecidableRel tw] :
    finrank F (LinearMap.ker (blockMap M tw)) + finrank F (LinearMap.range (twistPairing M tw)) =
      2 * finrank F (LinearMap.ker M.mulVecLin) := by
  classical
  have hB : ∀ p : (V → F) × (V → F), p ∈ LinearMap.ker (blockMap M tw) ↔
      M *ᵥ p.1 = 0 ∧ M *ᵥ p.2 + twistPart M tw *ᵥ p.1 = 0 := by
    intro p
    rw [LinearMap.mem_ker, blockMap_apply, Prod.ext_iff]
    rfl
  let fstK := (LinearMap.fst F (V → F) (V → F)).comp (LinearMap.ker (blockMap M tw)).subtype
  have hrn := LinearMap.finrank_range_add_finrank_ker fstK
  -- the fibres of the projection are `ker M`
  have hker : finrank F (LinearMap.ker fstK) = finrank F (LinearMap.ker M.mulVecLin) := by
    have hmap : (LinearMap.ker fstK).map (LinearMap.ker (blockMap M tw)).subtype =
        (LinearMap.ker M.mulVecLin).map (LinearMap.inr F (V → F) (V → F)) := by
      ext p
      constructor
      · rintro ⟨q, hq, rfl⟩
        have h0 : (q : (V → F) × (V → F)).1 = 0 := hq
        have hq' := (hB q).mp q.2
        simp only [h0, Matrix.mulVec_zero, add_zero] at hq'
        refine ⟨(q : (V → F) × (V → F)).2, LinearMap.mem_ker.mpr hq'.2, ?_⟩
        simp only [LinearMap.inr_apply, Submodule.subtype_apply]
        exact Prod.ext h0.symm rfl
      · rintro ⟨b, hb, rfl⟩
        have hb' : M *ᵥ b = 0 := LinearMap.mem_ker.mp hb
        have hmem : ((0 : V → F), b) ∈ LinearMap.ker (blockMap M tw) :=
          (hB _).mpr ⟨Matrix.mulVec_zero _, by simp [hb']⟩
        exact ⟨⟨(0, b), hmem⟩, rfl, rfl⟩
    rw [(Submodule.equivMapOfInjective _ (LinearMap.ker (blockMap M tw)).injective_subtype
        (LinearMap.ker fstK)).finrank_eq, hmap,
      ← (Submodule.equivMapOfInjective _ LinearMap.inr_injective
        (LinearMap.ker M.mulVecLin)).finrank_eq]
  -- the image of the projection is the kernel of the twist pairing
  have hrange : LinearMap.range fstK =
      (LinearMap.ker (twistPairing M tw)).map (LinearMap.ker M.mulVecLin).subtype := by
    ext a
    constructor
    · rintro ⟨q, rfl⟩
      obtain ⟨hq1, hq2⟩ := (hB q).mp q.2
      refine ⟨⟨(q : (V → F) × (V → F)).1, LinearMap.mem_ker.mpr hq1⟩, ?_, rfl⟩
      refine LinearMap.mem_ker.mpr (LinearMap.ext fun y => ?_)
      rw [twistPairing_apply, LinearMap.zero_apply]
      have hr : twistPart M tw *ᵥ (q : (V → F) × (V → F)).1 ∈ LinearMap.range M.mulVecLin :=
        ⟨-(q : (V → F) × (V → F)).2, by
          rw [Matrix.mulVecLin_apply, Matrix.mulVec_neg]
          exact (neg_eq_of_add_eq_zero_right hq2)⟩
      exact (mem_range_iff_dotProduct_ker_transpose M _).mp hr y (LinearMap.mem_ker.mp y.2)
    · rintro ⟨a', ha', rfl⟩
      have hr : twistPart M tw *ᵥ (a' : V → F) ∈ LinearMap.range M.mulVecLin := by
        refine (mem_range_iff_dotProduct_ker_transpose M _).mpr fun y hy => ?_
        have := congrArg (fun φ => φ ⟨y, LinearMap.mem_ker.mpr hy⟩) (LinearMap.mem_ker.mp ha')
        simpa [twistPairing_apply] using this
      obtain ⟨b, hb⟩ := hr
      have hmem : ((a' : V → F), -b) ∈ LinearMap.ker (blockMap M tw) := by
        refine (hB _).mpr ⟨LinearMap.mem_ker.mp a'.2, ?_⟩
        rw [Matrix.mulVecLin_apply] at hb
        simp only [Matrix.mulVec_neg, hb, neg_add_cancel]
      exact ⟨⟨_, hmem⟩, rfl⟩
  have hran : finrank F (LinearMap.range fstK) = finrank F (LinearMap.ker (twistPairing M tw)) := by
    rw [hrange, ← (Submodule.equivMapOfInjective _ (LinearMap.ker M.mulVecLin).injective_subtype
      (LinearMap.ker (twistPairing M tw))).finrank_eq]
  have htp := LinearMap.finrank_range_add_finrank_ker (twistPairing M tw)
  omega

omit [DecidableEq V] in
/-- **The equivariant crux (c), one step.** Over a field of characteristic `2`, the lift of `M` along a double
cover has `dim ker (lift2 M tw) = 2 dim ker M - r`, where `r` is the rank of the twist pairing. -/
theorem finrank_ker_lift2 (M : Matrix V V F) (tw : V → V → Prop) [DecidableRel tw] :
    finrank F (LinearMap.ker (lift2 M tw).mulVecLin) +
        finrank F (LinearMap.range (twistPairing M tw)) =
      2 * finrank F (LinearMap.ker M.mulVecLin) := by
  rw [finrank_ker_lift2_eq]
  exact finrank_ker_blockMap M tw

omit [DecidableEq V] in
/-- **The excess recursion** `e' = 2e - r`, for the excess `e = dim ker - N/2`. -/
theorem excess_lift2 (M : Matrix V V F) (tw : V → V → Prop) [DecidableRel tw] :
    (finrank F (LinearMap.ker (lift2 M tw).mulVecLin) : ℚ) - (Fintype.card (V × Bool) : ℚ) / 2 =
      2 * ((finrank F (LinearMap.ker M.mulVecLin) : ℚ) - (Fintype.card V : ℚ) / 2) -
        finrank F (LinearMap.range (twistPairing M tw)) := by
  have h : ((finrank F (LinearMap.ker (lift2 M tw).mulVecLin) : ℕ) : ℚ) +
      (finrank F (LinearMap.range (twistPairing M tw)) : ℚ) =
      2 * (finrank F (LinearMap.ker M.mulVecLin) : ℚ) := by
    exact_mod_cast finrank_ker_lift2 M tw
  rw [Fintype.card_prod, Fintype.card_bool]
  push_cast
  linarith

omit [DecidableEq V] in
/-- **The rate does not increase** along a double cover. -/
theorem rate_lift2_le (M : Matrix V V F) (tw : V → V → Prop) [DecidableRel tw] :
    (finrank F (LinearMap.ker (lift2 M tw).mulVecLin) : ℚ) / Fintype.card (V × Bool) ≤
      (finrank F (LinearMap.ker M.mulVecLin) : ℚ) / Fintype.card V := by
  have h := finrank_ker_lift2 M tw
  have hle : (finrank F (LinearMap.ker (lift2 M tw).mulVecLin) : ℚ) ≤
      2 * (finrank F (LinearMap.ker M.mulVecLin) : ℚ) := by
    exact_mod_cast (by omega : finrank F (LinearMap.ker (lift2 M tw).mulVecLin) ≤
      2 * finrank F (LinearMap.ker M.mulVecLin))
  rw [Fintype.card_prod, Fintype.card_bool]
  rcases Nat.eq_zero_or_pos (Fintype.card V) with h0 | hpos
  · simp [h0]
  · have hpos' : (0 : ℚ) < Fintype.card V := by exact_mod_cast hpos
    rw [div_le_div_iff₀ (by push_cast; positivity) hpos']
    push_cast
    nlinarith

end BoundedNesting
