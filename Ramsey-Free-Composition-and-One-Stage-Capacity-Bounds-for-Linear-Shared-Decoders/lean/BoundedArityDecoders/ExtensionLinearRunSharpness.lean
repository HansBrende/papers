import BoundedArityDecoders.ExtensionFieldTransfer
import Mathlib.Data.Sym.Card

/-!
# Proofs of Model Bridges and Alternating-Coloring Sharpness (`Result 1`, Part I)

Complete kernel-verified proofs of:
* `extension_LinearModelAndCharBridges : Extension_LinearModelAndCharBridgesSpec`
* `extension_Theorem1A_AlternatingSharpness : Extension_Theorem1A_AlternatingSharpnessSpec`
* `alternatingSharpCode_finrank_and_shift_inf` (unpacked top-level theorem)
-/

namespace BoundedArityDecoders

open Module
open scoped BigOperators

section ModelAndCharBridges

/-- `laneOneMatrixEquiv` intertwines `laneRot` with `SwapRigidity.rot`. -/
theorem laneOneMatrixEquiv_laneRot {F : Type*} [Field F] {d : ℕ} (s : ZMod d)
    (X : Matrix (ZMod d) (ZMod d) (Fin 1 → F)) :
    laneOneMatrixEquiv F d (laneRot s X) = SwapRigidity.rot s (laneOneMatrixEquiv F d X) := by
  ext i j
  rfl

/-- `matrixToSharedStateEquiv` intertwines `laneRot` with `SharedDecoders.rot`. -/
theorem matrixToSharedStateEquiv_laneRot {F : Type*} [Semiring F] {d b : ℕ} (s : ZMod d)
    (X : Matrix (ZMod d) (ZMod d) (Fin b → F)) :
    matrixToSharedStateEquiv F d b (laneRot s X) =
      SharedDecoders.rot s (matrixToSharedStateEquiv F d b X) :=
  rfl

private lemma laneOneMatrixEquiv_symm_rot {F : Type*} [Field F] {d : ℕ} (s : ZMod d)
    (Y : Matrix (ZMod d) (ZMod d) F) :
    (laneOneMatrixEquiv F d).symm (SwapRigidity.rot s Y) =
      laneRot s ((laneOneMatrixEquiv F d).symm Y) := by
  ext i j u
  fin_cases u
  rfl

/-- Proof of `Extension_LinearModelAndCharBridgesSpec`. -/
theorem extension_LinearModelAndCharBridges : Extension_LinearModelAndCharBridgesSpec := by
  refine ⟨?_, ?_, ?_⟩
  · intro F _ d κ p 𝒳 s
    let e := laneOneMatrixEquiv F d
    let 𝒳₁ := 𝒳.map e.toLinearMap
    refine ⟨?_, LinearEquiv.finrank_map_eq e 𝒳, ?_⟩
    · constructor
      · rintro ⟨dec, hdec⟩
        let rowEquiv : (ZMod d → Fin 1 → F) ≃ₗ[F] (ZMod d → F) :=
          { toFun := fun f j => f j 0
            invFun := fun g j _ => g j
            left_inv := fun f => by ext j u; fin_cases u; rfl
            right_inv := fun g => rfl
            map_add' := fun _ _ => rfl
            map_smul' := fun _ _ => rfl }
        refine ⟨fun k => rowEquiv.toLinearMap ∘ₗ dec k ∘ₗ e.symm.toLinearMap, ?_⟩
        rintro _ ⟨X, hX, rfl⟩ c
        funext j
        have hXc := congrFun (hdec X hX c) j
        have hXc0 := congrFun hXc 0
        have hrot : e.symm (SwapRigidity.rot c (e X)) = laneRot c X := by
          rw [laneOneMatrixEquiv_symm_rot]
          exact congrArg (laneRot c) (LinearEquiv.symm_apply_apply e X)
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
        rw [hrot]
        exact hXc0
      · rintro ⟨dec, hdec⟩
        let rowEquivInv : (ZMod d → F) →ₗ[F] (ZMod d → Fin 1 → F) :=
          { toFun := fun g j _ => g j
            map_add' := fun _ _ => rfl
            map_smul' := fun _ _ => rfl }
        refine ⟨fun k => rowEquivInv ∘ₗ dec k ∘ₗ e.toLinearMap, ?_⟩
        intro X hX c
        have hX₁ : e X ∈ 𝒳₁ := ⟨X, hX, rfl⟩
        have hXc := hdec (e X) hX₁ c
        funext j u
        fin_cases u
        have hXc_j := congrFun hXc j
        have hrot : e (laneRot c X) = SwapRigidity.rot c (e X) :=
          laneOneMatrixEquiv_laneRot c X
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hrot]
        exact hXc_j
    · have hmap_inf :
          (𝒳 ⊓ 𝒳.comap (laneRot s)).map e.toLinearMap =
            𝒳₁ ⊓ 𝒳₁.comap (SwapRigidity.rot s) := by
        ext Y
        constructor
        · rintro ⟨X, ⟨hX, hXs⟩, rfl⟩
          refine ⟨⟨X, hX, rfl⟩, ?_⟩
          show SwapRigidity.rot s (e X) ∈ 𝒳₁
          rw [← laneOneMatrixEquiv_laneRot]
          exact ⟨laneRot s X, hXs, rfl⟩
        · rintro ⟨⟨X, hX, rfl⟩, hYs⟩
          refine ⟨X, ⟨hX, ?_⟩, rfl⟩
          show laneRot s X ∈ 𝒳
          obtain ⟨Z, hZ, hZe⟩ := hYs
          have hZX : Z = laneRot s X := by
            apply e.injective
            change e.toLinearMap Z = e (laneRot s X)
            rw [hZe]
            exact (laneOneMatrixEquiv_laneRot s X).symm
          rwa [← hZX]
      rw [← hmap_inf]
      exact LinearEquiv.finrank_map_eq e (𝒳 ⊓ 𝒳.comap (laneRot s))
  · intro F _ d b κ p 𝒳 s hLin
    obtain ⟨dec, hdec⟩ := hLin
    let e := matrixToSharedStateEquiv F d b
    constructor
    · refine ⟨fun k Y => dec k (e.symm Y), ?_⟩
      rintro _ ⟨X, hX, rfl⟩ c
      have hrot : e.symm (SharedDecoders.rot c (e X)) = laneRot c X := by
        ext i j u
        rfl
      change X c = dec (p c) (e.symm (SharedDecoders.rot c (e X)))
      rw [hrot]
      exact hdec X hX c
    · rintro X ⟨hX0, hXs⟩ c c' δ δ' hδ hδ' hp hc j
      have hXδ : ∀ γ ∈ ({0, s} : Finset (ZMod d)), laneRot γ X ∈ 𝒳 := by
        intro γ hγ
        simp only [Finset.mem_insert, Finset.mem_singleton] at hγ
        rcases hγ with rfl | rfl
        · have hid : laneRot (0 : ZMod d) X = X := by
            ext i k u
            simp [laneRot]
          rwa [hid]
        · exact hXs
      have hrot_add : ∀ a γ : ZMod d, laneRot a (laneRot γ X) = laneRot (a + γ) X := by
        intro a γ
        ext i k u
        simp only [laneRot_apply]
        exact congrArg (fun t => X i t u) (by ring)
      have eq1 : X c (j + δ) = dec (p c) (laneRot (c + δ) X) j := by
        have h := congrFun (hdec (laneRot δ X) (hXδ δ hδ) c) j
        rwa [hrot_add c δ] at h
      have eq2 : X c' (j + δ') = dec (p c') (laneRot (c' + δ') X) j := by
        have h := congrFun (hdec (laneRot δ' X) (hXδ δ' hδ') c') j
        rwa [hrot_add c' δ'] at h
      rw [eq2, eq1, ← hp, hc]
  · intro F _ n _
    exact coprimeToChar_iff_natCast_ne_zero F n

end ModelAndCharBridges

section AlternatingSharpness

private def twoMulZMod (m : ℕ) [NeZero m] (i : ZMod m) : ZMod (2 * m) :=
  ((2 * i.val : ℕ) : ZMod (2 * m))

private lemma val_one_two_mul (m : ℕ) [NeZero m] :
    (1 : ZMod (2 * m)).val = 1 := by
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have : Fact (1 < 2 * m) := ⟨by omega⟩
  exact ZMod.val_one (2 * m)

private lemma zmod_two_mul_val_add_mod_two (m : ℕ) [NeZero m] (a b : ZMod (2 * m)) :
    (a + b).val % 2 = (a.val + b.val) % 2 := by
  have : NeZero (2 * m) := ⟨Nat.mul_ne_zero (by decide) (NeZero.ne m)⟩
  rw [ZMod.val_add, Nat.mod_mod_of_dvd _ (dvd_mul_right 2 m)]

private lemma twoMulZMod_val (m : ℕ) [NeZero m] (i : ZMod m) :
    (twoMulZMod m i).val = 2 * i.val := by
  have : NeZero (2 * m) := ⟨Nat.mul_ne_zero (by decide) (NeZero.ne m)⟩
  have hi : i.val < m := ZMod.val_lt i
  exact ZMod.val_natCast_of_lt (by omega)

private lemma twoMulZMod_add_one_val (m : ℕ) [NeZero m] (i : ZMod m) :
    (twoMulZMod m i + 1).val = 2 * i.val + 1 := by
  have : NeZero (2 * m) := ⟨Nat.mul_ne_zero (by decide) (NeZero.ne m)⟩
  have hi : i.val < m := ZMod.val_lt i
  rw [ZMod.val_add, twoMulZMod_val, val_one_two_mul]
  exact Nat.mod_eq_of_lt (by omega)

private lemma twoMulZMod_add (m : ℕ) [NeZero m] (i j : ZMod m) :
    twoMulZMod m (i + j) = twoMulZMod m i + twoMulZMod m j := by
  unfold twoMulZMod
  rw [← Nat.cast_add, ZMod.natCast_eq_natCast_iff]
  change (2 * (i + j).val) % (2 * m) = (2 * i.val + 2 * j.val) % (2 * m)
  rw [ZMod.val_add]
  have hdist : 2 * i.val + 2 * j.val = 2 * (i.val + j.val) := by ring
  rw [hdist]
  have hdiv : i.val + j.val = (i.val + j.val) % m + m * ((i.val + j.val) / m) :=
    (Nat.mod_add_div (i.val + j.val) m).symm
  conv_rhs => rw [hdiv]
  have hmul : 2 * ((i.val + j.val) % m + m * ((i.val + j.val) / m)) =
      2 * ((i.val + j.val) % m) + (2 * m) * ((i.val + j.val) / m) := by
    ring
  rw [hmul, Nat.add_mul_mod_self_left]

private lemma twoMulZMod_zero (m : ℕ) [NeZero m] :
    twoMulZMod m 0 = 0 := by
  simp [twoMulZMod]

private lemma twoMulZMod_one (m : ℕ) [NeZero m] :
    twoMulZMod m 1 = (2 : ZMod (2 * m)) := by
  unfold twoMulZMod
  rcases eq_or_lt_of_le (Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne m))) with rfl | hm
  · have h10 : (1 : ZMod 1) = 0 := Subsingleton.elim _ _
    rw [h10, ZMod.val_zero]
    exact (ZMod.natCast_self 2).symm
  · have : Fact (1 < m) := ⟨hm⟩
    rw [ZMod.val_one]
    simp

private lemma twoMulZMod_sub (m : ℕ) [NeZero m] (i j : ZMod m) :
    twoMulZMod m (i - j) = twoMulZMod m i - twoMulZMod m j := by
  have h := twoMulZMod_add m (i - j) j
  rw [sub_add_cancel] at h
  exact eq_sub_of_add_eq h.symm

private def paritySplitEquiv (m : ℕ) [NeZero m] : (ZMod m ⊕ ZMod m) ≃ ZMod (2 * m) where
  toFun s :=
    match s with
    | Sum.inl i => twoMulZMod m i
    | Sum.inr i => twoMulZMod m i + 1
  invFun c :=
    if c.val % 2 = 0 then Sum.inl ((c.val / 2 : ℕ) : ZMod m)
    else Sum.inr ((c.val / 2 : ℕ) : ZMod m)
  left_inv s := by
    rcases s with i | i
    · have hv := twoMulZMod_val m i
      have hmod : (twoMulZMod m i).val % 2 = 0 := by omega
      have hdiv : (twoMulZMod m i).val / 2 = i.val := by omega
      simp [hmod, hdiv]
    · have hv := twoMulZMod_add_one_val m i
      have hmod : (twoMulZMod m i + 1).val % 2 = 1 := by omega
      have hdiv : (twoMulZMod m i + 1).val / 2 = i.val := by omega
      simp [hmod, hdiv]
  right_inv c := by
    have : NeZero (2 * m) := ⟨Nat.mul_ne_zero (by decide) (NeZero.ne m)⟩
    have hc : c.val < 2 * m := ZMod.val_lt c
    have hdiv_lt : c.val / 2 < m := by omega
    have hval_div : (((c.val / 2 : ℕ) : ZMod m)).val = c.val / 2 :=
      ZMod.val_natCast_of_lt hdiv_lt
    by_cases hpar : c.val % 2 = 0
    · simp only [hpar, ↓reduceIte]
      apply ZMod.val_injective
      rw [twoMulZMod_val, hval_div]
      omega
    · simp only [hpar, ↓reduceIte]
      apply ZMod.val_injective
      rw [twoMulZMod_add_one_val, hval_div]
      omega

private lemma card_altTwoColoring_eq (m : ℕ) [NeZero m] (k : Fin 2) :
    haveI : NeZero (2 * m) := ⟨Nat.mul_ne_zero (by decide) (NeZero.ne m)⟩
    (Finset.univ.filter fun c : ZMod (2 * m) => altTwoColoring m c = k).card = m := by
  have : NeZero (2 * m) := ⟨Nat.mul_ne_zero (by decide) (NeZero.ne m)⟩
  fin_cases k
  · change (Finset.univ.filter fun c : ZMod (2 * m) => altTwoColoring m c = 0).card = m
    have hbij : (Finset.univ : Finset (ZMod m)).map
        ⟨fun i => twoMulZMod m i, fun i j hij => by
          have h := (paritySplitEquiv m).injective
            (show paritySplitEquiv m (Sum.inl i) = paritySplitEquiv m (Sum.inl j) from hij)
          exact Sum.inl.inj h⟩ =
        Finset.univ.filter (fun c : ZMod (2 * m) => altTwoColoring m c = 0) := by
      ext c
      simp only [Finset.mem_map, Finset.mem_univ, true_and,
        Finset.mem_filter, altTwoColoring, Fin.ext_iff, Fin.val_zero]
      constructor
      · rintro ⟨i, rfl⟩
        change (twoMulZMod m i).val % 2 = 0
        rw [twoMulZMod_val]
        omega
      · intro hc0
        obtain ⟨s, rfl⟩ := (paritySplitEquiv m).surjective c
        rcases s with i | i
        · exact ⟨i, rfl⟩
        · exfalso
          have hv := twoMulZMod_add_one_val m i
          change (twoMulZMod m i + 1).val % 2 = 0 at hc0
          omega
    rw [← hbij, Finset.card_map, Finset.card_univ, ZMod.card]
  · change (Finset.univ.filter fun c : ZMod (2 * m) => altTwoColoring m c = 1).card = m
    have hbij : (Finset.univ : Finset (ZMod m)).map
        ⟨fun i => twoMulZMod m i + 1, fun i j hij => by
          have h := (paritySplitEquiv m).injective
            (show paritySplitEquiv m (Sum.inr i) = paritySplitEquiv m (Sum.inr j) from hij)
          exact Sum.inr.inj h⟩ =
        Finset.univ.filter (fun c : ZMod (2 * m) => altTwoColoring m c = 1) := by
      ext c
      simp only [Finset.mem_map, Finset.mem_univ, true_and,
        Finset.mem_filter, altTwoColoring, Fin.ext_iff, Fin.val_one]
      constructor
      · rintro ⟨i, rfl⟩
        change (twoMulZMod m i + 1).val % 2 = 1
        rw [twoMulZMod_add_one_val]
        omega
      · intro hc1
        obtain ⟨s, rfl⟩ := (paritySplitEquiv m).surjective c
        rcases s with i | i
        · exfalso
          have hv := twoMulZMod_val m i
          change (twoMulZMod m i).val % 2 = 1 at hc1
          omega
        · exact ⟨i, rfl⟩
    rw [← hbij, Finset.card_map, Finset.card_univ, ZMod.card]

/-- Subspace of symmetric `m × m` matrices over `F`. -/
private def symMatrixSubmodule (F : Type*) [Field F] (m : ℕ) :
    Submodule F (Matrix (ZMod m) (ZMod m) F) where
  carrier := {M | ∀ i j : ZMod m, M i j = M j i}
  add_mem' {A B} hA hB i j := by simp [hA i j, hB i j]
  zero_mem' _ _ := rfl
  smul_mem' a {A} hA i j := by simp [hA i j]

private def symMatrixEquivSym2 (F : Type*) [Field F] (m : ℕ) :
    symMatrixSubmodule F m ≃ₗ[F] (Sym2 (ZMod m) → F) where
  toFun M := Sym2.lift ⟨M.1, M.2⟩
  invFun f := ⟨Matrix.of (fun i j => f s(i, j)), fun i j => by
    simp only [Matrix.of_apply]
    exact congrArg f Sym2.eq_swap⟩
  left_inv M := by
    ext i j
    rfl
  right_inv f := by
    ext z
    induction z using Sym2.ind with
    | _ i j => rfl
  map_add' M N := by
    ext z
    induction z using Sym2.ind with
    | _ i j => rfl
  map_smul' a M := by
    ext z
    induction z using Sym2.ind with
    | _ i j => rfl

private lemma finrank_symMatrixSubmodule (F : Type*) [Field F] (m : ℕ) [NeZero m] :
    finrank F (symMatrixSubmodule F m) = m * (m + 1) / 2 := by
  rw [LinearEquiv.finrank_eq (symMatrixEquivSym2 F m)]
  rw [Module.finrank_pi, Sym2.card, ZMod.card, Nat.choose_two_right]
  simp [Nat.mul_comm]

/-- Subspace of Hankel (`A i j = f (i + j)`) `m × m` matrices over `F`, cut out by
`A i j = A j i` and `A i j = A (j + 1) (i - 1)`. -/
private def hankelMatrixSubmodule (F : Type*) [Field F] (m : ℕ) :
    Submodule F (Matrix (ZMod m) (ZMod m) F) where
  carrier := {M | (∀ i j : ZMod m, M i j = M j i) ∧
    (∀ i j : ZMod m, M i j = M (j + 1) (i - 1))}
  add_mem' {A B} hA hB := ⟨fun i j => by simp [hA.1 i j, hB.1 i j],
    fun i j => by simp [hA.2 i j, hB.2 i j]⟩
  zero_mem' := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  smul_mem' a {A} hA := ⟨fun i j => by simp [hA.1 i j], fun i j => by simp [hA.2 i j]⟩

private lemma hankel_step_nat {F : Type*} [Field F] {m : ℕ} {M : Matrix (ZMod m) (ZMod m) F}
    (h1 : ∀ i j, M i j = M j i) (h2 : ∀ i j, M i j = M (j + 1) (i - 1)) :
    ∀ (k : ℕ) (i j : ZMod m), M i j = M (i - (k : ZMod m)) (j + (k : ZMod m))
  | 0, i, j => by simp
  | k + 1, i, j => by
    have ih := hankel_step_nat h1 h2 k i j
    have hstep : M (i - (k : ZMod m)) (j + (k : ZMod m)) =
        M (i - (k : ZMod m) - 1) (j + (k : ZMod m) + 1) := by
      rw [h2 (i - (k : ZMod m)) (j + (k : ZMod m)), h1]
    rw [ih, hstep]
    congr 1 <;> push_cast <;> ring

private def hankelMatrixEquivFun (F : Type*) [Field F] (m : ℕ) [NeZero m] :
    hankelMatrixSubmodule F m ≃ₗ[F] (ZMod m → F) where
  toFun M s := M.1 0 s
  invFun f := ⟨Matrix.of (fun i j => f (i + j)),
    ⟨fun i j => by simp [add_comm], fun i j => by
      simp only [Matrix.of_apply]
      congr 1
      ring⟩⟩
  left_inv M := by
    ext i j
    simp only [Matrix.of_apply]
    have h := hankel_step_nat M.2.1 M.2.2 i.val i j
    simp only [ZMod.natCast_zmod_val, sub_self] at h
    rw [h, add_comm j i]
  right_inv f := by
    ext s
    simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private lemma finrank_hankelMatrixSubmodule (F : Type*) [Field F] (m : ℕ) [NeZero m] :
    finrank F (hankelMatrixSubmodule F m) = m := by
  rw [LinearEquiv.finrank_eq (hankelMatrixEquivFun F m), Module.finrank_pi, ZMod.card]

/-- Four-block decomposition of `Matrix (ZMod (2 * m)) (ZMod (2 * m)) F` into `(even/odd) × (even/odd)`. -/
private def fourBlockEquiv (F : Type*) [Field F] (m : ℕ) [NeZero m] :
    Matrix (ZMod (2 * m)) (ZMod (2 * m)) F ≃ₗ[F]
      (Matrix (ZMod m) (ZMod m) F × Matrix (ZMod m) (ZMod m) F ×
        Matrix (ZMod m) (ZMod m) F × Matrix (ZMod m) (ZMod m) F) where
  toFun X :=
    (Matrix.of (fun i j => X (twoMulZMod m i) (twoMulZMod m j)),
     Matrix.of (fun i j => X (twoMulZMod m i) (twoMulZMod m j + 1)),
     Matrix.of (fun i j => X (twoMulZMod m i + 1) (twoMulZMod m j)),
     Matrix.of (fun i j => X (twoMulZMod m i + 1) (twoMulZMod m j + 1)))
  invFun T := Matrix.of fun r c =>
    match (paritySplitEquiv m).symm r, (paritySplitEquiv m).symm c with
    | Sum.inl i, Sum.inl j => T.1 i j
    | Sum.inl i, Sum.inr j => T.2.1 i j
    | Sum.inr i, Sum.inl j => T.2.2.1 i j
    | Sum.inr i, Sum.inr j => T.2.2.2 i j
  left_inv X := by
    ext r c
    simp only [Matrix.of_apply]
    obtain ⟨sr, rfl⟩ := (paritySplitEquiv m).surjective r
    obtain ⟨sc, rfl⟩ := (paritySplitEquiv m).surjective c
    simp only [Equiv.symm_apply_apply]
    rcases sr with i | i <;> rcases sc with j | j <;> rfl
  right_inv T := by
    rcases T with ⟨B, A, C, D⟩
    have hinl : ∀ i : ZMod m, (paritySplitEquiv m).symm (twoMulZMod m i) = Sum.inl i :=
      fun i => (paritySplitEquiv m).symm_apply_apply (Sum.inl i)
    have hinr : ∀ i : ZMod m, (paritySplitEquiv m).symm (twoMulZMod m i + 1) = Sum.inr i :=
      fun i => (paritySplitEquiv m).symm_apply_apply (Sum.inr i)
    ext i j <;> simp [hinl, hinr]
  map_add' X Y := by
    ext i j <;> rfl
  map_smul' a X := by
    ext i j <;> rfl

private lemma mem_alternatingSharpCode_iff_blocks {F : Type*} [Field F] {m : ℕ} [NeZero m]
    (X : Matrix (ZMod (2 * m)) (ZMod (2 * m)) F) :
    X ∈ alternatingSharpCode F m ↔
      let B := (fourBlockEquiv F m X).1
      let A := (fourBlockEquiv F m X).2.1
      let C := (fourBlockEquiv F m X).2.2.1
      let D := (fourBlockEquiv F m X).2.2.2
      (∀ i j, B i j = B j i) ∧
      (∀ i j, A i j = A (j + 1) (i - 1)) ∧
      (∀ i j, C i j = C j i) ∧
      (∀ i j, D i j = D (j + 1) (i - 1)) := by
  have heven_cls : ∀ i : ZMod m, (altTwoColoring m (twoMulZMod m i)).val = 0 := by
    intro i
    simp only [altTwoColoring, twoMulZMod_val]
    omega
  have hodd_cls : ∀ i : ZMod m, (altTwoColoring m (twoMulZMod m i + 1)).val = 1 := by
    intro i
    simp only [altTwoColoring, twoMulZMod_add_one_val]
    omega
  have heven_par : ∀ j : ZMod m, (twoMulZMod m j).val % 2 = 0 := by
    intro j
    rw [twoMulZMod_val]
    omega
  have hodd_par : ∀ j : ZMod m, (twoMulZMod m j + 1).val % 2 = 1 := by
    intro j
    rw [twoMulZMod_add_one_val]
    omega
  have h1 : ∀ j : ZMod m, (twoMulZMod m j + 1) + 1 = twoMulZMod m (j + 1) := by
    intro j
    rw [twoMulZMod_add, twoMulZMod_one]
    ring
  have h2 : ∀ i : ZMod m, (-1 : ZMod (2 * m)) + twoMulZMod m i = twoMulZMod m (i - 1) + 1 := by
    intro i
    rw [twoMulZMod_sub, twoMulZMod_one]
    ring
  have h3 : ∀ i : ZMod m, (-1 : ZMod (2 * m)) + (twoMulZMod m i + 1) = twoMulZMod m i := by
    intro i
    ring
  have h4 : ∀ j : ZMod m, (twoMulZMod m j + 1) + 2 = twoMulZMod m (j + 1) + 1 := by
    intro j
    rw [twoMulZMod_add, twoMulZMod_one]
    ring
  have h5 : ∀ i : ZMod m,
      (-2 : ZMod (2 * m)) + (twoMulZMod m i + 1) = twoMulZMod m (i - 1) + 1 := by
    intro i
    rw [twoMulZMod_sub, twoMulZMod_one]
    ring
  constructor
  · intro hX
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i j
      have h := congrFun (hX (twoMulZMod m i)) (twoMulZMod m j)
      simp only [alternatingSharpDecoder, LinearMap.coe_mk, AddHom.coe_mk,
        heven_cls, ↓reduceIte, heven_par, SwapRigidity.rot_apply, zero_add] at h
      simpa [fourBlockEquiv] using h
    · intro i j
      have h := congrFun (hX (twoMulZMod m i)) (twoMulZMod m j + 1)
      have hop : ¬ (twoMulZMod m j + 1).val % 2 = 0 := by rw [hodd_par]; decide
      simp only [alternatingSharpDecoder, LinearMap.coe_mk, AddHom.coe_mk,
        heven_cls, ↓reduceIte, hop, SwapRigidity.rot_apply, h1, h2] at h
      simpa [fourBlockEquiv] using h
    · intro i j
      have h := congrFun (hX (twoMulZMod m i + 1)) (twoMulZMod m j)
      have hoc : ¬ (altTwoColoring m (twoMulZMod m i + 1)).val = 0 := by rw [hodd_cls]; decide
      simp only [alternatingSharpDecoder, LinearMap.coe_mk, AddHom.coe_mk,
        hoc, ↓reduceIte, heven_par, SwapRigidity.rot_apply, h3] at h
      simpa [fourBlockEquiv] using h
    · intro i j
      have h := congrFun (hX (twoMulZMod m i + 1)) (twoMulZMod m j + 1)
      have hoc : ¬ (altTwoColoring m (twoMulZMod m i + 1)).val = 0 := by rw [hodd_cls]; decide
      have hop : ¬ (twoMulZMod m j + 1).val % 2 = 0 := by rw [hodd_par]; decide
      simp only [alternatingSharpDecoder, LinearMap.coe_mk, AddHom.coe_mk,
        hoc, ↓reduceIte, hop, SwapRigidity.rot_apply, h4, h5] at h
      simpa [fourBlockEquiv] using h
  · rintro ⟨hB, hA, hC, hD⟩ c
    funext u
    obtain ⟨sc, rfl⟩ := (paritySplitEquiv m).surjective c
    obtain ⟨su, rfl⟩ := (paritySplitEquiv m).surjective u
    rcases sc with i | i <;> rcases su with j | j
    · change X (twoMulZMod m i) (twoMulZMod m j) =
        alternatingSharpDecoder F m (altTwoColoring m (twoMulZMod m i))
          (SwapRigidity.rot (twoMulZMod m i) X) (twoMulZMod m j)
      simp only [alternatingSharpDecoder, LinearMap.coe_mk, AddHom.coe_mk,
        heven_cls, ↓reduceIte, heven_par, SwapRigidity.rot_apply, zero_add]
      exact hB i j
    · change X (twoMulZMod m i) (twoMulZMod m j + 1) =
        alternatingSharpDecoder F m (altTwoColoring m (twoMulZMod m i))
          (SwapRigidity.rot (twoMulZMod m i) X) (twoMulZMod m j + 1)
      have hop : ¬ (twoMulZMod m j + 1).val % 2 = 0 := by rw [hodd_par]; decide
      simp only [alternatingSharpDecoder, LinearMap.coe_mk, AddHom.coe_mk,
        heven_cls, ↓reduceIte, hop, SwapRigidity.rot_apply, h1, h2]
      exact hA i j
    · change X (twoMulZMod m i + 1) (twoMulZMod m j) =
        alternatingSharpDecoder F m (altTwoColoring m (twoMulZMod m i + 1))
          (SwapRigidity.rot (twoMulZMod m i + 1) X) (twoMulZMod m j)
      have hoc : ¬ (altTwoColoring m (twoMulZMod m i + 1)).val = 0 := by rw [hodd_cls]; decide
      simp only [alternatingSharpDecoder, LinearMap.coe_mk, AddHom.coe_mk,
        hoc, ↓reduceIte, heven_par, SwapRigidity.rot_apply, h3]
      exact hC i j
    · change X (twoMulZMod m i + 1) (twoMulZMod m j + 1) =
        alternatingSharpDecoder F m (altTwoColoring m (twoMulZMod m i + 1))
          (SwapRigidity.rot (twoMulZMod m i + 1) X) (twoMulZMod m j + 1)
      have hoc : ¬ (altTwoColoring m (twoMulZMod m i + 1)).val = 0 := by rw [hodd_cls]; decide
      have hop : ¬ (twoMulZMod m j + 1).val % 2 = 0 := by rw [hodd_par]; decide
      simp only [alternatingSharpDecoder, LinearMap.coe_mk, AddHom.coe_mk,
        hoc, ↓reduceIte, hop, SwapRigidity.rot_apply, h4, h5]
      exact hD i j

/-- Shifted-symmetric `m × m` matrices `{A | ∀ i j, A i j = A (j + 1) (i - 1)}`, linearly
isomorphic to `symMatrixSubmodule F m` via row shift `i ↦ i + 1`. -/
private def shiftedSymMatrixSubmodule (F : Type*) [Field F] (m : ℕ) :
    Submodule F (Matrix (ZMod m) (ZMod m) F) where
  carrier := {A | ∀ i j : ZMod m, A i j = A (j + 1) (i - 1)}
  add_mem' {A B} hA hB i j := by simp [hA i j, hB i j]
  zero_mem' _ _ := rfl
  smul_mem' a {A} hA i j := by simp [hA i j]

private def shiftedSymEquivSym (F : Type*) [Field F] (m : ℕ) :
    shiftedSymMatrixSubmodule F m ≃ₗ[F] symMatrixSubmodule F m where
  toFun A := ⟨Matrix.of (fun i j => A.1 (i + 1) j), fun i j => by
    simp only [Matrix.of_apply]
    have h := A.2 (i + 1) j
    simpa [add_sub_cancel_right] using h⟩
  invFun S := ⟨Matrix.of (fun i j => S.1 (i - 1) j), fun i j => by
    simp only [Matrix.of_apply]
    have h := S.2 (i - 1) j
    simpa [add_sub_cancel_right] using h⟩
  left_inv A := by
    ext i j
    simp [sub_add_cancel]
  right_inv S := by
    ext i j
    simp [add_sub_cancel_right]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private lemma finrank_alternatingSharpCode (F : Type*) [Field F] (m : ℕ) [NeZero m] :
    finrank F (alternatingSharpCode F m) = 2 * m * (m + 1) := by
  let P :=
    symMatrixSubmodule F m ×
      shiftedSymMatrixSubmodule F m ×
      symMatrixSubmodule F m ×
      shiftedSymMatrixSubmodule F m
  let equivCode : alternatingSharpCode F m ≃ₗ[F] P :=
    { toFun := fun X =>
        let T := fourBlockEquiv F m X.1
        have h := (mem_alternatingSharpCode_iff_blocks X.1).mp X.2
        (⟨T.1, h.1⟩, ⟨T.2.1, h.2.1⟩, ⟨T.2.2.1, h.2.2.1⟩, ⟨T.2.2.2, h.2.2.2⟩)
      invFun := fun Q =>
        ⟨(fourBlockEquiv F m).symm (Q.1.1, Q.2.1.1, Q.2.2.1.1, Q.2.2.2.1), by
          rw [mem_alternatingSharpCode_iff_blocks, LinearEquiv.apply_symm_apply]
          exact ⟨Q.1.2, Q.2.1.2, Q.2.2.1.2, Q.2.2.2.2⟩⟩
      left_inv := fun X => by
        ext r c
        exact congrFun (congrFun ((fourBlockEquiv F m).symm_apply_apply X.1) r) c
      right_inv := fun Q => by
        rcases Q with ⟨B, A, C, D⟩
        have h := (fourBlockEquiv F m).apply_symm_apply (B.1, A.1, C.1, D.1)
        ext i j <;> simp [h]
      map_add' := fun X Y => by
        ext i j <;> rfl
      map_smul' := fun a X => by
        ext i j <;> rfl }
  rw [LinearEquiv.finrank_eq equivCode]
  rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_prod]
  rw [LinearEquiv.finrank_eq (shiftedSymEquivSym F m)]
  rw [finrank_symMatrixSubmodule]
  have heven : 2 ∣ m * (m + 1) := by
    rcases Nat.even_or_odd m with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · exact ⟨k * (2 * k + 1), by ring⟩
    · exact ⟨(2 * k + 1) * (k + 1), by ring⟩
  obtain ⟨t, ht⟩ := heven
  rw [ht, Nat.mul_div_cancel_left _ (by omega)]
  linarith

private lemma finrank_alternatingSharpCode_inf_rot_one (F : Type*) [Field F] (m : ℕ) [NeZero m] :
    finrank F ↥(alternatingSharpCode F m ⊓
      (alternatingSharpCode F m).comap (SwapRigidity.rot 1)) = m ^ 2 + 3 * m := by
  have h1 : ∀ j : ZMod m, (twoMulZMod m j + 1) + 1 = twoMulZMod m (j + 1) := by
    intro j
    rw [twoMulZMod_add, twoMulZMod_one]
    ring
  have hmem_inf : ∀ X : Matrix (ZMod (2 * m)) (ZMod (2 * m)) F,
      X ∈ alternatingSharpCode F m ⊓
        (alternatingSharpCode F m).comap (SwapRigidity.rot 1) ↔
        let T := fourBlockEquiv F m X
        T.1 ∈ symMatrixSubmodule F m ∧
        T.2.1 ∈ hankelMatrixSubmodule F m ∧
        T.2.2.1 ∈ symMatrixSubmodule F m ∧
        T.2.2.2 ∈ hankelMatrixSubmodule F m := by
    intro X
    rw [Submodule.mem_inf, Submodule.mem_comap,
      mem_alternatingSharpCode_iff_blocks X,
      mem_alternatingSharpCode_iff_blocks (SwapRigidity.rot 1 X)]
    have hrotB : (fourBlockEquiv F m (SwapRigidity.rot 1 X)).1 = (fourBlockEquiv F m X).2.1 := by
      ext i j; rfl
    have hrotA : (fourBlockEquiv F m (SwapRigidity.rot 1 X)).2.1 =
        Matrix.of (fun i j => (fourBlockEquiv F m X).1 i (j + 1)) := by
      ext i j
      simp [fourBlockEquiv, SwapRigidity.rot_apply, h1]
    have hrotC : (fourBlockEquiv F m (SwapRigidity.rot 1 X)).2.2.1 =
        (fourBlockEquiv F m X).2.2.2 := by
      ext i j; rfl
    have hrotD : (fourBlockEquiv F m (SwapRigidity.rot 1 X)).2.2.2 =
        Matrix.of (fun i j => (fourBlockEquiv F m X).2.2.1 i (j + 1)) := by
      ext i j
      simp [fourBlockEquiv, SwapRigidity.rot_apply, h1]
    rw [hrotB, hrotA, hrotC, hrotD]
    constructor
    · rintro ⟨⟨hB, hA2, hC, hD2⟩, ⟨hA1, _, hD1, _⟩⟩
      exact ⟨hB, ⟨hA1, hA2⟩, hC, ⟨hD1, hD2⟩⟩
    · rintro ⟨hB, ⟨hA1, hA2⟩, hC, ⟨hD1, hD2⟩⟩
      refine ⟨⟨hB, hA2, hC, hD2⟩, ⟨hA1, ?_, hD1, ?_⟩⟩
      · intro i j
        simp only [Matrix.of_apply, sub_add_cancel]
        exact hB i (j + 1)
      · intro i j
        simp only [Matrix.of_apply, sub_add_cancel]
        exact hC i (j + 1)
  let P :=
    symMatrixSubmodule F m ×
      hankelMatrixSubmodule F m ×
      symMatrixSubmodule F m ×
      hankelMatrixSubmodule F m
  let equivInf :
      ↥(alternatingSharpCode F m ⊓
        (alternatingSharpCode F m).comap (SwapRigidity.rot 1)) ≃ₗ[F] P :=
    { toFun := fun X =>
        let T := fourBlockEquiv F m X.1
        have h := (hmem_inf X.1).mp X.2
        (⟨T.1, h.1⟩, ⟨T.2.1, h.2.1⟩, ⟨T.2.2.1, h.2.2.1⟩, ⟨T.2.2.2, h.2.2.2⟩)
      invFun := fun Q =>
        ⟨(fourBlockEquiv F m).symm (Q.1.1, Q.2.1.1, Q.2.2.1.1, Q.2.2.2.1), by
          rw [hmem_inf, LinearEquiv.apply_symm_apply]
          exact ⟨Q.1.2, Q.2.1.2, Q.2.2.1.2, Q.2.2.2.2⟩⟩
      left_inv := fun X => by
        ext r c
        exact congrFun (congrFun ((fourBlockEquiv F m).symm_apply_apply X.1) r) c
      right_inv := fun Q => by
        rcases Q with ⟨B, A, C, D⟩
        have h := (fourBlockEquiv F m).apply_symm_apply (B.1, A.1, C.1, D.1)
        ext i j <;> simp [h]
      map_add' := fun X Y => by
        ext i j <;> rfl
      map_smul' := fun a X => by
        ext i j <;> rfl }
  rw [LinearEquiv.finrank_eq equivInf]
  rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_prod]
  rw [finrank_symMatrixSubmodule, finrank_hankelMatrixSubmodule]
  have heven : 2 ∣ m * (m + 1) := by
    rcases Nat.even_or_odd m with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · exact ⟨k * (2 * k + 1), by ring⟩
    · exact ⟨(2 * k + 1) * (k + 1), by ring⟩
  obtain ⟨t, ht⟩ := heven
  rw [ht, Nat.mul_div_cancel_left _ (by omega)]
  nlinarith

/-- Proof of `Extension_Theorem1A_AlternatingSharpnessSpec`. -/
theorem extension_Theorem1A_AlternatingSharpness :
    Extension_Theorem1A_AlternatingSharpnessSpec := by
  intro m _
  have : NeZero (2 * m) := ⟨Nat.mul_ne_zero (by decide) (NeZero.ne m)⟩
  have hg : shiftGcd (2 * m) (1 : ZMod (2 * m)) = 1 := by
    unfold shiftGcd
    rw [val_one_two_mul, Nat.gcd_one_right]
  have hn : shiftOrbitLen (2 * m) (1 : ZMod (2 * m)) = 2 * m := by
    unfold shiftOrbitLen
    rw [hg, Nat.div_one]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · unfold theorem1ASingleShiftBound
    have horb : ∀ a : Fin (shiftGcd (2 * m) (1 : ZMod (2 * m))),
        shiftOrbit (1 : ZMod (2 * m)) a = Finset.univ := by
      intro a
      ext c
      simp only [shiftOrbit, Finset.mem_filter, Finset.mem_univ, true_and]
      have ha : a.val = 0 := Nat.lt_one_iff.mp (hg ▸ a.isLt)
      have hmod : c.val % shiftGcd (2 * m) (1 : ZMod (2 * m)) = 0 := by
        rw [hg, Nat.mod_one]
      rw [hmod, ha]
      simp
    have hflip : ∀ c : ZMod (2 * m),
        altTwoColoring m (c + 1) ≠ altTwoColoring m c := by
      intro c heq
      have hval := congrArg Fin.val heq
      simp only [altTwoColoring] at hval
      rw [zmod_two_mul_val_add_mod_two, val_one_two_mul] at hval
      omega
    have hcard : ∀ (a : Fin (shiftGcd (2 * m) (1 : ZMod (2 * m)))) (k : Fin 2),
        orbitClassCard (altTwoColoring m) 1 k a = m := by
      intro a k
      unfold orbitClassCard
      rw [horb a]
      exact card_altTwoColoring_eq m k
    have hrun : ∀ (a : Fin (shiftGcd (2 * m) (1 : ZMod (2 * m)))) (k : Fin 2),
        orbitRunCount (altTwoColoring m) 1 k a = m := by
      intro a k
      unfold orbitRunCount
      rw [horb a]
      have hfilter :
          (Finset.univ.filter fun c : ZMod (2 * m) =>
            altTwoColoring m c = k ∧ altTwoColoring m (c + 1) ≠ k) =
          (Finset.univ.filter fun c : ZMod (2 * m) => altTwoColoring m c = k) := by
        ext c
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_left_iff_imp]
        intro hck
        rw [← hck]
        exact hflip c
      rw [hfilter]
      exact card_altTwoColoring_eq m k
    have hsum_a :
        (∑ a : Fin (shiftGcd (2 * m) (1 : ZMod (2 * m))),
          ∑ k : Fin 2,
            ((orbitRunCount (altTwoColoring m) 1 k a : ℝ) *
                ((shiftOrbitLen (2 * m) (1 : ZMod (2 * m)) : ℝ) -
                  (orbitClassCard (altTwoColoring m) 1 k a : ℝ)) -
              (1 / 2 : ℝ) * (orbitRunCount (altTwoColoring m) 1 k a : ℝ) ^ 2 +
              (1 / 2 : ℝ) * (orbitRunCount (altTwoColoring m) 1 k a : ℝ))) =
          (m : ℝ) ^ 2 + (m : ℝ) := by
      have hcard_g : Fintype.card (Fin (shiftGcd (2 * m) (1 : ZMod (2 * m)))) = 1 := by
        rw [Fintype.card_fin, hg]
      have hconst : ∀ a : Fin (shiftGcd (2 * m) (1 : ZMod (2 * m))),
          (∑ k : Fin 2,
            ((orbitRunCount (altTwoColoring m) 1 k a : ℝ) *
                ((shiftOrbitLen (2 * m) (1 : ZMod (2 * m)) : ℝ) -
                  (orbitClassCard (altTwoColoring m) 1 k a : ℝ)) -
              (1 / 2 : ℝ) * (orbitRunCount (altTwoColoring m) 1 k a : ℝ) ^ 2 +
              (1 / 2 : ℝ) * (orbitRunCount (altTwoColoring m) 1 k a : ℝ))) =
            (m : ℝ) ^ 2 + (m : ℝ) := by
        intro a
        rw [Fin.sum_univ_two, hrun a 0, hrun a 1, hcard a 0, hcard a 1, hn]
        push_cast
        ring
      simp_rw [hconst, Finset.sum_const, Finset.card_univ, hcard_g, one_smul]
    dsimp only
    rw [hsum_a, hg]
    push_cast
    ring
  · push_cast
    ring
  · intro F _
    refine ⟨?_, ?_, finrank_alternatingSharpCode F m,
      finrank_alternatingSharpCode_inf_rot_one F m⟩
    · have htop : ShiftLinkCovarianceSpace F (2 * m) 1 (altTwoColoring m) 1 = ⊤ := by
        ext X
        simp only [Submodule.mem_top, iff_true]
        intro c c' δ δ' hδ hδ' hp hc j
        have hpar_eq : (c + δ).val % 2 = (c' + δ').val % 2 := by rw [hc]
        rw [zmod_two_mul_val_add_mod_two, zmod_two_mul_val_add_mod_two] at hpar_eq
        have hcp : c.val % 2 = c'.val % 2 := congrArg Fin.val hp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hδ hδ'
        have hδ_eq : δ = δ' := by
          rcases hδ with rfl | rfl <;> rcases hδ' with rfl | rfl
          · rfl
          · exfalso
            rw [ZMod.val_zero, val_one_two_mul] at hpar_eq
            omega
          · exfalso
            rw [ZMod.val_zero, val_one_two_mul] at hpar_eq
            omega
          · rfl
        subst hδ_eq
        have hc_eq : c = c' := add_right_cancel hc
        subst hc_eq
        rfl
      rw [htop, finrank_top]
      rw [LinearEquiv.finrank_eq (laneOneMatrixEquiv F (2 * m))]
      rw [SwapRigidity.finrank_matrix_zmod]
      ring
    · exact ⟨alternatingSharpDecoder F m, fun X hX c => hX c⟩

/-- Direct unpacked sharpness theorem for `Theorem 1A`: on `ZMod (2 * m)` with alternating
coloring `altTwoColoring m`, `alternatingSharpCode F m` is a linear class-uniform code of
dimension `2 m (m + 1)` attaining `dim(𝒳 ∩ σ⁻¹ 𝒳) = m^2 + 3m = theorem1ASingleShiftBound`,
while the nonlinear covariance space `H_{0, 1}` has full dimension `(2m)^2`. -/
theorem alternatingSharpCode_finrank_and_shift_inf (F : Type*) [Field F] (m : ℕ) [NeZero m] :
    haveI : NeZero (2 * m) := ⟨Nat.mul_ne_zero (by decide) (NeZero.ne m)⟩
    theorem1ASingleShiftBound 1 (altTwoColoring m) (1 : ZMod (2 * m)) = (m ^ 2 + 3 * m : ℝ) ∧
    finrank F (ShiftLinkCovarianceSpace F (2 * m) 1 (altTwoColoring m) 1) = (2 * m) ^ 2 ∧
    SwapRigidity.IsClassUniformCode (altTwoColoring m) (alternatingSharpCode F m) ∧
    finrank F (alternatingSharpCode F m) = 2 * m * (m + 1) ∧
    finrank F ↥(alternatingSharpCode F m ⊓
      (alternatingSharpCode F m).comap (SwapRigidity.rot 1)) = m ^ 2 + 3 * m := by
  have h := extension_Theorem1A_AlternatingSharpness m
  exact ⟨h.1.1, (h.2 F).1, (h.2 F).2.1, (h.2 F).2.2.1, (h.2 F).2.2.2⟩

end AlternatingSharpness

end BoundedArityDecoders
