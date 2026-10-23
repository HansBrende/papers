import TransposeFollowup.ExpanderShear
import TransposeFollowup.ExpanderCutCount

/-! Balanced cuts of the binary shear are counted from actual vertex
expansion. No rank or entropy lower bound is a premise. -/

namespace TransposeFollowup.ExpanderShear

open Classical
open scoped BigOperators
set_option autoImplicit false

noncomputable def supportRect {V F : Type*} [Fintype V] [Zero F]
    (M : Matrix V V F) (J K : Finset V) : Finset (V × V) :=
  Finset.univ.filter (fun p => p.1 ∈ J ∧ p.2 ∈ K ∧ M p.1 p.2 ≠ 0)

@[simp] theorem mem_supportRect {V F : Type*} [Fintype V] [Zero F]
    (M : Matrix V V F) (J K : Finset V) (p : V × V) :
    p ∈ supportRect M J K ↔ p.1 ∈ J ∧ p.2 ∈ K ∧ M p.1 p.2 ≠ 0 := by
  simp [supportRect]

theorem nnz_submatrix_eq_supportRect {V F : Type*} [Fintype V] [Zero F]
    (M : Matrix V V F) (J K : Finset V) :
    nnz (M.submatrix (Subtype.val : J → V) (Subtype.val : K → V)) =
      (supportRect M J K).card := by
  let e : {p : J × K // M p.1 p.2 ≠ 0} ≃
      {p : V × V // p.1 ∈ J ∧ p.2 ∈ K ∧ M p.1 p.2 ≠ 0} :=
    { toFun := fun p => ⟨(p.val.1.val, p.val.2.val),
        p.val.1.property, p.val.2.property, p.property⟩
      invFun := fun p => ⟨(⟨p.val.1, p.property.1⟩, ⟨p.val.2, p.property.2.1⟩),
        p.property.2.2⟩
      left_inv := by intro p; rfl
      right_inv := by intro p; rfl }
  have h := Fintype.card_congr e
  simp only [nnz, supportRect, Matrix.submatrix_apply, Fintype.card_subtype] at h ⊢
  convert h using 2
  congr 1

noncomputable def crossSupport {V F : Type*} [Fintype V] [DecidableEq V] [Zero F]
    (M : Matrix V V F) (I J : Finset V) : Finset (V × V) :=
  supportRect M J Iᶜ ∪ supportRect M Jᶜ I

@[simp] theorem mem_crossSupport {V F : Type*} [Fintype V] [DecidableEq V] [Zero F]
    (M : Matrix V V F) (I J : Finset V) (p : V × V) :
    p ∈ crossSupport M I J ↔
      (p.1 ∈ J ∧ p.2 ∉ I ∧ M p.1 p.2 ≠ 0) ∨
      (p.1 ∉ J ∧ p.2 ∈ I ∧ M p.1 p.2 ≠ 0) := by
  simp [crossSupport]

theorem card_crossSupport {V F : Type*} [Fintype V] [DecidableEq V] [Zero F]
    (M : Matrix V V F) (I J : Finset V) :
    (crossSupport M I J).card = nnz (crossMatrix M J I) + nnz (crossMatrix M Jᶜ Iᶜ) := by
  have hd : Disjoint (supportRect M J Iᶜ) (supportRect M Jᶜ I) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    exact (Finset.mem_compl.mp ((mem_supportRect M Jᶜ I p).mp hq).1)
      ((mem_supportRect M J Iᶜ p).mp hp).1
  simp only [crossMatrix, nnz_submatrix_eq_supportRect, compl_compl, crossSupport]
  exact Finset.card_union_of_disjoint hd

noncomputable def mismatch {V : Type*} [DecidableEq V] (I J : Finset V) : Finset V :=
  (I \ J) ∪ (J \ I)

@[simp] theorem mem_mismatch {V : Type*} [DecidableEq V]
    (I J : Finset V) (v : V) :
    v ∈ mismatch I J ↔ (v ∈ I ∧ v ∉ J) ∨ (v ∈ J ∧ v ∉ I) := by
  simp [mismatch]

theorem card_le_add_mismatch {V : Type*} [DecidableEq V] (I J : Finset V) :
    I.card ≤ J.card + (mismatch I J).card := by
  have hs : I ⊆ J ∪ mismatch I J := by
    intro v hv
    by_cases hj : v ∈ J
    · exact Finset.mem_union_left _ hj
    · exact Finset.mem_union_right _ ((mem_mismatch I J v).mpr (Or.inl ⟨hv, hj⟩))
  exact (Finset.card_le_card hs).trans (Finset.card_union_le _ _)

theorem diagonal_mismatch_image_subset {V F : Type*} [Fintype V] [DecidableEq V]
    [Zero F] (M : Matrix V V F) (hdiag : ∀ v, M v v ≠ 0) (I J : Finset V) :
    (mismatch I J).image (fun v => (v, v)) ⊆ crossSupport M I J := by
  intro p hp
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hp
  rcases (mem_mismatch I J v).mp hv with h | h
  · exact (mem_crossSupport M I J _).mpr (Or.inr ⟨h.2, h.1, hdiag v⟩)
  · exact (mem_crossSupport M I J _).mpr (Or.inl ⟨h.1, h.2, hdiag v⟩)

theorem diagonal_mismatch_le_crossSupport {V F : Type*} [Fintype V] [DecidableEq V]
    [Zero F] (M : Matrix V V F) (hdiag : ∀ v, M v v ≠ 0) (I J : Finset V) :
    (mismatch I J).card ≤ (crossSupport M I J).card := by
  simpa only [Finset.card_image_of_injective _
    (show Function.Injective (fun v : V => (v, v)) from fun _ _ h => congrArg Prod.fst h)]
    using Finset.card_le_card (diagonal_mismatch_image_subset M hdiag I J)

noncomputable def coreSelected {V : Type*} [DecidableEq V]
    (left I J : Finset V) : Finset V := (I ∩ left) ∪ (J \ left)

theorem coreSelected_card_sum {V : Type*} [DecidableEq V]
    (left I J : Finset V) :
    (coreSelected left I J).card + (coreSelected left J I).card = I.card + J.card := by
  have hI := Finset.card_sdiff_add_card_inter I left
  have hJ := Finset.card_sdiff_add_card_inter J left
  have hd (A B : Finset V) : Disjoint (A ∩ left) (B \ left) := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    exact (Finset.mem_sdiff.mp hw).2 (Finset.mem_inter.mp hv).2
  simp only [coreSelected, Finset.card_union_of_disjoint (hd _ _)]
  omega

theorem coreSelected_mismatch {V : Type*} [DecidableEq V]
    (left I J : Finset V) :
    mismatch (coreSelected left I J) (coreSelected left J I) = mismatch I J := by
  ext v
  by_cases hl : v ∈ left <;> by_cases hi : v ∈ I <;> by_cases hj : v ∈ J <;>
    simp [coreSelected, hl, hi, hj]

noncomputable def leftRows (m : ℕ) : Finset (Row m) :=
  Finset.univ.filter (fun v => v.isLeft)

@[simp] theorem inl_mem_coreSelected {m : ℕ} (I J : Finset (Row m)) (i : Fin m) :
    Sum.inl i ∈ coreSelected (leftRows m) I J ↔ Sum.inl i ∈ I := by
  simp [coreSelected, leftRows]

@[simp] theorem inr_mem_coreSelected {m : ℕ} (I J : Finset (Row m)) (j : Fin m) :
    Sum.inr j ∈ coreSelected (leftRows m) I J ↔ Sum.inr j ∈ J := by
  simp [coreSelected, leftRows]

noncomputable def coreCross {m : ℕ} (L : Matrix (Fin m) (Fin m) Bit)
    (C : Finset (Row m)) : Finset (Fin m × Fin m) :=
  Finset.univ.filter (fun p => L p.2 p.1 ≠ 0 ∧
    ((Sum.inl p.1 ∈ C ∧ Sum.inr p.2 ∉ C) ∨
      (Sum.inl p.1 ∉ C ∧ Sum.inr p.2 ∈ C)))

theorem coreCross_compl {m : ℕ} (L : Matrix (Fin m) (Fin m) Bit)
    (C : Finset (Row m)) : coreCross L Cᶜ = coreCross L C := by
  ext p
  by_cases hi : Sum.inl p.1 ∈ C <;> by_cases hj : Sum.inr p.2 ∈ C <;>
    simp [coreCross, hi, hj]

theorem outsideNeighbors_core_le {m : ℕ} (L : Matrix (Fin m) (Fin m) Bit)
    (C : Finset (Row m)) :
    (outsideNeighbors (coreGraph L) C).card ≤ (coreCross L C).card := by
  let outside : Fin m × Fin m → Row m :=
    fun p => if Sum.inl p.1 ∈ C then Sum.inr p.2 else Sum.inl p.1
  have hs : outsideNeighbors (coreGraph L) C ⊆ (coreCross L C).image outside := by
    intro v hv
    obtain ⟨⟨u, hu, huv⟩, hv⟩ := Finset.mem_sdiff.mp hv
      |>.imp_left Finset.mem_biUnion.mp
    have ha := ((coreGraph L).mem_neighborFinset u v).mp huv
    cases u with
    | inl i =>
      cases v with
      | inl j => exact False.elim ha
      | inr j =>
        apply Finset.mem_image.mpr
        refine ⟨(i,j), ?_, ?_⟩
        · simp only [coreCross, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨ha, Or.inl ⟨hu,hv⟩⟩
        · simp [outside, hu]
    | inr j =>
      cases v with
      | inr i => exact False.elim ha
      | inl i =>
        apply Finset.mem_image.mpr
        refine ⟨(i,j), ?_, ?_⟩
        · simp only [coreCross, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨ha, Or.inr ⟨hv,hu⟩⟩
        · simp [outside, hv]
  exact (Finset.card_le_card hs).trans (Finset.card_image_le)

/-- Diagonal mismatches and crossing core edges occupy disjoint matrix entries. -/
theorem mismatch_add_coreCross_le {m : ℕ} (L : Matrix (Fin m) (Fin m) Bit)
    (I J : Finset (Row m)) :
    (mismatch I J).card + (coreCross L (coreSelected (leftRows m) I J)).card ≤
      (crossSupport (matrix L) I J).card := by
  let f : Row m → Row m × Row m := fun v => (v, v)
  let g : Fin m × Fin m → Row m × Row m := fun p => (Sum.inr p.2, Sum.inl p.1)
  have hf : Function.Injective f := fun _ _ h => congrArg Prod.fst h
  have hg : Function.Injective g := fun _ _ h =>
    Prod.ext (Sum.inl.inj (congrArg Prod.snd h)) (Sum.inr.inj (congrArg Prod.fst h))
  have hd : Disjoint ((mismatch I J).image f)
      ((coreCross L (coreSelected (leftRows m) I J)).image g) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨e, _, he⟩ := Finset.mem_image.mp hq
    have hfst := congrArg Prod.fst he
    have hsnd := congrArg Prod.snd he
    have hbad : (Sum.inr e.2 : Row m) = Sum.inl e.1 := hfst.trans hsnd.symm
    cases hbad
  have hs : (mismatch I J).image f ∪
      (coreCross L (coreSelected (leftRows m) I J)).image g ⊆
        crossSupport (matrix L) I J := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hp
      exact diagonal_mismatch_image_subset (matrix L) (by
        intro v; cases v <;> simp [matrix]) I J (Finset.mem_image.mpr ⟨v, hv, rfl⟩)
    · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hp
      have h := (Finset.mem_filter.mp he).2
      simp only [inl_mem_coreSelected, inr_mem_coreSelected] at h
      rcases h.2 with hside | hside
      · exact (mem_crossSupport _ I J _).mpr (Or.inr ⟨hside.2, hside.1, h.1⟩)
      · exact (mem_crossSupport _ I J _).mpr (Or.inl ⟨hside.2, hside.1, h.1⟩)
  simpa only [Finset.card_union_of_disjoint hd, Finset.card_image_of_injective _ hf,
    Finset.card_image_of_injective _ hg] using Finset.card_le_card hs

theorem coreCross_le_crossSupport {m : ℕ} (L : Matrix (Fin m) (Fin m) Bit)
    (I J : Finset (Row m)) :
    (coreCross L (coreSelected (leftRows m) I J)).card ≤
      (crossSupport (matrix L) I J).card := by
  exact (Nat.le_add_left _ _).trans (mismatch_add_coreCross_le L I J)

/-- The disjoint diagonal/core count retains the sharper factor two. -/
theorem balanced_cross_nnz_sharp {m : ℕ} (L : Matrix (Fin m) (Fin m) Bit)
    (eta : ℝ) (heta0 : 0 ≤ eta) (heta2 : eta ≤ 2)
    (hexp : ∀ S : Finset (Row m), 2 * S.card ≤ 2 * m →
      eta * S.card ≤ (outsideNeighbors (coreGraph L) S).card)
    (I J : Finset (Row m)) (hI : I.card = m) (hJ : J.card = m) :
    eta * (2 * m) ≤ 2 * ((nnz (crossMatrix (matrix L) J I) +
      nnz (crossMatrix (matrix L) Jᶜ Iᶜ) : ℕ) : ℝ) := by
  let C := coreSelected (leftRows m) I J
  let D := coreSelected (leftRows m) J I
  let E := (mismatch C D).card
  let F := (coreCross L C).card
  have hsum : C.card + D.card = 2 * m := by
    dsimp [C, D]
    rw [coreSelected_card_sum, hI, hJ]
    omega
  have hCD : C.card ≤ D.card + E := card_le_add_mismatch C D
  have hDC : D.card ≤ C.card + E := by
    have hs : mismatch D C = mismatch C D := Finset.union_comm _ _
    simpa only [hs] using card_le_add_mismatch D C
  have hnear : (outsideNeighbors (coreGraph L) C).card ≤ F := outsideNeighbors_core_le L C
  have hfar : (outsideNeighbors (coreGraph L) Cᶜ).card ≤ F := by
    simpa only [coreCross_compl] using outsideNeighbors_core_le L Cᶜ
  have hcompl : Cᶜ.card = D.card := by
    have hc := Finset.card_add_card_compl C
    have hn : Fintype.card (Row m) = 2 * m := by simp [Row]; omega
    rw [hn] at hc
    omega
  have hcount : E + F ≤ (crossSupport (matrix L) I J).card := by
    dsimp only [E, F, C, D]
    rw [coreSelected_mismatch]
    exact mismatch_add_coreCross_le L I J
  have hgoal : eta * (2 * m) ≤ 2 * ((E : ℝ) + F) := by
    have hEmul := mul_le_mul_of_nonneg_right heta2 (Nat.cast_nonneg E : (0 : ℝ) ≤ E)
    by_cases hsmall : 2 * C.card ≤ 2 * m
    · have he : eta * C.card ≤ (F : ℝ) :=
        (hexp C hsmall).trans (by exact_mod_cast hnear)
      have hnum : 2 * m ≤ 2 * C.card + E := by omega
      have hnumR : (2 : ℝ) * m ≤ 2 * C.card + E := by exact_mod_cast hnum
      have hmul := mul_le_mul_of_nonneg_left hnumR heta0
      nlinarith
    · have hsmall' : 2 * Cᶜ.card ≤ 2 * m := by rw [hcompl]; omega
      have he : eta * Cᶜ.card ≤ (F : ℝ) :=
        (hexp Cᶜ hsmall').trans (by exact_mod_cast hfar)
      have hnum : 2 * m ≤ 2 * Cᶜ.card + E := by rw [hcompl]; omega
      have hnumR : (2 : ℝ) * m ≤ 2 * Cᶜ.card + E := by exact_mod_cast hnum
      have hmul := mul_le_mul_of_nonneg_left hnumR heta0
      nlinarith
  have hcountR : (E : ℝ) + F ≤ (crossSupport (matrix L) I J).card := by exact_mod_cast hcount
  rw [card_crossSupport] at hcountR
  push_cast at hcountR ⊢
  linarith

/-- Vertex expansion forces many nonzero entries across every balanced input/output
partition of the shear.  The two selected halves need not coincide. -/
theorem balanced_cross_nnz {m : ℕ} (L : Matrix (Fin m) (Fin m) Bit)
    (eta : ℝ) (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hexp : ∀ S : Finset (Row m), 2 * S.card ≤ 2 * m →
      eta * S.card ≤ (outsideNeighbors (coreGraph L) S).card)
    (I J : Finset (Row m)) (hI : I.card = m) (hJ : J.card = m) :
    eta * (2 * m) ≤ 4 * ((nnz (crossMatrix (matrix L) J I) +
      nnz (crossMatrix (matrix L) Jᶜ Iᶜ) : ℕ) : ℝ) := by
  have h := balanced_cross_nnz_sharp L eta heta0 (by linarith) hexp I J hI hJ
  have hn : (0 : ℝ) ≤ ((nnz (crossMatrix (matrix L) J I) +
      nnz (crossMatrix (matrix L) Jᶜ Iᶜ) : ℕ) : ℝ) := Nat.cast_nonneg _
  linarith

end TransposeFollowup.ExpanderShear
