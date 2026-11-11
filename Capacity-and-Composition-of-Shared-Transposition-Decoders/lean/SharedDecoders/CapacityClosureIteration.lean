import SharedDecoders.CapacityClosureSpace

/-! Actual nested hull intersections, with the defect charged only where used. -/

namespace SharedDecoders.CapacityClosure

open Module CapacityIntervals CapacityRuns

variable {d b : ℕ} [NeZero d] {κ : Type*}

abbrev rotationEquiv (s : ZMod d) : BinaryState d b ≃ₗ[Bit] BinaryState d b :=
  rotLinearEquiv Bit s

omit [NeZero d] in
@[simp] theorem rotationEquiv_toLinearMap (s : ZMod d) :
    (rotationEquiv (b := b) s).toLinearMap = rotLinear Bit s := rfl

omit [NeZero d] in
theorem rowSpace_comap_rotation (S : Finset (ZMod d)) (s : ZMod d) :
    (rowSpace S (b := b)).comap (rotationEquiv s).toLinearMap = rowSpace S := by
  ext X
  constructor
  · intro hX
    change rot s X ∈ rowSpace S at hX
    simpa only [rot_neg_rot] using rowSpace_rot hX (-s)
  · exact fun hX => rowSpace_rot hX s

noncomputable def defect (L : Submodule Bit (BinaryState d b)) : ℕ :=
  finrank Bit (scalarHull L) - finrank Bit L

theorem hull_dimension (L : Submodule Bit (BinaryState d b)) :
    finrank Bit (scalarHull L) = finrank Bit L + defect L := by
  have h := Submodule.finrank_mono (le_scalarHull L)
  dsimp [defect]
  omega

omit [NeZero d] in
theorem commonPreimage_mono {L H : Submodule Bit (BinaryState d b)} (hLH : L ≤ H)
    (Δ : Finset (ZMod d)) : commonPreimage L Δ ≤ commonPreimage H Δ := by
  intro X hX
  rw [mem_commonPreimage] at hX ⊢
  exact fun s hs => hLH (hX s hs)

theorem commonPreimage_hull_defect (L : Submodule Bit (BinaryState d b))
    (Δ : Finset (ZMod d)) :
    finrank Bit (commonPreimage (scalarHull L) Δ) ≤
      finrank Bit (commonPreimage L Δ) + Δ.card * defect L := by
  have h := finrank_finite_inf_defect Δ
    (fun s => L.comap (rotLinear Bit s))
    (fun s => (scalarHull L).comap (rotLinear Bit s))
    (by intro s _ X hX; exact le_scalarHull L hX)
  have he (W : Submodule Bit (BinaryState d b)) (s : ZMod d) :
      finrank Bit (W.comap (rotLinear Bit s)) = finrank Bit W :=
    finrank_comap_equiv W (rotationEquiv s)
  change finrank Bit (commonPreimage (scalarHull L) Δ) ≤
    finrank Bit (commonPreimage L Δ) + ∑ s ∈ Δ,
      (finrank Bit ((scalarHull L).comap (rotLinear Bit s)) -
       finrank Bit (L.comap (rotLinear Bit s))) at h
  simpa only [he, Finset.sum_const, smul_eq_mul, defect] using h

noncomputable def isolatedRows (p : ZMod d → κ) (Δ S : Finset (ZMod d)) : Finset (ZMod d) := by
  classical
  exact S.filter (IsIsolated p Δ)

theorem isolatedRows_card_le (p : ZMod d → κ) (Δ S : Finset (ZMod d)) :
    (isolatedRows p Δ S).card ≤ isolatedCount p Δ := by
  classical
  rw [isolatedCount, Fintype.card_subtype]
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))

theorem two_scalar_support (p : ZMod d → κ) (Δ S : Finset (ZMod d)) :
    rowSpace S (b := b) ⊓ covarianceSpace p Δ ⊓
      (covarianceSpace p Δ).comap (scalarEquiv (normalElement d) normalElement_ne_zero).toLinearMap ≤
        rowSpace (isolatedRows p Δ S) := by
  classical
  intro X hX c hc
  by_cases hS : c ∈ S
  · have hn : ¬IsIsolated p Δ c := by
      intro hi
      exact hc (Finset.mem_filter.mpr ⟨hS, hi⟩)
    obtain ⟨e, he⟩ := not_forall.mp hn
    obtain ⟨hce, hne⟩ := not_imp.mp he
    exact (two_scalar_covariance_zero hX.1.2 hX.2 hce (Ne.symm hne)).1
  · exact hX.1.1 c hS

omit [NeZero d] in
theorem commonPreimage_le_rows {H : Submodule Bit (BinaryState d b)}
    {S Δ : Finset (ZMod d)} (hH : H ≤ rowSpace S) (hzero : 0 ∈ Δ) :
    commonPreimage H Δ ≤ rowSpace S := by
  intro X hX
  exact hH (by simpa using (mem_commonPreimage.mp hX) 0 hzero)

/-- The dimension outside the actual isolated support is charged by two joint
covariance observations, without assuming the hull itself is a correct code. -/
theorem hull_projection_bound {p : ZMod d → κ} {L : Submodule Bit (BinaryState d b)}
    (hL : IsSharedCode Bit p L) {S : Finset (ZMod d)} (hs : L ≤ rowSpace S)
    (Δ : Finset (ZMod d)) (hzero : 0 ∈ Δ) :
    finrank Bit (commonPreimage (scalarHull L) Δ) ≤
      finrank Bit (commonPreimage (scalarHull L) Δ ⊓
        rowSpace (isolatedRows p Δ S) : Submodule Bit (BinaryState d b)) +
        2 * Δ.card * defect L := by
  let H := commonPreimage (scalarHull L) Δ
  let K := covarianceSpace (F := Bit) (A := Fin b → Bit) p Δ
  let I := rowSpace (isolatedRows p Δ S) (b := b)
  have hrows : H ≤ rowSpace S := commonPreimage_le_rows (scalarHull_le_rowSpace hs) hzero
  have hstab := (scalarHull_stable L).commonPreimage Δ
  have hsupport : H ⊓ K ⊓ K.comap
      (scalarEquiv (normalElement d) normalElement_ne_zero).toLinearMap ≤ I := by
    exact (inf_le_inf (inf_le_inf hrows le_rfl) le_rfl).trans (two_scalar_support p Δ S)
  have hproj := finrank_double_kernel_support H K I
    (scalarEquiv (normalElement d) normalElement_ne_zero)
    (hstab.comap_scalarEquiv _ _) hsupport
  have hgood : commonPreimage L Δ ≤ H ⊓ K :=
    le_inf (commonPreimage_mono (le_scalarHull L) Δ) (hL.commonPreimage_le_covariance Δ)
  have hdim := Submodule.finrank_mono hgood
  have hdef := commonPreimage_hull_defect L Δ
  have hHK := Submodule.finrank_mono (inf_le_left : H ⊓ K ≤ H)
  change finrank Bit H ≤ finrank Bit (H ⊓ I : Submodule Bit (BinaryState d b)) + _
  change finrank Bit H ≤ finrank Bit (commonPreimage L Δ) + _ at hdef
  dsimp only [H, K, I] at *
  have hdefect : finrank Bit (commonPreimage (scalarHull L) Δ) -
      finrank Bit (commonPreimage (scalarHull L) Δ ⊓ covarianceSpace p Δ :
        Submodule Bit (BinaryState d b)) ≤ Δ.card * defect L := by
    apply Nat.sub_le_iff_le_add.mpr
    exact hdef.trans ((Nat.add_le_add_right hdim _).trans_eq (Nat.add_comm ..))
  nlinarith only [hproj, hdefect]

theorem hull_terminal_bound {p : ZMod d → κ} {L : Submodule Bit (BinaryState d b)}
    (hL : IsSharedCode Bit p L) {S : Finset (ZMod d)} (hs : L ≤ rowSpace S)
    (Δ : Finset (ZMod d)) (hzero : 0 ∈ Δ) :
    finrank Bit (commonPreimage (scalarHull L) Δ) ≤
      d * b * isolatedCount p Δ + 2 * Δ.card * defect L := by
  have h := hull_projection_bound hL hs Δ hzero
  have hm := Submodule.finrank_mono (inf_le_right :
    commonPreimage (scalarHull L) Δ ⊓ rowSpace (isolatedRows p Δ S) ≤ rowSpace (isolatedRows p Δ S))
  rw [finrank_rowSpace] at hm
  have hc := Nat.mul_le_mul_right (d*b) (isolatedRows_card_le p Δ S)
  nlinarith only [h, hm, hc]

theorem hull_step_bound {p : ZMod d → κ} {L : Submodule Bit (BinaryState d b)}
    (hL : IsSharedCode Bit p L) {S : Finset (ZMod d)} (hs : L ≤ rowSpace S)
    (Δ : Finset (ZMod d)) (hzero : 0 ∈ Δ) (s : ZMod d) :
    2 * finrank Bit (commonPreimage (scalarHull L) Δ) ≤
      d * b * isolatedCount p Δ +
      finrank Bit (commonPreimage (scalarHull L) (extendShifts Δ s)) +
      4 * Δ.card * defect L := by
  let H := commonPreimage (scalarHull L) Δ
  let I := rowSpace (isolatedRows p Δ S) (b := b)
  have hproj := hull_projection_bound hL hs Δ hzero
  have hsup := finrank_sup_comap_support H I (rotationEquiv s)
    (rowSpace_comap_rotation _ s)
  have hgrass := Submodule.finrank_sup_add_finrank_inf_eq H (H.comap (rotLinear Bit s))
  have he := finrank_comap_equiv H (rotationEquiv s)
  rw [rotationEquiv_toLinearMap] at he hsup
  have hI : finrank Bit I ≤ d*b*isolatedCount p Δ := by
    dsimp [I]
    rw [finrank_rowSpace]
    have hc := Nat.mul_le_mul_right (d*b) (isolatedRows_card_le p Δ S)
    nlinarith only [hc]
  rw [commonPreimage_extend]
  change 2 * finrank Bit H ≤ _ + finrank Bit (H ⊓ H.comap (rotLinear Bit s) : Submodule Bit (BinaryState d b)) + _
  change finrank Bit H ≤ finrank Bit (H ⊓ I : Submodule Bit (BinaryState d b)) + _ at hproj
  dsimp only [H, I] at *
  nlinarith only [hproj, hsup, hgrass, he, hI]

omit [NeZero d] in
theorem card_extendShifts_le (Δ : Finset (ZMod d)) (s : ZMod d) :
    (extendShifts Δ s).card ≤ 2 * Δ.card := by
  have h := Finset.card_union_le Δ (Δ.image (fun x => x+s))
  have hi := Finset.card_image_le (s := Δ) (f := fun x => x+s)
  dsimp [extendShifts]
  omega

omit [NeZero d] in
theorem zero_mem_extendShifts {Δ : Finset (ZMod d)} (h : 0 ∈ Δ) (s : ZMod d) :
    0 ∈ extendShifts Δ s := Finset.mem_union_left _ h

/-- The one- and two-stage certificates retain the subtraction of the original
hull defect. The coefficients are `rho` and `3 rho`, not `2 rho` and `4 rho`. -/
theorem residual_certificates {p : ZMod d → Bool} {L : Submodule Bit (BinaryState d b)}
    (hL : IsSharedCode Bit p L) {S : Finset (ZMod d)} (hs : L ≤ rowSpace S)
    (s : ZMod d) :
    (2 * finrank Bit L ≤ d*b*S.card +
      d*b*isolatedCount p (extendShifts {0} s) + 2*defect L) ∧
    (4 * finrank Bit L ≤ 2*(d*b*S.card) +
      d*b*isolatedCount p (extendShifts {0} s) +
      d*b*isolatedCount p (extendShifts (extendShifts {0} s) (3 • s)) + 12*defect L) := by
  let F₁ := extendShifts {0} s
  let F₂ := extendShifts F₁ (3 • s)
  have hz₁ : 0 ∈ F₁ := zero_mem_extendShifts (Finset.mem_singleton_self 0) s
  have hz₂ : 0 ∈ F₂ := zero_mem_extendShifts hz₁ _
  have hc₁ : F₁.card ≤ 2 := by simpa using card_extendShifts_le ({0} : Finset (ZMod d)) s
  have hc₂ : F₂.card ≤ 4 := by
    have hh := card_extendShifts_le F₁ (3 • s)
    dsimp only [F₂]
    omega
  have hbase : 2 * finrank Bit (scalarHull L) ≤ S.card*d*b +
      finrank Bit (commonPreimage (scalarHull L) F₁) := by
    have hh := two_mul_finrank_inf_comap_le (scalarHull L) (rowSpace S) s
      (scalarHull_le_rowSpace hs) (fun _ hx => rowSpace_rot hx _)
    rw [finrank_rowSpace] at hh
    dsimp only [F₁]
    rw [commonPreimage_extend, commonPreimage_zero]
    exact hh
  have h₁ := hull_terminal_bound hL hs F₁ hz₁
  have hstep := hull_step_bound hL hs F₁ hz₁ (3 • s)
  have h₂ := hull_terminal_bound hL hs F₂ hz₂
  have hdim := hull_dimension L
  have hc₁' := Nat.mul_le_mul_right (defect L) hc₁
  have hc₂' := Nat.mul_le_mul_right (defect L) hc₂
  dsimp only [F₁, F₂] at *
  constructor <;> nlinarith only [hbase, h₁, hstep, h₂, hdim, hc₁', hc₂']

end SharedDecoders.CapacityClosure
