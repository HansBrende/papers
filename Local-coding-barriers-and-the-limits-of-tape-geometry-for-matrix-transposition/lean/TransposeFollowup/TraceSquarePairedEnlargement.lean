import TransposeFollowup.TraceSquareSourceSample
import TransposeFollowup.CentralizerScalarSumProduct
import TransposeFollowup.MixedReadoutSourceTransfer

/-! Enlarge approximants together with their actual source words in the
product group. Products and quotients retain the same correspondence,
word-length bounds, centralizer form and a charged approximation error. -/
namespace TransposeFollowup.SL2Projection
open Classical Matrix Set RealMobius
open scoped Pointwise Matrix.Norms.Frobenius
set_option autoImplicit false
local notation "RMat" => Matrix (Fin 2) (Fin 2) ℝ
local notation "G" => RealMobius.Group

theorem paired_enlargement_first_image (P : Finset (G × G)) :
    (P ∪ P*P ∪ P*P⁻¹).image Prod.fst =
      P.image Prod.fst ∪ P.image Prod.fst*P.image Prod.fst ∪
        P.image Prod.fst*(P.image Prod.fst)⁻¹ := by
  change (P ∪ P*P ∪ P*P⁻¹).image (MonoidHom.fst G G) = _
  simp only [Finset.image_union, Finset.image_mul (MonoidHom.fst G G),
    Finset.image_inv (MonoidHom.fst G G)]
  rfl

theorem paired_source_enlargement (P : Finset (G × G)) (b : RMat)
    {A : Set G} {m : ℕ} {R ε : ℝ}
    (hA1 : 1 ∈ A) (hAi : A⁻¹=A) (hR : 1 ≤ R) (hε : 0 ≤ ε)
    (hsource : ∀ w ∈ P, w.2 ∈ A^m)
    (hform : ∀ w ∈ P, ∃ c t : ℝ, (w.1 : RMat) = scalarAffine b c t)
    (hnear : ∀ w ∈ P, dist (w.1 : RMat) 1 ≤ 1/64)
    (hbound : ∀ w ∈ P, ∀ i j, |w.1 i j| ≤ R ∧ |w.2 i j| ≤ R)
    (hclose : ∀ w ∈ P, dist (w.1 : RMat) (w.2 : RMat) ≤ ε) :
    ∀ w ∈ P ∪ P*P ∪ P*P⁻¹,
      w.2 ∈ A^(2*m) ∧
      (∃ c t : ℝ, (w.1 : RMat) = scalarAffine b c t) ∧
      dist (w.1 : RMat) 1 ≤ 1/16 ∧
      (∀ i j, |w.1 i j| ≤ 2*R^2 ∧ |w.2 i j| ≤ 2*R^2) ∧
      dist (w.1 : RMat) (w.2 : RMat) ≤ 8*R^2*ε := by
  let F := P.image Prod.fst
  have hFn : ∀ u ∈ F, dist (u : RMat) 1 ≤ 1/64 := by
    intro u hu
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hu
    exact hnear w hw
  have hEn (w : G × G) (hw : w ∈ P ∪ P*P ∪ P*P⁻¹) :
      dist (w.1 : RMat) 1 ≤ 1/16 := by
    have hh : w.1 ∈ (P ∪ P*P ∪ P*P⁻¹).image Prod.fst :=
      Finset.mem_image.mpr ⟨w, hw, rfl⟩
    rw [paired_enlargement_first_image] at hh
    exact sl2_enlargement_near_identity F hFn w.1 hh
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hRlarge : R ≤ 2*R^2 := by nlinarith only [hR]
  have herror : ε ≤ 8*R^2*ε := by
    exact le_mul_of_one_le_left hε (by nlinarith only [hR])
  have hI (i j : Fin 2) : |(1 : G) i j| ≤ R := by
    have hh : |(1 : RMat) i j| ≤ 1 := by fin_cases i <;> fin_cases j <;> norm_num
    exact hh.trans hR
  have hmul (u v : G × G)
      (huA : u.2 ∈ A^m) (hvA : v.2 ∈ A^m)
      (huF : ∃ c t : ℝ, (u.1 : RMat) = scalarAffine b c t)
      (hvF : ∃ c t : ℝ, (v.1 : RMat) = scalarAffine b c t)
      (huB : ∀ i j, |u.1 i j| ≤ R ∧ |u.2 i j| ≤ R)
      (hvB : ∀ i j, |v.1 i j| ≤ R ∧ |v.2 i j| ≤ R)
      (hue : dist (u.1 : RMat) (u.2 : RMat) ≤ ε)
      (hve : dist (v.1 : RMat) (v.2 : RMat) ≤ ε) :
      (u*v).2 ∈ A^(2*m) ∧
      (∃ c t : ℝ, ((u*v).1 : RMat) = scalarAffine b c t) ∧
      (∀ i j, |(u*v).1 i j| ≤ 2*R^2 ∧ |(u*v).2 i j| ≤ 2*R^2) ∧
      dist ((u*v).1 : RMat) ((u*v).2 : RMat) ≤ 8*R^2*ε := by
    obtain ⟨c,t,huf⟩ := huF
    obtain ⟨p,q,hvf⟩ := hvF
    refine ⟨?_, ⟨_, _, (sl2_scalarAffine_product_coordinates b u.1 v.1 huf hvf).1⟩, ?_, ?_⟩
    · change u.2*v.2 ∈ A^(2*m)
      rw [two_mul, pow_add]
      exact Set.mul_mem_mul huA hvA
    · intro i j
      exact ⟨by simpa only [Prod.fst_mul, Prod.snd_mul, pow_two, mul_assoc] using
          matrixEntryBox_mul (fun i j => (huB i j).1) (fun i j => (hvB i j).1) i j,
        by simpa only [Prod.fst_mul, Prod.snd_mul, pow_two, mul_assoc] using
          matrixEntryBox_mul (fun i j => (huB i j).2) (fun i j => (hvB i j).2) i j⟩
    · simpa only [Prod.fst_mul, Prod.snd_mul, mul_one] using (two_source_word_distances u.1 v.1 u.2 v.2 1 1
        hR0 hε (fun i j => (hvB i j).1) (fun i j => (huB i j).2) hI hI hue hve).1
  intro w hw
  have hgeom : w.2 ∈ A^(2*m) ∧
      (∃ c t : ℝ, (w.1 : RMat) = scalarAffine b c t) ∧
      (∀ i j, |w.1 i j| ≤ 2*R^2 ∧ |w.2 i j| ≤ 2*R^2) ∧
      dist (w.1 : RMat) (w.2 : RMat) ≤ 8*R^2*ε := by
    rcases Finset.mem_union.mp hw with hw | hw
    · rcases Finset.mem_union.mp hw with hw | hw
      · exact ⟨Set.pow_subset_pow_right hA1 (by omega) (hsource w hw), hform w hw,
          fun i j => ⟨(hbound w hw i j).1.trans hRlarge, (hbound w hw i j).2.trans hRlarge⟩,
          (hclose w hw).trans herror⟩
      · obtain ⟨u,hu,v,hv,rfl⟩ := Finset.mem_mul.mp hw
        exact hmul u v (hsource u hu) (hsource v hv) (hform u hu) (hform v hv)
          (hbound u hu) (hbound v hv) (hclose u hu) (hclose v hv)
    · obtain ⟨u,hu,v,hv,rfl⟩ := Finset.mem_mul.mp hw
      obtain ⟨x,hx,hxv⟩ := Finset.mem_inv.mp hv
      subst v
      have hxA : x.2⁻¹ ∈ A^m := by
        simpa only [← inv_pow, hAi] using Set.inv_mem_inv.mpr (hsource x hx)
      have hxF : ∃ c t : ℝ, ((x⁻¹).1 : RMat) = scalarAffine b c t := by
        obtain ⟨c,t,hf⟩ := hform x hx
        exact ⟨_, _, sl2_scalarAffine_inv b x.1 hf⟩
      have hxB : ∀ i j, |(x⁻¹).1 i j| ≤ R ∧ |(x⁻¹).2 i j| ≤ R := by
        intro i j
        exact ⟨matrixEntryBox_inv (fun i j => (hbound x hx i j).1) i j,
          matrixEntryBox_inv (fun i j => (hbound x hx i j).2) i j⟩
      have hxe : dist ((x⁻¹).1 : RMat) ((x⁻¹).2 : RMat) ≤ ε := by
        change dist ((x.1⁻¹ : G) : RMat) ((x.2⁻¹ : G) : RMat) ≤ ε
        rw [sl2_inverse_frobenius_distance]
        exact hclose x hx
      exact hmul u x⁻¹ (hsource u hu) hxA (hform u hu) hxF (hbound u hu) hxB (hclose u hu) hxe
  exact ⟨hgeom.1, hgeom.2.1, hEn w hw, hgeom.2.2.1, hgeom.2.2.2⟩

end TransposeFollowup.SL2Projection
