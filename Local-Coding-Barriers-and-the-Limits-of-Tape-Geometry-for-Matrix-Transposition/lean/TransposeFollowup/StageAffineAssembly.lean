import TransposeFollowup.BoundedAffineCovers
import TransposeFollowup.AffineGridMass

/-! Assembly of the already proved local affine covers. Affine transport of
null sets is reused from AffineGridMass; countable null unions are mathlib's.
No common finite bound on the number of pieces across stages is needed. -/
namespace TransposeFollowup.RegularMotion
open Classical Set Filter Topology MeasureTheory
open TransposeFollowup.AffineMotion
set_option autoImplicit false

theorem local_affine_ae_on_stage {J : ℕ} {f : ℝ → ℝ} {l v ell : ℝ}
    (hv : 0 < v) (hq : HasAffineIntervalCover J (fun s => f (l+v*s)) ell) :
    ∃ R : Set ℝ, IsOpen R ∧ R ⊆ Ioo l (l+v*ell) ∧
      volume (Ioo l (l+v*ell) \ R)=0 ∧
      ∀ x ∈ R, ∃ U : Set ℝ, IsOpen U ∧ x ∈ U ∧ U ⊆ R ∧
        ∃ c d : ℝ, ∀ y ∈ U, f y=c*y+d := by
  obtain ⟨S,hSo,_,hSn,hSl⟩ := local_affine_ae_of_bounded_covers
    (fun _ : ℕ => hq) (fun _ _ => tendsto_const_nhds)
  let g : ℝ → ℝ := fun x => v⁻¹*x+(-l/v)
  have hg (x : ℝ) : g x=(x-l)/v := by dsimp [g]; ring
  have hinv (x : ℝ) : l+v*g x=x := by rw [hg]; field_simp; ring
  have hgc : Continuous g := by fun_prop
  have hmem {x : ℝ} (hx : x ∈ Ioo l (l+v*ell)) : g x ∈ Icc 0 ell := by
    rw [hg]
    constructor
    · exact div_nonneg (sub_nonneg.mpr hx.1.le) hv.le
    · apply (div_le_iff₀ hv).mpr
      nlinarith [hx.2]
  let R : Set ℝ := Ioo l (l+v*ell) ∩ g ⁻¹' S
  refine ⟨R,isOpen_Ioo.inter (hSo.preimage hgc),Set.inter_subset_left,?_,?_⟩
  · apply measure_mono_null (t:=g ⁻¹' (Icc 0 ell \ S))
    · intro x hx
      exact ⟨hmem hx.1,fun hxS => hx.2 ⟨hx.1,hxS⟩⟩
    · change volume ((fun x : ℝ => v⁻¹*x+(-l/v)) ⁻¹' (Icc 0 ell \ S))=0
      rw [volume_affine_preimage (inv_ne_zero hv.ne'),hSn,mul_zero]
  · intro x hx
    obtain ⟨U,hUo,hxU,hUS,c,d,hf⟩ := hSl (g x) hx.2
    refine ⟨Ioo l (l+v*ell) ∩ g ⁻¹' U,isOpen_Ioo.inter (hUo.preimage hgc),
      ⟨hx.1,hxU⟩,(fun y hy => ⟨hy.1,hUS hy.2⟩),c/v,d-c*l/v,?_⟩
    intro y hy
    calc
      f y = c*g y+d := by simpa only [hinv] using hf (g y) hy.2
      _ = (c/v)*y+(d-c*l/v) := by dsimp [g]; ring

theorem assemble_stage_local_affinity_ae {κ : Type*} [Countable κ]
    {f : ℝ → ℝ} {l r : κ → ℝ} {H : ℝ}
    (hb : ∀ p, 0 ≤ l p ∧ r p ≤ H)
    (hstage : ∀ p, ∃ R : Set ℝ, IsOpen R ∧ R ⊆ Ioo (l p) (r p) ∧
      volume (Ioo (l p) (r p) \ R)=0 ∧
      ∀ x ∈ R, ∃ U : Set ℝ, IsOpen U ∧ x ∈ U ∧ U ⊆ R ∧
        ∃ c d : ℝ, ∀ y ∈ U, f y=c*y+d) :
    ∃ R : Set ℝ, IsOpen R ∧ R ⊆ Icc 0 H ∧ (R =ᵐ[volume] ⋃ p, Ioo (l p) (r p)) ∧
      ∀ x ∈ R, ∃ U : Set ℝ, IsOpen U ∧ x ∈ U ∧ U ⊆ R ∧
        ∃ c d : ℝ, ∀ y ∈ U, f y=c*y+d := by
  choose R hRo hRi hRn hRl using hstage
  refine ⟨⋃ p, R p,isOpen_iUnion hRo,?_,?_,?_⟩
  · apply Set.iUnion_subset
    intro p x hx
    exact ⟨(hb p).1.trans (hRi p hx).1.le,(hRi p hx).2.le.trans (hb p).2⟩
  · exact EventuallyEqSet.countable_iUnion (fun p =>
      (hRi p).eventuallySubset.antisymm (ae_le_set.mpr (hRn p)))
  · intro x hx
    obtain ⟨p,hp⟩ := Set.mem_iUnion.mp hx
    obtain ⟨U,hUo,hxU,hUR,c,d,hf⟩ := hRl p x hp
    exact ⟨U,hUo,hxU,hUR.trans (Set.subset_iUnion R p),c,d,hf⟩

theorem assemble_stage_local_affinity {κ : Type*} [Countable κ]
    {f : ℝ → ℝ} {l r : κ → ℝ} {H : ℝ}
    (hb : ∀ p, 0 ≤ l p ∧ r p ≤ H)
    (hcov : volume (Icc 0 H \ ⋃ p, Ioo (l p) (r p))=0)
    (hstage : ∀ p, ∃ R : Set ℝ, IsOpen R ∧ R ⊆ Ioo (l p) (r p) ∧
      volume (Ioo (l p) (r p) \ R)=0 ∧
      ∀ x ∈ R, ∃ U : Set ℝ, IsOpen U ∧ x ∈ U ∧ U ⊆ R ∧
        ∃ c d : ℝ, ∀ y ∈ U, f y=c*y+d) :
    ∃ R : Set ℝ, IsOpen R ∧ R ⊆ Icc 0 H ∧ volume (Icc 0 H \ R)=0 ∧
      ∀ x ∈ R, ∃ U : Set ℝ, IsOpen U ∧ x ∈ U ∧ U ⊆ R ∧
        ∃ c d : ℝ, ∀ y ∈ U, f y=c*y+d := by
  obtain ⟨R,hRo,hRI,hReq,hRl⟩ := assemble_stage_local_affinity_ae hb hstage
  exact ⟨R,hRo,hRI,(measure_congr (ae_eq_set_sdiff .rfl hReq)).trans hcov,hRl⟩

theorem extend_affine_cover_by_constant_le {f : ℝ → ℝ} {H M : ℝ}
    (hHM : H ≤ M) {R : Set ℝ} (hRo : IsOpen R) (hRI : R ⊆ Icc 0 H)
    (hRl : ∀ x ∈ R, ∃ U : Set ℝ, IsOpen U ∧ x ∈ U ∧ U ⊆ R ∧
      ∃ c d : ℝ, ∀ y ∈ U, f y=c*y+d)
    (hconst : ∀ x ∈ Icc H M, f x=f H) :
    ∃ S : Set ℝ, IsOpen S ∧ S ⊆ Icc 0 M ∧
      volume (Icc 0 M \ S) ≤ volume (Icc 0 H \ R) ∧
      ∀ x ∈ S, ∃ U : Set ℝ, IsOpen U ∧ x ∈ U ∧ U ⊆ S ∧
        ∃ c d : ℝ, ∀ y ∈ U, f y=c*y+d := by
  let S : Set ℝ := R ∪ Ioo (max 0 H) M
  refine ⟨S,hRo.union isOpen_Ioo,?_,?_,?_⟩
  · intro x hx
    rcases hx with hx | hx
    · exact ⟨(hRI hx).1,(hRI hx).2.trans hHM⟩
    · exact ⟨(le_max_left _ _).trans hx.1.le,hx.2.le⟩
  · refine (measure_mono (t:=(Icc 0 H \ R) ∪ ({0,M} : Set ℝ)) ?_).trans ?_
    · intro x hx
      by_cases hxH : x ≤ H
      · exact Or.inl ⟨⟨hx.1.1,hxH⟩,fun hxR => hx.2 (Or.inl hxR)⟩
      · by_cases hx0 : x=0
        · exact Or.inr (by simp [hx0])
        · by_cases hxM : x=M
          · exact Or.inr (by simp [hxM])
          · exact False.elim (hx.2 (Or.inr ⟨max_lt (lt_of_le_of_ne hx.1.1 (Ne.symm hx0))
              (lt_of_not_ge hxH),lt_of_le_of_ne hx.1.2 hxM⟩))
    · simpa only [((Set.finite_singleton M).insert 0).measure_zero volume,add_zero] using
        measure_union_le (μ:=volume) (Icc 0 H \ R) ({0,M} : Set ℝ)
  · intro x hx
    rcases hx with hx | hx
    · obtain ⟨U,hUo,hxU,hUR,c,d,hf⟩ := hRl x hx
      exact ⟨U,hUo,hxU,hUR.trans Set.subset_union_left,c,d,hf⟩
    · refine ⟨Ioo (max 0 H) M,isOpen_Ioo,hx,Set.subset_union_right,0,f H,?_⟩
      intro y hy
      simpa only [zero_mul,zero_add] using hconst y ⟨(le_max_right _ _).trans hy.1.le,hy.2.le⟩

theorem extend_affine_cover_by_constant {f : ℝ → ℝ} {H M : ℝ}
    (hHM : H ≤ M) {R : Set ℝ} (hRo : IsOpen R) (hRI : R ⊆ Icc 0 H)
    (hRn : volume (Icc 0 H \ R)=0)
    (hRl : ∀ x ∈ R, ∃ U : Set ℝ, IsOpen U ∧ x ∈ U ∧ U ⊆ R ∧
      ∃ c d : ℝ, ∀ y ∈ U, f y=c*y+d)
    (hconst : ∀ x ∈ Icc H M, f x=f H) :
    ∃ S : Set ℝ, IsOpen S ∧ S ⊆ Icc 0 M ∧ volume (Icc 0 M \ S)=0 ∧
      ∀ x ∈ S, ∃ U : Set ℝ, IsOpen U ∧ x ∈ U ∧ U ⊆ S ∧
        ∃ c d : ℝ, ∀ y ∈ U, f y=c*y+d := by
  obtain ⟨S,hSo,hSI,hSn,hSl⟩ := extend_affine_cover_by_constant_le hHM hRo hRI hRl hconst
  exact ⟨S,hSo,hSI,le_zero_iff.mp (hSn.trans_eq hRn),hSl⟩

end TransposeFollowup.RegularMotion
