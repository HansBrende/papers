import TransposeFollowup.NativeFrozenProfiles
import TransposeFollowup.BoundedAffineCovers

/-! A regular subsequential local limit must be the already determined frozen
profile. Its actual unfrozen stage then inherits a finite affine cover. -/
namespace TransposeFollowup.RegularMotion
open Classical Set Filter Topology
open TransposeFollowup.AffineMotion
set_option autoImplicit false

theorem frozenProfile_affine_of_subsequence {profiles : ℕ → ℝ → ℝ} {f q : ℝ → ℝ}
    {α v ell a : ℝ} {J : ℕ} {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hconv : TendstoUniformlyOn profiles (frozenProfile f α v ell) atTop (Icc 0 a))
    (hlocal : TendstoUniformlyOn (fun i => profiles (φ i)) q atTop (Icc 0 a))
    (hq : HasAffineIntervalCover J q a) :
    HasAffineIntervalCover J (frozenProfile f α v ell) a := by
  obtain ⟨l,r,hcover,hpieces⟩ := hq
  refine ⟨l,r,hcover,fun i => ?_⟩
  obtain ⟨c,d,hcd⟩ := hpieces i
  refine ⟨c,d,fun x hx => ?_⟩
  have hxa : x ∈ Icc 0 a := ⟨(l i).property.1.trans hx.1,hx.2.trans (r i).property.2⟩
  have heq : frozenProfile f α v ell x=q x :=
    tendsto_nhds_unique ((hconv.tendsto_at hxa).comp hφ.tendsto_atTop) (hlocal.tendsto_at hxa)
  exact heq.trans (hcd x hx)

theorem frozenProfile_affine_stage {f : ℝ → ℝ} {α v ell a : ℝ} {J : ℕ}
    (hv : 0 < v) (hell : 0 ≤ ell) (hella : ell ≤ a)
    (hq : HasAffineIntervalCover J (frozenProfile f α v ell) a) :
    HasAffineIntervalCover J (fun s => f (α+v*s)) ell := by
  obtain ⟨l,r,hcover,hpieces⟩ := hq
  let l' : Fin J → Icc (0 : ℝ) ell :=
    fun i => ⟨min (l i : ℝ) ell,le_min (l i).property.1 hell,min_le_right _ _⟩
  let r' : Fin J → Icc (0 : ℝ) ell :=
    fun i => ⟨min (r i : ℝ) ell,le_min (r i).property.1 hell,min_le_right _ _⟩
  refine ⟨l',r',?_,?_⟩
  · intro x hx
    obtain ⟨i,hi⟩ := hcover x ⟨hx.1,hx.2.trans hella⟩
    exact ⟨i,(min_le_left _ _).trans hi.1,le_min hi.2 hx.2⟩
  · intro i
    by_cases hli : (l i : ℝ) ≤ ell
    · obtain ⟨c,d,hcd⟩ := hpieces i
      refine ⟨v*c,v*d+f α,fun x hx => ?_⟩
      have hx0 : (l i : ℝ) ≤ x := by simpa only [l',min_eq_left hli] using hx.1
      have hx1 : x ≤ (r i : ℝ) := hx.2.trans (min_le_left _ _)
      have hxell : x ≤ ell := hx.2.trans (min_le_right _ _)
      have hc := hcd x ⟨hx0,hx1⟩
      simp only [frozenProfile,min_eq_left hxell] at hc
      have he := (div_eq_iff hv.ne').mp hc
      nlinarith
    · refine ⟨0,f (α+v*ell),fun x hx => ?_⟩
      have hx0 : ell ≤ x := (le_min (le_of_not_ge hli) le_rfl).trans hx.1
      have hx1 : x ≤ ell := hx.2.trans (min_le_right _ _)
      have hxe : x=ell := le_antisymm hx1 hx0
      simp only [hxe,zero_mul,zero_add]

theorem native_positive_stage_affine {Ps Vs : ℕ → ℝ} {A L : ℕ → ℕ}
    {hs : ℕ → ℕ → ℤ} {fs : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {H a α v ell : ℝ}
    (hP : ∀ i, 0 < Ps i) (hPinf : Tendsto Ps atTop atTop) (hV : ∀ i, 0 < Vs i)
    (hf : ∀ i, LipschitzWith 1 (fs i)) (he : ∀ i (m : ℕ), fs i m=(hs i m : ℝ))
    (hconv : TendstoUniformlyOn (fun i => physicalPath (Ps i) (fs i)) f atTop (Icc 0 H))
    (ha : Tendsto (fun i => (A i : ℝ)/Ps i) atTop (𝓝 α))
    (hv : Tendsto (fun i => Vs i/Ps i) atTop (𝓝 v))
    (hl : Tendsto (fun i => (L i : ℝ)/Vs i) atTop (𝓝 ell)) (hv0 : 0 < v)
    (hend : ∀ i, (A i : ℝ)+(L i : ℝ) ≤ H*Ps i)
    (hbudget : ∀ i, (L i : ℝ) ≤ a*Vs i)
    (hregular : Tendsto Vs atTop atTop →
      ∃ (J : ℕ) (φ : ℕ → ℕ) (q : ℝ → ℝ), StrictMono φ ∧ HasAffineIntervalCover J q a ∧
        TendstoUniformlyOn (fun i s =>
          ((hs (φ i) (A (φ i)+min ⌊Vs (φ i)*s⌋₊ (L (φ i)))-hs (φ i) (A (φ i)) : ℤ) : ℝ)/Vs (φ i))
          q atTop (Icc 0 a)) :
    ∃ J, HasAffineIntervalCover J (fun s => f (α+v*s)) ell := by
  have hVinf : Tendsto Vs atTop atTop := by
    apply (hPinf.atTop_mul_pos hv0 hv).congr'
    exact Eventually.of_forall fun i => by field_simp [(hP i).ne']
  have hst : ∀ᶠ i in atTop, 0 ≤ (A i : ℝ)/Ps i ∧ 0 ≤ Vs i/Ps i ∧
      0 ≤ (L i : ℝ)/Vs i ∧ (A i : ℝ)/Ps i+(Vs i/Ps i)*((L i : ℝ)/Vs i) ≤ H := by
    apply Eventually.of_forall
    intro i
    refine ⟨div_nonneg (Nat.cast_nonneg _) (hP i).le,div_nonneg (hV i).le (hP i).le,
      div_nonneg (Nat.cast_nonneg _) (hV i).le,?_⟩
    have hpne := (hP i).ne'
    have hvne := (hV i).ne'
    rw [show (A i : ℝ)/Ps i+(Vs i/Ps i)*((L i : ℝ)/Vs i)=
      ((A i : ℝ)+(L i : ℝ))/Ps i by field_simp]
    exact (div_le_iff₀ (hP i)).mpr (hend i)
  have hu := frozenProfile_tendstoUniformlyOn (a:=a)
    (fun i => physicalPath_lipschitz (hP i) (hf i)) hconv ha hv hl hv0 hst
  have hraw : TendstoUniformlyOn (fun i s =>
      ((hs i (A i+min ⌊Vs i*s⌋₊ (L i))-hs i (A i) : ℤ) : ℝ)/Vs i)
      (frozenProfile f α v ell) atTop (Icc 0 a) := by
    exact (native_frozen_sampled_limit_iff hP hV hVinf hf he A L).mp hu
  have hell : ell ∈ Icc (0 : ℝ) a := isClosed_Icc.mem_of_tendsto hl
    (Eventually.of_forall fun i =>
      ⟨div_nonneg (Nat.cast_nonneg _) (hV i).le,(div_le_iff₀ (hV i)).mpr (hbudget i)⟩)
  obtain ⟨J,φ,q,hφ,hq,hlq⟩ := hregular hVinf
  exact ⟨J,frozenProfile_affine_stage hv0 hell.1 hell.2
    (frozenProfile_affine_of_subsequence hφ hraw hlq hq)⟩

end TransposeFollowup.RegularMotion
