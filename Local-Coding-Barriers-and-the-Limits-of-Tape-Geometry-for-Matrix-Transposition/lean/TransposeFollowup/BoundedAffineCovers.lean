import TransposeFollowup.AffinePointwiseClosure
import Mathlib.Topology.Sequences
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Fixed-size affine interval covers are stable enough under pointwise
limits to give local affinity away from finitely many limiting endpoints.
Intervals may overlap or collapse; no Lipschitz bound is required here. -/
namespace TransposeFollowup.AffineMotion
open Classical Set Filter Topology MeasureTheory
set_option autoImplicit false

def HasAffineIntervalCover (J : ℕ) (f : ℝ → ℝ) (H : ℝ) : Prop :=
  ∃ l r : Fin J → Icc (0 : ℝ) H,
    (∀ x ∈ Icc 0 H, ∃ i, (l i : ℝ) ≤ x ∧ x ≤ (r i : ℝ)) ∧
    ∀ i, ∃ a b : ℝ, ∀ x ∈ Icc (l i : ℝ) (r i : ℝ), f x=a*x+b

theorem local_affine_ae_of_bounded_covers {J : ℕ} {H : ℝ}
    {q : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (hq : ∀ n, HasAffineIntervalCover J (q n) H)
    (hconv : ∀ x ∈ Icc 0 H, Tendsto (fun n => q n x) atTop (𝓝 (f x))) :
    ∃ R : Set ℝ, IsOpen R ∧ R ⊆ Icc 0 H ∧ volume (Icc 0 H \ R)=0 ∧
      ∀ x ∈ R, ∃ U : Set ℝ, IsOpen U ∧ x ∈ U ∧ U ⊆ R ∧
        ∃ a b : ℝ, ∀ y ∈ U, f y=a*y+b := by
  choose l r hcover ha using hq
  obtain ⟨e,φ,hφ,he⟩ := CompactSpace.tendsto_subseq (fun n => (l n,r n))
  have hleft (i : Fin J) :
      Tendsto (fun n => (l (φ n) i : ℝ)) atTop (𝓝 (e.1 i : ℝ)) :=
    (show Continuous (fun v : ((Fin J → Icc (0 : ℝ) H) × (Fin J → Icc (0 : ℝ) H)) => (v.1 i : ℝ)) by fun_prop).continuousAt.tendsto.comp he
  have hright (i : Fin J) :
      Tendsto (fun n => (r (φ n) i : ℝ)) atTop (𝓝 (e.2 i : ℝ)) :=
    (show Continuous (fun v : ((Fin J → Icc (0 : ℝ) H) × (Fin J → Icc (0 : ℝ) H)) => (v.2 i : ℝ)) by fun_prop).continuousAt.tendsto.comp he
  have hcoverlim (x : ℝ) (hx : x ∈ Icc 0 H) :
      ∃ i, (e.1 i : ℝ) ≤ x ∧ x ≤ (e.2 i : ℝ) := by
    have hs : IsClosed {v : ((Fin J → Icc (0 : ℝ) H) × (Fin J → Icc (0 : ℝ) H)) | ∃ i, (v.1 i : ℝ) ≤ x ∧ x ≤ (v.2 i : ℝ)} := by
      simp only [Set.ofPred_exists]
      apply isClosed_iUnion_of_finite
      intro i
      exact (isClosed_le
        (show Continuous (fun v : ((Fin J → Icc (0 : ℝ) H) × (Fin J → Icc (0 : ℝ) H)) =>
          (v.1 i : ℝ)) by fun_prop) continuous_const).inter
        (isClosed_le continuous_const
          (show Continuous (fun v : ((Fin J → Icc (0 : ℝ) H) × (Fin J → Icc (0 : ℝ) H)) =>
            (v.2 i : ℝ)) by fun_prop))
    exact hs.mem_of_tendsto he (Eventually.of_forall fun n => hcover (φ n) x hx)
  let Z : Set ℝ := Set.range (fun i => (e.1 i : ℝ)) ∪ Set.range (fun i => (e.2 i : ℝ))
  have hZ : Z.Finite := (Set.finite_range _).union (Set.finite_range _)
  let R : Set ℝ := Ioo 0 H \ Z
  have hRo : IsOpen R := isOpen_Ioo.sdiff hZ.isClosed
  have hRI : R ⊆ Icc 0 H := fun _ hx => ⟨hx.1.1.le,hx.1.2.le⟩
  have hnull : volume (Icc 0 H \ R)=0 := by
    have hsub : Icc 0 H \ R ⊆ ({0,H} : Set ℝ) ∪ Z := by
      intro x hx
      by_cases hxZ : x ∈ Z
      · exact Or.inr hxZ
      · by_cases hx0 : x=0
        · exact Or.inl (by simp [hx0])
        · by_cases hxH : x=H
          · exact Or.inl (by simp [hxH])
          · exact False.elim (hx.2 ⟨⟨lt_of_le_of_ne hx.1.1 (Ne.symm hx0),
              lt_of_le_of_ne hx.1.2 hxH⟩,hxZ⟩)
    exact measure_mono_null hsub ((((Set.finite_singleton H).insert 0).union hZ).measure_zero volume)
  refine ⟨R,hRo,hRI,hnull,?_⟩
  intro x hx
  obtain ⟨i,hli,hri⟩ := hcoverlim x (hRI hx)
  have hneqL : x ≠ (e.1 i : ℝ) := fun heq => hx.2 (Or.inl ⟨i,heq.symm⟩)
  have hneqR : x ≠ (e.2 i : ℝ) := fun heq => hx.2 (Or.inr ⟨i,heq.symm⟩)
  have hl : (e.1 i : ℝ) < x := lt_of_le_of_ne hli hneqL.symm
  have hr : x < (e.2 i : ℝ) := lt_of_le_of_ne hri hneqR
  let u : ℝ := ((e.1 i : ℝ)+x)/2
  let v : ℝ := (x+(e.2 i : ℝ))/2
  have hlu : (e.1 i : ℝ) < u := by dsimp [u]; linarith
  have hux : u < x := by dsimp [u]; linarith
  have hxv : x < v := by dsimp [v]; linarith
  have hvr : v < (e.2 i : ℝ) := by dsimp [v]; linarith
  have hVI : Ioo u v ⊆ Icc 0 H := by
    intro y hy
    exact ⟨(e.1 i).property.1.trans (hlu.le.trans hy.1.le),
      hy.2.le.trans (hvr.le.trans (e.2 i).property.2)⟩
  have hevent : ∀ᶠ n in atTop, ∃ a b : ℝ, ∀ y ∈ Ioo u v, q (φ n) y=a*y+b := by
    filter_upwards [(hleft i).eventually_lt_const hlu,(hright i).eventually_const_lt hvr]
      with n hnL hnR
    obtain ⟨a,b,hab⟩ := ha (φ n) i
    exact ⟨a,b,fun y hy => hab y ⟨hnL.le.trans hy.1.le,hy.2.le.trans hnR.le⟩⟩
  obtain ⟨a,b,hab⟩ := affine_on_of_tendsto
    (fun y hy => (hconv y (hVI hy)).comp hφ.tendsto_atTop) hevent
  exact ⟨Ioo u v ∩ R,isOpen_Ioo.inter hRo,⟨⟨hux,hxv⟩,hx⟩,
    Set.inter_subset_right,a,b,fun y hy => hab y hy.1⟩

theorem local_affine_ae_of_eventual_bounded_covers {J : ℕ} {H : ℝ}
    {q : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (hq : ∀ᶠ n in atTop, HasAffineIntervalCover J (q n) H)
    (hconv : ∀ x ∈ Icc 0 H, Tendsto (fun n => q n x) atTop (𝓝 (f x))) :
    ∃ R : Set ℝ, IsOpen R ∧ R ⊆ Icc 0 H ∧ volume (Icc 0 H \ R)=0 ∧
      ∀ x ∈ R, ∃ U : Set ℝ, IsOpen U ∧ x ∈ U ∧ U ⊆ R ∧
        ∃ a b : ℝ, ∀ y ∈ U, f y=a*y+b := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp hq
  exact local_affine_ae_of_bounded_covers (q:=fun n => q (n+N))
    (fun n => hN (n+N) (by omega))
    (fun x hx => (hconv x hx).comp (tendsto_add_atTop_nat N))

end TransposeFollowup.AffineMotion
