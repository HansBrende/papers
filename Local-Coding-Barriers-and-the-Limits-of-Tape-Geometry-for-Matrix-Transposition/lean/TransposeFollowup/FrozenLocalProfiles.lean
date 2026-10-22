import TransposeFollowup.NativePhysicalLimits
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.MetricSpace.UniformConvergence

/-! Stability of the actual translated, rescaled, endpoint-frozen profiles
in source208 equation(208.2). Uniform convergence is obtained from mathlib's
Ascoli theorem, after proving pointwise convergence and a common Lipschitz bound. -/
namespace TransposeFollowup.RegularMotion
open Classical Set Filter Topology
set_option autoImplicit false

noncomputable def frozenProfile (f : ℝ → ℝ) (α v ell s : ℝ) : ℝ :=
  (f (α+v*min s ell)-f α)/v

theorem frozenProfile_lipschitz {f : ℝ → ℝ} (hf : LipschitzWith 1 f)
    (α v ell : ℝ) : LipschitzWith 1 (frozenProfile f α v ell) := by
  by_cases hv : v=0
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    simp [frozenProfile,hv]
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hm := (LipschitzWith.id.min_const ell).dist_le_mul x y
  have hd := hf.dist_le_mul (α+v*min x ell) (α+v*min y ell)
  simp only [NNReal.coe_one,one_mul,Real.dist_eq] at hm hd ⊢
  rw [frozenProfile,frozenProfile,← sub_div,
    show (f (α+v*min x ell)-f α)-(f (α+v*min y ell)-f α)=
      f (α+v*min x ell)-f (α+v*min y ell) by ring,
    abs_div,div_le_iff₀ (abs_pos.mpr hv)]
  calc
    _ ≤ |(α+v*min x ell)-(α+v*min y ell)| := hd
    _ = |v| * |min x ell-min y ell| := by
      rw [show (α+v*min x ell)-(α+v*min y ell)=v*(min x ell-min y ell) by ring,abs_mul]
    _ ≤ |v| * |x-y| := mul_le_mul_of_nonneg_left hm (abs_nonneg v)
    _ = |x-y| * |v| := mul_comm _ _

theorem frozenProfile_tendsto {fs : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    {H a α v ell : ℝ} {starts vs ls : ℕ → ℝ}
    (hf : ∀ i, LipschitzWith 1 (fs i))
    (hconv : TendstoUniformlyOn fs f atTop (Icc 0 H))
    (ha : Tendsto starts atTop (𝓝 α)) (hv : Tendsto vs atTop (𝓝 v))
    (hl : Tendsto ls atTop (𝓝 ell)) (hv0 : 0 < v)
    (hst : ∀ᶠ i in atTop, 0 ≤ starts i ∧ 0 ≤ vs i ∧ 0 ≤ ls i ∧ starts i+vs i*ls i ≤ H)
    {s : ℝ} (hs : s ∈ Icc 0 a) :
    Tendsto (fun i => frozenProfile (fs i) (starts i) (vs i) (ls i) s)
      atTop (𝓝 (frozenProfile f α v ell s)) := by
  have hc : ContinuousOn f (Icc 0 H) :=
    hconv.continuousOn (Eventually.of_forall (fun i => (hf i).continuous.continuousOn)).frequently
  have hstart : ∀ᶠ i in atTop, starts i ∈ Icc 0 H := hst.mono fun i hi =>
    ⟨hi.1,le_trans (le_add_of_nonneg_right (mul_nonneg hi.2.1 hi.2.2.1)) hi.2.2.2⟩
  have harg : Tendsto (fun i => starts i+vs i*min s (ls i)) atTop (𝓝 (α+v*min s ell)) :=
    ha.add (hv.mul (tendsto_const_nhds.min hl))
  have hargmem : ∀ᶠ i in atTop, starts i+vs i*min s (ls i) ∈ Icc 0 H := by
    filter_upwards [hst] with i hi
    exact ⟨add_nonneg hi.1 (mul_nonneg hi.2.1 (le_min hs.1 hi.2.2.1)),
      (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left (min_le_right _ _) hi.2.1)).trans hi.2.2.2⟩
  have hα : α ∈ Icc 0 H := isClosed_Icc.mem_of_tendsto ha hstart
  have hβ : α+v*min s ell ∈ Icc 0 H := isClosed_Icc.mem_of_tendsto harg hargmem
  exact ((hconv.tendsto_comp (hc _ hβ) (tendsto_nhdsWithin_iff.mpr ⟨harg,hargmem⟩)).sub
    (hconv.tendsto_comp (hc _ hα) (tendsto_nhdsWithin_iff.mpr ⟨ha,hstart⟩))).div hv hv0.ne'

theorem frozenProfile_tendstoUniformlyOn {fs : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    {H a α v ell : ℝ} {starts vs ls : ℕ → ℝ}
    (hf : ∀ i, LipschitzWith 1 (fs i))
    (hconv : TendstoUniformlyOn fs f atTop (Icc 0 H))
    (ha : Tendsto starts atTop (𝓝 α)) (hv : Tendsto vs atTop (𝓝 v))
    (hl : Tendsto ls atTop (𝓝 ell)) (hv0 : 0 < v)
    (hst : ∀ᶠ i in atTop, 0 ≤ starts i ∧ 0 ≤ vs i ∧ 0 ≤ ls i ∧ starts i+vs i*ls i ≤ H) :
    TendstoUniformlyOn (fun i => frozenProfile (fs i) (starts i) (vs i) (ls i))
      (frozenProfile f α v ell) atTop (Icc 0 a) := by
  let F : ℕ → Icc (0 : ℝ) a → ℝ := fun i s => frozenProfile (fs i) (starts i) (vs i) (ls i) s
  have hF : Equicontinuous F :=
    (LipschitzWith.uniformEquicontinuous F 1
      (fun i => (frozenProfile_lipschitz (hf i) (starts i) (vs i) (ls i)).restrict _)).equicontinuous
  have hpoint : Tendsto F atTop (𝓝 (fun s : Icc (0 : ℝ) a => frozenProfile f α v ell s)) :=
    tendsto_pi_nhds.mpr fun s => frozenProfile_tendsto hf hconv ha hv hl hv0 hst s.property
  have hu := UniformFun.tendsto_iff_tendstoUniformly.mp
    ((hF.tendsto_uniformFun_iff_pi atTop _).mpr hpoint)
  exact tendstoUniformlyOn_iff_restrict.mpr hu

end TransposeFollowup.RegularMotion
