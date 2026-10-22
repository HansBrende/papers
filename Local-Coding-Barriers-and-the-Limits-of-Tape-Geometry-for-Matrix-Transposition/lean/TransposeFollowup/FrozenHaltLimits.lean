import TransposeFollowup.NativePhysicalLimits
import Mathlib.Topology.UniformSpace.UniformApproximation

/-! Frozen discrete halting tails induce constant physical limit tails, even
when the Lipschitz extensions between integer ticks were chosen arbitrarily.
The native specialization imports the original workTraj_frozen theorem. -/
namespace TransposeFollowup.RegularMotion
open Classical Set Filter Topology Transpose Transpose.Tape Transpose.Tape.Impl
set_option autoImplicit false

theorem physical_limit_constant_after_halt {P : ℕ → ℝ} {T : ℕ → ℕ}
    {hs : ℕ → ℕ → ℤ} {fs : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {H M : ℝ}
    (hP : ∀ i, 0 < P i) (hPinf : Tendsto P atTop atTop)
    (hf : ∀ i, LipschitzWith 1 (fs i)) (he : ∀ i (m : ℕ), fs i m=(hs i m : ℝ))
    (hconv : TendstoUniformlyOn (fun i => physicalPath (P i) (fs i)) f atTop (Icc 0 M))
    (htime : ∀ i, (T i : ℝ)/P i ≤ M)
    (hT : Tendsto (fun i => (T i : ℝ)/P i) atTop (𝓝 H))
    (hstop : ∀ i m, T i ≤ m → hs i m=hs i (T i)) :
    ∀ x ∈ Icc H M, f x=f H := by
  have hmem : ∀ᶠ i in atTop, (T i : ℝ)/P i ∈ Icc 0 M :=
    Eventually.of_forall (fun i => ⟨div_nonneg (Nat.cast_nonneg _) (hP i).le,htime i⟩)
  have hHI : H ∈ Icc 0 M := isClosed_Icc.mem_of_tendsto hT hmem
  have hfc : ContinuousOn f (Icc 0 M) := hconv.continuousOn
    (Eventually.of_forall (fun i => (physicalPath_lipschitz (hP i) (hf i)).continuous.continuousOn)).frequently
  have hhalt : Tendsto (fun i => physicalPath (P i) (fs i) ((T i : ℝ)/P i))
      atTop (𝓝 (f H)) :=
    hconv.tendsto_comp (hfc H hHI) (tendsto_nhdsWithin_iff.mpr ⟨hT,hmem⟩)
  have herr0 : Tendsto (fun i => 1/P i) atTop (𝓝 (0 : ℝ)) := by
    simpa only [one_div,Function.comp_def] using tendsto_inv_atTop_zero.comp hPinf
  intro x hx
  by_cases hxH : x=H
  · exact congrArg f hxH
  have hHx : H < x := lt_of_le_of_ne hx.1 (Ne.symm hxH)
  have hx0 : 0 ≤ x := hHI.1.trans hx.1
  have herr : ∀ᶠ i in atTop,
      |physicalPath (P i) (fs i) x-physicalPath (P i) (fs i) ((T i : ℝ)/P i)| ≤ 1/P i := by
    filter_upwards [hT.eventually_lt_const hHx] with i hi
    have hfloor : T i ≤ ⌊P i*x⌋₊ := by
      apply (Nat.le_floor_iff (mul_nonneg (hP i).le hx0)).mpr
      have hh := (div_lt_iff₀ (hP i)).mp hi
      simpa only [mul_comm x (P i)] using hh.le
    have hsample := physicalPath_sample_error (hP i) (hf i) (he i) hx0
    rw [hstop i _ hfloor] at hsample
    have hhaltval : physicalPath (P i) (fs i) ((T i : ℝ)/P i)=(hs i (T i) : ℝ)/P i := by
      rw [physicalPath,show P i*((T i : ℝ)/P i)=(T i : ℝ) by field_simp [(hP i).ne'],he i]
    simpa only [hhaltval] using hsample
  have hzero : |f x-f H| ≤ 0 := le_of_tendsto_of_tendsto
    (((hconv.tendsto_at ⟨hx0,hx.2⟩).sub hhalt).abs) herr0 herr
  exact sub_eq_zero.mp (abs_nonpos_iff.mp hzero)

theorem native_physical_limit_constant_after_halt
    {Ms : ℕ → TM} {ws : ℕ → List Bool} {T : ℕ → ℕ} {P : ℕ → ℝ}
    (heads : ∀ i, Fin (Ms i).k) {fs : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {H M : ℝ}
    (hP : ∀ i, 0 < P i) (hPinf : Tendsto P atTop atTop)
    (hf : ∀ i, LipschitzWith 1 (fs i))
    (he : ∀ i (m : ℕ), fs i m=(workTraj (Ms i) (ws i) m (heads i) : ℝ))
    (hconv : TendstoUniformlyOn (fun i => physicalPath (P i) (fs i)) f atTop (Icc 0 M))
    (htime : ∀ i, (T i : ℝ)/P i ≤ M)
    (hT : Tendsto (fun i => (T i : ℝ)/P i) atTop (𝓝 H))
    (hhalt : ∀ i, HaltsAt (Ms i) (ws i) (T i)) :
    ∀ x ∈ Icc H M, f x=f H := by
  apply physical_limit_constant_after_halt hP hPinf hf he hconv htime hT
  intro i m hm
  simpa only [min_eq_right hm] using (congrFun (workTraj_frozen (hhalt i) (heads i)) m).symm

end TransposeFollowup.RegularMotion
