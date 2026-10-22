import TransposeFollowup.CanonicalTimeNormalization
import TransposeFollowup.AffineTimeScaling
import Transpose.Tape.DefsTrace
import Transpose.Tape.MStarClass

/-! Uniform equivalence of the actual block and physical normalizations.
The original native paths supply every discrete sample; the comparison
pays for both block rounding and time sampling. -/
namespace TransposeFollowup.RegularMotion
open Classical Set Filter Topology Transpose Transpose.Tape Transpose.Tape.Impl Transpose.Tape.TSDiagram
open TransposeFollowup.AffineMotion
set_option autoImplicit false

theorem uniform_limit_of_vanishing_error {α : Type*} {S : Set α}
    {u v : ℕ → α → ℝ} {P : α → ℝ} (hu : TendstoUniformlyOn u P atTop S)
    {e : ℕ → ℝ} (he : Tendsto e atTop (𝓝 0))
    (hd : ∀ᶠ n in atTop, ∀ x ∈ S, dist (u n x) (v n x) ≤ e n) :
    TendstoUniformlyOn v P atTop S := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu (ε/2) (by linarith),
    he.eventually_lt_const (show 0 < ε/2 by linarith),hd] with n hn he' hd'
  intro x hx
  exact (dist_triangle _ _ _).trans_lt
    (add_lt_add (hn x hx) ((hd' x hx).trans_lt he')) |>.trans_le (by linarith)

theorem block_limit_iff_scaled_physical_limit {G : ℕ} (hG : 1 ≤ G)
    {H : ℝ} {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop)
    {hs : ℕ → ℕ → ℤ} (hgood : ∀ᶠ i in atTop, UnitSteps (hs i) ∧ hs i 0=0)
    (fs : ℕ → ℝ → ℝ) (hf : ∀ i, LipschitzWith 1 (fs i))
    (he : ∀ i (m : ℕ), fs i m=(hs i m : ℝ)) {P : ℝ → ℝ} :
    TendstoUniformlyOn (fun i => blockTraj (blockSize G (ns i)) (ns i) (hs i)) P atTop (Icc 0 H) ↔
      TendstoUniformlyOn (fun i => scalePath G (physicalPath (inputLength (ns i)) (fs i)))
        P atTop (Icc 0 H) := by
  have hGp : (0 : ℝ) < G := by exact_mod_cast (show 0 < G by omega)
  let e : ℕ → ℝ := fun i => 2*(G : ℝ)*(H+1)/(ns i : ℝ)
  have he0 : Tendsto e atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat (2*(G : ℝ)*(H+1))).comp hns
  have hd : ∀ᶠ i in atTop, ∀ u ∈ Icc 0 H,
      dist (blockTraj (blockSize G (ns i)) (ns i) (hs i) u)
        (scalePath G (physicalPath (inputLength (ns i)) (fs i)) u) ≤ e i := by
    filter_upwards [hns.eventually_ge_atTop 1,hgood] with i hn hi
    intro u hu
    let B := blockTraj (blockSize G (ns i)) (ns i) (hs i) u
    let Q := physicalPath (inputLength (ns i)) (fs i) (u/G)
    have hc : |Q-B/G| ≤ 2*(u+1)/(ns i : ℝ) :=
      canonical_physical_error hG hn hi.1 hi.2 (hf i) (he i) hu.1
    change |B-(G : ℝ)*Q| ≤ e i
    calc
      _ = (G : ℝ)*|Q-B/G| := by
        rw [show B-(G : ℝ)*Q= -((G : ℝ)*(Q-B/G)) by field_simp; ring,
          abs_neg,abs_mul,abs_of_pos hGp]
      _ ≤ (G : ℝ)*(2*(u+1)/(ns i : ℝ)) := mul_le_mul_of_nonneg_left hc hGp.le
      _ ≤ (G : ℝ)*(2*(H+1)/(ns i : ℝ)) := by gcongr; exact hu.2
      _ = e i := by dsimp [e]; ring
  exact ⟨fun h => uniform_limit_of_vanishing_error h he0 hd,
    fun h => uniform_limit_of_vanishing_error h he0
      (hd.mono fun i hi u hu => by simpa only [dist_comm] using hi u hu)⟩

theorem physical_limit_of_block_limit {G : ℕ} (hG : 1 ≤ G)
    {H : ℝ} {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop)
    {hs : ℕ → ℕ → ℤ} (hgood : ∀ᶠ i in atTop, UnitSteps (hs i) ∧ hs i 0=0)
    (fs : ℕ → ℝ → ℝ) (hf : ∀ i, LipschitzWith 1 (fs i))
    (he : ∀ i (m : ℕ), fs i m=(hs i m : ℝ)) {P : ℝ → ℝ}
    (hconv : TendstoUniformlyOn (fun i => blockTraj (blockSize G (ns i)) (ns i) (hs i))
      P atTop (Icc 0 H)) :
    TendstoUniformlyOn (fun i => physicalPath (inputLength (ns i)) (fs i))
      (fun t => P ((G : ℝ)*t)/G) atTop (Icc 0 (H/G)) := by
  have hGp : (0 : ℝ) < G := by exact_mod_cast (show 0 < G by omega)
  have hs := (block_limit_iff_scaled_physical_limit hG hns hgood fs hf he).mp hconv
  have hu : UniformContinuous (fun x : ℝ => x/G) := by
    simpa only [div_eq_mul_inv,mul_comm] using (Real.uniformContinuous_const_mul (x:=(G : ℝ)⁻¹))
  have hc := hu.comp_tendstoUniformlyOn (hs.comp (fun t : ℝ => (G : ℝ)*t))
  have hsub : Icc 0 (H/(G : ℝ)) ⊆ (fun t : ℝ => (G : ℝ)*t) ⁻¹' Icc 0 H := by
    intro t ht
    exact ⟨mul_nonneg hGp.le ht.1,by simpa only [mul_comm] using (le_div_iff₀ hGp).mp ht.2⟩
  simpa only [Function.comp_def,scalePath,mul_div_cancel_left₀ _ hGp.ne'] using hc.mono hsub

theorem exists_native_physical_limits {k G : ℕ} {H : ℝ} {ns : ℕ → ℕ}
    (hns : Tendsto ns atTop atTop) (Ms : ℕ → TM) (hk : ∀ i, (Ms i).k=k)
    (hG : ∀ i, cellBits (Ms i)=G) (ws : ℕ → List Bool)
    (P : Fin k → ℝ → ℝ)
    (hconv : ∀ t, TendstoUniformlyOn (fun i => rescaledTrajOf (Ms i) (ns i) (ws i)
      (Fin.cast (hk i).symm t)) (P t) atTop (Icc 0 H)) :
    ∃ fs : ℕ → Fin k → ℝ → ℝ,
      (∀ i t, LipschitzWith 1 (fs i t)) ∧
      (∀ i t (m : ℕ), fs i t m=(workTraj (Ms i) (ws i) m (Fin.cast (hk i).symm t) : ℝ)) ∧
      ∀ t, TendstoUniformlyOn (fun i => physicalPath (inputLength (ns i)) (fs i t))
        (fun u => P t ((G : ℝ)*u)/G) atTop (Icc 0 (H/G)) := by
  choose fs hf he using fun i t =>
    exists_lipschitz_real_walk (unitSteps_workTraj (Ms i) (ws i) (Fin.cast (hk i).symm t))
  have hG1 : 1 ≤ G := hG 0 ▸ cellBits_pos (Ms 0)
  refine ⟨fs,hf,he,fun t => ?_⟩
  apply physical_limit_of_block_limit hG1 hns
    (hs:=fun i m => workTraj (Ms i) (ws i) m (Fin.cast (hk i).symm t))
    (Eventually.of_forall fun i => ⟨unitSteps_workTraj _ _ _,rfl⟩)
    (fun i => fs i t) (fun i => hf i t) (fun i m => he i t m)
  have heq : (fun i => blockTraj (blockSize G (ns i)) (ns i)
      (fun m => workTraj (Ms i) (ws i) m (Fin.cast (hk i).symm t)))=
      (fun i => rescaledTrajOf (Ms i) (ns i) (ws i) (Fin.cast (hk i).symm t)) := by
    funext i u
    simp only [rescaledTrajOf,blockTraj,slotLen,blockSize,hG]
  rw [heq]
  exact hconv t

theorem native_sampled_physical_limit {k G : ℕ} {H : ℝ} {ns : ℕ → ℕ}
    (hns : Tendsto ns atTop atTop) (Ms : ℕ → TM) (hk : ∀ i, (Ms i).k=k)
    (hG : ∀ i, cellBits (Ms i)=G) (ws : ℕ → List Bool)
    (P : Fin k → ℝ → ℝ)
    (hconv : ∀ t, TendstoUniformlyOn (fun i => rescaledTrajOf (Ms i) (ns i) (ws i)
      (Fin.cast (hk i).symm t)) (P t) atTop (Icc 0 H)) (t : Fin k) :
    TendstoUniformlyOn (fun i u =>
      (workTraj (Ms i) (ws i) ⌊(inputLength (ns i) : ℝ)*u⌋₊
        (Fin.cast (hk i).symm t) : ℝ)/inputLength (ns i))
      (fun u => P t ((G : ℝ)*u)/G) atTop (Icc 0 (H/G)) := by
  obtain ⟨fs,hf,he,hphys⟩ := exists_native_physical_limits hns Ms hk hG ws P hconv
  apply uniform_limit_of_vanishing_error (hphys t)
    (e:=fun i => 1/(inputLength (ns i) : ℝ))
    (tendsto_const_nhds.div_atTop (inputLength_tendsto hns))
  filter_upwards [(inputLength_tendsto hns).eventually_gt_atTop 0] with i hi
  intro u hu
  simpa only [Real.dist_eq] using physicalPath_sample_error hi (hf i t) (he i t) hu.1

end TransposeFollowup.RegularMotion
