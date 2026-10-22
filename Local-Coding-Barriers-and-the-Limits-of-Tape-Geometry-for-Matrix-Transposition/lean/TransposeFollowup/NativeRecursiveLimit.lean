import TransposeFollowup.ExceptionalRecursiveLimits
import TransposeFollowup.NativeAffineMotion

/-! Native integration of the recursion geometry. Actual HaltsAt freezes the
raw heads; exact normalization transports the already proved affine-time
requirement. Every fixed physical work head is included. -/
namespace TransposeFollowup.RegularMotion
open Classical Set Filter Topology MeasureTheory Transpose Transpose.Tape Transpose.Tape.Impl
open TransposeFollowup.AffineMotion
open scoped BigOperators ENNReal
set_option autoImplicit false

theorem native_flagged_limit_budget
    {B J k G : ℕ} {rho a C c eta : ℝ} {ns : ℕ → ℕ} {eps : ℕ → ℝ}
    (hns : Tendsto ns atTop atTop) {Ms : ℕ → TM}
    (hk : ∀ i, (Ms i).k=k) (hG : ∀ i, cellBits (Ms i)=G)
    {ws : ℕ → List Bool} {T : ℕ → ℕ}
    (clocks : ∀ i, ContractingStageClock B J rho a C (inputLength (ns i)) (T i))
    (good : ℕ → List (Fin B) × Fin J → Bool)
    (hr : 0 ≤ rho) (hr1 : rho < 1) (ha : 0 ≤ a)
    (hP : ∀ i, 0 < (inputLength (ns i) : ℝ))
    (htime : ∀ i, (T i : ℝ) ≤ c*inputLength (ns i))
    (hhalt : ∀ i, HaltsAt (Ms i) (ws i) (T i))
    (hregular : ∀ t : Fin k, RegularFlaggedClockHead clocks good
      (fun i m => workTraj (Ms i) (ws i) m (Fin.cast (hk i).symm t)))
    (heps : Tendsto eps atTop (𝓝 0))
    (hbad : ∀ i, (exceptionalTicks (clocks i) (good i) : ℝ)/inputLength (ns i) ≤ eta+eps i)
    (Q : Fin k → ℝ → ℝ)
    (hconv : ∀ t, TendstoUniformlyOn (fun i => rescaledTrajOf (Ms i) (ns i) (ws i)
      (Fin.cast (hk i).symm t)) (Q t) atTop (Icc 0 (c*G+1)))
    (hrequired : AffineTimeRequired Q (c*G+1)) : 1/(2*(G : ℝ)) ≤ (k : ℝ)*eta := by
  have hG1 : 1 ≤ G := hG 0 ▸ cellBits_pos (Ms 0)
  have hGp : (0 : ℝ) < G := by exact_mod_cast (show 0 < G by omega)
  let H : ℝ := (c*G+1)/G
  let f : Fin k → ℝ → ℝ := fun t u => Q t ((G : ℝ)*u)/G
  obtain ⟨fs,hf,he,hphys⟩ := exists_native_physical_limits hns Ms hk hG ws Q hconv
  have hbound (i : ℕ) : (T i : ℝ)/inputLength (ns i) ≤ H := by
    apply ((div_le_iff₀ (hP i)).mpr (htime i)).trans
    apply (le_div_iff₀ hGp).mpr
    linarith
  have hR (t : Fin k) : ∃ R : Set ℝ, IsOpen R ∧ R ⊆ Icc 0 H ∧ volume.real (Icc 0 H \ R) ≤ eta ∧
      ∀ x ∈ R, ∃ U : Set ℝ, IsOpen U ∧ x ∈ U ∧ U ⊆ R ∧
        ∃ b d : ℝ, ∀ y ∈ U, f t y=b*y+d := by
    apply flagged_clock_limit_locally_affine clocks good hr hr1 ha hP (inputLength_tendsto hns)
      hbound (fun i => hf i t) (fun i => he i t) (hphys t) ?_ (hregular t) heps hbad
    intro i m hm
    simpa only [min_eq_right hm] using
      (congrFun (workTraj_frozen (hhalt i) (Fin.cast (hk i).symm t)) m).symm
  choose R _ hRI hRn hRl using hR
  have hscale : (fun t => scalePath (G : ℝ) (f t))=Q := by
    funext t u
    dsimp [scalePath,f]
    rw [show (G : ℝ)*(u/G)=u by field_simp]
    field_simp
  have hH : (G : ℝ)*H=c*G+1 := by dsimp [H]; field_simp
  have hrequired' : AffineTimeRequired (fun t => scalePath (G : ℝ) (f t)) ((G : ℝ)*H) := by
    rw [hscale,hH]
    exact hrequired
  have hb := hrequired'.physical_omission hGp R hRI hRl
  have hfinite (t : Fin k) : volume (Icc 0 H \ R t) ≠ ⊤ :=
    measure_ne_top_of_subset Set.sdiff_subset (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have hbR : 1/(2*(G : ℝ)) ≤ ∑ t, volume.real (Icc 0 H \ R t) := by
    have hb' := ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr (fun t _ => hfinite t)) hb
    simpa [measureReal_def,ENNReal.toReal_sum (fun t _ => hfinite t),
      ENNReal.toReal_ofReal hGp.le] using hb'
  calc
    1/(2*(G : ℝ)) ≤ ∑ t, volume.real (Icc 0 H \ R t) := hbR
    _ ≤ ∑ _t : Fin k, eta := Finset.sum_le_sum (fun t _ => hRn t)
    _ = (k : ℝ)*eta := by simp

theorem native_regular_limit_not_affine_required
    {B J k G : ℕ} {rho a C c : ℝ} {ns : ℕ → ℕ}
    (hns : Tendsto ns atTop atTop) {Ms : ℕ → TM}
    (hk : ∀ i, (Ms i).k=k) (hG : ∀ i, cellBits (Ms i)=G)
    {ws : ℕ → List Bool} {T : ℕ → ℕ}
    (clocks : ∀ i, ContractingStageClock B J rho a C (inputLength (ns i)) (T i))
    (hr : 0 ≤ rho) (hr1 : rho < 1) (ha : 0 ≤ a)
    (hP : ∀ i, 0 < (inputLength (ns i) : ℝ))
    (htime : ∀ i, (T i : ℝ) ≤ c*inputLength (ns i))
    (hhalt : ∀ i, HaltsAt (Ms i) (ws i) (T i))
    (hregular : ∀ t : Fin k, RegularClockHead clocks
      (fun i m => workTraj (Ms i) (ws i) m (Fin.cast (hk i).symm t)))
    (Q : Fin k → ℝ → ℝ)
    (hconv : ∀ t, TendstoUniformlyOn (fun i => rescaledTrajOf (Ms i) (ns i) (ws i)
      (Fin.cast (hk i).symm t)) (Q t) atTop (Icc 0 (c*G+1)))
    (hrequired : AffineTimeRequired Q (c*G+1)) : False := by
  have hreg : ∀ t : Fin k, RegularFlaggedClockHead clocks (fun _ _ => true)
      (fun i m => workTraj (Ms i) (ws i) m (Fin.cast (hk i).symm t)) := by
    simpa only [RegularFlaggedClockHead,RegularClockHead,ite_true] using hregular
  have hb := native_flagged_limit_budget (eta:=0) (eps:=fun _ => 0) hns hk hG clocks
    (fun _ _ => true) hr hr1 ha hP htime hhalt hreg tendsto_const_nhds
    (by intro i; simp [exceptionalTicks]) Q hconv hrequired
  have hG1 : 1 ≤ G := hG 0 ▸ cellBits_pos (Ms 0)
  have hGp : (0 : ℝ) < G := by exact_mod_cast (show 0 < G by omega)
  have hp : (0 : ℝ) < 1/(2*(G : ℝ)) := by positivity
  exact (not_le_of_gt hp) (by simpa using hb)

end TransposeFollowup.RegularMotion
