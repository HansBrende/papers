import TransposeFollowup.AffineApproximationObstruction
import TransposeFollowup.NativePhysicalLimits

/-! The existing affine-time obstruction applied to physical-time samples.
The native normalization theorem supplies the change of units. A further
subsequence of bounded affine approximants suffices; a uniform bound on
the number of pieces across all subsequences is not required. -/
namespace TransposeFollowup.AffineMotion
open Classical Set Filter Topology MeasureTheory Transpose Transpose.Tape Transpose.Tape.Impl
open scoped ENNReal BigOperators
set_option autoImplicit false

theorem AffineTimeRequired.not_physical_pointwise_bounded_covers
    {k J : ℕ} {G H : ℝ} (hG : 0 < G) {P : Fin k → ℝ → ℝ}
    (h : AffineTimeRequired P H) (q : ℕ → Fin k → ℝ → ℝ)
    (hcover : ∀ᶠ i in atTop, ∀ t, HasAffineIntervalCover J (q i t) (H/G))
    (hconv : ∀ t x, x ∈ Icc 0 (H/G) →
      Tendsto (fun i => q i t x) atTop (𝓝 (P t (G*x)/G))) : False := by
  choose R _ hRI hnull hlocal using fun t =>
    local_affine_ae_of_eventual_bounded_covers
      (hcover.mono fun i hi => hi t) (hconv t)
  let f : Fin k → ℝ → ℝ := fun t x => P t (G*x)/G
  have hscale : (fun t => scalePath G (f t)) = P := by
    funext t x
    dsimp [scalePath,f]
    rw [show G*(x/G)=x by field_simp]
    field_simp
  have hrequired : AffineTimeRequired (fun t => scalePath G (f t)) (G*(H/G)) := by
    rw [hscale,show G*(H/G)=H by field_simp]
    exact h
  have hb := hrequired.physical_omission hG R hRI hlocal
  simp only [hnull,Finset.sum_const_zero] at hb
  have hp : (0 : ℝ≥0∞) < 1/(2*ENNReal.ofReal G) := by
    apply ENNReal.div_pos (by norm_num)
    exact ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top
  exact (not_le_of_gt hp) hb

/-- Pointwise approximation errors may converge at different rates at each
head and time. Geometry may depend on the selected correct input sequence and
on a further subsequence, exactly as in the uniform-error specialization. -/
theorem no_subsequential_physical_pointwise_affine_fast_approximation
    {k G : ℕ} {c : ℝ} {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop)
    {Ms : ℕ → TM} (hk : ∀ i, (Ms i).k = k) (hG : ∀ i, cellBits (Ms i) = G)
    (hq : Tendsto (fun i => (Nat.clog 2 ((Ms i).q+1) : ℝ)/inputLength (ns i)) atTop (𝓝 0))
    {Ws : ℕ → Set (List Bool)} {ms : ℕ → ℕ}
    (hm : ∀ᶠ i in atTop, 2^inputLength (ns i) ≤ 2^ms i*(Ws i).ncard)
    (hmL : Tendsto (fun i => (ms i : ℝ)/inputLength (ns i)) atTop (𝓝 0))
    (hfast : ∀ᶠ i in atTop, ∀ w ∈ Ws i, ∃ T : ℕ, (T : ℝ) ≤ c*inputLength (ns i) ∧
      HaltsAt (Ms i) w T ∧ ∃ A : Matrix, w = encode (ns i) (entryBits (ns i)) A ∧
        (run (Ms i) w T).outRev.reverse = encode (ns i) (entryBits (ns i)) (transpose A))
    (hgeometry : ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ (ws : ℕ → List Bool),
      (∀ᶠ i in atTop, ws i ∈ Ws i) →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ (J : ℕ) (q : ℕ → Fin k → ℝ → ℝ),
        (∀ᶠ i in atTop, ∀ t, HasAffineIntervalCover J (q i t) ((c*G+1)/G)) ∧
        ∀ t x, x ∈ Icc 0 ((c*G+1)/G) →
          Tendsto (fun i =>
            dist ((workTraj (Ms (φ (ψ i))) (ws (φ (ψ i)))
              ⌊(inputLength (ns (φ (ψ i))) : ℝ)*x⌋₊
              (Fin.cast (hk (φ (ψ i))).symm t) : ℝ)/inputLength (ns (φ (ψ i))))
              (q i t x)) atTop (𝓝 0)) : False := by
  obtain ⟨Ts,Ds,Fs,ws,hclasses,_,_,⟨φ,hφ,P,hconv⟩,hlim⟩ :=
    popular_affine_time_nonuniform hns hk hG hq hm hmL hfast
  have hrequired := (hlim φ hφ P hconv).2
  have hphys := RegularMotion.native_sampled_physical_limit (hns.comp hφ.tendsto_atTop)
    (fun i => Ms (φ i)) (fun i => hk (φ i)) (fun i => hG (φ i))
    (fun i => ws (φ i)) P hconv
  obtain ⟨ψ,hψ,J,q,hcover,happrox⟩ := hgeometry φ hφ ws
    (hclasses.mono fun _ hi => hi.2.1 hi.1.1)
  have hG1 : 1 ≤ G := hG 0 ▸ cellBits_pos (Ms 0)
  have hGp : (0 : ℝ) < G := by exact_mod_cast (show 0 < G by omega)
  apply hrequired.not_physical_pointwise_bounded_covers hGp q hcover
  intro t x hx
  exact (((hphys t).tendsto_at hx).comp hψ.tendsto_atTop).congr_dist
    (happrox t x hx)

/-- Geometry may depend on the selected inputs and on a further
subsequence. It is required only for sequences eventually in the correct sets.
All native heads, all executed phases and the physical
horizon are included in the approximation premise. -/
theorem no_subsequential_physical_affine_fast_approximation
    {k G : ℕ} {c : ℝ} {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop)
    {Ms : ℕ → TM} (hk : ∀ i, (Ms i).k = k) (hG : ∀ i, cellBits (Ms i) = G)
    (hq : Tendsto (fun i => (Nat.clog 2 ((Ms i).q+1) : ℝ)/inputLength (ns i)) atTop (𝓝 0))
    {Ws : ℕ → Set (List Bool)} {ms : ℕ → ℕ}
    (hm : ∀ᶠ i in atTop, 2^inputLength (ns i) ≤ 2^ms i*(Ws i).ncard)
    (hmL : Tendsto (fun i => (ms i : ℝ)/inputLength (ns i)) atTop (𝓝 0))
    (hfast : ∀ᶠ i in atTop, ∀ w ∈ Ws i, ∃ T : ℕ, (T : ℝ) ≤ c*inputLength (ns i) ∧
      HaltsAt (Ms i) w T ∧ ∃ A : Matrix, w = encode (ns i) (entryBits (ns i)) A ∧
        (run (Ms i) w T).outRev.reverse = encode (ns i) (entryBits (ns i)) (transpose A))
    (hgeometry : ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ (ws : ℕ → List Bool),
      (∀ᶠ i in atTop, ws i ∈ Ws i) →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ (J : ℕ) (e : ℕ → ℝ) (q : ℕ → Fin k → ℝ → ℝ),
        Tendsto e atTop (𝓝 0) ∧ ∀ᶠ i in atTop,
          (∀ t, HasAffineIntervalCover J (q i t) ((c*G+1)/G)) ∧
          ∀ t x, x ∈ Icc 0 ((c*G+1)/G) →
            dist ((workTraj (Ms (φ (ψ i))) (ws (φ (ψ i)))
              ⌊(inputLength (ns (φ (ψ i))) : ℝ)*x⌋₊
              (Fin.cast (hk (φ (ψ i))).symm t) : ℝ)/inputLength (ns (φ (ψ i))))
              (q i t x) ≤ e i) : False := by
  apply no_subsequential_physical_pointwise_affine_fast_approximation
    hns hk hG hq hm hmL hfast
  intro φ hφ ws hw
  obtain ⟨ψ,hψ,J,e,q,he,ha⟩ := hgeometry φ hφ ws hw
  refine ⟨ψ,hψ,J,q,ha.mono (fun i hi => hi.1),?_⟩
  intro t x hx
  exact squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg)
    (ha.mono fun i hi => hi.2 t x hx) he

end TransposeFollowup.AffineMotion
