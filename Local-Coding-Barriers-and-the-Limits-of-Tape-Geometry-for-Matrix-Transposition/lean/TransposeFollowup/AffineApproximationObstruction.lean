import TransposeFollowup.BoundedAffineCovers
import TransposeFollowup.NativeAffineMotion

/-! The bounded-piece approximation exclusion. Pointwise vanishing approximation
error suffices; the former uniform error bounds remain available as
specializations. No regularity of the limiting paths is assumed, and the
approximants need not be Lipschitz. -/
namespace TransposeFollowup.AffineMotion
open Classical Set Finset MeasureTheory Filter Topology Transpose Transpose.Tape Transpose.Tape.Impl
open scoped ENNReal BigOperators
set_option autoImplicit false

theorem AffineTimeRequired.not_pointwise_bounded_covers {k J : ℕ} {H : ℝ}
    {P : Fin k → ℝ → ℝ} (h : AffineTimeRequired P H)
    (q : ℕ → Fin k → ℝ → ℝ)
    (hcover : ∀ᶠ n in atTop, ∀ t, HasAffineIntervalCover J (q n t) H)
    (hconv : ∀ t x, x ∈ Icc 0 H →
      Tendsto (fun n => q n t x) atTop (𝓝 (P t x))) : False := by
  choose R hRo hRI hnull hlocal using fun t =>
    local_affine_ae_of_eventual_bounded_covers
      (hcover.mono fun n hn => hn t) (hconv t)
  have hb := h R hRI hlocal
  simp only [hnull,Finset.sum_const_zero] at hb
  norm_num at hb

/-- Pointwise vanishing error suffices. Neither one uniform error envelope nor
regularity of the approximants is needed. -/
theorem AffineTimeRequired.not_pointwise_affine_approximation {k J : ℕ} {H : ℝ}
    {P : Fin k → ℝ → ℝ} (h : AffineTimeRequired P H)
    (u q : ℕ → Fin k → ℝ → ℝ)
    (hconv : ∀ t x, x ∈ Icc 0 H → Tendsto (fun n => u n t x) atTop (𝓝 (P t x)))
    (hcover : ∀ᶠ n in atTop, ∀ t, HasAffineIntervalCover J (q n t) H)
    (happrox : ∀ t x, x ∈ Icc 0 H →
      Tendsto (fun n => dist (u n t x) (q n t x)) atTop (𝓝 0)) : False := by
  apply h.not_pointwise_bounded_covers q hcover
  intro t x hx
  exact (hconv t x hx).congr_dist (happrox t x hx)

theorem AffineTimeRequired.not_bounded_affine_approximation {k J : ℕ} {H : ℝ}
    {P : Fin k → ℝ → ℝ} (h : AffineTimeRequired P H)
    (u q : ℕ → Fin k → ℝ → ℝ)
    (hconv : ∀ t x, x ∈ Icc 0 H → Tendsto (fun n => u n t x) atTop (𝓝 (P t x)))
    (hcover : ∀ᶠ n in atTop, ∀ t, HasAffineIntervalCover J (q n t) H)
    {e : ℕ → ℝ} (he : Tendsto e atTop (𝓝 0))
    (happrox : ∀ᶠ n in atTop, ∀ t x, x ∈ Icc 0 H → dist (u n t x) (q n t x) ≤ e n) :
    False := by
  apply h.not_pointwise_affine_approximation u q hconv hcover
  intro t x hx
  exact squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg)
    (happrox.mono fun n hn => hn t x hx) he

theorem no_bounded_affine_class_approximation {k G : ℕ} {c : ℝ} {ns : ℕ → ℕ}
    (hns : Tendsto ns atTop atTop) {Ms : ℕ → TM} (hk : ∀ i, (Ms i).k = k)
    (hG : ∀ i, cellBits (Ms i) = G)
    (hq : Tendsto (fun i => (Nat.clog 2 ((Ms i).q + 1) : ℝ) / inputLength (ns i)) atTop (𝓝 0))
    {Ts Ds : ℕ → ℕ} {Fs : ℕ → Set (List Bool)} {ws : ℕ → List Bool}
    (hF : ∀ᶠ i in atTop,
      TraceClass (Ms i) (ns i) (entryBits (ns i)) (slotLen (Ms i) (ns i)) (Ts i) (Fs i) (ws i))
    (hD : ∀ᶠ i in atTop, 2 ^ inputLength (ns i) ≤ 2 ^ Ds i * (Fs i).ncard)
    (hDL : Tendsto (fun i => (Ds i : ℝ) / inputLength (ns i)) atTop (𝓝 0))
    (hcorr : ∀ᶠ i in atTop, ClassCorrect (Ms i) (ns i) (entryBits (ns i)) (Ts i) (Fs i))
    (htime : ∀ᶠ i in atTop, (Ts i : ℝ) ≤ c * inputLength (ns i))
    {J : ℕ} (q : ℕ → Fin k → ℝ → ℝ) (e : ℕ → ℝ)
    (hcover : ∀ᶠ i in atTop, ∀ t, HasAffineIntervalCover J (q i t) (c*G+1))
    (he : Tendsto e atTop (𝓝 0))
    (happrox : ∀ᶠ i in atTop, ∀ t x, x ∈ Icc 0 (c*G+1) →
      dist (rescaledTrajOf (Ms i) (ns i) (ws i) (Fin.cast (hk i).symm t) x)
        (q i t x) ≤ e i) : False := by
  obtain ⟨⟨φ,hφ,P,hconv⟩,hlim⟩ :=
    class_affine_time_nonuniform hns hk hG hq hF hD hDL hcorr htime
  exact ((hlim φ hφ P hconv).2).not_bounded_affine_approximation
    (fun n t => rescaledTrajOf (Ms (φ n)) (ns (φ n)) (ws (φ n))
      (Fin.cast (hk (φ n)).symm t)) (fun n t => q (φ n) t) (fun t x hx => (hconv t).tendsto_at hx)
    (hφ.tendsto_atTop.eventually hcover) (he.comp hφ.tendsto_atTop)
    (hφ.tendsto_atTop.eventually happrox)

theorem no_bounded_affine_fast_approximation {k G : ℕ} {c : ℝ} {ns : ℕ → ℕ}
    (hns : Tendsto ns atTop atTop) {Ms : ℕ → TM} (hk : ∀ i, (Ms i).k = k)
    (hG : ∀ i, cellBits (Ms i) = G)
    (hq : Tendsto (fun i => (Nat.clog 2 ((Ms i).q + 1) : ℝ) / inputLength (ns i)) atTop (𝓝 0))
    {Ws : ℕ → Set (List Bool)} {ms : ℕ → ℕ}
    (hm : ∀ᶠ i in atTop, 2 ^ inputLength (ns i) ≤ 2 ^ ms i * (Ws i).ncard)
    (hmL : Tendsto (fun i => (ms i : ℝ) / inputLength (ns i)) atTop (𝓝 0))
    (hfast : ∀ᶠ i in atTop, ∀ w ∈ Ws i, ∃ T : ℕ, (T : ℝ) ≤ c * inputLength (ns i) ∧
      HaltsAt (Ms i) w T ∧ ∃ A : Matrix, w = encode (ns i) (entryBits (ns i)) A ∧
        (run (Ms i) w T).outRev.reverse = encode (ns i) (entryBits (ns i)) (transpose A))
    {J : ℕ} (q : ℕ → List Bool → Fin k → ℝ → ℝ) (e : ℕ → ℝ)
    (hcover : ∀ᶠ i in atTop, ∀ w ∈ Ws i, ∀ t,
      HasAffineIntervalCover J (q i w t) (c*G+1))
    (he : Tendsto e atTop (𝓝 0))
    (happrox : ∀ᶠ i in atTop, ∀ w ∈ Ws i, ∀ t x, x ∈ Icc 0 (c*G+1) →
      dist (rescaledTrajOf (Ms i) (ns i) w (Fin.cast (hk i).symm t) x)
        (q i w t x) ≤ e i) : False := by
  obtain ⟨Ts,Ds,Fs,ws,hclasses,_,_,⟨φ,hφ,P,hconv⟩,hlim⟩ :=
    popular_affine_time_nonuniform hns hk hG hq hm hmL hfast
  have hw : ∀ᶠ i in atTop, ws i ∈ Ws i :=
    hclasses.mono fun i hi => hi.2.1 hi.1.1
  have hc : ∀ᶠ i in atTop, ∀ t,
      HasAffineIntervalCover J (q i (ws i) t) (c*G+1) :=
    (hw.and hcover).mono fun i hi => hi.2 (ws i) hi.1
  have ha : ∀ᶠ i in atTop, ∀ t x, x ∈ Icc 0 (c*G+1) →
      dist (rescaledTrajOf (Ms i) (ns i) (ws i) (Fin.cast (hk i).symm t) x)
        (q i (ws i) t x) ≤ e i :=
    (hw.and happrox).mono fun i hi => hi.2 (ws i) hi.1
  exact ((hlim φ hφ P hconv).2).not_bounded_affine_approximation
    (fun n t => rescaledTrajOf (Ms (φ n)) (ns (φ n)) (ws (φ n))
      (Fin.cast (hk (φ n)).symm t)) (fun n t => q (φ n) (ws (φ n)) t)
    (fun t x hx => (hconv t).tendsto_at hx)
    (hφ.tendsto_atTop.eventually hc) (he.comp hφ.tendsto_atTop)
    (hφ.tendsto_atTop.eventually ha)

end TransposeFollowup.AffineMotion
