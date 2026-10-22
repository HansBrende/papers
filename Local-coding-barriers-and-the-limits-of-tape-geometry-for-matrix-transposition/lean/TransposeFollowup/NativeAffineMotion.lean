import TransposeFollowup.AffineTimeScaling
import Transpose.Tape.MStarRobust

/-! Native consequences of the affine-motion obstruction. The original
machine-to-limit and popular-class theorems are imported unchanged. Their
full nonuniform, high-entropy and adaptive execution scope is retained. -/
namespace TransposeFollowup.AffineMotion
open Classical Set Finset MeasureTheory Filter Topology Transpose Transpose.Tape Transpose.Tape.Impl
open scoped ENNReal BigOperators
set_option autoImplicit false

/-- Every collection of locally affine regular time regions omits total
length at least one half. This is a property of the actual limiting paths. -/
def AffineTimeRequired {k : ℕ} (P : Fin k → ℝ → ℝ) (H : ℝ) : Prop :=
  ∀ (R : Fin k → Set ℝ), (∀ t, R t ⊆ Icc 0 H) →
    (∀ t x, x ∈ R t → ∃ U : Set ℝ, IsOpen U ∧ x ∈ U ∧ U ⊆ R t ∧
      ∃ a b : ℝ, ∀ y ∈ U, P t y=a*y+b) →
    (1/2 : ℝ≥0∞) ≤ ∑ t, volume (Icc 0 H \ R t)

theorem affineTimeRequired_of_star {k : ℕ} {H : ℝ} (hH : 0 ≤ H)
    (P : Fin k → ℝ → ℝ) (hP : ∀ t, LipschitzOnWith 1 (P t) (Icc 0 H))
    (hs : SatisfiesStar P H) : AffineTimeRequired P H :=
  fun R hRI hl => star_half_le_locally_affine_omission hH P hP R hRI hl hs

theorem AffineTimeRequired.not_countable_affine_ae {k : ℕ} {H : ℝ}
    {P : Fin k → ℝ → ℝ} (h : AffineTimeRequired P H)
    (J : Fin k → ℕ → Set ℝ) (a b : Fin k → ℕ → ℝ)
    (hJo : ∀ t n, IsOpen (J t n)) (hJI : ∀ t n, J t n ⊆ Icc 0 H)
    (hPa : ∀ t n x, x ∈ J t n → P t x=a t n*x+b t n)
    (hE : ∀ t, volume (Icc 0 H \ ⋃ n, J t n)=0) : False := by
  have hb := h (fun t => ⋃ n, J t n) (fun t => Set.iUnion_subset (hJI t)) (by
    intro t x hx
    obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hx
    exact ⟨J t n,hJo t n,hn,Set.subset_iUnion (J t) n,a t n,b t n,hPa t n⟩)
  simp only [hE,Finset.sum_const_zero] at hb
  norm_num at hb

/-- The native path conclusion in physical time units, under the exact
change of units. No additional Lipschitz or finite-branch premise is needed. -/
theorem AffineTimeRequired.physical_omission {k : ℕ} {G H : ℝ}
    (hG : 0 < G) {f : Fin k → ℝ → ℝ}
    (h : AffineTimeRequired (fun t => scalePath G (f t)) (G*H))
    (R : Fin k → Set ℝ) (hRI : ∀ t, R t ⊆ Icc 0 H)
    (hlocal : ∀ t x, x ∈ R t → ∃ U : Set ℝ, IsOpen U ∧ x ∈ U ∧ U ⊆ R t ∧
      ∃ a b : ℝ, ∀ y ∈ U, f t y=a*y+b) :
    (1/(2*ENNReal.ofReal G) : ℝ≥0∞) ≤ ∑ t, volume (Icc 0 H \ R t) := by
  apply scale_omission_lower_bound hG R
  exact h (fun t => (fun u : ℝ => u/G) ⁻¹' R t)
    (fun t u hu => (div_mem_scaled_interval hG).mp (hRI t hu))
    (fun t => scale_local_affine hG (f t) (R t) (hlocal t))

/-- Nonnegativity of the time constant follows from actual nonnegative
halting times and unbounded input length; it is not a new assumption. -/
theorem linear_time_constant_nonneg {ns Ts : ℕ → ℕ} {c : ℝ}
    (hns : Tendsto ns atTop atTop)
    (htime : ∀ᶠ i in atTop, (Ts i : ℝ) ≤ c*inputLength (ns i)) : 0 ≤ c := by
  obtain ⟨i,hi,ht⟩ := (((inputLength_tendsto hns).eventually
    (eventually_gt_atTop (0 : ℝ))).and htime).exists
  have hT : (0 : ℝ) ≤ Ts i := Nat.cast_nonneg _
  nlinarith

theorem class_affine_time_nonuniform {k G : ℕ} {c : ℝ} {ns : ℕ → ℕ}
    (hns : Tendsto ns atTop atTop) {Ms : ℕ → TM} (hk : ∀ i, (Ms i).k = k)
    (hG : ∀ i, cellBits (Ms i) = G)
    (hq : Tendsto (fun i => (Nat.clog 2 ((Ms i).q + 1) : ℝ) / inputLength (ns i)) atTop (𝓝 0))
    {Ts Ds : ℕ → ℕ} {Fs : ℕ → Set (List Bool)} {ws : ℕ → List Bool}
    (hF : ∀ᶠ i in atTop,
      TraceClass (Ms i) (ns i) (entryBits (ns i)) (slotLen (Ms i) (ns i)) (Ts i) (Fs i) (ws i))
    (hD : ∀ᶠ i in atTop, 2 ^ inputLength (ns i) ≤ 2 ^ Ds i * (Fs i).ncard)
    (hDL : Tendsto (fun i => (Ds i : ℝ) / inputLength (ns i)) atTop (𝓝 0))
    (hcorr : ∀ᶠ i in atTop, ClassCorrect (Ms i) (ns i) (entryBits (ns i)) (Ts i) (Fs i))
    (htime : ∀ᶠ i in atTop, (Ts i : ℝ) ≤ c * inputLength (ns i)) :
    (∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ P : Fin k → ℝ → ℝ, ∀ t,
      TendstoUniformlyOn (fun i => rescaledTrajOf (Ms (φ i)) (ns (φ i)) (ws (φ i))
        (Fin.cast (hk (φ i)).symm t)) (P t) atTop (Set.Icc 0 (c * G + 1))) ∧
    ∀ φ : ℕ → ℕ, StrictMono φ → ∀ P : Fin k → ℝ → ℝ,
      (∀ t, TendstoUniformlyOn (fun i => rescaledTrajOf (Ms (φ i)) (ns (φ i)) (ws (φ i))
        (Fin.cast (hk (φ i)).symm t)) (P t) atTop (Set.Icc 0 (c * G + 1))) →
      (∀ t, LipschitzOnWith 1 (P t) (Set.Icc 0 (c * G + 1))) ∧
      AffineTimeRequired P (c * G + 1) := by
  obtain ⟨hex,hlim⟩ := theoremMStar_class_nonuniform hns hk hG hq hF hD hDL hcorr htime
  refine ⟨hex,fun φ hφ P hconv => ?_⟩
  obtain ⟨hlip,hstar⟩ := hlim φ hφ P hconv
  have hc : 0 ≤ c := linear_time_constant_nonneg hns htime
  exact ⟨hlip,affineTimeRequired_of_star (by positivity) P hlip
    (fun θ _ _ S β hS hβ hclass => hstar θ S β hS hβ hclass)⟩

theorem popular_affine_time_nonuniform {k G : ℕ} {c : ℝ} {ns : ℕ → ℕ}
    (hns : Tendsto ns atTop atTop) {Ms : ℕ → TM} (hk : ∀ i, (Ms i).k = k)
    (hG : ∀ i, cellBits (Ms i) = G)
    (hq : Tendsto (fun i => (Nat.clog 2 ((Ms i).q + 1) : ℝ) / inputLength (ns i)) atTop (𝓝 0))
    {Ws : ℕ → Set (List Bool)} {ms : ℕ → ℕ}
    (hm : ∀ᶠ i in atTop, 2 ^ inputLength (ns i) ≤ 2 ^ ms i * (Ws i).ncard)
    (hmL : Tendsto (fun i => (ms i : ℝ) / inputLength (ns i)) atTop (𝓝 0))
    (hfast : ∀ᶠ i in atTop, ∀ w ∈ Ws i, ∃ T : ℕ, (T : ℝ) ≤ c * inputLength (ns i) ∧
      HaltsAt (Ms i) w T ∧ ∃ A : Matrix, w = encode (ns i) (entryBits (ns i)) A ∧
        (run (Ms i) w T).outRev.reverse = encode (ns i) (entryBits (ns i)) (transpose A)) :
    ∃ (Ts Ds : ℕ → ℕ) (Fs : ℕ → Set (List Bool)) (ws : ℕ → List Bool),
      (∀ᶠ i in atTop,
        TraceClass (Ms i) (ns i) (entryBits (ns i)) (slotLen (Ms i) (ns i)) (Ts i) (Fs i) (ws i) ∧
          Fs i ⊆ Ws i ∧ (Ts i : ℝ) ≤ c * inputLength (ns i) ∧
          2 ^ inputLength (ns i) ≤ 2 ^ Ds i * (Fs i).ncard) ∧
      (∀ᶠ i in atTop, Ds i ≤ ms i + traceConst (Ms 0) c * ns i * entryBits (ns i)) ∧
      Tendsto (fun i => (Ds i : ℝ) / inputLength (ns i)) atTop (𝓝 0) ∧
      (∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ P : Fin k → ℝ → ℝ, ∀ t,
        TendstoUniformlyOn (fun i => rescaledTrajOf (Ms (φ i)) (ns (φ i)) (ws (φ i))
          (Fin.cast (hk (φ i)).symm t)) (P t) atTop (Set.Icc 0 (c * G + 1))) ∧
      ∀ φ : ℕ → ℕ, StrictMono φ → ∀ P : Fin k → ℝ → ℝ,
        (∀ t, TendstoUniformlyOn (fun i => rescaledTrajOf (Ms (φ i)) (ns (φ i)) (ws (φ i))
          (Fin.cast (hk (φ i)).symm t)) (P t) atTop (Set.Icc 0 (c * G + 1))) →
        (∀ t, LipschitzOnWith 1 (P t) (Set.Icc 0 (c * G + 1))) ∧
        AffineTimeRequired P (c * G + 1) := by
  obtain ⟨Ts,Ds,Fs,ws,hclasses,hD,hDL,hex,hlim⟩ :=
    theoremMStar_level_nonuniform hns hk hG hq hm hmL hfast
  have hc : 0 ≤ c := linear_time_constant_nonneg hns
    (hclasses.mono fun _ hi => hi.2.2.1)
  refine ⟨Ts,Ds,Fs,ws,hclasses,hD,hDL,hex,fun φ hφ P hconv => ?_⟩
  obtain ⟨hlip,hstar⟩ := hlim φ hφ P hconv
  exact ⟨hlip,affineTimeRequired_of_star (by positivity) P hlip
    (fun θ _ _ S β hS hβ hclass => hstar θ S β hS hβ hclass)⟩

theorem popular_affine_time_robust {M : TM} {c : ℝ} {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop)
    {Ws : ℕ → Set (List Bool)} {ms : ℕ → ℕ}
    (hm : ∀ᶠ i in atTop, 2 ^ inputLength (ns i) ≤ 2 ^ ms i * (Ws i).ncard)
    (hmL : Tendsto (fun i => (ms i : ℝ) / inputLength (ns i)) atTop (𝓝 0))
    (hfast : ∀ᶠ i in atTop, ∀ w ∈ Ws i, ∃ T : ℕ, (T : ℝ) ≤ c * inputLength (ns i) ∧
      HaltsAt M w T ∧ ∃ A : Matrix, w = encode (ns i) (entryBits (ns i)) A ∧
        (run M w T).outRev.reverse = encode (ns i) (entryBits (ns i)) (transpose A)) :
    ∃ (Ts Ds : ℕ → ℕ) (Fs : ℕ → Set (List Bool)) (ws : ℕ → List Bool),
      (∀ᶠ i in atTop,
        TraceClass M (ns i) (entryBits (ns i)) (slotLen M (ns i)) (Ts i) (Fs i) (ws i) ∧
          Fs i ⊆ Ws i ∧ (Ts i : ℝ) ≤ c * inputLength (ns i) ∧
          2 ^ inputLength (ns i) ≤ 2 ^ Ds i * (Fs i).ncard) ∧
      (∀ᶠ i in atTop, Ds i ≤ ms i + traceConst M c * ns i * entryBits (ns i)) ∧
      Tendsto (fun i => (Ds i : ℝ) / inputLength (ns i)) atTop (𝓝 0) ∧
      (∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ P : Fin M.k → ℝ → ℝ, ∀ t,
        TendstoUniformlyOn (fun i => rescaledTrajOf M (ns (φ i)) (ws (φ i)) t) (P t) atTop
          (Set.Icc 0 (horizon M c))) ∧
      ∀ φ : ℕ → ℕ, StrictMono φ → ∀ P : Fin M.k → ℝ → ℝ,
        (∀ t, TendstoUniformlyOn (fun i => rescaledTrajOf M (ns (φ i)) (ws (φ i)) t) (P t) atTop
          (Set.Icc 0 (horizon M c))) →
        (∀ t, LipschitzOnWith 1 (P t) (Set.Icc 0 (horizon M c))) ∧
        AffineTimeRequired P (horizon M c) :=
  popular_affine_time_nonuniform hns (Ms := fun _ => M) (fun _ => rfl) (fun _ => rfl)
    (tendsto_const_nhds.div_atTop (inputLength_tendsto hns)) hm hmL hfast

end TransposeFollowup.AffineMotion
