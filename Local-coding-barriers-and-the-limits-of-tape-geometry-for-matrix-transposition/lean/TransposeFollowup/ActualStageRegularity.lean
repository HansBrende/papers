import TransposeFollowup.FrozenProfileRegularity

/-! Local regularity is required only on sequences of actual, positive-duration
stage occurrences. A positive limiting interval supplies that condition after
a proved finite prefix is discarded. Missing padded stages need no regularity. -/
namespace TransposeFollowup.RegularMotion
open Classical Set Filter Topology
open TransposeFollowup.AffineMotion
set_option autoImplicit false

def HasRegularStageSubsequences (a : ℝ) (V : ℕ → ℝ) (A L : ℕ → ℕ)
    (hs : ℕ → ℕ → ℤ) : Prop :=
  ∀ φ : ℕ → ℕ, StrictMono φ → (∀ i, 0 < L (φ i)) →
    Tendsto (fun i => V (φ i)) atTop atTop →
    ∃ (J : ℕ) (ψ : ℕ → ℕ) (q : ℝ → ℝ), StrictMono ψ ∧
      HasAffineIntervalCover J q a ∧
      TendstoUniformlyOn (fun i s =>
        ((hs (φ (ψ i)) (A (φ (ψ i))+min ⌊V (φ (ψ i))*s⌋₊ (L (φ (ψ i))))-
          hs (φ (ψ i)) (A (φ (ψ i))) : ℤ) : ℝ)/V (φ (ψ i))) q atTop (Icc 0 a)

theorem HasRegularStageSubsequences.subsequence {a : ℝ} {V : ℕ → ℝ}
    {A L : ℕ → ℕ} {hs : ℕ → ℕ → ℤ}
    (h : HasRegularStageSubsequences a V A L hs) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    HasRegularStageSubsequences a (fun i => V (φ i)) (fun i => A (φ i))
      (fun i => L (φ i)) (fun i => hs (φ i)) := by
  intro ψ hψ hL hV
  exact h (φ ∘ ψ) (hφ.comp hψ) hL hV

theorem positive_stage_affine_of_regular_occurrences
    {P V : ℕ → ℝ} {A E : ℕ → ℕ} {hs : ℕ → ℕ → ℤ} {fs : ℕ → ℝ → ℝ}
    {f : ℝ → ℝ} {H a l r v : ℝ}
    (hP : ∀ i, 0 < P i) (hPinf : Tendsto P atTop atTop)
    (ha : 0 ≤ a) (hAE : ∀ i, A i ≤ E i)
    (hf : ∀ i, LipschitzWith 1 (fs i)) (he : ∀ i (m : ℕ), fs i m=(hs i m : ℝ))
    (hconv : TendstoUniformlyOn (fun i => physicalPath (P i) (fs i)) f atTop (Icc 0 H))
    (hl : Tendsto (fun i => (A i : ℝ)/P i) atTop (𝓝 l))
    (hr : Tendsto (fun i => (E i : ℝ)/P i) atTop (𝓝 r))
    (hv : Tendsto (fun i => V i/P i) atTop (𝓝 v)) (hlr : l < r)
    (hend : ∀ i, (E i : ℝ) ≤ H*P i)
    (hbudget : ∀ i, ((E i-A i : ℕ) : ℝ) ≤ a*V i)
    (hregular : HasRegularStageSubsequences a V A (fun i => E i-A i) hs) :
    0 < v ∧ ∃ J, HasAffineIntervalCover J (fun s => f (l+v*s)) ((r-l)/v) := by
  have hL : Tendsto (fun i => ((E i-A i : ℕ) : ℝ)/P i) atTop (𝓝 (r-l)) := by
    apply (hr.sub hl).congr'
    exact Eventually.of_forall (fun i => by
      change (E i : ℝ)/P i-(A i : ℝ)/P i=((E i-A i : ℕ) : ℝ)/P i
      rw [Nat.cast_sub (hAE i),sub_div])
  have hcost : r-l ≤ a*v := by
    apply le_of_tendsto_of_tendsto' hL (hv.const_mul a)
    intro i
    simpa only [mul_div_assoc] using div_le_div_of_nonneg_right (hbudget i) (hP i).le
  have hvpos : 0 < v := by
    by_contra hvn
    have : a*v ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha (le_of_not_gt hvn)
    linarith
  have hactual : ∀ᶠ i in atTop, 0 < V i ∧ 0 < E i-A i := by
    filter_upwards [hv.eventually_const_lt hvpos,hL.eventually_const_lt (sub_pos.mpr hlr)]
      with i hiV hiL
    refine ⟨(div_pos_iff_of_pos_right (hP i)).mp hiV,?_⟩
    exact_mod_cast (div_pos_iff_of_pos_right (hP i)).mp hiL
  obtain ⟨N,hN⟩ := eventually_atTop.mp hactual
  let τ : ℕ → ℕ := fun i => i+N
  have hτ : StrictMono τ := by intro i j hij; exact Nat.add_lt_add_right hij N
  have hgood (i : ℕ) : 0 < V (τ i) ∧ 0 < E (τ i)-A (τ i) := hN (τ i) (by dsimp [τ]; omega)
  have hratio : Tendsto (fun i => ((E (τ i)-A (τ i) : ℕ) : ℝ)/V (τ i))
      atTop (𝓝 ((r-l)/v)) := by
    apply ((hL.comp hτ.tendsto_atTop).div (hv.comp hτ.tendsto_atTop) hvpos.ne').congr'
    exact Eventually.of_forall (fun i => by
      change (((E (τ i)-A (τ i) : ℕ) : ℝ)/P (τ i))/(V (τ i)/P (τ i))=
        ((E (τ i)-A (τ i) : ℕ) : ℝ)/V (τ i)
      field_simp [(hP (τ i)).ne',(hgood i).1.ne'])
  refine ⟨hvpos,?_⟩
  apply native_positive_stage_affine (fun i => hP (τ i)) (hPinf.comp hτ.tendsto_atTop)
    (fun i => (hgood i).1) (fun i => hf (τ i)) (fun i => he (τ i))
    (fun u hu => hτ.tendsto_atTop.eventually (hconv u hu))
    (hl.comp hτ.tendsto_atTop) (hv.comp hτ.tendsto_atTop) hratio hvpos
  · intro i
    simpa only [Nat.cast_sub (hAE (τ i)),add_sub_cancel] using hend (τ i)
  · exact fun i => hbudget (τ i)
  · exact hregular τ hτ (fun i => (hgood i).2)

end TransposeFollowup.RegularMotion
