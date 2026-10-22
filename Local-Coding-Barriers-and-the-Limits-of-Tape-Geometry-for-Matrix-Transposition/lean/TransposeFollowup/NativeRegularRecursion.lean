import TransposeFollowup.NativeExceptionalRecursion

/-! High-entropy native recursion exclusion. Regularity is quantified over
arbitrary eligible sequences of actual correct-set executions, so popular
representatives are eligible without fixing a common adaptive recursion tree.
The final theorem derives linear time from actual clock budgets. -/
namespace TransposeFollowup.RegularMotion
open Classical Set Filter Topology MeasureTheory Transpose Transpose.Tape Transpose.Tape.Impl
open TransposeFollowup.AffineMotion
set_option autoImplicit false

def HasRegularRecursiveExecutions {k : ℕ} (B J : ℕ) (rho a C : ℝ)
    (ns : ℕ → ℕ) (Ms : ℕ → TM) (Ws : ℕ → Set (List Bool))
    (hk : ∀ i, (Ms i).k=k) : Prop :=
  ∃ N : ℕ, ∀ φ : ℕ → ℕ, StrictMono φ → (∀ i, N ≤ φ i) →
    ∀ (ws : ℕ → List Bool) (T : ℕ → ℕ),
    (∀ i, ws i ∈ Ws (φ i)) → (∀ i, HaltsAt (Ms (φ i)) (ws i) (T i)) →
    (∀ i, 0 < (inputLength (ns (φ i)) : ℝ)) →
    ∃ clocks : ∀ i, ContractingStageClock B J rho a C (inputLength (ns (φ i))) (T i),
      ∀ t : Fin k, RegularClockHead clocks
        (fun i m => workTraj (Ms (φ i)) (ws i) m (Fin.cast (hk (φ i)).symm t))

theorem HasRegularRecursiveExecutions.flagged
    {B J k : ℕ} {rho a C : ℝ} {ns : ℕ → ℕ} {Ms : ℕ → TM}
    {Ws : ℕ → Set (List Bool)} {hk : ∀ i, (Ms i).k=k}
    (h : HasRegularRecursiveExecutions B J rho a C ns Ms Ws hk) :
    HasFlaggedRecursiveExecutions B J rho a C 0 (fun _ => 0) ns Ms Ws hk := by
  obtain ⟨N,h⟩ := h
  refine ⟨N,?_⟩
  intro φ hφ hN ws T hmem hhalt hP
  obtain ⟨clocks,hregular⟩ := h φ hφ hN ws T hmem hhalt hP
  refine ⟨clocks,(fun _ _ => true),?_,?_⟩
  · intro i
    simp [exceptionalTicks]
  · simpa only [RegularFlaggedClockHead,RegularClockHead,ite_true] using hregular

theorem no_native_fast_regular_recursion
    {B J k G : ℕ} {rho a C c : ℝ} {ns : ℕ → ℕ}
    (hns : Tendsto ns atTop atTop) {Ms : ℕ → TM}
    (hk : ∀ i, (Ms i).k=k) (hG : ∀ i, cellBits (Ms i)=G)
    (hq : Tendsto (fun i => (Nat.clog 2 ((Ms i).q+1) : ℝ)/inputLength (ns i)) atTop (𝓝 0))
    {Ws : ℕ → Set (List Bool)} {ms : ℕ → ℕ}
    (hm : ∀ᶠ i in atTop, 2^inputLength (ns i) ≤ 2^ms i*(Ws i).ncard)
    (hmL : Tendsto (fun i => (ms i : ℝ)/inputLength (ns i)) atTop (𝓝 0))
    (hfast : ∀ᶠ i in atTop, ∀ w ∈ Ws i, ∃ T : ℕ,
      (T : ℝ) ≤ c*inputLength (ns i) ∧ HaltsAt (Ms i) w T ∧
      ∃ A : Matrix, w=encode (ns i) (entryBits (ns i)) A ∧
        (run (Ms i) w T).outRev.reverse=encode (ns i) (entryBits (ns i)) (transpose A))
    (hr : 0 ≤ rho) (hr1 : rho < 1) (ha : 0 ≤ a)
    (hrec : HasRegularRecursiveExecutions B J rho a C ns Ms Ws hk) : False := by
  have hb := native_fast_flagged_recursion_budget hns hk hG hq hm hmL hfast
    hr hr1 ha tendsto_const_nhds hrec.flagged
  have hG1 : 1 ≤ G := hG 0 ▸ cellBits_pos (Ms 0)
  have hGp : (0 : ℝ) < G := by exact_mod_cast (show 0 < G by omega)
  have hp : (0 : ℝ) < 1/(2*(G : ℝ)) := by positivity
  exact (not_le_of_gt hp) (by simpa using hb)

theorem no_native_regular_recursion
    {B J k G : ℕ} {rho a C : ℝ} {ns : ℕ → ℕ}
    (hns : Tendsto ns atTop atTop) {Ms : ℕ → TM}
    (hk : ∀ i, (Ms i).k=k) (hG : ∀ i, cellBits (Ms i)=G)
    (hq : Tendsto (fun i => (Nat.clog 2 ((Ms i).q+1) : ℝ)/inputLength (ns i)) atTop (𝓝 0))
    {Ws : ℕ → Set (List Bool)} {ms : ℕ → ℕ}
    (hm : ∀ᶠ i in atTop, 2^inputLength (ns i) ≤ 2^ms i*(Ws i).ncard)
    (hmL : Tendsto (fun i => (ms i : ℝ)/inputLength (ns i)) atTop (𝓝 0))
    (hr : 0 ≤ rho) (hr1 : rho < 1) (ha : 0 ≤ a)
    (hcorrect : ∀ᶠ i in atTop, ∀ w ∈ Ws i, ∃ T : ℕ, HaltsAt (Ms i) w T ∧
      (∃ A : Matrix, w=encode (ns i) (entryBits (ns i)) A ∧
        (run (Ms i) w T).outRev.reverse=encode (ns i) (entryBits (ns i)) (transpose A)) ∧
      Nonempty (ContractingStageClock B J rho a C (inputLength (ns i)) T))
    (hrec : HasRegularRecursiveExecutions B J rho a C ns Ms Ws hk) : False := by
  have hb := (native_flagged_recursion_budget hns hk hG hq hm hmL hr hr1 ha
    hcorrect tendsto_const_nhds hrec.flagged).1
  have hG1 : 1 ≤ G := hG 0 ▸ cellBits_pos (Ms 0)
  have hGp : (0 : ℝ) < G := by exact_mod_cast (show 0 < G by omega)
  have hp : (0 : ℝ) < 1/(2*(G : ℝ)) := by positivity
  exact (not_le_of_gt hp) (by simpa using hb)

theorem no_uniform_regular_recursion
    {B J : ℕ} {rho a C : ℝ} {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop)
    (M : TM) {Ws : ℕ → Set (List Bool)} {ms : ℕ → ℕ}
    (hm : ∀ᶠ i in atTop, 2^inputLength (ns i) ≤ 2^ms i*(Ws i).ncard)
    (hmL : Tendsto (fun i => (ms i : ℝ)/inputLength (ns i)) atTop (𝓝 0))
    (hr : 0 ≤ rho) (hr1 : rho < 1) (ha : 0 ≤ a)
    (hcorrect : ∀ᶠ i in atTop, ∀ w ∈ Ws i, ∃ T : ℕ, HaltsAt M w T ∧
      (∃ A : Matrix, w=encode (ns i) (entryBits (ns i)) A ∧
        (run M w T).outRev.reverse=encode (ns i) (entryBits (ns i)) (transpose A)) ∧
      Nonempty (ContractingStageClock B J rho a C (inputLength (ns i)) T))
    (hrec : HasRegularRecursiveExecutions B J rho a C ns (fun _ => M) Ws (fun _ => rfl)) : False :=
  no_native_regular_recursion hns (fun _ => rfl) (fun _ => rfl)
    (tendsto_const_nhds.div_atTop (inputLength_tendsto hns)) hm hmL hr hr1 ha hcorrect hrec

end TransposeFollowup.RegularMotion
