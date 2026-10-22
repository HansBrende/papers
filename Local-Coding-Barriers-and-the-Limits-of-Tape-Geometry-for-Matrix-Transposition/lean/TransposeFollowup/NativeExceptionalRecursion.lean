import TransposeFollowup.NativeRecursiveLimit

/-! Quantitative native recursion obstruction with arbitrary exceptional
stages. The error sequence is fixed uniformly over the correct input family.
Popular representatives, actual halting, raw transpose correctness, nonuniform
state costs and physical-head normalization use the existing native chain. -/
namespace TransposeFollowup.RegularMotion
open Classical Set Filter Topology MeasureTheory Transpose Transpose.Tape Transpose.Tape.Impl
open TransposeFollowup.AffineMotion
set_option autoImplicit false

def HasFlaggedRecursiveExecutions {k : ℕ} (B J : ℕ) (rho a C eta : ℝ) (eps : ℕ → ℝ)
    (ns : ℕ → ℕ) (Ms : ℕ → TM) (Ws : ℕ → Set (List Bool))
    (hk : ∀ i, (Ms i).k=k) : Prop :=
  ∃ N : ℕ, ∀ φ : ℕ → ℕ, StrictMono φ → (∀ i, N ≤ φ i) →
    ∀ (ws : ℕ → List Bool) (T : ℕ → ℕ),
    (∀ i, ws i ∈ Ws (φ i)) → (∀ i, HaltsAt (Ms (φ i)) (ws i) (T i)) →
    (∀ i, 0 < (inputLength (ns (φ i)) : ℝ)) →
    ∃ (clocks : ∀ i, ContractingStageClock B J rho a C (inputLength (ns (φ i))) (T i))
      (good : ℕ → List (Fin B) × Fin J → Bool),
      (∀ i, (exceptionalTicks (clocks i) (good i) : ℝ)/inputLength (ns (φ i)) ≤ eta+eps (φ i)) ∧
      ∀ t : Fin k, RegularFlaggedClockHead clocks good
        (fun i m => workTraj (Ms (φ i)) (ws i) m (Fin.cast (hk (φ i)).symm t))

/-- The same executions, with exceptional ticks charged at each tree node. -/
def HasNodeBudgetRecursiveExecutions {k : ℕ} (B J : ℕ) (rho a C eta : ℝ)
    (ns : ℕ → ℕ) (Ms : ℕ → TM) (Ws : ℕ → Set (List Bool))
    (hk : ∀ i, (Ms i).k=k) : Prop :=
  ∃ N : ℕ, ∀ φ : ℕ → ℕ, StrictMono φ → (∀ i, N ≤ φ i) →
    ∀ (ws : ℕ → List Bool) (T : ℕ → ℕ),
    (∀ i, ws i ∈ Ws (φ i)) → (∀ i, HaltsAt (Ms (φ i)) (ws i) (T i)) →
    (∀ i, 0 < (inputLength (ns (φ i)) : ℝ)) →
    ∃ (clocks : ∀ i, ContractingStageClock B J rho a C (inputLength (ns (φ i))) (T i))
      (good : ℕ → List (Fin B) × Fin J → Bool),
      (∀ i w, (((Finset.univ.filter (fun t : Fin (T i) => good i ((clocks i).label t) ≠ true)).filter
        (fun t => ((clocks i).label t).1=w)).card : ℝ) ≤ eta*(clocks i).V w) ∧
      ∀ t : Fin k, RegularFlaggedClockHead clocks good
        (fun i m => workTraj (Ms (φ i)) (ws i) m (Fin.cast (hk (φ i)).symm t))

theorem HasNodeBudgetRecursiveExecutions.to_global
    {B J k : ℕ} {rho a C eta : ℝ} {ns : ℕ → ℕ} {Ms : ℕ → TM}
    {Ws : ℕ → Set (List Bool)} {hk : ∀ i, (Ms i).k=k}
    (h : HasNodeBudgetRecursiveExecutions B J rho a C eta ns Ms Ws hk)
    (hr : 0 ≤ rho) (hr1 : rho < 1) (heta : 0 ≤ eta) :
    HasFlaggedRecursiveExecutions B J rho a C (eta*C/(1-rho)) (fun _ => 0) ns Ms Ws hk := by
  obtain ⟨N,h⟩ := h
  refine ⟨N,?_⟩
  intro φ hφ hN ws T hw hT hP
  obtain ⟨clocks,good,hnode,hregular⟩ := h φ hφ hN ws T hw hT hP
  refine ⟨clocks,good,?_,hregular⟩
  intro i
  simpa only [add_zero] using
    exceptionalTicks_node_budget (clocks i) hr hr1 heta (hP i) (good i) (hnode i)

theorem native_fast_flagged_recursion_budget
    {B J k G : ℕ} {rho a C c eta : ℝ} {ns : ℕ → ℕ} {eps : ℕ → ℝ}
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
    (heps : Tendsto eps atTop (𝓝 0))
    (hrec : HasFlaggedRecursiveExecutions B J rho a C eta eps ns Ms Ws hk) :
    1/(2*(G : ℝ)) ≤ (k : ℝ)*eta := by
  obtain ⟨T,_,F,w,hclasses,_,_,⟨φ,hφ,Q,hconv⟩,hlim⟩ :=
    popular_affine_time_nonuniform hns hk hG hq hm hmL hfast
  obtain ⟨Nrec,hrec⟩ := hrec
  have hrequired := (hlim φ hφ Q hconv).2
  have hgood := ((hφ.tendsto_atTop.eventually hclasses).and
    ((inputLength_tendsto (hns.comp hφ.tendsto_atTop)).eventually_gt_atTop 0)).and
    (hφ.tendsto_atTop.eventually_ge_atTop Nrec)
  obtain ⟨N,hN⟩ := eventually_atTop.mp hgood
  let μ : ℕ → ℕ := fun i => φ (i+N)
  have hμ : StrictMono μ := by intro i j hij; exact hφ (Nat.add_lt_add_right hij N)
  have hi (i : ℕ) := hN (i+N) (by omega)
  have hmem (i : ℕ) : w (μ i) ∈ Ws (μ i) := (hi i).1.1.2.1 (hi i).1.1.1.1
  have hhalt (i : ℕ) : HaltsAt (Ms (μ i)) (w (μ i)) (T (μ i)) :=
    ((hi i).1.1.1.2 _ (hi i).1.1.1.1).2.1
  have hP (i : ℕ) : 0 < (inputLength (ns (μ i)) : ℝ) := (hi i).1.2
  obtain ⟨clocks,good,hbad,hregular⟩ := hrec μ hμ (fun i => (hi i).2)
    (fun i => w (μ i)) (fun i => T (μ i)) hmem hhalt hP
  apply native_flagged_limit_budget (hns.comp hμ.tendsto_atTop)
    (fun i => hk (μ i)) (fun i => hG (μ i)) clocks good hr hr1 ha hP
    (fun i => (hi i).1.1.2.2.1) hhalt hregular (heps.comp hμ.tendsto_atTop) hbad Q ?_ hrequired
  exact fun t u hu => (tendsto_add_atTop_nat N).eventually (hconv t u hu)

theorem native_flagged_recursion_budget
    {B J k G : ℕ} {rho a C eta : ℝ} {ns : ℕ → ℕ} {eps : ℕ → ℝ}
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
    (heps : Tendsto eps atTop (𝓝 0))
    (hrec : HasFlaggedRecursiveExecutions B J rho a C eta eps ns Ms Ws hk) :
    1/(2*(G : ℝ)) ≤ (k : ℝ)*eta ∧ 1/(2*(k : ℝ)*G) ≤ eta := by
  have hb : 1/(2*(G : ℝ)) ≤ (k : ℝ)*eta := by
    apply native_fast_flagged_recursion_budget (c:=a*C/(1-rho))
      hns hk hG hq hm hmL ?_ hr hr1 ha heps hrec
    filter_upwards [hcorrect] with i hi
    intro w hw
    obtain ⟨T,hT,hout,⟨clock⟩⟩ := hi w hw
    refine ⟨T,?_,hT,hout⟩
    have ht := stage_clock_total_time_bound clock.nonneg hr hr1 ha clock.children
      clock.label clock.A clock.E clock.bounded clock.partition clock.budget
    calc
      (T : ℝ) ≤ a*clock.V []/(1-rho) := ht
      _ ≤ a*(C*inputLength (ns i))/(1-rho) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left clock.root ha) (sub_pos.mpr hr1).le
      _ = (a*C/(1-rho))*inputLength (ns i) := by ring
  refine ⟨hb,?_⟩
  have hG1 : 1 ≤ G := hG 0 ▸ cellBits_pos (Ms 0)
  have hGp : (0 : ℝ) < G := by exact_mod_cast (show 0 < G by omega)
  have hkpos : (0 : ℝ) < k := by
    by_contra hn
    have hk0 : (k : ℝ)=0 := le_antisymm (le_of_not_gt hn) (Nat.cast_nonneg _)
    have hp : (0 : ℝ) < 1/(2*(G : ℝ)) := by positivity
    exact (not_le_of_gt hp) (by simpa only [hk0,zero_mul] using hb)
  calc
    1/(2*(k : ℝ)*G) = (1/(2*(G : ℝ)))/k := by ring
    _ ≤ eta := (div_le_iff₀ hkpos).mpr (by simpa only [mul_comm] using hb)

theorem uniform_flagged_recursion_budget
    {B J : ℕ} {rho a C eta : ℝ} {ns : ℕ → ℕ} {eps : ℕ → ℝ}
    (hns : Tendsto ns atTop atTop) (M : TM)
    {Ws : ℕ → Set (List Bool)} {ms : ℕ → ℕ}
    (hm : ∀ᶠ i in atTop, 2^inputLength (ns i) ≤ 2^ms i*(Ws i).ncard)
    (hmL : Tendsto (fun i => (ms i : ℝ)/inputLength (ns i)) atTop (𝓝 0))
    (hr : 0 ≤ rho) (hr1 : rho < 1) (ha : 0 ≤ a)
    (hcorrect : ∀ᶠ i in atTop, ∀ w ∈ Ws i, ∃ T : ℕ, HaltsAt M w T ∧
      (∃ A : Matrix, w=encode (ns i) (entryBits (ns i)) A ∧
        (run M w T).outRev.reverse=encode (ns i) (entryBits (ns i)) (transpose A)) ∧
      Nonempty (ContractingStageClock B J rho a C (inputLength (ns i)) T))
    (heps : Tendsto eps atTop (𝓝 0))
    (hrec : HasFlaggedRecursiveExecutions B J rho a C eta eps ns (fun _ => M) Ws (fun _ => rfl)) :
    1/(2*(cellBits M : ℝ)) ≤ (M.k : ℝ)*eta ∧ 1/(2*(M.k : ℝ)*cellBits M) ≤ eta :=
  native_flagged_recursion_budget hns (fun _ => rfl) (fun _ => rfl)
    (tendsto_const_nhds.div_atTop (inputLength_tendsto hns)) hm hmL hr hr1 ha hcorrect heps hrec

/-- Source210 §35: per-node exceptional work must have a positive total coefficient. -/
theorem native_node_budget_recursion_bound
    {B J k G : ℕ} {rho a C eta : ℝ} {ns : ℕ → ℕ}
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
    (heta : 0 ≤ eta)
    (hrec : HasNodeBudgetRecursiveExecutions B J rho a C eta ns Ms Ws hk) :
    1/(2*(G : ℝ)) ≤ (k : ℝ)*(eta*C/(1-rho)) ∧
      1/(2*(k : ℝ)*G) ≤ eta*C/(1-rho) :=
  native_flagged_recursion_budget hns hk hG hq hm hmL hr hr1 ha hcorrect
    tendsto_const_nhds (hrec.to_global hr hr1 heta)

end TransposeFollowup.RegularMotion
