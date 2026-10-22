import TransposeFollowup.RecursiveAffineLimits

/-! An execution-clock interface containing only finite integer tick data and
its charged-volume budget. No limiting path or affine-cover assertion is a
field. The geometric theorem is imported and applied to these data. -/
namespace TransposeFollowup.RegularMotion
open Classical Set Filter Topology MeasureTheory
open scoped BigOperators
set_option autoImplicit false

structure ContractingStageClock (B J : ℕ) (rho a C P : ℝ) (T : ℕ) where
  V : List (Fin B) → ℝ
  label : Fin T → List (Fin B) × Fin J
  A : List (Fin B) → Fin J → ℕ
  E : List (Fin B) → Fin J → ℕ
  nonneg : ∀ w, 0 ≤ V w
  children : ∀ w, ∑ b : Fin B, V (w++[b]) ≤ rho*V w
  root : V [] ≤ C*P
  ordered : ∀ w j, A w j ≤ E w j
  bounded : ∀ w j, E w j ≤ T
  partition : ∀ w j (t : Fin T), (A w j ≤ t.val ∧ t.val < E w j) ↔ label t=(w,j)
  budget : ∀ w, ((∑ j : Fin J, (E w j-A w j) : ℕ) : ℝ) ≤ a*V w

def RegularClockHead {B J : ℕ} {rho a C : ℝ} {P : ℕ → ℝ} {T : ℕ → ℕ}
    (clocks : ∀ i, ContractingStageClock B J rho a C (P i) (T i))
    (hs : ℕ → ℕ → ℤ) : Prop :=
  ∀ w j, HasRegularStageSubsequences a (fun i => (clocks i).V w)
    (fun i => (clocks i).A w j) (fun i => (clocks i).E w j-(clocks i).A w j) hs

theorem clock_family_limit_locally_affine {B J : ℕ} {T : ℕ → ℕ} {P : ℕ → ℝ}
    {rho a C M : ℝ} {hs : ℕ → ℕ → ℤ} {fs : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (clocks : ∀ i, ContractingStageClock B J rho a C (P i) (T i))
    (hr : 0 ≤ rho) (hr1 : rho < 1) (ha : 0 ≤ a)
    (hP : ∀ i, 0 < P i) (hPinf : Tendsto P atTop atTop)
    (htime : ∀ i, (T i : ℝ)/P i ≤ M)
    (hf : ∀ i, LipschitzWith 1 (fs i)) (he : ∀ i (m : ℕ), fs i m=(hs i m : ℝ))
    (hconv : TendstoUniformlyOn (fun i => physicalPath (P i) (fs i)) f atTop (Icc 0 M))
    (hstop : ∀ i m, T i ≤ m → hs i m=hs i (T i)) (hregular : RegularClockHead clocks hs) :
    ∃ R : Set ℝ, IsOpen R ∧ R ⊆ Icc 0 M ∧ volume (Icc 0 M \ R)=0 ∧
      ∀ x ∈ R, ∃ U : Set ℝ, IsOpen U ∧ x ∈ U ∧ U ⊆ R ∧
        ∃ c d : ℝ, ∀ y ∈ U, f y=c*y+d :=
  regular_physical_limit_locally_affine (fun i => (clocks i).nonneg) hr hr1 ha hP hPinf
    (fun i => (clocks i).children) (fun i => (clocks i).root)
    (fun i => (clocks i).label) (fun i => (clocks i).A) (fun i => (clocks i).E)
    (fun i => (clocks i).ordered) (fun i => (clocks i).bounded)
    (fun i => (clocks i).partition) (fun i => (clocks i).budget) htime hf he hconv hstop hregular

end TransposeFollowup.RegularMotion
