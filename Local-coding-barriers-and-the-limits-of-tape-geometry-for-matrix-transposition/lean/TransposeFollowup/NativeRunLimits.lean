import Transpose.Tape.MStarWalk

/-! The original M* theorem applied to actual work-head runs, with zero
slack. This is reuse of the original limit proof, not a new limit theorem. -/
namespace TransposeFollowup.NativeRunLimits
open Transpose Transpose.Tape Transpose.Tape.Impl Transpose.Tape.TSDiagram
open MeasureTheory Filter Topology
open scoped ENNReal BigOperators
set_option autoImplicit false

def Conclusion (M : TM) (ns : ℕ → ℕ) (ws : ℕ → List Bool) (Ts : ℕ → ℕ) (C : ℕ) : Prop :=
  let c₀ : ℝ:=(C:ℝ)*cellBits M+1
  (∃ φ : ℕ → ℕ,StrictMono φ ∧ ∃ P : Fin M.k → ℝ → ℝ,∀ t,
    TendstoUniformlyOn (fun i => blockTraj (blockSize (cellBits M) (ns (φ i))) (ns (φ i))
      (fun τ => workTraj M (ws (φ i)) (min τ (Ts (φ i))) t)) (P t) atTop (Set.Icc 0 c₀)) ∧
  ∀ φ : ℕ → ℕ,StrictMono φ → ∀ P : Fin M.k → ℝ → ℝ,
    (∀ t,TendstoUniformlyOn (fun i => blockTraj (blockSize (cellBits M) (ns (φ i))) (ns (φ i))
      (fun τ => workTraj M (ws (φ i)) (min τ (Ts (φ i))) t)) (P t) atTop (Set.Icc 0 c₀)) →
    (∀ t,LipschitzOnWith 1 (P t) (Set.Icc 0 c₀)) ∧
    (∀ (θ : ℝ≥0∞) (S : Set ℝ) (β : ℝ → ℕ),FinUnionIcc S → PiecewiseConstOn β S c₀ →
      (∀ ell,volume {u | u ∈ Set.Icc 0 c₀ ∧ u ∉ S ∧ β u=ell} ≤ θ) →
      1 ≤ (∑ t,∫⁻ p,levelCross (P t) S β c₀ p)+2*θ+2*M.k*volume (S ∩ Set.Icc 0 c₀)) ∧
    1 ≤ ∑ t,∫⁻ p,levelExcess (P t) c₀ p ∧
    1+∑ t,volume (P t '' Set.Icc 0 c₀) ≤ M.k*ENNReal.ofReal c₀ ∧
    ¬ ∀ t,MonotoneOn (P t) (Set.Icc 0 c₀) ∨ AntitoneOn (P t) (Set.Icc 0 c₀)

theorem of_cut (M : TM) (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop)
    (ws : ℕ → List Bool) (Ts : ℕ → ℕ) (C : ℕ)
    (htime : ∀ i,Ts i ≤ C*inputLength (ns i))
    (hcut : ∀ i,CutIneq (ns i) (cellBits M) (blockSize (cellBits M) (ns i)) (Ts i) 0 0
      (fun t τ => workTraj M (ws i) τ t)) : Conclusion M ns ws Ts C := by
  have hu : ∀ᶠ i in atTop,∀ t,∀ τ<Ts i,
      |workTraj M (ws i) (τ+1) t-workTraj M (ws i) τ t| ≤ 1 :=
    Eventually.of_forall (fun i t τ _ => unitSteps_workTraj M (ws i) t τ)
  have ht : ∀ᶠ i in atTop,(Ts i:ℝ) ≤ (C:ℝ)*inputLength (ns i) := by
    apply Eventually.of_forall
    intro i
    exact_mod_cast htime i
  have hm:=theoremMStar_walk (k:=M.k) (G:=cellBits M) (c:=(C:ℝ)) (ns:=ns) (Ts:=Ts)
    (Ds:=fun _ => 0) (ss:=fun _ => 0) (hs:=fun i t τ => workTraj M (ws i) τ t)
    hns hu ht (Eventually.of_forall hcut) (by simp)
  exact ⟨hm.1 (Eventually.of_forall (fun _ _ => rfl)),hm.2⟩

end TransposeFollowup.NativeRunLimits
