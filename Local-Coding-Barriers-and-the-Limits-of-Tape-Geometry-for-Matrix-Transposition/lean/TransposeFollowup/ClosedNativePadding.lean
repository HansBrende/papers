import TransposeFollowup.ClosedRationalExpansion
import TransposeFollowup.ContinuousNativePadding

/-! Graph and fully paid native adapters for the closed-domain expansion API.
The analytic closed/open image comparison remains independent of the compiler. -/
namespace TransposeFollowup
open Classical Set MeasureTheory
set_option autoImplicit false

namespace RationalUnitMobius

theorem restricted_vertex_expansion {c n : ℕ} (F : Fin c → RationalUnitMobius) (hn : 0<n)
    (eps : ℝ) (heps : 0≤eps)
    (hexp : ∀ A : Set ℝ,MeasurableSet A → A⊆Icc (0:ℝ) 1 → volume.real A≤1/2 →
      (1+eps)*volume.real A≤volume.real (restrictedImageUnion F A))
    (S : Finset (Fin (2*n))) (hS : 2*S.card≤Fintype.card (Fin (2*n))) :
    eps/2*S.card≤(outsideNeighbors (overlapGraph
      (rationalFamilyMaps (rationalSymmetricFamily (clippedFamily F))) n) S).card :=
  rationalSymmetricGraph_vertex_expansion_all_sizes (clippedFamily F) hn
    (clippedFamily_mapsTo F) eps heps (restricted_expansion_to_open F eps hexp) S hS

end RationalUnitMobius

namespace PaidPadding
open FixedTapeCompiler Transpose.Tape Transpose.Tape.Impl Transpose.Tape.TSDiagram Filter Topology
open RationalUnitMobius
variable {c : ℕ}

theorem restricted_uniform_computation_with_cut (F : Fin (c+1) → RationalUnitMobius)
    (eps : ℝ) (heps : 0<eps)
    (hexp : ∀ S : Set ℝ,MeasurableSet S → S⊆Icc (0:ℝ) 1 → volume.real S≤1/2 →
      (1+eps)*volume.real S≤volume.real (restrictedImageUnion F S)) (M : Transpose.TM) :
    ∃ K extra : ℕ,∀ (n : ℕ),1≤n → ∀ (w out : List Bool),w.length=Transpose.inputLength n →
      ∀ (t : ℕ),Transpose.ComputesWithin M w out t →
      ∃ T ≤ PaidPayload.coefficient (r:=c+1+c) (rationalSymmetricFamily (clippedFamily F)) K*w.length+t,
      ∃ d : Transpose.Config (machine (c:=c+1+c) (rationalSymmetricFamily (clippedFamily F)) K M extra),
        Transpose.stepN (machine (c:=c+1+c) (rationalSymmetricFamily (clippedFamily F)) K M extra) w T
          (Transpose.init (machine (c:=c+1+c) (rationalSymmetricFamily (clippedFamily F)) K M extra))=some d ∧
        Transpose.step (machine (c:=c+1+c) (rationalSymmetricFamily (clippedFamily F)) K M extra) w d=none ∧
        d.outRev.reverse=out ∧
        CutIneq n 3 (blockSize 3 n) T 0 0
          (paths (c:=c+1+c) (rationalSymmetricFamily (clippedFamily F)) K M extra w) := by
  obtain ⟨K, extra, h⟩ := continuous_uniform_computation_with_cut (clippedFamily F)
    (clippedFamily_mapsTo F) eps heps (restricted_expansion_to_open F eps hexp)
  exact ⟨K, extra, h M⟩

theorem restricted_uniform_linear_tasks_macrostar (F : Fin (c+1) → RationalUnitMobius)
    (eps : ℝ) (heps : 0<eps)
    (hexp : ∀ S : Set ℝ,MeasurableSet S → S⊆Icc (0:ℝ) 1 → volume.real S≤1/2 →
      (1+eps)*volume.real S≤volume.real (restrictedImageUnion F S)) (M : Transpose.TM) :
    ∃ K extra : ℕ,∀ (ns : ℕ → ℕ),Tendsto ns atTop atTop → (∀ i,1≤ns i) →
      ∀ (ws outs : ℕ → List Bool),(∀ i,(ws i).length=Transpose.inputLength (ns i)) →
      ∀ (a : ℕ),(∀ i,Transpose.ComputesWithin M (ws i) (outs i) (a*Transpose.inputLength (ns i))) →
      ∃ Ts : ℕ → ℕ,
        (∀ i,Ts i≤(PaidPayload.coefficient (r:=c+1+c) (rationalSymmetricFamily (clippedFamily F)) K+a)*
          Transpose.inputLength (ns i) ∧
          ∃ d : Transpose.Config (machine (c:=c+1+c) (rationalSymmetricFamily (clippedFamily F)) K M extra),
            Transpose.stepN (machine (c:=c+1+c) (rationalSymmetricFamily (clippedFamily F)) K M extra)
              (ws i) (Ts i)
              (Transpose.init (machine (c:=c+1+c) (rationalSymmetricFamily (clippedFamily F)) K M extra))=some d ∧
            Transpose.step (machine (c:=c+1+c) (rationalSymmetricFamily (clippedFamily F)) K M extra)
              (ws i) d=none ∧ d.outRev.reverse=outs i ∧
            CutIneq (ns i) 3 (blockSize 3 (ns i)) (Ts i) 0 0
              (paths (c:=c+1+c) (rationalSymmetricFamily (clippedFamily F)) K M extra (ws i))) ∧
        NativeRunLimits.Conclusion
          (machine (c:=c+1+c) (rationalSymmetricFamily (clippedFamily F)) K M extra) ns ws Ts
          (PaidPayload.coefficient (r:=c+1+c) (rationalSymmetricFamily (clippedFamily F)) K+a) :=
  continuous_uniform_linear_tasks_macrostar (clippedFamily F) (clippedFamily_mapsTo F)
    eps heps (restricted_expansion_to_open F eps hexp) M

end PaidPadding
end TransposeFollowup
