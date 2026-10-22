import TransposeFollowup.AllSizeOverlapExpansion
import TransposeFollowup.RationalSymmetricGraph
import TransposeFollowup.PaidPaddingLimits

/-! Complete native padding from a fixed rational continuous expander,
at every positive input dimension. The existence of that continuous
expander remains an explicit premise, not an unproved declaration or a numerical test. -/
namespace TransposeFollowup
open Classical MeasureTheory Set
set_option autoImplicit false

theorem rationalSymmetricGraph_vertex_expansion_all_sizes {c n : ℕ} (F : Fin c → RationalMobius)
    (hn : 0<n)
    (hmap : ∀ p,MapsTo (rationalFamilyMaps F p).map (rationalFamilyMaps F p).domain (Icc (0:ℝ) 1))
    (eps : ℝ) (heps : 0≤eps)
    (hforward : ∀ S : Set ℝ,MeasurableSet S → S⊆Icc (0:ℝ) 1 → volume.real S≤1/2 →
      (1+eps)*volume.real S≤volume.real (mapImageUnion (rationalFamilyMaps F) S))
    (S : Finset (Fin (2*n))) (hS : 2*S.card≤Fintype.card (Fin (2*n))) :
    eps/2*S.card≤(outsideNeighbors (overlapGraph (rationalFamilyMaps (rationalSymmetricFamily F)) n) S).card := by
  change eps/2*(S.card:ℝ)≤((outsideNeighbors (OrderedBipartite.graph
    (overlapEdges (rationalFamilyMaps (rationalSymmetricFamily F)) n)) S).card:ℝ)
  rw [← rationalFamilyEdges_eq (rationalSymmetricFamily F) n,rationalSymmetricEdges_eq]
  exact symmetrizedGraph_vertex_expansion_all_sizes (rationalFamilyMaps F) hn hmap eps heps hforward S hS

namespace PaidPadding
open FixedTapeCompiler Transpose.Tape Transpose.Tape.Impl Transpose.Tape.TSDiagram Filter Topology
variable {c : ℕ}

theorem continuous_uniform_computation_with_cut (F : Fin (c+1) → RationalMobius)
    (hmap : ∀ p,MapsTo (rationalFamilyMaps F p).map (rationalFamilyMaps F p).domain (Icc (0:ℝ) 1))
    (eps : ℝ) (heps : 0<eps)
    (hforward : ∀ S : Set ℝ,MeasurableSet S → S⊆Icc (0:ℝ) 1 → volume.real S≤1/2 →
      (1+eps)*volume.real S≤volume.real (mapImageUnion (rationalFamilyMaps F) S))
    : ∃ K extra : ℕ,∀ (M : Transpose.TM) (n : ℕ),1≤n → ∀ (w out : List Bool),w.length=Transpose.inputLength n →
      ∀ (t : ℕ),Transpose.ComputesWithin M w out t →
      ∃ T ≤ PaidPayload.coefficient (r:=c+1+c) (rationalSymmetricFamily F) K*w.length+t,
      ∃ d : Transpose.Config (machine (c:=c+1+c) (rationalSymmetricFamily F) K M extra),
        Transpose.stepN (machine (c:=c+1+c) (rationalSymmetricFamily F) K M extra) w T
          (Transpose.init (machine (c:=c+1+c) (rationalSymmetricFamily F) K M extra))=some d ∧
        Transpose.step (machine (c:=c+1+c) (rationalSymmetricFamily F) K M extra) w d=none ∧ d.outRev.reverse=out ∧
        CutIneq n 3 (blockSize 3 n) T 0 0 (paths (c:=c+1+c) (rationalSymmetricFamily F) K M extra w) := by
  obtain ⟨K,extra,h⟩:=uniform_computation_with_cut (c:=c+1+c) (rationalSymmetricFamily F) (eps/2) (by positivity)
  refine ⟨K,extra,?_⟩
  intro M n hn w out hw t ht
  apply h M n hn w out hw ?_ t ht
  intro S hS
  exact rationalSymmetricGraph_vertex_expansion_all_sizes F (by omega) hmap eps heps.le hforward S
    (by simpa only [Fintype.card_fin] using hS)

theorem continuous_uniform_linear_tasks_macrostar (F : Fin (c+1) → RationalMobius)
    (hmap : ∀ p,MapsTo (rationalFamilyMaps F p).map (rationalFamilyMaps F p).domain (Icc (0:ℝ) 1))
    (eps : ℝ) (heps : 0<eps)
    (hforward : ∀ S : Set ℝ,MeasurableSet S → S⊆Icc (0:ℝ) 1 → volume.real S≤1/2 →
      (1+eps)*volume.real S≤volume.real (mapImageUnion (rationalFamilyMaps F) S))
    (M : Transpose.TM) :
    ∃ K extra : ℕ,∀ (ns : ℕ → ℕ),Tendsto ns atTop atTop → (∀ i,1≤ns i) →
      ∀ (ws outs : ℕ → List Bool),(∀ i,(ws i).length=Transpose.inputLength (ns i)) →
      ∀ (a : ℕ),(∀ i,Transpose.ComputesWithin M (ws i) (outs i) (a*Transpose.inputLength (ns i))) →
      ∃ Ts : ℕ → ℕ,
        (∀ i,Ts i≤(PaidPayload.coefficient (r:=c+1+c) (rationalSymmetricFamily F) K+a)*Transpose.inputLength (ns i) ∧
          ∃ d : Transpose.Config (machine (c:=c+1+c) (rationalSymmetricFamily F) K M extra),
            Transpose.stepN (machine (c:=c+1+c) (rationalSymmetricFamily F) K M extra) (ws i) (Ts i)
              (Transpose.init (machine (c:=c+1+c) (rationalSymmetricFamily F) K M extra))=some d ∧
            Transpose.step (machine (c:=c+1+c) (rationalSymmetricFamily F) K M extra) (ws i) d=none ∧
            d.outRev.reverse=outs i ∧
            CutIneq (ns i) 3 (blockSize 3 (ns i)) (Ts i) 0 0 (paths (c:=c+1+c) (rationalSymmetricFamily F) K M extra (ws i))) ∧
        NativeRunLimits.Conclusion (machine (c:=c+1+c) (rationalSymmetricFamily F) K M extra) ns ws Ts
          (PaidPayload.coefficient (r:=c+1+c) (rationalSymmetricFamily F) K+a) := by
  obtain ⟨K,extra,h⟩:=uniform_linear_tasks_macrostar (c:=c+1+c) (rationalSymmetricFamily F) M (eps/2) (by positivity)
  refine ⟨K,extra,?_⟩
  intro ns hns hn ws outs hw a hc
  apply h ns hns hn ws outs hw a hc
  intro i S hS
  exact rationalSymmetricGraph_vertex_expansion_all_sizes F (by have := hn i;omega) hmap eps heps.le hforward S
    (by simpa only [Fintype.card_fin] using hS)

end PaidPadding
end TransposeFollowup
