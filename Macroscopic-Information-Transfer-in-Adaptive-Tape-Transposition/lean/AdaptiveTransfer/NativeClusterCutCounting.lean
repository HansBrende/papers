import AdaptiveTransfer.ClusterClassInvoice
import AdaptiveTransfer.UnrestrictedClusterClasses
import AdaptiveTransfer.CoreLocalCounting
import AdaptiveTransfer.NativeSlabCutCounting

/-! Exact local-cut union over computed cluster metadata. The cut separates
in the full original graph; no complementary-return count is assumed. -/
namespace AdaptiveTransfer
open Transpose MergeDepth BoundedNesting NativeRelations Finset LeanMachine
open scoped BigOperators

/-- Exact finite bound for an arbitrary set of timely correct native inputs,
each with any valid computed slab and an actual small original separator. -/
theorem native_cluster_cut_union_bound {M : TM} {d b a q H j r : ℕ} {c error : ℝ}
    (hq : M.q + 1 ≤ 2 ^ q) (hA : M.g + 1 ≤ 2 ^ a)
    (D : Finset (Fin (d * d * b) → Bool))
    (correct : ∀ X : D, TransposesInput M d b c X.val)
    (witness : ∀ X : D, NativeClusterCutWitness M d b a c error H j X.val)
    (hcut : ∀ X, (witness X).cut.card ≤ r) :
    (D.card : ℝ) ≤
      (clusterMetadataSize M.k (returnTime (d * d * b) c)
        (slabWidth (d * d * b) a c) (clusterRunCap M.k a c) j : ℝ) *
      ((2 : ℝ) ^ ((d * d * b : ℕ) - clusterSaving d b M.k a c +
          (clusterRunCap M.k a c : ℝ) * q + (a : ℝ) *
            (clusterRunCap M.k a c : ℝ) * M.k * (max (4 * j + 2) (2 * H + 1) : ℕ)) *
        (localCutMenu M.k (q + M.k * a + 2) (d * d * b)
          (returnTime (d * d * b) c) (clusterRunCap M.k a c) r : ℝ)) := by
  classical
  rcases D.eq_empty_or_nonempty with hD | hD
  · rw [hD, card_empty, Nat.cast_zero]
    positivity
  let P := d * d * b
  let T := returnTime P c
  let W := slabWidth P a c
  let N := clusterRunCap M.k a c
  let L := max (4 * j + 2) (2 * H + 1)
  let charts (X : D) := (witness X).chart
  let obs (X : D) := (witness X).slab.obs
  let X₀ : D := ⟨hD.choose, hD.choose_spec⟩
  let encoding (X : Fin P → Bool) : ClusterMetadata M.k T W N j :=
    if hX : X ∈ D then (obs ⟨X, hX⟩).encode else (obs X₀).encode
  have henc (X : D) : encoding X.val = (obs X).encode := by
    simp only [encoding, dite_eq_left X.property]
  let cost : ℝ := (2 : ℝ) ^ ((P : ℝ) - clusterSaving d b M.k a c + (N : ℝ) * q +
    (a : ℝ) * N * M.k * L) *
      (localCutMenu M.k (q + M.k * a + 2) P T N r : ℝ)
  have hfibre (σ : ClusterMetadata M.k T W N j) :
      ((D.filter fun X => encoding X = σ).card : ℝ) ≤ cost := by
    let F := D.filter fun X => encoding X = σ
    rcases F.eq_empty_or_nonempty with hF | hF
    · change (F.card : ℝ) ≤ cost
      rw [hF, card_empty, Nat.cast_zero]
      dsimp [cost]
      positivity
    let lift (X : F) : D := ⟨X.val, (mem_filter.mp X.property).1⟩
    let X₁ : F := ⟨hF.choose, hF.choose_spec⟩
    have hsame (X : F) : (obs (lift X)).encode = (obs (lift X₁)).encode := by
      rw [← henc (lift X), ← henc (lift X₁)]
      exact (mem_filter.mp X.property).2.trans (mem_filter.mp X₁.property).2.symm
    let G := unrestrictedClusterClass (H := H) F (fun X => correct (lift X)) (fun X => charts (lift X)) (fun X => obs (lift X)) X₁ hsame
    have hcompletion : G.Completion := unrestrictedClusterCompletion F (fun X => correct (lift X))
      (fun X => charts (lift X)) (fun X => obs (lift X)) X₁ hsame
      (fun X => (timely_native_data (correct (lift X))).1)
    have hN : (runStarts G.times).card ≤ N := (obs (lift X₁)).run_cap
    let cuts (X : G.inputs) : G.LocalCut X := {
      cut := (witness (lift X)).cut
      cut_lt := (witness (lift X)).cut_lt
      separates := by
        have ho := unrestrictedClusterClass_omitted (H := H) F (fun X => correct (lift X))
          (fun X => charts (lift X)) (fun X => obs (lift X)) X₁ hsame X
        have hf : G.cluster = (charts (lift X)).included := by
          change (charts (lift X₁)).included = (charts (lift X)).included
          have hs : (charts (lift X)).signature = (charts (lift X₁)).signature :=
            (obs (lift X)).signature_eq_of_encode_eq (hsame X)
          simp only [ClusterChart.included, hs]
        change IsMengerVertexCut _ _ (nativeDemandedOutputSteps _ _ _ _ G.omitted)
          (offClusterLowerEndpoints _ G.cluster _ H) _
        rw [ho, hf]
        exact (witness (lift X)).separates }
    have hsave : clusterSaving d b M.k a c ≤ (G.omitted.card : ℝ) -
        (a : ℝ) * Fintype.card G.SnapshotDomain :=
      constantClusterClass_saving F (fun X => correct (lift X)) (fun X => charts (lift X))
        (fun X => obs (lift X)) (le_unrestrictedClusterReturnCap (H := H) F (fun X => charts (lift X)))
        X₁ hsame a _ (witness (lift X₁)).slab.margin
    have hfr : ∀ h, (G.fringe h).card ≤ L := fun h =>
      ((charts (lift X₁)).fringe_card_le (obs (lift X₁)).ell W j h).trans (Nat.le_max_left _ _)
    exact G.local_saving_card_bound hcompletion N r hN cuts (fun X => hcut (lift X))
      q a L hq hA hfr (Nat.le_max_right _ _) _ hsave
  have hcard : D.card = ∑ σ : ClusterMetadata M.k T W N j, (D.filter fun X => encoding X = σ).card :=
    card_eq_sum_card_fiberwise (fun _ _ => mem_univ _)
  have hsum : (D.card : ℝ) ≤ (clusterMetadataSize M.k T W N j : ℝ) * cost := by
    rw [hcard, Nat.cast_sum]
    calc
      _ ≤ ∑ _σ : ClusterMetadata M.k T W N j, cost := sum_le_sum (fun σ _ => hfibre σ)
      _ = _ := by simp only [sum_const, card_univ, clusterMetadata_card, nsmul_eq_mul]
  exact hsum

/-- The actual bad event includes every input-dependent valid slab and cut.
No head, chunk, target set, or detailed trace is fixed across inputs. -/
theorem native_bad_cluster_cut_bound {M : TM} {d b a q H j r : ℕ} {c error : ℝ}
    (hq : M.q + 1 ≤ 2 ^ q) (hA : M.g + 1 ≤ 2 ^ a) :
    ((nativeBadClusterCuts M d b a c error H j r).card : ℝ) ≤
      (clusterMetadataSize M.k (returnTime (d * d * b) c)
        (slabWidth (d * d * b) a c) (clusterRunCap M.k a c) j : ℝ) *
      ((2 : ℝ) ^ ((d * d * b : ℕ) - clusterSaving d b M.k a c +
          (clusterRunCap M.k a c : ℝ) * q + (a : ℝ) *
            (clusterRunCap M.k a c : ℝ) * M.k * (max (4 * j + 2) (2 * H + 1) : ℕ)) *
        (localCutMenu M.k (q + M.k * a + 2) (d * d * b)
          (returnTime (d * d * b) c) (clusterRunCap M.k a c) r : ℝ)) := by
  classical
  let D := nativeBadClusterCuts M d b a c error H j r
  have hD (X : D) : TransposesInput M d b c X.val ∧
      ∃ w : NativeClusterCutWitness M d b a c error H j X.val, w.cut.card ≤ r :=
    (mem_filter.mp X.property).2
  exact native_cluster_cut_union_bound hq hA D (fun X => (hD X).1)
    (fun X => (hD X).2.choose) (fun X => (hD X).2.choose_spec)

end AdaptiveTransfer
