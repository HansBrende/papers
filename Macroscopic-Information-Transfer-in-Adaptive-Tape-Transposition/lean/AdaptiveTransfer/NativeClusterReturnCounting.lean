import AdaptiveTransfer.ClusterClassInvoice

/-! Finite union of actual coherent-cluster replay classes. The chart may
vary arbitrarily by input; only its computed rounded metadata is enumerated. -/
namespace AdaptiveTransfer
open Transpose MergeDepth BoundedNesting NativeRelations Finset LeanMachine
open scoped BigOperators

theorem native_cluster_return_union_bound {M : TM} {d b a q H J j : ℕ} {c error : ℝ}
    (hq : M.q + 1 ≤ 2 ^ q) (hA : M.g + 1 ≤ 2 ^ a)
    (D : Finset (Fin (d * d * b) → Bool))
    (correct : ∀ X : D, TransposesInput M d b c X.val)
    (charts : ∀ X : D, ClusterChart (trace M (List.ofFn X.val)).work
      (trace M (List.ofFn X.val)).haltTime error)
    (slabs : ∀ X : D, NativeValidClusterSlab (charts X) a c j)
    (returns : ∀ X : D, (offClusterReturns (trace M (List.ofFn X.val)).work
      (charts X).included (trace M (List.ofFn X.val)).haltTime H).card ≤ J) :
    (D.card : ℝ) ≤
      (clusterMetadataSize M.k (returnTime (d * d * b) c)
        (slabWidth (d * d * b) a c) (clusterRunCap M.k a c) j : ℝ) *
      ((2 : ℝ) ^ ((d * d * b : ℕ) - clusterSaving d b M.k a c +
          (clusterRunCap M.k a c : ℝ) * q + (a : ℝ) *
            (clusterRunCap M.k a c) * M.k * (max (4 * j + 2) (2 * H + 1) : ℕ)) *
        (returnSparseMenu M.k (returnTime (d * d * b) c) J (M.g + 1) : ℝ)) := by
  classical
  rcases D.eq_empty_or_nonempty with hD | hD
  · rw [hD, card_empty, Nat.cast_zero]
    positivity
  let P := d * d * b
  let T := returnTime P c
  let W := slabWidth P a c
  let N := clusterRunCap M.k a c
  let L := max (4 * j + 2) (2 * H + 1)
  let obs (X : D) := (slabs X).obs
  let X₀ : D := ⟨hD.choose, hD.choose_spec⟩
  let encoding (X : Fin P → Bool) : ClusterMetadata M.k T W N j :=
    if hX : X ∈ D then (obs ⟨X, hX⟩).encode else (obs X₀).encode
  have henc (X : D) : encoding X.val = (obs X).encode := by
    simp only [encoding, dite_eq_left X.property]
  let cost : ℝ := (2 : ℝ) ^ ((P : ℝ) - clusterSaving d b M.k a c + (N : ℝ) * q +
    (a : ℝ) * N * M.k * L) * (returnSparseMenu M.k T J (M.g + 1) : ℝ)
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
    let G := constantClusterClass F (fun X => correct (lift X)) (fun X => charts (lift X))
      (fun X => obs (lift X)) (fun X => returns (lift X)) X₁ hsame
    have hsave : clusterSaving d b M.k a c ≤ (G.omitted.card : ℝ) -
        (a : ℝ) * Fintype.card G.SnapshotDomain :=
      constantClusterClass_saving F (fun X => correct (lift X)) (fun X => charts (lift X))
        (fun X => obs (lift X)) (fun X => returns (lift X)) X₁ hsame a _ (slabs (lift X₁)).margin
    have hfr : ∀ h, (G.fringe h).card ≤ L := fun h =>
      ((charts (lift X₁)).fringe_card_le (obs (lift X₁)).ell W j h).trans (Nat.le_max_left _ _)
    exact G.saving_card_bound q a N L hq hA (obs (lift X₁)).run_cap hfr
      (Nat.le_max_right _ _) _ hsave
  have hcard : D.card = ∑ σ : ClusterMetadata M.k T W N j, (D.filter fun X => encoding X = σ).card :=
    card_eq_sum_card_fiberwise (fun _ _ => mem_univ _)
  have hsum : (D.card : ℝ) ≤ (clusterMetadataSize M.k T W N j : ℝ) * cost := by
    rw [hcard, Nat.cast_sum]
    calc
      _ ≤ ∑ _σ : ClusterMetadata M.k T W N j, cost := sum_le_sum (fun σ _ => hfibre σ)
      _ = _ := by simp only [sum_const, card_univ, clusterMetadata_card, nsmul_eq_mul]
  exact hsum

/-- Native bad-event bound, with chart and slab selection derived from each
original successful execution and the proved speed-k geometry. -/
theorem native_bad_cluster_return_bound {M : TM} {d b a q H J j : ℕ} {c error : ℝ}
    (hd : 1 ≤ d) (hb : 1 ≤ b) (hP : 2 ≤ d * d * b) (ha : 1 ≤ a) (hc : 1 ≤ c)
    (hq : M.q + 1 ≤ 2 ^ q) (hA : M.g + 1 ≤ 2 ^ a)
    (hsaving : 0 < clusterSaving d b M.k a c) (hj : error ≤ j) :
    ((nativeBadClusterReturns M d b c error H J).card : ℝ) ≤
      (clusterMetadataSize M.k (returnTime (d * d * b) c)
        (slabWidth (d * d * b) a c) (clusterRunCap M.k a c) j : ℝ) *
      ((2 : ℝ) ^ ((d * d * b : ℕ) - clusterSaving d b M.k a c +
          (clusterRunCap M.k a c : ℝ) * q + (a : ℝ) *
            (clusterRunCap M.k a c) * M.k * (max (4 * j + 2) (2 * H + 1) : ℕ)) *
        (returnSparseMenu M.k (returnTime (d * d * b) c) J (M.g + 1) : ℝ)) := by
  classical
  let D := nativeBadClusterReturns M d b c error H J
  have hD (X : D) : TransposesInput M d b c X.val ∧
      ∃ chart : ClusterChart (trace M (List.ofFn X.val)).work (trace M (List.ofFn X.val)).haltTime error,
        (offClusterReturns (trace M (List.ofFn X.val)).work chart.included
          (trace M (List.ofFn X.val)).haltTime H).card ≤ J := (mem_filter.mp X.property).2
  let charts (X : D) := (hD X).2.choose
  let slabs (X : D) : NativeValidClusterSlab (charts X) a c j :=
    (native_valid_cluster_exists hd hb hP ha hc (hD X).1 hsaving (charts X) hj).some
  exact native_cluster_return_union_bound hq hA D (fun X => (hD X).1) charts slabs
    (fun X => (hD X).2.choose_spec)

end AdaptiveTransfer
