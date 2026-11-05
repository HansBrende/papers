import MergeDepth.SkelUniformQ91
import AboveHalfRate.Incidence
import LeanMachine.IncidenceTrimming

/-! # Trimming a frozen packet schedule to a prescribed minimum paired distance -/

namespace TapeStorageRates

open Finset DirectedRecovery MergeDepth BoundedNesting

set_option autoImplicit false

/-- Coordinate embeddings that preserve and reflect incidences give embeddings of the two-port
graphs. One embedding handles both induced subrelations and bijective reindexings. -/
def pairedEmbedding {U V : Type*} (e : U ↪ V) {N : U → Finset U} {R : V → Finset V}
    (he : ∀ p q, p ∈ N q ↔ e p ∈ R (e q)) : pairedIncidenceGraph N ↪g pairedIncidenceGraph R where
  toEmbedding := e.sumMap e
  map_rel_iff' := by
    intro a b
    cases a with
    | inl p =>
      cases b with
      | inl u => rfl
      | inr q => exact (he p q).symm
    | inr q =>
      cases b with
      | inl p => exact (he p q).symm
      | inr u => rfl

open Classical in
theorem degree_le_of_pairedEmbedding {U V : Type*} [Fintype U] [Fintype V]
    {N : U → Finset U} {R : V → Finset V} (e : pairedIncidenceGraph N ↪g pairedIncidenceGraph R)
    (v : U ⊕ U) :
    (pairedIncidenceGraph N).degree v ≤ (pairedIncidenceGraph R).degree (e v) := by
  rw [← SimpleGraph.card_neighborSet_eq_degree, ← SimpleGraph.card_neighborSet_eq_degree]
  exact Fintype.card_le_of_embedding (e.mapNeighborSet v)

variable {V : Type*} [DecidableEq V]

/-- Inclusion of an induced set of coordinates preserves each of its two ports. -/
def inducedPortEmbedding (N : V → Finset V) (Q : Finset V) :
    pairedIncidenceGraph (inducedNeighborhood N Q) ↪g pairedIncidenceGraph N :=
  pairedEmbedding (Function.Embedding.subtype fun v => v ∈ Q)
    (fun _ _ => by simp [inducedNeighborhood])

open Classical in
/-- Removing all coordinates with a short paired path gives a growing-distance witness at any
specified radius. The remaining distances can only increase under this deletion. -/
theorem paired_far_on_complement [Fintype V] (N : V → Finset V) (r : ℕ)
    (q : ↥((shortPairedCoordinates N r)ᶜ : Finset V)) :
    ¬ (pairedIncidenceGraph (inducedNeighborhood N (shortPairedCoordinates N r)ᶜ)).edist
      (Sum.inl q) (Sum.inr q) ≤ r := by
  intro h
  apply (mem_compl.mp q.2)
  apply mem_filter.mpr
  refine ⟨mem_univ _, ?_⟩
  exact (AboveHalf.edist_map_le (inducedPortEmbedding N _).toHom (.inl q) (.inr q)).trans h

open Classical in
/-- Finite geometry at packet scale, with an arbitrary left-degree threshold and any target
radius. The two cardinality bounds count the coordinates lost at each deletion. The schedule
and packet width can vary freely, subject to the unit walks and the stated time and depth. -/
theorem packet_schedule_trim {k d b T D : ℕ} (hd : 2 ≤ d) (hb : 1 ≤ b)
    (z : Tp k → ℕ → ℤ) (hz : ∀ t, IsWalk (z t)) (Γ : Finset ℕ) (ot : ℕ → ℕ)
    (hdepth : ∀ π, IsDepPath (fun j => z (some (some j))) T π → LinNet.GFree Γ π →
      π.length ≤ D + 1)
    (hot : ∀ q : Fin (d*d*b), ot (tpos d b q) < T ∧ (tpos d b q : ℤ) = z (some none) (ot (tpos d b q)))
    {c : ℝ} (hc : 0 ≤ c) (htime : (T : ℝ) ≤ c * (d*d*b + 1))
    (θ r : ℕ) :
    let N := coneRel 1 z T Γ ot (fun q : Fin (d*d*b) => tpos d b q)
    let B := ∑ h ∈ range (D + 1), (k + 1) ^ h
    ∃ (Q : Finset (Fin (d*d*b))) (U : Finset Q),
      Qᶜ.card * (θ + 1) ≤ B * (d*d*b) ∧
      (Uᶜ.card : ℝ) ≤ pathPackingConstant r (max B θ)
        (fun j => 2 * j * c * B * (k + 2) * ((k + 2 : ℕ) + 1) + 3) *
          ((d : ℝ)^2 * b / Real.logb 2 d) ∧
      (∀ v, (pairedIncidenceGraph (inducedNeighborhood (inducedNeighborhood N Q) U)).degree v ≤ max B θ) ∧
      ∀ q : U, ¬ (pairedIncidenceGraph (inducedNeighborhood (inducedNeighborhood N Q) U)).edist
        (Sum.inl q) (Sum.inr q) ≤ r := by
  intro N B
  have hpath : ∀ π, IsDepPath (fun j => skel 1 (z (some (some j)))) T π →
      LinNet.GFree Γ π → π.length ≤ D + 1 := by simpa only [skel_one] using hdepth
  have hcard : ∀ q, (N q).card ≤ B := fun q => by
    simpa only [one_mul] using card_coneRel_le (by decide : 1 ≤ 1) hpath ot
      (fun j : Fin (d*d*b) => tpos d b j) q
  let Q := (heavyCoords N θ)ᶜ
  have hdeg := (paid_trimming N θ hcard).2
  let E := fun p q => p ∈ N q
  have hright (q) : LeanMachine.IncidenceTrimming.rightDegree E q ≤ B := by
    simpa [LeanMachine.IncidenceTrimming.rightDegree, E] using hcard q
  have hcount := LeanMachine.IncidenceTrimming.heavy_card_mul_succ_le E θ B hright
  have heq : LeanMachine.IncidenceTrimming.heavy E θ = heavyCoords N θ := by
    ext p
    simp [LeanMachine.IncidenceTrimming.heavy, LeanMachine.IncidenceTrimming.leftDegree,
      heavyCoords, degree_inl, E]
  rw [heq] at hcount
  let R := inducedNeighborhood N Q
  let U := (shortPairedCoordinates R r)ᶜ
  refine ⟨Q, U, by simpa [Q] using hcount, ?_, ?_, paired_far_on_complement R r⟩
  · have hwin : 2 * 1 - 1 ≤ d * b := by have := Nat.mul_le_mul hd hb; omega
    have h := skel_paired_packing (by decide : 1 ≤ 1) hd hb hwin hz hpath ot
      (by simpa using hot) hc htime Q r (max B θ) hdeg
    simpa [U, R, N, B] using h
  · intro v
    exact (degree_le_of_pairedEmbedding (inducedPortEmbedding R U) v).trans (hdeg _)

end TapeStorageRates
