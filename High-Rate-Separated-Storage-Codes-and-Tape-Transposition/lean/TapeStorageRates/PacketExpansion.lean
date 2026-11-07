import TapeStorageRates.PacketGeometry
import AboveHalfRate.BlowUp

/-! # Binary expansion on a standard finite coordinate set -/

namespace TapeStorageRates

open Finset DirectedRecovery MotionDepthCodes

set_option autoImplicit false

variable {U V A : Type*}

/-- Transport a recovery relation along a change of coordinate names. -/
def relabelRelation (e : U ≃ V) (N : U → Finset U) (q : V) : Finset V :=
  (N (e.symm q)).map e.toEmbedding

/-- The inverse relabeling of the two ports. -/
def relabelPorts (e : U ≃ V) (N : U → Finset U) :
    pairedIncidenceGraph (relabelRelation e N) ↪g pairedIncidenceGraph N :=
  pairedEmbedding e.symm.toEmbedding (fun p q => by simp [relabelRelation])

open Classical in
/-- Changing coordinate names preserves the code and its cardinality. -/
theorem relabel_storage_code (e : U ≃ V) {C : Finset (U → A)} {N : U → Finset U}
    (hC : IsStorageCode N C) :
    ∃ C' : Finset (V → A), IsStorageCode (relabelRelation e N) C' ∧ C'.card = C.card := by
  let f : (U → A) ↪ (V → A) := (e.arrowCongr (Equiv.refl A)).toEmbedding
  refine ⟨C.map f, ?_, card_map _⟩
  intro x hx y hy q hxy
  obtain ⟨u, hu, rfl⟩ := mem_map.mp hx
  obtain ⟨v, hv, rfl⟩ := mem_map.mp hy
  change u (e.symm q) = v (e.symm q)
  apply hC u hu v hv (e.symm q)
  intro i hi
  have h := hxy (e i) (mem_map.mpr ⟨i, hi, rfl⟩)
  simpa [f, Equiv.arrowCongr] using h

open Classical in
/-- Any injective binary packet encoding preserves the number of codewords and the minimum
paired distance. The binary coordinates are named by a single finite ordinal as required by
the headline, even when the packet coordinates are nested subtypes after trimming. -/
theorem exists_fin_binary_expansion [Fintype V] {s Δ r : ℕ} (enc : A ↪ (Fin s → Bool))
    {N : V → Finset V} {C : Finset (V → A)} (hC : IsStorageCode N C)
    (hdeg : ∀ v, (pairedIncidenceGraph N).degree v ≤ Δ)
    (hfar : ∀ q : V, ¬ (pairedIncidenceGraph N).edist (Sum.inl q) (Sum.inr q) ≤ r) :
    ∃ (N' : Fin (Fintype.card V * s) → Finset (Fin (Fintype.card V * s)))
      (C' : Finset (Fin (Fintype.card V * s) → Bool)),
      IsStorageCode N' C' ∧ C'.card = C.card ∧
      (∀ v, (pairedIncidenceGraph N').degree v ≤ s * Δ) ∧
      ∀ q, ¬ (pairedIncidenceGraph N').edist (Sum.inl q) (Sum.inr q) ≤ r := by
  let e : V × Fin s ≃ Fin (Fintype.card V * s) := Fintype.equivFinOfCardEq (by simp)
  let R := AboveHalf.blowUp N s
  obtain ⟨D, hD, hcard⟩ := relabel_storage_code e
    (AboveHalf.isStorageCode_blowCode hC enc.injective)
  refine ⟨relabelRelation e R, D, hD, hcard.trans (AboveHalf.card_blowCode enc.injective C), ?_, ?_⟩
  · intro v
    apply (degree_le_of_pairedEmbedding (relabelPorts e R) v).trans
    exact AboveHalf.degree_blowUp_le N (fun q => (AboveHalf.degree_inr N q).symm.trans_le (hdeg _))
      (fun q => (AboveHalf.degree_inl N q).symm.trans_le (hdeg _)) _
  · intro q h
    apply hfar (e.symm q).1
    exact (AboveHalf.edist_le_blowUp N (e.symm q)).trans
      ((AboveHalf.edist_map_le (relabelPorts e R).toHom (.inl q) (.inr q)).trans h)

end TapeStorageRates
