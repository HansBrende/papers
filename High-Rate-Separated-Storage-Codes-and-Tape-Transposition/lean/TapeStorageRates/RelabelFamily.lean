import TapeStorageRates.Statement
import TapeStorageRates.PacketExpansion

/-! # Separated families on arbitrary finite coordinate types -/

namespace TapeStorageRates

open Filter DirectedRecovery MotionDepthCodes

set_option autoImplicit false

open Classical in
/-- Coordinate relabeling preserves all family guarantees, including the
individual rates. This performs no alphabet expansion or coordinate deletion. -/
theorem exists_separated_family_of_finite_coordinates
    (V : ℕ → Type*) [∀ j, Fintype (V j)]
    (N : (j : ℕ) → V j → Finset (V j)) (C : (j : ℕ) → Finset (V j → Bool))
    {Δ : ℕ} (hpos : ∀ j, 0 < Fintype.card (V j))
    (hgrow : Tendsto (fun j => Fintype.card (V j)) atTop atTop)
    (hC : ∀ j, (C j).Nonempty) (hstorage : ∀ j, IsStorageCode (N j) (C j))
    (hdegree : ∀ j v, (pairedIncidenceGraph (N j)).degree v ≤ Δ)
    (hfar : ∀ r : ℕ, ∀ᶠ j in atTop, ∀ q : V j,
      ¬ (pairedIncidenceGraph (N j)).edist (Sum.inl q) (Sum.inr q) ≤ r) :
    ∃ F : SeparatedBinaryFamily Δ, ∀ j,
      F.length j = Fintype.card (V j) ∧ storageCodeRate (F.code j) = storageCodeRate (C j) := by
  let e (j : ℕ) := Fintype.equivFin (V j)
  have hex (j : ℕ) := relabel_storage_code (e j) (hstorage j)
  choose C' hstorage' hcard using hex
  let F : SeparatedBinaryFamily Δ := {
    length := fun j => Fintype.card (V j)
    length_pos := hpos
    length_tendsto := hgrow
    recovery := fun j => relabelRelation (e j) (N j)
    code := C'
    nonempty := fun j => Finset.card_pos.mp ((hcard j).symm ▸ (hC j).card_pos)
    storage := hstorage'
    degree_le := fun j v =>
      (degree_le_of_pairedEmbedding (relabelPorts (e j) (N j)) v).trans (hdegree j _)
    paired_far := fun r => by
      filter_upwards [hfar r] with j hj
      intro q hq
      exact hj ((e j).symm q)
        ((AboveHalf.edist_map_le (relabelPorts (e j) (N j)).toHom
          (Sum.inl q) (Sum.inr q)).trans hq) }
  refine ⟨F, fun j => ⟨rfl, ?_⟩⟩
  simp only [storageCodeRate, F, Fintype.card_fin, hcard]

end TapeStorageRates
