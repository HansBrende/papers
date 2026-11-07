import TapeStorageRates.Conditioning
import AboveHalfRate.Incidence
import Mathlib.Data.Fintype.BigOperators

/-! # Repeating binary index partitions and paying for leftover coordinates

Copies retain the original helper relation. Leftover coordinates have no
helpers and are sent as raw bits, costing exactly one binary symbol each.
-/

namespace TapeStorageRates.PartitionPadding

open Finset DirectedRecovery MotionDepthCodes

set_option autoImplicit false

variable {V Y : Type*} [Fintype V] [DecidableEq V]

/-- Repeated base coordinates followed by isolated binary coordinates. -/
abbrev Coordinates (V : Type*) (copies leftover : ℕ) := (Fin copies × V) ⊕ Fin leftover

/-- The embedding of one copy into the padded coordinate type. -/
def copyEmbedding {c a : ℕ} (i : Fin c) : V ↪ Coordinates V c a where
  toFun v := Sum.inl (i, v)
  inj' := by intro u v h; exact congrArg Prod.snd (Sum.inl.inj h)

omit [Fintype V] [DecidableEq V] in
@[simp] theorem copyEmbedding_apply {c a : ℕ} (i : Fin c) (v : V) :
    copyEmbedding (a := a) i v = Sum.inl (i, v) := rfl

/-- The disjoint repeated relation, with empty helper sets on the padding. -/
def relation (N : V → Finset V) (c a : ℕ) : Coordinates V c a → Finset (Coordinates V c a)
  | Sum.inl q => (N q.2).map (copyEmbedding q.1)
  | Sum.inr _ => ∅

omit [Fintype V] [DecidableEq V] in
@[simp] theorem mem_relation_copy {c a : ℕ} (N : V → Finset V)
    (i j : Fin c) (p q : V) :
    Sum.inl (i, p) ∈ relation N c a (Sum.inl (j, q)) ↔ i = j ∧ p ∈ N q := by
  rw [relation, mem_map]
  constructor
  · rintro ⟨v, hv, heq⟩
    have h := Prod.mk.inj (Sum.inl.inj heq)
    exact ⟨h.1.symm, h.2 ▸ hv⟩
  · rintro ⟨rfl, hp⟩
    exact ⟨p, hp, rfl⟩

omit [Fintype V] [DecidableEq V] in
@[simp] theorem mem_relation_padding_left {c a : ℕ} (N : V → Finset V)
    (i : Fin a) (q : Coordinates V c a) : Sum.inr i ∉ relation N c a q := by
  cases q <;> simp [relation, copyEmbedding]

omit [Fintype V] [DecidableEq V] in
@[simp] theorem mem_relation_padding_right {c a : ℕ} (N : V → Finset V)
    (p : Coordinates V c a) (i : Fin a) : p ∉ relation N c a (Sum.inr i) := by
  simp [relation]

/-- One attained base label per copy, together with the raw padding bits. -/
def encoder {c a : ℕ} (f : (V → Bool) → Y) (x : Coordinates V c a → Bool) :
    (Fin c → Y) × (Fin a → Bool) :=
  (fun i => f (fun v => x (Sum.inl (i, v))), fun i => x (Sum.inr i))

omit [Fintype V] [DecidableEq V] in
/-- Full-cube recovery uses the original decoder separately in each copy. -/
theorem isIndexCode {c a : ℕ} {N : V → Finset V} {f : (V → Bool) → Y}
    (hf : IsIndexCode N f) : IsIndexCode (relation N c a) (encoder (c := c) (a := a) f) := by
  intro x y hxy q hhelp
  rcases q with ⟨i, q⟩ | q
  · apply hf (fun v => x (Sum.inl (i, v))) (fun v => y (Sum.inl (i, v)))
      (congrFun (congrArg Prod.fst hxy) i) q
    intro p hp
    exact hhelp (Sum.inl (i, p)) (mem_relation_copy N i i p q |>.mpr ⟨rfl, hp⟩)
  · exact congrFun (congrArg Prod.snd hxy) q

open Classical in
/-- Only attained base labels are counted. The independent raw leftover
bits contribute the exact factor `2^a`, regardless of the message alphabet. -/
theorem encoder_image_card_le (f : (V → Bool) → Y) (c a : ℕ) :
    (univ.image (encoder (c := c) (a := a) f)).card ≤
      (univ.image f).card ^ c * 2 ^ a := by
  classical
  let S := (univ : Finset (V → Bool)).image f
  have hsub : (univ.image (encoder (c := c) (a := a) f)) ⊆
      Fintype.piFinset (fun _ : Fin c => S) ×ˢ (univ : Finset (Fin a → Bool)) := by
    intro z hz
    obtain ⟨x, _, rfl⟩ := mem_image.mp hz
    apply mem_product.mpr
    refine ⟨?_, mem_univ _⟩
    apply Fintype.mem_piFinset.mpr
    intro i
    exact mem_image_of_mem f (mem_univ _)
  calc
    _ ≤ (Fintype.piFinset (fun _ : Fin c => S) ×ˢ (univ : Finset (Fin a → Bool))).card :=
      card_le_card hsub
    _ = _ := by simp [S, Fintype.card_piFinset]

omit [DecidableEq V] in
@[simp] theorem card_coordinates (c a : ℕ) :
    Fintype.card (Coordinates V c a) = c * Fintype.card V + a := by simp [Coordinates]

private theorem incoming_copy (N : V → Finset V) (c a : ℕ) (i : Fin c) (p : V) :
    (univ.filter fun q => Sum.inl (i, p) ∈ relation N c a q) =
      (univ.filter fun q => p ∈ N q).map (copyEmbedding (a := a) i) := by
  ext q
  rcases q with ⟨j, q⟩ | q
  · simp only [mem_filter, mem_univ, true_and, mem_relation_copy, mem_map,
      copyEmbedding_apply, Sum.inl.injEq, Prod.mk.injEq]
    aesop
  · simp

open Classical in
/-- Both incidence degrees retain the original cap; padding has degree zero. -/
theorem degree_le (N : V → Finset V) (c a Δ : ℕ)
    (hdeg : ∀ v, (pairedIncidenceGraph N).degree v ≤ Δ) :
    ∀ v, (pairedIncidenceGraph (relation N c a)).degree v ≤ Δ := by
  classical
  intro v
  refine AboveHalf.degree_le_of_bounds _ ?_ ?_ v
  · rintro (⟨i, q⟩ | q)
    · simpa only [relation, card_map] using
        (AboveHalf.degree_inr N q).symm.trans_le (hdeg (Sum.inr q))
    · simp [relation]
  · rintro (⟨i, p⟩ | p)
    · rw [incoming_copy, card_map]
      exact (AboveHalf.degree_inl N p).symm.trans_le (hdeg (Sum.inl p))
    · simp

/-- Forget the copy index; isolated coordinates may be sent to any base point. -/
def forget {c a : ℕ} (v₀ : V) : Coordinates V c a → V :=
  Sum.elim Prod.snd (fun _ => v₀)

omit [Fintype V] [DecidableEq V] in
private theorem mem_relation_forget {c a : ℕ} (N : V → Finset V) (v₀ : V)
    {p q : Coordinates V c a} (h : p ∈ relation N c a q) :
    forget v₀ p ∈ N (forget v₀ q) := by
  rcases q with ⟨i, q⟩ | q
  · obtain ⟨p', hp', rfl⟩ := mem_map.mp h
    exact hp'
  · exact False.elim (notMem_empty p h)

/-- A paired-graph homomorphism preserving the identity of each prescribed pair. -/
def forgetPorts {c a : ℕ} (N : V → Finset V) (v₀ : V) :
    pairedIncidenceGraph (relation N c a) →g pairedIncidenceGraph N where
  toFun := Sum.map (forget v₀) (forget v₀)
  map_rel' := by
    intro u v h
    rcases u with p | p <;> rcases v with q | q
    · exact False.elim h
    · exact mem_relation_forget N v₀ h
    · exact mem_relation_forget N v₀ h
    · exact False.elim h

omit [Fintype V] [DecidableEq V] in
/-- Repetition and isolated padding do not shorten the minimum paired distance. -/
theorem paired_far (N : V → Finset V) (c a r : ℕ) (v₀ : V)
    (hfar : ∀ q, ¬ (pairedIncidenceGraph N).edist (Sum.inl q) (Sum.inr q) ≤ r) :
    ∀ q, ¬ (pairedIncidenceGraph (relation N c a)).edist (Sum.inl q) (Sum.inr q) ≤ r := by
  intro q hq
  apply hfar (forget v₀ q)
  exact (AboveHalf.edist_map_le (forgetPorts N v₀) (Sum.inl q) (Sum.inr q)).trans hq

end TapeStorageRates.PartitionPadding
