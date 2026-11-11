import AdaptiveTransfer.TransferEntryCoordinates
import AdaptiveTransfer.TransferEntryMaximum
import AdaptiveTransfer.TransferInputGeometry

/-! An actual frozen native trace produces nonlinear entry codes after one
joint guard/exterior conditioning. The only transport premise is literal
input-cone containment; recovery and the cardinal invoice are conclusions. -/

namespace AdaptiveTransfer.TransferEntry
open Finset Transpose Transpose.Tape MergeDepth DirectedRecovery MotionDepthCodes
attribute [local instance] Classical.propDecidable

noncomputable def record {n b : ℕ} (M : TM) (J : Finset (Fin n)) (s : ℕ)
    (Γ : Finset ℕ) (X : Fin (n * b) → Bool) :
    (Γ → Value M) × (↑(retainedBits J b s)ᶜ → Bool) :=
  (fullCutRecord M Γ X, fun p => X p.val)

noncomputable def cell {n b : ℕ} (M : TM) (J : Finset (Fin n)) (s : ℕ)
    (Γ : Finset ℕ) (S : Finset (Fin (n * b) → Bool))
    (z : (Γ → Value M) × (↑(retainedBits J b s)ᶜ → Bool)) : Finset (Fin (n * b) → Bool) :=
  S.filter fun X => record M J s Γ X = z

noncomputable def cellCode {n b : ℕ} (M : TM) (J : Finset (Fin n)) (s : ℕ)
    (Γ : Finset ℕ) (S : Finset (Fin (n * b) → Bool))
    (z : (Γ → Value M) × (↑(retainedBits J b s)ᶜ → Bool)) :
    Finset (J → Fin (b - 6 * s) → Bool) :=
  (cell M J s Γ S z).image (project J s)

theorem cellCode_card {n b : ℕ} (M : TM) (J : Finset (Fin n)) (s : ℕ)
    (Γ : Finset ℕ) (S : Finset (Fin (n * b) → Bool)) (z) :
    (cellCode M J s Γ S z).card = (cell M J s Γ S z).card := by
  apply card_image_of_injOn
  intro X hX Y hY heq
  apply project_injective_of_exterior (hproj := heq)
  intro p hp
  have hh := (mem_filter.mp hX).2.trans (mem_filter.mp hY).2.symm
  exact congrFun (congrArg Prod.snd hh) ⟨p, mem_compl.mpr hp⟩

theorem record_range_card_le {n b : ℕ} (M : TM) (J : Finset (Fin n)) (s : ℕ)
    (Γ : Finset ℕ) (S : Finset (Fin (n * b) → Bool)) :
    (S.image (record M J s Γ)).card ≤
      2 ^ (valueWidth M * Γ.card + (n * b - (b - 6 * s) * J.card)) := by
  calc
    _ ≤ Fintype.card ((Γ → Value M) × (↑(retainedBits J b s)ᶜ → Bool)) := card_le_univ _
    _ = Fintype.card (Value M) ^ Γ.card * 2 ^ (n * b - (b - 6 * s) * J.card) := by
      simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_coe,
        Fintype.card_bool, card_compl, Fintype.card_fin, retainedBits_card]
    _ ≤ (2 ^ valueWidth M) ^ Γ.card * 2 ^ (n * b - (b - 6 * s) * J.card) := by
      exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (card_value_le M) _)
    _ = _ := by rw [← pow_mul, ← pow_add]

section Recovery
variable {M : TM} {n b s T : ℕ} {τ : Trace M.k}
  (S : Finset (Fin (n * b) → Bool)) (J : Finset (Fin n)) (Γ : Finset ℕ)
  (root : Fin (n * b) → ℕ)
  (cones : Fin (n * b) → Finset (Fin (n * b)))
  (sourceTarget : Fin (n * b) → Fin (n * b))
  (hroot : ∀ p ∈ retainedBits J b s, root p < T)
  (htrace : ∀ X ∈ S, ∀ u < T, trace M (List.ofFn X) u = τ u)
  (hcorrect : ∀ X ∈ S, ∀ p ∈ retainedBits J b s,
    (outBit M (List.ofFn X) (root p)).getD false = X p)
  (htarget : ∀ p ∈ retainedBits J b s, entry (sourceTarget p) = entry p)
  (hcone : ∀ p ∈ retainedBits J b s, root p ∉ Γ →
    nativeInputCone τ (n * b) T Γ (root p) ⊆
      inputDilation (cones (sourceTarget p)) (3 * s) ∪ inputBoundary (n * b) (3 * s))

include hroot htrace hcorrect htarget hcone

/-- Actual equal joint labels and helper symbols determine each retained
symbol. Guarded roots use the output field already in the complete record. -/
theorem cellCode_storage (z) :
    IsStorageCode (inducedNeighborhood (entryQuotient cones) J) (cellCode M J s Γ S z) := by
  intro x hx y hy e hhelpers
  obtain ⟨X, hX, rfl⟩ := mem_image.mp hx
  obtain ⟨Y, hY, rfl⟩ := mem_image.mp hy
  have hXS := (mem_filter.mp hX).1
  have hYS := (mem_filter.mp hY).1
  have hlabel := (mem_filter.mp hX).2.trans (mem_filter.mp hY).2.symm
  have hΓ : ∀ u ∈ Γ, stepValue M (List.ofFn X) u = stepValue M (List.ofFn Y) u := by
    intro u hu
    exact congrFun (congrArg Prod.fst hlabel) ⟨u, hu⟩
  have hext : ∀ p ∉ retainedBits J b s, X p = Y p := by
    intro p hp
    exact congrFun (congrArg Prod.snd hlabel) ⟨p, mem_compl.mpr hp⟩
  funext j
  let p := interiorBit s e.val j
  have hp : p ∈ retainedBits J b s := mem_image_of_mem _ (mem_univ (e,j))
  change X p = Y p
  rw [← hcorrect X hXS p hp, ← hcorrect Y hYS p hp]
  suffices hv : stepValue M (List.ofFn X) (root p) = stepValue M (List.ofFn Y) (root p) by
    exact congrArg (fun v : Value M => v.2.2.getD false) hv
  by_cases hrΓ : root p ∈ Γ
  · exact hΓ (root p) hrΓ
  apply nativeInputCone_determines (hroot p hp) (htrace X hXS) (htrace Y hYS) hΓ
  intro a ha
  by_cases haI : a ∈ retainedBits J b s
  · obtain ⟨⟨f,l⟩, _, rfl⟩ := mem_image.mp haI
    have haI : interiorBit s f.val l ∈ retainedBits J b s := mem_image_of_mem _ (mem_univ (f,l))
    have hlanes := (mem_retainedBits.mp haI).2
    rcases mem_union.mp (hcone p hp hrΓ ha) with hdil | hboundary
    · obtain ⟨_, q, hq, hnear⟩ := mem_filter.mp hdil
      have heq := neighbor_same_entry hlanes.1 hlanes.2 hnear
      have hquot : f.val ∈ entryQuotient cones e.val := by
        apply mem_entryQuotient.mpr
        refine ⟨lane (sourceTarget p), q, ?_, ?_⟩
        · have het : entry (sourceTarget p) = e.val := by
            simpa only [p, interiorBit, entry_bit] using htarget p hp
          simpa only [← het, bit_entry_lane] using hq
        · simpa only [interiorBit, entry_bit] using heq
      exact congrFun (hhelpers f (by simpa only [inducedNeighborhood, mem_subtype] using hquot)) l
    · have hbnd := (mem_filter.mp hboundary).2
      change (interiorBit s f.val l).val < 3 * s ∨
        n * b ≤ (interiorBit s f.val l).val + 3 * s at hbnd
      have hav := interior_avoids_boundary hlanes.1 hlanes.2
      omega
  · exact hext a haI

/-- The actual largest joint-record cell is an injectively projected storage
code. Its members are restricted only by the common simulator trace. -/
theorem exists_large_entry_code (hS : S.Nonempty) :
    ∃ C : Finset (J → Fin (b - 6 * s) → Bool), C.Nonempty ∧
      IsStorageCode (inducedNeighborhood (entryQuotient cones) J) C ∧
      S.card ≤ 2 ^ (valueWidth M * Γ.card + (n * b - (b - 6 * s) * J.card)) * C.card := by
  obtain ⟨z, hz, hcount⟩ := TapeStorageRates.exists_large_observation_fibre hS (record M J s Γ)
  obtain ⟨X, hX, hzX⟩ := mem_image.mp hz
  refine ⟨cellCode M J s Γ S z, ?_, cellCode_storage S J Γ root cones sourceTarget
    hroot htrace hcorrect htarget hcone z, ?_⟩
  · exact ⟨project J s X, mem_image_of_mem _ (mem_filter.mpr ⟨hX, hzX⟩)⟩
  · rw [cellCode_card]
    exact hcount.trans (Nat.mul_le_mul_right _ (record_range_card_le M J s Γ S))

/-- Finite original-entry deficit with the actual complete guard-value width.
There is no terminal-output surcharge and no trace constraint on the source
runs other than the single reference used to supply the source cones. -/
theorem entry_capacity_of_cone_containment (hS : S.Nonempty) :
    deficit (inducedNeighborhood (entryQuotient cones) J) (b - 6 * s) ≤
      (n * b : ℕ) - Real.logb 2 (S.card : ℝ) + (valueWidth M : ℝ) * Γ.card := by
  obtain ⟨C, hCne, hC, hcount⟩ := exists_large_entry_code S J Γ root cones sourceTarget
    hroot htrace hcorrect htarget hcone hS
  have hd : (b - 6 * s) * J.card ≤ n * b := by
    rw [← retainedBits_card J b s]
    exact (retainedBits J b s).card_le_univ.trans_eq (Fintype.card_fin _)
  have hcR : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hCR : (0 : ℝ) < C.card := by exact_mod_cast hCne.card_pos
  have hc : (S.card : ℝ) ≤ (2 : ℝ) ^ (valueWidth M * Γ.card + (n * b - (b - 6 * s) * J.card)) * C.card := by
    exact_mod_cast hcount
  have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hcR hc
  rw [Real.logb_mul (by positivity) (ne_of_gt hCR), Real.logb_pow,
    Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at hl
  have hcap := code_log_le_capacity hC hCne
  simp only [Nat.cast_add, Nat.cast_sub hd, Nat.cast_mul] at hl
  unfold deficit
  simp only [Fintype.card_coe, Nat.cast_mul]
  linarith

end Recovery
end AdaptiveTransfer.TransferEntry
