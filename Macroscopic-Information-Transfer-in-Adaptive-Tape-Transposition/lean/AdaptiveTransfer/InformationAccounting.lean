import TransposeFollowup.ConditionalObservation
import TransposeFollowup.UniformEntropy
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

/-! Joint finite information invoices. The entropy convention is natural
logarithms, as in the imported library; divide by log 2 for bits. Constructing
the native injective record is a separate, explicit hypothesis. -/

namespace AdaptiveTransfer

open TransposeFollowup Finset Classical
open scoped BigOperators

/-- The chain identity also covers empty source and record alphabets; only
finite nonnegative weights and the actual joint injection are required. -/
theorem joint_record_entropy_identity {Ω Metadata Exterior Ordinary Import : Type*}
    [Fintype Ω] [Fintype Metadata] [Fintype Exterior] [Fintype Ordinary] [Fintype Import]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x)
    (metadata : Ω → Metadata) (exterior : Ω → Exterior)
    (ordinary : Ω → Ordinary) (imports : Ω → Import)
    (hinj : Function.Injective (fun x => (((metadata x, exterior x), ordinary x), imports x))) :
    conditionalObservationEntropy p imports (fun x => ((metadata x, exterior x), ordinary x)) =
      entropy p - observationEntropy p metadata -
        conditionalObservationEntropy p exterior metadata -
        conditionalObservationEntropy p ordinary (fun x => (metadata x, exterior x)) := by
  cases isEmpty_or_nonempty Ω with
  | inl h =>
    let := h
    simp [conditionalObservationEntropy, observationEntropy, entropy, pushforward]
  | inr h =>
    let := h
    have heq := observationEntropy_injective p hp _ hinj
    simp only [conditionalObservationEntropy, heq]
    ring

/-- A joint import record pays the unaccounted information under ONE law. -/
theorem joint_record_information_lower {Ω Metadata Exterior Ordinary Import : Type*}
    [Fintype Ω] [Fintype Metadata] [Fintype Exterior] [Fintype Ordinary] [Fintype Import]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x)
    (metadata : Ω → Metadata) (exterior : Ω → Exterior)
    (ordinary : Ω → Ordinary) (imports : Ω → Import)
    (hinj : Function.Injective (fun x => (((metadata x, exterior x), ordinary x), imports x)))
    (exteriorBill ordinaryBill : ℝ)
    (he : conditionalObservationEntropy p exterior metadata ≤ exteriorBill)
    (hr : conditionalObservationEntropy p ordinary (fun x => (metadata x, exterior x)) ≤ ordinaryBill) :
    entropy p - exteriorBill - ordinaryBill - observationEntropy p metadata ≤
      conditionalObservationEntropy p imports (fun x => ((metadata x, exterior x), ordinary x)) := by
  rw [joint_record_entropy_identity p hp metadata exterior ordinary imports hinj]
  linarith

/-- Only the ATTAINED joint range of the record is paid. -/
theorem joint_record_card_bound {Ω Record : Type*} [Fintype Ω]
    (e : ℕ) (exterior : Ω → Fin e → Bool) (record : Ω → Record)
    (hinj : Function.Injective (fun x => (exterior x, record x))) :
    Fintype.card Ω ≤ 2 ^ e * (Finset.univ.image record).card := by
  let encode (x : Ω) : (Fin e → Bool) × (Finset.univ.image record) :=
    (exterior x, ⟨record x, mem_image_of_mem record (mem_univ x)⟩)
  have hi : Function.Injective encode := by
    intro x y hxy
    apply hinj
    exact Prod.ext
      (congrArg (fun z : (Fin e → Bool) × (Finset.univ.image record) => z.1) hxy)
      (congrArg (fun z : (Fin e → Bool) × (Finset.univ.image record) => z.2.val) hxy)
  have hc := Fintype.card_le_of_injective encode hi
  simpa only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_bool, Fintype.card_coe] using hc

end AdaptiveTransfer
