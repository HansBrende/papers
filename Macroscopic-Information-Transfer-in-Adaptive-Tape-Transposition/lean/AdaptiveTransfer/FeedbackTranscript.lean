import LeanMachine.OwnerProgram
import TransposeFollowup.RectangleEntropy
import TransposeFollowup.FullFiberEntropy
import AdaptiveTransfer.ConditionalSupport

/-! Actual owner-program transcripts on the whole binary input cube.
Their full fibres are rectangular even when the law of correct inputs is
correlated. The dependency fields are supplied by a fixed chronological
program; this is not a native monitor or paid-spool compiler. -/

namespace AdaptiveTransfer

open TransposeFollowup LeanMachine Classical Finset
open scoped BigOperators

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]
  (owner : ι → κ)

abbrev OwnedBits (a : κ) := ownedCoordinates owner a → Bool

def ownedInput (x : ι → Bool) (a : κ) : OwnedBits owner a := fun i => x i.val

theorem ownedInput_eq_of_view {x y : ι → Bool} {a : κ}
    (h : bitView (ownedCoordinates owner a) x = bitView (ownedCoordinates owner a) y) :
    ownedInput owner x a = ownedInput owner y a := by
  funext i
  exact (bitView_eq_iff _ _ _).mp h i.val i.property

variable {V : ℕ → Type*} (p : OwnerProgram κ (OwnedBits owner) V)

noncomputable def feedbackTranscript (T : ℕ) (x : ι → Bool) :
    (u : p.exports T) → V u.val := p.transcript T (ownedInput owner x)

noncomputable def feedbackFiber (T : ℕ) (z : (u : p.exports T) → V u.val) :
    Finset (ι → Bool) := univ.filter (fun x => feedbackTranscript owner p T x = z)

/-- Derived from the actual chronological evaluation, not assumed as a
rectangle certificate for a transcript chosen in advance. -/
theorem feedbackFiber_rectangle (T : ℕ) (z : (u : p.exports T) → V u.val) :
    CoordinateRectangle owner (feedbackFiber owner p T z) := by
  intro x hx
  choose xs hmem hview using hx
  have hz : ∀ a, p.transcript T (ownedInput owner (xs a)) = z := by
    intro a
    exact (mem_filter.mp (hmem a)).2
  have hm := p.transcript_mix (fun a => ownedInput owner (xs a)) z hz
  have he : ownedInput owner x = fun a => ownedInput owner (xs a) a := by
    funext a
    exact ownedInput_eq_of_view owner (hview a)
  apply mem_filter.mpr
  refine ⟨mem_univ _, ?_⟩
  change p.transcript T (ownedInput owner x) = z
  rwa [he]

/-- Every final archive field has one common owner-local function once the
joint transcript is fixed. Repeated consumer queries use that same value. -/
theorem feedback_field_factorsThrough (T t : ℕ) (ht : t < T) :
    (fun x : ι → Bool => p.eval (ownedInput owner x) t).FactorsThrough
      (fun x => (feedbackTranscript owner p T x,
        bitView (ownedCoordinates owner (p.owner t)) x)) := by
  intro x y he
  exact p.eval_eq_of_owner_transcript (congrArg Prod.fst he) (p.owner t)
    (ownedInput_eq_of_view owner (congrArg Prod.snd he)) t ht rfl

/-- Conditional total correlation of the original owner blocks costs at most
the source deficit when every full transcript fibre is rectangular. -/
theorem rectangular_transcript_correlation_le_deficit
    {Ω Z : Type*} [Fintype Ω] [Nonempty Ω] [Fintype κ] [Nonempty κ]
    [Fintype Z] [Nonempty Z]
    (μ : Ω → ℝ) (hμ : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    (X : Ω → ι → Bool) (f : (ι → Bool) → Z)
    (hrect : ∀ z, CoordinateRectangle owner (univ.filter (fun x => f x = z))) :
    conditionalTotalCorrelation μ
      (fun x a => bitView (ownedCoordinates owner a) (X x)) (f ∘ X) ≤
      Fintype.card ι * Real.log 2 - observationEntropy μ X := by
  let H := f ∘ X
  let A := fun x a => bitView (ownedCoordinates owner a) (X x)
  have hm (z : Z) : helperMass μ H z *
      (∑ a, observationEntropy (helperConditionalWeight μ H z)
        (fun x : HelperFiber H z => A x.val a)) ≤
      helperMass μ H z * Real.log (fiberCard f z : ℝ) := by
    by_cases hz : helperMass μ H z = 0
    · simp only [hz, zero_mul, le_refl]
    · have hp := helperMass_nonneg μ hμ H z
      let := helperFiber_nonempty_of_mass_pos μ H z (lt_of_le_of_ne hp (Ne.symm hz))
      apply mul_le_mul_of_nonneg_left _ hp
      exact sum_owned_entropy_le_log_rectangle
        (helperConditionalWeight μ H z) (helperConditionalWeight_nonneg μ hμ H z)
        (sum_helperConditionalWeight μ H z hz)
        (fun x : HelperFiber H z => X x.val) owner _ (hrect z)
        (fun x => mem_filter.mpr ⟨mem_univ _, x.property⟩)
  have hs := sum_le_sum (fun z (_ : z ∈ univ) => hm z)
  simp_rw [mul_sum] at hs
  rw [sum_comm] at hs
  have hav (a : κ) := sum_helperMass_mul_observationEntropy μ hμ H (fun x => A x a)
  have havsum := sum_congr (s₁ := (univ : Finset κ)) rfl (fun a _ => hav a)
  rw [havsum] at hs
  have hf := fullFiberReference_deficit μ hμ hμ1 X f
  have he : conditionalObservationEntropy μ A H = conditionalObservationEntropy μ X H := by
    apply conditionalObservationEntropy_eq_of_same_fibers μ hμ
    intro x y _
    constructor
    · intro h
      funext i
      exact (bitView_eq_iff _ _ _).mp (congrFun h (owner i)) i (by simp [ownedCoordinates])
    · intro h
      simp only [A, h]
  have hsum : (∑ z, helperMass μ H z * Real.log (fiberCard f z : ℝ)) =
      ∑ x, μ x * Real.log (fiberCard f (f (X x)) : ℝ) :=
    sum_pushforward_mul μ H (fun z => Real.log (fiberCard f z : ℝ))
  rw [hsum] at hs
  have hc : Real.log (Fintype.card (ι → Bool) : ℝ) = Fintype.card ι * Real.log 2 := by
    simp only [Fintype.card_fun, Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  rw [hc] at hf
  change (∑ a, conditionalObservationEntropy μ (fun x => A x a) H) -
    conditionalObservationEntropy μ A H ≤ _
  rw [he]
  linarith

/-- The correlation bound for an actual evaluated owner program. -/
theorem feedback_transcript_correlation_le_deficit
    {Ω : Type*} [Fintype Ω] [Nonempty Ω] [Fintype κ] [Nonempty κ]
    [∀ t, Fintype (V t)] [∀ t, Nonempty (V t)]
    (T : ℕ) (μ : Ω → ℝ) (hμ : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    (X : Ω → ι → Bool) :
    conditionalTotalCorrelation μ
      (fun x a => bitView (ownedCoordinates owner a) (X x))
        (feedbackTranscript owner p T ∘ X) ≤
      Fintype.card ι * Real.log 2 - observationEntropy μ X :=
  rectangular_transcript_correlation_le_deficit owner μ hμ hμ1 X
    (feedbackTranscript owner p T) (by
      intro z
      convert feedbackFiber_rectangle owner p T z using 1
      ext x
      simp only [feedbackFiber, mem_filter, mem_univ, true_and])

end AdaptiveTransfer
