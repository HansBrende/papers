import AdaptiveTransfer.FeedbackTranscript
import LeanMachine.BlockProgramExports

/-! Literal fixed-word producer records: switch states and dated values.
The recurrence and its field translation prove rectangularity and owner-local
recovery. Capacities are charged on the original state and value alphabets. -/

namespace AdaptiveTransfer

open TransposeFollowup LeanMachine Classical Finset
open scoped BigOperators

variable {ι κ S A : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]
  (owner : ι → κ) (p : BlockProgram κ (OwnedBits owner) S A)

noncomputable def blockTranscript (T : ℕ) (x : ι → Bool) :=
  p.transcript T (ownedInput owner x)

theorem blockTranscript_rectangle [Nonempty κ] (T : ℕ)
    (z : (p.stateExports T → S) × (p.versionExports T → A)) :
    CoordinateRectangle owner (univ.filter (fun x => blockTranscript owner p T x = z)) := by
  intro x hx
  choose xs hmem hview using hx
  let a := Classical.arbitrary κ
  have hz : ∀ j, p.transcript T (ownedInput owner (xs j)) = z :=
    fun j => (mem_filter.mp (hmem j)).2
  have hm := p.transcript_mix T (fun j => ownedInput owner (xs j)) (ownedInput owner (xs a))
    (fun j => (hz j).trans (hz a).symm)
  have he : ownedInput owner x = fun j => ownedInput owner (xs j) j := by
    funext j
    exact ownedInput_eq_of_view owner (hview j)
  apply mem_filter.mpr
  refine ⟨mem_univ _, ?_⟩
  change p.transcript T (ownedInput owner x) = z
  rw [he]
  exact hm.trans (hz a)

/-- Each surviving version has one common group-local recovery function. -/
theorem block_version_factorsThrough (T t : ℕ) (ht : t < T) :
    (fun x : ι → Bool => (p.eval (ownedInput owner x) t).2).FactorsThrough
      (fun x => (blockTranscript owner p T x,
        bitView (ownedCoordinates owner (p.owner t)) x)) := by
  intro x y he
  have hz := p.transcript_eq_iff_fields.mp (congrArg Prod.fst he)
  have hraw := ownedInput_eq_of_view owner (congrArg Prod.snd he)
  have hf := p.fields.eval_eq_of_owner_transcript hz (p.owner t) hraw (2*t+1) (by omega)
    (by change p.owner ((2*t+1)/2)=p.owner t; congr 1; omega)
  rw [(p.fields_eval (ownedInput owner x) t).2, (p.fields_eval (ownedInput owner y) t).2] at hf
  have hh := congrArg Prod.snd hf
  exact hh

theorem block_transcript_correlation_le_deficit
    {Ω : Type*} [Fintype Ω] [Nonempty Ω] [Fintype κ] [Nonempty κ]
    [Fintype S] [Nonempty S] [Fintype A] [Nonempty A]
    (T : ℕ) (μ : Ω → ℝ) (hμ : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    (X : Ω → ι → Bool) :
    conditionalTotalCorrelation μ
      (fun x a => bitView (ownedCoordinates owner a) (X x))
        (blockTranscript owner p T ∘ X) ≤
      Fintype.card ι * Real.log 2 - observationEntropy μ X :=
  rectangular_transcript_correlation_le_deficit owner μ hμ hμ1 X
    (blockTranscript owner p T) (by
      intro z
      convert blockTranscript_rectangle owner p T z using 1
      ext x
      simp only [mem_filter, mem_univ, true_and])

omit [DecidableEq ι] in
/-- A field's range follows from its actual total operation's codomain. -/
theorem block_eval_mem (menu : ℕ → Finset A)
    (hmenu : ∀ t s r v, (p.update t s r v).2 ∈ menu t)
    (x : (a : κ) → OwnedBits owner a) (t : ℕ) : (p.eval x t).2 ∈ menu t := by
  rw [p.eval_eq]
  exact hmenu _ _ _ _

omit [DecidableEq ι] in
/-- One joint transcript costs each complete switch state and each distinct
foreign version once. Real-valued capacity bounds avoid rounding charges. -/
theorem block_transcript_entropy_le
    {Ω : Type*} [Fintype Ω] [Nonempty Ω] [Fintype S] [Fintype A]
    (T : ℕ) (μ : Ω → ℝ) (hμ : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    (X : Ω → ι → Bool) (sbits : ℝ) (hs : (Fintype.card S : ℝ) ≤ (2 : ℝ)^sbits)
    (menu : ℕ → Finset A) (bits : ℕ → ℝ)
    (hmenu : ∀ t s r v, (p.update t s r v).2 ∈ menu t)
    (hbits : ∀ t, ((menu t).card : ℝ) ≤ (2 : ℝ)^bits t) :
    observationEntropy μ (blockTranscript owner p T ∘ X) ≤
      (sbits * (p.stateExports T).card + ∑ t ∈ p.versionExports T, bits t) * Real.log 2 := by
  let : Nonempty S := ⟨p.initial⟩
  let : Nonempty A := ⟨p.constant⟩
  let E := (p.stateExports T → S) × ((t : p.versionExports T) → menu t.val)
  let enc (x : Ω) : E :=
    ((fun t => (p.eval (ownedInput owner (X x)) t.val).1),
      fun t => ⟨(p.eval (ownedInput owner (X x)) t.val).2,
        block_eval_mem owner p menu hmenu _ t.val⟩)
  have hfac : (blockTranscript owner p T ∘ X).FactorsThrough enc := by
    intro x y he
    apply Prod.ext
    · have hh := congrArg Prod.fst he
      exact hh
    · funext t
      exact congrArg Subtype.val (congrFun (congrArg Prod.snd he) t)
  have hpos (t : ℕ) : (0 : ℝ) < (menu t).card := by
    exact_mod_cast card_pos.mpr ⟨_, block_eval_mem owner p menu hmenu
      (ownedInput owner (X (Classical.arbitrary Ω))) t⟩
  have hslog : Real.log (Fintype.card S : ℝ) ≤ sbits * Real.log 2 :=
    (Real.log_le_log (by exact_mod_cast Fintype.card_pos (α := S)) hs).trans_eq
      (Real.log_rpow (by norm_num : (0 : ℝ)<2) sbits)
  have hblog (t : ℕ) : Real.log ((menu t).card : ℝ) ≤ bits t * Real.log 2 :=
    (Real.log_le_log (hpos t) (hbits t)).trans_eq
      (Real.log_rpow (by norm_num : (0 : ℝ)<2) (bits t))
  have he : Real.log (Fintype.card E : ℝ) =
      (p.stateExports T).card * Real.log (Fintype.card S : ℝ) +
        ∑ t : p.versionExports T, Real.log ((menu t.val).card : ℝ) := by
    change Real.log (Fintype.card ((p.stateExports T → S) ×
      ((t : p.versionExports T) → menu t.val)) : ℝ) = _
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_coe, Fintype.card_pi,
      Nat.cast_mul, Nat.cast_pow, Nat.cast_prod]
    rw [Real.log_mul (by positivity) (Finset.prod_ne_zero_iff.mpr (fun t _ => (hpos t.val).ne')),
      Real.log_pow, Real.log_prod (fun t _ => (hpos t.val).ne')]
  have hl : Real.log (Fintype.card E : ℝ) ≤
      (sbits * (p.stateExports T).card + ∑ t ∈ p.versionExports T, bits t) * Real.log 2 := by
    rw [he]
    calc
      _ ≤ (p.stateExports T).card * (sbits * Real.log 2) +
          ∑ t : p.versionExports T, bits t.val * Real.log 2 :=
        add_le_add (mul_le_mul_of_nonneg_left hslog (by positivity))
          (sum_le_sum (fun t _ => hblog t.val))
      _ = _ := by rw [← sum_mul, sum_coe_sort]; ring
  let := Nonempty.intro (enc (Classical.arbitrary Ω))
  have hh := entropy_le_log_card (pushforward μ enc) (pushforward_nonneg μ hμ enc)
    (by rw [sum_pushforward, hμ1])
  exact (observationEntropy_le_of_factorsThrough μ hμ enc _ hfac).trans (hh.trans hl)

end AdaptiveTransfer
