import FanoCertificate
import StatementsRowSpread
import SoftRecovery.Observations

/-!
# The full 49-cell Fano host

Condition on the 21 incident cells and apply the existing 28-cell paid
certificate. This proves the full upper bound and its arbitrary-alphabet
storage-code consequence without a linearity or symmetry hypothesis.
-/

namespace LeanBacklog.FanoFull

open Finset MotionDepthCodes SoftRecovery HalfRate
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000

abbrev Grid := Fin 7 × Fin 7

def embed (v : FanoCertificate.Cell) : Grid :=
  (FanoCertificate.row v, FanoCertificate.column v)

def loops : Finset Grid := univ.filter fun p => FanoCertificate.incident p.1 p.2

def rowRelation (l : Fin 7) : Finset (Fin 7) :=
  univ.filter fun p => FanoCertificate.incident p l

def helpers (p : Grid) : Finset Grid :=
  univ.filter fun x => FanoCertificate.incident x.1 p.2

theorem embed_injective : Function.Injective embed := FanoCertificate.cells_injective
theorem loops_card : loops.card = 21 := by decide
theorem embed_univ_union_loops : univ.image embed ∪ loops = (univ : Finset Grid) := by decide
theorem helpers_cover (v : FanoCertificate.Cell) :
    helpers (embed v) ⊆ (FanoCertificate.nbhd v).image embed ∪ loops := by
  revert v; decide

theorem helpers_wholeRow : helpers = RowSpread.wholeRowHelpers rowRelation ∅ := by
  funext p
  ext x
  simp [helpers, RowSpread.wholeRowHelpers, rowRelation]

/-- The contracted residual polymatroid satisfies the original residual
recovery equalities whenever the full host satisfies its own equalities. -/
theorem conditional_valid {h : Finset Grid → ℝ} (hh : IsPolymatroid h)
    (hv : IsValid h helpers) :
    IsValid (conditionalImage h loops embed) FanoCertificate.nbhd := by
  intro v
  apply sub_eq_zero.mp
  change increment (conditionalImage h loops embed) (FanoCertificate.nbhd v) v = 0
  apply le_antisymm
  · rw [conditionalImage_increment]
    have hi := increment_antitone hh (helpers_cover v) (embed v)
    simpa [increment, hv (embed v)] using hi
  · exact increment_nonneg (conditionalImage_isPolymatroid hh loops embed) _ _

/-- Stronger paid form: keep the joint entropy of the incident cells and
the conditional singleton prices. Only the recovery-error terms are enlarged
back to the original full-host helper sets. -/
theorem paid_full (h : Finset Grid → ℝ) (hh : IsPolymatroid h) :
    3 * (h univ - h loops) ≤
      2 * (∑ v : FanoCertificate.Cell, increment h loops (embed v)) +
      ∑ v : FanoCertificate.Cell, increment h (helpers (embed v)) (embed v) := by
  have hp := FanoCertificate.paid_fano (conditionalImage h loops embed)
    (conditionalImage_isPolymatroid hh loops embed)
  have he := Finset.sum_le_sum (s := (univ : Finset FanoCertificate.Cell))
    (fun v _ => increment_antitone hh (helpers_cover v) (embed v))
  simp only [conditionalImage_singleton, conditionalImage_increment] at hp
  change 3 * (h (univ.image embed ∪ loops) - h loops) ≤ _ at hp
  rw [embed_univ_union_loops] at hp
  exact hp.trans (add_le_add_right he _)

/-- Uniform singleton capacity may be any real number. -/
theorem full_upper_of_cap {h : Finset Grid → ℝ} (hh : IsPolymatroid h)
    (hv : IsValid h helpers) (a : ℝ) (hc : ∀ p, h {p} ≤ a) :
    3 * h univ ≤ 119 * a := by
  have hp := paid_full h hh
  have hz : (∑ v : FanoCertificate.Cell,
      increment h (helpers (embed v)) (embed v)) = 0 := by
    apply Finset.sum_eq_zero
    intro v _
    simp [increment, hv (embed v)]
  rw [hz, add_zero] at hp
  have hs : (∑ v : FanoCertificate.Cell, increment h loops (embed v)) ≤ 28 * a := by
    calc
      _ ≤ ∑ _v : FanoCertificate.Cell, a :=
        Finset.sum_le_sum fun v _ => (increment_le_singleton hh _ _).trans (hc _)
      _ = _ := by simp
  have hl : h loops ≤ 21 * a := by
    calc
      _ ≤ ∑ p ∈ loops, h {p} := hh.le_sum_singleton loops
      _ ≤ ∑ _p ∈ loops, a := Finset.sum_le_sum fun p _ => hc p
      _ = _ := by simp [loops_card]
  linarith

theorem full_upper {h : Finset Grid → ℝ} (hh : IsPolymatroid h)
    (hv : IsValid h helpers) (hc : ∀ p, h {p} ≤ 1) : h univ ≤ 119 / 3 := by
  have h := full_upper_of_cap hh hv 1 hc
  linarith

/-- Entropy of arbitrary distributions on the whole-row code, in nats. -/
theorem full_entropy_upper {Ω α : Type*} [Fintype Ω] [Fintype α] [Nonempty α]
    (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1)
    (X : Ω → Grid → α) (hX : IsRecoverable helpers X) :
    3 * codeEntropy p X univ ≤ 119 * Real.log (Fintype.card α) :=
  full_upper_of_cap (codeEntropy_isPolymatroid p X hp hp1)
    (codeEntropy_isValid p X hp hX) _ (codeEntropy_singleton_le p X hp hp1)

theorem storage_log_card {α : Type*} [Fintype α] [Nonempty α]
    (C : Finset (Grid → α)) (hC : IsStorageCode helpers C) :
    3 * Real.log C.card ≤ 119 * Real.log (Fintype.card α) := by
  rcases C.eq_empty_or_nonempty with he | hne
  · simp only [he, card_empty, Nat.cast_zero, Real.log_zero, mul_zero]
    exact mul_nonneg (by norm_num) (Real.log_nonneg (by exact_mod_cast Fintype.card_pos))
  · let p : C → ℝ := fun _ => (C.card : ℝ)⁻¹
    have hp : ∀ x, 0 ≤ p x := fun _ => inv_nonneg.mpr (Nat.cast_nonneg _)
    have hp1 : ∑ x, p x = 1 := by
      simp [p, hne.ne_empty]
    have hr : IsRecoverable helpers (fun x : C => (x : Grid → α)) :=
      fun v x y h => hC x x.2 y y.2 v h
    have hi := full_entropy_upper p hp hp1 _ hr
    simpa only [p, codeEntropy_univ_uniform C hne] using hi

/-- Integer form, including empty codes and the one-symbol alphabet. -/
theorem storage_card_cube {α : Type*} [Fintype α] [Nonempty α]
    (C : Finset (Grid → α)) (hC : IsStorageCode helpers C) :
    C.card ^ 3 ≤ Fintype.card α ^ 119 := by
  rcases C.eq_empty_or_nonempty with he | hne
  · simp [he]
  · have hCpos : (0 : ℝ) < C.card := by exact_mod_cast hne.card_pos
    have hqpos : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
    have hi : Real.log ((C.card : ℝ) ^ 3) ≤
        Real.log ((Fintype.card α : ℝ) ^ 119) := by
      simpa [Real.log_pow] using storage_log_card C hC
    have ho := (Real.log_le_log_iff (pow_pos hCpos _) (pow_pos hqpos _)).mp hi
    exact_mod_cast ho

/-- The same cardinality theorem in the native whole-row-code vocabulary. -/
theorem wholeRow_card_cube {α : Type*} [Fintype α] [Nonempty α]
    (C : Finset (Grid → α)) (hC : RowSpread.IsWholeRowCodeExcept rowRelation ∅ C) :
    C.card ^ 3 ≤ Fintype.card α ^ 119 := by
  apply storage_card_cube C
  simpa only [helpers_wholeRow, RowSpread.IsWholeRowCodeExcept] using hC

#print axioms paid_full
#print axioms full_upper
#print axioms full_entropy_upper
#print axioms storage_card_cube
#print axioms wholeRow_card_cube

end LeanBacklog.FanoFull
