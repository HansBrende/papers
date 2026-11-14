import GridCertificate
import SoftRecovery.Observations

/-!
# Full-host upper bound for the rectangular grid

The host has nine point rows, six line columns and 18 incident cells.
Conditioning on those cells transfers the paid 36-cell certificate to the
full 54-cell host. No square-grid, linear-code or symmetry assumption is added.
This is an upper bound; attainment at 204/5 is not asserted.
-/

namespace LeanBacklog.GridFull

open Finset MotionDepthCodes SoftRecovery HalfRate
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000

abbrev Grid := Fin 9 × Fin 6

def embed (v : GridCertificate.Cell) : Grid :=
  (GridCertificate.row v, GridCertificate.column v)

def loops : Finset Grid := univ.filter fun p => GridCertificate.incident p.1 p.2

def rowRelation (l : Fin 6) : Finset (Fin 9) :=
  univ.filter fun p => GridCertificate.incident p l

def helpers (p : Grid) : Finset Grid :=
  univ.filter fun x => GridCertificate.incident x.1 p.2

theorem embed_injective : Function.Injective embed := GridCertificate.cells_injective
theorem loops_card : loops.card = 18 := by decide
theorem embed_univ_union_loops : univ.image embed ∪ loops = (univ : Finset Grid) := by decide
theorem helpers_cover (v : GridCertificate.Cell) :
    helpers (embed v) ⊆ (GridCertificate.nbhd v).image embed ∪ loops := by
  revert v; decide

/-- The contracted residual rank obeys the actual residual recovery rules. -/
theorem conditional_valid {h : Finset Grid → ℝ} (hh : IsPolymatroid h)
    (hv : IsValid h helpers) :
    IsValid (conditionalImage h loops embed) GridCertificate.nbhd := by
  intro v
  apply sub_eq_zero.mp
  change increment (conditionalImage h loops embed) (GridCertificate.nbhd v) v = 0
  apply le_antisymm
  · rw [conditionalImage_increment]
    have hi := increment_antitone hh (helpers_cover v) (embed v)
    simpa [increment, hv (embed v)] using hi
  · exact increment_nonneg (conditionalImage_isPolymatroid hh loops embed) _ _

/-- Keep the joint loop entropy and conditional singleton prices in the paid bound. -/
theorem paid_full (h : Finset Grid → ℝ) (hh : IsPolymatroid h) :
    30 * (h univ - h loops) ≤
      19 * (∑ v : GridCertificate.Cell, increment h loops (embed v)) +
      11 * ∑ v : GridCertificate.Cell, increment h (helpers (embed v)) (embed v) := by
  have hp := GridCertificate.paid_grid (conditionalImage h loops embed)
    (conditionalImage_isPolymatroid hh loops embed)
  have he := Finset.sum_le_sum (s := (univ : Finset GridCertificate.Cell))
    (fun v _ => increment_antitone hh (helpers_cover v) (embed v))
  simp only [conditionalImage_singleton, conditionalImage_increment] at hp
  change 30 * (h (univ.image embed ∪ loops) - h loops) ≤ _ at hp
  rw [embed_univ_union_loops] at hp
  linarith

/-- Uniform singleton capacity may be any real number. -/
theorem full_upper_of_cap {h : Finset Grid → ℝ} (hh : IsPolymatroid h)
    (hv : IsValid h helpers) (a : ℝ) (hc : ∀ p, h {p} ≤ a) :
    5 * h univ ≤ 204 * a := by
  have hp := paid_full h hh
  have hz : (∑ v : GridCertificate.Cell,
      increment h (helpers (embed v)) (embed v)) = 0 := by
    apply Finset.sum_eq_zero
    intro v _
    simp [increment, hv (embed v)]
  rw [hz, mul_zero, add_zero] at hp
  have hs : (∑ v : GridCertificate.Cell, increment h loops (embed v)) ≤ 36 * a := by
    calc
      _ ≤ ∑ _v : GridCertificate.Cell, a :=
        Finset.sum_le_sum fun v _ => (increment_le_singleton hh _ _).trans (hc _)
      _ = _ := by simp
  have hl : h loops ≤ 18 * a := by
    calc
      _ ≤ ∑ p ∈ loops, h {p} := hh.le_sum_singleton loops
      _ ≤ ∑ _p ∈ loops, a := Finset.sum_le_sum fun p _ => hc p
      _ = _ := by simp [loops_card]
  linarith

theorem full_upper {h : Finset Grid → ℝ} (hh : IsPolymatroid h)
    (hv : IsValid h helpers) (hc : ∀ p, h {p} ≤ 1) : h univ ≤ 204 / 5 := by
  have h := full_upper_of_cap hh hv 1 hc
  linarith

/-- Arbitrary finite probability laws on recoverable words, in nats. -/
theorem full_entropy_upper {Ω α : Type*} [Fintype Ω] [Fintype α] [Nonempty α]
    (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1)
    (X : Ω → Grid → α) (hX : IsRecoverable helpers X) :
    5 * codeEntropy p X univ ≤ 204 * Real.log (Fintype.card α) :=
  full_upper_of_cap (codeEntropy_isPolymatroid p X hp hp1)
    (codeEntropy_isValid p X hp hX) _ (codeEntropy_singleton_le p X hp hp1)

theorem storage_log_card {α : Type*} [Fintype α] [Nonempty α]
    (C : Finset (Grid → α)) (hC : IsStorageCode helpers C) :
    5 * Real.log C.card ≤ 204 * Real.log (Fintype.card α) := by
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

/-- Integer form for every finite alphabet, even the empty or one-symbol alphabet. -/
theorem storage_card_fifth {α : Type*} [Fintype α]
    (C : Finset (Grid → α)) (hC : IsStorageCode helpers C) :
    C.card ^ 5 ≤ Fintype.card α ^ 204 := by
  rcases C.eq_empty_or_nonempty with he | hne
  · simp [he]
  · let : Nonempty α := ⟨hne.choose (0, 0)⟩
    have hCpos : (0 : ℝ) < C.card := by exact_mod_cast hne.card_pos
    have hqpos : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
    have hi : Real.log ((C.card : ℝ) ^ 5) ≤
        Real.log ((Fintype.card α : ℝ) ^ 204) := by
      simpa [Real.log_pow] using storage_log_card C hC
    have ho := (Real.log_le_log_iff (pow_pos hCpos _) (pow_pos hqpos _)).mp hi
    exact_mod_cast ho

end LeanBacklog.GridFull

#print axioms LeanBacklog.GridFull.paid_full
#print axioms LeanBacklog.GridFull.full_upper
#print axioms LeanBacklog.GridFull.storage_card_fifth
