import LeanMachine.SymmetricHelpers
import TwoSidedCodeTransfer

/-!
# Paid symmetry normalization for two-sided whole-row codes

Fix rows and columns at heavily reused helper indices, then grant reverse
helpers and diagonal helpers. The finite bound retains the exact union of
the fixed rows and columns; its coarser payment tends to zero with the
reverse-degree threshold. No linearity or symmetry of the code is assumed.
-/

namespace LeanBacklog.RowSpread

open Finset LeanMachine.SymmetricHelpers
open scoped BigOperators

universe u

/-- Granting helpers preserves both recovery directions. -/
theorem IsTwoSidedWholeRowCode.mono {d : ℕ} {α : Type u}
    {ρ σ : Fin d → Finset (Fin d)} {C : Finset (Entry d → α)}
    (hC : IsTwoSidedWholeRowCode ρ C) (hρ : ∀ r, ρ r ⊆ σ r) :
    IsTwoSidedWholeRowCode σ C :=
  ⟨wholeRowCode_mono hC.1 hρ (by simp),
    fun x hx y hy r hxy => hC.2 x hx y hy r (fun s hs j => hxy s (hρ r hs) j)⟩

/-- Recovery restricts to any subcode. -/
theorem IsTwoSidedWholeRowCode.subset {d : ℕ} {α : Type u}
    {ρ : Fin d → Finset (Fin d)} {C D : Finset (Entry d → α)}
    (hC : IsTwoSidedWholeRowCode ρ C) (hD : D ⊆ C) :
    IsTwoSidedWholeRowCode ρ D := by
  refine ⟨?_, fun x hx y hy => hC.2 x (hD hx) y (hD hy)⟩
  rw [wholeRowCode_iff]
  exact fun x hx y hy => (wholeRowCode_iff ρ ∅ C).mp hC.1 x (hD hx) y (hD hy)

/-- Constant helper rows and helper columns may be removed from both rules.
The choice of fixed indices is arbitrary; it need not come from degree trimming. -/
theorem IsTwoSidedWholeRowCode.remove_fixed {d : ℕ} {α : Type u}
    {ρ : Fin d → Finset (Fin d)} {C : Finset (Entry d → α)}
    (hC : IsTwoSidedWholeRowCode ρ C) (H : Finset (Fin d))
    (hfix : ∀ x ∈ C, ∀ y ∈ C, ∀ p ∈ fixedCross H, x p = y p) :
    IsTwoSidedWholeRowCode (trimHelpers ρ H) C := by
  constructor
  · rw [wholeRowCode_iff]
    intro x hx y hy r hr hxy i
    apply (wholeRowCode_iff ρ ∅ C).mp hC.1 x hx y hy r hr
    intro s hs j
    by_cases hsH : s ∈ H
    · exact hfix x hx y hy (s,j) (by simp [fixedCross, hsH])
    · exact hxy s (by simp [trimHelpers, hs, hsH]) j
  · intro x hx y hy r hxy i
    apply hC.2 x hx y hy r
    intro s hs j
    by_cases hsH : s ∈ H
    · exact hfix x hx y hy (j,s) (by simp [fixedCross, hsH])
    · exact hxy s (by simp [trimHelpers, hs, hsH]) j

/-- Every observed cross-fibre has the normalized recovery relation. -/
theorem twoSided_fixedCross_fibre {d : ℕ} {α : Type u} [DecidableEq α]
    (ρ : Fin d → Finset (Fin d)) (C : Finset (Entry d → α))
    (hC : IsTwoSidedWholeRowCode ρ C) (H : Finset (Fin d))
    (z : fixedCross H → α) :
    IsTwoSidedWholeRowCode (normalizedHelpers ρ H)
      (C.filter fun x => (fun p : fixedCross H => x p) = z) := by
  classical
  apply IsTwoSidedWholeRowCode.mono (hρ := trimHelpers_subset_normalizedHelpers ρ H)
  apply (hC.subset (filter_subset _ _)).remove_fixed H
  intro x hx y hy p hp
  exact congrFun ((mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm) ⟨p,hp⟩

/-- Sharper finite invoice: pay only for attained cross records. This version
does not require the ambient alphabet to be finite. -/
theorem twoSided_card_le_of_fixedCross_image {d : ℕ} {α : Type u} [DecidableEq α]
    (ρ : Fin d → Finset (Fin d)) (C : Finset (Entry d → α))
    (hC : IsTwoSidedWholeRowCode ρ C) (H : Finset (Fin d)) (A : ℝ)
    (hbound : ∀ D : Finset (Entry d → α),
      IsTwoSidedWholeRowCode (normalizedHelpers ρ H) D → (D.card : ℝ) ≤ A) :
    (C.card : ℝ) ≤
      (C.image (fun x => fun p : fixedCross H => x p)).card * A := by
  classical
  let obs : (Entry d → α) → (fixedCross H → α) := fun x p => x p
  have hcount : C.card = ∑ z ∈ C.image obs, (C.filter fun x => obs x = z).card :=
    card_eq_sum_card_fiberwise (fun _ hx => mem_image_of_mem obs hx)
  calc
    (C.card : ℝ) = ∑ z ∈ C.image obs, ((C.filter fun x => obs x = z).card : ℝ) := by
      exact_mod_cast hcount
    _ ≤ ∑ _z ∈ C.image obs, A := sum_le_sum (fun z _ =>
      hbound _ (twoSided_fixedCross_fibre ρ C hC H z))
    _ = _ := by simp [obs]

/-- A relation-specific finite bound. The payment is the number of distinct
fixed cells, so overlaps of the fixed rows and columns are charged only once.
Empty codes and empty or singleton alphabets are allowed. -/
theorem twoSided_card_le_of_fixedCross {d : ℕ} {α : Type u} [Fintype α]
    (ρ : Fin d → Finset (Fin d)) (C : Finset (Entry d → α))
    (hC : IsTwoSidedWholeRowCode ρ C) (H : Finset (Fin d)) (A : ℝ)
    (hbound : ∀ D : Finset (Entry d → α),
      IsTwoSidedWholeRowCode (normalizedHelpers ρ H) D → (D.card : ℝ) ≤ A) :
    (C.card : ℝ) ≤ (Fintype.card α : ℝ) ^ (fixedCross H).card * A := by
  classical
  let obs : (Entry d → α) → (fixedCross H → α) := fun x p => x p
  have hcount := card_le_of_real_fibre_bound C obs A (fun z => ?_)
  · simpa only [Fintype.card_fun, Fintype.card_coe, Nat.cast_pow] using hcount
  · exact hbound _ (twoSided_fixedCross_fibre ρ C hC H z)

/-- Capacity target restricted to symmetric, reflexive helper relations.
Neither the code nor either recovery function is assumed invariant. -/
def NormalizedTwoSidedWholeRowCardinalityBound (d w : ℕ) (α : Type u) [Fintype α]
    (exponent : ℝ) : Prop :=
  ∀ (ρ : Fin d → Finset (Fin d)) (C : Finset (Entry d → α)),
    (∀ r, (ρ r).card ≤ w) →
    (∀ r s, s ∈ ρ r ↔ r ∈ ρ s) → (∀ r, r ∈ ρ r) →
    IsTwoSidedWholeRowCode ρ C →
      (C.card : ℝ) ≤ (Fintype.card α : ℝ) ^ exponent

/-- Restricting the helper relations loses no bound. -/
theorem TwoSidedWholeRowCardinalityBound.normalized {d w : ℕ} {α : Type u}
    [Fintype α] {a : ℝ} (h : TwoSidedWholeRowCardinalityBound d w α a) :
    NormalizedTwoSidedWholeRowCardinalityBound d w α a :=
  fun ρ C hρ _ _ hC => h ρ C hρ hC

/-- A dimension-independent upper bound on the fraction of fixed cells. -/
noncomputable def symmetryPayment (w R : ℕ) : ℝ := 2 * (w : ℝ) / ((R : ℝ) + 1)

/-- The exact cross payment is bounded by the standard reverse-degree invoice. -/
theorem fixedCross_heavy_card_le {d w R : ℕ} (ρ : Fin d → Finset (Fin d))
    (hwidth : ∀ r, (ρ r).card ≤ w) :
    ((fixedCross (heavyHelpers ρ R)).card : ℝ) ≤ symmetryPayment w R * (d : ℝ) ^ 2 := by
  have hcross := fixedCross_card_le (heavyHelpers ρ R)
  have hheavy := heavyHelpers_card_mul_succ_le ρ w R hwidth
  simp only [Fintype.card_fin] at hcross hheavy
  have hc : ((fixedCross (heavyHelpers ρ R)).card : ℝ) ≤
      2 * (d : ℝ) * (heavyHelpers ρ R).card := by exact_mod_cast hcross
  have hh : ((heavyHelpers ρ R).card : ℝ) * ((R : ℝ) + 1) ≤ (w : ℝ) * d := by
    exact_mod_cast hheavy
  have hR : (0 : ℝ) < (R : ℝ) + 1 := by positivity
  rw [symmetryPayment, div_mul_eq_mul_div, le_div_iff₀ hR]
  calc
    _ ≤ (2 * (d : ℝ) * (heavyHelpers ρ R).card) * ((R : ℝ) + 1) :=
      mul_le_mul_of_nonneg_right hc hR.le
    _ = 2 * (d : ℝ) * ((heavyHelpers ρ R).card * ((R : ℝ) + 1)) := by ring
    _ ≤ 2 * (d : ℝ) * ((w : ℝ) * d) := mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by ring

/-- A symmetric-reflexive bound at window w+R+1 gives an unrestricted
bound with payment 2w/(R+1). There is no dimension or exponent sign premise. -/
theorem NormalizedTwoSidedWholeRowCardinalityBound.twoSided {d w R : ℕ}
    {α : Type u} [Fintype α] {a : ℝ}
    (h : NormalizedTwoSidedWholeRowCardinalityBound d (w + R + 1) α a)
    (hα : 0 < Fintype.card α) :
    TwoSidedWholeRowCardinalityBound d w α
      (a + symmetryPayment w R * (d : ℝ) ^ 2) := by
  intro ρ C hwidth hC
  have hcount := twoSided_card_le_of_fixedCross ρ C hC (heavyHelpers ρ R)
    ((Fintype.card α : ℝ) ^ a) (fun D hD =>
      h _ D (normalizedHelpers_card_le ρ w R hwidth)
        (normalizedHelpers_symmetric ρ _) (normalizedHelpers_reflexive ρ _) hD)
  have hq : (0 : ℝ) < Fintype.card α := by exact_mod_cast hα
  have hq1 : (1 : ℝ) ≤ Fintype.card α := by
    exact_mod_cast (show 1 ≤ Fintype.card α by omega)
  calc
    (C.card : ℝ) ≤ (Fintype.card α : ℝ) ^ (fixedCross (heavyHelpers ρ R)).card *
        (Fintype.card α : ℝ) ^ a := hcount
    _ = (Fintype.card α : ℝ) ^ ((fixedCross (heavyHelpers ρ R)).card + a) := by
      rw [Real.rpow_add hq, Real.rpow_natCast]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hq1 (by
      linarith [fixedCross_heavy_card_le ρ hwidth (R := R)])

#print axioms IsTwoSidedWholeRowCode.remove_fixed
#print axioms twoSided_fixedCross_fibre
#print axioms twoSided_card_le_of_fixedCross_image
#print axioms twoSided_card_le_of_fixedCross
#print axioms fixedCross_heavy_card_le
#print axioms NormalizedTwoSidedWholeRowCardinalityBound.twoSided

end LeanBacklog.RowSpread
