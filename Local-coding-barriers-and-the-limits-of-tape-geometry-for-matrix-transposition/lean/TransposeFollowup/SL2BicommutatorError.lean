import TransposeFollowup.ComplexMatrixProductError

/-! Quantitative comparison of a bicommutator with a triangular model,
using the actual sixteen matrix factors and their inverse entries. -/
namespace TransposeFollowup.SL2Escape
open Classical Matrix
open scoped commutatorElement
set_option autoImplicit false
local notation "G" => Matrix.SpecialLinearGroup (Fin 2) ℂ
local notation "M" => Matrix (Fin 2) (Fin 2) ℂ

def EntryApprox (R δ : ℝ) (g h : G) : Prop :=
  (∀ i j, ‖g i j‖ ≤ R) ∧ (∀ i j, ‖h i j‖ ≤ R) ∧ (∀ i j, ‖g i j - h i j‖ ≤ δ)

theorem complex_sl2_inverse_entry_bound {g : G} {R : ℝ} (hg : ∀ i j, ‖g i j‖ ≤ R) :
    ∀ i j, ‖g⁻¹ i j‖ ≤ R := by
  intro i j
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  fin_cases i <;> fin_cases j
  · exact hg 1 1
  · change ‖-g 0 1‖ ≤ _; simpa only [norm_neg] using hg 0 1
  · change ‖-g 1 0‖ ≤ _; simpa only [norm_neg] using hg 1 0
  · exact hg 0 0

theorem EntryApprox.inv {R δ : ℝ} {g h : G} (he : EntryApprox R δ g h) :
    EntryApprox R δ g⁻¹ h⁻¹ := by
  refine ⟨complex_sl2_inverse_entry_bound he.1, complex_sl2_inverse_entry_bound he.2.1, ?_⟩
  intro i j
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl, Matrix.SpecialLinearGroup.SL2_inv_expl]
  fin_cases i <;> fin_cases j
  · exact he.2.2 1 1
  · change ‖-g 0 1 - -h 0 1‖ ≤ _
    rw [neg_sub_neg, norm_sub_rev]
    exact he.2.2 0 1
  · change ‖-g 1 0 - -h 1 0‖ ≤ _
    rw [neg_sub_neg, norm_sub_rev]
    exact he.2.2 1 0
  · exact he.2.2 0 0

theorem bicommutator_entry_error {a x y a' x' y' : G} {R δ : ℝ}
    (hR : 1 ≤ R) (hδ : 0 ≤ δ)
    (ha : EntryApprox R δ a a') (hx : EntryApprox R δ x x') (hy : EntryApprox R δ y y') :
    ∀ i j, ‖⁅⁅a, x⁆, ⁅a, y⁆⁆ i j - ⁅⁅a', x'⁆, ⁅a', y'⁆⁆ i j‖ ≤ 16 * (2 * R) ^ 16 * δ := by
  let l : List (G × G) := [(a, a'), (x, x'), (a⁻¹, a'⁻¹), (x⁻¹, x'⁻¹),
    (a, a'), (y, y'), (a⁻¹, a'⁻¹), (y⁻¹, y'⁻¹),
    (x, x'), (a, a'), (x⁻¹, x'⁻¹), (a⁻¹, a'⁻¹),
    (y, y'), (a, a'), (y⁻¹, y'⁻¹), (a⁻¹, a'⁻¹)]
  have hai := ha.inv
  have hxi := hx.inv
  have hyi := hy.inv
  have hl : ∀ p ∈ l, EntryApprox R δ p.1 p.2 := by
    intro p hp
    simp only [l, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  have hh := complex_matrix_list_prod_error l (fun p => (p.1 : M)) (fun p => (p.2 : M))
    hR hδ (fun p hp => (hl p hp).1) (fun p hp => (hl p hp).2.1) (fun p hp => (hl p hp).2.2)
  simpa [l, commutatorElement_def, _root_.mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul, mul_assoc] using hh

theorem bicommutator_trace_error {a x y a' x' y' g : G} {R δ : ℝ}
    (hR : 1 ≤ R) (hδ : 0 ≤ δ)
    (ha : EntryApprox R δ a a') (hx : EntryApprox R δ x x') (hy : EntryApprox R δ y y')
    (ha' : a' 1 0 = 0) (hx' : x' 1 0 = 0) (hy' : y' 1 0 = 0)
    (hg : ∀ i j, ‖g i j‖ ≤ R) :
    ‖Matrix.trace ((⁅⁅a, x⁆, ⁅a, y⁆⁆ * g : G) : M) - Matrix.trace (g : M)‖ ≤
      64 * R * (2 * R) ^ 16 * δ := by
  have he := bicommutator_entry_error hR hδ ha hx hy
  rw [upper_bicommutator_eq_one ha' hx' hy'] at he
  have hh := complex_matrix_trace_error (b := ((⁅⁅a, x⁆, ⁅a, y⁆⁆ : G) : M)) he hg
  convert hh using 1
  ring

end TransposeFollowup.SL2Escape
