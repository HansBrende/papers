import TransposeFollowup.SL2BicommutatorError
import TransposeFollowup.SL2ConjugacyFiber

/-! Apply the existing finite-product error theorem directly to the ten
factors of a normalized cubic product. This also charges the error of
the chosen normalization center, without a separate inverse-metric chain. -/
namespace TransposeFollowup.SL2Projection
open Classical Matrix SL2Escape
open scoped Matrix.Norms.Frobenius
set_option autoImplicit false
local notation "CMat" => Matrix (Fin 2) (Fin 2) ℂ
local notation "CG" => Matrix.SpecialLinearGroup (Fin 2) ℂ
local notation "RMat" => Matrix (Fin 2) (Fin 2) ℝ
local notation "G" => Matrix.SpecialLinearGroup (Fin 2) ℝ

theorem complex_normalized_cubic_product_error (f a : Fin 3 → CG) (c d u v : CG)
    {R ε : ℝ} (hR : 1 ≤ R) (hε : 0 ≤ ε)
    (hc : EntryApprox R ε c d) (hf : ∀ k, EntryApprox R ε (f k) (a k))
    (hu : ∀ i j, ‖u i j‖ ≤ R) (hv : ∀ i j, ‖v i j‖ ≤ R) :
    ∀ i j, ‖((c⁻¹ * f 0) * (u * (c⁻¹ * f 1) * u⁻¹) *
        (v * (c⁻¹ * f 2) * v⁻¹) : CG) i j -
      ((d⁻¹ * a 0) * (u * (d⁻¹ * a 1) * u⁻¹) *
        (v * (d⁻¹ * a 2) * v⁻¹) : CG) i j‖ ≤ 10 * (2 * R) ^ 10 * ε := by
  have huu : EntryApprox R ε u u := ⟨hu, hu, by simpa using fun _ _ : Fin 2 => hε⟩
  have hvv : EntryApprox R ε v v := ⟨hv, hv, by simpa using fun _ _ : Fin 2 => hε⟩
  have hci := hc.inv
  have hui := huu.inv
  have hvi := hvv.inv
  have h₀ := hf 0
  have h₁ := hf 1
  have h₂ := hf 2
  let l : List (CG × CG) := [(c⁻¹, d⁻¹), (f 0, a 0), (u, u),
    (c⁻¹, d⁻¹), (f 1, a 1), (u⁻¹, u⁻¹), (v, v),
    (c⁻¹, d⁻¹), (f 2, a 2), (v⁻¹, v⁻¹)]
  have hl : ∀ p ∈ l, EntryApprox R ε p.1 p.2 := by
    intro p hp
    simp only [l, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  have he := complex_matrix_list_prod_error l (fun p => (p.1 : CMat))
    (fun p => (p.2 : CMat)) hR hε
    (fun p hp => (hl p hp).1) (fun p hp => (hl p hp).2.1) (fun p hp => (hl p hp).2.2)
  simpa [l, Matrix.SpecialLinearGroup.coe_mul, mul_assoc] using he

theorem normalized_cubic_product_dist_error (f a : Fin 3 → G) (c d u v : G)
    {R ε : ℝ} (hR : 1 ≤ R) (hε : 0 ≤ ε)
    (hc : ∀ i j, |c i j| ≤ R) (hd : ∀ i j, |d i j| ≤ R)
    (hf : ∀ k i j, |f k i j| ≤ R) (ha : ∀ k i j, |a k i j| ≤ R)
    (hu : ∀ i j, |u i j| ≤ R) (hv : ∀ i j, |v i j| ≤ R)
    (hec : dist (c : RMat) (d : RMat) ≤ ε)
    (hef : ∀ k, dist (f k : RMat) (a k : RMat) ≤ ε) :
    dist (((c⁻¹ * f 0) * (u * (c⁻¹ * f 1) * u⁻¹) *
        (v * (c⁻¹ * f 2) * v⁻¹) : G) : RMat)
      (((d⁻¹ * a 0) * (u * (d⁻¹ * a 1) * u⁻¹) *
        (v * (d⁻¹ * a 2) * v⁻¹) : G) : RMat) ≤ 20 * (2 * R) ^ 10 * ε := by
  let e : G →* CG := Matrix.SpecialLinearGroup.map Complex.ofRealHom
  have heb (x : G) (hx : ∀ i j, |x i j| ≤ R) : ∀ i j, ‖e x i j‖ ≤ R := by
    intro i j
    change ‖Complex.ofReal (x i j)‖ ≤ R
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hx i j
  have hee (x y : G) (hxy : dist (x : RMat) (y : RMat) ≤ ε) :
      ∀ i j, ‖e x i j - e y i j‖ ≤ ε := by
    intro i j
    change ‖Complex.ofReal (x i j) - Complex.ofReal (y i j)‖ ≤ ε
    simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using
      (entry_error_le_frobenius_dist (x : RMat) (y : RMat) i j).trans hxy
  have he := complex_normalized_cubic_product_error (fun k => e (f k))
    (fun k => e (a k)) (e c) (e d) (e u) (e v) hR hε
    ⟨heb c hc, heb d hd, hee c d hec⟩
    (fun k => ⟨heb (f k) (hf k), heb (a k) (ha k), hee (f k) (a k) (hef k)⟩)
    (heb u hu) (heb v hv)
  have he' : ∀ i j, |((c⁻¹ * f 0) * (u * (c⁻¹ * f 1) * u⁻¹) *
        (v * (c⁻¹ * f 2) * v⁻¹) : G) i j -
      ((d⁻¹ * a 0) * (u * (d⁻¹ * a 1) * u⁻¹) *
        (v * (d⁻¹ * a 2) * v⁻¹) : G) i j| ≤ 10 * (2 * R) ^ 10 * ε := by
    intro i j
    have hh := he i j
    simp only [← map_inv, ← map_mul] at hh
    change ‖Complex.ofReal _ - Complex.ofReal _‖ ≤ _ at hh
    simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using hh
  have hh := frobenius_dist_le_of_entry_error (by positivity : 0 ≤ 10 * (2 * R) ^ 10 * ε) he'
  convert hh using 1
  ring

end TransposeFollowup.SL2Projection
