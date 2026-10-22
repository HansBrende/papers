import TransposeFollowup.SL2TraceProjection
import TransposeFollowup.CoordinateCoverRefinement

/-! A finite cover from three scalar measurements, with a cubic
refinement loss, and its application to an actual SL2 trace patch. -/
namespace TransposeFollowup.BoundedCoordinatePacking
open Classical Set
set_option autoImplicit false

theorem exists_three_measurement_cover {X Y : Type*} [PseudoMetricSpace Y]
    (a : X → Y) (f : Fin 3 → X → ℝ) {A : Set X} {C η : ℝ}
    (hC : 0 ≤ C) (hη : 0 < η)
    (hrec : ∀ x ∈ A, ∀ y ∈ A, ∀ {t : ℝ}, 0 ≤ t →
      (∀ k, |f k x - f k y| ≤ t) → dist (a x) (a y) ≤ C * t)
    (F : Fin 3 → Finset ℝ)
    (hF : ∀ x ∈ A, ∀ k, ∃ c ∈ F k, |f k x - c| ≤ η) :
    ∃ E : Finset X, (E : Set X) ⊆ A ∧
      E.card ≤ (∏ k : Fin 3, (F k).card) * binCount η (η / (C + 1)) ^ 3 ∧
      ∀ x ∈ A, ∃ e ∈ E, dist (a x) (a e) ≤ η := by
  let δ := η / (C + 1)
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hc : ∀ x : A, ∀ k : Fin 3, ∃ c : F k, |f k x - (c : ℝ)| ≤ η := by
    intro x k
    obtain ⟨c, hc, he⟩ := hF x x.2 k
    exact ⟨⟨c, hc⟩, he⟩
  choose center hcenter using hc
  let K := binCount η δ
  let Label := (k : Fin 3) → F k × Fin K
  let code (x : A) : Label := fun k => (center x k,
    ⟨bin η δ (f k x - (center x k : ℝ)), bin_lt hδ (hcenter x k)⟩)
  obtain ⟨P, hcard, hrep⟩ := exists_finite_code_representatives code
  have hsize : Fintype.card Label = (∏ k : Fin 3, (F k).card) * K ^ 3 := by
    simp only [Label, Fintype.card_pi, Fintype.card_prod, Fintype.card_coe,
      Fintype.card_fin, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  refine ⟨P.image Subtype.val, ?_, Finset.card_image_le.trans (hcard.trans_eq hsize), ?_⟩
  · intro x hx
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hx
    exact y.2
  · intro x hx
    obtain ⟨e, he, hcode⟩ := hrep ⟨x, hx⟩
    refine ⟨e, Finset.mem_image.mpr ⟨e, he, rfl⟩, ?_⟩
    have hclose (k : Fin 3) : |f k x - f k e| < δ := by
      have hcent : center e k = center ⟨x, hx⟩ k := congrArg (fun z : Label => (z k).1) hcode
      have hbin := congrArg (fun z : Label => (z k).2.val) hcode
      have hh := same_bin_close hδ (hcenter ⟨x, hx⟩ k) (hcenter e k) hbin.symm
      rw [hcent] at hh
      convert hh using 1
      congr 1
      ring
    calc
      dist (a x) (a e) ≤ C * δ := hrec x hx e e.2 hδ.le (fun k => (hclose k).le)
      _ ≤ η := by
        dsimp only [δ]
        rw [← mul_div_assoc, div_le_iff₀ (by positivity : (0 : ℝ) < C + 1)]
        nlinarith

theorem three_measurement_bin_bound {C η : ℝ} (hC : 0 ≤ C) (hη : 0 < η) :
    (binCount η (η / (C + 1)) : ℝ) ≤ 2 * C + 3 := by
  have hh := binCount_le hη.le (by positivity : (0 : ℝ) < η / (C + 1))
  convert hh using 1
  field_simp
  ring

end TransposeFollowup.BoundedCoordinatePacking

namespace TransposeFollowup.SL2Projection
open Classical Matrix Set BoundedCoordinatePacking
open scoped Matrix.Norms.Frobenius
set_option autoImplicit false
local notation "RMat" => Matrix (Fin 2) (Fin 2) ℝ
local notation "G" => Matrix.SpecialLinearGroup (Fin 2) ℝ

theorem exists_local_three_trace_cover (g : Fin 4 → G) (z : G) {M d r : ℝ}
    (hM : 1 ≤ M) (hd : 0 < d) (hr : 0 ≤ r)
    (hg : ∀ i j k, |g i j k| ≤ M) (hz : ∀ j k, |z j k| ≤ M)
    (hz0 : 1 / 2 ≤ |z 0 0|) (hdet : d ≤ |(traceFrame g).det|)
    (hsmall : 6144 * M ^ 5 * r ≤ d) :
    ∃ i : Fin 4, ∀ {A : Set G} {η : ℝ}, 0 < η →
      (∀ x ∈ A, ∀ j k, |x j k - z j k| ≤ r) →
      ∀ F : Fin 3 → Finset ℝ,
      (∀ x ∈ A, ∀ k, ∃ c ∈ F k,
        |Matrix.trace (((g (i.succAbove k))⁻¹ * x : G) : RMat) - c| ≤ η) →
      ∃ E : Finset G, (E : Set G) ⊆ A ∧
        (E.card : ℝ) ≤ (∏ k : Fin 3, ((F k).card : ℝ)) * (6144 * M ^ 5 / d + 3) ^ 3 ∧
        ∀ x ∈ A, ∃ e ∈ E, dist (x : RMat) (e : RMat) ≤ η := by
  obtain ⟨i, hrec⟩ := exists_local_three_trace_projection g z hM hd hr hg hz hz0 hdet hsmall
  refine ⟨i, ?_⟩
  intro A η hη hpatch F hF
  let C := 3072 * M ^ 5 / d
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hmeasure : ∀ x ∈ A, ∀ y ∈ A, ∀ {t : ℝ}, 0 ≤ t →
      (∀ k : Fin 3,
        |Matrix.trace (((g (i.succAbove k))⁻¹ * x : G) : RMat) -
          Matrix.trace (((g (i.succAbove k))⁻¹ * y : G) : RMat)| ≤ t) →
      dist (x : RMat) (y : RMat) ≤ C * t := by
    intro x hx y hy t ht htrace
    have hh := hrec x y ht (hpatch x hx) (hpatch y hy) (by
      intro j hj
      obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
      exact htrace k)
    simpa only [C, div_mul_eq_mul_div, mul_assoc] using hh
  obtain ⟨E, hE, hcard, hcover⟩ := exists_three_measurement_cover
    (fun x : G => (x : RMat))
    (fun k x => Matrix.trace (((g (i.succAbove k))⁻¹ * x : G) : RMat)) hC hη hmeasure F hF
  refine ⟨E, hE, ?_, hcover⟩
  have hcard' : (E.card : ℝ) ≤ (∏ k : Fin 3, ((F k).card : ℝ)) *
      (binCount η (η / (C + 1)) : ℝ) ^ 3 := by exact_mod_cast hcard
  have hb := three_measurement_bin_bound hC hη
  calc
    _ ≤ (∏ k : Fin 3, ((F k).card : ℝ)) * (2 * C + 3) ^ 3 := by
      apply hcard'.trans
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (Nat.cast_nonneg _) hb 3)
        (Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _))
    _ = _ := by dsimp only [C]; congr 2; ring

end TransposeFollowup.SL2Projection
