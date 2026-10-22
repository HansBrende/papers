import TransposeFollowup.NormalizedCentralizerChart
import TransposeFollowup.BoundedCoordinatePacking

/-! Retain a quantitatively large finite part of a common centralizer,
normalize it at an actual member, and certify the chart and separation
bounds required by cubic packing. -/
namespace TransposeFollowup.SL2Projection
open Classical Matrix BoundedCoordinatePacking
open scoped Matrix.Norms.Frobenius
set_option autoImplicit false
local notation "RMat" => Matrix (Fin 2) (Fin 2) ℝ
local notation "G" => Matrix.SpecialLinearGroup (Fin 2) ℝ

theorem exists_localized_centered_parameters {ι : Type*} [Fintype ι]
    (f : ι → G) (b : RMat) (c t : ι → ℝ) {B M ρ r δ : ℝ} {m : ℕ}
    (hB : 1 ≤ B) (hM : 1 ≤ M) (hρ : 0 < ρ) (hδ : 0 < δ)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hm : 0 < m)
    (hb : Matrix.trace b = 0) (hbn : ‖b‖ ≤ M) (hbd : |b.det| ≤ M)
    (hpivot : ∃ i, ρ ≤ |noncentralCoordinates b i|)
    (hf : ∀ x i j, |f x i j| ≤ B)
    (hform : ∀ x, (f x : RMat) = scalarAffine b (c x) (t x))
    (hbranch : 8 * B * δ ≤ 1) (hradius : 8 * B * δ ≤ ρ * r)
    (hcard : binCount B δ ^ 4 * m ≤ Fintype.card ι) :
    ∃ S : Finset ι, m ≤ S.card ∧ ∃ x₀ ∈ S, ∃ p q : ι → ℝ,
      (∀ x, (((f x₀)⁻¹ * f x : G) : RMat) = scalarAffine b (p x) (q x)) ∧
      (∀ x ∈ S, 1 / 2 ≤ p x ∧ |q x| ≤ r) ∧
      (∀ x ∈ S, dist (f x : RMat) (f x₀ : RMat) ≤ 2 * δ) ∧
      (∀ x ∈ S, ∀ y ∈ S,
        dist (f x : RMat) (f y : RMat) ≤ 10 * B * M * |q x - q y|) := by
  have hB0 : 0 ≤ B := by linarith
  obtain ⟨S, hS, hclose⟩ := exists_cluster (fun x i j => f x i j) hδ hf hcard
  obtain ⟨x₀, hx₀⟩ := Finset.card_pos.mp (hm.trans_le hS)
  let p : ι → ℝ := fun x => c x₀ * c x + t x₀ * t x * b.det
  let q : ι → ℝ := fun x => c x₀ * t x - t x₀ * c x
  have hnform (x : ι) : (((f x₀)⁻¹ * f x : G) : RMat) = scalarAffine b (p x) (q x) := by
    rw [Matrix.SpecialLinearGroup.coe_mul, sl2_scalarAffine_inv b (f x₀) (hform x₀),
      hform x, scalarAffine_mul, hb]
    dsimp only [p, q]
    congr 1 <;> ring
  have hdist (x : ι) (hx : x ∈ S) : dist (f x : RMat) (f x₀ : RMat) ≤ 2 * δ :=
    frobenius_dist_le_of_entry_error hδ.le (fun i j => (hclose x hx x₀ hx₀ i j).le)
  have hchart (x : ι) (hx : x ∈ S) : 1 / 2 ≤ p x ∧ |q x| ≤ r := by
    have hn : dist (((f x₀)⁻¹ * f x : G) : RMat) 1 ≤ 4 * B * δ := by
      calc
        _ ≤ 2 * B * dist (f x : RMat) (f x₀ : RMat) :=
          dist_normalized_from_one_le (f x₀) (f x) hB0 (hf x₀)
        _ ≤ 2 * B * (2 * δ) := mul_le_mul_of_nonneg_left (hdist x hx) (by positivity)
        _ = _ := by ring
    obtain ⟨hc, ht⟩ := centered_parameters_of_distance b ((f x₀)⁻¹ * f x)
      hb hρ hpivot (hnform x) hn
    constructor
    · linarith [(abs_le.mp hc).1]
    · apply ht.trans
      apply (div_le_iff₀ hρ).mpr
      nlinarith only [hradius]
  refine ⟨S, hS, x₀, hx₀, p, q, hnform, hchart, hdist, ?_⟩
  intro x hx y hy
  exact normalized_parameter_distance_bound b (f x₀) (f x) (f y) hM hB0 hr hr1
    hb hbn hbd (hf x₀) (hnform x) (hnform y)
    (hchart x hx).1 (hchart y hy).1 (hchart x hx).2 (hchart y hy).2

end TransposeFollowup.SL2Projection
