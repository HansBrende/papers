import TransposeFollowup.IncidenceFiberMoments
import TransposeFollowup.WeightedFiberSelection

/-! A measurable dense relation has one large fiber in which almost
all pairs have many common neighbors. This is the weak-BSG selection. -/
namespace TransposeFollowup
open Classical MeasureTheory Set
open scoped ENNReal
set_option autoImplicit false

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem exists_large_fiber_few_low_codegrees (μ : Measure X) (ν : Measure Y)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {E : Set (X × Y)} (hE : MeasurableSet E)
    (hμ0 : 0 < μ univ) (hν0 : 0 < ν univ) {T : Set Y} (hT : ∀ᵐ y ∂ν, y ∈ T)
    {K ε : ℝ≥0∞} (hK : 0 < K) (hKt : K ≠ ⊤) (hε : 0 < ε) (hεt : ε ≠ ⊤)
    (hdense : μ univ * ν univ ≤ K * (μ.prod ν) E) :
    let t := ε * ν univ / (2 * K ^ 2)
    ∃ y ∈ T, μ univ ^ 2 < 4 * K ^ 2 * edgeFiberMass μ E y ^ 2 ∧
      edgeBadFiberMass μ ν E t y < ε * edgeFiberMass μ E y ^ 2 := by
  let u := μ univ
  let v := ν univ
  let z := u ^ 2 / (4 * K ^ 2)
  let t := ε * v / (2 * K ^ 2)
  let S := ∫⁻ y, edgeFiberMass μ E y ^ 2 ∂ν
  have hden4 : (4 * K ^ 2) * z = u ^ 2 :=
    ENNReal.mul_div_cancel (by positivity) (by finiteness)
  have hden2 : (2 * K ^ 2) * t = ε * v :=
    ENNReal.mul_div_cancel (by positivity) (by finiteness)
  have hmoment : u ^ 2 * v ≤ K ^ 2 * S := by
    apply (ENNReal.mul_le_mul_iff_left hν0.ne' (measure_ne_top ν univ)).mp
    calc
      (u ^ 2 * v) * v = (u * v) ^ 2 := by ring
      _ ≤ (K * (μ.prod ν) E) ^ 2 := pow_le_pow_left' hdense 2
      _ = K ^ 2 * ((μ.prod ν) E) ^ 2 := mul_pow _ _ _
      _ ≤ K ^ 2 * (S * v) := mul_le_mul' le_rfl (edgeFiberMass_second_moment_lower μ ν hE)
      _ = (K ^ 2 * S) * v := by ring
  have hlarge : 4 * z * v ≤ S := by
    apply (ENNReal.mul_le_mul_iff_right (pow_ne_zero 2 hK.ne') (by finiteness)).mp
    calc
      K ^ 2 * (4 * z * v) = ((4 * K ^ 2) * z) * v := by ring
      _ = u ^ 2 * v := by rw [hden4]
      _ ≤ K ^ 2 * S := hmoment
  have hsmall : (∫⁻ y, edgeBadFiberMass μ ν E t y ∂ν) ≤ 2 * ε * z * v := by
    calc
      _ ≤ t * u ^ 2 := edgeBadFiberMass_lintegral_le μ ν hE t
      _ ≤ 2 * ε * z * v := by
        apply (ENNReal.mul_le_mul_iff_right (by positivity : 2 * K ^ 2 ≠ 0) (by finiteness)).mp
        calc
          (2 * K ^ 2) * (t * u ^ 2) = ((2 * K ^ 2) * t) * u ^ 2 := by ring
          _ = (ε * v) * u ^ 2 := by rw [hden2]
          _ = (ε * v) * ((4 * K ^ 2) * z) := by rw [hden4]
          _ ≤ (2 * K ^ 2) * (2 * ε * z * v) := le_of_eq (by ring)
  have hz : 0 < z := ENNReal.div_pos (by positivity) (by finiteness)
  have hzt : z ≠ ⊤ := by dsimp [z, u]; finiteness
  obtain ⟨y, hy, hsize, hbad⟩ := exists_large_weight_small_error ν
    ((edgeFiberMass_measurable μ hE).pow_const 2) hT hν0 (measure_ne_top ν univ)
    hε hεt hz hzt hlarge hsmall
  refine ⟨y, hy, ?_, hbad⟩
  have hp := (ENNReal.mul_lt_mul_iff_right (by positivity : 4 * K ^ 2 ≠ 0) (by finiteness)).mpr hsize
  rwa [hden4] at hp

end TransposeFollowup
