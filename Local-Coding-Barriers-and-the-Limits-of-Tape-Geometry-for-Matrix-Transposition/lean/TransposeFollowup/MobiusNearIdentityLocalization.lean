import TransposeFollowup.CoordinateCoverRefinement
import TransposeFollowup.MobiusLocalCoverGeometry
import TransposeFollowup.HaarLocalPacking

/-! A bounded symmetric set is covered by explicitly many translates
of its square intersected with a prescribed identity neighborhood. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory Set
open scoped ENNReal Pointwise
set_option autoImplicit false

theorem exists_near_identity_translate_cover {U : Set Group} {Q α : ℝ}
    (hQ : 1 ≤ Q) (hα : 0 < α) (hαone : α ≤ 1)
    (hUb : U ⊆ matrixEntryBox Q) (hUi : U⁻¹ = U) :
    ∃ Z : Finset Group, (Z : Set Group) ⊆ U ∧
      (Z.card : ℝ≥0∞) ≤ ENNReal.ofReal (33 ^ 4 * Q ^ 8 / α ^ 4) ∧
      U ⊆ (Z : Set Group) * (U ^ 2 ∩ mobiusIdentityBall α) := by
  have hQ0 : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  let δ := α / (8 * Q)
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hpatch : ∀ g ∈ U, ∃ f ∈ ({1} : Finset Group), ∀ i j, |g i j - f i j| ≤ 2 * Q := by
    intro g hg
    refine ⟨1, Finset.mem_singleton_self _, fun i j => ?_⟩
    calc
      _ ≤ |g i j| + |(1 : Group) i j| := abs_sub _ _
      _ ≤ Q + 1 := add_le_add (hUb hg i j) (one_mem_matrixEntryBox i j)
      _ ≤ _ := by linarith
  obtain ⟨Z, hZ, hcard, hclose⟩ := BoundedCoordinatePacking.exists_coordinate_refinement
    (fun g : Group => fun i j => g i j) {1} hδ hpatch
  have hb : (BoundedCoordinatePacking.binCount (2 * Q) δ : ℝ) ≤ 33 * Q ^ 2 / α := by
    have hh := BoundedCoordinatePacking.binCount_le (by positivity : 0 ≤ 2 * Q) hδ
    have he : 2 * (2 * Q) / δ = 32 * Q ^ 2 / α := by dsimp only [δ]; field_simp; ring
    rw [he] at hh
    have hone : 1 ≤ Q ^ 2 / α := (le_div_iff₀ hα).mpr (by nlinarith)
    calc
      _ ≤ 32 * Q ^ 2 / α + 1 := hh
      _ ≤ 32 * Q ^ 2 / α + Q ^ 2 / α := add_le_add le_rfl hone
      _ = _ := by ring
  have hreal : (Z.card : ℝ) ≤ 33 ^ 4 * Q ^ 8 / α ^ 4 := by
    calc
      (Z.card : ℝ) ≤ (BoundedCoordinatePacking.binCount (2 * Q) δ : ℝ) ^ 4 := by
        exact_mod_cast (by simpa only [Finset.card_singleton, one_mul] using hcard)
      _ ≤ (33 * Q ^ 2 / α) ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg _) hb 4
      _ = _ := by ring
  refine ⟨Z, hZ, ?_, ?_⟩
  · simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hreal
  · intro g hg
    obtain ⟨z, hz, hgz⟩ := hclose g hg
    have hzi : z⁻¹ ∈ U := by
      rw [← hUi]
      simpa only [Set.mem_inv, inv_inv] using hZ hz
    have hsmall : z⁻¹ * g ∈ mobiusIdentityBall α := by
      apply RationalFreePair.real_inv_mul_mem_identityBall (matrixEntryBox_inv (hUb (hZ hz)))
        (fun i j => (hgz i j).le)
      have he : 4 * Q * δ = α / 2 := by dsimp only [δ]; field_simp; ring
      rw [he]
      linarith
    refine Set.mem_mul.mpr ⟨z, hz, z⁻¹ * g, ⟨?_, hsmall⟩, mul_inv_cancel_left z g⟩
    simpa only [pow_two] using Set.mul_mem_mul hzi hg

variable [MeasurableSpace Group] [BorelSpace Group]

theorem near_identity_square_geometry {U : Set Group} {α : ℝ}
    (hU1 : 1 ∈ U) (hUo : IsOpen U) (hUi : U⁻¹ = U)
    (hα : 0 < α) (hαone : α ≤ 1) :
    let A := U ^ 2 ∩ mobiusIdentityBall α
    1 ∈ A ∧ IsOpen A ∧ A⁻¹ = A ∧ IsCompact (closure A) ∧
      closure A ⊆ matrixEntryBox 2 ∧ 0 < (Measure.haar : Measure Group) A ∧
      (Measure.haar : Measure Group) A < ⊤ ∧ A ^ 3 ⊆ U ^ 6 := by
  let A := U ^ 2 ∩ mobiusIdentityBall α
  have hA1 : 1 ∈ A := ⟨Set.one_mem_pow hU1, one_mem_mobiusIdentityBall hα⟩
  have hU2o : IsOpen (U ^ 2) := by simpa only [pow_two] using hUo.mul_right
  have hAo : IsOpen A := hU2o.inter (mobiusIdentityBall_isOpen α)
  have hUb_inv {g : Group} (hg : g ∈ U) : g⁻¹ ∈ U := by
    rw [← hUi]
    simpa only [Set.mem_inv, inv_inv] using hg
  have hAi_mem {g : Group} (hg : g ∈ A) : g⁻¹ ∈ A := by
    refine ⟨?_, ?_⟩
    · obtain ⟨u, hu, v, hv, rfl⟩ := Set.mem_mul.mp (by simpa only [pow_two] using hg.1)
      simpa only [mul_inv_rev, pow_two] using Set.mul_mem_mul (hUb_inv hv) (hUb_inv hu)
    · rw [← mobiusIdentityBall_inv α]
      simpa only [Set.mem_inv, inv_inv] using hg.2
  have hAi : A⁻¹ = A := by
    ext g
    change g⁻¹ ∈ A ↔ g ∈ A
    exact ⟨fun hg => by simpa only [inv_inv] using hAi_mem hg, fun hg => hAi_mem hg⟩
  have hAb : A ⊆ matrixEntryBox 2 :=
    Set.inter_subset_right.trans (mobiusIdentityBall_subset_entryBox_two hα hαone)
  have hAc : closure A ⊆ matrixEntryBox 2 := closure_minimal hAb (matrixEntryBox_isCompact _).isClosed
  refine ⟨hA1, hAo, hAi, (matrixEntryBox_isCompact _).of_isClosed_subset isClosed_closure hAc,
    hAc, hAo.measure_pos _ ⟨1, hA1⟩,
    (measure_mono hAb).trans_lt (matrixEntryBox_isCompact _).measure_lt_top, ?_⟩
  calc
    A ^ 3 ⊆ (U ^ 2) ^ 3 := Set.pow_subset_pow_left Set.inter_subset_left
    _ = U ^ 6 := by rw [← pow_mul]

theorem near_identity_square_volume_bounds {U : Set Group} (Y : Finset Group) {Q α : ℝ}
    (hQ : 1 ≤ Q) (hα : 0 < α) (hαone : α ≤ 1)
    (hUb : U ⊆ matrixEntryBox Q) (hUi : U⁻¹ = U)
    (hcover : U ^ 2 ⊆ (Y : Set Group) * U) :
    let H : Measure Group := Measure.haar
    let A := U ^ 2 ∩ mobiusIdentityBall α
    H U ≤ ENNReal.ofReal (33 ^ 4 * Q ^ 8 / α ^ 4) * H A ∧
      H A ≤ (Y.card : ℝ≥0∞) * H U := by
  obtain ⟨Z, _, hcard, hcov⟩ := exists_near_identity_translate_cover hQ hα hαone hUb hUi
  exact ⟨(measure_le_of_finite_left_cover Measure.haar Z hcov).trans (mul_le_mul' hcard le_rfl),
    (measure_mono Set.inter_subset_left).trans (measure_le_of_finite_left_cover Measure.haar Y hcover)⟩

end TransposeFollowup.RealMobius
