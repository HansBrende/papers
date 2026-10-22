import Mathlib.GroupTheory.CoprodI
import Mathlib.GroupTheory.GroupAction.SubMulAction
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.Tactic

/-! A rational free pair, using the 3-adic norm on nonzero rational vectors.
No completion or projective quotient is needed for the ping-pong action. -/
namespace TransposeFollowup.RationalFreePair
open Classical Set
open scoped Pointwise
set_option autoImplicit false

abbrev Group := Matrix.SpecialLinearGroup (Fin 2) ℚ

def nonzeroVectors : SubMulAction Group (Fin 2 → ℚ) where
  carrier := {v | v ≠ 0}
  smul_mem' g _ hv := (smul_ne_zero_iff_ne g).mpr hv

abbrev Vector := ↥nonzeroVectors

instance primeThree : Fact (Nat.Prime 3) := ⟨by norm_num⟩

def diagonal (a : ℚ) (ha : a ≠ 0) : Group :=
  ⟨!![a, 0; 0, a⁻¹], by simp [Matrix.det_fin_two, ha]⟩

def conjugator : Group := ⟨!![1, 1; 1, 2], by norm_num [Matrix.det_fin_two]⟩

def positiveCone : Set Vector := {v | padicNorm 3 (v.1 1) < padicNorm 3 (v.1 0)}

def negativeCone : Set Vector := {v | padicNorm 3 (v.1 0) < padicNorm 3 (v.1 1)}

theorem positiveCone_nonempty : positiveCone.Nonempty := by
  refine ⟨⟨![1, 0], ?_⟩, ?_⟩
  · change (![1, 0] : Fin 2 → ℚ) ≠ 0
    simp
  · norm_num [positiveCone]

theorem cones_disjoint : Disjoint positiveCone negativeCone := by
  apply Set.disjoint_left.mpr
  intro v hx hy
  exact lt_asymm (show padicNorm 3 (v.1 1) < padicNorm 3 (v.1 0) from hx) hy

theorem vector_norm_pos_of_le (v : Vector)
    (h : padicNorm 3 (v.1 1) ≤ padicNorm 3 (v.1 0)) :
    0 < padicNorm 3 (v.1 0) := by
  apply lt_of_le_of_ne (padicNorm.nonneg _)
  intro he
  have h0 : v.1 0 = 0 := padicNorm.zero_of_padicNorm_eq_zero he.symm
  have h1 : v.1 1 = 0 := padicNorm.zero_of_padicNorm_eq_zero
    (le_antisymm (by simpa [h0] using h) (padicNorm.nonneg _))
  apply v.2
  ext i
  fin_cases i <;> assumption

theorem diagonal_action (a : ℚ) (ha : a ≠ 0) (v : Vector) :
    ((diagonal a ha • v : Vector).1) = ![a * v.1 0, a⁻¹ * v.1 1] := by
  change Matrix.mulVec !![a, 0; 0, a⁻¹] v.1 = _
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem diagonal_inverse (a : ℚ) (ha : a ≠ 0) :
    (diagonal a ha)⁻¹ = diagonal a⁻¹ (inv_ne_zero ha) := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagonal]

theorem conjugator_action (v : Vector) :
    ((conjugator • v : Vector).1) = ![v.1 0 + v.1 1, v.1 0 + 2 * v.1 1] := by
  change Matrix.mulVec !![1, 1; 1, 2] v.1 = _
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem conjugator_equal_norms (v : Vector)
    (h : padicNorm 3 (v.1 0) ≠ padicNorm 3 (v.1 1)) :
    padicNorm 3 ((conjugator • v : Vector).1 0) =
      padicNorm 3 ((conjugator • v : Vector).1 1) := by
  have htwo : padicNorm 3 2 = 1 := by
    exact (padicNorm.nat_eq_one_iff 2).mpr (by norm_num)
  rw [conjugator_action]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [padicNorm.add_eq_max_of_ne h, padicNorm.add_eq_max_of_ne]
  · rw [padicNorm.mul, htwo, one_mul]
  · simpa only [padicNorm.mul, htwo, one_mul] using h

theorem diagonal_positive {a : ℚ} (ha : a ≠ 0) (hn : 1 < padicNorm 3 a) :
    diagonal a ha • negativeConeᶜ ⊆ positiveCone := by
  rintro _ ⟨v, hv, rfl⟩
  have hle : padicNorm 3 (v.1 1) ≤ padicNorm 3 (v.1 0) := le_of_not_gt hv
  have hp := vector_norm_pos_of_le v hle
  change padicNorm 3 ((diagonal a ha • v : Vector).1 1) <
    padicNorm 3 ((diagonal a ha • v : Vector).1 0)
  rw [diagonal_action]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, padicNorm.mul]
  have hi : padicNorm 3 a⁻¹ = (padicNorm 3 a)⁻¹ := by
    simpa only [one_div, padicNorm.one] using padicNorm.div (p := 3) 1 a
  rw [hi]
  have hsmall : (padicNorm 3 a)⁻¹ ≤ 1 := (inv_le_one₀ (by linarith)).mpr hn.le
  calc
    _ ≤ 1 * padicNorm 3 (v.1 0) := mul_le_mul hsmall hle (padicNorm.nonneg _) (by norm_num)
    _ < _ := mul_lt_mul_of_pos_right hn hp

theorem diagonal_negative {a : ℚ} (ha : a ≠ 0) (hn : 1 < padicNorm 3 a) :
    (diagonal a ha)⁻¹ • positiveConeᶜ ⊆ negativeCone := by
  rintro _ ⟨v, hv, rfl⟩
  have hle : padicNorm 3 (v.1 0) ≤ padicNorm 3 (v.1 1) := le_of_not_gt hv
  have hp : 0 < padicNorm 3 (v.1 1) := by
    apply lt_of_le_of_ne (padicNorm.nonneg _)
    intro he
    have h1 : v.1 1 = 0 := padicNorm.zero_of_padicNorm_eq_zero he.symm
    have h0 : v.1 0 = 0 := padicNorm.zero_of_padicNorm_eq_zero
      (le_antisymm (by simpa [h1] using hle) (padicNorm.nonneg _))
    apply v.2
    ext i
    fin_cases i <;> assumption
  change padicNorm 3 (((diagonal a ha)⁻¹ • v : Vector).1 0) <
    padicNorm 3 (((diagonal a ha)⁻¹ • v : Vector).1 1)
  rw [diagonal_inverse, diagonal_action]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    padicNorm.mul, inv_inv]
  have hi : padicNorm 3 a⁻¹ = (padicNorm 3 a)⁻¹ := by
    simpa only [one_div, padicNorm.one] using padicNorm.div (p := 3) 1 a
  rw [hi]
  have hsmall : (padicNorm 3 a)⁻¹ ≤ 1 := (inv_le_one₀ (by linarith)).mpr hn.le
  calc
    _ ≤ 1 * padicNorm 3 (v.1 1) := mul_le_mul hsmall hle (padicNorm.nonneg _) (by norm_num)
    _ < _ := mul_lt_mul_of_pos_right hn hp

theorem cones_conjugates_disjoint :
    Disjoint (positiveCone ∪ negativeCone)
      (conjugator • (positiveCone ∪ negativeCone)) := by
  apply Set.disjoint_left.mpr
  rintro _ hv ⟨w, hw, rfl⟩
  have hwne : padicNorm 3 (w.1 0) ≠ padicNorm 3 (w.1 1) := by
    rcases hw with hw | hw
    · exact ne_of_gt hw
    · exact ne_of_lt hw
  have he := conjugator_equal_norms w hwne
  rcases hv with hv | hv
  · exact (ne_of_gt hv) he
  · exact (ne_of_lt hv) he

theorem conjugate_cone_update (g h : Group) (X Y : Set Vector)
    (hg : g • Yᶜ ⊆ X) : (h * g * h⁻¹) • (h • Y)ᶜ ⊆ h • X := by
  rintro _ ⟨v, hv, rfl⟩
  have hv' : h⁻¹ • v ∈ Yᶜ := by
    intro hy
    apply hv
    exact ⟨h⁻¹ • v, hy, smul_inv_smul h v⟩
  have hg' := hg (Set.mem_smul_set.mpr ⟨h⁻¹ • v, hv', rfl⟩)
  exact ⟨g • (h⁻¹ • v), hg', by simp only [mul_smul]⟩

def generators (a : ℚ) (ha : a ≠ 0) : Bool → Group
  | false => diagonal a ha
  | true => conjugator * diagonal a ha * conjugator⁻¹

def positiveDomains : Bool → Set Vector
  | false => positiveCone
  | true => conjugator • positiveCone

def negativeDomains : Bool → Set Vector
  | false => negativeCone
  | true => conjugator • negativeCone

theorem generators_free {a : ℚ} (ha : a ≠ 0) (hn : 1 < padicNorm 3 a) :
    Function.Injective (FreeGroup.lift (generators a ha)) := by
  have hd := cones_conjugates_disjoint
  have hpp : Disjoint positiveCone (conjugator • positiveCone) :=
    hd.mono Set.subset_union_left (Set.image_mono Set.subset_union_left)
  have hpn : Disjoint positiveCone (conjugator • negativeCone) :=
    hd.mono Set.subset_union_left (Set.image_mono Set.subset_union_right)
  have hnp : Disjoint negativeCone (conjugator • positiveCone) :=
    hd.mono Set.subset_union_right (Set.image_mono Set.subset_union_left)
  have hnn : Disjoint negativeCone (conjugator • negativeCone) :=
    hd.mono Set.subset_union_right (Set.image_mono Set.subset_union_right)
  apply FreeGroup.injective_lift_of_ping_pong (generators a ha)
    positiveDomains negativeDomains
  · intro i
    cases i with
    | false => exact positiveCone_nonempty
    | true =>
      obtain ⟨v, hv⟩ := positiveCone_nonempty
      exact ⟨conjugator • v, ⟨v, hv, rfl⟩⟩
  · intro i j hij
    cases i <;> cases j
    · exact (hij rfl).elim
    · exact hpp
    · exact hpp.symm
    · exact (hij rfl).elim
  · intro i j hij
    cases i <;> cases j
    · exact (hij rfl).elim
    · exact hnn
    · exact hnn.symm
    · exact (hij rfl).elim
  · intro i j
    cases i <;> cases j
    · exact cones_disjoint
    · exact hpn
    · exact hnp.symm
    · exact Set.disjoint_smul_set.mpr cones_disjoint
  · intro i
    cases i with
    | false => exact diagonal_positive ha hn
    | true => exact conjugate_cone_update _ _ _ _ (diagonal_positive ha hn)
  · intro i
    cases i with
    | false => exact diagonal_negative ha hn
    | true =>
      change (conjugator * diagonal a ha * conjugator⁻¹)⁻¹ •
        (conjugator • positiveCone)ᶜ ⊆ conjugator • negativeCone
      simpa only [mul_inv_rev, inv_inv, mul_assoc] using
        conjugate_cone_update (diagonal a ha)⁻¹ conjugator negativeCone positiveCone
          (diagonal_negative ha hn)

end TransposeFollowup.RationalFreePair
