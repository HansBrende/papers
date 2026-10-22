import TransposeFollowup.AffineGridMass
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Data.Finset.Lattice.Fold

/-! One mesh threshold controls all collisions in a finite family of distinct
affine maps. Coefficients need not be positive, and a common slope is handled
by exact offset separation rather than a false Jacobian estimate. -/
namespace TransposeFollowup.AffineMotion
open Classical Set Finset MeasureTheory
open scoped ENNReal BigOperators
set_option autoImplicit false

theorem exists_small_pair_grid_collision (a b c d : ℝ) (hne : (a,b) ≠ (c,d))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ h, 0 < h → h ≤ ρ →
      volume {x : ℝ | ⌊(a*x+b)/h⌋=⌊(c*x+d)/h⌋} ≤ ENNReal.ofReal ε := by
  by_cases hac : a=c
  · subst c
    have hbd : b ≠ d := fun he => hne (Prod.ext rfl he)
    refine ⟨|b-d|,abs_pos.mpr (sub_ne_zero.mpr hbd),fun h hh hρ => ?_⟩
    rw [affine_grid_collision_empty_same_slope hh a b d hρ,measure_empty]
    exact bot_le
  · have hd : 0 < |a-c| := abs_pos.mpr (sub_ne_zero.mpr hac)
    refine ⟨ε*|a-c|/2,by positivity,fun h hh hρ => ?_⟩
    apply (volume_affine_grid_collision hh hac b d).trans
    apply ENNReal.ofReal_le_ofReal
    apply (div_le_iff₀ hd).mpr
    linarith

noncomputable def gridCollisions {ι : Type*} (a b : ι → ℝ) (h : ℝ) : Set ℝ :=
  ⋃ p : ι × ι, if p.1=p.2 then ∅ else
    {x : ℝ | ⌊(a p.1*x+b p.1)/h⌋=⌊(a p.2*x+b p.2)/h⌋}

theorem measurableSet_gridCollisions {ι : Type*} [Fintype ι]
    (a b : ι → ℝ) (h : ℝ) : MeasurableSet (gridCollisions a b h) := by
  apply MeasurableSet.iUnion
  intro p
  split_ifs
  · exact MeasurableSet.empty
  · exact measurableSet_eq_fun
      ((show Measurable (fun x : ℝ => (a p.1*x+b p.1)/h) by fun_prop).floor)
      ((show Measurable (fun x : ℝ => (a p.2*x+b p.2)/h) by fun_prop).floor)

theorem grid_injective_off_collisions {ι : Type*} (a b : ι → ℝ) (h x : ℝ)
    (hx : x ∉ gridCollisions a b h) :
    Function.Injective (fun i => ⌊(a i*x+b i)/h⌋) := by
  intro i j he
  by_contra hij
  apply hx
  apply Set.mem_iUnion.mpr
  exact ⟨(i,j),by simpa only [hij,ite_false,Set.mem_ofPred_eq] using he⟩

theorem grid_not_mem_collisions_of_injective {ι : Type*} (a b : ι → ℝ) (h x : ℝ)
    (hinj : Function.Injective (fun i => ⌊(a i*x+b i)/h⌋)) :
    x ∉ gridCollisions a b h := by
  intro hx
  obtain ⟨p,hp⟩ := Set.mem_iUnion.mp hx
  by_cases he : p.1=p.2
  · simp only [he,ite_true,Set.notMem_empty] at hp
  · have hc : ⌊(a p.1*x+b p.1)/h⌋=⌊(a p.2*x+b p.2)/h⌋ := by
      simpa only [he,ite_false,Set.mem_ofPred_eq] using hp
    exact he (hinj hc)

theorem exists_small_grid_collisions {ι : Type*} [Fintype ι]
    (a b : ι → ℝ) (hinj : Function.Injective (fun i => (a i,b i)))
    {η : ℝ} (hη : 0 < η) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ h, 0 < h → h ≤ ρ →
      volume (gridCollisions a b h) ≤ ENNReal.ofReal η := by
  let N := Fintype.card (ι × ι)
  let ε : ℝ := η/(N+1)
  have hε : 0 < ε := by dsimp [ε]; positivity
  let E (p : ι × ι) (h : ℝ) : Set ℝ := if p.1=p.2 then ∅ else
    {x : ℝ | ⌊(a p.1*x+b p.1)/h⌋=⌊(a p.2*x+b p.2)/h⌋}
  have hp (p : ι × ι) : ∃ r : ℝ, 0 < r ∧ ∀ h, 0 < h → h ≤ r →
      volume (E p h) ≤ ENNReal.ofReal ε := by
    by_cases he : p.1=p.2
    · refine ⟨1,zero_lt_one,fun h _ _ => ?_⟩
      simp only [E,he,ite_true,measure_empty]
      exact bot_le
    · obtain ⟨r,hr,hb⟩ := exists_small_pair_grid_collision
        (a p.1) (b p.1) (a p.2) (b p.2) (fun h => he (hinj h)) hε
      exact ⟨r,hr,fun h hh hle => by simpa only [E,he,ite_false] using hb h hh hle⟩
  choose r hr hbound using hp
  let R : Option (ι × ι) → ℝ := fun p => p.elim 1 r
  let ρ := Finset.univ.inf' Finset.univ_nonempty R
  have hρ : 0 < ρ := by
    apply (Finset.lt_inf'_iff _).mpr
    intro p _
    cases p with
    | none => exact zero_lt_one
    | some p => exact hr p
  have hρle (p : ι × ι) : ρ ≤ r p :=
    Finset.inf'_le R (Finset.mem_univ (some p))
  refine ⟨ρ,hρ,fun h hh hle => ?_⟩
  calc
    volume (gridCollisions a b h) ≤ ∑ p, volume (E p h) := measure_iUnion_fintype_le volume _
    _ ≤ ∑ _p : ι × ι, ENNReal.ofReal ε :=
      Finset.sum_le_sum (fun p _ => hbound p h hh (hle.trans (hρle p)))
    _ = ENNReal.ofReal ((N : ℝ)*ε) := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
        ENNReal.ofReal_mul (Nat.cast_nonneg N),ENNReal.ofReal_natCast,N]
    _ ≤ ENNReal.ofReal η := by
      apply ENNReal.ofReal_le_ofReal
      dsimp only [ε]
      rw [← mul_div_assoc]
      apply (div_le_iff₀ (show (0 : ℝ) < N+1 by positivity)).mpr
      linarith

end TransposeFollowup.AffineMotion
