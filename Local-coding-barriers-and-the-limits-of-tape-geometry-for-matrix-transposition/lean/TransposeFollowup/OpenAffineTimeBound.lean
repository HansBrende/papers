import TransposeFollowup.CountableAffineTimeBound
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.Bases
import Mathlib.Logic.Encodable.Lattice

/-! From actual local affine neighborhoods to countably many branches.
Countability is derived by mathlib's open-cover theorem; it is not an
additional hypothesis. The component formulation is the original210 scope. -/
namespace TransposeFollowup.AffineMotion
open Classical Set Finset MeasureTheory Transpose.Tape
open scoped ENNReal BigOperators
set_option autoImplicit false

theorem exists_countable_local_affine_cover (P : ℝ → ℝ) (R : Set ℝ)
    (hlocal : ∀ x ∈ R, ∃ U : Set ℝ, IsOpen U ∧ x ∈ U ∧ U ⊆ R ∧
      ∃ a b : ℝ, ∀ y ∈ U, P y=a*y+b) :
    ∃ (J : ℕ → Set ℝ) (a b : ℕ → ℝ), (⋃ n, J n)=R ∧
      (∀ n, IsOpen (J n)) ∧ (∀ n, J n ⊆ R) ∧
      ∀ n y, y ∈ J n → P y=a n*y+b n := by
  let A : Set (Set ℝ) := {U | IsOpen U ∧ U ⊆ R ∧ ∃ a b : ℝ, ∀ y ∈ U, P y=a*y+b}
  have hwhole : (⋃ U : A, U.val)=R := by
    apply Set.Subset.antisymm
    · exact Set.iUnion_subset (fun U => U.property.2.1)
    · intro x hx
      obtain ⟨U,hUo,hxU,hUR,a,b,hP⟩ := hlocal x hx
      exact Set.mem_iUnion.mpr ⟨⟨U,hUo,hUR,a,b,hP⟩,hxU⟩
  obtain ⟨T,hT,hunion⟩ := TopologicalSpace.isOpen_iUnion_countable (fun U : A => U.val)
    (fun U => U.property.1)
  let : Countable T := hT.to_subtype
  let : Encodable T := Encodable.ofCountable T
  let J (n : ℕ) : Set ℝ := ⋃ U ∈ Encodable.decode₂ T n, U.val.val
  have hempty : (∅ : Set ℝ) ∈ A :=
    ⟨isOpen_empty,Set.empty_subset R,0,0,fun _ h => False.elim h⟩
  have hJ (n : ℕ) : J n ∈ A := Encodable.iUnion_decode₂_cases
    (f:=fun U : T => U.val.val) (C:=fun U => U ∈ A) (n:=n) hempty
    (fun U : T => U.val.property)
  choose a b hab using fun n => (hJ n).2.2
  refine ⟨J,a,b,?_,fun n => (hJ n).1,fun n => (hJ n).2.1,hab⟩
  calc
    (⋃ n, J n) = ⋃ U : T, U.val.val := Encodable.iUnion_decode₂ _
    _ = ⋃ U ∈ T, U.val := by ext x; simp
    _ = R := hunion.trans hwhole

theorem star_half_le_locally_affine_omission {k : ℕ} {c₀ : ℝ}
    (hc : 0 ≤ c₀) (P : Fin k → ℝ → ℝ)
    (hP : ∀ t, LipschitzOnWith 1 (P t) (Icc 0 c₀))
    (R : Fin k → Set ℝ) (hRI : ∀ t, R t ⊆ Icc 0 c₀)
    (hlocal : ∀ t x, x ∈ R t → ∃ U : Set ℝ, IsOpen U ∧ x ∈ U ∧ U ⊆ R t ∧
      ∃ a b : ℝ, ∀ y ∈ U, P t y=a*y+b)
    (hstar : SatisfiesStar P c₀) :
    (1/2 : ℝ≥0∞) ≤ ∑ t, volume (Icc 0 c₀ \ R t) := by
  choose J a b hunion hJo hJR hPa using fun t =>
    exists_countable_local_affine_cover (P t) (R t) (hlocal t)
  have h := star_half_le_countable_affine_omission hc P hP a b J hJo
    (fun t n => (hJR t n).trans (hRI t)) hPa hstar
  simpa only [hunion] using h

theorem star_half_le_affine_component_omission {k : ℕ} {c₀ : ℝ}
    (hc : 0 ≤ c₀) (P : Fin k → ℝ → ℝ)
    (hP : ∀ t, LipschitzOnWith 1 (P t) (Icc 0 c₀))
    (R : Fin k → Set ℝ) (hRo : ∀ t, IsOpen (R t)) (hRI : ∀ t, R t ⊆ Icc 0 c₀)
    (hPa : ∀ t x, x ∈ R t → ∃ a b : ℝ,
      ∀ y ∈ connectedComponentIn (R t) x, P t y=a*y+b)
    (hstar : SatisfiesStar P c₀) :
    (1/2 : ℝ≥0∞) ≤ ∑ t, volume (Icc 0 c₀ \ R t) := by
  apply star_half_le_locally_affine_omission hc P hP R hRI _ hstar
  intro t x hx
  exact ⟨connectedComponentIn (R t) x,(hRo t).connectedComponentIn,
    mem_connectedComponentIn hx,connectedComponentIn_subset (R t) x,hPa t x hx⟩

theorem star_common_affine_omission {k : ℕ} (hk : 0 < k) {c₀ : ℝ}
    (hc : 0 ≤ c₀) (P : Fin k → ℝ → ℝ)
    (hP : ∀ t, LipschitzOnWith 1 (P t) (Icc 0 c₀))
    (R : Set ℝ) (hRo : IsOpen R) (hRI : R ⊆ Icc 0 c₀)
    (hPa : ∀ t x, x ∈ R → ∃ a b : ℝ,
      ∀ y ∈ connectedComponentIn R x, P t y=a*y+b)
    (hstar : SatisfiesStar P c₀) :
    (1/(2*k) : ℝ≥0∞) ≤ volume (Icc 0 c₀ \ R) := by
  have h := star_half_le_affine_component_omission hc P hP (fun _ => R)
    (fun _ => hRo) (fun _ => hRI) hPa hstar
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at h
  have h2 := (ENNReal.div_le_iff' (show (2 : ℝ≥0∞) ≠ 0 by norm_num)
    (show (2 : ℝ≥0∞) ≠ ∞ by norm_num)).mp h
  apply (ENNReal.div_le_iff' (by exact mul_ne_zero (by norm_num) (by exact_mod_cast hk.ne'))
    (by exact ENNReal.mul_ne_top (by norm_num) (by simp))).mpr
  simpa only [mul_assoc] using h2

end TransposeFollowup.AffineMotion
