import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic

/-! Finite almost-invariant sets in a commutative group. Exponent-box images
have polynomial growth even when generators satisfy relations. Mathlib's
polynomial-versus-exponential limit supplies one small-growth step; no
amenability or freeness hypothesis is assumed. -/
namespace TransposeFollowup.FiniteBoundary
open Classical Finset Filter
open scoped BigOperators Topology
set_option autoImplicit false

theorem exists_small_growth_step (a : ℕ → ℝ) (m : ℕ) (ha : 1 ≤ a 0)
    (hbound : ∀ n, a n ≤ ((n : ℝ)+1)^m) {r : ℝ} (hr : 1 < r) :
    ∃ n, a (n+1) ≤ r*a n := by
  by_contra h
  push Not at h
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have hg (n : ℕ) : r^n ≤ a n := by
    induction n with
    | zero => simpa using ha
    | succ n ih =>
      calc
        r^(n+1)=r*r^n := pow_succ' r n
        _ ≤ r*a n := mul_le_mul_of_nonneg_left ih hr0.le
        _ ≤ a (n+1) := (h n).le
  have hl := (isLittleO_pow_const_const_pow_of_one_lt (R:=ℝ) m hr).bound
    (show 0 < 1/(2*r) by positivity)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hl
  have hn := hN (N+1) (Nat.le_succ N)
  rw [Real.norm_of_nonneg (pow_nonneg (Nat.cast_nonneg (N+1)) m),
    Real.norm_of_nonneg (pow_nonneg hr0.le (N+1))] at hn
  simp only [Nat.cast_add, Nat.cast_one, pow_succ] at hn
  have he : 1/(2*r)*(r^N*r)=r^N/2 := by field_simp
  rw [he] at hn
  have hp := pow_pos hr0 N
  have hb := hbound N
  have hh := hg N
  linarith

variable {G ι : Type*} [CommGroup G] [DecidableEq G] [Fintype ι]

noncomputable def exponentBox (g : ι → G) (n : ℕ) : Finset G :=
  (Fintype.piFinset (fun _ : ι => Finset.range (n+1))).image (fun e => ∏ i, g i^(e i))

theorem exponentBox_nonempty (g : ι → G) (n : ℕ) : (exponentBox g n).Nonempty := by
  refine ⟨1, Finset.mem_image.mpr ⟨fun _ => 0, ?_, ?_⟩⟩
  · simp
  · simp

theorem exponentBox_card_le (g : ι → G) (n : ℕ) :
    (exponentBox g n).card ≤ (n+1)^Fintype.card ι := by
  have h := Finset.card_image_le (s:=Fintype.piFinset (fun _ : ι => Finset.range (n+1)))
    (f:=fun e => ∏ i, g i^(e i))
  simpa only [exponentBox, Fintype.card_piFinset, Finset.card_range,
    Finset.prod_const, Finset.card_univ] using h

theorem exponentBox_subset_succ (g : ι → G) (n : ℕ) :
    exponentBox g n ⊆ exponentBox g (n+1) := by
  rintro x hx
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
  refine Finset.mem_image.mpr ⟨e, ?_, rfl⟩
  apply Fintype.mem_piFinset.mpr
  intro i
  have hi := Fintype.mem_piFinset.mp he i
  simp only [Finset.mem_range] at hi ⊢
  omega

theorem exponentBox_mul_subset_succ (g : ι → G) (n : ℕ) (j : ι) :
    (exponentBox g n).image (fun x => x*g j) ⊆ exponentBox g (n+1) := by
  rintro x hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hy
  refine Finset.mem_image.mpr ⟨Function.update e j (e j+1), ?_, ?_⟩
  · apply Fintype.mem_piFinset.mpr
    intro i
    have hi := Fintype.mem_piFinset.mp he i
    simp only [Finset.mem_range] at hi ⊢
    by_cases hij : i=j
    · subst i
      simp only [Function.update_self]
      omega
    · rw [Function.update_of_ne hij]
      omega
  · have heq (i : ι) : g i^(Function.update e j (e j+1) i)=
        g i^(e i)*(if i=j then g j else 1) := by
      by_cases hij : i=j
      · subst i
        simp only [Function.update_self, ite_true, pow_succ]
      · simp only [Function.update_of_ne hij, hij, ite_false, mul_one]
    simp_rw [heq]
    rw [Finset.prod_mul_distrib]
    simp

theorem exists_small_mul_boundary (g : ι → G) {ε : ℝ} (hε : 0 < ε) :
    ∃ F : Finset G, F.Nonempty ∧ ∀ j,
      (((F.image (fun x => x*g j)) \ F).card : ℝ) ≤ ε*F.card := by
  obtain ⟨n, hn⟩ := exists_small_growth_step (fun n => (exponentBox g n).card)
    (Fintype.card ι)
    (by exact_mod_cast Finset.card_pos.mpr (exponentBox_nonempty g 0))
    (fun n => by exact_mod_cast exponentBox_card_le g n)
    (show 1 < 1+ε by linarith)
  refine ⟨exponentBox g n, exponentBox_nonempty g n, fun j => ?_⟩
  have hs := exponentBox_subset_succ g n
  have hi := exponentBox_mul_subset_succ g n j
  have hc : (((exponentBox g n).image (fun x => x*g j)) \ exponentBox g n).card ≤
      (exponentBox g (n+1) \ exponentBox g n).card := by
    apply Finset.card_le_card
    intro x hx
    exact Finset.mem_sdiff.mpr ⟨hi (Finset.mem_sdiff.mp hx).1, (Finset.mem_sdiff.mp hx).2⟩
  have he := Finset.card_sdiff_add_card_eq_card hs
  have hc' : ((((exponentBox g n).image (fun x => x*g j)) \ exponentBox g n).card : ℝ) ≤
      (exponentBox g (n+1) \ exponentBox g n).card := by exact_mod_cast hc
  have he' : ((exponentBox g (n+1) \ exponentBox g n).card : ℝ)+
      (exponentBox g n).card=(exponentBox g (n+1)).card := by exact_mod_cast he
  nlinarith

theorem exists_small_add_boundary {A : Type*} [AddCommGroup A] [DecidableEq A] (g : ι → A)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ F : Finset A, F.Nonempty ∧ ∀ j,
      (((F.image (fun x => x+g j)) \ F).card : ℝ) ≤ ε*F.card := by
  exact exists_small_mul_boundary (fun j => Multiplicative.ofAdd (g j)) hε

end TransposeFollowup.FiniteBoundary
