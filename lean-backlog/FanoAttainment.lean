import FanoFull

/-!
# Attaining the residual Fano Shannon bound

The sum of the rank-two functions on the 28 mutual triangles, divided by
three, is an actual valid polymatroid with unit singleton values and total
value 56/3. Together with `FanoCertificate.residual_le` this proves the exact
residual Shannon value. This file does not formalize realization by the
three-lane code; the explicit polymatroid is sufficient for Shannon attainment.
Adding independent unit-rank incident coordinates gives the full value 119/3.
-/

namespace LeanBacklog.FanoAttainment

open Finset MotionDepthCodes FanoCertificate
open scoped BigOperators
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- A capped intersection cardinality, the rank of a restricted uniform matroid. -/
def cappedCard {V : Type*} [DecidableEq V] (k : ℕ) (T S : Finset V) : ℝ :=
  (min k (S ∩ T).card : ℕ)

theorem cappedCard_isPolymatroid {V : Type*} [DecidableEq V]
    (k : ℕ) (T : Finset V) : IsPolymatroid (cappedCard k T) where
  empty := by simp [cappedCard]
  mono := by
    intro A B hAB
    have hc : (A ∩ T).card ≤ (B ∩ T).card :=
      card_le_card (inter_subset_inter hAB (Subset.rfl : T ⊆ T))
    have h := min_le_min_left k hc
    simp only [cappedCard]
    exact_mod_cast h
  submod := by
    intro A B
    have hU : (A ∪ B) ∩ T = (A ∩ T) ∪ (B ∩ T) := by
      ext x; simp only [mem_inter, mem_union]; tauto
    have hI : (A ∩ B) ∩ T = (A ∩ T) ∩ (B ∩ T) := by
      ext x; simp only [mem_inter]; tauto
    have hc := card_union_add_card_inter (A ∩ T) (B ∩ T)
    have ha : ((A ∩ T) ∩ (B ∩ T)).card ≤ (A ∩ T).card :=
      card_le_card inter_subset_left
    have hb : ((A ∩ T) ∩ (B ∩ T)).card ≤ (B ∩ T).card :=
      card_le_card inter_subset_right
    have hn : min k ((A ∩ T) ∪ (B ∩ T)).card +
        min k ((A ∩ T) ∩ (B ∩ T)).card ≤
        min k (A ∩ T).card + min k (B ∩ T).card := by omega
    simp only [cappedCard, hU, hI]
    exact_mod_cast hn

/-- The triangles used in the saved exact certificate, in its residual cell order. -/
def triangle : Fin 28 → Finset Cell := ![
  {0, 4, 12}, {2, 4, 18}, {0, 6, 22}, {2, 6, 26},
  {1, 9, 12}, {3, 9, 18}, {3, 11, 22}, {1, 11, 26},
  {0, 14, 20}, {1, 14, 25}, {3, 19, 20}, {2, 19, 25},
  {5, 8, 12}, {7, 10, 18}, {7, 8, 22}, {5, 10, 26},
  {4, 13, 16}, {5, 13, 24}, {7, 16, 23}, {6, 23, 24},
  {9, 15, 17}, {8, 15, 21}, {10, 17, 27}, {11, 21, 27},
  {15, 16, 20}, {13, 17, 25}, {14, 21, 24}, {19, 23, 27}]

theorem triangle_card : ∀ t, (triangle t).card = 3 := by decide

theorem triangle_mutual : ∀ t, ∀ v ∈ triangle t, ∀ u ∈ triangle t,
    u ≠ v → u ∈ nbhd v := by decide

private theorem triangle_recovery : ∀ t v,
    min 2 ((insert v (nbhd v)) ∩ triangle t).card =
      min 2 ((nbhd v) ∩ triangle t).card := by decide

private theorem singleton_count : ∀ v : Cell,
    ∑ t : Fin 28, min 2 (({v} : Finset Cell) ∩ triangle t).card = 3 := by decide

private theorem total_count :
    ∑ t : Fin 28, min 2 ((univ : Finset Cell) ∩ triangle t).card = 56 := by decide

/-- Average of the 28 rank-two triangle functions. -/
noncomputable def triangleRank (S : Finset Cell) : ℝ :=
  (∑ t : Fin 28, cappedCard 2 (triangle t) S) / 3

theorem triangleRank_isPolymatroid : IsPolymatroid triangleRank where
  empty := by simp [triangleRank, cappedCard]
  mono := by
    intro A B hAB
    exact div_le_div_of_nonneg_right
      (sum_le_sum (fun t _ => (cappedCard_isPolymatroid 2 (triangle t)).mono hAB))
      (by norm_num)
  submod := by
    intro A B
    have h := sum_le_sum (fun t (_ : t ∈ (univ : Finset (Fin 28))) =>
      (cappedCard_isPolymatroid 2 (triangle t)).submod A B)
    simp only [sum_add_distrib] at h
    unfold triangleRank
    linarith

theorem triangleRank_isValid : IsValid triangleRank nbhd := by
  intro v
  unfold triangleRank
  congr 1
  apply sum_congr rfl
  intro t _
  simp only [cappedCard, triangle_recovery t v]

theorem triangleRank_singleton (v : Cell) : triangleRank {v} = 1 := by
  have h : (∑ t : Fin 28, cappedCard 2 (triangle t) {v}) = (3 : ℝ) := by
    simp only [cappedCard, ← Nat.cast_sum]
    exact_mod_cast singleton_count v
  rw [triangleRank, h]
  norm_num

theorem triangleRank_total : triangleRank univ = 56 / 3 := by
  have h : (∑ t : Fin 28, cappedCard 2 (triangle t) univ) = (56 : ℝ) := by
    simp only [cappedCard, ← Nat.cast_sum]
    exact_mod_cast total_count
  rw [triangleRank, h]

/-- An actual feasible polymatroid attains the residual upper bound. -/
theorem residual_attainment : ∃ h : Finset Cell → ℝ,
    IsPolymatroid h ∧ IsValid h nbhd ∧
      (∀ v, h {v} ≤ 1) ∧ h univ = 56 / 3 := by
  exact ⟨triangleRank, triangleRank_isPolymatroid, triangleRank_isValid,
    fun v => le_of_eq (triangleRank_singleton v), triangleRank_total⟩

/-- Exactness expressed without introducing a separate optimization definition. -/
theorem residual_shannon_exact :
    (∀ h : Finset Cell → ℝ, IsPolymatroid h → IsValid h nbhd →
      (∀ v, h {v} ≤ 1) → h univ ≤ 56 / 3) ∧
    (∃ h : Finset Cell → ℝ, IsPolymatroid h ∧ IsValid h nbhd ∧
      (∀ v, h {v} ≤ 1) ∧ h univ = 56 / 3) :=
  ⟨FanoCertificate.residual_le, residual_attainment⟩

open FanoFull

/-- The residual witness with an independent unit of rank at every incident cell. -/
noncomputable def fullTriangleRank (S : Finset Grid) : ℝ :=
  cappedCard 49 loops S + MotionDepthCodes.pushRank embed triangleRank S

theorem fullTriangleRank_isPolymatroid : IsPolymatroid fullTriangleRank where
  empty := by
    simp only [fullTriangleRank, (cappedCard_isPolymatroid 49 loops).empty,
      (triangleRank_isPolymatroid.pushRank embed).empty, add_zero]
  mono := by
    intro A B hAB
    exact add_le_add ((cappedCard_isPolymatroid 49 loops).mono hAB)
      ((triangleRank_isPolymatroid.pushRank embed).mono hAB)
  submod := by
    intro A B
    have h1 := (cappedCard_isPolymatroid 49 loops).submod A B
    have h2 := (triangleRank_isPolymatroid.pushRank embed).submod A B
    unfold fullTriangleRank
    linarith

private theorem loopValid : IsValid (cappedCard 49 loops) helpers := by
  intro v
  by_cases hv : v ∈ loops
  · have hself : v ∈ helpers v := by
      simpa only [loops, helpers, mem_filter, mem_univ, true_and] using hv
    rw [insert_eq_of_mem hself]
  · have hi : insert v (helpers v) ∩ loops = helpers v ∩ loops := by
      ext x
      simp only [mem_inter, mem_insert]
      aesop
    simp only [cappedCard, hi]

private theorem embed_helper : ∀ u, ∀ v ∈ nbhd u,
    embed v ∈ helpers (embed u) := by decide

theorem fullTriangleRank_isValid : IsValid fullTriangleRank helpers := by
  have hp := IsValid.pushRank triangleRank_isPolymatroid triangleRank_isValid
    embed embed_helper
  intro v
  simp only [fullTriangleRank, loopValid v, hp v]

private theorem singleton_partition : ∀ p : Grid,
    (({p} : Finset Grid) ∩ loops).card +
      (univ.filter (fun v : Cell => embed v ∈ ({p} : Finset Grid))).card = 1 := by decide

theorem fullTriangleRank_singleton_le (p : Grid) : fullTriangleRank {p} ≤ 1 := by
  have h1 : cappedCard 49 loops {p} ≤ (({p} ∩ loops).card : ℝ) := by
    simp only [cappedCard]
    exact_mod_cast Nat.min_le_right 49 (({p} : Finset Grid) ∩ loops).card
  have h2 := triangleRank_isPolymatroid.le_sum_singleton
    (univ.filter (fun v : Cell => embed v ∈ ({p} : Finset Grid)))
  simp only [triangleRank_singleton, sum_const, nsmul_eq_mul, mul_one] at h2
  have hc : ((({p} : Finset Grid) ∩ loops).card : ℝ) +
      ((univ.filter (fun v : Cell => embed v ∈ ({p} : Finset Grid))).card : ℝ) = 1 := by
    exact_mod_cast singleton_partition p
  unfold fullTriangleRank MotionDepthCodes.pushRank
  linarith

theorem fullTriangleRank_total : fullTriangleRank univ = 119 / 3 := by
  rw [fullTriangleRank, pushRank_univ, triangleRank_total]
  simp only [cappedCard, univ_inter, loops_card]
  norm_num

theorem full_attainment : ∃ h : Finset Grid → ℝ,
    IsPolymatroid h ∧ IsValid h helpers ∧
      (∀ p, h {p} ≤ 1) ∧ h univ = 119 / 3 :=
  ⟨fullTriangleRank, fullTriangleRank_isPolymatroid, fullTriangleRank_isValid,
    fullTriangleRank_singleton_le, fullTriangleRank_total⟩

/-- Exact full-host Shannon value; no entropic realization is asserted here. -/
theorem full_shannon_exact :
    (∀ h : Finset Grid → ℝ, IsPolymatroid h → IsValid h helpers →
      (∀ p, h {p} ≤ 1) → h univ ≤ 119 / 3) ∧
    (∃ h : Finset Grid → ℝ, IsPolymatroid h ∧ IsValid h helpers ∧
      (∀ p, h {p} ≤ 1) ∧ h univ = 119 / 3) :=
  ⟨fun _ hh hv hc => FanoFull.full_upper hh hv hc, full_attainment⟩

end LeanBacklog.FanoAttainment

#print axioms LeanBacklog.FanoAttainment.residual_attainment
#print axioms LeanBacklog.FanoAttainment.residual_shannon_exact
#print axioms LeanBacklog.FanoAttainment.full_attainment
#print axioms LeanBacklog.FanoAttainment.full_shannon_exact
