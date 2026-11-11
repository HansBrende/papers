import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-! # One retained subset with lower density in every attained context

Maximize mass minus a penalty for each attained context fibre. The retained
set works simultaneously for all contexts; the number of observed variables
sharing a context does not enter the loss.
-/

namespace LeanMachine.ContextPruning

open Finset
attribute [local instance] Classical.propDecidable

variable {Ω I Z : Type*} [Fintype Ω] [Fintype I]

noncomputable def mass (w : Ω → ℝ) (S : Finset Ω) : ℝ := ∑ x ∈ S, w x

noncomputable def fibre (z : Ω → Z) (a : Z) : Finset Ω :=
  Finset.univ.filter (fun x => z x = a)

noncomputable def cover (z : Ω → Z) (S : Finset Ω) : Finset Ω :=
  Finset.univ.filter (fun x => ∃ y ∈ S, z y = z x)

omit [Fintype Ω] in
theorem mass_nonneg {w : Ω → ℝ} (hw : ∀ x, 0 ≤ w x) (S : Finset Ω) :
    0 ≤ mass w S := sum_nonneg (fun x _ => hw x)

omit [Fintype Ω] in
theorem mass_mono {w : Ω → ℝ} (hw : ∀ x, 0 ≤ w x) {S T : Finset Ω}
    (h : S ⊆ T) : mass w S ≤ mass w T :=
  sum_le_sum_of_subset_of_nonneg h (fun x _ _ => hw x)

theorem cover_mono (z : Ω → Z) {S T : Finset Ω} (h : S ⊆ T) :
    cover z S ⊆ cover z T := by
  classical
  intro x hx
  obtain ⟨_, y, hy, he⟩ := mem_filter.mp hx
  exact mem_filter.mpr ⟨mem_univ _, y, h hy, he⟩

theorem cover_remove_fibre (z : Ω → Z) (S : Finset Ω) (a : Z) :
    cover z (S \ fibre z a) = cover z S \ fibre z a := by
  classical
  ext x
  simp only [cover, fibre, mem_filter, mem_univ, true_and, mem_sdiff]
  constructor
  · rintro ⟨y, ⟨hy, hya⟩, he⟩
    exact ⟨⟨y, hy, he⟩, by simpa [← he] using hya⟩
  · rintro ⟨⟨y, hy, he⟩, hxa⟩
    exact ⟨y, ⟨hy, by simpa [he] using hxa⟩, he⟩

theorem fibre_subset_cover (z : Ω → Z) (S : Finset Ω) (a : Z)
    (h : (S ∩ fibre z a).Nonempty) : fibre z a ⊆ cover z S := by
  classical
  obtain ⟨y, hy⟩ := h
  obtain ⟨hyS, hya⟩ := mem_inter.mp hy
  intro x hx
  have he : z y = z x := (mem_filter.mp hya).2.trans (mem_filter.mp hx).2.symm
  exact mem_filter.mpr ⟨mem_univ _, y, hyS, he⟩

theorem exists_dense_context_subset (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x)
    (z : I → Ω → Z) (B : Finset Ω) (θ : ℝ) (hθ : 0 ≤ θ) :
    ∃ D ⊆ B,
      mass w B - θ * ∑ i, mass w (cover (z i) B) ≤ mass w D ∧
      ∀ i a, (D ∩ fibre (z i) a).Nonempty →
        θ * mass w (fibre (z i) a) ≤ mass w (D ∩ fibre (z i) a) := by
  classical
  let cost (S : Finset Ω) := ∑ i, mass w (cover (z i) S)
  let potential (S : Finset Ω) := mass w S - θ * cost S
  obtain ⟨D, hD, hmax⟩ := (B.powerset).exists_max_image potential B.powerset_nonempty
  have hDB : D ⊆ B := mem_powerset.mp hD
  refine ⟨D, hDB, ?_, ?_⟩
  · have hm := hmax B (mem_powerset.mpr (Subset.refl B))
    have hc : 0 ≤ cost D := sum_nonneg (fun i _ => mass_nonneg hw _)
    have hp := mul_nonneg hθ hc
    dsimp [potential] at hm
    dsimp [cost] at hm hp
    linarith
  · intro i a ha
    let F := fibre (z i) a
    let D' := D \ F
    have hD'D : D' ⊆ D := sdiff_subset
    have hD'B : D' ⊆ B := hD'D.trans hDB
    have hm := hmax D' (mem_powerset.mpr hD'B)
    have hmass : mass w D' + mass w (D ∩ F) = mass w D := by
      simpa [mass, D'] using (sum_sdiff (inter_subset_left (s₁ := D) (s₂ := F))
        (f := w))
    have hcosti : mass w (cover (z i) D') + mass w F = mass w (cover (z i) D) := by
      rw [show cover (z i) D' = cover (z i) D \ F from cover_remove_fibre _ _ _]
      exact sum_sdiff (fibre_subset_cover _ _ _ ha)
    have hcost : cost D' + mass w F ≤ cost D := by
      have hterm (j : I) : mass w (cover (z j) D') +
          (if j = i then mass w F else 0) ≤ mass w (cover (z j) D) := by
        by_cases hji : j = i
        · subst j
          simpa using hcosti.le
        · simpa [hji] using mass_mono hw (cover_mono (z j) hD'D)
      have hs := sum_le_sum (fun j (_ : j ∈ (univ : Finset I)) => hterm j)
      simpa [sum_add_distrib, cost] using hs
    have hc := mul_le_mul_of_nonneg_left hcost hθ
    dsimp [potential] at hm
    dsimp [F] at hmass hc
    nlinarith

/-- Probability-normalized form, with a loss depending only on the number of
contexts. The previous theorem retains the sharper attained-support cost. -/
theorem exists_probability_context_subset (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hprob : mass w univ = 1) (z : I → Ω → Z) (B : Finset Ω)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    ∃ D ⊆ B,
      mass w B - (Fintype.card I : ℝ) * θ ≤ mass w D ∧
      ∀ i a, (D ∩ fibre (z i) a).Nonempty →
        θ * mass w (fibre (z i) a) ≤ mass w (D ∩ fibre (z i) a) := by
  obtain ⟨D, hDB, hm, hf⟩ := exists_dense_context_subset w hw z B θ hθ
  refine ⟨D, hDB, ?_, hf⟩
  have hc : ∑ i, mass w (cover (z i) B) ≤ (Fintype.card I : ℝ) := by
    calc
      ∑ i, mass w (cover (z i) B) ≤ ∑ _i : I, (1 : ℝ) :=
        sum_le_sum fun i _ => (mass_mono hw (subset_univ _)).trans_eq hprob
      _ = _ := by simp
  have hh := mul_le_mul_of_nonneg_left hc hθ
  nlinarith

omit [Fintype Ω] in
/-- The global conditioning factor cancels: joint atom bounds divided by the
retained context mass need no extra payment for other observed variables. -/
theorem conditional_mass_bound (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x)
    {D B F E : Finset Ω} (hDB : D ⊆ B) {c θ : ℝ} (hc : 0 ≤ c) (hθ : 0 < θ)
    (hden : 0 < mass w (D ∩ F))
    (hdense : θ * mass w F ≤ mass w (D ∩ F))
    (hjoint : mass w (B ∩ E ∩ F) ≤ c * mass w F) :
    mass w (D ∩ E ∩ F) / mass w (D ∩ F) ≤ c / θ := by
  have hn : mass w (D ∩ E ∩ F) ≤ c * mass w F :=
    (mass_mono hw (inter_subset_inter (inter_subset_inter hDB (Subset.refl E))
      (Subset.refl F))).trans hjoint
  apply (div_le_div_iff₀ hden hθ).mpr
  have h₁ := mul_le_mul_of_nonneg_right hn hθ.le
  have h₂ := mul_le_mul_of_nonneg_left hdense hc
  nlinarith

/-- A single set of at least half the initial mass supports every conditional
atom estimate, however many observed variables use each context. -/
theorem exists_half_mass_context_subset [Nonempty I]
    (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (hprob : mass w univ = 1)
    (z : I → Ω → Z) (B : Finset Ω) (hp : 0 < mass w B) :
    ∃ D ⊆ B, mass w B / 2 ≤ mass w D ∧
      ∀ i a E (c : ℝ), 0 ≤ c → 0 < mass w (D ∩ fibre (z i) a) →
        mass w (B ∩ E ∩ fibre (z i) a) ≤ c * mass w (fibre (z i) a) →
        mass w (D ∩ E ∩ fibre (z i) a) / mass w (D ∩ fibre (z i) a) ≤
          2 * c * Fintype.card I / mass w B := by
  have hn : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  let θ : ℝ := mass w B / (2 * Fintype.card I)
  have hθ : 0 < θ := div_pos hp (mul_pos (by norm_num) hn)
  obtain ⟨D, hDB, hm, hf⟩ := exists_probability_context_subset w hw hprob z B θ hθ.le
  refine ⟨D, hDB, ?_, ?_⟩
  · have he : (Fintype.card I : ℝ) * θ = mass w B / 2 := by
      dsimp [θ]
      field_simp
    linarith
  · intro i a E c hc hden hjoint
    have hne : (D ∩ fibre (z i) a).Nonempty := by
      by_contra he
      rw [not_nonempty_iff_eq_empty.mp he] at hden
      simp [mass] at hden
    have h := conditional_mass_bound w hw hDB hc hθ hden (hf i a hne) hjoint
    have he : c / θ = 2 * c * Fintype.card I / mass w B := by
      dsimp [θ]
      field_simp
    rwa [he] at h

end LeanMachine.ContextPruning
