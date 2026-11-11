import AdaptiveTransfer.ProtectedCores
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic

/-! Actual normalized charts for a fixed signed cluster. The signature has
three choices per physical head: excluded, positive, or negative. Protected
cores and fringes are finite physical address sets obtained by reflection.
-/

namespace AdaptiveTransfer

open Finset LeanMachine.ProtectedIntervals
open scoped BigOperators
attribute [local instance] Classical.propDecidable

abbrev ClusterSignature (k : ℕ) := Fin k → Option Bool
abbrev ClusterHeads {k : ℕ} (σ : ClusterSignature k) := {h : Fin k // σ h ≠ none}

/-- `some false` has positive orientation, `some true` negative orientation.
The value at an excluded head is immaterial and is chosen to be positive. -/
def clusterOrient (s : Option Bool) (z : ℤ) : ℤ := if s = some true then -z else z

@[simp] theorem clusterOrient_involutive (s : Option Bool) :
    Function.Involutive (clusterOrient s) := by
  intro z
  simp only [clusterOrient]
  split_ifs <;> simp

theorem clusterOrient_injective (s : Option Bool) : Function.Injective (clusterOrient s) :=
  (clusterOrient_involutive s).injective

@[simp] theorem clusterOrient_twice (s : Option Bool) (z : ℤ) :
    clusterOrient s (clusterOrient s z) = z := clusterOrient_involutive s z

@[simp] theorem clusterOrient_abs (s : Option Bool) (z : ℤ) : |clusterOrient s z| = |z| := by
  simp only [clusterOrient]
  split_ifs <;> simp

noncomputable def clusterCarrier {k : ℕ} (σ : ClusterSignature k)
    (xs : Fin k → ℕ → ℤ) (t : ℕ) : ℤ :=
  ∑ h : ClusterHeads σ, clusterOrient (σ h.val) (xs h.val t)

@[simp] theorem clusterSignature_card (k : ℕ) : Fintype.card (ClusterSignature k) = 3 ^ k := by
  simp [ClusterSignature]

theorem clusterHeads_card_le {k : ℕ} (σ : ClusterSignature k) :
    Fintype.card (ClusterHeads σ) ≤ k := by
  simpa only [Fintype.card_fin] using
    Fintype.card_le_of_injective (fun h : ClusterHeads σ => h.val) Subtype.val_injective

structure ClusterChart {k : ℕ} (xs : Fin k → ℕ → ℤ) (T : ℕ) (J : ℝ) where
  signature : ClusterSignature k
  nonempty : ∃ h : Fin k, signature h ≠ none
  map : ClusterHeads signature → ℝ → ℝ
  monotone : ∀ h, Monotone (map h)
  lipschitz : ∀ h, LipschitzWith 1 (map h)
  normalized : ∀ z, (∑ h, map h z) = z
  error : ∀ t < T, ∀ h : ClusterHeads signature,
    |(clusterOrient (signature h.val) (xs h.val t) : ℝ) - map h (clusterCarrier signature xs t)| ≤ J

namespace ClusterChart

variable {k T : ℕ} {J : ℝ} {xs : Fin k → ℕ → ℤ} (g : ClusterChart xs T J)

abbrev Heads := ClusterHeads g.signature

def included : Finset (Fin k) := univ.filter fun h => g.signature h ≠ none

noncomputable def carrier (t : ℕ) : ℤ := clusterCarrier g.signature xs t

include g in
theorem k_pos : 0 < k := by obtain ⟨h, _⟩ := g.nonempty; have := h.isLt; omega

theorem carrier_bound {t U : ℕ} (hbound : ∀ h : Fin k, |xs h t| ≤ (U : ℤ)) :
    |g.carrier t| ≤ (k * U : ℕ) := by
  unfold carrier clusterCarrier
  calc
    _ ≤ ∑ h : g.Heads, |clusterOrient (g.signature h.val) (xs h.val t)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _h : g.Heads, (U : ℤ) := sum_le_sum (fun h _ => by simpa using hbound h.val)
    _ = (Fintype.card g.Heads : ℤ) * U := by simp
    _ ≤ (k * U : ℕ) := by
      exact_mod_cast Nat.mul_le_mul_right U (clusterHeads_card_le g.signature)

noncomputable def orientedCore (ell : ℤ) (W j : ℕ) (h : g.Heads) : Finset ℤ :=
  LeanMachine.ProtectedIntervals.core (g.map h ell) (g.map h (ell + W)) j

noncomputable def orientedFringe (ell : ℤ) (W j : ℕ) (h : g.Heads) : Finset ℤ :=
  LeanMachine.ProtectedIntervals.fringe (g.map h ell) (g.map h (ell + W)) j

noncomputable def core (ell : ℤ) (W j : ℕ) (h : Fin k) : Finset ℤ :=
  if hh : g.signature h ≠ none then
    (g.orientedCore ell W j ⟨h, hh⟩).image (clusterOrient (g.signature h)) else ∅

noncomputable def fringe (ell : ℤ) (W j : ℕ) (h : Fin k) : Finset ℤ :=
  if hh : g.signature h ≠ none then
    (g.orientedFringe ell W j ⟨h, hh⟩).image (clusterOrient (g.signature h)) else ∅

@[simp] theorem core_of_excluded (ell : ℤ) (W j : ℕ) {h : Fin k} (hh : g.signature h = none) :
    g.core ell W j h = ∅ := by simp [core, hh]

@[simp] theorem fringe_of_excluded (ell : ℤ) (W j : ℕ) {h : Fin k} (hh : g.signature h = none) :
    g.fringe ell W j h = ∅ := by simp [fringe, hh]

theorem mem_core {ell z : ℤ} {W j : ℕ} {h : Fin k} (hh : g.signature h ≠ none) :
    z ∈ g.core ell W j h ↔ clusterOrient (g.signature h) z ∈ g.orientedCore ell W j ⟨h, hh⟩ := by
  simp only [core, dite_eq_left hh, mem_image]
  constructor
  · rintro ⟨u, hu, rfl⟩
    simpa only [clusterOrient_twice] using hu
  · intro hz
    exact ⟨clusterOrient (g.signature h) z, hz, clusterOrient_involutive _ _⟩

theorem mem_fringe {ell z : ℤ} {W j : ℕ} {h : Fin k} (hh : g.signature h ≠ none) :
    z ∈ g.fringe ell W j h ↔ clusterOrient (g.signature h) z ∈ g.orientedFringe ell W j ⟨h, hh⟩ := by
  simp only [fringe, dite_eq_left hh, mem_image]
  constructor
  · rintro ⟨u, hu, rfl⟩
    simpa only [clusterOrient_twice] using hu
  · intro hz
    exact ⟨clusterOrient (g.signature h) z, hz, clusterOrient_involutive _ _⟩

theorem selected_read {ell : ℤ} {W j t : ℕ} (ht : t < T) (hj : J ≤ j)
    (hslab : ell ≤ g.carrier t ∧ g.carrier t < ell + W) {h : Fin k}
    (hh : g.signature h ≠ none) : xs h t ∈ g.core ell W j h ∪ g.fringe ell W j h := by
  rw [mem_union, g.mem_core hh, g.mem_fringe hh]
  exact mem_union.mp (selected_in_core_or_fringe (g.monotone ⟨h, hh⟩)
    (by exact_mod_cast hslab) ((g.error t ht ⟨h, hh⟩).trans hj))

theorem outside_avoids {ell : ℤ} {W j t : ℕ} (ht : t < T) (hj : J ≤ j)
    (hslab : g.carrier t < ell ∨ ell + W ≤ g.carrier t) (h : Fin k) :
    xs h t ∉ g.core ell W j h := by
  by_cases hh : g.signature h ≠ none
  · rw [g.mem_core hh]
    exact outside_avoids_core (g.monotone ⟨h, hh⟩) (by exact_mod_cast hslab)
      ((g.error t ht ⟨h, hh⟩).trans hj)
  · simp only [core, dite_eq_right hh]
    simp

theorem core_disjoint_fringe (ell : ℤ) (W j : ℕ) (h : Fin k) :
    Disjoint (g.core ell W j h) (g.fringe ell W j h) := by
  by_cases hh : g.signature h ≠ none
  · rw [Finset.disjoint_left]
    intro z hc hf
    exact (Finset.disjoint_left.mp (LeanMachine.ProtectedIntervals.core_disjoint_fringe _ _ j))
      ((g.mem_core hh).mp hc) ((g.mem_fringe hh).mp hf)
  · simp only [core, fringe, dite_eq_right hh, disjoint_empty_left]

theorem core_card (ell : ℤ) (W j : ℕ) (h : g.Heads) :
    (g.core ell W j h.val).card = (g.orientedCore ell W j h).card := by
  simp only [core, dite_eq_left h.property]
  exact card_image_of_injective _ (clusterOrient_injective _)

theorem fringe_card (ell : ℤ) (W j : ℕ) (h : g.Heads) :
    (g.fringe ell W j h.val).card = (g.orientedFringe ell W j h).card := by
  simp only [fringe, dite_eq_left h.property]
  exact card_image_of_injective _ (clusterOrient_injective _)

theorem core_fringe_counts (ell : ℤ) (W j : ℕ) :
    (∑ h : g.Heads, ((g.core ell W j h.val).card : ℝ)) ≤ W + k ∧
      (∑ h : g.Heads, (g.fringe ell W j h.val).card) ≤ k * (4 * j + 2) := by
  have hc := normalized_chart_core_fringe_counts g.map g.monotone g.normalized
    ell W (Nat.cast_nonneg W) (fun _ => j)
  constructor
  · have hh : (∑ h : g.Heads, ((g.core ell W j h.val).card : ℝ)) ≤ W + Fintype.card g.Heads := by
      simpa only [g.core_card, orientedCore] using hc.1
    exact hh.trans (by exact_mod_cast Nat.add_le_add_left (clusterHeads_card_le g.signature) W)
  · have hh := hc.2
    simp only [sum_const, card_univ, smul_eq_mul] at hh
    have hh' : (∑ h : g.Heads, (g.fringe ell W j h.val).card) ≤
        4 * (Fintype.card g.Heads * j) + 2 * Fintype.card g.Heads := by
      simpa only [g.fringe_card, orientedFringe] using hh
    exact hh'.trans (by nlinarith [clusterHeads_card_le g.signature])

theorem fringe_card_le (ell : ℤ) (W j : ℕ) (h : Fin k) :
    (g.fringe ell W j h).card ≤ 4 * j + 2 := by
  by_cases hh : g.signature h ≠ none
  · rw [g.fringe_card ell W j ⟨h, hh⟩]
    exact card_fringe_le _ _ j
  · simp only [fringe, dite_eq_right hh, card_empty, zero_le]

theorem sum_core_card_le_real (ell : ℤ) (W j : ℕ) :
    (∑ h : Fin k, ((g.core ell W j h).card : ℝ)) ≤ W + k := by
  have he : (∑ h : Fin k, ((g.core ell W j h).card : ℝ)) =
      ∑ h ∈ g.included, ((g.core ell W j h).card : ℝ) := by
    symm
    apply sum_subset (subset_univ _)
    intro h _ hh
    have hex : g.signature h = none := by
      simpa only [included, mem_filter, mem_univ, true_and, not_not] using hh
    simp only [g.core_of_excluded ell W j hex, card_empty, Nat.cast_zero]
  rw [he, Finset.sum_subtype (p := fun h => g.signature h ≠ none)
    g.included (by intro h; simp [included])]
  exact (g.core_fringe_counts ell W j).1

theorem sum_core_card_le (ell : ℤ) (W j : ℕ) :
    (∑ h : Fin k, (g.core ell W j h).card) ≤ W + k := by
  exact_mod_cast g.sum_core_card_le_real ell W j

theorem sum_fringe_card_le (ell : ℤ) (W j : ℕ) :
    (∑ h : Fin k, (g.fringe ell W j h).card) ≤ k * (4 * j + 2) := by
  calc
    _ ≤ ∑ _h : Fin k, (4 * j + 2) := sum_le_sum (fun h _ => g.fringe_card_le ell W j h)
    _ = _ := by simp

end ClusterChart
end AdaptiveTransfer
