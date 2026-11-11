import LeanMachine.MonotoneNormalization
import Mathlib.Tactic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Data.Fintype.Order

/-! # A continuous monotone curve through a finite coordinatewise chain

The coordinate sum is surjective onto the real line. No sorting, strict
separation of knot sums or piecewise-linear interpolation API is required.
-/

namespace LeanMachine.MonotoneChain

open Finset

variable {I H : Type*} [Fintype I] [Nonempty I] [Fintype H] [Nonempty H]

noncomputable def total (g : I → H → ℝ) (i : I) : ℝ := ∑ h, g i h

noncomputable def topTotal (g : I → H → ℝ) : ℝ := univ.sup' univ_nonempty (total g)

noncomputable def envelope (g : I → H → ℝ) (h : H) (t : ℝ) : ℝ :=
  univ.sup' univ_nonempty (fun i => g i h - max (total g i - t) 0)

noncomputable def curve (g : I → H → ℝ) (h₀ : H) (h : H) (t : ℝ) : ℝ := by
  classical
  exact envelope g h t + if h = h₀ then max (t - topTotal g) 0 else 0

omit [Nonempty H] in
theorem envelope_continuous (g : I → H → ℝ) (h : H) : Continuous (envelope g h) := by
  apply Continuous.finset_sup'_apply
  intro i _
  exact continuous_const.sub ((continuous_const.sub continuous_id).max continuous_const)

omit [Nonempty H] in
theorem curve_continuous (g : I → H → ℝ) (h₀ h : H) : Continuous (curve g h₀ h) := by
  classical
  unfold curve
  split_ifs
  · exact (envelope_continuous g h).add ((continuous_id.sub continuous_const).max continuous_const)
  · exact (envelope_continuous g h).add continuous_const

omit [Nonempty H] in
theorem envelope_monotone (g : I → H → ℝ) (h : H) : Monotone (envelope g h) := by
  intro t u htu
  apply Finset.sup'_mono_fun
  intro i _
  exact sub_le_sub_left (max_le_max_right 0 (sub_le_sub_left htu _)) _

omit [Nonempty H] in
theorem curve_monotone (g : I → H → ℝ) (h₀ h : H) : Monotone (curve g h₀ h) := by
  classical
  intro t u htu
  unfold curve
  split_ifs
  · exact add_le_add (envelope_monotone g h htu)
      (max_le_max_right 0 (sub_le_sub_right htu _))
  · simpa only [add_zero] using envelope_monotone g h htu

omit [Nonempty H] in
theorem envelope_knot (g : I → H → ℝ)
    (hchain : ∀ i j, (∀ h, g i h ≤ g j h) ∨ (∀ h, g j h ≤ g i h)) (i : I) (h : H) :
    envelope g h (total g i) = g i h := by
  classical
  apply le_antisymm
  · apply Finset.sup'_le
    intro j _
    rcases hchain j i with hle | hge
    · exact (sub_le_self _ (le_max_right _ _)).trans (hle h)
    · have hh : g j h - g i h ≤ ∑ l, (g j l - g i l) :=
        Finset.single_le_sum (fun l _ => sub_nonneg.mpr (hge l)) (mem_univ h)
      rw [Finset.sum_sub_distrib] at hh
      have hm := le_max_left (total g j - total g i) (0 : ℝ)
      dsimp [total] at *
      linarith
  · have hh := Finset.le_sup' (fun j => g j h - max (total g j - total g i) 0) (mem_univ i)
    simpa only [envelope, sub_self, max_self, sub_zero] using hh

omit [Nonempty H] in
theorem curve_knot (g : I → H → ℝ)
    (hchain : ∀ i j, (∀ h, g i h ≤ g j h) ∨ (∀ h, g j h ≤ g i h))
    (h₀ h : H) (i : I) : curve g h₀ h (total g i) = g i h := by
  classical
  have hi : total g i ≤ topTotal g := Finset.le_sup' _ (mem_univ i)
  simp [curve, envelope_knot g hchain, max_eq_right (sub_nonpos.mpr hi)]

omit [Nonempty H] in
private theorem sum_curve (g : I → H → ℝ) (h₀ : H) (t : ℝ) :
    (∑ h, curve g h₀ h t) = (∑ h, envelope g h t) + max (t - topTotal g) 0 := by
  classical
  simp [curve, Finset.sum_add_distrib]

/-- The max envelope has a linear left tail and the chosen coordinate provides
an unbounded right tail. The intermediate value theorem fills all sums. -/
theorem sum_curve_surjective (g : I → H → ℝ) (h₀ : H) :
    Function.Surjective (fun t => ∑ h, curve g h₀ h t) := by
  classical
  intro z
  apply mem_range_of_exists_le_of_exists_ge
  · exact continuous_finsetSum _ (fun h _ => curve_continuous g h₀ h)
  · let lo : ℝ := univ.inf' univ_nonempty (total g)
    let M : ℝ := univ.sup' univ_nonempty
      (fun h => univ.sup' univ_nonempty (fun i => g i h - total g i))
    let t := min lo (z / Fintype.card H - M)
    have hlo : ∀ i, lo ≤ total g i := fun i => Finset.inf'_le _ (mem_univ i)
    have htlo : t ≤ lo := min_le_left _ _
    have hM : ∀ i h, g i h - total g i ≤ M := by
      intro i h
      exact (Finset.le_sup' (fun i => g i h - total g i) (mem_univ i)).trans
        (Finset.le_sup' (fun h => univ.sup' univ_nonempty (fun i => g i h - total g i)) (mem_univ h))
    have henv : ∀ h, envelope g h t ≤ z / Fintype.card H := by
      intro h
      apply Finset.sup'_le
      intro i _
      rw [max_eq_left (sub_nonneg.mpr (htlo.trans (hlo i)))]
      have ht := min_le_right lo (z / Fintype.card H - M)
      have hh := hM i h
      dsimp [t] at *
      linarith
    have htop : t ≤ topTotal g := htlo.trans
      ((hlo (Classical.arbitrary I)).trans (Finset.le_sup' _ (mem_univ _)))
    refine ⟨t, ?_⟩
    rw [sum_curve, max_eq_right (sub_nonpos.mpr htop), add_zero]
    calc
      _ ≤ ∑ _ : H, z / (Fintype.card H : ℝ) := Finset.sum_le_sum (fun h _ => henv h)
      _ = z := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        have hcard : (Fintype.card H : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
        field_simp
  · let M : ℝ := ∑ h, univ.sup' univ_nonempty (fun i => g i h)
    let t := max (topTotal g) (z + topTotal g - M)
    have ht : topTotal g ≤ t := le_max_left _ _
    have henv : ∀ h, envelope g h t = univ.sup' univ_nonempty (fun i => g i h) := by
      intro h
      apply Finset.sup'_congr univ_nonempty rfl
      intro i _
      have hi : total g i ≤ t := (Finset.le_sup' _ (mem_univ i)).trans ht
      rw [max_eq_right (sub_nonpos.mpr hi), sub_zero]
    refine ⟨t, ?_⟩
    rw [sum_curve, max_eq_left (sub_nonneg.mpr ht)]
    simp only [henv]
    change z ≤ M + (t - topTotal g)
    have hh := le_max_right (topTotal g) (z + topTotal g - M)
    dsimp [t]
    linarith


/-- Every nonempty finite coordinatewise chain has a normalized monotone
one-Lipschitz interpolation, including repeated knots. -/
theorem exists_normalized_chain (g : I → H → ℝ)
    (hchain : ∀ i j, (∀ h, g i h ≤ g j h) ∨ (∀ h, g j h ≤ g i h)) :
    ∃ f : H → ℝ → ℝ,
      (∀ h, Monotone (f h)) ∧
      (∀ h, LipschitzWith 1 (f h)) ∧
      (∀ z, (∑ h, f h z) = z) ∧
      (∀ i h, f h (total g i) = g i h) := by
  let h₀ : H := Classical.arbitrary H
  obtain ⟨f, hm, hl, hs, hk⟩ :=
    MonotoneNormalization.exists_normalized_curve (curve g h₀)
      (curve_monotone g h₀) (sum_curve_surjective g h₀)
  refine ⟨f, hm, hl, hs, ?_⟩
  intro i h
  have hh := hk (total g i) h
  have hsumk : (∑ j, curve g h₀ j (total g i)) = total g i :=
    Finset.sum_congr rfl (fun j _ => curve_knot g hchain h₀ j i)
  rw [hsumk, curve_knot g hchain] at hh
  exact hh

end LeanMachine.MonotoneChain
