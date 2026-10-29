import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Data.Int.Interval
import Mathlib.Tactic
import LeanMachine.QueryMovement

/-! Sharp elementary capacity bounds for equally spaced centres on a circle.
Lift each covered centre to an integer lattice point near a real representative
of the ball centre, then count integers in an interval. -/

namespace LeanMachine.CircleGridCapacity

open Finset
noncomputable section

/-- An integer set with real diameter at most `D` has at most `⌊D⌋ + 1`
elements. -/
theorem card_le_floor_diameter (A : Finset ℤ) {D : ℝ} (hD : 0 ≤ D)
    (hdiam : ∀ a ∈ A, ∀ b ∈ A, (a : ℝ) - b ≤ D) :
    A.card ≤ ⌊D⌋₊ + 1 := by
  rcases A.eq_empty_or_nonempty with rfl | hA
  · simp
  let a := A.min' hA
  let b := A.max' hA
  have ha : a ∈ A := min'_mem _ _
  have hb : b ∈ A := max'_mem _ _
  have hab : a ≤ b := le_max' _ _ ha
  have hcast : ((b - a).toNat : ℝ) = (b : ℝ) - a := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (sub_nonneg.mpr hab), Int.cast_sub]
  have hf : (b - a).toNat ≤ ⌊D⌋₊ :=
    (Nat.le_floor_iff hD).mpr (hcast ▸ hdiam b hb a ha)
  have hc : A.card ≤ (b + 1 - a).toNat := by
    rw [← Int.card_Icc]
    exact card_le_card (fun x hx => mem_Icc.mpr ⟨min'_le _ _ hx, le_max' _ _ hx⟩)
  omega

/-- A translated regular grid, with spacing `L / N`. The translation is
arbitrary, so the bound includes both endpoint and midpoint conventions. -/
def centre (L offset : ℝ) (N : ℕ) (i : Fin N) : AddCircle L :=
  ↑(offset + (i : ℝ) * (L / N))

/-- The number of regular-grid centres in a circular closed ball. -/
theorem card_ball_le (L offset : ℝ) (N : ℕ) (hL : 0 < L) (hN : 0 < N)
    (y : AddCircle L) (R : ℝ) (hR : 0 ≤ R) :
    (univ.filter fun i : Fin N => dist (centre L offset N i) y ≤ R).card ≤
      min N (⌊2 * R * N / L⌋₊ + 1) := by
  classical
  obtain ⟨y⟩ := y
  let A := univ.filter fun i : Fin N => dist (centre L offset N i) (↑y) ≤ R
  let z (i : Fin N) := round (L⁻¹ * (offset + (i : ℝ) * (L / N) - y))
  let lift (i : Fin N) : ℤ := (i : ℕ) - (N : ℤ) * z i
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hlift (i : Fin N) :
      offset + (lift i : ℝ) * (L / N) - y =
        offset + (i : ℝ) * (L / N) - y - (z i : ℝ) * L := by
    simp only [lift, Int.cast_sub, Int.cast_natCast, Int.cast_mul]
    field_simp
    ring
  have hmod (i : Fin N) : lift i % (N : ℤ) = (i : ℕ) := by
    have hi : (i : ℤ) < N := by exact_mod_cast i.isLt
    simp only [lift, Int.sub_emod, Int.mul_emod_right, sub_zero, Int.emod_emod]
    exact Int.emod_eq_of_lt (by positivity) hi
  have hinj : Function.Injective lift := by
    intro i j h
    have he := congrArg (fun x : ℤ => x % (N : ℤ)) h
    rw [hmod, hmod] at he
    exact Fin.ext (by exact_mod_cast he)
  have hdist (i : Fin N) (hi : i ∈ A) :
      |offset + (lift i : ℝ) * (L / N) - y| ≤ R := by
    have hi' := (mem_filter.mp hi).2
    simpa only [centre, dist_eq_norm, ← QuotientAddGroup.mk_sub,
      AddCircle.norm_eq, ← hlift, z] using hi'
  have hcard : A.card ≤ ⌊2 * R * N / L⌋₊ + 1 := by
    rw [← card_image_of_injective A hinj]
    apply card_le_floor_diameter _ (by positivity)
    intro a ha b hb
    obtain ⟨i, hi, rfl⟩ := mem_image.mp ha
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hb
    have hi' := (abs_le.mp (hdist i hi)).2
    have hj' := (abs_le.mp (hdist j hj)).1
    apply (le_div_iff₀ hL).mpr
    have h := mul_le_mul_of_nonneg_right (show
      ((lift i : ℝ) - lift j) * (L / N) ≤ 2 * R by nlinarith) hNR.le
    field_simp at h
    nlinarith
  refine le_min ?_ hcard
  calc
    A.card ≤ (univ : Finset (Fin N)).card := card_le_card (filter_subset _ _)
    _ = N := Fintype.card_fin N

/-- Passing from line coordinates to the circle never increases distance. -/
theorem dist_coe_le (L x y : ℝ) :
    dist (x : AddCircle L) (y : AddCircle L) ≤ dist x y := by
  simpa only [dist_eq_norm, ← QuotientAddGroup.mk_sub] using
    (QuotientAddGroup.norm_mk_le_norm (S := AddSubgroup.zmultiples L) (m := x - y))

/-- Capacity of a bank of circular balls, with all overlaps allowed. -/
theorem card_covered_le {ι : Type*} [Fintype ι]
    (L offset : ℝ) (N : ℕ) (hL : 0 < L) (hN : 0 < N)
    (Y : ι → AddCircle L) (R : ℝ) (hR : 0 ≤ R) :
    (QueryMovement.covered (centre L offset N) Y R).card ≤
      min N (Fintype.card ι * (⌊2 * R * N / L⌋₊ + 1)) := by
  classical
  let A (i : ι) := univ.filter fun a : Fin N => dist (centre L offset N a) (Y i) ≤ R
  have he : QueryMovement.covered (centre L offset N) Y R = univ.biUnion A := by
    ext a
    simp [A]
  apply le_min
  · exact (card_le_card (filter_subset _ _)).trans_eq (Fintype.card_fin N)
  · rw [he]
    calc
      _ ≤ ∑ i, (A i).card := card_biUnion_le
      _ ≤ ∑ _i : ι, (⌊2 * R * N / L⌋₊ + 1) := sum_le_sum fun i _ =>
        (card_ball_le L offset N hL hN (Y i) R hR).trans (min_le_right _ _)
      _ = _ := by simp

end
end LeanMachine.CircleGridCapacity
