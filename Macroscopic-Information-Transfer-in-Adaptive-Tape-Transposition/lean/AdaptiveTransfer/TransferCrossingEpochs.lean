import NativeRelations.MacroscopicSkeleton
import Mathlib

/-! Literal grid epochs and their canonical signed extrema. These finite
choices depend only on the head, sign and epoch, not on a subsequently
assigned crossing target.
-/

namespace AdaptiveTransfer.TransferCrossing
open Finset BoundedNesting NativeRelations MergeDepth

def signed (y : ℕ → ℤ) (sign : Bool) (t : ℕ) : ℤ := if sign then y t else -y t

theorem signed_abs_sub (y : ℕ → ℤ) (sign : Bool) (u v : ℕ) :
    |signed y sign u - signed y sign v| = |y u - y v| := by
  cases sign
  · simp only [signed, Bool.false_eq_true, ↓reduceIte]
    rw [show -y u - -y v = -(y u - y v) by ring, abs_neg]
  · rfl

theorem signed_isWalk {y : ℕ → ℤ} (hy : IsWalk y) (sign : Bool) : IsWalk (signed y sign) :=
  fun t => (signed_abs_sub y sign (t + 1) t).trans_le (hy t)

theorem signed_isHop_iff (y : ℕ → ℤ) (sign : Bool) (U p u : ℕ) :
    IsHop (signed y sign) U p u ↔ IsHop y U p u := by
  cases sign <;> simp [signed, IsHop]

theorem signed_excursion_iff (y : ℕ → ℤ) (sign : Bool) (H p u : ℕ) :
    HasHopExcursionGTAt (signed y sign) H p u ↔ HasHopExcursionGTAt y H p u := by
  simp only [HasHopExcursionGTAt, signed_abs_sub]

noncomputable def maximizeOn (f : ℕ → ℤ) (S : Finset ℕ) : ℕ :=
  if h : S.Nonempty then (exists_max_image S f h).choose else 0

theorem maximizeOn_spec {f : ℕ → ℤ} {S : Finset ℕ} (h : S.Nonempty) :
    maximizeOn f S ∈ S ∧ ∀ t ∈ S, f t ≤ f (maximizeOn f S) := by
  simp only [maximizeOn, dite_eq_left h]
  exact (exists_max_image S f h).choose_spec

noncomputable def minimizeOn (f : ℕ → ℤ) (S : Finset ℕ) : ℕ :=
  maximizeOn (fun t => -f t) S

theorem minimizeOn_spec {f : ℕ → ℤ} {S : Finset ℕ} (h : S.Nonempty) :
    minimizeOn f S ∈ S ∧ ∀ t ∈ S, f (minimizeOn f S) ≤ f t := by
  have hh := maximizeOn_spec (f := fun t => -f t) h
  refine ⟨hh.1, fun t ht => ?_⟩
  have he := hh.2 t ht
  change f (maximizeOn (fun t => -f t) S) ≤ f t
  omega

def epochTimes (y : ℕ → ℤ) (U H e : ℕ) : Finset ℕ :=
  (range U).filter fun t => epochIdx y H t = e

noncomputable def epochMax (y : ℕ → ℤ) (U H : ℕ) (sign : Bool) (e : ℕ) : ℕ :=
  maximizeOn (signed y sign) (epochTimes y U H e)

noncomputable def epochMin (y : ℕ → ℤ) (U H : ℕ) (sign : Bool) (e : ℕ) : ℕ :=
  minimizeOn (signed y sign) (epochTimes y U H e)

noncomputable def prefixMin (y : ℕ → ℤ) (sign : Bool) (A : ℕ) : ℕ :=
  minimizeOn (signed y sign) (Icc 0 A)

noncomputable def suffixMax (y : ℕ → ℤ) (U : ℕ) (sign : Bool) (B : ℕ) : ℕ :=
  maximizeOn (signed y sign) (Ico B U)

theorem epoch_diameter {y : ℕ → ℤ} (hy : IsWalk y) (hy0 : y 0 = 0)
    {U H a b : ℕ} (hH : 1 ≤ H) (ha : a < U) (hb : b < U)
    (he : epochIdx y H a = epochIdx y H b) (sign : Bool) :
    |signed y sign a - signed y sign b| < 2 * (H : ℤ) := by
  rw [signed_abs_sub]
  have h₁ := abs_sub_skeletonGridAt_lt hy hy0 hH ha
  have h₂ := abs_sub_skeletonGridAt_lt hy hy0 hH hb
  rw [he] at h₁
  have htri : |y a - y b| ≤
      |y a - skeletonGridAt (tapeSkeleton y U H) (epochIdx y H b) * (H : ℤ)| +
      |y b - skeletonGridAt (tapeSkeleton y U H) (epochIdx y H b) * (H : ℤ)| := by
    calc
      _ = |(y a - skeletonGridAt (tapeSkeleton y U H) (epochIdx y H b) * (H : ℤ)) -
          (y b - skeletonGridAt (tapeSkeleton y U H) (epochIdx y H b) * (H : ℤ))| := by congr 1; ring
      _ ≤ _ := abs_sub _ _
  omega

theorem epoch_between {y : ℕ → ℤ} {H a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c)
    (he : epochIdx y H a = epochIdx y H c) : epochIdx y H b = epochIdx y H a := by
  have h₁ := epochIdx_mono (y := y) (Λ := H) hab
  have h₂ := epochIdx_mono (y := y) (Λ := H) hbc
  omega

/-- An epoch containing a >2H excursion point cannot cross either endpoint
of its consecutive revisit. Thus all its canonical extrema stay inside. -/
theorem epoch_inside_long_hop {y : ℕ → ℤ} (hy : IsWalk y) (hy0 : y 0 = 0)
    {U H p u r z : ℕ} (hH : 1 ≤ H) (hh : IsHop y U p u)
    (hr : r ∈ Ioo p u) (hfar : 2 * (H : ℤ) < |y r - y p|)
    (_hz : z < U) (he : epochIdx y H z = epochIdx y H r) : z ∈ Ioo p u := by
  have hpU : p < U := by have := hh.1; have := hh.2.1; omega
  have hrU : r < U := (mem_Ioo.mp hr).2.trans hh.2.1
  have hpr := mem_Ioo.mp hr
  by_cases hpz : p < z
  · by_cases hzu : z < u
    · exact mem_Ioo.mpr ⟨hpz, hzu⟩
    · have he' := epoch_between hpr.2.le (show u ≤ z by omega) he.symm
      have hd := epoch_diameter hy hy0 hH hrU hh.2.1 he'.symm true
      simp only [signed, ↓reduceIte, hh.2.2.1] at hd
      omega
  · have he' := epoch_between (show z ≤ p by omega) hpr.1.le he
    have hd := epoch_diameter hy hy0 hH hrU hpU (he'.trans he).symm true
    simp only [signed, ↓reduceIte] at hd
    omega

theorem epochMax_spec {y : ℕ → ℤ} {U H r : ℕ} (hr : r < U) (sign : Bool) :
    epochMax y U H sign (epochIdx y H r) ∈ epochTimes y U H (epochIdx y H r) ∧
      signed y sign r ≤ signed y sign (epochMax y U H sign (epochIdx y H r)) := by
  have hm : r ∈ epochTimes y U H (epochIdx y H r) := mem_filter.mpr ⟨mem_range.mpr hr, rfl⟩
  have hh := maximizeOn_spec (f := signed y sign) ⟨r, hm⟩
  exact ⟨hh.1, hh.2 r hm⟩

theorem epochMin_spec {y : ℕ → ℤ} {U H r : ℕ} (hr : r < U) (sign : Bool) :
    epochMin y U H sign (epochIdx y H r) ∈ epochTimes y U H (epochIdx y H r) ∧
      signed y sign (epochMin y U H sign (epochIdx y H r)) ≤ signed y sign r := by
  have hm : r ∈ epochTimes y U H (epochIdx y H r) := mem_filter.mpr ⟨mem_range.mpr hr, rfl⟩
  have hh := minimizeOn_spec (f := signed y sign) ⟨r, hm⟩
  exact ⟨hh.1, hh.2 r hm⟩

end AdaptiveTransfer.TransferCrossing
