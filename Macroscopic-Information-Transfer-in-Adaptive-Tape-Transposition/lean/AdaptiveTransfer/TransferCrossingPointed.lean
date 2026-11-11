import AdaptiveTransfer.TransferCrossingEpochs

/-! Target-preserving crossing construction inside a genuine unit walk.
Both endpoint roles are explicit. The output is an actual crossing pair of
consecutive revisits, not a supplied target or path certificate.
-/

namespace AdaptiveTransfer.TransferCrossing
open Finset BoundedNesting NativeRelations

theorem pointed_upper_crossing {x : ℕ → ℤ} (hx : IsWalk x)
    {T H t₀ A B t₃ v : ℕ} {ell : ℤ}
    (h₀A : t₀ < A) (hAB : A < B) (hB₃ : B < t₃) (h₃T : t₃ < T)
    (h₀ : x t₀ ≤ ell) (hA : ell + 2 * (H : ℤ) < x A)
    (hB : x B ≤ ell) (h₃ : ell + 2 * (H : ℤ) + 1 ≤ x t₃)
    (_hvA : v ≤ A) (hside : ∀ r ∈ Icc v A, ell < x r) :
    ∃ p : ℕ, p < v ∧ x p = ell ∧ p ∈ tapeCrossingLowers x T H := by
  classical
  have hneg : IsWalk (fun r => -x r) := by
    intro r
    simpa only [neg_sub_neg, abs_sub_comm] using hx r
  obtain ⟨p, u, _, hpA, hAu, huB, hplevel, hulevel, hhopn, hexn⟩ :=
    exists_hop_gt_of_valley_eq (T := T) (H := 2 * H) (R := -ell) hneg
      h₀A hAB (hB₃.trans h₃T) (by omega) (by push_cast; omega) (by omega)
  have hp : x p = ell := by omega
  have hu : x u = ell := by omega
  have hhop : IsHop x T p u := (signed_isHop_iff x false T p u).mp hhopn
  have hex : HasHopExcursionGTAt x (2 * H) p u := (signed_excursion_iff x false (2 * H) p u).mp hexn
  have hpv : p < v := by
    by_contra hbad
    have hh := hside p (mem_Icc.mpr ⟨by omega, hpA.le⟩)
    omega
  obtain ⟨p', u', hAp', hp'u, huu', _, hp'level, _, hhop', hex'⟩ :=
    exists_hop_gt_of_valley_eq (T := T) (H := 2 * H)
      (R := ell + 2 * (H : ℤ) + 1) hx hAu (huB.trans_lt hB₃) h₃T
      (by omega) (by push_cast; omega) h₃
  refine ⟨p, hpv, hp, mem_filter.mpr ⟨mem_range.mpr ?_, u, hhop, hex, p', u', hhop', hex', ?_⟩⟩
  · exact hpA.trans (hAB.trans (hB₃.trans h₃T))
  · exact Or.inl ⟨hpA.trans_le hAp', hp'u, huu'⟩

theorem pointed_lower_crossing {x : ℕ → ℤ} (hx : IsWalk x)
    {T H t₀ A B t₃ v : ℕ} {ell : ℤ}
    (h₀A : t₀ < A) (hAB : A < B) (hB₃ : B < t₃) (h₃T : t₃ < T)
    (h₀ : x t₀ ≤ ell - 2 * (H : ℤ) - 1) (hA : ell ≤ x A)
    (hB : x B + 2 * (H : ℤ) < ell) (h₃ : ell ≤ x t₃)
    (_hvB : v ≤ B) (hside : ∀ r ∈ Icc v B, x r < ell) :
    ∃ p : ℕ, p < v ∧ x p = ell ∧ p ∈ tapeCrossingLowers x T H := by
  classical
  obtain ⟨p, u, hAp, hpB, hBu, _, hp, hu, hhop, hex⟩ :=
    exists_hop_gt_of_valley_eq (T := T) (H := 2 * H) (R := ell) hx hAB hB₃ h₃T
      hA (by push_cast; exact hB) h₃
  have hpv : p < v := by
    by_contra hbad
    have hh := hside p (mem_Icc.mpr ⟨by omega, hpB.le⟩)
    omega
  have hneg : IsWalk (fun r => -x r) := by
    intro r
    simpa only [neg_sub_neg, abs_sub_comm] using hx r
  let c : ℤ := ell - 2 * (H : ℤ) - 1
  obtain ⟨p', u', _, hp'p, hpu', hu'B, _, _, hhop'n, hex'n⟩ :=
    exists_hop_gt_of_valley_eq (T := T) (H := 2 * H) (R := -c) hneg
      (h₀A.trans_le hAp) hpB (hB₃.trans h₃T)
      (by dsimp [c]; omega) (by dsimp [c]; omega) (by dsimp [c]; omega)
  have hhop' : IsHop x T p' u' := (signed_isHop_iff x false T p' u').mp hhop'n
  have hex' : HasHopExcursionGTAt x (2 * H) p' u' := (signed_excursion_iff x false (2 * H) p' u').mp hex'n
  refine ⟨p, hpv, hp, mem_filter.mpr ⟨mem_range.mpr ?_, u, hhop, hex, p', u', hhop', hex', ?_⟩⟩
  · exact hpB.trans (hB₃.trans h₃T)
  · exact Or.inr ⟨hp'p, hpu', hu'B.trans_lt hBu⟩

theorem signed_crossingLowers_iff {y : ℕ → ℤ} (sign : Bool) {U H p : ℕ} :
    p ∈ tapeCrossingLowers (signed y sign) U H ↔ p ∈ tapeCrossingLowers y U H := by
  classical
  simp only [tapeCrossingLowers, mem_filter, mem_range, signed_isHop_iff, signed_excursion_iff]

end AdaptiveTransfer.TransferCrossing
