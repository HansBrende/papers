import SourceCovers.JointProfiles
import SourceCovers.PrefixDeficit
import LeanMachine.PrefixError

set_option autoImplicit false

/-! The paid-error limit, shared by all geometric credits. The same rounded
widths and outside-family budgets work independently of the credit chosen. -/

namespace SourceCovers

open Classical Finset Filter LeanMachine
open scoped BigOperators Topology
noncomputable section

namespace AdmissibleGeometry

variable {c β : ℝ} {N q : ℕ} (G : AdmissibleGeometry c β N q)

def prefixError (O : SortedCore G.core) (J R M w a : ℕ) : ℝ :=
  2 * bankCost M q * ((G.T - 1 : ℕ) : ℝ) / (G.d * G.inputLength) +
    2 * ((w : ℝ) - 1) / G.inputLength +
    ((G.d : ℝ) * G.b - G.b + 1) / (2 * G.inputLength) +
    β / G.inputLength * (J + q +
      ((G.inputLength : ℝ) * ∑ i ∈ Ico R J, O.hopProfile G.inputLength i) /
        ((M - R : ℕ) : ℝ) +
      (1 + (N : ℝ) * a) * bankCost M q * ((G.T - 1 : ℕ) : ℝ) / w)

end AdmissibleGeometry

namespace NearFullSequence.JointProfile

variable {c β : ℝ} {N q : ℕ} {S : NearFullSequence c β N q} (P : S.JointProfile)

/-- An explicit upper error converging on the same profile subsequence.
No assumption about the geometric credit, or about its convergence, is used. -/
theorem prefix_error_limit_of_rate (J R M : ℕ) {η lam : ℝ}
    (hη : 0 ≤ η) (hlam : 0 < lam) :
    ∃ (w a : ℕ → ℕ) (F : ℕ → ℝ),
      (∀ n, let G := S.geometry (P.subsequence n)
        let O := S.order (P.subsequence n)
        0 < w n ∧ G.a0 ≤ a n ∧ η * G.inputLength ≤ (a n : ℝ) ∧
          G.prefixError O J R M (w n) (a n) ≤ F n) ∧
      (∀ n, lam * (S.geometry (P.subsequence n)).inputLength ≤ (w n : ℝ)) ∧
      Tendsto (fun n => (w n : ℝ) / (S.geometry (P.subsequence n)).inputLength)
        atTop (𝓝 lam) ∧
      Tendsto (fun n => (S.geometry (P.subsequence n)).relativeDeficit + F n) atTop
        (𝓝 (β * (∑ i ∈ Ico R J, P.h i) / ((M - R : ℕ) : ℝ) + 2 * lam +
          β * N * (bankCost M q : ℝ) * c * η / lam)) := by
  have hβ : 0 ≤ β := recordCapacity_nonneg (S.geometry 0).capacity
  let G := fun n => S.geometry (P.subsequence n)
  let L := fun n => (G n).inputLength
  let w := fun n => Nat.ceil (lam * (L n : ℝ))
  let a := fun n => max (G n).a0 (Nat.ceil (η * (L n : ℝ)))
  let H := fun n => ∑ i ∈ Ico R J, S.hops (P.subsequence n) i
  let C : ℝ := bankCost M q
  let F := fun n =>
    (2 * C * c + 1) / (G n).d + 2 * ((w n : ℝ) / L n) +
      β * ((J : ℝ) + q) / L n + β * H n / ((M - R : ℕ) : ℝ) +
      β * C * c * ((1 / (L n : ℝ) + (N : ℝ) * ((a n : ℝ) / L n)) /
        ((w n : ℝ) / L n))
  have hw : ∀ n, 0 < w n := fun n =>
    Nat.ceil_pos.mpr (mul_pos hlam (by exact_mod_cast (G n).inputLength_pos))
  have hsub := P.strictMono.tendsto_atTop
  have hL : Tendsto L atTop atTop := S.inputLength_tendsto.comp hsub
  have hd : Tendsto (fun n => (G n).d) atTop atTop := S.dimension_tendsto.comp hsub
  have ha0 : Tendsto (fun n => ((G n).a0 : ℝ) / L n) atTop (𝓝 0) :=
    S.outside_tendsto.comp hsub
  have hΔ : Tendsto (fun n => (G n).relativeDeficit) atTop (𝓝 0) :=
    S.deficit_tendsto.comp hsub
  have hwidth : Tendsto (fun n => (w n : ℝ) / L n) atTop (𝓝 lam) :=
    PrefixError.ceil_scaled_tendsto hL hlam.le
  have hsize : Tendsto (fun n => (a n : ℝ) / L n) atTop (𝓝 η) := by
    simpa only [a, Nat.cast_max] using PrefixError.max_ceil_scaled_tendsto hL ha0 hη
  have hH : Tendsto H atTop (𝓝 (∑ i ∈ Ico R J, P.h i)) :=
    (P.finite_sums_tendsto (Ico R J)).1
  have hinvL : Tendsto (fun n => 1 / (L n : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat.comp hL
  have hmove : Tendsto (fun n => (2 * C * c + 1) / (G n).d) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat _).comp hd
  have houter : Tendsto (fun n => β * ((J : ℝ) + q) / (L n : ℝ)) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat _).comp hL
  have hres : Tendsto
      (fun n => β * C * c *
        ((1 / (L n : ℝ) + (N : ℝ) * ((a n : ℝ) / L n)) / ((w n : ℝ) / L n)))
      atTop (𝓝 (β * N * C * c * η / lam)) := by
    convert ((hinvL.add (hsize.const_mul (N : ℝ))).div hwidth hlam.ne').const_mul
      (β * C * c) using 1
    congr 1
    field_simp
    ring
  have hF : Tendsto F atTop
      (𝓝 (β * (∑ i ∈ Ico R J, P.h i) / ((M - R : ℕ) : ℝ) + 2 * lam +
        β * N * C * c * η / lam)) := by
    convert (((hmove.add (hwidth.const_mul 2)).add houter).add
      ((hH.const_mul β).div_const ((M - R : ℕ) : ℝ))).add hres using 1
    congr 1
    ring
  refine ⟨w, a, F, ?_, fun n => Nat.le_ceil _, hwidth, ?_⟩
  · intro n
    refine ⟨hw n, le_max_left _ _, ?_, ?_⟩
    · calc
        _ ≤ (Nat.ceil (η * (L n : ℝ)) : ℝ) := Nat.le_ceil _
        _ ≤ _ := Nat.cast_le.mpr (le_max_right _ _)
    · simpa only [AdmissibleGeometry.prefixError, F, L, C, H, NearFullSequence.hops,
        AdmissibleGeometry.inputLength, Nat.cast_mul] using
        PrefixError.finite_error_le (H := H n) (J := J) (q := q)
        (M := M) (R := R) (N := N) (a := a n)
        (G n).hd (G n).hb (hw n) hβ (Nat.cast_nonneg (bankCost M q)) (G n).runtime
  · simpa only [zero_add] using hΔ.add hF

/-- The original default-rate statement is a specialization of the same rounding proof. -/
theorem prefix_error_limit (J R M : ℕ) {lam : ℝ} (hlam : 0 < lam) :
    ∃ (w a : ℕ → ℕ) (F : ℕ → ℝ),
      (∀ n, let G := S.geometry (P.subsequence n)
        let O := S.order (P.subsequence n)
        0 < w n ∧ G.a0 ≤ a n ∧ c * G.inputLength / (J + 1) ≤ (a n : ℝ) ∧
          G.prefixError O J R M (w n) (a n) ≤ F n) ∧
      Tendsto (fun n => (S.geometry (P.subsequence n)).relativeDeficit + F n) atTop
        (𝓝 (β * (∑ i ∈ Ico R J, P.h i) / ((M - R : ℕ) : ℝ) + 2 * lam +
          β * N * (bankCost M q : ℝ) * c ^ 2 / (lam * (J + 1)))) := by
  have hc : 0 ≤ c := by simpa using P.hop_mass.2.1 ∅
  obtain ⟨w, a, F, hdata, _, _, hlimit⟩ := P.prefix_error_limit_of_rate J R M
    (η := c / (J + 1)) (div_nonneg hc (by positivity)) hlam
  refine ⟨w, a, F, ?_, ?_⟩
  · intro n
    obtain ⟨hw, ha0, ha, he⟩ := hdata n
    refine ⟨hw, ha0, ?_, he⟩
    convert ha using 1
    ring
  · convert hlimit using 1
    congr 1
    field_simp

end NearFullSequence.JointProfile
end
end SourceCovers
