import SourceCovers.NecessaryHopTails
import LeanMachine.UniformGap
import Mathlib.Analysis.SpecialFunctions.Log.Base

set_option autoImplicit false

/-!
# Uniform correctness deficits from exclusion of near-full sequences

The generic implication applies to any class of actual admissible geometries.
The one-exception case reuses the verified critical-moment contradiction.
All positive entry widths are covered by the same uniform constants.
-/

namespace SourceCovers

open Classical Filter LeanMachine
open scoped Topology
noncomputable section

namespace AdmissibleGeometry

variable {c β : ℝ} {N q : ℕ} (G : AdmissibleGeometry c β N q)

theorem deficit_nonneg : 0 ≤ G.deficit := by
  have hcard : (G.C.card : ℝ) ≤ 2 ^ G.inputLength := by
    exact_mod_cast (show G.C.card ≤ 2 ^ G.inputLength by
      simpa [inputLength] using G.C.card_le_univ)
  have hlog := Real.log_le_log (by exact_mod_cast G.correct_nonempty.card_pos) hcard
  rw [Real.log_pow] at hlog
  exact sub_nonneg.mpr ((div_le_iff₀ (Real.log_pos (by norm_num))).mpr hlog)

theorem relativeDeficit_nonneg : 0 ≤ G.relativeDeficit :=
  div_nonneg G.deficit_nonneg (by positivity)

/-- The cardinality conclusion is exactly the deficit conclusion, for any
real fraction; nonemptiness is retained when taking logarithms. -/
theorem deficit_card_iff {ε : ℝ} :
    ε * G.inputLength ≤ G.deficit ↔
      (G.C.card : ℝ) ≤ (2 : ℝ) ^ ((1 - ε) * G.inputLength) := by
  rw [← Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2)
    (by exact_mod_cast G.correct_nonempty.card_pos)]
  simp only [Real.logb, deficit]
  constructor <;> intro h <;> nlinarith

end AdmissibleGeometry

/-- A class-wide uniform gap follows once every near-full sequence in the
class is excluded. The subtype keeps all class hypotheses on every witness. -/
theorem uniform_deficit_of_no_nearFull {c β : ℝ} {N q : ℕ}
    (P : AdmissibleGeometry c β N q → Prop)
    (hno : ∀ S : NearFullSequence c β N q, (∀ n, P (S.geometry n)) → False) :
    ∃ ε > (0 : ℝ), ∃ d₀ : ℕ, ∀ G : AdmissibleGeometry c β N q,
      P G → d₀ ≤ G.d → (G.a0 : ℝ) ≤ ε * G.inputLength →
        ε * G.inputLength ≤ G.deficit ∧
          (G.C.card : ℝ) ≤ (2 : ℝ) ^ ((1 - ε) * G.inputLength) := by
  obtain ⟨ε, hε, d₀, hgap⟩ := UniformGap.exists_gap
    (fun G : {G : AdmissibleGeometry c β N q // P G} => G.val.d)
    (fun G => (G.val.a0 : ℝ) / G.val.inputLength)
    (fun G => G.val.relativeDeficit)
    (fun _ => by positivity) (fun G => G.val.relativeDeficit_nonneg)
    (fun G hd ha hΔ => hno
      (NearFullSequence.ofGeometry (fun n => (G n).val) hd ha hΔ)
      (fun n => (G n).property))
  refine ⟨ε, hε, d₀, fun G hP hd ha => ?_⟩
  have hL : (0 : ℝ) < G.inputLength := by exact_mod_cast G.inputLength_pos
  have h := hgap ⟨G, hP⟩ hd ((div_le_iff₀ hL).mpr ha)
  have hdef := (le_div_iff₀ hL).mp h
  exact ⟨hdef, G.deficit_card_iff.mp hdef⟩

/-- With at most one exception there is no near-full sequence. Even zero or
negative ambient capacity bounds need no separate assumption. -/
theorem NearFullSequence.one_exception_false {c β : ℝ} {N : ℕ}
    (S : NearFullSequence c β N 1) : False := by
  obtain ⟨P⟩ := S.exists_jointProfile
  by_cases hβ : 0 < β
  · apply P.not_summable_moment hβ (by decide)
    simpa using P.hop_mass.2.2.1
  · obtain ⟨K, hK⟩ := ((P.tails_tendsto_zero).2.eventually
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))).exists
    have hpos : 0 < max (1 - P.variationTail K) 0 :=
      (sub_pos.mpr hK).trans_le (le_max_left _ _)
    have h := P.necessary_hop_tail (K := K) (R := 0) (M := 2) (by decide) (by decide)
    have hright : β * P.hopTail 0 / ((2 - 0 : ℕ) : ℝ) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hβ) (P.tails_nonneg 0).1)
        (by positivity)
    exact (not_le_of_gt (by positivity)) (h.trans hright)

/-- Corollary 4.3, uniform over every positive entry width, every record
alphabet, and every admissible geometry with these fixed ambient bounds. -/
theorem one_exception_uniform_deficit (c β : ℝ) (N : ℕ) :
    ∃ ε > (0 : ℝ), ∃ d₀ : ℕ, ∀ G : AdmissibleGeometry c β N 1,
      d₀ ≤ G.d → (G.a0 : ℝ) ≤ ε * G.inputLength →
        ε * G.inputLength ≤ G.deficit ∧
          (G.C.card : ℝ) ≤ (2 : ℝ) ^ ((1 - ε) * G.inputLength) := by
  simpa only [forall_true_left] using
    uniform_deficit_of_no_nearFull (c := c) (β := β) (N := N) (q := 1)
      (fun _ => True) (fun S _ => S.one_exception_false)

end
end SourceCovers
