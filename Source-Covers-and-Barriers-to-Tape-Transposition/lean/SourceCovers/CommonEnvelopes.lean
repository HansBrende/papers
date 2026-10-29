import SourceCovers.UniformDeficit
import SourceCovers.HopEnvelope
import LeanMachine.TailLiminf
import LeanMachine.PowerEnvelope

set_option autoImplicit false

/-!
# Uniform exclusions from common size envelopes

The lower limit is taken in the extended nonnegative reals, so an unbounded
sequence cannot satisfy the condition through a default real extremum.
In fact only a fixed finite prefix needs obey the envelope, with positive
slack. The original exact common-envelope result follows immediately.
-/

namespace SourceCovers

open Classical Filter LeanMachine
open scoped BigOperators Topology
noncomputable section

/-- Arbitrarily late polynomially scaled envelope tails approach zero. -/
def EnvelopeTailSmall (q : ℕ) (g : ℕ → ℝ) : Prop :=
  liminf (fun R : ℕ => ENNReal.ofReal
    ((R + 2 : ℝ) ^ (q - 1) * ∑' i, g (i + R))) atTop = 0

/-- A dominated joint profile contradicts the common envelope's tail test.
All infinite sums here are justified by independently proved summability. -/
theorem NearFullSequence.JointProfile.false_of_envelope
    {c β : ℝ} {N q : ℕ} {S : NearFullSequence c β N q} (P : S.JointProfile)
    (hβ : 0 < β) (hq : 1 ≤ q) {g : ℕ → ℝ} (hg : Summable g)
    (hsmall : EnvelopeTailSmall q g) (hbound : ∀ i, P.h i ≤ g i) : False := by
  obtain ⟨A, hA, hfloor⟩ := P.exists_scaled_tail_floor hβ hq
  obtain ⟨R, _, hR⟩ := TailLiminf.liminf_ofReal_eq_zero_iff.mp hsmall A hA 0
  have htail : P.hopTail R ≤ ∑' i, g (i + R) :=
    ((summable_nat_add_iff R).mpr P.hop_mass.2.2.1).tsum_le_tsum
      (fun i => hbound (i + R)) ((summable_nat_add_iff R).mpr hg)
  exact (not_lt_of_ge ((hfloor R).trans
    (mul_le_mul_of_nonneg_left htail (by positivity)))) hR

private structure EnvelopeApproximation (c β : ℝ) (N q : ℕ) (g : ℕ → ℝ) where
  geometry : AdmissibleGeometry c β N q
  cutoff : ℕ
  slack : ℝ
  slack_nonneg : 0 ≤ slack
  order : SortedCore geometry.core
  bound : ∀ i < cutoff, order.hopProfile geometry.inputLength i ≤ g i + slack

/-- A fixed finite prefix, with a positive common slack, already suffices.
No envelope restriction is placed on any later core rank. -/
theorem finite_prefix_envelope_uniform_deficit {c β : ℝ} {N q : ℕ}
    (hβ : 0 < β) (hq : 1 ≤ q) {g : ℕ → ℝ}
    (hg : Summable g) (hsmall : EnvelopeTailSmall q g) :
    ∃ ε > (0 : ℝ), ∃ m : ℕ, ∀ G : AdmissibleGeometry c β N q,
      ∀ O : SortedCore G.core, m ≤ G.d → (G.a0 : ℝ) ≤ ε * G.inputLength →
      (∀ i < m, O.hopProfile G.inputLength i ≤ g i + ε) →
        ε * G.inputLength ≤ G.deficit ∧
          (G.C.card : ℝ) ≤ (2 : ℝ) ^ ((1 - ε) * G.inputLength) := by
  have hno : ∀ A : ℕ → EnvelopeApproximation c β N q g,
      Tendsto (fun n => min (A n).geometry.d (A n).cutoff) atTop atTop →
      Tendsto (fun n => max ((A n).geometry.a0 / ((A n).geometry.inputLength : ℝ))
        (A n).slack) atTop (𝓝 0) →
      Tendsto (fun n => (A n).geometry.relativeDeficit) atTop (𝓝 0) → False := by
    intro A hdim hcost hΔ
    have hd := tendsto_atTop_mono (fun n => Nat.min_le_left _ _) hdim
    have hJ := tendsto_atTop_mono (fun n => Nat.min_le_right _ _) hdim
    have ha := squeeze_zero (fun n => by positivity :
        ∀ n, (0 : ℝ) ≤ (A n).geometry.a0 / ((A n).geometry.inputLength : ℝ))
      (fun n => le_max_left _ _) hcost
    have hη := squeeze_zero (fun n => (A n).slack_nonneg)
      (fun n => le_max_right _ _) hcost
    let S : NearFullSequence c β N q :=
      { geometry := fun n => (A n).geometry
        order := fun n => (A n).order
        dimension_tendsto := hd
        outside_tendsto := ha
        deficit_tendsto := hΔ }
    obtain ⟨P⟩ := S.exists_jointProfile
    apply P.false_of_envelope hβ hq hg hsmall
    intro i
    have hright : Tendsto (fun n => g i + (A (P.subsequence n)).slack)
        atTop (𝓝 (g i)) := by
      simpa using tendsto_const_nhds.add (hη.comp P.strictMono.tendsto_atTop)
    apply le_of_tendsto_of_tendsto (P.hops_tendsto i) hright
    filter_upwards [(tendsto_atTop.1 (hJ.comp P.strictMono.tendsto_atTop)) (i + 1)] with n hn
    exact (A (P.subsequence n)).bound i (Nat.lt_of_succ_le hn)
  obtain ⟨ε, hε, m, hgap⟩ := UniformGap.exists_gap
    (fun A : EnvelopeApproximation c β N q g => min A.geometry.d A.cutoff)
    (fun A => max ((A.geometry.a0 : ℝ) / A.geometry.inputLength) A.slack)
    (fun A => A.geometry.relativeDeficit)
    (fun A => (A.slack_nonneg).trans (le_max_right _ _))
    (fun A => A.geometry.relativeDeficit_nonneg) hno
  refine ⟨ε, hε, m, fun G O hd ha henv => ?_⟩
  let A : EnvelopeApproximation c β N q g := ⟨G, m, ε, hε.le, O, henv⟩
  have hL : (0 : ℝ) < G.inputLength := by exact_mod_cast G.inputLength_pos
  have h := hgap A (le_min hd le_rfl) (max_le ((div_le_iff₀ hL).mpr ha) le_rfl)
  have hdef := (le_div_iff₀ hL).mp h
  exact ⟨hdef, G.deficit_card_iff.mp hdef⟩

/-- The original common-envelope conclusion, with the same constants for
all positive entry widths and every choice of sorted tie breaking. -/
theorem common_envelope_uniform_deficit {c β : ℝ} {N q : ℕ}
    (hβ : 0 < β) (hq : 1 ≤ q) {g : ℕ → ℝ}
    (hg : Summable g) (hsmall : EnvelopeTailSmall q g) :
    ∃ ε > (0 : ℝ), ∃ d₀ : ℕ, ∀ G : AdmissibleGeometry c β N q,
      G.HasHopEnvelope g → d₀ ≤ G.d → (G.a0 : ℝ) ≤ ε * G.inputLength →
        ε * G.inputLength ≤ G.deficit ∧
          (G.C.card : ℝ) ≤ (2 : ℝ) ^ ((1 - ε) * G.inputLength) := by
  obtain ⟨ε, hε, m, h⟩ := finite_prefix_envelope_uniform_deficit hβ hq hg hsmall
  refine ⟨ε, hε, m, fun G henv hd ha => ?_⟩
  obtain ⟨O, hO⟩ := henv
  exact h G O hd ha (fun i _ => (hO i).trans (le_add_of_nonneg_right hε.le))

/-- The paper's power-law specialization is obtained from a finite critical
moment, reusing the shared power-envelope and moment-to-tail lemmas. -/
theorem power_envelope_tailSmall {q : ℕ} (hq : 1 ≤ q)
    {p H : ℝ} (hp : (q : ℝ) < p) (hH : 0 ≤ H) :
    EnvelopeTailSmall q (fun i => H / (i + 1 : ℝ) ^ p) := by
  apply TailLiminf.liminf_ofReal_eq_zero_of_tendsto
  apply PowerEnvelope.polynomial_tail_tendsto_zero (q - 1) ?_ hH 2 (by norm_num)
  simpa only [Nat.cast_sub hq, Nat.cast_one, sub_add_cancel] using hp

/-- In particular every real exponent `p > q` and nonnegative amplitude
gives a uniform deficit. Zero amplitude is included. -/
theorem power_envelope_uniform_deficit {c β : ℝ} {N q : ℕ}
    (hβ : 0 < β) (hq : 1 ≤ q) {p H : ℝ} (hp : (q : ℝ) < p) (hH : 0 ≤ H) :
    ∃ ε > (0 : ℝ), ∃ d₀ : ℕ, ∀ G : AdmissibleGeometry c β N q,
      G.HasHopEnvelope (fun i => H / (i + 1 : ℝ) ^ p) →
      d₀ ≤ G.d → (G.a0 : ℝ) ≤ ε * G.inputLength →
        ε * G.inputLength ≤ G.deficit ∧
          (G.C.card : ℝ) ≤ (2 : ℝ) ^ ((1 - ε) * G.inputLength) := by
  apply common_envelope_uniform_deficit hβ hq
    (PowerEnvelope.summable (lt_of_le_of_lt (by exact_mod_cast hq) hp) H)
  exact power_envelope_tailSmall hq hp hH

end
end SourceCovers
