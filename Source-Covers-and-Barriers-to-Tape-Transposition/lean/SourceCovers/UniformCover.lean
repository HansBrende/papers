import SourceCovers.CoverMeans
import SourceCovers.UniformDeficit
import LeanMachine.PowerTail
import LeanMachine.TailLiminf

set_option autoImplicit false

/-!
# Uniform correctness deficits from mean cover budgets

One supplied original hop order is retained for both finite mean covers and
limiting profiles. The general envelope test requires only arbitrarily late
small values of the cover budget times the envelope tail, divided by `R + 2`.
The two manuscript criteria are specializations of the same paid-tail bound.
-/

namespace SourceCovers

open Classical Filter LeanMachine
open scoped BigOperators Topology
noncomputable section

namespace AdmissibleGeometry

variable {c β : ℝ} {N q : ℕ} (G : AdmissibleGeometry c β N q)

/-- The same budget bounds all original prefix selections in a supplied order. -/
def HasMeanCoverBound (O : SortedCore G.core) (f : ℕ → ℝ) : Prop :=
  ∀ R, 0 < R → ∀ J, R ≤ J →
    G.prefixMeanCover O J R (2 * R + 2) (by omega) ≤ f R

theorem HasMeanCoverBound.one_le {G : AdmissibleGeometry c β N q} {O : SortedCore G.core} {f : ℕ → ℝ}
    (h : G.HasMeanCoverBound O f) {R : ℕ} (hR : 0 < R) : 1 ≤ f R :=
  (G.one_le_prefixMeanCover O (J := R) (by omega : 2 ≤ 2 * R + 2)
    (by omega : R < 2 * R + 2)).trans (h R hR R le_rfl)

end AdmissibleGeometry

/-- Retain a chosen order while applying the existing class-uniform gap lemma. -/
theorem uniform_deficit_of_no_ordered_nearFull {c β : ℝ} {N q : ℕ}
    (P : ∀ G : AdmissibleGeometry c β N q, SortedCore G.core → Prop)
    (hno : ∀ S : NearFullSequence c β N q, (∀ n, P (S.geometry n) (S.order n)) → False) :
    ∃ ε > (0 : ℝ), ∃ d₀ : ℕ, ∀ G : AdmissibleGeometry c β N q,
      ∀ O : SortedCore G.core, P G O → d₀ ≤ G.d →
      (G.a0 : ℝ) ≤ ε * G.inputLength →
        ε * G.inputLength ≤ G.deficit ∧
          (G.C.card : ℝ) ≤ (2 : ℝ) ^ ((1 - ε) * G.inputLength) := by
  obtain ⟨ε, hε, d₀, hgap⟩ := uniform_deficit_of_no_nearFull
    (fun G => ∃ O, P G O) (by
      intro S hP
      choose O hO using hP
      exact hno { S with order := O } hO)
  exact ⟨ε, hε, d₀, fun G O hP => hgap G ⟨O, hP⟩⟩

namespace NearFullSequence.JointProfile

variable {c β : ℝ} {N q : ℕ} {S : NearFullSequence c β N q} (P : S.JointProfile)

/-- Finite arithmetic mean bounds pass through the same ordered upper limits. -/
theorem reciprocalCoverLimit_ge_of_mean {f : ℕ → ℝ}
    (hcover : ∀ n, (S.geometry n).HasMeanCoverBound (S.order n) f)
    {R : ℕ} (hR : 0 < R) :
    1 / f R ≤ P.reciprocalCoverLimit R (2 * R + 2) (by omega) := by
  apply BoundedLimsup.le_limsup
    (fun J => (P.prefixReciprocal_limsup_bounds (J := J)
      (by omega : 2 ≤ 2 * R + 2) (by omega : R < 2 * R + 2)).2)
  apply eventually_atTop.2 ⟨R, fun J hRJ => ?_⟩
  apply BoundedLimsup.le_limsup
    (fun n => (P.prefixReciprocal_bounds (J := J)
      (by omega : 2 ≤ 2 * R + 2) (by omega : R < 2 * R + 2) n).2)
  exact Eventually.of_forall fun n =>
    (S.geometry (P.subsequence n)).one_div_le_prefixMeanReciprocal
      (S.order (P.subsequence n)) (by omega) (by omega)
      (hcover (P.subsequence n) R hR J hRJ)

/-- A mean cover budget forces a positive weighted tail whenever `V_K < 1`.
The undivided form keeps the positive part and needs no such hypothesis. -/
theorem mean_cover_tail_lower {f : ℕ → ℝ}
    (hcover : ∀ n, (S.geometry n).HasMeanCoverBound (S.order n) f)
    (K : ℕ) {R : ℕ} (hR : 0 < R) :
    max (1 - P.variationTail K) 0 ^ 2 / (2 * (2 * (K : ℝ) + 1)) ≤
      β * (P.hopTail R * f R / (R + 2 : ℝ)) := by
  have hf : 0 < f R := zero_lt_one.trans_le ((hcover 0).one_le hR)
  have h := (mul_le_mul_of_nonneg_left (P.reciprocalCoverLimit_ge_of_mean hcover hR)
    (by positivity : 0 ≤ max (1 - P.variationTail K) 0 ^ 2 /
      (2 * (2 * (K : ℝ) + 1)))).trans
    (P.weighted_reciprocal_cover (K := K) (by omega : 2 ≤ 2 * R + 2)
      (by omega : R < 2 * R + 2))
  rw [mul_one_div, show 2 * R + 2 - R = R + 2 by omega] at h
  have h' := (div_le_iff₀ hf).mp h
  simpa only [Nat.cast_add, Nat.cast_ofNat, mul_div_assoc, div_mul_eq_mul_div,
    mul_assoc] using h'

private theorem false_of_mean_cover_upperTail {f u : ℕ → ℝ}
    (hcover : ∀ n, (S.geometry n).HasMeanCoverBound (S.order n) f)
    (hu : ∀ R, 0 < R → P.hopTail R * f R / (R + 2 : ℝ) ≤ u R)
    (hsmall : liminf (fun R => ENNReal.ofReal (u R)) atTop = 0) : False := by
  obtain ⟨K, hK⟩ := (P.tails_tendsto_zero.2.eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))).exists
  let A : ℝ := max (1 - P.variationTail K) 0 ^ 2 / (2 * (2 * (K : ℝ) + 1))
  have hA : 0 < A := by
    have : 0 < max (1 - P.variationTail K) 0 :=
      (sub_pos.mpr hK).trans_le (le_max_left _ _)
    positivity
  have hβ : 0 ≤ β := recordCapacity_nonneg (S.geometry 0).capacity
  have hden : 0 < β + 1 := by linarith
  obtain ⟨R, hR, hsmallR⟩ := TailLiminf.liminf_ofReal_eq_zero_iff.mp hsmall
    (A / (β + 1)) (div_pos hA hden) 1
  have h := (P.mean_cover_tail_lower hcover K (by omega : 0 < R)).trans
    (mul_le_mul_of_nonneg_left (hu R (by omega)) hβ)
  have hupper := mul_le_mul_of_nonneg_left hsmallR.le hβ
  have hid : (β + 1) * (A / (β + 1)) = A := mul_div_cancel₀ A hden.ne'
  change A ≤ β * u R at h
  nlinarith [div_pos hA hden]

include P in
/-- Linear mean cover growth is incompatible with summable hop mass. -/
theorem false_of_linear_mean_cover {B : ℝ}
    (hcover : ∀ n, (S.geometry n).HasMeanCoverBound (S.order n)
      (fun R => B * (R + 2 : ℝ))) : False := by
  apply false_of_mean_cover_upperTail P hcover (u := fun R => B * P.hopTail R)
  · intro R _
    have hden : (R + 2 : ℝ) ≠ 0 := by positivity
    field_simp
    ring_nf
    rfl
  · exact TailLiminf.liminf_ofReal_eq_zero_of_tendsto
      (by simpa only [mul_zero] using P.tails_tendsto_zero.1.const_mul B)

end NearFullSequence.JointProfile

/-- A cover budget times an envelope tail is arbitrarily small at arbitrarily
late cutoffs. Extended nonnegative limits avoid totalized real extrema. -/
def CoverTailSmall (g f : ℕ → ℝ) : Prop :=
  liminf (fun R => ENNReal.ofReal ((∑' i, g (i + R)) * f R / (R + 2 : ℝ))) atTop = 0

theorem NearFullSequence.JointProfile.false_of_mean_cover_envelope
    {c β : ℝ} {N q : ℕ} {S : NearFullSequence c β N q} (P : S.JointProfile)
    {g f : ℕ → ℝ} (hg : Summable g) (hsmall : CoverTailSmall g f)
    (hbound : ∀ i, P.h i ≤ g i)
    (hcover : ∀ n, (S.geometry n).HasMeanCoverBound (S.order n) f) : False := by
  apply NearFullSequence.JointProfile.false_of_mean_cover_upperTail P hcover (u := fun R =>
    (∑' i, g (i + R)) * f R / (R + 2 : ℝ)) _ hsmall
  intro R hR
  have htail : P.hopTail R ≤ ∑' i, g (i + R) :=
    ((summable_nat_add_iff R).mpr P.hop_mass.2.2.1).tsum_le_tsum
      (fun i => hbound (i + R)) ((summable_nat_add_iff R).mpr hg)
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right htail
    (zero_le_one.trans ((hcover 0).one_le hR))) (by positivity)

/-- Uniform criterion (a), including zero or negative proposed budgets:
if the class is nonempty, its actual means force a positive budget. -/
theorem linear_mean_cover_uniform_deficit {c β : ℝ} {N q : ℕ} (B : ℝ) :
    ∃ ε > (0 : ℝ), ∃ d₀ : ℕ, ∀ G : AdmissibleGeometry c β N q,
      ∀ O : SortedCore G.core,
      G.HasMeanCoverBound O (fun R => B * (R + 2 : ℝ)) → d₀ ≤ G.d →
      (G.a0 : ℝ) ≤ ε * G.inputLength →
        ε * G.inputLength ≤ G.deficit ∧
          (G.C.card : ℝ) ≤ (2 : ℝ) ^ ((1 - ε) * G.inputLength) := by
  apply uniform_deficit_of_no_ordered_nearFull
    (fun G O => G.HasMeanCoverBound O (fun R => B * (R + 2 : ℝ)))
  intro S hcover
  obtain ⟨P⟩ := S.exists_jointProfile
  exact P.false_of_linear_mean_cover hcover

/-- General uniform criterion: a summable envelope and its weighted-tail test.
The envelope and cover budget must hold in the same supplied original order. -/
theorem envelope_mean_cover_uniform_deficit {c β : ℝ} {N q : ℕ}
    {g f : ℕ → ℝ} (hg : Summable g) (hsmall : CoverTailSmall g f) :
    ∃ ε > (0 : ℝ), ∃ d₀ : ℕ, ∀ G : AdmissibleGeometry c β N q,
      ∀ O : SortedCore G.core,
      (∀ i, O.hopProfile G.inputLength i ≤ g i) → G.HasMeanCoverBound O f →
      d₀ ≤ G.d → (G.a0 : ℝ) ≤ ε * G.inputLength →
        ε * G.inputLength ≤ G.deficit ∧
          (G.C.card : ℝ) ≤ (2 : ℝ) ^ ((1 - ε) * G.inputLength) := by
  obtain ⟨ε, hε, d₀, hgap⟩ := uniform_deficit_of_no_ordered_nearFull
    (c := c) (β := β) (N := N) (q := q)
    (fun G O => (∀ i, O.hopProfile G.inputLength i ≤ g i) ∧ G.HasMeanCoverBound O f)
    (by
      intro S h
      obtain ⟨P⟩ := S.exists_jointProfile
      exact P.false_of_mean_cover_envelope hg hsmall
        (P.hop_le_of_pointwise (fun n => (h n).1)) (fun n => (h n).2))
  exact ⟨ε, hε, d₀, fun G O henv hcover => hgap G O ⟨henv, hcover⟩⟩

/-- Every nonnegative sub-power mean budget satisfies the weighted-tail test
for a power envelope with real exponent above one. -/
theorem power_cover_tailSmall {p H : ℝ} {f : ℕ → ℝ} (hp : 1 < p) (hH : 0 ≤ H)
    (hf0 : ∀ R, 0 ≤ f R)
    (hf : Tendsto (fun R : ℕ => f R / (R : ℝ) ^ p) atTop (𝓝 0)) :
    CoverTailSmall (fun i => H / (i + 1 : ℝ) ^ p) f := by
  apply TailLiminf.liminf_ofReal_eq_zero_of_tendsto
  exact PowerTail.scaled_tail_tendsto_zero hp hH (fun i => by positivity)
    (fun _ => le_rfl) hf0 hf 2 (by norm_num)

/-- Uniform criterion (b), for arbitrary real `p > 1` and `H ≥ 0`.
Zero values of the nonnegative cover budget are permitted. -/
theorem power_mean_cover_uniform_deficit {c β : ℝ} {N q : ℕ}
    {p H : ℝ} {f : ℕ → ℝ} (hp : 1 < p) (hH : 0 ≤ H)
    (hf0 : ∀ R, 0 ≤ f R)
    (hf : Tendsto (fun R : ℕ => f R / (R : ℝ) ^ p) atTop (𝓝 0)) :
    ∃ ε > (0 : ℝ), ∃ d₀ : ℕ, ∀ G : AdmissibleGeometry c β N q,
      ∀ O : SortedCore G.core,
      (∀ i, O.hopProfile G.inputLength i ≤ H / (i + 1 : ℝ) ^ p) →
      G.HasMeanCoverBound O f → d₀ ≤ G.d → (G.a0 : ℝ) ≤ ε * G.inputLength →
        ε * G.inputLength ≤ G.deficit ∧
          (G.C.card : ℝ) ≤ (2 : ℝ) ^ ((1 - ε) * G.inputLength) :=
  envelope_mean_cover_uniform_deficit (PowerEnvelope.summable hp H)
    (power_cover_tailSmall hp hH hf0 hf)

end
end SourceCovers
