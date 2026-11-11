import SharedDecoders.CapacityMaskProbabilityCorollaries
import SharedDecoders.CapacityMaskDirectCertificate
import SharedDecoders.CapacityMaskTernaryProbability

/-! # Normalized actual method floors and the strict random-mask comparison -/

namespace SharedDecoders.CapacityMaskProbability

open CapacityMask CapacityRuns CapacityClosure Module
open scoped BigOperators

variable {d : ℕ} [NeZero d]

noncomputable def isolationCertificate (p : ZMod d → Bool) (b : ℕ)
    (R : Finset (ZMod d)) (t : ℕ → ZMod d) (k : ℕ) : ℝ :=
  (b : ℝ)*d*(2+certificate (fun j =>
    ((isolatedRows p (translateSets t j) (Finset.univ\R)).card : ℝ)) k)

theorem isolationCertificate_normalized (p : ZMod d → Bool) (b : ℕ) (hb : 0<b)
    (R : Finset (ZMod d)) (t : ℕ → ZMod d) (k : ℕ) :
    isolationCertificate p b R t k/((b : ℝ)*d^2)=
      (2+certificate (fun j => ((isolatedRows p (translateSets t j) (Finset.univ\R)).card : ℝ)) k)/d := by
  have hb0 : (b : ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hb
  have hd0 : (d : ℝ)≠0 := by exact_mod_cast NeZero.ne d
  unfold isolationCertificate
  field_simp

theorem IsolationGood.normalized_floor (η : ℝ) (hη : 0≤η) (p : ZMod d → Bool)
    (hp : IsolationGood η p) (b : ℕ) (hb : 0<b) (R : Finset (ZMod d)) (hR : R.card=2)
    (t : ℕ → ZMod d) (k : ℕ) :
    9/16-η/4+1/(2*(d : ℝ))≤ isolationCertificate p b R t k/((b : ℝ)*d^2) := by
  rw [isolationCertificate_normalized p b hb R t k]
  have hd0 : (0 : ℝ)<d := by exact_mod_cast NeZero.pos d
  apply (le_div_iff₀ hd0).mpr
  have hh := hp.certificate_floor η hη p R hR t k
  have he : (9/16-η/4+1/(2*(d : ℝ)))*d=(9/16-η/4)*(d : ℝ)+1/2 := by
    field_simp
  rw [he]
  exact hh

theorem IsolationGood.rounded_floor (η : ℝ) (hη : 0≤η) (p : ZMod d → Bool)
    (hp : IsolationGood η p) (b : ℕ) (hb : 0<b) (R : Finset (ZMod d)) (hR : R.card=2)
    (t : ℕ → ZMod d) (k : ℕ) :
    9/16-η/4-1/(2*(d : ℝ))≤(⌊isolationCertificate p b R t k⌋ : ℝ)/((b : ℝ)*d^2) := by
  have hd0 : (0 : ℝ)<d := by exact_mod_cast NeZero.pos d
  have hb1 : (1 : ℝ)≤b := by exact_mod_cast hb
  have hd1 : (1 : ℝ)≤d := by exact_mod_cast NeZero.pos d
  have hN : (0 : ℝ)<(b : ℝ)*d^2 := by positivity
  have hh := hp.normalized_floor η hη p b hb R hR t k
  have hfloor := floor_normalized_lower (isolationCertificate p b R t k)
    (9/16-η/4+1/(2*(d : ℝ))) ((b : ℝ)*d^2) hN ((le_div_iff₀ hN).mp hh)
  have hsmall : 1/((b : ℝ)*d^2)≤1/(d : ℝ) := by
    apply one_div_le_one_div_of_le hd0
    nlinarith [mul_le_mul_of_nonneg_right hb1 (sq_nonneg (d : ℝ))]
  have he : 1/(2*(d : ℝ))+1/(2*(d : ℝ))=1/(d : ℝ) := by ring
  linarith

theorem isolation_rate_probability (η : ℝ) (hη : 0≤η) :
    prob (fun p : ZMod d → Bool => ¬∀ (b : ℕ), 0<b → ∀ (R : Finset (ZMod d)), R.card=2 →
      ∀ (t : ℕ → ZMod d) (k : ℕ),
        9/16-η/4+1/(2*(d : ℝ))≤ isolationCertificate p b R t k/((b : ℝ)*d^2)) ≤
      ((d : ℝ)-1)*Real.exp (-2*η^2*d/9) := by
  apply (prob_mono ?_).trans (isolation_bad_probability η hη)
  intro p hp hgood
  exact hp (hgood.normalized_floor η hη p)

theorem EqualityGood.direct_certificate {κ : Type*} [Fintype κ] [Nonempty κ]
    (η : ℝ) (hη : 0≤η) (p : ZMod d → κ) (hp : EqualityGood η p)
    (b : ℕ) (Δ : Finset (ZMod d)) (hΔ : Δ.Nonempty) :
    (b : ℝ)*d^2*(1-Real.sqrt ((1/(Fintype.card κ : ℝ)+η)/2))≤directCertificate p b Δ := by
  rw [directCertificate_eq_gain p b Δ hΔ]
  exact mul_le_mul_of_nonneg_left (sub_le_sub_left (hp.direct_gain η hη p Δ hΔ) 1) (by positivity)

theorem direct_certificate_probability {κ : Type*} [Fintype κ] [Nonempty κ]
    (η : ℝ) (hη : 0≤η) :
    prob (fun p : ZMod d → κ => ¬∀ (b : ℕ) (Δ : Finset (ZMod d)), Δ.Nonempty →
      (b : ℝ)*d^2*(1-Real.sqrt ((1/(Fintype.card κ : ℝ)+η)/2))≤directCertificate p b Δ) ≤
      ((d : ℝ)-1)*Real.exp (-η^2*d/2) := by
  apply (prob_mono ?_).trans (equality_bad_probability (κ := κ) η hη)
  intro p hp hgood
  exact hp (hgood.direct_certificate η hη p)

theorem ChangeGood.two_thirds_floor (p : ZMod d → Bool) (hp : ChangeGood (1/6) p)
    (b : ℕ) (Δ : Finset (ZMod d)) (hΔ : Δ.Nonempty) :
    (2/3)*(b : ℝ)*d^2≤directCertificate p b Δ := by
  have hh := directCertificate_floor_of_changes p b (1/3) (by norm_num)
    (fun s hs => by have hg := hp s hs; norm_num at hg; exact hg) Δ hΔ
  convert hh using 1; ring

theorem two_thirds_probability :
    prob (fun p : ZMod d → Bool => ¬∀ (b : ℕ) (Δ : Finset (ZMod d)), Δ.Nonempty →
      (2/3)*(b : ℝ)*d^2≤directCertificate p b Δ)≤
      ((d : ℝ)-1)*Real.exp (-(d : ℝ)/72) := by
  have hh := change_bad_probability (d := d) (1/6) (by norm_num)
  have he : -(1/6 : ℝ)^2*d/2=-(d : ℝ)/72 := by ring
  rw [he] at hh
  apply (prob_mono ?_).trans hh
  intro p hp hgood
  exact hp (hgood.two_thirds_floor p)

def ComparisonGood (ε : ℝ) (p : ZMod d → Bool) : Prop :=
  SpectrumGood ε p ∧ ChangeGood (1/6) p

theorem comparison_bad_probability (hd : 13<d) (ε : ℝ) (hε : 0≤ε) :
    prob (fun p : ZMod d → Bool => ¬ComparisonGood ε p)≤
      Real.exp (-128*ε^2*d/529)+((d : ℝ)-1)*Real.exp (-(d : ℝ)/72) := by
  have hm := prob_mono (fun (p : ZMod d → Bool) (hp : ¬ComparisonGood ε p) =>
    show ¬SpectrumGood ε p ∨ ¬ChangeGood (1/6) p from not_and_or.mp hp)
  apply (hm.trans (prob_or_le _ _)).trans
  have hc := change_bad_probability (d := d) (1/6) (by norm_num)
  rw [show -(1/6 : ℝ)^2*d/2=-(d : ℝ)/72 by ring] at hc
  exact add_le_add (spectrum_bad_probability hd ε hε) hc

variable {F A : Type*} [Field F] [AddCommGroup A] [Module F A] [FiniteDimensional F A]

/-- One mask event makes the actual source bound strictly smaller than every
actual direct certificate. The finite threshold is explicit. -/
theorem ComparisonGood.strict_direct_comparison (hd : 1<d) (ε : ℝ)
    (hgap : 3/4<(2/3-41473/65536-ε)*(d : ℝ)) {p : ZMod d → Bool}
    (hp : ComparisonGood ε p) {C : Submodule F (State d A)}
    (h : IsSharedCode F p C) (hb : 0<finrank F A)
    (Δ : Finset (ZMod d)) (hΔ : Δ.Nonempty) :
    (finrank F C : ℝ)<directCertificate p (finrank F A) Δ := by
  have hs := SpectrumGood.source_bound hd hp.1 h
  have hc := hp.2.two_thirds_floor p (finrank F A) Δ hΔ
  have hbd : (0 : ℝ)<(d : ℝ)*finrank F A := by positivity
  have hmul := mul_lt_mul_of_pos_right hgap hbd
  nlinarith only [hs,hc,hmul]


/-- Every stated epsilon below the constant gap eventually meets the explicit
finite threshold, including the extra unit needed for integer flooring. -/
theorem eventually_direct_gap (ε : ℝ) (hε : ε<2/3-41473/65536) (a : ℝ) :
    ∀ᶠ d : ℕ in Filter.atTop, a<(2/3-41473/65536-ε)*(d : ℝ) := by
  have hp : 0<(2/3-41473/65536-ε : ℝ) := by linarith
  have hh : Filter.Tendsto (fun d : ℕ => (2/3-41473/65536-ε)*(d : ℝ))
      Filter.atTop Filter.atTop := Filter.Tendsto.const_mul_atTop hp tendsto_natCast_atTop_atTop
  exact hh.eventually_gt_atTop a

/-- A dimension gap greater than one also separates final integer floors. -/
theorem floor_gap (x y : ℝ) (h : x+1<y) : ⌊x⌋<⌊y⌋ := by
  have hx := Int.floor_le x
  have hy := Int.lt_floor_add_one y
  have hh : (⌊x⌋ : ℝ)<(⌊y⌋ : ℝ) := by linarith
  exact_mod_cast hh

theorem infimum_floor (S : Set ℝ) (hS : S.Nonempty) (c : ℝ) (hc : ∀ x∈S, c≤x) :
    c≤sInf S := le_csInf hS hc

end SharedDecoders.CapacityMaskProbability
