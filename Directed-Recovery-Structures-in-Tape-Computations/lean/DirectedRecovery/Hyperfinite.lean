import DirectedRecovery.IncidenceSeparator

/-!
# Hyperfinite half rate with varying alphabets

Uniform hyperfiniteness chooses a component-size bound after the deletion
fraction is fixed. Paired-distance separation is then applied at that one
fixed radius. The alphabet, code, and coordinate type may all vary with the
sequence index. No degree hypothesis or uniformity in the radius is imposed.
-/

namespace DirectedRecovery

open Classical Filter MotionDepthCodes
open scoped Topology
set_option autoImplicit false

universe u v
variable {V : ℕ → Type u} [∀ n, DecidableEq (V n)] [∀ n, Fintype (V n)]

/-- The pointwise paired-distance condition: the proportion of prescribed
pairs at any fixed positive radius tends to zero. -/
def HasPairedDistanceSeparation (N : (n : ℕ) → V n → Finset (V n)) : Prop :=
  ∀ K : ℕ, 0 < K → Tendsto
    (fun n => ((shortPairedCoordinates (N n) K).card : ℝ) / Fintype.card (V n))
    atTop (𝓝 0)

/-- Uniform hyperfiniteness of the actual paired incidence graphs: after
fixing a positive deletion fraction, one component-size bound works for
all sufficiently large indices. The deleted objects are incidence ports. -/
def UniformlyHyperfinite (N : (n : ℕ) → V n → Finset (V n)) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ K : ℕ, 0 < K ∧ ∀ᶠ n in atTop,
    ∃ Z : Finset (V n ⊕ V n),
      (Z.card : ℝ) ≤ 2 * η * Fintype.card (V n) ∧ HasSmallPortComponents (N n) Z K

/-- Normalized logarithmic code size. For nonempty coordinate sets this is
the usual rate; its value at zero coordinates is irrelevant to a sequence
whose coordinate sizes tend to infinity. -/
noncomputable def storageCodeRate {W A : Type*} [Fintype W] [Fintype A]
    (C : Finset (W → A)) : ℝ :=
  Real.logb (Fintype.card A) C.card / Fintype.card W

variable {A : ℕ → Type v} [∀ n, Fintype (A n)]

/-- The finite separator estimate gives an eventual half-rate-plus-epsilon
bound for arbitrary varying finite alphabets and nonempty storage codes. -/
theorem hyperfinite_rate_eventually_le
    (N : (n : ℕ) → V n → Finset (V n))
    (hsize : Tendsto (fun n => Fintype.card (V n)) atTop atTop)
    (hhyper : UniformlyHyperfinite N) (hpair : HasPairedDistanceSeparation N)
    (C : (n : ℕ) → Finset (V n → A n))
    (hC : ∀ n, IsStorageCode (N n) (C n)) (hne : ∀ n, (C n).Nonempty)
    (ha : ∀ n, 1 < (Fintype.card (A n) : ℝ))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, storageCodeRate (C n) ≤ (1 : ℝ) / 2 + ε := by
  obtain ⟨K, hK, hZ⟩ := hhyper (ε / 2) (by linarith)
  have hshort : ∀ᶠ n in atTop,
      ((shortPairedCoordinates (N n) K).card : ℝ) / Fintype.card (V n) < ε :=
    (tendsto_order.mp (hpair K hK)).2 ε hε
  have hpos : ∀ᶠ n in atTop, 0 < Fintype.card (V n) :=
    hsize.eventually (eventually_gt_atTop 0)
  filter_upwards [hZ, hshort, hpos] with n hnZ hnshort hnpos
  obtain ⟨Z, hZcard, hcomp⟩ := hnZ
  have ha0 : 0 < Fintype.card (A n) := by exact_mod_cast (lt_trans zero_lt_one (ha n))
  let : Nonempty (A n) := Fintype.card_pos_iff.mp ha0
  have hbound := storageCode_separator_log_bound (N n) Z K hcomp (ha n) (C n) (hC n) (hne n)
  have hnR : (0 : ℝ) < Fintype.card (V n) := by exact_mod_cast hnpos
  have hshort' : ((shortPairedCoordinates (N n) K).card : ℝ) <
      ε * Fintype.card (V n) := (div_lt_iff₀ hnR).mp hnshort
  unfold storageCodeRate
  apply (div_le_iff₀ hnR).mpr
  nlinarith

/-- Uniform hyperfiniteness and paired-distance separation imply a half-rate
limsup for every sequence of finite alphabets of size at least two and every
sequence of nonempty storage codes. -/
theorem hyperfinite_rate_limsup_le_half
    (N : (n : ℕ) → V n → Finset (V n))
    (hsize : Tendsto (fun n => Fintype.card (V n)) atTop atTop)
    (hhyper : UniformlyHyperfinite N) (hpair : HasPairedDistanceSeparation N)
    (C : (n : ℕ) → Finset (V n → A n))
    (hC : ∀ n, IsStorageCode (N n) (C n)) (hne : ∀ n, (C n).Nonempty)
    (ha : ∀ n, 1 < (Fintype.card (A n) : ℝ)) :
    Filter.limsup (fun n => storageCodeRate (C n)) atTop ≤ (1 : ℝ) / 2 := by
  have hnonneg : ∀ n, 0 ≤ storageCodeRate (C n) := by
    intro n
    apply div_nonneg
    · exact Real.logb_nonneg (ha n) (by exact_mod_cast (hne n).card_pos)
    · exact Nat.cast_nonneg _
  have hcob : IsCoboundedUnder (· ≤ ·) atTop (fun n => storageCodeRate (C n)) :=
    Filter.isCoboundedUnder_le_of_le _ hnonneg
  apply le_of_forall_pos_le_add
  intro ε hε
  exact Filter.limsup_le_of_le hcob
    (hyperfinite_rate_eventually_le N hsize hhyper hpair C hC hne ha ε hε)

end DirectedRecovery
