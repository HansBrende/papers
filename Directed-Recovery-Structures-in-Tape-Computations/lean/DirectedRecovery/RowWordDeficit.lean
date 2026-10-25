import DirectedRecovery.ThresholdBuckets
import DirectedRecovery.IndependentRectangle
import DirectedRecovery.StorageCode
import LeanMachine.CanonicalBuckets
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# From an actual row-word cover to a finite coding deficit

The starting row of every word is the physical output row of the receiver;
the ending row is the raw row of the supplier. The occupied bucket relation
is therefore transposed before the independent-rectangle theorem is applied.

These finite and asymptotic implications start from a supplied row-word cover
of the actual recovery relation. They do not assert the native machine's
row-word extraction or its asymptotic exception estimate.
-/

namespace DirectedRecovery

open Classical Finset MotionDepthCodes ThresholdPullback
open LeanMachine.ThresholdPullback
open Filter
open scoped BigOperators Topology
set_option autoImplicit false

/-- The exact independent-set lower bound obtained from the threshold
exception budget and the rectangle argument. Natural subtraction represents
the displayed maximum with zero. -/
def rowWordIndependentLower (d b K r ell z : ℕ) : ℕ :=
  b * (2 * K + 1) * (d / (4 * K)) ^ 2 -
    b * d * min d (K * (4 * K - 1) * ((2 * r + 1) ^ (ell + 1) - 1)) - z

/-- A finite actual row-word cover yields one independent coordinate set
before any induced code or alphabet is chosen. -/
theorem row_word_cover_independent {d b K : ℕ} (hK : 0 < K) (r ell z : ℕ)
    (bucket : Fin d → Fin (4 * K)) (hbucket : Monotone bucket)
    (hsize : ∀ a, d / (4 * K) ≤ (univ.filter (fun i => bucket i = a)).card)
    (w : Fin K → Word d d) (hmaps : ∀ i, (w i).maps ≤ ell)
    (R : Fin K → Fin d → Fin d → Prop)
    (hR : ∀ i x y, R i x y → (w i).Rel r x y)
    (N : IndependentRectangle.Coordinate d b → Finset (IndependentRectangle.Coordinate d b))
    (Z : Finset (IndependentRectangle.Coordinate d b)) (hZ : Z.card ≤ z)
    (hcover : ∀ p q, p ∉ Z → q ∉ Z → p ∈ N q → ∃ i, R i q.2.1 p.1) :
    ∃ I : Finset (IndependentRectangle.Coordinate d b),
      IsIndependent N I ∧ rowWordIndependentLower d b K r ell z ≤ I.card := by
  obtain ⟨T, hT, _, _, hocc⟩ := finite_threshold_pullback r ell w hmaps R hR
    bucket bucket hbucket hbucket
  let Eout := univ.biUnion (fun i => occupiedPairs (R i) T bucket bucket)
  let E := Eout.image Prod.swap
  have hE : E.card ≤ K * (8 * K - 1) := by
    apply Finset.card_image_le.trans
    simpa only [show 2 * (4 * K) = 8 * K by omega] using hocc
  have hrectCover : ∀ p q : IndependentRectangle.Coordinate d b,
      p ∉ Z → q ∉ Z → p.1 ∉ (∅ : Finset (Fin d)) → q.2.1 ∉ T →
      p ∈ N q → (bucket p.1, bucket q.2.1) ∈ E := by
    intro p q hpZ hqZ _ hqT hpN
    obtain ⟨i, hi⟩ := hcover p q hpZ hqZ hpN
    apply Finset.mem_image.mpr
    refine ⟨(bucket q.2.1, bucket p.1), ?_, rfl⟩
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _,
      mem_occupiedPairs_of_rel bucket bucket hqT hi⟩
  obtain ⟨I, hI, hcard⟩ := IndependentRectangle.independent_rectangle hK
    bucket bucket hsize hsize E hE ∅ T Z N hrectCover
  refine ⟨I, ?_, ?_⟩
  · intro q hq p hp hpI
    exact hI q hq p hpI hp
  · simp only [Finset.card_empty, zero_add] at hcard
    have hmul := Nat.mul_le_mul_left (b * d) hT
    unfold rowWordIndependentLower
    omega

/-- A lower bound on one independent set gives the exact paid deficit on
every induced coordinate set. -/
theorem independent_lower_induced_code_bound {V α : Type*}
    [Fintype V] [DecidableEq V] [Fintype α] [Nonempty α]
    {N : V → Finset V} {I : Finset V} (hI : IsIndependent N I)
    {L : ℕ} (hL : L ≤ I.card) (Q : Finset V)
    {C : Finset (Q → α)} (hC : IsStorageCode (inducedNeighborhood N Q) C) :
    C.card ≤ Fintype.card α ^ (Q.card - (L - Qᶜ.card)) := by
  have hsub : I \ Q ⊆ Qᶜ := by
    intro p hp
    exact Finset.mem_compl.mpr (Finset.mem_sdiff.mp hp).2
  have hpart : (I \ Q).card + (I ∩ Q).card = I.card := Finset.card_sdiff_add_card_inter I Q
  have hsubcard := Finset.card_le_card hsub
  have hkeep : L - Qᶜ.card ≤ (I ∩ Q).card := by omega
  exact (induced_storageCode_card_le_of_independent hI Q hC).trans
    (Nat.pow_le_pow_right Fintype.card_pos (Nat.sub_le_sub_left hkeep Q.card))

/-- The logarithmic independent-set deficit, with ordinary real subtraction
outside the nonnegative integer deficit. -/
theorem independent_lower_induced_code_log_bound {V α : Type*}
    [Fintype V] [DecidableEq V] [Fintype α] [Nonempty α]
    {N : V → Finset V} {I : Finset V} (hI : IsIndependent N I)
    {L : ℕ} (hL : L ≤ I.card) (Q : Finset V)
    {C : Finset (Q → α)} (hC : IsStorageCode (inducedNeighborhood N Q) C)
    (hne : C.Nonempty) (ha : 1 < (Fintype.card α : ℝ)) :
    Real.logb (Fintype.card α) C.card ≤ (Q.card : ℝ) - ((L - Qᶜ.card : ℕ) : ℝ) := by
  have hcard := independent_lower_induced_code_bound hI hL Q hC
  have hdef : L - Qᶜ.card ≤ Q.card := by
    have hIcard := Finset.card_le_univ I
    have hQ := Finset.card_add_card_compl Q
    omega
  have hpow : (C.card : ℝ) ≤
      (Fintype.card α : ℝ) ^ ((Q.card : ℝ) - ((L - Qᶜ.card : ℕ) : ℝ)) := by
    rw [← Nat.cast_sub hdef, Real.rpow_natCast]
    exact_mod_cast hcard
  exact (Real.logb_le_iff_le_rpow ha (by exact_mod_cast hne.card_pos)).mpr hpow

/-- The exact finite code-deficit consequence of an actual row-word cover.
The single independent set is constructed from the full relation; no code
extension, linearity, degree, or genie-price premise is added. -/
theorem row_word_cover_induced_code_log_bound {d b K : ℕ} (hK : 0 < K) (r ell z : ℕ)
    (bucket : Fin d → Fin (4 * K)) (hbucket : Monotone bucket)
    (hsize : ∀ a, d / (4 * K) ≤ (univ.filter (fun i => bucket i = a)).card)
    (w : Fin K → Word d d) (hmaps : ∀ i, (w i).maps ≤ ell)
    (R : Fin K → Fin d → Fin d → Prop)
    (hR : ∀ i x y, R i x y → (w i).Rel r x y)
    (N : IndependentRectangle.Coordinate d b → Finset (IndependentRectangle.Coordinate d b))
    (Z : Finset (IndependentRectangle.Coordinate d b)) (hZ : Z.card ≤ z)
    (hcover : ∀ p q, p ∉ Z → q ∉ Z → p ∈ N q → ∃ i, R i q.2.1 p.1)
    {α : Type*} [Fintype α] [Nonempty α]
    (Q : Finset (IndependentRectangle.Coordinate d b))
    (C : Finset (Q → α)) (hC : IsStorageCode (inducedNeighborhood N Q) C)
    (hne : C.Nonempty) (ha : 1 < (Fintype.card α : ℝ)) :
    Real.logb (Fintype.card α) C.card ≤ (Q.card : ℝ) -
      ((rowWordIndependentLower d b K r ell z - Qᶜ.card : ℕ) : ℝ) := by
  obtain ⟨I, hI, hL⟩ := row_word_cover_independent hK r ell z bucket hbucket hsize
    w hmaps R hR N Z hZ hcover
  exact independent_lower_induced_code_log_bound hI hL Q hC hne ha

/-- A completely specified bucket choice removes the partition-selection
premise from the exact finite row-word-to-code implication. -/
theorem row_word_cover_code_log_bound {d b K : ℕ} (hK : 0 < K) (hd : 4 * K ≤ d)
    (r ell z : ℕ) (w : Fin K → Word d d) (hmaps : ∀ i, (w i).maps ≤ ell)
    (R : Fin K → Fin d → Fin d → Prop)
    (hR : ∀ i x y, R i x y → (w i).Rel r x y)
    (N : IndependentRectangle.Coordinate d b → Finset (IndependentRectangle.Coordinate d b))
    (Z : Finset (IndependentRectangle.Coordinate d b)) (hZ : Z.card ≤ z)
    (hcover : ∀ p q, p ∉ Z → q ∉ Z → p ∈ N q → ∃ i, R i q.2.1 p.1)
    {α : Type*} [Fintype α] [Nonempty α]
    (Q : Finset (IndependentRectangle.Coordinate d b))
    (C : Finset (Q → α)) (hC : IsStorageCode (inducedNeighborhood N Q) C)
    (hne : C.Nonempty) (ha : 1 < (Fintype.card α : ℝ)) :
    Real.logb (Fintype.card α) C.card ≤ (Q.card : ℝ) -
      ((rowWordIndependentLower d b K r ell z - Qᶜ.card : ℕ) : ℝ) := by
  have hB : 0 < 4 * K := by omega
  exact row_word_cover_induced_code_log_bound hK r ell z
    (LeanMachine.CanonicalBuckets.bucket hB)
    (LeanMachine.CanonicalBuckets.bucket_monotone hB)
    (LeanMachine.CanonicalBuckets.bucket_fibre_card hB hd)
    w hmaps R hR N Z hZ hcover Q C hC hne ha

/-- The fixed threshold budget; only this lower-order coefficient depends
on the band radius and word length. -/
def rowWordThresholdBudget (K r ell : ℕ) : ℕ :=
  K * (4 * K - 1) * ((2 * r + 1) ^ (ell + 1) - 1)

/-- The independent-set lower bound has leading coefficient at least
`1/(8*K)`, uniformly in the fixed radius and word length. -/
theorem rowWordIndependentLower_leading {d b K r ell z : ℕ} (hK : 0 < K) :
    (1 / (8 * (K : ℝ))) * ((d : ℝ) ^ 2 * b) ≤
      (rowWordIndependentLower d b K r ell z : ℝ) +
        ((rowWordThresholdBudget K r ell : ℝ) + 1) * d * b + z := by
  let q := d / (4 * K)
  let s := d % (4 * K)
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg _
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have hs : (s : ℝ) ≤ 4 * K := by
    exact_mod_cast (Nat.mod_lt d (by omega : 0 < 4 * K)).le
  have hd : (d : ℝ) = 4 * K * q + s := by
    exact_mod_cast (Nat.div_add_mod d (4 * K)).symm
  have hcross := mul_nonneg (by positivity : (0 : ℝ) ≤ 8 * K * q) (sub_nonneg.mpr hs)
  have hsquare := mul_nonneg hs0 (by linarith : (0 : ℝ) ≤ 8 * K - s)
  have hfloor : (d : ℝ) ^ 2 ≤ 16 * (K : ℝ) ^ 2 * (q : ℝ) ^ 2 + 8 * K * d := by
    nlinarith
  have hlead : (d : ℝ) ^ 2 / (8 * K) ≤ (2 * K + 1) * (q : ℝ) ^ 2 + d := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 8 * K)).mpr
    nlinarith [sq_nonneg (q : ℝ)]
  have hleadb := mul_le_mul_of_nonneg_right hlead (by positivity : (0 : ℝ) ≤ b)
  have hnat : b * (2 * K + 1) * q ^ 2 ≤ rowWordIndependentLower d b K r ell z +
      b * d * rowWordThresholdBudget K r ell + z := by
    have ht : min d (rowWordThresholdBudget K r ell) ≤ rowWordThresholdBudget K r ell :=
      Nat.min_le_right _ _
    have hm := Nat.mul_le_mul_left (b * d) ht
    dsimp [rowWordIndependentLower, rowWordThresholdBudget, q] at *
    omega
  have hreal : (b : ℝ) * (2 * K + 1) * (q : ℝ) ^ 2 ≤
      rowWordIndependentLower d b K r ell z + (b : ℝ) * d * rowWordThresholdBudget K r ell + z := by
    exact_mod_cast hnat
  have heq : (1 / (8 * (K : ℝ))) * ((d : ℝ) ^ 2 * b) =
      ((d : ℝ) ^ 2 / (8 * K)) * b := by ring
  rw [heq]
  nlinarith

/-- The explicit lower-order error. Its depth dependence is confined to
the fixed threshold budget and the supplied exceptional-coordinate count. -/
def rowWordDeficitError (d b K r ell z : ℕ) : ℝ :=
  ((rowWordThresholdBudget K r ell : ℝ) + 1) * d * b + z

/-- The full finite deficit, with coefficient depending only on the word
count. Removed induced coordinates are paid once, separately from the error. -/
theorem row_word_cover_code_gap {d b K : ℕ} (hK : 0 < K) (hd : 4 * K ≤ d)
    (r ell z : ℕ) (w : Fin K → Word d d) (hmaps : ∀ i, (w i).maps ≤ ell)
    (R : Fin K → Fin d → Fin d → Prop)
    (hR : ∀ i x y, R i x y → (w i).Rel r x y)
    (N : IndependentRectangle.Coordinate d b → Finset (IndependentRectangle.Coordinate d b))
    (Z : Finset (IndependentRectangle.Coordinate d b)) (hZ : Z.card ≤ z)
    (hcover : ∀ p q, p ∉ Z → q ∉ Z → p ∈ N q → ∃ i, R i q.2.1 p.1)
    {α : Type*} [Fintype α] [Nonempty α]
    (Q : Finset (IndependentRectangle.Coordinate d b))
    (C : Finset (Q → α)) (hC : IsStorageCode (inducedNeighborhood N Q) C)
    (hne : C.Nonempty) (ha : 1 < (Fintype.card α : ℝ)) :
    Real.logb (Fintype.card α) C.card ≤ (Q.card : ℝ) -
      (1 / (8 * (K : ℝ))) * ((d : ℝ) ^ 2 * b) + Qᶜ.card +
      rowWordDeficitError d b K r ell z := by
  have hc := row_word_cover_code_log_bound hK hd r ell z w hmaps R hR
    N Z hZ hcover Q C hC hne ha
  have hl := rowWordIndependentLower_leading (d := d) (b := b) (r := r)
    (ell := ell) (z := z) hK
  have hn : rowWordIndependentLower d b K r ell z ≤
      (rowWordIndependentLower d b K r ell z - Qᶜ.card) + Qᶜ.card := by omega
  have hr : (rowWordIndependentLower d b K r ell z : ℝ) ≤
      ((rowWordIndependentLower d b K r ell z - Qᶜ.card : ℕ) : ℝ) + Qᶜ.card := by
    exact_mod_cast hn
  unfold rowWordDeficitError
  linarith

/-- The explicit error is `o(d²b)` for every positive, possibly growing,
entry width. No bound on `b` and no uniformity in `r` or `ell` is imposed. -/
theorem rowWordDeficitError_normalized_tendsto (K r ell : ℕ)
    (d b z : ℕ → ℕ) (hd : Tendsto d atTop atTop) (hb : ∀ n, 1 ≤ b n)
    (hz : Tendsto (fun n => (z n : ℝ) / ((d n : ℝ) ^ 2 * b n)) atTop (𝓝 0)) :
    Tendsto (fun n => rowWordDeficitError (d n) (b n) K r ell (z n) /
      ((d n : ℝ) ^ 2 * b n)) atTop (𝓝 0) := by
  have hfirst := (tendsto_const_div_atTop_nhds_zero_nat
    ((rowWordThresholdBudget K r ell : ℝ) + 1)).comp hd
  have hsum := hfirst.add hz
  simp only [zero_add] at hsum
  apply hsum.congr'
  filter_upwards [hd.eventually (eventually_ge_atTop 1)] with n hn
  have hd0 : (d n : ℝ) ≠ 0 := by exact_mod_cast (by omega : d n ≠ 0)
  have hb0 : (b n : ℝ) ≠ 0 := by exact_mod_cast (by have := hb n; omega : b n ≠ 0)
  simp only [Function.comp_apply, rowWordDeficitError]
  field_simp

/-- The precise finite structural premise supplied by native row-word
extraction. Both endpoints outside the exceptional set must be covered,
with the word directed from physical output row to raw supplier row. -/
def HasRowWordCover (d b K r ell z : ℕ)
    (N : IndependentRectangle.Coordinate d b → Finset (IndependentRectangle.Coordinate d b)) : Prop :=
  ∃ (w : Fin K → Word d d), (∀ i, (w i).maps ≤ ell) ∧
    ∃ (R : Fin K → Fin d → Fin d → Prop),
      (∀ i x y, R i x y → (w i).Rel r x y) ∧
      ∃ (Z : Finset (IndependentRectangle.Coordinate d b)), Z.card ≤ z ∧
        ∀ p q, p ∉ Z → q ∉ Z → p ∈ N q → ∃ i, R i q.2.1 p.1

/-- From actual row-word covers with sublinear exceptional counts, the
depth-independent deficit holds uniformly over induced subsets and finite
alphabets. The error is chosen before the alphabet, subset, and code. -/
theorem row_word_cover_asymptotic_code_gap {K : ℕ} (hK : 0 < K) (r ell : ℕ)
    (d b z : ℕ → ℕ) (hd : Tendsto d atTop atTop) (hb : ∀ n, 1 ≤ b n)
    (hz : Tendsto (fun n => (z n : ℝ) / ((d n : ℝ) ^ 2 * b n)) atTop (𝓝 0))
    (N : ∀ n, IndependentRectangle.Coordinate (d n) (b n) →
      Finset (IndependentRectangle.Coordinate (d n) (b n)))
    (hcover : ∀ᶠ n in atTop, HasRowWordCover (d n) (b n) K r ell (z n) (N n)) :
    ∃ e : ℕ → ℝ,
      Tendsto (fun n => e n / ((d n : ℝ) ^ 2 * b n)) atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, ∀ (α : Type*) [Fintype α] [Nonempty α]
        (Q : Finset (IndependentRectangle.Coordinate (d n) (b n)))
        (C : Finset (Q → α)),
        IsStorageCode (inducedNeighborhood (N n) Q) C → C.Nonempty →
        1 < (Fintype.card α : ℝ) →
        Real.logb (Fintype.card α) C.card ≤ (Q.card : ℝ) -
          (1 / (8 * (K : ℝ))) * ((d n : ℝ) ^ 2 * b n) + Qᶜ.card + e n := by
  refine ⟨fun n => rowWordDeficitError (d n) (b n) K r ell (z n),
    rowWordDeficitError_normalized_tendsto K r ell d b z hd hb hz, ?_⟩
  filter_upwards [hd.eventually (eventually_ge_atTop (4 * K)), hcover] with n hn hcovern
  intro α _ _ Q C hC hne ha
  obtain ⟨w, hmaps, R, hR, Z, hZ, hc⟩ := hcovern
  exact row_word_cover_code_gap hK hn r ell (z n) w hmaps R hR (N n) Z hZ hc Q C hC hne ha

end DirectedRecovery
