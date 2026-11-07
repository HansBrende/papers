import TapeStorageRates.PaidClassesCompiler
import TapeStorageRates.PaidClassesTransfer
import TapeStorageRates.PacketFamily
import TapeStorageRates.RateGap

/-! # Native transposition forces binary storage codes with rates approaching one -/

namespace TapeStorageRates

open Filter MergeDepth PaidClasses PaidInputs PacketCompiler

set_option autoImplicit false

private theorem witnesses_of_native_classes (M : Transpose.TM) (c : ℝ) (A : ℕ)
    (hclasses : ∀ s : ℕ, 0 < s → HasPacketClasses M.k s (recordBits M * s) A
      (11 * (batchCoefficient c : ℝ))) : RateWitnesses M.k := by
  have hb : 1 ≤ batchCoefficient c := by unfold batchCoefficient; omega
  apply rates_of_packet_classes M.k A (recordBits M)
    (c := 11 * (batchCoefficient c : ℝ)) (β := fun s => recordBits M * s)
  · have hb' : 1 ≤ (batchCoefficient c : ℝ) := by exact_mod_cast hb
    linarith
  · filter_upwards [eventually_ge_atTop 1] with s hs
    exact ⟨Nat.mul_pos (recordBits_pos M) hs, le_rfl⟩
  · exact (eventually_ge_atTop 1).mono fun s hs => hclasses s hs

/-- The packet transfer holds at any cofinally growing dimensions and entry widths
on which success sets have rates approaching one. -/
theorem rate_witnesses_of_growing_widths (M : Transpose.TM) {c : ℝ} (hc : 0 < c)
    (hgood : GrowingWidthSuccess M c) : RateWitnesses M.k :=
  witnesses_of_native_classes M c (descriptorBill M.k (batchCoefficient c) + 1)
    (fun _ hs => hasPacketClasses_of_growing_widths hs (compiler M hc.le hs) hgood)

/-- Canonical near-full success supplies one instance of the growing-width hypothesis. -/
theorem rate_witnesses_of_near_full (M : Transpose.TM) {c : ℝ} (hc : 0 < c)
    (hgood : NearFullSuccess M c) : RateWitnesses M.k :=
  rate_witnesses_of_growing_widths M hc hgood.growing_widths

/-- **Theorem A at the actual tape count.** At each large cap a fixed successful machine
produces a family with the stated limiting lower rate. -/
theorem rate_witnesses_of_full (M : Transpose.TM) {c : ℝ} (hc : 0 < c)
    (hgood : ∀ d₀ : ℕ, ∃ d ≥ d₀, TransposesAt M d c) : RateWitnesses M.k :=
  witnesses_of_native_classes M c (descriptorBill M.k (batchCoefficient c))
    (fun _ hs => hasPacketClasses_of_full hs (compiler M hc.le hs) hgood)

/-- The exact quantitative target originally stated for this paper. -/
theorem quantitative_transfer : QuantitativeTarget := fun M _ hc hgood =>
  (rate_witnesses_of_full M hc hgood).mono (le_max_right 1 M.k)

/-- The corresponding qualitative conclusion for Paper 1's frozen (T). -/
theorem qualitative_transfer : QualitativeTarget := qualitative_of_quantitative quantitative_transfer

/-- The fixed-tape degree-gap criterion for the actual tape model. -/
theorem gap_excludes_transposition {ρ : ℕ → ℝ} (hgap : FamilyRateGap ρ) {k : ℕ}
    (hunbounded : ∀ K : ℝ, ∃ᶠ Δ : ℕ in atTop, K < ρ Δ / deficitScale k Δ)
    (M : Transpose.TM) (htapes : M.k ≤ k) (c : ℝ) (hc : 0 < c) :
    ¬ (∀ d₀ : ℕ, ∃ d ≥ d₀, TransposesAt M d c) :=
  fun h => hgap.no_witnesses hunbounded ((rate_witnesses_of_full M hc h).mono htapes)

/-- The all-powers gap excludes linear-time transposition with any fixed finite tape count. -/
theorem all_powers_exclude_transposition {ρ : ℕ → ℝ} (hgap : FamilyRateGap ρ)
    (h : ∀ a : ℝ, 0 < a → ∀ K : ℝ, ∃ᶠ Δ : ℕ in atTop, K < ρ Δ * degreeLogLog Δ ^ a)
    (M : Transpose.TM) (c : ℝ) (hc : 0 < c) :
    ¬ (∀ d₀ : ℕ, ∃ d ≥ d₀, TransposesAt M d c) :=
  no_transposer_of_all_powers quantitative_transfer hgap h M c hc

/-- Sparse caps suffice to bound success exponentially throughout the two-parameter
region of sufficiently large dimensions and widths. At the caps in the test it suffices
to bound lower limiting rates. -/
theorem exponentially_small_at_widths_of_sparse_gap {ρ : ℕ → ℝ} {k : ℕ}
    (hsparse : ∀ K : ℝ, ∃ᶠ Δ : ℕ in atTop, K < ρ Δ / deficitScale k Δ ∧
      ∀ F : SeparatedBinaryFamily Δ,
        liminf (fun i => DirectedRecovery.storageCodeRate (F.code i)) atTop ≤ 1-ρ Δ)
    (M : Transpose.TM) (htapes : M.k ≤ k) {c : ℝ} (hc : 0 < c) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ n : ℕ, ∀ d ≥ n, ∀ b ≥ n,
      ((successfulInputsAt M c d b).card : ℝ) / (2:ℝ)^(d*d*b) ≤ (2:ℝ)^(-γ*(d*d*b : ℕ)) :=
  exponentially_small_of_not_growing_widths fun h =>
    no_witnesses_of_sparse_rate_bounds hsparse ((rate_witnesses_of_growing_widths M hc h).mono htapes)

/-- At any tape cap with a sufficiently large rate gap, every fixed machine below the cap
has exponentially small uniform-input success probability at all sufficiently large dimensions. -/
theorem exponentially_small_of_gap {ρ : ℕ → ℝ} (hgap : FamilyRateGap ρ) {k : ℕ}
    (hunbounded : ∀ K : ℝ, ∃ᶠ Δ : ℕ in atTop, K < ρ Δ / deficitScale k Δ)
    (M : Transpose.TM) (htapes : M.k ≤ k) {c : ℝ} (hc : 0 < c) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ d : ℕ in atTop,
      ((successfulInputs M c d).card : ℝ) / (2 : ℝ) ^ canonicalLength d ≤
        (2 : ℝ) ^ (-γ * canonicalLength d) := by
  obtain ⟨γ,hγ,n,h⟩ := exponentially_small_at_widths_of_sparse_gap (hgap.sparse_bounds hunbounded) M htapes hc
  exact ⟨γ,hγ,((eventually_ge_atTop n).and (tendsto_entryBits.eventually_ge_atTop n)).mono
    fun d ⟨hd,hb⟩ => h d hd _ hb⟩

end TapeStorageRates
