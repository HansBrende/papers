import AdaptiveTransfer.ScanLoaderGetters
import AdaptiveTransfer.GetterTail
import AdaptiveTransfer.GetterDensityExistence

/-! A complete success-set bound for the actual paid producer followed by an
arbitrary archive-preserving consumer. Checkpoint labels and getter correctness
are constructed, and the preparation time is part of the source's own cap.
-/

namespace AdaptiveTransfer.ScanLoader

open Transpose MergeDepth NativeRelations

variable {r : ℕ} {S A : Fin r → Type*} {Q B : Type*}
variable (F : (j : Fin r) → S j → Bool → S j)
  (D : (j : Fin r) → S j → Bool → A j) (s₀ : ScanStates S) (q₀ : Q)
  (C : Consumer Q A B)
variable [Fintype Q] [∀ j, Fintype (S j)] [∀ j, Fintype (A j)] [Fintype B]

/-- Fixed scans and a fixed controller have exponentially few timely correct
inputs, uniformly in every positive entry width. The only consumer restriction
is its literal table-level archive preservation. Zero archives are included. -/
theorem native_scan_loader_tail (hC : PreservesArchives C) (a : ℕ) {c : ℝ}
    (ha : 1 ≤ a) (hc : 1 ≤ c)
    (hA : (nativeProducer F D s₀ q₀ C).g + 1 ≤ 2 ^ a) :
    let N := Getter.portRunCap a (r + 1) c
    ∃ d₀ : ℕ, ∀ d, d₀ ≤ d → ∀ b, 1 ≤ b →
      ∀ inputs : Finset (Fin (d * d * b) → Bool),
        (∀ X : inputs, TransposesInput (nativeProducer F D s₀ q₀ C) d b c X.val) →
        (inputs.card : ℝ) < (2 : ℝ) ^ ((1 - returnTailEta N) * (d * d * b : ℕ)) := by
  classical
  let M := nativeProducer F D s₀ q₀ C
  let N := Getter.portRunCap a (r + 1) c
  have hN : 1 ≤ N := by dsimp [N, Getter.portRunCap]; omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  let K := 8 * (r + 1) * N
  have hK : 0 < K := by dsimp [K]; positivity
  let q := M.q + 1
  let z := K * Fintype.card (ScanStates S)
  obtain ⟨γ, hγ, hγhalf, hγbudget⟩ := Getter.exists_getter_density (r + 1) a N (by omega) hN hc
  obtain ⟨d₁, htail⟩ := Getter.native_macroscopic_getter_tail (r + 1) a r
    (by omega) ha hc hγ hγhalf hγbudget
  let d₀ := d₁ + 1 + 64 * N ^ 2 * q + 64 * N * z
  refine ⟨d₀, ?_⟩
  intro d hd b hb inputs hcorrect
  have hd₁ : d₁ ≤ d := by dsimp [d₀] at hd; omega
  have hdpos : 1 ≤ d := by dsimp [d₀] at hd; omega
  let P := d * d * b
  have hdP : d ≤ P := by dsimp [P]; nlinarith
  have hqP : 64 * N ^ 2 * q ≤ P := by
    have hh : 64 * N ^ 2 * q ≤ d := by dsimp [d₀] at hd; omega
    exact hh.trans hdP
  have hzP : 64 * N * z ≤ P := by
    have hh : 64 * N * z ≤ d := by dsimp [d₀] at hd; omega
    exact hh.trans hdP
  have hqbudget : (q : ℝ) ≤ (P : ℝ) / (64 * (N : ℝ) ^ 2) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 64 * (N : ℝ) ^ 2)).mpr
    have hh : (64 : ℝ) * (N : ℝ) ^ 2 * q ≤ P := by exact_mod_cast hqP
    nlinarith
  have hzbudget : (z : ℝ) ≤ (P : ℝ) / (64 * (N : ℝ)) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 64 * (N : ℝ))).mpr
    have hh : (64 : ℝ) * N * z ≤ P := by exact_mod_cast hzP
    nlinarith
  let R := P / K
  have hcover : P ≤ (R + 1) * K := macroscopic_checkpoint_cover hK
  have hq : (M.q + 1) * Fintype.card Unit ≤ 2 ^ q := by
    simpa only [Fintype.card_unit, Nat.mul_one] using (Nat.lt_two_pow_self (n := q)).le
  have hz : Fintype.card (SpatialLabel S K) ≤ 2 ^ z := by
    rw [spatialLabel_card]
    calc
      _ ≤ (2 ^ Fintype.card (ScanStates S)) ^ K :=
        Nat.pow_le_pow_left (Nat.lt_two_pow_self.le) K
      _ = 2 ^ z := by rw [← pow_mul]; congr 1; exact Nat.mul_comm _ _
  apply htail d hd₁ b hb M rfl Unit (SpatialLabel S K) q z R hq hz hA hqbudget hzbudget le_rfl
    (archiveObserver F D s₀ q₀ C R) (fun _ => nativeArchiveGetters F D s₀ q₀ C P R K) inputs hcorrect
  intro X
  refine ⟨(0 : Fin (r + 1)), spatialLabel F s₀ R K (List.ofFn X.val), ?_⟩
  rw [nativeArchiveGetters_zero_errors F D s₀ q₀ C hC hcover _ List.length_ofFn]
  simp only [Finset.card_empty, Nat.zero_le]

/-- The finite alphabet automatically supplies an admissible bit budget, so
the unparameterized archive-consumer statement needs no resource premise. -/
theorem native_scan_loader_exponential (hC : PreservesArchives C) {c : ℝ} (hc : 1 ≤ c) :
    ∃ η : ℝ, 0 < η ∧ ∃ d₀ : ℕ, ∀ d, d₀ ≤ d → ∀ b, 1 ≤ b →
      ∀ inputs : Finset (Fin (d * d * b) → Bool),
        (∀ X : inputs, TransposesInput (nativeProducer F D s₀ q₀ C) d b c X.val) →
        (inputs.card : ℝ) < (2 : ℝ) ^ ((1 - η) * (d * d * b : ℕ)) := by
  let a := (nativeProducer F D s₀ q₀ C).g + 1
  let N := Getter.portRunCap a (r + 1) c
  have hN : 1 ≤ N := by dsimp [N, Getter.portRunCap]; omega
  refine ⟨returnTailEta N, returnTailEta_pos hN, ?_⟩
  exact native_scan_loader_tail F D s₀ q₀ C hC a (by dsimp [a]; omega) hc Nat.lt_two_pow_self.le

end AdaptiveTransfer.ScanLoader
