import AdaptiveTransfer.ReferenceBudgetRates
import AdaptiveTransfer.EnlargedTail
import AdaptiveTransfer.NativeTimelyData

/-! Reference and cache tails conditional on the actual common compiler.
Only the native simulation and its literal finite state/label bill are input.
The final controller budgets, output correctness and factor-two success bound
are derived. This module does not construct a handoff or cache transition table.
-/

namespace AdaptiveTransfer
open Transpose Transpose.Tape MergeDepth NativeRelations Finset Getter
attribute [local instance] Classical.propDecidable

universe u v w

namespace Enlarged.System
variable {Q : Type u} {Γ : Type v} {Λ : Type w} {p R : ℕ}

/-- The part of an exact native compiler contract needed for counting: every
successful native prefix is reproduced with the same output. It refers to
actual runs and instructions, not an input-to-output oracle. -/
def SimulatesNativePrefix (S : Enlarged.System Q Γ Λ 1 p R) (M : TM)
    (word : List Bool) (label : Λ) (T : ℕ) : Prop :=
  ∀ t ≤ T, (∀ u < t, transAt M word u ≠ none) →
    (∀ u < t, S.instruction label word u ≠ none) ∧
    (S.run label word t).outRev = (Transpose.Tape.run M word t).outRev

theorem outputBy_of_native_prefix {S : Enlarged.System Q Γ Λ 1 p R} {M : TM}
    {d b : ℕ} {C : ℝ} {X : Fin (d * d * b) → Bool} {label : Λ}
    (hc : TransposesInput M d b C X)
    (hs : S.SimulatesNativePrefix M (List.ofFn X) label (returnTime (d * d * b) C)) :
    S.OutputBy (tposOf d b) (returnTime (d * d * b) C) X label := by
  obtain ⟨hT, hsteps, hout⟩ := timely_native_data hc
  obtain ⟨hsuccess, houtput⟩ := hs _ hT hsteps
  exact ⟨_, hT, hsuccess, by rw [houtput]; exact hout⟩

end Enlarged.System

/-- One common enlarged system and label alphabet serve a subset of at least
half the promise set. The written native compiler must still supply this
contract; it is not inferred from the finite hash-selection lemma alone. -/
structure NativeHalfSimulation {P p R : ℕ} {Q : Type u} {Γ : Type v} {Λ : Type w}
    (M : TM) (S : Enlarged.System Q Γ Λ 1 p R) (G : Finset (Fin P → Bool)) (T : ℕ) where
  good : Finset (Fin P → Bool)
  subset : good ⊆ G
  half_card : G.card ≤ 2 * good.card
  label : good → Λ
  simulates : ∀ X : good, S.SimulatesNativePrefix M (List.ofFn X.val) (label X) T

theorem half_set_exponential {α : Type*} {G D : Finset α} {e : ℝ}
    (hhalf : G.card ≤ 2 * D.card) (hD : (D.card : ℝ) < (2 : ℝ) ^ e) :
    (G.card : ℝ) < (2 : ℝ) ^ (1 + e) := by
  have hh : (G.card : ℝ) ≤ 2 * (D.card : ℝ) := by exact_mod_cast hhalf
  rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
  linarith

/-- Exact reference budget and success tail, with the single actual native
half-set compiler contract left explicit. The dimension threshold precedes
all widths, machines, observers, finite state types and transition tables. -/
theorem reference_tail_of_half_simulation (k ell a : ℕ) (hk : 1 ≤ k) (hell : 1 ≤ ell)
    (ha : 1 ≤ a) {C : ℝ} (hC : 1 ≤ C) :
    let p := 1 + 2 * k * ell
    let N := portRunCap a p C
    ∃ d₀ : ℕ, ∀ d, d₀ ≤ d → ∀ b, 1 ≤ b →
      ∀ (M : TM) (U q u Z₀ s R : ℕ), M.q + 1 ≤ 2 ^ q → U ≤ 2 ^ u →
        ((q + u : ℕ) : ℝ) ≤ (d * d * b : ℕ) / (128 * (N : ℝ) ^ 2) →
        (Nat.clog 2 (blockSparseMenu (2 * returnTime (d * d * b) C + 1) a s) : ℝ) ≤
          (d * d * b : ℕ) / (256 * (k * (ell + 1) + 1) * (N : ℝ) ^ 2) →
        (Z₀ : ℝ) ≤ (d * d * b : ℕ) / (128 * (N : ℝ)) →
        R ≤ (d * d * b) / (8 * p * N) →
      ∀ (Q : Type u) (Γ : Type v) (Λ : Type w) [Fintype Q] [Fintype Γ] [Fintype Λ],
      ∀ S : Enlarged.System Q Γ Λ 1 p R,
        Fintype.card Q ≤ referenceStateBound k ell a (d * d * b)
          (returnTime (d * d * b) C) (M.q + 1) U s →
        Fintype.card Λ ≤ 2 ^ referenceLabelBits k ell a (returnTime (d * d * b) C) s Z₀ →
        Fintype.card Γ ≤ 2 ^ a →
      ∀ G : Finset (Fin (d * d * b) → Bool),
        (∀ X ∈ G, TransposesInput M d b C X) →
        NativeHalfSimulation M S G (returnTime (d * d * b) C) →
        (G.card : ℝ) < (2 : ℝ) ^ (1 + (1 - returnTailEta N) * (d * d * b : ℕ)) := by
  let p := 1 + 2 * k * ell
  let N := portRunCap a p C
  have hp : 1 ≤ p := by dsimp [p]; omega
  have hN : 1 ≤ N := by dsimp [N, portRunCap]; omega
  obtain ⟨P₀, hbudget⟩ := reference_budgets_small k ell a N hk hell hN C
  obtain ⟨d₁, hsize⟩ := uniform_positive_width_threshold (fun P => P₀ ≤ P) P₀ (fun _ h => h)
  obtain ⟨d₂, htail⟩ := Enlarged.macroscopic_tail a p ha hp hC
  refine ⟨max d₁ d₂, ?_⟩
  intro d hd b hb M U q u Z₀ s R hQ hU hqu hs hZ hR Q Γ Λ _ _ _ S hstates hlabels halphabet G correct sim
  let P := d * d * b
  let T := returnTime P C
  let bits := Nat.clog 2 (referenceStateBound k ell a P T (M.q + 1) U s)
  let labelBits := referenceLabelBits k ell a T s Z₀
  have hT : (T : ℝ) ≤ C * (P + 1) := Nat.floor_le (by positivity)
  obtain ⟨hbits, hlabelBits⟩ := hbudget P (hsize d ((le_max_left _ _).trans hd) b hb)
    T hT (M.q + 1) U q u Z₀ s hQ hU hqu hs hZ
  have hstates' : Fintype.card Q ≤ 2 ^ bits := hstates.trans
    (Nat.le_pow_clog (by decide : 1 < 2) _)
  have hcount := htail d ((le_max_right _ _).trans hd) b hb Q Γ Λ bits labelBits R
    hstates' hlabels halphabet hbits hlabelBits hR S sim.good (fun X =>
      ⟨sim.label X, Enlarged.System.outputBy_of_native_prefix
        (correct X.val (sim.subset X.property)) (sim.simulates X)⟩)
  exact half_set_exponential sim.half_card hcount

/-- Historical caches pay every frozen-base slot and every radius-M residual.
Only the construction of the actual common cache system remains a premise. -/
theorem cache_tail_of_half_simulation (k ell a : ℕ) (hk : 1 ≤ k) (hell : 1 ≤ ell)
    (ha : 1 ≤ a) {C : ℝ} (hC : 1 ≤ C) :
    let p := 1 + 2 * k * ell
    let N := portRunCap a p C
    ∃ d₀ : ℕ, ∀ d, d₀ ≤ d → ∀ b, 1 ≤ b →
      ∀ (M : TM) (U q u Z₀ s m R : ℕ), M.q + 1 ≤ 2 ^ q → U ≤ 2 ^ u →
        ((q + u : ℕ) : ℝ) ≤ (d * d * b : ℕ) / (128 * (N : ℝ) ^ 2) →
        (Nat.clog 2 (blockSparseMenu (2 * returnTime (d * d * b) C + 1) a (s + m + 1)) : ℝ) ≤
          (d * d * b : ℕ) / (256 * (k * (ell + 2)) * (N : ℝ) ^ 2) →
        (Z₀ : ℝ) ≤ (d * d * b : ℕ) / (128 * (N : ℝ)) →
        R ≤ (d * d * b) / (8 * p * N) →
      ∀ (Q : Type u) (Γ : Type v) (Λ : Type w) [Fintype Q] [Fintype Γ] [Fintype Λ],
      ∀ S : Enlarged.System Q Γ Λ 1 p R,
        Fintype.card Q ≤ cacheStateBound k ell a (d * d * b)
          (returnTime (d * d * b) C) (M.q + 1) U s (s + m + 1) →
        Fintype.card Λ ≤ 2 ^ referenceLabelBits k ell a (returnTime (d * d * b) C) s Z₀ →
        Fintype.card Γ ≤ 2 ^ a →
      ∀ G : Finset (Fin (d * d * b) → Bool),
        (∀ X ∈ G, TransposesInput M d b C X) →
        NativeHalfSimulation M S G (returnTime (d * d * b) C) →
        (G.card : ℝ) < (2 : ℝ) ^ (1 + (1 - returnTailEta N) * (d * d * b : ℕ)) := by
  let p := 1 + 2 * k * ell
  let N := portRunCap a p C
  have hp : 1 ≤ p := by dsimp [p]; omega
  have hN : 1 ≤ N := by dsimp [N, portRunCap]; omega
  obtain ⟨P₀, hbudget⟩ := cache_budgets_small k ell a N hk hell hN C
  obtain ⟨d₁, hsize⟩ := uniform_positive_width_threshold (fun P => P₀ ≤ P) P₀ (fun _ h => h)
  obtain ⟨d₂, htail⟩ := Enlarged.macroscopic_tail a p ha hp hC
  refine ⟨max d₁ d₂, ?_⟩
  intro d hd b hb M U q u Z₀ s m R hQ hU hqu hs hZ hR Q Γ Λ _ _ _ S hstates hlabels halphabet G correct sim
  let P := d * d * b
  let T := returnTime P C
  let bits := Nat.clog 2 (cacheStateBound k ell a P T (M.q + 1) U s (s + m + 1))
  let labelBits := referenceLabelBits k ell a T s Z₀
  have hT : (T : ℝ) ≤ C * (P + 1) := Nat.floor_le (by positivity)
  obtain ⟨hbits, hlabelBits⟩ := hbudget P (hsize d ((le_max_left _ _).trans hd) b hb)
    T hT (M.q + 1) U q u Z₀ s (s + m + 1) hQ hU (by omega) hqu hs hZ
  have hstates' : Fintype.card Q ≤ 2 ^ bits := hstates.trans
    (Nat.le_pow_clog (by decide : 1 < 2) _)
  have hcount := htail d ((le_max_right _ _).trans hd) b hb Q Γ Λ bits labelBits R
    hstates' hlabels halphabet hbits hlabelBits hR S sim.good (fun X =>
      ⟨sim.label X, Enlarged.System.outputBy_of_native_prefix
        (correct X.val (sim.subset X.property)) (sim.simulates X)⟩)
  exact half_set_exponential sim.half_card hcount

/-- One fixed positive density meets both sparse reserves, uniformly over all
positive widths. For caches the entering write is included in `s+floor(δP)+1`.
This is independent of the later choice of source, observer and compiler. -/
theorem reference_cache_sparse_reserves (k ell a N : ℕ) (hk : 1 ≤ k) (hN : 1 ≤ N)
    {C : ℝ} (hC : 0 ≤ C) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 8 ∧ ∃ d₀ : ℕ, ∀ d, d₀ ≤ d → ∀ b, 1 ≤ b →
      ∀ s : ℕ, (s : ℝ) ≤ δ * (d * d * b : ℕ) →
        (Nat.clog 2 (blockSparseMenu (2 * returnTime (d * d * b) C + 1) a s) : ℝ) ≤
          (d * d * b : ℕ) / (256 * (k * (ell + 1) + 1) * (N : ℝ) ^ 2) ∧
        (Nat.clog 2 (blockSparseMenu (2 * returnTime (d * d * b) C + 1) a
          (s + ⌊δ * (d * d * b : ℕ)⌋₊ + 1)) : ℝ) ≤
          (d * d * b : ℕ) / (256 * (k * (ell + 2)) * (N : ℝ) ^ 2) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have heps : 0 < 1 / (256 * ((k : ℝ) * (ell + 2)) * (N : ℝ) ^ 2) := by positivity
  obtain ⟨δ, hδ, hδcap, P₀, hbits⟩ := reference_cache_sparse_bits_small a hC heps
  obtain ⟨d₀, hsize⟩ := uniform_positive_width_threshold (fun P => P₀ ≤ P) P₀ (fun _ h => h)
  refine ⟨δ, hδ, hδcap, d₀, ?_⟩
  intro d hd b hb s hs
  let P := d * d * b
  have hT : ((returnTime P C : ℕ) : ℝ) ≤ C * (P + 1) := Nat.floor_le (by positivity)
  obtain ⟨hsparse, hcache⟩ := hbits P (hsize d hd b hb) (returnTime P C) hT s hs
  constructor
  · apply hsparse.trans
    rw [one_div_mul_eq_div]
    apply div_le_div_of_nonneg_left (Nat.cast_nonneg P) (by positivity)
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hcoef : (k : ℝ) * (ell + 1) + 1 ≤ (k : ℝ) * (ell + 2) := by linarith
    gcongr
  · simpa only [one_div_mul_eq_div] using hcache

end AdaptiveTransfer
