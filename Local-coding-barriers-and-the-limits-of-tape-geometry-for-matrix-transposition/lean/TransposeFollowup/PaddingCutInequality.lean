import TransposeFollowup.ExcursionLayout
import Transpose.Tape.DefsM

/-! The complete finite cut inequality from an explicit excursion layout and
vertex expansion. The global walk/generator/paid-machine construction remains
a separate obligation. Weighted accounting improves both sufficient numerical
thresholds from 8 in the written proof to 4.
-/

namespace TransposeFollowup

open Classical
open Transpose Transpose.Tape
open scoped BigOperators
set_option autoImplicit false

theorem weighted_padding_budget {eta v F q M k A C : ℝ}
    (heta : 0 < eta) (hF : 0 ≤ F) (hM : 0 ≤ M)
    (hA : 4 ≤ A * eta) (hk : 4 * q ≤ 3 * k * eta)
    (hcut : eta * v / 2 - q * M ≤ F) (hchord : A * F ≤ C) :
    2 * v ≤ 3 * k * M + C := by
  have h1 := mul_le_mul_of_nonneg_right hA hF
  have h2 := mul_le_mul_of_nonneg_left hchord heta.le
  have h3 := mul_le_mul_of_nonneg_right hk hM
  have h4 : eta * (2 * v) ≤ eta * (3 * k * M + C) := by nlinarith only [h1, h2, h3, hcut]
  exact (mul_le_mul_iff_right₀ heta).mp h4

namespace ExcursionLayout

variable {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {r K k T : ℕ} {h : Fin k → ℕ → ℤ}
    (D : ExcursionLayout G r K k T h)

include D

theorem padding_budget (eta : ℝ) (heta : 0 < eta)
    (hexp : ∀ S : Finset V, 2 * S.card ≤ Fintype.card V →
      eta * S.card ≤ (outsideNeighbors G S).card)
    (q : ℕ) (hdegree : ∀ i, G.degree i ≤ q)
    (hK : 4 ≤ (4 * K - 1 : ℕ) * eta) (hk : 4 * (q : ℝ) ≤ 3 * k * eta)
    (hv : 2 ≤ Fintype.card V) (lab : ℕ → ℕ) (m : ℕ) (hmv : m ≤ Fintype.card V)
    (hm : ∀ ell, ((Finset.range (numSlots r T)).filter (fun s => lab s = ell)).card ≤ m) :
    2 * Fintype.card V ≤ 3 * k * labelChanges lab (numSlots r T) +
      ∑ t : Fin k, (crossChords (pairRes r (h t) T) lab (numSlots r T)).card := by
  have he := expanding_good_cut G eta hexp (D.labels lab) (D.labels_small lab m hv hmv hm)
    (D.bad lab) q hdegree
  have hbad : (q : ℝ) * (D.bad lab).card ≤ q * labelChanges lab (numSlots r T) := by
    exact_mod_cast Nat.mul_le_mul_left q (D.bad_count lab)
  have hcut : eta * Fintype.card V / 2 - q * labelChanges lab (numSlots r T) ≤
      (D.goodEdges lab).card := by
    change eta * Fintype.card V / 2 - q * labelChanges lab (numSlots r T) ≤
      (goodCrossEdges G (D.labels lab) (D.bad lab)).card
    linarith
  have hch : ((4 * K - 1 : ℕ) : ℝ) * (D.goodEdges lab).card ≤
      ∑ t : Fin k, ((crossChords (pairRes r (h t) T) lab (numSlots r T)).card : ℝ) := by
    exact_mod_cast D.global_chord_count lab
  have hb := weighted_padding_budget heta (by positivity : 0 ≤ ((D.goodEdges lab).card : ℝ))
    (by positivity : 0 ≤ (labelChanges lab (numSlots r T) : ℝ)) hK hk hcut hch
  exact_mod_cast hb

/-- The original paper's full discrete `CutIneq`, with both numerical slacks
zero, for every finite slot labeling. No source entropy or correctness claim
is needed to derive this geometric inequality. -/
theorem cutIneq (eta : ℝ) (heta : 0 < eta)
    (hexp : ∀ S : Finset V, 2 * S.card ≤ Fintype.card V →
      eta * S.card ≤ (outsideNeighbors G S).card)
    (q : ℕ) (hdegree : ∀ i, G.degree i ≤ q)
    (hK : 4 ≤ (4 * K - 1 : ℕ) * eta) (hk : 4 * (q : ℝ) ≤ 3 * k * eta)
    (hv : 2 ≤ Fintype.card V) (n cellBits : ℕ) (hn : n ≤ 2 * Fintype.card V)
    (hrG : n * entryBits n ≤ r * cellBits) : CutIneq n cellBits r T 0 0 h := by
  intro lab m hm
  simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add]
  by_cases hlarge : n ≤ 2 * m
  · simp [Nat.sub_eq_zero_of_le hlarge]
  have hmv : m ≤ Fintype.card V := by omega
  have hbudget := D.padding_budget eta heta hexp q hdegree hK hk hv lab m hmv hm
  calc
    _ ≤ n * n * entryBits n := Nat.mul_le_mul_right _
      (Nat.mul_le_mul (Nat.sub_le n _) (Nat.sub_le n _))
    _ = n * (n * entryBits n) := by ring
    _ ≤ n * (r * cellBits) := Nat.mul_le_mul_left n hrG
    _ = r * cellBits * n := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ (hn.trans hbudget)

end ExcursionLayout
end TransposeFollowup
