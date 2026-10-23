import PaddingMemo.MachineCellUncond

/-! # The simplified statements, in the follow-up's own form

* `exists_uniform_paid_padding_without_idle_tapes` is the follow-up's
  `TransposeFollowup.PaidPadding.exists_uniform_paid_padding` with no extra stationary tapes:
  the tape count `K₀ + (k(M) + E) · max 1 (size g(M))` becomes `K₀ + k(M) · max 1 (size g(M))`,
  that is, `E = 0`. Every other clause is unchanged.
* `layout_cutIneq_without_head_count` is the follow-up's `ExcursionLayout.cutIneq` without the
  degree bound `q` and the head-count hypothesis `4 q ≤ 3 k η` (the hypothesis that the idle tapes
  exist to satisfy), and with the follow-up's own stretch hypothesis `4 ≤ (4K − 1) η`. In exchange
  it asks for unit-step walks (as head trajectories are) and `2 n ≤ |V|` instead of `n ≤ 2 |V|`;
  the follow-up's construction has `|V| = 2 n`.
-/

namespace PaddingMemo

open Classical
open Transpose Transpose.Tape Transpose.Tape.Impl Transpose.Tape.TSDiagram TransposeFollowup
open Filter Topology
set_option autoImplicit false

/-- **The follow-up's padding theorem without idle tapes.** The statement of
`TransposeFollowup.PaidPadding.exists_uniform_paid_padding` with `E = 0`. -/
theorem exists_uniform_paid_padding_without_idle_tapes :
    ∃ A H K₀ : ℕ, ∀ M : Transpose.TM, ∃ M' : Transpose.TM,
      M'.q + 1 = H + (M.q + 1) ∧ M'.k = K₀ + M.k * max 1 M.g.size ∧ cellBits M' = 3 ∧
      (∀ n : ℕ, 1 ≤ n → ∀ w out : List Bool, w.length = Transpose.inputLength n →
        ∀ t : ℕ, Transpose.ComputesWithin M w out t →
        ∃ T ≤ A*w.length+t, ∃ d : Transpose.Config M',
          Transpose.stepN M' w T (Transpose.init M') = some d ∧
          Transpose.step M' w d = none ∧ d.outRev.reverse = out ∧
          CutIneq n (cellBits M') (blockSize (cellBits M') n) T 0 0
            (fun p τ => workTraj M' w τ p)) ∧
      ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop → (∀ i, 1 ≤ ns i) →
        ∀ ws outs : ℕ → List Bool, (∀ i, (ws i).length = Transpose.inputLength (ns i)) →
        ∀ a : ℕ, (∀ i, Transpose.ComputesWithin M (ws i) (outs i)
          (a*Transpose.inputLength (ns i))) →
        ∃ Ts : ℕ → ℕ,
          (∀ i, Ts i ≤ (A+a)*Transpose.inputLength (ns i) ∧
            ∃ d : Transpose.Config M',
              Transpose.stepN M' (ws i) (Ts i) (Transpose.init M') = some d ∧
              Transpose.step M' (ws i) d = none ∧ d.outRev.reverse = outs i ∧
              CutIneq (ns i) (cellBits M') (blockSize (cellBits M') (ns i)) (Ts i) 0 0
                (fun p τ => workTraj M' (ws i) τ p)) ∧
          NativeRunLimits.Conclusion M' ns ws Ts (A+a) := by
  obtain ⟨A, H, K₀, K, hK, h⟩ := exists_uniform_paid_padding_cell
  refine ⟨A, H, K₀, fun M => ?_⟩
  obtain ⟨M', hq, hk, hbits, ha, hb⟩ := h M
  refine ⟨M', hq, hk, hbits, ?_, ?_⟩
  · intro n hn w out hw t ht
    obtain ⟨T, hT, d, hs, hh, ho, -, hcut⟩ := ha n hn w out hw t ht
    refine ⟨T, hT, d, hs, hh, ho, ?_⟩
    rw [hbits]
    have hb1 : 1 ≤ blockSize 3 n := one_le_blockSize (by omega) hn
    have hbK : blockSize 3 n ≤ 7 * K * blockSize 3 n := by
      have : 1 ≤ 7 * K := by omega
      calc blockSize 3 n = 1 * blockSize 3 n := (one_mul _).symm
        _ ≤ 7 * K * blockSize 3 n := Nat.mul_le_mul_right _ this
    exact hcut _ hb1 hbK
  · intro ns hns hn ws outs hw a hc
    obtain ⟨Ts, hTs, hconc⟩ := hb ns hns hn ws outs hw a hc
    refine ⟨Ts, fun i => ?_, hconc⟩
    obtain ⟨hle, d, hs, hh, ho, -, hcut⟩ := hTs i
    refine ⟨hle, d, hs, hh, ho, ?_⟩
    rw [hbits]
    exact hcut

/-- **The follow-up's layout theorem without the head-count hypothesis.** Under the follow-up's
expansion and stretch hypotheses, with no degree bound and no relation between `k`, `η` and the
pages, an excursion layout of unit-step walks satisfies the first paper's zero-slack cut inequality
at its block size `r`, provided `2 n ≤ |V|`. (`cutIneq_of_layout` gives every slot length up to
`7 K r`, and `cellCutIneq_of_layout` the finer cell-accurate inequality.) -/
theorem layout_cutIneq_without_head_count {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {r K k T : ℕ} {h : Fin k → ℕ → ℤ}
    (D : ExcursionLayout G r K k T h) (hunit : ∀ t, UnitSteps (h t)) (eta : ℝ)
    (hexp : ∀ S : Finset V, 2 * S.card ≤ Fintype.card V →
      eta * S.card ≤ (outsideNeighbors G S).card)
    (hK : 4 ≤ ((4 * K - 1 : ℕ) : ℝ) * eta) (n cellBits : ℕ)
    (hn : 2 * n ≤ Fintype.card V) (hrG : n * entryBits n ≤ r * cellBits) :
    CutIneq n cellBits r T 0 0 h := by
  have hr : 1 ≤ r := D.r_pos
  have hrK : r ≤ 7 * K * r := by
    have : 1 ≤ 7 * K := by have := D.K_pos; omega
    calc r = 1 * r := (one_mul _).symm
      _ ≤ 7 * K * r := Nat.mul_le_mul_right _ this
  exact cutIneq_of_layout D hunit eta hexp (stretch_of_followup D.K_pos hK) hr hrK hn hrG

end PaddingMemo
