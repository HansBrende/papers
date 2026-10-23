import PaddingMemo.MachineCell
import TransposeFollowup.UnconditionalPaidPadding

/-! # The follow-up's padding theorem without idle tapes, unconditionally

The follow-up's `PaidPadding.exists_uniform_paid_padding` adds `E · max 1 (size g)` stationary tapes
to meet the head-count condition of its cut-inequality proof. With the per-offset count of
`cellCutIneq_of_layout` those tapes are unnecessary: the padded machine `PaidPayload.machine`
(prefix of excursions, then a faithful bit-plane simulation of the payload) already satisfies both
the cell-accurate and the first paper's zero-slack cut inequality, at every slot length up to
`7 K ⌈n b / 3⌉`. The rational continuous expander comes from the follow-up's
`exists_rational_continuous_expander`, so no premise remains.

`exists_uniform_paid_padding_cell` has every clause of the follow-up's theorem (state count, tape
count with `E = 0`, cell bits, part (a) on computations, part (b) on limits), with part (a)
strengthened to both inequalities at every scale up to `7 K ⌈n b/3⌉`.
-/

namespace PaddingMemo

open Classical
open Transpose Transpose.Tape Transpose.Tape.Impl Transpose.Tape.TSDiagram TransposeFollowup
open Filter Topology
set_option autoImplicit false

/-- **Universal fully paid padding without idle tapes.** There are constants `A`, `H`, `K₀` and a
stretch parameter `K`, all chosen before the payload, such that every machine `M` has a padded
machine `M'` with `H + (q(M)+1)` states, `K₀ + k(M) · max 1 (size g(M))` work tapes and three-bit
cells, and:
(a) for every computation of `M` within `t` steps on an input of dimension `n ≥ 1`, an actual halting
time `T ≤ A·|w| + t` of `M'` with the same output, whose run satisfies the cell-accurate and the first
paper's zero-slack cut inequality at every slot length `1 ≤ r' ≤ 7 K ⌈n b/3⌉`;
(b) along every sequence of computations of `M` within `a·L` steps, actual halting times with the same
outputs, both inequalities at the block size `⌈n b/3⌉`, and the follow-up's full M* limit
conclusion with time constant `A + a`. -/
theorem exists_uniform_paid_padding_cell :
    ∃ A H K₀ K : ℕ, 0 < K ∧ ∀ M : Transpose.TM, ∃ M' : Transpose.TM,
      M'.q + 1 = H + (M.q + 1) ∧ M'.k = K₀ + M.k * max 1 M.g.size ∧ cellBits M' = 3 ∧
      (∀ n : ℕ, 1 ≤ n → ∀ w out : List Bool, w.length = Transpose.inputLength n →
        ∀ t : ℕ, Transpose.ComputesWithin M w out t →
        ∃ T ≤ A*w.length+t, ∃ d : Transpose.Config M',
          Transpose.stepN M' w T (Transpose.init M') = some d ∧
          Transpose.step M' w d = none ∧ d.outRev.reverse = out ∧
          (∀ r', 1 ≤ r' → r' ≤ 7 * K * blockSize 3 n →
            CellCutIneq n 3 r' T 0 0 (fun p τ => workTraj M' w τ p)) ∧
          (∀ r', 1 ≤ r' → r' ≤ 7 * K * blockSize 3 n →
            CutIneq n 3 r' T 0 0 (fun p τ => workTraj M' w τ p))) ∧
      ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop → (∀ i, 1 ≤ ns i) →
        ∀ ws outs : ℕ → List Bool, (∀ i, (ws i).length = Transpose.inputLength (ns i)) →
        ∀ a : ℕ, (∀ i, Transpose.ComputesWithin M (ws i) (outs i)
          (a*Transpose.inputLength (ns i))) →
        ∃ Ts : ℕ → ℕ,
          (∀ i, Ts i ≤ (A+a)*Transpose.inputLength (ns i) ∧
            ∃ d : Transpose.Config M',
              Transpose.stepN M' (ws i) (Ts i) (Transpose.init M') = some d ∧
              Transpose.step M' (ws i) d = none ∧ d.outRev.reverse = outs i ∧
              CellCutIneq (ns i) 3 (blockSize 3 (ns i)) (Ts i) 0 0
                (fun p τ => workTraj M' (ws i) τ p) ∧
              CutIneq (ns i) 3 (blockSize 3 (ns i)) (Ts i) 0 0
                (fun p τ => workTraj M' (ws i) τ p)) ∧
          NativeRunLimits.Conclusion M' ns ws Ts (A+a) := by
  obtain ⟨c, F, eps, heps, hmap, hexp⟩ := exists_rational_continuous_expander
  obtain ⟨K, hK, hcompile⟩ := continuous_uniform_computation_with_cellCut F hmap eps heps hexp
  refine ⟨PaidPayload.coefficient (r := c+1+c) (rationalSymmetricFamily F) K,
    (PaidPayload.prefixProgram (r := c+1+c) (rationalSymmetricFamily F) K).q + 1,
    53 + rationalPageCount (rationalSymmetricFamily F), K, hK, ?_⟩
  intro M
  have hrun := hcompile M
  refine ⟨PaidPayload.machine (r := c+1+c) (rationalSymmetricFamily F) K M, ?_,
    (PaidPayload.fixed_resources (r := c+1+c) (rationalSymmetricFamily F) K M).1,
    paidPayload_cellBits (c := c+1+c) (rationalSymmetricFamily F) K M, hrun, ?_⟩
  · -- the state count: the prefix's states plus the payload's (bit planes keep `q`)
    have h := (SequentialFive.fixed_resources
      (PaidPayload.prefixProgram (r := c+1+c) (rationalSymmetricFamily F) K)
      (PaidPayload.payloadProgram M)).2.2
    have hq : (PaidPayload.payloadProgram M).q = M.q := (BitPlaneMachine.fixed_resources M).2.2
    show (SequentialFive.machine
      (PaidPayload.prefixProgram (r := c+1+c) (rationalSymmetricFamily F) K)
      (PaidPayload.payloadProgram M)).q + 1 = _
    rw [h, hq]
  · -- part (b): limits along sequences, from part (a) at the block size
    intro ns hns hn ws outs hw a hc
    have hr := fun i => hrun (ns i) (hn i) (ws i) (outs i) (hw i)
      (a*Transpose.inputLength (ns i)) (hc i)
    choose Ts ht ds hs hh ho hcell hcut using hr
    have hb : ∀ i, 1 ≤ blockSize 3 (ns i) := fun i => one_le_blockSize (by omega) (hn i)
    have hbK : ∀ i, blockSize 3 (ns i) ≤ 7 * K * blockSize 3 (ns i) := fun i => by
      have : 1 ≤ 7 * K := by omega
      calc blockSize 3 (ns i) = 1 * blockSize 3 (ns i) := (one_mul _).symm
        _ ≤ 7 * K * blockSize 3 (ns i) := Nat.mul_le_mul_right _ this
    have htime : ∀ i, Ts i ≤ (PaidPayload.coefficient (r := c+1+c) (rationalSymmetricFamily F) K
        + a) * Transpose.inputLength (ns i) := by
      intro i
      simpa only [hw i, Nat.add_mul] using ht i
    refine ⟨Ts, fun i => ⟨htime i, ds i, hs i, hh i, ho i, hcell i _ (hb i) (hbK i),
      hcut i _ (hb i) (hbK i)⟩, ?_⟩
    apply NativeRunLimits.of_cut _ ns hns ws Ts _ htime
    intro i
    rw [paidPayload_cellBits]
    exact hcut i _ (hb i) (hbK i)

end PaddingMemo
