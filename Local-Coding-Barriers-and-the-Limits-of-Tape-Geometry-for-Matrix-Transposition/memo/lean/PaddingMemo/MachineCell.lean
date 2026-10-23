import PaddingMemo.LayoutCell
import TransposeFollowup.ContinuousNativePadding

/-! # The paid padding without idle tapes satisfies the cell-accurate cut inequality

Machine-level consequences of `cellCutIneq_of_layout`, for the follow-up's paid padding
`PaidPayload.machine F K M`: the prefix that runs the excursions, followed by a faithful simulation
of the payload machine `M`. This is the follow-up's construction *without* the extra stationary
tapes (`StationaryTapes.machine M extra`, used there only to meet the head-count condition
`4 · pages ≤ 3 k η`).

* `paidPayload_cellCut_after_prefix`: once the prefix has run, the actual work-head paths satisfy
  the cell-accurate cut inequality with zero slack at every slot length `1 ≤ r' ≤ 7 K r`, where
  `r = ⌈n b / 3⌉`, at every later horizon `T`.
* `paidPayload_preserves_computation_with_cellCut`: for every computation of `M`, the padded
  machine produces the same output within the follow-up's additive linear time bound, and its run
  satisfies both the cell-accurate and the first paper's zero-slack cut inequality.
* `uniform_computation_with_cellCut`: one choice of `K`, made before the payload machine, works
  for all payloads, sizes, inputs and outputs. Only the expansion of the finite overlap graphs is a
  premise, as in the follow-up's `PaidPadding.uniform_computation_with_cut`; the follow-up proves
  it unconditionally in `UnconditionalPaidPadding` (imported by `MachineCellUncond.lean`).
* `uniform_linear_tasks_macrostar_cell`: the corresponding limit statement, the original M*
  conclusion along any sequence of linear-time computations, again without idle tapes.
* `continuous_uniform_computation_with_cellCut`: the same from a rational continuous expander, with
  no premise on the finite graphs (the follow-up's `continuous_uniform_computation_with_cut` without
  stationary tapes); `MachineCellUncond.lean` removes the last premise.
-/

namespace PaddingMemo

open Classical
open Transpose Transpose.Tape Transpose.Tape.Impl Transpose.Tape.TSDiagram TransposeFollowup
open Filter Topology
set_option autoImplicit false

variable {c : ℕ}

theorem paidPayload_cellBits (F : Fin (c+1) → RationalMobius) (K : ℕ) (M : Transpose.TM) :
    cellBits (PaidPayload.machine F K M) = 3 := by
  unfold cellBits
  rw [(PaidPayload.fixed_resources F K M).2]
  decide +kernel

/-- **After the prefix, the padded machine satisfies the cell-accurate cut inequality** with zero
slack, at every slot length `1 ≤ r' ≤ 7 K ⌈n b/3⌉` and every horizon `T` after the prefix. -/
theorem paidPayload_cellCut_after_prefix (F : Fin (c+1) → RationalMobius) (K : ℕ)
    (M : Transpose.TM) (hK : 0 < K)
    (w : List Bool) (n : ℕ) (hn : 1 ≤ n) (hw : w.length = Transpose.inputLength n)
    (eta : ℝ)
    (hexp : ∀ S : Finset (Fin (2*n)), 2*S.card ≤ 2*n →
      eta*S.card ≤ (outsideNeighbors (overlapGraph (rationalFamilyMaps F) n) S).card)
    (hstretch : 1 ≤ ((2*K-1 : ℕ) : ℝ)*eta)
    (a : ℕ) (ca : Transpose.Config (PaidClean.nativeMachine F K))
    (ha : Transpose.stepN (PaidClean.nativeMachine F K) w a
      (Transpose.init (PaidClean.nativeMachine F K)) = some ca)
    (hh : Transpose.step (PaidClean.nativeMachine F K) w ca = none) (T : ℕ) (hT : a ≤ T)
    {r' : ℕ} (hr' : 1 ≤ r') (hr'K : r' ≤ 7 * K * blockSize 3 n) :
    CellCutIneq n 3 r' T 0 0 (PaidPayload.paths F K M w) := by
  obtain ⟨s, _hs, ⟨d, hd⟩, ⟨D⟩⟩ := PaidPayload.native_layout F K M hK w n hn hw
  have hsa := SequentialFive.successful_time_le_halting (PaidClean.nativeMachine F K) w a _ ca d
    ha hh hd
  let E := D.transfer_on_excursions (Function.Embedding.refl _) (hsa.trans hT) (by intros; rfl)
  exact cellCutIneq_of_layout E eta (by simpa only [Fintype.card_fin] using hexp) hstretch hr' hr'K
    (by simp only [Fintype.card_fin]; omega) (blockSize_mul_ge (by omega : 1 ≤ 3))

/-- **The padded machine preserves every computation and satisfies both cut inequalities.** -/
theorem paidPayload_preserves_computation_with_cellCut (F : Fin (c+1) → RationalMobius) (K : ℕ)
    (M : Transpose.TM) (hK : 0 < K) (w out : List Bool) (n : ℕ)
    (hn : 1 ≤ n) (hw : w.length = Transpose.inputLength n) (eta : ℝ)
    (hexp : ∀ S : Finset (Fin (2*n)), 2*S.card ≤ 2*n →
      eta*S.card ≤ (outsideNeighbors (overlapGraph (rationalFamilyMaps F) n) S).card)
    (hstretch : 1 ≤ ((2*K-1 : ℕ) : ℝ)*eta)
    (t : ℕ) (h : Transpose.ComputesWithin M w out t) :
    ∃ T ≤ PaidPayload.coefficient F K*w.length+t,
      ∃ d : Transpose.Config (PaidPayload.machine F K M),
        Transpose.stepN (PaidPayload.machine F K M) w T
          (Transpose.init (PaidPayload.machine F K M)) = some d ∧
        Transpose.step (PaidPayload.machine F K M) w d = none ∧ d.outRev.reverse = out ∧
        (∀ r', 1 ≤ r' → r' ≤ 7 * K * blockSize 3 n →
          CellCutIneq n 3 r' T 0 0 (PaidPayload.paths F K M w)) ∧
        (∀ r', 1 ≤ r' → r' ≤ 7 * K * blockSize 3 n →
          CutIneq n 3 r' T 0 0 (PaidPayload.paths F K M w)) := by
  obtain ⟨a, _ha, he, hh⟩ := PaidClean.native_complete F K w n hn hw
  obtain ⟨T, hT, d, hd, hhalt, hout⟩ := PaidPayload.preserves_computation F K M w out n hn hw t h
  have hp := SequentialFive.stepN_left (PaidPayload.prefixProgram F K)
    (PaidPayload.payloadProgram M) w a (Transpose.init (PaidPayload.prefixProgram F K).tm) _
    (SequentialFive.blankFrame (PaidPayload.payloadProgram M)) he
  rw [SequentialFive.initial_embed] at hp
  have haT := SequentialFive.successful_time_le_halting (PaidPayload.machine F K M) w T a d _
    hd hhalt hp
  have hcell : ∀ r', 1 ≤ r' → r' ≤ 7 * K * blockSize 3 n →
      CellCutIneq n 3 r' T 0 0 (PaidPayload.paths F K M w) := fun r' h1 h2 =>
    paidPayload_cellCut_after_prefix F K M hK w n hn hw eta hexp hstretch a _ he hh T haT h1 h2
  exact ⟨T, hT, d, hd, hhalt, hout, hcell, fun r' h1 h2 =>
    cutIneq_of_cellCutIneq h1 (fun p => unitSteps_workTraj (PaidPayload.machine F K M) w p)
      (hcell r' h1 h2)⟩

/-- A stretch parameter for a given expansion constant. -/
theorem exists_stretch {eta : ℝ} (heta : 0 < eta) :
    ∃ K : ℕ, 0 < K ∧ 1 ≤ ((2*K-1 : ℕ) : ℝ)*eta := by
  refine ⟨Nat.ceil (1/eta) + 1, by omega, ?_⟩
  have hc : 1/eta ≤ (Nat.ceil (1/eta) : ℝ) := Nat.le_ceil _
  have hcast : ((2*(Nat.ceil (1/eta) + 1) - 1 : ℕ) : ℝ) = 2 * (Nat.ceil (1/eta) : ℝ) + 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [hcast]
  have h1 : 1/eta * eta = 1 := by field_simp
  have h0 : (0 : ℝ) ≤ (Nat.ceil (1/eta) : ℝ) := Nat.cast_nonneg _
  nlinarith

/-- **One stretch parameter, chosen before the payload, for all computations.** No extra tapes are
added to the payload, and both cut inequalities hold on the actual run. The expansion of the finite
overlap graphs is the only premise (as in the follow-up's `uniform_computation_with_cut`). -/
theorem uniform_computation_with_cellCut (F : Fin (c+1) → RationalMobius)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ K : ℕ, 0 < K ∧ ∀ (M : Transpose.TM) (n : ℕ), 1 ≤ n → ∀ (w out : List Bool),
      w.length = Transpose.inputLength n →
      (∀ S : Finset (Fin (2*n)), 2*S.card ≤ 2*n →
        eta*S.card ≤ (outsideNeighbors (overlapGraph (rationalFamilyMaps F) n) S).card) →
      ∀ (t : ℕ), Transpose.ComputesWithin M w out t →
      ∃ T ≤ PaidPayload.coefficient F K*w.length+t,
        ∃ d : Transpose.Config (PaidPayload.machine F K M),
          Transpose.stepN (PaidPayload.machine F K M) w T
            (Transpose.init (PaidPayload.machine F K M)) = some d ∧
          Transpose.step (PaidPayload.machine F K M) w d = none ∧ d.outRev.reverse = out ∧
          (∀ r', 1 ≤ r' → r' ≤ 7 * K * blockSize 3 n →
            CellCutIneq n 3 r' T 0 0 (fun p τ => workTraj (PaidPayload.machine F K M) w τ p)) ∧
          (∀ r', 1 ≤ r' → r' ≤ 7 * K * blockSize 3 n →
            CutIneq n 3 r' T 0 0 (fun p τ => workTraj (PaidPayload.machine F K M) w τ p)) := by
  obtain ⟨K, hK, hstretch⟩ := exists_stretch heta
  exact ⟨K, hK, fun M n hn w out hw hexp t ht =>
    paidPayload_preserves_computation_with_cellCut F K M hK w out n hn hw eta hexp hstretch t ht⟩

/-- **The limit statement without idle tapes**: along any sequence of linear-time computations of a
payload machine, the padded machine (with no extra tapes) has actual halting times with the same
outputs and the follow-up's full M* limit conclusion. -/
theorem uniform_linear_tasks_macrostar_cell (F : Fin (c+1) → RationalMobius) (M : Transpose.TM)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ K : ℕ, ∀ (ns : ℕ → ℕ), Tendsto ns atTop atTop → (∀ i, 1 ≤ ns i) →
      ∀ (ws outs : ℕ → List Bool), (∀ i, (ws i).length = Transpose.inputLength (ns i)) →
      ∀ (a : ℕ), (∀ i, Transpose.ComputesWithin M (ws i) (outs i)
        (a*Transpose.inputLength (ns i))) →
      (∀ i (S : Finset (Fin (2*ns i))), 2*S.card ≤ 2*ns i →
        eta*S.card ≤ (outsideNeighbors (overlapGraph (rationalFamilyMaps F) (ns i)) S).card) →
      ∃ Ts : ℕ → ℕ,
        (∀ i, Ts i ≤ (PaidPayload.coefficient F K+a)*Transpose.inputLength (ns i) ∧
          ∃ d : Transpose.Config (PaidPayload.machine F K M),
            Transpose.stepN (PaidPayload.machine F K M) (ws i) (Ts i)
              (Transpose.init (PaidPayload.machine F K M)) = some d ∧
            Transpose.step (PaidPayload.machine F K M) (ws i) d = none ∧
            d.outRev.reverse = outs i ∧
            CellCutIneq (ns i) 3 (blockSize 3 (ns i)) (Ts i) 0 0
              (fun p τ => workTraj (PaidPayload.machine F K M) (ws i) τ p)) ∧
        NativeRunLimits.Conclusion (PaidPayload.machine F K M) ns ws Ts
          (PaidPayload.coefficient F K+a) := by
  obtain ⟨K, hK, hcompile⟩ := uniform_computation_with_cellCut F eta heta
  refine ⟨K, ?_⟩
  intro ns hns hn ws outs hw a hc he
  have hr := fun i => hcompile M (ns i) (hn i) (ws i) (outs i) (hw i) (he i)
    (a*Transpose.inputLength (ns i)) (hc i)
  choose Ts ht ds hs hh ho hcell hcut using hr
  have hb : ∀ i, 1 ≤ blockSize 3 (ns i) := fun i => one_le_blockSize (by omega) (hn i)
  have hbK : ∀ i, blockSize 3 (ns i) ≤ 7 * K * blockSize 3 (ns i) := fun i => by
    have : 1 ≤ 7 * K := by omega
    calc blockSize 3 (ns i) = 1 * blockSize 3 (ns i) := (one_mul _).symm
      _ ≤ 7 * K * blockSize 3 (ns i) := Nat.mul_le_mul_right _ this
  have htime : ∀ i, Ts i ≤ (PaidPayload.coefficient F K+a)*Transpose.inputLength (ns i) := by
    intro i
    simpa only [hw i, Nat.add_mul] using ht i
  refine ⟨Ts, fun i => ⟨htime i, ds i, hs i, hh i, ho i, hcell i _ (hb i) (hbK i)⟩, ?_⟩
  apply NativeRunLimits.of_cut _ ns hns ws Ts _ htime
  intro i
  rw [paidPayload_cellBits]
  exact hcut i _ (hb i) (hbK i)

/-- **The continuous-expander form**: from a rational family whose maps send their domains into
`[0, 1]` and expand every measurable set of measure `≤ 1/2` by a factor `1 + ε`, one stretch
parameter works for every payload, with no extra tapes and no remaining premise on the finite
graphs (the follow-up's `continuous_uniform_computation_with_cut`, without stationary tapes and
with both cut inequalities). -/
theorem continuous_uniform_computation_with_cellCut (F : Fin (c+1) → RationalMobius)
    (hmap : ∀ p, Set.MapsTo (rationalFamilyMaps F p).map (rationalFamilyMaps F p).domain
      (Set.Icc (0:ℝ) 1))
    (eps : ℝ) (heps : 0 < eps)
    (hforward : ∀ S : Set ℝ, MeasurableSet S → S ⊆ Set.Icc (0:ℝ) 1 →
      MeasureTheory.volume.real S ≤ 1/2 →
      (1+eps) * MeasureTheory.volume.real S ≤
        MeasureTheory.volume.real (mapImageUnion (rationalFamilyMaps F) S)) :
    ∃ K : ℕ, 0 < K ∧ ∀ (M : Transpose.TM) (n : ℕ), 1 ≤ n → ∀ (w out : List Bool),
      w.length = Transpose.inputLength n →
      ∀ (t : ℕ), Transpose.ComputesWithin M w out t →
      ∃ T ≤ PaidPayload.coefficient (r := c+1+c) (rationalSymmetricFamily F) K*w.length+t,
        ∃ d : Transpose.Config (PaidPayload.machine (r := c+1+c) (rationalSymmetricFamily F) K M),
          Transpose.stepN (PaidPayload.machine (r := c+1+c) (rationalSymmetricFamily F) K M) w T
            (Transpose.init (PaidPayload.machine (r := c+1+c) (rationalSymmetricFamily F) K M))
              = some d ∧
          Transpose.step (PaidPayload.machine (r := c+1+c) (rationalSymmetricFamily F) K M) w d
            = none ∧ d.outRev.reverse = out ∧
          (∀ r', 1 ≤ r' → r' ≤ 7 * K * blockSize 3 n →
            CellCutIneq n 3 r' T 0 0 (fun p τ =>
              workTraj (PaidPayload.machine (r := c+1+c) (rationalSymmetricFamily F) K M) w τ p)) ∧
          (∀ r', 1 ≤ r' → r' ≤ 7 * K * blockSize 3 n →
            CutIneq n 3 r' T 0 0 (fun p τ =>
              workTraj (PaidPayload.machine (r := c+1+c) (rationalSymmetricFamily F) K M) w τ p)) := by
  obtain ⟨K, hK, h⟩ := uniform_computation_with_cellCut (c := c+1+c) (rationalSymmetricFamily F)
    (eps/2) (by positivity)
  refine ⟨K, hK, ?_⟩
  intro M n hn w out hw t ht
  apply h M n hn w out hw ?_ t ht
  intro S hS
  exact rationalSymmetricGraph_vertex_expansion_all_sizes F (by omega) hmap eps heps.le hforward S
    (by simpa only [Fintype.card_fin] using hS)

end PaddingMemo
