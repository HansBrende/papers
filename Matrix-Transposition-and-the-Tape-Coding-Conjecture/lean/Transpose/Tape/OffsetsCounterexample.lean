import Transpose.Tape.CutTrace
import Transpose.Tape.WitnessGap

/-!
# The offsets-only form of the Block Locality Lemma is false

The Block Locality Lemma (`block_locality`) asks two runs with the same block-level trace to agree,
at every memory boundary of a set `U` of slots, on the full work-head positions. Agreement on the
offsets of the work heads within their blocks does not suffice: the block-level trace fixes the
blocks resident at a slot, but not which of them holds the work head at the memory boundary, so two
runs can agree on all the other data and on the offsets while their heads stand on different
cells.

`block_locality_offsets_counterexample`: the inputs `[false]` and `[true]` of `Witness.gapTM` (one
work tape, `1 × 1` matrices with `1`-bit entries) share the halting time `T = 9` and the block-level
trace for slots of `r = 4` steps. At the memory boundary `z = 2` of `U = {2}` they satisfy every
hypothesis of the offsets-only form:
* they agree on the state, the input-head position and the work-head offset;
* they agree on the contents of the resident blocks `{0, 1}`;
* no chord enters `U`, and no input row is touched during the steps `J` of the slots of `U`.

Yet the transition at step `8`, the first step of slot `2`, differs: the work heads stand at
offset `1` of the different resident blocks `1` and `0`, so they read different cells.
`block_locality` avoids this by recording the full head positions.
-/

namespace Transpose.Tape.Impl

open Transpose Witness

theorem gap_t0 : ∀ t : Fin gapTM.k, t = ⟨0, by decide⟩ :=
  fun t => Subsingleton.elim (α := Fin 1) t ⟨0, by decide⟩

theorem gap_halts (a : Bool) : HaltsAt gapTM [a] 9 := by
  cases a <;> exact ⟨by decide, by decide⟩

theorem gap_output (a : Bool) : (run gapTM [a] 9).outRev.reverse = [a] := by
  cases a <;> decide

theorem gap_transposes : Transposes gapTM 1 1 := by
  intro A
  refine ⟨9, (computesWithin_iff _ _).2 ⟨9, le_rfl, ?_, ?_⟩⟩
  · exact gap_halts (A 0 0 0)
  · exact gap_output (A 0 0 0)

theorem gap_numSlots : numSlots 4 9 = 3 := by decide

theorem gap_pairRes : ∀ y ≤ 3,
    pairRes 4 (fun τ => workTraj gapTM [false] τ ⟨0, by decide⟩) 9 y =
      pairRes 4 (fun τ => workTraj gapTM [true] τ ⟨0, by decide⟩) 9 y := by
  decide

theorem gap_inPos : ∀ τ ≤ 15, (run gapTM [false] τ).inPos = (run gapTM [true] τ).inPos := by
  decide

theorem gap_outLen : ∀ y ≤ 3, (run gapTM [false] (y * 4)).outRev.length =
    (run gapTM [true] (y * 4)).outRev.length := by
  decide

theorem gap_srcRows (y : ℕ) :
    srcRows gapTM [false] 1 1 (slotOf 4 9 y) = srcRows gapTM [true] 1 1 (slotOf 4 9 y) :=
  srcRows_congr fun τ hτ => gap_inPos τ (by
    simp only [slotOf, Finset.mem_filter, Finset.mem_Ico] at hτ; omega)

theorem gap_sameTrace : SameTrace gapTM 1 1 4 9 [false] [true] := by
  intro y hy
  rw [gap_numSlots] at hy
  simp only [blockTrace]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext t
    rw [gap_t0 t]
    exact gap_pairRes y hy
  · exact gap_srcRows y
  · exact gap_outLen y hy

theorem gap_boundary :
    (run gapTM [false] 8).state = (run gapTM [true] 8).state ∧
    (run gapTM [false] 8).inPos = (run gapTM [true] 8).inPos ∧
    (run gapTM [false] 8).workPos ⟨0, by decide⟩ % 4 =
      (run gapTM [true] 8).workPos ⟨0, by decide⟩ % 4 ∧
    pairRes 4 (fun τ => workTraj gapTM [false] τ ⟨0, by decide⟩) 9 2 = {0, 1} ∧
    (∀ c : Fin 8, (run gapTM [false] 8).work ⟨0, by decide⟩ (c : ℤ) =
      (run gapTM [true] 8).work ⟨0, by decide⟩ (c : ℤ)) ∧
    blockOf 4 ((run gapTM [false] 8).workPos ⟨0, by decide⟩) ≠
      blockOf 4 ((run gapTM [true] 8).workPos ⟨0, by decide⟩) := by
  decide

theorem gap_differs : transAt gapTM [false] 8 ≠ transAt gapTM [true] 8 := by decide

theorem gap_memBoundary : 2 ∈ memBoundaries {2} (numSlots 4 9) := by
  rw [gap_numSlots]; simp [memBoundaries]

theorem gap_noChord (β : ℤ) (x : ℕ) :
    ¬ IsChord (pairRes 4 (fun τ => workTraj gapTM [false] τ ⟨0, by decide⟩) 9) β x 2 := by
  rintro ⟨hx, h0, -, hmid⟩
  have hx0 : x = 0 := by omega
  subst hx0
  have hR0 : pairRes 4 (fun τ => workTraj gapTM [false] τ ⟨0, by decide⟩) 9 0 = {0} := by decide
  have hR1 : pairRes 4 (fun τ => workTraj gapTM [false] τ ⟨0, by decide⟩) 9 1 = {0, 1} := by
    decide
  rw [hR0, Finset.mem_singleton] at h0
  subst h0
  exact hmid 1 (by omega) (by omega) (by rw [hR1]; decide)

theorem gap_srcRows_J : srcRows gapTM [false] 1 1 (slotSteps 4 {2} 9) = ∅ := by
  have hJ : slotSteps 4 {2} 9 = {8} := by
    ext τ; simp only [slotSteps, Finset.mem_filter, Finset.mem_range, Set.mem_singleton_iff,
      Finset.mem_singleton]; omega
  have h8 : (run gapTM [false] 8).inPos = -1 := by decide
  rw [hJ]
  ext i
  simp [srcRows, h8]
  intro _; omega

/-- **The offsets-only form of the Block Locality Lemma is false.** -/
theorem block_locality_offsets_counterexample : ∃ (M : TM) (w w' : List Bool),
    Transposes M 1 1 ∧ w ∈ matrixInputs 1 1 ∧ w' ∈ matrixInputs 1 1 ∧
    HaltsAt M w 9 ∧ HaltsAt M w' 9 ∧ SameTrace M 1 1 4 9 w w' ∧
    2 ∈ memBoundaries {2} (numSlots 4 9) ∧
    (run M w 8).state = (run M w' 8).state ∧ (run M w 8).inPos = (run M w' 8).inPos ∧
    (∀ t, (run M w 8).workPos t % 4 = (run M w' 8).workPos t % 4) ∧
    (∀ (t : Fin M.k) (c : ℤ), blockOf 4 c ∈ pairRes 4 (fun τ => workTraj M w τ t) 9 2 →
      (run M w 8).work t c = (run M w' 8).work t c) ∧
    (∀ (t : Fin M.k) (β : ℤ) (x : ℕ), ¬ IsChord (pairRes 4 (fun τ => workTraj M w τ t) 9) β x 2) ∧
    srcRows M w 1 1 (slotSteps 4 {2} 9) = ∅ ∧
    (∃ t, blockOf 4 ((run M w 8).workPos t) ≠ blockOf 4 ((run M w' 8).workPos t)) ∧
    transAt M w 8 ≠ transAt M w' 8 := by
  obtain ⟨hs, hi, hoff, hres, hcont, hblk⟩ := gap_boundary
  refine ⟨gapTM, [false], [true], gap_transposes, ?_, ?_, gap_halts false, gap_halts true,
    gap_sameTrace, gap_memBoundary, hs, hi, ?_, ?_, ?_, gap_srcRows_J, ⟨⟨0, by decide⟩, hblk⟩,
    gap_differs⟩
  · rw [matrixInputs_eq]; rfl
  · rw [matrixInputs_eq]; rfl
  · intro t; rw [gap_t0 t]; exact hoff
  · intro t c hc
    rw [gap_t0 t] at hc ⊢
    rw [hres] at hc
    have hc' : 0 ≤ c ∧ c < 8 := by
      have h := (mem_blockCells (r := 4) (by norm_num) (c := c) (β := blockOf 4 c)).2 rfl
      simp only [blockCells, Finset.mem_Ico] at h
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with h0 | h0 <;> rw [h0] at h <;> omega
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, c = m := ⟨c.toNat, by omega⟩
    exact hcont ⟨m, by omega⟩
  · intro t β x
    rw [gap_t0 t]
    exact gap_noChord β x

end Transpose.Tape.Impl
