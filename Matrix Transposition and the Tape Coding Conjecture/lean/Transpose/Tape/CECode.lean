import Transpose.Tape.CECount
import Transpose.Tape.CutTrace
import Transpose.Tape.MStarTM
import Transpose.Tape.PopularTrace

/-!
# A trace class is a network code (the Block Locality Lemma in functional form)

Let `F` be a trace class (slot length `r`, halting time `T`, representative `w₀`) on which `M`
outputs the transposed encoding (`ClassCorrect`; `Transposes M n b` implies it).
* `runDiagram M w₀ T` (in `DefsCE.lean`): the time–space diagram of the run on `w₀`. It is valid when the
  run outputs `L` bits (`runDiagram_valid`).
* **Edge payloads.** An edge carries only what its source slot can compute.
  - The memory edge `y → y + 1` carries the state and the head positions at time `(y+1) r`, and the
    contents at that time of the blocks resident at slot `y` (`R_y`, at most `3` per tape).
  - A chord edge `x → z` carries, for each tape with a chord of some block `β` from `x` to `z`, the
    contents of `β` at time `z r` (at most one block per tape).

  A block of `R_{y+1} ∖ R_y` either arrives by the chord from its previous visit or was never
  visited (blank).
* `classCode`: each node chooses a member of `F` consistent with the values it receives and its
  visible input, and sends that member's payloads; the decoder outputs that member's output bit.
* `consistent_agree`: the Block Locality Lemma for the single slot `U = {y}`. Two members
  consistent with the same data at `y` have the same payloads on the edges out of `y` and the same
  output bits at `y`.
* `traceClass_code`: the code solves complete exchange on the class within the capacities.
* `code_bits_of_class`: **the single machine reduction**, at the per-node blocks plus `s` bits per
  memory edge (when the state bits plus the head-position bits fit in `s`); `diagram_of_class`: the
  same with the tapes indexed by `Fin k` for `M.k = k`, and `rescaled_runDiagram`: the diagram's
  rescaled walks are the machine's rescaled trajectories (Theorem M\* for machines from Theorem M\*
  for diagrams, `MStarClass.lean`).
-/

namespace Transpose.Tape.Impl

open Transpose TSDiagram

variable {M : TM}

/-! ### The diagram of a run -/

theorem runDiagram_valid {n b T : ℕ} {w₀ : List Bool} (hout : (run M w₀ T).outRev.length = n * n * b)
    (hT : HaltsAt M w₀ T) : (runDiagram M w₀ T).Valid (n * n * b) := by
  refine ⟨fun t => ⟨rfl, unitSteps_workTraj M w₀ t⟩, rfl, unitSteps_inTraj M w₀, rfl,
    fun τ => ?_, fun τ hτ => ?_⟩
  · have := outRev_length_succ (M := M) w₀ τ
    simp only [runDiagram]
    split_ifs at this <;> omega
  · simp only [runDiagram]
    rw [run_of_le_of_none hT.2 hτ, hout]

/-! ### Payloads -/

section Payload

variable (M) (r T : ℕ) (w₀ : List Bool)

/-- The pair residency of work tape `t` in the run on `w₀`. -/
def resT (t : Fin M.k) : ℕ → Finset ℤ := pairRes r (fun τ => workTraj M w₀ τ t) T

/-- The cells of the blocks resident at slot `y` on tape `t`. -/
def memCells (t : Fin M.k) (y : ℕ) : Finset ℤ := (resT M r T w₀ t y).biUnion (blockCells r)

open Classical in
/-- The cells of the blocks of tape `t` with a chord from slot `x` to slot `z`. -/
noncomputable def chordCells (t : Fin M.k) (x z : ℕ) : Finset ℤ :=
  ((resT M r T w₀ t z).filter (fun β => IsChord (resT M r T w₀ t) β x z)).biUnion (blockCells r)

/-- The payload type of the memory edge `y → y + 1`: state, input-head position, work-head
positions, contents of the cells of `R_y`. -/
abbrev MemPayload (y : ℕ) : Type :=
  Fin (M.q + 1) × Fin (2 * T + 1) × (Fin M.k → Fin (2 * T + 1)) ×
    ((t : Fin M.k) → ↥(memCells M r T w₀ t y) → Fin (M.g + 1))

/-- The payload type of the chord edge `x → z`: contents of the cells of the chord blocks. -/
abbrev ChordPayload (x z : ℕ) : Type :=
  (t : Fin M.k) → ↥(chordCells M r T w₀ t x z) → Fin (M.g + 1)

/-- The payload of the memory edge `y → y + 1` on input `w`, at time `(y+1) r`. -/
def memPayload (w : List Bool) (y : ℕ) : MemPayload M r T w₀ y :=
  ((run M w ((y + 1) * r)).state, posCode T (run M w ((y + 1) * r)).inPos,
    fun t => posCode T ((run M w ((y + 1) * r)).workPos t),
    fun t c => (run M w ((y + 1) * r)).work t c.1)

/-- The payload of the chord edge `x → z` on input `w`, at time `z r`. -/
noncomputable def chordPayload (w : List Bool) (x z : ℕ) : ChordPayload M r T w₀ x z :=
  fun t c => (run M w (z * r)).work t c.1

/-- The value on edge `e` on input `w`: the index of its payload. -/
noncomputable def eData (w : List Bool) (e : ℕ × ℕ) : ℕ :=
  if e.2 = e.1 + 1 then
    (Fintype.equivFin (MemPayload M r T w₀ e.1) (memPayload M r T w₀ w e.1) : ℕ)
  else (Fintype.equivFin (ChordPayload M r T w₀ e.1 e.2) (chordPayload M r T w₀ w e.1 e.2) : ℕ)

theorem eData_mem (w : List Bool) (y : ℕ) :
    eData M r T w₀ w (y, y + 1) =
      (Fintype.equivFin (MemPayload M r T w₀ y) (memPayload M r T w₀ w y) : ℕ) := by
  simp [eData]

theorem eData_chord (w : List Bool) {x z : ℕ} (h : z ≠ x + 1) :
    eData M r T w₀ w (x, z) =
      (Fintype.equivFin (ChordPayload M r T w₀ x z) (chordPayload M r T w₀ w x z) : ℕ) := by
  simp [eData, h]

theorem memPayload_eq_of_eData {w w' : List Bool} {y : ℕ}
    (h : eData M r T w₀ w (y, y + 1) = eData M r T w₀ w' (y, y + 1)) :
    memPayload M r T w₀ w y = memPayload M r T w₀ w' y := by
  rw [eData_mem, eData_mem] at h
  exact (Fintype.equivFin _).injective (Fin.val_injective h)

theorem chordPayload_eq_of_eData {w w' : List Bool} {x z : ℕ} (hz : z ≠ x + 1)
    (h : eData M r T w₀ w (x, z) = eData M r T w₀ w' (x, z)) :
    chordPayload M r T w₀ w x z = chordPayload M r T w₀ w' x z := by
  rw [eData_chord _ _ _ _ _ hz, eData_chord _ _ _ _ _ hz] at h
  exact (Fintype.equivFin _).injective (Fin.val_injective h)

theorem card_memCells_le (t : Fin M.k) (y : ℕ) :
    (memCells M r T w₀ t y).card ≤ (resT M r T w₀ t y).card * r := by
  unfold memCells
  calc _ ≤ ∑ β ∈ resT M r T w₀ t y, (blockCells r β).card := Finset.card_biUnion_le
    _ = (resT M r T w₀ t y).card * r := by simp [card_blockCells]

theorem card_chordCells_le (hr : 1 ≤ r) (t : Fin M.k) (x z : ℕ) :
    (chordCells M r T w₀ t x z).card ≤ r := by
  classical
  unfold chordCells
  have h1 : ((resT M r T w₀ t z).filter (fun β => IsChord (resT M r T w₀ t) β x z)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro β hβ β' hβ'
    exact (pairRes_chord_target_unique (unitSteps_workTraj M w₀ t) hr T
      (Finset.mem_filter.1 hβ).2 (Finset.mem_filter.1 hβ').2).1
  calc _ ≤ ∑ β ∈ (resT M r T w₀ t z).filter (fun β => IsChord (resT M r T w₀ t) β x z),
        (blockCells r β).card := Finset.card_biUnion_le
    _ = ((resT M r T w₀ t z).filter (fun β => IsChord (resT M r T w₀ t) β x z)).card * r := by
        simp [card_blockCells]
    _ ≤ 1 * r := Nat.mul_le_mul_right r h1
    _ = r := Nat.one_mul r

theorem pow_le_two_pow_clog (a m : ℕ) : a ^ m ≤ 2 ^ (Nat.clog 2 a * m) := by
  rw [pow_mul]
  exact Nat.pow_le_pow_left (Nat.le_pow_clog (by norm_num) a) m

/-- A memory edge `y → y+1` needs `⌈log₂(q+1)⌉ + (k+1)⌈log₂(2T+1)⌉ + r⌈log₂(g+1)⌉` bits per block
resident at slot `y`. -/
theorem card_memPayload_le (y : ℕ) :
    Fintype.card (MemPayload M r T w₀ y) ≤
      2 ^ (Nat.clog 2 (M.q + 1) + (M.k + 1) * Nat.clog 2 (2 * T + 1) +
        (∑ t, (resT M r T w₀ t y).card) * r * Nat.clog 2 (M.g + 1)) := by
  simp only [MemPayload, Fintype.card_prod, Fintype.card_fin, Fintype.card_fun, Fintype.card_pi,
    Fintype.card_coe]
  have h1 : M.q + 1 ≤ 2 ^ Nat.clog 2 (M.q + 1) := Nat.le_pow_clog (by norm_num) _
  have h2 : 2 * T + 1 ≤ 2 ^ Nat.clog 2 (2 * T + 1) := Nat.le_pow_clog (by norm_num) _
  have h3 : (2 * T + 1) ^ M.k ≤ 2 ^ (Nat.clog 2 (2 * T + 1) * M.k) := pow_le_two_pow_clog _ _
  have h4 : ∏ t : Fin M.k, (M.g + 1) ^ (memCells M r T w₀ t y).card ≤
      2 ^ (Nat.clog 2 (M.g + 1) * (r * ∑ t, (resT M r T w₀ t y).card)) := by
    calc ∏ t : Fin M.k, (M.g + 1) ^ (memCells M r T w₀ t y).card
        ≤ ∏ t : Fin M.k, (M.g + 1) ^ (r * (resT M r T w₀ t y).card) :=
          Finset.prod_le_prod (fun t _ => Nat.pow_le_pow_right (Nat.succ_pos _)
            (by rw [Nat.mul_comm]; exact card_memCells_le M r T w₀ t y))
      _ = (M.g + 1) ^ (r * ∑ t, (resT M r T w₀ t y).card) := by
          rw [Finset.prod_pow_eq_pow_sum, ← Finset.mul_sum]
      _ ≤ _ := pow_le_two_pow_clog _ _
  calc (M.q + 1) * ((2 * T + 1) * ((2 * T + 1) ^ M.k *
        ∏ t : Fin M.k, (M.g + 1) ^ (memCells M r T w₀ t y).card))
      ≤ 2 ^ Nat.clog 2 (M.q + 1) * (2 ^ Nat.clog 2 (2 * T + 1) *
          (2 ^ (Nat.clog 2 (2 * T + 1) * M.k) *
            2 ^ (Nat.clog 2 (M.g + 1) * (r * ∑ t, (resT M r T w₀ t y).card)))) := by
        gcongr
    _ = _ := by
        rw [← pow_add, ← pow_add, ← pow_add]
        congr 1
        ring

open Classical in
/-- A chord edge needs `r ⌈log₂(g+1)⌉` bits per tape having that chord. -/
theorem card_chordPayload_le (hr : 1 ≤ r) (x z : ℕ) :
    Fintype.card (ChordPayload M r T w₀ x z) ≤
      2 ^ ((Finset.univ.filter (fun t : Fin M.k =>
        ∃ β : ℤ, IsChord (resT M r T w₀ t) β x z)).card * r * Nat.clog 2 (M.g + 1)) := by
  simp only [ChordPayload, Fintype.card_fin, Fintype.card_fun, Fintype.card_pi, Fintype.card_coe]
  have hcell : ∀ t : Fin M.k, (chordCells M r T w₀ t x z).card ≤
      r * (if ∃ β : ℤ, IsChord (resT M r T w₀ t) β x z then 1 else 0) := by
    intro t
    split_ifs with h
    · rw [Nat.mul_one]; exact card_chordCells_le M r T w₀ hr t x z
    · have : chordCells M r T w₀ t x z = ∅ := by
        unfold chordCells
        rw [Finset.filter_false_of_mem (fun β _ hβ => h ⟨β, hβ⟩), Finset.biUnion_empty]
      rw [this, Finset.card_empty]
      exact Nat.zero_le _
  calc ∏ t : Fin M.k, (M.g + 1) ^ (chordCells M r T w₀ t x z).card
      ≤ ∏ t : Fin M.k, (M.g + 1) ^ (r * (if ∃ β : ℤ, IsChord (resT M r T w₀ t) β x z then 1 else 0)) :=
        Finset.prod_le_prod (fun t _ => Nat.pow_le_pow_right (Nat.succ_pos _) (hcell t))
    _ = (M.g + 1) ^ (r * (Finset.univ.filter (fun t : Fin M.k =>
          ∃ β : ℤ, IsChord (resT M r T w₀ t) β x z)).card) := by
        rw [Finset.prod_pow_eq_pow_sum, ← Finset.mul_sum, Finset.sum_boole, Nat.cast_id]
    _ ≤ 2 ^ (Nat.clog 2 (M.g + 1) * (r * (Finset.univ.filter (fun t : Fin M.k =>
          ∃ β : ℤ, IsChord (resT M r T w₀ t) β x z)).card)) := pow_le_two_pow_clog _ _
    _ = _ := by congr 1; ring

end Payload

/-! ### Node locality on a trace class -/

section Class

variable {n b r T : ℕ} {F : Set (List Bool)} {w₀ : List Bool}

theorem res_eq_of_mem (hr : 1 ≤ r) (hF : TraceClass M n b r T F w₀) {w : List Bool} (hw : w ∈ F)
    (t : Fin M.k) : pairRes r (fun τ => workTraj M w τ t) T = resT M r T w₀ t :=
  pairRes_eq_of_sameTrace hr (hF.2 w hw).2.2 t

theorem cur_mem_resT (hr : 1 ≤ r) (hF : TraceClass M n b r T F w₀) {w : List Bool} (hw : w ∈ F)
    (t : Fin M.k) {σ : ℕ} (hσ : σ < T) :
    blockOf r ((run M w σ).workPos t) ∈ resT M r T w₀ t (σ / r) := by
  rw [← res_eq_of_mem hr hF hw t]
  exact cur_mem_pairRes (h := fun τ => workTraj M w τ t) hr hσ

/-- **Contents at the start of a slot.** If `w, w' ∈ F` have equal values on the edges into `y`,
the contents of the blocks resident at slot `y` agree at time `y r`. A block resident at `y - 1`
comes by the memory edge, a block resident earlier but not at `y - 1` by the chord from its last
earlier resident slot, and a block never resident before `y` is blank. -/
theorem content_start (hr : 1 ≤ r) (hF : TraceClass M n b r T F w₀) {w w' : List Bool}
    (hw : w ∈ F) (hw' : w' ∈ F) {y : ℕ} (hy : y < numSlots r T)
    (hin : ∀ e ∈ (runDiagram M w₀ T).edges r, e.2 = y →
      eData M r T w₀ w' e = eData M r T w₀ w e)
    (t : Fin M.k) (c : ℤ) (hc : blockOf r c ∈ resT M r T w₀ t y) :
    (run M w (y * r)).work t c = (run M w' (y * r)).work t c := by
  classical
  by_cases hprev : ∃ y' < y, blockOf r c ∈ resT M r T w₀ t y'
  · obtain ⟨u, rfl⟩ : ∃ u, y = u + 1 := ⟨y - 1, by obtain ⟨y', hy', -⟩ := hprev; omega⟩
    by_cases hu : blockOf r c ∈ resT M r T w₀ t u
    · -- the memory edge `(u, u + 1)`
      have he : (u, u + 1) ∈ (runDiagram M w₀ T).edges r := by
        apply Finset.mem_union_left
        rw [mem_memEdges]; exact ⟨rfl, hy⟩
      have h' := memPayload_eq_of_eData M r T w₀ (hin (u, u + 1) he rfl)
      have hcm : c ∈ memCells M r T w₀ t u :=
        Finset.mem_biUnion.2 ⟨blockOf r c, hu, (mem_blockCells hr).2 rfl⟩
      have := congrFun (congrFun (congrArg (fun p => p.2.2.2) h') t) ⟨c, hcm⟩
      simpa [memPayload] using this.symm
    · -- the chord from the last earlier resident slot
      obtain ⟨y₁, hy₁, hP₁⟩ := hprev
      set x := Nat.findGreatest (fun y' => blockOf r c ∈ resT M r T w₀ t y') u with hx
      have hPx : blockOf r c ∈ resT M r T w₀ t x :=
        Nat.findGreatest_spec (P := fun y' => blockOf r c ∈ resT M r T w₀ t y')
          (show y₁ ≤ u by omega) hP₁
      have hxu : x < u := lt_of_le_of_ne (Nat.findGreatest_le u) (fun h => hu (h ▸ hPx))
      have hchord : IsChord (resT M r T w₀ t) (blockOf r c) x (u + 1) := by
        refine ⟨by omega, hPx, hc, fun y' h1 h2 hy' => ?_⟩
        exact Nat.findGreatest_is_greatest (P := fun y' => blockOf r c ∈ resT M r T w₀ t y')
          h1 (by omega) hy'
      have he : (x, u + 1) ∈ (runDiagram M w₀ T).edges r := by
        apply Finset.mem_union_right
        rw [mem_chordEdges]
        exact ⟨(show x < numSlots r T by omega), hy, t, blockOf r c, hchord⟩
      have hne : u + 1 ≠ x + 1 := by omega
      have h' := chordPayload_eq_of_eData M r T w₀ hne (hin (x, u + 1) he rfl)
      have hcc : c ∈ chordCells M r T w₀ t x (u + 1) :=
        Finset.mem_biUnion.2 ⟨blockOf r c, Finset.mem_filter.2 ⟨hc, hchord⟩,
          (mem_blockCells hr).2 rfl⟩
      have := congrFun (congrFun h' t) ⟨c, hcc⟩
      simpa [chordPayload] using this.symm
  · -- never resident before `y`: blank in both runs
    push Not at hprev
    have hblank : ∀ v ∈ F, (run M v (y * r)).work t c = 0 := by
      intro v hv
      apply work_eq_blank
      intro σ hσ hpos
      have hσT : σ < T := lt_trans hσ ((numSlots_spec hr).1 hy)
      have := cur_mem_resT hr hF hv t hσT
      rw [hpos] at this
      have hσy : σ / r < y := by
        rw [Nat.div_lt_iff_lt_mul (by omega)]; exact hσ
      exact hprev _ hσy this
    rw [hblank w hw, hblank w' hw']

/-- **The configuration at the start of a slot** `y = u + 1 ≥ 1` comes by the memory edge. -/
theorem config_start (hr : 1 ≤ r) {w w' : List Bool} {u : ℕ} (hy : u + 1 < numSlots r T)
    (hin : ∀ e ∈ (runDiagram M w₀ T).edges r, e.2 = u + 1 →
      eData M r T w₀ w' e = eData M r T w₀ w e) :
    (run M w ((u + 1) * r)).state = (run M w' ((u + 1) * r)).state ∧
    (run M w ((u + 1) * r)).inPos = (run M w' ((u + 1) * r)).inPos ∧
    (run M w ((u + 1) * r)).workPos = (run M w' ((u + 1) * r)).workPos := by
  have he : (u, u + 1) ∈ (runDiagram M w₀ T).edges r := by
    apply Finset.mem_union_left
    rw [mem_memEdges]; exact ⟨rfl, hy⟩
  have h' := memPayload_eq_of_eData M r T w₀ (hin (u, u + 1) he rfl)
  simp only [memPayload, Prod.mk.injEq] at h'
  obtain ⟨hs, hi, hwp, -⟩ := h'
  have hT : (((u + 1) * r : ℕ) : ℤ) ≤ T := by
    exact_mod_cast le_of_lt ((numSlots_spec hr).1 hy)
  refine ⟨hs.symm, ?_, ?_⟩
  · exact (posCode_inj (le_trans (abs_inPos_le _ _) hT) (le_trans (abs_inPos_le _ _) hT) hi).symm
  · funext t
    exact (posCode_inj (le_trans (abs_workPos_le _ _ t) hT) (le_trans (abs_workPos_le _ _ t) hT)
      (congrFun hwp t)).symm

/-- The agreement of two runs at every step of slot `y` (the conclusion of the Block Locality
Lemma). -/
def SlotAgree (M : TM) (r T : ℕ) (w w' : List Bool) (y : ℕ) : Prop :=
  ∀ τ ∈ slotSteps r {y} T,
    (run M w τ).state = (run M w' τ).state ∧ (run M w τ).inPos = (run M w' τ).inPos ∧
    (run M w τ).workPos = (run M w' τ).workPos ∧
    (run M w τ).outRev.length = (run M w' τ).outRev.length ∧
    headSym M w τ = headSym M w' τ ∧ transAt M w τ = transAt M w' τ

/-- **The Block Locality Lemma for one slot.** If `w, w' ∈ F` have equal values on the edges into
`y` and agree on the input rows touched during slot `y`, the runs agree at every step of slot
`y`. -/
theorem slot_local (hr : 1 ≤ r) (hF : TraceClass M n b r T F w₀) {w w' : List Bool}
    (hw : w ∈ F) (hw' : w' ∈ F) {y : ℕ} (hy : y < numSlots r T)
    (hin : ∀ e ∈ (runDiagram M w₀ T).edges r, e.2 = y →
      eData M r T w₀ w' e = eData M r T w₀ w e)
    (hrows : ∀ d < n * n * b, d / (n * b) ∈ srcRows M w₀ n b (slotOf r T y) →
      nth w d = nth w' d) :
    SlotAgree M r T w w' y := by
  classical
  have hwF := hF.2 w hw
  have hwF' := hF.2 w' hw'
  have htrace : SameTrace M n b r T w w' := sameTrace_trans hwF.2.2 (sameTrace_symm hwF'.2.2)
  apply block_locality hr (length_of_mem_matrixInputs hwF.1) (length_of_mem_matrixInputs hwF'.1) htrace
  · intro z hz
    rw [mem_memBoundaries] at hz
    obtain ⟨-, hzU, hz1, -⟩ := hz
    have hzy : z = y := hzU
    rw [hzy]
    rw [hzy] at hz1
    obtain ⟨u, rfl⟩ : ∃ u, y = u + 1 := ⟨y - 1, by omega⟩
    obtain ⟨hs, hi, hwp⟩ := config_start hr hy hin
    refine ⟨hs, hi, hwp, fun t c hc => ?_⟩
    rw [res_eq_of_mem hr hF hw t] at hc
    exact content_start hr hF hw hw' hy hin t c hc
  · intro t p hp c hc
    rcases p with ⟨z, β⟩
    rw [mem_chordsInto] at hp
    obtain ⟨-, hzU, hβ, -⟩ := hp
    have hzy : z = y := hzU
    rw [res_eq_of_mem hr hF hw t, hzy] at hβ
    simp only at hc ⊢
    rw [hzy]
    exact content_start hr hF hw hw' hy hin t c (by rw [hc]; exact hβ)
  · intro d hd hrow
    apply hrows d hd
    rw [srcRows_slotSteps_eq hr] at hrow
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_range] at hrow
    obtain ⟨y', ⟨-, hy'U⟩, hrow⟩ := hrow
    have hy'y : y' = y := hy'U
    rw [hy'y, sameTrace_srcRows hwF.2.2 hy.le] at hrow
    exact hrow

/-- **Contents at the end of a slot.** Under the hypotheses of `slot_local`, the contents of the
blocks resident at slot `y` agree at every time of `[y r, (y+1) r] ∩ [0, T]`. -/
theorem content_end (hr : 1 ≤ r) (hF : TraceClass M n b r T F w₀) {w w' : List Bool}
    (hw : w ∈ F) (hw' : w' ∈ F) {y : ℕ} (hy : y < numSlots r T)
    (hin : ∀ e ∈ (runDiagram M w₀ T).edges r, e.2 = y →
      eData M r T w₀ w' e = eData M r T w₀ w e)
    (hloc : SlotAgree M r T w w' y) (t : Fin M.k) (c : ℤ)
    (hc : blockOf r c ∈ resT M r T w₀ t y) :
    ∀ j, j ≤ r → y * r + j ≤ T →
      (run M w (y * r + j)).work t c = (run M w' (y * r + j)).work t c := by
  intro j
  induction j with
  | zero => intro _ _; simpa using content_start hr hF hw hw' hy hin t c hc
  | succ j ih =>
    intro hj hjT
    have hτ : y * r + j ∈ slotSteps r {y} T := by
      rw [mem_slotSteps]
      refine ⟨by omega, ?_⟩
      show (y * r + j) / r = y
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt (by omega),
        Nat.zero_add]
    obtain ⟨-, -, hwp, -, hhs, htr⟩ := hloc _ hτ
    rw [← Nat.add_assoc, run_succ_work, run_succ_work, ← hwp, writtenSym_eq_of_transAt' hhs htr t,
      ih (by omega) (by omega)]

/-- **The payloads out of a slot** agree. -/
theorem out_edges (hr : 1 ≤ r) (hF : TraceClass M n b r T F w₀) {w w' : List Bool}
    (hw : w ∈ F) (hw' : w' ∈ F) {y : ℕ} (hy : y < numSlots r T)
    (hin : ∀ e ∈ (runDiagram M w₀ T).edges r, e.2 = y →
      eData M r T w₀ w' e = eData M r T w₀ w e)
    (hloc : SlotAgree M r T w w' y) :
    ∀ e ∈ (runDiagram M w₀ T).edges r, e.1 = y → eData M r T w₀ w' e = eData M r T w₀ w e := by
  intro e he he1
  rcases e with ⟨x, z⟩
  simp only at he1
  subst x
  have hzN : z < numSlots r T := (edges_lt (runDiagram M w₀ T) (y, z) he).2
  have hyz : y < z := edges_fst_lt (runDiagram M w₀ T) (y, z) he
  have hzT : z * r < T := (numSlots_spec hr).1 hzN
  have hzle : (y + 1) * r ≤ z * r := Nat.mul_le_mul_right r hyz
  have hy1T : y * r + r ≤ T := by
    rw [Nat.add_mul, Nat.one_mul] at hzle; omega
  have hend : ∀ t c, blockOf r c ∈ resT M r T w₀ t y →
      (run M w ((y + 1) * r)).work t c = (run M w' ((y + 1) * r)).work t c := by
    intro t c hc
    have := content_end hr hF hw hw' hy hin hloc t c hc r le_rfl hy1T
    rwa [show y * r + r = (y + 1) * r by ring] at this
  by_cases hmem : z = y + 1
  · subst hmem
    rw [eData_mem, eData_mem]
    have hτ : y * r + (r - 1) ∈ slotSteps r {y} T := by
      rw [mem_slotSteps]
      refine ⟨by omega, ?_⟩
      show (y * r + (r - 1)) / r = y
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt (by omega),
        Nat.zero_add]
    obtain ⟨hs, hi, hwp, hl, -, htr⟩ := hloc _ hτ
    have hcfg := cfgAgree_succ ⟨hs, hi, hwp, hl⟩ htr
    have he' : y * r + (r - 1) + 1 = (y + 1) * r := by
      rw [Nat.add_mul, Nat.one_mul]; omega
    rw [he'] at hcfg
    obtain ⟨hs', hi', hwp', -⟩ := hcfg
    have hp : memPayload M r T w₀ w' y = memPayload M r T w₀ w y := by
      simp only [memPayload, Prod.mk.injEq]
      refine ⟨hs'.symm, by rw [hi'], by rw [hwp'], ?_⟩
      funext t c
      obtain ⟨β, hβ, hcβ⟩ := Finset.mem_biUnion.1 c.2
      exact (hend t c.1 (by rw [(mem_blockCells hr).1 hcβ]; exact hβ)).symm
    rw [hp]
  · rw [eData_chord _ _ _ _ _ hmem, eData_chord _ _ _ _ _ hmem]
    have hp : chordPayload M r T w₀ w' y z = chordPayload M r T w₀ w y z := by
      funext t c
      classical
      obtain ⟨β, hβ, hcβ⟩ := Finset.mem_biUnion.1 c.2
      have hch : IsChord (resT M r T w₀ t) β y z := (Finset.mem_filter.1 hβ).2
      have hcb : blockOf r c.1 = β := (mem_blockCells hr).1 hcβ
      -- no visits to the cell during `[(y+1) r, z r)`
      have hnv : ∀ v ∈ F, ∀ σ, (y + 1) * r ≤ σ → σ < z * r → (run M v σ).workPos t ≠ c.1 := by
        intro v hv σ h1 h2 hpos
        have hσT : σ < T := lt_trans h2 hzT
        have := cur_mem_resT hr hF hv t hσT
        rw [hpos, hcb] at this
        have hσ1 : y + 1 ≤ σ / r := (Nat.le_div_iff_mul_le (by omega)).2 h1
        have hσ2 : σ / r < z := by rw [Nat.div_lt_iff_lt_mul (by omega)]; exact h2
        exact hch.2.2.2 _ (by omega) hσ2 this
      simp only [chordPayload]
      rw [work_eq_of_no_visit t c.1 hzle (hnv w' hw'), work_eq_of_no_visit t c.1 hzle (hnv w hw)]
      exact (hend t c.1 (by rw [hcb]; exact hch.2.1)).symm
    rw [hp]

/-- **The output bits of a slot** agree: the step appending bit `o` lies in its sink's slot
(`outNode_eq`, the output lengths at slot boundaries being those of the representative). -/
theorem out_bits (hr : 1 ≤ r) (hcorr : ClassCorrect M n b T F) (hF : TraceClass M n b r T F w₀)
    {w w' : List Bool} (hw : w ∈ F) {y : ℕ} (hloc : SlotAgree M r T w w' y) {o : ℕ}
    (ho : o < n * n * b) (hoy : (runDiagram M w₀ T).outNode r o = y) :
    nth (run M w' T).outRev.reverse o = nth (run M w T).outRev.reverse o := by
  have hwF := hF.2 w hw
  have hlen : (run M w T).outRev.length = n * n * b := outLen_of_classCorrect hcorr hw
  obtain ⟨τ, hτT, hsome, hτo⟩ :=
    exists_append_step (M := M) w (show o < (run M w T).outRev.length by rw [hlen]; exact ho)
  have hy0 : τ / r < numSlots r T := div_lt_numSlots hr hτT
  have hDv := runDiagram_valid (outLen_of_classCorrect hcorr hF.1) (hF.2 w₀ hF.1).2.1
  have h1 := outRev_length_mono (M := M) w (Nat.div_mul_le_self τ r)
  have h2 := outRev_length_mono (M := M) w (show τ + 1 ≤ (τ / r + 1) * r by
    have := Nat.lt_mul_div_succ τ (show 0 < r by omega); rw [Nat.mul_comm] at this; omega)
  have h3 := outRev_length_succ (M := M) w τ
  rw [ite_eq_left_iff.2 (fun h => absurd hsome h)] at h3
  have h4 := sameTrace_outLen hwF.2.2 (y := τ / r) hy0.le
  have h5 := sameTrace_outLen hwF.2.2 (y := τ / r + 1) hy0
  have hτy : τ / r = y := by
    rw [← hoy]; symm
    exact outNode_eq hDv hy0 (show (run M w₀ (τ / r * r)).outRev.length ≤ o by omega)
      (show o < (run M w₀ ((τ / r + 1) * r)).outRev.length by omega)
  obtain ⟨-, -, -, hl, -, htr⟩ := hloc τ (mem_slotSteps.2 ⟨hτT, hτy⟩)
  have hob : outBit M w τ = outBit M w' τ := by simp only [outBit, htr]
  calc nth (run M w' T).outRev.reverse o
      = nth (run M w' T).outRev.reverse (run M w' τ).outRev.length := by rw [← hl, hτo]
    _ = outBit M w' τ := output_nth_eq_outBit w' hτT (by rw [← hob]; exact hsome)
    _ = nth (run M w T).outRev.reverse o := by
        rw [← hob, ← hτo]; exact (output_nth_eq_outBit w hτT hsome).symm

/-! ### The code of a trace class -/

/-- `w'` is **consistent** at node `y` with the values `f` on the edges into `y` and the visible
input `v`. -/
def Consistent (M : TM) (n b r T : ℕ) (w₀ w' : List Bool) (y : ℕ) (f : ℕ × ℕ → ℕ)
    (v : ℕ → Bool) : Prop :=
  (∀ e ∈ (runDiagram M w₀ T).edges r, e.2 = y → eData M r T w₀ w' e = f e) ∧
    (runDiagram M w₀ T).visible n b r y (toVec (n * n * b) w') = v

open Classical in
/-- **The code of a trace class.** Each node chooses a member of `F` consistent with the values it
receives and its visible input, and sends that member's payloads; the decoder outputs that member's
output bit. -/
noncomputable def classCode (M : TM) (n b r T : ℕ) (F : Set (List Bool)) (w₀ : List Bool) :
    NetCode where
  enc e f v := if h : ∃ w' ∈ F, Consistent M n b r T w₀ w' e.1 f v then
    eData M r T w₀ (Classical.choose h) e else 0
  dec o f v := if h : ∃ w' ∈ F, Consistent M n b r T w₀ w' ((runDiagram M w₀ T).outNode r o) f v
    then (nth (run M (Classical.choose h) T).outRev.reverse o).getD false else false

open Classical in
theorem classCode_enc (M : TM) (n b r T : ℕ) (F : Set (List Bool)) (w₀ : List Bool) (e : ℕ × ℕ)
    (f : ℕ × ℕ → ℕ) (v : ℕ → Bool) :
    (classCode M n b r T F w₀).enc e f v =
      if h : ∃ w' ∈ F, Consistent M n b r T w₀ w' e.1 f v then
        eData M r T w₀ (Classical.choose h) e else 0 := rfl

open Classical in
theorem classCode_dec (M : TM) (n b r T : ℕ) (F : Set (List Bool)) (w₀ : List Bool) (o : ℕ)
    (f : ℕ × ℕ → ℕ) (v : ℕ → Bool) :
    (classCode M n b r T F w₀).dec o f v =
      if h : ∃ w' ∈ F, Consistent M n b r T w₀ w' ((runDiagram M w₀ T).outNode r o) f v
      then (nth (run M (Classical.choose h) T).outRev.reverse o).getD false else false := rfl

/-- **The Block Locality Lemma in functional form.** Two members of `F` consistent with the same
data at node `y` have the same payloads on the edges out of `y` and the same output bits at `y`. -/
theorem consistent_agree (hr : 1 ≤ r) (hcorr : ClassCorrect M n b T F)
    (hF : TraceClass M n b r T F w₀) {w w' : List Bool} (hw : w ∈ F) (hw' : w' ∈ F) {y : ℕ}
    (hy : y < numSlots r T) {f : ℕ × ℕ → ℕ} {v : ℕ → Bool}
    (hc : Consistent M n b r T w₀ w y f v) (hc' : Consistent M n b r T w₀ w' y f v) :
    (∀ e ∈ (runDiagram M w₀ T).edges r, e.1 = y → eData M r T w₀ w' e = eData M r T w₀ w e) ∧
    (∀ o < n * n * b, (runDiagram M w₀ T).outNode r o = y →
      nth (run M w' T).outRev.reverse o = nth (run M w T).outRev.reverse o) := by
  classical
  have hin : ∀ e ∈ (runDiagram M w₀ T).edges r, e.2 = y →
      eData M r T w₀ w' e = eData M r T w₀ w e :=
    fun e he he2 => (hc'.1 e he he2).trans (hc.1 e he he2).symm
  have hlen := length_of_mem_matrixInputs (hF.2 w hw).1
  have hlen' := length_of_mem_matrixInputs (hF.2 w' hw').1
  have hrows : ∀ d < n * n * b, d / (n * b) ∈ srcRows M w₀ n b (slotOf r T y) →
      nth w d = nth w' d := by
    intro d hd hrow
    have hv := congrFun (hc.2.trans hc'.2.symm) d
    have hrow' : d / (n * b) ∈ (runDiagram M w₀ T).rowsAt n b r y := hrow
    simp only [TSDiagram.visible, hd, dite_true, hrow', ite_true, toVec] at hv
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at hv
    rw [nth_eq_getElem?, nth_eq_getElem?, List.getElem?_eq_getElem (by omega),
      List.getElem?_eq_getElem (by omega), hv]
  have hloc := slot_local hr hF hw hw' hy hin hrows
  exact ⟨out_edges hr hF hw hw' hy hin hloc, fun o ho hoy => out_bits hr hcorr hF hw hloc ho hoy⟩

/-- **The code computes the payloads.** On an input `x` of the class, the value the code puts on
every edge is the payload of `x`. -/
theorem classCode_edgeVal (hr : 1 ≤ r) (hcorr : ClassCorrect M n b T F)
    (hF : TraceClass M n b r T F w₀) {x : Fin (n * n * b) → Bool} (hx : List.ofFn x ∈ F) :
    ∀ u, ∀ e ∈ (runDiagram M w₀ T).edges r, e.1 = u →
      (classCode M n b r T F w₀).edgeVal ((runDiagram M w₀ T).edges r)
        (fun y => (runDiagram M w₀ T).visible n b r y x) e = eData M r T w₀ (List.ofFn x) e := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
  intro e he heu
  subst heu
  have hcons : Consistent M n b r T w₀ (List.ofFn x) e.1
      ((classCode M n b r T F w₀).inVals ((runDiagram M w₀ T).edges r)
        (fun y => (runDiagram M w₀ T).visible n b r y x) e.1)
      ((runDiagram M w₀ T).visible n b r e.1 x) := by
    refine ⟨fun e' he' he'2 => ?_, by rw [toVec_ofFn]⟩
    have hlt : e'.1 < e.1 := he'2 ▸ edges_fst_lt _ e' he'
    rw [inVals_eq, ite_eq_left_of_eq_true _ _ (eq_true ⟨he', he'2, hlt⟩)]
    exact (ih e'.1 hlt e' he' rfl).symm
  have hex : ∃ w' ∈ F, Consistent M n b r T w₀ w' e.1
      ((classCode M n b r T F w₀).inVals ((runDiagram M w₀ T).edges r)
        (fun y => (runDiagram M w₀ T).visible n b r y x) e.1)
      ((runDiagram M w₀ T).visible n b r e.1 x) := ⟨_, hx, hcons⟩
  have hu : e.1 < numSlots r T := (edges_lt _ e he).1
  show (classCode M n b r T F w₀).enc e _ _ = _
  rw [classCode_enc, dite_eq_left hex]
  exact (consistent_agree hr hcorr hF hx (Classical.choose_spec hex).1 hu hcons
    (Classical.choose_spec hex).2).1 e he rfl

/-- **A trace class is a network code.** -/
theorem classCode_solves {n T : ℕ} (hn : 1 ≤ n) {F : Set (List Bool)} {w₀ : List Bool}
    (hcorr : ClassCorrect M n (entryBits n) T F)
    (hF : TraceClass M n (entryBits n) (slotLen M n) T F w₀) (cap : ℕ × ℕ → ℕ)
    (hcap : ∀ e ∈ (runDiagram M w₀ T).edges (slotLen M n),
      ∀ w ∈ F, eData M (slotLen M n) T w₀ w e < 2 ^ cap e) :
    (runDiagram M w₀ T).Solves n (cellBits M) cap {v | List.ofFn v ∈ F}
      (classCode M n (entryBits n) (slotLen M n) T F w₀) := by
  classical
  have hr := one_le_slotLen M hn
  intro x hx
  have hx' : List.ofFn x ∈ F := hx
  refine ⟨fun e he => ?_, fun d hd => ?_⟩
  · have := classCode_edgeVal hr hcorr hF hx' e.1 e he rfl
    show (classCode M n (entryBits n) (slotLen M n) T F w₀).edgeVal
      ((runDiagram M w₀ T).edges (slotLen M n))
      (fun y => (runDiagram M w₀ T).visible n (entryBits n) (slotLen M n) y x) e < 2 ^ cap e
    rw [this]
    exact hcap e he _ hx'
  · -- the sink of `tpos d`
    set o := tpos n (entryBits n) d with ho
    have hoL : o < n * n * entryBits n := tpos_lt hd
    set s := (runDiagram M w₀ T).outNode (slotLen M n) o with hs
    have hwF := hF.2 _ hx'
    -- `T ≥ 1` and `s < N`
    have hlen : (run M (List.ofFn x) T).outRev.length = n * n * entryBits n :=
      outLen_of_classCorrect hcorr hx'
    have hT1 : 1 ≤ T := by
      have := outLen_le_self (M := M) (List.ofFn x) T
      omega
    have hN : 1 ≤ numSlots (slotLen M n) T := by
      rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, numSlots_spec hr]; omega
    have hsN : s < numSlots (slotLen M n) T := by
      have : s ≤ numSlots (slotLen M n) T - 1 := Nat.findGreatest_le _
      omega
    -- the values into `s` are the payloads, so `ofFn x` is consistent at `s`
    have hcons : Consistent M n (entryBits n) (slotLen M n) T w₀ (List.ofFn x) s
        ((classCode M n (entryBits n) (slotLen M n) T F w₀).inVals
          ((runDiagram M w₀ T).edges (slotLen M n))
          (fun y => (runDiagram M w₀ T).visible n (entryBits n) (slotLen M n) y x) s)
        ((runDiagram M w₀ T).visible n (entryBits n) (slotLen M n) s x) := by
      refine ⟨fun e' he' he'2 => ?_, by rw [toVec_ofFn]⟩
      have hlt : e'.1 < s := he'2 ▸ edges_fst_lt _ e' he'
      rw [inVals_eq, ite_eq_left_of_eq_true _ _ (eq_true ⟨he', he'2, hlt⟩)]
      exact (classCode_edgeVal hr hcorr hF hx' e'.1 e' he' rfl).symm
    have hex : ∃ w' ∈ F, Consistent M n (entryBits n) (slotLen M n) T w₀ w' s
        ((classCode M n (entryBits n) (slotLen M n) T F w₀).inVals
          ((runDiagram M w₀ T).edges (slotLen M n))
          (fun y => (runDiagram M w₀ T).visible n (entryBits n) (slotLen M n) y x) s)
        ((runDiagram M w₀ T).visible n (entryBits n) (slotLen M n) s x) := ⟨_, hx', hcons⟩
    show (classCode M n (entryBits n) (slotLen M n) T F w₀).dec o _ _ = _
    rw [classCode_dec]
    split_ifs with hh
    swap
    · exact absurd hex hh
    have hagree := (consistent_agree hr hcorr hF hx' (Classical.choose_spec hh).1 hsN hcons
      (Classical.choose_spec hh).2).2 o hoL rfl
    rw [hagree]
    -- the output of `ofFn x` at `tpos d` is `x d`
    obtain ⟨A, hA, hout⟩ := hcorr _ hx'
    rw [hout, ho, nth_encode_transpose_tpos A hd, ← hA, nth_ofFn x hd]
    rfl

/-- **A trace class is a network code** (the Block Locality Lemma in functional form). Let `M`
output the transposed encoding on every input of a trace class `F`. The time–space diagram of the
representative's run is valid, and its block network carries a causal code solving complete
exchange on the class, with the payload capacities:
* `⌈log₂(q+1)⌉ + (k+1)⌈log₂(2T+1)⌉ + r⌈log₂(g+1)⌉` bits per block resident at slot `y`, on a memory edge
  `y → y+1`;
* `r⌈log₂(g+1)⌉` bits per tape having the chord, on a chord edge. -/
theorem traceClass_code {n T : ℕ} (hn : 1 ≤ n) {F : Set (List Bool)} {w₀ : List Bool}
    (hF : TraceClass M n (entryBits n) (slotLen M n) T F w₀)
    (hcorr : ClassCorrect M n (entryBits n) T F) :
    ∃ (cap : ℕ × ℕ → ℕ) (code : NetCode),
      (runDiagram M w₀ T).Valid (n * n * entryBits n) ∧
      (runDiagram M w₀ T).Solves n (cellBits M) cap {v | List.ofFn v ∈ F} code ∧
      (∀ e ∈ (runDiagram M w₀ T).memEdges (slotLen M n), cap e ≤ Nat.clog 2 (M.q + 1) +
        (M.k + 1) * Nat.clog 2 (2 * T + 1) +
        (∑ t, (pairRes (slotLen M n) ((runDiagram M w₀ T).work t) (runDiagram M w₀ T).T e.1).card) *
          slotLen M n * Nat.clog 2 (M.g + 1)) ∧
      (∀ e ∈ (runDiagram M w₀ T).chordEdges (slotLen M n),
        cap e ≤ (runDiagram M w₀ T).chordTapes (slotLen M n) e * slotLen M n *
          Nat.clog 2 (M.g + 1)) ∧
      (∀ e, e ∉ (runDiagram M w₀ T).edges (slotLen M n) → cap e = 0) := by
  classical
  have hr := one_le_slotLen M hn
  set D := runDiagram M w₀ T with hD
  let capM : ℕ × ℕ → ℕ := fun e => Nat.clog 2 (M.q + 1) + (M.k + 1) * Nat.clog 2 (2 * T + 1) +
    (∑ t, (pairRes (slotLen M n) (D.work t) D.T e.1).card) * slotLen M n * Nat.clog 2 (M.g + 1)
  let cap : ℕ × ℕ → ℕ := fun e => if e ∈ D.memEdges (slotLen M n) then capM e
    else if e ∈ D.chordEdges (slotLen M n) then
      D.chordTapes (slotLen M n) e * slotLen M n * Nat.clog 2 (M.g + 1) else 0
  have hw₀ := hF.2 w₀ hF.1
  refine ⟨cap, classCode M n (entryBits n) (slotLen M n) T F w₀,
    runDiagram_valid (outLen_of_classCorrect hcorr hF.1) hw₀.2.1, ?_, fun e he => ?_,
    fun e he => ?_, fun e he => ?_⟩
  · apply classCode_solves hn hcorr hF
    intro e he w _
    rcases Finset.mem_union.1 he with hm | hc
    · have hcap : cap e = capM e := ite_eq_left hm
      rw [hcap]
      have hm' := (mem_memEdges D).1 hm
      obtain ⟨y, z⟩ := e
      simp only at hm'
      obtain ⟨rfl, -⟩ := hm'
      rw [eData_mem]
      exact lt_of_lt_of_le (Fin.isLt _) (card_memPayload_le M (slotLen M n) T w₀ y)
    · have hcap : cap e = D.chordTapes (slotLen M n) e * slotLen M n * Nat.clog 2 (M.g + 1) := by
        show (if e ∈ D.memEdges (slotLen M n) then capM e else _) = _
        rw [ite_eq_right (fun hm => not_mem_chordEdges_of_mem_memEdges D hm hc), ite_eq_left hc]
      rw [hcap]
      have hne : e.2 ≠ e.1 + 1 := by
        obtain ⟨-, -, t, β, hch⟩ := (mem_chordEdges D).1 hc
        have := hch.1
        omega
      obtain ⟨x, z⟩ := e
      rw [eData_chord _ _ _ _ _ hne]
      exact lt_of_lt_of_le (Fin.isLt _) (card_chordPayload_le M (slotLen M n) T w₀ hr x z)
  · show (if e ∈ D.memEdges (slotLen M n) then capM e else _) ≤ _
    rw [ite_eq_left he]
  · show (if e ∈ D.memEdges (slotLen M n) then capM e else _) ≤ _
    rw [ite_eq_right (fun hm => not_mem_chordEdges_of_mem_memEdges D hm he), ite_eq_left he]
  · show (if e ∈ D.memEdges (slotLen M n) then capM e else _) = 0
    rw [ite_eq_right (fun hm => he (Finset.mem_union_left _ hm)),
      ite_eq_right (fun hc => he (Finset.mem_union_right _ hc))]

end Class

/-! ### The code of a class, with extra bits: the single machine reduction -/

/-- **The code of a trace class at the per-node blocks plus `s` bits**, on the representative's own
diagram, if the state bits plus the head-position bits fit in `s`. This is the only step from a class
to a code (it fixes the capacities); every other capacity profile follows by TM-free conversions
(`solves_profileCap_addTapes`, `robustNoCode_bits_iff`). -/
theorem code_bits_of_class {n T s : ℕ} (hn1 : 1 ≤ n)
    (hs : Nat.clog 2 (M.q + 1) + (M.k + 1) * Nat.clog 2 (2 * T + 1) ≤ s)
    {F : Set (List Bool)} {w₀ : List Bool}
    (hF : TraceClass M n (entryBits n) (slotLen M n) T F w₀)
    (hcorr : ClassCorrect M n (entryBits n) T F) :
    ∃ code : NetCode, (runDiagram M w₀ T).Valid (n * n * entryBits n) ∧
      (runDiagram M w₀ T).Solves n (cellBits M) ((runDiagram M w₀ T).blockCap n (cellBits M)
        (fun y => ∑ t, (pairRes (blockSize (cellBits M) n) ((runDiagram M w₀ T).work t)
          (runDiagram M w₀ T).T y).card) s) {v | List.ofFn v ∈ F} code := by
  obtain ⟨cap, code, hDv, hsol, hmem, hchord, -⟩ := traceClass_code hn1 hF hcorr
  have hG : Nat.clog 2 (M.g + 1) ≤ cellBits M := le_max_right _ _
  refine ⟨code, hDv, solves_mono _ (fun e he => ?_) hsol⟩
  rcases Finset.mem_union.1 he with hm | hc
  · rw [blockCap_mem _ hm]
    have hme := hmem e hm
    set S := ∑ t, (pairRes (slotLen M n) ((runDiagram M w₀ T).work t)
      (runDiagram M w₀ T).T e.1).card with hS
    have h1 : S * slotLen M n * Nat.clog 2 (M.g + 1) ≤ S * (slotLen M n * cellBits M) := by
      rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hG)
    show cap e ≤ S * (slotLen M n * cellBits M) + s
    omega
  · rw [blockCap_chord _ hc]
    calc cap e ≤ _ := hchord e hc
      _ = (runDiagram M w₀ T).chordTapes (slotLen M n) e *
          (slotLen M n * Nat.clog 2 (M.g + 1)) := by ring
      _ ≤ (runDiagram M w₀ T).chordTapes (slotLen M n) e * (slotLen M n * cellBits M) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hG)

/-- **The rescaled walks of a run's diagram are the machine's rescaled trajectories** when the run
halts at `T` (the heads are frozen after halting). -/
theorem rescaled_runDiagram {n T : ℕ} {w : List Bool} (hT : HaltsAt M w T) (t : Fin M.k) :
    (runDiagram M w T).rescaled n (cellBits M) t = rescaledTrajOf M n w t := by
  funext u
  show (curBlock (slotLen M n) (fun τ => workTraj M w (min τ T) t) (⌊u * n⌋₊ * slotLen M n) : ℝ) /
      n = _
  rw [workTraj_frozen hT t]
  rfl

/-- **The single machine reduction, on `k` tapes**: `code_bits_of_class` with the diagram's tapes
indexed by `Fin k` for `M.k = k` (so that machines of different sizes give diagrams of one type), and
its rescaled walks are the machine's rescaled trajectories. -/
theorem diagram_of_class {k : ℕ} (hk : M.k = k) {n T s : ℕ} (hn1 : 1 ≤ n)
    (hs : Nat.clog 2 (M.q + 1) + (M.k + 1) * Nat.clog 2 (2 * T + 1) ≤ s)
    {F : Set (List Bool)} {w₀ : List Bool}
    (hF : TraceClass M n (entryBits n) (slotLen M n) T F w₀)
    (hcorr : ClassCorrect M n (entryBits n) T F) :
    ∃ (D : TSDiagram k) (code : NetCode), D.Valid (n * n * entryBits n) ∧ D.T = T ∧
      D.Solves n (cellBits M) (D.blockCap n (cellBits M)
        (fun y => ∑ t, (pairRes (blockSize (cellBits M) n) (D.work t) D.T y).card) s)
        {v | List.ofFn v ∈ F} code ∧
      ∀ t, D.rescaled n (cellBits M) t = rescaledTrajOf M n w₀ (Fin.cast hk.symm t) := by
  subst hk
  obtain ⟨code, hv, hsol⟩ := code_bits_of_class hn1 hs hF hcorr
  exact ⟨runDiagram M w₀ T, code, hv, rfl, hsol, fun t => rescaled_runDiagram (hF.2 w₀ hF.1).2.1 t⟩

end Transpose.Tape.Impl
