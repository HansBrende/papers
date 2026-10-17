import Transpose.Tape.LemmaOnePrime
import Transpose.Tape.PPrime

/-!
# The Cut Lemma on trace classes (the adaptive cut lemma) and Discrete Isoperimetry on trace classes

* Class invariants: inputs with the same block-level trace (and the same halting time) have the
  same resident blocks (`pairRes_eq_of_sameTrace`), the same input rows touched by a union of
  slots (`srcRows_eq_of_sameTrace`) and the same output positions appended during it
  (`appendedDuring_iff_of_sameTrace`).
* `cutRows`: the row-based cut set of a union of slots; `b |S_J| ≤ |cutRows|`.
* `cut_bound_trace`: the counting core `two_pow_mul_ncard_le` (`Counting.lean`), with the entry data
  at the memory boundaries and chords as the code and the Block Locality Lemma for the injectivity.
* `cut_bound_trace_bits` and `isoperimetry_trace` (its lower side is `lower_side_labels`,
  shared with the oblivious form).
-/

namespace Transpose.Tape.Impl

open Transpose

variable {M : TM}

/-! ### Output positions appended in a slot -/

/-- **The output positions appended during a union of slots**, for a run halting at `T`: `o` is
appended during `J` exactly when, for some slot `y < ⌈T/r⌉` of `U`, the output lengths at the first
steps of slots `y` and `y + 1` bracket `o`. -/
theorem appendedDuring_slotSteps_iff {w : List Bool} {r T : ℕ} (hr : 1 ≤ r) (hT : HaltsAt M w T)
    (U : Set ℕ) (o : ℕ) :
    AppendedDuring M w (slotSteps r U T) o ↔
      ∃ y < numSlots r T, y ∈ U ∧ (run M w (y * r)).outRev.length ≤ o ∧
        o < (run M w ((y + 1) * r)).outRev.length := by
  constructor
  · rintro ⟨τ, hτ, hsome, hlen⟩
    rw [mem_slotSteps] at hτ
    obtain ⟨hτT, hτU⟩ := hτ
    refine ⟨τ / r, div_lt_numSlots hr hτT, hτU, ?_, ?_⟩
    · rw [← hlen]; exact outRev_length_mono w (Nat.div_mul_le_self τ r)
    · have h1 := outRev_length_succ (M := M) w τ
      rw [ite_eq_left hsome] at h1
      have h2 : τ + 1 ≤ (τ / r + 1) * r := by
        have := Nat.lt_mul_div_succ τ (show 0 < r by omega)
        rw [Nat.mul_comm] at this; omega
      have h3 := outRev_length_mono (M := M) w h2
      omega
  · rintro ⟨y, hyN, hyU, h1, h2⟩
    obtain ⟨τ, hτ1, hτ2, hsome, hlen⟩ := exists_append_between w h1 h2
    refine ⟨τ, ?_, hsome, hlen⟩
    rw [mem_slotSteps]
    have hτT : τ < T := by
      by_contra hc
      push Not at hc
      have := transAt_of_le_of_none hT.2 hc
      simp [outBit, this] at hsome
    refine ⟨hτT, ?_⟩
    have : τ / r = y := by
      apply Nat.div_eq_of_lt_le
      · rw [Nat.mul_comm] at hτ1; linarith [Nat.mul_comm y r]
      · rw [Nat.add_mul, Nat.one_mul] at hτ2 ⊢; rw [Nat.mul_comm] at hτ2 ⊢; omega
    rw [this]; exact hyU

/-! ### Class invariants -/

/-- Inputs with the same trace have the same pair residency at every slot. -/
theorem pairRes_eq_of_sameTrace {n b r T : ℕ} (hr : 1 ≤ r) {w w' : List Bool}
    (h : SameTrace M n b r T w w') (t : Fin M.k) :
    pairRes r (fun τ => workTraj M w τ t) T = pairRes r (fun τ => workTraj M w' τ t) T := by
  funext y
  rcases le_or_gt y (numSlots r T) with hy | hy
  · exact sameTrace_pairRes h t hy
  · have hT : T ≤ y * r := not_lt.1 fun h' => absurd ((numSlots_spec hr).2 h') (by omega)
    rw [pairRes_empty hT, pairRes_empty hT]

theorem srcRows_eq_of_sameTrace {n b r T : ℕ} (hr : 1 ≤ r) {w w' : List Bool}
    (h : SameTrace M n b r T w w') (U : Set ℕ) :
    srcRows M w n b (slotSteps r U T) = srcRows M w' n b (slotSteps r U T) := by
  classical
  rw [srcRows_slotSteps_eq hr, srcRows_slotSteps_eq hr]
  apply Finset.biUnion_congr rfl
  intro y hy
  exact sameTrace_srcRows h (Finset.mem_range.1 (Finset.mem_filter.1 hy).1).le

theorem appendedDuring_iff_of_sameTrace {n b r T : ℕ} (hr : 1 ≤ r) {w w' : List Bool}
    (hT : HaltsAt M w T) (hT' : HaltsAt M w' T) (h : SameTrace M n b r T w w') (U : Set ℕ)
    (o : ℕ) :
    AppendedDuring M w (slotSteps r U T) o ↔ AppendedDuring M w' (slotSteps r U T) o := by
  rw [appendedDuring_slotSteps_iff hr hT, appendedDuring_slotSteps_iff hr hT']
  constructor
  · rintro ⟨y, hyN, hyU, h1, h2⟩
    exact ⟨y, hyN, hyU, by rw [← sameTrace_outLen h hyN.le]; exact h1,
      by rw [← sameTrace_outLen h (show y + 1 ≤ numSlots r T by omega)]; exact h2⟩
  · rintro ⟨y, hyN, hyU, h1, h2⟩
    exact ⟨y, hyN, hyU, by rw [sameTrace_outLen h hyN.le]; exact h1,
      by rw [sameTrace_outLen h (show y + 1 ≤ numSlots r T by omega)]; exact h2⟩

theorem sameTrace_symm {n b r T : ℕ} {w w' : List Bool} (h : SameTrace M n b r T w w') :
    SameTrace M n b r T w' w := fun y hy => (h y hy).symm

theorem sameTrace_trans {n b r T : ℕ} {w w' w'' : List Bool} (h : SameTrace M n b r T w w')
    (h' : SameTrace M n b r T w' w'') : SameTrace M n b r T w w'' :=
  fun y hy => (h y hy).trans (h' y hy)

/-! ### The row-based cut set -/

open Classical in
/-- The row-based cut set of `J` for the trajectory of `w₀`: the input bits `d < n²b` in rows not
touched during `J` whose transposed copy is appended during `J`. -/
noncomputable def cutRows (M : TM) (w₀ : List Bool) (n b : ℕ) (J : Finset ℕ) : Finset ℕ :=
  (Finset.range (n * n * b)).filter (fun d =>
    d / (n * b) ∉ srcRows M w₀ n b J ∧ AppendedDuring M w₀ J (tpos n b d))

theorem row_of_pos {n b i j t : ℕ} (hj : j < n) (ht : t < b) :
    ((i * n + j) * b + t) / (n * b) = i := by
  obtain ⟨h1, h2⟩ := pos_mem_row (i := i) hj ht
  apply Nat.div_eq_of_lt_le
  · calc i * (n * b) = i * n * b := by ring
      _ ≤ _ := h1
  · calc (i * n + j) * b + t < (i + 1) * n * b := h2
      _ = (i + 1) * (n * b) := by ring

/-- `|S_J| · b ≤ |cutRows J|`. -/
theorem cutPairs_card_mul_le_rows (M : TM) (w₀ : List Bool) (n b : ℕ) (J : Finset ℕ) :
    (cutPairs M w₀ n b J).card * b ≤ (cutRows M w₀ n b J).card := by
  classical
  refine cutPairs_card_mul_le_of fun i j t hi hsrc hsnk ht => ?_
  have hj := Finset.mem_range.1 (Finset.mem_filter.1 hsnk).1
  simp only [cutRows, Finset.mem_filter, Finset.mem_range]
  refine ⟨pos_lt hi hj ht, by rw [row_of_pos hj ht]; exact hsrc, ?_⟩
  rw [tpos_spec hj ht]
  obtain ⟨hcol1, hcol2⟩ := pos_mem_row (i := j) (j := i) (t := t) hi ht
  exact (Finset.mem_filter.1 hsnk).2 _ hcol1 hcol2

/-! ### Codes for positions and cells -/

/-- Positions in `[-T, T]`, coded in `Fin (2T+1)`. -/
def posCode (T : ℕ) (p : ℤ) : Fin (2 * T + 1) :=
  ⟨(p + T).toNat % (2 * T + 1), Nat.mod_lt _ (by omega)⟩

theorem posCode_inj {T : ℕ} {p p' : ℤ} (hp : |p| ≤ T) (hp' : |p'| ≤ T)
    (h : posCode T p = posCode T p') : p = p' := by
  simp only [posCode, Fin.mk.injEq] at h
  rw [abs_le] at hp hp'
  have h1 : (p + T).toNat < 2 * T + 1 := by omega
  have h2 : (p' + T).toNat < 2 * T + 1 := by omega
  rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at h
  omega

/-- The cells of block `β`. -/
def blockCells (r : ℕ) (β : ℤ) : Finset ℤ := Finset.Ico (β * r) (β * r + r)

theorem mem_blockCells {r : ℕ} (hr : 1 ≤ r) {c β : ℤ} : c ∈ blockCells r β ↔ blockOf r c = β := by
  rw [blockOf_eq_iff hr, blockCells, Finset.mem_Ico, add_mul, one_mul]

theorem card_blockCells (r : ℕ) (β : ℤ) : (blockCells r β).card = r := by
  simp [blockCells]

/-! ### The Cut Lemma on a trace class -/

/-- A machine correct on all inputs is correct on every trace class. -/
theorem classCorrect_of_transposes {n b r T : ℕ} {F : Set (List Bool)} {w₀ : List Bool}
    (hcorr : Transposes M n b) (hF : TraceClass M n b r T F w₀) : ClassCorrect M n b T F :=
  fun w hw => correct_of_transposes hcorr (hF.2 w hw).1 (hF.2 w hw).2.1

/-- **The Cut Lemma on a trace class**: the counting core with the state, the head positions and
the resident blocks at the memory boundaries and the chord blocks as the code. Two members with the
same code that agree outside the row-based cut agree on `J` by the Block Locality Lemma, so they
output the same cut bits. -/
theorem cut_bound_trace {n b r T : ℕ} {F : Set (List Bool)} {w₀ : List Bool} (hr : 1 ≤ r)
    (hcorr : ClassCorrect M n b T F) (hF : TraceClass M n b r T F w₀) (U : Set ℕ) :
    2 ^ (b * (cutPairs M w₀ n b (slotSteps r U T)).card) * F.ncard ≤
      2 ^ (n * n * b) *
        (((M.q + 1) * (2 * T + 1) ^ (M.k + 1)) ^ (memBoundaries U (numSlots r T)).card *
          (M.g + 1) ^ (r * (3 * M.k * (memBoundaries U (numSlots r T)).card +
            ∑ t : Fin M.k,
              (chordsInto (pairRes r (fun τ => workTraj M w₀ τ t) T) U (numSlots r T)).card))) := by
  classical
  set N := numSlots r T with hN
  set J := slotSteps r U T with hJ
  set MB := memBoundaries U N with hMB
  set C := cutRows M w₀ n b J with hC
  set R : Fin M.k → ℕ → Finset ℤ := fun t => pairRes r (fun τ => workTraj M w₀ τ t) T with hR
  let CellsM : Finset (Fin M.k × ℕ × ℤ) := Finset.univ.biUnion (fun t => MB.biUnion (fun z =>
    (R t z).biUnion (fun β => (blockCells r β).image (fun c => (t, z, c)))))
  let CellsC : Finset (Fin M.k × ℕ × ℤ) := Finset.univ.biUnion (fun t =>
    (chordsInto (R t) U N).biUnion (fun p => (blockCells r p.2).image (fun c => (t, p.1, c))))
  let E := (MB → Fin (M.q + 1) × Fin (2 * T + 1) × (Fin M.k → Fin (2 * T + 1))) ×
    (CellsM → Fin (M.g + 1)) × (CellsC → Fin (M.g + 1))
  let e : List Bool → E := fun w =>
    (fun z => ((run M w (z.1 * r)).state, posCode T (run M w (z.1 * r)).inPos,
        fun t => posCode T ((run M w (z.1 * r)).workPos t)),
      fun x => (run M w (x.1.2.1 * r)).work x.1.1 x.1.2.2,
      fun x => (run M w (x.1.2.1 * r)).work x.1.1 x.1.2.2)
  have hmemF : ∀ w ∈ F, w ∈ matrixInputs n b ∧ HaltsAt M w T ∧ SameTrace M n b r T w w₀ :=
    hF.2
  have hzT : ∀ z ∈ MB, z * r < T := fun z hz => (numSlots_spec hr).1 (mem_memBoundaries.1 hz).1
  have hcount := two_pow_mul_ncard_le (fun w hw => (hmemF w hw).1) (C := C)
    (fun d hd => (Finset.mem_filter.1 hd).1) e (fun w hw w' hw' hψ hout => by
    obtain ⟨hwM, hT, htr⟩ := hmemF w hw
    obtain ⟨hwM', hT', htr'⟩ := hmemF w' hw'
    have hlen := length_of_mem_matrixInputs hwM
    have hlen' := length_of_mem_matrixInputs hwM'
    have htrww : SameTrace M n b r T w w' := sameTrace_trans htr (sameTrace_symm htr')
    have hRw : ∀ t, pairRes r (fun τ => workTraj M w τ t) T = R t :=
      fun t => pairRes_eq_of_sameTrace hr htr t
    have h2 := congrArg (fun z => z.1) hψ
    have h3 := congrArg (fun z => z.2.1) hψ
    have h4 := congrArg (fun z => z.2.2) hψ
    simp only [e] at h2 h3 h4
    -- the Block Locality Lemma
    have hloc := block_locality (M := M) hr hlen hlen' htrww U
      (fun z hz => by
        have e := congrFun h2 ⟨z, hz⟩
        simp only [Prod.mk.injEq] at e
        obtain ⟨es, ei, ew⟩ := e
        have hzr := hzT z hz
        refine ⟨es, posCode_inj (le_trans (abs_inPos_le w _) (by exact_mod_cast hzr.le))
          (le_trans (abs_inPos_le w' _) (by exact_mod_cast hzr.le)) ei, ?_, ?_⟩
        · funext t
          exact posCode_inj (le_trans (abs_workPos_le w _ t) (by exact_mod_cast hzr.le))
            (le_trans (abs_workPos_le w' _ t) (by exact_mod_cast hzr.le)) (congrFun ew t)
        · intro t c hc
          rw [hRw t] at hc
          have hmem : (t, z, c) ∈ CellsM := by
            simp only [CellsM, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]
            exact ⟨t, z, hz, blockOf r c, hc, c, (mem_blockCells hr).2 rfl, rfl⟩
          exact congrFun h3 ⟨(t, z, c), hmem⟩)
      (fun t p hp c hc => by
        rw [hRw t] at hp
        have hmem : (t, p.1, c) ∈ CellsC := by
          simp only [CellsC, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]
          exact ⟨t, p, hp, c, (mem_blockCells hr).2 hc, rfl⟩
        exact congrFun h4 ⟨(t, p.1, c), hmem⟩)
      (fun d hdL hrow => by
        apply hout d hdL
        intro hdC
        simp only [hC, cutRows, Finset.mem_filter] at hdC
        apply hdC.2.1
        rw [← srcRows_eq_of_sameTrace hr htr U]
        exact hrow)
    -- a cut bit is appended during `J`, where the two runs take the same transitions
    intro d hdC
    have hdL : d < n * n * b := Finset.mem_range.1 (Finset.mem_filter.1 hdC).1
    simp only [hC, cutRows, Finset.mem_filter] at hdC
    obtain ⟨-, -, happ₀⟩ := hdC
    have happ : AppendedDuring M w (slotSteps r U T) (tpos n b d) :=
      (appendedDuring_iff_of_sameTrace hr hT (hmemF w₀ hF.1).2.1 htr U _).2 happ₀
    obtain ⟨τ, hτJ, hsome, hτlen⟩ := happ
    obtain ⟨-, -, -, hl, -, htrτ⟩ := hloc τ hτJ
    have hτT : τ < T := (mem_slotSteps.1 hτJ).1
    obtain ⟨A, rfl⟩ := hwM
    obtain ⟨A', rfl⟩ := hwM'
    have hob : outBit M (encode n b A') τ = outBit M (encode n b A) τ := by
      simp only [outBit, htrτ]
    have hsome' : (outBit M (encode n b A') τ).isSome := by rw [hob]; exact hsome
    have e1 := output_nth_eq_outBit (encode n b A) hτT hsome
    have e2 := output_nth_eq_outBit (encode n b A') hτT hsome'
    rw [output_eq_of_classCorrect hcorr hw, hτlen, nth_encode_transpose_tpos A hdL] at e1
    rw [output_eq_of_classCorrect hcorr hw', ← hl, hτlen, nth_encode_transpose_tpos A' hdL] at e2
    rw [e1, e2, hob])
  -- the size of the code
  have hR3 : ∀ t z, (R t z).card ≤ 3 := fun t z =>
    (pairRes_admissible (unitSteps_workTraj M w₀ t) hr T).2 z
  have hCellsM : CellsM.card ≤ r * (3 * M.k * MB.card) := by
    calc CellsM.card ≤ ∑ t : Fin M.k, (MB.biUnion (fun z => (R t z).biUnion (fun β =>
          (blockCells r β).image (fun c => (t, z, c))))).card := Finset.card_biUnion_le
      _ ≤ ∑ _t : Fin M.k, ∑ _z ∈ MB, 3 * r := by
          apply Finset.sum_le_sum; intro t _
          refine le_trans Finset.card_biUnion_le (Finset.sum_le_sum ?_)
          intro z _
          refine le_trans Finset.card_biUnion_le ?_
          calc ∑ β ∈ R t z, ((blockCells r β).image (fun c => (t, z, c))).card
              ≤ ∑ _β ∈ R t z, r := Finset.sum_le_sum (fun β _ =>
                le_trans Finset.card_image_le (le_of_eq (card_blockCells r β)))
            _ = (R t z).card * r := by rw [Finset.sum_const, smul_eq_mul]
            _ ≤ 3 * r := Nat.mul_le_mul_right _ (hR3 t z)
      _ = r * (3 * M.k * MB.card) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]; ring
  have hCellsC : CellsC.card ≤ r * ∑ t : Fin M.k, (chordsInto (R t) U N).card := by
    calc CellsC.card ≤ ∑ t : Fin M.k, ((chordsInto (R t) U N).biUnion (fun p =>
          (blockCells r p.2).image (fun c => (t, p.1, c)))).card := Finset.card_biUnion_le
      _ ≤ ∑ t : Fin M.k, (chordsInto (R t) U N).card * r := by
          apply Finset.sum_le_sum; intro t _
          refine le_trans Finset.card_biUnion_le ?_
          calc ∑ p ∈ chordsInto (R t) U N, ((blockCells r p.2).image (fun c => (t, p.1, c))).card
              ≤ ∑ _p ∈ chordsInto (R t) U N, r := Finset.sum_le_sum (fun p _ =>
                le_trans Finset.card_image_le (le_of_eq (card_blockCells r p.2)))
            _ = (chordsInto (R t) U N).card * r := by rw [Finset.sum_const, smul_eq_mul]
      _ = r * ∑ t : Fin M.k, (chordsInto (R t) U N).card := by
          rw [← Finset.sum_mul, Nat.mul_comm]
  have hE : Fintype.card E ≤ ((M.q + 1) * (2 * T + 1) ^ (M.k + 1)) ^ MB.card *
      (M.g + 1) ^ (r * (3 * M.k * MB.card + ∑ t : Fin M.k, (chordsInto (R t) U N).card)) := by
    simp only [E, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
    rw [← pow_add, show (2 * T + 1) * (2 * T + 1) ^ M.k = (2 * T + 1) ^ (M.k + 1) by
      rw [pow_succ, Nat.mul_comm]]
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_right (by omega)
    rw [Nat.mul_add]
    exact Nat.add_le_add hCellsM hCellsC
  have hcp : b * (cutPairs M w₀ n b J).card ≤ C.card := by
    rw [Nat.mul_comm]; exact cutPairs_card_mul_le_rows M w₀ n b J
  exact le_trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hcp))
    (le_trans hcount (Nat.mul_le_mul_left _ hE))

/-- `(q+1)(2T+1)^{k+1}` and `(g+1)` in bits. -/
theorem entry_le_pow (M : TM) (T μ x : ℕ) :
    ((M.q + 1) * (2 * T + 1) ^ (M.k + 1)) ^ μ * (M.g + 1) ^ x ≤
      2 ^ (μ * (Nat.clog 2 (M.q + 1) + (M.k + 1) * Nat.clog 2 (2 * T + 1)) +
        x * Nat.clog 2 (M.g + 1)) := by
  have h1 := Nat.le_pow_clog (by norm_num : 1 < 2) (M.q + 1)
  have h2 := Nat.le_pow_clog (by norm_num : 1 < 2) (2 * T + 1)
  have h3 := Nat.le_pow_clog (by norm_num : 1 < 2) (M.g + 1)
  calc ((M.q + 1) * (2 * T + 1) ^ (M.k + 1)) ^ μ * (M.g + 1) ^ x
      ≤ (2 ^ Nat.clog 2 (M.q + 1) * (2 ^ Nat.clog 2 (2 * T + 1)) ^ (M.k + 1)) ^ μ *
          (2 ^ Nat.clog 2 (M.g + 1)) ^ x :=
        Nat.mul_le_mul (Nat.pow_le_pow_left (Nat.mul_le_mul h1 (Nat.pow_le_pow_left h2 _)) _)
          (Nat.pow_le_pow_left h3 _)
    _ = _ := by
        rw [← pow_mul, ← pow_add, ← pow_mul, ← pow_mul, ← pow_add]
        congr 1
        ring

/-- **The Cut Lemma on a trace class, bits form** (co-entropy `≤ D`). -/
theorem cut_bound_trace_bits {n b r T : ℕ} {F : Set (List Bool)} {w₀ : List Bool} (hr : 1 ≤ r)
    (hcorr : ClassCorrect M n b T F) (hF : TraceClass M n b r T F w₀) {D : ℕ}
    (hD : 2 ^ (n * n * b) ≤ 2 ^ D * F.ncard) (U : Set ℕ) :
    b * (cutPairs M w₀ n b (slotSteps r U T)).card ≤ D +
      (memBoundaries U (numSlots r T)).card *
          (Nat.clog 2 (M.q + 1) + (M.k + 1) * Nat.clog 2 (2 * T + 1)) +
        r * Nat.clog 2 (M.g + 1) * (3 * M.k * (memBoundaries U (numSlots r T)).card +
          ∑ t : Fin M.k,
            (chordsInto (pairRes r (fun τ => workTraj M w₀ τ t) T) U (numSlots r T)).card) := by
  have h := cut_bound_trace hr hcorr hF U
  have hpos := ncard_pos_of_coentropy hD
  generalize hc : b * (cutPairs M w₀ n b (slotSteps r U T)).card = c at h ⊢
  generalize hμ : (memBoundaries U (numSlots r T)).card = μ at h ⊢
  generalize hχ : (∑ t : Fin M.k,
    (chordsInto (pairRes r (fun τ => workTraj M w₀ τ t) T) U (numSlots r T)).card) = χ at h ⊢
  have hE := entry_le_pow M T μ (r * (3 * M.k * μ + χ))
  have h2 : 2 ^ c * F.ncard ≤
      (2 ^ D * (((M.q + 1) * (2 * T + 1) ^ (M.k + 1)) ^ μ *
        (M.g + 1) ^ (r * (3 * M.k * μ + χ)))) * F.ncard := by
    calc 2 ^ c * F.ncard ≤ _ := h
      _ ≤ 2 ^ D * F.ncard * (((M.q + 1) * (2 * T + 1) ^ (M.k + 1)) ^ μ *
            (M.g + 1) ^ (r * (3 * M.k * μ + χ))) := Nat.mul_le_mul_right _ hD
      _ = _ := by ring
  have h3 := Nat.le_of_mul_le_mul_right h2 hpos
  have h4 : 2 ^ c ≤ 2 ^ (D + (μ * (Nat.clog 2 (M.q + 1) + (M.k + 1) * Nat.clog 2 (2 * T + 1)) +
      r * (3 * M.k * μ + χ) * Nat.clog 2 (M.g + 1))) := by
    rw [pow_add]
    exact le_trans h3 (Nat.mul_le_mul_left _ hE)
  have := (Nat.pow_le_pow_iff_right (by norm_num)).1 h4
  calc c ≤ _ := this
    _ = _ := by ring

/-! ### Discrete Isoperimetry on a trace class -/

/-- **Discrete Isoperimetry on a trace class (labelled partitions of the slots)**: the lower side
`lower_side_labels` and the Cut Lemma on each label class (`cut_bound_trace_bits`). -/
theorem isoperimetry_trace {n b r T : ℕ} {F : Set (List Bool)} {w₀ : List Bool} (hr : 1 ≤ r)
    (hrnb : r ≤ n * b) (hcorr : ClassCorrect M n b T F)
    (hF : TraceClass M n b r T F w₀) {D : ℕ} (hD : 2 ^ (n * n * b) ≤ 2 ^ D * F.ncard)
    (lab : ℕ → ℕ) (m : ℕ)
    (hm : ∀ ℓ, ((Finset.range (numSlots r T)).filter (fun y => lab y = ℓ)).card ≤ m) :
    (n - labelChanges lab (numSlots r T)) * (n - 2 * m) * b ≤
      (labelChanges lab (numSlots r T) + 1) * D +
        labelChanges lab (numSlots r T) *
          (Nat.clog 2 (M.q + 1) + (M.k + 1) * Nat.clog 2 (2 * T + 1)) +
        r * Nat.clog 2 (M.g + 1) * (3 * M.k * labelChanges lab (numSlots r T) +
          ∑ t : Fin M.k,
            (crossChords (pairRes r (fun τ => workTraj M w₀ τ t) T) lab (numSlots r T)).card) := by
  classical
  set N := numSlots r T with hN
  set Mb := labelChanges lab N with hMb
  set s := (Finset.range N).image lab with hs
  set K := Nat.clog 2 (M.q + 1) + (M.k + 1) * Nat.clog 2 (2 * T + 1) with hK
  set G := Nat.clog 2 (M.g + 1) with hG
  set R : Fin M.k → ℕ → Finset ℤ := fun t => pairRes r (fun τ => workTraj M w₀ τ t) T with hR
  refine (lower_side_labels (le_of_eq (outLen_of_classCorrect hcorr hF.1).symm) hr hrnb lab m
    hm).trans ?_
  -- the upper side: the Cut Lemma on each label class
  let μ : ℕ → ℕ := fun ℓ => (memBoundaries {y | lab y = ℓ} N).card
  let χ : ℕ → ℕ := fun ℓ => ∑ t : Fin M.k, (chordsInto (R t) {y | lab y = ℓ} N).card
  have hpart : ∀ ℓ ∈ s, b * (cutPairs M w₀ n b (labelPart r lab T ℓ)).card ≤
      D + (K + r * G * (3 * M.k)) * μ ℓ + r * G * χ ℓ := by
    intro ℓ _
    have h := cut_bound_trace_bits hr hcorr hF hD {y | lab y = ℓ}
    calc b * (cutPairs M w₀ n b (labelPart r lab T ℓ)).card ≤ _ := h
      _ = _ := by simp only [μ, χ, hR]; ring
  have hμ : ∑ ℓ ∈ s, μ ℓ ≤ Mb := sum_memBoundaries_le lab N s
  have hχ : ∑ ℓ ∈ s, χ ℓ ≤ ∑ t : Fin M.k, (crossChords (R t) lab N).card := by
    simp only [χ]
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum (fun t _ => sum_chordsInto_le _ lab N s)
  have hscard : s.card ≤ Mb + 1 := card_image_lab_le lab N
  rw [Finset.mul_sum]
  calc ∑ ℓ ∈ s, b * (cutPairs M w₀ n b (labelPart r lab T ℓ)).card
      ≤ ∑ ℓ ∈ s, (D + (K + r * G * (3 * M.k)) * μ ℓ + r * G * χ ℓ) := Finset.sum_le_sum hpart
    _ = s.card * D + (K + r * G * (3 * M.k)) * ∑ ℓ ∈ s, μ ℓ + r * G * ∑ ℓ ∈ s, χ ℓ := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul,
          ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ (Mb + 1) * D + (K + r * G * (3 * M.k)) * Mb +
          r * G * ∑ t : Fin M.k, (crossChords (R t) lab N).card := by
        apply Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_right _ hscard)
          (Nat.mul_le_mul_left _ hμ)) (Nat.mul_le_mul_left _ hχ)
    _ = _ := by ring

end Transpose.Tape.Impl
