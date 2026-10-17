import Transpose.Tape.Locality
import Transpose.Tape.Encode

/-!
# The Cut Lemma and the Cut Lemma for families

* Output positions: the bit appended at step `τ` is output bit `|outRev_τ|` (output lengths step by
  step: `outRev_length_succ` in `Run.lean`); `outLen_agree`: output lengths propagate along a step
  set when the transitions agree.
* `card_le_entryData`: the abstract injection form.
* `two_pow_mul_ncard_le`: the counting core of every cut lemma (also used for trace classes in
  `CutTrace.lean`). `cut_bound_on`: the Cut Lemma on a set `W` on which the machine is oblivious and
  correct, `2^{|cut|} |W| ≤ 2^{n²b} · (entry data)`.
* On a set of co-entropy `m` (`ncard_pos_of_coentropy`): `cut_bound_on_coentropy`,
  `cut_bound_sum_on`; `cut_bound` and `cut_bound_sum` are their case `W` = all matrix inputs,
  `m = 0`.
* `cutPairs_card_mul_le_of`, `cutPairs_card_mul_le`, `cut_bound_pairs`, `cut_bound_bits`.
* `correct_of_transposes`; inputs as vectors (`toVec`, `ncard_ofFn_preimage`, `ncard_matrixInputs`,
  `nth_ofFn`, `ofFn_mem_matrixInputs`).
* The Cut Lemma for families: `cut_bound_sum`, `cut_bound_sum_bits`, `sum_cutPairs_ge`,
  `uncovered_cols_le` (from `uncovered_cols_le_len`, which needs only the output length).
-/

namespace Transpose.Tape.Impl

open Transpose

variable {M : TM}

/-! ### Output positions -/

/-- The bit appended at step `τ < T` is bit number `|outRev_τ|` of the output at time `T`. -/
theorem output_nth_eq_outBit (w : List Bool) {τ T : ℕ} (hτ : τ < T)
    (hsome : (outBit M w τ).isSome) :
    nth (run M w T).outRev.reverse (run M w τ).outRev.length = outBit M w τ := by
  rw [nth_eq_getElem?, outRev_reverse_eq, ← List.length_reverse, outRev_reverse_eq]
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hτ
  rw [show τ + j + 1 = τ + (j + 1) by omega, List.range_add, List.filterMap_append,
    List.getElem?_append_right le_rfl, Nat.sub_self, List.range_succ_eq_map, List.map_cons,
    List.filterMap_cons]
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hsome
  simp [hx]

/-- On an oblivious class all inputs have the same output lengths. -/
theorem oblivious_outRev_length {W : Set (List Bool)} {T : ℕ} (hobl : ObliviousOn M W T)
    {w w' : List Bool} (hw : w ∈ W) (hw' : w' ∈ W) (τ : ℕ) :
    (run M w τ).outRev.length = (run M w' τ).outRev.length := by
  induction τ with
  | zero => rfl
  | succ τ ih => rw [outRev_length_succ, outRev_length_succ, ih, (hobl.2 w hw w' hw' τ).2.2]

/-- Output lengths propagate along `J` from the anchors when the transitions agree. -/
theorem outLen_agree {w w' : List Bool} {J : Finset ℕ} {A : Set ℕ}
    (hpred : ∀ τ ∈ J, τ ∉ A → 1 ≤ τ ∧ τ - 1 ∈ J)
    (hanchor : ∀ τ ∈ J, τ ∈ A → (run M w τ).outRev.length = (run M w' τ).outRev.length)
    (htr : ∀ τ ∈ J, transAt M w τ = transAt M w' τ) :
    ∀ τ ∈ J, (run M w τ).outRev.length = (run M w' τ).outRev.length := by
  intro τ
  induction τ using Nat.strong_induction_on with
  | _ τ ih =>
  intro hτ
  by_cases hA : τ ∈ A
  · exact hanchor τ hτ hA
  · obtain ⟨h1, hprev⟩ := hpred τ hτ hA
    have hob : outBit M w (τ - 1) = outBit M w' (τ - 1) := by simp only [outBit, htr _ hprev]
    rw [show τ = (τ - 1) + 1 by omega, outRev_length_succ, outRev_length_succ,
      ih (τ - 1) (by omega) hprev, hob]

/-! ### The abstract injection form -/

theorem card_le_entryData {W : Set (List Bool)} {T : ℕ} (hobl : ObliviousOn M W T)
    {w₀ : List Bool} (hw₀ : w₀ ∈ W) {J : Finset ℕ} (hJ : ∀ τ ∈ J, τ < T)
    {X : Type*} [Fintype X] (f : X → List Bool) (hfW : ∀ x, f x ∈ W)
    (hbits : ∀ x x', ∀ τ ∈ J,
      readInput (f x) (run M w₀ τ).inPos = readInput (f x') (run M w₀ τ).inPos)
    (hinj : ∀ x x', (∀ τ ∈ J, outBit M (f x) τ = outBit M (f x') τ) → x = x') :
    Fintype.card X ≤
      (M.q + 1) ^ (entryPoints J).card * (M.g + 1) ^ (entryCells (workTraj M w₀) J).card := by
  classical
  let E := (entryPoints J → Fin (M.q + 1)) × (entryCells (workTraj M w₀) J → Fin (M.g + 1))
  let φ : X → E := fun x =>
    (fun τ => (run M (f x) τ.1).state, fun p => headSym M (f x) p.1.2 p.1.1)
  have hφ : Function.Injective φ := by
    intro x x' hxx'
    have h1 := congrArg Prod.fst hxx'
    have h2 := congrArg Prod.snd hxx'
    simp only [φ] at h1 h2
    apply hinj
    have hcells : entryCells (workTraj M (f x)) J = entryCells (workTraj M w₀) J := by
      rw [oblivious_workTraj hobl (hfW x) hw₀]
    have hloc := locality_oblivious hobl (hfW x) (hfW x') hJ
      (fun τ hτ => congrFun h1 ⟨τ, hτ⟩)
      (fun p hp => congrFun h2 ⟨p, hcells ▸ hp⟩)
      (fun τ hτ => by rw [(hobl.2 (f x) (hfW x) w₀ hw₀ τ).1]; exact hbits x x' τ hτ)
    intro τ hτ
    simp only [outBit]; rw [(hloc τ hτ).2.2.2]
  calc Fintype.card X ≤ Fintype.card E := Fintype.card_le_of_injective φ hφ
    _ = _ := by simp [E, Fintype.card_prod]


/-! ### The cut set -/

/-- Output of a correct transposer that halts at `T` on the encoding of `A`. -/
theorem output_eq_of_haltsAt {n b T : ℕ} (hcorr : Transposes M n b) (A : Matrix)
    (hT : HaltsAt M (encode n b A) T) :
    (run M (encode n b A) T).outRev.reverse = encode n b (transpose A) := by
  obtain ⟨t, ht⟩ := hcorr A
  obtain ⟨T', -, hT', hout⟩ := (computesWithin_iff _ t).1 ht
  rw [haltsAt_unique hT hT']; exact hout

/-- `M` outputs the transposed encoding at time `T` on every input of `F`. -/
def ClassCorrect (M : TM) (n b T : ℕ) (F : Set (List Bool)) : Prop :=
  ∀ w ∈ F, ∃ A : Matrix, w = encode n b A ∧ (run M w T).outRev.reverse = encode n b (transpose A)

/-- The output on an input of a class on which `M` is correct. -/
theorem output_eq_of_classCorrect {n b T : ℕ} {F : Set (List Bool)} (hcorr : ClassCorrect M n b T F)
    {A : Matrix} (hA : encode n b A ∈ F) :
    (run M (encode n b A) T).outRev.reverse = encode n b (transpose A) := by
  obtain ⟨A', hA', hout⟩ := hcorr _ hA
  rw [hout, ← encode_transpose_eq_of_encode_eq hA']

theorem outLen_of_classCorrect {n b T : ℕ} {F : Set (List Bool)} (hcorr : ClassCorrect M n b T F)
    {w : List Bool} (hw : w ∈ F) : (run M w T).outRev.length = n * n * b := by
  obtain ⟨A, -, hout⟩ := hcorr w hw
  rw [← List.length_reverse, hout, length_encode]

/-- A transposer is correct on every matrix input, at its halting time. -/
theorem correct_of_transposes {n b T : ℕ} {w : List Bool} (hcorr : Transposes M n b)
    (hw : w ∈ matrixInputs n b) (hT : HaltsAt M w T) :
    ∃ A : Matrix, w = encode n b A ∧ (run M w T).outRev.reverse = encode n b (transpose A) := by
  obtain ⟨A, rfl⟩ := hw
  exact ⟨A, rfl, output_eq_of_haltsAt hcorr A hT⟩

/-- A step of `J` reads either outside `[0, n²b)` or a position outside the cut set. -/
theorem readInput_eq_of_agree {n b : ℕ} {C : Finset ℕ} {J : Finset ℕ} {M : TM} {w₀ : List Bool}
    (hC : C = cutSet M w₀ n b J) {w w' : List Bool} (hlen : w.length = n * n * b)
    (hlen' : w'.length = n * n * b)
    (hagree : ∀ d, d < n * n * b → d ∉ C → nth w d = nth w' d) {τ : ℕ} (hτ : τ ∈ J) :
    readInput w (run M w₀ τ).inPos = readInput w' (run M w₀ τ).inPos := by
  classical
  refine readInput_eq_of_nth hlen hlen' fun d hd hdL => hagree d hdL fun hdC => ?_
  rw [hC] at hdC
  exact (Finset.mem_filter.1 hdC).2.1 τ hτ hd.symm

/-- Two words of length `L` that agree at every position below `L` are equal. -/
theorem list_eq_of_nth {L : ℕ} {w w' : List Bool} (hw : w.length = L) (hw' : w'.length = L)
    (h : ∀ d, d < L → nth w d = nth w' d) : w = w' := by
  apply List.ext_getElem?
  intro d
  rw [← nth_eq_getElem?, ← nth_eq_getElem?]
  rcases lt_or_ge d L with hd | hd
  · exact h d hd
  · rw [nth_eq_none_of_le (by omega), nth_eq_none_of_le (by omega)]

theorem length_of_mem_matrixInputs {n b : ℕ} {w : List Bool} (hw : w ∈ matrixInputs n b) :
    w.length = n * n * b := by
  obtain ⟨A, rfl⟩ := hw; exact length_encode n b A

theorem ncard_inputsOfLength (L : ℕ) : (inputsOfLength L).ncard = 2 ^ L := by
  have e : (inputsOfLength L).ncard = Nat.card (List.Vector Bool L) := by
    rw [← Nat.card_coe_set_eq]
    rfl
  rw [e, Nat.card_eq_fintype_card, card_vector, Fintype.card_bool]

theorem ncard_matrixInputs (n b : ℕ) : (matrixInputs n b).ncard = 2 ^ (n * n * b) := by
  rw [matrixInputs_eq, ncard_inputsOfLength]

/-- A cut bit appears in the output during `J`, at a step common to the whole set, when `M` is
correct on the set. -/
theorem outBit_of_mem_cutSet_on {n b T : ℕ} {W : Set (List Bool)} (hobl : ObliviousOn M W T)
    (hcorr : ∀ w ∈ W, ∃ A : Matrix, w = encode n b A ∧
      (run M w T).outRev.reverse = encode n b (transpose A))
    {w₀ : List Bool} (hw₀ : w₀ ∈ W) {J : Finset ℕ} (hJ : ∀ τ ∈ J, τ < T) {d : ℕ}
    (hd : d ∈ cutSet M w₀ n b J) :
    ∃ τ ∈ J, ∀ w ∈ W, outBit M w τ = nth w d := by
  classical
  simp only [cutSet, Finset.mem_filter, Finset.mem_range] at hd
  obtain ⟨hdL, -, τ, hτJ, hsome, hlen⟩ := hd
  refine ⟨τ, hτJ, fun w hw => ?_⟩
  obtain ⟨A, rfl, hout⟩ := hcorr w hw
  have hsome' : (outBit M (encode n b A) τ).isSome := by
    rw [(hobl.2 _ hw w₀ hw₀ τ).2.2]; exact hsome
  have hlen' : (run M (encode n b A) τ).outRev.length = tpos n b d := by
    rw [oblivious_outRev_length hobl hw hw₀]; exact hlen
  rw [← output_nth_eq_outBit _ (hJ τ hτJ) hsome', hout, hlen', nth_encode_transpose_tpos A hdL]

/-- **The counting core of every cut lemma.** Let `F` be a set of matrix inputs, `C` a set of bit
positions and `e` any code with values in a finite type `E`. If two members of `F` with the same
code that agree outside `C` also agree on `C`, then `2^{|C|} |F| ≤ 2^{n²b} |E|`. -/
theorem two_pow_mul_ncard_le {n b : ℕ} {F : Set (List Bool)} (hF : F ⊆ matrixInputs n b)
    {C : Finset ℕ} (hC : C ⊆ Finset.range (n * n * b)) {E : Type*} [Fintype E] (e : List Bool → E)
    (hinj : ∀ w ∈ F, ∀ w' ∈ F, e w = e w' → (∀ d < n * n * b, d ∉ C → nth w d = nth w' d) →
      ∀ d ∈ C, nth w d = nth w' d) :
    2 ^ C.card * F.ncard ≤ 2 ^ (n * n * b) * Fintype.card E := by
  classical
  set D := Finset.range (n * n * b) \ C
  let ψ : List Bool → (D → Bool) × E := fun w => (fun d => (nth w d.1).getD false, e w)
  have hψ : Set.InjOn ψ F := by
    intro w hw w' hw' h
    have hlen := length_of_mem_matrixInputs (hF hw)
    have hlen' := length_of_mem_matrixInputs (hF hw')
    -- agreement outside `C`
    have hout : ∀ d < n * n * b, d ∉ C → nth w d = nth w' d := by
      intro d hdL hdC
      have := congrFun (congrArg Prod.fst h) ⟨d, Finset.mem_sdiff.2 ⟨Finset.mem_range.2 hdL, hdC⟩⟩
      simp only [ψ] at this
      rw [nth_eq_getElem?, nth_eq_getElem?, List.getElem?_eq_getElem (by omega),
        List.getElem?_eq_getElem (by omega)] at this ⊢
      simp only [Option.getD_some] at this
      rw [this]
    have hin := hinj w hw w' hw' (congrArg Prod.snd h) hout
    exact list_eq_of_nth hlen hlen' fun d hd => if hdC : d ∈ C then hin d hdC else hout d hd hdC
  have hcard : F.ncard ≤ Fintype.card ((D → Bool) × E) := by
    have := Set.ncard_le_ncard_of_injOn ψ (t := Set.univ) (fun _ _ => Set.mem_univ _) hψ
      Set.finite_univ
    rwa [Set.ncard_univ, Nat.card_eq_fintype_card] at this
  have hDC : D.card + C.card = n * n * b := by
    rw [Finset.card_sdiff_of_subset hC, Finset.card_range]
    have := Finset.card_le_card hC; rw [Finset.card_range] at this; omega
  calc 2 ^ C.card * F.ncard ≤ 2 ^ C.card * (2 ^ D.card * Fintype.card E) := by
        refine Nat.mul_le_mul_left _ (le_of_le_of_eq hcard ?_)
        simp [Fintype.card_prod, Fintype.card_bool]
    _ = _ := by rw [← Nat.mul_assoc, ← pow_add, Nat.add_comm, hDC]

/-- **The Cut Lemma on a set**, with obliviousness and correctness only on the set (which then
consists of matrix inputs): the counting core with the entry data as the code. -/
theorem cut_bound_on {n b T : ℕ} {W : Set (List Bool)} (hobl : ObliviousOn M W T)
    (hcorr : ∀ w ∈ W, ∃ A : Matrix, w = encode n b A ∧
      (run M w T).outRev.reverse = encode n b (transpose A))
    {w₀ : List Bool} (hw₀ : w₀ ∈ W) {J : Finset ℕ} (hJ : ∀ τ ∈ J, τ < T) :
    2 ^ (cutSet M w₀ n b J).card * W.ncard ≤
      2 ^ (n * n * b) *
        ((M.q + 1) ^ (entryPoints J).card * (M.g + 1) ^ (entryCells (workTraj M w₀) J).card) := by
  classical
  have hW : W ⊆ matrixInputs n b := fun w hw => by obtain ⟨A, rfl, -⟩ := hcorr w hw; exact ⟨A, rfl⟩
  have h := two_pow_mul_ncard_le hW (C := cutSet M w₀ n b J)
    (fun d hd => (Finset.mem_filter.1 hd).1)
    (fun w => ((fun τ => (run M w τ.1).state : entryPoints J → Fin (M.q + 1)),
      (fun p => headSym M w p.1.2 p.1.1 : entryCells (workTraj M w₀) J → Fin (M.g + 1))))
    (fun w hw w' hw' he hout d hdC => by
      -- the runs agree on `J`, which outputs the cut bit `d` at a common step
      have hcells : entryCells (workTraj M w) J = entryCells (workTraj M w₀) J := by
        rw [oblivious_workTraj hobl hw hw₀]
      have hloc := locality_oblivious hobl hw hw' hJ
        (fun τ hτ => congrFun (congrArg Prod.fst he) ⟨τ, hτ⟩)
        (fun p hp => congrFun (congrArg Prod.snd he) ⟨p, hcells ▸ hp⟩)
        (fun τ hτ => by
          rw [(hobl.2 w hw w₀ hw₀ τ).1]
          exact readInput_eq_of_agree rfl (length_of_mem_matrixInputs (hW hw))
            (length_of_mem_matrixInputs (hW hw')) hout hτ)
      obtain ⟨τ, hτJ, hτ⟩ := outBit_of_mem_cutSet_on hobl hcorr hw₀ hJ hdC
      rw [← hτ w hw, ← hτ w' hw']
      simp only [outBit]; rw [(hloc τ hτJ).2.2.2])
  simpa [Fintype.card_prod] using h

/-- A set of co-entropy `≤ m` is nonempty: `2^L ≤ 2^m |W|` forces `0 < |W|`. -/
theorem ncard_pos_of_coentropy {α : Type*} {L m : ℕ} {W : Set α} (hco : 2 ^ L ≤ 2 ^ m * W.ncard) :
    0 < W.ncard := by
  rcases Nat.eq_zero_or_pos W.ncard with h0 | h0
  · rw [h0, Nat.mul_zero] at hco; exact absurd hco (Nat.not_le.2 (Nat.two_pow_pos _))
  · exact h0

/-- **The Cut Lemma on a set of co-entropy `≤ m`**: `2^{|cut|} ≤ 2^m · (q+1)^{e₁} (g+1)^{e₂}`. -/
theorem cut_bound_on_coentropy {n b T : ℕ} {W : Set (List Bool)} (hobl : ObliviousOn M W T)
    (hcorr : ClassCorrect M n b T W) {w₀ : List Bool} (hw₀ : w₀ ∈ W) {J : Finset ℕ}
    (hJ : ∀ τ ∈ J, τ < T) {m : ℕ} (hco : 2 ^ (n * n * b) ≤ 2 ^ m * W.ncard) :
    2 ^ (cutSet M w₀ n b J).card ≤
      2 ^ m * ((M.q + 1) ^ (entryPoints J).card *
        (M.g + 1) ^ (entryCells (workTraj M w₀) J).card) := by
  have h := cut_bound_on hobl hcorr hw₀ hJ
  have hWpos : 0 < W.ncard := ncard_pos_of_coentropy hco
  have : 2 ^ (cutSet M w₀ n b J).card * W.ncard ≤
      (2 ^ m * ((M.q + 1) ^ (entryPoints J).card *
        (M.g + 1) ^ (entryCells (workTraj M w₀) J).card)) * W.ncard := by
    calc _ ≤ _ := h
      _ ≤ 2 ^ m * W.ncard * ((M.q + 1) ^ (entryPoints J).card *
            (M.g + 1) ^ (entryCells (workTraj M w₀) J).card) := Nat.mul_le_mul_right _ hco
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_right this hWpos

/-- **The Cut Lemma for families on a set of co-entropy `≤ m`** (product over a finite family of
step sets): `2^{Σ|cut|} ≤ 2^{|s| m} · (q+1)^{Σ e₁} (g+1)^{Σ e₂}`. -/
theorem cut_bound_sum_on {n b T : ℕ} {W : Set (List Bool)} (hobl : ObliviousOn M W T)
    (hcorr : ClassCorrect M n b T W) {w₀ : List Bool} (hw₀ : w₀ ∈ W) {m : ℕ}
    (hco : 2 ^ (n * n * b) ≤ 2 ^ m * W.ncard)
    {ι : Type*} (s : Finset ι) (J : ι → Finset ℕ) (hJ : ∀ u ∈ s, ∀ τ ∈ J u, τ < T) :
    2 ^ (∑ u ∈ s, (cutSet M w₀ n b (J u)).card) ≤
      2 ^ (s.card * m) * ((M.q + 1) ^ (∑ u ∈ s, (entryPoints (J u)).card) *
        (M.g + 1) ^ (∑ u ∈ s, (entryCells (workTraj M w₀) (J u)).card)) := by
  calc 2 ^ (∑ u ∈ s, (cutSet M w₀ n b (J u)).card)
      = ∏ u ∈ s, 2 ^ (cutSet M w₀ n b (J u)).card := (Finset.prod_pow_eq_pow_sum _ _ _).symm
    _ ≤ ∏ u ∈ s, (2 ^ m * ((M.q + 1) ^ (entryPoints (J u)).card *
          (M.g + 1) ^ (entryCells (workTraj M w₀) (J u)).card)) :=
        Finset.prod_le_prod (fun u hu => cut_bound_on_coentropy hobl hcorr hw₀ (hJ u hu) hco)
    _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const,
          Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum, ← pow_mul, Nat.mul_comm m]

/-- **The Cut Lemma, bit form**: the case `W` = all matrix inputs, `m = 0` of
`cut_bound_on_coentropy`. -/
theorem cut_bound {n b T : ℕ} (hobl : ObliviousOn M (matrixInputs n b) T)
    (hcorr : Transposes M n b) {w₀ : List Bool} (hw₀ : w₀ ∈ matrixInputs n b)
    {J : Finset ℕ} (hJ : ∀ τ ∈ J, τ < T) :
    2 ^ (cutSet M w₀ n b J).card ≤
      (M.q + 1) ^ (entryPoints J).card * (M.g + 1) ^ (entryCells (workTraj M w₀) J).card := by
  simpa using cut_bound_on_coentropy hobl (fun w hw => correct_of_transposes hcorr hw (hobl.1 w hw))
    hw₀ hJ (m := 0) (by rw [ncard_matrixInputs, pow_zero, one_mul])

/-- The decomposition `(i n + j) b + t` is injective on `i, j < n`, `t < b`. -/
theorem pos_inj {n b i j t i' j' t' : ℕ} (hj : j < n) (ht : t < b) (hj' : j' < n) (ht' : t' < b)
    (h : (i * n + j) * b + t = (i' * n + j') * b + t') : i = i' ∧ j = j' ∧ t = t' := by
  have hb : 0 < b := by omega
  have hn : 0 < n := by omega
  have e1 : ((i * n + j) * b + t) / b = ((i' * n + j') * b + t') / b := by rw [h]
  have e2 : ((i * n + j) * b + t) % b = ((i' * n + j') * b + t') % b := by rw [h]
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hb, Nat.div_eq_of_lt ht, Nat.zero_add,
    Nat.add_comm _ t', Nat.add_mul_div_right _ _ hb, Nat.div_eq_of_lt ht', Nat.zero_add] at e1
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht,
    Nat.add_comm _ t', Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht'] at e2
  have e3 : (i * n + j) / n = (i' * n + j') / n := by rw [e1]
  have e4 : (i * n + j) % n = (i' * n + j') % n := by rw [e1]
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hj, Nat.zero_add,
    Nat.add_comm _ j', Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hj', Nat.zero_add] at e3
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj,
    Nat.add_comm _ j', Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj'] at e4
  exact ⟨e3, e4, e2⟩

/-- Bounds for the position `(i n + j) b + t`. -/
theorem pos_lt {n b i j t : ℕ} (hi : i < n) (hj : j < n) (ht : t < b) :
    (i * n + j) * b + t < n * n * b := by
  calc (i * n + j) * b + t < (i * n + j) * b + b := by omega
    _ = (i * n + j + 1) * b := by ring
    _ ≤ (i * n + n) * b := by apply Nat.mul_le_mul_right; omega
    _ = (i + 1) * n * b := by ring
    _ ≤ n * n * b := by apply Nat.mul_le_mul_right; apply Nat.mul_le_mul_right; omega

theorem pos_mem_row {n b i j t : ℕ} (hj : j < n) (ht : t < b) :
    i * n * b ≤ (i * n + j) * b + t ∧ (i * n + j) * b + t < (i + 1) * n * b := by
  constructor
  · nlinarith [Nat.zero_le j, Nat.zero_le t, Nat.zero_le b]
  · calc (i * n + j) * b + t < (i * n + j) * b + b := by omega
      _ = (i * n + j + 1) * b := by ring
      _ ≤ (i * n + n) * b := by apply Nat.mul_le_mul_right; omega
      _ = (i + 1) * n * b := by ring

/-- Any set `C` of bit positions containing the bits of `S_J × [b]` has `|S_J| · b ≤ |C|`. -/
theorem cutPairs_card_mul_le_of {M : TM} {w₀ : List Bool} {n b : ℕ} {J : Finset ℕ}
    {C : Finset ℕ} (hC : ∀ i j t, i < n → i ∉ srcRows M w₀ n b J → j ∈ snkCols M w₀ n b J →
      t < b → (i * n + j) * b + t ∈ C) :
    (cutPairs M w₀ n b J).card * b ≤ C.card := by
  classical
  rw [show (cutPairs M w₀ n b J).card * b = ((cutPairs M w₀ n b J) ×ˢ Finset.range b).card by
    rw [Finset.card_product, Finset.card_range]]
  apply Finset.card_le_card_of_injOn (fun x => (x.1.1 * n + x.1.2) * b + x.2)
  · intro x hx
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range, cutPairs,
      Finset.mem_sdiff] at hx
    exact hC _ _ _ hx.1.1.1 hx.1.1.2 hx.1.2 hx.2
  · intro x hx y hy hxy
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range, cutPairs,
      Finset.mem_sdiff, snkCols, Finset.mem_filter] at hx hy
    obtain ⟨e1, e2, e3⟩ := pos_inj hx.1.2.1 hx.2 hy.1.2.1 hy.2 hxy
    exact Prod.ext (Prod.ext e1 e2) e3

/-- `|S_J| · b ≤ |cutSet J|`. -/
theorem cutPairs_card_mul_le (M : TM) (w₀ : List Bool) (n b : ℕ) (J : Finset ℕ) :
    (cutPairs M w₀ n b J).card * b ≤ (cutSet M w₀ n b J).card := by
  classical
  refine cutPairs_card_mul_le_of fun i j t hi hsrc hsnk ht => ?_
  have hj := Finset.mem_range.1 (Finset.mem_filter.1 hsnk).1
  obtain ⟨hrow1, hrow2⟩ := pos_mem_row (i := i) hj ht
  simp only [cutSet, Finset.mem_filter, Finset.mem_range]
  refine ⟨pos_lt hi hj ht, fun τ hτ heq => hsrc ?_, ?_⟩
  · simp only [srcRows, Finset.mem_filter, Finset.mem_range]
    exact ⟨hi, τ, hτ, by rw [heq]; exact_mod_cast hrow1, by rw [heq]; exact_mod_cast hrow2⟩
  · rw [tpos_spec hj ht]
    obtain ⟨hcol1, hcol2⟩ := pos_mem_row (i := j) (j := i) (t := t) hi ht
    exact (Finset.mem_filter.1 hsnk).2 _ hcol1 hcol2

/-! ### The Cut Lemma for the cut pairs `S_J`, log-free and bits forms -/

theorem cut_bound_pairs {n b T : ℕ} (hobl : ObliviousOn M (matrixInputs n b) T)
    (hcorr : Transposes M n b) {w₀ : List Bool} (hw₀ : w₀ ∈ matrixInputs n b)
    {J : Finset ℕ} (hJ : ∀ τ ∈ J, τ < T) :
    2 ^ (b * (cutPairs M w₀ n b J).card) ≤
      (M.q + 1) ^ (entryPoints J).card * (M.g + 1) ^ (entryCells (workTraj M w₀) J).card :=
  le_trans (Nat.pow_le_pow_right (by norm_num)
    (by rw [Nat.mul_comm]; exact cutPairs_card_mul_le M w₀ n b J)) (cut_bound hobl hcorr hw₀ hJ)

/-- From a log-free bound to a bits bound. -/
theorem bits_of_pow_le {a e₁ e₂ Q G : ℕ} (h : 2 ^ a ≤ (Q + 1) ^ e₁ * (G + 1) ^ e₂) :
    a ≤ e₁ * Nat.clog 2 (Q + 1) + e₂ * Nat.clog 2 (G + 1) := by
  have h1 : (Q + 1) ^ e₁ ≤ 2 ^ (e₁ * Nat.clog 2 (Q + 1)) := by
    rw [Nat.mul_comm, pow_mul]
    exact Nat.pow_le_pow_left (Nat.le_pow_clog (by norm_num) _) _
  have h2 : (G + 1) ^ e₂ ≤ 2 ^ (e₂ * Nat.clog 2 (G + 1)) := by
    rw [Nat.mul_comm, pow_mul]
    exact Nat.pow_le_pow_left (Nat.le_pow_clog (by norm_num) _) _
  have : 2 ^ a ≤ 2 ^ (e₁ * Nat.clog 2 (Q + 1) + e₂ * Nat.clog 2 (G + 1)) := by
    rw [pow_add]; exact le_trans h (Nat.mul_le_mul h1 h2)
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this

theorem cut_bound_bits {n b T : ℕ} (hobl : ObliviousOn M (matrixInputs n b) T)
    (hcorr : Transposes M n b) {w₀ : List Bool} (hw₀ : w₀ ∈ matrixInputs n b)
    {J : Finset ℕ} (hJ : ∀ τ ∈ J, τ < T) :
    b * (cutPairs M w₀ n b J).card ≤
      (entryPoints J).card * Nat.clog 2 (M.q + 1) +
        (entryCells (workTraj M w₀) J).card * Nat.clog 2 (M.g + 1) :=
  bits_of_pow_le (cut_bound_pairs hobl hcorr hw₀ hJ)

/-! ### The Cut Lemma for families -/

theorem cut_bound_sum {n b T : ℕ} (hobl : ObliviousOn M (matrixInputs n b) T)
    (hcorr : Transposes M n b) {w₀ : List Bool} (hw₀ : w₀ ∈ matrixInputs n b)
    {ι : Type*} (s : Finset ι) (J : ι → Finset ℕ) (hJ : ∀ u ∈ s, ∀ τ ∈ J u, τ < T) :
    2 ^ (∑ u ∈ s, (cutSet M w₀ n b (J u)).card) ≤
      (M.q + 1) ^ (∑ u ∈ s, (entryPoints (J u)).card) *
        (M.g + 1) ^ (∑ u ∈ s, (entryCells (workTraj M w₀) (J u)).card) := by
  simpa using cut_bound_sum_on hobl (fun w hw => correct_of_transposes hcorr hw (hobl.1 w hw))
    hw₀ (m := 0) (by rw [ncard_matrixInputs, pow_zero, one_mul]) s J hJ

theorem cut_bound_sum_bits {n b T : ℕ} (hobl : ObliviousOn M (matrixInputs n b) T)
    (hcorr : Transposes M n b) {w₀ : List Bool} (hw₀ : w₀ ∈ matrixInputs n b)
    {ι : Type*} (s : Finset ι) (J : ι → Finset ℕ) (hJ : ∀ u ∈ s, ∀ τ ∈ J u, τ < T) :
    b * (∑ u ∈ s, (cutPairs M w₀ n b (J u)).card) ≤
      (∑ u ∈ s, (entryPoints (J u)).card) * Nat.clog 2 (M.q + 1) +
        (∑ u ∈ s, (entryCells (workTraj M w₀) (J u)).card) * Nat.clog 2 (M.g + 1) := by
  rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun u hu => cut_bound_bits hobl hcorr hw₀ (hJ u hu))

theorem sum_cutPairs_ge (M : TM) (w₀ : List Bool) (n b : ℕ) {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (J : ι → Finset ℕ) (ρ : ℕ)
    (hρ : ∀ u ∈ s, (srcRows M w₀ n b (J u)).card ≤ ρ) :
    (s.biUnion (fun u => snkCols M w₀ n b (J u))).card * (n - ρ) ≤
      ∑ u ∈ s, (cutPairs M w₀ n b (J u)).card := by
  classical
  calc (s.biUnion (fun u => snkCols M w₀ n b (J u))).card * (n - ρ)
      ≤ (∑ u ∈ s, (snkCols M w₀ n b (J u)).card) * (n - ρ) :=
        Nat.mul_le_mul_right _ Finset.card_biUnion_le
    _ = ∑ u ∈ s, (snkCols M w₀ n b (J u)).card * (n - ρ) := Finset.sum_mul _ _ _
    _ ≤ ∑ u ∈ s, (cutPairs M w₀ n b (J u)).card := by
        apply Finset.sum_le_sum
        intro u hu
        rw [cutPairs, Finset.card_product, Nat.mul_comm]
        apply Nat.mul_le_mul_right
        have h1 := Finset.le_card_sdiff (srcRows M w₀ n b (J u)) (Finset.range n)
        rw [Finset.card_range] at h1
        have h2 := hρ u hu
        omega

/-- A label change between two steps with different labels. -/
theorem label_change_between (lab : ℕ → ℕ) {x y : ℕ} (hxy : x < y) (hlab : lab x ≠ lab y) :
    ∃ τ, x < τ ∧ τ ≤ y ∧ lab τ ≠ lab (τ - 1) := by
  obtain ⟨σ, h1, h2, h3, h4⟩ := exists_flip (P := fun τ => lab τ = lab x) hxy rfl (Ne.symm hlab)
  exact ⟨σ, h1, h2, fun h => h4 (h.trans h3)⟩

/-- Between two times with output lengths `≤ o` and `> o`, output position `o` is appended. -/
theorem exists_append_between (w : List Bool) {a e o : ℕ}
    (h1 : (run M w a).outRev.length ≤ o) (h2 : o < (run M w e).outRev.length) :
    ∃ τ, a ≤ τ ∧ τ < e ∧ (outBit M w τ).isSome ∧ (run M w τ).outRev.length = o := by
  have hae : a < e := by
    by_contra hc
    push Not at hc
    have := outRev_length_mono (M := M) w hc
    omega
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hae
  clear hae
  induction d with
  | zero =>
    simp only [Nat.add_zero] at h2
    have hs := outRev_length_succ (M := M) w a
    refine ⟨a, le_rfl, by omega, ?_, ?_⟩ <;> split_ifs at hs with hb <;> first | exact hb | omega
  | succ d ih =>
    by_cases hlt : o < (run M w (a + d + 1)).outRev.length
    · obtain ⟨τ, h1', h2', h3', h4'⟩ := ih hlt
      exact ⟨τ, h1', by omega, h3', h4'⟩
    · push Not at hlt
      have hs := outRev_length_succ (M := M) w (a + d + 1)
      rw [show a + (d + 1) + 1 = a + d + 1 + 1 by omega] at h2
      refine ⟨a + d + 1, by omega, by omega, ?_, ?_⟩ <;> split_ifs at hs with hb <;>
        first | exact hb | omega

/-- Every output position below the final length is appended at some step before `T`. -/
theorem exists_append_step (w : List Bool) {T o : ℕ} (ho : o < (run M w T).outRev.length) :
    ∃ τ < T, (outBit M w τ).isSome ∧ (run M w τ).outRev.length = o := by
  obtain ⟨τ, -, h1, h2, h3⟩ := exists_append_between (M := M) w (a := 0) (by simp [run, init]) ho
  exact ⟨τ, h1, h2, h3⟩

/-- Appending steps strictly increase the output length. -/
theorem append_step_lt (w : List Bool) {τ₁ τ₂ : ℕ} (h : τ₁ < τ₂)
    (hs : (outBit M w τ₁).isSome) :
    (run M w τ₁).outRev.length < (run M w τ₂).outRev.length := by
  have h1 := outRev_length_succ (M := M) w τ₁
  rw [ite_eq_left hs] at h1
  have h2 := outRev_length_mono (M := M) w (show τ₁ + 1 ≤ τ₂ from h)
  omega

/-- **The Cut Lemma for families, `σ ≤ M_b`, for one run**: it needs only `1 ≤ b` and that the run
has output at least `n²b` bits by time `T` (no obliviousness, correctness or halting). -/
theorem uncovered_cols_le_len {n b T : ℕ} (hb : 1 ≤ b) {w₀ : List Bool}
    (hlenT : n * n * b ≤ (run M w₀ T).outRev.length) (lab : ℕ → ℕ) :
    n - (((Finset.range T).image lab).biUnion (fun ℓ =>
        snkCols M w₀ n b ((Finset.range T).filter (fun τ => lab τ = ℓ)))).card ≤
      ((Finset.range T).filter (fun τ => 1 ≤ τ ∧ lab τ ≠ lab (τ - 1))).card := by
  classical
  set Cov := ((Finset.range T).image lab).biUnion (fun ℓ =>
    snkCols M w₀ n b ((Finset.range T).filter (fun τ => lab τ = ℓ))) with hCov
  set Ch := (Finset.range T).filter (fun τ => 1 ≤ τ ∧ lab τ ≠ lab (τ - 1)) with hCh
  let g : ℕ → ℕ := fun τ => ((run M w₀ τ).outRev.length - 1) / (n * b)
  have hsub : Finset.range n \ Cov ⊆ Ch.image g := by
    intro j hj
    rw [Finset.mem_sdiff, Finset.mem_range] at hj
    obtain ⟨hjn, hjC⟩ := hj
    have hnb : 0 < n * b := Nat.mul_pos (by omega) hb
    have hcol : j * n * b + n * b = (j + 1) * n * b := by ring
    have hcolle : (j + 1) * n * b ≤ n * n * b :=
      Nat.mul_le_mul_right b (Nat.mul_le_mul_right n hjn)
    have ho₁ : j * n * b < (run M w₀ T).outRev.length := by omega
    obtain ⟨s₁, hs₁T, hs₁, hlen₁⟩ := exists_append_step w₀ ho₁
    have hnot : j ∉ snkCols M w₀ n b ((Finset.range T).filter (fun τ => lab τ = lab s₁)) := by
      intro hj'
      apply hjC
      rw [hCov, Finset.mem_biUnion]
      exact ⟨lab s₁, Finset.mem_image.2 ⟨s₁, Finset.mem_range.2 hs₁T, rfl⟩, hj'⟩
    simp only [snkCols, Finset.mem_filter, Finset.mem_range, not_and, not_forall] at hnot
    obtain ⟨o, ho1, ho2, hnotA⟩ := hnot hjn
    have hoT : o < (run M w₀ T).outRev.length := by omega
    obtain ⟨s₂, hs₂T, hs₂, hlen₂⟩ := exists_append_step w₀ hoT
    have hlab : lab s₂ ≠ lab s₁ := by
      intro hl
      exact hnotA ⟨s₂, Finset.mem_filter.2 ⟨Finset.mem_range.2 hs₂T, hl⟩, hs₂, hlen₂⟩
    have hlt : s₁ < s₂ := by
      rcases lt_trichotomy s₁ s₂ with h | h | h
      · exact h
      · exact absurd (congrArg lab h).symm hlab
      · have := append_step_lt w₀ h hs₂; omega
    obtain ⟨τ, hτ1, hτ2, hτ3⟩ := label_change_between lab hlt (fun h => hlab h.symm)
    refine Finset.mem_image.2 ⟨τ, ?_, ?_⟩
    · rw [hCh, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, by omega, hτ3⟩
    · have hA := append_step_lt w₀ hτ1 hs₁
      have hB := outRev_length_mono (M := M) w₀ hτ2
      show ((run M w₀ τ).outRev.length - 1) / (n * b) = j
      have e1 : j * n * b = j * (n * b) := by ring
      have e2 : (j + 1) * n * b = (j + 1) * (n * b) := by ring
      apply Nat.div_eq_of_lt_le <;> omega
  have hCovsub : Cov ⊆ Finset.range n := by
    intro j hj
    rw [hCov, Finset.mem_biUnion] at hj
    obtain ⟨ℓ, -, hj⟩ := hj
    simp only [snkCols, Finset.mem_filter] at hj
    exact hj.1
  calc n - Cov.card = (Finset.range n \ Cov).card := by
        rw [Finset.card_sdiff_of_subset hCovsub, Finset.card_range]
    _ ≤ (Ch.image g).card := Finset.card_le_card hsub
    _ ≤ Ch.card := Finset.card_image_le

/-- **The Cut Lemma for families, `σ ≤ M_b`.** -/
theorem uncovered_cols_le {n b T : ℕ} (hb : 1 ≤ b)
    (hobl : ObliviousOn M (matrixInputs n b) T)
    (hcorr : Transposes M n b) {w₀ : List Bool} (hw₀ : w₀ ∈ matrixInputs n b) (lab : ℕ → ℕ) :
    n - (((Finset.range T).image lab).biUnion (fun ℓ =>
        snkCols M w₀ n b ((Finset.range T).filter (fun τ => lab τ = ℓ)))).card ≤
      ((Finset.range T).filter (fun τ => 1 ≤ τ ∧ lab τ ≠ lab (τ - 1))).card := by
  refine uncovered_cols_le_len hb (le_of_eq ?_) lab
  obtain ⟨A₀, rfl⟩ := hw₀
  rw [← List.length_reverse, output_eq_of_haltsAt hcorr A₀ (hobl.1 _ ⟨A₀, rfl⟩), length_encode]

/-! ### Inputs as vectors -/

/-- The input vector of a list (bits beyond the list read `false`). -/
def toVec (L : ℕ) (w : List Bool) : Fin L → Bool := fun i => w.getD i false

theorem toVec_ofFn {L : ℕ} (x : Fin L → Bool) : toVec L (List.ofFn x) = x := by
  funext i
  simp [toVec]

theorem ofFn_toVec {L : ℕ} {w : List Bool} (hw : w.length = L) : List.ofFn (toVec L w) = w := by
  apply List.ext_getElem (by rw [List.length_ofFn, hw])
  intro i h1 h2
  rw [List.getElem_ofFn]
  simp only [toVec]
  rw [List.getD_eq_getElem _ _ h2]

/-- Reading a set of matrix inputs as a set of vectors keeps its size. -/
theorem ncard_ofFn_preimage {n b : ℕ} {F : Set (List Bool)} (hF : F ⊆ matrixInputs n b) :
    {v : Fin (n * n * b) → Bool | List.ofFn v ∈ F}.ncard = F.ncard := by
  apply Set.ncard_preimage_of_injective_subset_range List.ofFn_injective
  intro w hw
  exact ⟨toVec (n * n * b) w, ofFn_toVec (length_of_mem_matrixInputs (hF hw))⟩

theorem nth_ofFn {L : ℕ} (v : Fin L → Bool) {d : ℕ} (hd : d < L) :
    nth (List.ofFn v) d = some (v ⟨d, hd⟩) := by
  rw [nth_eq_getElem?]
  simp [hd]

theorem ofFn_mem_matrixInputs {n b : ℕ} (v : Fin (n * n * b) → Bool) :
    List.ofFn v ∈ matrixInputs n b := by
  rw [matrixInputs_eq]
  simp [inputsOfLength]


end Transpose.Tape.Impl
