import Transpose.Tape.CECode
import Transpose.Tape.CEProfile
import Transpose.Tape.MStarAdaptive

/-!
# A fast transposer yields network codes

* `exists_popular_traceClass_on`: the popular trace within any set `F₀` of inputs on which the machine
  halts within `T_max` steps.
* `code_bits_of_class` (in `CECode.lean`): **the single machine reduction**. The code of a trace class
  (`traceClass_code`) on the representative's own diagram, at the per-node blocks plus `s` bits per
  memory edge, when the state bits plus the head-position bits fit in `s`. Every other capacity
  profile follows from it by TM-free conversions: `solves_profileCap_addTapes` (extra bits become
  stationary tapes) and `robustNoCode_bits_iff`.
* `codes_of_fastOn_bits`: a machine that transposes correctly within `c L` steps on a set `F₀` of
  co-entropy `C₀ n w` gives such a code for a set of co-entropy `(C₀ + traceConst M c) n w`.
  `codes_of_fastOn`: the same at the per-node profile on `k + 1` tapes (one block of extra bits, once
  `n ≥ slotSize k c` and the state takes at most half a block). Correctness implies that `F₀`
  consists of matrix inputs (`fast_subset_matrixInputs`).
* `fast_of_computesWithin`: a machine transposing within `c (L + 1)` steps at size `n` is fast and
  correct on all matrix inputs.
* `no_fast_transposer_of_robustNoCode_bits`: the target with `s` extra bits rules out every machine
  family whose state bits plus head-position bits fit in `s`.
* Oblivious machines: `NoCode_TM` (and `NoCode_TM_io`) refutes oblivious (T).

The consequences of `RobustNoCode_TM` for machines (`no_fast_transposer_of_robustNoCode`,
`linearTime_fails_of_robustNoCode`, ¬(T)) are corollaries of the stronger co-entropy-`O(n)` forms
(`CoarseTrace.lean`).
-/
namespace Transpose.Tape.Impl

open Transpose TSDiagram

variable {M : TM}

/-- The size from which the `k + 1` head positions take at most half a block, for running time
`≤ c L` and `k` work tapes (`pos_bits_le`). -/
def slotSize (k c : ℕ) : ℕ := max 1 (2 * (k + 1) * (Nat.clog 2 (2 * c + 1) + 3))

/-- **The head positions take at most half a block**: `2 (k+1) ⌈log₂(2T+1)⌉ ≤ n w` once
`n ≥ slotSize k c` and `T ≤ c L`. -/
theorem pos_bits_le {k c n T : ℕ} (hn : slotSize k c ≤ n) (hT : T ≤ c * (n * n * entryBits n)) :
    2 * ((k + 1) * Nat.clog 2 (2 * T + 1)) ≤ n * entryBits n := by
  have hn1 : 1 ≤ n := le_trans (le_max_left _ _) hn
  have hb1 : 1 ≤ entryBits n := by unfold entryBits; omega
  have hTr : ((T : ℕ) : ℝ) ≤ ((c : ℕ) : ℝ) * inputLength n := by
    have : ((T : ℕ) : ℝ) ≤ ((c * (n * n * entryBits n) : ℕ) : ℝ) := by exact_mod_cast hT
    rw [inputLength]; push_cast at this ⊢; linarith
  have hclog := clog_time_le hn1 hTr
  rw [Nat.ceil_natCast] at hclog
  set K₁ := Nat.clog 2 (2 * c + 1) with hK₁
  have hsize : 2 * (k + 1) * (K₁ + 3) ≤ n := le_trans (le_max_right _ _) hn
  have h1 : (k + 1) * Nat.clog 2 (2 * T + 1) ≤ (k + 1) * (K₁ + 3) * entryBits n := by
    calc (k + 1) * Nat.clog 2 (2 * T + 1) ≤ (k + 1) * (K₁ + 3 * entryBits n) :=
          Nat.mul_le_mul_left _ hclog
      _ ≤ (k + 1) * ((K₁ + 3) * entryBits n) := by
          apply Nat.mul_le_mul_left
          have : K₁ ≤ K₁ * entryBits n := Nat.le_mul_of_pos_right _ hb1
          nlinarith
      _ = (k + 1) * (K₁ + 3) * entryBits n := by ring
  calc 2 * ((k + 1) * Nat.clog 2 (2 * T + 1)) ≤ 2 * ((k + 1) * (K₁ + 3) * entryBits n) :=
        Nat.mul_le_mul_left _ h1
    _ = (2 * (k + 1) * (K₁ + 3)) * entryBits n := by ring
    _ ≤ n * entryBits n := Nat.mul_le_mul_right _ hsize

/-! ### Fast transposers give codes -/

/-- The inputs on which a machine outputs a transposed encoding are matrix inputs. -/
theorem fast_subset_matrixInputs {n Tmax : ℕ} {F₀ : Set (List Bool)}
    (hfast : ∀ w ∈ F₀, ∃ T ≤ Tmax, HaltsAt M w T ∧ ∃ A : Matrix, w = encode n (entryBits n) A ∧
      (run M w T).outRev.reverse = encode n (entryBits n) (transpose A)) :
    F₀ ⊆ matrixInputs n (entryBits n) := fun w hw => by
  obtain ⟨T, -, -, A, rfl, -⟩ := hfast w hw; exact ⟨A, rfl⟩

/-- **The popular class of a fast transposer.** Let `M` output the transposed encoding within `c L`
steps on every input of a set `F₀` of co-entropy `≤ C₀ n w`. Then some trace class `F ⊆ F₀`, with
halting time `T ≤ c L`, has co-entropy `≤ (C₀ + traceConst M c) n w`, and `M` is correct on it (the
case `m = C₀ n w` of `class_of_fast`). -/
theorem class_of_fastOn {c C₀ n : ℕ} (hn1 : 1 ≤ n) {F₀ : Set (List Bool)}
    (hco : 2 ^ (n * n * entryBits n) ≤ 2 ^ (C₀ * n * entryBits n) * F₀.ncard)
    (hfast : ∀ w ∈ F₀, ∃ T ≤ c * (n * n * entryBits n), HaltsAt M w T ∧
      ∃ A : Matrix, w = encode n (entryBits n) A ∧
        (run M w T).outRev.reverse = encode n (entryBits n) (transpose A)) :
    ∃ T ≤ c * (n * n * entryBits n), ∃ (F : Set (List Bool)) (w₀ : List Bool),
      TraceClass M n (entryBits n) (slotLen M n) T F w₀ ∧ ClassCorrect M n (entryBits n) T F ∧
      2 ^ (n * n * entryBits n) ≤
        2 ^ ((C₀ + traceConst M (c : ℝ)) * n * entryBits n) * F.ncard := by
  obtain ⟨T, hT, F, w₀, hF, -, hcorr, hco'⟩ := class_of_fast (c := (c : ℝ)) hn1 hco
    (fun w hw => by
      obtain ⟨T, hT, hh, hout⟩ := hfast w hw
      exact ⟨T, by rw [inputLength]; exact_mod_cast hT, hh, hout⟩)
  refine ⟨T, by rw [inputLength] at hT; exact_mod_cast hT, F, w₀, hF, hcorr, ?_⟩
  exact hco'.trans_eq (by congr 2; ring)

/-- **A fast transposer gives a code with `s` extra bits.** If the state bits plus the head-position
bits of `M` fit in `s`, its popular class is a code on its own `M.k`-tape diagram, at the per-node
capacities plus `s` bits per memory edge (no stationary tape needed). -/
theorem codes_of_fastOn_bits {c C₀ n s : ℕ} (hn1 : 1 ≤ n)
    (hs : Nat.clog 2 (M.q + 1) + (M.k + 1) * Nat.clog 2 (2 * (c * (n * n * entryBits n)) + 1) ≤ s)
    {F₀ : Set (List Bool)}
    (hco : 2 ^ (n * n * entryBits n) ≤ 2 ^ (C₀ * n * entryBits n) * F₀.ncard)
    (hfast : ∀ w ∈ F₀, ∃ T ≤ c * (n * n * entryBits n), HaltsAt M w T ∧
      ∃ A : Matrix, w = encode n (entryBits n) A ∧
        (run M w T).outRev.reverse = encode n (entryBits n) (transpose A)) :
    ∃ (D : TSDiagram M.k) (F : Set (Fin (n * n * entryBits n) → Bool)) (code : NetCode),
      D.Valid (n * n * entryBits n) ∧ D.T ≤ c * (n * n * entryBits n) ∧
      2 ^ (n * n * entryBits n) ≤
        2 ^ ((C₀ + traceConst M (c : ℝ)) * n * entryBits n) * F.ncard ∧
      D.Solves n (cellBits M) (D.blockCap n (cellBits M)
        (fun y => ∑ t, (pairRes (blockSize (cellBits M) n) (D.work t) D.T y).card) s) F code := by
  obtain ⟨T, hTle, F, w₀, hF, hcorr, hco'⟩ := class_of_fastOn hn1 hco hfast
  have hclog : Nat.clog 2 (2 * T + 1) ≤ Nat.clog 2 (2 * (c * (n * n * entryBits n)) + 1) :=
    Nat.clog_mono_right 2 (by omega)
  obtain ⟨code, hDv, hsol⟩ := code_bits_of_class hn1
    (le_trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ hclog) _) hs) hF hcorr
  have hFm : F ⊆ matrixInputs n (entryBits n) := fun w hw => (hF.2 w hw).1
  exact ⟨runDiagram M w₀ T, {v | List.ofFn v ∈ F}, code, hDv, hTle,
    by rw [ncard_ofFn_preimage hFm]; exact hco', hsol⟩

/-- **A machine that transposes a large set of inputs fast gives a code** at the per-node profile.
Let `M` transpose correctly within `c L` steps every input of a set `F₀` of co-entropy `≤ C₀ n w`, at
a size `n ≥ slotSize M.k c` where its state takes at most half a block. Then there are a valid
`(M.k + 1)`-tape diagram of length `≤ c L`, capacities within the block profile
(`G = cellBits M`), a set of inputs of co-entropy `≤ (C₀ + traceConst M c) n w` and a causal code
solving complete exchange on it. (From `codes_of_fastOn_bits` with one block of extra bits, which one
stationary tape carries: `solves_profileCap_addTapes`.) -/
theorem codes_of_fastOn {c C₀ n : ℕ} (hn : slotSize M.k c ≤ n)
    (hq : 2 * Nat.clog 2 (M.q + 1) ≤ n * entryBits n) {F₀ : Set (List Bool)}
    (hco : 2 ^ (n * n * entryBits n) ≤ 2 ^ (C₀ * n * entryBits n) * F₀.ncard)
    (hfast : ∀ w ∈ F₀, ∃ T ≤ c * (n * n * entryBits n), HaltsAt M w T ∧
      ∃ A : Matrix, w = encode n (entryBits n) A ∧
        (run M w T).outRev.reverse = encode n (entryBits n) (transpose A)) :
    ∃ (D : TSDiagram (M.k + 1)) (cap : ℕ × ℕ → ℕ) (F : Set (Fin (n * n * entryBits n) → Bool))
      (code : NetCode),
      D.Valid (n * n * entryBits n) ∧ D.T ≤ c * (n * n * entryBits n) ∧
      D.CapProfile n (cellBits M) cap ∧
      2 ^ (n * n * entryBits n) ≤
        2 ^ ((C₀ + traceConst M (c : ℝ)) * n * entryBits n) * F.ncard ∧
      D.Solves n (cellBits M) cap F code := by
  have hn1 : 1 ≤ n := le_trans (le_max_left _ _) hn
  have hpos := pos_bits_le hn (le_refl (c * (n * n * entryBits n)))
  have hrG := slotLen_mul_ge M n
  obtain ⟨D, F, code, hDv, hDT, hcoF, hsol⟩ :=
    codes_of_fastOn_bits (s := slotLen M n * cellBits M) hn1 (by omega) hco hfast
  exact ⟨addTapes D 1, _, F, code, valid_addTapes D hDv 1, by rw [T_addTapes]; exact hDT,
    capProfile_profileCap _ n _, hcoF,
    solves_profileCap_addTapes (one_le_slotLen M hn1) (by rw [Nat.one_mul]; exact le_rfl) hsol⟩

/-- **A machine transposing within `c (L + 1)` steps at size `n` is fast and correct**: it halts
with the transposed encoding within `2 c L` steps on every `n × n` matrix input. -/
theorem fast_of_computesWithin {c n : ℕ} (hn1 : 1 ≤ n)
    (hM : ∀ A : Matrix, ComputesWithin M (encode n (entryBits n) A)
      (encode n (entryBits n) (transpose A)) (c * (inputLength n + 1))) :
    ∀ w ∈ matrixInputs n (entryBits n), ∃ T ≤ 2 * c * (n * n * entryBits n), HaltsAt M w T ∧
      ∃ A : Matrix, w = encode n (entryBits n) A ∧
        (run M w T).outRev.reverse = encode n (entryBits n) (transpose A) := by
  have hb1 : 1 ≤ entryBits n := by unfold entryBits; omega
  have hL1 : 1 ≤ n * n * entryBits n := Nat.one_le_iff_ne_zero.2 (by positivity)
  rintro w ⟨A, rfl⟩
  obtain ⟨T, hT, hh, hout⟩ := (computesWithin_iff _ _).1 (hM A)
  refine ⟨T, ?_, hh, A, rfl, hout⟩
  have : T ≤ c * (n * n * entryBits n + 1) := hT
  nlinarith

/-- The size from which an oblivious machine transposing within `c (L + 1)` steps gives codes. -/
def codeSize (M : TM) (c : ℕ) : ℕ := max (slotSize M.k (2 * c)) (2 * Nat.clog 2 (M.q + 1))

/-! ### Consequences of the target with extra bits -/

/-- **The target with `s` extra bits rules out every machine family whose state bits plus
head-position bits fit in `s`.** Under `RobustNoCode_TM_bits s`, for all `k`, `g`, `c`, `C₀` and all
large `n`: no machine with `k` work tapes and alphabet `g + 1` (any transition table, which may depend
on `n`) with `⌈log₂(q+1)⌉ + (k+1)⌈log₂(2cL+1)⌉ ≤ s k n` outputs the transposed encoding within `c L`
steps on every input of a set of at least `2^{L - C₀ n w}` matrix inputs. -/
theorem no_fast_transposer_of_robustNoCode_bits {s : ℕ → ℕ → ℕ} (h : RobustNoCode_TM_bits s)
    (k g c C₀ : ℕ) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ M : TM, M.k = k → M.g = g →
      Nat.clog 2 (M.q + 1) + (k + 1) * Nat.clog 2 (2 * (c * (n * n * entryBits n)) + 1) ≤ s k n →
      ∀ F₀ : Set (List Bool),
        2 ^ (n * n * entryBits n) ≤ 2 ^ (C₀ * n * entryBits n) * F₀.ncard →
        ¬ ∀ w ∈ F₀, ∃ T ≤ c * (n * n * entryBits n), HaltsAt M w T ∧
          ∃ A : Matrix, w = encode n (entryBits n) A ∧
            (run M w T).outRev.reverse = encode n (entryBits n) (transpose A) := by
  obtain ⟨M₀, hM₀k, hM₀g⟩ : ∃ M₀ : TM, M₀.k = k ∧ M₀.g = g :=
    ⟨⟨k, g, 0, fun _ _ _ => none⟩, rfl, rfl⟩
  obtain ⟨n₀, hn₀⟩ := h k (cellBits M₀) c (C₀ + traceConst M₀ (c : ℝ)) (cellBits_pos M₀)
  refine ⟨max n₀ 1, fun n hn M hk hg hs F₀ hco hfast => ?_⟩
  subst hk
  have hG : cellBits M = cellBits M₀ := by unfold cellBits; rw [hg, hM₀g]
  have hC : traceConst M (c : ℝ) = traceConst M₀ (c : ℝ) := by
    unfold traceConst horizon; rw [hG, hM₀k]
  obtain ⟨D, F, code, hDv, hDT, hcoF, hsol⟩ :=
    codes_of_fastOn_bits (le_trans (le_max_right _ _) hn) hs hco hfast
  rw [hG] at hsol
  rw [hC] at hcoF
  exact hn₀ n (le_trans (le_max_left _ _) hn) D hDv hDT F hcoF code hsol

/-! ### Oblivious machines -/

/-- **An oblivious linear-time transposer gives codes for independent sources**: constants
`k, G ≥ 1, c` such that for all large `n` a code as in `NoCode_TM` exists. -/
theorem codes_of_obliviousLinearTimeTransposable (h : ObliviousLinearTimeTransposable) :
    ∃ (k G c : ℕ), 1 ≤ G ∧ ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      ∃ (D : TSDiagram k) (cap : ℕ × ℕ → ℕ) (code : NetCode),
        D.Valid (n * n * entryBits n) ∧ D.T ≤ c * (n * n * entryBits n) ∧ D.CapProfile n G cap ∧
        D.Solves n G cap Set.univ code := by
  obtain ⟨M, c, hM, hobl⟩ := h
  refine ⟨M.k + 1, cellBits M, 2 * c, cellBits_pos M, codeSize M c, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hn)
  have hb1 : 1 ≤ entryBits n := by unfold entryBits; omega
  have hq : 2 * Nat.clog 2 (M.q + 1) ≤ n * entryBits n :=
    le_trans (le_trans (le_max_right _ _) hn) (Nat.le_mul_of_pos_right _ hb1)
  have hcorr : Transposes M n (entryBits n) := transposes_of_transposesWithin hM n hn1
  obtain ⟨T, hT⟩ := hobl n hn1
  have hw₀ : encode n (entryBits n) (fun _ _ _ => false) ∈ matrixInputs n (entryBits n) := ⟨_, rfl⟩
  have hF := (traceClass_of_oblivious (r := slotLen M n) hT hw₀).1
  -- the common halting time is at most `2 c L`
  have hTle : T ≤ 2 * c * (n * n * entryBits n) := by
    obtain ⟨T', hT', hh, -⟩ := fast_of_computesWithin hn1 (hM n hn1) _ hw₀
    rw [haltsAt_unique (hT.1 _ hw₀) hh]; exact hT'
  have hpos := pos_bits_le (le_trans (le_max_left _ _) hn) hTle
  have hrG := slotLen_mul_ge M n
  obtain ⟨code, hDv, hsol⟩ := code_bits_of_class (s := slotLen M n * cellBits M) hn1 (by omega) hF
    (classCorrect_of_transposes hcorr hF)
  have huniv : {v : Fin (n * n * entryBits n) → Bool | List.ofFn v ∈ matrixInputs n (entryBits n)} =
      Set.univ := Set.eq_univ_of_forall (fun v => ofFn_mem_matrixInputs v)
  rw [huniv] at hsol
  exact ⟨addTapes (runDiagram M _ T) 1, _, code, valid_addTapes _ hDv 1,
    by rw [T_addTapes]; exact hTle, capProfile_profileCap _ n _,
    solves_profileCap_addTapes (one_le_slotLen M hn1) (by rw [Nat.one_mul]; exact le_rfl) hsol⟩

/-- **`NoCode_TM` refutes oblivious (T).** -/
theorem not_obliviousLinearTimeTransposable_of_noCode (h : NoCode_TM) :
    ¬ ObliviousLinearTimeTransposable := by
  intro hT
  obtain ⟨k, G, c, hG, n₀, hcodes⟩ := codes_of_obliviousLinearTimeTransposable hT
  obtain ⟨n₁, hn₁⟩ := h k G c hG
  obtain ⟨D, cap, code, hDv, hDT, hcap, hsol⟩ := hcodes (max n₀ n₁) (le_max_left _ _)
  exact hn₁ (max n₀ n₁) (le_max_right _ _) D hDv hDT code
    (solves_mono D (le_profileCap D hcap) hsol)

/-- **`NoCode_TM_io` refutes oblivious (T).** -/
theorem not_obliviousLinearTimeTransposable_of_noCode_io (h : NoCode_TM_io) :
    ¬ ObliviousLinearTimeTransposable := by
  intro hT
  obtain ⟨k, G, c, hG, n₀, hcodes⟩ := codes_of_obliviousLinearTimeTransposable hT
  obtain ⟨n, hn, hno⟩ := h k G c hG n₀
  obtain ⟨D, cap, code, hDv, hDT, hcap, hsol⟩ := hcodes n hn
  exact hno D hDv hDT code (solves_mono D (le_profileCap D hcap) hsol)

end Transpose.Tape.Impl
