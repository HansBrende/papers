import Transpose.Tape.Corollaries
import Transpose.Tape.DefsM

/-! # A cell-accurate cut inequality

The first paper's walk-level cut inequality `CutIneq` (Definition 7.4) charges `3r` cells per tape at
every label change and `r` cells per crossing chord, whether or not those cells are ever read. Here
`CellCutIneq` charges only the entry cells actually inherited by each label class: the pairs
`(t, τ)` with `τ` in the class at which work head `t` reads a cell last written outside the class
(the entry cells of the first paper's Cut Lemma).

* `cellCutIneq_of_oblivious_on`: every machine that is oblivious and correct on a set of co-entropy
  `≤ D` satisfies `CellCutIneq` with slack `D` and boundary cost `⌈log₂ (q+1)⌉`, at its common
  running time `T` on the set (in particular every linear-time oblivious transposer does).
* `cellCutIneq_of_oblivious`: the case of all matrix inputs, `D = 0`.

The proofs follow the first paper's proof of Discrete Isoperimetry (`isoperimetry_res_on`) and stop
before its final charging step, which replaces the entry cells by `r (3k M_b + Σ χ)`.
-/

namespace PaddingMemo

open Transpose Transpose.Tape Transpose.Tape.Impl
open scoped BigOperators

/-- **The cell-accurate cut inequality** at one size, for `k` walks `h t` (block size `r`, length `T`,
`N = ⌈T/r⌉` slots): for every slot labelling with at most `m` slots per label and `M_b` label
changes, `(n − M_b)(n − 2m) b ≤ (M_b + 1) D + M_b s + G Σ_ℓ |entryCells(J_ℓ)|`, where `J_ℓ` is the set
of steps below `T` in slots labelled `ℓ` and the sum runs over the labels used. -/
def CellCutIneq {k : ℕ} (n G r T D s : ℕ) (h : Fin k → ℕ → ℤ) : Prop :=
  ∀ (lab : ℕ → ℕ) (m : ℕ),
    (∀ ℓ, ((Finset.range (numSlots r T)).filter (fun y => lab y = ℓ)).card ≤ m) →
    (n - labelChanges lab (numSlots r T)) * (n - 2 * m) * entryBits n ≤
      (labelChanges lab (numSlots r T) + 1) * D + labelChanges lab (numSlots r T) * s +
        G * ∑ ℓ ∈ (Finset.range (numSlots r T)).image lab,
          (entryCells (fun τ t => h t τ) (labelPart r lab T ℓ)).card

/-- From `2^X ≤ 2^(c D) (q+1)^a (g+1)^e` to `X ≤ c D + a ⌈log₂ (q+1)⌉ + ⌈log₂ (g+1)⌉ e`. -/
theorem exp_bound_to_linear {X c D q g a e : ℕ}
    (h : 2 ^ X ≤ 2 ^ (c * D) * ((q + 1) ^ a * (g + 1) ^ e)) :
    X ≤ c * D + a * Nat.clog 2 (q + 1) + Nat.clog 2 (g + 1) * e := by
  have hq : (q + 1) ^ a ≤ 2 ^ (a * Nat.clog 2 (q + 1)) := by
    rw [Nat.mul_comm, pow_mul]
    exact Nat.pow_le_pow_left (Nat.le_pow_clog (by norm_num) _) a
  have hg : (g + 1) ^ e ≤ 2 ^ (Nat.clog 2 (g + 1) * e) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left (Nat.le_pow_clog (by norm_num) _) e
  have h2 : 2 ^ X ≤ 2 ^ (c * D + a * Nat.clog 2 (q + 1) + Nat.clog 2 (g + 1) * e) := by
    calc 2 ^ X ≤ 2 ^ (c * D) * ((q + 1) ^ a * (g + 1) ^ e) := h
      _ ≤ 2 ^ (c * D) * (2 ^ (a * Nat.clog 2 (q + 1)) * 2 ^ (Nat.clog 2 (g + 1) * e)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul hq hg)
      _ = 2 ^ (c * D + a * Nat.clog 2 (q + 1) + Nat.clog 2 (g + 1) * e) := by
          rw [← pow_add, ← pow_add, Nat.add_assoc]
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h2

/-- **Oblivious machines correct on a set of co-entropy `≤ D` satisfy the cell-accurate cut
inequality**, with slack `D` and boundary cost `⌈log₂ (q+1)⌉`, at its common running time `T` on `W` (no linear-time
assumption is needed). -/
theorem cellCutIneq_of_oblivious_on {M : TM} {n T r D : ℕ} {W : Set (List Bool)}
    (hobl : ObliviousOn M W T) (hcorr : ClassCorrect M n (entryBits n) T W) {w₀ : List Bool}
    (hw₀ : w₀ ∈ W) (hco : 2 ^ (n * n * entryBits n) ≤ 2 ^ D * W.ncard)
    (hr : 1 ≤ r) (hrnb : r ≤ n * entryBits n) :
    CellCutIneq n (Nat.clog 2 (M.g + 1)) r T D (Nat.clog 2 (M.q + 1))
      (fun t τ => workTraj M w₀ τ t) := by
  intro lab m hm
  set b := entryBits n
  set N := numSlots r T
  set s := (Finset.range N).image lab
  set Mb := labelChanges lab N
  -- the lower side: cut pairs of the label classes
  have hlow := lower_side_labels (M := M) (le_of_eq (outLen_of_classCorrect hcorr hw₀).symm)
    hr hrnb lab m hm
  rw [Finset.mul_sum] at hlow
  have hcut : ∑ ℓ ∈ s, b * (cutPairs M w₀ n b (labelPart r lab T ℓ)).card ≤
      ∑ ℓ ∈ s, (cutSet M w₀ n b (labelPart r lab T ℓ)).card :=
    Finset.sum_le_sum fun ℓ _ => by rw [Nat.mul_comm]; exact cutPairs_card_mul_le M w₀ n b _
  -- the Cut Lemma for the family of label classes
  have hfam := cut_bound_sum_on hobl hcorr hw₀ hco s (labelPart r lab T)
    (fun ℓ _ => labelPart_subset lab T ℓ)
  -- entry points: at most one per label change
  have he1 := (sum_entry_labelPart_le (M := M) (w₀ := w₀) hr
    (fun t => pairRes r (fun τ => workTraj M w₀ τ t) T)
    (fun t => pairRes_admissible (unitSteps_workTraj M w₀ t) hr T) lab s).1
  have hs : s.card ≤ Mb + 1 := card_image_lab_le lab N
  have hexp : 2 ^ ((n - Mb) * (n - 2 * m) * b) ≤
      2 ^ ((Mb + 1) * D) * ((M.q + 1) ^ Mb *
        (M.g + 1) ^ (∑ ℓ ∈ s, (entryCells (workTraj M w₀) (labelPart r lab T ℓ)).card)) :=
    calc 2 ^ ((n - Mb) * (n - 2 * m) * b)
        ≤ 2 ^ (∑ ℓ ∈ s, (cutSet M w₀ n b (labelPart r lab T ℓ)).card) :=
          Nat.pow_le_pow_right (by norm_num) (hlow.trans hcut)
      _ ≤ _ := hfam
      _ ≤ _ := Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ hs))
          (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) he1))
  have hlin := exp_bound_to_linear hexp
  simpa [Nat.mul_comm] using hlin

/-- **Oblivious transposers satisfy the cell-accurate cut inequality** with zero slack and boundary
cost `⌈log₂ (q+1)⌉`, at its running time `T`. -/
theorem cellCutIneq_of_oblivious {M : TM} {n T r : ℕ}
    (hobl : ObliviousOn M (matrixInputs n (entryBits n)) T)
    (hcorr : Transposes M n (entryBits n)) {w₀ : List Bool}
    (hw₀ : w₀ ∈ matrixInputs n (entryBits n)) (hr : 1 ≤ r) (hrnb : r ≤ n * entryBits n) :
    CellCutIneq n (Nat.clog 2 (M.g + 1)) r T 0 (Nat.clog 2 (M.q + 1))
      (fun t τ => workTraj M w₀ τ t) :=
  cellCutIneq_of_oblivious_on hobl
    (fun w hw => correct_of_transposes hcorr hw (hobl.1 w hw)) hw₀
    (by rw [ncard_matrixInputs, pow_zero, one_mul]) hr hrnb

end PaddingMemo
