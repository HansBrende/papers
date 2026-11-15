import MatrixCoding.BlockCodeLocal

/-! # Paid grouping of block outputs into complete output rows -/

namespace LeanBacklog.BlockTCC

open Finset Transpose Transpose.Tape Transpose.Tape.Impl
open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Classical in
noncomputable def slotRows {k : ℕ} (Dg : TSDiagram k) (d b r y : ℕ) : Finset (Fin d) :=
  univ.filter fun j => ∃ o : Fin (d * d * b), o.val / (d * b) = j.val ∧ Dg.outNode r o.val = y

open Classical in
noncomputable def rowSlots {k : ℕ} (Dg : TSDiagram k) (d b r : ℕ) (j : Fin d) : Finset ℕ :=
  (range (Dg.nodes r)).filter fun y => j ∈ slotRows Dg d b r y

theorem card_slotRows {k d b r : ℕ} {Dg : TSDiagram k}
    (hDg : Dg.Valid (d * d * b)) (hr : 1 ≤ r) (hwidth : r ≤ d * b)
    (hW : 0 < d * b) (y : ℕ) : (slotRows Dg d b r y).card ≤ 2 := by
  classical
  let q := Dg.out (y * r) / (d * b)
  calc
    _ ≤ ({q, q + 1} : Finset ℕ).card := by
      apply card_le_card_of_injOn (fun j : Fin d => j.val)
      · intro j hj
        obtain ⟨o, ho, hs⟩ := (mem_filter.mp hj).2
        have hspec := outNode_spec hDg hr o.isLt
        rw [hs] at hspec
        have h1 : q ≤ j.val := by rw [← ho]; exact Nat.div_le_div_right hspec.1
        have h2 : j.val ≤ q + 1 := by
          rw [← ho]
          calc
            _ ≤ (Dg.out (y * r) + d * b) / (d * b) := Nat.div_le_div_right (by omega)
            _ = q + 1 := Nat.add_div_right _ hW
        change j.val ∈ ({q, q + 1} : Finset ℕ)
        simp only [mem_insert, mem_singleton]
        omega
      · intro j _ j' _ he
        exact Fin.ext he
    _ ≤ 2 := card_le_two

theorem sum_card_rowSlots {k d b r : ℕ} {Dg : TSDiagram k}
    (hDg : Dg.Valid (d * d * b)) (hr : 1 ≤ r) (hwidth : r ≤ d * b)
    (hW : 0 < d * b) : ∑ j : Fin d, (rowSlots Dg d b r j).card ≤ 2 * Dg.nodes r := by
  classical
  calc
    _ = ∑ y ∈ range (Dg.nodes r), (slotRows Dg d b r y).card := by
      simp only [rowSlots, card_filter]
      rw [sum_comm]
      simp only [← card_filter]
      apply sum_congr rfl
      intro y _
      congr 1
      ext j
      simp
    _ ≤ ∑ _y ∈ range (Dg.nodes r), 2 :=
      sum_le_sum fun y _ => card_slotRows hDg hr hwidth hW y
    _ = 2 * Dg.nodes r := by simp [mul_comm]

open Classical in
noncomputable def badOutputRows {k : ℕ} (Dg : TSDiagram k) (d b r M : ℕ) : Finset (Fin d) :=
  univ.filter fun j => M < (rowSlots Dg d b r j).card

theorem badOutputRows_bill {k d b r : ℕ} {Dg : TSDiagram k}
    (hDg : Dg.Valid (d * d * b)) (hr : 1 ≤ r) (hwidth : r ≤ d * b)
    (hW : 0 < d * b) (M : ℕ) :
    M * (badOutputRows Dg d b r M).card ≤ 2 * Dg.nodes r := by
  classical
  calc
    _ = ∑ _j ∈ badOutputRows Dg d b r M, M := by simp [mul_comm]
    _ ≤ ∑ j ∈ badOutputRows Dg d b r M, (rowSlots Dg d b r j).card := by
      apply sum_le_sum
      intro j hj
      exact Nat.le_of_lt (mem_filter.mp hj).2
    _ ≤ ∑ j : Fin d, (rowSlots Dg d b r j).card :=
      sum_le_sum_of_subset (subset_univ _)
    _ ≤ _ := sum_card_rowSlots hDg hr hwidth hW

theorem mem_rowSlots {k d b r : ℕ} {Dg : TSDiagram k}
    (hDg : Dg.Valid (d * d * b)) (hr : 1 ≤ r)
    (o : Fin (d * d * b)) (j : Fin d) (ho : o.val / (d * b) = j.val) :
    Dg.outNode r o.val ∈ rowSlots Dg d b r j := by
  classical
  apply mem_filter.mpr
  have hL : 1 ≤ d * d * b := by have := o.isLt; omega
  refine ⟨mem_range.mpr (outNode_lt hDg hr hL o.val), ?_⟩
  exact mem_filter.mpr ⟨mem_univ _, o, ho, rfl⟩

open Classical in
/-- All exceptional columns receive the empty helper set; their values
will be paid for by the exceptional-column fibre theorem. -/
noncomputable def blockHelpers {k : ℕ} (Dg : TSDiagram k) (d b r D M : ℕ)
    (j : Fin d) : Finset (Fin d) :=
  if j ∈ badOutputRows Dg d b r M then ∅ else
    univ.filter fun i => i.val ∈ (rowSlots Dg d b r j).biUnion (nodeRows Dg d b r D)

theorem card_blockHelpers {k d b r : ℕ} {Dg : TSDiagram k}
    (hDg : Dg.Valid (d * d * b)) (hr : 1 ≤ r) (hwidth : r ≤ d * b)
    (D M : ℕ) (j : Fin d) :
    (blockHelpers Dg d b r D M j).card ≤ M * (2 * (2 * k + 3) ^ D) := by
  classical
  unfold blockHelpers
  split_ifs with hj
  · simp
  · have hM : (rowSlots Dg d b r j).card ≤ M := by
      simpa only [badOutputRows, mem_filter, mem_univ, true_and, not_lt] using hj
    calc
      _ ≤ ((rowSlots Dg d b r j).biUnion (nodeRows Dg d b r D)).card := by
        apply card_le_card_of_injOn (fun i : Fin d => i.val)
        · intro i hi; exact (mem_filter.mp hi).2
        · intro i _ i' _ hi; exact Fin.ext hi
      _ ≤ ∑ y ∈ rowSlots Dg d b r j, (nodeRows Dg d b r D y).card := card_biUnion_le
      _ ≤ ∑ _y ∈ rowSlots Dg d b r j, 2 * (2 * k + 3) ^ D :=
        sum_le_sum fun y _ => card_nodeRows hDg hr hwidth D y
      _ = (rowSlots Dg d b r j).card * (2 * (2 * k + 3) ^ D) := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ hM

theorem mem_blockHelpers {k d b r D M : ℕ} {Dg : TSDiagram k}
    {j i : Fin d} (hj : j ∉ badOutputRows Dg d b r M) {v : ℕ}
    (hv : v ∈ rowSlots Dg d b r j) (hi : i.val ∈ nodeRows Dg d b r D v) :
    i ∈ blockHelpers Dg d b r D M j := by
  classical
  simp only [blockHelpers, ite_eq_right hj, mem_filter, mem_univ, true_and]
  exact mem_biUnion.mpr ⟨v, hv, hi⟩

#print axioms slotRows
#print axioms rowSlots
#print axioms card_slotRows
#print axioms sum_card_rowSlots
#print axioms badOutputRows
#print axioms badOutputRows_bill
#print axioms mem_rowSlots
#print axioms blockHelpers
#print axioms card_blockHelpers
#print axioms mem_blockHelpers

end LeanBacklog.BlockTCC
