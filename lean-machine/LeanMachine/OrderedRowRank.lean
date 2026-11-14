import LeanMachine.LastRowSupport
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-!
# Rank counted along a prescribed row order

The order is supplied, not constructed. Prefix spans identify the rows that
increase rank; new columns are charged to those rows. The final selected
row uses `LastRowSupport` to improve its charge to one.
-/

namespace LeanMachine.OrderedRowRank

open Finset Module
open scoped BigOperators
set_option autoImplicit false

variable {F : Type*} [Field F] {n : ℕ}

/-- Actual row vectors with index strictly below the prefix length. -/
def prefixRows (B : Matrix (Fin n) (Fin n) F) (k : ℕ) : Set (Fin n → F) :=
  B '' {i | i.val < k}

/-- Span of the rows already processed. -/
def prefixSpan (B : Matrix (Fin n) (Fin n) F) (k : ℕ) : Submodule F (Fin n → F) :=
  Submodule.span F (prefixRows B k)

/-- The rows that increase the span when processed in index order. -/
noncomputable def selectedRows (B : Matrix (Fin n) (Fin n) F) : Finset (Fin n) := by
  classical
  exact univ.filter fun i => B i ∉ prefixSpan B i.val

/-- Selected rows in an initial segment. -/
noncomputable def selectedPrefix (B : Matrix (Fin n) (Fin n) F) (k : ℕ) :
    Finset (Fin n) :=
  (selectedRows B).filter fun i => i.val < k

/-- Columns first appearing in the current row. -/
noncomputable def newColumns (B : Matrix (Fin n) (Fin n) F) (i : Fin n) :
    Finset (Fin n) := by
  classical
  exact univ.filter fun j => B i j ≠ 0 ∧ ∀ p : Fin n, p.val < i.val → B p j = 0

@[simp] theorem mem_selectedRows (B : Matrix (Fin n) (Fin n) F) (i : Fin n) :
    i ∈ selectedRows B ↔ B i ∉ prefixSpan B i.val := by
  classical
  simp [selectedRows]

@[simp] theorem mem_selectedPrefix (B : Matrix (Fin n) (Fin n) F) (k : ℕ) (i : Fin n) :
    i ∈ selectedPrefix B k ↔ i ∈ selectedRows B ∧ i.val < k := by
  simp [selectedPrefix]

@[simp] theorem mem_newColumns (B : Matrix (Fin n) (Fin n) F) (i j : Fin n) :
    j ∈ newColumns B i ↔ B i j ≠ 0 ∧ ∀ p : Fin n, p.val < i.val → B p j = 0 := by
  classical
  simp [newColumns]

omit [Field F] in
@[simp] theorem prefixRows_zero (B : Matrix (Fin n) (Fin n) F) :
    prefixRows B 0 = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro x ⟨i, hi, rfl⟩
  exact Nat.not_lt_zero i.val hi

@[simp] theorem prefixSpan_zero (B : Matrix (Fin n) (Fin n) F) :
    prefixSpan B 0 = ⊥ := by simp [prefixSpan]

omit [Field F] in
theorem prefixRows_succ (B : Matrix (Fin n) (Fin n) F) (k : ℕ) (hk : k < n) :
    prefixRows B (k + 1) = insert (B ⟨k, hk⟩) (prefixRows B k) := by
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    change i.val < k + 1 at hi
    by_cases hik : i.val < k
    · exact Set.mem_insert_of_mem _ ⟨i, hik, rfl⟩
    · have hi' : i = ⟨k, hk⟩ := Fin.ext (show i.val = k by omega)
      simp [hi']
  · rintro (rfl | ⟨i, hi, rfl⟩)
    · exact ⟨⟨k, hk⟩, Nat.lt_succ_self k, rfl⟩
    · exact ⟨i, Nat.lt_succ_of_lt hi, rfl⟩

theorem prefixSpan_succ (B : Matrix (Fin n) (Fin n) F) (k : ℕ) (hk : k < n) :
    prefixSpan B (k + 1) = prefixSpan B k ⊔ Submodule.span F {B ⟨k, hk⟩} := by
  rw [prefixSpan, prefixRows_succ B k hk, Submodule.span_insert, sup_comm]
  rfl

theorem prefixSpan_mono (B : Matrix (Fin n) (Fin n) F) : Monotone (prefixSpan B) := by
  intro k l hkl
  apply Submodule.span_mono
  exact Set.image_mono (fun i hi => lt_of_lt_of_le hi hkl)

omit [Field F] in
theorem prefixRows_all (B : Matrix (Fin n) (Fin n) F) :
    prefixRows B n = Set.range B := by
  ext x
  constructor
  · rintro ⟨i, _, rfl⟩; exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩; exact ⟨i, i.isLt, rfl⟩

@[simp] theorem selectedPrefix_zero (B : Matrix (Fin n) (Fin n) F) :
    selectedPrefix B 0 = ∅ := by simp [selectedPrefix]

@[simp] theorem selectedPrefix_all (B : Matrix (Fin n) (Fin n) F) :
    selectedPrefix B n = selectedRows B := by
  ext i
  simp [i.isLt]

theorem selectedPrefix_succ (B : Matrix (Fin n) (Fin n) F) (k : ℕ) (hk : k < n) :
    selectedPrefix B (k + 1) =
      if (⟨k, hk⟩ : Fin n) ∈ selectedRows B then
        insert ⟨k, hk⟩ (selectedPrefix B k) else selectedPrefix B k := by
  classical
  split_ifs with hs
  · ext i
    simp only [mem_insert, mem_selectedPrefix]
    have hi : i = ⟨k, hk⟩ ↔ i.val = k := Fin.ext_iff
    constructor
    · rintro ⟨hsi, hik⟩
      by_cases he : i.val = k
      · exact Or.inl (hi.mpr he)
      · exact Or.inr ⟨hsi, by omega⟩
    · rintro (rfl | ⟨hsi, hik⟩)
      · exact ⟨hs, by simp⟩
      · exact ⟨hsi, by omega⟩
  · ext i
    simp only [mem_selectedPrefix]
    constructor
    · rintro ⟨hsi, hik⟩
      have he : i.val ≠ k := fun he => hs ((show i = ⟨k, hk⟩ from Fin.ext he) ▸ hsi)
      exact ⟨hsi, by omega⟩
    · rintro ⟨hsi, hik⟩; exact ⟨hsi, by omega⟩

theorem selectedPrefix_card (B : Matrix (Fin n) (Fin n) F) :
    ∀ k, k ≤ n → (selectedPrefix B k).card = finrank F (prefixSpan B k) := by
  classical
  intro k
  induction k with
  | zero => intro _; rw [selectedPrefix_zero, card_empty, prefixSpan_zero, finrank_bot]
  | succ k ih =>
    intro hk
    have hkn : k < n := by omega
    rw [selectedPrefix_succ B k hkn]
    by_cases hs : (⟨k, hkn⟩ : Fin n) ∈ selectedRows B
    · rw [ite_eq_left hs, card_insert_of_notMem (by simp), ih (by omega)]
      rw [prefixSpan_succ B k hkn,
        Submodule.finrank_sup_span_singleton (mem_selectedRows B _ |>.mp hs)]
    · rw [ite_eq_right hs, ih (by omega)]
      have hm : B ⟨k, hkn⟩ ∈ prefixSpan B k := by simpa using hs
      have he : prefixSpan B (k + 1) = prefixSpan B k := by
        rw [prefixSpan, prefixRows_succ B k hkn, Submodule.span_insert_eq_span hm]
        rfl
      rw [he]

theorem selectedRows_card (B : Matrix (Fin n) (Fin n) F) :
    (selectedRows B).card = B.rank := by
  rw [← selectedPrefix_all B, selectedPrefix_card B n le_rfl,
    prefixSpan, prefixRows_all, Matrix.rank_eq_finrank_span_row]
  rfl

/-- Every vector in a prefix span vanishes on a column absent from that prefix. -/
theorem apply_eq_zero_of_mem_prefixSpan (B : Matrix (Fin n) (Fin n) F) (k : ℕ)
    (j : Fin n) (hz : ∀ p : Fin n, p.val < k → B p j = 0)
    {x : Fin n → F} (hx : x ∈ prefixSpan B k) : x j = 0 := by
  change x ∈ Submodule.span F (prefixRows B k) at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨p, hp, rfl⟩ := hy
      exact hz p hp
  | zero => rfl
  | add x y hx hy ihx ihy => change x j + y j = 0; rw [ihx, ihy, add_zero]
  | smul a x hx ih => change a * x j = 0; rw [ih, mul_zero]

theorem newColumns_eq_empty_of_not_selected (B : Matrix (Fin n) (Fin n) F)
    (i : Fin n) (hi : i ∉ selectedRows B) : newColumns B i = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro j hj
  obtain ⟨hij, hzero⟩ := (mem_newColumns B i j).mp hj
  exact hij (apply_eq_zero_of_mem_prefixSpan B i.val j hzero (by simpa using hi))

theorem newColumns_disjoint (B : Matrix (Fin n) (Fin n) F)
    {i k : Fin n} (hik : i ≠ k) : Disjoint (newColumns B i) (newColumns B k) := by
  apply disjoint_left.mpr
  intro j hji hjk
  obtain ⟨hij, hzi⟩ := (mem_newColumns B i j).mp hji
  obtain ⟨hkj, hzk⟩ := (mem_newColumns B k j).mp hjk
  rcases lt_or_gt_of_ne hik with hik | hki
  · exact hij (hzk i hik)
  · exact hkj (hzi k hki)

theorem newColumns_cover (B : Matrix (Fin n) (Fin n) F) (hdiag : ∀ i, B i i ≠ 0) :
    univ.biUnion (newColumns B) = (univ : Finset (Fin n)) := by
  classical
  apply eq_univ_of_forall
  intro j
  let S := univ.filter fun i : Fin n => B i j ≠ 0
  have hs : S.Nonempty := ⟨j, by simp [S, hdiag j]⟩
  let i := S.min' hs
  have hiS : i ∈ S := S.min'_mem hs
  refine mem_biUnion.mpr ⟨i, mem_univ _, (mem_newColumns B i j).mpr ⟨?_, ?_⟩⟩
  · exact (mem_filter.mp hiS).2
  · intro p hp
    by_contra hpj
    have hpi : i ≤ p := S.min'_le p (by simp [S, hpj])
    exact (not_lt_of_ge hpi) hp

/-- Every coordinate is charged exactly once, to a row that increases rank. -/
theorem sum_selected_newColumns (B : Matrix (Fin n) (Fin n) F)
    (hdiag : ∀ i, B i i ≠ 0) :
    (∑ i ∈ selectedRows B, (newColumns B i).card) = n := by
  classical
  have hsum : (∑ i : Fin n, (newColumns B i).card) = n := by
    rw [← card_biUnion (fun i _ k _ hik => newColumns_disjoint B hik),
      newColumns_cover B hdiag, card_univ, Fintype.card_fin]
  calc
    _ = ∑ i : Fin n, (newColumns B i).card := by
      apply sum_subset (subset_univ _)
      intro i _ hi
      rw [newColumns_eq_empty_of_not_selected B i hi, card_empty]
    _ = n := hsum

/-- Once the last selected row has been processed, the span is already full. -/
theorem prefixSpan_eq_full_of_selected_le (B : Matrix (Fin n) (Fin n) F)
    (v : Fin n) (hv : ∀ i ∈ selectedRows B, i ≤ v) :
    prefixSpan B (v.val + 1) = prefixSpan B n := by
  apply Submodule.eq_of_le_of_finrank_eq
    (prefixSpan_mono B (by omega))
  have he : selectedPrefix B (v.val + 1) = selectedRows B := by
    ext i
    simp only [mem_selectedPrefix]
    exact ⟨And.left, fun hi => ⟨hi, Nat.lt_succ_of_le (hv i hi)⟩⟩
  rw [← selectedPrefix_card B (v.val + 1) (by omega),
    ← selectedPrefix_card B n le_rfl, he, selectedPrefix_all]

/-- The supplied order makes the last selected row's new-column charge at most one. -/
theorem last_newColumns_card_le_one (B : Matrix (Fin n) (Fin n) F)
    (hdiag : ∀ i, B i i ≠ 0) (hpattern : LastRowSupport.NoFourArcPattern B)
    (v : Fin n) (hlast : ∀ i ∈ selectedRows B, i ≤ v)
    (hown : ∃ p : Fin n, p.val < v.val ∧ B p v ≠ 0) :
    (newColumns B v).card ≤ 1 := by
  apply LastRowSupport.card_le_one_of_rows_mem_span_insert
    B (prefixRows B v.val) v (newColumns B v) hpattern
  · intro j _
    have hm : B j ∈ prefixSpan B n :=
      Submodule.subset_span (by rw [prefixRows_all]; exact ⟨j, rfl⟩)
    rw [← prefixSpan_eq_full_of_selected_le B v hlast,
      prefixSpan, prefixRows_succ B v.val v.isLt] at hm
    exact hm
  · rintro y ⟨p, hp, rfl⟩ j hj
    exact ((mem_newColumns B v j).mp hj).2 p hp
  · exact fun j _ => hdiag j
  · intro hv
    obtain ⟨p, hp, hpv⟩ := hown
    exact hpv (((mem_newColumns B v v).mp hv).2 p hp)

/-- The row-order certificate. Only an already supplied order is used;
no graph traversal or closed-cut induction is hidden in the hypotheses. -/
theorem rank_count_of_order (B : Matrix (Fin n) (Fin n) F) (a h : ℕ)
    (hdiag : ∀ i, B i i ≠ 0) (hpattern : LastRowSupport.NoFourArcPattern B)
    (hr : 2 ≤ B.rank)
    (hfirst : ∀ i : Fin n, i.val = 0 → (newColumns B i).card ≤ a)
    (hstep : ∀ i : Fin n, 0 < i.val → (newColumns B i).card ≤ h)
    (hown : ∀ i : Fin n, 0 < i.val → ∃ p : Fin n, p.val < i.val ∧ B p i ≠ 0) :
    n ≤ a + h * (B.rank - 2) + 1 := by
  classical
  have hcard : 2 ≤ (selectedRows B).card := by rw [selectedRows_card]; exact hr
  have hs : (selectedRows B).Nonempty := card_pos.mp (by omega)
  let v := (selectedRows B).max' hs
  have hv : v ∈ selectedRows B := (selectedRows B).max'_mem hs
  have hmax : ∀ i ∈ selectedRows B, i ≤ v :=
    fun i hi => (selectedRows B).le_max' i hi
  have hn : 0 < n := by have := v.isLt; omega
  let first : Fin n := ⟨0, hn⟩
  have hf : first ∈ selectedRows B := by
    rw [mem_selectedRows]
    change B first ∉ prefixSpan B 0
    rw [prefixSpan_zero]
    intro hz
    have he : B first = 0 := by simpa using hz
    exact hdiag first (congrFun he first)
  have hfv : first ≠ v := by
    intro he
    have hsub : selectedRows B ⊆ {first} := by
      intro i hi
      have hle := hmax i hi
      rw [← he] at hle
      have hie : i = first := Fin.ext (by change i.val = 0; change i.val ≤ 0 at hle; omega)
      simp [hie]
    have hc := card_le_card hsub
    simp only [card_singleton] at hc
    omega
  have hvpos : 0 < v.val := by
    by_contra hh
    have he : first = v := Fin.ext (by change 0 = v.val; omega)
    exact hfv he
  have hlast := last_newColumns_card_le_one B hdiag hpattern v hmax (hown v hvpos)
  have hve : v ∈ (selectedRows B).erase first := mem_erase.mpr ⟨Ne.symm hfv, hv⟩
  let R := ((selectedRows B).erase first).erase v
  have hR : R.card = B.rank - 2 := by
    dsimp [R]
    rw [card_erase_of_mem hve, card_erase_of_mem hf, selectedRows_card]
    omega
  have hmid : (∑ i ∈ R, (newColumns B i).card) ≤ R.card * h := by
    calc
      _ ≤ ∑ _i ∈ R, h := by
        apply sum_le_sum
        intro i hi
        have hif : i ≠ first := (mem_erase.mp (mem_erase.mp hi).2).1
        apply hstep i
        by_contra hnz
        exact hif (Fin.ext (by change i.val = 0; omega))
      _ = R.card * h := by simp
  have hsum : (newColumns B first).card + (newColumns B v).card +
      (∑ i ∈ R, (newColumns B i).card) = n := by
    rw [add_assoc, show (newColumns B v).card +
      (∑ i ∈ R, (newColumns B i).card) =
      ∑ i ∈ (selectedRows B).erase first, (newColumns B i).card from
        add_sum_erase _ (fun i : Fin n => (newColumns B i).card) hve,
      add_sum_erase _ (fun i : Fin n => (newColumns B i).card) hf,
      sum_selected_newColumns B hdiag]
  have ha := hfirst first rfl
  rw [hR] at hmid
  nlinarith

end LeanMachine.OrderedRowRank

#print axioms LeanMachine.OrderedRowRank.selectedRows_card
#print axioms LeanMachine.OrderedRowRank.sum_selected_newColumns
#print axioms LeanMachine.OrderedRowRank.last_newColumns_card_le_one
#print axioms LeanMachine.OrderedRowRank.rank_count_of_order
