import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-! Joint sparse records: supports and their values are counted together.
The zero value is represented uniquely, so only nonzero alphabets are paid. -/

namespace LeanMachine

open Classical
open scoped BigOperators

abbrev SizedImports (n A j : ℕ) :=
  {s : Finset (Fin n) // s.card = j} × (Fin j → Fin A)

abbrev SparseImports (n A J : ℕ) := Σ j : Fin (J + 1), SizedImports n A j.val

theorem sizedImports_card (n A j : ℕ) :
    Fintype.card (SizedImports n A j) = n.choose j * A ^ j := by
  simp [SizedImports, Fintype.card_finset_len]

theorem sparseImports_card (n A J : ℕ) :
    Fintype.card (SparseImports n A J) =
      ∑ j ∈ Finset.range (J + 1), n.choose j * A ^ j := by
  simp only [SparseImports, Fintype.card_sigma, sizedImports_card]
  exact Fin.sum_univ_eq_sum_range (fun j : ℕ => n.choose j * A ^ j) (J + 1)

abbrev SizedSupportRecord (I A : Type*) (j : ℕ) :=
  Σ s : {s : Finset I // s.card = j}, (s.1 → A)

abbrev SparseSupportRecord (I A : Type*) (s : ℕ) :=
  Σ j : Fin (s + 1), SizedSupportRecord I A j.val

theorem sizedSupportRecord_card (I A : Type*) [Fintype I] [Fintype A] (j : ℕ) :
    Fintype.card (SizedSupportRecord I A j) =
      (Fintype.card I).choose j * Fintype.card A ^ j := by
  classical
  simp only [SizedSupportRecord, Fintype.card_sigma, Fintype.card_fun, Fintype.card_coe]
  simp_rw [show ∀ s : {s : Finset I // s.card = j}, s.1.card = j from fun s => s.2]
  simp [Fintype.card_finset_len]

theorem sparseSupportRecord_card (I A : Type*) [Fintype I] [Fintype A] (s : ℕ) :
    Fintype.card (SparseSupportRecord I A s) =
      ∑ j ∈ Finset.range (s + 1), (Fintype.card I).choose j * Fintype.card A ^ j := by
  rw [show Fintype.card (SparseSupportRecord I A s) =
    ∑ j : Fin (s + 1), Fintype.card (SizedSupportRecord I A j.val) from Fintype.card_sigma]
  simp_rw [sizedSupportRecord_card]
  exact Fin.sum_univ_eq_sum_range
    (fun j : ℕ => (Fintype.card I).choose j * Fintype.card A ^ j) (s + 1)

noncomputable def recordSupport {I : Type*} [Fintype I] {A : I → Type*}
    (zero : ∀ i, A i) (x : ∀ i, A i) : Finset I := by
  classical
  exact Finset.univ.filter (fun i => x i ≠ zero i)

@[simp] theorem mem_recordSupport {I : Type*} [Fintype I] {A : I → Type*}
    (zero : ∀ i, A i) (x : ∀ i, A i) (i : I) :
    i ∈ recordSupport zero x ↔ x i ≠ zero i := by
  classical
  simp [recordSupport]

/-- The actual support and the encoded nonzero values. Different positions may
have different alphabets, and may choose their support adaptively. -/
noncomputable def encodeSparseRecord {I B : Type*} [Fintype I] {A : I → Type*}
    (zero : ∀ i, A i) (encode : ∀ i, {a : A i // a ≠ zero i} → B) (s : ℕ)
    (x : {x : ∀ i, A i // (recordSupport zero x).card ≤ s}) : SparseSupportRecord I B s :=
  ⟨⟨(recordSupport zero x.1).card, Nat.lt_succ_of_le x.2⟩,
    ⟨⟨recordSupport zero x.1, rfl⟩,
      fun i => encode i.1 ⟨x.1 i.1, (mem_recordSupport zero x.1 i.1).mp i.2⟩⟩⟩

theorem encodeSparseRecord_injective {I B : Type*} [Fintype I] {A : I → Type*}
    (zero : ∀ i, A i) (encode : ∀ i, {a : A i // a ≠ zero i} → B)
    (hinj : ∀ i, Function.Injective (encode i)) (s : ℕ) :
    Function.Injective (encodeSparseRecord zero encode s) := by
  classical
  intro x y he
  have hs : recordSupport zero x.1 = recordSupport zero y.1 :=
    congrArg (fun r : SparseSupportRecord I B s => r.2.1.1) he
  apply Subtype.ext
  funext i
  by_cases hi : i ∈ recordSupport zero x.1
  · have hiy : i ∈ recordSupport zero y.1 := hs ▸ hi
    let observe (r : SparseSupportRecord I B s) : Option B :=
      if h : i ∈ r.2.1.1 then some (r.2.2 ⟨i, h⟩) else none
    have hv := congrArg observe he
    simp only [observe, encodeSparseRecord, hi, hiy, dite_true, Option.some.injEq] at hv
    exact congrArg Subtype.val (hinj i hv)
  · have hiy : i ∉ recordSupport zero y.1 := hs ▸ hi
    have hx : x.1 i = zero i := not_not.mp ((mem_recordSupport zero x.1 i).not.mp hi)
    have hy : y.1 i = zero i := not_not.mp ((mem_recordSupport zero y.1 i).not.mp hiy)
    exact hx.trans hy.symm

/-- Exact support menus bound sparse dependent tuples using only a uniform
bound on each nonzero alphabet, without independence assumptions. -/
theorem sparse_record_card_le {I : Type*} [Fintype I] {A : I → Type*}
    [∀ i, Fintype (A i)] (zero : ∀ i, A i) (B s : ℕ)
    (hcard : ∀ i, Fintype.card {a : A i // a ≠ zero i} ≤ B) :
    Nat.card {x : ∀ i, A i // (recordSupport zero x).card ≤ s} ≤
      ∑ j ∈ Finset.range (s + 1), (Fintype.card I).choose j * B ^ j := by
  classical
  let encode (i : I) : {a : A i // a ≠ zero i} → Fin B :=
    fun a => Fin.castLE (hcard i) (Fintype.equivFin _ a)
  have hinj (i : I) : Function.Injective (encode i) :=
    (Fin.castLE_injective (hcard i)).comp (Fintype.equivFin _).injective
  have hc := Nat.card_le_card_of_injective
    (encodeSparseRecord zero encode s) (encodeSparseRecord_injective zero encode hinj s)
  simpa only [Nat.card_eq_fintype_card, sparseSupportRecord_card, Fintype.card_fin] using hc

theorem recordSupport_sub_subset {I : Type*} [Fintype I] {A : I → Type*}
    [∀ i, AddGroup (A i)] (x y : ∀ i, A i) :
    recordSupport (fun _ => 0) (x - y) ⊆
      recordSupport (fun _ => 0) x ∪ recordSupport (fun _ => 0) y := by
  intro i hi
  simp only [mem_recordSupport, Pi.sub_apply, Finset.mem_union] at hi ⊢
  by_contra h
  obtain ⟨hx, hy⟩ := not_or.mp h
  exact hi (by rw [not_not.mp hx, not_not.mp hy, sub_self])

theorem recordSupport_sub_card_le {I : Type*} [Fintype I] {A : I → Type*}
    [∀ i, AddGroup (A i)] (x y : ∀ i, A i) :
    (recordSupport (fun _ => 0) (x - y)).card ≤
      (recordSupport (fun _ => 0) x).card + (recordSupport (fun _ => 0) y).card :=
  (Finset.card_le_card (recordSupport_sub_subset x y)).trans (Finset.card_union_le _ _)

end LeanMachine
