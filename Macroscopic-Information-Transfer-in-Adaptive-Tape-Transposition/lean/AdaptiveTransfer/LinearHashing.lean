import LeanMachine.FiniteLinearHash
import LeanMachine.SparseRecords
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! Actual binary linear hashes for sparse tape words and finite, input-indexed
comparison catalogues. These are finite selection kernels, not a native carrier
compiler or a claim that a dense tape can be recovered from its syndrome. -/

namespace AdaptiveTransfer

open Module Classical LeanMachine
open scoped BigOperators

abbrev BinaryWord (N : ℕ) := Fin N → ZMod 2
abbrev BlockWord (n a : ℕ) := Fin n → BinaryWord a

theorem binary_matrix_collision_card (N r : ℕ) (v : BinaryWord N) (hv : v ≠ 0) :
    Nat.card {M : Matrix (Fin r) (Fin N) (ZMod 2) // M.mulVec v = 0} =
      2 ^ (N * r - r) := by
  let E : {M : Matrix (Fin r) (Fin N) (ZMod 2) // M.mulVec v = 0} ≃
      {H : BinaryWord N →ₗ[ZMod 2] BinaryWord r // H v = 0} :=
    Matrix.toLin'.toEquiv.subtypeEquiv (fun _ => Iff.rfl)
  rw [Nat.card_congr E]
  simpa only [Nat.card_eq_fintype_card, ZMod.card, Module.finrank_fintype_fun_eq_card,
    Fintype.card_fin] using
    linearHash_collision_card (F := ZMod 2) (W := BinaryWord r) v hv

def blockSparseMenu (n a s : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (min n s + 1), n.choose j * (2 ^ a - 1) ^ j

noncomputable def sparseNonzeroWords (n a s : ℕ) : Finset (BlockWord n a) :=
  Finset.univ.filter (fun w => w ≠ 0 ∧ (recordSupport (fun _ => 0) w).card ≤ s)

theorem sparseNonzeroWords_card (n a s : ℕ) :
    (sparseNonzeroWords n a s).card + 1 ≤ blockSparseMenu n a s := by
  let all : Finset (BlockWord n a) :=
    Finset.univ.filter (fun w => (recordSupport (fun _ => 0) w).card ≤ s)
  have he : insert 0 (sparseNonzeroWords n a s) = all := by
    ext w
    simp only [sparseNonzeroWords, all, Finset.mem_insert, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro (rfl | ⟨_, hs⟩)
      · simp [recordSupport]
      · exact hs
    · intro hs
      by_cases h : w = 0
      · exact Or.inl h
      · exact Or.inr ⟨h, hs⟩
  have hzero : (0 : BlockWord n a) ∉ sparseNonzeroWords n a s := by
    simp [sparseNonzeroWords]
  have hc := sparse_record_card_le (I := Fin n) (A := fun _ => BinaryWord a)
    (fun _ => 0) (2 ^ a - 1) (min n s)
    (fun _ => by simp [Fintype.card_subtype_compl, BinaryWord, ZMod.card])
  have hset : {w : BlockWord n a | (recordSupport (fun _ => 0) w).card ≤ min n s} =
      {w | w ∈ all} := by
    ext w
    simp only [all, Finset.mem_filter, Finset.mem_univ, true_and, le_min_iff]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      simpa only [Fintype.card_fin] using
        (Finset.card_le_univ (recordSupport (fun _ => 0) w))
  change Nat.card ({w : BlockWord n a | (recordSupport (fun _ => 0) w).card ≤ min n s} : Set (BlockWord n a)) ≤ _ at hc
  rw [hset] at hc
  have hc' : all.card ≤ blockSparseMenu n a s := by
    simpa [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.filter_mem_eq_inter,
      blockSparseMenu] using hc
  rwa [← he, Finset.card_insert_of_notMem hzero] at hc'

/-- One fixed syndrome separates every word of block weight at most `m+1`.
The bit length is the exact ceiling used by the carrier construction. -/
theorem exists_sparse_injective_hash (n a m : ℕ) :
    ∃ H : BlockWord n a →ₗ[ZMod 2] BinaryWord (Nat.clog 2 (blockSparseMenu n a (2 * m + 2))),
      Set.InjOn H {w | (recordSupport (fun _ => 0) w).card ≤ m + 1} := by
  let r := Nat.clog 2 (blockSparseMenu n a (2 * m + 2))
  obtain ⟨H, hH⟩ := exists_linearHash_avoiding (F := ZMod 2) (W := BinaryWord r)
    (sparseNonzeroWords n a (2 * m + 2))
    (fun v hv => (Finset.mem_filter.mp hv).2.1)
    (by
      have hc := sparseNonzeroWords_card n a (2 * m + 2)
      have hp := Nat.le_pow_clog (by decide : 1 < 2) (blockSparseMenu n a (2 * m + 2))
      simp only [BinaryWord, Fintype.card_fun, ZMod.card, Fintype.card_fin]
      exact lt_of_lt_of_le (by omega) hp)
  refine ⟨H, ?_⟩
  intro x hx y hy hxy
  by_contra hne
  have hs := recordSupport_sub_card_le x y
  have hmem : x - y ∈ sparseNonzeroWords n a (2 * m + 2) := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, sub_ne_zero.mpr hne, by dsimp at hx hy; omega⟩
  exact hH _ hmem (by rw [map_sub, hxy, sub_self])

/-- A single binary hash is simultaneously collision-free for at least half
the given inputs; the per-input comparison sets are chosen before the hash. -/
theorem exists_binary_common_half_of_bits {X : Type*} (N r : ℕ)
    (G : Finset X) (D : X → Finset (BinaryWord N)) (B : ℕ)
    (hnonzero : ∀ x ∈ G, ∀ v ∈ D x, v ≠ 0)
    (hsize : ∀ x ∈ G, (D x).card ≤ B) (hb : 2 * B ≤ 2 ^ r) :
    ∃ (H : BinaryWord N →ₗ[ZMod 2] BinaryWord r) (G' : Finset X),
      G' ⊆ G ∧ G.card ≤ 2 * G'.card ∧ ∀ x ∈ G', ∀ v ∈ D x, H v ≠ 0 := by
  have hb' : 2 * B ≤ Fintype.card (BinaryWord r) := by
    simpa only [BinaryWord, Fintype.card_fun, Fintype.card_fin, ZMod.card] using hb
  exact exists_linearHash_common_subset (F := ZMod 2)
    (V := BinaryWord N) (W := BinaryWord r) G D B hnonzero hsize hb'

theorem exists_binary_common_half {X : Type*} (N : ℕ)
    (G : Finset X) (D : X → Finset (BinaryWord N)) (B : ℕ)
    (hnonzero : ∀ x ∈ G, ∀ v ∈ D x, v ≠ 0)
    (hsize : ∀ x ∈ G, (D x).card ≤ B) :
    ∃ (H : BinaryWord N →ₗ[ZMod 2] BinaryWord (Nat.clog 2 (2 * B))) (G' : Finset X),
      G' ⊆ G ∧ G.card ≤ 2 * G'.card ∧ ∀ x ∈ G', ∀ v ∈ D x, H v ≠ 0 :=
  exists_binary_common_half_of_bits N (Nat.clog 2 (2 * B)) G D B hnonzero hsize
    (Nat.le_pow_clog (by decide : 1 < 2) (2 * B))

theorem binary_hash_bits_eq_ceiling (B : ℕ) :
    Nat.clog 2 B = ⌈Real.logb 2 B⌉₊ := (Real.natCeil_logb_natCast 2 B).symm

end AdaptiveTransfer
