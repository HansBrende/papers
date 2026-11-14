import LeanMachine.DisjointSumsRecords

/-! # Recovery forces parity-block compatibility

In a nonempty code invariant under the parity kernel, a kernel shift invisible
to a recovery view cannot change its target. Two cancelling coordinate shifts
therefore force the rest of a target's block into its view; a free coordinate
must itself belong to its view. These local claims need no finite block index.
-/

namespace LeanMachine.DisjointSums

open Finset

variable {ι κ A : Type*} [AddCommGroup A]
variable (D : DisjointSums ι κ) (C : Set (ι → A))
variable (hstable : ∀ x ∈ C, ∀ z : ι → A, D.encode z = 0 → x + z ∈ C)

include hstable in
private theorem kernel_shift_zero_of_recovery (hC : C.Nonempty) (S : Set ι) (i : ι)
    (hrecover : ∀ u ∈ C, ∀ v ∈ C, Set.EqOn u v S → u i = v i)
    (z : ι → A) (hz : D.encode z = 0) (hview : Set.EqOn z 0 S) : z i = 0 := by
  obtain ⟨x, hx⟩ := hC
  have heq : Set.EqOn (x + z) x S := by
    intro j hj
    change x j + z j = x j
    rw [hview hj]
    exact add_zero _
  have hi := hrecover (x + z) (hstable x hx z hz) x hx heq
  simpa only [Pi.add_apply, add_eq_left] using hi

include hstable in
/-- A nonincident recovered coordinate forces every other coordinate of its
parity block into the recovery view. No finiteness assumption is used. -/
theorem support_subset_insert_of_recovery [Nontrivial A] (hC : C.Nonempty)
    (S : Set ι) (i : ι)
    (hrecover : ∀ u ∈ C, ∀ v ∈ C, Set.EqOn u v S → u i = v i)
    (hiS : i ∉ S) (k : κ) (hik : i ∈ D.support k) :
    (↑(D.support k) : Set ι) ⊆ insert i S := by
  classical
  intro j hj
  by_contra hnot
  have hji : j ≠ i := fun h => hnot (Set.mem_insert_iff.mpr (Or.inl h))
  have hjS : j ∉ S := fun h => hnot (Set.mem_insert_iff.mpr (Or.inr h))
  obtain ⟨a, ha⟩ := exists_ne (0 : A)
  let z : ι → A := Pi.single i a - Pi.single j a
  have hmembership (l : κ) : i ∈ D.support l ↔ j ∈ D.support l := by
    by_cases hl : l = k
    · subst l
      exact ⟨fun _ => hj, fun _ => hik⟩
    · have hd := D.disjoint hl
      have hni : i ∉ D.support l := fun hil => disjoint_left.mp hd hil hik
      have hnj : j ∉ D.support l := fun hjl => disjoint_left.mp hd hjl hj
      simp only [hni, hnj]
  have hz : D.encode z = 0 := by
    ext l
    simp [encode_apply, z, sum_sub_distrib, hmembership l]
  have hview : Set.EqOn z 0 S := by
    intro v hv
    have hvi : v ≠ i := fun h => hiS (h ▸ hv)
    have hvj : v ≠ j := fun h => hjS (h ▸ hv)
    simp [z, Pi.single_eq_of_ne hvi, Pi.single_eq_of_ne hvj]
  have hzero := D.kernel_shift_zero_of_recovery C hstable hC S i hrecover z hz hview
  apply ha
  simpa [z, hji.symm] using hzero

include hstable in
/-- A coordinate outside every parity block has an independent kernel shift,
so any recovery view for it must contain the coordinate itself. -/
theorem mem_view_of_free [Nontrivial A] (hC : C.Nonempty) (S : Set ι) (i : ι)
    (hrecover : ∀ u ∈ C, ∀ v ∈ C, Set.EqOn u v S → u i = v i)
    (hfree : ∀ k, i ∉ D.support k) : i ∈ S := by
  classical
  by_contra hiS
  obtain ⟨a, ha⟩ := exists_ne (0 : A)
  let z : ι → A := Pi.single i a
  have hz : D.encode z = 0 := by
    ext k
    simp [encode_apply, z, hfree]
  have hview : Set.EqOn z 0 S := by
    intro j hj
    have hji : j ≠ i := fun h => hiS (h ▸ hj)
    simp [z, Pi.single_eq_of_ne hji]
  have hzero := D.kernel_shift_zero_of_recovery C hstable hC S i hrecover z hz hview
  apply ha
  simpa [z] using hzero

include hstable in
/-- Kernel invariance and recovery supply compatibility, so only enclosure of
fully viewed and all-incident blocks is needed for record separation. The
conclusion also allows empty codes and trivial alphabets. -/
theorem encode_eq_of_invariant_recovery [Finite κ] (H : ι → Set ι) (T : Set κ)
    (hrecover : ∀ i, ∀ u ∈ C, ∀ v ∈ C, Set.EqOn u v (H i) → u i = v i)
    (hinternal : ∀ i k, (↑(D.support k) : Set ι) ⊆ H i → k ∈ T)
    (hincident : ∀ k, (∀ i ∈ D.support k, i ∈ H i) → k ∈ T)
    {x y : ι → A} (hx : x ∈ C) (hy : y ∈ C)
    (hrecord : Set.EqOn (D.encode x) (D.encode y) T) :
    D.encode x = D.encode y := by
  cases subsingleton_or_nontrivial A with
  | inl h => exact Subsingleton.elim _ _
  | inr h =>
    apply D.encode_eq_of_compatibility C hstable H T hrecover ?_
      hinternal hincident hx hy hrecord
    intro k i hik hi
    exact D.support_subset_insert_of_recovery C hstable ⟨x, hx⟩ (H i) i
      (hrecover i) hi k hik

include hstable in
/-- Exact attained-record count after deriving compatibility from invariance
and recovery. No nonempty-code or nontrivial-alphabet hypothesis is needed. -/
theorem card_eq_kernel_mul_record_image_of_recovery [Finite κ]
    (H : ι → Set ι) (T : Set κ)
    (hrecover : ∀ i, ∀ u ∈ C, ∀ v ∈ C, Set.EqOn u v (H i) → u i = v i)
    (hinternal : ∀ i k, (↑(D.support k) : Set ι) ⊆ H i → k ∈ T)
    (hincident : ∀ k, (∀ i ∈ D.support k, i ∈ H i) → k ∈ T) :
    Nat.card C = Nat.card (D.encode (A := A)).ker *
      Nat.card (D.syndromeRecord T '' C) := by
  apply CosetRecords.card_eq_subgroup_mul_image D.encode.ker C (D.syndromeRecord T)
  · intro x hx z hz
    exact hstable x hx z hz
  · intro x hx z hz
    have hz' : D.encode z = 0 := hz
    funext k
    change D.encode (x + z) k = D.encode x k
    rw [map_add, hz', add_zero]
  · intro x hx y hy hrecord
    change D.encode (y - x) = 0
    have heq := D.encode_eq_of_invariant_recovery C hstable H T hrecover
      hinternal hincident hx hy (fun k hk => congrFun hrecord ⟨k, hk⟩)
    rw [map_sub, heq, sub_self]

end LeanMachine.DisjointSums
