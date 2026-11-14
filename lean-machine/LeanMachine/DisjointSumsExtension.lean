import LeanMachine.DisjointSums

/-! # Extending partially prescribed disjoint sums

Prescribing coordinates constrains exactly the parity blocks that are already
fully observed. Every other block has a missing coordinate on which to correct
its sum. The proof reuses surjectivity of the disjoint-sum encoder on residual
supports; the coordinate type and additive alphabet need not be finite.
-/

namespace LeanMachine.DisjointSums

open Finset
open scoped BigOperators

variable {ι κ A : Type*} (C : DisjointSums ι κ) [Finite κ] [AddCommGroup A]

/-- A partial assignment extends to arbitrary target sums exactly when its
fully observed blocks already have their target sums. -/
theorem exists_extension_iff (S : Set ι) (x : ι → A) (y : κ → A) :
    (∃ z : ι → A, Set.EqOn z x S ∧ C.encode z = y) ↔
      ∀ k, (↑(C.support k) : Set ι) ⊆ S → C.encode x k = y k := by
  classical
  constructor
  · rintro ⟨z, hzx, hzy⟩ k hk
    calc
      C.encode x k = C.encode z k := by
        apply sum_congr rfl
        intro i hi
        exact (hzx (hk hi)).symm
      _ = y k := congrFun hzy k
  · intro hconsistent
    let _ : Fintype κ := Fintype.ofFinite κ
    let K := {k : κ // ¬ (↑(C.support k) : Set ι) ⊆ S}
    let D : DisjointSums ι K := {
      support := fun k => (C.support k.val).filter (fun i => i ∉ S)
      nonempty := by
        intro k
        by_contra h
        apply k.property
        intro i hi
        by_contra hiS
        exact h ⟨i, mem_filter.mpr ⟨hi, hiS⟩⟩
      disjoint := by
        intro k l hkl
        apply (C.disjoint (Subtype.val_injective.ne hkl)).mono
        · exact filter_subset _ _
        · exact filter_subset _ _ }
    obtain ⟨u, hu⟩ := D.encode_surjective (fun k => y k.val - C.encode x k.val)
    let δ : ι → A := fun i => if i ∈ S then 0 else u i
    have hδ (k : κ) : C.encode δ k = y k - C.encode x k := by
      by_cases hk : (↑(C.support k) : Set ι) ⊆ S
      · rw [hconsistent k hk, sub_self]
        apply sum_eq_zero
        intro i hi
        simp [δ, hk hi]
      · have hu' := congrFun hu (⟨k, hk⟩ : K)
        simpa [encode_apply, D, δ, sum_filter, ite_not] using hu'
    refine ⟨x + δ, ?_, ?_⟩
    · intro i hi
      simp [δ, hi]
    · ext k
      simp only [map_add, Pi.add_apply, hδ]
      abel

/-- Matching two partial words by a parity-kernel shift requires only equality
of their sums on the fully observed blocks. -/
theorem exists_kernel_shift (S : Set ι) (x y : ι → A)
    (hconsistent : ∀ k, (↑(C.support k) : Set ι) ⊆ S →
      C.encode x k = C.encode y k) :
    ∃ z : ι → A, C.encode z = 0 ∧ Set.EqOn (x + z) y S := by
  obtain ⟨z, hz, hzero⟩ := (C.exists_extension_iff S (y - x) 0).mpr (by
    intro k hk
    simp only [map_sub, Pi.sub_apply, Pi.zero_apply]
    exact sub_eq_zero.mpr (hconsistent k hk).symm)
  refine ⟨z, hzero, ?_⟩
  intro i hi
  change x i + z i = y i
  rw [hz hi]
  simp only [Pi.sub_apply]
  abel

/-- Coordinatewise additive automorphisms reduce weighted parity blocks to
ordinary disjoint sums without changing which coordinates are observed. -/
theorem exists_weighted_extension_iff (θ : ι → A ≃+ A) (S : Set ι)
    (x : ι → A) (y : κ → A) :
    (∃ z : ι → A, Set.EqOn z x S ∧ C.encode (fun i => θ i (z i)) = y) ↔
      ∀ k, (↑(C.support k) : Set ι) ⊆ S →
        C.encode (fun i => θ i (x i)) k = y k := by
  constructor
  · rintro ⟨z, hz, hsum⟩
    apply (C.exists_extension_iff S (fun i => θ i (x i)) y).mp
    exact ⟨fun i => θ i (z i), fun i hi => congrArg (θ i) (hz hi), hsum⟩
  · intro hconsistent
    obtain ⟨z, hz, hsum⟩ :=
      (C.exists_extension_iff S (fun i => θ i (x i)) y).mpr hconsistent
    refine ⟨fun i => (θ i).symm (z i), ?_, ?_⟩
    · intro i hi
      change (θ i).symm (z i) = x i
      rw [hz hi]
      exact (θ i).symm_apply_apply (x i)
    · simpa only [AddEquiv.apply_symm_apply] using hsum

end LeanMachine.DisjointSums
