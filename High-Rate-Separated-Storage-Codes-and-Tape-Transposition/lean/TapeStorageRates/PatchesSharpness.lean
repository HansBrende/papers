import TapeStorageRates.PatchesFamily

/-! # Repeated bits attain the coefficient two at overlap one -/

namespace TapeStorageRates

open Finset DirectedRecovery MotionDepthCodes

set_option autoImplicit false

/-- On `m` disjoint pairs, each partner recovers its bit. All paired distances
are infinite, every target is served by one size-two patch, and the deficit
is exactly `m` bits. -/
theorem repetition_pairs_sharp (m : ℕ) :
    ∃ (N : Fin m × Bool → Finset (Fin m × Bool)) (C : Finset ((Fin m × Bool) → Bool)),
      C.Nonempty ∧ IsStorageCode N C ∧ (∀ t, shortPairedCoordinates N t = ∅) ∧
      Nonempty (RecoveryPatches (Fin m) N C univ 2 1) ∧
      Real.logb 2 C.card = m ∧
      (Fintype.card (Fin m × Bool) : ℝ) = 2 * (Fintype.card (Fin m × Bool) - Real.logb 2 C.card) := by
  classical
  let N (q : Fin m × Bool) : Finset (Fin m × Bool) := {(q.1, !q.2)}
  let enc (x : Fin m → Bool) (q : Fin m × Bool) := x q.1
  let C := univ.image enc
  have hinj : Function.Injective enc := fun x y h => funext fun i => congrFun h (i, false)
  have hcard : C.card = 2 ^ m := by simp [C, card_image_of_injective _ hinj]
  have hs : IsStorageCode N C := by
    rintro _ hx _ hy q hagree
    obtain ⟨x, _, rfl⟩ := mem_image.mp hx
    obtain ⟨y, _, rfl⟩ := mem_image.mp hy
    exact hagree (q.1, !q.2) (mem_singleton_self _)
  let P (i : Fin m) := univ.filter fun q : Fin m × Bool => q.1 = i
  have hsize (i : Fin m) : (P i).card ≤ 2 := by
    have h : P i = {(i, false), (i, true)} := by
      ext ⟨j, b⟩
      cases b <;> simp [P]
    simp [h]
  have cov : RecoveryPatches (Fin m) N C univ 2 1 :=
    { patch := P, served := P, size_le := hsize, within := fun _ => subset_rfl
      overlap_le := by
        intro q
        have h : (univ.filter fun j => q ∈ P j) = {q.1} := by
          ext j
          simp [P, eq_comm]
        simp [h]
      covers := fun q _ => ⟨q.1, by simp [P]⟩
      recovers := by
        intro j q hq x hx y hy hagree
        apply hs x hx y hy q
        intro u hu
        obtain rfl := mem_singleton.mp hu
        exact hagree _ (mem_singleton_self _) (by simpa [P] using hq) }
  have hlog : Real.logb 2 C.card = m := by
    rw [hcard, Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast,
      Real.logb_rpow (by norm_num) (by norm_num)]
  refine ⟨N, C, univ_nonempty.image enc, hs, ?_, ⟨cov⟩, hlog, ?_⟩
  · exact shortPairedCoordinates_eq_empty_of_colors N Prod.snd (fun q => !q.2)
      (fun ⟨_, b⟩ => by change b ≠ !b; cases b <;> decide)
      (fun _ _ hu => by obtain rfl := mem_singleton.mp hu; rfl)
  · simp [hlog]
    ring

end TapeStorageRates
