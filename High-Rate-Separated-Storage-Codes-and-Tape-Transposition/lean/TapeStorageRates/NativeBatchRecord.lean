import TapeStorageRates.NativeBatchRecordLocal

/-! # Joint support of all native records in selected intervals

One seed is charged per interval. Overlapping windows and correlations
between seeds require no independence assumption.
-/

namespace TapeStorageRates.NativeBatchRecord

open Finset Transpose Transpose.Tape Transpose.Tape.Impl MergeDepth Native

set_option autoImplicit false

/-- The actual trace remains within its entry windows on each selected
interval. This includes stationary terminal intervals. -/
structure WindowIntervals {k : ℕ} (τ : Trace k) (s : ℕ) {I : Type*}
    (J : Finset I) (lo hi : I → ℕ) : Prop where
  input : ∀ j ∈ J, ∀ t, lo j ≤ t → t < hi j →
    Fits s 0 (τ.input t-τ.input (lo j))
  work : ∀ j ∈ J, ∀ t, lo j ≤ t → t < hi j → ∀ h,
    Fits s 0 (τ.work h t-τ.work h (lo j))
  live : ∀ j ∈ J, ∀ t, lo j ≤ t → t < hi j → τ t ≠ none

open Classical in
/-- All revealed physical records jointly fit in one seed per covering
interval. The machine and the words are arbitrary; only their actual common
trace and the specified local windows are used. -/
theorem joint_record_support {M : TM} {X I : Type*} (word : X → List Bool)
    (S : Finset X) (τ : Trace M.k) (s : ℕ) (J : Finset I) (lo hi : I → ℕ)
    (htrace : ∀ x ∈ S, trace M (word x) = τ)
    (hwin : WindowIntervals τ s J lo hi) (Γ : Finset ℕ)
    (hcover : ∀ t ∈ Γ, ∃ j ∈ J, lo j ≤ t ∧ t < hi j) :
    (S.image (fun x => fun t : Γ => blockVal M 1 (word x) t)).card ≤
      Fintype.card (Seed M s) ^ J.card := by
  let seeds (x : X) : J → Seed M s := fun j =>
    seed M s (lo j) (τ.input (lo j)) (fun h => τ.work h (lo j)) (word x)
  have hdet : ∀ x ∈ S, ∀ y ∈ S, seeds x = seeds y →
      (fun t : Γ => blockVal M 1 (word x) t) =
        (fun t : Γ => blockVal M 1 (word y) t) := by
    intro x hx y hy he
    funext t
    obtain ⟨j,hj,hlo,hhi⟩ := hcover t t.property
    have hseed := congrFun he (⟨j,hj⟩ : J)
    have hip : (run M (word x) (lo j)).inPos = (run M (word y) (lo j)).inPos := by
      simp only [inPos_eq_input,htrace x hx,htrace y hy]
    have hwp : (run M (word x) (lo j)).workPos = (run M (word y) (lo j)).workPos := by
      funext h
      simp only [workPos_eq_work,htrace x hx,htrace y hy]
    apply record_eq_of_seed_eq hseed hip hwp ?_ ?_ ?_ t hlo hhi
    · intro u hu hv
      simpa only [inPos_eq_input,htrace x hx] using hwin.input j hj u hu hv
    · intro u hu hv h
      simpa only [workPos_eq_work,htrace x hx] using hwin.work j hj u hu hv h
    · intro u hu hv hz
      apply hwin.live j hj u hu hv
      rw [← htrace x hx]
      exact (trace_eq_none_iff u).mpr hz
  have h := card_image_le_of_seed S (fun x => fun t : Γ => blockVal M 1 (word x) t)
    seeds hdet
  simpa only [Fintype.card_fun,Fintype.card_coe] using h

open Classical in
/-- For the published native compiler, the joint records use linearly many
bits per selected interval, uniformly in the batch size and input length. -/
theorem compiler_joint_record_support (M : TM) {s : ℕ} (hs : 0<s)
    {X I : Type*} (word : X → List Bool) (S : Finset X) (τ : Trace M.k)
    (J : Finset I) (lo hi : I → ℕ)
    (htrace : ∀ x ∈ S, trace (machine M hs) (word x) = τ)
    (hwin : WindowIntervals τ s J lo hi) (Γ : Finset ℕ)
    (hcover : ∀ t ∈ Γ, ∃ j ∈ J, lo j ≤ t ∧ t < hi j) :
      (S.image (fun x => fun t : Γ => blockVal (machine M hs) 1 (word x) t)).card ≤
        2 ^ (batchSeedBits M*s*J.card) := by
  calc
    _ ≤ Fintype.card (Seed (machine M hs) s) ^ J.card :=
      joint_record_support (M := machine M hs) word S τ s J lo hi htrace hwin Γ hcover
    _ ≤ (2^(batchSeedBits M*s))^J.card := Nat.pow_le_pow_left (seed_card_le M hs) _
    _ = _ := (pow_mul _ _ _).symm

end TapeStorageRates.NativeBatchRecord
