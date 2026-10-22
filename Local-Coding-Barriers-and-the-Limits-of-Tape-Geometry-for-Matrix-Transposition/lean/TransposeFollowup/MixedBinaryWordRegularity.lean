import TransposeFollowup.BinarySlotFamilyRegularity
import TransposeFollowup.ScheduledWordSlots
import TransposeFollowup.FiniteAffineSums

/-! Bounded mixed words inherit simultaneous affine approximants. Each
slot is shifted by its actual paid prefix time; start times need not
converge. The entire word error is a fixed finite sum of vanishing errors. -/
namespace TransposeFollowup.MixedBinaryWord
open Classical Set Filter Topology Finset AffineMotion
open BinaryBankOperation (Operation)
set_option autoImplicit false

theorem slot_valid {P : ℕ} {ops : List Operation} (hv : Valid P ops) (j : ℕ) :
    BinaryBankSlot.Valid P (ops[j]?) := by
  intro op hop
  exact hv op (List.mem_of_getElem? hop)

theorem path_eq_sum_slots (P : ℕ) (ops : List Operation) {K : ℕ} (hK : ops.length ≤ K) (h : Fin 2) (n : ℕ) :
    path P ops h n = ∑ j : Fin K,
      BinaryBankSlot.path P (ops[j.val]?) h (n-ticks P (ops.take j.val)) := by
  rw [path,ScheduledWord.path_eq_sum_slots _ _ ops K hK,Finset.sum_range]
  rfl

theorem affine_approximation_subsequence {K : ℕ} {P : ℕ → ℕ} (hP : ∀ i, 0 < P i)
    (ops : ℕ → List Operation) (hv : ∀ᶠ i in atTop, Valid (P i) (ops i))
    (hK : ∀ᶠ i in atTop, (ops i).length ≤ K)
    (hPinf : Tendsto (fun i => (P i : ℝ)) atTop atTop) {H : ℝ} (hH : 0 ≤ H) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ (J : ℕ) (e : ℕ → ℝ) (q : ℕ → ℕ → Fin 2 → ℝ → ℝ),
      Tendsto e atTop (𝓝 0) ∧ ∀ᶠ i in atTop, ∀ A,
        (∀ h, HasAffineIntervalCover J (q i A h) H) ∧
        ∀ h t, |(path (P (φ i)) (ops (φ i)) h (⌊(P (φ i) : ℝ)*t⌋₊-A) : ℝ)/P (φ i)-q i A h t| ≤ e i := by
  obtain ⟨φ,hφ,J,es,qs,_,hes,hqs⟩ := BinaryBankSlot.finite_affine_approximation_subsequence hP
    (fun i (j : Fin K) => (ops i)[j.val]?) (hv.mono fun i hi j => slot_valid hi j.val) hPinf hH
  refine ⟨φ,hφ,J^K,fun i => ∑ j, es j i,
    fun i A h t => ∑ j, qs j i (A+ticks (P (φ i)) ((ops (φ i)).take j.val)) h t,?_,?_⟩
  · simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun j _ => hes j)
  · filter_upwards [hqs,hφ.tendsto_atTop.eventually hK] with i hi hk
    intro A
    refine ⟨fun h => HasAffineIntervalCover.sum_fin hH _ (fun j => (hi j _).1 h),?_⟩
    intro h t
    rw [path_eq_sum_slots _ _ hk,Int.cast_sum,Finset.sum_div,← Finset.sum_sub_distrib]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro j _
    simpa only [Nat.sub_sub] using (hi j (A+ticks (P (φ i)) ((ops (φ i)).take j.val))).2 h t

end TransposeFollowup.MixedBinaryWord
