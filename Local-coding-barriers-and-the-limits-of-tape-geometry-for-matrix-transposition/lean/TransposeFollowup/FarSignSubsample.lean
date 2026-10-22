import TransposeFollowup.TraceSquareScalarSeparation

/-! Finite trimming for the trace-square coordinate. A proved bound on
the discarded neighborhood and a two-way sign partition retain a quarter
of the original indices. -/
namespace TransposeFollowup.SL2Projection
open Classical Matrix
open scoped Matrix.Norms.Frobenius
set_option autoImplicit false
local notation "RMat" => Matrix (Fin 2) (Fin 2) ℝ

theorem exists_far_sign_subsample {ι : Type*} (F : Finset ι)
    (f : ι → RMat) (t : ι → ℝ) (r : ℝ) (hF : F.Nonempty)
    (hhalf : 2 * (F.filter (fun i => dist (f i) 1 ≤ r)).card ≤ F.card) :
    ∃ S : Finset ι, S ⊆ F ∧ S.Nonempty ∧ F.card ≤ 4*S.card ∧
      (∀ i ∈ S, r < dist (f i) 1) ∧
      (∀ i ∈ S, ∀ j ∈ S, 0 ≤ t i * t j) := by
  classical
  let T := F.filter (fun i => ¬ dist (f i) 1 ≤ r)
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := F) (fun i => dist (f i) 1 ≤ r)
  have hT : F.card ≤ 2*T.card := by dsimp only [T]; omega
  have hsign := Finset.card_filter_add_card_filter_not (s := T) (fun i => 0 ≤ t i)
  have hchoice : ∃ S : Finset ι, S ⊆ T ∧ T.card ≤ 2*S.card ∧
      (∀ i ∈ S, ∀ j ∈ S, 0 ≤ t i * t j) := by
    by_cases hpos : (T.filter (fun i => ¬ 0 ≤ t i)).card ≤
        (T.filter (fun i => 0 ≤ t i)).card
    · refine ⟨T.filter (fun i => 0 ≤ t i), Finset.filter_subset _ _, by omega, ?_⟩
      intro i hi j hj
      exact mul_nonneg (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
    · refine ⟨T.filter (fun i => ¬ 0 ≤ t i), Finset.filter_subset _ _, by omega, ?_⟩
      intro i hi j hj
      exact mul_nonneg_of_nonpos_of_nonpos
        (le_of_lt (lt_of_not_ge (Finset.mem_filter.mp hi).2))
        (le_of_lt (lt_of_not_ge (Finset.mem_filter.mp hj).2))
  obtain ⟨S, hST, hcard, hsignS⟩ := hchoice
  have hfour : F.card ≤ 4*S.card := by omega
  have hSn : S.Nonempty := Finset.card_pos.mp (by have hh := hF.card_pos; omega)
  refine ⟨S, hST.trans (Finset.filter_subset _ _), hSn, hfour, ?_, hsignS⟩
  intro i hi
  exact lt_of_not_ge (Finset.mem_filter.mp (hST hi)).2

end TransposeFollowup.SL2Projection
