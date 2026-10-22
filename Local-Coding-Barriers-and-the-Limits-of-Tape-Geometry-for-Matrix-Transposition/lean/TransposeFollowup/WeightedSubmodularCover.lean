import Mathlib.Tactic

/-! Weighted finite covering for normalized monotone submodular functions.
Applied to entropy only after its hypotheses have been proved. -/

namespace TransposeFollowup

open scoped BigOperators
set_option autoImplicit false

/-- Shearer's covering inequality for a normalized monotone submodular
function. The lower bound on covering multiplicity can be any real. -/
theorem weighted_submodular_cover {ι κ : Type*} [DecidableEq ι] [Fintype κ]
    (U : Finset ι) (f : Finset ι → ℝ)
    (hzero : f ∅ = 0)
    (hmono : Monotone f)
    (hsub : ∀ A B, f (A ∪ B) + f (A ∩ B) ≤ f A + f B)
    (S : κ → Finset ι) (hS : ∀ a, S a ⊆ U)
    (w : κ → ℝ) (hw : ∀ a, 0 ≤ w a) (k : ℝ)
    (hcover : ∀ i ∈ U, k ≤ ∑ a, if i ∈ S a then w a else 0) :
    k * f U ≤ ∑ a, w a * f (S a) := by
  classical
  induction U using Finset.induction_on generalizing f S with
  | empty =>
      have hempty : ∀ a, S a = ∅ := fun a => Finset.subset_empty.mp (hS a)
      simp [hempty, hzero]
  | @insert i U hi ih =>
      let f' := fun A => f (insert i A) - f {i}
      have hz' : f' ∅ = 0 := by simp [f']
      have hm' : Monotone f' := by
        intro A B hAB
        exact sub_le_sub_right (hmono (Finset.insert_subset_insert i hAB)) _
      have hs' : ∀ A B, f' (A ∪ B) + f' (A ∩ B) ≤ f' A + f' B := by
        intro A B
        have h := hsub (insert i A) (insert i B)
        have hu : insert i A ∪ insert i B = insert i (A ∪ B) := by ext; simp
        have hn : insert i A ∩ insert i B = insert i (A ∩ B) := by ext; simp; tauto
        rw [hu, hn] at h
        dsimp only [f']
        linarith
      have hSU : ∀ a, (S a).erase i ⊆ U := by
        intro a j hj
        have hj' := hS a (Finset.mem_of_mem_erase hj)
        rcases Finset.mem_insert.mp hj' with hji | hjU
        · exact False.elim ((Finset.mem_erase.mp hj).1 hji)
        · exact hjU
      have hc' : ∀ j ∈ U, k ≤ ∑ a, if j ∈ (S a).erase i then w a else 0 := by
        intro j hj
        have hji : j ≠ i := by rintro rfl; exact hi hj
        simpa [Finset.mem_erase, hji] using
          hcover j (Finset.mem_insert_of_mem hj)
      have hind := ih f' hz' hm' hs' (fun a => (S a).erase i) hSU hc'
      have hpoint : ∀ a, f' ((S a).erase i) ≤
          f (S a) - (if i ∈ S a then f {i} else 0) := by
        intro a
        by_cases hia : i ∈ S a
        · simp [f', hia, Finset.insert_erase hia]
        · have h := hsub (S a) {i}
          have hinter : S a ∩ {i} = ∅ := by
            ext j
            simp_all
          rw [hinter, hzero, Finset.union_singleton] at h
          have herase : (S a).erase i = S a := by ext j; simp; aesop
          simp only [f', herase, hia, ite_false, sub_zero]
          linarith
      have hsum := Finset.sum_le_sum (s := Finset.univ)
        (fun a _ => mul_le_mul_of_nonneg_left (hpoint a) (hw a))
      change (∑ a, w a * f' ((S a).erase i)) ≤ _ at hsum
      simp only [mul_sub, Finset.sum_sub_distrib] at hsum
      have hsingle : 0 ≤ f {i} := by
        simpa only [hzero] using hmono (Finset.empty_subset ({i} : Finset ι))
      have hcount := mul_le_mul_of_nonneg_right
        (hcover i (Finset.mem_insert_self i U)) hsingle
      simp only [Finset.sum_mul, ite_mul, zero_mul] at hcount
      have hweights : (∑ a, w a * (if i ∈ S a then f {i} else 0)) =
          ∑ a, if i ∈ S a then w a * f {i} else 0 := by
        simp only [mul_ite, mul_zero]
      rw [hweights] at hsum
      dsimp only [f'] at hind hsum
      simp only [mul_sub, Finset.sum_sub_distrib] at hind hsum
      nlinarith

end TransposeFollowup
