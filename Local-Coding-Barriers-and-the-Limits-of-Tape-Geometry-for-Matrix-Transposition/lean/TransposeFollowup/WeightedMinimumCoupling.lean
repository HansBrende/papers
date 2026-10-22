import TransposeFollowup.FiniteMinimumCoupling
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Basic.ENNReal.BigOperators

/-! One global finite ordering with small weighted disagreement. The measure
may charge pairs rather than points, so the same ordering can be selected
for all return maps and all heads at once. A measurable exceptional set is
charged explicitly. No invariance of the underlying measure is assumed. -/
namespace TransposeFollowup.FiniteMinimumCoupling
open Classical Finset MeasureTheory Set
open scoped BigOperators ENNReal
set_option autoImplicit false

variable {α : Type*} [Fintype α] [LinearOrder α]

theorem disagreement_count_le (A B : Finset α) (hA : A.Nonempty) (hB : B.Nonempty)
    (δ : ℝ≥0∞) (hδ : (((A ∪ B) \ (A ∩ B)).card : ℝ≥0∞) ≤ δ*(A ∪ B).card) :
    ((univ.filter (fun σ : Equiv.Perm α => first σ A hA ≠ first σ B hB)).card : ℝ≥0∞) ≤
      δ*Fintype.card (Equiv.Perm α) := by
  have hU : ((A ∪ B).card : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr (hA.mono Finset.subset_union_left))
  apply (ENNReal.mul_le_mul_iff_left hU (ENNReal.natCast_ne_top _)).mp
  have he : ((univ.filter (fun σ : Equiv.Perm α => first σ A hA ≠ first σ B hB)).card : ℝ≥0∞)*
      (A ∪ B).card=Fintype.card (Equiv.Perm α)*((A ∪ B) \ (A ∩ B)).card := by
    exact_mod_cast disagreement_count A B hA hB
  calc
    _ = _ := he
    _ ≤ (Fintype.card (Equiv.Perm α) : ℝ≥0∞)*(δ*(A ∪ B).card) := by gcongr
    _ = _ := by ring

theorem exists_small_weighted_disagreement {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (A B : Ω → Finset α) (hA : ∀ x, (A x).Nonempty) (hB : ∀ x, (B x).Nonempty)
    (bad : Set Ω) (hbad : MeasurableSet bad) (δ : ℝ≥0∞)
    (hδ : ∀ x ∉ bad, (((A x ∪ B x) \ (A x ∩ B x)).card : ℝ≥0∞) ≤ δ*(A x ∪ B x).card)
    (hmeas : ∀ σ : Equiv.Perm α,
      MeasurableSet {x | first σ (A x) (hA x) ≠ first σ (B x) (hB x)}) :
    ∃ σ : Equiv.Perm α, μ {x | first σ (A x) (hA x) ≠ first σ (B x) (hB x)} ≤
      δ*μ univ+μ bad := by
  let E (σ : Equiv.Perm α) := {x | first σ (A x) (hA x) ≠ first σ (B x) (hB x)}
  let N : ℝ≥0∞ := Fintype.card (Equiv.Perm α)
  have hcount (x : Ω) :
      ∑ σ : Equiv.Perm α, (E σ).indicator (fun _ => (1 : ℝ≥0∞)) x ≤
        δ*N+bad.indicator (fun _ => N) x := by
    have he : (∑ σ : Equiv.Perm α, (E σ).indicator (fun _ => (1 : ℝ≥0∞)) x)=
        ((Finset.univ.filter (fun σ : Equiv.Perm α => x ∈ E σ)).card : ℝ≥0∞) := by
      simp only [Set.indicator_apply]
      rw [← Finset.sum_filter]
      simp
    rw [he]
    by_cases hx : x ∈ bad
    · rw [Set.indicator_of_mem hx]
      have hc : (Finset.univ.filter (fun σ : Equiv.Perm α => x ∈ E σ)).card ≤
          Fintype.card (Equiv.Perm α) := by
        simpa only [Finset.card_univ] using
          (Finset.card_filter_le (Finset.univ : Finset (Equiv.Perm α)) (fun σ => x ∈ E σ))
      have hc' : ((Finset.univ.filter (fun σ : Equiv.Perm α => x ∈ E σ)).card : ℝ≥0∞) ≤ N := by
        dsimp only [N]
        exact_mod_cast hc
      exact hc'.trans (le_add_left le_rfl)
    · rw [Set.indicator_of_notMem hx, add_zero]
      exact disagreement_count_le (A x) (B x) (hA x) (hB x) δ (hδ x hx)
  have hsum : ∑ σ : Equiv.Perm α, μ (E σ) ≤ N*(δ*μ univ+μ bad) := by
    have hi : (∫⁻ x, ∑ σ : Equiv.Perm α, (E σ).indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ)=
        ∑ σ : Equiv.Perm α, μ (E σ) := by
      rw [lintegral_finsetSum _ (fun σ _ => measurable_const.indicator (hmeas σ))]
      simp only [E, lintegral_indicator_const (hmeas _), one_mul]
    rw [← hi]
    calc
      _ ≤ ∫⁻ x, δ*N+bad.indicator (fun _ => N) x ∂μ := lintegral_mono hcount
      _ = δ*N*μ univ+N*μ bad := by
        rw [lintegral_add_left measurable_const, lintegral_const, lintegral_indicator_const hbad]
      _ = _ := by ring
  obtain ⟨σ, _, hσ⟩ := ENNReal.exists_le_of_sum_le (s:=Finset.univ)
    (f:=fun σ : Equiv.Perm α => μ (E σ)) (g:=fun _ => δ*μ univ+μ bad)
    Finset.univ_nonempty (by simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hsum)
  exact ⟨σ, hσ⟩

end TransposeFollowup.FiniteMinimumCoupling
