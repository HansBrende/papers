import TransposeFollowup.LargeConjugacyFiber
import TransposeFollowup.SL2ComplexConjugation

/-! Separated scalar traces give disjoint classes of external cover
centers, and hence an actual conjugacy orbit with a small cover. -/
namespace TransposeFollowup.SL2Projection
open Classical Matrix Set RealMobius
open scoped Matrix.Norms.Frobenius Pointwise
set_option autoImplicit false
local notation "RMat" => Matrix (Fin 2) (Fin 2) ℝ
local notation "G" => RealMobius.Group

theorem trace_error_le_frobenius_dist (a b : RMat) :
    |Matrix.trace a - Matrix.trace b| ≤ 2 * dist a b := by
  have hh := abs_add_le (a 0 0 - b 0 0) (a 1 1 - b 1 1)
  have he : Matrix.trace a - Matrix.trace b = (a 0 0 - b 0 0) + (a 1 1 - b 1 1) := by
    simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_two]
    ring
  rw [he]
  linarith [entry_error_le_frobenius_dist a b 0 0, entry_error_le_frobenius_dist a b 1 1]

theorem exists_small_trace_bucket (T : Finset ℝ) (F : Finset RMat) {δ : ℝ}
    (hT : T.Nonempty)
    (hsep : ∀ s ∈ T, ∀ t ∈ T, s ≠ t → 4 * δ < |s - t|) :
    ∃ t ∈ T, T.card * (F.filter (fun c => |Matrix.trace c - t| ≤ 2 * δ)).card ≤ F.card := by
  let bucket (t : ℝ) := F.filter (fun c => |Matrix.trace c - t| ≤ 2 * δ)
  have hdis : (T : Set ℝ).PairwiseDisjoint bucket := by
    intro s hs t ht hne
    apply Finset.disjoint_left.mpr
    intro c hcs hct
    have hcs' : |s - Matrix.trace c| ≤ 2 * δ := by
      rw [abs_sub_comm]
      exact (Finset.mem_filter.mp hcs).2
    have hct' := (Finset.mem_filter.mp hct).2
    have hh := abs_sub_le s (Matrix.trace c) t
    have hst := hsep s hs t ht hne
    linarith
  have hsum : ∑ t ∈ T, (bucket t).card ≤ F.card := by
    rw [← Finset.card_biUnion hdis]
    apply Finset.card_le_card
    intro c hc
    obtain ⟨t, _ht, hct⟩ := Finset.mem_biUnion.mp hc
    exact (Finset.mem_filter.mp hct).1
  obtain ⟨t, ht, hmin⟩ := T.exists_min_image (fun t => (bucket t).card) hT
  refine ⟨t, ht, ?_⟩
  calc
    _ = ∑ _s ∈ T, (bucket t).card := by simp [bucket]
    _ ≤ ∑ s ∈ T, (bucket s).card := Finset.sum_le_sum (fun s hs => hmin s hs)
    _ ≤ _ := hsum

theorem conjugate_mem_mixed_product {A D : Set G} {g x : G} (hg : g ∈ D) (hx : x ∈ A) :
    x * g * x⁻¹ ∈ A * D * A⁻¹ := by
  exact Set.mul_mem_mul (Set.mul_mem_mul hx hg) (Set.inv_mem_inv.mpr hx)

theorem exists_small_conjugacy_orbit_cover {A D : Set G} (T : Finset ℝ) (F : Finset RMat)
    {δ : ℝ} (hT : T.Nonempty)
    (hTD : (T : Set ℝ) ⊆ (fun g : G => Matrix.trace (g : RMat)) '' D)
    (hsep : ∀ s ∈ T, ∀ t ∈ T, s ≠ t → 4 * δ < |s - t|)
    (hcover : ∀ z ∈ A * D * A⁻¹, ∃ c ∈ F, dist (z : RMat) c ≤ δ) :
    ∃ g ∈ D, ∃ E : Finset RMat, E ⊆ F ∧ T.card * E.card ≤ F.card ∧
      ∀ x ∈ A, ∃ c ∈ E, dist ((x * g * x⁻¹ : G) : RMat) c ≤ δ := by
  obtain ⟨t, ht, hcard⟩ := exists_small_trace_bucket T F hT hsep
  obtain ⟨g, hg, htr⟩ := hTD ht
  let E := F.filter (fun c => |Matrix.trace c - t| ≤ 2 * δ)
  refine ⟨g, hg, E, Finset.filter_subset _ _, hcard, ?_⟩
  intro x hx
  obtain ⟨c, hc, hd⟩ := hcover _ (conjugate_mem_mixed_product hg hx)
  have ht' : Matrix.trace ((x * g * x⁻¹ : G) : RMat) = t := by
    exact (SL2Escape.sl2_trace_conjugate x g).trans htr
  have htrace := trace_error_le_frobenius_dist ((x * g * x⁻¹ : G) : RMat) c
  rw [ht', abs_sub_comm] at htrace
  have hct : |Matrix.trace c - t| ≤ 2 * δ := by linarith
  exact ⟨c, Finset.mem_filter.mpr ⟨hc, hct⟩, hd⟩

end TransposeFollowup.SL2Projection
