import TransposeFollowup.ConjugacyFiberCovering
import TransposeFollowup.FiniteCoverSelection

/-! Select an actual large conjugacy fiber and transfer its covering
complexity to a pairwise commuting set near A^-1*A. -/
namespace TransposeFollowup.SL2Projection
open Classical Matrix Set RealMobius
open scoped Matrix.Norms.Frobenius Pointwise ENNReal NNReal
set_option autoImplicit false
local notation "RMat" => Matrix (Fin 2) (Fin 2) ℝ
local notation "G" => RealMobius.Group

theorem exists_large_conjugacy_fiber_commuting_cover (g : G) {A : Set G}
    (F : Finset RMat) {α r B δ : ℝ} {η : ℝ≥0}
    (hα : 0 < α) (hαhalf : α ≤ 1 / 2) (hg : g ∈ mobiusIdentityBall α)
    (hr : 0 < r) (hfar : r ≤ dist (g : RMat) 1)
    (hB : 1 ≤ B) (hδ : 0 ≤ δ) (hη : 0 < η) (hsmall : 1536 * B ^ 4 * δ ≤ r)
    (hAn : A.Nonempty) (hA : ∀ x ∈ A, ∀ i j, |x i j| ≤ B)
    (hcover : ∀ x ∈ A, ∃ c ∈ F, dist ((x * g * x⁻¹ : G) : RMat) c ≤ δ) :
    ∃ c ∈ F,
      let S := {x : G | x ∈ A ∧ dist ((x * g * x⁻¹ : G) : RMat) c ≤ δ}
      ∃ x₀ ∈ S, ∃ f : S → G,
        (∀ x : S, ∃ s t : ℝ, (f x : RMat) = scalarAffine (g : RMat) s t) ∧
        (∀ x : S, x₀⁻¹ * x ∈ A⁻¹ * A ∧
          dist ((x₀⁻¹ * x : G) : RMat) (f x : RMat) ≤ 12800 * B ^ 6 * δ / r) ∧
        (∀ x y : S, Commute (f x) (f y)) ∧
        Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' A) ≠ ⊤ ∧
        Metric.externalCoveringNumber η (Set.range (fun x : S => (f x : RMat))) ≠ ⊤ ∧
        (Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' A) : ℝ≥0∞).toReal ≤
          (F.card : ℝ) * (8 * B * (12800 * B ^ 6 * δ / r + (η : ℝ)) / (η : ℝ) + 1) ^ 4 *
            (Metric.externalCoveringNumber η (Set.range (fun x : S => (f x : RMat))) : ℝ≥0∞).toReal := by
  let S (c : RMat) : Set G := {x | x ∈ A ∧ dist ((x * g * x⁻¹ : G) : RMat) c ≤ δ}
  let F' := F.filter (fun c => (S c).Nonempty)
  have hF' : F'.Nonempty := by
    obtain ⟨x, hx⟩ := hAn
    obtain ⟨c, hc, hd⟩ := hcover x hx
    exact ⟨c, Finset.mem_filter.mpr ⟨hc, ⟨x, hx, hd⟩⟩⟩
  let C (c : RMat) := (fun x : G => (x : RMat)) '' S c
  have hpieces : ∀ z ∈ (fun x : G => (x : RMat)) '' A, ∃ c ∈ F', z ∈ C c := by
    rintro z ⟨x, hx, rfl⟩
    obtain ⟨c, hc, hd⟩ := hcover x hx
    exact ⟨c, Finset.mem_filter.mpr ⟨hc, ⟨x, hx, hd⟩⟩, ⟨x, ⟨hx, hd⟩, rfl⟩⟩
  have hfin : ∀ c ∈ F', Metric.externalCoveringNumber η (C c) ≠ ⊤ := by
    intro c _
    apply finite_coveringNumber_of_entry_bound (by linarith : 0 ≤ B) hη
    rintro z ⟨x, hx, rfl⟩
    exact hA x hx.1
  obtain ⟨c, hc', hAfin, hbig⟩ := exists_large_cover_piece F' hF'
    ((fun x : G => (x : RMat)) '' A) C hpieces hfin
  obtain ⟨hc, x₀, hx₀⟩ := Finset.mem_filter.mp hc'
  have hpairclose : ∀ x ∈ S c,
      dist ((x * g * x⁻¹ : G) : RMat) ((x₀ * g * x₀⁻¹ : G) : RMat) ≤ 2 * δ := by
    intro x hx
    have hh := dist_triangle ((x * g * x⁻¹ : G) : RMat) c ((x₀ * g * x₀⁻¹ : G) : RMat)
    have hd : dist c ((x₀ * g * x₀⁻¹ : G) : RMat) ≤ δ := by
      rw [dist_comm]; exact hx₀.2
    linarith [hx.2]
  have hsmall' : 768 * B ^ 4 * (2 * δ) ≤ r := by convert hsmall using 1; ring
  obtain ⟨f, hform, hclose', hcomm, _hSfin, hVfin, hbound⟩ := exists_conjugacy_fiber_commuting_cover
    g x₀ hα hαhalf hg hr hfar hB (by positivity : 0 ≤ 2 * δ) hη hsmall' hx₀
    (fun x hx => hA x hx.1) hpairclose
  have hR : 6400 * B ^ 6 * (2 * δ) / r = 12800 * B ^ 6 * δ / r := by ring
  simp only [hR] at hclose' hbound
  refine ⟨c, hc, x₀, hx₀, f, hform, ?_, hcomm, hAfin, hVfin, ?_⟩
  · intro x
    exact ⟨Set.mul_mem_mul (Set.inv_mem_inv.mpr hx₀.1) x.2.1, (hclose' x).2⟩
  · have hcard : (F'.card : ℝ) ≤ (F.card : ℝ) := by exact_mod_cast (Finset.card_filter_le F _)
    calc
      _ ≤ (F'.card : ℝ) * (Metric.externalCoveringNumber η (C c) : ℝ≥0∞).toReal := hbig
      _ ≤ (F.card : ℝ) * (Metric.externalCoveringNumber η (C c) : ℝ≥0∞).toReal :=
        mul_le_mul_of_nonneg_right hcard ENNReal.toReal_nonneg
      _ ≤ (F.card : ℝ) *
          ((8 * B * (12800 * B ^ 6 * δ / r + (η : ℝ)) / (η : ℝ) + 1) ^ 4 *
            (Metric.externalCoveringNumber η (Set.range (fun x : S c => (f x : RMat))) : ℝ≥0∞).toReal) :=
        mul_le_mul_of_nonneg_left hbound (Nat.cast_nonneg _)
      _ = _ := (mul_assoc _ _ _).symm

end TransposeFollowup.SL2Projection
