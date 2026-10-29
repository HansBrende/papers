import SourceCovers.SerialCoverTargets
import SourceCovers.CoreFractionalCover

set_option autoImplicit false

/-! Exact fractional cover of the prescribed raw target set. The seed
universe may be all computation times or any finite selection containing
the Q exhibited seeds. Identifying the joint orbit with this target set
is a separate construction obligation. -/

namespace SourceCovers

open Classical Finset LeanMachine
open scoped BigOperators ENNReal
noncomputable section

/-- Identify arbitrary retained indexed cores with their actual-family
word orbits. Unlike the phase-specific adapter, this needs no coloring. -/
theorem coreRawSets_shadowOrbit_image {k T : ℕ} {xs : Fin k → ℕ → ℤ}
    {K : Finset (ActualFamily xs T)} (I : Finset (CoreFamily K))
    (x : ℕ → ℕ) (u : Fin T) :
    coreRawSets I x u = x '' shadowOrbit (I.image Subtype.val) u.val := by
  have he : shadowOrbit (I.image Subtype.val) u.val = (coreOrbit I u.val : Set ℕ) := by
    simpa only [shadowOrbit, FiniteOrbits.wordOrbit] using
      (FiniteOrbits.wordOrbit_image I Subtype.val ActualFamily.shadowAction u.val).trans
        (core_orbit_exact I u.val)
  rw [he]
  exact coe_image

namespace SerialGeometry.Parameters

variable (P : Parameters) {k T : ℕ} {xs : Fin k → ℕ → ℤ}
  (head : Fin k) (hx : xs head = NativeExcursion.walk P.early)
  (hT : P.early.arrive 0 < T)

local notation "H" => NativeExcursion.family P.early head hx hT

/-- Arbitrary additional seeds and arbitrary late core families do not
reduce the exact Q-point packing cost. -/
theorem serial_cover_number (K : Finset (ActualFamily xs T)) (hH : H ∈ K)
    (hK : ∀ F ∈ K, F = H ∨ 3 * P.length ≤ F.start)
    {ι : Type*} [Fintype ι] (seed : ι → ℕ)
    (choose : Fin P.targets → ι) (hchoose : ∀ i, seed (choose i) = P.coverSeed i) :
    FractionalCover.number P.completeRaw (fun u => P.raw '' shadowOrbit K (seed u)) =
      (P.targets : ℝ≥0∞) := by
  let A : ι → Set ℕ := fun u => P.raw '' shadowOrbit K (seed u)
  let chosen : Finset ι := univ.image choose
  let w : ι → ℝ := fun u => if u ∈ chosen then 1 else 0
  have hinj : Function.Injective choose := by
    intro i j hij
    apply P.coverSeed_injective
    exact (hchoose i).symm.trans ((congrArg seed hij).trans (hchoose j))
  have hcard : chosen.card = P.targets := by
    change (univ.image choose).card = P.targets
    rw [card_image_of_injective _ hinj]
    exact Fintype.card_fin _
  have hnonneg : ∀ u, 0 ≤ w u := by intro u; dsimp [w]; split <;> norm_num
  have hcost : FractionalCover.cost w = (P.targets : ℝ) := by
    simp [FractionalCover.cost, w, hcard]
  have hw : FractionalCover.Covers P.completeRaw A w := by
    refine ⟨hnonneg, fun a ha => ?_⟩
    have hwitness : ∃ i : Fin P.targets, a ∈ A (choose i) := by
      rcases mem_insert.mp ha with rfl | ha
      · refine ⟨0, ?_⟩
        change 0 ∈ P.raw '' shadowOrbit K (seed (choose 0))
        rw [hchoose, P.coverSeed_rawOrbit head hx hT K hH hK]
        simp
      · obtain ⟨i, _, rfl⟩ := mem_image.mp ha
        refine ⟨i, ?_⟩
        change P.coverTarget i ∈ P.raw '' shadowOrbit K (seed (choose i))
        rw [hchoose, P.coverSeed_rawOrbit head hx hT K hH hK]
        simp
    obtain ⟨i, hi⟩ := hwitness
    have hwi : w (choose i) = 1 := by simp [w, chosen]
    calc
      1 = if a ∈ A (choose i) then w (choose i) else 0 := by rw [ite_eq_left hi, hwi]
      _ ≤ ∑ u, if a ∈ A u then w u else 0 :=
        single_le_sum (f := fun u => if a ∈ A u then w u else 0)
          (fun u _ => by split_ifs; exact hnonneg u; exact le_rfl) (mem_univ _)
  have hvalue : FractionalCover.value P.completeRaw A = (P.targets : ℝ) := by
    apply le_antisymm
    · rw [← hcost]
      exact csInf_le ⟨0, by rintro _ ⟨v, hv, rfl⟩; exact FractionalCover.cost_nonneg hv⟩
        ⟨w, hw, rfl⟩
    · obtain ⟨v, hv, he, _⟩ := FractionalCover.exists_optimal ⟨w, hw⟩
      rw [← he]
      have hl := P.isolated_core_cover_lower head hx hT K hK P.coverTargets P.completeRaw
        (subset_insert _ _) (fun _ ha => P.coverTargets_avoid ha) seed v hv
      simpa only [P.coverTargets_card] using hl
  change FractionalCover.number P.completeRaw A = _
  simp only [FractionalCover.number, ite_eq_left (show ∃ v, FractionalCover.Covers P.completeRaw A v
    from ⟨w, hw⟩), hvalue, ENNReal.ofReal_natCast]

theorem serial_cover_number_all (K : Finset (ActualFamily xs T)) (hH : H ∈ K)
    (hK : ∀ F ∈ K, F = H ∨ 3 * P.length ≤ F.start) :
    FractionalCover.number P.completeRaw (fun u : Fin T => P.raw '' shadowOrbit K u.val) =
      (P.targets : ℝ≥0∞) := by
  apply P.serial_cover_number head hx hT K hH hK Fin.val
    (fun i => ⟨P.coverSeed i, ?_⟩) (fun _ => rfl)
  have ht : 3 * P.length < T := by simpa using hT
  exact (P.coverSeed_bounds i).2.trans ht

/-- This applies in particular when the allowed seeds are the original
joint orbit, once the construction proves that all Q seeds are reached. -/
theorem serial_cover_number_restrict (K : Finset (ActualFamily xs T)) (hH : H ∈ K)
    (hK : ∀ F ∈ K, F = H ∨ 3 * P.length ≤ F.start)
    (R : Finset ℕ) (hR : ∀ i, P.coverSeed i ∈ R) :
    FractionalCover.number P.completeRaw (fun u : R => P.raw '' shadowOrbit K u.val) =
      (P.targets : ℝ≥0∞) :=
  P.serial_cover_number head hx hT K hH hK Subtype.val
    (fun i => ⟨P.coverSeed i, hR i⟩) (fun _ => rfl)

/-- The exact number uses the paper's existing fractional-core-cover
definition, with every computation time allowed as a witness. -/
theorem serial_fractional_core_cover {K₀ : Finset (ActualFamily xs T)}
    (I : Finset (CoreFamily K₀)) (hH : H ∈ I.image Subtype.val)
    (hK : ∀ F ∈ I.image Subtype.val, F = H ∨ 3 * P.length ≤ F.start) :
    fractionalCoreCover I P.raw P.completeRaw = (P.targets : ℝ≥0∞) := by
  unfold fractionalCoreCover
  have he : coreRawSets I P.raw =
      fun u => P.raw '' shadowOrbit (I.image Subtype.val) u.val :=
    funext (coreRawSets_shadowOrbit_image I P.raw)
  rw [he]
  exact P.serial_cover_number_all head hx hT _ hH hK

end SerialGeometry.Parameters
end
end SourceCovers
