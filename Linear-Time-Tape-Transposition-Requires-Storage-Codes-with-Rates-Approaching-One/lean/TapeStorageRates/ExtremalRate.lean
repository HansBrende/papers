import TapeStorageRates.RateGap

/-! # The extremal binary rate used in the statement of the paper -/

namespace TapeStorageRates

open DirectedRecovery Filter
open scoped Topology

set_option autoImplicit false

/-- The supremum of the limiting upper rates of admissible binary families at the fixed cap. -/
noncomputable def extremalRate (Δ : ℕ) : ℝ :=
  sSup (Set.range (fun F : SeparatedBinaryFamily Δ => limsup (fun i => storageCodeRate (F.code i)) atTop))

private theorem family_limsup_le_one {Δ : ℕ} (F : SeparatedBinaryFamily Δ) :
    limsup (fun i => storageCodeRate (F.code i)) atTop ≤ 1 :=
  limsup_le_of_le (isCoboundedUnder_le_of_le atTop
    (fun i => MergeDepth.storageCodeRate_nonneg (by simp) (F.nonempty i)))
    (Eventually.of_forall (fun i => MergeDepth.storageCodeRate_le_one (by simp) (F.code i)))

/-- Every witnessed limiting upper rate is at most the extremal rate. -/
theorem SeparatedBinaryFamily.limsup_le_extremalRate {Δ : ℕ} (F : SeparatedBinaryFamily Δ) :
    limsup (fun i => storageCodeRate (F.code i)) atTop ≤ extremalRate Δ := by
  apply le_csSup (a := limsup (fun i => storageCodeRate (F.code i)) atTop)
    (show BddAbove (Set.range (fun G : SeparatedBinaryFamily Δ =>
      limsup (fun i => storageCodeRate (G.code i)) atTop)) from ⟨1, by
        rintro _ ⟨G, rfl⟩; exact family_limsup_le_one G⟩)
  exact ⟨F, rfl⟩

/-- In particular the actual supremum converges to one as the cap grows. No concatenation
of families at different caps is required, and no maximum is assumed attained. -/
theorem RateWitnesses.extremal_rates {k : ℕ} (h : RateWitnesses k) :
    (∃ K : ℝ, 0 < K ∧ ∀ᶠ Δ : ℕ in atTop, 1 - K*deficitScale k Δ ≤ extremalRate Δ) ∧
      Tendsto extremalRate atTop (𝓝 1) := by
  obtain ⟨K, hK, hfamilies⟩ := h
  have bounds : ∀ᶠ Δ : ℕ in atTop, 1 - K*deficitScale k Δ ≤ extremalRate Δ ∧ extremalRate Δ ≤ 1 := by
    filter_upwards [hfamilies] with Δ ⟨F, hF⟩
    refine ⟨hF.trans (F.liminf_le_limsup.trans F.limsup_le_extremalRate), ?_⟩
    unfold extremalRate
    refine csSup_le ?_ ?_
    · exact ⟨_, ⟨F, rfl⟩⟩
    · rintro _ ⟨G, rfl⟩
      exact family_limsup_le_one G
  refine ⟨⟨K, hK, bounds.mono (fun _ hΔ => hΔ.1)⟩, ?_⟩
  have ht : Tendsto (fun Δ => 1 - K*deficitScale k Δ) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub ((tendsto_deficitScale k).const_mul K)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' ht tendsto_const_nhds
    (bounds.mono fun _ hΔ => hΔ.1) (bounds.mono fun _ hΔ => hΔ.2)

end TapeStorageRates
