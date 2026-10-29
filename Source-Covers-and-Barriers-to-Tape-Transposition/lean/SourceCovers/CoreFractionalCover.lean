import SourceCovers.CoreCoverComponents
import SourceCovers.ExactSourceBank
import LeanMachine.FractionalCover

/-! Fractional covers by actual complete core orbits, rooted at every computation time. -/

namespace SourceCovers

open Classical Finset LeanMachine LeanMachine.SourceBank
open scoped BigOperators ENNReal

noncomputable section

variable {k T : ℕ} {xs : Fin k → ℕ → ℤ} {K : Finset (ActualFamily xs T)}

/-- Raw coordinates of one complete retained-core orbit. Roots range over all
computation times, and the covering set need not be contained in the target. -/
def coreRawSets (I : Finset (CoreFamily K)) (x : ℕ → ℕ) (u : Fin T) : Set ℕ :=
  ↑((coreOrbit I u.val).image x)

/-- Minimum fractional weight, with infinity exactly when there is no feasible cover. -/
def fractionalCoreCover (I : Finset (CoreFamily K)) (x : ℕ → ℕ) (S : Finset ℕ) : ℝ≥0∞ :=
  FractionalCover.number S (coreRawSets I x)

theorem fractionalCoreCover_ne_top_iff (I : Finset (CoreFamily K)) (x : ℕ → ℕ)
    (S : Finset ℕ) :
    fractionalCoreCover I x S ≠ ⊤ ↔ ∃ w, FractionalCover.Covers S (coreRawSets I x) w :=
  FractionalCover.number_ne_top_iff S (coreRawSets I x)

/-- The minimum is attained by weights in `[0,1]`, including for an empty target. -/
theorem fractionalCoreCover_exists_optimal (I : Finset (CoreFamily K)) (x : ℕ → ℕ)
    (S : Finset ℕ) (hfinite : fractionalCoreCover I x S ≠ ⊤) :
    ∃ w, FractionalCover.Covers S (coreRawSets I x) w ∧
      FractionalCover.cost w = (fractionalCoreCover I x S).toReal ∧ ∀ u, w u ≤ 1 := by
  have h := (fractionalCoreCover_ne_top_iff I x S).mp hfinite
  simpa only [fractionalCoreCover, FractionalCover.number_toReal h] using
    FractionalCover.exists_optimal h

theorem one_le_fractionalCoreCover_toReal (I : Finset (CoreFamily K)) (x : ℕ → ℕ)
    {S : Finset ℕ} (hS : S.Nonempty) (hfinite : fractionalCoreCover I x S ≠ ⊤) :
    1 ≤ (fractionalCoreCover I x S).toReal := by
  have h := (fractionalCoreCover_ne_top_iff I x S).mp hfinite
  rw [fractionalCoreCover, FractionalCover.number_toReal h]
  exact FractionalCover.one_le_value hS h

theorem coreRawSets_phase_eq (hc : HasSpanColoring K 2) {M ρ : ℕ}
    (hρ : ρ < M) (x : ℕ → ℕ) (u : Fin T) :
    coreRawSets (phaseSurvivors K M ρ) x u =
      ((phaseOrbit K M ρ u.val).image x : Set ℕ) := by
  unfold coreRawSets
  rw [coreOrbit_phase_eq hc hρ]

theorem coreRawSets_phase_shadowOrbit_eq (hc : HasSpanColoring K 2) {M ρ : ℕ}
    (hρ : ρ < M) (x : ℕ → ℕ) (u : Fin T) :
    coreRawSets (phaseSurvivors K M ρ) x u = x '' shadowOrbit (retainedCore K M ρ) u.val := by
  rw [coreRawSets_phase_eq hc hρ, phase_shadowOrbit_exact hc hρ]
  exact coe_image

theorem coreRawSets_root_mem (I : Finset (CoreFamily K)) (x : ℕ → ℕ) (u : Fin T) :
    x u.val ∈ coreRawSets I x u :=
  mem_image_of_mem x (FiniteOrbits.mem_cloud_self _ _ _)

theorem coreRawSets_subset_time_image (I : Finset (CoreFamily K)) (x : ℕ → ℕ) (u : Fin T) :
    coreRawSets I x u ⊆ ((range T).image x : Set ℕ) := by
  intro a ha
  obtain ⟨v, hv, rfl⟩ := mem_image.mp ha
  exact mem_image.mpr ⟨v, mem_range.mpr ((coreOrbit_le I hv).trans_lt u.isLt), rfl⟩

/-- A point read during the computation belongs to the core orbit rooted at
that very time. Thus all-one weights cover every subset of the visited raw coordinates. -/
theorem coreRawSets_one_covers (I : Finset (CoreFamily K)) (x : ℕ → ℕ)
    {S : Finset ℕ} (hS : S ⊆ (range T).image x) :
    FractionalCover.Covers S (coreRawSets I x) (fun _ => 1) := by
  refine ⟨fun _ => zero_le_one, fun a ha => ?_⟩
  obtain ⟨t, ht, rfl⟩ := mem_image.mp (hS ha)
  let u : Fin T := ⟨t, mem_range.mp ht⟩
  have hu : x t ∈ coreRawSets I x u := coreRawSets_root_mem I x u
  have h := single_le_sum (f := fun v => if x t ∈ coreRawSets I x v then (1 : ℝ) else 0)
    (s := univ) (a := u) (fun v _ => by split_ifs <;> norm_num) (mem_univ u)
  simpa only [ite_eq_left hu] using h

/-- Feasibility has an exact description: the target must consist of raw
coordinates visited during the computation. No positivity assumption on `T` is needed. -/
theorem fractionalCoreCover_ne_top_iff_subset (I : Finset (CoreFamily K)) (x : ℕ → ℕ)
    (S : Finset ℕ) :
    fractionalCoreCover I x S ≠ ⊤ ↔ S ⊆ (range T).image x := by
  rw [fractionalCoreCover_ne_top_iff]
  constructor
  · rintro ⟨w, hw⟩ a ha
    by_contra hout
    have hn (u : Fin T) : a ∉ coreRawSets I x u :=
      fun h => hout (coreRawSets_subset_time_image I x u h)
    have h := hw.2 a ha
    simp only [ite_eq_right (hn _), sum_const_zero] at h
    norm_num at h
  · intro hS
    exact ⟨_, coreRawSets_one_covers I x hS⟩

theorem shadowOrbit_le {F : Finset (ActualFamily xs T)} {t u : ℕ}
    (hu : u ∈ shadowOrbit F t) : u ≤ t := by
  obtain ⟨w, _, rfl⟩ := hu
  exact (shadow_word_structure w).2.2 t

theorem raw_shadowOrbit_subset_time_image (F : Finset (ActualFamily xs T)) (x : ℕ → ℕ)
    {t : ℕ} (ht : t < T) :
    x '' shadowOrbit F t ⊆ ((range T).image x : Set ℕ) := by
  rintro a ⟨u, hu, rfl⟩
  exact mem_image.mpr ⟨u, mem_range.mpr ((shadowOrbit_le hu).trans_lt ht), rfl⟩

theorem ExactCoreBank.raw_values_subset_time_image {F : Finset (ActualFamily xs T)}
    {B : Bank} (hB : ExactCoreBank F B) (x : ℕ → ℕ) {t : ℕ} (ht : t < T) :
    rawBankValues B x t ⊆ (range T).image x := by
  intro a ha
  obtain ⟨u, hu, rfl⟩ := mem_image.mp ha
  exact raw_shadowOrbit_subset_time_image F x ht ⟨u, (hB t).subset hu, rfl⟩

theorem fractionalCoreCover_exactBank_ne_top (I : Finset (CoreFamily K))
    {F : Finset (ActualFamily xs T)} {B : Bank} (hB : ExactCoreBank F B)
    (x : ℕ → ℕ) {t : ℕ} (ht : t < T) :
    fractionalCoreCover I x (rawBankValues B x t) ≠ ⊤ :=
  (fractionalCoreCover_ne_top_iff_subset I x _).mpr (hB.raw_values_subset_time_image x ht)

/-- In particular the actual complete source bank, including every exception,
has a finite fractional cover by retained-core orbits. -/
theorem fractionalCoreCover_exactSourceBank_ne_top (hc : HasSpanColoring K 2)
    {M ρ : ℕ} (hM : 2 ≤ M) (hρ : ρ < M) (E : Finset (ActualFamily xs T))
    (x : ℕ → ℕ) {t : ℕ} (ht : t < T) :
    fractionalCoreCover (phaseSurvivors K M ρ) x
      (rawBankValues (exactSourceBank (ρ := ρ) hc hM E) x t) ≠ ⊤ :=
  fractionalCoreCover_exactBank_ne_top _ (exactSourceBank_exact hc hM hρ E) x ht

end
end SourceCovers
