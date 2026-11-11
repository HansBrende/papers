import AdaptiveTransfer.TransferGuardsClock
import AdaptiveTransfer.TransferGuardsHops
import AdaptiveTransfer.TransferRoutes
import AdaptiveTransfer.TransferClockShadow

/-! Guarded projection through the actual aligned compiler. Only endpoint
shadow is needed: arbitrary source excursions can be removed by the checked
closed-band native dependency route. All cut endpoints and singleton paths
are retained, with no input-revisit edges. -/
namespace AdaptiveTransfer.TransferGuards
open Finset BoundedNesting MergeDepth TapeStorageRates
open AdaptiveTransfer.TransferClock AdaptiveTransfer.TransferBandPaths

noncomputable def projectionGuard {k : ℕ} (s t : ℕ) (xs ys : Fin k → ℕ → ℤ)
    (R : ℕ) (B : Finset ℕ) : Finset ℕ :=
  batchGuard s t B ∪ hopGuard xs ys (sourceClock s t) (alignedTime s t) R B

theorem projectionGuard_card_le {k s t R : ℕ} (xs ys : Fin k → ℕ → ℤ)
    (hs : 1 ≤ s) (B : Finset ℕ) (hB : ∀ b ∈ B, b < t) :
    (projectionGuard s t xs ys R B).card ≤
      (4 * batchLength s + k * (2 * R + 1)) * B.card := by
  calc
    _ ≤ (batchGuard s t B).card +
        (hopGuard xs ys (sourceClock s t) (alignedTime s t) R B).card := card_union_le _ _
    _ ≤ 4 * batchLength s * B.card + k * (2 * R + 1) * B.card :=
      Nat.add_le_add (batchGuard_card_le hs B hB) (hopGuard_card_le xs ys (sourceClock_mono s t) B)
    _ = _ := by ring

theorem batchGuard_time {s t u : ℕ} {B : Finset ℕ} (hu : u ∈ batchGuard s t B) :
    u < alignedTime s t := by
  obtain ⟨b, _, hu⟩ := mem_biUnion.mp hu
  obtain ⟨j, _, hu⟩ := mem_biUnion.mp hu
  exact (mem_Ico.mp hu).2.trans_le (min_le_right _ _)

theorem projectionGuard_time {k s t R u : ℕ} {xs ys : Fin k → ℕ → ℤ} {B : Finset ℕ}
    (hu : u ∈ projectionGuard s t xs ys R B) : u < alignedTime s t := by
  rcases mem_union.mp hu with hu | hu
  · exact batchGuard_time hu
  · exact hopGuard_time hu

theorem projected_endpoint_avoids {k s t R u : ℕ} {xs ys : Fin k → ℕ → ℤ} {B : Finset ℕ}
    (hu : u < alignedTime s t) (hgood : u ∉ projectionGuard s t xs ys R B) :
    sourceClock s t u ∉ B := fun hb =>
  hgood (mem_union_left _ (endpoint_in_batchGuard hu hb))

/-- Every surviving literal physical dependency edge has an original source
route avoiding B. The work case uses the actual band route rather than a
common trace, an idealized time dilation, or an assumed projected path. -/
theorem project_edge {k s t R u v : ℕ} {xs ys : Fin k → ℕ → ℤ} {B : Finset ℕ}
    (ht : 1 ≤ t) (hx : ∀ h, IsWalk (xs h))
    (shadow : ∀ h w, w < alignedTime s t → |ys h w - xs h (sourceClock s t w)| ≤ R)
    (he : DepStep ys (alignedTime s t) u v)
    (hu : u ∉ projectionGuard s t xs ys R B) (hv : v ∉ projectionGuard s t xs ys R B) :
    Route xs t B (sourceClock s t u) (sourceClock s t v) := by
  have hut := (depStep_lt he).2
  have hvut := (depStep_lt he).1
  have hvt := hvut.trans hut
  have hqu := projected_endpoint_avoids hut hu
  have hqv := projected_endpoint_avoids hvt hv
  have hquT := sourceClock_lt (s := s) ht u
  have hquv := sourceClock_mono s t hvut.le
  rcases he with ⟨hedge, _⟩ | he
  · apply spine_route hquv hquT
    intro r hlo hhi hrB
    exact hu (mem_union_left _ (state_interval_in_batchGuard hut hedge hrB hlo hhi))
  · obtain ⟨e, he, hpair⟩ := mem_image.mp he
    rcases e with ⟨h, p, w⟩
    change (p, w) = (v, u) at hpair
    obtain ⟨hp, hw⟩ := Prod.mk.inj hpair
    subst p
    subst w
    have hop : IsHop (ys h) (alignedTime s t) v u := mem_allHops.mp he
    let z := ys h u
    have huBand : z - R ≤ xs h (sourceClock s t u) ∧ xs h (sourceClock s t u) ≤ z + R := by
      have hh := abs_le.mp (shadow h u hut)
      dsimp only [z]
      omega
    have hvBand : z - R ≤ xs h (sourceClock s t v) ∧ xs h (sourceClock s t v) ≤ z + R := by
      have hh := shadow h v hvt
      rw [← hop.2.2.1] at hh
      have hh' := abs_le.mp hh
      dsimp only [z]
      omega
    obtain ⟨ρ, hρ, hlast, hband⟩ := exists_band_path h (hx h)
      (sourceClock s t v) (sourceClock s t u) hquv hquT hvBand huBand
    refine ⟨ρ, hρ, hlast, ?_⟩
    intro r hr hrB
    obtain ⟨hlo, hhi, hpos⟩ := hband r hr
    by_cases heu : r = sourceClock s t u
    · exact hqu (heu ▸ hrB)
    by_cases hev : r = sourceClock s t v
    · exact hqv (hev ▸ hrB)
    have hcell : |ys h u - xs h r| ≤ (R : ℤ) := by
      apply abs_le.mpr
      dsimp only [z] at hpos
      omega
    exact hu (mem_union_right _ (mem_hopGuard h hop hrB (by omega) (by omega) hcell))

/-- Concatenation projects every surviving dependency path, preserving its
actual two endpoints even when the projected route has zero edges. -/
theorem project_path {k s t R : ℕ} {xs ys : Fin k → ℕ → ℤ} {B : Finset ℕ}
    (ht : 1 ≤ t) (hx : ∀ h, IsWalk (xs h))
    (shadow : ∀ h w, w < alignedTime s t → |ys h w - xs h (sourceClock s t w)| ≤ R)
    (u : ℕ) (ρ : List ℕ) (hu : u < alignedTime s t)
    (hpath : IsDepPath ys (alignedTime s t) (u :: ρ))
    (hgood : ∀ v ∈ u :: ρ, v ∉ projectionGuard s t xs ys R B) :
    Route xs t B (sourceClock s t u) (sourceClock s t ((u :: ρ).getLastD u)) := by
  induction ρ generalizing u with
  | nil => exact Route.refl (projected_endpoint_avoids hu (hgood u (by simp)))
  | cons v ρ ih =>
    have hv : v < alignedTime s t := (depStep_lt hpath.1).1.trans hu
    have hedge := project_edge ht hx shadow hpath.1 (hgood u (by simp)) (hgood v (by simp))
    have htail := ih v hv hpath.2 (fun r hr => hgood r (List.mem_cons_of_mem _ hr))
    simpa only [List.getLastD_cons] using hedge.trans htail

end AdaptiveTransfer.TransferGuards
