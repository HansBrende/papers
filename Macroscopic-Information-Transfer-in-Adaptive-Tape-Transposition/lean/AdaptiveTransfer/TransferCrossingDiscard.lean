import AdaptiveTransfer.TransferCrossingAssignments

/-! Literal discarded crossing targets are injected into a finite label
space. Reversing the two distinct epoch indices encodes which overlap strip
was used, without charging an extra factor of two. -/

namespace AdaptiveTransfer.TransferCrossing
open Finset BoundedNesting NativeRelations MergeDepth
attribute [local instance] Classical.propDecidable

/-- The full frame is chosen from the proved existence theorem on the actual
crossing-lower set. There is no supplied assignment or multiplicity bound. -/
noncomputable def chosenFrame {y : ℕ → ℤ} (hy : IsWalk y) (hy0 : y 0 = 0)
    {U H : ℕ} (hH : 1 ≤ H) (v : ↥(tapeCrossingLowers y U H)) : CrossingFrame y U H v.val :=
  Classical.choice (crossing_frame_exists hy hy0 hH v.property)

def NearBoundary {y : ℕ → ℤ} {U H v : ℕ} (F : CrossingFrame y U H v) (w : ℕ) : Prop :=
  signed y F.sign v - overlapLow y U H F.sign F.firstEpoch F.secondEpoch ≤ w ∨
    overlapHigh y U H F.sign F.firstEpoch F.secondEpoch - signed y F.sign v ≤ w

abbrev DiscardLabel (K w : ℕ) := Bool × Bool × Fin K × Fin K × Fin (w + 1)

/-- Low-strip labels list the epochs in increasing order; high-strip labels
reverse them. Their strict order makes the two cases disjoint. -/
noncomputable def discardLabel {y : ℕ → ℤ} {U H v K w : ℕ}
    (F : CrossingFrame y U H v) (hK : (tapeSkeleton y U H).length + 1 ≤ K)
    (hF : NearBoundary F w) : DiscardLabel K w :=
  if hl : signed y F.sign v - overlapLow y U H F.sign F.firstEpoch F.secondEpoch ≤ w then
    (F.sign, F.second, ⟨F.firstEpoch, by have := F.epoch_order; have := F.epoch_bound; omega⟩,
      ⟨F.secondEpoch, by have := F.epoch_bound; omega⟩,
      ⟨(signed y F.sign v - overlapLow y U H F.sign F.firstEpoch F.secondEpoch).toNat, by omega⟩)
  else
    (F.sign, F.second, ⟨F.secondEpoch, by have := F.epoch_bound; omega⟩,
      ⟨F.firstEpoch, by have := F.epoch_order; have := F.epoch_bound; omega⟩,
      ⟨(overlapHigh y U H F.sign F.firstEpoch F.secondEpoch - signed y F.sign v).toNat, by
        have hh := hF.resolve_left hl
        omega⟩)

/-- Two actual consecutive-return hops at one base cannot both contain the
same canonical extremizer. -/
theorem frame_target_unique {y : ℕ → ℤ} {U H v v' : ℕ}
    (F : CrossingFrame y U H v) (G : CrossingFrame y U H v')
    (hs : F.sign = G.sign) (hr : F.second = G.second)
    (h₁ : F.firstEpoch = G.firstEpoch) (h₂ : F.secondEpoch = G.secondEpoch)
    (hz : signed y F.sign v = signed y G.sign v') : v = v' := by
  have hc : y v = y v' := by
    rw [hs] at hz
    cases hsign : G.sign <;> simpa only [signed, hsign, Bool.false_eq_true, ↓reduceIte,
      neg_inj] using hz
  have ht : (if F.second then epochMin y U H F.sign F.secondEpoch else epochMax y U H F.sign F.firstEpoch) =
      (if G.second then epochMin y U H G.sign G.secondEpoch else epochMax y U H G.sign G.firstEpoch) := by
    rw [hs, hr, h₁, h₂]
  have hg := G.inside
  rw [← ht] at hg
  exact (hop_unique F.hop G.hop hc ⟨F.inside.1, F.inside.2.le⟩ ⟨hg.1, hg.2.le⟩).1

/-- The finite label determines the literal target vertex. -/
theorem discardLabel_target_unique {y : ℕ → ℤ} {U H v v' K w : ℕ}
    (F : CrossingFrame y U H v) (G : CrossingFrame y U H v')
    (hK : (tapeSkeleton y U H).length + 1 ≤ K)
    (hF : NearBoundary F w) (hG : NearBoundary G w)
    (he : discardLabel F hK hF = discardLabel G hK hG) : v = v' := by
  have hFs := F.level
  have hGs := G.level
  have hFo := F.epoch_order
  have hGo := G.epoch_order
  by_cases hf : signed y F.sign v - overlapLow y U H F.sign F.firstEpoch F.secondEpoch ≤ w
  · by_cases hg : signed y G.sign v' - overlapLow y U H G.sign G.firstEpoch G.secondEpoch ≤ w
    · simp only [discardLabel, dite_eq_left hf, dite_eq_left hg, Prod.mk.injEq, Fin.mk.injEq] at he
      obtain ⟨hs, hr, h₁, h₂, hz⟩ := he
      apply frame_target_unique F G hs hr h₁ h₂
      rw [hs, h₁, h₂] at hFs hz
      rw [hs]
      omega
    · simp only [discardLabel, dite_eq_left hf, dite_eq_right hg, Prod.mk.injEq, Fin.mk.injEq] at he
      obtain ⟨_, _, h₁, h₂, _⟩ := he
      omega
  · by_cases hg : signed y G.sign v' - overlapLow y U H G.sign G.firstEpoch G.secondEpoch ≤ w
    · simp only [discardLabel, dite_eq_right hf, dite_eq_left hg, Prod.mk.injEq, Fin.mk.injEq] at he
      obtain ⟨_, _, h₁, h₂, _⟩ := he
      omega
    · simp only [discardLabel, dite_eq_right hf, dite_eq_right hg, Prod.mk.injEq, Fin.mk.injEq] at he
      obtain ⟨hs, hr, h₂, h₁, hz⟩ := he
      apply frame_target_unique F G hs hr h₁ h₂
      rw [hs, h₁, h₂] at hFs hz
      rw [hs]
      omega

noncomputable def badTargets {y : ℕ → ℤ} (hy : IsWalk y) (hy0 : y 0 = 0)
    {U H : ℕ} (hH : 1 ≤ H) (w : ℕ) : Finset ↥(tapeCrossingLowers y U H) :=
  univ.filter fun v => NearBoundary (chosenFrame hy hy0 hH v) w

noncomputable def discardedLowers {y : ℕ → ℤ} (hy : IsWalk y) (hy0 : y 0 = 0)
    {U H : ℕ} (hH : 1 ≤ H) (w : ℕ) : Finset ℕ :=
  (badTargets hy hy0 (U := U) hH w).image Subtype.val

theorem badTargets_card_le {y : ℕ → ℤ} (hy : IsWalk y) (hy0 : y 0 = 0)
    {U H K : ℕ} (hH : 1 ≤ H) (hK : (tapeSkeleton y U H).length + 1 ≤ K) (w : ℕ) :
    (badTargets hy hy0 (U := U) hH w).card ≤ 4 * K ^ 2 * (w + 1) := by
  let enc (v : ↥(badTargets hy hy0 (U := U) hH w)) : DiscardLabel K w :=
    discardLabel (chosenFrame hy hy0 hH v.val) hK (mem_filter.mp v.property).2
  have hinj : Function.Injective enc := by
    intro v v' hh
    apply Subtype.ext
    apply Subtype.ext
    exact discardLabel_target_unique _ _ hK _ _ hh
  have hc := Fintype.card_le_of_injective enc hinj
  simp only [Fintype.card_coe, DiscardLabel, Fintype.card_prod, Fintype.card_bool,
    Fintype.card_fin] at hc
  exact hc.trans_eq (by ring)

theorem discardedLowers_card_le {y : ℕ → ℤ} (hy : IsWalk y) (hy0 : y 0 = 0)
    {U H K : ℕ} (hH : 1 ≤ H) (hK : (tapeSkeleton y U H).length + 1 ≤ K) (w : ℕ) :
    (discardedLowers hy hy0 (U := U) hH w).card ≤ 4 * K ^ 2 * (w + 1) :=
  card_image_le.trans (badTargets_card_le hy hy0 hH hK w)

theorem discardedLowers_subset {y : ℕ → ℤ} (hy : IsWalk y) (hy0 : y 0 = 0)
    {U H : ℕ} (hH : 1 ≤ H) (w : ℕ) :
    discardedLowers hy hy0 (U := U) hH w ⊆ tapeCrossingLowers y U H := by
  intro v hv
  obtain ⟨u, _, rfl⟩ := mem_image.mp hv
  exact u.property

/-- Every surviving actual target has both strict overlap margins. -/
theorem surviving_margins {y : ℕ → ℤ} (hy : IsWalk y) (hy0 : y 0 = 0)
    {U H v : ℕ} (hH : 1 ≤ H) (w : ℕ) (hv : v ∈ tapeCrossingLowers y U H)
    (hgood : v ∉ discardedLowers hy hy0 (U := U) hH w) :
    let F := chosenFrame hy hy0 hH ⟨v,hv⟩
    (w : ℤ) < signed y F.sign v - overlapLow y U H F.sign F.firstEpoch F.secondEpoch ∧
      (w : ℤ) < overlapHigh y U H F.sign F.firstEpoch F.secondEpoch - signed y F.sign v := by
  have hn : ¬ NearBoundary (chosenFrame hy hy0 hH ⟨v,hv⟩) w := by
    intro hh
    exact hgood (mem_image.mpr ⟨⟨v,hv⟩, mem_filter.mpr ⟨mem_univ _, hh⟩, rfl⟩)
  exact ⟨lt_of_not_ge (fun h => hn (Or.inl h)), lt_of_not_ge (fun h => hn (Or.inr h))⟩

noncomputable def globalDiscarded {k : ℕ} (ys : Fin k → ℕ → ℤ)
    (hy : ∀ j, IsWalk (ys j)) (hy0 : ∀ j, ys j 0 = 0)
    {U H : ℕ} (hH : 1 ≤ H) (w : ℕ) : Finset ℕ :=
  univ.biUnion fun j => discardedLowers (hy j) (hy0 j) (U := U) hH w

theorem globalDiscarded_card_le {k : ℕ} (ys : Fin k → ℕ → ℤ)
    (hy : ∀ j, IsWalk (ys j)) (hy0 : ∀ j, ys j 0 = 0)
    {U H K : ℕ} (hH : 1 ≤ H)
    (hK : ∀ j, (tapeSkeleton (ys j) U H).length + 1 ≤ K) (w : ℕ) :
    (globalDiscarded ys hy hy0 (U := U) hH w).card ≤ 4 * k * K ^ 2 * (w + 1) := by
  calc
    _ ≤ ∑ j : Fin k, (discardedLowers (hy j) (hy0 j) (U := U) hH w).card := card_biUnion_le
    _ ≤ ∑ _j : Fin k, 4 * K ^ 2 * (w + 1) :=
      sum_le_sum fun j _ => discardedLowers_card_le (hy j) (hy0 j) hH (hK j) w
    _ = _ := by simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]; ring

theorem head_not_discarded {k U H v w : ℕ} {ys : Fin k → ℕ → ℤ}
    {hy : ∀ j, IsWalk (ys j)} {hy0 : ∀ j, ys j 0 = 0} {hH : 1 ≤ H}
    (hgood : v ∉ globalDiscarded ys hy hy0 (U := U) hH w) (j : Fin k) :
    v ∉ discardedLowers (hy j) (hy0 j) (U := U) hH w := by
  intro hv
  exact hgood (mem_biUnion.mpr ⟨j, mem_univ _, hv⟩)

theorem globalDiscarded_live {k : ℕ} (ys : Fin k → ℕ → ℤ)
    (hy : ∀ j, IsWalk (ys j)) (hy0 : ∀ j, ys j 0 = 0)
    {U H : ℕ} (hH : 1 ≤ H) (w : ℕ) :
    ∀ v ∈ globalDiscarded ys hy hy0 (U := U) hH w, v < U := by
  intro v hv
  obtain ⟨j, _, hj⟩ := mem_biUnion.mp hv
  exact mem_range.mp (mem_filter.mp (discardedLowers_subset (hy j) (hy0 j) hH w hj)).1

/-- At an actual multi-tape crossing lower endpoint outside the global
discard, one participating tape supplies the constructed strict-margin frame. -/
theorem surviving_crossing_frame {k U H v w : ℕ} (τ : Trace k) (hH : 1 ≤ H)
    (hv : v ∈ crossingLowerEtaSteps τ U H 1 U)
    (hgood : v ∉ globalDiscarded τ.work τ.work_isWalk τ.work_zero (U := U) hH w) :
    ∃ j : Fin k, ∃ hj : v ∈ tapeCrossingLowers (τ.work j) U H,
      let F := chosenFrame (τ.work_isWalk j) (τ.work_zero j) hH ⟨v,hj⟩
      v < U ∧
      (w : ℤ) < signed (τ.work j) F.sign v - overlapLow (τ.work j) U H F.sign F.firstEpoch F.secondEpoch ∧
      (w : ℤ) < overlapHigh (τ.work j) U H F.sign F.firstEpoch F.secondEpoch - signed (τ.work j) F.sign v := by
  rw [crossingLowerEtaSteps_eq_biUnion_tapeCrossingLowers] at hv
  obtain ⟨j, _, hj⟩ := mem_biUnion.mp hv
  refine ⟨j, hj, mem_range.mp (mem_filter.mp hj).1, ?_⟩
  exact surviving_margins (τ.work_isWalk j) (τ.work_zero j) hH w hj (head_not_discarded hgood j)

/-- Exact finite constant used in the native crossing-target lift. -/
theorem globalDiscarded_shadow_card_le {k : ℕ} (ys : Fin k → ℕ → ℤ)
    (hy : ∀ j, IsWalk (ys j)) (hy0 : ∀ j, ys j 0 = 0)
    {U H K : ℕ} (hH : 1 ≤ H)
    (hK : ∀ j, (tapeSkeleton (ys j) U H).length + 1 ≤ K) (h s : ℕ) :
    (globalDiscarded ys hy hy0 (U := U) hH (2 * h + 6 * s + 2)).card ≤
      4 * k * K ^ 2 * (2 * h + 6 * s + 3) := by
  simpa only [Nat.add_assoc] using globalDiscarded_card_le ys hy hy0 hH hK (2 * h + 6 * s + 2)

end AdaptiveTransfer.TransferCrossing
