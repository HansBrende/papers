import AdaptiveTransfer.NativeSlabCutEvent
import AdaptiveTransfer.LocalSnapshots

/-! The good-event meaning of the localized count: every actual valid chunk
has an original cut larger than the chosen density, for all smaller excursion
thresholds simultaneously. The demanded set has the stated size bounds. -/

namespace AdaptiveTransfer
open Transpose MergeDepth BoundedNesting NativeRelations Finset

/-- The finite geometric margin is at least P/(8N) uniformly for b>=1. -/
theorem slabSaving_lower_bound {d b a : ℕ} {c : ℝ}
    (hd : 1 ≤ d) (hb : 1 ≤ b)
    (hdN : 48 * (slabRunCap a c) ^ 2 ≤ d) (hda : 16 * slabRunCap a c * a ≤ d) :
    (d * d * b : ℕ) / (8 * (slabRunCap a c : ℝ)) ≤ slabSaving d b a c := by
  let N := slabRunCap a c
  let P := d * d * b
  have hN : 1 ≤ N := by dsimp [N, slabRunCap]; omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hdP : d ≤ P := by dsimp [P]; nlinarith
  have hgeom : 3 * (N : ℝ) * d * b ≤ (P : ℝ) / (16 * (N : ℝ)) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 16 * (N : ℝ))).mpr
    have hh : 48 * (N : ℝ) ^ 2 ≤ d := by exact_mod_cast hdN
    have hh' := mul_le_mul_of_nonneg_right hh (show 0 ≤ (d : ℝ) * b by positivity)
    dsimp [P]
    push_cast
    nlinarith
  have ha : (a : ℝ) ≤ (P : ℝ) / (16 * (N : ℝ)) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 16 * (N : ℝ))).mpr
    have hh : 16 * (N : ℝ) * a ≤ P := by exact_mod_cast hda.trans hdP
    nlinarith
  change (P : ℝ) / (8 * (N : ℝ)) ≤ (P : ℝ) / (4 * (N : ℝ)) - 3 * (N : ℝ) * d * b - a
  ring_nf at hgeom ha ⊢
  linarith

namespace NativeValidSlab
variable {M : TM} {d b a : ℕ} {c : ℝ} {X : Fin (d * d * b) → Bool}

theorem omitted_card_upper (g : NativeValidSlab M d b a c X)
    (hcorrect : TransposesInput M d b c X) :
    (g.obs.omittedGeometry (tposOf d b)).card ≤ (d * d * b) / 2 := by
  classical
  let τ := trace M (List.ofFn X)
  have hlen := (fibre_haltTime (mem_fibre.mpr rfl) hcorrect).2
  change (appendList τ τ.haltTime).length = d * d * b at hlen
  rw [g.obs.omittedGeometry_eq_literal g.finish_le hlen.ge]
  have hinj : Function.Injective (fun j : Fin (d * d * b) => appendTime τ τ.haltTime j.val) := by
    intro i j he
    apply Fin.ext
    exact (appendTime_strictMonoOn τ τ.haltTime).injOn
      (by simpa only [Set.mem_Iio, hlen] using i.isLt)
      (by simpa only [Set.mem_Iio, hlen] using j.isLt) he
  have hout : (outIn (fun j : Fin (d * d * b) => appendTime τ τ.haltTime j.val) g.obs.times).card ≤
      g.obs.times.card := by
    apply card_le_card_of_injOn (fun j => appendTime τ τ.haltTime j.val)
    · intro j hj
      exact (mem_filter.mp hj).2
    · exact hinj.injOn
  exact (card_le_card sdiff_subset).trans ((card_image_le).trans (hout.trans g.half))

theorem omitted_card_lower (g : NativeValidSlab M d b a c X)
    (hs : (d * d * b : ℕ) / (8 * (slabRunCap a c : ℝ)) ≤ slabSaving d b a c) :
    (d * d * b : ℕ) / (8 * (slabRunCap a c : ℝ)) ≤
      ((g.obs.omittedGeometry (tposOf d b)).card : ℝ) := by
  have hcost : 0 ≤ (a : ℝ) *
      (if g.obs.start = 0 then 0 else (slabWidth (d * d * b) a c : ℝ)) := by
    split_ifs <;> positivity
  have hh := g.margin
  linarith

end NativeValidSlab

/-- Lowering the excursion threshold only adds original long-return targets. -/
theorem offCarrierLowerEndpoints_anti {k : ℕ} (xs : Fin k → ℕ → ℤ)
    (f : Fin k) (T : ℕ) {H H' : ℕ} (hH : H' ≤ H) :
    offCarrierLowerEndpoints xs f T H ⊆ offCarrierLowerEndpoints xs f T H' := by
  apply image_subset_image
  intro e he
  simp only [offCarrierReturns, mem_filter] at he ⊢
  obtain ⟨u, hu, hfar⟩ := he.2.2
  exact ⟨he.1, he.2.1, u, hu, lt_of_le_of_lt hH hfar⟩

/-- Outside the one bad event, EVERY valid actual chunk has a large original
separator, even at every smaller nonnegative integer excursion threshold. -/
theorem native_good_slab_cuts {M : TM} {d b a H : ℕ} {c lam : ℝ}
    {X : Fin (d * d * b) → Bool} (hcorrect : TransposesInput M d b c X)
    (hgood : X ∉ nativeBadSlabCuts M d b a c H ⌊lam * (d * d * b : ℕ)⌋₊)
    (g : NativeValidSlab M d b a c X) {H' : ℕ} (hH : H' ≤ H)
    (B : Finset ℕ) (hB : ∀ t ∈ B, t < (trace M (List.ofFn X)).haltTime)
    (hsep : IsMengerVertexCut (trace M (List.ofFn X)).work (trace M (List.ofFn X)).haltTime
      (nativeDemandedOutputSteps M X (trace M (List.ofFn X)).haltTime (tposOf d b)
        (g.obs.omittedGeometry (tposOf d b)))
      (offCarrierLowerEndpoints (trace M (List.ofFn X)).work g.obs.free
        (trace M (List.ofFn X)).haltTime H') B) :
    lam * (d * d * b : ℕ) < (B.card : ℝ) := by
  classical
  by_contra hn
  have hb : B.card ≤ ⌊lam * (d * d * b : ℕ)⌋₊ := Nat.le_floor (le_of_not_gt hn)
  apply hgood
  apply mem_filter.mpr
  refine ⟨mem_univ _, hcorrect, ⟨g, B, hB, ?_⟩, hb⟩
  intro ρ r hr hp ht
  exact hsep ρ r hr hp (offCarrierLowerEndpoints_anti _ _ _ hH ht)

end AdaptiveTransfer
