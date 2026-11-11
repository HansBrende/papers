import AdaptiveTransfer.LocalCutTail
import AdaptiveTransfer.LocalCutGoodInputs

/-! The complete original off-carrier expansion endpoint. A single actual
bad-input event controls all valid chunks and all free heads. Its cuts are
endpoint-inclusive cuts of the original execution graph, and its targets
include long-return lowers outside the selected chunk. -/

namespace AdaptiveTransfer
open Transpose MergeDepth NativeRelations Finset

/-- Large original separators, simultaneously for every smaller excursion
threshold. The finset B consists of actual vertices of the complete run. -/
def OriginalCutExpansion (M : TM) {P : ℕ} (X : Fin P → Bool) (π : Fin P → Fin P)
    (f : Fin M.k) (U : Finset (Fin P)) (H : ℕ) (lam : ℝ) : Prop :=
  ∀ H' ≤ H, ∀ B : Finset ℕ, (∀ t ∈ B, t < (trace M (List.ofFn X)).haltTime) →
    IsMengerVertexCut (trace M (List.ofFn X)).work (trace M (List.ofFn X)).haltTime
      (nativeDemandedOutputSteps M X (trace M (List.ofFn X)).haltTime π U)
      (offCarrierLowerEndpoints (trace M (List.ofFn X)).work f
        (trace M (List.ofFn X)).haltTime H') B → lam * P < (B.card : ℝ)

/-- Theorem H, with explicit epsilon and eta and a dimension threshold uniform
in every b>=1. In addition to one demanded set for each free head, every valid
actual slab enjoys the same size and full original-cut conclusions. -/
theorem native_off_carrier_expansion (k a q : ℕ) {c : ℝ}
    (hk : 1 ≤ k) (ha : 1 ≤ a) (hc : 1 ≤ c) :
    let N := slabRunCap a c
    let eps := returnTailEpsilon k a N
    let eta := returnTailEta N
    0 < eps ∧ 0 < eta ∧ ∃ lam : ℝ, 0 < lam ∧ ∃ d₀ : ℕ,
      ∀ d, d₀ ≤ d → ∀ b, 1 ≤ b → ∀ M : TM,
        M.k = k → M.q + 1 ≤ 2 ^ q → M.g + 1 ≤ 2 ^ a →
        let P := d * d * b
        let H := ⌊eps * (P : ℝ)⌋₊
        let E := nativeBadSlabCuts M d b a c H ⌊lam * (P : ℝ)⌋₊
        (E.card : ℝ) < (2 : ℝ) ^ ((1 - eta) * P) ∧
        ∀ X : Fin P → Bool, TransposesInput M d b c X → X ∉ E →
          (∀ f : Fin M.k, ∃ U : Finset (Fin P),
            (P : ℝ) / (8 * (N : ℝ)) ≤ (U.card : ℝ) ∧ U.card ≤ P / 2 ∧
            OriginalCutExpansion M X (tposOf d b) f U H lam) ∧
          (∀ g : NativeValidSlab M d b a c X,
            let U := g.obs.omittedGeometry (tposOf d b)
            (P : ℝ) / (8 * (N : ℝ)) ≤ (U.card : ℝ) ∧ U.card ≤ P / 2 ∧
            OriginalCutExpansion M X (tposOf d b) g.obs.free U H lam) := by
  let N := slabRunCap a c
  have hN : 1 ≤ N := by dsimp [N, slabRunCap]; omega
  obtain ⟨lam, hlam, d₁, htail⟩ := native_local_cut_tail k a q hk ha hc
  refine ⟨returnTailEpsilon_pos ha hN, returnTailEta_pos hN,
    lam, hlam, d₁ + 2 + 48 * N ^ 2 + 16 * N * a, ?_⟩
  intro d hd b hb M hMk hq hA
  have hd₁ : d₁ ≤ d := by omega
  have hd2 : 2 ≤ d := by omega
  have hdN : 48 * N ^ 2 ≤ d := by omega
  have hda : 16 * N * a ≤ d := by omega
  let P := d * d * b
  let H := ⌊returnTailEpsilon k a N * (P : ℝ)⌋₊
  have hP : 2 ≤ P := by dsimp [P]; nlinarith
  have hs : (P : ℝ) / (8 * (N : ℝ)) ≤ slabSaving d b a c :=
    slabSaving_lower_bound (by omega) hb hdN hda
  have hsp : 0 < slabSaving d b a c := lt_of_lt_of_le (by positivity) hs
  refine ⟨htail d hd₁ b hb M hMk hq hA, ?_⟩
  intro X hcorrect hgood
  have hslab (g : NativeValidSlab M d b a c X) :
      (P : ℝ) / (8 * (N : ℝ)) ≤ ((g.obs.omittedGeometry (tposOf d b)).card : ℝ) ∧
      (g.obs.omittedGeometry (tposOf d b)).card ≤ P / 2 ∧
      OriginalCutExpansion M X (tposOf d b) g.obs.free
        (g.obs.omittedGeometry (tposOf d b)) H lam := by
    refine ⟨g.omitted_card_lower hs, g.omitted_card_upper hcorrect, ?_⟩
    intro H' hH B hB hsep
    exact native_good_slab_cuts hcorrect hgood g hH B hB hsep
  refine ⟨?_, hslab⟩
  intro f
  obtain ⟨g, hg⟩ := native_valid_slab_exists (by omega) hb hP ha hc hcorrect hsp f
  exact ⟨g.obs.omittedGeometry (tposOf d b), (hslab g).1, (hslab g).2.1,
    hg ▸ (hslab g).2.2⟩

end AdaptiveTransfer
