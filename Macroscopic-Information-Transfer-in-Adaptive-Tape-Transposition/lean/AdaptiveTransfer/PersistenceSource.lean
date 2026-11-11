import AdaptiveTransfer.ConditionalPersistence
import AdaptiveTransfer.SourceEscapeRates

/-! The complete conditional-persistence consequence of the native
catalogue counting theorem, kept as an explicit cardinality hypothesis.
Its factor two is retained. All source selection and asymptotic steps
after that theorem are checked here. -/

namespace AdaptiveTransfer.ConditionalPersistence

open Transpose Transpose.Tape MergeDepth LeanMachine Finset
open PersistenceRates FiniteSourceEscape
attribute [local instance] Classical.propDecidable

noncomputable def outside {d b : ℕ} (M : TM)
    (S : Finset (Fin (d*d*b) → Bool)) (A : ℕ) (h₀ C : ℝ) (X : S) (t : ℕ) :
    Finset (Fin M.k) :=
  univ.filter (fun h => (run M (List.ofFn X.val) t).work h ∉
    wordCatalogue M (fun Y : S => List.ofFn Y.val) weight (returnTime (d*d*b) C)
      (topSize (alpha h₀) (d*d*b)) (radius (beta h₀ A) (d*d*b)) h t (priorWord M S t X))

noncomputable def thinSource {d b : ℕ} (M : TM)
    (S : Finset (Fin (d*d*b) → Bool)) (A : ℕ) (h₀ C : ℝ) : Finset S :=
  thin (fun X : S => (trace M (List.ofFn X.val)).haltTime) (outside M S A h₀ C)

/-- One threshold precedes the width, native machine and source. The sole
unformalized ingredient is the displayed small-cardinality bound for the
actual thin source, with exactly the catalogue theorem's factor two. -/
theorem of_small_thin_source (k A : ℕ) {h₀ C η : ℝ}
    (hk : 2 ≤ k) (hA : 1 ≤ A) (hh : 0 < h₀) (hC : 0 ≤ C) (hη : 0 < η) :
    ∃ d₀ : ℕ, ∀ d, d₀ ≤ d → ∀ b, 1 ≤ b → ∀ M : TM, M.k = k →
      ∀ S : Finset (Fin (d*d*b) → Bool), (∀ X ∈ S, TransposesInput M d b C X) →
      (2 : ℝ) ^ ((1 - η / 2) * (d*d*b : ℕ)) ≤ S.card →
      ((thinSource M S A h₀ C).card : ℝ) ≤
        (2 : ℝ) ^ (1 + (1 - η) * (d*d*b : ℕ)) →
      Nonempty (Witness M d b A h₀ C S weight) := by
  obtain ⟨d₁, hinfo⟩ := of_half_mass_escapes k A hk hA hh hC
  obtain ⟨d₂, hgap⟩ := source_exponent_gap_all_widths hη 1
  refine ⟨max d₁ d₂, ?_⟩
  intro d hd b hb M hMk S hcorrect hsource hbad
  have hcard : 0 < S.card := by
    have hpos := (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2)
      ((1 - η / 2) * (d*d*b : ℕ))).trans_le hsource
    exact_mod_cast hpos
  let : Nonempty S := (card_pos.mp hcard).coe_sort
  have hs : (2 : ℝ) ^ ((1 - η / 2) * (d*d*b : ℕ)) ≤ Fintype.card S := by
    simpa only [Fintype.card_coe] using hsource
  obtain ⟨B, hB, hesc⟩ := half_mass_pair_escape
    (fun X : S => (trace M (List.ofFn X.val)).haltTime) (outside M S A h₀ C)
    (hgap d ((le_max_right _ _).trans hd) b hb) hs hbad
  obtain ⟨result, _⟩ := hinfo d ((le_max_left _ _).trans hd) b hb M hMk S hcorrect
    weight weight_pos weight_sum B hB (by
      intro X hX
      obtain ⟨t, ht, H, hH, hsub⟩ := hesc X hX
      refine ⟨t, ht, H, hH, ?_⟩
      intro h hh
      exact (mem_filter.mp (hsub hh)).2)
  exact ⟨result⟩

end AdaptiveTransfer.ConditionalPersistence
