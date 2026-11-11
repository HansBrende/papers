import AdaptiveTransfer.PersistenceFutureRates
import AdaptiveTransfer.SourceEscapeRates
import AdaptiveTransfer.NativeReturnCounting

/-! Uniform timely sources reduce remote persistence to the explicit native
future-catalogue thin-set bound. The source lower bound supplies nonemptiness;
normalized counting and the exponential separation derive the half-mass
escape event. The native source catalogue/eraser theorem is not asserted.
-/

namespace AdaptiveTransfer.PersistenceFutureSource

open Transpose Transpose.Tape MergeDepth LeanMachine Finset
open PersistenceRates PersistenceFutureRates FiniteSourceEscape
open scoped BigOperators
attribute [local instance] Classical.propDecidable

noncomputable def stop {d b : ℕ} (M : TM)
    (S : Finset (Fin (d * d * b) → Bool)) (X : S) : ℕ :=
  (trace M (List.ofFn X.val)).haltTime

noncomputable def catalogue {d b : ℕ} (M : TM)
    (S : Finset (Fin (d * d * b) → Bool)) (A : ℕ) (h₀ C : ℝ) (t : ℕ) (h : Fin M.k) :
    Finset (ℤ → Fin (M.g + 1)) :=
  PersistenceFutureCatalogues.wordCatalogue M (fun X : S => List.ofFn X.val) (stop M S)
    weight (returnTime (d * d * b) C) (topSize (alpha h₀) (d * d * b))
    (radius (beta h₀ A) (d * d * b)) t h

noncomputable def outside {d b : ℕ} (M : TM)
    (S : Finset (Fin (d * d * b) → Bool)) (A : ℕ) (h₀ C : ℝ) (X : S) (t : ℕ) :
    Finset (Fin M.k) :=
  univ.filter fun h => PersistenceFuture.word M (List.ofFn X.val) (stop M S X) t h ∉
    catalogue M S A h₀ C t h

noncomputable def thinSource {d b : ℕ} (M : TM)
    (S : Finset (Fin (d * d * b) → Bool)) (A : ℕ) (h₀ C : ℝ) : Finset S :=
  FiniteSourceEscape.thin (stop M S) (outside M S A h₀ C)

theorem catalogue_card_bound {d b : ℕ} (M : TM)
    (S : Finset (Fin (d * d * b) → Bool)) (A : ℕ) (h₀ C : ℝ)
    (hA : M.g + 1 ≤ A) (t : ℕ) (h : Fin M.k) :
    (catalogue M S A h₀ C t h).card ≤ futureCatalogue h₀ A (d * d * b) :=
  word_catalogue_fits M (fun X : S => List.ofFn X.val) (stop M S) weight h₀ A
    (returnTime (d * d * b) C) (d * d * b) t hA h

/-- Timely native correctness fixes the same first halt used in every
future-readable word; the halt-test tuple is not a successful read. -/
theorem timely_haltsAt {M : TM} {d b : ℕ} {C : ℝ} {X : Fin (d * d * b) → Bool}
    (htr : TransposesInput M d b C X) :
    HaltsAt M (List.ofFn X) (trace M (List.ofFn X)).haltTime := by
  obtain ⟨t, _ht, hhalt⟩ := htr.halts
  have hh := (haltsAt_iff_trace t).mp hhalt
  exact (haltsAt_iff_trace _).mpr ((trace M (List.ofFn X)).haltsAt_haltTime ⟨t, hh.2⟩)

/-- The full uniform-source consequence, with exactly the native thin-set
cardinality estimate left explicit. There is no assumed nonempty source,
normalized law, half-mass escape event, or interval/entropy certificate.
The thin-set exponent has no extra multiplicative factor (`κ=0`). -/
theorem of_thin_source_bound (k A : ℕ) {h₀ C e : ℝ}
    (hk : 2 ≤ k) (hA : 1 ≤ A) (hh : 0 < h₀) (hC : 0 ≤ C) (he : 0 < e) :
    ∃ d₀ : ℕ, ∀ d, d₀ ≤ d → ∀ b, 1 ≤ b → ∀ M : TM, M.k = k → M.g + 1 ≤ A →
      ∀ S : Finset (Fin (d * d * b) → Bool),
        (∀ X ∈ S, TransposesInput M d b C X) →
        (2 : ℝ) ^ ((1 - e / 2) * (d * d * b : ℕ)) ≤ S.card →
        ((thinSource M S A h₀ C).card : ℝ) ≤ (2 : ℝ) ^ ((1 - e) * (d * d * b : ℕ)) →
        (⌈Real.logb 2 (futureCatalogue h₀ A (d * d * b))⌉₊ : ℝ) ≤ h₀ * (d * d * b : ℕ) ∧
        (∀ t h, (catalogue M S A h₀ C t h).card ≤ futureCatalogue h₀ A (d * d * b)) ∧
        beta h₀ A * (d * d * b : ℕ) / 4 ≤ intervalLength (beta h₀ A) (d * d * b) ∧
        Information M (fun X : S => List.ofFn X.val) (stop M S) weight univ
          (returnTime (d * d * b) C) (radius (beta h₀ A) (d * d * b)) 2
          (remoteRadius (alpha h₀) A (d * d * b)) (selectionMass k 2 C (beta h₀ A))
          ((2 : ℝ) ^ (-alpha h₀ * (d * d * b : ℕ) / 2)) := by
  obtain ⟨d₁, hrate⟩ := of_half_mass_escapes_all_widths.{0} hh hA hC hk
  obtain ⟨d₂, hgap⟩ := source_exponent_gap_all_widths he 0
  refine ⟨max d₁ d₂, ?_⟩
  intro d hd b hb M hMk hMA S correct hsource hbad
  have hScard : 0 < S.card := by
    have hpos : (0 : ℝ) < S.card :=
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).trans_le hsource
    exact_mod_cast hpos
  obtain ⟨X₀, hX₀⟩ := card_pos.mp hScard
  let : Nonempty S := ⟨⟨X₀, hX₀⟩⟩
  let P := d * d * b
  let T := returnTime P C
  have hT : (T : ℝ) ≤ C * (P + 1) := Nat.floor_le (by positivity)
  have hgap' : (0 : ℝ) + 1 ≤ e * P / 2 :=
    hgap d ((le_max_right _ _).trans hd) b hb
  have hsource' : (2 : ℝ) ^ ((1 - e / 2) * P) ≤ Fintype.card S := by
    simpa only [Fintype.card_coe] using hsource
  obtain ⟨B, hB, hpair⟩ := half_mass_pair_escape (stop M S) (outside M S A h₀ C)
    hgap' hsource' (show ((FiniteSourceEscape.thin (stop M S) (outside M S A h₀ C)).card : ℝ) ≤
      (2 : ℝ) ^ (0 + (1 - e) * P) by simpa only [zero_add, thinSource] using hbad)
  have hescape : ∀ X ∈ B, ∃ t ≤ stop M S X, ∃ H : Finset (Fin M.k), H.card = 2 ∧
      ∀ h ∈ H, PersistenceFuture.word M (List.ofFn X.val) (stop M S X) t h ∉
        PersistenceFutureCatalogues.wordCatalogue M (fun Y : S => List.ofFn Y.val) (stop M S)
          weight T (topSize (alpha h₀) P) (radius (beta h₀ A) P) t h := by
    intro X hX
    obtain ⟨t, ht, H, hH, hsub⟩ := hpair X hX
    refine ⟨t, ht, H, hH, ?_⟩
    intro h hh'
    exact (mem_filter.mp (hsub hh')).2
  obtain ⟨hbits, hlen, hinfo⟩ := hrate d ((le_max_left _ _).trans hd) b hb T hT
  have hresult := hinfo M hMk hMA S (fun X : S => List.ofFn X.val) (stop M S) weight
    (fun X => (weight_pos X).le) weight_sum B hB
    (fun X _ => (timely_native_data (correct X.val X.property)).1)
    (fun X _ => timely_haltsAt (correct X.val X.property)) hescape
  refine ⟨hbits, fun t h => catalogue_card_bound M S A h₀ C hMA t h, hlen, ?_⟩
  obtain ⟨H, hH, j, hj, E, _hEB, hmass, hlive, hwhole, hremote, hreturn⟩ := hresult
  exact ⟨H, hH, j, hj, E, subset_univ _, hmass, hlive, hwhole, hremote, hreturn⟩

end AdaptiveTransfer.PersistenceFutureSource
