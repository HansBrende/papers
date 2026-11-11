import AdaptiveTransfer.PersistenceAtoms
import AdaptiveTransfer.PersistencePrefixSupport
import AdaptiveTransfer.PersistenceRates
import AdaptiveTransfer.NativeReturnCounting

/-! The complete ordinary conditional-persistence assembly. The source
catalogue theorem must still supply the literal escape event of mass at
least one half. From that event, this file derives one common native live
interval, retained law, whole-word atom bound and undelivered-bit bound. -/

namespace AdaptiveTransfer.ConditionalPersistence
open Transpose Transpose.Tape MergeDepth LeanMachine Finset
open PersistenceGraph PersistenceCatalogues PersistenceRates
open scoped BigOperators
attribute [local instance] Classical.propDecidable

noncomputable def wordCatalogue {Ω : Type*} [Fintype Ω] (M : TM)
    (input : Ω → List Bool) (w : Ω → ℝ) (T K R : ℕ)
    (h : Fin M.k) (t : ℕ) (y : List Bool) : Finset (ℤ → Fin (M.g + 1)) :=
  (PersistenceCatalogues.catalogue (nativeTop M input w T K h) t R y).image
    (fun v => extendWord (0 : Fin (M.g + 1)) T v.1)

theorem wordCatalogue_card {Ω : Type*} [Fintype Ω] (M : TM)
    (input : Ω → List Bool) (w : Ω → ℝ) (T K R : ℕ)
    (h : Fin M.k) (t : ℕ) (y : List Bool) :
    (wordCatalogue M input w T K R h t y).card ≤
      (R + 1) ^ 2 * K * (6 * (M.g + 1)) ^ (R + 1) :=
  card_image_le.trans (native_catalogue_card M input w T K R t h y)

theorem wordCatalogue_rate_bound {Ω : Type*} [Fintype Ω] (M : TM)
    (input : Ω → List Bool) (w : Ω → ℝ) (T P A : ℕ) (h₀ : ℝ)
    (hA : M.g + 1 ≤ A) (h : Fin M.k) (t : ℕ) (y : List Bool) :
    (wordCatalogue M input w T (topSize (alpha h₀) P)
      (radius (beta h₀ A) P) h t y).card ≤ PersistenceRates.catalogue h₀ A P := by
  apply (wordCatalogue_card M input w T _ _ h t y).trans
  unfold PersistenceRates.catalogue
  gcongr

theorem vertex_escape_of_word {Ω : Type*} [Fintype Ω] (M : TM)
    (input : Ω → List Bool) (w : Ω → ℝ) (T K R : ℕ)
    (h : Fin M.k) (t : ℕ) (y : List Bool) (X : Ω) (ht : t ≤ T)
    (hescape : (run M (input X) t).work h ∉ wordCatalogue M input w T K R h t y) :
    vertex M (input X) T t h ∉ PersistenceCatalogues.catalogue
      (nativeTop M input w T K h) t R y := by
  intro hv
  apply hescape
  have hw := mem_image_of_mem (fun v => extendWord (0 : Fin (M.g + 1)) T v.1) hv
  simpa only [wordCatalogue, extendWord_vertex M (input X) h ht] using hw

noncomputable def priorWord {d b : ℕ} (M : TM)
    (S : Finset (Fin (d*d*b) → Bool)) (t : ℕ) (X : S) : List Bool :=
  PrefixOutput.word (outBit M (List.ofFn X.val)) t

noncomputable def contextMass {Ω Z : Type*} [Fintype Ω]
    (w : Ω → ℝ) (D : Finset Ω) (context : Ω → Z) (z : Z) : ℝ :=
  ContextPruning.mass w (D ∩ ContextPruning.fibre context z)

noncomputable def conditionalAtom {Ω Z V : Type*} [Fintype Ω]
    (w : Ω → ℝ) (D : Finset Ω) (context : Ω → Z) (value : Ω → V) (z : Z) (v : V) : ℝ :=
  FiniteObservationTopSets.atom (fun x => if x ∈ D then w x else 0) context value z v /
    contextMass w D context z

noncomputable def wholeAtom {d b : ℕ} (M : TM)
    (S : Finset (Fin (d*d*b) → Bool)) (w : S → ℝ) (D : Finset S)
    (h : Fin M.k) (t : ℕ) (z : List Bool) (v : ℤ → Fin (M.g + 1)) : ℝ :=
  conditionalAtom w D (priorWord M S t)
    (fun X => (run M (List.ofFn X.val) t).work h) z v

structure Witness (M : TM) (d b A : ℕ) (h₀ C : ℝ)
    (S : Finset (Fin (d*d*b) → Bool)) (w : S → ℝ) where
  heads : Finset (Fin M.k)
  heads_card : heads.card = 2
  grid : ℕ
  retained : Finset S
  mass : selectionMass M.k 2 C (beta h₀ A) / 2 ≤ ContextPruning.mass w retained
  length : beta h₀ A * (d*d*b : ℕ) / 4 ≤
    (FiniteTimeGrid.interval (intervalLength (beta h₀ A) (d*d*b)) grid).card
  live : ∀ X ∈ retained, ∀ t ∈ FiniteTimeGrid.interval (intervalLength (beta h₀ A) (d*d*b)) grid,
    t < (trace M (List.ofFn X.val)).haltTime
  pending : ∀ X ∈ retained, ∀ t ∈ FiniteTimeGrid.interval (intervalLength (beta h₀ A) (d*d*b)) grid,
    alpha h₀ * (d*d*b : ℕ) ≤ (d*d*b : ℕ) - (priorWord M S t X).length
  atoms : ∀ h ∈ heads, ∀ t ∈ FiniteTimeGrid.interval (intervalLength (beta h₀ A) (d*d*b)) grid,
    ∀ z v, 0 < contextMass w retained (priorWord M S t) z →
      wholeAtom M S w retained h t z v ≤ (2 : ℝ) ^ (-alpha h₀ * (d*d*b : ℕ) / 2)

/-- One dimension threshold works for all positive widths, all native
tables with the fixed number of heads, and every positive finite source law.
The only unproved native input is the explicitly stated catalogue-escape
event. No entropy, common interval or retained law is assumed. -/
theorem of_half_mass_escapes (k A : ℕ) {h₀ C : ℝ}
    (hk : 2 ≤ k) (hA : 1 ≤ A) (hh : 0 < h₀) (hC : 0 ≤ C) :
    ∃ d₀ : ℕ, ∀ d, d₀ ≤ d → ∀ b, 1 ≤ b → ∀ M : TM, M.k = k →
      ∀ S : Finset (Fin (d*d*b) → Bool), (∀ X ∈ S, TransposesInput M d b C X) →
      ∀ w : S → ℝ, (∀ X, 0 < w X) → (∑ X, w X = 1) →
      ∀ B : Finset S, 1 / 2 ≤ ContextPruning.mass w B →
      (∀ X ∈ B, ∃ t ≤ (trace M (List.ofFn X.val)).haltTime,
        ∃ H : Finset (Fin M.k), H.card = 2 ∧ ∀ h ∈ H,
          (run M (List.ofFn X.val) t).work h ∉
            wordCatalogue M (fun Y : S => List.ofFn Y.val) w (returnTime (d*d*b) C)
              (topSize (alpha h₀) (d*d*b)) (radius (beta h₀ A) (d*d*b)) h t
              (priorWord M S t X)) →
      ∃ result : Witness M d b A h₀ C S w, result.retained ⊆ B := by
  obtain ⟨d₀, rates⟩ := persistence_rates_all_widths hh hA hC hk
  refine ⟨d₀, ?_⟩
  intro d hd b hb M hMk S correct w hw hprob B hB escapes
  let P := d*d*b
  let T := returnTime P C
  let K := topSize (alpha h₀) P
  let R := radius (beta h₀ A) P
  let stop (X : S) := (trace M (List.ofFn X.val)).haltTime
  have hT : (T : ℝ) ≤ C * ((P : ℝ) + 1) := Nat.floor_le (by positivity)
  obtain ⟨_hcat, hR, _hell, hlen, _hmenu, hrate⟩ := rates d hd b hb T hT
  have hstop (X : S) (_hX : X ∈ B) : stop X ≤ T :=
    (timely_native_data (correct X.val X.property)).1
  have hBp : 0 < ContextPruning.mass w B := by linarith
  have vertexEscapes (X : S) (hX : X ∈ B) :
      ∃ t ≤ stop X, ∃ H : Finset (Fin M.k), H.card = 2 ∧ ∀ h ∈ H,
        vertex M (List.ofFn X.val) T t h ∉ PersistenceCatalogues.catalogue
          (nativeTop M (fun Y : S => List.ofFn Y.val) w T K h) t R
            (priorWord M S t X) := by
    obtain ⟨t, ht, H, hH, he⟩ := escapes X hX
    exact ⟨t, ht, H, hH, fun h hh => vertex_escape_of_word M
      (fun Y : S => List.ofFn Y.val) w T K R h t (priorWord M S t X) X
      (ht.trans (hstop X hX)) (he h hh)⟩
  obtain ⟨H, hH, j, _hj, D, hDB, hmass, havoid, hatoms⟩ :=
    PersistenceSelection.exists_common_interval_atoms M (fun X : S => List.ofFn X.val)
      w (fun X => (hw X).le) hprob T K R 2 (topSize_pos _ _) hR stop B hBp hstop vertexEscapes
  obtain ⟨hretain, hsmall⟩ := hrate (ContextPruning.mass w B) hB
  rw [← hMk] at hretain hsmall
  have hHne : H.Nonempty := card_pos.mp (by omega)
  obtain ⟨head, hhead⟩ := hHne
  refine ⟨⟨H, hH, j, D, hretain.trans hmass, ?_, ?_, ?_, ?_⟩, hDB⟩
  · rw [FiniteTimeGrid.card_interval]
    exact hlen
  · intro X hX t ht
    exact (havoid X hX head hhead t ht).1
  · intro X hX t ht
    have htop := (havoid X hX head hhead t ht).2
    have hpending := PersistencePrefixFibres.native_outside_remaining_bits M d b C S correct
      w (fun X => (hw X).le) T K t head X (hw X) htop
    have hpending' : Real.logb 2 (topSize (alpha h₀) P + 1) ≤
        (d*d*b : ℕ) - (priorWord M S t X).length := by
      simpa only [K, Nat.cast_add, Nat.cast_one, priorWord] using hpending
    exact (topSize_log_lower (alpha h₀) P).trans hpending'
  · intro h hh t ht z v hden
    exact (hatoms h hh t ht z v hden).trans hsmall

end AdaptiveTransfer.ConditionalPersistence
