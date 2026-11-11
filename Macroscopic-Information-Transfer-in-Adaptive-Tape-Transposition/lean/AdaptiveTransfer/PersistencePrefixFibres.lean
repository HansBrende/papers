import AdaptiveTransfer.PersistenceCatalogues
import MergeDepth.LowAdaptivity
import LeanMachine.FiniteCoordinateFibres

/-! Actual strict output-prefix fibres fix distinct raw coordinates.
Adaptive output times may shrink such a fibre; equality with the full
coordinate fibre is neither assumed nor asserted. -/

namespace AdaptiveTransfer.PersistencePrefixFibres

open Transpose Transpose.Tape Transpose.Tape.Impl MergeDepth Finset LeanMachine
attribute [local instance] Classical.propDecidable

theorem prefix_fibre_card {P : ℕ} (S : Finset (Fin P → Bool))
    (emit : (Fin P → Bool) → ℕ → Option Bool) (π : Fin P → Fin P)
    (hπ : Function.Injective π) (t : ℕ) (z : List Bool)
    (hcorrect : ∀ X ∈ S, ∃ N, t ≤ N ∧
      PrefixOutput.word (emit X) N = List.ofFn (fun j => X (π j))) :
    (S.filter fun X => PrefixOutput.word (emit X) t = z).card ≤ 2 ^ (P - z.length) := by
  classical
  let D := S.filter fun X => PrefixOutput.word (emit X) t = z
  by_cases hD : D.Nonempty
  · obtain ⟨X₀, hX₀⟩ := hD
    obtain ⟨N₀, htN₀, hfinal₀⟩ := hcorrect X₀ (mem_filter.mp hX₀).1
    have hzP : z.length ≤ P := by
      have hh := PrefixOutput.length_mono (emit X₀) htN₀
      change (PrefixOutput.word (emit X₀) t).length ≤
        (PrefixOutput.word (emit X₀) N₀).length at hh
      rw [(mem_filter.mp hX₀).2, hfinal₀, List.length_ofFn] at hh
      exact hh
    let coords := (univ.filter fun j : Fin P => j.val < z.length).image π
    have hc : coords.card = z.length := by
      rw [card_image_of_injective _ hπ, Fin.card_filter_val_lt, min_eq_right hzP]
    have ha : ∀ X ∈ D, ∀ Y ∈ D, ∀ i ∈ coords, X i = Y i := by
      intro X hX Y hY i hi
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hi
      have hjz := (mem_filter.mp hj).2
      obtain ⟨NX, htNX, hfinalX⟩ := hcorrect X (mem_filter.mp hX).1
      obtain ⟨NY, htNY, hfinalY⟩ := hcorrect Y (mem_filter.mp hY).1
      have hpx := (mem_filter.mp hX).2
      have hpy := (mem_filter.mp hY).2
      have hx := PrefixOutput.getElem_stable (emit X) htNX (by simpa only [hpx] using hjz)
      have hy := PrefixOutput.getElem_stable (emit Y) htNY (by simpa only [hpy] using hjz)
      rw [hfinalX, hpx] at hx
      rw [hfinalY, hpy] at hy
      have he := hx.trans hy.symm
      simpa only [List.getElem?_ofFn, dite_eq_left j.isLt, Option.some.injEq] using he
    have hh := FiniteCoordinateFibres.card_le_complement D coords ha
    simpa only [Fintype.card_bool, Fintype.card_fin, hc] using hh
  · have he : D = ∅ := not_nonempty_iff_eq_empty.mp hD
    change D.card ≤ _
    simp only [he, card_empty, zero_le]

/-- A timely correct native input has the same correct final output at every
later frozen time, so any strict time admits the preceding prefix estimate. -/
theorem timely_later_output {M : TM} {d b : ℕ} {c : ℝ} {X : Fin (d*d*b) → Bool}
    (htr : TransposesInput M d b c X) (t : ℕ) :
    ∃ N, t ≤ N ∧ PrefixOutput.word (outBit M (List.ofFn X)) N =
      List.ofFn (fun j => X (tposOf d b j)) := by
  obtain ⟨s, hhalt, hlen, hout⟩ := htr.outputsTranspose.output
  have hfinal : (run M (List.ofFn X) s).outRev.reverse =
      List.ofFn (fun j => X (tposOf d b j)) := by
    apply List.ext_getElem?
    intro j
    by_cases hj : j < d*d*b
    · have he := hout (tposOf d b ⟨j, hj⟩)
      have hp : Transpose.Tape.tpos d b (tposOf d b ⟨j, hj⟩) = j :=
        congrArg Fin.val (tposOf_tposOf d b ⟨j, hj⟩)
      rw [hp] at he
      simpa only [List.getElem?_ofFn, dite_eq_left hj] using he
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]
  refine ⟨max t s, le_max_left _ _, ?_⟩
  rw [PrefixOutput.native_word,
    run_of_le_of_none hhalt.2 (le_max_right t s), hfinal]

theorem native_prefix_fibre_card (M : TM) (d b : ℕ) (c : ℝ)
    (S : Finset (Fin (d*d*b) → Bool)) (hS : ∀ X ∈ S, TransposesInput M d b c X)
    (t : ℕ) (z : List Bool) :
    (S.filter fun X => PrefixOutput.word (outBit M (List.ofFn X)) t = z).card ≤
      2 ^ (d*d*b - z.length) :=
  prefix_fibre_card S (fun X => outBit M (List.ofFn X)) (tposOf d b)
    (fun X Y h => by simpa only [tposOf_tposOf] using congrArg (tposOf d b) h)
    t z (fun X hX => timely_later_output (hS X hX) t)

end AdaptiveTransfer.PersistencePrefixFibres
