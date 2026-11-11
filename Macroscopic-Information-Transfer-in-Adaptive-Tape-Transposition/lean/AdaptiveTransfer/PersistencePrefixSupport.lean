import AdaptiveTransfer.PersistencePrefixFibres

/-! Positive attained vertices outside the original conditional top sets
force undelivered input information. Correctness supplies the prefix-fibre
upper bound, rather than an assumed independence or full-size fibre. -/

namespace AdaptiveTransfer.PersistencePrefixFibres
open Transpose Transpose.Tape MergeDepth LeanMachine Finset
open PersistenceGraph PersistenceCatalogues FiniteObservationTopSets
attribute [local instance] Classical.propDecidable

theorem native_outside_prefix_support (M : TM) (d b : ℕ) (c : ℝ)
    (S : Finset (Fin (d*d*b) → Bool)) (hS : ∀ X ∈ S, TransposesInput M d b c X)
    (w : S → ℝ) (hw : ∀ X, 0 ≤ w X) (T K t : ℕ) (h : Fin M.k)
    (X : S) (hX : 0 < w X)
    (hout : vertex M (List.ofFn X.val) T t h ∉
      nativeTop M (fun Y : S => List.ofFn Y.val) w T K h t
        (PrefixOutput.word (outBit M (List.ofFn X.val)) t)) :
    K + 1 ≤ 2 ^ (d*d*b - (PrefixOutput.word (outBit M (List.ofFn X.val)) t).length) := by
  classical
  let z (Y : S) := PrefixOutput.word (outBit M (List.ofFn Y.val)) t
  let f (Y : S) := vertex M (List.ofFn Y.val) T t h
  have hpos := attained_atom_pos w hw z f X hX
  have hsupport := context_card_of_outside w z f (z X) K hout hpos
  let F := (univ : Finset S).filter fun Y => z Y = z X
  have hsub : F.image (fun Y : S => Y.val) ⊆
      S.filter (fun Y => PrefixOutput.word (outBit M (List.ofFn Y)) t = z X) := by
    intro Y hY
    obtain ⟨Z, hZ, rfl⟩ := mem_image.mp hY
    exact mem_filter.mpr ⟨Z.property, (mem_filter.mp hZ).2⟩
  have hc : F.card ≤
      (S.filter (fun Y => PrefixOutput.word (outBit M (List.ofFn Y)) t = z X)).card := by
    rw [← card_image_of_injective F Subtype.val_injective]
    exact card_le_card hsub
  have hsupport' : K + 1 ≤ F.card := by
    convert hsupport using 1
    congr 1
    ext Y
    simp only [F, mem_filter, mem_univ, true_and]
  exact hsupport'.trans (hc.trans (native_prefix_fibre_card M d b c S hS t (z X)))

theorem native_outside_remaining_bits (M : TM) (d b : ℕ) (c : ℝ)
    (S : Finset (Fin (d*d*b) → Bool)) (hS : ∀ X ∈ S, TransposesInput M d b c X)
    (w : S → ℝ) (hw : ∀ X, 0 ≤ w X) (T K t : ℕ) (h : Fin M.k)
    (X : S) (hX : 0 < w X)
    (hout : vertex M (List.ofFn X.val) T t h ∉
      nativeTop M (fun Y : S => List.ofFn Y.val) w T K h t
        (PrefixOutput.word (outBit M (List.ofFn X.val)) t)) :
    Real.logb 2 (K + 1 : ℕ) ≤
      (d*d*b : ℕ) - (PrefixOutput.word (outBit M (List.ofFn X.val)) t).length := by
  let z := PrefixOutput.word (outBit M (List.ofFn X.val)) t
  have hs := native_outside_prefix_support M d b c S hS w hw T K t h X hX hout
  obtain ⟨N, htN, hN⟩ := timely_later_output (hS X.val X.property) t
  have hlen : z.length ≤ d*d*b := by
    have hh := PrefixOutput.length_mono (outBit M (List.ofFn X.val)) htN
    change z.length ≤ (PrefixOutput.word (outBit M (List.ofFn X.val)) N).length at hh
    simpa only [hN, List.length_ofFn] using hh
  have hreal : (K + 1 : ℝ) ≤ (2 : ℝ) ^ (d*d*b - z.length) := by exact_mod_cast hs
  have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by positivity : (0 : ℝ) < K + 1) hreal
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),
    mul_one, Nat.cast_sub hlen] at hh
  simpa only [Nat.cast_add, Nat.cast_one] using hh

end AdaptiveTransfer.PersistencePrefixFibres
