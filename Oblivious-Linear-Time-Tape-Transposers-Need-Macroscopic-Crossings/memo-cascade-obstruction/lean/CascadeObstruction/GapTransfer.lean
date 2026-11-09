import CascadeObstruction.DeficitAccounting
import CascadeObstruction.NativeObstruction

/-! Transfer a certified native integer gap to the source controller bits plus
its exact real correctness deficit. Compiler and regularity certificates remain
explicit hypotheses; the only discarded cost is proved sublinear overhead. -/

namespace CascadeObstruction

open Filter Topology Transpose Transpose.Tape Transpose.Tape.Impl
open TransposeFollowup.RegularMotion TransposeFollowup.AffineMotion

set_option autoImplicit false

/-- An eventual uniform gap survives an additive error tending to zero.
The estimate is uniform over all admissible objects at each size. -/
theorem uniform_gap_of_le_add_vanishing {Obj : ℕ → Type*}
    {source target : (n : ℕ) → Obj n → ℝ} {overhead : ℕ → ℝ}
    (hgap : ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ,
      ∀ n ≥ N, ∀ x : Obj n, δ ≤ target n x)
    (haccount : ∀ n x, target n x ≤ source n x + overhead n)
    (hsmall : Tendsto overhead atTop (𝓝 0)) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ,
      ∀ n ≥ N, ∀ x : Obj n, δ ≤ source n x := by
  obtain ⟨δ, hδ, N, hN⟩ := hgap
  have hev : ∀ᶠ n in atTop, overhead n < δ / 2 :=
    hsmall.eventually (Iio_mem_nhds (by linarith))
  obtain ⟨N', hN'⟩ := eventually_atTop.1 hev
  refine ⟨δ / 2, by positivity, max N N', ?_⟩
  intro n hn x
  have hg := hN n (le_trans (le_max_left _ _) hn) x
  have hs := hN' n (le_trans (le_max_right _ _) hn)
  have ha := haccount n x
  linarith

/-- Adding a fixed number of bits to a sublinear overhead remains sublinear. -/
theorem add_const_div_inputLength_tendsto {overhead : ℕ → ℝ}
    (hsmall : Tendsto (fun n => overhead n / inputLength n) atTop (𝓝 0))
    (c : ℝ) :
    Tendsto (fun n => (overhead n + c) / inputLength n) atTop (𝓝 0) := by
  have hconst : Tendsto (fun n => c / (inputLength n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (inputLength_tendsto tendsto_id)
  simpa only [add_zero, add_div] using hsmall.add hconst

/-- A paid public clock has sublinear bit cost on every linear-time family.
The existing Paper 1 estimate also covers an arbitrary diverging size sequence. -/
theorem clock_bits_div_inputLength_tendsto {ns T : ℕ → ℕ} {c : ℝ}
    (hns : Tendsto ns atTop atTop)
    (htime : ∀ᶠ i in atTop, (T i : ℝ) ≤ c * inputLength (ns i)) :
    Tendsto (fun i => (Nat.clog 2 (T i + 1) : ℝ) / inputLength (ns i))
      atTop (𝓝 0) := by
  have hbig : Tendsto (fun i => (Nat.clog 2 (2 * T i + 1) : ℝ) /
      inputLength (ns i)) atTop (𝓝 0) := by
    simpa only [Nat.zero_add, Nat.one_mul, Nat.cast_zero, zero_div] using
      (stateBits_div_tendsto (k := 0) (qs := fun _ => 0) hns htime (by simp))
  apply squeeze_zero (fun i => by positivity) _ hbig
  intro i
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Nat.clog_mono_right 2 (show T i + 1 ≤ 2 * T i + 1 by omega)

/-- The native correctness and counting certificates already imply that the
correct-set cardinality is positive and at most the full binary cube. -/
theorem NativeDyadicInstance.card_bounds {k G n : ℕ} {a : ℝ}
    (F : NativeDyadicInstance k G a n) :
    0 < F.correctSet.ncard ∧ F.correctSet.ncard ≤ 2 ^ inputLength n := by
  have hpos : 0 < 2 ^ F.deficit * F.correctSet.ncard :=
    lt_of_lt_of_le (by positivity : 0 < 2 ^ inputLength n) F.count
  have hcard : 0 < F.correctSet.ncard := by
    by_contra h
    have hz : F.correctSet.ncard = 0 := by omega
    simp [hz] at hpos
  refine ⟨hcard, ?_⟩
  have hsub : F.correctSet ⊆ matrixInputs n (entryBits n) := by
    intro w hw
    obtain ⟨T, _, ⟨A, hwA, _⟩, _⟩ := F.correct w hw
    exact ⟨A, hwA.symm⟩
  have hfinite : (matrixInputs n (entryBits n)).Finite := by
    rw [matrixInputs_eq]
    exact List.finite_length_eq Bool _
  simpa only [ncard_matrixInputs, inputLength] using Set.ncard_le_ncard hsub hfinite

/-- Tighten an existing integer certificate by rounding the exact deficit.
The machine, correctness set, physical clocks and correctness proofs are unchanged. -/
noncomputable def NativeDyadicInstance.rounded {k G n : ℕ} {a : ℝ}
    (F : NativeDyadicInstance k G a n) : NativeDyadicInstance k G a n :=
  { F with
    deficit := roundedDeficit (inputLength n) F.correctSet.ncard
    count := pow_le_roundedDeficit_mul F.card_bounds.1 }

/-- A uniform native gap yields a uniform gap for the exact real deficit of
its correct set. `stateCost` is the source controller-bit cost, and `overhead`
is a uniform bound on the additional compiler controller bits. -/
theorem uniform_native_real_deficit_gap {k G : ℕ} {a : ℝ}
    {Obj : ℕ → Type*}
    (family : ∀ n, Obj n → NativeDyadicInstance k G a n)
    (stateCost : (n : ℕ) → Obj n → ℝ) (overhead : ℕ → ℝ)
    (ha : 0 ≤ a)
    (hregular : ∀ (ns : ℕ → ℕ) (xs : ∀ i, Obj (ns i)),
      Tendsto ns atTop atTop →
      HasRegularRecursiveExecutions 1 2 (1 / 2) a 1 ns
        (fun i => (family (ns i) (xs i)).machine)
        (fun i => (family (ns i) (xs i)).correctSet)
        (fun i => (family (ns i) (xs i)).tape_count))
    (hstate : ∀ n x, (Nat.clog 2 ((family n x).machine.q + 1) : ℝ) ≤
      stateCost n x + overhead n)
    (hsmall : Tendsto (fun n => overhead n / inputLength n) atTop (𝓝 0)) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ x : Obj n,
      δ ≤ (stateCost n x + realDeficit (inputLength n)
        (family n x).correctSet.ncard) / inputLength n := by
  apply uniform_gap_of_le_add_vanishing
    (target := fun n x => (family n x).rounded.cost)
    (overhead := fun n => (overhead n + 1) / inputLength n)
    (uniform_native_dyadic_gap (fun n x => (family n x).rounded) ha hregular)
  · intro n x
    have hd := roundedDeficit_lt_add_one (family n x).card_bounds.1
      (family n x).card_bounds.2
    have hs := hstate n x
    unfold NativeDyadicInstance.cost NativeDyadicInstance.rounded
    calc
      _ ≤ (stateCost n x + realDeficit (inputLength n)
          (family n x).correctSet.ncard + (overhead n + 1)) / inputLength n :=
        div_le_div_of_nonneg_right (by linarith) (by positivity)
      _ = _ := add_div _ _ _
  · exact add_const_div_inputLength_tendsto hsmall 1

end CascadeObstruction
