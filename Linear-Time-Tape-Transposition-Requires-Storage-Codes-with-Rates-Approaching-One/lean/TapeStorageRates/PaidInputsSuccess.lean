import TapeStorageRates.PaidInputs
import MergeDepth.Q91
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Correct sets, payload output and exponential success probabilities

The good set uses the native bounded-time transposition predicate on each
individual raw input. No halting condition is imposed outside this set.
-/

namespace TapeStorageRates.PaidInputs

open Finset Filter DirectedRecovery MergeDepth
open scoped Topology

set_option autoImplicit false

open Classical in
/-- Inputs on which the actual machine halts within the given coefficient
and emits the correct transpose, at the specified width. -/
noncomputable def successfulInputsAt (M : Transpose.TM) (c : ℝ) (d b : ℕ) :
    Finset (Raw d b) := univ.filter (TransposesInput M d b c)

@[simp] theorem mem_successfulInputsAt {M : Transpose.TM} {c : ℝ} {d b : ℕ} {x : Raw d b} :
    x ∈ successfulInputsAt M c d b ↔ TransposesInput M d b c x := by
  simp [successfulInputsAt]

theorem successfulInputsAt_eq_univ {M : Transpose.TM} {c : ℝ} {d b : ℕ}
    (h : TransposesAtWidth M d b c) : successfulInputsAt M c d b = univ := by
  ext x
  simp [h.transposesInput x]

/-- A successful payload on a fixed tail has a timely physical halting run
whose actual output supplies each required packet bit and each required tail bit. -/
theorem successful_payload_output {M : Transpose.TM} {c : ℝ} {d a s r : ℕ}
    (u : Payload d a s) (z : Raw d r)
    (hu : u ∈ payloadFibre (successfulInputsAt M c d (a*s+r)) z) :
    let x := (splitWord d a s r).symm (u,z)
    ∃ t ≤ ⌊c * (((d*d*(a*s+r) : ℕ) : ℝ) + 1)⌋₊,
      Transpose.Tape.HaltsAt M (List.ofFn x) t ∧
      (Transpose.Tape.run M (List.ofFn x) t).outRev.reverse.length = d*d*(a*s+r) ∧
      (∀ q l, (Transpose.Tape.run M (List.ofFn x) t).outRev.reverse[
        (raggedAddress d a s r (.inl (tposOf d a q,l))).val]? = some (u q l)) ∧
      ∀ q, (Transpose.Tape.run M (List.ofFn x) t).outRev.reverse[
        (raggedAddress d a s r (.inr (tposOf d r q))).val]? = some (z q) := by
  let x := (splitWord d a s r).symm (u,z)
  have h : TransposesInput M d (a*s+r) c x := mem_successfulInputsAt.mp (mem_payloadFibre.mp hu)
  obtain ⟨t,ht,hlen,hout⟩ := h.outputsTranspose.output
  obtain ⟨t',ht',hHalt'⟩ := h.halts
  obtain rfl := Transpose.Tape.Impl.haltsAt_unique hHalt' ht
  refine ⟨t', ht', hHalt', hlen, ?_, ?_⟩
  · intro q l
    have hbit := hout (raggedAddress d a s r (.inl (q,l)))
    change _[(tposOf d (a*s+r) (raggedAddress d a s r (.inl (q,l)))).val]? = _ at hbit
    simpa only [tpos_payload, x, rebuild_payload] using hbit
  · intro q
    have hbit := hout (raggedAddress d a s r (.inr q))
    change _[(tposOf d (a*s+r) (raggedAddress d a s r (.inr q))).val]? = _ at hbit
    simpa only [tpos_tail, x, rebuild_tail] using hbit

abbrev canonicalLength (d : ℕ) := d*d*Transpose.entryBits d

noncomputable abbrev successfulInputs (M : Transpose.TM) (c : ℝ) (d : ℕ) :=
  successfulInputsAt M c d (Transpose.entryBits d)

/-- The eventually exponentially small success conclusion, in raw cardinality form. -/
def ExponentiallySmallSuccess (M : Transpose.TM) (c : ℝ) : Prop :=
  ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ d : ℕ in atTop,
    ((successfulInputs M c d).card : ℝ) ≤ (2 : ℝ) ^ ((1-γ) * canonicalLength d)

/-- A sequence of increasing positive dimensions with success on `2^(L-o(L))`
inputs, expressed by the vanishing logarithmic deficit divided by length. -/
def NearFullSuccess (M : Transpose.TM) (c : ℝ) : Prop :=
  ∃ D : ℕ → ℕ, StrictMono D ∧ (∀ i, 0 < D i ∧ (successfulInputs M c (D i)).Nonempty) ∧
    Tendsto (fun i => 1 - storageCodeRate (successfulInputs M c (D i))) atTop (𝓝 0)

/-- Failure of every eventual exponential upper bound produces one strictly
increasing sequence of actual correct sets with vanishing relative deficit.
This is an unconditional statement about the native success probabilities. -/
theorem nearFullSuccess_of_not_exponentiallySmall {M : Transpose.TM} {c : ℝ}
    (hn : ¬ ExponentiallySmallSuccess M c) : NearFullSuccess M c := by
  let err (i : ℕ) : ℝ := 1 / (i + 1)
  have herr (i : ℕ) : 0 < err i := by dsimp [err]; positivity
  have hf (i : ℕ) : ∃ᶠ d : ℕ in atTop, 0 < d ∧
      (2 : ℝ) ^ ((1-err i) * canonicalLength d) < (successfulInputs M c d).card := by
    have he : ¬ ∀ᶠ d : ℕ in atTop, ((successfulInputs M c d).card : ℝ) ≤
        (2 : ℝ) ^ ((1-err i) * canonicalLength d) := fun h => hn ⟨err i, herr i, h⟩
    have hfreq : ∃ᶠ d : ℕ in atTop, (2 : ℝ) ^ ((1-err i) * canonicalLength d) <
        (successfulInputs M c d).card := by simpa only [Filter.Frequently, not_lt] using he
    exact (hfreq.and_eventually (eventually_gt_atTop 0)).mono fun _ h => ⟨h.2,h.1⟩
  obtain ⟨D,hD,hcard⟩ := extraction_forall_of_frequently hf
  have hpos (i : ℕ) : 0 < ((successfulInputs M c (D i)).card : ℝ) :=
    (Real.rpow_pos_of_pos (by norm_num) _).trans (hcard i).2
  refine ⟨D,hD, fun i => ⟨(hcard i).1, card_pos.mp (by exact_mod_cast hpos i)⟩, ?_⟩
  apply squeeze_zero (fun i => sub_nonneg.mpr (MergeDepth.storageCodeRate_le_one (by simp) _))
    (g := err) _ tendsto_one_div_add_atTop_nhds_zero_nat
  intro i
  have hi := (hcard i).1
  have hL : 0 < (canonicalLength (D i) : ℝ) := by
    exact_mod_cast Nat.mul_pos (Nat.mul_pos hi hi) (by simp [Transpose.entryBits])
  have hlt : 1 - err i < storageCodeRate (successfulInputs M c (D i)) := by
    unfold storageCodeRate
    simp only [Fintype.card_bool, Fintype.card_fin, Nat.cast_ofNat]
    exact (lt_div_iff₀ hL).mpr ((Real.lt_logb_iff_rpow_lt (by norm_num) (hpos i)).mpr (hcard i).2)
  linarith

/-- It suffices to exclude success sets of vanishing deficit fraction along
an unbounded sequence to obtain one eventual exponential bound. -/
theorem exponentiallySmall_of_not_nearFull {M : Transpose.TM} {c : ℝ}
    (hn : ¬ NearFullSuccess M c) : ExponentiallySmallSuccess M c :=
  Classical.byContradiction fun he => hn (nearFullSuccess_of_not_exponentiallySmall he)

/-- A binary-cube probability bound and its unnormalized cardinality bound
have exactly the same exponent, also when the successful set is empty. -/
theorem uniform_fraction_le_iff {n m : ℕ} (γ : ℝ) :
    (m : ℝ) / (2:ℝ)^n ≤ (2:ℝ)^(-γ*n) ↔ (m:ℝ) ≤ (2:ℝ)^((1-γ)*n) := by
  rw [div_le_iff₀ (by positivity), ← Real.rpow_natCast (2:ℝ) n,
    ← Real.rpow_add (by norm_num : (0:ℝ)<2), show -γ*n+n = (1-γ)*n by ring]

/-- Cardinality and uniform-input probability versions have the same exponent. -/
theorem exponentiallySmall_iff_probability (M : Transpose.TM) (c : ℝ) :
    ExponentiallySmallSuccess M c ↔
      ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ d : ℕ in atTop,
        ((successfulInputs M c d).card : ℝ) / (2 : ℝ) ^ canonicalLength d ≤
          (2 : ℝ) ^ (-γ * canonicalLength d) := by
  simp only [ExponentiallySmallSuccess,uniform_fraction_le_iff]

end TapeStorageRates.PaidInputs
