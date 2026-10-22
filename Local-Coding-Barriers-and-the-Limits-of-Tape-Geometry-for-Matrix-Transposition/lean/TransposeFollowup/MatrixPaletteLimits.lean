import TransposeFollowup.RawSymbolWordObstruction
import TransposeFollowup.MatrixPermutationGeometry

/-! Canonical matrix-size specialization of the full native word theorem.
The row-to-payload ratio is 1/d. All logarithmic entry-width and state-bit
facts refer to the original paper's unchanged definitions. -/
namespace TransposeFollowup.MatrixPaletteLimits
open Classical Set Filter Topology FixedTapeCompiler ScheduledNativeIO AffineMotion
open Transpose Transpose.Tape Transpose.Tape.Impl
open MatrixPermutationPalette (coverSize errorBound)
set_option autoImplicit false
variable {O : Type*}

theorem bits_pos (n : ℕ) : 0 < entryBits n := by unfold entryBits; omega

theorem error_vanishes {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop) :
    Tendsto (fun i => errorBound (ns i*entryBits (ns i))/inputLength (ns i)) atTop (𝓝 0) := by
  have hn : Tendsto (fun i => (ns i : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hns
  have hrow : Tendsto (fun i => ((ns i*entryBits (ns i) : ℕ) : ℝ)/inputLength (ns i)) atTop (𝓝 0) := by
    apply (show Tendsto (fun i => (1 : ℝ)/ns i) atTop (𝓝 0) from tendsto_const_nhds.div_atTop hn).congr'
    filter_upwards [hns.eventually_ge_atTop 1] with i hi
    have hn0 : (ns i : ℝ) ≠ 0 := by exact_mod_cast (show ns i ≠ 0 by omega)
    have hb0 : (entryBits (ns i) : ℝ) ≠ 0 := by exact_mod_cast (bits_pos (ns i)).ne'
    simp only [inputLength,Nat.cast_mul]
    field_simp
  have hconst : Tendsto (fun i => (32 : ℝ)/inputLength (ns i)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (inputLength_tendsto hns)
  simpa only [errorBound,mul_add,mul_one,add_div,mul_div_assoc,mul_zero,add_zero] using
    (hrow.const_mul 32).add hconst

theorem no_high_entropy_transpose {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop)
    (cost : ℕ → ℕ → O → ℕ)
    (code : ℕ → ℕ → O → ℕ → NativeIO.Program (Fin 2) SharedRowBank.Mode)
    (value : ℕ → ℕ → O → (ℕ → CopyMachine.Sym Bool) → ℕ → CopyMachine.Sym Bool)
    (q : ℕ → ℕ → O → ℕ → Fin 2 → ℝ → ℝ)
    (hcorrect : ∀ b d, 0<b → 0<d → RawSymbolWord.Correct (d*(d*b)) (cost b d) (code b d) (value b d))
    (hcost : ∀ b d, 0<b → 0<d → ∀ op, cost b d op ≤ 24*(d*(d*b)))
    (hcover : ∀ b d op A t H, 0 ≤ H → HasAffineIntervalCover coverSize (q b d op A t) H)
    (herror : ∀ b d, 0<b → 0<d → ∀ op A w c x t,
      |((trajectory (code b d op) w c (min (⌊x⌋₊-A) (cost b d op))).work.pos t : ℝ)-
        c.work.pos t-q b d op A t x| ≤ errorBound (d*b))
    {K : ℕ} (ops : ℕ → List O) (hK : ∀ᶠ i in atTop, (ops i).length ≤ K)
    {Ws : ℕ → Set (List Bool)} {ms : ℕ → ℕ}
    (hm : ∀ᶠ i in atTop, 2^inputLength (ns i) ≤ 2^ms i*(Ws i).ncard)
    (hmL : Tendsto (fun i => (ms i : ℝ)/inputLength (ns i)) atTop (𝓝 0))
    (hcorr : ∀ᶠ i in atTop, ∀ w ∈ Ws i, ∃ A : Matrix,
      w=encode (ns i) (entryBits (ns i)) A ∧
      RawSymbolWord.output (ns i*(ns i*entryBits (ns i))) (value (entryBits (ns i)) (ns i)) (ops i) w=
        encode (ns i) (entryBits (ns i)) (transpose A)) : False := by
  refine RawSymbolWord.no_high_entropy_transpose hns
    (fun i => cost (entryBits (ns i)) (ns i))
    (fun i => code (entryBits (ns i)) (ns i))
    (fun i => value (entryBits (ns i)) (ns i)) ops (C:=24) (J:=coverSize)
    (by norm_num [coverSize]) ?_ hK ?_
    (fun i => q (entryBits (ns i)) (ns i)) (fun i => errorBound (ns i*entryBits (ns i)))
    ?_ (error_vanishes hns) ?_ ?_ hm hmL ?_
  · filter_upwards [hns.eventually_ge_atTop 1] with i hi
    simpa only [inputLength,Nat.mul_assoc] using
      hcorrect (entryBits (ns i)) (ns i) (bits_pos (ns i)) (by omega)
  · filter_upwards [hns.eventually_ge_atTop 1] with i hi
    intro op _
    simpa only [inputLength,Nat.mul_assoc] using
      hcost (entryBits (ns i)) (ns i) (bits_pos (ns i)) (by omega) op
  · exact Eventually.of_forall (fun i => by unfold errorBound; positivity)
  · exact Eventually.of_forall (fun i op _ A t H hH => hcover _ _ op A t H hH)
  · filter_upwards [hns.eventually_ge_atTop 1] with i hi
    intro op _ w A c x t
    exact herror (entryBits (ns i)) (ns i) (bits_pos (ns i)) (by omega) op A w c x t
  · simpa only [inputLength,Nat.mul_assoc] using hcorr

end TransposeFollowup.MatrixPaletteLimits
