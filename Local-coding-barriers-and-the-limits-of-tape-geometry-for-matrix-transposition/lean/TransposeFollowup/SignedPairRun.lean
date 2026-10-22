import TransposeFollowup.SignedPairCalls

/-! The complete signed-pair comparison has an actual native trace. Four
source words and all six absolute heads are preserved, both scratch buffers
are cleared and prepared again, and all transfers/cleanup are charged. -/

namespace TransposeFollowup.SignedPair

open FixedTapeCompiler
open BinaryCompare (value)
open RepeatedAdd (addWord addWord_length)
set_option autoImplicit false

theorem comparison_trace (a b c d : List Bool)
    (ha : a.length = d.length) (hb : b.length = d.length) (hc : c.length = d.length)
    (pos : Port → ℤ) :
    ∃ t ≤ 23 * d.length + 37,
      Trace t (cfg (.add false (.scan false false)) (ready a b c d) pos)
        (cfg (.done (result a b c d)) (ready a b c d) pos) := by
  let l := addWord a d
  let r := addWord c b
  have hl : l.length = d.length := addWord_length a d ha
  have hr : r.length = d.length := (addWord_length c b (hc.trans hb.symm)).trans hb
  let s0 := ready a b c d
  let s1 := {s0 with left := BinaryCarry.marked l}
  let s2 := {s1 with right := BinaryCarry.marked r}
  let s3 := {s2 with left := BinaryCarry.preparedOutput}
  let s4 := {s3 with right := BinaryCarry.preparedOutput}
  let cl := (BinaryCarry.result false false a d).2
  let cr := (BinaryCarry.result false false c b).2
  let answer := result a b c d
  obtain ⟨tl, htl, hLeft⟩ := left_call a d ha s0 pos
  have tLeft : Trace tl (cfg (.add false (.scan false false)) s0 pos)
      (cfg (.add false (.done cl)) s1 pos) := by
    simpa [s0, s1, l, cl, ready] using hLeft
  obtain ⟨tr, htr, hRight⟩ := right_call c b (hc.trans hb.symm) s1 pos
  rw [hb] at htr
  have tRight : Trace tr (cfg (.add true (.scan false false)) s1 pos)
      (cfg (.add true (.done cr)) s2 pos) := by
    simpa [s2, s1, s0, r, cr, ready] using hRight
  obtain ⟨tc, htc, hCompare⟩ := compare_call l r (hl.trans hr.symm) s2 pos
  rw [hl] at htc
  have tCompare : Trace tc (cfg (.compare (.scan .equal)) s2 pos)
      (cfg (.compare (.done answer)) s2 pos) := by
    simpa [s2, s1, s0, l, r, answer, result, ready, BinaryCarry.marked] using hCompare
  obtain ⟨te, hte, hErase⟩ := recycle_call false answer l s2 pos
  rw [hl] at hte
  have tErase : Trace te (cfg (.clear false answer (.erase 2)) s2 pos)
      (cfg (.clear false answer .done) s3 pos) := by
    simpa [Bank.set, s3, s2, s1, s0, ready, Counter.marked, BinaryCarry.marked,
      BinaryCompare.marked] using hErase
  obtain ⟨tf, htf, hFinish⟩ := recycle_call true answer r s3 pos
  rw [hr] at htf
  have tFinish : Trace tf (cfg (.clear true answer (.erase 2)) s3 pos)
      (cfg (.clear true answer .done) s4 pos) := by
    simpa [Bank.set, s4, s3, s2, s1, s0, ready, Counter.marked, BinaryCarry.marked,
      BinaryCompare.marked] using hFinish
  have j1 := jump_trace (.add false (.done cl)) (.add true (.scan false false)) s1 pos rfl
  have j2 := jump_trace (.add true (.done cr)) (.compare (.scan .equal)) s2 pos rfl
  have j3 := jump_trace (.compare (.done answer)) (.clear false answer (.erase 2)) s2 pos rfl
  have j4 := jump_trace (.clear false answer .done) (.clear true answer (.erase 2)) s3 pos rfl
  have j5 := jump_trace (.clear true answer .done) (.done answer) s4 pos rfl
  have whole := NativeCountedLoop.trace_trans tLeft (NativeCountedLoop.trace_trans j1
    (NativeCountedLoop.trace_trans tRight (NativeCountedLoop.trace_trans j2
      (NativeCountedLoop.trace_trans tCompare (NativeCountedLoop.trace_trans j3
        (NativeCountedLoop.trace_trans tErase (NativeCountedLoop.trace_trans j4
          (NativeCountedLoop.trace_trans tFinish j5))))))))
  refine ⟨tl + (1 + (tr + (1 + (tc + (1 + (te + (1 + (tf + 1)))))))), ?_, ?_⟩
  · omega
  · simpa [s4, s3, s2, s1, s0, ready, answer] using whole

theorem signed_comparison_trace (a b c d : List Bool)
    (ha : a.length = d.length) (hb : b.length = d.length) (hc : c.length = d.length)
    (hleft : value a + value d < 2 ^ d.length)
    (hright : value c + value b < 2 ^ d.length) (pos : Port → ℤ) :
    ∃ t ≤ 23 * d.length + 37,
      Trace t (cfg (.add false (.scan false false)) (ready a b c d) pos)
        (cfg (.done (numeric (integer a b) (integer c d))) (ready a b c d) pos) := by
  simpa only [result_spec a b c d ha (hc.trans hb.symm) hleft (by simpa [hb] using hright)]
    using comparison_trace a b c d ha hb hc pos

theorem native_comparison (a b c d : List Bool)
    (ha : a.length = d.length) (hb : b.length = d.length) (hc : c.length = d.length)
    (hleft : value a + value d < 2 ^ d.length)
    (hright : value c + value b < 2 ^ d.length) (pos : Port → ℤ)
    (w : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ 23 * d.length + 37,
      Transpose.stepN nativeMachine w t
        ((cfg (.add false (.scan false false)) (ready a b c d) pos).denote
          nativeEncoding program inputPos outRev) =
        some ((cfg (.done (numeric (integer a b) (integer c d))) (ready a b c d) pos).denote
          nativeEncoding program inputPos outRev) ∧
      Transpose.step nativeMachine w
        ((cfg (.done (numeric (integer a b) (integer c d))) (ready a b c d) pos).denote
          nativeEncoding program inputPos outRev) = none := by
  obtain ⟨t, ht, htr⟩ := signed_comparison_trace a b c d ha hb hc hleft hright pos
  refine ⟨t, ht, NativeMicrocode.trace_stepN nativeEncoding program w inputPos outRev htr, ?_⟩
  apply (NativeMicrocode.step_none_iff nativeEncoding program w inputPos outRev _).mpr
  simp [NativeMicrocode.Active, cfg, program]

theorem native_call {U J : Type*} {k q : ℕ}
    (encoding : NativeMicrocode.Encoding U J k q) (ports : Port ↪ U)
    (labels : Label → J) (target : Microcode.Program U J)
    (outerFrame : MicrocodeEmbedding.Frame U)
    (hcode : ∀ pc, program pc ≠ .halt → program pc ≠ .reject →
      target (labels pc) = MicrocodeEmbedding.instruction ports labels (program pc))
    (a b c d : List Bool)
    (ha : a.length = d.length) (hb : b.length = d.length) (hc : c.length = d.length)
    (hleft : value a + value d < 2 ^ d.length)
    (hright : value c + value b < 2 ^ d.length) (pos : Port → ℤ)
    (w : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ 23 * d.length + 37,
      Transpose.stepN (NativeMicrocode.machine encoding target) w t
        ((MicrocodeEmbedding.embed ports labels
          (cfg (.add false (.scan false false)) (ready a b c d) pos)
          outerFrame).denote encoding target inputPos outRev) =
        some ((MicrocodeEmbedding.embed ports labels
          (cfg (.done (numeric (integer a b) (integer c d))) (ready a b c d) pos)
          outerFrame).denote encoding target inputPos outRev) := by
  obtain ⟨t, ht, htr⟩ := signed_comparison_trace a b c d ha hb hc hleft hright pos
  exact ⟨t, ht, MicrocodeEmbedding.native_call encoding ports labels program target
    outerFrame w inputPos outRev hcode htr⟩

end TransposeFollowup.SignedPair
