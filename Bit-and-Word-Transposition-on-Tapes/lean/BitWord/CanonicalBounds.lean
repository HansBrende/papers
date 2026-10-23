import BitWord.CanonicalGates
import BitWord.NativeRulersRun
import TransposeFollowup.EntryBitsRun

/-! Explicit input-size bounds for the uniform canonical wrapper, including
its smallest dimension. -/
namespace BitWord
open Transpose FixedTapeCompiler TransposeFollowup

 theorem canonical_h_pos (d : ℕ) : 0<entryBits d := by unfold entryBits; omega

 theorem canonical_dimension_bounds {d : ℕ} (hd : 1≤d) :
     d≤2^entryBits d ∧ 2^entryBits d≤2*d := by
   refine ⟨Tape.Impl.le_two_pow_entryBits d,?_⟩
   by_cases h1 : d=1
   · subst d; decide
   · have hh : d-1≠0 := by omega
     have hpow := Nat.log2_self_le hh
     simp only [entryBits,pow_succ]
     omega

 theorem laneBits_le (h : ℕ) : laneBits h≤h := by
   exact Nat.clog_le_of_le_pow (Nat.le_of_lt (Nat.lt_two_pow_self (n := h)))

 theorem tailBits_le_twice {h : ℕ} (hh : 1≤h) : tailBits h≤2*h := by
   have hu := laneBits_le h
   unfold tailBits dummyBits
   omega

 theorem halfAddress_le_twice {h : ℕ} (hh : 1≤h) : halfAddress h≤2*h := by
   have hw := tailBits_le_twice hh
   unfold halfAddress
   omega

 theorem tail_padding_lower {h : ℕ} (hh : 0<h) : h≤2^tailBits h := by
   have hp := (lane_padding_bounds hh).1
   exact hp.trans (Nat.pow_le_pow_right (by decide) (by unfold tailBits; omega))

 theorem canonical_input_bounds {d : ℕ} (hd : 1≤d) :
     1≤ inputLength d ∧ d≤ inputLength d ∧ entryBits d≤ inputLength d ∧
     d.size≤ inputLength d ∧ d*entryBits d≤ inputLength d ∧ entryBits d*entryBits d≤ inputLength d := by
   have hh := canonical_h_pos d
   have hhd := Tape.Impl.entryBits_le_self hd
   have hsize : d.size≤d := Nat.size_le.mpr (Nat.lt_two_pow_self (n := d))
   have hmul : d*entryBits d≤d*d*entryBits d :=
     Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right d (by omega))
   have hdP : d≤ inputLength d := by unfold inputLength; nlinarith
   have hhP : entryBits d≤ inputLength d := le_trans hhd hdP
   refine ⟨hd.trans hdP,hdP,hhP,hsize.trans hdP,hmul,?_⟩
   exact (Nat.mul_le_mul_right _ hhd).trans hmul

 theorem canonical_padded_volume {d : ℕ} (hd : 1≤d) :
     (2^entryBits d)*(2^entryBits d)*(2^tailBits (entryBits d))≤16*inputLength d := by
   have hD := (canonical_dimension_bounds hd).2
   have hB : 2^tailBits (entryBits d)≤4*entryBits d := (tail_padding_bound (canonical_h_pos d)).le
   calc
     _ ≤ (2*d)*(2*d)*(4*entryBits d) := Nat.mul_le_mul (Nat.mul_le_mul hD hD) hB
     _ = 16*inputLength d := by unfold inputLength; ring

 theorem canonical_row_widths {d : ℕ} (hd : 1≤d) :
     d*(2^tailBits (entryBits d))≤4*inputLength d ∧
     (2^entryBits d)*(2^tailBits (entryBits d))≤8*inputLength d := by
   have hD := (canonical_dimension_bounds hd).2
   have hB : 2^tailBits (entryBits d)≤4*entryBits d := (tail_padding_bound (canonical_h_pos d)).le
   have hdH := (canonical_input_bounds hd).2.2.2.2.1
   constructor
   · have hh := Nat.mul_le_mul_left d hB
     nlinarith
   · have hh := Nat.mul_le_mul hD hB
     nlinarith

 theorem canonical_rulers_budget {d : ℕ} (hd : 1≤d) (xs hs ws : List Bool)
     (hx : Counter.value xs=d) (hlx : xs.length=d.size)
     (hh : Counter.value hs=entryBits d) (hlh : hs.length=entryBits d)
     (hw : Counter.value ws=tailBits (entryBits d)) (hlw : ws.length≤4*entryBits d+8) :
     NativeRulers.budget xs hs ws≤20000*inputLength d := by
   have hb := NativeRulers.budget_le xs hs ws
   rw [hx,hlx,hh,hlh,hw] at hb
   obtain ⟨hP,hdP,hhP,hsP,_,_⟩ := canonical_input_bounds hd
   obtain ⟨hdB,hDB⟩ := canonical_row_widths hd
   have hD := (canonical_dimension_bounds hd).2
   have hB : 2^tailBits (entryBits d)≤4*entryBits d := (tail_padding_bound (canonical_h_pos d)).le
   have hwle := tailBits_le_twice (canonical_h_pos d)
   omega

end BitWord
