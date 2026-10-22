import TransposeFollowup.SignedPairRun
import TransposeFollowup.SignedOverlapData
import TransposeFollowup.InPlaceAdd

/-! Word banks and literal updates for one row cell. Only the four crossing
components change. Thresholds and increments are preserved. -/

namespace TransposeFollowup.RowCell

set_option autoImplicit false

inductive Group | threshold | crossing | delta
  deriving DecidableEq

instance : Fintype Group where
  elems := {.threshold, .crossing, .delta}
  complete := by intro g; cases g <;> simp

abbrev Index := Bool × Bool
abbrev WordPort := Group × Index
abbrev Words := WordPort → List Bool

def Width (m : ℕ) (w : Words) : Prop := ∀ p, (w p).length = m

def update (w : Words) (i : Index) : Words :=
  Function.update w (.crossing, i) (RepeatedAdd.addWord (w (.crossing, i)) (w (.delta, i)))

def updateAll (w : Words) : Words :=
  update (update (update (update w (false, false)) (false, true)) (true, false)) (true, true)

theorem update_width (m : ℕ) (w : Words) (h : Width m w) (i : Index) :
    Width m (update w i) := by
  intro p
  by_cases hp : p = (.crossing, i)
  · subst p
    simp only [update, Function.update_self]
    exact (RepeatedAdd.addWord_length _ _ ((h _).trans (h _).symm)).trans (h _)
  · simpa only [update, Function.update_of_ne hp] using h p

theorem updateAll_width (m : ℕ) (w : Words) (h : Width m w) : Width m (updateAll w) :=
  update_width m _ (update_width m _ (update_width m _ (update_width m w h _) _) _) _

theorem updateAll_apply (w : Words) (g : Group) (i : Index) :
    updateAll w (g, i) = if g = .crossing then
      RepeatedAdd.addWord (w (.crossing, i)) (w (.delta, i)) else w (g, i) := by
  rcases i with ⟨side, sign⟩
  cases g <;> cases side <;> cases sign <;> rfl

def compareA (second : Bool) : WordPort :=
  if second then (.crossing, true, false) else (.threshold, false, false)
def compareB (second : Bool) : WordPort :=
  if second then (.crossing, true, true) else (.threshold, false, true)
def compareC (second : Bool) : WordPort :=
  if second then (.threshold, true, false) else (.crossing, false, false)
def compareD (second : Bool) : WordPort :=
  if second then (.threshold, true, true) else (.crossing, false, true)

def comparison (second : Bool) (w : Words) : BinaryCompare.Result :=
  SignedPair.result (w (compareA second)) (w (compareB second))
    (w (compareC second)) (w (compareD second))

def answer (guard : Bool) (w : Words) : Bool :=
  (guard && decide (comparison false w = .less)) && decide (comparison true w = .less)

end TransposeFollowup.RowCell


/-! An actual fixed per-cell caller. Two signed comparisons retain their
conjunction in finite control; four in-place additions advance the crossing
components. Scratch is shared only after the subroutines clear it. -/

namespace TransposeFollowup.RowCell

open FixedTapeCompiler
open CopyMachine (Tape)
set_option autoImplicit false

inductive Port | word (p : WordPort) | fuel | zero | scratch (right : Bool)
  deriving DecidableEq, Fintype

def comparePort (second : Bool) : SignedPair.Port → Port
  | .a => .word (compareA second) | .b => .word (compareB second)
  | .c => .word (compareC second) | .d => .word (compareD second)
  | .left => .scratch false | .right => .scratch true

def compareDecode (second : Bool) (p : Port) : Option SignedPair.Port :=
  if p = comparePort second .a then some .a else
  if p = comparePort second .b then some .b else
  if p = comparePort second .c then some .c else
  if p = comparePort second .d then some .d else
  if p = .scratch false then some .left else
  if p = .scratch true then some .right else none

def compareBinding (second : Bool) : FinitePortBinding SignedPair.Port Port where
  ports := ⟨comparePort second, by cases second <;> decide +kernel⟩
  decode := compareDecode second
  decode_spec := by cases second <;> decide +kernel

def addPort (i : Index) : RepeatedAdd.Port → Port
  | .fuel => .fuel | .acc => .word (.crossing, i) | .factor => .word (.delta, i)
  | .scratch => .scratch false | .zero => .zero

def addDecode (i : Index) : Port → Option RepeatedAdd.Port
  | .fuel => some .fuel | .zero => some .zero | .scratch false => some .scratch
  | .word p => if p = (.crossing, i) then some .acc else
      if p = (.delta, i) then some .factor else none
  | _ => none

def addBinding (i : Index) : FinitePortBinding RepeatedAdd.Port Port where
  ports := ⟨addPort i, by rcases i with ⟨s, b⟩; cases s <;> cases b <;> decide +kernel⟩
  decode := addDecode i
  decode_spec := by rcases i with ⟨s, b⟩; cases s <;> cases b <;> decide +kernel

inductive Label
  | first (guard : Bool) (pc : SignedPair.Label)
  | second (gate : Bool) (pc : SignedPair.Label)
  | add (i : Index) (answer : Bool) (pc : RepeatedAdd.Label)
  | done (answer : Bool)
  deriving DecidableEq, Fintype

def compareLabel (second gate : Bool) : SignedPair.Label → Label :=
  if second then Label.second gate else Label.first gate

def nextAdd (i : Index) (r : Bool) : Label :=
  match i with
  | (false, false) => .add (false, true) r (.counter 0)
  | (false, true) => .add (true, false) r (.counter 0)
  | (true, false) => .add (true, true) r (.counter 0)
  | (true, true) => .done r

def program : Microcode.Program Port Label
  | .first guard (.done r) =>
      .jump (.second (guard && decide (r = .less)) (.add false (.scan false false)))
  | .first guard pc =>
      (compareBinding false).instruction (Label.first guard) (SignedPair.program pc)
  | .second gate (.done r) =>
      .jump (.add (false, false) (gate && decide (r = .less)) (.counter 0))
  | .second gate pc =>
      (compareBinding true).instruction (Label.second gate) (SignedPair.program pc)
  | .add i r (.counter pc) => if pc = 12 then .jump (nextAdd i r) else
      (addBinding i).instruction (Label.add i r) (RepeatedAdd.program (.counter pc))
  | .add i r pc => (addBinding i).instruction (Label.add i r) (RepeatedAdd.program pc)
  | .done _ => .halt

theorem compare_code (second gate : Bool) (pc : SignedPair.Label)
    (hh : SignedPair.program pc ≠ .halt) (_ : SignedPair.program pc ≠ .reject) :
    program (compareLabel second gate pc) =
      MicrocodeEmbedding.instruction (compareBinding second).ports (compareLabel second gate)
        (SignedPair.program pc) := by
  cases second <;> cases pc <;>
    simp_all [compareLabel, program, SignedPair.program, FinitePortBinding.instruction_eq]

theorem add_code (i : Index) (r : Bool) (pc : RepeatedAdd.Label)
    (hh : RepeatedAdd.program pc ≠ .halt) (_ : RepeatedAdd.program pc ≠ .reject) :
    program (.add i r pc) = MicrocodeEmbedding.instruction (addBinding i).ports
      (Label.add i r) (RepeatedAdd.program pc) := by
  cases pc with
  | counter pc =>
    have hn : pc ≠ 12 := by
      intro h; subst pc
      exact hh rfl
    simp [program, hn, FinitePortBinding.instruction_eq]
  | arithmetic copy pc => simp [program, FinitePortBinding.instruction_eq]
  | clear scratch pc => simp [program, FinitePortBinding.instruction_eq]

abbrev Bank := Port → Tape Bool

def ready (m : ℕ) (w : Words) : Bank
  | .word p => BinaryCarry.marked (w p)
  | .fuel => Counter.marked [true]
  | .zero => BinaryCarry.marked (List.replicate m false)
  | .scratch _ => BinaryCarry.preparedOutput

def cfg (pc : Label) (b : Bank) (pos : Port → ℤ) : NativeMicrocode.Config Port Label :=
  ⟨⟨pc, fun t => (b t).denote⟩, pos⟩

def zipperCfg (pc : Label) (b : Bank) (pos : Port → ℤ) : NativeZipper.Config Port Label :=
  ⟨⟨pc, b⟩, pos⟩

def frame (b : Bank) (pos : Port → ℤ) : MicrocodeEmbedding.Frame Port :=
  ⟨fun t => (b t).denote, pos⟩

noncomputable def nativeEncoding :=
  NativeMicrocode.initialEncoding (T := Port) (Label.first false (.add false (.scan false false)))

noncomputable def nativeMachine : Transpose.TM := NativeMicrocode.machine nativeEncoding program

theorem fixed_resources : nativeMachine.k = 16 ∧ nativeMachine.g + 1 = 5 ∧
    nativeMachine.q + 1 = 1422 ∧
    nativeEncoding.label (.first false (.add false (.scan false false))) = 0 := by
  refine ⟨?_, rfl, ?_, NativeMicrocode.initialEncoding_start _⟩
  · change Fintype.card Port = 16
    decide +kernel
  · change Fintype.card Label - 1 + 1 = 1422
    decide +kernel

end TransposeFollowup.RowCell


/-! Concrete embeddings of the proved signed comparison and in-place update
into the actual cell program. All unused tapes and absolute heads are framed. -/

namespace TransposeFollowup.RowCell

open FixedTapeCompiler
set_option autoImplicit false

theorem embed_compare (second gate : Bool) (pc : SignedPair.Label)
    (m : ℕ) (w : Words) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed (compareBinding second).ports (compareLabel second gate)
      (SignedPair.cfg pc (SignedPair.ready (w (compareA second)) (w (compareB second))
        (w (compareC second)) (w (compareD second)))
        (fun p => pos ((compareBinding second).ports p))) (frame (ready m w) pos) =
      cfg (compareLabel second gate pc) (ready m w) pos := by
  unfold MicrocodeEmbedding.embed SignedPair.cfg cfg frame
  simp only [← (compareBinding second).values_eq_extend]
  cases second <;> congr 2
  all_goals
    funext t
    cases t with
    | word p =>
      rcases p with ⟨g, side, sign⟩
      cases g <;> cases side <;> cases sign <;> rfl
    | fuel => rfl
    | zero => rfl
    | scratch right => cases right <;> rfl

theorem embed_add (i : Index) (r : Bool) (pc : RepeatedAdd.Label)
    (m : ℕ) (w : Words) (a : List Bool)
    (h : (w (.delta, i)).length = m) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed (addBinding i).ports (Label.add i r)
      (RepeatedAdd.cfg pc (RepeatedAdd.ready [true] a (w (.delta, i)))
        (fun p => pos ((addBinding i).ports p))) (frame (ready m w) pos) =
      cfg (.add i r pc) (ready m (Function.update w (.crossing, i) a)) pos := by
  unfold MicrocodeEmbedding.embed RepeatedAdd.cfg cfg frame
  simp only [← (addBinding i).values_eq_extend, RepeatedAdd.ready, h]
  rcases i with ⟨s, b⟩
  cases s <;> cases b <;> congr 2
  all_goals
    funext t
    cases t with
    | word p =>
      rcases p with ⟨g, side, sign⟩
      cases g <;> cases side <;> cases sign <;> rfl
    | fuel => rfl
    | zero => rfl
    | scratch right => cases right <;> rfl

abbrev Trace := OperationalTrace.Trace (NativeMicrocode.step program) (NativeMicrocode.Active program)

theorem jump_trace (pc next : Label) (m : ℕ) (w : Words) (pos : Port → ℤ)
    (h : program pc = .jump next) : Trace 1 (cfg pc (ready m w) pos) (cfg next (ready m w) pos) :=
  NativeMicrocode.jump_trace _ _ _ h

theorem compare_call (second gate : Bool) (m : ℕ) (w : Words) (h : Width m w)
    (pos : Port → ℤ) :
    ∃ t ≤ 23*m+37,
      Trace t (cfg (compareLabel second gate (.add false (.scan false false))) (ready m w) pos)
        (cfg (compareLabel second gate (.done (comparison second w))) (ready m w) pos) := by
  obtain ⟨t, ht, htr⟩ := SignedPair.comparison_trace
    (w (compareA second)) (w (compareB second)) (w (compareC second)) (w (compareD second))
    ((h _).trans (h _).symm) ((h _).trans (h _).symm) ((h _).trans (h _).symm)
    (fun p => pos ((compareBinding second).ports p))
  have he := MicrocodeEmbedding.trace_embed (compareBinding second).ports (compareLabel second gate)
    SignedPair.program program (frame (ready m w) pos) (compare_code second gate) htr
  refine ⟨t, by simpa only [h (compareD second)] using ht, ?_⟩
  simpa only [embed_compare, comparison] using he

theorem add_call (i : Index) (r : Bool) (m : ℕ) (w : Words) (h : Width m w)
    (pos : Port → ℤ) :
    ∃ t ≤ 18*m+51,
      Trace t (cfg (.add i r (.counter 0)) (ready m w) pos)
        (cfg (.add i r (.counter 12)) (ready m (update w i)) pos) := by
  obtain ⟨t, ht, htr⟩ := RepeatedAdd.single_add_trace
    (w (.crossing, i)) (w (.delta, i)) ((h _).trans (h _).symm)
    (fun p => pos ((addBinding i).ports p))
  have he := MicrocodeEmbedding.trace_embed (addBinding i).ports (Label.add i r)
    RepeatedAdd.program program (frame (ready m w) pos) (add_code i r) htr
  refine ⟨t, by simpa only [h (.delta, i)] using ht, ?_⟩
  simpa only [embed_add i r _ m w _ (h _), Function.update_eq_self, update] using he

end TransposeFollowup.RowCell


/-! Complete cell execution: two comparisons, four updates and six actual
linking jumps. The returned flag concerns the old crossing state, while the
four crossing words have advanced. The initial source-open guard is explicit. -/

namespace TransposeFollowup.RowCell

open FixedTapeCompiler
set_option autoImplicit false

theorem cell_trace (guard : Bool) (m : ℕ) (w : Words) (h : Width m w) (pos : Port → ℤ) :
    ∃ t ≤ 118*m+284,
      Trace t (cfg (.first guard (.add false (.scan false false))) (ready m w) pos)
        (cfg (.done (answer guard w)) (ready m (updateAll w)) pos) := by
  let gate := guard && decide (comparison false w = .less)
  let r := answer guard w
  let w1 := update w (false, false)
  let w2 := update w1 (false, true)
  let w3 := update w2 (true, false)
  let w4 := update w3 (true, true)
  have h1 : Width m w1 := update_width m w h _
  have h2 : Width m w2 := update_width m w1 h1 _
  have h3 : Width m w3 := update_width m w2 h2 _
  obtain ⟨t1, ht1, tr1⟩ := compare_call false guard m w h pos
  obtain ⟨t2, ht2, tr2⟩ := compare_call true gate m w h pos
  obtain ⟨t3, ht3, tr3⟩ := add_call (false, false) r m w h pos
  obtain ⟨t4, ht4, tr4⟩ := add_call (false, true) r m w1 h1 pos
  obtain ⟨t5, ht5, tr5⟩ := add_call (true, false) r m w2 h2 pos
  obtain ⟨t6, ht6, tr6⟩ := add_call (true, true) r m w3 h3 pos
  have j1 := jump_trace (.first guard (.done (comparison false w)))
    (.second gate (.add false (.scan false false))) m w pos rfl
  have j2 := jump_trace (.second gate (.done (comparison true w)))
    (.add (false, false) r (.counter 0)) m w pos rfl
  have j3 := jump_trace (.add (false, false) r (.counter 12))
    (.add (false, true) r (.counter 0)) m w1 pos rfl
  have j4 := jump_trace (.add (false, true) r (.counter 12))
    (.add (true, false) r (.counter 0)) m w2 pos rfl
  have j5 := jump_trace (.add (true, false) r (.counter 12))
    (.add (true, true) r (.counter 0)) m w3 pos rfl
  have j6 := jump_trace (.add (true, true) r (.counter 12)) (.done r) m w4 pos rfl
  have whole := NativeCountedLoop.trace_trans tr1 (NativeCountedLoop.trace_trans j1
    (NativeCountedLoop.trace_trans tr2 (NativeCountedLoop.trace_trans j2
      (NativeCountedLoop.trace_trans tr3 (NativeCountedLoop.trace_trans j3
        (NativeCountedLoop.trace_trans tr4 (NativeCountedLoop.trace_trans j4
          (NativeCountedLoop.trace_trans tr5 (NativeCountedLoop.trace_trans j5
            (NativeCountedLoop.trace_trans tr6 j6))))))))))
  refine ⟨_, ?_, whole⟩
  omega

theorem native_cell (guard : Bool) (m : ℕ) (words : Words) (h : Width m words)
    (pos : Port → ℤ) (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ 118*m+284,
      Transpose.stepN nativeMachine input t
        ((cfg (.first guard (.add false (.scan false false))) (ready m words) pos).denote
          nativeEncoding program inputPos outRev) =
        some ((cfg (.done (answer guard words)) (ready m (updateAll words)) pos).denote
          nativeEncoding program inputPos outRev) ∧
      Transpose.step nativeMachine input
        ((cfg (.done (answer guard words)) (ready m (updateAll words)) pos).denote
          nativeEncoding program inputPos outRev) = none := by
  obtain ⟨t, ht, htr⟩ := cell_trace guard m words h pos
  refine ⟨t, ht, NativeMicrocode.trace_stepN nativeEncoding program input inputPos outRev htr, ?_⟩
  apply (NativeMicrocode.step_none_iff nativeEncoding program input inputPos outRev _).mpr
  simp [NativeMicrocode.Active, cfg, program]

theorem native_call {U J : Type*} {k q : ℕ}
    (encoding : NativeMicrocode.Encoding U J k q) (ports : Port ↪ U)
    (labels : Label → J) (target : Microcode.Program U J)
    (outerFrame : MicrocodeEmbedding.Frame U)
    (hc : ∀ pc, program pc ≠ .halt → program pc ≠ .reject →
      target (labels pc) = MicrocodeEmbedding.instruction ports labels (program pc))
    (guard : Bool) (m : ℕ) (words : Words) (h : Width m words) (pos : Port → ℤ)
    (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ 118*m+284,
      Transpose.stepN (NativeMicrocode.machine encoding target) input t
        ((MicrocodeEmbedding.embed ports labels
          (cfg (.first guard (.add false (.scan false false))) (ready m words) pos)
          outerFrame).denote encoding target inputPos outRev) =
        some ((MicrocodeEmbedding.embed ports labels
          (cfg (.done (answer guard words)) (ready m (updateAll words)) pos)
          outerFrame).denote encoding target inputPos outRev) := by
  obtain ⟨t, ht, htr⟩ := cell_trace guard m words h pos
  exact ⟨t, ht, MicrocodeEmbedding.native_call encoding ports labels program target
    outerFrame input inputPos outRev hc htr⟩

end TransposeFollowup.RowCell


/-! Interpret the actual cell words as the nonnegative components of the
proved row circuit. Explicit comparison/update fits give exact arithmetic.
The Mobius component-width theorem supplies those fits through j=n. -/

namespace TransposeFollowup.RowCell

open SignedComponents
open BinaryCompare (value)
set_option autoImplicit false

def component (p : Pair) (sign : Bool) : ℕ := if sign then p.negative else p.positive

def pairAt (r : ComponentRow) (j : ℕ) (g : Group) (side : Bool) : Pair :=
  match g with
  | .threshold => if side then r.upper else r.lower
  | .crossing => let v := SignedComponents.scan r.deltaLeft r.deltaRight j
                if side then v.2 else v.1
  | .delta => if side then r.deltaRight else r.deltaLeft

def expected (r : ComponentRow) (j : ℕ) (p : WordPort) : ℕ :=
  component (pairAt r j p.1 p.2.1) p.2.2

def Represents (m : ℕ) (w : Words) (r : ComponentRow) (j : ℕ) : Prop :=
  Width m w ∧ ∀ p, value (w p) = expected r j p

def compareLeft (second : Bool) (r : ComponentRow) (j : ℕ) : Pair :=
  if second then (SignedComponents.scan r.deltaLeft r.deltaRight j).2 else r.lower

def compareRight (second : Bool) (r : ComponentRow) (j : ℕ) : Pair :=
  if second then r.upper else (SignedComponents.scan r.deltaLeft r.deltaRight j).1

def ComparisonFits (m : ℕ) (w : Words) : Prop := ∀ second,
  value (w (compareA second)) + value (w (compareD second)) < 2^m ∧
  value (w (compareC second)) + value (w (compareB second)) < 2^m

def UpdateFits (m : ℕ) (w : Words) : Prop := ∀ i,
  value (w (.crossing, i)) + value (w (.delta, i)) < 2^m

theorem compare_values (m : ℕ) (w : Words) (r : ComponentRow) (j : ℕ)
    (h : Represents m w r j) (second : Bool) :
    value (w (compareA second)) = (compareLeft second r j).positive ∧
    value (w (compareB second)) = (compareLeft second r j).negative ∧
    value (w (compareC second)) = (compareRight second r j).positive ∧
    value (w (compareD second)) = (compareRight second r j).negative := by
  cases second <;> exact ⟨h.2 _, h.2 _, h.2 _, h.2 _⟩

theorem comparison_exact (m : ℕ) (w : Words) (r : ComponentRow) (j : ℕ)
    (h : Represents m w r j) (hf : ComparisonFits m w) (second : Bool) :
    comparison second w = SignedPair.numeric (compareLeft second r j).denote
      (compareRight second r j).denote := by
  have hv := compare_values m w r j h second
  unfold comparison
  rw [SignedPair.result_spec _ _ _ _ ((h.1 _).trans (h.1 _).symm)
    ((h.1 _).trans (h.1 _).symm)
    (by simpa only [h.1 (compareD second)] using (hf second).1)
    (by simpa only [h.1 (compareB second)] using (hf second).2)]
  simp only [SignedPair.integer, hv.1, hv.2.1, hv.2.2.1, hv.2.2.2, Pair.denote]

theorem answer_exact (m : ℕ) (w : Words) (r : ComponentRow) (j : ℕ)
    (h : Represents m w r j) (hf : ComparisonFits m w) :
    answer (r.sourceLeft.less r.sourceRight) w = r.hit j := by
  unfold answer
  rw [comparison_exact m w r j h hf false, comparison_exact m w r j h hf true]
  apply Bool.eq_iff_iff.mpr
  simp only [ComponentRow.hit, compareLeft, compareRight, Bool.false_eq_true, ite_false,
    ite_true, Bool.and_eq_true, decide_eq_true_eq, SignedPair.numeric_less, less_spec]

theorem expected_next (r : ComponentRow) (j : ℕ) (i : Index) :
    expected r (j+1) (.crossing, i) = expected r j (.crossing, i) + expected r j (.delta, i) := by
  rcases i with ⟨side, sign⟩
  cases side <;> cases sign <;> rfl

theorem updateAll_represents (m : ℕ) (w : Words) (r : ComponentRow) (j : ℕ)
    (h : Represents m w r j) (hf : UpdateFits m w) :
    Represents m (updateAll w) r (j+1) := by
  refine ⟨updateAll_width m w h.1, ?_⟩
  rintro ⟨g, i⟩
  rw [updateAll_apply]
  cases g with
  | threshold => exact h.2 (.threshold, i)
  | delta => exact h.2 (.delta, i)
  | crossing =>
    simp only [ite_true]
    rw [RepeatedAdd.addWord_value _ _ ((h.1 _).trans (h.1 _).symm), h.1 (.delta, i),
      Nat.mod_eq_of_lt (hf i), h.2 _, h.2 _, expected_next]

theorem component_le_mass (p : Pair) (sign : Bool) : component p sign ≤ p.mass := by
  cases sign <;> dsimp [component, Pair.mass] <;> omega

theorem comparisonFits_of_row (F : RationalMobius) {n : ℕ} (i : Fin n)
    (j : ℕ) (hj : j ≤ n) (w : Words)
    (h : Represents (F.componentWidth n) w (F.componentRow i) j) :
    ComparisonFits (F.componentWidth n) w := by
  have hf := F.componentRow_comparison_fit i j hj
  dsimp only at hf
  intro second
  have hv := compare_values _ w _ j h second
  rw [hv.1, hv.2.1, hv.2.2.1, hv.2.2.2]
  cases second <;> constructor
  all_goals apply hf <;> simp [compareLeft, compareRight]

theorem updateFits_of_row (F : RationalMobius) {n : ℕ} (i : Fin n)
    (j : ℕ) (hj : j < n) (w : Words)
    (h : Represents (F.componentWidth n) w (F.componentRow i) j) :
    UpdateFits (F.componentWidth n) w := by
  let r := F.componentRow i
  have hf := F.componentRow_comparison_fit i (j+1) (by omega)
  dsimp only at hf
  rintro ⟨side, sign⟩
  have hm : (pairAt r (j+1) .crossing side).mass < 2^F.componentWidth n := by
    cases side
    · exact hf _ (by simp [pairAt, r]) _ (by simp [pairAt, r])
    · exact hf _ (by simp [pairAt, r]) _ (by simp [pairAt, r])
  have hc := (component_le_mass (pairAt r (j+1) .crossing side) sign).trans_lt hm
  change expected r (j+1) (.crossing, side, sign) < _ at hc
  rw [expected_next] at hc
  simpa only [h.2 (.crossing, side, sign), h.2 (.delta, side, sign)] using hc

theorem rational_cell_trace (F : RationalMobius) {n : ℕ} (i : Fin n)
    (j : ℕ) (hj : j < n) (w : Words)
    (h : Represents (F.componentWidth n) w (F.componentRow i) j) (pos : Port → ℤ) :
    ∃ t ≤ 118*F.componentWidth n+284,
      Trace t (cfg (.first ((F.componentRow i).sourceLeft.less (F.componentRow i).sourceRight)
        (.add false (.scan false false))) (ready (F.componentWidth n) w) pos)
        (cfg (.done (F.denseHit i j)) (ready (F.componentWidth n) (updateAll w)) pos) ∧
      Represents (F.componentWidth n) (updateAll w) (F.componentRow i) (j+1) := by
  obtain ⟨t, ht, htr⟩ := cell_trace
    ((F.componentRow i).sourceLeft.less (F.componentRow i).sourceRight)
    (F.componentWidth n) w h.1 pos
  rw [answer_exact _ w _ j h (comparisonFits_of_row F i j hj.le w h), F.componentRow_hit] at htr
  exact ⟨t, ht, htr, updateAll_represents _ w _ j h (updateFits_of_row F i j hj w h)⟩

/-- Exact rational overlap and next-state interpretation in the original TM.
The guard, all twelve words, zero/fuel and scratch markers are prepared inputs. -/
theorem native_rational_cell (F : RationalMobius) {n : ℕ} (i : Fin n)
    (j : ℕ) (hj : j < n) (w : Words)
    (h : Represents (F.componentWidth n) w (F.componentRow i) j) (pos : Port → ℤ)
    (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ 118*F.componentWidth n+284,
      Transpose.stepN nativeMachine input t
        ((cfg (.first ((F.componentRow i).sourceLeft.less (F.componentRow i).sourceRight)
          (.add false (.scan false false))) (ready (F.componentWidth n) w) pos).denote
          nativeEncoding program inputPos outRev) =
        some ((cfg (.done (F.denseHit i j)) (ready (F.componentWidth n) (updateAll w)) pos).denote
          nativeEncoding program inputPos outRev) ∧
      Transpose.step nativeMachine input
        ((cfg (.done (F.denseHit i j)) (ready (F.componentWidth n) (updateAll w)) pos).denote
          nativeEncoding program inputPos outRev) = none ∧
      Represents (F.componentWidth n) (updateAll w) (F.componentRow i) (j+1) := by
  obtain ⟨t, ht, htr, hrep⟩ := rational_cell_trace F i j hj w h pos
  refine ⟨t, ht, NativeMicrocode.trace_stepN nativeEncoding program input inputPos outRev htr, ?_, hrep⟩
  apply (NativeMicrocode.step_none_iff nativeEncoding program input inputPos outRev _).mpr
  simp [NativeMicrocode.Active, cfg, program]


end TransposeFollowup.RowCell


/-! Sum of actual native cell budgets. The row counter, loading, emitting
records and complete generator are not yet included in this sum. -/

namespace TransposeFollowup.RowCell
set_option autoImplicit false

theorem total_budget_le_input (A B n m : ℕ) (hn : 1 ≤ n)
    (hm : m ≤ A + B*(n+1).size) :
    n * (n * (118*m+284)) ≤
      2 * ((118*A+284)+3*(118*B)) * Transpose.inputLength n := by
  calc
    _ ≤ n * (n * ((118*A+284)+(118*B)*(n+1).size)) := by
      apply Nat.mul_le_mul_left
      apply Nat.mul_le_mul_left
      nlinarith
    _ ≤ _ := dense_scan_budget (118*A+284) (118*B) n hn

theorem rational_total_budget (F : RationalMobius) (n : ℕ) (hn : 1 ≤ n) :
    n * (n * (118*F.componentWidth n+284)) ≤
      (236*(F.integerOperandConstant^2).size+2456) * Transpose.inputLength n := by
  have h := total_budget_le_input ((F.integerOperandConstant^2).size+2) 2 n
    (F.componentWidth n) hn (by unfold RationalMobius.componentWidth; omega)
  have hc : 2*((118*((F.integerOperandConstant^2).size+2)+284)+3*(118*2)) =
      236*(F.integerOperandConstant^2).size+2456 := by omega
  simpa only [hc] using h

end TransposeFollowup.RowCell


/-! Logical state of a counted row traversal. Appending to the list here is
only the specification of one physical output write, proved in the caller. -/

namespace TransposeFollowup.RowStream

open FixedTapeCompiler
open CopyMachine (Tape Sym symbols)
set_option autoImplicit false

structure State (m : ℕ) where
  words : RowCell.Words
  width : RowCell.Width m words
  written : List Bool

def State.appendBit {m : ℕ} (s : State m) (b : Bool) : State m :=
  {s with written := s.written ++ [b]}

def State.afterCell {m : ℕ} (s : State m) : State m :=
  {s with words := RowCell.updateAll s.words, width := RowCell.updateAll_width m s.words s.width}

def advance {m : ℕ} (guard : Bool) (s : State m) : State m :=
  s.afterCell.appendBit (RowCell.answer guard s.words)

def process {m : ℕ} (guard : Bool) : ℕ → State m → State m
  | 0, s => s
  | n+1, s => process guard n (advance guard s)

def flags (guard : Bool) : ℕ → RowCell.Words → List Bool
  | 0, _ => []
  | n+1, w => RowCell.answer guard w :: flags guard n (RowCell.updateAll w)

theorem flags_length (guard : Bool) (n : ℕ) (w : RowCell.Words) :
    (flags guard n w).length = n := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih => simp [flags, ih]

theorem process_written {m : ℕ} (guard : Bool) (n : ℕ) (s : State m) :
    (process guard n s).written = s.written ++ flags guard n s.words := by
  induction n generalizing s with
  | zero => simp [process, flags]
  | succ n ih =>
    simpa [process, advance, State.appendBit, State.afterCell, flags, List.append_assoc] using
      ih (advance guard s)

theorem process_length {m : ℕ} (guard : Bool) (n : ℕ) (s : State m) :
    (process guard n s).written.length = s.written.length + n := by
  rw [process_written, List.length_append, flags_length]

def openTape (written : List Bool) : Tape Bool := ⟨symbols written.reverse ++ [.start], []⟩

def closedTape (written : List Bool) : Tape Bool :=
  ⟨symbols written.reverse ++ [.start], [.stop]⟩

theorem append_tape (written : List Bool) (b : Bool) :
    ((openTape written).write (.data b)).moveRight = openTape (written ++ [b]) := by
  simp [openTape, Tape.write, Tape.moveRight, Tape.read, symbols, List.reverse_append]

theorem close_tape (written : List Bool) :
    (openTape written).write .stop = closedTape written := rfl

end TransposeFollowup.RowStream


/-! A physical countdown calls the actual cell, writes one returned bit and
moves the stream head one cell. The source-open flag is retained in finite
labels. A final paid STOP write closes the stream without a free rewind. -/

namespace TransposeFollowup.RowStream

open FixedTapeCompiler
open CopyMachine (Tape Sym)
set_option autoImplicit false

inductive Port | cell (t : RowCell.Port) | counter | stream
  deriving DecidableEq, Fintype

def cellBinding : FinitePortBinding RowCell.Port Port where
  ports := ⟨Port.cell, fun _ _ h => Port.cell.inj h⟩
  decode := fun p => match p with | .cell t => some t | _ => none
  decode_spec := by
    intro p t
    change (match p with | .cell u => some u | _ => none) = some t ↔ Port.cell t = p
    cases p <;> simp [eq_comm]

def counterBinding : FinitePortBinding (Fin 1) Port where
  ports := ⟨fun _ => .counter, fun _ _ _ => Subsingleton.elim _ _⟩
  decode := fun p => match p with | .counter => some 0 | _ => none
  decode_spec := by
    intro p t
    fin_cases t
    change (match p with | .counter => some (0 : Fin 1) | _ => none) = some 0 ↔ Port.counter = p
    cases p <;> simp

inductive Label
  | counter (guard : Bool) (pc : Microcode.DecrementFamily.Label)
  | cell (guard : Bool) (pc : RowCell.Label)
  | emit (guard bit : Bool)
  | done (guard : Bool)
  deriving DecidableEq, Fintype

def program : Microcode.Program Port Label
  | .counter guard pc =>
      if pc = 11 then .jump (.cell guard (.first guard (.add false (.scan false false))))
      else if pc = 12 then .act (Microcode.single .stream ⟨some .stop, .stay⟩) (.done guard)
      else counterBinding.instruction (Label.counter guard) (Microcode.DecrementFamily.program pc)
  | .cell guard (.done bit) => .jump (.emit guard bit)
  | .cell guard pc => cellBinding.instruction (Label.cell guard) (RowCell.program pc)
  | .emit guard bit =>
      .act (Microcode.single .stream ⟨some (.data bit), .right⟩) (.counter guard 0)
  | .done _ => .halt

theorem counter_code (guard : Bool) (pc : Microcode.DecrementFamily.Label)
    (hh : Microcode.DecrementFamily.program pc ≠ .halt)
    (_ : Microcode.DecrementFamily.program pc ≠ .reject) :
    program (.counter guard pc) = MicrocodeEmbedding.instruction counterBinding.ports
      (Label.counter guard) (Microcode.DecrementFamily.program pc) := by
  have h11 : pc ≠ 11 := by intro h; subst pc; exact hh rfl
  have h12 : pc ≠ 12 := by intro h; subst pc; exact hh rfl
  simp [program, h11, h12, FinitePortBinding.instruction_eq]

theorem cell_code (guard : Bool) (pc : RowCell.Label)
    (hh : RowCell.program pc ≠ .halt) (_ : RowCell.program pc ≠ .reject) :
    program (.cell guard pc) = MicrocodeEmbedding.instruction cellBinding.ports
      (Label.cell guard) (RowCell.program pc) := by
  cases pc <;> simp_all [program, RowCell.program, FinitePortBinding.instruction_eq]

def bank {m : ℕ} (closed : Bool) (fuel : List Bool) (s : State m) : Port → Tape Bool
  | .cell t => RowCell.ready m s.words t
  | .counter => Counter.marked fuel
  | .stream => if closed then closedTape s.written else openTape s.written

def positions (pos : Port → ℤ) (written : List Bool) : Port → ℤ
  | .stream => pos .stream + written.length
  | p => pos p

def config {m : ℕ} (closed : Bool) (pc : Label) (fuel : List Bool)
    (s : State m) (pos : Port → ℤ) : NativeMicrocode.Config Port Label :=
  ⟨⟨pc, fun p => (bank closed fuel s p).denote⟩, positions pos s.written⟩

abbrev cfg {m : ℕ} := @config m false
abbrev finishedCfg {m : ℕ} := @config m true

def zipperCfg {m : ℕ} (closed : Bool) (pc : Label) (fuel : List Bool)
    (s : State m) (pos : Port → ℤ) : NativeZipper.Config Port Label :=
  ⟨⟨pc, bank closed fuel s⟩, positions pos s.written⟩

def frame {m : ℕ} (fuel : List Bool) (s : State m) (pos : Port → ℤ) :
    MicrocodeEmbedding.Frame Port :=
  ⟨fun p => (bank false fuel s p).denote, positions pos s.written⟩

noncomputable def nativeEncoding :=
  NativeMicrocode.initialEncoding (T := Port) (Label.counter false 0)

noncomputable def nativeMachine : Transpose.TM := NativeMicrocode.machine nativeEncoding program

theorem fixed_resources : nativeMachine.k = 18 ∧ nativeMachine.g + 1 = 5 ∧
    nativeMachine.q + 1 = 2876 ∧ nativeEncoding.label (.counter false 0) = 0 := by
  refine ⟨?_, rfl, ?_, NativeMicrocode.initialEncoding_start _⟩
  · change Fintype.card Port = 18
    decide +kernel
  · change Fintype.card Label - 1 + 1 = 2876
    decide +kernel

end TransposeFollowup.RowStream


/-! Exact subroutine frames plus the physical stream writes. The stream
head advances once per emitted bit; STOP is written without moving it. -/

namespace TransposeFollowup.RowStream

open FixedTapeCompiler
open CopyMachine (Tape Sym)
set_option autoImplicit false

theorem embed_cell {m : ℕ} (guard : Bool) (pc : RowCell.Label) (fuel : List Bool)
    (s : State m) (words : RowCell.Words) (h : RowCell.Width m words) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed cellBinding.ports (Label.cell guard)
      (RowCell.cfg pc (RowCell.ready m words) (fun t => pos (.cell t))) (frame fuel s pos) =
      cfg (.cell guard pc) fuel ⟨words, h, s.written⟩ pos := by
  unfold MicrocodeEmbedding.embed RowCell.cfg cfg config frame
  simp only [← cellBinding.values_eq_extend]
  congr 2 <;> funext p <;> cases p <;> rfl

theorem embed_counter {m : ℕ} (guard : Bool) (pc : Microcode.DecrementFamily.Label)
    (fuel : List Bool) (s : State m) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed counterBinding.ports (Label.counter guard)
      (NativeCounter.cfg pc fuel (fun _ => pos .counter)).denote (frame [] s pos) =
      cfg (.counter guard pc) fuel s pos := by
  unfold MicrocodeEmbedding.embed NativeZipper.Config.denote Microcode.Config.denote
    NativeCounter.cfg Microcode.focus cfg config frame
  simp only [← counterBinding.values_eq_extend]
  congr 2 <;> funext p <;> cases p <;> rfl

abbrev Trace := OperationalTrace.Trace (NativeMicrocode.step program) (NativeMicrocode.Active program)

theorem jump_trace {m : ℕ} (pc next : Label) (fuel : List Bool) (s : State m) (pos : Port → ℤ)
    (h : program pc = .jump next) : Trace 1 (cfg pc fuel s pos) (cfg next fuel s pos) :=
  NativeMicrocode.jump_trace _ _ _ h

theorem cell_call {m : ℕ} (guard : Bool) (fuel : List Bool) (s : State m) (pos : Port → ℤ) :
    ∃ t ≤ 118*m+284,
      Trace t (cfg (.cell guard (.first guard (.add false (.scan false false)))) fuel s pos)
        (cfg (.cell guard (.done (RowCell.answer guard s.words))) fuel s.afterCell pos) := by
  obtain ⟨t, ht, htr⟩ := RowCell.cell_trace guard m s.words s.width (fun t => pos (.cell t))
  have he := MicrocodeEmbedding.trace_embed cellBinding.ports (Label.cell guard)
    RowCell.program program (frame fuel s pos) (cell_code guard) htr
  rw [embed_cell guard _ fuel s s.words s.width pos,
    embed_cell guard _ fuel s (RowCell.updateAll s.words)
      (RowCell.updateAll_width m s.words s.width) pos] at he
  exact ⟨t, ht, he⟩

theorem emit_tapes {m : ℕ} (fuel : List Bool) (s : State m) (bit : Bool) :
    (fun p => (Microcode.single Port.stream ⟨some (.data bit), .right⟩ p).apply
      (bank false fuel s p)) = bank false fuel (s.appendBit bit) := by
  funext p
  cases p with
  | cell t => rfl
  | counter => rfl
  | stream => exact append_tape s.written bit

theorem emit_positions (pos : Port → ℤ) (written : List Bool) (bit : Bool) :
    (fun p => (NativeMicrocode.direction
      (Microcode.single Port.stream ⟨some (.data bit), .right⟩ p).move).shift
        (positions pos written p)) = positions pos (written ++ [bit]) := by
  funext p
  cases p with
  | cell t => rfl
  | counter => rfl
  | stream =>
    change (pos .stream + written.length) + 1 = pos .stream + (written ++ [bit]).length
    simp
    ring

theorem emit_step {m : ℕ} (guard bit : Bool) (fuel : List Bool) (s : State m) (pos : Port → ℤ) :
    NativeZipper.step program (zipperCfg false (.emit guard bit) fuel s pos) =
      zipperCfg false (.counter guard 0) fuel (s.appendBit bit) pos := by
  simp only [NativeZipper.step, Microcode.step, program, zipperCfg, emit_tapes, emit_positions,
    State.appendBit]

theorem emit_trace {m : ℕ} (guard bit : Bool) (fuel : List Bool) (s : State m) (pos : Port → ℤ) :
    Trace 1 (cfg (.emit guard bit) fuel s pos)
      (cfg (.counter guard 0) fuel (s.appendBit bit) pos) := by
  have he := congrArg NativeZipper.Config.denote (emit_step guard bit fuel s pos)
  rw [NativeZipper.step_denote] at he
  change NativeMicrocode.step program (cfg (.emit guard bit) fuel s pos) =
    cfg (.counter guard 0) fuel (s.appendBit bit) pos at he
  apply OperationalTrace.Trace.cons
  · simp [NativeMicrocode.Active, config, program]
  · rw [he]
    exact .refl _

theorem finish_tapes {m : ℕ} (fuel : List Bool) (s : State m) :
    (fun p => (Microcode.single Port.stream ⟨some .stop, .stay⟩ p).apply
      (bank false fuel s p)) = bank true fuel s := by
  funext p
  cases p <;> rfl

theorem finish_step {m : ℕ} (guard : Bool) (fuel : List Bool) (s : State m) (pos : Port → ℤ) :
    NativeZipper.step program (zipperCfg false (.counter guard 12) fuel s pos) =
      zipperCfg true (.done guard) fuel s pos := by
  simp only [NativeZipper.step, Microcode.step, program, zipperCfg]
  change NativeZipper.Config.mk (T := Port) (L := Label) ⟨Label.done guard, _⟩ _ = _
  rw [finish_tapes]
  congr 1
  funext p
  cases p <;> rfl

theorem finish_trace {m : ℕ} (guard : Bool) (fuel : List Bool) (s : State m) (pos : Port → ℤ) :
    Trace 1 (cfg (.counter guard 12) fuel s pos) (finishedCfg (.done guard) fuel s pos) := by
  have he := congrArg NativeZipper.Config.denote (finish_step guard fuel s pos)
  rw [NativeZipper.step_denote] at he
  change NativeMicrocode.step program (cfg (.counter guard 12) fuel s pos) =
    finishedCfg (.done guard) fuel s pos at he
  apply OperationalTrace.Trace.cons
  · simp [NativeMicrocode.Active, config, program]
  · rw [he]
    exact .refl _

theorem body_trace {m : ℕ} (guard : Bool) (fuel : List Bool) (s : State m) (pos : Port → ℤ) :
    ∃ t ≤ 118*m+287,
      Trace t (cfg (.counter guard 11) fuel s pos)
        (cfg (.counter guard 0) fuel (advance guard s) pos) := by
  have j1 := jump_trace (.counter guard 11)
    (.cell guard (.first guard (.add false (.scan false false)))) fuel s pos rfl
  obtain ⟨t, ht, hcell⟩ := cell_call guard fuel s pos
  have j2 := jump_trace (.cell guard (.done (RowCell.answer guard s.words)))
    (.emit guard (RowCell.answer guard s.words)) fuel s.afterCell pos rfl
  have out := emit_trace guard (RowCell.answer guard s.words) fuel s.afterCell pos
  have whole := NativeCountedLoop.trace_trans j1
    (NativeCountedLoop.trace_trans hcell (NativeCountedLoop.trace_trans j2 out))
  exact ⟨1+(t+(1+1)), by omega, whole⟩

end TransposeFollowup.RowStream


/-! Actual counted row traversal, including the final zero check, both
linking jumps per cell, every output-bit write and the terminal STOP write. -/

namespace TransposeFollowup.RowStream

open FixedTapeCompiler
set_option autoImplicit false

def loopUpdate {m : ℕ} (guard : Bool) (_ : List Bool) (s : State m) : State m := advance guard s

def loopFrame {m : ℕ} (pos : Port → ℤ) (s : State m) : MicrocodeEmbedding.Frame Port :=
  frame [] s pos

theorem loop_state {m : ℕ} (guard : Bool) (pos : Port → ℤ)
    (pc : Microcode.DecrementFamily.Label) (fuel : List Bool) (s : State m) :
    NativeCountedLoop.state counterBinding.ports (Label.counter guard) (loopFrame pos)
      (fun _ => pos .counter) pc fuel s = cfg (.counter guard pc) fuel s pos := by
  simp only [NativeCountedLoop.state, loopFrame, embed_counter]

theorem resultState_eq {m : ℕ} (guard : Bool) (n : ℕ) (fuel : List Bool) (s : State m) :
    NativeCountedLoop.resultState (loopUpdate guard) n fuel s = process guard n s := by
  induction n generalizing fuel s with
  | zero => rfl
  | succ n ih =>
    simpa only [NativeCountedLoop.resultState, process, loopUpdate] using
      (ih (Counter.decrement fuel) (advance guard s))

theorem assembled_body {m : ℕ} (guard : Bool) (pos : Port → ℤ)
    (fuel : List Bool) (s : State m) :
    ∃ t ≤ 118*m+287,
      Trace t (NativeCountedLoop.state counterBinding.ports (Label.counter guard) (loopFrame pos)
        (fun _ => pos .counter) 11 fuel s)
        (NativeCountedLoop.state counterBinding.ports (Label.counter guard) (loopFrame pos)
          (fun _ => pos .counter) 0 fuel (loopUpdate guard fuel s)) := by
  simpa only [loop_state, loopUpdate] using body_trace guard fuel s pos

def budget (m : ℕ) (fuel : List Bool) : ℕ :=
  Counter.value fuel*(118*m+287)+8*(Counter.value fuel+1)+4*fuel.length+1

theorem row_trace {m : ℕ} (guard : Bool) (fuel : List Bool) (s : State m) (pos : Port → ℤ) :
    ∃ t ≤ budget m fuel,
      Trace t (cfg (.counter guard 0) fuel s pos)
        (finishedCfg (.done guard) (List.replicate fuel.length true)
          (process guard (Counter.value fuel) s) pos) := by
  obtain ⟨t, ht, htr⟩ := NativeCountedLoop.counted_trace counterBinding.ports
    (Label.counter guard) program (loopFrame pos) (fun _ => pos .counter) (loopUpdate guard)
    fuel.length (118*m+287) (counter_code guard) (fun xs _ st => assembled_body guard pos xs st)
    (Counter.value fuel) fuel s rfl rfl
  have hcost := NativeCounter.native_sequence_budget (Counter.value fuel+1) fuel
  simp only [loop_state, resultState_eq,
    NativeCountedLoop.terminal_word (Counter.value fuel) fuel rfl] at htr
  have final := finish_trace guard (List.replicate fuel.length true)
    (process guard (Counter.value fuel) s) pos
  refine ⟨t+1, ?_, NativeCountedLoop.trace_trans htr final⟩
  unfold budget
  omega

theorem native_row {m : ℕ} (guard : Bool) (fuel : List Bool) (s : State m) (pos : Port → ℤ)
    (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ budget m fuel,
      Transpose.stepN nativeMachine input t
        ((cfg (.counter guard 0) fuel s pos).denote nativeEncoding program inputPos outRev) =
        some ((finishedCfg (.done guard) (List.replicate fuel.length true)
          (process guard (Counter.value fuel) s) pos).denote nativeEncoding program inputPos outRev) ∧
      Transpose.step nativeMachine input
        ((finishedCfg (.done guard) (List.replicate fuel.length true)
          (process guard (Counter.value fuel) s) pos).denote nativeEncoding program inputPos outRev) = none := by
  obtain ⟨t, ht, htr⟩ := row_trace guard fuel s pos
  refine ⟨t, ht, NativeMicrocode.trace_stepN nativeEncoding program input inputPos outRev htr, ?_⟩
  apply (NativeMicrocode.step_none_iff nativeEncoding program input inputPos outRev _).mpr
  simp [NativeMicrocode.Active, config, program]

theorem native_call {U J : Type*} {k q : ℕ} {m : ℕ}
    (encoding : NativeMicrocode.Encoding U J k q) (ports : Port ↪ U)
    (labels : Label → J) (target : Microcode.Program U J)
    (outerFrame : MicrocodeEmbedding.Frame U)
    (hc : ∀ pc, program pc ≠ .halt → program pc ≠ .reject →
      target (labels pc) = MicrocodeEmbedding.instruction ports labels (program pc))
    (guard : Bool) (fuel : List Bool) (s : State m) (pos : Port → ℤ)
    (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ budget m fuel,
      Transpose.stepN (NativeMicrocode.machine encoding target) input t
        ((MicrocodeEmbedding.embed ports labels (cfg (.counter guard 0) fuel s pos)
          outerFrame).denote encoding target inputPos outRev) =
        some ((MicrocodeEmbedding.embed ports labels
          (finishedCfg (.done guard) (List.replicate fuel.length true)
            (process guard (Counter.value fuel) s) pos)
          outerFrame).denote encoding target inputPos outRev) := by
  obtain ⟨t, ht, htr⟩ := row_trace guard fuel s pos
  exact ⟨t, ht, MicrocodeEmbedding.native_call encoding ports labels program target
    outerFrame input inputPos outRev hc htr⟩

theorem final_stream {m : ℕ} (guard : Bool) (n : ℕ) (fuel : List Bool) (s : State m) :
    bank true fuel (process guard n s) .stream = closedTape (s.written ++ flags guard n s.words) := by
  simp only [bank, ite_true, process_written]

theorem final_stream_position {m : ℕ} (guard : Bool) (n : ℕ) (s : State m) (pos : Port → ℤ) :
    positions pos (process guard n s).written .stream = positions pos s.written .stream + n := by
  simp only [positions, process_length, Nat.cast_add]
  ring

end TransposeFollowup.RowStream


/-! The physical row loop emits the exact rational-overlap row in order.
All arithmetic fits follow from the component-width theorem. Initial words,
the source-open flag, countdown and stream START are prepared inputs. -/

namespace TransposeFollowup.RowStream

open FixedTapeCompiler
set_option autoImplicit false

def rowGuard (F : RationalMobius) {n : ℕ} (i : Fin n) : Bool :=
  (F.componentRow i).sourceLeft.less (F.componentRow i).sourceRight

theorem flags_exact (F : RationalMobius) {n : ℕ} (i : Fin n) (k j : ℕ)
    (hj : j+k ≤ n) (w : RowCell.Words)
    (h : RowCell.Represents (F.componentWidth n) w (F.componentRow i) j) :
    flags (rowGuard F i) k w = (List.range k).map (fun x => F.denseHit i (j+x)) := by
  induction k generalizing j w with
  | zero => rfl
  | succ k ih =>
    have hlt : j < n := by omega
    have hnext := RowCell.updateAll_represents _ w _ j h
      (RowCell.updateFits_of_row F i j hlt w h)
    rw [flags, show RowCell.answer (rowGuard F i) w = F.denseHit i j from
      (RowCell.answer_exact _ w _ j h
        (RowCell.comparisonFits_of_row F i j hlt.le w h)).trans (F.componentRow_hit i j),
      ih (j+1) (by omega) _ hnext, List.range_succ_eq_map]
    simp only [List.map_cons, Nat.add_zero, List.map_map, Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro x _
    congr 1
    omega

theorem process_represents (F : RationalMobius) {n : ℕ} (i : Fin n) (k j : ℕ)
    (hj : j+k ≤ n) (s : State (F.componentWidth n))
    (h : RowCell.Represents (F.componentWidth n) s.words (F.componentRow i) j) :
    RowCell.Represents (F.componentWidth n) (process (rowGuard F i) k s).words
      (F.componentRow i) (j+k) := by
  induction k generalizing j s with
  | zero => exact h
  | succ k ih =>
    have hnext := RowCell.updateAll_represents _ s.words _ j h
      (RowCell.updateFits_of_row F i j (by omega) s.words h)
    have he := ih (j+1) (by omega) (advance (rowGuard F i) s) hnext
    simpa only [process, Nat.add_assoc, Nat.add_comm 1 k] using he

theorem process_row_written (F : RationalMobius) {n : ℕ} (i : Fin n)
    (s : State (F.componentWidth n))
    (h : RowCell.Represents (F.componentWidth n) s.words (F.componentRow i) 0) :
    (process (rowGuard F i) n s).written = s.written ++ F.denseRow i := by
  rw [process_written, flags_exact F i n 0 (by omega) s.words h, F.denseRow_eq_range]
  simp only [Nat.zero_add]

theorem rational_row_trace (F : RationalMobius) {n : ℕ} (i : Fin n)
    (fuel : List Bool) (hf : Counter.value fuel = n) (s : State (F.componentWidth n))
    (h : RowCell.Represents (F.componentWidth n) s.words (F.componentRow i) 0)
    (pos : Port → ℤ) :
    ∃ t ≤ budget (F.componentWidth n) fuel,
      Trace t (cfg (.counter (rowGuard F i) 0) fuel s pos)
        (finishedCfg (.done (rowGuard F i)) (List.replicate fuel.length true)
          (process (rowGuard F i) n s) pos) ∧
      (process (rowGuard F i) n s).written = s.written ++ F.denseRow i ∧
      RowCell.Represents (F.componentWidth n) (process (rowGuard F i) n s).words
        (F.componentRow i) n := by
  obtain ⟨t, ht, htr⟩ := row_trace (rowGuard F i) fuel s pos
  rw [hf] at htr
  exact ⟨t, ht, htr, process_row_written F i s h,
    by simpa only [Nat.zero_add] using process_represents F i n 0 (by omega) s h⟩

/-- Full row output in the original machine model, with a paid STOP write.
The output head is on STOP; no rewind or initialization is hidden here. -/
theorem native_rational_row (F : RationalMobius) {n : ℕ} (i : Fin n)
    (fuel : List Bool) (hf : Counter.value fuel = n) (s : State (F.componentWidth n))
    (h : RowCell.Represents (F.componentWidth n) s.words (F.componentRow i) 0)
    (pos : Port → ℤ) (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ budget (F.componentWidth n) fuel,
      Transpose.stepN nativeMachine input t
        ((cfg (.counter (rowGuard F i) 0) fuel s pos).denote nativeEncoding program inputPos outRev) =
        some ((finishedCfg (.done (rowGuard F i)) (List.replicate fuel.length true)
          (process (rowGuard F i) n s) pos).denote nativeEncoding program inputPos outRev) ∧
      Transpose.step nativeMachine input
        ((finishedCfg (.done (rowGuard F i)) (List.replicate fuel.length true)
          (process (rowGuard F i) n s) pos).denote nativeEncoding program inputPos outRev) = none ∧
      (process (rowGuard F i) n s).written = s.written ++ F.denseRow i ∧
      RowCell.Represents (F.componentWidth n) (process (rowGuard F i) n s).words
        (F.componentRow i) n := by
  obtain ⟨t, ht, hrun, hhalt⟩ := native_row (rowGuard F i) fuel s pos input inputPos outRev
  rw [hf] at hrun hhalt
  exact ⟨t, ht, hrun, hhalt, process_row_written F i s h,
    by simpa only [Nat.zero_add] using process_represents F i n 0 (by omega) s h⟩

end TransposeFollowup.RowStream


/-! Aggregate bounds include the actual counter, linking transitions, every
emitted bit and STOP. Initial loading, subsequent consumption or rewind, and
final fuel cleanup are separate obligations of the eventual generator. -/

namespace TransposeFollowup.RowStream

open FixedTapeCompiler
set_option autoImplicit false

theorem budget_le (n m : ℕ) (fuel : List Bool) (hn : 1 ≤ n)
    (hf : Counter.value fuel = n) :
    budget m fuel ≤ n * (118*m+4*fuel.length+304) := by
  unfold budget
  rw [hf]
  nlinarith [Nat.mul_le_mul_left (4*fuel.length) hn]

theorem total_budget_le_input (A B n m : ℕ) (fuel : List Bool) (hn : 1 ≤ n)
    (hf : Counter.value fuel = n) (hm : m ≤ A+B*(n+1).size)
    (hl : fuel.length ≤ A+B*(n+1).size) :
    n * budget m fuel ≤
      2*((122*A+304)+3*(122*B)) * Transpose.inputLength n := by
  calc
    _ ≤ n * (n * (118*m+4*fuel.length+304)) := Nat.mul_le_mul_left n (budget_le n m fuel hn hf)
    _ ≤ n * (n * ((122*A+304)+(122*B)*(n+1).size)) := by
      apply Nat.mul_le_mul_left
      apply Nat.mul_le_mul_left
      nlinarith
    _ ≤ _ := dense_scan_budget (122*A+304) (122*B) n hn

theorem rational_total_budget (F : RationalMobius) (n : ℕ) (fuel : List Bool) (hn : 1 ≤ n)
    (hf : Counter.value fuel = n) (hl : fuel.length ≤ F.componentWidth n) :
    n * budget (F.componentWidth n) fuel ≤
      (244*(F.integerOperandConstant^2).size+2560) * Transpose.inputLength n := by
  have hm : F.componentWidth n ≤ (F.integerOperandConstant^2).size+2+2*(n+1).size := by
    unfold RationalMobius.componentWidth
    omega
  have h := total_budget_le_input ((F.integerOperandConstant^2).size+2) 2 n
    (F.componentWidth n) fuel hn hf hm (hl.trans hm)
  have hc : 2*((122*((F.integerOperandConstant^2).size+2)+304)+3*(122*2)) =
      244*(F.integerOperandConstant^2).size+2560 := by omega
  simpa only [hc] using h

end TransposeFollowup.RowStream
