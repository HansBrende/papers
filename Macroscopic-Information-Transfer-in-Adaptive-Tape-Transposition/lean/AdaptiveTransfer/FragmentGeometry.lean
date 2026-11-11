import AdaptiveTransfer.FragmentCounters
import AdaptiveTransfer.FragmentCutRecords
import AdaptiveTransfer.FragmentExtrema
import AdaptiveTransfer.FragmentReplay

/-! Actual native observations and the exact global fragment record. Every
field is computed from a successful execution. Equality of records determines
the retained times, cut instructions, raw coordinates and output counters. -/

namespace AdaptiveTransfer
open Transpose Transpose.Tape MergeDepth Finset LeanMachine BoundedNesting

/-- A retained native fragment before choosing its roots. Closure is used only
for the geometry lemma here; the cut theorem instantiates it with literal
cut-free ancestors and proves closure from the dependency graph. -/
structure FragmentObservation (M : TM) (P T : ℕ) (X : Fin P → Bool) (B : Finset ℕ) where
  finish : ℕ
  finish_le : finish ≤ T
  active : ∀ t < finish, transAt M (List.ofFn X) t ≠ none
  kept : Finset ℕ
  kept_lt : ∀ t ∈ kept, t < finish
  cut_lt : ∀ t ∈ B, t < finish
  closed : StateClosedExcept kept B
  count_le : (run M (List.ofFn X) finish).outRev.length ≤ P

abbrev FragmentGeometryMenu (k P T s : ℕ) :=
  Fin (T + 1) × BoundedTuple (s + 1) T × (Fin (k + 1) → HeadDescription s T) ×
    BoundedTuple (2 * (s + 1)) T × Sym (Fin (P + 1)) (4 * s + 2)

abbrev FragmentRecord (M : TM) (P T : ℕ) (B : Finset ℕ) :=
  FragmentGeometryMenu M.k P T B.card × (B → Value M)

def fragmentGeometrySize (k P T s : ℕ) : ℕ :=
  (T + 1) * (T + (s + 1)).choose (s + 1) *
    (6 ^ s * (T + s).choose s) ^ (k + 1) *
    (T + 2 * (s + 1)).choose (2 * (s + 1)) *
    (P + 4 * s + 2).choose (4 * s + 2)

theorem fragmentGeometryMenu_card (k P T s : ℕ) :
    Fintype.card (FragmentGeometryMenu k P T s) = fragmentGeometrySize k P T s := by
  simp only [FragmentGeometryMenu, fragmentGeometrySize, Fintype.card_prod,
    Fintype.card_fin, boundedTuple_card, Fintype.card_fun, Fintype.card_bool,
    Sym.card_sym_eq_choose]
  have he : P + 1 + (4 * s + 2) - 1 = P + 4 * s + 2 := by omega
  have hsix : (6 : ℕ) ^ s = 2 ^ s * 3 ^ s := by rw [← mul_pow]; rfl
  rw [he, hsix]
  ring

theorem fragmentRecord_card (M : TM) (P T : ℕ) (B : Finset ℕ) :
    Fintype.card (FragmentRecord M P T B) =
      fragmentGeometrySize M.k P T B.card * Fintype.card (Value M) ^ B.card := by
  rw [Fintype.card_prod, fragmentGeometryMenu_card, Fintype.card_fun, Fintype.card_coe]

def traceHead {k : ℕ} (τ : Trace k) : Fin (k + 1) → ℕ → ℤ := Fin.cons τ.input τ.work

theorem traceHead_walk {k : ℕ} (τ : Trace k) (h : Fin (k + 1)) : IsWalk (traceHead τ h) := by
  refine Fin.cases ?_ (fun h => ?_) h
  · exact τ.abs_input_succ_sub_le
  · exact τ.work_isWalk h

theorem traceHead_zero {k : ℕ} (τ : Trace k) (h : Fin (k + 1)) : traceHead τ h 0 = 0 := by
  refine Fin.cases ?_ (fun h => ?_) h
  · exact τ.input_zero
  · exact τ.work_zero h

namespace FragmentObservation
variable {M : TM} {P T : ℕ} {X Y : Fin P → Bool} {B : Finset ℕ}

abbrev exec (g : FragmentObservation M P T X B) : ExecutionPrefix M (List.ofFn X) g.finish :=
  ExecutionPrefix.ofRun M (List.ofFn X) g.finish g.active

theorem kept_bound (g : FragmentObservation M P T X B) : ∀ t ∈ g.kept, t < T :=
  fun t ht => (g.kept_lt t ht).trans_le g.finish_le

theorem cut_bound (g : FragmentObservation M P T X B) : ∀ t ∈ B, t < T :=
  fun t ht => (g.cut_lt t ht).trans_le g.finish_le

noncomputable def cutInstruction (g : FragmentObservation M P T X B) (p : B) : NativeInstruction M :=
  g.exec.actualInstruction (g.cut_lt p.val p.property)

theorem cutInstruction_spec (g : FragmentObservation M P T X B) (p : B) :
    nativeInstruction M (List.ofFn X) (run M (List.ofFn X) p.val) = some (g.cutInstruction p) :=
  g.exec.actualInstruction_spec (g.cut_lt p.val p.property)

noncomputable def cutMoves (g : FragmentObservation M P T X B) (h : Fin (M.k + 1))
    (i : Fin B.card) : Fin 3 :=
  instructionMoves (g.cutInstruction ⟨(B.orderEmbOfFin rfl) i, B.orderEmbOfFin_mem rfl i⟩) h

noncomputable def encode (g : FragmentObservation M P T X B) : FragmentRecord M P T B :=
  ((⟨g.finish, by have := g.finish_le; omega⟩,
    prefixDescription B g.kept T g.kept_bound,
    (fun h => cutHeadDescription g.cut_bound (traceHead (trace M (List.ofFn X)) h)
      (traceHead_walk _ h) (traceHead_zero _ h) (g.cutMoves h)),
    prefixExtremaDescription B g.kept T g.kept_bound (trace M (List.ofFn X)).input
      (trace M (List.ofFn X)).abs_input_succ_sub_le,
    fragmentCounterDescription B g.kept P (fun t => (appendList (trace M (List.ofFn X)) t).length)),
    fun p => instructionPayload (g.cutInstruction p))

theorem encode_finish {g : FragmentObservation M P T X B} {h : FragmentObservation M P T Y B}
    (he : g.encode = h.encode) : g.finish = h.finish :=
  congrArg (fun z => z.1.1.val) he

theorem encode_kept {g : FragmentObservation M P T X B} {h : FragmentObservation M P T Y B}
    (he : g.encode = h.encode) : g.kept = h.kept := by
  exact prefixDescription_recovers g.closed h.closed g.kept_bound h.kept_bound
    (congrArg (fun z => z.1.2.1) he)

theorem encode_cut_heads {g : FragmentObservation M P T X B} {h : FragmentObservation M P T Y B}
    (he : g.encode = h.encode) (i : Fin (M.k + 1)) :
    (∀ p ∈ B, traceHead (trace M (List.ofFn X)) i p = traceHead (trace M (List.ofFn Y)) i p) ∧
      g.cutMoves i = h.cutMoves i := by
  exact cutHeadDescription_recovers g.cut_bound (traceHead_walk _ i) (traceHead_walk _ i)
    (traceHead_zero _ i) (traceHead_zero _ i)
    (congrFun (congrArg (fun z => z.1.2.2.1) he) i)

theorem encode_cut_positions {g : FragmentObservation M P T X B} {h : FragmentObservation M P T Y B}
    (he : g.encode = h.encode) {p : ℕ} (hp : p ∈ B) :
    (run M (List.ofFn X) p).inPos = (run M (List.ofFn Y) p).inPos ∧
    (run M (List.ofFn X) p).workPos = (run M (List.ofFn Y) p).workPos := by
  constructor
  · simpa only [inPos_eq_input, traceHead, Fin.cons_zero] using (encode_cut_heads he 0).1 p hp
  · funext i
    simpa only [workPos_eq_work, traceHead, Fin.cons_succ] using (encode_cut_heads he i.succ).1 p hp

theorem encode_cut_instruction {g : FragmentObservation M P T X B} {h : FragmentObservation M P T Y B}
    (he : g.encode = h.encode) (p : B) :
    nativeInstruction M (List.ofFn X) (run M (List.ofFn X) p.val) =
      nativeInstruction M (List.ofFn Y) (run M (List.ofFn Y) p.val) := by
  rw [g.cutInstruction_spec, h.cutInstruction_spec]
  congr 1
  apply instruction_fields_injective M
  apply Prod.ext
  · exact congrFun (congrArg Prod.snd he) p
  · funext i
    let j := (B.orderIsoOfFin rfl).symm p
    have hpj : (⟨(B.orderEmbOfFin rfl) j, B.orderEmbOfFin_mem rfl j⟩ : B) = p :=
      (B.orderIsoOfFin rfl).apply_symm_apply p
    have hh := congrFun (encode_cut_heads he i).2 j
    simpa only [cutMoves, hpj] using hh

theorem encode_next_cut_control {g : FragmentObservation M P T X B} {h : FragmentObservation M P T Y B}
    (he : g.encode = h.encode) {p : ℕ} (hp : p ∈ B) :
    SameControl (run M (List.ofFn X) (p + 1)) (run M (List.ofFn Y) (p + 1)) :=
  (step_positions_instruction_agreement (g.exec.successful p (g.cut_lt p hp))
    (h.exec.successful p (h.cut_lt p hp)) (encode_cut_positions he hp).1
    (encode_cut_positions he hp).2 (encode_cut_instruction he ⟨p, hp⟩)).1

theorem encode_gap_raw_entry {g : FragmentObservation M P T X B} {h : FragmentObservation M P T Y B}
    (he : g.encode = h.encode) {a : ℕ} (ha : a ∈ cutGapStarts B) :
    (trace M (List.ofFn X)).input a = (trace M (List.ofFn Y)).input a := by
  rcases mem_insert.mp ha with ha0 | hap
  · simp only [ha0, Trace.input_zero]
  · obtain ⟨p, hp, hpa⟩ := mem_image.mp hap
    subst a
    simpa only [inPos_eq_input] using (encode_next_cut_control he hp).2.1

theorem encode_raw_image {g : FragmentObservation M P T X B} {h : FragmentObservation M P T Y B}
    (he : g.encode = h.encode) :
    g.kept.image (trace M (List.ofFn X)).input = h.kept.image (trace M (List.ofFn Y)).input := by
  have hK := encode_kept he
  have hfield := congrArg (fun z => z.1.2.2.2.1) he
  change prefixExtremaDescription B g.kept T g.kept_bound (trace M (List.ofFn X)).input
    (trace M (List.ofFn X)).abs_input_succ_sub_le =
    prefixExtremaDescription B h.kept T h.kept_bound (trace M (List.ofFn Y)).input
      (trace M (List.ofFn Y)).abs_input_succ_sub_le at hfield
  simp only [← hK] at hfield ⊢
  exact prefixExtrema_recovers_image g.closed g.kept_bound
    (trace M (List.ofFn X)).abs_input_succ_sub_le (trace M (List.ofFn Y)).abs_input_succ_sub_le
    (fun _ ha => encode_gap_raw_entry he ha) hfield

theorem encode_counter {g : FragmentObservation M P T X B} {h : FragmentObservation M P T Y B}
    (he : g.encode = h.encode) (i : FragmentCounterLabel B) :
    (appendList (trace M (List.ofFn X)) (fragmentCounterTime B g.kept i)).length =
      (appendList (trace M (List.ofFn Y)) (fragmentCounterTime B g.kept i)).length := by
  have hK := encode_kept he
  have hfield := congrArg (fun z => z.1.2.2.2.2) he
  change fragmentCounterDescription B g.kept P _ = fragmentCounterDescription B h.kept P _ at hfield
  rw [← hK] at hfield
  apply fragmentCounterDescription_recovers g.closed g.kept_lt g.cut_lt
    (append_length_mono _) (append_length_mono _) _ _ hfield i
  · simpa only [← native_output_count] using g.count_le
  · rw [encode_finish he]
    simpa only [← native_output_count] using h.count_le

theorem encode_gap_counter {g : FragmentObservation M P T X B} {h : FragmentObservation M P T Y B}
    (he : g.encode = h.encode) (a : cutGapStarts B) :
    (run M (List.ofFn X) a.val).outRev.length = (run M (List.ofFn Y) a.val).outRev.length := by
  simpa only [native_output_count, fragmentCounterTime, Fin.val_zero, ite_true] using
    encode_counter he (.inl (a, 0))

theorem encode_cut_counter {g : FragmentObservation M P T X B} {h : FragmentObservation M P T Y B}
    (he : g.encode = h.encode) (p : B) :
    (run M (List.ofFn X) p.val).outRev.length = (run M (List.ofFn Y) p.val).outRev.length := by
  simpa only [native_output_count, fragmentCounterTime, Fin.val_zero, add_zero] using
    encode_counter he (.inr (p, 0))

end FragmentObservation
end AdaptiveTransfer
