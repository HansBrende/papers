import AdaptiveTransfer.LocalCounters
import AdaptiveTransfer.FragmentGeometry

/-! Actual bounded records for fragments inside a public selected chunk.
The N+s prefix tuple and 4s+2N counter multiset have the exact localized
menu size; head movements and cut payloads use the global native encoders. -/

namespace AdaptiveTransfer
open Transpose Transpose.Tape MergeDepth Finset LeanMachine BoundedNesting NativeRelations

structure LocalFragmentObservation (M : TM) (P T N : ℕ) (X : Fin P → Bool)
    (C B : Finset ℕ) where
  finish : ℕ
  finish_le : finish ≤ T
  active : ∀ t < finish, transAt M (List.ofFn X) t ≠ none
  kept : Finset ℕ
  closed : LocallyStateClosedExcept C kept B
  chunk_lt : ∀ t ∈ C, t < finish
  cut_lt : ∀ t ∈ B, t < finish
  run_cap : (runStarts C).card ≤ N
  count_le : (run M (List.ofFn X) finish).outRev.length ≤ P

abbrev LocalFragmentGeometryMenu (k P T N s : ℕ) :=
  Fin (T + 1) × BoundedTuple (N + s) T × (Fin (k + 1) → HeadDescription s T) ×
    Sym (Fin (P + 1)) (4 * s + 2 * N)

abbrev LocalFragmentRecord (M : TM) (P T N : ℕ) (B : Finset ℕ) :=
  LocalFragmentGeometryMenu M.k P T N B.card × (B → Value M)

def localFragmentGeometrySize (k P T N s : ℕ) : ℕ :=
  (T + 1) * (T + N + s).choose (N + s) *
    (6 ^ s * (T + s).choose s) ^ (k + 1) * (P + 4 * s + 2 * N).choose (4 * s + 2 * N)

theorem localFragmentGeometryMenu_card (k P T N s : ℕ) :
    Fintype.card (LocalFragmentGeometryMenu k P T N s) = localFragmentGeometrySize k P T N s := by
  simp only [LocalFragmentGeometryMenu, localFragmentGeometrySize, Fintype.card_prod,
    Fintype.card_fin, boundedTuple_card, Fintype.card_fun, Fintype.card_bool, Sym.card_sym_eq_choose]
  have he : P + 1 + (4 * s + 2 * N) - 1 = P + 4 * s + 2 * N := by omega
  have hsix : (6 : ℕ) ^ s = 2 ^ s * 3 ^ s := by rw [← mul_pow]; rfl
  rw [he, hsix, ← Nat.add_assoc T N s]
  ring

theorem localFragmentRecord_card (M : TM) (P T N : ℕ) (B : Finset ℕ) :
    Fintype.card (LocalFragmentRecord M P T N B) =
      localFragmentGeometrySize M.k P T N B.card * Fintype.card (Value M) ^ B.card := by
  rw [Fintype.card_prod, localFragmentGeometryMenu_card, Fintype.card_fun, Fintype.card_coe]

namespace LocalFragmentObservation
variable {M : TM} {P T N : ℕ} {X Y : Fin P → Bool} {C B : Finset ℕ}

/-- Reuse the actual global cut-field encoder with an empty retained set;
its extra global prefix/extremum/counter fields are discarded. -/
def cutView (g : LocalFragmentObservation M P T N X C B) : FragmentObservation M P T X B where
  finish := g.finish
  finish_le := g.finish_le
  active := g.active
  kept := ∅
  kept_lt := by simp
  cut_lt := g.cut_lt
  closed := by simp [StateClosedExcept]
  count_le := g.count_le

abbrev exec (g : LocalFragmentObservation M P T N X C B) : ExecutionPrefix M (List.ofFn X) g.finish :=
  g.cutView.exec

theorem kept_lt (g : LocalFragmentObservation M P T N X C B) : ∀ t ∈ g.kept, t < g.finish :=
  fun t ht => g.chunk_lt t (g.closed.1 ht)

theorem kept_bound (g : LocalFragmentObservation M P T N X C B) : ∀ t ∈ g.kept, t < T :=
  fun t ht => (g.kept_lt t ht).trans_le g.finish_le

noncomputable def encode (g : LocalFragmentObservation M P T N X C B) : LocalFragmentRecord M P T N B :=
  ((⟨g.finish, by have := g.finish_le; omega⟩,
    localPrefixDescription C g.kept B T N g.closed g.kept_bound g.run_cap,
    g.cutView.encode.1.2.2.1,
    localCounterDescription C g.kept B P N (fun t => (appendList (trace M (List.ofFn X)) t).length)),
    g.cutView.encode.2)

theorem encode_finish {g : LocalFragmentObservation M P T N X C B}
    {h : LocalFragmentObservation M P T N Y C B} (he : g.encode = h.encode) : g.finish = h.finish :=
  congrArg (fun z => z.1.1.val) he

theorem encode_kept {g : LocalFragmentObservation M P T N X C B}
    {h : LocalFragmentObservation M P T N Y C B} (he : g.encode = h.encode) : g.kept = h.kept :=
  localPrefixDescription_recovers g.closed h.closed g.kept_bound h.kept_bound g.run_cap
    (congrArg (fun z => z.1.2.1) he)

theorem encode_cut_heads {g : LocalFragmentObservation M P T N X C B}
    {h : LocalFragmentObservation M P T N Y C B} (he : g.encode = h.encode) (i : Fin (M.k + 1)) :
    (∀ p ∈ B, traceHead (trace M (List.ofFn X)) i p = traceHead (trace M (List.ofFn Y)) i p) ∧
      g.cutView.cutMoves i = h.cutView.cutMoves i :=
  cutHeadDescription_recovers g.cutView.cut_bound (traceHead_walk _ i) (traceHead_walk _ i)
    (traceHead_zero _ i) (traceHead_zero _ i) (congrFun (congrArg (fun z => z.1.2.2.1) he) i)

theorem encode_cut_positions {g : LocalFragmentObservation M P T N X C B}
    {h : LocalFragmentObservation M P T N Y C B} (he : g.encode = h.encode) {p : ℕ} (hp : p ∈ B) :
    (run M (List.ofFn X) p).inPos = (run M (List.ofFn Y) p).inPos ∧
    (run M (List.ofFn X) p).workPos = (run M (List.ofFn Y) p).workPos := by
  constructor
  · simpa only [inPos_eq_input, traceHead, Fin.cons_zero] using (encode_cut_heads he 0).1 p hp
  · funext i
    simpa only [workPos_eq_work, traceHead, Fin.cons_succ] using (encode_cut_heads he i.succ).1 p hp

theorem encode_cut_instruction {g : LocalFragmentObservation M P T N X C B}
    {h : LocalFragmentObservation M P T N Y C B} (he : g.encode = h.encode) (p : B) :
    nativeInstruction M (List.ofFn X) (run M (List.ofFn X) p.val) =
      nativeInstruction M (List.ofFn Y) (run M (List.ofFn Y) p.val) := by
  rw [g.cutView.cutInstruction_spec, h.cutView.cutInstruction_spec]
  congr 1
  apply instruction_fields_injective M
  apply Prod.ext
  · exact congrFun (congrArg Prod.snd he) p
  · funext i
    let j := (B.orderIsoOfFin rfl).symm p
    have hpj : (⟨(B.orderEmbOfFin rfl) j, B.orderEmbOfFin_mem rfl j⟩ : B) = p :=
      (B.orderIsoOfFin rfl).apply_symm_apply p
    simpa only [FragmentObservation.cutMoves, hpj] using congrFun (encode_cut_heads he i).2 j

theorem encode_counter {g : LocalFragmentObservation M P T N X C B}
    {h : LocalFragmentObservation M P T N Y C B} (he : g.encode = h.encode) (i : LocalCounterLabel C B) :
    (run M (List.ofFn X) (localCounterTime C g.kept B i)).outRev.length =
      (run M (List.ofFn Y) (localCounterTime C g.kept B i)).outRev.length := by
  have hK := encode_kept he
  have hfield := congrArg (fun z => z.1.2.2.2) he
  change localCounterDescription C g.kept B P N _ = localCounterDescription C h.kept B P N _ at hfield
  rw [← hK] at hfield
  rw [native_output_count, native_output_count]
  apply localCounterDescription_recovers g.closed g.chunk_lt g.cut_lt g.run_cap
    (append_length_mono _) (append_length_mono _) _ _ hfield i
  · simpa only [← native_output_count] using g.count_le
  · rw [encode_finish he]
    simpa only [← native_output_count] using h.count_le

theorem encode_entry_counter {g : LocalFragmentObservation M P T N X C B}
    {h : LocalFragmentObservation M P T N Y C B} (he : g.encode = h.encode) (a : localGapStarts C B) :
    (run M (List.ofFn X) a.val).outRev.length = (run M (List.ofFn Y) a.val).outRev.length := by
  simpa only [localCounterTime, Fin.val_zero, ite_true] using encode_counter he (.inl (a, 0))

theorem encode_cut_counter {g : LocalFragmentObservation M P T N X C B}
    {h : LocalFragmentObservation M P T N Y C B} (he : g.encode = h.encode) (p : B) :
    (run M (List.ofFn X) p.val).outRev.length = (run M (List.ofFn Y) p.val).outRev.length := by
  simpa only [localCounterTime, Fin.val_zero, add_zero] using encode_counter he (.inr (p, 0))

end LocalFragmentObservation
end AdaptiveTransfer
