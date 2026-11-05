import TapeStorageRates.NativeMachine
import TapeStorageRates.NativeWarmPath

/-! Observations on actual executions of the compiled machine. The fixed-index
sweep lemma advances the frozen run and certifies every fine native motion. -/

namespace TapeStorageRates.Native

open Transpose Transpose.Tape Transpose.Tape.Impl MergeDepth

noncomputable def labelAt (M : TM) {s : ℕ} (hs : 0<s) (w : List Bool) (t : ℕ) :=
  (labelEquiv M hs).symm (run (machine M hs) w t).state

noncomputable abbrev labelFrom (M : TM) {s : ℕ} (hs : 0<s) (w : List Bool)
    (o : Option (Config (machine M hs))) (t : ℕ) :=
  (labelEquiv M hs).symm (runAt (machine M hs) w o t).state

@[simp] theorem labelAt_zero (M : TM) {s : ℕ} (hs : 0<s) (w : List Bool) :
    labelAt M hs w 0 = initialLabel M hs := by
  change (labelEquiv M hs).symm 0 = _
  rw [Equiv.symm_apply_eq, labelEquiv_initial]

def instrMotion {M : TM} {s : ℕ} (z : Instruction M s) : Motion M.k :=
  (z.2.1, fun j => (z.2.2.1 j).2, z.2.2.2.isSome)

theorem transAt_machine (M : TM) {s : ℕ} (hs : 0<s) (w : List Bool) (t : ℕ) :
    transAt (machine M hs) w t =
      (drive hs (labelAt M hs w t) (inSym (machine M hs) w t)
        (headSym (machine M hs) w t)).map (fun z => (labelEquiv M hs z.1,z.2)) := rfl

theorem transFrom_machine (M : TM) {s : ℕ} (hs : 0<s) (w : List Bool)
    (o : Option (Config (machine M hs))) (t : ℕ) :
    transFrom (machine M hs) w o t =
      (drive hs (labelFrom M hs w o t) (inputAt (machine M hs) w o t)
        (workAt (machine M hs) w o t)).map (fun z => (labelEquiv M hs z.1,z.2)) := rfl

theorem run_drive_from {M : TM} {s : ℕ} {hs : 0<s} {w : List Bool}
    {o : Option (Config (machine M hs))} {t : ℕ} {z : Instruction M s}
    (h : drive hs (labelFrom M hs w o t) (inputAt (machine M hs) w o t)
      (workAt (machine M hs) w o t) = some z) :
    labelFrom M hs w o (t+1) = z.1 ∧ traceFrom (machine M hs) w o t = some (instrMotion z) := by
  have e : transFrom (machine M hs) w o t = some (labelEquiv M hs z.1,z.2) := by
    rw [transFrom_machine,h]; rfl
  refine ⟨?_,?_⟩
  · unfold labelFrom
    rw [after_from_action e]
    exact Equiv.symm_apply_apply _ _
  · unfold traceFrom
    rw [e]
    rfl

def Follows {k : ℕ} (τ : Trace k) (t : ℕ) (xs : List (Motion k)) : Prop :=
  ∀ i (h : i<xs.length), τ (t+i) = some xs[i]

theorem Follows.append {k : ℕ} {τ : Trace k} {t : ℕ} {a b : List (Motion k)}
    (ha : Follows τ t a) (hb : Follows τ (t+a.length) b) : Follows τ t (a++b) := by
  intro i hi
  by_cases h : i<a.length
  · rw [List.getElem_append_left h]
    exact ha i h
  · have hi' : i-a.length<b.length := by simp only [List.length_append] at hi; omega
    simpa [List.getElem_append_right (by omega : a.length ≤ i),
      show t+a.length+(i-a.length)=t+i by omega] using hb (i-a.length) hi'

theorem follows_single {k : ℕ} {τ : Trace k} {t : ℕ} {m : Motion k}
    (h : τ t = some m) : Follows τ t [m] := by
  intro i hi
  have : i=0 := by simpa using hi
  subst i
  simpa using h

/-- The checked transition of every native tick in a finite indexed phase gives
its exact physical execution. The invariant may depend on the index and the
current registers. In particular a read sweep can track its acquired prefix. -/
theorem sweep_from {M : TM} {s : ℕ} (hs : 0<s) (w : List Bool) (o : Option (Config (machine M hs))) (t n : ℕ)
    (ph : ℕ → Phase s) (P : ℕ → Registers M s → Prop) (moves : Fin n → Motion M.k)
    (start : (labelFrom M hs w o t).1 = ph 0 ∧ P 0 (labelFrom M hs w o t).2)
    (tick : ∀ (i : Fin n) (r : Registers M s), P i.val r →
      ∀ (x : Option Bool) (a : Fin M.k → Fin (M.g+1)),
      ∃ z : Instruction M s, drive hs (ph i.val,r) x a = some z ∧
        z.1.1 = ph (i.val+1) ∧ P (i.val+1) z.1.2 ∧ instrMotion z = moves i) :
    ((labelFrom M hs w o (t+n)).1 = ph n ∧ P n (labelFrom M hs w o (t+n)).2) ∧
      Follows (traceFrom (machine M hs) w o) t (List.ofFn moves) := by
  let I := fun i => (labelFrom M hs w o (t+i)).1 = ph i ∧ P i (labelFrom M hs w o (t+i)).2
  have step' (i : ℕ) (hi : i<n) (h : I i) :
      I (i+1) ∧ traceFrom (machine M hs) w o (t+i) = some (moves ⟨i,hi⟩) := by
    obtain ⟨z, hz, hph, hP, hm⟩ := tick ⟨i,hi⟩ _ h.2
      (inputAt (machine M hs) w o (t+i)) (workAt (machine M hs) w o (t+i))
    have eq' : labelFrom M hs w o (t+i) =
        (ph i,(labelFrom M hs w o (t+i)).2) := Prod.ext h.1 rfl
    rw [← eq'] at hz
    obtain ⟨hnext,hmot⟩ := run_drive_from (o := o) hz
    refine ⟨?_, by rw [hmot,hm]⟩
    dsimp only [I]
    rw [← Nat.add_assoc, hnext]
    exact ⟨hph,hP⟩
  have all (i : ℕ) (hi : i≤n) : I i := by
    induction i with
    | zero => simpa [I] using start
    | succ i ih => exact (step' i (by omega) (ih (by omega))).1
  refine ⟨all n le_rfl, ?_⟩
  intro i hi
  have hi' : i<n := by simpa using hi
  simpa using (step' i hi' (all i hi'.le)).2

theorem sweep {M : TM} {s : ℕ} (hs : 0<s) (w : List Bool) (t n : ℕ)
    (ph : ℕ → Phase s) (P : ℕ → Registers M s → Prop) (moves : Fin n → Motion M.k)
    (start : (labelAt M hs w t).1 = ph 0 ∧ P 0 (labelAt M hs w t).2)
    (tick : ∀ (i : Fin n) (r : Registers M s), P i.val r →
      ∀ (x : Option Bool) (a : Fin M.k → Fin (M.g+1)),
      ∃ z : Instruction M s, drive hs (ph i.val,r) x a = some z ∧
        z.1.1 = ph (i.val+1) ∧ P (i.val+1) z.1.2 ∧ instrMotion z = moves i) :
    ((labelAt M hs w (t+n)).1 = ph n ∧ P n (labelAt M hs w (t+n)).2) ∧
      Follows (trace (machine M hs) w) t (List.ofFn moves) :=
  sweep_from hs w none t n ph P moves start tick

def phaseAt {s n : ℕ} (during : Fin n → Phase s) (after : Phase s) (i : ℕ) : Phase s :=
  if hi : i<n then during ⟨i,hi⟩ else after

theorem phaseAt_fin {s n : ℕ} (during : Fin n → Phase s) (after : Phase s) (i : Fin n) :
    phaseAt during after i.val = during i := by simp [phaseAt,i.isLt]

theorem nextIndex_phaseAt {s n : ℕ} (during : Fin n → Phase s) (after : Phase s) (i : Fin n) :
    nextIndex i during after = phaseAt during after (i.val+1) := rfl

/-- The same theorem for the counted loops of the actual native control. -/
theorem runPhase_from {M : TM} {s n : ℕ} (hs : 0<s) (hn : 0<n) (w : List Bool) (o : Option (Config (machine M hs))) (t : ℕ)
    (during : Fin n → Phase s) (after : Phase s) (P : Registers M s → Prop)
    (moves : Fin n → Motion M.k)
    (start : (labelFrom M hs w o t).1 = during ⟨0,hn⟩ ∧ P (labelFrom M hs w o t).2)
    (tick : ∀ i r, P r → ∀ x a,
      ∃ z : Instruction M s, drive hs (during i,r) x a = some z ∧
        z.1.1 = nextIndex i during after ∧ P z.1.2 ∧ instrMotion z = moves i) :
    ((labelFrom M hs w o (t+n)).1 = after ∧ P (labelFrom M hs w o (t+n)).2) ∧
      Follows (traceFrom (machine M hs) w o) t (List.ofFn moves) := by
  apply (sweep_from hs w o t n (phaseAt during after) (fun _ => P) moves ?_ ?_).imp
  · simp [phaseAt]
  · exact id
  · simpa [phaseAt, hn] using start
  · intro i r hr x a
    simpa only [phaseAt_fin, nextIndex_phaseAt] using tick i r hr x a

end TapeStorageRates.Native
