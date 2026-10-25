import Transpose.Tape.Passes
import Transpose.Tape.Encode
import PassMemo.FiniteTermination

/-! Exact finite-control simulation while heads stay put or advance into blank rays.
The output is unreadable in the original model and is not included in the signature.
-/

namespace PassMemo

open Transpose Transpose.Tape Transpose.Tape.Impl

def Allowed (θ d : Dir) : Prop := d = .stay ∨ d = θ

instance (θ d : Dir) : Decidable (Allowed θ d) := inferInstanceAs (Decidable (_ ∨ _))

def SafeWork {g : ℕ} (θ : Dir) (t : ℤ → Fin (g + 1)) (p : ℤ) : Prop :=
  match θ with
  | .stay => True
  | .left => ∀ q < p, t q = 0
  | .right => ∀ q > p, t q = 0

def SafeInput (w : List Bool) (θ : Dir) (p : ℤ) : Prop :=
  match θ with
  | .stay => True
  | .left => p < 0
  | .right => (w.length : ℤ) ≤ p

def Clean (M : TM) (w : List Bool) (θ₀ : Dir) (θ : Fin M.k → Dir) (c : Config M) : Prop :=
  SafeInput w θ₀ c.inPos ∧ ∀ i, SafeWork (θ i) (c.work i) (c.workPos i)

abbrev Signature (M : TM) := Fin (M.q + 1) × Option Bool × (Fin M.k → Fin (M.g + 1))

def signature (M : TM) (w : List Bool) (c : Config M) : Signature M :=
  (c.state, readInput w c.inPos, fun i => c.work i (c.workPos i))

abbrev Action (M : TM) :=
  Fin (M.q + 1) × Dir × (Fin M.k → Fin (M.g + 1) × Dir) × Option Bool

def Admissible (M : TM) (θ₀ : Dir) (θ : Fin M.k → Dir) (a : Action M) : Prop :=
  Allowed θ₀ a.2.1 ∧ ∀ i, Allowed (θ i) (a.2.2.1 i).2

instance (M : TM) (θ₀ : Dir) (θ : Fin M.k → Dir) (a : Action M) :
    Decidable (Admissible M θ₀ θ a) := inferInstanceAs (Decidable (_ ∧ _))

def signatureNext (M : TM) (s : Signature M) (a : Action M) : Signature M :=
  (a.1, s.2.1, fun i => if (a.2.2.1 i).2 = .stay then (a.2.2.1 i).1 else 0)

def rayStep (M : TM) (θ₀ : Dir) (θ : Fin M.k → Dir) : Option (Signature M) → Option (Signature M)
  | none => none
  | some s => match M.δ s.1 s.2.1 s.2.2 with
    | none => none
    | some a => if Admissible M θ₀ θ a then some (signatureNext M s a) else none

theorem safeWork_update {g : ℕ} {θ d : Dir} {t : ℤ → Fin (g + 1)} {p : ℤ}
    (b : Fin (g + 1)) (hs : SafeWork θ t p) (hd : Allowed θ d) :
    SafeWork θ (fun q => if q = p then b else t q) (d.shift p) := by
  cases θ <;> cases d <;> simp only [Allowed, SafeWork, Dir.shift] at *
  all_goals try contradiction
  all_goals intro q hq; rw [ite_eq_right (by omega)]; exact hs q (by omega)

theorem scanned_update {g : ℕ} {θ d : Dir} {t : ℤ → Fin (g + 1)} {p : ℤ}
    (b : Fin (g + 1)) (hs : SafeWork θ t p) (hd : Allowed θ d) :
    (if d.shift p = p then b else t (d.shift p)) = if d = .stay then b else 0 := by
  cases θ <;> cases d <;> simp only [Allowed, SafeWork, Dir.shift] at *
  all_goals try contradiction
  all_goals try simp
  all_goals exact hs _ (by omega)

theorem safeInput_shift {w : List Bool} {θ d : Dir} {p : ℤ}
    (hs : SafeInput w θ p) (hd : Allowed θ d) :
    SafeInput w θ (d.shift p) ∧ readInput w (d.shift p) = readInput w p := by
  cases θ <;> cases d <;> simp only [Allowed, SafeInput, Dir.shift] at *
  all_goals try contradiction
  all_goals try simp_all
  all_goals constructor
  all_goals first | omega | rw [readInput_eq_none (by omega), readInput_eq_none (by omega)]

/-- A valid ray transition reproduces the original machine step, including the
blank symbols exposed by moving heads; the ray invariant is preserved. -/
theorem ray_simulation {M : TM} {w : List Bool} {θ₀ : Dir} {θ : Fin M.k → Dir}
    {c : Config M} (hc : Clean M w θ₀ θ c) {a : Action M}
    (ha : M.δ (signature M w c).1 (signature M w c).2.1 (signature M w c).2.2 = some a)
    (hadm : Admissible M θ₀ θ a) :
    ∃ c', step M w c = some c' ∧ Clean M w θ₀ θ c' ∧
      signature M w c' = signatureNext M (signature M w c) a := by
  obtain ⟨s, d, acts, o⟩ := a
  let c' : Config M :=
    { state := s
      inPos := d.shift c.inPos
      work := fun i p => if p = c.workPos i then (acts i).1 else c.work i p
      workPos := fun i => (acts i).2.shift (c.workPos i)
      outRev := match o with | none => c.outRev | some b => b :: c.outRev }
  refine ⟨c', ?_, ?_, ?_⟩
  · change (match M.δ c.state (readInput w c.inPos) (fun i => c.work i (c.workPos i)) with
      | none => none
      | some (s, d, acts, o) => _) = some c'
    change M.δ c.state (readInput w c.inPos) (fun i => c.work i (c.workPos i)) = _ at ha
    rw [ha]
    cases o <;> rfl
  · exact ⟨(safeInput_shift hc.1 hadm.1).1,
      fun i => safeWork_update (acts i).1 (hc.2 i) (hadm.2 i)⟩
  · refine Prod.ext rfl (Prod.ext ?_ ?_)
    · exact (safeInput_shift hc.1 hadm.1).2
    · funext i
      exact scanned_update (acts i).1 (hc.2 i) (hadm.2 i)

theorem ray_lift {M : TM} {w : List Bool} {θ₀ : Dir} {θ : Fin M.k → Dir}
    {c : Config M} (hc : Clean M w θ₀ θ c) {s' : Signature M}
    (hnext : rayStep M θ₀ θ (some (signature M w c)) = some s') :
    ∃ c', step M w c = some c' ∧ Clean M w θ₀ θ c' ∧ signature M w c' = s' := by
  cases ha : M.δ (signature M w c).1 (signature M w c).2.1 (signature M w c).2.2 with
  | none => simp [rayStep, ha] at hnext
  | some a =>
    simp only [rayStep, ha] at hnext
    split_ifs at hnext with hadm
    · obtain ⟨c', hstep, hc', hs'⟩ := ray_simulation hc ha hadm
      exact ⟨c', hstep, hc', hs'.trans (Option.some.inj hnext)⟩

/-- A halting native continuation forces exit from every clean-ray simulation.
The simulation may exit earlier when a head tries a disallowed move. -/
theorem ray_eventually_none {M : TM} {w : List Bool} {θ₀ : Dir} {θ : Fin M.k → Dir}
    {a n : ℕ} (hc : Clean M w θ₀ θ (run M w a))
    (hstop : transAt M w (a + n) = none) :
    ∃ j, (rayStep M θ₀ θ)^[j] (some (signature M w (run M w a))) = none := by
  induction n generalizing a with
  | zero =>
    refine ⟨1, ?_⟩
    change rayStep M θ₀ θ (some (signature M w (run M w a))) = none
    have ha : M.δ (signature M w (run M w a)).1
        (signature M w (run M w a)).2.1 (signature M w (run M w a)).2.2 = none := by
      exact hstop
    simp [rayStep, ha]
  | succ n ih =>
    cases hnext : rayStep M θ₀ θ (some (signature M w (run M w a))) with
    | none => exact ⟨1, hnext⟩
    | some s' =>
      obtain ⟨c', hstep, hc', hs'⟩ := ray_lift hc hnext
      have hrun : run M w (a + 1) = c' := by rw [run_succ, next, hstep]; rfl
      rw [← hrun] at hc' hs'
      obtain ⟨j, hj⟩ := ih hc' (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hstop)
      refine ⟨j + 1, ?_⟩
      rw [Function.iterate_succ_apply, hnext, ← hs']
      exact hj

theorem ray_step_run {M : TM} {w : List Bool} {θ₀ : Dir} {θ : Fin M.k → Dir}
    {t : ℕ} (hc : Clean M w θ₀ θ (run M w t)) {a : Action M}
    (ha : transAt M w t = some a) (hadm : Admissible M θ₀ θ a) :
    Clean M w θ₀ θ (run M w (t + 1)) ∧
      rayStep M θ₀ θ (some (signature M w (run M w t))) =
        some (signature M w (run M w (t + 1))) := by
  obtain ⟨c', hstep, hc', hs'⟩ := ray_simulation hc ha hadm
  have hrun : run M w (t + 1) = c' := by rw [run_succ, next, hstep]; rfl
  refine ⟨hrun ▸ hc', ?_⟩
  rw [hrun, hs']
  change (match transAt M w t with | none => none | some a => _) = _
  simp [ha, hadm]

def signatureCount (M : TM) : ℕ := 3 * (M.q + 1) * (M.g + 1) ^ M.k

theorem card_signature (M : TM) : Fintype.card (Signature M) = signatureCount M := by
  simp [Signature, signatureCount]
  ring

/-- An actual halting run cannot remain in one clean-ray regime for more than
the number of finite-control signatures. -/
theorem ray_interval_bound {M : TM} {w : List Bool} {θ₀ : Dir} {θ : Fin M.k → Dir}
    {a n T : ℕ} (hc : Clean M w θ₀ θ (run M w a)) (haT : a ≤ T)
    (hstop : transAt M w T = none)
    (hsteps : ∀ j < n, ∃ b : Action M,
      transAt M w (a + j) = some b ∧ Admissible M θ₀ θ b) :
    n ≤ signatureCount M := by
  have hshadow : ∀ j ≤ n, Clean M w θ₀ θ (run M w (a + j)) ∧
      (rayStep M θ₀ θ)^[j] (some (signature M w (run M w a))) =
        some (signature M w (run M w (a + j))) := by
    intro j
    induction j with
    | zero => intro _; exact ⟨hc, rfl⟩
    | succ j ih =>
      intro hj
      obtain ⟨hcj, hsj⟩ := ih (by omega)
      obtain ⟨b, hb, hadm⟩ := hsteps j (by omega)
      obtain ⟨hcnext, hsnext⟩ := ray_step_run hcj hb hadm
      refine ⟨by simpa [Nat.add_assoc] using hcnext, ?_⟩
      rw [Function.iterate_succ_apply', hsj]
      simpa [Nat.add_assoc] using hsnext
  have hterm := ray_eventually_none hc (n := T - a) (by simpa [Nat.add_sub_of_le haT] using hstop)
  rw [← card_signature]
  apply live_prefix_le_card _ _ hterm
  intro j hj
  rw [(hshadow j (by omega)).2]
  simp

end PassMemo
