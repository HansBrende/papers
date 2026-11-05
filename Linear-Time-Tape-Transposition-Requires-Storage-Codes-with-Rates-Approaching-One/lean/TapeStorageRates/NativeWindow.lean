import MergeDepth.Traces

/-! The stationary finite lookup in an aligned batch. For a genuine native
configuration, the three captured blocks on each tape determine all writes,
ending offsets, control, new output, and the halt flag for up to s transitions. -/

namespace TapeStorageRates.Native

open Transpose MergeDepth

abbrev Action (M : TM) :=
  Fin (M.q+1) × Dir × (Fin M.k → Fin (M.g+1) × Dir) × Option Bool

/-- Run the original transition table with an arbitrary read-only input tape. -/
def lookup (M : TM) (I : ℤ → Option Bool) (c : Config M) : Option (Action M) :=
  M.δ c.state (I c.inPos) (fun j => c.work j (c.workPos j))

def commit {M : TM} (c : Config M) (z : Action M) : Config M where
  state := z.1
  inPos := z.2.1.shift c.inPos
  work := fun j p => if p = c.workPos j then (z.2.2.1 j).1 else c.work j p
  workPos := fun j => (z.2.2.1 j).2.shift (c.workPos j)
  outRev := match z.2.2.2 with | none => c.outRev | some b => b :: c.outRev

theorem step_eq_lookup (M : TM) (w : List Bool) (c : Config M) :
    step M w c = (lookup M (readInput w) c).map (commit c) := by
  unfold lookup step
  cases M.δ c.state (readInput w c.inPos) (fun j => c.work j (c.workPos j)) with
  | none => rfl
  | some z => rcases z with ⟨q, i, h, o⟩; rfl

/-- The Bool is true exactly when a failed lookup has already been observed.
At fuel zero the batch performs no speculative lookahead. -/
def advance (M : TM) (I : ℤ → Option Bool) : ℕ → Config M → Config M × Bool
  | 0, c => (c,false)
  | n+1, c => match lookup M I c with
    | none => (c,true)
    | some z => advance M I n (commit c z)

/-- A head can make n more moves in this window, including its final position. -/
def Fits (s n : ℕ) (p : ℤ) : Prop :=
  -(s : ℤ) + (n : ℤ) ≤ p ∧ p < 2*(s : ℤ) - (n : ℤ)

theorem fits_zero_of_fits {s n : ℕ} {p : ℤ} (hp : Fits s n p) : Fits s 0 p := by
  unfold Fits at *
  omega

theorem fits_shift {s n : ℕ} {p : ℤ} (hp : Fits s (n+1) p) (d : Dir) :
    Fits s n (d.shift p) := by
  unfold Fits at *
  cases d <;> simp only [Dir.shift] <;> omega

def HeadsFit {M : TM} (s n : ℕ) (c : Config M) : Prop :=
  Fits s n c.inPos ∧ ∀ j, Fits s n (c.workPos j)

theorem fits_commit {M : TM} {s n : ℕ} {c : Config M} (h : HeadsFit s (n+1) c)
    (z : Action M) : HeadsFit s n (commit c z) :=
  ⟨fits_shift h.1 _, fun j => fits_shift (h.2 j) _⟩

theorem advance_fits {M : TM} {I : ℤ → Option Bool} {s n : ℕ} {c : Config M}
    (h : HeadsFit s n c) : HeadsFit s 0 (advance M I n c).1 := by
  induction n generalizing c with
  | zero => exact h
  | succ n ih =>
    cases he : lookup M I c with
    | none => simpa [advance, he] using
        (show HeadsFit s 0 c from ⟨fits_zero_of_fits h.1, fun j => fits_zero_of_fits (h.2 j)⟩)
    | some z => simpa [advance, he] using ih (fits_commit h z)

/-- Native and local tapes agree on the full window after translating each tape
by its own anchor. The local output represents the prefix produced this batch. -/
structure WindowAgrees {M : TM} (s : ℕ) (ai : ℤ) (aw : Fin M.k → ℤ) (past : List Bool)
    (c v : Config M) : Prop where
  state : c.state = v.state
  inputPos : c.inPos = ai + v.inPos
  workPos : ∀ j, c.workPos j = aw j + v.workPos j
  cells : ∀ j p, Fits s 0 p → c.work j (aw j+p) = v.work j p
  output : c.outRev = v.outRev ++ past

private theorem WindowAgrees.lookup_eq {M : TM} {I J : ℤ → Option Bool} {s n : ℕ}
    {ai : ℤ} {aw : Fin M.k → ℤ} {past : List Bool} {c v : Config M}
    (h : WindowAgrees s ai aw past c v) (hf : HeadsFit s n v)
    (hI : ∀ p, Fits s 0 p → I (ai+p) = J p) : lookup M I c = lookup M J v := by
  unfold lookup
  rw [h.state, h.inputPos, hI _ (fits_zero_of_fits hf.1)]
  congr 1
  funext j
  rw [h.workPos j, h.cells j _ (fits_zero_of_fits (hf.2 j))]

private theorem WindowAgrees.commit {M : TM} {s : ℕ} {ai : ℤ} {aw : Fin M.k → ℤ}
    {past : List Bool} {c v : Config M} (h : WindowAgrees s ai aw past c v) (z : Action M) :
    WindowAgrees s ai aw past (commit c z) (commit v z) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · simp [Native.commit, shift_eq_add_moveInt, h.inputPos, add_assoc]
  · intro j
    simp [Native.commit, shift_eq_add_moveInt, h.workPos, add_assoc]
  · intro j p hp
    simp [Native.commit, h.workPos, h.cells _ _ hp]
  · cases ho : z.2.2.2 <;> simp [Native.commit, ho, h.output]

theorem advance_agrees {M : TM} {I J : ℤ → Option Bool} {s n : ℕ}
    {ai : ℤ} {aw : Fin M.k → ℤ} {past : List Bool} {c v : Config M}
    (h : WindowAgrees s ai aw past c v) (hf : HeadsFit s n v)
    (hI : ∀ p, Fits s 0 p → I (ai+p) = J p) :
    WindowAgrees s ai aw past (advance M I n c).1 (advance M J n v).1 ∧
      (advance M I n c).2 = (advance M J n v).2 := by
  induction n generalizing c v with
  | zero => exact ⟨h,rfl⟩
  | succ n ih =>
    have he := h.lookup_eq hf hI
    cases hz : lookup M J v with
    | none => simpa [advance, he, hz] using h
    | some z => simpa [advance, he, hz] using ih (h.commit z) (fits_commit hf z)

/-- A finite three-block window and its true reading at an arbitrary anchor. -/
abbrev Cells (α : Type*) (s : ℕ) := Fin (3*s) → α

def capture (s : ℕ) {α : Type*} (read : ℤ → α) (anchor : ℤ) : Cells α s :=
  fun i => read (anchor + ((i.val : ℤ) - s))

def windowIndex {s : ℕ} {p : ℤ} (hp : Fits s 0 p) : Fin (3*s) :=
  ⟨(p+s).toNat, by unfold Fits at hp; omega⟩

def windowRead {s : ℕ} {α : Type*} (a : Cells α s) (blank : α) (p : ℤ) : α :=
  if hp : -(s : ℤ) ≤ p ∧ p < 2*(s : ℤ) then a (windowIndex (by simpa [Fits] using hp)) else blank

theorem windowRead_capture {s : ℕ} {α : Type*} (read : ℤ → α) (anchor p : ℤ) (blank : α)
    (hp : Fits s 0 p) : windowRead (capture s read anchor) blank p = read (anchor+p) := by
  have h : -(s : ℤ) ≤ p ∧ p < 2*(s : ℤ) := by simpa [Fits] using hp
  simp only [windowRead, dite_eq_left h, capture, windowIndex]
  congr 1
  omega

def localConfig (M : TM) (s : ℕ) (q : Fin (M.q+1)) (oi : Fin s)
    (ow : Fin M.k → Fin s) (work : Fin M.k → Cells (Fin (M.g+1)) s) : Config M where
  state := q
  inPos := oi.val
  work := fun j => windowRead (work j) 0
  workPos := fun j => (ow j).val
  outRev := []

theorem localConfig_fits {M : TM} {s : ℕ} (q : Fin (M.q+1)) (oi : Fin s)
    (ow : Fin M.k → Fin s) (work : Fin M.k → Cells (Fin (M.g+1)) s) :
    HeadsFit s s (localConfig M s q oi ow work) := by
  have hf (i : Fin s) : Fits s s (i.val : ℤ) := by
    have := i.isLt
    unfold Fits
    omega
  exact ⟨hf oi, fun j => hf (ow j)⟩

/-- A native batch from any aligned configuration is determined by the captured
finite arrays, even when the simulated run starts next to either end marker. -/
theorem native_batch_local (M : TM) (s : ℕ) (w : List Bool) (c : Config M)
    (ai : ℤ) (aw : Fin M.k → ℤ) (oi : Fin s) (ow : Fin M.k → Fin s)
    (hi : c.inPos = ai + oi.val) (hw : ∀ j, c.workPos j = aw j + (ow j).val) :
    let v := localConfig M s c.state oi ow (fun j => capture s (c.work j) (aw j))
    let J := windowRead (capture s (readInput w) ai) none
    WindowAgrees s ai aw c.outRev (advance M (readInput w) s c).1 (advance M J s v).1 ∧
      (advance M (readInput w) s c).2 = (advance M J s v).2 := by
  dsimp only
  apply advance_agrees
  · exact ⟨rfl, hi, hw, fun j p hp => (windowRead_capture _ _ _ _ hp).symm, rfl⟩
  · apply localConfig_fits
  · intro p hp
    exact (windowRead_capture _ _ _ _ hp).symm

/-- The lookup cannot generate more output bits than its fuel. -/
theorem advance_output_le (M : TM) (I : ℤ → Option Bool) (n : ℕ) (c : Config M) :
    (advance M I n c).1.outRev.length ≤ c.outRev.length+n := by
  induction n generalizing c with
  | zero => simp [advance]
  | succ n ih =>
    cases hz : lookup M I c with
    | none => simp [advance, hz]
    | some z =>
      simp only [advance, hz]
      apply (ih (commit c z)).trans
      cases ho : z.2.2.2 <;> simp [commit, ho]
      omega

/-- A native cell beyond the window is unchanged throughout the local computation. -/
theorem advance_outside {M : TM} {I : ℤ → Option Bool} (s n : ℕ) (c : Config M)
    (ai : ℤ) (aw : Fin M.k → ℤ) (hi : Fits s n (c.inPos-ai))
    (hw : ∀ j, Fits s n (c.workPos j-aw j)) (j : Fin M.k) (p : ℤ)
    (hp : ¬ Fits s 0 (p-aw j)) : (advance M I n c).1.work j p = c.work j p := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    cases hz : lookup M I c with
    | none => simp [advance, hz]
    | some z =>
      simp only [advance, hz]
      have shift (d : Dir) (pos a : ℤ) : d.shift pos - a = d.shift (pos-a) := by
        rw [shift_eq_add_moveInt, shift_eq_add_moveInt]; omega
      rw [ih (commit c z) (by simpa [commit, shift] using fits_shift hi z.2.1)
        (fun h => by simpa [commit, shift] using fits_shift (hw h) (z.2.2.1 h).2)]
      have hne : p ≠ c.workPos j := fun h => hp (h ▸ fits_zero_of_fits (hw j))
      simp [commit, hne]

/-- On a run having at least n successful transitions this lookup observes
no halt and reaches the exact frozen stepN configuration. -/
theorem advance_of_stepN {M : TM} {w : List Bool} {n : ℕ} {c d : Config M}
    (h : stepN M w n c = some d) : advance M (readInput w) n c = (d,false) := by
  induction n generalizing c with
  | zero => rw [advance, Option.some.inj h]
  | succ n ih =>
    simp only [stepN, step_eq_lookup] at h
    cases hz : lookup M (readInput w) c with
    | none => simp [hz] at h
    | some z => simpa [advance, hz] using ih (by simpa [hz] using h)

/-- If the native execution halts after n successes within the available fuel,
the table reaches that exact halted configuration and sets the stop flag. -/
theorem advance_of_halt {M : TM} {w : List Bool} {n : ℕ} {c d : Config M}
    (h : stepN M w n c = some d) (halt : step M w d = none) (extra : ℕ) :
    advance M (readInput w) (n+extra+1) c = (d,true) := by
  induction n generalizing c with
  | zero =>
    have e : c = d := Option.some.inj h
    subst c
    have hnone : lookup M (readInput w) d = none := by
      simpa [step_eq_lookup] using halt
    simp [advance, hnone]
  | succ n ih =>
    simp only [stepN, step_eq_lookup] at h
    cases hz : lookup M (readInput w) c with
    | none => simp [hz] at h
    | some z =>
      rw [show n+1+extra+1 = (n+extra+1)+1 by omega, advance, hz]
      exact ih (by simpa [hz] using h)

end TapeStorageRates.Native
