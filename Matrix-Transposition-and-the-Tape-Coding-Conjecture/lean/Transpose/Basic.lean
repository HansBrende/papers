import Transpose.Statement
import Transpose.Sanity

/-!
# Basic facts about the frozen model

Infrastructure for later proofs: the output grows by at most one bit per step, so every
transposition machine needs at least `inputLength n` steps on inputs of size `n`; and a
verified link between a fuel-bounded executable run and `ComputesWithin`.
-/

namespace Transpose

/-- One step appends at most one output bit. -/
theorem step_outRev_length {M : TM} {w : List Bool} {c c' : Config M}
    (h : step M w c = some c') : c'.outRev.length ≤ c.outRev.length + 1 := by
  unfold step at h
  revert h
  cases M.δ c.state (readInput w c.inPos) (fun i => c.work i (c.workPos i)) with
  | none => intro h; exact absurd h (by simp)
  | some r =>
    obtain ⟨s, d, acts, o⟩ := r
    intro h
    have h' := Option.some.inj h
    subst h'
    cases o <;> simp

/-- `n` steps append at most `n` output bits. -/
theorem stepN_outRev_length {M : TM} {w : List Bool} :
    ∀ {n : Nat} {c c' : Config M}, stepN M w n c = some c' →
      c'.outRev.length ≤ c.outRev.length + n
  | 0, c, c', h => by
      simp [stepN] at h
      subst h
      simp
  | n + 1, c, c', h => by
      unfold stepN at h
      revert h
      cases hs : step M w c with
      | none => intro h; exact absurd h (by simp)
      | some c₁ =>
        intro h
        have h1 := step_outRev_length hs
        have h2 := stepN_outRev_length (n := n) h
        omega

/-- A machine that computes `out` within `t` steps needs at least `out.length` steps. -/
theorem length_le_of_computesWithin {M : TM} {w out : List Bool} {t : Nat}
    (h : ComputesWithin M w out t) : out.length ≤ t := by
  obtain ⟨s, hs, c, hc, _, hout⟩ := h
  have := stepN_outRev_length hc
  simp [init] at this
  rw [← hout, List.length_reverse]
  omega

/-- The trivial lower bound: any transposition machine with time bound `T` satisfies
`T (inputLength n) ≥ inputLength n` for every `n ≥ 1`. -/
theorem inputLength_le_time {M : TM} {T : Nat → Nat} (h : TransposesWithin M T)
    (n : Nat) (hn : 1 ≤ n) : inputLength n ≤ T (inputLength n) := by
  have := length_le_of_computesWithin (h n hn (fun _ _ _ => false))
  rwa [Sanity.length_encode] at this

/-- Run until the machine halts, with fuel; returns the number of steps taken and the
final configuration. -/
def runFrom (M : TM) (w : List Bool) : Nat → Config M → Option (Nat × Config M)
  | 0, _ => none
  | fuel + 1, c =>
    match step M w c with
    | none => some (0, c)
    | some c' => (runFrom M w fuel c').map (fun p => (p.1 + 1, p.2))

/-- Soundness of `runFrom` with respect to the step relation. -/
theorem runFrom_spec {M : TM} {w : List Bool} :
    ∀ {fuel : Nat} {c : Config M} {k : Nat} {c' : Config M},
      runFrom M w fuel c = some (k, c') → stepN M w k c = some c' ∧ step M w c' = none
  | 0, c, k, c', h => by simp [runFrom] at h
  | fuel + 1, c, k, c', h => by
      unfold runFrom at h
      revert h
      cases hs : step M w c with
      | none =>
        intro h
        have h' : (0, c) = (k, c') := Option.some.inj h
        injection h' with hk hc
        subst hk; subst hc
        exact ⟨rfl, hs⟩
      | some c₁ =>
        intro h
        cases hr : runFrom M w fuel c₁ with
        | none => simp [hr] at h
        | some p =>
          simp [hr] at h
          obtain ⟨hk, hc⟩ := h
          subst hk; subst hc
          obtain ⟨h1, h2⟩ := runFrom_spec hr
          exact ⟨by simp [stepN, hs, h1], h2⟩

/-- A terminating executable run certifies `ComputesWithin`. -/
theorem computesWithin_of_runFrom {M : TM} {w : List Bool} {fuel k : Nat} {c' : Config M}
    (h : runFrom M w fuel (init M) = some (k, c')) :
    ComputesWithin M w c'.outRev.reverse k :=
  let ⟨h1, h2⟩ := runFrom_spec h
  ⟨k, Nat.le_refl _, c', h1, h2, rfl⟩

end Transpose
