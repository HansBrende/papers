import HalfRate.Decomposition

/-!
# Positional charging conditions

`relCharged_of_cosupply` turns step-by-step inclusions along an elimination list, together with
co-supply (all steps charged to the same outside vertex use the same supplying record), into the
recursive predicate `RelCharged` used by piece certificates. Co-supply makes the nesting
condition automatic.
-/

namespace HalfRate

open Finset MotionDepthCodes

variable {V : Type*} [DecidableEq V] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The revealed set before position `j` of `l`, starting from `S`. -/
def rev (S : Finset V) (l : List V) (j : ℕ) : Finset V := S ∪ (l.take j).toFinset

omit [Fintype ι] [DecidableEq ι] in
theorem rev_cons_succ (S : Finset V) (v : V) (l : List V) (j : ℕ) :
    rev S (v :: l) (j + 1) = rev (insert v S) l j := by
  ext x; simp [rev, List.take_succ_cons]

omit [Fintype ι] [DecidableEq ι] in
theorem rev_zero (S : Finset V) (l : List V) : rev S l 0 = S := by simp [rev]

omit [Fintype ι] [DecidableEq ι] in
/-- Positional step conditions plus co-supply give `RelCharged`. -/
theorem relCharged_of_cosupply (N : V → Finset V) (U : Finset V) (P : ι → Finset V)
    (b : V → ι) (par : V → Option V) (W : Finset V) :
    ∀ (l : List V) (S : Finset V) (L : V → Finset V),
      (∀ j (hj : j < l.length), par l[j] = none →
          N l[j] ⊆ U ∪ (rev S l j ∪ P (b l[j]))) →
      (∀ j (hj : j < l.length) w, par l[j] = some w →
          w ∈ W ∧ N l[j] ⊆ U ∪ insert w (rev S l j ∪ P (b l[j])) ∧
            L w ⊆ rev S l j ∪ P (b l[j])) →
      (∀ j j' (hj : j < j') (hj' : j' < l.length) w, par l[j] = some w →
          par l[j'] = some w → b l[j] = b l[j']) →
      RelCharged N U P b par W S L l := by
  intro l
  induction l with
  | nil => intro _ _ _ _ _; trivial
  | cons v l ih =>
    intro S L hnone hsome hco
    have h0n := hnone 0 (by simp)
    have h0s := hsome 0 (by simp)
    simp only [List.getElem_cons_zero, rev_zero] at h0n h0s
    -- conditions for the tail
    have tnone : ∀ j (hj : j < l.length), par l[j] = none →
        N l[j] ⊆ U ∪ (rev (insert v S) l j ∪ P (b l[j])) := by
      intro j hj hp
      have := hnone (j + 1) (by simp; omega) (by simpa using hp)
      simpa [rev_cons_succ] using this
    have tco : ∀ j j' (hj : j < j') (hj' : j' < l.length) w, par l[j] = some w →
        par l[j'] = some w → b l[j] = b l[j'] := by
      intro j j' hjj hj' w h1 h2
      have := hco (j + 1) (j' + 1) (by omega) (by simp; omega) w (by simpa using h1)
        (by simpa using h2)
      simpa using this
    cases hp : par v with
    | none =>
      simp only [RelCharged, hp]
      refine ⟨h0n hp, ih (insert v S) L tnone ?_ tco⟩
      intro j hj w hw
      have := hsome (j + 1) (by simp; omega) w (by simpa using hw)
      simpa [rev_cons_succ] using this
    | some w =>
      obtain ⟨hwW, hN, hLw⟩ := h0s w hp
      simp only [RelCharged, hp]
      refine ⟨hwW, hN, hLw, ih (insert v S) _ tnone ?_ tco⟩
      intro j hj w' hw'
      have h1 := hsome (j + 1) (by simp; omega) w' (by simpa using hw')
      simp only [List.getElem_cons_succ, rev_cons_succ] at h1
      obtain ⟨hw'W, hN', hL'⟩ := h1
      refine ⟨hw'W, hN', ?_⟩
      by_cases hww : w' = w
      · subst hww
        rw [Function.update_self]
        have hb : b v = b l[j] := hco 0 (j + 1) (by omega) (by simp; omega) w' (by simpa using hp)
          (by simpa using hw')
        intro x hx
        rcases mem_insert.mp hx with rfl | hx
        · exact mem_union_left _ (by simp [rev])
        · rcases mem_union.mp hx with hxS | hxP
          · exact mem_union_left _ (by simp [rev] at hxS ⊢; tauto)
          · exact mem_union_right _ (hb ▸ hxP)
      · rw [Function.update_of_ne hww]; exact hL'

end HalfRate
