import SharedDecoders.CapacityAmbient
import Mathlib.Data.Finset.Card

/-!
# Binary runs along a cyclic translation

Runs are represented by their starting cells and a finite constant prefix.
No choice of a list of cycles or of a maximal run is part of the definitions.
-/

namespace SharedDecoders
namespace CapacityRuns

open Finset
attribute [local instance] Classical.propDecidable

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- A constant prefix of length `r`, beginning at `x`, along the step `s`. -/
def Prefix (p : G → Bool) (s : G) (r : ℕ) (x : G) : Prop :=
  ∀ j < r, p (x + j • s) = p x

/-- A run start with at least `r` cells. Constant translation orbits have no starts. -/
def Start (p : G → Bool) (s : G) (r : ℕ) (x : G) : Prop :=
  p (x - s) ≠ p x ∧ Prefix p s r x

noncomputable def runCount (p : G → Bool) (s : G) (r : ℕ) : ℕ :=
  by classical exact Fintype.card {x // Start p s r x}

noncomputable def changeCount (p : G → Bool) (s : G) : ℕ :=
  Fintype.card {x // p (x + s) ≠ p x}

omit [Fintype G] [DecidableEq G] in
theorem prefix_one (p : G → Bool) (s x : G) : Prefix p s 1 x := by
  intro j hj
  have : j = 0 := by omega
  simp [this]

omit [DecidableEq G] in
/-- Translating a boundary to the start on its right preserves its count. -/
theorem runCount_one (p : G → Bool) (s : G) :
    runCount p s 1 = changeCount p s := by
  classical
  unfold runCount changeCount
  apply Fintype.card_congr
  exact {
    toFun := fun x => ⟨x.1 - s, by simpa using x.2.1.symm⟩
    invFun := fun x => ⟨x.1 + s, by
      refine ⟨?_, prefix_one p s _⟩
      simpa using x.2.symm⟩
    left_inv := by intro x; apply Subtype.ext; simp
    right_inv := by intro x; apply Subtype.ext; simp }

omit [DecidableEq G] in
theorem card_filter_translate (P : G → Prop) (s : G) [DecidablePred P] :
    (univ.filter (fun x => P (x + s))).card = (univ.filter P).card := by
  classical
  apply Finset.card_bij (fun x _ => x + s)
  · intro x hx
    simpa using hx
  · intro x _ y _ h
    exact add_right_cancel h
  · intro y hy
    exact ⟨y - s, by simpa using hy, by simp⟩

/-- In a finite cyclic motion the number of entries into any predicate equals
the number of exits. This is independent of the colouring and the orbit lengths. -/
theorem boundary_balance (P : G → Prop) (s : G) [DecidablePred P] :
    (univ.filter (fun x => P x ∧ ¬P (x + s))).card =
      (univ.filter (fun x => ¬P x ∧ P (x + s))).card := by
  classical
  let A := univ.filter P
  let B := univ.filter (fun x => P (x + s))
  have hc : A.card = B.card := (card_filter_translate P s).symm
  have ha : A \ B = univ.filter (fun x => P x ∧ ¬P (x + s)) := by
    ext x; simp [A, B]
  have hb : B \ A = univ.filter (fun x => ¬P x ∧ P (x + s)) := by
    ext x; simp [A, B, and_comm]
  simpa [ha, hb] using Finset.card_sdiff_comm hc

omit [Fintype G] [DecidableEq G] in
theorem start_iff_prefix_boundary {p : G → Bool} {s x : G} {r : ℕ} (hr : 2 ≤ r) :
    Start p s r x ↔ Prefix p s r x ∧ ¬Prefix p s r (x - s) := by
  constructor
  · rintro ⟨hchange, hp⟩
    refine ⟨hp, fun hprev => ?_⟩
    have he := hprev 1 (by omega)
    simp only [one_nsmul, sub_add_cancel] at he
    exact hchange he.symm
  · rintro ⟨hp, hn⟩
    refine ⟨?_, hp⟩
    intro he
    apply hn
    intro j hj
    by_cases hj0 : j = 0
    · simp [hj0]
    · have hj' : j - 1 < r := by omega
      have heq : x - s + j • s = x + (j - 1) • s := by
        have : j = (j - 1) + 1 := by omega
        rw [this, add_nsmul, one_nsmul]
        abel
      rw [heq, hp _ hj', he]

def End (p : G → Bool) (s : G) (r : ℕ) (x : G) : Prop :=
  Prefix p s r x ∧ p (x + r • s) ≠ p x

omit [Fintype G] [DecidableEq G] in
theorem end_iff_prefix_boundary {p : G → Bool} {s x : G} {r : ℕ} (hr : 2 ≤ r) :
    End p s r x ↔ Prefix p s r x ∧ ¬Prefix p s r (x + s) := by
  constructor
  · rintro ⟨hp, hn⟩
    refine ⟨hp, fun hnext => ?_⟩
    have he := hnext (r - 1) (by omega)
    have heq : x + s + (r - 1) • s = x + r • s := by
      have hn : (r - 1) + 1 = r := by omega
      calc
        _ = x + ((r - 1) + 1) • s := by rw [add_nsmul, one_nsmul]; abel
        _ = _ := by rw [hn]
    have hp1 : p (x + s) = p x := by simpa using hp 1 (by omega)
    rw [heq, hp1] at he
    exact hn he
  · rintro ⟨hp, hn⟩
    refine ⟨hp, fun he => ?_⟩
    apply hn
    intro j hj
    have heq : x + s + j • s = x + (j + 1) • s := by
      rw [add_nsmul, one_nsmul]
      abel
    have hp1 : p (x + s) = p x := by simpa using hp 1 (by omega)
    rw [heq, hp1]
    by_cases hlast : j + 1 = r
    · simpa [hlast] using he
    · exact hp (j + 1) (by omega)

/-- Starts and ends of runs of at least two cells have the same cardinality. -/
theorem end_card_eq_runCount (p : G → Bool) (s : G) {r : ℕ} (hr : 2 ≤ r) :
    Fintype.card {x // End p s r x} = runCount p s r := by
  classical
  let P := Prefix p s r
  have htranslate := card_filter_translate (fun x => P x ∧ ¬P (x - s)) s
  have hbalance := boundary_balance P s
  have hs : (univ.filter (fun x => P x ∧ ¬P (x - s))).card = runCount p s r := by
    simp only [runCount, Fintype.card_subtype]
    congr 1
    ext x
    simp only [mem_filter, mem_univ, true_and]
    exact (start_iff_prefix_boundary hr).symm
  have he : (univ.filter (fun x => P x ∧ ¬P (x + s))).card =
      Fintype.card {x // End p s r x} := by
    simp only [Fintype.card_subtype]
    congr 1
    ext x
    simp only [mem_filter, mem_univ, true_and]
    exact (end_iff_prefix_boundary hr).symm
  have ht : (univ.filter (fun x => ¬P x ∧ P (x + s))).card =
      (univ.filter (fun x => P x ∧ ¬P (x - s))).card := by
    simpa only [add_sub_cancel_right, and_comm] using htranslate
  omega

omit [Fintype G] [DecidableEq G] in
theorem prefix_two_iff (p : G → Bool) (s x : G) :
    Prefix p s 2 x ↔ p (x + s) = p x := by
  constructor
  · intro h; simpa using h 1 (by omega)
  · intro h j hj
    have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl
    · simp
    · simpa using h

/-- The binary two-step identity, without assumptions on the order of `s`. -/
theorem changeCount_double (p : G → Bool) (s : G) :
    changeCount p (2 • s) = 2 * runCount p s 2 := by
  classical
  let A := univ.filter (fun x => Start p s 2 (x + s))
  let B := univ.filter (fun x => End p s 2 x)
  have hsplit (x : G) : p (x + 2 • s) ≠ p x ↔
      Start p s 2 (x + s) ∨ End p s 2 x := by
    have he : x + s + s = x + 2 • s := by simp [two_nsmul, add_assoc]
    cases hx : p x <;> cases hm : p (x + s) <;> cases ht : p (x + 2 • s) <;>
      simp [Start, End, prefix_two_iff, he, hx, hm, ht]
  have hdis : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have hs := (mem_filter.mp hx).2.1
    have he := (prefix_two_iff p s x).mp (mem_filter.mp hy).2.1
    exact hs (by simpa using he.symm)
  have hc : changeCount p (2 • s) = (A ∪ B).card := by
    unfold changeCount
    rw [Fintype.card_subtype]
    congr 1
    ext x
    simp [A, B, hsplit]
  have ha : A.card = runCount p s 2 := by
    simpa only [A, runCount, Fintype.card_subtype] using
      card_filter_translate (Start p s 2) s
  have hb : B.card = runCount p s 2 := by
    simpa only [B, Fintype.card_subtype] using end_card_eq_runCount p s (by omega : 2 ≤ 2)
  rw [hc, Finset.card_union_of_disjoint hdis, ha, hb]
  omega

omit [Fintype G] [DecidableEq G] in
/-- Two interior cells of run prefixes coincide only if their starts and offsets
coincide. The statement includes short cycles and the zero translation. -/
theorem start_offset_injective {p : G → Bool} {s x y : G} {r t i j : ℕ}
    (hx : Start p s r x) (hy : Start p s t y) (hi : i < r) (hj : j < t)
    (he : x + i • s = y + j • s) : i = j ∧ x = y := by
  have exclude (x y : G) (r t i j : ℕ)
      (hx : Start p s r x) (hy : Start p s t y)
      (hi : i < r) (hj : j < t)
      (he : x + i • s = y + j • s) (hij : i < j) : False := by
    have hji : j - i < t := by omega
    have hji' : j - i - 1 < t := by omega
    have hsum : i + (j - i) = j := by omega
    have hpos : 1 ≤ j - i := by omega
    have hx' : x = y + (j - i) • s := by
      apply add_right_cancel (b := i • s)
      rw [he, add_assoc, ← add_nsmul]
      rw [show j - i + i = j by omega]
    have hxprev : x - s = y + (j - i - 1) • s := by
      rw [hx']
      have hn : j - i = (j - i - 1) + 1 := by omega
      rw [hn, add_nsmul, one_nsmul]
      abel
    exact hx.1 (by rw [hxprev, hx', hy.2 _ hji', hy.2 _ hji])
  have hij : i = j := by
    rcases lt_trichotomy i j with h | h | h
    · exact False.elim (exclude x y r t i j hx hy hi hj he h)
    · exact h
    · exact False.elim (exclude y x t r j i hy hx hj hi he.symm h)
  refine ⟨hij, ?_⟩
  simpa [hij] using he

private def ticketLength (i : Fin 6) : ℕ :=
  if i = 0 then 1 else if i = 1 then 2 else if i < 4 then 4 else 13

private theorem ticket_lt (i : Fin 6) : i.val < ticketLength i := by
  fin_cases i <;> norm_num [ticketLength]

omit [DecidableEq G] in
/-- The precise weighted run budget used by the three-stage translate bound. -/
theorem weighted_run_budget (p : G → Bool) (s : G) :
    changeCount p s + runCount p s 2 + 2 * runCount p s 4 +
      2 * runCount p s 13 ≤ Fintype.card G := by
  classical
  let Tickets := Σ i : Fin 6, {x // Start p s (ticketLength i) x}
  let mark : Tickets → G := fun t => t.2.1 + t.1.val • s
  have hinj : Function.Injective mark := by
    intro a b hab
    obtain ⟨hidx, hx⟩ := start_offset_injective a.2.2 b.2.2
      (ticket_lt a.1) (ticket_lt b.1) hab
    have hi : a.1 = b.1 := Fin.ext hidx
    cases a with
    | mk i x =>
      cases b with
      | mk j y =>
        dsimp at hi hx
        subst j
        congr 1
        exact Subtype.ext hx
  have hcard := Fintype.card_le_of_injective mark hinj
  have hsum : Fintype.card Tickets =
      runCount p s 1 + runCount p s 2 + 2 * runCount p s 4 +
        2 * runCount p s 13 := by
    change Fintype.card (Sigma (fun i : Fin 6 => {x // Start p s (ticketLength i) x})) = _
    rw [Fintype.card_sigma]
    simp only [Fin.sum_univ_succ]
    norm_num [ticketLength, runCount]
    omega
  rw [hsum, runCount_one] at hcard
  exact hcard

end CapacityRuns
end SharedDecoders
