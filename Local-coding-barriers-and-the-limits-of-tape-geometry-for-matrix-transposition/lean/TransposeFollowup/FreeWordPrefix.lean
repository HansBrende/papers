import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced
import Mathlib.GroupTheory.CoprodI
import Mathlib.Tactic

/-! Prefix preservation when a product cannot cancel an entire suffix.
This is the cancellation estimate needed for the short-word free family. -/
namespace TransposeFollowup.FreeWordFamily
open Classical FreeGroup List
set_option autoImplicit false

variable {α : Type*} [DecidableEq α]

theorem prefix_survives (u v : List (α × Bool)) (x : FreeGroup α)
    (huv : IsReduced (u ++ v)) (hx : ¬invRev v <+: x.toWord) :
    u <+: (mk (u ++ v) * x).toWord := by
  induction v using List.reverseRecOn generalizing x with
  | nil => simp at hx
  | append_singleton v a ih =>
    let y : FreeGroup α := mk [a] * x
    have hy : y.toWord = if x.toWord.head? = some (a.1, !a.2)
        then x.toWord.tail else a :: x.toWord := by
      exact toWord_mk_mul_eq a.1 a.2 x
    by_cases hc : x.toWord.head? = some (a.1, !a.2)
    · have hyword : y.toWord = x.toWord.tail := by rw [hy, ite_eq_left hc]
      have hhead : x.toWord = (a.1, !a.2) :: x.toWord.tail := by
        cases he : x.toWord with
        | nil => simp [he] at hc
        | cons b t =>
          have hb : b = (a.1, !a.2) := by simpa only [he, head?_cons, Option.some.injEq] using hc
          simp [hb]
      have hx' : ¬invRev v <+: y.toWord := by
        intro hp
        apply hx
        rw [invRev_append]
        change (a.1, !a.2) :: invRev v <+: x.toWord
        rw [hhead]
        rw [hyword] at hp
        obtain ⟨t, ht⟩ := hp
        exact ⟨t, by simp only [List.cons_append, ht]⟩
      have huv' : IsReduced (u ++ v) :=
        huv.infix ⟨[], [a], by simp [List.append_assoc]⟩
      have he : mk (u ++ (v ++ [a])) * x = mk (u ++ v) * y := by
        simp only [y, ← mul_assoc, mul_mk, List.append_assoc]
      rw [he]
      exact ih y huv' hx'
    · have hyword : y.toWord = a :: x.toWord := by rw [hy, ite_eq_right hc]
      have hared : IsReduced ([a] ++ x.toWord) := by
        change IsReduced (a :: x.toWord)
        rw [← hyword]
        exact isReduced_toWord
      have huv' : IsReduced ((u ++ v) ++ [a]) := by
        simpa only [List.append_assoc] using huv
      have hwhole : IsReduced ((u ++ (v ++ [a])) ++ x.toWord) := by
        simpa only [List.append_assoc] using huv'.append_overlap hared (by simp)
      rw [toWord_mul, toWord_mk, huv.reduce_eq, hwhole.reduce_eq]
      exact ⟨(v ++ [a]) ++ x.toWord, by simp only [List.append_assoc]⟩

def prefixDomain (w : List (α × Bool)) : Set (FreeGroup α) := {x | w <+: x.toWord}

theorem prefixDomain_nonempty {w : List (α × Bool)} (hw : IsReduced w) :
    (prefixDomain w).Nonempty := by
  refine ⟨mk w, ?_⟩
  change w <+: (mk w).toWord
  rw [toWord_mk, hw.reduce_eq]

theorem prefixDomain_disjoint {u v : List (α × Bool)} (hlen : u.length = v.length)
    (hne : u ≠ v) : Disjoint (prefixDomain u) (prefixDomain v) := by
  apply Set.disjoint_left.mpr
  intro x hu hv
  apply hne
  have he := List.prefix_iff_eq_take.mp hu
  have hf := List.prefix_iff_eq_take.mp hv
  rw [hlen] at he
  exact he.trans hf.symm

theorem reduced_double_inverse {w : List (α × Bool)} (hw : IsReduced (w ++ w)) :
    IsReduced (invRev w ++ invRev w) := by
  have h : IsReduced ((mk (w ++ w))⁻¹).toWord := isReduced_toWord
  simpa only [toWord_inv, toWord_mk, hw.reduce_eq, invRev_append] using h

end TransposeFollowup.FreeWordFamily
