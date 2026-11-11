import AdaptiveTransfer.PersistenceGraph
import LeanMachine.FiniteMaskFibres

/-! The finite horizon word has an injective blank extension to the actual
whole tape. Forgetting the head therefore pays exactly the finite head menu,
even when the output variable is the entire infinite native tape word. -/

namespace AdaptiveTransfer.PersistenceGraph
open Transpose Transpose.Tape Transpose.Tape.Impl LeanMachine Finset
attribute [local instance] Classical.propDecidable

def extendWord {A : Type*} (blank : A) (T : ℕ) (v : Fin (2 * T + 1) → A) : ℤ → A :=
  fun z => if |z| ≤ T then v (posCode T z) else blank

theorem extendWord_address {A : Type*} (blank : A) (T : ℕ)
    (v : Fin (2 * T + 1) → A) (i : Fin (2 * T + 1)) :
    extendWord blank T v (address T i) = v i := by
  have hi := i.isLt
  have hb : |address T i| ≤ T := by rw [abs_le]; dsimp [address]; omega
  simp only [extendWord, hb, ite_true, posCode_address]

theorem extendWord_injective {A : Type*} (blank : A) (T : ℕ) :
    Function.Injective (extendWord blank T) := by
  intro v w he
  funext i
  simpa only [extendWord_address] using congrFun he (address T i)

theorem extendWord_vertex (M : TM) (w : List Bool) {T t : ℕ} (h : Fin M.k) (ht : t ≤ T) :
    extendWord (0 : Fin (M.g + 1)) T (vertex M w T t h).1 = (run M w t).work h := by
  funext z
  by_cases hz : |z| ≤ T
  · simp only [extendWord, hz, ite_true, vertex, min_eq_left ht, address_posCode hz]
  · simp only [extendWord, hz, ite_false]
    symm
    apply work_eq_blank
    intro u hu he
    have hb := abs_workPos_le (M := M) w u h
    rw [he] at hb
    exact hz (hb.trans (by exact_mod_cast hu.le.trans ht))

/-- Each whole-word fibre has at most one finite word and all possible heads. -/
theorem whole_word_fibre {A : Type*} [Fintype A] [DecidableEq A]
    (blank : A) (T : ℕ) (v : ℤ → A) :
    ((univ : Finset (FiniteTapeGraph.Vertex A (2 * T + 1))).filter
      (fun x : FiniteTapeGraph.Vertex A (2 * T + 1) => extendWord blank T x.1 = v)).card ≤ 2 * T + 1 := by
  classical
  let D := (univ : Finset (FiniteTapeGraph.Vertex A (2 * T + 1))).filter
    (fun x => extendWord blank T x.1 = v)
  let f (x : D) := x.val.2
  have hf : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    apply Prod.ext
    · apply extendWord_injective blank T
      exact (mem_filter.mp x.property).2.trans (mem_filter.mp y.property).2.symm
    · exact he
  have hh := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe, Fintype.card_fin] using hh

end AdaptiveTransfer.PersistenceGraph
