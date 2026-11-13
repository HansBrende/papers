import LeanMachine.BoundedWeight.Bounds
import LeanMachine.BoundedWeight.Closure
import Mathlib.Data.List.Induction

/-! Odd products of bounded-weight decoders and their adjoints. -/

namespace LeanMachine.BoundedWeight

open scoped Matrix Kronecker

variable {d : ℕ}

/-- An odd product of swapped tensor combinations is itself a single swapped
tensor combination. Different factors may have different weights. -/
theorem exists_odd_product_core
    (l : List (Matrix (Idx d) (Idx d) ℂ × ℝ))
    (hl : ∀ p ∈ l, HasWeight p.1 p.2) (ho : Odd l.length) :
    ∃ Q, HasWeight Q (l.map Prod.snd).prod ∧
      (l.map (fun p => T p.1)).prod = T Q := by
  induction l using List.twoStepInduction with
  | nil => simp at ho
  | singleton p =>
    refine ⟨p.1, ?_, ?_⟩
    · simpa using hl p (by simp)
    · simp
  | cons_cons a b l ih _ =>
    have hl' : ∀ p ∈ l, HasWeight p.1 p.2 := fun p hp => hl p (by simp [hp])
    have ho' : Odd l.length := by
      simpa [Nat.odd_add_one] using ho
    obtain ⟨Q, hQ, he⟩ := ih hl' ho'
    refine ⟨a.1 * (swapMat d * b.1 * swapMat d) * Q, ?_, ?_⟩
    · simpa only [List.map_cons, List.prod_cons, mul_assoc] using
        ((hl a (by simp)).mul (hl b (by simp)).swap_conj).mul hQ
    · rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons, he]
      simp only [T, Matrix.mul_assoc]

/-- The odd-product trace bound with the product of the individual weights. -/
theorem norm_trace_odd_product_le
    (l : List (Matrix (Idx d) (Idx d) ℂ × ℝ))
    (hl : ∀ p ∈ l, HasWeight p.1 p.2) (ho : Odd l.length) :
    ‖(l.map (fun p => T p.1)).prod.trace‖ ≤ (l.map Prod.snd).prod * d := by
  obtain ⟨Q, hQ, he⟩ := exists_odd_product_core l hl ho
  rw [he]
  exact hQ.norm_trace_T_le

/-- The tensor combination left after taking out the leading transpose from
either `T K` or its adjoint. -/
def letterCore (K : Matrix (Idx d) (Idx d) ℂ) (b : Bool) : Matrix (Idx d) (Idx d) ℂ :=
  if b then K else swapMat d * Kᴴ * swapMat d

/-- Both kinds of letters have a core of the original weight. -/
theorem HasWeight.letterCore {K : Matrix (Idx d) (Idx d) ℂ} {γ : ℝ}
    (h : HasWeight K γ) (b : Bool) : HasWeight (letterCore K b) γ := by
  cases b
  · exact h.conjTranspose.swap_conj
  · exact h

/-- Reattaching transpose recovers the letter or its adjoint. -/
theorem T_letterCore (K : Matrix (Idx d) (Idx d) ℂ) (b : Bool) :
    T (letterCore K b) = if b then T K else (T K)ᴴ := by
  cases b <;> simp [letterCore, T, Matrix.conjTranspose_mul, conjTranspose_swapMat,
    ← Matrix.mul_assoc, swapMat_mul_self]

/-- A word can choose its decoder as well as whether to take its adjoint. -/
def mixedWord {ι : Type*} (K : ι → Matrix (Idx d) (Idx d) ℂ) :
    List (ι × Bool) → Matrix (Idx d) (Idx d) ℂ
  | [] => 1
  | p :: w => (if p.2 then T (K p.1) else (T (K p.1))ᴴ) * mixedWord K w

/-- Each mixed word is an ordinary product of the corresponding swapped cores. -/
theorem mixedWord_eq_prod {ι : Type*} (K : ι → Matrix (Idx d) (Idx d) ℂ)
    (w : List (ι × Bool)) :
    mixedWord K w = (w.map (fun p => T (letterCore (K p.1) p.2))).prod := by
  induction w with
  | nil => rfl
  | cons p w ih => simp only [mixedWord, List.map_cons, List.prod_cons, T_letterCore, ih]

/-- A1 with different decoders and different weights at the different positions. -/
theorem norm_trace_mixedWord_le {ι : Type*} (K : ι → Matrix (Idx d) (Idx d) ℂ)
    (γ : ι → ℝ) (w : List (ι × Bool))
    (h : ∀ p ∈ w, HasWeight (K p.1) (γ p.1)) (hw : Odd w.length) :
    ‖(mixedWord K w).trace‖ ≤ (w.map (fun p => γ p.1)).prod * d := by
  have hl : ∀ p ∈ w.map (fun p => (letterCore (K p.1) p.2, γ p.1)),
      HasWeight p.1 p.2 := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact (h q hq).letterCore q.2
  have ht := norm_trace_odd_product_le _ hl (by simpa only [List.length_map] using hw)
  simpa only [List.map_map, Function.comp_def, ← mixedWord_eq_prod] using ht

/-- The original word convention: `true` is `T K`, `false` is its adjoint. -/
def word (K : Matrix (Idx d) (Idx d) ℂ) : List Bool → Matrix (Idx d) (Idx d) ℂ
  | [] => 1
  | b :: w => (if b then T K else (T K)ᴴ) * word K w

/-- A fixed-decoder word is the corresponding mixed word with a single index. -/
theorem word_eq_mixedWord (K : Matrix (Idx d) (Idx d) ℂ) (w : List Bool) :
    word K w = mixedWord (fun _ : Unit => K) (w.map (fun b => ((), b))) := by
  induction w with
  | nil => rfl
  | cons b w ih => simp only [word, List.map_cons, mixedWord, ih]

/-- Backlog A1: every odd word in `T K` and its adjoint has a trace of
magnitude at most `γ ^ length * d`. -/
theorem norm_trace_word_le {K : Matrix (Idx d) (Idx d) ℂ} {γ : ℝ}
    (h : HasWeight K γ) (w : List Bool) (hw : Odd w.length) :
    ‖(word K w).trace‖ ≤ γ ^ w.length * d := by
  rw [word_eq_mixedWord]
  have ht := norm_trace_mixedWord_le (fun _ : Unit => K) (fun _ => γ)
    (w.map (fun b => ((), b))) (fun _ _ => h) (by simpa only [List.length_map] using hw)
  simpa only [List.map_map, Function.comp_def, List.map_const', List.prod_replicate] using ht

end LeanMachine.BoundedWeight
