import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

/-! Finite guards for delayed output ordinals and bounded look-ahead.
Repeated bit values are irrelevant: all statements count distinct ordinals. -/

namespace LeanMachine.FiniteOrdinalGuards
open Finset
attribute [local instance] Classical.propDecidable

noncomputable def delayed {P : ℕ} (root shadow : Fin P → ℕ) (c : ℕ) : Finset (Fin P) :=
  univ.filter fun i => root i < c ∧ c ≤ shadow i

theorem delayed_card_le {P K : ℕ} {root shadow : Fin P → ℕ} {O : ℕ → ℕ}
    (hO : Monotone O) (hroot : ∀ i c, root i < c → i.val < O c)
    (hpre : ∀ i, O (shadow i) ≤ i.val + K) (c : ℕ) :
    (delayed root shadow c).card ≤ K := by
  have hb : ∀ i ∈ delayed root shadow c, i.val ∈ Ico (O c - K) (O c) := by
    intro i hi
    obtain ⟨hr, hs⟩ := (mem_filter.mp hi).2
    have hu := hroot i c hr
    have hl := (hO hs).trans (hpre i)
    exact mem_Ico.mpr ⟨by omega, hu⟩
  have hc := card_le_card_of_injOn Fin.val hb (fun _ _ _ _ he => Fin.ext he)
  rw [Nat.card_Ico] at hc
  omega

noncomputable def delayedUnion {P : ℕ} (root shadow : Fin P → ℕ) (C : Finset ℕ) : Finset (Fin P) :=
  C.biUnion (delayed root shadow)

theorem delayedUnion_card_le {P K : ℕ} {root shadow : Fin P → ℕ} {O : ℕ → ℕ}
    (hO : Monotone O) (hroot : ∀ i c, root i < c → i.val < O c)
    (hpre : ∀ i, O (shadow i) ≤ i.val + K) (C : Finset ℕ) :
    (delayedUnion root shadow C).card ≤ C.card * K := by
  calc
    _ ≤ ∑ c ∈ C, (delayed root shadow c).card := card_biUnion_le
    _ ≤ ∑ _c ∈ C, K := sum_le_sum fun c _ => delayed_card_le hO hroot hpre c
    _ = _ := by simp

noncomputable def lookahead {P : ℕ} (root : Fin P → ℕ) (K c : ℕ) : Finset (Fin P) :=
  univ.filter fun i => ∃ j : Fin P, j.val = i.val + K ∧ root i ≤ c ∧ c ≤ root j

/-- A cut time lies in at most K+1 closed output-ordinal windows of length K.
This includes both endpoints and does not bound physical waiting time. -/
theorem lookahead_card_le {P K : ℕ} {root : Fin P → ℕ}
    (hroot : StrictMono root) (c : ℕ) : (lookahead root K c).card ≤ K + 1 := by
  let S := lookahead root K c
  rcases S.eq_empty_or_nonempty with hS | hS
  · simp only [show lookahead root K c = ∅ from hS, card_empty, zero_le]
  let i₀ := S.min' hS
  have hi₀ : i₀ ∈ S := min'_mem S hS
  obtain ⟨j₀, hj₀, _hl, hu⟩ := (mem_filter.mp hi₀).2
  have hb : ∀ i ∈ S, i.val ∈ Icc i₀.val (i₀.val + K) := by
    intro i hi
    obtain ⟨j, _hj, hl, _hu⟩ := (mem_filter.mp hi).2
    have hlow := min'_le S i hi
    have hhigh := hroot.le_iff_le.mp (hl.trans hu)
    exact mem_Icc.mpr ⟨hlow, by change i.val ≤ j₀.val at hhigh; omega⟩
  have hc := card_le_card_of_injOn Fin.val hb (fun _ _ _ _ he => Fin.ext he)
  rw [Nat.card_Icc] at hc
  change S.card ≤ K + 1
  omega

noncomputable def lookaheadUnion {P : ℕ} (root : Fin P → ℕ) (K : ℕ) (B : Finset ℕ) :
    Finset (Fin P) := B.biUnion (lookahead root K)

theorem lookaheadUnion_card_le {P K : ℕ} {root : Fin P → ℕ}
    (hroot : StrictMono root) (B : Finset ℕ) :
    (lookaheadUnion root K B).card ≤ B.card * (K + 1) := by
  calc
    _ ≤ ∑ c ∈ B, (lookahead root K c).card := card_biUnion_le
    _ ≤ ∑ _c ∈ B, (K + 1) := sum_le_sum fun c _ => lookahead_card_le hroot c
    _ = _ := by simp

def terminal (P K : ℕ) : Finset (Fin P) := univ.filter fun i => P ≤ i.val + K

theorem terminal_card_le (P K : ℕ) : (terminal P K).card ≤ K := by
  have hb : ∀ i ∈ terminal P K, i.val ∈ Ico (P - K) P := by
    intro i hi
    exact mem_Ico.mpr ⟨by have := (mem_filter.mp hi).2; omega, i.isLt⟩
  have hc := card_le_card_of_injOn Fin.val hb (fun _ _ _ _ he => Fin.ext he)
  rw [Nat.card_Ico] at hc
  omega

end LeanMachine.FiniteOrdinalGuards
