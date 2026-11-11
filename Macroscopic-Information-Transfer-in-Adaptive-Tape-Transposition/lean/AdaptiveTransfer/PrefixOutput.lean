import AdaptiveTransfer.NativeReplayAdapters
import Mathlib.Data.List.Infix

/-! Strict prior output reconstructed from earlier retained appends and exterior
input bits. Chronology and the output permutation are proved to prevent a
retained witness from referring to a future output. No prefix decoder is assumed.
-/

namespace AdaptiveTransfer.PrefixOutput

open Finset

/-- The chronological output produced by the actual optional append sequence. -/
def word (emit : ℕ → Option Bool) (t : ℕ) : List Bool := (List.range t).filterMap emit

@[simp] theorem word_zero (emit : ℕ → Option Bool) : word emit 0 = [] := rfl

theorem word_add (emit : ℕ → Option Bool) (t n : ℕ) :
    word emit (t + n) = word emit t ++ (List.range n).filterMap (fun i => emit (t + i)) := by
  simp [word, List.range_add]

theorem word_succ (emit : ℕ → Option Bool) (t : ℕ) :
    word emit (t + 1) = word emit t ++ (emit t).toList := by
  rw [word_add]
  cases h : emit t <;> simp [h]

theorem length_succ (emit : ℕ → Option Bool) (t : ℕ) :
    (word emit (t + 1)).length = (word emit t).length + if (emit t).isSome then 1 else 0 := by
  rw [word_succ, List.length_append]
  cases emit t <;> rfl

theorem length_mono (emit : ℕ → Option Bool) : Monotone (fun t => (word emit t).length) := by
  apply monotone_nat_of_le_succ
  intro t
  rw [length_succ]
  omega

theorem getElem_stable (emit : ℕ → Option Bool) {t N j : ℕ} (htN : t ≤ N)
    (hj : j < (word emit t).length) : (word emit N)[j]? = (word emit t)[j]? := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le htN
  rw [word_add, List.getElem?_append_left hj]

/-- An actual append occupies its old output count in every later prefix. -/
theorem emitted_at_count (emit : ℕ → Option Bool) {t N : ℕ} {bit : Bool}
    (htN : t < N) (hb : emit t = some bit) :
    (word emit N)[(word emit t).length]? = some bit := by
  have hj : (word emit t).length < (word emit (t + 1)).length := by
    rw [length_succ, hb]
    simp
  rw [getElem_stable emit (Nat.succ_le_of_lt htN) hj, word_succ, hb]
  simp

/-- Every earlier ordinal has an actual chronological append witness. -/
theorem exists_append_between (emit : ℕ → Option Bool) {a e j : ℕ}
    (hae : a ≤ e) (ha : (word emit a).length ≤ j) (he : j < (word emit e).length) :
    ∃ t, a ≤ t ∧ t < e ∧ (word emit t).length = j ∧ (emit t).isSome := by
  induction e, hae using Nat.le_induction with
  | base => omega
  | succ e hae ih =>
    by_cases hj : j < (word emit e).length
    · obtain ⟨t, hat, hte, hc, ho⟩ := ih hj
      exact ⟨t, hat, by omega, hc, ho⟩
    · have hc := length_succ emit e
      have ho : (emit e).isSome := by
        by_contra hn
        simp only [Bool.not_eq_true] at hn
        simp only [hn, Bool.false_eq_true, ite_false, add_zero] at hc
        omega
      simp only [ho, ite_true] at hc
      exact ⟨e, hae, by omega, by omega, ho⟩

/-- Equality of past retained append data and the exterior determines the entire
strict prefix. Injectivity of the public output permutation is used to identify
the retained witness's ordinal, whose strict precedence then follows from counts. -/
theorem strictPrefix_eq {P : ℕ} {X Y : Fin P → Bool}
    (π : Fin P → Fin P) (hπ : Function.Injective π)
    (emitE emitF : ℕ → Option Bool) (NE NF t : ℕ)
    (htE : t ≤ NE) (htF : t ≤ NF)
    (hfinalE : word emitE NE = List.ofFn (fun j => X (π j)))
    (hfinalF : word emitF NF = List.ofFn (fun j => Y (π j)))
    (C : Finset ℕ) (U : Finset (Fin P))
    (hcount : (word emitE t).length = (word emitF t).length)
    (hcover : ∀ p ∈ U, ∃ u ∈ C, ∃ j : Fin P,
      π j = p ∧ (word emitE u).length = j.val ∧ (emitE u).isSome)
    (hearlier : ∀ u ∈ C, u < t →
      (word emitE u).length = (word emitF u).length ∧ emitE u = emitF u)
    (hexterior : ∀ p ∉ U, X p = Y p) : word emitE t = word emitF t := by
  apply List.ext_getElem?
  intro j
  by_cases hj : j < (word emitE t).length
  · have hjP : j < P := by
      have hh := length_mono emitE htE
      dsimp only at hh
      rw [hfinalE, List.length_ofFn] at hh
      omega
    let i : Fin P := ⟨j, hjP⟩
    have hE : (word emitE t)[j]? = some (X (π i)) := by
      rw [← getElem_stable emitE htE hj, hfinalE]
      simp [i, hjP]
    have hF : (word emitF t)[j]? = some (Y (π i)) := by
      rw [← getElem_stable emitF htF (by omega), hfinalF]
      simp [i, hjP]
    rw [hE, hF]
    congr 1
    by_cases hp : π i ∈ U
    · obtain ⟨u, huC, i', hpi, hcu, hem⟩ := hcover _ hp
      have hii : i' = i := hπ hpi
      subst i'
      have hut : u < t := by
        by_contra hn
        have hh := length_mono emitE (show t ≤ u by omega)
        dsimp only at hh
        rw [hcu] at hh
        dsimp [i] at hh
        omega
      obtain ⟨hcnt, hemit⟩ := hearlier u huC hut
      obtain ⟨bit, hb⟩ := Option.isSome_iff_exists.mp hem
      have he := emitted_at_count emitE (hut.trans_le htE) hb
      rw [hfinalE, hcu] at he
      have hf := emitted_at_count emitF (hut.trans_le htF) (hemit.symm.trans hb)
      rw [hfinalF, ← hcnt, hcu] at hf
      simpa only [List.getElem?_ofFn, dite_eq_left i.isLt, Option.some.injEq] using he.trans hf.symm
    · exact hexterior _ hp
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

open Transpose Transpose.Tape Transpose.Tape.Impl

/-- The generic word is exactly the actual native strict output, including
frozen post-halt configurations. -/
theorem native_word (M : TM) (w : List Bool) (t : ℕ) :
    word (outBit M w) t = (run M w t).outRev.reverse :=
  (outRev_reverse_eq (M := M) (w := w) t).symm

end AdaptiveTransfer.PrefixOutput
