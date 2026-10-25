import SubcubicMemo.SquareFork

/-! A uniform good target for closed ladders. Adding two rungs folds back
over the first edge, so four finite base maps suffice. -/

namespace SubcubicMemo.Squares

open MotionDepthCodes
open scoped Classical

def ladderAdj (n : ℕ) (twist : Bool) (x y : Fin n × Bool) : Prop :=
  (x.1 = y.1 ∧ x.2 ≠ y.2) ∨
  ((x.1.val + 1 = y.1.val ∨ y.1.val + 1 = x.1.val) ∧ x.2 = y.2) ∨
  (((x.1.val = 0 ∧ y.1.val + 1 = n) ∨ (y.1.val = 0 ∧ x.1.val + 1 = n)) ∧
    x.1 ≠ y.1 ∧ (x.2 ^^ y.2) = twist)

def closedLadder (n : ℕ) (twist : Bool) : SimpleGraph (Fin n × Bool) where
  Adj := ladderAdj n twist
  symm := ⟨by
    intro x y h
    rcases h with h | h | h
    · exact Or.inl ⟨h.1.symm, Ne.symm h.2⟩
    · exact Or.inr (Or.inl ⟨h.1.symm,h.2.symm⟩)
    · exact Or.inr (Or.inr ⟨h.1.symm,Ne.symm h.2.1,by simpa [Bool.xor_comm] using h.2.2⟩)⟩
  loopless := ⟨by
    intro x h
    rcases h with h | h | h
    · exact h.2 rfl
    · omega
    · exact h.2.1 rfl⟩

instance (n : ℕ) (t : Bool) : DecidableRel (closedLadder n t).Adj := by
  unfold closedLadder ladderAdj
  infer_instance

def foldRungs (n : ℕ) (hn : 2 ≤ n) (i : Fin (n+2)) : Fin n :=
  ⟨if i.val < 2 then i.val else i.val - 2, by split_ifs <;> omega⟩

theorem foldRungs_rail {n : ℕ} (hn : 2 ≤ n) {i j : Fin (n+2)}
    (h : i.val+1=j.val ∨ j.val+1=i.val) :
    (foldRungs n hn i).val+1=(foldRungs n hn j).val ∨
    (foldRungs n hn j).val+1=(foldRungs n hn i).val := by
  simp only [foldRungs]
  split_ifs <;> omega

def foldLadder (n : ℕ) (hn : 2 ≤ n) (t : Bool) :
    closedLadder (n+2) t →g closedLadder n t where
  toFun x := (foldRungs n hn x.1,x.2)
  map_rel' := by
    intro x y h
    rcases h with h | h | h
    · exact Or.inl ⟨congrArg (foldRungs n hn) h.1,h.2⟩
    · exact Or.inr (Or.inl ⟨foldRungs_rail hn h.1,h.2⟩)
    · apply Or.inr; apply Or.inr
      refine ⟨?_,?_,h.2.2⟩
      · simp only [foldRungs]
        rcases h.1 with h | h <;> split_ifs <;> omega
      · intro he
        have he' := congrArg Fin.val he
        simp only [foldRungs] at he'
        rcases h.1 with h | h <;> split_ifs at he' <;> omega

def parityColor {n : ℕ} (x : Fin n × Bool) : Fin 8 :=
  if (x.1.val % 2 == 1) ^^ x.2 then 3 else 0

theorem base_three : Nonempty (closedLadder 3 true →g circularClique 8 3) := by
  exact ⟨⟨parityColor,by decide⟩⟩

theorem base_four_untwisted : Nonempty (closedLadder 4 false →g circularClique 8 3) := by
  exact ⟨⟨parityColor,by decide⟩⟩

def mobiusColor (x : Fin 4 × Bool) : Fin 8 :=
  ⟨(3 * (x.1.val + if x.2 then 4 else 0)) % 8, Nat.mod_lt _ (by decide)⟩

theorem base_four_twisted : Nonempty (closedLadder 4 true →g circularClique 8 3) := by
  exact ⟨⟨mobiusColor,by decide⟩⟩

def prismColor (x : Fin 5 × Bool) : Fin 8 :=
  ⟨(3 * ((x.1.val + if x.2 then 1 else 0) % 5)) % 8, Nat.mod_lt _ (by decide)⟩

theorem base_five_untwisted : Nonempty (closedLadder 5 false →g circularClique 8 3) := by
  exact ⟨⟨prismColor,by decide⟩⟩

theorem ladder_target (n : ℕ) (t : Bool) (hn : 3 ≤ n) (hsmall : n = 3 → t = true) :
    Nonempty (closedLadder n t →g circularClique 8 3) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h3 : n = 3
    · subst n; rw [hsmall rfl]; exact base_three
    by_cases h4 : n = 4
    · subst n
      cases t
      · exact base_four_untwisted
      · exact base_four_twisted
    by_cases h5 : n = 5
    · subst n
      cases t
      · exact base_five_untwisted
      · exact ⟨base_three.some.comp (foldLadder 3 (by omega) true)⟩
    have h6 : 6 ≤ n := by omega
    obtain ⟨f⟩ := ih (n-2) (by omega) (by omega) (by omega)
    have he : n-2+2=n := by omega
    exact he ▸ ⟨f.comp (foldLadder (n-2) (by omega) t)⟩

end SubcubicMemo.Squares
