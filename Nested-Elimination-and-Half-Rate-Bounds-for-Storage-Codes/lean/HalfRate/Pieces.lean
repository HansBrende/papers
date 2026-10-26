import HalfRate.Positional
import HalfRate.Corollaries

/-!
# General piece certificates

* `PieceCert.mono`: certificates transfer to sub-relations (fewer arcs).
* `exists_relCharged`, `pieceCert_of_elim`: an elimination list from a greedy elimination
  property whose outside parents are co-supplied.
* `bdirPiece`: relative 2-dicolourings (Lemma B_dir of the paper):
  `H = A ⊔ B` with `D[A]` and `D[B]` acyclic, at most one designated outside parent per vertex,
  and the children of each outside vertex inside one part.
* `outPar`: the designated outside parent; `TTFree`: no transitive triangle.
-/

namespace HalfRate

open Finset MotionDepthCodes

variable {V : Type*} [DecidableEq V]

/-- No transitive triangle: distinct `x → y → z` with `x → z` never occur (`x → y` means
`x ∈ N y`). -/
def TTFree (N : V → Finset V) : Prop :=
  ∀ x y z, x ≠ y → y ≠ z → x ≠ z → x ∈ N y → y ∈ N z → x ∈ N z → False

theorem three_le_card {s : Finset V} {a b c : V} (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : 3 ≤ s.card := by
  have hsub : ({a, b, c} : Finset V) ⊆ s := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have h3 : ({a, b, c} : Finset V).card = 3 := by
    rw [card_insert_of_notMem (by simp [hab, hac]), card_pair hbc]
  exact h3 ▸ card_le_card hsub

theorem four_le_card {s : Finset V} {a b c d : V} (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s)
    (hd : d ∈ s) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d) : 4 ≤ s.card := by
  have hsub : ({a, b, c, d} : Finset V) ⊆ s := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have h4 : ({a, b, c, d} : Finset V).card = 4 := by
    rw [card_insert_of_notMem (by simp [hab, hac, had]),
      card_insert_of_notMem (by simp [hbc, hbd]), card_pair hcd]
  exact h4 ▸ card_le_card hsub

/-- The designated outside parent of `v`: an element of `M v` in `R \ C`, if any. -/
noncomputable def outPar (M : V → Finset V) (R C : Finset V) (v : V) : Option V :=
  if h : ((M v).filter (fun w => w ∈ R ∧ w ∉ C)).Nonempty then some h.choose else none

theorem outPar_none {M : V → Finset V} {R C : Finset V} {v : V} (h : outPar M R C v = none)
    {w : V} (hw : w ∈ M v) (hwR : w ∈ R) : w ∈ C := by
  by_contra hwC
  unfold outPar at h
  split_ifs at h with hne
  exact hne ⟨w, by simp [hw, hwR, hwC]⟩

theorem outPar_some {M : V → Finset V} {R C : Finset V} {v w : V}
    (h : outPar M R C v = some w) : w ∈ M v ∧ w ∈ R ∧ w ∉ C := by
  unfold outPar at h
  split_ifs at h with hne
  have hc := hne.choose_spec
  rw [Option.some_inj] at h
  subst h
  simpa using hc

section Mono

variable {ι : Type*}

theorem RelCharged.mono {N N' : V → Finset V} (U : Finset V)
    (P : ι → Finset V) (b : V → ι) (par : V → Option V) (W : Finset V) :
    ∀ (l : List V) (S : Finset V) (L : V → Finset V), (∀ v ∈ l, N v ⊆ N' v) →
      RelCharged N' U P b par W S L l → RelCharged N U P b par W S L l := by
  intro l
  induction l with
  | nil => intro _ _ _ _; trivial
  | cons v l ih =>
    intro S L hN h
    have hv : N v ⊆ N' v := hN v (List.mem_cons_self ..)
    have hl : ∀ x ∈ l, N x ⊆ N' x := fun x hx => hN x (List.mem_cons_of_mem _ hx)
    cases hp : par v with
    | none =>
      simp only [RelCharged, hp] at h ⊢
      exact ⟨hv.trans h.1, ih _ _ hl h.2⟩
    | some w =>
      simp only [RelCharged, hp] at h ⊢
      exact ⟨h.1, hv.trans h.2.1, h.2.2.1, ih _ _ hl h.2.2.2⟩

/-- Piece certificates transfer to relations with fewer arcs at the vertices of the piece. -/
def PieceCert.mono [Fintype V] {N N' : V → Finset V} {U H : Finset V} (c : PieceCert N' U H)
    (hN : ∀ v ∈ H, N v ⊆ N' v) : PieceCert N U H :=
  have hl : ∀ v ∈ c.l, N v ⊆ N' v := fun v hv => hN v (c.hl ▸ List.mem_toFinset.mpr hv)
  { c with charged := RelCharged.mono U c.P c.b c.par _ c.l ∅ _ hl c.charged }

end Mono

section Builder

variable {ι : Type*}

/-- An elimination list from a greedy elimination property, with co-supplied outside parents
(all steps charged to one outside vertex use the same supplying record). -/
theorem exists_relCharged (N : V → Finset V) (U H W : Finset V) (P : ι → Finset V)
    (b : V → ι) (par : V → Option V)
    (hco : ∀ v ∈ H, ∀ v' ∈ H, ∀ w, par v = some w → par v' = some w → b v = b v')
    (helim : ∀ S ⊆ H, S ≠ H → ∃ v ∈ H, v ∉ S ∧
        (par v = none → N v ⊆ U ∪ (S ∪ P (b v))) ∧
        (∀ w, par v = some w → w ∈ W ∧ N v ⊆ U ∪ insert w (S ∪ P (b v)))) :
    ∀ (n : ℕ) (S : Finset V), S ⊆ H → (H \ S).card = n → ∀ L : V → Finset V,
      (∀ w, ∀ v ∈ H, par v = some w → L w ⊆ S ∪ P (b v)) →
      ∃ l : List V, S ∪ l.toFinset = H ∧ (∀ v ∈ l, v ∈ H) ∧
        RelCharged N U P b par W S L l := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro S hSH hn L hL
    by_cases hS : S = H
    · exact ⟨[], by simp [hS], by simp, trivial⟩
    obtain ⟨v, hvH, hvS, hnone, hsome⟩ := helim S hSH hS
    have hlt : (H \ insert v S).card < n := by
      rw [← hn]; apply card_lt_card
      refine ⟨sdiff_subset_sdiff (subset_refl _) (subset_insert v S), ?_⟩
      intro hsub
      have : v ∈ H \ S := mem_sdiff.mpr ⟨hvH, hvS⟩
      have := hsub this; simp at this
    have hSH' : insert v S ⊆ H := insert_subset hvH hSH
    have hcons : ∀ l : List V, insert v S ∪ l.toFinset = H → S ∪ (v :: l).toFinset = H := by
      intro l hl; rw [← hl]; ext x
      simp only [mem_union, mem_insert, List.mem_toFinset, List.mem_cons]; tauto
    have hmem : ∀ l : List V, (∀ x ∈ l, x ∈ H) → ∀ x ∈ v :: l, x ∈ H := by
      intro l hl x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hvH
      · exact hl x hx
    cases hp : par v with
    | none =>
      obtain ⟨l, hl1, hl2, hl3⟩ := ih _ hlt (insert v S) hSH' rfl L
        (fun w v' hv' hpw => (hL w v' hv' hpw).trans
          (union_subset_union (subset_insert _ _) (subset_refl _)))
      refine ⟨v :: l, hcons l hl1, hmem l hl2, ?_⟩
      simp only [RelCharged, hp]
      exact ⟨hnone hp, hl3⟩
    | some w =>
      obtain ⟨hwW, hN⟩ := hsome w hp
      have hL' : ∀ w', ∀ v' ∈ H, par v' = some w' →
          Function.update L w (insert v (S ∪ P (b v))) w' ⊆ insert v S ∪ P (b v') := by
        intro w' v' hv' hpw'
        by_cases hww : w' = w
        · subst hww
          rw [Function.update_self, hco v' hv' v hvH w' hpw' hp]
          intro x hx
          simp only [mem_insert, mem_union] at hx ⊢
          tauto
        · rw [Function.update_of_ne hww]
          exact (hL w' v' hv' hpw').trans
            (union_subset_union (subset_insert _ _) (subset_refl _))
      obtain ⟨l, hl1, hl2, hl3⟩ := ih _ hlt (insert v S) hSH' rfl _ hL'
      refine ⟨v :: l, hcons l hl1, hmem l hl2, ?_⟩
      simp only [RelCharged, hp]
      exact ⟨hwW, hN, hL w v hvH hp, hl3⟩

/-- A piece certificate from a greedy elimination property with co-supplied outside
parents. -/
theorem pieceCert_of_elim [Fintype V] (N : V → Finset V) (U H : Finset V) {m : ℕ}
    (P : Fin m → Finset V) (disj : ∀ i j, i ≠ j → Disjoint (P i) (P j))
    (cover : (univ : Finset (Fin m)).biUnion P = H) (a b : V → Fin m) (par : V → Option V)
    (own : ∀ v ∈ H, v ∈ P (a v)) (ab : ∀ v ∈ H, a v ≠ b v)
    (hco : ∀ v ∈ H, ∀ v' ∈ H, ∀ w, par v = some w → par v' = some w → b v = b v')
    (helim : ∀ S ⊆ H, S ≠ H → ∃ v ∈ H, v ∉ S ∧
        (par v = none → N v ⊆ U ∪ (S ∪ P (b v))) ∧
        (∀ w, par v = some w → w ∈ univ \ (U ∪ H) ∧ N v ⊆ U ∪ insert w (S ∪ P (b v)))) :
    Nonempty (PieceCert N U H) := by
  obtain ⟨l, hl1, hl2, hl3⟩ := exists_relCharged N U H (univ \ (U ∪ H)) P b par hco helim _ ∅
    (empty_subset _) rfl (fun _ => ∅) (fun _ _ _ _ => empty_subset _)
  exact ⟨{
    m := m
    P := P
    disj := disj
    cover := cover
    l := l
    hl := by simpa using hl1
    a := a
    b := b
    par := par
    own := fun v hv => own v (hl2 v hv)
    ab := fun v hv => ab v (hl2 v hv)
    charged := hl3 }⟩

end Builder

section TwoParts

variable [Fintype V]

omit [DecidableEq V] [Fintype V] in
theorem IsAcyclicIn.mono {N : V → Finset V} {A A' : Finset V} (h : IsAcyclicIn N A)
    (hA : A' ⊆ A) : IsAcyclicIn N A' := fun T hT hne => h T (hT.trans hA) hne

omit [DecidableEq V] [Fintype V] in
theorem isAcyclicIn_empty (N : V → Finset V) : IsAcyclicIn N ∅ := fun T hT hne => by
  obtain ⟨x, hx⟩ := hne
  exact absurd (hT hx) (by simp)

omit [DecidableEq V] [Fintype V] in
theorem isAcyclicIn_singleton {N : V → Finset V} {v : V} (hv : v ∉ N v) :
    IsAcyclicIn N {v} := by
  intro T hT hne
  obtain ⟨x, hx⟩ := hne
  have hxv : x = v := mem_singleton.mp (hT hx)
  subst hxv
  refine ⟨x, hx, fun u hu huT => ?_⟩
  have := mem_singleton.mp (hT huT)
  subst this
  exact hv hu

/-- **Relative 2-dicolourings** (Lemma B_dir): `H = A ⊔ B` with both parts acyclic, every
parent of a vertex of `H` outside `U ∪ H` its designated outside parent, and the children of
each outside vertex inside one part. -/
theorem bdirPiece (N : V → Finset V) (U H A B : Finset V) (hAB : Disjoint A B)
    (hcov : A ∪ B = H) (hA : IsAcyclicIn N A) (hB : IsAcyclicIn N B) (par : V → Option V)
    (hpar : ∀ v ∈ H, ∀ u ∈ N v, u ∈ U ∨ u ∈ H ∨ par v = some u)
    (hparW : ∀ v ∈ H, ∀ w, par v = some w → w ∉ U ∧ w ∉ H)
    (hco : ∀ v ∈ H, ∀ v' ∈ H, ∀ w, par v = some w → par v' = some w → (v ∈ A ↔ v' ∈ A)) :
    Nonempty (PieceCert N U H) := by
  have hmemB : ∀ x ∈ H, x ∉ A → x ∈ B := fun x hx hxA => by
    rw [← hcov] at hx; exact (mem_union.mp hx).resolve_left hxA
  -- a vertex whose parents in `H` are revealed or in the other part can be eliminated
  have good : ∀ (S : Finset V) (v : V), v ∈ H →
      (∀ u ∈ N v, u ∈ H → u ∈ S ∪ ![A, B] (if v ∈ A then 1 else 0)) →
      (par v = none → N v ⊆ U ∪ (S ∪ ![A, B] (if v ∈ A then 1 else 0))) ∧
      (∀ w, par v = some w → w ∈ univ \ (U ∪ H) ∧
        N v ⊆ U ∪ insert w (S ∪ ![A, B] (if v ∈ A then 1 else 0))) := by
    intro S v hv hgood
    refine ⟨fun hp u hu => ?_, fun w hp => ⟨?_, fun u hu => ?_⟩⟩
    · rcases hpar v hv u hu with h | h | h
      · exact mem_union_left _ h
      · exact mem_union_right _ (hgood u hu h)
      · rw [hp] at h; exact absurd h (by simp)
    · obtain ⟨h1, h2⟩ := hparW v hv w hp
      simp [h1, h2]
    · rcases hpar v hv u hu with h | h | h
      · exact mem_union_left _ h
      · exact mem_union_right _ (mem_insert_of_mem (hgood u hu h))
      · rw [hp] at h
        cases h
        exact mem_union_right _ (mem_insert_self _ _)
  refine pieceCert_of_elim N U H (m := 2) ![A, B] ?_ ?_ (fun v => if v ∈ A then 0 else 1)
    (fun v => if v ∈ A then 1 else 0) par ?_ ?_ ?_ ?_
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [disjoint_comm]
  · ext x
    simp only [mem_biUnion, mem_univ, true_and, Fin.exists_fin_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, ← hcov, mem_union]
  · intro v hv
    by_cases hvA : v ∈ A
    · simp [hvA]
    · simp [hvA, hmemB v hv hvA]
  · intro v _
    by_cases hvA : v ∈ A <;> simp [hvA]
  · intro v hv v' hv' w h1 h2
    have := hco v hv v' hv' w h1 h2
    by_cases hvA : v ∈ A
    · simp [hvA, this.mp hvA]
    · simp [hvA, mt this.mpr hvA]
  · intro S hSH hS
    by_cases hAS : (A \ S).Nonempty
    · obtain ⟨v, hvT, hsrc⟩ := hA (A \ S) sdiff_subset hAS
      have hvA := (mem_sdiff.mp hvT).1
      have hvH : v ∈ H := hcov ▸ mem_union_left _ hvA
      refine ⟨v, hvH, (mem_sdiff.mp hvT).2, good S v hvH fun u hu huH => ?_⟩
      simp only [hvA, ↓reduceIte]
      by_cases huA : u ∈ A
      · have : u ∉ A \ S := hsrc u hu
        simp only [mem_sdiff, not_and, not_not] at this
        exact mem_union_left _ (this huA)
      · exact mem_union_right _ (by simpa using hmemB u huH huA)
    · have hAsub : A ⊆ S := by
        intro x hx; by_contra hxS; exact hAS ⟨x, mem_sdiff.mpr ⟨hx, hxS⟩⟩
      obtain ⟨x, hxH, hxS⟩ : ∃ x ∈ H, x ∉ S := by
        by_contra hcon
        exact hS (subset_antisymm hSH fun x hx => by_contra fun hxS => hcon ⟨x, hx, hxS⟩)
      have hBS : (B \ S).Nonempty :=
        ⟨x, mem_sdiff.mpr ⟨hmemB x hxH (fun hxA => hxS (hAsub hxA)), hxS⟩⟩
      obtain ⟨v, hvT, hsrc⟩ := hB (B \ S) sdiff_subset hBS
      have hvB := (mem_sdiff.mp hvT).1
      have hvH : v ∈ H := hcov ▸ mem_union_right _ hvB
      refine ⟨v, hvH, (mem_sdiff.mp hvT).2, good S v hvH fun u hu huH => mem_union_left _ ?_⟩
      by_cases huA : u ∈ A
      · exact hAsub huA
      · have : u ∉ B \ S := hsrc u hu
        simp only [mem_sdiff, not_and, not_not] at this
        exact this (hmemB u huH huA)

end TwoParts

end HalfRate
