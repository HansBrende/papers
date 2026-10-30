import Mathlib

/-!
# Lemma PG: separated centred sets in a projective plane are small

A *centred set* in a finite projective plane is a set `S` of points with a line `ℓ s` through every
`s ∈ S`; the *helpers* of `s` are the other points of `ℓ s`. Its incidence graph `E(S)` lives on two
copies of the points, `L_p = inl p` and `R_p = inr p`, with an edge `L_h R_s` whenever `h` is a
helper of `s ∈ S`. The set is *separated* if `L_s` and `R_s` lie in different components for every
`s ∈ S`, and *bipartite-compatible* if a two-colouring of the points separates every point of `S`
from its helpers.

* `Centred.separated_of_bipCompat`: bipartite-compatible sets are separated.
* `Centred.card_le`: a separated centred set in a projective plane of order `q` has at most `4q`
  points, or else `(|S| - 1)² ≤ q³`.

The one-component case is a Cauchy–Schwarz count over the points off `S`: the `t` lines meet `S`
only in their own points, and any two of them meet off `S`. The several-component case bounds each
component by `2q` and counts the pairs in different components.
-/

namespace MergeDepth

open Finset Configuration Configuration.ProjectivePlane

/-- A centred set: points `S` and a line `ℓ s` through each of them. -/
structure Centred (P L : Type*) [Membership P L] where
  S : Finset P
  ℓ : P → L
  mem : ∀ s ∈ S, s ∈ ℓ s

namespace Centred

variable {P L : Type*} [Membership P L] (C : Centred P L)

/-- `h` is a helper of `s`: another point of the line `ℓ s`. -/
def Helper (s h : P) : Prop := h ∈ C.ℓ s ∧ h ≠ s

/-- The incidence graph `E(S)`: `inl h` is adjacent to `inr s` when `s ∈ S` and `h` helps `s`. -/
def graph : SimpleGraph (P ⊕ P) :=
  SimpleGraph.fromRel fun x y => ∃ h s, x = Sum.inl h ∧ y = Sum.inr s ∧ s ∈ C.S ∧ C.Helper s h

/-- Separated: `L_s` and `R_s` lie in different components for every `s ∈ S`. -/
def Separated : Prop := ∀ s ∈ C.S, ¬ C.graph.Reachable (Sum.inl s) (Sum.inr s)

/-- Bipartite-compatible: a two-colouring separates every point of `S` from its helpers. -/
def BipCompat : Prop := ∃ χ : P → Bool, ∀ s ∈ C.S, ∀ h, C.Helper s h → χ h ≠ χ s

theorem adj {s h : P} (hs : s ∈ C.S) (hh : C.Helper s h) : C.graph.Adj (Sum.inl h) (Sum.inr s) := by
  simp only [graph, SimpleGraph.fromRel_adj]
  exact ⟨by simp, Or.inl ⟨h, s, rfl, rfl, hs, hh⟩⟩

theorem reach {s h : P} (hs : s ∈ C.S) (hh : C.Helper s h) :
    C.graph.Reachable (Sum.inl h) (Sum.inr s) :=
  (C.adj hs hh).reachable

/-- Two points of `S` with a common helper have connected `R`-vertices. -/
theorem reach_common {s s' h : P} (hs : s ∈ C.S) (hs' : s' ∈ C.S) (hh : C.Helper s h)
    (hh' : C.Helper s' h) : C.graph.Reachable (Sum.inr s) (Sum.inr s') :=
  (C.reach hs hh).symm.trans (C.reach hs' hh')

/-- **Bipartite-compatible sets are separated.** -/
theorem separated_of_bipCompat (hC : C.BipCompat) : C.Separated := by
  obtain ⟨χ, hχ⟩ := hC
  let col : P ⊕ P → Bool := fun x => Sum.elim χ (fun p => !χ p) x
  have hadj : ∀ x y, C.graph.Adj x y → col x = col y := by
    intro x y hxy
    simp only [graph, SimpleGraph.fromRel_adj] at hxy
    obtain ⟨-, ⟨h, s, rfl, rfl, hs, hh⟩ | ⟨h, s, rfl, rfl, hs, hh⟩⟩ := hxy
    · have := hχ s hs h hh
      simp only [col, Sum.elim_inl, Sum.elim_inr]
      cases hχh : χ h <;> cases hχs : χ s <;> simp_all
    · have := hχ s hs h hh
      simp only [col, Sum.elim_inl, Sum.elim_inr]
      cases hχh : χ h <;> cases hχs : χ s <;> simp_all
  have hreach : ∀ x y, C.graph.Reachable x y → col x = col y := by
    intro x y ⟨w⟩
    induction w with
    | nil => rfl
    | cons h _ ih => exact (hadj _ _ h).trans ih
  intro s _ hr
  have := hreach _ _ hr
  simp only [col, Sum.elim_inl, Sum.elim_inr] at this
  cases hχs : χ s <;> simp_all

/-- **Step 3.** Points with connected `R`-vertices do not lie on each other's lines. -/
theorem not_mem_line (hC : C.Separated) {s s' : P} (hs : s ∈ C.S) (hs' : s' ∈ C.S) (hne : s ≠ s')
    (hr : C.graph.Reachable (Sum.inr s) (Sum.inr s')) : s ∉ C.ℓ s' := fun hmem =>
  hC s hs ((C.reach hs' ⟨hmem, hne⟩).trans hr.symm)

variable [ProjectivePlane P L] [Fintype P] [Fintype L]

attribute [local instance] Classical.propDecidable

/-- **Step 1.** In a separated centred set, distinct points have distinct lines. -/
theorem line_ne (hC : C.Separated) {s s' : P} (hs : s ∈ C.S) (hs' : s' ∈ C.S) (hne : s ≠ s') :
    C.ℓ s ≠ C.ℓ s' := by
  classical
  intro heq
  -- a third point `h` on the common line
  have h3 := two_lt_pointCount P (C.ℓ s)
  have hcard : 2 < ((univ : Finset P).filter fun p => p ∈ C.ℓ s).card := by
    rw [pointCount, Nat.card_eq_fintype_card, Fintype.card_subtype] at h3
    exact h3
  obtain ⟨h, hh, hhs, hhs'⟩ : ∃ h ∈ (univ : Finset P).filter (· ∈ C.ℓ s), h ≠ s ∧ h ≠ s' := by
    by_contra hno
    push Not at hno
    have : (univ : Finset P).filter (· ∈ C.ℓ s) ⊆ {s, s'} := fun p hp => by
      by_cases h1 : p = s
      · simp [h1]
      · simp [hno p hp h1]
    have := (card_le_card this).trans (card_insert_le _ _)
    simp at this
    omega
  have hhl : h ∈ C.ℓ s := (mem_filter.mp hh).2
  have hs'h : C.Helper s s' := ⟨heq ▸ C.mem s' hs', hne.symm⟩
  have hhh : C.Helper s h := ⟨hhl, hhs⟩
  have hhh' : C.Helper s' h := ⟨heq ▸ hhl, hhs'⟩
  exact hC s' hs' ((C.reach hs hs'h).trans (C.reach_common hs hs' hhh hhh'))

/-- **Step 2.** Points with disconnected `R`-vertices: one lies on the other's line. -/
theorem mem_line_of_not_reach (hC : C.Separated) {s s' : P} (hs : s ∈ C.S) (hs' : s' ∈ C.S)
    (hne : s ≠ s') (hr : ¬ C.graph.Reachable (Sum.inr s) (Sum.inr s')) :
    s ∈ C.ℓ s' ∨ s' ∈ C.ℓ s := by
  have hl := C.line_ne hC hs hs' hne
  obtain ⟨hz, hz'⟩ := HasPoints.mkPoint_ax (P := P) hl
  set z := HasPoints.mkPoint (P := P) hl
  by_cases h1 : z = s
  · exact Or.inl (h1 ▸ hz')
  by_cases h2 : z = s'
  · exact Or.inr (h2 ▸ hz)
  exact absurd (C.reach_common hs hs' ⟨hz, h1⟩ ⟨hz', h2⟩) hr

theorem card_line (l : L) :
    ((univ : Finset P).filter (· ∈ l)).card = order P L + 1 := by
  have := pointCount_eq P l
  rw [pointCount, Nat.card_eq_fintype_card, Fintype.card_subtype] at this
  convert this

theorem card_pencil (p : P) :
    ((univ : Finset L).filter fun l => p ∈ l).card = order P L + 1 := by
  have := lineCount_eq L p
  rw [lineCount, Nat.card_eq_fintype_card, Fintype.card_subtype] at this
  convert this

/-- At most `q` points other than `y ∈ S` lie on the line `ℓ y`. -/
theorem card_on_line_le {y : P} (hy : y ∈ C.S) (T : Finset P) :
    (T.filter fun x => x ≠ y ∧ x ∈ C.ℓ y).card ≤ order P L := by
  classical
  have hsub : (T.filter fun x => x ≠ y ∧ x ∈ C.ℓ y) ⊆
      ((univ : Finset P).filter (· ∈ C.ℓ y)).erase y := fun x hx => by
    obtain ⟨-, hxy, hxl⟩ := mem_filter.mp hx
    exact mem_erase.mpr ⟨hxy, mem_filter.mpr ⟨mem_univ _, hxl⟩⟩
  refine (card_le_card hsub).trans ?_
  rw [card_erase_of_mem (mem_filter.mpr ⟨mem_univ _, C.mem y hy⟩), card_line]
  omega

/-- At most `q` lines other than `ℓ y` pass through `y ∈ S`. -/
theorem card_pencil_erase_le {y : P} (hy : y ∈ C.S) :
    (((univ : Finset L).filter fun l => y ∈ l).erase (C.ℓ y)).card = order P L := by
  classical
  rw [card_erase_of_mem (s := (univ : Finset L).filter fun l => y ∈ l)
    (mem_filter.mpr ⟨mem_univ _, C.mem y hy⟩), card_pencil]
  omega

/-- The points of `S` whose `R`-vertices are connected to that of `x`. -/
noncomputable def cls (x : P) : Finset P := C.S.filter fun y => C.graph.Reachable (Sum.inr x) (Sum.inr y)

/-- **Step 5, first half.** If some point of `S` is not connected to `x`, the class of `x` has at
most `2q` points. -/
theorem card_cls_le (hC : C.Separated) {x s' : P} (hs' : s' ∈ C.S)
    (hxs' : ¬ C.graph.Reachable (Sum.inr x) (Sum.inr s')) : (C.cls x).card ≤ 2 * order P L := by
  -- every `y` in the class of `x` lies on `ℓ s'`, or `s'` lies on `ℓ y`
  have hsplit : ∀ y ∈ C.cls x, (y ≠ s' ∧ y ∈ C.ℓ s') ∨ s' ∈ C.ℓ y := by
    intro y hy
    obtain ⟨hyS, hxy⟩ := mem_filter.mp hy
    have hne : y ≠ s' := fun h => hxs' (h ▸ hxy)
    have hnr : ¬ C.graph.Reachable (Sum.inr y) (Sum.inr s') := fun h => hxs' (hxy.trans h)
    rcases C.mem_line_of_not_reach hC hyS hs' hne hnr with h | h
    · exact Or.inl ⟨hne, h⟩
    · exact Or.inr h
  set A := (C.cls x).filter fun y => y ≠ s' ∧ y ∈ C.ℓ s'
  set B := (C.cls x).filter fun y => s' ∈ C.ℓ y
  have hAB : C.cls x ⊆ A ∪ B := fun y hy => by
    rcases hsplit y hy with h | h
    · exact mem_union_left _ (mem_filter.mpr ⟨hy, h⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hy, h⟩)
  have hA : A.card ≤ order P L := C.card_on_line_le hs' (C.cls x)
  -- the lines of the points of `B` are distinct lines through `s'` other than `ℓ s'`
  have hB : B.card ≤ order P L := by
    have hinj : Set.InjOn C.ℓ B := fun y hy y' hy' heq => by
      by_contra hne
      exact C.line_ne hC (mem_filter.mp (mem_filter.mp hy).1).1
        (mem_filter.mp (mem_filter.mp hy').1).1 hne heq
    rw [← card_image_of_injOn hinj, ← C.card_pencil_erase_le hs']
    refine card_le_card fun l hl => ?_
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hl
    obtain ⟨hyc, hs'y⟩ := mem_filter.mp hy
    have hyS := (mem_filter.mp hyc).1
    refine mem_erase.mpr ⟨fun heq => ?_, mem_filter.mpr ⟨mem_univ _, hs'y⟩⟩
    have hne : y ≠ s' := fun h => hxs' (h ▸ (mem_filter.mp hyc).2)
    exact C.line_ne hC hyS hs' hne heq
  calc (C.cls x).card ≤ (A ∪ B).card := card_le_card hAB
    _ ≤ A.card + B.card := card_union_le _ _
    _ ≤ 2 * order P L := by omega

/-- **Step 5.** A separated centred set with two disconnected `R`-vertices has at most `4q` points. -/
theorem card_le_of_two (hC : C.Separated) {s₀ s₁ : P} (hs₀ : s₀ ∈ C.S) (hs₁ : s₁ ∈ C.S)
    (h01 : ¬ C.graph.Reachable (Sum.inr s₀) (Sum.inr s₁)) : C.S.card ≤ 4 * order P L := by
  set q := order P L
  set t := C.S.card
  -- every class has at most `2q` points
  have hcls : ∀ x ∈ C.S, (C.cls x).card ≤ 2 * q := by
    intro x _
    by_cases hx0 : C.graph.Reachable (Sum.inr x) (Sum.inr s₀)
    · exact C.card_cls_le hC hs₁ fun hx1 => h01 (hx0.symm.trans hx1)
    · exact C.card_cls_le hC hs₀ hx0
  -- the ordered pairs in different classes
  set X := (C.S ×ˢ C.S).filter fun p => ¬ C.graph.Reachable (Sum.inr p.1) (Sum.inr p.2)
  have hXlow : t * t ≤ X.card + t * (2 * q) := by
    have hX : X.card = ∑ x ∈ C.S, (C.S.filter fun y =>
        ¬ C.graph.Reachable (Sum.inr x) (Sum.inr y)).card := by
      rw [card_filter, sum_product]
      refine sum_congr rfl fun x _ => ?_
      rw [card_filter]
    have hterm : ∀ x ∈ C.S, t ≤ (C.S.filter fun y =>
        ¬ C.graph.Reachable (Sum.inr x) (Sum.inr y)).card + 2 * q := by
      intro x hx
      have h1 := card_filter_add_card_filter_not
        (s := C.S) (fun y => C.graph.Reachable (Sum.inr x) (Sum.inr y))
      have h2 : (C.S.filter fun y => C.graph.Reachable (Sum.inr x) (Sum.inr y)).card ≤ 2 * q :=
        hcls x hx
      omega
    calc t * t = ∑ _x ∈ C.S, t := by rw [sum_const, smul_eq_mul]
      _ ≤ ∑ x ∈ C.S, ((C.S.filter fun y =>
          ¬ C.graph.Reachable (Sum.inr x) (Sum.inr y)).card + 2 * q) := sum_le_sum hterm
      _ = X.card + t * (2 * q) := by rw [sum_add_distrib, hX, sum_const, smul_eq_mul]
  -- every pair in different classes has one point on the other's line
  set X₁ := (C.S ×ˢ C.S).filter fun p => p.1 ≠ p.2 ∧ p.1 ∈ C.ℓ p.2
  set X₂ := (C.S ×ˢ C.S).filter fun p => p.2 ≠ p.1 ∧ p.2 ∈ C.ℓ p.1
  have hXsub : X ⊆ X₁ ∪ X₂ := by
    intro p hp
    obtain ⟨hpS, hnr⟩ := mem_filter.mp hp
    obtain ⟨h1, h2⟩ := mem_product.mp hpS
    have hne : p.1 ≠ p.2 := fun h => hnr (h ▸ SimpleGraph.Reachable.refl _)
    rcases C.mem_line_of_not_reach hC h1 h2 hne hnr with h | h
    · exact mem_union_left _ (mem_filter.mpr ⟨hpS, hne, h⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hpS, fun e => hne e.symm, h⟩)
  have hX₁ : X₁.card ≤ t * q := by
    have : X₁.card = ∑ y ∈ C.S, (C.S.filter fun x => x ≠ y ∧ x ∈ C.ℓ y).card := by
      rw [card_filter, sum_product_right]
      refine sum_congr rfl fun y _ => ?_
      rw [card_filter]
    rw [this]
    calc ∑ y ∈ C.S, (C.S.filter fun x => x ≠ y ∧ x ∈ C.ℓ y).card ≤ ∑ _y ∈ C.S, q :=
          sum_le_sum fun y hy => C.card_on_line_le hy C.S
      _ = t * q := by rw [sum_const, smul_eq_mul]
  have hX₂ : X₂.card ≤ t * q := by
    have : X₂.card = ∑ x ∈ C.S, (C.S.filter fun y => y ≠ x ∧ y ∈ C.ℓ x).card := by
      rw [card_filter, sum_product]
      refine sum_congr rfl fun x _ => ?_
      rw [card_filter]
    rw [this]
    calc ∑ x ∈ C.S, (C.S.filter fun y => y ≠ x ∧ y ∈ C.ℓ x).card ≤ ∑ _x ∈ C.S, q :=
          sum_le_sum fun x hx => C.card_on_line_le hx C.S
      _ = t * q := by rw [sum_const, smul_eq_mul]
  have hXup : X.card ≤ t * q + t * q :=
    (card_le_card hXsub).trans ((card_union_le _ _).trans (Nat.add_le_add hX₁ hX₂))
  have ht : 0 < t := card_pos.mpr ⟨s₀, hs₀⟩
  have : t * t ≤ t * (4 * q) := by nlinarith
  exact Nat.le_of_mul_le_mul_left this ht

/-- **Step 4.** A separated centred set whose `R`-vertices are all connected has
`(|S| - 1)² ≤ q³`: its lines meet `S` only in their own points and pairwise off `S`, and a
Cauchy–Schwarz count over the points off `S` gives the bound. -/
theorem card_le_of_one (hC : C.Separated)
    (hone : ∀ s ∈ C.S, ∀ s' ∈ C.S, C.graph.Reachable (Sum.inr s) (Sum.inr s')) :
    (C.S.card - 1) ^ 2 ≤ order P L ^ 3 := by
  set q := order P L
  set t := C.S.card
  -- a line `ℓ s` meets `S` only in `s`
  have hown : ∀ s ∈ C.S, ∀ s' ∈ C.S, s' ∈ C.ℓ s → s' = s := by
    intro s hs s' hs' hmem
    by_contra hne
    exact C.not_mem_line hC hs' hs hne (hone s' hs' s hs) hmem
  set Pc := (univ : Finset P) \ C.S
  have hPc : Pc.card = q ^ 2 + q + 1 - t := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ, card_points P L]
  have htv : t ≤ q ^ 2 + q + 1 := by
    rw [← card_points P L, ← card_univ]
    exact card_le_card (subset_univ _)
  -- `d p`: the number of lines `ℓ s` through `p`
  let d : P → ℕ := fun p => (C.S.filter fun s => p ∈ C.ℓ s).card
  -- first moment: every line has `q` points off `S`
  have hsum1 : ∑ p ∈ Pc, d p = t * q := by
    have : ∑ p ∈ Pc, d p = ∑ s ∈ C.S, (Pc.filter fun p => p ∈ C.ℓ s).card := by
      simp only [d, card_filter]
      exact sum_comm
    rw [this]
    have hline : ∀ s ∈ C.S, (Pc.filter fun p => p ∈ C.ℓ s).card = q := by
      intro s hs
      have hsplit : (univ : Finset P).filter (· ∈ C.ℓ s) =
          insert s (Pc.filter fun p => p ∈ C.ℓ s) := by
        ext p
        simp only [mem_filter, mem_univ, true_and, mem_insert, Pc, mem_sdiff]
        constructor
        · intro hp
          by_cases hpS : p ∈ C.S
          · exact Or.inl (hown s hs p hpS hp)
          · exact Or.inr ⟨hpS, hp⟩
        · rintro (rfl | ⟨-, hp⟩)
          · exact C.mem p hs
          · exact hp
      have hnot : s ∉ Pc.filter fun p => p ∈ C.ℓ s := fun h =>
        (mem_sdiff.mp (mem_filter.mp h).1).2 hs
      have := card_line (P := P) (C.ℓ s)
      rw [hsplit, card_insert_of_notMem hnot] at this
      omega
    rw [sum_congr rfl hline, sum_const, smul_eq_mul]
  -- second moment: two distinct lines meet in exactly one point, off `S`
  have hsum2 : ∑ p ∈ Pc, d p ^ 2 = t * q + (t * t - t) := by
    have hsq : ∀ p, d p ^ 2 = d p + ((C.S.filter fun s => p ∈ C.ℓ s).offDiag).card := by
      intro p
      rw [offDiag_card, sq]
      have : d p ≤ d p * d p := Nat.le_mul_self _
      simp only [d] at this ⊢
      omega
    rw [sum_congr rfl fun p _ => hsq p, sum_add_distrib, hsum1]
    congr 1
    -- count the triples `(p, s, s')` with `s ≠ s'` and `p ∈ ℓ s ∩ ℓ s'` both ways
    have hpair : ∀ x ∈ C.S.offDiag,
        (Pc.filter fun p => p ∈ C.ℓ x.1 ∧ p ∈ C.ℓ x.2).card = 1 := by
      intro x hx
      obtain ⟨hx1, hx2, hne⟩ := mem_offDiag.mp hx
      have hl := C.line_ne hC hx1 hx2 hne
      obtain ⟨z, ⟨hz1, hz2⟩, hzu⟩ := HasPoints.existsUnique_point P L (C.ℓ x.1) (C.ℓ x.2) hl
      rw [card_eq_one]
      refine ⟨z, ?_⟩
      ext p
      simp only [mem_filter, mem_singleton, Pc, mem_sdiff, mem_univ, true_and]
      constructor
      · rintro ⟨-, hp⟩
        exact hzu p hp
      · rintro rfl
        refine ⟨fun hpS => hne ?_, hz1, hz2⟩
        exact (hown x.1 hx1 p hpS hz1).symm.trans (hown x.2 hx2 p hpS hz2)
    have hcount : ∑ p ∈ Pc, ((C.S.filter fun s => p ∈ C.ℓ s).offDiag).card =
        ∑ x ∈ C.S.offDiag, (Pc.filter fun p => p ∈ C.ℓ x.1 ∧ p ∈ C.ℓ x.2).card := by
      have : ∀ p, ((C.S.filter fun s => p ∈ C.ℓ s).offDiag).card =
          (C.S.offDiag.filter fun x => p ∈ C.ℓ x.1 ∧ p ∈ C.ℓ x.2).card := by
        intro p
        congr 1
        ext x
        simp only [mem_offDiag, mem_filter]
        tauto
      simp only [this, card_filter]
      exact sum_comm
    rw [hcount, sum_congr rfl hpair, sum_const, smul_eq_mul, mul_one, offDiag_card]
  -- Cauchy–Schwarz
  have hcs := sq_sum_le_card_mul_sum_sq (s := Pc) (f := d)
  rw [hsum1, hsum2, hPc] at hcs
  -- algebra: `(t q)² ≤ (v - t)(t q + t² - t)` gives `(t - 1)² ≤ q³`
  rcases Nat.eq_zero_or_pos t with h0 | hpos
  · rw [h0]; simp
  have ht1 : 1 ≤ t := hpos
  have key : t * (q ^ 3) + t * (2 * t) ≥ t * (t * t + 1) := by
    -- cast to `ℤ` and expand
    have hz : ((t : ℤ) * q) ^ 2 ≤ ((q : ℤ) ^ 2 + q + 1 - t) * (t * q + (t * t - t)) := by
      have h1 : ((q ^ 2 + q + 1 - t : ℕ) : ℤ) = (q : ℤ) ^ 2 + q + 1 - t := by
        push_cast [htv]; ring
      have h2 : ((t * t - t : ℕ) : ℤ) = (t : ℤ) * t - t := by
        push_cast [Nat.le_mul_self t]; ring
      have := (Nat.cast_le (α := ℤ)).mpr hcs
      push_cast at this
      rw [h1, h2] at this
      linarith
    have : (0 : ℤ) ≤ t * ((q : ℤ) ^ 3 - ((t : ℤ) - 1) ^ 2) := by nlinarith
    have hz' : (t : ℤ) * (t * t + 1) ≤ t * (q ^ 3) + t * (2 * t) := by nlinarith
    exact_mod_cast hz'
  have key2 : t * (t * t + 1) ≤ t * (q ^ 3 + 2 * t) := by
    calc t * (t * t + 1) ≤ t * q ^ 3 + t * (2 * t) := key
      _ = t * (q ^ 3 + 2 * t) := by ring
  have : t * t + 1 ≤ q ^ 3 + 2 * t := Nat.le_of_mul_le_mul_left key2 hpos
  have hsq : (t - 1) ^ 2 + 2 * t = t * t + 1 := by
    zify [ht1]
    ring
  omega

/-- **Lemma PG.** A separated centred set in a projective plane of order `q` has at most `4q`
points, or else `(|S| - 1)² ≤ q³`. -/
theorem card_le (hC : C.Separated) :
    C.S.card ≤ 4 * order P L ∨ (C.S.card - 1) ^ 2 ≤ order P L ^ 3 := by
  by_cases hone : ∀ s ∈ C.S, ∀ s' ∈ C.S, C.graph.Reachable (Sum.inr s) (Sum.inr s')
  · exact Or.inr (C.card_le_of_one hC hone)
  · push Not at hone
    obtain ⟨s₀, hs₀, s₁, hs₁, h01⟩ := hone
    exact Or.inl (C.card_le_of_two hC hs₀ hs₁ h01)

/-- **Lemma PG, consequence.** For `q ≥ 7`, a separated centred set contains fewer than half of the
points of the plane. -/
theorem two_mul_card_lt (hC : C.Separated) (hq : 7 ≤ order P L) :
    2 * C.S.card < order P L ^ 2 + order P L + 1 := by
  set q := order P L
  set t := C.S.card
  rcases C.card_le hC with h | h
  · nlinarith
  · by_contra hcon
    push Not at hcon
    -- `2 t ≥ q² + q + 1` forces `(t - 1)² > q³`
    have h1 : q ^ 2 + q - 1 ≤ 2 * (t - 1) := by omega
    have h2 : (q ^ 2 + q - 1) ^ 2 ≤ 4 * (t - 1) ^ 2 := by
      have := Nat.mul_le_mul h1 h1
      nlinarith
    have h3 : 4 * q ^ 3 < (q ^ 2 + q - 1) ^ 2 := by
      have hq1 : 1 ≤ q ^ 2 + q := by nlinarith
      zify [hq1]
      have : (7 : ℤ) ≤ q := by exact_mod_cast hq
      nlinarith
    nlinarith

end Centred

end MergeDepth
