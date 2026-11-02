import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import AboveHalfRate.Fluid

/-!
# Lift selections of low degeneracy

The deterministic part of Theorem D. The vertices of a finite graph carry labels `ξ : W → ℝ` below
`1` (in the paper: distinct labels in `(0, 1)`). Every vertex `v` has two *lifts* `(v, false)`
and `(v, true)`, written `(v, 0)` and `(v, 1)` in the paper, placed on the line at
`liftPos ξ (v, false) = ξ v` and `liftPos ξ (v, true) = 2 - ξ v`; distinct labels give distinct
positions (`liftPos_injective`). A *lift* of an edge `s(x, y)` is one of the four pairs
`s((x, i), (y, j))` (`isLift_iff`), and a *lift selection* chooses one lift of every edge.
A finite set `A` of pairs is `t`-degenerate for an order `p` (`IsDegenerateFor`) if every vertex
is the earlier endpoint (`IsEarlierEnd`) of at most `t` pairs of `A`.

* **Options** (`isEarlierEnd_lifts`, `IsOption`, `isOption_mk_iff`,
  `isOption_iff_exists_lift`). For an edge with `ξ x < ξ y`, the earlier endpoints of its four
  lifts are `(x, 0)`, `(x, 0)`, `(y, 0)` and `(y, 1)`. These three lifted vertices are the
  *options* of the edge.
* **Construction** (`liftOf`, `liftOf_options`, `isLift_liftOf`, `isEarlierEnd_liftOf`). The
  option `z` of `e` is realized by the lift joining `z` to the lift `1` of the other endpoint;
  its earlier endpoint is `z`. Hence if every lifted vertex is the option of at most `t` edges,
  the selection `A` is `t`-degenerate for `liftPos ξ` (`isDegenerateFor_image_liftOf`). Swapping
  the two lifts of every vertex is an isomorphism, so `B = swap(A)` is `t`-degenerate for the
  swapped order `liftPos ξ ∘ liftSwap` (`IsDegenerateFor.image_map_liftSwap`).
* **Hall rounding** (`exists_assignment_of_fractional`). A fractional assignment of the elements
  of a finite type to their options with all loads at most the natural number `T` rounds to an
  assignment in which every option is used at most `T` times (Hall's theorem applied to `T`
  copies of every option).
* **Theorem D, deterministic part** (`exists_liftSelection_of_fractional`, and
  `exists_liftSelection_degenerate` for the edge set of a simple graph). A fractional assignment
  of the edges to their options with all loads at most `T` yields a lift selection `A` such that
  `A` and `swap(A)` are both `T`-degenerate. Only labels below `1` are needed here.
* **The fluid rule** (`fluidCharge`, `sum_optionSet_fluidCharge`, `sum_fluidCharge_eq`,
  `exists_liftSelection_of_fluid`). The charging rule of `AboveHalfRate.Fluid` is such a
  fractional assignment when the labels are distinct and lie in `(0, 1)`; its load on the lifted
  vertex `(v, b)` is `∑_{w ∼ v} f_b (ξ v) (ξ w)`. Hence if all these neighbour sums are at most
  `T`, there is a lift selection `A` with `A` and `swap(A)` both `T`-degenerate.

The probabilistic part of Theorem D (bounding the neighbour sums for random labels by Bernstein's
inequality, using the moments computed in `AboveHalfRate.Fluid`, and the union bound) is not
formalized here.
-/

namespace AboveHalf

open Finset

set_option autoImplicit false

/-! ### Earlier endpoints and degeneracy -/

section Degeneracy

variable {V : Type*}

/-- `z` is the *earlier endpoint* of the pair `a` for the position function `p`: `a = s(z, w)`
with `p z < p w`. -/
def IsEarlierEnd (p : V → ℝ) (a : Sym2 V) (z : V) : Prop :=
  ∃ w, a = s(z, w) ∧ p z < p w

/-- A pair has at most one earlier endpoint. -/
theorem IsEarlierEnd.unique {p : V → ℝ} {a : Sym2 V} {z z' : V} (h : IsEarlierEnd p a z)
    (h' : IsEarlierEnd p a z') : z = z' := by
  obtain ⟨w, rfl, hzw⟩ := h
  obtain ⟨w', hw', hzw'⟩ := h'
  rcases Sym2.eq_iff.1 hw' with ⟨h1, -⟩ | ⟨h1, h2⟩
  · exact h1
  · rw [h2] at hzw
    rw [← h1] at hzw'
    exact absurd (hzw.trans hzw') (lt_irrefl _)

/-- `z` is the earlier endpoint of `a` iff `z ∈ a` and the other endpoint of `a` is later. -/
theorem isEarlierEnd_iff_exists_mem {p : V → ℝ} {a : Sym2 V} {z : V} :
    IsEarlierEnd p a z ↔ ∃ h : z ∈ a, p z < p (Sym2.Mem.other h) := by
  constructor
  · rintro ⟨w, rfl, hlt⟩
    refine ⟨Sym2.mem_mk_left z w, ?_⟩
    rwa [Sym2.congr_right.1 (Sym2.other_spec (Sym2.mem_mk_left z w))]
  · rintro ⟨h, hlt⟩
    exact ⟨_, (Sym2.other_spec h).symm, hlt⟩

open Classical in
/-- The *later degree* of `z` in the finite set of pairs `A` for the order `p`: the number of
pairs of `A` whose earlier endpoint is `z`, that is, the number of neighbours of `z` in `A` that
come after `z`. -/
noncomputable def laterDeg (p : V → ℝ) (A : Finset (Sym2 V)) (z : V) : ℕ :=
  #(A.filter fun a => IsEarlierEnd p a z)

/-- `A` is `t`-*degenerate for the order* `p`: every vertex has at most `t` neighbours in `A`
that come after it. -/
def IsDegenerateFor (p : V → ℝ) (A : Finset (Sym2 V)) (t : ℕ) : Prop :=
  ∀ z, laterDeg p A z ≤ t

end Degeneracy

/-! ### Lifted vertices, lifts and the swap -/

section Lift

variable {W : Type*}

/-- The position of a lifted vertex: `(v, false) ↦ ξ v` and `(v, true) ↦ 2 - ξ v`. -/
def liftPos (ξ : W → ℝ) (z : W × Bool) : ℝ :=
  bif z.2 then 2 - ξ z.1 else ξ z.1

@[simp] theorem liftPos_false (ξ : W → ℝ) (v : W) : liftPos ξ (v, false) = ξ v := rfl

@[simp] theorem liftPos_true (ξ : W → ℝ) (v : W) : liftPos ξ (v, true) = 2 - ξ v := rfl

/-- With distinct labels below `1`, distinct lifted vertices have distinct positions: the lifts
`0` lie below `1` and the lifts `1` lie above `1`. -/
theorem liftPos_injective {ξ : W → ℝ} (hinj : Function.Injective ξ) (hξ : ∀ v, ξ v < 1) :
    Function.Injective (liftPos ξ) := by
  rintro ⟨v, _ | _⟩ ⟨v', _ | _⟩ h <;> simp only [liftPos_false, liftPos_true] at h
  · rw [hinj h]
  · linarith [hξ v, hξ v']
  · linarith [hξ v, hξ v']
  · rw [hinj (by linarith : ξ v = ξ v')]

/-- The swap of a lifted vertex, `(v, b) ↦ (v, !b)`. -/
def liftSwap (z : W × Bool) : W × Bool := (z.1, !z.2)

@[simp] theorem liftSwap_mk (v : W) (b : Bool) : liftSwap (v, b) = (v, !b) := rfl

@[simp] theorem liftSwap_liftSwap (z : W × Bool) : liftSwap (liftSwap z) = z := by
  simp [liftSwap]

/-- The swap is an involution. -/
theorem liftSwap_involutive : Function.Involutive (liftSwap (W := W)) := liftSwap_liftSwap

/-- Swapping a pair of lifted vertices twice gives it back. -/
@[simp] theorem map_liftSwap_map_liftSwap (a : Sym2 (W × Bool)) :
    Sym2.map liftSwap (Sym2.map liftSwap a) = a := by
  refine Sym2.inductionOn a fun x y => ?_
  simp only [Sym2.map_mk, liftSwap_liftSwap]

/-- `a` is a *lift* of the edge `e`: forgetting the second coordinates maps `a` to `e`. -/
def IsLift (e : Sym2 W) (a : Sym2 (W × Bool)) : Prop :=
  Sym2.map Prod.fst a = e

/-- The lifts of `s(x, y)` are the four pairs `s((x, i), (y, j))`. -/
theorem isLift_iff {x y : W} {a : Sym2 (W × Bool)} :
    IsLift s(x, y) a ↔ ∃ i j : Bool, a = s((x, i), (y, j)) := by
  constructor
  · refine Sym2.inductionOn a fun p q h => ?_
    simp only [IsLift, Sym2.map_mk] at h
    rcases Sym2.eq_iff.1 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨p.2, q.2, rfl⟩
    · exact ⟨q.2, p.2, Sym2.eq_swap⟩
  · rintro ⟨i, j, rfl⟩
    rfl

/-- Swapping both endpoints of a lift of `e` gives a lift of `e`. -/
theorem IsLift.map_liftSwap {e : Sym2 W} {a : Sym2 (W × Bool)} (h : IsLift e a) :
    IsLift e (Sym2.map liftSwap a) := by
  rw [IsLift, Sym2.map_map]
  exact h

/-- The swap carries the order `p ∘ liftSwap` to the order `p`: `z` is the earlier endpoint of
`swap(a)` for `p ∘ liftSwap` iff `swap(z)` is the earlier endpoint of `a` for `p`. -/
theorem isEarlierEnd_map_liftSwap {p : W × Bool → ℝ} {a : Sym2 (W × Bool)} {z : W × Bool} :
    IsEarlierEnd (p ∘ liftSwap) (Sym2.map liftSwap a) z ↔ IsEarlierEnd p a (liftSwap z) := by
  constructor
  · rintro ⟨w, hw, hlt⟩
    refine ⟨liftSwap w, ?_, hlt⟩
    have := congrArg (Sym2.map liftSwap) hw
    rwa [map_liftSwap_map_liftSwap, Sym2.map_mk] at this
  · rintro ⟨w, rfl, hlt⟩
    refine ⟨liftSwap w, ?_, ?_⟩
    · rw [Sym2.map_mk, liftSwap_liftSwap]
    · simpa only [Function.comp_apply, liftSwap_liftSwap] using hlt

/-- The later degree of `z` in `swap(A)` for the swapped order is the later degree of `swap(z)`
in `A`. -/
theorem laterDeg_image_map_liftSwap [DecidableEq W] (p : W × Bool → ℝ)
    (A : Finset (Sym2 (W × Bool))) (z : W × Bool) :
    laterDeg (p ∘ liftSwap) (A.image (Sym2.map liftSwap)) z = laterDeg p A (liftSwap z) := by
  classical
  unfold laterDeg
  rw [filter_image, card_image_of_injective _ (Sym2.map.injective liftSwap_involutive.injective)]
  congr 1
  exact filter_congr fun a _ => isEarlierEnd_map_liftSwap

/-- **Swapping preserves degeneracy.** If `A` is `t`-degenerate for `p`, then `B = swap(A)` is
`t`-degenerate for the swapped order `p ∘ liftSwap`. -/
theorem IsDegenerateFor.image_map_liftSwap [DecidableEq W] {p : W × Bool → ℝ}
    {A : Finset (Sym2 (W × Bool))} {t : ℕ} (h : IsDegenerateFor p A t) :
    IsDegenerateFor (p ∘ liftSwap) (A.image (Sym2.map liftSwap)) t := fun z =>
  (laterDeg_image_map_liftSwap p A z).trans_le (h _)

open Classical in
/-- For a selection `L` of lifts of the edges of `F`, the later degree of `z` in the selected set
`L(F)` counts the edges whose selected lift has earlier endpoint `z`. -/
theorem laterDeg_image [DecidableEq W] {p : W × Bool → ℝ} {F : Finset (Sym2 W)}
    {L : Sym2 W → Sym2 (W × Bool)} (hL : ∀ e ∈ F, IsLift e (L e)) (z : W × Bool) :
    laterDeg p (F.image L) z = #(F.filter fun e => IsEarlierEnd p (L e) z) := by
  unfold laterDeg
  rw [filter_image, card_image_of_injOn]
  intro e he e' he' h
  rw [coe_filter] at he he'
  rw [← hL e he.1, ← hL e' he'.1, h]

end Lift

/-! ### Options and the construction of the selection -/

section Options

variable {W : Type*}

/-- **The four lifts of an edge.** For an edge `s(x, y)` with `ξ x < ξ y` and labels below `1`,
the earlier endpoints of the four lifts `s((x,0),(y,0))`, `s((x,0),(y,1))`, `s((x,1),(y,0))`,
`s((x,1),(y,1))` are `(x,0)`, `(x,0)`, `(y,0)` and `(y,1)`. -/
theorem isEarlierEnd_lifts {ξ : W → ℝ} (hξ : ∀ v, ξ v < 1) {x y : W} (hxy : ξ x < ξ y) :
    IsEarlierEnd (liftPos ξ) s((x, false), (y, false)) (x, false) ∧
    IsEarlierEnd (liftPos ξ) s((x, false), (y, true)) (x, false) ∧
    IsEarlierEnd (liftPos ξ) s((x, true), (y, false)) (y, false) ∧
    IsEarlierEnd (liftPos ξ) s((x, true), (y, true)) (y, true) := by
  have hx := hξ x
  have hy := hξ y
  refine ⟨⟨(y, false), rfl, ?_⟩, ⟨(y, true), rfl, ?_⟩, ⟨(x, true), Sym2.eq_swap, ?_⟩,
    ⟨(x, true), Sym2.eq_swap, ?_⟩⟩ <;> simp only [liftPos_false, liftPos_true] <;> linarith

/-- `z = (v, b)` is an *option* of the edge `e`: `v` is an endpoint of `e`, and if `b = true`
then the other endpoint has a smaller label. For `ξ x < ξ y` the options of `s(x, y)` are
`(x, false)`, `(y, false)` and `(y, true)` (`isOption_mk_iff`). -/
def IsOption (ξ : W → ℝ) (e : Sym2 W) (z : W × Bool) : Prop :=
  ∃ w, e = s(z.1, w) ∧ (z.2 = true → ξ w < ξ z.1)

/-- The options of an edge `s(x, y)` with `ξ x < ξ y` are `(x, 0)`, `(y, 0)` and `(y, 1)`. -/
theorem isOption_mk_iff {ξ : W → ℝ} {x y : W} (hxy : ξ x < ξ y) {z : W × Bool} :
    IsOption ξ s(x, y) z ↔ z = (x, false) ∨ z = (y, false) ∨ z = (y, true) := by
  obtain ⟨v, b⟩ := z
  constructor
  · rintro ⟨w, he, hb⟩
    simp only at he hb
    rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases b
      · exact Or.inl rfl
      · exact absurd (hb rfl) (not_lt.2 hxy.le)
    · cases b
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
  · rintro (h | h | h) <;> obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    · exact ⟨y, rfl, fun h => absurd h Bool.false_ne_true⟩
    · exact ⟨x, Sym2.eq_swap, fun h => absurd h Bool.false_ne_true⟩
    · exact ⟨x, Sym2.eq_swap, fun _ => hxy⟩

open Classical in
/-- The lift realizing the option `z` of the edge `e`: it joins `z` to the lift `1` of the other
endpoint of `e`. (The value when `z.1 ∉ e` is irrelevant.) -/
noncomputable def liftOf (e : Sym2 W) (z : W × Bool) : Sym2 (W × Bool) :=
  if h : z.1 ∈ e then s(z, (Sym2.Mem.other h, true)) else s(z, z)

/-- If `e = s(v, w)`, the option `(v, b)` is realized by `s((v, b), (w, 1))`. -/
theorem liftOf_eq {e : Sym2 W} {z : W × Bool} {w : W} (he : e = s(z.1, w)) :
    liftOf e z = s(z, (w, true)) := by
  subst he
  have h : z.1 ∈ s(z.1, w) := Sym2.mem_mk_left _ _
  rw [liftOf, dite_eq_left h, Sym2.congr_right.1 (Sym2.other_spec h)]

/-- The three lifts of the construction, for `e = s(x, y)`: the option `(x, 0)` is realized by
`s((x,0),(y,1))`, the option `(y, 0)` by `s((x,1),(y,0))` and the option `(y, 1)` by
`s((x,1),(y,1))`. -/
theorem liftOf_options (x y : W) :
    liftOf s(x, y) (x, false) = s((x, false), (y, true)) ∧
    liftOf s(x, y) (y, false) = s((x, true), (y, false)) ∧
    liftOf s(x, y) (y, true) = s((x, true), (y, true)) :=
  ⟨liftOf_eq rfl, (liftOf_eq (z := (y, false)) Sym2.eq_swap).trans Sym2.eq_swap,
    (liftOf_eq (z := (y, true)) Sym2.eq_swap).trans Sym2.eq_swap⟩

/-- The construction gives a lift of the edge. -/
theorem isLift_liftOf {ξ : W → ℝ} {e : Sym2 W} {z : W × Bool} (h : IsOption ξ e z) :
    IsLift e (liftOf e z) := by
  obtain ⟨w, rfl, -⟩ := h
  rw [liftOf_eq rfl]
  rfl

/-- The earlier endpoint of the lift realizing an option is that option, and the other endpoint
is later. -/
theorem isEarlierEnd_liftOf {ξ : W → ℝ} (hξ : ∀ v, ξ v < 1) {e : Sym2 W} {z : W × Bool}
    (h : IsOption ξ e z) : IsEarlierEnd (liftPos ξ) (liftOf e z) z := by
  obtain ⟨w, rfl, hb⟩ := h
  refine ⟨(w, true), liftOf_eq rfl, ?_⟩
  obtain ⟨v, b⟩ := z
  have hv := hξ v
  have hw := hξ w
  cases b
  · simp only [liftPos_false, liftPos_true]
    linarith
  · have := hb rfl
    simp only [liftPos_true] at this ⊢
    linarith

/-- The options of an edge are exactly the earlier endpoints of its lifts. -/
theorem isOption_iff_exists_lift {ξ : W → ℝ} (hξ : ∀ v, ξ v < 1) {e : Sym2 W} {z : W × Bool} :
    IsOption ξ e z ↔ ∃ a, IsLift e a ∧ IsEarlierEnd (liftPos ξ) a z := by
  constructor
  · exact fun h => ⟨liftOf e z, isLift_liftOf h, isEarlierEnd_liftOf hξ h⟩
  · rintro ⟨a, ha, w, rfl, hlt⟩
    refine ⟨w.1, ha.symm, fun hz => ?_⟩
    obtain ⟨v, b⟩ := z
    obtain ⟨u, c⟩ := w
    simp only at hz ⊢
    subst hz
    have hv := hξ v
    have hu := hξ u
    cases c
    · simp only [liftPos_true, liftPos_false] at hlt
      linarith
    · simp only [liftPos_true] at hlt
      linarith

/-- The options of the edge `e`, as a finite set of lifted vertices. -/
noncomputable def optionSet [Fintype W] (ξ : W → ℝ) (e : Sym2 W) : Finset (W × Bool) := by
  classical exact univ.filter (IsOption ξ e)

/-- Membership in `optionSet`. -/
@[simp] theorem mem_optionSet [Fintype W] {ξ : W → ℝ} {e : Sym2 W} {z : W × Bool} :
    z ∈ optionSet ξ e ↔ IsOption ξ e z := by
  simp [optionSet]

/-- For `ξ x < ξ y` the option set of `s(x, y)` is `{(x, 0), (y, 0), (y, 1)}`. -/
theorem optionSet_mk [Fintype W] [DecidableEq W] {ξ : W → ℝ} {x y : W} (hxy : ξ x < ξ y) :
    optionSet ξ s(x, y) = {(x, false), (y, false), (y, true)} := by
  ext z
  simp [isOption_mk_iff hxy]

open Classical in
/-- **Degeneracy of the constructed selection.** Let `o` choose an option `o e` of every edge
`e ∈ F`. If every lifted vertex is chosen by at most `t` edges, then every lifted vertex `z` is
the earlier endpoint of at most `t` of the selected lifts `liftOf e (o e)`; that is, at most `t`
selected lifts contain `z` and have their other endpoint later than `z`
(`isEarlierEnd_iff_exists_mem`). -/
theorem card_filter_isEarlierEnd_liftOf_le [DecidableEq W] {ξ : W → ℝ} (hξ : ∀ v, ξ v < 1)
    {F : Finset (Sym2 W)} {o : Sym2 W → W × Bool} (ho : ∀ e ∈ F, IsOption ξ e (o e)) {t : ℕ}
    (ht : ∀ z, #(F.filter fun e => o e = z) ≤ t) (z : W × Bool) :
    #(F.filter fun e => IsEarlierEnd (liftPos ξ) (liftOf e (o e)) z) ≤ t := by
  refine (card_le_card fun e he => ?_).trans (ht z)
  rw [mem_filter] at he ⊢
  exact ⟨he.1, (isEarlierEnd_liftOf hξ (ho e he.1)).unique he.2⟩

/-- **Degeneracy of the constructed selection, as a set of lifted edges.** Under the hypotheses
of `card_filter_isEarlierEnd_liftOf_le`, the selection `A = {liftOf e (o e) : e ∈ F}` is
`t`-degenerate for `liftPos ξ`, and `B = swap(A)` is `t`-degenerate for `liftPos ξ ∘ liftSwap`. -/
theorem isDegenerateFor_image_liftOf [DecidableEq W] {ξ : W → ℝ} (hξ : ∀ v, ξ v < 1)
    {F : Finset (Sym2 W)} {o : Sym2 W → W × Bool} (ho : ∀ e ∈ F, IsOption ξ e (o e)) {t : ℕ}
    (ht : ∀ z, #(F.filter fun e => o e = z) ≤ t) :
    IsDegenerateFor (liftPos ξ) (F.image fun e => liftOf e (o e)) t ∧
    IsDegenerateFor (liftPos ξ ∘ liftSwap)
      ((F.image fun e => liftOf e (o e)).image (Sym2.map liftSwap)) t := by
  have hA : IsDegenerateFor (liftPos ξ) (F.image fun e => liftOf e (o e)) t := fun z => by
    rw [laterDeg_image fun e he => isLift_liftOf (ho e he)]
    exact card_filter_isEarlierEnd_liftOf_le hξ ho ht z
  exact ⟨hA, hA.image_map_liftSwap⟩

end Options

/-! ### Hall rounding -/

/-- **Hall rounding.** Let every element `e` of a finite type `E` carry a finite set of options
`opts e` and nonnegative weights `w e o` on them summing to `1`. If every option `o` carries total
weight at most the natural number `T`, then there is an assignment `f` choosing an option of every
element such that every option is chosen at most `T` times. -/
theorem exists_assignment_of_fractional {E O : Type*} [Fintype E] [DecidableEq O]
    (opts : E → Finset O) (w : E → O → ℝ) (hw0 : ∀ e, ∀ o ∈ opts e, 0 ≤ w e o)
    (hw1 : ∀ e, ∑ o ∈ opts e, w e o = 1) (T : ℕ)
    (hT : ∀ o, ∑ e, (if o ∈ opts e then w e o else 0) ≤ T) :
    ∃ f : E → O, (∀ e, f e ∈ opts e) ∧ ∀ o, #(univ.filter fun e => f e = o) ≤ T := by
  -- Hall's condition for the family `e ↦ opts e × Fin T` of `T` copies of the options
  have hall : ∀ S : Finset E, #S ≤ #(S.biUnion fun e => opts e ×ˢ (univ : Finset (Fin T))) := by
    intro S
    have hU : (S.biUnion fun e => opts e ×ˢ (univ : Finset (Fin T))) =
        S.biUnion opts ×ˢ univ := by
      ext ⟨o, i⟩
      simp
    have key : (#S : ℝ) ≤ #(S.biUnion opts) * T := by
      calc (#S : ℝ) = ∑ e ∈ S, ∑ o ∈ opts e, w e o := by simp [hw1]
        _ = ∑ e ∈ S, ∑ o ∈ S.biUnion opts, (if o ∈ opts e then w e o else 0) := by
          refine sum_congr rfl fun e he => ?_
          rw [sum_ite_mem, inter_eq_right.2 (subset_biUnion_of_mem opts he)]
        _ = ∑ o ∈ S.biUnion opts, ∑ e ∈ S, (if o ∈ opts e then w e o else 0) := sum_comm
        _ ≤ ∑ o ∈ S.biUnion opts, ∑ e, (if o ∈ opts e then w e o else 0) := by
          refine sum_le_sum fun o _ => sum_le_sum_of_subset_of_nonneg (subset_univ S) ?_
          intro e _ _
          split_ifs with h
          · exact hw0 e o h
          · exact le_rfl
        _ ≤ ∑ _o ∈ S.biUnion opts, (T : ℝ) := sum_le_sum fun o _ => hT o
        _ = #(S.biUnion opts) * T := by rw [sum_const, nsmul_eq_mul]
    rw [hU, card_product, card_univ, Fintype.card_fin]
    exact_mod_cast key
  obtain ⟨g, hg, hgmem⟩ := (all_card_le_biUnion_card_iff_existsInjective' _).1 hall
  refine ⟨fun e => (g e).1, fun e => (mem_product.1 (hgmem e)).1, fun o => ?_⟩
  -- the fibre over `o` injects into `Fin T` through the second coordinate
  calc #(univ.filter fun e => (g e).1 = o) ≤ #(univ : Finset (Fin T)) := by
        refine card_le_card_of_injOn (fun e => (g e).2) (fun e _ => by simp) ?_
        intro e he e' he' h
        rw [mem_coe, mem_filter] at he he'
        exact hg (Prod.ext (he.2.trans he'.2.symm) h)
    _ = T := by simp

/-! ### Theorem D, deterministic part -/

section LemmaD

variable {W : Type*}

/-- Counting a filter of `F` on the subtype `↥F`. -/
private lemma card_filter_univ_coe {α : Type*} (F : Finset α) (P : α → Prop) [DecidablePred P] :
    #((univ : Finset F).filter fun e : F => P e) = #(F.filter P) := by
  rw [card_filter, card_filter]
  exact sum_coe_sort F fun e => if P e then 1 else 0

/-- **Theorem D, deterministic part.** Let the labels be below `1`, and let `w` be a fractional
assignment of the edges `e ∈ F` to their options: nonnegative weights on `optionSet ξ e` summing
to `1`, such that the total weight on every lifted vertex is at most the natural number `T`.
Then there is a lift selection `L` of `F`, choosing for every edge the lift `liftOf e z` of one
of its options `z`, such that the selected set `A = L(F)` is `T`-degenerate for `liftPos ξ` and
`B = swap(A)` is `T`-degenerate for the swapped order `liftPos ξ ∘ liftSwap`. -/
theorem exists_liftSelection_of_fractional [DecidableEq W] [Fintype W] {ξ : W → ℝ}
    (hξ : ∀ v, ξ v < 1) (F : Finset (Sym2 W)) (w : Sym2 W → W × Bool → ℝ)
    (hw0 : ∀ e ∈ F, ∀ z ∈ optionSet ξ e, 0 ≤ w e z)
    (hw1 : ∀ e ∈ F, ∑ z ∈ optionSet ξ e, w e z = 1) (T : ℕ)
    (hT : ∀ z, ∑ e ∈ F, (if z ∈ optionSet ξ e then w e z else 0) ≤ T) :
    ∃ L : Sym2 W → Sym2 (W × Bool),
      (∀ e ∈ F, ∃ z, IsOption ξ e z ∧ L e = liftOf e z) ∧
      (∀ e ∈ F, IsLift e (L e)) ∧
      IsDegenerateFor (liftPos ξ) (F.image L) T ∧
      IsDegenerateFor (liftPos ξ ∘ liftSwap) ((F.image L).image (Sym2.map liftSwap)) T := by
  classical
  obtain ⟨f, hf, hfib⟩ := exists_assignment_of_fractional (E := F) (fun e => optionSet ξ e)
    (fun e z => w e z) (fun e z hz => hw0 e e.2 z hz) (fun e => hw1 e e.2) T fun z => by
      rw [sum_coe_sort F fun e => if z ∈ optionSet ξ e then w e z else 0]
      exact hT z
  let L : Sym2 W → Sym2 (W × Bool) := fun e =>
    if h : e ∈ F then liftOf e (f ⟨e, h⟩) else Sym2.map (fun v => (v, false)) e
  have hLF : ∀ e (h : e ∈ F), L e = liftOf e (f ⟨e, h⟩) := fun e h => dite_eq_left h
  have hopt : ∀ e (h : e ∈ F), IsOption ξ e (f ⟨e, h⟩) := fun e h => mem_optionSet.1 (hf ⟨e, h⟩)
  have hlift : ∀ e ∈ F, IsLift e (L e) := fun e h => (hLF e h) ▸ isLift_liftOf (hopt e h)
  have hA : IsDegenerateFor (liftPos ξ) (F.image L) T := by
    intro z
    rw [laterDeg_image hlift, ← card_filter_univ_coe]
    refine (card_le_card fun e he => ?_).trans (hfib z)
    rw [mem_filter] at he ⊢
    refine ⟨mem_univ _, ?_⟩
    have h1 := isEarlierEnd_liftOf hξ (hopt e e.2)
    rw [← hLF e e.2] at h1
    exact h1.unique he.2
  exact ⟨L, fun e h => ⟨_, hopt e h, hLF e h⟩, hlift, hA, hA.image_map_liftSwap⟩

/-- **Theorem D, deterministic part, for a finite simple graph** (`exists_liftSelection_of_fractional`
for the edge set of `X`). -/
theorem exists_liftSelection_degenerate [DecidableEq W] [Fintype W] (X : SimpleGraph W)
    [DecidableRel X.Adj] {ξ : W → ℝ} (hξ : ∀ v, ξ v < 1) (w : Sym2 W → W × Bool → ℝ)
    (hw0 : ∀ e ∈ X.edgeFinset, ∀ z ∈ optionSet ξ e, 0 ≤ w e z)
    (hw1 : ∀ e ∈ X.edgeFinset, ∑ z ∈ optionSet ξ e, w e z = 1) (T : ℕ)
    (hT : ∀ z, ∑ e ∈ X.edgeFinset, (if z ∈ optionSet ξ e then w e z else 0) ≤ T) :
    ∃ L : Sym2 W → Sym2 (W × Bool),
      (∀ e ∈ X.edgeFinset, ∃ z, IsOption ξ e z ∧ L e = liftOf e z) ∧
      (∀ e ∈ X.edgeFinset, IsLift e (L e)) ∧
      IsDegenerateFor (liftPos ξ) (X.edgeFinset.image L) T ∧
      IsDegenerateFor (liftPos ξ ∘ liftSwap)
        ((X.edgeFinset.image L).image (Sym2.map liftSwap)) T :=
  exists_liftSelection_of_fractional hξ X.edgeFinset w hw0 hw1 T hT

end LemmaD

/-! ### The fluid rule as a fractional assignment -/

section FluidRule

variable {W : Type*}

open Classical in
/-- The charge that the fluid rule of `AboveHalfRate.Fluid` sends from the edge `e` to the lifted
vertex `z = (v, b)`: if `v ∈ e` and `w` is the other endpoint of `e`, it is `Fluid.f1 (ξ v) (ξ w)`
for `b = true` and `Fluid.f0 (ξ v) (ξ w)` for `b = false`; it is `0` if `v ∉ e`. For
`e = s(x, y)` with `ξ x < ξ y` the edge sends `a1 (ξ y)` to `(y, 1)`, `a0 (ξ y)` to `(y, 0)`,
`b0 (ξ y)` to `(x, 0)` and nothing to `(x, 1)` (`fluidCharge_options`). -/
noncomputable def fluidCharge (ξ : W → ℝ) (e : Sym2 W) (z : W × Bool) : ℝ :=
  if h : z.1 ∈ e then (bif z.2 then Fluid.f1 else Fluid.f0) (ξ z.1) (ξ (Sym2.Mem.other h))
  else 0

/-- If `e = s(v, w)`, the edge sends `f_b (ξ v) (ξ w)` to `(v, b)`. -/
theorem fluidCharge_eq {ξ : W → ℝ} {e : Sym2 W} {z : W × Bool} {w : W} (he : e = s(z.1, w)) :
    fluidCharge ξ e z = (bif z.2 then Fluid.f1 else Fluid.f0) (ξ z.1) (ξ w) := by
  subst he
  have h : z.1 ∈ s(z.1, w) := Sym2.mem_mk_left _ _
  rw [fluidCharge, dite_eq_left h, Sym2.congr_right.1 (Sym2.other_spec h)]

/-- An edge sends nothing to the lifts of a vertex outside it. -/
theorem fluidCharge_of_not_mem {ξ : W → ℝ} {e : Sym2 W} {z : W × Bool} (h : z.1 ∉ e) :
    fluidCharge ξ e z = 0 := by
  rw [fluidCharge, dite_eq_right h]

/-- The fluid charges of an edge `s(x, y)` with `ξ x < ξ y`. -/
theorem fluidCharge_options {ξ : W → ℝ} {x y : W} (hxy : ξ x < ξ y) :
    fluidCharge ξ s(x, y) (y, true) = Fluid.a1 (ξ y) ∧
    fluidCharge ξ s(x, y) (y, false) = Fluid.a0 (ξ y) ∧
    fluidCharge ξ s(x, y) (x, false) = Fluid.b0 (ξ y) ∧
    fluidCharge ξ s(x, y) (x, true) = 0 := by
  have hyx : ¬ ξ y < ξ x := not_lt.2 hxy.le
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [fluidCharge_eq (z := (y, true)) Sym2.eq_swap]
    simp [Fluid.f1, hxy]
  · rw [fluidCharge_eq (z := (y, false)) Sym2.eq_swap]
    simp [Fluid.f0, hxy]
  · rw [fluidCharge_eq (z := (x, false)) rfl]
    simp [Fluid.f0, hxy, hyx]
  · rw [fluidCharge_eq (z := (x, true)) rfl]
    simp [Fluid.f1, hyx]

/-- With positive labels the fluid charges are nonnegative. -/
theorem fluidCharge_nonneg {ξ : W → ℝ} (hξ : ∀ v, 0 < ξ v) (e : Sym2 W) (z : W × Bool) :
    0 ≤ fluidCharge ξ e z := by
  obtain ⟨v, b⟩ := z
  unfold fluidCharge
  split_ifs with h
  · cases b
    · exact Fluid.f0_nonneg (hξ v) _
    · exact Fluid.f1_nonneg (hξ v) _
  · exact le_rfl

/-- The fluid rule charges only options. -/
theorem fluidCharge_eq_zero_of_not_isOption {ξ : W → ℝ} {e : Sym2 W} {z : W × Bool}
    (h : ¬ IsOption ξ e z) : fluidCharge ξ e z = 0 := by
  by_cases hz : z.1 ∈ e
  · obtain ⟨v, b⟩ := z
    have he : e = s(v, Sym2.Mem.other hz) := (Sym2.other_spec hz).symm
    rw [fluidCharge_eq (z := (v, b)) he]
    have hb : b = true ∧ ¬ ξ (Sym2.Mem.other hz) < ξ v := by
      by_contra hc
      refine h ⟨Sym2.Mem.other hz, he, fun hb => ?_⟩
      by_contra hlt
      exact hc ⟨hb, hlt⟩
    obtain ⟨rfl, hlt⟩ := hb
    simp [Fluid.f1, hlt]
  · exact fluidCharge_of_not_mem hz

/-- With positive labels and `ξ x ≠ ξ y`, the edge `s(x, y)` distributes one unit of fluid charge
over its options. -/
theorem sum_optionSet_fluidCharge [Fintype W] [DecidableEq W] {ξ : W → ℝ} (hξ : ∀ v, 0 < ξ v)
    {x y : W} (hxy : ξ x ≠ ξ y) : ∑ z ∈ optionSet ξ s(x, y), fluidCharge ξ s(x, y) z = 1 := by
  wlog h : ξ x < ξ y generalizing x y
  · rw [Sym2.eq_swap]
    exact this hxy.symm (lt_of_le_of_ne (not_lt.1 h) hxy.symm)
  have hne : x ≠ y := fun hxy' => hxy (congrArg ξ hxy')
  obtain ⟨h1, h2, h3, -⟩ := fluidCharge_options (ξ := ξ) h
  have hx : (x, false) ∉ ({(y, false), (y, true)} : Finset (W × Bool)) := by simp [hne]
  have hy : (y, false) ∉ ({(y, true)} : Finset (W × Bool)) := by simp
  rw [optionSet_mk h, sum_insert hx, sum_insert hy, sum_singleton, h1, h2, h3]
  linarith [Fluid.charges_sum (hξ y)]

/-- The fluid load of the lifted vertex `(v, b)` is the sum of `Fluid.f1` (for `b = true`) or
`Fluid.f0` (for `b = false`) over the neighbours of `v`. -/
theorem sum_fluidCharge_eq [Fintype W] [DecidableEq W] (X : SimpleGraph W) [DecidableRel X.Adj]
    (ξ : W → ℝ) (v : W) (b : Bool) :
    ∑ e ∈ X.edgeFinset, (if (v, b) ∈ optionSet ξ e then fluidCharge ξ e (v, b) else 0) =
      ∑ w ∈ X.neighborFinset v, (bif b then Fluid.f1 else Fluid.f0) (ξ v) (ξ w) := by
  have hopt : ∀ e, (if (v, b) ∈ optionSet ξ e then fluidCharge ξ e (v, b) else 0) =
      fluidCharge ξ e (v, b) := fun e => by
    split_ifs with h
    · rfl
    · exact (fluidCharge_eq_zero_of_not_isOption (mt mem_optionSet.2 h)).symm
  have hsub : (X.neighborFinset v).image (fun w => s(v, w)) ⊆ X.edgeFinset := by
    intro e he
    obtain ⟨w, hw, rfl⟩ := mem_image.1 he
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact (X.mem_neighborFinset v w).1 hw
  have hzero : ∀ e ∈ X.edgeFinset, e ∉ (X.neighborFinset v).image (fun w => s(v, w)) →
      fluidCharge ξ e (v, b) = 0 := by
    intro e he hne
    refine fluidCharge_of_not_mem fun hv => hne (mem_image.2 ⟨Sym2.Mem.other hv, ?_,
      Sym2.other_spec hv⟩)
    rw [SimpleGraph.mem_neighborFinset, ← SimpleGraph.mem_edgeSet, Sym2.other_spec hv]
    exact SimpleGraph.mem_edgeFinset.1 he
  have hinj : Set.InjOn (fun w => s(v, w)) (X.neighborFinset v : Set W) :=
    fun w _ w' _ h => Sym2.congr_right.1 h
  rw [sum_congr rfl fun e _ => hopt e, ← sum_subset hsub hzero, sum_image hinj]
  exact sum_congr rfl fun w _ => fluidCharge_eq (z := (v, b)) rfl

/-- **Theorem D, deterministic part, fluid form.** Let `X` be a finite simple graph whose vertices
carry distinct labels in `(0, 1)`. If for every vertex `v` both fluid loads
`∑_{w ∼ v} Fluid.f1 (ξ v) (ξ w)` and `∑_{w ∼ v} Fluid.f0 (ξ v) (ξ w)` are at most the natural
number `T`, then there is a lift selection `A` of `X` such that `A` is `T`-degenerate for
`liftPos ξ` and `swap(A)` is `T`-degenerate for `liftPos ξ ∘ liftSwap`. -/
theorem exists_liftSelection_of_fluid [Fintype W] [DecidableEq W] (X : SimpleGraph W)
    [DecidableRel X.Adj] {ξ : W → ℝ} (hinj : Function.Injective ξ)
    (hξ : ∀ v, 0 < ξ v ∧ ξ v < 1) (T : ℕ)
    (h1 : ∀ v, ∑ w ∈ X.neighborFinset v, Fluid.f1 (ξ v) (ξ w) ≤ T)
    (h0 : ∀ v, ∑ w ∈ X.neighborFinset v, Fluid.f0 (ξ v) (ξ w) ≤ T) :
    ∃ L : Sym2 W → Sym2 (W × Bool),
      (∀ e ∈ X.edgeFinset, ∃ z, IsOption ξ e z ∧ L e = liftOf e z) ∧
      (∀ e ∈ X.edgeFinset, IsLift e (L e)) ∧
      IsDegenerateFor (liftPos ξ) (X.edgeFinset.image L) T ∧
      IsDegenerateFor (liftPos ξ ∘ liftSwap)
        ((X.edgeFinset.image L).image (Sym2.map liftSwap)) T := by
  refine exists_liftSelection_degenerate X (fun v => (hξ v).2) (fluidCharge ξ)
    (fun e _ z _ => fluidCharge_nonneg (fun v => (hξ v).1) e z) (fun e he => ?_) T
    (fun z => ?_)
  · revert he
    refine Sym2.inductionOn e fun x y he => ?_
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    exact sum_optionSet_fluidCharge (fun v => (hξ v).1) fun h => he.ne (hinj h)
  · obtain ⟨v, b⟩ := z
    rw [sum_fluidCharge_eq]
    cases b
    · exact h0 v
    · exact h1 v

end FluidRule

end AboveHalf
