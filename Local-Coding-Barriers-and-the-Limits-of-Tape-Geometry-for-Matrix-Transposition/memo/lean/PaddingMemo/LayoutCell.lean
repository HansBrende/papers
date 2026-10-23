import PaddingMemo.CellCut
import TransposeFollowup.ExcursionLayout

/-! # Excursion layouts satisfy the cell-accurate cut inequality

The follow-up's padding (family 4) meets the first paper's cut inequality `CutIneq` with the help of
idle tapes, whose per-tape memory-boundary charge `3 k M_b` absorbs the expander edges lost at label
changes. Here the excursions alone are shown to satisfy the cell-accurate inequality `CellCutIneq`,
which charges only the entry cells actually inherited by each label class. This holds for every
slot labelling and every slot length `r' ≤ 7 K r`, with no idle tapes and no degree bound.

The count is per time offset. Fix an offset `o` of the rise ramps, strictly inside their first half,
and its mirror offset `6Kr − o`. For an edge `{u, v}`, the cell that the fall ramp reads at offset `o`
of one endpoint's window was last visited by the rise ramp at offset `6Kr − o` of the other
endpoint's window, and symmetrically. So the edge yields one entry cell for each of the two ordered
pairs whose two slots carry different labels. These ordered pairs are the edges of the bipartite
double cover of the graph between the two offset layers, and vertex expansion of the graph gives
vertex expansion of the double cover.

* `excursion_isLastVisit`: the cell read at fall time `c + (4Kr − j)` was last visited at rise
  time `a + j`.
* `expanding_link_cut`: two colourings of a vertex expander with small joint classes disagree on at
  least `η |V| / 2` ordered adjacent pairs.
* `cellCutIneq_of_layout`: the main theorem.
* `cutIneq_of_cellCutIneq`, `cutIneq_of_layout`: for unit-step walks the cell-accurate inequality
  implies `CutIneq`, so an excursion layout of unit-step walks satisfies the first paper's zero-slack
  cut inequality without any head-count hypothesis.
-/

namespace PaddingMemo

open Classical
open Transpose Transpose.Tape Transpose.Tape.Impl TransposeFollowup
open scoped BigOperators
set_option autoImplicit false

/-! ## All entry cells of a labelling -/

/-- The entry cells of all label classes of `lab` together. -/
noncomputable def allEntryCells {k : ℕ} (r T : ℕ) (h : Fin k → ℕ → ℤ) (lab : ℕ → ℕ) :
    Finset (Fin k × ℕ) :=
  ((Finset.range (numSlots r T)).image lab).biUnion
    (fun ℓ => entryCells (fun τ t => h t τ) (labelPart r lab T ℓ))

theorem card_allEntryCells_le {k : ℕ} (r T : ℕ) (h : Fin k → ℕ → ℤ) (lab : ℕ → ℕ) :
    (allEntryCells r T h lab).card ≤ ∑ ℓ ∈ (Finset.range (numSlots r T)).image lab,
      (entryCells (fun τ t => h t τ) (labelPart r lab T ℓ)).card :=
  Finset.card_biUnion_le

/-- A step below `T` whose cell was last visited in a slot with a different label is an entry cell
of its label class. -/
theorem mem_allEntryCells {k r T : ℕ} {h : Fin k → ℕ → ℤ} {lab : ℕ → ℕ} (hr : 1 ≤ r)
    {t : Fin k} {τ σ : ℕ} (hτ : τ < T) (hlab : lab (σ / r) ≠ lab (τ / r))
    (hlast : IsLastVisit (h t) τ σ) : (t, τ) ∈ allEntryCells r T h lab := by
  refine Finset.mem_biUnion.mpr ⟨lab (τ / r),
    Finset.mem_image.mpr ⟨τ / r, Finset.mem_range.mpr (div_lt_numSlots hr hτ), rfl⟩, ?_⟩
  rw [mem_entryCells]
  simp only [labelPart]
  refine ⟨mem_slotSteps.mpr ⟨hτ, rfl⟩, σ, ?_, hlast⟩
  intro hσ
  exact hlab (mem_slotSteps.mp hσ).2

/-! ## Last visits in a nested excursion -/

/-- In a nested excursion, the cell read at fall time `c + (4Kr − j)` was last visited at rise time
`a + j`, for every `j < 4Kr`. -/
theorem excursion_isLastVisit {r K a c : ℕ} {z : ℤ} {hh : ℕ → ℤ}
    (E : NestedExcursion r K a c z hh) {j : ℕ} (hj : j < 4 * K * r) :
    IsLastVisit hh (c + (4 * K * r - j)) (a + j) := by
  have hsep : a + 7 * K * r ≤ c := E.separated
  have h47 : 4 * K * r ≤ 7 * K * r := Nat.mul_le_mul_right r (by omega)
  have hrise : hh (a + j) = z * r + (j : ℤ) := by
    rw [E.rise (a + j) (by omega) (by omega), show a + j - a = j by omega]
  have hfall : hh (c + (4 * K * r - j)) = (z + 4 * K) * r - ((4 * K * r - j : ℕ) : ℤ) := by
    rw [E.fall _ (by omega) (by omega), show c + (4 * K * r - j) - c = 4 * K * r - j by omega]
  have hcast : ((4 * K * r - j : ℕ) : ℤ) = 4 * K * r - j := by
    rw [Nat.cast_sub hj.le]; push_cast; ring
  have hjZ : (j : ℤ) < 4 * K * r := by exact_mod_cast hj
  refine ⟨by omega, by rw [hrise, hfall, hcast]; ring, ?_⟩
  intro ρ h1 h2
  rw [hfall, hcast]
  by_cases hρ1 : ρ ≤ a + 4 * K * r
  · rw [E.rise ρ (by omega) hρ1]
    have hlt : ((j : ℕ) : ℤ) < ((ρ - a : ℕ) : ℤ) := by exact_mod_cast (show j < ρ - a by omega)
    intro heq
    linarith
  · by_cases hρ2 : ρ ≤ c
    · have hm := E.middle ρ (by omega) hρ2
      intro heq
      linarith
    · rw [E.fall ρ (by omega) (by omega)]
      have hlt : ((ρ - c : ℕ) : ℤ) < ((4 * K * r - j : ℕ) : ℤ) := by
        exact_mod_cast (show ρ - c < 4 * K * r - j by omega)
      rw [hcast] at hlt
      intro heq
      linarith

/-! ## Two colourings of a vertex expander -/

/-- **Disagreeing pairs of two colourings of a vertex expander.** If `α, β : V → L` are such that
for every colour `l` at most half of the vertices have `α`-colour `l` or `β`-colour `l`, then at least
`η |V| / 2` ordered adjacent pairs `(a, b)` have `α a ≠ β b`. (These are the bichromatic edges of
the bipartite double cover coloured by `α` on one side and `β` on the other.) -/
theorem expanding_link_cut {V L : Type*} [Fintype V] [DecidableEq V] [DecidableEq L]
    (G : SimpleGraph V) [DecidableRel G.Adj] (eta : ℝ)
    (hexp : ∀ S : Finset V, 2 * S.card ≤ Fintype.card V →
      eta * S.card ≤ (outsideNeighbors G S).card)
    (α β : V → L)
    (hsmall : ∀ l, 2 * (Finset.univ.filter (fun x => α x = l ∨ β x = l)).card ≤
      Fintype.card V) :
    eta * Fintype.card V ≤ 2 * (((Finset.univ ×ˢ Finset.univ).filter
      (fun p : V × V => G.Adj p.1 p.2 ∧ α p.1 ≠ β p.2)).card : ℝ) := by
  set links := (Finset.univ ×ˢ Finset.univ).filter
      (fun p : V × V => G.Adj p.1 p.2 ∧ α p.1 ≠ β p.2) with hlinks
  by_cases heta : eta ≤ 0
  · have h1 : eta * Fintype.card V ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg heta (Nat.cast_nonneg _)
    have h2 : (0 : ℝ) ≤ 2 * (links.card : ℝ) := by positivity
    linarith
  rw [not_le] at heta
  let d1 : V → ℕ := fun x => ((G.neighborFinset x).filter (fun w => α x ≠ β w)).card
  let d2 : V → ℕ := fun x => ((G.neighborFinset x).filter (fun w => α w ≠ β x)).card
  -- each ordered pair is counted once from its first and once from its second vertex
  have hd1 : links.card = ∑ x, d1 x := by
    rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := Finset.univ)
      (fun p _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    have he : links.filter (fun p => p.1 = x) =
        ((G.neighborFinset x).filter (fun w => α x ≠ β w)).map
          ⟨fun w => (x, w), fun w w' hw => (Prod.mk.inj hw).2⟩ := by
      ext ⟨a, b⟩
      simp only [hlinks, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and,
        Finset.mem_map, SimpleGraph.mem_neighborFinset]
      constructor
      · rintro ⟨⟨hab, hne⟩, rfl⟩
        exact ⟨b, ⟨hab, hne⟩, rfl⟩
      · rintro ⟨w, ⟨hxw, hne⟩, hw⟩
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hw
        exact ⟨⟨hxw, hne⟩, rfl⟩
    rw [he, Finset.card_map]
  have hd2 : links.card = ∑ x, d2 x := by
    rw [Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (t := Finset.univ)
      (fun p _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    have he : links.filter (fun p => p.2 = x) =
        ((G.neighborFinset x).filter (fun w => α w ≠ β x)).map
          ⟨fun w => (w, x), fun w w' hw => (Prod.mk.inj hw).1⟩ := by
      ext ⟨a, b⟩
      simp only [hlinks, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and,
        Finset.mem_map, SimpleGraph.mem_neighborFinset]
      constructor
      · rintro ⟨⟨hab, hne⟩, rfl⟩
        exact ⟨a, ⟨hab.symm, hne⟩, rfl⟩
      · rintro ⟨w, ⟨hxw, hne⟩, hw⟩
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hw
        exact ⟨⟨hxw.symm, hne⟩, rfl⟩
    rw [he, Finset.card_map]
  -- the colours in use and the joint classes
  set labs : Finset L := Finset.univ.image α ∪ Finset.univ.image β with hlabs
  let A : L → Finset V := fun l => Finset.univ.filter (fun x => α x = l)
  let B : L → Finset V := fun l => Finset.univ.filter (fun x => β x = l)
  let U : L → Finset V := fun l => Finset.univ.filter (fun x => α x = l ∨ β x = l)
  have hAU : ∀ l, (A l).card ≤ (U l).card := fun l =>
    Finset.card_le_card (fun x hx => by
      simp only [A, U, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact Or.inl hx)
  -- the outside neighbours of a joint class are reached along disagreeing pairs
  have hbd : ∀ l, (outsideNeighbors G (U l)).card ≤
      ∑ x ∈ A l, d1 x + ∑ x ∈ B l, d2 x := by
    intro l
    have hsub : outsideNeighbors G (U l) ⊆
        (A l).biUnion (fun x => (G.neighborFinset x).filter (fun w => α x ≠ β w)) ∪
        (B l).biUnion (fun x => (G.neighborFinset x).filter (fun w => α w ≠ β x)) := by
      intro w hw
      simp only [outsideNeighbors, Finset.mem_sdiff, Finset.mem_biUnion] at hw
      obtain ⟨⟨x, hxU, hwx⟩, hwU⟩ := hw
      simp only [U, Finset.mem_filter, Finset.mem_univ, true_and, not_or] at hxU hwU
      rcases hxU with hx | hx
      · refine Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨x, ?_, ?_⟩)
        · simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]; exact hx
        · refine Finset.mem_filter.mpr ⟨hwx, ?_⟩
          rw [hx]; exact fun h => hwU.2 h.symm
      · refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨x, ?_, ?_⟩)
        · simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]; exact hx
        · refine Finset.mem_filter.mpr ⟨hwx, ?_⟩
          rw [hx]; exact hwU.1
    calc (outsideNeighbors G (U l)).card
        ≤ ((A l).biUnion (fun x => (G.neighborFinset x).filter (fun w => α x ≠ β w)) ∪
          (B l).biUnion (fun x => (G.neighborFinset x).filter (fun w => α w ≠ β x))).card :=
          Finset.card_le_card hsub
      _ ≤ _ := (Finset.card_union_le _ _).trans
          (Nat.add_le_add Finset.card_biUnion_le Finset.card_biUnion_le)
  -- fibrewise sums
  have hsumA : ∑ l ∈ labs, (A l).card = Fintype.card V := by
    rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := α) (t := labs)
      (fun x _ => Finset.mem_union_left _ (Finset.mem_image_of_mem α (Finset.mem_univ x)))]
  have hsum1 : ∑ l ∈ labs, ∑ x ∈ A l, d1 x = ∑ x, d1 x :=
    Finset.sum_fiberwise_of_maps_to
      (fun x _ => Finset.mem_union_left _ (Finset.mem_image_of_mem α (Finset.mem_univ x))) _
  have hsum2 : ∑ l ∈ labs, ∑ x ∈ B l, d2 x = ∑ x, d2 x :=
    Finset.sum_fiberwise_of_maps_to
      (fun x _ => Finset.mem_union_right _ (Finset.mem_image_of_mem β (Finset.mem_univ x))) _
  have hpoint : ∀ l, eta * (A l).card ≤ ((∑ x ∈ A l, d1 x + ∑ x ∈ B l, d2 x : ℕ) : ℝ) := by
    intro l
    have h1 : eta * (A l).card ≤ eta * (U l).card :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hAU l) heta.le
    have h2 := hexp (U l) (hsmall l)
    have h3 : ((outsideNeighbors G (U l)).card : ℝ) ≤
        ((∑ x ∈ A l, d1 x + ∑ x ∈ B l, d2 x : ℕ) : ℝ) := by exact_mod_cast hbd l
    linarith
  have htotal : ∑ l ∈ labs, (∑ x ∈ A l, d1 x + ∑ x ∈ B l, d2 x) = 2 * links.card := by
    rw [Finset.sum_add_distrib, hsum1, hsum2, ← hd1, ← hd2]; ring
  calc eta * Fintype.card V = ∑ l ∈ labs, eta * ((A l).card : ℝ) := by
        rw [← Finset.mul_sum]; congr 1; exact_mod_cast hsumA.symm
    _ ≤ ∑ l ∈ labs, ((∑ x ∈ A l, d1 x + ∑ x ∈ B l, d2 x : ℕ) : ℝ) :=
        Finset.sum_le_sum (fun l _ => hpoint l)
    _ = 2 * (links.card : ℝ) := by exact_mod_cast htotal

/-! ## The main theorem -/

theorem div_lt_div_of_add_le {a b r : ℕ} (hr : 1 ≤ r) (h : a + r ≤ b) : a / r < b / r := by
  have h1 : (a + r) / r = a / r + 1 := Nat.add_div_right a (by omega)
  have h2 : (a + r) / r ≤ b / r := Nat.div_le_div_right h
  omega

/-- The label of the slot (of length `r'`) that contains time `start x + o`. -/
noncomputable def colorAt {V : Type*} (start : V → ℕ) (lab : ℕ → ℕ) (r' o : ℕ) (x : V) : ℕ :=
  lab ((start x + o) / r')

/-- The rise offset of a link at offset `o`, with `R = K r`: `o − R` when the source of the edge
rises at offset `o` (`true`), and `5R − o` when it rises at the mirror offset `6R − o` (`false`). -/
def riseOffset (R o : ℕ) (b : Bool) : ℕ := cond b (o - R) (5 * R - o)

/-- In an excursion layout, the fall ramp of edge `e` reaches the cell `base e · r + j` at time
`closeTime e + (4Kr − j)`. -/
theorem fall_position {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {r K k T : ℕ} {h : Fin k → ℕ → ℤ}
    (D : ExcursionLayout G r K k T h) (e : G.edgeFinset) {j : ℕ} (hj : j < 4 * K * r) :
    h (D.page e) (D.closeTime e + (4 * K * r - j)) = D.base e * r + j := by
  have E := D.excursion e
  rw [show D.closeTime e = D.start (D.dst e) + K * r from rfl,
    E.fall _ (by omega) (by omega),
    show D.start (D.dst e) + K * r + (4 * K * r - j) - (D.start (D.dst e) + K * r) =
      4 * K * r - j by omega, Nat.cast_sub hj.le]
  push_cast
  ring

set_option maxHeartbeats 1000000 in
/-- **Excursion layouts satisfy the cell-accurate cut inequality**, with zero slack, for every slot
length `1 ≤ r' ≤ 7Kr`. The hypotheses are vertex expansion `η` of the graph, the stretch condition
`(2K − 1) η ≥ 1` (implied by the follow-up's `4 ≤ (4K − 1) η`), `2n ≤ |V|`, and `n b ≤ r G`. No idle
tapes, head-count condition or degree bound is needed. -/
theorem cellCutIneq_of_layout {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {r K k T : ℕ} {h : Fin k → ℕ → ℤ}
    (D : ExcursionLayout G r K k T h) (eta : ℝ)
    (hexp : ∀ S : Finset V, 2 * S.card ≤ Fintype.card V →
      eta * S.card ≤ (outsideNeighbors G S).card)
    (hK : 1 ≤ ((2 * K - 1 : ℕ) : ℝ) * eta)
    {n cellBits r' : ℕ} (hr' : 1 ≤ r') (hr'K : r' ≤ 7 * K * r)
    (hn : 2 * n ≤ Fintype.card V) (hrG : n * entryBits n ≤ r * cellBits) :
    CellCutIneq n cellBits r' T 0 0 h := by
  intro lab m hm
  simp only [Nat.mul_zero, Nat.zero_add]
  by_cases hlarge : n ≤ 2 * m
  · rw [Nat.sub_eq_zero_of_le hlarge, Nat.mul_zero, Nat.zero_mul]; exact Nat.zero_le _
  rw [not_le] at hlarge
  have hr := D.r_pos
  have hKpos := D.K_pos
  obtain ⟨R, hRdef⟩ : ∃ R, R = K * r := ⟨_, rfl⟩
  have hR : 0 < R := by rw [hRdef]; exact Nat.mul_pos hKpos hr
  have h4 : 4 * K * r = 4 * R := by rw [hRdef]; ring
  have h7 : 7 * K * r = 7 * R := by rw [hRdef]; ring
  have h2 : 2 * K * r = 2 * R := by rw [hRdef]; ring
  -- class sizes at one offset: different vertices give different slots
  have hclass : ∀ o', o' < 7 * R → ∀ ℓ,
      (Finset.univ.filter (fun x => colorAt D.start lab r' o' x = ℓ)).card ≤ m := by
    intro o' ho' ℓ
    refine le_trans ?_ (hm ℓ)
    refine Finset.card_le_card_of_injOn (fun x => (D.start x + o') / r') ?_ ?_
    · intro x hx
      have hx' := (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2
      refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hx'⟩)
      apply div_lt_numSlots hr'
      have := D.within x
      omega
    · intro x _ y _ hxy
      by_contra hne
      rcases D.separated x y hne with hs | hs
      · exact absurd hxy (ne_of_lt (div_lt_div_of_add_le hr' (by omega)))
      · exact absurd hxy (ne_of_gt (div_lt_div_of_add_le hr' (by omega)))
  -- joint class sizes at an offset pair
  have hsmall : ∀ o, R < o → o < 3 * R → ∀ ℓ,
      2 * (Finset.univ.filter (fun x => colorAt D.start lab r' o x = ℓ ∨
        colorAt D.start lab r' (6 * R - o) x = ℓ)).card ≤ Fintype.card V := by
    intro o ho1 ho2 ℓ
    rw [Finset.filter_or]
    have c1 := hclass o (by omega) ℓ
    have c2 := hclass (6 * R - o) (by omega) ℓ
    have cu := Finset.card_union_le
      (Finset.univ.filter (fun x => colorAt D.start lab r' o x = ℓ))
      (Finset.univ.filter (fun x => colorAt D.start lab r' (6 * R - o) x = ℓ))
    omega
  -- disagreeing ordered pairs, and the edge links that realize them
  let links : ℕ → Finset (V × V) := fun o => (Finset.univ ×ˢ Finset.univ).filter
    (fun p : V × V => G.Adj p.1 p.2 ∧
      colorAt D.start lab r' o p.1 ≠ colorAt D.start lab r' (6 * R - o) p.2)
  let elinks : ℕ → Finset (G.edgeFinset × Bool) := fun o => Finset.univ.filter
    (fun p => lab ((D.openTime p.1 + riseOffset R o p.2) / r') ≠
      lab ((D.closeTime p.1 + (4 * R - riseOffset R o p.2)) / r'))
  have hlinks : ∀ o, R < o → o < 3 * R → eta * Fintype.card V ≤ 2 * ((links o).card : ℝ) :=
    fun o ho1 ho2 => expanding_link_cut G eta hexp (colorAt D.start lab r' o)
      (colorAt D.start lab r' (6 * R - o)) (hsmall o ho1 ho2)
  have hle : ∀ o, R < o → o < 3 * R → (links o).card ≤ (elinks o).card := by
    intro o ho1 ho2
    refine le_trans (Finset.card_le_card ?_) (Finset.card_image_le (s := elinks o)
      (f := fun p => cond p.2 (D.src p.1, D.dst p.1) (D.dst p.1, D.src p.1)))
    rintro ⟨a, b⟩ hab
    simp only [links, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at hab
    obtain ⟨hadj, hne⟩ := hab
    let e : G.edgeFinset := ⟨s(a, b), by simpa using hadj⟩
    have hee : s(D.src e, D.dst e) = s(a, b) := D.edge_eq e
    rcases Sym2.eq_iff.mp hee with ⟨hs, hd⟩ | ⟨hs, hd⟩
    · refine Finset.mem_image.mpr ⟨(e, true), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · show lab ((D.openTime e + riseOffset R o true) / r') ≠
          lab ((D.closeTime e + (4 * R - riseOffset R o true)) / r')
        have e1 : D.openTime e + riseOffset R o true = D.start a + o := by
          rw [show D.openTime e = D.start (D.src e) + K * r from rfl, hs]
          simp only [riseOffset, Bool.cond_true]; omega
        have e2 : D.closeTime e + (4 * R - riseOffset R o true) = D.start b + (6 * R - o) := by
          rw [show D.closeTime e = D.start (D.dst e) + K * r from rfl, hd]
          simp only [riseOffset, Bool.cond_true]; omega
        rw [e1, e2]; exact hne
      · show (D.src e, D.dst e) = (a, b)
        rw [hs, hd]
    · refine Finset.mem_image.mpr ⟨(e, false), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · show lab ((D.openTime e + riseOffset R o false) / r') ≠
          lab ((D.closeTime e + (4 * R - riseOffset R o false)) / r')
        have e1 : D.openTime e + riseOffset R o false = D.start b + (6 * R - o) := by
          rw [show D.openTime e = D.start (D.src e) + K * r from rfl, hs]
          simp only [riseOffset, Bool.cond_false]; omega
        have e2 : D.closeTime e + (4 * R - riseOffset R o false) = D.start a + o := by
          rw [show D.closeTime e = D.start (D.dst e) + K * r from rfl, hd]
          simp only [riseOffset, Bool.cond_false]; omega
        rw [e1, e2]; exact fun h' => hne h'.symm
      · show (D.dst e, D.src e) = (a, b)
        rw [hs, hd]
  -- all edge links, injected into the entry cells
  have hro4 : ∀ o, R < o → o < 3 * R → ∀ b : Bool, riseOffset R o b < 4 * R := by
    intro o ho1 ho2 b
    cases b <;> simp only [riseOffset, Bool.cond_true, Bool.cond_false] <;> omega
  have hro2 : ∀ o, R < o → o < 3 * R →
      riseOffset R o true < 2 * R ∧ 2 * R < riseOffset R o false := by
    intro o ho1 ho2
    simp only [riseOffset, Bool.cond_true, Bool.cond_false]
    omega
  let O := Finset.Ico (R + 1) (3 * R)
  let S := O.sigma elinks
  let Φ : (Σ _ : ℕ, G.edgeFinset × Bool) → Fin k × ℕ := fun x =>
    (D.page x.2.1, D.closeTime x.2.1 + (4 * R - riseOffset R x.1 x.2.2))
  have hΦmem : ∀ x ∈ S, Φ x ∈ allEntryCells r' T h lab := by
    rintro ⟨o, e, b⟩ hx
    have ho : o ∈ O := (Finset.mem_sigma.mp hx).1
    have hel : (e, b) ∈ elinks o := (Finset.mem_sigma.mp hx).2
    have hoI := Finset.mem_Ico.mp ho
    simp only [elinks, Finset.mem_filter, Finset.mem_univ, true_and] at hel
    have hj4 := hro4 o (by omega) hoI.2 b
    have hlast := excursion_isLastVisit (D.excursion e) (j := riseOffset R o b)
      (by rw [h4]; exact hj4)
    rw [h4] at hlast
    have hwin := D.within (D.dst e)
    refine mem_allEntryCells (σ := D.openTime e + riseOffset R o b) hr' ?_ hel hlast
    show D.start (D.dst e) + K * r + (4 * R - riseOffset R o b) < T
    omega
  have hΦinj : Set.InjOn Φ S := by
    rintro ⟨o, e, b⟩ hx ⟨o', e', b'⟩ hy hxy
    have ho : o ∈ O := (Finset.mem_sigma.mp (Finset.mem_coe.mp hx)).1
    have ho' : o' ∈ O := (Finset.mem_sigma.mp (Finset.mem_coe.mp hy)).1
    have hoI := Finset.mem_Ico.mp ho
    have hoI' := Finset.mem_Ico.mp ho'
    simp only [Φ, Prod.mk.injEq] at hxy
    obtain ⟨hpage, htime⟩ := hxy
    have hj := hro4 o (by omega) hoI.2 b
    have hj' := hro4 o' (by omega) hoI'.2 b'
    have hee : e = e' := by
      by_contra hne
      have p1 := fall_position D e (j := riseOffset R o b) (by rw [h4]; exact hj)
      have p2 := fall_position D e' (j := riseOffset R o' b') (by rw [h4]; exact hj')
      rw [h4] at p1 p2
      rw [← hpage, ← htime, p1] at p2
      have hjZ : ((riseOffset R o b : ℕ) : ℤ) < 4 * K * r := by
        have : riseOffset R o b < 4 * K * r := by rw [h4]; exact hj
        exact_mod_cast this
      have hjZ' : ((riseOffset R o' b' : ℕ) : ℤ) < 4 * K * r := by
        have : riseOffset R o' b' < 4 * K * r := by rw [h4]; exact hj'
        exact_mod_cast this
      have hr0 : (0 : ℤ) ≤ r := Nat.cast_nonneg _
      rcases D.slabs e e' hne hpage with hs | hs
      · have := mul_le_mul_of_nonneg_right hs hr0
        have h0 : (0 : ℤ) ≤ ((riseOffset R o' b' : ℕ) : ℤ) := Nat.cast_nonneg _
        linarith
      · have := mul_le_mul_of_nonneg_right hs hr0
        have h0 : (0 : ℤ) ≤ ((riseOffset R o b : ℕ) : ℤ) := Nat.cast_nonneg _
        linarith
    subst hee
    have hjj : riseOffset R o b = riseOffset R o' b' := by omega
    have hbb : b = b' := by
      have q1 := hro2 o (by omega) hoI.2
      have q2 := hro2 o' (by omega) hoI'.2
      cases b <;> cases b' <;> first | rfl | omega
    subst hbb
    have hoo : o = o' := by
      cases b <;> simp only [riseOffset, Bool.cond_true, Bool.cond_false] at hjj <;> omega
    subst hoo
    rfl
  have hSle : S.card ≤ ∑ ℓ ∈ (Finset.range (numSlots r' T)).image lab,
      (entryCells (fun τ t => h t τ) (labelPart r' lab T ℓ)).card := by
    calc S.card = (S.image Φ).card := (Finset.card_image_of_injOn hΦinj).symm
      _ ≤ (allEntryCells r' T h lab).card := Finset.card_le_card (fun y hy => by
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
          exact hΦmem x hx)
      _ ≤ _ := card_allEntryCells_le r' T h lab
  -- counting
  have hcardS : S.card = ∑ o ∈ O, (elinks o).card := Finset.card_sigma _ _
  have hO : O.card = 2 * R - 1 := by simp only [O, Nat.card_Ico]; omega
  have heta : 0 < eta := by
    by_contra hneg
    rw [not_lt] at hneg
    have : ((2 * K - 1 : ℕ) : ℝ) * eta ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hneg
    linarith
  have hsumR : (O.card : ℝ) * (eta * Fintype.card V) ≤ 2 * (S.card : ℝ) := by
    have s1 : ∑ _o ∈ O, eta * (Fintype.card V : ℝ) = (O.card : ℝ) * (eta * Fintype.card V) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    have s2 : ∑ o ∈ O, 2 * ((elinks o).card : ℝ) = 2 * (S.card : ℝ) := by
      rw [← Finset.mul_sum, hcardS]; push_cast; ring
    have s3 : ∑ _o ∈ O, eta * (Fintype.card V : ℝ) ≤ ∑ o ∈ O, 2 * ((elinks o).card : ℝ) :=
      Finset.sum_le_sum (fun o ho => by
        have hoI := Finset.mem_Ico.mp ho
        have l1 := hlinks o (by omega) hoI.2
        have l2 : ((links o).card : ℝ) ≤ ((elinks o).card : ℝ) := by
          exact_mod_cast hle o (by omega) hoI.2
        linarith)
    linarith
  have hAr : ((2 * K - 1 : ℕ) : ℝ) * r ≤ (O.card : ℝ) := by
    rw [hO]
    have : (2 * K - 1) * r ≤ 2 * R - 1 := by
      rw [Nat.sub_mul, one_mul]
      omega
    exact_mod_cast this
  have hVn : (2 * n : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
  have hnr : (n : ℝ) * r ≤ S.card := by
    have k1 : ((2 * K - 1 : ℕ) : ℝ) * r * (eta * (2 * n)) ≤
        (O.card : ℝ) * (eta * Fintype.card V) :=
      mul_le_mul hAr (mul_le_mul_of_nonneg_left hVn heta.le) (by positivity) (Nat.cast_nonneg _)
    have k2 : ((2 * K - 1 : ℕ) : ℝ) * r * (eta * (2 * n)) =
        2 * ((n : ℝ) * r) * (((2 * K - 1 : ℕ) : ℝ) * eta) := by ring
    have k3 : 2 * ((n : ℝ) * r) ≤ 2 * ((n : ℝ) * r) * (((2 * K - 1 : ℕ) : ℝ) * eta) :=
      le_mul_of_one_le_right (by positivity) hK
    linarith
  have hnrN : n * r ≤ S.card := by exact_mod_cast hnr
  calc (n - labelChanges lab (numSlots r' T)) * (n - 2 * m) * entryBits n
      ≤ n * n * entryBits n :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _))
    _ = n * (n * entryBits n) := by ring
    _ ≤ n * (r * cellBits) := Nat.mul_le_mul_left n hrG
    _ = (n * r) * cellBits := by ring
    _ ≤ S.card * cellBits := Nat.mul_le_mul_right _ hnrN
    _ ≤ (∑ ℓ ∈ (Finset.range (numSlots r' T)).image lab,
          (entryCells (fun τ t => h t τ) (labelPart r' lab T ℓ)).card) * cellBits :=
        Nat.mul_le_mul_right _ hSle
    _ = _ := by ring

/-! ## From the cell-accurate inequality to the first paper's cut inequality -/

/-- Entry cells split over the tapes (the walk version of `entryCells_slotSteps_card`). -/
theorem entryCells_slotSteps_card_walk {k : ℕ} (h : Fin k → ℕ → ℤ) (r : ℕ) (U : Set ℕ) (T : ℕ) :
    (entryCells (fun τ t => h t τ) (slotSteps r U T)).card =
      ∑ t : Fin k, (entryTimes r (h t) U T).card := by
  have heq : entryCells (fun τ t => h t τ) (slotSteps r U T) =
      Finset.univ.biUnion (fun t => (entryTimes r (h t) U T).image (fun τ => (t, τ))) := by
    ext ⟨t, τ⟩
    simp only [mem_entryCells, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image,
      mem_entryTimes, mem_slotSteps, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨hτT, hτU⟩, σ, hσJ, hσ⟩
      refine ⟨t, τ, ⟨hτT, hτU, σ, ?_, hσ⟩, rfl, rfl⟩
      intro hσU; exact hσJ ⟨lt_trans hσ.1 hτT, hσU⟩
    · rintro ⟨t', τ', ⟨hτT, hτU, σ, hσU, hσ⟩, rfl, rfl⟩
      exact ⟨⟨hτT, hτU⟩, σ, fun h => hσU h.2, hσ⟩
  rw [heq, Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro t _
    exact Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).2)
  · intro t _ t' _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro p hp hp'
    simp only [Finset.mem_image] at hp hp'
    obtain ⟨τ, -, rfl⟩ := hp
    obtain ⟨τ', -, he⟩ := hp'
    exact hne (Prod.mk.inj he).1.symm

/-- **The first paper's charging step for unit-step walks**: the entry cells of the label classes
number at most `r (3 k M_b + Σ χ)` (the walk version of the second half of
`sum_entry_labelPart_le`, with pair residency). -/
theorem sum_entryCells_labelPart_le {k : ℕ} {h : Fin k → ℕ → ℤ} {T r : ℕ} (hr : 1 ≤ r)
    (hunit : ∀ t, UnitSteps (h t)) (lab : ℕ → ℕ) (s : Finset ℕ) :
    ∑ ℓ ∈ s, (entryCells (fun τ t => h t τ) (labelPart r lab T ℓ)).card ≤
      r * (3 * k * labelChanges lab (numSlots r T) +
        ∑ t : Fin k, (crossChords (pairRes r (h t) T) lab (numSlots r T)).card) := by
  set N := numSlots r T
  calc ∑ ℓ ∈ s, (entryCells (fun τ t => h t τ) (labelPart r lab T ℓ)).card
      ≤ ∑ ℓ ∈ s, ∑ t : Fin k, r * ((chordsInto (pairRes r (h t) T) {y | lab y = ℓ} N).card +
          3 * (memBoundaries {y | lab y = ℓ} N).card) := by
        refine Finset.sum_le_sum fun ℓ _ => ?_
        rw [labelPart, entryCells_slotSteps_card_walk]
        exact Finset.sum_le_sum fun t _ =>
          entryTimes_card_le hr (pairRes_admissible (hunit t) hr T) _
    _ = r * (∑ t : Fin k, ∑ ℓ ∈ s, (chordsInto (pairRes r (h t) T) {y | lab y = ℓ} N).card +
          3 * k * ∑ ℓ ∈ s, (memBoundaries {y | lab y = ℓ} N).card) := by
        simp only [Nat.mul_add, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, smul_eq_mul]
        rw [Finset.sum_comm]; ring
    _ ≤ r * (∑ t : Fin k, (crossChords (pairRes r (h t) T) lab N).card +
          3 * k * labelChanges lab N) :=
        Nat.mul_le_mul_left _ (Nat.add_le_add
          (Finset.sum_le_sum fun t _ => sum_chordsInto_le _ lab N s)
          (Nat.mul_le_mul_left _ (sum_memBoundaries_le lab N s)))
    _ = _ := by ring

/-- **For unit-step walks the cell-accurate inequality implies the first paper's cut inequality**
(with the same parameters). -/
theorem cutIneq_of_cellCutIneq {k n G r T D s : ℕ} {h : Fin k → ℕ → ℤ} (hr : 1 ≤ r)
    (hunit : ∀ t, UnitSteps (h t)) (hc : CellCutIneq n G r T D s h) : CutIneq n G r T D s h := by
  intro lab m hm
  refine (hc lab m hm).trans (Nat.add_le_add_left ?_ _)
  calc G * ∑ ℓ ∈ (Finset.range (numSlots r T)).image lab,
        (entryCells (fun τ t => h t τ) (labelPart r lab T ℓ)).card
      ≤ G * (r * (3 * k * labelChanges lab (numSlots r T) +
          ∑ t, (crossChords (pairRes r (h t) T) lab (numSlots r T)).card)) :=
        Nat.mul_le_mul_left _ (sum_entryCells_labelPart_le hr hunit lab _)
    _ = _ := by ring

/-- **Excursion layouts of unit-step walks satisfy the first paper's zero-slack cut inequality**
at every slot length `1 ≤ r' ≤ 7Kr`, for every number `k` of tapes: no hypothesis relating `k`, the
expansion and the page count is needed, so no idle tapes are needed to inflate the term `3 k M_b`
(which the charging step `sum_entryCells_labelPart_le` does use). -/
theorem cutIneq_of_layout {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {r K k T : ℕ} {h : Fin k → ℕ → ℤ}
    (D : ExcursionLayout G r K k T h) (hunit : ∀ t, UnitSteps (h t)) (eta : ℝ)
    (hexp : ∀ S : Finset V, 2 * S.card ≤ Fintype.card V →
      eta * S.card ≤ (outsideNeighbors G S).card)
    (hK : 1 ≤ ((2 * K - 1 : ℕ) : ℝ) * eta)
    {n cellBits r' : ℕ} (hr' : 1 ≤ r') (hr'K : r' ≤ 7 * K * r)
    (hn : 2 * n ≤ Fintype.card V) (hrG : n * entryBits n ≤ r * cellBits) :
    CutIneq n cellBits r' T 0 0 h :=
  cutIneq_of_cellCutIneq hr' hunit (cellCutIneq_of_layout D eta hexp hK hr' hr'K hn hrG)

/-- The follow-up's stretch condition `4 ≤ (4K − 1) η` implies the stretch condition
`1 ≤ (2K − 1) η` used here. -/
theorem stretch_of_followup {K : ℕ} {eta : ℝ} (hKpos : 0 < K)
    (hK : 4 ≤ ((4 * K - 1 : ℕ) : ℝ) * eta) : 1 ≤ ((2 * K - 1 : ℕ) : ℝ) * eta := by
  have h4 : ((4 * K - 1 : ℕ) : ℝ) = 4 * (K : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have h2 : ((2 * K - 1 : ℕ) : ℝ) = 2 * (K : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [h4] at hK
  rw [h2]
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hKpos
  have heta : 0 < eta := by
    by_contra hneg
    rw [not_lt] at hneg
    have : (4 * (K : ℝ) - 1) * eta ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hneg
    linarith
  nlinarith

end PaddingMemo
