import TransposeFollowup.ExcursionChordCount
import TransposeFollowup.RepairedGadgetLabels

/-! A finite geometric interface, with all construction obligations explicit.
The layout supplies actual nested path windows and disjoint spatial slabs on
each page. From these we derive a globally injective family of counted chords;
no chord count or expansion-to-CutIneq implication is assumed in the interface.
-/

namespace TransposeFollowup

open Classical
open Transpose.Tape Transpose.Tape.Impl
open scoped BigOperators
set_option autoImplicit false

theorem floor_le_numSlots {r a c : ℕ} (hr : 0 < r) (hac : a ≤ c) :
    a / r ≤ numSlots r c := by
  have hceil : c ≤ numSlots r c * r := by
    have he := not_congr (numSlots_spec (r := r) (T := c) (y := numSlots r c) hr)
    simpa only [lt_self_iff_false, not_false_eq_true, not_lt, true_iff] using he
  have hfloor := Nat.div_mul_le_self a r
  by_contra hn
  have hm := Nat.mul_le_mul_right r (show numSlots r c + 1 ≤ a / r by omega)
  nlinarith

structure ExcursionLayout {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r K k T : ℕ) (h : Fin k → ℕ → ℤ) where
  r_pos : 0 < r
  K_pos : 0 < K
  start : V → ℕ
  separated : ∀ i j, i ≠ j → start i + 7 * K * r ≤ start j ∨ start j + 7 * K * r ≤ start i
  within : ∀ i, start i + 7 * K * r ≤ T
  src : G.edgeFinset → V
  dst : G.edgeFinset → V
  edge_eq : ∀ e, s(src e, dst e) = e.val
  page : G.edgeFinset → Fin k
  base : G.edgeFinset → ℤ
  excursion : ∀ e, NestedExcursion r K (start (src e) + K * r) (start (dst e) + K * r)
    (base e) (h (page e))
  slabs : ∀ e f, e ≠ f → page e = page f →
    base e + 4 * K ≤ base f ∨ base f + 4 * K ≤ base e

namespace ExcursionLayout

variable {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {r K k T : ℕ} {h : Fin k → ℕ → ℤ}
    (D : ExcursionLayout G r K k T h)

def lo (i : V) : ℕ := numSlots r (D.start i)
def hi (i : V) : ℕ := (D.start i + 7 * K * r) / r
def openTime (e : G.edgeFinset) : ℕ := D.start (D.src e) + K * r
def closeTime (e : G.edgeFinset) : ℕ := D.start (D.dst e) + K * r

noncomputable def bad (lab : ℕ → ℕ) : Finset V := badWindows lab D.lo D.hi
noncomputable def labels (lab : ℕ → ℕ) : V → ℕ ⊕ V := repairedLabel lab D.lo D.hi
noncomputable def goodEdges (lab : ℕ → ℕ) : Finset (Sym2 V) :=
  goodCrossEdges G (D.labels lab) (D.bad lab)

theorem windows_separated : ∀ i j, i ≠ j → D.hi i ≤ D.lo j ∨ D.hi j ≤ D.lo i := by
  intro i j hij
  rcases D.separated i j hij with he | he
  · exact Or.inl (floor_le_numSlots D.r_pos he)
  · exact Or.inr (floor_le_numSlots D.r_pos he)

theorem windows_within (i : V) : D.hi i ≤ numSlots r T :=
  floor_le_numSlots D.r_pos (D.within i)

theorem window_length (i : V) : 7 * K - 1 ≤ D.hi i - D.lo i := by
  simpa only [fullSlots, Nat.card_Ico, hi, lo] using
    fullSlots_card_lower (a := D.start i) (L := 7 * K) D.r_pos

theorem bad_count (lab : ℕ → ℕ) : (D.bad lab).card ≤ labelChanges lab (numSlots r T) :=
  badWindows_card_le lab D.lo D.hi _ D.windows_separated D.windows_within

theorem labels_small (lab : ℕ → ℕ) (m : ℕ) (hv : 2 ≤ Fintype.card V)
    (hmv : m ≤ Fintype.card V)
    (hm : ∀ ell, ((Finset.range (numSlots r T)).filter (fun s => lab s = ell)).card ≤ m) :
    ∀ l, 2 * (labelFiber (D.labels lab) l).card ≤ Fintype.card V := by
  exact repairedLabel_small lab D.lo D.hi _ (7 * K - 1) m D.windows_separated
    D.windows_within D.window_length (by have := D.K_pos; omega) hv hmv hm

theorem goodEdges_subset (lab : ℕ → ℕ) : D.goodEdges lab ⊆ G.edgeFinset := by
  intro e he
  have hm := (Finset.mem_sdiff.mp he).1
  apply SimpleGraph.edgeFinset_mono (show crossingGraph G (D.labels lab) ≤ G from fun _ _ h => h.1)
  exact hm

theorem good_edge_properties (lab : ℕ → ℕ) (e : G.edgeFinset) (he : e.val ∈ D.goodEdges lab) :
    D.labels lab (D.src e) ≠ D.labels lab (D.dst e) ∧
      D.src e ∉ D.bad lab ∧ D.dst e ∉ D.bad lab := by
  rw [← D.edge_eq e] at he
  exact ((mem_goodCrossEdges G (D.labels lab) (D.bad lab) _ _).mp he).2

theorem close_before_end (e : G.edgeFinset) : D.closeTime e + 4 * K * r < T := by
  have he := D.within (D.dst e)
  have hp := Nat.mul_pos D.K_pos D.r_pos
  dsimp [closeTime]
  nlinarith

def sourceSlot (e : G.edgeFinset) (j : Fin (4 * K - 1)) : ℕ :=
  (D.openTime e + (j.val + 2) * r - 1) / r

def targetSlot (e : G.edgeFinset) (j : Fin (4 * K - 1)) : ℕ :=
  (D.closeTime e + (4 * K - j.val - 1) * r + 1) / r

theorem sourceSlot_mem (e : G.edgeFinset) (j : Fin (4 * K - 1)) :
    D.sourceSlot e j ∈ Finset.Ico (D.lo (D.src e)) (D.hi (D.src e)) := by
  change D.sourceSlot e j ∈ fullSlots r (D.start (D.src e)) (D.start (D.src e) + 7 * K * r)
  apply (mem_fullSlots D.r_pos).mpr
  have he := (D.excursion e).source_slot_contained (j := j.val) (by have := j.isLt; omega)
  change D.openTime e ≤ D.sourceSlot e j * r ∧
    (D.sourceSlot e j + 1) * r ≤ D.openTime e + 6 * K * r at he
  dsimp [openTime] at he
  constructor <;> nlinarith

theorem targetSlot_mem (e : G.edgeFinset) (j : Fin (4 * K - 1)) :
    D.targetSlot e j ∈ Finset.Ico (D.lo (D.dst e)) (D.hi (D.dst e)) := by
  change D.targetSlot e j ∈ fullSlots r (D.start (D.dst e)) (D.start (D.dst e) + 7 * K * r)
  apply (mem_fullSlots D.r_pos).mpr
  have he := (D.excursion e).target_slot_contained (j := j.val) (by have := j.isLt; omega)
  change D.closeTime e ≤ D.targetSlot e j * r ∧
    (D.targetSlot e j + 1) * r ≤ D.closeTime e + 6 * K * r at he
  dsimp [closeTime] at he
  constructor <;> nlinarith

theorem endpoint_labels_differ (lab : ℕ → ℕ) (e : G.edgeFinset)
    (he : e.val ∈ D.goodEdges lab) (j : Fin (4 * K - 1)) :
    lab (D.sourceSlot e j) ≠ lab (D.targetSlot e j) := by
  obtain ⟨hne, hs, ht⟩ := D.good_edge_properties lab e he
  have hsl := good_window_label_eq lab D.lo D.hi hs (D.sourceSlot_mem e j)
  have htl := good_window_label_eq lab D.lo D.hi ht (D.targetSlot_mem e j)
  intro hl
  apply hne
  change repairedLabel lab D.lo D.hi (D.src e) = repairedLabel lab D.lo D.hi (D.dst e)
  rw [repairedLabel_good lab D.lo D.hi hs, repairedLabel_good lab D.lo D.hi ht]
  exact congrArg Sum.inl (hsl.symm.trans (hl.trans htl))

/-- Spatial slab separation, with a page tag, makes all selected addresses
distinct globally. Target-slot coincidences therefore cannot double-count. -/
theorem address_injective : Function.Injective
    (fun p : G.edgeFinset × Fin (4 * K - 1) => (D.page p.1, D.base p.1 + (p.2.val : ℤ))) := by
  rintro ⟨e, i⟩ ⟨f, j⟩ he
  have hp := congrArg Prod.fst he
  have hb := congrArg Prod.snd he
  change D.page e = D.page f at hp
  change D.base e + (i.val : ℤ) = D.base f + (j.val : ℤ) at hb
  have hij := i.isLt
  have hjj := j.isLt
  have hef : e = f := by
    by_contra hn
    rcases D.slabs e f hn hp with hsep | hsep <;> omega
  subst f
  have hijEq : i = j := by
    apply Fin.ext
    have heval : (i.val : ℤ) = (j.val : ℤ) := add_left_cancel hb
    exact_mod_cast heval
  subst j
  rfl

/-- Count all good edge slabs in the literal imported crossing-chord sets. -/
theorem global_chord_count (lab : ℕ → ℕ) :
    (4 * K - 1) * (D.goodEdges lab).card ≤
      ∑ t : Fin k, (crossChords (pairRes r (h t) T) lab (numSlots r T)).card := by
  let edge : D.goodEdges lab → G.edgeFinset := fun e => ⟨e.val, D.goodEdges_subset lab e.property⟩
  let code : (D.goodEdges lab) × Fin (4 * K - 1) →
      Σ t : Fin k, crossChords (pairRes r (h t) T) lab (numSlots r T) := fun p =>
    ⟨D.page (edge p.1), ⟨(D.targetSlot (edge p.1) p.2, D.base (edge p.1) + p.2.val), by
      have hj : p.2.val + 2 ≤ 4 * K := by have := p.2.isLt; omega
      have hc := (D.excursion (edge p.1)).isChord hj (D.close_before_end (edge p.1))
      apply mem_crossChords.mpr
      refine ⟨?_, hc.2.2.1, D.sourceSlot (edge p.1) p.2,
        D.endpoint_labels_differ lab _ p.1.property p.2, hc⟩
      apply div_lt_numSlots D.r_pos
      exact lt_of_le_of_lt ((D.excursion (edge p.1)).return_time_le hj) (D.close_before_end _)⟩⟩
  have hinj : Function.Injective code := by
    intro p q he
    have hp := congrArg Sigma.fst he
    have hb := congrArg (fun s : Σ t : Fin k, crossChords (pairRes r (h t) T) lab (numSlots r T) =>
      s.2.val.2) he
    have haddr : (D.page (edge p.1), D.base (edge p.1) + (p.2.val : ℤ)) =
        (D.page (edge q.1), D.base (edge q.1) + (q.2.val : ℤ)) := Prod.ext hp hb
    have heq : (edge p.1, p.2) = (edge q.1, q.2) := D.address_injective haddr
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg (fun p : G.edgeFinset × Fin (4 * K - 1) => p.1.val) heq
    · exact congrArg (fun s : G.edgeFinset × Fin (4 * K - 1) => s.2) heq
  have hc := Fintype.card_le_of_injective code hinj
  simpa only [Fintype.card_prod, Fintype.card_fin, Fintype.card_sigma, Fintype.card_coe,
    Nat.mul_comm] using hc

end ExcursionLayout
end TransposeFollowup
