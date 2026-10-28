import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.List.ChainOfFn
import LeanMachine.PeriodicPhases

/-!
# Thin interval overlap graphs

Triangle-free overlap graphs of nonempty half-open intervals are forests.
Their nonleaf intervals have strictly ordered endpoints, and an edge between
nonleaves joins consecutive members of that order. These facts use only the
interval representation, not a particular two-coloring or tape geometry.
-/

namespace LeanMachine.ThinIntervals

open Classical Finset SimpleGraph

variable {V : Type*}

/-- Intervals are `(left v, right v]`; the overlap test also works for `[left,right)`. -/
structure Model (V : Type*) where
  left : V → ℕ
  right : V → ℕ
  nonempty : ∀ v, left v < right v

namespace Model

variable (I : Model V)

def graph : SimpleGraph V where
  Adj a b := a ≠ b ∧ I.left a < I.right b ∧ I.left b < I.right a
  symm := ⟨by rintro a b ⟨h, h₁, h₂⟩; exact ⟨Ne.symm h, h₂, h₁⟩⟩
  loopless := ⟨by intro a h; exact h.1 rfl⟩

def Thin : Prop := ∀ ⦃a b c⦄, I.graph.Adj a b → I.graph.Adj b c →
  I.graph.Adj a c → False

/-- A nonleaf has two distinct neighbors. Isolated vertices are not nonleaves. -/
def Nonleaf (a : V) : Prop := ∃ b c, I.graph.Adj a b ∧ I.graph.Adj a c ∧ b ≠ c

variable {I}

theorem isAcyclic (hI : I.Thin) : I.graph.IsAcyclic := by
  intro v p hp
  obtain ⟨a, ha, hmax⟩ := p.support.toFinset.exists_max_image I.left
    ⟨v, List.mem_toFinset.mpr p.start_mem_support⟩
  have ha' := List.mem_toFinset.mp ha
  let q := p.rotate a ha'
  have hq : q.IsCycle := hp.rotate ha'
  have hs := q.adj_snd hq.not_nil
  have ht := q.adj_penultimate hq.not_nil
  have hsl : I.left q.snd ≤ I.left a := hmax _ <| List.mem_toFinset.mpr <|
    (p.mem_support_rotate_iff a ha').mp (List.mem_of_mem_tail (q.snd_mem_tail_support hq.not_nil))
  have htl : I.left q.penultimate ≤ I.left a := hmax _ <| List.mem_toFinset.mpr <|
    (p.mem_support_rotate_iff a ha').mp
      (List.mem_of_mem_dropLast (q.penultimate_mem_dropLast_support hq.not_nil))
  exact hI hs ⟨hq.snd_ne_penultimate, hsl.trans_lt ht.2.2, htl.trans_lt hs.2.1⟩ ht.symm

/-- A contained interval can have no neighbor other than its container. -/
theorem eq_container_of_adj (hI : I.Thin) {a b c : V} (hab : a ≠ b)
    (hl : I.left a ≤ I.left b) (hr : I.right b ≤ I.right a)
    (hbc : I.graph.Adj b c) : c = a := by
  by_contra hca
  have hab' : I.graph.Adj a b :=
    ⟨hab, hl.trans_lt (I.nonempty b), (I.nonempty b).trans_le hr⟩
  exact hI hab' hbc ⟨Ne.symm hca, hl.trans_lt hbc.2.1, hbc.2.2.trans_le hr⟩

theorem not_nonleaf_of_contained (hI : I.Thin) {a b : V} (hab : a ≠ b)
    (hl : I.left a ≤ I.left b) (hr : I.right b ≤ I.right a) : ¬ I.Nonleaf b := by
  rintro ⟨c, d, hc, hd, hcd⟩
  exact hcd ((eq_container_of_adj hI hab hl hr hc).trans
    (eq_container_of_adj hI hab hl hr hd).symm)

/-- Nonleaf intervals have distinct left endpoints. -/
theorem nonleaf_left_injective (hI : I.Thin) {a b : V}
    (ha : I.Nonleaf a) (hb : I.Nonleaf b) (he : I.left a = I.left b) : a = b := by
  by_contra hn
  rcases le_total (I.right a) (I.right b) with hr | hr
  · exact not_nonleaf_of_contained hI (Ne.symm hn) he.ge hr ha
  · exact not_nonleaf_of_contained hI hn he.le hr hb

/-- The right endpoints of nonleaves increase strictly with their left endpoints. -/
theorem nonleaf_right_strict (hI : I.Thin) {a b : V}
    (hb : I.Nonleaf b) (hl : I.left a < I.left b) : I.right a < I.right b := by
  by_contra hr
  exact not_nonleaf_of_contained hI (by rintro rfl; omega) hl.le (by omega) hb

/-- An edge between nonleaves skips no nonleaf in the left-endpoint order. -/
theorem no_nonleaf_between (hI : I.Thin) {a b c : V} (hab : I.graph.Adj a b)
    (hc : I.Nonleaf c) (hac : I.left a < I.left c) (hcb : I.left c < I.left b) : False := by
  have hr := nonleaf_right_strict hI hc hac
  exact hI
    (show I.graph.Adj a c from ⟨by rintro rfl; omega,
      (I.nonempty a).trans hr, hcb.trans hab.2.2⟩)
    (show I.graph.Adj c b from ⟨by rintro rfl; omega,
      hcb.trans (I.nonempty b), hab.2.2.trans hr⟩)
    hab

/-- Every internal vertex of a simple path is a nonleaf of the original graph. -/
theorem nonleaf_or_endpoint {a b c : V} {p : I.graph.Walk a b} (hp : p.IsPath)
    (hc : c ∈ p.support) : I.Nonleaf c ∨ c = a ∨ c = b := by
  obtain ⟨i, hi, hib⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hc
  subst c
  by_cases h0 : i = 0
  · subst i; simp
  by_cases hn : i = p.length
  · subst i; simp
  left
  refine ⟨p.getVert (i - 1), p.getVert (i + 1), ?_, p.adj_getVert_succ (by omega), ?_⟩
  · have h := (p.adj_getVert_succ (show i - 1 < p.length by omega)).symm
    simpa only [Nat.sub_add_cancel (show 1 ≤ i by omega)] using h
  · intro he
    have := hp.getVert_injOn (show i - 1 ≤ p.length by omega)
      (show i + 1 ≤ p.length by omega) he
    omega

theorem nonleaf_getVert {a b : V} {p : I.graph.Walk a b} (hp : p.IsPath)
    {i : ℕ} (hi : 0 < i) (hn : i < p.length) : I.Nonleaf (p.getVert i) := by
  rcases nonleaf_or_endpoint hp (p.getVert_mem_support i) with h | h | h
  · exact h
  · have := (hp.getVert_eq_start_iff hn.le).mp h; omega
  · have := (hp.getVert_eq_end_iff hn.le).mp h; omega

/-- Deleting original leaves never disconnects two original nonleaves. -/
theorem nonleaf_reachable {a b : V} (ha : I.Nonleaf a) (hb : I.Nonleaf b)
    (hab : I.graph.Reachable a b) :
    (I.graph.induce I.Nonleaf).Reachable ⟨a, ha⟩ ⟨b, hb⟩ := by
  apply hab.elim_path
  rintro ⟨p, hp⟩
  refine ⟨p.induce I.Nonleaf (fun c hc => ?_)⟩
  rcases nonleaf_or_endpoint hp hc with h | rfl | rfl
  · exact h
  · exact ha
  · exact hb

section Finite

variable [Fintype V]

/-- The nonleaf predecessors in the vertex's original connected component. -/
noncomputable def predecessors (a : V) : Finset V :=
  univ.filter (fun b => I.Nonleaf b ∧ I.graph.Reachable a b ∧ I.left b < I.left a)

/-- The left-to-right rank of an original nonleaf, starting at one in its component. -/
noncomputable def spineRank (a : V) : ℕ := (I.predecessors a).card + 1

theorem spineRank_pos (a : V) : 0 < I.spineRank a := by simp [spineRank]

theorem spineRank_strict {a b : V} (ha : I.Nonleaf a)
    (hab : I.graph.Reachable a b) (hl : I.left a < I.left b) :
    I.spineRank a < I.spineRank b := by
  have hsub : insert a (I.predecessors a) ⊆ I.predecessors b := by
    intro c hc
    simp only [mem_insert, predecessors, mem_filter, mem_univ, true_and] at hc ⊢
    rcases hc with rfl | ⟨hc, hr, hlt⟩
    · exact ⟨ha, hab.symm, hl⟩
    · exact ⟨hc, hab.symm.trans hr, hlt.trans hl⟩
  have hnot : a ∉ I.predecessors a := by simp [predecessors]
  have := card_le_card hsub
  rw [card_insert_of_notMem hnot] at this
  simp only [spineRank]
  omega

theorem spineRank_injective (hI : I.Thin) {a b : V} (ha : I.Nonleaf a)
    (hb : I.Nonleaf b) (hab : I.graph.Reachable a b)
    (he : I.spineRank a = I.spineRank b) : a = b := by
  rcases lt_trichotomy (I.left a) (I.left b) with hl | hl | hl
  · have := spineRank_strict ha hab hl; omega
  · exact nonleaf_left_injective hI ha hb hl
  · have := spineRank_strict hb hab.symm hl; omega

/-- Adjacent nonleaves have consecutive ranks in their original component. -/
theorem spineRank_step (hI : I.Thin) {a b : V} (ha : I.Nonleaf a)
    (hab : I.graph.Adj a b) (hl : I.left a < I.left b) :
    I.spineRank b = I.spineRank a + 1 := by
  have he : I.predecessors b = insert a (I.predecessors a) := by
    ext c
    simp only [predecessors, mem_filter, mem_univ, true_and, mem_insert]
    constructor
    · rintro ⟨hc, hr, hcb⟩
      rcases lt_trichotomy (I.left c) (I.left a) with hca | hca | hca
      · exact Or.inr ⟨hc, hab.reachable.trans hr, hca⟩
      · exact Or.inl (nonleaf_left_injective hI hc ha hca)
      · exact (no_nonleaf_between hI hab hc hca hcb).elim
    · rintro (rfl | ⟨hc, hr, hca⟩)
      · exact ⟨ha, hab.symm.reachable, hl⟩
      · exact ⟨hc, hab.symm.reachable.trans hr, hca.trans hl⟩
  have hnot : a ∉ I.predecessors a := by simp [predecessors]
  simp only [spineRank, he, card_insert_of_notMem hnot]

theorem spineRank_adj (hI : I.Thin) {a b : V} (ha : I.Nonleaf a)
    (hb : I.Nonleaf b) (hab : I.graph.Adj a b) :
    I.spineRank b = I.spineRank a + 1 ∨ I.spineRank a = I.spineRank b + 1 := by
  rcases lt_trichotomy (I.left a) (I.left b) with hl | hl | hl
  · exact Or.inl (spineRank_step hI ha hab hl)
  · exact (hab.ne (nonleaf_left_injective hI ha hb hl)).elim
  · exact Or.inr (spineRank_step hI hb hab.symm hl)

/-- The induced graph on original nonleaves has maximum degree two. Together
with `isAcyclic` and `nonleaf_reachable`, this is the caterpillar property. -/
theorem nonleaf_neighbors_card_le_two (hI : I.Thin) {a : V} (ha : I.Nonleaf a) :
    (univ.filter (fun b => I.Nonleaf b ∧ I.graph.Adj a b)).card ≤ 2 := by
  let S := univ.filter (fun b => I.Nonleaf b ∧ I.graph.Adj a b)
  have hmem {b} (hb : b ∈ S) : I.Nonleaf b ∧ I.graph.Adj a b := (mem_filter.mp hb).2
  have hinj : Set.InjOn I.spineRank (S : Set V) := by
    intro b hb c hc he
    exact spineRank_injective hI (hmem hb).1 (hmem hc).1
      ((hmem hb).2.symm.reachable.trans (hmem hc).2.reachable) he
  have hsub : S.image I.spineRank ⊆ {I.spineRank a - 1, I.spineRank a + 1} := by
    intro n hn
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hn
    have := spineRank_adj hI ha (hmem hb).1 (hmem hb).2
    simp only [mem_insert, mem_singleton]; omega
  calc
    _ = (S.image I.spineRank).card := (card_image_iff.mpr hinj).symm
    _ ≤ ({I.spineRank a - 1, I.spineRank a + 1} : Finset ℕ).card := card_le_card hsub
    _ ≤ 2 := (card_insert_le _ _).trans_eq (by simp)

/-- Only original nonleaves need to be cut. Leaves, isolated vertices and
two-vertex components may all survive; the bound is on every simple path. -/
theorem path_card_le_of_avoids (hI : I.Thin) {a b : V} {p : I.graph.Walk a b}
    (hp : p.IsPath) {M ρ : ℕ} (hρ : ρ < M)
    (havoid : ∀ v ∈ p.support, I.Nonleaf v → I.spineRank v % M ≠ ρ) :
    p.support.length ≤ M + 1 := by
  let f : Fin (p.length - 1) → ℕ := fun i => I.spineRank (p.getVert (i.val + 1))
  have hn (i : Fin (p.length - 1)) : I.Nonleaf (p.getVert (i.val + 1)) :=
    nonleaf_getVert hp (by omega) (by have := i.isLt; omega)
  have hf : Function.Injective f := by
    intro i j hij
    have hv := spineRank_injective hI (hn i) (hn j)
      ((p.take (i.val + 1)).reachable.symm.trans (p.take (j.val + 1)).reachable) hij
    have he := hp.getVert_injOn (show i.val + 1 ≤ p.length by have := i.isLt; omega)
      (show j.val + 1 ≤ p.length by have := j.isLt; omega) hv
    exact Fin.ext (by omega)
  have hc : (List.ofFn f).IsChain (fun a b => a ≤ b + 1 ∧ b ≤ a + 1) := by
    apply List.isChain_ofFn.mpr
    intro i hi
    have hs := spineRank_adj hI (hn ⟨i, by omega⟩) (hn ⟨i + 1, hi⟩)
      (p.adj_getVert_succ (show i + 1 < p.length by omega))
    dsimp only at hs
    dsimp [f]
    omega
  have ha : ∀ v ∈ List.ofFn f, v % M ≠ ρ := by
    intro v hv
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
    exact havoid _ (p.getVert_mem_support _) (hn i)
  have h := PeriodicPhases.unit_chain_card_lt hρ hc ha
  rw [List.toFinset_card_of_nodup (List.nodup_ofFn.mpr hf), List.length_ofFn] at h
  rw [p.length_support]
  omega

end Finite

end Model
end LeanMachine.ThinIntervals
