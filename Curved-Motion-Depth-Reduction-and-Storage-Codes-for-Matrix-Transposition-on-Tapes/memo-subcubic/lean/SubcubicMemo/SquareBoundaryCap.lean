import SubcubicMemo.SquareGeometry

/-! A common closure argument for the complete-bipartite and cube caps:
three boundary vertices, each with two fixed neighbors, admit at most one
additional vertex. The resulting component remains bipartite. -/

namespace SubcubicMemo.Squares

open Finset MotionDepthCodes
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

structure BoundarySeed (L Q P : Finset V) : Prop where
  boundary : P ⊆ L
  card : P.card = 3
  disjoint : Disjoint L Q
  independent : ∀ a ∈ L, ∀ b ∈ L, ¬ G.Adj a b
  right : ∀ q ∈ Q, ∀ x, G.Adj q x → x ∈ L
  internal : ∀ a ∈ L, a ∉ P → ∀ x, G.Adj a x → x ∈ Q
  pair : ∀ a ∈ P, ∃ q ∈ Q, ∃ r ∈ Q, q ≠ r ∧ G.Adj a q ∧ G.Adj a r

theorem two_pairs_meet {P : Finset V} {a b c d : V} (ha : a ∈ P) (hb : b ∈ P)
    (hc : c ∈ P) (hd : d ∈ P) (hab : a ≠ b) (hcd : c ≠ d)
    (hcard : P.card ≤ 3) : a = c ∨ a = d ∨ b = c ∨ b = d := by
  by_contra hno
  push Not at hno
  obtain ⟨hac, had, hbc, hbd⟩ := hno
  have hsub : ({a, b, c, d} : Finset V) ⊆ P := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with hx | hx | hx | hx <;> subst x <;> assumption
  have hh := card_le_card hsub
  have hn : ({a, b, c, d} : Finset V).card = 4 := by
    simp [hab, hac, had, hbc, hbd, hcd]
  omega

variable (h : Hyp G) {L Q P : Finset V} (s : BoundarySeed (G := G) L Q P)
include h s

theorem BoundarySeed.saturated {a x : V} (ha : a ∈ P) (hax : G.Adj a x) (hx : x ∉ Q)
    {z : V} (haz : G.Adj a z) : z ∈ Q ∨ z = x := by
  obtain ⟨q, hq, r, hr, hqr, haq, har⟩ := s.pair a ha
  have hxq : x ≠ q := fun he => hx (he ▸ hq)
  have hxr : x ≠ r := fun he => hx (he ▸ hr)
  have hz := neighbor_of_three G h.degree haq har hax hqr hxq.symm hxr.symm haz
  rcases hz with hz | hz | hz
  · exact Or.inl (hz ▸ hq)
  · exact Or.inl (hz ▸ hr)
  · exact Or.inr hz

theorem BoundarySeed.extra_second {a x : V} (ha : a ∈ P) (hax : G.Adj a x) (hx : x ∉ Q) :
    ∃ b ∈ P, b ≠ a ∧ G.Adj x b := by
  obtain ⟨b, z, hs⟩ := h.covered a x hax
  have hz : z ∈ Q := (s.saturated h ha hax hx hs.2.2.2.1.symm).resolve_right
    (fun he => hs.2.2.2.2.2 he.symm)
  have hbL := s.right z hz b hs.2.2.1.symm
  have hb : b ∈ P := by
    by_contra hn
    exact hx (s.internal b hbL hn x hs.2.1.symm)
  exact ⟨b, hb, hs.2.2.2.2.1.symm, hs.2.1⟩

theorem BoundarySeed.one_extension {a b x : V} (ha : a ∈ P) (hb : b ∈ P)
    (hab : a ≠ b) (hax : G.Adj a x) (hbx : G.Adj b x) (hx : x ∉ Q) :
    (∀ z, G.Adj x z → z ∈ P) ∧
    (∀ c ∈ L, ∀ z, G.Adj c z → z ∈ insert x Q) := by
  constructor
  · intro z hxz
    by_cases hza : z = a
    · subst z; exact ha
    by_cases hzb : z = b
    · subst z; exact hb
    obtain ⟨y, w, hs⟩ := h.covered x z hxz
    have hw := neighbor_of_three G h.degree hax.symm hbx.symm hxz
      hab (Ne.symm hza) (Ne.symm hzb) hs.2.2.2.1.symm
    have hy' : y ∈ Q ∨ y = x := by
      rcases hw with hw | hw | hw
      · subst w; exact s.saturated h ha hax hx hs.2.2.1.symm
      · subst w; exact s.saturated h hb hbx hx hs.2.2.1.symm
      · exact False.elim (hs.2.2.2.2.2 hw.symm)
    have hy : y ∈ Q := hy'.resolve_right (fun he => hs.2.2.2.2.1 he.symm)
    have hzL := s.right y hy z hs.2.1.symm
    by_contra hzP
    exact hx (s.internal z hzL hzP x hxz.symm)
  · intro c hc z hcz
    by_cases hz : z ∈ Q
    · exact mem_insert_of_mem hz
    have hcP : c ∈ P := by
      by_contra hn
      exact hz (s.internal c hc hn z hcz)
    obtain ⟨d, hd, hdc, hzd⟩ := s.extra_second h hcP hcz hz
    have hpair := two_pairs_meet hcP hd ha hb hdc.symm hab (by rw [s.card])
    have hz' : z ∈ Q ∨ z = x := by
      rcases hpair with hca | hcb | hda | hdb
      · subst c; exact s.saturated h ha hax hx hcz
      · subst c; exact s.saturated h hb hbx hx hcz
      · subst d; exact s.saturated h ha hax hx hzd.symm
      · subst d; exact s.saturated h hb hbx hx hzd.symm
    exact mem_insert.mpr (Or.inl (hz'.resolve_left hz))

theorem BoundarySeed.hom (hconn : G.Preconnected) :
    Nonempty (G →g circularClique 8 3) := by
  have hP : P.Nonempty := card_pos.mp (by rw [s.card]; omega)
  obtain ⟨a0, ha0⟩ := hP
  by_cases he : ∃ a ∈ P, ∃ x, G.Adj a x ∧ x ∉ Q
  · obtain ⟨a, ha, x, hax, hx⟩ := he
    obtain ⟨b, hb, hba, hxb⟩ := s.extra_second h ha hax hx
    have hxn : x ∉ L := fun hxl => s.independent a (s.boundary ha) x hxl hax
    obtain ⟨hNx, hNL⟩ := s.one_extension h ha hb hba.symm hax hxb.symm hx
    apply hom_of_closed_bipartition G hconn L (insert x Q)
    · exact ⟨a0, mem_union_left _ (s.boundary ha0)⟩
    · exact disjoint_insert_right.mpr ⟨hxn, s.disjoint⟩
    · exact hNL
    · intro q hq z hqz
      rcases mem_insert.mp hq with hq | hq
      · subst q; exact s.boundary (hNx z hqz)
      · exact s.right q hq z hqz
  · apply hom_of_closed_bipartition G hconn L Q
    · exact ⟨a0, mem_union_left _ (s.boundary ha0)⟩
    · exact s.disjoint
    · intro a ha x hax
      by_cases haP : a ∈ P
      · by_contra hx
        exact he ⟨a, haP, x, hax, hx⟩
      · exact s.internal a ha haP x hax
    · exact s.right

end SubcubicMemo.Squares
