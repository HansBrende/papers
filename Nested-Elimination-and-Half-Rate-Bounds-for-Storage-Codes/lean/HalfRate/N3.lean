import HalfRate.Pieces
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# N3: triangle-free graphs of maximum degree three

Every triangle-free graph of maximum degree at most three satisfies the weighted half bound
`2 h(V) ≤ Σ_v h({v})` (Theorem N3 of the paper). The proof follows the paper:
remove a shortest cycle of what remains (a three-record piece; an outside vertex adjacent to two
cycle vertices exists only for 4-cycles, at opposite vertices, and those are co-supplied), and
end with the acyclic remainder (a two-record piece). The decomposition theorem combines the
pieces.
-/

namespace HalfRate

open Finset MotionDepthCodes SimpleGraph

variable {V : Type*}

section CycleIndex

/-- Index `k` read modulo `g`. -/
def idx {g : ℕ} (hg : 0 < g) (k : ℕ) : Fin g := ⟨k % g, Nat.mod_lt _ hg⟩

@[simp] theorem idx_val {g : ℕ} (hg : 0 < g) (k : ℕ) : (idx hg k).val = k % g := rfl

theorem idx_self {g : ℕ} (hg : 0 < g) (i : Fin g) : idx hg i.val = i :=
  Fin.ext (Nat.mod_eq_of_lt i.isLt)

theorem idx_of_lt {g : ℕ} (hg : 0 < g) {k : ℕ} (hk : k < g) : idx hg k = ⟨k, hk⟩ :=
  Fin.ext (Nat.mod_eq_of_lt hk)

theorem idx_add_self {g : ℕ} (hg : 0 < g) (k : ℕ) : idx hg (g + k) = idx hg k :=
  Fin.ext (Nat.add_mod_left g k)

theorem fin_sub_val_eq_one {g : ℕ} (hg : 2 ≤ g) (i j : Fin g) :
    (i - j).val = 1 ↔ i.val = j.val + 1 ∨ (i.val = 0 ∧ j.val + 1 = g) := by
  have hi := i.isLt; have hj := j.isLt
  rcases le_or_gt j i with h | h
  · have h' : j.val ≤ i.val := h
    rw [Fin.sub_val_of_le h]; omega
  · have h' : i.val < j.val := h
    rw [Fin.coe_sub_iff_lt.mpr h]; omega

/-- Adjacency in the cycle graph in terms of values. -/
theorem cyc_adj_val {g : ℕ} (hg : 2 ≤ g) {i j : Fin g} :
    (cycleGraph g).Adj i j ↔ (i.val = j.val + 1 ∨ (i.val = 0 ∧ j.val + 1 = g)) ∨
      (j.val = i.val + 1 ∨ (j.val = 0 ∧ i.val + 1 = g)) := by
  rw [cycleGraph_adj', fin_sub_val_eq_one hg, fin_sub_val_eq_one hg]

theorem idx_adj {g : ℕ} (hg : 3 ≤ g) (k : ℕ) :
    (cycleGraph g).Adj (idx (by omega) k) (idx (by omega) (k + 1)) := by
  rw [cyc_adj_val (by omega)]
  simp only [idx_val]
  have h1 : (k + 1) % g = if g ≤ k % g + 1 % g then k % g + 1 % g - g else k % g + 1 % g :=
    Nat.add_mod_eq_ite
  have h2 : 1 % g = 1 := Nat.mod_eq_of_lt (by omega)
  have h3 := Nat.mod_lt k (show 0 < g by omega)
  rw [h2] at h1
  split_ifs at h1 <;> omega

theorem idx_inj {g : ℕ} (hg : 0 < g) {a b : ℕ} (hab : a ≤ b) (hb : b < a + g)
    (h : idx hg a = idx hg b) : a = b := by
  have h1 : b % g = a % g := (congrArg Fin.val h).symm
  have h2 := Nat.sub_mod_eq_zero_of_mod_eq h1
  rw [Nat.mod_eq_of_lt (by omega : b - a < g)] at h2
  omega

end CycleIndex

section Cycles

variable (G : SimpleGraph V)

/-- A cycle of length `g` in `G` with all vertices in `R`: a copy of `cycleGraph g`. -/
structure CycIn (R : Finset V) (g : ℕ) where
  f : Fin g → V
  inj : Function.Injective f
  mem : ∀ i, f i ∈ R
  adj : ∀ i j, (cycleGraph g).Adj i j → G.Adj (f i) (f j)

/-- `R` contains a cycle of length `g ≥ 3`. -/
def HasCyc (R : Finset V) (g : ℕ) : Prop := 3 ≤ g ∧ Nonempty (CycIn G R g)

variable {G}

/-- A closed path `p 0, …, p n` (`n ≥ 2`) in `R` is a cycle of length `n + 1`. -/
theorem hasCyc_of_closed {R : Finset V} (p : ℕ → V) (n : ℕ) (hn : 2 ≤ n)
    (hinj : ∀ s t, s ≤ n → t ≤ n → p s = p t → s = t)
    (hadj : ∀ s < n, G.Adj (p s) (p (s + 1))) (hclose : G.Adj (p n) (p 0))
    (hmem : ∀ s ≤ n, p s ∈ R) : HasCyc G R (n + 1) := by
  refine ⟨by omega, ⟨⟨fun i => p i.val, ?_, fun i => hmem _ (Nat.lt_succ_iff.mp i.isLt), ?_⟩⟩⟩
  · intro i j h
    exact Fin.ext (hinj _ _ (Nat.lt_succ_iff.mp i.isLt) (Nat.lt_succ_iff.mp j.isLt) h)
  · intro i j hij
    have hi := i.isLt; have hj := j.isLt
    rw [cyc_adj_val (by omega)] at hij
    rcases hij with (h | ⟨h1, h2⟩) | (h | ⟨h1, h2⟩)
    · have := hadj j.val (by omega); rw [show j.val + 1 = i.val by omega] at this
      exact this.symm
    · have hj' : j.val = n := by omega
      simp only [h1, hj']; exact hclose.symm
    · have := hadj i.val (by omega); rw [show i.val + 1 = j.val by omega] at this; exact this
    · have hi' : i.val = n := by omega
      simp only [h1, hi']; exact hclose

variable {R : Finset V} {g : ℕ}

theorem CycIn.arc_adj (c : CycIn G R g) (hg : 3 ≤ g) (k : ℕ) :
    G.Adj (c.f (idx (by omega) k)) (c.f (idx (by omega) (k + 1))) :=
  c.adj _ _ (idx_adj hg k)

theorem CycIn.arc_inj (c : CycIn G R g) (hg : 0 < g) {a s t d : ℕ} (hd : d < g) (hs : s ≤ d)
    (ht : t ≤ d) (h : c.f (idx hg (a + s)) = c.f (idx hg (a + t))) : s = t := by
  have h' := c.inj h
  rcases le_total s t with hst | hts
  · have := idx_inj hg (by omega) (by omega) h'; omega
  · have := idx_inj hg (by omega) (by omega) h'.symm; omega

/-- A chord of an arc of the cycle closes a cycle of length `d + 1`. -/
theorem CycIn.hasCyc_chord (c : CycIn G R g) (hg : 3 ≤ g) (a d : ℕ) (hd2 : 2 ≤ d) (hd : d < g)
    (h : G.Adj (c.f (idx (by omega) (a + d))) (c.f (idx (by omega) a))) :
    HasCyc G R (d + 1) := by
  have hg0 : 0 < g := by omega
  refine hasCyc_of_closed (fun s => c.f (idx hg0 (a + s))) d hd2 ?_ ?_ ?_ ?_
  · intro s t hs ht hst; exact c.arc_inj hg0 hd hs ht hst
  · intro s _; exact c.arc_adj hg (a + s)
  · simpa using h
  · intro s _; exact c.mem _

/-- A vertex of `R` off the cycle adjacent to both ends of an arc closes a cycle through it. -/
theorem CycIn.hasCyc_through (c : CycIn G R g) (hg : 3 ≤ g) {w : V} (hwR : w ∈ R)
    (hwC : ∀ k, c.f k ≠ w) (a d : ℕ) (hd1 : 1 ≤ d) (hd : d < g)
    (h1 : G.Adj w (c.f (idx (by omega) a))) (h2 : G.Adj w (c.f (idx (by omega) (a + d)))) :
    HasCyc G R (d + 1 + 1) := by
  have hg0 : 0 < g := by omega
  let p : ℕ → V := fun s => if s = 0 then w else c.f (idx hg0 (a + (s - 1)))
  have p0 : p 0 = w := by simp [p]
  have ps : ∀ s, p (s + 1) = c.f (idx hg0 (a + s)) := fun s => by
    simp only [p, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
  refine hasCyc_of_closed p (d + 1) (by omega) ?_ ?_ ?_ ?_
  · intro s t hs ht hst
    rcases s with _ | s <;> rcases t with _ | t
    · rfl
    · rw [p0, ps] at hst; exact absurd hst.symm (hwC _)
    · rw [p0, ps] at hst; exact absurd hst (hwC _)
    · rw [ps, ps] at hst
      have := c.arc_inj hg0 hd (by omega) (by omega) hst
      omega
  · intro s _
    rcases s with _ | s
    · rw [p0, ps]; simpa using h1
    · rw [ps, ps]; exact c.arc_adj hg (a + s)
  · rw [ps, p0]; exact h2.symm
  · intro s _
    rcases s with _ | s
    · rw [p0]; exact hwR
    · rw [ps]; exact c.mem _

/-- A shortest cycle has no chords. -/
theorem CycIn.chordless (c : CycIn G R g) (hg : 3 ≤ g) (hmin : ∀ g', HasCyc G R g' → g ≤ g')
    {i j : Fin g} (h : G.Adj (c.f i) (c.f j)) : (cycleGraph g).Adj i j := by
  have hg0 : 0 < g := by omega
  have key : ∀ i j : Fin g, i.val < j.val → G.Adj (c.f i) (c.f j) →
      (cycleGraph g).Adj i j := by
    intro i j hij h
    have hj := j.isLt
    rw [cyc_adj_val (by omega)]
    by_contra hne
    simp only [not_or, not_and] at hne
    have hd2 : 2 ≤ j.val - i.val := by omega
    have hd : j.val - i.val < g := by omega
    have hlt : j.val - i.val + 1 < g := by
      by_contra hge
      exact hne.2.2 (by omega) (by omega)
    have hc := c.hasCyc_chord hg i.val (j.val - i.val) hd2 hd (by
      rw [show i.val + (j.val - i.val) = j.val by omega, idx_self, idx_self]; exact h.symm)
    have := hmin _ hc
    omega
  rcases lt_trichotomy i.val j.val with hlt | heq | hgt
  · exact key i j hlt h
  · have := Fin.ext heq; subst this; exact absurd rfl h.ne
  · exact (key j i hgt h.symm).symm

/-- In a shortest cycle of length at least four, a vertex of `R` off the cycle adjacent to two
cycle vertices forces a 4-cycle with the two vertices opposite. -/
theorem CycIn.share (c : CycIn G R g) (hg : 4 ≤ g) (hmin : ∀ g', HasCyc G R g' → g ≤ g')
    {w : V} (hwR : w ∈ R) (hwC : ∀ k, c.f k ≠ w) {i j : Fin g} (hij : i.val < j.val)
    (hi : G.Adj w (c.f i)) (hj : G.Adj w (c.f j)) : g = 4 ∧ j.val = i.val + 2 := by
  have hjg := j.isLt
  have hA := c.hasCyc_through (by omega) hwR hwC i.val (j.val - i.val) (by omega) (by omega)
    (by rw [idx_self]; exact hi)
    (by rw [show i.val + (j.val - i.val) = j.val by omega, idx_self]; exact hj)
  have hB := c.hasCyc_through (by omega) hwR hwC j.val (g - j.val + i.val) (by omega)
    (by omega) (by rw [idx_self]; exact hj)
    (by rw [show j.val + (g - j.val + i.val) = g + i.val by omega, idx_add_self, idx_self]
        exact hi)
  have h1 := hmin _ hA
  have h2 := hmin _ hB
  constructor <;> omega

theorem not_cliqueFree_of_cycIn3 [DecidableEq V] (c : CycIn G R 3) : ¬ G.CliqueFree 3 := by
  intro hcf
  apply hcf {c.f 0, c.f 1, c.f 2}
  rw [is3Clique_triple_iff]
  exact ⟨c.adj 0 1 (by decide), c.adj 0 2 (by decide), c.adj 1 2 (by decide)⟩

end Cycles

section Pieces

variable [DecidableEq V] [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] {R : Finset V} {g : ℕ}

omit [Fintype V] [DecidableRel G.Adj] in
theorem mem_rev_ofFn (f : Fin g → V) {j : ℕ} (i : Fin g) (hi : i.val < j) :
    f i ∈ rev ∅ (List.ofFn f) j := by
  simp only [rev, empty_union, List.mem_toFinset]
  have := i.isLt
  have hlt : i.val < (List.take j (List.ofFn f)).length := by simp; omega
  simpa using List.getElem_mem hlt

/-- Colours of cycle positions: proper around the cycle, with positions `1` and `g - 1`
(the two neighbours of position `0`) in the same colour. -/
def ccol (g t : ℕ) : Fin 3 :=
  if t = 0 then 0 else if t + 1 = g then 1 else if g % 2 = 1 ∧ t + 2 = g then 2
  else if t % 2 = 1 then 1 else 0

/-- The supplying record of position `t`: the colour of the next position. -/
def bcol (g t : ℕ) : Fin 3 := if t + 1 = g then 0 else ccol g (t + 1)

theorem ccol_ne_bcol (hg : 4 ≤ g) {t : ℕ} (ht : t < g) : ccol g t ≠ bcol g t := by
  unfold bcol ccol
  split_ifs <;> first | decide | (exfalso; omega)

theorem ccol_last (hg : 4 ≤ g) : ccol g (g - 1) = bcol g 0 := by
  unfold bcol ccol
  split_ifs <;> first | rfl | (exfalso; omega)

/-- Position of a vertex on the cycle. -/
noncomputable def CycIn.pos (c : CycIn G R g) (hg : 0 < g) (v : V) : Fin g :=
  haveI : Nonempty (Fin g) := ⟨⟨0, hg⟩⟩
  Function.invFun c.f v

omit [DecidableEq V] [Fintype V] [DecidableRel G.Adj] in
theorem CycIn.pos_f (c : CycIn G R g) (hg : 0 < g) (t : Fin g) : c.pos hg (c.f t) = t := by
  have : Nonempty (Fin g) := ⟨⟨0, hg⟩⟩
  exact Function.leftInverse_invFun c.inj t

/-- The records of a cycle piece: positions of each colour. -/
def cycParts (c : CycIn G R g) (k : Fin 3) : Finset V :=
  (univ.filter (fun i : Fin g => ccol g i.val = k)).image c.f

/-- The charging conditions of a cycle piece. -/
theorem cycle_charged (c : CycIn G R g) (hg : 4 ≤ g)
    (hind : ∀ i j, G.Adj (c.f i) (c.f j) → (cycleGraph g).Adj i j)
    (hshare : ∀ w ∈ R, (∀ k, c.f k ≠ w) → ∀ i j : Fin g, i.val < j.val →
      G.Adj w (c.f i) → G.Adj w (c.f j) → g = 4 ∧ j.val = i.val + 2)
    (hdeg : ∀ v, (nbhd G v).card ≤ 3) :
    RelCharged (nbhd G) (univ \ R) (cycParts c) (fun v => bcol g (c.pos (by omega) v).val)
      (outPar (nbhd G) R (univ.image c.f)) (univ \ ((univ \ R) ∪ univ.image c.f)) ∅ (fun _ => ∅)
      (List.ofFn c.f) := by
  have hg0 : 0 < g := by omega
  have hg3 : 3 ≤ g := by omega
  -- every cycle neighbour of position `j` is revealed or lies in the supplying record
  have cov : ∀ (j : ℕ) (hj : j < g) (s : Fin g), (cycleGraph g).Adj ⟨j, hj⟩ s →
      c.f s ∈ rev ∅ (List.ofFn c.f) j ∪ cycParts c (bcol g j) := by
    intro j hj s hs
    have hsg := s.isLt
    rw [cyc_adj_val (by omega)] at hs
    simp only at hs
    rcases hs with (h | ⟨h1, h2⟩) | (h | ⟨h1, h2⟩)
    · exact mem_union_left _ (mem_rev_ofFn c.f s (by omega))
    · apply mem_union_right
      simp only [cycParts, mem_image, mem_filter, mem_univ, true_and]
      refine ⟨s, ?_, rfl⟩
      rw [show s.val = g - 1 by omega, h1]; exact ccol_last hg
    · apply mem_union_right
      simp only [cycParts, mem_image, mem_filter, mem_univ, true_and]
      refine ⟨s, ?_, rfl⟩
      simp only [bcol, show ¬(j + 1 = g) by omega, ↓reduceIte, h]
    · exact mem_union_left _ (mem_rev_ofFn c.f s (by omega))
  have nbC : ∀ (j : ℕ) (hj : j < g) (u : V), G.Adj (c.f ⟨j, hj⟩) u → u ∈ univ.image c.f →
      u ∈ rev ∅ (List.ofFn c.f) j ∪ cycParts c (bcol g j) := by
    intro j hj u hu huC
    obtain ⟨s, -, rfl⟩ := mem_image.mp huC
    exact cov j hj s (hind _ _ hu)
  apply relCharged_of_cosupply
  · -- steps without an outside parent
    intro j hj hp
    have hj' : j < g := by simpa using hj
    simp only [List.getElem_ofFn, CycIn.pos_f] at hp ⊢
    intro u hu
    have hu' : G.Adj (c.f ⟨j, hj'⟩) u := by simpa [nbhd] using hu
    by_cases huR : u ∈ R
    · exact mem_union_right _ (nbC j hj' u hu' (outPar_none hp hu huR))
    · exact mem_union_left _ (by simp [huR])
  · -- steps with an outside parent
    intro j hj w hp
    have hj' : j < g := by simpa using hj
    simp only [List.getElem_ofFn, CycIn.pos_f] at hp ⊢
    obtain ⟨hw, hwR, hwC⟩ := outPar_some hp
    refine ⟨by simp [hwR, hwC], ?_, by simp⟩
    intro u hu
    have hu' : G.Adj (c.f ⟨j, hj'⟩) u := by simpa [nbhd] using hu
    by_cases huw : u = w
    · subst huw; exact mem_union_right _ (mem_insert_self _ _)
    by_cases huR : u ∈ R
    swap
    · exact mem_union_left _ (by simp [huR])
    by_cases huC : u ∈ univ.image c.f
    · exact mem_union_right _ (mem_insert_of_mem (nbC j hj' u hu' huC))
    exfalso
    -- four distinct neighbours: the two cycle neighbours, `w` and `u`
    have hx : G.Adj (c.f ⟨j, hj'⟩) (c.f (idx hg0 (j + 1))) := by
      have := c.arc_adj hg3 j; rwa [idx_of_lt hg0 hj'] at this
    have hy : G.Adj (c.f ⟨j, hj'⟩) (c.f (idx hg0 (j + g - 1))) := by
      have := c.arc_adj hg3 (j + g - 1)
      rw [show j + g - 1 + 1 = g + j by omega, idx_add_self, idx_of_lt hg0 hj'] at this
      exact this.symm
    have hxy : c.f (idx hg0 (j + 1)) ≠ c.f (idx hg0 (j + g - 1)) := by
      intro he
      have := c.arc_inj hg0 (a := j + 1) (s := 0) (t := g - 2) (d := g - 2) (by omega)
        (by omega) le_rfl (by rw [show j + 1 + (g - 2) = j + g - 1 by omega]; exact he)
      omega
    have hxC : c.f (idx hg0 (j + 1)) ∈ univ.image c.f := mem_image_of_mem _ (mem_univ _)
    have hyC : c.f (idx hg0 (j + g - 1)) ∈ univ.image c.f := mem_image_of_mem _ (mem_univ _)
    have h4 := four_le_card (s := nbhd G (c.f ⟨j, hj'⟩)) (by simpa [nbhd] using hx)
      (by simpa [nbhd] using hy) hw hu hxy
      (by rintro rfl; exact hwC hxC) (by rintro rfl; exact huC hxC)
      (by rintro rfl; exact hwC hyC) (by rintro rfl; exact huC hyC) (Ne.symm huw)
    have := hdeg (c.f ⟨j, hj'⟩)
    omega
  · -- co-supply
    intro j j' hjj hj' w h1 h2
    have hj'' : j' < g := by simpa using hj'
    simp only [List.getElem_ofFn, CycIn.pos_f] at h1 h2 ⊢
    obtain ⟨hw1, hwR, hwC⟩ := outPar_some h1
    obtain ⟨hw2, -, -⟩ := outPar_some h2
    have hwC' : ∀ k, c.f k ≠ w := fun k hk => hwC (hk ▸ mem_image_of_mem _ (mem_univ k))
    obtain ⟨rfl, hjj'⟩ := hshare w hwR hwC' ⟨j, by omega⟩ ⟨j', hj''⟩ hjj (mem_filter.mp hw1).2.symm (mem_filter.mp hw2).2.symm
    simp only at hjj'
    subst hjj'
    have : j < 2 := by omega
    interval_cases j <;> decide

/-- **Cycle pieces.** A chordless cycle of length at least four in `R`, met by the other vertices
of `R` at most once except at opposite vertices of a 4-cycle, is a three-record piece in context
`univ \ R`, in a graph of maximum degree three. -/
noncomputable def cyclePiece (c : CycIn G R g) (hg : 4 ≤ g)
    (hind : ∀ i j, G.Adj (c.f i) (c.f j) → (cycleGraph g).Adj i j)
    (hshare : ∀ w ∈ R, (∀ k, c.f k ≠ w) → ∀ i j : Fin g, i.val < j.val →
      G.Adj w (c.f i) → G.Adj w (c.f j) → g = 4 ∧ j.val = i.val + 2)
    (hdeg : ∀ v, (nbhd G v).card ≤ 3) :
    PieceCert (nbhd G) (univ \ R) (univ.image c.f) where
  m := 3
  P := cycParts c
  disj k k' hkk' := by
    rw [Finset.disjoint_left]; intro x hx hx'
    simp only [cycParts, mem_image, mem_filter, mem_univ, true_and] at hx hx'
    obtain ⟨i, hi, rfl⟩ := hx
    obtain ⟨i', hi', he⟩ := hx'
    have := c.inj he; subst this; exact hkk' (hi.symm.trans hi')
  cover := by
    ext x; simp only [cycParts, mem_biUnion, mem_image, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨_, i, _, rfl⟩; exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩; exact ⟨_, i, rfl, rfl⟩
  l := List.ofFn c.f
  hl := by ext x; simp [List.mem_ofFn]
  a v := ccol g (c.pos (by omega) v).val
  b v := bcol g (c.pos (by omega) v).val
  par := outPar (nbhd G) R (univ.image c.f)
  own v hv := by
    obtain ⟨t, rfl⟩ := List.mem_ofFn.mp hv
    simp only [CycIn.pos_f, cycParts]
    exact mem_image_of_mem _ (by simp)
  ab v hv := by
    obtain ⟨t, rfl⟩ := List.mem_ofFn.mp hv
    simp only [CycIn.pos_f]
    exact ccol_ne_bcol hg t.isLt
  charged := cycle_charged c hg hind hshare hdeg

end Pieces

section Main

variable [DecidableEq V] [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **Shortest-cycle decompositions, block form.** Let the side information at the vertices of a
block `K` lie in the neighbourhoods of a graph `G` of maximum degree three in which every vertex
outside `K` has at most one neighbour, let every vertex of `K` have at most one in-neighbour
outside `K`, and let `L` (disjoint from `K`) be the vertices still to come after `K`. Given pieces
for shortest cycles of length three, a decomposition from the context `univ \ L` extends to one
from `univ \ (R ∪ L)` for every `R ⊆ K`: longer shortest cycles are three-record pieces and the
acyclic remainder is a relative 2-colouring. -/
theorem block_decomp_of_cycles (N : V → Finset V) {K L : Finset V} (hKL : Disjoint K L)
    (hNG : ∀ v ∈ K, N v ⊆ nbhd G v) (hdeg : ∀ v, (nbhd G v).card ≤ 3)
    (hpend : ∀ w, w ∉ K → (nbhd G w).card ≤ 1)
    (hout : ∀ v ∈ K, ∀ u ∈ N v, ∀ u' ∈ N v, u ∉ K → u' ∉ K → u = u')
    (htri : ∀ R ⊆ K, ∀ c : CycIn G R 3,
      Nonempty (PieceCert N (univ \ (R ∪ L)) (univ.image c.f)))
    {q : List (Finset V)} (hq : Decomp N (univ \ L) q) :
    ∀ R ⊆ K, ∃ pcs, Decomp N (univ \ (R ∪ L)) pcs := by
  intro R
  induction R using Finset.strongInduction with
  | H R ih =>
    intro hRK
    have hRL : Disjoint R L := disjoint_of_subset_left hRK hKL
    have hadj : ∀ v ∈ K, ∀ u ∈ N v, G.Adj v u := fun v hv u hu => by
      have := hNG v hv hu; simpa [nbhd] using this
    by_cases hcyc : ∃ g, HasCyc G R g
    · classical
      obtain ⟨g, ⟨hg3, ⟨c⟩⟩, hmin⟩ : ∃ g, HasCyc G R g ∧ ∀ g', HasCyc G R g' → g ≤ g' :=
        ⟨Nat.find hcyc, Nat.find_spec hcyc, fun g' h => Nat.find_min' hcyc h⟩
      have hCR : univ.image c.f ⊆ R := by
        intro x hx; obtain ⟨i, -, rfl⟩ := mem_image.mp hx; exact c.mem i
      have hCne : (univ.image c.f).Nonempty :=
        ⟨c.f ⟨0, by omega⟩, mem_image_of_mem _ (mem_univ _)⟩
      have hpiece : Nonempty (PieceCert N (univ \ (R ∪ L)) (univ.image c.f)) := by
        rcases (show g = 3 ∨ 4 ≤ g by omega) with h3 | hg4
        · subst h3; exact htri R hRK c
        · let c' : CycIn G (R ∪ L) g :=
            { f := c.f, inj := c.inj, mem := fun i => mem_union_left _ (c.mem i), adj := c.adj }
          have hshare : ∀ w ∈ R ∪ L, (∀ k, c'.f k ≠ w) → ∀ i j : Fin g, i.val < j.val →
              G.Adj w (c'.f i) → G.Adj w (c'.f j) → g = 4 ∧ j.val = i.val + 2 := by
            intro w hw hwC i j hij hi hj
            rcases mem_union.mp hw with hwR | hwL
            · exact c.share hg4 hmin hwR hwC hij hi hj
            · exfalso
              have hwK : w ∉ K := fun h => Finset.disjoint_left.mp hKL h hwL
              have hne : c.f i ≠ c.f j := fun e => by
                have := congrArg Fin.val (c.inj e); omega
              have h2 := card_le_one.mp (hpend w hwK) _ (by simpa [nbhd] using hi) _
                (by simpa [nbhd] using hj)
              exact hne h2
          exact ⟨(cyclePiece c' hg4 (fun i j h => c.chordless (by omega) hmin h) hshare
            hdeg).mono fun v hv => hNG v (hRK (hCR hv))⟩
      obtain ⟨rest, hrest⟩ := ih _ (sdiff_ssubset hCR hCne) (sdiff_subset.trans hRK)
      refine ⟨univ.image c.f :: rest, ?_⟩
      simp only [Decomp]
      refine ⟨Finset.disjoint_left.mpr fun x hx hx' => ?_, hpiece, ?_⟩
      · simp only [mem_sdiff, mem_univ, true_and, mem_union, not_or] at hx
        exact hx.1 (hCR hx')
      · have he : (univ \ (R ∪ L)) ∪ univ.image c.f = univ \ ((R \ univ.image c.f) ∪ L) := by
          ext x
          have h1 : x ∈ univ.image c.f → x ∈ R := fun h => hCR h
          have h2 : x ∈ R → x ∉ L := fun h hxL => Finset.disjoint_left.mp hRL h hxL
          simp only [mem_union, mem_sdiff, mem_univ, true_and]
          tauto
        rw [he]; exact hrest
    · -- the acyclic remainder: a relative 2-colouring
      have hac : (G.induce (R : Set V)).IsAcyclic := by
        rw [isAcyclic_iff_free_cycleGraph]
        intro n hn hcont
        obtain ⟨φ⟩ := hcont
        exact hcyc ⟨n, hn, ⟨⟨fun i => (φ i).val, fun i j h => φ.injective (Subtype.ext h),
          fun i => Finset.mem_coe.mp (φ i).prop, fun i j hij => φ.toHom.map_adj hij⟩⟩⟩
      obtain ⟨col⟩ := hac.colorable_two
      let κ : V → Fin 2 := fun v => if h : v ∈ R then col ⟨v, by simpa using h⟩ else 0
      have hκ : ∀ u v, u ∈ R → v ∈ R → G.Adj u v → κ u ≠ κ v := by
        intro u v hu hv huv
        simp only [κ, hu, hv, ↓reduceDIte]
        exact col.valid (show (G.induce (R : Set V)).Adj ⟨u, by simpa using hu⟩
          ⟨v, by simpa using hv⟩ from huv)
      -- a colour class has no arc inside
      have hclass : ∀ k : Fin 2, IsAcyclicIn N (R.filter (κ · = k)) := by
        intro k T hT hne
        obtain ⟨v, hv⟩ := hne
        refine ⟨v, hv, fun u hu huT => ?_⟩
        have hv' := mem_filter.mp (hT hv)
        have hu' := mem_filter.mp (hT huT)
        exact hκ v u hv'.1 hu'.1 (hadj v (hRK hv'.1) u hu) (hv'.2.trans hu'.2.symm)
      have he : (univ \ (R ∪ L)) ∪ R = univ \ L := by
        ext x
        have h1 : x ∈ R → x ∉ L := fun h hxL => Finset.disjoint_left.mp hRL h hxL
        simp only [mem_union, mem_sdiff, mem_univ, true_and]
        tauto
      refine ⟨R :: q, ?_⟩
      simp only [Decomp]
      refine ⟨Finset.disjoint_left.mpr fun x hx hx' => by simp [hx'] at hx, ?_, by rw [he]; exact hq⟩
      refine bdirPiece N (univ \ (R ∪ L)) R (R.filter (κ · = 0)) (R.filter (κ · = 1)) ?_ ?_
        (hclass 0) (hclass 1) (outPar N (R ∪ L) R) ?_ ?_ ?_
      · rw [Finset.disjoint_left]; intro x hx hx'
        have h0 := (mem_filter.mp hx).2
        have h1 := (mem_filter.mp hx').2
        rw [h0] at h1
        exact absurd h1 (by decide)
      · ext x; simp only [mem_union, mem_filter]
        constructor
        · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
        · intro hx
          have : κ x = 0 ∨ κ x = 1 := by
            generalize κ x = y; revert y; decide
          rcases this with h | h
          · exact Or.inl ⟨hx, h⟩
          · exact Or.inr ⟨hx, h⟩
      · intro v hv u hu
        by_cases huR : u ∈ R
        · exact Or.inr (Or.inl huR)
        by_cases huL : u ∈ L
        · right; right
          have huK : u ∉ K := fun h => Finset.disjoint_left.mp hKL h huL
          cases hp : outPar N (R ∪ L) R v with
          | none => exact absurd (outPar_none hp hu (mem_union_right _ huL)) huR
          | some w =>
            obtain ⟨hw, hwRL, hwR⟩ := outPar_some hp
            have hwL : w ∈ L := (mem_union.mp hwRL).resolve_left hwR
            have hwK : w ∉ K := fun h => Finset.disjoint_left.mp hKL h hwL
            rw [hout v (hRK hv) w hw u hu hwK huK]
        · exact Or.inl (by simp [huR, huL])
      · intro v _ w hp
        obtain ⟨-, hwRL, hwR⟩ := outPar_some hp
        exact ⟨by simp [hwRL], hwR⟩
      · intro v hv v' hv' w h1 h2
        obtain ⟨hw1, hwRL, hwR⟩ := outPar_some h1
        obtain ⟨hw2, -, -⟩ := outPar_some h2
        have hwK : w ∉ K := fun h =>
          Finset.disjoint_left.mp hKL h ((mem_union.mp hwRL).resolve_left hwR)
        have e := card_le_one.mp (hpend w hwK) v
          (by simpa [nbhd] using (hadj v (hRK hv) w hw1).symm) v'
          (by simpa [nbhd] using (hadj v' (hRK hv') w hw2).symm)
        subst e; exact Iff.rfl

/-- **Shortest-cycle decompositions.** For any relation `N` whose side information lies in the
neighbourhoods of a graph `G` of maximum degree three, every remaining vertex set has a certified
decomposition, given pieces for shortest cycles of length three (the block form with one
block). -/
theorem decomp_of_cycles (N : V → Finset V) (hNG : ∀ v, N v ⊆ nbhd G v)
    (hdeg : ∀ v, (nbhd G v).card ≤ 3)
    (htri : ∀ (R : Finset V) (c : CycIn G R 3),
      Nonempty (PieceCert N (univ \ R) (univ.image c.f))) :
    ∀ R : Finset V, ∃ pcs, Decomp N (univ \ R) pcs := by
  intro R
  have h := block_decomp_of_cycles N (K := univ) (L := ∅) (disjoint_empty_right _)
    (fun v _ => hNG v) hdeg (fun w hw => absurd (mem_univ w) hw)
    (fun v _ u _ u' _ hu _ => absurd (mem_univ u) hu)
    (fun R _ c => by rw [union_empty]; exact htri R c) (q := []) (by simp [Decomp]) R
    (subset_univ R)
  rwa [union_empty] at h

/-- Every remaining vertex set has a certified decomposition, for triangle-free graphs of
maximum degree three. -/
theorem n3_decomp (hcf : G.CliqueFree 3) (hdeg : ∀ v, (nbhd G v).card ≤ 3) :
    ∀ R : Finset V, ∃ pcs, Decomp (nbhd G) (univ \ R) pcs :=
  decomp_of_cycles (nbhd G) (fun _ => subset_refl _) hdeg
    (fun _ c => absurd hcf (not_cliqueFree_of_cycIn3 c))

/-- **N3.** Every triangle-free graph of maximum degree at most three satisfies the weighted half
bound: `2 h(V) ≤ Σ_v h({v})` for every polymatroid valid on its neighbourhood relation. -/
theorem rateBound_n3 (hcf : G.CliqueFree 3) (hdeg : ∀ v, G.degree v ≤ 3) :
    RateBound (nbhd G) (1 / 2) := by
  have hdeg' : ∀ v, (nbhd G v).card ≤ 3 := fun v => by
    have h := hdeg v
    rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter] at h
    exact h
  obtain ⟨pcs, h⟩ := n3_decomp hcf hdeg' univ
  rw [sdiff_self] at h
  exact rateBound_of_decomp h

/-- Storage codes on triangle-free graphs of maximum degree three have `|C|² ≤ |α|^|V|`. -/
theorem card_sq_le_n3 {α : Type*} [Fintype α] [Nonempty α] (hcf : G.CliqueFree 3)
    (hdeg : ∀ v, G.degree v ≤ 3) {C : Finset (V → α)} (hC : IsStorageCode (nbhd G) C) :
    C.card ^ 2 ≤ Fintype.card α ^ Fintype.card V :=
  card_sq_le_of_rateBound_half (rateBound_n3 hcf hdeg) hC

end Main

end HalfRate
