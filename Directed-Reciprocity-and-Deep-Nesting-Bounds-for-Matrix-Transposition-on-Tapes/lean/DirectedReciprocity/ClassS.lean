import DirectedReciprocity.DigonCycle
import HalfRate.Components
import HalfRate.Barrier
import HalfRate.PairedDistance

/-!
# Directed reciprocity, `Class S` decompositions (`Theorem S*`), and the barrier bound (`Corollary B*`)

A finite recovery relation `N : V → Finset V` belongs to **`Class S`** (`IsClassS N`) if:
1. `N` is loopless (`∀ v, v ∉ N v`),
2. `N` has no transitive triangle (`TTFree N`),
3. every vertex has in-degree at most three (`∀ v, (N v).card ≤ 3`), and
4. every vertex of full in-degree three reciprocates all outgoing arcs:
   `∀ v, (N v).card = 3 → ∀ u, v ∈ N u → u ∈ N v` (no child that is not a parent).

No bound is assumed on out-degrees of vertices with `(N v).card ≤ 2`.

We prove **Theorem S\*** (`classS_decomp`, `rateBound_classS`, `card_sq_le_classS`): every remaining
subset `R` of a `Class S` relation admits a certified piece decomposition `Decomp N (univ \ R) pcs`,
resolving the intermediate target named in Section 9.2, item 2 of *Nested Elimination and Half-Rate
Bounds for Storage Codes* (the all-code version of the fourth paper's Theorem S on its whole class;
Conjecture P, numbered Conjecture 9.1 there, remains open) for all storage codes (linear and
nonlinear) over arbitrary alphabets.

As an immediate consequence, we obtain **Corollary B\*** (`barrier_ineq_classS`,
`log_card_le_barrier_classS`), extending the vertex-cut / isolated-outside-vertex barrier inequality
from undirected triangle-free graphs of maximum degree `3` to all `Class S` digraphs.
-/

namespace DirectedReciprocity

open Finset HalfRate MotionDepthCodes SimpleGraph

section Defs

variable {V : Type*} [DecidableEq V]

/-- **`Class S`**: loopless, `TTFree`, in-degree at most `3`, and every in-degree-`3` vertex
reciprocates every outgoing arc (`v ∈ N u → u ∈ N v`). -/
def IsClassS (N : V → Finset V) : Prop :=
  (∀ v, v ∉ N v) ∧ TTFree N ∧ (∀ v, (N v).card ≤ 3) ∧
    ∀ v, (N v).card = 3 → ∀ u, v ∈ N u → u ∈ N v

instance [Fintype V] (N : V → Finset V) : Decidable (IsClassS N) := by
  unfold IsClassS TTFree; infer_instance

/-- Relative `Class S` on a vertex subset `R`. -/
def ClassSOn (N : V → Finset V) (R : Finset V) : Prop :=
  (∀ v ∈ R, v ∉ N v) ∧ TTFreeOn N R ∧ (∀ v ∈ R, (N v ∩ R).card ≤ 3) ∧
    ∀ v ∈ R, (N v ∩ R).card = 3 → ∀ u ∈ R, v ∈ N u → u ∈ N v

theorem IsClassS.classSOn {N : V → Finset V} (h : IsClassS N) (R : Finset V) :
    ClassSOn N R := by
  obtain ⟨hloop, hTT, hdeg, hrec⟩ := h
  refine ⟨fun v _ => hloop v, fun x _ y _ z _ => hTT x y z,
    fun v _ => (card_le_card inter_subset_left).trans (hdeg v), ?_⟩
  intro v _ hcard3 u _ hvu
  have hle1 : (N v ∩ R).card ≤ (N v).card := card_le_card inter_subset_left
  have hle2 : (N v).card ≤ 3 := hdeg v
  exact hrec v (by omega) u hvu

theorem ClassSOn.mono {N : V → Finset V} {R R' : Finset V}
    (h : ClassSOn N R) (hsub : R' ⊆ R) : ClassSOn N R' := by
  obtain ⟨hloop, hTT, hdeg, hrec⟩ := h
  refine ⟨fun v hv => hloop v (hsub hv), hTT.mono hsub,
    fun v hv => (card_le_card (inter_subset_inter_left hsub)).trans (hdeg v (hsub hv)), ?_⟩
  intro v hv hcard3 u hu hvu
  have hle1 : (N v ∩ R').card ≤ (N v ∩ R).card := card_le_card (inter_subset_inter_left hsub)
  have hle2 : (N v ∩ R).card ≤ 3 := hdeg v (hsub hv)
  exact hrec v (hsub hv) (by omega) u (hsub hu) hvu

/-- Mutual-arc (digon) simple graph of a recovery relation `M`. -/
def digonGraph (M : V → Finset V) : SimpleGraph V where
  Adj u v := u ≠ v ∧ u ∈ M v ∧ v ∈ M u
  symm := ⟨fun _ _ ⟨hne, h1, h2⟩ => ⟨hne.symm, h2, h1⟩⟩
  loopless := ⟨fun _ ⟨hne, _, _⟩ => hne rfl⟩

instance (M : V → Finset V) : DecidableRel (digonGraph M).Adj :=
  fun u v => inferInstanceAs (Decidable (u ≠ v ∧ u ∈ M v ∧ v ∈ M u))

theorem digonGraph_cliqueFree3 {M : V → Finset V} (hTT : TTFree M) :
    (digonGraph M).CliqueFree 3 := by
  intro t ht
  obtain ⟨x, y, z, hxy, hxz, hyz, -⟩ := is3Clique_iff.mp ht
  exact hTT x y z hxy.1 hyz.1 hxz.1 hxy.2.1 hyz.2.1 hxz.2.1

/-- Restriction of a recovery relation `N` to internal arcs on `S`. -/
def resRel (N : V → Finset V) (S : Finset V) (v : V) : Finset V :=
  if v ∈ S then N v ∩ S else ∅

theorem resRel_subset {N : V → Finset V} {S : Finset V} (v : V) :
    resRel N S v ⊆ S := by
  unfold resRel
  split_ifs with hv
  · exact inter_subset_right
  · exact empty_subset _

theorem resRel_of_not_mem {N : V → Finset V} {S : Finset V} {v : V} (hv : v ∉ S) :
    resRel N S v = ∅ := by
  simp [resRel, hv]

theorem resRel_of_mem {N : V → Finset V} {S : Finset V} {v : V} (hv : v ∈ S) :
    resRel N S v = N v ∩ S := by
  simp [resRel, hv]

theorem ClassSOn.isClassS_resRel {N : V → Finset V} {S : Finset V} (h : ClassSOn N S) :
    IsClassS (resRel N S) := by
  obtain ⟨hloop, hTT, hdeg, hrec⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v hv
    by_cases hvS : v ∈ S
    · rw [resRel_of_mem hvS] at hv
      exact hloop v hvS (mem_inter.mp hv).1
    · rw [resRel_of_not_mem hvS] at hv
      exact nomatch hv
  · intro x y z hxy hyz hxz h1 h2 h3
    have hzS : z ∈ S := by
      by_contra hz
      rw [resRel_of_not_mem hz] at h2
      exact nomatch h2
    rw [resRel_of_mem hzS] at h2 h3
    have hyS : y ∈ S := (mem_inter.mp h2).2
    have hxS : x ∈ S := (mem_inter.mp h3).2
    rw [resRel_of_mem hyS] at h1
    exact hTT x hxS y hyS z hzS hxy hyz hxz (mem_inter.mp h1).1 (mem_inter.mp h2).1
      (mem_inter.mp h3).1
  · intro v
    by_cases hvS : v ∈ S
    · rw [resRel_of_mem hvS]; exact hdeg v hvS
    · rw [resRel_of_not_mem hvS]; simp
  · intro v hcard3 u hvu
    have hvS : v ∈ S := by
      by_contra hvS
      rw [resRel_of_not_mem hvS] at hcard3
      simp at hcard3
    have huS : u ∈ S := by
      by_contra huS
      rw [resRel_of_not_mem huS] at hvu
      exact nomatch hvu
    rw [resRel_of_mem hvS] at hcard3 ⊢
    rw [resRel_of_mem huS] at hvu
    exact mem_inter.mpr ⟨hrec v hvS hcard3 u huS (mem_inter.mp hvu).1, huS⟩

end Defs

section SourceSCC

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Directed reachability along arcs staying inside `R` (`a ∈ N b` is an arc `a → b`). -/
inductive ReachesIn (N : V → Finset V) (R : Finset V) : V → V → Prop
  | refl {u : V} : u ∈ R → ReachesIn N R u u
  | tail {u v w : V} : ReachesIn N R u v → v ∈ N w → w ∈ R → ReachesIn N R u w

omit [DecidableEq V] [Fintype V] in
theorem ReachesIn.mem_left {N : V → Finset V} {R : Finset V} {u v : V}
    (h : ReachesIn N R u v) : u ∈ R := by
  induction h with
  | refl hu => exact hu
  | tail _ _ _ ih => exact ih

omit [DecidableEq V] [Fintype V] in
theorem ReachesIn.mem_right {N : V → Finset V} {R : Finset V} {u v : V}
    (h : ReachesIn N R u v) : v ∈ R := by
  cases h with
  | refl hu => exact hu
  | tail _ _ hw => exact hw

omit [DecidableEq V] [Fintype V] in
theorem ReachesIn.trans {N : V → Finset V} {R : Finset V} {u v w : V}
    (h1 : ReachesIn N R u v) (h2 : ReachesIn N R v w) : ReachesIn N R u w := by
  induction h2 with
  | refl _ => exact h1
  | tail _ hvw hw ih => exact ReachesIn.tail ih hvw hw

open Classical in
noncomputable def ancIn (N : V → Finset V) (R : Finset V) (v : V) : Finset V :=
  R.filter (fun u => ReachesIn N R u v)

omit [DecidableEq V] [Fintype V] in
theorem mem_ancIn {N : V → Finset V} {R : Finset V} {u v : V} :
    u ∈ ancIn N R v ↔ ReachesIn N R u v := by
  classical
  simp only [ancIn, mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨h.mem_left, h⟩⟩

omit [Fintype V] in
/-- Every nonempty `R` contains a nonempty subset `S ⊆ R` that is in-closed in `R`
(`∀ v ∈ S, ∀ u ∈ N v, u ∈ R → u ∈ S`) and strongly connected under `resRel N S`. -/
theorem exists_inClosed_scc (N : V → Finset V) {R : Finset V} (hR : R.Nonempty) :
    ∃ S ⊆ R, S.Nonempty ∧
      (∀ v ∈ S, ∀ u ∈ N v, u ∈ R → u ∈ S) ∧
      (∀ x ∈ S, ∀ y ∈ S, Reaches (resRel N S) x y) := by
  classical
  obtain ⟨v₀, hv₀R, hmin⟩ := exists_min_image R (fun v => (ancIn N R v).card) hR
  let S := ancIn N R v₀
  have hv₀S : v₀ ∈ S := mem_ancIn.mpr (ReachesIn.refl hv₀R)
  have hSR : S ⊆ R := filter_subset _ _
  have hinClosed : ∀ v ∈ S, ∀ u ∈ N v, u ∈ R → u ∈ S := by
    intro v hvS u huv huR
    have hvv₀ := mem_ancIn.mp hvS
    have huv' : ReachesIn N R u v := ReachesIn.tail (ReachesIn.refl huR) huv (hSR hvS)
    exact mem_ancIn.mpr (huv'.trans hvv₀)
  have hstay : ∀ {x y : V}, ReachesIn N R x y → y ∈ S → Reaches (resRel N S) x y := by
    intro x y hxy
    induction hxy with
    | refl _ => intro _; exact Relation.ReflTransGen.refl
    | tail hab hbc _ ih =>
      intro hcS
      have hbS := hinClosed _ hcS _ hbc hab.mem_right
      exact (ih hbS).tail ((resRel_of_mem hcS).symm ▸ mem_inter.mpr ⟨hbc, hbS⟩)
  refine ⟨S, hSR, ⟨v₀, hv₀S⟩, hinClosed, ?_⟩
  intro x hxS y hyS
  have hx_v0 : Reaches (resRel N S) x v₀ := hstay (mem_ancIn.mp hxS) hv₀S
  have hsub_y : ancIn N R y ⊆ S := by
    intro z hz
    exact mem_ancIn.mpr ((mem_ancIn.mp hz).trans (mem_ancIn.mp hyS))
  have heq_y : ancIn N R y = S :=
    eq_of_subset_of_card_le hsub_y (hmin y (hSR hyS))
  have hv0_y : ReachesIn N R v₀ y := mem_ancIn.mp (heq_y.symm ▸ hv₀S)
  exact hx_v0.trans (hstay hv0_y hyS)

/-- Lifting a piece certificate from an in-closed subset `S ⊆ R` to `R`. -/
def liftPieceCertInClosed {N : V → Finset V} {R S H : Finset V}
    (hSR : S ⊆ R) (hin : ∀ v ∈ S, ∀ u ∈ N v, u ∈ R → u ∈ S) (hHS : H ⊆ S)
    (c : PieceCert (resRel N S) (univ \ S) H) :
    PieceCert N (univ \ R) H where
  m := c.m
  P := c.P
  disj := c.disj
  cover := c.cover
  l := c.l
  hl := c.hl
  a := c.a
  b := c.b
  par := c.par
  own := c.own
  ab := c.ab
  charged := by
    have hnest := (relCharged_iff_nested (resRel N S) (univ \ S) c.P c.b c.par
      (univ \ ((univ \ S) ∪ H)) c.l).mp c.charged
    refine (relCharged_iff_nested N (univ \ R) c.P c.b c.par
      (univ \ ((univ \ R) ∪ H)) c.l).mpr ⟨?_, ?_, hnest.2.2⟩
    · intro j hj hp
      have hvH : c.l[j] ∈ H :=
        Eq.mp (congrArg (c.l[j] ∈ ·) c.hl) (List.mem_toFinset.mpr (List.getElem_mem hj))
      have hvS : c.l[j] ∈ S := hHS hvH
      have hcov := hnest.1 j hj hp
      intro u hu
      by_cases huR : u ∈ R
      · have huS : u ∈ S := hin c.l[j] hvS u hu huR
        have hures : u ∈ resRel N S c.l[j] := by
          rw [resRel_of_mem hvS]; exact mem_inter.mpr ⟨hu, huS⟩
        rcases mem_union.mp (hcov hures) with huUS | hrem
        · exact absurd huS (mem_sdiff.mp huUS).2
        · exact mem_union_right _ hrem
      · exact mem_union_left _ (mem_sdiff.mpr ⟨mem_univ u, huR⟩)
    · intro j hj w hp
      have hvH : c.l[j] ∈ H :=
        Eq.mp (congrArg (c.l[j] ∈ ·) c.hl) (List.mem_toFinset.mpr (List.getElem_mem hj))
      have hvS : c.l[j] ∈ S := hHS hvH
      obtain ⟨hwW, hcov⟩ := hnest.2.1 j hj w hp
      have hwS : w ∈ S ∧ w ∉ H := by
        simp only [mem_sdiff, mem_univ, true_and, mem_union, not_or, not_not] at hwW
        exact hwW
      refine ⟨?_, ?_⟩
      · simp only [mem_sdiff, mem_univ, true_and, mem_union, not_or]
        exact ⟨fun h => h (hSR hwS.1), hwS.2⟩
      · intro u hu
        by_cases huR : u ∈ R
        · have huS : u ∈ S := hin c.l[j] hvS u hu huR
          have hures : u ∈ resRel N S c.l[j] := by
            rw [resRel_of_mem hvS]; exact mem_inter.mpr ⟨hu, huS⟩
          rcases mem_union.mp (hcov hures) with huUS | hrem
          · exact absurd huS (mem_sdiff.mp huUS).2
          · exact mem_union_right _ hrem
        · exact mem_union_left _ (mem_sdiff.mpr ⟨mem_univ u, huR⟩)

end SourceSCC

section SubPieces

variable {V : Type*} [DecidableEq V] [Fintype V]

omit [Fintype V] in
private theorem not_hasDCyc_of_isAcyclicIn {M : V → Finset V} {W : Finset V}
    (hac : IsAcyclicIn M W) {ℓ : ℕ} (hc : HasDCyc M W ℓ) : False := by
  obtain ⟨_, ⟨c⟩⟩ := hc
  let T : Finset V := univ.image c.f
  have hTW : T ⊆ W := by
    intro x hx; obtain ⟨i, -, rfl⟩ := mem_image.mp hx; exact c.mem i
  have hTne : T.Nonempty := ⟨c.f ⟨0, c.pos⟩, mem_image_of_mem _ (mem_univ _)⟩
  obtain ⟨v, hvT, hno⟩ := hac T hTW hTne
  obtain ⟨i, -, rfl⟩ := mem_image.mp hvT
  have harc : c.f (idx c.pos (i.val + 1)) ∈ M (c.f i) := by
    have := c.arc i.val; rwa [idx_self] at this
  exact hno _ harc (mem_image_of_mem _ (mem_univ _))

/-- Reversing the orientation of a `CycIn G S L`. -/
def cycRev {G : SimpleGraph V} {S : Finset V} {L : ℕ} (hL : 3 ≤ L) (c : CycIn G S L) :
    CycIn G S L where
  f i := c.f (idx (by omega) (L - i.val))
  inj i j hij := by
    have hi := i.isLt; have hj := j.isLt
    have heq := congrArg Fin.val (c.inj hij)
    simp only [idx_val] at heq
    by_cases hi0 : i.val = 0 <;> by_cases hj0 : j.val = 0
    · exact Fin.ext (by omega)
    · rw [hi0, Nat.sub_zero, Nat.mod_self, Nat.mod_eq_of_lt (by omega)] at heq; omega
    · rw [hj0, Nat.sub_zero, Nat.mod_self, Nat.mod_eq_of_lt (by omega)] at heq; omega
    · rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at heq
      exact Fin.ext (by omega)
  mem i := c.mem _
  adj i j hij := by
    apply c.adj
    have hi := i.isLt; have hj := j.isLt
    rw [cyc_adj_val (by omega)] at hij ⊢
    simp only [idx_val]
    have hmod : ∀ x < L, (L - x) % L = if x = 0 then 0 else L - x := by
      intro x hx
      split_ifs with h0
      · simp [h0]
      · exact Nat.mod_eq_of_lt (by omega)
    rw [hmod i.val hi, hmod j.val hj]
    rcases hij with (h | ⟨h1, h2⟩) | (h | ⟨h1, h2⟩) <;> split_ifs <;> omega

/-- **Subcase 4a (`minChordArc_pieceCert`)**: A path `p : Fin (d + 1) → V` (`d ≥ 3`) inside `S`
whose consecutive vertices form digons, with a single forward one-way chord `p 0 ∈ M (p d)`,
no other internal `M`-arcs, and at most one parent in `S \ H'` per vertex, admits a `(d + 2)`-record
piece certificate `PieceCert M (univ \ S) (univ.image p)`. -/
noncomputable def minChordArc_pieceCert {M : V → Finset V} {S : Finset V} {d : ℕ}
    (hd : 3 ≤ d) (p : Fin (d + 1) → V) (hp_inj : Function.Injective p)
    (hpS : ∀ s, p s ∈ S) (hMS : ∀ v ∈ S, M v ⊆ S) (hTT : TTFree M)
    (hdig : ∀ s : Fin (d + 1), ∀ hs : s.val < d,
      p ⟨s.val + 1, by omega⟩ ∈ M (p s) ∧ p s ∈ M (p ⟨s.val + 1, by omega⟩))
    (hinternal : ∀ s t : Fin (d + 1), p t ∈ M (p s) →
      t.val + 1 = s.val ∨ s.val + 1 = t.val ∨ (s.val = d ∧ t.val = 0))
    (hout1 : ∀ s : Fin (d + 1), ∀ w₁ w₂, w₁ ∈ M (p s) → w₂ ∈ M (p s) →
      w₁ ∉ univ.image p → w₂ ∉ univ.image p → w₁ = w₂) :
    PieceCert M (univ \ S) (univ.image p) := by
  classical
  let H' : Finset V := univ.image p
  let P : Fin (d + 2) → Finset V := fun r =>
    if hr : r.val ≤ d then {p ⟨r.val, by omega⟩} else ∅
  have hdisj : ∀ r₁ r₂ : Fin (d + 2), r₁ ≠ r₂ → Disjoint (P r₁) (P r₂) := by
    intro r₁ r₂ hne
    rw [Finset.disjoint_left]
    intro v h1 h2
    simp only [P] at h1 h2
    split_ifs at h1 h2 with hr1 hr2
    · rw [mem_singleton] at h1 h2
      have hidx := hp_inj (h1.symm.trans h2)
      have hv : r₁.val = r₂.val := congrArg (Fin.val : Fin (d + 1) → ℕ) hidx
      exact hne (Fin.ext hv)
    · exact nomatch h2
    · exact nomatch h1
    · exact nomatch h1
  have hcover : (univ : Finset (Fin (d + 2))).biUnion P = H' := by
    ext v
    simp only [mem_biUnion, mem_univ, true_and, H', mem_image]
    constructor
    · rintro ⟨r, hr⟩
      simp only [P] at hr
      split_ifs at hr with hrd
      · exact ⟨⟨r.val, by omega⟩, (mem_singleton.mp hr).symm⟩
      · exact nomatch hr
    · rintro ⟨s, rfl⟩
      exact ⟨⟨s.val, by omega⟩, by simp [P, Nat.lt_succ_iff.mp s.isLt]⟩
  haveI : Nonempty (Fin (d + 1)) := ⟨0⟩
  let invP : V → Fin (d + 1) := Function.invFun p
  have hinvP : ∀ s : Fin (d + 1), invP (p s) = s := Function.leftInverse_invFun hp_inj
  let a : V → Fin (d + 2) := fun v => ⟨(invP v).val, by have := (invP v).isLt; omega⟩
  let b : V → Fin (d + 2) := fun v => ⟨(invP v).val + 1, by have := (invP v).isLt; omega⟩
  let par : V → Option V := outPar M S H'
  let l : List V := List.ofFn p
  have hl_len : l.length = d + 1 := List.length_ofFn
  have hl_get : ∀ (j : ℕ) (hj : j < l.length), l[j] = p ⟨j, hl_len ▸ hj⟩ := by
    intro j hj; simp only [l, List.getElem_ofFn]
  have hown : ∀ v ∈ l, v ∈ P (a v) := by
    intro v hv
    obtain ⟨s, rfl⟩ := List.mem_ofFn.mp hv
    simp [a, hinvP s, P, Nat.lt_succ_iff.mp s.isLt]
  have hab : ∀ v ∈ l, a v ≠ b v := by
    intro v _ heq
    have := congrArg Fin.val heq
    simp [a, b] at this
  have hstep_in : ∀ (j : ℕ) (hj : j < d + 1) (u : V),
      u ∈ M (p ⟨j, hj⟩) → u ∈ H' →
      u ∈ rev ∅ l j ∪ P (b (p ⟨j, hj⟩)) := by
    intro j hj u hu huH'
    obtain ⟨t, -, rfl⟩ := mem_image.mp huH'
    rcases hinternal ⟨j, hj⟩ t hu with hprev | hnext | ⟨hjd, ht0⟩
    · dsimp only at hprev
      exact mem_union_left _ (mem_rev_ofFn p t (by omega))
    · dsimp only at hnext
      apply mem_union_right
      simp only [b, hinvP ⟨j, hj⟩, P, show j + 1 ≤ d by omega, ↓reduceDIte, mem_singleton]
      exact congrArg p (Fin.ext hnext.symm)
    · dsimp only at hjd ht0
      exact mem_union_left _ (mem_rev_ofFn p t (by omega))
  refine {
    m := d + 2
    P := P
    disj := hdisj
    cover := hcover
    l := l
    hl := by ext v; simp only [l, List.mem_toFinset, List.mem_ofFn, mem_image, mem_univ, true_and]
    a := a
    b := b
    par := par
    own := hown
    ab := hab
    charged := ?_ }
  apply relCharged_of_nested
  · intro j hj hp_none
    have hjd : j < d + 1 := hl_len ▸ hj
    rw [hl_get j hj] at hp_none ⊢
    intro u hu
    have huS : u ∈ S := hMS _ (hpS _) hu
    have huH' : u ∈ H' := outPar_none hp_none hu huS
    exact mem_union_right _ (hstep_in j hjd u hu huH')
  · intro j hj w hp_some
    have hjd : j < d + 1 := hl_len ▸ hj
    rw [hl_get j hj] at hp_some ⊢
    obtain ⟨hwM, hwS, hwH'⟩ := outPar_some hp_some
    refine ⟨?_, ?_, empty_subset _⟩
    · simp only [mem_sdiff, mem_univ, true_and, mem_union, not_or, not_not]
      exact ⟨hwS, hwH'⟩
    · intro u hu
      by_cases huH' : u ∈ H'
      · exact mem_union_right _ (mem_insert_of_mem (hstep_in j hjd u hu huH'))
      · have huw : u = w := hout1 ⟨j, hjd⟩ u w hu hwM huH' hwH'
        subst huw
        exact mem_union_right _ (mem_insert_self _ _)
  · intro j j' hlt hj' w hp1 hp2
    have hj'd : j' < d + 1 := hl_len ▸ hj'
    have hjd : j < d + 1 := by omega
    rw [hl_get j (by omega)] at hp1 ⊢
    rw [hl_get j' hj'] at hp2
    obtain ⟨hw1, _, hwH'⟩ := outPar_some hp1
    obtain ⟨hw2, _, _⟩ := outPar_some hp2
    intro x hxP
    apply mem_union_left
    simp only [b, hinvP ⟨j, hjd⟩, P] at hxP
    split_ifs at hxP with hj1d
    · rw [mem_singleton] at hxP
      subst hxP
      have hne_succ : j' ≠ j + 1 := by
        intro heq
        subst heq
        have hp_edge := (hdig ⟨j, hjd⟩ (by dsimp; omega)).2
        have hne1 : w ≠ p ⟨j, hjd⟩ := fun e => hwH' (e ▸ mem_image_of_mem p (mem_univ _))
        have hne2 : p ⟨j, hjd⟩ ≠ p ⟨j + 1, hj'd⟩ := fun e => by
          have := congrArg Fin.val (hp_inj e); simp at this
        have hne3 : w ≠ p ⟨j + 1, hj'd⟩ := fun e => hwH' (e ▸ mem_image_of_mem p (mem_univ _))
        exact hTT w (p ⟨j, hjd⟩) (p ⟨j + 1, hj'd⟩) hne1 hne2 hne3 hw1 hp_edge hw2
      exact mem_rev_ofFn p ⟨j + 1, by omega⟩ (by dsimp; omega)
    · exact nomatch hxP

/-- **Subcase 4c (`augmentedStride3_pieceCert`)**: Let `f' : Fin L → V` (`L ≥ 6`, `3 ∣ L`) be a
chordless digon cycle inside `S` with stride-3 outside hubs `w' : Fin 3 → V` (`w' r ∈ S \ C`), such
that `u₀ := w' 0` has `(M u₀).card = 2`, `M u₀ ∩ C = {f' 0}`, and `M (f' t) = {f' (t-1), f' (t+1), w' (t % 3)}`.
Then `H_+ := insert u₀ (univ.image f')` admits an explicit `(L + 2)`-record `PieceCert M (univ \ S) H_+`. -/
noncomputable def augmentedStride3_pieceCert {M : V → Finset V} {S : Finset V} {L : ℕ}
    (hL6 : 6 ≤ L) (h3L : 3 ∣ L) (f' : Fin L → V) (hf' : Function.Injective f')
    (hf'S : ∀ t, f' t ∈ S) (hMS : ∀ v ∈ S, M v ⊆ S) (hTT : TTFree M)
    (w' : Fin 3 → V) (hw'S : ∀ r, w' r ∈ S ∧ w' r ∉ univ.image f')
    (hMf' : ∀ t : Fin L, ∀ u ∈ M (f' t),
      u = f' (idx (by omega) (t.val + L - 1)) ∨
      u = f' (idx (by omega) (t.val + 1)) ∨
      u = w' ⟨t.val % 3, Nat.mod_lt _ (by decide)⟩)
    (hcyc_f' : ∀ t : Fin L, f' (idx (by omega) (t.val + 1)) ∈ M (f' t) ∧
      f' (idx (by omega) (t.val + L - 1)) ∈ M (f' t))
    (_hu0_in : f' ⟨0, by omega⟩ ∈ M (w' 0))
    (hu0_out1 : ∀ z₁ z₂, z₁ ∈ M (w' 0) → z₂ ∈ M (w' 0) →
      z₁ ∉ insert (w' 0) (univ.image f') → z₂ ∉ insert (w' 0) (univ.image f') → z₁ = z₂)
    (hu0_C : ∀ t : Fin L, f' t ∈ M (w' 0) → t = ⟨0, by omega⟩)
    (hloop_u0 : w' 0 ∉ M (w' 0)) :
    PieceCert M (univ \ S) (insert (w' 0) (univ.image f')) := by
  classical
  have hL0 : 0 < L := by omega
  let u₀ := w' 0
  let Hplus : Finset V := insert u₀ (univ.image f')
  let g : Fin (L + 1) → V := fun j =>
    if hj0 : j.val = 0 then u₀ else f' ⟨j.val - 1, by omega⟩
  have hg0 : g ⟨0, by omega⟩ = u₀ := by simp [g]
  have hg_succ : ∀ t : Fin L, g ⟨t.val + 1, by omega⟩ = f' t := fun t => by simp [g]
  have hg_ne : ∀ (j : Fin (L + 1)), j.val ≠ 0 → g j = f' ⟨j.val - 1, by omega⟩ :=
    fun j h => by simp only [g, h, ↓reduceDIte]
  have hg_inj : Function.Injective g := by
    intro j₁ j₂ heq
    by_cases h1 : j₁.val = 0 <;> by_cases h2 : j₂.val = 0
    · exact Fin.ext (by omega)
    · exfalso
      simp only [g, h1, h2, ↓reduceDIte, u₀] at heq
      exact (hw'S 0).2 (heq ▸ mem_image_of_mem f' (mem_univ _))
    · exfalso
      simp only [g, h1, h2, ↓reduceDIte, u₀] at heq
      exact (hw'S 0).2 (heq.symm ▸ mem_image_of_mem f' (mem_univ _))
    · simp only [g, h1, h2, ↓reduceDIte] at heq
      have hidx := congrArg Fin.val (hf' heq)
      simp at hidx
      exact Fin.ext (by omega)
  have hg_img : univ.image g = Hplus := by
    ext v
    simp only [mem_image, mem_univ, true_and, Hplus, mem_insert]
    constructor
    · rintro ⟨j, rfl⟩
      by_cases hj0 : j.val = 0
      · left; rw [show j = ⟨0, by omega⟩ from Fin.ext hj0, hg0]
      · right; exact ⟨⟨j.val - 1, by omega⟩, (hg_ne j hj0).symm⟩
    · rintro (rfl | ⟨t, rfl⟩)
      · exact ⟨⟨0, by omega⟩, hg0⟩
      · exact ⟨⟨t.val + 1, by omega⟩, hg_succ t⟩
  let col : Fin (L + 1) → Fin (L + 2) := fun j =>
    if j.val = 0 then ⟨L, by omega⟩
    else if j.val = 1 then ⟨1, by omega⟩
    else if j.val = 2 ∨ j.val = L then ⟨0, by omega⟩
    else ⟨j.val, by omega⟩
  let sup : Fin (L + 1) → Fin (L + 2) := fun j =>
    if j.val = 0 then ⟨1, by omega⟩
    else if j.val = 1 then ⟨0, by omega⟩
    else if hjL : j.val < L then col ⟨j.val + 1, by omega⟩
    else ⟨L + 1, by omega⟩
  have hcol_ne_sup : ∀ j : Fin (L + 1), col j ≠ sup j := by
    intro j heq
    have hj := j.isLt
    have hv := congrArg Fin.val heq
    dsimp only [col, sup] at hv
    split_ifs at hv <;> simp only at hv <;> omega
  let P : Fin (L + 2) → Finset V := fun r =>
    (univ.filter (fun j : Fin (L + 1) => col j = r)).image g
  have hdisj : ∀ r₁ r₂ : Fin (L + 2), r₁ ≠ r₂ → Disjoint (P r₁) (P r₂) := by
    intro r₁ r₂ hne
    rw [Finset.disjoint_left]
    intro v h1 h2
    obtain ⟨j₁, hj₁, rfl⟩ := mem_image.mp h1
    obtain ⟨j₂, hj₂, heq⟩ := mem_image.mp h2
    cases hg_inj heq
    exact hne ((mem_filter.mp hj₁).2.symm.trans (mem_filter.mp hj₂).2)
  have hcover : (univ : Finset (Fin (L + 2))).biUnion P = Hplus := by
    rw [← hg_img]
    ext v
    simp only [mem_biUnion, mem_univ, true_and, P, mem_image, mem_filter]
    constructor
    · rintro ⟨r, j, -, rfl⟩; exact ⟨j, rfl⟩
    · rintro ⟨j, rfl⟩; exact ⟨col j, j, rfl, rfl⟩
  haveI : Nonempty (Fin (L + 1)) := ⟨0⟩
  let invG : V → Fin (L + 1) := Function.invFun g
  have hinvG : ∀ j : Fin (L + 1), invG (g j) = j := Function.leftInverse_invFun hg_inj
  let a : V → Fin (L + 2) := fun v => col (invG v)
  let b : V → Fin (L + 2) := fun v => sup (invG v)
  let par : V → Option V := outPar M S Hplus
  let l : List V := List.ofFn g
  have hl_len : l.length = L + 1 := List.length_ofFn
  have hl_get : ∀ (j : ℕ) (hj : j < l.length), l[j] = g ⟨j, hl_len ▸ hj⟩ := by
    intro j hj; simp only [l, List.getElem_ofFn]
  have hP1 : P ⟨1, by omega⟩ = {g ⟨1, by omega⟩} := by
    ext v
    simp only [P, mem_image, mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · rintro ⟨j, hj, rfl⟩
      have hval := congrArg Fin.val hj
      have hjlt := j.isLt
      dsimp only [col] at hval
      split_ifs at hval <;> simp only at hval <;> try omega
      congr; exact Fin.ext (by omega)
    · rintro rfl
      refine ⟨⟨1, by omega⟩, ?_, rfl⟩
      apply Fin.ext; dsimp [col]
  have hPmid : ∀ (k : ℕ) (hk3 : 3 ≤ k) (hkL : k ≤ L - 1),
      P ⟨k, by omega⟩ = {g ⟨k, by omega⟩} := by
    intro k hk3 hkL
    ext v
    simp only [P, mem_image, mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · rintro ⟨j, hj, rfl⟩
      have hval := congrArg Fin.val hj
      have hjlt := j.isLt
      dsimp only [col] at hval
      split_ifs at hval <;> simp only at hval <;> try omega
      congr; exact Fin.ext hval
    · rintro rfl
      refine ⟨⟨k, by omega⟩, ?_, rfl⟩
      apply Fin.ext; dsimp only [col]; split_ifs <;> (try dsimp) <;> omega
  have hpar1_none : par (g ⟨1, by omega⟩) = none := by
    rw [hg_succ ⟨0, by omega⟩]
    cases hp : par (f' ⟨0, by omega⟩) with
    | none => rfl
    | some z =>
      exfalso
      obtain ⟨hzM, _, hzH⟩ := outPar_some hp
      rcases hMf' ⟨0, by omega⟩ z hzM with h | h | h
      · exact hzH (mem_insert_of_mem (h ▸ mem_image_of_mem _ (mem_univ _)))
      · exact hzH (mem_insert_of_mem (h ▸ mem_image_of_mem _ (mem_univ _)))
      · simp only [Nat.zero_mod] at h
        exact hzH (h ▸ mem_insert_self _ _)
  have hg_in_step : ∀ (j : ℕ) (hj : j < L + 1) (u : V),
      u ∈ M (g ⟨j, hj⟩) → u ∈ Hplus →
      u ∈ rev ∅ l j ∪ P (sup ⟨j, hj⟩) := by
    intro j hj u hu huH
    rcases (show j = 0 ∨ j = 1 ∨ (2 ≤ j ∧ j ≤ L - 1) ∨ j = L by omega) with
      hj0 | hj1 | ⟨hj2, hjL1⟩ | hj_eq_L
    · subst hj0
      rw [hg0] at hu
      rcases mem_insert.mp huH with hu_eq | huC
      · rw [hu_eq] at hu; exact absurd hu hloop_u0
      · obtain ⟨t, -, rfl⟩ := mem_image.mp huC
        have ht0 := hu0_C t hu
        subst ht0
        apply mem_union_right
        have hsup0 : sup ⟨0, hj⟩ = ⟨1, by omega⟩ := by dsimp only [sup]; rfl
        rw [hsup0, hP1, mem_singleton]
        exact (hg_succ ⟨0, by omega⟩).symm
    · subst hj1
      rw [hg_succ ⟨0, by omega⟩] at hu
      have hsup1 : sup ⟨1, hj⟩ = ⟨0, by omega⟩ := by dsimp only [sup]; rfl
      rcases hMf' ⟨0, by omega⟩ u hu with h | h | h
      · apply mem_union_right
        rw [h, show idx hL0 (0 + L - 1) = ⟨L - 1, by omega⟩ from
          Fin.ext (by simp [idx_val, Nat.mod_eq_of_lt (show L - 1 < L by omega)])]
        rw [hsup1]
        simp only [P, mem_image, mem_filter, mem_univ, true_and]
        refine ⟨⟨L, by omega⟩, ?_, ?_⟩
        · apply Fin.ext; dsimp only [col]; split_ifs <;> (try dsimp) <;> omega
        · exact hg_ne ⟨L, by omega⟩ (by dsimp; omega)
      · apply mem_union_right
        rw [h, show idx hL0 (0 + 1) = ⟨1, by omega⟩ from
          Fin.ext (by simp [idx_val, Nat.mod_eq_of_lt (show 1 < L by omega)])]
        rw [hsup1]
        simp only [P, mem_image, mem_filter, mem_univ, true_and]
        refine ⟨⟨2, by omega⟩, ?_, ?_⟩
        · apply Fin.ext; dsimp [col]
        · exact hg_ne ⟨2, by omega⟩ (by dsimp; omega)
      · apply mem_union_left
        simp only [Nat.zero_mod] at h
        have hw0_eq : w' ⟨0, Nat.mod_lt 0 (by decide)⟩ = g ⟨0, by omega⟩ := hg0.symm
        rw [h, hw0_eq]
        exact mem_rev_ofFn g ⟨0, by omega⟩ (by dsimp; omega)
    · have hg_eq : g ⟨j, hj⟩ = f' ⟨j - 1, by omega⟩ := hg_ne ⟨j, hj⟩ (by dsimp; omega)
      rw [hg_eq] at hu
      rcases hMf' ⟨j - 1, by omega⟩ u hu with h | h | h
      · apply mem_union_left
        have hprev : idx hL0 (j - 1 + L - 1) = ⟨j - 2, by omega⟩ := by
          apply Fin.ext
          simp only [idx_val]
          rw [show j - 1 + L - 1 = L + (j - 2) by omega, Nat.add_mod_left]
          exact Nat.mod_eq_of_lt (by omega)
        have hge1 : f' ⟨j - 2, by omega⟩ = g ⟨j - 1, by omega⟩ := by
          rw [hg_ne ⟨j - 1, by omega⟩ (by dsimp; omega)]
          congr 1
        rw [h, hprev, hge1]
        exact mem_rev_ofFn g ⟨j - 1, by omega⟩ (by dsimp; omega)
      · apply mem_union_right
        have hnext : idx hL0 (j - 1 + 1) = ⟨j, by omega⟩ := by
          apply Fin.ext
          simp only [idx_val, show j - 1 + 1 = j by omega]
          exact Nat.mod_eq_of_lt (by omega)
        have hge2 : f' ⟨j, by omega⟩ = g ⟨j + 1, by omega⟩ := (hg_succ ⟨j, by omega⟩).symm
        rw [h, hnext, hge2]
        have hsup_j : sup ⟨j, hj⟩ = col ⟨j + 1, by omega⟩ := by
          dsimp only [sup]; split_ifs <;> (try dsimp) <;> omega
        rw [hsup_j]
        exact mem_image_of_mem g (mem_filter.mpr ⟨mem_univ _, rfl⟩)
      · apply mem_union_left
        rcases mem_insert.mp huH with hu_eq | huC
        · rw [hu_eq, ← hg0]; exact mem_rev_ofFn g ⟨0, by omega⟩ (by dsimp; omega)
        · exfalso; exact (hw'S _).2 (h ▸ huC)
    · have hg_eq : g ⟨j, hj⟩ = f' ⟨L - 1, by omega⟩ := by
        rw [hg_ne ⟨j, hj⟩ (by dsimp; omega)]
        congr 1; exact Fin.ext (by dsimp; omega)
      rw [hg_eq] at hu
      rcases hMf' ⟨L - 1, by omega⟩ u hu with h | h | h
      · apply mem_union_left
        have hprev : idx hL0 (L - 1 + L - 1) = ⟨L - 2, by omega⟩ := by
          apply Fin.ext
          simp only [idx_val]
          rw [show L - 1 + L - 1 = L + (L - 2) by omega, Nat.add_mod_left]
          exact Nat.mod_eq_of_lt (by omega)
        have hge1 : f' ⟨L - 2, by omega⟩ = g ⟨L - 1, by omega⟩ := by
          rw [hg_ne ⟨L - 1, by omega⟩ (by dsimp; omega)]
          congr 1
        rw [h, hprev, hge1]
        exact mem_rev_ofFn g ⟨L - 1, by omega⟩ (by dsimp; omega)
      · apply mem_union_left
        have hnext : idx hL0 (L - 1 + 1) = ⟨0, by omega⟩ := by
          apply Fin.ext
          simp only [idx_val, show L - 1 + 1 = L by omega, Nat.mod_self]
        rw [h, hnext, ← hg_succ ⟨0, by omega⟩]
        exact mem_rev_ofFn g ⟨1, by omega⟩ (by dsimp; omega)
      · apply mem_union_left
        rcases mem_insert.mp huH with hu_eq | huC
        · rw [hu_eq, ← hg0]; exact mem_rev_ofFn g ⟨0, by omega⟩ (by dsimp; omega)
        · exfalso; exact (hw'S _).2 (h ▸ huC)
  have hg_out1 : ∀ (j : Fin (L + 1)) (z₁ z₂ : V),
      z₁ ∈ M (g j) → z₂ ∈ M (g j) → z₁ ∉ Hplus → z₂ ∉ Hplus → z₁ = z₂ := by
    intro j z₁ z₂ h1 h2 hz1 hz2
    by_cases hj0 : j.val = 0
    · have hjeq : j = ⟨0, by omega⟩ := Fin.ext hj0
      rw [hjeq, hg0] at h1 h2
      exact hu0_out1 z₁ z₂ h1 h2 hz1 hz2
    · have hgeq : g j = f' ⟨j.val - 1, by omega⟩ := hg_ne j hj0
      rw [hgeq] at h1 h2
      have h1w : z₁ = w' ⟨(j.val - 1) % 3, Nat.mod_lt _ (by decide)⟩ := by
        rcases hMf' ⟨j.val - 1, by omega⟩ z₁ h1 with h | h | h
        · exfalso; exact hz1 (mem_insert_of_mem (h ▸ mem_image_of_mem f' (mem_univ _)))
        · exfalso; exact hz1 (mem_insert_of_mem (h ▸ mem_image_of_mem f' (mem_univ _)))
        · exact h
      have h2w : z₂ = w' ⟨(j.val - 1) % 3, Nat.mod_lt _ (by decide)⟩ := by
        rcases hMf' ⟨j.val - 1, by omega⟩ z₂ h2 with h | h | h
        · exfalso; exact hz2 (mem_insert_of_mem (h ▸ mem_image_of_mem f' (mem_univ _)))
        · exfalso; exact hz2 (mem_insert_of_mem (h ▸ mem_image_of_mem f' (mem_univ _)))
        · exact h
      exact h1w.trans h2w.symm
  have hgS : ∀ j : Fin (L + 1), g j ∈ S := by
    intro j
    by_cases hj0 : j.val = 0
    · rw [show j = ⟨0, by omega⟩ from Fin.ext hj0, hg0]; exact (hw'S 0).1
    · rw [hg_ne j hj0]; exact hf'S _
  refine {
    m := L + 2
    P := P
    disj := hdisj
    cover := hcover
    l := l
    hl := by
      change l.toFinset = Hplus
      rw [← hg_img]; ext v; simp only [l, List.mem_toFinset, List.mem_ofFn, mem_image, mem_univ, true_and]
    a := a
    b := b
    par := par
    own := fun v hv => by
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hv
      simp only [a, hinvG j, P, mem_image, mem_filter, mem_univ, true_and]
      exact ⟨j, rfl, rfl⟩
    ab := fun v hv => by
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hv
      simpa [a, b, hinvG j] using hcol_ne_sup j
    charged := ?_ }
  apply relCharged_of_nested
  · intro j hj hp_none
    have hjL : j < L + 1 := hl_len ▸ hj
    rw [hl_get j hj] at hp_none ⊢
    simp only [b, hinvG ⟨j, hjL⟩]
    intro u hu
    have huS : u ∈ S := hMS _ (hgS _) hu
    have huH : u ∈ Hplus := outPar_none hp_none hu huS
    exact mem_union_right _ (hg_in_step j hjL u hu huH)
  · intro j hj z hp_some
    have hjL : j < L + 1 := hl_len ▸ hj
    rw [hl_get j hj] at hp_some ⊢
    simp only [b, hinvG ⟨j, hjL⟩]
    obtain ⟨hzM, hzS, hzH⟩ := outPar_some hp_some
    refine ⟨?_, ?_, empty_subset _⟩
    · simp only [mem_sdiff, mem_univ, true_and, mem_union, not_or, not_not]
      exact ⟨hzS, hzH⟩
    · intro u hu
      by_cases huH : u ∈ Hplus
      · exact mem_union_right _ (mem_insert_of_mem (hg_in_step j hjL u hu huH))
      · have huz : u = z := hg_out1 ⟨j, hjL⟩ u z hu hzM huH hzH
        subst huz
        exact mem_union_right _ (mem_insert_self _ _)
  · intro j j' hlt hj' z hp1 hp2
    have hj'L : j' < L + 1 := hl_len ▸ hj'
    have hjL : j < L + 1 := by omega
    rw [hl_get j (by omega)] at hp1 ⊢
    rw [hl_get j' hj'] at hp2
    simp only [b, hinvG ⟨j, hjL⟩]
    obtain ⟨hz1, _, hzH⟩ := outPar_some hp1
    obtain ⟨hz2, _, _⟩ := outPar_some hp2
    intro x hxP
    apply mem_union_left
    rcases (show j = 0 ∨ j = 1 ∨ (2 ≤ j ∧ j ≤ L - 2) ∨ j = L - 1 ∨ j = L by omega) with
      hj0 | hj1 | ⟨hj2, hjL2⟩ | hjL1 | hj_eq_L
    · subst hj0
      have hj'1 : j' ≠ 1 := by
        intro heq
        subst heq
        rw [hpar1_none] at hp2
        cases hp2
      have hsup0 : sup ⟨0, hjL⟩ = ⟨1, by omega⟩ := by dsimp only [sup]; rfl
      rw [hsup0, hP1, mem_singleton] at hxP
      subst hxP
      exact mem_rev_ofFn g ⟨1, by omega⟩ (by dsimp; omega)
    · subst hj1
      rw [hpar1_none] at hp1
      cases hp1
    · have hsup_eq : sup ⟨j, hjL⟩ = ⟨j + 1, by omega⟩ := by
        apply Fin.ext; dsimp [sup, col]; split_ifs <;> (try dsimp) <;> omega
      have hj'_succ : j' ≠ j + 1 := by
        intro heq
        subst heq
        have hg1 : g ⟨j, hjL⟩ = f' ⟨j - 1, by omega⟩ := hg_ne ⟨j, hjL⟩ (by dsimp; omega)
        have hg2 : g ⟨j + 1, hj'L⟩ = f' ⟨j, by omega⟩ := by simp [g]
        rw [hg1] at hz1; rw [hg2] at hz2
        have hedge : f' ⟨j - 1, by omega⟩ ∈ M (f' ⟨j, by omega⟩) := by
          have hc := (hcyc_f' ⟨j, by omega⟩).2
          have hidx : idx hL0 (j + L - 1) = ⟨j - 1, by omega⟩ := by
            apply Fin.ext; simp only [idx_val]
            rw [show j + L - 1 = L + (j - 1) by omega, Nat.add_mod_left]
            exact Nat.mod_eq_of_lt (by omega)
          rwa [hidx] at hc
        have hne1 : z ≠ f' ⟨j - 1, by omega⟩ :=
          fun e => hzH (e ▸ mem_insert_of_mem (mem_image_of_mem f' (mem_univ _)))
        have hne2 : f' ⟨j - 1, by omega⟩ ≠ f' ⟨j, by omega⟩ := fun e => by
          have := congrArg Fin.val (hf' e); simp at this; omega
        have hne3 : z ≠ f' ⟨j, by omega⟩ :=
          fun e => hzH (e ▸ mem_insert_of_mem (mem_image_of_mem f' (mem_univ _)))
        exact hTT z _ _ hne1 hne2 hne3 hz1 hedge hz2
      rw [hsup_eq, hPmid (j + 1) (by omega) (by omega), mem_singleton] at hxP
      subst hxP
      exact mem_rev_ofFn g ⟨j + 1, by omega⟩ (by dsimp; omega)
    · exfalso
      have hj'eq : j' = L := by omega
      have hg1 : g ⟨j, hjL⟩ = f' ⟨L - 2, by omega⟩ := by
        rw [hg_ne ⟨j, hjL⟩ (by dsimp; omega)]
        congr 1; exact Fin.ext (by dsimp; omega)
      have hg2 : g ⟨j', hj'L⟩ = f' ⟨L - 1, by omega⟩ := by
        rw [hg_ne ⟨j', hj'L⟩ (by dsimp; omega)]
        congr 1; exact Fin.ext (by dsimp; omega)
      rw [hg1] at hz1; rw [hg2] at hz2
      have hedge : f' ⟨L - 2, by omega⟩ ∈ M (f' ⟨L - 1, by omega⟩) := by
        have hc := (hcyc_f' ⟨L - 1, by omega⟩).2
        have hidx : idx hL0 (L - 1 + L - 1) = ⟨L - 2, by omega⟩ := by
          apply Fin.ext; simp only [idx_val]
          rw [show L - 1 + L - 1 = L + (L - 2) by omega, Nat.add_mod_left]
          exact Nat.mod_eq_of_lt (by omega)
        rwa [hidx] at hc
      have hne1 : z ≠ f' ⟨L - 2, by omega⟩ :=
        fun e => hzH (e ▸ mem_insert_of_mem (mem_image_of_mem f' (mem_univ _)))
      have hne2 : f' ⟨L - 2, by omega⟩ ≠ f' ⟨L - 1, by omega⟩ := fun e => by
        have := congrArg Fin.val (hf' e); simp at this; omega
      have hne3 : z ≠ f' ⟨L - 1, by omega⟩ :=
        fun e => hzH (e ▸ mem_insert_of_mem (mem_image_of_mem f' (mem_univ _)))
      exact hTT z _ _ hne1 hne2 hne3 hz1 hedge hz2
    · omega

/-- Given a strongly connected nonempty `S` with `IsClassS M`, `M v = ∅` outside `S`, and
`M v ⊆ S` on `S`, finds a nonempty certified piece `H ⊆ S` (`PieceCert M (univ \ S) H`). -/
theorem exists_piece_of_scc_classS {M : V → Finset V} {S : Finset V}
    (hS : S.Nonempty) (hM : IsClassS M)
    (_hout : ∀ v, v ∉ S → M v = ∅) (hin : ∀ v ∈ S, M v ⊆ S)
    (hscc : ∀ x ∈ S, ∀ y ∈ S, Reaches M x y) :
    ∃ H ⊆ S, H.Nonempty ∧ Nonempty (PieceCert M (univ \ S) H) := by
  classical
  obtain ⟨hloop, hTT, hdeg, hrec⟩ := hM
  have hinter : ∀ v ∈ S, M v ∩ S = M v := fun v hv => inter_eq_left.mpr (hin v hv)
  -- Case 1: some vertex in `S` has `(M v).card ≤ 1`
  by_cases h1 : ∃ v ∈ S, (M v).card ≤ 1
  · obtain ⟨v, hvS, hv1⟩ := h1
    have hp := singlePiece (N := M) (R := S) (L := ∅) hloop (fun _ _ h => nomatch h)
      (by rwa [hinter v hvS])
    rw [union_empty] at hp
    exact ⟨{v}, singleton_subset_iff.mpr hvS, singleton_nonempty v, hp⟩
  have hge2 : ∀ v ∈ S, 2 ≤ (M v).card := fun v hv => by
    by_contra hlt; exact h1 ⟨v, hv, by omega⟩
  -- Case 2: directed cycle inside `W_S := S.filter ((M ·).card = 2)`
  let W_S : Finset V := S.filter (fun v => (M v ∩ S).card = 2)
  have hWS_iff : ∀ v, v ∈ W_S ↔ v ∈ S ∧ (M v).card = 2 := by
    intro v
    simp only [W_S, mem_filter]
    exact ⟨fun ⟨hv, hc⟩ => ⟨hv, by rwa [hinter v hv] at hc⟩,
      fun ⟨hv, hc⟩ => ⟨hv, by rwa [hinter v hv]⟩⟩
  by_cases hacW : IsAcyclicIn M W_S
  · -- `W_S` is `M`-acyclic; split on whether `(digonGraph M)` has a cycle in `S`
    by_cases hcyc : ∃ g, HasCyc (digonGraph M) S g
    · -- Case 4: take a shortest cycle `c` of `digonGraph M` in `S`
      obtain ⟨L, ⟨hL3, ⟨c⟩⟩, hmin⟩ :
          ∃ L, HasCyc (digonGraph M) S L ∧ ∀ g', HasCyc (digonGraph M) S g' → L ≤ g' :=
        ⟨Nat.find hcyc, Nat.find_spec hcyc, fun g' h => Nat.find_min' hcyc h⟩
      have hcf := digonGraph_cliqueFree3 hTT
      have hL4 : 4 ≤ L := by
        by_contra hlt
        have h3 : L = 3 := by omega
        subst h3
        exact not_cliqueFree_of_cycIn3 c hcf
      have hL0 : 0 < L := by omega
      -- Check whether ANY shortest cycle `c' : CycIn (digonGraph M) S L` has a non-cycle `M`-chord
      let HasSpanChord (d : ℕ) : Prop :=
        2 ≤ d ∧ 2 * d ≤ L ∧ ∃ c' : CycIn (digonGraph M) S L, ∃ i : Fin L,
          c'.f i ∈ M (c'.f (idx hL0 (i.val + d)))
      by_cases hex_span : ∃ d, HasSpanChord d
      · -- Subcase 4a: minimum-span one-way chord arc `H'`
        obtain ⟨d, ⟨hd2, hdL, c', i₀, hch0⟩, hmin_d⟩ :
            ∃ d, HasSpanChord d ∧ ∀ d' < d, ¬ HasSpanChord d' :=
          ⟨Nat.find hex_span, Nat.find_spec hex_span, fun d' h => Nat.find_min hex_span h⟩
        let p : Fin (d + 1) → V := fun s => c'.f (idx hL0 (i₀.val + s.val))
        have hp_inj : Function.Injective p := by
          intro s₁ s₂ heq
          exact Fin.ext (c'.arc_inj hL0 (d := d) (by omega)
            (Nat.lt_succ_iff.mp s₁.isLt) (Nat.lt_succ_iff.mp s₂.isLt) heq)
        have hd3 : 3 ≤ d := by
          by_contra hlt3
          have hd_eq : d = 2 := by omega
          subst hd_eq
          have h01 := (c'.arc_adj hL3 (i₀.val + 0)).2.1
          have h12 := (c'.arc_adj hL3 (i₀.val + 1)).2.1
          simp only [Nat.add_zero] at h01
          rw [show i₀.val + 1 + 1 = i₀.val + 2 by omega] at h12
          have hne01 : p 0 ≠ p 1 := fun e => by have := hp_inj e; simp at this
          have hne12 : p 1 ≠ p 2 := fun e => by have := hp_inj e; simp at this
          have hne02 : p 0 ≠ p 2 := fun e => by have := hp_inj e; simp at this
          exact hTT (p 0) (p 1) (p 2) hne01 hne12 hne02 h01 h12
            (by simpa [p, idx_self] using hch0)
        have hnot_rev : p ⟨d, by omega⟩ ∉ M (p ⟨0, by omega⟩) := by
          intro hrev
          have hp0_eq : p ⟨0, by omega⟩ = c'.f i₀ := by simp [p, idx_self]
          have hpd_eq : p ⟨d, by omega⟩ = c'.f (idx hL0 (i₀.val + d)) := rfl
          have hne_dig : c'.f i₀ ≠ c'.f (idx hL0 (i₀.val + d)) := by
            intro e
            have hpe : p ⟨0, by omega⟩ = p ⟨d, by omega⟩ := by
              rw [hp0_eq, hpd_eq]; exact e
            have := congrArg Fin.val (hp_inj hpe); dsimp at this; omega
          have hadj_dig : (digonGraph M).Adj (c'.f i₀) (c'.f (idx hL0 (i₀.val + d))) :=
            ⟨hne_dig, hch0, by rwa [← hp0_eq, ← hpd_eq]⟩
          have hcadj := c'.chordless hL3 hmin hadj_dig
          rw [cyc_adj_val (by omega)] at hcadj
          have hi0 := i₀.isLt
          simp only [idx_val] at hcadj
          by_cases hlt : i₀.val + d < L
          · rw [Nat.mod_eq_of_lt hlt] at hcadj
            rcases hcadj with (h | ⟨h1, h2⟩) | (h | ⟨h1, h2⟩) <;> omega
          · rw [show i₀.val + d = L + (i₀.val + d - L) by omega, Nat.add_mod_left] at hcadj
            rw [Nat.mod_eq_of_lt (by omega)] at hcadj
            rcases hcadj with (h | ⟨h1, h2⟩) | (h | ⟨h1, h2⟩) <;> omega
        have hinternal : ∀ s t : Fin (d + 1), p t ∈ M (p s) →
            t.val + 1 = s.val ∨ s.val + 1 = t.val ∨ (s.val = d ∧ t.val = 0) := by
          intro s t hst
          have hs := s.isLt; have ht := t.isLt
          rcases lt_trichotomy t.val s.val with hlt | heq | hgt
          · by_cases h1 : t.val + 1 = s.val
            · exact Or.inl h1
            · right; right
              have hd' : 2 ≤ s.val - t.val := by omega
              by_cases hlt_d : s.val - t.val < d
              · exfalso
                refine hmin_d (s.val - t.val) hlt_d ⟨hd', by omega, c', idx hL0 (i₀.val + t.val), ?_⟩
                have hidx_eq : idx hL0 ((idx hL0 (i₀.val + t.val)).val + (s.val - t.val)) =
                    idx hL0 (i₀.val + s.val) := by
                  apply Fin.ext
                  simp only [idx_val, Nat.mod_add_mod, show i₀.val + t.val + (s.val - t.val) = i₀.val + s.val by omega]
                rwa [hidx_eq]
              · omega
          · exfalso; exact hloop _ (Fin.ext heq ▸ hst)
          · by_cases h1 : s.val + 1 = t.val
            · exact Or.inr (Or.inl h1)
            · exfalso
              have hd' : 2 ≤ t.val - s.val := by omega
              by_cases hlt_d : t.val - s.val < d
              · -- Reverse `c'` to get a forward chord of span `t - s < d`!
                let crev := cycRev hL3 c'
                let irev : Fin L := idx hL0 (L - (idx hL0 (i₀.val + t.val)).val)
                refine hmin_d (t.val - s.val) hlt_d ⟨hd', by omega, crev, irev, ?_⟩
                have hc_t : crev.f irev = p t := by
                  simp only [crev, cycRev, irev, p]
                  congr 1; apply Fin.ext
                  simp only [idx_val]
                  set x := (i₀.val + t.val) % L
                  have hx : x < L := Nat.mod_lt _ hL0
                  by_cases hx0 : x = 0
                  · simp [hx0]
                  · rw [Nat.mod_eq_of_lt (by omega : L - x < L), show L - (L - x) = x by omega,
                      Nat.mod_eq_of_lt hx]
                have hc_s : crev.f (idx hL0 (irev.val + (t.val - s.val))) = p s := by
                  simp only [crev, cycRev, irev, p]
                  congr 1; apply Fin.ext
                  simp only [idx_val]
                  have hcong : ((L - (i₀.val + t.val) % L) % L + (t.val - s.val)) % L =
                      (L - (i₀.val + s.val) % L) % L := by
                    have hlt_t := Nat.mod_lt (i₀.val + t.val) hL0
                    have hlt_s := Nat.mod_lt (i₀.val + s.val) hL0
                    have hrel : (i₀.val + t.val) % L = ((i₀.val + s.val) % L + (t.val - s.val)) % L := by
                      rw [Nat.mod_add_mod, show i₀.val + s.val + (t.val - s.val) = i₀.val + t.val by omega]
                    rw [Nat.mod_add_mod]
                    set xs := (i₀.val + s.val) % L
                    set xt := (i₀.val + t.val) % L
                    by_cases hsum : xs + (t.val - s.val) < L
                    · have hxt : xt = xs + (t.val - s.val) := by rw [hrel, Nat.mod_eq_of_lt hsum]
                      rw [show L - xt + (t.val - s.val) = L - xs by omega]
                    · have hxt : xt = xs + (t.val - s.val) - L := by
                        have h1 : (xs + (t.val - s.val)) % L = xs + (t.val - s.val) - L := by
                          conv_lhs =>
                            rw [show xs + (t.val - s.val) = L + (xs + (t.val - s.val) - L) by omega]
                          rw [Nat.add_mod_left]
                          exact Nat.mod_eq_of_lt (by omega)
                        omega
                      have hxs0 : xs ≠ 0 := by omega
                      rw [show L - xt + (t.val - s.val) = L + (L - xs) by omega, Nat.add_mod_left]
                  rw [hcong]
                  set xs := (i₀.val + s.val) % L
                  have hxs : xs < L := Nat.mod_lt _ hL0
                  by_cases hxs0 : xs = 0
                  · simp [hxs0]
                  · rw [Nat.mod_eq_of_lt (by omega : L - xs < L), show L - (L - xs) = xs by omega,
                      Nat.mod_eq_of_lt hxs]
                rwa [hc_t, hc_s]
              · have hs0 : s = ⟨0, by omega⟩ := Fin.ext (by dsimp; omega)
                have htd : t = ⟨d, by omega⟩ := Fin.ext (by dsimp; omega)
                rw [hs0, htd] at hst
                exact hnot_rev hst
        have hdig : ∀ s : Fin (d + 1), ∀ hs : s.val < d,
            p ⟨s.val + 1, by omega⟩ ∈ M (p s) ∧ p s ∈ M (p ⟨s.val + 1, by omega⟩) := by
          intro s hs
          have hadj := c'.arc_adj hL3 (i₀.val + s.val)
          rw [show i₀.val + s.val + 1 = i₀.val + (s.val + 1) by omega] at hadj
          exact ⟨hadj.2.2, hadj.2.1⟩
        have hout1 : ∀ s : Fin (d + 1), ∀ w₁ w₂, w₁ ∈ M (p s) → w₂ ∈ M (p s) →
            w₁ ∉ univ.image p → w₂ ∉ univ.image p → w₁ = w₂ := by
          intro s w₁ w₂ h1 h2 hw1 hw2
          by_contra hne
          by_cases hs0 : s.val = 0
          · -- `(M (p 0)).card ≤ 2` by `Class S` since `p 0 ∈ M (p d)` and `p d ∉ M (p 0)`!
            have hse : s = ⟨0, by omega⟩ := Fin.ext hs0
            rw [hse] at h1 h2
            have hp0_2 : (M (p ⟨0, by omega⟩)).card ≤ 2 := by
              have hle3 := hdeg (p ⟨0, by omega⟩)
              by_contra hgt2
              have hc3 : (M (p ⟨0, by omega⟩)).card = 3 := by omega
              have hp0d : p ⟨0, by omega⟩ ∈ M (p ⟨d, by omega⟩) := by
                simpa [p, idx_self] using hch0
              exact hnot_rev (hrec _ hc3 _ hp0d)
            have hp1_in : p ⟨1, by omega⟩ ∈ M (p ⟨0, by omega⟩) :=
              (hdig ⟨0, by omega⟩ (by dsimp; omega)).1
            have hp1_mem : p ⟨1, by omega⟩ ∈ univ.image p := mem_image_of_mem p (mem_univ _)
            have h3 := three_le_card hp1_in h1 h2
              (fun e => hw1 (e ▸ hp1_mem)) (fun e => hw2 (e ▸ hp1_mem)) hne
            omega
          · -- `s ≥ 1`: `p (s - 1)` and `(s < d ? p (s + 1) : p 0)` are 2 distinct parents in `image p`!
            have hs_lt := s.isLt
            let u₁ : V := p ⟨s.val - 1, by omega⟩
            let u₂ : V := if hsd : s.val < d then p ⟨s.val + 1, by omega⟩ else p ⟨0, by omega⟩
            have hu1_in : u₁ ∈ M (p s) := by
              have hprev_dig := (hdig ⟨s.val - 1, by omega⟩ (by dsimp; omega)).2
              have hseq : (⟨(⟨s.val - 1, by omega⟩ : Fin (d + 1)).val + 1, by dsimp; omega⟩ : Fin (d + 1)) = s :=
                Fin.ext (by dsimp; omega)
              rw [hseq] at hprev_dig
              exact hprev_dig
            have hu2_in : u₂ ∈ M (p s) := by
              dsimp only [u₂]
              split_ifs with hsd
              · exact (hdig s hsd).1
              · have hps : p s = c'.f (idx hL0 (i₀.val + d)) := by
                  dsimp only [p]; congr 2; omega
                rw [hps]; simpa [p, idx_self] using hch0
            have hu12 : u₁ ≠ u₂ := by
              dsimp only [u₁, u₂]
              split_ifs with hsd
              · intro e; have := congrArg Fin.val (hp_inj e); simp at this; try omega
              · intro e; have := congrArg Fin.val (hp_inj e); simp at this; try omega
            have hu1_mem : u₁ ∈ univ.image p := mem_image_of_mem p (mem_univ _)
            have hu2_mem : u₂ ∈ univ.image p := by
              dsimp only [u₂]; split_ifs <;> exact mem_image_of_mem p (mem_univ _)
            have h4 := four_le_card hu1_in hu2_in h1 h2
              hu12 (fun e => hw1 (e ▸ hu1_mem)) (fun e => hw2 (e ▸ hu1_mem))
              (fun e => hw1 (e ▸ hu2_mem)) (fun e => hw2 (e ▸ hu2_mem)) hne
            have := hdeg (p s); omega
        exact ⟨univ.image p,
          fun x hx => by obtain ⟨s, -, rfl⟩ := mem_image.mp hx; exact c'.mem _,
          ⟨p ⟨0, by omega⟩, mem_image_of_mem _ (mem_univ _)⟩,
          ⟨minChordArc_pieceCert hd3 p hp_inj (fun _ => c'.mem _) hin hTT hdig hinternal hout1⟩⟩
      · -- No shortest cycle has ANY non-cycle `M`-chord! In particular `c` is `M`-chordless!
        have hno_chord : ∀ i j : Fin L, c.f j ∈ M (c.f i) →
            j = idx hL0 (i.val + 1) ∨ j = idx hL0 (i.val + L - 1) := by
          intro i j hij
          have hadj_or : (cycleGraph L).Adj i j := by
            by_contra hnot_adj
            have hij_ne : i ≠ j := by rintro rfl; exact hloop _ hij
            have hi := i.isLt; have hj := j.isLt
            let d₁ := (i.val + L - j.val) % L
            let d₂ := (j.val + L - i.val) % L
            have hd1_ge2 : 2 ≤ d₁ := by
              rw [cyc_adj_val (by omega)] at hnot_adj
              dsimp only [d₁]
              rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij_ne) with hlt | hgt
              · rw [Nat.mod_eq_of_lt (by omega)]; omega
              · rw [show i.val + L - j.val = L + (i.val - j.val) by omega, Nat.add_mod_left]
                rw [Nat.mod_eq_of_lt (by omega)]; omega
            have hd2_ge2 : 2 ≤ d₂ := by
              rw [cyc_adj_val (by omega)] at hnot_adj
              dsimp only [d₂]
              rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij_ne) with hlt | hgt
              · rw [show j.val + L - i.val = L + (j.val - i.val) by omega, Nat.add_mod_left]
                rw [Nat.mod_eq_of_lt (by omega)]; omega
              · rw [Nat.mod_eq_of_lt (by omega)]; omega
            have hsum_L : d₁ + d₂ = L := by
              dsimp only [d₁, d₂]
              rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij_ne) with hlt | hgt
              · rw [Nat.mod_eq_of_lt (show i.val + L - j.val < L by omega),
                  show j.val + L - i.val = L + (j.val - i.val) by omega, Nat.add_mod_left]
                rw [Nat.mod_eq_of_lt (by omega)]; omega
              · rw [Nat.mod_eq_of_lt (show j.val + L - i.val < L by omega),
                  show i.val + L - j.val = L + (i.val - j.val) by omega, Nat.add_mod_left]
                rw [Nat.mod_eq_of_lt (by omega)]; omega
            rcases le_total d₁ d₂ with hle | hle
            · refine hex_span ⟨d₁, hd1_ge2, by omega, c, j, ?_⟩
              have hidx : idx hL0 (j.val + d₁) = i := by
                apply Fin.ext; simp only [idx_val, d₁, Nat.add_mod_mod]
                rw [show j.val + (i.val + L - j.val) = L + i.val by omega, Nat.add_mod_left,
                  Nat.mod_eq_of_lt hi]
              rwa [hidx]
            · let crev := cycRev hL3 c
              let jrev : Fin L := idx hL0 (L - j.val)
              refine hex_span ⟨d₂, hd2_ge2, by omega, crev, jrev, ?_⟩
              have hcj : crev.f jrev = c.f j := by
                simp only [crev, cycRev, jrev]
                congr 1; apply Fin.ext; simp only [idx_val]
                by_cases hj0 : j.val = 0
                · simp [hj0]
                · rw [Nat.mod_eq_of_lt (by omega : L - j.val < L),
                    show L - (L - j.val) = j.val by omega, Nat.mod_eq_of_lt hj]
              have hci : crev.f (idx hL0 (jrev.val + d₂)) = c.f i := by
                simp only [crev, cycRev, jrev]
                congr 1; apply Fin.ext; simp only [idx_val]
                have hcong : ((L - j.val) % L + d₂) % L = (L - i.val) % L := by
                  rw [Nat.mod_add_mod]
                  dsimp only [d₂]
                  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij_ne) with hlt | hgt
                  · rw [show j.val + L - i.val = L + (j.val - i.val) by omega, Nat.add_mod_left]
                    rw [Nat.mod_eq_of_lt (show j.val - i.val < L by omega),
                      show L - j.val + (j.val - i.val) = L - i.val by omega]
                  · rw [Nat.mod_eq_of_lt (show j.val + L - i.val < L by omega)]
                    by_cases hj0 : j.val = 0
                    · rw [hj0, Nat.sub_zero, Nat.zero_add, Nat.add_mod_left]
                    · rw [show L - j.val + (j.val + L - i.val) = L + (L - i.val) by omega,
                        Nat.add_mod_left]
                rw [hcong]
                by_cases hi0 : i.val = 0
                · simp [hi0]
                · rw [Nat.mod_eq_of_lt (by omega : L - i.val < L),
                    show L - (L - i.val) = i.val by omega, Nat.mod_eq_of_lt hi]
              rwa [hcj, hci]
          rw [cyc_adj_val (by omega)] at hadj_or
          have hi := i.isLt; have hj := j.isLt
          rcases hadj_or with (h | ⟨h1, h2⟩) | (h | ⟨h1, h2⟩)
          · right; apply Fin.ext; simp only [idx_val]
            rw [show i.val + L - 1 = L + j.val by omega, Nat.add_mod_left, Nat.mod_eq_of_lt hj]
          · right; apply Fin.ext; simp only [idx_val]
            rw [h1, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]; omega
          · left; apply Fin.ext; simp only [idx_val]
            rw [← h, Nat.mod_eq_of_lt hj]
          · left; apply Fin.ext; simp only [idx_val]
            rw [h2, Nat.mod_self, h1]
        have hcyc_M : ∀ i : Fin L,
            c.f (idx hL0 (i.val + 1)) ∈ M (c.f i) ∧
            c.f (idx hL0 (i.val + L - 1)) ∈ M (c.f i) := by
          intro i
          have h1 := (c.arc_adj hL3 i.val).2.2
          rw [idx_self] at h1
          have h2 := (c.arc_adj hL3 (i.val + L - 1)).2.1
          have hidx2 : idx hL0 (i.val + L - 1 + 1) = i := by
            apply Fin.ext; simp only [idx_val, show i.val + L - 1 + 1 = L + i.val by omega,
              Nat.add_mod_left, Nat.mod_eq_of_lt i.isLt]
          rw [hidx2] at h2
          exact ⟨h1, h2⟩
        have hout1_c : ∀ i : Fin L, ∀ w₁ w₂, w₁ ∈ M (c.f i) → w₂ ∈ M (c.f i) →
            w₁ ∉ univ \ S → w₁ ∉ univ.image c.f → w₂ ∉ univ \ S → w₂ ∉ univ.image c.f →
            w₁ = w₂ := by
          intro i w₁ w₂ h1 h2 _ hw1C _ hw2C
          by_contra hne
          have hc1 := (hcyc_M i).1
          have hc2 := (hcyc_M i).2
          have hne_c : c.f (idx hL0 (i.val + 1)) ≠ c.f (idx hL0 (i.val + L - 1)) := by
            intro e
            have hev := congrArg Fin.val (c.inj e)
            simp only [idx_val] at hev
            have hi := i.isLt
            by_cases hi0 : i.val = 0
            · rw [hi0, Nat.zero_add, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hev
              omega
            · rw [show i.val + L - 1 = L + (i.val - 1) by omega, Nat.add_mod_left] at hev
              rw [Nat.mod_eq_of_lt (show i.val - 1 < L by omega)] at hev
              by_cases hil : i.val + 1 = L
              · rw [hil, Nat.mod_self] at hev; omega
              · rw [Nat.mod_eq_of_lt (by omega)] at hev; omega
          have hm1 : c.f (idx hL0 (i.val + 1)) ∈ univ.image c.f := mem_image_of_mem _ (mem_univ _)
          have hm2 : c.f (idx hL0 (i.val + L - 1)) ∈ univ.image c.f := mem_image_of_mem _ (mem_univ _)
          have h4 := four_le_card hc1 hc2 h1 h2 hne_c
            (fun e => hw1C (e ▸ hm1)) (fun e => hw2C (e ▸ hm1))
            (fun e => hw1C (e ▸ hm2)) (fun e => hw2C (e ▸ hm2)) hne
          have := hdeg (c.f i); omega
        have hTT_c : ∀ i : Fin L, ∀ w, w ∉ univ \ S → w ∉ univ.image c.f →
            w ∈ M (c.f i) → w ∈ M (c.f (idx hL0 (i.val + 1))) → False := by
          intro i w _ hwC h1 h2
          have hne1 : w ≠ c.f i := fun e => hwC (e ▸ mem_image_of_mem _ (mem_univ _))
          have hne2 : c.f i ≠ c.f (idx hL0 (i.val + 1)) := fun e => by
            have := (c.arc_adj hL3 i.val).1
            rw [idx_self] at this
            exact this e
          have hne3 : w ≠ c.f (idx hL0 (i.val + 1)) :=
            fun e => hwC (e ▸ mem_image_of_mem _ (mem_univ _))
          have hedge := (c.arc_adj hL3 i.val).2.1
          rw [idx_self] at hedge
          exact hTT w (c.f i) (c.f (idx hL0 (i.val + 1))) hne1 hne2 hne3 h1 hedge h2
        -- Subcase 4b vs 4c: non-stride-3 (`Theorem DC`) vs stride-3 (`augmentedStride3_pieceCert`)
        by_cases hs3 : IsStride3Cycle M (univ \ S) c.f
        · -- Subcase 4c: `IsStride3Cycle M (univ \ S) c.f`
          obtain ⟨h3L, w, hw, hw_in⟩ := hs3
          have hL6 : 6 ≤ L := by obtain ⟨k, hk⟩ := h3L; omega
          have hwS : ∀ r, w r ∈ S ∧ w r ∉ univ.image c.f := by
            intro r
            obtain ⟨h1, h2⟩ := hw r
            exact ⟨by simp at h1; exact h1, h2⟩
          have hMc : ∀ i : Fin L, ∀ u ∈ M (c.f i),
              u = c.f (idx hL0 (i.val + L - 1)) ∨
              u = c.f (idx hL0 (i.val + 1)) ∨
              u = w ⟨i.val % 3, Nat.mod_lt _ (by decide)⟩ := by
            intro i u hu
            by_cases huC : u ∈ univ.image c.f
            · obtain ⟨j, -, rfl⟩ := mem_image.mp huC
              rcases hno_chord i j hu with h | h
              · exact Or.inr (Or.inl (congrArg c.f h))
              · exact Or.inl (congrArg c.f h)
            · right; right
              exact hout1_c i u (w ⟨i.val % 3, Nat.mod_lt _ (by decide)⟩) hu (hw_in i)
                (by simp [hin _ (c.mem i) hu]) huC (by simp [(hwS _).1]) (hwS _).2
          have hcard3_c : ∀ i : Fin L, (M (c.f i)).card = 3 := by
            intro i
            have hc1 := (hcyc_M i).1
            have hc2 := (hcyc_M i).2
            have hw_i := hw_in i
            have hne_c : c.f (idx hL0 (i.val + 1)) ≠ c.f (idx hL0 (i.val + L - 1)) := by
              intro e
              have hev := congrArg Fin.val (c.inj e)
              simp only [idx_val] at hev
              have hi := i.isLt
              by_cases hi0 : i.val = 0
              · rw [hi0, Nat.zero_add, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hev
                omega
              · rw [show i.val + L - 1 = L + (i.val - 1) by omega, Nat.add_mod_left,
                  Nat.mod_eq_of_lt (show i.val - 1 < L by omega)] at hev
                by_cases hil : i.val + 1 = L
                · rw [hil, Nat.mod_self] at hev; omega
                · rw [Nat.mod_eq_of_lt (by omega)] at hev; omega
            have h3 := three_le_card hc1 hc2 hw_i hne_c
              (fun e => (hwS _).2 (e ▸ mem_image_of_mem c.f (mem_univ _)))
              (fun e => (hwS _).2 (e ▸ mem_image_of_mem c.f (mem_univ _)))
            have := hdeg (c.f i); omega
          -- Strong connectivity gives an arc from `C` to `S \ C`
          have hex_exit : ∃ (i₀ : Fin L) (y : V), y ∉ univ.image c.f ∧ c.f i₀ ∈ M y := by
            have hreach := hscc (c.f ⟨0, hL0⟩) (c.mem _) (w 0) (hwS 0).1
            have step_exit : ∀ {a b : V}, Reaches M a b → a ∈ univ.image c.f → b ∉ univ.image c.f →
                ∃ (i₀ : Fin L) (y : V), y ∉ univ.image c.f ∧ c.f i₀ ∈ M y := by
              intro a b hab
              induction hab with
              | refl => intro ha hb; exact absurd ha hb
              | @tail u v huv hvw ih =>
                intro ha hv_not
                by_cases huC : u ∈ univ.image c.f
                · obtain ⟨i₀, -, rfl⟩ := mem_image.mp huC
                  exact ⟨i₀, v, hv_not, hvw⟩
                · exact ih ha huC
            exact step_exit hreach (mem_image_of_mem _ (mem_univ _)) (hwS 0).2
          obtain ⟨i₀, y, hyC, hfi0_y⟩ := hex_exit
          have hy_in_M : y ∈ M (c.f i₀) := hrec (c.f i₀) (hcard3_c i₀) y hfi0_y
          let r₀ : Fin 3 := ⟨i₀.val % 3, Nat.mod_lt _ (by decide)⟩
          have hy_eq : y = w r₀ := by
            rcases hMc i₀ y hy_in_M with h | h | h
            · exact absurd (h ▸ mem_image_of_mem _ (mem_univ _)) hyC
            · exact absurd (h ▸ mem_image_of_mem _ (mem_univ _)) hyC
            · exact h
          subst hy_eq
          -- `c.share` forces `w r₀` to have NO other `M`-parent on `C` and `(M (w r₀)).card = 2`!
          have hwr0_unique_C : ∀ k : Fin L, c.f k ∈ M (w r₀) → k = i₀ := by
            intro k hfk
            by_contra hne
            have hwr0_fk : w r₀ ∈ M (c.f k) := hrec (c.f k) (hcard3_c k) (w r₀) hfk
            have hadj_i0 : (digonGraph M).Adj (w r₀) (c.f i₀) :=
              ⟨fun e => (hwS r₀).2 (e ▸ mem_image_of_mem _ (mem_univ _)), hw_in i₀, hfi0_y⟩
            have hadj_k : (digonGraph M).Adj (w r₀) (c.f k) :=
              ⟨fun e => (hwS r₀).2 (e ▸ mem_image_of_mem _ (mem_univ _)), hwr0_fk, hfk⟩
            have hw_ne_C : ∀ t, c.f t ≠ w r₀ :=
              fun t e => (hwS r₀).2 (e ▸ mem_image_of_mem _ (mem_univ _))
            rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
            · have h4 := (c.share hL4 hmin (hwS r₀).1 hw_ne_C hlt hadj_k hadj_i0).1; omega
            · have h4 := (c.share hL4 hmin (hwS r₀).1 hw_ne_C hgt hadj_i0 hadj_k).1; omega
          have hwr0_card2 : (M (w r₀)).card = 2 := by
            have hge := hge2 (w r₀) (hwS r₀).1
            have hle := hdeg (w r₀)
            by_contra hne2
            have hc3 : (M (w r₀)).card = 3 := by omega
            let k₁ : Fin L := idx hL0 (i₀.val + 3)
            have hk1_mod : k₁.val % 3 = r₀.val := by
              simp only [k₁, idx_val, r₀]
              rw [Nat.mod_mod_of_dvd _ h3L]
              omega
            have hwr0_k1 : w r₀ ∈ M (c.f k₁) := by
              have := hw_in k₁
              convert this using 2
              exact Fin.ext hk1_mod.symm
            have hfk1 : c.f k₁ ∈ M (w r₀) := hrec (w r₀) hc3 (c.f k₁) hwr0_k1
            have heq := hwr0_unique_C k₁ hfk1
            have hev := congrArg Fin.val heq
            simp only [k₁, idx_val] at hev
            have hi0 := i₀.isLt
            rcases Nat.lt_or_ge (i₀.val + 3) L with hlt | hge'
            · rw [Nat.mod_eq_of_lt hlt] at hev; omega
            · rw [show i₀.val + 3 = L + (i₀.val + 3 - L) by omega, Nat.add_mod_left] at hev
              rw [Nat.mod_eq_of_lt (by omega)] at hev; omega
          -- Rotate `c.f` by `i₀` and shift `w` by `r₀`
          let f' : Fin L → V := fun t => c.f (idx hL0 (i₀.val + t.val))
          let w' : Fin 3 → V := fun r => w ⟨(r₀.val + r.val) % 3, Nat.mod_lt _ (by decide)⟩
          have hf'_inj : Function.Injective f' := by
            intro t₁ t₂ heq
            exact Fin.ext (c.arc_inj hL0 (d := L - 1) (by omega)
              (by have := t₁.isLt; omega) (by have := t₂.isLt; omega) heq)
          have hf'_img : univ.image f' = univ.image c.f := by
            ext v
            simp only [mem_image, mem_univ, true_and, f']
            constructor
            · rintro ⟨t, rfl⟩; exact ⟨_, rfl⟩
            · rintro ⟨k, rfl⟩
              refine ⟨idx hL0 (k.val + L - i₀.val), ?_⟩
              congr 1; apply Fin.ext; simp only [idx_val, Nat.add_mod_mod]
              have hi0 := i₀.isLt; have hk := k.isLt
              rw [show i₀.val + (k.val + L - i₀.val) = L + k.val by omega, Nat.add_mod_left,
                Nat.mod_eq_of_lt hk]
          have hw'0 : w' 0 = w r₀ := by
            simp only [w', Fin.val_zero, Nat.add_zero]
            congr 1; exact Fin.ext (Nat.mod_eq_of_lt r₀.isLt)
          have hMf' : ∀ t : Fin L, ∀ u ∈ M (f' t),
              u = f' (idx hL0 (t.val + L - 1)) ∨
              u = f' (idx hL0 (t.val + 1)) ∨
              u = w' ⟨t.val % 3, Nat.mod_lt _ (by decide)⟩ := by
            intro t u hu
            rcases hMc (idx hL0 (i₀.val + t.val)) u hu with h | h | h
            · left; rw [h]; simp only [f']
              congr 1; apply Fin.ext; simp only [idx_val]
              have ht := t.isLt
              have hmod_add : ((i₀.val + t.val) % L + L - 1) % L = (i₀.val + (t.val + L - 1) % L) % L := by
                have hlt := Nat.mod_lt (i₀.val + t.val) hL0
                rw [show (i₀.val + t.val) % L + L - 1 = (i₀.val + t.val) % L + (L - 1) by omega,
                  Nat.mod_add_mod, Nat.add_mod_mod,
                  show i₀.val + t.val + (L - 1) = i₀.val + (t.val + L - 1) by omega]
              exact hmod_add
            · right; left; rw [h]; simp only [f']
              congr 1; apply Fin.ext; simp only [idx_val, Nat.mod_add_mod, Nat.add_mod_mod, Nat.add_assoc]
            · right; right; rw [h]; simp only [w']
              congr 1; apply Fin.ext; simp only [idx_val]
              obtain ⟨q, hq⟩ := h3L
              have hmod3 : ((i₀.val + t.val) % L) % 3 = (i₀.val % 3 + t.val % 3) % 3 := by
                have hdiv : 3 ∣ L := ⟨q, hq⟩
                rw [Nat.mod_mod_of_dvd _ hdiv, Nat.add_mod]
              simpa [r₀] using hmod3
          have hcyc_f' : ∀ t : Fin L, f' (idx hL0 (t.val + 1)) ∈ M (f' t) ∧
              f' (idx hL0 (t.val + L - 1)) ∈ M (f' t) := by
            intro t
            obtain ⟨h1, h2⟩ := hcyc_M (idx hL0 (i₀.val + t.val))
            refine ⟨?_, ?_⟩
            · convert h1 using 2; apply Fin.ext
              simp [idx_val, Nat.mod_add_mod, Nat.add_mod_mod, Nat.add_assoc]
            · convert h2 using 2; apply Fin.ext
              simp only [idx_val, Nat.add_mod_mod]
              have hlt := Nat.mod_lt (i₀.val + t.val) hL0
              rw [show (i₀.val + t.val) % L + L - 1 = (i₀.val + t.val) % L + (L - 1) by omega,
                Nat.mod_add_mod, show i₀.val + t.val + (L - 1) = i₀.val + (t.val + L - 1) by omega]
          have hu0_C : ∀ t : Fin L, f' t ∈ M (w' 0) → t = ⟨0, hL0⟩ := by
            intro t hft
            rw [hw'0] at hft
            have hidx := hwr0_unique_C _ hft
            have ht := t.isLt
            have h0 : idx hL0 (i₀.val + 0) = i₀ := by simp [idx_self]
            exact Fin.ext (c.arc_inj hL0 (d := L - 1) (by omega) (by omega) (by omega)
              (congrArg c.f (hidx.trans h0.symm)))
          have hu0_out1 : ∀ z₁ z₂, z₁ ∈ M (w' 0) → z₂ ∈ M (w' 0) →
              z₁ ∉ insert (w' 0) (univ.image f') → z₂ ∉ insert (w' 0) (univ.image f') →
              z₁ = z₂ := by
            intro z₁ z₂ hz1 hz2 hnot1 hnot2
            by_contra hne
            have hf0_in : f' ⟨0, hL0⟩ ∈ M (w' 0) := by
              simpa [hw'0, f', idx_self] using hfi0_y
            have hf0_mem : f' ⟨0, hL0⟩ ∈ insert (w' 0) (univ.image f') :=
              mem_insert_of_mem (mem_image_of_mem _ (mem_univ _))
            have h3 := three_le_card hf0_in hz1 hz2
              (fun e => hnot1 (e ▸ hf0_mem)) (fun e => hnot2 (e ▸ hf0_mem)) hne
            rw [hw'0, hwr0_card2] at h3; omega
          refine ⟨insert (w' 0) (univ.image f'),
            insert_subset (hw'0 ▸ (hwS r₀).1) (hf'_img.symm ▸ fun x hx => by
              obtain ⟨k, -, rfl⟩ := mem_image.mp hx; exact c.mem k),
            insert_nonempty _ _,
            ⟨augmentedStride3_pieceCert hL6 h3L f' hf'_inj (fun _ => c.mem _) hin hTT w'
              (fun r => ⟨(hwS _).1, hf'_img.symm ▸ (hwS _).2⟩) hMf' hcyc_f'
              (by simpa [hw'0, f', idx_self] using hfi0_y) hu0_out1 hu0_C (hloop _)⟩⟩
        · -- Subcase 4b: `¬ IsStride3Cycle M (univ \ S) c.f` -> `Theorem DC`!
          obtain ⟨cert, _⟩ := digonCycle_pieceCert_of_not_stride3 hL4 c.inj hTT_c hno_chord
            hout1_c hs3
          exact ⟨univ.image c.f,
            fun x hx => by obtain ⟨i, -, rfl⟩ := mem_image.mp hx; exact c.mem i,
            ⟨c.f ⟨0, hL0⟩, mem_image_of_mem _ (mem_univ _)⟩,
            ⟨cert⟩⟩
    · -- Case 3: `digonGraph M` is acyclic on `S`, and `W_S` is `M`-acyclic -> `bdirPiece` on `S`!
      have hac_dig : ((digonGraph M).induce (S : Set V)).IsAcyclic := by
        rw [isAcyclic_iff_free_cycleGraph]
        intro n hn hcont
        obtain ⟨φ⟩ := hcont
        exact hcyc ⟨n, hn, ⟨⟨fun i => (φ i).val, fun i j h => φ.injective (Subtype.ext h),
          fun i => Finset.mem_coe.mp (φ i).prop, fun i j hij => φ.toHom.map_adj hij⟩⟩⟩
      obtain ⟨col⟩ := hac_dig.colorable_two
      let κ : V → Fin 2 := fun v => if h : v ∈ S then col ⟨v, by simpa using h⟩ else 0
      have hκ : ∀ u v, u ∈ S → v ∈ S → (digonGraph M).Adj u v → κ u ≠ κ v := by
        intro u v hu hv huv
        simp only [κ, hu, hv, ↓reduceDIte]
        exact col.valid (show ((digonGraph M).induce (S : Set V)).Adj ⟨u, by simpa using hu⟩
          ⟨v, by simpa using hv⟩ from huv)
      have hclass : ∀ k : Fin 2, IsAcyclicIn M (S.filter (κ · = k)) := by
        intro k
        by_contra hnot_ac
        unfold IsAcyclicIn at hnot_ac
        push Not at hnot_ac
        obtain ⟨T, hTS, hTne, hsrc⟩ := hnot_ac
        obtain ⟨ℓ, hℓ, ⟨dc⟩⟩ := exists_hasDCyc_of_sourceless hloop hTne hsrc
        by_cases hallW : ∀ i : Fin ℓ, dc.f i ∈ W_S
        · exact not_hasDCyc_of_isAcyclicIn hacW
            ⟨hℓ, ⟨{ pos := dc.pos, f := dc.f, inj := dc.inj, mem := hallW, arc := dc.arc }⟩⟩
        · push Not at hallW
          obtain ⟨i, hiW⟩ := hallW
          have hiS : dc.f i ∈ S := (mem_filter.mp (hTS (dc.mem i))).1
          have hi3 : (M (dc.f i)).card = 3 := by
            have hge := hge2 _ hiS
            have hle := hdeg (dc.f i)
            have hne2 : (M (dc.f i)).card ≠ 2 := fun e => hiW ((hWS_iff _).mpr ⟨hiS, e⟩)
            omega
          let prev := idx dc.pos (i.val + ℓ - 1)
          have hidx_succ : idx dc.pos (prev.val + 1) = i := by
            apply Fin.ext
            simp only [prev, idx_val, Nat.mod_add_mod]
            have hi := i.isLt
            rw [show i.val + ℓ - 1 + 1 = ℓ + i.val by omega, Nat.add_mod_left,
              Nat.mod_eq_of_lt hi]
          have harc : dc.f i ∈ M (dc.f prev) := by
            have := dc.arc prev.val
            rwa [idx_self, hidx_succ] at this
          have hrev_arc : dc.f prev ∈ M (dc.f i) := hrec _ hi3 _ harc
          have hadj_dig : (digonGraph M).Adj (dc.f i) (dc.f prev) :=
            ⟨fun e => hloop _ (e ▸ hrev_arc), harc, hrev_arc⟩
          have hk1 := (mem_filter.mp (hTS (dc.mem i))).2
          have hk2 := (mem_filter.mp (hTS (dc.mem prev))).2
          exact hκ _ _ hiS (mem_filter.mp (hTS (dc.mem prev))).1 hadj_dig (hk1.trans hk2.symm)
      refine ⟨S, subset_refl S, hS, ?_⟩
      refine bdirPiece M (univ \ S) S (S.filter (κ · = 0)) (S.filter (κ · = 1)) ?_ ?_
        (hclass 0) (hclass 1) (fun _ => none) ?_ ?_ ?_
      · rw [Finset.disjoint_left]; intro x hx hx'
        have h0 := (mem_filter.mp hx).2
        have h1 := (mem_filter.mp hx').2
        rw [h0] at h1; exact absurd h1 (by decide)
      · ext x; simp only [mem_union, mem_filter]
        constructor
        · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
        · intro hx
          have : κ x = 0 ∨ κ x = 1 := by generalize κ x = y; revert y; decide
          rcases this with h | h
          · exact Or.inl ⟨hx, h⟩
          · exact Or.inr ⟨hx, h⟩
      · intro v hv u hu
        exact Or.inr (Or.inl (hin v hv hu))
      · intro _ _ _ hp; cases hp
      · intro _ _ _ _ _ hp _; cases hp
  · -- Case 2 (`¬ IsAcyclicIn M W_S`): `i5Piece` on a shortest `DCyc` in `W_S`!
    unfold IsAcyclicIn at hacW
    push Not at hacW
    obtain ⟨T, hTW, hTne, hsrc⟩ := hacW
    have hex_dcyc : ∃ ℓ, HasDCyc M W_S ℓ := by
      obtain ⟨ℓ, hℓ⟩ := exists_hasDCyc_of_sourceless hloop hTne hsrc
      exact ⟨ℓ, hℓ.mono hTW⟩
    obtain ⟨ℓ, ⟨hℓ2, ⟨dc⟩⟩, hmin_dc⟩ :
        ∃ ℓ, HasDCyc M W_S ℓ ∧ ∀ ℓ', HasDCyc M W_S ℓ' → ℓ ≤ ℓ' :=
      ⟨Nat.find hex_dcyc, Nat.find_spec hex_dcyc, fun ℓ' h => Nat.find_min' hex_dcyc h⟩
    have hp := i5Piece (N := M) (R := S) (L := ∅) (fun x _ y _ z _ => hTT x y z)
      (fun _ _ _ _ h => nomatch h) dc hℓ2 (fun i j h => dc.chordless hloop hmin_dc h)
    rw [union_empty] at hp
    exact ⟨univ.image dc.f,
      fun x hx => by obtain ⟨i, -, rfl⟩ := mem_image.mp hx; exact (mem_filter.mp (dc.mem i)).1,
      ⟨dc.f ⟨0, dc.pos⟩, mem_image_of_mem _ (mem_univ _)⟩,
      hp⟩

end SubPieces

section Main

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Relative decomposition for any subset `R` satisfying `ClassSOn N R`. -/
theorem classSOn_decomp {N : V → Finset V} :
    ∀ (R : Finset V), ClassSOn N R → ∃ pcs, Decomp N (univ \ R) pcs := by
  intro R
  induction R using Finset.strongInduction with
  | H R ih =>
    intro hR
    rcases R.eq_empty_or_nonempty with rfl | hRne
    · exact ⟨[], by simp [Decomp]⟩
    · obtain ⟨S, hSR, hSne, hinClosed, hscc⟩ := exists_inClosed_scc N hRne
      have hM : IsClassS (resRel N S) := (hR.mono hSR).isClassS_resRel
      obtain ⟨H, hHS, hHne, ⟨c_res⟩⟩ := exists_piece_of_scc_classS hSne hM
        (fun _ hv => resRel_of_not_mem hv) (fun v _ => resRel_subset v) hscc
      have hHR : H ⊆ R := hHS.trans hSR
      let c_lift : PieceCert N (univ \ R) H := liftPieceCertInClosed hSR hinClosed hHS c_res
      obtain ⟨rest, hrest⟩ := ih (R \ H) (sdiff_ssubset hHR hHne) (hR.mono sdiff_subset)
      refine ⟨H :: rest, ?_⟩
      simp only [Decomp]
      refine ⟨Finset.disjoint_left.mpr fun x hx hx' => (mem_sdiff.mp hx).2 (hHR hx'),
        ⟨c_lift⟩, ?_⟩
      have heq : (univ \ R) ∪ H = univ \ (R \ H) := by
        ext x
        have h1 : x ∈ H → x ∈ R := fun h => hHR h
        simp only [mem_union, mem_sdiff, mem_univ, true_and]
        tauto
      rwa [heq]

/-- **Theorem S\* (piece decomposition for `Class S`).** Every recovery relation in `Class S`
admits a certified piece decomposition on every remaining vertex set `R`. -/
theorem classS_decomp {N : V → Finset V} (h : IsClassS N) (R : Finset V) :
    ∃ pcs, Decomp N (univ \ R) pcs :=
  classSOn_decomp R (h.classSOn R)

/-- **Theorem S\* (polymatroid weighted half-rate bound).** Every `Class S` recovery relation
satisfies `RateBound N (1 / 2)`, i.e. `2 h(V) ≤ Σ_v h({v})` for every valid polymatroid `h`. -/
theorem rateBound_classS {N : V → Finset V} (h : IsClassS N) :
    RateBound N (1 / 2) := by
  obtain ⟨pcs, hD⟩ := classS_decomp h univ
  rw [sdiff_self] at hD
  exact rateBound_of_decomp hD

/-- **Theorem S\* (all-code bound).** Every storage code `C ⊆ α^V` (linear or nonlinear) over any
nonempty finite alphabet `α` on a `Class S` recovery relation satisfies `|C|² ≤ |α|^|V|`. -/
theorem card_sq_le_classS {N : V → Finset V} {α : Type*} [Fintype α] [Nonempty α]
    (h : IsClassS N) {C : Finset (V → α)} (hC : IsStorageCode N C) :
    C.card ^ 2 ≤ Fintype.card α ^ Fintype.card V :=
  card_sq_le_of_rateBound_half (rateBound_classS h) hC

/-! ### Corollary B\*: Directed barrier inequality for `Class S` -/

/-- Vertices outside `S` all of whose recovery parents lie inside `S` (the directed counterpart of
`HalfRate.isolatedOut`). -/
def isolatedOutDir (N : V → Finset V) (S : Finset V) : Finset V :=
  univ.filter (fun v => v ∉ S ∧ N v ⊆ S)

theorem disjoint_isolatedOutDir (N : V → Finset V) (S : Finset V) :
    Disjoint S (isolatedOutDir N S) := by
  rw [Finset.disjoint_left]
  intro v hv hv'
  exact (mem_filter.mp hv').2.1 hv

theorem card_sdiff_isolatedOutDir (N : V → Finset V) (S : Finset V) :
    ((univ \ (S ∪ isolatedOutDir N S)).card : ℝ) =
      Fintype.card V - S.card - (isolatedOutDir N S).card := by
  rw [card_sdiff_of_subset (subset_univ _),
    card_union_of_disjoint (disjoint_isolatedOutDir N S), card_univ]
  have hle : S.card + (isolatedOutDir N S).card ≤ Fintype.card V := by
    rw [← card_union_of_disjoint (disjoint_isolatedOutDir N S), ← card_univ]
    exact card_le_card (subset_univ _)
  push_cast [Nat.cast_sub hle]
  ring

/-- **Corollary B\* (polymatroid barrier inequality for `Class S`).** For any `Class S` recovery
relation `N` and any vertex set `S ⊆ V`, every valid polymatroid satisfies
`2 h(V) ≤ 2 Σ_{v ∈ S} h({v}) + Σ_{v ∉ S ∪ isolatedOutDir N S} h({v})`. -/
theorem barrier_ineq_classS {N : V → Finset V} (hS_cls : IsClassS N)
    {h : Finset V → ℝ} (hh : IsPolymatroid h) (hv : IsValid h N) (S : Finset V) :
    2 * h univ ≤ 2 * ∑ v ∈ S, h {v} + ∑ v ∈ univ \ (S ∪ isolatedOutDir N S), h {v} := by
  set U := S ∪ isolatedOutDir N S
  obtain ⟨pcs, hD⟩ := classS_decomp hS_cls (univ \ U)
  rw [sdiff_sdiff_right_self, inf_eq_inter, univ_inter] at hD
  have h1 := decomp_ineq hh hv pcs U hD
  have h2 : ∑ v ∈ univ \ U, (h (insert v U) - h U) ≤ ∑ v ∈ univ \ U, h {v} := by
    refine sum_le_sum fun v _ => ?_
    have := hh.union_le {v} U
    rw [singleton_union] at this
    linarith
  have h3 : h U = h S := by
    refine hh.eq_of_closure hv subset_union_left ?_
    intro v hvU hvS
    rcases mem_union.mp hvU with h' | h'
    · exact absurd h' hvS
    · exact (mem_filter.mp h').2.2
  have h4 := hh.le_sum_singleton S
  linarith

/-- **Corollary B\* (all-code barrier bound for `Class S`).** Every storage code `C ⊆ α^V` on a
`Class S` recovery relation satisfies
`2 log |C| ≤ (|V| + |S| - |isolatedOutDir N S|) log |α|` for every vertex cut `S ⊆ V`. -/
theorem log_card_le_barrier_classS {N : V → Finset V} {α : Type*} [Fintype α] [Nonempty α]
    (hS_cls : IsClassS N) {C : Finset (V → α)} (hC : IsStorageCode N C) (S : Finset V) :
    2 * Real.log C.card ≤
      ((Fintype.card V : ℝ) + S.card - (isolatedOutDir N S).card) *
        Real.log (Fintype.card α) := by
  have hα : 0 ≤ Real.log (Fintype.card α) :=
    Real.log_nonneg (by exact_mod_cast Fintype.card_pos)
  have hw : 0 ≤ (Fintype.card V : ℝ) + S.card - (isolatedOutDir N S).card := by
    have := card_sdiff_isolatedOutDir N S
    have : (0 : ℝ) ≤ ((univ \ (S ∪ isolatedOutDir N S)).card : ℝ) := Nat.cast_nonneg _
    linarith [(Nat.cast_nonneg S.card : (0 : ℝ) ≤ S.card)]
  rcases C.eq_empty_or_nonempty with hCe | hne
  · rw [hCe, card_empty, Nat.cast_zero, Real.log_zero, mul_zero]
    positivity
  · have hc0 : (0 : ℝ) < C.card := by exact_mod_cast hne.card_pos
    have hp : ∀ ω : C, (0 : ℝ) ≤ (fun _ : C => ((C.card : ℝ))⁻¹) ω :=
      fun _ => inv_nonneg.mpr hc0.le
    have hp1 : ∑ ω : C, (fun _ : C => ((C.card : ℝ))⁻¹) ω = 1 := by
      simp only [sum_const, card_univ, Fintype.card_coe, nsmul_eq_mul]
      field_simp
    have hX : IsRecoverable N (fun x : C => (x : V → α)) :=
      fun v ω ω' h => hC ω.1 ω.2 ω'.1 ω'.2 v h
    set H := codeEntropy (fun _ : C => ((C.card : ℝ))⁻¹) (fun x : C => (x : V → α)) with hHdef
    have hH := codeEntropy_isPolymatroid (fun _ : C => ((C.card : ℝ))⁻¹)
      (fun x : C => (x : V → α)) hp hp1
    have hHv := codeEntropy_isValid (fun _ : C => ((C.card : ℝ))⁻¹)
      (fun x : C => (x : V → α)) hp hX
    have hb := barrier_ineq_classS hS_cls hH hHv S
    rw [codeEntropy_univ_uniform C hne, ← hHdef] at hb
    have hsing : ∀ v, H {v} ≤ Real.log (Fintype.card α) := fun v =>
      codeEntropy_singleton_le (fun _ : C => ((C.card : ℝ))⁻¹) (fun x : C => (x : V → α)) hp hp1 v
    have hS : ∑ v ∈ S, H {v} ≤ S.card * Real.log (Fintype.card α) := by
      calc ∑ v ∈ S, H {v} ≤ ∑ _v ∈ S, Real.log (Fintype.card α) := sum_le_sum fun v _ => hsing v
        _ = S.card * Real.log (Fintype.card α) := by rw [sum_const, nsmul_eq_mul]
    have hR : ∑ v ∈ univ \ (S ∪ isolatedOutDir N S), H {v} ≤
        (univ \ (S ∪ isolatedOutDir N S)).card * Real.log (Fintype.card α) := by
      calc ∑ v ∈ univ \ (S ∪ isolatedOutDir N S), H {v}
          ≤ ∑ _v ∈ univ \ (S ∪ isolatedOutDir N S), Real.log (Fintype.card α) :=
            sum_le_sum fun v _ => hsing v
        _ = _ := by rw [sum_const, nsmul_eq_mul]
    rw [card_sdiff_isolatedOutDir] at hR
    nlinarith

end Main

end DirectedReciprocity
