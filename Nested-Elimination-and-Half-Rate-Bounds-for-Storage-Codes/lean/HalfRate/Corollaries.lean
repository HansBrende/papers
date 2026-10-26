import HalfRate.Decomposition
import CircularMemo.Circular

/-!
# Corollaries of the decomposition theorem

* `ElimCert.rateBound`: an order-free global elimination certificate (any number of records,
  free choice of the supplying record) gives the weighted half bound. This contains the
  three-record criterion of the circular memo (`CircularMemo.three_part_elimination`, cyclic
  supply).
* `ElimCert.pullback`: certificates pull back along homomorphisms of recovery relations
  (the pull-back lemma of the paper).
* `andrasfaiCert`, `rateBound_of_circularHom'`: every graph with circular chromatic number
  below three is a direct instance (the circular memo's theorem, re-derived through the
  pull-back).
* `rateBound_of_twoAcyclic`: relations whose vertex set splits into two acyclic parts
  (2-dicolourable relations; bipartite graphs in particular).
-/

namespace HalfRate

open Finset MotionDepthCodes

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- An order-free global elimination certificate with `m` records. -/
structure ElimCert (N : V → Finset V) (m : ℕ) where
  P : Fin m → Finset V
  disj : ∀ i j, i ≠ j → Disjoint (P i) (P j)
  cover : ∀ v, ∃ i, v ∈ P i
  a : V → Fin m
  b : V → Fin m
  own : ∀ v, v ∈ P (a v)
  ab : ∀ v, a v ≠ b v
  elim : ∀ S : Finset V, S ≠ univ → ∃ v, v ∉ S ∧ N v ⊆ S ∪ P (b v)

/-- **Global elimination certificates give the weighted half bound.** -/
theorem ElimCert.rateBound {N : V → Finset V} {m : ℕ} (c : ElimCert N m) :
    RateBound N (1 / 2) := by
  intro h hh hv
  have inv : ∀ n : ℕ, ∀ S : Finset V, (univ \ S).card = n →
      2 * h univ + ((m : ℝ) - 2) * h S ≤ ∑ i, h (S ∪ c.P i) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro S hn
      by_cases hS : S = univ
      · subst hS
        have hu : ∀ i, (univ : Finset V) ∪ c.P i = univ := fun i => union_eq_left.mpr (subset_univ _)
        simp only [hu, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        linarith
      obtain ⟨v, hvS, hN⟩ := c.elim S hS
      have hlt : (univ \ insert v S).card < n := by
        rw [← hn]; apply card_lt_card
        refine ⟨sdiff_subset_sdiff (subset_refl _) (subset_insert v S), ?_⟩
        intro hsub
        have : v ∈ univ \ S := by simp [hvS]
        have := hsub this; simp at this
      have hi := ih _ hlt (insert v S) rfl
      have hstep := sum_records_step hh c.P S v (c.a v) (c.b v) (c.own v) (c.ab v)
      have hd : defect h S (c.P (c.b v)) v = 0 := by
        simp only [defect, hh.insert_eq_of_subset hN (hv v), sub_self]
      rw [hd, Fintype.card_fin] at hstep
      linarith
  have h0 := inv _ ∅ rfl
  simp only [empty_union, hh.empty, mul_zero, add_zero] at h0
  have hsub : ∑ i, h (c.P i) ≤ ∑ v, h {v} := by
    calc ∑ i, h (c.P i) ≤ ∑ i, ∑ v ∈ c.P i, h {v} := sum_le_sum fun i _ => hh.le_sum_singleton _
      _ = ∑ v ∈ (univ : Finset (Fin m)).biUnion c.P, h {v} := by
          rw [sum_biUnion]; intro i _ j _ hij; exact c.disj i j hij
      _ = ∑ v, h {v} := by
          congr 1; apply eq_univ_of_forall; intro v
          obtain ⟨i, hi⟩ := c.cover v; exact mem_biUnion.mpr ⟨i, mem_univ _, hi⟩
  linarith

/-- **Pull-back.** A homomorphism of recovery relations (side information maps into side
information) transports elimination certificates backwards. -/
def ElimCert.pullback {W : Type*} [DecidableEq W] [Fintype W] {N : V → Finset V}
    {N' : W → Finset W} {m : ℕ} (φ : V → W) (hφ : ∀ v, ∀ u ∈ N v, φ u ∈ N' (φ v))
    (c : ElimCert N' m) : ElimCert N m where
  P i := univ.filter (fun v => φ v ∈ c.P i)
  disj i j hij := by
    rw [disjoint_left]; intro v hi hj
    simp only [mem_filter, mem_univ, true_and] at hi hj
    exact disjoint_left.mp (c.disj i j hij) hi hj
  cover v := by
    obtain ⟨i, hi⟩ := c.cover (φ v); exact ⟨i, by simp [hi]⟩
  a v := c.a (φ v)
  b v := c.b (φ v)
  own v := by simp [c.own (φ v)]
  ab v := c.ab (φ v)
  elim S hS := by
    classical
    let S' : Finset W := univ.filter (fun x => ∀ v, φ v = x → v ∈ S)
    obtain ⟨v₀, hv₀⟩ : ∃ v, v ∉ S := by
      by_contra hcon
      exact hS (eq_univ_of_forall fun v => by_contra fun hv => hcon ⟨v, hv⟩)
    have hS' : S' ≠ univ := by
      intro he
      have : φ v₀ ∈ S' := he ▸ mem_univ _
      simp only [S', mem_filter, mem_univ, true_and] at this
      exact hv₀ (this v₀ rfl)
    obtain ⟨x, hxS', hNx⟩ := c.elim S' hS'
    have : ∃ v, φ v = x ∧ v ∉ S := by
      simp only [S', mem_filter, mem_univ, true_and, not_forall] at hxS'
      obtain ⟨v, hv, hvS⟩ := hxS'; exact ⟨v, hv, hvS⟩
    obtain ⟨v, rfl, hvS⟩ := this
    refine ⟨v, hvS, ?_⟩
    intro u hu
    have hφu := hNx (hφ v u hu)
    rcases mem_union.mp hφu with h1 | h2
    · simp only [S', mem_filter, mem_univ, true_and] at h1
      exact mem_union_left _ (h1 u rfl)
    · exact mem_union_right _ (by simp [h2])

/-- The cyclic 3-record certificate of the Andrásfai graph `And(k) = K_{(3k-1)/k}`
(the circular memo's interleaved order, `CircularMemo.neighbor_order`). -/
def andrasfaiCert (k : ℕ) (hk : 2 ≤ k) :
    ElimCert (nbhd (circularClique (3 * k - 1) k)) 3 where
  P i := univ.filter (fun v : Fin (3 * k - 1) =>
    (i = 0 ∧ v.val < k) ∨ (i = 1 ∧ k ≤ v.val ∧ v.val < 2 * k) ∨ (i = 2 ∧ 2 * k ≤ v.val))
  disj i j hij := by
    rw [disjoint_left]; intro v hi hj
    simp only [mem_filter, mem_univ, true_and] at hi hj
    omega
  cover v := by
    by_cases h1 : v.val < k
    · exact ⟨0, by simp [h1]⟩
    · by_cases h2 : v.val < 2 * k
      · exact ⟨1, by simp; omega⟩
      · exact ⟨2, by simp; omega⟩
  a v := if v.val < k then 0 else if v.val < 2 * k then 1 else 2
  b v := if v.val < k then 1 else if v.val < 2 * k then 2 else 0
  own v := by
    simp only [mem_filter, mem_univ, true_and]
    split_ifs <;> omega
  ab v := by split_ifs <;> decide
  elim S hS := by
    have hex : Set.Nonempty {v : Fin (3 * k - 1) | v ∉ S} := by
      by_contra hempty
      rw [Set.not_nonempty_iff_eq_empty] at hempty
      apply hS; apply eq_univ_of_forall; intro v
      by_contra hvS
      have hm : v ∈ ({v : Fin (3 * k - 1) | v ∉ S} : Set _) := hvS
      rw [hempty] at hm; exact hm
    obtain ⟨v, hvS, hmin⟩ := Set.exists_min_image {v | v ∉ S}
      (CircularMemo.interleavedOrder k) (Set.toFinite _) hex
    refine ⟨v, hvS, ?_⟩
    intro w hw
    by_cases hwS : w ∈ S
    · exact mem_union_left _ hwS
    · apply mem_union_right
      have ha : (circularClique (3 * k - 1) k).Adj v w := by
        simpa only [nbhd, mem_filter, mem_univ, true_and] using hw
      have ht := (CircularMemo.neighbor_order hk ha).resolve_left
        (not_lt_of_ge (hmin w hwS))
      simp only [mem_filter, mem_univ, true_and]
      split_ifs <;> omega

/-- **Every graph of circular chromatic number below three**, as a direct instance of the
elimination identity: pull back the Andrásfai certificate along the Bondy–Hell map. -/
theorem rateBound_of_circularHom' {G : SimpleGraph V} [DecidableRel G.Adj] {p q : ℕ}
    (hq : 0 < q) (hpq : p < 3 * q) (φ : G →g circularClique p q) :
    RateBound (nbhd G) (1 / 2) := by
  let k := q + 1
  have hk : 2 ≤ k := by dsimp [k]; omega
  have hn : 0 < 3 * k - 1 := by omega
  have hineq : p * k ≤ (3 * k - 1) * q := by
    have he : 3 * k - 1 + 1 = 3 * k := by omega
    dsimp [k] at *
    nlinarith
  let ψ : G →g circularClique (3 * k - 1) k :=
    (circularCliqueHom p q (3 * k - 1) k hn (by omega) hineq).comp φ
  refine ((andrasfaiCert k hk).pullback ψ ?_).rateBound
  intro v u hu
  simp only [nbhd, mem_filter, mem_univ, true_and] at hu ⊢
  exact ψ.map_adj hu

/-- A set is acyclic for `N` if every nonempty subset has a vertex with no side information
inside it (a source of the induced sub-relation). -/
def IsAcyclicIn (N : V → Finset V) (A : Finset V) : Prop :=
  ∀ T ⊆ A, T.Nonempty → ∃ v ∈ T, ∀ u ∈ N v, u ∉ T

/-- **2-dicolourable relations** (two acyclic parts): the weighted half bound. -/
theorem rateBound_of_twoAcyclic {N : V → Finset V} (A B : Finset V) (hAB : Disjoint A B)
    (hcov : A ∪ B = univ) (hA : IsAcyclicIn N A) (hB : IsAcyclicIn N B) :
    RateBound N (1 / 2) := by
  classical
  have hmem : ∀ v, v ∉ A → v ∈ B := fun v hv => by
    have : v ∈ A ∪ B := hcov ▸ mem_univ v
    rcases mem_union.mp this with h | h
    · exact absurd h hv
    · exact h
  let c : ElimCert N 2 :=
    { P := ![A, B]
      disj := by
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all [disjoint_comm]
      cover := by
        intro v; by_cases hv : v ∈ A
        · exact ⟨0, by simpa using hv⟩
        · exact ⟨1, by simpa using hmem v hv⟩
      a := fun v => if v ∈ A then 0 else 1
      b := fun v => if v ∈ A then 1 else 0
      own := by
        intro v; by_cases hv : v ∈ A
        · simp [hv]
        · simp [hv, hmem v hv]
      ab := by intro v; by_cases hv : v ∈ A <;> simp [hv]
      elim := by
        intro S hS
        by_cases hAS : (A \ S).Nonempty
        · obtain ⟨v, hvT, hsrc⟩ := hA (A \ S) sdiff_subset hAS
          have hvA : v ∈ A := (mem_sdiff.mp hvT).1
          refine ⟨v, (mem_sdiff.mp hvT).2, ?_⟩
          intro u hu
          by_cases huA : u ∈ A
          · have : u ∉ A \ S := hsrc u hu
            simp only [mem_sdiff, not_and, not_not] at this
            exact mem_union_left _ (this huA)
          · apply mem_union_right; simp [hvA, hmem u huA]
        · have hAsub : A ⊆ S := by
            intro x hx; by_contra hxS
            exact hAS ⟨x, mem_sdiff.mpr ⟨hx, hxS⟩⟩
          have hBS : (B \ S).Nonempty := by
            obtain ⟨v, hv⟩ : ∃ v, v ∉ S := by
              by_contra hcon
              exact hS (eq_univ_of_forall fun v => by_contra fun hv => hcon ⟨v, hv⟩)
            exact ⟨v, mem_sdiff.mpr ⟨hmem v (fun hvA => hv (hAsub hvA)), hv⟩⟩
          obtain ⟨v, hvT, hsrc⟩ := hB (B \ S) sdiff_subset hBS
          refine ⟨v, (mem_sdiff.mp hvT).2, ?_⟩
          intro u hu
          apply mem_union_left
          by_cases huA : u ∈ A
          · exact hAsub huA
          · have : u ∉ B \ S := hsrc u hu
            simp only [mem_sdiff, not_and, not_not] at this
            exact this (hmem u huA) }
  exact c.rateBound

end HalfRate
