import LeanMachine.WholeRow.ParityTrimming
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Parities on a partition into induced matchings

The nonincident cells are partitioned into disjoint nonempty blocks. Distinct
cells of a block are mutual helpers. The large-block count keeps an arbitrary
reverse-degree cutoff; the square-root specialization is Proposition 10.1 of
*Tape Transposition and the Matrix Coding Conjecture*.

No field, reverse-degree bound, or uniform block size is assumed. Exact fibre
sizes reuse `DisjointSums.fiber_card`; prescribed nonzero sums work as well.
-/

namespace LeanMachine.WholeRow

open Finset
open scoped BigOperators Classical
noncomputable section

/-- A partition of all nonincident cells into induced matchings of the
complement of the helper relation. Incident cells remain unconstrained. -/
structure InducedMatchingPartition {R J : Type*} (ρ : J → Finset R) (κ : Type*)
    extends DisjointSums (R × J) κ where
  nonincident : ∀ k, ∀ e ∈ support k, e.1 ∉ ρ e.2
  cross : ∀ k, ∀ e ∈ support k, ∀ f ∈ support k, e ≠ f → e.1 ∈ ρ f.2
  covers : ∀ e, e.1 ∉ ρ e.2 → ∃ k, e ∈ support k

namespace InducedMatchingPartition

variable {R J κ : Type*} [Fintype R] [Fintype J] [Fintype κ]
variable {ρ : J → Finset R} (D : InducedMatchingPartition ρ κ)

omit [Fintype R] [Fintype J] [Fintype κ] in
theorem row_injective (k : κ) : Set.InjOn Prod.fst (D.support k : Set (R × J)) := by
  intro e he f hf h
  by_contra hne
  exact D.nonincident k f hf (h ▸ D.cross k e he f hf hne)

omit [Fintype R] [Fintype J] [Fintype κ] in
theorem column_injective (k : κ) : Set.InjOn Prod.snd (D.support k : Set (R × J)) := by
  intro e he f hf h
  by_contra hne
  exact D.nonincident k e he (h.symm ▸ D.cross k e he f hf hne)

/-- All cells in blocks of size at least three. -/
def largeCells : Finset (R × J) :=
  (univ.filter (fun k => 3 ≤ (D.support k).card)).biUnion D.support

/-- Endpoints of three-step incidence paths with their first interior row
outside the selected heavy-row set. -/
def pathCells (ρ : J → Finset R) (H : Finset R) : Finset (R × J) :=
  univ.biUnion fun j => (ρ j \ H).biUnion fun i =>
    (univ.filter (fun c => i ∈ ρ c)).biUnion fun c =>
      (ρ c).image fun a => (a, j)

omit [Fintype R] [Fintype κ] in
private theorem mem_pathCells {k : κ} {e f g : R × J} {H : Finset R}
    (he : e ∈ D.support k) (hf : f ∈ D.support k) (hg : g ∈ D.support k)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) (hH : f.1 ∉ H) :
    e ∈ pathCells ρ H := by
  apply mem_biUnion.mpr
  refine ⟨e.2, mem_univ _, mem_biUnion.mpr ⟨f.1, ?_, ?_⟩⟩
  · exact mem_sdiff.mpr ⟨D.cross k f hf e he hef.symm, hH⟩
  · apply mem_biUnion.mpr
    refine ⟨g.2, mem_filter.mpr ⟨mem_univ _, D.cross k f hf g hg hfg⟩, ?_⟩
    exact mem_image.mpr ⟨e.1, D.cross k e he g hg heg, Prod.eta e⟩

omit [Fintype R] in
/-- Counting paths needs only forward width and a reverse bound outside H. -/
theorem pathCells_card_le (H : Finset R) (w t : ℕ)
    (hf : ∀ j, (ρ j).card ≤ w)
    (hr : ∀ i ∉ H, (univ.filter (fun j => i ∈ ρ j)).card ≤ t) :
    (pathCells ρ H).card ≤ Fintype.card J * w * t * w := by
  apply card_biUnion_le.trans
  calc
    _ ≤ ∑ j : J, w * (t * w) := by
      apply sum_le_sum
      intro j _
      apply (card_biUnion_le_card_mul (ρ j \ H) _ (t * w) ?_).trans
      · exact Nat.mul_le_mul_right _ ((card_le_card sdiff_subset).trans (hf j))
      · intro i hi
        apply (card_biUnion_le_card_mul _ _ w (fun c _ =>
          (card_image_le).trans (hf c))).trans
        exact Nat.mul_le_mul_right _ (hr i (mem_sdiff.mp hi).2)
    _ = _ := by simp [Nat.mul_assoc]

omit [Fintype R] [Fintype κ] in
private theorem block_charge (H : Finset R) (k : κ) (hk : 3 ≤ (D.support k).card) :
    2 * (D.support k).card ≤
      2 * (D.support k ∩ pathCells ρ H).card +
      3 * (D.support k ∩ (H ×ˢ (univ : Finset J))).card := by
  let L := (D.support k).filter (fun e => e.1 ∉ H)
  by_cases hL : 2 ≤ L.card
  · have hs : D.support k ⊆ pathCells ρ H := by
      intro e he
      obtain ⟨f, hf, hfe⟩ := exists_mem_ne (by omega : 1 < L.card) e
      have hp : 2 < (D.support k).card := by omega
      have htwo : 1 < ((D.support k).erase e).card := by
        rw [card_erase_of_mem he]
        omega
      obtain ⟨g, hg0, hgf⟩ := exists_mem_ne htwo f
      obtain ⟨hge, hg⟩ := mem_erase.mp hg0
      exact D.mem_pathCells he (mem_filter.mp hf).1 hg hfe.symm hge.symm hgf.symm
        (mem_filter.mp hf).2
    rw [inter_eq_left.mpr hs]
    omega
  · have hsplit : L.card + (D.support k ∩ (H ×ˢ (univ : Finset J))).card =
        (D.support k).card := by
      have := card_filter_add_card_filter_not (s := D.support k) (p := fun e => e.1 ∉ H)
      simpa [L, ← filter_mem_eq_inter] using this
    omega

omit [Fintype R] [Fintype J] [Fintype κ] in
private theorem sum_inter_card_le (K : Finset κ) (S : Finset (R × J)) :
    (∑ k ∈ K, (D.support k ∩ S).card) ≤ S.card := by
  rw [← card_biUnion]
  · exact card_le_card (biUnion_subset.mpr fun _ _ => inter_subset_right)
  · intro k hk l hl hkl
    exact (D.disjoint hkl).mono inter_subset_left inter_subset_left

omit [Fintype R] in
/-- The heavy cells pay at most three halves; all remaining large-block
cells inject into the path-endpoint count. This is purely finite counting. -/
theorem largeCells_charge (H : Finset R) :
    2 * D.largeCells.card ≤ 2 * (pathCells ρ H).card +
      3 * (H.card * Fintype.card J) := by
  let K := univ.filter fun k => 3 ≤ (D.support k).card
  have h := sum_le_sum (s := K) (fun k hk => D.block_charge H k (mem_filter.mp hk).2)
  rw [sum_add_distrib, ← mul_sum, ← mul_sum, ← mul_sum] at h
  have he : D.largeCells.card = ∑ k ∈ K, (D.support k).card :=
    card_biUnion (fun k _ l _ hkl => D.disjoint hkl)
  rw [← he] at h
  have hp := D.sum_inter_card_le K (pathCells ρ H)
  have hh := D.sum_inter_card_le K (H ×ˢ (univ : Finset J))
  rw [card_product, card_univ] at hh
  omega

/-- Quantitative finite cutoff bound, including rectangular arrays.
Keeping t free permits optimizing the growing-window estimate. -/
theorem largeCells_cutoff (w t : ℕ) (hf : ∀ j, (ρ j).card ≤ w) :
    2 * (t + 1) * D.largeCells.card ≤
      2 * Fintype.card J * w * t * w * (t + 1) + 3 * w * (Fintype.card J)^2 := by
  let H := heavyRows ρ t
  have hr : ∀ i ∉ H, (univ.filter fun j => i ∈ ρ j).card ≤ t := by
    intro i hi
    simpa [H, heavyRows] using hi
  have hp := pathCells_card_le H w t hf hr
  have hc := D.largeCells_charge H
  have hh := heavyRows_card_mul_succ_le ρ w t hf
  change H.card * (t + 1) ≤ _ at hh
  nlinarith [Nat.mul_le_mul_right (t + 1) hc,
    Nat.mul_le_mul_right (Fintype.card J) hh]

/-- A real cutoff avoids rounding losses. The bound is uniform in the number
of rows, the block sizes, and the alphabet. -/
theorem largeCells_threshold (w : ℕ) (hf : ∀ j, (ρ j).card ≤ w)
    (x : ℝ) (hx : 0 < x) :
    (D.largeCells.card : ℝ) ≤
      Fintype.card J * (w : ℝ)^2 * x +
        3 / 2 * w * (Fintype.card J : ℝ)^2 / x := by
  let t := Nat.floor x
  let H := heavyRows ρ t
  have ht : (t : ℝ) ≤ x := Nat.floor_le hx.le
  have hx' : x ≤ (t : ℝ) + 1 := (Nat.lt_floor_add_one x).le
  have hr : ∀ i ∉ H, (univ.filter fun j => i ∈ ρ j).card ≤ t := by
    intro i hi
    simpa [H, heavyRows] using hi
  have hp := pathCells_card_le H w t hf hr
  have hp' : ((pathCells ρ H).card : ℝ) ≤ Fintype.card J * (w : ℝ)^2 * x := by
    have hpR : ((pathCells ρ H).card : ℝ) ≤ Fintype.card J * w * t * w := by
      exact_mod_cast hp
    nlinarith [mul_le_mul_of_nonneg_left ht
      (show 0 ≤ (Fintype.card J : ℝ) * (w : ℝ)^2 by positivity)]
  have hh := heavyRows_card_mul_succ_le ρ w t hf
  have hhR : (H.card : ℝ) * ((t : ℝ) + 1) ≤ w * Fintype.card J := by
    exact_mod_cast hh
  have hhx : (H.card : ℝ) * x ≤ w * Fintype.card J := by
    nlinarith [mul_le_mul_of_nonneg_left hx' (show 0 ≤ (H.card : ℝ) by positivity)]
  have hpay : (H.card : ℝ) * Fintype.card J ≤
      w * (Fintype.card J : ℝ)^2 / x := by
    apply (le_div_iff₀ hx).mpr
    nlinarith [mul_le_mul_of_nonneg_right hhx (show 0 ≤ (Fintype.card J : ℝ) by positivity)]
  have hc : 2 * (D.largeCells.card : ℝ) ≤ 2 * (pathCells ρ H).card +
      3 * ((H.card : ℝ) * Fintype.card J) := by
    exact_mod_cast D.largeCells_charge H
  have he : 3 / 2 * (w : ℝ) * (Fintype.card J : ℝ)^2 / x =
      3 / 2 * (w * (Fintype.card J : ℝ)^2 / x) := by ring
  rw [he]
  linarith

/-- The square-root bound in the manuscript. The natural number d is the
number of columns; the row type need not have the same cardinality. -/
theorem largeCells_sqrt (w : ℕ) (hf : ∀ j, (ρ j).card ≤ w) :
    (D.largeCells.card : ℝ) ≤ ((w : ℝ)^2 + 3 / 2 * w) *
      Fintype.card J * Real.sqrt (Fintype.card J) := by
  by_cases hd : Fintype.card J = 0
  · have hcard : D.largeCells.card = 0 := by
      have := card_le_univ D.largeCells
      simpa [hd] using this
    simp [hd, hcard]
  · have hdR : (0 : ℝ) < Fintype.card J := by exact_mod_cast Nat.pos_of_ne_zero hd
    have hs := Real.sq_sqrt hdR.le
    have hspos := Real.sqrt_pos.mpr hdR
    have h := D.largeCells_threshold w hf (Real.sqrt (Fintype.card J)) hspos
    have he : (Fintype.card J : ℝ)^2 / Real.sqrt (Fintype.card J) =
        Fintype.card J * Real.sqrt (Fintype.card J) := by
      apply (div_eq_iff hspos.ne').mpr
      nlinarith
    have hr : 3 / 2 * (w : ℝ) * (Fintype.card J : ℝ)^2 /
        Real.sqrt (Fintype.card J) =
        3 / 2 * w * (Fintype.card J * Real.sqrt (Fintype.card J)) := by
      rw [mul_div_assoc, he]
    rw [hr] at h
    nlinarith

/-- Balancing the two charges improves the growing-window threshold:
large blocks occupy at most (5/2)(w d)^(3/2) cells. Thus their density vanishes
already for w = o(d^(1/3)), even when block sizes are mixed. -/
theorem largeCells_balanced (w : ℕ) (hf : ∀ j, (ρ j).card ≤ w) :
    (D.largeCells.card : ℝ) ≤ 5 / 2 * (w * Fintype.card J : ℝ) *
      Real.sqrt (w * Fintype.card J) := by
  by_cases hw : w = 0
  · simpa [hw] using D.largeCells_sqrt w hf
  by_cases hd : Fintype.card J = 0
  · simpa [hd] using D.largeCells_sqrt w hf
  have hwR : (0 : ℝ) < w := by exact_mod_cast Nat.pos_of_ne_zero hw
  have hdR : (0 : ℝ) < Fintype.card J := by exact_mod_cast Nat.pos_of_ne_zero hd
  let s := Real.sqrt (w * Fintype.card J)
  have hs : 0 < s := Real.sqrt_pos.mpr (mul_pos hwR hdR)
  have he : s^2 = (w : ℝ) * Fintype.card J := Real.sq_sqrt (mul_pos hwR hdR).le
  have h := D.largeCells_threshold w hf (s / w) (div_pos hs hwR)
  have hfirst : (Fintype.card J : ℝ) * (w : ℝ)^2 * (s / w) =
      (w : ℝ) * Fintype.card J * s := by field_simp
  have hsecond : 3 / 2 * (w : ℝ) * (Fintype.card J : ℝ)^2 / (s / w) =
      3 / 2 * ((w : ℝ) * Fintype.card J * s) := by
    apply (div_eq_iff (div_pos hs hwR).ne').mpr
    field_simp
    nlinarith [sq_nonneg ((w : ℝ) * Fintype.card J - s^2)]
  rw [hfirst, hsecond] at h
  dsimp [s] at h ⊢
  linarith

private theorem total_card :
    Fintype.card R * Fintype.card J =
      (univ.filter (fun e : R × J => e.1 ∈ ρ e.2)).card +
        ∑ k, (D.support k).card := by
  have he : univ.biUnion D.support = univ.filter (fun e : R × J => e.1 ∉ ρ e.2) := by
    ext e
    simp only [mem_biUnion, mem_univ, true_and, mem_filter]
    exact ⟨fun ⟨k, hk⟩ => D.nonincident k e hk, D.covers e⟩
  rw [← card_biUnion (fun k _ l _ hkl => D.disjoint hkl), he,
    card_filter_add_card_filter_not]
  simp

/-- At most two cells per small block; the large cells are charged separately. -/
theorem dimension_le (w : ℕ) (hf : ∀ j, (ρ j).card ≤ w) :
    2 * (Fintype.card (R × J) - Fintype.card κ) ≤
      Fintype.card R * Fintype.card J + w * Fintype.card J + D.largeCells.card := by
  have hi : (univ.filter (fun e : R × J => e.1 ∈ ρ e.2)).card ≤
      w * Fintype.card J := by
    have he : (univ.filter (fun e : R × J => e.1 ∈ ρ e.2)).card =
        ∑ j, (ρ j).card := by
      simp only [card_filter, Fintype.sum_prod_type]
      rw [sum_comm]
      simp
    rw [he]
    simpa [Nat.mul_comm] using sum_le_sum (s := univ) (fun j _ => hf j)
  have hb : (∑ k, (D.support k).card) ≤ 2 * Fintype.card κ + D.largeCells.card := by
    have hp (k : κ) : (D.support k).card ≤
        2 + if 3 ≤ (D.support k).card then (D.support k).card else 0 := by
      split_ifs <;> omega
    have he : D.largeCells.card = ∑ k, if 3 ≤ (D.support k).card then
        (D.support k).card else 0 := by
      rw [largeCells, card_biUnion (fun k _ l _ hkl => D.disjoint hkl), sum_filter]
    rw [he]
    simpa [sum_add_distrib, Nat.mul_comm] using sum_le_sum (s := univ) (fun k _ => hp k)
  have ht := D.total_card
  have hk := D.toDisjointSums.card_le
  rw [Fintype.card_prod] at hk ⊢
  omega

variable {A : Type*} [AddCommGroup A] [Fintype A]

/-- Prescribed sums; the zero syndrome is the parity code in the paper. -/
def code (y : κ → A) : Finset (R × J → A) :=
  univ.filter fun x => D.encode x = y

theorem code_card (y : κ → A) :
    (D.code y).card = Fintype.card A ^ (Fintype.card (R × J) - Fintype.card κ) := by
  convert D.toDisjointSums.fiber_card (A := A) y using 1
  congr 1
  ext x
  simp [code]

/-- Any prescribed sums give whole-column recovery from the helper rows. -/
theorem code_recovers (y : κ → A) {x z : R × J → A}
    (hx : x ∈ D.code y) (hz : z ∈ D.code y) (j : J)
    (hxz : ∀ i ∈ ρ j, ∀ c, x (i, c) = z (i, c)) : ∀ i, x (i, j) = z (i, j) := by
  intro i
  by_cases hi : i ∈ ρ j
  · exact hxz i hi j
  · obtain ⟨k, hk⟩ := D.covers (i, j) hi
    rw [D.toDisjointSums.recover x k hk, D.toDisjointSums.recover z k hk,
      (mem_filter.mp hx).2, (mem_filter.mp hz).2]
    congr 1
    apply sum_congr rfl
    intro e he
    exact hxz e.1 (D.cross k e (mem_erase.mp he).2 (i, j) hk (mem_erase.mp he).1) e.2

/-- Cardinality form, uniform over all finite abelian alphabets and every
syndrome. In particular it applies bitwise to the canonical alphabet. -/
theorem code_card_le_sqrt (y : κ → A) (w : ℕ) (hf : ∀ j, (ρ j).card ≤ w) :
    ((D.code y).card : ℝ) ≤ (Fintype.card A : ℝ) ^
      ((Fintype.card R : ℝ) * Fintype.card J / 2 + w * Fintype.card J / 2 +
        ((w : ℝ)^2 / 2 + 3 * w / 4) * Fintype.card J * Real.sqrt (Fintype.card J)) := by
  have hd : 2 * ((Fintype.card (R × J) - Fintype.card κ : ℕ) : ℝ) ≤
      (Fintype.card R : ℝ) * Fintype.card J + w * Fintype.card J + D.largeCells.card := by
    exact_mod_cast D.dimension_le w hf
  have hb := D.largeCells_sqrt w hf
  rw [D.code_card, Nat.cast_pow, ← Real.rpow_natCast]
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Fintype.card_pos (α := A))
  nlinarith

/-- The balanced cardinality bound, allowing arbitrary prescribed block sums. -/
theorem code_card_le_balanced (y : κ → A) (w : ℕ) (hf : ∀ j, (ρ j).card ≤ w) :
    ((D.code y).card : ℝ) ≤ (Fintype.card A : ℝ) ^
      ((Fintype.card R : ℝ) * Fintype.card J / 2 + w * Fintype.card J / 2 +
        5 / 4 * (w * Fintype.card J : ℝ) * Real.sqrt (w * Fintype.card J)) := by
  have hd : 2 * ((Fintype.card (R × J) - Fintype.card κ : ℕ) : ℝ) ≤
      (Fintype.card R : ℝ) * Fintype.card J + w * Fintype.card J + D.largeCells.card := by
    exact_mod_cast D.dimension_le w hf
  have hb := D.largeCells_balanced w hf
  rw [D.code_card, Nat.cast_pow, ← Real.rpow_natCast]
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Fintype.card_pos (α := A))
  nlinarith

end InducedMatchingPartition
end
end LeanMachine.WholeRow
