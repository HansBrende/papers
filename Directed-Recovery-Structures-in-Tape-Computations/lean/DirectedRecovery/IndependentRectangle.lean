import Mathlib

/-!
# Independent rectangles from sparse bucket incidence

The finite rectangle lemma is purely combinatorial.  A bucket partition enters
only through the lower bound on the cardinality of every fibre; neither order nor
contiguity is needed for the conclusion.  Hence the result applies in particular
to the near-equal consecutive buckets used in the manuscript.
-/

namespace DirectedRecovery

open Classical
open scoped BigOperators
set_option autoImplicit false

namespace IndependentRectangle

abbrev Coordinate (d b : ℕ) := Fin d × Fin d × Fin b

/-- Raw buckets incident to one output bucket. -/
noncomputable def bucketNeighbors {B : ℕ} (E : Finset (Fin B × Fin B))
    (c : Fin B) : Finset (Fin B) :=
  (E.filter (fun e => e.2 = c)).image Prod.fst

theorem mem_bucketNeighbors {B : ℕ} (E : Finset (Fin B × Fin B))
    (a c : Fin B) : a ∈ bucketNeighbors E c ↔ (a, c) ∈ E := by
  constructor
  · intro h
    obtain ⟨⟨x, y⟩, hxy, hx⟩ := Finset.mem_image.mp h
    obtain ⟨he, hy⟩ := Finset.mem_filter.mp hxy
    change x = a at hx
    change y = c at hy
    subst x
    subst y
    exact he
  · intro h
    exact Finset.mem_image.mpr ⟨(a, c), Finset.mem_filter.mpr ⟨h, rfl⟩, rfl⟩

theorem sum_bucketNeighbors_le {B : ℕ} (E : Finset (Fin B × Fin B)) :
    (∑ c, (bucketNeighbors E c).card) ≤ E.card := by
  calc
    _ ≤ ∑ c : Fin B, (E.filter (fun e => e.2 = c)).card := by
      exact Finset.sum_le_sum (fun c _ => Finset.card_image_le)
    _ = E.card := by
      simpa using Finset.sum_card_fiberwise_eq_card_filter E Finset.univ Prod.snd

/-- A sparse bucket graph has one output bucket incident to at most `2*K-1`
raw buckets.  The strict quarter-bucket margin avoids rounding assumptions. -/
theorem exists_sparse_bucket {K : ℕ} (hK : 0 < K)
    (E : Finset (Fin (4 * K) × Fin (4 * K)))
    (hE : E.card ≤ K * (8 * K - 1)) :
    ∃ c, (bucketNeighbors E c).card ≤ 2 * K - 1 := by
  by_contra! h
  have hpoint : ∀ c, 2 * K ≤ (bucketNeighbors E c).card := by
    intro c
    have := h c
    omega
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun c _ => hpoint c)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  have htotal := sum_bucketNeighbors_le E
  have hsub : 8 * K - 1 + 1 = 8 * K := by omega
  nlinarith

/-- A union of bucket fibres, each of cardinality at least `m`, has at least
`m` times as many rows as bucket labels. -/
theorem bucket_union_card_lower {d B m : ℕ} (bucket : Fin d → Fin B)
    (hsize : ∀ a, m ≤ (Finset.univ.filter (fun i => bucket i = a)).card)
    (A : Finset (Fin B)) :
    A.card * m ≤ (Finset.univ.filter (fun i => bucket i ∈ A)).card := by
  calc
    A.card * m = ∑ _a ∈ A, m := by simp
    _ ≤ ∑ a ∈ A, (Finset.univ.filter (fun i => bucket i = a)).card :=
      Finset.sum_le_sum (fun a _ => hsize a)
    _ = _ := Finset.sum_card_fiberwise_eq_card_filter Finset.univ A bucket

/-- The full finite independent-rectangle conclusion, in an equivalent
additive cardinality form.  The bucket maps may differ on the two sides.
Near-equal consecutive partitions satisfy the two stated fibre-size hypotheses.
The relation `N` is the full directed recovery relation; no edges are pruned. -/
theorem independent_rectangle {d b K : ℕ} (hK : 0 < K)
    (rawBucket outBucket : Fin d → Fin (4 * K))
    (hraw : ∀ a, d / (4 * K) ≤
      (Finset.univ.filter (fun i => rawBucket i = a)).card)
    (hout : ∀ c, d / (4 * K) ≤
      (Finset.univ.filter (fun j => outBucket j = c)).card)
    (E : Finset (Fin (4 * K) × Fin (4 * K)))
    (hE : E.card ≤ K * (8 * K - 1))
    (S T : Finset (Fin d)) (Z : Finset (Coordinate d b))
    (N : Coordinate d b → Finset (Coordinate d b))
    (hcover : ∀ p q, p ∉ Z → q ∉ Z → p.1 ∉ S → q.2.1 ∉ T →
      p ∈ N q → (rawBucket p.1, outBucket q.2.1) ∈ E) :
    ∃ I : Finset (Coordinate d b),
      (∀ q ∈ I, ∀ p ∈ I, p ∉ N q) ∧
      b * (2 * K + 1) * (d / (4 * K)) ^ 2 ≤
        I.card + b * d * (S.card + T.card) + Z.card := by
  obtain ⟨c, hc⟩ := exists_sparse_bucket hK E hE
  let A : Finset (Fin (4 * K)) := Finset.univ \ bucketNeighbors E c
  let R : Finset (Fin d) := Finset.univ.filter (fun i => rawBucket i ∈ A)
  let C : Finset (Fin d) := Finset.univ.filter (fun j => outBucket j = c)
  let rect : Finset (Coordinate d b) := R ×ˢ (C ×ˢ Finset.univ)
  let badS : Finset (Coordinate d b) := S ×ˢ (Finset.univ ×ˢ Finset.univ)
  let badT : Finset (Coordinate d b) := Finset.univ ×ˢ (T ×ˢ Finset.univ)
  let bad := badS ∪ badT ∪ Z
  let I := rect \ bad
  have hAc : 2 * K + 1 ≤ A.card := by
    have he : A.card = 4 * K - (bucketNeighbors E c).card := by
      simp [A, Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    omega
  have hRc : (2 * K + 1) * (d / (4 * K)) ≤ R.card := by
    exact (Nat.mul_le_mul_right _ hAc).trans (bucket_union_card_lower rawBucket hraw A)
  have hCc : d / (4 * K) ≤ C.card := hout c
  have hrect : b * (2 * K + 1) * (d / (4 * K)) ^ 2 ≤ rect.card := by
    have hh := Nat.mul_le_mul hRc hCc
    have hh' := Nat.mul_le_mul_left b hh
    simpa only [rect, Finset.card_product, Finset.card_univ, Fintype.card_fin,
      pow_two, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hh'
  have hbad : bad.card ≤ b * d * (S.card + T.card) + Z.card := by
    calc
      bad.card ≤ (badS ∪ badT).card + Z.card := Finset.card_union_le _ _
      _ ≤ (badS.card + badT.card) + Z.card :=
        Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ = _ := by
        simp only [badS, badT, Finset.card_product, Finset.card_univ, Fintype.card_fin]
        ring
  refine ⟨I, ?_, ?_⟩
  · intro q hq p hp hpq
    obtain ⟨hpRect, hpBad⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨hqRect, hqBad⟩ := Finset.mem_sdiff.mp hq
    have hpR := (Finset.mem_product.mp hpRect).1
    have hqC := (Finset.mem_product.mp (Finset.mem_product.mp hqRect).2).1
    have hpA := (Finset.mem_filter.mp hpR).2
    have hqc := (Finset.mem_filter.mp hqC).2
    have hpZ : p ∉ Z := by
      intro h
      exact hpBad (Finset.mem_union_right _ h)
    have hqZ : q ∉ Z := by
      intro h
      exact hqBad (Finset.mem_union_right _ h)
    have hpS : p.1 ∉ S := by
      intro h
      apply hpBad
      exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_product.mpr ⟨h, Finset.mem_product.mpr
          ⟨Finset.mem_univ _, Finset.mem_univ _⟩⟩))
    have hqT : q.2.1 ∉ T := by
      intro h
      apply hqBad
      exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_product.mpr
          ⟨h, Finset.mem_univ _⟩⟩))
    have hedge := hcover p q hpZ hqZ hpS hqT hpq
    rw [hqc] at hedge
    exact (Finset.mem_sdiff.mp hpA).2 ((mem_bucketNeighbors E _ _).mpr hedge)
  · have hh : rect.card ≤ I.card + bad.card := Finset.card_le_card_sdiff_add_card
    exact hrect.trans (hh.trans (by omega))

/-! ## Consecutive near-equal buckets

Bucket `a` is the half-open interval
`[a*d/B, (a+1)*d/B)`, with both endpoints rounded down.  The following
cardinality lemma provides the precise floor bound used above.
-/

theorem interval_card {d lo hi : ℕ} (hlo : lo ≤ hi) (hhi : hi ≤ d) :
    (Finset.univ.filter (fun i : Fin d => lo ≤ i.val ∧ i.val < hi)).card = hi - lo := by
  have he : Finset.univ.filter (fun i : Fin d => lo ≤ i.val ∧ i.val < hi) =
      (Finset.univ.filter (fun i : Fin d => i.val < hi)) \
        (Finset.univ.filter (fun i : Fin d => i.val < lo)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
    omega
  have hs : Finset.univ.filter (fun i : Fin d => i.val < lo) ⊆
      Finset.univ.filter (fun i : Fin d => i.val < hi) := by
    intro i hi'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' ⊢
    omega
  rw [he, Finset.card_sdiff_of_subset hs, Fin.card_filter_val_lt,
    Fin.card_filter_val_lt, Nat.min_eq_right hhi, Nat.min_eq_right (hlo.trans hhi)]

theorem consecutive_bucket_size {d B : ℕ} (hB : 0 < B) (a : Fin B) :
    d / B ≤ (Finset.univ.filter (fun i : Fin d =>
      a.val * d / B ≤ i.val ∧ i.val < (a.val + 1) * d / B)).card := by
  have hstep : a.val * d / B + d / B ≤ (a.val + 1) * d / B := by
    simpa only [Nat.add_mul, Nat.one_mul] using
      (Nat.div_add_div_le_add_div (x := a.val * d) (y := d) (z := B))
  have hupper : (a.val + 1) * d / B ≤ d := by
    have hmul : (a.val + 1) * d ≤ B * d := Nat.mul_le_mul_right d (by omega)
    have hd := Nat.div_le_div_right (c := B) hmul
    simpa [Nat.mul_div_right, hB.ne'] using hd
  have hlower : a.val * d / B ≤ (a.val + 1) * d / B :=
    (Nat.le_add_right _ _).trans hstep
  rw [interval_card hlower hupper]
  omega

/-- A direct specialization to the usual consecutive near-equal partition.
The interval description specifies the partition exactly, rather than imposing
an additional minimum-size assumption. -/
theorem independent_rectangle_consecutive {d b K : ℕ} (hK : 0 < K)
    (bucket : Fin d → Fin (4 * K))
    (hinterval : ∀ i a, bucket i = a ↔
      a.val * d / (4 * K) ≤ i.val ∧ i.val < (a.val + 1) * d / (4 * K))
    (E : Finset (Fin (4 * K) × Fin (4 * K)))
    (hE : E.card ≤ K * (8 * K - 1))
    (S T : Finset (Fin d)) (Z : Finset (Coordinate d b))
    (N : Coordinate d b → Finset (Coordinate d b))
    (hcover : ∀ p q, p ∉ Z → q ∉ Z → p.1 ∉ S → q.2.1 ∉ T →
      p ∈ N q → (bucket p.1, bucket q.2.1) ∈ E) :
    ∃ I : Finset (Coordinate d b),
      (∀ q ∈ I, ∀ p ∈ I, p ∉ N q) ∧
      b * (2 * K + 1) * (d / (4 * K)) ^ 2 -
        (b * d * (S.card + T.card) + Z.card) ≤ I.card := by
  have hsize : ∀ a, d / (4 * K) ≤
      (Finset.univ.filter (fun i => bucket i = a)).card := by
    intro a
    simpa only [hinterval] using consecutive_bucket_size (d := d) (by omega) a
  obtain ⟨I, hI, hcard⟩ := independent_rectangle hK bucket bucket hsize hsize E hE S T Z N hcover
  exact ⟨I, hI, by omega⟩

end IndependentRectangle
end DirectedRecovery
