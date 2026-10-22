import TransposeFollowup.RationalInverse
import TransposeFollowup.SymmetricOverlap

/-! An executable finite-family edge stream agrees exactly with the previous
real overlap graph. Each source row is built from bounded neighbor lists.
The stream needs no global deduplication; a finite set is also provided as
a convenient specification, without a runtime claim for its union operation. -/

namespace TransposeFollowup

open scoped BigOperators
set_option autoImplicit false

namespace BoundedMonotoneMap

noncomputable def widen {B C : ℕ} (F : BoundedMonotoneMap B) (hBC : B ≤ C) :
    BoundedMonotoneMap C where
  domain := F.domain
  map := F.map
  strictMono := F.strictMono
  forward x hx y hy := (F.forward x hx y hy).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hBC) (abs_nonneg _))
  backward x hx y hy := (F.backward x hx y hy).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hBC) (abs_nonneg _))

theorem widen_overlap {B C n : ℕ} (F : BoundedMonotoneMap B) (hBC : B ≤ C) (i j : Fin n) :
    (F.widen hBC).Overlap i j ↔ F.Overlap i j := Iff.rfl

end BoundedMonotoneMap

def rationalFamilyBound {c : ℕ} (F : Fin c → RationalMobius) : ℕ :=
  Finset.univ.sup (fun p => (F p).distortion)

theorem le_rationalFamilyBound {c : ℕ} (F : Fin c → RationalMobius) (p : Fin c) :
    (F p).distortion ≤ rationalFamilyBound F := by
  unfold rationalFamilyBound
  exact Finset.le_sup (f := fun q : Fin c => (F q).distortion) (Finset.mem_univ p)

noncomputable def rationalFamilyMaps {c : ℕ} (F : Fin c → RationalMobius) :
    Fin c → BoundedMonotoneMap (rationalFamilyBound F) :=
  fun p => (F p).bounded.widen (le_rationalFamilyBound F p)

def rationalFamilyNeighbors {c n : ℕ} (F : Fin c → RationalMobius) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.biUnion (fun p => (F p).neighbors i)

def rationalFamilyIncoming {c n : ℕ} (F : Fin c → RationalMobius) (j : Fin n) : Finset (Fin n) :=
  Finset.univ.biUnion (fun p => (F p).incomingNeighbors j)

def rationalFamilyEdges {c : ℕ} (F : Fin c → RationalMobius) (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.biUnion (fun i => (rationalFamilyNeighbors F i).image (fun j => (i, j)))

def rationalFamilyEdgeStream {c : ℕ} (F : Fin c → RationalMobius) (n : ℕ) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap (fun i =>
    ((rationalFamilyNeighbors F i).sort (· ≤ ·)).map (fun j => (i, j)))

theorem rationalFamilyEdgeStream_nodup {c : ℕ} (F : Fin c → RationalMobius) (n : ℕ) :
    (rationalFamilyEdgeStream F n).Nodup := by
  apply List.nodup_flatMap.mpr
  constructor
  · intro i _
    exact ((rationalFamilyNeighbors F i).sort_nodup (· ≤ ·)).map
      (fun _ _ h => congrArg Prod.snd h)
  · apply (List.nodup_finRange n).imp
    intro i i' hne e he he'
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp he
    obtain ⟨j', _, he'⟩ := List.mem_map.mp he'
    exact hne (congrArg Prod.fst he').symm

theorem mem_rationalFamilyEdgeStream {c n : ℕ} (F : Fin c → RationalMobius) (i j : Fin n) :
    (i, j) ∈ rationalFamilyEdgeStream F n ↔ j ∈ rationalFamilyNeighbors F i := by
  simp only [rationalFamilyEdgeStream, List.mem_flatMap, List.mem_finRange, true_and,
    List.mem_map, Finset.mem_sort, Prod.mk.injEq]
  constructor
  · rintro ⟨i', j', hj, hi, hje⟩
    subst i'
    subst j'
    exact hj
  · exact fun h => ⟨i, j, h, rfl, rfl⟩

theorem mem_rationalFamilyNeighbors {c n : ℕ} (F : Fin c → RationalMobius) (i j : Fin n) :
    j ∈ rationalFamilyNeighbors F i ↔ ∃ p, (rationalFamilyMaps F p).Overlap i j := by
  simp only [rationalFamilyNeighbors, Finset.mem_biUnion, Finset.mem_univ, true_and,
    RationalMobius.mem_neighbors, rationalFamilyMaps, BoundedMonotoneMap.widen_overlap]

theorem mem_rationalFamilyIncoming {c n : ℕ} (F : Fin c → RationalMobius) (i j : Fin n) :
    i ∈ rationalFamilyIncoming F j ↔ ∃ p, (rationalFamilyMaps F p).Overlap i j := by
  simp only [rationalFamilyIncoming, Finset.mem_biUnion, Finset.mem_univ, true_and,
    RationalMobius.mem_incomingNeighbors, rationalFamilyMaps, BoundedMonotoneMap.widen_overlap]

theorem rationalFamilyEdges_eq {c : ℕ} (F : Fin c → RationalMobius) (n : ℕ) :
    rationalFamilyEdges F n = overlapEdges (rationalFamilyMaps F) n := by
  ext e
  obtain ⟨i, j⟩ := e
  simp only [rationalFamilyEdges, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_image, Prod.mk.injEq]
  rw [mem_overlapEdges]
  constructor
  · rintro ⟨i', j', hj, hi, hje⟩
    subst i'
    subst j'
    exact (mem_rationalFamilyNeighbors F i j).mp hj
  · intro h
    exact ⟨i, j, (mem_rationalFamilyNeighbors F i j).mpr h, rfl, rfl⟩

theorem rationalFamilyNeighbors_card_le {c n : ℕ} (F : Fin c → RationalMobius) (i : Fin n) :
    (rationalFamilyNeighbors F i).card ≤ c * (rationalFamilyBound F + 1) := by
  calc
    _ ≤ ∑ p : Fin c, ((F p).neighbors i).card := Finset.card_biUnion_le
    _ ≤ ∑ _p : Fin c, (rationalFamilyBound F + 1) := Finset.sum_le_sum (fun p _ =>
      ((F p).neighbors_card_le i).trans (Nat.add_le_add_right (le_rationalFamilyBound F p) 1))
    _ = _ := by simp

theorem rationalFamilyEdges_card_le {c : ℕ} (F : Fin c → RationalMobius) (n : ℕ) :
    (rationalFamilyEdges F n).card ≤ n * (c * (rationalFamilyBound F + 1)) := by
  calc
    _ ≤ ∑ i : Fin n, ((rationalFamilyNeighbors F i).image (fun j => (i, j))).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ i : Fin n, (rationalFamilyNeighbors F i).card :=
      Finset.sum_le_sum (fun _ _ => Finset.card_image_le)
    _ ≤ ∑ _i : Fin n, c * (rationalFamilyBound F + 1) :=
      Finset.sum_le_sum (fun i _ => rationalFamilyNeighbors_card_le F i)
    _ = _ := by simp

theorem rationalFamilyEdgeStream_toFinset {c : ℕ} (F : Fin c → RationalMobius) (n : ℕ) :
    (rationalFamilyEdgeStream F n).toFinset = overlapEdges (rationalFamilyMaps F) n := by
  ext e
  obtain ⟨i, j⟩ := e
  rw [List.mem_toFinset, mem_rationalFamilyEdgeStream, mem_rationalFamilyNeighbors, mem_overlapEdges]

theorem rationalFamilyEdgeStream_length_le {c : ℕ} (F : Fin c → RationalMobius) (n : ℕ) :
    (rationalFamilyEdgeStream F n).length ≤ n * (c * (rationalFamilyBound F + 1)) := by
  rw [← List.toFinset_card_of_nodup (rationalFamilyEdgeStream_nodup F n),
    rationalFamilyEdgeStream_toFinset, ← rationalFamilyEdges_eq]
  exact rationalFamilyEdges_card_le F n

end TransposeFollowup
