import LeanMachine.FinitePacking
import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# Counting short paths from bounds on disjoint subfamilies

Paths have distinct designated starting vertices. The number passing through
one vertex is therefore bounded by a radius ball, not by the number of
combinatorial choices of paths.
-/

namespace LeanMachine.PathPacking

open scoped BigOperators

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    (G : SimpleGraph V)

omit [Fintype V] in
/-- A vertex on a short walk is within the same radius of its starting vertex. -/
theorem edist_start_le_of_mem_support {u v z : V} (p : G.Walk u v) {r : ℕ}
    (hlen : p.length ≤ r) (hz : z ∈ p.support) : G.edist z u ≤ (r : ℕ∞) := by
  calc
    G.edist z u ≤ ((p.takeUntil z hz).reverse).length := G.edist_le _
    _ = ((p.takeUntil z hz).length : ℕ∞) := by rw [SimpleGraph.Walk.length_reverse]
    _ ≤ (p.length : ℕ∞) := by exact_mod_cast p.length_takeUntil_le_length hz
    _ ≤ (r : ℕ∞) := by exact_mod_cast hlen

omit [DecidableEq I] in
/-- Distinct starting vertices inject all walks through one vertex into its
radius ball. The walks may be chosen arbitrarily. -/
theorem support_multiplicity_le_ball (source target : I → V)
    (hinj : Function.Injective source) (p : ∀ i, G.Walk (source i) (target i))
    (r : ℕ) (hlen : ∀ i, (p i).length ≤ r) (z : V) :
    (Finset.univ.filter (fun i => z ∈ (p i).support.toFinset)).card ≤
      (Finset.univ.filter (fun v => G.edist z v ≤ (r : ℕ∞))).card := by
  classical
  apply Finset.card_le_card_of_injOn source
  · intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      edist_start_le_of_mem_support G (p i) (hlen i)
        (List.mem_toFinset.mp (Finset.mem_filter.mp hi).2)⟩
  · exact hinj.injOn

/-- A chosen family of equal-length walks is bounded by its largest disjoint
subfamily, with the exact `(s+1)*ballBound` loss. -/
theorem fixed_length_count (source target : I → V)
    (hinj : Function.Injective source) (p : ∀ i, G.Walk (source i) (target i))
    (s r ballBound : ℕ) (hlen : ∀ i, (p i).length = s) (hsr : s ≤ r)
    (hball : ∀ z, (Finset.univ.filter (fun v => G.edist z v ≤ (r : ℕ∞))).card ≤ ballBound)
    (M : ℝ) (hM : ∀ J : Finset I,
      (J : Set I).PairwiseDisjoint (fun i => (p i).support.toFinset) → (J.card : ℝ) ≤ M) :
    (Fintype.card I : ℝ) ≤ ((s + 1 : ℕ) : ℝ) * ballBound * M := by
  classical
  apply FinitePacking.card_le_of_disjoint_bound (fun i => (p i).support.toFinset)
    (s + 1) ballBound _ _ _ M hM
  · intro i
    exact ⟨source i, List.mem_toFinset.mpr (p i).start_mem_support⟩
  · intro i
    calc
      (p i).support.toFinset.card ≤ (p i).support.length := List.toFinset_card_le _
      _ = s + 1 := by rw [SimpleGraph.Walk.length_support, hlen i]
  · intro z
    exact (support_multiplicity_le_ball G source target hinj p r
      (fun i => (hlen i).le.trans hsr) z).trans (hball z)

/-- Sum the disjoint-path bound separately over every attained odd length.
The family has one chosen walk per distinct starting endpoint. -/
theorem odd_length_count (source target : I → V)
    (hinj : Function.Injective source) (p : ∀ i, G.Walk (source i) (target i))
    (r ballBound : ℕ) (hlen : ∀ i, (p i).length ≤ r) (hodd : ∀ i, Odd (p i).length)
    (hball : ∀ z, (Finset.univ.filter (fun v => G.edist z v ≤ (r : ℕ∞))).card ≤ ballBound)
    (M : ℕ → ℝ)
    (hM : ∀ s, Odd s → s ≤ r → ∀ J : Finset I,
      (∀ i ∈ J, (p i).length = s) →
      (J : Set I).PairwiseDisjoint (fun i => (p i).support.toFinset) → (J.card : ℝ) ≤ M s) :
    (Fintype.card I : ℝ) ≤
      ∑ s ∈ (Finset.range (r + 1)).filter Odd, ((s + 1 : ℕ) : ℝ) * ballBound * M s := by
  classical
  let lengths := (Finset.range (r + 1)).filter Odd
  have hpartition : Fintype.card I =
      ∑ s ∈ lengths, (Finset.univ.filter (fun i => (p i).length = s)).card := by
    simpa only [Finset.card_univ] using
      (Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset I)) (t := lengths)
        (f := fun i => (p i).length) (fun i _ =>
          Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by change (p i).length < r + 1; exact Nat.lt_succ_of_le (hlen i)), hodd i⟩))
  rw [hpartition, Nat.cast_sum]
  apply Finset.sum_le_sum
  intro s hs
  have hsr : s ≤ r := by have := (Finset.mem_filter.mp hs).1; simp at this; omega
  have hso : Odd s := (Finset.mem_filter.mp hs).2
  let S := Finset.univ.filter (fun i => (p i).length = s)
  have hlenS (i : S) : (p i).length = s := (Finset.mem_filter.mp i.property).2
  have hrestricted := fixed_length_count G
    (fun i : S => source i) (fun i : S => target i)
    (hinj.comp Subtype.val_injective) (fun i : S => p i) s r ballBound hlenS hsr hball
    (M s) (fun J hJ => ?_)
  · simpa only [Fintype.card_coe] using hrestricted
  · let J' := J.image Subtype.val
    have hlenJ : ∀ i ∈ J', (p i).length = s := by
      intro i hi
      obtain ⟨i', _, rfl⟩ := Finset.mem_image.mp hi
      exact hlenS i'
    have hdisJ : (J' : Set I).PairwiseDisjoint (fun i => (p i).support.toFinset) := by
      intro i hi j hj hij
      obtain ⟨i', hi', rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨j', hj', rfl⟩ := Finset.mem_image.mp hj
      exact hJ hi' hj' (fun h => hij (congrArg Subtype.val h))
    have hcard : J'.card = J.card := Finset.card_image_of_injective J Subtype.val_injective
    rw [← hcard]
    exact hM s hso hsr J' hlenJ hdisJ

end LeanMachine.PathPacking
