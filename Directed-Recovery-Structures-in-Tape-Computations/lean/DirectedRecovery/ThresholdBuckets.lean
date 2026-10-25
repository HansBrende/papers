import LeanMachine.ThresholdPullback
import LeanMachine.BucketChains

/-!
# Finite threshold pullback into endpoint buckets

Actual word relations may be arbitrary subrelations of the full-band words.
Thus deleting permitted band pairs, omitting paths, or leaving domain gaps
does not require any additional hypothesis or cost.
-/

namespace DirectedRecovery.ThresholdPullback

open LeanMachine.ThresholdPullback
open Classical Finset
open scoped BigOperators
set_option autoImplicit false

/-- Every upper boundary of a monotone bucket map is an upper cut on rows. -/
theorem bucket_boundary_cut {d B : ℕ} (bucket : Fin d → Fin B)
    (hb : Monotone bucket) (j : ℕ) :
    ∃ c : Cut d, c.positive = true ∧
      ∀ y, c.holds y ↔ j < (bucket y).val := by
  let D : Finset (Fin d) := univ
  let P : D → Prop := fun y => j < (bucket y.val).val
  have hP : Monotone P := by
    intro x y hxy hx
    exact lt_of_lt_of_le hx (hb hxy)
  obtain ⟨θ, hθ⟩ := exists_upper_cut D P hP
  refine ⟨⟨θ, true⟩, rfl, ?_⟩
  intro y
  exact (hθ ⟨y, Finset.mem_univ _⟩).symm

/-- Uniformly polarized boundary comparisons force the claimed order of
all attained ending buckets. This applies to multivalued row relations. -/
theorem ordered_endings {d B : ℕ} (positive : Bool)
    (R : Fin d → Fin d → Prop) (T : Finset (Fin d)) (bucket : Fin d → Fin B)
    (a : Fin (B - 1) → Cut d) (hpol : ∀ j, (a j).positive = positive)
    (hex : ∀ j x, x ∉ T → ∀ y, R x y →
      ((a j).holds x ↔ j.val < (bucket y).val)) :
    ∀ x x', x ≤ x' → x ∉ T → x' ∉ T → ∀ y y', R x y → R x' y' →
      if positive then bucket y ≤ bucket y' else bucket y' ≤ bucket y := by
  intro x x' hxx hx hx' y y' hxy hx'y'
  cases hp : positive
  · simp only [Bool.false_eq_true, ite_false]
    by_contra hn
    have hlt : (bucket y).val < (bucket y').val := lt_of_not_ge hn
    let j : Fin (B - 1) := ⟨(bucket y).val, by have h := (bucket y').isLt; omega⟩
    have hy' : (a j).holds x' := (hex j x' hx' y' hx'y').mpr hlt
    have hy : (a j).holds x := (a j).antitone_holds ((hpol j).trans hp) hxx hy'
    exact (Nat.lt_irrefl _) ((hex j x hx y hxy).mp hy)
  · simp only [ite_true]
    by_contra hn
    have hlt : (bucket y').val < (bucket y).val := lt_of_not_ge hn
    let j : Fin (B - 1) := ⟨(bucket y').val, by have h := (bucket y).isLt; omega⟩
    have hy : (a j).holds x := (hex j x hx y hxy).mpr hlt
    have hy' : (a j).holds x' := (a j).monotone_holds ((hpol j).trans hp) hxx hy
    exact (Nat.lt_irrefl _) ((hex j x' hx' y' hx'y').mp hy')

/-- Bucket pairs attained by retained starting rows. -/
noncomputable def occupiedPairs {d B : ℕ} (R : Fin d → Fin d → Prop)
    (T : Finset (Fin d)) (start finish : Fin d → Fin B) : Finset (Fin B × Fin B) :=
  (univ.filter (fun xy : Fin d × Fin d => xy.1 ∉ T ∧ R xy.1 xy.2)).image
    (fun xy => (start xy.1, finish xy.2))

/-- Every actual endpoint pair with an uncharged starting row is included. -/
theorem mem_occupiedPairs_of_rel {d B : ℕ} {R : Fin d → Fin d → Prop}
    {T : Finset (Fin d)} (start finish : Fin d → Fin B)
    {x y : Fin d} (hx : x ∉ T) (hxy : R x y) :
    (start x, finish y) ∈ occupiedPairs R T start finish := by
  exact Finset.mem_image.mpr ⟨(x, y),
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx, hxy⟩, rfl⟩

/-- A signed monotone relation occupies at most `2*B-1` bucket pairs. -/
theorem occupiedPairs_card {d B : ℕ} (positive : Bool)
    (R : Fin d → Fin d → Prop) (T : Finset (Fin d))
    (start finish : Fin d → Fin B) (hstart : Monotone start)
    (hord : ∀ x x', x ≤ x' → x ∉ T → x' ∉ T → ∀ y y', R x y → R x' y' →
      if positive then finish y ≤ finish y' else finish y' ≤ finish y) :
    (occupiedPairs R T start finish).card ≤ 2 * B - 1 := by
  cases hp : positive
  · apply LeanMachine.BucketChains.card_le_of_oppositely_comparable
    intro a ha b hb
    obtain ⟨⟨x, y⟩, hxy, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨⟨x', y'⟩, hx'y', rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨hx, hR⟩ := (Finset.mem_filter.mp hxy).2
    obtain ⟨hx', hR'⟩ := (Finset.mem_filter.mp hx'y').2
    rcases le_total x x' with h | h
    · exact Or.inl ⟨hstart h, by simpa [hp] using hord x x' h hx hx' y y' hR hR'⟩
    · exact Or.inr ⟨hstart h, by simpa [hp] using hord x' x h hx' hx y' y hR' hR⟩
  · apply LeanMachine.BucketChains.card_le_of_comparable
    intro a ha b hb
    obtain ⟨⟨x, y⟩, hxy, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨⟨x', y'⟩, hx'y', rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨hx, hR⟩ := (Finset.mem_filter.mp hxy).2
    obtain ⟨hx', hR'⟩ := (Finset.mem_filter.mp hx'y').2
    rcases le_total x x' with h | h
    · exact Or.inl ⟨hstart h, by simpa [hp] using hord x x' h hx hx' y y' hR hR'⟩
    · exact Or.inr ⟨hstart h, by simpa [hp] using hord x' x h hx' hx y' y hR' hR⟩

/-- The complete finite threshold-pullback statement, with its exact
exception budget, one ending bucket per attained retained row, signed
monotonicity, and the union bound on occupied bucket pairs. -/
theorem finite_threshold_pullback {d B K : ℕ} (r ell : ℕ)
    (w : Fin K → Word d d) (hmaps : ∀ i, (w i).maps ≤ ell)
    (R : Fin K → Fin d → Fin d → Prop)
    (hR : ∀ i x y, R i x y → (w i).Rel r x y)
    (start finish : Fin d → Fin B) (hstart : Monotone start) (hfinish : Monotone finish) :
    ∃ T : Finset (Fin d),
      T.card ≤ min d (K * (B - 1) * ((2 * r + 1) ^ (ell + 1) - 1)) ∧
      (∀ i x, x ∉ T → ∀ y z, R i x y → R i x z → finish y = finish z) ∧
      (∀ i x x', x ≤ x' → x ∉ T → x' ∉ T → ∀ y y', R i x y → R i x' y' →
        if (w i).positive then finish y ≤ finish y' else finish y' ≤ finish y) ∧
      (univ.biUnion (fun i => occupiedPairs (R i) T start finish)).card ≤ K * (2 * B - 1) := by
  let err := (2 * r + 1) ^ (ell + 1) - 1
  have hcuts : ∀ (i : Fin K) (j : Fin (B - 1)), ∃ a : Cut d, ∃ U : Finset (Fin d),
      a.positive = (w i).positive ∧ U.card ≤ err ∧
      ∀ x, x ∉ U → ∀ y, R i x y → (a.holds x ↔ j.val < (finish y).val) := by
    intro i j
    obtain ⟨c, hc, hcb⟩ := bucket_boundary_cut finish hfinish j.val
    obtain ⟨a, U, ha, hU, he⟩ := word_threshold_pullback r (w i) c
    refine ⟨a, U, ?_, ?_, ?_⟩
    · simpa [hc] using ha
    · apply hU.trans
      exact Nat.sub_le_sub_right (Nat.pow_le_pow_right (by omega : 0 < 2 * r + 1)
        (Nat.add_le_add_right (hmaps i) 1)) 1
    · intro x hx y hxy
      exact (he x hx y (hR i x y hxy)).trans (hcb y)
  choose a U hpol hU hex using hcuts
  let T : Finset (Fin d) := univ.biUnion (fun i => univ.biUnion (fun j => U i j))
  have hT : T.card ≤ K * (B - 1) * err := by
    calc
      T.card ≤ ∑ i : Fin K, (univ.biUnion (fun j => U i j)).card := Finset.card_biUnion_le
      _ ≤ ∑ i : Fin K, ∑ j : Fin (B - 1), (U i j).card :=
        Finset.sum_le_sum (fun i _ => Finset.card_biUnion_le)
      _ ≤ ∑ _i : Fin K, ∑ _j : Fin (B - 1), err :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hU i j))
      _ = K * (B - 1) * err := by simp [Nat.mul_assoc]
  have hout : ∀ i j x, x ∉ T → x ∉ U i j := by
    intro i j x hx hu
    exact hx (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _,
      Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hu⟩⟩)
  have hord : ∀ i x x', x ≤ x' → x ∉ T → x' ∉ T → ∀ y y', R i x y → R i x' y' →
      if (w i).positive then finish y ≤ finish y' else finish y' ≤ finish y := by
    intro i
    apply ordered_endings (w i).positive (R i) T finish (a i) (hpol i)
    intro j x hx y hxy
    exact hex i j x (hout i j x hx) y hxy
  refine ⟨T, le_min (by simpa using Finset.card_le_univ T) hT, ?_, hord, ?_⟩
  · intro i x hx y z hxy hxz
    have hyz := hord i x x le_rfl hx hx y z hxy hxz
    have hzy := hord i x x le_rfl hx hx z y hxz hxy
    cases hp : (w i).positive <;> simp only [hp, Bool.false_eq_true, ite_false, ite_true] at hyz hzy
    · exact le_antisymm hzy hyz
    · exact le_antisymm hyz hzy
  · calc
      _ ≤ ∑ i : Fin K, (occupiedPairs (R i) T start finish).card := Finset.card_biUnion_le
      _ ≤ ∑ _i : Fin K, (2 * B - 1) := Finset.sum_le_sum (fun i _ =>
        occupiedPairs_card (w i).positive (R i) T start finish hstart (hord i))
      _ = K * (2 * B - 1) := by simp

end DirectedRecovery.ThresholdPullback
