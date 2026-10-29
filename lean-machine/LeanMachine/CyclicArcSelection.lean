import LeanMachine.CyclicSelection

/-!
# Safe common orders for an empty circular arc

Every point of an uncovered circular arc precedes the covered set under at
least `ell + 1` cut-and-orientation choices. The covered set may be empty.
-/

namespace LeanMachine.CyclicSelection

open Finset
noncomputable section

/-- Reverse orientation reverses the same cut order. -/
def orientedRank (L cut : ℕ) (reverse : Bool) (z : ℕ) : ℤ :=
  if reverse then -rank L cut z else rank L cut z

/-- A natural-valued rank for the same order, suitable for reverse recovery. -/
def orientedRankNat (L cut : ℕ) (reverse : Bool) (z : ℕ) : ℕ :=
  (orientedRank L cut reverse z + L).toNat

theorem orientedRank_lt_iff_nat {L cut x y : ℕ} {reverse : Bool} (hL : 0 < L) :
    orientedRank L cut reverse x < orientedRank L cut reverse y ↔
      orientedRankNat L cut reverse x < orientedRankNat L cut reverse y := by
  have hx := rank_nonneg (cut := cut) (z := x) hL
  have hy := rank_nonneg (cut := cut) (z := y) hL
  have hxL := rank_lt (cut := cut) (z := x) hL
  have hyL := rank_lt (cut := cut) (z := y) hL
  unfold orientedRankNat orientedRank
  cases reverse <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

/-- Common orders in which `z` precedes every member of `T`. -/
def selectingOrders (L : ℕ) (T : Finset ℕ) (z : ℕ) : Finset (ℕ × Bool) :=
  ((range L) ×ˢ univ).filter fun p => ∀ y ∈ T,
    orientedRank L p.1 p.2 z < orientedRank L p.1 p.2 y

theorem mem_selectingOrders_iff_nat {L z : ℕ} {T : Finset ℕ} {p : ℕ × Bool}
    (hL : 0 < L) : p ∈ selectingOrders L T z ↔
      p.1 < L ∧ ∀ y ∈ T, orientedRankNat L p.1 p.2 z < orientedRankNat L p.1 p.2 y := by
  simp only [selectingOrders, mem_filter, mem_product, mem_range, mem_univ, and_true,
    orientedRank_lt_iff_nat hL]

private theorem outside_arc_representation {L a ell y : ℕ}
    (hL : 0 < L) (hy : y < L) (hout : y ∉ arc L a ell) :
    ∃ q, ell ≤ q ∧ q < L ∧ (a + q) % L = y := by
  let q := forward L (a % L) y
  have hq : q < L := forward_lt (Nat.mod_lt _ hL) hy
  have he : (a + q) % L = y := by
    have h := mod_add_forward (Nat.mod_lt a hL) hy
    simpa only [Nat.add_mod, Nat.mod_mod] using h
  refine ⟨q, ?_, hq, he⟩
  by_contra h
  exact hout (mem_image.mpr ⟨q, mem_range.mpr (by omega), he⟩)

private theorem safe_arc_order {L a ell k t : ℕ} {T : Finset ℕ}
    (hell : ell ≤ L) (hk : k < ell) (ht : t ≤ ell)
    (hT : T ⊆ range L) (hdis : Disjoint (arc L a ell) T) :
    ((a + t) % L, decide (k < t)) ∈ selectingOrders L T ((a + k) % L) := by
  have hL : 0 < L := by omega
  apply mem_filter.mpr
  refine ⟨mem_product.mpr ⟨mem_range.mpr (Nat.mod_lt _ hL), mem_univ _⟩, ?_⟩
  intro y hy
  obtain ⟨q, hqe, hqL, hqy⟩ := outside_arc_representation hL (mem_range.mp (hT hy))
    (fun hyarc => disjoint_left.mp hdis hyarc hy)
  rw [← hqy]
  by_cases hkt : k < t
  · simp only [orientedRank, hkt, decide_true, ↓reduceIte,
      rank_rotate]
    have hkmod : ((k : ℤ) - t) % L = L + ((k : ℤ) - t) := by
      rw [← Int.add_emod_left (L : ℤ) ((k : ℤ) - t)]
      exact Int.emod_eq_of_lt (by omega) (by omega)
    have hqmod : ((q : ℤ) - t) % L = (q : ℤ) - t :=
      Int.emod_eq_of_lt (by omega) (by omega)
    rw [hkmod, hqmod]
    omega
  · simp only [orientedRank, hkt, decide_false, Bool.false_eq_true, ↓reduceIte,
      rank_rotate]
    have hkmod : ((k : ℤ) - t) % L = (k : ℤ) - t :=
      Int.emod_eq_of_lt (by omega) (by omega)
    have hqmod : ((q : ℤ) - t) % L = (q : ℤ) - t :=
      Int.emod_eq_of_lt (by omega) (by omega)
    rw [hkmod, hqmod]
    omega

/-- The two orientations contribute at least `ell + 1` safe choices for each
point of an uncovered arc of length `ell`. No nonemptiness of `T` is needed. -/
theorem arc_selection_card_lower {L a ell k : ℕ} {T : Finset ℕ}
    (hell : ell ≤ L) (hk : k < ell)
    (hT : T ⊆ range L) (hdis : Disjoint (arc L a ell) T) :
    ell + 1 ≤ (selectingOrders L T ((a + k) % L)).card := by
  have hL : 0 < L := by omega
  let f := fun t => ((a + t) % L, decide (k < t))
  have hmap : Set.MapsTo f (range (ell + 1))
      (selectingOrders L T ((a + k) % L)) := by
    intro t ht
    exact safe_arc_order hell hk (by have := mem_range.mp ht; omega) hT hdis
  have hinj : Set.InjOn f (range (ell + 1)) := by
    intro t ht u hu he
    have htL : t ≤ L := by have := mem_range.mp ht; omega
    have huL : u ≤ L := by have := mem_range.mp hu; omega
    have hc : (a + t) % L = (a + u) % L := congrArg Prod.fst he
    have hd : decide (k < t) = decide (k < u) := congrArg Prod.snd he
    have hm : t % L = u % L := Nat.ModEq.add_left_cancel' a hc
    by_cases ht' : t < L
    · by_cases hu' : u < L
      · simpa only [Nat.mod_eq_of_lt ht', Nat.mod_eq_of_lt hu'] using hm
      · have huL' : u = L := by omega
        have ht0 : t = 0 := by simpa [huL', Nat.mod_eq_of_lt ht'] using hm
        simp [ht0, huL', show k < L by omega] at hd
    · have htL' : t = L := by omega
      by_cases hu' : u < L
      · have hu0 : u = 0 := by simpa [htL', Nat.mod_eq_of_lt hu'] using hm.symm
        simp [hu0, htL', show k < L by omega] at hd
      · omega
  simpa only [card_range] using card_le_card_of_injOn f hmap hinj

/-- Coordinate-membership form of the safe-order count. -/
theorem arc_selection_card_lower_of_mem {L a ell z : ℕ} {T : Finset ℕ}
    (hell : ell ≤ L) (hz : z ∈ arc L a ell)
    (hT : T ⊆ range L) (hdis : Disjoint (arc L a ell) T) :
    ell + 1 ≤ (selectingOrders L T z).card := by
  obtain ⟨k, hk, rfl⟩ := mem_image.mp hz
  exact arc_selection_card_lower hell (mem_range.mp hk) hT hdis

end
end LeanMachine.CyclicSelection
