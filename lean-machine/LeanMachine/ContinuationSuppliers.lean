import LeanMachine.CausalClosure
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Supplier reductions for two ordered causal extensions. Neither extension
map needs to be injective; identity maps and coincident landings are allowed. -/

namespace LeanMachine.CausalClosure

open Classical Finset
open scoped BigOperators
noncomputable section

def landings (S : Finset ℕ) (f : ℕ → ℕ) : Finset ℕ :=
  (S.filter fun u => f u ≠ u).image f

def extend (C D : CausalClosure) (f : ℕ → ℕ) (t : ℕ) : Finset ℕ :=
  D.reach t ∪ (C.reach t).biUnion (fun u => D.reach (f u))

def suppliers (C D : CausalClosure) (f : ℕ → ℕ) (t : ℕ) : Finset ℕ :=
  D.maximal (insert t (landings (C.reach t) f))

theorem extend_eq_hull_suppliers (C D : CausalClosure)
    (hCD : ∀ t, C.reach t ⊆ D.reach t) (f : ℕ → ℕ) (t : ℕ) :
    C.extend D f t = D.hull (C.suppliers D f t) := by
  rw [suppliers, D.hull_maximal]
  ext v
  simp only [extend, hull, biUnion_insert, mem_union, mem_biUnion, landings, mem_image,
    mem_filter]
  constructor
  · rintro (hv | ⟨u, hu, hv⟩)
    · exact Or.inl hv
    · by_cases he : f u = u
      · exact Or.inl (D.trans (hCD t hu) (he ▸ hv))
      · exact Or.inr ⟨f u, ⟨u, ⟨hu, he⟩, rfl⟩, hv⟩
  · rintro (hv | ⟨v, ⟨u, ⟨hu, _⟩, rfl⟩, hv⟩)
    · exact Or.inl hv
    · exact Or.inr ⟨u, hu, hv⟩

theorem supplier_past (C D : CausalClosure) (f : ℕ → ℕ)
    (hf : ∀ u, f u ≤ u) {t u : ℕ} (hu : u ∈ C.suppliers D f t) : u ≤ t := by
  rcases mem_insert.mp (D.maximal_subset _ hu) with rfl | hu
  · exact le_rfl
  · obtain ⟨v, hv, rfl⟩ := mem_image.mp hu
    exact (hf v).trans (C.past (mem_filter.mp hv).1)

theorem root_mem_suppliers (C D : CausalClosure) (f : ℕ → ℕ)
    (hf : ∀ u, f u ≤ u) (t : ℕ) : t ∈ C.suppliers D f t := by
  apply D.root_mem_maximal (mem_insert_self t _)
  intro u hu
  rcases mem_insert.mp hu with rfl | hu
  · exact le_rfl
  · obtain ⟨v, hv, rfl⟩ := mem_image.mp hu
    exact (hf v).trans (C.past (mem_filter.mp hv).1)

/-- An older extension from any finite seed family is covered by complete
core orbits. The actual per-seed core cardinalities give a sharper budget. -/
theorem hull_extension_core_cover (C D : CausalClosure) (e : ℕ → ℕ)
    (hD : ∀ t, D.reach t = C.extend C e t) (S : Finset ℕ) :
    ∃ R : Finset ℕ, R.card ≤ ∑ u ∈ S, (1 + (C.reach u).card) ∧
      C.hull R = D.hull S := by
  let R := S.biUnion fun u => insert u ((C.reach u).image e)
  refine ⟨R, ?_, ?_⟩
  · exact card_biUnion_le.trans (sum_le_sum fun u _ =>
      (card_insert_le ..).trans (Nat.add_le_add_right card_image_le 1) |>.trans_eq (Nat.add_comm ..))
  · change R.biUnion C.reach = S.biUnion D.reach
    dsimp only [R]
    rw [biUnion_biUnion]
    apply biUnion_congr rfl
    intro u _
    rw [hD u]
    simp only [biUnion_insert, image_biUnion, extend]

theorem hull_extension_core_cover_uniform (C D : CausalClosure) (e : ℕ → ℕ)
    (hD : ∀ t, D.reach t = C.extend C e t) {ell : ℕ}
    (hcard : ∀ t, (C.reach t).card ≤ ell) (S : Finset ℕ) :
    ∃ R : Finset ℕ, R.card ≤ (ell + 1) * S.card ∧ C.hull R = D.hull S := by
  obtain ⟨R, hR, he⟩ := C.hull_extension_core_cover D e hD S
  refine ⟨R, hR.trans ?_, he⟩
  calc
    _ ≤ ∑ _u ∈ S, (ell + 1) := sum_le_sum fun u _ => by have := hcard u; omega
    _ = _ := by simp [Nat.mul_comm]

/-- Expanding the two layers in the other order gives the complete older
landings after the newer-only closure. No commutation of maps is asserted. -/
theorem two_extension_eq (C D G : CausalClosure) (e g : ℕ → ℕ)
    (hD : ∀ t, D.reach t = C.extend C e t)
    (hG : ∀ t, G.reach t = C.extend C g t) (t : ℕ) :
    C.extend D g t = G.reach t ∪ C.hull ((G.reach t).image e) := by
  simp only [extend, hD, hG, hull, biUnion_union, image_union, image_biUnion,
    union_biUnion, biUnion_image, biUnion_biUnion]
  ac_rfl

theorem landing_diff_eq (S : Finset ℕ) (f : ℕ → ℕ) :
    landings S f \ S = S.image f \ S := by
  ext u
  simp only [landings, mem_sdiff, mem_image, mem_filter]
  aesop

/-- The older landing bound discards only points already in the complete
newer closure, then keeps maximal remaining seeds for the core relation. -/
theorem two_extension_maximal_landings (C D G : CausalClosure) (e g : ℕ → ℕ)
    (hCG : ∀ t, C.reach t ⊆ G.reach t)
    (hD : ∀ t, D.reach t = C.extend C e t)
    (hG : ∀ t, G.reach t = C.extend C g t) (t : ℕ) :
    C.extend D g t = G.reach t ∪
      C.hull (C.maximal (landings (G.reach t) e \ G.reach t)) := by
  rw [C.two_extension_eq D G e g hD hG, landing_diff_eq]
  exact (C.closed_union_hull_maximal_diff
    (fun u hu v hv => G.trans hu (hCG u hv)) _).symm

end
end LeanMachine.CausalClosure
