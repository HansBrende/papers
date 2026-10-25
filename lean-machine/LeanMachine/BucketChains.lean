import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.Rev
import Mathlib.Order.Fin.Basic
import Mathlib.Order.Monotone.Basic
import Lean.Elab.Tactic.Omega

/-!
# Finite chains of ordered bucket pairs

A coordinatewise chain in a `B` by `B` grid has at most `2 * B - 1`
points. Reversing the second coordinate gives the same bound for an
oppositely ordered chain. The image corollaries allow an arbitrary finite
subset of an ordered domain; no consecutive attainment or interval
hypothesis is needed.
-/

namespace LeanMachine.BucketChains

/-- A chain of pairs of `B` ordered buckets contains at most `2B - 1` pairs.
The statement also covers the empty grid `B = 0`. -/
theorem card_le_of_comparable {B : ℕ} (E : Finset (Fin B × Fin B))
    (hE : ∀ a ∈ E, ∀ b ∈ E,
      (a.1 ≤ b.1 ∧ a.2 ≤ b.2) ∨ (b.1 ≤ a.1 ∧ b.2 ≤ a.2)) :
    E.card ≤ 2 * B - 1 := by
  have hmap : Set.MapsTo (fun a : Fin B × Fin B => a.1.val + a.2.val)
      E (Finset.range (2 * B - 1)) := by
    intro a _
    simp only [Finset.mem_coe, Finset.mem_range]
    have h₁ := a.1.isLt
    have h₂ := a.2.isLt
    omega
  have hinj : Set.InjOn (fun a : Fin B × Fin B => a.1.val + a.2.val) E := by
    intro a ha b hb hab
    change a.1.val + a.2.val = b.1.val + b.2.val at hab
    rcases hE a ha b hb with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · apply Prod.ext <;> apply Fin.ext <;> simp only [Fin.le_iff_val_le_val] at h₁ h₂ <;> omega
    · apply Prod.ext <;> apply Fin.ext <;> simp only [Fin.le_iff_val_le_val] at h₁ h₂ <;> omega
  simpa only [Finset.card_range] using Finset.card_le_card_of_injOn _ hmap hinj

/-- The same bound holds when the two bucket coordinates are oppositely ordered. -/
theorem card_le_of_oppositely_comparable {B : ℕ} (E : Finset (Fin B × Fin B))
    (hE : ∀ a ∈ E, ∀ b ∈ E,
      (a.1 ≤ b.1 ∧ b.2 ≤ a.2) ∨ (b.1 ≤ a.1 ∧ a.2 ≤ b.2)) :
    E.card ≤ 2 * B - 1 := by
  let r : Fin B × Fin B → Fin B × Fin B := fun a => (a.1, a.2.rev)
  have hr : Function.Injective r := by
    intro a b h
    change (a.1, a.2.rev) = (b.1, b.2.rev) at h
    apply Prod.ext
    · exact (Prod.mk.inj h).1
    · exact Fin.rev_injective (Prod.mk.inj h).2
  rw [← Finset.card_image_of_injective E hr]
  apply card_le_of_comparable
  intro a ha b hb
  obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨b', hb', rfl⟩ := Finset.mem_image.mp hb
  simpa only [r, Fin.rev_le_rev] using hE a' ha' b' hb'

/-- Simultaneously monotone bucket coordinates attain at most `2B - 1`
pairs on any finite selected domain, including domains with arbitrary gaps. -/
theorem card_image_mono {α : Type*} [LinearOrder α] {B : ℕ}
    (D : Finset α) (f g : α → Fin B)
    (hf : MonotoneOn f (D : Set α)) (hg : MonotoneOn g (D : Set α)) :
    (D.image (fun x => (f x, g x))).card ≤ 2 * B - 1 := by
  apply card_le_of_comparable
  intro a ha b hb
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
  rcases le_total x y with hxy | hyx
  · exact Or.inl ⟨hf hx hy hxy, hg hx hy hxy⟩
  · exact Or.inr ⟨hf hy hx hyx, hg hy hx hyx⟩

/-- Monotone and antitone bucket coordinates attain at most `2B - 1`
pairs on any finite selected domain, including domains with arbitrary gaps. -/
theorem card_image_antitone {α : Type*} [LinearOrder α] {B : ℕ}
    (D : Finset α) (f g : α → Fin B)
    (hf : MonotoneOn f (D : Set α)) (hg : AntitoneOn g (D : Set α)) :
    (D.image (fun x => (f x, g x))).card ≤ 2 * B - 1 := by
  apply card_le_of_oppositely_comparable
  intro a ha b hb
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
  rcases le_total x y with hxy | hyx
  · exact Or.inl ⟨hf hx hy hxy, hg hx hy hxy⟩
  · exact Or.inr ⟨hf hy hx hyx, hg hy hx hyx⟩

end LeanMachine.BucketChains
