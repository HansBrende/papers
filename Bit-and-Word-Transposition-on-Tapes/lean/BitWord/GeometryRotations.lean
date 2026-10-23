import BitWord.GeometryEntries

namespace BitWord.Geometry

/-- A cyclic rotation of one interval cuts a source-bin intersection into at
most two rigidly translated pieces. -/
theorem rotate_image_bins_le_four {B j a n r : ℕ} (hB : 0 < B)
    (_hn : 0 < n) (hr : r < n) (S : Finset ℕ) (f : ℕ → ℕ)
    (hS : ∀ x ∈ S, j * B ≤ x ∧ x < (j + 1) * B)
    (ha : ∀ x ∈ S, a ≤ x ∧ x < a + n)
    (hf : ∀ x ∈ S, f x = a + ((x - a + r) % n)) :
    (bins B (S.image f)).card ≤ 4 := by
  classical
  let S₀ := S.filter (fun x => x - a + r < n)
  let S₁ := S.filter (fun x => ¬ x - a + r < n)
  have he : S.image f = S₀.image f ∪ S₁.image f := by
    rw [← Finset.image_union, Finset.filter_union_filter_not_eq]
  have h₀ : (bins B (S₀.image f)).card ≤ 2 := by
    apply bins_translate_card_le_two hB S₀ f 0 r
    · intro x hx
      exact hS x (Finset.mem_filter.mp hx).1
    · intro x hx
      obtain ⟨hx, hl⟩ := Finset.mem_filter.mp hx
      rw [hf x hx, Nat.mod_eq_of_lt hl]
      have := Nat.sub_add_cancel (ha x hx).1
      omega
  have h₁ : (bins B (S₁.image f)).card ≤ 2 := by
    apply bins_translate_card_le_two hB S₁ f n r
    · intro x hx
      exact hS x (Finset.mem_filter.mp hx).1
    · intro x hx
      obtain ⟨hx, hl⟩ := Finset.mem_filter.mp hx
      have hax := ha x hx
      have hs := Nat.sub_add_cancel hax.1
      have hlt : x - a + r < 2 * n := by omega
      have hm : (x - a + r) % n = x - a + r - n := by
        apply Nat.mod_eq_sub_mod (Nat.le_of_not_gt hl) |>.trans
        exact Nat.mod_eq_of_lt (by omega)
      rw [hf x hx, hm]
      omega
  rw [he, bins_union]
  exact (Finset.card_union_le _ _).trans (by omega)

/-- Reversal has just one rigidly reflected piece. -/
theorem reverse_image_bins_le_two {B j a n : ℕ} (hB : 0 < B)
    (S : Finset ℕ) (f : ℕ → ℕ)
    (hS : ∀ x ∈ S, j * B ≤ x ∧ x < (j + 1) * B)
    (ha : ∀ x ∈ S, a ≤ x ∧ x < a + n)
    (hf : ∀ x ∈ S, f x = a + (n - 1 - (x - a))) :
    (bins B (S.image f)).card ≤ 2 := by
  apply bins_reflect_card_le_two hB S f (a + a + n - 1) hS
  intro x hx
  rw [hf x hx]
  have hax := ha x hx
  have hs := Nat.sub_add_cancel hax.1
  omega

end BitWord.Geometry
