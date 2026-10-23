import BitWord.GeometryIntervals

namespace BitWord.Geometry

/-- A whole-entry map preserves the within-entry offset. No bound or
regularity is imposed on the public destination function. -/
def entryMap (k : ℕ) (dest : ℕ → ℕ) (x : ℕ) : ℕ :=
  k * dest (x / k) + x % k

/-- A subset of one B-bin meets at most two k-entries when B≤k. The
entry block's start need not align with either bin system. -/
theorem entry_indices_card_le_two {B j a k : ℕ} (hB : 0 < B) (hk : B ≤ k)
    (S : Finset ℕ) (hS : ∀ x ∈ S, j * B ≤ x ∧ x < (j + 1) * B)
    (ha : ∀ x ∈ S, a ≤ x) :
    ((S.image (fun x => (x - a) / k))).card ≤ 2 := by
  have he : S.image (fun x => (x - a) / k) = bins k (S.image (fun x => x - a)) := by
    simp [bins, Finset.image_image, Function.comp_def]
  rw [he]
  apply bins_card_le_two_of_diameter (lt_of_lt_of_le hB hk)
  intro x hx y hy
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
  have hu' := hS u hu
  have hv' := hS v hv
  have hau := ha u hu
  have hav := ha v hv
  have hsubu := Nat.sub_add_cancel hau
  have hsubv := Nat.sub_add_cancel hav
  nlinarith

/-- An arbitrary whole-entry permutation has at most four image bins on a
source B-bin when its entry width is at least B. This proof even grants
nonbijective destination functions. -/
theorem entry_image_bins_le_four {B j a k : ℕ} (hB : 0 < B) (hk : B ≤ k)
    (S : Finset ℕ) (f dest : ℕ → ℕ)
    (hS : ∀ x ∈ S, j * B ≤ x ∧ x < (j + 1) * B)
    (ha : ∀ x ∈ S, a ≤ x)
    (hf : ∀ x ∈ S, f x = a + entryMap k dest (x - a)) :
    (bins B (S.image f)).card ≤ 4 := by
  classical
  let E := S.image (fun x => (x - a) / k)
  let piece := fun e => S.filter (fun x => (x - a) / k = e)
  have hE : E.card ≤ 2 := entry_indices_card_le_two hB hk S hS ha
  have hp : ∀ e ∈ E, (bins B ((piece e).image f)).card ≤ 2 := by
    intro e he
    apply bins_translate_card_le_two hB (piece e) f (k * e) (k * dest e)
    · intro x hx
      exact hS x (Finset.mem_filter.mp hx).1
    · intro x hx
      obtain ⟨hx, hxe⟩ := Finset.mem_filter.mp hx
      rw [hf x hx]
      unfold entryMap
      rw [hxe]
      have hd := Nat.div_add_mod (x - a) k
      have hxa := Nat.sub_add_cancel (ha x hx)
      rw [hxe] at hd
      omega
  have hu : S.image f = E.biUnion (fun e => (piece e).image f) := by
    rw [← Finset.biUnion_image]
    exact congrArg (fun T : Finset ℕ => T.image f)
      (Finset.image_biUnion_filter_eq S (fun x => (x - a) / k)).symm
  rw [hu]
  exact (bins_biUnion_card_le B 2 E _ hp).trans (by omega)

end BitWord.Geometry
