import BitWord.GeometryBins

namespace BitWord.Geometry

 theorem image_partition (S : Finset ℕ) (f : ℕ → ℕ) (p : ℕ → Prop)
     [DecidablePred p] :
     S.image f = (S.filter p).image f ∪ (S.filter (fun x => ¬ p x)).image f := by
   rw [← Finset.image_union, Finset.filter_union_filter_not_eq]

 def split (P x : ℕ) : ℕ := if x % 2 = 0 then x / 2 else P / 2 + x / 2
 def interleave (P x : ℕ) : ℕ := if x < P / 2 then 2 * x else 2 * (x - P / 2) + 1

 theorem split_image_bins_le {P B j : ℕ} (hB : 0 < B) (S : Finset ℕ)
     (hS : ∀ x ∈ S, j * B ≤ x ∧ x < (j + 1) * B) :
     (bins B (S.image (split P))).card ≤ 11 := by
   let S₀ := S.filter (fun x => x % 2 = 0)
   let S₁ := S.filter (fun x => ¬ x % 2 = 0)
   have hpiece : ∀ t : Bool, (bins B ((S.filter (fun x => decide (x % 2 = 0) = t)).image (split P))).card ≤ 2 := by
     intro t
     apply bins_card_le_two_of_diameter hB
     intro x hx y hy
     obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
     obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
     obtain ⟨hu, hut⟩ := Finset.mem_filter.mp hu
     obtain ⟨hv, hvt⟩ := Finset.mem_filter.mp hv
     have hsu := hS u hu
     have hsv := hS v hv
     have hdiff : u < v + B := by nlinarith
     have hdiv : u / 2 < v / 2 + B := by omega
     have he : (u % 2 = 0) ↔ (v % 2 = 0) := by
       have : decide (u % 2 = 0) = decide (v % 2 = 0) := hut.trans hvt.symm
       simpa using this
     unfold split
     by_cases hh : u % 2 = 0
     · simp [hh, he.mp hh]; omega
     · have hvv : ¬ v % 2 = 0 := fun h => hh (he.mpr h)
       simp [hh, hvv]; omega
   have h₀ : (bins B (S₀.image (split P))).card ≤ 2 := by simpa [S₀] using hpiece true
   have h₁ : (bins B (S₁.image (split P))).card ≤ 2 := by simpa [S₁] using hpiece false
   rw [image_partition S (split P) (fun x => x % 2 = 0), bins_union]
   change (bins B (S₀.image (split P)) ∪ bins B (S₁.image (split P))).card ≤ 11
   have hu := Finset.card_union_le (bins B (S₀.image (split P))) (bins B (S₁.image (split P)))
   omega

 theorem interleave_image_bins_le {P B j : ℕ} (hB : 0 < B) (S : Finset ℕ)
     (hS : ∀ x ∈ S, j * B ≤ x ∧ x < (j + 1) * B) :
     (bins B (S.image (interleave P))).card ≤ 11 := by
   let S₀ := S.filter (fun x => x < P / 2)
   let S₁ := S.filter (fun x => ¬ x < P / 2)
   have hpiece : ∀ t : Bool, (bins B ((S.filter (fun x => decide (x < P / 2) = t)).image (interleave P))).card ≤ 3 := by
     intro t
     apply bins_card_le_of_diameter_mul (c := 2) hB
     intro x hx y hy
     obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
     obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
     obtain ⟨hu, hut⟩ := Finset.mem_filter.mp hu
     obtain ⟨hv, hvt⟩ := Finset.mem_filter.mp hv
     have hsu := hS u hu
     have hsv := hS v hv
     have hdiff : u < v + B := by nlinarith
     have he : (u < P / 2) ↔ (v < P / 2) := by
       have : decide (u < P / 2) = decide (v < P / 2) := hut.trans hvt.symm
       simpa using this
     unfold interleave
     by_cases hh : u < P / 2
     · simp [hh, he.mp hh]; omega
     · have hvv : ¬ v < P / 2 := fun h => hh (he.mpr h)
       simp only [hh, hvv, ↓reduceIte]
       omega
   have h₀ : (bins B (S₀.image (interleave P))).card ≤ 3 := by simpa [S₀] using hpiece true
   have h₁ : (bins B (S₁.image (interleave P))).card ≤ 3 := by simpa [S₁] using hpiece false
   rw [image_partition S (interleave P) (fun x => x < P / 2), bins_union]
   change (bins B (S₀.image (interleave P)) ∪ bins B (S₁.image (interleave P))).card ≤ 11
   have hu := Finset.card_union_le (bins B (S₀.image (interleave P))) (bins B (S₁.image (interleave P)))
   omega

end BitWord.Geometry
