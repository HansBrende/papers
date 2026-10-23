import BitWord.CompilerDirty

namespace BitWord.Compiler
open Geometry
open scoped BigOperators
open Classical

/-- Transpose-like dispersion: distinct source positions in one aligned bin
have target images in distinct bins. -/
def Disperses (P B : ℕ) (target : ℕ → ℕ) : Prop :=
  ∀ x < P, ∀ y < P, x / B = y / B → target x / B = target y / B → x = y

noncomputable def agreement {P : ℕ} (ts : Path P) (target : ℕ → ℕ) : Finset ℕ :=
  (Finset.range P).filter (fun x => forward ts x = target x)

/-- Clean exact coincidences in one source bin are bounded by the clean path's
bin fanout. No probabilistic or payload independence hypothesis is used. -/
theorem clean_agreement_bin_card_le {P B j : ℕ} (ts : Path P)
    (hB : 0 < B) (target : ℕ → ℕ) (hd : Disperses P B target) :
    ((agreement ts target).filter (fun x => Clean B ts x ∧ x / B = j)).card ≤
      11 ^ ts.length := by
  let S := (agreement ts target).filter (fun x => Clean B ts x ∧ x / B = j)
  have hP : ∀ x ∈ S, x < P := by
    intro x hx
    exact Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1
  have hclean : ∀ x ∈ S, Clean B ts x := fun x hx => (Finset.mem_filter.mp hx).2.1
  have hbin : (bins B S).card ≤ 1 := by
    apply (Finset.card_le_card (t := {j}) ?_).trans
    · simp
    · intro k hk
      obtain ⟨x, hx, rfl⟩ := mem_bins.mp hk
      exact Finset.mem_singleton.mpr (Finset.mem_filter.mp hx).2.2
  have hinj : Set.InjOn (fun x => forward ts x / B) S := by
    intro x hx y hy he
    have hxe := (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2
    have hye := (Finset.mem_filter.mp (Finset.mem_filter.mp hy).1).2
    apply hd x (hP x hx) y (hP y hy)
    · exact (Finset.mem_filter.mp hx).2.2.trans (Finset.mem_filter.mp hy).2.2.symm
    · simpa only [hxe, hye] using he
  have hcard : S.card = (bins B (S.image (forward ts))).card := by
    simp only [bins, Finset.image_image, Function.comp_def]
    exact (Finset.card_image_of_injOn hinj).symm
  change S.card ≤ _
  rw [hcard]
  exact (clean_forward_bins_le ts hB S hP hclean).trans ((Nat.mul_le_mul_right _ hbin).trans_eq (Nat.one_mul _))

/-- At a given scale, all possible exact path coincidences are paid by dirty
positions or by the clean per-bin dispersion budget. -/
theorem agreement_card_le {P B : ℕ} (ts : Path P) (hB : 0 < B) (hdiv : B ∣ P)
    (target : ℕ → ℕ) (hd : Disperses P B target) :
    (agreement ts target).card ≤ (dirty B ts).card + (P / B) * 11 ^ ts.length := by
  let C := (agreement ts target).filter (fun x => Clean B ts x)
  let piece := fun j => (agreement ts target).filter (fun x => Clean B ts x ∧ x / B = j)
  have hC : C = (Finset.range (P / B)).biUnion piece := by
    ext x
    simp only [C, piece, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_range]
    constructor
    · rintro ⟨hx, hc⟩
      have hxp := Finset.mem_range.mp (Finset.mem_filter.mp hx).1
      exact ⟨x / B, (Nat.div_lt_iff_lt_mul hB).2 (by simpa [Nat.div_mul_cancel hdiv] using hxp), hx, hc, rfl⟩
    · rintro ⟨j, hj, hx, hc, he⟩
      exact ⟨hx, hc⟩
  have hCc : C.card ≤ (P / B) * 11 ^ ts.length := by
    rw [hC]
    apply Finset.card_biUnion_le.trans
    calc
      (∑ j ∈ Finset.range (P / B), (piece j).card) ≤ ∑ _j ∈ Finset.range (P / B), 11 ^ ts.length :=
        Finset.sum_le_sum (fun j hj => clean_agreement_bin_card_le ts hB target hd)
      _ = _ := by simp
  have hsub : agreement ts target ⊆ dirty B ts ∪ C := by
    intro x hx
    by_cases hc : Clean B ts x
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx, hc⟩)
    · exact Finset.mem_union_left _ (mem_dirty.mpr
        ⟨Finset.mem_range.mp (Finset.mem_filter.mp hx).1, hc⟩)
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (Nat.add_le_add_left hCc _))

end BitWord.Compiler
