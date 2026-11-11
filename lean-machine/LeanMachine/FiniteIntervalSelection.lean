import LeanMachine.FiniteWeightedPigeonhole
import LeanMachine.FiniteTimeGrid

/-! A literal witness time and unordered coordinate set select one common
preceding grid interval and one heavy event. No heavy-cell certificate is
assumed, and the menu is the exact unordered-set count times the grid count.
-/

namespace LeanMachine.FiniteIntervalSelection

open Finset FiniteTimeGrid

theorem exists_fixed_interval {Ω : Type*} [Fintype Ω]
    (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (B : Finset Ω)
    (hp : 0 < ContextPruning.mass w B) (k m T ell : ℕ)
    (good : Ω → Fin k → ℕ → Prop)
    (hchoice : ∀ x ∈ B, ∃ t ≤ T, ∃ H : Finset (Fin k), H.card = m ∧
      ∀ h ∈ H, ∀ u ∈ interval ell (previousIndex ell t), good x h u) :
    ∃ H : Finset (Fin k), H.card = m ∧ ∃ j < T / ell + 1,
      ∃ E ⊆ B, ContextPruning.mass w B / (k.choose m * (T / ell + 1) : ℕ) ≤
        ContextPruning.mass w E ∧
        ∀ x ∈ E, ∀ h ∈ H, ∀ u ∈ interval ell j, good x h u := by
  classical
  let witness (x : Ω) (hx : x ∈ B) := (hchoice x hx).choose
  have htime (x : Ω) (hx : x ∈ B) : witness x hx ≤ T := (hchoice x hx).choose_spec.1
  let heads (x : Ω) (hx : x ∈ B) := (hchoice x hx).choose_spec.2.choose
  have hcard (x : Ω) (hx : x ∈ B) : (heads x hx).card = m :=
    (hchoice x hx).choose_spec.2.choose_spec.1
  have hgood (x : Ω) (hx : x ∈ B) :
      ∀ h ∈ heads x hx, ∀ u ∈ interval ell (previousIndex ell (witness x hx)), good x h u :=
    (hchoice x hx).choose_spec.2.choose_spec.2
  let label (x : Ω) : Finset (Fin k) × ℕ := if hx : x ∈ B then
    (heads x hx, previousIndex ell (witness x hx)) else (∅, 0)
  let menu := (univ : Finset (Fin k)).powersetCard m ×ˢ range (T / ell + 1)
  have hsub : B.image label ⊆ menu := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hz
    simp only [label, dite_eq_left hx, menu, mem_product]
    exact ⟨mem_powersetCard.mpr ⟨subset_univ _, hcard x hx⟩, previousIndex_mem (htime x hx)⟩
  have hmenu : menu.card = k.choose m * (T / ell + 1) := by
    simp only [menu, card_product, card_powersetCard, card_univ, Fintype.card_fin, card_range]
  have hcount : (B.image label).card ≤ k.choose m * (T / ell + 1) := by
    rw [← hmenu]
    exact card_le_card hsub
  have hB : B.Nonempty := by
    by_contra hn
    have he := not_nonempty_iff_eq_empty.mp hn
    simp [he, ContextPruning.mass] at hp
  have hpos : (0 : ℝ) < (k.choose m * (T / ell + 1) : ℕ) := by
    exact_mod_cast (hB.image label).card_pos.trans_le hcount
  obtain ⟨y, hy, hmass⟩ := FiniteWeightedPigeonhole.exists_heavy_cell w hw B label hp hpos
    (by exact_mod_cast hcount)
  have hym := mem_product.mp (hsub hy)
  refine ⟨y.1, (mem_powersetCard.mp hym.1).2, y.2, mem_range.mp hym.2,
    B.filter (fun x => label x = y), filter_subset _ _, hmass, ?_⟩
  intro x hx h hh u hu
  have hxB := (mem_filter.mp hx).1
  have he : (heads x hxB, previousIndex ell (witness x hxB)) = y := by
    simpa only [label, dite_eq_left hxB] using (mem_filter.mp hx).2
  have heH : heads x hxB = y.1 := congrArg Prod.fst he
  have hej : previousIndex ell (witness x hxB) = y.2 := congrArg Prod.snd he
  apply hgood x hxB h (by rw [heH]; exact hh) u
  simpa only [hej] using hu

end LeanMachine.FiniteIntervalSelection
