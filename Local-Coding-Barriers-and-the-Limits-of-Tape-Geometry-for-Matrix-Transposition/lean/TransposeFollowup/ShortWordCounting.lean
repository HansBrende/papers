import TransposeFollowup.FreeWordPowerNorm
import TransposeFollowup.FreeGroupCentralizer
import Mathlib.Data.Int.Interval

/-! Sharp finite counts for short words in cyclic subgroups and in the
centralizer of a nontrivial word. -/
namespace TransposeFollowup.FreeWordFamily
open Classical
set_option autoImplicit false

variable {α : Type*} [DecidableEq α]

theorem cyclic_short_words_card_le (F : Finset (FreeGroup α)) (L : ℕ)
    (hL : ∀ x ∈ F, FreeGroup.norm x ≤ L) (g : FreeGroup α)
    (hg : ∀ x ∈ F, ∃ n : ℤ, g ^ n = x) : F.card ≤ 2 * L + 1 := by
  by_cases hg1 : g = 1
  · have hF : F ⊆ {1} := by
      intro x hx
      obtain ⟨n, rfl⟩ := hg x hx
      simp [hg1]
    have := Finset.card_le_card hF
    simp only [Finset.card_singleton] at this
    omega
  · have hF : F ⊆ (Finset.Icc (-(L : ℤ)) (L : ℤ)).image (fun n => g ^ n) := by
      intro x hx
      obtain ⟨n, hn⟩ := hg x hx
      have habs : n.natAbs ≤ L := (exponent_le_norm_zpow hg1 n).trans (hn.symm ▸ hL x hx)
      refine Finset.mem_image.mpr ⟨n, ?_, hn⟩
      rw [Finset.mem_Icc]
      have hpos := Int.le_natAbs (a := n)
      have hneg := Int.le_natAbs (a := -n)
      rw [Int.natAbs_neg] at hneg
      omega
    calc
      F.card ≤ ((Finset.Icc (-(L : ℤ)) (L : ℤ)).image (fun n => g ^ n)).card := Finset.card_le_card hF
      _ ≤ (Finset.Icc (-(L : ℤ)) (L : ℤ)).card := Finset.card_image_le
      _ = 2 * L + 1 := by rw [Int.card_Icc]; omega

theorem centralizer_short_words_card_le (F : Finset (FreeGroup α)) (L : ℕ)
    (hL : ∀ x ∈ F, FreeGroup.norm x ≤ L) {a : FreeGroup α} (ha : a ≠ 1)
    (hcomm : ∀ x ∈ F, x * a = a * x) : F.card ≤ 2 * L + 1 := by
  let H := Subgroup.centralizer ({a} : Set (FreeGroup α))
  have hcyc : IsCyclic H := centralizer_isCyclic ha
  obtain ⟨g, hg⟩ := H.isCyclic_iff_exists_zpowers_eq_top.mp hcyc
  apply cyclic_short_words_card_le F L hL g
  intro x hx
  apply Subgroup.mem_zpowers_iff.mp
  rw [hg]
  exact Subgroup.mem_centralizer_singleton_iff.mpr (hcomm x hx)

theorem commuting_short_words_card_le (F : Finset (FreeGroup α)) (L : ℕ)
    (hL : ∀ x ∈ F, FreeGroup.norm x ≤ L)
    (hcomm : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x) : F.card ≤ 2 * L + 1 := by
  by_cases hn : ∃ a ∈ F, a ≠ 1
  · obtain ⟨a, ha, hane⟩ := hn
    exact centralizer_short_words_card_le F L hL hane (fun x hx => hcomm x hx a ha)
  · have hF : F ⊆ {1} := by
      intro x hx
      have he : x = 1 := by by_contra h; exact hn ⟨x, hx, h⟩
      simp only [Finset.mem_singleton, he]
    have := Finset.card_le_card hF
    simp only [Finset.card_singleton] at this
    omega

end TransposeFollowup.FreeWordFamily
