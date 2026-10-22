import TransposeFollowup.ShortWordCounting
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! A quadratic exceptional-set bound: a large set of bounded words
forces a nontrivial iterated commutator with one shared first argument. -/
namespace TransposeFollowup.FreeWordFamily
open Classical
open scoped commutatorElement
set_option autoImplicit false

variable {α : Type*} [DecidableEq α]

theorem commutator_norm_le (a x : FreeGroup α) :
    FreeGroup.norm ⁅a, x⁆ ≤ 2 * (FreeGroup.norm a + FreeGroup.norm x) := by
  have h₁ := FreeGroup.norm_mul_le a x
  have h₂ := FreeGroup.norm_mul_le (a * x) a⁻¹
  have h₃ := FreeGroup.norm_mul_le (a * x * a⁻¹) x⁻¹
  simp only [FreeGroup.norm_inv_eq] at h₂ h₃
  change FreeGroup.norm (a * x * a⁻¹ * x⁻¹) ≤ _
  omega

theorem commutator_fiber_card_le (F : Finset (FreeGroup α)) (L : ℕ)
    (hL : ∀ x ∈ F, FreeGroup.norm x ≤ L) {a : FreeGroup α} (ha : a ≠ 1)
    (b : FreeGroup α) : (F.filter (fun x => ⁅a, x⁆ = b)).card ≤ 4 * L + 1 := by
  let E := F.filter (fun x => ⁅a, x⁆ = b)
  by_cases hn : E.Nonempty
  · obtain ⟨y, hy⟩ := hn
    let f := fun x : FreeGroup α => y⁻¹ * x
    have hf : Function.Injective f := by intro x z h; exact mul_left_cancel h
    have hlen : ∀ z ∈ E.image f, FreeGroup.norm z ≤ 2 * L := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      have hh := FreeGroup.norm_mul_le y⁻¹ x
      rw [FreeGroup.norm_inv_eq] at hh
      have hyL := hL y (Finset.mem_filter.mp hy).1
      have hxL := hL x (Finset.mem_filter.mp hx).1
      dsimp only [f]
      omega
    have hcentral : ∀ z ∈ E.image f, z * a = a * z := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      have he : ⁅a, x⁆ = ⁅a, y⁆ :=
        (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
      have he' := congrArg (fun v => y⁻¹ * a⁻¹ * v * x) he
      have hi : Commute (f x) a⁻¹ := by
        change (y⁻¹ * x) * a⁻¹ = a⁻¹ * (y⁻¹ * x)
        simp only [commutatorElement_def] at he'
        convert he' using 1 <;> group
      exact (Commute.inv_right_iff.mp hi).eq
    have h := centralizer_short_words_card_le (E.image f) (2 * L) hlen ha hcentral
    rw [Finset.card_image_of_injective E hf] at h
    simpa only [show 2 * (2 * L) + 1 = 4 * L + 1 by omega] using h
  · have he : E = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    change E.card ≤ _
    simp [he]

theorem vanishing_bicommutator_card_le (F : Finset (FreeGroup α)) (L : ℕ)
    (hL : ∀ x ∈ F, FreeGroup.norm x ≤ L) {a : FreeGroup α} (ha : a ≠ 1)
    (haL : FreeGroup.norm a ≤ L)
    (hvanish : ∀ x ∈ F, ∀ y ∈ F, ⁅⁅a, x⁆, ⁅a, y⁆⁆ = 1) :
    F.card ≤ (8 * L + 1) * (4 * L + 1) := by
  let f := fun x : FreeGroup α => ⁅a, x⁆
  have hlen : ∀ z ∈ F.image f, FreeGroup.norm z ≤ 4 * L := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    have h := commutator_norm_le a x
    have hxL := hL x hx
    dsimp only [f]
    omega
  have hcomm : ∀ x ∈ F.image f, ∀ y ∈ F.image f, x * y = y * x := by
    intro x hx y hy
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
    exact commutatorElement_eq_one_iff_mul_comm.mp (hvanish v hv w hw)
  have hc := commuting_short_words_card_le (F.image f) (4 * L) hlen hcomm
  have hf := Finset.card_le_mul_card_image (f := f) F (4 * L + 1)
    (fun b _ => commutator_fiber_card_le F L hL ha b)
  calc
    F.card ≤ (4 * L + 1) * (F.image f).card := hf
    _ ≤ (4 * L + 1) * (2 * (4 * L) + 1) := Nat.mul_le_mul_left _ hc
    _ = _ := by ring

theorem exists_nontrivial_bicommutator (F : Finset (FreeGroup α)) (L : ℕ)
    (hL : ∀ x ∈ F, FreeGroup.norm x ≤ L)
    (hcard : (8 * L + 1) * (4 * L + 1) < F.card) :
    ∃ a ∈ F, ∃ x ∈ F, ∃ y ∈ F, ⁅⁅a, x⁆, ⁅a, y⁆⁆ ≠ 1 ∧
      FreeGroup.norm ⁅⁅a, x⁆, ⁅a, y⁆⁆ ≤ 16 * L := by
  have hn : ∃ a ∈ F, a ≠ 1 := by
    by_contra hn
    have hsub : F ⊆ {1} := by
      intro x hx
      have he : x = 1 := by by_contra h; exact hn ⟨x, hx, h⟩
      simp only [Finset.mem_singleton, he]
    have hh := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at hh
    have : 1 ≤ (8 * L + 1) * (4 * L + 1) := by nlinarith
    omega
  obtain ⟨a, ha, hane⟩ := hn
  have hex : ∃ x ∈ F, ∃ y ∈ F, ⁅⁅a, x⁆, ⁅a, y⁆⁆ ≠ 1 := by
    by_contra hv
    push Not at hv
    exact (not_le_of_gt hcard) (vanishing_bicommutator_card_le F L hL hane (hL a ha) hv)
  obtain ⟨x, hx, y, hy, hne⟩ := hex
  refine ⟨a, ha, x, hx, y, hy, hne, ?_⟩
  have hax := commutator_norm_le a x
  have hay := commutator_norm_le a y
  have hlast := commutator_norm_le ⁅a, x⁆ ⁅a, y⁆
  have h₁ := hL a ha
  have h₂ := hL x hx
  have h₃ := hL y hy
  omega

end TransposeFollowup.FreeWordFamily
