import Mathlib.Data.Finset.Interval
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-! Finite aligned bins and the elementary interval estimates used by the
mixed-radix compiler obstruction. All coordinates are ordinary raw positions. -/
namespace BitWord
namespace Geometry

/-- The aligned bins touched by a finite set of raw positions. -/
def bins (B : ℕ) (S : Finset ℕ) : Finset ℕ := S.image (fun x => x / B)

@[simp] theorem mem_bins {B j : ℕ} {S : Finset ℕ} :
    j ∈ bins B S ↔ ∃ x ∈ S, x / B = j := Finset.mem_image

theorem bins_mono {B : ℕ} {S T : Finset ℕ} (h : S ⊆ T) :
    bins B S ⊆ bins B T := Finset.image_mono _ h

@[simp] theorem bins_union (B : ℕ) (S T : Finset ℕ) :
    bins B (S ∪ T) = bins B S ∪ bins B T := Finset.image_union S T

/-- Points within one bin width of a fixed aligned bin touch at most three bins. -/
theorem bins_card_le_three {B j : ℕ} (hB : 0 < B) (S : Finset ℕ)
    (hS : ∀ x ∈ S, j * B < x + B ∧ x < (j + 2) * B) :
    (bins B S).card ≤ 3 := by
  have hs : bins B S ⊆ Finset.Icc (j - 1) (j + 1) := by
    intro k hk
    obtain ⟨x, hx, rfl⟩ := mem_bins.mp hk
    obtain ⟨hlo, hhi⟩ := hS x hx
    rw [Finset.mem_Icc]
    constructor
    · have hdiv : j ≤ (x + B) / B :=
        (Nat.le_div_iff_mul_le hB).2 (Nat.le_of_lt hlo)
      rw [Nat.add_div_right x hB] at hdiv
      exact Nat.sub_le_of_le_add hdiv
    · have := (Nat.div_lt_iff_lt_mul hB).2 hhi
      omega
  exact (Finset.card_le_card hs).trans (by simp; omega)

/-- A finite union of pieces, each touching at most `c` bins. -/
theorem bins_biUnion_card_le {ι : Type*} [DecidableEq ι] (B c : ℕ)
    (I : Finset ι) (S : ι → Finset ℕ)
    (h : ∀ i ∈ I, (bins B (S i)).card ≤ c) :
    (bins B (I.biUnion S)).card ≤ I.card * c := by
  classical
  rw [bins, Finset.biUnion_image]
  exact (Finset.card_biUnion_le).trans <| (Finset.sum_le_sum h).trans_eq (by simp)

/-- Two disjoint intervals meeting the same bin can be classified by which
side of the bin's left boundary their starts lie. For intervals at least as
long as the bin this classification is injective. -/
theorem large_meeting_card_le_two {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (start len : ι → ℕ) {B j : ℕ} (_hB : 0 < B)
    (hdis : ∀ i ∈ I, ∀ k ∈ I, i ≠ k →
      start i + len i ≤ start k ∨ start k + len k ≤ start i)
    (hlen : ∀ i ∈ I, B ≤ len i)
    (hmeet : ∀ i ∈ I, ∃ x, j * B ≤ x ∧ x < (j + 1) * B ∧
      start i ≤ x ∧ x < start i + len i) : I.card ≤ 2 := by
  classical
  let f : ι → Bool := fun i => decide (start i ≤ j * B)
  have hi : Set.InjOn f I := by
    intro i hi k hk he
    by_contra hne
    have hd := hdis i hi k hk hne
    obtain ⟨x, hxl, hxu, hix, hxe⟩ := hmeet i hi
    obtain ⟨y, hyl, hyu, hky, hye⟩ := hmeet k hk
    have hli := hlen i hi
    have hlk := hlen k hk
    have hc : (start i ≤ j * B) ↔ (start k ≤ j * B) := by
      simpa [f] using he
    rcases hd with hd | hd <;>
      by_cases hside : start i ≤ j * B <;> simp_all <;> nlinarith [hlen i hi, hlen k hk]
  simpa using (Finset.card_le_card_of_injOn f (by simp [Set.MapsTo]) hi :
    I.card ≤ (Finset.univ : Finset Bool).card)

end Geometry
end BitWord

namespace BitWord.Geometry

 theorem bins_card_le_of_diameter_mul {B c : ℕ} (hB : 0 < B)
     (S : Finset ℕ) (hS : ∀ x ∈ S, ∀ y ∈ S, x < y + c * B) :
     (bins B S).card ≤ c + 1 := by
   classical
   by_cases hn : S.Nonempty
   · let a := S.min' hn
     have hs : bins B S ⊆ Finset.Icc (a / B) (a / B + c) := by
       intro j hj
       obtain ⟨x, hx, rfl⟩ := mem_bins.mp hj
       have ha : a ≤ x := S.min'_le x hx
       have hxa := hS x hx a (S.min'_mem hn)
       have hm := Nat.mod_lt a hB
       have hd := Nat.div_add_mod a B
       have hh : x < (a / B + c + 1) * B := by nlinarith
       have hq := (Nat.div_lt_iff_lt_mul hB).2 hh
       exact Finset.mem_Icc.mpr ⟨Nat.div_le_div_right ha, by omega⟩
     exact (Finset.card_le_card hs).trans (by simp; omega)
   · simp_all [Finset.not_nonempty_iff_eq_empty, bins]


/-- A diameter version, convenient for translated and reflected pieces. -/
theorem bins_card_le_two_of_diameter {B : ℕ} (hB : 0 < B) (S : Finset ℕ)
    (hS : ∀ x ∈ S, ∀ y ∈ S, x < y + B) : (bins B S).card ≤ 2 := by
  simpa only [one_mul] using bins_card_le_of_diameter_mul (c := 1) hB S
    (by simpa only [one_mul] using hS)

/-- A rigid translation of a subset of a bin meets at most two bins. -/
theorem bins_translate_card_le_two {B j : ℕ} (hB : 0 < B)
    (S : Finset ℕ) (f : ℕ → ℕ) (a c : ℕ)
    (hS : ∀ x ∈ S, j * B ≤ x ∧ x < (j + 1) * B)
    (hf : ∀ x ∈ S, f x + a = x + c) :
    (bins B (S.image f)).card ≤ 2 := by
  apply bins_card_le_two_of_diameter hB
  intro x hx y hy
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
  have hu' := hS u hu
  have hv' := hS v hv
  have hfu := hf u hu
  have hfv := hf v hv
  nlinarith

/-- A rigid reflection obeys the same two-bin estimate. -/
theorem bins_reflect_card_le_two {B j : ℕ} (hB : 0 < B)
    (S : Finset ℕ) (f : ℕ → ℕ) (c : ℕ)
    (hS : ∀ x ∈ S, j * B ≤ x ∧ x < (j + 1) * B)
    (hf : ∀ x ∈ S, f x + x = c) :
    (bins B (S.image f)).card ≤ 2 := by
  apply bins_card_le_two_of_diameter hB
  intro x hx y hy
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
  have hu' := hS u hu
  have hv' := hS v hv
  have hfu := hf u hu
  have hfv := hf v hv
  nlinarith

end BitWord.Geometry
