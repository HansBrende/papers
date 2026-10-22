import TransposeFollowup.RationalPackedFamily
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Encodable.Pi

/-! Common denominators and exact separation for arbitrary rational
generator families, including words before or after free reduction. -/
namespace TransposeFollowup.RationalFreePair
open Classical
set_option autoImplicit false

theorem hasDenominator_identity (D : ℕ) : HasDenominator D (1 : Group) := by
  intro i j
  refine ⟨(D : ℤ) * (1 : Matrix (Fin 2) (Fin 2) ℤ) i j, ?_⟩
  fin_cases i <;> fin_cases j <;> norm_num

def signedGenerator {ι : Type*} (g : ι → Group) (letter : ι × Bool) : Group :=
  cond letter.2 (g letter.1) (g letter.1)⁻¹

theorem signedGenerator_hasDenominator {ι : Type*} (g : ι → Group) {D : ℕ}
    (hg : ∀ i, HasDenominator D (g i)) (letter : ι × Bool) :
    HasDenominator D (signedGenerator g letter) := by
  rcases letter with ⟨i, b⟩
  cases b
  · exact (hg i).inv
  · exact hg i

theorem generator_word_eq_lift {ι : Type*} (g : ι → Group) (w : List (ι × Bool)) :
    (w.map (signedGenerator g)).prod = FreeGroup.lift g (FreeGroup.mk w) := rfl

theorem generator_word_hasDenominator {ι : Type*} (g : ι → Group) {D : ℕ}
    (hg : ∀ i, HasDenominator D (g i)) (w : List (ι × Bool)) :
    HasDenominator (D ^ w.length) (FreeGroup.lift g (FreeGroup.mk w)) := by
  rw [← generator_word_eq_lift]
  simpa only [List.length_map] using list_product_hasDenominator D
    (w.map (signedGenerator g)) (by
      intro a ha
      obtain ⟨letter, _, rfl⟩ := List.mem_map.mp ha
      exact signedGenerator_hasDenominator g hg letter)

theorem HasDenominator.real_separated {D : ℕ} {g h : Group}
    (hg : HasDenominator D g) (hD : 0 < D) (hh : HasDenominator D h) (hne : g ≠ h) :
    ∃ i j : Fin 2, 1 / (D : ℝ) ≤ |realEmbedding g i j - realEmbedding h i j| := by
  obtain ⟨i, j, he⟩ := hg.separated hD hh hne
  refine ⟨i, j, ?_⟩
  simp only [realEmbedding_entry]
  have hc := (Rat.cast_le (K := ℝ)).mpr he
  push_cast at hc
  exact hc

theorem free_generator_words_separated {ι : Type*} (g : ι → Group)
    (hfree : Function.Injective (FreeGroup.lift g)) {D : ℕ} (hD : 0 < D)
    (hg : ∀ i, HasDenominator D (g i)) (u v : List (ι × Bool))
    (hlen : u.length = v.length) (hne : FreeGroup.mk u ≠ FreeGroup.mk v) :
    ∃ i j : Fin 2, 1 / ((D : ℝ) ^ u.length) ≤
      |realEmbedding (FreeGroup.lift g (FreeGroup.mk u)) i j -
        realEmbedding (FreeGroup.lift g (FreeGroup.mk v)) i j| := by
  have hv := generator_word_hasDenominator g hg v
  rw [← hlen] at hv
  simpa only [Nat.cast_pow] using (generator_word_hasDenominator g hg u).real_separated
    (pow_pos hD _) hv (hfree.ne hne)

def denominatorCarrier (D : ℕ) : Set RealMobius.Group :=
  {x | ∃ g : Group, HasDenominator D g ∧ realEmbedding g = x}

theorem denominatorCarrier_countable (D : ℕ) : (denominatorCarrier D).Countable := by
  let : Countable (Matrix (Fin 2) (Fin 2) ℚ) :=
    inferInstanceAs (Countable (Fin 2 → Fin 2 → ℚ))
  let : Countable Group := inferInstanceAs
    (Countable {g : Matrix (Fin 2) (Fin 2) ℚ // g.det = 1})
  have hs : denominatorCarrier D ⊆ Set.range realEmbedding := by
    rintro x ⟨g, _, hg⟩
    exact ⟨g, hg⟩
  exact (Set.countable_range realEmbedding).mono hs

theorem denominatorCarrier_measurableSet [MeasurableSpace RealMobius.Group]
    [BorelSpace RealMobius.Group] (D : ℕ) : MeasurableSet (denominatorCarrier D) :=
  (denominatorCarrier_countable D).measurableSet

theorem denominatorCarrier_one (D : ℕ) : (1 : RealMobius.Group) ∈ denominatorCarrier D :=
  ⟨1, hasDenominator_identity D, map_one realEmbedding⟩

theorem denominatorCarrier_inv {D : ℕ} {x : RealMobius.Group}
    (hx : x ∈ denominatorCarrier D) : x⁻¹ ∈ denominatorCarrier D := by
  obtain ⟨g, hg, rfl⟩ := hx
  exact ⟨g⁻¹, hg.inv, map_inv realEmbedding g⟩

theorem denominatorCarrier_mul {D E : ℕ} {x y : RealMobius.Group}
    (hx : x ∈ denominatorCarrier D) (hy : y ∈ denominatorCarrier E) :
    x * y ∈ denominatorCarrier (D * E) := by
  obtain ⟨g, hg, rfl⟩ := hx
  obtain ⟨h, hh, rfl⟩ := hy
  exact ⟨g * h, hg.mul hh, map_mul realEmbedding g h⟩

theorem denominatorCarrier_separated {D : ℕ} (hD : 0 < D) {x y : RealMobius.Group}
    (hx : x ∈ denominatorCarrier D) (hy : y ∈ denominatorCarrier D) (hne : x ≠ y) :
    ∃ i j : Fin 2, 1 / (D : ℝ) ≤ |x i j - y i j| := by
  obtain ⟨g, hg, rfl⟩ := hx
  obtain ⟨h, hh, rfl⟩ := hy
  exact hg.real_separated hD hh (fun he => hne (congrArg realEmbedding he))

end TransposeFollowup.RationalFreePair
