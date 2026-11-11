import SharedDecoders.CompositionScalarExtension
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

/-! # The complete two-stage rank bound over every admissible field -/

namespace SharedDecoders

open Module

variable {F κ₁ κ₂ : Type*} [Field F] [Fintype κ₂]
  {d b k : ℕ} [NeZero d]

/-- Scalar extension supplies the actual primitive character, extends both
complete maps and their shared decoders, and does not increase the rank error. -/
theorem twoHop_rank_interval_any_field
    (hd : (d : F) ≠ 0)
    (p₁ : ZMod d → κ₁) (p₂ : ZMod d → κ₂)
    (K₁ K₂ : State d (Fin b → F) →ₗ[F] State d (Fin b → F))
    (hK₁ : ClassUniform p₁ K₁) (hK₂ : ClassUniform p₂ K₂)
    (hk : 0 < k) (N : ℕ) (hNd : N ≤ d)
    (hRamsey : ∀ C : ℕ → κ₁, ∃ a s : ℕ, 0 < s ∧
      ∀ j < (2 * Fintype.card κ₂ + 1) * k - 1,
        a + s * j < N ∧ C (a + s * j) = C a) :
    b * k * (d - N + 1) ≤ 2 * finrank F (LinearMap.range (swapLinear F - K₂.comp K₁)) := by
  let dn : ℕ+ := ⟨d, NeZero.pos d⟩
  let ψ := AddChar.primitiveZModChar dn F hd
  let E := CyclotomicField ψ.n F
  let χ : AddChar (ZMod d) E := ψ.char
  have hχ : Function.Injective χ := by
    intro a c hac
    have hz : χ (a - c) = 1 := by
      calc
        χ (a - c) = χ a * χ (-c) := by rw [sub_eq_add_neg, χ.map_add_eq_mul]
        _ = χ c * χ (-c) := by rw [hac]
        _ = 1 := by rw [← χ.map_add_eq_mul, add_neg_cancel, χ.map_zero_eq_one]
    exact sub_eq_zero.mp ((ψ.prim.zmod_char_eq_one_iff d (a - c)).mp hz)
  let K₁' := stateExtension E K₁
  let K₂' := stateExtension E K₂
  have h := twoHop_rank_interval χ hχ p₁ p₂ K₁' K₂'
    (stateExtension_classUniform p₁ K₁ hK₁)
    (stateExtension_classUniform p₂ K₂ hK₂) hk N hNd hRamsey
  have hr := stateExtension_rank_le (E := E) (swapLinear F - K₂.comp K₁)
  rw [stateExtension_sub, stateExtension_swap, stateExtension_comp] at hr
  exact h.trans (Nat.mul_le_mul_left 2 hr)

/-- A single finite Ramsey bound works uniformly for all coefficient fields,
positive widths, partitions and complete linear operators. -/
theorem exists_twoHop_rank_threshold [Finite κ₁] (hk : 0 < k) :
    ∃ N : ℕ, 0 < N ∧ ∀ (F : Type*) [Field F] (d b : ℕ) [NeZero d],
      (d : F) ≠ 0 → N ≤ d →
      ∀ (p₁ : ZMod d → κ₁) (p₂ : ZMod d → κ₂)
        (K₁ K₂ : State d (Fin b → F) →ₗ[F] State d (Fin b → F)),
      ClassUniform p₁ K₁ → ClassUniform p₂ K₂ →
      b * k * (d - N + 1) ≤
        2 * finrank F (LinearMap.range (swapLinear F (d := d) (A := Fin b → F) - K₂.comp K₁)) := by
  by_cases hκ : Nonempty κ₂
  · let := hκ
    have hM : 0 < Fintype.card κ₂ := Fintype.card_pos
    have hell : 0 < (2 * Fintype.card κ₂ + 1) * k - 1 := by
      have h : 2 ≤ (2 * Fintype.card κ₂ + 1) * k := by nlinarith
      omega
    obtain ⟨N, hN, hRamsey⟩ := exists_progression_bound κ₁ ((2 * Fintype.card κ₂ + 1) * k - 1) hell
    refine ⟨N, lt_of_lt_of_le hell hN, ?_⟩
    intro F _ d b _ hd hNd p₁ p₂ K₁ K₂ hK₁ hK₂
    exact twoHop_rank_interval_any_field hd p₁ p₂ K₁ K₂ hK₁ hK₂ hk N hNd hRamsey
  · refine ⟨1, by omega, ?_⟩
    intro F _ d b _ hd hNd p₁ p₂ K₁ K₂ hK₁ hK₂
    exact (hκ ⟨p₂ 0⟩).elim


/-- The rank deficit divided by `b*d` grows without bound, uniformly in every
field whose characteristic does not divide `d`. This does not assert a
positive fraction of the full `b*d*d` volume. -/
theorem twoHop_rank_superlinear [Finite κ₁] (t : ℕ) :
    ∃ D₀ : ℕ, ∀ (F : Type*) [Field F] (d b : ℕ) [NeZero d],
      (d : F) ≠ 0 → D₀ ≤ d →
      ∀ (p₁ : ZMod d → κ₁) (p₂ : ZMod d → κ₂)
        (K₁ K₂ : State d (Fin b → F) →ₗ[F] State d (Fin b → F)),
      ClassUniform p₁ K₁ → ClassUniform p₂ K₂ →
      t * (b * d) ≤ finrank F (LinearMap.range
        (swapLinear F (d := d) (A := Fin b → F) - K₂.comp K₁)) := by
  obtain ⟨N, hN, hbound⟩ := exists_twoHop_rank_threshold
    (κ₁ := κ₁) (κ₂ := κ₂) (k := 4 * (t + 1)) (by omega)
  refine ⟨2 * N, ?_⟩
  intro F _ d b _ hd hD p₁ p₂ K₁ K₂ hK₁ hK₂
  have h := hbound F d b hd (by omega) p₁ p₂ K₁ K₂ hK₁ hK₂
  have hsplit : d - N + N = d := Nat.sub_add_cancel (by omega)
  have htwice : d ≤ 2 * (d - N + 1) := by omega
  have hmul := Nat.mul_le_mul_left (b * (t + 1)) htwice
  nlinarith

end SharedDecoders
