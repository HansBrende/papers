import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Joint residual records for an exhibited affine computation

The source is an arbitrary finite set, not necessarily a linear or affine
code. A single joint record is charged once. The kernel is that of the
complete baseline, not of an isolated stage or an assumed normal form.
-/

namespace SharedDecoders

open Module
open scoped BigOperators

variable {F V W Ω : Type*} [Field F] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]

/-- A finite set in one affine equation fibre fits in a translate of the kernel. -/
theorem affine_equation_card_le [Finite F] [Finite V] [FiniteDimensional F V]
    (S : Set V) (A : V →ₗ[F] W) (c : W)
    (h : ∀ x ∈ S, A x = c) :
    Nat.card S ≤ Nat.card F ^ finrank F A.ker := by
  classical
  by_cases hS : S.Nonempty
  · obtain ⟨x₀, hx₀⟩ := hS
    have hi : Nat.card S ≤ Nat.card A.ker := by
      refine Nat.card_le_card_of_injective
        (fun x : S => (⟨x.1 - x₀, ?_⟩ : A.ker)) ?_
      · apply LinearMap.mem_ker.mpr
        rw [map_sub, h x.1 x.2, h x₀ hx₀, sub_self]
      · intro x y heq
        apply Subtype.ext
        exact sub_left_injective (congrArg Subtype.val heq)
    rwa [Module.natCard_eq_pow_finrank (K := F) (V := A.ker)] at hi
  · have : IsEmpty S := ⟨fun x => hS ⟨x.1, x.2⟩⟩
    rw [Nat.card_of_isEmpty]
    exact Nat.zero_le _

/-- Counting the attained record values, rather than the entire record alphabet. -/
theorem natCard_le_image_mul {α β : Type*} [Finite α]
    (S : Set α) (z : α → β) (B : ℕ)
    (h : ∀ ω, Nat.card {x : S // z x.1 = ω} ≤ B) :
    Nat.card S ≤ Nat.card (z '' S) * B := by
  classical
  have : Finite (z '' S) := (Set.toFinite S).image z
  let f : S → z '' S := fun x => ⟨z x.1, ⟨x.1, x.2, rfl⟩⟩
  let : Fintype (z '' S) := Fintype.ofFinite _
  have hcard : Nat.card S = ∑ ω, Nat.card {x : S // f x = ω} := by
    rw [← Nat.card_sigma]
    exact Nat.card_congr (Equiv.sigmaFiberEquiv f).symm
  have hf (ω : z '' S) : Nat.card {x : S // f x = ω} ≤ B := by
    apply le_trans _ (h ω.1)
    refine Nat.card_le_card_of_injective
      (fun x : {x : S // f x = ω} =>
        (⟨x.1, congrArg Subtype.val x.2⟩ : {x : S // z x.1 = ω.1})) ?_
    intro x y heq
    exact Subtype.ext (congrArg (fun t : {x : S // z x.1 = ω.1} => t.1) heq)
  rw [hcard, Nat.card_eq_fintype_card]
  calc
    _ ≤ ∑ _ω : z '' S, B := Finset.sum_le_sum (fun ω _ => hf ω)
    _ = _ := by simp

/-- The exact affine constraint is needed only on the selected record fibre. -/
theorem equation_record_fiber_card_le [Finite F] [Finite V] [FiniteDimensional F V]
    (S : Set V) (A : V →ₗ[F] W) (z : V → Ω) (ω : Ω) (c : W)
    (h : ∀ x ∈ S, z x = ω → A x = c) :
    Nat.card {x : S // z x.1 = ω} ≤ Nat.card F ^ finrank F A.ker := by
  classical
  let he : {x : S // z x.1 = ω} ≃ {x : V // x ∈ S ∧ z x = ω} :=
    ⟨fun x => ⟨x.1.1, x.1.2, x.2⟩, fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩,
      fun _ => rfl, fun _ => rfl⟩
  rw [Nat.card_congr he]
  exact affine_equation_card_le {x | x ∈ S ∧ z x = ω} A c
    (fun x hx => h x hx.1 hx.2)

/-- Every fixed joint residual record leaves the same complete linear part. -/
theorem residual_record_card_le [Finite F] [Finite V] [FiniteDimensional F V]
    (S : Set V) (A : V →ₗ[F] W) (z : V → Ω) (offset : Ω → W)
    (h : ∀ x ∈ S, A x = offset (z x)) :
    Nat.card S ≤ Nat.card (z '' S) * Nat.card F ^ finrank F A.ker := by
  apply natCard_le_image_mul
  intro ω
  exact equation_record_fiber_card_le S A z ω (offset ω)
    (fun x hx hz => (h x hx).trans (congrArg offset hz))

/-- A record fibre has at most as many points as the complete baseline kernel. -/
theorem same_record_fiber_card_le [Finite F] [Finite V] [FiniteDimensional F V]
    (S : Set V) (A : V →ₗ[F] W) (z : V → Ω)
    (h : ∀ x ∈ S, ∀ y ∈ S, z x = z y → A x = A y) (ω : Ω) :
    Nat.card {x : S // z x.1 = ω} ≤ Nat.card F ^ finrank F A.ker := by
  classical
  by_cases hf : Nonempty {x : S // z x.1 = ω}
  · obtain ⟨x₀⟩ := hf
    exact equation_record_fiber_card_le S A z ω (A x₀.1)
      (fun x hx hz => h x hx x₀.1 x₀.1.2 (hz.trans x₀.2.symm))
  · have : IsEmpty {x : S // z x.1 = ω} := not_nonempty_iff.mp hf
    simp only [Nat.card_of_isEmpty, zero_le]

/-- Only equality of the attained records is needed, not an offset decoder or
a finite ambient record alphabet. -/
theorem same_record_card_le [Finite F] [Finite V] [FiniteDimensional F V]
    (S : Set V) (A : V →ₗ[F] W) (z : V → Ω)
    (h : ∀ x ∈ S, ∀ y ∈ S, z x = z y → A x = A y) :
    Nat.card S ≤ Nat.card (z '' S) * Nat.card F ^ finrank F A.ker :=
  natCard_le_image_mul S z _ (same_record_fiber_card_le S A z h)

/-- A fixed global affine recurrence with the actual joint residuals inserted. -/
def residualRun (L : ℕ → V →ₗ[F] V) (g : ℕ → V) (J : W →ₗ[F] V)
    (j : V) (e : ℕ → W → V) (x : W) : ℕ → V
  | 0 => J x + j
  | n + 1 => L n (residualRun L g J j e x n) + g n + e n x

def residualLinearPart (L : ℕ → V →ₗ[F] V) (J : W →ₗ[F] V) :
    ℕ → W →ₗ[F] V
  | 0 => J
  | n + 1 => (L n).comp (residualLinearPart L J n)

def residualOffset (L : ℕ → V →ₗ[F] V) (g : ℕ → V) (j : V)
    (e : ℕ → W → V) (x : W) : ℕ → V
  | 0 => j
  | n + 1 => L n (residualOffset L g j e x n) + g n + e n x

/-- The original chronological recurrence retains its baseline linear part. -/
theorem residualRun_eq (L : ℕ → V →ₗ[F] V) (g : ℕ → V) (J : W →ₗ[F] V)
    (j : V) (e : ℕ → W → V) (x : W) (n : ℕ) :
    residualRun L g J j e x n = residualLinearPart L J n x +
      residualOffset L g j e x n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [residualRun, residualLinearPart, residualOffset, ih, map_add,
      LinearMap.comp_apply]
    abel

omit [AddCommGroup W] [Module F W] in
/-- Equal actual residual tuples give equal replay offsets. -/
theorem residualOffset_eq_of_records (L : ℕ → V →ₗ[F] V) (g : ℕ → V) (j : V)
    (e : ℕ → W → V) (x y : W) (n : ℕ)
    (h : ∀ i < n, e i x = e i y) :
    residualOffset L g j e x n = residualOffset L g j e y n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [residualOffset]
    rw [ih (fun i hi => h i (by omega)), h n (by omega)]

end SharedDecoders
