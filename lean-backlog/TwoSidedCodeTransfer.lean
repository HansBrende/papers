import RowSpreadCrux
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.Data.ZMod.Basic

/-!
# Two-sided recovery and the native crux

Two-sided recovery requires both an array code and its transposed image to
obey the same whole-row rule. No transpose invariance, linearity, or field
structure is assumed. A finite counting argument transfers a two-sided
deficit to half that deficit for one-sided codes. The native consequences
reuse `RowSpreadCrux`; a positive capacity deficit remains a hypothesis.
-/

namespace LeanBacklog.RowSpread

open Finset BoundedNesting MergeDepth BoundedStackDepth Transpose

universe u

/-- Transpose an array without changing its alphabet. -/
def transposeWord {d : ℕ} {α : Type u} (x : Entry d → α) : Entry d → α :=
  fun p => x (p.2, p.1)

@[simp] theorem transposeWord_transposeWord {d : ℕ} {α : Type u}
    (x : Entry d → α) : transposeWord (transposeWord x) = x := rfl

/-- Both directions use precisely the same helper relation. -/
def IsTwoSidedWholeRowCode {d : ℕ} {α : Type u}
    (ρ : Fin d → Finset (Fin d)) (C : Finset (Entry d → α)) : Prop :=
  IsWholeRowCodeExcept ρ ∅ C ∧
    ∀ x ∈ C, ∀ y ∈ C, ∀ r,
      (∀ s ∈ ρ r, ∀ j, x (j, s) = y (j, s)) →
      ∀ i, x (r, i) = y (r, i)

/-- The coordinate definition is exactly whole-row recovery for the code
and for its transposed image, with one unchanged helper map. -/
theorem twoSided_iff_transpose {d : ℕ} {α : Type u} [DecidableEq α]
    (ρ : Fin d → Finset (Fin d)) (C : Finset (Entry d → α)) :
    IsTwoSidedWholeRowCode ρ C ↔ IsWholeRowCodeExcept ρ ∅ C ∧
      IsWholeRowCodeExcept ρ ∅ (C.image transposeWord) := by
  rw [IsTwoSidedWholeRowCode, wholeRowCode_iff ρ ∅ (C.image transposeWord)]
  constructor
  · rintro ⟨hC, hrev⟩
    refine ⟨hC, ?_⟩
    intro x hx y hy r _ hxy i
    obtain ⟨x₀, hx₀, rfl⟩ := mem_image.mp hx
    obtain ⟨y₀, hy₀, rfl⟩ := mem_image.mp hy
    exact hrev x₀ hx₀ y₀ hy₀ r hxy i
  · rintro ⟨hC, hrev⟩
    refine ⟨hC, ?_⟩
    intro x hx y hy r hxy i
    exact hrev _ (mem_image_of_mem transposeWord hx)
      _ (mem_image_of_mem transposeWord hy) r (by simp) hxy i

/-- Finite two-sided capacity target, with no sign restriction on its exponent. -/
def TwoSidedWholeRowCardinalityBound (d w : ℕ) (α : Type u) [Fintype α]
    (exponent : ℝ) : Prop :=
  ∀ (ρ : Fin d → Finset (Fin d)) (C : Finset (Entry d → α)),
    (∀ r, (ρ r).card ≤ w) → IsTwoSidedWholeRowCode ρ C →
      (C.card : ℝ) ≤ (Fintype.card α : ℝ) ^ exponent

/-- The first-coordinate image of a difference fibre is two-sided.
The auxiliary group operation is used only for counting translations. -/
theorem difference_fibre_twoSided {d : ℕ} {α : Type u} [AddGroup α] [DecidableEq α]
    (ρ : Fin d → Finset (Fin d)) (C : Finset (Entry d → α))
    (hC : IsWholeRowCodeExcept ρ ∅ C) (z : Entry d → α) :
    IsTwoSidedWholeRowCode ρ
      (((C.product C).filter fun p : (Entry d → α) × (Entry d → α) =>
        p.1 - transposeWord p.2 = z).image Prod.fst) := by
  classical
  let F : Finset ((Entry d → α) × (Entry d → α)) :=
    (C.product C).filter fun p => p.1 - transposeWord p.2 = z
  have hmem {x y : Entry d → α} (h : (x, y) ∈ F) :
      x ∈ C ∧ y ∈ C ∧ x - transposeWord y = z := by
    simpa [F, and_assoc] using h
  change IsWholeRowCodeExcept ρ ∅ (F.image Prod.fst) ∧ _
  constructor
  · rw [wholeRowCode_iff]
    intro x hx y hy r hr hxy i
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hx
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hy
    exact (wholeRowCode_iff ρ ∅ C).mp hC p.1 (hmem hp).1 q.1 (hmem hq).1 r hr hxy i
  · intro x hx y hy r hxy i
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hx
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hy
    obtain ⟨_, hp', hpz⟩ := hmem hp
    obtain ⟨_, hq', hqz⟩ := hmem hq
    have he (v : Entry d) : p.1 v - p.2 (v.2, v.1) = q.1 v - q.2 (v.2, v.1) :=
      congrFun (hpz.trans hqz.symm) v
    have hrec : p.2 (i, r) = q.2 (i, r) := by
      apply (wholeRowCode_iff ρ ∅ C).mp hC p.2 hp' q.2 hq' r (by simp)
      intro s hs j
      have h := he (j, s)
      rw [hxy s hs j] at h
      exact sub_right_inj.mp h
    have h := he (r, i)
    rw [hrec] at h
    exact sub_left_inj.mp h

/-- Relation-specific squared bound. This is stronger than a uniform-window
adapter: any common real cardinality bound for the two-sided codes of this
one relation bounds the square of every one-sided code's size. -/
theorem wholeRow_card_sq_le_of_twoSided_group {d : ℕ} {α : Type u}
    [Fintype α] [AddGroup α] (ρ : Fin d → Finset (Fin d))
    (C : Finset (Entry d → α)) (hC : IsWholeRowCodeExcept ρ ∅ C)
    (A : ℝ) (hbound : ∀ D : Finset (Entry d → α),
      IsTwoSidedWholeRowCode ρ D → (D.card : ℝ) ≤ A) :
    (C.card : ℝ) ^ 2 ≤ (Fintype.card α : ℝ) ^ (d * d) * A := by
  classical
  have hcount := card_le_of_real_fibre_bound (C.product C)
    (fun p => p.1 - transposeWord p.2) A (fun z => ?_)
  · simpa [sq, Entry, Nat.cast_pow] using hcount
  · let F : Finset ((Entry d → α) × (Entry d → α)) :=
    (C.product C).filter fun p => p.1 - transposeWord p.2 = z
    have hinj : Set.InjOn Prod.fst (F : Set ((Entry d → α) × (Entry d → α))) := by
      intro x hx y hy hxy
      have hxz := (mem_filter.mp hx).2
      have hyz := (mem_filter.mp hy).2
      have he : transposeWord x.2 = transposeWord y.2 := by
        have h := hxz.trans hyz.symm
        rw [hxy] at h
        exact sub_right_inj.mp h
      exact Prod.ext hxy (congrArg transposeWord he)
    calc
      (F.card : ℝ) = (F.image Prod.fst).card := by rw [card_image_of_injOn hinj]
      _ ≤ A := hbound _ (difference_fibre_twoSided ρ C hC z)

/-- Every nonempty finite alphabet can be given an auxiliary cyclic group
structure. The statement and the recovery hypotheses use none of it. -/
theorem wholeRow_card_sq_le_of_twoSided {d : ℕ} {α : Type u} [Fintype α]
    (hα : 0 < Fintype.card α) (ρ : Fin d → Finset (Fin d))
    (C : Finset (Entry d → α)) (hC : IsWholeRowCodeExcept ρ ∅ C)
    (A : ℝ) (hbound : ∀ D : Finset (Entry d → α),
      IsTwoSidedWholeRowCode ρ D → (D.card : ℝ) ≤ A) :
    (C.card : ℝ) ^ 2 ≤ (Fintype.card α : ℝ) ^ (d * d) * A := by
  let : NeZero (Fintype.card α) := ⟨by omega⟩
  let e : α ≃ ZMod (Fintype.card α) :=
    (Fintype.equivFin α).trans (ZMod.finEquiv (Fintype.card α)).toEquiv
  let : AddCommGroup α := e.addCommGroup
  exact wholeRow_card_sq_le_of_twoSided_group ρ C hC A hbound

/-- Passing to a smaller class of codes loses nothing in this direction. -/
theorem WholeRowCardinalityBound.twoSided {d w : ℕ} {α : Type u} [Fintype α]
    {a : ℝ} (h : WholeRowCardinalityBound d w α a) :
    TwoSidedWholeRowCardinalityBound d w α a :=
  fun ρ C hρ hC => h ρ C hρ hC.1

/-- A two-sided exponent `a` yields the one-sided exponent `(d²+a)/2`.
Even a one-symbol alphabet is allowed; no code-size or exponent sign is assumed. -/
theorem TwoSidedWholeRowCardinalityBound.oneSided {d w : ℕ} {α : Type u}
    [Fintype α] {a : ℝ} (h : TwoSidedWholeRowCardinalityBound d w α a)
    (hα : 0 < Fintype.card α) :
    WholeRowCardinalityBound d w α (((d : ℝ) ^ 2 + a) / 2) := by
  intro ρ C hρ hC
  have hsq := wholeRow_card_sq_le_of_twoSided hα ρ C hC
    ((Fintype.card α : ℝ) ^ a) (fun D hD => h ρ D hρ hD)
  have hq : (0 : ℝ) < Fintype.card α := by exact_mod_cast hα
  have he : ((Fintype.card α : ℝ) ^ (((d : ℝ) ^ 2 + a) / 2)) ^ 2 =
      (Fintype.card α : ℝ) ^ (d * d) * (Fintype.card α : ℝ) ^ a := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq.le]
    have hx : (((d : ℝ) ^ 2 + a) / 2) * (2 : ℕ) = (d * d : ℕ) + a := by
      push_cast
      ring
    rw [hx, Real.rpow_add hq, Real.rpow_natCast]
  nlinarith [Real.rpow_nonneg hq.le (((d : ℝ) ^ 2 + a) / 2)]

/-- Open common two-sided rate target, uniform over all finite alphabets. -/
def UniformTwoSidedWholeRowRate (rate : ℝ) : Prop :=
  ∀ (w : ℕ) (η : ℝ), 0 < η → ∃ d₀ : ℕ, ∀ d ≥ d₀,
    ∀ (α : Type u) [Fintype α], 2 ≤ Fintype.card α →
      TwoSidedWholeRowCardinalityBound d w α ((rate + η) * (d : ℝ) ^ 2)

/-- Open common two-sided rate target at the canonical growing alphabets. -/
def UniformTwoSidedWholeRowRateCanonicalBits (rate : ℝ) : Prop :=
  ∀ (w : ℕ) (η : ℝ), 0 < η → ∃ d₀ : ℕ, ∀ d ≥ d₀,
    TwoSidedWholeRowCardinalityBound d w (Fin (entryBits d) → Bool)
      ((rate + η) * (d : ℝ) ^ 2)

/-- Uniform finite-alphabet rates transfer with exactly half the deficit. -/
theorem UniformTwoSidedWholeRowRate.oneSided {rate : ℝ}
    (h : UniformTwoSidedWholeRowRate.{u} rate) :
    UniformWholeRowRate.{u} ((1 + rate) / 2) := by
  intro w η hη
  obtain ⟨d₀, hd₀⟩ := h w (2 * η) (by positivity)
  refine ⟨d₀, fun d hd α _ hα => ?_⟩
  convert (hd₀ d hd α hα).oneSided (by omega) using 1; ring

/-- No fixed-alphabet restriction is introduced by the transfer. -/
theorem UniformTwoSidedWholeRowRateCanonicalBits.oneSided {rate : ℝ}
    (h : UniformTwoSidedWholeRowRateCanonicalBits rate) :
    UniformWholeRowRateCanonicalBits ((1 + rate) / 2) := by
  intro w η hη
  obtain ⟨d₀, hd₀⟩ := h w (2 * η) (by positivity)
  refine ⟨d₀, fun d hd => ?_⟩
  convert (hd₀ d hd).oneSided (by simp) using 1; ring

/-- The one-sided and two-sided common-positive-deficit questions are equivalent.
This equivalence concerns actual codes, not their Shannon relaxations. -/
theorem commonDeficit_iff_twoSided :
    (∃ δ : ℝ, 0 < δ ∧ UniformWholeRowRateCanonicalBits (1 - δ)) ↔
      ∃ δ : ℝ, 0 < δ ∧ UniformTwoSidedWholeRowRateCanonicalBits (1 - δ) := by
  constructor
  · rintro ⟨δ, hδ, h⟩
    refine ⟨δ, hδ, fun w η hη => ?_⟩
    obtain ⟨d₀, hd₀⟩ := h w η hη
    exact ⟨d₀, fun d hd => (hd₀ d hd).twoSided⟩
  · rintro ⟨δ, hδ, h⟩
    refine ⟨δ / 2, by positivity, ?_⟩
    convert h.oneSided using 1; ring

/-- Literal native crux at half the two-sided deficit. -/
theorem uniformTwoSidedWholeRowRateCanonicalBits_crux
    {k β D : ℕ} {C δ : ℝ} (hC : 1 ≤ C)
    (hbound : UniformTwoSidedWholeRowRateCanonicalBits (1 - δ)) :
    Crux k C β D (δ / 2) := by
  apply uniformWholeRowRateCanonicalBits_crux hC
  convert hbound.oneSided using 1; ring

/-- The all-alphabet form is uniform over every positive entry bit width. -/
theorem uniformTwoSidedWholeRowRate_cruxOn
    {k β D : ℕ} {C δ : ℝ} (hC : 1 ≤ C)
    (hbound : UniformTwoSidedWholeRowRate.{0} (1 - δ)) :
    CruxOn (fun _ b => 1 ≤ b) k C β D (δ / 2) := by
  apply uniformWholeRowRate_cruxOn hC
  convert hbound.oneSided using 1; ring

/-- A positive canonical two-sided deficit excludes oblivious linear-time
transposers. The hypothesis is an open capacity bound, not an asserted fact. -/
theorem uniformTwoSidedWholeRowRateCanonicalBits_excludes
    {k β : ℕ} {C δ : ℝ} (hC : 1 ≤ C) (hδ : 0 < δ)
    (hbound : UniformTwoSidedWholeRowRateCanonicalBits (1 - δ)) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ M : TM, M.k = k → valueWidth M ≤ β → ∀ T : ℕ,
      ¬ ObliviousLinTime M d (entryBits d) C T := by
  apply uniformWholeRowRateCanonicalBits_excludes (δ := δ / 2) hC (by positivity)
  convert hbound.oneSided using 1; ring

/-- The direct route needs only one explicit window, with threshold 169ε/32. -/
theorem twoSidedWholeRow_window_bound_excludes
    {k β : ℕ} {C ε δ : ℝ} (hC : 1 ≤ C) (hε : 0 < ε)
    (hgap : (169 / 32 : ℝ) * ε < δ)
    (hbound : ∀ η : ℝ, 0 < η → ∃ d₀ : ℕ, ∀ d ≥ d₀,
      TwoSidedWholeRowCardinalityBound d
        (rowSpreadWindow k β (genieDepth k β C ε) C ε)
        (Fin (entryBits d) → Bool) ((1 - δ + η) * (d : ℝ) ^ 2)) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ M : TM, M.k = k → valueWidth M ≤ β → ∀ T : ℕ,
      ¬ ObliviousLinTime M d (entryBits d) C T := by
  apply wholeRow_window_bound_excludes (δ := δ / 2) hC hε (by linarith)
  intro η hη
  obtain ⟨d₀, hd₀⟩ := hbound (2 * η) (by positivity)
  refine ⟨d₀, fun d hd => ?_⟩
  convert (hd₀ d hd).oneSided (by simp) using 1; ring

#print axioms difference_fibre_twoSided
#print axioms twoSided_iff_transpose
#print axioms wholeRow_card_sq_le_of_twoSided
#print axioms TwoSidedWholeRowCardinalityBound.oneSided
#print axioms UniformTwoSidedWholeRowRate.oneSided
#print axioms commonDeficit_iff_twoSided
#print axioms uniformTwoSidedWholeRowRateCanonicalBits_crux
#print axioms uniformTwoSidedWholeRowRate_cruxOn
#print axioms uniformTwoSidedWholeRowRateCanonicalBits_excludes
#print axioms twoSidedWholeRow_window_bound_excludes

end LeanBacklog.RowSpread
