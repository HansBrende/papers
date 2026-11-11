import SharedDecoders.CapacityClosureAverage

/-! Scalar-closure defect of an actual two-class binary source. -/

namespace SharedDecoders.CapacityClosure

open Module CapacityIntervals

variable {d b : ℕ} [NeZero d]

noncomputable def residual (C : Submodule Bit (BinaryState d b))
    (p : ZMod d → Bool) (r : Bool → ZMod d) : Submodule Bit (BinaryState d b) :=
  C ⊓ LinearMap.ker (classProjection p r)

def residualRows (r : Bool → ZMod d) : Finset (ZMod d) :=
  Finset.univ \ {r false, r true}

theorem residual_rows_card {p : ZMod d → Bool} {r : Bool → ZMod d}
    (hr : ∀ a, p (r a) = a) : (residualRows r).card + 2 = d := by
  have hne : r false ≠ r true := by
    intro he
    have hh := congrArg p he
    rw [hr, hr] at hh
    cases hh
  have hh := Finset.card_sdiff_add_card_eq_card
    (Finset.subset_univ ({r false, r true} : Finset (ZMod d)))
  simpa only [residualRows, Finset.card_pair hne, Finset.card_univ, ZMod.card] using hh

theorem residual_le_rows (C : Submodule Bit (BinaryState d b))
    {p : ZMod d → Bool} {r : Bool → ZMod d} (hr : ∀ a, p (r a) = a) :
    residual C p r ≤ rowSpace (residualRows r) := by
  intro X hX c hc
  have hz := (mem_classProjection_ker hr).mp hX.2
  have hm : c = r false ∨ c = r true := by
    by_cases h₀ : c = r false
    · exact Or.inl h₀
    · right
      by_contra h₁
      exact hc (by simp [residualRows, h₀, h₁])
  rcases hm with rfl | rfl
  · exact hz false
  · exact hz true

omit [NeZero d] in
theorem residual_isSharedCode {C : Submodule Bit (BinaryState d b)}
    {p : ZMod d → Bool} (hC : IsSharedCode Bit p C) (r : Bool → ZMod d) :
    IsSharedCode Bit p (residual C p r) := by
  obtain ⟨f, hf⟩ := hC
  exact ⟨f, fun X hX c => hf X hX.1 c⟩

theorem finrank_le_residual_add (C : Submodule Bit (BinaryState d b))
    {p : ZMod d → Bool} {r : Bool → ZMod d} (hr : ∀ a, p (r a) = a) :
    finrank Bit C ≤ finrank Bit (residual C p r) + 2*d*b := by
  have hh := finrank_le_completedCode hr C
  rw [finrank_completedCode hr] at hh
  have hb : finrank Bit (Fin b → Bit) = b := by simp
  rw [Fintype.card_bool, hb] at hh
  exact hh

/-- The complete source, not an unpromised scalar hull, satisfies the finite
bound. The defect is measured in binary dimensions and all lanes may couple. -/
theorem capacity_bound {C : Submodule Bit (BinaryState d b)} {p : ZMod d → Bool}
    (hC : IsSharedCode Bit p C) {r : Bool → ZMod d} (hr : ∀ a, p (r a) = a)
    (R : ℕ) (hR : 0 < R) :
    (finrank Bit C : ℝ) ≤ 3/5*(b : ℝ)*(d : ℝ)^2 + (b : ℝ)*d +
      (b : ℝ)*d*error d R + 13/5*(defect (residual C p r) : ℝ) := by
  have hres := residual_finite_bound (residual_isSharedCode hC r)
    (residual_le_rows C hr) R hR
  have hdim := (Nat.cast_le (α := ℝ)).2 (finrank_le_residual_add C hr)
  have hrows := congrArg (Nat.cast (R := ℝ)) (residual_rows_card hr)
  push_cast at hres hdim hrows
  nlinarith only [hres, hdim, hrows]

end SharedDecoders.CapacityClosure
