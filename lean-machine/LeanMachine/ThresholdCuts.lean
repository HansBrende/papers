import Mathlib

/-!
# Exact threshold pullback across partial monotone injections

The domain can have arbitrary gaps, and the source or target interval can
be empty. Thresholds at zero or at the interval length represent constants.
-/

namespace LeanMachine.ThresholdPullback

open Classical
set_option autoImplicit false

/-- A threshold with a specified polarity. The threshold need not belong
to the interval; this permits both constant predicates. -/
structure Cut (n : ℕ) where
  threshold : ℕ
  positive : Bool

def Cut.holds {n : ℕ} (c : Cut n) (x : Fin n) : Prop :=
  if c.positive then c.threshold ≤ x.val else x.val < c.threshold

theorem Cut.monotone_holds {n : ℕ} (c : Cut n) (hc : c.positive = true) :
    Monotone c.holds := by
  intro x y hxy hx
  simp only [Cut.holds, hc, ite_true] at hx ⊢
  exact hx.trans hxy

theorem Cut.antitone_holds {n : ℕ} (c : Cut n) (hc : c.positive = false) :
    Antitone c.holds := by
  intro x y hxy hy
  simp only [Cut.holds, hc, Bool.false_eq_true, ite_false] at hy ⊢
  exact lt_of_le_of_lt hxy hy

/-- Every increasing predicate on a finite partial domain is exactly an
upper threshold on that domain. No interval assumption is imposed on `D`. -/
theorem exists_upper_cut {n : ℕ} (D : Finset (Fin n)) (P : D → Prop)
    (hP : Monotone P) :
    ∃ θ : ℕ, ∀ x : D, P x ↔ θ ≤ x.val.val := by
  let T : Finset D := Finset.univ.filter P
  by_cases hT : T.Nonempty
  · let lo := T.min' hT
    refine ⟨lo.val.val, ?_⟩
    intro x
    constructor
    · intro hx
      exact Finset.min'_le T x (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩)
    · intro hx
      exact hP hx (Finset.mem_filter.mp (Finset.min'_mem T hT)).2
  · refine ⟨n, ?_⟩
    intro x
    constructor
    · intro hx
      exact False.elim (hT ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩)
    · intro hx
      exact False.elim (Nat.not_le_of_lt x.val.isLt hx)

/-- Every decreasing predicate on a finite partial domain is exactly a
lower threshold on that domain, including the empty and constant cases. -/
theorem exists_lower_cut {n : ℕ} (D : Finset (Fin n)) (P : D → Prop)
    (hP : Antitone P) :
    ∃ θ : ℕ, ∀ x : D, P x ↔ x.val.val < θ := by
  let T : Finset D := Finset.univ.filter P
  by_cases hT : T.Nonempty
  · let hi := T.max' hT
    refine ⟨hi.val.val + 1, ?_⟩
    intro x
    constructor
    · intro hx
      have h : x ≤ hi := Finset.le_max' T x (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩)
      exact Nat.lt_succ_of_le h
    · intro hx
      have h : x ≤ hi := Nat.le_of_lt_succ hx
      exact hP h (Finset.mem_filter.mp (Finset.max'_mem T hT)).2
  · refine ⟨0, ?_⟩
    intro x
    constructor
    · intro hx
      exact False.elim (hT ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩)
    · intro hx
      exact False.elim (Nat.not_lt_zero _ hx)

/-- A signed strictly monotone partial map of finite row intervals. -/
structure PartialMap (n m : ℕ) where
  domain : Finset (Fin n)
  toFun : domain → Fin m
  positive : Bool
  strict : if positive then StrictMono toFun else StrictAnti toFun

theorem PartialMap.injective {n m : ℕ} (f : PartialMap n m) :
    Function.Injective f.toFun := by
  cases hp : f.positive with
  | false =>
    have h : StrictAnti f.toFun := by simpa [hp] using f.strict
    exact h.injective
  | true =>
    have h : StrictMono f.toFun := by simpa [hp] using f.strict
    exact h.injective

/-- Exact pullback of every signed threshold.  Equality is required only
on the partial domain; gaps and unused intermediate values are unrestricted.
The output polarity is the product of the two input signs. -/
theorem exists_pullback_cut {n m : ℕ} (f : PartialMap n m) (c : Cut m) :
    ∃ a : Cut n, a.positive = (f.positive == c.positive) ∧
      ∀ x : f.domain, a.holds x.val ↔ c.holds (f.toFun x) := by
  cases hf : f.positive <;> cases hc : c.positive
  · have hmono : Monotone (fun x => c.holds (f.toFun x)) := by
      have hfm : Antitone f.toFun := (show StrictAnti f.toFun by simpa [hf] using f.strict).antitone
      exact (c.antitone_holds hc).comp hfm
    obtain ⟨θ, hθ⟩ := exists_upper_cut f.domain _ hmono
    refine ⟨⟨θ, true⟩, rfl, ?_⟩
    intro x
    exact (hθ x).symm
  · have hanti : Antitone (fun x => c.holds (f.toFun x)) := by
      have hfm : Antitone f.toFun := (show StrictAnti f.toFun by simpa [hf] using f.strict).antitone
      exact (c.monotone_holds hc).comp_antitone hfm
    obtain ⟨θ, hθ⟩ := exists_lower_cut f.domain _ hanti
    refine ⟨⟨θ, false⟩, rfl, ?_⟩
    intro x
    exact (hθ x).symm
  · have hanti : Antitone (fun x => c.holds (f.toFun x)) := by
      have hfm : Monotone f.toFun := (show StrictMono f.toFun by simpa [hf] using f.strict).monotone
      exact (c.antitone_holds hc).comp_monotone hfm
    obtain ⟨θ, hθ⟩ := exists_lower_cut f.domain _ hanti
    refine ⟨⟨θ, false⟩, rfl, ?_⟩
    intro x
    exact (hθ x).symm
  · have hmono : Monotone (fun x => c.holds (f.toFun x)) := by
      have hfm : Monotone f.toFun := (show StrictMono f.toFun by simpa [hf] using f.strict).monotone
      exact (c.monotone_holds hc).comp hfm
    obtain ⟨θ, hθ⟩ := exists_upper_cut f.domain _ hmono
    refine ⟨⟨θ, true⟩, rfl, ?_⟩
    intro x
    exact (hθ x).symm

end LeanMachine.ThresholdPullback
