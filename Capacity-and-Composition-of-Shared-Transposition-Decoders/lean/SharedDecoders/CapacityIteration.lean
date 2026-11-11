import SharedDecoders.CapacityAmbient
import Mathlib.Basic.Real.Basic

/-! # Repeated translate intersection inside its actual invariant ambient -/

namespace SharedDecoders

open Module

variable {F A κ : Type*} [Field F] [AddCommGroup A] [Module F A] {d : ℕ}

def extendShifts (Δ : Finset (ZMod d)) (t : ZMod d) : Finset (ZMod d) :=
  Δ ∪ Δ.image (fun s => s + t)

theorem commonPreimage_extend (C : Submodule F (State d A))
    (Δ : Finset (ZMod d)) (t : ZMod d) :
    commonPreimage C (extendShifts Δ t) =
      commonPreimage C Δ ⊓ (commonPreimage C Δ).comap (rotLinear F t) := by
  ext X
  simp only [mem_commonPreimage, extendShifts, Finset.mem_union,
    Finset.mem_image, Submodule.mem_inf, Submodule.mem_comap, rotLinear_apply]
  constructor
  · intro h
    constructor
    · intro s hs
      exact h s (Or.inl hs)
    · intro s hs
      simpa only [rot_rot] using h (s + t) (Or.inr ⟨s, hs, rfl⟩)
  · rintro ⟨h₁, h₂⟩ s (hs | ⟨u, hu, rfl⟩)
    · exact h₁ s hs
    · simpa only [rot_rot] using h₂ u hu

@[simp] theorem commonPreimage_zero (C : Submodule F (State d A)) :
    commonPreimage C {0} = C := by
  ext X
  simp

def translateSets (t : ℕ → ZMod d) : ℕ → Finset (ZMod d)
  | 0 => {0}
  | n + 1 => extendShifts (translateSets t n) (t n)

variable [NeZero d] [FiniteDimensional F A]

theorem two_mul_finrank_inf_comap_le (D H : Submodule F (State d A))
    (t : ZMod d) (hD : D ≤ H)
    (hH : ∀ X ∈ H, rot (-t) X ∈ H) :
    2 * finrank F D ≤ finrank F H +
      finrank F (D ⊓ D.comap (rotLinear F t) : Submodule F (State d A)) := by
  have hpre : D.comap (rotLinear F t) ≤ H := by
    intro X hX
    simpa using hH (rot t X) (hD hX)
  have hsup := Submodule.finrank_mono (sup_le hD hpre)
  have hgrass := Submodule.finrank_sup_add_finrank_inf_eq D (D.comap (rotLinear F t))
  have hdim := SwapRigidity.finrank_le_finrank_comap D (rotLinear F t)
  omega

theorem IsSharedCode.two_mul_commonPreimage_finrank_le {p : ZMod d → κ}
    {C : Submodule F (State d A)} (h : IsSharedCode F p C)
    (Δ : Finset (ZMod d)) (t : ZMod d) :
    2 * finrank F (commonPreimage C Δ) ≤
      d * componentCount p Δ * finrank F A +
      finrank F (commonPreimage C (extendShifts Δ t)) := by
  have hh := two_mul_finrank_inf_comap_le (commonPreimage C Δ)
    (covarianceSpace p Δ) t (h.commonPreimage_le_covariance Δ)
    (fun X hX => covarianceSpace_rot hX (-t))
  rwa [finrank_covarianceSpace, ← commonPreimage_extend] at hh

theorem componentCount_zero (p : ZMod d → κ) : componentCount p {0} = d := by
  classical
  have hrel : ∀ c e, Relation.EqvGen (Link p {0}) c e → c = e := by
    intro c e hce
    induction hce with
    | rel c e h => simpa [Link, SwapRigidity.Link] using h.2
    | refl _ => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  let equiv : LinkComponent p {0} ≃ ZMod d :=
    { toFun := Quotient.lift id (fun _ _ h => hrel _ _ h)
      invFun := Quotient.mk _
      left_inv := by intro q; induction q using Quotient.inductionOn; rfl
      right_inv := by intro c; rfl }
  exact (Fintype.card_congr equiv).trans (ZMod.card d)

/-- The finite telescoping identity used for an arbitrary number of stages. -/
theorem dyadic_bound (x n : ℕ → ℝ) (k : ℕ)
    (hstep : ∀ j < k, 2 * x j ≤ n j + x (j + 1)) (hend : x k ≤ n k) :
    x 0 ≤ (∑ j ∈ Finset.range k, n j / 2 ^ (j + 1)) + n k / 2 ^ k := by
  have hpartial : ∀ i ≤ k,
      x 0 ≤ (∑ j ∈ Finset.range i, n j / 2 ^ (j + 1)) + x i / 2 ^ i := by
    intro i hi
    induction i with
    | zero => simp
    | succ i ih =>
      have hprev := ih (by omega)
      have hcur := hstep i (by omega)
      rw [Finset.sum_range_succ]
      have hp : (0 : ℝ) < 2 ^ i := pow_pos (by norm_num) _
      have hdiv : x i / 2 ^ i ≤ n i / 2 ^ (i + 1) + x (i + 1) / 2 ^ (i + 1) := by
        rw [pow_succ]
        field_simp
        nlinarith
      linarith
  apply (hpartial k le_rfl).trans
  gcongr

/-- Actual nested translated sources, with exact component dimensions at every stage. -/
theorem IsSharedCode.iterated_finrank_le {p : ZMod d → κ}
    {C : Submodule F (State d A)} (h : IsSharedCode F p C)
    (t : ℕ → ZMod d) (k : ℕ) :
    (finrank F C : ℝ) ≤
      (∑ j ∈ Finset.range k,
        (d * componentCount p (translateSets t j) * finrank F A : ℕ) / (2 : ℝ) ^ (j + 1)) +
      (d * componentCount p (translateSets t k) * finrank F A : ℕ) / (2 : ℝ) ^ k := by
  let x j : ℝ := finrank F (commonPreimage C (translateSets t j))
  let n j : ℝ := d * componentCount p (translateSets t j) * finrank F A
  have hstep : ∀ j < k, 2 * x j ≤ n j + x (j + 1) := by
    intro j _
    dsimp [x, n, translateSets]
    exact_mod_cast h.two_mul_commonPreimage_finrank_le (translateSets t j) (t j)
  have hend : x k ≤ n k := by
    dsimp [x, n]
    exact_mod_cast h.commonPreimage_finrank_le (translateSets t k)
  have hh := dyadic_bound x n k hstep hend
  change (finrank F (commonPreimage C {0}) : ℝ) ≤ _ at hh
  rw [commonPreimage_zero] at hh
  simpa only [n, Nat.cast_mul] using hh

/-- Three actual intersection stages, in integral form for the run-count application. -/
theorem IsSharedCode.eight_mul_finrank_le {p : ZMod d → κ}
    {C : Submodule F (State d A)} (h : IsSharedCode F p C)
    (s t u : ZMod d) :
    8 * finrank F C ≤ 4 * (d * d * finrank F A) +
      2 * (d * componentCount p (extendShifts {0} s) * finrank F A) +
      d * componentCount p (extendShifts (extendShifts {0} s) t) * finrank F A +
      d * componentCount p (extendShifts (extendShifts (extendShifts {0} s) t) u) * finrank F A := by
  have h₀ := h.two_mul_commonPreimage_finrank_le {0} s
  have h₁ := h.two_mul_commonPreimage_finrank_le (extendShifts {0} s) t
  have h₂ := h.two_mul_commonPreimage_finrank_le (extendShifts (extendShifts {0} s) t) u
  have h₃ := h.commonPreimage_finrank_le (extendShifts (extendShifts (extendShifts {0} s) t) u)
  rw [commonPreimage_zero, componentCount_zero] at h₀
  omega

end SharedDecoders
