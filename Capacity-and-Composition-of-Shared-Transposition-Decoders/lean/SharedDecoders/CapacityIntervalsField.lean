import SharedDecoders.CapacityGluing
import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# An actual reversed normal basis for binary row words

The extension field and normal element exist by Mathlib's finite-field and
normal-basis theorems. Column rotation is identified with Frobenius, including
even and composite degrees. No semisimplicity assumption is made.
-/

namespace SharedDecoders.CapacityIntervals

open Module FiniteField

abbrev Bit := ZMod 2
abbrev Extension (d : ℕ) := GaloisField 2 d

variable (d : ℕ) [NeZero d]

noncomputable instance extensionFintype : Fintype (Extension d) := Fintype.ofFinite _

theorem extension_finrank : finrank Bit (Extension d) = d :=
  GaloisField.finrank 2 (NeZero.ne d)

noncomputable def frobenius : Gal(Extension d / Bit) :=
  frobeniusAlgEquivOfAlgebraic Bit (Extension d)

omit [NeZero d] in
theorem frobenius_generates (e : Gal(Extension d / Bit)) :
    e ∈ Subgroup.zpowers (frobenius d) := by
  obtain ⟨j, hj⟩ := (bijective_frobeniusAlgEquivOfAlgebraic_pow Bit (Extension d)).surjective e
  exact ⟨(j.val : ℤ), by simpa [frobenius] using hj⟩

noncomputable def phaseEquiv : Multiplicative (ZMod d) ≃* Gal(Extension d / Bit) :=
  zmodMulEquivOfGenerator (frobenius_generates d)
    ((IsGalois.card_aut_eq_finrank Bit (Extension d)).trans (extension_finrank d))

noncomputable def phase (s : ZMod d) : Gal(Extension d / Bit) :=
  phaseEquiv d (Multiplicative.ofAdd s)

@[simp] theorem phase_zero : phase d 0 = 1 := (phaseEquiv d).map_one

theorem phase_add (s t : ZMod d) : phase d (s + t) = phase d s * phase d t :=
  (phaseEquiv d).map_mul (Multiplicative.ofAdd s) (Multiplicative.ofAdd t)

@[simp] theorem phase_one : phase d 1 = frobenius d :=
  zmodMulEquivOfGenerator_apply_ofAdd_one _ _

theorem phase_one_apply (x : Extension d) : phase d 1 x = x ^ 2 := by
  rw [phase_one]
  simp [frobenius, ZMod.card]

theorem phase_injective : Function.Injective (phase d) :=
  (phaseEquiv d).injective.comp Multiplicative.ofAdd.injective

noncomputable def normalElement : Extension d := (IsGalois.normalBasis Bit (Extension d)) 1

theorem phase_normal_injective : Function.Injective (fun s => phase d s (normalElement d)) := by
  intro s t h
  apply phase_injective d
  apply (IsGalois.normalBasis Bit (Extension d)).injective
  exact (IsGalois.normalBasis_apply (phase d s)).trans
    (h.trans (IsGalois.normalBasis_apply (phase d t)).symm)

noncomputable def reverseIndex : ZMod d ≃ Gal(Extension d / Bit) :=
  (Equiv.neg (ZMod d)).trans (Multiplicative.ofAdd.trans (phaseEquiv d).toEquiv)

noncomputable def rowBasis : Basis (ZMod d) Bit (Extension d) :=
  (IsGalois.normalBasis Bit (Extension d)).reindex (reverseIndex d).symm

theorem rowBasis_apply (j : ZMod d) : rowBasis d j = phase d (-j) (normalElement d) := by
  rw [rowBasis, Basis.reindex_apply]
  simp only [Equiv.symm_symm]
  change (IsGalois.normalBasis Bit (Extension d)) (phase d (-j)) = _
  exact IsGalois.normalBasis_apply (phase d (-j))

noncomputable def rowEncode : (ZMod d → Bit) ≃ₗ[Bit] Extension d := (rowBasis d).equivFun.symm

theorem rowEncode_apply (x : ZMod d → Bit) :
    rowEncode d x = ∑ j, x j • phase d (-j) (normalElement d) := by
  simp only [rowEncode, Basis.equivFun_symm_apply, rowBasis_apply]

/-- The literal plus-shift convention of the shared decoder model. -/
theorem rowEncode_shift (x : ZMod d → Bit) (s : ZMod d) :
    rowEncode d (fun j => x (j + s)) = phase d s (rowEncode d x) := by
  rw [rowEncode_apply, rowEncode_apply, map_sum]
  have hsum := Equiv.sum_comp (Equiv.addRight s)
    (fun j : ZMod d => x j • phase d s (phase d (-j) (normalElement d)))
  calc
    _ = ∑ j, x (j + s) • phase d s (phase d (-(j + s)) (normalElement d)) := by
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      rw [← AlgEquiv.mul_apply, ← phase_add]
      congr 2
      abel
    _ = ∑ j, x j • phase d s (phase d (-j) (normalElement d)) := hsum
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      exact (map_smul (phase d s) (x j) (phase d (-j) (normalElement d))).symm

variable {b : ℕ}

/-- Apply the same field coordinate separately to every row and lane. -/
noncomputable def fieldEncode : State d (Fin b → Bit) ≃ₗ[Bit]
    (ZMod d → Fin b → Extension d) where
  toFun X c l := rowEncode d (fun j => X c j l)
  invFun Y c j l := (rowEncode d).symm (Y c l) j
  left_inv X := by
    funext c j l
    exact congrFun ((rowEncode d).symm_apply_apply (fun j => X c j l)) j
  right_inv Y := by
    funext c l
    exact (rowEncode d).apply_symm_apply (Y c l)
  map_add' X Y := by
    funext c l
    exact (rowEncode d).map_add _ _
  map_smul' a X := by
    funext c l
    exact (rowEncode d).map_smul a _

@[simp] theorem fieldEncode_apply (X : State d (Fin b → Bit)) (c : ZMod d) (l : Fin b) :
    fieldEncode d X c l = rowEncode d (fun j => X c j l) := rfl

theorem fieldEncode_rot (X : State d (Fin b → Bit)) (s c : ZMod d) (l : Fin b) :
    fieldEncode d (rot s X) c l = phase d s (fieldEncode d X c l) :=
  rowEncode_shift d (fun j => X c j l) s

end SharedDecoders.CapacityIntervals
