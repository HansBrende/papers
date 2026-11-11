import SharedDecoders.CapacityClosureRank
import SharedDecoders.CapacityClosureIsolation

/-! Actual scalar hulls in the reversed-normal-basis coordinates. -/

namespace SharedDecoders.CapacityClosure

open Module CapacityIntervals

variable {d b : ℕ} [NeZero d]

abbrev BinaryState (d b : ℕ) := State d (Fin b → Bit)
abbrev FieldState (d b : ℕ) := ZMod d → Fin b → Extension d

/-- The rows outside `S` vanish. -/
def rowSpace (S : Finset (ZMod d)) : Submodule Bit (BinaryState d b) where
  carrier := {X | ∀ c ∉ S, X c = 0}
  zero_mem' := by simp
  add_mem' := by intro X Y hX hY c hc; simp [hX c hc, hY c hc]
  smul_mem' := by intro a X hX c hc; simp [hX c hc]

omit [NeZero d] in
@[simp] theorem mem_rowSpace {S : Finset (ZMod d)} {X : BinaryState d b} :
    X ∈ rowSpace S ↔ ∀ c ∉ S, X c = 0 := Iff.rfl

noncomputable def rowSpaceEquiv (S : Finset (ZMod d)) :
    rowSpace S (b := b) ≃ₗ[Bit] (S → ZMod d → Fin b → Bit) where
  toFun X c := X.1 c.1
  invFun Y := ⟨fun c => if h : c ∈ S then Y ⟨c,h⟩ else 0, by
    intro c hc; simp [hc]⟩
  left_inv X := by
    apply Subtype.ext
    funext c
    by_cases hc : c ∈ S
    · simp [hc]
    · simp [hc, X.2 c hc]
  right_inv Y := by funext c; simp
  map_add' X Y := rfl
  map_smul' a X := rfl

theorem finrank_rowSpace (S : Finset (ZMod d)) :
    finrank Bit (rowSpace S (b := b)) = S.card * d * b := by
  rw [(rowSpaceEquiv S).finrank_eq]
  simp [Module.finrank_pi_fintype, ZMod.card, mul_assoc]

omit [NeZero d] in
theorem rowSpace_rot {S : Finset (ZMod d)} {X : BinaryState d b}
    (hX : X ∈ rowSpace S) (s : ZMod d) : rot s X ∈ rowSpace S := by
  intro c hc
  funext j l
  exact congrFun (congrFun (hX c hc) (j+s)) l

def fieldRowSpace (S : Finset (ZMod d)) : Submodule (Extension d) (FieldState d b) where
  carrier := {X | ∀ c ∉ S, X c = 0}
  zero_mem' := by simp
  add_mem' := by intro X Y hX hY c hc; simp [hX c hc, hY c hc]
  smul_mem' := by intro a X hX c hc; simp [hX c hc]

theorem fieldEncode_row_zero_iff (X : BinaryState d b) (c : ZMod d) :
    fieldEncode d X c = 0 ↔ X c = 0 := by
  constructor
  · intro h
    funext j l
    have he := congrFun h l
    change rowEncode d (fun j => X c j l) = 0 at he
    have hz := (rowEncode d).injective (he.trans (map_zero (rowEncode d)).symm)
    exact congrFun hz j
  · intro h
    funext l
    change rowEncode d (fun j => X c j l) = 0
    rw [show (fun j => X c j l) = 0 by funext j; exact congrFun (congrFun h j) l]
    exact map_zero _

theorem fieldEncode_mem_rowSpace_iff (X : BinaryState d b) (S : Finset (ZMod d)) :
    fieldEncode d X ∈ fieldRowSpace S ↔ X ∈ rowSpace S := by
  change (∀ c ∉ S, fieldEncode d X c = 0) ↔ ∀ c ∉ S, X c = 0
  simp only [fieldEncode_row_zero_iff]

/-- Extension scalars are actual binary-linear maps in the chosen coordinates. -/
noncomputable def scalarMul (a : Extension d) (X : BinaryState d b) : BinaryState d b :=
  (fieldEncode d).symm (a • fieldEncode d X)

@[simp] theorem fieldEncode_scalarMul (a : Extension d) (X : BinaryState d b) :
    fieldEncode d (scalarMul a X) = a • fieldEncode d X :=
  (fieldEncode d).apply_symm_apply _

noncomputable def scalarEquiv (a : Extension d) (ha : a ≠ 0) :
    BinaryState d b ≃ₗ[Bit] BinaryState d b :=
  (fieldEncode d).trans
    (((LinearEquiv.smulOfNeZero (Extension d) (FieldState d b) a ha).restrictScalars Bit).trans
      (fieldEncode d).symm)

@[simp] theorem scalarEquiv_apply (a : Extension d) (ha : a ≠ 0) (X : BinaryState d b) :
    scalarEquiv a ha X = scalarMul a X := rfl

theorem scalarMul_rot (a : Extension d) (X : BinaryState d b) (s : ZMod d) :
    rot s (scalarMul a X) = scalarMul (phase d s a) (rot s X) := by
  apply (fieldEncode d).injective
  funext c l
  simp only [fieldEncode_rot, fieldEncode_scalarMul, Pi.smul_apply, smul_eq_mul, map_mul]

def ScalarStable (H : Submodule Bit (BinaryState d b)) : Prop :=
  ∀ a X, X ∈ H → scalarMul a X ∈ H

/-- The actual extension-field span, pulled back to the original binary words. -/
noncomputable def scalarHull (L : Submodule Bit (BinaryState d b)) :
    Submodule Bit (BinaryState d b) :=
  Submodule.comap (fieldEncode d).toLinearMap
    (Submodule.restrictScalars Bit
      (Submodule.span (Extension d) (L.map (fieldEncode d).toLinearMap : Set (FieldState d b))))

theorem le_scalarHull (L : Submodule Bit (BinaryState d b)) : L ≤ scalarHull L := by
  intro X hX
  exact Submodule.subset_span ⟨X, hX, rfl⟩

theorem scalarHull_stable (L : Submodule Bit (BinaryState d b)) : ScalarStable (scalarHull L) := by
  intro a X hX
  change fieldEncode d (scalarMul a X) ∈
    Submodule.span (Extension d) (L.map (fieldEncode d).toLinearMap : Set (FieldState d b))
  rw [fieldEncode_scalarMul]
  exact Submodule.smul_mem _ a hX

theorem scalarHull_le_rowSpace {L : Submodule Bit (BinaryState d b)}
    {S : Finset (ZMod d)} (hL : L ≤ rowSpace S) : scalarHull L ≤ rowSpace S := by
  have hh : Submodule.span (Extension d)
      (L.map (fieldEncode d).toLinearMap : Set (FieldState d b)) ≤ fieldRowSpace S := by
    apply Submodule.span_le.mpr
    rintro Y ⟨X, hX, rfl⟩
    exact (fieldEncode_mem_rowSpace_iff X S).mpr (hL hX)
  intro X hX
  exact (fieldEncode_mem_rowSpace_iff X S).mp (hh hX)

theorem ScalarStable.commonPreimage {H : Submodule Bit (BinaryState d b)}
    (hH : ScalarStable H) (Δ : Finset (ZMod d)) : ScalarStable (commonPreimage H Δ) := by
  intro a X hX
  rw [mem_commonPreimage] at hX ⊢
  intro s hs
  rw [scalarMul_rot]
  exact hH _ _ (hX s hs)

theorem ScalarStable.comap_scalarEquiv {H : Submodule Bit (BinaryState d b)}
    (hH : ScalarStable H) (a : Extension d) (ha : a ≠ 0) :
    H.comap (scalarEquiv a ha).toLinearMap = H := by
  ext X
  constructor
  · intro hX
    have hh := hH a⁻¹ (scalarMul a X) hX
    have he : scalarMul a⁻¹ (scalarMul a X) = X := by
      apply (fieldEncode d).injective
      simp only [fieldEncode_scalarMul, smul_smul, inv_mul_cancel₀ ha, one_smul]
    rwa [he] at hh
  · exact hH a X

/-- A direct link identifies two Frobenius-adjusted row vectors. -/
theorem covariance_field_row {κ : Type*} {p : ZMod d → κ} {Δ : Finset (ZMod d)}
    {X : BinaryState d b} (hX : X ∈ covarianceSpace (F := Bit) p Δ)
    {c e : ZMod d} (hce : Link p Δ c e) (l : Fin b) :
    fieldEncode d X c l = phase d (c-e) (fieldEncode d X e l) := by
  have hr : (fun j => X c j l) = fun j => X e (j+(c-e)) l := by
    funext j
    have hh := congrFun (hX c e (.rel _ _ hce) (j+c)) l
    simpa only [add_sub_cancel_right, add_sub_assoc] using hh
  change rowEncode d (fun j => X c j l) = _
  rw [hr]
  exact rowEncode_shift d (fun j => X e j l) (c-e)

/-- The two observations kill every nonloop endpoint, over all lanes together. -/
theorem two_scalar_covariance_zero {κ : Type*} {p : ZMod d → κ}
    {Δ : Finset (ZMod d)} {X : BinaryState d b}
    (hX : X ∈ covarianceSpace (F := Bit) p Δ)
    (hscaled : scalarMul (normalElement d) X ∈ covarianceSpace (F := Bit) p Δ)
    {c e : ZMod d} (hce : Link p Δ c e) (hne : c ≠ e) : X c = 0 ∧ X e = 0 := by
  have hcoeff : normalElement d - phase d (c-e) (normalElement d) ≠ 0 := by
    apply sub_ne_zero.mpr
    intro he
    have hh := phase_normal_injective d (a₁ := 0) (a₂ := c-e) (by simpa using he)
    exact hne (sub_eq_zero.mp hh.symm)
  have he0 : fieldEncode d X e = 0 := by
    funext l
    have h₁ := covariance_field_row hX hce l
    have h₂ := covariance_field_row hscaled hce l
    simp only [fieldEncode_scalarMul, Pi.smul_apply, smul_eq_mul, map_mul] at h₂
    rw [h₁] at h₂
    have hp : (normalElement d - phase d (c-e) (normalElement d)) *
        phase d (c-e) (fieldEncode d X e l) = 0 := by
      rw [sub_mul]
      exact sub_eq_zero.mpr h₂
    have hz := (mul_eq_zero.mp hp).resolve_left hcoeff
    exact (phase d (c-e)).injective (hz.trans (map_zero _).symm)
  have hc0 : fieldEncode d X c = 0 := by
    funext l
    rw [covariance_field_row hX hce l, congrFun he0 l]
    exact map_zero _
  exact ⟨(fieldEncode_row_zero_iff X c).mp hc0, (fieldEncode_row_zero_iff X e).mp he0⟩

omit [NeZero d] in
theorem normalElement_ne_zero : normalElement d ≠ 0 :=
  (IsGalois.normalBasis Bit (Extension d)).ne_zero 1

end SharedDecoders.CapacityClosure
