import SharedDecoders.CapacityTP

/-!
# The invariant ambient of a common translated source

Normalized rows are constant on the connected components of the translate-link
relation. This gives an exact dimension and, importantly, an ambient preserved
by every column rotation. The latter permits a fresh Grassmann inequality at
each nested intersection, rather than repeatedly using the full matrix space.
-/

namespace SharedDecoders

open Module

variable {F A κ : Type*} [Field F] [AddCommGroup A] [Module F A] {d : ℕ}

abbrev LinkComponent (p : ZMod d → κ) (Δ : Finset (ZMod d)) :=
  Quotient (Relation.EqvGen.setoid (Link p Δ))

def covarianceSpace (p : ZMod d → κ) (Δ : Finset (ZMod d)) :
    Submodule F (State d A) where
  carrier := {X | ∀ c e, Relation.EqvGen (Link p Δ) c e →
    ∀ j, X c (j - c) = X e (j - e)}
  zero_mem' := by simp
  add_mem' := by
    intro X Y hX hY c e hce j
    exact congrArg₂ (· + ·) (hX c e hce j) (hY c e hce j)
  smul_mem' := by
    intro a X hX c e hce j
    exact congrArg (a • ·) (hX c e hce j)

@[simp] theorem mem_covarianceSpace {p : ZMod d → κ} {Δ : Finset (ZMod d)}
    {X : State d A} : X ∈ covarianceSpace (F := F) p Δ ↔
    ∀ c e, Relation.EqvGen (Link p Δ) c e →
      ∀ j, X c (j - c) = X e (j - e) := Iff.rfl

theorem covarianceSpace_rot {p : ZMod d → κ} {Δ : Finset (ZMod d)}
    {X : State d A} (hX : X ∈ covarianceSpace (F := F) p Δ) (s : ZMod d) :
    rot s X ∈ covarianceSpace (F := F) p Δ := by
  intro c e hce j
  have h := hX c e hce (j + s)
  simpa only [rot_apply, add_sub_right_comm] using h

theorem IsSharedCode.commonPreimage_le_covariance {p : ZMod d → κ}
    {C : Submodule F (State d A)} (h : IsSharedCode F p C)
    (Δ : Finset (ZMod d)) : commonPreimage C Δ ≤ covarianceSpace p Δ := by
  intro X hX c e hce
  have hx := mem_commonPreimage.mp hX
  induction hce with
  | rel c e hce =>
      obtain ⟨hp, s, hs, t, ht, hsum⟩ := hce
      intro j
      have key := h.row_eq_of_rot_mem (hx s hs) (hx t ht) hp hsum (j - c - s)
      have ht' : j - c - s + t = j - e := by
        have : c + s - t = e := (sub_eq_iff_eq_add).2 (by simpa [add_comm] using hsum)
        rw [← this]
        abel
      rw [sub_add_cancel, ht'] at key
      exact key.symm
  | refl _ => intro j; rfl
  | symm _ _ _ ih => intro j; exact (ih j).symm
  | trans _ _ _ _ _ ih₁ ih₂ => intro j; exact (ih₁ j).trans (ih₂ j)

noncomputable def covarianceEquiv (p : ZMod d → κ) (Δ : Finset (ZMod d)) :
    covarianceSpace (F := F) (A := A) p Δ ≃ₗ[F]
      (LinkComponent p Δ → ZMod d → A) where
  toFun X q j := Quotient.lift (fun c => (X : State d A) c (j - c))
    (fun c e hce => X.2 c e hce j) q
  invFun Y := ⟨fun c j => Y (Quotient.mk _ c) (j + c), by
    intro c e hce j
    simp only [sub_add_cancel]
    rw [Quotient.sound hce]⟩
  left_inv X := by
    apply Subtype.ext
    funext c j
    simp
  right_inv Y := by
    funext q j
    induction q using Quotient.inductionOn with
    | h c => simp
  map_add' X Y := by
    funext q j
    induction q using Quotient.inductionOn with
    | h c => rfl
  map_smul' a X := by
    funext q j
    induction q using Quotient.inductionOn with
    | h c => rfl

variable [NeZero d] [FiniteDimensional F A]

noncomputable instance linkComponentFintype (p : ZMod d → κ)
    (Δ : Finset (ZMod d)) : Fintype (LinkComponent p Δ) :=
  Fintype.ofFinite _

noncomputable def componentCount (p : ZMod d → κ) (Δ : Finset (ZMod d)) : ℕ :=
  Fintype.card (LinkComponent p Δ)

theorem finrank_covarianceSpace (p : ZMod d → κ) (Δ : Finset (ZMod d)) :
    finrank F (covarianceSpace (F := F) (A := A) p Δ) =
      d * componentCount p Δ * finrank F A := by
  rw [(covarianceEquiv (F := F) (A := A) p Δ).finrank_eq]
  simp [Module.finrank_pi_fintype, componentCount, ZMod.card, mul_left_comm, mul_assoc]

theorem IsSharedCode.commonPreimage_finrank_le {p : ZMod d → κ}
    {C : Submodule F (State d A)} (h : IsSharedCode F p C)
    (Δ : Finset (ZMod d)) : finrank F (commonPreimage C Δ) ≤
      d * componentCount p Δ * finrank F A := by
  exact (Submodule.finrank_mono (h.commonPreimage_le_covariance Δ)).trans_eq
    (finrank_covarianceSpace p Δ)

/-- The translate bound with the actual component count, without a separately
chosen transversal. -/
theorem IsSharedCode.component_finrank_le {p : ZMod d → κ}
    {C : Submodule F (State d A)} (h : IsSharedCode F p C)
    {Δ : Finset (ZMod d)} (hΔ : Δ.Nonempty) :
    Δ.card * finrank F C ≤ (Δ.card - 1) * (d * d * finrank F A) +
      d * componentCount p Δ * finrank F A := by
  have hcount := SwapRigidity.card_mul_finrank_add_le_iInf_comap Δ C
    (fun s => rotLinear F s)
  rw [finrank_state] at hcount
  change Δ.card * finrank F C + d * d * finrank F A ≤
    Δ.card * (d * d * finrank F A) + finrank F (commonPreimage C Δ) at hcount
  have hdim := h.commonPreimage_finrank_le Δ
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hΔ.card_pos.ne'
  rw [hk, Nat.succ_eq_add_one, add_mul, one_mul] at hcount
  rw [hk, Nat.succ_eq_add_one, Nat.add_sub_cancel]
  nlinarith

end SharedDecoders
