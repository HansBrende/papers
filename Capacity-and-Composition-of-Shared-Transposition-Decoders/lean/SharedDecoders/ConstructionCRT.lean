import SharedDecoders.ConstructionLiftDimension

/-! # Transfer of the complete lift to the literal cyclic matrix indices -/

namespace SharedDecoders

open Module

variable {F A κ : Type*} [Field F] [AddCommGroup A] [Module F A]
  {m s : ℕ}

def crtStateEquiv (hc : m.Coprime s) :
    State (m * s) A ≃ₗ[F] LiftState (ZMod m) (ZMod s) A where
  toFun X ar bt := X ((ZMod.chineseRemainder hc).symm ar) ((ZMod.chineseRemainder hc).symm bt)
  invFun Y i j := Y (ZMod.chineseRemainder hc i) (ZMod.chineseRemainder hc j)
  left_inv X := by funext i j; simp
  right_inv Y := by funext ar bt; simp
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

@[simp] theorem crtStateEquiv_apply (hc : m.Coprime s) (X : State (m * s) A)
    (ar bt : ZMod m × ZMod s) :
    crtStateEquiv (F := F) hc X ar bt =
      X ((ZMod.chineseRemainder hc).symm ar) ((ZMod.chineseRemainder hc).symm bt) := rfl

theorem crtStateEquiv_rot (hc : m.Coprime s) (c : ZMod (m * s)) (X : State (m * s) A) :
    crtStateEquiv (F := F) hc (rot c X) =
      liftRot (ZMod.chineseRemainder hc c).1 (ZMod.chineseRemainder hc c).2
        (crtStateEquiv (F := F) hc X) := by
  funext ar bt
  change X _ (_ + c) = X _ ((ZMod.chineseRemainder hc).symm (bt + ZMod.chineseRemainder hc c))
  rw [map_add, RingEquiv.symm_apply_apply]

def liftedPartition (hc : m.Coprime s) (p : ZMod s → κ) : ZMod (m * s) → κ :=
  fun c => p (ZMod.chineseRemainder hc c).2

theorem liftedPartition_apply [NeZero (m * s)] (hc : m.Coprime s) (p : ZMod s → κ)
    (c : ZMod (m * s)) : liftedPartition hc p c = p (c.val : ZMod s) := by
  unfold liftedPartition
  conv_lhs => rw [← ZMod.natCast_zmod_val c]
  simp only [map_natCast, Prod.snd_natCast]

theorem liftedPartition_surjective (hc : m.Coprime s) {p : ZMod s → κ}
    (hp : Function.Surjective p) : Function.Surjective (liftedPartition hc p) := by
  intro a
  obtain ⟨c, hc'⟩ := hp a
  refine ⟨(ZMod.chineseRemainder hc).symm (0, c), ?_⟩
  simpa [liftedPartition] using hc'

variable [NeZero m] [NeZero s]

def cyclicLiftCode (hc : m.Coprime s) (C : Submodule F (State s A)) :
    Submodule F (State (m * s) A) :=
  (liftedCode (G := ZMod m) C).comap (crtStateEquiv (F := F) hc).toLinearMap

noncomputable def cyclicLiftEquiv (hc : m.Coprime s) (C : Submodule F (State s A)) :
    cyclicLiftCode hc C ≃ₗ[F] liftedCode (G := ZMod m) C where
  toFun X := ⟨crtStateEquiv (F := F) hc (X : State (m * s) A), X.2⟩
  invFun Y := ⟨(crtStateEquiv (F := F) hc).symm (Y : LiftState (ZMod m) (ZMod s) A), by
    change crtStateEquiv (F := F) hc ((crtStateEquiv (F := F) hc).symm (Y : LiftState (ZMod m) (ZMod s) A)) ∈
      liftedCode (G := ZMod m) C
    simpa only [LinearEquiv.apply_symm_apply] using Y.2⟩
  left_inv X := by apply Subtype.ext; exact (crtStateEquiv (F := F) hc).symm_apply_apply _
  right_inv Y := by apply Subtype.ext; exact (crtStateEquiv (F := F) hc).apply_symm_apply _
  map_add' := by intros; apply Subtype.ext; rfl
  map_smul' := by intros; apply Subtype.ext; rfl

omit [NeZero s] in
theorem IsSharedCode.cyclicLiftCode {p : ZMod s → κ}
    {C : Submodule F (State s A)} (h : IsSharedCode F p C)
    (hc : m.Coprime s) (hm : (m : F) ≠ 0) :
    IsSharedCode F (liftedPartition hc p) (cyclicLiftCode hc C) := by
  have hG : (Fintype.card (ZMod m) : F) ≠ 0 := by simpa [ZMod.card] using hm
  obtain ⟨f, hf⟩ := h.liftedCode hG
  refine ⟨fun a Y i => f a (crtStateEquiv (F := F) hc Y) (ZMod.chineseRemainder hc i), ?_⟩
  intro X hX c
  have hh := hf (crtStateEquiv (F := F) hc X) hX
    (ZMod.chineseRemainder hc c).1 (ZMod.chineseRemainder hc c).2
  funext i
  have hrow := congrFun hh (ZMod.chineseRemainder hc i)
  change X c i = f (p (ZMod.chineseRemainder hc c).2)
    (crtStateEquiv (F := F) hc (rot c X)) (ZMod.chineseRemainder hc i)
  rw [crtStateEquiv_rot]
  simpa only [crtStateEquiv_apply, RingEquiv.symm_apply_apply, Prod.mk.eta]
    using hrow

variable [FiniteDimensional F A]

theorem two_mul_finrank_cyclicLiftCode (hc : m.Coprime s) (hm : (m : F) ≠ 0)
    (C : Submodule F (State s A)) :
    2 * finrank F (cyclicLiftCode hc C) + m * (s * s * finrank F A) =
      (m * s) * (m * s) * finrank F A + 2 * m * finrank F C := by
  rw [(cyclicLiftEquiv hc C).finrank_eq]
  simpa only [ZMod.card] using two_mul_finrank_liftedCode (G := ZMod m)
    (by simpa only [ZMod.card] using hm) C

end SharedDecoders
