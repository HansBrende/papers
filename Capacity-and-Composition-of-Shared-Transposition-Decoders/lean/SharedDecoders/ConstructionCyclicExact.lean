import SharedDecoders.ConstructionLiftExact
import SharedDecoders.ConstructionSeedExact

/-! # Exact agreement kernels on literal cyclic coordinates -/

namespace SharedDecoders

variable {F A κ : Type*} [Field F] [AddCommGroup A] [Module F A]
  {m s : ℕ} [NeZero m] [NeZero s]

omit [NeZero s] in
theorem mem_cyclicLiftCode_iff_full_rule {p : ZMod s → κ}
    (f : κ → State s A →ₗ[F] (ZMod s → A)) (C : Submodule F (State s A))
    (hfull : ∀ Y, Y ∈ C ↔ ∀ c, Y c = f (p c) (rot c Y))
    (hc : m.Coprime s) (hm : (m : F) ≠ 0) (X : State (m*s) A) :
    X ∈ cyclicLiftCode hc C ↔
      ∀ c, X c = cyclicLinearDecoder hc f (liftedPartition hc p c) (rot c X) := by
  have hG : (Fintype.card (ZMod m) : F) ≠ 0 := by simpa only [ZMod.card] using hm
  change crtStateEquiv (F := F) hc X ∈ liftedCode (G := ZMod m) C ↔ _
  rw [mem_liftedCode_iff_full_rule (fun j => f j) C hfull hG]
  constructor
  · intro h c
    have hh := h (ZMod.chineseRemainder hc c).1 (ZMod.chineseRemainder hc c).2
    funext i
    have hi := congrFun hh (ZMod.chineseRemainder hc i)
    change X c i = liftedDecoder (F := F) (fun j => f j)
      (p (ZMod.chineseRemainder hc c).2) (crtStateEquiv (F := F) hc (rot c X))
      (ZMod.chineseRemainder hc i)
    rw [crtStateEquiv_rot]
    simpa only [crtStateEquiv_apply, RingEquiv.symm_apply_apply, Prod.mk.eta] using hi
  · intro h u v
    have hh := h ((ZMod.chineseRemainder hc).symm (u,v))
    funext ar
    have hi := congrFun hh ((ZMod.chineseRemainder hc).symm ar)
    change X ((ZMod.chineseRemainder hc).symm (u,v))
      ((ZMod.chineseRemainder hc).symm ar) = liftedDecoder (F := F) (fun j => f j)
      (p v) (liftRot u v (crtStateEquiv (F := F) hc X)) ar
    change X _ _ = liftedDecoder (F := F) (fun j => f j)
      (p (ZMod.chineseRemainder hc ((ZMod.chineseRemainder hc).symm (u,v))).2)
      (crtStateEquiv (F := F) hc (rot ((ZMod.chineseRemainder hc).symm (u,v)) X))
      (ZMod.chineseRemainder hc ((ZMod.chineseRemainder hc).symm ar)) at hi
    rw [crtStateEquiv_rot] at hi
    simpa only [RingEquiv.apply_symm_apply] using hi

theorem binarySeed_full_rule (Y : State 6 (ZMod 2)) :
    Y ∈ binarySeedCode ↔ ∀ c, Y c =
      SwapRigidity.aperiodicDec (SwapRigidity.aperiodicCls c) (rot c Y) := by
  rw [← binarySeedDefect_ker, LinearMap.mem_ker]
  constructor
  · intro h c
    funext r
    exact sub_eq_zero.mp (congrFun (congrFun h c) r)
  · intro h
    funext c r
    exact sub_eq_zero.mpr (congrFun (h c) r)

def binaryCyclicDefect (hc : m.Coprime 6) :
    State (m*6) (ZMod 2) →ₗ[ZMod 2] State (m*6) (ZMod 2) :=
  LinearMap.id - LinearMap.pi (fun c =>
    (cyclicLinearDecoder hc SwapRigidity.aperiodicDec
      (liftedPartition hc SwapRigidity.aperiodicCls c)).comp (rotLinear (ZMod 2) c))

theorem binaryCyclicDefect_ker (hc : m.Coprime 6) :
    (binaryCyclicDefect hc).ker = binaryCyclicCode hc := by
  ext X
  rw [LinearMap.mem_ker]
  change _ ↔ X ∈ cyclicLiftCode hc binarySeedCode
  rw [mem_cyclicLiftCode_iff_full_rule SwapRigidity.aperiodicDec binarySeedCode
    binarySeed_full_rule hc (binary_cast_ne_zero_of_coprime_six hc)]
  constructor
  · intro h c
    funext r
    exact sub_eq_zero.mp (congrFun (congrFun h c) r)
  · intro h
    funext c r
    exact sub_eq_zero.mpr (congrFun (h c) r)

theorem finrank_binaryCyclicDefect_ker (hc : m.Coprime 6) :
    Module.finrank (ZMod 2) (binaryCyclicDefect hc).ker = 18*m*m + 7*m := by
  rw [binaryCyclicDefect_ker, finrank_binaryCyclicCode]

def binaryCyclicLaneDefect (hc : m.Coprime 6) (b : ℕ) :
    (Fin b → State (m*6) (ZMod 2)) →ₗ[ZMod 2] (Fin b → State (m*6) (ZMod 2)) :=
  LinearMap.pi (fun i => (binaryCyclicDefect hc).comp (LinearMap.proj i))

def binaryCyclicLaneKernelEquiv (hc : m.Coprime 6) (b : ℕ) :
    (binaryCyclicLaneDefect hc b).ker ≃ₗ[ZMod 2] (Fin b → binaryCyclicCode hc) where
  toFun X i := ⟨X.1 i, by
    rw [← binaryCyclicDefect_ker, LinearMap.mem_ker]
    exact congrFun (LinearMap.mem_ker.mp X.2) i⟩
  invFun X := ⟨fun i => X i, by
    apply LinearMap.mem_ker.mpr
    funext i
    have hi : (X i : State (m*6) (ZMod 2)) ∈ (binaryCyclicDefect hc).ker := by
      simpa only [binaryCyclicDefect_ker] using (X i).2
    exact LinearMap.mem_ker.mp hi⟩
  left_inv X := rfl
  right_inv X := rfl
  map_add' X Y := rfl
  map_smul' a X := rfl

theorem finrank_binaryCyclicLaneDefect_ker (hc : m.Coprime 6) (b : ℕ) :
    Module.finrank (ZMod 2) (binaryCyclicLaneDefect hc b).ker = b*(18*m*m+7*m) := by
  rw [(binaryCyclicLaneKernelEquiv hc b).finrank_eq]
  simp only [Module.finrank_pi_fintype, finrank_binaryCyclicCode, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul]

end SharedDecoders
