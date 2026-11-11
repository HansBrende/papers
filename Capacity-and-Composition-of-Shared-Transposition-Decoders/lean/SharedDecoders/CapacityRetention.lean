import SharedDecoders.ConstructionSymmetric
import SharedDecoders.CapacityRetentionAlgebra

/-! # Symmetric directions retained by a deterministic shared source -/

namespace SharedDecoders

open Module
attribute [local instance] Classical.propDecidable

variable {F A I : Type*} [Field F] [AddCommGroup A] [Module F A]

def antisym : (I → I → A) →ₗ[F] (I → I → A) where
  toFun X i j := X i j - X j i
  map_add' X Y := by ext i j; simp only [Pi.add_apply]; abel
  map_smul' a X := by ext i j; exact (smul_sub a _ _).symm

@[simp] theorem antisym_apply (X : I → I → A) (i j : I) :
    antisym (F := F) X i j = X i j - X j i := rfl

theorem ker_antisym : LinearMap.ker (antisym (F := F) (A := A) (I := I)) = symmetricSpace := by
  ext X
  change (fun i j => X i j - X j i) = 0 ↔ ∀ i j, X i j = X j i
  constructor
  · intro h i j
    exact sub_eq_zero.mp (congrFun (congrFun h i) j)
  · intro h
    ext i j
    exact sub_eq_zero.mpr (h i j)

theorem twice_rank_antisym_add_diagonal [Fintype I] [FiniteDimensional F A] :
    2 * finrank F (LinearMap.range (antisym (F := F) (A := A) (I := I))) +
      Fintype.card I * finrank F A = Fintype.card I * Fintype.card I * finrank F A := by
  have hn := (antisym (F := F) (A := A) (I := I)).finrank_range_add_finrank_ker
  rw [ker_antisym] at hn
  have hS := two_mul_finrank_symmetricSpace (F := F) (A := A) (I := I)
  have hd : finrank F (I → I → A) = Fintype.card I * Fintype.card I * finrank F A := by
    simp [Module.finrank_pi_fintype, mul_assoc]
  rw [hd] at hn
  nlinarith

variable {d : ℕ} {κ : Type*}

/-- Actual decoder equality makes the covered rows of a rotated symmetric
source symmetric again. Decoder linearity is not used. -/
theorem IsSharedCode.rotated_symmetric_row {p : ZMod d → κ}
    {C : Submodule F (State d A)} (hC : IsSharedCode F p C)
    {Y : State d A} (hY : Y ∈ C) (hS : Y ∈ symmetricSpace (F := F))
    {s c : ZMod d} (hrot : rot s Y ∈ C) (hp : p c = p (c + s)) :
    antisym (F := F) (rot s Y) c = 0 := by
  obtain ⟨f, hf⟩ := hC
  have hrow : (rot s Y) c = Y (c + s) := by
    rw [hf _ hrot c, hf _ hY (c + s), hp, rot_rot]
  funext j
  change rot s Y c j - Y j (c + s) = 0
  rw [congrFun hrow j, hS (c + s) j, sub_self]

noncomputable def coveredRows [NeZero d] (p : ZMod d → κ) (s : ZMod d) : Finset (ZMod d) := by
  classical
  exact Finset.univ.filter (fun c => p c = p (c + s))

noncomputable def rowMask (Z : Finset I) : (I → I → A) →ₗ[F] (I → I → A) := by
  classical
  exact
    { toFun := fun X i j => if i ∈ Z then X i j else 0
      map_add' := fun X Y => by ext i j; by_cases h : i ∈ Z <;> simp [h]
      map_smul' := fun a X => by ext i j; by_cases h : i ∈ Z <;> simp [h] }

@[simp] theorem rowMask_apply (Z : Finset I) (X : I → I → A) (i j : I) :
    rowMask (F := F) Z X i j = if i ∈ Z then X i j else 0 := rfl

def restrictSquare (U : Finset I) : (I → I → A) →ₗ[F] (U → U → A) where
  toFun X i j := X i.val j.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def uncoveredRows [Fintype I] {J : Type*} (Z : J → Finset I) : Finset I := by
  classical
  exact Finset.univ.filter (fun i => ∀ j, i ∉ Z j)

/-- Observing several sets of rows of an antisymmetric image leaves at most
the antisymmetric image supported on the jointly uncovered square. -/
theorem antisym_cover_bound [Fintype I] [FiniteDimensional F A]
    {J : Type*} [Fintype J] (C : Submodule F (I → I → A)) (Z : J → Finset I) :
    let U := uncoveredRows Z
    finrank F C ≤ finrank F (C ⊓ symmetricSpace : Submodule F (I → I → A)) +
      (∑ j, finrank F (C.map ((rowMask (Z j)).comp (antisym (F := F))))) +
      finrank F (LinearMap.range (antisym (F := F) (A := A) (I := U))) := by
  classical
  let U := uncoveredRows Z
  let V := C.map (antisym (F := F))
  let image (j : J) := C.map ((rowMask (Z j)).comp (antisym (F := F)))
  let f : V →ₗ[F] ((∀ j, image j) ×
      LinearMap.range (antisym (F := F) (A := A) (I := U))) :=
    { toFun := fun Y =>
        (fun j => ⟨rowMask (F := F) (Z j) Y.val, by
          obtain ⟨X, hX, he⟩ := Y.property
          exact ⟨X, hX, congrArg (rowMask (F := F) (Z j)) he⟩⟩,
        ⟨restrictSquare (F := F) U Y.val, by
          obtain ⟨X, _, he⟩ := Y.property
          refine ⟨restrictSquare (F := F) U X, ?_⟩
          exact congrArg (restrictSquare (F := F) U) he⟩)
      map_add' := fun X Y => by
        apply Prod.ext
        · funext j
          apply Subtype.ext
          exact (rowMask (F := F) (Z j)).map_add X.val Y.val
        · apply Subtype.ext; rfl
      map_smul' := fun a X => by
        apply Prod.ext
        · funext j
          apply Subtype.ext
          exact (rowMask (F := F) (Z j)).map_smul a X.val
        · apply Subtype.ext; rfl }
  have hf : Function.Injective f := by
    intro X Y h
    have hmask (j : J) : rowMask (F := F) (Z j) X.val = rowMask (F := F) (Z j) Y.val :=
      congrArg Subtype.val (congrFun (congrArg Prod.fst h) j)
    have hsquare : restrictSquare (F := F) U X.val = restrictSquare (F := F) U Y.val :=
      congrArg Subtype.val (congrArg Prod.snd h)
    have hrow {i : I} (hi : i ∉ U) (k : I) : X.val i k = Y.val i k := by
      have hex : ∃ j, i ∈ Z j := by simpa [U, uncoveredRows] using hi
      obtain ⟨j, hj⟩ := hex
      simpa [rowMask, hj] using congrFun (congrFun (hmask j) i) k
    have hskew (Y : V) (i k : I) : Y.val i k = -Y.val k i := by
      obtain ⟨X, _, he⟩ := Y.property
      rw [← he]
      simp [antisym_apply, neg_sub]
    apply Subtype.ext
    funext i k
    by_cases hi : i ∈ U
    · by_cases hk : k ∈ U
      · exact congrFun (congrFun hsquare ⟨i, hi⟩) ⟨k, hk⟩
      · rw [hskew X, hskew Y, hrow hk]
    · exact hrow hi k
  have hd := LinearMap.finrank_le_finrank_of_injective hf
  simp only [Module.finrank_prod, Module.finrank_pi_fintype] at hd
  have hn := finrank_map_add_inf_ker C (antisym (F := F))
  rw [ker_antisym] at hn
  dsimp [V, image] at hd
  change finrank F C ≤ finrank F (C ⊓ symmetricSpace : Submodule F (I → I → A)) +
    (∑ j, finrank F (C.map ((rowMask (Z j)).comp (antisym (F := F))))) +
    finrank F (LinearMap.range (antisym (F := F) (A := A) (I := U)))
  omega

variable [NeZero d] [FiniteDimensional F A]

/-- Local cost uses the actual retained symmetric space and its translated
sum. Replacing it by a gcd bound is a separate, weaker numerical step. -/
theorem IsSharedCode.covered_rows_rank {p : ZMod d → κ}
    {C : Submodule F (State d A)} (hC : IsSharedCode F p C) (s : ZMod d) :
    finrank F (C.map ((rowMask (coveredRows p s)).comp (antisym (F := F)))) +
      finrank F ((C ⊓ symmetricSpace) ⊔
        (C ⊓ symmetricSpace).map (rotLinear F s) : Submodule F (State d A)) ≤
      d * d * finrank F A := by
  classical
  let U := C ⊓ symmetricSpace
  let H := U.map (rotLinear F s)
  let f := (rowMask (F := F) (A := A) (coveredRows p s)).comp antisym
  have hkill : U ⊔ (C ⊓ H) ≤ LinearMap.ker f := by
    apply sup_le
    · intro X hX
      apply LinearMap.mem_ker.mpr
      have hz : antisym (F := F) X = 0 := by
        apply LinearMap.mem_ker.mp
        rw [ker_antisym]
        exact hX.2
      change rowMask (F := F) _ (antisym (F := F) X) = 0
      rw [hz, map_zero]
    · intro X hX
      obtain ⟨Y, hY, rfl⟩ := hX.2
      apply LinearMap.mem_ker.mpr
      ext c j
      simp only [f, LinearMap.comp_apply, rotLinear_apply, rowMask_apply, Pi.zero_apply]
      split_ifs with hc
      · have hp := (Finset.mem_filter.mp hc).2
        exact congrFun (hC.rotated_symmetric_row hY.1 hY.2 hX.1 hp) j
      · rfl
  have hh := restricted_rank_ambient_bound C U H f inf_le_left hkill
  simpa only [finrank_state] using hh

/-- An exact retained-space invoice, stronger than replacing each summand by
the generic symmetry loss and gcd costs. Repeated shifts are permitted. -/
theorem IsSharedCode.intrinsic_retention_bound {p : ZMod d → κ}
    {C : Submodule F (State d A)} (hC : IsSharedCode F p C)
    {J : Type*} [Fintype J] (t : J → ZMod d) :
    let U := uncoveredRows (fun j => coveredRows p (t j))
    2 * finrank F C + U.card * finrank F A ≤
      2 * finrank F (C ⊓ symmetricSpace : Submodule F (State d A)) +
      2 * ∑ j, (d * d * finrank F A -
        finrank F ((C ⊓ symmetricSpace) ⊔
          (C ⊓ symmetricSpace).map (rotLinear F (t j)) : Submodule F (State d A))) +
      U.card * U.card * finrank F A := by
  classical
  let U := uncoveredRows (fun j => coveredRows p (t j))
  have hcover := antisym_cover_bound C (fun j => coveredRows p (t j))
  have hrank := twice_rank_antisym_add_diagonal (F := F) (A := A) (I := U)
  simp only [Fintype.card_coe] at hrank
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
    Nat.le_sub_of_add_le (hC.covered_rows_rank (t j)))
  change finrank F C ≤ finrank F (C ⊓ symmetricSpace : Submodule F (State d A)) +
    (∑ j, finrank F (C.map ((rowMask (coveredRows p (t j))).comp (antisym (F := F))))) +
    finrank F (LinearMap.range (antisym (F := F) (A := A) (I := U))) at hcover
  change 2 * finrank F C + U.card * finrank F A ≤ _
  nlinarith

end SharedDecoders
