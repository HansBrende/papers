import SharedDecoders.CapacityTripleRows

/-! # The hard source, with arbitrary coupled binary lane blocks

The parameter space and every row are actual spaces over the base field.
The upper bound concerns arbitrary base-linear subcodes, not independently
decoded copies of the extension-field block.
-/

namespace SharedDecoders.CapacityTriple

open Module

variable {F E κ : Type*} [Field F] [Field E] [Algebra F E]
  {s q : ℕ} [NeZero s]

noncomputable def laneRowMap (χ : AddChar (ZMod (3 * s)) E) :
    (Fin q → Fin s → E) →ₗ[F] (ZMod (3 * s) → Fin q → E) where
  toFun x t l := pairRowMap χ (x l) t
  map_add' x y := by funext t l; exact congrFun ((pairRowMap χ).map_add (x l) (y l)) t
  map_smul' a x := by
    funext t l
    exact congrFun (((pairRowMap χ).restrictScalars F).map_smul a (x l)) t

omit [NeZero s] in
theorem laneRowMap_injective (χ : AddChar (ZMod (3 * s)) E) (hχ : Function.Injective χ) :
    Function.Injective (laneRowMap (F := F) (q := q) χ) := by
  intro x y h
  funext l
  apply pairRowMap_injective χ hχ
  exact funext (fun t => congrFun (congrFun h t) l)

noncomputable def laneRowSpace (χ : AddChar (ZMod (3 * s)) E) :
    Submodule F (ZMod (3 * s) → Fin q → E) := LinearMap.range (laneRowMap (F := F) χ)

omit [NeZero s] in
theorem finrank_laneRowSpace [FiniteDimensional F E]
    (χ : AddChar (ZMod (3 * s)) E) (hχ : Function.Injective χ) :
    finrank F (laneRowSpace (F := F) (q := q) χ) = q * s * finrank F E := by
  rw [laneRowSpace, LinearMap.finrank_range_of_inj (laneRowMap_injective (F := F) χ hχ)]
  simp [Module.finrank_pi_fintype, mul_assoc]

noncomputable def sourceMap (χ : AddChar (ZMod (3 * s)) E) :
    (ZMod (3 * s) → Fin q → Fin s → E) →ₗ[F] State (3 * s) (Fin q → E) where
  toFun x c := laneRowMap (F := F) χ (x c)
  map_add' x y := by funext c; exact (laneRowMap (F := F) χ).map_add (x c) (y c)
  map_smul' a x := by funext c; exact (laneRowMap (F := F) χ).map_smul a (x c)

omit [NeZero s] in
theorem sourceMap_injective (χ : AddChar (ZMod (3 * s)) E) (hχ : Function.Injective χ) :
    Function.Injective (sourceMap (F := F) (q := q) χ) := by
  intro x y h
  funext c
  exact laneRowMap_injective (F := F) χ hχ (congrFun h c)

noncomputable def hardSource (χ : AddChar (ZMod (3 * s)) E) :
    Submodule F (State (3 * s) (Fin q → E)) := LinearMap.range (sourceMap (F := F) χ)

theorem finrank_hardSource [FiniteDimensional F E]
    (χ : AddChar (ZMod (3 * s)) E) (hχ : Function.Injective χ) :
    finrank F (hardSource (F := F) (q := q) χ) = (3 * s) * q * s * finrank F E := by
  rw [hardSource, LinearMap.finrank_range_of_inj (sourceMap_injective (F := F) χ hχ)]
  simp [Module.finrank_pi_fintype, ZMod.card, mul_assoc]

omit [NeZero s] in
theorem hardSource_disjoint_views (χ : AddChar (ZMod (3 * s)) E)
    (hχ : Function.Injective χ) (c e : ZMod (3 * s)) (hce : c ≠ e) :
    Disjoint ((hardSource (F := F) (q := q) χ).map (rotLinear F c))
      ((hardSource (F := F) (q := q) χ).map (rotLinear F e)) := by
  rw [Submodule.disjoint_def]
  rintro X ⟨Y, ⟨x, rfl⟩, rfl⟩ ⟨Z, ⟨y, rfl⟩, h⟩
  have hx : x = 0 := by
    funext r l
    exact (rotated_pairRowMap_eq_zero χ hχ (x r l) (y r l) c e hce
      (funext (fun t => congrFun (congrFun (congrFun h.symm r) t) l))).1
  rw [hx, map_zero]
  rfl

omit [NeZero s] in
theorem hardSource_shared (χ : AddChar (ZMod (3 * s)) E)
    (hχ : Function.Injective χ) (p : ZMod (3 * s) → κ) :
    IsSharedCode F p (hardSource (F := F) (q := q) χ) :=
  IsSharedCode.of_disjoint_views (hardSource_disjoint_views χ hχ)

theorem hardSource_triple (χ : AddChar (ZMod (3 * s)) E)
    (hχ : Function.Injective χ) {X : State (3 * s) (Fin q → E)}
    (hX : X ∈ hardSource (F := F) χ) :
    X + rot (s : ZMod (3 * s)) X + rot (2 * (s : ZMod (3 * s))) X = 0 := by
  obtain ⟨x, rfl⟩ := hX
  funext c t l
  exact congrFun (pairRowMap_triple χ hχ (x c l)) t


private theorem finEquiv_apply_nat {n : ℕ} [NeZero n] (i : Fin n) :
    ZMod.finEquiv n i = (i.val : ZMod n) := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
    apply Fin.ext
    change i.val = i.val % (n + 1)
    exact (Nat.mod_eq_of_lt i.isLt).symm

noncomputable def tripleIndex : (Fin 3 × Fin s) ≃ ZMod (3 * s) :=
  finProdFinEquiv.trans (ZMod.finEquiv (3 * s)).toEquiv

@[simp] theorem tripleIndex_zero (j : Fin s) : tripleIndex (0, j) = (j.val : ZMod (3 * s)) := by
  simp [tripleIndex, finProdFinEquiv, finEquiv_apply_nat]

@[simp] theorem tripleIndex_one (j : Fin s) :
    tripleIndex (1, j) = (j.val : ZMod (3 * s)) + (s : ZMod (3 * s)) := by
  simp [tripleIndex, finProdFinEquiv, finEquiv_apply_nat]

@[simp] theorem tripleIndex_two (j : Fin s) :
    tripleIndex (2, j) = (j.val : ZMod (3 * s)) + 2 * (s : ZMod (3 * s)) := by
  simp [tripleIndex, finProdFinEquiv, finEquiv_apply_nat, mul_comm]

theorem hardSource_linear_subcode_bound [FiniteDimensional F E]
    (χ : AddChar (ZMod (3 * s)) E) (hχ : Function.Injective χ)
    (p : ZMod (3 * s) → κ)
    (hp : ∀ c, p (c + (s : ZMod (3 * s))) = p c)
    (C : Submodule F (State (3 * s) (Fin q → E)))
    (hC : C ≤ hardSource (F := F) χ) (hlin : IsLinearSharedCode p C) :
    finrank F C ≤ 2 * s * (q * s * finrank F E) := by
  have hr : ∀ X ∈ C, ∀ c, X c ∈ laneRowSpace (F := F) χ := by
    intro X hX c
    obtain ⟨x, rfl⟩ := hC hX
    exact ⟨x c, rfl⟩
  have hz : ∀ X ∈ C, ∀ j : Fin s,
      X (tripleIndex (0,j)) + X (tripleIndex (1,j)) + X (tripleIndex (2,j)) = 0 := by
    intro X hX j
    simp only [tripleIndex_zero, tripleIndex_one, tripleIndex_two]
    apply hlin.triple_rows_zero hX (s : ZMod (3 * s)) (j.val : ZMod (3 * s))
      (hardSource_triple χ hχ (hC hX)) (hp _)
    have hh := (hp ((j.val : ZMod (3 * s)) + (s : ZMod (3 * s)))).trans (hp _)
    convert hh using 1
    congr 1
    ring
  have hh := triple_row_finrank_bound tripleIndex (laneRowSpace (F := F) χ) C hr hz
  simpa only [Fintype.card_fin, finrank_laneRowSpace (F := F) χ hχ] using hh

end SharedDecoders.CapacityTriple
