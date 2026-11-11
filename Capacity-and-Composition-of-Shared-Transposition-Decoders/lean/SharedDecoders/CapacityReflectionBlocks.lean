import SharedDecoders.CapacityReflectionFourier

/-! # Actual paired-frequency compression and descending reconstruction

Every nonzero frequency is explicitly covered by a signed positive index.
The column reconstruction map is constructed from this coordinate injection.
It produces the block maps used by the existing recovery theorem.
-/

namespace SharedDecoders.CapacityReflection

open Module
open scoped BigOperators

variable {F : Type*} [Field F] {m b : ℕ}

def positiveIndex (a : Fin m) : ZMod (2*m+1) := ((a.val+1 : ℕ) : ZMod (2*m+1))

def signedIndex (a : Fin m) (s : Fin 2) : ZMod (2*m+1) :=
  if s=0 then positiveIndex a else -positiveIndex a

theorem signedIndex_covers (j : ZMod (2*m+1)) (hj : j ≠ 0) :
    ∃ a : Fin m, ∃ s : Fin 2, signedIndex a s = j := by
  have hp : 0 < min j.val (-j).val :=
    lt_min (ZMod.val_pos.mpr hj) (ZMod.val_pos.mpr (neg_ne_zero.mpr hj))
  have hv : (pairRep j hj).val+1 = min j.val (-j).val := by
    simp only [pairRep]
    omega
  by_cases hle : j.val ≤ (-j).val
  · refine ⟨pairRep j hj,0,?_⟩
    simp only [signedIndex, ite_true, positiveIndex, hv, min_eq_left hle,
      ZMod.natCast_zmod_val]
  · refine ⟨pairRep j hj,1,?_⟩
    simp only [signedIndex, one_ne_zero, ite_false, positiveIndex, hv,
      min_eq_right (le_of_not_ge hle), ZMod.natCast_zmod_val, neg_neg]

def zeroWord : Submodule F (ZMod (2*m+1) → Fin b → F) :=
  LinearMap.ker (LinearMap.proj 0)

def pairRead : zeroWord (F := F) (m := m) (b := b) →ₗ[F]
    (Fin m → Fin 2 → Fin b → F) where
  toFun v a s := v.val (signedIndex a s)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem pairRead_injective : Function.Injective (pairRead (F := F) (m := m) (b := b)) := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  apply Subtype.ext
  funext j
  by_cases hj : j=0
  · subst j
    exact v.property
  · obtain ⟨a,s,rfl⟩ := signedIndex_covers j hj
    exact congrFun (congrFun hv a) s

noncomputable def pairInsert :
    (Fin m → Fin 2 → Fin b → F) →ₗ[F] (ZMod (2*m+1) → Fin b → F) :=
  (zeroWord (F := F) (m := m) (b := b)).subtype.comp pairRead.leftInverse

theorem pairInsert_read (v : ZMod (2*m+1) → Fin b → F) (hv : v 0=0) :
    pairInsert (fun a s => v (signedIndex a s)) = v := by
  have hh := LinearMap.leftInverse_apply_of_inj
    (LinearMap.ker_eq_bot.mpr (pairRead_injective (F := F) (m := m) (b := b)))
    (⟨v,hv⟩ : zeroWord)
  exact congrArg Subtype.val hh

def compress : State (2*m+1) (Fin b → F) →ₗ[F]
    (Fin m → Fin m → Fin 2 → Fin b → F) where
  toFun X a c s := X (signedIndex a s) (positiveIndex c)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Field F] in
theorem column_signedIndex (X : State (2*m+1) (Fin b → F))
    (hX : ∀ i j, X i (-j)=X i j) (a : Fin m) (s : Fin 2) :
    (fun i => X i (signedIndex a s)) = fun i => X i (positiveIndex a) := by
  funext i
  simp only [signedIndex]
  split
  · rfl
  · exact hX i _

noncomputable def blockRowMap
    (B : ZMod (2*m+1) → (ZMod (2*m+1) → Fin b → F) →ₗ[F]
      (ZMod (2*m+1) → Fin b → F)) (a c : Fin m) :
    (Fin m → Fin 2 → Fin b → F) →ₗ[F] (Fin 2 → Fin b → F) where
  toFun v s := B (signedIndex a s) (pairInsert v) (positiveIndex c)
  map_add' x y := by ext s l; simp only [map_add, Pi.add_apply]
  map_smul' k x := by ext s l; simp only [map_smul, Pi.smul_apply, RingHom.id_apply]

noncomputable def blockCoefficients
    (B : ZMod (2*m+1) → (ZMod (2*m+1) → Fin b → F) →ₗ[F]
      (ZMod (2*m+1) → Fin b → F)) (a c k : Fin m) :
    (Fin 2 → Fin b → F) →ₗ[F] (Fin 2 → Fin b → F) :=
  (blockRowMap B a c).comp (LinearMap.single F (fun _ : Fin m => Fin 2 → Fin b → F) k)

theorem compressed_mem_blockAgreement
    (B : ZMod (2*m+1) → (ZMod (2*m+1) → Fin b → F) →ₗ[F]
      (ZMod (2*m+1) → Fin b → F))
    (X : State (2*m+1) (Fin b → F))
    (hz : ∀ i, X i 0=0) (hs : ∀ i j, X i (-j)=X i j)
    (he : ∀ j, X j=B j (fun i => X i j)) :
    compress X ∈ blockAgreement (LinearEquiv.refl F _) (blockCoefficients B) := by
  have hrow : X 0=0 := by
    rw [he 0, show (fun i => X i 0)=0 from funext hz, map_zero]
  intro a c
  change compress X a c = ∑ k, blockRowMap B a c (Pi.single k (compress X k a))
  rw [← map_sum, LinearMap.sum_single_apply]
  funext s
  change X (signedIndex a s) (positiveIndex c) =
    B (signedIndex a s) (pairInsert (fun k t => X (signedIndex k t) (positiveIndex a)))
      (positiveIndex c)
  rw [pairInsert_read (fun i => X i (positiveIndex a))
    (congrFun hrow (positiveIndex a))]
  rw [he (signedIndex a s), column_signedIndex X hs a s]

theorem reflected_equations_finrank_le
    (B : ZMod (2*m+1) → (ZMod (2*m+1) → Fin b → F) →ₗ[F]
      (ZMod (2*m+1) → Fin b → F))
    (C : Submodule F (State (2*m+1) (Fin b → F)))
    (hz : ∀ X ∈ C, ∀ i, X i 0=0)
    (hs : ∀ X ∈ C, ∀ i j, X i (-j)=X i j)
    (he : ∀ X ∈ C, ∀ j, X j=B j (fun i => X i j)) :
    finrank F C ≤ b*m*(m+1) := by
  let P : C →ₗ[F] blockAgreement (LinearEquiv.refl F _) (blockCoefficients B) :=
    { toFun X := ⟨compress X, compressed_mem_blockAgreement B X (hz X X.property)
        (hs X X.property) (he X X.property)⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  have hinj : Function.Injective P := by
    rw [injective_iff_map_eq_zero]
    intro X hX
    have hcomp : compress X.val=0 := congrArg Subtype.val hX
    have hrow : X.val 0=0 := by
      rw [he X X.property 0, show (fun i => X.val i 0)=0 from funext (hz X X.property), map_zero]
    apply Subtype.ext
    funext i j
    by_cases hi : i=0
    · subst i
      exact congrFun hrow j
    by_cases hj : j=0
    · subst j
      exact hz X X.property i
    obtain ⟨a,s,rfl⟩ := signedIndex_covers i hi
    obtain ⟨c,t,rfl⟩ := signedIndex_covers j hj
    have hcol := congrFun (column_signedIndex X.val (hs X X.property) c t) (signedIndex a s)
    exact hcol.trans (congrFun (congrFun (congrFun hcomp a) c) s)
  exact (LinearMap.finrank_le_finrank_of_injective hinj).trans
    (reflected_block_finrank_bound (blockCoefficients B))

end SharedDecoders.CapacityReflection
