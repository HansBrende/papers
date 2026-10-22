import TransposeFollowup.PacketComponentCount
import Mathlib.Data.Fintype.Pigeonhole

/-! Independent binary collisions in deficient packet components. No packet
linearity, output independence, or closure assumption on a promise is used. -/

namespace TransposeFollowup

open Classical
set_option autoImplicit false
universe u

namespace CoordinateSystem

variable {V : Type u} [Fintype V] [DecidableEq V] {B : ℕ} (C : CoordinateSystem V B)

noncomputable def extendComponent (S : Finset V) (a : S → Bool) : V → Bool :=
  fun v => if hv : v ∈ S then a ⟨v, hv⟩ else false

noncomputable def componentBroadcast (S : Finset V) (a : S → Bool) : C.packetIndices S → Bool :=
  fun k => (C.packet k.val).eval (extendComponent S a)

omit [Fintype V] in
theorem eval_eq_componentBroadcast (S : Finset V) (z : V → Bool)
    (k : C.packetIndices S) :
    (C.packet k.val).eval z = C.componentBroadcast S (fun v => z v.val) k := by
  apply (C.packet k.val).eval_congr
  intro v hv
  have hs := ((C.mem_packetIndices S k.val).mp k.property).2 hv
  simp [extendComponent, hs]

structure ComponentCollision (S : Finset V) where
  left : S → Bool
  right : S → Bool
  different : left ≠ right
  same : C.componentBroadcast S left = C.componentBroadcast S right

theorem exists_componentCollision {S : Finset V} (hS : S ∈ C.deficient) :
    Nonempty (C.ComponentCollision S) := by
  have hcard : Fintype.card (C.packetIndices S → Bool) < Fintype.card (S → Bool) := by
    simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]
    exact (pow_lt_pow_iff_right₀ (by decide : 1 < (2 : ℕ))).mpr
      ((C.mem_deficient S).mp hS).2
  obtain ⟨a, a', hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt (C.componentBroadcast S) hcard
  exact ⟨⟨a, a', hne, heq⟩⟩

noncomputable def collision (S : C.deficient) : C.ComponentCollision S.val :=
  (C.exists_componentCollision S.property).some

variable {C} in
def ComponentCollision.select {S : Finset V} (D : C.ComponentCollision S) (t : Bool) : S → Bool :=
  if t then D.right else D.left

variable {C} in
omit [Fintype V] in
theorem ComponentCollision.select_injective {S : Finset V} (D : C.ComponentCollision S) :
    Function.Injective D.select := by
  intro a b h
  cases a <;> cases b <;> simp_all [select, D.different, Ne.symm D.different]

variable {C} in
omit [Fintype V] in
theorem ComponentCollision.broadcast_select {S : Finset V} (D : C.ComponentCollision S)
    (a b : Bool) : C.componentBroadcast S (D.select a) = C.componentBroadcast S (D.select b) := by
  cases a <;> cases b <;> simp [select, D.same]

noncomputable def collisionValue (S : C.deficient) (t : Bool) : V → Bool :=
  extendComponent S.val ((C.collision S).select t)

/-- One collision choice per selected component, with zero outside the family.
K records the components on which the right member is selected. -/
noncomputable def choiceInput (U : Finset (Finset V)) (hU : U ⊆ C.deficient)
    (K : Finset (Finset V)) : V → Bool := fun v =>
  if hv : C.component v ∈ U then
    C.collisionValue ⟨C.component v, hU hv⟩ (decide (C.component v ∈ K)) v
  else false

theorem choiceInput_on (U : Finset (Finset V)) (hU : U ⊆ C.deficient)
    (K : Finset (Finset V)) {S : Finset V} (hS : S ∈ U) (v : S) :
    C.choiceInput U hU K v.val =
      (C.collision ⟨S, hU hS⟩).select (decide (S ∈ K)) v := by
  have he := (C.mem_component_iff ((C.mem_deficient S).mp (hU hS)).1 v.val).mp v.property
  have hm : C.component v.val ∈ U := he.symm ▸ hS
  simp only [choiceInput, dite_eq_left hm]
  have hs : (⟨C.component v.val, hU hm⟩ : C.deficient) = ⟨S, hU hS⟩ := Subtype.ext he
  rw [hs, he]
  simp [collisionValue, extendComponent, v.property]

theorem choiceInput_broadcast (U : Finset (Finset V)) (hU : U ⊆ C.deficient)
    (K L : Finset (Finset V)) :
    C.broadcast (C.choiceInput U hU K) = C.broadcast (C.choiceInput U hU L) := by
  funext k
  by_cases hn : (C.packet k).support.Nonempty
  · obtain ⟨v, hv⟩ := hn
    let S := C.component v
    have hs : (C.packet k).support ⊆ S :=
      C.support_subset_component k (C.component_mem v) hv (C.mem_component_self v)
    by_cases hS : S ∈ U
    · have hk : k ∈ C.packetIndices S := (C.mem_packetIndices S k).mpr ⟨⟨v, hv⟩, hs⟩
      have hK : (fun w : S => C.choiceInput U hU K w.val) =
          (C.collision ⟨S, hU hS⟩).select (decide (S ∈ K)) := by
        funext w; exact C.choiceInput_on U hU K hS w
      have hL : (fun w : S => C.choiceInput U hU L w.val) =
          (C.collision ⟨S, hU hS⟩).select (decide (S ∈ L)) := by
        funext w; exact C.choiceInput_on U hU L hS w
      change (C.packet k).eval _ = (C.packet k).eval _
      rw [C.eval_eq_componentBroadcast S _ ⟨k, hk⟩,
        C.eval_eq_componentBroadcast S _ ⟨k, hk⟩, hK, hL]
      exact congrFun ((C.collision ⟨S, hU hS⟩).broadcast_select _ _) ⟨k, hk⟩
    · apply (C.packet k).eval_congr
      intro w hw
      have he : C.component w = S := (C.support_same_component k hv hw).symm
      simp [choiceInput, he, hS]
  · apply (C.packet k).eval_congr
    intro v hv
    exact False.elim (hn ⟨v, hv⟩)

theorem choiceInput_injective (U : Finset (Finset V)) (hU : U ⊆ C.deficient) :
    Function.Injective (fun K : U.powerset => C.choiceInput U hU K.val) := by
  intro K L heq
  have hm : ∀ S ∈ U, S ∈ K.val ↔ S ∈ L.val := by
    intro S hS
    have hf : (C.collision ⟨S, hU hS⟩).select (decide (S ∈ K.val)) =
        (C.collision ⟨S, hU hS⟩).select (decide (S ∈ L.val)) := by
      funext v
      rw [← C.choiceInput_on U hU K.val hS v, ← C.choiceInput_on U hU L.val hS v]
      exact congrFun heq v.val
    have hb := (C.collision ⟨S, hU hS⟩).select_injective hf
    by_cases hk : S ∈ K.val <;> by_cases hl : S ∈ L.val <;> simp_all
  apply Subtype.ext
  apply Finset.Subset.antisymm
  · intro S hS
    exact (hm S (Finset.mem_powerset.mp K.property hS)).mp hS
  · intro S hS
    exact (hm S (Finset.mem_powerset.mp L.property hS)).mpr hS

theorem choiceInput_insert_outside (U : Finset (Finset V)) (hU : U ⊆ C.deficient)
    (K : Finset (Finset V)) {S : Finset V} (_hS : S ∈ U) {v : V} (hv : v ∉ S) :
    C.choiceInput U hU (insert S K) v = C.choiceInput U hU K v := by
  have he : C.component v ≠ S := by
    intro h; exact hv (h ▸ C.mem_component_self v)
  simp only [choiceInput, Finset.mem_insert, he, false_or]

/-- Transport a selected collision cube through any injective change of
coordinates. If each component change fixes the complement of Q, the
number of selected components is at most the number of coordinates in Q. -/
theorem choiceInput_image_bound {W : Type*} [Fintype W]
    (U : Finset (Finset V)) (hU : U ⊆ C.deficient)
    (f : (V → Bool) → (W → Bool)) (hf : Function.Injective f) (Q : Finset W)
    (hfix : ∀ S ∈ U, ∀ K : Finset (Finset V), ∀ v ∉ Q,
      f (C.choiceInput U hU (insert S K)) v = f (C.choiceInput U hU K) v) :
    U.card ≤ Q.card := by
  have hpres : ∀ K : Finset (Finset V), K ⊆ U → ∀ v ∉ Q,
      f (C.choiceInput U hU K) v = f (C.choiceInput U hU ∅) v := by
    intro K
    induction K using Finset.induction_on with
    | empty => intro _ v _; rfl
    | @insert S K hSK ih =>
      intro hK v hv
      rw [hfix S (hK (Finset.mem_insert_self _ _)) K v hv]
      exact ih (fun T hT => hK (Finset.mem_insert_of_mem hT)) v hv
  let view : U.powerset → (Q → Bool) := fun K v => f (C.choiceInput U hU K.val) v.val
  have hinj : Function.Injective view := by
    intro K L h
    apply C.choiceInput_injective U hU
    apply hf
    funext v
    by_cases hv : v ∈ Q
    · exact congrFun h ⟨v, hv⟩
    · rw [hpres K.val (Finset.mem_powerset.mp K.property) v hv,
        hpres L.val (Finset.mem_powerset.mp L.property) v hv]
  have hcard := Fintype.card_le_of_injective view hinj
  simp only [Fintype.card_coe, Finset.card_powerset, Fintype.card_fun,
    Fintype.card_bool] at hcard
  exact (pow_le_pow_iff_right₀ (by decide : 1 < (2 : ℕ))).mp hcard

end CoordinateSystem
end TransposeFollowup
