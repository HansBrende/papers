import SharedDecoders.Model
import Mathlib.Data.Fintype.Card

/-! # Literal mask periods transport through complete factorizations -/

namespace SharedDecoders

section Cancellation

variable {X : Type*}

/-- Commutation pulls back through an injective intertwiner. -/
theorem commute_of_injective_intertwiner {F Q R S : X → X}
    (hF : Function.Injective F)
    (hQ : ∀ x, F (Q x) = R (F x))
    (hS : ∀ x, F (S x) = S (F x))
    (hRS : ∀ x, R (S x) = S (R x)) (x : X) : Q (S x) = S (Q x) := by
  apply hF
  rw [hQ, hS, hRS, ← hQ, ← hS]

/-- An injective composite of endomaps of one finite set makes every factor
injective. This elementary lemma prevents hiding reversibility assumptions. -/
theorem finite_middle_bijective [Finite X] {F L H : X → X}
    (h : Function.Injective (F ∘ L ∘ H)) : Function.Bijective L := by
  have hHi : Function.Injective H := by
    intro x y hxy
    apply h
    simp only [Function.comp_apply, hxy]
  have hHs := Finite.surjective_of_injective hHi
  apply Finite.injective_iff_bijective.mp
  intro x y hxy
  obtain ⟨u, rfl⟩ := hHs x
  obtain ⟨v, rfl⟩ := hHs y
  have huv : u = v := h (congrArg F hxy)
  exact congrArg H huv

end Cancellation

section FixedSets

variable {X : Type*}

/-- The fixed set of a conjugate is exactly the image of the original fixed
set. This is a statement about the actual equivalence, not an assumed source. -/
theorem fixed_conjugate_iff (L : X ≃ X) (T : X → X) (y : X) :
    L (T (L.symm y)) = y ↔ ∃ x, T x = x ∧ L x = y := by
  constructor
  · intro h
    refine ⟨L.symm y, ?_, L.apply_symm_apply y⟩
    apply L.injective
    simpa using h
  · rintro ⟨x, hx, rfl⟩
    simp [hx]

/-- A symmetry commuting with a conjugate preserves the transported fixed
set. No finiteness, linearity or surjectivity of the symmetry is needed. -/
theorem fixed_image_preserved (L : X ≃ X) (T S : X → X)
    (h : ∀ y, L (T (L.symm (S y))) = S (L (T (L.symm y))))
    {y : X} (hy : ∃ x, T x = x ∧ L x = y) :
    ∃ x, T x = x ∧ L x = S y := by
  apply (fixed_conjugate_iff L T (S y)).mp
  rw [h, (fixed_conjugate_iff L T y).mpr hy]

end FixedSets

variable {d : ℕ} {A κ : Type*}

/-- The inverse of an equivariant equivalence is equivariant. -/
theorem equivariant_symm {H : State d A ≃ State d A} (hH : Equivariant H) :
    Equivariant H.symm := by
  intro s X
  apply H.injective
  rw [H.apply_symm_apply, hH, H.apply_symm_apply]

/-- The conjugated column shift is intertwined with the row shift by the
complete remaining map. -/
theorem conjugate_intertwining {F : State d A → State d A}
    (L H : State d A ≃ State d A) (hH : Equivariant H)
    (hexact : ∀ X, F (L (H X)) = swap X) (Y : State d A) :
    F (L (rot 1 (L.symm Y))) = rowRot 1 (F Y) := by
  obtain ⟨X, hX⟩ := H.surjective (L.symm Y)
  have hY : L (H X) = Y := by rw [hX, L.apply_symm_apply]
  rw [← hX, ← hH, hexact, swap_rot, ← hexact, hY]

/-- A literal period of the final receiver mask must commute with the
actual conjugated shift. An arbitrary equivariant outer factor is allowed. -/
theorem literal_period_conjugate
    {p : ZMod d → κ} {U K B : State d A → State d A}
    (L H : State d A ≃ State d A)
    (hU : Equivariant U) (hB : Equivariant B) (hH : Equivariant H)
    (hK : ClassUniform p K)
    (hF : Function.Injective (U ∘ K ∘ B))
    (hexact : ∀ X, U (K (B (L (H X)))) = swap X)
    (s : ZMod d) (hp : ∀ c, p (c + s) = p c) (X : State d A) :
    L (rot 1 (L.symm (rot s X))) = rot s (L (rot 1 (L.symm X))) := by
  let F := U ∘ K ∘ B
  have hFS : ∀ X, F (rot s X) = rot s (F X) := by
    intro Y
    change U (K (B (rot s Y))) = rot s (U (K (B Y)))
    rw [hB, hK.commutes_of_period hp, hU]
  have hi := conjugate_intertwining (F := F) L H hH hexact
  exact commute_of_injective_intertwiner hF hi hFS (fun _ => rfl) X

/-- Exactness on the finite complete state space supplies the reversible
maps and cancellation required by the preceding theorem. -/
theorem literal_period_complete [Finite A] [NeZero d]
    {p : ZMod d → κ} {U K B L H : State d A → State d A}
    (hU : Equivariant U) (hB : Equivariant B) (hH : Equivariant H)
    (hK : ClassUniform p K)
    (hexact : ∀ X, U (K (B (L (H X)))) = swap X) :
    ∃ LE : State d A ≃ State d A,
      (∀ X, LE X = L X) ∧ ∀ s, (∀ c, p (c + s) = p c) →
      ∀ X, LE (rot 1 (LE.symm (rot s X))) = rot s (LE (rot 1 (LE.symm X))) := by
  classical
  let F := U ∘ K ∘ B
  have he : Function.Injective (F ∘ L ∘ H) := by
    intro X Y h
    apply swapEquiv.injective
    change swap X = swap Y
    change U (K (B (L (H X)))) = U (K (B (L (H Y)))) at h
    simpa only [hexact] using h
  have hL : Function.Bijective L := finite_middle_bijective he
  have hHi : Function.Injective H := by
    intro X Y h
    apply he
    simp only [Function.comp_apply, h]
  have hHb := Finite.injective_iff_bijective.mp hHi
  have hFs : Function.Surjective F := by
    intro X
    refine ⟨L (H (swap X)), ?_⟩
    change U (K (B (L (H (swap X))))) = X
    rw [hexact, swap_swap]
  let LE := Equiv.ofBijective L hL
  let HE := Equiv.ofBijective H hHb
  refine ⟨LE, fun _ => rfl, ?_⟩
  intro s hp X
  exact literal_period_conjugate LE HE hU hB hH hK
    (Finite.injective_iff_surjective.mpr hFs) hexact s hp X

end SharedDecoders
