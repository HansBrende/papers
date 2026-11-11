import SharedDecoders.CapacityReflectionRecovery
import SharedDecoders.ConstructionFourier
import Mathlib.Algebra.CharP.Two

/-! # The actual common Fourier coordinates of a reflected shared code

Synthesis acts on both physical indices and leaves all lane coordinates in
place. Character independence derives the row/column equation from the one
actual shared decoder, with no restriction on its cross-lane coefficients.
-/

namespace SharedDecoders.CapacityReflection

open Module
open scoped BigOperators

variable {F : Type*} [Field F] {d b : ℕ} [NeZero d]

private theorem finEquiv_apply_nat (i : Fin d) :
    ZMod.finEquiv d i = (i.val : ZMod d) := by
  cases d with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
    apply Fin.ext
    exact (Nat.mod_eq_of_lt i.isLt).symm

def zSynthesis (χ : AddChar (ZMod d) F) : (ZMod d → F) →ₗ[F] (ZMod d → F) where
  toFun x c := ∑ j, χ (j*c)*x j
  map_add' x y := by ext c; simp [mul_add, Finset.sum_add_distrib]
  map_smul' a x := by ext c; simp [Finset.mul_sum, mul_left_comm]

theorem zSynthesis_injective (χ : AddChar (ZMod d) F) (hχ : Function.Injective χ) :
    Function.Injective (zSynthesis χ) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hh : fourierSynthesis χ (fun i => x (ZMod.finEquiv d i)) = 0 := by
    funext c
    have hs : (∑ i : Fin d, χ ((i.val : ZMod d)*c)*x (ZMod.finEquiv d i)) =
        ∑ j : ZMod d, χ (j*c)*x j :=
      Fintype.sum_equiv (ZMod.finEquiv d).toEquiv _ _ (by
        intro i
        change χ ((i.val : ZMod d)*c)*x (ZMod.finEquiv d i) =
          χ (ZMod.finEquiv d i*c)*x (ZMod.finEquiv d i)
        rw [finEquiv_apply_nat])
    exact hs.trans (congrFun hx c)
  have hz := (fourierSynthesis_injective χ hχ) (hh.trans (map_zero _).symm)
  funext j
  obtain ⟨i,rfl⟩ := (ZMod.finEquiv d).surjective j
  exact congrFun hz i

def wordSynthesis (χ : AddChar (ZMod d) F) :
    (ZMod d → Fin b → F) →ₗ[F] (ZMod d → Fin b → F) where
  toFun x c l := ∑ j, χ (j*c)*x j l
  map_add' x y := by ext c l; simp [mul_add, Finset.sum_add_distrib]
  map_smul' a x := by ext c l; simp [Finset.mul_sum, mul_left_comm]

theorem wordSynthesis_injective (χ : AddChar (ZMod d) F) (hχ : Function.Injective χ) :
    Function.Injective (wordSynthesis (b := b) χ) := by
  intro x y hxy
  funext j l
  exact congrFun (zSynthesis_injective χ hχ
    (show zSynthesis χ (fun j => x j l) = zSynthesis χ (fun j => y j l) from
      funext fun c => congrFun (congrFun hxy c) l)) j

noncomputable def wordFourierEquiv (χ : AddChar (ZMod d) F)
    (hχ : Function.Injective χ) :
    (ZMod d → Fin b → F) ≃ₗ[F] (ZMod d → Fin b → F) :=
  (wordSynthesis χ).linearEquivOfInjective (wordSynthesis_injective χ hχ) rfl

def squareSynthesis (χ : AddChar (ZMod d) F) :
    State d (Fin b → F) →ₗ[F] State d (Fin b → F) where
  toFun X r c l := ∑ i, χ (i*r)*(∑ j, χ (j*c)*X i j l)
  map_add' X Y := by ext r c l; simp [mul_add, Finset.sum_add_distrib]
  map_smul' a X := by ext r c l; simp [Finset.mul_sum, mul_left_comm]

theorem squareSynthesis_injective (χ : AddChar (ZMod d) F)
    (hχ : Function.Injective χ) : Function.Injective (squareSynthesis (b := b) χ) := by
  rw [injective_iff_map_eq_zero]
  intro X hX
  have hrow (c : ZMod d) (l : Fin b) :
      (fun i => ∑ j, χ (j*c)*X i j l) = 0 :=
    (zSynthesis_injective χ hχ) ((funext fun r => congrFun (congrFun (congrFun hX r) c) l).trans
      (map_zero _).symm)
  funext i j l
  have hz : (fun j => X i j l) = 0 :=
    (zSynthesis_injective χ hχ) ((funext fun c => congrFun (hrow c l) i).trans (map_zero _).symm)
  exact congrFun hz j

noncomputable def squareFourierEquiv (χ : AddChar (ZMod d) F)
    (hχ : Function.Injective χ) : State d (Fin b → F) ≃ₗ[F] State d (Fin b → F) :=
  (squareSynthesis χ).linearEquivOfInjective (squareSynthesis_injective χ hχ) rfl

def columnMode (χ : AddChar (ZMod d) F) (j : ZMod d) :
    (ZMod d → Fin b → F) →ₗ[F] State d (Fin b → F) where
  toFun v r c l := χ (j*c)*wordSynthesis χ v r l
  map_add' x y := by ext r c l; simp [map_add, mul_add]
  map_smul' a x := by ext r c l; simp [map_smul, mul_left_comm]

theorem rot_squareSynthesis (χ : AddChar (ZMod d) F)
    (X : State d (Fin b → F)) (c : ZMod d) :
    rot c (squareSynthesis χ X) =
      ∑ j, χ (j*c) • columnMode χ j (fun i => X i j) := by
  funext r t l
  simp only [rot_apply, squareSynthesis, LinearMap.coe_mk, AddHom.coe_mk,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, columnMode, wordSynthesis,
    mul_add, χ.map_add_eq_mul]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

noncomputable def frequencyDecoder (χ : AddChar (ZMod d) F)
    (hχ : Function.Injective χ)
    (f : State d (Fin b → F) →ₗ[F] (ZMod d → Fin b → F)) (j : ZMod d) :
    (ZMod d → Fin b → F) →ₗ[F] (ZMod d → Fin b → F) :=
  (wordFourierEquiv χ hχ).symm.toLinearMap.comp (f.comp (columnMode χ j))

theorem frequency_decoder_equation (χ : AddChar (ZMod d) F)
    (hχ : Function.Injective χ)
    (f : State d (Fin b → F) →ₗ[F] (ZMod d → Fin b → F))
    (X : State d (Fin b → F))
    (hdec : ∀ c, squareSynthesis χ X c = f (rot c (squareSynthesis χ X)))
    (j : ZMod d) :
    X j = frequencyDecoder χ hχ f j (fun i => X i j) := by
  have he : wordSynthesis χ (X j) = f (columnMode χ j (fun i => X i j)) := by
    funext r l
    have hh : zSynthesis χ (fun j => wordSynthesis χ (X j) r l) =
        zSynthesis χ (fun j => f (columnMode χ j (fun i => X i j)) r l) := by
      funext c
      have hc := congrFun (congrFun (hdec c) r) l
      rw [rot_squareSynthesis, map_sum] at hc
      simpa only [squareSynthesis, zSynthesis, wordSynthesis, LinearMap.coe_mk,
        AddHom.coe_mk, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hc
    exact congrFun (zSynthesis_injective χ hχ hh) j
  exact (wordFourierEquiv χ hχ).symm_apply_eq.mpr he.symm |>.symm

theorem wordSynthesis_reflect (χ : AddChar (ZMod d) F)
    (x : ZMod d → Fin b → F) (c : ZMod d) (l : Fin b) :
    wordSynthesis χ (fun j => x (-j)) c l = wordSynthesis χ x (-c) l := by
  exact Fintype.sum_equiv (Equiv.neg (ZMod d)) _ _ (by
    intro j
    simp only [Equiv.neg_apply, neg_mul_neg])

theorem squareSynthesis_reflect (χ : AddChar (ZMod d) F)
    (X : State d (Fin b → F)) (r c : ZMod d) (l : Fin b) :
    squareSynthesis χ (fun i j => X i (-j)) r c l = squareSynthesis χ X r (-c) l := by
  change (∑ i, χ (i*r)*wordSynthesis χ (fun j => X i (-j)) c l) =
    ∑ i, χ (i*r)*wordSynthesis χ (X i) (-c) l
  simp_rw [wordSynthesis_reflect]

theorem reflected_fourier_columns (χ : AddChar (ZMod d) F)
    (hχ : Function.Injective χ) (X : State d (Fin b → F))
    (hX : squareSynthesis χ X ∈ source (F := F) d) :
    ∀ i j, X i (-j) = X i j := by
  have he : (fun i j => X i (-j)) = X := by
    apply squareSynthesis_injective χ hχ
    funext r c l
    rw [squareSynthesis_reflect]
    exact congrFun ((hX r).2 c) l
  intro i j
  exact congrFun (congrFun he i) j

theorem neg_ne_self_odd {m : ℕ} (j : ZMod (2*m+1)) (hj : j ≠ 0) : -j ≠ j := by
  let : NeZero j := ⟨hj⟩
  intro he
  have hn := ZMod.val_neg_of_ne_zero j
  have hv := ZMod.val_lt j
  have he' := congrArg ZMod.val he
  omega

theorem sum_reflected_eq_zero_coordinate [CharP F 2] {m : ℕ}
    (x : ZMod (2*m+1) → F) (hx : ∀ j, x (-j)=x j) :
    ∑ j, x j = x 0 := by
  classical
  have hz : ∑ j ∈ (Finset.univ : Finset (ZMod (2*m+1))).erase 0, x j = 0 := by
    apply Finset.sum_involution (fun j _ => -j)
    · intro j _
      rw [hx]
      exact CharTwo.add_self_eq_zero _
    · intro j hj _
      exact neg_ne_self_odd j (Finset.mem_erase.mp hj).1
    · intro j _
      exact neg_neg j
    · intro j hj
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hj ⊢
      exact neg_ne_zero.mpr hj
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : ZMod (2*m+1))), hz, zero_add]

theorem reflected_fourier_zero_column [CharP F 2] {m : ℕ}
    (χ : AddChar (ZMod (2*m+1)) F) (hχ : Function.Injective χ)
    (X : State (2*m+1) (Fin b → F))
    (hX : squareSynthesis χ X ∈ source (F := F) (2*m+1)) :
    ∀ i, X i 0 = 0 := by
  have href := reflected_fourier_columns χ hχ X hX
  intro i
  funext l
  have hs : zSynthesis χ (fun i => ∑ j, X i j l) = 0 := by
    funext r
    have hh := congrFun (hX r).1 l
    simpa only [squareSynthesis, zSynthesis, LinearMap.coe_mk, AddHom.coe_mk,
      mul_zero, χ.map_zero_eq_one, one_mul, Pi.zero_apply] using hh
  have hz := zSynthesis_injective χ hχ (hs.trans (map_zero _).symm)
  have hp := sum_reflected_eq_zero_coordinate (fun j => X i j l)
    (fun j => congrFun (href i j) l)
  exact hp.symm.trans (congrFun hz i)

end SharedDecoders.CapacityReflection
