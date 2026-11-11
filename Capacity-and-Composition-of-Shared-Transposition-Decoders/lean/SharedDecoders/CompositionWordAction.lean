import SharedDecoders.CompositionComplete
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.Group.TypeTags.Finite

/-!
# Word permutations acting on complete matrix states

This module supplies the literal coordinate bridge used by the balance theorem.
A single permutation of a scalar word acts identically on every row and lane;
the other complete maps need not respect lanes.
-/

namespace SharedDecoders

variable {d b : ℕ} {S : Type*}

abbrev ScalarWord (d : ℕ) (S : Type*) := ZMod d → S

def matrixWordEquiv : State d (Fin b → S) ≃ ((ZMod d × Fin b) → ScalarWord d S) where
  toFun X il c := X il.1 c il.2
  invFun x i c l := x (i, l) c
  left_inv _ := rfl
  right_inv _ := rfl

def wordwise (L : Equiv.Perm (ScalarWord d S)) : Equiv.Perm (State d (Fin b → S)) where
  toFun X i c l := L (fun j => X i j l) c
  invFun X i c l := L.symm (fun j => X i j l) c
  left_inv X := by funext i c l; exact congrFun (L.symm_apply_apply (fun j => X i j l)) c
  right_inv X := by funext i c l; exact congrFun (L.apply_symm_apply (fun j => X i j l)) c

def scalarRotation (s : ZMod d) : Equiv.Perm (ScalarWord d S) where
  toFun x j := x (j + s)
  invFun x j := x (j - s)
  left_inv x := by funext j; simp
  right_inv x := by funext j; simp

def conjugateWordRotation (L : Equiv.Perm (ScalarWord d S)) (c : ZMod d) :
    Equiv.Perm (ScalarWord d S) :=
  scalarRotation c * L * scalarRotation 1 * L⁻¹ * scalarRotation (-c)

@[simp] theorem wordwise_rotation (s : ZMod d) (X : State d (Fin b → S)) :
    wordwise (scalarRotation s) X = rot s X := rfl

theorem wordwise_conjugate (L : Equiv.Perm (ScalarWord d S)) (c : ZMod d)
    (X : State d (Fin b → S)) :
    wordwise (conjugateWordRotation L c) X =
      rot c (wordwise L (rot 1 ((wordwise L).symm (rot (-c) X)))) := rfl

theorem matrixWordEquiv_wordwise (L : Equiv.Perm (ScalarWord d S))
    (X : State d (Fin b → S)) : matrixWordEquiv (wordwise L X) =
      fun il => L (matrixWordEquiv X il) := rfl

theorem conjugateWordRotation_fixes (L : Equiv.Perm (ScalarWord d S))
    (zero : S) (hL : L (fun _ => zero) = fun _ => zero) (c : ZMod d) :
    conjugateWordRotation L c (fun _ => zero) = fun _ => zero := by
  have hi : L.symm (fun _ => zero) = fun _ => zero := by
    apply L.injective
    rw [L.apply_symm_apply, hL]
  change scalarRotation c (L (scalarRotation 1 (L.symm
    (scalarRotation (-c) (fun _ => zero))))) = fun _ => zero
  change scalarRotation c (L (scalarRotation 1 (L.symm (fun _ => zero)))) = fun _ => zero
  rw [hi]
  change scalarRotation c (L (fun _ => zero)) = fun _ => zero
  rw [hL]
  rfl

theorem dimension_lt_punctured_word_card {a d : ℕ} (ha : 2 ≤ a) (hd : 2 ≤ d) :
    d < a ^ d - 1 := by
  have hk : ∀ k : ℕ, k + 3 < a ^ (k + 2) := by
    intro k
    induction k with
    | zero => norm_num [pow_two]; nlinarith
    | succ k ih =>
      rw [show k + 1 + 2 = (k + 2) + 1 by omega, pow_succ]
      nlinarith
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hd
  have h : 2 + k + 1 < a ^ (2 + k) := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hk k
  omega

theorem coprime_punctured_word_card {a d : ℕ} (ha : 0 < a) (hd : 0 < d) :
    Nat.Coprime a (a ^ d - 1) := by
  have hp : 1 ≤ a ^ d := Nat.one_le_pow d a ha
  have hc : Nat.Coprime (a ^ d) (a ^ d - 1) :=
    (Nat.coprime_self_sub_right hp).mpr (Nat.coprime_one_right _)
  exact hc.coprime_dvd_left (dvd_pow_self a hd.ne')

def conjugatePairGroup (L : Equiv.Perm (ScalarWord d S)) (c e : ZMod d) :
    Subgroup (Equiv.Perm (ScalarWord d S)) :=
  Subgroup.closure {conjugateWordRotation L c, conjugateWordRotation L e}

theorem conjugatePairGroup_fixes (L : Equiv.Perm (ScalarWord d S))
    (zero : S) (hL : L (fun _ => zero) = fun _ => zero) (c e : ZMod d)
    (g : conjugatePairGroup L c e) : g.val (fun _ => zero) = fun _ => zero := by
  have hle : conjugatePairGroup L c e ≤
      MulAction.stabilizer (Equiv.Perm (ScalarWord d S)) (fun _ : ZMod d => zero) := by
    apply (Subgroup.closure_le _).mpr
    intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl
    · exact conjugateWordRotation_fixes L zero hL c
    · exact conjugateWordRotation_fixes L zero hL e
  exact hle g.property

/-- The complete transitive-pair criterion, with the actual scalar conjugates
and actual shared map. Surjectivity, balance and the covariance quotient are
all derived; arbitrary lane mixing is allowed in `H`, `K` and their decoders. -/
theorem transitive_pair_impossible
    [Fintype S] [Nontrivial S] [NeZero d] [NeZero b]
    {κ : Type*} (hd : 2 ≤ d) (zero : S)
    (L : Equiv.Perm (ScalarWord d S)) (hL : L (fun _ => zero) = fun _ => zero)
    (p : ZMod d → κ) (K H : State d (Fin b → S) → State d (Fin b → S))
    (hH : Equivariant H) (hK : ClassUniform p K)
    (hexact : ∀ X, K (wordwise L (H X)) = swap X)
    (c e : ZMod d) (hce : p c = p e)
    (htrans : ∀ x : ScalarWord d S, x ≠ (fun _ => zero) →
      ∀ y : ScalarWord d S, y ≠ (fun _ => zero) →
        ∃ g : conjugatePairGroup L c e, g.val x = y) : False := by
  classical
  obtain ⟨f, hf⟩ := hK
  have hHi : Function.Injective H := by
    intro X Y h
    apply swapEquiv.injective
    change swap X = swap Y
    rw [← hexact X, ← hexact Y, h]
  let HE := Equiv.ofBijective H (Finite.injective_iff_bijective.mp hHi)
  have hKs : Function.Surjective K := by
    intro Y
    refine ⟨wordwise L (H (swap Y)), ?_⟩
    rw [hexact, swap_swap]
  have hKb : Function.Bijective K := Finite.injective_iff_bijective.mp
    (Finite.injective_iff_surjective.mpr hKs)
  have hQ := conjugate_intertwining (F := K) (wordwise L) HE hH hexact
  have hcov (i : ZMod d) (Y : State d (Fin b → S)) :
      f (p i) (wordwise (conjugateWordRotation L i) Y) =
        fun j => f (p i) Y (j + 1) := by
    rw [wordwise_conjugate]
    exact complete_decoder_covariance p K _ f hf hQ i Y
  let G := conjugatePairGroup L c e
  let E : State d (Fin b → S) ≃ ((ZMod d × Fin b) → ScalarWord d S) :=
    matrixWordEquiv
  let φ : ((ZMod d × Fin b) → ScalarWord d S) → (ZMod d → Fin b → S) :=
    f (p c) ∘ E.symm
  have hφ : Function.Surjective φ :=
    (complete_decoder_surjective p K f hf hKs c).comp E.symm.surjective
  let gens : Set G := (Subtype.val : G → Equiv.Perm (ScalarWord d S)) ⁻¹'
    {conjugateWordRotation L c, conjugateWordRotation L e}
  have hgen : Subgroup.closure gens = ⊤ := Subgroup.closure_closure_coe_preimage
  have hgens : ∀ g ∈ gens, ∃ t : Multiplicative (ZMod d),
      ∀ x, φ (g • x) = t • φ x := by
    intro g hg
    refine ⟨Multiplicative.ofAdd 1, ?_⟩
    intro x
    change f (p c) (E.symm (g • x)) = fun j => f (p c) (E.symm x) (j + 1)
    have he : E.symm (g • x) = wordwise g.val (E.symm x) := rfl
    rw [he]
    change g.val ∈ ({conjugateWordRotation L c, conjugateWordRotation L e} :
      Set (Equiv.Perm (ScalarWord d S))) at hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with hg | hg
    · rw [hg]
      exact hcov c (E.symm x)
    · rw [hg, hce]
      exact hcov e (E.symm x)
  obtain ⟨z, hz⟩ := exists_ne (φ (fun _ => fun _ => zero))
  have hbal : Nat.card {x : (ZMod d × Fin b) → ScalarWord d S // φ x = z} =
      Fintype.card S ^ (b * d * (d - 1)) := by
    have he := Nat.card_congr (E.symm.subtypeEquiv
      (p := fun x => φ x = z) (q := fun X => f (p c) X = z) (fun _ => Iff.rfl))
    rw [he, complete_decoder_fiber_card p K f hf hKb c z]
    simp only [Fintype.card_fun, Fintype.card_fin, ← pow_mul]
  have hcard : Nat.card (ScalarWord d S) = Fintype.card S ^ d := by
    simp [ScalarWord, Nat.card_eq_fintype_card, ZMod.card]
  have hsize : Nat.card (Multiplicative (ZMod d)) < Nat.card (ScalarWord d S) - 1 := by
    simpa [hcard, Nat.card_eq_fintype_card, ZMod.card] using
      dimension_lt_punctured_word_card (Fintype.one_lt_card (α := S)) hd
  have hcop : Nat.Coprime (Fintype.card S) (Nat.card (ScalarWord d S) - 1) := by
    rw [hcard]
    exact coprime_punctured_word_card Fintype.card_pos (by omega)
  exact no_balanced_pointed_covariance (G := G) (fun _ => zero)
    (conjugatePairGroup_fixes L zero hL c e) htrans
    (Fintype.card S) (b * d * (d - 1)) hsize hcop
    φ hφ gens hgen hgens z hz hbal

end SharedDecoders
