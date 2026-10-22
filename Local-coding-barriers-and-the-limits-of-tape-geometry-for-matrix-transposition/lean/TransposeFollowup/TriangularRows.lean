import TransposeFollowup.MatrixView

/-! Ordered row updates and the block-injectivity property they imply.
The first stage updates each row bijectively in its own argument, with
arbitrary nonlinear dependence on earlier rows. No block property is assumed.
-/

namespace TransposeFollowup

set_option autoImplicit false
open Classical

def BlockInjective {ι Q : Type*} [Fintype ι] (f : (ι → Q) → (ι → Q)) : Prop :=
  ∀ (I : Finset ι) (x y : ι → Q),
    (∀ i ∉ I, x i = y i) → (∀ i ∈ I, f x i = f y i) → x = y

structure TriangularRows (n : ℕ) (Q : Type*) where
  order : Equiv.Perm (Fin n)
  update : (i : Fin n) → ({j : Fin n // order j < order i} → Q) → (Q ≃ Q)

namespace TriangularRows

variable {n : ℕ} {Q : Type*} (F : TriangularRows n Q)

def apply (x : Fin n → Q) (i : Fin n) : Q :=
  F.update i (fun j => x j.val) (x i)

theorem block_injective : BlockInjective F.apply := by
  intro I x y houtside hinside
  have h : ∀ k : ℕ, ∀ i : Fin n, (F.order i).val = k → x i = y i := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro i hi
      by_cases hiI : i ∈ I
      · have hp : (fun j : {j : Fin n // F.order j < F.order i} => x j.val) =
            (fun j : {j : Fin n // F.order j < F.order i} => y j.val) := by
          funext j
          exact ih (F.order j.val).val (by simpa [← hi] using j.property) j.val rfl
        have he := hinside i hiI
        change F.update i _ (x i) = F.update i _ (y i) at he
        rw [hp] at he
        exact (F.update i _).injective he
      · exact houtside i hiI
  funext i
  exact h _ i rfl

theorem injective : Function.Injective F.apply := by
  intro x y he
  exact F.block_injective Finset.univ x y (by simp) (by intro i _; exact congrFun he i)

/-- Global invertibility is derived from the triangular updates on a finite
row alphabet. It is not an extra assumption on a purported algorithm. -/
noncomputable def equiv [Fintype Q] : (Fin n → Q) ≃ (Fin n → Q) :=
  Equiv.ofBijective F.apply ((Finite.injective_iff_bijective).mp F.injective)

@[simp] theorem equiv_apply [Fintype Q] (x : Fin n → Q) : F.equiv x = F.apply x := rfl

end TriangularRows

theorem blockInjective_inverse {ι Q : Type*} [Fintype ι]
    (f : (ι → Q) ≃ (ι → Q)) (hf : BlockInjective f) : BlockInjective f.symm := by
  intro I x y houtside hinside
  have he : f.symm x = f.symm y := by
    apply hf Iᶜ
    · intro i hi
      exact hinside i (by simpa using hi)
    · intro i hi
      simpa only [f.apply_symm_apply] using houtside i (by simpa using hi)
  exact f.symm.injective he

/-- A rowwise bijection following a block-injective map preserves the property. -/
theorem blockInjective_rowwise {ι Q : Type*} [Fintype ι]
    (f : (ι → Q) → (ι → Q)) (hf : BlockInjective f) (L : (i : ι) → Q ≃ Q) :
    BlockInjective (fun x i => L i (f x i)) := by
  intro I x y houtside hinside
  apply hf I x y houtside
  intro i hi
  exact (L i).injective (hinside i hi)

/-- The second stage may discard information. Each output uses only its own
and earlier incoming rows in this stage's public order. -/
structure CausalRows (n : ℕ) (Q : Type*) where
  order : Equiv.Perm (Fin n)
  update : (i : Fin n) → ({j : Fin n // order j ≤ order i} → Q) → Q

namespace CausalRows

variable {n : ℕ} {Q : Type*} (G : CausalRows n Q)

def apply (x : Fin n → Q) (i : Fin n) : Q := G.update i (fun j => x j.val)

theorem prefix_eq {x y : Fin n → Q} (i : Fin n)
    (h : ∀ j, G.order j ≤ G.order i → x j = y j) : G.apply x i = G.apply y i := by
  unfold apply
  congr 1
  funext j
  exact h j.val j.property

end CausalRows

end TransposeFollowup
