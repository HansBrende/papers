import TransposeFollowup.TriangularRows

/-! A finite counting lemma for a block-injective middle inverse, a fixed set
of queried original rows, and a common output support. Correctness may hold
only on an arbitrary correlated subfamily. End maps need not be injective.
This fixed-query lemma is sufficient for the exact two-stage architecture;
it does not purport to formalize the optional adaptive-wrapper extension.
-/

namespace TransposeFollowup

set_option autoImplicit false
open Classical

theorem transposed_injective (n b : ℕ) :
    Function.Injective (transposed (n := n) (b := b)) := by
  intro x y h
  funext i j t
  simpa only [transposed_apply] using congrFun (congrFun (congrFun h j) i) t

abbrev SandwichRecord {n b : ℕ} (I R J : Finset (Fin n)) :=
  ({i : Fin n // i ∉ I} → Row n b) × (R → J → Fin b → Bool)

theorem sandwichRecord_card {n b : ℕ} (I R J : Finset (Fin n)) :
    Fintype.card (SandwichRecord (b := b) I R J) =
      2 ^ ((n - I.card) * n * b + R.card * J.card * b) := by
  simp only [SandwichRecord, Row, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_subtype_compl, Fintype.card_coe, Fintype.card_fin, Fintype.card_bool]
  simp only [← pow_mul, ← pow_add]
  congr 1
  ring

def sandwichRecord {n b : ℕ}
    (A : FiniteMatrix n b ≃ FiniteMatrix n b) (C : FiniteMatrix n b → FiniteMatrix n b)
    (I R J : Finset (Fin n)) (x : FiniteMatrix n b) : SandwichRecord (b := b) I R J :=
  (fun i => A.symm (C x) i.val, fun i j t => x i.val j.val t)

/-- The record consists of complementary intermediate rows and the R-by-J
raw rectangle. Correctness fixes all other coordinates of the queried rows. -/
theorem sandwichRecord_injective {n b : ℕ}
    (A : FiniteMatrix n b ≃ FiniteMatrix n b) (B C : FiniteMatrix n b → FiniteMatrix n b)
    (I R J : Finset (Fin n)) (hA : BlockInjective A)
    (hC : ∀ x y, (∀ i ∈ R, x i = y i) → ∀ i ∈ I, C x i = C y i)
    (hB : ∀ u v, (∀ i ∉ I, u i = v i) → ∀ j ∉ J, B u j = B v j)
    (F : Finset (FiniteMatrix n b))
    (hc : ∀ x ∈ F, B (A.symm (C x)) = transposed x) :
    Function.Injective (fun x : F => sandwichRecord A C I R J x.val) := by
  intro x y he
  have hout : ∀ i ∉ I, A.symm (C x.val) i = A.symm (C y.val) i := by
    intro i hi
    exact congrFun (congrArg Prod.fst he) ⟨i, hi⟩
  have hrows : ∀ i ∈ R, x.val i = y.val i := by
    intro i hi
    funext j t
    by_cases hj : j ∈ J
    · exact congrFun (congrFun (congrFun (congrArg Prod.snd he) ⟨i, hi⟩) ⟨j, hj⟩) t
    · have hcj := hB _ _ hout j hj
      rw [hc x.val x.property, hc y.val y.property] at hcj
      simpa only [transposed_apply] using congrFun (congrFun hcj i) t
  have hmid : A.symm (C x.val) = A.symm (C y.val) := by
    apply hA I _ _ hout
    simpa only [A.apply_symm_apply] using hC x.val y.val hrows
  apply Subtype.ext
  apply transposed_injective n b
  rw [← hc x.val x.property, ← hc y.val y.property, hmid]

theorem fixed_support_transpose_count {n b : ℕ}
    (A : FiniteMatrix n b ≃ FiniteMatrix n b) (B C : FiniteMatrix n b → FiniteMatrix n b)
    (I R J : Finset (Fin n)) (hA : BlockInjective A)
    (hC : ∀ x y, (∀ i ∈ R, x i = y i) → ∀ i ∈ I, C x i = C y i)
    (hB : ∀ u v, (∀ i ∉ I, u i = v i) → ∀ j ∉ J, B u j = B v j)
    (F : Finset (FiniteMatrix n b))
    (hc : ∀ x ∈ F, B (A.symm (C x)) = transposed x) :
    F.card ≤ 2 ^ ((n - I.card) * n * b + R.card * J.card * b) := by
  have h := Fintype.card_le_of_injective _ (sandwichRecord_injective A B C I R J hA hC hB F hc)
  simpa only [Fintype.card_coe, sandwichRecord_card] using h

end TransposeFollowup
