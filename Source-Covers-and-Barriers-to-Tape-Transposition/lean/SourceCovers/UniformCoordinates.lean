import LeanMachine.DisjointSums
import TransposeFollowup.EntropyFibers

/-! Exact uniform laws for the finite maps used by the subset code. Entropy
is the earlier papers' finite entropy (natural logarithms until converted
to bits); independence is equality of the joint and product mass functions. -/

namespace SourceCovers

open Finset LeanMachine TransposeFollowup
open scoped BigOperators Classical
noncomputable section

theorem uniform_disjointSums {ι κ A : Type*} [Fintype ι] [Fintype κ]
    [Fintype A] [AddCommGroup A] (C : DisjointSums ι κ) :
    pushforward (uniformWeight (ι → A)) C.encode = uniformWeight (κ → A) := by
  funext y
  rw [pushforward_uniformWeight]
  have h := @card_fiber_mul_card (ι → A) (κ → A) _ _ _ _
    (fun a b => Classical.propDecidable (a = b)) C.encode C.encode_surjective y
  have hR : (fiberCard C.encode y : ℝ) * Fintype.card (κ → A) =
      Fintype.card (ι → A) := by
    simpa only [fiberCard, Nat.cast_mul] using congrArg (fun n : ℕ => (n : ℝ)) h
  have hd : (Fintype.card (ι → A) : ℝ) ≠ 0 := by positivity
  have hc : (Fintype.card (κ → A) : ℝ) ≠ 0 := by positivity
  dsimp only [uniformWeight]
  field_simp
  nlinarith

/-- Joint independence of one coordinate and any observation invariant
under updating it. In particular the observation may contain all other
coordinates together with a helper that ignores this coordinate. -/
theorem uniform_independent_coordinate {ι A B : Type*}
    [Fintype ι] [Fintype A] [Nonempty A]
    (f : (ι → A) → B) (i : ι)
    (hf : ∀ x c, f (Function.update x i c) = f x) (a : A) (b : B) :
    pushforward (uniformWeight (ι → A)) (fun x => (x i, f x)) (a, b) =
      pushforward (uniformWeight (ι → A)) (fun x => x i) a *
        pushforward (uniformWeight (ι → A)) f b := by
  simp only [pushforward_uniformWeight, fiberCard, Prod.mk.injEq]
  have h := card_independent_coordinate f i a b hf
  have hR : ((univ.filter fun x : ι → A => x i = a ∧ f x = b).card : ℝ) *
      Fintype.card (ι → A) =
      (univ.filter fun x : ι → A => x i = a).card *
        ((univ.filter fun x : ι → A => f x = b).card : ℝ) := by exact_mod_cast h
  have hd : (Fintype.card (ι → A) : ℝ) ≠ 0 := by positivity
  field_simp
  nlinarith

end
end SourceCovers
