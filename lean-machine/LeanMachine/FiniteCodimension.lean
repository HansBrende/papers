import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Order.CompleteLattice.Finset
import Mathlib.Tactic

/-! Finite relative-codimension bounds for intersections, sums and joint observations. -/

namespace LeanMachine.FiniteCodimension

open Module

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  [FiniteDimensional F V]

omit [FiniteDimensional F V] in
theorem finrank_comap_equiv (W : Submodule F V) (e : V ≃ₗ[F] V) :
    finrank F (W.comap e.toLinearMap) = finrank F W := by
  rw [Submodule.comap_equiv_eq_map_symm]
  exact (Submodule.equivMapOfInjective e.symm.toLinearMap e.symm.injective W).finrank_eq.symm

/-- Intersecting two pairs of nested spaces adds their codimension invoices. -/
theorem finrank_inf_defect (L₁ H₁ L₂ H₂ : Submodule F V)
    (h₁ : L₁ ≤ H₁) (h₂ : L₂ ≤ H₂) :
    finrank F (H₁ ⊓ H₂ : Submodule F V) + finrank F L₁ + finrank F L₂ ≤
      finrank F (L₁ ⊓ L₂ : Submodule F V) + finrank F H₁ + finrank F H₂ := by
  have hs := Submodule.finrank_mono (sup_le_sup h₁ h₂)
  have hL := Submodule.finrank_sup_add_finrank_inf_eq L₁ L₂
  have hH := Submodule.finrank_sup_add_finrank_inf_eq H₁ H₂
  omega

/-- Taking sums loses at most the sum of the two relative codimensions. -/
theorem finrank_sup_defect (L₁ H₁ L₂ H₂ : Submodule F V)
    (h₁ : L₁ ≤ H₁) (h₂ : L₂ ≤ H₂) :
    finrank F (H₁ ⊔ H₂ : Submodule F V) + finrank F L₁ + finrank F L₂ ≤
      finrank F (L₁ ⊔ L₂ : Submodule F V) + finrank F H₁ + finrank F H₂ := by
  have hi := Submodule.finrank_mono (inf_le_inf h₁ h₂)
  have hL := Submodule.finrank_sup_add_finrank_inf_eq L₁ L₂
  have hH := Submodule.finrank_sup_add_finrank_inf_eq H₁ H₂
  omega

theorem finrank_finite_inf_defect {ι : Type*} (S : Finset ι)
    (L H : ι → Submodule F V) (hLH : ∀ i ∈ S, L i ≤ H i) :
    finrank F (⨅ i ∈ S, H i : Submodule F V) ≤ finrank F (⨅ i ∈ S, L i : Submodule F V) +
      ∑ i ∈ S, (finrank F (H i) - finrank F (L i)) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have hH : (⨅ i ∈ (∅ : Finset ι), H i : Submodule F V) = ⊤ := by simp
    have hL : (⨅ i ∈ (∅ : Finset ι), L i : Submodule F V) = ⊤ := by simp
    rw [hH, hL]
    simp
  | @insert i S hi ih =>
    have hLi := hLH i (Finset.mem_insert_self ..)
    have hLS : ∀ j ∈ S, L j ≤ H j := fun j hj => hLH j (Finset.mem_insert_of_mem hj)
    have hmeet : (⨅ j ∈ S, L j) ≤ (⨅ j ∈ S, H j) := by
      apply iInf_mono
      intro j
      exact iInf_mono fun hj => hLS j hj
    have hc := finrank_inf_defect (L i) (H i) (⨅ j ∈ S, L j) (⨅ j ∈ S, H j) hLi hmeet
    have hdim := Submodule.finrank_mono hLi
    have hind := ih hLS
    rw [Finset.iInf_insert, Finset.iInf_insert, Finset.sum_insert hi]
    exact
      (show finrank F (H i ⊓ ⨅ j ∈ S, H j : Submodule F V) ≤
        finrank F (L i ⊓ ⨅ j ∈ S, L j : Submodule F V) +
          ((finrank F (H i) - finrank F (L i)) +
            ∑ j ∈ S, (finrank F (H j) - finrank F (L j))) by omega)

/-- Two observations of the same codimension, with an invertible change of
coordinates preserving `H`, recover a subspace supported in `I`. -/
theorem finrank_double_kernel_support (H K I : Submodule F V) (e : V ≃ₗ[F] V)
    (hH : H.comap e.toLinearMap = H)
    (hsupport : H ⊓ K ⊓ K.comap e.toLinearMap ≤ I) :
    finrank F H ≤ finrank F (H ⊓ I : Submodule F V) +
      2 * (finrank F H - finrank F (H ⊓ K : Submodule F V)) := by
  let A := H ⊓ K
  let B := A.comap e.toLinearMap
  have hB : B = H ⊓ K.comap e.toLinearMap := by
    simp only [B, A, Submodule.comap_inf, hH]
  have hdim : finrank F B = finrank F A := finrank_comap_equiv A e
  have hAB : A ⊓ B ≤ H ⊓ I := by
    apply le_inf
    · exact inf_le_left.trans inf_le_left
    · intro x hx
      have hb : x ∈ (H ⊓ K.comap e.toLinearMap : Submodule F V) := by
        rw [← hB]
        exact hx.2
      exact hsupport ⟨hx.1, hb.2⟩
  have hjoint := Submodule.finrank_mono hAB
  have hsup := Submodule.finrank_mono
    (sup_le (inf_le_left : A ≤ H) (show B ≤ H by rw [hB]; exact inf_le_left))
  have hc := Submodule.finrank_sup_add_finrank_inf_eq A B
  have hAK := Submodule.finrank_mono (inf_le_left : H ⊓ K ≤ H)
  rw [hdim] at hc
  dsimp only [A] at hjoint hc hsup
  omega

/-- Both error images are paid separately; no invariance of their image is used. -/
theorem finrank_sup_comap_support (H I : Submodule F V) (e : V ≃ₗ[F] V)
    (hI : I.comap e.toLinearMap = I) :
    finrank F (H ⊔ H.comap e.toLinearMap : Submodule F V) +
      2 * finrank F (H ⊓ I : Submodule F V) ≤ finrank F I + 2 * finrank F H := by
  have he := finrank_comap_equiv H e
  have hi : finrank F (I ⊓ H.comap e.toLinearMap : Submodule F V) =
      finrank F (H ⊓ I : Submodule F V) := by
    calc
      _ = finrank F ((I ⊓ H).comap e.toLinearMap) := by rw [Submodule.comap_inf, hI]
      _ = finrank F (I ⊓ H : Submodule F V) := finrank_comap_equiv _ e
      _ = _ := by rw [inf_comm]
  have h₁ := Submodule.finrank_sup_add_finrank_inf_eq I H
  have h₂ := Submodule.finrank_sup_add_finrank_inf_eq (I ⊔ H) (H.comap e.toLinearMap)
  have hlow := Submodule.finrank_mono
    (inf_le_inf_right (H.comap e.toLinearMap) (le_sup_left : I ≤ I ⊔ H))
  have hupp := Submodule.finrank_mono
    (sup_le_sup_right (le_sup_right : H ≤ I ⊔ H) (H.comap e.toLinearMap))
  rw [hi] at hlow
  rw [inf_comm I H] at h₁
  omega

end LeanMachine.FiniteCodimension
