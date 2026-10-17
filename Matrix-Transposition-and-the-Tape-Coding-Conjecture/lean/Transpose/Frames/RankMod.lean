import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.RingTheory.Localization.Module
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat

/-!
# Rank modulo 2 is at most rank over `ℚ`

For an integer matrix `J`, the rank of `J mod 2` over `F₂ = ZMod 2` is at most the rank of
`J` over `ℚ`.

Proof: pick columns of `J mod 2` forming a basis of its column space (over `F₂`). The
corresponding integer columns are linearly independent over `ℤ`: a nontrivial integer dependence
can be divided by the gcd of its coefficients, after which some coefficient is odd, and reducing
modulo 2 gives a nontrivial dependence over `F₂`. Linear independence over `ℤ` of integer vectors
is the same as linear independence over the fraction field `ℚ`
(`LinearIndependent.iff_fractionRing`), so the rank over `ℚ` is at least the number of chosen
columns, which is the rank over `F₂`.
-/

namespace Transpose.ShearFrame

open Module Submodule Matrix

/-- Integer vectors whose reductions modulo 2 are linearly independent over `ZMod 2` are
linearly independent over `ℤ`. -/
theorem linearIndependent_int_of_mod_two {ι m : Type*} (v : ι → (m → ℤ))
    (h : LinearIndependent (ZMod 2) (fun i => fun r => ((v i r : ℤ) : ZMod 2))) :
    LinearIndependent ℤ v := by
  rw [linearIndependent_iff'] at h ⊢
  intro s g hg i hi
  by_contra hne
  obtain ⟨e, he, hgcd⟩ := Finset.extract_gcd g ⟨i, hi⟩
  have hG : s.gcd g ≠ 0 := fun h0 => hne (Finset.gcd_eq_zero_iff.mp h0 i hi)
  have h1 : ∑ j ∈ s, e j • v j = 0 := by
    have h1' : s.gcd g • ∑ j ∈ s, e j • v j = 0 := by
      rw [Finset.smul_sum, ← hg]
      exact Finset.sum_congr rfl fun j hj => by rw [he j hj, mul_smul]
    exact (smul_eq_zero.mp h1').resolve_left hG
  have h2 : ∑ j ∈ s, (fun j => (e j : ZMod 2)) j •
      (fun i => fun r => ((v i r : ℤ) : ZMod 2)) j = 0 := by
    funext r
    have := congrArg (fun w : m → ℤ => ((w r : ℤ) : ZMod 2)) h1
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this
  have h3 := h s _ h2
  have h4 : (2 : ℤ) ∣ s.gcd e := Finset.dvd_gcd fun j hj => by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (e j) 2).mp (h3 j hj)
    exact_mod_cast this
  rw [hgcd] at h4
  omega

/-- Integer vectors whose reductions modulo 2 are linearly independent over `ZMod 2` are
linearly independent over `ℚ` (after casting to `ℚ`). -/
theorem linearIndependent_rat_of_mod_two {ι m : Type*} (v : ι → (m → ℤ))
    (h : LinearIndependent (ZMod 2) (fun i => fun r => ((v i r : ℤ) : ZMod 2))) :
    LinearIndependent ℚ (fun i => fun r => ((v i r : ℤ) : ℚ)) := by
  rw [← LinearIndependent.iff_fractionRing ℤ ℚ]
  let f : (m → ℤ) →ₗ[ℤ] (m → ℚ) := (Int.castAddHom ℚ).toIntLinearMap.compLeft m
  have hf : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro x y hxy
    funext r
    have := congrFun hxy r
    simpa [f] using this
  exact (linearIndependent_int_of_mod_two v h).map' f hf

/-- The rank of an integer matrix reduced modulo 2 is at most its rank over `ℚ`. -/
theorem rank_map_zmod_le_rank_map_rat {m n : ℕ} (J : Matrix (Fin m) (Fin n) ℤ) :
    (J.map (Int.cast : ℤ → ZMod 2)).rank ≤ (J.map (Int.cast : ℤ → ℚ)).rank := by
  classical
  rw [Matrix.rank_eq_finrank_span_cols, Matrix.rank_eq_finrank_span_cols]
  obtain ⟨κ, a, ha, hspan, hli⟩ :=
    exists_linearIndependent' (ZMod 2) (J.map (Int.cast : ℤ → ZMod 2)).col
  have : Finite κ := Finite.of_injective a ha
  have : Fintype κ := Fintype.ofFinite κ
  rw [← hspan, finrank_span_eq_card hli]
  have hliQ : LinearIndependent ℚ ((J.map (Int.cast : ℤ → ℚ)).col ∘ a) :=
    linearIndependent_rat_of_mod_two (fun k => J.col (a k)) hli
  calc Fintype.card κ
      = finrank ℚ (span ℚ (Set.range ((J.map (Int.cast : ℤ → ℚ)).col ∘ a))) :=
        (finrank_span_eq_card hliQ).symm
    _ ≤ finrank ℚ (span ℚ (Set.range (J.map (Int.cast : ℤ → ℚ)).col)) := by
        apply Submodule.finrank_mono
        apply span_mono
        rintro _ ⟨k, rfl⟩
        exact ⟨a k, rfl⟩

end Transpose.ShearFrame
