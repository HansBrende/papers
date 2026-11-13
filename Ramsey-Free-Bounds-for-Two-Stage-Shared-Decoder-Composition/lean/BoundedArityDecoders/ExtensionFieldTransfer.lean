import BoundedArityDecoders.ExtensionLinearRun
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Data.Nat.Totient

/-!
# Field-Extension Rank & Primitive-Root Transfer Infrastructure

Shared algebraic-closure and field-homomorphism transfer lemmas used across the formal proofs of
Results 1 and 2 (`ExtensionLinearRunProofs` and `ExtensionAperiodicSixProofs`):

1. `coprimeToChar_iff_natCast_ne_zero`: `CoprimeToChar F n ↔ ((n : ℕ) : F) ≠ 0` for `n ≥ 1`.
2. `exists_isPrimitiveRoot_of_isAlgClosed` & `exists_isPrimitiveRoot_algebraicClosure`: when
   `n ≥ 1` and `CoprimeToChar F n`, `AlgebraicClosure F` admits a primitive `n`-th root of unity.
3. `linearIndependent_fin_pi_ringHom` & `finrank_le_of_pi_ringHom`: pushing an `F`-subspace
   `U ≤ (I → F)` into a `K`-subspace `W ≤ (I → K)` along any field homomorphism `φ : F →+* K`
   preserves linear independence and bounds dimension (`finrank F U ≤ finrank K W`).
4. `extendLinearMapPi`: canonical extension of an `F`-linear map `(I → F) →ₗ[F] (J → F)` along
   `φ : F →+* K` to `(I → K) →ₗ[K] (J → K)` commuting with coordinatewise `φ`.
-/

namespace BoundedArityDecoders

open Module Polynomial
open scoped BigOperators

section CharAndRoots

/-- For `n ≥ 1`, `CoprimeToChar F n` holds if and only if `(n : F) ≠ 0`. -/
theorem coprimeToChar_iff_natCast_ne_zero (F : Type*) [Field F] (n : ℕ) [NeZero n] :
    CoprimeToChar F n ↔ ((n : ℕ) : F) ≠ 0 := by
  unfold CoprimeToChar
  have hcast_zero : (((n : ℕ) : F) = 0) ↔ ringChar F ∣ n :=
    CharP.cast_eq_zero_iff F (ringChar F) n
  rcases eq_or_ne (ringChar F) 0 with h0 | hpos
  · constructor
    · intro _ hzero
      rw [hcast_zero, h0, zero_dvd_iff] at hzero
      exact NeZero.ne n hzero
    · intro _
      exact Or.inl h0
  · have hp : Nat.Prime (ringChar F) :=
      (CharP.char_is_prime_or_zero F (ringChar F)).resolve_right hpos
    rw [or_iff_right hpos, Nat.coprime_comm, hp.coprime_iff_not_dvd]
    exact not_congr hcast_zero.symm

/-- Over any algebraically closed field `K` in which `(n : K) ≠ 0` (`n ≥ 1`), there exists a
primitive `n`-th root of unity `ω : K`. -/
theorem exists_isPrimitiveRoot_of_isAlgClosed (K : Type*) [Field K] [IsAlgClosed K]
    (n : ℕ) [NeZero n] (hn_cast : ((n : ℕ) : K) ≠ 0) :
    ∃ ω : K, IsPrimitiveRoot ω n := by
  classical
  have hn_pos : 0 < n := NeZero.pos n
  let P : K[X] := X ^ n - 1
  have hP_deg : P.natDegree = n := by
    simpa [P] using natDegree_X_pow_sub_C (n := n) (r := (1 : K))
  have hP_ne : P ≠ 0 := X_pow_sub_C_ne_zero hn_pos (1 : K)
  have hcard_roots : P.roots.card = n := by
    rw [IsAlgClosed.card_roots_eq_natDegree, hP_deg]
  have hderiv : derivative P = C ((n : ℕ) : K) * X ^ (n - 1) := by
    simp [P, derivative_X_pow]
  have hnodup : P.roots.Nodup := by
    rw [Multiset.nodup_iff_count_le_one]
    intro a
    by_contra hgt
    have hcount_pos : 0 < P.roots.count a := by omega
    have ha_mem : a ∈ P.roots := Multiset.count_pos.mp hcount_pos
    have h2 : 2 ≤ rootMultiplicity a P := by
      rw [← Polynomial.count_roots]
      omega
    have hdvd : (X - C a) ^ 2 ∣ P :=
      dvd_trans (pow_dvd_pow (X - C a) h2) (Polynomial.pow_rootMultiplicity_dvd P a)
    obtain ⟨Q, hQ⟩ := hdvd
    have ha_eval : P.eval a = 0 := (Polynomial.mem_roots hP_ne).mp ha_mem
    have ha_pow : a ^ n = 1 := by
      dsimp [P] at ha_eval
      simpa [sub_eq_zero] using ha_eval
    have ha_ne : a ≠ 0 := by
      intro ha0
      rw [ha0, zero_pow (NeZero.ne n)] at ha_pow
      exact zero_ne_one ha_pow
    have hderiv_eval_ne : (derivative P).eval a ≠ 0 := by
      rw [hderiv]
      simp only [eval_mul, eval_C, eval_pow, eval_X]
      exact mul_ne_zero hn_cast (pow_ne_zero _ ha_ne)
    have hderiv_eval_zero : (derivative P).eval a = 0 := by
      have hQ' : P = (X - C a) * ((X - C a) * Q) := by
        rw [hQ]
        ring
      rw [hQ', derivative_mul]
      simp
    exact hderiv_eval_ne hderiv_eval_zero
  have hnth_eq : nthRootsFinset n (1 : K) = P.roots.toFinset := by
    ext z
    simp only [Polynomial.mem_nthRootsFinset hn_pos, Multiset.mem_toFinset,
      Polynomial.mem_roots hP_ne, IsRoot.def, P, eval_sub, eval_pow, eval_X, eval_one, sub_eq_zero]
  have hnth_card : (nthRootsFinset n (1 : K)).card = n := by
    rw [hnth_eq, Multiset.toFinset_card_of_nodup hnodup, hcard_roots]
  have hprim_le : ∀ d : ℕ, (primitiveRoots d K).card ≤ Nat.totient d := by
    intro d
    by_cases hne : (primitiveRoots d K).Nonempty
    · obtain ⟨ζ, hζ⟩ := hne
      rw [(isPrimitiveRoot_of_mem_primitiveRoots hζ).card_primitiveRoots]
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty]
      exact Nat.zero_le _
  have hprim_n_ne : (primitiveRoots n K).Nonempty := by
    by_contra hempty
    have h0 : (primitiveRoots n K).card = 0 := by
      rw [Finset.not_nonempty_iff_eq_empty.mp hempty, Finset.card_empty]
    have htot_pos : 0 < Nat.totient n := Nat.totient_pos.mpr hn_pos
    have hn_mem : n ∈ n.divisors := Nat.mem_divisors.mpr ⟨dvd_rfl, NeZero.ne n⟩
    have hbiUnion : nthRootsFinset n (1 : K) = n.divisors.biUnion (fun d => primitiveRoots d K) :=
      @IsPrimitiveRoot.nthRoots_one_eq_biUnion_primitiveRoots K _ _ inferInstance n
    have hsum_lt : ∑ d ∈ n.divisors, (primitiveRoots d K).card <
        ∑ d ∈ n.divisors, Nat.totient d := by
      refine Finset.sum_lt_sum (fun d _ => hprim_le d) ⟨n, hn_mem, ?_⟩
      omega
    have hcard_le : n ≤ ∑ d ∈ n.divisors, (primitiveRoots d K).card := by
      calc n = (nthRootsFinset n (1 : K)).card := hnth_card.symm
        _ = (n.divisors.biUnion (fun d => primitiveRoots d K)).card := congrArg Finset.card hbiUnion
        _ ≤ ∑ d ∈ n.divisors, (primitiveRoots d K).card := Finset.card_biUnion_le
    rw [Nat.sum_totient n] at hsum_lt
    omega
  obtain ⟨ω, hω⟩ := hprim_n_ne
  exact ⟨ω, isPrimitiveRoot_of_mem_primitiveRoots hω⟩

/-- When `CoprimeToChar F n` (`n ≥ 1`), `AlgebraicClosure F` contains a primitive `n`-th root of
unity. -/
theorem exists_isPrimitiveRoot_algebraicClosure (F : Type*) [Field F]
    (n : ℕ) [NeZero n] (hchar : CoprimeToChar F n) :
    ∃ ω : AlgebraicClosure F, IsPrimitiveRoot ω n := by
  have hnF : ((n : ℕ) : F) ≠ 0 := (coprimeToChar_iff_natCast_ne_zero F n).mp hchar
  have hnK : ((n : ℕ) : AlgebraicClosure F) ≠ 0 := by
    intro h0
    apply hnF
    apply (algebraMap F (AlgebraicClosure F)).injective
    rw [map_natCast, map_zero]
    exact h0
  exact exists_isPrimitiveRoot_of_isAlgClosed (AlgebraicClosure F) n hnK

end CharAndRoots

section FieldHomLinearTransfer

/-- Coordinatewise pushforward of `Fin r → (I → F)` along a field homomorphism `φ : F →+* K`
preserves linear independence (for arbitrary index type `I`, with no finiteness restriction on the
field extension). -/
theorem linearIndependent_fin_pi_ringHom {F K I : Type*} [Field F] [Field K]
    (φ : F →+* K) :
    ∀ {r : ℕ} (v : Fin r → (I → F)),
      LinearIndependent F v →
      LinearIndependent K (fun t i => φ (v t i))
  | 0, _, _ => linearIndependent_empty_type
  | r + 1, v, hv => by
    have hv0_ne : v 0 ≠ 0 := hv.ne_zero 0
    have hex_i : ∃ i₀ : I, v 0 i₀ ≠ 0 := by
      by_contra hall
      apply hv0_ne
      funext i
      by_contra hi
      exact hall ⟨i, hi⟩
    obtain ⟨i₀, hi₀⟩ := hex_i
    let c : Fin r → F := fun t => v t.succ i₀ / v 0 i₀
    let w : Fin r → (I → F) := fun t => v t.succ - c t • v 0
    have hw_i0 : ∀ t : Fin r, w t i₀ = 0 := by
      intro t
      show v t.succ i₀ - (v t.succ i₀ / v 0 i₀) * v 0 i₀ = 0
      rw [div_mul_cancel₀ _ hi₀, sub_self]
    have hw_lin : LinearIndependent F w := by
      rw [Fintype.linearIndependent_iff] at hv ⊢
      intro a ha
      let b : Fin (r + 1) → F := Fin.cases (- ∑ t : Fin r, a t * c t) a
      have hb : ∑ s : Fin (r + 1), b s • v s = 0 := by
        rw [Fin.sum_univ_succ]
        simp only [b, Fin.cases_zero, Fin.cases_succ]
        funext i
        have hai := congrFun ha i
        simp only [Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, Pi.zero_apply,
          smul_eq_mul, w] at hai
        simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
        have hident :
            (- ∑ t : Fin r, a t * c t) * v 0 i + ∑ x : Fin r, a x * v x.succ i =
              ∑ x : Fin r, a x * (v x.succ i - c x * v 0 i) := by
          simp only [mul_sub, Finset.sum_sub_distrib, ← mul_assoc, ← Finset.sum_mul, neg_mul]
          ring
        rw [hident]
        exact hai
      intro t
      simpa [b] using hv b hb t.succ
    have hwK : LinearIndependent K (fun t i => φ (w t i)) :=
      linearIndependent_fin_pi_ringHom φ w hw_lin
    rw [Fintype.linearIndependent_iff] at hwK ⊢
    intro α hα
    have hα_i0 : α 0 = - ∑ t : Fin r, α t.succ * φ (c t) := by
      have hi := congrFun hα i₀
      rw [Fin.sum_univ_succ] at hi
      simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hi
      have hrel : ∀ t : Fin r, φ (v t.succ i₀) = φ (c t) * φ (v 0 i₀) := by
        intro t
        have h0 := hw_i0 t
        dsimp [w] at h0
        have hEq : v t.succ i₀ = c t * v 0 i₀ := sub_eq_zero.mp h0
        rw [hEq, map_mul]
      have hfactor : (α 0 + ∑ t : Fin r, α t.succ * φ (c t)) * φ (v 0 i₀) = 0 := by
        calc (α 0 + ∑ t : Fin r, α t.succ * φ (c t)) * φ (v 0 i₀)
            = α 0 * φ (v 0 i₀) + ∑ t : Fin r, α t.succ * (φ (c t) * φ (v 0 i₀)) := by
                rw [add_mul, Finset.sum_mul]
                simp only [mul_assoc]
          _ = α 0 * φ (v 0 i₀) + ∑ t : Fin r, α t.succ * φ (v t.succ i₀) := by
                congr 1
                refine Finset.sum_congr rfl fun t _ => by rw [hrel t]
          _ = 0 := hi
      have hφ_ne : φ (v 0 i₀) ≠ 0 := by
        intro hz
        exact hi₀ (φ.injective (by simpa using hz))
      have hsum0 : α 0 + ∑ t : Fin r, α t.succ * φ (c t) = 0 :=
        (mul_eq_zero.mp hfactor).resolve_right hφ_ne
      exact eq_neg_of_add_eq_zero_left hsum0
    have hα_w : ∑ t : Fin r, α t.succ • (fun i => φ (w t i)) = 0 := by
      funext i
      have hi := congrFun hα i
      rw [Fin.sum_univ_succ] at hi
      simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hi
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
      rw [hα_i0] at hi
      have hw_map : ∀ t : Fin r, φ (w t i) = φ (v t.succ i) - φ (c t) * φ (v 0 i) := by
        intro t
        dsimp [w]
        simp [map_sub, map_mul]
      simp only [hw_map]
      have hident :
          ∑ x : Fin r, α x.succ * (φ (v x.succ i) - φ (c x) * φ (v 0 i)) =
            (- ∑ t : Fin r, α t.succ * φ (c t)) * φ (v 0 i) +
              ∑ x : Fin r, α x.succ * φ (v x.succ i) := by
        simp only [mul_sub, Finset.sum_sub_distrib, ← mul_assoc, ← Finset.sum_mul, neg_mul]
        ring
      rw [hident]
      exact hi
    have hsucc_zero : ∀ t : Fin r, α t.succ = 0 := hwK (fun t => α t.succ) hα_w
    intro s
    refine Fin.cases ?_ hsucc_zero s
    rw [hα_i0]
    simp [hsucc_zero]

/-- If `U ≤ (I → F)` is mapped coordinatewise by `φ : F →+* K` into `W ≤ (I → K)` (`[Fintype I]`),
then `finrank F U ≤ finrank K W`. -/
theorem finrank_le_of_pi_ringHom {F K I : Type*} [Field F] [Field K] [Fintype I]
    (φ : F →+* K)
    (U : Submodule F (I → F)) (W : Submodule K (I → K))
    (hUW : ∀ x ∈ U, (fun i => φ (x i)) ∈ W) :
    finrank F U ≤ finrank K W := by
  let r := finrank F U
  let B := Module.finBasis F U
  have hB_lin : LinearIndependent F (fun t : Fin r => (B t : I → F)) :=
    B.linearIndependent.map' U.subtype U.ker_subtype
  have hBK_lin : LinearIndependent K (fun t : Fin r => (fun i => φ ((B t : I → F) i))) :=
    linearIndependent_fin_pi_ringHom φ _ hB_lin
  let vecW : Fin r → W := fun t => ⟨fun i => φ ((B t : I → F) i), hUW (B t).1 (B t).2⟩
  have hvecW_lin : LinearIndependent K vecW := by
    rw [Fintype.linearIndependent_iff] at hBK_lin ⊢
    intro c hc
    apply hBK_lin c
    have hc' := congrArg Subtype.val hc
    simpa [vecW] using hc'
  simpa [r] using hvecW_lin.fintype_card_le_finrank

/-- Canonical `K`-linear extension of `L : (I → F) →ₗ[F] (J → F)` (`[Fintype I]`) along a field
homomorphism `φ : F →+* K`. -/
def extendLinearMapPi {F K I J : Type*} [Field F] [Field K] [Fintype I] [DecidableEq I]
    (φ : F →+* K) (L : (I → F) →ₗ[F] (J → F)) : (I → K) →ₗ[K] (J → K) where
  toFun y j := ∑ i : I, φ (L (Pi.single i 1) j) * y i
  map_add' y₁ y₂ := by
    funext j
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c y := by
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => by ring

/-- `extendLinearMapPi φ L` commutes with coordinatewise application of `φ`. -/
theorem extendLinearMapPi_comp_map {F K I J : Type*} [Field F] [Field K]
    [Fintype I] [DecidableEq I]
    (φ : F →+* K) (L : (I → F) →ₗ[F] (J → F)) (x : I → F) :
    extendLinearMapPi φ L (fun i => φ (x i)) = fun j => φ (L x j) := by
  funext j
  have hx : x = ∑ i : I, x i • Pi.single i (1 : F) := by
    funext i'
    simp [Pi.single_apply]
  conv_rhs => rw [hx, map_sum]
  simp only [extendLinearMapPi, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply,
    LinearMap.map_smul, Pi.smul_apply, smul_eq_mul, map_sum, map_mul]
  refine Finset.sum_congr rfl fun i _ => mul_comm _ _

end FieldHomLinearTransfer

end BoundedArityDecoders
