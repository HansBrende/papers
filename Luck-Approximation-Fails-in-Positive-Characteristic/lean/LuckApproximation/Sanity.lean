import LuckApproximation.Statement
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Data.Int.Star
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Topology.Metrizable.Uniformity

/-!
# Sanity checks for `LuckApproximation.Statement`

* `phi_apply`: `φ_A^{G/N}` is `x ↦ x A`, with the entries of `A` mapped to `K[G/N]`.
* `finrank_domain`, `rk_le`, `rk_eq_sub`, `rk_one`: `dim_K K[G/N]^n = n |G : N|`, `rk ≤ n`, the
  survey's formula (1), `rk_{G/N}(A) = n − dim_K ker φ_A^{G/N} / |G : N|`, and `rk(Iₙ) = n`.
* `intChain`: a chain in `ℤ` (`2ⁱℤ`), so `Chain` is satisfiable. `PChain.lean` constructs chains with
  `p`-group quotients in free groups of finite rank. `SemanticChecks.lean` computes a non-trivial limit
  along `intChain`.
* `luckApproximation_iff`: parts (1) and (2) together say that for each matrix one number is the
  limit along every chain.
* `not_conjecture_of_target`: `MainTheoremTarget` disproves the conjecture.
-/

namespace Luck

open Filter Topology

section Rank

variable (K : Type*) [Field K] {G : Type*} [Group G]

theorem phi_apply (N : Subgroup G) [N.Normal] {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) (MonoidAlgebra K G)) (x : Fin n → MonoidAlgebra K (G ⧸ N))
    (j : Fin m) :
    phi K N A x j = ∑ i, x i * MonoidAlgebra.mapDomainRingHom K (QuotientGroup.mk' N) (A i j) :=
  rfl

theorem finiteDimensional_quotient (N : Subgroup G) [N.Normal] [N.FiniteIndex] :
    Module.Finite K (MonoidAlgebra K (G ⧸ N)) :=
  haveI : Finite (G ⧸ N) := Subgroup.finite_quotient_of_finiteIndex
  Module.Finite.of_basis (MonoidAlgebra.basis (G ⧸ N) K)

theorem finrank_domain (N : Subgroup G) [N.Normal] [N.FiniteIndex] (n : ℕ) :
    Module.finrank K (Fin n → MonoidAlgebra K (G ⧸ N)) = n * N.index := by
  have := finiteDimensional_quotient K N
  have hQ : Module.finrank K (MonoidAlgebra K (G ⧸ N)) = N.index := by
    rw [Module.finrank_eq_nat_card_basis (MonoidAlgebra.basis (G ⧸ N) K),
      Subgroup.index_eq_card]
  rw [Module.finrank_pi_fintype, hQ]
  simp

theorem rk_le (N : Subgroup G) [N.Normal] [N.FiniteIndex] {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) (MonoidAlgebra K G)) : rk K N A ≤ n := by
  have := finiteDimensional_quotient K N
  have h := LinearMap.finrank_range_le (phi K N A)
  rw [finrank_domain] at h
  have hidx : (0 : ℝ) < N.index := by
    exact_mod_cast Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  unfold rk
  rw [div_le_iff₀ hidx]
  exact_mod_cast h

theorem rk_eq_sub (N : Subgroup G) [N.Normal] [N.FiniteIndex] {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) (MonoidAlgebra K G)) :
    rk K N A = n - (Module.finrank K (LinearMap.ker (phi K N A)) : ℝ) / N.index := by
  have := finiteDimensional_quotient K N
  have h := LinearMap.finrank_range_add_finrank_ker (phi K N A)
  rw [finrank_domain] at h
  have hidx : (N.index : ℝ) ≠ 0 := by exact_mod_cast Subgroup.FiniteIndex.index_ne_zero
  unfold rk
  rw [eq_sub_iff_add_eq, ← add_div, div_eq_iff hidx]
  exact_mod_cast h

/-- The identity matrix has `rk = n` at every level, so the normalisation is right and `rk` is not
degenerate. -/
theorem rk_one (N : Subgroup G) [N.Normal] [N.FiniteIndex] (n : ℕ) :
    rk K N (1 : Matrix (Fin n) (Fin n) (MonoidAlgebra K G)) = n := by
  have hphi : phi K N (1 : Matrix (Fin n) (Fin n) (MonoidAlgebra K G)) = LinearMap.id := by
    refine LinearMap.ext fun x => ?_
    show Matrix.vecMul x (quotientMatrix K N 1) = x
    rw [quotientMatrix, Matrix.map_one _ (map_zero _) (map_one _), Matrix.vecMul_one]
  have := finiteDimensional_quotient K N
  unfold rk
  rw [hphi, LinearMap.range_id, finrank_top, finrank_domain]
  have hidx : (N.index : ℝ) ≠ 0 := by exact_mod_cast Subgroup.FiniteIndex.index_ne_zero
  push_cast
  field_simp

end Rank

/-- Chains exist: the subgroups `2ⁱℤ` of `ℤ`, written multiplicatively. -/
noncomputable def intChain : Chain (Multiplicative ℤ) where
  N i := AddSubgroup.toSubgroup (AddSubgroup.zmultiples ((2 : ℤ) ^ i))
  normal _ := Subgroup.normal_of_isMulCommutative _
  finiteIndex i := ⟨by
    rw [AddSubgroup.index_toSubgroup, Int.index_zmultiples]
    exact Int.natAbs_ne_zero.mpr (pow_ne_zero _ two_ne_zero)⟩
  strictAnti := by
    intro i j hij
    apply AddSubgroup.toSubgroup.strictMono
    refine lt_of_le_of_ne (Int.zmultiples_le_zmultiples_iff.mpr (pow_dvd_pow 2 hij.le)) ?_
    intro h
    have hdvd : (2 : ℤ) ^ j ∣ 2 ^ i := Int.zmultiples_le_zmultiples_iff.mp h.ge
    have hle := Int.le_of_dvd (by positivity) hdvd
    have hlt : (2 : ℤ) ^ i < 2 ^ j := pow_lt_pow_right₀ (by norm_num) hij
    linarith
  iInf_eq_bot := by
    rw [← OrderIso.map_iInf, ← AddSubgroup.toSubgroup.map_bot]
    congr 1
    rw [eq_bot_iff]
    intro x hx
    rw [AddSubgroup.mem_iInf] at hx
    have hdvd : (2 : ℤ) ^ x.natAbs ∣ x := Int.mem_zmultiples_iff.mp (hx x.natAbs)
    have hlt : x.natAbs < ((2 : ℤ) ^ x.natAbs).natAbs := by
      rw [Int.natAbs_pow]
      exact Nat.lt_two_pow_self
    exact (AddSubgroup.mem_bot).mpr (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd hlt)

/-- Parts (1) and (2) together: for each matrix, one number is the limit along every chain. -/
theorem luckApproximation_iff (K : Type*) [Field K] (G : Type*) [Group G] :
    LuckApproximation K G ↔ ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) (MonoidAlgebra K G)),
      ∃ l : ℝ, ∀ c : Chain G, Tendsto (c.rkSeq K A) atTop (𝓝 l) := by
  constructor
  · rintro ⟨hconv, hind⟩ n m A
    by_cases h : Nonempty (Chain G)
    · obtain ⟨c₀⟩ := h
      obtain ⟨l, hl⟩ := hconv n m A c₀
      refine ⟨l, fun c => ?_⟩
      obtain ⟨l', hl'⟩ := hconv n m A c
      rw [hind n m A c₀ c l l' hl hl']
      exact hl'
    · exact ⟨0, fun c => (h ⟨c⟩).elim⟩
  · intro h
    refine ⟨fun n m A c => ?_, fun n m A c₁ c₂ l₁ l₂ h₁ h₂ => ?_⟩
    · obtain ⟨l, hl⟩ := h n m A
      exact ⟨l, hl c⟩
    · obtain ⟨l, hl⟩ := h n m A
      exact (tendsto_nhds_unique h₁ (hl c₁)).trans (tendsto_nhds_unique (hl c₂) h₂)

/-- The target `MainTheoremTarget` disproves the conjecture. -/
theorem not_conjecture_of_target (h : MainTheoremTarget) : ¬ LuckApproximationConjecture := by
  obtain ⟨r, hr⟩ := h
  intro hc
  exact hr (hc (ZMod 3) (FreeGroup (Fin r)))

end Luck
