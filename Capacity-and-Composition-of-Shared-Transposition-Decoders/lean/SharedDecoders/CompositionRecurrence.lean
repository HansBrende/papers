import SharedDecoders.CompositionProgression

/-!
# Polynomial recurrence growth

The same global annihilator is used at every translate.  The theorem prices its
ambient kernel once per growth step, never sums unrelated local error ranks.
-/

namespace SharedDecoders

open Module
open scoped BigOperators

variable {F V Z : Type*} [Field F] [AddCommGroup V] [Module F V]
  [AddCommGroup Z] [Module F Z]

theorem pow_mem_orbitSpan (R : V →ₗ[F] V) (W : Submodule F V)
    {t : ℕ} {x : V} (hx : x ∈ orbitSpan R W t) (j : ℕ) :
    (R ^ j) x ∈ orbitSpan R W (t + j) := by
  induction j with
  | zero => simpa using hx
  | succ j ih =>
      simpa [pow_succ', Module.End.mul_apply, Nat.add_assoc] using
        (map_orbitSpan_le R W (t + j) ⟨(R ^ j) x, ih, rfl⟩)

/-- A polynomial in an endomorphism, with an explicit degree bound. -/
def boundedPolynomial (R : V →ₗ[F] V) {k : ℕ} (coeff : Fin (k + 1) → F) :
    V →ₗ[F] V := ∑ i, coeff i • R ^ i.val

theorem boundedPolynomial_pow (R : V →ₗ[F] V) {k : ℕ}
    (coeff : Fin (k + 1) → F) (j : ℕ) (x : V) :
    boundedPolynomial R coeff ((R ^ j) x) = (R ^ j) (boundedPolynomial R coeff x) := by
  simp only [boundedPolynomial, LinearMap.sum_apply, LinearMap.smul_apply,
    map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  simp only [← Module.End.mul_apply, ← pow_add, Nat.add_comm]

theorem boundedPolynomial_mem (R : V →ₗ[F] V) (W : Submodule F V)
    {k t : ℕ} (coeff : Fin (k + 1) → F) {x : V}
    (hx : x ∈ orbitSpan R W t) :
    boundedPolynomial R coeff x ∈ orbitSpan R W (t + k) := by
  simp only [boundedPolynomial, LinearMap.sum_apply, LinearMap.smul_apply]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  exact orbitSpan_mono R W (by omega) (pow_mem_orbitSpan R W hx i.val)

/-- The first `k` linear observations, as a single linear map. -/
def stackedObservations (R : V →ₗ[F] V) (L : V →ₗ[F] Z) (k : ℕ) :
    V →ₗ[F] (Fin k → Z) := LinearMap.pi (fun i => L.comp (R ^ i.val))

@[simp] theorem stackedObservations_apply (R : V →ₗ[F] V) (L : V →ₗ[F] Z)
    (k : ℕ) (x : V) (i : Fin k) :
    stackedObservations R L k x i = L ((R ^ i.val) x) := rfl

/-- A common polynomial recurrence and an injective stack force block growth. -/
theorem recurrence_finrank_le [FiniteDimensional F V]
    (R : V →ₗ[F] V) (W : Submodule F V) (L : V →ₗ[F] Z)
    {k m : ℕ} (hk : 0 < k) (hm : 0 < m)
    (coeff : Fin (k + 1) → F)
    (hinj : ∀ x ∈ W, stackedObservations R L k x = 0 → x = 0)
    (hrec : ∀ j : ℕ, j + 2 ≤ m * k → ∀ x ∈ W,
      L ((R ^ j) (boundedPolynomial R coeff x)) = 0) :
    m * finrank F W ≤ finrank F V +
      (m - 1) * finrank F (LinearMap.ker (boundedPolynomial R coeff)) := by
  let P := boundedPolynomial R coeff
  let G := stackedObservations R L k
  have hstep : ∀ t, t + k ≤ m * k →
      finrank F W + finrank F (orbitSpan R W t) ≤
        finrank F (orbitSpan R W (t + k)) + finrank F (LinearMap.ker P) := by
    intro t ht
    apply finrank_growth W (orbitSpan R W t) (orbitSpan R W (t + k)) P G
    · exact (self_le_orbitSpan_succ R W 0).trans (orbitSpan_mono R W (by omega))
    · rintro _ ⟨x, hx, rfl⟩
      exact boundedPolynomial_mem R W coeff hx
    · rintro _ ⟨x, hx, rfl⟩
      have hz : orbitSpan R W t ≤ LinearMap.ker (G.comp P) := by
        apply orbitSpan_le_ker
        intro j hj w hw
        ext i
        change L ((R ^ i.val) (P ((R ^ j) w))) = 0
        rw [boundedPolynomial_pow]
        rw [← Module.End.mul_apply, ← pow_add]
        exact hrec (i.val + j) (by omega) w hw
      exact hz hx
    · exact hinj
  have hgrow : ∀ n, n + 1 ≤ m →
      (n + 1) * finrank F W ≤ finrank F (orbitSpan R W ((n + 1) * k)) +
        n * finrank F (LinearMap.ker P) := by
    intro n
    induction n with
    | zero =>
        intro _
        rw [show (0 + 1 : ℕ) = 1 from rfl, one_mul, one_mul, zero_mul, add_zero]
        apply Submodule.finrank_mono
        exact (self_le_orbitSpan_succ R W 0).trans (orbitSpan_mono R W hk)
    | succ n ih =>
        intro hn
        have hi := ih (by omega)
        have ht : (n + 1) * k + k ≤ m * k := by nlinarith
        have hs := hstep ((n + 1) * k) ht
        have he : (n + 1) * k + k = (n + 2) * k := by ring
        rw [he] at hs
        change (n + 2) * finrank F W ≤ finrank F (orbitSpan R W ((n + 2) * k)) +
          (n + 1) * finrank F (LinearMap.ker P)
        nlinarith
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  have hg := hgrow n le_rfl
  have ha := (orbitSpan R W ((n + 1) * k)).finrank_le
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel] at *
  exact hg.trans (Nat.add_le_add_right ha _)

end SharedDecoders
