import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/-!
# Growth of a common-message subspace

A single linear decoder that recovers the same injective message on consecutive
translates forces dimension growth.  The fixed-space term is retained explicitly.
The ambient endomorphism need not be invertible.
-/

namespace SharedDecoders

open Module

variable {F V Z : Type*} [Field F] [AddCommGroup V] [Module F V]
  [AddCommGroup Z] [Module F Z]

/-- The span of the first `n` translates of `W` under `R`. -/
def orbitSpan (R : V →ₗ[F] V) (W : Submodule F V) : ℕ → Submodule F V
  | 0 => ⊥
  | n + 1 => W ⊔ (orbitSpan R W n).map R

@[simp] theorem orbitSpan_zero (R : V →ₗ[F] V) (W : Submodule F V) :
    orbitSpan R W 0 = ⊥ := rfl

@[simp] theorem orbitSpan_succ (R : V →ₗ[F] V) (W : Submodule F V) (n : ℕ) :
    orbitSpan R W (n + 1) = W ⊔ (orbitSpan R W n).map R := rfl

@[simp] theorem orbitSpan_one (R : V →ₗ[F] V) (W : Submodule F V) :
    orbitSpan R W 1 = W := by simp

theorem orbitSpan_mono (R : V →ₗ[F] V) (W : Submodule F V) :
    Monotone (orbitSpan R W) := by
  apply monotone_nat_of_le_succ
  intro n
  induction n with
  | zero => exact bot_le
  | succ n ih =>
      exact sup_le_sup_left (Submodule.map_mono ih) W

theorem self_le_orbitSpan_succ (R : V →ₗ[F] V) (W : Submodule F V) (n : ℕ) :
    W ≤ orbitSpan R W (n + 1) := le_sup_left

theorem map_orbitSpan_le (R : V →ₗ[F] V) (W : Submodule F V) (n : ℕ) :
    (orbitSpan R W n).map R ≤ orbitSpan R W (n + 1) := le_sup_right

/-- A linear map vanishing on each generating translate vanishes on their span. -/
theorem orbitSpan_le_ker (R : V →ₗ[F] V) (W : Submodule F V) (n : ℕ)
    (L : V →ₗ[F] Z)
    (h : ∀ j < n, ∀ x ∈ W, L ((R ^ j) x) = 0) :
    orbitSpan R W n ≤ LinearMap.ker L := by
  induction n generalizing L with
  | zero => exact bot_le
  | succ n ih =>
      apply sup_le
      · intro x hx
        simpa using h 0 (Nat.zero_lt_succ n) x hx
      · rintro _ ⟨x, hx, rfl⟩
        apply ih (L.comp R) ?_ hx
        intro j hj x hx
        simpa [LinearMap.comp_apply, pow_succ', Module.End.mul_apply] using
          h (j + 1) (Nat.succ_lt_succ hj) x hx

/-- Rank-nullity for a restriction, with the full ambient kernel as an upper bound. -/
theorem finrank_le_map_add_ker [FiniteDimensional F V]
    (P : V →ₗ[F] V) (W : Submodule F V) :
    finrank F W ≤ finrank F (W.map P) + finrank F (LinearMap.ker P) := by
  let Q : LinearMap.ker (P.domRestrict W) →ₗ[F] LinearMap.ker P :=
    { toFun := fun x => ⟨x.1.1, x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hQ : Function.Injective Q := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : LinearMap.ker P => (z : V)) hxy
  have hk := LinearMap.finrank_le_finrank_of_injective hQ
  have hr := (P.domRestrict W).finrank_range_add_finrank_ker
  have he : LinearMap.range (P.domRestrict W) = W.map P := by
    ext x
    simp
  rw [he] at hr
  omega

/-- One growth step, using an actual annihilator and one ambient kernel bill. -/
theorem finrank_growth [FiniteDimensional F V]
    (W A B : Submodule F V) (P : V →ₗ[F] V) (L : V →ₗ[F] Z)
    (hW : W ≤ B) (hP : A.map P ≤ B)
    (hzero : A.map P ≤ LinearMap.ker L)
    (hinj : ∀ x ∈ W, L x = 0 → x = 0) :
    finrank F W + finrank F A ≤ finrank F B + finrank F (LinearMap.ker P) := by
  have hd : Disjoint W (A.map P) := by
    rw [Submodule.disjoint_def]
    intro x hx hx'
    exact hinj x hx (hzero hx')
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq W (A.map P)
  rw [hd.eq_bot, finrank_bot, add_zero] at hdim
  have hle : finrank F (W ⊔ A.map P : Submodule F V) ≤ finrank F B :=
    Submodule.finrank_mono (sup_le hW hP)
  have hr := finrank_le_map_add_ker P A
  omega

/-- The common-message progression bound.  Only the listed linear observations
are assumed equal; all dimension growth and the fixed-space correction are proved. -/
theorem commonMessage_finrank_le [FiniteDimensional F V]
    (R : V →ₗ[F] V) (W : Submodule F V) (L : V →ₗ[F] Z)
    (ell : ℕ) (hell : 0 < ell)
    (hinj : ∀ x ∈ W, L x = 0 → x = 0)
    (hmessage : ∀ j < ell, ∀ x ∈ W, L ((R ^ j) x) = L x) :
    ell * finrank F W ≤ finrank F V +
      (ell - 1) * finrank F (LinearMap.ker (R - LinearMap.id)) := by
  let P := R - LinearMap.id
  have hstep : ∀ n, n + 1 < ell →
      finrank F W + finrank F (orbitSpan R W (n + 1)) ≤
        finrank F (orbitSpan R W (n + 2)) + finrank F (LinearMap.ker P) := by
    intro n hn
    apply finrank_growth W (orbitSpan R W (n + 1)) (orbitSpan R W (n + 2)) P L
    · exact self_le_orbitSpan_succ R W (n + 1)
    · rintro _ ⟨x, hx, rfl⟩
      exact (orbitSpan R W (n + 2)).sub_mem
        (map_orbitSpan_le R W (n + 1) ⟨x, hx, rfl⟩)
        (orbitSpan_mono R W (by omega) hx)
    · rintro _ ⟨x, hx, rfl⟩
      have hz : orbitSpan R W (n + 1) ≤ LinearMap.ker (L.comp P) := by
        apply orbitSpan_le_ker
        intro j hj w hw
        change L ((R - LinearMap.id : V →ₗ[F] V) ((R ^ j) w)) = 0
        simp only [LinearMap.sub_apply, LinearMap.id_apply, map_sub]
        have h1 := hmessage (j + 1) (by omega) w hw
        have h0 := hmessage j (by omega) w hw
        apply sub_eq_zero.mpr
        simpa [pow_succ', Module.End.mul_apply, h0] using h1
      exact hz hx
    · exact hinj
  have hgrow : ∀ n, n + 1 ≤ ell →
      (n + 1) * finrank F W ≤ finrank F (orbitSpan R W (n + 1)) +
        n * finrank F (LinearMap.ker P) := by
    intro n
    induction n with
    | zero =>
        intro _
        rw [show (0 + 1 : ℕ) = 1 from rfl, orbitSpan_one, one_mul, zero_mul, add_zero]
    | succ n ih =>
        intro hn
        have hi := ih (by omega)
        have hs := hstep n (by omega)
        change (n + 2) * finrank F W ≤ finrank F (orbitSpan R W (n + 2)) +
          (n + 1) * finrank F (LinearMap.ker P)
        simp only [add_mul, one_mul] at *
        norm_num at *
        omega
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hell)
  have hg := hgrow n le_rfl
  have ha := (orbitSpan R W (n + 1)).finrank_le
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel] at *
  exact hg.trans (Nat.add_le_add_right ha _)

end SharedDecoders
