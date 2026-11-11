import SharedDecoders.CompositionColumnAmbient
import SharedDecoders.CompositionSpectralRecurrence

/-! # Rank deficit of actual two-stage maps over a splitting field

The one band is intersected with the actual correct intermediate space. Its
lost dimension is bounded by the single global rank error.
-/

namespace SharedDecoders

open Module
open scoped BigOperators

variable {F κ₁ κ₂ : Type*} [Field F] [Fintype κ₂]
  {d b k m : ℕ} [NeZero d]

lemma swap_error_rank (K₁ K₂ : State d (Fin b → F) →ₗ[F] State d (Fin b → F)) :
    finrank F (LinearMap.range (LinearMap.id - (swapLinear F).comp (K₂.comp K₁))) =
      finrank F (LinearMap.range (swapLinear F - K₂.comp K₁)) := by
  let E := swapLinear F - K₂.comp K₁
  let e : State d (Fin b → F) ≃ₗ[F] State d (Fin b → F) := {
    toFun := swap
    invFun := swap
    left_inv := swap_swap
    right_inv := swap_swap
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  have he : LinearMap.id - (swapLinear F).comp (K₂.comp K₁) = e.toLinearMap.comp E := by
    ext X i c l
    rfl
  rw [he, LinearMap.range_comp]
  exact e.finrank_map_eq (LinearMap.range E)

/-- A monochromatic progression and an actual character band bound the single
rank error. The character is injective on the cyclic group; no band or row
ambient is assumed as an extra certificate. -/
theorem twoHop_rank_progression
    (χ : AddChar (ZMod d) F) (hχ : Function.Injective χ)
    (p₁ : ZMod d → κ₁) (p₂ : ZMod d → κ₂)
    (K₁ K₂ : State d (Fin b → F) →ₗ[F] State d (Fin b → F))
    (hK₁ : LinearClassUniform p₁ K₁) (hK₂ : LinearClassUniform p₂ K₂)
    (hk : 0 < k) (hm : 0 < m) (hkd : k ≤ d)
    (a s : ℕ) (hs : 0 < s) (hsep : (k - 1) * s < d)
    (hmono : ∀ j < (m + 1) * k - 1,
      p₁ ((a : ZMod d) + (j : ZMod d) * (s : ZMod d)) = p₁ (a : ZMod d)) :
    m * (k * d * b) ≤
      m * finrank F (LinearMap.range (swapLinear F - K₂.comp K₁)) +
      d * (Fintype.card κ₂ * k * b) +
      (m - 1) * ((k * s) * (Fintype.card κ₂ * k * b)) := by
  classical
  have hellEq : ((m + 1) * k - 1) + 1 = m * k + k := by
    rw [Nat.sub_add_cancel (by nlinarith : 1 ≤ (m + 1) * k)]
    ring
  obtain ⟨f₁, hf₁⟩ := hK₁
  let H := bandRowSpace (b := b) χ p₂ k
  let V := ColumnAmbient H
  let E := bandMap (b := b) χ k
  let B := (swapLinear F).comp K₂
  let Q := LinearMap.ker ((LinearMap.id - K₁.comp B).comp E)
  let P : Q →ₗ[F] V := (bandPull χ p₂ K₂ hK₂).comp Q.subtype
  let W := LinearMap.range P
  let R : V →ₗ[F] V := channelRotation (s : ZMod d)
  let L : V →ₗ[F] (ZMod d → Fin b → F) := (f₁ (p₁ (a : ZMod d))).comp
    ((rotLinear F (a : ZMod d)).comp (columnAmbientEmbed H))
  let lam : Fin k → F := fun ν => χ ((ν.val : ZMod d) * (s : ZMod d))
  have hlam : Function.Injective lam := by
    intro ν μ heq
    have he := congrArg ZMod.val (hχ heq)
    have hnν : ν.val * s < d := lt_of_le_of_lt
      (Nat.mul_le_mul_right s (by omega : ν.val ≤ k - 1)) hsep
    have hnμ : μ.val * s < d := lt_of_le_of_lt
      (Nat.mul_le_mul_right s (by omega : μ.val ≤ k - 1)) hsep
    have hh : ν.val * s = μ.val * s := by
      simpa [← Nat.cast_mul, ZMod.val_natCast, Nat.mod_eq_of_lt hnν,
        Nat.mod_eq_of_lt hnμ] using he
    apply Fin.ext
    exact Nat.eq_of_mul_eq_mul_right hs hh
  have hP : Function.Injective P := by
    intro x y h
    apply band_correct_map_injective K₁ B E (bandMap_injective χ hχ hkd)
    exact congrArg (columnAmbientEmbed H) h
  have hdim := band_correct_dimension K₁ B E
  have hdimW : k * d * b ≤ finrank F W +
      finrank F (LinearMap.range (swapLinear F - K₂.comp K₁)) := by
    rw [LinearMap.finrank_range_of_inj hP]
    have he : (LinearMap.id - B.comp K₁) =
        LinearMap.id - (swapLinear F).comp (K₂.comp K₁) := by rfl
    rw [he, swap_error_rank] at hdim
    simpa [Module.finrank_pi_fintype, ZMod.card, mul_assoc] using hdim
  have hwitness (x : V) (hx : x ∈ W) :
      ∃ u : Fin k → ZMod d → Fin b → F,
        K₁ (columnAmbientEmbed H x) = E u ∧
        columnAmbientEmbed H x = B (E u) := by
    obtain ⟨u, rfl⟩ := hx
    refine ⟨u.val, ?_, rfl⟩
    exact (sub_eq_zero.mp u.property).symm
  have hobs (x : V) (u : Fin k → ZMod d → Fin b → F)
      (hu : K₁ (columnAmbientEmbed H x) = E u)
      (j : ℕ) (hj : j < (m + 1) * k - 1) :
      L ((R ^ j) x) = ∑ ν, lam ν ^ j • (χ ((ν.val : ZMod d) * (a : ZMod d)) • u ν) := by
    change f₁ (p₁ (a : ZMod d)) (rot (a : ZMod d)
      (columnAmbientEmbed H ((channelRotation (F := F) (s : ZMod d) ^ j) x))) = _
    rw [columnAmbientEmbed_rotation_pow, rot_rot, ← hmono j hj]
    funext i l
    have he := congrFun (congrFun (congrFun hu i)
      ((a : ZMod d) + (j : ZMod d) * (s : ZMod d))) l
    rw [hf₁] at he
    rw [he]
    change (∑ ν, χ ((ν.val : ZMod d) *
      ((a : ZMod d) + (j : ZMod d) * (s : ZMod d))) * u ν i l) = _
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro ν _
    have hc : χ ((ν.val : ZMod d) * ((j : ZMod d) * (s : ZMod d))) = lam ν ^ j := by
      rw [mul_left_comm, mul_comm (j : ZMod d)]
      exact character_nat_mul χ _ j
    rw [mul_add, χ.map_add_eq_mul, hc]
    ring
  have hinj : ∀ x ∈ W, stackedObservations R L k x = 0 → x = 0 := by
    intro x hx hz
    obtain ⟨u, hu, hxu⟩ := hwitness x hx
    have hu0 : u = 0 := by
      funext ν i l
      have hv : (fun μ : Fin k => χ ((μ.val : ZMod d) * (a : ZMod d)) * u μ i l) = 0 := by
        apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hlam
        intro j
        have he := congrFun (congrFun (congrFun hz j) i) l
        rw [stackedObservations_apply, hobs x u hu j.val (by nlinarith [j.isLt])] at he
        simpa [Finset.sum_apply, mul_comm, mul_left_comm, mul_assoc] using he
      have he := congrFun hv ν
      exact (mul_eq_zero.mp he).resolve_left (χ.val_isUnit _).ne_zero
    apply columnAmbientEmbed_injective H
    rw [hxu, hu0, map_zero, map_zero, map_zero]
  have hrec : ∀ j : ℕ, j + 2 ≤ m * k → ∀ x ∈ W,
      L ((R ^ j) (boundedPolynomial R (rootCoefficients lam) x)) = 0 := by
    intro j hj x hx
    obtain ⟨u, hu, _⟩ := hwitness x hx
    apply exponential_observations_recurrence R L lam x
      (fun ν => χ ((ν.val : ZMod d) * (a : ZMod d)) • u ν)
      (ell := (m + 1) * k - 1) (by nlinarith)
    exact hobs x u hu
  have hg := recurrence_finrank_le R W L hk hm (rootCoefficients lam) hinj hrec
  have hker := polynomial_channel_kernel_finrank_le (F := F) (I := Unit)
    (A := H) (d := d) hs (rootCoefficients lam) (rootCoefficients_monic lam)
  have hH := bandRowSpace_finrank_le (b := b) χ p₂ k
  have hV : finrank F V = d * finrank F H := columnAmbient_finrank H
  have hker' : finrank F (LinearMap.ker (boundedPolynomial R (rootCoefficients lam))) ≤
      (k * s) * finrank F H := by simpa only [Fintype.card_unit, one_mul] using hker
  have hresult := hg.trans (Nat.add_le_add (le_of_eq hV)
    (Nat.mul_le_mul_left (m - 1) hker'))
  have hupper := Nat.add_le_add (Nat.mul_le_mul_left d hH)
    (Nat.mul_le_mul_left (m - 1) (Nat.mul_le_mul_left (k * s) hH))
  have hfinal := hresult.trans hupper
  nlinarith [Nat.mul_le_mul_left m hdimW]


/-- The explicit Ramsey-interval rank bound over any field already containing
an injective character of the cyclic coordinate group. -/
theorem twoHop_rank_interval
    (χ : AddChar (ZMod d) F) (hχ : Function.Injective χ)
    (p₁ : ZMod d → κ₁) (p₂ : ZMod d → κ₂)
    (K₁ K₂ : State d (Fin b → F) →ₗ[F] State d (Fin b → F))
    (hK₁ : ClassUniform p₁ K₁) (hK₂ : ClassUniform p₂ K₂)
    (hk : 0 < k) (N : ℕ) (hNd : N ≤ d)
    (hRamsey : ∀ C : ℕ → κ₁, ∃ a s : ℕ, 0 < s ∧
      ∀ j < (2 * Fintype.card κ₂ + 1) * k - 1,
        a + s * j < N ∧ C (a + s * j) = C a) :
    b * k * (d - N + 1) ≤ 2 * finrank F (LinearMap.range (swapLinear F - K₂.comp K₁)) := by
  classical
  let M := Fintype.card κ₂
  let ell := (2 * M + 1) * k - 1
  have hM : 0 < M := Fintype.card_pos_iff.mpr ⟨p₂ 0⟩
  have hellEq : ell + 1 = (2 * M + 1) * k := Nat.sub_add_cancel (by nlinarith)
  have hell : 0 < ell := by nlinarith
  have hkell : k ≤ ell := by nlinarith
  obtain ⟨a, s, hs, hprog⟩ := hRamsey (fun n => p₁ (n : ZMod d))
  change ∀ j < ell, a + s * j < N ∧ p₁ ((a + s * j : ℕ) : ZMod d) = p₁ (a : ZMod d) at hprog
  have hlast := (hprog (ell - 1) (by omega)).1
  have hstep : (ell - 1) * s ≤ N - 1 := by
    have h : s * (ell - 1) ≤ N - 1 := by omega
    simpa [mul_comm] using h
  have hellN : ell ≤ N := by
    have hmult := Nat.mul_le_mul_left (ell - 1) hs
    nlinarith [Nat.sub_add_cancel (by omega : 1 ≤ ell)]
  have hsep : (k - 1) * s < d := by
    have hks := Nat.mul_le_mul_right s (by omega : k - 1 ≤ ell - 1)
    omega
  have hmono : ∀ j < (2 * M + 1) * k - 1,
      p₁ ((a : ZMod d) + (j : ZMod d) * (s : ZMod d)) = p₁ (a : ZMod d) := by
    intro j hj
    simpa [Nat.cast_add, Nat.cast_mul, mul_comm] using (hprog j hj).2
  have hg := twoHop_rank_progression χ hχ p₁ p₂ K₁ K₂
    (linearClassUniform_of_classUniform p₁ K₁ hK₁)
    (linearClassUniform_of_classUniform p₂ K₂ hK₂)
    hk (by omega : 0 < 2 * M) (hkell.trans (hellN.trans hNd)) a s hs hsep hmono
  let r := finrank F (LinearMap.range (swapLinear F - K₂.comp K₁))
  have hbase : b * k * d ≤ 2 * r + (2 * M - 1) * b * k * k * s := by
    have hscaled : M * (b * k * d) ≤
        M * (2 * r + (2 * M - 1) * b * k * k * s) := by
      dsimp [M, r] at *
      nlinarith
    exact Nat.le_of_mul_le_mul_left hscaled hM
  have hcoeff : (2 * M - 1) * k ≤ ell - 1 := by
    have he₁ := Nat.sub_add_cancel (by omega : 1 ≤ 2 * M)
    have he₂ := Nat.sub_add_cancel (by omega : 1 ≤ ell)
    nlinarith
  have hpay : (2 * M - 1) * k * s ≤ N - 1 :=
    (Nat.mul_le_mul_right s hcoeff).trans hstep
  have hpay' := Nat.mul_le_mul_left (b * k) hpay
  have hN : 0 < N := lt_of_lt_of_le hell hellN
  have hsplit : d - N + 1 + (N - 1) = d := by omega
  change b * k * (d - N + 1) ≤ 2 * r
  nlinarith

end SharedDecoders
