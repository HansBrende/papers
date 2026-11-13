import BoundedArityDecoders.ExtensionLinearRunSingleShift
import BoundedArityDecoders.ExtensionLinearRunSharpness

/-!
# Proofs for Result 1, Theorem 1B (`ExtensionLinearRunProofs`)

Proves both specifications of `Theorem 1B` from `BoundedArityDecoders.ExtensionLinearRun`:
* `extension_Theorem1B_TwoClass : Extension_Theorem1B_TwoClassSpec`
* `extension_Theorem1B_MultiClassPrime : Extension_Theorem1B_MultiClassPrimeSpec`

along with the direct unpacked top-level theorems:
* `linearClassUniform_twoClass_finrank_le`
* `linearClassUniform_multiClass_prime_finrank_le`
-/

namespace BoundedArityDecoders

open Module

/-! ### Section 1: Ambient Dimension, Grassmann Shift-Averaging & Cauchy–Schwarz -/

section ShiftAveragingInfra

private def matFlatEquiv1B (R : Type*) [Semiring R] (d b : ℕ) :
    Matrix (ZMod d) (ZMod d) (Fin b → R) ≃ₗ[R] ((ZMod d × ZMod d × Fin b) → R) where
  toFun X idx := X idx.1 idx.2.1 idx.2.2
  invFun f := Matrix.of fun i j u => f (i, j, u)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private lemma finrank_matrix_lane (F : Type*) [Field F] (d b : ℕ) [NeZero d] :
    finrank F (Matrix (ZMod d) (ZMod d) (Fin b → F)) = b * d ^ 2 := by
  rw [LinearEquiv.finrank_eq (matFlatEquiv1B F d b), Module.finrank_pi,
    Fintype.card_prod, Fintype.card_prod, ZMod.card, Fintype.card_fin]
  ring

private def laneRotEquiv (F : Type*) [Semiring F] {d b : ℕ} (s : ZMod d) :
    Matrix (ZMod d) (ZMod d) (Fin b → F) ≃ₗ[F] Matrix (ZMod d) (ZMod d) (Fin b → F) where
  toFun := laneRot s
  invFun := laneRot (-s)
  left_inv X := by
    ext i j u
    simp [laneRot_apply]
  right_inv X := by
    ext i j u
    simp [laneRot_apply]
  map_add' := (laneRot s).map_add'
  map_smul' := (laneRot s).map_smul'

private lemma comap_laneRot_eq_map {F : Type*} [Field F] {d b : ℕ}
    (𝒳 : Submodule F (Matrix (ZMod d) (ZMod d) (Fin b → F))) (s : ZMod d) :
    𝒳.comap (laneRot s) = 𝒳.map (laneRotEquiv F (-s)).toLinearMap := by
  ext X
  simp only [Submodule.mem_comap, Submodule.mem_map]
  constructor
  · intro hX
    refine ⟨laneRot s X, hX, ?_⟩
    ext i j u
    simp [laneRotEquiv, laneRot_apply]
  · rintro ⟨Y, hY, rfl⟩
    have hcancel : laneRot s ((laneRotEquiv F (-s)).toLinearMap Y) = Y := by
      ext i j u
      simp [laneRotEquiv, laneRot_apply]
    rwa [hcancel]

private lemma grassmann_shift_finrank_le {F : Type*} [Field F] {d b : ℕ} [NeZero d]
    (𝒳 : Submodule F (Matrix (ZMod d) (ZMod d) (Fin b → F))) (s : ZMod d) :
    2 * finrank F 𝒳 ≤ b * d ^ 2 + finrank F ↥(𝒳 ⊓ 𝒳.comap (laneRot s)) := by
  have hcomap : finrank F ↥(𝒳.comap (laneRot s)) = finrank F 𝒳 := by
    rw [comap_laneRot_eq_map]
    exact LinearEquiv.finrank_map_eq (laneRotEquiv F (-s)) 𝒳
  have hgrass := Submodule.finrank_sup_add_finrank_inf_eq 𝒳 (𝒳.comap (laneRot s))
  have hsup_le :
      finrank F ↥(𝒳 ⊔ 𝒳.comap (laneRot s)) ≤ b * d ^ 2 :=
    (Submodule.finrank_le _).trans (le_of_eq (finrank_matrix_lane F d b))
  omega

private lemma shift_avg_finrank_real_le {F : Type*} [Field F] {d b : ℕ} [NeZero d]
    (𝒳 : Submodule F (Matrix (ZMod d) (ZMod d) (Fin b → F))) :
    (2 * (d : ℝ)) * (finrank F 𝒳 : ℝ) ≤
      (b : ℝ) * (d : ℝ) ^ 3 +
        ∑ s : ZMod d, (finrank F ↥(𝒳 ⊓ 𝒳.comap (laneRot s)) : ℝ) := by
  have hsum_nat :
      ∑ _s : ZMod d, (2 * finrank F 𝒳) ≤
        ∑ s : ZMod d, (b * d ^ 2 + finrank F ↥(𝒳 ⊓ 𝒳.comap (laneRot s))) :=
    Finset.sum_le_sum fun s _ => grassmann_shift_finrank_le 𝒳 s
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, ZMod.card,
    smul_eq_mul] at hsum_nat
  have hreal : ((d * (2 * finrank F 𝒳) : ℕ) : ℝ) ≤
      ((d * (b * d ^ 2) + ∑ s : ZMod d, finrank F ↥(𝒳 ⊓ 𝒳.comap (laneRot s)) : ℕ) : ℝ) := by
    exact_mod_cast hsum_nat
  push_cast at hreal
  linarith

private lemma coprimeToChar_shiftOrbitLen_of_dim {F : Type*} [Field F] {d : ℕ} [NeZero d]
    (hchar : CoprimeToChar F d) (s : ZMod d) :
    CoprimeToChar F (shiftOrbitLen d s) := by
  have : NeZero (shiftOrbitLen d s) := ⟨Nat.ne_of_gt (shiftOrbitLen_pos d s)⟩
  rw [coprimeToChar_iff_natCast_ne_zero] at hchar ⊢
  intro hz
  have hmul : ((d : ℕ) : F) = 0 := by
    rw [← shiftGcd_mul_orbitLen d s, Nat.cast_mul, hz, mul_zero]
  exact hchar hmul

private lemma sq_sum_le_card_mul_sum_sq_fintype {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    (∑ i : ι, f i) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i : ι, (f i) ^ 2 := by
  have hnonneg : 0 ≤ ∑ i : ι, ∑ j : ι, (f i - f j) ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hexpand :
      (∑ i : ι, ∑ j : ι, (f i - f j) ^ 2) =
        2 * ((Fintype.card ι : ℝ) * (∑ i : ι, (f i) ^ 2) - (∑ i : ι, f i) ^ 2) := by
    have hterm : ∀ i j : ι, (f i - f j) ^ 2 = (f i) ^ 2 - 2 * (f i * f j) + (f j) ^ 2 :=
      fun _ _ => by ring
    simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have h1 : (∑ i : ι, ∑ _j : ι, (f i) ^ 2) = (Fintype.card ι : ℝ) * ∑ i : ι, (f i) ^ 2 := by
      simp_rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← Finset.mul_sum]
    have h2 : (∑ _i : ι, ∑ j : ι, (f j) ^ 2) = (Fintype.card ι : ℝ) * ∑ j : ι, (f j) ^ 2 := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have h3 : (∑ i : ι, ∑ j : ι, 2 * (f i * f j)) = 2 * (∑ i : ι, f i) ^ 2 := by
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul, sq]
    rw [h1, h2, h3]
    ring
  linarith

private lemma linearClassUniformMaxDim_real_le {F : Type*} [Field F] {d b : ℕ} [NeZero d]
    {κ : Type*} (p : ZMod d → κ) {B : ℝ}
    (hB : ∀ 𝒳 : Submodule F (Matrix (ZMod d) (ZMod d) (Fin b → F)),
      IsLinearClassUniformCode p 𝒳 → (finrank F 𝒳 : ℝ) ≤ B) :
    (linearClassUniformMaxDim F b p : ℝ) ≤ B := by
  let S : Set ℕ := {k : ℕ | ∃ 𝒳 : Submodule F (Matrix (ZMod d) (ZMod d) (Fin b → F)),
    IsLinearClassUniformCode p 𝒳 ∧ finrank F 𝒳 = k}
  have hne : S.Nonempty := by
    refine ⟨0, ⊥, ⟨fun _ => 0, ?_⟩, finrank_bot F _⟩
    intro X hX c
    rw [(Submodule.mem_bot (R := F)).mp hX]
    funext j u
    simp
  have hbdd : BddAbove S := by
    refine ⟨b * d ^ 2, ?_⟩
    rintro k ⟨𝒳, _, rfl⟩
    exact (Submodule.finrank_le 𝒳).trans (le_of_eq (finrank_matrix_lane F d b))
  obtain ⟨𝒳₀, hLin₀, hdim₀⟩ := Nat.sSup_mem hne hbdd
  unfold linearClassUniformMaxDim
  change ((sSup S : ℕ) : ℝ) ≤ B
  rw [← hdim₀]
  exact hB 𝒳₀ hLin₀

end ShiftAveragingInfra

/-! ### Section 2: Orbit Transition Sums & Divisor-Count Bound on `∑_s gcd(d, s)` -/

section CombinatorialSums

private lemma sum_orbitRunCount_eq_shiftTransitionCount {d M : ℕ} [NeZero d]
    (p : ZMod d → Fin M) (s : ZMod d) :
    (∑ a : Fin (shiftGcd d s), ∑ m : Fin M, orbitRunCount p s m a) =
      shiftTransitionCount p s := by
  classical
  let g := shiftGcd d s
  have hg_pos : 0 < g := shiftGcd_pos d s
  unfold orbitRunCount shiftTransitionCount
  have hinner : ∀ a : Fin g,
      (∑ m : Fin M, ((shiftOrbit s a).filter fun c => p c = m ∧ p (c + s) ≠ m).card) =
        ((shiftOrbit s a).filter fun c => p c ≠ p (c + s)).card := by
    intro a
    rw [← Finset.card_biUnion]
    · congr 1
      ext c
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter]
      constructor
      · rintro ⟨m, hc_orb, hpm, hne⟩
        subst m
        exact ⟨hc_orb, hne.symm⟩
      · rintro ⟨hc_orb, hne⟩
        exact ⟨p c, hc_orb, rfl, hne.symm⟩
    · intro m₁ _ m₂ _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro c hc₁ hc₂
      simp only [Finset.mem_filter] at hc₁ hc₂
      exact hne (hc₁.2.1.symm.trans hc₂.2.1)
  simp_rw [hinner]
  rw [← Finset.card_biUnion]
  · congr 1
    ext c
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter, shiftOrbit]
    constructor
    · rintro ⟨_, _, hne⟩
      exact hne
    · intro hne
      exact ⟨⟨c.val % g, Nat.mod_lt _ hg_pos⟩, rfl, hne⟩
  · intro a₁ _ a₂ _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro c hc₁ hc₂
    simp only [Finset.mem_filter, shiftOrbit, Finset.mem_univ, true_and] at hc₁ hc₂
    exact hne (Fin.ext (hc₁.1.symm.trans hc₂.1))

private lemma orbitRunCount_zero_eq_one_twoClass {d : ℕ} [NeZero d]
    (p : ZMod d → Fin 2) (s : ZMod d) (a : Fin (shiftGcd d s)) :
    orbitRunCount p s 0 a = orbitRunCount p s 1 a := by
  classical
  let ind0 : ZMod d → ℤ := fun c => if p c = 0 then 1 else 0
  have hshift_sum :
      (∑ c ∈ shiftOrbit s a, ind0 (c + s)) = ∑ c ∈ shiftOrbit s a, ind0 c := by
    refine Finset.sum_bij (fun c _ => c + s)
      (fun c hc => (mem_shiftOrbit_add_shift_iff s a c).mpr hc)
      (fun c₁ _ c₂ _ h => add_right_cancel h)
      (fun y hy => ⟨y - s, ?_, sub_add_cancel y s⟩)
      (fun _ _ => rfl)
    have hy' : (y - s) + s ∈ shiftOrbit s a := by simpa using hy
    exact (mem_shiftOrbit_add_shift_iff s a (y - s)).mp hy'
  have hdiff_zero : ∑ c ∈ shiftOrbit s a, (ind0 c - ind0 (c + s)) = 0 := by
    rw [Finset.sum_sub_distrib, hshift_sum, sub_self]
  let R0 := (shiftOrbit s a).filter fun c => p c = 0 ∧ p (c + s) ≠ 0
  let R1 := (shiftOrbit s a).filter fun c => p c = 1 ∧ p (c + s) ≠ 1
  have hpoint : ∀ c : ZMod d,
      ind0 c - ind0 (c + s) =
        (if p c = 0 ∧ p (c + s) ≠ 0 then (1 : ℤ) else 0) -
        (if p c = 1 ∧ p (c + s) ≠ 1 then (1 : ℤ) else 0) := by
    intro c
    have hc2 : p c = 0 ∨ p c = 1 := by
      rcases p c with ⟨v, hv⟩
      interval_cases v
      · left; rfl
      · right; rfl
    have hcs2 : p (c + s) = 0 ∨ p (c + s) = 1 := by
      rcases p (c + s) with ⟨v, hv⟩
      interval_cases v
      · left; rfl
      · right; rfl
    rcases hc2 with h | h <;> rcases hcs2 with hs | hs <;>
      simp [ind0, h, hs]
  simp_rw [hpoint, Finset.sum_sub_distrib] at hdiff_zero
  have hsum0 :
      (∑ c ∈ shiftOrbit s a, if p c = 0 ∧ p (c + s) ≠ 0 then (1 : ℤ) else 0) = R0.card := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hsum1 :
      (∑ c ∈ shiftOrbit s a, if p c = 1 ∧ p (c + s) ≠ 1 then (1 : ℤ) else 0) = R1.card := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hsum0, hsum1] at hdiff_zero
  change (orbitRunCount p s 0 a : ℤ) - (orbitRunCount p s 1 a : ℤ) = 0 at hdiff_zero
  omega

private lemma divisors_card_le_two_mul_sqrt (d : ℕ) [NeZero d] :
    d.divisors.card ≤ 2 * Nat.sqrt d := by
  classical
  have hd_pos : 0 < d := NeZero.pos d
  let D_low := d.divisors.filter fun k => k ≤ Nat.sqrt d
  let D_high := d.divisors.filter fun k => ¬ k ≤ Nat.sqrt d
  have hpart : D_low.card + D_high.card = d.divisors.card :=
    Finset.card_filter_add_card_filter_not (fun k => k ≤ Nat.sqrt d)
  have hlow_le : D_low.card ≤ Nat.sqrt d := by
    have hsub : D_low ⊆ Finset.Icc 1 (Nat.sqrt d) := by
      intro k hk
      simp only [D_low, Finset.mem_filter, Nat.mem_divisors] at hk
      simp only [Finset.mem_Icc]
      refine ⟨?_, hk.2⟩
      rcases Nat.eq_zero_or_pos k with rfl | hpos
      · exfalso
        have := zero_dvd_iff.mp hk.1.1
        exact hk.1.2 this
      · exact hpos
    calc D_low.card
        ≤ (Finset.Icc 1 (Nat.sqrt d)).card := Finset.card_le_card hsub
      _ = Nat.sqrt d := by simp
  have hhigh_le : D_high.card ≤ Nat.sqrt d := by
    have hmap_sub : D_high.image (fun k => d / k) ⊆ Finset.Icc 1 (Nat.sqrt d) := by
      intro q hq
      simp only [Finset.mem_image, D_high, Finset.mem_filter, Nat.mem_divisors] at hq
      obtain ⟨k, ⟨⟨hdvd, _⟩, hgt⟩, rfl⟩ := hq
      have hk_gt : Nat.sqrt d + 1 ≤ k := by omega
      have hmul_eq : (d / k) * k = d := Nat.div_mul_cancel hdvd
      have hdiv_pos : 0 < d / k := by
        rcases Nat.eq_zero_or_pos (d / k) with h0 | hpos
        · rw [h0, zero_mul] at hmul_eq
          omega
        · exact hpos
      have hdiv_le : d / k ≤ Nat.sqrt d := by
        by_contra hdiv_gt
        have h1 : Nat.sqrt d + 1 ≤ d / k := by omega
        have hprod : (Nat.sqrt d + 1) * (Nat.sqrt d + 1) ≤ (d / k) * k :=
          Nat.mul_le_mul h1 hk_gt
        rw [hmul_eq] at hprod
        have hlt_sq : d < (Nat.sqrt d + 1) * (Nat.sqrt d + 1) := Nat.lt_succ_sqrt d
        omega
      exact Finset.mem_Icc.mpr ⟨hdiv_pos, hdiv_le⟩
    have hinj : Set.InjOn (fun k : ℕ => d / k) D_high := by
      intro k₁ hk₁ k₂ hk₂ heq
      dsimp only at heq
      simp only [Finset.mem_coe, D_high, Finset.mem_filter, Nat.mem_divisors] at hk₁ hk₂
      have h1 := Nat.div_div_self hk₁.1.1 (NeZero.ne d)
      have h2 := Nat.div_div_self hk₂.1.1 (NeZero.ne d)
      rw [← h1, heq, h2]
    calc D_high.card
        = (D_high.image fun k => d / k).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.Icc 1 (Nat.sqrt d)).card := Finset.card_le_card hmap_sub
      _ = Nat.sqrt d := by simp
  omega

private lemma sum_shiftGcd_le (d : ℕ) [NeZero d] :
    (∑ s : ZMod d, shiftGcd d s) ≤ d * (2 * Nat.sqrt d) := by
  classical
  have hd_pos : 0 < d := NeZero.pos d
  have hbij_range :
      (∑ s : ZMod d, shiftGcd d s) = ∑ x ∈ Finset.range d, Nat.gcd d x := by
    refine Finset.sum_bij (fun (s : ZMod d) _ => s.val)
      (fun s _ => Finset.mem_range.mpr (ZMod.val_lt s))
      (fun s₁ _ s₂ _ h => ZMod.val_injective d h)
      (fun x hx => ⟨(x : ZMod d), Finset.mem_univ _,
        ZMod.val_natCast_of_lt (Finset.mem_range.mp hx)⟩)
      (fun _ _ => rfl)
  rw [hbij_range]
  have hmaps : ∀ x ∈ Finset.range d, Nat.gcd d x ∈ d.divisors :=
    fun x _ => Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left d x, NeZero.ne d⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfiber : ∀ k ∈ d.divisors,
      (∑ x ∈ (Finset.range d).filter (fun x => Nat.gcd d x = k), Nat.gcd d x) ≤ d := by
    intro k hk
    have hdvd : k ∣ d := (Nat.mem_divisors.mp hk).1
    have hk_pos : 0 < k := Nat.pos_of_dvd_of_pos hdvd hd_pos
    have hconst :
        (∑ x ∈ (Finset.range d).filter (fun x => Nat.gcd d x = k), Nat.gcd d x) =
          ((Finset.range d).filter (fun x => Nat.gcd d x = k)).card * k := by
      have hcongr :
          (∑ x ∈ (Finset.range d).filter (fun x => Nat.gcd d x = k), Nat.gcd d x) =
            ∑ _x ∈ (Finset.range d).filter (fun x => Nat.gcd d x = k), k :=
        Finset.sum_congr rfl fun x hx => (Finset.mem_filter.mp hx).2
      rw [hcongr, Finset.sum_const, smul_eq_mul]
    rw [hconst]
    have hsub_img :
        (Finset.range d).filter (fun x => Nat.gcd d x = k) ⊆
          (Finset.range (d / k)).image (fun q => k * q) := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_range] at hx
      simp only [Finset.mem_image, Finset.mem_range]
      have hk_dvd_x : k ∣ x := hx.2 ▸ Nat.gcd_dvd_right d x
      refine ⟨x / k, ?_, Nat.mul_div_cancel' hk_dvd_x⟩
      have hmul_x : k * (x / k) = x := Nat.mul_div_cancel' hk_dvd_x
      have hmul_d : k * (d / k) = d := Nat.mul_div_cancel' hdvd
      by_contra hge
      have hle_q : d / k ≤ x / k := by omega
      have hle_mul : k * (d / k) ≤ k * (x / k) := Nat.mul_le_mul_left k hle_q
      rw [hmul_d, hmul_x] at hle_mul
      omega
    have hcard_le :
        ((Finset.range d).filter (fun x => Nat.gcd d x = k)).card ≤ d / k := by
      calc ((Finset.range d).filter (fun x => Nat.gcd d x = k)).card
          ≤ ((Finset.range (d / k)).image (fun q => k * q)).card :=
            Finset.card_le_card hsub_img
        _ ≤ (Finset.range (d / k)).card := Finset.card_image_le
        _ = d / k := Finset.card_range _
    calc ((Finset.range d).filter (fun x => Nat.gcd d x = k)).card * k
        ≤ (d / k) * k := Nat.mul_le_mul_right k hcard_le
      _ = d := Nat.div_mul_cancel hdvd
  calc (∑ k ∈ d.divisors, ∑ x ∈ (Finset.range d).filter (fun x => Nat.gcd d x = k), Nat.gcd d x)
      ≤ ∑ _k ∈ d.divisors, d := Finset.sum_le_sum hfiber
    _ = d.divisors.card * d := by rw [Finset.sum_const, smul_eq_mul]
    _ = d * d.divisors.card := Nat.mul_comm _ _
    _ ≤ d * (2 * Nat.sqrt d) := Nat.mul_le_mul_left d (divisors_card_le_two_mul_sqrt d)

private lemma mul_natSqrt_le_rpow_three_halves (d : ℕ) :
    (d : ℝ) * (Nat.sqrt d : ℝ) ≤ (d : ℝ) ^ (3 / 2 : ℝ) := by
  have hd_nn : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  have hlhs_nn : 0 ≤ (d : ℝ) * (Nat.sqrt d : ℝ) := by positivity
  have hrhs_nn : 0 ≤ (d : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_nonneg hd_nn _
  have hsq_le_nat : (Nat.sqrt d : ℝ) * (Nat.sqrt d : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast Nat.sqrt_le d
  have hsq_lhs : ((d : ℝ) * (Nat.sqrt d : ℝ)) ^ 2 ≤ (d : ℝ) ^ 3 := by
    have h1 : ((d : ℝ) * (Nat.sqrt d : ℝ)) ^ 2 =
        (d : ℝ) ^ 2 * ((Nat.sqrt d : ℝ) * (Nat.sqrt d : ℝ)) := by ring
    rw [h1]
    calc (d : ℝ) ^ 2 * ((Nat.sqrt d : ℝ) * (Nat.sqrt d : ℝ))
        ≤ (d : ℝ) ^ 2 * (d : ℝ) := mul_le_mul_of_nonneg_left hsq_le_nat (sq_nonneg _)
      _ = (d : ℝ) ^ 3 := by ring
  have hsq_rhs : ((d : ℝ) ^ (3 / 2 : ℝ)) ^ 2 = (d : ℝ) ^ 3 := by
    rw [← Real.rpow_natCast ((d : ℝ) ^ (3 / 2 : ℝ)) 2, ← Real.rpow_mul hd_nn]
    have hexp : (3 / 2 : ℝ) * ((2 : ℕ) : ℝ) = ((3 : ℕ) : ℝ) := by norm_num
    rw [hexp, Real.rpow_natCast]
  rw [← hsq_rhs] at hsq_lhs
  nlinarith

private lemma sum_shiftTransitionCount_twoClass {d : ℕ} [NeZero d] (p : ZMod d → Fin 2) :
    (∑ s : ZMod d, shiftTransitionCount p s) =
      2 * (Finset.univ.filter fun c : ZMod d => p c = 0).card *
        (d - (Finset.univ.filter fun c : ZMod d => p c = 0).card) := by
  classical
  let J0 := Finset.univ.filter fun c : ZMod d => p c = 0
  let J1 := Finset.univ.filter fun c : ZMod d => p c ≠ 0
  have hpart : J0.card + J1.card = d := by
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (ZMod d)))
      (fun c => p c = 0)
    simp_rw [← ne_eq] at h
    simpa [J0, J1, ZMod.card] using h
  have hJ1_eq : J1.card = d - J0.card := by omega
  unfold shiftTransitionCount
  have hswap :
      (∑ s : ZMod d, (Finset.univ.filter fun c : ZMod d => p c ≠ p (c + s)).card) =
        ∑ c : ZMod d, (Finset.univ.filter fun s : ZMod d => p c ≠ p (c + s)).card := by
    simp_rw [Finset.card_filter]
    exact Finset.sum_comm
  rw [hswap]
  have hper_c : ∀ c : ZMod d,
      (Finset.univ.filter fun s : ZMod d => p c ≠ p (c + s)).card =
        if p c = 0 then J1.card else J0.card := by
    intro c
    have hbij :
        (Finset.univ.filter fun s : ZMod d => p c ≠ p (c + s)).card =
          (Finset.univ.filter fun y : ZMod d => p c ≠ p y).card := by
      refine Finset.card_bij (fun s _ => c + s)
        (fun s hs => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hs).2⟩)
        (fun s₁ _ s₂ _ h => add_left_cancel h)
        (fun y hy => ⟨y - c, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
          rw [add_sub_cancel]; exact (Finset.mem_filter.mp hy).2⟩, add_sub_cancel c y⟩)
    rw [hbij]
    have hc2 : p c = 0 ∨ p c = 1 := by
      rcases p c with ⟨v, hv⟩
      interval_cases v
      · left; rfl
      · right; rfl
    rcases hc2 with h0 | h1
    · simp only [h0, ↓reduceIte, J1]
      congr 1
      ext y
      simp [eq_comm]
    · have h1_ne : (1 : Fin 2) ≠ 0 := by decide
      simp only [h1, h1_ne, ↓reduceIte, J0]
      congr 1
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases p y with ⟨v, hv⟩
      interval_cases v <;> simp
  simp_rw [hper_c]
  have hsplit :
      (∑ c : ZMod d, if p c = 0 then J1.card else J0.card) =
        (∑ c ∈ J0, J1.card) + (∑ c ∈ J1, J0.card) := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (ZMod d)) (fun c => p c = 0)]
    congr 1
    · refine Finset.sum_congr rfl fun c hc => ?_
      simp [(Finset.mem_filter.mp hc).2]
    · simp_rw [← ne_eq]
      refine Finset.sum_congr rfl fun c hc => ?_
      have hne := (Finset.mem_filter.mp hc).2
      simp [hne]
  rw [hsplit, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul, hJ1_eq]
  ring

end CombinatorialSums

/-! ### Section 3: Proof of `Theorem 1B`, Part 1 (`extension_Theorem1B_TwoClass`) -/

private lemma theorem1B_twoClass_perShift {F : Type*} [Field F] {d b : ℕ} [NeZero d] [NeZero b]
    (p : ZMod d → Fin 2) (s : ZMod d)
    (hchar : CoprimeToChar F (shiftOrbitLen d s))
    (𝒳 : Submodule F (Matrix (ZMod d) (ZMod d) (Fin b → F)))
    (hLin : IsLinearClassUniformCode p 𝒳) :
    let Qs : ℝ := (shiftTransitionCount p s : ℝ)
    let gs : ℝ := (shiftGcd d s : ℝ)
    (finrank F ↥(𝒳 ⊓ 𝒳.comap (laneRot s)) : ℝ) ≤
      (b : ℝ) * ((1 / 2 : ℝ) * Qs * (d : ℝ) - (1 / 4 : ℝ) * Qs ^ 2 +
        (1 / 2 : ℝ) * gs * Qs + gs * (d : ℝ)) := by
  have : NeZero 2 := ⟨by decide⟩
  have h1A := linearClassUniform_singleShift_finrank_le F p s hchar 𝒳 hLin
  refine le_trans h1A ?_
  let g := shiftGcd d s
  let n := shiftOrbitLen d s
  let t : Fin g → ℝ := fun a => (orbitRunCount p s 0 a : ℝ)
  have ht_eq1 : ∀ a : Fin g, (orbitRunCount p s 1 a : ℝ) = t a := fun a => by
    dsimp [t]
    exact_mod_cast (orbitRunCount_zero_eq_one_twoClass p s a).symm
  have hinner_a : ∀ a : Fin g,
      (∑ m : Fin 2,
        ((orbitRunCount p s m a : ℝ) * ((n : ℝ) - (orbitClassCard p s m a : ℝ)) -
          (1 / 2 : ℝ) * (orbitRunCount p s m a : ℝ) ^ 2 +
          (1 / 2 : ℝ) * (orbitRunCount p s m a : ℝ))) =
      t a * (n : ℝ) - (t a) ^ 2 + t a := by
    intro a
    rw [Fin.sum_univ_two]
    have hcards : (orbitClassCard p s 0 a : ℝ) + (orbitClassCard p s 1 a : ℝ) = (n : ℝ) := by
      have h := sum_orbitClassCard_eq p s a
      rw [Fin.sum_univ_two] at h
      exact_mod_cast h
    change (t a * ((n : ℝ) - (orbitClassCard p s 0 a : ℝ)) - (1 / 2 : ℝ) * (t a) ^ 2 +
        (1 / 2 : ℝ) * t a) +
      ((orbitRunCount p s 1 a : ℝ) * ((n : ℝ) - (orbitClassCard p s 1 a : ℝ)) -
        (1 / 2 : ℝ) * (orbitRunCount p s 1 a : ℝ) ^ 2 +
        (1 / 2 : ℝ) * (orbitRunCount p s 1 a : ℝ)) = _
    rw [ht_eq1 a]
    have hmul_cards :
        t a * (orbitClassCard p s 0 a : ℝ) + t a * (orbitClassCard p s 1 a : ℝ) =
          t a * (n : ℝ) := by
      rw [← mul_add, hcards]
    linarith
  have hsum_t : 2 * (∑ a : Fin g, t a) = (shiftTransitionCount p s : ℝ) := by
    have h := sum_orbitRunCount_eq_shiftTransitionCount p s
    simp_rw [Fin.sum_univ_two, ← orbitRunCount_zero_eq_one_twoClass p s] at h
    have hr : (∑ a : Fin g, ((orbitRunCount p s 0 a : ℝ) + (orbitRunCount p s 0 a : ℝ))) =
        (shiftTransitionCount p s : ℝ) := by
      exact_mod_cast h
    have htwo : ∀ a : Fin g,
        (orbitRunCount p s 0 a : ℝ) + (orbitRunCount p s 0 a : ℝ) = 2 * t a :=
      fun a => by dsimp [t]; ring
    simp_rw [htwo, ← Finset.mul_sum] at hr
    exact hr
  have hcs : (∑ a : Fin g, t a) ^ 2 ≤ (g : ℝ) * ∑ a : Fin g, (t a) ^ 2 := by
    simpa using sq_sum_le_card_mul_sum_sq_fintype t
  have hgn : (g : ℝ) * (n : ℝ) = (d : ℝ) := by
    exact_mod_cast shiftGcd_mul_orbitLen d s
  unfold theorem1ASingleShiftBound
  dsimp only [g, n] at hinner_a hsum_t hcs hgn ⊢
  simp_rw [hinner_a, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul]
  have hb_nn : 0 ≤ (b : ℝ) := Nat.cast_nonneg b
  have hcore :
      (shiftGcd d s : ℝ) *
          ((∑ a : Fin (shiftGcd d s), t a) * (shiftOrbitLen d s : ℝ) -
            (∑ a : Fin (shiftGcd d s), (t a) ^ 2) +
            (∑ a : Fin (shiftGcd d s), t a)) +
        (shiftGcd d s : ℝ) * (d : ℝ) ≤
      (1 / 2 : ℝ) * (shiftTransitionCount p s : ℝ) * (d : ℝ) -
        (1 / 4 : ℝ) * (shiftTransitionCount p s : ℝ) ^ 2 +
        (1 / 2 : ℝ) * (shiftGcd d s : ℝ) * (shiftTransitionCount p s : ℝ) +
        (shiftGcd d s : ℝ) * (d : ℝ) := by
    have h1 : (shiftGcd d s : ℝ) * ((∑ a : Fin (shiftGcd d s), t a) * (shiftOrbitLen d s : ℝ)) =
        (1 / 2 : ℝ) * (shiftTransitionCount p s : ℝ) * (d : ℝ) := by
      calc (shiftGcd d s : ℝ) * ((∑ a : Fin (shiftGcd d s), t a) * (shiftOrbitLen d s : ℝ))
          = ((shiftGcd d s : ℝ) * (shiftOrbitLen d s : ℝ)) * (∑ a : Fin (shiftGcd d s), t a) := by
              ring
        _ = (d : ℝ) * (∑ a : Fin (shiftGcd d s), t a) := by rw [hgn]
        _ = (1 / 2 : ℝ) * (2 * ∑ a : Fin (shiftGcd d s), t a) * (d : ℝ) := by ring
        _ = (1 / 2 : ℝ) * (shiftTransitionCount p s : ℝ) * (d : ℝ) := by rw [hsum_t]
    have h2 : (1 / 4 : ℝ) * (shiftTransitionCount p s : ℝ) ^ 2 ≤
        (shiftGcd d s : ℝ) * ∑ a : Fin (shiftGcd d s), (t a) ^ 2 := by
      rw [← hsum_t]
      linarith
    have h3 : (shiftGcd d s : ℝ) * (∑ a : Fin (shiftGcd d s), t a) =
        (1 / 2 : ℝ) * (shiftGcd d s : ℝ) * (shiftTransitionCount p s : ℝ) := by
      rw [← hsum_t]
      ring
    linarith
  have hmul := mul_le_mul_of_nonneg_left hcore hb_nn
  linarith

private lemma theorem1B_twoClass_fin2_finrank_le {F : Type*} [Field F] {d b : ℕ}
    [NeZero d] [NeZero b] (p : ZMod d → Fin 2) (hchar : CoprimeToChar F d)
    (𝒳 : Submodule F (Matrix (ZMod d) (ZMod d) (Fin b → F)))
    (hLin : IsLinearClassUniformCode p 𝒳) :
    (finrank F 𝒳 : ℝ) ≤
      (19 / 32 : ℝ) * (b : ℝ) * (d : ℝ) ^ 2 +
        (3 / 2 : ℝ) * (b : ℝ) * (d : ℝ) ^ (3 / 2 : ℝ) := by
  classical
  have hd_pos : 0 < (d : ℝ) := Nat.cast_pos.mpr (NeZero.pos d)
  have hb_nn : 0 ≤ (b : ℝ) := Nat.cast_nonneg b
  have hper_s : ∀ s : ZMod d,
      (finrank F ↥(𝒳 ⊓ 𝒳.comap (laneRot s)) : ℝ) ≤
        (b : ℝ) * ((1 / 2 : ℝ) * (shiftTransitionCount p s : ℝ) * (d : ℝ) -
          (1 / 4 : ℝ) * (shiftTransitionCount p s : ℝ) ^ 2 +
          (3 / 2 : ℝ) * (d : ℝ) * (shiftGcd d s : ℝ)) := by
    intro s
    have hbase := theorem1B_twoClass_perShift p s
      (coprimeToChar_shiftOrbitLen_of_dim hchar s) 𝒳 hLin
    have hQ_le : (shiftTransitionCount p s : ℝ) ≤ (d : ℝ) := by
      unfold shiftTransitionCount
      have hcard : (Finset.univ.filter fun c : ZMod d => p c ≠ p (c + s)).card ≤ d := by
        calc (Finset.univ.filter fun c : ZMod d => p c ≠ p (c + s)).card
            ≤ (Finset.univ : Finset (ZMod d)).card := Finset.card_filter_le _ _
          _ = d := ZMod.card d
      exact_mod_cast hcard
    have hg_nn : 0 ≤ (shiftGcd d s : ℝ) := Nat.cast_nonneg _
    have hstep : (1 / 2 : ℝ) * (shiftGcd d s : ℝ) * (shiftTransitionCount p s : ℝ) ≤
        (1 / 2 : ℝ) * (shiftGcd d s : ℝ) * (d : ℝ) := by
      nlinarith
    have hinner :
        (1 / 2 : ℝ) * (shiftTransitionCount p s : ℝ) * (d : ℝ) -
            (1 / 4 : ℝ) * (shiftTransitionCount p s : ℝ) ^ 2 +
            (1 / 2 : ℝ) * (shiftGcd d s : ℝ) * (shiftTransitionCount p s : ℝ) +
            (shiftGcd d s : ℝ) * (d : ℝ) ≤
          (1 / 2 : ℝ) * (shiftTransitionCount p s : ℝ) * (d : ℝ) -
            (1 / 4 : ℝ) * (shiftTransitionCount p s : ℝ) ^ 2 +
            (3 / 2 : ℝ) * (d : ℝ) * (shiftGcd d s : ℝ) := by
      linarith
    exact le_trans hbase (mul_le_mul_of_nonneg_left hinner hb_nn)
  have hsum_inter :
      (∑ s : ZMod d, (finrank F ↥(𝒳 ⊓ 𝒳.comap (laneRot s)) : ℝ)) ≤
        (b : ℝ) * ((1 / 2 : ℝ) * (d : ℝ) * (∑ s : ZMod d, (shiftTransitionCount p s : ℝ)) -
          (1 / 4 : ℝ) * (∑ s : ZMod d, (shiftTransitionCount p s : ℝ) ^ 2) +
          (3 / 2 : ℝ) * (d : ℝ) * (∑ s : ZMod d, (shiftGcd d s : ℝ))) := by
    refine le_trans (Finset.sum_le_sum fun s _ => hper_s s) (le_of_eq ?_)
    rw [← Finset.mul_sum]
    congr 1
    have hrew : ∀ s : ZMod d,
        (1 / 2 : ℝ) * (shiftTransitionCount p s : ℝ) * (d : ℝ) =
          (1 / 2 : ℝ) * (d : ℝ) * (shiftTransitionCount p s : ℝ) := fun _ => by ring
    simp_rw [hrew, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  -- Double-count Q_s and apply Cauchy-Schwarz + SOS
  let d0 : ℕ := (Finset.univ.filter fun c : ZMod d => p c = 0).card
  have hd0_le : d0 ≤ d := by
    calc d0 ≤ (Finset.univ : Finset (ZMod d)).card := Finset.card_filter_le _ _
      _ = d := ZMod.card d
  have hsum_Q :
      (∑ s : ZMod d, (shiftTransitionCount p s : ℝ)) = 2 * (d0 : ℝ) * ((d : ℝ) - (d0 : ℝ)) := by
    have hnat := sum_shiftTransitionCount_twoClass p
    have hcast : ((∑ s : ZMod d, shiftTransitionCount p s : ℕ) : ℝ) =
        ((2 * d0 * (d - d0) : ℕ) : ℝ) := congrArg Nat.cast hnat
    rw [Nat.cast_sum] at hcast
    rw [hcast, Nat.cast_mul, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hd0_le]
  have hcs_Q :
      (2 * (d0 : ℝ) * ((d : ℝ) - (d0 : ℝ))) ^ 2 ≤
        (d : ℝ) * ∑ s : ZMod d, (shiftTransitionCount p s : ℝ) ^ 2 := by
    rw [← hsum_Q]
    simpa [ZMod.card] using
      sq_sum_le_card_mul_sum_sq_fintype (fun s : ZMod d => (shiftTransitionCount p s : ℝ))
  let K : ℝ := (d0 : ℝ) * ((d : ℝ) - (d0 : ℝ))
  have hsos : (d : ℝ) ^ 2 * K - K ^ 2 ≤ (3 / 16 : ℝ) * (d : ℝ) ^ 4 := by
    let δ : ℝ := (d : ℝ) / 2 - (d0 : ℝ)
    have hK_eq : K = (d : ℝ) ^ 2 / 4 - δ ^ 2 := by
      dsimp [K, δ]; ring
    have hid : (3 / 16 : ℝ) * (d : ℝ) ^ 4 - ((d : ℝ) ^ 2 * K - K ^ 2) =
        δ ^ 2 * (δ ^ 2 + (1 / 2 : ℝ) * (d : ℝ) ^ 2) := by
      rw [hK_eq]; ring
    have hnn : 0 ≤ δ ^ 2 * (δ ^ 2 + (1 / 2 : ℝ) * (d : ℝ) ^ 2) := by positivity
    linarith
  have hquad :
      (1 / 2 : ℝ) * (d : ℝ) * (∑ s : ZMod d, (shiftTransitionCount p s : ℝ)) -
          (1 / 4 : ℝ) * (∑ s : ZMod d, (shiftTransitionCount p s : ℝ) ^ 2) ≤
        (3 / 16 : ℝ) * (d : ℝ) ^ 3 := by
    have hmul_d :
        (d : ℝ) * ((1 / 2 : ℝ) * (d : ℝ) * (∑ s : ZMod d, (shiftTransitionCount p s : ℝ)) -
          (1 / 4 : ℝ) * (∑ s : ZMod d, (shiftTransitionCount p s : ℝ) ^ 2)) ≤
        (d : ℝ) * ((3 / 16 : ℝ) * (d : ℝ) ^ 3) := by
      rw [hsum_Q]
      have h2K : 2 * (d0 : ℝ) * ((d : ℝ) - (d0 : ℝ)) = 2 * K := by dsimp [K]; ring
      rw [h2K]
      have hcs' : 4 * K ^ 2 ≤ (d : ℝ) * ∑ s : ZMod d, (shiftTransitionCount p s : ℝ) ^ 2 := by
        calc 4 * K ^ 2 = (2 * (d0 : ℝ) * ((d : ℝ) - (d0 : ℝ))) ^ 2 := by dsimp [K]; ring
          _ ≤ (d : ℝ) * ∑ s : ZMod d, (shiftTransitionCount p s : ℝ) ^ 2 := hcs_Q
      linarith
    exact le_of_mul_le_mul_left hmul_d hd_pos
  have hgcd_real :
      (∑ s : ZMod d, (shiftGcd d s : ℝ)) ≤ 2 * (d : ℝ) ^ (3 / 2 : ℝ) := by
    have hnat : (∑ s : ZMod d, (shiftGcd d s : ℝ)) ≤
        (d : ℝ) * (2 * (Nat.sqrt d : ℝ)) := by
      exact_mod_cast sum_shiftGcd_le d
    have hrpow := mul_natSqrt_le_rpow_three_halves d
    linarith
  have havg := shift_avg_finrank_real_le 𝒳
  have h2d_bound :
      (2 * (d : ℝ)) * (finrank F 𝒳 : ℝ) ≤
        (2 * (d : ℝ)) * ((19 / 32 : ℝ) * (b : ℝ) * (d : ℝ) ^ 2 +
          (3 / 2 : ℝ) * (b : ℝ) * (d : ℝ) ^ (3 / 2 : ℝ)) := by
    have hcomb :
        (1 / 2 : ℝ) * (d : ℝ) * (∑ s : ZMod d, (shiftTransitionCount p s : ℝ)) -
            (1 / 4 : ℝ) * (∑ s : ZMod d, (shiftTransitionCount p s : ℝ) ^ 2) +
            (3 / 2 : ℝ) * (d : ℝ) * (∑ s : ZMod d, (shiftGcd d s : ℝ)) ≤
          (3 / 16 : ℝ) * (d : ℝ) ^ 3 + 3 * (d : ℝ) * (d : ℝ) ^ (3 / 2 : ℝ) := by
      have hg2 : (3 / 2 : ℝ) * (d : ℝ) * (∑ s : ZMod d, (shiftGcd d s : ℝ)) ≤
          3 * (d : ℝ) * (d : ℝ) ^ (3 / 2 : ℝ) := by
        nlinarith
      linarith
    have hb_comb := mul_le_mul_of_nonneg_left hcomb hb_nn
    linarith
  exact le_of_mul_le_mul_left h2d_bound (by positivity)

/-- Proof of `Extension_Theorem1B_TwoClassSpec`. -/
theorem extension_Theorem1B_TwoClass : Extension_Theorem1B_TwoClassSpec := by
  refine ⟨?_, ?_, ?_⟩
  · -- Clause 1: Per-shift bound for M = 2
    intro F _ d b _ _ p s hchar 𝒳 hLin
    exact theorem1B_twoClass_perShift p s hchar 𝒳 hLin
  · -- Clause 2: Universal 19/32 ceiling for any two-class partition Fintype.card κ ≤ 2
    intro F _ d b _ _ κ _ hκ p hchar
    have hcode_bound :
        ∀ 𝒳 : Submodule F (Matrix (ZMod d) (ZMod d) (Fin b → F)),
          IsLinearClassUniformCode p 𝒳 →
            (finrank F 𝒳 : ℝ) ≤
              (19 / 32 : ℝ) * (b : ℝ) * (d : ℝ) ^ 2 +
                (3 / 2 : ℝ) * (b : ℝ) * (d : ℝ) ^ (3 / 2 : ℝ) := by
      intro 𝒳 hLin
      classical
      let e := Fintype.equivFin κ
      let ι : κ → Fin 2 := fun k => ⟨(e k).val, lt_of_lt_of_le (e k).isLt hκ⟩
      have hι_inj : Function.Injective ι := fun k₁ k₂ h =>
        e.injective (Fin.ext (Fin.mk.inj h))
      let p' : ZMod d → Fin 2 := fun c => ι (p c)
      obtain ⟨dec, hdec⟩ := hLin
      have hLin' : IsLinearClassUniformCode p' 𝒳 := by
        refine ⟨fun m => if h : ∃ k : κ, ι k = m then dec (Classical.choose h) else 0, ?_⟩
        intro X hX c
        have hex : ∃ k : κ, ι k = p' c := ⟨p c, rfl⟩
        have hchoose : Classical.choose hex = p c := hι_inj (Classical.choose_spec hex)
        simp only [hex, ↓reduceDIte, hchoose]
        exact hdec X hX c
      exact theorem1B_twoClass_fin2_finrank_le p' hchar 𝒳 hLin'
    exact ⟨hcode_bound, linearClassUniformMaxDim_real_le p hcode_bound⟩
  · -- Clause 3: Rational barrier comparisons 19/32 = 38/64 < 5/8 = 40/64 < 41/64
    norm_num

/-- Direct unpacked theorem for `Theorem 1B`, Part 1: universal `19/32` dimension ceiling for
`b`-lane linear class-uniform codes on any two-class partition when `gcd(d, char F) = 1`. -/
theorem linearClassUniform_twoClass_finrank_le
    (F : Type*) [Field F] {d b : ℕ} [NeZero d] [NeZero b]
    {κ : Type*} [Fintype κ] (hκ : Fintype.card κ ≤ 2) (p : ZMod d → κ)
    (hchar : CoprimeToChar F d)
    (𝒳 : Submodule F (Matrix (ZMod d) (ZMod d) (Fin b → F)))
    (hLin : IsLinearClassUniformCode p 𝒳) :
    (finrank F 𝒳 : ℝ) ≤
      (19 / 32 : ℝ) * (b : ℝ) * (d : ℝ) ^ 2 +
        (3 / 2 : ℝ) * (b : ℝ) * (d : ℝ) ^ (3 / 2 : ℝ) :=
  (extension_Theorem1B_TwoClass.{0, _, _}.2.1 F d b κ hκ p hchar).1 𝒳 hLin

/-! ### Section 4: Proof of `Theorem 1B`, Part 2 (`extension_Theorem1B_MultiClassPrime`) -/

section MultiClassPrime

private noncomputable def simplexQuartic (x : ℝ) : ℝ :=
  x * (1 - x) ^ 2 * (1 - x / 2)

private lemma half_add_mul_simplexQuartic_inv_eq (M : ℕ) (hM : 2 ≤ M) :
    (1 / 2 : ℝ) + (1 / 2 : ℝ) * ((M : ℝ) * simplexQuartic (1 / (M : ℝ))) =
      multiClassLeadingCoeff M := by
  have hM_ne : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  unfold simplexQuartic multiClassLeadingCoeff
  field_simp [hM_ne]
  ring

private lemma simplexQuartic_sos_two (x : ℝ) :
    2 * simplexQuartic (1 / 2) - (simplexQuartic x + simplexQuartic (1 - x)) =
      (x - 1 / 2) ^ 2 * (1 / 2 + (x - 1 / 2) ^ 2) := by
  unfold simplexQuartic
  ring

private lemma simplexQuartic_sos_ge_three (x c : ℝ) :
    simplexQuartic c + (1 - 5 * c + 6 * c ^ 2 - 2 * c ^ 3) * (x - c) - simplexQuartic x =
      (x - c) ^ 2 * ((1 / 2 : ℝ) * (1 - x) * (3 - x - 2 * c) +
        (3 / 2 : ℝ) * (1 / 3 - c) ^ 2 + 2 * (1 / 3 - c) + (1 / 6 : ℝ)) := by
  unfold simplexQuartic
  ring

private lemma simplex_maximization_clause (M : ℕ) (hM : 2 ≤ M) (α : Fin M → ℝ)
    (hα_nn : ∀ m, 0 ≤ α m) (hα_sum : ∑ m : Fin M, α m = 1) :
    (1 / 2 : ℝ) + (1 / 2 : ℝ) * ∑ m : Fin M,
        α m * (1 - α m) ^ 2 * (1 - α m / 2) ≤ multiClassLeadingCoeff M ∧
    ((∃ m, α m ≠ 1 / (M : ℝ)) →
      (1 / 2 : ℝ) + (1 / 2 : ℝ) * ∑ m : Fin M,
        α m * (1 - α m) ^ 2 * (1 - α m / 2) < multiClassLeadingCoeff M) := by
  change (1 / 2 : ℝ) + (1 / 2 : ℝ) * ∑ m : Fin M, simplexQuartic (α m) ≤
      multiClassLeadingCoeff M ∧
    ((∃ m, α m ≠ 1 / (M : ℝ)) →
      (1 / 2 : ℝ) + (1 / 2 : ℝ) * ∑ m : Fin M, simplexQuartic (α m) <
        multiClassLeadingCoeff M)
  rcases eq_or_lt_of_le hM with rfl | hM_gt2
  · -- Case M = 2
    rw [Fin.sum_univ_two] at hα_sum ⊢
    have hα1 : α 1 = 1 - α 0 := by linarith
    have heq_coeff := half_add_mul_simplexQuartic_inv_eq 2 (by omega)
    norm_num at heq_coeff
    have hdiff :
        multiClassLeadingCoeff 2 -
          ((1 / 2 : ℝ) + (1 / 2 : ℝ) * (simplexQuartic (α 0) + simplexQuartic (α 1))) =
        (1 / 2 : ℝ) * ((α 0 - 1 / 2) ^ 2 * (1 / 2 + (α 0 - 1 / 2) ^ 2)) := by
      rw [← heq_coeff, hα1, ← simplexQuartic_sos_two (α 0)]
      ring
    refine ⟨?_, ?_⟩
    · have hnn : 0 ≤ (1 / 2 : ℝ) * ((α 0 - 1 / 2) ^ 2 * (1 / 2 + (α 0 - 1 / 2) ^ 2)) := by
        positivity
      linarith
    · rintro ⟨m, hm_ne⟩
      have hα0_ne : α 0 ≠ 1 / 2 := by
        intro h0
        rcases m with ⟨v, hv⟩
        interval_cases v
        · exact hm_ne (by norm_num [h0])
        · apply hm_ne
          change α 1 = 1 / (2 : ℝ)
          linarith
      have hsq_pos : 0 < (α 0 - 1 / 2) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hα0_ne)
      have hpos : 0 < (1 / 2 : ℝ) * ((α 0 - 1 / 2) ^ 2 * (1 / 2 + (α 0 - 1 / 2) ^ 2)) := by
        positivity
      linarith
  · -- Case M ≥ 3
    have hM3 : 3 ≤ M := hM_gt2
    let c : ℝ := 1 / (M : ℝ)
    have hM_pos : 0 < (M : ℝ) := Nat.cast_pos.mpr (by omega)
    have hc_le : c ≤ 1 / 3 := by
      dsimp [c]
      rw [div_le_div_iff₀ hM_pos (by norm_num)]
      have : (3 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM3
      linarith
    have hα_le_one : ∀ m : Fin M, α m ≤ 1 := fun m => by
      rw [← hα_sum]
      exact Finset.single_le_sum (fun i _ => hα_nn i) (Finset.mem_univ m)
    let L : ℝ := 1 - 5 * c + 6 * c ^ 2 - 2 * c ^ 3
    have hterm_ge : ∀ m : Fin M,
        (1 / 6 : ℝ) * (α m - c) ^ 2 ≤
          simplexQuartic c + L * (α m - c) - simplexQuartic (α m) := by
      intro m
      rw [simplexQuartic_sos_ge_three (α m) c]
      have h1 : 0 ≤ 1 - α m := sub_nonneg.mpr (hα_le_one m)
      have h2 : 0 ≤ 3 - α m - 2 * c := by
        have := hα_le_one m
        linarith
      have h3 : 0 ≤ 1 / 3 - c := sub_nonneg.mpr hc_le
      have hbrack : (1 / 6 : ℝ) ≤
          (1 / 2 : ℝ) * (1 - α m) * (3 - α m - 2 * c) +
            (3 / 2 : ℝ) * (1 / 3 - c) ^ 2 + 2 * (1 / 3 - c) + (1 / 6 : ℝ) := by
        have hp1 : 0 ≤ (1 / 2 : ℝ) * (1 - α m) * (3 - α m - 2 * c) := by positivity
        have hp2 : 0 ≤ (3 / 2 : ℝ) * (1 / 3 - c) ^ 2 + 2 * (1 / 3 - c) := by positivity
        linarith
      have hm := mul_le_mul_of_nonneg_left hbrack (sq_nonneg (α m - c))
      linarith
    have hsum_ge :
        (1 / 6 : ℝ) * (∑ m : Fin M, (α m - c) ^ 2) ≤
          (M : ℝ) * simplexQuartic c - ∑ m : Fin M, simplexQuartic (α m) := by
      have h1 := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin M))) fun m _ => hterm_ge m
      rw [← Finset.mul_sum] at h1
      have hrhs :
          (∑ m : Fin M, (simplexQuartic c + L * (α m - c) - simplexQuartic (α m))) =
            (M : ℝ) * simplexQuartic c - ∑ m : Fin M, simplexQuartic (α m) := by
        simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum,
          Finset.sum_sub_distrib, hα_sum]
        have hMc : (M : ℝ) * c = 1 := mul_one_div_cancel (ne_of_gt hM_pos)
        simp_rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hMc,
          sub_self, mul_zero, add_zero]
      rwa [hrhs] at h1
    have heq_coeff := half_add_mul_simplexQuartic_inv_eq M hM
    refine ⟨?_, ?_⟩
    · have hsq_sum_nn : 0 ≤ ∑ m : Fin M, (α m - c) ^ 2 :=
        Finset.sum_nonneg fun m _ => sq_nonneg _
      dsimp [c] at hsum_ge hsq_sum_nn
      linarith
    · rintro ⟨m₀, hm₀⟩
      have hm₀_pos : 0 < (α m₀ - c) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hm₀)
      have hsq_sum_pos : 0 < ∑ m : Fin M, (α m - c) ^ 2 :=
        lt_of_lt_of_le hm₀_pos
          (Finset.single_le_sum (fun m _ => sq_nonneg (α m - c)) (Finset.mem_univ m₀))
      dsimp [c] at hsum_ge hsq_sum_pos
      linarith

private lemma coprimeToChar_of_prime_ne_ringChar (F : Type*) [Field F] {d : ℕ}
    (hd : Nat.Prime d) (hchar : d ≠ ringChar F) :
    CoprimeToChar F d := by
  have : NeZero d := ⟨hd.ne_zero⟩
  rw [coprimeToChar_iff_natCast_ne_zero]
  intro hz
  have hdvd : ringChar F ∣ d := (ringChar.spec F d).mp hz
  rcases hd.eq_one_or_self_of_dvd (ringChar F) hdvd with h1 | hself
  · have h1_dvd : ringChar F ∣ 1 := by rw [h1]
    have h1_zero : ((1 : ℕ) : F) = 0 := (ringChar.spec F 1).mpr h1_dvd
    simp at h1_zero
  · exact hchar hself.symm

private lemma sum_classTransition_all_shifts {d M : ℕ} [NeZero d]
    (p : ZMod d → Fin M) (m : Fin M) :
    (∑ s : ZMod d,
      (Finset.univ.filter fun c : ZMod d => p c = m ∧ p (c + s) ≠ m).card) =
    (Finset.univ.filter fun c : ZMod d => p c = m).card *
      (d - (Finset.univ.filter fun c : ZMod d => p c = m).card) := by
  classical
  let Jm := Finset.univ.filter fun c : ZMod d => p c = m
  let Comp := Finset.univ.filter fun c : ZMod d => p c ≠ m
  have hpart : Jm.card + Comp.card = d := by
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (ZMod d)))
      (fun c => p c = m)
    simp_rw [← ne_eq] at h
    simpa [Jm, Comp, ZMod.card] using h
  have hComp : Comp.card = d - Jm.card := by omega
  have hswap :
      (∑ s : ZMod d,
        (Finset.univ.filter fun c : ZMod d => p c = m ∧ p (c + s) ≠ m).card) =
      ∑ c : ZMod d,
        (Finset.univ.filter fun s : ZMod d => p c = m ∧ p (c + s) ≠ m).card := by
    simp_rw [Finset.card_filter]
    exact Finset.sum_comm
  rw [hswap]
  have hper_c : ∀ c : ZMod d,
      (Finset.univ.filter fun s : ZMod d => p c = m ∧ p (c + s) ≠ m).card =
        if p c = m then Comp.card else 0 := by
    intro c
    by_cases hpc : p c = m
    · simp only [hpc, true_and, ↓reduceIte, Comp]
      refine Finset.card_bij (fun s _ => c + s)
        (fun s hs => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hs).2⟩)
        (fun s₁ _ s₂ _ h => add_left_cancel h)
        (fun y hy => ⟨y - c, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
          rw [add_sub_cancel]; exact (Finset.mem_filter.mp hy).2⟩, add_sub_cancel c y⟩)
    · simp [hpc]
  simp_rw [hper_c, ← Finset.sum_filter, Finset.sum_const, smul_eq_mul, hComp]
  rfl

private lemma theorem1B_multiClass_prime_finrank_le
    (F : Type*) [Field F] {d M b : ℕ} [NeZero b]
    (hd : Nat.Prime d) (hchar : d ≠ ringChar F) (hM : 3 ≤ M)
    (p : ZMod d → Fin M)
    (𝒳 : Submodule F (Matrix (ZMod d) (ZMod d) (Fin b → F)))
    (hLin : IsLinearClassUniformCode p 𝒳) :
    (finrank F 𝒳 : ℝ) ≤
      multiClassLeadingCoeff M * (b : ℝ) * (d : ℝ) ^ 2 +
        (1 : ℝ) * (b : ℝ) * (M : ℝ) * (d : ℝ) := by
  classical
  have : NeZero d := ⟨hd.ne_zero⟩
  have : NeZero M := ⟨by omega⟩
  have hd_pos : 0 < (d : ℝ) := Nat.cast_pos.mpr hd.pos
  have hb_nn : 0 ≤ (b : ℝ) := Nat.cast_nonneg b
  have hcop_d : CoprimeToChar F d := coprimeToChar_of_prime_ne_ringChar F hd hchar
  let dm : Fin M → ℕ := fun m => (Finset.univ.filter fun c : ZMod d => p c = m).card
  let Tm : Fin M → ZMod d → ℕ := fun m s =>
    (Finset.univ.filter fun c : ZMod d => p c = m ∧ p (c + s) ≠ m).card
  have hdm_sum_nat : ∑ m : Fin M, dm m = d := by
    have h := sum_orbitClassCard_eq p (0 : ZMod d)
      ⟨0, shiftGcd_pos d 0⟩
    -- Or directly partition ZMod d by p
    clear h
    rw [← ZMod.card d, ← Finset.card_univ]
    symm
    rw [← Finset.card_biUnion (s := Finset.univ) (t := fun m : Fin M =>
      Finset.univ.filter fun c : ZMod d => p c = m)]
    · congr 1
      ext c
      simp
    · intro m₁ _ m₂ _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro c hc₁ hc₂
      simp only [Finset.mem_filter] at hc₁ hc₂
      exact hne (hc₁.2.symm.trans hc₂.2)
  have hdm_le : ∀ m : Fin M, dm m ≤ d := fun m => by
    rw [← hdm_sum_nat]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ m)
  -- Nonzero shifts have shiftGcd = 1 and shiftOrbitLen = d
  have hper_nz : ∀ s ∈ (Finset.univ : Finset (ZMod d)).erase 0,
      (finrank F ↥(𝒳 ⊓ 𝒳.comap (laneRot s)) : ℝ) ≤
        (b : ℝ) * (∑ m : Fin M,
          ((Tm m s : ℝ) * ((d : ℝ) - (dm m : ℝ)) -
            (1 / 2 : ℝ) * (Tm m s : ℝ) ^ 2 +
            (1 / 2 : ℝ) * (Tm m s : ℝ))) + (b : ℝ) * (d : ℝ) := by
    intro s hs
    have hs_ne : s ≠ 0 := (Finset.mem_erase.mp hs).1
    have hsval_pos : 0 < s.val :=
      Nat.pos_of_ne_zero fun hz => hs_ne ((ZMod.val_eq_zero s).mp hz)
    have hnot_dvd : ¬ (d ∣ s.val) := Nat.not_dvd_of_pos_of_lt hsval_pos (ZMod.val_lt s)
    have hg1 : shiftGcd d s = 1 := hd.coprime_iff_not_dvd.mpr hnot_dvd
    have hn_eq : shiftOrbitLen d s = d := by
      unfold shiftOrbitLen
      rw [hg1, Nat.div_one]
    have hcop_orb : CoprimeToChar F (shiftOrbitLen d s) := by
      rw [hn_eq]
      exact hcop_d
    have h1A := linearClassUniform_singleShift_finrank_le F p s hcop_orb 𝒳 hLin
    refine le_trans h1A (le_of_eq ?_)
    unfold theorem1ASingleShiftBound
    let a₀ : Fin (shiftGcd d s) := ⟨0, by omega⟩
    have huniv_fin : (Finset.univ : Finset (Fin (shiftGcd d s))) = {a₀} := by
      ext a
      simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
      apply Fin.ext
      have := a.isLt
      change a.val < shiftGcd d s at this
      dsimp [a₀]
      omega
    have horb_univ : shiftOrbit s a₀ = Finset.univ := by
      ext c
      simp [shiftOrbit, a₀, hg1, Nat.mod_one]
    have hcard_eq : ∀ m : Fin M, orbitClassCard p s m a₀ = dm m := fun m => by
      simp [orbitClassCard, horb_univ, dm]
    have hrun_eq : ∀ m : Fin M, orbitRunCount p s m a₀ = Tm m s := fun m => by
      simp [orbitRunCount, horb_univ, Tm]
    change ((b : ℝ) * (shiftGcd d s : ℝ)) *
        (∑ a ∈ (Finset.univ : Finset (Fin (shiftGcd d s))), ∑ m : Fin M,
          ((orbitRunCount p s m a : ℝ) *
              ((shiftOrbitLen d s : ℝ) - (orbitClassCard p s m a : ℝ)) -
            (1 / 2 : ℝ) * (orbitRunCount p s m a : ℝ) ^ 2 +
            (1 / 2 : ℝ) * (orbitRunCount p s m a : ℝ))) +
      (b : ℝ) * (shiftGcd d s : ℝ) * (d : ℝ) = _
    rw [huniv_fin, Finset.sum_singleton]
    simp_rw [hg1, hn_eq, hcard_eq, hrun_eq, Nat.cast_one]
    ring
  -- s = 0 bound
  have hzero_le :
      (finrank F ↥(𝒳 ⊓ 𝒳.comap (laneRot (0 : ZMod d))) : ℝ) ≤ (b : ℝ) * (d : ℝ) ^ 2 := by
    have hnat : finrank F ↥(𝒳 ⊓ 𝒳.comap (laneRot (0 : ZMod d))) ≤ b * d ^ 2 :=
      (Submodule.finrank_le _).trans (le_of_eq (finrank_matrix_lane F d b))
    exact_mod_cast hnat
  -- T_m(0) = 0 and sums over nonzero shifts
  have hTm_zero : ∀ m : Fin M, Tm m 0 = 0 := by
    intro m
    simp [Tm]
  have hTm_sum_nz : ∀ m : Fin M,
      (∑ s ∈ (Finset.univ : Finset (ZMod d)).erase 0, (Tm m s : ℝ)) =
        (dm m : ℝ) * ((d : ℝ) - (dm m : ℝ)) := by
    intro m
    have hall : (∑ s : ZMod d, (Tm m s : ℝ)) = (dm m : ℝ) * ((d : ℝ) - (dm m : ℝ)) := by
      have hnat := sum_classTransition_all_shifts p m
      have hcast : ((∑ s : ZMod d, Tm m s : ℕ) : ℝ) =
          ((dm m * (d - dm m) : ℕ) : ℝ) := congrArg Nat.cast hnat
      rw [Nat.cast_sum] at hcast
      rw [hcast, Nat.cast_mul, Nat.cast_sub (hdm_le m)]
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : ZMod d)),
      hTm_zero m, Nat.cast_zero, zero_add] at hall
    exact hall
  have hTm_sq_nz : ∀ m : Fin M,
      ((dm m : ℝ) * ((d : ℝ) - (dm m : ℝ))) ^ 2 / (d : ℝ) ≤
        ∑ s ∈ (Finset.univ : Finset (ZMod d)).erase 0, (Tm m s : ℝ) ^ 2 := by
    intro m
    have hsq_eq :
        (∑ s ∈ (Finset.univ : Finset (ZMod d)).erase 0, (Tm m s : ℝ) ^ 2) =
          ∑ s : ZMod d, (Tm m s : ℝ) ^ 2 := by
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : ZMod d)),
        hTm_zero m, Nat.cast_zero]
      ring
    rw [hsq_eq]
    have hcs : ((dm m : ℝ) * ((d : ℝ) - (dm m : ℝ))) ^ 2 ≤
        (d : ℝ) * ∑ s : ZMod d, (Tm m s : ℝ) ^ 2 := by
      have hall : (∑ s : ZMod d, (Tm m s : ℝ)) = (dm m : ℝ) * ((d : ℝ) - (dm m : ℝ)) := by
        rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : ZMod d)),
          hTm_zero m, Nat.cast_zero, zero_add, hTm_sum_nz m]
      rw [← hall]
      simpa [ZMod.card] using
        sq_sum_le_card_mul_sum_sq_fintype (fun s : ZMod d => (Tm m s : ℝ))
    rw [div_le_iff₀ hd_pos]
    linarith
  -- Sum over all shifts s : ZMod d
  let α : Fin M → ℝ := fun m => (dm m : ℝ) / (d : ℝ)
  have hα_nn : ∀ m : Fin M, 0 ≤ α m := fun m => by dsimp [α]; positivity
  have hα_sum : ∑ m : Fin M, α m = 1 := by
    dsimp [α]
    simp_rw [div_eq_mul_inv, ← Finset.sum_mul]
    have hsum_r : (∑ m : Fin M, (dm m : ℝ)) = (d : ℝ) := by exact_mod_cast hdm_sum_nat
    rw [hsum_r, mul_inv_cancel₀ (ne_of_gt hd_pos)]
  have hper_m : ∀ m : Fin M,
      (∑ s ∈ (Finset.univ : Finset (ZMod d)).erase 0,
        ((Tm m s : ℝ) * ((d : ℝ) - (dm m : ℝ)) -
          (1 / 2 : ℝ) * (Tm m s : ℝ) ^ 2 +
          (1 / 2 : ℝ) * (Tm m s : ℝ))) ≤
      (d : ℝ) ^ 3 * (α m * (1 - α m) ^ 2 * (1 - α m / 2)) +
        (1 / 2 : ℝ) * (dm m : ℝ) * (d : ℝ) := by
    intro m
    simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
      hTm_sum_nz m]
    have hsq := hTm_sq_nz m
    have hlin : (1 / 2 : ℝ) * ((dm m : ℝ) * ((d : ℝ) - (dm m : ℝ))) ≤
        (1 / 2 : ℝ) * (dm m : ℝ) * (d : ℝ) := by
      have : 0 ≤ (dm m : ℝ) ^ 2 := sq_nonneg _
      linarith
    have hquart :
        (dm m : ℝ) * ((d : ℝ) - (dm m : ℝ)) * ((d : ℝ) - (dm m : ℝ)) -
          (1 / 2 : ℝ) * (((dm m : ℝ) * ((d : ℝ) - (dm m : ℝ))) ^ 2 / (d : ℝ)) =
        (d : ℝ) ^ 3 * (α m * (1 - α m) ^ 2 * (1 - α m / 2)) := by
      dsimp [α]
      have hd_ne : (d : ℝ) ≠ 0 := ne_of_gt hd_pos
      field_simp [hd_ne]
    linarith
  have hsum_nz :
      (∑ s ∈ (Finset.univ : Finset (ZMod d)).erase 0,
        (finrank F ↥(𝒳 ⊓ 𝒳.comap (laneRot s)) : ℝ)) ≤
      (b : ℝ) * ((d : ℝ) ^ 3 * ∑ m : Fin M, (α m * (1 - α m) ^ 2 * (1 - α m / 2))) +
        (3 / 2 : ℝ) * (b : ℝ) * (d : ℝ) ^ 2 - (b : ℝ) * (d : ℝ) := by
    have h1 := Finset.sum_le_sum hper_nz
    refine le_trans h1 ?_
    have hcard_nz : ((Finset.univ : Finset (ZMod d)).erase 0).card = d - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]
    rw [Finset.sum_add_distrib, Finset.sum_const, hcard_nz, nsmul_eq_mul, ← Finset.mul_sum,
      Finset.sum_comm]
    have h2 := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (s := (Finset.univ : Finset (Fin M))) fun m _ => hper_m m) hb_nn
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at h2
    have hsum_dm_r : (∑ m : Fin M, (1 / 2 : ℝ) * (dm m : ℝ) * (d : ℝ)) =
        (1 / 2 : ℝ) * (d : ℝ) ^ 2 := by
      have hdm_r : (∑ m : Fin M, (dm m : ℝ)) = (d : ℝ) := by exact_mod_cast hdm_sum_nat
      calc (∑ m : Fin M, (1 / 2 : ℝ) * (dm m : ℝ) * (d : ℝ))
          = (1 / 2 : ℝ) * (∑ m : Fin M, (dm m : ℝ)) * (d : ℝ) := by
              simp_rw [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul]
        _ = (1 / 2 : ℝ) * (d : ℝ) ^ 2 := by rw [hdm_r]; ring
    rw [hsum_dm_r] at h2
    have hd1_cast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
      have : 1 ≤ d := hd.one_lt.le
      simpa using Nat.cast_sub (R := ℝ) this
    rw [hd1_cast]
    linarith
  have hsum_all :
      (∑ s : ZMod d, (finrank F ↥(𝒳 ⊓ 𝒳.comap (laneRot s)) : ℝ)) ≤
      (b : ℝ) * ((d : ℝ) ^ 3 * ∑ m : Fin M, (α m * (1 - α m) ^ 2 * (1 - α m / 2))) +
        (5 / 2 : ℝ) * (b : ℝ) * (d : ℝ) ^ 2 := by
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : ZMod d))]
    have hbd_nn : 0 ≤ (b : ℝ) * (d : ℝ) := by positivity
    linarith
  have havg := shift_avg_finrank_real_le 𝒳
  have hsimplex := (simplex_maximization_clause M (by omega) α hα_nn hα_sum).1
  have hM_ge3_r : (5 / 2 : ℝ) ≤ 2 * (M : ℝ) := by
    have : (3 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    linarith
  have h2d_bound :
      (2 * (d : ℝ)) * (finrank F 𝒳 : ℝ) ≤
        (2 * (d : ℝ)) * (multiClassLeadingCoeff M * (b : ℝ) * (d : ℝ) ^ 2 +
          (1 : ℝ) * (b : ℝ) * (M : ℝ) * (d : ℝ)) := by
    have hlead :
        (b : ℝ) * (d : ℝ) ^ 3 +
          (b : ℝ) * ((d : ℝ) ^ 3 * ∑ m : Fin M, (α m * (1 - α m) ^ 2 * (1 - α m / 2))) ≤
        2 * multiClassLeadingCoeff M * (b : ℝ) * (d : ℝ) ^ 3 := by
      have hmul := mul_le_mul_of_nonneg_right hsimplex (by positivity : 0 ≤ 2 * (b : ℝ) * (d : ℝ) ^ 3)
      linarith
    have herr :
        (5 / 2 : ℝ) * (b : ℝ) * (d : ℝ) ^ 2 ≤
          2 * (M : ℝ) * (b : ℝ) * (d : ℝ) ^ 2 := by
      have hbd2 : 0 ≤ (b : ℝ) * (d : ℝ) ^ 2 := by positivity
      nlinarith
    linarith
  exact le_of_mul_le_mul_left h2d_bound (by positivity)

end MultiClassPrime

/-- Proof of `Extension_Theorem1B_MultiClassPrimeSpec`. -/
theorem extension_Theorem1B_MultiClassPrime : Extension_Theorem1B_MultiClassPrimeSpec := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- Clause 1: Simplex global maximum + strict inequality off (1/M, ..., 1/M)
    intro M hM α hα_nn hα_sum
    exact simplex_maximization_clause M hM α hα_nn hα_sum
  · -- Clause 2: Prime-d multi-class ceiling with explicit absolute constant C = 1 > 0
    refine ⟨1, by norm_num, ?_⟩
    intro F _ d M b _ hd hchar hM p
    have hcode_bound :
        ∀ 𝒳 : Submodule F (Matrix (ZMod d) (ZMod d) (Fin b → F)),
          IsLinearClassUniformCode p 𝒳 →
            (finrank F 𝒳 : ℝ) ≤
              multiClassLeadingCoeff M * (b : ℝ) * (d : ℝ) ^ 2 +
                (1 : ℝ) * (b : ℝ) * (M : ℝ) * (d : ℝ) :=
      fun 𝒳 hLin => theorem1B_multiClass_prime_finrank_le F hd hchar hM p 𝒳 hLin
    have : NeZero d := ⟨hd.ne_zero⟩
    exact ⟨hcode_bound, linearClassUniformMaxDim_real_le p hcode_bound⟩
  · -- Clause 3: Strict improvement multiClassLeadingCoeff M < 1 - 1 / (2 * M) for all M ≥ 2
    intro M hM
    have hM2 : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    have hM_pos : 0 < (M : ℝ) := by positivity
    have hM_ne : (M : ℝ) ≠ 0 := ne_of_gt hM_pos
    have hdiff :
        (1 - 1 / (2 * (M : ℝ))) - multiClassLeadingCoeff M =
          (((M : ℝ) - 1) * (3 * (M : ℝ) - 1)) / (4 * (M : ℝ) ^ 3) := by
      unfold multiClassLeadingCoeff
      field_simp [hM_ne]
      ring
    have hnum_pos : 0 < ((M : ℝ) - 1) * (3 * (M : ℝ) - 1) := by nlinarith
    have hpos : 0 < (((M : ℝ) - 1) * (3 * (M : ℝ) - 1)) / (4 * (M : ℝ) ^ 3) :=
      div_pos hnum_pos (by positivity)
    linarith
  · -- Clause 4: M = 3 evaluation 37/54 < 5/6
    unfold multiClassLeadingCoeff
    norm_num
  · -- Clause 5: M = 4 evaluation 191/256 < 7/8
    unfold multiClassLeadingCoeff
    norm_num

/-- Direct unpacked theorem for `Theorem 1B`, Part 2: prime-`d` (`d ≠ char F`) multi-class
dimension ceiling (`C = 1`) for `b`-lane linear class-uniform codes with `M ≥ 3` classes. -/
theorem linearClassUniform_multiClass_prime_finrank_le
    (F : Type*) [Field F] {d M b : ℕ} [NeZero b]
    (hd : Nat.Prime d) (hchar : d ≠ ringChar F) (hM : 3 ≤ M)
    (p : ZMod d → Fin M)
    (𝒳 : Submodule F (Matrix (ZMod d) (ZMod d) (Fin b → F)))
    (hLin : IsLinearClassUniformCode p 𝒳) :
    (finrank F 𝒳 : ℝ) ≤
      multiClassLeadingCoeff M * (b : ℝ) * (d : ℝ) ^ 2 +
        (b : ℝ) * (M : ℝ) * (d : ℝ) := by
  simpa [one_mul] using theorem1B_multiClass_prime_finrank_le F hd hchar hM p 𝒳 hLin

end BoundedArityDecoders
