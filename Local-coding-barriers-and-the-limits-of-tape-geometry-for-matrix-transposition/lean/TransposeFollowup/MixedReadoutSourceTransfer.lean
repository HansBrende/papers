import TransposeFollowup.MixedReadoutDistance

/-! Transfer the mixed-readout separation to actual source words. Both
input errors, the inverse, and all fixed factors are charged in the native
Frobenius metric. The actual coefficient selector supplies a single word
that works uniformly for every pair in the centralizer. -/
namespace TransposeFollowup.SL2Projection
open Classical Matrix Set RealMobius
open scoped Matrix.Norms.Frobenius Pointwise
set_option autoImplicit false
local notation "RMat" => Matrix (Fin 2) (Fin 2) ℝ
local notation "G" => Matrix.SpecialLinearGroup (Fin 2) ℝ

theorem mixed_readout_word_geometry {A : Set G} {α : ℝ} {U V g : G} {m n k : ℕ}
    (hAi : A⁻¹ = A) (hα : 0 < α) (hαone : α ≤ 1)
    (hA : A ⊆ mobiusIdentityBall α)
    (hU : U ∈ A^m) (hV : V ∈ A^n) (hg : g ∈ A^k) :
    V*U⁻¹*g*(V*U)*g⁻¹ ∈ A^(2*m+2*n+2*k) ∧
      dist ((V*U⁻¹*g*(V*U)*g⁻¹ : G):RMat) 1 ≤ (5:ℝ)^(2*m+2*n+2*k)*α := by
  have hi {x : G} {j : ℕ} (hx : x ∈ A^j) : x⁻¹ ∈ A^j := by
    have hh := Set.inv_mem_inv.mpr hx
    rwa [← inv_pow, hAi] at hh
  have hm {x y : G} {i j : ℕ} (hx : x ∈ A^i) (hy : y ∈ A^j) :
      x*y ∈ A^(i+j) := by
    rw [pow_add]
    exact Set.mul_mem_mul hx hy
  have hw : V*U⁻¹*g*(V*U)*g⁻¹ ∈ A^(2*m+2*n+2*k) := by
    simpa only [show n+m+k+(n+m)+k = 2*m+2*n+2*k by omega] using
      hm (hm (hm (hm hV (hi hU)) hg) (hm hV hU)) (hi hg)
  exact ⟨hw, set_pow_dist_from_one_le hα hαone hA _ _ hw⟩

theorem mixed_readout_source_error (u v U V g : G) {R ε : ℝ}
    (hR : 1 ≤ R) (hε : 0 ≤ ε)
    (hu : ∀ i j, |u i j| ≤ R) (hv : ∀ i j, |v i j| ≤ R)
    (hU : ∀ i j, |U i j| ≤ R) (hV : ∀ i j, |V i j| ≤ R)
    (hg : ∀ i j, |g i j| ≤ R)
    (heu : dist (u : RMat) (U : RMat) ≤ ε)
    (hev : dist (v : RMat) (V : RMat) ≤ ε) :
    dist ((v * u⁻¹ * g * (v * u) * g⁻¹ : G) : RMat)
      ((V * U⁻¹ * g * (V * U) * g⁻¹ : G) : RMat) ≤ 512 * R^7 * ε := by
  have hR0 : 0 ≤ R := by linarith
  have hp (x y X Y : G) (hy : ∀ i j, |y i j| ≤ R) (hX : ∀ i j, |X i j| ≤ R)
      (hx : dist (x : RMat) (X : RMat) ≤ ε)
      (hyy : dist (y : RMat) (Y : RMat) ≤ ε) :
      dist ((x*y : G) : RMat) ((X*Y : G) : RMat) ≤ 4*R*ε := by
    have hh := frobenius_product_distance (x:RMat) (X:RMat) (y:RMat) (Y:RMat)
    have hm := add_le_add
      (mul_le_mul hx (frobenius_norm_le_of_entry_bound hR0 hy) (norm_nonneg _) hε)
      (mul_le_mul (frobenius_norm_le_of_entry_bound hR0 hX) hyy dist_nonneg
        (by positivity : 0 ≤ 2*R))
    exact hh.trans (hm.trans_eq (by ring))
  have he₁ := hp v u⁻¹ V U⁻¹ (matrixEntryBox_inv hu) hV hev
    (by rw [sl2_inverse_frobenius_distance]; exact heu)
  have he₂ := hp v u V U hu hV hev heu
  have hg' : ∀ i j, |g i j| ≤ 2*R^2 := by
    intro i j
    exact (hg i j).trans (by nlinarith)
  have hvu : ∀ i j, |(v*u) i j| ≤ 2*R^2 := by
    intro i j
    simpa only [pow_two, mul_assoc] using matrixEntryBox_mul hv hu i j
  have hVU : ∀ i j, |(V*U⁻¹) i j| ≤ 2*R^2 := by
    intro i j
    simpa only [pow_two, mul_assoc] using matrixEntryBox_mul hV (matrixEntryBox_inv hU) i j
  have hh := (two_source_word_distances (v*u⁻¹) (v*u) (V*U⁻¹) (V*U) g g⁻¹
    (by positivity : 0 ≤ 2*R^2) (by positivity : 0 ≤ 4*R*ε)
    hvu hVU hg' (matrixEntryBox_inv hg') he₁ he₂).2
  convert hh using 1; ring

theorem mixed_readout_source_far (b : RMat) (u v U V g : G) {s t p q M ρ R ε r : ℝ}
    (hM : 1 ≤ M) (hρ : 0 < ρ) (hb : Matrix.trace b = 0)
    (hbn : ‖b‖ ≤ M) (hbd : |b.det| ≤ M)
    (hbg : ‖matrixConjugationLinear g b‖ ≤ M)
    (hu : (u : RMat) = scalarAffine b s t) (hv : (v : RMat) = scalarAffine b p q)
    (hun : dist (u : RMat) 1 ≤ 1/8) (hvn : dist (v : RMat) 1 ≤ 1/8)
    (hD : ρ ≤ |(b * (g : RMat) - (g : RMat) * b).det|)
    (hD' : ρ ≤ |(b * (g : RMat) - (g : RMat) * b).det - 4 * b.det|)
    (hfar : r ≤ max (dist (u : RMat) 1) (dist (v : RMat) 1))
    (hR : 1 ≤ R) (hε : 0 ≤ ε)
    (hub : ∀ i j, |u i j| ≤ R) (hvb : ∀ i j, |v i j| ≤ R)
    (hUb : ∀ i j, |U i j| ≤ R) (hVb : ∀ i j, |V i j| ≤ R)
    (hg : ∀ i j, |g i j| ≤ R)
    (heu : dist (u : RMat) (U : RMat) ≤ ε)
    (hev : dist (v : RMat) (V : RMat) ≤ ε)
    (herror : 512 * R^7 * ε ≤ ρ*r/(288*M^2)) :
    ρ*r/(288*M^2) ≤ dist ((V * U⁻¹ * g * (V * U) * g⁻¹ : G) : RMat) 1 := by
  have hgeom := hfar.trans (mixed_readout_distance_bound b u v g hM hρ hb hbn hbd
    hbg hu hv hun hvn hD hD')
  have herr := mixed_readout_source_error u v U V g hR hε hub hvb hUb hVb hg heu hev
  have htri := dist_triangle ((v*u⁻¹*g*(v*u)*g⁻¹ : G):RMat)
    ((V*U⁻¹*g*(V*U)*g⁻¹ : G):RMat) 1
  have hMp : 0 < 144*M^2 := by positivity
  have hlow : ρ*r/(144*M^2) ≤ dist ((v*u⁻¹*g*(v*u)*g⁻¹ : G):RMat) 1 := by
    apply (div_le_iff₀ hMp).mpr
    have hh := (le_div_iff₀ hρ).mp
      (show r ≤ (144*M^2*dist ((v*u⁻¹*g*(v*u)*g⁻¹ : G):RMat) 1)/ρ by
        simpa only [div_mul_eq_mul_div] using hgeom)
    nlinarith only [hh]
  have heq : ρ*r/(144*M^2) = 2*(ρ*r/(288*M^2)) := by ring
  linarith only [hlow, heq, htri, herr, herror]

/-- The previously selected actual word also provides uniform geometric
separation. No new coefficient-gap hypothesis is added to the extraction. -/
theorem exists_actual_readout_distance {A : Set G} {α d r : ℝ} {p q z : G}
    (hA1 : 1 ∈ A) (hAi : A⁻¹ = A) (hα : 0 < α) (hαone : α ≤ 1)
    (hA : A ⊆ mobiusIdentityBall α) (hsmall : 4*(5:ℝ)^102*α ≤ 1)
    (hp : p ∈ A^34) (hq : q ∈ A^34) (hpq : p*q ∈ A^34)
    (hd : 0 < d) (hspan : d ≤ |(SL2Escape.pairSpanMatrix (p:RMat) (q:RMat)).det|)
    (hz : z ∈ mobiusIdentityBall (1/2)) (hr : 0 < r) (hfar : r ≤ dist (z:RMat) 1) :
    let b := (z:RMat) - (Matrix.trace (z:RMat)/2) • (1:RMat)
    let Γ := (r/8)^3/(3456*(96*((4:ℝ)^34)^4/d)^3)
    let B := 128*((4:ℝ)^68)^2
    let ρ := Γ^2/(3328*B^4)
    let M := 128*((4:ℝ)^204)^2
    ∃ g ∈ A^204,
      (ρ ≤ |(b*(g:RMat)-(g:RMat)*b).det| ∧
       ρ ≤ |(b*(g:RMat)-(g:RMat)*b).det - 4*b.det|) ∧
      ∀ (u v : G) (s t c e : ℝ),
        (u:RMat) = scalarAffine b s t → (v:RMat) = scalarAffine b c e →
        dist (u:RMat) 1 ≤ 1/8 → dist (v:RMat) 1 ≤ 1/8 →
        max (dist (u:RMat) 1) (dist (v:RMat) 1) ≤
          144*M^2/ρ * dist ((v*u⁻¹*g*(v*u)*g⁻¹ : G):RMat) 1 := by
  dsimp only
  obtain ⟨g, hg, hD, hD'⟩ := exists_actual_two_readout_coefficients
    hA1 hAi hα hαone hA hsmall hp hq hpq hd hspan hz hr hfar
  refine ⟨g, hg, ⟨hD, hD'⟩, ?_⟩
  intro u v s t c e hu hv hun hvn
  let b := (z:RMat) - (Matrix.trace (z:RMat)/2) • (1:RMat)
  let H := (4:ℝ)^204
  have hH : 1 ≤ H := one_le_pow₀ (by norm_num)
  have hMb : 32 ≤ 128*H^2 := by nlinarith only [hH]
  have hbn := (centered_near_identity_generator_bounds z hz).1
  have hbd := (centered_near_identity_generator_bounds z hz).2
  have hgb : ∀ i j, |g i j| ≤ H := by
    intro i j
    simpa only [H, show (2:ℝ)*2 = 4 by norm_num] using
      set_pow_subset_matrixEntryBox
        (hA.trans (mobiusIdentityBall_subset_entryBox_two hα hαone)) 204 hg i j
  have hbg := (matrixConjugation_trace_det_norm g b (by linarith) hgb hbn).2.2
  apply mixed_readout_distance_bound b u v g
    (by linarith only [hMb]) (by positivity)
    (by simp [b, Matrix.trace_sub, Matrix.trace_smul])
    (hbn.trans hMb) (hbd.trans hMb) ?_ hu hv hun hvn hD hD'
  convert hbg using 1; ring

end TransposeFollowup.SL2Projection
