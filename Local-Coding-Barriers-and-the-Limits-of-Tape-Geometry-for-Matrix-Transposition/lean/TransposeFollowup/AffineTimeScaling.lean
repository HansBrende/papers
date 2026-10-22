import TransposeFollowup.OpenAffineTimeBound

/-! Transport of the exceptional-time bound under the exact change of units
`F u = G * f (u / G)`. The actual time sets and affine neighborhoods
are transported; their measure scaling is imported from mathlib. -/
namespace TransposeFollowup.AffineMotion
open Classical Set Finset MeasureTheory Transpose.Tape
open scoped ENNReal BigOperators
set_option autoImplicit false

noncomputable def scalePath (G : ℝ) (f : ℝ → ℝ) (u : ℝ) : ℝ := G*f (u/G)

theorem div_mem_scaled_interval {G H u : ℝ} (hG : 0 < G) :
    u/G ∈ Icc 0 H ↔ u ∈ Icc 0 (G*H) := by
  simp only [Set.mem_Icc,le_div_iff₀ hG,div_le_iff₀ hG,zero_mul,mul_comm H G]

theorem scalePath_lipschitz {G H : ℝ} (hG : 0 < G) {f : ℝ → ℝ}
    (hf : LipschitzOnWith 1 f (Icc 0 H)) :
    LipschitzOnWith 1 (scalePath G f) (Icc 0 (G*H)) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have h := hf.dist_le_mul (x/G) ((div_mem_scaled_interval hG).mpr hx)
    (y/G) ((div_mem_scaled_interval hG).mpr hy)
  simp only [NNReal.coe_one,one_mul,Real.dist_eq] at h ⊢
  calc
    |scalePath G f x-scalePath G f y| = G*|f (x/G)-f (y/G)| := by
      rw [scalePath,scalePath,← mul_sub,abs_mul,abs_of_pos hG]
    _ ≤ G*|x/G-y/G| := mul_le_mul_of_nonneg_left h hG.le
    _ = |x-y| := by rw [← sub_div,abs_div,abs_of_pos hG]; field_simp

theorem scale_omission_volume {G H : ℝ} (hG : 0 < G) (R : Set ℝ) :
    volume (Icc 0 (G*H) \ (fun u : ℝ => u/G) ⁻¹' R)=
      ENNReal.ofReal G*volume (Icc 0 H \ R) := by
  have he : Icc 0 (G*H) \ (fun u : ℝ => u/G) ⁻¹' R=
      (fun u : ℝ => G⁻¹*u) ⁻¹' (Icc 0 H \ R) := by
    ext u
    simp only [Set.mem_sdiff,Set.mem_preimage,div_eq_mul_inv,mul_comm G⁻¹ u]
    rw [← div_eq_mul_inv,div_mem_scaled_interval hG]
  rw [he,Real.volume_preimage_mul_left (inv_ne_zero hG.ne'),inv_inv,abs_of_pos hG]

theorem scale_local_affine {G : ℝ} (hG : 0 < G) (f : ℝ → ℝ) (R : Set ℝ)
    (hlocal : ∀ x ∈ R, ∃ U : Set ℝ, IsOpen U ∧ x ∈ U ∧ U ⊆ R ∧
      ∃ a b : ℝ, ∀ y ∈ U, f y=a*y+b) :
    ∀ x ∈ (fun u : ℝ => u/G) ⁻¹' R, ∃ U : Set ℝ,
      IsOpen U ∧ x ∈ U ∧ U ⊆ (fun u : ℝ => u/G) ⁻¹' R ∧
        ∃ a b : ℝ, ∀ y ∈ U, scalePath G f y=a*y+b := by
  intro x hx
  obtain ⟨U,hUo,hxU,hUR,a,b,ha⟩ := hlocal (x/G) hx
  refine ⟨(fun u : ℝ => u/G) ⁻¹' U,hUo.preimage (continuous_id.div_const G),
    hxU,Set.preimage_mono hUR,a,G*b,?_⟩
  intro y hy
  rw [scalePath,ha (y/G) hy]
  field_simp

theorem scale_omission_lower_bound {k : ℕ} {G H : ℝ} (hG : 0 < G)
    (R : Fin k → Set ℝ)
    (hs : (1/2 : ℝ≥0∞) ≤ ∑ t,
      volume (Icc 0 (G*H) \ (fun u : ℝ => u/G) ⁻¹' R t)) :
    (1/(2*ENNReal.ofReal G) : ℝ≥0∞) ≤ ∑ t, volume (Icc 0 H \ R t) := by
  simp_rw [scale_omission_volume hG] at hs
  rw [← Finset.mul_sum] at hs
  have hh := (ENNReal.div_le_iff' (show (2 : ℝ≥0∞) ≠ 0 by norm_num)
    (show (2 : ℝ≥0∞) ≠ ∞ by norm_num)).mp hs
  apply (ENNReal.div_le_iff' (mul_ne_zero (by norm_num) ((ENNReal.ofReal_pos.mpr hG).ne'))
    (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)).mpr
  simpa only [mul_assoc] using hh

theorem star_physical_affine_omission {k : ℕ} {G H : ℝ}
    (hG : 0 < G) (hH : 0 ≤ H) (f : Fin k → ℝ → ℝ)
    (hf : ∀ t, LipschitzOnWith 1 (f t) (Icc 0 H))
    (R : Fin k → Set ℝ) (hRI : ∀ t, R t ⊆ Icc 0 H)
    (hlocal : ∀ t x, x ∈ R t → ∃ U : Set ℝ, IsOpen U ∧ x ∈ U ∧ U ⊆ R t ∧
      ∃ a b : ℝ, ∀ y ∈ U, f t y=a*y+b)
    (hstar : SatisfiesStar (fun t => scalePath G (f t)) (G*H)) :
    (1/(2*ENNReal.ofReal G) : ℝ≥0∞) ≤ ∑ t, volume (Icc 0 H \ R t) := by
  have hs := star_half_le_locally_affine_omission (mul_nonneg hG.le hH)
    (fun t => scalePath G (f t)) (fun t => scalePath_lipschitz hG (hf t))
    (fun t => (fun u : ℝ => u/G) ⁻¹' R t)
    (fun t u hu => (div_mem_scaled_interval hG).mp (hRI t hu))
    (fun t => scale_local_affine hG (f t) (R t) (hlocal t)) hstar
  exact scale_omission_lower_bound hG R hs

theorem star_physical_affine_component_omission {k : ℕ} {G H : ℝ}
    (hG : 0 < G) (hH : 0 ≤ H) (f : Fin k → ℝ → ℝ)
    (hf : ∀ t, LipschitzOnWith 1 (f t) (Icc 0 H))
    (R : Fin k → Set ℝ) (hRo : ∀ t, IsOpen (R t)) (hRI : ∀ t, R t ⊆ Icc 0 H)
    (hPa : ∀ t x, x ∈ R t → ∃ a b : ℝ,
      ∀ y ∈ connectedComponentIn (R t) x, f t y=a*y+b)
    (hstar : SatisfiesStar (fun t => scalePath G (f t)) (G*H)) :
    (1/(2*ENNReal.ofReal G) : ℝ≥0∞) ≤ ∑ t, volume (Icc 0 H \ R t) := by
  apply star_physical_affine_omission hG hH f hf R hRI _ hstar
  intro t x hx
  exact ⟨connectedComponentIn (R t) x,(hRo t).connectedComponentIn,
    mem_connectedComponentIn hx,connectedComponentIn_subset (R t) x,hPa t x hx⟩

theorem star_physical_common_affine_omission {k : ℕ} (hk : 0 < k) {G H : ℝ}
    (hG : 0 < G) (hH : 0 ≤ H) (f : Fin k → ℝ → ℝ)
    (hf : ∀ t, LipschitzOnWith 1 (f t) (Icc 0 H))
    (R : Set ℝ) (hRo : IsOpen R) (hRI : R ⊆ Icc 0 H)
    (hPa : ∀ t x, x ∈ R → ∃ a b : ℝ,
      ∀ y ∈ connectedComponentIn R x, f t y=a*y+b)
    (hstar : SatisfiesStar (fun t => scalePath G (f t)) (G*H)) :
    (1/(2*k*ENNReal.ofReal G) : ℝ≥0∞) ≤ volume (Icc 0 H \ R) := by
  have hs := star_physical_affine_component_omission hG hH f hf (fun _ => R)
    (fun _ => hRo) (fun _ => hRI) hPa hstar
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
  have h2G : (2*ENNReal.ofReal G : ℝ≥0∞) ≠ 0 :=
    mul_ne_zero (by norm_num) ((ENNReal.ofReal_pos.mpr hG).ne')
  have h2Gt : (2*ENNReal.ofReal G : ℝ≥0∞) ≠ ∞ :=
    ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top
  have hh := (ENNReal.div_le_iff' h2G h2Gt).mp hs
  apply (ENNReal.div_le_iff' (by positivity)
    (by exact ENNReal.mul_ne_top (by finiteness) ENNReal.ofReal_ne_top)).mpr
  convert hh using 1; ac_rfl

end TransposeFollowup.AffineMotion
