import TransposeFollowup.MobiusCalculus

/-! Quantitative denominator, displacement, Jacobian and support bounds.
The same coefficient hypothesis applies to the adjugate inverse. -/
namespace TransposeFollowup
open Set MeasureTheory
set_option autoImplicit false

namespace RationalUnitMobius

structure NearIdentity (F : RationalUnitMobius) (eta : ℝ) : Prop where
  a_bound : |(F.a:ℝ)-1| ≤ eta
  b_bound : |(F.b:ℝ)| ≤ eta
  c_bound : |(F.c:ℝ)| ≤ eta
  d_bound : |(F.d:ℝ)-1| ≤ eta

namespace NearIdentity
variable {F : RationalUnitMobius} {eta : ℝ}

theorem nonneg (h : F.NearIdentity eta) : 0 ≤ eta := (abs_nonneg _).trans h.b_bound

theorem inverse (h : F.NearIdentity eta) : F.inverse.NearIdentity eta := by
  refine ⟨h.d_bound,?_,?_,h.a_bound⟩
  · simpa only [RationalUnitMobius.inverse,Rat.cast_neg,abs_neg] using h.b_bound
  · simpa only [RationalUnitMobius.inverse,Rat.cast_neg,abs_neg] using h.c_bound

theorem of_squared (he : 0 ≤ eta)
    (h : ((F.a:ℝ)-1)^2+(F.b:ℝ)^2+(F.c:ℝ)^2+((F.d:ℝ)-1)^2 ≤ eta^2) :
    F.NearIdentity eta := by
  constructor <;> apply abs_le.mpr <;> constructor <;>
    nlinarith [sq_nonneg ((F.a:ℝ)-1),sq_nonneg (F.b:ℝ),
      sq_nonneg (F.c:ℝ),sq_nonneg ((F.d:ℝ)-1)]

theorem denom_error (h : F.NearIdentity eta) {x : ℝ} (hx : x∈Icc (0:ℝ) 1) :
    |F.whole.denom x-1| ≤ 2*eta := by
  have hxabs : |x| ≤ 1 := by simpa only [abs_of_nonneg hx.1] using hx.2
  have hcx : |(F.c:ℝ)*x| ≤ eta := by
    rw [abs_mul]
    simpa using mul_le_mul h.c_bound hxabs (abs_nonneg _) h.nonneg
  calc
    _ = |(F.c:ℝ)*x+((F.d:ℝ)-1)| := by congr 1; dsimp [RationalMobius.denom,whole]; ring
    _ ≤ |(F.c:ℝ)*x|+|(F.d:ℝ)-1| := abs_add_le _ _
    _ ≤ 2*eta := by linarith [h.d_bound]

theorem denom_bounds (h : F.NearIdentity eta) {x : ℝ} (hx : x∈Icc (0:ℝ) 1) :
    1-2*eta ≤ F.whole.denom x ∧ F.whole.denom x ≤ 1+2*eta := by
  have he := abs_le.mp (h.denom_error hx)
  constructor <;> linarith [he.1,he.2]

theorem determinant_error (h : F.NearIdentity eta) (he : eta ≤ 1/8) :
    |(F.whole.delta:ℝ)-1| ≤ 3*eta := by
  have had : |((F.a:ℝ)-1)*((F.d:ℝ)-1)| ≤ eta^2 := by
    rw [abs_mul,pow_two]
    exact mul_le_mul h.a_bound h.d_bound (abs_nonneg _) h.nonneg
  have hbc : |(F.b:ℝ)*(F.c:ℝ)| ≤ eta^2 := by
    rw [abs_mul,pow_two]
    exact mul_le_mul h.b_bound h.c_bound (abs_nonneg _) h.nonneg
  have he2 := mul_le_mul_of_nonneg_right he h.nonneg
  calc
    _ = |((F.a:ℝ)-1)+((F.d:ℝ)-1)+((F.a:ℝ)-1)*((F.d:ℝ)-1)-(F.b:ℝ)*(F.c:ℝ)| := by
      congr 1
      dsimp [RationalMobius.delta,whole]
      push_cast
      ring
    _ ≤ |((F.a:ℝ)-1)+((F.d:ℝ)-1)+((F.a:ℝ)-1)*((F.d:ℝ)-1)|+|(F.b:ℝ)*(F.c:ℝ)| := abs_sub _ _
    _ ≤ 3*eta := by
      have ha := abs_add_le ((F.a:ℝ)-1) ((F.d:ℝ)-1)
      have hb := abs_add_le (((F.a:ℝ)-1)+((F.d:ℝ)-1)) (((F.a:ℝ)-1)*((F.d:ℝ)-1))
      nlinarith only [ha,hb,had,hbc,h.a_bound,h.d_bound,he2,h.nonneg]

theorem eval_displacement (h : F.NearIdentity eta) (he : eta ≤ 1/8)
    {x : ℝ} (hx : x∈Icc (0:ℝ) 1) : |F.whole.eval x-x| ≤ 8*eta := by
  have hxabs : |x| ≤ 1 := by simpa only [abs_of_nonneg hx.1] using hx.2
  have hx2 : x^2 ≤ 1 := by nlinarith [hx.1,hx.2]
  have ha : |((F.a:ℝ)-1)*x| ≤ eta := by
    rw [abs_mul]
    simpa using mul_le_mul h.a_bound hxabs (abs_nonneg _) h.nonneg
  have hd : |((F.d:ℝ)-1)*x| ≤ eta := by
    rw [abs_mul]
    simpa using mul_le_mul h.d_bound hxabs (abs_nonneg _) h.nonneg
  have hc : |(F.c:ℝ)*x^2| ≤ eta := by
    rw [abs_mul,abs_of_nonneg (sq_nonneg x)]
    simpa using mul_le_mul h.c_bound hx2 (sq_nonneg x) h.nonneg
  have hq : 0<F.whole.denom x := F.whole_denom_pos hx
  have hv : F.whole.eval x*F.whole.denom x=(F.a:ℝ)*x+F.b := div_mul_cancel₀ _ hq.ne'
  have hi : (F.whole.eval x-x)*F.whole.denom x=
      (((F.a:ℝ)-1)*x+F.b)-((F.c:ℝ)*x^2+((F.d:ℝ)-1)*x) := by
    calc
      _ = F.whole.eval x*F.whole.denom x-x*F.whole.denom x := by ring
      _ = _ := by rw [hv]; dsimp [RationalMobius.denom,whole]; ring
  have hn : |(F.whole.eval x-x)*F.whole.denom x| ≤ 4*eta := by
    rw [hi]
    have h1 := abs_sub (((F.a:ℝ)-1)*x+F.b) ((F.c:ℝ)*x^2+((F.d:ℝ)-1)*x)
    have h2 := abs_add_le (((F.a:ℝ)-1)*x) (F.b:ℝ)
    have h3 := abs_add_le ((F.c:ℝ)*x^2) (((F.d:ℝ)-1)*x)
    linarith [h.b_bound]
  rw [abs_mul,abs_of_pos hq] at hn
  have hq2 : (1/2:ℝ) ≤ F.whole.denom x := by linarith [(h.denom_bounds hx).1]
  have hp := mul_le_mul_of_nonneg_left hq2 (abs_nonneg (F.whole.eval x-x))
  nlinarith only [hn,hp]

theorem derivative_error (h : F.NearIdentity eta) (he : eta ≤ 1/8)
    {x : ℝ} (hx : x∈Icc (0:ℝ) 1) : |F.whole.derivative x-1| ≤ 32*eta := by
  have he0 := h.nonneg
  let q := F.whole.denom x
  have hq : 0<q := F.whole_denom_pos hx
  have hb := h.denom_bounds hx
  have hq2 : (1/2:ℝ) ≤ q := by dsimp [q]; linarith [hb.1]
  have hqp : |q+1| ≤ (5/2:ℝ) := by
    rw [abs_of_pos (by linarith : 0<q+1)]
    dsimp [q]
    linarith [hb.2]
  have hsq : |q^2-1| ≤ 5*eta := by
    calc
      _ = |q-1| *|q+1| := by rw [← abs_mul]; congr 1; ring
      _ ≤ (2*eta)*(5/2) := mul_le_mul (h.denom_error hx) hqp (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hnum : |(F.whole.delta:ℝ)-q^2| ≤ 8*eta := by
    have ht := abs_sub_le (F.whole.delta:ℝ) 1 (q^2)
    rw [abs_sub_comm 1] at ht
    linarith [h.determinant_error he]
  have hid : (F.whole.derivative x-1)*q^2=(F.whole.delta:ℝ)-q^2 := by
    change ((F.whole.delta:ℝ)/q^2-1)*q^2=_
    field_simp
  have hn : |F.whole.derivative x-1| *q^2 ≤ 8*eta := by
    calc
      _ = |(F.whole.derivative x-1)*q^2| := by rw [abs_mul,abs_of_nonneg (sq_nonneg q)]
      _ ≤ _ := by rw [hid]; exact hnum
  have hsqlo : (1/4:ℝ) ≤ q^2 := by nlinarith only [hq2]
  have hp := mul_le_mul_of_nonneg_left hsqlo (abs_nonneg (F.whole.derivative x-1))
  nlinarith only [hn,hp]

theorem mapsTo_central (h : F.NearIdentity eta) (he : eta ≤ 1/8)
    {r : ℝ} (hr : 8*eta ≤ r) : MapsTo F.whole.eval (Icc r (1-r)) (Icc (0:ℝ) 1) := by
  intro x hx
  have hr0 : 0 ≤ r := (mul_nonneg (by norm_num : (0:ℝ) ≤ 8) h.nonneg).trans hr
  have hxunit : x∈Icc (0:ℝ) 1 := ⟨hr0.trans hx.1,by linarith [hx.2]⟩
  have hd := abs_le.mp (h.eval_displacement he hxunit)
  constructor <;> linarith [hd.1,hd.2,hx.1,hx.2]

theorem sqrt_derivative_error (h : F.NearIdentity eta) (he : eta ≤ 1/8)
    {x : ℝ} (hx : x∈Icc (0:ℝ) 1) : |Real.sqrt (F.whole.derivative x)-1| ≤ 32*eta := by
  have hp : 0<F.whole.derivative x := F.whole.derivative_pos (by simpa [whole] using hx)
  have hs := Real.sqrt_nonneg (F.whole.derivative x)
  calc
    _ ≤ |Real.sqrt (F.whole.derivative x)-1| * |Real.sqrt (F.whole.derivative x)+1| :=
      le_mul_of_one_le_right (abs_nonneg _) (by rw [abs_of_nonneg (by linarith)]; linarith)
    _ = |F.whole.derivative x-1| := by
      rw [← abs_mul]
      congr 1
      nlinarith only [Real.sq_sqrt hp.le]
    _ ≤ _ := h.derivative_error he hx

theorem central_subset_clipped (h : F.NearIdentity eta) (he : eta ≤ 1/8)
    {r : ℝ} (hr : 8*eta ≤ r) : Icc r (1-r)⊆Icc (F.clipped.lo:ℝ) F.clipped.hi := by
  intro x hx
  rw [F.clipped_domain]
  have hr0 : 0 ≤ r := (mul_nonneg (by norm_num : (0:ℝ) ≤ 8) h.nonneg).trans hr
  exact ⟨⟨hr0.trans hx.1,by linarith [hx.2]⟩,h.mapsTo_central he hr hx⟩

theorem central_preimage_eq_inverse_image (h : F.NearIdentity eta) (he : eta ≤ 1/8)
    {r : ℝ} (hr : 8*eta ≤ r) {A : Set ℝ} (hcentral : A⊆Icc r (1-r)) :
    Icc (0:ℝ) 1 ∩ F.whole.eval ⁻¹' A=F.inverse.whole.eval '' A := by
  apply F.unit_preimage_eq_inverse_image
  · intro x hx
    have hr0 : 0 ≤ r := (mul_nonneg (by norm_num : (0:ℝ) ≤ 8) h.nonneg).trans hr
    exact ⟨hr0.trans (hcentral hx).1,by linarith [(hcentral hx).2]⟩
  · exact fun x hx => h.inverse.mapsTo_central he hr (hcentral hx)

theorem volume_distortion (h : F.NearIdentity eta) (he : eta ≤ 1/8)
    {A : Set ℝ} (hA : MeasurableSet A) (hunit : A⊆Icc (0:ℝ) 1) :
    (1-32*eta)*volume.real A ≤ volume.real (F.whole.eval '' A) ∧
      volume.real (F.whole.eval '' A) ≤ (1+32*eta)*volume.real A := by
  have hsub : A⊆Icc (F.whole.lo:ℝ) F.whole.hi := by simpa [whole] using hunit
  rw [F.whole.volume_real_image_eval hA hsub]
  have hd := F.whole.integrableOn_derivative hsub
  have hfinite : volume A≠⊤ := ne_top_of_le_ne_top (by simp) (measure_mono hunit)
  have hlo : IntegrableOn (fun _ : ℝ => 1-32*eta) A := integrableOn_const hfinite
  have hhi : IntegrableOn (fun _ : ℝ => 1+32*eta) A := integrableOn_const hfinite
  constructor
  · have hb := setIntegral_mono_on hlo hd hA (fun x hx => by
      have hh := (abs_le.mp (h.derivative_error he (hunit hx))).1
      linarith)
    simpa only [setIntegral_const,smul_eq_mul,mul_comm] using hb
  · have hb := setIntegral_mono_on hd hhi hA (fun x hx => by
      have hh := (abs_le.mp (h.derivative_error he (hunit hx))).2
      linarith)
    simpa only [setIntegral_const,smul_eq_mul,mul_comm] using hb

end NearIdentity
end RationalUnitMobius
end TransposeFollowup
