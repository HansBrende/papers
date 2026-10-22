import TransposeFollowup.RationalFamilyGraph

/-! Rational coefficient data for the unit-interval restrictions used in
the continuous-expander construction. The six strict linear inequalities
hold near the identity and are preserved by the adjugate inverse. They
ensure that the clipped domain has nonempty interior and rational ends.
No expansion assumption is used in this file. -/
namespace TransposeFollowup
open Set
set_option autoImplicit false

structure RationalUnitMobius where
  a : ℚ
  b : ℚ
  c : ℚ
  d : ℚ
  determinant_pos : 0 < a*d-b*c
  a_pos : 0 < a
  d_pos : 0 < d
  a_sub_c_pos : 0 < a-c
  c_add_d_pos : 0 < c+d
  a_add_b_pos : 0 < a+b
  d_sub_b_pos : 0 < d-b

namespace RationalUnitMobius
variable (F : RationalUnitMobius)

def lower : ℚ := max 0 (-F.b/F.a)
def upper : ℚ := min 1 ((F.d-F.b)/(F.a-F.c))

theorem lower_lt_upper : F.lower < F.upper := by
  unfold lower upper
  apply max_lt
  · exact lt_min (by norm_num) (div_pos F.d_sub_b_pos F.a_sub_c_pos)
  · apply lt_min
    · apply (div_lt_iff₀ F.a_pos).mpr
      linarith [F.a_add_b_pos]
    · apply (div_lt_div_iff₀ F.a_pos F.a_sub_c_pos).mpr
      nlinarith [F.determinant_pos]

theorem lower_nonneg : 0 ≤ F.lower := le_max_left _ _
theorem upper_le_one : F.upper ≤ 1 := min_le_left _ _

def whole : RationalMobius where
  a := F.a
  b := F.b
  c := F.c
  d := F.d
  lo := 0
  hi := 1
  interval_nonempty := by norm_num
  determinant_pos := F.determinant_pos
  denominator_lo_pos := by simpa using F.d_pos
  denominator_hi_pos := by simpa using F.c_add_d_pos

theorem whole_denom_pos {x : ℝ} (hx : x∈Icc (0:ℝ) 1) :
    0<(F.c:ℝ)*x+F.d := by
  have hx' : x∈Icc (F.whole.lo:ℝ) F.whole.hi := by simpa [whole] using hx
  exact F.whole.denom_pos hx'

def clipped : RationalMobius where
  a := F.a
  b := F.b
  c := F.c
  d := F.d
  lo := F.lower
  hi := F.upper
  interval_nonempty := F.lower_lt_upper
  determinant_pos := F.determinant_pos
  denominator_lo_pos := by
    have hx : (F.lower:ℝ) ∈ Icc (0:ℝ) 1 := by
      constructor
      · exact_mod_cast F.lower_nonneg
      · exact_mod_cast F.lower_lt_upper.le.trans F.upper_le_one
    exact_mod_cast F.whole_denom_pos hx
  denominator_hi_pos := by
    have hx : (F.upper:ℝ) ∈ Icc (0:ℝ) 1 := by
      constructor
      · exact_mod_cast F.lower_nonneg.trans F.lower_lt_upper.le
      · exact_mod_cast F.upper_le_one
    exact_mod_cast F.whole_denom_pos hx

theorem clipped_eval : F.clipped.eval = F.whole.eval := rfl

theorem clipped_domain :
    Icc (F.clipped.lo:ℝ) F.clipped.hi =
      Icc (0:ℝ) 1 ∩ F.whole.eval ⁻¹' Icc (0:ℝ) 1 := by
  have ha : (0:ℝ)<F.a := by exact_mod_cast F.a_pos
  have hac : (0:ℝ)<(F.a:ℝ)-F.c := by exact_mod_cast F.a_sub_c_pos
  have hl : (F.clipped.lo:ℝ)=max 0 (-(F.b:ℝ)/F.a) := by
    simp only [clipped,lower,Rat.cast_max,Rat.cast_zero,Rat.cast_div,Rat.cast_neg]
  have hu : (F.clipped.hi:ℝ)=min 1 (((F.d:ℝ)-F.b)/((F.a:ℝ)-F.c)) := by
    simp only [clipped,upper,Rat.cast_min,Rat.cast_one,Rat.cast_div,Rat.cast_sub]
  ext x
  rw [hl,hu]
  simp only [mem_Icc,max_le_iff,le_min_iff,mem_inter_iff,mem_preimage]
  have heval : F.whole.eval x=((F.a:ℝ)*x+F.b)/((F.c:ℝ)*x+F.d) := rfl
  constructor
  · rintro ⟨⟨hx0,hlo⟩,hx1,hhi⟩
    have hd : 0<(F.c:ℝ)*x+F.d := F.whole_denom_pos ⟨hx0,hx1⟩
    rw [div_le_iff₀ ha] at hlo
    rw [le_div_iff₀ hac] at hhi
    refine ⟨⟨hx0,hx1⟩,?_,?_⟩
    · rw [heval]
      exact div_nonneg (by nlinarith) hd.le
    · rw [heval,div_le_one hd]
      nlinarith
  · rintro ⟨⟨hx0,hx1⟩,hy0,hy1⟩
    have hd : 0<(F.c:ℝ)*x+F.d := F.whole_denom_pos ⟨hx0,hx1⟩
    rw [heval] at hy0 hy1
    have hnum : 0≤(F.a:ℝ)*x+F.b := by simpa using (le_div_iff₀ hd).mp hy0
    rw [div_le_one hd] at hy1
    refine ⟨⟨hx0,?_⟩,hx1,?_⟩
    · apply (div_le_iff₀ ha).mpr
      nlinarith
    · apply (le_div_iff₀ hac).mpr
      nlinarith

theorem clipped_mapsTo : MapsTo F.clipped.eval (Icc (F.clipped.lo:ℝ) F.clipped.hi)
    (Icc (0:ℝ) 1) := by
  intro x hx
  rw [F.clipped_domain] at hx
  exact hx.2

theorem clipped_open_mapsTo : MapsTo F.clipped.bounded.map F.clipped.bounded.domain
    (Icc (0:ℝ) 1) := fun _ hx => F.clipped_mapsTo (Ioo_subset_Icc_self hx)

def inverse : RationalUnitMobius where
  a := F.d
  b := -F.b
  c := -F.c
  d := F.a
  determinant_pos := by nlinarith [F.determinant_pos]
  a_pos := F.d_pos
  d_pos := F.a_pos
  a_sub_c_pos := by simpa [sub_eq_add_neg,add_comm] using F.c_add_d_pos
  c_add_d_pos := by simpa [sub_eq_add_neg,add_comm] using F.a_sub_c_pos
  a_add_b_pos := by simpa [sub_eq_add_neg] using F.d_sub_b_pos
  d_sub_b_pos := by simpa using F.a_add_b_pos

def identity : RationalUnitMobius where
  a := 1
  b := 0
  c := 0
  d := 1
  determinant_pos := by norm_num
  a_pos := by norm_num
  d_pos := by norm_num
  a_sub_c_pos := by norm_num
  c_add_d_pos := by norm_num
  a_add_b_pos := by norm_num
  d_sub_b_pos := by norm_num

def translation (t : ℚ) (ht : |t|<1) : RationalUnitMobius where
  a := 1
  b := t
  c := 0
  d := 1
  determinant_pos := by norm_num
  a_pos := by norm_num
  d_pos := by norm_num
  a_sub_c_pos := by norm_num
  c_add_d_pos := by norm_num
  a_add_b_pos := by have := (abs_lt.mp ht).1;linarith
  d_sub_b_pos := by have := (abs_lt.mp ht).2;linarith

theorem identity_eval (x : ℝ) : identity.whole.eval x=x := by
  simp [whole,identity,RationalMobius.eval]

theorem translation_eval (t : ℚ) (ht : |t|<1) (x : ℝ) :
    (translation t ht).whole.eval x=x+t := by
  simp [whole,translation,RationalMobius.eval]

/-- A concrete neighborhood sufficient for all clipping obligations. -/
def of_near_identity (a b c d : ℚ) (hdet : 0<a*d-b*c)
    (ha : |a-1|<1/4) (hb : |b|<1/4) (hc : |c|<1/4) (hd : |d-1|<1/4) :
    RationalUnitMobius where
  a := a
  b := b
  c := c
  d := d
  determinant_pos := hdet
  a_pos := by have := (abs_lt.mp ha).1;linarith
  d_pos := by have := (abs_lt.mp hd).1;linarith
  a_sub_c_pos := by have := (abs_lt.mp ha).1;have := (abs_lt.mp hc).2;linarith
  c_add_d_pos := by have := (abs_lt.mp hc).1;have := (abs_lt.mp hd).1;linarith
  a_add_b_pos := by have := (abs_lt.mp ha).1;have := (abs_lt.mp hb).1;linarith
  d_sub_b_pos := by have := (abs_lt.mp hd).1;have := (abs_lt.mp hb).2;linarith

/-- The squared coefficient-distance condition directly used near the identity. -/
def of_squared_near_identity (a b c d : ℚ) (hdet : 0<a*d-b*c)
    (hsmall : (a-1)^2+b^2+c^2+(d-1)^2<1/16) : RationalUnitMobius :=
  of_near_identity a b c d hdet
    (by apply abs_lt.mpr;constructor <;>
      nlinarith [sq_nonneg (a-1),sq_nonneg b,sq_nonneg c,sq_nonneg (d-1)])
    (by apply abs_lt.mpr;constructor <;>
      nlinarith [sq_nonneg (a-1),sq_nonneg b,sq_nonneg c,sq_nonneg (d-1)])
    (by apply abs_lt.mpr;constructor <;>
      nlinarith [sq_nonneg (a-1),sq_nonneg b,sq_nonneg c,sq_nonneg (d-1)])
    (by apply abs_lt.mpr;constructor <;>
      nlinarith [sq_nonneg (a-1),sq_nonneg b,sq_nonneg c,sq_nonneg (d-1)])

theorem inverse_eval (x : ℝ) :
    F.inverse.whole.eval x=((F.d:ℝ)*x-F.b)/(-(F.c:ℝ)*x+F.a) := by
  simp only [whole,inverse,RationalMobius.eval,Rat.cast_neg,sub_eq_add_neg]

/-- The three auxiliary maps in the source: two opposite translations and identity. -/
def auxiliaries (t : ℚ) (ht : |t|<1) : Fin 3 → RationalUnitMobius :=
  ![translation t ht,translation (-t) (by simpa using ht),identity]

def augmentedFamily {c : ℕ} (F : Fin c → RationalUnitMobius) (t : ℚ) (ht : |t|<1) :
    Fin (c+c+3) → RationalUnitMobius :=
  Fin.addCases (Fin.addCases F (fun p => (F p).inverse)) (auxiliaries t ht)

theorem auxiliary_eval (t : ℚ) (ht : |t|<1) (x : ℝ) :
    (auxiliaries t ht 0).whole.eval x=x+t ∧
    (auxiliaries t ht 1).whole.eval x=x-t ∧
    (auxiliaries t ht 2).whole.eval x=x := by
  simp [auxiliaries,whole,translation,identity,RationalMobius.eval,sub_eq_add_neg]

end RationalUnitMobius
end TransposeFollowup
