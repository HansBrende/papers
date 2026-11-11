import SharedDecoders.CapacityMaskRunProbability
import SharedDecoders.CapacityMaskComparisonProbability

/-! # The full actual fixed-depth balanced-ternary spectrum -/

namespace SharedDecoders.CapacityTernarySpectrum

open CapacityRuns CapacityMask CapacityMaskProbability Module
open scoped BigOperators

/-- Half of `3^j-1`, defined without truncated subtraction or division. -/
def radius : ℕ → ℕ
  | 0 => 0
  | j+1 => 3*radius j+1

theorem radius_power (j : ℕ) : 2*radius j+1=3^j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [radius,pow_succ]; nlinarith only [ih]

theorem radius_formula (j : ℕ) : radius j=(3^j-1)/2 := by
  have hh := radius_power j
  omega

theorem radius_mono : Monotone radius := by
  apply monotone_nat_of_le_succ
  intro j
  simp only [radius]
  omega

theorem radius_pos {j : ℕ} (hj : 0<j) : 0<radius j := by
  have hh := radius_mono (show 1≤j by omega)
  norm_num [radius] at hh
  omega

theorem radius_two {j : ℕ} (hj : 2≤j) : 2≤radius j := by
  have hh := radius_mono hj
  norm_num [radius] at hh
  omega

def shifts {d : ℕ} (j : ℕ) : ZMod d := (3^j : ℕ)

/-- A balanced-ternary digit is implemented as the difference of two actual
translate-set digits. No interval-coverage certificate is assumed. -/
theorem cover_extend {d : ℕ} (Δ : Finset (ZMod d)) (r : ℕ)
    (hcover : CoversRadius Δ 1 r) :
    CoversRadius (extendShifts Δ ((2*r+1 : ℕ) : ZMod d)) 1 (3*r+1) := by
  intro j hj
  by_cases hsmall : j≤r
  · obtain ⟨u,hu,v,hv,he⟩ := hcover j hsmall
    exact ⟨u,Finset.mem_union_left _ hu,v,Finset.mem_union_left _ hv,he⟩
  by_cases hmid : j≤2*r+1
  · obtain ⟨u,hu,v,hv,he⟩ := hcover (2*r+1-j) (by omega)
    refine ⟨v+(2*r+1 : ℕ),Finset.mem_union_right _ (Finset.mem_image_of_mem _ hv),
      u,Finset.mem_union_left _ hu,?_⟩
    simp only [nsmul_eq_mul,mul_one] at he ⊢
    rw [Nat.cast_sub hmid] at he
    linear_combination -he
  · obtain ⟨u,hu,v,hv,he⟩ := hcover (j-(2*r+1)) (by omega)
    refine ⟨u+(2*r+1 : ℕ),Finset.mem_union_right _ (Finset.mem_image_of_mem _ hu),
      v,Finset.mem_union_left _ hv,?_⟩
    simp only [nsmul_eq_mul,mul_one] at he ⊢
    rw [Nat.cast_sub (by omega : 2*r+1≤j)] at he
    linear_combination he

theorem actual_cover {d : ℕ} (j : ℕ) :
    CoversRadius (translateSets (shifts (d := d)) j) 1 (radius j) := by
  induction j with
  | zero =>
    intro i hi
    have hi0 : i=0 := by change i≤0 at hi; omega
    subst i
    exact ⟨0,by simp [translateSets],0,by simp [translateSets],by simp⟩
  | succ j ih =>
    simpa only [translateSets,shifts,← radius_power j,radius] using
      cover_extend (translateSets shifts j) (radius j) ih

variable {d : ℕ} [NeZero d]

theorem actual_component_bound (hd : 1<d) (p : ZMod d → Bool) (j : ℕ) (hj : 0<j) :
    componentCount p (translateSets shifts j)≤
      runCount p 1 (radius j)+(if j=1 then 1 else 2) := by
  have hg : Nat.gcd d (1 : ZMod d).val=1 := by
    rw [show (1 : ZMod d).val=1 by simpa only [Nat.cast_one] using ZMod.val_natCast_of_lt hd,
      Nat.gcd_one_right]
  by_cases hj1 : j=1
  · subst j
    have hh := componentCount_first_shift p (1 : ZMod d)
    simp only [← runCount_one,hg] at hh
    simpa [translateSets,shifts,radius] using hh
  · have hh := componentCount_le_runs_add_two_gcd p _ 1 (radius j)
      (radius_two (by omega)) (actual_cover j)
    simpa only [hg,mul_one,ite_eq_right hj1] using hh

noncomputable def runSequence (p : ZMod d → Bool) (j : ℕ) : ℝ :=
  if j=0 then 0 else runCount p 1 (radius j)

noncomputable def spectrum (k : ℕ) (p : ZMod d → Bool) : ℝ := certificate (runSequence p) k

def errorSequence (j : ℕ) : ℝ := if j=0 then 0 else if j=1 then 1 else 2

theorem certificate_add (x y : ℕ → ℝ) (k : ℕ) :
    certificate (fun j => x j+y j) k=certificate x k+certificate y k := by
  simp only [certificate,add_div,Finset.sum_add_distrib]
  ring

theorem certificate_mono {x y : ℕ → ℝ} (h : ∀ j, x j≤y j) (k : ℕ) :
    certificate x k≤certificate y k := by
  exact add_le_add (Finset.sum_le_sum (fun j _ => div_le_div_of_nonneg_right (h j) (by positivity)))
    (div_le_div_of_nonneg_right (h k) (by positivity))

theorem certificate_delta (a : ℝ) (k : ℕ) (hk : 0<k) :
    certificate (fun j => if j=0 then a else 0) k=a/2 := by
  simp [certificate,ite_div,Nat.ne_zero_of_lt hk,Finset.sum_ite_eq',Finset.mem_range.mpr hk]

theorem certificate_successor (x : ℕ → ℝ) (k : ℕ) :
    certificate x (k+1)=certificate x k+(x (k+1)-x k)/2^(k+1) := by
  rw [certificate,certificate,Finset.sum_range_succ,pow_succ]
  field_simp
  ring

theorem certificate_error (k : ℕ) (hk : 2≤k) : certificate errorSequence k=3/4 := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le hk
  clear hk
  induction n with
  | zero => norm_num [certificate,errorSequence,Finset.sum_range_succ]
  | succ n ih =>
    rw [show 2+(n+1)=(2+n)+1 by omega,certificate_successor,ih]
    simp [errorSequence,show 2+n≠1 by omega]

theorem spectrum_expansion (k : ℕ) (hk : 0<k) (p : ZMod d → Bool) :
    spectrum k p=(∑ i ∈ Finset.range (k-1),
      (runCount p 1 (radius (i+1)) : ℝ)/2^(i+2))+
      (runCount p 1 (radius k) : ℝ)/2^k := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hk)
  simp [spectrum,certificate,Finset.sum_range_succ',runSequence,Nat.add_assoc]

variable {F A : Type*} [Field F] [AddCommGroup A] [Module F A] [FiniteDimensional F A]

/-- The actual nested shift chain yields the complete fixed-depth source
inequality, with the exact error `3bd/4` at every depth at least two. -/
theorem source_bound (hd : 1<d) (k : ℕ) (hk : 2≤k) {p : ZMod d → Bool}
    {C : Submodule F (State d A)} (h : IsSharedCode F p C) :
    (finrank F C : ℝ)≤(d : ℝ)^2*finrank F A/2+
      (d : ℝ)*finrank F A*spectrum k p+(3/4)*(d : ℝ)*finrank F A := by
  have hh := h.iterated_finrank_le (shifts (d := d)) k
  let b : ℝ := finrank F A
  let N : ℝ := (d : ℝ)^2*b
  let m : ℕ → ℝ := fun j => (d : ℝ)*b*componentCount p (translateSets shifts j)
  have hstart : (finrank F C : ℝ)≤certificate m k := by
    simpa only [certificate,m,b,Nat.cast_mul,mul_comm,mul_left_comm,mul_assoc] using hh
  let upper : ℕ → ℝ := fun j => (if j=0 then N else 0)+
    ((d : ℝ)*b)*runSequence p j+((d : ℝ)*b)*errorSequence j
  have hm : ∀ j, m j≤upper j := by
    intro j
    by_cases hj : j=0
    · subst j
      simp [m,upper,runSequence,errorSequence,translateSets,componentCount_zero,N,pow_two,mul_assoc,mul_comm]
    · have hc : (componentCount p (translateSets shifts j) : ℝ)≤
          (runCount p 1 (radius j) : ℝ)+(if j=1 then 1 else 2) := by
        exact_mod_cast actual_component_bound hd p j (by omega)
      have hmul := mul_le_mul_of_nonneg_left hc (show (0 : ℝ)≤(d : ℝ)*b by dsimp [b]; positivity)
      simpa only [m,upper,runSequence,errorSequence,ite_eq_right hj,zero_add,mul_add] using hmul
  have hupper := hstart.trans (certificate_mono hm k)
  simp only [upper,certificate_add,certificate_const_mul,
    certificate_delta N k (by omega),certificate_error k hk] at hupper
  dsimp [N,b] at hupper
  dsimp only [spectrum]
  nlinarith only [hupper]

end SharedDecoders.CapacityTernarySpectrum
