import TransposeFollowup.BoundedAffineCovers
import Mathlib.Algebra.Order.Floor.Semifield

/-! Small closure interfaces for the existing affine-cover obstruction.
Clipped ramps have three pieces; sums use intersections of their covers.
The quantitative rounding lemma is mathlib's floor estimate transported
through its Lipschitz clipping map. -/
namespace TransposeFollowup.AffineMotion
open Classical Set Finset
set_option autoImplicit false

theorem HasAffineIntervalCover.const {H : ℝ} (hH : 0 ≤ H) (c : ℝ) :
    HasAffineIntervalCover 1 (fun _ => c) H := by
  refine ⟨fun _ => ⟨0,⟨le_rfl,hH⟩⟩,fun _ => ⟨H,⟨hH,le_rfl⟩⟩,
    fun x hx => ⟨0,hx⟩,?_⟩
  exact fun _ => ⟨0,c,fun _ _ => by ring⟩

theorem HasAffineIntervalCover.add {J K : ℕ} {H : ℝ} {f g : ℝ → ℝ}
    (hf : HasAffineIntervalCover J f H) (hg : HasAffineIntervalCover K g H) :
    HasAffineIntervalCover (J*K) (fun x => f x+g x) H := by
  obtain ⟨l,r,hcover,ha⟩ := hf
  obtain ⟨l',r',hcover',ha'⟩ := hg
  let e : Fin (J*K) ≃ Fin J × Fin K := finProdFinEquiv.symm
  refine ⟨fun i => max (l (e i).1) (l' (e i).2),
    fun i => min (r (e i).1) (r' (e i).2),?_,?_⟩
  · intro x hx
    obtain ⟨i,hi⟩ := hcover x hx
    obtain ⟨j,hj⟩ := hcover' x hx
    refine ⟨e.symm (i,j),?_⟩
    simp only [Equiv.apply_symm_apply]
    change max (l i : ℝ) (l' j) ≤ x ∧ x ≤ min (r i : ℝ) (r' j)
    exact ⟨max_le hi.1 hj.1,le_min hi.2 hj.2⟩
  · intro i
    obtain ⟨a,b,hab⟩ := ha (e i).1
    obtain ⟨c,d,hcd⟩ := ha' (e i).2
    refine ⟨a+c,b+d,fun x hx => ?_⟩
    change max (l (e i).1 : ℝ) (l' (e i).2) ≤ x ∧
      x ≤ min (r (e i).1 : ℝ) (r' (e i).2) at hx
    change f x+g x=_
    rw [hab x ⟨(le_max_left _ _).trans hx.1,hx.2.trans (min_le_left _ _)⟩,
      hcd x ⟨(le_max_right _ _).trans hx.1,hx.2.trans (min_le_right _ _)⟩]
    ring

theorem HasAffineIntervalCover.neg {J : ℕ} {H : ℝ} {f : ℝ → ℝ}
    (hf : HasAffineIntervalCover J f H) : HasAffineIntervalCover J (fun x => -f x) H := by
  obtain ⟨l,r,hcover,ha⟩ := hf
  refine ⟨l,r,hcover,fun i => ?_⟩
  obtain ⟨a,b,hab⟩ := ha i
  exact ⟨-a,-b,fun x hx => by change -f x=_; rw [hab x hx]; ring⟩

theorem HasAffineIntervalCover.sub {J K : ℕ} {H : ℝ} {f g : ℝ → ℝ}
    (hf : HasAffineIntervalCover J f H) (hg : HasAffineIntervalCover K g H) :
    HasAffineIntervalCover (J*K) (fun x => f x-g x) H := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem HasAffineIntervalCover.sum_range {J Q : ℕ} {H : ℝ} (hH : 0 ≤ H)
    (f : ℕ → ℝ → ℝ) (hf : ∀ i<Q, HasAffineIntervalCover J (f i) H) :
    HasAffineIntervalCover (J^Q) (fun x => ∑ i ∈ range Q, f i x) H := by
  induction Q with
  | zero => simpa using HasAffineIntervalCover.const hH 0
  | succ Q ih =>
    simpa only [pow_succ,Finset.sum_range_succ] using
      (ih (fun i hi => hf i (by omega))).add (hf Q (by omega))

theorem HasAffineIntervalCover.mono {J K : ℕ} {H : ℝ} {f : ℝ → ℝ}
    (hf : HasAffineIntervalCover J f H) (hJ : 0<J) (hJK : J ≤ K) :
    HasAffineIntervalCover K f H := by
  obtain ⟨l,r,hcover,ha⟩ := hf
  let e : Fin K → Fin J := fun i => ⟨min i.val (J-1),by have := Nat.min_le_right i.val (J-1); omega⟩
  refine ⟨l ∘ e,r ∘ e,?_,fun i => ha (e i)⟩
  intro x hx
  obtain ⟨i,hi⟩ := hcover x hx
  let j : Fin K := ⟨i.val,lt_of_lt_of_le i.isLt hJK⟩
  have he : e j=i := by apply Fin.ext; dsimp [e,j]; omega
  exact ⟨j,by simpa only [Function.comp_apply,he] using hi⟩

theorem HasAffineIntervalCover.rescale {J : ℕ} {H P : ℝ} {f : ℝ → ℝ}
    (hP : 0<P) (hf : HasAffineIntervalCover J f (P*H)) :
    HasAffineIntervalCover J (fun x => f (P*x)/P) H := by
  obtain ⟨l,r,hcover,ha⟩ := hf
  have hmem (x : Icc (0 : ℝ) (P*H)) : (x : ℝ)/P ∈ Icc 0 H :=
    ⟨div_nonneg x.property.1 hP.le,(div_le_iff₀ hP).mpr (by simpa [mul_comm] using x.property.2)⟩
  refine ⟨fun i => ⟨(l i : ℝ)/P,hmem (l i)⟩,
    fun i => ⟨(r i : ℝ)/P,hmem (r i)⟩,?_,?_⟩
  · intro x hx
    obtain ⟨i,hi⟩ := hcover (P*x) ⟨mul_nonneg hP.le hx.1,mul_le_mul_of_nonneg_left hx.2 hP.le⟩
    exact ⟨i,(div_le_iff₀ hP).mpr (by simpa [mul_comm] using hi.1),
      (le_div_iff₀ hP).mpr (by simpa [mul_comm] using hi.2)⟩
  · intro i
    obtain ⟨a,b,hab⟩ := ha i
    refine ⟨a,b/P,fun x hx => ?_⟩
    change f (P*x)/P=_
    rw [hab (P*x) ⟨by simpa [mul_comm] using (div_le_iff₀ hP).mp hx.1,
      by simpa [mul_comm] using (le_div_iff₀ hP).mp hx.2⟩]
    field_simp

noncomputable def clippedRamp (L a d t : ℝ) : ℝ := min (max ((t-a)/d) 0) L

theorem clippedRamp_cover {H L a d : ℝ} (hH : 0 ≤ H) (hL : 0 ≤ L)
    (ha : 0 ≤ a) (hd : 0<d) : HasAffineIntervalCover 3 (clippedRamp L a d) H := by
  let b := a+d*L
  have hab : a ≤ b := by dsimp [b]; nlinarith
  have hc : 0 ≤ min a H := le_min ha hH
  have hbc : min a H ≤ min b H := min_le_min_right H hab
  let l : Fin 3 → Icc (0 : ℝ) H := ![⟨0,⟨le_rfl,hH⟩⟩,
    ⟨min a H,⟨hc,min_le_right _ _⟩⟩,⟨min b H,⟨hc.trans hbc,min_le_right _ _⟩⟩]
  let r : Fin 3 → Icc (0 : ℝ) H := ![⟨min a H,⟨hc,min_le_right _ _⟩⟩,
    ⟨min b H,⟨hc.trans hbc,min_le_right _ _⟩⟩,⟨H,⟨hH,le_rfl⟩⟩]
  refine ⟨l,r,?_,?_⟩
  · intro x hx
    by_cases hxa : x ≤ min a H
    · exact ⟨0,hx.1,hxa⟩
    · by_cases hxb : x ≤ min b H
      · exact ⟨1,le_of_not_ge hxa,hxb⟩
      · exact ⟨2,le_of_not_ge hxb,hx.2⟩
  · intro i
    fin_cases i
    · refine ⟨0,0,fun x hx => ?_⟩
      have hxa : x ≤ a := hx.2.trans (min_le_left _ _)
      have hq : (x-a)/d ≤ 0 := div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hxa) hd.le
      rw [clippedRamp,max_eq_right hq,min_eq_left hL]
      ring
    · by_cases h : a ≤ H
      · refine ⟨1/d,-a/d,fun x hx => ?_⟩
        have hax' : min a H ≤ x := hx.1
        have hax : a ≤ x := by simpa only [min_eq_left h] using hax'
        have hxb : x ≤ b := hx.2.trans (min_le_left _ _)
        have hq0 : 0 ≤ (x-a)/d := div_nonneg (by linarith) hd.le
        have hqL : (x-a)/d ≤ L := (div_le_iff₀ hd).mpr (by dsimp [b] at hxb; nlinarith)
        rw [clippedRamp,max_eq_left hq0,min_eq_left hqL]
        ring
      · refine ⟨0,clippedRamp L a d H,fun x hx => ?_⟩
        have hax : H ≤ x := by simpa [l,min_eq_right (le_of_not_ge h)] using hx.1
        have hxH : x ≤ H := hx.2.trans (min_le_right _ _)
        rw [le_antisymm hxH hax]
        ring
    · by_cases h : b ≤ H
      · refine ⟨0,L,fun x hx => ?_⟩
        have hbx : b ≤ x := by simpa [l,min_eq_left h] using hx.1
        have hLq : L ≤ (x-a)/d := (le_div_iff₀ hd).mpr (by dsimp [b] at hbx; nlinarith)
        rw [clippedRamp,max_eq_left (hL.trans hLq),min_eq_right hLq]
        ring
      · refine ⟨0,clippedRamp L a d H,fun x hx => ?_⟩
        have hbx : H ≤ x := by simpa [l,min_eq_right (le_of_not_ge h)] using hx.1
        have hxH : x ≤ H := hx.2
        rw [le_antisymm hxH hbx]
        ring

theorem clippedRamp_sample_error (L a d : ℕ) (t : ℝ) :
    |((min ((⌊t⌋₊-a)/d) L : ℕ) : ℝ)-clippedRamp L a d t| ≤ 1 := by
  let x : ℝ := (t-a)/d
  have hx : |(⌊x⌋₊ : ℝ)-max x 0| ≤ 1 := by
    by_cases h : 0 ≤ x
    · simpa only [max_eq_left h] using Nat.abs_floor_sub_le h
    · simp [max_eq_right (le_of_not_ge h),Nat.floor_of_nonpos (le_of_not_ge h)]
  have he : (⌊t⌋₊-a)/d=⌊x⌋₊ := by
    simp only [x,Nat.floor_div_natCast,Nat.floor_sub_natCast]
  rw [he,Nat.cast_min]
  exact ((LipschitzWith.id.min_const (L : ℝ)).dist_le_mul (⌊x⌋₊ : ℝ) (max x 0) |>.trans
    (by simpa only [NNReal.coe_one,one_mul,Real.dist_eq] using hx))

end TransposeFollowup.AffineMotion
