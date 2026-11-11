import SharedDecoders.CapacityMaskEdges
import SharedDecoders.CapacityClosureIsolation
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Numerical limitations of the specified translate certificates

These are lower bounds on numerical proof certificates, not on source
capacity. The simultaneous concentration events are separate statements.
-/

namespace SharedDecoders.CapacityMask

open Module CapacityRuns
open scoped BigOperators
attribute [local instance] Classical.propDecidable

noncomputable def certificate (n : ℕ → ℝ) (k : ℕ) : ℝ :=
  (∑ j ∈ Finset.range k, n j / 2^(j+1)) + n k / 2^k

theorem certificate_nonneg (n : ℕ → ℝ) (hn : ∀ j, 0≤n j) (k : ℕ) :
    0 ≤ certificate n k := by
  exact add_nonneg (Finset.sum_nonneg fun j _ => div_nonneg (hn j) (by positivity))
    (div_nonneg (hn k) (by positivity))

theorem certificate_first_bill (n : ℕ → ℝ) (hn : ∀ j, 0≤n j)
    (h₁ : n 1≤n 0) (k : ℕ) : n 0/2+n 1/4 ≤ certificate n k := by
  rcases k with _|k
  · simp only [certificate, Finset.range_zero, Finset.sum_empty, pow_zero, div_one, zero_add]
    linarith [hn 0]
  rcases k with _|k
  · norm_num [certificate, Finset.sum_range_succ]
    linarith [hn 1]
  have hs : (∑ j ∈ Finset.range 2, n j/2^(j+1)) ≤
      ∑ j ∈ Finset.range (k+1+1), n j/2^(j+1) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
    intro j _ _
    exact div_nonneg (hn j) (by positivity)
  have ht := div_nonneg (hn (k+1+1)) (show (0 : ℝ) ≤ 2^(k+1+1) by positivity)
  have htwo : (∑ j ∈ Finset.range 2, n j/2^(j+1))=n 0/2+n 1/4 := by
    norm_num [Finset.sum_range_succ]
  rw [htwo] at hs
  dsimp [certificate]
  linarith

variable {d : ℕ} [NeZero d] {κ : Type*}

theorem changeCount_le_first_components (p : ZMod d → Bool) (s : ZMod d) :
    changeCount p s ≤ componentCount p (extendShifts {0} s) := by
  classical
  let e : Fin 2 → ZMod d := ![0,s]
  let : Unique (UpperBlocks 2) := {
    default := ⟨(0,1), by decide⟩
    uniq := by
      intro ij
      rcases ij with ⟨⟨i,j⟩,hij⟩
      change i.val<j.val at hij
      fin_cases i <;> fin_cases j <;> norm_num at hij
      rfl }
  have hc := component_defect_le_pair_sum p e (extendShifts {0} s) (by
    intro t
    simp [extendShifts, e, Fin.exists_fin_two, eq_comm])
  simp only [Finset.univ_unique, Finset.sum_singleton] at hc
  have hdef : (default : UpperBlocks 2)=⟨(0,1),by decide⟩ := Subsingleton.elim _ _
  rw [hdef] at hc
  simp only [e, Matrix.cons_val_one, Matrix.cons_val_zero, sub_zero] at hc
  have hecard : monochromaticCount p s = Fintype.card {c : ZMod d // p (c+s)=p c} :=
    Nat.card_eq_fintype_card
  have hm : monochromaticCount p s ≤ d := by
    rw [hecard]
    simpa only [ZMod.card] using
      Fintype.card_subtype_le (fun c : ZMod d => p (c+s)=p c)
  have he : changeCount p s = d-monochromaticCount p s := by
    rw [hecard]
    simpa only [changeCount, ZMod.card] using
      Fintype.card_subtype_compl (fun c : ZMod d => p (c+s)=p c)
  omega

/-- One event about all first steps controls every finite nested chain. -/
theorem component_certificate_floor (p : ZMod d → Bool) (η : ℝ) (hη : 0≤η)
    (hevent : ∀ s : ZMod d, s≠0 → (1/2-η)*d ≤ (changeCount p s : ℝ))
    (t : ℕ → ZMod d) (k : ℕ) :
    (5/8-η/4)*(d : ℝ)^2 ≤
      certificate (fun j => (d : ℝ)*componentCount p (translateSets t j)) k := by
  let n : ℕ → ℝ := fun j => (d : ℝ)*componentCount p (translateSets t j)
  have hn : ∀ j, 0≤n j := by intro j; positivity
  have hn0 : n 0=(d : ℝ)^2 := by simp [n, translateSets, componentCount_zero, pow_two]
  have hn1 : n 1≤n 0 := by
    rw [hn0]
    dsimp [n]
    have hh : (componentCount p (translateSets t 1) : ℝ)≤d := by
      exact_mod_cast componentCount_le_d p (translateSets t 1)
    nlinarith [Nat.cast_nonneg (α := ℝ) d]
  have hc : (1/2-η)*(d : ℝ) ≤ componentCount p (translateSets t 1) := by
    by_cases hs : t 0=0
    · simp only [translateSets, hs, extendShifts, Finset.image_singleton, zero_add,
        Finset.union_self, componentCount_zero]
      nlinarith [mul_nonneg hη (Nat.cast_nonneg (α := ℝ) d)]
    · exact (hevent _ hs).trans (by exact_mod_cast changeCount_le_first_components p (t 0))
  have hbill := certificate_first_bill n hn hn1 k
  rw [hn0] at hbill
  have hmul := mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg (α := ℝ) d)
  dsimp [n] at hbill
  nlinarith only [hbill,hmul]

/-- The floor for the full nonrepresentative-row starting ambient. -/
theorem isolation_certificate_floor (d : ℕ) (η : ℝ) (n : ℕ → ℝ)
    (hn : ∀ j, 0≤n j) (hn0 : n 0=(d : ℝ)-2) (hn1 : n 1≤n 0)
    (hfirst : (d : ℝ)/4-η*d-2≤n 1) (k : ℕ) :
    (9/16-η/4)*(d : ℝ)+1/2 ≤ 2+certificate n k := by
  have hh := certificate_first_bill n hn hn1 k
  rw [hn0] at hh
  linarith

noncomputable def directGain (p : ZMod d → κ) (Δ : Finset (ZMod d)) : ℝ :=
  ((d : ℝ)-componentCount p Δ)/((Δ.card : ℝ)*d)

/-- The exact deterministic event-to-envelope implication for every nonempty
shift set, including sets chosen after the whole partition is known. -/
theorem directGain_le_sqrt (p : ZMod d → κ) (a : ℝ) (ha : 0≤a)
    (hevent : ∀ s : ZMod d, s≠0 → (monochromaticCount p s : ℝ)≤a*d)
    (Δ : Finset (ZMod d)) (hΔ : Δ.Nonempty) : directGain p Δ ≤ Real.sqrt (a/2) := by
  classical
  let e : Fin (Fintype.card Δ) → ZMod d := fun i => ((Fintype.equivFin Δ).symm i).1
  have he : Function.Injective e := by
    intro i j hij
    exact (Fintype.equivFin Δ).symm.injective (Subtype.ext hij)
  have hcover : ∀ s, s∈Δ ↔ ∃ i, e i=s := by
    intro s
    constructor
    · intro hs
      exact ⟨(Fintype.equivFin Δ) ⟨s,hs⟩, by simp [e]⟩
    · rintro ⟨i,rfl⟩
      exact ((Fintype.equivFin Δ).symm i).2
  have hedge := component_defect_real_bound p e he Δ hcover (a*d) hevent
  simp only [Fintype.card_coe] at hedge
  have hd : (0 : ℝ)<d := by exact_mod_cast NeZero.pos d
  have hk : (0 : ℝ)<Δ.card := by exact_mod_cast hΔ.card_pos
  have hcomp : 0≤(componentCount p Δ : ℝ) := Nat.cast_nonneg _
  have hs : 0≤Real.sqrt (a/2) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt (a/2)^2=a/2 := Real.sq_sqrt (by positivity)
  have hnum : 0≤(d : ℝ)-componentCount p Δ := by
    exact sub_nonneg.mpr (by exact_mod_cast componentCount_le_d p Δ)
  have hg : 0≤directGain p Δ := div_nonneg hnum (le_of_lt (mul_pos hk hd))
  have hden : directGain p Δ * ((Δ.card : ℝ)*d)=(d : ℝ)-componentCount p Δ := by
    exact div_mul_cancel₀ _ (ne_of_gt (mul_pos hk hd))
  have hsmall : directGain p Δ ≤ (Δ.card : ℝ)*a/2 := by
    have hka : 0≤(Δ.card : ℝ)*a*d := by positivity
    apply (mul_le_mul_iff_of_pos_right (mul_pos hk hd)).mp
    rw [hden]
    nlinarith only [hedge,hka]
  have hlarge : directGain p Δ * (Δ.card : ℝ)≤1 := by
    nlinarith only [hden,hcomp,hd]
  by_contra hnot
  have hgt : Real.sqrt (a/2)<directGain p Δ := lt_of_not_ge hnot
  have hsq : a/2 < (directGain p Δ)^2 := by nlinarith only [hgt,hg,hs,hs2]
  have hprod := mul_le_mul_of_nonneg_left hlarge (show 0≤a/2 by positivity)
  have hprod' := mul_le_mul_of_nonneg_right hsmall hg
  nlinarith only [hsq,hprod,hprod',ha]

end SharedDecoders.CapacityMask
