import SharedDecoders.CapacityMaskLocalWindows
import SharedDecoders.CapacityMaskMethods

/-! # Actual comparison statistics and simultaneous mask events

The sample is the full uniform function space. Means, coordinate-change
constants and the finite union over every nonzero cyclic shift are derived
from the actual equality/change predicates.
-/

namespace SharedDecoders.CapacityMaskProbability

open CapacityRuns CapacityMask
open scoped BigOperators

variable {κ : Type*} [Fintype κ] [Nonempty κ]

noncomputable def equalIndicator (x : Fin 2 → κ) : ℝ := by
  classical
  exact if x 0=x 1 then 1 else 0

def equalPairEquiv : {x : Fin 2 → κ // x 0=x 1} ≃ κ where
  toFun x := x.val 0
  invFun a := ⟨fun _ => a,rfl⟩
  left_inv x := by
    apply Subtype.ext
    funext j
    fin_cases j
    · rfl
    · exact x.property
  right_inv _ := rfl

theorem avg_equalIndicator : avg (equalIndicator (κ := κ)) = 1/(Fintype.card κ : ℝ) := by
  classical
  change prob (fun x : Fin 2 → κ => x 0=x 1) = _
  rw [prob_eq_card,Fintype.card_congr (equalPairEquiv (κ := κ))]
  simp only [Fintype.card_fun,Fintype.card_fin]
  have hc : (Fintype.card κ : ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  push_cast
  field_simp

def comparisonOffset {d : ℕ} (s : ZMod d) : Fin 2 → ZMod d := ![0,s]

theorem comparisonOffset_injective {d : ℕ} (s : ZMod d) (hs : s≠0) :
    Function.Injective (comparisonOffset s) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [comparisonOffset]

variable {d : ℕ} [NeZero d]

omit [Fintype κ] [Nonempty κ] in
theorem monochromaticCount_eq_windowSum (p : ZMod d → κ) (s : ZMod d) :
    (monochromaticCount p s : ℝ) = windowSum (comparisonOffset s) equalIndicator p := by
  classical
  simp only [monochromaticCount,Nat.card_eq_fintype_card,Fintype.card_subtype,
    Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,
    windowSum,equalIndicator,comparisonOffset,Matrix.cons_val_zero,Matrix.cons_val_one,
    add_zero]
  apply Finset.sum_congr rfl
  intro x _
  simp only [eq_comm]

theorem monochromaticCount_mean (s : ZMod d) (hs : s≠0) :
    avg (fun p : ZMod d → κ => (monochromaticCount p s : ℝ)) =
      (d : ℝ)/(Fintype.card κ : ℝ) := by
  have he : (fun p : ZMod d → κ => (monochromaticCount p s : ℝ)) =
      windowSum (comparisonOffset s) equalIndicator :=
    funext fun p => monochromaticCount_eq_windowSum p s
  rw [he,windowSum_mean _ (comparisonOffset_injective s hs),avg_equalIndicator,ZMod.card]
  ring

omit [Fintype κ] [Nonempty κ] in
theorem monochromaticCount_boundedChanges (s : ZMod d) :
    BoundedChanges (fun p : ZMod d → κ => (monochromaticCount p s : ℝ)) (fun _ => 2) := by
  have he : (fun p : ZMod d → κ => (monochromaticCount p s : ℝ)) =
      windowSum (comparisonOffset s) equalIndicator :=
    funext fun p => monochromaticCount_eq_windowSum p s
  rw [he]
  apply windowSum_boundedChanges
  intro x
  dsimp [equalIndicator]
  split <;> norm_num

theorem changeCount_add_monochromaticCount (p : ZMod d → Bool) (s : ZMod d) :
    changeCount p s+monochromaticCount p s=d := by
  classical
  have h := Fintype.card_subtype_compl (fun c : ZMod d => p (c+s)=p c)
  have hm : monochromaticCount p s≤d := by
    simpa only [monochromaticCount,Nat.card_eq_fintype_card,ZMod.card] using
      Fintype.card_subtype_le (fun c : ZMod d => p (c+s)=p c)
  have he : changeCount p s=d-monochromaticCount p s := by
    simpa only [changeCount,monochromaticCount,Nat.card_eq_fintype_card,ZMod.card] using h
  omega

theorem changeCount_mean (s : ZMod d) (hs : s≠0) :
    avg (fun p : ZMod d → Bool => (changeCount p s : ℝ))=(d : ℝ)/2 := by
  have he : (fun p : ZMod d → Bool => (changeCount p s : ℝ)) =
      (fun p => (d : ℝ)-(monochromaticCount p s : ℝ)) := by
    funext p
    have hh := changeCount_add_monochromaticCount p s
    have hh' : (changeCount p s : ℝ)+(monochromaticCount p s : ℝ)=d := by exact_mod_cast hh
    linarith
  rw [he,avg_sub,avg_const,monochromaticCount_mean s hs]
  simp only [Fintype.card_bool,Nat.cast_ofNat]
  ring

theorem changeCount_boundedChanges (s : ZMod d) :
    BoundedChanges (fun p : ZMod d → Bool => (changeCount p s : ℝ)) (fun _ => 2) := by
  intro i p q hpq
  have hh := monochromaticCount_boundedChanges (κ := Bool) s i p q hpq
  have hp := changeCount_add_monochromaticCount p s
  have hq := changeCount_add_monochromaticCount q s
  have hp' : (changeCount p s : ℝ)+(monochromaticCount p s : ℝ)=d := by exact_mod_cast hp
  have hq' : (changeCount q s : ℝ)+(monochromaticCount q s : ℝ)=d := by exact_mod_cast hq
  apply abs_le.mpr
  have habs := abs_le.mp hh
  constructor <;> linarith

theorem monochromaticCount_upper_tail (s : ZMod d) (hs : s≠0) (η : ℝ) (hη : 0≤η) :
    prob (fun p : ZMod d → κ => (d : ℝ)*(1/(Fintype.card κ : ℝ)+η) ≤
      (monochromaticCount p s : ℝ)) ≤ Real.exp (-η^2*d/2) := by
  have hh := boundedDifferences_upper (fun p : ZMod d → κ => (monochromaticCount p s : ℝ))
    (fun _ => 2) (fun _ => by norm_num) (monochromaticCount_boundedChanges s)
    (η*d) (by positivity)
  rw [monochromaticCount_mean s hs] at hh
  simp only [Finset.sum_const,Finset.card_univ,ZMod.card] at hh
  have he : (d : ℝ)/(Fintype.card κ : ℝ)+η*d = d*(1/(Fintype.card κ : ℝ)+η) := by ring
  rw [he] at hh
  have hd : (d : ℝ)≠0 := by exact_mod_cast NeZero.ne d
  convert hh using 1
  congr 1
  field_simp
  ring

theorem changeCount_lower_tail (s : ZMod d) (hs : s≠0) (η : ℝ) (hη : 0≤η) :
    prob (fun p : ZMod d → Bool => (changeCount p s : ℝ)≤(1/2-η)*d) ≤
      Real.exp (-η^2*d/2) := by
  have hh := boundedDifferences_lower (fun p : ZMod d → Bool => (changeCount p s : ℝ))
    (fun _ => 2) (fun _ => by norm_num) (changeCount_boundedChanges s) (η*d) (by positivity)
  rw [changeCount_mean s hs] at hh
  simp only [Finset.sum_const,Finset.card_univ,ZMod.card] at hh
  have he : (d : ℝ)/2-η*d=(1/2-η)*d := by ring
  rw [he] at hh
  have hd : (d : ℝ)≠0 := by exact_mod_cast NeZero.ne d
  convert hh using 1
  congr 1
  field_simp
  ring


omit [Nonempty κ] in
/-- The union is over the actual nonzero cyclic shifts. -/
theorem nonzero_shift_union (P : ZMod d → (ZMod d → κ) → Prop) (a : ℝ)
    (ha : ∀ s : ZMod d, s≠0 → prob (fun p => ¬P s p)≤a) :
    prob (fun p => ¬∀ s : ZMod d, s≠0 → P s p) ≤ ((d : ℝ)-1)*a := by
  classical
  let J := {s : ZMod d // s≠0}
  have hcard : Fintype.card J=d-1 := by
    simpa only [J,ZMod.card,Fintype.card_subtype_eq] using
      Fintype.card_subtype_compl (fun s : ZMod d => s=0)
  have h0 : 1≤d := NeZero.pos d
  calc
    prob (fun p => ¬∀ s : ZMod d, s≠0 → P s p) ≤
        prob (fun p => ∃ s : J, ¬P s.val p) := by
      apply prob_mono
      intro p hp
      push Not at hp
      obtain ⟨s,hs,hp⟩ := hp
      exact ⟨⟨s,hs⟩,hp⟩
    _ ≤ ∑ s : J, prob (fun p => ¬P s.val p) := prob_exists_le_sum _
    _ ≤ ∑ _s : J, a := Finset.sum_le_sum (fun s _ => ha s.val s.property)
    _ = ((d : ℝ)-1)*a := by simp [hcard,Nat.cast_sub h0]

def ChangeGood (η : ℝ) (p : ZMod d → Bool) : Prop :=
  ∀ s : ZMod d, s≠0 → (1/2-η)*d≤(changeCount p s : ℝ)

def EqualityGood (η : ℝ) (p : ZMod d → κ) : Prop :=
  ∀ s : ZMod d, s≠0 → (monochromaticCount p s : ℝ)≤(1/(Fintype.card κ : ℝ)+η)*d

theorem change_bad_probability (η : ℝ) (hη : 0≤η) :
    prob (fun p : ZMod d → Bool => ¬ChangeGood η p) ≤
      ((d : ℝ)-1)*Real.exp (-η^2*d/2) := by
  apply nonzero_shift_union
  intro s hs
  exact (prob_mono (fun _ hp => le_of_lt (lt_of_not_ge hp))).trans
    (changeCount_lower_tail s hs η hη)

theorem equality_bad_probability (η : ℝ) (hη : 0≤η) :
    prob (fun p : ZMod d → κ => ¬EqualityGood η p) ≤
      ((d : ℝ)-1)*Real.exp (-η^2*d/2) := by
  apply nonzero_shift_union
  intro s hs
  have hh := monochromaticCount_upper_tail (κ := κ) s hs η hη
  rw [mul_comm (d : ℝ)] at hh
  exact (prob_mono (fun _ hp => le_of_lt (lt_of_not_ge hp))).trans hh

theorem certificate_const_mul (a : ℝ) (n : ℕ → ℝ) (k : ℕ) :
    certificate (fun j => a*n j) k = a*certificate n k := by
  simp only [certificate,mul_add,Finset.mul_sum,mul_div_assoc]

theorem ChangeGood.certificate_floor (η : ℝ) (hη : 0≤η) (p : ZMod d → Bool)
    (hp : ChangeGood η p) (b : ℕ) (t : ℕ → ZMod d) (k : ℕ) :
    (5/8-η/4)*(b : ℝ)*d^2 ≤
      certificate (fun j => (b : ℝ)*d*componentCount p (translateSets t j)) k := by
  have hh := component_certificate_floor p η hη hp t k
  have hm := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg (α := ℝ) b)
  have he : (fun j => (b : ℝ)*d*componentCount p (translateSets t j)) =
      (fun j => (b : ℝ)*((d : ℝ)*componentCount p (translateSets t j))) := by
    funext j
    ring
  rw [he,certificate_const_mul]
  nlinarith only [hm]

/-- The sampled event controls all widths and all finite chains, including
chains selected from the full mask. -/
theorem component_floor_probability (η : ℝ) (hη : 0≤η) :
    prob (fun p : ZMod d → Bool => ¬∀ (b : ℕ) (t : ℕ → ZMod d) (k : ℕ),
      (5/8-η/4)*(b : ℝ)*d^2 ≤
        certificate (fun j => (b : ℝ)*d*componentCount p (translateSets t j)) k) ≤
      ((d : ℝ)-1)*Real.exp (-η^2*d/2) := by
  apply (prob_mono ?_).trans (change_bad_probability η hη)
  intro p hp hgood
  exact hp (hgood.certificate_floor η hη p)

theorem EqualityGood.direct_gain (η : ℝ) (hη : 0≤η) (p : ZMod d → κ)
    (hp : EqualityGood η p) (Δ : Finset (ZMod d)) (hΔ : Δ.Nonempty) :
    directGain p Δ ≤ Real.sqrt ((1/(Fintype.card κ : ℝ)+η)/2) := by
  exact directGain_le_sqrt p _ (by positivity) hp Δ hΔ

/-- One finite probability statement controls every nonempty shift set. -/
theorem direct_floor_probability (η : ℝ) (hη : 0≤η) :
    prob (fun p : ZMod d → κ => ¬∀ Δ : Finset (ZMod d), Δ.Nonempty →
      directGain p Δ ≤ Real.sqrt ((1/(Fintype.card κ : ℝ)+η)/2)) ≤
      ((d : ℝ)-1)*Real.exp (-η^2*d/2) := by
  apply (prob_mono ?_).trans (equality_bad_probability (κ := κ) η hη)
  intro p hp hgood
  exact hp (hgood.direct_gain η hη p)

theorem EqualityGood.direct_gain_inverse_sqrt (η : ℝ) (hη : 0≤η)
    (hMη : (Fintype.card κ : ℝ)*η≤1) (p : ZMod d → κ) (hp : EqualityGood η p)
    (Δ : Finset (ZMod d)) (hΔ : Δ.Nonempty) :
    directGain p Δ≤1/Real.sqrt (Fintype.card κ : ℝ) := by
  have hM : (0 : ℝ)<Fintype.card κ := by exact_mod_cast Fintype.card_pos
  have ha : (1/(Fintype.card κ : ℝ)+η)/2≤1/(Fintype.card κ : ℝ) := by
    have hh := (le_div_iff₀ hM).mpr (by simpa only [mul_comm] using hMη)
    linarith
  calc
    directGain p Δ ≤ Real.sqrt ((1/(Fintype.card κ : ℝ)+η)/2) :=
      hp.direct_gain η hη p Δ hΔ
    _ ≤ Real.sqrt (1/(Fintype.card κ : ℝ)) := Real.sqrt_le_sqrt ha
    _ = 1/Real.sqrt (Fintype.card κ : ℝ) := by rw [Real.sqrt_div (by norm_num),Real.sqrt_one]

end SharedDecoders.CapacityMaskProbability
