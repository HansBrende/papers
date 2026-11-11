import SharedDecoders.CapacityMaskComparisonProbability

/-! # Conditioning the finite mask law and excluding empty labels -/

namespace SharedDecoders.CapacityMaskProbability

open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {α I κ : Type*} [Fintype α] [Fintype I] [Fintype κ]

/-- Conditional probabilities are literal ratios of normalized finite counts. -/
noncomputable def condProb (P B : α → Prop) : ℝ := prob (fun x => P x ∧ B x)/prob B

theorem prob_compl [Nonempty α] (P : α → Prop) : prob (fun x => ¬P x)=1-prob P := by
  classical
  calc
    prob (fun x => ¬P x) = avg (fun x => 1-(if P x then (1 : ℝ) else 0)) := by
      unfold prob
      congr 1
      funext x
      by_cases hx : P x <;> simp [hx]
    _ = 1-prob P := by rw [avg_sub,avg_const]; rfl

theorem prob_or_le (P Q : α → Prop) : prob (fun x => P x ∨ Q x)≤prob P+prob Q := by
  classical
  simp only [prob,← avg_add]
  apply avg_mono
  intro x
  by_cases hp : P x <;> by_cases hq : Q x <;> simp [hp,hq]

theorem condProb_le (P B : α → Prop) {a q : ℝ} (hP : prob P≤a)
    (hB : q≤prob B) (hq : 0<q) : condProb P B≤a/q := by
  classical
  have ha : 0≤a := (prob_nonneg P).trans hP
  exact div_le_div₀ ha ((prob_mono (fun _ h => h.1)).trans hP) hq hB

/-- Uniform sampling inside a nonempty event agrees with the literal conditional
law, so conditioning introduces no measure-theoretic hypothesis. -/
theorem prob_subtype_eq_condProb (P B : α → Prop) [Nonempty {x // B x}] :
    prob (fun x : {x // B x} => P x.val)=condProb P B := by
  classical
  let e : {x : {x // B x} // P x.val} ≃ {x // P x ∧ B x} := {
    toFun := fun x => ⟨x.val.val,x.property,x.val.property⟩
    invFun := fun x => ⟨⟨x.val,x.property.2⟩,x.property.1⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hB : (Fintype.card {x // B x} : ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  have hA : (Fintype.card α : ℝ)≠0 := by
    have : Nonempty α := ⟨(Classical.choice (inferInstance : Nonempty {x // B x})).val⟩
    exact_mod_cast Fintype.card_ne_zero
  rw [condProb,prob_eq_card,prob_eq_card,prob_eq_card,Fintype.card_congr e]
  field_simp
  simp only [← Nat.card_eq_fintype_card]

/-- Functions avoiding a fixed label are exactly functions into its complement. -/
def avoidingLabelEquiv [DecidableEq I] (a : κ) :
    {p : I → κ // ∀ i, p i≠a} ≃ (I → {b : κ // b≠a}) where
  toFun p i := ⟨p.val i,p.property i⟩
  invFun p := ⟨fun i => (p i).val,fun i => (p i).property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem absent_label_probability [DecidableEq I] [Nonempty κ] (a : κ) :
    prob (fun p : I → κ => ∀ i, p i≠a)=
      (1-1/(Fintype.card κ : ℝ))^(Fintype.card I) := by
  classical
  have hc : Fintype.card {b : κ // b≠a}=Fintype.card κ-1 := by
    simpa only [Fintype.card_subtype_eq] using Fintype.card_subtype_compl (fun b : κ => b=a)
  have hM : 1≤Fintype.card κ := Fintype.card_pos
  have hc' : Nat.card {p : I → κ // ∀ i, p i≠a} =
      (Fintype.card κ-1)^(Fintype.card I) := by
    rw [Nat.card_congr (avoidingLabelEquiv a),Nat.card_eq_fintype_card,Fintype.card_fun,hc]
  have hp := prob_eq_card (fun p : I → κ => ∀ i, p i≠a)
  simp only [← Nat.card_eq_fintype_card] at hp
  rw [hp,hc']
  simp only [Nat.card_eq_fintype_card,Fintype.card_fun]
  rw [Nat.cast_pow,Nat.cast_pow,Nat.cast_sub hM,Nat.cast_one,← div_pow]
  congr 1
  have hm : (Fintype.card κ : ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

theorem absent_label_exponential [DecidableEq I] [Nonempty κ] (a : κ) :
    prob (fun p : I → κ => ∀ i, p i≠a)≤
      Real.exp (-(Fintype.card I : ℝ)/(Fintype.card κ : ℝ)) := by
  classical
  rw [absent_label_probability]
  have hM : (1 : ℝ)≤Fintype.card κ := by exact_mod_cast Fintype.card_pos
  have h0 : 0≤1-1/(Fintype.card κ : ℝ) := by
    have hh : 1/(Fintype.card κ : ℝ)≤1 := (div_le_one (by positivity)).mpr hM
    linarith
  have hh : 1-1/(Fintype.card κ : ℝ)≤Real.exp (-1/(Fintype.card κ : ℝ)) := by
    have he := Real.add_one_le_exp (-1/(Fintype.card κ : ℝ))
    convert he using 1; ring
  calc
    _ ≤ (Real.exp (-1/(Fintype.card κ : ℝ)))^(Fintype.card I) := pow_le_pow_left₀ h0 hh _
    _ = Real.exp (-(Fintype.card I : ℝ)/(Fintype.card κ : ℝ)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

def AllLabels (p : I → κ) : Prop := Function.Surjective p

theorem missing_label_probability [DecidableEq I] [Nonempty κ] :
    prob (fun p : I → κ => ¬AllLabels p)≤
      (Fintype.card κ : ℝ)*(1-1/(Fintype.card κ : ℝ))^(Fintype.card I) := by
  classical
  calc
    _ ≤ prob (fun p : I → κ => ∃ a : κ, ∀ i, p i≠a) := by
      apply prob_mono
      intro p hp
      simpa only [AllLabels,Function.Surjective,not_forall,not_exists] using hp
    _ ≤ ∑ a : κ, prob (fun p : I → κ => ∀ i, p i≠a) := prob_exists_le_sum _
    _ = _ := by simp only [absent_label_probability,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]

theorem missing_label_exponential [DecidableEq I] [Nonempty κ] :
    prob (fun p : I → κ => ¬AllLabels p)≤
      (Fintype.card κ : ℝ)*Real.exp (-(Fintype.card I : ℝ)/(Fintype.card κ : ℝ)) := by
  classical
  calc
    _ ≤ prob (fun p : I → κ => ∃ a : κ, ∀ i, p i≠a) := by
      apply prob_mono
      intro p hp
      simpa only [AllLabels,Function.Surjective,not_forall,not_exists] using hp
    _ ≤ ∑ a : κ, prob (fun p : I → κ => ∀ i, p i≠a) := prob_exists_le_sum _
    _ ≤ ∑ _a : κ, Real.exp (-(Fintype.card I : ℝ)/(Fintype.card κ : ℝ)) :=
      Finset.sum_le_sum (fun a _ => absent_label_exponential a)
    _ = _ := by simp

theorem condProb_allLabels [DecidableEq I] [Nonempty κ] (P : (I → κ) → Prop)
    {a : ℝ} (hP : prob P≤a)
    (hq : (Fintype.card κ : ℝ)*Real.exp (-(Fintype.card I : ℝ)/(Fintype.card κ : ℝ))<1) :
    condProb P AllLabels≤
      a/(1-(Fintype.card κ : ℝ)*Real.exp (-(Fintype.card I : ℝ)/(Fintype.card κ : ℝ))) := by
  classical
  apply condProb_le P AllLabels hP _ (by linarith)
  have hh := missing_label_exponential (I := I) (κ := κ)
  rw [prob_compl] at hh
  linarith

/-- The exact binary conditioning denominator, including the constant masks. -/
theorem binary_allLabels_probability {d : ℕ} [NeZero d] :
    prob (AllLabels (I := ZMod d) (κ := Bool))=1-2/(2 : ℝ)^d := by
  classical
  have he : (fun p : ZMod d → Bool => ¬AllLabels p)=
      (fun p => (∀ i, p i≠false) ∨ (∀ i, p i≠true)) := by
    funext p
    simp only [AllLabels,Function.Surjective,not_forall,not_exists,Bool.exists_bool]
  have hd : ∀ p : ZMod d → Bool, ¬((∀ i, p i≠false) ∧ (∀ i, p i≠true)) := by
    intro p ⟨hf,ht⟩
    cases h : p 0
    · exact hf 0 h
    · exact ht 0 h
  have hh := prob_or_of_disjoint (fun p : ZMod d → Bool => ∀ i, p i≠false)
    (fun p : ZMod d → Bool => ∀ i, p i≠true) hd
  rw [← he,prob_compl,absent_label_probability,absent_label_probability] at hh
  simp only [Fintype.card_bool,Nat.cast_ofNat,ZMod.card] at hh
  norm_num only [show (1 : ℝ)-1/2=1/2 by norm_num] at hh
  rw [div_pow,one_pow] at hh
  linear_combination -hh

end SharedDecoders.CapacityMaskProbability
