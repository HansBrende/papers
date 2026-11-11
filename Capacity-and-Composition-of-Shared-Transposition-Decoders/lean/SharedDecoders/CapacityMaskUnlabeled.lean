import SharedDecoders.CapacityMaskProbabilityCorollaries
import Mathlib.Data.Fintype.Perm

/-! # Uniform nonempty unlabeled partitions and their exact labeling fibers -/

namespace SharedDecoders.CapacityMaskProbability

open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {I κ : Type*} [Fintype I] [Fintype κ] [DecidableEq I]

def SamePartition (p q : I → κ) : Prop := ∀ i j, p i=p j ↔ q i=q j

omit [Fintype I] [Fintype κ] [DecidableEq I] in
/-- An actual relabeling is reconstructed from two surjective label functions
with the same fibers. -/
theorem samePartition_permutation (p q : I → κ) (hp : Function.Surjective p)
    (hq : Function.Surjective q) (h : SamePartition p q) :
    ∃ σ : Equiv.Perm κ, ∀ i, σ (p i)=q i := by
  classical
  let r : κ → I := fun a => Classical.choose (hp a)
  have hr : ∀ a, p (r a)=a := fun a => Classical.choose_spec (hp a)
  let f : κ → κ := fun a => q (r a)
  have hf : ∀ i, f (p i)=q i := by
    intro i
    exact (h (r (p i)) i).mp (hr (p i))
  have hinj : Function.Injective f := by
    intro a b hab
    have hh := (h (r a) (r b)).mpr hab
    simpa only [hr] using hh
  have hsurj : Function.Surjective f := by
    intro b
    obtain ⟨i,rfl⟩ := hq b
    exact ⟨p i,hf i⟩
  exact ⟨Equiv.ofBijective f ⟨hinj,hsurj⟩,hf⟩

noncomputable def labelingEquiv (p : I → κ) (hp : Function.Surjective p) :
    Equiv.Perm κ ≃ {q : I → κ // Function.Surjective q ∧ SamePartition p q} := by
  classical
  let f : Equiv.Perm κ → {q : I → κ // Function.Surjective q ∧ SamePartition p q} :=
    fun σ => ⟨σ ∘ p,σ.surjective.comp hp,fun _ _ => σ.injective.eq_iff.symm⟩
  apply Equiv.ofBijective f
  constructor
  · intro σ τ hστ
    apply Equiv.ext
    intro a
    obtain ⟨i,rfl⟩ := hp a
    exact congrFun (congrArg Subtype.val hστ) i
  · intro q
    obtain ⟨σ,hσ⟩ := samePartition_permutation p q.val hp q.property.1 q.property.2
    exact ⟨σ,Subtype.ext (funext hσ)⟩

omit [Fintype I] [DecidableEq I] in
theorem labeling_count (p : I → κ) (hp : Function.Surjective p) :
    Nat.card {q : I → κ // Function.Surjective q ∧ SamePartition p q}=(Fintype.card κ).factorial := by
  rw [← Nat.card_congr (labelingEquiv p hp),Nat.card_eq_fintype_card,Fintype.card_perm]

abbrev SurjectiveMask (I κ : Type*) := {p : I → κ // Function.Surjective p}

def partitionSetoid : Setoid (SurjectiveMask I κ) where
  r p q := SamePartition p.val q.val
  iseqv := {
    refl := fun _ _ _ => Iff.rfl
    symm := fun h i j => (h i j).symm
    trans := fun h h' i j => (h i j).trans (h' i j) }

abbrev UnlabeledPartition := Quotient (partitionSetoid (I := I) (κ := κ))

noncomputable instance : Fintype (UnlabeledPartition (I := I) (κ := κ)) := Fintype.ofFinite _

noncomputable def unlabeled (p : SurjectiveMask I κ) : UnlabeledPartition (I := I) (κ := κ) :=
  Quotient.mk _ p

noncomputable def labelingFiberEquiv (p : SurjectiveMask I κ) :
    {q : SurjectiveMask I κ // unlabeled q=unlabeled p} ≃
      {q : I → κ // Function.Surjective q ∧ SamePartition p.val q} where
  toFun q := ⟨q.val.val,q.val.property,fun i j => (Quotient.exact q.property i j).symm⟩
  invFun q := ⟨⟨q.val,q.property.1⟩,Quotient.sound (fun i j => (q.property.2 i j).symm)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem unlabeled_fiber_count (q : UnlabeledPartition (I := I) (κ := κ)) :
    Fintype.card {p : SurjectiveMask I κ // unlabeled p=q}=(Fintype.card κ).factorial := by
  induction q using Quotient.inductionOn with
  | h p =>
    change Fintype.card {q : SurjectiveMask I κ // unlabeled q=unlabeled p}=_
    rw [← Nat.card_eq_fintype_card,Nat.card_congr (labelingFiberEquiv p)]
    exact labeling_count p.val p.property

/-- A constant-size fiber law preserves the uniform average. -/
theorem avg_constant_fibers {α β : Type*} [Fintype α] [Fintype β] [Nonempty β]
    (q : α → β) (m : ℕ) (hm : 0<m) (hcard : ∀ b, Fintype.card {a // q a=b}=m)
    (f : β → ℝ) : avg (fun a => f (q a))=avg f := by
  classical
  have htotal : Fintype.card α=Fintype.card β*m := by
    rw [← Fintype.card_congr (Equiv.sigmaFiberEquiv q),Fintype.card_sigma]
    simp only [hcard,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id]
  have hsum : (∑ a : α, f (q a))=∑ b : β, (m : ℝ)*f b := by
    have hh := Fintype.sum_equiv (Equiv.sigmaFiberEquiv q)
      (fun z => f z.1) (fun a => f (q a)) (fun z => congrArg f z.2.property.symm)
    rw [Fintype.sum_sigma] at hh
    simp only [Finset.sum_const,Finset.card_univ,hcard,nsmul_eq_mul] at hh
    exact hh.symm
  rw [avg_eq_sum_div_card,avg_eq_sum_div_card,hsum,htotal,Nat.cast_mul,← Finset.mul_sum]
  have hm0 : (m : ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hm
  have hb0 : (Fintype.card β : ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

theorem unlabeled_probability [Nonempty (SurjectiveMask I κ)]
    (P : UnlabeledPartition (I := I) (κ := κ) → Prop) :
    prob (fun p : SurjectiveMask I κ => P (unlabeled p))=prob P := by
  classical
  let _ : Nonempty (UnlabeledPartition (I := I) (κ := κ)) :=
    ⟨unlabeled (Classical.choice (inferInstance : Nonempty (SurjectiveMask I κ)))⟩
  exact avg_constant_fibers unlabeled (Fintype.card κ).factorial (Nat.factorial_pos _)
    (fun q => by simpa only [← Nat.card_eq_fintype_card] using unlabeled_fiber_count q)
    (fun q => if P q then 1 else 0)

omit [DecidableEq I] in
theorem surjectiveMask_nonempty [Nonempty κ] (hcard : Fintype.card κ≤Fintype.card I) :
    Nonempty (SurjectiveMask I κ) := by
  classical
  obtain ⟨e : κ ↪ I⟩ := Function.Embedding.nonempty_of_card_le hcard
  exact ⟨⟨Function.invFun e,Function.invFun_surjective e.injective⟩⟩

variable {d : ℕ} [NeZero d]

omit [Fintype κ] in
/-- Actual graph quotients depend only on the unlabeled partition. -/
theorem SamePartition.componentCount {p q : ZMod d → κ} (h : SamePartition p q)
    (Δ : Finset (ZMod d)) : componentCount p Δ=componentCount q Δ := by
  have hlink : Link p Δ=Link q Δ := by
    funext x y
    apply propext
    exact and_congr (h x y) Iff.rfl
  simp only [SharedDecoders.componentCount,LinkComponent,hlink]

omit [Fintype κ] in
theorem SamePartition.directGain {p q : ZMod d → κ} (h : SamePartition p q)
    (Δ : Finset (ZMod d)) : CapacityMask.directGain p Δ=CapacityMask.directGain q Δ := by
  rw [CapacityMask.directGain,CapacityMask.directGain,h.componentCount]

noncomputable def UnlabeledDirectGood (a : ℝ)
    (q : UnlabeledPartition (I := ZMod d) (κ := κ)) : Prop :=
  Quotient.lift (fun p : SurjectiveMask (ZMod d) κ => ∀ Δ : Finset (ZMod d), Δ.Nonempty →
    CapacityMask.directGain p.val Δ≤a) (by
      intro p q h
      apply propext
      simp only [h.directGain]) q



/-- Literal run starts depend only on equality and inequality of receiver labels. -/
theorem SamePartition.runCount {p q : ZMod d → Bool} (h : SamePartition p q)
    (s : ZMod d) (r : ℕ) : CapacityRuns.runCount p s r=CapacityRuns.runCount q s r := by
  classical
  have hs (x : ZMod d) : CapacityRuns.Start p s r x ↔ CapacityRuns.Start q s r x := by
    constructor
    · rintro ⟨hx,hh⟩
      refine ⟨(not_congr (h (x-s) x)).mp hx,?_⟩
      intro j hj
      exact (h (x+j•s) x).mp (hh j hj)
    · rintro ⟨hx,hh⟩
      refine ⟨(not_congr (h (x-s) x)).mpr hx,?_⟩
      intro j hj
      exact (h (x+j•s) x).mpr (hh j hj)
  exact Fintype.card_congr (Equiv.subtypeEquivRight hs)

theorem SamePartition.spectrum_eq {p q : ZMod d → Bool} (h : SamePartition p q) :
    runSpectrum p=runSpectrum q := by
  unfold runSpectrum
  rw [h.runCount 1 1,h.runCount 1 4,h.runCount 1 13]

omit [NeZero d] in
theorem complement_samePartition (p : ZMod d → Bool) : SamePartition p (fun c => !p c) := by
  intro i j
  exact Bool.not_inj_iff.symm

theorem spectrum_complement (p : ZMod d → Bool) : runSpectrum p=runSpectrum (fun c => !p c) :=
  (complement_samePartition p).spectrum_eq

noncomputable def UnlabeledSpectrumGood (ε : ℝ)
    (q : UnlabeledPartition (I := ZMod d) (κ := Bool)) : Prop :=
  Quotient.lift (fun p : SurjectiveMask (ZMod d) Bool => SpectrumGood ε p.val) (by
    intro p q h
    apply propext
    simp only [SpectrumGood,h.spectrum_eq]) q

set_option maxHeartbeats 800000 in
/-- Identifying complementary nonconstant binary labelings preserves the exact
random-spectrum fraction, with its explicit conditioning denominator. -/
theorem unlabeled_spectrum_probability (hd : 13<d) (ε : ℝ) (hε : 0≤ε) :
    prob (fun q : UnlabeledPartition (I := ZMod d) (κ := Bool) => ¬UnlabeledSpectrumGood ε q)≤
      Real.exp (-128*ε^2*d/529)/(1-2/(2 : ℝ)^d) := by
  let _ : Nonempty (SurjectiveMask (ZMod d) Bool) :=
    surjectiveMask_nonempty (by simp only [Fintype.card_bool,ZMod.card]; omega)
  let _ : Nonempty {p : ZMod d → Bool // AllLabels p} :=
    surjectiveMask_nonempty (by simp only [Fintype.card_bool,ZMod.card]; omega)
  rw [← unlabeled_probability]
  have hsub := prob_subtype_eq_condProb (fun p : ZMod d → Bool => ¬SpectrumGood ε p) AllLabels
  have heq : prob (fun p : SurjectiveMask (ZMod d) Bool => ¬UnlabeledSpectrumGood ε (unlabeled p))=
      condProb (fun p : ZMod d → Bool => ¬SpectrumGood ε p) AllLabels := by
    convert hsub using 1
    rw [prob_eq_card,prob_eq_card]
    simp only [← Nat.card_eq_fintype_card]
    rfl
  have hh := heq.trans_le (spectrum_conditioned_probability hd ε hε)
  convert hh using 1
  exact congrArg (fun instF : Fintype (SurjectiveMask (ZMod d) Bool) =>
    @prob _ instF (fun p => ¬UnlabeledSpectrumGood ε (unlabeled p))) (Subsingleton.elim _ _)

/-- Conditioning on all labels is a nonempty event whenever the number of
labels does not exceed the actual number of positions. -/
theorem allLabels_positive [Nonempty κ] (hM : Fintype.card κ≤d) :
    0<prob (AllLabels (I := ZMod d) (κ := κ)) := by
  classical
  let _ : Nonempty {p : ZMod d → κ // AllLabels p} :=
    surjectiveMask_nonempty (by simpa only [ZMod.card] using hM)
  rw [prob_eq_card]
  positivity

theorem unlabeled_direct_conditional_eq [Nonempty κ] (hM : Fintype.card κ≤d) (a : ℝ) :
    prob (fun q : UnlabeledPartition (I := ZMod d) (κ := κ) => ¬UnlabeledDirectGood a q)=
      condProb (fun p : ZMod d → κ => ¬∀ Δ : Finset (ZMod d), Δ.Nonempty →
        CapacityMask.directGain p Δ≤a) AllLabels := by
  let _ : Nonempty (SurjectiveMask (ZMod d) κ) :=
    surjectiveMask_nonempty (by simpa only [ZMod.card] using hM)
  let _ : Nonempty {p : ZMod d → κ // AllLabels p} :=
    surjectiveMask_nonempty (by simpa only [ZMod.card] using hM)
  rw [← unlabeled_probability]
  have hsub := prob_subtype_eq_condProb (fun p : ZMod d → κ => ¬∀ Δ : Finset (ZMod d),
    Δ.Nonempty → CapacityMask.directGain p Δ≤a) (AllLabels (I := ZMod d))
  convert hsub using 1
  rw [prob_eq_card,prob_eq_card]
  simp only [← Nat.card_eq_fintype_card]
  rfl

/-- The exact positive conditioning denominator is valid even when the
empty-label union estimate is at least one. -/
theorem unlabeled_direct_exact_probability [Nonempty κ] (hM : Fintype.card κ≤d)
    (η : ℝ) (hη : 0≤η) :
    prob (fun q : UnlabeledPartition (I := ZMod d) (κ := κ) =>
      ¬UnlabeledDirectGood (Real.sqrt ((1/(Fintype.card κ : ℝ)+η)/2)) q) ≤
      (((d : ℝ)-1)*Real.exp (-η^2*d/2))/prob (AllLabels (I := ZMod d) (κ := κ)) := by
  rw [unlabeled_direct_conditional_eq hM]
  exact condProb_le _ AllLabels (direct_floor_probability η hη) le_rfl (allLabels_positive hM)

/-- The literal uniform unlabeled-partition law obeys the same conditional
bound, with the actual missing-label estimate and its explicit positivity
condition. -/
theorem unlabeled_direct_probability [Nonempty κ] (hM : Fintype.card κ≤d)
    (η : ℝ) (hη : 0≤η)
    (hq : (Fintype.card κ : ℝ)*Real.exp (-(d : ℝ)/(Fintype.card κ : ℝ))<1) :
    prob (fun q : UnlabeledPartition (I := ZMod d) (κ := κ) =>
      ¬UnlabeledDirectGood (Real.sqrt ((1/(Fintype.card κ : ℝ)+η)/2)) q) ≤
      (((d : ℝ)-1)*Real.exp (-η^2*d/2))/
        (1-(Fintype.card κ : ℝ)*Real.exp (-(d : ℝ)/(Fintype.card κ : ℝ))) := by
  rw [unlabeled_direct_conditional_eq hM]
  have hh := condProb_allLabels
    (fun p : ZMod d → κ => ¬∀ Δ : Finset (ZMod d), Δ.Nonempty → CapacityMask.directGain p Δ≤
      Real.sqrt ((1/(Fintype.card κ : ℝ)+η)/2)) (direct_floor_probability η hη)
    (by simpa only [ZMod.card] using hq)
  simpa only [ZMod.card] using hh

end SharedDecoders.CapacityMaskProbability
