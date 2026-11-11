import SharedDecoders.CapacityMaskComparisonProbability
import SharedDecoders.CapacityClosureIteration

/-! # Actual isolation events and arbitrary representative deletion

The mean is computed from the literal first-graph isolation predicate,
including the order-two exception. The final event controls every pair of
removed rows and every finite chain.
-/

namespace SharedDecoders.CapacityMaskProbability

open CapacityRuns CapacityMask CapacityClosure
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
theorem first_link_iff {κ : Type*} (p : ZMod d → κ) (s x y : ZMod d) :
    Link p (extendShifts {0} s) x y ↔ p x=p y ∧ (y=x ∨ y=x+s ∨ y=x-s) := by
  classical
  have hmem (u : ZMod d) : u∈extendShifts {0} s ↔ u=0 ∨ u=s := by
    simp [extendShifts]
  constructor
  · rintro ⟨hp,u,hu,v,hv,he⟩
    refine ⟨hp,?_⟩
    rcases (hmem u).mp hu with rfl|rfl <;> rcases (hmem v).mp hv with rfl|rfl
    · exact Or.inl (by simpa using he.symm)
    · exact Or.inr (Or.inr (by linear_combination -he))
    · exact Or.inr (Or.inl (by linear_combination -he))
    · exact Or.inl (add_right_cancel he.symm)
  · rintro ⟨hp,rfl|rfl|rfl⟩
    · exact ⟨hp,0,(hmem 0).mpr (Or.inl rfl),0,(hmem 0).mpr (Or.inl rfl),rfl⟩
    · exact ⟨hp,s,(hmem s).mpr (Or.inr rfl),0,(hmem 0).mpr (Or.inl rfl),by simp⟩
    · exact ⟨hp,0,(hmem 0).mpr (Or.inl rfl),s,(hmem s).mpr (Or.inr rfl),by simp⟩

omit [NeZero d] in
theorem isIsolated_first_iff {κ : Type*} (p : ZMod d → κ) (s : ZMod d)
    (hs : s≠0) (x : ZMod d) :
    IsIsolated p (extendShifts {0} s) x ↔ p (x-s)≠p x ∧ p (x+s)≠p x := by
  constructor
  · intro h
    constructor
    · intro he
      have hh := h (x-s) ((first_link_iff p s x (x-s)).mpr ⟨he.symm,Or.inr (Or.inr rfl)⟩)
      exact hs (by linear_combination -hh)
    · intro he
      have hh := h (x+s) ((first_link_iff p s x (x+s)).mpr ⟨he.symm,Or.inr (Or.inl rfl)⟩)
      exact hs (by linear_combination hh)
  · rintro ⟨hm,hp⟩ y hxy
    obtain ⟨hlabel,hy|hy|hy⟩ := (first_link_iff p s x y).mp hxy
    · exact hy
    · subst y; exact (hp hlabel.symm).elim
    · subst y; exact (hm hlabel.symm).elim

omit [NeZero d] in
theorem isIsolated_zero {κ : Type*} (p : ZMod d → κ) (x : ZMod d) :
    IsIsolated p {0} x := by
  intro y hxy
  have he : x=y := by simpa [Link,SwapRigidity.Link] using hxy.2
  exact he.symm

def isolationOffset (s : ZMod d) : Fin 3 → ZMod d := ![-s,0,s]

def IsolatedWindow (x : Fin 3 → Bool) : Prop := x 0≠x 1 ∧ x 2≠x 1

noncomputable def isolationIndicator (x : Fin 3 → Bool) : ℝ :=
  if IsolatedWindow x then 1 else 0

def isolatedWindowEquiv : {x : Fin 3 → Bool // IsolatedWindow x} ≃ Bool where
  toFun x := x.val 1
  invFun a := ⟨![!a,a,!a],by cases a <;> simp [IsolatedWindow]⟩
  left_inv x := by
    apply Subtype.ext
    funext j
    fin_cases j
    · exact (Bool.eq_not_iff.mpr x.property.1).symm
    · rfl
    · exact (Bool.eq_not_iff.mpr x.property.2).symm
  right_inv _ := rfl

theorem avg_isolationIndicator : avg isolationIndicator=1/4 := by
  change prob IsolatedWindow=1/4
  rw [prob_eq_card,Fintype.card_congr isolatedWindowEquiv]
  norm_num [Fintype.card_fun]

omit [NeZero d] in
theorem isolationOffset_injective (s : ZMod d) (hs : s≠0) (horder : s+s≠0) :
    Function.Injective (isolationOffset s) := by
  have hn : -s≠s := by intro h; apply horder; linear_combination -h
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals dsimp [isolationOffset] at hij
  · rfl
  · exact (hs (neg_eq_zero.mp hij)).elim
  · exact (hn hij).elim
  · exact (hs (neg_eq_zero.mp hij.symm)).elim
  · rfl
  · exact (hs hij.symm).elim
  · exact (hn hij.symm).elim
  · exact (hs hij).elim
  · rfl

theorem isolatedCount_eq_windowSum (p : ZMod d → Bool) (s : ZMod d) (hs : s≠0) :
    (isolatedCount p (extendShifts {0} s) : ℝ)=windowSum (isolationOffset s) isolationIndicator p := by
  classical
  simp only [isolatedCount,Fintype.card_subtype,Finset.card_filter,Nat.cast_sum,
    Nat.cast_ite,Nat.cast_one,Nat.cast_zero,windowSum,isolationIndicator,IsolatedWindow,
    isolationOffset,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    add_zero,← sub_eq_add_neg,isIsolated_first_iff p s hs]
  rfl

theorem isolatedCount_order_two (p : ZMod d → Bool) (s : ZMod d) (hs : s≠0)
    (horder : s+s=0) : isolatedCount p (extendShifts {0} s)=changeCount p s := by
  have hm : -s=s := by linear_combination -horder
  simp only [isolatedCount,changeCount,isIsolated_first_iff p s hs,sub_eq_add_neg,hm,and_self]

theorem isolatedCount_mean (s : ZMod d) (hs : s≠0) :
    (d : ℝ)/4≤avg (fun p : ZMod d → Bool => (isolatedCount p (extendShifts {0} s) : ℝ)) := by
  by_cases horder : s+s=0
  · have he : (fun p : ZMod d → Bool => (isolatedCount p (extendShifts {0} s) : ℝ))=
        (fun p => (changeCount p s : ℝ)) := by
      funext p
      rw [isolatedCount_order_two p s hs horder]
    rw [he,changeCount_mean s hs]
    linarith [Nat.cast_nonneg (α := ℝ) d]
  · have he : (fun p : ZMod d → Bool => (isolatedCount p (extendShifts {0} s) : ℝ))=
        windowSum (isolationOffset s) isolationIndicator :=
      funext fun p => isolatedCount_eq_windowSum p s hs
    rw [he,windowSum_mean _ (isolationOffset_injective s hs horder),avg_isolationIndicator,ZMod.card]
    linarith

theorem isolatedCount_boundedChanges (s : ZMod d) (hs : s≠0) :
    BoundedChanges (fun p : ZMod d → Bool => (isolatedCount p (extendShifts {0} s) : ℝ))
      (fun _ => 3) := by
  have he : (fun p : ZMod d → Bool => (isolatedCount p (extendShifts {0} s) : ℝ))=
      windowSum (isolationOffset s) isolationIndicator :=
    funext fun p => isolatedCount_eq_windowSum p s hs
  rw [he]
  apply windowSum_boundedChanges
  intro x
  dsimp [isolationIndicator]
  split <;> norm_num

theorem isolatedCount_lower_tail (s : ZMod d) (hs : s≠0) (η : ℝ) (hη : 0≤η) :
    prob (fun p : ZMod d → Bool => (isolatedCount p (extendShifts {0} s) : ℝ)≤(1/4-η)*d) ≤
      Real.exp (-2*η^2*d/9) := by
  have hh := boundedDifferences_lower
    (fun p : ZMod d → Bool => (isolatedCount p (extendShifts {0} s) : ℝ))
    (fun _ => 3) (fun _ => by norm_num) (isolatedCount_boundedChanges s hs)
    (η*d) (by positivity)
  have hm := isolatedCount_mean s hs
  have he := prob_mono (fun (p : ZMod d → Bool) (hp : (isolatedCount p (extendShifts {0} s) : ℝ)≤(1/4-η)*d) =>
    show (isolatedCount p (extendShifts {0} s) : ℝ)≤
      avg (fun q : ZMod d → Bool => (isolatedCount q (extendShifts {0} s) : ℝ))-η*d by
      linarith)
  apply he.trans
  simp only [Finset.sum_const,Finset.card_univ,ZMod.card] at hh
  have hd : (d : ℝ)≠0 := by exact_mod_cast NeZero.ne d
  convert hh using 1
  congr 1
  field_simp
  ring

def IsolationGood (η : ℝ) (p : ZMod d → Bool) : Prop :=
  ∀ s : ZMod d, s≠0 → (1/4-η)*d≤(isolatedCount p (extendShifts {0} s) : ℝ)

theorem isolation_bad_probability (η : ℝ) (hη : 0≤η) :
    prob (fun p : ZMod d → Bool => ¬IsolationGood η p)≤
      ((d : ℝ)-1)*Real.exp (-2*η^2*d/9) := by
  apply nonzero_shift_union
  intro s hs
  exact (prob_mono (fun _ hp => le_of_lt (lt_of_not_ge hp))).trans
    (isolatedCount_lower_tail s hs η hη)

/-- Deleting any representatives can lose no more than their number of isolates. -/
theorem isolatedRows_delete (p : ZMod d → Bool) (Δ R : Finset (ZMod d)) :
    isolatedCount p Δ ≤ (isolatedRows p Δ (Finset.univ\R)).card+R.card := by
  classical
  have he : isolatedRows p Δ (Finset.univ\R)=(Finset.univ.filter (IsIsolated p Δ))\R := by
    ext x
    simp [isolatedRows,and_comm]
  rw [he,isolatedCount,Fintype.card_subtype]
  exact Finset.card_le_card_sdiff_add_card

theorem isolatedRows_zero_card (p : ZMod d → Bool) (R : Finset (ZMod d)) :
    (isolatedRows p {0} (Finset.univ\R)).card=d-R.card := by
  classical
  have he : isolatedRows p {0} (Finset.univ\R)=Finset.univ\R := by
    ext x
    simp [isolatedRows,isIsolated_zero]
  rw [he,Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,ZMod.card]

theorem IsolationGood.certificate_floor (η : ℝ) (hη : 0≤η) (p : ZMod d → Bool)
    (hp : IsolationGood η p) (R : Finset (ZMod d)) (hR : R.card=2)
    (t : ℕ → ZMod d) (k : ℕ) :
    (9/16-η/4)*(d : ℝ)+1/2 ≤
      2+certificate (fun j => ((isolatedRows p (translateSets t j) (Finset.univ\R)).card : ℝ)) k := by
  classical
  have hRd : R.card≤d := by simpa only [Finset.card_univ,ZMod.card] using Finset.card_le_univ R
  have h0 : ((isolatedRows p (translateSets t 0) (Finset.univ\R)).card : ℝ)=(d : ℝ)-2 := by
    simp only [translateSets,isolatedRows_zero_card,hR,Nat.cast_sub (by omega : 2≤d),Nat.cast_ofNat]
  have h1 : ((isolatedRows p (translateSets t 1) (Finset.univ\R)).card : ℝ)≤
      ((isolatedRows p (translateSets t 0) (Finset.univ\R)).card : ℝ) := by
    have hh := Finset.card_filter_le (Finset.univ\R) (IsIsolated p (translateSets t 1))
    have he : (Finset.univ\R).card=d-R.card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,ZMod.card]
    rw [he] at hh
    rw [show translateSets t 0={0} from rfl,isolatedRows_zero_card]
    exact_mod_cast hh
  apply isolation_certificate_floor d η
    (fun j => ((isolatedRows p (translateSets t j) (Finset.univ\R)).card : ℝ))
    (fun _ => Nat.cast_nonneg _) h0 h1 _ k
  by_cases hs : t 0=0
  · have he : translateSets t 1={0} := by simp [translateSets,hs,extendShifts]
    rw [he,isolatedRows_zero_card,hR,Nat.cast_sub (by omega : 2≤d)]
    norm_num only [Nat.cast_ofNat]
    nlinarith [mul_nonneg hη (Nat.cast_nonneg (α := ℝ) d)]
  · have hh := isolatedRows_delete p (extendShifts {0} (t 0)) R
    have hh' : (isolatedCount p (extendShifts {0} (t 0)) : ℝ) ≤
        ((isolatedRows p (extendShifts {0} (t 0)) (Finset.univ\R)).card : ℝ)+2 := by
      exact_mod_cast (by simpa only [hR] using hh)
    have hg := hp (t 0) hs
    change (d : ℝ)/4-η*d-2≤
      ((isolatedRows p (extendShifts {0} (t 0)) (Finset.univ\R)).card : ℝ)
    linarith

/-- The sampled event already quantifies over every choice of the two deleted
representatives and every mask-dependent finite shift chain. -/
theorem isolation_floor_probability (η : ℝ) (hη : 0≤η) :
    prob (fun p : ZMod d → Bool => ¬∀ (R : Finset (ZMod d)), R.card=2 →
      ∀ (t : ℕ → ZMod d) (k : ℕ), (9/16-η/4)*(d : ℝ)+1/2 ≤
        2+certificate (fun j => ((isolatedRows p (translateSets t j) (Finset.univ\R)).card : ℝ)) k) ≤
      ((d : ℝ)-1)*Real.exp (-2*η^2*d/9) := by
  apply (prob_mono ?_).trans (isolation_bad_probability η hη)
  intro p hp hgood
  exact hp (hgood.certificate_floor η hη p)

end SharedDecoders.CapacityMaskProbability
