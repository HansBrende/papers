import SharedDecoders.CapacityMaskTernarySpectrum

/-! # Exact means and concentration for every fixed-depth actual run spectrum -/

namespace SharedDecoders.CapacityMaskProbability

open CapacityMask
open scoped BigOperators

theorem BoundedChanges.certificate {I κ : Type*} (f : ℕ → (I → κ) → ℝ)
    (c : ℕ → I → ℝ) (hf : ∀ j, BoundedChanges (f j) (c j)) (k : ℕ) :
    BoundedChanges (fun x => certificate (fun j => f j x) k)
      (fun i => certificate (fun j => c j i) k) := by
  exact (BoundedChanges.finset_sum (Finset.range k)
    (fun j x => f j x/2^(j+1)) (fun j i => c j i/2^(j+1))
    (fun j _ => (hf j).div_const _ (by positivity))).add
      ((hf k).div_const _ (by positivity))

theorem avg_certificate {α : Type*} [Fintype α] (f : ℕ → α → ℝ) (k : ℕ) :
    avg (fun x => certificate (fun j => f j x) k)=certificate (fun j => avg (f j)) k := by
  simp only [certificate,avg_add,avg_finset_sum,avg_div]

end SharedDecoders.CapacityMaskProbability

namespace SharedDecoders.CapacityTernarySpectrum

open CapacityMaskProbability CapacityMask CapacityRuns Module
open scoped BigOperators

noncomputable def meanSequence (j : ℕ) : ℝ := if j=0 then 0 else 1/(2 : ℝ)^(radius j)
noncomputable def sensitivitySequence (j : ℕ) : ℝ := if j=0 then 0 else (radius j : ℝ)+1
noncomputable def meanCoefficient (k : ℕ) : ℝ := certificate meanSequence k
noncomputable def sensitivity (k : ℕ) : ℝ := certificate sensitivitySequence k


theorem meanCoefficient_expansion (k : ℕ) (hk : 0<k) :
    meanCoefficient k=(∑ i∈Finset.range (k-1),
      (1/(2 : ℝ)^(radius (i+1)))/2^(i+2))+(1/(2 : ℝ)^(radius k))/2^k := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hk)
  simp [meanCoefficient,certificate,meanSequence,Finset.sum_range_succ',Nat.add_assoc]

theorem sensitivity_expansion (k : ℕ) (hk : 0<k) :
    sensitivity k=(∑ i∈Finset.range (k-1),
      ((radius (i+1) : ℝ)+1)/2^(i+2))+((radius k : ℝ)+1)/2^k := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hk)
  simp [sensitivity,certificate,sensitivitySequence,Finset.sum_range_succ',Nat.add_assoc]

theorem sensitivitySequence_nonneg (j : ℕ) : 0≤sensitivitySequence j := by
  unfold sensitivitySequence
  split <;> positivity

theorem sensitivity_pos (k : ℕ) (hk : 0<k) : 0<sensitivity k := by
  have hs : 0≤∑ j∈Finset.range k, sensitivitySequence j/2^(j+1) :=
    Finset.sum_nonneg (fun j _ => div_nonneg (sensitivitySequence_nonneg j) (by positivity))
  have ht : 0<sensitivitySequence k/2^k := by
    simp only [sensitivitySequence,ite_eq_right (Nat.ne_zero_of_lt hk)]
    positivity
  exact add_pos_of_nonneg_of_pos hs ht

theorem certificate_congr_prefix {x y : ℕ → ℝ} (k : ℕ) (h : ∀ j≤k, x j=y j) :
    certificate x k=certificate y k := by
  unfold certificate
  rw [h k le_rfl]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [h j (by have := Finset.mem_range.mp hj; omega)]

variable {d : ℕ} [NeZero d]

theorem runSequence_boundedChanges (j : ℕ) :
    BoundedChanges (fun p : ZMod d → Bool => runSequence p j) (fun _ => sensitivitySequence j) := by
  by_cases hj : j=0
  · subst j
    intro i p q hpq
    simp [runSequence,sensitivitySequence]
  · simpa only [runSequence,sensitivitySequence,ite_eq_right hj,Nat.cast_add,Nat.cast_one] using
      runCount_boundedChanges (d := d) (radius j) (radius_pos (by omega))

theorem spectrum_boundedChanges (k : ℕ) :
    BoundedChanges (spectrum (d := d) k) (fun _ => sensitivity k) :=
  BoundedChanges.certificate (fun j p => runSequence p j) (fun j _ => sensitivitySequence j)
    runSequence_boundedChanges k

theorem spectrum_mean (k : ℕ) (hd : radius k<d) :
    avg (spectrum (d := d) k)=(d : ℝ)*meanCoefficient k := by
  change avg (fun p : ZMod d → Bool => certificate (fun j => runSequence p j) k)=_
  rw [avg_certificate]
  have he : certificate (fun j => avg (fun p : ZMod d → Bool => runSequence p j)) k=
      certificate (fun j => (d : ℝ)*meanSequence j) k := by
    apply certificate_congr_prefix
    intro j hj
    by_cases hj0 : j=0
    · subst j
      simp [runSequence,meanSequence,avg_const]
    · have hjd : radius j<d := (radius_mono hj).trans_lt hd
      simp only [runSequence,meanSequence,ite_eq_right hj0]
      rw [runCount_mean (radius j) (radius_pos (by omega)) hjd]
      ring
  rw [he,certificate_const_mul]
  rfl

/-- `c_k` and `L_k` are the exact dyadic sums of actual local-window means
and sensitivities, with no probabilistic or graph-count input hypothesis. -/
theorem spectrum_upper_tail (k : ℕ) (hk : 0<k) (hd : radius k<d)
    (ε : ℝ) (hε : 0≤ε) :
    prob (fun p : ZMod d → Bool => (meanCoefficient k+ε)*d≤spectrum k p)≤
      Real.exp (-2*ε^2*d/(sensitivity k)^2) := by
  have hh := boundedDifferences_upper (spectrum (d := d) k) (fun _ => sensitivity k)
    (fun _ => le_of_lt (sensitivity_pos k hk)) (spectrum_boundedChanges k)
    (ε*d) (by positivity)
  rw [spectrum_mean k hd] at hh
  simp only [Finset.sum_const,Finset.card_univ,ZMod.card] at hh
  have he : (d : ℝ)*meanCoefficient k+ε*d=(meanCoefficient k+ε)*d := by ring
  rw [he] at hh
  have hd0 : (d : ℝ)≠0 := by exact_mod_cast NeZero.ne d
  have hL : sensitivity k≠0 := ne_of_gt (sensitivity_pos k hk)
  convert hh using 1
  congr 1
  field_simp
  ring

def Good (k : ℕ) (ε : ℝ) (p : ZMod d → Bool) : Prop :=
  spectrum k p≤(meanCoefficient k+ε)*d

theorem bad_probability (k : ℕ) (hk : 0<k) (hd : radius k<d) (ε : ℝ) (hε : 0≤ε) :
    prob (fun p : ZMod d → Bool => ¬Good k ε p)≤Real.exp (-2*ε^2*d/(sensitivity k)^2) :=
  (prob_mono (fun _ hp => le_of_lt (lt_of_not_ge hp))).trans (spectrum_upper_tail k hk hd ε hε)

variable {F A : Type*} [Field F] [AddCommGroup A] [Module F A] [FiniteDimensional F A]

theorem Good.source_bound (hd : 1<d) (k : ℕ) (hk : 2≤k) (ε : ℝ)
    {p : ZMod d → Bool} (hp : Good k ε p) {C : Submodule F (State d A)}
    (h : IsSharedCode F p C) :
    (finrank F C : ℝ)≤(1/2+meanCoefficient k+ε)*(d : ℝ)^2*finrank F A+
      (3/4)*(d : ℝ)*finrank F A := by
  have hh := CapacityTernarySpectrum.source_bound hd k hk h
  have hm := mul_le_mul_of_nonneg_left hp (show (0 : ℝ)≤(d : ℝ)*finrank F A by positivity)
  nlinarith only [hh,hm]

end SharedDecoders.CapacityTernarySpectrum
