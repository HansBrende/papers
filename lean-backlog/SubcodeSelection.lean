import EntropyConsolidation
import TransposeFollowup.EntropyFibers
import DecoderEntropy
import DecoderSelection

/-!
# Exact subcodes selected from finite distributions

Finite random decoder tables and the existing Gibbs inequality select an
exact code inside the positive support. The record version adds one decoding
constraint rather than repeating the argument on conditional distributions.
All entropies use natural logarithms.
-/

namespace LeanBacklog.SubcodeSelection

open Finset TransposeFollowup MotionDepthCodes EntropyConsolidation
open scoped BigOperators
set_option autoImplicit false
open DecoderEntropy

/-- Gibbs with a finite mass cap, including zero-probability source points. -/
theorem entropy_add_mean_log_le_log_cap {A : Type*} [Fintype A]
    (p a : A → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (ha : ∀ x, 0 ≤ a x) (hsupport : ∀ x, 0 < p x → 0 < a x)
    (M : ℝ) (hM : 0 < M) (hcap : ∑ x, a x ≤ M) :
    entropy p + ∑ x, p x * Real.log (a x) ≤ Real.log M := by
  have hsum : ∑ x, a x / M ≤ 1 := by
    rw [← Finset.sum_div]
    exact (div_le_one hM).mpr hcap
  have hg := entropy_le_crossEntropy p (fun x => a x / M) hp
    (fun x => div_nonneg (ha x) hM.le) hp1 hsum
    (fun x hx => div_pos (hsupport x hx) hM)
  have hlog : ∀ x, p x * Real.log (a x / M) =
      p x * Real.log (a x) - p x * Real.log M := by
    intro x
    by_cases hz : p x = 0
    · simp [hz]
    · rw [Real.log_div (hsupport x (lt_of_le_of_ne (hp x) (Ne.symm hz))).ne'
        hM.ne', mul_sub]
  simp_rw [hlog] at hg
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hp1, one_mul] at hg
  linarith

/-- A probability law has a point of positive mass, even when no
nonemptiness instance was supplied for its sample space. -/
theorem exists_pos_mass {A : Type*} [Fintype A]
    (p : A → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1) :
    ∃ x, 0 < p x := by
  have hs : 0 < ∑ x, p x := by rw [hp1]; norm_num
  obtain ⟨x, _, hx⟩ := (Finset.sum_pos_iff_of_nonneg (fun x _ => hp x)).mp hs
  exact ⟨x, hx⟩

theorem pushforward_pos_iff {Ω A : Type*} [Fintype Ω]
    (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (X : Ω → A) (x : A) :
    0 < pushforward p X x ↔ ∃ ω, 0 < p ω ∧ X ω = x := by
  classical
  constructor
  · intro h
    obtain ⟨ω, _, hω⟩ := (Finset.sum_pos_iff_of_nonneg
      (fun ω _ => by split_ifs; exact hp ω; exact le_rfl)).mp h
    split_ifs at hω with heq
    · exact ⟨ω, hω, heq⟩
    · exact (lt_irrefl _ hω).elim
  · rintro ⟨ω, hω, rfl⟩
    exact hω.trans_le (le_pushforward p hp X ω)

theorem codeEntropy_univ_eq_observationEntropy {V Ω α : Type*}
    [DecidableEq V] [Fintype V] [Fintype Ω] [Fintype α] [Nonempty Ω]
    (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (X : Ω → V → α) :
    codeEntropy p X univ = observationEntropy p X := by
  classical
  let : Nonempty (V → α) := ⟨X (Classical.arbitrary Ω)⟩
  apply observationEntropy_eq_of_same_fibers p hp
  intro ω ω'
  rw [view_eq_iff]
  simp only [Finset.mem_univ, forall_const, funext_iff]

theorem recoveryError_eq_conditional {V Ω α : Type*}
    [DecidableEq V] [Fintype V] [Fintype Ω] [Fintype α] [Nonempty Ω]
    (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (X : Ω → V → α)
    (H : V → Finset V) (v : V) :
    recoveryError (codeEntropy p X) H v =
      conditionalObservationEntropy p (fun ω => X ω v)
        (fun ω => view (H v) (X ω)) := by
  classical
  let : Nonempty α := ⟨X (Classical.arbitrary Ω) v⟩
  unfold recoveryError conditionalObservationEntropy codeEntropy
  congr 1
  apply observationEntropy_eq_of_same_fibers p hp
  intro ω ω'
  simp only [view_eq_iff, Finset.mem_insert, Prod.mk.injEq]
  constructor
  · intro h
    exact ⟨fun u hu => h u (Or.inr hu), h v (Or.inl rfl)⟩
  · rintro ⟨hH, hv⟩ u (rfl | hu)
    · exact hv
    · exact hH u hu

/-- Simultaneously make any finite collection of functional dependencies exact.
The value and helper alphabets may differ between constraints. -/
theorem exists_dependency_subset {A I : Type*} [Fintype A] [Fintype I]
    {B C : I → Type*} [∀ i, Fintype (B i)] [∀ i, Fintype (C i)]
    (p : A → ℝ) (hp : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1)
    (f : ∀ i, A → C i) (g : ∀ i, A → B i) :
    ∃ D : Finset A, D.Nonempty ∧ (∀ a ∈ D, 0 < p a) ∧
      (∀ i, ∀ x ∈ D, ∀ y ∈ D, g i x = g i y → f i x = f i y) ∧
      entropy p - ∑ i, conditionalObservationEntropy p (f i) (g i) ≤
        Real.log D.card := by
  classical
  obtain ⟨a₀, ha₀⟩ := exists_pos_mass p hp hp1
  let : ∀ i, Nonempty (C i) := fun i => ⟨f i a₀⟩
  let S := univ.filter (fun a => 0 < p a)
  let q := fun i => conditionalResponse p (f i) (g i)
  obtain ⟨D, hDS, hdet, hcount⟩ := DecoderSelection.exists_decodable_subset q
    (fun i => conditionalResponse_nonneg p hp (f i) (g i))
    (fun i => conditionalResponse_sum p (f i) (g i)) f g S
  change (∑ a ∈ S, responseSuccess p f g a) ≤ (D.card : ℝ) at hcount
  have hpos : 0 < ∑ a ∈ S, responseSuccess p f g a :=
    (responseSuccess_pos p hp f g a₀ ha₀).trans_le
      (Finset.single_le_sum (fun a _ => responseSuccess_nonneg p hp f g a)
        (by simp [S, ha₀]))
  have hD : 0 < (D.card : ℝ) := hpos.trans_le hcount
  refine ⟨D, Finset.card_pos.mp (Nat.cast_pos.mp hD),
    fun a ha => (mem_filter.mp (hDS ha)).2, hdet, ?_⟩
  let a := fun x => if 0 < p x then responseSuccess p f g x else 0
  have ha : ∀ x, 0 ≤ a x := by
    intro x
    dsimp [a]
    split_ifs
    · exact responseSuccess_nonneg p hp f g x
    · exact le_rfl
  have hsupport : ∀ x, 0 < p x → 0 < a x := by
    intro x hx
    simpa [a, hx] using responseSuccess_pos p hp f g x hx
  have hcap : ∑ x, a x ≤ (D.card : ℝ) := by
    simpa [a, S, Finset.sum_filter] using hcount
  have hlog : ∑ x, p x * Real.log (a x) =
      ∑ x, p x * Real.log (responseSuccess p f g x) := by
    apply sum_congr rfl
    intro x _
    by_cases hx : 0 < p x
    · simp [a, hx]
    · have hz : p x = 0 := le_antisymm (not_lt.mp hx) (hp x)
      simp [hz]
  have h := entropy_add_mean_log_le_log_cap p a hp hp1 ha hsupport _ hD hcap
  rw [hlog, responseSuccess_log p hp f g] at h
  exact h

/-- The same theorem for an observation of a finite sample space. Counting
the distinct observed states, rather than samples, avoids duplicate words. -/
theorem exists_observed_dependency_subset {Ω A I : Type*}
    [Fintype Ω] [Fintype A] [Fintype I]
    {B C : I → Type*} [∀ i, Fintype (B i)] [∀ i, Fintype (C i)]
    (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1)
    (X : Ω → A) (f : ∀ i, A → C i) (g : ∀ i, A → B i) :
    ∃ D : Finset A, D.Nonempty ∧
      (∀ x ∈ D, ∃ ω, 0 < p ω ∧ X ω = x) ∧
      (∀ i, ∀ x ∈ D, ∀ y ∈ D, g i x = g i y → f i x = f i y) ∧
      observationEntropy p X -
        ∑ i, conditionalObservationEntropy p (fun ω => f i (X ω))
          (fun ω => g i (X ω)) ≤ Real.log D.card := by
  obtain ⟨D, hD, hs, hf, hbound⟩ := exists_dependency_subset
    (pushforward p X) (pushforward_nonneg p hp X)
    (by rw [sum_pushforward, hp1]) f g
  refine ⟨D, hD, fun x hx => (pushforward_pos_iff p hp X x).mp (hs x hx), hf, ?_⟩
  simpa only [conditionalObservationEntropy, observationEntropy, pushforward_comp,
    Function.comp_def] using hbound

/-- Every finite distribution has an exact storage subcode inside its positive
support, paying only the sum of its conditional recovery entropies. -/
theorem subcode_selection {V Ω α : Type*}
    [DecidableEq V] [Fintype V] [Fintype Ω] [Fintype α]
    (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1)
    (X : Ω → V → α) (H : V → Finset V) :
    ∃ D : Finset (V → α), D.Nonempty ∧
      (∀ x ∈ D, ∃ ω, 0 < p ω ∧ X ω = x) ∧ IsStorageCode H D ∧
      codeEntropy p X univ - ∑ v, recoveryError (codeEntropy p X) H v ≤
        Real.log D.card := by
  obtain ⟨ω₀, _⟩ := exists_pos_mass p hp hp1
  let : Nonempty Ω := ⟨ω₀⟩
  obtain ⟨D, hD, hs, hf, hbound⟩ := exists_observed_dependency_subset p hp hp1 X
    (fun (v : V) (x : V → α) => x v) (fun v x => view (H v) x)
  refine ⟨D, hD, hs, ?_, ?_⟩
  · intro x hx y hy v hv
    exact hf v x hx y hy ((view_eq_iff _ _ _).mpr hv)
  · rw [codeEntropy_univ_eq_observationEntropy p hp X]
    simpa only [recoveryError_eq_conditional p hp X H] using hbound

/-- The original unconditioned target, with no extra hypotheses. -/
theorem subcodeSelectionTarget {V : Type} [DecidableEq V] [Fintype V] :
    SubcodeSelectionTarget (V := V) := by
  intro Ω α _ _ _ p hp hp1 X H
  exact subcode_selection p hp hp1 X H

#print axioms exists_dependency_subset
#print axioms exists_observed_dependency_subset
#print axioms subcode_selection
#print axioms subcodeSelectionTarget

end LeanBacklog.SubcodeSelection
