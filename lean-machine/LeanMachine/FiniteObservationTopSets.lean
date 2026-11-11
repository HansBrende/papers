import LeanMachine.FiniteTopSets
import LeanMachine.ContextPruning

/-! # Top sets of actual conditional observations

All atom weights are summed from the original finite law. The envelope for a
retained event is derived from avoidance of these actual top sets, and a
coarsening pays only its literal finite fibre cardinality.
-/

namespace LeanMachine.FiniteObservationTopSets

open Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {Ω V W Z : Type*} [Fintype Ω] [Fintype V] [DecidableEq V]

noncomputable def atom (w : Ω → ℝ) (z : Ω → Z) (f : Ω → V) (a : Z) (v : V) : ℝ :=
  ∑ x, if z x = a ∧ f x = v then w x else 0

noncomputable def context (w : Ω → ℝ) (z : Ω → Z) (a : Z) : ℝ :=
  ∑ x, if z x = a then w x else 0

omit [Fintype V] in
theorem atom_nonneg (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x)
    (z : Ω → Z) (f : Ω → V) (a : Z) (v : V) : 0 ≤ atom w z f a v := by
  apply sum_nonneg
  intro x _
  split
  · exact hw x
  · rfl

omit [Fintype V] in
theorem attained_atom_pos (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x)
    (z : Ω → Z) (f : Ω → V) (x : Ω) (hx : 0 < w x) :
    0 < atom w z f (z x) (f x) := by
  have hh : w x ≤ atom w z f (z x) (f x) := by
    unfold atom
    have hs := single_le_sum (f := fun y => if z y = z x ∧ f y = f x then w y else 0)
      (fun y (_hy : y ∈ (univ : Finset Ω)) => by split; exact hw y; rfl) (mem_univ x)
    simpa only [and_self, ite_true] using hs
  exact hx.trans_le hh

theorem sum_atom (w : Ω → ℝ) (z : Ω → Z) (f : Ω → V) (a : Z) :
    ∑ v, atom w z f a v = context w z a := by
  unfold atom context
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  by_cases h : z x = a <;> simp [h]

noncomputable def top (w : Ω → ℝ) (z : Ω → Z) (f : Ω → V) (a : Z) (K : ℕ) : Finset V :=
  FiniteTopSets.top (atom w z f a) K

theorem card_top_le (w : Ω → ℝ) (z : Ω → Z) (f : Ω → V) (a : Z) (K : ℕ) :
    (top w z f a K).card ≤ K := FiniteTopSets.card_top_le _ _

theorem outside_atom (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x)
    (z : Ω → Z) (f : Ω → V) (a : Z) (K : ℕ) {v : V}
    (hv : v ∉ top w z f a K) : atom w z f a v ≤ context w z a / (K + 1) := by
  simpa only [sum_atom] using
    FiniteTopSets.outside_le_total_div (atom w z f a) (atom_nonneg w hw z f a) K hv

omit [Fintype V] in
theorem atom_mono {w r : Ω → ℝ} (hrw : ∀ x, r x ≤ w x)
    (z : Ω → Z) (f : Ω → V) (a : Z) (v : V) : atom r z f a v ≤ atom w z f a v := by
  apply sum_le_sum
  intro x _
  split <;> simp_all

theorem coarsen_atom (w : Ω → ℝ) (z : Ω → Z) (f : Ω → V) (g : V → W)
    (a : Z) (c : W) :
    atom w z (g ∘ f) a c = ∑ v ∈ univ.filter (fun v => g v = c), atom w z f a v := by
  unfold atom
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  by_cases hz : z x = a <;> simp [hz]

/-- Avoiding the original conditional top sets controls every coarsened atom
on the retained event. No independence or uniformity of the law is required. -/
theorem coarsened_avoid_top (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x)
    (z : Ω → Z) (f : Ω → V) (g : V → W) (B : Finset Ω) (a : Z) (c : W)
    (K n : ℕ) (hfib : (univ.filter fun v => g v = c).card ≤ n)
    (havoid : ∀ x ∈ B, z x = a → f x ∉ top w z f a K) :
    atom (fun x => if x ∈ B then w x else 0) z (g ∘ f) a c ≤
      (n : ℝ) / (K + 1) * context w z a := by
  let r := fun x => if x ∈ B then w x else 0
  have htotal : 0 ≤ context w z a := by
    rw [← sum_atom w z f a]
    exact sum_nonneg (fun v _ => atom_nonneg w hw z f a v)
  have hbound (v : V) : atom r z f a v ≤ context w z a / (K + 1) := by
    by_cases hv : v ∈ top w z f a K
    · have hz : atom r z f a v = 0 := by
        apply sum_eq_zero
        intro x _
        by_cases hx : x ∈ B
        · have he : ¬(z x = a ∧ f x = v) := by
            rintro ⟨hza, hfv⟩
            exact havoid x hx hza (hfv ▸ hv)
          simp [he]
        · simp [r, hx]
      rw [hz]
      positivity
    · exact (atom_mono (fun x => by dsimp [r]; split <;> simp_all) z f a v).trans
        (outside_atom w hw z f a K hv)
  rw [coarsen_atom]
  calc
    _ ≤ ∑ _v ∈ univ.filter (fun v => g v = c), context w z a / (K + 1) :=
      sum_le_sum (fun v _ => hbound v)
    _ = ((univ.filter fun v => g v = c).card : ℝ) * (context w z a / (K + 1)) := by simp
    _ ≤ (n : ℝ) * (context w z a / (K + 1)) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hfib) (by positivity)
    _ = _ := by ring

/-- A positive attained observation outside the actual top set witnesses at
least K+1 original inputs in its original context fibre. -/
theorem context_card_of_outside (w : Ω → ℝ)
    (z : Ω → Z) (f : Ω → V) (a : Z) (K : ℕ) {v : V}
    (hv : v ∉ top w z f a K) (hpos : 0 < atom w z f a v) :
    K + 1 ≤ (univ.filter fun x => z x = a).card := by
  have hs := FiniteTopSets.support_large_of_outside (atom w z f a) K hv hpos
  have hsub : FiniteTopSets.positiveSupport (atom w z f a) ⊆
      (univ.filter fun x => z x = a).image f := by
    intro u hu
    have hp : 0 < atom w z f a u := (mem_filter.mp hu).2
    have hex : ∃ x, z x = a ∧ f x = u := by
      by_contra hn
      have hz : atom w z f a u = 0 := by
        apply sum_eq_zero
        intro x _
        simp [show ¬(z x = a ∧ f x = u) from fun h => hn ⟨x, h⟩]
      linarith
    obtain ⟨x, he⟩ := hex
    exact mem_image.mpr ⟨x, mem_filter.mpr ⟨mem_univ _, he.1⟩, he.2⟩
  exact hs.trans ((card_le_card hsub).trans card_image_le)

omit [Fintype V] in
theorem atom_eq_mass (w : Ω → ℝ) (B : Finset Ω) (z : Ω → Z)
    (f : Ω → V) (a : Z) (v : V) :
    atom (fun x => if x ∈ B then w x else 0) z f a v =
      ContextPruning.mass w (B ∩ ContextPruning.fibre f v ∩ ContextPruning.fibre z a) := by
  unfold ContextPruning.mass
  rw [show B ∩ ContextPruning.fibre f v ∩ ContextPruning.fibre z a =
    univ.filter (fun x => x ∈ B ∧ f x = v ∧ z x = a) by
      ext x
      simp [ContextPruning.fibre]]
  simp only [atom, sum_filter]
  apply sum_congr rfl
  intro x _
  by_cases hB : x ∈ B <;> by_cases hz : z x = a <;> by_cases hf : f x = v <;>
    simp [hB, hz, hf]

theorem context_eq_mass (w : Ω → ℝ) (z : Ω → Z) (a : Z) :
    context w z a = ContextPruning.mass w (ContextPruning.fibre z a) := by
  simp [context, ContextPruning.mass, ContextPruning.fibre, sum_filter]

/-- One retained event simultaneously bounds every coarsened word at every
attained context. There is no loss for the number of words sharing a context. -/
theorem exists_half_mass_avoid_top {I J : Type*} [Fintype I] [Nonempty I]
    (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (hprob : ContextPruning.mass w univ = 1)
    (z : I → Ω → Z) (f : J → I → Ω → V) (g : J → I → V → W)
    (B : Finset Ω) (hp : 0 < ContextPruning.mass w B) (K n : ℕ)
    (hfib : ∀ j i c, (univ.filter fun v => g j i v = c).card ≤ n)
    (havoid : ∀ j i x, x ∈ B → f j i x ∉ top w (z i) (f j i) (z i x) K) :
    ∃ D ⊆ B, ContextPruning.mass w B / 2 ≤ ContextPruning.mass w D ∧
      ∀ j i a c, 0 < ContextPruning.mass w (D ∩ ContextPruning.fibre (z i) a) →
        atom (fun x => if x ∈ D then w x else 0) (z i) (g j i ∘ f j i) a c /
          ContextPruning.mass w (D ∩ ContextPruning.fibre (z i) a) ≤
        2 * (n : ℝ) * Fintype.card I / ((K + 1) * ContextPruning.mass w B) := by
  obtain ⟨D, hDB, hmass, hcond⟩ :=
    ContextPruning.exists_half_mass_context_subset w hw hprob z B hp
  refine ⟨D, hDB, hmass, ?_⟩
  intro j i a c hden
  have he := coarsened_avoid_top w hw (z i) (f j i) (g j i) B a c K n (hfib j i c)
    (fun x hx hza => by simpa only [← hza] using havoid j i x hx)
  rw [atom_eq_mass, context_eq_mass] at he
  have hh := hcond i a (ContextPruning.fibre (g j i ∘ f j i) c)
    ((n : ℝ) / (K + 1)) (by positivity) hden he
  rw [atom_eq_mass]
  convert hh using 1
  field_simp

end LeanMachine.FiniteObservationTopSets
