import BoundedStackDepth.Machines
import Mathlib.Data.Nat.Find

/-!
# Whole-batch cuts from a chronological coarse dependency graph

A fine dependency edge may lift to several coarse edges, provided the lift
stays in its two endpoint batches. Revealing whole batches then transfers a
coarse full-path bound, with one extra vertex for a revealed root.
-/

namespace TapeStorageRates.BatchCoarsening

open Finset MergeDepth BoundedNesting

set_option autoImplicit false
noncomputable section
open Classical

variable {k : ℕ}

/-- A chronological coarse representation of fine dependency edges. -/
structure Coarsening (xs : Fin k → ℕ → ℤ) (T : ℕ)
    (ys : Fin k → ℕ → ℤ) (V B : ℕ) where
  positive : 0 < B
  phi : ℕ → ℕ
  owner : ℕ → ℕ
  owns : ∀ t < T, owner (phi t) = t / B
  edge_lift : ∀ {a b}, DepStep xs T a b → phi a = phi b ∨
    Relation.TransGen (fun u v => DepStep ys V u v ∧
      (owner u = a / B ∨ owner u = b / B) ∧
      (owner v = a / B ∨ owner v = b / B)) (phi a) (phi b)

/-- Every selected coarse vertex marks its entire containing fine batch. -/
def markedBatches (owner : ℕ → ℕ) (Γc : Finset ℕ) : Finset ℕ := Γc.image owner

def wholeBatchCut (T B : ℕ) (owner : ℕ → ℕ) (Γc : Finset ℕ) : Finset ℕ :=
  (range T).filter fun t => t / B ∈ markedBatches owner Γc

theorem markedBatches_card_le (owner : ℕ → ℕ) (Γc : Finset ℕ) :
    (markedBatches owner Γc).card ≤ Γc.card := card_image_le

@[simp] theorem mem_wholeBatchCut {T B t : ℕ} {owner : ℕ → ℕ} {Γc : Finset ℕ} :
    t ∈ wholeBatchCut T B owner Γc ↔ t < T ∧ t / B ∈ markedBatches owner Γc := by
  simp [wholeBatchCut]

private def HeightWitness (ys : Fin k → ℕ → ℤ) (V : ℕ) (Γc : Finset ℕ)
    (a n : ℕ) : Prop :=
  ∃ tail : List ℕ, IsDepPath ys V (a :: tail) ∧
    (∀ v ∈ a :: tail, v ∉ Γc) ∧ (a :: tail).length = n

private def height (ys : Fin k → ℕ → ℤ) (V : ℕ) (Γc : Finset ℕ)
    (H a : ℕ) : ℕ := Nat.findGreatest (HeightWitness ys V Γc a) H

private theorem witness_one (ys : Fin k → ℕ → ℤ) (V : ℕ) (Γc : Finset ℕ)
    {a : ℕ} (ha : a ∉ Γc) : HeightWitness ys V Γc a 1 := by
  exact ⟨[], trivial, by simpa using ha, rfl⟩

private theorem height_le (ys : Fin k → ℕ → ℤ) (V : ℕ) (Γc : Finset ℕ)
    (H a : ℕ) : height ys V Γc H a ≤ H := Nat.findGreatest_le H

private theorem height_pos (ys : Fin k → ℕ → ℤ) (V : ℕ) (Γc : Finset ℕ)
    {H a : ℕ} (hH : 1 ≤ H) (ha : a ∉ Γc) : 1 ≤ height ys V Γc H a :=
  Nat.le_findGreatest hH (witness_one ys V Γc ha)

private theorem height_spec (ys : Fin k → ℕ → ℤ) (V : ℕ) (Γc : Finset ℕ)
    {H a : ℕ} (hH : 1 ≤ H) (ha : a ∉ Γc) :
    HeightWitness ys V Γc a (height ys V Γc H a) :=
  Nat.findGreatest_spec hH (witness_one ys V Γc ha)

private theorem height_step (ys : Fin k → ℕ → ℤ) (V : ℕ) (Γc : Finset ℕ)
    {H : ℕ} (hdepth : ∀ π, IsDepPath ys V π → LinNet.GFree Γc π → π.length ≤ H)
    {a b : ℕ} (hab : DepStep ys V a b) (ha : a ∉ Γc) (hb : b ∉ Γc) :
    height ys V Γc H b < height ys V Γc H a := by
  have hH : 1 ≤ H := hdepth [0] trivial (by simp [LinNet.GFree])
  obtain ⟨tail, hp, hf, he⟩ := height_spec ys V Γc hH hb
  have hp' : IsDepPath ys V (a :: b :: tail) := ⟨hab, hp⟩
  have hf' : ∀ v ∈ a :: b :: tail, v ∉ Γc := by
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact ha
    · exact hf v hv
  have hlen := hdepth (a :: b :: tail) hp' (by
    simpa [LinNet.GFree] using hf)
  have hw : HeightWitness ys V Γc a ((a :: b :: tail).length) :=
    ⟨b :: tail, hp', hf', rfl⟩
  have hmax := Nat.le_findGreatest hlen hw
  change (a :: b :: tail).length ≤ height ys V Γc H a at hmax
  simp only [List.length_cons] at he hmax
  omega

private theorem depPath_mem_le_head (xs : Fin k → ℕ → ℤ) (T : ℕ) :
    ∀ (tail : List ℕ) (a : ℕ), IsDepPath xs T (a :: tail) →
      ∀ v ∈ a :: tail, v ≤ a
  | [], a, _, v, hv => by simpa using (List.mem_singleton.mp hv).le
  | b :: tail, a, hp, v, hv => by
    rcases List.mem_cons.mp hv with rfl | hv
    · exact le_rfl
    · exact (depPath_mem_le_head xs T tail b hp.2 v hv).trans
        (depStep_lt hp.1).1.le

/-- Every vertex after the first of a dependency path is before the horizon. -/
theorem depPath_tail_lt (xs : Fin k → ℕ → ℤ) (T : ℕ)
    (π : List ℕ) (hp : IsDepPath xs T π) : ∀ v ∈ π.tail, v < T := by
  cases π with
  | nil => simp
  | cons a tail =>
    cases tail with
    | nil => simp
    | cons b tail =>
      intro v hv
      have hbT := (depStep_lt hp.1).1.trans (depStep_lt hp.1).2
      exact (depPath_mem_le_head xs T tail b hp.2 v hv).trans_lt hbT

private theorem length_le_of_decreasing (R : ℕ → ℕ → Prop) (f : ℕ → ℕ) :
    ∀ (tail : List ℕ) (a : ℕ),
      (∀ u v, R u v → f v < f u) →
      (a :: tail).IsChain R → (a :: tail).length ≤ f a + 1
  | [], _, _, _ => by simp
  | b :: tail, a, hstep, hp => by
    have hab : R a b := (List.isChain_cons_cons.mp hp).1
    have htail := (List.isChain_cons_cons.mp hp).2
    have ih := length_le_of_decreasing R f tail b hstep htail
    have hlt := hstep a b hab
    simp only [List.length_cons] at ih ⊢
    omega

private theorem depPath_chain (xs : Fin k → ℕ → ℤ) (T : ℕ) :
    ∀ π : List ℕ, IsDepPath xs T π → π.IsChain (DepStep xs T)
  | [], _ => by simp
  | [_], _ => by simp
  | a :: b :: tail, hp => List.isChain_cons_cons.mpr
      ⟨hp.1, depPath_chain xs T (b :: tail) hp.2⟩

namespace Coarsening

variable {xs ys : Fin k → ℕ → ℤ} {T V B : ℕ}
variable (C : Coarsening xs T ys V B)

private theorem coarse_height_lt {Γc : Finset ℕ} {H a b : ℕ}
    (hdepth : ∀ π, IsDepPath ys V π → LinNet.GFree Γc π → π.length ≤ H)
    (hab : DepStep xs T a b)
    (ha : a / B ∉ markedBatches C.owner Γc)
    (hb : b / B ∉ markedBatches C.owner Γc)
    (hne : C.phi a ≠ C.phi b) :
    height ys V Γc H (C.phi b) < height ys V Γc H (C.phi a) := by
  have unmarked {v : ℕ} (hv : C.owner v = a / B ∨ C.owner v = b / B) : v ∉ Γc := by
    intro h
    have hm : C.owner v ∈ markedBatches C.owner Γc := mem_image.mpr ⟨v, h, rfl⟩
    rcases hv with h | h
    · exact ha (h ▸ hm)
    · exact hb (h ▸ hm)
  rcases C.edge_lift hab with h | h
  · exact (hne h).elim
  · exact Relation.TransGen.trans_induction_on
      (motive := fun {u v} _ => height ys V Γc H v < height ys V Γc H u) h
      (fun huv => height_step ys V Γc hdepth huv.1 (unmarked huv.2.1) (unmarked huv.2.2))
      (fun _ _ h₁ h₂ => h₂.trans h₁)

/-- A full-path bound transfers across endpoint-batch edge lifts. The root may be revealed. -/
theorem path_length_le {Γc : Finset ℕ} {H : ℕ}
    (hdepth : ∀ π, IsDepPath ys V π → LinNet.GFree Γc π → π.length ≤ H)
    (π : List ℕ) (hp : IsDepPath xs T π)
    (hf : LinNet.GFree (wholeBatchCut T B C.owner Γc) π) :
    π.length ≤ B * H + 1 := by
  have hH : 1 ≤ H := hdepth [0] trivial (by simp [LinNet.GFree])
  let f : ℕ → ℕ := fun t => B * (height ys V Γc H (C.phi t) - 1) + t % B
  have dec {a b : ℕ} (hab : DepStep xs T a b)
      (ha : a / B ∉ markedBatches C.owner Γc)
      (hb : b / B ∉ markedBatches C.owner Γc) : f b < f a := by
    obtain ⟨hba, haT⟩ := depStep_lt hab
    have hbT := hba.trans haT
    have apos : 1 ≤ height ys V Γc H (C.phi a) := height_pos ys V Γc hH (by
      intro h
      apply ha
      rw [← C.owns a haT]
      exact mem_image.mpr ⟨_, h, rfl⟩)
    have bpos : 1 ≤ height ys V Γc H (C.phi b) := height_pos ys V Γc hH (by
      intro h
      apply hb
      rw [← C.owns b hbT]
      exact mem_image.mpr ⟨_, h, rfl⟩)
    have amod := Nat.mod_lt a C.positive
    have bmod := Nat.mod_lt b C.positive
    by_cases he : C.phi a = C.phi b
    · have hdiv : a / B = b / B := by rw [← C.owns a haT, ← C.owns b hbT, he]
      have hmod : b % B < a % B := by
        have h₁ := Nat.div_add_mod a B
        have h₂ := Nat.div_add_mod b B
        rw [hdiv] at h₁
        omega
      simp only [f, he]
      omega
    · have hheight := C.coarse_height_lt hdepth hab ha hb he
      have hmul : B * (height ys V Γc H (C.phi b) - 1) + B ≤
          B * (height ys V Γc H (C.phi a) - 1) := by
        rw [← Nat.mul_succ]
        exact Nat.mul_le_mul_left B (by omega)
      dsimp [f]
      omega
  cases π with
  | nil => simp
  | cons a tail =>
    cases tail with
    | nil => simp
    | cons b tail =>
      have hbT : b < T := (depStep_lt hp.1).1.trans (depStep_lt hp.1).2
      have allT : ∀ t ∈ b :: tail, t < T := fun t ht =>
        (depPath_mem_le_head xs T tail b hp.2 t ht).trans_lt hbT
      have allfree : ∀ t ∈ b :: tail, t / B ∉ markedBatches C.owner Γc := by
        intro t ht hm
        exact hf t ht (mem_wholeBatchCut.mpr ⟨allT t ht, hm⟩)
      let R : ℕ → ℕ → Prop := fun u v => DepStep xs T u v ∧
        u / B ∉ markedBatches C.owner Γc ∧ v / B ∉ markedBatches C.owner Γc
      have chain : (b :: tail).IsChain R := by
        apply (depPath_chain xs T _ hp.2).imp_of_mem_imp
        intro u v hu hv huv
        exact ⟨huv, allfree u hu, allfree v hv⟩
      have hl := length_le_of_decreasing R f tail b (fun u v h => dec h.1 h.2.1 h.2.2) chain
      have hbound : f b + 1 ≤ B * H := by
        have hbmod := Nat.mod_lt b C.positive
        have hh := height_le ys V Γc H (C.phi b)
        have hm : B * (height ys V Γc H (C.phi b) - 1) + B ≤ B * H := by
          rw [← Nat.mul_succ]
          exact Nat.mul_le_mul_left B (by omega)
        dsimp [f]
        omega
      simp only [List.length_cons] at hl ⊢
      omega

/-- The coarse cut can be restricted to its actual time horizon, so every marked batch exists. -/
theorem exists_cut_bounded (hV : 1 ≤ V) (hy : ∀ h, IsWalk (ys h))
    {η : ℝ} (hη : 0 < η) :
    ∃ Γc : Finset ℕ, Γc ⊆ range V ∧ (Γc.card : ℝ) ≤ η * V ∧
      (markedBatches C.owner Γc).card ≤ Γc.card ∧
      ∀ π, IsDepPath xs T π → LinNet.GFree (wholeBatchCut T B C.owner Γc) π →
        π.length ≤ B * BoundedStackDepth.genieDepth k 1 1 η + 1 := by
  obtain ⟨Γ₀, hc, hd⟩ := BoundedStackDepth.genie_cost (by decide : 1 ≤ 1) hV
    (by norm_num : (1 : ℝ) ≤ 1) hη (by norm_num : (V : ℝ) ≤ 1 * (V + 1)) ys hy
  let Γc := Γ₀ ∩ range V
  have hc' : (Γc.card : ℝ) ≤ η * V := by
    calc (Γc.card : ℝ) ≤ Γ₀.card := by exact_mod_cast card_le_card inter_subset_left
         _ ≤ η * V := by simpa using hc
  have hd' (π : List ℕ) (hp : IsDepPath ys V π) (hf : LinNet.GFree Γc π) :
      π.length ≤ BoundedStackDepth.genieDepth k 1 1 η := by
    apply hd π hp
    intro v hv hmem
    exact hf v hv (mem_inter.mpr ⟨hmem, mem_range.mpr (depPath_tail_lt ys V π hp v hv)⟩)
  exact ⟨Γc, inter_subset_right, hc', markedBatches_card_le _ _,
    fun π hp hf => C.path_length_le hd' π hp hf⟩

end Coarsening
end
end TapeStorageRates.BatchCoarsening
