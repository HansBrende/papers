import ClosureBarriers
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.FieldSimp

/-!
# Empty-rectangle barrier for transported coordinate closure

This proves `ClosureBarriers.RectangleBarrierTarget`. The proof also allows
different helper incidences in the different layouts, provided each has the
same empty-rectangle exclusion. Recovery ranks may have ties: at the first
threshold rank we select exactly the required number of completed rows.
-/

namespace LeanBacklog.RectangleBarrier

open Finset ClosureBarriers

universe u

variable {V : Type u} {d : ℕ}

/-- The cells of a rectangle in a chosen layout. -/
def cells (e : V ≃ Fin d × Fin d) (R C : Finset (Fin d)) : Finset V :=
  (R ×ˢ C).map e.symm.toEmbedding

@[simp] theorem mem_cells (e : V ≃ Fin d × Fin d) (R C : Finset (Fin d))
    (x : V) : x ∈ cells e R C ↔ (e x).1 ∈ R ∧ (e x).2 ∈ C := by
  simp [cells]

@[simp] theorem card_cells (e : V ≃ Fin d × Fin d) (R C : Finset (Fin d)) :
    (cells e R C).card = R.card * C.card := by
  simp [cells]

variable [DecidableEq V]

/-- Rows entirely present in the known cell set. -/
def completeRows (e : V ≃ Fin d × Fin d) (A : Finset V) : Finset (Fin d) :=
  univ.filter fun i => ∀ c, e.symm (i, c) ∈ A

@[simp] theorem mem_completeRows (e : V ≃ Fin d × Fin d) (A : Finset V)
    (i : Fin d) : i ∈ completeRows e A ↔ ∀ c, e.symm (i, c) ∈ A := by
  simp [completeRows]

theorem cells_subset_of_complete (e : V ≃ Fin d × Fin d) (A : Finset V)
    {R : Finset (Fin d)} (hR : R ⊆ completeRows e A) :
    cells e R univ ⊆ A := by
  intro x hx
  have h := (mem_completeRows e A _).1 (hR ((mem_cells e R univ x).1 hx).1)
  simpa using h (e x).2

/-- Columns whose entire helper-row union is already known. -/
def readyColumns (ρ : Fin d → Finset (Fin d)) (e : V ≃ Fin d × Fin d)
    (A : Finset V) : Finset (Fin d) :=
  univ.filter fun c => ρ c ⊆ completeRows e A

@[simp] theorem mem_readyColumns (ρ : Fin d → Finset (Fin d))
    (e : V ≃ Fin d × Fin d) (A : Finset V) (c : Fin d) :
    c ∈ readyColumns ρ e A ↔ ρ c ⊆ completeRows e A := by
  simp [readyColumns]

theorem ready_of_helpers_subset [Fintype V] (ρ : Fin d → Finset (Fin d))
    (e : V ≃ Fin d × Fin d) (A : Finset V) (x : V)
    (h : gridHelpers ρ e x ⊆ A) : (e x).2 ∈ readyColumns ρ e A := by
  rw [mem_readyColumns]
  intro i hi
  rw [mem_completeRows]
  intro c
  apply h
  simpa [gridHelpers] using hi

/-- An incomplete row set of size at least `r` leaves fewer than `r`
ready columns; otherwise these rows and columns would form an empty rectangle. -/
theorem ready_card_lt (ρ : Fin d → Finset (Fin d)) (r : ℕ)
    (hρ : NoEmptyRectangle ρ r) (e : V ≃ Fin d × Fin d) (A : Finset V)
    (hA : r ≤ d - (completeRows e A).card) :
    (readyColumns ρ e A).card < r := by
  by_contra h
  have hr : r ≤ (univ \ completeRows e A).card := by
    simpa [card_sdiff_of_subset (subset_univ _)] using hA
  obtain ⟨R, hR, hRc⟩ := exists_subset_card_eq hr
  obtain ⟨C, hC, hCc⟩ := exists_subset_card_eq (Nat.le_of_not_gt h)
  obtain ⟨i, hi, c, hc, hic⟩ := hρ R C hRc hCc
  exact (mem_sdiff.mp (hR hi)).2
    ((mem_readyColumns ρ e A c).1 (hC hc) hic)

variable [Fintype V]

/-- Count completed rows against the ready columns in all layouts. The
selected layout saves an exact square over the uniform column-area bound. -/
theorem threshold_count {m a t : ℕ}
    (ρ : Fin m → Fin d → Finset (Fin d))
    (e : Fin m → V ≃ Fin d × Fin d) (S A B : Finset V)
    (hready : ∀ j, (readyColumns (ρ j) (e j) A).card ≤ a)
    (hrecover : ∀ x ∈ B, x ∉ S → ∃ j, gridHelpers (ρ j) (e j) x ⊆ A)
    (j₀ : Fin m) (R : Finset (Fin d))
    (hR : R ⊆ completeRows (e j₀) B) (hRc : R.card = t) (ht : t + a = d) :
    t * d + a ^ 2 ≤ S.card + m * d * a := by
  let T := cells (e j₀) R univ
  let F := fun j => T ∩ cells (e j) univ (readyColumns (ρ j) (e j) A)
  have hcover : T ⊆ S ∪ univ.biUnion F := by
    intro x hx
    by_cases hs : x ∈ S
    · exact mem_union_left _ hs
    · obtain ⟨j, hj⟩ := hrecover x (cells_subset_of_complete _ _ hR hx) hs
      apply mem_union_right
      exact mem_biUnion.mpr ⟨j, mem_univ _, mem_inter.mpr ⟨hx,
        (mem_cells _ _ _ _).2 ⟨mem_univ _, ready_of_helpers_subset _ _ _ _ hj⟩⟩⟩
  have hcount : t * d ≤ S.card + ∑ j, (F j).card := by
    calc
      t * d = T.card := by simp [T, hRc]
      _ ≤ (S ∪ univ.biUnion F).card := card_le_card hcover
      _ ≤ S.card + (univ.biUnion F).card := card_union_le _ _
      _ ≤ S.card + ∑ j, (F j).card := Nat.add_le_add_left card_biUnion_le _
  have hother (j) : (F j).card ≤ d * a := by
    calc
      (F j).card ≤ (cells (e j) univ (readyColumns (ρ j) (e j) A)).card :=
        card_le_card inter_subset_right
      _ = d * (readyColumns (ρ j) (e j) A).card := by simp
      _ ≤ d * a := Nat.mul_le_mul_left _ (hready j)
  have hown : (F j₀).card ≤ t * a := by
    have heq : F j₀ = cells (e j₀) R (readyColumns (ρ j₀) (e j₀) A) := by
      ext x
      simp [F, T]
    rw [heq, card_cells, hRc]
    exact Nat.mul_le_mul_left _ (hready j₀)
  have hsum : (∑ j, (F j).card) + a ^ 2 ≤ m * (d * a) := by
    have h := sum_le_sum (s := (univ : Finset (Fin m)))
      (f := fun j => (F j).card + if j = j₀ then a ^ 2 else 0)
      (g := fun _ => d * a) (by
        intro j _
        by_cases hj : j = j₀
        · subst j
          simp only [ite_true]
          nlinarith only [hown, congrArg (fun n => n * a) ht]
        · simpa [hj] using hother j)
    simpa [sum_add_distrib] using h
  nlinarith only [hcount, hsum]

/-- The exact rectangle bound, allowing a different incidence relation in
each layout. Only their common empty-rectangle size is used. -/
theorem rectangle_barrier {m r : ℕ} (hm : 0 < m) (hr : 1 ≤ r) (hrd : r ≤ d)
    (ρ : Fin m → Fin d → Finset (Fin d))
    (hρ : ∀ j, NoEmptyRectangle (ρ j) r)
    (e : Fin m → V ≃ Fin d × Fin d) (S : Finset V)
    (W : RecoveryWitness (fun j => gridHelpers (ρ j) (e j)) S) :
    d * d + (r - 1) ^ 2 ≤ S.card + (m + 1) * d * (r - 1) := by
  let a := r - 1
  let t := d - a
  have ha : a ≤ d := by dsimp [a]; omega
  have ht : t + a = d := Nat.sub_add_cancel ha
  suffices hmain : t * d + a ^ 2 ≤ S.card + m * d * a by
    have htd := congrArg (fun n => n * d) ht
    dsimp [a] at hmain htd
    nlinarith only [hmain, htd]
  by_cases hseed : ∃ j, t ≤ (completeRows (e j) S).card
  · obtain ⟨j, hj⟩ := hseed
    obtain ⟨R, hR, hRc⟩ := exists_subset_card_eq hj
    have hS : t * d ≤ S.card := by
      simpa [hRc] using card_le_card (cells_subset_of_complete (e j) S hR)
    have had : a * a ≤ d * a := Nat.mul_le_mul_right _ ha
    have hdm : d ≤ m * d := by
      simpa using Nat.mul_le_mul_right d (show 1 ≤ m by omega)
    have hmd := Nat.mul_le_mul_right a hdm
    nlinarith only [hS, had, hmd]
  · let K := fun n => S ∪ univ.filter (fun x => W.rank x < n)
    have hfull : K (univ.sup W.rank + 1) = univ := by
      apply eq_univ_of_forall
      intro x
      apply mem_union_right
      exact mem_filter.mpr ⟨mem_univ _, Nat.lt_succ_of_le (le_sup (mem_univ x))⟩
    have hex : ∃ n, ∃ j, t ≤ (completeRows (e j) (K n)).card := by
      refine ⟨univ.sup W.rank + 1, ⟨0, hm⟩, ?_⟩
      rw [hfull]
      simpa [completeRows] using (show t ≤ d by omega)
    let n := Nat.find hex
    have hn : ∃ j, t ≤ (completeRows (e j) (K n)).card := Nat.find_spec hex
    have hnpos : 0 < n := by
      by_contra h
      have hnzero : n = 0 := by omega
      apply hseed
      simpa [hnzero, K] using hn
    have hbefore (j) : (completeRows (e j) (K (n - 1))).card < t := by
      have h := Nat.find_min hex (show n - 1 < n by omega)
      exact Nat.lt_of_not_ge (fun hj => h ⟨j, hj⟩)
    have hready (j) : (readyColumns (ρ j) (e j) (K (n - 1))).card ≤ a := by
      have hrows : r ≤ d - (completeRows (e j) (K (n - 1))).card := by
        have h := hbefore j
        dsimp [t, a] at h
        omega
      have h := ready_card_lt (ρ j) r (hρ j) (e j) (K (n - 1)) hrows
      dsimp [a]
      omega
    have hrecover : ∀ x ∈ K n, x ∉ S →
        ∃ j, gridHelpers (ρ j) (e j) x ⊆ K (n - 1) := by
      intro x hx hs
      have hxrank : W.rank x < n := (mem_filter.mp ((mem_union.mp hx).resolve_left hs)).2
      refine ⟨W.copy ⟨x, hs⟩, ?_⟩
      intro y hy
      rcases W.earlier ⟨x, hs⟩ y hy with hys | hyr
      · exact mem_union_left _ hys
      · apply mem_union_right
        change W.rank y < W.rank x at hyr
        exact mem_filter.mpr ⟨mem_univ _, by omega⟩
    obtain ⟨j, hj⟩ := hn
    obtain ⟨R, hR, hRc⟩ := exists_subset_card_eq hj
    exact threshold_count ρ e S (K (n - 1)) (K n) hready hrecover j R hR hRc ht

/-- The previously recorded common-relation target follows without any
additional hypothesis. -/
theorem rectangleBarrierTarget : RectangleBarrierTarget V := by
  intro d m r hm hr hrd ρ hρ e S ⟨W⟩
  exact rectangle_barrier hm hr hrd (fun _ => ρ) (fun _ => hρ) e S W

/-- The corresponding lower bound on an `m`-copy intersection/seed invoice.
This limits that certificate, not the actual capacity of the helper relation. -/
theorem rectangle_invoice_ge {m r : ℕ} (hm : 0 < m) (hr : 1 ≤ r) (hrd : r ≤ d)
    (ρ : Fin m → Fin d → Finset (Fin d))
    (hρ : ∀ j, NoEmptyRectangle (ρ j) r)
    (e : Fin m → V ≃ Fin d × Fin d) (S : Finset V)
    (W : RecoveryWitness (fun j => gridHelpers (ρ j) (e j)) S) :
    (d : ℝ) ^ 2 - (1 + 1 / (m : ℝ)) * d * (r - 1 : ℕ) +
        (r - 1 : ℕ) ^ 2 / (m : ℝ) ≤
      (((m : ℝ) - 1) * (d : ℝ) ^ 2 + S.card) / m := by
  have h := rectangle_barrier hm hr hrd ρ hρ e S W
  have h' : (d : ℝ) * d + (r - 1 : ℕ) ^ 2 ≤
      (S.card : ℝ) + ((m : ℝ) + 1) * d * (r - 1 : ℕ) := by
    exact_mod_cast h
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  apply (le_div_iff₀ hm').2
  calc
    _ = (m : ℝ) * (d : ℝ) ^ 2 - ((m : ℝ) + 1) * d * (r - 1 : ℕ) +
        (r - 1 : ℕ) ^ 2 := by
      field_simp [ne_of_gt hm']
    _ ≤ _ := by nlinarith only [h']

#print axioms rectangle_barrier
#print axioms rectangleBarrierTarget
#print axioms rectangle_invoice_ge

end LeanBacklog.RectangleBarrier
