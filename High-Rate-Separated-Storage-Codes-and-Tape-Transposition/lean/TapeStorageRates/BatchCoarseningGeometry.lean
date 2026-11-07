import TapeStorageRates.BatchCoarsening

/-!
# Complete block visits give chronological dependency-edge lifts

The final block may be a partial drain. Every earlier batch that touches a
coarse cell must visit all of its physical cells. This keeps a lifted
last-visit chain inside the original edge's two endpoint batches.
-/

namespace TapeStorageRates.BatchCoarsening

open Finset MergeDepth BoundedNesting

set_option autoImplicit false
noncomputable section
open Classical

variable {k : ℕ}

/-- Consecutive visits to one coarse cell give a path through precisely its intervening visits. -/
theorem visits_transGen (ys : Fin k → ℕ → ℤ) (V : ℕ) (h : Fin k)
    (P : ℕ → Prop) : ∀ a b : ℕ, b < a → a < V → ys h a = ys h b →
      (∀ q, b ≤ q → q ≤ a → ys h q = ys h a → P q) →
      Relation.TransGen (fun u v => DepStep ys V u v ∧ P u ∧ P v) a b := by
  intro a
  induction a using Nat.strong_induction_on with
  | h a ih =>
    intro b hba haV he hP
    let F := (range a).filter fun q => ys h q = ys h a
    have hbF : b ∈ F := mem_filter.mpr ⟨mem_range.mpr hba, he.symm⟩
    have hF : F.Nonempty := ⟨b, hbF⟩
    let u := F.max' hF
    have huF : u ∈ F := max'_mem F hF
    have hua : u < a := mem_range.mp (mem_filter.mp huF).1
    have hue : ys h u = ys h a := (mem_filter.mp huF).2
    have hbu : b ≤ u := le_max' F b hbF
    have hstep : DepStep ys V a u := by
      by_cases heq : u + 1 = a
      · exact Or.inl ⟨heq, haV⟩
      · have hhop : IsHop (ys h) V u a := by
          refine ⟨by omega, haV, hue.symm, ?_⟩
          intro q hq hval
          have hqa := (mem_Ioo.mp hq).2
          have hqF : q ∈ F := mem_filter.mpr ⟨mem_range.mpr hqa, hval.trans hue⟩
          have hqu : q ≤ u := le_max' F q hqF
          have := (mem_Ioo.mp hq).1
          omega
        exact Or.inr (mem_image.mpr ⟨(h, u, a), mem_allHops.mpr hhop, rfl⟩)
    have hPu : P u := hP u hbu hua.le hue
    have hPa : P a := hP a hba.le le_rfl rfl
    by_cases hbe : b = u
    · simpa [hbe] using Relation.TransGen.single ⟨hstep, hPa, hPu⟩
    · have hsub := ih u hua b (by omega) (hua.trans haV) (hue.trans he)
        (fun q hbq hqu hq => hP q hbq (hqu.trans hua.le) (hq.trans hue))
      exact Relation.TransGen.head ⟨hstep, hPa, hPu⟩ hsub

/-- A backward spine can be followed while retaining any interval-wide property. -/
theorem spine_transGen (ys : Fin k → ℕ → ℤ) (V : ℕ) (P : ℕ → Prop) :
    ∀ a b : ℕ, b < a → a < V → (∀ q, b ≤ q → q ≤ a → P q) →
      Relation.TransGen (fun u v => DepStep ys V u v ∧ P u ∧ P v) a b := by
  intro a
  induction a using Nat.strong_induction_on with
  | h a ih =>
    intro b hba haV hP
    have ha0 : 0 < a := by omega
    have hstep : DepStep ys V a (a-1) := Or.inl ⟨by omega, haV⟩
    have hPb : P (a-1) := hP _ (by omega) (by omega)
    have hPa : P a := hP _ hba.le le_rfl
    by_cases he : b = a-1
    · simpa [he] using Relation.TransGen.single ⟨hstep, hPa, hPb⟩
    · exact Relation.TransGen.head ⟨hstep, hPa, hPb⟩
        (ih (a-1) (by omega) b (by omega) (by omega)
          (fun q hbq hq => hP q hbq (by omega)))

/-- Geometric data sufficient for the endpoint-batch lifting theorem.
`N` is the final batch index; only that batch may fail full block visitation. -/
structure CompleteBlockCover (xs : Fin k → ℕ → ℤ) (T : ℕ)
    (ys : Fin k → ℕ → ℤ) (V B s N : ℕ) where
  positive : 0 < B
  phi : ℕ → ℕ
  owner : ℕ → ℕ
  phi_lt : ∀ t < T, phi t < V
  phi_mono : ∀ a b, a ≤ b → b < T → phi a ≤ phi b
  owner_mono : Monotone owner
  owns : ∀ t < T, owner (phi t) = t / B
  positions : ∀ h t, t < T → ys h (phi t) = xs h t / (s : ℤ)
  batch_bound : ∀ t < T, t / B ≤ N
  full : ∀ h q c, q < V → owner q < N → c / (s : ℤ) = ys h q →
    ∃ t < T, t / B = owner q ∧ xs h t = c

namespace CompleteBlockCover

variable {xs ys : Fin k → ℕ → ℤ} {T V B s N : ℕ}
variable (C : CompleteBlockCover xs T ys V B s N)

private theorem owner_between {a b q : ℕ} (ha : a < T) (hb : b < T)
    (hlo : C.phi b ≤ q) (hhi : q ≤ C.phi a) :
    b / B ≤ C.owner q ∧ C.owner q ≤ a / B := by
  constructor
  · rw [← C.owns b hb]
    exact C.owner_mono hlo
  · rw [← C.owns a ha]
    exact C.owner_mono hhi

/-- A physical last-visit edge admits no intermediate coarse visit in a third batch. -/
theorem owner_of_visit {a b q : ℕ} {h : Fin k}
    (hh : IsHop (xs h) T b a)
    (hlo : C.phi b ≤ q) (hhi : q ≤ C.phi a)
    (he : ys h q = ys h (C.phi a)) :
    C.owner q = a / B ∨ C.owner q = b / B := by
  have ha : a < T := hh.2.1
  have hba : b < a := by have := hh.1; omega
  have hb : b < T := hba.trans ha
  obtain ⟨hqb, hqa⟩ := C.owner_between ha hb hlo hhi
  by_contra! hn
  have hbq : b / B < C.owner q := by omega
  have hqa' : C.owner q < a / B := by omega
  obtain ⟨t, htT, howner, hcell⟩ := C.full h q (xs h a)
    (hhi.trans_lt (C.phi_lt a ha)) (hqa'.trans_le (C.batch_bound a ha))
    (by rw [he, C.positions h a ha])
  have hbt : b < t := by
    by_contra! h
    have := Nat.div_le_div_right (c := B) h
    omega
  have hta : t < a := by
    by_contra! h
    have := Nat.div_le_div_right (c := B) h
    omega
  exact hh.2.2.2 t (mem_Ioo.mpr ⟨hbt, hta⟩) (hcell.trans hh.2.2.1)

/-- Full visits in intermediate batches supply the exact edge-lifting interface. -/
def toCoarsening : Coarsening xs T ys V B where
  positive := C.positive
  phi := C.phi
  owner := C.owner
  owns := C.owns
  edge_lift := by
    intro a b hab
    obtain ⟨hba, haT⟩ := depStep_lt hab
    have hbT := hba.trans haT
    have hp := C.phi_mono b a hba.le haT
    by_cases he : C.phi a = C.phi b
    · exact Or.inl he
    right
    have hlt : C.phi b < C.phi a := by omega
    let P := fun q => C.owner q = a / B ∨ C.owner q = b / B
    change Relation.TransGen (fun u v => DepStep ys V u v ∧ P u ∧ P v) _ _
    rcases hab with ⟨hstate, _⟩ | hhop
    · apply spine_transGen ys V P _ _ hlt (C.phi_lt a haT)
      intro q hlo hhi
      obtain ⟨hqb, hqa⟩ := C.owner_between haT hbT hlo hhi
      have hdiv : a / B ≤ b / B + 1 := by
        rw [← hstate, Nat.succ_div]
        split_ifs <;> omega
      dsimp [P]
      omega
    · obtain ⟨e, hmemhop, heq⟩ := mem_image.mp hhop
      obtain ⟨h, u, v⟩ := e
      simp only [Prod.mk.injEq] at heq
      have hu : u = b := heq.1
      have hv : v = a := heq.2
      subst u
      subst v
      have hh := mem_allHops.mp hmemhop
      apply visits_transGen ys V h P _ _ hlt (C.phi_lt a haT)
      · rw [C.positions h a haT, C.positions h b hbT, hh.2.2.1]
      · exact fun q hlo hhi hq => C.owner_of_visit hh hlo hhi hq

end CompleteBlockCover
end
end TapeStorageRates.BatchCoarsening
