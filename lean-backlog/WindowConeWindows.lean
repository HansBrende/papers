import WindowGuards
import WindowRows

/-!
# Native dependency cones in a finite-branching window graph

The coarse edges are constructed from actual last work visits. Windows with
too many work-predecessor windows are guarded, and every surviving native
dependency edge maps to one of at most `M+2` reflexive coarse choices.
Consequently a root-exempt free path with at most `D` edges ends in a set
of at most `(M+2)^D` windows. No coarse/native compatibility is assumed.
-/

namespace LeanBacklog.WindowConeWindows

open Finset BoundedNesting MergeDepth WindowGuards WindowRows

variable {k : ℕ}

/-- Distinct earlier windows reached by actual external work predecessors. -/
noncomputable def workWindows (xs : Fin k → ℕ → ℤ) (T h i : ℕ) : Finset ℕ :=
  (externalWork xs T h i).image (· / h)

/-- Only windows that intersect the finite execution may be selected. -/
noncomputable def badWindows (xs : Fin k → ℕ → ℤ) (T h M : ℕ) : Finset ℕ :=
  (range ((T + h - 1) / h)).filter fun i => M < (workWindows xs T h i).card

/-- A guarded window only stays at itself. A good window can stay, follow
the state boundary, or follow an actual work-predecessor window. -/
noncomputable def coarseNext (xs : Fin k → ℕ → ℤ) (T h M i : ℕ) : Finset ℕ :=
  if M < (workWindows xs T h i).card then {i}
  else insert i (insert (i - 1) (workWindows xs T h i))

theorem self_mem_coarseNext (xs : Fin k → ℕ → ℤ) (T h M i : ℕ) :
    i ∈ coarseNext xs T h M i := by
  classical
  unfold coarseNext
  split_ifs <;> simp

theorem card_coarseNext_le (xs : Fin k → ℕ → ℤ) (T h M i : ℕ) :
    (coarseNext xs T h M i).card ≤ M + 2 := by
  classical
  unfold coarseNext
  split_ifs with hi
  · simp
  · have h₁ := card_insert_le i (insert (i - 1) (workWindows xs T h i))
    have h₂ := card_insert_le (i - 1) (workWindows xs T h i)
    omega

theorem time_mem_windowTimes {T h t : ℕ} (hh : 0 < h) (ht : t < T) :
    t ∈ windowTimes T h (t / h) := by
  apply mem_windowTimes.mpr
  refine ⟨?_, ht, ?_⟩
  · simpa only [Nat.mul_comm] using (Nat.mul_div_le t h)
  · have hmod := Nat.mod_lt t hh
    have hdiv := Nat.mod_add_div t h
    nlinarith

theorem windowIndex_eq {T h i t : ℕ} (ht : t ∈ windowTimes T h i) :
    t / h = i :=
  Nat.div_eq_of_lt_le (mem_windowTimes.mp ht).1 (mem_windowTimes.mp ht).2.2

/-- Exact native-to-coarse edge inclusion. The edge's source need not
avoid the cut, so this applies also to a revealed path root. -/
theorem depStep_window_mem_coarseNext {xs : Fin k → ℕ → ℤ} {T h M t u : ℕ}
    (hh : 0 < h) (he : DepStep xs T t u)
    (hfree : u ∉ guards xs T h (badWindows xs T h M)) :
    u / h ∈ coarseNext xs T h M (t / h) := by
  classical
  have htime := depStep_lt he
  have ht := time_mem_windowTimes hh htime.2
  by_cases hbad : M < (workWindows xs T h (t / h)).card
  · have hi : t / h ∈ badWindows xs T h M :=
      mem_filter.mpr ⟨mem_range.mpr (div_lt_windowCount hh htime.2), hbad⟩
    have hu : u ∉ windowGuard xs T h (t / h) :=
      fun hu => hfree (windowGuard_subset_guards xs T h hi hu)
    have hsame := windowIndex_eq (depStep_stays_in_window ht he hu)
    simp only [coarseNext, ite_eq_left hbad, mem_singleton]
    exact hsame
  · rw [coarseNext, ite_eq_right hbad]
    by_cases hsame : u / h = t / h
    · exact mem_insert.mpr (Or.inl hsame)
    have hbefore : u < (t / h) * h := by
      by_contra hn
      have hwin : u ∈ windowTimes T h (t / h) :=
        mem_windowTimes.mpr ⟨by omega, htime.1.trans htime.2,
          htime.1.trans (mem_windowTimes.mp ht).2.2⟩
      exact hsame (windowIndex_eq hwin)
    rcases (blockStep_iff xs T t u).mpr he with ⟨_, hstate | ⟨j, hj⟩⟩
    · have hstep : t / h ≤ u / h + 1 := by
        rw [← hstate, Nat.succ_div]
        split_ifs <;> omega
      have hmono : u / h ≤ t / h := Nat.div_le_div_right htime.1.le
      have hlt : u / h < t / h := by
        rcases lt_or_eq_of_le hmono with hlt | heq
        · exact hlt
        · exact (hsame heq).elim
      have hsucc : u / h + 1 = t / h := le_antisymm (Nat.succ_le_iff.mpr hlt) hstep
      have hprev : u / h = t / h - 1 := by rw [← hsucc, Nat.add_sub_cancel]
      exact mem_insert_of_mem (mem_insert.mpr (Or.inl hprev))
    · exact mem_insert_of_mem (mem_insert_of_mem (mem_image.mpr
        ⟨u, mem_externalWork.mpr ⟨⟨t, ht, j, hj⟩, hbefore⟩, rfl⟩))

/-- A free native path gives an exact-length path in the reflexive coarse
graph. Its length is the number of edges, not the number of vertices. -/
theorem free_path_last_window_mem (xs : Fin k → ℕ → ℤ) (T h M : ℕ)
    (hh : 0 < h) (π : List ℕ) (t : ℕ)
    (hp : IsDepPath xs T (t :: π))
    (hf : LinNet.GFree (guards xs T h (badWindows xs T h M)) (t :: π)) :
    (t :: π).getLastD t / h ∈
      neighborReach (coarseNext xs T h M) π.length (t / h) := by
  induction π generalizing t with
  | nil => simp [neighborReach]
  | cons u π ih =>
    obtain ⟨hu, hf'⟩ := gfree_cons_cons.mp hf
    have he := depStep_window_mem_coarseNext hh hp.1 hu
    rw [LinNet.getLastD_cons_cons]
    exact mem_biUnion.mpr ⟨u / h, he, ih u hp.2 hf'⟩

theorem free_path_last_window_mem_of_length_le (xs : Fin k → ℕ → ℤ) (T h M D : ℕ)
    (hh : 0 < h) (π : List ℕ) (t : ℕ)
    (hp : IsDepPath xs T (t :: π))
    (hf : LinNet.GFree (guards xs T h (badWindows xs T h M)) (t :: π))
    (hD : π.length ≤ D) :
    (t :: π).getLastD t / h ∈ neighborReach (coarseNext xs T h M) D (t / h) :=
  neighborReach_mono _ (self_mem_coarseNext xs T h M) hD _
    (free_path_last_window_mem xs T h M hh π t hp hf)

theorem card_windowReach_le (xs : Fin k → ℕ → ℤ) (T h M D i : ℕ) :
    (neighborReach (coarseNext xs T h M) D i).card ≤ (M + 2) ^ D :=
  card_neighborReach_le _ (card_coarseNext_le xs T h M) D i

#print axioms depStep_window_mem_coarseNext
#print axioms free_path_last_window_mem_of_length_le
#print axioms card_windowReach_le

end LeanBacklog.WindowConeWindows
