import BoundedStackDepth.Display

/-!
# The display above a group is a function of the view

Fix a group `d`. The *candidates* at `d` are the entries with `bot e ≤ d < top e`. Every other entry
with a top above `d` is *visible*: its whole window lies above `d`. The *view* above `d` is
* `aboveVals`: the seeds above `d` together with the tops of the candidates, as one set, and
* `visPairs`: the (nonempty) windows of the unbroken visible entries.

`mem_dispVals_iff_reach`: if every candidate at `d` is displayed, a value above `d` is displayed iff it
is reachable from `aboveVals` through windows in `visPairs` (`Reach`). Hence (`shown_above_eq`) two
configurations with the same view, in which all candidates at `d` are displayed, show the same groups
above `d`. Candidates are displayed when their window starts at `0`, or when they are unbroken and `d`
is a seed (`disp_of_cand`). This is part (ii) of the exposure proposition; part (iii) counts the bit
vectors that break a candidate (`card_some_broken_le`).
-/

namespace BoundedStackDepth

open Finset

variable {ι : Type*} [Fintype ι]

/-- The values reachable from a base set `X` through windows: a window `[b, c]` containing a
reachable value makes `c` reachable. -/
inductive Reach (X : Finset ℕ) (V : Finset (ℕ × ℕ)) : ℕ → Prop
  | base {y : ℕ} : y ∈ X → Reach X V y
  | step {y b c : ℕ} : (b, c) ∈ V → Reach X V y → b ≤ y → y ≤ c → Reach X V c

open Classical in
/-- The seeds above `d` and the tops of the candidates at `d`. -/
noncomputable def aboveVals (bot top : ι → ℕ) (seeds : Finset ℕ) (d : ℕ) : Finset ℕ :=
  seeds.filter (d < ·) ∪ (univ.filter (fun e => bot e ≤ d ∧ d < top e)).image top

open Classical in
/-- The nonempty windows of the unbroken entries whose window lies above `d`. -/
noncomputable def visPairs (bot top : ι → ℕ) (unbroken : ι → Prop) (d : ℕ) : Finset (ℕ × ℕ) :=
  (univ.filter (fun e => d < bot e ∧ bot e ≤ top e ∧ unbroken e)).image (fun e => (bot e, top e))

variable {bot top : ι → ℕ} {unbroken : ι → Prop} {seeds : Finset ℕ} {d : ℕ}

omit [Fintype ι] in
/-- A candidate at `d` is displayed if its window starts at `0`, or if it is unbroken and `d` is a seed. -/
theorem disp_of_cand {e : ι} (hb : bot e ≤ d) (ht : d < top e)
    (h : bot e = 0 ∨ (unbroken e ∧ d ∈ seeds)) : Disp bot top unbroken seeds e := by
  rcases h with h0 | ⟨hu, hd⟩
  · exact Disp.zero h0
  · exact Disp.seed d hd hu hb ht.le

/-- **The display above `d` from the view.** If every candidate at `d` is displayed, a value above `d`
is displayed iff it is reachable from `aboveVals` through `visPairs`. -/
theorem mem_dispVals_iff_reach
    (hc : ∀ e, bot e ≤ d → d < top e → Disp bot top unbroken seeds e) {y : ℕ} (hy : d < y) :
    y ∈ dispVals bot top unbroken seeds ↔
      Reach (aboveVals bot top seeds d) (visPairs bot top unbroken d) y := by
  classical
  have hcandX : ∀ e, bot e ≤ d → d < top e → top e ∈ aboveVals bot top seeds d := fun e hb ht =>
    mem_union_right _ (mem_image_of_mem _ (mem_filter.mpr ⟨mem_univ _, hb, ht⟩))
  have hvis : ∀ e, d < bot e → bot e ≤ top e → unbroken e →
      (bot e, top e) ∈ visPairs bot top unbroken d :=
    fun e hb hbt hu => mem_image_of_mem _ (mem_filter.mpr ⟨mem_univ _, hb, hbt, hu⟩)
  -- Displayed entries with a top above `d` have reachable tops.
  have key : ∀ e, Disp bot top unbroken seeds e → d < top e →
      Reach (aboveVals bot top seeds d) (visPairs bot top unbroken d) (top e) := by
    intro e he
    induction he with
    | @zero e h0 => exact fun ht => Reach.base (hcandX e (by omega) ht)
    | @seed e s hs hu hb hst =>
      intro ht
      by_cases hbd : bot e ≤ d
      · exact Reach.base (hcandX e hbd ht)
      · push Not at hbd
        exact Reach.step (hvis e hbd (hb.trans hst) hu)
          (Reach.base (mem_union_left _ (mem_filter.mpr ⟨hs, by omega⟩))) hb hst
    | @step e e' _ hu hb hle ih =>
      intro ht
      by_cases hbd : bot e ≤ d
      · exact Reach.base (hcandX e hbd ht)
      · push Not at hbd
        exact Reach.step (hvis e hbd (hb.trans hle) hu) (ih (by omega)) hb hle
  constructor
  · intro hmem
    rcases mem_union.mp hmem with hs | ht
    · exact Reach.base (mem_union_left _ (mem_filter.mpr ⟨hs, hy⟩))
    · obtain ⟨e, he, rfl⟩ := mem_image.mp ht
      exact key e (mem_filter.mp he).2 hy
  · intro hr
    clear hy
    induction hr with
    | base hX =>
      rcases mem_union.mp hX with hs | ht
      · exact mem_union_left _ (mem_filter.mp hs).1
      · obtain ⟨e, he, rfl⟩ := mem_image.mp ht
        obtain ⟨-, hb, ht⟩ := mem_filter.mp he
        exact mem_union_right _ (mem_image_of_mem _ (mem_filter.mpr ⟨mem_univ _, hc e hb ht⟩))
    | @step y b c hbc _ hby hyc ih =>
      obtain ⟨e, he, hbe⟩ := mem_image.mp hbc
      obtain ⟨-, hbd, -, hu⟩ := mem_filter.mp he
      simp only [Prod.mk.injEq] at hbe
      obtain ⟨rfl, rfl⟩ := hbe
      refine mem_union_right _ (mem_image_of_mem _ (mem_filter.mpr ⟨mem_univ _, ?_⟩))
      rcases mem_union.mp ih with hs | ht
      · exact Disp.seed y hs hu hby hyc
      · obtain ⟨e', he', rfl⟩ := mem_image.mp ht
        exact Disp.step (mem_filter.mp he').2 hu hby hyc

/-- **Part (ii) of exposure.** Two configurations with the same view above `d`, in which every
candidate at `d` is displayed, show the same groups above `d`. -/
theorem shown_above_eq {bot' top' : ι → ℕ} {unbroken' : ι → Prop} {seeds' : Finset ℕ}
    (hc : ∀ e, bot e ≤ d → d < top e → Disp bot top unbroken seeds e)
    (hc' : ∀ e, bot' e ≤ d → d < top' e → Disp bot' top' unbroken' seeds' e)
    (hX : aboveVals bot top seeds d = aboveVals bot' top' seeds' d)
    (hV : visPairs bot top unbroken d = visPairs bot' top' unbroken' d) :
    (shownSet bot top unbroken seeds).filter (d < ·) =
      (shownSet bot' top' unbroken' seeds').filter (d < ·) := by
  ext y
  simp only [mem_filter, shownSet, mem_insert]
  constructor
  · rintro ⟨h, hy⟩
    refine ⟨Or.inr ?_, hy⟩
    have hm : y ∈ dispVals bot top unbroken seeds := h.resolve_left (by omega)
    rw [mem_dispVals_iff_reach hc' hy, ← hX, ← hV]
    exact (mem_dispVals_iff_reach hc hy).mp hm
  · rintro ⟨h, hy⟩
    refine ⟨Or.inr ?_, hy⟩
    have hm : y ∈ dispVals bot' top' unbroken' seeds' := h.resolve_left (by omega)
    rw [mem_dispVals_iff_reach hc hy, hX, hV]
    exact (mem_dispVals_iff_reach hc' hy).mp hm

/-! ### Part (iii): few bit vectors break a candidate -/

/-- At most `|C| Q ^ (|ι| - 1)` bit vectors break some entry of a set `C` (bits `ξ e = 0`). -/
theorem card_some_broken_le [DecidableEq ι] {Q : ℕ} [NeZero Q] (C : Finset ι) :
    (univ.filter (fun ξ : ι → Fin Q => ∃ e ∈ C, ξ e = 0)).card ≤ C.card * Q ^ (Fintype.card ι - 1) := by
  calc (univ.filter (fun ξ : ι → Fin Q => ∃ e ∈ C, ξ e = 0)).card
      ≤ (C.biUnion fun e => univ.filter (fun ξ : ι → Fin Q => ξ e = 0)).card := by
        refine card_le_card fun ξ hξ => ?_
        obtain ⟨e, he, h0⟩ := (mem_filter.mp hξ).2
        exact mem_biUnion.mpr ⟨e, he, mem_filter.mpr ⟨mem_univ _, h0⟩⟩
    _ ≤ ∑ e ∈ C, (univ.filter (fun ξ : ι → Fin Q => ξ e = 0)).card := card_biUnion_le
    _ ≤ ∑ _e ∈ C, Q ^ (Fintype.card ι - 1) := sum_le_sum fun e _ => card_bit_zero_le e
    _ = C.card * Q ^ (Fintype.card ι - 1) := by rw [sum_const, smul_eq_mul]
where
  /-- The bit vectors with `ξ e = 0` are determined by the other coordinates. -/
  card_bit_zero_le (e : ι) :
      (univ.filter (fun ξ : ι → Fin Q => ξ e = 0)).card ≤ Q ^ (Fintype.card ι - 1) := by
    have hinj : Set.InjOn (fun ξ : ι → Fin Q => fun e' : {e' // e' ≠ e} => ξ e')
        (univ.filter (fun ξ : ι → Fin Q => ξ e = 0) : Set (ι → Fin Q)) := by
      intro ξ hξ ξ' hξ' h
      funext e'
      by_cases he : e' = e
      · subst he
        rw [(mem_filter.mp (Finset.mem_coe.mp hξ)).2, (mem_filter.mp (Finset.mem_coe.mp hξ')).2]
      · exact congrFun h ⟨e', he⟩
    calc (univ.filter (fun ξ : ι → Fin Q => ξ e = 0)).card
        ≤ (univ : Finset ({e' // e' ≠ e} → Fin Q)).card :=
          card_le_card_of_injOn _ (fun _ _ => mem_coe.mpr (mem_univ _)) hinj
      _ = Q ^ (Fintype.card ι - 1) := by
          rw [card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_subtype_compl,
            Fintype.card_subtype_eq]

end BoundedStackDepth
