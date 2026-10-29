import HalfRate.Positional

/-!
# Nested-supply positional certificates and first-appearance invariants

This file generalizes `HalfRate.relCharged_of_cosupply` to arbitrary nested supplying records
and proves the converse positional extraction lemmas for `HalfRate.RelCharged` and
`HalfRate.PieceCert`:

* `relCharged_of_nested` and `relCharged_iff_nested`: exact positional characterization of
  `RelCharged N U P b par W ∅ (fun _ => ∅) l` via nested supply
  `P (b l[j]) ⊆ rev ∅ l j' ∪ P (b l[j'])` whenever `j < j'` share an outside parent.
* `disjoint_nested_iff`: when the records `P` are pairwise disjoint, nested supply at `(j, j')`
  is equivalent to co-supply `b l[j] = b l[j']` or full revelation `P (b l[j]) ⊆ rev S l j'`.
* `PieceCert.mem_supply_of_idxOf_lt`: if `Disjoint U H`, `u, v ∈ H`, `v ∈ N u`, and `u` appears
  strictly before `v` in `c.l`, then `v ∈ c.P (c.b u)` and `c.b u = c.a v`.
* `PieceCert.digon_ne`: every reciprocated pair (`u ∈ N v` and `v ∈ N u`) inside a piece `H`
  disjoint from `U` receives distinct own records `c.a u ≠ c.a v`.
-/

namespace DirectedReciprocity

open Finset HalfRate

section Positional

variable {V : Type*} [DecidableEq V] {ι : Type*}

theorem rev_mono_idx (S : Finset V) (l : List V) {j j' : ℕ} (h : j ≤ j') :
    rev S l j ⊆ rev S l j' := by
  intro x hx
  simp only [rev, mem_union, List.mem_toFinset] at hx ⊢
  rcases hx with hxS | hxl
  · exact Or.inl hxS
  · have htk : l.take j = (l.take j').take j := by rw [List.take_take, Nat.min_eq_left h]
    rw [htk] at hxl
    exact Or.inr (List.mem_of_mem_take hxl)

theorem getElem_mem_rev (S : Finset V) (l : List V) {j j' : ℕ} (hj : j < j')
    (hj' : j' ≤ l.length) : l[j]'(lt_of_lt_of_le hj hj') ∈ rev S l j' := by
  apply mem_union_right
  rw [List.mem_toFinset]
  have hlen : j < (l.take j').length := by simp [Nat.min_eq_left hj', hj]
  have heq : (l.take j')[j]'hlen = l[j]'(lt_of_lt_of_le hj hj') := List.getElem_take
  rw [← heq]
  exact List.getElem_mem hlen

/-- Positional step conditions plus nested supply give `RelCharged`. -/
theorem relCharged_of_nested (N : V → Finset V) (U : Finset V) (P : ι → Finset V)
    (b : V → ι) (par : V → Option V) (W : Finset V) :
    ∀ (l : List V) (S : Finset V) (L : V → Finset V),
      (∀ j (hj : j < l.length), par l[j] = none →
          N l[j] ⊆ U ∪ (rev S l j ∪ P (b l[j]))) →
      (∀ j (hj : j < l.length) w, par l[j] = some w →
          w ∈ W ∧ N l[j] ⊆ U ∪ insert w (rev S l j ∪ P (b l[j])) ∧
            L w ⊆ rev S l j ∪ P (b l[j])) →
      (∀ j j' (hj : j < j') (hj' : j' < l.length) w, par l[j] = some w →
          par l[j'] = some w → P (b l[j]) ⊆ rev S l j' ∪ P (b l[j'])) →
      RelCharged N U P b par W S L l := by
  intro l
  induction l with
  | nil => intro _ _ _ _ _; trivial
  | cons v l ih =>
    intro S L hnone hsome hnest
    have h0n := hnone 0 (by simp)
    have h0s := hsome 0 (by simp)
    simp only [List.getElem_cons_zero, rev_zero] at h0n h0s
    have tnone : ∀ j (hj : j < l.length), par l[j] = none →
        N l[j] ⊆ U ∪ (rev (insert v S) l j ∪ P (b l[j])) := by
      intro j hj hp
      have := hnone (j + 1) (by simp; omega) (by simpa using hp)
      simpa [rev_cons_succ] using this
    have tnest : ∀ j j' (hj : j < j') (hj' : j' < l.length) w, par l[j] = some w →
        par l[j'] = some w → P (b l[j]) ⊆ rev (insert v S) l j' ∪ P (b l[j']) := by
      intro j j' hjj hj' w h1 h2
      have := hnest (j + 1) (j' + 1) (by omega) (by simp; omega) w (by simpa using h1)
        (by simpa using h2)
      simpa [rev_cons_succ] using this
    cases hp : par v with
    | none =>
      simp only [RelCharged, hp]
      refine ⟨h0n hp, ih (insert v S) L tnone ?_ tnest⟩
      intro j hj w hw
      have := hsome (j + 1) (by simp; omega) w (by simpa using hw)
      simpa [rev_cons_succ] using this
    | some w =>
      obtain ⟨hwW, hN, hLw⟩ := h0s w hp
      simp only [RelCharged, hp]
      refine ⟨hwW, hN, hLw, ih (insert v S) _ tnone ?_ tnest⟩
      intro j hj w' hw'
      have h1 := hsome (j + 1) (by simp; omega) w' (by simpa using hw')
      simp only [List.getElem_cons_succ, rev_cons_succ] at h1
      obtain ⟨hw'W, hN', hL'⟩ := h1
      refine ⟨hw'W, hN', ?_⟩
      by_cases hww : w' = w
      · subst hww
        rw [Function.update_self]
        have hsub : P (b v) ⊆ rev (insert v S) l j ∪ P (b l[j]) := by
          have := hnest 0 (j + 1) (by omega) (by simp; omega) w' (by simpa using hp)
            (by simpa using hw')
          simpa [rev_cons_succ] using this
        intro x hx
        rcases mem_insert.mp hx with rfl | hx
        · exact mem_union_left _ (by simp [rev])
        · rcases mem_union.mp hx with hxS | hxP
          · exact mem_union_left _ (by simp [rev] at hxS ⊢; tauto)
          · exact hsub hxP
      · rw [Function.update_of_ne hww]; exact hL'

/-- When records are pairwise disjoint, nested supply at `(j, j')` holds if and only if either
the two steps use the same supplying record (`co-supply`) or the earlier supplying record has
been completely revealed before step `j'`. -/
theorem disjoint_nested_iff [DecidableEq ι] {P : ι → Finset V}
    (disj : ∀ i i', i ≠ i' → Disjoint (P i) (P i'))
    {S : Finset V} {l : List V} {b : V → ι} {j j' : ℕ} (hj : j < l.length) (hj' : j' < l.length) :
    P (b l[j]) ⊆ rev S l j' ∪ P (b l[j']) ↔
      (b l[j] = b l[j'] ∨ P (b l[j]) ⊆ rev S l j') := by
  constructor
  · intro hsub
    by_cases h : b l[j] = b l[j']
    · exact Or.inl h
    · right
      intro x hx
      rcases mem_union.mp (hsub hx) with hxR | hxP
      · exact hxR
      · exact absurd hxP (disjoint_left.mp (disj _ _ h) hx)
  · rintro (heq | hrev)
    · rw [heq]; exact subset_union_right
    · exact hrev.trans subset_union_left

theorem relCharged_step_none {N : V → Finset V} {U : Finset V} {P : ι → Finset V}
    {b : V → ι} {par : V → Option V} {W : Finset V} :
    ∀ {l : List V} {S : Finset V} {L : V → Finset V},
      RelCharged N U P b par W S L l →
      ∀ j (hj : j < l.length), par l[j] = none →
        N l[j] ⊆ U ∪ (rev S l j ∪ P (b l[j]))
  | [], _, _, _, j, hj, _ => absurd hj (by simp)
  | v :: l, S, L, hrc, 0, _, hp => by
      simp only [List.getElem_cons_zero] at hp ⊢
      simp only [RelCharged, hp, rev_zero] at hrc ⊢
      exact hrc.1
  | v :: l, S, L, hrc, j + 1, hj, hp => by
      simp only [List.getElem_cons_succ, rev_cons_succ] at hp ⊢
      cases hpv : par v with
      | none =>
        simp only [RelCharged, hpv] at hrc
        exact relCharged_step_none hrc.2 j (by simp at hj; omega) hp
      | some w =>
        simp only [RelCharged, hpv] at hrc
        exact relCharged_step_none hrc.2.2.2 j (by simp at hj; omega) hp

theorem relCharged_step_some {N : V → Finset V} {U : Finset V} {P : ι → Finset V}
    {b : V → ι} {par : V → Option V} {W : Finset V} :
    ∀ {l : List V} {S : Finset V} {L : V → Finset V},
      RelCharged N U P b par W S L l →
      ∀ j (hj : j < l.length) w, par l[j] = some w →
        w ∈ W ∧ N l[j] ⊆ U ∪ insert w (rev S l j ∪ P (b l[j])) ∧
          L w ⊆ rev S l j ∪ P (b l[j])
  | [], _, _, _, j, hj, _, _ => absurd hj (by simp)
  | v :: l, S, L, hrc, 0, _, w, hp => by
      simp only [List.getElem_cons_zero] at hp ⊢
      simp only [RelCharged, hp, rev_zero] at hrc ⊢
      exact ⟨hrc.1, hrc.2.1, hrc.2.2.1⟩
  | v :: l, S, L, hrc, j + 1, hj, w, hp => by
      simp only [List.getElem_cons_succ, rev_cons_succ] at hp ⊢
      have hj' : j < l.length := by simp at hj; omega
      cases hpv : par v with
      | none =>
        simp only [RelCharged, hpv] at hrc
        exact relCharged_step_some hrc.2 j hj' w hp
      | some w₀ =>
        simp only [RelCharged, hpv] at hrc
        obtain ⟨hwW, hN, hLw⟩ := relCharged_step_some hrc.2.2.2 j hj' w hp
        refine ⟨hwW, hN, ?_⟩
        by_cases hww : w = w₀
        · subst hww
          rw [Function.update_self] at hLw
          exact (hrc.2.2.1.trans (subset_insert _ _)).trans hLw
        · rwa [Function.update_of_ne hww] at hLw

theorem relCharged_step_nested {N : V → Finset V} {U : Finset V} {P : ι → Finset V}
    {b : V → ι} {par : V → Option V} {W : Finset V} :
    ∀ {l : List V} {S : Finset V} {L : V → Finset V},
      RelCharged N U P b par W S L l →
      ∀ j j' (hj : j < j') (hj' : j' < l.length) w,
        par l[j] = some w → par l[j'] = some w →
        insert l[j] (rev S l j ∪ P (b l[j])) ⊆ rev S l j' ∪ P (b l[j'])
  | [], _, _, _, _, _, _, hj', _, _, _ => absurd hj' (by simp)
  | v :: l, S, L, hrc, 0, j' + 1, _, hj', w, hp, hp' => by
      simp only [List.getElem_cons_zero, List.getElem_cons_succ, rev_zero, rev_cons_succ] at hp hp' ⊢
      simp only [RelCharged, hp] at hrc
      have hj'' : j' < l.length := by simp at hj'; omega
      obtain ⟨_, _, hLw⟩ := relCharged_step_some hrc.2.2.2 j' hj'' w hp'
      rwa [Function.update_self] at hLw
  | v :: l, S, L, hrc, j + 1, j' + 1, hjj, hj', w, hp, hp' => by
      simp only [List.getElem_cons_succ, rev_cons_succ] at hp hp' ⊢
      have hj'' : j' < l.length := by simp at hj'; omega
      cases hpv : par v with
      | none =>
        simp only [RelCharged, hpv] at hrc
        exact relCharged_step_nested hrc.2 j j' (by omega) hj'' w hp hp'
      | some w₀ =>
        simp only [RelCharged, hpv] at hrc
        exact relCharged_step_nested hrc.2.2.2 j j' (by omega) hj'' w hp hp'

/-- Exact positional equivalence for `RelCharged` from empty initial state. -/
theorem relCharged_iff_nested (N : V → Finset V) (U : Finset V) (P : ι → Finset V)
    (b : V → ι) (par : V → Option V) (W : Finset V) (l : List V) :
    RelCharged N U P b par W ∅ (fun _ => ∅) l ↔
      (∀ j (hj : j < l.length), par l[j] = none →
          N l[j] ⊆ U ∪ (rev ∅ l j ∪ P (b l[j]))) ∧
      (∀ j (hj : j < l.length) w, par l[j] = some w →
          w ∈ W ∧ N l[j] ⊆ U ∪ insert w (rev ∅ l j ∪ P (b l[j]))) ∧
      (∀ j j' (hj : j < j') (hj' : j' < l.length) w, par l[j] = some w →
          par l[j'] = some w → P (b l[j]) ⊆ rev ∅ l j' ∪ P (b l[j'])) := by
  constructor
  · intro hrc
    refine ⟨fun j hj hp => relCharged_step_none hrc j hj hp,
      fun j hj w hp => ?_, fun j j' hjj hj' w hp hp' => ?_⟩
    · obtain ⟨hwW, hN, _⟩ := relCharged_step_some hrc j hj w hp
      exact ⟨hwW, hN⟩
    · have hsub := relCharged_step_nested hrc j j' hjj hj' w hp hp'
      exact (subset_union_right.trans (subset_insert _ _)).trans hsub
  · rintro ⟨hnone, hsome, hnest⟩
    refine relCharged_of_nested N U P b par W l ∅ (fun _ => ∅) hnone ?_ hnest
    intro j hj w hp
    obtain ⟨hwW, hN⟩ := hsome j hj w hp
    exact ⟨hwW, hN, empty_subset _⟩

end Positional

section FirstAppearance

variable {V : Type*} [DecidableEq V] [Fintype V]

omit [Fintype V] in
theorem not_mem_rev_empty_of_lt_idxOf {l : List V} {v : V} {j : ℕ} (hj : j < l.idxOf v) :
    v ∉ rev ∅ l j := by
  induction l generalizing j with
  | nil => simp [rev]
  | cons a l ih =>
    cases j with
    | zero => simp [rev]
    | succ j =>
      rw [rev_cons_succ, insert_empty_eq]
      have hne : a ≠ v := by
        rintro rfl
        simp at hj
      have hj' : j < l.idxOf v := by
        simp [hne] at hj
        omega
      intro hv
      simp only [rev, mem_union, mem_singleton, List.mem_toFinset] at hv
      rcases hv with rfl | hvl
      · exact hne rfl
      · exact ih hj' (by simp [rev, hvl])

/-- If `u` and `v` lie in a certified piece `H` disjoint from context `U`, `v ∈ N u`, and `u`
first appears strictly before `v` in `c.l`, then `v` must be supplied by `c.b u`, forcing
`c.b u = c.a v`. -/
theorem PieceCert.mem_supply_of_idxOf_lt {N : V → Finset V} {U H : Finset V}
    (c : PieceCert N U H) (hUH : Disjoint U H) {u v : V} (huH : u ∈ H) (hvH : v ∈ H)
    (hvu : v ∈ N u) (hlt : c.l.idxOf u < c.l.idxOf v) :
    v ∈ c.P (c.b u) ∧ c.b u = c.a v := by
  have hul : u ∈ c.l := List.mem_toFinset.mp (c.hl.symm ▸ huH)
  have hvl : v ∈ c.l := List.mem_toFinset.mp (c.hl.symm ▸ hvH)
  set ju := c.l.idxOf u
  have hju : ju < c.l.length := List.idxOf_lt_length_of_mem hul
  have hequ : c.l[ju]'hju = u := List.getElem_idxOf hju
  have hvnotU : v ∉ U := disjoint_right.mp hUH hvH
  have hvnotRev : v ∉ rev ∅ c.l ju := not_mem_rev_empty_of_lt_idxOf hlt
  have hvP : v ∈ c.P (c.b u) := by
    cases hp : c.par u with
    | none =>
      have hp' : c.par (c.l[ju]'hju) = none := by rwa [hequ]
      have hsub := relCharged_step_none c.charged ju hju hp'
      rw [hequ] at hsub
      rcases mem_union.mp (hsub hvu) with hvU | hvRP
      · exact absurd hvU hvnotU
      · exact (mem_union.mp hvRP).resolve_left hvnotRev
    | some w =>
      have hp' : c.par (c.l[ju]'hju) = some w := by rwa [hequ]
      obtain ⟨hwW, hsub, _⟩ := relCharged_step_some c.charged ju hju w hp'
      rw [hequ] at hsub
      have hvw : v ≠ w := by
        rintro rfl
        exact (mem_sdiff.mp hwW).2 (mem_union_right _ hvH)
      rcases mem_union.mp (hsub hvu) with hvU | hvIRP
      · exact absurd hvU hvnotU
      · rcases mem_insert.mp hvIRP with rfl | hvRP
        · exact absurd rfl hvw
        · exact (mem_union.mp hvRP).resolve_left hvnotRev
  have hvA : v ∈ c.P (c.a v) := c.own v hvl
  have hba : c.b u = c.a v := by
    by_contra hne
    exact disjoint_left.mp (c.disj _ _ hne) hvP hvA
  exact ⟨hvP, hba⟩

/-- **Digon proper-coloring invariant.** Any two distinct vertices `u, v ∈ H` linked by a digon
(`u ∈ N v` and `v ∈ N u`) inside a certified piece `H` disjoint from `U` belong to distinct
own records (`c.a u ≠ c.a v`). -/
theorem PieceCert.digon_ne {N : V → Finset V} {U H : Finset V}
    (c : PieceCert N U H) (hUH : Disjoint U H) {u v : V} (huH : u ∈ H) (hvH : v ∈ H)
    (huv : u ≠ v) (huvN : u ∈ N v) (hvuN : v ∈ N u) :
    c.a u ≠ c.a v := by
  have hul : u ∈ c.l := List.mem_toFinset.mp (c.hl.symm ▸ huH)
  have hvl : v ∈ c.l := List.mem_toFinset.mp (c.hl.symm ▸ hvH)
  have hidx_ne : c.l.idxOf u ≠ c.l.idxOf v := by
    intro heq
    have hju : c.l.idxOf u < c.l.length := List.idxOf_lt_length_of_mem hul
    have hjv : c.l.idxOf v < c.l.length := List.idxOf_lt_length_of_mem hvl
    have : u = v := by
      calc u = c.l[c.l.idxOf u]'hju := (List.getElem_idxOf hju).symm
        _ = c.l[c.l.idxOf v]'hjv := by congr 1
        _ = v := List.getElem_idxOf hjv
    exact huv this
  rcases lt_trichotomy (c.l.idxOf u) (c.l.idxOf v) with hlt | heq | hgt
  · obtain ⟨_, hba⟩ := PieceCert.mem_supply_of_idxOf_lt c hUH huH hvH hvuN hlt
    rw [← hba]
    exact c.ab u hul
  · exact absurd heq hidx_ne
  · obtain ⟨_, hba⟩ := PieceCert.mem_supply_of_idxOf_lt c hUH hvH huH huvN hgt
    intro haeq
    exact c.ab v hvl (haeq.symm.trans hba.symm)

end FirstAppearance

end DirectedReciprocity
