import DirectedReciprocity.PositionalNest
import HalfRate.N3

/-!
# Stride-`s` digon cycle cores (`Proposition CS`)

Consider a bidirected cycle `C_{s k}` (`k ≥ 1`) whose vertices `i ∈ Fin (s * k)` additionally
have outside recovery parent `w_{i mod s}` (`w : Fin s → V` outside `U ∪ H`):

* `stride3_no_pieceCert`: for `s = 3` and every `k ≥ 1`, `C_{3 k}` admits **no** `PieceCert`
  over any number of records `m ≥ 1` and any nested-supply schedule (`RelCharged`), even if
  only `f (i ± 1) ∈ N (f i)` and `w (i % 3) ∈ N (f i)` are assumed.
* `strideEven_pieceCert`: for even `s ≥ 4` and every `k ≥ 1`, `strideCore s k` admits a
  co-supplied `2`-record `PieceCert` (`m = 2`).
* `strideGe4_pieceCert`: for every `s ≥ 4` (in particular odd `s ≥ 5`) and `k ≥ 1`, pulling back
  `HalfRate.ccol s` modulo `s` gives an explicit co-supplied `3`-record `PieceCert` (`m = 3`).
* `strideCore_pieceCert_iff`: for `s ≥ 3` and `k ≥ 1`, `strideCore s k` is a certified piece if
  and only if `4 ≤ s`.
-/

namespace DirectedReciprocity

open Finset HalfRate

section Stride3Impossibility

variable {V : Type*} [DecidableEq V] [Fintype V]

private theorem idx_mod3 {k : ℕ} (hk : 0 < 3 * k) (n : ℕ) :
    (idx hk n).val % 3 = n % 3 := by
  simp only [idx_val]
  exact Nat.mod_mod_of_dvd n ⟨k, rfl⟩

private theorem idx_pred_succ {L : ℕ} (hL : 2 ≤ L) (i : Fin L) :
    idx (g := L) (by omega) ((idx (g := L) (by omega) (i.val + 1)).val + L - 1) = i := by
  have hi := i.isLt
  apply Fin.ext
  simp only [idx_val]
  rcases Nat.lt_or_ge (i.val + 1) L with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt, show i.val + 1 + L - 1 = L + i.val by omega,
      Nat.add_mod_left, Nat.mod_eq_of_lt hi]
  · have heq : i.val + 1 = L := by omega
    rw [heq, Nat.mod_self, show 0 + L - 1 = i.val by omega, Nat.mod_eq_of_lt hi]

private theorem idx_succ_pred {L : ℕ} (hL : 2 ≤ L) (i : Fin L) :
    idx (g := L) (by omega) ((idx (g := L) (by omega) (i.val + L - 1)).val + 1) = i := by
  have hi := i.isLt
  apply Fin.ext
  simp only [idx_val]
  rcases Nat.eq_zero_or_pos i.val with h0 | hpos
  · rw [h0, show 0 + L - 1 = L - 1 by omega, Nat.mod_eq_of_lt (show L - 1 < L by omega),
      show L - 1 + 1 = L by omega, Nat.mod_self]
  · rw [show i.val + L - 1 = L + (i.val - 1) by omega, Nat.add_mod_left,
      Nat.mod_eq_of_lt (show i.val - 1 < L by omega),
      show i.val - 1 + 1 = i.val by omega, Nat.mod_eq_of_lt hi]

/-- **General stride-3 impossibility.** Any set `H = image f` (`f : Fin (3 * k) ↪ V`, `k ≥ 1`)
disjoint from `U` whose vertices have cycle digons `f (i ± 1) ∈ N (f i)` and stride-3 outside
parents `w (i % 3) ∈ N (f i)` (`w r ∉ U ∪ H`) admits **no** `PieceCert N U H` over any `m`. -/
theorem stride3_no_pieceCert {N : V → Finset V} {U H : Finset V} (hUH : Disjoint U H)
    {k : ℕ} (hk : 1 ≤ k) (f : Fin (3 * k) → V) (hf : Function.Injective f)
    (hfH : univ.image f = H) (w : Fin 3 → V)
    (hw : ∀ r, w r ∉ U ∧ w r ∉ H)
    (hcyc : ∀ i : Fin (3 * k),
      f (idx (by omega) (i.val + 1)) ∈ N (f i) ∧
      f (idx (by omega) (i.val + 3 * k - 1)) ∈ N (f i))
    (hout : ∀ i : Fin (3 * k), w ⟨i.val % 3, by omega⟩ ∈ N (f i)) :
    ¬ Nonempty (PieceCert N U H) := by
  rintro ⟨c⟩
  have hL0 : 0 < 3 * k := by omega
  have hL2 : 2 ≤ 3 * k := by omega
  have hmemH : ∀ i, f i ∈ H := fun i => hfH ▸ mem_image_of_mem f (mem_univ i)
  have hmemL : ∀ i, f i ∈ c.l := fun i => List.mem_toFinset.mp (c.hl.symm ▸ hmemH i)
  have hPH : ∀ r, c.P r ⊆ H := fun r =>
    (subset_biUnion_of_mem c.P (mem_univ r)).trans c.cover.le
  let τ : Fin (3 * k) → ℕ := fun i => c.l.idxOf (f i)
  have hτ_lt : ∀ i, τ i < c.l.length := fun i => List.idxOf_lt_length_of_mem (hmemL i)
  have hτ_get : ∀ i, c.l[τ i]'(hτ_lt i) = f i := fun i => List.getElem_idxOf (hτ_lt i)
  have hτ_inj : Function.Injective τ := by
    intro i j hij
    apply hf
    calc f i = c.l[τ i]'(hτ_lt i) := (hτ_get i).symm
      _ = c.l[τ j]'(hτ_lt j) := by congr 1
      _ = f j := hτ_get j
  -- Every vertex `f i` must use `w (i % 3)` as its designated outside parent
  have hpar : ∀ i : Fin (3 * k), c.par (f i) = some (w ⟨i.val % 3, by omega⟩) := by
    intro i
    set wr := w ⟨i.val % 3, by omega⟩
    have hwrN : wr ∈ N (f i) := hout i
    have hwrU : wr ∉ U := (hw _).1
    have hwrH : wr ∉ H := (hw _).2
    have hwrRev : wr ∉ rev ∅ c.l (τ i) := by
      simp only [rev, empty_union, List.mem_toFinset]
      intro hm
      exact hwrH (c.hl ▸ List.mem_toFinset.mpr (List.mem_of_mem_take hm))
    have hwrP : wr ∉ c.P (c.b (f i)) := fun hm => hwrH (hPH _ hm)
    cases hp : c.par (f i) with
    | none =>
      have hp' : c.par (c.l[τ i]'(hτ_lt i)) = none := by rwa [hτ_get]
      have hsub := relCharged_step_none c.charged (τ i) (hτ_lt i) hp'
      rw [hτ_get] at hsub
      rcases mem_union.mp (hsub hwrN) with hU | hRP
      · exact absurd hU hwrU
      · rcases mem_union.mp hRP with hR | hP
        · exact absurd hR hwrRev
        · exact absurd hP hwrP
    | some w' =>
      have hp' : c.par (c.l[τ i]'(hτ_lt i)) = some w' := by rwa [hτ_get]
      obtain ⟨_, hsub, _⟩ := relCharged_step_some c.charged (τ i) (hτ_lt i) w' hp'
      rw [hτ_get] at hsub
      rcases mem_union.mp (hsub hwrN) with hU | hIRP
      · exact absurd hU hwrU
      · rcases mem_insert.mp hIRP with heq | hRP
        · exact congrArg some heq.symm
        · rcases mem_union.mp hRP with hR | hP
          · exact absurd hR hwrRev
          · exact absurd hP hwrP
  -- Locking Lemma: if `f u ∈ N (f i)` with `j % 3 = i % 3` and `τ i ≤ τ j < τ u`, then `c.b (f j) = c.a (f u)`
  have lock : ∀ i j u : Fin (3 * k), f u ∈ N (f i) → j.val % 3 = i.val % 3 →
      τ i ≤ τ j → τ j < τ u → c.b (f j) = c.a (f u) := by
    intro i j u hui hmod hij hju
    obtain ⟨huP, hbia⟩ := PieceCert.mem_supply_of_idxOf_lt c hUH (hmemH i) (hmemH u) hui
      (lt_of_le_of_lt hij hju)
    rcases eq_or_lt_of_le hij with heq | hlt
    · rw [hτ_inj heq.symm]; exact hbia
    · have hp_i : c.par (c.l[τ i]'(hτ_lt i)) = some (w ⟨i.val % 3, by omega⟩) := by
        rw [hτ_get]; exact hpar i
      have hp_j : c.par (c.l[τ j]'(hτ_lt j)) = some (w ⟨i.val % 3, by omega⟩) := by
        rw [hτ_get, hpar j]; congr 2; exact Fin.ext hmod
      have hnest := relCharged_step_nested c.charged (τ i) (τ j) hlt (hτ_lt j) _ hp_i hp_j
      have hsub : c.P (c.b (c.l[τ i]'(hτ_lt i))) ⊆
          rev ∅ c.l (τ j) ∪ c.P (c.b (c.l[τ j]'(hτ_lt j))) :=
        (subset_union_right.trans (subset_insert _ _)).trans hnest
      rcases (disjoint_nested_iff c.disj (hτ_lt i) (hτ_lt j)).mp hsub with hbeq | hrev
      · simp only [hτ_get] at hbeq
        exact hbeq.symm.trans hbia
      · simp only [hτ_get] at hrev
        exact absurd (hrev huP) (not_mem_rev_empty_of_lt_idxOf hju)
  -- Two-arc corollary: if `j₁, j₂` share residue mod 3 and both precede `u₁, u₂`, then `a(f u₁) = a(f u₂)`
  have same_col : ∀ j₁ j₂ u₁ u₂ : Fin (3 * k), j₁.val % 3 = j₂.val % 3 →
      f u₁ ∈ N (f j₁) → f u₂ ∈ N (f j₂) →
      τ j₁ < τ u₁ → τ j₂ < τ u₁ → τ j₁ < τ u₂ → τ j₂ < τ u₂ →
      c.a (f u₁) = c.a (f u₂) := by
    intro j₁ j₂ u₁ u₂ hmod h1 h2 h11 h21 h12 h22
    rcases le_total (τ j₁) (τ j₂) with hle | hle
    · have hb1 := lock j₁ j₂ u₁ h1 hmod.symm hle h21
      have hb2 := lock j₂ j₂ u₂ h2 rfl le_rfl h22
      exact hb1.symm.trans hb2
    · have hb1 := lock j₁ j₁ u₁ h1 rfl le_rfl h11
      have hb2 := lock j₂ j₁ u₂ h2 hmod hle h12
      exact hb1.symm.trans hb2
  -- Helper: every `y` has a reciprocated cycle neighbour of each residue `r ≠ y % 3`
  have exists_nb : ∀ (y : Fin (3 * k)) (r : ℕ), r < 3 → r ≠ y.val % 3 →
      ∃ v : Fin (3 * k), v.val % 3 = r ∧ f y ∈ N (f v) ∧ f v ∈ N (f y) := by
    intro y r hr hry
    rcases (show r = (y.val + 1) % 3 ∨ r = (y.val + 2) % 3 by omega) with hr1 | hr2
    · refine ⟨idx hL0 (y.val + 1), ?_, ?_, (hcyc y).1⟩
      · rw [idx_mod3, hr1]
      · have := (hcyc (idx hL0 (y.val + 1))).2
        rwa [idx_pred_succ hL2] at this
    · refine ⟨idx hL0 (y.val + 3 * k - 1), ?_, ?_, (hcyc y).2⟩
      · rw [idx_mod3]
        have : (y.val + 3 * k - 1) % 3 = (y.val + 2) % 3 := by
          have : y.val + 3 * k - 1 = (y.val + 2) + 3 * (k - 1) := by omega
          rw [this, Nat.add_mul_mod_self_left]
        rw [this, hr2]
      · have := (hcyc (idx hL0 (y.val + 3 * k - 1))).1
        rwa [idx_succ_pred hL2] at this
  -- Choose `z` maximizing `τ` on `univ`, and `x` maximizing `τ` on `{i | i % 3 ≠ z % 3}`
  obtain ⟨z, _, hz_max⟩ := exists_max_image univ τ ⟨⟨0, hL0⟩, mem_univ _⟩
  set r₀ := z.val % 3
  let S_other : Finset (Fin (3 * k)) := univ.filter (fun i => i.val % 3 ≠ r₀)
  have hS_ne : S_other.Nonempty := by
    refine ⟨idx hL0 (z.val + 1), mem_filter.mpr ⟨mem_univ _, ?_⟩⟩
    rw [idx_mod3]; omega
  obtain ⟨x, hxS, hx_max⟩ := exists_max_image S_other τ hS_ne
  have hrx_ne : x.val % 3 ≠ r₀ := (mem_filter.mp hxS).2
  have hxz_ne : x ≠ z := fun e => hrx_ne (e ▸ rfl)
  have hτ_xz : τ x < τ z :=
    lt_of_le_of_ne (hz_max x (mem_univ x)) (fun e => hxz_ne (hτ_inj e))
  set r_x := x.val % 3
  set r₃ := (6 - r₀ - r_x) % 3
  have hr₃_lt : r₃ < 3 := Nat.mod_lt _ (by omega)
  have hr₃_ne0 : r₃ ≠ r₀ := by omega
  have hr₃_nex : r₃ ≠ r_x := by omega
  obtain ⟨v_x, hvx_mod, hvx_z, hz_vx⟩ := exists_nb z r_x (Nat.mod_lt _ (by omega)) hrx_ne
  obtain ⟨v₃, hv₃_mod, hv₃_z, _⟩ := exists_nb z r₃ hr₃_lt hr₃_ne0
  obtain ⟨u₃, hu₃_mod, hu₃_x, _⟩ := exists_nb x r₃ hr₃_lt hr₃_nex
  have hτ_u₃ : τ u₃ < τ x := by
    have hu₃S : u₃ ∈ S_other := mem_filter.mpr ⟨mem_univ _, by rw [hu₃_mod]; exact hr₃_ne0⟩
    have hu₃_ne : u₃ ≠ x := fun e => hr₃_nex (hu₃_mod.symm.trans (congrArg (·.val % 3) e))
    exact lt_of_le_of_ne (hx_max u₃ hu₃S) (fun e => hu₃_ne (hτ_inj e))
  have hτ_v₃ : τ v₃ < τ x := by
    have hv₃S : v₃ ∈ S_other := mem_filter.mpr ⟨mem_univ _, by rw [hv₃_mod]; exact hr₃_ne0⟩
    have hv₃_ne : v₃ ≠ x := fun e => hr₃_nex (hv₃_mod.symm.trans (congrArg (·.val % 3) e))
    exact lt_of_le_of_ne (hx_max v₃ hv₃S) (fun e => hv₃_ne (hτ_inj e))
  -- Unconditionally, `a(f x) = a(f z)` via the third residue `r₃`
  have hcol_xz : c.a (f x) = c.a (f z) :=
    same_col u₃ v₃ x z (hu₃_mod.trans hv₃_mod.symm) hu₃_x hv₃_z hτ_u₃ hτ_v₃
      (hτ_u₃.trans hτ_xz) (hτ_v₃.trans hτ_xz)
  by_cases hxv : x = v_x
  · subst hxv
    have hf_ne : f x ≠ f z := fun e => hxz_ne (hf e)
    exact PieceCert.digon_ne c hUH (hmemH x) (hmemH z) hf_ne hz_vx hvx_z hcol_xz
  · have hvxS : v_x ∈ S_other := mem_filter.mpr ⟨mem_univ _, by rw [hvx_mod]; exact hrx_ne⟩
    have hτ_vx : τ v_x < τ x :=
      lt_of_le_of_ne (hx_max v_x hvxS) (fun e => hxv (hτ_inj e).symm)
    have hbx : c.b (f x) = c.a (f z) :=
      lock v_x x z hvx_z hvx_mod.symm hτ_vx.le hτ_xz
    exact c.ab (f x) (hmemL x) (hcol_xz.trans hbx.symm)

end Stride3Impossibility

section StrideModel

/-- Canonical stride-`s` digon cycle relation on `Fin (s * k) ⊕ Fin s`:
cycle vertices `Sum.inl i` recover from `i ± 1` and hub `Sum.inr (i % s)`;
hubs `Sum.inr r` have empty recovery set. -/
def strideRel (s k : ℕ) [NeZero s] [NeZero k] :
    (Fin (s * k) ⊕ Fin s) → Finset (Fin (s * k) ⊕ Fin s)
  | Sum.inl i =>
      have hs0 : 0 < s := NeZero.pos s
      have hsk0 : 0 < s * k := Nat.mul_pos hs0 (NeZero.pos k)
      {Sum.inl (idx hsk0 (i.val + 1)),
       Sum.inl (idx hsk0 (i.val + s * k - 1)),
       Sum.inr ⟨i.val % s, Nat.mod_lt _ hs0⟩}
  | Sum.inr _ => ∅

/-- The cycle core `Fin (s * k)` inside `Fin (s * k) ⊕ Fin s`. -/
def strideCore (s k : ℕ) : Finset (Fin (s * k) ⊕ Fin s) :=
  univ.image Sum.inl

/-- **Proposition CS(a).** For `s = 3` and every `k ≥ 1`, `strideCore 3 k` has no `PieceCert`. -/
theorem strideCore3_no_pieceCert (k : ℕ) [NeZero k] :
    ¬ Nonempty (PieceCert (strideRel 3 k) ∅ (strideCore 3 k)) := by
  have hk : 1 ≤ k := NeZero.one_le
  refine stride3_no_pieceCert (disjoint_empty_left _) hk Sum.inl Sum.inl_injective rfl
    Sum.inr ?_ ?_ ?_
  · intro r
    simp [strideCore]
  · intro i
    simp [strideRel]
  · intro i
    simp [strideRel]

/-- **Proposition CS(c) (and all `s ≥ 4`).** For every `s ≥ 4` and `k ≥ 1`, pulling back
`HalfRate.ccol s` and `HalfRate.bcol s` modulo `s` along `0, 1, …, s * k - 1` constructs an
explicit co-supplied `3`-record `PieceCert` for `strideCore s k`. -/
def strideGe4_pieceCert (s k : ℕ) [NeZero s] [NeZero k] (hs : 4 ≤ s) :
    PieceCert (strideRel s k) ∅ (strideCore s k) := by
  have hk : 1 ≤ k := NeZero.one_le
  have hs0 : 0 < s := by omega
  have hsk0 : 0 < s * k := Nat.mul_pos hs0 (by omega)
  let col : (Fin (s * k) ⊕ Fin s) → Fin 3 := fun
    | Sum.inl i => ccol s (i.val % s)
    | Sum.inr _ => 0
  let bfn : (Fin (s * k) ⊕ Fin s) → Fin 3 := fun
    | Sum.inl i => bcol s (i.val % s)
    | Sum.inr _ => 1
  let par : (Fin (s * k) ⊕ Fin s) → Option (Fin (s * k) ⊕ Fin s) := fun
    | Sum.inl i => some (Sum.inr ⟨i.val % s, Nat.mod_lt _ hs0⟩)
    | Sum.inr _ => none
  let P : Fin 3 → Finset (Fin (s * k) ⊕ Fin s) :=
    fun r => (strideCore s k).filter (fun v => col v = r)
  let l : List (Fin (s * k) ⊕ Fin s) := List.ofFn (fun i : Fin (s * k) => Sum.inl i)
  refine
    { m := 3
      P := P
      disj := ?_
      cover := ?_
      l := l
      hl := ?_
      a := col
      b := bfn
      par := par
      own := ?_
      ab := ?_
      charged := ?_ }
  · intro r₁ r₂ hne
    rw [disjoint_left]
    intro v hv₁ hv₂
    exact hne ((mem_filter.mp hv₁).2.symm.trans (mem_filter.mp hv₂).2)
  · ext v
    simp only [P, mem_biUnion, mem_univ, true_and, mem_filter]
    exact ⟨fun ⟨_, hv, _⟩ => hv, fun hv => ⟨col v, hv, rfl⟩⟩
  · ext v
    simp [l, strideCore, List.mem_ofFn]
  · intro v hv
    have hvC : v ∈ strideCore s k := by
      simp only [l, List.mem_ofFn] at hv
      obtain ⟨i, rfl⟩ := hv
      exact mem_image_of_mem _ (mem_univ i)
    exact mem_filter.mpr ⟨hvC, rfl⟩
  · intro v hv
    simp only [l, List.mem_ofFn] at hv
    obtain ⟨i, rfl⟩ := hv
    exact ccol_ne_bcol hs (Nat.mod_lt _ hs0)
  · refine relCharged_of_cosupply _ _ _ _ _ _ l ∅ (fun _ => ∅) ?_ ?_ ?_
    · intro j hj hp
      have hj' : j < s * k := by simpa [l] using hj
      simp [l, par] at hp
    · intro j hj w hp
      have hj' : j < s * k := by simpa [l] using hj
      simp only [l, List.getElem_ofFn, par, Option.some.injEq] at hp
      subst hp
      refine ⟨by simp [strideCore], ?_, empty_subset _⟩
      intro u hu
      simp only [l, List.getElem_ofFn, strideRel, mem_insert, mem_singleton] at hu ⊢
      rcases hu with rfl | rfl | rfl
      · -- `u = Sum.inl (idx (j + 1))`
        apply mem_union_right
        apply mem_insert_of_mem
        rcases Nat.lt_or_ge (j + 1) (s * k) with hlt | hge
        · apply mem_union_right
          refine mem_filter.mpr ⟨mem_image_of_mem _ (mem_univ _), ?_⟩
          simp only [col, bfn, idx_val, Nat.mod_eq_of_lt hlt]
          have hmod : (j + 1) % s = if j % s + 1 = s then 0 else j % s + 1 := by
            have h1 := Nat.mod_lt j hs0
            rw [Nat.add_mod, Nat.mod_eq_of_lt (show 1 < s by omega)]
            split_ifs with h
            · simp [h]
            · exact Nat.mod_eq_of_lt (by omega)
          rw [hmod]
          unfold bcol
          split_ifs <;> rfl
        · -- `j = s * k - 1`, so `idx (j + 1) = 0`, already revealed at step `0 < j`
          apply mem_union_left
          have hj_last : j = s * k - 1 := by omega
          have h4sk : 4 ≤ s * k := by nlinarith
          have hj_pos : 0 < j := by omega
          have hidx0 : idx hsk0 (j + 1) = ⟨0, hsk0⟩ := by
            apply Fin.ext; simp [idx_val, show j + 1 = s * k by omega]
          rw [hidx0]
          exact mem_rev_ofFn (fun i : Fin (s * k) => Sum.inl i) ⟨0, hsk0⟩ (by simpa using hj_pos)
      · -- `u = Sum.inl (idx (j + s * k - 1))`
        apply mem_union_right
        apply mem_insert_of_mem
        rcases Nat.eq_zero_or_pos j with rfl | hj_pos
        · -- `j = 0`: `idx (s * k - 1) = s * k - 1`, whose residue mod `s` is `s - 1`
          apply mem_union_right
          refine mem_filter.mpr ⟨mem_image_of_mem _ (mem_univ _), ?_⟩
          have hmod_last : (s * k - 1) % s = s - 1 := by
            have : s * k - 1 = (s - 1) + s * (k - 1) := by
              cases k with
              | zero => omega
              | succ k' => simp [Nat.mul_succ]; omega
            rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
          simp only [col, bfn, Nat.zero_add, idx_val, Nat.mod_eq_of_lt (show s * k - 1 < s * k by omega),
            hmod_last, Nat.zero_mod]
          exact ccol_last hs
        · -- `j > 0`: `idx (j + s * k - 1) = j - 1 < j`, already revealed!
          apply mem_union_left
          have hidx_prev : idx hsk0 (j + s * k - 1) = ⟨j - 1, by omega⟩ := by
            apply Fin.ext
            simp only [idx_val]
            rw [show j + s * k - 1 = s * k + (j - 1) by omega, Nat.add_mod_left,
              Nat.mod_eq_of_lt (by omega)]
          rw [hidx_prev]
          exact mem_rev_ofFn (fun i : Fin (s * k) => Sum.inl i) ⟨j - 1, by omega⟩ (by simp; omega)
      · exact mem_union_right _ (mem_insert_self _ _)
    · intro j j' _ hj' w h1 h2
      have hj1 : j < s * k := by have : j' < l.length := hj'; simp [l] at this; omega
      have hj2 : j' < s * k := by simpa [l] using hj'
      have h12 : j % s = j' % s := by
        have := h1.trans h2.symm
        simpa [l, par] using this
      simp only [l, List.getElem_ofFn, bfn, h12]

/-- **Proposition CS(b).** For even `s ≥ 4` and every `k ≥ 1`, `strideCore s k` admits a
`2`-record (`m = 2`) co-supplied `PieceCert` via parity 2-coloring. -/
theorem strideEven_pieceCert_two (s k : ℕ) [NeZero s] [NeZero k] (hs : 4 ≤ s) (heven : Even s) :
    ∃ c : PieceCert (strideRel s k) ∅ (strideCore s k), c.m = 2 := by
  have hk : 1 ≤ k := NeZero.one_le
  have hs0 : 0 < s := by omega
  have hsk0 : 0 < s * k := Nat.mul_pos hs0 (by omega)
  obtain ⟨s₂, hs₂⟩ := heven
  have h2s : 2 ∣ s := ⟨s₂, by omega⟩
  have h2sk : 2 ∣ s * k := dvd_mul_of_dvd_left h2s k
  let A : Finset (Fin (s * k) ⊕ Fin s) :=
    (univ.filter (fun i : Fin (s * k) => i.val % 2 = 0)).image Sum.inl
  let B : Finset (Fin (s * k) ⊕ Fin s) :=
    (univ.filter (fun i : Fin (s * k) => i.val % 2 = 1)).image Sum.inl
  -- Eliminate all of `A` first, then all of `B`!
  let lA : List (Fin (s * k) ⊕ Fin s) :=
    ((List.finRange (s * k)).filter (fun i => i.val % 2 == 0)).map Sum.inl
  let lB : List (Fin (s * k) ⊕ Fin s) :=
    ((List.finRange (s * k)).filter (fun i => i.val % 2 == 1)).map Sum.inl
  let col : (Fin (s * k) ⊕ Fin s) → Fin 2 := fun
    | Sum.inl i => ⟨i.val % 2, Nat.mod_lt _ (by omega)⟩
    | Sum.inr _ => 0
  let bfn : (Fin (s * k) ⊕ Fin s) → Fin 2 := fun
    | Sum.inl i => ⟨1 - i.val % 2, by omega⟩
    | Sum.inr _ => 1
  let par : (Fin (s * k) ⊕ Fin s) → Option (Fin (s * k) ⊕ Fin s) := fun
    | Sum.inl i => some (Sum.inr ⟨i.val % s, Nat.mod_lt _ hs0⟩)
    | Sum.inr _ => none
  have hpar_nb : ∀ (i : Fin (s * k)) (n : ℕ), n % 2 ≠ i.val % 2 →
      (idx hsk0 n).val % 2 = 1 - i.val % 2 := by
    intro i n hn
    simp only [idx_val]
    rw [Nat.mod_mod_of_dvd n h2sk]
    omega
  have hAB : Disjoint A B := by
    rw [disjoint_left]
    intro v hv₁ hv₂
    simp only [A, B, mem_image, mem_filter, mem_univ, true_and] at hv₁ hv₂
    obtain ⟨i₁, hi₁, rfl⟩ := hv₁
    obtain ⟨i₂, hi₂, heq⟩ := hv₂
    cases Sum.inl.inj heq
    omega
  let P2 : Fin 2 → Finset (Fin (s * k) ⊕ Fin s) := fun r => if r = 0 then A else B
  refine ⟨{
    m := 2
    P := P2
    disj := by
      intro r₁ r₂ hne
      fin_cases r₁ <;> fin_cases r₂ <;> simp_all [P2, disjoint_comm]
    cover := by
      ext v
      simp only [P2, mem_biUnion, mem_univ, true_and, Fin.exists_fin_two, ↓reduceIte,
        show (1 : Fin 2) ≠ 0 by decide, strideCore, A, B, mem_image, mem_filter]
      constructor
      · rintro (⟨i, _, rfl⟩ | ⟨i, _, rfl⟩) <;> exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩
        rcases (show i.val % 2 = 0 ∨ i.val % 2 = 1 by omega) with h0 | h1
        · exact Or.inl ⟨i, h0, rfl⟩
        · exact Or.inr ⟨i, h1, rfl⟩
    l := lA ++ lB
    hl := by
      ext v
      simp only [lA, lB, List.toFinset_append, mem_union, List.mem_toFinset, List.mem_map,
        List.mem_filter, List.mem_finRange, true_and, strideCore, mem_image, mem_univ]
      constructor
      · rintro (⟨i, _, rfl⟩ | ⟨i, _, rfl⟩) <;> exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩
        rcases (show (i.val % 2 == 0) = true ∨ (i.val % 2 == 1) = true by
          rcases (show i.val % 2 = 0 ∨ i.val % 2 = 1 by omega) with h | h <;> simp [h]) with h0 | h1
        · exact Or.inl ⟨i, h0, rfl⟩
        · exact Or.inr ⟨i, h1, rfl⟩
    a := col
    b := bfn
    par := par
    own := by
      intro v hv
      simp only [lA, lB, List.mem_append, List.mem_map, List.mem_filter, List.mem_finRange,
        true_and] at hv
      rcases hv with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
      · have hi0 : i.val % 2 = 0 := by simpa using hi
        simp [P2, col, hi0, A]
      · have hi1 : i.val % 2 = 1 := by simpa using hi
        simp [P2, col, hi1, B]
    ab := by
      intro v hv
      simp only [lA, lB, List.mem_append, List.mem_map, List.mem_filter, List.mem_finRange,
        true_and] at hv
      rcases hv with ⟨i, _, rfl⟩ | ⟨i, _, rfl⟩ <;>
        (simp only [col, bfn, ne_eq, Fin.ext_iff]; omega)
    charged := by
      refine relCharged_of_cosupply _ _ _ _ _ _ (lA ++ lB) ∅ (fun _ => ∅) ?_ ?_ ?_
      · intro j hj hp
        have hmem : (lA ++ lB)[j] ∈ lA ++ lB := List.getElem_mem hj
        simp only [lA, lB, List.mem_append, List.mem_map] at hmem
        rcases hmem with ⟨i, _, heq⟩ | ⟨i, _, heq⟩ <;> (rw [← heq] at hp; simp [par] at hp)
      · intro j hj w hp
        have hmem : (lA ++ lB)[j] ∈ lA ++ lB := List.getElem_mem hj
        simp only [lA, lB, List.mem_append, List.mem_map, List.mem_filter, List.mem_finRange,
          true_and] at hmem
        obtain ⟨i, heq⟩ : ∃ i : Fin (s * k), Sum.inl i = (lA ++ lB)[j] := by
          rcases hmem with ⟨i, _, heq⟩ | ⟨i, _, heq⟩ <;> exact ⟨i, heq⟩
        rw [← heq] at hp ⊢
        simp only [par, Option.some.injEq] at hp
        subst hp
        refine ⟨by simp [strideCore], ?_, empty_subset _⟩
        intro u hu
        simp only [strideRel, mem_insert, mem_singleton] at hu ⊢
        have hsupp : ∀ n : ℕ, n % 2 ≠ i.val % 2 →
            Sum.inl (idx hsk0 n) ∈ P2 (bfn (Sum.inl i)) := by
          intro n hn
          have hidx := hpar_nb i n hn
          rcases (show i.val % 2 = 0 ∨ i.val % 2 = 1 by omega) with hi0 | hi1
          · have h1 : bfn (Sum.inl i) = 1 := by apply Fin.ext; simp [bfn, hi0]
            simp only [P2, h1, show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte]
            exact mem_image.mpr ⟨idx hsk0 n, mem_filter.mpr ⟨mem_univ _, by omega⟩, rfl⟩
          · have h0 : bfn (Sum.inl i) = 0 := by apply Fin.ext; simp [bfn, hi1]
            simp only [P2, h0, ↓reduceIte]
            exact mem_image.mpr ⟨idx hsk0 n, mem_filter.mpr ⟨mem_univ _, by omega⟩, rfl⟩
        rcases hu with rfl | rfl | rfl
        · exact mem_union_right _ (mem_insert_of_mem (mem_union_right _
            (hsupp (i.val + 1) (by omega))))
        · exact mem_union_right _ (mem_insert_of_mem (mem_union_right _
            (hsupp (i.val + s * k - 1) (by
              have : 1 ≤ s * k := hsk0
              obtain ⟨m, hm⟩ := h2sk
              omega))))
        · exact mem_union_right _ (mem_insert_self _ _)
      · intro j j' hj hj' w h1 h2
        have hj_lt : j < (lA ++ lB).length := lt_trans hj hj'
        have hmem1 : (lA ++ lB)[j]'hj_lt ∈ lA ++ lB := List.getElem_mem hj_lt
        have hmem2 : (lA ++ lB)[j']'hj' ∈ lA ++ lB := List.getElem_mem hj'
        simp only [lA, lB, List.mem_append, List.mem_map] at hmem1 hmem2
        obtain ⟨i₁, heq₁⟩ : ∃ i, Sum.inl i = (lA ++ lB)[j]'hj_lt := by
          rcases hmem1 with ⟨i, _, h⟩ | ⟨i, _, h⟩ <;> exact ⟨i, h⟩
        obtain ⟨i₂, heq₂⟩ : ∃ i, Sum.inl i = (lA ++ lB)[j']'hj' := by
          rcases hmem2 with ⟨i, _, h⟩ | ⟨i, _, h⟩ <;> exact ⟨i, h⟩
        rw [← heq₁] at h1 ⊢
        rw [← heq₂] at h2 ⊢
        have h12 : i₁.val % s = i₂.val % s := by
          have := h1.trans h2.symm
          simpa [par] using this
        have hmod2 : i₁.val % 2 = i₂.val % 2 := by
          calc i₁.val % 2 = (i₁.val % s) % 2 := (Nat.mod_mod_of_dvd i₁.val h2s).symm
            _ = (i₂.val % s) % 2 := by rw [h12]
            _ = i₂.val % 2 := Nat.mod_mod_of_dvd i₂.val h2s
        apply Fin.ext
        simp only [bfn, hmod2]
  }, rfl⟩

/-- **Proposition CS (stride dichotomy).** For `s ≥ 3` and `k ≥ 1`, the canonical stride-`s`
digon cycle core `strideCore s k` admits a `PieceCert` (for some `m`) if and only if `4 ≤ s`. -/
theorem strideCore_pieceCert_iff (s k : ℕ) [NeZero s] [NeZero k] (hs : 3 ≤ s) :
    Nonempty (PieceCert (strideRel s k) ∅ (strideCore s k)) ↔ 4 ≤ s := by
  constructor
  · intro hne
    by_contra hlt
    have hs3 : s = 3 := by omega
    subst hs3
    exact strideCore3_no_pieceCert k hne
  · intro hs4
    exact ⟨strideGe4_pieceCert s k hs4⟩

end StrideModel

end DirectedReciprocity
