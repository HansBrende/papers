import Transpose.Tape.PPrime
import NativeRelations.TightConstants

/-!
# Grouped Pass Counting with Coarse Passes (Theorem 10.3 and Its Corollaries)

Extends the first paper's grouped pass bound to passes that are coarsely monotone up to a bounded
amplitude with auxiliary small-workspace tapes (`CoarseWorkspacePartition`,
`theoremP_coarseWorkspace_grouped_on_bits`, `theoremPprime_coarseWorkspace_grouped_on_bits`,
`oblivious_singleScale_coarseWorkspace_closed_lb`, `adaptive_singleScale_coarseWorkspace_closed_lb`),
and deduces subcritical phase-profile exclusions (`subcriticalPhaseProfile_oblivious_excludes`,
`subcriticalDimPhaseProfile_oblivious_excludes`,
`subcriticalPhaseProfile_adaptive_polyTime_excludes`), the exclusion of boundedly many coarse
passes with amplitudes and workspaces up to a small fixed fraction of `L`, in particular of size
`o(L)` (`boundedCoarsePasses_oblivious_excludes`, `boundedCoarsePasses_adaptive_polyTime_excludes`,
`boundedCoarsePasses_sublinear_oblivious_excludes`,
`boundedCoarsePasses_sublinear_adaptive_polyTime_excludes`), the `θ = 2` sharpness clauses
(`groupedBound_thetaTwo_not_excluded_above_half`, `perfectUnshuffleSlopeProduct_tendsto_half`,
`unshuffleStep_iter_transpose`), and the non-exclusion above `1 / 2` at every `θ > 0` and every
bank size (`groupedBound_not_excluded_above_half`).
-/

set_option autoImplicit false

namespace NativeRelations

open Filter Transpose Transpose.Tape Transpose.Tape.Impl
open scoped BigOperators Topology

/-! ## §1. Coarse-Monotone & Workspace-Folded Pass Partitions and Bank-Restricted Addresses -/

/-- Work-tape cells visited on tape `t` during steps `[0, T')`. -/
noncomputable def visitedWorkCells (M : TM) (w : List Bool) (T' : ℕ) (t : Fin M.k) : Finset ℤ :=
  (Finset.range T').image (fun τ => workTraj M w τ t)

/-- Total workspace cell budget across all non-bank tapes `t ∉ B_bank`. -/
def workspaceCellSum {k : ℕ} (B_bank : Finset (Fin k)) (S : Fin k → ℕ) : ℕ :=
  ∑ t ∈ Finset.univ \ B_bank, S t

/-- `p` splits `[0, T')` into `r` consecutive passes `[p i, p (i + 1))` such that:
1. `inTraj M w` is `A_in`-coarsely monotone on each pass;
2. every bank tape `t ∈ B_bank` is `A`-coarsely monotone on each pass; and
3. every workspace tape `t ∉ B_bank` visits at most `S t` distinct cells during `[0, T')`. -/
def CoarseWorkspacePartition (M : TM) (w : List Bool) (T' r : ℕ) (B_bank : Finset (Fin M.k))
    (A_in A : ℕ) (S : Fin M.k → ℕ) (p : ℕ → ℕ) : Prop :=
  p 0 = 0 ∧ p r = T' ∧ (∀ i < r, p i ≤ p (i + 1)) ∧
    (∀ i < r, CoarseMonoOnInterval (inTraj M w) (p i) (p (i + 1)) A_in) ∧
    (∀ i < r, ∀ t ∈ B_bank,
      CoarseMonoOnInterval (fun τ => workTraj M w τ t) (p i) (p (i + 1)) A) ∧
    (∀ t : Fin M.k, t ∉ B_bank → (visitedWorkCells M w T' t).card ≤ S t)

theorem coarseMonoOnInterval_empty (h : ℕ → ℤ) (a A : ℕ) :
    CoarseMonoOnInterval h a a A :=
  Or.inl (fun _ _ h1 h2 h3 => by omega)

/-- Padding a `CoarseWorkspacePartition` from `r₀` passes to any `r ≥ r₀` by appending empty
`[T', T')` passes. -/
theorem coarseWorkspacePartition_pad {M : TM} {w : List Bool} {T' r₀ r : ℕ}
    {B_bank : Finset (Fin M.k)} {A_in A : ℕ} {S : Fin M.k → ℕ} {p : ℕ → ℕ}
    (hp : CoarseWorkspacePartition M w T' r₀ B_bank A_in A S p) (hle : r₀ ≤ r) :
    ∃ p' : ℕ → ℕ, CoarseWorkspacePartition M w T' r B_bank A_in A S p' := by
  refine ⟨fun i => if i ≤ r₀ then p i else T', ?_⟩
  have hp_mono : ∀ i j, i ≤ j → j ≤ r₀ → p i ≤ p j := by
    intro i j hij hj
    induction j, hij using Nat.le_induction with
    | base => exact le_rfl
    | succ j hij ih => exact le_trans (ih (by omega)) (hp.2.2.1 j (by omega))
  have hp_le_T : ∀ i ≤ r₀, p i ≤ T' := by
    intro i hi; rw [← hp.2.1]; exact hp_mono i r₀ hi le_rfl
  refine ⟨by simp [hp.1], ?_, ?_, ?_, ?_, hp.2.2.2.2.2⟩
  · dsimp only
    split_ifs with h
    · have : r = r₀ := le_antisymm h hle
      rw [this, hp.2.1]
    · rfl
  · intro i hi
    dsimp only
    split_ifs with h0 h1 h1'
    · exact hp.2.2.1 i (by omega)
    · exact hp_le_T i h0
    · omega
    · exact le_rfl
  · intro i hi
    dsimp only
    split_ifs with h0 h1 h1'
    · exact hp.2.2.2.1 i (by omega)
    · have : i = r₀ := by omega
      rw [this, hp.2.1]
      exact coarseMonoOnInterval_empty _ _ _
    · omega
    · exact coarseMonoOnInterval_empty _ _ _
  · intro i hi t ht
    dsimp only
    split_ifs with h0 h1 h1'
    · exact hp.2.2.2.2.1 i (by omega) t ht
    · have : i = r₀ := by omega
      rw [this, hp.2.1]
      exact coarseMonoOnInterval_empty _ _ _
    · omega
    · exact coarseMonoOnInterval_empty _ _ _

theorem cwp_mono {M : TM} {w : List Bool} {T' r : ℕ} {B_bank : Finset (Fin M.k)}
    {A_in A : ℕ} {S : Fin M.k → ℕ} {p : ℕ → ℕ}
    (hp : CoarseWorkspacePartition M w T' r B_bank A_in A S p)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ r) : p i ≤ p j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih => exact le_trans (ih (by omega)) (hp.2.2.1 j (by omega))

theorem cwp_le_T {M : TM} {w : List Bool} {T' r : ℕ} {B_bank : Finset (Fin M.k)}
    {A_in A : ℕ} {S : Fin M.k → ℕ} {p : ℕ → ℕ}
    (hp : CoarseWorkspacePartition M w T' r B_bank A_in A S p) {i : ℕ} (hi : i ≤ r) :
    p i ≤ T' := by
  rw [← hp.2.1]; exact cwp_mono hp hi le_rfl

theorem cwp_exists_pass {M : TM} {w : List Bool} {T' r : ℕ} {B_bank : Finset (Fin M.k)}
    {A_in A : ℕ} {S : Fin M.k → ℕ} {p : ℕ → ℕ}
    (hp : CoarseWorkspacePartition M w T' r B_bank A_in A S p) {σ : ℕ} (hσ : σ < T') :
    ∃ P < r, p P ≤ σ ∧ σ < p (P + 1) := by
  classical
  have h0 : p 0 ≤ σ := by rw [hp.1]; exact Nat.zero_le _
  set P := Nat.findGreatest (fun i => p i ≤ σ) r
  have hPσ : p P ≤ σ := Nat.findGreatest_spec (P := fun i => p i ≤ σ) (Nat.zero_le r) h0
  have hPr : P ≤ r := Nat.findGreatest_le r
  have hPlt : P < r := by
    rcases Nat.lt_or_ge P r with h | h
    · exact h
    · have : P = r := le_antisymm hPr h
      rw [this, hp.2.1] at hPσ; omega
  refine ⟨P, hPlt, hPσ, ?_⟩
  by_contra hc
  push Not at hc
  exact Nat.findGreatest_is_greatest (P := fun i => p i ≤ σ) (Nat.lt_succ_self P) hPlt hc

/-- Bank-restricted addresses below pass `P`: lists of `(pass, tape)` with `tape ∈ B_bank` and
strictly decreasing passes `< P`. -/
def bankAddrsBelow {k : ℕ} (B_bank : Finset (Fin k)) : ℕ → Finset (List (ℕ × Fin k))
  | 0 => {[]}
  | P + 1 => bankAddrsBelow B_bank P ∪
      B_bank.biUnion (fun t => (bankAddrsBelow B_bank P).image (fun l => (P, t) :: l))

/-- All bank-restricted addresses across `r` passes. -/
def bankAddresses {k : ℕ} (B_bank : Finset (Fin k)) (r : ℕ) : Finset (ℕ × List (ℕ × Fin k)) :=
  (Finset.range r).biUnion (fun P₀ => (bankAddrsBelow B_bank P₀).image (fun l => (P₀, l)))

theorem nil_mem_bankAddrsBelow {k : ℕ} (B_bank : Finset (Fin k)) (P : ℕ) :
    ([] : List (ℕ × Fin k)) ∈ bankAddrsBelow B_bank P := by
  induction P with
  | zero => simp [bankAddrsBelow]
  | succ P ih => simp only [bankAddrsBelow]; exact Finset.mem_union_left _ ih

theorem mem_bankAddrsBelow {k : ℕ} {B_bank : Finset (Fin k)} {P : ℕ} {l : List (ℕ × Fin k)} :
    l ∈ bankAddrsBelow B_bank P ↔
      l = [] ∨ ∃ x l', l = x :: l' ∧ x.1 < P ∧ x.2 ∈ B_bank ∧ l' ∈ bankAddrsBelow B_bank x.1 := by
  induction P generalizing l with
  | zero => simp [bankAddrsBelow]
  | succ P ih =>
    simp only [bankAddrsBelow, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image]
    constructor
    · rintro (h | ⟨t, ht, l', hl', rfl⟩)
      · rcases ih.1 h with h | ⟨x, l', rfl, hx, hxt, hl'⟩
        · exact Or.inl h
        · exact Or.inr ⟨x, l', rfl, by omega, hxt, hl'⟩
      · exact Or.inr ⟨(P, t), l', rfl, by simp, ht, hl'⟩
    · rintro (rfl | ⟨x, l', rfl, hx, hxt, hl'⟩)
      · exact Or.inl (nil_mem_bankAddrsBelow B_bank P)
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hx with hlt | heq
        · exact Or.inl (ih.2 (Or.inr ⟨x, l', rfl, hlt, hxt, hl'⟩))
        · right
          refine ⟨x.2, hxt, l', ?_, ?_⟩
          · rw [← heq]; exact hl'
          · rw [← heq]

theorem bankAddrsBelow_subset_addrsBelow {k : ℕ} (B_bank : Finset (Fin k)) (P : ℕ) :
    bankAddrsBelow B_bank P ⊆ addrsBelow k P := by
  induction P with
  | zero => simp [bankAddrsBelow, addrsBelow]
  | succ P ih =>
    intro l hl
    simp only [bankAddrsBelow, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image] at hl
    simp only [addrsBelow, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and,
      Finset.mem_image]
    rcases hl with h | ⟨t, _, l', hl', rfl⟩
    · exact Or.inl (ih h)
    · exact Or.inr ⟨t, l', ih hl', rfl⟩

theorem mem_bankAddresses {k : ℕ} {B_bank : Finset (Fin k)} {r : ℕ}
    {α : ℕ × List (ℕ × Fin k)} :
    α ∈ bankAddresses B_bank r ↔ α.1 < r ∧ α.2 ∈ bankAddrsBelow B_bank α.1 := by
  obtain ⟨P₀, l⟩ := α
  simp only [bankAddresses, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨P, hP, l', hl', rfl, rfl⟩; exact ⟨hP, hl'⟩
  · rintro ⟨hP, hl⟩; exact ⟨P₀, hP, l, hl, rfl, rfl⟩

theorem bankAddresses_subset_addresses {k : ℕ} (B_bank : Finset (Fin k)) (r : ℕ) :
    bankAddresses B_bank r ⊆ addresses k r := by
  intro α hα
  rw [mem_bankAddresses] at hα
  exact mem_addresses.2 ⟨hα.1, bankAddrsBelow_subset_addrsBelow B_bank α.1 hα.2⟩

theorem card_bankAddrsBelow_le {k : ℕ} (B_bank : Finset (Fin k)) (P : ℕ) :
    (bankAddrsBelow B_bank P).card ≤ (B_bank.card + 1) ^ P := by
  induction P with
  | zero => simp [bankAddrsBelow]
  | succ P ih =>
    simp only [bankAddrsBelow]
    calc (bankAddrsBelow B_bank P ∪ B_bank.biUnion (fun t =>
            (bankAddrsBelow B_bank P).image (fun l => (P, t) :: l))).card
        ≤ (bankAddrsBelow B_bank P).card + (B_bank.biUnion (fun t =>
            (bankAddrsBelow B_bank P).image (fun l => (P, t) :: l))).card :=
          Finset.card_union_le _ _
      _ ≤ (bankAddrsBelow B_bank P).card +
            ∑ t ∈ B_bank, ((bankAddrsBelow B_bank P).image (fun l => (P, t) :: l)).card :=
          Nat.add_le_add_left Finset.card_biUnion_le _
      _ ≤ (bankAddrsBelow B_bank P).card + ∑ _t ∈ B_bank, (bankAddrsBelow B_bank P).card :=
          Nat.add_le_add_left (Finset.sum_le_sum (fun _ _ => Finset.card_image_le)) _
      _ = (B_bank.card + 1) * (bankAddrsBelow B_bank P).card := by
          rw [Finset.sum_const, smul_eq_mul]; ring
      _ ≤ (B_bank.card + 1) * (B_bank.card + 1) ^ P := Nat.mul_le_mul_left _ ih
      _ = (B_bank.card + 1) ^ (P + 1) := by ring

theorem card_bankAddresses_le {k : ℕ} (B_bank : Finset (Fin k)) (r : ℕ) :
    (bankAddresses B_bank r).card ≤ addrCount B_bank.card r := by
  unfold bankAddresses addrCount
  calc ((Finset.range r).biUnion (fun P₀ => (bankAddrsBelow B_bank P₀).image (fun l => (P₀, l)))).card
      ≤ ∑ P₀ ∈ Finset.range r, ((bankAddrsBelow B_bank P₀).image (fun l => (P₀, l))).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ P₀ ∈ Finset.range r, (B_bank.card + 1) ^ P₀ :=
        Finset.sum_le_sum (fun P₀ _ => le_trans Finset.card_image_le (card_bankAddrsBelow_le B_bank P₀))

theorem append_mem_bankAddrsBelow {k : ℕ} {B_bank : Finset (Fin k)} {t : Fin k} (ht : t ∈ B_bank) :
    ∀ {l : List (ℕ × Fin k)} {P P' : ℕ},
      l ∈ bankAddrsBelow B_bank P → P' < lastPass l P → l ++ [(P', t)] ∈ bankAddrsBelow B_bank P
  | [], P, P', _, hP' => by
    rw [mem_bankAddrsBelow]
    exact Or.inr ⟨(P', t), [], rfl, hP', ht, nil_mem_bankAddrsBelow B_bank P'⟩
  | x :: l, P, P', h, hP' => by
    rcases mem_bankAddrsBelow.1 h with h | ⟨y, l', he, hy, hyt, hl'⟩
    · exact absurd h (List.cons_ne_nil _ _)
    · obtain ⟨rfl, rfl⟩ := List.cons.inj he
      rw [mem_bankAddrsBelow]
      exact Or.inr ⟨x, l ++ [(P', t)], rfl, hy, hyt, append_mem_bankAddrsBelow ht hl' hP'⟩

/-! ## §2. Coarse-Monotone Dependency Forest, Freshness, Time Separation, & Coverage -/

/-- Symmetric `(4A + 1)`-cell anchor window `[h a - 2A, h a + 2A]` around `h a`. -/
def coarseAnchorWin (h : ℕ → ℤ) (a A : ℕ) : Finset ℤ :=
  Finset.Icc (h a - 2 * (A : ℤ)) (h a + 2 * (A : ℤ))

/-- Directional `(3A + 1)`-cell window `[pos - A, pos + 2A]` (`up = true`) or
`[pos - 2A, pos + A]` (`up = false`). -/
def coarseDirWin (pos : ℤ) (A : ℕ) (up : Bool) : Finset ℤ :=
  if up then Finset.Icc (pos - (A : ℤ)) (pos + 2 * (A : ℤ))
  else Finset.Icc (pos - 2 * (A : ℤ)) (pos + (A : ℤ))

theorem card_coarseDirWin (pos : ℤ) (A : ℕ) (up : Bool) :
    (coarseDirWin pos A up).card = 3 * A + 1 := by
  cases up <;> simp [coarseDirWin, Int.card_Icc] <;> omega

open Classical in
/-- `A`-filtered S-set of node `J` for trajectory `h` and earlier pass `P'`: cells visited during
`J` outside `coarseAnchorWin h (firstStep J) A` whose last visit before `firstStep J` lies in
`passSteps p P'`. -/
noncomputable def sSetCoarse (h : ℕ → ℤ) (p : ℕ → ℕ) (A : ℕ) (J : Finset ℕ) (P' : ℕ) : Finset ℤ :=
  (J.image h).filter (fun c => c ∉ coarseAnchorWin h (firstStep J) A ∧
    ∃ σ ∈ passSteps p P', IsLastVisitTo h c (firstStep J) σ)

open Classical in
/-- Steps of `passSteps p P'` visiting `[min S, max S]` where `S = sSetCoarse h p A J P'`. -/
noncomputable def childUCoarse (h : ℕ → ℤ) (p : ℕ → ℕ) (A : ℕ) (J : Finset ℕ) (P' : ℕ) : Finset ℕ :=
  if hS : (sSetCoarse h p A J P').Nonempty then
    (passSteps p P').filter (fun τ =>
      (sSetCoarse h p A J P').min' hS ≤ h τ ∧ h τ ≤ (sSetCoarse h p A J P').max' hS)
  else ∅

open Classical in
/-- Convex-hull child node in pass `P'`: `[min U, max U]` when `U = childUCoarse h p A J P'` is
nonempty, else `∅`. -/
noncomputable def childNodeCoarse (h : ℕ → ℤ) (p : ℕ → ℕ) (A : ℕ) (J : Finset ℕ) (P' : ℕ) :
    Finset ℕ :=
  if hU : (childUCoarse h p A J P').Nonempty then
    Finset.Icc ((childUCoarse h p A J P').min' hU) ((childUCoarse h p A J P').max' hU)
  else ∅

/-- Node at address `(P₀, l)` in the `A`-coarse dependency forest. -/
noncomputable def forestNodeCoarse (M : TM) (w : List Bool) (p : ℕ → ℕ) (A o₁ o₂ P₀ : ℕ)
    (l : List (ℕ × Fin M.k)) : Finset ℕ :=
  l.foldl (fun J x => childNodeCoarse (fun τ => workTraj M w τ x.2) p A J x.1)
    (rootNode (outLen M w) p o₁ o₂ P₀)

/-- Coarse dependency forest of `[o₁, o₂)` restricted to bank tapes `B_bank`. -/
noncomputable def forestCoarse (M : TM) (w : List Bool) (B_bank : Finset (Fin M.k))
    (p : ℕ → ℕ) (r A o₁ o₂ : ℕ) : Finset ℕ :=
  (bankAddresses B_bank r).biUnion (fun α => forestNodeCoarse M w p A o₁ o₂ α.1 α.2)

theorem mem_sSetCoarse {h : ℕ → ℤ} {p : ℕ → ℕ} {A : ℕ} {J : Finset ℕ} {P' : ℕ} {c : ℤ} :
    c ∈ sSetCoarse h p A J P' ↔ (∃ τ ∈ J, h τ = c) ∧
      c ∉ coarseAnchorWin h (firstStep J) A ∧
      ∃ σ ∈ passSteps p P', IsLastVisitTo h c (firstStep J) σ := by
  classical
  simp only [sSetCoarse, Finset.mem_filter, Finset.mem_image]

theorem childUCoarse_subset (h : ℕ → ℤ) (p : ℕ → ℕ) (A : ℕ) (J : Finset ℕ) (P' : ℕ) :
    childUCoarse h p A J P' ⊆ passSteps p P' := by
  unfold childUCoarse
  split_ifs
  · exact Finset.filter_subset _ _
  · exact Finset.empty_subset _

theorem childNodeCoarse_subset (h : ℕ → ℤ) (p : ℕ → ℕ) (A : ℕ) (J : Finset ℕ) (P' : ℕ) :
    childNodeCoarse h p A J P' ⊆ passSteps p P' := by
  unfold childNodeCoarse
  split_ifs with hU
  · intro τ hτ
    rw [Finset.mem_Icc] at hτ
    have hmin := mem_passSteps.1 (childUCoarse_subset h p A J P' (Finset.min'_mem _ hU))
    have hmax := mem_passSteps.1 (childUCoarse_subset h p A J P' (Finset.max'_mem _ hU))
    exact mem_passSteps.2 ⟨by omega, by omega⟩
  · exact Finset.empty_subset _

theorem childNodeCoarse_convex (h : ℕ → ℤ) (p : ℕ → ℕ) (A : ℕ) (J : Finset ℕ) (P' : ℕ) :
    IsConvex (childNodeCoarse h p A J P') := by
  unfold childNodeCoarse
  split_ifs with hU
  · intro x hx y hy z hxz hzy
    rw [Finset.mem_Icc] at hx hy ⊢
    exact ⟨by omega, by omega⟩
  · intro x hx
    exact absurd hx (Finset.notMem_empty x)

theorem mem_childUCoarse_of_sSetCoarse {h : ℕ → ℤ} {p : ℕ → ℕ} {A : ℕ} {J : Finset ℕ} {P' σ : ℕ}
    (hσ : σ ∈ passSteps p P') (hc : h σ ∈ sSetCoarse h p A J P') :
    σ ∈ childUCoarse h p A J P' := by
  classical
  have hS : (sSetCoarse h p A J P').Nonempty := ⟨h σ, hc⟩
  unfold childUCoarse
  rw [dite_eq_left hS, Finset.mem_filter]
  exact ⟨hσ, Finset.min'_le _ _ hc, Finset.le_max' _ _ hc⟩

theorem mem_childNodeCoarse_of_sSetCoarse {h : ℕ → ℤ} {p : ℕ → ℕ} {A : ℕ} {J : Finset ℕ}
    {P' σ : ℕ} (hσ : σ ∈ passSteps p P') (hc : h σ ∈ sSetCoarse h p A J P') :
    σ ∈ childNodeCoarse h p A J P' := by
  classical
  have hUσ : σ ∈ childUCoarse h p A J P' := mem_childUCoarse_of_sSetCoarse hσ hc
  have hU : (childUCoarse h p A J P').Nonempty := ⟨σ, hUσ⟩
  unfold childNodeCoarse
  rw [dite_eq_left hU, Finset.mem_Icc]
  exact ⟨Finset.min'_le _ _ hUσ, Finset.le_max' _ _ hUσ⟩

theorem foldl_coarse_inv {M : TM} {w : List Bool} {p : ℕ → ℕ} {r A : ℕ} :
    ∀ (l : List (ℕ × Fin M.k)) (J : Finset ℕ) (P : ℕ), P < r → J ⊆ passSteps p P → IsConvex J →
      l ∈ addrsBelow M.k P →
      l.foldl (fun J x => childNodeCoarse (fun τ => workTraj M w τ x.2) p A J x.1) J ⊆
          passSteps p (lastPass l P) ∧
        IsConvex (l.foldl (fun J x => childNodeCoarse (fun τ => workTraj M w τ x.2) p A J x.1) J)
  | [], J, P, _, hJ, hc, _ => ⟨hJ, hc⟩
  | x :: l, J, P, hP, _, _, hl => by
    rcases mem_addrsBelow.1 hl with h | ⟨y, l', he, hy, hl'⟩
    · exact absurd h (List.cons_ne_nil _ _)
    · obtain ⟨rfl, rfl⟩ := List.cons.inj he
      simp only [List.foldl_cons, lastPass]
      exact foldl_coarse_inv l _ x.1 (by omega) (childNodeCoarse_subset _ _ _ _ _)
        (childNodeCoarse_convex _ _ _ _ _) hl'

theorem forestNodeCoarse_inv {M : TM} {w : List Bool} {p : ℕ → ℕ} {B_bank : Finset (Fin M.k)}
    {r A : ℕ} {α : ℕ × List (ℕ × Fin M.k)} (hα : α ∈ bankAddresses B_bank r) (o₁ o₂ : ℕ) :
    forestNodeCoarse M w p A o₁ o₂ α.1 α.2 ⊆ passSteps p (lastPass α.2 α.1) ∧
      IsConvex (forestNodeCoarse M w p A o₁ o₂ α.1 α.2) := by
  have hα' := bankAddresses_subset_addresses B_bank r hα
  exact foldl_coarse_inv (r := r) α.2 _ α.1 (mem_addresses.1 hα').1 (rootNode_subset _ _ _ _)
    (rootNode_convex M w _ _ _) (mem_addresses.1 hα').2

theorem forestNodeCoarse_append {M : TM} {w : List Bool} {p : ℕ → ℕ} (A o₁ o₂ P₀ : ℕ)
    (l : List (ℕ × Fin M.k)) (P' : ℕ) (t : Fin M.k) :
    forestNodeCoarse M w p A o₁ o₂ P₀ (l ++ [(P', t)]) =
      childNodeCoarse (fun τ => workTraj M w τ t) p A (forestNodeCoarse M w p A o₁ o₂ P₀ l) P' := by
  simp [forestNodeCoarse, List.foldl_append]

theorem forestCoarse_subset {M : TM} {w : List Bool} {T' r A_in A : ℕ}
    {B_bank : Finset (Fin M.k)} {S : Fin M.k → ℕ} {p : ℕ → ℕ}
    (hp : CoarseWorkspacePartition M w T' r B_bank A_in A S p) (o₁ o₂ : ℕ) :
    ∀ τ ∈ forestCoarse M w B_bank p r A o₁ o₂, τ < T' := by
  intro τ hτ
  obtain ⟨α, hα, hτα⟩ := Finset.mem_biUnion.1 hτ
  have h1 := mem_passSteps.1 ((forestNodeCoarse_inv hα o₁ o₂).1 hτα)
  have hlt : lastPass α.2 α.1 < r := lastPass_lt (bankAddresses_subset_addresses B_bank r hα)
  have h2 := cwp_le_T hp (show lastPass α.2 α.1 + 1 ≤ r from hlt)
  omega

theorem exists_append_step_mem_forestCoarse {M : TM} {w : List Bool} {T' r A_in A : ℕ}
    {B_bank : Finset (Fin M.k)} {S : Fin M.k → ℕ} {p : ℕ → ℕ}
    (hp : CoarseWorkspacePartition M w T' r B_bank A_in A S p) {o₁ o₂ o : ℕ}
    (ho₁ : o₁ ≤ o) (ho₂ : o < o₂) (ho : o < (run M w T').outRev.length) :
    ∃ τ < T', τ ∈ forestCoarse M w B_bank p r A o₁ o₂ ∧
      (outBit M w τ).isSome ∧ (run M w τ).outRev.length = o := by
  classical
  obtain ⟨τ, hτT, hsome, hlen⟩ := exists_append_step w ho
  obtain ⟨P, hPr, hP1, hP2⟩ := cwp_exists_pass hp hτT
  refine ⟨τ, hτT, Finset.mem_biUnion.2 ⟨(P, []),
    mem_bankAddresses.2 ⟨hPr, nil_mem_bankAddrsBelow _ _⟩, ?_⟩, hsome, hlen⟩
  show τ ∈ rootNode (outLen M w) p o₁ o₂ P
  have := outRev_length_succ (M := M) w τ
  simp only [hsome, ite_true] at this
  rw [rootNode, Finset.mem_filter, mem_passSteps]
  exact ⟨⟨hP1, hP2⟩, by simp only [outLen]; omega, by simp only [outLen]; omega⟩

/-- Directional `(3A + 1)`-cell confinement: on an `A`-non-decreasing (`up = true`) or
`A`-non-increasing (`up = false`) pass containing `J`, every `τ ∈ J` inside `coarseAnchorWin`
visits `coarseDirWin (h (firstStep J)) A up`. -/
theorem mem_coarseDirWin_of_mem_coarseAnchorWin_up {h : ℕ → ℤ} {lo hi A : ℕ}
    (hinc : ∀ t t', lo ≤ t → t ≤ t' → t' < hi → h t - (A : ℤ) ≤ h t')
    {J : Finset ℕ} (hJ : J ⊆ Finset.Ico lo hi) {τ : ℕ} (hτ : τ ∈ J)
    (hwin : h τ ∈ coarseAnchorWin h (firstStep J) A) :
    h τ ∈ coarseDirWin (h (firstStep J)) A true := by
  have haJ : firstStep J ∈ J := firstStep_mem ⟨τ, hτ⟩
  have ha_mem := Finset.mem_Ico.1 (hJ haJ)
  have hτ_mem := Finset.mem_Ico.1 (hJ hτ)
  have haτ : firstStep J ≤ τ := firstStep_le hτ
  have h1 := hinc (firstStep J) τ ha_mem.1 haτ hτ_mem.2
  simp only [coarseAnchorWin, Finset.mem_Icc] at hwin
  simp only [coarseDirWin, ite_true, Finset.mem_Icc]
  omega

theorem mem_coarseDirWin_of_mem_coarseAnchorWin_dn {h : ℕ → ℤ} {lo hi A : ℕ}
    (hdec : ∀ t t', lo ≤ t → t ≤ t' → t' < hi → h t' ≤ h t + (A : ℤ))
    {J : Finset ℕ} (hJ : J ⊆ Finset.Ico lo hi) {τ : ℕ} (hτ : τ ∈ J)
    (hwin : h τ ∈ coarseAnchorWin h (firstStep J) A) :
    h τ ∈ coarseDirWin (h (firstStep J)) A false := by
  have haJ : firstStep J ∈ J := firstStep_mem ⟨τ, hτ⟩
  have ha_mem := Finset.mem_Ico.1 (hJ haJ)
  have hτ_mem := Finset.mem_Ico.1 (hJ hτ)
  have haτ : firstStep J ≤ τ := firstStep_le hτ
  have h1 := hdec (firstStep J) τ ha_mem.1 haτ hτ_mem.2
  simp only [coarseAnchorWin, Finset.mem_Icc] at hwin
  simp [coarseDirWin]
  omega

/-- **Coarse Fresh-Cell Lemma (Step 2)**: if `h` is `A`-coarsely monotone on `[lo, hi)`, `J ⊆ [lo, hi)`,
`τ ∈ J`, and `h τ ∉ coarseAnchorWin h (firstStep J) A`, then no `ρ ∈ [lo, firstStep J)` visits `h τ`. -/
theorem coarse_pass_fresh {h : ℕ → ℤ} {lo hi A : ℕ} (hm : CoarseMonoOnInterval h lo hi A)
    {J : Finset ℕ} (hJ : J ⊆ Finset.Ico lo hi) {τ ρ : ℕ} (hτ : τ ∈ J)
    (hout : h τ ∉ coarseAnchorWin h (firstStep J) A)
    (hlo : lo ≤ ρ) (hρa : ρ < firstStep J) : h ρ ≠ h τ := by
  intro heq
  have haJ : firstStep J ∈ J := firstStep_mem ⟨τ, hτ⟩
  have ha_mem := Finset.mem_Ico.1 (hJ haJ)
  have hτ_mem := Finset.mem_Ico.1 (hJ hτ)
  have haτ : firstStep J ≤ τ := firstStep_le hτ
  simp only [coarseAnchorWin, Finset.mem_Icc, not_and_or] at hout
  rcases hm with hinc | hdec
  · have h1 := hinc (firstStep J) τ ha_mem.1 haτ hτ_mem.2
    have h2 := hinc ρ (firstStep J) hlo (le_of_lt hρa) ha_mem.2
    rcases hout with hlt | hgt <;> omega
  · have h1 := hdec (firstStep J) τ ha_mem.1 haτ hτ_mem.2
    have h2 := hdec ρ (firstStep J) hlo (le_of_lt hρa) ha_mem.2
    rcases hout with hlt | hgt <;> omega

/-- `(A + 1)`-cell separation between `sSetCoarse` of time-ordered nodes inside an `A`-coarse pass. -/
theorem sSetCoarse_sep {h : ℕ → ℤ} {p : ℕ → ℕ} {A P P' : ℕ} {J₁ J₂ : Finset ℕ}
    (hm : CoarseMonoOnInterval h (p P) (p (P + 1)) A)
    (h1 : J₁ ⊆ passSteps p P) (h2 : J₂ ⊆ passSteps p P)
    (hsep : ∀ x ∈ J₁, ∀ y ∈ J₂, x < y) :
    (∀ c ∈ sSetCoarse h p A J₁ P', ∀ c' ∈ sSetCoarse h p A J₂ P', c + (A : ℤ) < c') ∨
      (∀ c ∈ sSetCoarse h p A J₁ P', ∀ c' ∈ sSetCoarse h p A J₂ P', c' + (A : ℤ) < c) := by
  rcases hm with hinc | hdec
  · left
    intro c hc c' hc'
    rw [mem_sSetCoarse] at hc hc'
    obtain ⟨⟨τ₁, hτ₁, rfl⟩, -, -⟩ := hc
    obtain ⟨⟨τ₂, hτ₂, rfl⟩, hout₂, -⟩ := hc'
    have ha₂ : firstStep J₂ ∈ J₂ := firstStep_mem ⟨τ₂, hτ₂⟩
    have hτ₁a₂ : τ₁ < firstStep J₂ := hsep τ₁ hτ₁ _ ha₂
    have ha₂τ₂ : firstStep J₂ ≤ τ₂ := firstStep_le hτ₂
    have m1 := mem_passSteps.1 (h1 hτ₁)
    have m2 := mem_passSteps.1 (h2 ha₂)
    have m3 := mem_passSteps.1 (h2 hτ₂)
    have e1 := hinc τ₁ (firstStep J₂) m1.1 (le_of_lt hτ₁a₂) m2.2
    have e2 := hinc (firstStep J₂) τ₂ m2.1 ha₂τ₂ m3.2
    simp only [coarseAnchorWin, Finset.mem_Icc, not_and_or] at hout₂
    rcases hout₂ with hlt | hgt <;> omega
  · right
    intro c hc c' hc'
    rw [mem_sSetCoarse] at hc hc'
    obtain ⟨⟨τ₁, hτ₁, rfl⟩, -, -⟩ := hc
    obtain ⟨⟨τ₂, hτ₂, rfl⟩, hout₂, -⟩ := hc'
    have ha₂ : firstStep J₂ ∈ J₂ := firstStep_mem ⟨τ₂, hτ₂⟩
    have hτ₁a₂ : τ₁ < firstStep J₂ := hsep τ₁ hτ₁ _ ha₂
    have ha₂τ₂ : firstStep J₂ ≤ τ₂ := firstStep_le hτ₂
    have m1 := mem_passSteps.1 (h1 hτ₁)
    have m2 := mem_passSteps.1 (h2 ha₂)
    have m3 := mem_passSteps.1 (h2 hτ₂)
    have e1 := hdec τ₁ (firstStep J₂) m1.1 (le_of_lt hτ₁a₂) m2.2
    have e2 := hdec (firstStep J₂) τ₂ m2.1 ha₂τ₂ m3.2
    simp only [coarseAnchorWin, Finset.mem_Icc, not_and_or] at hout₂
    rcases hout₂ with hlt | hgt <;> omega

/-- Children in an `A`-coarse pass `P'` whose `sSetCoarse` sets have gap `> A` are `TimeSep`. -/
theorem childNodeCoarse_sep {h : ℕ → ℤ} {p : ℕ → ℕ} {A P' : ℕ} {J₁ J₂ : Finset ℕ}
    (hm' : CoarseMonoOnInterval h (p P') (p (P' + 1)) A)
    (hc : ∀ c ∈ sSetCoarse h p A J₁ P', ∀ c' ∈ sSetCoarse h p A J₂ P', c + (A : ℤ) < c') :
    TimeSep (childNodeCoarse h p A J₁ P') (childNodeCoarse h p A J₂ P') := by
  classical
  have hU_gap : ∀ x ∈ childUCoarse h p A J₁ P', ∀ y ∈ childUCoarse h p A J₂ P',
      h x + (A : ℤ) < h y := by
    intro x hx y hy
    unfold childUCoarse at hx hy
    split_ifs at hx with hS₁
    · split_ifs at hy with hS₂
      · rw [Finset.mem_filter] at hx hy
        have hgap := hc _ (Finset.max'_mem _ hS₁) _ (Finset.min'_mem _ hS₂)
        linarith [hx.2.2, hy.2.1]
      · exact absurd hy (Finset.notMem_empty y)
    · exact absurd hx (Finset.notMem_empty x)
  rcases hm' with hinc | hdec
  · left
    intro x hx y hy
    unfold childNodeCoarse at hx hy
    split_ifs at hx with hU₁
    · split_ifs at hy with hU₂
      · rw [Finset.mem_Icc] at hx hy
        set x_max := (childUCoarse h p A J₁ P').max' hU₁
        set y_min := (childUCoarse h p A J₂ P').min' hU₂
        have hxm_mem : x_max ∈ childUCoarse h p A J₁ P' := Finset.max'_mem _ hU₁
        have hym_mem : y_min ∈ childUCoarse h p A J₂ P' := Finset.min'_mem _ hU₂
        have mx := mem_passSteps.1 (childUCoarse_subset h p A J₁ P' hxm_mem)
        have my := mem_passSteps.1 (childUCoarse_subset h p A J₂ P' hym_mem)
        have hlt : x_max < y_min := by
          by_contra hge
          push Not at hge
          have := hinc y_min x_max my.1 hge mx.2
          have := hU_gap x_max hxm_mem y_min hym_mem
          omega
        omega
      · exact absurd hy (Finset.notMem_empty y)
    · exact absurd hx (Finset.notMem_empty x)
  · right
    intro x hx y hy
    unfold childNodeCoarse at hx hy
    split_ifs at hx with hU₁
    · split_ifs at hy with hU₂
      · rw [Finset.mem_Icc] at hx hy
        set x_min := (childUCoarse h p A J₁ P').min' hU₁
        set y_max := (childUCoarse h p A J₂ P').max' hU₂
        have hxm_mem : x_min ∈ childUCoarse h p A J₁ P' := Finset.min'_mem _ hU₁
        have hym_mem : y_max ∈ childUCoarse h p A J₂ P' := Finset.max'_mem _ hU₂
        have mx := mem_passSteps.1 (childUCoarse_subset h p A J₁ P' hxm_mem)
        have my := mem_passSteps.1 (childUCoarse_subset h p A J₂ P' hym_mem)
        have hlt : y_max < x_min := by
          by_contra hge
          push Not at hge
          have := hdec x_min y_max mx.1 hge my.2
          have := hU_gap x_min hxm_mem y_max hym_mem
          omega
        omega
      · exact absurd hy (Finset.notMem_empty y)
    · exact absurd hx (Finset.notMem_empty x)

theorem childNodeCoarse_timeSep {h : ℕ → ℤ} {p : ℕ → ℕ} {A P P' : ℕ} {J₁ J₂ : Finset ℕ}
    (hm : CoarseMonoOnInterval h (p P) (p (P + 1)) A)
    (hm' : CoarseMonoOnInterval h (p P') (p (P' + 1)) A)
    (h1 : J₁ ⊆ passSteps p P) (h2 : J₂ ⊆ passSteps p P) (hsep : TimeSep J₁ J₂) :
    TimeSep (childNodeCoarse h p A J₁ P') (childNodeCoarse h p A J₂ P') := by
  rcases hsep with hsep | hsep
  · rcases sSetCoarse_sep (P' := P') hm h1 h2 hsep with hc | hc
    · exact childNodeCoarse_sep hm' hc
    · exact timeSep_symm (childNodeCoarse_sep hm' (fun c hc' c' hc'' => hc c' hc'' c hc'))
  · rcases sSetCoarse_sep (P' := P') hm h2 h1 (fun x hx y hy => hsep y hy x hx) with hc | hc
    · exact timeSep_symm (childNodeCoarse_sep hm' hc)
    · exact childNodeCoarse_sep hm' (fun c hc' c' hc'' => hc c' hc'' c hc')

theorem foldl_coarse_timeSep {M : TM} {w : List Bool} {T' r A_in A : ℕ}
    {B_bank : Finset (Fin M.k)} {S : Fin M.k → ℕ} {p : ℕ → ℕ}
    (hp : CoarseWorkspacePartition M w T' r B_bank A_in A S p) :
    ∀ (l : List (ℕ × Fin M.k)) (J₁ J₂ : Finset ℕ) (P : ℕ), P < r → J₁ ⊆ passSteps p P →
      J₂ ⊆ passSteps p P → TimeSep J₁ J₂ → l ∈ bankAddrsBelow B_bank P →
      TimeSep (l.foldl (fun J x => childNodeCoarse (fun τ => workTraj M w τ x.2) p A J x.1) J₁)
        (l.foldl (fun J x => childNodeCoarse (fun τ => workTraj M w τ x.2) p A J x.1) J₂)
  | [], _, _, _, _, _, _, hsep, _ => hsep
  | x :: l, J₁, J₂, P, hP, h1, h2, hsep, hl => by
    rcases mem_bankAddrsBelow.1 hl with h | ⟨y, l', he, hy, hyt, hl'⟩
    · exact absurd h (List.cons_ne_nil _ _)
    · obtain ⟨rfl, rfl⟩ := List.cons.inj he
      simp only [List.foldl_cons]
      exact foldl_coarse_timeSep hp l _ _ x.1 (by omega) (childNodeCoarse_subset _ _ _ _ _)
        (childNodeCoarse_subset _ _ _ _ _)
        (childNodeCoarse_timeSep (hp.2.2.2.2.1 P hP x.2 hyt)
          (hp.2.2.2.2.1 x.1 (by omega) x.2 hyt) h1 h2 hsep)
        hl'

theorem forestNodeCoarse_timeSep {M : TM} {w : List Bool} {T' r A_in A : ℕ}
    {B_bank : Finset (Fin M.k)} {S : Fin M.k → ℕ} {p : ℕ → ℕ}
    (hp : CoarseWorkspacePartition M w T' r B_bank A_in A S p)
    {α : ℕ × List (ℕ × Fin M.k)} (hα : α ∈ bankAddresses B_bank r)
    {o₁ o₂ o₁' o₂' : ℕ} (h : o₂ ≤ o₁') :
    TimeSep (forestNodeCoarse M w p A o₁ o₂ α.1 α.2) (forestNodeCoarse M w p A o₁' o₂' α.1 α.2) :=
  foldl_coarse_timeSep hp α.2 _ _ α.1 (mem_bankAddresses.1 hα).1 (rootNode_subset _ _ _ _)
    (rootNode_subset _ _ _ _) (Or.inl (rootNode_before M w h)) (mem_bankAddresses.1 hα).2

/-- **Coarse time-ordered input chain (Step 3.1)**: for pairwise `TimeSep` step sets `N s ⊆ [lo, hi)`
under `A_in`-coarse input monotonicity, `∑_{s ∈ S} |readSet ip L (N s)| ≤ L + (|S| - 1)(2 A_in + 1)`. -/
theorem read_chain_coarse_abstract {ip : ℕ → ℤ} {lo hi L A_in : ℕ}
    (hm : CoarseMonoOnInterval ip lo hi A_in) {ι : Type*}
    (S : Finset ι) (_hS : S.Nonempty) (N : ι → Finset ℕ)
    (hN : ∀ s ∈ S, ∀ τ ∈ N s, lo ≤ τ ∧ τ < hi)
    (hsep : ∀ s ∈ S, ∀ s' ∈ S, s ≠ s' → TimeSep (N s) (N s')) :
    ∑ s ∈ S, (readSet ip L (N s)).card ≤ L + (S.card - 1) * (2 * A_in + 1) := by
  classical
  set R : ι → Finset ℕ := fun s => readSet ip L (N s) with hR
  have key : ∀ S' : Finset ι, S' ⊆ S →
      ∑ s ∈ S', (R s).card ≤ (S'.biUnion R).card + (S'.card - 1) * (2 * A_in + 1) := by
    intro S'
    refine Finset.induction_on_max_value
      (motive := fun S' => S' ⊆ S →
        ∑ s ∈ S', (R s).card ≤ (S'.biUnion R).card + (S'.card - 1) * (2 * A_in + 1))
      (fun s => firstStep (N s)) S' (fun _ => by simp) ?_
    intro x S' hx hmax ih hsub
    have hxS : x ∈ S := hsub (Finset.mem_insert_self _ _)
    have ih' := ih (fun y hy => hsub (Finset.mem_insert_of_mem hy))
    rw [Finset.sum_insert hx, Finset.biUnion_insert, Finset.card_insert_of_notMem hx]
    rcases S'.eq_empty_or_nonempty with he | hne
    · subst he; simp
    have hinter : (R x ∩ S'.biUnion R).card ≤ 2 * A_in + 1 := by
      have hsub_win : (R x ∩ S'.biUnion R).image (fun d : ℕ => (d : ℤ)) ⊆
          Finset.Icc (ip (firstStep (N x)) - (A_in : ℤ)) (ip (firstStep (N x)) + (A_in : ℤ)) := by
        intro z hz
        obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 hz
        rw [Finset.mem_inter, Finset.mem_biUnion] at hd
        obtain ⟨hdx, y, hy, hdy⟩ := hd
        simp only [hR, readSet, Finset.mem_filter, Finset.mem_range] at hdx hdy
        obtain ⟨-, τ, hτ, hτd⟩ := hdx
        obtain ⟨-, τ', hτ', hτ'd⟩ := hdy
        have hyS : y ∈ S := hsub (Finset.mem_insert_of_mem hy)
        have hyx : y ≠ x := fun h => hx (h ▸ hy)
        have ha : firstStep (N x) ∈ N x := firstStep_mem ⟨τ, hτ⟩
        have haτ : firstStep (N x) ≤ τ := firstStep_le hτ
        have hτ'a : τ' < firstStep (N x) := by
          rcases hsep y hyS x hxS hyx with h | h
          · exact h τ' hτ' _ ha
          · exfalso
            have h1 := h (firstStep (N y)) (firstStep_mem ⟨τ', hτ'⟩) _ ha
            have h2 : firstStep (N y) ≤ firstStep (N x) := hmax y hy
            omega
        have m1 := hN x hxS τ hτ
        have m2 := hN x hxS _ ha
        have m3 := hN y hyS τ' hτ'
        rw [Finset.mem_Icc]
        rcases hm with hinc | hdec
        · have e1 := hinc τ' _ m3.1 (le_of_lt hτ'a) m2.2
          have e2 := hinc _ τ m2.1 haτ m1.2
          omega
        · have e1 := hdec τ' _ m3.1 (le_of_lt hτ'a) m2.2
          have e2 := hdec _ τ m2.1 haτ m1.2
          omega
      have hinj : Set.InjOn (fun d : ℕ => (d : ℤ)) ↑(R x ∩ S'.biUnion R) := by
        intro d₁ _ d₂ _ heq; exact Int.ofNat.inj heq
      calc (R x ∩ S'.biUnion R).card
          = ((R x ∩ S'.biUnion R).image (fun d : ℕ => (d : ℤ))).card :=
            (Finset.card_image_of_injOn hinj).symm
        _ ≤ (Finset.Icc (ip (firstStep (N x)) - (A_in : ℤ))
              (ip (firstStep (N x)) + (A_in : ℤ))).card := Finset.card_le_card hsub_win
        _ = 2 * A_in + 1 := by rw [Int.card_Icc]; omega
    have hu := Finset.card_union_add_card_inter (R x) (S'.biUnion R)
    have hpos := hne.card_pos
    have hmul : (S'.card + 1 - 1) * (2 * A_in + 1) =
        (S'.card - 1) * (2 * A_in + 1) + (2 * A_in + 1) := by
      rw [Nat.add_sub_cancel]
      have : S'.card = (S'.card - 1) + 1 := by omega
      conv_lhs => rw [this]
      ring
    omega
  have h1 := key S (subset_refl _)
  have h2 : (S.biUnion R).card ≤ L := by
    calc (S.biUnion R).card ≤ (Finset.range L).card := Finset.card_le_card (by
          intro d hd
          rw [Finset.mem_biUnion] at hd
          obtain ⟨s, -, hds⟩ := hd
          simp only [hR, readSet, Finset.mem_filter] at hds
          exact hds.1)
      _ = L := Finset.card_range L
  dsimp only [R] at h1 h2
  omega

/-- **Coarse coverage per address (Step 3.2)**: `≤ (γ + 1) * n * b + 2 * A_in`. -/
theorem coverage_per_address_coarse {M : TM} {w : List Bool} {n b T' r γ A_in A : ℕ}
    {B_bank : Finset (Fin M.k)} {S : Fin M.k → ℕ} {p : ℕ → ℕ}
    (hp : CoarseWorkspacePartition M w T' r B_bank A_in A S p)
    {α : ℕ × List (ℕ × Fin M.k)} (hα : α ∈ bankAddresses B_bank r) :
    ∑ s ∈ Finset.range (numGroups n γ),
      (combSet n b (segLo n b γ s) (segHi n b γ s) ∩
        readSet (inTraj M w) (n * n * b)
          (forestNodeCoarse M w p A (segLo n b γ s) (segHi n b γ s) α.1 α.2)).card ≤
      (γ + 1) * n * b + 2 * A_in := by
  classical
  rcases Nat.eq_zero_or_pos γ with rfl | hγ
  · simp [numGroups]
  replace hγ : 1 ≤ γ := hγ
  rcases Nat.eq_zero_or_pos b with hb | hb
  · subst hb; simp [combSet]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have : numGroups 0 γ = 0 := by unfold numGroups; exact Nat.div_eq_of_lt (by omega)
    simp [this]
  set G := numGroups n γ
  set R : ℕ → Finset ℕ := fun s => readSet (inTraj M w) (n * n * b)
    (forestNodeCoarse M w p A (segLo n b γ s) (segHi n b γ s) α.1 α.2)
  set C : ℕ → Finset ℕ := fun s => combSet n b (segLo n b γ s) (segHi n b γ s) ∩ R s
  set g : ℕ → ℕ := fun s => min ((s + 1) * γ) n - min (s * γ) n
  have hper : ∀ s, (n * b) * (C s).card ≤ g s * b * ((R s).card + n * b) := by
    intro s
    have hsub : C s ⊆ (R s).filter (fun d => d % (n * b) ∈
        Finset.Ico (min (s * γ) n * b) (min ((s + 1) * γ) n * b)) := by
      intro d hd
      rw [Finset.mem_inter] at hd
      have := combSet_subset_residue n b (min (s * γ) n) (min ((s + 1) * γ) n) hd.1
      rw [Finset.mem_filter] at this ⊢
      exact ⟨hd.2, this.2⟩
    have hconv : IsConvex (R s) :=
      readSet_convex (unitSteps_inTraj M w) (forestNodeCoarse_inv hα _ _).2
    have := residue_count (Res := Finset.Ico (min (s * γ) n * b) (min ((s + 1) * γ) n * b))
      (m := n * b) hconv
    rw [Nat.card_Ico] at this
    calc (n * b) * (C s).card ≤ (n * b) * ((R s).filter (fun d => d % (n * b) ∈
          Finset.Ico (min (s * γ) n * b) (min ((s + 1) * γ) n * b))).card :=
          Nat.mul_le_mul_left _ (Finset.card_le_card hsub)
      _ ≤ (min ((s + 1) * γ) n * b - min (s * γ) n * b) * ((R s).card + n * b) := this
      _ = g s * b * ((R s).card + n * b) := by rw [← Nat.sub_mul]
  have hPr : lastPass α.2 α.1 < r := lastPass_lt (bankAddresses_subset_addresses B_bank r hα)
  have hchain : ∑ s ∈ Finset.range G, (R s).card ≤ n * n * b + (G - 1) * (2 * A_in + 1) := by
    have := read_chain_coarse_abstract (L := n * n * b) (hp.2.2.2.1 _ hPr) (Finset.range G)
      (Finset.nonempty_range_iff.2 (Nat.pos_iff_ne_zero.1 (numGroups_pos hγ hn)))
      (fun s => forestNodeCoarse M w p A (segLo n b γ s) (segHi n b γ s) α.1 α.2)
      (fun s _ τ hτ => mem_passSteps.1 ((forestNodeCoarse_inv hα _ _).1 hτ))
      (fun s _ s' _ hss' => by
        rcases Nat.lt_or_gt_of_ne hss' with h | h
        · exact forestNodeCoarse_timeSep hp hα (segLo_mono n b γ (show s + 1 ≤ s' by omega))
        · exact timeSep_symm
            (forestNodeCoarse_timeSep hp hα (segLo_mono n b γ (show s' + 1 ≤ s by omega))))
    simpa [Finset.card_range] using this
  have hsumg : ∑ s ∈ Finset.range G, g s = n := by
    rw [sum_width]; exact min_eq_right (numGroups_mul_ge hγ)
  have h1 : (n * b) * ∑ s ∈ Finset.range G, (C s).card ≤
      ∑ s ∈ Finset.range G, g s * b * ((R s).card + n * b) := by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum (fun s _ => hper s)
  have h2 : ∑ s ∈ Finset.range G, g s * b * ((R s).card + n * b) ≤
      b * (γ * ∑ s ∈ Finset.range G, (R s).card) + b * (n * b) * n := by
    calc ∑ s ∈ Finset.range G, g s * b * ((R s).card + n * b)
        = b * ∑ s ∈ Finset.range G, g s * (R s).card +
            b * (n * b) * ∑ s ∈ Finset.range G, g s := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro s _; ring
      _ ≤ b * (γ * ∑ s ∈ Finset.range G, (R s).card) + b * (n * b) * n := by
          rw [hsumg]
          apply Nat.add_le_add_right
          apply Nat.mul_le_mul_left
          rw [Finset.mul_sum]
          exact Finset.sum_le_sum (fun s _ => Nat.mul_le_mul_right _ (width_le n γ s))
  have h3 : n * ∑ s ∈ Finset.range G, (C s).card ≤
      γ * ∑ s ∈ Finset.range G, (R s).card + n * b * n := by
    have : b * (n * ∑ s ∈ Finset.range G, (C s).card) ≤
        b * (γ * ∑ s ∈ Finset.range G, (R s).card + n * b * n) := by
      calc b * (n * ∑ s ∈ Finset.range G, (C s).card)
          = (n * b) * ∑ s ∈ Finset.range G, (C s).card := by ring
        _ ≤ _ := le_trans h1 h2
        _ = b * (γ * ∑ s ∈ Finset.range G, (R s).card + n * b * n) := by ring
    exact Nat.le_of_mul_le_mul_left this hb
  have h4 : (G - 1) * γ ≤ n - 1 := by
    dsimp only [G]
    exact Nat.le_sub_one_of_lt (numGroups_sub_one_mul hγ hn)
  have h5 : γ * ∑ s ∈ Finset.range G, (R s).card ≤
      γ * (n * n * b) + (n - 1) * (2 * A_in + 1) := by
    calc γ * ∑ s ∈ Finset.range G, (R s).card
        ≤ γ * (n * n * b + (G - 1) * (2 * A_in + 1)) := Nat.mul_le_mul_left _ hchain
      _ = γ * (n * n * b) + ((G - 1) * γ) * (2 * A_in + 1) := by ring
      _ ≤ γ * (n * n * b) + (n - 1) * (2 * A_in + 1) :=
          Nat.add_le_add_left (Nat.mul_le_mul_right _ h4) _
  have h6 : n * ∑ s ∈ Finset.range G, (C s).card <
      n * ((γ + 1) * n * b + 2 * A_in + 1) := by
    have hsub_eq : (n - 1) * (2 * A_in + 1) + 2 * A_in + 1 = n * (2 * A_in + 1) := by
      have : n - 1 + 1 = n := by omega
      calc (n - 1) * (2 * A_in + 1) + 2 * A_in + 1
          = (n - 1 + 1) * (2 * A_in + 1) := by ring
        _ = n * (2 * A_in + 1) := by rw [this]
    calc n * ∑ s ∈ Finset.range G, (C s).card
        ≤ γ * ∑ s ∈ Finset.range G, (R s).card + n * b * n := h3
      _ ≤ γ * (n * n * b) + (n - 1) * (2 * A_in + 1) + n * b * n :=
          Nat.add_le_add_right h5 _
      _ < n * ((γ + 1) * n * b + 2 * A_in + 1) := by
          have hrhs : n * ((γ + 1) * n * b + 2 * A_in + 1) =
              γ * (n * n * b) + n * (2 * A_in + 1) + n * b * n := by ring
          omega
  exact Nat.le_of_lt_succ (Nat.lt_of_mul_lt_mul_left h6)

theorem coverage_grouped_coarse {M : TM} {w : List Bool} {n b T' r γ A_in A : ℕ}
    {B_bank : Finset (Fin M.k)} {S : Fin M.k → ℕ} {p : ℕ → ℕ}
    (hp : CoarseWorkspacePartition M w T' r B_bank A_in A S p) :
    ∑ s ∈ Finset.range (numGroups n γ),
      (combSet n b (segLo n b γ s) (segHi n b γ s) ∩
        readSet (inTraj M w) (n * n * b)
          (forestCoarse M w B_bank p r A (segLo n b γ s) (segHi n b γ s))).card ≤
      (bankAddresses B_bank r).card * ((γ + 1) * n * b + 2 * A_in) := by
  classical
  have hper_group : ∀ s, (combSet n b (segLo n b γ s) (segHi n b γ s) ∩
      readSet (inTraj M w) (n * n * b)
        (forestCoarse M w B_bank p r A (segLo n b γ s) (segHi n b γ s))).card ≤
      ∑ α ∈ bankAddresses B_bank r,
        (combSet n b (segLo n b γ s) (segHi n b γ s) ∩
          readSet (inTraj M w) (n * n * b)
            (forestNodeCoarse M w p A (segLo n b γ s) (segHi n b γ s) α.1 α.2)).card := by
    intro s
    have hsub : combSet n b (segLo n b γ s) (segHi n b γ s) ∩
        readSet (inTraj M w) (n * n * b)
          (forestCoarse M w B_bank p r A (segLo n b γ s) (segHi n b γ s)) ⊆
        (bankAddresses B_bank r).biUnion (fun α =>
          combSet n b (segLo n b γ s) (segHi n b γ s) ∩
            readSet (inTraj M w) (n * n * b)
              (forestNodeCoarse M w p A (segLo n b γ s) (segHi n b γ s) α.1 α.2)) := by
      intro d hd
      rw [Finset.mem_inter] at hd
      simp only [readSet, forestCoarse, Finset.mem_filter, Finset.mem_biUnion] at hd
      obtain ⟨hdc, hdL, τ, ⟨α, hα, hτα⟩, hτd⟩ := hd
      rw [Finset.mem_biUnion]
      refine ⟨α, hα, Finset.mem_inter.2 ⟨hdc, ?_⟩⟩
      simp only [readSet, Finset.mem_filter]
      exact ⟨hdL, τ, hτα, hτd⟩
    exact (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  calc ∑ s ∈ Finset.range (numGroups n γ), _
      ≤ ∑ s ∈ Finset.range (numGroups n γ), ∑ α ∈ bankAddresses B_bank r,
          (combSet n b (segLo n b γ s) (segHi n b γ s) ∩
            readSet (inTraj M w) (n * n * b)
              (forestNodeCoarse M w p A (segLo n b γ s) (segHi n b γ s) α.1 α.2)).card :=
        Finset.sum_le_sum (fun s _ => hper_group s)
    _ = ∑ α ∈ bankAddresses B_bank r, ∑ s ∈ Finset.range (numGroups n γ),
          (combSet n b (segLo n b γ s) (segHi n b γ s) ∩
            readSet (inTraj M w) (n * n * b)
              (forestNodeCoarse M w p A (segLo n b γ s) (segHi n b γ s) α.1 α.2)).card :=
        Finset.sum_comm
    _ ≤ ∑ _α ∈ bankAddresses B_bank r, ((γ + 1) * n * b + 2 * A_in) :=
        Finset.sum_le_sum (fun α hα => coverage_per_address_coarse hp hα)
    _ = (bankAddresses B_bank r).card * ((γ + 1) * n * b + 2 * A_in) := by
        rw [Finset.sum_const, smul_eq_mul]

theorem comb_split_coarse_le {M : TM} {w : List Bool} {n b T' r γ A_in A : ℕ}
    {B_bank : Finset (Fin M.k)} {S : Fin M.k → ℕ} {p : ℕ → ℕ}
    (hp : CoarseWorkspacePartition M w T' r B_bank A_in A S p) (hγ : 1 ≤ γ) :
    n * n * b ≤ ∑ s ∈ Finset.range (numGroups n γ),
      (combSet n b (segLo n b γ s) (segHi n b γ s) \ readSet (inTraj M w) (n * n * b)
        (forestCoarse M w B_bank p r A (segLo n b γ s) (segHi n b γ s))).card +
      addrCount B_bank.card r * ((γ + 1) * n * b + 2 * A_in) :=
  calc n * n * b = _ := (sum_combSet_all n b hγ).symm
    _ = _ := Finset.sum_congr rfl (fun s _ => (Finset.card_sdiff_add_card_inter _
          (readSet (inTraj M w) (n * n * b)
            (forestCoarse M w B_bank p r A (segLo n b γ s) (segHi n b γ s)))).symm)
    _ = _ := Finset.sum_add_distrib
    _ ≤ _ := Nat.add_le_add_left ((coverage_grouped_coarse hp).trans
          (Nat.mul_le_mul_right _ (card_bankAddresses_le B_bank r))) _

/-! ## §3. Oblivious Entry-Data Count and Grouped Pass Bound -/

theorem forestCoarse_entryPoints_card_le {M : TM} {w : List Bool} {B_bank : Finset (Fin M.k)}
    {p : ℕ → ℕ} {r A : ℕ} (o₁ o₂ : ℕ) :
    (entryPoints (forestCoarse M w B_bank p r A o₁ o₂)).card ≤ (bankAddresses B_bank r).card := by
  have hsub : entryPoints (forestCoarse M w B_bank p r A o₁ o₂) ⊆
      (bankAddresses B_bank r).image
        (fun α => firstStep (forestNodeCoarse M w p A o₁ o₂ α.1 α.2)) := by
    intro τ hτ
    rw [mem_entryPoints] at hτ
    obtain ⟨hτF, _, hprev⟩ := hτ
    obtain ⟨α, hα, hτα⟩ := Finset.mem_biUnion.1 hτF
    refine Finset.mem_image.2 ⟨α, hα, ?_⟩
    have hconv := (forestNodeCoarse_inv (w := w) (p := p) (A := A) hα o₁ o₂).2
    have hle := firstStep_le hτα
    by_contra hne
    have hlt : firstStep (forestNodeCoarse M w p A o₁ o₂ α.1 α.2) < τ := lt_of_le_of_ne hle hne
    exact hprev (Finset.mem_biUnion.2 ⟨α, hα,
      hconv _ (firstStep_mem ⟨τ, hτα⟩) τ hτα (τ - 1) (by omega) (by omega)⟩)
  exact le_trans (Finset.card_le_card hsub) Finset.card_image_le

/-- Core Step-4 helper: if `τ ∈ J_α` is an entry cell of `F` on bank tape `t ∈ B_bank`, then
`workTraj M w τ t ∈ coarseAnchorWin (fun s => workTraj M w s t) (firstStep J_α) A`. -/
theorem entryCell_mem_coarseAnchorWin_of_bank {M : TM} {w : List Bool} {T' r A_in A : ℕ}
    {B_bank : Finset (Fin M.k)} {S : Fin M.k → ℕ} {p : ℕ → ℕ}
    (hp : CoarseWorkspacePartition M w T' r B_bank A_in A S p) {o₁ o₂ : ℕ}
    {α : ℕ × List (ℕ × Fin M.k)} (hα : α ∈ bankAddresses B_bank r)
    {t : Fin M.k} (ht : t ∈ B_bank) {τ σ : ℕ}
    (hτα : τ ∈ forestNodeCoarse M w p A o₁ o₂ α.1 α.2)
    (hσF : σ ∉ forestCoarse M w B_bank p r A o₁ o₂)
    (hlast : IsLastVisit (fun s => workTraj M w s t) τ σ) :
    workTraj M w τ t ∈
      coarseAnchorWin (fun s => workTraj M w s t)
        (firstStep (forestNodeCoarse M w p A o₁ o₂ α.1 α.2)) A := by
  set J := forestNodeCoarse M w p A o₁ o₂ α.1 α.2
  set h := fun s => workTraj M w s t
  obtain ⟨hJsub, hJconv⟩ := forestNodeCoarse_inv (w := w) (p := p) (A := A) hα o₁ o₂
  set P := lastPass α.2 α.1
  have hPr : P < r := lastPass_lt (bankAddresses_subset_addresses B_bank r hα)
  have haJ : firstStep J ∈ J := firstStep_mem ⟨τ, hτα⟩
  have hσa : σ < firstStep J := by
    by_contra hc
    push Not at hc
    exact hσF (Finset.mem_biUnion.2 ⟨α, hα, hJconv _ haJ τ hτα σ hc (le_of_lt hlast.1)⟩)
  by_contra hout
  have hσP : σ < p P := by
    by_contra hc
    push Not at hc
    exact coarse_pass_fresh (hp.2.2.2.2.1 P hPr t ht) hJsub hτα hout hc hσa hlast.2.1
  have hτT : τ < T' := forestCoarse_subset hp o₁ o₂ τ (Finset.mem_biUnion.2 ⟨α, hα, hτα⟩)
  obtain ⟨P', hP'r, hP'1, hP'2⟩ := cwp_exists_pass hp (show σ < T' by have := hlast.1; omega)
  have hP'P : P' < P := by
    by_contra hc
    push Not at hc
    have := cwp_mono hp hc (le_of_lt hP'r)
    omega
  have hc : h τ ∈ sSetCoarse h p A J P' := by
    rw [mem_sSetCoarse]
    refine ⟨⟨τ, hτα, rfl⟩, hout, σ, mem_passSteps.2 ⟨hP'1, hP'2⟩, hσa, hlast.2.1, ?_⟩
    intro ρ h1 h2
    exact hlast.2.2 ρ h1 (lt_of_lt_of_le h2 (firstStep_le hτα))
  have hα' : (α.1, α.2 ++ [(P', t)]) ∈ bankAddresses B_bank r :=
    mem_bankAddresses.2 ⟨(mem_bankAddresses.1 hα).1,
      append_mem_bankAddrsBelow ht (mem_bankAddresses.1 hα).2 hP'P⟩
  have hσ' : σ ∈ forestNodeCoarse M w p A o₁ o₂ α.1 (α.2 ++ [(P', t)]) := by
    rw [forestNodeCoarse_append]
    exact mem_childNodeCoarse_of_sSetCoarse (mem_passSteps.2 ⟨hP'1, hP'2⟩)
      (show h σ ∈ sSetCoarse h p A J P' by rw [hlast.2.1]; exact hc)
  exact hσF (Finset.mem_biUnion.2 ⟨_, hα', hσ'⟩)

theorem forestCoarse_entryCells_card_le {M : TM} {w : List Bool} {T' r A_in A : ℕ}
    {B_bank : Finset (Fin M.k)} {S : Fin M.k → ℕ} {p : ℕ → ℕ}
    (hp : CoarseWorkspacePartition M w T' r B_bank A_in A S p) (o₁ o₂ : ℕ) :
    (entryCells (workTraj M w) (forestCoarse M w B_bank p r A o₁ o₂)).card ≤
      (bankAddresses B_bank r).card * (B_bank.card * (3 * A + 1) + workspaceCellSum B_bank S) := by
  classical
  set F := forestCoarse M w B_bank p r A o₁ o₂
  set E := entryCells (workTraj M w) F
  have hsub_union : E ⊆ (bankAddresses B_bank r).biUnion (fun α =>
      Finset.univ.biUnion (fun t : Fin M.k =>
        ((forestNodeCoarse M w p A o₁ o₂ α.1 α.2).filter (fun τ => (t, τ) ∈ E)).image
          (fun τ => (t, τ)))) := by
    rintro ⟨t, τ⟩ hmem
    have hτF : τ ∈ F := (mem_entryCells.1 hmem).1
    obtain ⟨α, hα, hτα⟩ := Finset.mem_biUnion.1 hτF
    refine Finset.mem_biUnion.2 ⟨α, hα, Finset.mem_biUnion.2 ⟨t, Finset.mem_univ t, ?_⟩⟩
    exact Finset.mem_image.2 ⟨τ, Finset.mem_filter.2 ⟨hτα, hmem⟩, rfl⟩
  have hper_node_tape : ∀ α ∈ bankAddresses B_bank r, ∀ t : Fin M.k,
      ((forestNodeCoarse M w p A o₁ o₂ α.1 α.2).filter (fun τ => (t, τ) ∈ E)).card ≤
        if t ∈ B_bank then 3 * A + 1 else S t := by
    intro α hα t
    set J := forestNodeCoarse M w p A o₁ o₂ α.1 α.2
    set E_αt := J.filter (fun τ => (t, τ) ∈ E)
    set h := fun s => workTraj M w s t
    obtain ⟨hJsub, hJconv⟩ := forestNodeCoarse_inv hα o₁ o₂
    have hinj : Set.InjOn h E_αt := by
      intro τ₁ h₁ τ₂ h₂ heq
      rw [Finset.mem_coe, Finset.mem_filter] at h₁ h₂
      rcases lt_trichotomy τ₁ τ₂ with hlt | rfl | hgt
      · obtain ⟨-, σ₂, hσ₂F, hlast₂⟩ := mem_entryCells.1 h₂.2
        have haJ : firstStep J ∈ J := firstStep_mem ⟨τ₁, h₁.1⟩
        have hσ₂a : σ₂ < firstStep J := by
          by_contra hc; push Not at hc
          exact hσ₂F (Finset.mem_biUnion.2 ⟨α, hα, hJconv _ haJ τ₂ h₂.1 σ₂ hc (le_of_lt hlast₂.1)⟩)
        exact absurd heq (hlast₂.2.2 τ₁ (lt_of_lt_of_le hσ₂a (firstStep_le h₁.1)) hlt)
      · rfl
      · obtain ⟨-, σ₁, hσ₁F, hlast₁⟩ := mem_entryCells.1 h₁.2
        have haJ : firstStep J ∈ J := firstStep_mem ⟨τ₂, h₂.1⟩
        have hσ₁a : σ₁ < firstStep J := by
          by_contra hc; push Not at hc
          exact hσ₁F (Finset.mem_biUnion.2 ⟨α, hα, hJconv _ haJ τ₁ h₁.1 σ₁ hc (le_of_lt hlast₁.1)⟩)
        exact absurd heq.symm (hlast₁.2.2 τ₂ (lt_of_lt_of_le hσ₁a (firstStep_le h₂.1)) hgt)
    split_ifs with ht
    · set P := lastPass α.2 α.1
      have hPr : P < r := lastPass_lt (bankAddresses_subset_addresses B_bank r hα)
      rcases hp.2.2.2.2.1 P hPr t ht with hinc | hdec
      · have himg : E_αt.image h ⊆ coarseDirWin (h (firstStep J)) A true := by
          intro c hc
          obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.1 hc
          obtain ⟨hτJ, hτE⟩ := Finset.mem_filter.1 hτ
          obtain ⟨-, σ, hσF, hlast⟩ := mem_entryCells.1 hτE
          exact mem_coarseDirWin_of_mem_coarseAnchorWin_up hinc hJsub hτJ
            (entryCell_mem_coarseAnchorWin_of_bank hp hα ht hτJ hσF hlast)
        calc E_αt.card = (E_αt.image h).card := (Finset.card_image_of_injOn hinj).symm
          _ ≤ (coarseDirWin (h (firstStep J)) A true).card := Finset.card_le_card himg
          _ = 3 * A + 1 := card_coarseDirWin _ _ _
      · have himg : E_αt.image h ⊆ coarseDirWin (h (firstStep J)) A false := by
          intro c hc
          obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.1 hc
          obtain ⟨hτJ, hτE⟩ := Finset.mem_filter.1 hτ
          obtain ⟨-, σ, hσF, hlast⟩ := mem_entryCells.1 hτE
          exact mem_coarseDirWin_of_mem_coarseAnchorWin_dn hdec hJsub hτJ
            (entryCell_mem_coarseAnchorWin_of_bank hp hα ht hτJ hσF hlast)
        calc E_αt.card = (E_αt.image h).card := (Finset.card_image_of_injOn hinj).symm
          _ ≤ (coarseDirWin (h (firstStep J)) A false).card := Finset.card_le_card himg
          _ = 3 * A + 1 := card_coarseDirWin _ _ _
    · have himg : E_αt.image h ⊆ visitedWorkCells M w T' t := by
        intro c hc
        obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.1 hc
        obtain ⟨hτJ, -⟩ := Finset.mem_filter.1 hτ
        have hτT : τ < T' := forestCoarse_subset hp o₁ o₂ τ (Finset.mem_biUnion.2 ⟨α, hα, hτJ⟩)
        exact Finset.mem_image.2 ⟨τ, Finset.mem_range.2 hτT, rfl⟩
      calc E_αt.card = (E_αt.image h).card := (Finset.card_image_of_injOn hinj).symm
        _ ≤ (visitedWorkCells M w T' t).card := Finset.card_le_card himg
        _ ≤ S t := hp.2.2.2.2.2 t ht
  have hsum_t : ∑ t : Fin M.k, (if t ∈ B_bank then 3 * A + 1 else S t) =
      B_bank.card * (3 * A + 1) + workspaceCellSum B_bank S := by
    have hsplit := (Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin M.k))
      (fun t => t ∈ B_bank) (fun t => if t ∈ B_bank then 3 * A + 1 else S t)).symm
    rw [hsplit]
    have h1 : (Finset.univ : Finset (Fin M.k)).filter (fun t => t ∈ B_bank) = B_bank := by
      ext t; simp
    have h2 : (Finset.univ : Finset (Fin M.k)).filter (fun t => t ∉ B_bank) =
        Finset.univ \ B_bank := by
      ext t; simp [Finset.mem_sdiff]
    rw [h1, h2]
    have hs1 : ∑ t ∈ B_bank, (if t ∈ B_bank then 3 * A + 1 else S t) =
        B_bank.card * (3 * A + 1) := by
      calc ∑ t ∈ B_bank, (if t ∈ B_bank then 3 * A + 1 else S t)
          = ∑ _t ∈ B_bank, (3 * A + 1) :=
            Finset.sum_congr rfl (fun t ht => by simp [ht])
        _ = B_bank.card * (3 * A + 1) := by rw [Finset.sum_const, smul_eq_mul]
    have hs2 : ∑ t ∈ Finset.univ \ B_bank, (if t ∈ B_bank then 3 * A + 1 else S t) =
        workspaceCellSum B_bank S := by
      unfold workspaceCellSum
      refine Finset.sum_congr rfl (fun t ht => ?_)
      have ht' : t ∉ B_bank := (Finset.mem_sdiff.1 ht).2
      simp [ht']
    rw [hs1, hs2]
  calc E.card
      ≤ ∑ α ∈ bankAddresses B_bank r,
          (Finset.univ.biUnion (fun t : Fin M.k =>
            ((forestNodeCoarse M w p A o₁ o₂ α.1 α.2).filter (fun τ => (t, τ) ∈ E)).image
              (fun τ => (t, τ)))).card :=
        (Finset.card_le_card hsub_union).trans Finset.card_biUnion_le
    _ ≤ ∑ α ∈ bankAddresses B_bank r, ∑ t : Fin M.k,
          (((forestNodeCoarse M w p A o₁ o₂ α.1 α.2).filter (fun τ => (t, τ) ∈ E)).image
            (fun τ => (t, τ))).card :=
        Finset.sum_le_sum (fun _ _ => Finset.card_biUnion_le)
    _ ≤ ∑ α ∈ bankAddresses B_bank r, ∑ t : Fin M.k,
          ((forestNodeCoarse M w p A o₁ o₂ α.1 α.2).filter (fun τ => (t, τ) ∈ E)).card :=
        Finset.sum_le_sum (fun _ _ => Finset.sum_le_sum (fun _ _ => Finset.card_image_le))
    _ ≤ ∑ _α ∈ bankAddresses B_bank r, ∑ t : Fin M.k, (if t ∈ B_bank then 3 * A + 1 else S t) :=
        Finset.sum_le_sum (fun α hα => Finset.sum_le_sum (fun t _ => hper_node_tape α hα t))
    _ = (bankAddresses B_bank r).card *
          (B_bank.card * (3 * A + 1) + workspaceCellSum B_bank S) := by
        rw [hsum_t, Finset.sum_const, smul_eq_mul]

theorem comb_diff_subset_cutSet_coarse_on {M : TM} {n b T' r A_in A : ℕ}
    {B_bank : Finset (Fin M.k)} {S : Fin M.k → ℕ} {w₀ : List Bool} {p : ℕ → ℕ}
    (hlen : outLen M w₀ T' = n * n * b)
    (hp : CoarseWorkspacePartition M w₀ T' r B_bank A_in A S p) {o₁ o₂ : ℕ} :
    combSet n b o₁ o₂ \ readSet (inTraj M w₀) (n * n * b)
        (forestCoarse M w₀ B_bank p r A o₁ o₂) ⊆
      Transpose.Tape.cutSet M w₀ n b (forestCoarse M w₀ B_bank p r A o₁ o₂) := by
  classical
  intro d hd
  simp only [Finset.mem_sdiff, combSet, readSet, Finset.mem_filter, Finset.mem_range, not_and,
    not_exists] at hd
  obtain ⟨⟨hdL, ho1, ho2⟩, hdr⟩ := hd
  obtain ⟨τ, -, hτF, hsome, hlen'⟩ := exists_append_step_mem_forestCoarse hp ho1 ho2 (by
    have := tpos_lt hdL; simp only [outLen] at hlen; omega)
  simp only [Transpose.Tape.cutSet, Finset.mem_filter, Finset.mem_range]
  exact ⟨hdL, fun τ hτ heq => hdr hdL τ hτ heq, τ, hτF, hsome, hlen'⟩

theorem forestCoarse_info_on {M : TM} {n b T r A_in A : ℕ} {B_bank : Finset (Fin M.k)}
    {S : Fin M.k → ℕ} {W : Set (List Bool)} (hobl : ObliviousOn M W T)
    (hcorr : ClassCorrect M n b T W) {w₀ : List Bool} (hw₀ : w₀ ∈ W) {p : ℕ → ℕ}
    (hp : CoarseWorkspacePartition M w₀ T r B_bank A_in A S p) {m : ℕ}
    (hco : 2 ^ (n * n * b) ≤ 2 ^ m * W.ncard) {o₁ o₂ : ℕ} :
    2 ^ (combSet n b o₁ o₂ \ readSet (inTraj M w₀) (n * n * b)
        (forestCoarse M w₀ B_bank p r A o₁ o₂)).card ≤
      2 ^ m * ((M.q + 1) * (M.g + 1) ^
        (B_bank.card * (3 * A + 1) + workspaceCellSum B_bank S)) ^
          (bankAddresses B_bank r).card := by
  have h2 := Finset.card_le_card
    (comb_diff_subset_cutSet_coarse_on (o₁ := o₁) (o₂ := o₂) (outLen_of_classCorrect hcorr hw₀) hp)
  calc _ ≤ 2 ^ (Transpose.Tape.cutSet M w₀ n b
            (forestCoarse M w₀ B_bank p r A o₁ o₂)).card :=
        Nat.pow_le_pow_right (by norm_num) h2
    _ ≤ _ := cut_bound_on_coentropy hobl hcorr hw₀ (forestCoarse_subset hp o₁ o₂) hco
    _ ≤ _ := Nat.mul_le_mul_left _ (by
        rw [mul_pow, ← pow_mul,
          Nat.mul_comm (B_bank.card * (3 * A + 1) + workspaceCellSum B_bank S)
            (bankAddresses B_bank r).card]
        exact Nat.mul_le_mul
          (Nat.pow_le_pow_right (by omega) (forestCoarse_entryPoints_card_le o₁ o₂))
          (Nat.pow_le_pow_right (by omega) (forestCoarse_entryCells_card_le hp o₁ o₂)))

/-- Oblivious per-node entry-data bit cost `σ_{M, A, S}^{obl}` for the coarse-monotone,
workspace-folded grouped pass bound. -/
def oblEntryBits (M : TM) (B_bank : Finset (Fin M.k)) (A : ℕ) (S : Fin M.k → ℕ) : ℕ :=
  Nat.clog 2 (M.q + 1) +
    (B_bank.card * (3 * A + 1) + workspaceCellSum B_bank S) * Nat.clog 2 (M.g + 1)

theorem side_coarse_obl_le_pow (M : TM) (B_bank : Finset (Fin M.k)) (A : ℕ) (S : Fin M.k → ℕ) :
    (M.q + 1) * (M.g + 1) ^ (B_bank.card * (3 * A + 1) + workspaceCellSum B_bank S) ≤
      2 ^ oblEntryBits M B_bank A S := by
  unfold oblEntryBits
  have h1 := Nat.le_pow_clog (by norm_num : 1 < 2) (M.q + 1)
  have h2 := Nat.pow_le_pow_left (Nat.le_pow_clog (by norm_num : 1 < 2) (M.g + 1))
    (B_bank.card * (3 * A + 1) + workspaceCellSum B_bank S)
  calc (M.q + 1) * (M.g + 1) ^ (B_bank.card * (3 * A + 1) + workspaceCellSum B_bank S)
      ≤ 2 ^ Nat.clog 2 (M.q + 1) *
          (2 ^ Nat.clog 2 (M.g + 1)) ^ (B_bank.card * (3 * A + 1) + workspaceCellSum B_bank S) :=
        Nat.mul_le_mul h1 h2
    _ = _ := by
        rw [← pow_mul, ← pow_add, Nat.mul_comm (Nat.clog 2 (M.g + 1))]

/-- **Oblivious Coarse-Monotone & Workspace-Folded Grouped Pass Bound on a Set of Co-Entropy `≤ m`
(Log-Free Form)**. -/
theorem theoremP_coarseWorkspace_grouped_on {M : TM} {d b T r γ A_in A : ℕ}
    {B_bank : Finset (Fin M.k)} {S : Fin M.k → ℕ} {W : Set (List Bool)}
    (hobl : ObliviousOn M W T) (hcorr : ClassCorrect M d b T W)
    {w₀ : List Bool} (hw₀ : w₀ ∈ W) {p : ℕ → ℕ}
    (hp : CoarseWorkspacePartition M w₀ T r B_bank A_in A S p)
    (hγ : 1 ≤ γ) {m : ℕ} (hco : 2 ^ (d * d * b) ≤ 2 ^ m * W.ncard) :
    2 ^ (d * d * b) ≤
      2 ^ (numGroups d γ * m) *
        (2 ^ (addrCount B_bank.card r * ((γ + 1) * d * b + 2 * A_in)) *
          ((M.q + 1) * (M.g + 1) ^ (B_bank.card * (3 * A + 1) + workspaceCellSum B_bank S)) ^
            (numGroups d γ * addrCount B_bank.card r)) := by
  have hB : 1 ≤ (M.q + 1) *
      (M.g + 1) ^ (B_bank.card * (3 * A + 1) + workspaceCellSum B_bank S) :=
    Nat.one_le_iff_ne_zero.2 (by positivity)
  have h := pow_le_of_sum_pow_le _ (comb_split_coarse_le (n := d) (b := b) hp hγ)
    (sum_le_card_mul fun s _ => (forestCoarse_info_on hobl hcorr hw₀ hp hco).trans
      (Nat.mul_le_mul_left (2 ^ m) (Nat.pow_le_pow_right hB (card_bankAddresses_le B_bank r))))
  calc _ ≤ _ := h
    _ = _ := by rw [mul_pow, ← pow_mul, ← pow_mul]; ring

/-- **Oblivious Coarse-Monotone & Workspace-Folded Grouped Pass Bound on a Set of Co-Entropy `≤ m`
(Bits Form)**:
`d² b ≤ ⌈d/γ⌉ m + H(k_b, r) ((γ + 1) d b + 2 A_in + ⌈d/γ⌉ σ_{M, A, S}^{obl})`. -/
theorem theoremP_coarseWorkspace_grouped_on_bits {M : TM} {d b T r γ A_in A : ℕ}
    {B_bank : Finset (Fin M.k)} {S : Fin M.k → ℕ} {W : Set (List Bool)}
    (hobl : ObliviousOn M W T) (hcorr : ClassCorrect M d b T W)
    {w₀ : List Bool} (hw₀ : w₀ ∈ W) {p : ℕ → ℕ}
    (hp : CoarseWorkspacePartition M w₀ T r B_bank A_in A S p)
    (hγ : 1 ≤ γ) {m : ℕ} (hco : 2 ^ (d * d * b) ≤ 2 ^ m * W.ncard) :
    d * d * b ≤ numGroups d γ * m + addrCount B_bank.card r *
      ((γ + 1) * d * b + 2 * A_in + numGroups d γ * oblEntryBits M B_bank A S) :=
  bits_of_logfree (side_coarse_obl_le_pow M B_bank A S)
    (theoremP_coarseWorkspace_grouped_on hobl hcorr hw₀ hp hγ hco)

/-- Zero-constant-loss check: at `B_bank = Finset.univ` and `A_in = A = S_tot = 0`,
`oblEntryBits M Finset.univ 0 (fun _ => 0)` equals `Nat.clog 2 (M.q + 1) + M.k * Nat.clog 2 (M.g + 1)`. -/
theorem oblEntryBits_zero_univ_eq (M : TM) :
    oblEntryBits M Finset.univ 0 (fun _ => 0) =
      Nat.clog 2 (M.q + 1) + M.k * Nat.clog 2 (M.g + 1) := by
  simp [oblEntryBits, workspaceCellSum]

/-! ## §4. Adaptive Coarse-Monotone & Workspace-Folded Grouped Pass Bound and Single-Scale Exclusions -/

/-- Left endpoint of `coarseDirWin pos A up`. -/
def coarseDirBase (pos : ℤ) (A : ℕ) (up : Bool) : ℤ :=
  if up then pos - (A : ℤ) else pos - 2 * (A : ℤ)

theorem mem_coarseDirWin_iff_base (pos : ℤ) (A : ℕ) (up : Bool) (c : ℤ) :
    c ∈ coarseDirWin pos A up ↔
      coarseDirBase pos A up ≤ c ∧ c < coarseDirBase pos A up + (3 * (A : ℤ) + 1) := by
  cases up <;> simp [coarseDirWin, coarseDirBase] <;> omega

theorem zero_mem_visitedWorkCells {M : TM} {w : List Bool} {T' : ℕ} (hT : 0 < T') (t : Fin M.k) :
    (0 : ℤ) ∈ visitedWorkCells M w T' t :=
  Finset.mem_image.2 ⟨0, Finset.mem_range.2 hT, rfl⟩

theorem visitedWorkCells_icc_subset {M : TM} {w : List Bool} {T' : ℕ} (t : Fin M.k)
    (hV : (visitedWorkCells M w T' t).Nonempty) :
    Finset.Icc ((visitedWorkCells M w T' t).min' hV) ((visitedWorkCells M w T' t).max' hV) ⊆
      visitedWorkCells M w T' t := by
  intro z hz
  rw [Finset.mem_Icc] at hz
  obtain ⟨y₁, hy₁, hmin⟩ := Finset.mem_image.1 (Finset.min'_mem _ hV)
  obtain ⟨y₂, hy₂, hmax⟩ := Finset.mem_image.1 (Finset.max'_mem _ hV)
  rw [Finset.mem_range] at hy₁ hy₂
  rcases le_total y₁ y₂ with hle | hle
  · obtain ⟨y, _, hy, hyz⟩ := discrete_ivt (f := fun τ => workTraj M w τ t)
      (unitSteps_workTraj M w t) hle (β := z) ⟨by rw [hmin, hmax]; omega, by rw [hmin, hmax]; omega⟩
    exact Finset.mem_image.2 ⟨y, Finset.mem_range.2 (lt_of_le_of_lt hy hy₂), hyz⟩
  · obtain ⟨y, _, hy, hyz⟩ := discrete_ivt (f := fun τ => workTraj M w τ t)
      (unitSteps_workTraj M w t) hle (β := z) ⟨by rw [hmin, hmax]; omega, by rw [hmin, hmax]; omega⟩
    exact Finset.mem_image.2 ⟨y, Finset.mem_range.2 (lt_of_le_of_lt hy hy₁), hyz⟩

open Classical in
/-- Nonnegative left-shift `(- min V_t).toNat` anchoring workspace tape `t`'s visited interval. -/
noncomputable def wsShift (M : TM) (w : List Bool) (T' : ℕ) (t : Fin M.k) : ℕ :=
  if hV : (visitedWorkCells M w T' t).Nonempty then
    (-(visitedWorkCells M w T' t).min' hV).toNat
  else 0

theorem wsShift_lt {M : TM} {w : List Bool} {T' : ℕ} {t : Fin M.k} {S : Fin M.k → ℕ}
    (hS : (visitedWorkCells M w T' t).card ≤ S t) :
    wsShift M w T' t < S t + 1 := by
  classical
  by_cases hV : (visitedWorkCells M w T' t).Nonempty
  · rw [wsShift, dite_eq_left hV]
    obtain ⟨c, hc⟩ := id hV
    obtain ⟨τ, hτ, -⟩ := Finset.mem_image.1 hc
    have hT : 0 < T' := lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_range.1 hτ)
    have h0 : (0 : ℤ) ∈ visitedWorkCells M w T' t := zero_mem_visitedWorkCells hT t
    have hmin0 : (visitedWorkCells M w T' t).min' hV ≤ 0 := Finset.min'_le _ _ h0
    have hmax0 : 0 ≤ (visitedWorkCells M w T' t).max' hV := Finset.le_max' _ _ h0
    have hcard : (Finset.Icc ((visitedWorkCells M w T' t).min' hV)
        ((visitedWorkCells M w T' t).max' hV)).card ≤ S t :=
      (Finset.card_le_card (visitedWorkCells_icc_subset t hV)).trans hS
    rw [Int.card_Icc] at hcard
    omega
  · rw [wsShift, dite_eq_right hV]
    omega

theorem mem_visitedWorkCells_bounds_of_shift {M : TM} {w : List Bool} {T' : ℕ} {t : Fin M.k}
    {S : Fin M.k → ℕ} (hS : (visitedWorkCells M w T' t).card ≤ S t)
    {c : ℤ} (hc : c ∈ visitedWorkCells M w T' t) :
    -(wsShift M w T' t : ℤ) ≤ c ∧ c < -(wsShift M w T' t : ℤ) + (S t : ℤ) := by
  classical
  have hV : (visitedWorkCells M w T' t).Nonempty := ⟨c, hc⟩
  obtain ⟨τ, hτ, -⟩ := Finset.mem_image.1 hc
  have hT : 0 < T' := lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_range.1 hτ)
  have h0 : (0 : ℤ) ∈ visitedWorkCells M w T' t := zero_mem_visitedWorkCells hT t
  have hmin0 : (visitedWorkCells M w T' t).min' hV ≤ 0 := Finset.min'_le _ _ h0
  have hmax0 : 0 ≤ (visitedWorkCells M w T' t).max' hV := Finset.le_max' _ _ h0
  have hminc : (visitedWorkCells M w T' t).min' hV ≤ c := Finset.min'_le _ _ hc
  have hmaxc : c ≤ (visitedWorkCells M w T' t).max' hV := Finset.le_max' _ _ hc
  have hcard : (Finset.Icc ((visitedWorkCells M w T' t).min' hV)
      ((visitedWorkCells M w T' t).max' hV)).card ≤ S t :=
    (Finset.card_le_card (visitedWorkCells_icc_subset t hV)).trans hS
  rw [Int.card_Icc] at hcard
  have hsh : wsShift M w T' t = (-(visitedWorkCells M w T' t).min' hV).toNat := by
    unfold wsShift; rw [dite_eq_left hV]
  rw [hsh]
  omega

theorem work_eq_blank_outside_shift {M : TM} {w : List Bool} {T' : ℕ} {t : Fin M.k}
    {S : Fin M.k → ℕ} (hS : (visitedWorkCells M w T' t).card ≤ S t)
    {a : ℕ} (ha : a < T') {c : ℤ}
    (hout : ¬ (-(wsShift M w T' t : ℤ) ≤ c ∧ c < -(wsShift M w T' t : ℤ) + (S t : ℤ))) :
    (run M w a).work t c = 0 := by
  apply work_eq_blank t c
  intro σ hσ heq
  exact hout (mem_visitedWorkCells_bounds_of_shift hS
    (Finset.mem_image.2 ⟨σ, Finset.mem_range.2 (lt_trans hσ ha), heq⟩))

/-- Finite side-code type at one node of the adaptive coarse-monotone, workspace-folded forest. -/
abbrev CoarseSideCode (M : TM) (B_bank : Finset (Fin M.k)) (A : ℕ) (S : Fin M.k → ℕ) : Type :=
  Fin (M.q + 1) ×
    ({t // t ∈ B_bank} → Bool × (Fin (3 * A + 1) → Fin (M.g + 1))) ×
    ((t : {t // t ∈ Finset.univ \ B_bank}) → Fin (S t.1 + 1) × (Fin (S t.1) → Fin (M.g + 1)))

/-- Cardinality of `CoarseSideCode M B_bank A S`. -/
def coarseSideCount (M : TM) (B_bank : Finset (Fin M.k)) (A : ℕ) (S : Fin M.k → ℕ) : ℕ :=
  (M.q + 1) * 2 ^ B_bank.card * (∏ t ∈ Finset.univ \ B_bank, (S t + 1)) *
    (M.g + 1) ^ (B_bank.card * (3 * A + 1) + workspaceCellSum B_bank S)

theorem card_coarseSideCode_eq (M : TM) (B_bank : Finset (Fin M.k)) (A : ℕ) (S : Fin M.k → ℕ) :
    Fintype.card (CoarseSideCode M B_bank A S) = coarseSideCount M B_bank A S := by
  classical
  have hbank : Fintype.card ({t // t ∈ B_bank} → Bool × (Fin (3 * A + 1) → Fin (M.g + 1))) =
      2 ^ B_bank.card * (M.g + 1) ^ (B_bank.card * (3 * A + 1)) := by
    simp only [Fintype.card_fun, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin,
      Fintype.card_coe, mul_pow, ← pow_mul, Nat.mul_comm (3 * A + 1) B_bank.card]
  have hpi : Fintype.card ((t : {t // t ∈ Finset.univ \ B_bank}) →
      Fin (S t.1 + 1) × (Fin (S t.1) → Fin (M.g + 1))) =
      (∏ t ∈ Finset.univ \ B_bank, (S t + 1)) *
        (M.g + 1) ^ workspaceCellSum B_bank S := by
    rw [Fintype.card_pi]
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_fun]
    rw [Finset.prod_coe_sort (Finset.univ \ B_bank)
      (fun t => (S t + 1) * (M.g + 1) ^ S t), Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum]
    rfl
  unfold CoarseSideCode coarseSideCount
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, hbank, hpi, pow_add]
  ring

open Classical in
/-- Augmented side code of node `N` in pass `P` on run `(M, w)` with horizon `T'`. -/
noncomputable def coarseSideCodeOf {M : TM} {w : List Bool} {T' r A_in A : ℕ}
    {B_bank : Finset (Fin M.k)} {S : Fin M.k → ℕ} {p : ℕ → ℕ}
    (hp : CoarseWorkspacePartition M w T' r B_bank A_in A S p) (P : ℕ) (N : Finset ℕ) :
    CoarseSideCode M B_bank A S :=
  let a := firstStep N
  ((run M w a).state,
    fun t =>
      let up := decide (∀ x y, p P ≤ x → x ≤ y → y < p (P + 1) →
        workTraj M w x t.1 - (A : ℤ) ≤ workTraj M w y t.1)
      (up, fun j => (run M w a).work t.1
        (coarseDirBase ((run M w a).workPos t.1) A up + (j.1 : ℤ))),
    fun t =>
      let sh := wsShift M w T' t.1
      (⟨sh, wsShift_lt (hp.2.2.2.2.2 t.1 (Finset.mem_sdiff.1 t.2).2)⟩,
        fun j => (run M w a).work t.1 (-(sh : ℤ) + (j.1 : ℤ))))

theorem coarseSideCodeOf_ws_work_eq {M : TM} {w w' : List Bool} {T₁ T₂ r A_in A : ℕ}
    {B_bank : Finset (Fin M.k)} {S : Fin M.k → ℕ} {p p' : ℕ → ℕ}
    (hp : CoarseWorkspacePartition M w T₁ r B_bank A_in A S p)
    (hp' : CoarseWorkspacePartition M w' T₂ r B_bank A_in A S p')
    {P : ℕ} {N : Finset ℕ} (ha₁ : firstStep N < T₁) (ha₂ : firstStep N < T₂)
    (hside : coarseSideCodeOf hp P N = coarseSideCodeOf hp' P N)
    {t : Fin M.k} (ht : t ∉ B_bank) (c : ℤ) :
    (run M w (firstStep N)).work t c = (run M w' (firstStep N)).work t c := by
  have ht' : t ∈ Finset.univ \ B_bank := Finset.mem_sdiff.2 ⟨Finset.mem_univ t, ht⟩
  have h2 := congrFun (congrArg (fun x => x.2.2) hside) ⟨t, ht'⟩
  simp only [coarseSideCodeOf, Prod.mk.injEq, Fin.ext_iff] at h2
  obtain ⟨hsh, hvals⟩ := h2
  set sh := wsShift M w T₁ t
  have hsh' : wsShift M w' T₂ t = sh := hsh.symm
  by_cases hin : -(sh : ℤ) ≤ c ∧ c < -(sh : ℤ) + (S t : ℤ)
  · let idx : Fin (S t) := ⟨(c + (sh : ℤ)).toNat, by omega⟩
    have hidx : -(sh : ℤ) + (idx.1 : ℤ) = c := by dsimp [idx]; omega
    have hj := congrFun hvals idx
    simp only [hsh', hidx] at hj
    exact hj
  · rw [work_eq_blank_outside_shift (hp.2.2.2.2.2 t ht) ha₁ hin,
      work_eq_blank_outside_shift (hp'.2.2.2.2.2 t ht) ha₂ (by rw [hsh']; exact hin)]

theorem coarseSideCodeOf_bank_work_eq {M : TM} {w w' : List Bool} {T₁ T₂ r A_in A : ℕ}
    {B_bank : Finset (Fin M.k)} {S : Fin M.k → ℕ} {p p' : ℕ → ℕ}
    (hp : CoarseWorkspacePartition M w T₁ r B_bank A_in A S p)
    (hp' : CoarseWorkspacePartition M w' T₂ r B_bank A_in A S p')
    {P : ℕ} (hP : P < r) {N : Finset ℕ} (hN_w : N ⊆ passSteps p P)
    (hwp : (run M w (firstStep N)).workPos = (run M w' (firstStep N)).workPos)
    (hside : coarseSideCodeOf hp P N = coarseSideCodeOf hp' P N)
    {t : Fin M.k} (ht : t ∈ B_bank) {τ : ℕ} (hτ : τ ∈ N)
    (hwin : workTraj M w τ t ∈ coarseAnchorWin (fun s => workTraj M w s t) (firstStep N) A) :
    (run M w (firstStep N)).work t (workTraj M w τ t) =
      (run M w' (firstStep N)).work t (workTraj M w τ t) := by
  classical
  have h1 := congrFun (congrArg (fun x => x.2.1) hside) ⟨t, ht⟩
  simp only [coarseSideCodeOf, Prod.mk.injEq] at h1
  obtain ⟨hup, hvals⟩ := h1
  set up := decide (∀ x y, p P ≤ x → x ≤ y → y < p (P + 1) →
    workTraj M w x t - (A : ℤ) ≤ workTraj M w y t) with hup_def
  set pos := (run M w (firstStep N)).workPos t
  have hpos' : (run M w' (firstStep N)).workPos t = pos := by rw [← hwp]
  have hdir : workTraj M w τ t ∈ coarseDirWin pos A up := by
    by_cases htru : up = true
    · rw [htru]
      have hinc : ∀ x y, p P ≤ x → x ≤ y → y < p (P + 1) →
          workTraj M w x t - (A : ℤ) ≤ workTraj M w y t := by
        rw [hup_def, decide_eq_true_eq] at htru; exact htru
      exact mem_coarseDirWin_of_mem_coarseAnchorWin_up hinc hN_w hτ hwin
    · have hfls : up = false := Bool.eq_false_iff.2 htru
      rw [hfls]
      have hnot_inc : ¬ (∀ x y, p P ≤ x → x ≤ y → y < p (P + 1) →
          workTraj M w x t - (A : ℤ) ≤ workTraj M w y t) := by
        intro hinc; apply htru; rw [hup_def, decide_eq_true_eq]; exact hinc
      rcases hp.2.2.2.2.1 P hP t ht with hinc | hdec
      · exact absurd hinc hnot_inc
      · exact mem_coarseDirWin_of_mem_coarseAnchorWin_dn hdec hN_w hτ hwin
  obtain ⟨hlo, hhi⟩ := (mem_coarseDirWin_iff_base pos A up (workTraj M w τ t)).1 hdir
  let idx : Fin (3 * A + 1) := ⟨(workTraj M w τ t - coarseDirBase pos A up).toNat, by omega⟩
  have hidx : coarseDirBase pos A up + (idx.1 : ℤ) = workTraj M w τ t := by dsimp [idx]; omega
  have hj := congrFun hvals idx
  rw [← hup, hpos', hidx] at hj
  exact hj

/-- **Adaptive Forest Agreement Lemma** for `CoarseWorkspacePartition` via `locality_core`. -/
theorem coarseForestAgree {M : TM} {w w' : List Bool} {L T₁ T₂ r A_in A : ℕ}
    {B_bank : Finset (Fin M.k)} {S : Fin M.k → ℕ} {p p' : ℕ → ℕ}
    (hw : w.length = L) (hw' : w'.length = L)
    (hp : CoarseWorkspacePartition M w T₁ r B_bank A_in A S p)
    (hp' : CoarseWorkspacePartition M w' T₂ r B_bank A_in A S p') {o₁ o₂ : ℕ}
    (hcode : ∀ α ∈ bankAddresses B_bank r,
      nodeCode M w (forestNodeCoarse M w p A o₁ o₂ α.1 α.2) =
          nodeCode M w' (forestNodeCoarse M w' p' A o₁ o₂ α.1 α.2) ∧
        coarseSideCodeOf hp (lastPass α.2 α.1) (forestNodeCoarse M w p A o₁ o₂ α.1 α.2) =
          coarseSideCodeOf hp' (lastPass α.2 α.1) (forestNodeCoarse M w' p' A o₁ o₂ α.1 α.2))
    (hinput : ∀ d ∈ readSet (inTraj M w) L (forestCoarse M w B_bank p r A o₁ o₂),
      d ∈ readSet (inTraj M w') L (forestCoarse M w' B_bank p' r A o₁ o₂) → nth w d = nth w' d) :
    (∀ α ∈ bankAddresses B_bank r,
      forestNodeCoarse M w p A o₁ o₂ α.1 α.2 = forestNodeCoarse M w' p' A o₁ o₂ α.1 α.2) ∧
    ∀ τ ∈ forestCoarse M w B_bank p r A o₁ o₂,
      (run M w τ).state = (run M w' τ).state ∧ (run M w τ).inPos = (run M w' τ).inPos ∧
      (run M w τ).workPos = (run M w' τ).workPos ∧
      (run M w τ).outRev.length = (run M w' τ).outRev.length ∧
      headSym M w τ = headSym M w' τ ∧ transAt M w τ = transAt M w' τ := by
  classical
  have hnode : ∀ α ∈ bankAddresses B_bank r,
      forestNodeCoarse M w p A o₁ o₂ α.1 α.2 = forestNodeCoarse M w' p' A o₁ o₂ α.1 α.2 :=
    fun α hα => eq_of_nodeCode_eq
      (forestNodeCoarse_inv (w := w) (p := p) (A := A) hα o₁ o₂).2
      (forestNodeCoarse_inv (w := w') (p := p') (A := A) hα o₁ o₂).2 (hcode α hα).1
  have hF : forestCoarse M w B_bank p r A o₁ o₂ = forestCoarse M w' B_bank p' r A o₁ o₂ :=
    Finset.biUnion_congr rfl (fun α hα => hnode α hα)
  refine ⟨hnode, ?_⟩
  let A_anch : Set ℕ := {τ | ∃ α ∈ bankAddresses B_bank r,
    (forestNodeCoarse M w p A o₁ o₂ α.1 α.2).Nonempty ∧
      firstStep (forestNodeCoarse M w p A o₁ o₂ α.1 α.2) = τ}
  have hA : ∀ τ ∈ forestCoarse M w B_bank p r A o₁ o₂, ∀ α ∈ bankAddresses B_bank r,
      firstStep (forestNodeCoarse M w p A o₁ o₂ α.1 α.2) = τ → τ ∈ A_anch := by
    intro τ hτ α hα hfs
    by_cases hne : (forestNodeCoarse M w p A o₁ o₂ α.1 α.2).Nonempty
    · exact ⟨α, hα, hne, hfs⟩
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      have h0 : τ = 0 := by rw [← hfs, hne]; simp [firstStep]
      obtain ⟨β, hβ, hτβ⟩ := Finset.mem_biUnion.1 hτ
      refine ⟨β, hβ, ⟨τ, hτβ⟩, ?_⟩
      have := firstStep_le hτβ
      omega
  have hnodeCode_fields : ∀ α ∈ bankAddresses B_bank r,
      (forestNodeCoarse M w p A o₁ o₂ α.1 α.2).Nonempty →
      (run M w (firstStep (forestNodeCoarse M w p A o₁ o₂ α.1 α.2))).inPos =
        (run M w' (firstStep (forestNodeCoarse M w p A o₁ o₂ α.1 α.2))).inPos ∧
      (run M w (firstStep (forestNodeCoarse M w p A o₁ o₂ α.1 α.2))).workPos =
        (run M w' (firstStep (forestNodeCoarse M w p A o₁ o₂ α.1 α.2))).workPos ∧
      (run M w (firstStep (forestNodeCoarse M w p A o₁ o₂ α.1 α.2))).outRev.length =
        (run M w' (firstStep (forestNodeCoarse M w p A o₁ o₂ α.1 α.2))).outRev.length := by
    intro α hα hne
    have h1 := (hcode α hα).1
    rw [← hnode α hα] at h1
    have hfs : firstStep (forestNodeCoarse M w p A o₁ o₂ α.1 α.2) =
        (forestNodeCoarse M w p A o₁ o₂ α.1 α.2).min' hne := by
      simp [firstStep, hne]
    unfold nodeCode at h1
    rw [dite_eq_left hne, dite_eq_left hne] at h1
    simp only [Option.some.injEq, Prod.mk.injEq] at h1
    rw [← hfs] at h1
    exact ⟨h1.2.2.1, h1.2.2.2.1, h1.2.2.2.2⟩
  have hpred : ∀ τ ∈ forestCoarse M w B_bank p r A o₁ o₂, τ ∉ A_anch →
      1 ≤ τ ∧ τ - 1 ∈ forestCoarse M w B_bank p r A o₁ o₂ := by
    intro τ hτ hτA
    have hτ0 : τ ≠ 0 := by
      intro h0
      obtain ⟨β, hβ, hτβ⟩ := Finset.mem_biUnion.1 hτ
      have := firstStep_le hτβ
      exact hτA (hA τ hτ β hβ (by omega))
    refine ⟨by omega, ?_⟩
    by_contra hprev
    obtain ⟨α, hα, hτα⟩ := Finset.mem_biUnion.1 hτ
    have hconv := (forestNodeCoarse_inv (w := w) (p := p) (A := A) hα o₁ o₂).2
    have hle := firstStep_le hτα
    have hlt : firstStep (forestNodeCoarse M w p A o₁ o₂ α.1 α.2) < τ :=
      lt_of_le_of_ne hle (fun he => hτA (hA τ hτ α hα he))
    exact hprev (Finset.mem_biUnion.2 ⟨α, hα,
      hconv _ (firstStep_mem ⟨τ, hτα⟩) τ hτα (τ - 1) (by omega) (by omega)⟩)
  have hanchor : ∀ τ ∈ forestCoarse M w B_bank p r A o₁ o₂, τ ∈ A_anch →
      (run M w τ).state = (run M w' τ).state ∧ (run M w τ).inPos = (run M w' τ).inPos ∧
      (run M w τ).workPos = (run M w' τ).workPos ∧
      (run M w τ).outRev.length = (run M w' τ).outRev.length ∧
      headSym M w τ = headSym M w' τ := by
    rintro τ - ⟨α, hα, hne, rfl⟩
    set N := forestNodeCoarse M w p A o₁ o₂ α.1 α.2
    obtain ⟨hi, hwp, hl⟩ := hnodeCode_fields α hα hne
    have hside := (hcode α hα).2
    rw [← hnode α hα] at hside
    have hst : (run M w (firstStep N)).state = (run M w' (firstStep N)).state :=
      congrArg Prod.fst hside
    refine ⟨hst, hi, hwp, hl, ?_⟩
    funext t
    simp only [headSym]
    have hwp_t : (run M w' (firstStep N)).workPos t = (run M w (firstStep N)).workPos t := by
      rw [← hwp]
    rw [hwp_t]
    have haN : firstStep N ∈ N := firstStep_mem hne
    by_cases ht : t ∈ B_bank
    · have hPr : lastPass α.2 α.1 < r :=
        lastPass_lt (bankAddresses_subset_addresses B_bank r hα)
      have hself : workTraj M w (firstStep N) t ∈
          coarseAnchorWin (fun s => workTraj M w s t) (firstStep N) A := by
        simp [coarseAnchorWin]
      exact coarseSideCodeOf_bank_work_eq hp hp' hPr
        (forestNodeCoarse_inv (w := w) (p := p) (A := A) hα o₁ o₂).1 hwp hside ht haN hself
    · have ha₁ : firstStep N < T₁ :=
        forestCoarse_subset hp o₁ o₂ _ (Finset.mem_biUnion.2 ⟨α, hα, haN⟩)
      have ha₂ : firstStep N < T₂ :=
        forestCoarse_subset hp' o₁ o₂ _ (hF ▸ Finset.mem_biUnion.2 ⟨α, hα, haN⟩)
      exact coarseSideCodeOf_ws_work_eq hp hp' ha₁ ha₂ hside ht _
  have hc := locality_core hpred
    (fun τ hτ hτA => ⟨(hanchor τ hτ hτA).1, (hanchor τ hτ hτA).2.1, (hanchor τ hτ hτA).2.2.1,
      (hanchor τ hτ hτA).2.2.2.2⟩)
    (fun τ hτ hτA hwp_τ t => by
      obtain ⟨α, hα, hτα⟩ := Finset.mem_biUnion.1 hτ
      set N := forestNodeCoarse M w p A o₁ o₂ α.1 α.2
      have hne : N.Nonempty := ⟨τ, hτα⟩
      obtain ⟨hNsub, hNconv⟩ := forestNodeCoarse_inv (w := w) (p := p) (A := A) hα o₁ o₂
      have haN : firstStep N ∈ N := firstStep_mem hne
      have haτ : firstStep N ≤ τ := firstStep_le hτα
      obtain ⟨-, hwp_a, -⟩ := hnodeCode_fields α hα hne
      have hside := (hcode α hα).2
      rw [← hnode α hα] at hside
      by_cases ht : t ∈ B_bank
      · by_cases hwin : workTraj M w τ t ∈
            coarseAnchorWin (fun s => workTraj M w s t) (firstStep N) A
        · have hPr : lastPass α.2 α.1 < r :=
            lastPass_lt (bankAddresses_subset_addresses B_bank r hα)
          refine ⟨firstStep N, haτ,
            coarseSideCodeOf_bank_work_eq hp hp' hPr hNsub hwp_a hside ht hτα hwin,
            fun σ h1 h2 _ _ => Finset.mem_biUnion.2 ⟨α, hα,
              hNconv _ haN τ hτα σ h1 (le_of_lt h2)⟩,
            fun σ h1 h2 _ _ => Finset.mem_biUnion.2 ⟨α, hα,
              hNconv _ haN τ hτα σ h1 (le_of_lt h2)⟩⟩
        · have he_τ : workTraj M w τ t = workTraj M w' τ t := by simp only [workTraj, hwp_τ]
          refine ⟨0, Nat.zero_le _, rfl, ?_, ?_⟩
          · intro σ _ h2 h3 h4
            by_contra hσF
            exact hwin (entryCell_mem_coarseAnchorWin_of_bank hp hα ht hτα hσF ⟨h2, h3, h4⟩)
          · intro σ _ h2 h3 h4
            by_contra hσF
            have hτα' : τ ∈ forestNodeCoarse M w' p' A o₁ o₂ α.1 α.2 := hnode α hα ▸ hτα
            have hσF' : σ ∉ forestCoarse M w' B_bank p' r A o₁ o₂ := hF ▸ hσF
            have hlast' : IsLastVisit (fun s => workTraj M w' s t) τ σ :=
              ⟨h2, h3.trans he_τ, fun ρ h5 h6 h7 => h4 ρ h5 h6 (h7.trans he_τ.symm)⟩
            have hwin' := entryCell_mem_coarseAnchorWin_of_bank hp' hα ht hτα' hσF' hlast'
            rw [← hnode α hα] at hwin'
            have hca : coarseAnchorWin (fun s => workTraj M w' s t) (firstStep N) A =
                coarseAnchorWin (fun s => workTraj M w s t) (firstStep N) A := by
              dsimp only [coarseAnchorWin, workTraj, N]
              rw [hwp_a]
            rw [hca, ← he_τ] at hwin'
            exact hwin hwin'
      · have ha₁ : firstStep N < T₁ :=
          forestCoarse_subset hp o₁ o₂ _ (Finset.mem_biUnion.2 ⟨α, hα, haN⟩)
        have ha₂ : firstStep N < T₂ :=
          forestCoarse_subset hp' o₁ o₂ _ (hF ▸ Finset.mem_biUnion.2 ⟨α, hα, haN⟩)
        exact ⟨firstStep N, haτ,
          coarseSideCodeOf_ws_work_eq hp hp' ha₁ ha₂ hside ht _,
          fun σ h1 h2 _ _ => Finset.mem_biUnion.2 ⟨α, hα,
            hNconv _ haN τ hτα σ h1 (le_of_lt h2)⟩,
          fun σ h1 h2 _ _ => Finset.mem_biUnion.2 ⟨α, hα,
            hNconv _ haN τ hτα σ h1 (le_of_lt h2)⟩⟩)
    (fun τ hτ hi => by
      refine readInput_eq_of_nth hw hw' fun d hd hdL => hinput d ?_ ?_
      · simp only [readSet, Finset.mem_filter, Finset.mem_range]
        exact ⟨hdL, τ, hτ, hd.symm⟩
      · simp only [readSet, Finset.mem_filter, Finset.mem_range]
        exact ⟨hdL, τ, hF ▸ hτ, by rw [hd]; exact hi.symm⟩)
  have hl := outLen_agree hpred (fun τ hτ hτA => (hanchor τ hτ hτA).2.2.2.1)
    (fun τ hτ => (hc τ hτ).2.2.2.2)
  intro τ hτ
  obtain ⟨h1, h2, h3, h4, h5⟩ := hc τ hτ
  exact ⟨h1, h2, h3, hl τ hτ, h4, h5⟩

/-- Comb determination under equal coarse-workspace augmented codes. -/
theorem coarseForestCombAgreeOn {M : TM} {n b T₁ T₂ r A_in A : ℕ}
    {B_bank : Finset (Fin M.k)} {S : Fin M.k → ℕ} {w w' : List Bool} {p p' : ℕ → ℕ}
    (hcw : ∃ Mat : Matrix, w = encode n b Mat ∧
      (run M w T₁).outRev.reverse = encode n b (transpose Mat))
    (hcw' : ∃ Mat : Matrix, w' = encode n b Mat ∧
      (run M w' T₂).outRev.reverse = encode n b (transpose Mat))
    (hp : CoarseWorkspacePartition M w T₁ r B_bank A_in A S p)
    (hp' : CoarseWorkspacePartition M w' T₂ r B_bank A_in A S p') {o₁ o₂ : ℕ}
    (hcode : ∀ α ∈ bankAddresses B_bank r,
      nodeCode M w (forestNodeCoarse M w p A o₁ o₂ α.1 α.2) =
          nodeCode M w' (forestNodeCoarse M w' p' A o₁ o₂ α.1 α.2) ∧
        coarseSideCodeOf hp (lastPass α.2 α.1) (forestNodeCoarse M w p A o₁ o₂ α.1 α.2) =
          coarseSideCodeOf hp' (lastPass α.2 α.1) (forestNodeCoarse M w' p' A o₁ o₂ α.1 α.2))
    (hinput : ∀ d ∈ readSet (inTraj M w) (n * n * b) (forestCoarse M w B_bank p r A o₁ o₂),
      d ∈ readSet (inTraj M w') (n * n * b) (forestCoarse M w' B_bank p' r A o₁ o₂) →
        nth w d = nth w' d) :
    ∀ d ∈ combSet n b o₁ o₂, nth w d = nth w' d := by
  classical
  obtain ⟨Mat, rfl, hout⟩ := hcw
  obtain ⟨Mat', rfl, hout'⟩ := hcw'
  have hFA := coarseForestAgree (length_of_mem_matrixInputs ⟨Mat, rfl⟩)
    (length_of_mem_matrixInputs ⟨Mat', rfl⟩) hp hp' hcode hinput
  have hF : forestCoarse M (encode n b Mat) B_bank p r A o₁ o₂ =
      forestCoarse M (encode n b Mat') B_bank p' r A o₁ o₂ :=
    Finset.biUnion_congr rfl (fun α hα => hFA.1 α hα)
  intro d hd
  simp only [combSet, Finset.mem_filter, Finset.mem_range] at hd
  obtain ⟨hdL, ho1, ho2⟩ := hd
  obtain ⟨τ, hτT, hτF, hsome, hτlen⟩ := exists_append_step_mem_forestCoarse hp ho1 ho2
    (by rw [← List.length_reverse, hout, length_encode]; exact tpos_lt hdL)
  obtain ⟨-, -, -, hl, -, htr⟩ := hFA.2 τ hτF
  have hob : outBit M (encode n b Mat') τ = outBit M (encode n b Mat) τ := by
    simp only [outBit, htr]
  have e1 := output_nth_eq_outBit (encode n b Mat) hτT hsome
  have e2 := output_nth_eq_outBit (encode n b Mat') (forestCoarse_subset hp' o₁ o₂ τ (hF ▸ hτF))
    (hob ▸ hsome)
  rw [hout, hτlen, nth_encode_transpose_tpos Mat hdL] at e1
  rw [hout', ← hl, hτlen, nth_encode_transpose_tpos Mat' hdL] at e2
  rw [e1, e2, hob]

/-- **Kraft Count for Adaptive Coarse-Monotone & Workspace-Folded Forests** on a set `V` of inputs. -/
theorem kraft_coarseWorkspace_group_on {M : TM} {n b T r A_in A : ℕ}
    {B_bank : Finset (Fin M.k)} {S : Fin M.k → ℕ}
    (V : Finset (Fin (n * n * b) → Bool))
    (Tv : (Fin (n * n * b) → Bool) → ℕ) (pv : (Fin (n * n * b) → Bool) → ℕ → ℕ)
    (hTv : ∀ v ∈ V, Tv v ≤ T)
    (hpv : ∀ v ∈ V, CoarseWorkspacePartition M (List.ofFn v) (Tv v) r B_bank A_in A S (pv v))
    (hcv : ∀ v ∈ V, ∃ Mat : Matrix, List.ofFn v = encode n b Mat ∧
      (run M (List.ofFn v) (Tv v)).outRev.reverse = encode n b (transpose Mat))
    {o₁ o₂ : ℕ} :
    ∑ v ∈ V, 2 ^ (combSet n b o₁ o₂ \ readSet (inTraj M (List.ofFn v)) (n * n * b)
        (forestCoarse M (List.ofFn v) B_bank (pv v) r A o₁ o₂)).card ≤
      2 ^ (n * n * b) *
        (structCount M.k T * coarseSideCount M B_bank A S) ^ addrCount B_bank.card r := by
  classical
  let freeC : (Fin (n * n * b) → Bool) → Finset ℕ := fun v =>
    combSet n b o₁ o₂ \ readSet (inTraj M (List.ofFn v)) (n * n * b)
      (forestCoarse M (List.ofFn v) B_bank (pv v) r A o₁ o₂)
  have hfree_lt : ∀ v, ∀ d ∈ freeC v, d < n * n * b := by
    intro v d hd
    simp only [freeC, combSet, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_range] at hd
    exact hd.1.1
  let defaultSide : CoarseSideCode M B_bank A S :=
    (0, fun _ => (false, fun _ => 0), fun _ => (0, fun _ => 0))
  let gCode : (Fin (n * n * b) → Bool) →
      ({α // α ∈ bankAddresses B_bank r} → NodeCode M.k × CoarseSideCode M B_bank A S) :=
    fun v α =>
      if hv : v ∈ V then
        (nodeCode M (List.ofFn v)
            (forestNodeCoarse M (List.ofFn v) (pv v) A o₁ o₂ α.1.1 α.1.2),
          coarseSideCodeOf (hpv v hv) (lastPass α.1.2 α.1.1)
            (forestNodeCoarse M (List.ofFn v) (pv v) A o₁ o₂ α.1.1 α.1.2))
      else (none, defaultSide)
  let box : Finset ({α // α ∈ bankAddresses B_bank r} →
      NodeCode M.k × CoarseSideCode M B_bank A S) :=
    Fintype.piFinset (fun _ => nodeBox M.k T ×ˢ Finset.univ)
  have hbox : ∀ v ∈ V, gCode v ∈ box := by
    intro v hv
    simp only [box, gCode, dite_eq_left hv, Fintype.mem_piFinset, Finset.mem_product,
      Finset.mem_univ, and_true]
    intro α
    apply nodeCode_mem_nodeBox
    intro τ hτ
    have hτF : τ ∈ forestCoarse M (List.ofFn v) B_bank (pv v) r A o₁ o₂ :=
      Finset.mem_biUnion.2 ⟨α.1, α.2, hτ⟩
    exact lt_of_lt_of_le (forestCoarse_subset (hpv v hv) o₁ o₂ τ hτF) (hTv v hv)
  have hcard_box : box.card ≤
      (structCount M.k T * coarseSideCount M B_bank A S) ^ addrCount B_bank.card r := by
    simp only [box, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ,
      Fintype.card_coe, Finset.card_product, card_coarseSideCode_eq]
    have hc : (nodeBox M.k T).card * coarseSideCount M B_bank A S ≤
        structCount M.k T * coarseSideCount M B_bank A S :=
      Nat.mul_le_mul_right _ (card_nodeBox_le M.k T)
    have hC : 1 ≤ structCount M.k T * coarseSideCount M B_bank A S := by
      have h1 : 1 ≤ structCount M.k T := Nat.one_le_iff_ne_zero.2 (by unfold structCount; positivity)
      have h2 : 1 ≤ coarseSideCount M B_bank A S := by
        unfold coarseSideCount
        have hprod : 1 ≤ ∏ t ∈ Finset.univ \ B_bank, (S t + 1) :=
          Finset.one_le_prod (fun _ _ => by omega)
        have hprod_pos : 0 < ∏ t ∈ Finset.univ \ B_bank, (S t + 1) := hprod
        exact Nat.one_le_iff_ne_zero.2 (by positivity)
      exact Nat.mul_le_mul h1 h2
    calc _ ≤ (structCount M.k T * coarseSideCount M B_bank A S) ^ (bankAddresses B_bank r).card :=
          Nat.pow_le_pow_left hc _
      _ ≤ _ := Nat.pow_le_pow_right hC (card_bankAddresses_le B_bank r)
  have hfiber : ∀ c ∈ box, ∑ v ∈ V.filter (fun v => gCode v = c),
      2 ^ (freeC v).card ≤ 2 ^ (n * n * b) := by
    intro c _
    set Fib := V.filter (fun v => gCode v = c) with hFib
    let N_ow : (Fin (n * n * b) → Bool) → Finset (Fin (n * n * b) → Bool) := fun v =>
      (freeC v).powerset.image (overwrite (freeC v) v)
    have hN : ∀ v, (N_ow v).card = 2 ^ (freeC v).card := by
      intro v
      rw [Finset.card_image_of_injOn (overwrite_injOn (hfree_lt v) v), Finset.card_powerset]
    have hdisj : (Fib : Set (Fin (n * n * b) → Bool)).PairwiseDisjoint N_ow := by
      intro v hv v' hv' hne
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, hFib] at hv hv'
      rw [Function.onFun, Finset.disjoint_left]
      intro u hu hu'
      obtain ⟨S₁, -, rfl⟩ := Finset.mem_image.1 hu
      obtain ⟨S₂, -, hSS'⟩ := Finset.mem_image.1 hu'
      apply hne
      have hout_eq : ∀ d : Fin (n * n * b), d.val ∉ freeC v → d.val ∉ freeC v' →
          v d = v' d := by
        intro d hd hd'
        have := congrFun hSS'.symm d
        simp only [overwrite, hd, hd', ite_false] at this
        exact this
      have hcode_eq : gCode v = gCode v' := hv.2.trans hv'.2.symm
      have hcomb := coarseForestCombAgreeOn (hcv v hv.1) (hcv v' hv'.1) (hpv v hv.1) (hpv v' hv'.1)
        (o₁ := o₁) (o₂ := o₂)
        (fun α hα => by
          have := congrFun hcode_eq ⟨α, hα⟩
          simp only [gCode, dite_eq_left hv.1, dite_eq_left hv'.1, Prod.mk.injEq] at this
          exact this)
        (fun d hd hd' => by
          have hdL : d < n * n * b := Finset.mem_range.1 (Finset.mem_filter.1 hd).1
          rw [nth_ofFn v hdL, nth_ofFn v' hdL]
          congr 1
          apply hout_eq ⟨d, hdL⟩
          · intro hF; exact (Finset.mem_sdiff.1 hF).2 hd
          · intro hF; exact (Finset.mem_sdiff.1 hF).2 hd')
      funext d
      by_cases hdc : d.val ∈ combSet n b o₁ o₂
      · have := hcomb d.val hdc
        rw [nth_ofFn v d.isLt, nth_ofFn v' d.isLt] at this
        exact Option.some.inj this
      · apply hout_eq d
        · intro hF; exact hdc (Finset.mem_sdiff.1 hF).1
        · intro hF; exact hdc (Finset.mem_sdiff.1 hF).1
    calc ∑ v ∈ Fib, 2 ^ (freeC v).card = ∑ v ∈ Fib, (N_ow v).card :=
          Finset.sum_congr rfl (fun v _ => (hN v).symm)
      _ = (Fib.biUnion N_ow).card := (Finset.card_biUnion hdisj).symm
      _ ≤ Fintype.card (Fin (n * n * b) → Bool) := Finset.card_le_univ _
      _ = 2 ^ (n * n * b) := by simp
  calc ∑ v ∈ V, 2 ^ (freeC v).card
      = ∑ c ∈ box, ∑ v ∈ V.filter (fun v => gCode v = c), 2 ^ (freeC v).card :=
        (Finset.sum_fiberwise_of_maps_to (fun v hv => hbox v hv) _).symm
    _ ≤ ∑ _c ∈ box, 2 ^ (n * n * b) := Finset.sum_le_sum hfiber
    _ = box.card * 2 ^ (n * n * b) := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ (structCount M.k T * coarseSideCount M B_bank A S) ^ addrCount B_bank.card r *
          2 ^ (n * n * b) := Nat.mul_le_mul_right _ hcard_box
    _ = _ := Nat.mul_comm _ _

/-- Node-structure bit overhead `(k + 4) ⌈log₂(2T + 1)⌉` at time cap `T`. -/
def structBitsAtTime (k T : ℕ) : ℕ :=
  (k + 4) * Nat.clog 2 (2 * T + 1)

/-- Adaptive per-node entry-data bit cost `σ_{M, A, S}^{adap}` for the coarse-monotone,
workspace-folded grouped pass bound. -/
def adapEntryBits (M : TM) (B_bank : Finset (Fin M.k)) (A : ℕ) (S : Fin M.k → ℕ) : ℕ :=
  Nat.clog 2 (M.q + 1) + B_bank.card +
    (∑ t ∈ Finset.univ \ B_bank, Nat.clog 2 (S t + 1)) +
    (B_bank.card * (3 * A + 1) + workspaceCellSum B_bank S) * Nat.clog 2 (M.g + 1)

theorem coarseSideCount_le_pow (M : TM) (B_bank : Finset (Fin M.k)) (A : ℕ) (S : Fin M.k → ℕ) :
    coarseSideCount M B_bank A S ≤ 2 ^ adapEntryBits M B_bank A S := by
  unfold coarseSideCount adapEntryBits
  have hq : M.q + 1 ≤ 2 ^ Nat.clog 2 (M.q + 1) := Nat.le_pow_clog (by norm_num) _
  have hprod : ∏ t ∈ Finset.univ \ B_bank, (S t + 1) ≤
      2 ^ (∑ t ∈ Finset.univ \ B_bank, Nat.clog 2 (S t + 1)) := by
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_le_prod (fun t _ => Nat.le_pow_clog (by norm_num) (S t + 1))
  have hg : (M.g + 1) ^ (B_bank.card * (3 * A + 1) + workspaceCellSum B_bank S) ≤
      2 ^ ((B_bank.card * (3 * A + 1) + workspaceCellSum B_bank S) * Nat.clog 2 (M.g + 1)) := by
    calc _ ≤ (2 ^ Nat.clog 2 (M.g + 1)) ^
            (B_bank.card * (3 * A + 1) + workspaceCellSum B_bank S) :=
          Nat.pow_le_pow_left (Nat.le_pow_clog (by norm_num) _) _
      _ = _ := by rw [← pow_mul, Nat.mul_comm (Nat.clog 2 (M.g + 1))]
  calc (M.q + 1) * 2 ^ B_bank.card * (∏ t ∈ Finset.univ \ B_bank, (S t + 1)) *
        (M.g + 1) ^ (B_bank.card * (3 * A + 1) + workspaceCellSum B_bank S)
      ≤ 2 ^ Nat.clog 2 (M.q + 1) * 2 ^ B_bank.card *
          2 ^ (∑ t ∈ Finset.univ \ B_bank, Nat.clog 2 (S t + 1)) *
          2 ^ ((B_bank.card * (3 * A + 1) + workspaceCellSum B_bank S) * Nat.clog 2 (M.g + 1)) :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_right _ hq) hprod) hg
    _ = _ := by simp only [← pow_add]

theorem struct_mul_coarseSide_le_pow (M : TM) (T : ℕ) (B_bank : Finset (Fin M.k)) (A : ℕ)
    (S : Fin M.k → ℕ) :
    structCount M.k T * coarseSideCount M B_bank A S ≤
      2 ^ (structBitsAtTime M.k T + adapEntryBits M B_bank A S) := by
  rw [pow_add]
  exact Nat.mul_le_mul (structCount_le_pow M.k T) (coarseSideCount_le_pow M B_bank A S)

/-- **Adaptive Coarse-Monotone & Workspace-Folded Grouped Pass Bound on a Set of Co-Entropy `≤ m`
(Log-Free Form)**. -/
theorem theoremPprime_coarseWorkspace_grouped_on {M : TM} {d b T r γ A_in A : ℕ}
    {B_bank : Finset (Fin M.k)} {S : Fin M.k → ℕ} {W : Set (List Bool)}
    (hrun : ∀ w ∈ W, ∃ T' ≤ T, ∃ p, CoarseWorkspacePartition M w T' r B_bank A_in A S p ∧
      ∃ Mat : Matrix, w = encode d b Mat ∧
        (run M w T').outRev.reverse = encode d b (transpose Mat))
    (hγ : 1 ≤ γ) {m : ℕ} (hco : 2 ^ (d * d * b) ≤ 2 ^ m * W.ncard) :
    2 ^ (d * d * b) ≤
      2 ^ (numGroups d γ * m) *
        (2 ^ (addrCount B_bank.card r * ((γ + 1) * d * b + 2 * A_in)) *
          (structCount M.k T * coarseSideCount M B_bank A S) ^
            (numGroups d γ * addrCount B_bank.card r)) := by
  classical
  have hW : W ⊆ matrixInputs d b := fun w hw => by
    obtain ⟨-, -, -, -, Mat, rfl, -⟩ := hrun w hw
    exact ⟨Mat, rfl⟩
  set V := (Finset.univ : Finset (Fin (d * d * b) → Bool)).filter (fun v => List.ofFn v ∈ W)
    with hV
  have hVcard : W.ncard = V.card := by
    rw [← ncard_ofFn_preimage hW, ← Set.ncard_coe_finset]
    congr 1
    ext v
    rw [Set.mem_ofPred_eq, Finset.mem_coe, hV, Finset.mem_filter]
    exact ⟨fun h => ⟨Finset.mem_univ _, h⟩, fun h => h.2⟩
  have hVne : V.Nonempty := by
    rw [← Finset.card_pos, ← hVcard]; exact ncard_pos_of_coentropy hco
  have hmem : ∀ v ∈ V, List.ofFn v ∈ W := fun v h => (Finset.mem_filter.1 h).2
  have hrun' : ∀ v : Fin (d * d * b) → Bool, ∃ T' ≤ T, ∃ p : ℕ → ℕ, List.ofFn v ∈ W →
      CoarseWorkspacePartition M (List.ofFn v) T' r B_bank A_in A S p ∧
      ∃ Mat : Matrix, List.ofFn v = encode d b Mat ∧
        (run M (List.ofFn v) T').outRev.reverse = encode d b (transpose Mat) := by
    intro v
    by_cases hv : List.ofFn v ∈ W
    · obtain ⟨T', hT', p, h⟩ := hrun _ hv
      exact ⟨T', hT', p, fun _ => h⟩
    · exact ⟨0, Nat.zero_le _, fun _ => 0, fun h => absurd h hv⟩
  choose Tv hTv pv hv using hrun'
  set K := (structCount M.k T * coarseSideCount M B_bank A S) ^ addrCount B_bank.card r with hK
  set G := numGroups d γ
  let mm : ℕ → (Fin (d * d * b) → Bool) → ℕ := fun s v =>
    (combSet d b (segLo d b γ s) (segHi d b γ s) \ readSet (inTraj M (List.ofFn v)) (d * d * b)
      (forestCoarse M (List.ofFn v) B_bank (pv v) r A (segLo d b γ s) (segHi d b γ s))).card
  have hsum : ∑ v ∈ V, ∑ s ∈ Finset.range G, 2 ^ mm s v ≤ ∑ _v ∈ V, G * (K * 2 ^ m) := by
    rw [Finset.sum_comm]
    calc ∑ s ∈ Finset.range G, ∑ v ∈ V, 2 ^ mm s v
        ≤ ∑ _s ∈ Finset.range G, 2 ^ (d * d * b) * K :=
          Finset.sum_le_sum (fun s _ => kraft_coarseWorkspace_group_on V Tv pv (fun v _ => hTv v)
            (fun v h => (hv v (hmem v h)).1) (fun v h => (hv v (hmem v h)).2))
      _ = G * (2 ^ (d * d * b) * K) := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
      _ ≤ G * (2 ^ m * V.card * K) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (hVcard ▸ hco))
      _ = ∑ _v ∈ V, G * (K * 2 ^ m) := by rw [Finset.sum_const, smul_eq_mul]; ring
  obtain ⟨v₀, hv₀V, hv₀⟩ := Finset.exists_le_of_sum_le hVne hsum
  calc _ ≤ _ := pow_le_of_sum_pow_le (fun s => mm s v₀)
        (comb_split_coarse_le (n := d) (b := b) (hv v₀ (hmem v₀ hv₀V)).1 hγ) hv₀
    _ = _ := by rw [mul_pow, hK, ← pow_mul, ← pow_mul]; ring

/-- **Adaptive Coarse-Monotone & Workspace-Folded Grouped Pass Bound on a Set of Co-Entropy `≤ m`
(Bits Form)**:
`d² b ≤ ⌈d/γ⌉ m + H(k_b, r) ((γ + 1) d b + 2 A_in + ⌈d/γ⌉ (γ_T + σ_{M, A, S}^{adap}))`. -/
theorem theoremPprime_coarseWorkspace_grouped_on_bits {M : TM} {d b T r γ A_in A : ℕ}
    {B_bank : Finset (Fin M.k)} {S : Fin M.k → ℕ} {W : Set (List Bool)}
    (hrun : ∀ w ∈ W, ∃ T' ≤ T, ∃ p, CoarseWorkspacePartition M w T' r B_bank A_in A S p ∧
      ∃ Mat : Matrix, w = encode d b Mat ∧
        (run M w T').outRev.reverse = encode d b (transpose Mat))
    (hγ : 1 ≤ γ) {m : ℕ} (hco : 2 ^ (d * d * b) ≤ 2 ^ m * W.ncard) :
    d * d * b ≤ numGroups d γ * m + addrCount B_bank.card r *
      ((γ + 1) * d * b + 2 * A_in +
        numGroups d γ * (structBitsAtTime M.k T + adapEntryBits M B_bank A S)) :=
  bits_of_logfree (struct_mul_coarseSide_le_pow M T B_bank A S)
    (theoremPprime_coarseWorkspace_grouped_on hrun hγ hco)

/-- When `1 ≤ k_b`, `addrCount k_b r < (k_b + 1) ^ r`. -/
theorem addrCount_lt_pow_of_pos {k_b : ℕ} (hk : 1 ≤ k_b) (r : ℕ) :
    addrCount k_b r < (k_b + 1) ^ r := by
  induction r with
  | zero => simp [addrCount]
  | succ r ih =>
    unfold addrCount at ih ⊢
    rw [Finset.sum_range_succ]
    have hpos : 1 ≤ (k_b + 1) ^ r := Nat.one_le_pow r (k_b + 1) (by omega)
    calc ∑ P₀ ∈ Finset.range r, (k_b + 1) ^ P₀ + (k_b + 1) ^ r
        < (k_b + 1) ^ r + (k_b + 1) ^ r := Nat.add_lt_add_right ih _
      _ = 2 * (k_b + 1) ^ r := by ring
      _ ≤ (k_b + 1) * (k_b + 1) ^ r := Nat.mul_le_mul_right _ (by omega)
      _ = (k_b + 1) ^ (r + 1) := by ring

/-- **Single-Scale Exclusion (Oblivious)**: if the grouped right-hand side is strictly less than
`d² b`, no such oblivious `r`-pass `CoarseWorkspacePartition` exists. -/
theorem oblivious_singleScale_coarseWorkspace_excludes {M : TM} {d b T r γ A_in A m : ℕ}
    {B_bank : Finset (Fin M.k)} {S : Fin M.k → ℕ} {W : Set (List Bool)}
    (hobl : ObliviousOn M W T) (hcorr : ClassCorrect M d b T W)
    {w₀ : List Bool} (hw₀ : w₀ ∈ W) {p : ℕ → ℕ}
    (hp : CoarseWorkspacePartition M w₀ T r B_bank A_in A S p)
    (hγ : 1 ≤ γ) (hco : 2 ^ (d * d * b) ≤ 2 ^ m * W.ncard)
    (hlt : numGroups d γ * m + addrCount B_bank.card r *
      ((γ + 1) * d * b + 2 * A_in + numGroups d γ * oblEntryBits M B_bank A S) < d * d * b) :
    False := by
  have hle := theoremP_coarseWorkspace_grouped_on_bits hobl hcorr hw₀ hp hγ hco
  omega

/-- **Single-Scale Exclusion (Adaptive)**: if the adaptive grouped right-hand side is strictly less
than `d² b`, no family of adaptive `≤ r`-pass `CoarseWorkspacePartition`s up to time `T` exists. -/
theorem adaptive_singleScale_coarseWorkspace_excludes {M : TM} {d b T r γ A_in A m : ℕ}
    {B_bank : Finset (Fin M.k)} {S : Fin M.k → ℕ} {W : Set (List Bool)}
    (hrun : ∀ w ∈ W, ∃ T' ≤ T, ∃ r' ≤ r, ∃ p,
      CoarseWorkspacePartition M w T' r' B_bank A_in A S p ∧
      ∃ Mat : Matrix, w = encode d b Mat ∧
        (run M w T').outRev.reverse = encode d b (transpose Mat))
    (hγ : 1 ≤ γ) (hco : 2 ^ (d * d * b) ≤ 2 ^ m * W.ncard)
    (hlt : numGroups d γ * m + addrCount B_bank.card r *
      ((γ + 1) * d * b + 2 * A_in +
        numGroups d γ * (structBitsAtTime M.k T + adapEntryBits M B_bank A S)) < d * d * b) :
    False := by
  have hrun_pad : ∀ w ∈ W, ∃ T' ≤ T, ∃ p,
      CoarseWorkspacePartition M w T' r B_bank A_in A S p ∧
      ∃ Mat : Matrix, w = encode d b Mat ∧
        (run M w T').outRev.reverse = encode d b (transpose Mat) := by
    intro w hw
    obtain ⟨T', hT', r', hr', p, hp, hMat⟩ := hrun w hw
    obtain ⟨p', hp'⟩ := coarseWorkspacePartition_pad hp hr'
    exact ⟨T', hT', p', hp', hMat⟩
  have hle := theoremPprime_coarseWorkspace_grouped_on_bits hrun_pad hγ hco
  omega

/-- **Closed Single-Scale Pass Lower Bound (Oblivious)**: for `k_b ≥ 1`, `d, b, γ ≥ 1` on all
matrix inputs (`m = 0`), `r > log_{k_b + 1}((d² b) / ((γ + 1) d b + 2 A_in + ⌈d/γ⌉ σ^{obl}))`. -/
theorem oblivious_singleScale_coarseWorkspace_closed_lb {M : TM} {d b T r γ A_in A : ℕ}
    {B_bank : Finset (Fin M.k)} {S : Fin M.k → ℕ}
    (hk : 1 ≤ B_bank.card) (hd : 1 ≤ d) (hb : 1 ≤ b) (hγ : 1 ≤ γ)
    (hobl : ObliviousOn M (matrixInputs d b) T)
    (hcorr : ClassCorrect M d b T (matrixInputs d b))
    {w₀ : List Bool} (hw₀ : w₀ ∈ matrixInputs d b) {p : ℕ → ℕ}
    (hp : CoarseWorkspacePartition M w₀ T r B_bank A_in A S p) :
    Real.logb ((B_bank.card : ℝ) + 1)
      ((d * d * b : ℝ) /
        (((γ + 1) * d * b + 2 * A_in + numGroups d γ * oblEntryBits M B_bank A S : ℕ) : ℝ)) <
      (r : ℝ) := by
  have hco : 2 ^ (d * d * b) ≤ 2 ^ 0 * (matrixInputs d b).ncard := by
    rw [ncard_matrixInputs, pow_zero, one_mul]
  have hbits := theoremP_coarseWorkspace_grouped_on_bits hobl hcorr hw₀ hp hγ hco
  simp only [Nat.mul_zero, Nat.zero_add] at hbits
  set D := (γ + 1) * d * b + 2 * A_in + numGroups d γ * oblEntryBits M B_bank A S
  have hD_pos : 0 < D := by dsimp [D]; positivity
  have hL_pos : 0 < d * d * b := by positivity
  have hlt_pow : d * d * b < (B_bank.card + 1) ^ r * D :=
    lt_of_le_of_lt hbits (Nat.mul_lt_mul_of_pos_right (addrCount_lt_pow_of_pos hk r) hD_pos)
  have hdiv_lt : (d * d * b : ℝ) / (D : ℝ) < (((B_bank.card : ℝ) + 1) ^ r) := by
    rw [div_lt_iff₀ (by exact_mod_cast hD_pos)]
    exact_mod_cast hlt_pow
  have hbase : (1 : ℝ) < (B_bank.card : ℝ) + 1 := by exact_mod_cast (show 1 < B_bank.card + 1 by omega)
  have hlog := Real.logb_lt_logb hbase (div_pos (by exact_mod_cast hL_pos) (by exact_mod_cast hD_pos))
    hdiv_lt
  rw [← Real.rpow_natCast, Real.logb_rpow (by linarith) (ne_of_gt hbase)] at hlog
  exact hlog

/-- **Closed Single-Scale Pass Lower Bound (Adaptive)**: for `k_b ≥ 1`, `d, b, γ ≥ 1` on all
matrix inputs (`m = 0`),
`r > log_{k_b + 1}((d² b) / ((γ + 1) d b + 2 A_in + ⌈d/γ⌉ (γ_T + σ^{adap})))`. -/
theorem adaptive_singleScale_coarseWorkspace_closed_lb {M : TM} {d b T r γ A_in A : ℕ}
    {B_bank : Finset (Fin M.k)} {S : Fin M.k → ℕ}
    (hk : 1 ≤ B_bank.card) (hd : 1 ≤ d) (hb : 1 ≤ b) (hγ : 1 ≤ γ)
    (hrun : ∀ w ∈ matrixInputs d b, ∃ T' ≤ T, ∃ r' ≤ r, ∃ p,
      CoarseWorkspacePartition M w T' r' B_bank A_in A S p ∧
      ∃ Mat : Matrix, w = encode d b Mat ∧
        (run M w T').outRev.reverse = encode d b (transpose Mat)) :
    Real.logb ((B_bank.card : ℝ) + 1)
      ((d * d * b : ℝ) /
        (((γ + 1) * d * b + 2 * A_in +
          numGroups d γ * (structBitsAtTime M.k T + adapEntryBits M B_bank A S) : ℕ) : ℝ)) <
      (r : ℝ) := by
  have hrun_pad : ∀ w ∈ matrixInputs d b, ∃ T' ≤ T, ∃ p,
      CoarseWorkspacePartition M w T' r B_bank A_in A S p ∧
      ∃ Mat : Matrix, w = encode d b Mat ∧
        (run M w T').outRev.reverse = encode d b (transpose Mat) := by
    intro w hw
    obtain ⟨T', hT', r', hr', p, hp, hMat⟩ := hrun w hw
    obtain ⟨p', hp'⟩ := coarseWorkspacePartition_pad hp hr'
    exact ⟨T', hT', p', hp', hMat⟩
  have hco : 2 ^ (d * d * b) ≤ 2 ^ 0 * (matrixInputs d b).ncard := by
    rw [ncard_matrixInputs, pow_zero, one_mul]
  have hbits := theoremPprime_coarseWorkspace_grouped_on_bits hrun_pad hγ hco
  simp only [Nat.mul_zero, Nat.zero_add] at hbits
  set D := (γ + 1) * d * b + 2 * A_in +
    numGroups d γ * (structBitsAtTime M.k T + adapEntryBits M B_bank A S)
  have hD_pos : 0 < D := by dsimp [D]; positivity
  have hL_pos : 0 < d * d * b := by positivity
  have hlt_pow : d * d * b < (B_bank.card + 1) ^ r * D :=
    lt_of_le_of_lt hbits (Nat.mul_lt_mul_of_pos_right (addrCount_lt_pow_of_pos hk r) hD_pos)
  have hdiv_lt : (d * d * b : ℝ) / (D : ℝ) < (((B_bank.card : ℝ) + 1) ^ r) := by
    rw [div_lt_iff₀ (by exact_mod_cast hD_pos)]
    exact_mod_cast hlt_pow
  have hbase : (1 : ℝ) < (B_bank.card : ℝ) + 1 := by exact_mod_cast (show 1 < B_bank.card + 1 by omega)
  have hlog := Real.logb_lt_logb hbase (div_pos (by exact_mod_cast hL_pos) (by exact_mod_cast hD_pos))
    hdiv_lt
  rw [← Real.rpow_natCast, Real.logb_rpow (by linarith) (ne_of_gt hbase)] at hlog
  exact hlog

/-! ## §5. Sub-Critical Phase-Profile and Bounded-Pass Exclusions, and the Limit `1 / 2` -/

private theorem self_le_two_pow_entryBits {d : ℕ} (hd : 1 ≤ d) : d ≤ 2 ^ entryBits d := by
  unfold entryBits
  rcases eq_or_lt_of_le hd with rfl | hd2
  · simp
  · have hpos : d - 1 ≠ 0 := by omega
    have hlt := Nat.lt_log2_self (n := d - 1)
    omega

private theorem canonicalLen_le_two_pow_three_entryBits {d : ℕ} (hd : 1 ≤ d) :
    d * d * entryBits d ≤ 2 ^ (3 * entryBits d) := by
  have h1 : d ≤ 2 ^ entryBits d := self_le_two_pow_entryBits hd
  have h2 : entryBits d ≤ 2 ^ entryBits d := le_of_lt Nat.lt_two_pow_self
  calc d * d * entryBits d
      ≤ 2 ^ entryBits d * 2 ^ entryBits d * 2 ^ entryBits d :=
        Nat.mul_le_mul (Nat.mul_le_mul h1 h1) h2
    _ = 2 ^ (3 * entryBits d) := by rw [← pow_add, ← pow_add]; ring_nf

private theorem eventually_const_mul_nat_rpow_lt_one (K : ℝ) {e : ℝ} (he : e < 0) :
    ∀ᶠ d : ℕ in atTop, K * (d : ℝ) ^ e < 1 := by
  have h1 : Tendsto (fun x : ℝ => x ^ (-(-e))) atTop (nhds 0) :=
    tendsto_rpow_neg_atTop (neg_pos.2 he)
  simp only [neg_neg] at h1
  have h2 : Tendsto (fun d : ℕ => K * (d : ℝ) ^ e) atTop (nhds (K * 0)) :=
    (h1.comp tendsto_natCast_atTop_atTop).const_mul K
  rw [mul_zero] at h2
  exact (tendsto_order.1 h2).2 1 (by norm_num)

/-- Unified asymptotic engine: whenever `1 ≤ k_b`, `θ ∈ (0, 2]`, and
`A_slope * log₂(k_b + 1) < 1 / 2`, for all sufficiently large `d`, choosing
`γ_d := ⌈d^{1 - θ/2}⌉` makes the grouped pass RHS strictly smaller than `d² * entryBits d`. -/
private theorem subcritical_grouped_rhs_lt_eventually
    {k_b : ℕ} (hk : 1 ≤ k_b) {θ A_slope : ℝ} (C_0 : ℝ) {C_in C_coeff C_log : ℝ}
    (hθ_pos : 0 < θ) (hθ_le : θ ≤ 2)
    (hslope : A_slope * Real.logb 2 ((k_b : ℝ) + 1) < 1 / 2)
    (hCin : 0 ≤ C_in) (hCcoeff : 0 ≤ C_coeff) (hClog : 0 ≤ C_log) :
    ∀ᶠ d : ℕ in atTop,
      ∃ γ : ℕ, 1 ≤ γ ∧
        ∀ (r A_in σ_tot : ℕ),
          (r : ℝ) ≤ A_slope * Real.logb 2 (1 / (d : ℝ) ^ (-θ)) + C_0 →
          (A_in : ℝ) ≤ C_in * (d : ℝ) ^ (-θ) * (d * d * entryBits d : ℝ) →
          (σ_tot : ℝ) ≤ C_coeff * (d : ℝ) ^ (-θ) * (d * d * entryBits d : ℝ) +
            C_log * (entryBits d : ℝ) →
          addrCount k_b r * ((γ + 1) * d * entryBits d + 2 * A_in + numGroups d γ * σ_tot) <
            d * d * entryBits d := by
  set ψ := A_slope * Real.logb 2 ((k_b : ℝ) + 1)
  have hbase2 : (1 : ℝ) < 2 := by norm_num
  have hkb2 : (2 : ℝ) ≤ (k_b : ℝ) + 1 := by exact_mod_cast (show 2 ≤ k_b + 1 by omega)
  have hlog_kb_pos : 0 < Real.logb 2 ((k_b : ℝ) + 1) :=
    Real.logb_pos hbase2 (by linarith)
  set K_par : ℝ := 3 + 2 * C_in + 2 * (C_coeff + C_log)
  have hKpar_pos : 0 < K_par := by dsimp [K_par]; linarith
  set K_r : ℝ := (2 : ℝ) ^ (C_0 * Real.logb 2 ((k_b : ℝ) + 1))
  have hKr_pos : 0 < K_r := Real.rpow_pos_of_pos (by norm_num) _
  have hexp_neg : (ψ - 1 / 2) * θ < 0 := mul_neg_of_neg_of_pos (by linarith) hθ_pos
  filter_upwards [eventually_ge_atTop (2 : ℕ),
    eventually_const_mul_nat_rpow_lt_one (K_r * K_par) hexp_neg] with d hd2 hlt1
  have hd_pos : (0 : ℝ) < (d : ℝ) := by positivity
  have hd_ge1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (show 1 ≤ d by omega)
  set γ : ℕ := Nat.ceil ((d : ℝ) ^ (1 - θ / 2))
  have h1_sub_nonneg : 0 ≤ 1 - θ / 2 := by linarith
  have hd_pow_ge1 : (1 : ℝ) ≤ (d : ℝ) ^ (1 - θ / 2) := by
    calc (1 : ℝ) = (d : ℝ) ^ (0 : ℝ) := (Real.rpow_zero _).symm
      _ ≤ (d : ℝ) ^ (1 - θ / 2) := Real.rpow_le_rpow_of_exponent_le hd_ge1 h1_sub_nonneg
  have hγ_ge1 : 1 ≤ γ := by
    exact_mod_cast (le_trans hd_pow_ge1 (Nat.le_ceil _))
  refine ⟨γ, hγ_ge1, fun r A_in σ_tot hr hAin hσ => ?_⟩
  set b := entryBits d
  have hb_pos : 1 ≤ b := by unfold b entryBits; omega
  set L : ℕ := d * d * b
  have hL_pos : (0 : ℝ) < (L : ℝ) := by dsimp [L]; positivity
  have hL_cast : (d : ℝ) * (d : ℝ) * (b : ℝ) = (L : ℝ) := by dsimp [L]; push_cast; ring
  have hAinL : (A_in : ℝ) ≤ C_in * (d : ℝ) ^ (-θ) * (L : ℝ) := by rwa [← hL_cast]
  have hσL : (σ_tot : ℝ) ≤ C_coeff * (d : ℝ) ^ (-θ) * (L : ℝ) + C_log * (b : ℝ) := by
    rwa [← hL_cast]
  have hγ_le : (γ : ℝ) ≤ 2 * (d : ℝ) ^ (1 - θ / 2) := by
    have hceil : (γ : ℝ) < (d : ℝ) ^ (1 - θ / 2) + 1 := Nat.ceil_lt_add_one (by positivity)
    linarith
  have hγ1_div : ((γ + 1 : ℕ) : ℝ) / (d : ℝ) ≤ 3 * (d : ℝ) ^ (-θ / 2) := by
    have hnum : ((γ + 1 : ℕ) : ℝ) ≤ 3 * (d : ℝ) ^ (1 - θ / 2) := by
      push_cast; linarith
    calc ((γ + 1 : ℕ) : ℝ) / (d : ℝ)
        ≤ (3 * (d : ℝ) ^ (1 - θ / 2)) / (d : ℝ) :=
          div_le_div_of_nonneg_right hnum (le_of_lt hd_pos)
      _ = 3 * ((d : ℝ) ^ (1 - θ / 2) * (d : ℝ) ^ (-1 : ℝ)) := by
          rw [div_eq_mul_inv, mul_assoc, Real.rpow_neg_one]
      _ = 3 * (d : ℝ) ^ (-θ / 2) := by
          rw [← Real.rpow_add hd_pos]; ring_nf
  have hG_le : (numGroups d γ : ℝ) ≤ 2 * (d : ℝ) ^ (θ / 2) := by
    have hng : numGroups d γ ≤ d / γ + 1 := by
      unfold numGroups
      have hdiv : (d + γ - 1) / γ ≤ (d + γ) / γ := Nat.div_le_div_right (by omega)
      rw [Nat.add_div_right _ (by omega)] at hdiv
      exact hdiv
    have hd_div_γ : ((d / γ : ℕ) : ℝ) ≤ (d : ℝ) / (γ : ℝ) :=
      Nat.cast_div_le
    have hγ_ge_pow : (d : ℝ) ^ (1 - θ / 2) ≤ (γ : ℝ) := Nat.le_ceil _
    have hpow_ge1 : (1 : ℝ) ≤ (d : ℝ) ^ (θ / 2) := by
      calc (1 : ℝ) = (d : ℝ) ^ (0 : ℝ) := (Real.rpow_zero _).symm
        _ ≤ (d : ℝ) ^ (θ / 2) := Real.rpow_le_rpow_of_exponent_le hd_ge1 (by linarith)
    have hquot : (d : ℝ) / (γ : ℝ) ≤ (d : ℝ) ^ (θ / 2) := by
      calc (d : ℝ) / (γ : ℝ)
          ≤ (d : ℝ) / (d : ℝ) ^ (1 - θ / 2) :=
            div_le_div_of_nonneg_left (le_of_lt hd_pos) (by positivity) hγ_ge_pow
        _ = (d : ℝ) ^ (1 : ℝ) * (d : ℝ) ^ (-(1 - θ / 2)) := by
            rw [Real.rpow_one, div_eq_mul_inv, Real.rpow_neg (le_of_lt hd_pos)]
        _ = (d : ℝ) ^ (θ / 2) := by rw [← Real.rpow_add hd_pos]; ring_nf
    calc (numGroups d γ : ℝ)
        ≤ ((d / γ + 1 : ℕ) : ℝ) := by exact_mod_cast hng
      _ = ((d / γ : ℕ) : ℝ) + 1 := by push_cast; ring
      _ ≤ (d : ℝ) ^ (θ / 2) + 1 := by linarith
      _ ≤ 2 * (d : ℝ) ^ (θ / 2) := by linarith
  have hd_m2_le : (d : ℝ) ^ (-2 : ℝ) ≤ (d : ℝ) ^ (-θ) :=
    Real.rpow_le_rpow_of_exponent_le hd_ge1 (by linarith)
  have hd_mθ_le : (d : ℝ) ^ (-θ) ≤ (d : ℝ) ^ (-θ / 2) :=
    Real.rpow_le_rpow_of_exponent_le hd_ge1 (by linarith)
  have hσ_div : (σ_tot : ℝ) / (L : ℝ) ≤ (C_coeff + C_log) * (d : ℝ) ^ (-θ) := by
    have hL_eq : (L : ℝ) = (d : ℝ) ^ (2 : ℝ) * (b : ℝ) := by
      dsimp [L]; push_cast; rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
    have hb_div : (b : ℝ) / (L : ℝ) = (d : ℝ) ^ (-2 : ℝ) := by
      calc (b : ℝ) / (L : ℝ)
          = ((b : ℝ) * 1) / ((b : ℝ) * (d : ℝ) ^ (2 : ℝ)) := by rw [hL_eq]; ring
        _ = 1 / (d : ℝ) ^ (2 : ℝ) := mul_div_mul_left 1 _ (by positivity : (b : ℝ) ≠ 0)
        _ = (d : ℝ) ^ (-2 : ℝ) := by rw [one_div, ← Real.rpow_neg (le_of_lt hd_pos)]
    calc (σ_tot : ℝ) / (L : ℝ)
        ≤ (C_coeff * (d : ℝ) ^ (-θ) * (L : ℝ) + C_log * (b : ℝ)) / (L : ℝ) :=
          div_le_div_of_nonneg_right hσL (le_of_lt hL_pos)
      _ = C_coeff * (d : ℝ) ^ (-θ) + C_log * ((b : ℝ) / (L : ℝ)) := by
          rw [add_div, mul_div_cancel_right₀ _ (ne_of_gt hL_pos), mul_div_assoc]
      _ = C_coeff * (d : ℝ) ^ (-θ) + C_log * (d : ℝ) ^ (-2 : ℝ) := by rw [hb_div]
      _ ≤ C_coeff * (d : ℝ) ^ (-θ) + C_log * (d : ℝ) ^ (-θ) := by
          linarith [mul_le_mul_of_nonneg_left hd_m2_le hClog]
      _ = (C_coeff + C_log) * (d : ℝ) ^ (-θ) := by ring
  have hpar_div :
      (((γ + 1) * d * b + 2 * A_in + numGroups d γ * σ_tot : ℕ) : ℝ) / (L : ℝ) ≤
        K_par * (d : ℝ) ^ (-θ / 2) := by
    have h1 : (((γ + 1) * d * b : ℕ) : ℝ) / (L : ℝ) = ((γ + 1 : ℕ) : ℝ) / (d : ℝ) := by
      dsimp [L]
      push_cast
      have hdb : (d : ℝ) * (b : ℝ) ≠ 0 := by positivity
      calc ((γ : ℝ) + 1) * (d : ℝ) * (b : ℝ) / ((d : ℝ) * (d : ℝ) * (b : ℝ))
          = (((γ : ℝ) + 1) * ((d : ℝ) * (b : ℝ))) / ((d : ℝ) * ((d : ℝ) * (b : ℝ))) := by ring
        _ = ((γ : ℝ) + 1) / (d : ℝ) := mul_div_mul_right _ _ hdb
    have h2 : ((2 * A_in : ℕ) : ℝ) / (L : ℝ) ≤ 2 * C_in * (d : ℝ) ^ (-θ / 2) := by
      calc ((2 * A_in : ℕ) : ℝ) / (L : ℝ)
          ≤ (2 * (C_in * (d : ℝ) ^ (-θ) * (L : ℝ))) / (L : ℝ) := by
            push_cast; exact div_le_div_of_nonneg_right (by linarith [hAinL]) (le_of_lt hL_pos)
        _ = 2 * C_in * (d : ℝ) ^ (-θ) := by
            rw [show 2 * (C_in * (d : ℝ) ^ (-θ) * (L : ℝ)) =
              (2 * C_in * (d : ℝ) ^ (-θ)) * (L : ℝ) by ring,
              mul_div_cancel_right₀ _ (ne_of_gt hL_pos)]
        _ ≤ 2 * C_in * (d : ℝ) ^ (-θ / 2) :=
            mul_le_mul_of_nonneg_left hd_mθ_le (by linarith)
    have h3 : ((numGroups d γ * σ_tot : ℕ) : ℝ) / (L : ℝ) ≤
        2 * (C_coeff + C_log) * (d : ℝ) ^ (-θ / 2) := by
      calc ((numGroups d γ * σ_tot : ℕ) : ℝ) / (L : ℝ)
          = (numGroups d γ : ℝ) * ((σ_tot : ℝ) / (L : ℝ)) := by push_cast; ring
        _ ≤ (2 * (d : ℝ) ^ (θ / 2)) * ((C_coeff + C_log) * (d : ℝ) ^ (-θ)) :=
            mul_le_mul hG_le hσ_div (by positivity) (by positivity)
        _ = 2 * (C_coeff + C_log) * ((d : ℝ) ^ (θ / 2) * (d : ℝ) ^ (-θ)) := by ring
        _ = 2 * (C_coeff + C_log) * (d : ℝ) ^ (-θ / 2) := by
            rw [← Real.rpow_add hd_pos]; ring_nf
    calc (((γ + 1) * d * b + 2 * A_in + numGroups d γ * σ_tot : ℕ) : ℝ) / (L : ℝ)
        = (((γ + 1) * d * b : ℕ) : ℝ) / (L : ℝ) + ((2 * A_in : ℕ) : ℝ) / (L : ℝ) +
            ((numGroups d γ * σ_tot : ℕ) : ℝ) / (L : ℝ) := by
          push_cast; ring
      _ ≤ 3 * (d : ℝ) ^ (-θ / 2) + 2 * C_in * (d : ℝ) ^ (-θ / 2) +
            2 * (C_coeff + C_log) * (d : ℝ) ^ (-θ / 2) := by
          rw [h1]; linarith [hγ1_div, h2, h3]
      _ = K_par * (d : ℝ) ^ (-θ / 2) := by dsimp [K_par]; ring
  have hlog_inv : Real.logb 2 (1 / (d : ℝ) ^ (-θ)) = θ * Real.logb 2 (d : ℝ) := by
    rw [one_div, ← Real.rpow_neg (le_of_lt hd_pos), neg_neg,
      Real.logb_rpow_eq_mul_logb_of_pos hd_pos]
  have haddr_le : (addrCount k_b r : ℝ) ≤ K_r * (d : ℝ) ^ (ψ * θ) := by
    have hlt_pow : (addrCount k_b r : ℝ) ≤ ((k_b : ℝ) + 1) ^ (r : ℝ) := by
      rw [Real.rpow_natCast]
      exact_mod_cast le_of_lt (addrCount_lt_pow_of_pos hk r)
    have hr_log : (r : ℝ) * Real.logb 2 ((k_b : ℝ) + 1) ≤
        ψ * θ * Real.logb 2 (d : ℝ) + C_0 * Real.logb 2 ((k_b : ℝ) + 1) := by
      have hr' : (r : ℝ) ≤ A_slope * (θ * Real.logb 2 (d : ℝ)) + C_0 := by
        rwa [hlog_inv] at hr
      have := mul_le_mul_of_nonneg_right hr' (le_of_lt hlog_kb_pos)
      dsimp [ψ]
      linarith
    have hkb_eq : ((k_b : ℝ) + 1) ^ (r : ℝ) =
        (2 : ℝ) ^ ((r : ℝ) * Real.logb 2 ((k_b : ℝ) + 1)) := by
      conv_lhs => rw [← Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)
        (by positivity : (0 : ℝ) < (k_b : ℝ) + 1)]
      rw [← Real.rpow_mul (by norm_num)]
      ring_nf
    have hd_eq : (2 : ℝ) ^ (ψ * θ * Real.logb 2 (d : ℝ)) = (d : ℝ) ^ (ψ * θ) := by
      rw [mul_comm (ψ * θ), Real.rpow_mul (by norm_num),
        Real.rpow_logb (by norm_num) (by norm_num) hd_pos]
    calc (addrCount k_b r : ℝ)
        ≤ (2 : ℝ) ^ ((r : ℝ) * Real.logb 2 ((k_b : ℝ) + 1)) := hlt_pow.trans_eq hkb_eq
      _ ≤ (2 : ℝ) ^ (ψ * θ * Real.logb 2 (d : ℝ) + C_0 * Real.logb 2 ((k_b : ℝ) + 1)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hr_log
      _ = K_r * (d : ℝ) ^ (ψ * θ) := by
          rw [Real.rpow_add (by norm_num), hd_eq, mul_comm]
  have hprod_lt1 :
      ((addrCount k_b r * ((γ + 1) * d * b + 2 * A_in + numGroups d γ * σ_tot) : ℕ) : ℝ) /
        (L : ℝ) < 1 := by
    calc ((addrCount k_b r * ((γ + 1) * d * b + 2 * A_in + numGroups d γ * σ_tot) : ℕ) : ℝ) /
          (L : ℝ)
        = (addrCount k_b r : ℝ) *
            ((((γ + 1) * d * b + 2 * A_in + numGroups d γ * σ_tot : ℕ) : ℝ) / (L : ℝ)) := by
          push_cast; ring
      _ ≤ (K_r * (d : ℝ) ^ (ψ * θ)) * (K_par * (d : ℝ) ^ (-θ / 2)) :=
          mul_le_mul haddr_le hpar_div (by positivity) (by positivity)
      _ = K_r * K_par * ((d : ℝ) ^ (ψ * θ) * (d : ℝ) ^ (-θ / 2)) := by ring
      _ = K_r * K_par * (d : ℝ) ^ ((ψ - 1 / 2) * θ) := by
          rw [← Real.rpow_add hd_pos]; ring_nf
      _ < 1 := hlt1
  have hlt_real :
      ((addrCount k_b r * ((γ + 1) * d * b + 2 * A_in + numGroups d γ * σ_tot) : ℕ) : ℝ) <
        (L : ℝ) := (div_lt_one hL_pos).1 hprod_lt1
  exact_mod_cast hlt_real

/-- **Sub-Critical Phase-Profile Exclusion (Oblivious — Arbitrary Unbounded Running Time `T`)**:
for any `M : TM`, bank subset `B_bank` with `k_b = B_bank.card ≥ 1`, exponent `θ ∈ (0, 2]`, and
slope `A_slope` satisfying `A_slope * log₂(k_b + 1) < 1 / 2`, for all sufficiently large `d` and
**every** completion horizon `T : ℕ` (`even super-exponential in d`), `M` cannot transpose all
`d × d` matrices of `entryBits d`-bit entries obliviously at time `T` with an `r`-pass
`CoarseWorkspacePartition` satisfying `r ≤ A_slope * log₂(1 / d^{-θ}) + C_0`. -/
theorem subcriticalPhaseProfile_oblivious_excludes
    (M : TM) (B_bank : Finset (Fin M.k)) (hk : 1 ≤ B_bank.card)
    {θ A_slope C_0 C_in C_amp C_ws : ℝ}
    (hθ_pos : 0 < θ) (hθ_le : θ ≤ 2)
    (hslope : A_slope * Real.logb 2 ((B_bank.card : ℝ) + 1) < 1 / 2)
    (hCin : 0 ≤ C_in) (hCamp : 0 ≤ C_amp) (hCws : 0 ≤ C_ws) :
    ∀ᶠ d : ℕ in atTop,
      ∀ (T r A_in A : ℕ) (S : Fin M.k → ℕ) (w₀ : List Bool) (p : ℕ → ℕ),
        ObliviousOn M (matrixInputs d (entryBits d)) T →
        ClassCorrect M d (entryBits d) T (matrixInputs d (entryBits d)) →
        w₀ ∈ matrixInputs d (entryBits d) →
        CoarseWorkspacePartition M w₀ T r B_bank A_in A S p →
        (A_in : ℝ) ≤ C_in * (d : ℝ) ^ (-θ) * (d * d * entryBits d : ℝ) →
        (A : ℝ) ≤ C_amp * (d : ℝ) ^ (-θ) * (d * d * entryBits d : ℝ) →
        (workspaceCellSum B_bank S : ℝ) ≤ C_ws * (d : ℝ) ^ (-θ) * (d * d * entryBits d : ℝ) →
        (r : ℝ) ≤ A_slope * Real.logb 2 (1 / (d : ℝ) ^ (-θ)) + C_0 →
        False := by
  set β_g : ℝ := (Nat.clog 2 (M.g + 1) : ℝ)
  set C_coeff : ℝ := (3 * (B_bank.card : ℝ) * C_amp + C_ws) * β_g
  set C_log : ℝ := ((Nat.clog 2 (M.q + 1) + B_bank.card * Nat.clog 2 (M.g + 1) : ℕ) : ℝ)
  have hCcoeff : 0 ≤ C_coeff := by dsimp [C_coeff, β_g]; positivity
  have hClog : 0 ≤ C_log := by dsimp [C_log]; positivity
  filter_upwards [subcritical_grouped_rhs_lt_eventually hk C_0 hθ_pos hθ_le hslope hCin hCcoeff hClog]
    with d ⟨γ, hγ, hbound⟩ T r A_in A S w₀ p hobl hcorr hw₀ hp hAin hA hws hr
  have hb_ge1 : (1 : ℝ) ≤ (entryBits d : ℝ) := by
    exact_mod_cast (show 1 ≤ entryBits d by unfold entryBits; omega)
  have hσ : (oblEntryBits M B_bank A S : ℝ) ≤
      C_coeff * (d : ℝ) ^ (-θ) * (d * d * entryBits d : ℝ) + C_log * (entryBits d : ℝ) := by
    have heq : (oblEntryBits M B_bank A S : ℝ) =
        (3 * (B_bank.card : ℝ) * (A : ℝ) + (workspaceCellSum B_bank S : ℝ)) * β_g + C_log := by
      unfold oblEntryBits
      dsimp [β_g, C_log]
      push_cast
      ring
    rw [heq]
    have h1 : (3 * (B_bank.card : ℝ) * (A : ℝ) + (workspaceCellSum B_bank S : ℝ)) * β_g ≤
        C_coeff * (d : ℝ) ^ (-θ) * (d * d * entryBits d : ℝ) := by
      dsimp [C_coeff]
      have hsum : 3 * (B_bank.card : ℝ) * (A : ℝ) + (workspaceCellSum B_bank S : ℝ) ≤
          (3 * (B_bank.card : ℝ) * C_amp + C_ws) * (d : ℝ) ^ (-θ) *
            (d * d * entryBits d : ℝ) := by
        nlinarith [hA, hws]
      have hβg : 0 ≤ β_g := Nat.cast_nonneg _
      have := mul_le_mul_of_nonneg_right hsum hβg
      linarith
    have h2 : C_log ≤ C_log * (entryBits d : ℝ) := le_mul_of_one_le_right hClog hb_ge1
    linarith
  have hco : 2 ^ (d * d * entryBits d) ≤ 2 ^ 0 * (matrixInputs d (entryBits d)).ncard := by
    rw [ncard_matrixInputs, pow_zero, one_mul]
  have hlt := hbound r A_in (oblEntryBits M B_bank A S) hr hAin hσ
  exact oblivious_singleScale_coarseWorkspace_excludes (m := 0) hobl hcorr hw₀ hp hγ hco
    (by simpa using hlt)

/-- Dimension-normalized form (`ε_dim := √ε_d = d^{-θ/2}`, `A_dim * log₂(k_b + 1) < 1`) of
`subcriticalPhaseProfile_oblivious_excludes`. -/
theorem subcriticalDimPhaseProfile_oblivious_excludes
    (M : TM) (B_bank : Finset (Fin M.k)) (hk : 1 ≤ B_bank.card)
    {θ A_dim C_0 C_in C_amp C_ws : ℝ}
    (hθ_pos : 0 < θ) (hθ_le : θ ≤ 2)
    (hslope_dim : A_dim * Real.logb 2 ((B_bank.card : ℝ) + 1) < 1)
    (hCin : 0 ≤ C_in) (hCamp : 0 ≤ C_amp) (hCws : 0 ≤ C_ws) :
    ∀ᶠ d : ℕ in atTop,
      ∀ (T r A_in A : ℕ) (S : Fin M.k → ℕ) (w₀ : List Bool) (p : ℕ → ℕ),
        ObliviousOn M (matrixInputs d (entryBits d)) T →
        ClassCorrect M d (entryBits d) T (matrixInputs d (entryBits d)) →
        w₀ ∈ matrixInputs d (entryBits d) →
        CoarseWorkspacePartition M w₀ T r B_bank A_in A S p →
        (A_in : ℝ) ≤ C_in * (d : ℝ) ^ (-θ) * (d * d * entryBits d : ℝ) →
        (A : ℝ) ≤ C_amp * (d : ℝ) ^ (-θ) * (d * d * entryBits d : ℝ) →
        (workspaceCellSum B_bank S : ℝ) ≤ C_ws * (d : ℝ) ^ (-θ) * (d * d * entryBits d : ℝ) →
        (r : ℝ) ≤ A_dim * Real.logb 2 (1 / Real.sqrt ((d : ℝ) ^ (-θ))) + C_0 →
        False := by
  have hhalf : (A_dim / 2) * Real.logb 2 ((B_bank.card : ℝ) + 1) < 1 / 2 := by linarith
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    subcriticalPhaseProfile_oblivious_excludes M B_bank hk hθ_pos hθ_le hhalf hCin hCamp hCws]
    with d hd1 hexcl T r A_in A S w₀ p hobl hcorr hw₀ hp hAin hA hws hr_dim
  have hd_pos : (0 : ℝ) < (d : ℝ) := by positivity
  have hlog_sqrt : Real.logb 2 (1 / Real.sqrt ((d : ℝ) ^ (-θ))) =
      (1 / 2) * Real.logb 2 (1 / (d : ℝ) ^ (-θ)) := by
    have hpos : (0 : ℝ) < (d : ℝ) ^ (-θ) := Real.rpow_pos_of_pos hd_pos _
    rw [Real.sqrt_eq_rpow, one_div, ← Real.rpow_neg (le_of_lt hpos),
      one_div ((d : ℝ) ^ (-θ)), ← Real.rpow_neg (le_of_lt hd_pos),
      ← Real.rpow_mul (le_of_lt hd_pos)]
    rw [Real.logb_rpow_eq_mul_logb_of_pos hd_pos, Real.logb_rpow_eq_mul_logb_of_pos hd_pos]
    ring
  have hr : (r : ℝ) ≤ (A_dim / 2) * Real.logb 2 (1 / (d : ℝ) ^ (-θ)) + C_0 := by
    rw [hlog_sqrt] at hr_dim; linarith
  exact hexcl T r A_in A S w₀ p hobl hcorr hw₀ hp hAin hA hws hr

/-- Adaptive per-node bits at polynomial running time and linear workspaces: if `T ≤ C_T L^κ` and
`S_tot ≤ C_W L` (`L = d² entryBits d`), then
`γ_T + σ^{adap} ≤ (3 k_b A + S_tot) ⌈log₂(g + 1)⌉ + c b` with `c` depending only on `M`, `k_b`,
`C_T`, `κ` and `C_W`. -/
private theorem adaptiveNodeBits_le_of_polyTime (M : TM) (B_bank : Finset (Fin M.k))
    (C_T κ C_W : ℕ) {d T A : ℕ} {S : Fin M.k → ℕ} (hd1 : 1 ≤ d)
    (hT : T ≤ C_T * (d * d * entryBits d) ^ κ)
    (hws : workspaceCellSum B_bank S ≤ C_W * (d * d * entryBits d)) :
    structBitsAtTime M.k T + adapEntryBits M B_bank A S ≤
      (B_bank.card * 3 * A + workspaceCellSum B_bank S) * Nat.clog 2 (M.g + 1) +
        ((M.k + 4) * (Nat.clog 2 (2 * C_T + 1) + 3 * κ) + M.k * (Nat.clog 2 (C_W + 2) + 3) +
          (Nat.clog 2 (M.q + 1) + B_bank.card + B_bank.card * Nat.clog 2 (M.g + 1))) *
          entryBits d := by
  set b := entryBits d
  have hb1 : 1 ≤ b := by unfold b entryBits; omega
  set L := d * d * b
  have hL_pow : L ≤ 2 ^ (3 * b) := canonicalLen_le_two_pow_three_entryBits hd1
  set c_time := (M.k + 4) * (Nat.clog 2 (2 * C_T + 1) + 3 * κ)
  set c_ws := M.k * (Nat.clog 2 (C_W + 2) + 3)
  set c_base := Nat.clog 2 (M.q + 1) + B_bank.card + B_bank.card * Nat.clog 2 (M.g + 1)
  have hclog_T : structBitsAtTime M.k T ≤ c_time * b := by
    unfold structBitsAtTime
    have h2T : 2 * T + 1 ≤ 2 ^ ((Nat.clog 2 (2 * C_T + 1) + 3 * κ) * b) := by
      have h1 : 2 * T + 1 ≤ (2 * C_T + 1) * L ^ κ := by
        have hL_pos : 1 ≤ L ^ κ := Nat.one_le_pow κ L (by dsimp [L]; positivity)
        calc 2 * T + 1 ≤ 2 * (C_T * L ^ κ) + 1 := by omega
          _ ≤ 2 * C_T * L ^ κ + 1 * L ^ κ := by nlinarith
          _ = (2 * C_T + 1) * L ^ κ := by ring
      have h2 : (2 * C_T + 1) * L ^ κ ≤
          2 ^ Nat.clog 2 (2 * C_T + 1) * (2 ^ (3 * b)) ^ κ :=
        Nat.mul_le_mul (Nat.le_pow_clog (by norm_num) _) (Nat.pow_le_pow_left hL_pow κ)
      have h3 : Nat.clog 2 (2 * C_T + 1) + 3 * b * κ ≤
          (Nat.clog 2 (2 * C_T + 1) + 3 * κ) * b := by
        nlinarith [hb1]
      calc 2 * T + 1 ≤ 2 ^ Nat.clog 2 (2 * C_T + 1) * (2 ^ (3 * b)) ^ κ := h1.trans h2
        _ = 2 ^ (Nat.clog 2 (2 * C_T + 1) + 3 * b * κ) := by rw [← pow_mul, ← pow_add]
        _ ≤ 2 ^ ((Nat.clog 2 (2 * C_T + 1) + 3 * κ) * b) := Nat.pow_le_pow_right (by norm_num) h3
    have hcl : Nat.clog 2 (2 * T + 1) ≤ (Nat.clog 2 (2 * C_T + 1) + 3 * κ) * b :=
      (Nat.clog_le_iff_le_pow (by norm_num)).2 h2T
    calc (M.k + 4) * Nat.clog 2 (2 * T + 1)
        ≤ (M.k + 4) * ((Nat.clog 2 (2 * C_T + 1) + 3 * κ) * b) := Nat.mul_le_mul_left _ hcl
      _ = c_time * b := by dsimp [c_time]; ring
  have hclog_ws : ∑ t ∈ Finset.univ \ B_bank, Nat.clog 2 (S t + 1) ≤ c_ws * b := by
    have hper_t : ∀ t ∈ Finset.univ \ B_bank,
        Nat.clog 2 (S t + 1) ≤ (Nat.clog 2 (C_W + 2) + 3) * b := by
      intro t ht
      have hSt : S t ≤ workspaceCellSum B_bank S :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) ht
      have hL_ge1 : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (by dsimp [L]; positivity)
      have hSt1 : S t + 1 ≤ (C_W + 2) * L := by nlinarith
      have hpow : S t + 1 ≤ 2 ^ ((Nat.clog 2 (C_W + 2) + 3) * b) := by
        calc S t + 1 ≤ (C_W + 2) * L := hSt1
          _ ≤ 2 ^ Nat.clog 2 (C_W + 2) * 2 ^ (3 * b) :=
              Nat.mul_le_mul (Nat.le_pow_clog (by norm_num) _) hL_pow
          _ = 2 ^ (Nat.clog 2 (C_W + 2) + 3 * b) := by rw [← pow_add]
          _ ≤ 2 ^ ((Nat.clog 2 (C_W + 2) + 3) * b) :=
              Nat.pow_le_pow_right (by norm_num) (by nlinarith [hb1])
      exact (Nat.clog_le_iff_le_pow (by norm_num)).2 hpow
    calc ∑ t ∈ Finset.univ \ B_bank, Nat.clog 2 (S t + 1)
        ≤ ∑ _t ∈ Finset.univ \ B_bank, (Nat.clog 2 (C_W + 2) + 3) * b :=
          Finset.sum_le_sum hper_t
      _ = (Finset.univ \ B_bank).card * ((Nat.clog 2 (C_W + 2) + 3) * b) := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ M.k * ((Nat.clog 2 (C_W + 2) + 3) * b) :=
          Nat.mul_le_mul_right _ (by
            calc (Finset.univ \ B_bank).card ≤ (Finset.univ : Finset (Fin M.k)).card :=
                  Finset.card_le_card (Finset.sdiff_subset)
              _ = M.k := by simp)
      _ = c_ws * b := by dsimp [c_ws]; ring
  have hbase_le : c_base ≤ c_base * b := Nat.le_mul_of_pos_right c_base hb1
  have hmul : (c_time + c_ws + c_base) * b = c_time * b + c_ws * b + c_base * b := by ring
  have hexp : structBitsAtTime M.k T + adapEntryBits M B_bank A S =
      (B_bank.card * 3 * A + workspaceCellSum B_bank S) * Nat.clog 2 (M.g + 1) +
        structBitsAtTime M.k T + (∑ t ∈ Finset.univ \ B_bank, Nat.clog 2 (S t + 1)) + c_base := by
    dsimp [adapEntryBits, c_base]
    ring
  rw [hexp, hmul]
  linarith [hclog_T, hclog_ws, hbase_le]

/-- **Sub-Critical Phase-Profile Exclusion (Adaptive — Arbitrary Polynomial Running Time
`T ≤ C_T * L_d ^ κ` across all `θ ∈ (0, 2]`)**:
for any `M : TM`, bank subset `B_bank` with `k_b = B_bank.card ≥ 1`, exponent `θ ∈ (0, 2]`,
polynomial time constants `C_T, κ : ℕ`, and slope `A_slope` satisfying
`A_slope * log₂(k_b + 1) < 1 / 2`, for all sufficiently large `d`, `M` cannot adaptively transpose
all `d × d` matrices of `entryBits d`-bit entries within `T ≤ C_T * L_d ^ κ` steps while admitting
`r(w) ≤ A_slope * log₂(1 / d^{-θ}) + C_0` coarse-workspace passes on each input `w`. -/
theorem subcriticalPhaseProfile_adaptive_polyTime_excludes
    (M : TM) (B_bank : Finset (Fin M.k)) (hk : 1 ≤ B_bank.card)
    {θ A_slope C_0 C_in C_amp C_ws : ℝ} (C_T κ : ℕ)
    (hθ_pos : 0 < θ) (hθ_le : θ ≤ 2)
    (hslope : A_slope * Real.logb 2 ((B_bank.card : ℝ) + 1) < 1 / 2)
    (hCin : 0 ≤ C_in) (hCamp : 0 ≤ C_amp) (hCws : 0 ≤ C_ws) :
    ∀ᶠ d : ℕ in atTop,
      ∀ (T r A_in A : ℕ) (S : Fin M.k → ℕ),
        T ≤ C_T * (d * d * entryBits d) ^ κ →
        (∀ w ∈ matrixInputs d (entryBits d), ∃ T' ≤ T, ∃ r' ≤ r, ∃ p,
          CoarseWorkspacePartition M w T' r' B_bank A_in A S p ∧
          ∃ Mat : Matrix, w = encode d (entryBits d) Mat ∧
            (run M w T').outRev.reverse = encode d (entryBits d) (transpose Mat)) →
        (A_in : ℝ) ≤ C_in * (d : ℝ) ^ (-θ) * (d * d * entryBits d : ℝ) →
        (A : ℝ) ≤ C_amp * (d : ℝ) ^ (-θ) * (d * d * entryBits d : ℝ) →
        (workspaceCellSum B_bank S : ℝ) ≤ C_ws * (d : ℝ) ^ (-θ) * (d * d * entryBits d : ℝ) →
        (r : ℝ) ≤ A_slope * Real.logb 2 (1 / (d : ℝ) ^ (-θ)) + C_0 →
        False := by
  set β_g : ℝ := (Nat.clog 2 (M.g + 1) : ℝ)
  set C_coeff : ℝ := (3 * (B_bank.card : ℝ) * C_amp + C_ws) * β_g
  set c_time : ℕ := (M.k + 4) * (Nat.clog 2 (2 * C_T + 1) + 3 * κ)
  set c_ws : ℕ := M.k * (Nat.clog 2 (Nat.ceil C_ws + 2) + 3)
  set c_base : ℕ := Nat.clog 2 (M.q + 1) + B_bank.card + B_bank.card * Nat.clog 2 (M.g + 1)
  set C_log : ℝ := ((c_time + c_ws + c_base : ℕ) : ℝ)
  have hCcoeff : 0 ≤ C_coeff := by dsimp [C_coeff, β_g]; positivity
  have hClog : 0 ≤ C_log := by dsimp [C_log]; positivity
  filter_upwards [eventually_ge_atTop (2 : ℕ),
    subcritical_grouped_rhs_lt_eventually hk C_0 hθ_pos hθ_le hslope hCin hCcoeff hClog]
    with d hd2 ⟨γ, hγ, hbound⟩ T r A_in A S hT hrun hAin hA hws hr
  have hd1 : 1 ≤ d := by omega
  set b := entryBits d
  set L := d * d * b
  have hws_L : workspaceCellSum B_bank S ≤ Nat.ceil C_ws * L := by
    have hd_mθ_le1 : (d : ℝ) ^ (-θ) ≤ 1 := by
      calc (d : ℝ) ^ (-θ) ≤ (d : ℝ) ^ (0 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hd1) (by linarith)
        _ = 1 := Real.rpow_zero _
    have hL_cast : (d : ℝ) * (d : ℝ) * (b : ℝ) = (L : ℝ) := by dsimp [L]; push_cast; ring
    have hws' : (workspaceCellSum B_bank S : ℝ) ≤ C_ws * (d : ℝ) ^ (-θ) * (L : ℝ) := by
      rwa [← hL_cast]
    have hr1 : (workspaceCellSum B_bank S : ℝ) ≤ (Nat.ceil C_ws : ℝ) * (L : ℝ) := by
      calc (workspaceCellSum B_bank S : ℝ)
          ≤ C_ws * (d : ℝ) ^ (-θ) * (L : ℝ) := hws'
        _ ≤ C_ws * 1 * (L : ℝ) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hd_mθ_le1 hCws) (by positivity)
        _ = C_ws * (L : ℝ) := by ring
        _ ≤ (Nat.ceil C_ws : ℝ) * (L : ℝ) :=
            mul_le_mul_of_nonneg_right (Nat.le_ceil C_ws) (by positivity)
    exact_mod_cast hr1
  set σ_tot := structBitsAtTime M.k T + adapEntryBits M B_bank A S
  have hσ : (σ_tot : ℝ) ≤
      C_coeff * (d : ℝ) ^ (-θ) * (d * d * entryBits d : ℝ) + C_log * (entryBits d : ℝ) := by
    have hnat : σ_tot ≤
        (B_bank.card * 3 * A + workspaceCellSum B_bank S) * Nat.clog 2 (M.g + 1) +
          (c_time + c_ws + c_base) * b :=
      adaptiveNodeBits_le_of_polyTime M B_bank C_T κ (Nat.ceil C_ws) hd1 hT hws_L
    have hreal_nat : (σ_tot : ℝ) ≤
        (3 * (B_bank.card : ℝ) * (A : ℝ) + (workspaceCellSum B_bank S : ℝ)) * β_g +
          C_log * (b : ℝ) := by
      have hcast : (((B_bank.card * 3 * A + workspaceCellSum B_bank S) * Nat.clog 2 (M.g + 1) +
          (c_time + c_ws + c_base) * b : ℕ) : ℝ) =
          (3 * (B_bank.card : ℝ) * (A : ℝ) + (workspaceCellSum B_bank S : ℝ)) * β_g +
            C_log * (b : ℝ) := by
        dsimp [β_g, C_log]
        push_cast
        ring
      exact (Nat.cast_le.2 hnat).trans_eq hcast
    have h1 : (3 * (B_bank.card : ℝ) * (A : ℝ) + (workspaceCellSum B_bank S : ℝ)) * β_g ≤
        C_coeff * (d : ℝ) ^ (-θ) * (d * d * entryBits d : ℝ) := by
      dsimp [C_coeff]
      have hsum : 3 * (B_bank.card : ℝ) * (A : ℝ) + (workspaceCellSum B_bank S : ℝ) ≤
          (3 * (B_bank.card : ℝ) * C_amp + C_ws) * (d : ℝ) ^ (-θ) *
            (d * d * entryBits d : ℝ) := by
        nlinarith [hA, hws]
      have hβg : 0 ≤ β_g := Nat.cast_nonneg _
      have := mul_le_mul_of_nonneg_right hsum hβg
      linarith
    linarith
  have hco : 2 ^ (d * d * entryBits d) ≤ 2 ^ 0 * (matrixInputs d (entryBits d)).ncard := by
    rw [ncard_matrixInputs, pow_zero, one_mul]
  have hlt := hbound r A_in σ_tot hr hAin hσ
  exact adaptive_singleScale_coarseWorkspace_excludes (m := 0) hrun hγ hco
    (by simpa [σ_tot] using hlt)

/-! ### Boundedly Many Coarse Passes with Amplitudes and Workspaces `≤ ε L` -/

/-- Bounded-pass engine: for fixed `k_b`, `r₀` and `C_coeff ≥ 0` there is `ε ∈ (0, 1]` such that,
for every `C_log ≥ 0` and all large `d`, the group width `γ_d = ⌊d / N⌋ + 1` with
`N = 4 (H(k_b, r₀) + 1)` (so `γ_d ≍ √(σ / b)` when `σ ≍ C_coeff ε L`) makes the grouped pass RHS
smaller than `d² b` for every `b ≥ 1`, `r ≤ r₀`, `A_in ≤ ε d² b` and
`σ_tot ≤ C_coeff ε d² b + C_log b`. -/
private theorem boundedPass_grouped_rhs_lt_eventually (k_b r₀ : ℕ) {C_coeff : ℝ}
    (hC : 0 ≤ C_coeff) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∀ C_log : ℝ, 0 ≤ C_log →
      ∀ᶠ d : ℕ in atTop, ∃ γ : ℕ, 1 ≤ γ ∧
        ∀ (b r A_in σ_tot : ℕ), 1 ≤ b → r ≤ r₀ →
          (A_in : ℝ) ≤ ε * (d * d * b : ℝ) →
          (σ_tot : ℝ) ≤ C_coeff * ε * (d * d * b : ℝ) + C_log * (b : ℝ) →
          addrCount k_b r * ((γ + 1) * d * b + 2 * A_in + numGroups d γ * σ_tot) <
            d * d * b := by
  set H₀ := addrCount k_b r₀
  set N : ℕ := 4 * (H₀ + 1) with hN
  have hN_pos : 0 < N := by omega
  have hNr : (N : ℝ) = 4 * ((H₀ : ℝ) + 1) := by rw [hN]; push_cast; ring
  have hH₀ : (0 : ℝ) ≤ (H₀ : ℝ) := Nat.cast_nonneg _
  have hden : (0 : ℝ) < (N : ℝ) * (2 + (N : ℝ) * C_coeff) := by positivity
  refine ⟨1 / ((N : ℝ) * (2 + (N : ℝ) * C_coeff)), by positivity, ?_, ?_⟩
  · rw [div_le_one hden]
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) N) hC]
  intro C_log hClog
  filter_upwards [eventually_gt_atTop (4 * H₀ + 2 * H₀ * N * ⌈C_log⌉₊)] with d hd
  refine ⟨d / N + 1, le_add_self, fun b r A_in σ_tot hb hr hA hσ => ?_⟩
  set ε : ℝ := 1 / ((N : ℝ) * (2 + (N : ℝ) * C_coeff))
  have hε : 0 < ε := by positivity
  have hH : addrCount k_b r ≤ H₀ := Finset.sum_le_sum_of_subset (Finset.range_mono hr)
  have hG : numGroups d (d / N + 1) ≤ N := by
    unfold numGroups
    generalize hq : d / N = q
    have hlt : d < N * (q + 1) := hq ▸ Nat.lt_mul_div_succ d hN_pos
    have h2 : d + (q + 1) - 1 < (N + 1) * (q + 1) := by rw [add_one_mul]; omega
    have h3 := (Nat.div_lt_iff_lt_mul (by omega : 0 < q + 1)).2 h2
    omega
  have hx1 : (1 : ℝ) ≤ (d : ℝ) := by
    have : 1 ≤ d := by omega
    exact_mod_cast this
  have hy1 : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hdx : ((4 * H₀ + 2 * H₀ * N * ⌈C_log⌉₊ : ℕ) : ℝ) + 1 ≤ (d : ℝ) := by
    have hd' : 4 * H₀ + 2 * H₀ * N * ⌈C_log⌉₊ + 1 ≤ d := hd
    exact_mod_cast hd'
  push_cast at hdx
  have hγr : (((d / N : ℕ) : ℝ) + 1) + 1 ≤ (d : ℝ) / (N : ℝ) + 2 := by
    have : ((d / N : ℕ) : ℝ) ≤ (d : ℝ) / (N : ℝ) := Nat.cast_div_le
    linarith
  set x : ℝ := (d : ℝ)
  set y : ℝ := (b : ℝ)
  have hGr : (numGroups d (d / N + 1) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hG
  have hHr : (addrCount k_b r : ℝ) ≤ (H₀ : ℝ) := by exact_mod_cast hH
  have hεN : ε * (2 + (N : ℝ) * C_coeff) = 1 / (N : ℝ) := by
    dsimp only [ε]; field_simp
  have hHN : (H₀ : ℝ) * (2 / (N : ℝ)) ≤ 1 / 2 := by
    rw [hNr, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hd_large : 2 * (H₀ : ℝ) * (2 * x + (N : ℝ) * C_log) < x * x := by
    have e1 := mul_le_mul_of_nonneg_left hdx (by positivity : (0 : ℝ) ≤ x)
    have e2 : 2 * (H₀ : ℝ) * (N : ℝ) * C_log ≤ 2 * (H₀ : ℝ) * (N : ℝ) * ((⌈C_log⌉₊ : ℝ) * x) :=
      mul_le_mul_of_nonneg_left ((Nat.le_ceil C_log).trans
        (le_mul_of_one_le_right (Nat.cast_nonneg _) hx1)) (by positivity)
    nlinarith
  have hinner : ((((d / N + 1) + 1) * d * b + 2 * A_in +
      numGroups d (d / N + 1) * σ_tot : ℕ) : ℝ) ≤
        x * x * y * (2 / (N : ℝ)) + y * (2 * x + (N : ℝ) * C_log) := by
    push_cast
    have h1 : (((d / N : ℕ) : ℝ) + 1 + 1) * x * y ≤ (x / (N : ℝ) + 2) * x * y :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hγr (by positivity)) (by positivity)
    have h2 : (numGroups d (d / N + 1) : ℝ) * (σ_tot : ℝ) ≤
        (N : ℝ) * (C_coeff * ε * (x * x * y) + C_log * y) :=
      mul_le_mul hGr hσ (Nat.cast_nonneg _) (by positivity)
    calc (((d / N : ℕ) : ℝ) + 1 + 1) * x * y + 2 * (A_in : ℝ) +
          (numGroups d (d / N + 1) : ℝ) * (σ_tot : ℝ)
        ≤ (x / (N : ℝ) + 2) * x * y + 2 * (ε * (x * x * y)) +
            (N : ℝ) * (C_coeff * ε * (x * x * y) + C_log * y) := by linarith
      _ = x * x * y * (1 / (N : ℝ) + ε * (2 + (N : ℝ) * C_coeff)) +
            y * (2 * x + (N : ℝ) * C_log) := by ring
      _ = x * x * y * (2 / (N : ℝ)) + y * (2 * x + (N : ℝ) * C_log) := by rw [hεN]; ring
  have key : ((addrCount k_b r * (((d / N + 1) + 1) * d * b + 2 * A_in +
      numGroups d (d / N + 1) * σ_tot) : ℕ) : ℝ) < ((d * d * b : ℕ) : ℝ) := by
    rw [Nat.cast_mul (addrCount k_b r)]
    calc (addrCount k_b r : ℝ) * ((((d / N + 1) + 1) * d * b + 2 * A_in +
          numGroups d (d / N + 1) * σ_tot : ℕ) : ℝ)
        ≤ (H₀ : ℝ) * (x * x * y * (2 / (N : ℝ)) + y * (2 * x + (N : ℝ) * C_log)) :=
          mul_le_mul hHr hinner (Nat.cast_nonneg _) hH₀
      _ = x * x * y * ((H₀ : ℝ) * (2 / (N : ℝ))) + y * ((H₀ : ℝ) * (2 * x + (N : ℝ) * C_log)) := by
          ring
      _ < x * x * y * (1 / 2) + y * (x * x / 2) := by
          have e1 := mul_le_mul_of_nonneg_left hHN (by positivity : (0 : ℝ) ≤ x * x * y)
          have e2 : y * ((H₀ : ℝ) * (2 * x + (N : ℝ) * C_log)) < y * (x * x / 2) :=
            mul_lt_mul_of_pos_left (by linarith) (by positivity)
          linarith
      _ = ((d * d * b : ℕ) : ℝ) := by push_cast; ring
  exact_mod_cast key

/-- **Boundedly Many Coarse Passes Are Excluded (Oblivious — Arbitrary Running Time)**: for any
`M : TM`, bank `B_bank` and pass bound `r₀`, there is `ε > 0` such that for all sufficiently large
`d` and **every** halting time `T`, `M` is not an oblivious transposer of the `d × d` matrices of
`entryBits d`-bit entries whose run has a `CoarseWorkspacePartition` with at most `r₀` passes,
amplitudes `A_in, A ≤ ε L` and workspaces `S_tot ≤ ε L` (`L = d² entryBits d`). The proof takes
`ε` depending only on `k_b`, `r₀` and the work alphabet of `M`. -/
theorem boundedCoarsePasses_oblivious_excludes (M : TM) (B_bank : Finset (Fin M.k)) (r₀ : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ d : ℕ in atTop,
      ∀ (T r A_in A : ℕ) (S : Fin M.k → ℕ) (w₀ : List Bool) (p : ℕ → ℕ),
        ObliviousOn M (matrixInputs d (entryBits d)) T →
        ClassCorrect M d (entryBits d) T (matrixInputs d (entryBits d)) →
        w₀ ∈ matrixInputs d (entryBits d) →
        CoarseWorkspacePartition M w₀ T r B_bank A_in A S p → r ≤ r₀ →
        (A_in : ℝ) ≤ ε * (d * d * entryBits d : ℝ) →
        (A : ℝ) ≤ ε * (d * d * entryBits d : ℝ) →
        (workspaceCellSum B_bank S : ℝ) ≤ ε * (d * d * entryBits d : ℝ) →
        False := by
  obtain ⟨ε, hε, -, heng⟩ := boundedPass_grouped_rhs_lt_eventually B_bank.card r₀
    (C_coeff := (3 * (B_bank.card : ℝ) + 1) * (Nat.clog 2 (M.g + 1) : ℝ)) (by positivity)
  refine ⟨ε, hε, ?_⟩
  filter_upwards [heng ((Nat.clog 2 (M.q + 1) + B_bank.card * Nat.clog 2 (M.g + 1) : ℕ) : ℝ)
    (Nat.cast_nonneg _)] with d ⟨γ, hγ, hbound⟩ T r A_in A S w₀ p hobl hcorr hw₀ hp hr hAin hA hws
  have hb1 : 1 ≤ entryBits d := by unfold entryBits; omega
  have hσ : (oblEntryBits M B_bank A S : ℝ) ≤
      (3 * (B_bank.card : ℝ) + 1) * (Nat.clog 2 (M.g + 1) : ℝ) * ε * (d * d * entryBits d : ℝ) +
        ((Nat.clog 2 (M.q + 1) + B_bank.card * Nat.clog 2 (M.g + 1) : ℕ) : ℝ) *
          (entryBits d : ℝ) := by
    have hsum : 3 * (B_bank.card : ℝ) * (A : ℝ) + (workspaceCellSum B_bank S : ℝ) ≤
        (3 * (B_bank.card : ℝ) + 1) * (ε * (d * d * entryBits d : ℝ)) := by
      nlinarith [mul_le_mul_of_nonneg_left hA (by positivity : (0 : ℝ) ≤ 3 * (B_bank.card : ℝ))]
    have h1 := mul_le_mul_of_nonneg_right hsum (Nat.cast_nonneg (α := ℝ) (Nat.clog 2 (M.g + 1)))
    have h2 := le_mul_of_one_le_right
      (Nat.cast_nonneg (α := ℝ) (Nat.clog 2 (M.q + 1) + B_bank.card * Nat.clog 2 (M.g + 1)))
      (show (1 : ℝ) ≤ (entryBits d : ℝ) by exact_mod_cast hb1)
    unfold oblEntryBits
    push_cast at h2 ⊢
    nlinarith
  have hco : 2 ^ (d * d * entryBits d) ≤ 2 ^ 0 * (matrixInputs d (entryBits d)).ncard := by
    rw [ncard_matrixInputs, pow_zero, one_mul]
  exact oblivious_singleScale_coarseWorkspace_excludes (m := 0) hobl hcorr hw₀ hp hγ hco
    (by simpa using hbound (entryBits d) r A_in _ hb1 hr hAin hσ)

/-- **Boundedly Many Coarse Passes Are Excluded (Adaptive — Arbitrary Polynomial Running Time)**:
for any `M : TM`, bank `B_bank` and pass bound `r₀`, there is `ε > 0` such that for all time
constants `C_T, κ : ℕ` and all sufficiently large `d`, `M` does not transpose every `d × d`
matrix of `entryBits d`-bit entries within `T ≤ C_T L^κ` steps if the run on each input `w` has,
up to a step `T' ≤ T` at which its output is the transpose, a `CoarseWorkspacePartition` with at
most `r₀` passes, amplitudes `A_in, A ≤ ε L` and workspaces `S_tot ≤ ε L` (`L = d² entryBits d`);
the passes may depend on `w`. The same `ε` serves every `C_T` and `κ`. -/
theorem boundedCoarsePasses_adaptive_polyTime_excludes (M : TM) (B_bank : Finset (Fin M.k))
    (r₀ : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ C_T κ : ℕ, ∀ᶠ d : ℕ in atTop,
      ∀ (T A_in A : ℕ) (S : Fin M.k → ℕ),
        T ≤ C_T * (d * d * entryBits d) ^ κ →
        (∀ w ∈ matrixInputs d (entryBits d), ∃ T' ≤ T, ∃ r ≤ r₀, ∃ p,
          CoarseWorkspacePartition M w T' r B_bank A_in A S p ∧
          ∃ Mat : Matrix, w = encode d (entryBits d) Mat ∧
            (run M w T').outRev.reverse = encode d (entryBits d) (transpose Mat)) →
        (A_in : ℝ) ≤ ε * (d * d * entryBits d : ℝ) →
        (A : ℝ) ≤ ε * (d * d * entryBits d : ℝ) →
        (workspaceCellSum B_bank S : ℝ) ≤ ε * (d * d * entryBits d : ℝ) →
        False := by
  obtain ⟨ε, hε, hε1, heng⟩ := boundedPass_grouped_rhs_lt_eventually B_bank.card r₀
    (C_coeff := (3 * (B_bank.card : ℝ) + 1) * (Nat.clog 2 (M.g + 1) : ℝ)) (by positivity)
  refine ⟨ε, hε, fun C_T κ => ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ), heng
    (((M.k + 4) * (Nat.clog 2 (2 * C_T + 1) + 3 * κ) + M.k * (Nat.clog 2 (1 + 2) + 3) +
      (Nat.clog 2 (M.q + 1) + B_bank.card + B_bank.card * Nat.clog 2 (M.g + 1)) : ℕ) : ℝ)
    (Nat.cast_nonneg _)] with d hd1 ⟨γ, hγ, hbound⟩ T A_in A S hT hrun hAin hA hws
  have hb1 : 1 ≤ entryBits d := by unfold entryBits; omega
  have hL0 : (0 : ℝ) ≤ (d * d * entryBits d : ℝ) := by positivity
  have hws_L : workspaceCellSum B_bank S ≤ 1 * (d * d * entryBits d) := by
    have : (workspaceCellSum B_bank S : ℝ) ≤ (d * d * entryBits d : ℝ) := by nlinarith
    rw [one_mul]; exact_mod_cast this
  have hnat := adaptiveNodeBits_le_of_polyTime M B_bank C_T κ 1 (A := A) hd1 hT hws_L
  have hσ : ((structBitsAtTime M.k T + adapEntryBits M B_bank A S : ℕ) : ℝ) ≤
      (3 * (B_bank.card : ℝ) + 1) * (Nat.clog 2 (M.g + 1) : ℝ) * ε * (d * d * entryBits d : ℝ) +
        (((M.k + 4) * (Nat.clog 2 (2 * C_T + 1) + 3 * κ) + M.k * (Nat.clog 2 (1 + 2) + 3) +
          (Nat.clog 2 (M.q + 1) + B_bank.card + B_bank.card * Nat.clog 2 (M.g + 1)) : ℕ) : ℝ) *
          (entryBits d : ℝ) := by
    have hsum : 3 * (B_bank.card : ℝ) * (A : ℝ) + (workspaceCellSum B_bank S : ℝ) ≤
        (3 * (B_bank.card : ℝ) + 1) * (ε * (d * d * entryBits d : ℝ)) := by
      nlinarith [mul_le_mul_of_nonneg_left hA (by positivity : (0 : ℝ) ≤ 3 * (B_bank.card : ℝ))]
    have h1 := mul_le_mul_of_nonneg_right hsum (Nat.cast_nonneg (α := ℝ) (Nat.clog 2 (M.g + 1)))
    have h0 := (Nat.cast_le (α := ℝ)).2 hnat
    push_cast at h0 h1 ⊢
    nlinarith
  have hco : 2 ^ (d * d * entryBits d) ≤ 2 ^ 0 * (matrixInputs d (entryBits d)).ncard := by
    rw [ncard_matrixInputs, pow_zero, one_mul]
  exact adaptive_singleScale_coarseWorkspace_excludes (r := r₀) (m := 0) hrun hγ hco
    (by simpa using hbound (entryBits d) r₀ A_in _ hb1 le_rfl hAin hσ)

/-- **Boundedly Many Coarse Passes with `o(L)` Amplitudes and Workspaces (Oblivious)**: for any
`M : TM`, bank `B_bank`, pass bound `r₀` and `ω(d) = o(L_d)` (`L_d = d² entryBits d`), for all
sufficiently large `d` and **every** halting time `T`, `M` is not an oblivious transposer at size
`d` whose run has a `CoarseWorkspacePartition` with at most `r₀` passes, `A_in, A ≤ ω(d)` and
`S_tot ≤ ω(d)`. -/
theorem boundedCoarsePasses_sublinear_oblivious_excludes (M : TM) (B_bank : Finset (Fin M.k))
    (r₀ : ℕ) {ω : ℕ → ℝ}
    (hω : Asymptotics.IsLittleO atTop ω fun d : ℕ => (d * d * entryBits d : ℝ)) :
    ∀ᶠ d : ℕ in atTop,
      ∀ (T r A_in A : ℕ) (S : Fin M.k → ℕ) (w₀ : List Bool) (p : ℕ → ℕ),
        ObliviousOn M (matrixInputs d (entryBits d)) T →
        ClassCorrect M d (entryBits d) T (matrixInputs d (entryBits d)) →
        w₀ ∈ matrixInputs d (entryBits d) →
        CoarseWorkspacePartition M w₀ T r B_bank A_in A S p → r ≤ r₀ →
        (A_in : ℝ) ≤ ω d → (A : ℝ) ≤ ω d → (workspaceCellSum B_bank S : ℝ) ≤ ω d →
        False := by
  obtain ⟨ε, hε, hev⟩ := boundedCoarsePasses_oblivious_excludes M B_bank r₀
  filter_upwards [hev, hω.def hε]
    with d hexcl hωd T r A_in A S w₀ p hobl hcorr hw₀ hp hr hAin hA hws
  have hle : ω d ≤ ε * (d * d * entryBits d : ℝ) := by
    rw [Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (d * d * entryBits d : ℝ))] at hωd
    exact (le_abs_self _).trans hωd
  exact hexcl T r A_in A S w₀ p hobl hcorr hw₀ hp hr (hAin.trans hle) (hA.trans hle)
    (hws.trans hle)

/-- **Boundedly Many Coarse Passes with `o(L)` Amplitudes and Workspaces (Adaptive — Polynomial
Running Time)**: for any `M : TM`, bank `B_bank`, pass bound `r₀`, time constants `C_T, κ : ℕ` and
`ω(d) = o(L_d)`, for all sufficiently large `d`, `M` does not transpose every input at size `d`
within `T ≤ C_T L^κ` steps if the run on each input has, up to a step at which its output is the
transpose, a `CoarseWorkspacePartition` with at most `r₀` passes, `A_in, A ≤ ω(d)` and
`S_tot ≤ ω(d)`. -/
theorem boundedCoarsePasses_sublinear_adaptive_polyTime_excludes (M : TM)
    (B_bank : Finset (Fin M.k)) (r₀ C_T κ : ℕ) {ω : ℕ → ℝ}
    (hω : Asymptotics.IsLittleO atTop ω fun d : ℕ => (d * d * entryBits d : ℝ)) :
    ∀ᶠ d : ℕ in atTop,
      ∀ (T A_in A : ℕ) (S : Fin M.k → ℕ),
        T ≤ C_T * (d * d * entryBits d) ^ κ →
        (∀ w ∈ matrixInputs d (entryBits d), ∃ T' ≤ T, ∃ r ≤ r₀, ∃ p,
          CoarseWorkspacePartition M w T' r B_bank A_in A S p ∧
          ∃ Mat : Matrix, w = encode d (entryBits d) Mat ∧
            (run M w T').outRev.reverse = encode d (entryBits d) (transpose Mat)) →
        (A_in : ℝ) ≤ ω d → (A : ℝ) ≤ ω d → (workspaceCellSum B_bank S : ℝ) ≤ ω d →
        False := by
  obtain ⟨ε, hε, hev⟩ := boundedCoarsePasses_adaptive_polyTime_excludes M B_bank r₀
  filter_upwards [hev C_T κ, hω.def hε] with d hexcl hωd T A_in A S hT hrun hAin hA hws
  have hle : ω d ≤ ε * (d * d * entryBits d : ℝ) := by
    rw [Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (d * d * entryBits d : ℝ))] at hωd
    exact (le_abs_self _).trans hωd
  exact hexcl T A_in A S hT hrun (hAin.trans hle) (hA.trans hle) (hws.trans hle)

/-! ### `θ = 2` Uniform-in-`k_b` Sharpness via `f`-Way Perfect Unshuffle -/

/-- One round of `f`-way perfect unshuffle on `[0, f^N)`: sends `x` to `(x % f) * f^(N - 1) + x / f`
(rotating the least-significant base-`f` digit to the most-significant position). -/
def unshuffleStep (f N x : ℕ) : ℕ :=
  (x % f) * f ^ (N - 1) + x / f

private theorem unshuffleStep_iter_split {f : ℕ} (hf : 1 ≤ f) :
    ∀ (m k hi lo : ℕ), hi < f ^ k → lo < f ^ m →
      (unshuffleStep f (k + m))^[m] (hi * f ^ m + lo) = lo * f ^ k + hi
  | 0, k, hi, lo, _, hlo => by
    have : lo = 0 := by simp at hlo; omega
    subst this
    simp
  | m + 1, k, hi, lo, hhi, hlo => by
    set q := lo / f
    set rem := lo % f
    have hrem : rem < f := Nat.mod_lt lo hf
    have hlo_eq : lo = q * f + rem := by
      have := Nat.div_add_mod lo f
      dsimp [q, rem]
      linarith
    have hq : q < f ^ m := by
      apply Nat.div_lt_of_lt_mul
      simpa [pow_succ, Nat.mul_comm] using hlo
    have hx_eq : hi * f ^ (m + 1) + lo = rem + f * (hi * f ^ m + q) := by
      rw [pow_succ, hlo_eq]; ring
    have hstep : unshuffleStep f (k + (m + 1)) (hi * f ^ (m + 1) + lo) =
        (rem * f ^ k + hi) * f ^ m + q := by
      unfold unshuffleStep
      have hN : k + (m + 1) - 1 = k + m := by omega
      have hmod : (hi * f ^ (m + 1) + lo) % f = rem := by
        rw [hx_eq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrem]
      have hdiv : (hi * f ^ (m + 1) + lo) / f = hi * f ^ m + q := by
        rw [hx_eq, Nat.add_mul_div_left _ _ hf, Nat.div_eq_of_lt hrem, Nat.zero_add]
      rw [hN, hmod, hdiv, pow_add]
      ring
    have hhi' : rem * f ^ k + hi < f ^ (k + 1) := by
      have hrem1 : rem + 1 ≤ f := hrem
      calc rem * f ^ k + hi
          < rem * f ^ k + f ^ k := Nat.add_lt_add_left hhi _
        _ = (rem + 1) * f ^ k := by ring
        _ ≤ f * f ^ k := Nat.mul_le_mul_right _ hrem1
        _ = f ^ (k + 1) := by rw [pow_succ, Nat.mul_comm]
    rw [Function.iterate_succ_apply, hstep,
      show k + (m + 1) = (k + 1) + m by omega,
      unshuffleStep_iter_split hf m (k + 1) (rem * f ^ k + hi) q hhi' hq]
    rw [pow_succ, hlo_eq]
    ring

/-- **`f`-Way Perfect-Unshuffle Transposition Identity**: `P` rounds of `f`-way perfect unshuffle on
`f^(2P)` entries map every row-major index `i * f^P + j` (`i, j < f^P`) to its transpose index
`j * f^P + i`. -/
theorem unshuffleStep_iter_transpose {f P i j : ℕ} (hf : 1 ≤ f) (hi : i < f ^ P) (hj : j < f ^ P) :
    (unshuffleStep f (2 * P))^[P] (i * f ^ P + j) = j * f ^ P + i := by
  simpa [two_mul] using unshuffleStep_iter_split hf P P i j hi hj

/-- Slope-product `A_slope * log₂(k_b + 1) = log₂(2f + 1) / (2 log₂ f)` of the `f`-way
perfect-unshuffle transposer (`k_b = 2f`, `A_slope = 1 / (2 log₂ f)`) at `θ = 2`. -/
noncomputable def perfectUnshuffleSlopeProduct (f : ℕ) : ℝ :=
  Real.logb 2 (2 * (f : ℝ) + 1) / (2 * Real.logb 2 (f : ℝ))

theorem perfectUnshuffleSlopeProduct_gt_half {f : ℕ} (hf : 2 ≤ f) :
    1 / 2 < perfectUnshuffleSlopeProduct f := by
  unfold perfectUnshuffleSlopeProduct
  have hf_real : (2 : ℝ) ≤ (f : ℝ) := by exact_mod_cast hf
  have hlog_pos : 0 < Real.logb 2 (f : ℝ) := Real.logb_pos (by norm_num) (by linarith)
  have hlog_lt : Real.logb 2 (f : ℝ) < Real.logb 2 (2 * (f : ℝ) + 1) :=
    Real.logb_lt_logb (by norm_num) (by linarith) (by linarith)
  rw [lt_div_iff₀ (by linarith)]
  linarith

/-- As `f → ∞`, `perfectUnshuffleSlopeProduct f = log₂(2f + 1) / (2 log₂ f) → 1 / 2`. -/
theorem perfectUnshuffleSlopeProduct_tendsto_half :
    Tendsto perfectUnshuffleSlopeProduct atTop (nhds (1 / 2)) := by
  have hupper : ∀ f : ℕ, 2 ≤ f →
      perfectUnshuffleSlopeProduct f ≤ 1 / 2 + Real.logb 2 3 / (2 * Real.logb 2 (f : ℝ)) := by
    intro f hf
    unfold perfectUnshuffleSlopeProduct
    have hf_real : (2 : ℝ) ≤ (f : ℝ) := by exact_mod_cast hf
    have hlog_pos : 0 < Real.logb 2 (f : ℝ) := Real.logb_pos (by norm_num) (by linarith)
    have h2f1_le : 2 * (f : ℝ) + 1 ≤ 3 * (f : ℝ) := by linarith
    have hlog_le : Real.logb 2 (2 * (f : ℝ) + 1) ≤ Real.logb 2 3 + Real.logb 2 (f : ℝ) := by
      calc Real.logb 2 (2 * (f : ℝ) + 1)
          ≤ Real.logb 2 (3 * (f : ℝ)) :=
            Real.logb_le_logb_of_le (by norm_num) (by linarith) h2f1_le
        _ = Real.logb 2 3 + Real.logb 2 (f : ℝ) :=
            Real.logb_mul (by norm_num) (by linarith)
    calc Real.logb 2 (2 * (f : ℝ) + 1) / (2 * Real.logb 2 (f : ℝ))
        ≤ (Real.logb 2 3 + Real.logb 2 (f : ℝ)) / (2 * Real.logb 2 (f : ℝ)) :=
          div_le_div_of_nonneg_right hlog_le (by linarith)
      _ = 1 / 2 + Real.logb 2 3 / (2 * Real.logb 2 (f : ℝ)) := by
          rw [add_div, add_comm]
          congr 1
          field_simp [ne_of_gt hlog_pos]
  have htend_log : Tendsto (fun f : ℕ => 2 * Real.logb 2 (f : ℝ)) atTop atTop := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h1 : Tendsto (fun f : ℕ => Real.log (f : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun f : ℕ => (2 / Real.log 2) * Real.log (f : ℝ)) atTop atTop :=
      Tendsto.const_mul_atTop (by positivity) h1
    refine h2.congr (fun f => ?_)
    unfold Real.logb
    ring
  have htend_rhs :
      Tendsto (fun f : ℕ => 1 / 2 + Real.logb 2 3 / (2 * Real.logb 2 (f : ℝ)))
        atTop (nhds (1 / 2)) := by
    have h0 : Tendsto (fun f : ℕ => Real.logb 2 3 * (2 * Real.logb 2 (f : ℝ))⁻¹)
        atTop (nhds (Real.logb 2 3 * 0)) :=
      (tendsto_inv_atTop_zero.comp htend_log).const_mul (Real.logb 2 3)
    simpa [div_eq_mul_inv] using h0.const_add (1 / 2 : ℝ)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htend_rhs ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with f hf
    exact le_of_lt (perfectUnshuffleSlopeProduct_gt_half hf)
  · filter_upwards [eventually_ge_atTop 2] with f hf
    exact hupper f hf

/-- **Uniform-in-`k_b` Sharpness of `1 / 2` at `θ = 2`**: for every `c > 1 / 2`, there exists `f ≥ 2`
with `perfectUnshuffleSlopeProduct f = log₂(2f + 1) / (2 log₂ f) < c`. -/
theorem exists_perfectUnshuffleSlopeProduct_lt_of_gt_half {c : ℝ} (hc : 1 / 2 < c) :
    ∃ f : ℕ, 2 ≤ f ∧ perfectUnshuffleSlopeProduct f < c := by
  have hev := (tendsto_order.1 perfectUnshuffleSlopeProduct_tendsto_half).2 c hc
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  exact ⟨max N 2, le_max_right N 2, hN (max N 2) (le_max_left N 2)⟩

/-- **Algebraic Non-Exclusion Above `1 / 2` Uniform in `k_b` at `θ = 2`**: for every `c > 1 / 2`,
there exist `f ≥ 2` (`k_b = 2f`, `A_slope = 1 / (2 log₂ f)`) with
`A_slope * log₂(k_b + 1) < c` such that along all `d = f ^ P` (`P ≥ 1`) with `r = P + 1` passes
satisfying `r = A_slope * log₂(1 / d^{-2}) + 1`, the oblivious grouped pass inequality holds for
**every** group width `γ ≥ 1` (so no choice of `γ` can push the single-scale ceiling at `θ = 2`
above `1 / 2` uniformly in `k_b`). -/
theorem groupedBound_thetaTwo_not_excluded_above_half {c : ℝ} (hc : 1 / 2 < c) :
    ∃ (f : ℕ), 2 ≤ f ∧
      let k_b := 2 * f
      let A_slope := 1 / (2 * Real.logb 2 (f : ℝ))
      A_slope * Real.logb 2 ((k_b : ℝ) + 1) < c ∧
        ∀ P : ℕ, 1 ≤ P →
          let d := f ^ P
          let r := P + 1
          (r : ℝ) = A_slope * Real.logb 2 (1 / (d : ℝ) ^ (-2 : ℝ)) + 1 ∧
            ∀ (M : TM) (B_bank : Finset (Fin M.k)), B_bank.card = k_b →
              ∀ (b γ A_in A : ℕ) (S : Fin M.k → ℕ), 1 ≤ γ →
                d * d * b ≤ addrCount B_bank.card r *
                  ((γ + 1) * d * b + 2 * A_in + numGroups d γ * oblEntryBits M B_bank A S) := by
  obtain ⟨f, hf, hlt⟩ := exists_perfectUnshuffleSlopeProduct_lt_of_gt_half hc
  refine ⟨f, hf, ?_, ?_⟩
  · unfold perfectUnshuffleSlopeProduct at hlt
    have hcast : ((2 * f : ℕ) : ℝ) + 1 = 2 * (f : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    linarith [show (1 / (2 * Real.logb 2 (f : ℝ))) * Real.logb 2 (2 * (f : ℝ) + 1) =
      Real.logb 2 (2 * (f : ℝ) + 1) / (2 * Real.logb 2 (f : ℝ)) by ring]
  · intro P _hP
    have hf_real : (2 : ℝ) ≤ (f : ℝ) := by exact_mod_cast hf
    have hlog_pos : 0 < Real.logb 2 (f : ℝ) := Real.logb_pos (by norm_num) (by linarith)
    refine ⟨?_, ?_⟩
    · have hd_pos : (0 : ℝ) < ((f ^ P : ℕ) : ℝ) := by positivity
      have hinv : 1 / (((f ^ P : ℕ) : ℝ) ^ (-2 : ℝ)) = (f : ℝ) ^ (2 * P) := by
        rw [one_div, ← Real.rpow_neg (le_of_lt hd_pos), neg_neg]
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        push_cast
        rw [← pow_mul, Nat.mul_comm P 2]
      rw [hinv, ← Real.rpow_natCast, Real.logb_rpow_eq_mul_logb_of_pos (by linarith)]
      push_cast
      field_simp [ne_of_gt hlog_pos]
    · intro M B_bank hcard b γ A_in A S _hγ
      rw [hcard]
      have haddr_ge : f ^ P ≤ addrCount (2 * f) (P + 1) := by
        unfold addrCount
        have hterm : (2 * f + 1) ^ P ≤ ∑ P₀ ∈ Finset.range (P + 1), (2 * f + 1) ^ P₀ :=
          Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (Nat.lt_succ_self P))
        exact le_trans (Nat.pow_le_pow_left (by omega) P) hterm
      have hpar_ge : f ^ P * b ≤
          (γ + 1) * f ^ P * b + 2 * A_in + numGroups (f ^ P) γ * oblEntryBits M B_bank A S := by
        have h1 : 1 * (f ^ P * b) ≤ (γ + 1) * (f ^ P * b) :=
          Nat.mul_le_mul_right _ (by omega)
        nlinarith
      calc f ^ P * f ^ P * b
          = f ^ P * (f ^ P * b) := by ring
        _ ≤ addrCount (2 * f) (P + 1) *
              ((γ + 1) * f ^ P * b + 2 * A_in +
                numGroups (f ^ P) γ * oblEntryBits M B_bank A S) :=
            Nat.mul_le_mul haddr_ge hpar_ge

/-! ### Non-Exclusion Above `1 / 2` at Every `θ` and Every Bank Size -/

/-- **Algebraic Non-Exclusion Above `1 / 2` at Every `θ > 0` and Every Bank Size**: let
`ψ = A_slope * log₂(k_b + 1) > 1 / 2`, `θ > 0`, `C_ws > 0` and `ε_d = d^{-θ}`. For all large `d`,
the oblivious grouped inequality of `theoremP_coarseWorkspace_grouped_on_bits` (at `m = 0`) holds
for **every** group width `γ ≥ 1`, every machine whose work alphabet has at least two symbols,
every bank of size `k_b`, every `b`, `A_in` and `A`, every pass count `r` with
`A_slope log₂(1/ε_d) + C_0 ≤ r + 1` and every workspace vector with `C_ws ε_d d² b ≤ S_tot + 1`.
These include `r = ⌊A_slope log₂(1/ε_d) + C_0⌋₊` and `S_tot = ⌊C_ws ε_d d² b⌋₊`, the largest values
admitted by `subcriticalPhaseProfile_oblivious_excludes`, so that exclusion cannot be pushed above
`1 / 2` by the grouped bound. The proof uses `H(k_b, r) ≥ (k_b + 1)^{C_0 - 2} d^{θψ}` and
`(γ + 1) d b + ⌈d/γ⌉ σ ≥ 2 √C_ws d^{2 - θ/2} b`. -/
theorem groupedBound_not_excluded_above_half {k_b : ℕ} {θ A_slope C_0 C_ws : ℝ} (hθ : 0 < θ)
    (hslope : 1 / 2 < A_slope * Real.logb 2 ((k_b : ℝ) + 1)) (hCws : 0 < C_ws) :
    ∀ᶠ d : ℕ in atTop,
      ∀ (M : TM) (B_bank : Finset (Fin M.k)), B_bank.card = k_b → 1 ≤ M.g →
        ∀ (b r γ A_in A : ℕ) (S : Fin M.k → ℕ), 1 ≤ γ →
          A_slope * Real.logb 2 (1 / (d : ℝ) ^ (-θ)) + C_0 ≤ (r : ℝ) + 1 →
          C_ws * (d : ℝ) ^ (-θ) * (d * d * b : ℝ) ≤ (workspaceCellSum B_bank S : ℝ) + 1 →
          d * d * b ≤ addrCount B_bank.card r *
            ((γ + 1) * d * b + 2 * A_in + numGroups d γ * oblEntryBits M B_bank A S) := by
  obtain ⟨l, hl⟩ : ∃ l, l = Real.logb 2 ((k_b : ℝ) + 1) := ⟨_, rfl⟩
  rw [← hl] at hslope
  have hl_nonneg : 0 ≤ l := by
    rw [hl]
    exact Real.logb_nonneg (by norm_num) (by linarith [(Nat.cast_nonneg k_b : (0 : ℝ) ≤ k_b)])
  have hl_pos : 0 < l := by
    rcases hl_nonneg.lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hslope; norm_num at hslope
  have hkb : (2 : ℝ) ^ l = (k_b : ℝ) + 1 := by
    rw [hl]; exact Real.rpow_logb (by norm_num) (by norm_num) (by positivity)
  have hA_pos : 0 < A_slope := pos_of_mul_pos_left (by linarith) hl_nonneg
  have hgap : 0 < θ * (2 * (A_slope * l) - 1) := mul_pos hθ (by linarith)
  have htend : Tendsto (fun d : ℕ => Real.logb 2 (d : ℝ)) atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hev1 : ∀ᶠ d : ℕ in atTop, 1 < A_slope * θ * Real.logb 2 (d : ℝ) + C_0 :=
    (tendsto_atTop_add_const_right _ C_0
      (htend.const_mul_atTop (mul_pos hA_pos hθ))).eventually_gt_atTop 1
  have hev2 : ∀ᶠ d : ℕ in atTop, 0 ≤ Real.logb 2 (4 * C_ws) + 2 * (C_0 - 2) * l +
      θ * (2 * (A_slope * l) - 1) * Real.logb 2 (d : ℝ) :=
    (tendsto_atTop_add_const_left _ _ (htend.const_mul_atTop hgap)).eventually_ge_atTop 0
  filter_upwards [eventually_gt_atTop 0, hev1, hev2] with d hd0 h1 h2
  intro M B_bank hcard hg b r γ A_in A S hγ hr hS
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
  have hlog_inv : Real.logb 2 (1 / (d : ℝ) ^ (-θ)) = θ * Real.logb 2 (d : ℝ) := by
    rw [one_div, ← Real.rpow_neg (le_of_lt hd_pos), neg_neg,
      Real.logb_rpow_eq_mul_logb_of_pos hd_pos]
  rw [hlog_inv] at hr
  -- `H = H(k_b, r) ≥ (k_b + 1)^{r - 1} = 2^{l (r - 1)}`, hence `d^θ ≤ 4 C_ws H²`
  have hr1 : 1 ≤ r := by
    have : (0 : ℝ) < (r : ℝ) := by linarith
    exact_mod_cast this
  obtain ⟨H, hH_def⟩ : ∃ H, H = addrCount B_bank.card r := ⟨_, rfl⟩
  rw [← hH_def]
  have hH_nat : (k_b + 1) ^ (r - 1) ≤ H := by
    rw [hH_def, hcard]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (by omega))
  have hHr : (2 : ℝ) ^ (l * ((r : ℝ) - 1)) ≤ (H : ℝ) := by
    have hr_cast : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by rw [Nat.cast_sub hr1]; simp
    calc (2 : ℝ) ^ (l * ((r : ℝ) - 1)) = ((2 : ℝ) ^ l) ^ ((r - 1 : ℕ) : ℝ) := by
          rw [← Real.rpow_mul (by norm_num), hr_cast]
      _ = ((k_b : ℝ) + 1) ^ (r - 1) := by rw [hkb, Real.rpow_natCast]
      _ ≤ (H : ℝ) := by exact_mod_cast hH_nat
  have hkey : (d : ℝ) ^ θ ≤ 4 * C_ws * (H : ℝ) ^ 2 := by
    have hdθ : (d : ℝ) ^ θ = (2 : ℝ) ^ (θ * Real.logb 2 (d : ℝ)) := by
      rw [mul_comm, Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hd_pos]
    have h4C : (2 : ℝ) ^ Real.logb 2 (4 * C_ws) = 4 * C_ws :=
      Real.rpow_logb (by norm_num) (by norm_num) (by positivity)
    have hH2 : (2 : ℝ) ^ (2 * (l * ((r : ℝ) - 1))) ≤ (H : ℝ) ^ 2 := by
      calc (2 : ℝ) ^ (2 * (l * ((r : ℝ) - 1))) = ((2 : ℝ) ^ (l * ((r : ℝ) - 1))) ^ 2 := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; ring_nf
        _ ≤ (H : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hHr 2
    have hexp : θ * Real.logb 2 (d : ℝ) ≤ Real.logb 2 (4 * C_ws) + 2 * (l * ((r : ℝ) - 1)) := by
      have := mul_le_mul_of_nonneg_left hr (by linarith : (0 : ℝ) ≤ 2 * l)
      linarith
    calc (d : ℝ) ^ θ = (2 : ℝ) ^ (θ * Real.logb 2 (d : ℝ)) := hdθ
      _ ≤ (2 : ℝ) ^ (Real.logb 2 (4 * C_ws) + 2 * (l * ((r : ℝ) - 1))) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      _ = 4 * C_ws * (2 : ℝ) ^ (2 * (l * ((r : ℝ) - 1))) := by
          rw [Real.rpow_add (by norm_num), h4C]
      _ ≤ 4 * C_ws * (H : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hH2 (by positivity)
  -- the grouped right-hand side is at least `H (u + v)` with `u = γ d b`, `v = (d / γ) Y` and
  -- `Y = C_ws ε_d d² b ≤ S_tot + 1 ≤ σ + 1`, and `(u + v)² ≥ 4 u v = 4 C_ws ε_d (d² b)²`
  obtain ⟨σ, hσ_def⟩ : ∃ σ, σ = oblEntryBits M B_bank A S := ⟨_, rfl⟩
  obtain ⟨G, hG_def⟩ : ∃ G, G = numGroups d γ := ⟨_, rfl⟩
  rw [← hσ_def, ← hG_def]
  have hσS : workspaceCellSum B_bank S ≤ σ := by
    have hclog : 0 < Nat.clog 2 (M.g + 1) := Nat.clog_pos (by norm_num) (by omega)
    rw [hσ_def]
    unfold oblEntryBits
    calc workspaceCellSum B_bank S ≤ workspaceCellSum B_bank S * Nat.clog 2 (M.g + 1) :=
          Nat.le_mul_of_pos_right _ hclog
      _ ≤ (B_bank.card * (3 * A + 1) + workspaceCellSum B_bank S) * Nat.clog 2 (M.g + 1) :=
          Nat.mul_le_mul_right _ (Nat.le_add_left _ _)
      _ ≤ _ := Nat.le_add_left _ _
  have hGγ : d ≤ G * γ := by
    rw [hG_def]
    unfold numGroups
    have := Nat.lt_div_mul_add (a := d + γ - 1) (by omega : 0 < γ)
    omega
  have hγr : (1 : ℝ) ≤ (γ : ℝ) := by exact_mod_cast hγ
  have hbr : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hGr : (d : ℝ) / (γ : ℝ) ≤ (G : ℝ) := by
    rw [div_le_iff₀ (by positivity)]; exact_mod_cast hGγ
  have hdγ : (d : ℝ) / (γ : ℝ) ≤ (d : ℝ) * (b : ℝ) :=
    (div_le_self (le_of_lt hd_pos) hγr).trans (le_mul_of_one_le_right (le_of_lt hd_pos) hbr)
  obtain ⟨Y, hY⟩ : ∃ Y, Y = C_ws * (d : ℝ) ^ (-θ) * (d * d * b : ℝ) := ⟨_, rfl⟩
  rw [← hY] at hS
  have hσY : Y - 1 ≤ (σ : ℝ) := by
    have : (workspaceCellSum B_bank S : ℝ) ≤ (σ : ℝ) := by exact_mod_cast hσS
    linarith
  obtain ⟨u, hu⟩ : ∃ u, u = (γ : ℝ) * (d : ℝ) * (b : ℝ) := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, v = (d : ℝ) / (γ : ℝ) * Y := ⟨_, rfl⟩
  have huv_nonneg : 0 ≤ u + v := by rw [hu, hv, hY]; positivity
  have hX_le : u + v ≤ (((γ + 1) * d * b + 2 * A_in + G * σ : ℕ) : ℝ) := by
    have e1 : (d : ℝ) / (γ : ℝ) * (σ : ℝ) ≤ (G : ℝ) * (σ : ℝ) :=
      mul_le_mul_of_nonneg_right hGr (Nat.cast_nonneg _)
    have e2 : (d : ℝ) / (γ : ℝ) * (Y - 1) ≤ (d : ℝ) / (γ : ℝ) * (σ : ℝ) :=
      mul_le_mul_of_nonneg_left hσY (by positivity)
    have e3 : (0 : ℝ) ≤ (A_in : ℝ) := Nat.cast_nonneg _
    rw [hu, hv]
    push_cast
    linarith
  have hX2 : 4 * C_ws * (d : ℝ) ^ (-θ) * (d * d * b : ℝ) ^ 2 ≤ (u + v) ^ 2 := by
    have hγ0 : (γ : ℝ) ≠ 0 := by positivity
    have h4 : 4 * C_ws * (d : ℝ) ^ (-θ) * (d * d * b : ℝ) ^ 2 = 4 * (u * v) := by
      rw [hu, hv, hY]
      calc 4 * C_ws * (d : ℝ) ^ (-θ) * ((d : ℝ) * (d : ℝ) * (b : ℝ)) ^ 2
          = ((γ : ℝ) / (γ : ℝ)) *
              (4 * C_ws * (d : ℝ) ^ (-θ) * ((d : ℝ) * (d : ℝ) * (b : ℝ)) ^ 2) := by
            rw [div_self hγ0, one_mul]
        _ = _ := by ring
    rw [h4, show (u + v) ^ 2 = 4 * (u * v) + (u - v) ^ 2 by ring]
    linarith [sq_nonneg (u - v)]
  have hdθ_inv : (d : ℝ) ^ θ * (d : ℝ) ^ (-θ) = 1 := by
    rw [Real.rpow_neg (le_of_lt hd_pos), mul_inv_cancel₀ (Real.rpow_pos_of_pos hd_pos θ).ne']
  have hHX : (d * d * b : ℝ) ≤ (H : ℝ) * (u + v) := by
    apply le_of_sq_le_sq _ (mul_nonneg (Nat.cast_nonneg _) huv_nonneg)
    calc (d * d * b : ℝ) ^ 2 = (d : ℝ) ^ θ * (d : ℝ) ^ (-θ) * (d * d * b : ℝ) ^ 2 := by
          rw [hdθ_inv, one_mul]
      _ ≤ 4 * C_ws * (H : ℝ) ^ 2 * (d : ℝ) ^ (-θ) * (d * d * b : ℝ) ^ 2 := by gcongr
      _ = (H : ℝ) ^ 2 * (4 * C_ws * (d : ℝ) ^ (-θ) * (d * d * b : ℝ) ^ 2) := by ring
      _ ≤ (H : ℝ) ^ 2 * (u + v) ^ 2 := mul_le_mul_of_nonneg_left hX2 (by positivity)
      _ = ((H : ℝ) * (u + v)) ^ 2 := by ring
  have key : ((d * d * b : ℕ) : ℝ) ≤ ((H * ((γ + 1) * d * b + 2 * A_in + G * σ) : ℕ) : ℝ) := by
    rw [Nat.cast_mul H]
    calc ((d * d * b : ℕ) : ℝ) = (d * d * b : ℝ) := by push_cast; ring
      _ ≤ (H : ℝ) * (u + v) := hHX
      _ ≤ _ := mul_le_mul_of_nonneg_left hX_le (Nat.cast_nonneg _)
  exact_mod_cast key

end NativeRelations
