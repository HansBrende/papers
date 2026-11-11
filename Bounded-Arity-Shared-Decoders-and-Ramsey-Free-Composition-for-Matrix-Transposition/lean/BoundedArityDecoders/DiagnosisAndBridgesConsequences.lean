import BoundedArityDecoders.DiagnosisAndBarriersProofs
import BoundedArityDecoders.NativeSweepInterfaceProofs
import BoundedArityDecoders.DualityAndSwapConsequences
import BoundedArityDecoders.AffineCubeComposition
import AdaptiveTransfer.TransferEntryNative

/-!
# Diagnosis Consequences, Adaptive Entry Pullback & Machine-to-Operator Bridges

Kernel-verified consequences of `DiagnosisAndBarriersProofs`, `NativeSweepInterfaceProofs`,
`DualityAndSwapConsequences`, `AffineCubeComposition`, and Paper 18 (`AdaptiveTransfer`):

1. **Diagnosis 1 Consequences (`README.md` §I.1 Line 6)**:
   * `tmWholeCellCutConeBound`: whole-cell input cone bound `≤ entryBits d * (M.k + 1)^D` on any
     `Transpose.TM` frozen-trace `Γ`-cut fibre.
   * `WordStepFrozenTrace`, `wordStepTCPDepth`, & `wordStepTrace_TCPCellConeReduction`: word-step
     `k`-head frozen-trace model with `TCP` cut size `≤ ε * steps` and whole-cell cone bound
     `≤ (k + 1)^D` independent of `|Sigma|` and `d`.
   * `diagnosis_Paper18AdaptiveOriginalEntryPullback`: direct bridge from Paper 18's
     `AdaptiveTransfer` original-entry pullback (`Theorem Q`) to interior `(b - 6s)_+` lanes and
     whole-entry simulator cone fan-in `≤ 2 * (6 * s + 1) * (M.k + 3)^D`.

2. **Diagnoses 2–6 Consequences (`README.md` §I.1–I.2 & §II.2 Line 55)**:
   * `diagnosis2_HighRateTendstoOne`: `1 - C_code * Delta ^ (-α) → 1` as `Delta → ∞` (`α > 0`).
   * `diagnosis3_MultiBitBlockEdgeShiftBarrier`: multi-bit `w`-bit block-edge coding-gain barrier.
   * `ceilSqrtTwoMul` & `diagnosis4_ExplicitSquareCoverAndMaskCertificateBridge`: explicit integer
     ceiling `⌈√(2M)⌉`, `1 - 1 / (4 * ceilSqrtTwoMul M)` rate bound, `finrank U_Δ = componentCount p Δ`,
     and generic tensor-subspace realization explaining Paper 19's mask floor.
   * `invVdW` & `diagnosis5_CombinatorialInvVdWTendstoAndRankBound`: combinatorial inverse van der
     Waerden function `invVdW M₁ M₂ d → ∞` and two-stage rank lower bound `(invVdW M₁ M₂ d) / 4`.
   * `diagnosis6_ModularBehrendAndRandomZModProgression`: modular Behrend `ThreeAPFreeMod` subsets
     in `ZMod d` and `d * (d - 1) * (1 / M₁)^(ℓ - 1) → 0` modular random progression bound.

3. **Machine-to-Operator Representation Bridges (`README.md` §I.2 Line 14 & §II.3.2)**:
   * `encodeTMMatrixToGrid` and `tmMatrix_gridLinear_bridges` (alongside `stoneUnshuffleTMMatrix`
     and `stoneUnshuffleTM_twoTape_linear`).
-/

namespace BoundedArityDecoders

open SharedDecoders Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-! ### 1. Diagnosis 1 Consequences: Whole-Cell Cut Cones, Word-Step `TCP`, & Paper 18 Pullback -/

section Diagnosis1Consequences

/-- **Whole-Cell Cut-Cone Bound on `Transpose.TM` Frozen-Trace Fibres (`README.md` §I.1 Line 6).**
Taking the union of bit-level cones `Q_bit` across all `ℓ : Fin (Transpose.entryBits d)` from
`tmTraceCutConeDetermination`, every whole output cell `(r, c) : ZMod d × ZMod d` on a `Γ`-cut
frozen-trace fibre `C_mat` (`1 ≤ M.k`, `Γ`-free causal path vertex bound `1 ≤ D`) is uniquely
determined by at most `Transpose.entryBits d * (M.k + 1)^D` whole input matrix cells. -/
theorem tmWholeCellCutConeBound
    (M : Transpose.TM) (d steps D : ℕ) [NeZero d]
    (inPos : ℕ → Int)
    (workPos : ℕ → Fin M.k → Int)
    (emitStep : Fin (Transpose.inputLength d) → ℕ)
    (Γ : Finset ℕ)
    (C_mat : Set (State d (CanonicalWordAlphabet d)))
    (hk : 1 ≤ M.k) (hD : 1 ≤ D)
    (hFibre : IsFrozenTraceCutFibre M d steps inPos workPos emitStep Γ C_mat)
    (hDepth : ∀ π : List ℕ, IsCutFreeCausalPath workPos steps Γ π → π.length ≤ D) :
    ∀ (r c : ZMod d),
      ∃ Q_cell : Finset (ZMod d × ZMod d),
        Q_cell.card ≤ Transpose.entryBits d * (M.k + 1) ^ D ∧
        ∀ X₁ ∈ C_mat, ∀ X₂ ∈ C_mat,
          (∀ ij ∈ Q_cell, X₁ ij.1 ij.2 = X₂ ij.1 ij.2) →
          X₁ c r = X₂ c r := by
  classical
  intro r c
  have hBit := (tmTraceCutConeDetermination M d steps D inPos workPos emitStep Γ C_mat
    hk hD hFibre hDepth).2 r c
  choose Q_bit hQ_card hQ_det using hBit
  let Q_cell : Finset (ZMod d × ZMod d) := Finset.univ.biUnion Q_bit
  refine ⟨Q_cell, ?_, ?_⟩
  · calc Q_cell.card
        ≤ ∑ ℓ : Fin (Transpose.entryBits d), (Q_bit ℓ).card := Finset.card_biUnion_le
      _ ≤ ∑ _ℓ : Fin (Transpose.entryBits d), (M.k + 1) ^ D :=
          Finset.sum_le_sum fun ℓ _ => hQ_card ℓ
      _ = Transpose.entryBits d * (M.k + 1) ^ D := by simp
  · intro X₁ hX₁ X₂ hX₂ hAgree
    funext ℓ
    exact hQ_det ℓ X₁ hX₁ X₂ hX₂ fun ij hij =>
      hAgree ij (Finset.mem_biUnion.mpr ⟨ℓ, Finset.mem_univ ℓ, hij⟩)

/-- Explicit `TCP` causal-path vertex bound `D(k, ε)` from Paper 14 (`BoundedStackDepth.parK`,
`BoundedStackDepth.parP`), depending only on `(k, ε)` and independent of alphabet and dimension. -/
noncomputable def wordStepTCPDepth (k : ℕ) (ε : ℝ) : ℕ :=
  max 1 (BoundedStackDepth.parK k (ε / 2) ^ BoundedStackDepth.parP k (ε / 2) * max 1 ⌈2 / ε⌉₊)

/-- A concrete word-step `k`-head frozen-trace computation on `State d Sigma`: at each step
`t : Fin steps`, `k` unit-speed work heads scan/write whole `Sigma`-cells, the input head reads
whole cell `inCell t`, and output cell `(r, c)` is produced at terminal step `outStep r c`. -/
structure WordStepFrozenTrace (d k steps : ℕ) (Sigma : Type*) where
  StateQ : Type
  initState : StateQ
  blankWork : Sigma
  workPos : ℕ → Fin k → Int
  unit_speed : ∀ (t : ℕ) (h : Fin k), |workPos (t + 1) h - workPos t h| ≤ 1
  inCell : Fin steps → ZMod d × ZMod d
  outStep : ZMod d → ZMod d → Fin steps
  stepState : Fin steps → StateQ → Sigma → (Fin k → Sigma) → StateQ
  stepWrite : Fin steps → StateQ → Sigma → (Fin k → Sigma) → (Fin k → Sigma)
  stepOut : Fin steps → StateQ → Sigma → (Fin k → Sigma) → Sigma

/-- Pre-step control state and work-tape contents after `t` transitions of a `WordStepFrozenTrace`
on input matrix `X : State d Sigma`. -/
def WordStepFrozenTrace.cfgAt {d k steps : ℕ} {Sigma : Type*}
    (T : WordStepFrozenTrace d k steps Sigma) (X : State d Sigma) :
    ℕ → T.StateQ × (Fin k → Int → Sigma)
  | 0 => (T.initState, fun _ _ => T.blankWork)
  | t + 1 =>
      if ht : t < steps then
        let prev := T.cfgAt X t
        let inVal := X (T.inCell ⟨t, ht⟩).1 (T.inCell ⟨t, ht⟩).2
        let scanned := fun h => prev.2 h (T.workPos t h)
        let written := T.stepWrite ⟨t, ht⟩ prev.1 inVal scanned
        (T.stepState ⟨t, ht⟩ prev.1 inVal scanned,
          fun h pos => if pos = T.workPos t h then written h else prev.2 h pos)
      else T.cfgAt X t

/-- Output cell `(r, c)` emitted at designated step `T.outStep r c` on input `X`. -/
def WordStepFrozenTrace.evalOut {d k steps : ℕ} {Sigma : Type*}
    (T : WordStepFrozenTrace d k steps Sigma) (X : State d Sigma) (r c : ZMod d) : Sigma :=
  let t := T.outStep r c
  let prev := T.cfgAt X t.val
  T.stepOut t prev.1 (X (T.inCell t).1 (T.inCell t).2) (fun h => prev.2 h (T.workPos t.val h))

/-- A subset `C ⊆ State d Sigma` lies in a single `Γ`-cut fibre of `T` if all `X ∈ C` share the
same post-step control state and written work-tape symbols at every cut step `u ∈ Γ` (`u < steps`). -/
def WordStepFrozenTrace.IsCutFibre {d k steps : ℕ} {Sigma : Type*}
    (T : WordStepFrozenTrace d k steps Sigma) (Γ : Finset ℕ) (C : Set (State d Sigma)) : Prop :=
  ∀ X₁ ∈ C, ∀ X₂ ∈ C, ∀ u ∈ Γ, u < steps →
    (T.cfgAt X₁ (u + 1)).1 = (T.cfgAt X₂ (u + 1)).1 ∧
    ∀ h : Fin k, (T.cfgAt X₁ (u + 1)).2 h (T.workPos u h) =
      (T.cfgAt X₂ (u + 1)).2 h (T.workPos u h)

private theorem cutFreeCausalPath_snoc {k : ℕ} {workPos : ℕ → Fin k → Int} {T : ℕ} {Γ : Finset ℕ} :
    ∀ {π : List ℕ} {v u : ℕ},
      π.getLast? = some v →
      IsCutFreeCausalPath workPos T Γ π →
      TMDepStep workPos T u v →
      u ∉ Γ →
      u < T →
      IsCutFreeCausalPath workPos T Γ (π ++ [u])
  | [], _, _, hlast, _, _, _, _ => by simp at hlast
  | [x], v, u, hlast, _, hstep, huΓ, huT => by
      simp only [List.getLast?_singleton, Option.some.injEq] at hlast
      subst hlast
      exact ⟨hstep, huΓ, huT⟩
  | x :: y :: rest, v, u, hlast, ⟨hxy, hyΓ, hrest⟩, hstep, huΓ, huT => by
      have hlast' : (y :: rest).getLast? = some v := by simpa using hlast
      exact ⟨hxy, hyΓ, cutFreeCausalPath_snoc hlast' hrest hstep huΓ huT⟩

private theorem cfgAt_work_unvisited {d k steps : ℕ} {Sigma : Type*}
    (T : WordStepFrozenTrace d k steps Sigma) (X : State d Sigma) (h : Fin k) (pos : Int) :
    ∀ v : ℕ, (∀ u < v, T.workPos u h ≠ pos) → (T.cfgAt X v).2 h pos = T.blankWork
  | 0, _ => rfl
  | v + 1, hno => by
      have ih := cfgAt_work_unvisited T X h pos v (fun u hu => hno u (Nat.lt_succ_of_lt hu))
      dsimp only [WordStepFrozenTrace.cfgAt]
      split_ifs with hv
      · have hne : pos ≠ T.workPos v h := (hno v (Nat.lt_succ_self v)).symm
        simp [hne, ih]
      · exact ih

private theorem cfgAt_work_after_visit {d k steps : ℕ} {Sigma : Type*}
    (T : WordStepFrozenTrace d k steps Sigma) (X : State d Sigma) (h : Fin k) (u : ℕ) :
    ∀ v : ℕ, u < v → (∀ w : ℕ, u < w → w < v → T.workPos w h ≠ T.workPos u h) →
      (T.cfgAt X v).2 h (T.workPos u h) = (T.cfgAt X (u + 1)).2 h (T.workPos u h)
  | 0, huv, _ => absurd huv (Nat.not_lt_zero _)
  | v + 1, huv, hno => by
      rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ huv) with rfl | hlt
      · rfl
      · have ih := cfgAt_work_after_visit T X h u v hlt
          (fun w hwu hwv => hno w hwu (Nat.lt_succ_of_lt hwv))
        conv_lhs => rw [WordStepFrozenTrace.cfgAt]
        split_ifs with hv
        · have hne : T.workPos u h ≠ T.workPos v h :=
            (hno v hlt (Nat.lt_succ_self v)).symm
          simp only [hne, ↓reduceIte]
          exact ih
        · exact ih

private theorem tmDepStep_iff_mergeBlockStep {k : ℕ} (workPos : ℕ → Fin k → Int) (T u v : ℕ) :
    TMDepStep workPos T u v ↔ MergeDepth.BlockStep (fun h t => workPos t h) T v u := by
  unfold TMDepStep MergeDepth.BlockStep IsLastWorkVisit
  refine and_congr_right fun _ => or_congr ⟨fun h => by omega, fun h => by omega⟩
    (exists_congr fun h => ?_)
  rw [MergeDepth.prevS_spec]

/-- **Word-Step `TCP` Cell-Cone Reduction (`README.md` §I.1 Line 6).**
For every `k ≥ 1` and `ε > 0`, setting `D := wordStepTCPDepth k ε`, any `WordStepFrozenTrace`
admits a step cut `Γ` of size `|Γ| ≤ ε * steps` reducing all `Γ`-free causal paths to `≤ D`
vertices, under which every output cell `(r, c)` has a fixed input cone `Q_cell` of at most
`(k + 1)^D` whole cells (independent of `|Sigma|` and `d`) determining `T.evalOut · r c` across
every `Γ`-cut fibre `C` (and hence determining `X c r` whenever `T` transposes on `C`). -/
theorem wordStepTrace_TCPCellConeReduction
    {d k steps : ℕ} {Sigma : Type*}
    (T : WordStepFrozenTrace d k steps Sigma)
    (hk : 1 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    1 ≤ wordStepTCPDepth k ε ∧
    ∃ Γ : Finset ℕ,
      (∀ u ∈ Γ, u < steps) ∧
      (Γ.card : ℝ) ≤ ε * (steps : ℝ) ∧
      (∀ π : List ℕ, IsCutFreeCausalPath T.workPos steps Γ π →
        π.length ≤ wordStepTCPDepth k ε) ∧
      ∀ (r c : ZMod d),
        ∃ Q_cell : Finset (ZMod d × ZMod d),
          Q_cell.card ≤ (k + 1) ^ wordStepTCPDepth k ε ∧
          ∀ (C : Set (State d Sigma)), T.IsCutFibre Γ C →
            ∀ X₁ ∈ C, ∀ X₂ ∈ C,
              (∀ ij ∈ Q_cell, X₁ ij.1 ij.2 = X₂ ij.1 ij.2) →
              T.evalOut X₁ r c = T.evalOut X₂ r c := by
  classical
  set D := wordStepTCPDepth k ε
  have hD1 : 1 ≤ D := le_max_left _ _
  refine ⟨hD1, ?_⟩
  by_cases hsteps0 : steps = 0
  · subst hsteps0
    refine ⟨∅, by simp, by simp, ?_, fun r c => Fin.elim0 (T.outStep r c)⟩
    intro π hπ
    cases π with
    | nil => simp
    | cons v rest =>
      cases rest with
      | nil => exact absurd hπ (Nat.not_lt_zero _)
      | cons u rest' => exact absurd hπ.1.1 (Nat.not_lt_zero _)
  · let ε' : ℝ := ε / 2
    have hε' : 0 < ε' := by dsimp [ε']; linarith
    let R : ℕ := max 1 ⌈2 / ε⌉₊
    have hR : 1 ≤ R := le_max_left _ _
    let xs : Fin k → ℕ → ℤ := fun h t => T.workPos t h
    have hxs : ∀ h, BoundedNesting.IsWalk (xs h) := fun h t => T.unit_speed t h
    obtain ⟨Γ₀, hcard₀, hpath₀⟩ := BoundedStackDepth.genie k hε' hR xs hxs steps
    let Γ := Γ₀.filter (· < steps)
    have hΓ_lt : ∀ u ∈ Γ, u < steps := fun u hu => (Finset.mem_filter.mp hu).2
    have hΓ_card : (Γ.card : ℝ) ≤ ε * (steps : ℝ) := by
      have hc1 : (Γ.card : ℝ) ≤ (Γ₀.card : ℝ) := Nat.cast_le.mpr (Finset.card_filter_le _ _)
      have hRpos : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hR
      have hRceil : 2 / ε ≤ (R : ℝ) :=
        (Nat.le_ceil (2 / ε)).trans (by exact_mod_cast le_max_right 1 ⌈2 / ε⌉₊)
      have h2 : 2 ≤ (R : ℝ) * ε := (div_le_iff₀ hε).mp hRceil
      have hSnn : (0 : ℝ) ≤ (steps : ℝ) := Nat.cast_nonneg steps
      have hRS : (R : ℝ) * (Γ₀.card : ℝ) ≤ (R : ℝ) * (ε * (steps : ℝ)) := by
        dsimp [ε'] at hcard₀
        nlinarith
      exact hc1.trans (le_of_mul_le_mul_left hRS hRpos)
    have hCutToDep : ∀ π : List ℕ, IsCutFreeCausalPath T.workPos steps Γ π →
        MergeDepth.IsDepPath xs steps π ∧ BoundedNesting.LinNet.GFree Γ₀ π := by
      intro π
      induction π with
      | nil => exact fun _ => ⟨trivial, fun _ hv => by simp at hv⟩
      | cons v rest ih =>
        cases rest with
        | nil => exact fun _ => ⟨trivial, fun _ hv => by simp at hv⟩
        | cons u rest' =>
          rintro ⟨hstep, huΓ, hrest⟩
          obtain ⟨hudep, hufree⟩ := ih hrest
          have hblk : MergeDepth.BlockStep xs steps v u :=
            (tmDepStep_iff_mergeBlockStep T.workPos steps u v).mp hstep
          have hdep : MergeDepth.DepStep xs steps v u :=
            (MergeDepth.blockStep_iff xs steps v u).mp hblk
          have huS : u < steps := Nat.lt_trans (MergeDepth.depStep_lt hdep).1 hstep.1
          have hu0 : u ∉ Γ₀ := fun hm => huΓ (Finset.mem_filter.mpr ⟨hm, huS⟩)
          exact ⟨⟨hdep, hudep⟩, (MergeDepth.gfree_cons_cons).mpr ⟨hu0, hufree⟩⟩
    have hΓ_depth : ∀ π : List ℕ, IsCutFreeCausalPath T.workPos steps Γ π → π.length ≤ D := by
      intro π hπ
      obtain ⟨hdep, hfree⟩ := hCutToDep π hπ
      exact (hpath₀ π hdep hfree).trans (le_max_right _ _)
    refine ⟨Γ, hΓ_lt, hΓ_card, hΓ_depth, fun r c => ?_⟩
    let wStep := T.outStep r c
    let net : BoundedNesting.LinNet ℚ 1 1 := {
      out := fun v => (Finset.range steps).filter (fun u => MergeDepth.BlockStep xs steps v u)
      out_lt := fun v u hu => by
        have hd := (MergeDepth.blockStep_iff xs steps v u).mp (Finset.mem_filter.mp hu).2
        exact (MergeDepth.depStep_lt hd).1
      c := fun _ => 0, A := fun _ _ => 0, a := fun _ => 0, rd := fun _ => none }
    let coneSteps : Finset ℕ := MergeDepth.coneV net Γ wStep.val
    let Q_cell : Finset (ZMod d × ZMod d) :=
      (coneSteps.attach).image fun u =>
        if hu : u.1 < steps then T.inCell ⟨u.1, hu⟩ else (0, 0)
    have hSumPow : ∀ m : ℕ, ∑ h ∈ Finset.range m, (k + 1) ^ h ≤ (k + 1) ^ m := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [Finset.sum_range_succ, pow_succ]
        have h1 : ∑ h ∈ Finset.range m, (k + 1) ^ h ≤ (k + 1) ^ m * k :=
          ih.trans (Nat.le_mul_of_pos_right _ hk)
        nlinarith
    have hConeCard : coneSteps.card ≤ (k + 1) ^ D := by
      have hdeg : ∀ u, (net.out u).card ≤ k + 1 := fun u => MergeDepth.card_blockOut_le xs steps u
      have hD1_eq : D = (D - 1) + 1 := (Nat.sub_add_cancel hD1).symm
      have hnetD : ∀ π ∈ net.paths wStep.val, BoundedNesting.LinNet.GFree Γ π →
          π.length ≤ (D - 1) + 1 := by
        intro π hπ hfree
        have hconv : ∀ (v : ℕ) (ρ : List ℕ), v < steps → ρ ∈ net.paths v →
            BoundedNesting.LinNet.GFree Γ ρ → IsCutFreeCausalPath T.workPos steps Γ ρ := by
          intro v ρ
          induction ρ generalizing v with
          | nil => intros; trivial
          | cons a rest ih =>
            intro hvS hρ hfr
            have ha := MergeDepth.head_eq_of_mem_paths hρ
            rw [ha] at hρ hfr ⊢
            cases rest with
            | nil => exact hvS
            | cons b rest' =>
              obtain ⟨hbout, hbrest⟩ := (MergeDepth.cons_cons_mem_paths).mp hρ
              obtain ⟨hbΓ, hfr'⟩ := (MergeDepth.gfree_cons_cons).mp hfr
              obtain ⟨hbS_mem, hb_blk⟩ := Finset.mem_filter.mp hbout
              have hbS : b < steps := Finset.mem_range.mp hbS_mem
              have hbstep : TMDepStep T.workPos steps b v :=
                (tmDepStep_iff_mergeBlockStep T.workPos steps b v).mpr hb_blk
              exact ⟨hbstep, hbΓ, ih b hbS hbrest hfr'⟩
        rw [← hD1_eq]
        exact hΓ_depth π (hconv wStep.val π wStep.isLt hπ hfree)
      have hc := MergeDepth.card_coneV_le net hdeg hnetD
      rw [← hD1_eq] at hc
      exact hc.trans (hSumPow D)
    have hInCone : ∀ u < steps, InCutCausalCone T.workPos steps Γ wStep.val u → u ∈ coneSteps := by
      intro u _ ⟨π, hhead, hlast, hcut⟩
      have hmem : ∀ (ρ : List ℕ) (v : ℕ), ρ.head? = some v →
          IsCutFreeCausalPath T.workPos steps Γ ρ →
          ρ ∈ net.paths v ∧ BoundedNesting.LinNet.GFree Γ ρ := by
        intro ρ
        induction ρ with
        | nil => intro _ hh _; simp at hh
        | cons a rest ih =>
          intro v hh hc
          simp only [List.head?_cons, Option.some.injEq] at hh; subst hh
          cases rest with
          | nil => exact ⟨MergeDepth.singleton_mem_paths _ _, MergeDepth.gfree_singleton _ _⟩
          | cons b rest' =>
            obtain ⟨hstep, hbΓ, hrest⟩ := hc
            obtain ⟨hp', hf'⟩ := ih b rfl hrest
            have hblk : MergeDepth.BlockStep xs steps a b :=
              (tmDepStep_iff_mergeBlockStep T.workPos steps b a).mp hstep
            have hbS : b < steps := Nat.lt_trans
              (MergeDepth.depStep_lt ((MergeDepth.blockStep_iff xs steps a b).mp hblk)).1 hstep.1
            have hbout : b ∈ net.out a :=
              Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hbS, hblk⟩
            exact ⟨(MergeDepth.cons_cons_mem_paths).mpr ⟨hbout, hp'⟩,
              (MergeDepth.gfree_cons_cons).mpr ⟨hbΓ, hf'⟩⟩
      have hlastD : ∀ (ρ : List ℕ) (d₀ u₀ : ℕ), ρ.getLast? = some u₀ → ρ.getLastD d₀ = u₀ := by
        intro ρ
        induction ρ with
        | nil => intro _ _ hh; simp at hh
        | cons x rest ih =>
          intro d₀ u₀ hh
          cases rest with
          | nil => simp only [List.getLast?_singleton, Option.some.injEq] at hh; subst hh; rfl
          | cons y rest' => rw [List.getLastD_cons]; exact ih x u₀ (by simpa using hh)
      obtain ⟨hp, hf⟩ := hmem π wStep.val hhead hcut
      exact (MergeDepth.mem_coneV net).mpr ⟨π, hp, hf, hlastD π wStep.val u hlast⟩
    refine ⟨Q_cell, ?_, ?_⟩
    · calc Q_cell.card ≤ coneSteps.attach.card := Finset.card_image_le
        _ = coneSteps.card := Finset.card_attach
        _ ≤ (k + 1) ^ D := hConeCard
    · intro C hCut X₁ hX₁ X₂ hX₂ hAgree
      have hStepAgree : ∀ v : ℕ, ∀ hv : v < steps,
          InCutCausalCone T.workPos steps Γ wStep.val v →
          (T.cfgAt X₁ v).1 = (T.cfgAt X₂ v).1 ∧
          X₁ (T.inCell ⟨v, hv⟩).1 (T.inCell ⟨v, hv⟩).2 =
            X₂ (T.inCell ⟨v, hv⟩).1 (T.inCell ⟨v, hv⟩).2 ∧
          (∀ h : Fin k, (T.cfgAt X₁ v).2 h (T.workPos v h) =
            (T.cfgAt X₂ v).2 h (T.workPos v h)) := by
        intro v
        induction v using Nat.strong_induction_on with
        | h v ih =>
          intro hv hcone
          obtain ⟨π, hhead, hlast, hcutP⟩ := hcone
          have hvMem : v ∈ coneSteps := hInCone v hv ⟨π, hhead, hlast, hcutP⟩
          have hInQ : T.inCell ⟨v, hv⟩ ∈ Q_cell := by
            refine Finset.mem_image.mpr ⟨⟨v, hvMem⟩, Finset.mem_attach _ _, ?_⟩
            simp [hv]
          have hInEq := hAgree _ hInQ
          have hStateEq : (T.cfgAt X₁ v).1 = (T.cfgAt X₂ v).1 := by
            rcases v with _ | u
            · rfl
            · have huS : u < steps := Nat.lt_of_succ_lt hv
              by_cases huΓ : u ∈ Γ
              · exact (hCut X₁ hX₁ X₂ hX₂ u huΓ huS).1
              · have hstep : TMDepStep T.workPos steps u (u + 1) := ⟨hv, Or.inl rfl⟩
                have hconeU : InCutCausalCone T.workPos steps Γ wStep.val u :=
                  ⟨π ++ [u], by cases π with | nil => simp at hhead | cons _ _ => simpa using hhead,
                    List.getLast?_append_of_ne_nil _ (List.cons_ne_nil u []),
                    cutFreeCausalPath_snoc hlast hcutP hstep huΓ huS⟩
                obtain ⟨hqU, hinU, hwkU⟩ := ih u (Nat.lt_succ_self u) huS hconeU
                dsimp only [WordStepFrozenTrace.cfgAt]
                simp [huS, hqU, hinU, funext hwkU]
          have hWorkEq : ∀ h : Fin k,
              (T.cfgAt X₁ v).2 h (T.workPos v h) = (T.cfgAt X₂ v).2 h (T.workPos v h) := by
            intro h
            let visits := (Finset.range v).filter (fun u => T.workPos u h = T.workPos v h)
            by_cases hne : visits.Nonempty
            · let u := visits.max' hne
              have huMem : u ∈ visits := Finset.max'_mem visits hne
              obtain ⟨huLt_mem, huPos⟩ := Finset.mem_filter.mp huMem
              have huLt : u < v := Finset.mem_range.mp huLt_mem
              have huNo : ∀ w : ℕ, u < w → w < v → T.workPos w h ≠ T.workPos v h := by
                intro w hwu hwv heq
                have hwMem : w ∈ visits :=
                  Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hwv, heq⟩
                exact absurd (Finset.le_max' visits w hwMem) (by omega)
              have hrw1 := cfgAt_work_after_visit T X₁ h u v huLt
                (fun w h1 h2 => by rw [huPos]; exact huNo w h1 h2)
              have hrw2 := cfgAt_work_after_visit T X₂ h u v huLt
                (fun w h1 h2 => by rw [huPos]; exact huNo w h1 h2)
              rw [← huPos, hrw1, hrw2]
              have huS : u < steps := Nat.lt_trans huLt hv
              by_cases huΓ : u ∈ Γ
              · exact (hCut X₁ hX₁ X₂ hX₂ u huΓ huS).2 h
              · have hstep : TMDepStep T.workPos steps u v :=
                  ⟨hv, Or.inr ⟨h, huLt, huPos, huNo⟩⟩
                have hconeU : InCutCausalCone T.workPos steps Γ wStep.val u :=
                  ⟨π ++ [u], by cases π with | nil => simp at hhead | cons _ _ => simpa using hhead,
                    List.getLast?_append_of_ne_nil _ (List.cons_ne_nil u []),
                    cutFreeCausalPath_snoc hlast hcutP hstep huΓ huS⟩
                obtain ⟨hqU, hinU, hwkU⟩ := ih u huLt huS hconeU
                dsimp only [WordStepFrozenTrace.cfgAt]
                simp [huS, hqU, hinU, funext hwkU]
            · rw [Finset.not_nonempty_iff_eq_empty] at hne
              have hno : ∀ u < v, T.workPos u h ≠ T.workPos v h := by
                intro u huv heq
                have hm : u ∈ visits :=
                  Finset.mem_filter.mpr ⟨Finset.mem_range.mpr huv, heq⟩
                rw [hne] at hm; exact Finset.notMem_empty u hm
              rw [cfgAt_work_unvisited T X₁ h _ v hno, cfgAt_work_unvisited T X₂ h _ v hno]
          exact ⟨hStateEq, hInEq, hWorkEq⟩
      have hwCone : InCutCausalCone T.workPos steps Γ wStep.val wStep.val :=
        ⟨[wStep.val], rfl, rfl, wStep.isLt⟩
      obtain ⟨hqW, hinW, hwkW⟩ := hStepAgree wStep.val wStep.isLt hwCone
      dsimp only [WordStepFrozenTrace.evalOut]
      rw [hqW, hinW, funext hwkW]

private theorem card_depCone_le_pow {k L T D : ℕ}
    (xs : Fin k → ℕ → ℤ) (rdStep : ℕ → Option (Fin L)) (B : Finset ℕ) (root : ℕ)
    (hD : 1 ≤ D)
    (hDepth : ∀ π : List ℕ, MergeDepth.IsDepPath xs T π →
      BoundedNesting.LinNet.GFree B π → π.length ≤ D) :
    (BoundedStackDepth.depCone xs T rdStep B root).card ≤
      ∑ h ∈ Finset.range D, (k + 1) ^ h := by
  classical
  let net : BoundedNesting.LinNet ℚ 1 1 := {
    out := fun v => (Finset.range T).filter (fun u => MergeDepth.BlockStep xs T v u)
    out_lt := fun v u hu => by
      have hd := (MergeDepth.blockStep_iff xs T v u).mp (Finset.mem_filter.mp hu).2
      exact (MergeDepth.depStep_lt hd).1
    c := fun _ => 0, A := fun _ _ => 0, a := fun _ => 0, rd := fun _ => none }
  have hDepToPaths : ∀ (v : ℕ) (ρ : List ℕ),
      MergeDepth.IsDepPath xs T (v :: ρ) → (v :: ρ) ∈ net.paths v := by
    intro v ρ
    induction ρ generalizing v with
    | nil => intro _; exact MergeDepth.singleton_mem_paths _ _
    | cons u rest ih =>
      rintro ⟨hstep, hrest⟩
      have huT : u < T := Nat.lt_trans (MergeDepth.depStep_lt hstep).1 (MergeDepth.depStep_lt hstep).2
      have hblk : MergeDepth.BlockStep xs T v u := (MergeDepth.blockStep_iff xs T v u).mpr hstep
      have huOut : u ∈ net.out v := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr huT, hblk⟩
      exact (MergeDepth.cons_cons_mem_paths).mpr ⟨huOut, ih u hrest⟩
  have hPathsToDep : ∀ (v : ℕ) (π : List ℕ), π ∈ net.paths v → MergeDepth.IsDepPath xs T π := by
    intro v π
    induction π generalizing v with
    | nil => intros; trivial
    | cons a rest ih =>
      intro hπ
      have ha := MergeDepth.head_eq_of_mem_paths hπ
      rw [ha] at hπ ⊢
      cases rest with
      | nil => trivial
      | cons b rest' =>
        obtain ⟨hbOut, hbrest⟩ := (MergeDepth.cons_cons_mem_paths).mp hπ
        have hstep : MergeDepth.DepStep xs T v b :=
          (MergeDepth.blockStep_iff xs T v b).mp (Finset.mem_filter.mp hbOut).2
        exact ⟨hstep, ih b hbrest⟩
  have hdeg : ∀ u, (net.out u).card ≤ k + 1 := fun u => MergeDepth.card_blockOut_le xs T u
  have hD1 : D = (D - 1) + 1 := (Nat.sub_add_cancel hD).symm
  have hnetD : ∀ π ∈ net.paths root, BoundedNesting.LinNet.GFree B π → π.length ≤ (D - 1) + 1 := by
    intro π hπ hfree
    rw [← hD1]
    exact hDepth π (hPathsToDep root π hπ) hfree
  have hConeCard := MergeDepth.card_coneV_le net hdeg hnetD
  rw [← hD1] at hConeCard
  let cone := BoundedStackDepth.depCone xs T rdStep B root
  have hSub : ∀ j ∈ cone, ∃ u ∈ MergeDepth.coneV net B root, rdStep u = some j := by
    intro j hj
    obtain ⟨_, ρ, hdep, hfree, hrd⟩ := Finset.mem_filter.mp hj
    exact ⟨(root :: ρ).getLastD root,
      (MergeDepth.mem_coneV net).mpr ⟨root :: ρ, hDepToPaths root ρ hdep, hfree, rfl⟩, hrd⟩
  choose uOf huMem huRd using hSub
  have hInj : Set.InjOn (fun j : {x // x ∈ cone} => uOf j.1 j.2) ↑(Finset.univ : Finset {x // x ∈ cone}) := by
    intro j₁ _ j₂ _ hEq
    dsimp only at hEq
    have h1 := huRd j₁.1 j₁.2
    have h2 := huRd j₂.1 j₂.2
    rw [hEq] at h1
    exact Subtype.ext (Option.some.inj (h1.symm.trans h2))
  have hImgSub : Finset.univ.image (fun j : {x // x ∈ cone} => uOf j.1 j.2) ⊆
      MergeDepth.coneV net B root := by
    intro u hu
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hu
    exact huMem j.1 j.2
  calc cone.card
      = (Finset.univ : Finset {x // x ∈ cone}).card := by simp
    _ = (Finset.univ.image (fun j : {x // x ∈ cone} => uOf j.1 j.2)).card :=
        (Finset.card_image_of_injOn hInj).symm
    _ ≤ (MergeDepth.coneV net B root).card := Finset.card_le_card hImgSub
    _ ≤ ∑ h ∈ Finset.range D, (k + 1) ^ h := hConeCard

private theorem card_inputDilation_le {L : ℕ} (S : Finset (Fin L)) (R : ℕ) :
    (AdaptiveTransfer.inputDilation S R).card ≤ (2 * R + 1) * S.card := by
  classical
  let ball (j : Fin L) : Finset (Fin L) :=
    Finset.univ.filter fun p => |(p.val : ℤ) - (j.val : ℤ)| ≤ (R : ℤ)
  have hSub : AdaptiveTransfer.inputDilation S R ⊆ S.biUnion ball := by
    intro p hp
    obtain ⟨_, j, hjS, hnear⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_biUnion.mpr ⟨j, hjS, Finset.mem_filter.mpr ⟨Finset.mem_univ p, hnear⟩⟩
  have hBall : ∀ j : Fin L, (ball j).card ≤ 2 * R + 1 := by
    intro j
    let f (p : Fin L) : ℕ := ((p.val : ℤ) - (j.val : ℤ) + (R : ℤ)).toNat
    have hImg : (ball j).image f ⊆ Finset.range (2 * R + 1) := by
      intro x hx
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
      have habs := abs_le.mp (Finset.mem_filter.mp hp).2
      exact Finset.mem_range.mpr (by dsimp [f]; omega)
    have hInj : Set.InjOn f ↑(ball j) := by
      intro p₁ hp₁ p₂ hp₂ hEq
      have h1 := abs_le.mp (Finset.mem_filter.mp hp₁).2
      have h2 := abs_le.mp (Finset.mem_filter.mp hp₂).2
      dsimp [f] at hEq
      exact Fin.ext (by omega)
    calc (ball j).card = ((ball j).image f).card := (Finset.card_image_of_injOn hInj).symm
      _ ≤ (Finset.range (2 * R + 1)).card := Finset.card_le_card hImg
      _ = 2 * R + 1 := Finset.card_range _
  calc (AdaptiveTransfer.inputDilation S R).card
      ≤ (S.biUnion ball).card := Finset.card_le_card hSub
    _ ≤ ∑ j ∈ S, (ball j).card := Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ S, (2 * R + 1) := Finset.sum_le_sum fun j _ => hBall j
    _ = (2 * R + 1) * S.card := by simp [Nat.mul_comm]

private theorem card_inputBoundary_le (L R : ℕ) :
    (AdaptiveTransfer.inputBoundary L R).card ≤ 2 * R := by
  classical
  let leftB : Finset (Fin L) := Finset.univ.filter fun p => p.val < R
  let rightB : Finset (Fin L) := Finset.univ.filter fun p => L ≤ p.val + R
  have hSub : AdaptiveTransfer.inputBoundary L R ⊆ leftB ∪ rightB := by
    intro p hp
    rcases (Finset.mem_filter.mp hp).2 with hL | hR
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ p, hL⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ p, hR⟩)
  have hLeft : leftB.card ≤ R := by
    have hImg : leftB.image Fin.val ⊆ Finset.range R := by
      intro x hx
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
    calc leftB.card = (leftB.image Fin.val).card :=
          (Finset.card_image_of_injective _ Fin.val_injective).symm
      _ ≤ (Finset.range R).card := Finset.card_le_card hImg
      _ = R := Finset.card_range R
  have hRight : rightB.card ≤ R := by
    let g (p : Fin L) : ℕ := L - 1 - p.val
    have hImg : rightB.image g ⊆ Finset.range R := by
      intro x hx
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
      have hpR := (Finset.mem_filter.mp hp).2
      have hpL := p.isLt
      exact Finset.mem_range.mpr (by dsimp [g]; omega)
    have hInj : Set.InjOn g ↑rightB := by
      intro p₁ _ p₂ _ hEq
      have h1 := p₁.isLt; have h2 := p₂.isLt
      dsimp [g] at hEq
      exact Fin.ext (by omega)
    calc rightB.card = (rightB.image g).card := (Finset.card_image_of_injOn hInj).symm
      _ ≤ (Finset.range R).card := Finset.card_le_card hImg
      _ = R := Finset.card_range R
  calc (AdaptiveTransfer.inputBoundary L R).card
      ≤ (leftB ∪ rightB).card := Finset.card_le_card hSub
    _ ≤ leftB.card + rightB.card := Finset.card_union_le _ _
    _ ≤ R + R := Nat.add_le_add hLeft hRight
    _ = 2 * R := by omega

/-- **Paper 18 Adaptive Original-Entry Pullback & Interior `(b - 6s)_+` Cone Bound
(`README.md` §I.1 Line 6).**
Exports Paper 18 (`AdaptiveTransfer.TransferEntry`):
1. (*Uniform original-entry success tail*) For any adaptive `M : Transpose.TM`, `c ≥ 0`, `δ > 0`,
   there exist batch size `s > 0` and `d₀` such that for all `d ≥ d₀`, `24 * s ≤ entryBits d` and
   fewer than `2^((1 - δ/2) * d^2 * entryBits d)` timely correct inputs fail `EntryCertificates`.
2. (*Theorem Q capacity & interior `(b - 6s)`-lane cone fan-in `≤ 2 * (6 * s + 1) * (M.k + 3)^D`*)
   On any common-simulator-trace fibre `S` (`X ∈ S`, `HaltsAt M (List.ofFn X) t`), original cut `B`
   reducing `B`-free causal paths to `≤ D` (`1 ≤ D`), and entry set `J ⊆ Fin (d * d)`, `B` lifts to
   a simulator guard `Γ` (`|Γ| ≤ guardCoefficient M.k s * |B|`) yielding both Paper 18's `(b - 6s)`
   interior-lane storage code / deficit bound and simulator input-cone fan-in
   `≤ 2 * (6 * s + 1) * (M.k + 3)^D` (both raw bits and whole entries, independent of `b` and `d`)
   on every unguarded retained interior lane bit `p ∈ retainedBits J b s`. -/
theorem diagnosis_Paper18AdaptiveOriginalEntryPullback :
    (∀ (M : Transpose.TM) (c δ : ℝ), 0 ≤ c → 0 < δ →
      ∃ s : ℕ, ∃ hs : 0 < s, ∃ d₀ : ℕ, ∀ d ≥ d₀,
        24 * s ≤ Transpose.entryBits d ∧
        ∀ G : Finset (Fin (d * d * Transpose.entryBits d) → Bool),
          (∀ X ∈ G, MergeDepth.TransposesInput M d (Transpose.entryBits d) c X) →
          ((G.filter fun X =>
            ¬ AdaptiveTransfer.TransferEntry.EntryCertificates M hs δ X).card : ℝ) <
            (2 : ℝ) ^ ((1 - δ / 2) * (d * d * Transpose.entryBits d : ℕ))) ∧
    (∀ (M : Transpose.TM) {d b s t D : ℕ}
      (hs : 0 < s), 0 < d → 0 < b → 1 ≤ D →
      ∀ (S : Finset (Fin (d * d * b) → Bool)) {X : Fin (d * d * b) → Bool}, X ∈ S →
      Transpose.Tape.HaltsAt M (List.ofFn X) t →
      (∀ Y ∈ S, MergeDepth.OutputsTranspose M d b Y) →
      (∀ Y ∈ S,
        MergeDepth.trace (TapeStorageRates.Native.machine M hs) (List.ofFn Y) =
          MergeDepth.trace (TapeStorageRates.Native.machine M hs) (List.ofFn X)) →
      ∀ (B : Finset ℕ), (∀ u ∈ B, u < t) →
      (∀ π : List ℕ,
        MergeDepth.IsDepPath (MergeDepth.trace M (List.ofFn X)).work t π →
        BoundedNesting.LinNet.GFree B π → π.length ≤ D) →
      ∀ (J : Finset (Fin (d * d))),
      AdaptiveTransfer.TransferEntry.deficit
        (DirectedRecovery.inducedNeighborhood
          (AdaptiveTransfer.TransferEntry.originalRelation M X t B) J) (b - 6 * s) ≤
        (d * d * b : ℕ) - Real.logb 2 (S.card : ℝ) +
          (MergeDepth.valueWidth (TapeStorageRates.Native.machine M hs) : ℝ) *
            AdaptiveTransfer.TransferCones.guardCoefficient M.k s * B.card ∧
      (∀ e : Fin (d * d),
        (AdaptiveTransfer.TransferEntry.originalRelation M X t B e).card ≤
          b * (M.k + 3) ^ D) ∧
      ∃ (Γ : Finset ℕ) (C : Finset (J → Fin (b - 6 * s) → Bool)),
        Γ.card ≤ AdaptiveTransfer.TransferCones.guardCoefficient M.k s * B.card ∧
        C.Nonempty ∧
        MotionDepthCodes.IsStorageCode
          (DirectedRecovery.inducedNeighborhood
            (AdaptiveTransfer.TransferEntry.originalRelation M X t B) J) C ∧
        S.card ≤
          2 ^ (MergeDepth.valueWidth (TapeStorageRates.Native.machine M hs) * Γ.card +
            (d * d * b - (b - 6 * s) * J.card)) * C.card ∧
        ∀ p ∈ AdaptiveTransfer.TransferEntry.retainedBits J b s,
          let rSim := AdaptiveTransfer.TransferFIFO.simulatorRoot M hs (List.ofFn X) t
            (MergeDepth.tposOf d b p).val
          rSim ∉ Γ →
          let simCone := AdaptiveTransfer.nativeInputCone
            (MergeDepth.trace (TapeStorageRates.Native.machine M hs) (List.ofFn X))
            (d * d * b) (TapeStorageRates.alignedTime s t) Γ rSim
          simCone.card ≤ 2 * (6 * s + 1) * (M.k + 3) ^ D ∧
          (simCone.image AdaptiveTransfer.TransferEntry.entry).card ≤
            2 * (6 * s + 1) * (M.k + 3) ^ D) := by
  refine ⟨fun M c δ hc hδ => AdaptiveTransfer.TransferEntry.uniform_entry_success_tail M hc hδ, ?_⟩
  intro M d b s t D hs hd hb hD S X hX H hcorrect htrace B hB hDepth J
  have hDeficit := AdaptiveTransfer.TransferEntry.native_original_entry_capacity
    hs hd hb S hX H hcorrect htrace B hB J
  have hSumPow3 : ∀ m : ℕ, ∑ h ∈ Finset.range m, (M.k + 1) ^ h ≤ (M.k + 3) ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, pow_succ]
      have h1 : (M.k + 1) ^ m ≤ (M.k + 3) ^ m := Nat.pow_le_pow_left (by omega) m
      have h2 : ∑ h ∈ Finset.range m, (M.k + 1) ^ h ≤ (M.k + 3) ^ m * (M.k + 2) := by
        calc ∑ h ∈ Finset.range m, (M.k + 1) ^ h
            ≤ (M.k + 3) ^ m := ih
          _ ≤ (M.k + 3) ^ m * (M.k + 2) := Nat.le_mul_of_pos_right _ (by omega)
      nlinarith
  have hOrigConeCard : ∀ q : Fin (d * d * b),
      (AdaptiveTransfer.TransferEntry.originalCones M X t B q).card ≤ (M.k + 3) ^ D := by
    intro q
    exact (card_depCone_le_pow _ _ B _ hD hDepth).trans (hSumPow3 D)
  have hOrigRelCard : ∀ e : Fin (d * d),
      (AdaptiveTransfer.TransferEntry.originalRelation M X t B e).card ≤ b * (M.k + 3) ^ D := by
    classical
    intro e
    let laneEntries (l : Fin b) : Finset (Fin (d * d)) :=
      (AdaptiveTransfer.TransferEntry.originalCones M X t B
        (AdaptiveTransfer.TransferEntry.bit e l)).image AdaptiveTransfer.TransferEntry.entry
    have hSub : AdaptiveTransfer.TransferEntry.originalRelation M X t B e ⊆
        Finset.univ.biUnion laneEntries := by
      intro f hf
      obtain ⟨l, p, hp, rfl⟩ := AdaptiveTransfer.TransferEntry.mem_entryQuotient.mp hf
      exact Finset.mem_biUnion.mpr ⟨l, Finset.mem_univ l, Finset.mem_image.mpr ⟨p, hp, rfl⟩⟩
    calc (AdaptiveTransfer.TransferEntry.originalRelation M X t B e).card
        ≤ (Finset.univ.biUnion laneEntries).card := Finset.card_le_card hSub
      _ ≤ ∑ l : Fin b, (laneEntries l).card := Finset.card_biUnion_le
      _ ≤ ∑ l : Fin b, (AdaptiveTransfer.TransferEntry.originalCones M X t B
            (AdaptiveTransfer.TransferEntry.bit e l)).card :=
          Finset.sum_le_sum fun l _ => Finset.card_image_le
      _ ≤ ∑ _l : Fin b, (M.k + 3) ^ D := Finset.sum_le_sum fun l _ => hOrigConeCard _
      _ = b * (M.k + 3) ^ D := by simp
  refine ⟨hDeficit, hOrigRelCard, ?_⟩
  have hcount := AdaptiveTransfer.TransferCorrect.correct_source_count H (hcorrect X hX)
  have ht1 : 1 ≤ t := by
    have hp := Nat.mul_pos (Nat.mul_pos hd hd) hb
    have hh := AdaptiveTransfer.TransferFIFO.outputCount_add_le M (List.ofFn X) 0 t
    simp only [Nat.zero_add] at hh
    have hz : AdaptiveTransfer.TransferFIFO.outputCount M (List.ofFn X) 0 = 0 := rfl
    rw [hz, hcount, Nat.zero_add] at hh
    omega
  obtain ⟨Γ, hΓcard, _, hcone⟩ := AdaptiveTransfer.TransferCones.native_cone_transport_interior
    (L := d * d * b) (P := d * d * b) hs ht1 H hcount.ge B hB
  have hSubCone : ∀ p ∈ AdaptiveTransfer.TransferEntry.retainedBits J b s,
      AdaptiveTransfer.TransferFIFO.simulatorRoot M hs (List.ofFn X) t
        (MergeDepth.tposOf d b p).val ∉ Γ →
      AdaptiveTransfer.nativeInputCone
        (MergeDepth.trace (TapeStorageRates.Native.machine M hs) (List.ofFn X))
        (d * d * b) (TapeStorageRates.alignedTime s t) Γ
        (AdaptiveTransfer.TransferFIFO.simulatorRoot M hs (List.ofFn X) t
          (MergeDepth.tposOf d b p).val) ⊆
      AdaptiveTransfer.inputDilation
        (AdaptiveTransfer.TransferEntry.originalCones M X t B
          (AdaptiveTransfer.TransferEntry.futureTarget s p)) (3 * s) ∪
      AdaptiveTransfer.inputBoundary (d * d * b) (3 * s) := by
    intro p hp hroot
    have hfuture :=
      (AdaptiveTransfer.TransferEntry.interior_output_lookahead
        (AdaptiveTransfer.TransferEntry.mem_retainedBits.mp hp).2.2).1
    have hh := hcone (MergeDepth.tposOf d b p) hfuture hroot
    simpa only [AdaptiveTransfer.TransferEntry.originalCones,
      AdaptiveTransfer.TransferEntry.futureTarget, dite_eq_left hfuture,
      MergeDepth.tposOf_tposOf, AdaptiveTransfer.TransferRoots.simulatorOrdinal] using hh
  obtain ⟨C, hCne, hCstor, hCcard⟩ := AdaptiveTransfer.TransferEntry.exists_large_entry_code
    (M := TapeStorageRates.Native.machine M hs) (T := TapeStorageRates.alignedTime s t)
    (τ := MergeDepth.trace (TapeStorageRates.Native.machine M hs) (List.ofFn X)) S J Γ
    (fun p => AdaptiveTransfer.TransferFIFO.simulatorRoot M hs (List.ofFn X) t
      (MergeDepth.tposOf d b p).val)
    (AdaptiveTransfer.TransferEntry.originalCones M X t B)
    (AdaptiveTransfer.TransferEntry.futureTarget s)
    (fun p _ => (AdaptiveTransfer.TransferCorrect.correct_simulator_root hs H
      (hcorrect X hX) p).1)
    (fun Y hY u _ => congrFun (htrace Y hY) u)
    (fun Y hY p _ => AdaptiveTransfer.TransferCorrect.common_simulator_root hs H
      (hcorrect Y hY) (htrace Y hY) p)
    (fun p hp => AdaptiveTransfer.TransferEntry.entry_futureTarget
      (AdaptiveTransfer.TransferEntry.mem_retainedBits.mp hp).2.2)
    hSubCone ⟨X, hX⟩
  refine ⟨Γ, C, hΓcard, hCne, hCstor, hCcard, fun p hp hroot => ?_⟩
  have hSub := hSubCone p hp hroot
  have hPow1 : 1 ≤ (M.k + 3) ^ D := Nat.one_le_pow D (M.k + 3) (by omega)
  have hRawCard :
      (AdaptiveTransfer.nativeInputCone
        (MergeDepth.trace (TapeStorageRates.Native.machine M hs) (List.ofFn X))
        (d * d * b) (TapeStorageRates.alignedTime s t) Γ
        (AdaptiveTransfer.TransferFIFO.simulatorRoot M hs (List.ofFn X) t
          (MergeDepth.tposOf d b p).val)).card ≤
      2 * (6 * s + 1) * (M.k + 3) ^ D := by
    calc _ ≤ (AdaptiveTransfer.inputDilation
              (AdaptiveTransfer.TransferEntry.originalCones M X t B
                (AdaptiveTransfer.TransferEntry.futureTarget s p)) (3 * s) ∪
            AdaptiveTransfer.inputBoundary (d * d * b) (3 * s)).card := Finset.card_le_card hSub
      _ ≤ (AdaptiveTransfer.inputDilation
            (AdaptiveTransfer.TransferEntry.originalCones M X t B
              (AdaptiveTransfer.TransferEntry.futureTarget s p)) (3 * s)).card +
          (AdaptiveTransfer.inputBoundary (d * d * b) (3 * s)).card := Finset.card_union_le _ _
      _ ≤ (2 * (3 * s) + 1) * (AdaptiveTransfer.TransferEntry.originalCones M X t B
            (AdaptiveTransfer.TransferEntry.futureTarget s p)).card + 2 * (3 * s) :=
          Nat.add_le_add (card_inputDilation_le _ _) (card_inputBoundary_le _ _)
      _ ≤ (6 * s + 1) * (M.k + 3) ^ D + 6 * s := by
          have hc := hOrigConeCard (AdaptiveTransfer.TransferEntry.futureTarget s p)
          nlinarith
      _ ≤ 2 * (6 * s + 1) * (M.k + 3) ^ D := by nlinarith
  exact ⟨hRawCard, Finset.card_image_le.trans hRawCard⟩

end Diagnosis1Consequences

/-! ### 2. Diagnoses 2, 3, 4, 5, 6 Consequences -/

section Diagnosis2To4Consequences

/-- **Diagnosis 2 Asymptotic Rate Limit (`README.md` §I.1 Line 7a).**
For every `C_code : ℝ` and `0 < α`, `1 - C_code * (Delta : ℝ) ^ (-α) → 1` as `Delta → ∞`. -/
theorem diagnosis2_HighRateTendstoOne (C_code α : ℝ) (hα : 0 < α) :
    Filter.Tendsto (fun Delta : ℕ => 1 - C_code * (Delta : ℝ) ^ (-α))
      Filter.atTop (nhds 1) := by
  have hpow : Filter.Tendsto (fun Delta : ℕ => (Delta : ℝ) ^ (-α)) Filter.atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hα).comp tendsto_natCast_atTop_atTop
  have hsub := (tendsto_const_nhds (x := (1 : ℝ))).sub (hpow.const_mul C_code)
  simpa using hsub

/-- **Diagnosis 3 Multi-Bit `w`-Bit Block-Edge Shift Coding-Gain Barrier (`README.md` §I.1 Line 7b).**
Specializing `diagnosis_ShiftAndRotationCodingGainBarrier` to `s_blk` multi-bit block edges each
carrying `w ≥ 1` bits (total Boolean wire count `s = w * s_blk`), any `n`-bit programmable barrel
shift circuit (`n ≥ N₀`) induces a max-degree-`4` complete-exchange graph on
`V ≤ C_net * (w * s_blk + n)` vertices forcing coding-to-routing gain
`c_gain * n * log₂ n / (w * s_blk + n) ≤ (1 / n) / rateRoute` under unit-capacity edge duality
(and `c_gain * n * log₂ n / (w * (w * s_blk + n)) ≤ (1 / n) / rateRoute` when each undirected
graph edge carries `w`-bit capacity `rateRoute * ∑ distBound ≤ w * m_edges`). -/
theorem diagnosis3_MultiBitBlockEdgeShiftBarrier :
    ∃ (c_dist c_gain : ℝ) (C_net N₀ : ℕ),
      0 < c_dist ∧ 0 < c_gain ∧ 1 ≤ C_net ∧ 2 ≤ N₀ ∧
      ∀ (n w s_blk : ℕ) [NeZero n],
        N₀ ≤ n → 1 ≤ w →
        HasBarrelShiftCircuit n (w * s_blk) →
        ∃ (V : ℕ) (adj : Fin V → Finset (Fin V))
          (src sink : Fin n → Fin V)
          (distBound : Fin n → Fin n → ℕ),
          1 ≤ V ∧ V ≤ C_net * (w * s_blk + n) ∧
          (∀ u : Fin V, (adj u).card ≤ 4) ∧
          HasCausalCompleteExchangeCode adj src sink ∧
          c_dist * ((n : ℝ) ^ 2) * (Real.log (n : ℝ) / Real.log 2) ≤
            (∑ i : Fin n, ∑ j : Fin n, (distBound i j : ℝ)) ∧
          (∀ rateRoute : ℝ, 0 < rateRoute →
            rateRoute * (∑ i : Fin n, ∑ j : Fin n, (distBound i j : ℝ)) ≤
              ((∑ u : Fin V, (adj u).card : ℕ) : ℝ) / 2 →
            c_gain * (n : ℝ) * (Real.log (n : ℝ) / Real.log 2) /
              ((w : ℝ) * (s_blk : ℝ) + (n : ℝ)) ≤ (1 / (n : ℝ)) / rateRoute) ∧
          (∀ rateRoute : ℝ, 0 < rateRoute →
            rateRoute * (∑ i : Fin n, ∑ j : Fin n, (distBound i j : ℝ)) ≤
              (w : ℝ) * (((∑ u : Fin V, (adj u).card : ℕ) : ℝ) / 2) →
            c_gain * (n : ℝ) * (Real.log (n : ℝ) / Real.log 2) /
              ((w : ℝ) * ((w : ℝ) * (s_blk : ℝ) + (n : ℝ))) ≤ (1 / (n : ℝ)) / rateRoute) := by
  obtain ⟨c_dist, c_gain, C_net, N₀, hcd, hcg, hCnet, hN₀, hMain⟩ :=
    diagnosis_ShiftAndRotationCodingGainBarrier.1
  refine ⟨c_dist, c_gain, C_net, N₀, hcd, hcg, hCnet, hN₀, ?_⟩
  intro n w s_blk _ hn hw hShift
  obtain ⟨V, adj, src, sink, distBound, hV1, hVle, _, _, hdeg, hExch, _, hDistSum, hGain⟩ :=
    hMain n (w * s_blk) hn hShift
  refine ⟨V, adj, src, sink, distBound, hV1, hVle, hdeg, hExch, hDistSum, ?_, ?_⟩
  · intro rateRoute hrPos hDual
    have hg := hGain rateRoute hrPos hDual
    simpa [Nat.cast_mul] using hg
  · intro rateRoute hrPos hDualW
    have hwPos : (0 : ℝ) < (w : ℝ) := by exact_mod_cast hw
    have hrDivPos : 0 < rateRoute / (w : ℝ) := div_pos hrPos hwPos
    have hDual1 : (rateRoute / (w : ℝ)) * (∑ i : Fin n, ∑ j : Fin n, (distBound i j : ℝ)) ≤
        ((∑ u : Fin V, (adj u).card : ℕ) : ℝ) / 2 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hwPos]
      linarith
    have hg := hGain (rateRoute / (w : ℝ)) hrDivPos hDual1
    have hcast : ((w * s_blk : ℕ) : ℝ) + (n : ℝ) = (w : ℝ) * (s_blk : ℝ) + (n : ℝ) := by
      push_cast; ring
    rw [hcast, div_div_eq_mul_div] at hg
    have hmul := div_le_div_of_nonneg_right hg hwPos.le
    calc c_gain * (n : ℝ) * (Real.log (n : ℝ) / Real.log 2) /
            ((w : ℝ) * ((w : ℝ) * (s_blk : ℝ) + (n : ℝ)))
        = (c_gain * (n : ℝ) * (Real.log (n : ℝ) / Real.log 2) /
            ((w : ℝ) * (s_blk : ℝ) + (n : ℝ))) / (w : ℝ) := by
          rw [mul_comm (w : ℝ) ((w : ℝ) * (s_blk : ℝ) + (n : ℝ)), ← div_div]
      _ ≤ ((1 / (n : ℝ) * (w : ℝ)) / rateRoute) / (w : ℝ) := hmul
      _ = (1 / (n : ℝ)) / rateRoute := by
          have hwNe : (w : ℝ) ≠ 0 := hwPos.ne'
          field_simp

/-- Explicit integer ceiling `⌈√(2 M)⌉` for `M`-class difference-cover shared-decoder bounds. -/
def ceilSqrtTwoMul (M : ℕ) : ℕ :=
  if M = 0 then 0 else Nat.sqrt (2 * M - 1) + 1

private theorem finrank_leftComponent_eq_componentCount (F : Type*) [Field F]
    {d : ℕ} [NeZero d] {κ : Type*} (p : ZMod d → κ) (Δ : Finset (ZMod d)) :
    finrank F (leftComponentSubmodule F p Δ) = SharedDecoders.componentCount p Δ := by
  let e : leftComponentSubmodule F p Δ ≃ₗ[F] (SharedDecoders.LinkComponent p Δ → F) :=
    { toFun := fun u => Quotient.lift u.1 (fun c c' hrel => u.2 c c' hrel)
      invFun := fun f =>
        ⟨fun c => f (Quotient.mk _ c),
         fun c c' hrel => congrArg f (Quotient.sound hrel)⟩
      map_add' := fun _ _ => funext fun q => Quotient.inductionOn q fun _ => rfl
      map_smul' := fun _ _ => funext fun q => Quotient.inductionOn q fun _ => rfl
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun f => funext fun q => Quotient.inductionOn q fun _ => rfl }
  rw [e.finrank_eq, Module.finrank_fintype_fun_eq_card]
  rfl

/-- **Diagnosis 4 Explicit `⌈√(2 M)⌉` Rate Bound & `5/8` Mask-Certificate Bridge
(`README.md` §I.2 Line 10 & §II.3.1 Line 99).**
1. For `1 ≤ M` and `2 * M ≤ d`, `ceilSqrtTwoMul M` satisfies `1 ≤ ceilSqrtTwoMul M`,
   `2 * M ≤ (ceilSqrtTwoMul M)^2`, `(ceilSqrtTwoMul M - 1)^2 < 2 * M`, and every `M`-class linear
   shared code `C ≤ State d A` (`1 ≤ finrank F A`) has rate
   `finrank F C / (finrank F A * d^2) ≤ 1 - 1 / (4 * ceilSqrtTwoMul M)`.
2. For every `p : ZMod d → Bool` and `s : ZMod d`, `finrank F (leftComponentSubmodule F p {0, s}) =
   SharedDecoders.componentCount p {0, s}` and `finrank F (shiftSetCovarianceSubmodule F p {0, s} A) =
   SharedDecoders.componentCount p {0, s} * (d * finrank F A)`; whenever
   `(1 / 4 - η / 2) * d ≤ componentCount p {0, s}` (which holds with margin `(1 / 2 - η) * d` across
   all `s` under `ChangeGood η p` outside probability `(d - 1) exp(-η^2 d / 2)`), the generic
   tensor-product subspaces `C₀ = V₀ ⊗ ⊤`, `Cₛ = Vₛ ⊗ ⊤` from `maskFloor_GenericSubspaceRealization`
   satisfy `C₀ ⊓ Cₛ = shiftSetCovarianceSubmodule F p {0, s} A` and rate
   `5 / 8 - η / 4 - 1 / (2 * d) ≤ finrank F C₀ / (finrank F A * d^2)`. -/
theorem diagnosis4_ExplicitSquareCoverAndMaskCertificateBridge :
    (∀ (M : ℕ), 1 ≤ M →
      1 ≤ ceilSqrtTwoMul M ∧
      2 * M ≤ (ceilSqrtTwoMul M) ^ 2 ∧
      (ceilSqrtTwoMul M - 1) ^ 2 < 2 * M) ∧
    (∀ (F A : Type*) [Field F] [AddCommGroup A] [Module F A] [FiniteDimensional F A]
      (d M : ℕ) [NeZero d] (p : ZMod d → Fin M) (C : Submodule F (State d A)),
      IsSharedCode F p C → 1 ≤ M → 2 * M ≤ d → 1 ≤ finrank F A →
      (finrank F C : ℝ) / ((finrank F A : ℝ) * (d : ℝ) ^ 2) ≤
        1 - 1 / (4 * (ceilSqrtTwoMul M : ℝ))) ∧
    (∀ (F A : Type*) [Field F] [AddCommGroup A] [Module F A] [FiniteDimensional F A]
      (d : ℕ) [NeZero d] (p : ZMod d → Bool) (s : ZMod d),
      finrank F (leftComponentSubmodule F p {0, s}) =
        SharedDecoders.componentCount p {0, s} ∧
      finrank F (shiftSetCovarianceSubmodule F p {0, s} A) =
        SharedDecoders.componentCount p {0, s} * (d * finrank F A) ∧
      ∀ η : ℝ, 1 ≤ finrank F A →
        (1 / 4 - η / 2) * (d : ℝ) ≤ (SharedDecoders.componentCount p {0, s} : ℝ) →
        ∃ (V₀ Vₛ : Submodule F (ZMod d → F)) (C₀ Cₛ : Submodule F (State d A)),
          C₀ = Submodule.map (antiDiagTensorEquiv F d A).toLinearMap
            (Submodule.map₂ (TensorProduct.mk F (ZMod d → F) (ZMod d → A)) V₀ ⊤) ∧
          Cₛ = Submodule.map (antiDiagTensorEquiv F d A).toLinearMap
            (Submodule.map₂ (TensorProduct.mk F (ZMod d → F) (ZMod d → A)) Vₛ ⊤) ∧
          C₀ ⊓ Cₛ = shiftSetCovarianceSubmodule F p {0, s} A ∧
          finrank F C₀ = finrank F Cₛ ∧
          5 / 8 - η / 4 - 1 / (2 * (d : ℝ)) ≤
            (finrank F C₀ : ℝ) / ((finrank F A : ℝ) * (d : ℝ) ^ 2)) ∧
    (∀ (d : ℕ) [NeZero d] (η : ℝ), 0 ≤ η →
      SharedDecoders.CapacityMaskProbability.prob (fun p : ZMod d → Bool =>
        ¬ ∀ s : ZMod d, (1 / 2 - η) * (d : ℝ) ≤
          (SharedDecoders.componentCount p {0, s} : ℝ)) ≤
        ((d : ℝ) - 1) * Real.exp (-η ^ 2 * (d : ℝ) / 2)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro M hM1
    have hM0 : M ≠ 0 := by omega
    simp only [ceilSqrtTwoMul, hM0, ↓reduceIte]
    have hle := Nat.sqrt_le (2 * M - 1)
    have hlt := Nat.lt_succ_sqrt (2 * M - 1)
    simp only [Nat.succ_eq_add_one] at hlt
    refine ⟨by omega, ?_, ?_⟩
    · rw [sq]; omega
    · rw [Nat.add_sub_cancel, sq]; omega
  · intro F A _ _ _ _ d M _ p C hShared hM1 h2Md hb1
    have hM0 : M ≠ 0 := by omega
    have ht1 : 1 ≤ ceilSqrtTwoMul M := by simp [ceilSqrtTwoMul, hM0]
    have htSq : 2 * M ≤ ceilSqrtTwoMul M * ceilSqrtTwoMul M := by
      simp only [ceilSqrtTwoMul, hM0, ↓reduceIte]
      have hlt := Nat.lt_succ_sqrt (2 * M - 1)
      simp only [Nat.succ_eq_add_one] at hlt
      omega
    have hNat := diagnosis_LinearSharedDecoderBoundsAndMaskFloors.{0, 0, _, _}.2.1
      F A d M (ceilSqrtTwoMul M) p C hShared ht1 h2Md htSq
    have hReal : 4 * (ceilSqrtTwoMul M : ℝ) * (finrank F C : ℝ) +
        (d : ℝ) ^ 2 * (finrank F A : ℝ) ≤
        4 * (ceilSqrtTwoMul M : ℝ) * ((d : ℝ) ^ 2 * (finrank F A : ℝ)) := by
      have hr : ((4 * ceilSqrtTwoMul M * finrank F C + d * d * finrank F A : ℕ) : ℝ) ≤
          ((4 * ceilSqrtTwoMul M * (d * d * finrank F A) : ℕ) : ℝ) := Nat.cast_le.mpr hNat
      push_cast at hr
      nlinarith
    have hdPos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast NeZero.pos d
    have hbPos : (0 : ℝ) < (finrank F A : ℝ) := by exact_mod_cast hb1
    have htPos : (0 : ℝ) < (ceilSqrtTwoMul M : ℝ) := by exact_mod_cast ht1
    have hDenPos : (0 : ℝ) < (finrank F A : ℝ) * (d : ℝ) ^ 2 := by positivity
    rw [div_le_iff₀ hDenPos]
    have h4tNe : 4 * (ceilSqrtTwoMul M : ℝ) ≠ 0 := by positivity
    apply le_of_mul_le_mul_left _ (show (0 : ℝ) < 4 * (ceilSqrtTwoMul M : ℝ) by positivity)
    calc 4 * (ceilSqrtTwoMul M : ℝ) * (finrank F C : ℝ)
        ≤ 4 * (ceilSqrtTwoMul M : ℝ) * ((d : ℝ) ^ 2 * (finrank F A : ℝ)) -
            (d : ℝ) ^ 2 * (finrank F A : ℝ) := by linarith
      _ = 4 * (ceilSqrtTwoMul M : ℝ) *
            ((1 - 1 / (4 * (ceilSqrtTwoMul M : ℝ))) * ((finrank F A : ℝ) * (d : ℝ) ^ 2)) := by
          field_simp
  · intro F A _ _ _ _ d _ p s
    have hLeft := finrank_leftComponent_eq_componentCount F p {0, s}
    have hCov := (shiftSetCovariance_tensor_finrank F p {0, s} A).2
    rw [hLeft] at hCov
    refine ⟨hLeft, hCov, fun η hb1 hComp => ?_⟩
    obtain ⟨V₀, Vₛ, C₀, Cₛ, hC₀, hCₛ, hInf, hEqRank, hLowerNat⟩ :=
      (maskFloor_GenericSubspaceRealization.{_, _, _, 0, 0}.1 F d Bool A p s).2
    refine ⟨V₀, Vₛ, C₀, Cₛ, hC₀, hCₛ, hInf, hEqRank, ?_⟩
    rw [hCov] at hLowerNat
    have hReal : (d : ℝ) ^ 2 * (finrank F A : ℝ) +
        (SharedDecoders.componentCount p {0, s} : ℝ) * ((d : ℝ) * (finrank F A : ℝ)) ≤
        2 * (finrank F C₀ : ℝ) + (d : ℝ) * (finrank F A : ℝ) := by
      exact_mod_cast hLowerNat
    have hdPos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast NeZero.pos d
    have hbPos : (0 : ℝ) < (finrank F A : ℝ) := by exact_mod_cast hb1
    have hDenPos : (0 : ℝ) < (finrank F A : ℝ) * (d : ℝ) ^ 2 := by positivity
    rw [le_div_iff₀ hDenPos]
    have hCompMul : (1 / 4 - η / 2) * (d : ℝ) * ((d : ℝ) * (finrank F A : ℝ)) ≤
        (SharedDecoders.componentCount p {0, s} : ℝ) * ((d : ℝ) * (finrank F A : ℝ)) :=
      mul_le_mul_of_nonneg_right hComp (by positivity)
    have hExpand : (5 / 8 - η / 4 - 1 / (2 * (d : ℝ))) * ((finrank F A : ℝ) * (d : ℝ) ^ 2) =
        ((d : ℝ) ^ 2 * (finrank F A : ℝ) +
          (1 / 4 - η / 2) * (d : ℝ) * ((d : ℝ) * (finrank F A : ℝ)) -
          (d : ℝ) * (finrank F A : ℝ)) / 2 := by
      have hdNe : (d : ℝ) ≠ 0 := hdPos.ne'
      field_simp; ring
    rw [hExpand]
    linarith
  · intro d _ η hη
    apply (SharedDecoders.CapacityMaskProbability.prob_mono ?_).trans
      (SharedDecoders.CapacityMaskProbability.change_bad_probability η hη)
    intro p hBad hGood
    apply hBad
    intro s
    by_cases hs : s = 0
    · subst hs
      have h0 : ({0, 0} : Finset (ZMod d)) = {0} := by simp
      rw [h0, SharedDecoders.componentCount_zero]
      nlinarith [mul_nonneg hη (Nat.cast_nonneg (α := ℝ) d),
        show (0 : ℝ) ≤ (d : ℝ) from Nat.cast_nonneg d]
    · have hchg : (1 / 2 - η) * (d : ℝ) ≤ (SharedDecoders.CapacityRuns.changeCount p s : ℝ) :=
        hGood s hs
      have hle : SharedDecoders.CapacityRuns.changeCount p s ≤
          SharedDecoders.componentCount p (SharedDecoders.extendShifts {0} s) :=
        SharedDecoders.CapacityMask.changeCount_le_first_components p s
      have hSetEq : SharedDecoders.extendShifts ({0} : Finset (ZMod d)) s = {0, s} := by
        ext x
        simp [SharedDecoders.extendShifts, or_comm]
      rw [hSetEq] at hle
      exact hchg.trans (Nat.cast_le.mpr hle)

end Diagnosis2To4Consequences

section Diagnosis5And6Consequences

/-- Combinatorial inverse van der Waerden scale `invVdW M₁ M₂ d`: the largest `k ≤ d` such that
every `M₁`-coloring of `Fin (d / 2)` contains a monochromatic `((2 * M₂ + 1) * k - 1)`-term
arithmetic progression. -/
noncomputable def invVdW (M₁ M₂ d : ℕ) : ℕ := by
  classical
  let S : Finset ℕ := (Finset.range (d + 1)).filter fun k =>
    ∀ C : Fin (d / 2) → Fin M₁,
      ∃ a s : ℕ, 0 < s ∧
        ∀ j < (2 * M₂ + 1) * k - 1,
          ∃ hj : a + s * j < d / 2,
            ∃ ha : a < d / 2,
              C ⟨a + s * j, hj⟩ = C ⟨a, ha⟩
  have h0 : 0 ∈ S := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.succ_pos d), fun _ => ⟨0, 1, by omega, ?_⟩⟩
    intro j hj
    simp at hj
  exact S.max' ⟨0, h0⟩

/--Modular non-overlapping monochromatic progression of length `ℓ` in `p : ZMod d → Fin M₁`. -/
def HasInjectiveMonoModAP {d M₁ : ℕ} (p : ZMod d → Fin M₁) (ℓ : ℕ) : Prop :=
  ∃ (c₀ s : ZMod d), s ≠ 0 ∧
    Function.Injective (fun j : Fin ℓ => c₀ + (j.val : ZMod d) * s) ∧
    ∀ j : Fin ℓ, p (c₀ + (j.val : ZMod d) * s) = p c₀

/-- **Diagnosis 5 Inverse van der Waerden Divergence & Rank Lower Bound
(`README.md` §I.2 Line 13 & §II.2 Line 53).**
1. For every `1 ≤ M₁` and `1 ≤ M₂`, `invVdW M₁ M₂ d → ∞` as `d → ∞`.
2. Over every field `F` with `(d : F) ≠ 0` (`d ≥ 2`, `b ≥ 1`), any two `ClassUniform` linear stages
   `K₁, K₂` satisfy `(invVdW M₁ M₂ d : ℝ) / 4 ≤ finrank F (range (swapLinear F - K₂.comp K₁)) / (b * d)`. -/
theorem diagnosis5_CombinatorialInvVdWTendstoAndRankBound :
    (∀ (M₁ M₂ : ℕ), 1 ≤ M₁ → 1 ≤ M₂ →
      Filter.Tendsto (invVdW M₁ M₂) Filter.atTop Filter.atTop) ∧
    (∀ (F : Type*) [Field F] (d b M₁ M₂ : ℕ) [NeZero d]
      (p₁ : ZMod d → Fin M₁) (p₂ : ZMod d → Fin M₂)
      (K₁ K₂ : State d (Fin b → F) →ₗ[F] State d (Fin b → F)),
      2 ≤ d → 1 ≤ b → (d : F) ≠ 0 →
      ClassUniform p₁ K₁ → ClassUniform p₂ K₂ →
      (invVdW M₁ M₂ d : ℝ) / 4 ≤
        (finrank F (LinearMap.range (swapLinear F (d := d) (A := Fin b → F) - K₂.comp K₁)) : ℝ) /
          ((b : ℝ) * (d : ℝ))) := by
  classical
  constructor
  · intro M₁ M₂ hM₁ hM₂
    rw [Filter.tendsto_atTop_atTop]
    intro K
    let K' := max K 1
    have hK'1 : 1 ≤ K' := le_max_right K 1
    let ℓ := (2 * M₂ + 1) * K' - 1
    have hℓ : 0 < ℓ := by
      have h2 : 2 ≤ (2 * M₂ + 1) * K' := by nlinarith
      omega
    obtain ⟨N, _, hRamsey⟩ := SharedDecoders.exists_progression_bound (Fin M₁) ℓ hℓ
    refine ⟨max K' (2 * N), fun d hd => ?_⟩
    have hK'd : K' ≤ d := (le_max_left K' (2 * N)).trans hd
    have h2Nd : 2 * N ≤ d := (le_max_right K' (2 * N)).trans hd
    have hNd2 : N ≤ d / 2 := by omega
    let S : Finset ℕ := (Finset.range (d + 1)).filter fun k =>
      ∀ C : Fin (d / 2) → Fin M₁,
        ∃ a s : ℕ, 0 < s ∧
          ∀ j < (2 * M₂ + 1) * k - 1,
            ∃ hj : a + s * j < d / 2,
              ∃ ha : a < d / 2,
                C ⟨a + s * j, hj⟩ = C ⟨a, ha⟩
    have hK'mem : K' ∈ S := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), fun C₀ => ?_⟩
      let C (x : ℕ) : Fin M₁ := if hx : x < d / 2 then C₀ ⟨x, hx⟩ else ⟨0, hM₁⟩
      obtain ⟨a, s, hs, hAP⟩ := hRamsey C
      have haLt : a < d / 2 := by
        have h0 := (hAP 0 hℓ).1
        omega
      refine ⟨a, s, hs, fun j hj => ?_⟩
      obtain ⟨hjN, hEq⟩ := hAP j hj
      have hjLt : a + s * j < d / 2 := lt_of_lt_of_le hjN hNd2
      refine ⟨hjLt, haLt, ?_⟩
      dsimp only [C] at hEq
      simp only [hjLt, haLt, ↓reduceDIte] at hEq
      exact hEq
    have h0 : 0 ∈ S := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.succ_pos d), fun _ => ⟨0, 1, by omega, ?_⟩⟩
      intro j hj; simp at hj
    have hMax : K' ≤ invVdW M₁ M₂ d := Finset.le_max' S K' hK'mem
    exact (le_max_left K 1).trans hMax
  · intro F _ d b M₁ M₂ _ p₁ p₂ K₁ K₂ hd2 hb1 hdF hK₁ hK₂
    let k := invVdW M₁ M₂ d
    by_cases hk0 : k = 0
    · change (k : ℝ) / 4 ≤ _
      rw [hk0]
      simp only [Nat.cast_zero, zero_div]
      positivity
    · have hkPos : 0 < k := Nat.pos_of_ne_zero hk0
      let S : Finset ℕ := (Finset.range (d + 1)).filter fun m =>
        ∀ C : Fin (d / 2) → Fin M₁,
          ∃ a s : ℕ, 0 < s ∧
            ∀ j < (2 * M₂ + 1) * m - 1,
              ∃ hj : a + s * j < d / 2,
                ∃ ha : a < d / 2,
                  C ⟨a + s * j, hj⟩ = C ⟨a, ha⟩
      have h0 : 0 ∈ S := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.succ_pos d), fun _ => ⟨0, 1, by omega, ?_⟩⟩
        intro j hj; simp at hj
      have hkMem : k ∈ S := Finset.max'_mem S ⟨0, h0⟩
      have hkProp := (Finset.mem_filter.mp hkMem).2
      have hRamsey : ∀ C : ℕ → Fin M₁, ∃ a s : ℕ, 0 < s ∧
          ∀ j < (2 * Fintype.card (Fin M₂) + 1) * k - 1,
            a + s * j < d / 2 ∧ C (a + s * j) = C a := by
        intro C
        obtain ⟨a, s, hs, hAP⟩ := hkProp (fun x => C x.val)
        refine ⟨a, s, hs, fun j hj => ?_⟩
        rw [Fintype.card_fin] at hj
        obtain ⟨hjLt, _, hEq⟩ := hAP j hj
        exact ⟨hjLt, hEq⟩
      have hRank2 := SharedDecoders.twoHop_rank_interval_any_field
        hdF p₁ p₂ K₁ K₂ hK₁ hK₂ hkPos (d / 2) (Nat.div_le_self d 2) hRamsey
      have hTwice : d ≤ 2 * (d - d / 2 + 1) := by omega
      have hMul : b * k * d ≤ 2 * (b * k * (d - d / 2 + 1)) := by
        calc b * k * d ≤ b * k * (2 * (d - d / 2 + 1)) := Nat.mul_le_mul_left (b * k) hTwice
          _ = 2 * (b * k * (d - d / 2 + 1)) := by ring
      have hRank4 : b * k * d ≤
          4 * finrank F (LinearMap.range (swapLinear F (d := d) (A := Fin b → F) - K₂.comp K₁)) :=
        hMul.trans (by omega)
      have hReal : (b : ℝ) * (k : ℝ) * (d : ℝ) ≤
          4 * (finrank F (LinearMap.range (swapLinear F (d := d) (A := Fin b → F) - K₂.comp K₁)) : ℝ) := by
        exact_mod_cast hRank4
      have hbdPos : (0 : ℝ) < (b : ℝ) * (d : ℝ) := by
        have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb1
        have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
        positivity
      rw [le_div_iff₀ hbdPos]
      change (k : ℝ) / 4 * ((b : ℝ) * (d : ℝ)) ≤ _
      linarith

/-- **Diagnosis 6 Modular Behrend `ThreeAPFreeMod` Sets & Modular `ZMod d` Random Progression Bound
(`README.md` §II.2 Line 55).**
1. (*Modular Behrend*) There exist `C_B > 0` and `D₀` such that every `d ≥ D₀` (`[NeZero d]`) admits
   `J : Finset (ZMod d)` satisfying `ThreeAPFreeMod J` and `d * exp(-C_B * √(log d)) ≤ J.card`.
2. (*Modular `ZMod d` random `M₁`-colorings*) For every `M₁ ≥ 2`, `d ≥ 1` (`[NeZero d]`), and `ℓ ≥ 1`,
   the fraction of colorings `p : ZMod d → Fin M₁` admitting an injective monochromatic modular
   progression `{c₀ + j * s : j < ℓ}` (`s ≠ 0`) is at most `d * (d - 1) * (1 / M₁)^(ℓ - 1)` (which
   automatically covers **every** modular progression `{c₀ + j * s : j < ℓ}` with `s ≠ 0` and
   `ℓ ≤ d` whenever `Nat.Prime d`), and for `ℓ ≥ C_R * log d` (`d ≥ 2`), this fraction is `≤ 1 / d → 0`. -/
theorem diagnosis6_ModularBehrendAndRandomZModProgression :
    (∃ (C_B : ℝ) (D₀ : ℕ), 0 < C_B ∧ 2 ≤ D₀ ∧
      ∀ (d : ℕ) [NeZero d], D₀ ≤ d →
        ∃ J : Finset (ZMod d),
          ThreeAPFreeMod J ∧
          (d : ℝ) * Real.exp (-C_B * Real.sqrt (Real.log (d : ℝ))) ≤ (J.card : ℝ)) ∧
    (∀ (M₁ : ℕ), 2 ≤ M₁ →
      (∀ (d ℓ : ℕ) [NeZero d], 1 ≤ ℓ →
        ((Finset.univ.filter fun p : ZMod d → Fin M₁ => HasInjectiveMonoModAP p ℓ).card : ℝ) /
          (Fintype.card (ZMod d → Fin M₁) : ℝ) ≤
          (d : ℝ) * ((d : ℝ) - 1) * ((1 / (M₁ : ℝ)) ^ (ℓ - 1))) ∧
      (∀ (d ℓ : ℕ) [NeZero d], Nat.Prime d → 1 ≤ ℓ → ℓ ≤ d →
        ((Finset.univ.filter fun p : ZMod d → Fin M₁ =>
          ∃ (c₀ s : ZMod d), s ≠ 0 ∧ ∀ j : Fin ℓ, p (c₀ + (j.val : ZMod d) * s) = p c₀).card : ℝ) /
          (Fintype.card (ZMod d → Fin M₁) : ℝ) ≤
          (d : ℝ) * ((d : ℝ) - 1) * ((1 / (M₁ : ℝ)) ^ (ℓ - 1))) ∧
      (∃ C_R : ℝ, 0 < C_R ∧
        ∀ (d ℓ : ℕ) [NeZero d], 2 ≤ d → C_R * Real.log (d : ℝ) ≤ (ℓ : ℝ) →
          (d : ℝ) * ((d : ℝ) - 1) * ((1 / (M₁ : ℝ)) ^ (ℓ - 1)) ≤ 1 / (d : ℝ))) := by
  classical
  constructor
  · obtain ⟨C_beh, hCbeh, hBeh⟩ := diagnosis_BehrendAndRandomAPBound.1
    have hlog4 : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
    have hsqrt4 : 0 < Real.sqrt (Real.log (4 : ℝ)) := Real.sqrt_pos.mpr hlog4
    have hlog3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
    let C_B : ℝ := C_beh + Real.log 3 / Real.sqrt (Real.log 4)
    have hCB : 0 < C_B := by positivity
    refine ⟨C_B, 4, hCB, by decide, fun d _ hd4 => ?_⟩
    let n := d / 2
    have hn2 : 2 ≤ n := by omega
    obtain ⟨S, hSlt, hSAP, hScard⟩ := hBeh n hn2
    let J : Finset (ZMod d) := S.image fun x : ℕ => (x : ZMod d)
    have hInj : Set.InjOn (fun x : ℕ => (x : ZMod d)) ↑S := by
      intro x hx y hy hEq
      have hxd : x < d := lt_of_lt_of_le (hSlt x hx) (Nat.div_le_self d 2)
      have hyd : y < d := lt_of_lt_of_le (hSlt y hy) (Nat.div_le_self d 2)
      have hv := congrArg ZMod.val hEq
      rwa [ZMod.val_natCast_of_lt hxd, ZMod.val_natCast_of_lt hyd] at hv
    refine ⟨J, ?_, ?_⟩
    · intro a s hs ⟨ha, has, ha2s⟩
      obtain ⟨x, hxS, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨y, hyS, hyEq⟩ := Finset.mem_image.mp has
      obtain ⟨z, hzS, hzEq⟩ := Finset.mem_image.mp ha2s
      have hxlt := hSlt x hxS
      have hylt := hSlt y hyS
      have hzlt := hSlt z hzS
      have h2nd : 2 * n ≤ d := Nat.mul_div_le d 2
      have hSumMod : ((x + z : ℕ) : ZMod d) = ((2 * y : ℕ) : ZMod d) := by
        push_cast
        rw [hzEq, hyEq]
        ring
      have hxzLt : x + z < d := by omega
      have h2yLt : 2 * y < d := by omega
      have hSumNat : x + z = 2 * y := by
        have hv := congrArg ZMod.val hSumMod
        rwa [ZMod.val_natCast_of_lt hxzLt, ZMod.val_natCast_of_lt h2yLt] at hv
      rcases lt_trichotomy x y with hxy | rfl | hyx
      · exact hSAP x (y - x) (by omega) ⟨hxS, by convert hyS using 1; omega,
          by convert hzS using 1; omega⟩
      · have hs0 : s = 0 := by
          have h0 : (x : ZMod d) + 0 = (x : ZMod d) + s := by
            rw [add_zero]
            exact hyEq
          exact (add_left_cancel h0).symm
        exact hs hs0
      · exact hSAP z (y - z) (by omega) ⟨hzS, by convert hyS using 1; omega,
          by convert hxS using 1; omega⟩
    · rw [Finset.card_image_of_injOn hInj]
      have hdR4 : (4 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd4
      have hnd : (d : ℝ) / 3 ≤ (n : ℝ) := by
        have hnat : d ≤ 3 * n := by omega
        have hr : (d : ℝ) ≤ 3 * (n : ℝ) := by exact_mod_cast hnat
        linarith
      have hlogLe : Real.log (n : ℝ) ≤ Real.log (d : ℝ) :=
        Real.log_le_log (by positivity) (by exact_mod_cast Nat.div_le_self d 2)
      have hsqrtLe : Real.sqrt (Real.log (n : ℝ)) ≤ Real.sqrt (Real.log (d : ℝ)) :=
        Real.sqrt_le_sqrt hlogLe
      have hsqrt4Le : Real.sqrt (Real.log 4) ≤ Real.sqrt (Real.log (d : ℝ)) :=
        Real.sqrt_le_sqrt (Real.log_le_log (by norm_num) hdR4)
      have hCB_split : -C_B * Real.sqrt (Real.log (d : ℝ)) ≤
          -C_beh * Real.sqrt (Real.log (n : ℝ)) - Real.log 3 := by
        have hdiv : Real.log 3 ≤
            (Real.log 3 / Real.sqrt (Real.log 4)) * Real.sqrt (Real.log (d : ℝ)) := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hsqrt4]
          exact mul_le_mul_of_nonneg_left hsqrt4Le hlog3.le
        dsimp only [C_B]
        nlinarith
      calc (d : ℝ) * Real.exp (-C_B * Real.sqrt (Real.log (d : ℝ)))
          ≤ (d : ℝ) * Real.exp (-C_beh * Real.sqrt (Real.log (n : ℝ)) - Real.log 3) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hCB_split) (Nat.cast_nonneg d)
        _ = ((d : ℝ) / 3) * Real.exp (-C_beh * Real.sqrt (Real.log (n : ℝ))) := by
            rw [sub_eq_add_neg, Real.exp_add, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
            ring
        _ ≤ (n : ℝ) * Real.exp (-C_beh * Real.sqrt (Real.log (n : ℝ))) :=
            mul_le_mul_of_nonneg_right hnd (Real.exp_pos _).le
        _ ≤ (S.card : ℝ) := hScard
  · intro M₁ hM₁
    have hBound : ∀ (d ℓ : ℕ) [NeZero d], 1 ≤ ℓ →
        ((Finset.univ.filter fun p : ZMod d → Fin M₁ => HasInjectiveMonoModAP p ℓ).card : ℝ) /
          (Fintype.card (ZMod d → Fin M₁) : ℝ) ≤
          (d : ℝ) * ((d : ℝ) - 1) * ((1 / (M₁ : ℝ)) ^ (ℓ - 1)) := by
      intro d ℓ _ hℓ1
      let pairs : Finset (ZMod d × ZMod d) :=
        Finset.univ ×ˢ (Finset.univ.erase 0)
      let event (cs : ZMod d × ZMod d) : Finset (ZMod d → Fin M₁) :=
        Finset.univ.filter fun p =>
          Function.Injective (fun j : Fin ℓ => cs.1 + (j.val : ZMod d) * cs.2) ∧
          ∀ j : Fin ℓ, p (cs.1 + (j.val : ZMod d) * cs.2) = p cs.1
      have hSub : (Finset.univ.filter fun p : ZMod d → Fin M₁ => HasInjectiveMonoModAP p ℓ) ⊆
          pairs.biUnion event := by
        intro p hp
        obtain ⟨_, c₀, s, hs, hinj, hmono⟩ := Finset.mem_filter.mp hp
        refine Finset.mem_biUnion.mpr ⟨(c₀, s), ?_, Finset.mem_filter.mpr ⟨Finset.mem_univ p, hinj, hmono⟩⟩
        exact Finset.mem_product.mpr ⟨Finset.mem_univ c₀, Finset.mem_erase.mpr ⟨hs, Finset.mem_univ s⟩⟩
      have hEventCard : ∀ cs : ZMod d × ZMod d,
          (event cs).card * M₁ ^ (ℓ - 1) ≤ Fintype.card (ZMod d → Fin M₁) := by
        intro ⟨c₀, s⟩
        let g (j : Fin ℓ) : ZMod d := c₀ + (j.val : ZMod d) * s
        by_cases hInjG : Function.Injective g
        · let Img : Finset (ZMod d) := Finset.univ.image g
          have hImgCard : Img.card = ℓ := by
            rw [Finset.card_image_of_injective _ hInjG, Finset.card_univ, Fintype.card_fin]
          have hℓd : ℓ ≤ d := by
            calc ℓ = Img.card := hImgCard.symm
              _ ≤ (Finset.univ : Finset (ZMod d)).card := Finset.card_le_univ Img
              _ = d := by simp [ZMod.card]
          let Compl : Finset (ZMod d) := Finset.univ \ Img
          have hComplCard : Compl.card = d - ℓ := by
            rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, ZMod.card, hImgCard]
          let toPair (p : ZMod d → Fin M₁) : Fin M₁ × (↑Compl → Fin M₁) :=
            (p c₀, fun x => p x.1)
          have hInjPair : Set.InjOn toPair ↑(event (c₀, s)) := by
            intro p₁ hp₁ p₂ hp₂ hEq
            have hm₁ := (Finset.mem_filter.mp hp₁).2.2
            have hm₂ := (Finset.mem_filter.mp hp₂).2.2
            have hcol : p₁ c₀ = p₂ c₀ := congrArg Prod.fst hEq
            have hrest := congrArg Prod.snd hEq
            funext x
            by_cases hx : x ∈ Img
            · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
              exact (hm₁ j).trans (hcol.trans (hm₂ j).symm)
            · have hxC : x ∈ Compl := Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hx⟩
              exact congrFun hrest ⟨x, hxC⟩
          have hCardLe : (event (c₀, s)).card ≤ M₁ * M₁ ^ (d - ℓ) := by
            calc (event (c₀, s)).card
                = ((event (c₀, s)).image toPair).card := (Finset.card_image_of_injOn hInjPair).symm
              _ ≤ Fintype.card (Fin M₁ × (↑Compl → Fin M₁)) := Finset.card_le_univ _
              _ = M₁ * M₁ ^ (d - ℓ) := by
                  simp [Fintype.card_prod, hComplCard]
          calc (event (c₀, s)).card * M₁ ^ (ℓ - 1)
              ≤ (M₁ * M₁ ^ (d - ℓ)) * M₁ ^ (ℓ - 1) := Nat.mul_le_mul_right _ hCardLe
            _ = M₁ ^ (1 + (d - ℓ) + (ℓ - 1)) := by
                rw [← pow_succ', ← pow_add]
                congr 1; omega
            _ = M₁ ^ d := by congr 1; omega
            _ = Fintype.card (ZMod d → Fin M₁) := by simp [ZMod.card]
        · have hEmpty : event (c₀, s) = ∅ := by
            ext p
            simp only [event, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
              iff_false, not_and]
            intro hi
            exact absurd hi hInjG
          rw [hEmpty]
          simp
      have hPairsCard : pairs.card = d * (d - 1) := by
        rw [Finset.card_product, Finset.card_erase_of_mem (Finset.mem_univ (0 : ZMod d))]
        simp [ZMod.card]
      have hNatTotal :
          (Finset.univ.filter fun p : ZMod d → Fin M₁ => HasInjectiveMonoModAP p ℓ).card *
            M₁ ^ (ℓ - 1) ≤ (d * (d - 1)) * Fintype.card (ZMod d → Fin M₁) := by
        calc _ ≤ (pairs.biUnion event).card * M₁ ^ (ℓ - 1) :=
                Nat.mul_le_mul_right _ (Finset.card_le_card hSub)
          _ ≤ (∑ cs ∈ pairs, (event cs).card) * M₁ ^ (ℓ - 1) :=
                Nat.mul_le_mul_right _ Finset.card_biUnion_le
          _ = ∑ cs ∈ pairs, (event cs).card * M₁ ^ (ℓ - 1) := Finset.sum_mul _ _ _
          _ ≤ ∑ _cs ∈ pairs, Fintype.card (ZMod d → Fin M₁) :=
                Finset.sum_le_sum fun cs _ => hEventCard cs
          _ = (d * (d - 1)) * Fintype.card (ZMod d → Fin M₁) := by simp [hPairsCard]
      have hCardPos : (0 : ℝ) < (Fintype.card (ZMod d → Fin M₁) : ℝ) := by
        have hM1Pos : 0 < M₁ := by omega
        have : 0 < Fintype.card (ZMod d → Fin M₁) := by
          simp [ZMod.card, Nat.pos_iff_ne_zero, hM1Pos.ne']
        exact_mod_cast this
      have hPowPos : (0 : ℝ) < (M₁ : ℝ) ^ (ℓ - 1) := by positivity
      have hReal :
          ((Finset.univ.filter fun p : ZMod d → Fin M₁ => HasInjectiveMonoModAP p ℓ).card : ℝ) *
            (M₁ : ℝ) ^ (ℓ - 1) ≤
          (d : ℝ) * ((d : ℝ) - 1) * (Fintype.card (ZMod d → Fin M₁) : ℝ) := by
        have hd1 : 1 ≤ d := NeZero.pos d
        have hr : (((Finset.univ.filter fun p : ZMod d → Fin M₁ =>
              HasInjectiveMonoModAP p ℓ).card * M₁ ^ (ℓ - 1) : ℕ) : ℝ) ≤
            (((d * (d - 1)) * Fintype.card (ZMod d → Fin M₁) : ℕ) : ℝ) :=
          Nat.cast_le.mpr hNatTotal
        push_cast [Nat.cast_sub hd1] at hr
        linarith
      rw [div_le_iff₀ hCardPos, one_div, inv_pow]
      apply le_of_mul_le_mul_right _ hPowPos
      calc ((Finset.univ.filter fun p : ZMod d → Fin M₁ => HasInjectiveMonoModAP p ℓ).card : ℝ) *
              (M₁ : ℝ) ^ (ℓ - 1)
          ≤ (d : ℝ) * ((d : ℝ) - 1) * (Fintype.card (ZMod d → Fin M₁) : ℝ) := hReal
        _ = (d : ℝ) * ((d : ℝ) - 1) * ((M₁ : ℝ) ^ (ℓ - 1))⁻¹ *
              (Fintype.card (ZMod d → Fin M₁) : ℝ) * (M₁ : ℝ) ^ (ℓ - 1) := by
            field_simp
    refine ⟨hBound, ?_, ?_⟩
    · intro d ℓ _ hPrime hℓ1 hℓd
      have hFact : Fact (Nat.Prime d) := ⟨hPrime⟩
      have hSubPrime :
          (Finset.univ.filter fun p : ZMod d → Fin M₁ =>
            ∃ (c₀ s : ZMod d), s ≠ 0 ∧ ∀ j : Fin ℓ, p (c₀ + (j.val : ZMod d) * s) = p c₀) ⊆
          (Finset.univ.filter fun p : ZMod d → Fin M₁ => HasInjectiveMonoModAP p ℓ) := by
        intro p hp
        obtain ⟨_, c₀, s, hs, hm⟩ := Finset.mem_filter.mp hp
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ p, c₀, s, hs, ?_, hm⟩
        intro j₁ j₂ hEq
        have hmul : (j₁.val : ZMod d) * s = (j₂.val : ZMod d) * s := add_left_cancel hEq
        have hcast : (j₁.val : ZMod d) = (j₂.val : ZMod d) := mul_right_cancel₀ hs hmul
        have hv := congrArg ZMod.val hcast
        rw [ZMod.val_natCast_of_lt (lt_of_lt_of_le j₁.isLt hℓd),
            ZMod.val_natCast_of_lt (lt_of_lt_of_le j₂.isLt hℓd)] at hv
        exact Fin.ext hv
      have hCardSub :
          ((Finset.univ.filter fun p : ZMod d → Fin M₁ =>
            ∃ (c₀ s : ZMod d), s ≠ 0 ∧ ∀ j : Fin ℓ, p (c₀ + (j.val : ZMod d) * s) = p c₀).card : ℝ) ≤
          ((Finset.univ.filter fun p : ZMod d → Fin M₁ => HasInjectiveMonoModAP p ℓ).card : ℝ) :=
        Nat.cast_le.mpr (Finset.card_le_card hSubPrime)
      exact (div_le_div_of_nonneg_right hCardSub (Nat.cast_nonneg _)).trans (hBound d ℓ hℓ1)
    · have hlogM : 0 < Real.log (M₁ : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < M₁ by omega))
      have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
      let C_R : ℝ := 3 / Real.log (M₁ : ℝ) + 1 / Real.log 2
      have hCRpos : 0 < C_R := by positivity
      refine ⟨C_R, hCRpos, fun d ℓ _ hd2 hℓLog => ?_⟩
      have hdR2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd2
      have hdPos : (0 : ℝ) < (d : ℝ) := by linarith
      have hlogdGe : Real.log 2 ≤ Real.log (d : ℝ) := Real.log_le_log (by norm_num) hdR2
      have hlogdPos : 0 < Real.log (d : ℝ) := lt_of_lt_of_le hlog2 hlogdGe
      have h1Le : 1 ≤ (1 / Real.log 2) * Real.log (d : ℝ) := by
        rw [one_div, inv_mul_eq_div, one_le_div hlog2]
        exact hlogdGe
      have hℓPos : 1 ≤ ℓ := by
        have hposR : (0 : ℝ) < (ℓ : ℝ) := lt_of_lt_of_le (mul_pos hCRpos hlogdPos) hℓLog
        have hposN : 0 < ℓ := by exact_mod_cast hposR
        omega
      have hℓm1 : (3 / Real.log (M₁ : ℝ)) * Real.log (d : ℝ) ≤ ((ℓ - 1 : ℕ) : ℝ) := by
        rw [Nat.cast_sub hℓPos, Nat.cast_one]
        dsimp only [C_R] at hℓLog
        linarith
      have hExpIneq : 3 * Real.log (d : ℝ) ≤ ((ℓ - 1 : ℕ) : ℝ) * Real.log (M₁ : ℝ) := by
        have hm := mul_le_mul_of_nonneg_right hℓm1 hlogM.le
        have hMne : Real.log (M₁ : ℝ) ≠ 0 := hlogM.ne'
        calc 3 * Real.log (d : ℝ)
            = (3 / Real.log (M₁ : ℝ)) * Real.log (d : ℝ) * Real.log (M₁ : ℝ) := by field_simp
          _ ≤ ((ℓ - 1 : ℕ) : ℝ) * Real.log (M₁ : ℝ) := hm
      have hd3Le : (d : ℝ) ^ 3 ≤ (M₁ : ℝ) ^ (ℓ - 1) := by
        have hexp := Real.exp_le_exp.mpr hExpIneq
        have hL : Real.exp (3 * Real.log (d : ℝ)) = (d : ℝ) ^ 3 := by
          rw [show (3 : ℝ) * Real.log (d : ℝ) = (3 : ℕ) * Real.log (d : ℝ) by norm_num,
              Real.exp_nat_mul, Real.exp_log hdPos]
        have hMpos : (0 : ℝ) < (M₁ : ℝ) := by positivity
        have hR : Real.exp (((ℓ - 1 : ℕ) : ℝ) * Real.log (M₁ : ℝ)) = (M₁ : ℝ) ^ (ℓ - 1) := by
          rw [Real.exp_nat_mul, Real.exp_log hMpos]
        rwa [hL, hR] at hexp
      have hPowPos : (0 : ℝ) < (M₁ : ℝ) ^ (ℓ - 1) := by positivity
      rw [one_div (M₁ : ℝ), inv_pow, ← div_eq_mul_inv, div_le_div_iff₀ hPowPos hdPos]
      have hdSq : (d : ℝ) * ((d : ℝ) - 1) * (d : ℝ) ≤ (d : ℝ) ^ 3 := by nlinarith
      exact hdSq.trans (by linarith)

end Diagnosis5And6Consequences

/-! ### 3. Machine-to-Operator Representation Bridges -/

section MachineOperatorBridges

/-- Canonical 0/1 embedding of `M : Transpose.Matrix` into `GridState F d (Transpose.entryBits d)`,
mapping cell `(r, c) : Fin d × Fin d` and bit lane `ℓ : Fin (Transpose.entryBits d)` to `1 : F`
when `M r.val c.val ℓ.val = true` and `0 : F` otherwise. -/
def encodeTMMatrixToGrid (F : Type*) [Semiring F] (d : ℕ) (M : Transpose.Matrix) :
    GridState F d (Transpose.entryBits d) :=
  fun r c ℓ => if M r.val c.val ℓ.val then 1 else 0

/-- **Exact Machine-to-Operator Representation Bridges (`README.md` §I.2 Line 14 & §II.3.2).**
Under `encodeTMMatrixToGrid`, the Turing-machine matrix transformations `stoneShuffleTMMatrix`,
`stoneUnshuffleTMMatrix`, `rowShearTMMatrix`, and `Transpose.transpose` intertwine identically
with `stoneShuffleGridLinear`, `stoneUnshuffleGridLinear`, `rowShearLinear`, and `gridSwapLinear`
over every ring `F`, paired directly with `stoneUnshuffleTM_twoTape_linear`. -/
theorem tmMatrix_gridLinear_bridges (F : Type*) [Ring F] :
    (∀ (m : ℕ) (M : Transpose.Matrix),
      encodeTMMatrixToGrid F (2 ^ m) (stoneShuffleTMMatrix m M) =
        stoneShuffleGridLinear F m (Transpose.entryBits (2 ^ m))
          (encodeTMMatrixToGrid F (2 ^ m) M)) ∧
    (∀ (m : ℕ) (M : Transpose.Matrix),
      encodeTMMatrixToGrid F (2 ^ m) (stoneUnshuffleTMMatrix m M) =
        stoneUnshuffleGridLinear F m (Transpose.entryBits (2 ^ m))
          (encodeTMMatrixToGrid F (2 ^ m) M)) ∧
    (∀ (d : ℕ) [NeZero d] (M : Transpose.Matrix),
      encodeTMMatrixToGrid F d (rowShearTMMatrix d M) =
        rowShearLinear F d (Transpose.entryBits d) (encodeTMMatrixToGrid F d M)) ∧
    (∀ (d : ℕ) (M : Transpose.Matrix),
      encodeTMMatrixToGrid F d (Transpose.transpose M) =
        gridSwapLinear F d (Transpose.entryBits d) (encodeTMMatrixToGrid F d M)) ∧
    (∃ (M_unshuf : Transpose.TM) (C_unshuf : ℕ),
      M_unshuf.k = 2 ∧
      ∀ (m : ℕ) (A : Transpose.Matrix), 1 ≤ m →
        let d := 2 ^ m
        Transpose.ComputesWithin M_unshuf
          (Transpose.encode d (Transpose.entryBits d) A)
          (Transpose.encode d (Transpose.entryBits d) (stoneUnshuffleTMMatrix m A))
          (C_unshuf * Transpose.inputLength d)) := by
  refine ⟨?_, ?_, ?_, ?_, stoneUnshuffleTM_twoTape_linear⟩
  · intro m M
    cases m <;> rfl
  · intro m M
    cases m <;> rfl
  · intro d _ M
    rfl
  · intro d M
    rfl

end MachineOperatorBridges

end BoundedArityDecoders
