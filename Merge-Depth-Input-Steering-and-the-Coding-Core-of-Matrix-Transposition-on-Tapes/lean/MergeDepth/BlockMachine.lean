import MergeDepth.SkeletonCones
import MergeDepth.SkeletonGenie
import MergeDepth.LowAdaptivity

set_option autoImplicit false

/-!
# The block machine of a skeleton class in the frozen model (Lemma 4.5)

The machine is the frozen `Transpose.TM`, run with the first paper's total run
`Transpose.Tape.run` (configurations frozen after halting).

* **Skeletons** (Definition 4.1). A skeleton `σ : Skeleton k` has a length `σ.T` and components
  `σ.s0` (input head), `σ.s j` (the coarse work walks) and `σ.sout` (output count); only their
  values at times `< σ.T` matter. `InClass M w σ x`: the run on `x` halts at time `σ.T` and, at
  every time `t < σ.T`, `⌊x₀(t)/w⌋ = s₀(t)`, `⌊x_j(t)/w⌋ = s_j(t)` and `⌊n(t)/w⌋ = s_out(t)`, where
  `n(t)` is the number of bits appended before step `t`. `skelClass M w L σ` is the class `𝒳_σ`
  among the inputs `X ∈ {0,1}^L`. `runSkeleton M w x` is the skeleton `σ_w(x)` of a run, and
  `inClass_iff_runSkeleton` says that `𝒳_σ` is the fibre of `σ_w` over `σ` (among halting runs).
  `CoarseAgree M w σ x t` (agreement at all times `≤ t`, no halting) is the prefix version.
* **Block values** (Definition 4.4). `blockVal M w x t` records, for the run on `x`,
  (i) `state`: the state after step `t`; (ii) `cells j i`: the cell `w ⌊x_j(t)/w⌋ + i` of work
  tape `j` after step `t`, `i < w`; (iii) `inOff`, `workOff j`: the offsets
  `x₀(t+1) - w ⌊x₀(t)/w⌋` and `x_j(t+1) - w ⌊x_j(t)/w⌋`; (iv) `outWord`: the output bits at the
  positions in `[w ⌊n(t)/w⌋, n(t+1))`. The block indices are read off the run itself; on a
  skeleton class they are the components of `σ`, so `blockVal` is the paper's `v̄_t` there.
* **Lemma 4.5(b).** `blockVal_eq_of_coarseAgree` (for skeleton prefixes) and `blockVal_eq_of_args`
  (on a class): `v̄_t` is determined by `v̄_{t-1}`, the values `v̄_{prev_j(t)}` and the input bits
  in the input block `ℬ^in_{s₀(t)}` (`inBlock`). `block_oblivious` is the functional form, with the
  function `Φ_t` of the paper.
* **The block machine.** `blockMachine` (and `exists_blockFunDag`): the block machine of `σ` as a
  `BlockFunDag`: out-edges the steps of the block DAG, input block `ℬ^in_{s₀(t)}`, class `𝒳_σ`,
  values `v̄_t` (as `some`) for `t < T` and `none` from `T` on. No nonemptiness is needed.
* **Lemma 4.5(c).** `outTime σ w r` is `t̂_r = max {t < T : s_out(t) = ⌊r/w⌋}`; `outTime_spec`
  (and `outTime_spec_of_sout`, which uses only the output component of the skeleton) decodes the
  output bit `r` of a member that appends more than `r` bits; `card_outTime_eq_le` is the last
  sentence. `blockMachine_hdec` and `blockMachine_htr` are the hypotheses `hdec` and `htr` of
  `BlockFunDag.output_eq` and `BlockFunDag.isStorageCode_fibre`.
* **Lemma 4.5(d) for `σ`.** `skeleton_entries_ownerLoad`: the entry and owner-load bounds for the
  coarse work walks of `σ` itself (via `allHops_congr`, `entries_congr`, `ownerLoadLE_congr`).
* **Lemma 4.7 for the actual block machine.** `blockMachine_card_cone_le` (a), `blockMachine_cone`
  and `blockMachine_output_eq` (b), `blockMachine_isStorageCode_fibre` (c, for a class on which `M`
  transposes). `skelClass_storageCode` composes them with the genie of Lemma 4.6
  (`skel_genie_cost`, transferred to `σ` by `isDepPath_congr`).
* **The value width.** `card_admissible_le`, `blockVal_mem_admissible`: block values take at most
  `2^{β_w}` values, `β_w = ⌈log₂ |Q|⌉ + k w ⌈log₂ |Σ|⌉ + (k + 1) ⌈log₂ (w + 2)⌉ + w + 1`
  (`blockWidth`), for every input and every time; `six_le_blockWidth`; `card_revealed_le`: the
  revealed word of a genie `Γ` takes at most `2^{β_w |Γ|}` values.
-/

namespace MergeDepth

open Finset Transpose Transpose.Tape Transpose.Tape.Impl BoundedNesting

/-! ### Skeletons and skeleton classes -/

/-- A skeleton: its length `T` and its components, the blocks `s0` of the input head, `s j` of
the work heads (the coarse work walks) and `sout` of the output count. Only the values at times
`< T` matter. -/
structure Skeleton (k : ℕ) where
  T : ℕ
  s0 : ℕ → ℤ
  s : Fin k → ℕ → ℤ
  sout : ℕ → ℕ

/-- The run on `x` has skeleton `σ` at scale `w`: it halts at time `σ.T`, and before that time the
blocks of the heads and of the output count are the components of `σ`. -/
def InClass (M : TM) (w : ℕ) (σ : Skeleton M.k) (x : List Bool) : Prop :=
  HaltsAt M x σ.T ∧ ∀ t < σ.T, (run M x t).inPos / (w : ℤ) = σ.s0 t ∧
    (∀ j, (run M x t).workPos j / (w : ℤ) = σ.s j t) ∧ (run M x t).outRev.length / w = σ.sout t

/-- The skeleton class `𝒳_σ` among the inputs `X ∈ {0,1}^L`. -/
def skelClass (M : TM) (w L : ℕ) (σ : Skeleton M.k) : Set (Fin L → Bool) :=
  {X | InClass M w σ (List.ofFn X)}

theorem mem_skelClass {M : TM} {w L : ℕ} {σ : Skeleton M.k} {X : Fin L → Bool} :
    X ∈ skelClass M w L σ ↔ InClass M w σ (List.ofFn X) := Iff.rfl

/-- The run on `x` follows `σ` up to time `t`: at every time `τ ≤ t` the blocks of the heads and of
the output count are the components of `σ`. Halting is not required. -/
def CoarseAgree (M : TM) (w : ℕ) (σ : Skeleton M.k) (x : List Bool) (t : ℕ) : Prop :=
  ∀ τ ≤ t, (run M x τ).inPos / (w : ℤ) = σ.s0 τ ∧
    (∀ j, (run M x τ).workPos j / (w : ℤ) = σ.s j τ) ∧ (run M x τ).outRev.length / w = σ.sout τ

/-- A member of the class follows `σ` up to every time `t < T`. -/
theorem InClass.coarseAgree {M : TM} {w : ℕ} {σ : Skeleton M.k} {x : List Bool}
    (hx : InClass M w σ x) {t : ℕ} (ht : t < σ.T) : CoarseAgree M w σ x t :=
  fun τ hτ => hx.2 τ (by omega)

/-! ### Block values -/

/-- A block value (Definition 4.4): the state, the cells of the blocks of the work heads, the
offsets of the heads and the output word. -/
@[ext]
structure BlockVal (M : TM) (w : ℕ) where
  state : Fin (M.q + 1)
  cells : Fin M.k → Fin w → Fin (M.g + 1)
  inOff : ℤ
  workOff : Fin M.k → ℤ
  outWord : List Bool

instance (M : TM) (w : ℕ) : Nonempty (BlockVal M w) :=
  ⟨⟨0, fun _ _ => 0, 0, fun _ => 0, []⟩⟩

/-- The block value `v̄_t(x)` at scale `w`: (i) the state after step `t`; (ii) for every work tape
`j` the cells `w ⌊x_j(t)/w⌋ + i`, `i < w`, after step `t`; (iii) the offsets
`x₀(t+1) - w ⌊x₀(t)/w⌋` and `x_j(t+1) - w ⌊x_j(t)/w⌋`; (iv) the output bits at the positions in
`[w ⌊n(t)/w⌋, n(t+1))`. -/
def blockVal (M : TM) (w : ℕ) (x : List Bool) (t : ℕ) : BlockVal M w where
  state := (run M x (t + 1)).state
  cells j i := (run M x (t + 1)).work j ((w : ℤ) * ((run M x t).workPos j / w) + ((i : ℕ) : ℤ))
  inOff := (run M x (t + 1)).inPos - w * ((run M x t).inPos / w)
  workOff j := (run M x (t + 1)).workPos j - w * ((run M x t).workPos j / w)
  outWord := (run M x (t + 1)).outRev.reverse.drop (w * ((run M x t).outRev.length / w))

/-- The input block `ℬ^in_a = ℬ_a ∩ [0, L)` of `a` at scale `w`. -/
def inBlock (L w : ℕ) (a : ℤ) : Finset (Fin L) :=
  univ.filter fun p => ((p : ℕ) : ℤ) / (w : ℤ) = a

theorem mem_inBlock {L w : ℕ} {a : ℤ} {p : Fin L} :
    p ∈ inBlock L w a ↔ ((p : ℕ) : ℤ) / (w : ℤ) = a := by
  simp [inBlock]

/-- An input block has at most `w` cells. -/
theorem card_inBlock_le {w : ℕ} (hw : 0 < w) (L : ℕ) (a : ℤ) : (inBlock L w a).card ≤ w := by
  have hw' : (0 : ℤ) < w := by exact_mod_cast hw
  have h : (inBlock L w a).card ≤ (Ico ((w : ℤ) * a) (w * a + w)).card := by
    refine card_le_card_of_injOn (fun p : Fin L => ((p : ℕ) : ℤ)) ?_ ?_
    · intro p hp
      have hpa := mem_inBlock.mp (mem_coe.mp hp)
      obtain ⟨h1, h2⟩ := block_bounds hw' ((p : ℕ) : ℤ)
      rw [hpa] at h1 h2
      exact mem_coe.mpr (mem_Ico.mpr ⟨h1, h2⟩)
    · intro p _ q _ hpq
      have hpq' : ((p : ℕ) : ℤ) = ((q : ℕ) : ℤ) := hpq
      exact Fin.ext (by exact_mod_cast hpq')
  rwa [Int.card_Ico, show (w : ℤ) * a + w - w * a = w by ring, Int.toNat_natCast] at h

/-! ### Arithmetic of blocks -/

/-- The cell `w a + i`, `i < w`, lies in the block `a`. -/
theorem block_div {w : ℕ} (hw : 0 < w) (a : ℤ) (i : Fin w) :
    ((w : ℤ) * a + ((i : ℕ) : ℤ)) / (w : ℤ) = a := by
  have hw' : (0 : ℤ) < w := by exact_mod_cast hw
  rw [add_comm, Int.add_mul_ediv_left _ _ hw'.ne',
    Int.ediv_eq_zero_of_lt (by positivity) (by exact_mod_cast i.2), zero_add]

/-- If one more bit moves the count to a new block, the new count is a multiple of `w`. -/
theorem mul_div_succ_of_ne {w n : ℕ} (h : (n + 1) / w ≠ n / w) : w * ((n + 1) / w) = n + 1 := by
  have hd : w ∣ n + 1 := by
    by_contra hd
    exact h (by simp [Nat.succ_div, hd])
  exact Nat.mul_div_cancel' hd

/-- `prevS y t` is undefined iff `y` never had the value `y t` before `t`. -/
theorem prevS_eq_none {y : ℕ → ℤ} {t : ℕ} : prevS y t = none ↔ ∀ u < t, y u ≠ y t := by
  classical
  unfold prevS
  split_ifs with h
  · simp only [false_iff]
    intro hall
    obtain ⟨u, hu⟩ := h
    obtain ⟨h1, h2⟩ := mem_filter.mp hu
    exact hall u (mem_range.mp h1) h2
  · simp only [true_iff]
    intro u hu he
    exact h ⟨u, mem_filter.mpr ⟨mem_range.mpr hu, he⟩⟩

/-! ### Lemma 4.5(b): obliviousness -/

section Oblivious

variable {M : TM} {w : ℕ} {σ : Skeleton M.k}

/-- A cell of the block `s_j(t)` at time `t` holds what it held after step `prev_j(t)`: head `j`
did not visit the block in between. -/
theorem work_eq_of_prevS {x : List Bool} {t t' : ℕ} (hx : CoarseAgree M w σ x t)
    (j : Fin M.k) (h : prevS (σ.s j) t = some t') {p : ℤ} (hp : p / (w : ℤ) = σ.s j t) :
    (run M x t).work j p = (run M x (t' + 1)).work j p := by
  obtain ⟨h1, -, h3⟩ := prevS_spec.mp h
  refine work_eq_of_no_visit j p (by omega) fun τ hτ1 hτ2 hpos => ?_
  have hτ := (hx τ (by omega)).2.1 j
  rw [hpos, hp] at hτ
  exact h3 τ (by omega) hτ2 hτ.symm

/-- If head `j` never visited the block `s_j(t)` before `t`, the block is blank at time `t`. -/
theorem work_eq_blank_of_prevS {x : List Bool} {t : ℕ} (hx : CoarseAgree M w σ x t)
    (j : Fin M.k) (h : prevS (σ.s j) t = none) {p : ℤ} (hp : p / (w : ℤ) = σ.s j t) :
    (run M x t).work j p = 0 := by
  refine work_eq_blank j p fun τ hτ hpos => ?_
  have hτ' := (hx τ (by omega)).2.1 j
  rw [hpos, hp] at hτ'
  exact prevS_eq_none.mp h τ hτ hτ'.symm

/-- Item (ii) of `v̄_t`: the cell `w s_j(t) + i` after step `t`. -/
theorem work_succ_eq_cells {x : List Bool} {t : ℕ} (hx : CoarseAgree M w σ x t)
    (j : Fin M.k) {p : ℤ} (i : Fin w) (hi : ((i : ℕ) : ℤ) = p - w * σ.s j t) :
    (run M x (t + 1)).work j p = (blockVal M w x t).cells j i := by
  simp only [blockVal]
  rw [(hx t le_rfl).2.1 j]
  congr 1
  omega

/-- The output word at time `t`: the positions in `[w ⌊n(t)/w⌋, n(t))` before step `t`. On a class
it is `O_{t-1}` if `s_out(t) = s_out(t - 1)`, and empty otherwise. -/
theorem outPrefix_eq {x y : List Bool} {t : ℕ} (hx : CoarseAgree M w σ x t)
    (hy : CoarseAgree M w σ y t) (hprev : ∀ u, u + 1 = t → blockVal M w x u = blockVal M w y u) :
    (run M x t).outRev.reverse.drop (w * ((run M x t).outRev.length / w)) =
      (run M y t).outRev.reverse.drop (w * ((run M y t).outRev.length / w)) := by
  rcases t with _ | u
  · simp [run_zero, init]
  · have hxu := hx u (by omega)
    have hyu := hy u (by omega)
    have hxt := hx (u + 1) le_rfl
    have hyt := hy (u + 1) le_rfl
    by_cases hs : σ.sout (u + 1) = σ.sout u
    · have e := congrArg BlockVal.outWord (hprev u rfl)
      simp only [blockVal] at e
      rw [hxt.2.2, hyt.2.2, hs]
      rw [hxu.2.2, hyu.2.2] at e
      exact e
    · -- a new output block starts at `u + 1`: the count is a multiple of `w`
      have hmul : ∀ z : List Bool, CoarseAgree M w σ z (u + 1) →
          w * ((run M z (u + 1)).outRev.length / w) = (run M z (u + 1)).outRev.length := by
        intro z hz
        have hzu := (hz u (by omega)).2.2
        have hzt := (hz (u + 1) le_rfl).2.2
        rw [outRev_length_succ] at hzt ⊢
        split_ifs at hzt ⊢ with hb
        · refine mul_div_succ_of_ne fun he => hs ?_
          rw [← hzt, ← hzu, he]
        · exact absurd (hzt.symm.trans (by rw [add_zero] at hzt ⊢; exact hzu)) hs
      rw [List.drop_eq_nil_of_le (by rw [List.length_reverse, hmul x hx]),
        List.drop_eq_nil_of_le (by rw [List.length_reverse, hmul y hy])]

/-- **Lemma 4.5(b), relational form, for skeleton prefixes.** Let the runs on `X` and `Y` follow
`σ` up to time `t` (neither needs to halt at `T`). If the block values agree at `t - 1` (for
`t ≥ 1`) and at `prev_j(t)` for every work tape `j` for which it is defined, and the inputs agree on
the input block `ℬ^in_{s₀(t)}`, then `v̄_t(X) = v̄_t(Y)`. -/
theorem blockVal_eq_of_coarseAgree (hw : 0 < w) {L : ℕ} {X Y : Fin L → Bool} {t : ℕ}
    (hX : CoarseAgree M w σ (List.ofFn X) t) (hY : CoarseAgree M w σ (List.ofFn Y) t)
    (hprev : ∀ u, u + 1 = t → blockVal M w (List.ofFn X) u = blockVal M w (List.ofFn Y) u)
    (hblock : ∀ j t', prevS (σ.s j) t = some t' →
      blockVal M w (List.ofFn X) t' = blockVal M w (List.ofFn Y) t')
    (hin : ∀ p ∈ inBlock L w (σ.s0 t), X p = Y p) :
    blockVal M w (List.ofFn X) t = blockVal M w (List.ofFn Y) t := by
  set x := List.ofFn X with hxdef
  set y := List.ofFn Y with hydef
  have hw' : (0 : ℤ) < w := by exact_mod_cast hw
  -- the state and the head positions at time `t`, from `v̄_{t-1}`
  have hcfg : (run M x t).state = (run M y t).state ∧ (run M x t).inPos = (run M y t).inPos ∧
      (run M x t).workPos = (run M y t).workPos := by
    rcases t with _ | u
    · exact ⟨rfl, rfl, rfl⟩
    · have h := hprev u rfl
      have hxu := hX u (by omega)
      have hyu := hY u (by omega)
      refine ⟨congrArg BlockVal.state h, ?_, funext fun j => ?_⟩
      · have e := congrArg BlockVal.inOff h
        simp only [blockVal] at e
        rw [hxu.1, hyu.1] at e
        linarith
      · have e := congrFun (congrArg BlockVal.workOff h) j
        simp only [blockVal] at e
        rw [hxu.2.1 j, hyu.2.1 j] at e
        linarith
  obtain ⟨hst, hinp, hwp⟩ := hcfg
  -- the blocks of the work heads at time `t`, from `v̄_{prev_j(t)}` (or blank)
  have hcell : ∀ j p, p / (w : ℤ) = σ.s j t → (run M x t).work j p = (run M y t).work j p := by
    intro j p hp
    rcases h : prevS (σ.s j) t with _ | t'
    · rw [work_eq_blank_of_prevS hX j h hp, work_eq_blank_of_prevS hY j h hp]
    · obtain ⟨h1, h2, -⟩ := prevS_spec.mp h
      have hp' : p / (w : ℤ) = σ.s j t' := hp.trans h2.symm
      obtain ⟨b0, b1⟩ := block_bounds hw' p
      rw [hp'] at b0 b1
      have hlt : (p - w * σ.s j t').toNat < w := by omega
      have hi : (((⟨(p - w * σ.s j t').toNat, hlt⟩ : Fin w) : ℕ) : ℤ) = p - w * σ.s j t' := by
        show (((p - w * σ.s j t').toNat : ℕ) : ℤ) = _
        omega
      rw [work_eq_of_prevS hX j h hp, work_eq_of_prevS hY j h hp,
        work_succ_eq_cells (fun τ hτ => hX τ (by omega)) j _ hi,
        work_succ_eq_cells (fun τ hτ => hY τ (by omega)) j _ hi, hblock j t' h]
  -- the symbols under the work heads and the input head at time `t`
  have hhead : headSym M x t = headSym M y t := by
    funext j
    unfold headSym
    rw [← hwp]
    exact hcell j _ ((hX t le_rfl).2.1 j)
  have hinsym : inSym M x t = inSym M y t := by
    unfold inSym
    rw [← hinp]
    refine readInput_eq_of_nth (L := L) List.length_ofFn List.length_ofFn ?_
    intro d hd hdL
    have hdb : (⟨d, hdL⟩ : Fin L) ∈ inBlock L w (σ.s0 t) := by
      rw [mem_inBlock]
      simp only
      rw [hd]
      exact (hX t le_rfl).1
    rw [nth_eq_getElem?, nth_eq_getElem?, List.getElem?_ofFn, List.getElem?_ofFn,
      dite_eq_left hdL, dite_eq_left hdL, hin _ hdb]
  -- the transition of step `t`
  have htr : transAt M x t = transAt M y t := transAt_eq_of_args hst hinsym hhead
  have hsucc := stateHeads_succ hst hinp hwp htr
  have hob : outBit M x t = outBit M y t := by simp only [outBit, htr]
  have hout := outPrefix_eq hX hY hprev
  refine BlockVal.ext hsucc.1 (funext fun j => funext fun i => ?_) ?_ (funext fun j => ?_) ?_
  · simp only [blockVal]
    rw [run_succ_work, run_succ_work, ← hwp, writtenSym_eq_of_transAt' hhead htr j,
      hcell j _ (by rw [block_div hw]; exact (hX t le_rfl).2.1 j)]
  · simp only [blockVal]
    rw [hsucc.2.1, hinp]
  · simp only [blockVal]
    rw [hsucc.2.2, hwp]
  · simp only [blockVal]
    have hlx : w * ((run M x t).outRev.length / w) ≤ (run M x t).outRev.reverse.length := by
      rw [List.length_reverse]; exact Nat.mul_div_le _ _
    have hly : w * ((run M y t).outRev.length / w) ≤ (run M y t).outRev.reverse.length := by
      rw [List.length_reverse]; exact Nat.mul_div_le _ _
    rw [run_succ_outRev_reverse, run_succ_outRev_reverse, List.drop_append_of_le_length hlx,
      List.drop_append_of_le_length hly, hout, hob]

/-- **Lemma 4.5(b), relational form.** Let `X, Y ∈ 𝒳_σ` and `t < T`. If the block values agree at
`t - 1` (for `t ≥ 1`) and at `prev_j(t)` for every work tape `j` for which it is defined, and the
inputs agree on the input block `ℬ^in_{s₀(t)}`, then `v̄_t(X) = v̄_t(Y)`. -/
theorem blockVal_eq_of_args (hw : 0 < w) {L : ℕ} {X Y : Fin L → Bool}
    (hX : InClass M w σ (List.ofFn X)) (hY : InClass M w σ (List.ofFn Y)) {t : ℕ}
    (ht : t < σ.T)
    (hprev : ∀ u, u + 1 = t → blockVal M w (List.ofFn X) u = blockVal M w (List.ofFn Y) u)
    (hblock : ∀ j t', prevS (σ.s j) t = some t' →
      blockVal M w (List.ofFn X) t' = blockVal M w (List.ofFn Y) t')
    (hin : ∀ p ∈ inBlock L w (σ.s0 t), X p = Y p) :
    blockVal M w (List.ofFn X) t = blockVal M w (List.ofFn Y) t :=
  blockVal_eq_of_coarseAgree hw (hX.coarseAgree ht) (hY.coarseAgree ht) hprev hblock hin

/-- A map that is constant on the fibres of `g` on `S` factors through `g` on `S`. -/
theorem exists_factor {α β γ : Type*} [Nonempty β] (S : Set α) (f : α → β) (g : α → γ)
    (h : ∀ a ∈ S, ∀ a' ∈ S, g a = g a' → f a = f a') : ∃ Φ : γ → β, ∀ a ∈ S, f a = Φ (g a) := by
  classical
  refine ⟨fun c => if hc : ∃ a ∈ S, g a = c then f hc.choose else Classical.arbitrary β, ?_⟩
  intro a ha
  have hc : ∃ a' ∈ S, g a' = g a := ⟨a, ha, rfl⟩
  simp only [dite_eq_left hc]
  exact h a ha _ hc.choose_spec.1 hc.choose_spec.2.symm

/-- **Lemma 4.5(b) (obliviousness).** For every `t < T` there is a function `Φ_t`, determined by
`M`, `σ` and `t`, such that for every `X ∈ 𝒳_σ`
`v̄_t(X) = Φ_t(v̄_{t-1}(X), v̄_{prev_1(t)}(X), …, v̄_{prev_k(t)}(X), X|ℬ^in_{s₀(t)})`, where an
argument that is not defined (`t = 0`, or `prev_j(t)` undefined) is replaced by `none`. -/
theorem block_oblivious (hw : 0 < w) (L : ℕ) (σ : Skeleton M.k) {t : ℕ} (ht : t < σ.T) :
    ∃ Φ : Option (BlockVal M w) → (Fin M.k → Option (BlockVal M w)) →
        (inBlock L w (σ.s0 t) → Bool) → BlockVal M w,
      ∀ X ∈ skelClass M w L σ,
        blockVal M w (List.ofFn X) t =
          Φ (if t = 0 then none else some (blockVal M w (List.ofFn X) (t - 1)))
            (fun j => (prevS (σ.s j) t).map (blockVal M w (List.ofFn X)))
            (fun p => X p) := by
  obtain ⟨Φ, hΦ⟩ := exists_factor (skelClass M w L σ) (fun X => blockVal M w (List.ofFn X) t)
    (fun X => ((if t = 0 then none else some (blockVal M w (List.ofFn X) (t - 1)) :
        Option (BlockVal M w)),
      (fun j => (prevS (σ.s j) t).map (blockVal M w (List.ofFn X))),
      (fun p : inBlock L w (σ.s0 t) => X p))) (by
    intro X hX Y hY he
    simp only [Prod.mk.injEq] at he
    obtain ⟨h1, h2, h3⟩ := he
    refine blockVal_eq_of_args hw hX hY ht (fun u hu => ?_) (fun j t' h => ?_)
      (fun p hp => congrFun h3 ⟨p, hp⟩)
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), Option.some_inj,
        show t - 1 = u by omega] at h1
      exact h1
    · have := congrFun h2 j
      rw [h, Option.map_some, Option.map_some, Option.some_inj] at this
      exact this)
  exact ⟨fun a b c => Φ (a, b, c), hΦ⟩

end Oblivious

/-! ### The block machine as a `BlockFunDag` -/

open Classical in
/-- **The block machine of `σ`** (Definition 4.4) as a `BlockFunDag`: out-edges the steps of the
block DAG of the coarse work walks (`BlockStep`), input block `ℬ^in_{s₀(t)}` at time `t`, class
`𝒳_σ`, and value `v̄_t` (as `some`) at the times `t < T`, `none` from `T` on. The field `det` is
Lemma 4.5(b). -/
noncomputable def blockMachine (M : TM) {w : ℕ} (hw : 0 < w) (L : ℕ) (σ : Skeleton M.k) :
    BlockFunDag L (Option (BlockVal M w)) where
  out t := (range σ.T).filter (BlockStep σ.s σ.T t ·)
  out_lt t u hu := by
    obtain ⟨-, -, h | ⟨j, hj⟩⟩ := mem_filter.mp hu
    · omega
    · exact (prevS_spec.mp hj).1
  blk t := inBlock L w (σ.s0 t)
  S := skelClass M w L σ
  val X t := if t < σ.T then some (blockVal M w (List.ofFn X) t) else none
  det X hX Y hY t hout hblk := by
    by_cases ht : t < σ.T
    · rw [ite_eq_left ht, ite_eq_left ht, Option.some_inj]
      refine blockVal_eq_of_args hw hX hY ht (fun u hu => ?_) (fun j t' h => ?_) hblk
      · have := hout u (mem_filter.mpr ⟨mem_range.mpr (by omega), ht, Or.inl hu⟩)
        rwa [ite_eq_left (by omega), ite_eq_left (by omega), Option.some_inj] at this
      · have h1 := (prevS_spec.mp h).1
        have := hout t' (mem_filter.mpr ⟨mem_range.mpr (by omega), ht, Or.inr ⟨j, h⟩⟩)
        rwa [ite_eq_left (by omega), ite_eq_left (by omega), Option.some_inj] at this
    · rw [ite_eq_right ht, ite_eq_right ht]

section Machine

variable {M : TM} {w : ℕ} (hw : 0 < w) (L : ℕ) (σ : Skeleton M.k)

open Classical in
theorem blockMachine_out (t : ℕ) :
    (blockMachine M hw L σ).out t = (range σ.T).filter (BlockStep σ.s σ.T t ·) := rfl

theorem blockMachine_blk (t : ℕ) : (blockMachine M hw L σ).blk t = inBlock L w (σ.s0 t) := rfl

theorem blockMachine_S : (blockMachine M hw L σ).S = skelClass M w L σ := rfl

theorem blockMachine_val {X : Fin L → Bool} {t : ℕ} (ht : t < σ.T) :
    (blockMachine M hw L σ).val X t = some (blockVal M w (List.ofFn X) t) := ite_eq_left ht

theorem blockMachine_val_of_le {X : Fin L → Bool} {t : ℕ} (ht : σ.T ≤ t) :
    (blockMachine M hw L σ).val X t = none := ite_eq_right (by omega)

end Machine

/-! ### Lemma 4.5(c): output decoding -/

/-- `t̂_r = max {t < T : s_out(t) = ⌊r/w⌋}` (`0` if the set is empty). -/
def outTime {k : ℕ} (σ : Skeleton k) (w r : ℕ) : ℕ :=
  Nat.findGreatest (fun t => t < σ.T ∧ σ.sout t = r / w) σ.T

/-- The step that appends bit `r`. -/
theorem exists_append_step {M : TM} (x : List Bool) {r : ℕ} :
    ∀ T, r < (run M x T).outRev.length →
      ∃ t < T, (run M x t).outRev.length = r ∧ (run M x (t + 1)).outRev.length = r + 1
  | 0, h => by simp [run_zero, init] at h
  | T + 1, h => by
    by_cases hT : r < (run M x T).outRev.length
    · obtain ⟨t, ht, h1, h2⟩ := exists_append_step x T hT
      exact ⟨t, by omega, h1, h2⟩
    · have hs := outRev_length_succ (M := M) x T
      refine ⟨T, by omega, ?_, ?_⟩ <;> split_ifs at hs <;> omega

section Decoding

variable {M : TM} {w : ℕ} {σ : Skeleton M.k}

/-- **Lemma 4.5(c), general form.** Let the output count of the run on `x` have the blocks
`s_out(t)` at the times `t < T` (only this component of the skeleton is used), and let `x` append
more than `r` bits before `T`. Then `t̂_r` exists: it is a time `< T` with
`s_out(t̂_r) = ⌊r/w⌋`, and no later time `< T` has this property. The output bit of `x` at
position `r` is the letter of `O_{t̂_r}(x)` at place `r - w ⌊r/w⌋ = r mod w`. No bound on `w` is
needed. -/
theorem outTime_spec_of_sout {x : List Bool}
    (hx : ∀ t < σ.T, (run M x t).outRev.length / w = σ.sout t) {r : ℕ}
    (hr : r < (run M x σ.T).outRev.length) :
    outTime σ w r < σ.T ∧ σ.sout (outTime σ w r) = r / w ∧
      (∀ t, outTime σ w r < t → t < σ.T → σ.sout t ≠ r / w) ∧
      (run M x σ.T).outRev.reverse[r]? = (blockVal M w x (outTime σ w r)).outWord[r % w]? := by
  obtain ⟨t₀, ht₀, hn₀, hn₁⟩ := exists_append_step x σ.T hr
  have hP₀ : t₀ < σ.T ∧ σ.sout t₀ = r / w := ⟨ht₀, by rw [← hx t₀ ht₀, hn₀]⟩
  have hspec : outTime σ w r < σ.T ∧ σ.sout (outTime σ w r) = r / w :=
    Nat.findGreatest_spec (P := fun t => t < σ.T ∧ σ.sout t = r / w) ht₀.le hP₀
  have hle : t₀ ≤ outTime σ w r := Nat.le_findGreatest ht₀.le hP₀
  refine ⟨hspec.1, hspec.2, fun t h1 h2 he => Nat.findGreatest_is_greatest h1 h2.le ⟨h2, he⟩, ?_⟩
  have hlen : r + 1 ≤ (run M x (outTime σ w r + 1)).outRev.length :=
    hn₁ ▸ outRev_length_mono x (by omega)
  obtain ⟨l, hl⟩ := exists_outRev_append (M := M) x (outTime σ w r + 1)
    (σ.T - (outTime σ w r + 1))
  rw [show outTime σ w r + 1 + (σ.T - (outTime σ w r + 1)) = σ.T by omega] at hl
  rw [hl, List.getElem?_append_left (by rw [List.length_reverse]; omega)]
  simp only [blockVal]
  rw [List.getElem?_drop, hx _ hspec.1, hspec.2, Nat.div_add_mod]

/-- **Lemma 4.5(c).** Let `x ∈ 𝒳_σ` append more than `r` bits. Then `t̂_r` exists: it is a time
`< T` with `s_out(t̂_r) = ⌊r/w⌋`, and no later time `< T` has this property. The output bit of `x`
at position `r` is the letter of `O_{t̂_r}(x)` at place `r - w ⌊r/w⌋ = r mod w`. -/
theorem outTime_spec {x : List Bool} (hx : InClass M w σ x) {r : ℕ}
    (hr : r < (run M x σ.T).outRev.length) :
    outTime σ w r < σ.T ∧ σ.sout (outTime σ w r) = r / w ∧
      (∀ t, outTime σ w r < t → t < σ.T → σ.sout t ≠ r / w) ∧
      (run M x σ.T).outRev.reverse[r]? = (blockVal M w x (outTime σ w r)).outWord[r % w]? :=
  outTime_spec_of_sout (fun t ht => (hx.2 t ht).2.2) hr

/-- **Lemma 4.5(c), last sentence.** If some member of `𝒳_σ` appends at least `L` bits, at most `w`
positions `r < L` share one time `t̂_r`. -/
theorem card_outTime_eq_le (hw : 0 < w) {x : List Bool} (hx : InClass M w σ x) {L : ℕ}
    (hL : L ≤ (run M x σ.T).outRev.length) (t : ℕ) :
    ((range L).filter fun r => outTime σ w r = t).card ≤ w := by
  have hsub : (range L).filter (fun r => outTime σ w r = t) ⊆
      Ico (w * σ.sout t) (w * σ.sout t + w) := by
    intro r hr
    obtain ⟨hrL, hrt⟩ := mem_filter.mp hr
    have h := (outTime_spec hx (lt_of_lt_of_le (mem_range.mp hrL) hL)).2.1
    rw [hrt] at h
    have h1 := Nat.div_add_mod r w
    have h2 := Nat.mod_lt r hw
    rw [mem_Ico, h]
    constructor <;> omega
  calc _ ≤ (Ico (w * σ.sout t) (w * σ.sout t + w)).card := card_le_card hsub
    _ = w := by simp

end Decoding

/-! ### Lemma 4.7 for the block machine -/

/-- Transposing bit positions twice is the identity. -/
theorem tpos_tpos_of_lt {n b d : ℕ} (hd : d < n * n * b) : tpos n b (tpos n b d) = d := by
  obtain ⟨hi, hj, ht, hdec⟩ := pos_decomp hd
  have h1 := tpos_spec (i := d / b / n) hj ht
  rw [← hdec] at h1
  rw [h1, tpos_spec hi ht]
  exact hdec.symm

/-- The output bit of `X` at position `r` at time `T` (`false` beyond the output). -/
def outBitAt (M : TM) {L : ℕ} (T : ℕ) (X : Fin L → Bool) (r : Fin L) : Bool :=
  ((run M (List.ofFn X) T).outRev.reverse[(r : ℕ)]?).getD false

/-- Decoding the output bit at position `r` from a value of the block machine: the letter of the
output word at place `r mod w`. -/
def outDec {M : TM} {w L : ℕ} (r : Fin L) (v : Option (BlockVal M w)) : Bool :=
  (v.bind fun v => v.outWord[(r : ℕ) % w]?).getD false

section Cones

variable {M : TM} {w : ℕ} (hw : 0 < w) {L : ℕ} (σ : Skeleton M.k)

/-- **Lemma 4.5(c) in the form of `BlockFunDag.output_eq`.** If every member of `𝒳_σ` appends at
least `L` bits, the output bit at position `r < L` is a function of the value at `t̂_r`. -/
theorem blockMachine_hdec
    (happ : ∀ X ∈ skelClass M w L σ, L ≤ (run M (List.ofFn X) σ.T).outRev.length) :
    ∀ X ∈ (blockMachine M hw L σ).S, ∀ r : Fin L,
      outBitAt M σ.T X r = outDec r ((blockMachine M hw L σ).val X (outTime σ w r)) := by
  intro X hX r
  have hr : (r : ℕ) < (run M (List.ofFn X) σ.T).outRev.length := lt_of_lt_of_le r.2 (happ X hX)
  obtain ⟨h1, -, -, h4⟩ := outTime_spec hX hr
  rw [blockMachine_val hw L σ h1, outBitAt, outDec, Option.bind_some, h4]

/-- **Lemma 4.7(a) for the block machine.** If every `Γ`-free path of the dependency DAG of the
coarse work walks has at most `D + 1` vertices, then `|C_Γ(t)| ≤ B = ∑_{h ≤ D} (k + 1)^h` and
`|J_Γ(t)| ≤ w B`. -/
theorem blockMachine_card_cone_le {Γ : Finset ℕ} {D : ℕ}
    (hΓ : ∀ π, IsDepPath σ.s σ.T π → LinNet.GFree Γ π → π.length ≤ D + 1) (t : ℕ) :
    (coneV (blockMachine M hw L σ).net Γ t).card ≤ ∑ h ∈ range (D + 1), (M.k + 1) ^ h ∧
      ((blockMachine M hw L σ).coneJ Γ t).card ≤ w * ∑ h ∈ range (D + 1), (M.k + 1) ^ h :=
  card_coneV_le_of_blockStep _ σ.s σ.T (blockMachine_out hw L σ) hΓ
    (fun _ => card_inBlock_le hw L _) t

/-- **Lemma 4.7(b) for the block machine.** Members of `𝒳_σ` with the same revealed values
`v̄_u`, `u ∈ Γ`, that agree on `J_Γ(t)` have the same block value at `t < T`. -/
theorem blockMachine_cone (Γ : Finset ℕ) {X Y : Fin L → Bool} (hX : X ∈ skelClass M w L σ)
    (hY : Y ∈ skelClass M w L σ)
    (hΓ : ∀ u ∈ Γ, u < σ.T → blockVal M w (List.ofFn X) u = blockVal M w (List.ofFn Y) u)
    {t : ℕ} (ht : t < σ.T) (hJ : ∀ p ∈ (blockMachine M hw L σ).coneJ Γ t, X p = Y p) :
    blockVal M w (List.ofFn X) t = blockVal M w (List.ofFn Y) t := by
  have hΓ' : ∀ v ∈ Γ, (blockMachine M hw L σ).val X v = (blockMachine M hw L σ).val Y v := by
    intro v hv
    by_cases hvT : v < σ.T
    · rw [blockMachine_val hw L σ hvT, blockMachine_val hw L σ hvT, hΓ v hv hvT]
    · rw [blockMachine_val_of_le hw L σ (by omega), blockMachine_val_of_le hw L σ (by omega)]
  have h := (blockMachine M hw L σ).cone Γ hX hY hΓ' t hJ
  rwa [blockMachine_val hw L σ ht, blockMachine_val hw L σ ht, Option.some_inj] at h

/-- **Lemma 4.7(b), outputs, for the block machine.** If `X, Y ∈ 𝒳_σ` append more than `r` bits,
have the same revealed values and agree on `I_Γ(r) = J_Γ(t̂_r)`, their output bits at position
`r` agree. -/
theorem blockMachine_output_eq (Γ : Finset ℕ) {X Y : Fin L → Bool} (hX : X ∈ skelClass M w L σ)
    (hY : Y ∈ skelClass M w L σ)
    (hΓ : ∀ u ∈ Γ, u < σ.T → blockVal M w (List.ofFn X) u = blockVal M w (List.ofFn Y) u)
    {r : ℕ} (hrX : r < (run M (List.ofFn X) σ.T).outRev.length)
    (hrY : r < (run M (List.ofFn Y) σ.T).outRev.length)
    (hJ : ∀ p ∈ (blockMachine M hw L σ).coneJ Γ (outTime σ w r), X p = Y p) :
    (run M (List.ofFn X) σ.T).outRev.reverse[r]? =
      (run M (List.ofFn Y) σ.T).outRev.reverse[r]? := by
  obtain ⟨h1, -, -, hX'⟩ := outTime_spec hX hrX
  obtain ⟨-, -, -, hY'⟩ := outTime_spec hY hrY
  rw [hX', hY', blockMachine_cone hw σ Γ hX hY hΓ h1 hJ]

/-- **The transposition hypothesis in the form of `BlockFunDag.isStorageCode_fibre`.** If `M`
transposes every input of `𝒳_σ`, every member appends exactly `L = d² b` bits, and its output bit
at position `r` is its input bit at `tpos r`. -/
theorem blockMachine_htr {d b : ℕ}
    (htr : ∀ X ∈ skelClass M w (d * d * b) σ, OutputsTranspose M d b X) :
    ∀ X ∈ skelClass M w (d * d * b) σ,
      (run M (List.ofFn X) σ.T).outRev.length = d * d * b ∧
        ∀ r : Fin (d * d * b),
          outBitAt M σ.T X r = X ⟨tpos d b r, tpos_lt r.2⟩ := by
  intro X hX
  obtain ⟨s, hs, hlen, hval⟩ := (htr X hX).output
  obtain rfl : s = σ.T := haltsAt_unique hs hX.1
  refine ⟨by rw [← List.length_reverse]; exact hlen, fun r => ?_⟩
  have h := hval ⟨tpos d b r, tpos_lt r.2⟩
  rw [show tpos d b (tpos d b r) = r from tpos_tpos_of_lt r.2] at h
  rw [outBitAt, h]
  rfl

/-- **Lemma 4.7(c) for the block machine.** Let `L = d² b` and let `M` transpose every input of
`𝒳_σ` (at any halting time). For every value `g` of the revealed word, the fibre of `g` in `𝒳_σ`
is a storage code for the relation `N_Γ(q) = J_Γ(t̂_{tpos q})`. -/
theorem blockMachine_isStorageCode_fibre {d b : ℕ}
    (htr : ∀ X ∈ skelClass M w (d * d * b) σ, OutputsTranspose M d b X) (Γ : Finset ℕ)
    (g : ℕ → Option (BlockVal M w)) :
    MotionDepthCodes.IsStorageCode
      (fun q : Fin (d * d * b) =>
        (blockMachine M hw (d * d * b) σ).coneJ Γ (outTime σ w (tpos d b q)))
      ((blockMachine M hw (d * d * b) σ).fibre Γ g) := by
  have hout := blockMachine_htr σ htr
  have htp : ∀ q : Fin (d * d * b), (⟨tpos d b (⟨tpos d b q, tpos_lt q.2⟩ : Fin (d * d * b)),
      tpos_lt (tpos_lt q.2)⟩ : Fin (d * d * b)) = q := fun q => Fin.ext (tpos_tpos_of_lt q.2)
  exact (blockMachine M hw (d * d * b) σ).isStorageCode_fibre Γ (fun r => outTime σ w r)
    (fun q => ⟨tpos d b q, tpos_lt q.2⟩) htp (outBitAt M σ.T) outDec
    (blockMachine_hdec hw σ fun X hX => (hout X hX).1.ge) (fun X hX r => (hout X hX).2 r) g

end Cones

/-! ### The value width -/

/-- The value width `β_w = ⌈log₂ |Q|⌉ + k w ⌈log₂ |Σ|⌉ + (k + 1) ⌈log₂ (w + 2)⌉ + w + 1`, with
`|Q| = q + 1` states and `|Σ| = g + 1` work symbols. -/
def blockWidth (M : TM) (w : ℕ) : ℕ :=
  Nat.clog 2 (M.q + 1) + M.k * w * Nat.clog 2 (M.g + 1) + (M.k + 1) * Nat.clog 2 (w + 2) + w + 1

/-- `β_w ≥ 6` for `k, w ≥ 1`. -/
theorem six_le_blockWidth {M : TM} {w : ℕ} (hk : 1 ≤ M.k) (hw : 1 ≤ w) : 6 ≤ blockWidth M w := by
  have h : 1 < Nat.clog 2 (w + 2) := (Nat.lt_clog_iff_pow_lt (by norm_num)).mpr (by omega)
  have : 2 * 2 ≤ (M.k + 1) * Nat.clog 2 (w + 2) := Nat.mul_le_mul (by omega) h
  unfold blockWidth
  omega

/-- The binary words of length at most `n`. -/
def wordsLE : ℕ → Finset (List Bool)
  | 0 => {[]}
  | n + 1 => insert [] ((wordsLE n).image (List.cons true) ∪ (wordsLE n).image (List.cons false))

/-- There are `2^{n+1} - 1` binary words of length at most `n`. -/
theorem card_wordsLE : ∀ n, (wordsLE n).card + 1 ≤ 2 ^ (n + 1)
  | 0 => by simp [wordsLE]
  | n + 1 => by
    have ih := card_wordsLE n
    have h1 := card_insert_le ([] : List Bool)
      ((wordsLE n).image (List.cons true) ∪ (wordsLE n).image (List.cons false))
    have h2 := card_union_le ((wordsLE n).image (List.cons true))
      ((wordsLE n).image (List.cons false))
    have h3 := card_image_le (s := wordsLE n) (f := List.cons true)
    have h4 := card_image_le (s := wordsLE n) (f := List.cons false)
    simp only [wordsLE]
    rw [pow_succ]
    omega

theorem mem_wordsLE : ∀ {n : ℕ} {l : List Bool}, l.length ≤ n → l ∈ wordsLE n
  | 0, l, h => by
    have hl : l = [] := List.length_eq_zero_iff.mp (by omega)
    subst hl
    simp [wordsLE]
  | n + 1, [], _ => by simp [wordsLE]
  | n + 1, b :: l, h => by
    have hl : l ∈ wordsLE n := mem_wordsLE (by simp at h; omega)
    simp only [wordsLE, mem_insert, mem_union, mem_image]
    right
    cases b
    · exact Or.inr ⟨l, hl, rfl⟩
    · exact Or.inl ⟨l, hl, rfl⟩

open Classical in
/-- The admissible block values: offsets in `[-1, w]` and output words of length at most `w`. -/
noncomputable def admissible (M : TM) (w : ℕ) : Finset (BlockVal M w) :=
  ((univ : Finset (Fin (M.q + 1))) ×ˢ (univ : Finset (Fin M.k → Fin w → Fin (M.g + 1))) ×ˢ
      Icc (-1 : ℤ) w ×ˢ Fintype.piFinset (fun _ : Fin M.k => Icc (-1 : ℤ) w) ×ˢ wordsLE w).image
    fun z => ⟨z.1, z.2.1, z.2.2.1, z.2.2.2.1, z.2.2.2.2⟩

/-- **The value width.** There are at most `2^{β_w}` admissible block values. -/
theorem card_admissible_le (M : TM) (w : ℕ) : (admissible M w).card ≤ 2 ^ blockWidth M w := by
  classical
  refine card_image_le.trans ?_
  have hI : (Icc (-1 : ℤ) w).card = w + 2 := by rw [Int.card_Icc]; omega
  simp only [card_product, card_univ, Fintype.card_fun, Fintype.card_fin, hI,
    Fintype.card_piFinset, prod_const]
  have h1 : M.q + 1 ≤ 2 ^ Nat.clog 2 (M.q + 1) := Nat.le_pow_clog (by norm_num) _
  have h2 : ((M.g + 1) ^ w) ^ M.k ≤ 2 ^ (M.k * w * Nat.clog 2 (M.g + 1)) :=
    calc ((M.g + 1) ^ w) ^ M.k ≤ ((2 ^ Nat.clog 2 (M.g + 1)) ^ w) ^ M.k := by
          gcongr; exact Nat.le_pow_clog (by norm_num) _
      _ = 2 ^ (M.k * w * Nat.clog 2 (M.g + 1)) := by rw [← pow_mul, ← pow_mul]; ring_nf
  have h3 : (w + 2) * (w + 2) ^ M.k ≤ 2 ^ ((M.k + 1) * Nat.clog 2 (w + 2)) :=
    calc (w + 2) * (w + 2) ^ M.k = (w + 2) ^ (M.k + 1) := by ring
      _ ≤ (2 ^ Nat.clog 2 (w + 2)) ^ (M.k + 1) := by gcongr; exact Nat.le_pow_clog (by norm_num) _
      _ = 2 ^ ((M.k + 1) * Nat.clog 2 (w + 2)) := by rw [← pow_mul, mul_comm]
  have h4 : (wordsLE w).card ≤ 2 ^ (w + 1) := by have := card_wordsLE w; omega
  calc (M.q + 1) * (((M.g + 1) ^ w) ^ M.k * ((w + 2) * ((w + 2) ^ M.k * (wordsLE w).card)))
      = (M.q + 1) * (((M.g + 1) ^ w) ^ M.k * (((w + 2) * (w + 2) ^ M.k) * (wordsLE w).card)) := by
        ring
    _ ≤ 2 ^ Nat.clog 2 (M.q + 1) * (2 ^ (M.k * w * Nat.clog 2 (M.g + 1)) *
          (2 ^ ((M.k + 1) * Nat.clog 2 (w + 2)) * 2 ^ (w + 1))) :=
        Nat.mul_le_mul h1 (Nat.mul_le_mul h2 (Nat.mul_le_mul h3 h4))
    _ = 2 ^ blockWidth M w := by
        rw [← pow_add, ← pow_add, ← pow_add, blockWidth]
        congr 1
        ring

/-- Every block value is admissible: the offsets lie in `[-1, w]` because heads move by at most one
cell, and the output word has length at most `w` because at most one bit is appended per step. -/
theorem blockVal_mem_admissible {M : TM} {w : ℕ} (hw : 0 < w) (x : List Bool) (t : ℕ) :
    blockVal M w x t ∈ admissible M w := by
  classical
  have hw' : (0 : ℤ) < w := by exact_mod_cast hw
  refine mem_image.mpr ⟨((blockVal M w x t).state, (blockVal M w x t).cells,
    (blockVal M w x t).inOff, (blockVal M w x t).workOff, (blockVal M w x t).outWord), ?_, rfl⟩
  simp only [mem_product, mem_univ, true_and, mem_Icc, Fintype.mem_piFinset]
  refine ⟨?_, fun j => ?_, mem_wordsLE ?_⟩
  · have hstep : |(run M x (t + 1)).inPos - (run M x t).inPos| ≤ 1 := by
      rw [inPos_eq_input, inPos_eq_input]
      exact (trace M x).abs_input_succ_sub_le t
    obtain ⟨b0, b1⟩ := block_bounds hw' (run M x t).inPos
    have := abs_le.mp hstep
    simp only [blockVal]
    constructor <;> linarith
  · have hstep : |(run M x (t + 1)).workPos j - (run M x t).workPos j| ≤ 1 := by
      rw [workPos_eq_work, workPos_eq_work]
      exact (trace M x).work_isWalk j t
    obtain ⟨b0, b1⟩ := block_bounds hw' ((run M x t).workPos j)
    have := abs_le.mp hstep
    simp only [blockVal]
    constructor <;> linarith
  · simp only [blockVal, List.length_drop, List.length_reverse]
    have h1 := outRev_length_succ (M := M) x t
    have h2 := Nat.div_add_mod (run M x t).outRev.length w
    have h3 := Nat.mod_lt (run M x t).outRev.length hw
    split_ifs at h1 <;> omega

/-! ### The skeleton of a run -/

/-- The skeleton `σ_w(x)` of the run on `x` at scale `w`: the halting time `T(x)` (the first time
whose configuration halts; `0` if there is none) and the blocks of the heads and of the output count
before it, normalized to `0` from `T(x)` on. -/
noncomputable def runSkeleton (M : TM) (w : ℕ) (x : List Bool) : Skeleton M.k where
  T := (trace M x).haltTime
  s0 t := if t < (trace M x).haltTime then (run M x t).inPos / w else 0
  s j t := if t < (trace M x).haltTime then (run M x t).workPos j / w else 0
  sout t := if t < (trace M x).haltTime then (run M x t).outRev.length / w else 0

/-- A skeleton normalized to `0` from its length on: two skeletons with the same normalization are
the same sequence of length `T`. -/
def Skeleton.normalize {k : ℕ} (σ : Skeleton k) : Skeleton k where
  T := σ.T
  s0 t := if t < σ.T then σ.s0 t else 0
  s j t := if t < σ.T then σ.s j t else 0
  sout t := if t < σ.T then σ.sout t else 0

section RunSkeleton

variable {M : TM} {w : ℕ}

theorem haltTime_eq_of_haltsAt {x : List Bool} {T : ℕ} (h : HaltsAt M x T) :
    (trace M x).haltTime = T :=
  ((trace M x).haltsAt_haltTime ⟨T, ((haltsAt_iff_trace T).mp h).2⟩).unique
    ((haltsAt_iff_trace T).mp h)

/-- A halting run lies in the class of its own skeleton. -/
theorem inClass_runSkeleton {x : List Bool} {T : ℕ} (h : HaltsAt M x T) :
    InClass M w (runSkeleton M w x) x := by
  have hT := haltTime_eq_of_haltsAt h
  refine ⟨by simp only [runSkeleton, hT]; exact h, fun t ht => ?_⟩
  simp only [runSkeleton, hT] at ht ⊢
  simp only [ite_eq_left ht, implies_true, and_self]

theorem inClass_normalize_iff {σ : Skeleton M.k} {x : List Bool} :
    InClass M w σ.normalize x ↔ InClass M w σ x := by
  simp only [InClass, Skeleton.normalize]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun t ht => ?_⟩
    have := h2 t ht
    simp only [ite_eq_left ht] at this
    exact this
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun t ht => ?_⟩
    simp only [ite_eq_left ht]
    exact h2 t ht

/-- The skeleton of a member of `𝒳_σ` is `σ`, as a sequence of length `T`. -/
theorem runSkeleton_eq_of_inClass {σ : Skeleton M.k} {x : List Bool} (h : InClass M w σ x) :
    runSkeleton M w x = σ.normalize := by
  have hT := haltTime_eq_of_haltsAt h.1
  simp only [runSkeleton, Skeleton.normalize, hT, Skeleton.mk.injEq, true_and]
  refine ⟨funext fun t => ?_, funext fun j => funext fun t => ?_, funext fun t => ?_⟩ <;>
    by_cases ht : t < σ.T <;> simp only [ht, ↓reduceIte]
  · exact (h.2 t ht).1
  · exact (h.2 t ht).2.1 j
  · exact (h.2 t ht).2.2

/-- **The class is the fibre (Definition 4.1).** `x ∈ 𝒳_σ` iff the run on `x` halts and its
skeleton `σ_w(x)` is `σ` as a sequence of length `T_σ`. -/
theorem inClass_iff_runSkeleton {σ : Skeleton M.k} {x : List Bool} :
    InClass M w σ x ↔ (∃ T, HaltsAt M x T) ∧ runSkeleton M w x = σ.normalize := by
  constructor
  · intro h
    exact ⟨⟨σ.T, h.1⟩, runSkeleton_eq_of_inClass h⟩
  · rintro ⟨⟨T, hT⟩, he⟩
    have h := inClass_runSkeleton (w := w) hT
    rw [he] at h
    exact inClass_normalize_iff.mp h

end RunSkeleton

/-! ### The headline statements -/

section Headline

variable {M : TM} {w : ℕ}

open Classical in
/-- **Lemma 4.5(a), (b) as a `BlockFunDag`.** For every machine, scale `w ≥ 1`, length `L` and
skeleton `σ`, the block machine of `σ` is a `BlockFunDag` whose out-neighbours are those of the
block DAG of the coarse work walks, whose input block at `t` is `ℬ^in_{s₀(t)}`, whose class is
`𝒳_σ` and whose values are the block values before `T` (`none` from `T` on). No nonemptiness is
needed. -/
theorem exists_blockFunDag (hw : 0 < w) (L : ℕ) (σ : Skeleton M.k) :
    ∃ G : BlockFunDag L (Option (BlockVal M w)),
      (∀ t, G.out t = (range σ.T).filter (BlockStep σ.s σ.T t ·)) ∧
      (∀ t, G.blk t = inBlock L w (σ.s0 t)) ∧ G.S = skelClass M w L σ ∧
      (∀ X t, t < σ.T → G.val X t = some (blockVal M w (List.ofFn X) t)) ∧
      (∀ X t, σ.T ≤ t → G.val X t = none) :=
  ⟨blockMachine M hw L σ, blockMachine_out hw L σ, blockMachine_blk hw L σ,
    blockMachine_S hw L σ, fun _ _ ht => blockMachine_val hw L σ ht,
    fun _ _ ht => blockMachine_val_of_le hw L σ ht⟩

open Classical in
/-- **The revealed word.** For a genie `Γ`, the revealed values `(v̄_u(X))_{u ∈ Γ}` take at most
`2^{β_w |Γ|}` values on any set of inputs. -/
theorem card_revealed_le (hw : 0 < w) {L : ℕ} (Γ : Finset ℕ) (S : Finset (Fin L → Bool)) :
    (S.image fun X => fun u : Γ => blockVal M w (List.ofFn X) u).card ≤
      2 ^ (blockWidth M w * Γ.card) := by
  classical
  have hsub : (S.image fun X => fun u : Γ => blockVal M w (List.ofFn X) u) ⊆
      Fintype.piFinset fun _ : Γ => admissible M w := by
    intro f hf
    obtain ⟨X, -, rfl⟩ := mem_image.mp hf
    exact Fintype.mem_piFinset.mpr fun u => blockVal_mem_admissible hw _ _
  calc _ ≤ (Fintype.piFinset fun _ : Γ => admissible M w).card := card_le_card hsub
    _ = (admissible M w).card ^ Γ.card := by
        rw [Fintype.card_piFinset, prod_const, card_univ, Fintype.card_coe]
    _ ≤ (2 ^ blockWidth M w) ^ Γ.card := Nat.pow_le_pow_left (card_admissible_le M w) _
    _ = 2 ^ (blockWidth M w * Γ.card) := by rw [pow_mul]

end Headline

/-! ### The genie of Lemma 4.6 on the block DAG of `σ` -/

section Genie

variable {k : ℕ}

/-- Long hops before `T` depend only on the walks before `T`. -/
theorem allHops_congr {s s' : Fin k → ℕ → ℤ} {T : ℕ} (h : ∀ j t, t < T → s j t = s' j t) :
    allHops s T = allHops s' T := by
  have key : ∀ {s s' : Fin k → ℕ → ℤ}, (∀ j t, t < T → s j t = s' j t) →
      ∀ η, η ∈ allHops s T → η ∈ allHops s' T := by
    intro s s' h η hη
    obtain ⟨h1, h2, h3, h4⟩ := mem_allHops.mp hη
    refine mem_allHops.mpr ⟨h1, h2, ?_, fun t ht => ?_⟩
    · rw [← h _ _ h2, ← h _ _ (by omega)]
      exact h3
    · obtain ⟨ht1, ht2⟩ := mem_Ioo.mp ht
      rw [← h _ _ (by omega), ← h _ _ (by omega)]
      exact h4 t ht
  ext η
  exact ⟨key h η, key (fun j t ht => (h j t ht).symm) η⟩

/-- Dependency paths before `T` depend only on the walks before `T`. -/
theorem isDepPath_congr {s s' : Fin k → ℕ → ℤ} {T : ℕ} (h : ∀ j t, t < T → s j t = s' j t) :
    ∀ π, IsDepPath s T π ↔ IsDepPath s' T π
  | [] => Iff.rfl
  | [_] => Iff.rfl
  | a :: b :: π => by
    simp only [IsDepPath, DepStep, allHops_congr h, isDepPath_congr h (b :: π)]

/-- Entries up to `T'` depend only on the walk up to `T'`. -/
theorem entries_congr {x x' : ℕ → ℤ} {c : ℤ} {T' : ℕ} (h : ∀ t ≤ T', x t = x' t) :
    entries x c T' = entries x' c T' := by
  unfold entries
  refine filter_congr fun t ht => ?_
  have ht' := mem_range.mp ht
  rw [h t (by omega), h (t - 1) (by omega)]

/-- The owner of a long hop depends only on the walk up to the end of the hop. -/
theorem hopOwner_congr {x x' : ℕ → ℤ} {p u : ℕ} (hpu : p + 2 ≤ u) (h : ∀ t ≤ u, x t = x' t) :
    hopOwner x p u = hopOwner x' p u := by
  obtain ⟨a1, a2, a3, a4⟩ := hopOwner_spec x hpu
  obtain ⟨b1, b2, b3, b4⟩ := hopOwner_spec x' hpu
  have e : ∀ t, t ≤ u → |x t - x p| = |x' t - x' p| := fun t ht => by
    rw [h t ht, h p (by omega)]
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have h1 := b4 _ a1 hlt
    have h2 := a3 _ b1 b2
    rw [e _ (by omega), e _ (by omega)] at h2
    linarith
  · have h1 := a4 _ b1 hlt
    have h2 := b3 _ a1 a2
    rw [← e _ (by omega), ← e _ (by omega)] at h2
    linarith

/-- Owner-load of the long hops before `T` depends only on the walks before `T`. -/
theorem ownerLoadLE_congr {s s' : Fin k → ℕ → ℤ} {T ℓ : ℕ} (h : ∀ j t, t < T → s j t = s' j t)
    (hs' : OwnerLoadLE s' (allHops s' T) (fun η => hopOwner (s' η.1) η.2.1 η.2.2) ℓ) :
    OwnerLoadLE s (allHops s T) (fun η => hopOwner (s η.1) η.2.1 η.2.2) ℓ := by
  intro j b t
  have hH := hs' j b t
  rw [allHops_congr h]
  have hside : ∀ η ∈ allHops s' T, side s η = side s' η := by
    intro η hη
    obtain ⟨h1, h2, -, -⟩ := mem_allHops.mp hη
    simp only [side, h η.1 η.2.1 (by omega), h η.1 (η.2.1 + 1) (by omega)]
  have hown : ∀ η ∈ allHops s' T,
      hopOwner (s η.1) η.2.1 η.2.2 = hopOwner (s' η.1) η.2.1 η.2.2 := by
    intro η hη
    obtain ⟨h1, h2, -, -⟩ := mem_allHops.mp hη
    exact hopOwner_congr h1 fun t ht => h η.1 t (by omega)
  rw [filter_congr fun η hη => by rw [hside η hη],
    image_congr fun η hη => hown η (mem_filter.mp hη).1]
  exact hH

variable {M : TM}

/-- The work walk of head `j` on input `x`. -/
def workWalk (M : TM) (x : List Bool) (j : Fin M.k) : ℕ → ℤ := fun t => (run M x t).workPos j

theorem workWalk_isWalk (x : List Bool) (j : Fin M.k) : IsWalk (workWalk M x j) := by
  have e : workWalk M x j = (trace M x).work j := funext fun t => workPos_eq_work j t
  rw [e]
  exact (trace M x).work_isWalk j

/-- **Lemma 4.5(d) for the coarse work walks of `σ`.** If a member of `𝒳_σ` has entry at most `V`
on every work tape, every coarse work walk `s_j` of `σ` enters every block at most `2V` times before
`T`, and the long hops of `s_1, …, s_k` have owner-load at most `4V - 1`. -/
theorem skeleton_entries_ownerLoad {w : ℕ} (hw : 0 < w) {σ : Skeleton M.k} {x : List Bool}
    (hx : InClass M w σ x) {V : ℕ}
    (hV : ∀ j c, (entries (workWalk M x j) c (σ.T - 1)).card ≤ V) :
    (∀ j a, (entries (σ.s j) a (σ.T - 1)).card ≤ 2 * V) ∧
      OwnerLoadLE σ.s (allHops σ.s σ.T) (fun η => hopOwner (σ.s η.1) η.2.1 η.2.2) (4 * V - 1) := by
  have hwz : (0 : ℤ) < w := by exact_mod_cast hw
  have h0 : ∀ j, workWalk M x j 0 = 0 := fun j => rfl
  have hagree : ∀ j t, t < σ.T → σ.s j t = skel (w : ℤ) (workWalk M x j) t := fun j t ht =>
    ((hx.2 t ht).2.1 j).symm
  rcases Nat.eq_zero_or_pos σ.T with hT | hT
  · -- `T = 0`: there are no hops, and at most one entry
    refine ⟨fun j a => ?_, fun j b t => ?_⟩
    · have h1 : (entries (σ.s j) a (σ.T - 1)).card ≤ 1 := by
        rw [hT]
        exact (card_le_card (filter_subset _ _)).trans (by simp)
      have h2 : 1 ≤ V := by
        have h := hV j (workWalk M x j 0)
        rw [hT] at h
        have hmem : 0 ∈ entries (workWalk M x j) (workWalk M x j 0) 0 :=
          mem_filter.mpr ⟨by simp, rfl, Or.inl rfl⟩
        exact le_trans (card_pos.mpr ⟨0, hmem⟩) h
      omega
    · have hempty : allHops σ.s σ.T = ∅ := by
        rw [hT]
        ext η
        simp only [mem_allHops, IsHop, notMem_empty, iff_false]
        omega
      simp [hempty]
  · refine ⟨fun j a => ?_, ?_⟩
    · rw [entries_congr fun t ht => hagree j t (by omega)]
      exact card_entries_skel_le hwz (workWalk_isWalk x j) (h0 j) (hV j) a
    · have h := coarse_ownerLoad_le hwz (fun j => workWalk_isWalk x j) h0 (T := σ.T) hV
      rw [show 2 * (2 * V) - 1 = 4 * V - 1 by omega] at h
      exact ownerLoadLE_congr hagree h

/-- **Lemma 4.6 on the block DAG of `σ`.** Let `M` have `k ≥ 1` work tapes, let `V, w, L ≥ 1`,
`ε > 0`, and let `σ` be a skeleton at scale `w` with `T_σ ≤ c (L + 1)` such that some member of
`𝒳_σ` (among the inputs of any length) has entry at most `V` on every work tape. With
`C = max(c, 1)`, `P = ⌈4 β_w C/ε⌉` and `D₁ = DF(k, 4V - 1, ε/(4 β_w C))` there is a genie `Γ` of
cost `β_w |Γ| ≤ ε L` such that every `Γ`-free path of the block DAG `H̄_σ` (the dependency DAG of
the coarse work walks `σ.s`) has at most `D₁ P` vertices, that is, at most `D = D₁ P - 1`
edges. -/
theorem skeleton_genie (hk : 1 ≤ M.k) {V w L : ℕ} (hV : 1 ≤ V) (hw : 0 < w) (hL : 1 ≤ L)
    {c ε : ℝ} (hε : 0 < ε) (σ : Skeleton M.k) (hT : (σ.T : ℝ) ≤ c * (L + 1))
    (hentry : ∃ x, InClass M w σ x ∧
      ∀ j cell, (entries (workWalk M x j) cell (σ.T - 1)).card ≤ V) :
    ∃ Γ : Finset ℕ, ((blockWidth M w : ℝ) * Γ.card ≤ ε * L) ∧
      ∀ π, IsDepPath σ.s σ.T π → LinNet.GFree Γ π →
        π.length ≤ DF M.k (4 * V - 1) (ε / (4 * blockWidth M w * max c 1)) *
          ⌈4 * blockWidth M w * max c 1 / ε⌉₊ := by
  obtain ⟨x₀, hx₀, hV₀⟩ := hentry
  have hwz : (0 : ℤ) < w := by exact_mod_cast hw
  have hβ : 1 ≤ blockWidth M w := le_trans (by norm_num) (six_le_blockWidth hk hw)
  -- the coarse walks of the member `x₀` agree with `σ` before `T`
  have hagree : ∀ j t, t < σ.T → σ.s j t = skel (w : ℤ) (workWalk M x₀ j) t := fun j t ht =>
    ((hx₀.2 t ht).2.1 j).symm
  obtain ⟨Γ, hcost, hpath⟩ := skel_genie_cost hk hV hβ hL hε hT hwz
    (fun j => skel (w : ℤ) (workWalk M x₀ j))
    ⟨workWalk M x₀, workWalk_isWalk _, fun j => rfl, hV₀, fun j => rfl⟩
  exact ⟨Γ, hcost, fun π hπ hfree => hpath π ((isDepPath_congr hagree π).mp hπ) hfree⟩

/-- **Lemmas 4.6 and 4.7 for the block machine of a transposer.** Let `M` have `k ≥ 1` work tapes,
let `V, w ≥ 1`, `ε > 0`, `L = d² b ≥ 1`, and let `σ` be a skeleton at scale `w` with
`T_σ ≤ c (L + 1)` such that some member of `𝒳_σ` has entry at most `V` on every work tape and `M`
transposes every member. With `C = max(c, 1)`, `P = ⌈4 β_w C/ε⌉`,
`D₁ = DF(k, 4V - 1, ε/(4 β_w C))`, `D = D₁ P - 1` and `B = ∑_{h ≤ D} (k + 1)^h`, there is a genie
`Γ` of cost `β_w |Γ| ≤ ε L` such that `|C_Γ(t)| ≤ B` and `|J_Γ(t)| ≤ w B` for every `t` (so
`|N_Γ(q)| ≤ w B`), and every fibre of the revealed word in `𝒳_σ` is a storage code for
`N_Γ(q) = J_Γ(t̂_{tpos q})`. -/
theorem skelClass_storageCode (hk : 1 ≤ M.k) {V w : ℕ} (hV : 1 ≤ V) (hw : 0 < w) {d b : ℕ}
    (hL : 1 ≤ d * d * b) {c ε : ℝ} (hε : 0 < ε) (σ : Skeleton M.k)
    (hT : (σ.T : ℝ) ≤ c * ((d * d * b : ℕ) + 1))
    (hentry : ∃ X ∈ skelClass M w (d * d * b) σ,
      ∀ j cell, (entries (workWalk M (List.ofFn X) j) cell (σ.T - 1)).card ≤ V)
    (htr : ∀ X ∈ skelClass M w (d * d * b) σ, OutputsTranspose M d b X) :
    ∃ Γ : Finset ℕ, ((blockWidth M w : ℝ) * Γ.card ≤ ε * (d * d * b : ℕ)) ∧
      (∀ t,
        (coneV (blockMachine M hw (d * d * b) σ).net Γ t).card ≤
          ∑ h ∈ range (DF M.k (4 * V - 1) (ε / (4 * blockWidth M w * max c 1)) *
            ⌈4 * blockWidth M w * max c 1 / ε⌉₊ - 1 + 1), (M.k + 1) ^ h ∧
        ((blockMachine M hw (d * d * b) σ).coneJ Γ t).card ≤
          w * ∑ h ∈ range (DF M.k (4 * V - 1) (ε / (4 * blockWidth M w * max c 1)) *
            ⌈4 * blockWidth M w * max c 1 / ε⌉₊ - 1 + 1), (M.k + 1) ^ h) ∧
      ∀ g, MotionDepthCodes.IsStorageCode
        (fun q : Fin (d * d * b) =>
          (blockMachine M hw (d * d * b) σ).coneJ Γ (outTime σ w (tpos d b q)))
        ((blockMachine M hw (d * d * b) σ).fibre Γ g) := by
  obtain ⟨X₀, hX₀, hV₀⟩ := hentry
  obtain ⟨Γ, hcost, hpath⟩ := skeleton_genie hk hV hw hL hε σ hT ⟨_, hX₀, hV₀⟩
  have hΓ : ∀ π, IsDepPath σ.s σ.T π → LinNet.GFree Γ π →
      π.length ≤ DF M.k (4 * V - 1) (ε / (4 * blockWidth M w * max c 1)) *
        ⌈4 * blockWidth M w * max c 1 / ε⌉₊ - 1 + 1 := fun π hπ hfree => by
    have := hpath π hπ hfree
    omega
  exact ⟨Γ, hcost, fun t => blockMachine_card_cone_le hw σ hΓ t,
    fun g => blockMachine_isStorageCode_fibre hw σ htr Γ g⟩

end Genie

end MergeDepth
