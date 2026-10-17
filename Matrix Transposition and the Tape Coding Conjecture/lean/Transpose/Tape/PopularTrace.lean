import Transpose.Tape.CutTrace

/-!
# Trace classes: oblivious machines and the popular trace

* `traceClass_of_obliviousOn`: a set of matrix inputs on which the machine is oblivious is a trace
  class; `traceClass_of_oblivious`: in particular all matrix inputs, of size `2^{n²b}`.
* `traceClass_of_mem`: any member of a trace class is a representative.
* `card_small_subsets_le`: a set of size `m` has at most `(m+1)^j` subsets of size `≤ j`.
* `abs_blockOf_le`, `mem_pairRes_curBlock`: every resident block before time `T` has index in
  `[-⌈T/r⌉, ⌈T/r⌉]`.
* `exists_traceClass_of_labels`: the pigeonhole behind every popular trace (any finite labelling
  that, with the halting time, determines the block-level trace); `exists_popular_traceClass_on`: its
  case of the block-level trace on the slots `y ≤ N`, within any set `F₀` of inputs;
  `exists_popular_traceClass`: the case `F₀` = all matrix inputs. The coarse traces of
  `CoarseTrace.lean` are another labelling.
-/

namespace Transpose.Tape.Impl

open Transpose

variable {M : TM}

/-! ### Oblivious machines -/

/-- **An oblivious class is a trace class.** If `M` is oblivious on a set `W` of matrix inputs (time
`T`), then `W` is a trace class, with any of its members as representative. -/
theorem traceClass_of_obliviousOn {n b r T : ℕ} {W : Set (List Bool)} (hW : W ⊆ matrixInputs n b)
    (hobl : ObliviousOn M W T) {w₀ : List Bool} (hw₀ : w₀ ∈ W) : TraceClass M n b r T W w₀ :=
  ⟨hw₀, fun w hw => ⟨hW hw, hobl.1 w hw, fun y _ => by
    simp only [blockTrace, Prod.mk.injEq, oblivious_workTraj hobl hw hw₀,
      oblivious_outRev_length hobl hw hw₀, and_true, true_and]
    exact srcRows_congr fun τ _ => (hobl.2 w hw w₀ hw₀ τ).1⟩⟩

theorem traceClass_of_oblivious {n b r T : ℕ} (hobl : ObliviousOn M (matrixInputs n b) T)
    {w₀ : List Bool} (hw₀ : w₀ ∈ matrixInputs n b) :
    TraceClass M n b r T (matrixInputs n b) w₀ ∧ (matrixInputs n b).ncard = 2 ^ (n * n * b) :=
  ⟨traceClass_of_obliviousOn subset_rfl hobl hw₀, ncard_matrixInputs n b⟩

/-- **Any member of a trace class is a representative.** -/
theorem traceClass_of_mem {n b r T : ℕ} {F : Set (List Bool)} {w₀ w : List Bool}
    (hF : TraceClass M n b r T F w₀) (hw : w ∈ F) : TraceClass M n b r T F w :=
  ⟨hw, fun w' hw' => ⟨(hF.2 w' hw').1, (hF.2 w' hw').2.1,
    sameTrace_trans (hF.2 w' hw').2.2 (sameTrace_symm (hF.2 w hw).2.2)⟩⟩

/-! ### Counting -/

/-- A finite set of size `m` has at most `(m+1)^j` subsets of size at most `j`. -/
theorem card_small_subsets_le {α : Type*} [DecidableEq α] (A : Finset α) (j : ℕ) :
    (A.powerset.filter (fun S => S.card ≤ j)).card ≤ (A.card + 1) ^ j := by
  induction j with
  | zero =>
    calc (A.powerset.filter (fun S => S.card ≤ 0)).card ≤ ({∅} : Finset (Finset α)).card := by
          apply Finset.card_le_card
          intro S hS
          simp only [Finset.mem_filter, Nat.le_zero, Finset.card_eq_zero] at hS
          simp [hS.2]
      _ = (A.card + 1) ^ 0 := by simp
  | succ j ih =>
    have hsub : A.powerset.filter (fun S => S.card ≤ j + 1) ⊆
        insert ∅ ((A ×ˢ A.powerset.filter (fun S => S.card ≤ j)).image
          (fun p => insert p.1 p.2)) := by
      intro S hS
      simp only [Finset.mem_filter, Finset.mem_powerset] at hS
      rcases S.eq_empty_or_nonempty with h | ⟨a, ha⟩
      · rw [h]; exact Finset.mem_insert_self _ _
      · apply Finset.mem_insert_of_mem
        rw [Finset.mem_image]
        refine ⟨(a, S.erase a), ?_, Finset.insert_erase ha⟩
        simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_powerset]
        refine ⟨hS.1 ha, le_trans (Finset.erase_subset _ _) hS.1, ?_⟩
        rw [Finset.card_erase_of_mem ha]; omega
    calc (A.powerset.filter (fun S => S.card ≤ j + 1)).card
        ≤ (insert ∅ ((A ×ˢ A.powerset.filter (fun S => S.card ≤ j)).image
            (fun p => insert p.1 p.2))).card := Finset.card_le_card hsub
      _ ≤ 1 + A.card * (A.card + 1) ^ j := by
          refine le_trans (Finset.card_insert_le _ _) ?_
          rw [Nat.add_comm]
          apply Nat.add_le_add_left
          refine le_trans Finset.card_image_le ?_
          rw [Finset.card_product]
          exact Nat.mul_le_mul_left _ ih
      _ ≤ (A.card + 1) ^ (j + 1) := by
          have : 1 ≤ (A.card + 1) ^ j := Nat.one_le_pow _ _ (by omega)
          rw [pow_succ]
          nlinarith

/-! ### Block indices -/

/-- A block index of a position `|p| < T` lies in `[-⌈T/r⌉, ⌈T/r⌉]`. -/
theorem abs_blockOf_le {r T : ℕ} (hr : 1 ≤ r) {p : ℤ} (hp : |p| < T) :
    |blockOf r p| ≤ numSlots r T := by
  have hr0 : (0 : ℤ) < r := by exact_mod_cast hr
  have hNr : T ≤ numSlots r T * r := by
    unfold numSlots
    have := Nat.lt_div_mul_add (a := T + r - 1) (show 0 < r by omega)
    have h2 := Nat.div_add_mod (T + r - 1) r
    have h3 := Nat.mod_lt (T + r - 1) (show 0 < r by omega)
    rw [Nat.mul_comm] at h2
    omega
  have hNr' : (T : ℤ) ≤ (numSlots r T : ℤ) * r := by exact_mod_cast hNr
  rw [abs_lt] at hp
  rw [abs_le]
  unfold blockOf
  constructor
  · have h1 := Int.lt_ediv_add_one_mul_self p hr0
    by_contra hc
    push Not at hc
    have : p / r + 1 ≤ -(numSlots r T : ℤ) := by omega
    have : (p / r + 1) * r ≤ -(numSlots r T : ℤ) * r := Int.mul_le_mul_of_nonneg_right this hr0.le
    nlinarith
  · have h1 := Int.ediv_mul_le p (ne_of_gt hr0)
    by_contra hc
    push Not at hc
    have : (numSlots r T : ℤ) + 1 ≤ p / r := by omega
    have : ((numSlots r T : ℤ) + 1) * r ≤ p / r * r := Int.mul_le_mul_of_nonneg_right this hr0.le
    nlinarith

/-- Every block resident at a slot is the head's block at some step before `T`. -/
theorem mem_pairRes_curBlock {r T y : ℕ} {h : ℕ → ℤ} {β : ℤ} (hβ : β ∈ pairRes r h T y) :
    ∃ σ < T, β = curBlock r h σ := by
  rw [mem_pairRes] at hβ
  obtain ⟨τ, -, -, hτT, hβτ⟩ := hβ
  rw [mem_residentPair] at hβτ
  rcases hβτ with h1 | h1
  · exact ⟨τ, hτT, h1⟩
  · unfold prevBlock at h1
    split_ifs at h1 with hc
    · refine ⟨lastBlockChange r h τ - 1, ?_, (Option.some.inj h1).symm⟩
      have : lastBlockChange r h τ ≤ τ := Nat.findGreatest_le τ
      omega

/-- The resident blocks of a run halting at `T ≤ T_max` have indices in `[-N, N]`,
`N = ⌈T_max / r⌉`. -/
theorem pairRes_subset_Icc {w : List Bool} {r T Tmax : ℕ} (hr : 1 ≤ r) (hT : T ≤ Tmax)
    (t : Fin M.k) (y : ℕ) :
    pairRes r (fun τ => workTraj M w τ t) T y ⊆
      Finset.Icc (-(numSlots r Tmax : ℤ)) (numSlots r Tmax) := by
  intro β hβ
  obtain ⟨σ, hσT, rfl⟩ := mem_pairRes_curBlock hβ
  have h1 : |workTraj M w σ t| < Tmax := by
    have := abs_workPos_le (M := M) w σ t
    have : (σ : ℤ) < Tmax := by exact_mod_cast lt_of_lt_of_le hσT hT
    simp only [workTraj]; linarith
  have h2 := abs_blockOf_le hr h1
  rw [Finset.mem_Icc]
  exact abs_le.1 h2

/-! ### The popular trace -/

theorem numSlots_mono (r : ℕ) {T T' : ℕ} (h : T ≤ T') : numSlots r T ≤ numSlots r T' :=
  Nat.div_le_div_right (by omega)

/-! ### The popular trace within a set of inputs -/

/-- **The popular class of a labelling** (the pigeonhole behind every popular trace). Let every input
of a nonempty set `F₀` of matrix inputs halt within `T_max` steps, let `κ T` label the inputs halting
at time `T ≤ T_max` by elements of a finite set `B`, and let inputs with the same halting time and
the same label have the same block-level trace. Then some trace class `F ⊆ F₀` (halting time
`T ≤ T_max`) has `|F₀| ≤ (T_max + 1) |B| |F|`. -/
theorem exists_traceClass_of_labels {n b r Tmax : ℕ} {β : Type*} [DecidableEq β]
    {F₀ : Set (List Bool)} (hF₀ : F₀ ⊆ matrixInputs n b) (hne : F₀.Nonempty)
    (hrun : ∀ w ∈ F₀, ∃ T ≤ Tmax, HaltsAt M w T) (κ : ℕ → List Bool → β) (B : Finset β)
    (hκ : ∀ w ∈ F₀, ∀ T ≤ Tmax, HaltsAt M w T → κ T w ∈ B)
    (hsame : ∀ w ∈ F₀, ∀ w' ∈ F₀, ∀ T ≤ Tmax, HaltsAt M w T → HaltsAt M w' T →
      κ T w = κ T w' → SameTrace M n b r T w w') :
    ∃ T ≤ Tmax, ∃ (F : Set (List Bool)) (w₀ : List Bool), TraceClass M n b r T F w₀ ∧ F ⊆ F₀ ∧
      F₀.ncard ≤ (Tmax + 1) * B.card * F.ncard := by
  classical
  choose! Tw hTw hhalt using hrun
  have hfin : F₀.Finite :=
    Set.Finite.subset (by rw [matrixInputs_eq]; exact List.finite_length_eq Bool _) hF₀
  let κ' : List Bool → ℕ × β := fun w => (Tw w, κ (Tw w) w)
  have hκ' : ∀ w ∈ hfin.toFinset, κ' w ∈ Finset.range (Tmax + 1) ×ˢ B := fun w hw => by
    rw [Set.Finite.mem_toFinset] at hw
    exact Finset.mem_product.2 ⟨Finset.mem_range.2 (Nat.lt_succ_of_le (hTw w hw)),
      hκ w hw _ (hTw w hw) (hhalt w hw)⟩
  obtain ⟨w₁, hw₁⟩ := hne
  -- pigeonhole over the labels `(T, κ)`
  obtain ⟨c, -, hc⟩ : ∃ c ∈ Finset.range (Tmax + 1) ×ˢ B, hfin.toFinset.card ≤
      (Finset.range (Tmax + 1) ×ˢ B).card * (hfin.toFinset.filter (fun w => κ' w = c)).card := by
    apply Finset.exists_le_of_sum_le ⟨κ' w₁, hκ' _ (hfin.mem_toFinset.2 hw₁)⟩
    rw [Finset.sum_const, ← Finset.mul_sum, ← Finset.card_eq_sum_card_fiberwise hκ', smul_eq_mul]
  obtain ⟨w₀, hw₀⟩ : (hfin.toFinset.filter (fun w => κ' w = c)).Nonempty := by
    rw [← Finset.card_pos]
    have : 0 < hfin.toFinset.card := Finset.card_pos.2 ⟨w₁, hfin.mem_toFinset.2 hw₁⟩
    exact Nat.pos_of_ne_zero (fun h0 => by rw [h0, Nat.mul_zero] at hc; omega)
  rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hw₀
  have hF : {w | w ∈ F₀ ∧ κ' w = c} = ↑(hfin.toFinset.filter (fun w => κ' w = c)) := by
    ext w; simp
  refine ⟨Tw w₀, hTw w₀ hw₀.1, {w | w ∈ F₀ ∧ κ' w = c}, w₀, ⟨⟨hw₀.1, hw₀.2⟩, fun w hw => ?_⟩,
    fun w hw => hw.1, ?_⟩
  · have hκe : κ' w = κ' w₀ := hw.2.trans hw₀.2.symm
    have hT : Tw w = Tw w₀ := congrArg Prod.fst hκe
    have hh := hhalt w hw.1
    rw [hT] at hh
    refine ⟨hF₀ hw.1, hh, hsame w hw.1 w₀ hw₀.1 _ (hTw w₀ hw₀.1) hh (hhalt w₀ hw₀.1) ?_⟩
    have := congrArg Prod.snd hκe
    simp only [κ'] at this
    rwa [hT] at this
  · rw [hF, Set.ncard_coe_finset, Set.ncard_eq_toFinset_card F₀ hfin]
    simpa only [Finset.card_product, Finset.card_range] using hc

/-- **The popular trace within `F₀`.** If every input of a nonempty set `F₀` of matrix inputs halts
within `T_max` steps, some trace class `F ⊆ F₀` (halting time `T ≤ T_max`) has
`|F₀| ≤ traceCount · |F|`. (The labels: the block-level trace on the slots `y ≤ ⌈T_max/r⌉`.) -/
theorem exists_popular_traceClass_on {n b r Tmax : ℕ} (hr : 1 ≤ r) (hrnb : r ≤ n * b)
    {F₀ : Set (List Bool)} (hF₀ : F₀ ⊆ matrixInputs n b) (hne : F₀.Nonempty)
    (hrun : ∀ w ∈ F₀, ∃ T ≤ Tmax, HaltsAt M w T) :
    ∃ T ≤ Tmax, ∃ (F : Set (List Bool)) (w₀ : List Bool), TraceClass M n b r T F w₀ ∧ F ⊆ F₀ ∧
      F₀.ncard ≤ traceCount M.k n (numSlots r Tmax) Tmax * F.ncard := by
  classical
  set N := numSlots r Tmax
  let resBox : Finset (Finset ℤ) := (Finset.Icc (-(N : ℤ)) N).powerset.filter (fun S => S.card ≤ 3)
  let rowBox : Finset (Finset ℕ) := (Finset.range n).powerset.filter (fun S => S.card ≤ 2)
  let B := Fintype.piFinset (fun _ : Fin (N + 1) =>
    Fintype.piFinset (fun _ : Fin M.k => resBox) ×ˢ rowBox ×ˢ Finset.range (Tmax + 1))
  have hBcard : (Tmax + 1) * B.card ≤ traceCount M.k n N Tmax := by
    have hres : resBox.card ≤ (2 * N + 2) ^ 3 := by
      have := card_small_subsets_le (Finset.Icc (-(N : ℤ)) N) 3
      rwa [Int.card_Icc, show ((N : ℤ) + 1 - -(N : ℤ)).toNat = 2 * N + 1 by omega] at this
    have hrow : rowBox.card ≤ (n + 1) ^ 2 := by
      have := card_small_subsets_le (Finset.range n) 2
      rwa [Finset.card_range] at this
    simp only [B, Finset.card_product, Fintype.card_piFinset, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, Finset.card_range]
    unfold traceCount
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_left
    rw [Nat.mul_assoc ((2 * N + 2) ^ (3 * M.k))]
    apply Nat.mul_le_mul _ (Nat.mul_le_mul_right _ hrow)
    rw [pow_mul]
    exact Nat.pow_le_pow_left hres _
  obtain ⟨T, hT, F, w₀, hF, hsub, hc⟩ := exists_traceClass_of_labels (r := r) hF₀ hne hrun
    (fun T w (y : Fin (N + 1)) => blockTrace M n b r T w y.1) B
    (fun w _ T hT hh => Fintype.mem_piFinset.2 fun y => by
      simp only [resBox, rowBox, Finset.mem_product, Finset.mem_filter, Finset.mem_powerset,
        Fintype.mem_piFinset, Finset.mem_range, blockTrace]
      refine ⟨fun t => ⟨pairRes_subset_Icc hr hT t y.1,
        (pairRes_admissible (unitSteps_workTraj M w t) hr T).2 y.1⟩,
        ⟨Finset.filter_subset _ _, rows_in_slot_card_le M w hrnb T y.1⟩, ?_⟩
      rcases le_or_gt (y.1 * r) T with h | h
      · have := outLen_le_self (M := M) w (y.1 * r); omega
      · rw [run_of_le_of_none hh.2 h.le]; have := outLen_le_self (M := M) w T; omega)
    (fun w _ w' _ T hT _ _ hκ y hy =>
      congrFun hκ ⟨y, Nat.lt_succ_of_le (le_trans hy (numSlots_mono r hT))⟩)
  exact ⟨T, hT, F, w₀, hF, hsub, le_trans hc (Nat.mul_le_mul_right _ hBcard)⟩

/-- **The popular trace.** -/
theorem exists_popular_traceClass {n b r Tmax : ℕ} (hr : 1 ≤ r) (hrnb : r ≤ n * b)
    (hrun : ∀ w ∈ matrixInputs n b, ∃ T ≤ Tmax, HaltsAt M w T) :
    ∃ T ≤ Tmax, ∃ (F : Set (List Bool)) (w₀ : List Bool), TraceClass M n b r T F w₀ ∧
      2 ^ (n * n * b) ≤ traceCount M.k n (numSlots r Tmax) Tmax * F.ncard := by
  obtain ⟨T, hT, F, w₀, hF, -, hc⟩ := exists_popular_traceClass_on hr hrnb subset_rfl
    ⟨_, ⟨fun _ _ _ => false, rfl⟩⟩ hrun
  exact ⟨T, hT, F, w₀, hF, by rwa [ncard_matrixInputs] at hc⟩

end Transpose.Tape.Impl
