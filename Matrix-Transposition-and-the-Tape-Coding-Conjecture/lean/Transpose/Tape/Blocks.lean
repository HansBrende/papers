import Transpose.Tape.Run

/-!
# Block bookkeeping

* Block arithmetic, unit steps, (V2), and slot geometry.
* The resident pair, the Residency Lemma, touched residency, pair changes and (P2); the pair
  residency before `T` reads the walk only before `T` (`pairRes_eq_of_agree`).
* The Charging Lemma: `entry_slot` (the `y*` argument, also used by the Block Locality Lemma),
  `entryTimes_charged` (the charging step, containment form) and `entryTimes_card_le`.
-/

namespace Transpose.Tape.Impl

open Transpose

/-! ### Block arithmetic -/

theorem blockOf_spec {r : ℕ} (hr : 1 ≤ r) (p : ℤ) :
    blockOf r p * r ≤ p ∧ p < (blockOf r p + 1) * r := by
  have hr' : (0 : ℤ) < r := by exact_mod_cast hr
  exact ⟨Int.ediv_mul_le p (ne_of_gt hr'), Int.lt_ediv_add_one_mul_self p hr'⟩

theorem blockOf_eq_iff {r : ℕ} (hr : 1 ≤ r) {p β : ℤ} :
    blockOf r p = β ↔ β * r ≤ p ∧ p < (β + 1) * r := by
  constructor
  · rintro rfl; exact blockOf_spec hr p
  · rintro ⟨h1, h2⟩
    have hr' : (0 : ℤ) < r := by exact_mod_cast hr
    have a1 : β ≤ blockOf r p := (Int.le_ediv_iff_mul_le hr').2 h1
    have a2 : blockOf r p < β + 1 := (Int.ediv_lt_iff_lt_mul hr').2 h2
    omega

theorem blockOf_mono {r : ℕ} {p q : ℤ} (h : p ≤ q) : blockOf r p ≤ blockOf r q := by
  unfold blockOf
  rcases Nat.eq_zero_or_pos r with h0 | hpos
  · simp [h0]
  · exact Int.ediv_le_ediv (by exact_mod_cast hpos) h

theorem blockOf_add_r {r : ℕ} (hr : 1 ≤ r) (p : ℤ) : blockOf r (p + r) = blockOf r p + 1 := by
  have hr' : (r : ℤ) ≠ 0 := by
    have : (0 : ℤ) < r := by exact_mod_cast hr
    omega
  unfold blockOf
  rw [show p + (r : ℤ) = p + 1 * r by ring, Int.add_mul_ediv_right _ _ hr']

/-- Positions at most `r` apart have blocks at most one apart. -/
theorem blockOf_close {r : ℕ} (hr : 1 ≤ r) {p q : ℤ} (h : |p - q| ≤ r) :
    |blockOf r p - blockOf r q| ≤ 1 := by
  rw [abs_le] at h ⊢
  rcases le_total p q with hpq | hqp
  · have h1 := blockOf_mono (r := r) hpq
    have h2 := blockOf_mono (r := r) (show q ≤ p + r by linarith)
    rw [blockOf_add_r hr] at h2
    constructor <;> linarith
  · have h1 := blockOf_mono (r := r) hqp
    have h2 := blockOf_mono (r := r) (show p ≤ q + r by linarith)
    rw [blockOf_add_r hr] at h2
    constructor <;> linarith

/-- Blocks two apart force positions more than `r` apart. -/
theorem far_of_blockOf {r : ℕ} (hr : 1 ≤ r) {p q : ℤ} (h : blockOf r p + 2 ≤ blockOf r q) :
    p + r + 1 ≤ q := by
  obtain ⟨-, hp⟩ := blockOf_spec hr p
  obtain ⟨hq, -⟩ := blockOf_spec hr q
  have hr0 : (0 : ℤ) ≤ r := by positivity
  have := Int.mul_le_mul_of_nonneg_right h hr0
  nlinarith

/-- Entering block `β + 1` from block `β` by a unit step lands on its first cell. -/
theorem enter_up {r : ℕ} (hr : 1 ≤ r) {p q : ℤ} (hstep : |q - p| ≤ 1)
    (hb : blockOf r q = blockOf r p + 1) : q = (blockOf r p + 1) * r := by
  obtain ⟨-, hp⟩ := blockOf_spec hr p
  obtain ⟨hq, -⟩ := blockOf_spec hr q
  rw [hb] at hq
  rw [abs_le] at hstep
  have : q ≤ p + 1 := by linarith
  omega

/-- Entering block `β - 1` from block `β` by a unit step lands on its last cell. -/
theorem enter_down {r : ℕ} (hr : 1 ≤ r) {p q : ℤ} (hstep : |q - p| ≤ 1)
    (hb : blockOf r q = blockOf r p - 1) : q = blockOf r p * r - 1 := by
  obtain ⟨hp, -⟩ := blockOf_spec hr p
  obtain ⟨-, hq⟩ := blockOf_spec hr q
  rw [hb, sub_add_cancel] at hq
  rw [abs_le] at hstep
  have : p - 1 ≤ q := by linarith
  omega

/-! ### Unit steps -/

theorem shift_dist (d : Dir) (p : ℤ) : |d.shift p - p| ≤ 1 := by
  cases d <;> simp [Dir.shift]

theorem unitSteps_inTraj (M : TM) (w : List Bool) : UnitSteps (inTraj M w) := by
  intro τ
  simp only [inTraj]
  rw [run_succ_inPos]
  rcases transAt M w τ with _ | ⟨s, d, acts, o⟩
  · simp
  · exact shift_dist d _

theorem unitSteps_workTraj (M : TM) (w : List Bool) (t : Fin M.k) :
    UnitSteps (fun τ => workTraj M w τ t) := by
  intro τ
  simp only [workTraj]
  rw [run_succ_workPos]
  rcases transAt M w τ with _ | ⟨s, d, acts, o⟩
  · simp
  · exact shift_dist _ _

theorem unitSteps_dist {h : ℕ → ℤ} (hh : UnitSteps h) {τ τ' : ℕ} (hle : τ ≤ τ') :
    |h τ' - h τ| ≤ (τ' : ℤ) - τ := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hle
  clear hle
  induction j with
  | zero => simp
  | succ j ih =>
    have h1 := hh (τ + j)
    have h2 : h (τ + (j + 1)) - h τ = (h (τ + j + 1) - h (τ + j)) + (h (τ + j) - h τ) := by
      rw [← Nat.add_assoc]; ring
    rw [h2]
    calc _ ≤ |h (τ + j + 1) - h (τ + j)| + |h (τ + j) - h τ| := abs_add_le _ _
      _ ≤ 1 + (((τ + j : ℕ) : ℤ) - τ) := add_le_add h1 ih
      _ = ((τ + (j + 1) : ℕ) : ℤ) - τ := by push_cast; ring

theorem unitSteps_dist' {h : ℕ → ℤ} (hh : UnitSteps h) (τ τ' : ℕ) :
    |h τ' - h τ| ≤ |(τ' : ℤ) - τ| := by
  rcases le_total τ τ' with hle | hle
  · exact le_trans (unitSteps_dist hh hle) (le_abs_self _)
  · rw [abs_sub_comm, abs_sub_comm (τ' : ℤ)]
    exact le_trans (unitSteps_dist hh hle) (le_abs_self _)

/-! ### (V2) -/

theorem slot_block_step {r : ℕ} {h : ℕ → ℤ} (hh : UnitSteps h) (hr : 1 ≤ r) (y : ℕ) :
    |curBlock r h ((y + 1) * r) - curBlock r h (y * r)| ≤ 1 := by
  apply blockOf_close hr
  have := unitSteps_dist hh (show y * r ≤ (y + 1) * r by nlinarith)
  have e : (((y + 1) * r : ℕ) : ℤ) - ((y * r : ℕ) : ℤ) = r := by push_cast; ring
  rw [e] at this
  exact this

/-- Discrete intermediate values for a sequence with steps of size at most one. -/
theorem discrete_ivt {f : ℕ → ℤ} (hf : ∀ y, |f (y + 1) - f y| ≤ 1) {y₁ y₂ : ℕ} (hy : y₁ ≤ y₂)
    {β : ℤ} (hβ : min (f y₁) (f y₂) ≤ β ∧ β ≤ max (f y₁) (f y₂)) :
    ∃ y, y₁ ≤ y ∧ y ≤ y₂ ∧ f y = β := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hy
  clear hy
  induction j generalizing β with
  | zero => exact ⟨y₁, le_rfl, by simp, by simp at hβ; omega⟩
  | succ j ih =>
    have hstep := hf (y₁ + j)
    rw [abs_le] at hstep
    by_cases hin : min (f y₁) (f (y₁ + j)) ≤ β ∧ β ≤ max (f y₁) (f (y₁ + j))
    · obtain ⟨y, h1, h2, h3⟩ := ih hin
      exact ⟨y, h1, by omega, h3⟩
    · refine ⟨y₁ + (j + 1), by omega, le_rfl, ?_⟩
      rw [← Nat.add_assoc] at hβ ⊢
      simp only [min_def, max_def] at hβ hin
      split_ifs at hβ hin <;> omega

theorem exists_slot_block_eq {r : ℕ} {h : ℕ → ℤ} (hh : UnitSteps h) (hr : 1 ≤ r) {y₁ y₂ : ℕ}
    (hy : y₁ ≤ y₂) {β : ℤ}
    (hβ : min (curBlock r h (y₁ * r)) (curBlock r h (y₂ * r)) ≤ β ∧
      β ≤ max (curBlock r h (y₁ * r)) (curBlock r h (y₂ * r))) :
    ∃ y, y₁ ≤ y ∧ y ≤ y₂ ∧ curBlock r h (y * r) = β :=
  discrete_ivt (f := fun y => curBlock r h (y * r)) (fun y => slot_block_step hh hr y) hy hβ

/-! ### Slot geometry -/

theorem mem_slotOf {r T y τ : ℕ} : τ ∈ slotOf r T y ↔ y * r ≤ τ ∧ τ < y * r + r ∧ τ < T := by
  simp [slotOf, Finset.mem_Ico]

theorem slot_div {r y τ : ℕ} (h1 : y * r ≤ τ) (h2 : τ < y * r + r) : τ / r = y := by
  apply Nat.div_eq_of_lt_le
  · rw [Nat.mul_comm] at h1; linarith [Nat.mul_comm y r]
  · rw [Nat.succ_mul]; omega

theorem mem_slotOf_div {r T τ : ℕ} (hr : 1 ≤ r) (hτ : τ < T) : τ ∈ slotOf r T (τ / r) := by
  rw [mem_slotOf]
  refine ⟨Nat.div_mul_le_self τ r, ?_, hτ⟩
  have := Nat.lt_div_mul_add (a := τ) (show 0 < r by omega)
  linarith

/-- Positions within one slot are at most `r - 1` apart. -/
theorem slot_dist {r : ℕ} {h : ℕ → ℤ} (hh : UnitSteps h) {y τ τ' : ℕ}
    (h1 : y * r ≤ τ) (h2 : τ < y * r + r) (h1' : y * r ≤ τ') (h2' : τ' < y * r + r) :
    |h τ' - h τ| ≤ (r : ℤ) - 1 := by
  have h3 := unitSteps_dist' hh τ τ'
  have h4 : |(τ' : ℤ) - τ| ≤ (r : ℤ) - 1 := by
    rw [abs_le]; constructor <;> omega
  linarith

/-- Within a slot the head's block stays within `±1` of its block at the first step. -/
theorem slot_block_near {r : ℕ} {h : ℕ → ℤ} (hh : UnitSteps h) (hr : 1 ≤ r) {y τ : ℕ}
    (h1 : y * r ≤ τ) (h2 : τ < y * r + r) :
    |curBlock r h τ - curBlock r h (y * r)| ≤ 1 := by
  apply blockOf_close hr
  have := slot_dist hh (le_refl (y * r)) (by omega : y * r < y * r + r) h1 h2
  linarith

/-- Within a slot the head never visits two blocks that are two apart. -/
theorem slot_not_both {r : ℕ} {h : ℕ → ℤ} (hh : UnitSteps h) (hr : 1 ≤ r) {y τ τ' : ℕ}
    (h1 : y * r ≤ τ) (h2 : τ < y * r + r) (h1' : y * r ≤ τ') (h2' : τ' < y * r + r)
    (hlow : curBlock r h τ + 2 ≤ curBlock r h τ') : False := by
  have hfar := far_of_blockOf hr hlow
  have hd := slot_dist hh h1 h2 h1' h2'
  have := le_abs_self (h τ' - h τ)
  linarith

/-! ### The resident pair -/

section Pair

variable {r : ℕ} {h : ℕ → ℤ}

theorem lastBlockChange_zero : lastBlockChange r h 0 = 0 := by
  simp [lastBlockChange]

theorem lastBlockChange_succ (τ : ℕ) :
    lastBlockChange r h (τ + 1) =
      if curBlock r h (τ + 1) ≠ curBlock r h τ then τ + 1 else lastBlockChange r h τ := by
  unfold lastBlockChange
  rw [Nat.findGreatest_succ]
  simp

theorem prevBlock_zero : prevBlock r h 0 = none := by
  simp [prevBlock, lastBlockChange_zero]

theorem prevBlock_succ (τ : ℕ) :
    prevBlock r h (τ + 1) =
      if curBlock r h (τ + 1) ≠ curBlock r h τ then some (curBlock r h τ) else prevBlock r h τ := by
  unfold prevBlock
  rw [lastBlockChange_succ]
  split_ifs with h1 h2 <;> simp_all

theorem residentPair_succ (τ : ℕ) :
    residentPair r h (τ + 1) =
      if curBlock r h (τ + 1) ≠ curBlock r h τ then {curBlock r h (τ + 1), curBlock r h τ}
      else residentPair r h τ := by
  unfold residentPair
  rw [prevBlock_succ]
  split_ifs with h1
  · simp
  · push Not at h1
    rw [h1]

theorem cur_mem_residentPair (τ : ℕ) : curBlock r h τ ∈ residentPair r h τ :=
  Finset.mem_insert_self _ _

theorem mem_residentPair {τ : ℕ} {β : ℤ} :
    β ∈ residentPair r h τ ↔ β = curBlock r h τ ∨ prevBlock r h τ = some β := by
  simp [residentPair, Option.mem_toFinset, eq_comm]

/-- The previous block is adjacent to and different from the current one. -/
theorem prevBlock_adj (hh : UnitSteps h) (hr : 1 ≤ r) :
    ∀ τ β, prevBlock r h τ = some β → β ≠ curBlock r h τ ∧ |β - curBlock r h τ| ≤ 1 := by
  intro τ
  induction τ with
  | zero => intro β hβ; simp [prevBlock_zero] at hβ
  | succ τ ih =>
    intro β hβ
    rw [prevBlock_succ] at hβ
    split_ifs at hβ with hc
    · simp only [Option.some.injEq] at hβ
      subst hβ
      refine ⟨Ne.symm hc, ?_⟩
      rw [abs_sub_comm]
      exact blockOf_close hr (le_trans (hh τ) (by exact_mod_cast hr))
    · push Not at hc
      rw [hc]
      exact ih β hβ

/-- `R_y` contains the head's block at every step of the slot. -/
theorem cur_mem_pairRes {T τ : ℕ} (hr : 1 ≤ r) (hτ : τ < T) :
    curBlock r h τ ∈ pairRes r h T (τ / r) :=
  Finset.mem_biUnion.2 ⟨τ, mem_slotOf_div hr hτ, cur_mem_residentPair τ⟩

theorem mem_pairRes {T y : ℕ} {β : ℤ} :
    β ∈ pairRes r h T y ↔ ∃ τ, y * r ≤ τ ∧ τ < y * r + r ∧ τ < T ∧ β ∈ residentPair r h τ := by
  simp only [pairRes, Finset.mem_biUnion, mem_slotOf]
  constructor
  · rintro ⟨τ, ⟨h1, h2, h3⟩, h4⟩; exact ⟨τ, h1, h2, h3, h4⟩
  · rintro ⟨τ, h1, h2, h3, h4⟩; exact ⟨τ, ⟨h1, h2, h3⟩, h4⟩

/-- The resident pair at `τ` reads the walk only on `[0, τ]`. -/
theorem residentPair_eq_of_agree {h' : ℕ → ℤ} {τ : ℕ} (he : ∀ σ ≤ τ, h σ = h' σ) :
    residentPair r h τ = residentPair r h' τ := by
  induction τ with
  | zero => simp [residentPair, prevBlock_zero, curBlock, he 0 le_rfl]
  | succ τ ih =>
    have e1 : curBlock r h (τ + 1) = curBlock r h' (τ + 1) := by rw [curBlock, he _ le_rfl]; rfl
    have e0 : curBlock r h τ = curBlock r h' τ := by rw [curBlock, he τ (by omega)]; rfl
    rw [residentPair_succ, residentPair_succ, ih (fun σ hσ => he σ (by omega)), e1, e0]

/-- **The pair residency reads the walk only before `T`**: walks that agree before `T` have the same
residency `R_y` at every slot. -/
theorem pairRes_eq_of_agree {h' : ℕ → ℤ} {T : ℕ} (he : ∀ σ < T, h σ = h' σ) (y : ℕ) :
    pairRes r h T y = pairRes r h' T y :=
  Finset.biUnion_congr rfl fun _ hτ =>
    residentPair_eq_of_agree fun σ hσ => he σ (lt_of_le_of_lt hσ (mem_slotOf.1 hτ).2.2)

/-- **The Residency Lemma**: the blocks resident at slot `y` lie within `±1` of the head's block at
the first step of the slot (so there are at most three, `pairRes_admissible`). -/
theorem pairRes_subset (hh : UnitSteps h) (hr : 1 ≤ r) (T y : ℕ) :
    pairRes r h T y ⊆
      {curBlock r h (y * r) - 1, curBlock r h (y * r), curBlock r h (y * r) + 1} := by
  intro β hβ
  rw [mem_pairRes] at hβ
  obtain ⟨τ, h1, h2, -, hβ⟩ := hβ
  -- every pair at a step of the slot is within ±1 of β₀
  set β₀ := curBlock r h (y * r)
  suffices key : ∀ j, y * r + j < y * r + r →
      ∀ β ∈ residentPair r h (y * r + j), |β - β₀| ≤ 1 by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h1
    have := key j h2 β hβ
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rw [abs_le] at this
    omega
  intro j
  induction j with
  | zero =>
    intro _ β hβ
    rw [Nat.add_zero, mem_residentPair] at hβ
    rcases hβ with rfl | hβ
    · simp [β₀]
    · exact (prevBlock_adj hh hr _ β hβ).2
  | succ j ih =>
    intro hj β hβ
    rw [← Nat.add_assoc, residentPair_succ] at hβ
    split_ifs at hβ with hc
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hβ
      rcases hβ with rfl | rfl
      · exact slot_block_near hh hr (by omega) (by omega)
      · exact slot_block_near hh hr (by omega) (by omega)
    · exact ih (by omega) β hβ

theorem pairRes_admissible (hh : UnitSteps h) (hr : 1 ≤ r) (T : ℕ) :
    AdmissibleRes r h T (pairRes r h T) 3 := by
  refine ⟨fun τ hτ => cur_mem_pairRes hr hτ, fun y => ?_⟩
  calc (pairRes r h T y).card
      ≤ ({curBlock r h (y * r) - 1, curBlock r h (y * r), curBlock r h (y * r) + 1} :
          Finset ℤ).card := Finset.card_le_card (pairRes_subset hh hr T y)
    _ ≤ 3 := by
        refine le_trans (Finset.card_insert_le _ _) ?_
        refine le_trans (Nat.succ_le_succ (Finset.card_insert_le _ _)) ?_
        simp

end Pair

/-! ### Touched residency, pair changes, (P2) -/

section P2

variable {r : ℕ} {h : ℕ → ℤ}

/-- Times at most `r` apart have blocks at most one apart. -/
theorem cur_close (hh : UnitSteps h) (hr : 1 ≤ r) {τ τ' : ℕ} (h1 : τ ≤ τ' + r)
    (h2 : τ' ≤ τ + r) : |curBlock r h τ - curBlock r h τ'| ≤ 1 := by
  apply blockOf_close hr
  have := unitSteps_dist' hh τ' τ
  have h3 : |(τ : ℤ) - τ'| ≤ r := by rw [abs_le]; constructor <;> omega
  linarith

theorem mem_touchRes {T y : ℕ} {β : ℤ} :
    β ∈ touchRes r h T y ↔ ∃ τ, y * r ≤ τ ∧ τ < y * r + r ∧ τ < T ∧ curBlock r h τ = β := by
  simp only [touchRes, Finset.mem_image, mem_slotOf]
  constructor
  · rintro ⟨τ, ⟨h1, h2, h3⟩, h4⟩; exact ⟨τ, h1, h2, h3, h4⟩
  · rintro ⟨τ, h1, h2, h3, h4⟩; exact ⟨τ, ⟨h1, h2, h3⟩, h4⟩

theorem touchRes_admissible (hh : UnitSteps h) (hr : 1 ≤ r) (T : ℕ) :
    AdmissibleRes r h T (touchRes r h T) 2 ∧
      ∀ y, touchRes r h T y ⊆
        {curBlock r h (y * r) - 1, curBlock r h (y * r), curBlock r h (y * r) + 1} := by
  have hsub : ∀ y, touchRes r h T y ⊆
      {curBlock r h (y * r) - 1, curBlock r h (y * r), curBlock r h (y * r) + 1} := by
    intro y β hβ
    rw [mem_touchRes] at hβ
    obtain ⟨τ, h1, h2, -, rfl⟩ := hβ
    have := slot_block_near hh hr h1 h2
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rw [abs_le] at this; omega
  refine ⟨⟨fun τ hτ => ?_, fun y => ?_⟩, hsub⟩
  · rw [mem_touchRes]
    exact ⟨τ, (mem_slotOf.1 (mem_slotOf_div hr hτ)).1, (mem_slotOf.1 (mem_slotOf_div hr hτ)).2.1,
      hτ, rfl⟩
  · -- at most two blocks: no two touched blocks are two apart
    by_cases hne : (touchRes r h T y).Nonempty
    · set m := (touchRes r h T y).min' hne
      have hsub2 : touchRes r h T y ⊆ {m, m + 1} := by
        intro β hβ
        have hmβ : m ≤ β := Finset.min'_le _ _ hβ
        have hm : m ∈ touchRes r h T y := Finset.min'_mem _ _
        rw [mem_touchRes] at hβ hm
        obtain ⟨τ, h1, h2, -, rfl⟩ := hβ
        obtain ⟨τ', h1', h2', -, hm'⟩ := hm
        simp only [Finset.mem_insert, Finset.mem_singleton]
        by_contra hc
        push Not at hc
        exact slot_not_both hh hr h1' h2' h1 h2 (by rw [hm']; omega)
      calc (touchRes r h T y).card ≤ ({m, m + 1} : Finset ℤ).card := Finset.card_le_card hsub2
        _ ≤ 2 := by refine le_trans (Finset.card_insert_le _ _) ?_; simp
    · rw [Finset.not_nonempty_iff_eq_empty.1 hne]; simp

theorem touchRes_begin_unique (hh : UnitSteps h) (hr : 1 ≤ r) (T y : ℕ) {β β' : ℤ}
    (h₁ : β ∈ touchRes r h T (y + 1)) (h₁' : β ∉ touchRes r h T y)
    (h₂ : β' ∈ touchRes r h T (y + 1)) (h₂' : β' ∉ touchRes r h T y) : β = β' := by
  rw [mem_touchRes] at h₁ h₂
  obtain ⟨τ, a1, a2, a3, rfl⟩ := h₁
  obtain ⟨τ', b1, b2, b3, rfl⟩ := h₂
  -- the last step of slot y
  have hlast : curBlock r h ((y + 1) * r - 1) ∈ touchRes r h T y := by
    rw [mem_touchRes]
    refine ⟨(y + 1) * r - 1, ?_, ?_, ?_, rfl⟩
    · rw [Nat.succ_mul]; omega
    · rw [Nat.succ_mul] at a1 ⊢; omega
    · omega
  have hγ : curBlock r h τ ≠ curBlock r h ((y + 1) * r - 1) := fun e => h₁' (e ▸ hlast)
  have hγ' : curBlock r h τ' ≠ curBlock r h ((y + 1) * r - 1) := fun e => h₂' (e ▸ hlast)
  have c1 := cur_close (h := h) hh hr (τ := τ) (τ' := (y + 1) * r - 1)
    (by rw [Nat.succ_mul] at a2 ⊢; omega) (by rw [Nat.succ_mul] at a1 ⊢; omega)
  have c2 := cur_close (h := h) hh hr (τ := τ') (τ' := (y + 1) * r - 1)
    (by rw [Nat.succ_mul] at b2 ⊢; omega) (by rw [Nat.succ_mul] at b1 ⊢; omega)
  have c3 := cur_close (h := h) hh hr (τ := τ) (τ' := τ')
    (by rw [Nat.succ_mul] at a2 b1; omega) (by rw [Nat.succ_mul] at a1 b2; omega)
  rw [abs_le] at c1 c2 c3
  omega

theorem touchRes_end_unique (hh : UnitSteps h) (hr : 1 ≤ r) {T : ℕ} (y : ℕ)
    (hy : (y + 1) * r < T) {β β' : ℤ}
    (h₁ : β ∈ touchRes r h T y) (h₁' : β ∉ touchRes r h T (y + 1))
    (h₂ : β' ∈ touchRes r h T y) (h₂' : β' ∉ touchRes r h T (y + 1)) : β = β' := by
  rw [mem_touchRes] at h₁ h₂
  obtain ⟨τ, a1, a2, a3, rfl⟩ := h₁
  obtain ⟨τ', b1, b2, b3, rfl⟩ := h₂
  have hfirst : curBlock r h ((y + 1) * r) ∈ touchRes r h T (y + 1) := by
    rw [mem_touchRes]
    exact ⟨(y + 1) * r, le_rfl, by omega, hy, rfl⟩
  have hγ : curBlock r h τ ≠ curBlock r h ((y + 1) * r) := fun e => h₁' (e ▸ hfirst)
  have hγ' : curBlock r h τ' ≠ curBlock r h ((y + 1) * r) := fun e => h₂' (e ▸ hfirst)
  have c1 := cur_close (h := h) hh hr (τ := τ) (τ' := (y + 1) * r)
    (by rw [Nat.succ_mul]; omega) (by rw [Nat.succ_mul]; omega)
  have c2 := cur_close (h := h) hh hr (τ := τ') (τ' := (y + 1) * r)
    (by rw [Nat.succ_mul]; omega) (by rw [Nat.succ_mul]; omega)
  have c3 := cur_close (h := h) hh hr (τ := τ) (τ' := τ') (by omega) (by omega)
  rw [abs_le] at c1 c2 c3
  omega

theorem pair_succ_of_not_change {τ : ℕ} (hpc : ¬ PairChange r h (τ + 1)) :
    residentPair r h (τ + 1) = residentPair r h τ := by
  rw [residentPair_succ]
  split_ifs with hc
  · have hmem : curBlock r h (τ + 1) ∈ residentPair r h τ := by
      by_contra hn; exact hpc ⟨by omega, by simpa using hn⟩
    rw [mem_residentPair] at hmem
    rcases hmem with e | hprev
    · exact absurd e hc
    · ext β
      rw [mem_residentPair]
      simp only [Finset.mem_insert, Finset.mem_singleton, hprev, Option.some.injEq]
      tauto
  · rfl

theorem pair_succ_of_change {τ : ℕ} (hpc : PairChange r h (τ + 1)) :
    residentPair r h (τ + 1) = {curBlock r h (τ + 1), curBlock r h τ} ∧
      curBlock r h (τ + 1) ≠ curBlock r h τ := by
  have hne : curBlock r h (τ + 1) ≠ curBlock r h τ := by
    intro e; apply hpc.2; simp only [Nat.add_sub_cancel]; rw [e]; exact cur_mem_residentPair τ
  refine ⟨?_, hne⟩
  rw [residentPair_succ, ite_eq_left hne]

/-- Entering the pair happens only at a pair change, with the current block. -/
theorem entry_is_change {τ : ℕ} {β : ℤ} (h0 : β ∉ residentPair r h τ)
    (h1 : β ∈ residentPair r h (τ + 1)) : PairChange r h (τ + 1) ∧ β = curBlock r h (τ + 1) := by
  by_cases hpc : PairChange r h (τ + 1)
  · refine ⟨hpc, ?_⟩
    rw [(pair_succ_of_change hpc).1] at h1
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1
    rcases h1 with e | e
    · exact e
    · exact absurd (e ▸ cur_mem_residentPair τ) h0
  · rw [pair_succ_of_not_change hpc] at h1; exact absurd h1 h0

/-- Leaving the pair happens only at a pair change, with the previous block. -/
theorem exit_is_change {τ : ℕ} {β : ℤ} (h0 : β ∈ residentPair r h τ)
    (h1 : β ∉ residentPair r h (τ + 1)) : PairChange r h (τ + 1) ∧ prevBlock r h τ = some β := by
  by_cases hpc : PairChange r h (τ + 1)
  · refine ⟨hpc, ?_⟩
    rw [(pair_succ_of_change hpc).1] at h1
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h1
    rw [mem_residentPair] at h0
    rcases h0 with e | e
    · exact absurd e h1.2
    · exact e
  · rw [pair_succ_of_not_change hpc] at h1; exact absurd h0 h1

theorem pair_const {a : ℕ} : ∀ j, (∀ ρ, a < ρ → ρ ≤ a + j → ¬ PairChange r h ρ) →
    residentPair r h (a + j) = residentPair r h a := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hno
    rw [← Nat.add_assoc,
      pair_succ_of_not_change (τ := a + j) (hno (a + j + 1) (by omega) (by omega))]
    exact ih (fun ρ h1 h2 => hno ρ h1 (by omega))

/-- **Pair changes are at least `r` steps apart.** -/
theorem pairChange_spacing (hh : UnitSteps h) (hr : 1 ≤ r) {σ₁ σ₂ : ℕ}
    (h₁ : PairChange r h σ₁) (h₂ : PairChange r h σ₂) (hlt : σ₁ < σ₂) : σ₁ + r ≤ σ₂ := by
  classical
  -- the first pair change after σ₁
  have hex : ∃ σ, σ₁ < σ ∧ PairChange r h σ := ⟨σ₂, hlt, h₂⟩
  let σ₃ := Nat.find hex
  have hσ₃ : σ₁ < σ₃ ∧ PairChange r h σ₃ := Nat.find_spec hex
  have hσ₃le : σ₃ ≤ σ₂ := Nat.find_min' hex ⟨hlt, h₂⟩
  have hmin : ∀ ρ, σ₁ < ρ → ρ < σ₃ → ¬ PairChange r h ρ := fun ρ h1 h2 hp =>
    Nat.find_min hex h2 ⟨h1, hp⟩
  suffices σ₁ + r ≤ σ₃ by omega
  have hσ₁1 := h₁.1
  obtain ⟨s, rfl⟩ : ∃ s, σ₁ = s + 1 := ⟨σ₁ - 1, by omega⟩
  obtain ⟨hpair₁, hne₁⟩ := pair_succ_of_change h₁
  -- the pair stays {β', β} until σ₃ - 1
  have hconst := pair_const (r := r) (h := h) (a := s + 1) (σ₃ - 1 - (s + 1))
    (fun ρ h1 h2 => hmin ρ h1 (by omega))
  rw [show s + 1 + (σ₃ - 1 - (s + 1)) = σ₃ - 1 by omega, hpair₁] at hconst
  have hcur3 := cur_mem_residentPair (r := r) (h := h) (σ₃ - 1)
  rw [hconst] at hcur3
  have hnot3 := hσ₃.2.2
  rw [hconst] at hnot3
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcur3 hnot3
  -- block steps
  have hadj₁ := cur_close (h := h) hh hr (τ := s + 1) (τ' := s) (by omega) (by omega)
  have hadj₃ := cur_close (h := h) hh hr (τ := σ₃) (τ' := σ₃ - 1) (by omega) (by omega)
  -- distances in time and space
  have hdist := unitSteps_dist hh (le_of_lt hσ₃.1)
  have hstep₁ := hh s
  set β := curBlock r h s
  set β' := curBlock r h (s + 1)
  set c := curBlock r h σ₃
  have hr' : (1 : ℤ) ≤ r := by exact_mod_cast hr
  rw [abs_le] at hadj₁ hadj₃ hdist hstep₁
  -- the entry cell at σ₁
  have hspec₃ := blockOf_spec hr (h σ₃)
  change c * r ≤ h σ₃ ∧ h σ₃ < (c + 1) * r at hspec₃
  have hσ₃cast : ((σ₃ : ℤ) - (s + 1 : ℕ)) ≥ r := by
    rcases (show β' = β + 1 ∨ β' = β - 1 by omega) with hup | hdown
    · have hent : h (s + 1) = (β + 1) * r :=
        enter_up hr (p := h s) (q := h (s + 1)) (by rw [abs_le]; exact hstep₁) hup
      have hc : c = β - 1 ∨ c = β + 2 := by omega
      rcases hc with hc | hc
      · rw [hc] at hspec₃
        have e : (β - 1 + 1) * (r : ℤ) = β * r := by ring
        rw [e] at hspec₃
        have e2 : (β + 1) * (r : ℤ) = β * r + r := by ring
        rw [e2] at hent
        linarith
      · rw [hc] at hspec₃
        have e : (β + 2) * (r : ℤ) = β * r + 2 * r := by ring
        rw [e] at hspec₃
        have e2 : (β + 1) * (r : ℤ) = β * r + r := by ring
        rw [e2] at hent
        linarith
    · have hent : h (s + 1) = β * r - 1 :=
        enter_down hr (p := h s) (q := h (s + 1)) (by rw [abs_le]; exact hstep₁) hdown
      have hc : c = β - 2 ∨ c = β + 1 := by omega
      rcases hc with hc | hc
      · rw [hc] at hspec₃
        have e : (β - 2 + 1) * (r : ℤ) = β * r - r := by ring
        rw [e] at hspec₃
        linarith
      · rw [hc] at hspec₃
        have e : (β + 1) * (r : ℤ) = β * r + r := by ring
        rw [e] at hspec₃
        linarith
  push_cast at hσ₃cast
  omega

theorem pairRes_begin_unique (hh : UnitSteps h) (hr : 1 ≤ r) (T y : ℕ) {β β' : ℤ}
    (h₁ : β ∈ pairRes r h T (y + 1)) (h₁' : β ∉ pairRes r h T y)
    (h₂ : β' ∈ pairRes r h T (y + 1)) (h₂' : β' ∉ pairRes r h T y) : β = β' := by
  rw [mem_pairRes] at h₁ h₂
  obtain ⟨τ, a1, a2, a3, a4⟩ := h₁
  obtain ⟨τ', b1, b2, b3, b4⟩ := h₂
  have hy : (y + 1) * r = y * r + r := Nat.succ_mul y r
  -- the last step of slot y is not resident for β, β'
  have hlast : ∀ γ, γ ∉ pairRes r h T y → γ ∉ residentPair r h ((y + 1) * r - 1) := by
    intro γ hγ hmem
    apply hγ
    rw [mem_pairRes]
    exact ⟨(y + 1) * r - 1, by omega, by omega, by omega, hmem⟩
  obtain ⟨σ, s1, s2, s3, s4⟩ := exists_flip (P := fun t => β ∉ residentPair r h t)
    (show (y + 1) * r - 1 < τ by omega) (hlast β h₁') (by simpa using a4)
  obtain ⟨σ', t1, t2, t3, t4⟩ := exists_flip (P := fun t => β' ∉ residentPair r h t)
    (show (y + 1) * r - 1 < τ' by omega) (hlast β' h₂') (by simpa using b4)
  simp only [not_not] at s4 t4
  obtain ⟨u, rfl⟩ : ∃ u, σ = u + 1 := ⟨σ - 1, by omega⟩
  obtain ⟨u', rfl⟩ : ∃ u', σ' = u' + 1 := ⟨σ' - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at s3 t3
  obtain ⟨pc, e⟩ := entry_is_change s3 s4
  obtain ⟨pc', e'⟩ := entry_is_change t3 t4
  rw [e, e']
  rcases lt_trichotomy u u' with hlt | heq | hgt
  · have := pairChange_spacing hh hr pc pc' (by omega); omega
  · rw [heq]
  · have := pairChange_spacing hh hr pc' pc (by omega); omega

theorem pairRes_end_unique (hh : UnitSteps h) (hr : 1 ≤ r) {T : ℕ} (y : ℕ)
    (hy : (y + 1) * r < T) {β β' : ℤ}
    (h₁ : β ∈ pairRes r h T y) (h₁' : β ∉ pairRes r h T (y + 1))
    (h₂ : β' ∈ pairRes r h T y) (h₂' : β' ∉ pairRes r h T (y + 1)) : β = β' := by
  rw [mem_pairRes] at h₁ h₂
  obtain ⟨τ, a1, a2, a3, a4⟩ := h₁
  obtain ⟨τ', b1, b2, b3, b4⟩ := h₂
  have hys : (y + 1) * r = y * r + r := Nat.succ_mul y r
  have hfirst : ∀ γ, γ ∉ pairRes r h T (y + 1) → γ ∉ residentPair r h ((y + 1) * r) := by
    intro γ hγ hmem
    apply hγ
    rw [mem_pairRes]
    exact ⟨(y + 1) * r, le_rfl, by omega, hy, hmem⟩
  obtain ⟨σ, s1, s2, s3, s4⟩ := exists_flip (P := fun t => β ∈ residentPair r h t)
    (show τ < (y + 1) * r by omega) a4 (hfirst β h₁')
  obtain ⟨σ', t1, t2, t3, t4⟩ := exists_flip (P := fun t => β' ∈ residentPair r h t)
    (show τ' < (y + 1) * r by omega) b4 (hfirst β' h₂')
  obtain ⟨u, rfl⟩ : ∃ u, σ = u + 1 := ⟨σ - 1, by omega⟩
  obtain ⟨u', rfl⟩ : ∃ u', σ' = u' + 1 := ⟨σ' - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at s3 t3
  obtain ⟨pc, e⟩ := exit_is_change s3 s4
  obtain ⟨pc', e'⟩ := exit_is_change t3 t4
  rcases lt_trichotomy u u' with hlt | heq | hgt
  · have := pairChange_spacing hh hr pc pc' (by omega); omega
  · subst heq; rw [e] at e'; exact Option.some.inj e'
  · have := pairChange_spacing hh hr pc' pc (by omega); omega

/-- Generic chord uniqueness from (P2). -/
theorem chord_source_unique_of {R : ℕ → Finset ℤ} {T : ℕ}
    (hempty : ∀ y, T ≤ y * r → R y = ∅)
    (hend : ∀ y, (y + 1) * r < T → ∀ β β', β ∈ R y → β ∉ R (y + 1) → β' ∈ R y →
      β' ∉ R (y + 1) → β = β')
    {β β' : ℤ} {x z z' : ℕ} (he : IsChord R β x z) (he' : IsChord R β' x z') :
    β = β' ∧ z = z' := by
  obtain ⟨hxz, hx, hz, hgap⟩ := he
  obtain ⟨hxz', hx', hz', hgap'⟩ := he'
  have hzT : z * r < T := by
    by_contra hc; push Not at hc; rw [hempty z hc] at hz; simp at hz
  have hyT : (x + 1) * r < T := lt_of_le_of_lt (Nat.mul_le_mul_right r (by omega)) hzT
  have hb : β = β' :=
    hend x hyT β β' hx (hgap (x + 1) (by omega) hxz) hx' (hgap' (x + 1) (by omega) hxz')
  subst hb
  refine ⟨rfl, ?_⟩
  rcases lt_trichotomy z z' with hlt | heq | hgt
  · exact absurd hz (hgap' z (by omega) hlt)
  · exact heq
  · exact absurd hz' (hgap z' (by omega) hgt)

theorem chord_target_unique_of {R : ℕ → Finset ℤ}
    (hbegin : ∀ y β β', β ∈ R (y + 1) → β ∉ R y → β' ∈ R (y + 1) → β' ∉ R y → β = β')
    {β β' : ℤ} {x x' z : ℕ} (he : IsChord R β x z) (he' : IsChord R β' x' z) :
    β = β' ∧ x = x' := by
  obtain ⟨hxz, hx, hz, hgap⟩ := he
  obtain ⟨hxz', hx', hz', hgap'⟩ := he'
  obtain ⟨u, rfl⟩ : ∃ u, z = u + 1 := ⟨z - 1, by omega⟩
  have hb : β = β' :=
    hbegin u β β' hz (hgap u (by omega) (by omega)) hz' (hgap' u (by omega) (by omega))
  subst hb
  refine ⟨rfl, ?_⟩
  rcases lt_trichotomy x x' with hlt | heq | hgt
  · exact absurd hx' (hgap x' hlt (by omega))
  · exact heq
  · exact absurd hx (hgap' x hgt (by omega))

theorem pairRes_empty {T y : ℕ} (hT : T ≤ y * r) : pairRes r h T y = ∅ := by
  ext β; simp only [mem_pairRes, Finset.notMem_empty, iff_false]; omega

theorem touchRes_empty {T y : ℕ} (hT : T ≤ y * r) : touchRes r h T y = ∅ := by
  ext β; simp only [mem_touchRes, Finset.notMem_empty, iff_false]; omega

theorem pairRes_chord_source_unique (hh : UnitSteps h) (hr : 1 ≤ r) (T : ℕ) {β β' : ℤ}
    {x z z' : ℕ} (he : IsChord (pairRes r h T) β x z) (he' : IsChord (pairRes r h T) β' x z') :
    β = β' ∧ z = z' :=
  chord_source_unique_of (fun _ hT => pairRes_empty hT)
    (fun y hy _ _ a b c d => pairRes_end_unique hh hr y hy a b c d) he he'

theorem pairRes_chord_target_unique (hh : UnitSteps h) (hr : 1 ≤ r) (T : ℕ) {β β' : ℤ}
    {x x' z : ℕ} (he : IsChord (pairRes r h T) β x z) (he' : IsChord (pairRes r h T) β' x' z) :
    β = β' ∧ x = x' :=
  chord_target_unique_of (fun y _ _ a b c d => pairRes_begin_unique hh hr T y a b c d) he he'

theorem touchRes_chord_source_unique (hh : UnitSteps h) (hr : 1 ≤ r) (T : ℕ) {β β' : ℤ}
    {x z z' : ℕ} (he : IsChord (touchRes r h T) β x z)
    (he' : IsChord (touchRes r h T) β' x z') : β = β' ∧ z = z' :=
  chord_source_unique_of (fun _ hT => touchRes_empty hT)
    (fun y hy _ _ a b c d => touchRes_end_unique hh hr y hy a b c d) he he'

theorem touchRes_chord_target_unique (hh : UnitSteps h) (hr : 1 ≤ r) (T : ℕ) {β β' : ℤ}
    {x x' z : ℕ} (he : IsChord (touchRes r h T) β x z)
    (he' : IsChord (touchRes r h T) β' x' z) : β = β' ∧ x = x' :=
  chord_target_unique_of (fun y _ _ a b c d => touchRes_begin_unique hh hr T y a b c d) he he'

end P2

/-! ### The Charging Lemma -/

section Charging

variable {r : ℕ} {h : ℕ → ℤ}

theorem isLastVisit_unique {pos : ℕ → ℤ} {τ σ σ' : ℕ} (h₁ : IsLastVisit pos τ σ)
    (h₂ : IsLastVisit pos τ σ') : σ = σ' := by
  obtain ⟨a1, a2, a3⟩ := h₁
  obtain ⟨b1, b2, b3⟩ := h₂
  rcases lt_trichotomy σ σ' with hlt | heq | hgt
  · exact absurd b2 (a3 σ' hlt b1)
  · exact heq
  · exact absurd a2 (b3 σ hgt a1)

theorem mem_entryTimes {U : Set ℕ} {T τ : ℕ} :
    τ ∈ entryTimes r h U T ↔ τ < T ∧ τ / r ∈ U ∧ ∃ σ, σ / r ∉ U ∧ IsLastVisit h τ σ := by
  classical
  simp [entryTimes, Finset.mem_filter]

theorem numSlots_spec (hr : 1 ≤ r) {T y : ℕ} : y < numSlots r T ↔ y * r < T := by
  unfold numSlots
  rw [Nat.lt_div_iff_mul_lt hr]
  constructor <;> intro h <;> omega

theorem div_lt_numSlots (hr : 1 ≤ r) {T τ : ℕ} (hτ : τ < T) : τ / r < numSlots r T := by
  rw [numSlots_spec hr]
  exact lt_of_le_of_lt (Nat.div_mul_le_self τ r) hτ

theorem mem_chordsInto {R : ℕ → Finset ℤ} {U : Set ℕ} {N z : ℕ} {β : ℤ} :
    (z, β) ∈ chordsInto R U N ↔ z < N ∧ z ∈ U ∧ β ∈ R z ∧ ∃ x, x ∉ U ∧ IsChord R β x z := by
  classical
  simp only [chordsInto, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_range,
    Finset.mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨z', ⟨h1, h2⟩, β', ⟨h3, h4⟩, rfl, rfl⟩; exact ⟨h1, h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨z, ⟨h1, h2⟩, β, ⟨h3, h4⟩, rfl, rfl⟩

theorem mem_memBoundaries {U : Set ℕ} {N z : ℕ} :
    z ∈ memBoundaries U N ↔ z < N ∧ z ∈ U ∧ 1 ≤ z ∧ z - 1 ∉ U := by
  classical
  simp [memBoundaries, Finset.mem_filter]

/-- **The entry slot of a block (the `y*` argument).** Let block `β` be resident at slot
`y₀ ∈ U`, `y₀ < N`. Either `β` is resident at no slot `y < y₀` outside `U`, or there is a slot
`z ≤ y₀` that is a memory boundary with `β` resident at `z` and at `z - 1`, or the target of a
chord of `β` entering `U`, such that every slot of `[z, y₀]` at which `β` is resident lies in
`U`. -/
theorem entry_slot {R : ℕ → Finset ℤ} {U : Set ℕ} {N y₀ : ℕ} {β : ℤ} (hy₀N : y₀ < N)
    (hy₀U : y₀ ∈ U) (hβ : β ∈ R y₀) :
    (∀ y < y₀, β ∈ R y → y ∈ U) ∨
      ∃ z ≤ y₀, ((z ∈ memBoundaries U N ∧ β ∈ R z ∧ β ∈ R (z - 1)) ∨
          (z, β) ∈ chordsInto R U N) ∧
        ∀ y, z ≤ y → y ≤ y₀ → β ∈ R y → y ∈ U := by
  classical
  by_cases hex : ∃ y < y₀, y ∉ U ∧ β ∈ R y
  · right
    obtain ⟨y₁, hy₁, hy₁U, hy₁β⟩ := hex
    let P : ℕ → Prop := fun y => y ∉ U ∧ β ∈ R y
    have hPys : P (Nat.findGreatest P y₀) := Nat.findGreatest_spec hy₁.le ⟨hy₁U, hy₁β⟩
    have hys_le : Nat.findGreatest P y₀ ≤ y₀ := Nat.findGreatest_le _
    have hys_lt : Nat.findGreatest P y₀ < y₀ := by
      rcases Nat.lt_or_ge (Nat.findGreatest P y₀) y₀ with h' | h'
      · exact h'
      · exfalso
        have : Nat.findGreatest P y₀ = y₀ := le_antisymm hys_le h'
        exact hPys.1 (by rw [this]; exact hy₀U)
    set ys := Nat.findGreatest P y₀ with hysdef
    have hmax : ∀ y, ys < y → y ≤ y₀ → β ∈ R y → y ∈ U := by
      intro y h1 h2 h3
      by_contra hyU
      exact Nat.findGreatest_is_greatest h1 h2 ⟨hyU, h3⟩
    have hexz : ∃ z, ys < z ∧ β ∈ R z := ⟨y₀, hys_lt, hβ⟩
    set z := Nat.find hexz with hzdef
    have hz : ys < z ∧ β ∈ R z := Nat.find_spec hexz
    have hzle : z ≤ y₀ := Nat.find_min' hexz ⟨hys_lt, hβ⟩
    have hzmin : ∀ y, ys < y → y < z → β ∉ R y := fun y h1 h2 hy => Nat.find_min hexz h2 ⟨h1, hy⟩
    have hzU : z ∈ U := hmax z hz.1 hzle hz.2
    refine ⟨z, hzle, ?_, fun y h1 h2 h3 => hmax y (lt_of_lt_of_le hz.1 h1) h2 h3⟩
    rcases Nat.lt_or_ge (ys + 1) z with hch | hmem
    · right
      rw [mem_chordsInto]
      exact ⟨lt_of_le_of_lt hzle hy₀N, hzU, hz.2, ys, hPys.1, hch, hPys.2, hz.2, hzmin⟩
    · left
      have hz1 : z = ys + 1 := by omega
      refine ⟨?_, hz.2, by rw [hz1, Nat.add_sub_cancel]; exact hPys.2⟩
      rw [mem_memBoundaries]
      refine ⟨lt_of_le_of_lt hzle hy₀N, hzU, by omega, ?_⟩
      rw [hz1, Nat.add_sub_cancel]
      exact hPys.1
  · left
    intro y hy hyβ
    by_contra hyU
    exact hex ⟨y, hy, hyU, hyβ⟩

/-- **The charging step, containment form**: `entry_slot` for the block of an external read. -/
theorem entryTimes_charged (hr : 1 ≤ r) {T c : ℕ} {R : ℕ → Finset ℤ}
    (hR : AdmissibleRes r h T R c) (U : Set ℕ) {τ : ℕ} (hτ : τ ∈ entryTimes r h U T) :
    ∃ z, z ≤ τ / r ∧ (∀ σ, IsLastVisit h τ σ → σ / r < z) ∧
      ((z ∈ memBoundaries U (numSlots r T) ∧ curBlock r h τ ∈ R z ∧
          curBlock r h τ ∈ R (z - 1)) ∨
        (z, curBlock r h τ) ∈ chordsInto R U (numSlots r T)) := by
  obtain ⟨hτT, hτU, σ, hσU, hσ⟩ := mem_entryTimes.1 hτ
  have hβσ : curBlock r h τ ∈ R (σ / r) := by
    have := hR.1 σ (lt_trans hσ.1 hτT); unfold curBlock at this ⊢; rwa [hσ.2.1] at this
  have hσle : σ / r ≤ τ / r := Nat.div_le_div_right hσ.1.le
  rcases entry_slot (div_lt_numSlots hr hτT) hτU (hR.1 τ hτT) with hnone | ⟨z, hz, hent, hU⟩
  · exact absurd (hnone _ (lt_of_le_of_ne hσle fun e => hσU (e ▸ hτU)) hβσ) hσU
  · refine ⟨z, hz, fun σ' hσ' => ?_, hent⟩
    rw [isLastVisit_unique hσ' hσ]
    by_contra hge
    exact hσU (hU _ (not_lt.1 hge) hσle hβσ)

/-- **The Charging Lemma, any admissible residency.** Each external read is charged, by
`entryTimes_charged`, to an event entering `U` (a memory boundary with a resident block, or a
chord), together with its offset in the block; two reads with the same charge would read the same
cell, and the later read's last write would fall after the earlier read. -/
theorem entryTimes_card_le (hr : 1 ≤ r) {T c : ℕ} {R : ℕ → Finset ℤ}
    (hR : AdmissibleRes r h T R c) (U : Set ℕ) :
    (entryTimes r h U T).card ≤
      r * ((chordsInto R U (numSlots r T)).card + c * (memBoundaries U (numSlots r T)).card) := by
  classical
  set N := numSlots r T
  set memEv : Finset (ℕ × ℤ) :=
    (memBoundaries U N).biUnion (fun z => (R z).image (fun β => (z, β)))
  have hmemEv : memEv.card ≤ c * (memBoundaries U N).card := by
    refine le_trans Finset.card_biUnion_le (le_trans (Finset.sum_le_sum fun z _ =>
      le_trans Finset.card_image_le (hR.2 z)) ?_)
    rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  choose! zf hzle hlast hcase using
    fun τ (hτ : τ ∈ entryTimes r h U T) => entryTimes_charged hr hR U hτ
  have hr0 : (0 : ℤ) < r := by exact_mod_cast hr
  let f : ℕ → (ℕ × ℤ) × ℕ := fun τ => ((zf τ, curBlock r h τ), ((h τ) % (r : ℤ)).toNat)
  have hmaps : ∀ τ ∈ entryTimes r h U T, f τ ∈ (memEv ∪ chordsInto R U N) ×ˢ Finset.range r := by
    intro τ hτ
    refine Finset.mem_product.2 ⟨?_, Finset.mem_range.2 ?_⟩
    · rcases hcase τ hτ with ⟨hzm, hβ, -⟩ | hch
      · exact Finset.mem_union_left _
          (Finset.mem_biUnion.2 ⟨_, hzm, Finset.mem_image.2 ⟨_, hβ, rfl⟩⟩)
      · exact Finset.mem_union_right _ hch
    · show ((h τ) % (r : ℤ)).toNat < r
      have := Int.emod_lt_of_pos (h τ) hr0
      have := Int.emod_nonneg (h τ) (ne_of_gt hr0)
      omega
  -- two reads of the same cell have different charges
  have key : ∀ τ₁ ∈ entryTimes r h U T, ∀ τ₂ ∈ entryTimes r h U T, τ₁ < τ₂ → h τ₁ = h τ₂ →
      zf τ₁ ≠ zf τ₂ := by
    intro τ₁ hτ₁ τ₂ hτ₂ hlt hcell hz
    obtain ⟨-, -, σ, hσU, hσ⟩ := mem_entryTimes.1 hτ₂
    have hσgt : τ₁ < σ := by
      rcases lt_trichotomy τ₁ σ with h' | rfl | h'
      · exact h'
      · exact absurd (mem_entryTimes.1 hτ₁).2.1 hσU
      · exact absurd hcell (hσ.2.2 τ₁ h' hlt)
    have := hlast τ₂ hτ₂ σ hσ
    have := hzle τ₁ hτ₁
    have : τ₁ / r ≤ σ / r := Nat.div_le_div_right hσgt.le
    omega
  have hinj : Set.InjOn f (entryTimes r h U T) := by
    intro τ₁ hτ₁ τ₂ hτ₂ hf
    simp only [f, Prod.mk.injEq] at hf
    obtain ⟨⟨hz, hβ⟩, hoff⟩ := hf
    have hcell : h τ₁ = h τ₂ := by
      have e1 := Int.emod_add_mul_ediv (h τ₁) r
      have e2 := Int.emod_add_mul_ediv (h τ₂) r
      have n1 := Int.emod_nonneg (h τ₁) (ne_of_gt hr0)
      have n2 := Int.emod_nonneg (h τ₂) (ne_of_gt hr0)
      have hβ' : h τ₁ / r = h τ₂ / r := hβ
      have : h τ₁ % r = h τ₂ % r := by omega
      rw [← e1, ← e2, this, hβ']
    rcases lt_trichotomy τ₁ τ₂ with hlt | heq | hlt
    · exact absurd hz (key τ₁ hτ₁ τ₂ hτ₂ hlt hcell)
    · exact heq
    · exact absurd hz.symm (key τ₂ hτ₂ τ₁ hτ₁ hlt hcell.symm)
  calc (entryTimes r h U T).card ≤ ((memEv ∪ chordsInto R U N) ×ˢ Finset.range r).card :=
        Finset.card_le_card_of_injOn f hmaps hinj
    _ ≤ (c * (memBoundaries U N).card + (chordsInto R U N).card) * r := by
        rw [Finset.card_product, Finset.card_range]
        exact Nat.mul_le_mul_right _ (le_trans (Finset.card_union_le _ _) (by omega))
    _ = _ := by ring

end Charging

end Transpose.Tape.Impl
