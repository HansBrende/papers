import BoundedStackDepth.CutHops
import BoundedStackDepth.Totals
import BoundedStackDepth.Choice
import BoundedStackDepth.TheoremA
import BoundedStackDepth.Assembly
import BoundedStackDepth.Statement

/-!
# The main theorem

The random label of `Global.lean`, with the parameters of `Choice.lean`, has a small expected cut. Over
the random choices `(r, ω, ξ)` the cut is a sum of terms, each bounded in one file:

* lost hops: Theorem A (`thmA_upper`);
* truncated hops: Lemma D (`card_bad_le`);
* charged hops: the counting fact and the budgets (`card_chargedSet_le`, `sum_stdWeight_le`, Lemma W1);
* exposed hops: `sum_card_exposedSet_le`;
* wraps: `sum_card_wrapSet_le`, with the event weight `weight_events_head_le`;
* cut state edges: `sum_descents_le`.

`sum_violated_head_le` collects the hop terms of one head in natural numbers.
-/

namespace BoundedStackDepth

open BoundedNesting Finset FrameSystem

variable {k : ℕ} {xs : Fin k → ℕ → ℤ} (T : ℕ) (hx : ∀ i, IsWalk (xs i)) {h₀ : ℕ} {Q : ℕ} [NeZero Q]

/-- The weighted standard events of a head, summed over the offsets, total at most `8T`. -/
theorem sum_weight_events_head_le (v : Fin (k * 2)) :
    ∑ r ∈ range h₀, ∑ tg ∈ rises (headFrames T hx v) h₀ r T ∪ lastStints (headFrames T hx v) h₀ r T,
      2 ^ flr h₀ r tg.2 ≤ 8 * T := by
  have hW : ∑ σ ∈ (headFrames T hx v).segments, 2 ^ band ((headFrames T hx v).segMax σ) ≤ T :=
    sum_segWeight_upperFrames_le (isWalk_headWalk hx v)
  have hB := sum_stdWeight_le (S := headFrames T hx v) (h₀ := h₀) T
  calc _ ≤ ∑ r ∈ range h₀, (∑ tg ∈ rises (headFrames T hx v) h₀ r T, 2 ^ flr h₀ r tg.2 +
        ∑ tg ∈ lastStints (headFrames T hx v) h₀ r T, 2 ^ flr h₀ r tg.2) :=
        sum_le_sum fun r _ => sum_union_le_sum_add_sum
    _ ≤ 8 * T := hB.trans (Nat.mul_le_mul_left _ hW)
where
  sum_union_le_sum_add_sum {A B : Finset (ℕ × ℕ)} {f : ℕ × ℕ → ℕ} :
      ∑ x ∈ A ∪ B, f x ≤ ∑ x ∈ A, f x + ∑ x ∈ B, f x := by
    classical
    rw [← sum_union_inter]
    exact Nat.le_add_right _ _

/-- **The hop terms of one head**, summed over the random choices (without truncation). -/
theorem sum_violated_head_le {K P : ℕ} (hK : 0 < K) (v : Fin (k * 2)) :
    ∑ r ∈ range h₀, ∑ ω ∈ Fintype.piFinset (fun _ : Fin P => range K),
        ∑ ξ : EntryIdx (headFrames T hx) → Fin Q,
          ((upperHops (headWalk xs v) T).filter fun e =>
            labelOf T hx h₀ K P r ω ξ e.2 ≤ labelOf T hx h₀ K P r ω ξ e.1).card ≤
      K ^ P * Q ^ Fintype.card (EntryIdx (headFrames T hx)) * (6 * T) +
      K ^ P * ∑ r ∈ range h₀, ∑ ξ : EntryIdx (headFrames T hx) → Fin Q, (badTimes hx (h₀ := h₀) P r ξ).card +
      K ^ P * Q ^ Fintype.card (EntryIdx (headFrames T hx)) * (10 * (k * 2 * (8 * T))) +
      K ^ P * (h₀ * (T * (2 * (k * 2) * Q ^ (Fintype.card (EntryIdx (headFrames T hx)) - 1)))) +
      h₀ * (Q ^ Fintype.card (EntryIdx (headFrames T hx)) *
        (K ^ (P - 1) * (20 * 2 ^ h₀ * (k * 2 * (6 * T + 1))))) := by
  classical
  set ι := EntryIdx (headFrames T hx)
  have hω : (Fintype.piFinset fun _ : Fin P => range K).card = K ^ P := by
    rw [Fintype.card_piFinset]; simp
  have hξ : (univ : Finset (ι → Fin Q)).card = Q ^ Fintype.card ι := by
    rw [card_univ, Fintype.card_fun, Fintype.card_fin]
  have hHv := card_upperHops_head_le T hx v
  -- the five terms
  have hlost : ∑ r ∈ range h₀, (lostSet T hx h₀ v r).card ≤ 6 * T :=
    (thmA_upper (isWalk_headWalk hx v) h₀).trans (Nat.mul_le_mul_left _ hHv)
  have hcharged : ∑ r ∈ range h₀, (chargedSet T hx h₀ v r).card ≤ 10 * (k * 2 * (8 * T)) := by
    calc ∑ r ∈ range h₀, (chargedSet T hx h₀ v r).card
        ≤ ∑ r ∈ range h₀, ∑ w, ∑ tg ∈ rises (headFrames T hx w) h₀ r T ∪
            lastStints (headFrames T hx w) h₀ r T, 10 * 2 ^ flr h₀ r tg.2 :=
          sum_le_sum fun r hr => card_chargedSet_le hx (mem_range.mp hr) v
      _ = 10 * ∑ w, ∑ r ∈ range h₀, ∑ tg ∈ rises (headFrames T hx w) h₀ r T ∪
            lastStints (headFrames T hx w) h₀ r T, 2 ^ flr h₀ r tg.2 := by
          simp only [← mul_sum]
          rw [sum_comm]
      _ ≤ 10 * ∑ _w : Fin (k * 2), 8 * T :=
          Nat.mul_le_mul_left _ (sum_le_sum fun w _ => sum_weight_events_head_le T hx w)
      _ = 10 * (k * 2 * (8 * T)) := by simp
  have hexposed : ∀ r ∈ range h₀, ∑ ξ : ι → Fin Q, (exposedSet T hx h₀ v r ξ).card ≤
      T * (2 * (k * 2) * Q ^ (Fintype.card ι - 1)) := fun r hr =>
    (sum_card_exposedSet_le hx (mem_range.mp hr) v).trans (Nat.mul_le_mul_right _ hHv)
  have hwrap : ∀ r ∈ range h₀, ∀ ξ : ι → Fin Q,
      ∑ ω ∈ Fintype.piFinset (fun _ : Fin P => range K), (wrapSet T hx h₀ K P v r ω ξ).card ≤
        K ^ (P - 1) * (20 * 2 ^ h₀ * (k * 2 * (6 * T + 1))) := fun r hr ξ => by
    refine (sum_card_wrapSet_le hx hK (mem_range.mp hr) v ξ).trans (Nat.mul_le_mul_left _ ?_)
    calc ∑ w, (∑ s ∈ turnsOf (headFrames T hx w),
          20 * 2 ^ h₀ * 2 ^ band (prom (headFrames T hx w).x (headFrames T hx w).T s) +
        ∑ Fs ∈ segStarts (headFrames T hx w), 20 * 2 ^ h₀ * 2 ^ segScale (headFrames T hx w) Fs.1 Fs.2)
        = 20 * 2 ^ h₀ * ∑ w, (∑ s ∈ turnsOf (headFrames T hx w),
            2 ^ band (prom (headFrames T hx w).x (headFrames T hx w).T s) +
          ∑ Fs ∈ segStarts (headFrames T hx w), 2 ^ segScale (headFrames T hx w) Fs.1 Fs.2) := by
          rw [mul_sum]
          exact sum_congr rfl fun w _ => by rw [mul_add, mul_sum, mul_sum]
      _ ≤ 20 * 2 ^ h₀ * ∑ _w : Fin (k * 2), (6 * T + 1) :=
          Nat.mul_le_mul_left _ (sum_le_sum fun w _ => weight_events_head_le T hx w)
      _ = 20 * 2 ^ h₀ * (k * 2 * (6 * T + 1)) := by simp
  -- the five triple sums
  have hc : ∀ c : ℕ, ∑ _ω ∈ Fintype.piFinset (fun _ : Fin P => range K), ∑ _ξ : ι → Fin Q, c =
      K ^ P * Q ^ Fintype.card ι * c := fun c => by
    rw [sum_const, hω, smul_eq_mul, sum_const, card_univ, Fintype.card_fun, Fintype.card_fin,
      smul_eq_mul, mul_assoc]
  have b1 : ∑ r ∈ range h₀, ∑ ω ∈ Fintype.piFinset (fun _ : Fin P => range K), ∑ ξ : ι → Fin Q,
      (lostSet T hx h₀ v r).card ≤ K ^ P * Q ^ Fintype.card ι * (6 * T) := by
    simp only [hc, ← mul_sum]
    exact Nat.mul_le_mul_left _ hlost
  have b2 : ∑ r ∈ range h₀, ∑ ω ∈ Fintype.piFinset (fun _ : Fin P => range K), ∑ ξ : ι → Fin Q,
      (truncSet T hx h₀ P v r ξ).card ≤
      K ^ P * ∑ r ∈ range h₀, ∑ ξ : ι → Fin Q, (badTimes hx (h₀ := h₀) P r ξ).card := by
    rw [mul_sum]
    refine sum_le_sum fun r _ => ?_
    rw [sum_const, hω, smul_eq_mul]
    exact Nat.mul_le_mul_left _ (sum_le_sum fun ξ _ => card_truncSet_le_bad hx P v r ξ)
  have b3 : ∑ r ∈ range h₀, ∑ ω ∈ Fintype.piFinset (fun _ : Fin P => range K), ∑ ξ : ι → Fin Q,
      (chargedSet T hx h₀ v r).card ≤ K ^ P * Q ^ Fintype.card ι * (10 * (k * 2 * (8 * T))) := by
    simp only [hc, ← mul_sum]
    exact Nat.mul_le_mul_left _ hcharged
  have b4 : ∑ r ∈ range h₀, ∑ ω ∈ Fintype.piFinset (fun _ : Fin P => range K), ∑ ξ : ι → Fin Q,
      (exposedSet T hx h₀ v r ξ).card ≤
      K ^ P * (h₀ * (T * (2 * (k * 2) * Q ^ (Fintype.card ι - 1)))) := by
    calc _ = ∑ r ∈ range h₀, K ^ P * ∑ ξ : ι → Fin Q, (exposedSet T hx h₀ v r ξ).card :=
          sum_congr rfl fun r _ => by rw [sum_const, hω, smul_eq_mul]
      _ ≤ ∑ _r ∈ range h₀, K ^ P * (T * (2 * (k * 2) * Q ^ (Fintype.card ι - 1))) :=
          sum_le_sum fun r hr => Nat.mul_le_mul_left _ (hexposed r hr)
      _ = _ := by rw [sum_const, card_range, smul_eq_mul]; ring
  have b5 : ∑ r ∈ range h₀, ∑ ω ∈ Fintype.piFinset (fun _ : Fin P => range K), ∑ ξ : ι → Fin Q,
      (wrapSet T hx h₀ K P v r ω ξ).card ≤
      h₀ * (Q ^ Fintype.card ι * (K ^ (P - 1) * (20 * 2 ^ h₀ * (k * 2 * (6 * T + 1))))) := by
    calc _ = ∑ r ∈ range h₀, ∑ ξ : ι → Fin Q,
          ∑ ω ∈ Fintype.piFinset (fun _ : Fin P => range K), (wrapSet T hx h₀ K P v r ω ξ).card :=
          sum_congr rfl fun r _ => sum_comm
      _ ≤ ∑ _r ∈ range h₀, ∑ _ξ : ι → Fin Q, K ^ (P - 1) * (20 * 2 ^ h₀ * (k * 2 * (6 * T + 1))) :=
          sum_le_sum fun r hr => sum_le_sum fun ξ _ => hwrap r hr ξ
      _ = _ := by
          rw [sum_const, card_range, smul_eq_mul, sum_const, card_univ, Fintype.card_fun,
            Fintype.card_fin, smul_eq_mul]
  calc _ ≤ ∑ r ∈ range h₀, ∑ ω ∈ Fintype.piFinset (fun _ : Fin P => range K), ∑ ξ : ι → Fin Q,
        ((lostSet T hx h₀ v r).card + (truncSet T hx h₀ P v r ξ).card + (chargedSet T hx h₀ v r).card +
          (exposedSet T hx h₀ v r ξ).card + (wrapSet T hx h₀ K P v r ω ξ).card) :=
        sum_le_sum fun r _ => sum_le_sum fun ω _ => sum_le_sum fun ξ _ =>
          card_violated_le_cut hx hK v r ω ξ
    _ = _ := by simp only [sum_add_distrib]
    _ ≤ _ := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add b1 b2) b3) b4) b5

/-- **The cut, summed over the random choices**, in natural numbers. -/
theorem sum_labelCutSize_le {K P : ℕ} (hK : 0 < K) :
    ∑ r ∈ range h₀, ∑ ω ∈ Fintype.piFinset (fun _ : Fin P => range K),
        ∑ ξ : EntryIdx (headFrames T hx) → Fin Q, labelCutSize xs T (labelOf T hx h₀ K P r ω ξ) ≤
      (K ^ P * Q ^ Fintype.card (EntryIdx (headFrames T hx)) * (k * 2 * (8 * T)) +
        Q ^ Fintype.card (EntryIdx (headFrames T hx)) * h₀ * (P * K ^ (P - 1) * (k * 2 * (4 * T + 1)))) +
      k * 2 * (K ^ P * Q ^ Fintype.card (EntryIdx (headFrames T hx)) * (6 * T) +
        K ^ P * ∑ r ∈ range h₀, ∑ ξ : EntryIdx (headFrames T hx) → Fin Q,
          (badTimes hx (h₀ := h₀) P r ξ).card +
        K ^ P * Q ^ Fintype.card (EntryIdx (headFrames T hx)) * (10 * (k * 2 * (8 * T))) +
        K ^ P * (h₀ * (T * (2 * (k * 2) * Q ^ (Fintype.card (EntryIdx (headFrames T hx)) - 1)))) +
        h₀ * (Q ^ Fintype.card (EntryIdx (headFrames T hx)) *
          (K ^ (P - 1) * (20 * 2 ^ h₀ * (k * 2 * (6 * T + 1)))))) := by
  classical
  calc _ ≤ ∑ r ∈ range h₀, ∑ ω ∈ Fintype.piFinset (fun _ : Fin P => range K),
        ∑ ξ : EntryIdx (headFrames T hx) → Fin Q,
          ((descentsOf (labelOf T hx h₀ K P r ω ξ) T).card +
            ∑ v, ((upperHops (headWalk xs v) T).filter fun e =>
              labelOf T hx h₀ K P r ω ξ e.2 ≤ labelOf T hx h₀ K P r ω ξ e.1).card) :=
        sum_le_sum fun r _ => sum_le_sum fun ω _ => sum_le_sum fun ξ _ =>
          Nat.add_le_add_left (card_violated_le_heads xs T _) _
    _ = ∑ r ∈ range h₀, ∑ ω ∈ Fintype.piFinset (fun _ : Fin P => range K),
          ∑ ξ : EntryIdx (headFrames T hx) → Fin Q, (descentsOf (labelOf T hx h₀ K P r ω ξ) T).card +
        ∑ v, ∑ r ∈ range h₀, ∑ ω ∈ Fintype.piFinset (fun _ : Fin P => range K),
          ∑ ξ : EntryIdx (headFrames T hx) → Fin Q, ((upperHops (headWalk xs v) T).filter fun e =>
            labelOf T hx h₀ K P r ω ξ e.2 ≤ labelOf T hx h₀ K P r ω ξ e.1).card := by
        simp only [sum_add_distrib]
        congr 1
        exact (sum_congr rfl fun r _ => sum_congr rfl fun ω _ => sum_comm).trans
          ((sum_congr rfl fun r _ => sum_comm).trans sum_comm)
    _ ≤ _ := by
        refine Nat.add_le_add (sum_descents_le T hx hK) ?_
        refine (sum_le_sum fun v _ => sum_violated_head_le T hx hK v).trans ?_
        rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]

/-- **The bad times** (Lemma D), summed over the offsets and the bits. -/
theorem sum_bad_le (j P : ℕ) (hP : 1 + (k * 2 + k * 2) * (j * (k * 2) + 1) ≤ P) :
    ((∑ r ∈ range h₀, ∑ ξ : EntryIdx (headFrames T hx) → Fin Q,
      (badTimes hx (h₀ := h₀) P r ξ).card : ℕ) : ℝ) ≤
      h₀ * (T * ((k * 2 + k * 2 : ℕ) * (1 - ((Q : ℝ) ^ (k * 2 * (k * 2)))⁻¹) ^ j *
        (Q : ℝ) ^ Fintype.card (EntryIdx (headFrames T hx)))) := by
  classical
  have hper : ∀ r, ((∑ ξ : EntryIdx (headFrames T hx) → Fin Q,
      (badTimes hx (h₀ := h₀) P r ξ).card : ℕ) : ℝ) ≤ T * ((k * 2 + k * 2 : ℕ) *
        (1 - ((Q : ℝ) ^ (k * 2 * (k * 2)))⁻¹) ^ j * (Q : ℝ) ^ Fintype.card (EntryIdx (headFrames T hx))) := by
    intro r
    have hexch : ∑ ξ : EntryIdx (headFrames T hx) → Fin Q, (badTimes hx (h₀ := h₀) P r ξ).card =
        ∑ t ∈ range T, (univ.filter fun ξ : EntryIdx (headFrames T hx) → Fin Q =>
          P < (shown T hx h₀ r ξ t).card).card := by
      simp only [badTimes, card_eq_sum_ones, sum_filter]
      exact sum_comm
    rw [hexch]
    push_cast
    calc ∑ t ∈ range T, ((univ.filter fun ξ : EntryIdx (headFrames T hx) → Fin Q =>
          P < (shown T hx h₀ r ξ t).card).card : ℝ)
        ≤ ∑ _t ∈ range T, ((k * 2 + k * 2 : ℕ) * (1 - ((Q : ℝ) ^ (k * 2 * (k * 2)))⁻¹) ^ j *
            (Q : ℝ) ^ Fintype.card (EntryIdx (headFrames T hx))) :=
          sum_le_sum fun t _ => card_bad_le hx P r j t hP
      _ = _ := by rw [sum_const, card_range, nsmul_eq_mul]; push_cast; ring
  push_cast
  calc ∑ r ∈ range h₀, (∑ ξ : EntryIdx (headFrames T hx) → Fin Q,
        ((badTimes hx (h₀ := h₀) P r ξ).card : ℝ))
      ≤ ∑ _r ∈ range h₀, (T * ((k * 2 + k * 2 : ℕ) * (1 - ((Q : ℝ) ^ (k * 2 * (k * 2)))⁻¹) ^ j *
          (Q : ℝ) ^ Fintype.card (EntryIdx (headFrames T hx)))) :=
        sum_le_sum fun r _ => by exact_mod_cast hper r
    _ = _ := by rw [sum_const, card_range, nsmul_eq_mul]; push_cast; ring

/-! ### The parameters and the main theorem -/

/-- The grid size: `h₀ = ⌈(14n + 80n²)/(ε/4)⌉ + 1` for `n = 2k` heads. -/
noncomputable def parH (k : ℕ) (ε : ℝ) : ℕ :=
  ⌈(14 * ((k * 2 : ℕ) : ℝ) + 80 * ((k * 2 : ℕ) : ℝ) ^ 2) / (ε / 4)⌉₊ + 1

/-- The bit size: `Q = ⌈2n²/(ε/4)⌉ + 1` (a bit is broken with probability `1/Q`). -/
noncomputable def parQ (k : ℕ) (ε : ℝ) : ℕ := ⌈2 * ((k * 2 : ℕ) : ℝ) ^ 2 / (ε / 4)⌉₊ + 1

/-- The number of blocks of Lemma D: `j = ⌈ln(max 1 (8n²/ε)) · Q^{n²}⌉`. -/
noncomputable def parJ (k : ℕ) (ε : ℝ) : ℕ :=
  ⌈Real.log (max 1 (8 * ((k * 2 : ℕ) : ℝ) ^ 2 / ε)) /
    (((parQ k ε : ℕ) : ℝ) ^ (k * 2 * (k * 2)))⁻¹⌉₊

/-- The number of digits: `P = 1 + 2n(jn + 1)`. -/
noncomputable def parP (k : ℕ) (ε : ℝ) : ℕ := 1 + (k * 2 + k * 2) * (parJ k ε * (k * 2) + 1)

/-- The digit radix: `K = ⌈(5Pn + 140 · 2^{h₀} n²)/(ε/4)⌉ + 1`. -/
noncomputable def parK (k : ℕ) (ε : ℝ) : ℕ :=
  ⌈(5 * (parP k ε : ℝ) * ((k * 2 : ℕ) : ℝ) + 140 * 2 ^ parH k ε * ((k * 2 : ℕ) : ℝ) ^ 2) / (ε / 4)⌉₊ + 1

theorem parH_spec (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    14 * ((k * 2 : ℕ) : ℝ) + 80 * ((k * 2 : ℕ) : ℝ) ^ 2 ≤ (parH k ε : ℝ) * (ε / 4) :=
  le_natCeil_add_one_mul (by linarith)

theorem parQ_spec (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    2 * ((k * 2 : ℕ) : ℝ) ^ 2 ≤ (parQ k ε : ℝ) * (ε / 4) :=
  le_natCeil_add_one_mul (by linarith)

theorem parK_spec (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    5 * (parP k ε : ℝ) * ((k * 2 : ℕ) : ℝ) + 140 * 2 ^ parH k ε * ((k * 2 : ℕ) : ℝ) ^ 2 ≤
      (parK k ε : ℝ) * (ε / 4) :=
  le_natCeil_add_one_mul (by linarith)

theorem parJ_spec (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    2 * ((k * 2 : ℕ) : ℝ) ^ 2 * (1 - ((parQ k ε : ℝ) ^ (k * 2 * (k * 2)))⁻¹) ^ parJ k ε ≤ ε / 4 :=
  trunc_term_le hε (k * 2) (parQ k ε) (by unfold parQ; omega)

/-- **The main estimate.** For `k` walks (pauses allowed) and `ε > 0`, the random label with the
parameters above takes fewer than `K^P` values and its cut averages at most `εT`. -/
theorem exists_avgLabel (k : ℕ) {ε : ℝ} (hε : 0 < ε) (T : ℕ) (xs : Fin k → ℕ → ℤ)
    (hx : ∀ h, IsWalk (xs h)) :
    ∃ (α : Type) (Ω : Finset α) (Ψ : α → ℕ → ℕ), Ω.Nonempty ∧ (∀ ω t, Ψ ω t < parK k ε ^ parP k ε) ∧
      (∑ ω ∈ Ω, (labelCutSize xs T (Ψ ω) : ℝ)) ≤ Ω.card * (ε * T) := by
  classical
  set h₀ := parH k ε with hh₀
  set Q := parQ k ε with hQ
  set j := parJ k ε with hj
  set P := parP k ε with hP
  set K := parK k ε with hK
  have hh : 0 < h₀ := by rw [hh₀, parH]; omega
  have hQ1 : 1 ≤ Q := by rw [hQ, parQ]; omega
  have hK0 : 0 < K := by rw [hK, parK]; omega
  have hP1 : 1 ≤ P := by rw [hP, parP]; omega
  have : NeZero Q := ⟨by omega⟩
  set ι := Fintype.card (EntryIdx (headFrames T hx)) with hι
  refine ⟨ℕ × (Fin P → ℕ) × (EntryIdx (headFrames T hx) → Fin Q),
    range h₀ ×ˢ (Fintype.piFinset (fun _ : Fin P => range K) ×ˢ univ),
    fun a => labelOf T hx h₀ K P a.1 a.2.1 a.2.2, ?_, fun a t => labelOf_lt T hx h₀ hK0 _ _ t, ?_⟩
  · exact ⟨(0, fun _ => 0, fun _ => 0), mem_product.mpr ⟨mem_range.mpr hh, mem_product.mpr
      ⟨Fintype.mem_piFinset.mpr fun _ => mem_range.mpr hK0, mem_univ _⟩⟩⟩
  -- the sum over `Ω` as an iterated sum
  have hsum : ∑ a ∈ range h₀ ×ˢ (Fintype.piFinset (fun _ : Fin P => range K) ×ˢ
      (univ : Finset (EntryIdx (headFrames T hx) → Fin Q))),
      (labelCutSize xs T (labelOf T hx h₀ K P a.1 a.2.1 a.2.2) : ℝ) =
      ((∑ r ∈ range h₀, ∑ ω ∈ Fintype.piFinset (fun _ : Fin P => range K),
        ∑ ξ : EntryIdx (headFrames T hx) → Fin Q,
          labelCutSize xs T (labelOf T hx h₀ K P r ω ξ) : ℕ) : ℝ) := by
    rw [sum_product, Nat.cast_sum]
    refine sum_congr rfl fun r _ => ?_
    rw [sum_product, Nat.cast_sum]
    refine sum_congr rfl fun ω _ => ?_
    rw [Nat.cast_sum]
  have hcard : ((range h₀ ×ˢ (Fintype.piFinset (fun _ : Fin P => range K) ×ˢ
      (univ : Finset (EntryIdx (headFrames T hx) → Fin Q)))).card : ℝ) =
      (h₀ : ℝ) * ((K : ℝ) ^ P * (Q : ℝ) ^ ι) := by
    rw [card_product, card_product, card_range, Fintype.card_piFinset, card_univ,
      Fintype.card_fun, Fintype.card_fin]
    simp only [card_range, prod_const, card_univ, Fintype.card_fin]
    push_cast
    ring
  rw [hsum, hcard]
  -- the case `T = 0`
  rcases Nat.eq_zero_or_pos T with hT0 | hT
  · subst hT0
    have : ∀ (r : ℕ) (ω : Fin P → ℕ) (ξ : EntryIdx (headFrames 0 hx) → Fin Q),
        labelCutSize xs 0 (labelOf 0 hx h₀ K P r ω ξ) = 0 := fun r ω ξ => by
      unfold labelCutSize descentsOf violatedOf
      simp [allHops, hopPairs]
    simp [this]
  -- the bound in natural numbers, and Lemma D
  have hS := sum_labelCutSize_le T hx (h₀ := h₀) (Q := Q) (P := P) hK0
  have hbad := sum_bad_le T hx (h₀ := h₀) (Q := Q) j P (le_of_eq (by rw [hP, parP, hj]))
  have hS' := (Nat.cast_le (α := ℝ)).mpr hS
  push_cast at hS' hbad
  rw [← hι] at hS' hbad
  -- the parameter facts
  have p1 := parH_spec k hε
  have p2 := parQ_spec k hε
  have p3 := parJ_spec k hε
  have p4 := parK_spec k hε
  rw [← hh₀] at p1 p4
  rw [← hQ] at p2 p3
  rw [← hj] at p3
  rw [← hP, ← hK] at p4
  -- abbreviations
  have hTr : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hKP : (K : ℝ) ^ P = K * (K : ℝ) ^ (P - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hQι : 2 * ((k * 2 : ℕ) : ℝ) ^ 2 * (Q : ℝ) ^ (ι - 1) ≤ (ε / 4) * (Q : ℝ) ^ ι := by
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0; simp only [Nat.zero_mul, Nat.cast_zero]; norm_num; positivity
    · have hι1 : 1 ≤ ι := by
        rw [hι]
        exact Fintype.card_pos_iff.mpr ⟨⟨⟨0, by omega⟩, ⟨(0, T), (headFrames T hx _).root_mem⟩⟩⟩
      have : (Q : ℝ) ^ ι = Q * (Q : ℝ) ^ (ι - 1) := by rw [← pow_succ']; congr 1; omega
      rw [this]
      have hb : (0 : ℝ) ≤ (Q : ℝ) ^ (ι - 1) := by positivity
      nlinarith
  push_cast at p1 p2 p3 p4 hQι
  -- nonnegativity
  have hn : (0 : ℝ) ≤ (k : ℝ) * 2 := by positivity
  have hc : (0 : ℝ) ≤ (Q : ℝ) ^ ι := by positivity
  have ha : (0 : ℝ) ≤ (K : ℝ) ^ (P - 1) := by positivity
  have hKp : (0 : ℝ) ≤ (K : ℝ) ^ P := by positivity
  have hh0 : (0 : ℝ) ≤ (h₀ : ℝ) := by positivity
  have hX : (0 : ℝ) ≤ (1 - ((Q : ℝ) ^ (k * 2 * (k * 2)))⁻¹) ^ j := by
    refine pow_nonneg ?_ _
    have : ((Q : ℝ) ^ (k * 2 * (k * 2)))⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (one_le_pow₀ (by exact_mod_cast hQ1))
    linarith
  -- (i) the terms paid by the grid
  have e1 : (K : ℝ) ^ P * (Q : ℝ) ^ ι * T * (14 * ((k : ℝ) * 2) + 80 * ((k : ℝ) * 2) ^ 2) ≤
      (K : ℝ) ^ P * (Q : ℝ) ^ ι * T * (h₀ * (ε / 4)) :=
    mul_le_mul_of_nonneg_left p1 (by positivity)
  -- (ii) truncation
  have e2 : (k : ℝ) * 2 * (K : ℝ) ^ P * (∑ r ∈ range h₀, ∑ ξ : EntryIdx (headFrames T hx) → Fin Q,
      ((badTimes hx (h₀ := h₀) P r ξ).card : ℝ)) ≤ (K : ℝ) ^ P * (Q : ℝ) ^ ι * h₀ * T * (ε / 4) := by
    calc _ ≤ (k : ℝ) * 2 * (K : ℝ) ^ P * (h₀ * (T * (((k : ℝ) * 2 + (k : ℝ) * 2) *
          (1 - ((Q : ℝ) ^ (k * 2 * (k * 2)))⁻¹) ^ j * (Q : ℝ) ^ ι))) :=
          mul_le_mul_of_nonneg_left hbad (by positivity)
      _ = (K : ℝ) ^ P * (Q : ℝ) ^ ι * h₀ * T *
          (2 * ((k : ℝ) * 2) ^ 2 * (1 - ((Q : ℝ) ^ (k * 2 * (k * 2)))⁻¹) ^ j) := by ring
      _ ≤ (K : ℝ) ^ P * (Q : ℝ) ^ ι * h₀ * T * (ε / 4) :=
          mul_le_mul_of_nonneg_left p3 (by positivity)
  -- (iii) exposure
  have e3 : (K : ℝ) ^ P * h₀ * T * (2 * ((k : ℝ) * 2) ^ 2 * (Q : ℝ) ^ (ι - 1)) ≤
      (K : ℝ) ^ P * h₀ * T * (ε / 4 * (Q : ℝ) ^ ι) :=
    mul_le_mul_of_nonneg_left hQι (by positivity)
  -- (iv) the digit wraps
  have e4 : (Q : ℝ) ^ ι * h₀ * (K : ℝ) ^ (P - 1) * ((k : ℝ) * 2) *
      ((P : ℝ) * (4 * T + 1) + 20 * 2 ^ h₀ * ((k : ℝ) * 2) * (6 * T + 1)) ≤
      (Q : ℝ) ^ ι * h₀ * (K : ℝ) ^ P * T * (ε / 4) := by
    have hP0 : (0 : ℝ) ≤ P := by positivity
    have h2 : (0 : ℝ) ≤ 2 ^ h₀ := by positivity
    calc _ ≤ (Q : ℝ) ^ ι * h₀ * (K : ℝ) ^ (P - 1) * T *
          (5 * (P : ℝ) * ((k : ℝ) * 2) + 140 * 2 ^ h₀ * ((k : ℝ) * 2) ^ 2) := by
          have hin : ((k : ℝ) * 2) * ((P : ℝ) * (4 * T + 1) + 20 * 2 ^ h₀ * ((k : ℝ) * 2) * (6 * T + 1)) ≤
              T * (5 * (P : ℝ) * ((k : ℝ) * 2) + 140 * 2 ^ h₀ * ((k : ℝ) * 2) ^ 2) := by
            nlinarith [mul_nonneg hn hP0, mul_nonneg (mul_nonneg hn hn) h2]
          have := mul_le_mul_of_nonneg_left hin (show (0 : ℝ) ≤ (Q : ℝ) ^ ι * h₀ * (K : ℝ) ^ (P - 1) by
            positivity)
          linarith
      _ ≤ (Q : ℝ) ^ ι * h₀ * (K : ℝ) ^ (P - 1) * T * ((K : ℝ) * (ε / 4)) :=
          mul_le_mul_of_nonneg_left p4 (by positivity)
      _ = _ := by rw [hKP]; ring
  push_cast
  refine hS'.trans ?_
  calc _ = (K : ℝ) ^ P * (Q : ℝ) ^ ι * T * (14 * ((k : ℝ) * 2) + 80 * ((k : ℝ) * 2) ^ 2) +
        (k : ℝ) * 2 * (K : ℝ) ^ P * (∑ r ∈ range h₀, ∑ ξ : EntryIdx (headFrames T hx) → Fin Q,
          ((badTimes hx (h₀ := h₀) P r ξ).card : ℝ)) +
        (K : ℝ) ^ P * h₀ * T * (2 * ((k : ℝ) * 2) ^ 2 * (Q : ℝ) ^ (ι - 1)) +
        (Q : ℝ) ^ ι * h₀ * (K : ℝ) ^ (P - 1) * ((k : ℝ) * 2) *
          ((P : ℝ) * (4 * T + 1) + 20 * 2 ^ h₀ * ((k : ℝ) * 2) * (6 * T + 1)) := by ring
    _ ≤ (K : ℝ) ^ P * (Q : ℝ) ^ ι * T * (h₀ * (ε / 4)) +
        (K : ℝ) ^ P * (Q : ℝ) ^ ι * h₀ * T * (ε / 4) +
        (K : ℝ) ^ P * h₀ * T * (ε / 4 * (Q : ℝ) ^ ι) +
        (Q : ℝ) ^ ι * h₀ * (K : ℝ) ^ P * T * (ε / 4) := by gcongr
    _ = _ := by ring

/-- **The main theorem, with the explicit depth.** For `k` walks (pauses allowed) and `ε > 0`, the walk
DAG has a cut of at most `εT` edges and depth at most `K^P − 1`, with the parameters above. -/
theorem tcpAt_direct (k : ℕ) {ε : ℝ} (hε : 0 < ε) : TCPat k ε (parK k ε ^ parP k ε - 1) := by
  intro T xs hx
  obtain ⟨α, Ω, Ψ, hΩ, hΨ, havg⟩ := exists_avgLabel k hε T xs hx
  exact exists_cut_of_avg Ω hΩ Ψ hΨ havg

/-- **TCP(k) for every `k`** (walks with pauses). -/
theorem tcp (k : ℕ) : TCP k := fun _ hε => ⟨_, tcpAt_direct k hε⟩

/-- **The main theorem**: `TCP k` for every number `k` of walks. -/
theorem main : MainStatement := tcp

/-- **SR(s) for every `s`**: `s`-stack DAGs reduce to constant depth. -/
theorem sr (s : ℕ) : SR s := sr_of_main main s

end BoundedStackDepth
