import Transpose.Tape.MStarLevel
import Transpose.Tape.Blocks
import Transpose.Tape.DefsCE

/-!
# Theorem M*: walks and the machine walk

Block sizes: `one_le_blockSize`, `blockSize_le`, `blockSize_mul_ge` and `blockSize_mul_le` for
`r = blockSize G n = ⌈n b / G⌉` (`n b ≤ r G ≤ n b + G`); the machine's slot length is the instance
`slotLen M n = blockSize (cellBits M) n` (definitionally; `one_le_slotLen`, `slotLen_le`,
`slotLen_mul_ge`).

Generic lemmas on walks (`h : ℕ → ℤ` with unit steps), shared by machines, code-carrying diagrams
and the abstract core (`MStarWalk.lean`):
* `blockTraj`: the rescaled block trajectory; `unitSteps_frozen`, `frozen_V1` and `frozen_V2`: (V1′)
  and (V2′) for a walk frozen at time `T`; `numSlots_le_of`: `⌈T/r⌉ ≤ (c G + 1) n` when
  `T ≤ c n² b` and `n b ≤ r G`;
* `blockTraj_lipschitz_approx`, `blockTraj_limit_lipschitz` (uniform limits are 1-Lipschitz),
  `blockTraj_abs_le` and `exists_subseq_blockTraj` (Arzelà–Ascoli).

Their machine instances:
* `workTraj_frozen`: after halting the run is frozen;
* `pairRes_V2`: (V2′) for the walk of a work head's block at the first steps of slots, with pair
  residency, including slots after halting;
* `numSlots_le_horizon`: `⌈T/r⌉ ≤ c₀ n` when `T ≤ c n² b`;
* `rescaledTraj_limit_lipschitz`.
-/

namespace Transpose.Tape.Impl

open Transpose MeasureTheory Filter Topology TSDiagram

open scoped ENNReal

/-! ### Slot lengths -/

theorem cellBits_pos (M : TM) : 1 ≤ cellBits M := le_max_left _ _

theorem one_le_blockSize {G n : ℕ} (hG : 1 ≤ G) (hn : 1 ≤ n) : 1 ≤ blockSize G n := by
  unfold blockSize
  have hb : 1 ≤ entryBits n := by unfold entryBits; omega
  have : 1 ≤ n * entryBits n := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  rw [Nat.le_div_iff_mul_le (by omega)]
  omega

theorem blockSize_le {G n : ℕ} (hG : 1 ≤ G) : blockSize G n ≤ n * entryBits n := by
  unfold blockSize
  set x := n * entryBits n
  rcases Nat.eq_zero_or_pos x with h0 | hx
  · rw [h0, Nat.zero_add, Nat.div_eq_of_lt (by omega)]
  · apply Nat.div_le_of_le_mul
    have : x + G ≤ G * x + 1 := by nlinarith
    omega

/-- `r G ≥ n b`: a block holds at least one row. -/
theorem blockSize_mul_ge {G n : ℕ} (hG : 1 ≤ G) : n * entryBits n ≤ blockSize G n * G := by
  unfold blockSize
  have h1 := Nat.div_add_mod (n * entryBits n + G - 1) G
  have h2 := Nat.mod_lt (n * entryBits n + G - 1) (show 0 < G by omega)
  rw [Nat.mul_comm G] at h1
  omega

/-- `r G ≤ n b + G`: a block holds at most one row plus one cell. -/
theorem blockSize_mul_le (G n : ℕ) : blockSize G n * G ≤ n * entryBits n + G := by
  unfold blockSize
  have := Nat.div_mul_le_self (n * entryBits n + G - 1) G
  omega

theorem one_le_slotLen (M : TM) {n : ℕ} (hn : 1 ≤ n) : 1 ≤ slotLen M n :=
  one_le_blockSize (cellBits_pos M) hn

theorem slotLen_le (M : TM) (n : ℕ) : slotLen M n ≤ n * entryBits n :=
  blockSize_le (cellBits_pos M)

/-- `r G ≥ n b`: a block holds at least one row. -/
theorem slotLen_mul_ge (M : TM) (n : ℕ) : n * entryBits n ≤ slotLen M n * cellBits M :=
  blockSize_mul_ge (cellBits_pos M)

/-! ### Generic walks -/

/-- A walk frozen at time `T` still has unit steps. -/
theorem unitSteps_frozen {h : ℕ → ℤ} (hh : UnitSteps h) (T : ℕ) :
    UnitSteps (fun τ => h (min τ T)) := by
  intro τ
  show |h (min (τ + 1) T) - h (min τ T)| ≤ 1
  rcases lt_or_ge τ T with hτ | hτ
  · rw [min_eq_left hτ.le, min_eq_left (show τ + 1 ≤ T by omega)]
    exact hh τ
  · rw [min_eq_right hτ, min_eq_right (show T ≤ τ + 1 by omega)]
    simp

/-- **(V1′) for a frozen walk**: a block resident at slot `y` is within one block of the frozen
walk's block at the first step of `y`. -/
theorem frozen_V1 {h : ℕ → ℤ} (hh : UnitSteps h) {r : ℕ} (hr : 1 ≤ r) (T y : ℕ) {σ : ℤ}
    (hσ : σ ∈ pairRes r h T y) : |curBlock r (fun τ => h (min τ T)) (y * r) - σ| ≤ 1 := by
  have hyT : y * r < T := by
    by_contra hc
    push Not at hc
    rw [pairRes_empty hc] at hσ
    exact Finset.notMem_empty _ hσ
  have heq : curBlock r (fun τ => h (min τ T)) (y * r) = curBlock r h (y * r) := by
    simp only [curBlock]; rw [min_eq_left hyT.le]
  rw [heq]
  have hsub := pairRes_subset hh hr T y hσ
  simp only [Finset.mem_insert, Finset.mem_singleton] at hsub
  rcases hsub with h1 | h1 | h1 <;> rw [h1] <;> simp

/-- **(V2′) for a frozen walk**: a block strictly between the frozen walk's blocks at the first steps
of slots `y₁ ≤ y₂` is resident at some slot in between. -/
theorem frozen_V2 {h : ℕ → ℤ} (hh : UnitSteps h) {r T : ℕ} (hr : 1 ≤ r) {y₁ y₂ : ℕ}
    (hy : y₁ ≤ y₂) {σ : ℤ}
    (hσ : curBlock r (fun τ => h (min τ T)) (y₁ * r) < σ ∧
          σ < curBlock r (fun τ => h (min τ T)) (y₂ * r) ∨
        curBlock r (fun τ => h (min τ T)) (y₂ * r) < σ ∧
          σ < curBlock r (fun τ => h (min τ T)) (y₁ * r)) :
    ∃ y, y₁ ≤ y ∧ y ≤ y₂ ∧ σ ∈ pairRes r h T y := by
  set h' : ℕ → ℤ := fun τ => h (min τ T) with hh'def
  have hh' : UnitSteps h' := unitSteps_frozen hh T
  obtain ⟨y, hy1, hy2, hyσ⟩ := exists_slot_block_eq hh' hr hy (β := σ) (by
    rcases hσ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨le_trans (min_le_left _ _) h1.le, le_trans h2.le (le_max_right _ _)⟩
    · exact ⟨le_trans (min_le_right _ _) h1.le, le_trans h2.le (le_max_left _ _)⟩)
  refine ⟨y, hy1, hy2, ?_⟩
  have hyT : y * r < T := by
    by_contra hc
    push Not at hc
    have hT2 : T ≤ y₂ * r := le_trans hc (Nat.mul_le_mul_right r hy2)
    have hfr : curBlock r h' (y * r) = curBlock r h' (y₂ * r) := by
      simp only [curBlock, hh'def]; rw [min_eq_right hc, min_eq_right hT2]
    rw [hyσ] at hfr
    rcases hσ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [hfr] at h2; exact lt_irrefl _ h2
    · rw [hfr] at h1; exact lt_irrefl _ h1
  have hcur : curBlock r h' (y * r) = curBlock r h (y * r) := by
    simp only [curBlock, hh'def]; rw [min_eq_left hyT.le]
  rw [← hyσ, hcur]
  have := cur_mem_pairRes (h := h) hr hyT
  rwa [show y * r / r = y from Nat.mul_div_cancel y (by omega)] at this

/-- **The number of slots**: `⌈T/r⌉ ≤ (c G + 1) n` when `T ≤ c n² b` and a block holds a row
(`n b ≤ r G`). -/
theorem numSlots_le_of {n T r G : ℕ} {c : ℝ} (hn : 1 ≤ n)
    (hrG : n * entryBits n ≤ r * G) (hT : (T : ℝ) ≤ c * inputLength n) :
    (numSlots r T : ℝ) ≤ (c * G + 1) * n := by
  set b := entryBits n with hb
  have hb1 : 1 ≤ b := by rw [hb]; unfold entryBits; omega
  have hnb1 : 1 ≤ n * b := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hr : 1 ≤ r := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · rw [h0, Nat.zero_mul] at hrG; omega
    · exact h0
  have hG1 : 1 ≤ G := by
    rcases Nat.eq_zero_or_pos G with h0 | h0
    · rw [h0, Nat.mul_zero] at hrG; omega
    · exact h0
  set N := numSlots r T with hN
  have hNr : N * r ≤ T + r - 1 := Nat.div_mul_le_self _ _
  have hL : (inputLength n : ℝ) = n * n * b := by rw [inputLength]; push_cast; ring
  have hnb : (0 : ℝ) < n * b := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have : (1 : ℝ) ≤ b := by exact_mod_cast hb1
    positivity
  have hc : 0 ≤ c := by
    by_contra hc'
    push Not at hc'
    have : c * inputLength n < 0 := by
      rw [hL]; apply mul_neg_of_neg_of_pos hc'; nlinarith
    have : (0 : ℝ) ≤ T := Nat.cast_nonneg _
    linarith
  have h1 : ((N : ℝ) - 1) * r < T := by
    have : (N : ℝ) * r ≤ T + r - 1 := by
      have : ((N * r : ℕ) : ℝ) ≤ ((T + r - 1 : ℕ) : ℝ) := by exact_mod_cast hNr
      push_cast at this
      rw [Nat.cast_sub (by omega)] at this
      push_cast at this; linarith
    nlinarith
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · rw [h0]; push_cast
    have : (0 : ℝ) ≤ c * G + 1 := by positivity
    positivity
  · have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hpos
    have hrG' : (n : ℝ) * b ≤ r * G := by exact_mod_cast hrG
    have h2 : ((N : ℝ) - 1) * (n * b) < c * n * b * n * G := by
      calc ((N : ℝ) - 1) * (n * b) ≤ ((N : ℝ) - 1) * (r * G) :=
            mul_le_mul_of_nonneg_left hrG' (by linarith)
        _ = ((N : ℝ) - 1) * r * G := by ring
        _ < T * G := by
            apply mul_lt_mul_of_pos_right h1; exact_mod_cast (show 0 < G by omega)
        _ ≤ c * inputLength n * G := by
            apply mul_le_mul_of_nonneg_right hT; positivity
        _ = c * n * b * n * G := by rw [hL]; ring
    have h3 : (N : ℝ) - 1 < c * n * G := by
      have : ((N : ℝ) - 1) * (n * b) < (c * n * G) * (n * b) := by linarith
      exact lt_of_mul_lt_mul_right this hnb.le
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith

/-! ### Lipschitz limits and Arzelà–Ascoli -/

/-- The rescaled block trajectory of a unit-step walk is 1-Lipschitz up to `1/n`. -/
theorem blockTraj_lipschitz_approx {r n : ℕ} {h : ℕ → ℤ} (hh : UnitSteps h) (hr : 1 ≤ r)
    (hn : 1 ≤ n) {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    |blockTraj r n h u - blockTraj r n h v| ≤ |u - v| + 1 / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hW : UnitSteps (fun y => curBlock r h (y * r)) := fun y => by
    have := slot_block_step hh hr y
    simpa using this
  set a := ⌊u * n⌋₊
  set b := ⌊v * n⌋₊
  have hab : |curBlock r h (a * r) - curBlock r h (b * r)| ≤ |(a : ℤ) - (b : ℤ)| :=
    unitSteps_dist' hW b a
  have hcast : |((curBlock r h (a * r) : ℤ) : ℝ) - ((curBlock r h (b * r) : ℤ) : ℝ)| ≤
      |(a : ℝ) - b| := by
    have := (Int.cast_le (R := ℝ)).2 hab
    push_cast at this
    exact this
  have ha1 : (a : ℝ) ≤ u * n := Nat.floor_le (by positivity)
  have ha2 : u * n < a + 1 := Nat.lt_floor_add_one _
  have hb1 : (b : ℝ) ≤ v * n := Nat.floor_le (by positivity)
  have hb2 : v * n < b + 1 := Nat.lt_floor_add_one _
  have hab' : |(a : ℝ) - b| ≤ |u - v| * n + 1 := by
    have e1 : (u - v) * n ≤ |u - v| * n := mul_le_mul_of_nonneg_right (le_abs_self _) hn'.le
    have e2 : (v - u) * n ≤ |u - v| * n := by
      rw [abs_sub_comm]; exact mul_le_mul_of_nonneg_right (le_abs_self _) hn'.le
    rw [abs_le]; constructor <;> linarith
  unfold blockTraj
  rw [← sub_div, abs_div, abs_of_pos hn', div_le_iff₀ hn', add_mul, div_mul_cancel₀ _ hn'.ne']
  linarith

/-- **Uniform limits of rescaled block trajectories are 1-Lipschitz.** -/
theorem blockTraj_limit_lipschitz {c₀ : ℝ} {ns rs : ℕ → ℕ} (hns : Tendsto ns atTop atTop)
    {hs : ℕ → ℕ → ℤ} (hgood : ∀ᶠ i in atTop, UnitSteps (hs i) ∧ 1 ≤ rs i) {P : ℝ → ℝ}
    (hconv : TendstoUniformlyOn (fun i => blockTraj (rs i) (ns i) (hs i)) P atTop
      (Set.Icc 0 c₀)) :
    LipschitzOnWith 1 P (Set.Icc 0 c₀) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro u hu v hv
  rw [NNReal.coe_one, one_mul, Real.dist_eq, Real.dist_eq]
  apply le_of_forall_pos_le_add
  intro ε hε
  have hclose := Metric.tendstoUniformlyOn_iff.1 hconv (ε / 3) (by linarith)
  obtain ⟨i, hi1, hi2, hi3⟩ :=
    (hclose.and ((hns.eventually_ge_atTop (⌈3 / ε⌉₊ + 1)).and hgood)).exists
  have hn1 : 1 ≤ ns i := le_trans (Nat.le_add_left 1 _) hi2
  have hn' : (0 : ℝ) < ns i := by exact_mod_cast (show 0 < ns i by omega)
  have h1n : 1 / (ns i : ℝ) ≤ ε / 3 := by
    rw [div_le_iff₀ hn']
    have : (3 / ε) ≤ ns i := by
      have := Nat.le_ceil (3 / ε)
      have : ((⌈3 / ε⌉₊ + 1 : ℕ) : ℝ) ≤ ns i := by exact_mod_cast hi2
      push_cast at this; linarith
    rw [div_le_iff₀ hε] at this; linarith
  have hu' := hi1 u hu
  have hv' := hi1 v hv
  rw [Real.dist_eq] at hu' hv'
  have happ := blockTraj_lipschitz_approx hi3.1 hi3.2 hn1 hu.1 hv.1
  set f := blockTraj (rs i) (ns i) (hs i)
  calc |P u - P v| ≤ |P u - f u| + |f u - f v| + |f v - P v| := by
        have := abs_sub_le (P u) (f u) (P v)
        have := abs_sub_le (f u) (f v) (P v)
        linarith
    _ ≤ ε / 3 + (|u - v| + ε / 3) + ε / 3 := by
        rw [abs_sub_comm (f v)]
        linarith
    _ = |u - v| + ε := by ring

/-- A unit-step walk starting at `0`: `|blockTraj(u)| ≤ u` for `u ≥ 0`. -/
theorem blockTraj_abs_le {r n : ℕ} {h : ℕ → ℤ} (hh : UnitSteps h) (h0 : h 0 = 0) {u : ℝ}
    (hu : 0 ≤ u) : |blockTraj r n h u| ≤ u := by
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0; simpa [blockTraj] using hu
  rcases Nat.eq_zero_or_pos r with hr0 | hr
  · subst hr0; simpa [blockTraj, curBlock, blockOf] using hu
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hW : UnitSteps (fun y => curBlock r h (y * r)) := fun y => by
    have := slot_block_step hh hr y
    simpa using this
  have hW0 : curBlock r h (0 * r) = 0 := by
    simp [curBlock, blockOf, h0]
  set a := ⌊u * n⌋₊
  have ha : |curBlock r h (a * r) - curBlock r h (0 * r)| ≤ |(a : ℤ) - (0 : ℕ)| :=
    unitSteps_dist' hW 0 a
  rw [hW0, sub_zero] at ha
  have ha' : |((curBlock r h (a * r) : ℤ) : ℝ)| ≤ a := by
    have := (Int.cast_le (R := ℝ)).2 ha
    push_cast at this
    simpa using this
  have ha1 : (a : ℝ) ≤ u * n := Nat.floor_le (by positivity)
  unfold blockTraj
  rw [abs_div, abs_of_pos hn', div_le_iff₀ hn']
  linarith

/-- **Arzelà–Ascoli for block walks.** If, eventually, the block sizes are positive and the `k` walks
have unit steps and start at `0`, a subsequence of the rescaled block trajectories converges
uniformly on `[0, c₀]`. -/
theorem exists_subseq_blockTraj {k : ℕ} (c₀ : ℝ) {ns rs : ℕ → ℕ} (hns : Tendsto ns atTop atTop)
    {hs : ℕ → Fin k → ℕ → ℤ}
    (hgood : ∀ᶠ i in atTop, 1 ≤ rs i ∧ ∀ t, UnitSteps (hs i t) ∧ hs i t 0 = 0) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ P : Fin k → ℝ → ℝ, ∀ t,
      TendstoUniformlyOn (fun i => blockTraj (rs (φ i)) (ns (φ i)) (hs (φ i) t)) (P t) atTop
        (Set.Icc 0 c₀) := by
  classical
  rcases lt_or_ge c₀ 0 with hneg | hc₀0
  · refine ⟨id, strictMono_id, fun _ _ => 0, fun t => ?_⟩
    rw [Set.Icc_eq_empty (by linarith)]
    exact tendstoUniformlyOn_empty
  have hab : -c₀ ≤ c₀ := by linarith
  -- the values at rational points, in a compact metrizable product
  let x : ℕ → ({q : ℚ // 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ c₀} × Fin k → Set.Icc (-c₀) c₀) :=
    fun i qt => Set.projIcc (-c₀) c₀ hab (blockTraj (rs i) (ns i) (hs i qt.2) (qt.1 : ℝ))
  obtain ⟨a, φ, hφ, hlim⟩ := CompactSpace.tendsto_subseq x
  refine ⟨φ, hφ, ?_⟩
  have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hnsφ : Tendsto (fun i => ns (φ i)) atTop atTop := hns.comp hφt
  have hgoodφ : ∀ᶠ i in atTop, 1 ≤ rs (φ i) ∧ ∀ t, UnitSteps (hs (φ i) t) ∧ hs (φ i) t 0 = 0 :=
    hφt.eventually hgood
  -- convergence at rational points
  have hpt : ∀ (q : {q : ℚ // 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ c₀}) (t : Fin k),
      Tendsto (fun i => blockTraj (rs (φ i)) (ns (φ i)) (hs (φ i) t) (q : ℝ)) atTop
        (𝓝 (a (q, t) : ℝ)) := by
    intro q t
    have h1 : Tendsto (fun i => ((x (φ i) (q, t) : Set.Icc (-c₀) c₀) : ℝ)) atTop
        (𝓝 (a (q, t) : ℝ)) :=
      (continuous_subtype_val.tendsto _).comp ((continuous_apply (q, t)).tendsto _ |>.comp hlim)
    refine h1.congr' (hgoodφ.mono fun i hi => ?_)
    have hmem : blockTraj (rs (φ i)) (ns (φ i)) (hs (φ i) t) (q : ℝ) ∈ Set.Icc (-c₀) c₀ := by
      have := blockTraj_abs_le (r := rs (φ i)) (n := ns (φ i)) (hi.2 t).1 (hi.2 t).2 q.2.1
      rw [abs_le] at this
      exact ⟨by linarith [q.2.2], by linarith [q.2.2]⟩
    show ((Set.projIcc (-c₀) c₀ hab (blockTraj (rs (φ i)) (ns (φ i)) (hs (φ i) t) (q : ℝ)) :
      Set.Icc (-c₀) c₀) : ℝ) = blockTraj (rs (φ i)) (ns (φ i)) (hs (φ i) t) (q : ℝ)
    rw [Set.projIcc_of_mem hab hmem]
  -- uniformly Cauchy on `[0, c₀]`
  have hcauchy : ∀ t, UniformCauchySeqOn
      (fun i => blockTraj (rs (φ i)) (ns (φ i)) (hs (φ i) t)) atTop (Set.Icc 0 c₀) := by
    intro t
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    obtain ⟨q₀, hq₀pos, hq₀lt⟩ : ∃ q₀ : ℚ, (0 : ℝ) < q₀ ∧ (q₀ : ℝ) < ε / 5 :=
      exists_rat_btwn (by positivity)
    set L := ⌊c₀ / q₀⌋₊ with hL
    have hmesh : ∀ j ≤ L, 0 ≤ (((j : ℚ) * q₀ : ℚ) : ℝ) ∧ (((j : ℚ) * q₀ : ℚ) : ℝ) ≤ c₀ := by
      intro j hj
      push_cast
      refine ⟨by positivity, ?_⟩
      have : (j : ℝ) ≤ c₀ / q₀ := le_trans (by exact_mod_cast hj) (Nat.floor_le (by positivity))
      rwa [le_div_iff₀ hq₀pos] at this
    have hC : ∀ j ∈ Finset.range (L + 1), ∃ N, ∀ m ≥ N, ∀ n ≥ N,
        dist (blockTraj (rs (φ m)) (ns (φ m)) (hs (φ m) t) (((j : ℚ) * q₀ : ℚ) : ℝ))
          (blockTraj (rs (φ n)) (ns (φ n)) (hs (φ n) t) (((j : ℚ) * q₀ : ℚ) : ℝ)) < ε / 5 := by
      intro j hj
      have hj' : j ≤ L := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
      have := (hpt ⟨(j : ℚ) * q₀, hmesh j hj'⟩ t).cauchySeq
      exact Metric.cauchySeq_iff.1 this (ε / 5) (by positivity)
    choose! Nk hNk using hC
    obtain ⟨N₂, hN₂⟩ :=
      eventually_atTop.1 ((hnsφ.eventually_ge_atTop (⌈5 / ε⌉₊ + 1)).and hgoodφ)
    refine ⟨max N₂ ((Finset.range (L + 1)).sup Nk), ?_⟩
    intro m hm n hn u hu
    have hmN : N₂ ≤ m := le_trans (le_max_left _ _) hm
    have hnN : N₂ ≤ n := le_trans (le_max_left _ _) hn
    -- the mesh point below `u`
    set j := ⌊u / q₀⌋₊ with hj
    have hjL : j ≤ L := Nat.floor_le_floor (div_le_div_of_nonneg_right hu.2 hq₀pos.le)
    have hju1 : (j : ℝ) * q₀ ≤ u := by
      have := Nat.floor_le (show 0 ≤ u / q₀ from div_nonneg hu.1 hq₀pos.le)
      rwa [le_div_iff₀ hq₀pos] at this
    have hju2 : u < ((j : ℝ) + 1) * q₀ := by
      have := Nat.lt_floor_add_one (u / q₀)
      rwa [div_lt_iff₀ hq₀pos] at this
    have hdist : |u - (((j : ℚ) * q₀ : ℚ) : ℝ)| < ε / 5 := by
      push_cast
      rw [abs_lt]; constructor <;> nlinarith
    -- large sizes
    have hlarge : ∀ i ≥ N₂, 1 ≤ ns (φ i) ∧ 1 / (ns (φ i) : ℝ) < ε / 5 ∧ 1 ≤ rs (φ i) ∧
        UnitSteps (hs (φ i) t) := by
      intro i hi
      obtain ⟨h1, h2⟩ := hN₂ i hi
      refine ⟨le_trans (Nat.le_add_left 1 _) h1, ?_, h2.1, (h2.2 t).1⟩
      have hn' : (5 / ε) < ns (φ i) := by
        have := Nat.le_ceil (5 / ε)
        have : ((⌈5 / ε⌉₊ + 1 : ℕ) : ℝ) ≤ ns (φ i) := by exact_mod_cast h1
        push_cast at this; linarith
      have hpos : (0 : ℝ) < ns (φ i) := lt_of_le_of_lt (by positivity) hn'
      rw [div_lt_iff₀ hpos]
      rw [div_lt_iff₀ hε] at hn'
      linarith
    obtain ⟨hm1, hm2, hm3, hm4⟩ := hlarge m hmN
    obtain ⟨hn1, hn2, hn3, hn4⟩ := hlarge n hnN
    have hjmem : j ∈ Finset.range (L + 1) := Finset.mem_range.2 (Nat.lt_succ_of_le hjL)
    have hNkm : Nk j ≤ m :=
      le_trans (Finset.le_sup hjmem) (le_trans (le_max_right _ _) hm)
    have hNkn : Nk j ≤ n :=
      le_trans (Finset.le_sup hjmem) (le_trans (le_max_right _ _) hn)
    set fm := blockTraj (rs (φ m)) (ns (φ m)) (hs (φ m) t)
    set fn := blockTraj (rs (φ n)) (ns (φ n)) (hs (φ n) t)
    set q := (((j : ℚ) * q₀ : ℚ) : ℝ)
    have h1 : |fm u - fm q| ≤ |u - q| + 1 / ns (φ m) :=
      blockTraj_lipschitz_approx hm4 hm3 hm1 hu.1 (hmesh j hjL).1
    have h2 : |fn u - fn q| ≤ |u - q| + 1 / ns (φ n) :=
      blockTraj_lipschitz_approx hn4 hn3 hn1 hu.1 (hmesh j hjL).1
    have h3 := hNk j hjmem m hNkm n hNkn
    rw [Real.dist_eq] at h3 ⊢
    calc |fm u - fn u| ≤ |fm u - fm q| + |fm q - fn q| + |fn q - fn u| := by
          have := abs_sub_le (fm u) (fm q) (fn u)
          have := abs_sub_le (fm q) (fn q) (fn u)
          linarith
      _ < ε := by
          rw [abs_sub_comm (fn q)]
          linarith
  -- the limits
  refine ⟨fun t u => limUnder atTop
    (fun i => blockTraj (rs (φ i)) (ns (φ i)) (hs (φ i) t) u), fun t => ?_⟩
  apply (hcauchy t).tendstoUniformlyOn_of_tendsto
  intro u hu
  exact ((hcauchy t).cauchySeq hu).tendsto_limUnder

/-! ### The machine walk -/

/-- **After halting the run is frozen**: a work head's walk equals its walk frozen at the halting
time. -/
theorem workTraj_frozen {M : TM} {w : List Bool} {T : ℕ} (hT : HaltsAt M w T) (t : Fin M.k) :
    (fun τ => workTraj M w (min τ T) t) = fun τ => workTraj M w τ t := by
  funext τ
  rcases le_total τ T with hτ | hτ
  · rw [min_eq_left hτ]
  · rw [min_eq_right hτ]; simp only [workTraj]; rw [run_of_le_of_none hT.2 hτ]

theorem pairRes_V2 {M : TM} {w : List Bool} {T r : ℕ} (hT : HaltsAt M w T) (hr : 1 ≤ r)
    (t : Fin M.k) {y₁ y₂ : ℕ} (hy : y₁ ≤ y₂) {σ : ℤ}
    (hσ : curBlock r (fun τ => workTraj M w τ t) (y₁ * r) < σ ∧
          σ < curBlock r (fun τ => workTraj M w τ t) (y₂ * r) ∨
        curBlock r (fun τ => workTraj M w τ t) (y₂ * r) < σ ∧
          σ < curBlock r (fun τ => workTraj M w τ t) (y₁ * r)) :
    ∃ y, y₁ ≤ y ∧ y ≤ y₂ ∧ σ ∈ pairRes r (fun τ => workTraj M w τ t) T y := by
  have hfz : ∀ y, curBlock r (fun τ => workTraj M w (min τ T) t) (y * r) =
      curBlock r (fun τ => workTraj M w τ t) (y * r) := fun y => by rw [workTraj_frozen hT t]
  exact frozen_V2 (unitSteps_workTraj M w t) hr hy (by rw [hfz, hfz]; exact hσ)

/-! ### The number of slots -/

theorem numSlots_le_horizon {M : TM} {n T : ℕ} {c : ℝ} (hn : 1 ≤ n)
    (hT : (T : ℝ) ≤ c * inputLength n) :
    (numSlots (slotLen M n) T : ℝ) ≤ horizon M c * n :=
  numSlots_le_of hn (slotLen_mul_ge M n) hT

/-! ### Rescaled trajectories -/

theorem rescaledTraj_limit_lipschitz {M : TM} {c : ℝ} {ns : ℕ → ℕ}
    (hns : Tendsto ns atTop atTop) {t : Fin M.k} {P : ℝ → ℝ}
    (hconv : TendstoUniformlyOn (fun i => rescaledTraj M (ns i) t) P atTop
      (Set.Icc 0 (horizon M c))) :
    LipschitzOnWith 1 P (Set.Icc 0 (horizon M c)) :=
  blockTraj_limit_lipschitz hns (rs := fun i => slotLen M (ns i))
    (hs := fun i τ => workTraj M (zeroInput (ns i)) τ t)
    ((hns.eventually_ge_atTop 1).mono fun _i hi => ⟨unitSteps_workTraj M _ t, one_le_slotLen M hi⟩)
    hconv

theorem zeroInput_mem (n : ℕ) : zeroInput n ∈ matrixInputs n (entryBits n) := ⟨_, rfl⟩

end Transpose.Tape.Impl
