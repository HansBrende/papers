import Transpose.Tape.MStarClass

/-!
# Theorem M* for machines correct on a large set of inputs (robust and non-uniform M*)

The class form of Theorem M\* (`theoremMStar_class_nonuniform`) and the trace-class cut lemmas need
the machine to be correct only on the class itself (`ClassCorrect`). So M\* survives errors.

* `class_of_fast`: the popular class of a machine fast and correct on a set `F₀` of co-entropy
  `m`: a trace class `F ⊆ F₀` of co-entropy `≤ m + C n b` (`C = traceConst M c`) on which the
  machine is correct (also the source of `class_of_fastOn`, `CEMain.lean`).
* `theoremMStar_level_nonuniform`: let machines `M_i` (one per size `n_i → ∞`, with `k` work tapes and
  `G` bits per cell; any transition tables, and state counts with `⌈log₂(q_i+1)⌉ = o(L_i)`) halt
  within `c L_i` steps with the transposed output on every input of a set `W_i` (of matrix inputs)
  of co-entropy `m_i` (`2^{L_i} ≤ 2^{m_i} |W_i|`), with `m_i / L_i → 0`. Then there are trace classes
  `F_i ⊆ W_i` with `2^{L_i} ≤ 2^{D_i} |F_i|`, `D_i ≤ m_i + C n_i b_i` (`C = traceConst M_0 c`, the
  same for all `i`) and `D_i / L_i → 0`; their representatives' rescaled trajectories have uniformly
  convergent subsequences; and every subsequential limit is 1-Lipschitz and satisfies (★). The proof
  is `class_of_fast` followed by `theoremMStar_class_nonuniform`.
* `theoremMStar_level_robust`: the case of one machine. With `W_i` all matrix inputs and `m_i = 0`
  it gives `theoremMStar_level_adaptive`.
* `theoremMStar_excess_nonuniform` and its case of one machine `theoremMStar_excess_robust`: the
  labelling-free form (`excess_of_star`): every such limit has total excess level multiplicity `≥ 1`
  and total range `≤ k c₀ − 1`, and is not monotone on every tape.
-/

namespace Transpose.Tape.Impl

open Transpose MeasureTheory Filter Topology TSDiagram

open scoped ENNReal

/-- **The popular class of a fast transposer.** Let `M` output the transposed encoding within `c L`
steps on every input of a set `F₀` of co-entropy `≤ m` (`2^L ≤ 2^m |F₀|`). Then some trace class
`F ⊆ F₀`, with halting time `T ≤ c L`, has co-entropy `≤ m + C n b` (`C = traceConst M c`), and `M`
is correct on it. -/
theorem class_of_fast {M : TM} {c : ℝ} {m n : ℕ} (hn1 : 1 ≤ n) {F₀ : Set (List Bool)}
    (hco : 2 ^ (n * n * entryBits n) ≤ 2 ^ m * F₀.ncard)
    (hfast : ∀ w ∈ F₀, ∃ T : ℕ, (T : ℝ) ≤ c * inputLength n ∧ HaltsAt M w T ∧
      ∃ A : Matrix, w = encode n (entryBits n) A ∧
        (run M w T).outRev.reverse = encode n (entryBits n) (transpose A)) :
    ∃ T : ℕ, (T : ℝ) ≤ c * inputLength n ∧ ∃ (F : Set (List Bool)) (w₀ : List Bool),
      TraceClass M n (entryBits n) (slotLen M n) T F w₀ ∧ F ⊆ F₀ ∧
      ClassCorrect M n (entryBits n) T F ∧
      2 ^ (n * n * entryBits n) ≤ 2 ^ (m + traceConst M c * n * entryBits n) * F.ncard := by
  have hne : F₀.Nonempty := Set.nonempty_of_ncard_ne_zero (ncard_pos_of_coentropy hco).ne'
  have hcL : 0 ≤ c * inputLength n := by
    obtain ⟨w, hw⟩ := hne
    obtain ⟨T, hT, -⟩ := hfast w hw
    exact le_trans (Nat.cast_nonneg T) hT
  obtain ⟨T, hTle, F, w₀, hF, hFsub, hcount⟩ := exists_popular_traceClass_on
    (Tmax := ⌊c * inputLength n⌋₊) (one_le_slotLen M hn1) (slotLen_le M n)
    (fun w hw => by obtain ⟨T, -, -, A, rfl, -⟩ := hfast w hw; exact ⟨A, rfl⟩) hne
    (fun w hw => by obtain ⟨T, hT, hh, -⟩ := hfast w hw; exact ⟨T, Nat.le_floor hT, hh⟩)
  refine ⟨T, le_trans (by exact_mod_cast hTle) (Nat.floor_le hcL), F, w₀, hF, hFsub,
    fun w hw => ?_, ?_⟩
  · obtain ⟨T', -, hh, hcw⟩ := hfast w (hFsub hw)
    rw [haltsAt_unique (hF.2 w hw).2.1 hh]
    exact hcw
  · have hpc : traceCount M.k n (numSlots (slotLen M n) ⌊c * inputLength n⌋₊)
        ⌊c * inputLength n⌋₊ ≤ 2 ^ (traceConst M c * n * entryBits n) :=
      le_trans (Nat.le_pow_clog (by norm_num) _)
        (Nat.pow_le_pow_right (by norm_num) (traceBits_le hn1 (Nat.floor_le hcL)))
    calc 2 ^ (n * n * entryBits n) ≤ 2 ^ m * F₀.ncard := hco
      _ ≤ 2 ^ m * (2 ^ (traceConst M c * n * entryBits n) * F.ncard) :=
          Nat.mul_le_mul_left _ (le_trans hcount (Nat.mul_le_mul_right _ hpc))
      _ = 2 ^ (m + traceConst M c * n * entryBits n) * F.ncard := by
          rw [← Nat.mul_assoc, ← pow_add]

/-- **Theorem M\* for non-uniform machines fast and correct on a set of co-entropy `o(L)`.** At sizes
`n_i → ∞`, let `M_i` be machines with `k` work tapes and `G` bits per cell (`cellBits`; any transition
tables, and any state counts with `⌈log₂(q_i+1)⌉ = o(L_i)`), and let `M_i` halt within `c L_i` steps
with the transposed output on every input of a set `W_i` (of matrix inputs) of co-entropy `m_i`
(`2^{L_i} ≤ 2^{m_i} |W_i|`), with `m_i / L_i → 0`. Then there are trace classes `F_i ⊆ W_i` with
`2^{L_i} ≤ 2^{D_i} |F_i|`, `D_i ≤ m_i + C n_i b_i` (`C = traceConst M_i c`, which depends on `k`, `G`
and `c` only) and `D_i / L_i → 0`; their representatives' rescaled trajectories have uniformly
convergent subsequences on `[0, c₀]`, `c₀ = c G + 1`; and every subsequential limit is 1-Lipschitz
and satisfies (★). The tapes of `M_i` are indexed by `Fin k` through `M_i.k = k`.

The popular classes come from `class_of_fast`, and the limits from `theoremMStar_class_nonuniform`
(Theorem M\* for code-carrying diagrams applied to the class codes, with
`⌈log₂(q_i+1)⌉ + (k+1)⌈log₂(2T_i+1)⌉ = o(L_i)` extra bits per memory edge). -/
theorem theoremMStar_level_nonuniform {k G : ℕ} {c : ℝ} {ns : ℕ → ℕ}
    (hns : Tendsto ns atTop atTop) {Ms : ℕ → TM} (hk : ∀ i, (Ms i).k = k)
    (hG : ∀ i, cellBits (Ms i) = G)
    (hq : Tendsto (fun i => (Nat.clog 2 ((Ms i).q + 1) : ℝ) / inputLength (ns i)) atTop (𝓝 0))
    {Ws : ℕ → Set (List Bool)} {ms : ℕ → ℕ}
    (hm : ∀ᶠ i in atTop, 2 ^ inputLength (ns i) ≤ 2 ^ ms i * (Ws i).ncard)
    (hmL : Tendsto (fun i => (ms i : ℝ) / inputLength (ns i)) atTop (𝓝 0))
    (hfast : ∀ᶠ i in atTop, ∀ w ∈ Ws i, ∃ T : ℕ, (T : ℝ) ≤ c * inputLength (ns i) ∧
      HaltsAt (Ms i) w T ∧ ∃ A : Matrix, w = encode (ns i) (entryBits (ns i)) A ∧
        (run (Ms i) w T).outRev.reverse = encode (ns i) (entryBits (ns i)) (transpose A)) :
    ∃ (Ts Ds : ℕ → ℕ) (Fs : ℕ → Set (List Bool)) (ws : ℕ → List Bool),
      (∀ᶠ i in atTop,
        TraceClass (Ms i) (ns i) (entryBits (ns i)) (slotLen (Ms i) (ns i)) (Ts i) (Fs i) (ws i) ∧
          Fs i ⊆ Ws i ∧ (Ts i : ℝ) ≤ c * inputLength (ns i) ∧
          2 ^ inputLength (ns i) ≤ 2 ^ Ds i * (Fs i).ncard) ∧
      (∀ᶠ i in atTop, Ds i ≤ ms i + traceConst (Ms 0) c * ns i * entryBits (ns i)) ∧
      Tendsto (fun i => (Ds i : ℝ) / inputLength (ns i)) atTop (𝓝 0) ∧
      (∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ P : Fin k → ℝ → ℝ, ∀ t,
        TendstoUniformlyOn (fun i => rescaledTrajOf (Ms (φ i)) (ns (φ i)) (ws (φ i))
          (Fin.cast (hk (φ i)).symm t)) (P t) atTop (Set.Icc 0 (c * G + 1))) ∧
      ∀ φ : ℕ → ℕ, StrictMono φ → ∀ P : Fin k → ℝ → ℝ,
        (∀ t, TendstoUniformlyOn (fun i => rescaledTrajOf (Ms (φ i)) (ns (φ i)) (ws (φ i))
          (Fin.cast (hk (φ i)).symm t)) (P t) atTop (Set.Icc 0 (c * G + 1))) →
        (∀ t, LipschitzOnWith 1 (P t) (Set.Icc 0 (c * G + 1))) ∧
        ∀ (θ : ℝ≥0∞) (S : Set ℝ) (β : ℝ → ℕ), FinUnionIcc S → PiecewiseConstOn β S (c * G + 1) →
          (∀ ℓ, volume {u | u ∈ Set.Icc 0 (c * G + 1) ∧ u ∉ S ∧ β u = ℓ} ≤ θ) →
          1 ≤ (∑ t, ∫⁻ p, levelCross (P t) S β (c * G + 1) p) + 2 * θ +
            2 * k * volume (S ∩ Set.Icc 0 (c * G + 1)) := by
  classical
  -- the trace constant does not depend on `i`
  have htc : ∀ i, traceConst (Ms i) c = traceConst (Ms 0) c := by
    intro i
    unfold traceConst horizon
    rw [hk i, hk 0, hG i, hG 0]
  -- the hypotheses at one size
  let Hyp : ℕ → Prop := fun i => 1 ≤ ns i ∧ 2 ^ inputLength (ns i) ≤ 2 ^ ms i * (Ws i).ncard ∧
    ∀ w ∈ Ws i, ∃ T : ℕ, (T : ℝ) ≤ c * inputLength (ns i) ∧ HaltsAt (Ms i) w T ∧
      ∃ A : Matrix, w = encode (ns i) (entryBits (ns i)) A ∧
        (run (Ms i) w T).outRev.reverse = encode (ns i) (entryBits (ns i)) (transpose A)
  -- the popular trace class inside `W_i`
  have key : ∀ i, ∃ (T : ℕ) (F : Set (List Bool)) (w : List Bool), Hyp i →
      (T : ℝ) ≤ c * inputLength (ns i) ∧
      TraceClass (Ms i) (ns i) (entryBits (ns i)) (slotLen (Ms i) (ns i)) T F w ∧ F ⊆ Ws i ∧
      ClassCorrect (Ms i) (ns i) (entryBits (ns i)) T F ∧
      2 ^ inputLength (ns i) ≤
        2 ^ (ms i + traceConst (Ms 0) c * ns i * entryBits (ns i)) * F.ncard := by
    intro i
    by_cases hyp : Hyp i
    · obtain ⟨T, hT, F, w, hF, hFW, hcc, hco⟩ := class_of_fast hyp.1 hyp.2.1 hyp.2.2
      exact ⟨T, F, w, fun _ => ⟨hT, hF, hFW, hcc, htc i ▸ hco⟩⟩
    · exact ⟨0, ∅, [], fun h => absurd h hyp⟩
  choose Ts Fs ws hkey using key
  have hev : ∀ᶠ i in atTop, Hyp i := ((hns.eventually_ge_atTop 1).and (hm.and hfast)).mono
    fun i h => ⟨h.1, h.2.1, h.2.2⟩
  let Ds : ℕ → ℕ := fun i => ms i + traceConst (Ms 0) c * ns i * entryBits (ns i)
  have hall : ∀ᶠ i in atTop,
      TraceClass (Ms i) (ns i) (entryBits (ns i)) (slotLen (Ms i) (ns i)) (Ts i) (Fs i) (ws i) ∧
        Fs i ⊆ Ws i ∧ (Ts i : ℝ) ≤ c * inputLength (ns i) ∧
        2 ^ inputLength (ns i) ≤ 2 ^ Ds i * (Fs i).ncard :=
    hev.mono fun i hi => ⟨(hkey i hi).2.1, (hkey i hi).2.2.1, (hkey i hi).1, (hkey i hi).2.2.2.2⟩
  have hDL : Tendsto (fun i => (Ds i : ℝ) / inputLength (ns i)) atTop (𝓝 0) := by
    have h := hmL.add (div_inputLength_tendsto (C := traceConst (Ms 0) c) hns
      (Ds := fun i => traceConst (Ms 0) c * ns i * entryBits (ns i))
      (Eventually.of_forall fun _ => le_rfl))
    rw [add_zero] at h
    exact h.congr fun i => by simp only [Ds]; push_cast; rw [add_div]
  exact ⟨Ts, Ds, Fs, ws, hall, Eventually.of_forall fun _ => le_rfl, hDL,
    theoremMStar_class_nonuniform hns hk hG hq (hall.mono fun i h => h.1)
      (hall.mono fun i h => h.2.2.2) hDL (hev.mono fun i hi => (hkey i hi).2.2.2.1)
      (hall.mono fun i h => h.2.2.1)⟩

/-- **Theorem M\* for machines fast and correct on a set of co-entropy `o(L)`**: the case of one
machine of `theoremMStar_level_nonuniform`. -/
theorem theoremMStar_level_robust {M : TM} {c : ℝ} {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop)
    {Ws : ℕ → Set (List Bool)} {ms : ℕ → ℕ}
    (hm : ∀ᶠ i in atTop, 2 ^ inputLength (ns i) ≤ 2 ^ ms i * (Ws i).ncard)
    (hmL : Tendsto (fun i => (ms i : ℝ) / inputLength (ns i)) atTop (𝓝 0))
    (hfast : ∀ᶠ i in atTop, ∀ w ∈ Ws i, ∃ T : ℕ, (T : ℝ) ≤ c * inputLength (ns i) ∧
      HaltsAt M w T ∧ ∃ A : Matrix, w = encode (ns i) (entryBits (ns i)) A ∧
        (run M w T).outRev.reverse = encode (ns i) (entryBits (ns i)) (transpose A)) :
    ∃ (Ts Ds : ℕ → ℕ) (Fs : ℕ → Set (List Bool)) (ws : ℕ → List Bool),
      (∀ᶠ i in atTop,
        TraceClass M (ns i) (entryBits (ns i)) (slotLen M (ns i)) (Ts i) (Fs i) (ws i) ∧
          Fs i ⊆ Ws i ∧ (Ts i : ℝ) ≤ c * inputLength (ns i) ∧
          2 ^ inputLength (ns i) ≤ 2 ^ Ds i * (Fs i).ncard) ∧
      (∀ᶠ i in atTop, Ds i ≤ ms i + traceConst M c * ns i * entryBits (ns i)) ∧
      Tendsto (fun i => (Ds i : ℝ) / inputLength (ns i)) atTop (𝓝 0) ∧
      (∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ P : Fin M.k → ℝ → ℝ, ∀ t,
        TendstoUniformlyOn (fun i => rescaledTrajOf M (ns (φ i)) (ws (φ i)) t) (P t) atTop
          (Set.Icc 0 (horizon M c))) ∧
      ∀ φ : ℕ → ℕ, StrictMono φ → ∀ P : Fin M.k → ℝ → ℝ,
        (∀ t, TendstoUniformlyOn (fun i => rescaledTrajOf M (ns (φ i)) (ws (φ i)) t) (P t) atTop
          (Set.Icc 0 (horizon M c))) →
        (∀ t, LipschitzOnWith 1 (P t) (Set.Icc 0 (horizon M c))) ∧
        ∀ (θ : ℝ≥0∞) (S : Set ℝ) (β : ℝ → ℕ), FinUnionIcc S → PiecewiseConstOn β S (horizon M c) →
          (∀ ℓ, volume {u | u ∈ Set.Icc 0 (horizon M c) ∧ u ∉ S ∧ β u = ℓ} ≤ θ) →
          1 ≤ (∑ t, ∫⁻ p, levelCross (P t) S β (horizon M c) p) + 2 * θ +
            2 * M.k * volume (S ∩ Set.Icc 0 (horizon M c)) :=
  theoremMStar_level_nonuniform hns (Ms := fun _ => M) (fun _ => rfl) (fun _ => rfl)
    (tendsto_const_nhds.div_atTop (inputLength_tendsto hns)) hm hmL hfast

/-- **Labelling-free non-uniform M\*.** Under the hypotheses of `theoremMStar_level_nonuniform`,
every subsequential limit `P` of the popular representatives' rescaled trajectories has total excess
level multiplicity `Σ_t ∫⁻ (#Λ_t(p) − 1) dp ≥ 1` and total range `1 + Σ_t |P_t([0, c₀])| ≤ k c₀`,
and its paths are not all monotone (`excess_of_star`). -/
theorem theoremMStar_excess_nonuniform {k G : ℕ} {c : ℝ} {ns : ℕ → ℕ}
    (hns : Tendsto ns atTop atTop) {Ms : ℕ → TM} (hk : ∀ i, (Ms i).k = k)
    (hG : ∀ i, cellBits (Ms i) = G)
    (hq : Tendsto (fun i => (Nat.clog 2 ((Ms i).q + 1) : ℝ) / inputLength (ns i)) atTop (𝓝 0))
    {Ws : ℕ → Set (List Bool)} {ms : ℕ → ℕ}
    (hm : ∀ᶠ i in atTop, 2 ^ inputLength (ns i) ≤ 2 ^ ms i * (Ws i).ncard)
    (hmL : Tendsto (fun i => (ms i : ℝ) / inputLength (ns i)) atTop (𝓝 0))
    (hfast : ∀ᶠ i in atTop, ∀ w ∈ Ws i, ∃ T : ℕ, (T : ℝ) ≤ c * inputLength (ns i) ∧
      HaltsAt (Ms i) w T ∧ ∃ A : Matrix, w = encode (ns i) (entryBits (ns i)) A ∧
        (run (Ms i) w T).outRev.reverse = encode (ns i) (entryBits (ns i)) (transpose A)) :
    ∃ (Ts Ds : ℕ → ℕ) (Fs : ℕ → Set (List Bool)) (ws : ℕ → List Bool),
      (∀ᶠ i in atTop,
        TraceClass (Ms i) (ns i) (entryBits (ns i)) (slotLen (Ms i) (ns i)) (Ts i) (Fs i) (ws i) ∧
          Fs i ⊆ Ws i ∧ (Ts i : ℝ) ≤ c * inputLength (ns i) ∧
          2 ^ inputLength (ns i) ≤ 2 ^ Ds i * (Fs i).ncard) ∧
      (∀ᶠ i in atTop, Ds i ≤ ms i + traceConst (Ms 0) c * ns i * entryBits (ns i)) ∧
      Tendsto (fun i => (Ds i : ℝ) / inputLength (ns i)) atTop (𝓝 0) ∧
      (∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ P : Fin k → ℝ → ℝ, ∀ t,
        TendstoUniformlyOn (fun i => rescaledTrajOf (Ms (φ i)) (ns (φ i)) (ws (φ i))
          (Fin.cast (hk (φ i)).symm t)) (P t) atTop (Set.Icc 0 (c * G + 1))) ∧
      ∀ φ : ℕ → ℕ, StrictMono φ → ∀ P : Fin k → ℝ → ℝ,
        (∀ t, TendstoUniformlyOn (fun i => rescaledTrajOf (Ms (φ i)) (ns (φ i)) (ws (φ i))
          (Fin.cast (hk (φ i)).symm t)) (P t) atTop (Set.Icc 0 (c * G + 1))) →
        1 ≤ ∑ t, ∫⁻ p, levelExcess (P t) (c * G + 1) p ∧
          1 + ∑ t, volume (P t '' Set.Icc 0 (c * G + 1)) ≤ k * ENNReal.ofReal (c * G + 1) ∧
          ¬ ∀ t, MonotoneOn (P t) (Set.Icc 0 (c * G + 1)) ∨
            AntitoneOn (P t) (Set.Icc 0 (c * G + 1)) := by
  obtain ⟨Ts, Ds, Fs, ws, hall, hDs, hDL, hsub, hlim⟩ :=
    theoremMStar_level_nonuniform hns hk hG hq hm hmL hfast
  exact ⟨Ts, Ds, Fs, ws, hall, hDs, hDL, hsub, fun φ hφ P hP =>
    excess_of_star (hlim φ hφ P hP).1 (hlim φ hφ P hP).2⟩

/-- **Labelling-free robust M\*.** Under the hypotheses of `theoremMStar_level_robust`, every
subsequential limit `P` of the popular representatives' rescaled trajectories has total excess level
multiplicity `Σ_t ∫⁻ (#Λ_t(p) − 1) dp ≥ 1` and total range `1 + Σ_t |P_t([0, c₀])| ≤ k c₀`, and its
paths are not all monotone: the case of one machine of `theoremMStar_excess_nonuniform`. -/
theorem theoremMStar_excess_robust {M : TM} {c : ℝ} {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop)
    {Ws : ℕ → Set (List Bool)} {ms : ℕ → ℕ}
    (hm : ∀ᶠ i in atTop, 2 ^ inputLength (ns i) ≤ 2 ^ ms i * (Ws i).ncard)
    (hmL : Tendsto (fun i => (ms i : ℝ) / inputLength (ns i)) atTop (𝓝 0))
    (hfast : ∀ᶠ i in atTop, ∀ w ∈ Ws i, ∃ T : ℕ, (T : ℝ) ≤ c * inputLength (ns i) ∧
      HaltsAt M w T ∧ ∃ A : Matrix, w = encode (ns i) (entryBits (ns i)) A ∧
        (run M w T).outRev.reverse = encode (ns i) (entryBits (ns i)) (transpose A)) :
    ∃ (Ts Ds : ℕ → ℕ) (Fs : ℕ → Set (List Bool)) (ws : ℕ → List Bool),
      (∀ᶠ i in atTop,
        TraceClass M (ns i) (entryBits (ns i)) (slotLen M (ns i)) (Ts i) (Fs i) (ws i) ∧
          Fs i ⊆ Ws i ∧ (Ts i : ℝ) ≤ c * inputLength (ns i) ∧
          2 ^ inputLength (ns i) ≤ 2 ^ Ds i * (Fs i).ncard) ∧
      Tendsto (fun i => (Ds i : ℝ) / inputLength (ns i)) atTop (𝓝 0) ∧
      (∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ P : Fin M.k → ℝ → ℝ, ∀ t,
        TendstoUniformlyOn (fun i => rescaledTrajOf M (ns (φ i)) (ws (φ i)) t) (P t) atTop
          (Set.Icc 0 (horizon M c))) ∧
      ∀ φ : ℕ → ℕ, StrictMono φ → ∀ P : Fin M.k → ℝ → ℝ,
        (∀ t, TendstoUniformlyOn (fun i => rescaledTrajOf M (ns (φ i)) (ws (φ i)) t) (P t) atTop
          (Set.Icc 0 (horizon M c))) →
        1 ≤ ∑ t, ∫⁻ p, levelExcess (P t) (horizon M c) p ∧
          1 + ∑ t, volume (P t '' Set.Icc 0 (horizon M c)) ≤ M.k * ENNReal.ofReal (horizon M c) ∧
          ¬ ∀ t, MonotoneOn (P t) (Set.Icc 0 (horizon M c)) ∨
            AntitoneOn (P t) (Set.Icc 0 (horizon M c)) := by
  obtain ⟨Ts, Ds, Fs, ws, hall, -, hDL, hsub, hlim⟩ := theoremMStar_excess_nonuniform hns
    (Ms := fun _ => M) (fun _ => rfl) (fun _ => rfl)
    (tendsto_const_nhds.div_atTop (inputLength_tendsto hns)) hm hmL hfast
  exact ⟨Ts, Ds, Fs, ws, hall, hDL, hsub, hlim⟩

end Transpose.Tape.Impl
