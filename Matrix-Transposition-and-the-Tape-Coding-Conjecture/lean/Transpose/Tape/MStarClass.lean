import Transpose.Tape.MStarDiagram
import Transpose.Tape.CECode
import Transpose.Tape.PopularTrace

/-!
# Theorem M* for trace classes and adaptive machines

Theorem M\* for machines is the instance `runDiagram` of Theorem M\* for code-carrying diagrams
(`MStarDiagram.lean`). The code of a trace class (`code_bits_of_class`, on `k` tapes
`diagram_of_class`) carries the state and the head positions as
`s = ⌈log₂(q+1)⌉ + (k+1)⌈log₂(2T+1)⌉ = o(L)` extra bits per memory edge
(`stateBits_div_tendsto`), and the diagram's rescaled walks are the representative's rescaled
trajectories (`rescaled_runDiagram`). Correctness is needed only on the class (`ClassCorrect`).

* `cutIneq_of_class` (the class code satisfies the cut inequality) and `mstar_discrete_class` (the
  per-size inequality on a trace class, from `mstar_discrete_walk`);
* `inputLength_tendsto`, `stateBits_div_tendsto`;
* `theoremMStar_class_nonuniform`: **the one route from machines to codes**. Machines `M_i` (one per
  size, `k` tapes, `G` bits per cell, state bits `o(L)`) with trace classes of co-entropy `o(L)`,
  correct on the classes: the representatives' trajectories have convergent subsequences, and every
  subsequential limit is 1-Lipschitz and satisfies (★) (from `theoremMStar_diagram`);
  `theoremMStar_level_class` is its case of one machine and `φ = id`;
* `traceBits_le`: the popular trace costs `D ≤ C n b` bits (`C = traceConst M c`), so `D / L → 0`
  (`div_inputLength_tendsto`);
* representative independence: `curBlock_close_of_sameTrace`, `rescaledTrajOf_close` (members of a
  class are within `4/n` of each other) and `tendstoUniformlyOn_of_mem` (so the limits do not depend
  on the representatives).
-/

namespace Transpose.Tape.Impl

open Transpose MeasureTheory Filter Topology TSDiagram

open scoped ENNReal

/-! ### Rescaled trajectories of representatives -/

theorem workTraj_zero (M : TM) (w : List Bool) (t : Fin M.k) : workTraj M w 0 t = 0 := by
  simp [workTraj, run_zero, init]

/-! ### The per-size inequality on a trace class -/

/-- **The class code satisfies the cut inequality**, with `s = ⌈log₂(q+1)⌉ + (k+1)⌈log₂(2T+1)⌉`
bits per label change (the state and the head positions): `cutIneq_of_solves` for the code of the
class on the representative's diagram (`code_bits_of_class`). -/
theorem cutIneq_of_class {M : TM} {n T : ℕ} (hn : 1 ≤ n) {F : Set (List Bool)} {w₀ : List Bool}
    (hF : TraceClass M n (entryBits n) (slotLen M n) T F w₀) {D : ℕ}
    (hD : 2 ^ (n * n * entryBits n) ≤ 2 ^ D * F.ncard)
    (hcorr : ClassCorrect M n (entryBits n) T F) :
    CutIneq n (cellBits M) (slotLen M n) T D
      (Nat.clog 2 (M.q + 1) + (M.k + 1) * Nat.clog 2 (2 * T + 1)) (fun t τ => workTraj M w₀ τ t) := by
  obtain ⟨code, hv, hsol⟩ := code_bits_of_class hn le_rfl hF hcorr
  have hFm : F ⊆ matrixInputs n (entryBits n) := fun w hw => (hF.2 w hw).1
  exact cutIneq_of_solves (runDiagram M w₀ T) (cellBits_pos M) hn hv hsol
    (by rw [ncard_ofFn_preimage hFm]; exact hD)

open Classical in
/-- **The discrete inequality on a trace class**: `mstar_discrete_walk` for the representative's
walks, at the cost of `(M_c + 1) D` and the state and head positions at the label changes. -/
theorem mstar_discrete_class {M : TM} {n T : ℕ} {c θ η : ℝ} (hθ : 0 < θ)
    {F : Set (List Bool)} {w₀ : List Bool}
    (hF : TraceClass M n (entryBits n) (slotLen M n) T F w₀) {D : ℕ}
    (hD : 2 ^ (n * n * entryBits n) ≤ 2 ^ D * F.ncard)
    (hcorr : ClassCorrect M n (entryBits n) T F)
    (htime : (T : ℝ) ≤ c * inputLength n)
    {S : Set ℝ} {I : Finset (ℝ × ℝ)} (hSI : S = ⋃ x ∈ I, Set.Icc x.1 x.2) {β : ℝ → ℕ}
    {Z : Finset ℝ}
    (hβZ : ∀ u v, 0 ≤ u → u ≤ v → v ≤ horizon M c →
      (∀ x ∈ Set.Icc u v, x ∉ S ∧ x ∉ (Z : Set ℝ)) → β u = β v)
    (hclass : ∀ ℓ, volume {u | u ∈ Set.Icc 0 (horizon M c) ∧ u ∉ S ∧ β u = ℓ} ≤
      ENNReal.ofReal θ) :
    (n - 2 * (mstarBreaks Z I (horizon M c) θ).card) *
        (n - 2 * (⌊θ * n⌋₊ + 2 * (Z ∪ endpts I).card + 1)) * entryBits n ≤
      (2 * (mstarBreaks Z I (horizon M c) θ).card + 1) * D +
      2 * (mstarBreaks Z I (horizon M c) θ).card * ((M.k + 1) * Nat.clog 2 (2 * T + 1)) +
      2 * (mstarBreaks Z I (horizon M c) θ).card * Nat.clog 2 (M.q + 1) +
        (n * entryBits n + cellBits M) * (3 * M.k * (2 * (mstarBreaks Z I (horizon M c) θ).card) +
          ∑ t : Fin M.k, (2 * (mstarBreaks Z I (horizon M c) θ).card * (⌈η * n⌉₊ + 1) +
            2 * ((Finset.range (numSlots (slotLen M n) T)).filter
              (fun y : ℕ => (y : ℝ) / n ∈ S)).card +
            (longCross (pairRes (slotLen M n) (fun τ => workTraj M (w₀) τ t) T) S β n η
              (numSlots (slotLen M n) T)).card)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have h := mstar_discrete_walk (η := η) hn (one_le_slotLen M hn)
      (blockSize_mul_le (cellBits M) n)
      (fun t => unitSteps_workTraj M w₀ t) (numSlots_le_horizon hn htime) hθ
      (cutIneq_of_class hn hF hD hcorr) hSI hβZ hclass
    calc _ ≤ _ := h
      _ = _ := by ring

/-! ### The extra bits are `o(L)` -/

theorem entryBits_le_self {n : ℕ} (hn : 1 ≤ n) : entryBits n ≤ n := by
  unfold entryBits
  have := Nat.log2_le_self (n - 1)
  omega

theorem le_two_pow_entryBits (n : ℕ) : n ≤ 2 ^ entryBits n := by
  unfold entryBits
  have := Nat.lt_log2_self (n := n - 1)
  omega

/-- For `T ≤ c n² b`: `⌈log₂(2T+1)⌉ ≤ ⌈log₂(2⌈c⌉+1)⌉ + 3b` (using `b ≤ n ≤ 2^b`). -/
theorem clog_time_le {n T : ℕ} {c : ℝ} (hn : 1 ≤ n) (hT : (T : ℝ) ≤ c * inputLength n) :
    Nat.clog 2 (2 * T + 1) ≤ Nat.clog 2 (2 * ⌈c⌉₊ + 1) + 3 * entryBits n := by
  have hb1 : 1 ≤ entryBits n := by unfold entryBits; omega
  have hnb : n ≤ 2 ^ entryBits n := le_two_pow_entryBits n
  have hbb : entryBits n ≤ 2 ^ entryBits n := Nat.lt_two_pow_self.le
  have hL : (inputLength n : ℝ) = n * n * entryBits n := by rw [inputLength]; push_cast; ring
  have hTc : T ≤ ⌈c⌉₊ * (n * n * entryBits n) := by
    have h1 : (T : ℝ) ≤ ⌈c⌉₊ * (n * n * entryBits n) := by
      calc (T : ℝ) ≤ c * inputLength n := hT
        _ ≤ ⌈c⌉₊ * inputLength n := mul_le_mul_of_nonneg_right (Nat.le_ceil c) (by positivity)
        _ = _ := by rw [hL]
    exact_mod_cast h1
  have h1 : 1 ≤ n * n * entryBits n := Nat.one_le_iff_ne_zero.2 (by positivity)
  have h2 : 2 * T + 1 ≤ (2 * ⌈c⌉₊ + 1) * (n * n * entryBits n) := by nlinarith
  have h3 : n * n * entryBits n ≤ 2 ^ (3 * entryBits n) := by
    calc n * n * entryBits n ≤ 2 ^ entryBits n * 2 ^ entryBits n * 2 ^ entryBits n :=
          Nat.mul_le_mul (Nat.mul_le_mul hnb hnb) hbb
      _ = 2 ^ (3 * entryBits n) := by ring
  apply Nat.clog_le_of_le_pow
  calc 2 * T + 1 ≤ (2 * ⌈c⌉₊ + 1) * (n * n * entryBits n) := h2
    _ ≤ 2 ^ Nat.clog 2 (2 * ⌈c⌉₊ + 1) * 2 ^ (3 * entryBits n) :=
        Nat.mul_le_mul (Nat.le_pow_clog (by norm_num) _) h3
    _ = 2 ^ (Nat.clog 2 (2 * ⌈c⌉₊ + 1) + 3 * entryBits n) := by rw [pow_add]

/-- `L_i → ∞` when `n_i → ∞`. -/
theorem inputLength_tendsto {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop) :
    Tendsto (fun i => (inputLength (ns i) : ℝ)) atTop atTop := by
  have h : Tendsto (fun i => inputLength (ns i)) atTop atTop := by
    refine tendsto_atTop_mono (fun i => ?_) hns
    rcases Nat.eq_zero_or_pos (ns i) with h0 | hpos
    · rw [h0]; exact Nat.zero_le _
    · have hb : 1 ≤ entryBits (ns i) := by unfold entryBits; omega
      show ns i ≤ ns i * ns i * entryBits (ns i)
      nlinarith
  exact tendsto_natCast_atTop_atTop.comp h

/-- **The state and head-position bits are `o(L)`**: `(q_i + (k+1)⌈log₂(2T_i+1)⌉) / L_i → 0` when
`q_i / L_i → 0` and `T_i ≤ c L_i` (`⌈log₂(2T+1)⌉ ≤ (K + 3) b`, `clog_time_le`). -/
theorem stateBits_div_tendsto {k : ℕ} {c : ℝ} {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop)
    {Ts qs : ℕ → ℕ} (htime : ∀ᶠ i in atTop, (Ts i : ℝ) ≤ c * inputLength (ns i))
    (hq : Tendsto (fun i => (qs i : ℝ) / inputLength (ns i)) atTop (𝓝 0)) :
    Tendsto (fun i => ((qs i + (k + 1) * Nat.clog 2 (2 * Ts i + 1) : ℕ) : ℝ) / inputLength (ns i))
      atTop (𝓝 0) := by
  set K := Nat.clog 2 (2 * ⌈c⌉₊ + 1)
  have h2 := div_inputLength_tendsto (C := (k + 1) * (K + 3)) hns
    (Ds := fun i => (k + 1) * Nat.clog 2 (2 * Ts i + 1)) (by
      filter_upwards [htime, hns.eventually_ge_atTop 1] with i hti hn
      have hb1 : 1 ≤ entryBits (ns i) := by unfold entryBits; omega
      have hK : K ≤ K * entryBits (ns i) := Nat.le_mul_of_pos_right _ hb1
      calc (k + 1) * Nat.clog 2 (2 * Ts i + 1) ≤ (k + 1) * (K + 3 * entryBits (ns i)) :=
            Nat.mul_le_mul_left _ (clog_time_le hn hti)
        _ ≤ (k + 1) * ((K + 3) * entryBits (ns i)) :=
            Nat.mul_le_mul_left _ (by rw [Nat.add_mul]; exact Nat.add_le_add_right hK _)
        _ ≤ (k + 1) * ((K + 3) * entryBits (ns i)) * ns i := Nat.le_mul_of_pos_right _ hn
        _ = (k + 1) * (K + 3) * ns i * entryBits (ns i) := by ring)
  have h := hq.add h2
  rw [add_zero] at h
  exact h.congr fun i => by push_cast; rw [add_div]

/-! ### Theorem M* for trace classes -/

/-- **Theorem M\* for non-uniform machines on trace classes** (the one route from machines to
codes). At sizes `n_i → ∞`, let `M_i` be machines with `k` work tapes and `G` bits per cell, with
state bits `⌈log₂(q_i+1)⌉ = o(L_i)`, and let `F_i` be trace classes (halting time `T_i ≤ c L_i`,
representative `w_i`) with `2^{L_i} ≤ 2^{D_i} |F_i|`, `D_i / L_i → 0`, on which `M_i` is correct.
Then the representatives' rescaled trajectories have a uniformly convergent subsequence on
`[0, c₀]`, `c₀ = c G + 1`, and every subsequential limit is 1-Lipschitz and satisfies (★). The
proof applies `theoremMStar_diagram` to the class codes on `k`-tape diagrams
(`diagram_of_class`). -/
theorem theoremMStar_class_nonuniform {k G : ℕ} {c : ℝ} {ns : ℕ → ℕ}
    (hns : Tendsto ns atTop atTop) {Ms : ℕ → TM} (hk : ∀ i, (Ms i).k = k)
    (hG : ∀ i, cellBits (Ms i) = G)
    (hq : Tendsto (fun i => (Nat.clog 2 ((Ms i).q + 1) : ℝ) / inputLength (ns i)) atTop (𝓝 0))
    {Ts Ds : ℕ → ℕ} {Fs : ℕ → Set (List Bool)} {ws : ℕ → List Bool}
    (hF : ∀ᶠ i in atTop,
      TraceClass (Ms i) (ns i) (entryBits (ns i)) (slotLen (Ms i) (ns i)) (Ts i) (Fs i) (ws i))
    (hD : ∀ᶠ i in atTop, 2 ^ inputLength (ns i) ≤ 2 ^ Ds i * (Fs i).ncard)
    (hDL : Tendsto (fun i => (Ds i : ℝ) / inputLength (ns i)) atTop (𝓝 0))
    (hcorr : ∀ᶠ i in atTop, ClassCorrect (Ms i) (ns i) (entryBits (ns i)) (Ts i) (Fs i))
    (htime : ∀ᶠ i in atTop, (Ts i : ℝ) ≤ c * inputLength (ns i)) :
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
  have hG1 : 1 ≤ G := hG 0 ▸ cellBits_pos (Ms 0)
  -- the extra bits: state and head positions
  let ss : ℕ → ℕ := fun i => Nat.clog 2 ((Ms i).q + 1) + (k + 1) * Nat.clog 2 (2 * Ts i + 1)
  -- the class codes, on `k`-tape diagrams
  have key : ∀ i, ∃ (D : TSDiagram k) (code : NetCode), (1 ≤ ns i ∧
      TraceClass (Ms i) (ns i) (entryBits (ns i)) (slotLen (Ms i) (ns i)) (Ts i) (Fs i) (ws i) ∧
      ClassCorrect (Ms i) (ns i) (entryBits (ns i)) (Ts i) (Fs i)) →
      D.Valid (ns i * ns i * entryBits (ns i)) ∧ D.T = Ts i ∧
      D.Solves (ns i) G (D.blockCap (ns i) G
        (fun y => ∑ t, (pairRes (blockSize G (ns i)) (D.work t) D.T y).card) (ss i))
        {v | List.ofFn v ∈ Fs i} code ∧
      ∀ t, D.rescaled (ns i) G t =
        rescaledTrajOf (Ms i) (ns i) (ws i) (Fin.cast (hk i).symm t) := by
    intro i
    by_cases h : 1 ≤ ns i ∧
        TraceClass (Ms i) (ns i) (entryBits (ns i)) (slotLen (Ms i) (ns i)) (Ts i) (Fs i) (ws i) ∧
        ClassCorrect (Ms i) (ns i) (entryBits (ns i)) (Ts i) (Fs i)
    · obtain ⟨D, code, hv, hT, hsol, hres⟩ := diagram_of_class (hk i) (s := ss i) h.1
        (by show _ ≤ Nat.clog 2 ((Ms i).q + 1) + (k + 1) * Nat.clog 2 (2 * Ts i + 1); rw [hk i])
        h.2.1 h.2.2
      rw [hG i] at hsol hres
      exact ⟨D, code, fun _ => ⟨hv, hT, hsol, hres⟩⟩
    · exact ⟨⟨0, fun _ _ => 0, fun _ => 0, fun _ => 0⟩, ⟨fun _ _ _ => 0, fun _ _ _ => false⟩,
        fun h' => absurd h' h⟩
  choose Dg codes hDg using key
  have hev := (hns.eventually_ge_atTop 1).and (hF.and hcorr)
  have hsmall : Tendsto (fun i => ((Ds i : ℝ) + ss i) / inputLength (ns i)) atTop (𝓝 0) := by
    have h := hDL.add (stateBits_div_tendsto (k := k) (qs := fun i => Nat.clog 2 ((Ms i).q + 1))
      hns htime hq)
    rw [add_zero] at h
    exact h.congr fun i => (add_div _ _ _).symm
  obtain ⟨⟨φ₀, hφ₀, P₀, hP₀⟩, hlim⟩ := theoremMStar_diagram hG1 hns (c := c) (Ds := Dg)
    (Fs := fun i => {v | List.ofFn v ∈ Fs i}) (codes := codes) (ms := Ds) (ss := ss)
    (hev.mono fun i h => (hDg i h).1)
    (by filter_upwards [hev, htime] with i h hi; rw [(hDg i h).2.1]; exact hi)
    (by
      filter_upwards [hD, hF] with i hDi hFi
      rw [ncard_ofFn_preimage (fun w hw => (hFi.2 w hw).1)]
      exact hDi)
    (hev.mono fun i h => (hDg i h).2.2.1) hsmall
  -- the diagrams' rescaled walks are the machines' rescaled trajectories
  have heq : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ t, ∀ᶠ i in atTop,
      Set.EqOn ((Dg (φ i)).rescaled (ns (φ i)) G t)
        (rescaledTrajOf (Ms (φ i)) (ns (φ i)) (ws (φ i)) (Fin.cast (hk (φ i)).symm t))
        (Set.Icc 0 (c * G + 1)) := by
    intro φ hφ t
    filter_upwards [hφ.tendsto_atTop.eventually hev] with i hi u _
    rw [(hDg (φ i) hi).2.2.2 t]
  exact ⟨⟨φ₀, hφ₀, P₀, fun t => (hP₀ t).congr (heq φ₀ hφ₀ t)⟩, fun φ hφ P hP =>
    hlim φ hφ P fun t => (hP t).congr ((heq φ hφ t).mono fun i h => h.symm)⟩

/-- **Theorem M\*, level form, for trace classes**: the case of one machine and `φ = id` of
`theoremMStar_class_nonuniform`. -/
theorem theoremMStar_level_class {M : TM} {c : ℝ} {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop)
    {Ts Ds : ℕ → ℕ} {Fs : ℕ → Set (List Bool)} {ws : ℕ → List Bool}
    (hF : ∀ᶠ i in atTop,
      TraceClass M (ns i) (entryBits (ns i)) (slotLen M (ns i)) (Ts i) (Fs i) (ws i))
    (hD : ∀ᶠ i in atTop, 2 ^ inputLength (ns i) ≤ 2 ^ Ds i * (Fs i).ncard)
    (hDL : Tendsto (fun i => (Ds i : ℝ) / inputLength (ns i)) atTop (𝓝 0))
    (hcorr : ∀ᶠ i in atTop, ClassCorrect M (ns i) (entryBits (ns i)) (Ts i) (Fs i))
    (htime : ∀ᶠ i in atTop, (Ts i : ℝ) ≤ c * inputLength (ns i))
    {P : Fin M.k → ℝ → ℝ}
    (hconv : ∀ t, TendstoUniformlyOn (fun i => rescaledTrajOf M (ns i) (ws i) t) (P t) atTop
      (Set.Icc 0 (horizon M c)))
    {θ : ℝ≥0∞} {S : Set ℝ} (hS : FinUnionIcc S) {β : ℝ → ℕ}
    (hβ : PiecewiseConstOn β S (horizon M c))
    (hclass : ∀ ℓ, volume {u | u ∈ Set.Icc 0 (horizon M c) ∧ u ∉ S ∧ β u = ℓ} ≤ θ) :
    1 ≤ (∑ t, ∫⁻ p, levelCross (P t) S β (horizon M c) p) + 2 * θ +
      2 * M.k * volume (S ∩ Set.Icc 0 (horizon M c)) :=
  ((theoremMStar_class_nonuniform hns (Ms := fun _ => M) (fun _ => rfl) (fun _ => rfl)
    (tendsto_const_nhds.div_atTop (inputLength_tendsto hns)) hF hD hDL hcorr htime).2 id
    strictMono_id P hconv).2 θ S β hS hβ hclass

/-! ### The cost of the popular trace -/

/-- **The popular trace costs `O(n b)` bits**: for `T_max ≤ c L` and slot length `slotLen M n`,
`⌈log₂ traceCount⌉ ≤ C n b`. -/
theorem traceBits_le {M : TM} {c : ℝ} {n Tmax : ℕ} (hn : 1 ≤ n)
    (hT : (Tmax : ℝ) ≤ c * inputLength n) :
    Nat.clog 2 (traceCount M.k n (numSlots (slotLen M n) Tmax) Tmax) ≤
      traceConst M c * n * entryBits n := by
  set b := entryBits n with hb
  set N := numSlots (slotLen M n) Tmax with hNdef
  set C₀ := ⌈horizon M c⌉₊ with hC₀
  set Cc := Nat.clog 2 (2 * ⌈c⌉₊ + 1) with hCc
  have hb1 : 1 ≤ b := by rw [hb]; unfold entryBits; omega
  have hnb : n ≤ 2 ^ b := le_two_pow_entryBits n
  -- the halting-time factor
  set A := Nat.clog 2 (2 * Tmax + 1) with hAdef
  have hA : A ≤ Cc + 3 * b := clog_time_le hn hT
  have hTA : Tmax + 1 ≤ 2 ^ A := le_trans (by omega) (Nat.le_pow_clog (by norm_num) _)
  -- the number of slots
  have hNr : (N : ℝ) ≤ horizon M c * n := numSlots_le_horizon hn hT
  have hN : N ≤ C₀ * n := by
    have : (N : ℝ) ≤ C₀ * n :=
      le_trans hNr (mul_le_mul_of_nonneg_right (Nat.le_ceil _) (by positivity))
    exact_mod_cast this
  -- the block range
  set B₁ := Nat.clog 2 (2 * N + 2) with hB₁def
  have hB₁ : B₁ ≤ Nat.clog 2 (2 * C₀ + 2) + b := by
    apply Nat.clog_le_of_le_pow
    calc 2 * N + 2 ≤ (2 * C₀ + 2) * n := by nlinarith
      _ ≤ 2 ^ Nat.clog 2 (2 * C₀ + 2) * 2 ^ b :=
          Nat.mul_le_mul (Nat.le_pow_clog (by norm_num) _) hnb
      _ = _ := by rw [pow_add]
  have hNB : 2 * N + 2 ≤ 2 ^ B₁ := Nat.le_pow_clog (by norm_num) _
  have hn1b : n + 1 ≤ 2 ^ (b + 1) := by
    rw [pow_succ]
    have : 1 ≤ 2 ^ b := Nat.one_le_two_pow
    omega
  -- `traceCount ≤ 2^E`
  have hcount : traceCount M.k n N Tmax ≤
      2 ^ (A + (N + 1) * (3 * M.k * B₁ + 2 * (b + 1) + A)) := by
    unfold traceCount
    calc (Tmax + 1) * ((2 * N + 2) ^ (3 * M.k) * (n + 1) ^ 2 * (Tmax + 1)) ^ (N + 1)
        ≤ 2 ^ A * ((2 ^ B₁) ^ (3 * M.k) * (2 ^ (b + 1)) ^ 2 * 2 ^ A) ^ (N + 1) := by
          apply Nat.mul_le_mul hTA
          apply Nat.pow_le_pow_left
          exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_left hNB _)
            (Nat.pow_le_pow_left hn1b _)) hTA
      _ = 2 ^ (A + (N + 1) * (3 * M.k * B₁ + 2 * (b + 1) + A)) := by
          rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add, ← pow_mul, ← pow_add]
          congr 1
          ring
  have hD := Nat.clog_le_of_le_pow hcount
  -- `E ≤ C n b`
  set K := 3 * M.k * Nat.clog 2 (2 * C₀ + 2) + 3 * M.k + 7 + Cc with hK
  have hX : 3 * M.k * B₁ + 2 * (b + 1) + A ≤ K * b := by
    have e1 : 3 * M.k * B₁ ≤ 3 * M.k * Nat.clog 2 (2 * C₀ + 2) + 3 * M.k * b := by
      rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ hB₁
    have e2 : 3 * M.k * Nat.clog 2 (2 * C₀ + 2) ≤ 3 * M.k * Nat.clog 2 (2 * C₀ + 2) * b :=
      Nat.le_mul_of_pos_right _ hb1
    have e3 : Cc ≤ Cc * b := Nat.le_mul_of_pos_right _ hb1
    have e4 : K * b = 3 * M.k * Nat.clog 2 (2 * C₀ + 2) * b + 3 * M.k * b + 7 * b + Cc * b := by
      rw [hK]; ring
    omega
  have hN1 : N + 1 ≤ (C₀ + 1) * n := by nlinarith
  have hA' : A ≤ (Cc + 3) * n * b := by
    have : Cc + 3 * b ≤ (Cc + 3) * b := by nlinarith
    have h2 : (Cc + 3) * b ≤ (Cc + 3) * n * b := by
      rw [Nat.mul_assoc]
      exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by omega))
    omega
  calc Nat.clog 2 (traceCount M.k n N Tmax)
      ≤ A + (N + 1) * (3 * M.k * B₁ + 2 * (b + 1) + A) := hD
    _ ≤ (Cc + 3) * n * b + (C₀ + 1) * n * (K * b) :=
        Nat.add_le_add hA' (Nat.mul_le_mul hN1 hX)
    _ = traceConst M c * n * b := by
        unfold traceConst
        rw [← hC₀, ← hCc, hK]
        ring

/-! ### Representative independence -/

/-- Two runs with the same trace and the same halting time have work-head blocks within `2` of each
other before halting, and within `4` afterwards. -/
theorem curBlock_close_of_sameTrace {M : TM} {n b r T : ℕ} (hr : 1 ≤ r) {w w' : List Bool}
    (hT : HaltsAt M w T) (hT' : HaltsAt M w' T) (htr : SameTrace M n b r T w w')
    (t : Fin M.k) (τ : ℕ) :
    |curBlock r (fun σ => workTraj M w σ t) τ - curBlock r (fun σ => workTraj M w' σ t) τ| ≤ 4 := by
  have hh := unitSteps_workTraj M w t
  have hh' := unitSteps_workTraj M w' t
  have hR := pairRes_eq_of_sameTrace hr htr t
  -- before halting: both blocks are resident at the slot, which has diameter `≤ 2`
  have key : ∀ σ < T, |curBlock r (fun σ => workTraj M w σ t) σ -
      curBlock r (fun σ => workTraj M w' σ t) σ| ≤ 2 := by
    intro σ hσ
    have h1 := cur_mem_pairRes (h := fun σ => workTraj M w σ t) hr hσ
    have h2 := cur_mem_pairRes (h := fun σ => workTraj M w' σ t) hr hσ
    rw [hR] at h1
    have s1 := pairRes_subset hh' hr T (σ / r) h1
    have s2 := pairRes_subset hh' hr T (σ / r) h2
    simp only [Finset.mem_insert, Finset.mem_singleton] at s1 s2
    rw [abs_le]
    constructor <;> omega
  rcases lt_or_ge τ T with hτ | hτ
  · exact le_trans (key τ hτ) (by norm_num)
  · -- after halting both runs are frozen at time `T`
    have e1 : curBlock r (fun σ => workTraj M w σ t) τ =
        curBlock r (fun σ => workTraj M w σ t) T := by
      simp only [curBlock, workTraj, run_of_le_of_none hT.2 hτ]
    have e2 : curBlock r (fun σ => workTraj M w' σ t) τ =
        curBlock r (fun σ => workTraj M w' σ t) T := by
      simp only [curBlock, workTraj, run_of_le_of_none hT'.2 hτ]
    rw [e1, e2]
    rcases Nat.eq_zero_or_pos T with h0 | hpos
    · subst h0; simp [curBlock, workTraj, run_zero, init]
    · obtain ⟨T₀, rfl⟩ : ∃ T₀, T = T₀ + 1 := ⟨T - 1, by omega⟩
      have k0 := key T₀ (by omega)
      have a1 : |curBlock r (fun σ => workTraj M w σ t) (T₀ + 1) -
          curBlock r (fun σ => workTraj M w σ t) T₀| ≤ 1 :=
        blockOf_close hr (le_trans (hh T₀) (by exact_mod_cast hr))
      have a2 : |curBlock r (fun σ => workTraj M w' σ t) (T₀ + 1) -
          curBlock r (fun σ => workTraj M w' σ t) T₀| ≤ 1 :=
        blockOf_close hr (le_trans (hh' T₀) (by exact_mod_cast hr))
      rw [abs_le] at k0 a1 a2 ⊢
      constructor <;> linarith [k0.1, k0.2, a1.1, a1.2, a2.1, a2.2]

/-- **Representative independence.** Members of one trace class have rescaled trajectories within
`4/n` of each other. -/
theorem rescaledTrajOf_close {M : TM} {n T : ℕ} (hn : 1 ≤ n) {F : Set (List Bool)}
    {w₀ w : List Bool} (hF : TraceClass M n (entryBits n) (slotLen M n) T F w₀) (hw : w ∈ F)
    (t : Fin M.k) (u : ℝ) :
    |rescaledTrajOf M n w t u - rescaledTrajOf M n w₀ t u| ≤ 4 / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h := curBlock_close_of_sameTrace (one_le_slotLen M hn) (hF.2 w hw).2.1
    (hF.2 w₀ hF.1).2.1 (hF.2 w hw).2.2 t (⌊u * n⌋₊ * slotLen M n)
  unfold rescaledTrajOf
  rw [← sub_div, abs_div, abs_of_pos hn']
  apply div_le_div_of_nonneg_right _ hn'.le
  exact_mod_cast h

/-- **The limits do not depend on the representatives:** if the representatives' rescaled
trajectories converge uniformly to `P`, so do those of any members. -/
theorem tendstoUniformlyOn_of_mem {M : TM} {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop)
    {Ts : ℕ → ℕ} {Fs : ℕ → Set (List Bool)} {ws ws' : ℕ → List Bool}
    (hF : ∀ᶠ i in atTop,
      TraceClass M (ns i) (entryBits (ns i)) (slotLen M (ns i)) (Ts i) (Fs i) (ws i))
    (hmem : ∀ᶠ i in atTop, ws' i ∈ Fs i) {t : Fin M.k} {P : ℝ → ℝ} {s : Set ℝ}
    (hconv : TendstoUniformlyOn (fun i => rescaledTrajOf M (ns i) (ws i) t) P atTop s) :
    TendstoUniformlyOn (fun i => rescaledTrajOf M (ns i) (ws' i) t) P atTop s := by
  rw [Metric.tendstoUniformlyOn_iff] at hconv ⊢
  intro ε hε
  have h4 : ∀ᶠ i in atTop, (4 : ℝ) / ns i < ε / 2 := by
    have := (tendsto_const_div_atTop_nhds_zero_nat (4 : ℝ)).comp hns
    exact this.eventually (gt_mem_nhds (by positivity))
  filter_upwards [hconv (ε / 2) (by positivity), hF, hmem, h4, hns.eventually_ge_atTop 1]
    with i hi hFi hwi h4i hn1 u hu
  have hc := rescaledTrajOf_close hn1 hFi hwi t u
  have := hi u hu
  rw [Real.dist_eq] at this ⊢
  calc |P u - rescaledTrajOf M (ns i) (ws' i) t u|
      ≤ |P u - rescaledTrajOf M (ns i) (ws i) t u| +
        |rescaledTrajOf M (ns i) (ws' i) t u - rescaledTrajOf M (ns i) (ws i) t u| := by
        have := abs_sub_le (P u) (rescaledTrajOf M (ns i) (ws i) t u)
          (rescaledTrajOf M (ns i) (ws' i) t u)
        rw [abs_sub_comm (rescaledTrajOf M (ns i) (ws i) t u)] at this
        exact this
    _ < ε / 2 + ε / 2 := by
        have : (4 : ℝ) / ns i < ε / 2 := h4i
        linarith
    _ = ε := by ring

end Transpose.Tape.Impl
