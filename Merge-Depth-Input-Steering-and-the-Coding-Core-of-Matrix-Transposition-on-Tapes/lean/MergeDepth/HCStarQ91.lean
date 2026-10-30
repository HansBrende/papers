import MergeDepth.BallsQ91
import MergeDepth.FieldMachine

/-!
# Corollary HC* at all sizes, given binary [Q9.1]

`cor_HCstar_pruning` (Corollary HC* at one size for the field DAG of a pruning of an oblivious
transposer) assumes the conclusion of Lemma 3.14(b) at the size in question (`hballs`). Here that
hypothesis is discharged by `ball_rate_binary`, for the head walks of the oblivious schedule:

* `traceWalks τ₀`: the input head `τ₀.input`, the append count `appendCount τ₀` (the number of
  appends before each time) and the work heads `τ₀.work`. `appendCount_isWalk`, and
  `appendCount_appendTime`: the count before the `r`-th append time is `r`.
* `trace_ball_data`: the walk hypotheses of Lemma 3.14 hold for the head walks of any trace that
  appends at least `L` bits before `T` (no obliviousness or correctness needed);
  `ball_paired_packing_trace`, `ball_self_demands_trace`: Lemma 3.14(a) for traces, and
  `ball_rate_trace`: Lemma 3.14(b) for traces as stated (all alphabets, from [Q9.1]), without walk
  hypotheses.
* `hballs_of_obliviousTransposer`: Lemma 3.14(b) in the form of `hballs`, for all `d ≥ d₁`, every
  width `b ≥ 1` and every oblivious transposer with `T ≤ C (L + 1)`.
* `cor_HCstar_uniform`: **Corollary HC\*** for field DAGs of prunings: given binary [Q9.1], for
  `V`, `β`, `C`, `D`, `s`, `τ` and `ε, η` with `γ = 1/2 - ε - η > 0` and `4 β (k + 2) k C ≤ γ τ`
  there is `d₀` such that at no `d ≥ d₀` (and no width `b ≥ 1`) does an oblivious transposer with
  `T ≤ C (L + 1)` have a pruning, a cold genie at `(V, ε)` of depth `D` and a lineage assignment
  with merge depth at most `s` outside at most `η L` output positions.
* `cor_HCstar_uniform_frozen`: the same for a machine oblivious at length `L` in the frozen model
  (`ObliviousOn`) that transposes within `c (L + 1)` steps (`TransposesAtWidth`, real `c > 0`).
* `cor_HCstar_uniform_empty`: the last sentence of Corollary HC* (empty genie).

The two encodings of the transposition permutation, `Transpose.Tape.tpos` (frozen model, used by
`tposOf`) and `MergeDepth.tpos` (transport lemmas), agree: `tape_tpos_eq`.
-/

namespace MergeDepth

open Finset Filter BoundedNesting DirectedRecovery MotionDepthCodes Transpose

set_option autoImplicit false

/-- The two encodings of the transposition permutation agree. -/
theorem tape_tpos_eq (d b p : ℕ) : Transpose.Tape.tpos d b p = MergeDepth.tpos d b p := by
  unfold Transpose.Tape.tpos MergeDepth.tpos
  rw [Nat.mod_mul_left_div_self, Nat.div_div_eq_div_mul, Nat.mul_comm b d]

/-! ### The append count of a trace -/

section AppendCount

variable {k : ℕ}

/-- The number of appends of `τ` before time `t`. -/
def appendCount (τ : Trace k) (t : ℕ) : ℤ := ((appendList τ t).length : ℤ)

theorem appendList_succ (τ : Trace k) (t : ℕ) :
    appendList τ (t + 1) = appendList τ t ++ (if τ.appends t then [t] else []) := by
  unfold appendList
  rw [List.range_succ, List.filter_append]
  congr 1
  rcases h : τ.appends t <;> simp [List.filter, h]

theorem appendCount_isWalk (τ : Trace k) : IsWalk (appendCount τ) := by
  intro t
  simp only [appendCount, appendList_succ, List.length_append]
  split_ifs <;> simp

/-- The appends before `t ≤ T` are the appends before `T` that precede `t`. -/
theorem appendList_eq_filter_lt (τ : Trace k) {t T : ℕ} (h : t ≤ T) :
    appendList τ t = (appendList τ T).filter fun x => decide (x < t) := by
  induction T, h using Nat.le_induction with
  | base =>
    symm
    rw [List.filter_eq_self]
    intro x hx
    simp only [appendList, List.mem_filter, List.mem_range] at hx
    simpa using hx.1
  | succ T hT ih =>
    rw [appendList_succ, List.filter_append, ← ih]
    split_ifs with hT'
    · simp only [List.filter_cons, List.filter_nil]
      have : ¬ T < t := by omega
      simp [this]
    · simp

/-- In a strictly increasing list, `r` elements precede the `r`-th one. -/
theorem length_filter_lt_getElem :
    ∀ {l : List ℕ}, l.Pairwise (· < ·) → ∀ {r : ℕ} (hr : r < l.length),
      (l.filter fun x => decide (x < l[r])).length = r
  | [], _, r, hr => by simp at hr
  | a :: l, hl, r, hr => by
    obtain ⟨ha, hl'⟩ := List.pairwise_cons.mp hl
    cases r with
    | zero =>
      simp only [List.getElem_cons_zero, List.filter_cons, lt_self_iff_false, decide_false,
        Bool.false_eq_true, ↓reduceIte, List.length_eq_zero_iff]
      rw [List.filter_eq_nil_iff]
      intro x hx
      simpa using (ha x hx).le
    | succ r =>
      have hr' : r < l.length := by simpa using hr
      have hlt : a < l[r] := ha _ (List.getElem_mem hr')
      simp only [List.getElem_cons_succ, List.filter_cons, hlt, decide_true, ↓reduceIte,
        List.length_cons]
      rw [length_filter_lt_getElem hl' hr']

/-- **The append count at the `r`-th append time is `r`.** -/
theorem appendCount_appendTime (τ : Trace k) (T : ℕ) {r : ℕ} (hr : r < (appendList τ T).length) :
    appendCount τ (appendTime τ T r) = r := by
  have hlt := appendTime_lt τ T hr
  unfold appendCount
  rw [appendList_eq_filter_lt τ hlt.le, appendTime_eq_getElem τ T hr,
    length_filter_lt_getElem (l := appendList τ T) (List.pairwise_lt_range.filter _) hr]

end AppendCount

/-! ### The head walks of an oblivious schedule -/

/-- The head walks of a trace: the input head, the append count and the work heads. -/
def traceWalks {k : ℕ} (τ₀ : Trace k) : Tp k → ℕ → ℤ
  | none => τ₀.input
  | some none => appendCount τ₀
  | some (some j) => τ₀.work j

theorem traceWalks_isWalk {k : ℕ} (τ₀ : Trace k) : ∀ c, IsWalk (traceWalks τ₀ c)
  | none => fun t => τ₀.abs_input_succ_sub_le t
  | some none => appendCount_isWalk τ₀
  | some (some j) => τ₀.work_isWalk j

/-- **The walk facts of a trace.** For a trace `τ₀` (of any machine with `k` work tapes) that
appends at least `L = d² b` bits before `T`, the head walks of the trace (`traceWalks`) satisfy the
hypotheses of Lemma 3.14 on the walks of the machine: the input head reads the position under it
(`readPos`), output position `tpos q` is appended at a step `< T` at which the append count is
`tpos q`, and the balls around the output steps are those of the work walks. Neither obliviousness
nor correctness is needed. -/
theorem trace_ball_data {k d b : ℕ} (hb : 1 ≤ b) {τ₀ : Trace k} {T : ℕ}
    (happ : d * d * b ≤ (appendList τ₀ T).length) :
    (∀ u j, readPos τ₀ (d * d * b) u = some j → traceWalks τ₀ none u = j) ∧
    (∀ q : Fin (d * d * b), appendTime τ₀ T (tpos d b q) < T ∧
      traceWalks τ₀ (some none) (appendTime τ₀ T (tpos d b q)) = tpos d b q) ∧
    ∀ (r : ℕ) (q : Fin (d * d * b)),
      stepBall τ₀.work T (readPos τ₀ (d * d * b)) r (appendTime τ₀ T (tposOf d b q)) =
        stepBall (fun j => traceWalks τ₀ (some (some j))) T (readPos τ₀ (d * d * b)) r
          (appendTime τ₀ T (tpos d b q)) := by
  refine ⟨fun u j h => readPos_eq_some_iff.mp h, fun q => ?_, fun r q => ?_⟩
  · have hr : tpos d b q < (appendList τ₀ T).length :=
      lt_of_lt_of_le (tpos_lt (by omega) q.2) happ
    exact ⟨appendTime_lt τ₀ T hr, appendCount_appendTime τ₀ T hr⟩
  · have e : ((tposOf d b q : Fin (d * d * b)) : ℕ) = tpos d b q := tape_tpos_eq d b q
    rw [e]
    rfl

open Classical in
/-- **Lemma 3.14(a) for a trace** (in particular, for oblivious machines in the frozen model):
Theorem 3.3 of the fifth paper for relations inside the balls `B^{D'}` around the output steps of a
trace `τ₀` that appends at least `L` bits before `T ≤ c (L + 1)`, with the walk hypotheses of
`ball_paired_packing` discharged. -/
theorem ball_paired_packing_trace {k d b : ℕ} (hd : 2 ≤ d) (hb : 1 ≤ b) {τ₀ : Trace k}
    {T D' : ℕ} (happ : d * d * b ≤ (appendList τ₀ T).length) {c : ℝ} (hc : 0 ≤ c)
    (hT : (T : ℝ) ≤ c * (d * d * b + 1)) (N : Fin (d * d * b) → Finset (Fin (d * d * b)))
    (hN : ∀ q, N q ⊆ stepBall τ₀.work T (readPos τ₀ (d * d * b)) D'
      (appendTime τ₀ T (tposOf d b q)))
    (Q : Finset (Fin (d * d * b))) (r Δ : ℕ)
    (hdeg : ∀ v, (pairedIncidenceGraph (inducedNeighborhood N Q)).degree v ≤ Δ) :
    ((shortPairedCoordinates (inducedNeighborhood N Q) r).card : ℝ) ≤
      pathPackingConstant r Δ (fun s => 2 * s * c * (∑ h ∈ range (D' + 1), (k + 1) ^ h : ℕ) *
        (k + 2 : ℕ) * ((k + 2 : ℕ) + 1) + 3) * (((d : ℝ) ^ 2 * b) / Real.logb 2 d) := by
  obtain ⟨hrd, htout, hball⟩ := trace_ball_data hb happ
  exact ball_paired_packing hd hb (traceWalks_isWalk τ₀) (readPos τ₀ (d * d * b)) hrd
    (appendTime τ₀ T) htout N (fun q => hball D' q ▸ hN q) hc hT Q r Δ hdeg

open Classical in
/-- **Lemma 3.14(a), self-demands, for a trace**: at most `(2 c K (k + 2)(k + 3) + 3) L/log₂ d`
positions `p` satisfy `p ∈ N(p)`. -/
theorem ball_self_demands_trace {k d b : ℕ} (hd : 2 ≤ d) (hb : 1 ≤ b) {τ₀ : Trace k}
    {T D' : ℕ} (happ : d * d * b ≤ (appendList τ₀ T).length) {c : ℝ} (hc : 0 ≤ c)
    (hT : (T : ℝ) ≤ c * (d * d * b + 1)) (N : Fin (d * d * b) → Finset (Fin (d * d * b)))
    (hN : ∀ q, N q ⊆ stepBall τ₀.work T (readPos τ₀ (d * d * b)) D'
      (appendTime τ₀ T (tposOf d b q))) :
    ((selfDemandCoordinates N).card : ℝ) ≤
      (2 * c * (∑ h ∈ range (D' + 1), (k + 1) ^ h : ℕ) * (k + 2 : ℕ) * ((k + 2 : ℕ) + 1) + 3) *
        ((d : ℝ) ^ 2 * b) / Real.logb 2 d := by
  obtain ⟨hrd, htout, hball⟩ := trace_ball_data hb happ
  exact ball_self_demands hd hb (traceWalks_isWalk τ₀) (readPos τ₀ (d * d * b)) hrd
    (appendTime τ₀ T) htout N (fun q => hball D' q ▸ hN q) hc hT

open Classical in
/-- **Lemma 3.14(b) for a trace, as stated (every finite alphabet), given [Q9.1].** For `k`, `D'`,
`c ≥ 0` and `δ > 0` there is `d₁`, depending only on `k`, `D'`, `c` and `δ`, such that for
`d ≥ d₁`, every width `b ≥ 1` and every trace `τ₀` with `k` work heads that appends at least `L`
bits before `T ≤ c (L + 1)`, every storage code over a finite alphabet `𝒜` with `|𝒜| ≥ 2` for a
relation inside the balls of radius `D'` around the output steps has `log_{|𝒜|} |𝒞| ≤ (1/2 + δ) L`. -/
theorem ball_rate_trace (hQ : Q91) (k D' : ℕ) {c δ : ℝ} (hc : 0 ≤ c) (hδ : 0 < δ) :
    ∃ d₁ : ℕ, ∀ d ≥ d₁, ∀ b : ℕ, 1 ≤ b → ∀ (τ₀ : Trace k) (T : ℕ),
      d * d * b ≤ (appendList τ₀ T).length → (T : ℝ) ≤ c * (d * d * b + 1) →
      ∀ N : Fin (d * d * b) → Finset (Fin (d * d * b)),
        (∀ q, N q ⊆ stepBall τ₀.work T (readPos τ₀ (d * d * b)) D'
          (appendTime τ₀ T (tposOf d b q))) →
      ∀ (A : Type) [Fintype A], 2 ≤ Fintype.card A → ∀ C : Finset (Fin (d * d * b) → A),
        IsStorageCode N C → Real.logb (Fintype.card A) C.card ≤ (1 / 2 + δ) * (d * d * b : ℕ) := by
  obtain ⟨d₁, hd₁⟩ := ball_rate hQ k D' hc hδ
  refine ⟨d₁, fun d hd b hb τ₀ T happ hT N hN A _ hA C hC => ?_⟩
  obtain ⟨hrd, htout, hball⟩ := trace_ball_data hb happ
  exact hd₁ d hd b hb (traceWalks τ₀) (traceWalks_isWalk τ₀) T (readPos τ₀ (d * d * b)) hrd
    (appendTime τ₀ T) htout hT N (fun q => hball D' q ▸ hN q) A hA C hC

open Classical in
/-- **Lemma 3.14(b) in the form of the hypothesis `hballs` of `cor_HCstar_pruning`.** Given binary
[Q9.1], for `k`, a radius `r`, `C` and `δ > 0` there is `d₁` such that for `d ≥ d₁`, every width
`b ≥ 1` and every oblivious transposer `M` with `k` work tapes and `T ≤ C (L + 1)`, every binary
storage code for a relation inside the balls of radius `r` around the output steps has at most
`2^{(1/2 + δ) L}` words. -/
theorem hballs_of_obliviousTransposer (hQ : Q91Binary) (k r C : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ d₁ : ℕ, ∀ d ≥ d₁, ∀ b, 1 ≤ b → ∀ (M : TM), M.k = k → ∀ (τ₀ : Trace M.k) (T : ℕ),
      ObliviousTransposer M d b τ₀ T → T ≤ C * (d * d * b + 1) →
      ∀ N : Fin (d * d * b) → Finset (Fin (d * d * b)),
        (∀ q, N q ⊆ stepBall τ₀.work T (readPos τ₀ (d * d * b)) r
          (appendTime τ₀ T (tposOf d b q))) →
      ∀ Cd : Finset (Fin (d * d * b) → Bool), IsStorageCode N Cd →
        (Cd.card : ℝ) ≤ (2 : ℝ) ^ ((1 / 2 + δ) * (d * d * b : ℕ)) := by
  obtain ⟨d₁, hd₁⟩ := ball_rate_binary hQ k r (c := C) (Nat.cast_nonneg C) hδ
  refine ⟨d₁, fun d hd b hb M hk τ₀ T hM hT N hN Cd hCd => ?_⟩
  subst hk
  obtain ⟨hrd, htout, hball⟩ := trace_ball_data hb hM.appends
  have hT' : (T : ℝ) ≤ (C : ℝ) * (d * d * b + 1) := by exact_mod_cast hT
  have hlog := hd₁ d hd b hb (traceWalks τ₀) (traceWalks_isWalk τ₀) T (readPos τ₀ (d * d * b)) hrd
    (appendTime τ₀ T) htout hT' N (fun q => hball r q ▸ hN q) Cd hCd
  rcases Nat.eq_zero_or_pos Cd.card with h0 | hpos
  · rw [h0, Nat.cast_zero]
    positivity
  · exact (Real.logb_le_iff_le_rpow (by norm_num) (by exact_mod_cast hpos)).mp hlog

/-! ### Corollary HC* -/

open Classical in
/-- **Corollary HC\*, given binary [Q9.1], for field DAGs of prunings.** Let `V, β, C, D, s, τ` be
integers and `ε, η` reals with `γ = 1/2 - ε - η > 0`, `τ ≥ 1` and `4 β (k + 2) k C ≤ γ τ`. There is
`d₀` such that at no `d ≥ d₀` and no width `b ≥ 1` is there an oblivious transposer `M` with `k`
work tapes along a trace `τ₀` before `T ≤ C (L + 1)`, `β ≥ β(M)`, a pruning of its field DAG, a
cold genie `ΓF` at `(V, ε)` with depth `D`, a lineage assignment for it, and a set `X` of at most
`η L` output positions outside which every `ΓF`-free path from an output node has at most `s` deep
merges. The threshold depends only on `k`, `V`, `β`, `C`, `D`, `s`, `τ`, `ε` and `η`. -/
theorem cor_HCstar_uniform (hQ : Q91Binary) (k : ℕ) {V β C D s τ : ℕ} {ε η : ℝ}
    (hγ : 0 < 1 / 2 - ε - η) (hτ : 1 ≤ τ)
    (hτbig : 4 * β * (k + 2) * k * C ≤ (1 / 2 - ε - η) * τ) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ b, 1 ≤ b → ∀ (M : TM), M.k = k → ∀ (τ₀ : Trace M.k) (T : ℕ),
      ObliviousTransposer M d b τ₀ T → ∀ Pr : Pruning M (d * d * b) τ₀ T, valueWidth M ≤ β →
      T ≤ C * (d * d * b + 1) → ∀ ΓF : Finset ℕ,
      IsColdGenie (L := d * d * b) τ₀.work T V β ε D ΓF → ∀ lin : Forest,
      (∀ u v v' π, lin.nxt u = some v → v' ≠ v → (u :: v' :: π) ∈ Pr.toFunDag.net.paths u →
        LinNet.GFree (ΓF.biUnion (fieldNodesAt M.k)) (u :: v' :: π) →
        rCount (fun u v => DeepStep τ₀.work T V (u / (M.k + 2)) (v / (M.k + 2)))
          (u :: v' :: π) = 0) →
      ∀ X : Finset (Fin (d * d * b)), (X.card : ℝ) ≤ η * (d * d * b : ℕ) →
      ¬ (∀ ℓ ∉ X, ∀ π, π ∈ Pr.toFunDag.net.paths (outputNodeOf τ₀ T ℓ) →
        LinNet.GFree (ΓF.biUnion (fieldNodesAt M.k)) π →
        dm lin (fun u v => DeepStep τ₀.work T V (u / (M.k + 2)) (v / (M.k + 2))) false π ≤ s) := by
  obtain ⟨d₁, hd₁⟩ := hballs_of_obliviousTransposer hQ k ((s + 1) * τ * D) C
    (by linarith : 0 < (1 / 2 - ε - η) / 4)
  refine ⟨max d₁ 1, fun d hd b hb M hk τ₀ T hM Pr hβ hT ΓF hcold lin hside X hX hround => ?_⟩
  subst hk
  have hL : 1 ≤ d * d * b := Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) hb
  exact cor_HCstar_pruning hM Pr hβ hT hL hcold hγ lin hside hτ hτbig s X hX hround
    (hd₁ d (le_of_max_le_left hd) b hb M rfl τ₀ T hM hT)

open Classical in
/-- **Corollary HC\* in the frozen model, as in Theorem L(c).** Given binary [Q9.1], for a machine
`M`, `c > 0`, `β ≥ β(M)`, `V`, `D`, `s` and `ε, η` with `ε + η < 1/2`, there is `d₀` such that for
`d ≥ d₀` and every width `b ≥ 1`: if `M` transposes `d × d` matrices with `b`-bit entries within
`c (L + 1)` steps and is oblivious at length `L` with halting time `T`, then for every pruning of its
field DAG, every cold genie at `(V, ε)` with depth `D` and every lineage assignment for it, more
than `η L` output positions `ℓ` have a `ΓF`-free path from their output node with more than `s`
deep merges. -/
theorem cor_HCstar_uniform_frozen (hQ : Q91Binary) (M : TM) {c : ℝ} (hc : 0 < c) {V β D s : ℕ}
    (hβ : valueWidth M ≤ β) {ε η : ℝ} (hγ : 0 < 1 / 2 - ε - η) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ b, 1 ≤ b → TransposesAtWidth M d b c → ∀ T : ℕ,
      Transpose.Tape.ObliviousOn M (Transpose.Tape.inputsOfLength (d * d * b)) T →
      ∀ (w₀ : Fin (d * d * b) → Bool)
      (Pr : Pruning M (d * d * b) (trace M (List.ofFn w₀)) T) (ΓF : Finset ℕ),
      IsColdGenie (L := d * d * b) (trace M (List.ofFn w₀)).work T V β ε D ΓF →
      ∀ lin : Forest,
      (∀ u v v' π, lin.nxt u = some v → v' ≠ v → (u :: v' :: π) ∈ Pr.toFunDag.net.paths u →
        LinNet.GFree (ΓF.biUnion (fieldNodesAt M.k)) (u :: v' :: π) →
        rCount (fun u v => DeepStep (trace M (List.ofFn w₀)).work T V (u / (M.k + 2))
          (v / (M.k + 2))) (u :: v' :: π) = 0) →
      η * (d * d * b : ℕ) < ((univ.filter fun ℓ : Fin (d * d * b) =>
        ∃ π ∈ Pr.toFunDag.net.paths (outputNodeOf (trace M (List.ofFn w₀)) T ℓ),
          LinNet.GFree (ΓF.biUnion (fieldNodesAt M.k)) π ∧
          s < dm lin (fun u v => DeepStep (trace M (List.ofFn w₀)).work T V (u / (M.k + 2))
            (v / (M.k + 2))) false π).card : ℝ) := by
  set C := ⌈c⌉₊
  set γ := 1 / 2 - ε - η
  set τ := max 1 ⌈(4 * β * (M.k + 2) * M.k * C : ℝ) / γ⌉₊
  have hτ : 1 ≤ τ := le_max_left _ _
  have hτbig : 4 * β * (M.k + 2) * M.k * C ≤ γ * τ := by
    have h1 : (4 * β * (M.k + 2) * M.k * C : ℝ) / γ ≤ τ :=
      (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right _ _))
    rw [div_le_iff₀ hγ] at h1
    linarith
  obtain ⟨d₀, hd₀⟩ := cor_HCstar_uniform hQ M.k (V := V) (D := D) (s := s) hγ hτ hτbig
  refine ⟨d₀, fun d hd b hb htr T hobl w₀ Pr ΓF hcold lin hside => ?_⟩
  obtain ⟨hM, hT⟩ := ObliviousTransposer.of_obliviousOn hobl htr w₀
  have hTC : T ≤ C * (d * d * b + 1) := by
    have h1 : (T : ℝ) ≤ c * (((d * d * b : ℕ) : ℝ) + 1) :=
      (Nat.cast_le.mpr hT).trans (Nat.floor_le (by positivity))
    have h2 : c * (((d * d * b : ℕ) : ℝ) + 1) ≤ (C : ℝ) * (((d * d * b : ℕ) : ℝ) + 1) :=
      mul_le_mul_of_nonneg_right (Nat.le_ceil c) (by positivity)
    have h3 : (T : ℝ) ≤ (C : ℝ) * (((d * d * b : ℕ) : ℝ) + 1) := h1.trans h2
    have h4 : (T : ℝ) ≤ ((C * (d * d * b + 1) : ℕ) : ℝ) := by
      rw [show ((C * (d * d * b + 1) : ℕ) : ℝ) = (C : ℝ) * (((d * d * b : ℕ) : ℝ) + 1) by
        push_cast; ring]
      exact h3
    exact_mod_cast h4
  by_contra hle
  push Not at hle
  apply hd₀ d hd b hb M rfl _ T hM Pr hβ hTC ΓF hcold lin hside _ hle
  intro ℓ hℓ π hπ hfree
  by_contra hgt
  push Not at hgt
  exact hℓ (mem_filter.mpr ⟨mem_univ _, π, hπ, hfree, hgt⟩)

open Classical in
/-- **The last sentence of Corollary HC\*, given binary [Q9.1].** For `V ≥ 1`, `s`, `C ≥ 1` and
`β ≥ β(M)` there is `d₀` such that at no `d ≥ d₀` (and no width `b ≥ 1`) does an oblivious
transposer with `T ≤ C (L + 1)` have a pruning and a lineage assignment for the empty genie with
merge depth at most `s` at every output position. -/
theorem cor_HCstar_uniform_empty (hQ : Q91Binary) (M : TM) (hk : 1 ≤ M.k) {V β C : ℕ} (hV : 1 ≤ V)
    (hβ : valueWidth M ≤ β) (hC : 1 ≤ C) (s : ℕ) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ b, 1 ≤ b → ∀ (τ₀ : Trace M.k) (T : ℕ),
      ObliviousTransposer M d b τ₀ T → ∀ Pr : Pruning M (d * d * b) τ₀ T,
      T ≤ C * (d * d * b + 1) → ∀ lin : Forest,
      (∀ u v v' π, lin.nxt u = some v → v' ≠ v → (u :: v' :: π) ∈ Pr.toFunDag.net.paths u →
        rCount (fun u v => DeepStep τ₀.work T V (u / (M.k + 2)) (v / (M.k + 2)))
          (u :: v' :: π) = 0) →
      ¬ (∀ (ℓ : Fin (d * d * b)) π, π ∈ Pr.toFunDag.net.paths (outputNodeOf τ₀ T ℓ) →
        dm lin (fun u v => DeepStep τ₀.work T V (u / (M.k + 2)) (v / (M.k + 2))) false π ≤ s) := by
  obtain ⟨d₁, hd₁⟩ := hballs_of_obliviousTransposer hQ M.k
    ((s + 1) * (16 * β * (M.k + 2) * M.k * C) *
      (DF M.k (2 * V - 1) ((1 / 4 : ℝ) / (4 * β * C)) * ⌈4 * β * C / (1 / 4 : ℝ)⌉₊)) C
    (by norm_num : (0 : ℝ) < 1 / 16)
  refine ⟨max d₁ 1, fun d hd b hb τ₀ T hM Pr hT lin hside hround => ?_⟩
  have hL : 1 ≤ d * d * b := Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) hb
  exact cor_HCstar_pruning_empty hM Pr hk hV hβ hC hT hL lin hside s hround
    (hd₁ d (le_of_max_le_left hd) b hb M rfl τ₀ T hM hT)

end MergeDepth
