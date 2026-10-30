import MergeDepth.SkeletonSE
import MergeDepth.SkeletonEntropy

/-!
# Corollaries IS and RV, given binary [Q9.1]

The run of the frozen machine on `X ∈ {0,1}^L` gives the data of Lemma 4.15: the halting time
`haltT M X`, the input-head walk `inPosW M X`, the work-head walks `workPosW M X j` and the output
count `outCountW M X`. The input skeleton at scale `w` is `inSkel w (haltT M) (inPosW M)`
(Lemma 4.15's `inSkel`: the halting time and the blocks of the input head before it).

* `entropy_comp_le`: data processing, `H(g ∘ f) ≤ H(f)`; `entropy_le_logb_card`:
  `H(f) ≤ log₂ |image f|`.
* `frozen_coarse_entropy_le_of_halts`: Lemma 4.15 as stated, for the runs of a machine that halts
  within `⌊c (L + 1)⌋` steps with exactly `L` output bits on every input and has entry at most `V`
  on its work tapes (the hypotheses of the formal `coarse_entropy_le` discharged from the frozen
  model); `frozen_coarse_entropy_le`: the same for a machine that transposes every input within
  `c (L + 1)` steps.
* `runSkeleton_eq_skelOfData`, `inSkel_mul`: the frozen skeleton is a function of Lemma 4.15's
  skeleton data, and the input skeleton at scale `w m` is a function of that at scale `w`.
* `cor_IS`: **Corollary IS.** Given binary [Q9.1], for `k ≥ 1`, `V, w ≥ 1`, `c > 0` and `η > 0`
  there is `d₀` such that for `d ≥ d₀` and every width `b ≥ 1`: if `M` transposes every input
  within `c (L + 1)` steps and has entry at most `V` on every work tape on every input, then
  `H(σ^in_w(X)) > (1/2 - η) L`.
* `cor_RV`: **Corollary RV.** Given binary [Q9.1], for `k ≥ 1`, `V ≥ 1` and `c > 0` there is `d₀`
  such that for `d ≥ d₀` and every width `b ≥ 1`, no machine that transposes every input within
  `c (L + 1)` steps has entry at most `V` on the input tape and on every work tape on every input.
-/

namespace MergeDepth

open Finset Filter BoundedNesting Real Transpose
open scoped Topology

set_option autoImplicit false

/-! ### Data processing -/

section DataProcessing

variable {Ω α β : Type*} [Fintype Ω] [Nonempty Ω] [DecidableEq α] [DecidableEq β]

/-- **Data processing.** A function of `f` has at most the entropy of `f`. -/
theorem entropy_comp_le (f : Ω → α) (g : α → β) : entropy (g ∘ f) ≤ entropy f := by
  have himg : univ.image (g ∘ f) = (univ.image f).image g := by rw [image_image]
  have hsplit : entropy f = ∑ b ∈ univ.image (g ∘ f),
      ∑ a ∈ (univ.image f).filter (g · = b), prob f a * logb 2 (1 / prob f a) := by
    unfold entropy
    rw [himg, sum_fiberwise_of_maps_to (fun a ha => mem_image_of_mem g ha)]
  rw [hsplit]
  unfold entropy
  refine sum_le_sum fun b hb => ?_
  have hq : prob (g ∘ f) b = ∑ a ∈ (univ.image f).filter (g · = b), prob f a := prob_comp f g b
  calc prob (g ∘ f) b * logb 2 (1 / prob (g ∘ f) b)
      = (∑ a ∈ (univ.image f).filter (g · = b), prob f a) * logb 2 (1 / prob (g ∘ f) b) := by
        rw [← hq]
    _ = ∑ a ∈ (univ.image f).filter (g · = b), prob f a * logb 2 (1 / prob (g ∘ f) b) :=
        sum_mul _ _ _
    _ ≤ ∑ a ∈ (univ.image f).filter (g · = b), prob f a * logb 2 (1 / prob f a) := by
        refine sum_le_sum fun a ha => ?_
        have hpa : 0 < prob f a := prob_pos (mem_filter.mp ha).1
        have hle : prob f a ≤ prob (g ∘ f) b := by
          rw [hq]
          exact single_le_sum (f := fun a => prob f a)
            (fun a ha => (prob_pos (mem_filter.mp ha).1).le) ha
        exact mul_le_mul_of_nonneg_left (logb_le_logb_of_le (by norm_num)
          (one_div_pos.mpr (prob_pos hb)) (one_div_le_one_div_of_le hpa hle)) hpa.le

omit [DecidableEq α] [DecidableEq β] in
/-- A constant has entropy zero. -/
theorem entropy_const_unit : entropy (fun _ : Ω => ()) = 0 := by
  unfold entropy
  have himg : univ.image (fun _ : Ω => ()) = {()} := by
    ext u
    simp
  have hp : prob (fun _ : Ω => ()) () = 1 := by
    unfold prob
    rw [filter_true_of_mem (fun _ _ => rfl), card_univ]
    exact div_self (by exact_mod_cast Fintype.card_ne_zero)
  rw [himg, sum_singleton, hp]
  simp

omit [DecidableEq β] in
/-- The entropy is at most the logarithm of the number of values. -/
theorem entropy_le_logb_card (f : Ω → α) : entropy f ≤ logb 2 (univ.image f).card := by
  have h := entropy_le_of_fibres f (fun _ : α => ()) (N := ((univ.image f).card : ℝ))
    (fun _ => by exact_mod_cast card_le_card (filter_subset _ _))
  have e : ((fun _ : α => ()) ∘ f) = fun _ : Ω => () := rfl
  rw [e, entropy_const_unit, zero_add] at h
  exact h

end DataProcessing

/-! ### The data of a run -/

section Run

variable (M : TM) {L : ℕ}

/-- The halting time of the run on `X` (`0` if it does not halt). -/
noncomputable def haltT (X : Fin L → Bool) : ℕ := (trace M (List.ofFn X)).haltTime

/-- The input-head walk of the run on `X`. -/
def inPosW (X : Fin L → Bool) (t : ℕ) : ℤ := (Transpose.Tape.run M (List.ofFn X) t).inPos

/-- The work-head walks of the run on `X`. -/
def workPosW (X : Fin L → Bool) (j : Fin M.k) (t : ℕ) : ℤ :=
  (Transpose.Tape.run M (List.ofFn X) t).workPos j

/-- The output count of the run on `X`: the number of bits appended before each time. -/
def outCountW (X : Fin L → Bool) (t : ℕ) : ℤ :=
  ((Transpose.Tape.run M (List.ofFn X) t).outRev.length : ℤ)

end Run

theorem inPosW_isWalk (M : TM) {L : ℕ} (X : Fin L → Bool) : IsWalk (inPosW M X) := fun t => by
  simp only [inPosW]
  rw [inPos_eq_input, inPos_eq_input]
  exact (trace M _).abs_input_succ_sub_le t

/-- **A run that halts with `L` output bits.** If the run on `X ∈ {0,1}^L` halts at time `s` with
exactly `L` output bits, then `haltT M X = s` and `L ≤ s`. -/
theorem haltT_eq_of_haltsAt {M : TM} {L s : ℕ} {X : Fin L → Bool}
    (hs : Transpose.Tape.HaltsAt M (List.ofFn X) s)
    (hlen : (Transpose.Tape.run M (List.ofFn X) s).outRev.length = L) :
    haltT M X = s ∧ L ≤ s := by
  refine ⟨haltTime_eq_of_haltsAt hs, ?_⟩
  have := Transpose.Tape.Impl.outLen_le_self (M := M) (List.ofFn X) s
  omega

/-- **A transposed input.** The run halts at `haltT M X`, which lies between `L` and `c (L + 1)`,
and appends exactly `L` bits. -/
theorem haltT_spec {M : TM} {d b : ℕ} {c : ℝ} {X : Fin (d * d * b) → Bool}
    (h : TransposesInput M d b c X) :
    Transpose.Tape.HaltsAt M (List.ofFn X) (haltT M X) ∧ d * d * b ≤ haltT M X ∧
      haltT M X ≤ ⌊c * (((d * d * b : ℕ) : ℝ) + 1)⌋₊ ∧
      (Transpose.Tape.run M (List.ofFn X) (haltT M X)).outRev.length = d * d * b := by
  obtain ⟨s, hs, hhalt⟩ := h.halts
  obtain ⟨s', hs', hlen, -⟩ := h.outputsTranspose.output
  obtain rfl := Transpose.Tape.Impl.haltsAt_unique hs' hhalt
  have hlen' : (Transpose.Tape.run M (List.ofFn X) s').outRev.length = d * d * b := by
    rw [← List.length_reverse]
    exact hlen
  obtain ⟨hT, hL⟩ := haltT_eq_of_haltsAt hhalt hlen'
  rw [hT]
  exact ⟨hhalt, hL, hs, hlen'⟩

open Classical in
/-- **Lemma 4.15 for the runs of a machine**, with the hypotheses of the lemma: on every input
`X ∈ {0,1}^L` the machine halts within `⌊c (L + 1)⌋` steps with exactly `L` output bits, and before
its halting time it enters every work-tape cell at most `V` times. -/
theorem frozen_coarse_entropy_le_of_halts {M : TM} {L V w : ℕ} {c : ℝ} (hc : 0 < c) (hV : 1 ≤ V)
    (hw : 4 * V ≤ w) (hL2w : 2 * w ≤ L) (hL16 : 16 * V ≤ L)
    (hrun : ∀ X : Fin L → Bool, ∃ s ≤ ⌊c * ((L : ℝ) + 1)⌋₊,
      Transpose.Tape.HaltsAt M (List.ofFn X) s ∧
        (Transpose.Tape.run M (List.ofFn X) s).outRev.length = L)
    (hentry : ∀ (X : Fin L → Bool) (T : ℕ), Transpose.Tape.HaltsAt M (List.ofFn X) T →
      ∀ j cell, (entries (workWalk M (List.ofFn X) j) cell (T - 1)).card ≤ V) :
    entropy (skelData w (haltT M (L := L)) (inPosW M) (workPosW M) (outCountW M)) ≤
      entropy (inSkel w (haltT M (L := L)) (inPosW M)) +
      (4 * M.k * V * c * logb 2 (exp 1 * w / V) + logb 2 (2 * exp 1 * c * w)) / w * L +
        4 * M.k * V * logb 2 (exp 1 * w / V) := by
  have hX : ∀ X : Fin L → Bool, Transpose.Tape.HaltsAt M (List.ofFn X) (haltT M X) ∧
      L ≤ haltT M X ∧ haltT M X ≤ ⌊c * ((L : ℝ) + 1)⌋₊ ∧
      (Transpose.Tape.run M (List.ofFn X) (haltT M X)).outRev.length = L := fun X => by
    obtain ⟨s, hsc, hs, hlen⟩ := hrun X
    obtain ⟨hT, hL⟩ := haltT_eq_of_haltsAt hs hlen
    rw [hT]
    exact ⟨hs, hL, hsc, hlen⟩
  refine coarse_entropy_le hV hw hL2w hL16 (haltT M) (inPosW M) (workPosW M) (outCountW M)
    (fun X => ?_) (fun X j => ?_) (fun X => ?_)
  · obtain ⟨-, h1, h2, -⟩ := hX X
    exact ⟨h1, (Nat.cast_le.mpr h2).trans (Nat.floor_le (by positivity))⟩
  · obtain ⟨hh, -, -, -⟩ := hX X
    exact ⟨workWalk_isWalk (List.ofFn X) j, rfl, fun c' => hentry X _ hh j c'⟩
  · obtain ⟨-, -, -, hlen⟩ := hX X
    refine ⟨rfl, fun t _ => ?_, fun t ht => ?_⟩
    · simp only [outCountW]
      rw [Transpose.Tape.Impl.outRev_length_succ]
      split_ifs
      · right; push_cast; ring
      · left; simp
    · simp only [outCountW]
      have := Transpose.Tape.Impl.outRev_length_mono (M := M) (List.ofFn X) ht.le
      rw [hlen] at this
      exact_mod_cast this

open Classical in
/-- **Lemma 4.15 for the runs of a transposer**: a machine that transposes every input within
`c (L + 1)` steps (`TransposesInput`) satisfies the hypotheses of
`frozen_coarse_entropy_le_of_halts`. -/
theorem frozen_coarse_entropy_le {M : TM} {d b V w : ℕ} {c : ℝ} (hc : 0 < c) (hV : 1 ≤ V)
    (hw : 4 * V ≤ w) (hL2w : 2 * w ≤ d * d * b) (hL16 : 16 * V ≤ d * d * b)
    (htr : ∀ X : Fin (d * d * b) → Bool, TransposesInput M d b c X)
    (hentry : ∀ (X : Fin (d * d * b) → Bool) (T : ℕ), Transpose.Tape.HaltsAt M (List.ofFn X) T →
      ∀ j cell, (entries (workWalk M (List.ofFn X) j) cell (T - 1)).card ≤ V) :
    entropy (skelData w (haltT M (L := d * d * b)) (inPosW M) (workPosW M) (outCountW M)) ≤
      entropy (inSkel w (haltT M (L := d * d * b)) (inPosW M)) +
      (4 * M.k * V * c * logb 2 (exp 1 * w / V) + logb 2 (2 * exp 1 * c * w)) / w *
        (d * d * b : ℕ) + 4 * M.k * V * logb 2 (exp 1 * w / V) :=
  frozen_coarse_entropy_le_of_halts hc hV hw hL2w hL16 (fun X =>
    ⟨haltT M X, (haltT_spec (htr X)).2.2.1, (haltT_spec (htr X)).1, (haltT_spec (htr X)).2.2.2⟩)
    hentry

/-- The frozen skeleton as a function of the skeleton data of Lemma 4.15. -/
def skelOfData {k : ℕ} (p : ℕ × (ℕ → ℤ × (Fin k → ℤ) × ℤ)) : Skeleton k where
  T := p.1
  s0 t := (p.2 t).1
  s j t := (p.2 t).2.1 j
  sout t := ((p.2 t).2.2).toNat

/-- The frozen skeleton of a run is a function of the skeleton data of Lemma 4.15. -/
theorem runSkeleton_eq_skelOfData (M : TM) (w : ℕ) {L : ℕ} (X : Fin L → Bool) :
    runSkeleton M w (List.ofFn X) =
      skelOfData (skelData w (haltT M) (inPosW M) (workPosW M) (outCountW M) X) := by
  show runSkeleton M w (List.ofFn X) = skelOfData ((trace M (List.ofFn X)).haltTime,
    fun t => if t < (trace M (List.ofFn X)).haltTime then
      ((Transpose.Tape.run M (List.ofFn X) t).inPos / w,
        fun j => (Transpose.Tape.run M (List.ofFn X) t).workPos j / w,
        ((Transpose.Tape.run M (List.ofFn X) t).outRev.length : ℤ) / w)
    else (0, fun _ => 0, 0))
  simp only [runSkeleton, skelOfData, Skeleton.mk.injEq, true_and]
  refine ⟨funext fun t => ?_, funext fun j => funext fun t => ?_, funext fun t => ?_⟩ <;>
    split_ifs <;> rfl

/-- The input skeleton at scale `w m` is a function of the input skeleton at scale `w`. -/
theorem inSkel_mul (w m : ℕ) {L : ℕ} (T : (Fin L → Bool) → ℕ) (x0 : (Fin L → Bool) → ℕ → ℤ) :
    inSkel (w * m) T x0 =
      (fun p : ℕ × (ℕ → ℤ) => (p.1, fun t => p.2 t / (m : ℤ))) ∘ inSkel w T x0 := by
  funext X
  simp only [inSkel, Function.comp_apply, Prod.mk.injEq, true_and]
  funext t
  split_ifs
  · push_cast
    rw [Int.ediv_ediv_of_nonneg (by positivity)]
  · simp

/-! ### Corollary IS -/

open Classical in
/-- **Corollary IS (input steering), given binary [Q9.1].** Let `M` have `k ≥ 1` work tapes,
`V, w ≥ 1`, `c > 0` and `η > 0`. There is `d₀` such that for `d ≥ d₀` and every width `b ≥ 1`:
if (i) `M` transposes every input `X ∈ {0,1}^L` within `c (L + 1)` steps and (ii) on every input
every work-tape cell is entered at most `V` times before the halting time, then (iii) fails:
the input skeleton at scale `w` has entropy `H(σ^in_w(X)) > (1/2 - η) L`. -/
theorem cor_IS (hQ : Q91Binary) {M : TM} (hk : 1 ≤ M.k) {V w : ℕ} (hV : 1 ≤ V) (hw : 1 ≤ w)
    {c η : ℝ} (hc : 0 < c) (hη : 0 < η) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ b, 1 ≤ b →
      (∀ X : Fin (d * d * b) → Bool, TransposesInput M d b c X) →
      (∀ (X : Fin (d * d * b) → Bool) (T : ℕ), Transpose.Tape.HaltsAt M (List.ofFn X) T →
        ∀ j cell, (entries (workWalk M (List.ofFn X) j) cell (T - 1)).card ≤ V) →
      (1 / 2 - η) * (d * d * b : ℕ) <
        entropy (inSkel w (haltT M) (inPosW M (L := d * d * b))) := by
  -- a scale `w m` at which the coarse work walks and the output carry little entropy
  have hθ := theta_tendsto (M.k : ℝ) (V : ℝ) c (by exact_mod_cast hV) hc
  have hcast : Tendsto (fun m : ℕ => ((w * m : ℕ) : ℝ)) atTop atTop := by
    refine tendsto_atTop_mono (fun m => ?_) tendsto_natCast_atTop_atTop
    exact_mod_cast Nat.le_mul_of_pos_left m (by omega)
  obtain ⟨m, hm1, hm2⟩ := (((hθ.comp hcast).eventually (gt_mem_nhds
    (by positivity : (0 : ℝ) < η / 2))).and (eventually_ge_atTop (4 * V))).exists
  simp only [Function.comp_apply] at hm1
  have hwm : 4 * V ≤ w * m := le_trans hm2 (Nat.le_mul_of_pos_left m (by omega))
  obtain ⟨d₁, hd₁⟩ := thm_SE hQ hk hV (by omega : 1 ≤ w * m) hc (by positivity : 0 < η / 4)
  set K : ℝ := 4 * M.k * V * logb 2 (exp 1 * ((w * m : ℕ) : ℝ) / V)
  refine ⟨max (max d₁ (2 * (w * m) + 16 * V)) ⌈4 * K / η⌉₊, fun d hd b hb htr hentry => ?_⟩
  have hdL : d ≤ d * d * b := by
    rcases Nat.eq_zero_or_pos d with h0 | hpos
    · omega
    · calc d ≤ d * d := Nat.le_mul_of_pos_right _ hpos
        _ ≤ d * d * b := Nat.le_mul_of_pos_right _ (by omega)
  have hd' : 2 * (w * m) + 16 * V ≤ d * d * b :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_trans hd hdL)
  have hKL : K ≤ η / 4 * (d * d * b : ℕ) := by
    have h1 : (4 * K / η : ℝ) ≤ (d * d * b : ℕ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_right _ _) (le_trans hd hdL))
    rw [div_le_iff₀ hη] at h1
    linarith
  by_contra hH
  push Not at hH
  -- the input skeleton at scale `w m` is a function of that at scale `w`
  have h1 : entropy (inSkel (w * m) (haltT M) (inPosW M (L := d * d * b))) ≤
      entropy (inSkel w (haltT M) (inPosW M (L := d * d * b))) := by
    rw [inSkel_mul]
    exact entropy_comp_le _ _
  -- Lemma 4.15 at scale `w m`
  have h2 := frozen_coarse_entropy_le hc hV hwm (by omega) (by omega) htr hentry
  -- the frozen skeleton is a function of the skeleton data
  have h3 : entropy (fun X : Fin (d * d * b) → Bool => runSkeleton M (w * m) (List.ofFn X)) ≤
      entropy (skelData (w * m) (haltT M (L := d * d * b)) (inPosW M) (workPosW M)
        (outCountW M)) := by
    have e : (fun X : Fin (d * d * b) → Bool => runSkeleton M (w * m) (List.ofFn X)) =
        skelOfData ∘ skelData (w * m) (haltT M (L := d * d * b)) (inPosW M) (workPosW M)
          (outCountW M) :=
      funext fun X => runSkeleton_eq_skelOfData M (w * m) X
    rw [e]
    exact entropy_comp_le _ _
  have h4 := hd₁ d (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hd)) b hb htr hentry
  have hL0 : (0 : ℝ) ≤ (d * d * b : ℕ) := Nat.cast_nonneg _
  have h5 : (4 * M.k * V * c * logb 2 (exp 1 * ((w * m : ℕ) : ℝ) / V) +
      logb 2 (2 * exp 1 * c * ((w * m : ℕ) : ℝ))) / ((w * m : ℕ) : ℝ) * (d * d * b : ℕ) ≤
      η / 2 * (d * d * b : ℕ) := mul_le_mul_of_nonneg_right hm1.le hL0
  linarith

/-! ### Corollary RV -/

open Classical in
/-- **The input skeleton of a bounded-entry input head** carries at most
`log₂ (c (L + 1) + 1) + 2 V (c (L + 1)/w + 2) log₂ (e w/V)` bits. -/
theorem inSkel_entropy_le {M : TM} {d b V w : ℕ} {c : ℝ} (hc : 0 < c) (hV : 1 ≤ V)
    (hw : 4 * V ≤ w) (hL16 : 16 * V ≤ d * d * b)
    (htr : ∀ X : Fin (d * d * b) → Bool, TransposesInput M d b c X)
    (hin : ∀ (X : Fin (d * d * b) → Bool) (T : ℕ), Transpose.Tape.HaltsAt M (List.ofFn X) T →
      ∀ cell, (entries (inPosW M X) cell (T - 1)).card ≤ V) :
    entropy (inSkel w (haltT M) (inPosW M (L := d * d * b))) ≤
      logb 2 (c * ((d * d * b : ℕ) + 1) + 1) +
        2 * V * (c * ((d * d * b : ℕ) + 1) / w + 2) * logb 2 (exp 1 * w / V) := by
  have hw0 : 0 < w := by omega
  have hwr : (0 : ℝ) < w := by exact_mod_cast hw0
  have hVr : (1 : ℝ) ≤ V := by exact_mod_cast hV
  set A : ℝ := exp 1 * w / V
  have hA : 1 ≤ A := by
    have h4 : (4 : ℝ) * V ≤ w := by exact_mod_cast hw
    have he : (2 : ℝ) < exp 1 := by have := add_one_lt_exp (one_ne_zero (α := ℝ)); linarith
    simp only [A]
    rw [le_div_iff₀ (by linarith)]
    nlinarith
  set CL : ℝ := c * ((d * d * b : ℕ) + 1)
  set N : ℝ := A ^ (2 * V * (CL / w + 2) : ℝ)
  -- the fibres over the halting time
  have hfib : ∀ T₀ : ℕ, (((univ.image (inSkel w (haltT M) (inPosW M (L := d * d * b)))).filter
      (fun p : ℕ × (ℕ → ℤ) => p.1 = T₀)).card : ℝ) ≤ N := by
    intro T₀
    set F := (univ.image (inSkel w (haltT M) (inPosW M (L := d * d * b)))).filter
      (fun p : ℕ × (ℕ → ℤ) => p.1 = T₀)
    have hF : ∀ p ∈ F, ∃ X : Fin (d * d * b) → Bool,
        haltT M X = T₀ ∧ inSkel w (haltT M) (inPosW M) X = p := by
      intro p hp
      obtain ⟨hp1, hp2⟩ := mem_filter.mp hp
      obtain ⟨X, -, rfl⟩ := mem_image.mp hp1
      exact ⟨X, hp2, rfl⟩
    rcases F.eq_empty_or_nonempty with hFe | ⟨p₀, hp₀⟩
    · rw [hFe, card_empty, Nat.cast_zero]
      positivity
    obtain ⟨X₀, hX₀, -⟩ := hF p₀ hp₀
    obtain ⟨-, hLT, hTc, -⟩ := haltT_spec (htr X₀)
    rw [hX₀] at hLT hTc
    -- restrict to `[0, T₀)`
    let e : ℕ × (ℕ → ℤ) → (Fin T₀ → ℤ) := fun p t => p.2 t
    have hinj : Set.InjOn e F := by
      intro p hp p' hp' he
      obtain ⟨X, hX, rfl⟩ := hF p hp
      obtain ⟨X', hX', rfl⟩ := hF p' hp'
      simp only [inSkel, Prod.mk.injEq]
      refine ⟨hX.trans hX'.symm, funext fun t => ?_⟩
      by_cases ht : t < T₀
      · have := congr_fun he ⟨t, ht⟩
        simpa [e, inSkel] using this
      · simp only [hX, hX', ht, ↓reduceIte]
    have hcard : (F.card : ℝ) ≤ A ^ (2 * V * (T₀ / w + 2) : ℝ) := by
      rw [← card_image_of_injOn hinj]
      refine card_coarse_le hV hw (by omega) (F.image e) fun σ hσ => ?_
      obtain ⟨p, hp, rfl⟩ := mem_image.mp hσ
      obtain ⟨X, hX, rfl⟩ := hF p hp
      obtain ⟨hh, -, -, -⟩ := haltT_spec (htr X)
      refine ⟨inPosW M X, inPosW_isWalk M X, rfl, fun cell => ?_, fun t => ?_⟩
      · have := hin X _ hh cell
        rwa [hX] at this
      · simp [e, inSkel, hX, t.2]
    refine hcard.trans (Real.rpow_le_rpow_of_exponent_le hA ?_)
    have hT₀ : (T₀ : ℝ) ≤ CL := (Nat.cast_le.mpr hTc).trans (Nat.floor_le (by positivity))
    have : (T₀ : ℝ) / w ≤ CL / w := div_le_div_of_nonneg_right hT₀ hwr.le
    nlinarith
  have h1 := entropy_le_of_fibres (inSkel w (haltT M) (inPosW M (L := d * d * b)))
    (fun p : ℕ × (ℕ → ℤ) => p.1) hfib
  -- the halting time takes at most `c (L + 1) + 1` values
  have h2 : entropy ((fun p : ℕ × (ℕ → ℤ) => p.1) ∘
      inSkel w (haltT M) (inPosW M (L := d * d * b))) ≤ logb 2 (CL + 1) := by
    refine (entropy_le_logb_card _).trans ?_
    have hsub : univ.image ((fun p : ℕ × (ℕ → ℤ) => p.1) ∘
        inSkel w (haltT M) (inPosW M (L := d * d * b))) ⊆
        range (⌊CL⌋₊ + 1) := by
      intro n hn
      obtain ⟨X, -, rfl⟩ := mem_image.mp hn
      obtain ⟨-, -, h, -⟩ := haltT_spec (htr X)
      exact mem_range.mpr (Nat.lt_succ_of_le h)
    have hpos : (0 : ℝ) < (univ.image ((fun p : ℕ × (ℕ → ℤ) => p.1) ∘
        inSkel w (haltT M) (inPosW M (L := d * d * b)))).card := by
      exact_mod_cast (univ_nonempty.image _).card_pos
    refine logb_le_logb_of_le (by norm_num) hpos ?_
    have := card_le_card hsub
    rw [card_range] at this
    have h3 : ((⌊CL⌋₊ + 1 : ℕ) : ℝ) ≤ CL + 1 := by
      push_cast
      linarith [Nat.floor_le (show (0 : ℝ) ≤ CL by positivity)]
    exact (Nat.cast_le.mpr this).trans h3
  have hNlog : logb 2 N = 2 * V * (CL / w + 2) * logb 2 A := by
    simp only [N]
    rw [logb_rpow_eq_mul_logb_of_pos (by linarith)]
  linarith

open Classical in
/-- **Corollary RV (revisits), given binary [Q9.1].** Let `M` have `k ≥ 1` work tapes, `V ≥ 1` and
`c > 0`. There is `d₀` such that for `d ≥ d₀` and every width `b ≥ 1`: if `M` transposes every
input `X ∈ {0,1}^L` within `c (L + 1)` steps and its input head enters every cell at most `V`
times before the halting time, on every input, then on some input some work-tape cell is entered
more than `V` times. -/
theorem cor_RV (hQ : Q91Binary) {M : TM} (hk : 1 ≤ M.k) {V : ℕ} (hV : 1 ≤ V) {c : ℝ}
    (hc : 0 < c) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ b, 1 ≤ b →
      (∀ X : Fin (d * d * b) → Bool, TransposesInput M d b c X) →
      (∀ (X : Fin (d * d * b) → Bool) (T : ℕ), Transpose.Tape.HaltsAt M (List.ofFn X) T →
        ∀ cell, (entries (inPosW M X) cell (T - 1)).card ≤ V) →
      ¬ (∀ (X : Fin (d * d * b) → Bool) (T : ℕ), Transpose.Tape.HaltsAt M (List.ofFn X) T →
        ∀ j cell, (entries (workWalk M (List.ofFn X) j) cell (T - 1)).card ≤ V) := by
  have hVr : (0 : ℝ) < V := by exact_mod_cast hV
  -- a scale `w` with `4 V c log₂ (e w/V) ≤ w/8`
  have hθ := theta_tendsto (1 : ℝ) (V : ℝ) c hVr hc
  obtain ⟨w, hw1, hw2, hw3⟩ := (((hθ.comp tendsto_natCast_atTop_atTop).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8))).and ((eventually_ge_atTop (4 * V)).and
      (eventually_ge_atTop ⌈1 / (2 * exp 1 * c)⌉₊))).exists
  simp only [Function.comp_apply] at hw1
  have hw0 : 0 < w := by omega
  have hwr : (0 : ℝ) < w := by exact_mod_cast hw0
  have hlogpos : 0 ≤ logb 2 (2 * exp 1 * c * w) := by
    apply logb_nonneg (by norm_num)
    have h1 : 1 / (2 * exp 1 * c) ≤ (w : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hw3)
    rw [div_le_iff₀ (by positivity)] at h1
    linarith
  have hwθ : 4 * V * c * logb 2 (exp 1 * w / V) ≤ w / 8 := by
    have h := hw1.le
    rw [div_le_iff₀ hwr] at h
    nlinarith
  obtain ⟨d₁, hd₁⟩ := cor_IS hQ hk hV (by omega : 1 ≤ w) hc (by norm_num : (0 : ℝ) < 1 / 4)
  -- `log₂ L ≤ L/32` eventually
  have hlog : Tendsto (fun x : ℝ => log x / x) atTop (𝓝 0) := by
    simpa using tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp
    ((tendsto_order.mp hlog).2 (log 2 / 32) (by positivity))
  set K : ℝ := logb 2 (2 * c + 1) + 4 * V * logb 2 (exp 1 * w / V)
  refine ⟨max (max d₁ (16 * V + 2)) (max ⌈x₀⌉₊ ⌈32 * K⌉₊), fun d hd b hb htr hin hwork => ?_⟩
  have hdL : d ≤ d * d * b := by
    rcases Nat.eq_zero_or_pos d with h0 | hpos
    · omega
    · calc d ≤ d * d := Nat.le_mul_of_pos_right _ hpos
        _ ≤ d * d * b := Nat.le_mul_of_pos_right _ (by omega)
  have hdmax := le_trans hd hdL
  have hL16 : 16 * V ≤ d * d * b := le_trans (by omega)
    (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hdmax)
  have hL1 : (1 : ℝ) ≤ ((d * d * b : ℕ) : ℝ) := by
    have : 1 ≤ d * d * b := by omega
    exact_mod_cast this
  have hLx : x₀ ≤ ((d * d * b : ℕ) : ℝ) := (Nat.le_ceil _).trans
    (by exact_mod_cast le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hdmax)
  have hLK : 32 * K ≤ ((d * d * b : ℕ) : ℝ) := (Nat.le_ceil _).trans
    (by exact_mod_cast le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hdmax)
  have hE := inSkel_entropy_le hc hV hw2 hL16 htr hin
  have hIS := hd₁ d (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hd)) b hb htr hwork
  set L : ℝ := ((d * d * b : ℕ) : ℝ)
  -- the arithmetic: `log₂ (c (L + 1) + 1) ≤ log₂ (2c + 1) + log₂ L ≤ log₂ (2c + 1) + L/32`
  have hlogL : logb 2 L ≤ L / 32 := by
    have h := (hx₀ L hLx).le
    rw [div_le_iff₀ (by linarith)] at h
    rw [logb, div_le_iff₀ (log_pos (by norm_num))]
    nlinarith [log_pos (show (1 : ℝ) < 2 by norm_num)]
  have h1 : logb 2 (c * (L + 1) + 1) ≤ logb 2 (2 * c + 1) + logb 2 L := by
    rw [← logb_mul (by positivity) (by positivity)]
    refine logb_le_logb_of_le (by norm_num) (by positivity) ?_
    nlinarith
  have h2 : 2 * V * (c * (L + 1) / w + 2) * logb 2 (exp 1 * w / V) ≤
      L / 8 + 4 * V * logb 2 (exp 1 * w / V) := by
    have hA : 0 ≤ logb 2 (exp 1 * w / V) := by
      apply logb_nonneg (by norm_num)
      have h4 : (4 : ℝ) * V ≤ w := by exact_mod_cast hw2
      have he : (2 : ℝ) < exp 1 := by have := add_one_lt_exp (one_ne_zero (α := ℝ)); linarith
      rw [le_div_iff₀ hVr]
      nlinarith
    have e : 2 * V * (c * (L + 1) / w + 2) * logb 2 (exp 1 * w / V) =
        (4 * V * c * logb 2 (exp 1 * w / V)) * ((L + 1) / (2 * w)) +
          4 * V * logb 2 (exp 1 * w / V) := by
      field_simp
      ring
    rw [e]
    have h5 : (4 * V * c * logb 2 (exp 1 * w / V)) * ((L + 1) / (2 * w)) ≤
        w / 8 * ((L + 1) / (2 * w)) :=
      mul_le_mul_of_nonneg_right hwθ (by positivity)
    have h6 : w / 8 * ((L + 1) / (2 * w)) = (L + 1) / 16 := by
      field_simp
      ring
    linarith
  linarith

end MergeDepth
