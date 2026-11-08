import NativeRelations.MacroscopicThreshold
import TapeStorageRates.TraceTransfer
import Mathlib.Data.Fintype.Pi

/-!
# Macroscopic Displacement Skeletons and Crossing-Capable Words

Discretizes each work-tape walk at spatial scale `Λ` into milestones and a sign word (`milestones`,
`tapeSkeleton`, `traceSkeletonTuple`), proves confinement and finiteness (`epochGrid_confines_and_exact`,
`card_boundedSkeletonTuple`), characterizes crossing-capable skeletons (`IsScaleFreeCrossingCapable`,
`isCrossingCapableSkeleton_of_tapeCrossingLowers_nonempty`), and shows that macroscopic revisits cross
leg boundaries (`legOfEpoch_lt_of_isHop_gt2H`, `legCrossingLowers`).
-/

set_option autoImplicit false

namespace NativeRelations

open Filter Finset Transpose Transpose.Tape BoundedNesting MergeDepth MotionDepthCodes
  BoundedStackDepth TapeStorageRates
open scoped BigOperators

/-! ## §1. Greedy `Λ`-Milestone Walk Skeleton, Confinement, & Turn Bound (Lemma 6.3(a)) -/

section GreedyMilestoneSkeleton

/-- Net integer grid displacement of a milestone list `ms : List (ℕ × Bool)` (`true = +1`, `false = -1`). -/
def milestoneGrid (ms : List (ℕ × Bool)) : ℤ :=
  ms.foldl (fun g x => g + if x.2 then 1 else -1) 0

/-- Net integer grid displacement of a step-direction list `s : List Bool`. -/
def skeletonGridEnd (s : List Bool) : ℤ :=
  s.foldl (fun g b => g + if b then 1 else -1) 0

/-- Grid coordinate `g_i` after the first `i` skeleton steps (`g_0 = 0`). -/
def skeletonGridAt (s : List Bool) (i : ℕ) : ℤ :=
  skeletonGridEnd (s.take i)

@[simp] theorem milestoneGrid_nil : milestoneGrid [] = 0 := rfl

@[simp] theorem milestoneGrid_append_singleton (ms : List (ℕ × Bool)) (x : ℕ × Bool) :
    milestoneGrid (ms ++ [x]) = milestoneGrid ms + (if x.2 then 1 else -1) := by
  simp [milestoneGrid, List.foldl_append]

@[simp] theorem skeletonGridEnd_nil : skeletonGridEnd [] = 0 := rfl

@[simp] theorem skeletonGridEnd_append_singleton (s : List Bool) (b : Bool) :
    skeletonGridEnd (s ++ [b]) = skeletonGridEnd s + (if b then 1 else -1) := by
  simp [skeletonGridEnd, List.foldl_append]

theorem milestoneGrid_eq_skeletonGridEnd_map (ms : List (ℕ × Bool)) :
    milestoneGrid ms = skeletonGridEnd (ms.map Prod.snd) := by
  induction ms using List.reverseRecOn with
  | nil => rfl
  | append_singleton xs x ih =>
    simp [milestoneGrid_append_singleton, skeletonGridEnd_append_singleton, ih]

@[simp] theorem skeletonGridAt_zero (s : List Bool) : skeletonGridAt s 0 = 0 := rfl

theorem skeletonGridAt_succ_of_lt (s : List Bool) {i : ℕ} (hi : i < s.length) :
    skeletonGridAt s (i + 1) = skeletonGridAt s i + (if s[i] then 1 else -1) := by
  unfold skeletonGridAt
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some,
    skeletonGridEnd_append_singleton]

theorem abs_skeletonGridAt_succ_sub_eq_one (s : List Bool) {i : ℕ} (hi : i < s.length) :
    |skeletonGridAt s (i + 1) - skeletonGridAt s i| = 1 := by
  rw [skeletonGridAt_succ_of_lt s hi]
  cases s[i] <;> norm_num

theorem abs_skeletonGridAt_sub_le (s : List Bool) {a b : ℕ} (hab : a ≤ b) :
    |skeletonGridAt s b - skeletonGridAt s a| ≤ ((b - a : ℕ) : ℤ) := by
  induction b with
  | zero =>
    have ha0 : a = 0 := Nat.eq_zero_of_le_zero hab
    subst ha0
    simp
  | succ b ih =>
    rcases eq_or_lt_of_le hab with rfl | hlt
    · simp
    · have hab' : a ≤ b := Nat.le_of_lt_succ hlt
      have hstep : |skeletonGridAt s (b + 1) - skeletonGridAt s b| ≤ 1 := by
        by_cases hb : b < s.length
        · rw [abs_skeletonGridAt_succ_sub_eq_one s hb]
        · have hge : s.length ≤ b := Nat.le_of_not_lt hb
          unfold skeletonGridAt
          rw [List.take_of_length_le (Nat.le_succ_of_le hge), List.take_of_length_le hge]
          simp
      have htri : |skeletonGridAt s (b + 1) - skeletonGridAt s a| ≤
          |skeletonGridAt s (b + 1) - skeletonGridAt s b| +
            |skeletonGridAt s b - skeletonGridAt s a| := by
        simpa using abs_add_le (skeletonGridAt s (b + 1) - skeletonGridAt s b)
          (skeletonGridAt s b - skeletonGridAt s a)
      have hih := ih hab'
      have hcast : ((b + 1 - a : ℕ) : ℤ) = ((b - a : ℕ) : ℤ) + 1 := by omega
      linarith

/-- **Greedy `Λ`-Milestone Scan (`Hysteresis-Free`)**:
Scans steps `t = 0, 1, ..., T - 1` and records `(t, dir)` each time `|y t - g * Λ| ≥ Λ`. -/
def milestones (y : ℕ → ℤ) (Λ : ℕ) : ℕ → List (ℕ × Bool)
  | 0 => []
  | t + 1 =>
    let ms := milestones y Λ t
    let g := milestoneGrid ms
    if (Λ : ℤ) ≤ |y t - g * (Λ : ℤ)| then
      ms ++ [(t, decide (0 < y t - g * (Λ : ℤ)))]
    else
      ms

theorem milestones_succ (y : ℕ → ℤ) (Λ t : ℕ) :
    milestones y Λ (t + 1) =
      if (Λ : ℤ) ≤ |y t - milestoneGrid (milestones y Λ t) * (Λ : ℤ)| then
        milestones y Λ t ++ [(t, decide (0 < y t - milestoneGrid (milestones y Λ t) * (Λ : ℤ)))]
      else
        milestones y Λ t := rfl

theorem milestones_succ_of_le {y : ℕ → ℤ} {Λ t : ℕ}
    (h : (Λ : ℤ) ≤ |y t - milestoneGrid (milestones y Λ t) * (Λ : ℤ)|) :
    milestones y Λ (t + 1) =
      milestones y Λ t ++ [(t, decide (0 < y t - milestoneGrid (milestones y Λ t) * (Λ : ℤ)))] := by
  rw [milestones_succ]
  split_ifs
  rfl

theorem milestones_succ_of_not_le {y : ℕ → ℤ} {Λ t : ℕ}
    (h : ¬ (Λ : ℤ) ≤ |y t - milestoneGrid (milestones y Λ t) * (Λ : ℤ)|) :
    milestones y Λ (t + 1) = milestones y Λ t := by
  rw [milestones_succ]
  split_ifs
  rfl

/-- Coarse step-direction skeleton `tapeSkeleton y T Λ : List Bool` (`true = +Λ`, `false = -Λ`). -/
def tapeSkeleton (y : ℕ → ℤ) (T Λ : ℕ) : List Bool :=
  (milestones y Λ T).map Prod.snd

/-- Milestone timestamps `0 :: [τ_1, ..., τ_m]` (`length = (tapeSkeleton y T Λ).length + 1`). -/
def milestoneTimes (y : ℕ → ℤ) (T Λ : ℕ) : List ℕ :=
  0 :: (milestones y Λ T).map Prod.fst

/-- Active skeleton epoch index `epochIdx y Λ t ∈ {0, ..., m}` containing timestamp `t`. -/
def epochIdx (y : ℕ → ℤ) (Λ t : ℕ) : ℕ :=
  (milestones y Λ (t + 1)).length

/-- Active grid coordinate `epochGrid y Λ t` during timestamp `t`. -/
def epochGrid (y : ℕ → ℤ) (Λ t : ℕ) : ℤ :=
  milestoneGrid (milestones y Λ (t + 1))

/-- Number of macroscopic sign-reversal turns along a step-direction list `s : List Bool`. -/
def macroTurns : List Bool → ℕ
  | [] => 0
  | [_] => 0
  | b₁ :: b₂ :: rest => (if b₁ != b₂ then 1 else 0) + macroTurns (b₂ :: rest)

theorem macroTurns_le_pred : ∀ s : List Bool, macroTurns s ≤ s.length - 1
  | [] => by simp [macroTurns]
  | [_] => by simp [macroTurns]
  | b₁ :: b₂ :: rest => by
    have ih := macroTurns_le_pred (b₂ :: rest)
    cases b₁ <;> cases b₂ <;> simp [macroTurns] at ih ⊢ <;> omega

theorem macroTurns_le_length (s : List Bool) : macroTurns s ≤ s.length :=
  (macroTurns_le_pred s).trans (Nat.sub_le _ _)

theorem milestones_prefix {y : ℕ → ℤ} {Λ : ℕ} {t₁ t₂ : ℕ} (hle : t₁ ≤ t₂) :
    milestones y Λ t₁ <+: milestones y Λ t₂ := by
  induction t₂ with
  | zero =>
    have ht0 : t₁ = 0 := Nat.eq_zero_of_le_zero hle
    subst ht0
    exact List.prefix_rfl
  | succ t₂ ih =>
    rcases eq_or_lt_of_le hle with rfl | hlt
    · exact List.prefix_rfl
    · have hprev := ih (Nat.le_of_lt_succ hlt)
      simp only [milestones]
      split_ifs
      · exact hprev.trans (List.prefix_append _ _)
      · exact hprev

theorem epochIdx_mono {y : ℕ → ℤ} {Λ t₁ t₂ : ℕ} (hle : t₁ ≤ t₂) :
    epochIdx y Λ t₁ ≤ epochIdx y Λ t₂ :=
  (milestones_prefix (Nat.add_le_add_right hle 1)).length_le

theorem epochIdx_le_length {y : ℕ → ℤ} {Λ t T : ℕ} (ht : t < T) :
    epochIdx y Λ t ≤ (tapeSkeleton y T Λ).length := by
  unfold epochIdx tapeSkeleton
  rw [List.length_map]
  exact (milestones_prefix (Nat.succ_le_of_lt ht)).length_le

theorem epochGrid_eq_skeletonGridAt {y : ℕ → ℤ} {Λ t T : ℕ} (ht : t < T) :
    epochGrid y Λ t = skeletonGridAt (tapeSkeleton y T Λ) (epochIdx y Λ t) := by
  unfold epochGrid skeletonGridAt tapeSkeleton epochIdx
  rw [milestoneGrid_eq_skeletonGridEnd_map]
  obtain ⟨rest, hrest⟩ := milestones_prefix (y := y) (Λ := Λ) (Nat.succ_le_of_lt ht)
  rw [← hrest, List.map_append, List.take_left' (by simp)]

@[simp] theorem milestones_one_of_zero {y : ℕ → ℤ} {Λ : ℕ} (hy0 : y 0 = 0) (hΛ : 1 ≤ Λ) :
    milestones y Λ 1 = [] := by
  have hΛz : (1 : ℤ) ≤ (Λ : ℤ) := by exact_mod_cast hΛ
  rw [milestones_succ_of_not_le]
  · rfl
  · simp only [milestones, milestoneGrid_nil, hy0, zero_mul, sub_zero, abs_zero]
    omega

/-- **Core Epoch-Confinement & Exact-Milestone Identity (`Unit-Speed Walk Induction`):**
For every unit-speed walk `y` (`IsWalk y`, `y 0 = 0`) and `Λ ≥ 1`, at every step `t`,
`|y t - epochGrid y Λ t * Λ| < Λ`; moreover, whenever step `t` triggers a milestone,
`y t = epochGrid y Λ t * Λ` holds **with exact equality**. -/
theorem epochGrid_confines_and_exact {y : ℕ → ℤ} (hy : IsWalk y) (hy0 : y 0 = 0)
    {Λ : ℕ} (hΛ : 1 ≤ Λ) :
    ∀ t : ℕ, |y t - epochGrid y Λ t * (Λ : ℤ)| < (Λ : ℤ) ∧
      ((Λ : ℤ) ≤ |y t - milestoneGrid (milestones y Λ t) * (Λ : ℤ)| →
        y t = epochGrid y Λ t * (Λ : ℤ)) := by
  have hΛz : (1 : ℤ) ≤ (Λ : ℤ) := by exact_mod_cast hΛ
  intro t
  induction t with
  | zero =>
    unfold epochGrid
    rw [milestones_one_of_zero hy0 hΛ]
    simp only [milestones, milestoneGrid_nil, hy0, zero_mul, sub_zero, abs_zero]
    exact ⟨by omega, fun h => absurd h (by omega)⟩
  | succ s ih =>
    have hprev_lt : |y s - milestoneGrid (milestones y Λ (s + 1)) * (Λ : ℤ)| < (Λ : ℤ) := ih.1
    have hstep : |y (s + 1) - y s| ≤ 1 := hy s
    set g_prev := milestoneGrid (milestones y Λ (s + 1))
    have hle_Λ : |y (s + 1) - g_prev * (Λ : ℤ)| ≤ (Λ : ℤ) := by
      have htri : |y (s + 1) - g_prev * (Λ : ℤ)| ≤
          |y (s + 1) - y s| + |y s - g_prev * (Λ : ℤ)| := by
        simpa using abs_add_le (y (s + 1) - y s) (y s - g_prev * (Λ : ℤ))
      linarith
    by_cases htrig : (Λ : ℤ) ≤ |y (s + 1) - g_prev * (Λ : ℤ)|
    · have heq_abs : |y (s + 1) - g_prev * (Λ : ℤ)| = (Λ : ℤ) := le_antisymm hle_Λ htrig
      have hexact : y (s + 1) = epochGrid y Λ (s + 1) * (Λ : ℤ) := by
        unfold epochGrid
        rw [milestones_succ_of_le htrig, milestoneGrid_append_singleton]
        change y (s + 1) =
          (g_prev + if decide (0 < y (s + 1) - g_prev * (Λ : ℤ)) then 1 else -1) * (Λ : ℤ)
        rcases abs_cases (y (s + 1) - g_prev * (Λ : ℤ)) with ⟨habs, hnn⟩ | ⟨habs, hneg⟩
        · have hpos : 0 < y (s + 1) - g_prev * (Λ : ℤ) := by linarith
          rw [decide_eq_true hpos]
          simp only [↓reduceIte]
          linarith
        · have hn_pos : ¬ (0 < y (s + 1) - g_prev * (Λ : ℤ)) := by linarith
          rw [decide_eq_false hn_pos]
          simp only [Bool.false_eq_true, ↓reduceIte]
          linarith
      refine ⟨?_, fun _ => hexact⟩
      rw [hexact, sub_self, abs_zero]
      omega
    · have hlt_Λ : |y (s + 1) - g_prev * (Λ : ℤ)| < (Λ : ℤ) := lt_of_not_ge htrig
      refine ⟨?_, fun h => absurd h htrig⟩
      unfold epochGrid
      rw [milestones_succ_of_not_le htrig]
      exact hlt_Λ

/-- **Epoch Confinement Theorem:** for every `t < T`, `|y t - g_{epoch(t)} * Λ| < Λ`. -/
theorem abs_sub_skeletonGridAt_lt {y : ℕ → ℤ} (hy : IsWalk y) (hy0 : y 0 = 0)
    {T Λ : ℕ} (hΛ : 1 ≤ Λ) {t : ℕ} (ht : t < T) :
    |y t - skeletonGridAt (tapeSkeleton y T Λ) (epochIdx y Λ t) * (Λ : ℤ)| < (Λ : ℤ) := by
  rw [← epochGrid_eq_skeletonGridAt ht]
  exact (epochGrid_confines_and_exact hy hy0 hΛ t).1

private def lastMilestoneTime (ms : List (ℕ × Bool)) : ℕ :=
  match ms.getLast? with
  | none => 0
  | some x => x.1

private theorem milestones_spacing_aux {y : ℕ → ℤ} (hy : IsWalk y) (hy0 : y 0 = 0)
    {Λ : ℕ} (hΛ : 1 ≤ Λ) :
    ∀ n : ℕ,
      (milestones y Λ (n + 1)).length * Λ ≤ lastMilestoneTime (milestones y Λ (n + 1)) ∧
      lastMilestoneTime (milestones y Λ (n + 1)) < n + 1 ∧
      y (lastMilestoneTime (milestones y Λ (n + 1))) =
        milestoneGrid (milestones y Λ (n + 1)) * (Λ : ℤ) := by
  intro n
  induction n with
  | zero =>
    rw [milestones_one_of_zero hy0 hΛ]
    simp [lastMilestoneTime, hy0]
  | succ s ih =>
    obtain ⟨hlen_le, hlast_lt, hlast_eq⟩ := ih
    set ms := milestones y Λ (s + 1)
    set g_prev := milestoneGrid ms
    by_cases htrig : (Λ : ℤ) ≤ |y (s + 1) - g_prev * (Λ : ℤ)|
    · have hexact := (epochGrid_confines_and_exact hy hy0 hΛ (s + 1)).2 htrig
      have hms_next : milestones y Λ (s + 2) =
          ms ++ [(s + 1, decide (0 < y (s + 1) - g_prev * (Λ : ℤ)))] :=
        milestones_succ_of_le htrig
      rw [hms_next]
      have hlast_new : lastMilestoneTime (ms ++ [(s + 1, decide (0 < y (s + 1) - g_prev * (Λ : ℤ)))]) =
          s + 1 := by
        simp [lastMilestoneTime]
      rw [hlast_new, List.length_append, List.length_singleton]
      have hlip := hy.lip (le_of_lt hlast_lt)
      have habs_lip : |y (s + 1) - y (lastMilestoneTime ms)| ≤
          ((s + 1 - lastMilestoneTime ms : ℕ) : ℤ) :=
        abs_le.mpr ⟨by linarith [hlip.2], hlip.1⟩
      have hdist_ge : (Λ : ℤ) ≤ ((s + 1 - lastMilestoneTime ms : ℕ) : ℤ) := by
        have h1 : (Λ : ℤ) ≤ |y (s + 1) - y (lastMilestoneTime ms)| := by
          rwa [hlast_eq]
        exact h1.trans habs_lip
      have hdist_nat : Λ ≤ s + 1 - lastMilestoneTime ms := Nat.cast_le.mp hdist_ge
      refine ⟨?_, Nat.lt_succ_self (s + 1), ?_⟩
      · calc (ms.length + 1) * Λ = ms.length * Λ + Λ := by ring
          _ ≤ lastMilestoneTime ms + (s + 1 - lastMilestoneTime ms) := Nat.add_le_add hlen_le hdist_nat
          _ = s + 1 := by omega
      · unfold epochGrid at hexact
        rwa [hms_next] at hexact
    · have hms_next : milestones y Λ (s + 2) = ms :=
        milestones_succ_of_not_le htrig
      rw [hms_next]
      exact ⟨hlen_le, lt_trans hlast_lt (Nat.lt_succ_self (s + 1)), hlast_eq⟩

/-- **Milestone Count & Turn Bound (Lemma 6.3(a)).** Every unit-speed walk `y` (`IsWalk y`, `y 0 = 0`) over horizon `T` at threshold `Λ ≥ 1` has
`(tapeSkeleton y T Λ).length * Λ ≤ T` (hence `(tapeSkeleton y T Λ).length ≤ T / Λ` and
`macroTurns (tapeSkeleton y T Λ) ≤ T / Λ`). -/
theorem tapeSkeleton_length_mul_le {y : ℕ → ℤ} (hy : IsWalk y) (hy0 : y 0 = 0)
    (T : ℕ) {Λ : ℕ} (hΛ : 1 ≤ Λ) :
    (tapeSkeleton y T Λ).length * Λ ≤ T := by
  unfold tapeSkeleton
  rw [List.length_map]
  cases T with
  | zero => simp [milestones]
  | succ n =>
    obtain ⟨hlen, hlt, _⟩ := milestones_spacing_aux hy hy0 hΛ n
    exact hlen.trans (le_of_lt hlt)

/-- Exact grid value and strict monotonicity of `milestoneTimes y T Λ` (`for T ≥ 1`). -/
theorem milestoneTimes_properties {y : ℕ → ℤ} (hy : IsWalk y) (hy0 : y 0 = 0)
    {T Λ : ℕ} (hT : 1 ≤ T) (hΛ : 1 ≤ Λ) :
    (milestoneTimes y T Λ).length = (tapeSkeleton y T Λ).length + 1 ∧
    List.Pairwise (· < ·) (milestoneTimes y T Λ) ∧
    (∀ τ ∈ milestoneTimes y T Λ, τ < T) ∧
    (∀ (i : ℕ) (hi : i < (milestoneTimes y T Λ).length),
      y ((milestoneTimes y T Λ)[i]) =
        skeletonGridAt (tapeSkeleton y T Λ) i * (Λ : ℤ)) := by
  have haux : ∀ n : ℕ,
      List.Pairwise (· < ·) (0 :: (milestones y Λ (n + 1)).map Prod.fst) ∧
      (∀ τ ∈ (0 :: (milestones y Λ (n + 1)).map Prod.fst), τ < n + 1) ∧
      (∀ (i : ℕ) (hi : i < (0 :: (milestones y Λ (n + 1)).map Prod.fst).length),
        y ((0 :: (milestones y Λ (n + 1)).map Prod.fst)[i]) =
          skeletonGridAt ((milestones y Λ (n + 1)).map Prod.snd) i * (Λ : ℤ)) := by
    intro n
    induction n with
    | zero =>
      rw [milestones_one_of_zero hy0 hΛ]
      refine ⟨by simp, by simp, ?_⟩
      intro i hi
      simp only [List.map_nil, List.length_singleton] at hi
      have hi0 : i = 0 := by omega
      subst hi0
      simp [hy0]
    | succ s ih =>
      obtain ⟨hpw, hall_lt, hgrid⟩ := ih
      set ms := milestones y Λ (s + 1)
      set g_prev := milestoneGrid ms
      by_cases htrig : (Λ : ℤ) ≤ |y (s + 1) - g_prev * (Λ : ℤ)|
      · have hexact := (epochGrid_confines_and_exact hy hy0 hΛ (s + 1)).2 htrig
        have hms_next : milestones y Λ (s + 2) =
            ms ++ [(s + 1, decide (0 < y (s + 1) - g_prev * (Λ : ℤ)))] :=
          milestones_succ_of_le htrig
        rw [hms_next, List.map_append, List.map_singleton, ← List.cons_append]
        have hpw' : List.Pairwise (· < ·) ((0 :: ms.map Prod.fst) ++ [s + 1]) := by
          rw [List.pairwise_append]
          refine ⟨hpw, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
          simp only [List.mem_singleton] at hb
          subst hb
          exact hall_lt a ha
        have hall_lt' : ∀ τ ∈ (0 :: ms.map Prod.fst) ++ [s + 1], τ < s + 2 := by
          intro τ hτ
          rcases List.mem_append.mp hτ with hleft | hright
          · exact lt_trans (hall_lt τ hleft) (Nat.lt_succ_self (s + 1))
          · simp only [List.mem_singleton] at hright
            omega
        refine ⟨hpw', hall_lt', ?_⟩
        intro i hi
        rw [List.map_append, List.map_singleton]
        simp only [List.length_append, List.length_cons, List.length_map] at hi
        rcases lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi_lt | rfl
        · have hi_old : i < (0 :: ms.map Prod.fst).length := by simpa using hi_lt
          rw [List.getElem_append_left hi_old]
          have htake : ((ms.map Prod.snd ++
              [decide (0 < y (s + 1) - g_prev * (Λ : ℤ))]).take i) = (ms.map Prod.snd).take i := by
            apply List.take_append_of_le_length
            simp only [List.length_cons, List.length_map] at hi_old ⊢
            omega
          unfold skeletonGridAt
          rw [htake]
          exact hgrid i hi_old
        · have hget : ((0 :: ms.map Prod.fst) ++ [s + 1])[(0 :: ms.map Prod.fst).length] = s + 1 := by
            simp
          simp only [List.length_cons, List.length_map] at hget
          rw [hget]
          unfold epochGrid at hexact
          rw [hms_next, milestoneGrid_eq_skeletonGridEnd_map, List.map_append, List.map_singleton] at hexact
          unfold skeletonGridAt
          have htake_all : ((ms.map Prod.snd ++
              [decide (0 < y (s + 1) - g_prev * (Λ : ℤ))]).take (ms.length + 1)) =
              ms.map Prod.snd ++ [decide (0 < y (s + 1) - g_prev * (Λ : ℤ))] := by
            apply List.take_of_length_le
            simp
          rw [htake_all]
          exact hexact
      · have hms_next : milestones y Λ (s + 2) = ms :=
          milestones_succ_of_not_le htrig
        rw [hms_next]
        exact ⟨hpw, fun τ hτ => lt_trans (hall_lt τ hτ) (Nat.lt_succ_self (s + 1)), hgrid⟩
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : T ≠ 0)
  obtain ⟨hpw, hall_lt, hgrid⟩ := haux n
  exact ⟨by simp [milestoneTimes, tapeSkeleton], hpw, hall_lt, hgrid⟩

end GreedyMilestoneSkeleton

/-! ## §2. Explicit Finiteness of `k`-Tape Macroscopic Skeleton Types (Lemma 6.3(b)) -/

section FiniteSkeletonTypes

/-- Explicit `Finset` of all `Bool`-lists of length `≤ M_max`. -/
def boundedBoolLists : ℕ → Finset (List Bool)
  | 0 => {[]}
  | n + 1 =>
    insert []
      ((boundedBoolLists n).image (List.cons true) ∪
        (boundedBoolLists n).image (List.cons false))

@[simp] theorem mem_boundedBoolLists {M_max : ℕ} {w : List Bool} :
    w ∈ boundedBoolLists M_max ↔ w.length ≤ M_max := by
  induction M_max generalizing w with
  | zero =>
    cases w <;> simp [boundedBoolLists]
  | succ n ih =>
    cases w with
    | nil => simp [boundedBoolLists]
    | cons b rest =>
      simp only [boundedBoolLists, mem_insert, reduceCtorEq, false_or, mem_union, mem_image,
        List.cons.injEq, List.length_cons, Nat.add_le_add_iff_right]
      cases b
      · constructor
        · rintro (⟨_, _, ⟨h1, _⟩⟩ | ⟨w', hw', ⟨_, rfl⟩⟩)
          · cases h1
          · exact ih.mp hw'
        · intro hlen
          exact Or.inr ⟨rest, ih.mpr hlen, rfl, rfl⟩
      · constructor
        · rintro (⟨w', hw', ⟨_, rfl⟩⟩ | ⟨_, _, ⟨h1, _⟩⟩)
          · exact ih.mp hw'
          · cases h1
        · intro hlen
          exact Or.inl ⟨rest, ih.mpr hlen, rfl, rfl⟩

/-- Exact cardinality `(boundedBoolLists M_max).card = 2 ^ (M_max + 1) - 1`. -/
theorem card_boundedBoolLists (M_max : ℕ) :
    (boundedBoolLists M_max).card = 2 ^ (M_max + 1) - 1 := by
  induction M_max with
  | zero => rfl
  | succ n ih =>
    unfold boundedBoolLists
    set S_t := (boundedBoolLists n).image (List.cons true)
    set S_f := (boundedBoolLists n).image (List.cons false)
    have hcard_t : S_t.card = (boundedBoolLists n).card :=
      card_image_of_injective _ (fun _ _ h => (List.cons.inj h).2)
    have hcard_f : S_f.card = (boundedBoolLists n).card :=
      card_image_of_injective _ (fun _ _ h => (List.cons.inj h).2)
    have hdisj : Disjoint S_t S_f := by
      rw [disjoint_left]
      intro x hxt hxf
      obtain ⟨_, _, rfl⟩ := mem_image.mp hxt
      obtain ⟨_, _, heq⟩ := mem_image.mp hxf
      cases heq
    have hnil_not : ([] : List Bool) ∉ S_t ∪ S_f := by
      intro hmem
      rcases mem_union.mp hmem with hxt | hxf
      · obtain ⟨_, _, heq⟩ := mem_image.mp hxt; cases heq
      · obtain ⟨_, _, heq⟩ := mem_image.mp hxf; cases heq
    rw [card_insert_of_notMem hnil_not, card_union_of_disjoint hdisj, hcard_t, hcard_f, ih]
    have hpow : 1 ≤ 2 ^ (n + 1) := Nat.one_le_pow _ _ (by decide)
    have hpow2 : 2 ^ (n + 2) = 2 * 2 ^ (n + 1) := by ring
    omega

/-- Explicit finite set of all `k`-tape macroscopic skeleton tuples of per-tape length `≤ M_max`
(`completely independent of dimension d!`). -/
def BoundedSkeletonTuple (k M_max : ℕ) : Finset (Fin k → List Bool) :=
  Fintype.piFinset fun _ : Fin k => boundedBoolLists M_max

@[simp] theorem mem_boundedSkeletonTuple {k M_max : ℕ} {skTuple : Fin k → List Bool} :
    skTuple ∈ BoundedSkeletonTuple k M_max ↔ ∀ j : Fin k, (skTuple j).length ≤ M_max := by
  simp [BoundedSkeletonTuple, Fintype.mem_piFinset]

/-- Exact cardinality `(BoundedSkeletonTuple k M_max).card = (2 ^ (M_max + 1) - 1) ^ k`. -/
theorem card_boundedSkeletonTuple (k M_max : ℕ) :
    (BoundedSkeletonTuple k M_max).card = (2 ^ (M_max + 1) - 1) ^ k := by
  simp [BoundedSkeletonTuple, Fintype.card_piFinset, card_boundedBoolLists]

/-- Full `k`-tape skeleton tuple of a trace `τ₀ : Trace k` over horizon `T` at scale `Λ`. -/
def traceSkeletonTuple {k : ℕ} (τ₀ : Trace k) (T Λ : ℕ) : Fin k → List Bool :=
  fun j => tapeSkeleton (τ₀.work j) T Λ

/-- `(C, θ)`-only milestone/turn cap `M_max(C, θ) = ⌊16 * C / θ⌋₊` (`independent of d`). -/
noncomputable def skeletonMaxLen (C θ : ℝ) : ℕ :=
  ⌊16 * C / θ⌋₊

/-- **Linear-Time Trace Skeleton Finiteness Theorem (Lemma 6.3(b)).** For every `k`-tape trace `τ₀` with `(T : ℝ) ≤ C * (L + 1)` (`L = d * d * b`, `d, b ≥ 1`, `C ≥ 1`)
and every macroscopic scale `θ > 0` (`with d ≥ ⌈8 / θ⌉₊`), setting `Λ := ⌊(θ / 4) * L⌋₊` gives:
1. `1 ≤ Λ`,
2. every tape `j : Fin k` has `macroTurns (traceSkeletonTuple τ₀ T Λ j) ≤ skeletonMaxLen C θ`, and
3. `traceSkeletonTuple τ₀ T Λ ∈ BoundedSkeletonTuple k (skeletonMaxLen C θ)` (`finitely many types
   bounded purely by (k, C, θ) and independent of d!`). -/
theorem traceSkeletonTuple_mem_boundedSkeletonTuple {k T d b : ℕ} {C θ : ℝ} (τ₀ : Trace k)
    (hd1 : 1 ≤ d) (hb1 : 1 ≤ b) (hC : 1 ≤ C) (hθ : 0 < θ)
    (hd_θ : ⌈8 / θ⌉₊ ≤ d)
    (hT : (T : ℝ) ≤ C * (((d * d * b : ℕ) : ℝ) + 1)) :
    let L := d * d * b
    let Λ := ⌊(θ / 4) * (L : ℝ)⌋₊
    1 ≤ Λ ∧
      (∀ j : Fin k, macroTurns (traceSkeletonTuple τ₀ T Λ j) ≤ skeletonMaxLen C θ) ∧
      traceSkeletonTuple τ₀ T Λ ∈ BoundedSkeletonTuple k (skeletonMaxLen C θ) := by
  intro L Λ
  have hL_ge_d : (d : ℝ) ≤ (L : ℝ) := by
    have : d ≤ d * d * b := by
      calc d = d * 1 * 1 := by ring
        _ ≤ d * d * b := Nat.mul_le_mul (Nat.mul_le_mul le_rfl hd1) hb1
    exact_mod_cast this
  have h8_le_θd : 8 ≤ θ * (d : ℝ) := by
    have hge : 8 / θ ≤ (d : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hd_θ)
    have hmul := (div_le_iff₀ hθ).mp hge
    linarith
  have h8_le_θL : 8 ≤ θ * (L : ℝ) := by
    calc (8 : ℝ) ≤ θ * (d : ℝ) := h8_le_θd
      _ ≤ θ * (L : ℝ) := mul_le_mul_of_nonneg_left hL_ge_d hθ.le
  have h2_le_q : (2 : ℝ) ≤ (θ / 4) * (L : ℝ) := by linarith
  have hΛ_ge_2 : 2 ≤ Λ := Nat.le_floor h2_le_q
  have hΛ_pos : 1 ≤ Λ := by omega
  have hΛ_gt : (θ / 4) * (L : ℝ) - 1 < (Λ : ℝ) := by
    have := Nat.lt_floor_add_one ((θ / 4) * (L : ℝ))
    linarith
  have hΛ_ge_θ8 : (θ / 8) * (L : ℝ) ≤ (Λ : ℝ) := by linarith
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by
    have : 1 ≤ d := hd1
    have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
    linarith
  have hT_2CL : (T : ℝ) ≤ 2 * C * (L : ℝ) := by
    have hCL : C ≤ C * (L : ℝ) := by simpa using mul_le_mul_of_nonneg_left hL1 (by linarith)
    change (T : ℝ) ≤ 2 * C * (L : ℝ)
    linarith
  have hlen_le : ∀ j : Fin k, (traceSkeletonTuple τ₀ T Λ j).length ≤ skeletonMaxLen C θ := by
    intro j
    have hmul_nat := tapeSkeleton_length_mul_le (τ₀.work_isWalk j) (τ₀.work_zero j) T hΛ_pos
    have hmul_r : ((traceSkeletonTuple τ₀ T Λ j).length : ℝ) * (Λ : ℝ) ≤ (T : ℝ) := by
      unfold traceSkeletonTuple
      exact_mod_cast hmul_nat
    have hprod_pos : (0 : ℝ) < (θ / 8) * (L : ℝ) := by positivity
    have hchain : ((traceSkeletonTuple τ₀ T Λ j).length : ℝ) * ((θ / 8) * (L : ℝ)) ≤
        (16 * C / θ) * ((θ / 8) * (L : ℝ)) := by
      calc ((traceSkeletonTuple τ₀ T Λ j).length : ℝ) * ((θ / 8) * (L : ℝ))
          ≤ ((traceSkeletonTuple τ₀ T Λ j).length : ℝ) * (Λ : ℝ) :=
            mul_le_mul_of_nonneg_left hΛ_ge_θ8 (Nat.cast_nonneg _)
        _ ≤ (T : ℝ) := hmul_r
        _ ≤ 2 * C * (L : ℝ) := hT_2CL
        _ = (16 * C / θ) * ((θ / 8) * (L : ℝ)) := by field_simp; ring
    have hle_real : ((traceSkeletonTuple τ₀ T Λ j).length : ℝ) ≤ 16 * C / θ :=
      le_of_mul_le_mul_right hchain hprod_pos
    exact Nat.le_floor hle_real
  refine ⟨hΛ_pos, fun j => (macroTurns_le_length _).trans (hlen_le j), ?_⟩
  exact mem_boundedSkeletonTuple.mpr hlen_le

end FiniteSkeletonTypes

/-! ## §3. Opposite-Polarity Law, 3-Leg Overlapping Zigzag, & Crossing-Capable Skeletons (Lemma 6.1 and Proposition 6.5) -/

section CrossingCapableCharacterization

open scoped Classical

/-- Lower endpoints of `> 2H` revisit hops on a single walk `y` that cross another `> 2H` revisit hop on `y`. -/
noncomputable def tapeCrossingLowers (y : ℕ → ℤ) (T H : ℕ) : Finset ℕ :=
  (range T).filter fun v =>
    ∃ u : ℕ, IsHop y T v u ∧ HasHopExcursionGTAt y (2 * H) v u ∧
      ∃ p' u' : ℕ, IsHop y T p' u' ∧ HasHopExcursionGTAt y (2 * H) p' u' ∧ HopsCross v u p' u'

theorem crossingLowerEtaSteps_eq_biUnion_tapeCrossingLowers {k : ℕ} (τ₀ : Trace k) (T H : ℕ) :
    crossingLowerEtaSteps τ₀ T H 1 T =
      (univ : Finset (Fin k)).biUnion fun j => tapeCrossingLowers (τ₀.work j) T H := by
  ext v
  simp only [crossingLowerEtaSteps, tapeCrossingLowers, mem_filter, mem_range, mem_biUnion,
    mem_univ, true_and, Nat.div_one]
  constructor
  · rintro ⟨hvT, j, u, hb, p', u', hb', hcr⟩
    exact ⟨j, hvT, u, hb.1, hb.2.1, p', u', hb'.1, hb'.2.1, hcr⟩
  · rintro ⟨j, hvT, u, hhop, hexc, p', u', hhop', hexc', hcr⟩
    exact ⟨hvT, j, u, ⟨hhop, hexc, hop_excursion_le_T τ₀ j hhop⟩,
      p', u', ⟨hhop', hexc', hop_excursion_le_T τ₀ j hhop'⟩, hcr⟩

/-- Discrete intermediate-value theorem on unit-speed walks (`IsWalk y`). -/
theorem isWalk_ivt {y : ℕ → ℤ} (hy : IsWalk y) {a b : ℕ} (hab : a ≤ b) {z : ℤ}
    (hz : (y a ≤ z ∧ z ≤ y b) ∨ (y b ≤ z ∧ z ≤ y a)) :
    ∃ c ∈ Icc a b, y c = z := by
  induction b with
  | zero =>
    have ha0 : a = 0 := Nat.eq_zero_of_le_zero hab
    subst ha0
    refine ⟨0, mem_Icc.mpr ⟨le_rfl, le_rfl⟩, ?_⟩
    rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  | succ b ih =>
    rcases eq_or_lt_of_le hab with rfl | hlt
    · refine ⟨b + 1, mem_Icc.mpr ⟨le_rfl, le_rfl⟩, ?_⟩
      rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    · have hab' : a ≤ b := Nat.le_of_lt_succ hlt
      have hstep := abs_le.mp (hy b)
      by_cases hyb1 : y (b + 1) = z
      · exact ⟨b + 1, mem_Icc.mpr ⟨hab, le_rfl⟩, hyb1⟩
      · have hz' : (y a ≤ z ∧ z ≤ y b) ∨ (y b ≤ z ∧ z ≤ y a) := by
          rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inl ⟨h1, by omega⟩
          · exact Or.inr ⟨by omega, h2⟩
        obtain ⟨c, hc, hyc⟩ := ih hab' hz'
        obtain ⟨hac, hcb⟩ := mem_Icc.mp hc
        exact ⟨c, mem_Icc.mpr ⟨hac, Nat.le_succ_of_le hcb⟩, hyc⟩

/-- **No-Sign-Change Lemma on `IsHop` (`Unit-Speed Walk`):**
An `IsHop y T p u` on a unit-speed walk maintains strict sign on all of `Ioo p u` relative to `y p`. -/
theorem isHop_same_sign_of_isWalk {y : ℕ → ℤ} (hy : IsWalk y) {T p u t₁ t₂ : ℕ}
    (hhop : IsHop y T p u) (ht₁ : t₁ ∈ Ioo p u) (ht₂ : t₂ ∈ Ioo p u)
    (hpos : y p < y t₁) : y p < y t₂ := by
  by_contra hle
  push Not at hle
  have hne₂ : y t₂ ≠ y p := hhop.2.2.2 t₂ ht₂
  have hneg : y t₂ < y p := lt_of_le_of_ne hle hne₂
  obtain ⟨hp₁, h₁u⟩ := mem_Ioo.mp ht₁
  obtain ⟨hp₂, h₂u⟩ := mem_Ioo.mp ht₂
  rcases le_total t₁ t₂ with h12 | h21
  · obtain ⟨c, hc, hyc⟩ := isWalk_ivt hy h12 (Or.inr ⟨le_of_lt hneg, le_of_lt hpos⟩)
    obtain ⟨h1c, hc2⟩ := mem_Icc.mp hc
    exact hhop.2.2.2 c (mem_Ioo.mpr ⟨lt_of_lt_of_le hp₁ h1c, lt_of_le_of_lt hc2 h₂u⟩) hyc
  · obtain ⟨c, hc, hyc⟩ := isWalk_ivt hy h21 (Or.inl ⟨le_of_lt hneg, le_of_lt hpos⟩)
    obtain ⟨h2c, hc1⟩ := mem_Icc.mp hc
    exact hhop.2.2.2 c (mem_Ioo.mpr ⟨lt_of_lt_of_le hp₂ h2c, lt_of_le_of_lt hc1 h₁u⟩) hyc

/-- **Opposite-Polarity Law for Crossing Hops (Lemma 6.1(a)):**
Whenever two revisit hops `(v₁, u₁)` and `(v₂, u₂)` cross (`v₁ < v₂ < u₁ < u₂`) on a unit-speed
walk `y`, they sit at distinct levels (`y v₁ ≠ y v₂`) and have strictly **opposite** excursion
polarities (`one is purely upper, the other is purely lower`). -/
theorem crossing_isHop_opposite_polarity {y : ℕ → ℤ} (hy : IsWalk y) {T v₁ u₁ v₂ u₂ : ℕ}
    (h₁ : IsHop y T v₁ u₁) (h₂ : IsHop y T v₂ u₂)
    (hv₁₂ : v₁ < v₂) (hv₂u₁ : v₂ < u₁) (hu₁₂ : u₁ < u₂) :
    (y v₁ < y v₂ ∧ (∀ t ∈ Ioo v₁ u₁, y v₁ < y t) ∧ (∀ t ∈ Ioo v₂ u₂, y t < y v₂)) ∨
    (y v₂ < y v₁ ∧ (∀ t ∈ Ioo v₁ u₁, y t < y v₁) ∧ (∀ t ∈ Ioo v₂ u₂, y v₂ < y t)) := by
  have hv₂_in : v₂ ∈ Ioo v₁ u₁ := mem_Ioo.mpr ⟨hv₁₂, hv₂u₁⟩
  have hu₁_in : u₁ ∈ Ioo v₂ u₂ := mem_Ioo.mpr ⟨hv₂u₁, hu₁₂⟩
  have hne : y v₂ ≠ y v₁ := h₁.2.2.2 v₂ hv₂_in
  have hyu₁ : y u₁ = y v₁ := h₁.2.2.1
  have hy_neg : IsWalk (fun s => -y s) := by
    intro s
    have h := abs_le.mp (hy s)
    change |-y (s + 1) - -y s| ≤ 1
    rw [abs_le]; omega
  have h₁_neg : IsHop (fun s => -y s) T v₁ u₁ := by
    unfold IsHop; simp only [ne_eq, neg_inj]; exact h₁
  have h₂_neg : IsHop (fun s => -y s) T v₂ u₂ := by
    unfold IsHop; simp only [ne_eq, neg_inj]; exact h₂
  rcases lt_or_gt_of_ne hne.symm with hlt | hgt
  · refine Or.inl ⟨hlt, fun t ht => isHop_same_sign_of_isWalk hy h₁ hv₂_in ht hlt, fun t ht => ?_⟩
    have hneg_lt : -y v₂ < -y u₁ := by omega
    have hres := isHop_same_sign_of_isWalk hy_neg h₂_neg hu₁_in ht hneg_lt
    omega
  · refine Or.inr ⟨hgt, fun t ht => ?_, fun t ht => ?_⟩
    · have hneg_lt : -y v₁ < -y v₂ := by omega
      have hres := isHop_same_sign_of_isWalk hy_neg h₁_neg hv₂_in ht hneg_lt
      omega
    · have hu₁_gt : y v₂ < y u₁ := by omega
      exact isHop_same_sign_of_isWalk hy h₂ hu₁_in ht hu₁_gt

/-- **Raw-Walk 4-Timestamp Overlapping Zigzag Necessary Lemma (Lemma 6.1(b)):**
Any walk `y` (`IsWalk y`) admitting crossing `> 2H` revisit hops contains `s₀ < s₁ < s₂ < s₃ < T`
and polarity `ε : Bool` (`h t := if ε then y t else -y t`) with three alternating `≥ 2H + 1` jumps
and positive spatial overlap `1 ≤ min (h s₁) (h s₃) - max (h s₀) (h s₂)`. -/
theorem exists_crossingZigzag_of_crossingHopsGT2H {y : ℕ → ℤ} (hy : IsWalk y) {T H v₁ u₁ v₂ u₂ : ℕ}
    (h₁ : IsHop y T v₁ u₁) (hexc₁ : HasHopExcursionGTAt y (2 * H) v₁ u₁)
    (h₂ : IsHop y T v₂ u₂) (hexc₂ : HasHopExcursionGTAt y (2 * H) v₂ u₂)
    (hcr : HopsCross v₁ u₁ v₂ u₂) :
    ∃ (ε : Bool) (s₀ s₁ s₂ s₃ : ℕ),
      s₀ < s₁ ∧ s₁ < s₂ ∧ s₂ < s₃ ∧ s₃ < T ∧
      let h : ℕ → ℤ := fun t => if ε then y t else -y t
      2 * (H : ℤ) + 1 ≤ h s₁ - h s₀ ∧
      2 * (H : ℤ) + 1 ≤ h s₁ - h s₂ ∧
      2 * (H : ℤ) + 1 ≤ h s₃ - h s₂ ∧
      1 ≤ min (h s₁) (h s₃) - max (h s₀) (h s₂) := by
  have core : ∀ {w : ℕ → ℤ}, IsWalk w → ∀ {a₁ b₁ a₂ b₂ : ℕ},
      IsHop w T a₁ b₁ → HasHopExcursionGTAt w (2 * H) a₁ b₁ →
      IsHop w T a₂ b₂ → HasHopExcursionGTAt w (2 * H) a₂ b₂ →
      a₁ < a₂ → a₂ < b₁ → b₁ < b₂ → w a₁ < w a₂ →
      (∀ t ∈ Ioo a₁ b₁, w a₁ < w t) → (∀ t ∈ Ioo a₂ b₂, w t < w a₂) →
      ∃ s₀ s₁ s₂ s₃ : ℕ,
        s₀ < s₁ ∧ s₁ < s₂ ∧ s₂ < s₃ ∧ s₃ < T ∧
        2 * (H : ℤ) + 1 ≤ w s₁ - w s₀ ∧
        2 * (H : ℤ) + 1 ≤ w s₁ - w s₂ ∧
        2 * (H : ℤ) + 1 ≤ w s₃ - w s₂ ∧
        1 ≤ min (w s₁) (w s₃) - max (w s₀) (w s₂) := by
    intro w _ a₁ b₁ a₂ b₂ hh₁ hx₁ hh₂ hx₂ ha₁₂ ha₂b₁ hb₁₂ hwa hup₁ hlow₂
    have hwb₁ : w b₁ = w a₁ := hh₁.2.2.1
    have hwb₂ : w b₂ = w a₂ := hh₂.2.2.1
    have hb₂T : b₂ < T := hh₂.2.1
    rcases le_or_gt (2 * (H : ℤ) + 1) (w a₂ - w a₁) with hbig | hsmall
    · refine ⟨a₁, a₂, b₁, b₂, ha₁₂, ha₂b₁, hb₁₂, hb₂T, hbig, ?_, ?_, ?_⟩
      · omega
      · omega
      · have hmin : min (w a₂) (w b₂) = w a₂ := by omega
        have hmax : max (w a₁) (w b₁) = w a₁ := by omega
        omega
    · obtain ⟨t₁, ht₁_in, hgt₁⟩ := hx₁
      obtain ⟨t₂, ht₂_in, hgt₂⟩ := hx₂
      have hpos₁ : w a₁ < w t₁ := hup₁ t₁ ht₁_in
      have hneg₂ : w t₂ < w a₂ := hlow₂ t₂ ht₂_in
      have ht₁_val : w a₁ + 2 * (H : ℤ) + 1 ≤ w t₁ := by
        rw [abs_of_pos (by omega)] at hgt₁; omega
      have ht₂_val : w t₂ ≤ w a₂ - 2 * (H : ℤ) - 1 := by
        rw [abs_of_neg (by omega)] at hgt₂; omega
      obtain ⟨ha₁t₁, ht₁b₁⟩ := mem_Ioo.mp ht₁_in
      obtain ⟨ha₂t₂, ht₂b₂⟩ := mem_Ioo.mp ht₂_in
      have ht₁_lt_a₂ : t₁ < a₂ := by
        by_contra hge
        push Not at hge
        rcases eq_or_lt_of_le hge with rfl | ha₂_lt_t₁
        · omega
        · have := hlow₂ t₁ (mem_Ioo.mpr ⟨ha₂_lt_t₁, lt_trans ht₁b₁ hb₁₂⟩)
          omega
      have hb₁_lt_t₂ : b₁ < t₂ := by
        by_contra hle
        push Not at hle
        rcases eq_or_lt_of_le hle with rfl | ht₂_lt_b₁
        · omega
        · have := hup₁ t₂ (mem_Ioo.mpr ⟨lt_trans ha₁₂ ha₂t₂, ht₂_lt_b₁⟩)
          omega
      refine ⟨a₁, t₁, t₂, b₂, ha₁t₁, lt_trans ht₁_lt_a₂ ha₂t₂, ht₂b₂, hb₂T,
        by omega, by omega, by omega, ?_⟩
      have hmin : min (w t₁) (w b₂) = w a₂ := by omega
      have hmax : max (w a₁) (w t₂) = w a₁ := by omega
      omega
  have hy_neg : IsWalk (fun t => -y t) := by
    intro t; have h := abs_le.mp (hy t); change |-y (t + 1) - -y t| ≤ 1; rw [abs_le]; omega
  have to_neg : ∀ {p u : ℕ}, IsHop y T p u → HasHopExcursionGTAt y (2 * H) p u →
      IsHop (fun t => -y t) T p u ∧ HasHopExcursionGTAt (fun t => -y t) (2 * H) p u := by
    intro p u hh hx
    refine ⟨by unfold IsHop; simp only [ne_eq, neg_inj]; exact hh, ?_⟩
    obtain ⟨t, ht, hgt⟩ := hx
    exact ⟨t, ht, by rw [show -y t - -y p = -(y t - y p) by ring, abs_neg]; exact hgt⟩
  rcases hcr with ⟨hv₁₂, hv₂u₁, hu₁₂⟩ | ⟨hv₂₁, hv₁u₂, hu₂₁⟩
  · rcases crossing_isHop_opposite_polarity hy h₁ h₂ hv₁₂ hv₂u₁ hu₁₂ with
      ⟨hlt, hup, hlow⟩ | ⟨hgt, hlow, hup⟩
    · obtain ⟨s₀, s₁, s₂, s₃, hs⟩ := core hy h₁ hexc₁ h₂ hexc₂ hv₁₂ hv₂u₁ hu₁₂ hlt hup hlow
      exact ⟨true, s₀, s₁, s₂, s₃, by simpa using hs⟩
    · obtain ⟨h₁n, hx₁n⟩ := to_neg h₁ hexc₁
      obtain ⟨h₂n, hx₂n⟩ := to_neg h₂ hexc₂
      obtain ⟨s₀, s₁, s₂, s₃, hs⟩ := core hy_neg h₁n hx₁n h₂n hx₂n hv₁₂ hv₂u₁ hu₁₂
        (by omega) (fun t ht => by have := hlow t ht; omega) (fun t ht => by have := hup t ht; omega)
      exact ⟨false, s₀, s₁, s₂, s₃, by simpa using hs⟩
  · rcases crossing_isHop_opposite_polarity hy h₂ h₁ hv₂₁ hv₁u₂ hu₂₁ with
      ⟨hlt, hup, hlow⟩ | ⟨hgt, hlow, hup⟩
    · obtain ⟨s₀, s₁, s₂, s₃, hs⟩ := core hy h₂ hexc₂ h₁ hexc₁ hv₂₁ hv₁u₂ hu₂₁ hlt hup hlow
      exact ⟨true, s₀, s₁, s₂, s₃, by simpa using hs⟩
    · obtain ⟨h₁n, hx₁n⟩ := to_neg h₁ hexc₁
      obtain ⟨h₂n, hx₂n⟩ := to_neg h₂ hexc₂
      obtain ⟨s₀, s₁, s₂, s₃, hs⟩ := core hy_neg h₂n hx₂n h₁n hx₁n hv₂₁ hv₁u₂ hu₂₁
        (by omega) (fun t ht => by have := hlow t ht; omega) (fun t ht => by have := hup t ht; omega)
      exact ⟨false, s₀, s₁, s₂, s₃, by simpa using hs⟩

/-- Valley-to-hop lemma (`EnvelopeCrux.exists_hop_gt_of_valley`) additionally exposing `y p' = R`. -/
theorem exists_hop_gt_of_valley_eq {y : ℕ → ℤ} (hy : IsWalk y) {T s₁ m s₂ H : ℕ} {R : ℤ}
    (hs₁m : s₁ < m) (hms₂ : m < s₂) (hs₂T : s₂ < T)
    (hys₁ : R ≤ y s₁) (hym : y m + (H : ℤ) < R) (hys₂ : R ≤ y s₂) :
    ∃ p' u' : ℕ, s₁ ≤ p' ∧ p' < m ∧ m < u' ∧ u' ≤ s₂ ∧
      y p' = R ∧ y u' = R ∧ IsHop y T p' u' ∧ HasHopExcursionGTAt y H p' u' := by
  set S_left := (Ico s₁ m).filter fun t => R ≤ y t
  set S_right := (Ioc m s₂).filter fun t => R ≤ y t
  have hne_l : S_left.Nonempty := ⟨s₁, mem_filter.mpr ⟨mem_Ico.mpr ⟨le_rfl, hs₁m⟩, hys₁⟩⟩
  have hne_r : S_right.Nonempty := ⟨s₂, mem_filter.mpr ⟨mem_Ioc.mpr ⟨hms₂, le_rfl⟩, hys₂⟩⟩
  let p' := S_left.max' hne_l
  let u' := S_right.min' hne_r
  have hp'_mem := mem_filter.mp (S_left.max'_mem hne_l)
  have hu'_mem := mem_filter.mp (S_right.min'_mem hne_r)
  obtain ⟨hs₁p', hp'm⟩ := mem_Ico.mp hp'_mem.1
  obtain ⟨hmu', hu's₂⟩ := mem_Ioc.mp hu'_mem.1
  have hleft_lt : ∀ t, p' < t → t ≤ m → y t < R := by
    intro t hpt htm
    rcases eq_or_lt_of_le htm with rfl | ht_lt_m
    · omega
    · by_contra hge; push Not at hge
      have := S_left.le_max' t (mem_filter.mpr ⟨mem_Ico.mpr ⟨hs₁p'.trans hpt.le, ht_lt_m⟩, hge⟩)
      omega
  have hright_lt : ∀ t, m ≤ t → t < u' → y t < R := by
    intro t hmt htu
    rcases eq_or_lt_of_le hmt with rfl | hm_lt_t
    · omega
    · by_contra hge; push Not at hge
      have := S_right.min'_le t (mem_filter.mpr ⟨mem_Ioc.mpr ⟨hm_lt_t, htu.le.trans hu's₂⟩, hge⟩)
      omega
  have hp1_lt : y (p' + 1) < R := hleft_lt (p' + 1) (Nat.lt_succ_self p') hp'm
  have hu1_lt : y (u' - 1) < R := hright_lt (u' - 1) (by omega) (by omega)
  have hyp_step := abs_le.mp (hy p')
  have hyu_step := abs_le.mp (hy (u' - 1))
  rw [show u' - 1 + 1 = u' by omega] at hyu_step
  have hyp'_eq : y p' = R := by linarith [hp'_mem.2]
  have hyu'_eq : y u' = R := by linarith [hu'_mem.2]
  have hhop : IsHop y T p' u' := by
    refine ⟨by omega, lt_of_le_of_lt hu's₂ hs₂T, hyu'_eq.trans hyp'_eq.symm, fun t ht => ?_⟩
    obtain ⟨hpt, htu⟩ := mem_Ioo.mp ht
    rcases le_or_gt t m with htm | hmt
    · have := hleft_lt t hpt htm; omega
    · have := hright_lt t hmt.le htu; omega
  have hexc : HasHopExcursionGTAt y H p' u' := by
    refine ⟨m, mem_Ioo.mpr ⟨hp'm, hmu'⟩, ?_⟩
    rw [abs_of_neg (by omega)]; omega
  exact ⟨p', u', hs₁p', hp'm, hmu', hu's₂, hyp'_eq, hyu'_eq, hhop, hexc⟩

/-- **Detour-Proof Macroscopic-Overlap Converse (Lemma 6.1(c)):**
On **every** unit-speed walk `y` (`IsWalk y`), whenever `s₀ < s₁ < s₂ < s₃ < T` and `ε : Bool`
(`h t := if ε then y t else -y t`) satisfy `min (h s₁) (h s₃) - max (h s₀) (h s₂) ≥ 2 * H + 1`,
`tapeCrossingLowers y T H` contains at least `2 * (min (h s₁) (h s₃) - max (h s₀) (h s₂) - 2 * H)`
distinct crossing-lower timestamps, **regardless of arbitrary internal detours**! -/
theorem card_tapeCrossingLowers_ge_of_macroOverlap {y : ℕ → ℤ} (hy : IsWalk y)
    {T H s₀ s₁ s₂ s₃ : ℕ} (ε : Bool)
    (hs₀₁ : s₀ < s₁) (hs₁₂ : s₁ < s₂) (hs₂₃ : s₂ < s₃) (hs₃T : s₃ < T) :
    let h : ℕ → ℤ := fun t => if ε then y t else -y t
    let N_ov : ℕ := (min (h s₁) (h s₃) - max (h s₀) (h s₂) - 2 * (H : ℤ)).toNat
    2 * N_ov ≤ (tapeCrossingLowers y T H).card := by
  intro h N_ov
  rcases Nat.eq_zero_or_pos N_ov with hzero | hpos
  · simp [hzero]
  · set L_ov := max (h s₀) (h s₂)
    set R_ov := min (h s₁) (h s₃)
    have hh_walk : IsWalk h := by
      intro t; cases ε
      · have hs := abs_le.mp (hy t); change |-y (t + 1) - -y t| ≤ 1; rw [abs_le]; omega
      · exact hy t
    have hnh_walk : IsWalk (fun t => -h t) := by
      intro t; have hs := abs_le.mp (hh_walk t); change |-h (t + 1) - -h t| ≤ 1; rw [abs_le]; omega
    have hh_to_y : ∀ {p u : ℕ}, IsHop h T p u → HasHopExcursionGTAt h (2 * H) p u →
        IsHop y T p u ∧ HasHopExcursionGTAt y (2 * H) p u := by
      intro p u hh hx
      cases ε
      · refine ⟨⟨hh.1, hh.2.1, by dsimp [h] at hh; linarith [hh.2.2.1], fun t ht heq => ?_⟩, ?_⟩
        · exact hh.2.2.2 t ht (by dsimp [h]; omega)
        · obtain ⟨t, ht, hgt⟩ := hx
          refine ⟨t, ht, ?_⟩
          dsimp [h] at hgt
          rwa [show -y t - -y p = -(y t - y p) by ring, abs_neg] at hgt
      · exact ⟨hh, hx⟩
    have pair_for : ∀ i : Fin N_ov,
        ∃ v₁ v₂ : ℕ, v₁ < s₁ ∧ s₁ ≤ v₂ ∧
          h v₁ = L_ov + (i.1 : ℤ) ∧ h v₂ = L_ov + (i.1 : ℤ) + 2 * (H : ℤ) + 1 ∧
          v₁ ∈ tapeCrossingLowers y T H ∧ v₂ ∈ tapeCrossingLowers y T H := by
      intro i
      have hi_lt : (i.1 : ℤ) < R_ov - L_ov - 2 * (H : ℤ) := by
        have : i.1 < (R_ov - L_ov - 2 * (H : ℤ)).toNat := i.2
        omega
      set z : ℤ := L_ov + (i.1 : ℤ)
      have hs₀_le : L_ov ≥ h s₀ := le_max_left _ _
      have hs₂_le : L_ov ≥ h s₂ := le_max_right _ _
      have hs₁_ge : h s₁ ≥ R_ov := min_le_left _ _
      have hs₃_ge : h s₃ ≥ R_ov := min_le_right _ _
      -- Call 1: valley on `-h` across `(s₀, s₁, s₂)` at level `-z`.
      obtain ⟨v₁, u₁, _, hv₁s₁, hs₁u₁, hu₁s₂, hv₁z, hu₁z, hhop₁_nh, hexc₁_nh⟩ :=
        exists_hop_gt_of_valley_eq (T := T) (H := 2 * H) (R := -z) hnh_walk
          hs₀₁ hs₁₂ (lt_trans hs₂₃ hs₃T) (by omega) (by push_cast; omega) (by omega)
      have hhop₁_h : IsHop h T v₁ u₁ := by
        unfold IsHop at hhop₁_nh ⊢; simp only [ne_eq, neg_inj] at hhop₁_nh; exact hhop₁_nh
      have hexc₁_h : HasHopExcursionGTAt h (2 * H) v₁ u₁ := by
        obtain ⟨t, ht, hgt⟩ := hexc₁_nh
        exact ⟨t, ht, by rwa [show -h t - -h v₁ = -(h t - h v₁) by ring, abs_neg] at hgt⟩
      -- Call 2: valley on `h` across `(s₁, u₁, s₃)` at level `z + 2 * H + 1`.
      obtain ⟨v₂, u₂, hs₁v₂, hv₂u₁, hu₁u₂, _, hv₂z, _, hhop₂_h, hexc₂_h⟩ :=
        exists_hop_gt_of_valley_eq (T := T) (H := 2 * H) (R := z + 2 * (H : ℤ) + 1) hh_walk
          hs₁u₁ (lt_of_le_of_lt hu₁s₂ hs₂₃) hs₃T (by omega) (by push_cast; omega) (by omega)
      obtain ⟨hhop₁_y, hexc₁_y⟩ := hh_to_y hhop₁_h hexc₁_h
      obtain ⟨hhop₂_y, hexc₂_y⟩ := hh_to_y hhop₂_h hexc₂_h
      have hv₁T : v₁ < T := lt_trans hv₁s₁ (lt_trans hs₁₂ (lt_trans hs₂₃ hs₃T))
      have hv₂T : v₂ < T := lt_trans hv₂u₁ (lt_of_le_of_lt hu₁s₂ (lt_trans hs₂₃ hs₃T))
      have hcr₁₂ : HopsCross v₁ u₁ v₂ u₂ := Or.inl ⟨lt_of_lt_of_le hv₁s₁ hs₁v₂, hv₂u₁, hu₁u₂⟩
      have hcr₂₁ : HopsCross v₂ u₂ v₁ u₁ := Or.inr ⟨lt_of_lt_of_le hv₁s₁ hs₁v₂, hv₂u₁, hu₁u₂⟩
      exact ⟨v₁, v₂, hv₁s₁, hs₁v₂, by omega, hv₂z,
        mem_filter.mpr ⟨mem_range.mpr hv₁T, u₁, hhop₁_y, hexc₁_y, v₂, u₂, hhop₂_y, hexc₂_y, hcr₁₂⟩,
        mem_filter.mpr ⟨mem_range.mpr hv₂T, u₂, hhop₂_y, hexc₂_y, v₁, u₁, hhop₁_y, hexc₁_y, hcr₂₁⟩⟩
    choose f₁ f₂ hf₁_lt hf₂_ge hf₁_val hf₂_val hf₁_mem hf₂_mem using pair_for
    let emb : Fin N_ov ⊕ Fin N_ov → ℕ
      | Sum.inl i => f₁ i
      | Sum.inr i => f₂ i
    have hinj : Function.Injective emb := by
      intro x y_in heq
      cases x with
      | inl i =>
        cases y_in with
        | inl j =>
          dsimp [emb] at heq
          have hv : h (f₁ i) = h (f₁ j) := congrArg h heq
          rw [hf₁_val, hf₁_val] at hv
          exact congrArg Sum.inl (Fin.ext (by omega))
        | inr j =>
          dsimp [emb] at heq
          have := hf₁_lt i; have := hf₂_ge j; omega
      | inr i =>
        cases y_in with
        | inl j =>
          dsimp [emb] at heq
          have := hf₁_lt j; have := hf₂_ge i; omega
        | inr j =>
          dsimp [emb] at heq
          have hv : h (f₂ i) = h (f₂ j) := congrArg h heq
          rw [hf₂_val, hf₂_val] at hv
          exact congrArg Sum.inr (Fin.ext (by omega))
    have hsub : (univ : Finset (Fin N_ov ⊕ Fin N_ov)).image emb ⊆ tapeCrossingLowers y T H := by
      intro v hv
      obtain ⟨x, _, rfl⟩ := mem_image.mp hv
      cases x with
      | inl i => exact hf₁_mem i
      | inr i => exact hf₂_mem i
    calc 2 * N_ov = (univ : Finset (Fin N_ov ⊕ Fin N_ov)).card := by simp [two_mul]
      _ = ((univ : Finset (Fin N_ov ⊕ Fin N_ov)).image emb).card :=
          (card_image_of_injective _ hinj).symm
      _ ≤ (tapeCrossingLowers y T H).card := card_le_card hsub

/-- **Exact Crossing-Capable Skeleton Characterization (Proposition 6.5).** A skeleton `s : List Bool` is crossing-capable at hop parameter `H` and milestone scale `Λ` iff
it contains `0 ≤ i₀ ≤ i₁ ≤ i₂ ≤ i₃ ≤ s.length` and polarity `ε : Bool` whose grid coordinates
`h i = ± skeletonGridAt s i` satisfy the three alternating amplitude inequalities
`2H + 3 ≤ (h i₁ - h i₀ + 2) * Λ`, `2H + 3 ≤ (h i₁ - h i₂ + 2) * Λ`, `2H + 3 ≤ (h i₃ - h i₂ + 2) * Λ`
and spatial overlap inequality `3 ≤ (min (h i₁) (h i₃) - max (h i₀) (h i₂) + 2) * Λ` (`i.e. ov ≥ -1`).
Whenever `Λ ≤ H + 1` (`in particular whenever 2 * Λ ≤ H`), these inequalities automatically force strict
inequalities `i₀ < i₁ < i₂ < i₃`, while for `Λ ≥ H + 2` (`where 2Λ - 2 ≥ 2H + 1`), `i₀ = i₁ = i₂ = i₃`
exact-matches sub-milestone intra-epoch crossing hops! -/
def IsCrossingCapableSkeleton (H Λ : ℕ) (s : List Bool) : Prop :=
  ∃ (ε : Bool) (i₀ i₁ i₂ i₃ : ℕ),
    i₀ ≤ i₁ ∧ i₁ ≤ i₂ ∧ i₂ ≤ i₃ ∧ i₃ ≤ s.length ∧
    let h : ℕ → ℤ := fun i => (if ε then 1 else -1) * skeletonGridAt s i
    2 * (H : ℤ) + 3 ≤ (h i₁ - h i₀ + 2) * (Λ : ℤ) ∧
    2 * (H : ℤ) + 3 ≤ (h i₁ - h i₂ + 2) * (Λ : ℤ) ∧
    2 * (H : ℤ) + 3 ≤ (h i₃ - h i₂ + 2) * (Λ : ℤ) ∧
    3 ≤ (min (h i₁) (h i₃) - max (h i₀) (h i₂) + 2) * (Λ : ℤ)

/-- **Detour-Proof Sufficient Skeleton Condition (`Regime III`):**
Grid overlap satisfies `(min (h i₁) (h i₃) - max (h i₀) (h i₂)) * Λ ≥ 2H + 1`. -/
def IsDetourProofSkeleton (H Λ : ℕ) (s : List Bool) : Prop :=
  ∃ (ε : Bool) (i₀ i₁ i₂ i₃ : ℕ),
    i₀ < i₁ ∧ i₁ < i₂ ∧ i₂ < i₃ ∧ i₃ ≤ s.length ∧
    let h : ℕ → ℤ := fun i => (if ε then 1 else -1) * skeletonGridAt s i
    2 * (H : ℤ) + 1 ≤ (min (h i₁) (h i₃) - max (h i₀) (h i₂)) * (Λ : ℤ)

/-- Scale-free `2 * Λ ≤ H` crossing-capable skeleton predicate (`3` alternating legs of grid
amplitude `≥ 3` and grid overlap `≥ -1`, completely independent of `H`, `Λ`, and `d`!). -/
def IsScaleFreeCrossingCapable (s : List Bool) : Prop :=
  ∃ (ε : Bool) (i₀ i₁ i₂ i₃ : ℕ),
    i₀ < i₁ ∧ i₁ < i₂ ∧ i₂ < i₃ ∧ i₃ ≤ s.length ∧
    let h : ℕ → ℤ := fun i => (if ε then 1 else -1) * skeletonGridAt s i
    3 ≤ h i₁ - h i₀ ∧ 3 ≤ h i₁ - h i₂ ∧ 3 ≤ h i₃ - h i₂ ∧
    -1 ≤ min (h i₁) (h i₃) - max (h i₀) (h i₂)

/-- Whenever `1 ≤ Λ` and `2 * Λ ≤ H`, `IsCrossingCapableSkeleton H Λ s` implies the scale-free
`3`-leg overlapping zigzag predicate `IsScaleFreeCrossingCapable s` **and** `9 ≤ s.length`. -/
theorem isScaleFreeCrossingCapable_of_two_mul_le {H Λ : ℕ} {s : List Bool}
    (hΛ : 1 ≤ Λ) (h2Λ : 2 * Λ ≤ H) (hcap : IsCrossingCapableSkeleton H Λ s) :
    IsScaleFreeCrossingCapable s ∧ 9 ≤ s.length := by
  obtain ⟨ε, i₀, i₁, i₂, i₃, h01, h12, h23, h3len, ha1, ha2, ha3, hov⟩ := hcap
  set h : ℕ → ℤ := fun i => (if ε then 1 else -1) * skeletonGridAt s i
  have hΛz : (1 : ℤ) ≤ (Λ : ℤ) := by exact_mod_cast hΛ
  have h2Λz : 2 * (Λ : ℤ) ≤ (H : ℤ) := by exact_mod_cast h2Λ
  have hd10 : 3 ≤ h i₁ - h i₀ := by nlinarith
  have hd12 : 3 ≤ h i₁ - h i₂ := by nlinarith
  have hd32 : 3 ≤ h i₃ - h i₂ := by nlinarith
  have hdov : -1 ≤ min (h i₁) (h i₃) - max (h i₀) (h i₂) := by nlinarith
  have step_bound : ∀ {a b : ℕ}, a ≤ b → |h b - h a| ≤ ((b - a : ℕ) : ℤ) := by
    intro a b hab
    have hbd := abs_skeletonGridAt_sub_le s hab
    cases ε
    · dsimp [h]
      rw [show (-1 : ℤ) * skeletonGridAt s b - (-1 : ℤ) * skeletonGridAt s a =
        -(skeletonGridAt s b - skeletonGridAt s a) by ring, abs_neg]
      exact hbd
    · dsimp [h]
      simpa using hbd
  have hi01 : 3 ≤ i₁ - i₀ := by
    have := (le_abs_self _).trans (step_bound h01); omega
  have hi12 : 3 ≤ i₂ - i₁ := by
    have : h i₁ - h i₂ ≤ |h i₂ - h i₁| := by rw [abs_sub_comm]; exact le_abs_self _
    have := this.trans (step_bound h12); omega
  have hi23 : 3 ≤ i₃ - i₂ := by
    have := (le_abs_self _).trans (step_bound h23); omega
  exact ⟨⟨ε, i₀, i₁, i₂, i₃, by omega, by omega, by omega, h3len, hd10, hd12, hd32, hdov⟩, by omega⟩

private theorem exists_turn_between_opp_steps : ∀ (w : List Bool) {p q : ℕ}
    (hp : p < w.length) (hq : q < w.length), p < q → w[p] ≠ w[q] → 1 ≤ macroTurns w
  | [], _, _, hp, _, _, _ => by simp at hp
  | [_], p, q, hp, hq, hpq, _ => by simp at hp hq; omega
  | b₁ :: b₂ :: rest, p, q, hp, hq, hpq, hne => by
    by_cases h12 : b₁ = b₂
    · subst h12
      cases p with
      | zero =>
        cases q with
        | zero => omega
        | succ q' =>
          cases q' with
          | zero => exact absurd rfl hne
          | succ q'' =>
            have hq' : q'' + 1 < (b₁ :: rest).length := by simpa using hq
            have hres := exists_turn_between_opp_steps (b₁ :: rest) (p := 0) (q := q'' + 1)
              (by simp) hq' (by omega) (by simpa using hne)
            simpa [macroTurns] using hres
      | succ p' =>
        cases q with
        | zero => omega
        | succ q' =>
          have hres := exists_turn_between_opp_steps (b₁ :: rest)
            (by simpa using hp) (by simpa using hq) (by omega) (by simpa using hne)
          simpa [macroTurns] using hres
    · simp [macroTurns, h12]

private theorem two_turns_of_three_opp_steps : ∀ (w : List Bool) {p q r : ℕ}
    (hp : p < w.length) (hq : q < w.length) (hr : r < w.length),
    p < q → q < r → w[p] ≠ w[q] → w[q] ≠ w[r] → 2 ≤ macroTurns w
  | [], _, _, _, hp, _, _, _, _, _, _ => by simp at hp
  | [_], p, q, _, hp, hq, _, hpq, _, _, _ => by simp at hp hq; omega
  | b₁ :: b₂ :: rest, p, q, r, hp, hq, hr, hpq, hqr, hne1, hne2 => by
    by_cases h12 : b₁ = b₂
    · subst h12
      cases p with
      | zero =>
        cases q with
        | zero => omega
        | succ q' =>
          cases q' with
          | zero => exact absurd rfl hne1
          | succ q'' =>
            cases r with
            | zero => omega
            | succ r' =>
              have hres := two_turns_of_three_opp_steps (b₁ :: rest) (p := 0) (q := q'' + 1) (r := r')
                (by simp) (by simpa using hq) (by simpa using hr) (by omega) (by omega)
                (by simpa using hne1) (by simpa using hne2)
              simpa [macroTurns] using hres
      | succ p' =>
        cases q with
        | zero => omega
        | succ q' =>
          cases r with
          | zero => omega
          | succ r' =>
            have hres := two_turns_of_three_opp_steps (b₁ :: rest)
              (by simpa using hp) (by simpa using hq) (by simpa using hr)
              (by omega) (by omega) (by simpa using hne1) (by simpa using hne2)
            simpa [macroTurns] using hres
    · cases q with
      | zero => omega
      | succ q' =>
        cases r with
        | zero => omega
        | succ r' =>
          have h1 : 1 ≤ macroTurns (b₂ :: rest) :=
            exists_turn_between_opp_steps (b₂ :: rest)
              (by simpa using hq) (by simpa using hr) (by omega) (by simpa using hne2)
          simp only [macroTurns, bne_iff_ne, ne_eq, h12, not_false_eq_true, ↓reduceIte]
          omega

private theorem exists_step_with_val {s : List Bool} {a b : ℕ} {target : Bool}
    (hab : a < b) (hb : b ≤ s.length)
    (hdiff : (if target then 1 else -1) * (skeletonGridAt s b - skeletonGridAt s a) > 0) :
    ∃ (p : ℕ) (hp : p < s.length), a ≤ p ∧ p < b ∧ s[p] = target := by
  by_contra hall
  push Not at hall
  have hle_zero : ∀ k : ℕ, a ≤ k → k ≤ b →
      (if target then 1 else -1) * (skeletonGridAt s k - skeletonGridAt s a) ≤ 0 := by
    intro k hak hkb
    induction k with
    | zero =>
      have ha0 : a = 0 := Nat.eq_zero_of_le_zero hak; subst ha0; simp
    | succ k ih =>
      rcases eq_or_lt_of_le hak with rfl | hlt
      · simp
      · have hak' : a ≤ k := Nat.le_of_lt_succ hlt
        have hprev := ih hak' (le_of_lt hkb)
        have hk_len : k < s.length := lt_of_lt_of_le hkb hb
        have hstep := skeletonGridAt_succ_of_lt s hk_len
        have hne := hall k hk_len hak' hkb
        cases target <;> cases hsk : s[k] <;> simp_all <;> omega
  have := hle_zero b hab.le le_rfl
  omega

/-- Every `IsScaleFreeCrossingCapable` skeleton has **at least `2` macroscopic sign-reversal turns**! -/
theorem two_le_macroTurns_of_isScaleFreeCrossingCapable {s : List Bool}
    (hcap : IsScaleFreeCrossingCapable s) : 2 ≤ macroTurns s := by
  obtain ⟨ε, i₀, i₁, i₂, i₃, h01, h12, h23, h3len, hd10, hd12, hd32, _⟩ := hcap
  obtain ⟨p, hp_len, hp0, hp1, hsp⟩ := exists_step_with_val (s := s) (target := ε) h01
    (le_trans h12.le (le_trans h23.le h3len)) (by cases ε <;> simp_all <;> omega)
  obtain ⟨q, hq_len, hq1, hq2, hsq⟩ := exists_step_with_val (s := s) (target := !ε) h12
    (le_trans h23.le h3len) (by cases ε <;> simp_all <;> omega)
  obtain ⟨r, hr_len, hr2, hr3, hsr⟩ := exists_step_with_val (s := s) (target := ε) h23 h3len
    (by cases ε <;> simp_all <;> omega)
  exact two_turns_of_three_opp_steps s hp_len hq_len hr_len
    (lt_of_lt_of_le hp1 hq1) (lt_of_lt_of_le hq2 hr2)
    (by rw [hsp, hsq]; cases ε <;> decide)
    (by rw [hsq, hsr]; cases ε <;> decide)

/-- **Soundness Theorem (Proposition 6.5 Necessary Direction):**
For **every** unit-speed walk `y` (`IsWalk y`, `y 0 = 0`) and **every** `Λ ≥ 1`, if
`(tapeCrossingLowers y T H).Nonempty`, then `IsCrossingCapableSkeleton H Λ (tapeSkeleton y T Λ)` holds! -/
theorem isCrossingCapableSkeleton_of_tapeCrossingLowers_nonempty {y : ℕ → ℤ}
    (hy : IsWalk y) (hy0 : y 0 = 0) {T H Λ : ℕ} (hΛ : 1 ≤ Λ)
    (hne : (tapeCrossingLowers y T H).Nonempty) :
    IsCrossingCapableSkeleton H Λ (tapeSkeleton y T Λ) := by
  obtain ⟨v, hv⟩ := hne
  obtain ⟨_, u, hhop, hexc, p', u', hhop', hexc', hcr⟩ := mem_filter.mp hv
  obtain ⟨ε, s₀, s₁, s₂, s₃, hs01, hs12, hs23, hs3T, hj10, hj12, hj32, hjov⟩ :=
    exists_crossingZigzag_of_crossingHopsGT2H hy hhop hexc hhop' hexc' hcr
  set sk := tapeSkeleton y T Λ
  set i₀ := epochIdx y Λ s₀
  set i₁ := epochIdx y Λ s₁
  set i₂ := epochIdx y Λ s₂
  set i₃ := epochIdx y Λ s₃
  have hs0T : s₀ < T := lt_trans hs01 (lt_trans hs12 (lt_trans hs23 hs3T))
  have hs1T : s₁ < T := lt_trans hs12 (lt_trans hs23 hs3T)
  have hs2T : s₂ < T := lt_trans hs23 hs3T
  have hi0_le : i₀ ≤ i₁ := epochIdx_mono hs01.le
  have hi1_le : i₁ ≤ i₂ := epochIdx_mono hs12.le
  have hi2_le : i₂ ≤ i₃ := epochIdx_mono hs23.le
  have hi3_len : i₃ ≤ sk.length := epochIdx_le_length hs3T
  set h_raw : ℕ → ℤ := fun t => if ε then y t else -y t
  set h_grid : ℕ → ℤ := fun i => (if ε then 1 else -1) * skeletonGridAt sk i
  have conf : ∀ {t : ℕ} (ht : t < T), |h_raw t - h_grid (epochIdx y Λ t) * (Λ : ℤ)| ≤ (Λ : ℤ) - 1 := by
    intro t ht
    have hlt := abs_sub_skeletonGridAt_lt hy hy0 hΛ ht
    have habs : |h_raw t - h_grid (epochIdx y Λ t) * (Λ : ℤ)| < (Λ : ℤ) := by
      cases ε
      · dsimp [h_raw, h_grid, sk]
        rw [show -y t - (-1 : ℤ) * skeletonGridAt (tapeSkeleton y T Λ) (epochIdx y Λ t) * (Λ : ℤ) =
          -(y t - skeletonGridAt (tapeSkeleton y T Λ) (epochIdx y Λ t) * (Λ : ℤ)) by ring, abs_neg]
        exact hlt
      · dsimp [h_raw, h_grid, sk]
        simpa using hlt
    omega
  have hc0 := abs_le.mp (conf hs0T)
  have hc1 := abs_le.mp (conf hs1T)
  have hc2 := abs_le.mp (conf hs2T)
  have hc3 := abs_le.mp (conf hs3T)
  have h0_val : |h_raw s₀ - h_grid i₀ * (Λ : ℤ)| ≤ (Λ : ℤ) - 1 := conf hs0T
  have h1_val : |h_raw s₁ - h_grid i₁ * (Λ : ℤ)| ≤ (Λ : ℤ) - 1 := conf hs1T
  have h2_val : |h_raw s₂ - h_grid i₂ * (Λ : ℤ)| ≤ (Λ : ℤ) - 1 := conf hs2T
  have h3_val : |h_raw s₃ - h_grid i₃ * (Λ : ℤ)| ≤ (Λ : ℤ) - 1 := conf hs3T
  have hb0 := abs_le.mp h0_val
  have hb1 := abs_le.mp h1_val
  have hb2 := abs_le.mp h2_val
  have hb3 := abs_le.mp h3_val
  have ha1 : 2 * (H : ℤ) + 3 ≤ (h_grid i₁ - h_grid i₀ + 2) * (Λ : ℤ) := by
    change 2 * (H : ℤ) + 1 ≤ h_raw s₁ - h_raw s₀ at hj10
    have : (h_grid i₁ - h_grid i₀ + 2) * (Λ : ℤ) =
        h_grid i₁ * (Λ : ℤ) - h_grid i₀ * (Λ : ℤ) + 2 * (Λ : ℤ) := by ring
    linarith
  have ha2 : 2 * (H : ℤ) + 3 ≤ (h_grid i₁ - h_grid i₂ + 2) * (Λ : ℤ) := by
    change 2 * (H : ℤ) + 1 ≤ h_raw s₁ - h_raw s₂ at hj12
    have : (h_grid i₁ - h_grid i₂ + 2) * (Λ : ℤ) =
        h_grid i₁ * (Λ : ℤ) - h_grid i₂ * (Λ : ℤ) + 2 * (Λ : ℤ) := by ring
    linarith
  have ha3 : 2 * (H : ℤ) + 3 ≤ (h_grid i₃ - h_grid i₂ + 2) * (Λ : ℤ) := by
    change 2 * (H : ℤ) + 1 ≤ h_raw s₃ - h_raw s₂ at hj32
    have : (h_grid i₃ - h_grid i₂ + 2) * (Λ : ℤ) =
        h_grid i₃ * (Λ : ℤ) - h_grid i₂ * (Λ : ℤ) + 2 * (Λ : ℤ) := by ring
    linarith
  have hov : 3 ≤ (min (h_grid i₁) (h_grid i₃) - max (h_grid i₀) (h_grid i₂) + 2) * (Λ : ℤ) := by
    change 1 ≤ min (h_raw s₁) (h_raw s₃) - max (h_raw s₀) (h_raw s₂) at hjov
    have hmin_ub : min (h_raw s₁) (h_raw s₃) ≤ min (h_grid i₁) (h_grid i₃) * (Λ : ℤ) + (Λ : ℤ) - 1 := by
      rcases le_total (h_grid i₁) (h_grid i₃) with hm1 | hm3
      · rw [min_eq_left hm1]; linarith [min_le_left (h_raw s₁) (h_raw s₃)]
      · rw [min_eq_right hm3]; linarith [min_le_right (h_raw s₁) (h_raw s₃)]
    have hmax_lb : max (h_grid i₀) (h_grid i₂) * (Λ : ℤ) - ((Λ : ℤ) - 1) ≤ max (h_raw s₀) (h_raw s₂) := by
      rcases le_total (h_grid i₀) (h_grid i₂) with hx0 | hx2
      · rw [max_eq_right hx0]; linarith [le_max_right (h_raw s₀) (h_raw s₂)]
      · rw [max_eq_left hx2]; linarith [le_max_left (h_raw s₀) (h_raw s₂)]
    have hrew : (min (h_grid i₁) (h_grid i₃) - max (h_grid i₀) (h_grid i₂) + 2) * (Λ : ℤ) =
        min (h_grid i₁) (h_grid i₃) * (Λ : ℤ) - max (h_grid i₀) (h_grid i₂) * (Λ : ℤ) + 2 * (Λ : ℤ) := by ring
    linarith
  exact ⟨ε, i₀, i₁, i₂, i₃, hi0_le, hi1_le, hi2_le, hi3_len, ha1, ha2, ha3, hov⟩

/-- **Detour-Proof Skeleton Sufficiency Theorem (Proposition 6.5 Sufficient Direction):**
Whenever `tapeSkeleton y T Λ` satisfies `IsDetourProofSkeleton H Λ` (`with T ≥ 1, Λ ≥ 1`),
`(tapeCrossingLowers y T H).Nonempty` holds unconditionally on `y`! -/
theorem tapeCrossingLowers_nonempty_of_isDetourProofSkeleton {y : ℕ → ℤ}
    (hy : IsWalk y) (hy0 : y 0 = 0) {T H Λ : ℕ} (hT : 1 ≤ T) (hΛ : 1 ≤ Λ)
    (hdet : IsDetourProofSkeleton H Λ (tapeSkeleton y T Λ)) :
    (tapeCrossingLowers y T H).Nonempty := by
  obtain ⟨ε, i₀, i₁, i₂, i₃, hi01, hi12, hi23, hi3_len, hov⟩ := hdet
  obtain ⟨hlen_mt, hpw, hall_lt, hgrid⟩ := milestoneTimes_properties hy hy0 hT hΛ
  set mt := milestoneTimes y T Λ
  have h3_mt : i₃ < mt.length := by omega
  have h2_mt : i₂ < mt.length := by omega
  have h1_mt : i₁ < mt.length := by omega
  have h0_mt : i₀ < mt.length := by omega
  have mono_mt : ∀ {a b : ℕ} (ha : a < mt.length) (hb : b < mt.length), a < b → mt[a] < mt[b] :=
    fun ha hb hab => List.pairwise_iff_getElem.mp hpw _ _ ha hb hab
  have hs01 : mt[i₀] < mt[i₁] := mono_mt h0_mt h1_mt hi01
  have hs12 : mt[i₁] < mt[i₂] := mono_mt h1_mt h2_mt hi12
  have hs23 : mt[i₂] < mt[i₃] := mono_mt h2_mt h3_mt hi23
  have hs3T : mt[i₃] < T := hall_lt mt[i₃] (List.getElem_mem h3_mt)
  have hlb := card_tapeCrossingLowers_ge_of_macroOverlap (T := T) (H := H) hy ε hs01 hs12 hs23 hs3T
  dsimp only at hlb
  set h_raw : ℕ → ℤ := fun t => if ε then y t else -y t
  set h_sk : ℕ → ℤ := fun i => (if ε then 1 else -1) * skeletonGridAt (tapeSkeleton y T Λ) i
  have hval : ∀ (i : ℕ) (hi : i < mt.length), h_raw mt[i] = h_sk i * (Λ : ℤ) := by
    intro i hi
    have hg := hgrid i hi
    cases ε <;> simp [h_raw, h_sk, mt, hg]
  have hmin_eq : min (h_raw mt[i₁]) (h_raw mt[i₃]) = min (h_sk i₁) (h_sk i₃) * (Λ : ℤ) := by
    rw [hval i₁ h1_mt, hval i₃ h3_mt]
    exact (min_mul_of_nonneg _ _ (Nat.cast_nonneg Λ)).symm
  have hmax_eq : max (h_raw mt[i₀]) (h_raw mt[i₂]) = max (h_sk i₀) (h_sk i₂) * (Λ : ℤ) := by
    rw [hval i₀ h0_mt, hval i₂ h2_mt]
    exact (max_mul_of_nonneg _ _ (Nat.cast_nonneg Λ)).symm
  have hpos_card : 0 < (tapeCrossingLowers y T H).card := by
    rw [hmin_eq, hmax_eq, ← sub_mul] at hlb
    change 2 * (H : ℤ) + 1 ≤ (min (h_sk i₁) (h_sk i₃) - max (h_sk i₀) (h_sk i₂)) * (Λ : ℤ) at hov
    omega
  exact Finset.card_pos.mp hpos_card

/-- Explicit finite subset of `BoundedSkeletonTuple k M_max` consisting of `k`-tape skeletons where
at least one tape satisfies `IsScaleFreeCrossingCapable` (`≥ 3` alternating `≥ 3` legs + `ov ≥ -1`). -/
noncomputable def CrossingCapableSkeletonTuple (k M_max : ℕ) : Finset (Fin k → List Bool) :=
  (BoundedSkeletonTuple k M_max).filter fun skTuple => ∃ j : Fin k, IsScaleFreeCrossingCapable (skTuple j)

/-- Strict proper-subset theorem: the idle/monotone skeleton `fun _ => []` lies in
`BoundedSkeletonTuple k M_max \ CrossingCapableSkeletonTuple k M_max` (`so CrossingCapableSkeletonTuple`
has strictly smaller cardinality `< (2 ^ (M_max + 1) - 1) ^ k`). -/
theorem card_crossingCapableSkeletonTuple_lt (k M_max : ℕ) :
    (CrossingCapableSkeletonTuple k M_max).card < (BoundedSkeletonTuple k M_max).card := by
  apply card_lt_card
  rw [ssubset_iff_subset_not_subset]
  refine ⟨filter_subset _ _, fun hsub => ?_⟩
  have hidle_in : (fun _ : Fin k => ([] : List Bool)) ∈ BoundedSkeletonTuple k M_max := by
    simp [BoundedSkeletonTuple, Fintype.mem_piFinset]
  obtain ⟨_, j, ⟨_, _, _, _, i₃, h01, h12, h23, h3len, _⟩⟩ := mem_filter.mp (hsub hidle_in)
  simp at h3len
  omega

end CrossingCapableCharacterization

/-! ## §4. Open-Territory Reduction: Single-Leg Expansion & Infinite-`d` Pigeonhole (Theorem S) -/

section OpenTerritoryReduction

open scoped Classical

/-- Monotone skeleton leg index `legOfEpoch s ep ∈ {0, ..., macroTurns s}` of epoch `ep`:
consecutive steps of the same sign stay in the same leg, and a sign reversal increments the leg. -/
def legOfEpoch : List Bool → ℕ → ℕ
  | [], _ => 0
  | [_], _ => 0
  | _, 0 => 0
  | _, 1 => 0
  | b₁ :: b₂ :: rest, ep + 2 =>
    (if b₁ != b₂ then 1 else 0) + legOfEpoch (b₂ :: rest) (ep + 1)

theorem legOfEpoch_mono : ∀ (s : List Bool) {a b : ℕ}, a ≤ b → legOfEpoch s a ≤ legOfEpoch s b
  | [], _, _, _ => le_rfl
  | [_], _, _, _ => le_rfl
  | b₁ :: b₂ :: rest, 0, _, _ => Nat.zero_le _
  | b₁ :: b₂ :: rest, 1, 0, hab => by omega
  | b₁ :: b₂ :: rest, 1, 1, _ => le_rfl
  | b₁ :: b₂ :: rest, 1, b' + 2, _ => by
    simp only [legOfEpoch]; omega
  | b₁ :: b₂ :: rest, a' + 2, 0, hab => by omega
  | b₁ :: b₂ :: rest, a' + 2, 1, hab => by omega
  | b₁ :: b₂ :: rest, a' + 2, b' + 2, hab => by
    simp only [legOfEpoch]
    exact Nat.add_le_add_left (legOfEpoch_mono (b₂ :: rest) (by omega)) _

theorem legOfEpoch_le_macroTurns : ∀ (s : List Bool) (ep : ℕ), legOfEpoch s ep ≤ macroTurns s
  | [], _ => le_rfl
  | [_], _ => le_rfl
  | b₁ :: b₂ :: rest, 0 => Nat.zero_le _
  | b₁ :: b₂ :: rest, 1 => Nat.zero_le _
  | b₁ :: b₂ :: rest, ep + 2 => by
    simp only [legOfEpoch, macroTurns]
    exact Nat.add_le_add_left (legOfEpoch_le_macroTurns (b₂ :: rest) (ep + 1)) _

private theorem legOfEpoch_adj_same : ∀ (w : List Bool) {m : ℕ} (hm : m + 1 < w.length),
    legOfEpoch w (m + 1) = legOfEpoch w (m + 2) → w[m]'(Nat.lt_of_succ_lt hm) = w[m + 1]
  | [], _, hm, _ => by simp at hm
  | [_], _, hm, _ => by simp at hm
  | b₁ :: b₂ :: rest, 0, _, hl => by
    cases b₁ <;> cases b₂ <;> simp [legOfEpoch] at hl ⊢ <;> omega
  | b₁ :: b₂ :: rest, m' + 1, hm, hl => by
    have hl' : legOfEpoch (b₂ :: rest) (m' + 1) = legOfEpoch (b₂ :: rest) (m' + 2) := by
      change (if b₁ != b₂ then 1 else 0) + legOfEpoch (b₂ :: rest) (m' + 1) =
        (if b₁ != b₂ then 1 else 0) + legOfEpoch (b₂ :: rest) (m' + 2) at hl
      omega
    exact legOfEpoch_adj_same (b₂ :: rest) (by simpa using hm) hl'

/-- Within a single monotone skeleton leg (`legOfEpoch s a = legOfEpoch s b`), all steps between
`a` and `b` share the same sign, so `|skeletonGridAt s b - skeletonGridAt s a| = b - a`. -/
theorem abs_skeletonGridAt_eq_of_legOfEpoch_eq {s : List Bool} {a b : ℕ}
    (hab : a ≤ b) (hb : b ≤ s.length) (hleg : legOfEpoch s a = legOfEpoch s b) :
    |skeletonGridAt s b - skeletonGridAt s a| = ((b - a : ℕ) : ℤ) := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · simp
  · have ha_lt : a < s.length := lt_of_lt_of_le hlt hb
    have step_eq : ∀ (m : ℕ) (hm_ge : a ≤ m) (hm_lt : m < b),
        s[m]'(lt_of_lt_of_le hm_lt hb) = s[a] := by
      intro m hm_ge hm_lt
      induction m with
      | zero =>
        have ha0 : a = 0 := Nat.eq_zero_of_le_zero hm_ge
        subst ha0; rfl
      | succ m' ihm =>
        rcases eq_or_lt_of_le hm_ge with rfl | hlt_m
        · rfl
        · have hm'_ge : a ≤ m' := Nat.le_of_lt_succ hlt_m
          have hm'_lt : m' < b := lt_trans (Nat.lt_succ_self m') hm_lt
          have hprev := ihm hm'_ge hm'_lt
          have hl_eq : legOfEpoch s (m' + 1) = legOfEpoch s (m' + 2) :=
            le_antisymm (legOfEpoch_mono s (by omega))
              ((legOfEpoch_mono s (Nat.succ_le_of_lt hm_lt)).trans
                (hleg.symm.trans_le (legOfEpoch_mono s (by omega))) |>.trans le_rfl)
          exact (legOfEpoch_adj_same s (lt_of_lt_of_le hm_lt hb) hl_eq).symm.trans hprev
    set sgn : ℤ := if s[a] then 1 else -1
    have hlin : ∀ k : ℕ, a ≤ k → k ≤ b →
        skeletonGridAt s k - skeletonGridAt s a = sgn * ((k - a : ℕ) : ℤ) := by
      intro k hak hkb
      induction k with
      | zero => have ha0 : a = 0 := Nat.eq_zero_of_le_zero hak; subst ha0; simp
      | succ k ihk =>
        rcases eq_or_lt_of_le hak with rfl | hlt_k
        · simp
        · have hak' : a ≤ k := Nat.le_of_lt_succ hlt_k
          have hprev := ihk hak' (le_of_lt hkb)
          have hk_lt : k < s.length := lt_of_lt_of_le hkb hb
          have hsk_eq : s[k] = s[a] := step_eq k hak' hkb
          rw [skeletonGridAt_succ_of_lt s hk_lt, hsk_eq]
          have hcast : ((k + 1 - a : ℕ) : ℤ) = ((k - a : ℕ) : ℤ) + 1 := by omega
          rw [hcast]
          dsimp [sgn]; linarith
    rw [hlin b hab le_rfl, abs_mul]
    have hsgn : |sgn| = 1 := by dsimp [sgn]; cases s[a] <;> norm_num
    rw [hsgn, one_mul, abs_of_nonneg (Nat.cast_nonneg _)]

/-- **No-Intra-Leg Macroscopic Hop Lemma (Lemma 6.6):**
Whenever `1 ≤ Λ` and `2 * Λ ≤ H`, **every** `> 2H` revisit hop `(v, u)` on `y` spans across at least
one macroscopic turn: `legOfEpoch (tapeSkeleton y T Λ) (epochIdx y Λ v) < legOfEpoch (tapeSkeleton y T Λ) (epochIdx y Λ u)`! -/
theorem legOfEpoch_lt_of_isHop_gt2H {y : ℕ → ℤ} (hy : IsWalk y) (hy0 : y 0 = 0)
    {T H Λ v u : ℕ} (hΛ : 1 ≤ Λ) (h2Λ : 2 * Λ ≤ H)
    (hhop : IsHop y T v u) (hexc : HasHopExcursionGTAt y (2 * H) v u) :
    let s := tapeSkeleton y T Λ
    legOfEpoch s (epochIdx y Λ v) < legOfEpoch s (epochIdx y Λ u) := by
  intro s
  have hvu : v < u := lt_trans (Nat.lt_succ_self v) hhop.1
  have huT : u < T := hhop.2.1
  have hvT : v < T := lt_trans hvu huT
  have hep_le : epochIdx y Λ v ≤ epochIdx y Λ u := epochIdx_mono hvu.le
  have hleg_le : legOfEpoch s (epochIdx y Λ v) ≤ legOfEpoch s (epochIdx y Λ u) :=
    legOfEpoch_mono s hep_le
  rcases lt_or_eq_of_le hleg_le with hlt | heq
  · exact hlt
  · exfalso
    have hlen_u : epochIdx y Λ u ≤ s.length := epochIdx_le_length huT
    have hgrid_diff := abs_skeletonGridAt_eq_of_legOfEpoch_eq hep_le hlen_u heq
    have hconf_v : |y v - skeletonGridAt s (epochIdx y Λ v) * (Λ : ℤ)| < (Λ : ℤ) :=
      abs_sub_skeletonGridAt_lt hy hy0 hΛ hvT
    have hconf_u : |y u - skeletonGridAt s (epochIdx y Λ u) * (Λ : ℤ)| < (Λ : ℤ) :=
      abs_sub_skeletonGridAt_lt hy hy0 hΛ huT
    have hyv_eq : y u = y v := hhop.2.2.1
    have hΛz : (1 : ℤ) ≤ (Λ : ℤ) := by exact_mod_cast hΛ
    have h2Λz : 2 * (Λ : ℤ) ≤ (H : ℤ) := by exact_mod_cast h2Λ
    -- Endpoint equality forces `|g_u - g_v| ≤ 1`, hence `epochIdx u - epochIdx v ≤ 1`!
    have hdiff_lt2 : |skeletonGridAt s (epochIdx y Λ u) - skeletonGridAt s (epochIdx y Λ v)| * (Λ : ℤ) <
        2 * (Λ : ℤ) := by
      have htri : |skeletonGridAt s (epochIdx y Λ u) * (Λ : ℤ) -
          skeletonGridAt s (epochIdx y Λ v) * (Λ : ℤ)| ≤
          |y v - skeletonGridAt s (epochIdx y Λ v) * (Λ : ℤ)| +
          |y u - skeletonGridAt s (epochIdx y Λ u) * (Λ : ℤ)| := by
        have hrew : skeletonGridAt s (epochIdx y Λ u) * (Λ : ℤ) -
            skeletonGridAt s (epochIdx y Λ v) * (Λ : ℤ) =
            (y v - skeletonGridAt s (epochIdx y Λ v) * (Λ : ℤ)) -
            (y u - skeletonGridAt s (epochIdx y Λ u) * (Λ : ℤ)) := by linarith
        rw [hrew]
        exact abs_sub _ _
      have hlt_mul : |skeletonGridAt s (epochIdx y Λ u) * (Λ : ℤ) -
          skeletonGridAt s (epochIdx y Λ v) * (Λ : ℤ)| < 2 * (Λ : ℤ) := by linarith
      rwa [← sub_mul, abs_mul, abs_of_nonneg (by omega : (0 : ℤ) ≤ (Λ : ℤ))] at hlt_mul
    have hep_diff_le1 : epochIdx y Λ u - epochIdx y Λ v ≤ 1 := by
      rw [hgrid_diff] at hdiff_lt2
      have : ((epochIdx y Λ u - epochIdx y Λ v : ℕ) : ℤ) < 2 := by nlinarith
      omega
    obtain ⟨t, ht_in, hgt⟩ := hexc
    obtain ⟨hvt, htu⟩ := mem_Ioo.mp ht_in
    have htT : t < T := lt_trans htu huT
    have hep_vt : epochIdx y Λ v ≤ epochIdx y Λ t := epochIdx_mono hvt.le
    have hep_tu : epochIdx y Λ t ≤ epochIdx y Λ u := epochIdx_mono htu.le
    have hep_tv_le1 : epochIdx y Λ t - epochIdx y Λ v ≤ 1 := by omega
    have hgrid_tv_le1 : |skeletonGridAt s (epochIdx y Λ t) - skeletonGridAt s (epochIdx y Λ v)| ≤ 1 :=
      (abs_skeletonGridAt_sub_le s hep_vt).trans (by exact_mod_cast hep_tv_le1)
    have hconf_t : |y t - skeletonGridAt s (epochIdx y Λ t) * (Λ : ℤ)| < (Λ : ℤ) :=
      abs_sub_skeletonGridAt_lt hy hy0 hΛ htT
    have hexc_ub : |y t - y v| < 3 * (Λ : ℤ) := by
      have hrew : y t - y v =
          (y t - skeletonGridAt s (epochIdx y Λ t) * (Λ : ℤ)) -
          (y v - skeletonGridAt s (epochIdx y Λ v) * (Λ : ℤ)) +
          (skeletonGridAt s (epochIdx y Λ t) - skeletonGridAt s (epochIdx y Λ v)) * (Λ : ℤ) := by ring
      rw [hrew]
      have h1 := abs_add_le
        ((y t - skeletonGridAt s (epochIdx y Λ t) * (Λ : ℤ)) -
          (y v - skeletonGridAt s (epochIdx y Λ v) * (Λ : ℤ)))
        ((skeletonGridAt s (epochIdx y Λ t) - skeletonGridAt s (epochIdx y Λ v)) * (Λ : ℤ))
      have h2 := abs_sub (y t - skeletonGridAt s (epochIdx y Λ t) * (Λ : ℤ))
        (y v - skeletonGridAt s (epochIdx y Λ v) * (Λ : ℤ))
      have h3 : |(skeletonGridAt s (epochIdx y Λ t) - skeletonGridAt s (epochIdx y Λ v)) * (Λ : ℤ)| ≤
          (Λ : ℤ) := by
        rw [abs_mul, abs_of_nonneg (by omega : (0 : ℤ) ≤ (Λ : ℤ))]
        nlinarith
      linarith
    push_cast at hgt
    linarith

/-- Crossing-lower steps on tape `j` falling inside monotone skeleton leg `r` of `tapeSkeleton (τ₀.work j) T Λ`. -/
noncomputable def legCrossingLowers {k : ℕ} (τ₀ : Trace k) (T H Λ : ℕ) (j : Fin k) (r : ℕ) :
    Finset ℕ :=
  (tapeCrossingLowers (τ₀.work j) T H).filter fun v =>
    legOfEpoch (tapeSkeleton (τ₀.work j) T Λ) (epochIdx (τ₀.work j) Λ v) = r

/-- Finite-set infinite-fiber pigeonhole lemma (`zero upstream lemma dependencies`). -/
theorem exists_infinite_fiber_of_mapsTo_finset {α : Type*} {S : Set ℕ} (hS : S.Infinite)
    (F : Finset α) (f : ℕ → α) (hf : ∀ d ∈ S, f d ∈ F) :
    ∃ x ∈ F, {d : ℕ | d ∈ S ∧ f d = x}.Infinite := by
  by_contra hall
  push Not at hall
  have hfin : (⋃ x ∈ (F : Set α), {d : ℕ | d ∈ S ∧ f d = x}).Finite :=
    F.finite_toSet.biUnion fun x hx => hall x hx
  refine hS (hfin.subset fun d hd => ?_)
  exact Set.mem_biUnion (hf d hd) ⟨hd, rfl⟩

end OpenTerritoryReduction

section SimulatorHeavyTraceSkeleton

open scoped Classical

/-- Physical simulator linear-time coefficient `C_sim(c) := 11 * c + 1` from Paper 15
(`TapeStorageRates.aligned_low_trace_dimensions`). -/
noncomputable def adaptiveBridge_cSim (c : ℝ) : ℝ :=
  11 * c + 1

/-- Complete trace support `𝒯_d(N)` of simulator `N : TM` over all `2^L` canonical inputs
`X : Fin (d * d * entryBits d) → Bool` (`matching TapeStorageRates.TraceTransfer.lean:20`). -/
noncomputable def SimulatorTraceSupport (N : TM) (d : ℕ) : Finset (Trace N.k) :=
  (univ : Finset (Fin (d * d * entryBits d) → Bool)).image fun X =>
    trace N (List.ofFn X)

/-- Subset `𝒯_heavy(N, d, η_heavy) ⊆ SimulatorTraceSupport N d` of heavy traces with
`traceProb N L τ₀ ≥ 2 ^ (-η_heavy * L)`. -/
noncomputable def SimulatorHeavyTraces (N : TM) (d : ℕ) (η_heavy : ℝ) : Finset (Trace N.k) :=
  (SimulatorTraceSupport N d).filter fun τ₀ =>
    (2 : ℝ) ^ (-η_heavy * ((d * d * entryBits d : ℕ) : ℝ)) ≤
      traceProb N (d * d * entryBits d) τ₀

end SimulatorHeavyTraceSkeleton

end NativeRelations
