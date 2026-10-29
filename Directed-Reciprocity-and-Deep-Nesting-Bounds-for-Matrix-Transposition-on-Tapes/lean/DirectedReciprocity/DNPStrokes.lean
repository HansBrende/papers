import Mathlib

/-!
# Exact Stroke Law and `O(m)` Recursive Turn Potential (`Proposition SL`)

For the deep-nesting walk `U(s₀, m, 1)` (`m ≤ s₀`, scale `R_i = 2^{s₀ - i}`, stroke length
`Π_i = (m - i + 1) R_i`, period `P = 4 Π₀ = 4 (m + 1) 2^{s₀}`), we formalize:

1. **Recursive stroke offset bijection (`decompStroke` / `reconstructStroke`)**:
   Every offset `o ∈ {0, …, Π_κ - 1}` inside a level-`κ` stroke (`κ ≤ m ≤ s₀`) decomposes uniquely
   into a stopping depth `s ∈ {0, …, m - κ}`, a nested stroke-direction word
   `w ∈ {false, true}^s` (`false` = back stroke, `true` = forward stroke), and a plain-segment
   remainder `rem ∈ {0, …, R_{κ + s} - 1}`.
2. **Uniform stopping depth, fair-coin nested directions, and parity independence**:
   - For each `s ≤ m - κ` and each word `w` of length `s`, exactly `R_{κ + s}` offsets in
     `[0, Π_κ)` yield `(s, w)`, with `2^s · R_{κ + s} = R_κ` (`card_stroke_stopDepth_branchWord`).
   - Summing over `w ∈ {false, true}^s`, each stopping depth `s ∈ {0, …, m - κ}` occurs on
     exactly `R_κ = Π_κ / (m - κ + 1)` offsets (`card_stroke_stopDepth`).
   - When `m < s₀` (so every `R_i` for `i ≤ m` is even), `reconstructStroke` preserves parity modulo
     `R_m` and hence modulo `2`; for each parity `p ∈ Fin 2`, stopping depth `s ≤ m - κ`, and word
     `w` of length `s`, the joint count is `R_{κ + s} / 2`, and the marginal count at depth `s` and
     parity `p` is `R_κ / 2` (`card_stroke_stopDepth_branchWord_parity`,
     `card_stroke_stopDepth_parity`).
3. **`O(m)` recursive turn-potential evaluator (`evalPhiRec`)**:
   For any level-uniform turn-supported label with path-sum increments `cb`, `cf` (`c_b(l) = 1 + A_l`,
   `c_f(l) = 2 + A_l + E_l`) and tip jump `jTip`, `evalPhiRec` computes the cumulative turn potential
   `Φ(t) = ∑_{0 < τ ≤ t} J(τ)` in `O(m)` arithmetic steps (`evalPhiRec_eq_sum_turnJumps`), and along
   the back and forward strokes of any V of level `κ` (`1 ≤ κ ≤ m`) decomposes `Φ` into
   `cb κ + strokePhiRec ... κ o` and `cf κ + strokePhiRec ... κ o` (`strokePhiRec_back`,
   `strokePhiRec_fwd`).
-/

namespace DirectedReciprocity

open Finset

/-- Scale `R_i = 2^{s₀ - i}` of level `i` in `U(s₀, m, 1)`. -/
def scaleR (s0 i : ℕ) : ℕ := 2 ^ (s0 - i)

/-- Length `Π_i = (m - i + 1) R_i` of a level-`i` stroke in `U(s₀, m, 1)`. -/
def strokeLen (s0 m i : ℕ) : ℕ := (m - i + 1) * scaleR s0 i

/-- Full period `P = 4 Π₀ = 4 (m + 1) 2^{s₀}` of `U(s₀, m, 1)`. -/
def dnpPeriod (s0 m : ℕ) : ℕ := 4 * strokeLen s0 m 0

theorem scaleR_pos (s0 i : ℕ) : 0 < scaleR s0 i := by
  unfold scaleR; positivity

theorem strokeLen_pos (s0 m i : ℕ) : 0 < strokeLen s0 m i := by
  unfold strokeLen
  exact Nat.mul_pos (by omega) (scaleR_pos s0 i)

theorem scaleR_succ {s0 i : ℕ} (hi : i < s0) :
    scaleR s0 i = 2 * scaleR s0 (i + 1) := by
  unfold scaleR
  rw [show s0 - i = (s0 - (i + 1)) + 1 by omega, Nat.pow_succ, Nat.mul_comm]

theorem strokeLen_succ {s0 m i : ℕ} (hi : i < m) (hms : m ≤ s0) :
    strokeLen s0 m i = scaleR s0 i + 2 * strokeLen s0 m (i + 1) := by
  unfold strokeLen
  rw [scaleR_succ (by omega : i < s0), show m - i + 1 = 1 + (m - (i + 1) + 1) by omega]
  ring

theorem even_scaleR {s0 i : ℕ} (hi : i < s0) : 2 ∣ scaleR s0 i := by
  rw [scaleR_succ hi]
  exact Nat.dvd_mul_right 2 _

theorem even_strokeLen {s0 m i : ℕ} (hi : i < s0) : 2 ∣ strokeLen s0 m i := by
  unfold strokeLen
  exact dvd_mul_of_dvd_right (even_scaleR hi) _

theorem scaleR_eq_pow_mul {s0 m κ s : ℕ} (hκs : κ + s ≤ m) (hms : m ≤ s0) :
    scaleR s0 (κ + s) = 2 ^ (m - κ - s) * scaleR s0 m := by
  unfold scaleR
  rw [← Nat.pow_add, show m - κ - s + (s0 - m) = s0 - (κ + s) by omega]

theorem strokeLen_eq_pow_mul {s0 m κ : ℕ} (hκ : κ ≤ m) (hms : m ≤ s0) :
    strokeLen s0 m κ = (m - κ + 1) * (2 ^ (m - κ) * scaleR s0 m) := by
  unfold strokeLen
  have h := scaleR_eq_pow_mul (s := 0) (by omega : κ + 0 ≤ m) hms
  simpa using congrArg ((m - κ + 1) * ·) h

/-! ### Part 1: Recursive stroke offset decomposition and bijection -/

/-- Recursive decomposition of an offset `o` in a stroke with remaining nesting depth `d` and
finest-level segment length `r_m`: returns `(stopDepth, branchWord, segRem)`. -/
def decompDepth (r_m : ℕ) : ℕ → ℕ → ℕ × List Bool × ℕ
  | 0, o => (0, [], o)
  | d + 1, o =>
    let rCur := 2 ^ (d + 1) * r_m
    if o < rCur then (0, [], o)
    else
      let o' := o - rCur
      let piNext := (d + 1) * (2 ^ d * r_m)
      if o' < piNext then
        let res := decompDepth r_m d o'
        (res.1 + 1, false :: res.2.1, res.2.2)
      else
        let res := decompDepth r_m d (o' - piNext)
        (res.1 + 1, true :: res.2.1, res.2.2)

/-- Inverse of `decompDepth`: reconstructs the stroke offset from `(stopDepth, branchWord, segRem)`. -/
def reconstructDepth (r_m : ℕ) : ℕ → ℕ → List Bool → ℕ → ℕ
  | 0, _, _, rem => rem
  | _ + 1, 0, _, rem => rem
  | _ + 1, _ + 1, [], rem => rem
  | d + 1, s + 1, b :: w, rem =>
    let rCur := 2 ^ (d + 1) * r_m
    let piNext := (d + 1) * (2 ^ d * r_m)
    rCur + (if b then piNext else 0) + reconstructDepth r_m d s w rem

/-- Validity predicate for a stroke code `(s, w, rem)` at remaining depth `d` and base scale `r_m`. -/
def ValidStrokeCode (r_m d s : ℕ) (w : List Bool) (rem : ℕ) : Prop :=
  s ≤ d ∧ w.length = s ∧ rem < 2 ^ (d - s) * r_m

private theorem stroke_split_len (r_m d : ℕ) :
    (d + 2) * (2 ^ (d + 1) * r_m) = 2 ^ (d + 1) * r_m + 2 * ((d + 1) * (2 ^ d * r_m)) := by
  rw [Nat.pow_succ]
  ring

theorem decompDepth_valid (r_m d o : ℕ) (ho : o < (d + 1) * (2 ^ d * r_m)) :
    ValidStrokeCode r_m d (decompDepth r_m d o).1 (decompDepth r_m d o).2.1
      (decompDepth r_m d o).2.2 := by
  induction d generalizing o with
  | zero =>
    simp only [decompDepth, ValidStrokeCode, Nat.zero_le, List.length_nil, Nat.sub_self, pow_zero,
      one_mul, true_and] at ho ⊢
    simpa using ho
  | succ d ih =>
    rw [show d + 1 + 1 = d + 2 from rfl, stroke_split_len] at ho
    simp only [decompDepth]
    split_ifs with h1 h2
    · exact ⟨Nat.zero_le _, rfl, by simpa using h1⟩
    · have ho' : o - 2 ^ (d + 1) * r_m < (d + 1) * (2 ^ d * r_m) := h2
      obtain ⟨hs, hw, hrem⟩ := ih (o - 2 ^ (d + 1) * r_m) ho'
      refine ⟨by omega, by simp [hw], ?_⟩
      simpa [Nat.succ_sub_succ_eq_sub] using hrem
    · have ho'' : o - 2 ^ (d + 1) * r_m - (d + 1) * (2 ^ d * r_m) < (d + 1) * (2 ^ d * r_m) := by
        omega
      obtain ⟨hs, hw, hrem⟩ := ih _ ho''
      refine ⟨by omega, by simp [hw], ?_⟩
      simpa [Nat.succ_sub_succ_eq_sub] using hrem

theorem reconstructDepth_lt (r_m d s : ℕ) (w : List Bool) (rem : ℕ)
    (hv : ValidStrokeCode r_m d s w rem) :
    reconstructDepth r_m d s w rem < (d + 1) * (2 ^ d * r_m) := by
  induction d generalizing s w with
  | zero =>
    obtain ⟨hs, _, hrem⟩ := hv
    have hs0 : s = 0 := by omega
    subst hs0
    simpa [reconstructDepth] using hrem
  | succ d ih =>
    rw [show d + 1 + 1 = d + 2 from rfl, stroke_split_len]
    obtain ⟨hs, hw, hrem⟩ := hv
    cases s with
    | zero =>
      simp only [reconstructDepth]
      simp only [Nat.sub_zero] at hrem
      omega
    | succ s' =>
      cases w with
      | nil => simp at hw
      | cons b w' =>
        simp only [reconstructDepth]
        have hv' : ValidStrokeCode r_m d s' w' rem :=
          ⟨by omega, by simpa using hw, by simpa [Nat.succ_sub_succ_eq_sub] using hrem⟩
        have hlt' := ih s' w' hv'
        cases b <;> simp only [↓reduceIte, Bool.false_eq_true] <;> omega

theorem reconstruct_decomp (r_m d o : ℕ) (ho : o < (d + 1) * (2 ^ d * r_m)) :
    reconstructDepth r_m d (decompDepth r_m d o).1 (decompDepth r_m d o).2.1
      (decompDepth r_m d o).2.2 = o := by
  induction d generalizing o with
  | zero => rfl
  | succ d ih =>
    rw [show d + 1 + 1 = d + 2 from rfl, stroke_split_len] at ho
    simp only [decompDepth]
    split_ifs with h1 h2
    · rfl
    · simp only [reconstructDepth, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      rw [ih _ h2]
      omega
    · simp only [reconstructDepth, ↓reduceIte]
      have ho'' : o - 2 ^ (d + 1) * r_m - (d + 1) * (2 ^ d * r_m) < (d + 1) * (2 ^ d * r_m) := by
        omega
      rw [ih _ ho'']
      omega

theorem decomp_reconstruct (r_m d s : ℕ) (w : List Bool) (rem : ℕ)
    (hv : ValidStrokeCode r_m d s w rem) :
    decompDepth r_m d (reconstructDepth r_m d s w rem) = (s, w, rem) := by
  induction d generalizing s w with
  | zero =>
    obtain ⟨hs, hw, _⟩ := hv
    have hs0 : s = 0 := by omega
    subst hs0
    cases w with
    | nil => rfl
    | cons _ _ => simp at hw
  | succ d ih =>
    obtain ⟨hs, hw, hrem⟩ := hv
    cases s with
    | zero =>
      cases w with
      | nil =>
        simp only [Nat.sub_zero] at hrem
        simp [reconstructDepth, decompDepth, hrem]
      | cons _ _ => simp at hw
    | succ s' =>
      cases w with
      | nil => simp at hw
      | cons b w' =>
        have hv' : ValidStrokeCode r_m d s' w' rem :=
          ⟨by omega, by simpa using hw, by simpa [Nat.succ_sub_succ_eq_sub] using hrem⟩
        have hlt' := reconstructDepth_lt r_m d s' w' rem hv'
        have hih := ih s' w' hv'
        cases b
        · simp only [reconstructDepth, Bool.false_eq_true, ↓reduceIte, Nat.add_zero, decompDepth]
          have hnot1 : ¬ (2 ^ (d + 1) * r_m + reconstructDepth r_m d s' w' rem < 2 ^ (d + 1) * r_m) := by
            omega
          have hsub1 : 2 ^ (d + 1) * r_m + reconstructDepth r_m d s' w' rem - 2 ^ (d + 1) * r_m =
              reconstructDepth r_m d s' w' rem := by omega
          simp only [hnot1, ↓reduceIte, hsub1, hlt', hih]
        · simp only [reconstructDepth, ↓reduceIte, decompDepth]
          have hnot1 : ¬ (2 ^ (d + 1) * r_m + (d + 1) * (2 ^ d * r_m) +
              reconstructDepth r_m d s' w' rem < 2 ^ (d + 1) * r_m) := by omega
          have hsub1 : 2 ^ (d + 1) * r_m + (d + 1) * (2 ^ d * r_m) +
              reconstructDepth r_m d s' w' rem - 2 ^ (d + 1) * r_m =
              (d + 1) * (2 ^ d * r_m) + reconstructDepth r_m d s' w' rem := by omega
          have hnot2 : ¬ ((d + 1) * (2 ^ d * r_m) + reconstructDepth r_m d s' w' rem <
              (d + 1) * (2 ^ d * r_m)) := by omega
          have hsub2 : (d + 1) * (2 ^ d * r_m) + reconstructDepth r_m d s' w' rem -
              (d + 1) * (2 ^ d * r_m) = reconstructDepth r_m d s' w' rem := by omega
          simp only [hnot1, ↓reduceIte, hsub1, hnot2, hsub2, hih]

theorem reconstructDepth_mod_base (r_m d s : ℕ) (w : List Bool) (rem : ℕ) :
    reconstructDepth r_m d s w rem % r_m = rem % r_m := by
  induction d generalizing s w with
  | zero => rfl
  | succ d ih =>
    cases s with
    | zero => rfl
    | succ s' =>
      cases w with
      | nil => rfl
      | cons b w' =>
        simp only [reconstructDepth]
        have hdvd1 : r_m ∣ 2 ^ (d + 1) * r_m := Nat.dvd_mul_left _ _
        have hdvd2 : r_m ∣ (if b then (d + 1) * (2 ^ d * r_m) else 0) := by
          cases b <;> simp [dvd_mul_of_dvd_right]
        have hdvd : r_m ∣ 2 ^ (d + 1) * r_m + (if b then (d + 1) * (2 ^ d * r_m) else 0) :=
          Nat.dvd_add hdvd1 hdvd2
        obtain ⟨k, hk⟩ := hdvd
        rw [hk, Nat.mul_comm r_m k, Nat.mul_add_mod_self_right]
        exact ih s' w'

/-- Decomposition `(stopDepth, branchWord, segRem)` of an offset `o` in a level-`κ` stroke of
`U(s₀, m, 1)`. -/
def decompStroke (s0 m κ o : ℕ) : ℕ × List Bool × ℕ :=
  decompDepth (scaleR s0 m) (m - κ) o

/-- Reconstruction of an offset in a level-`κ` stroke of `U(s₀, m, 1)`. -/
def reconstructStroke (s0 m κ s : ℕ) (w : List Bool) (rem : ℕ) : ℕ :=
  reconstructDepth (scaleR s0 m) (m - κ) s w rem

/-! ### Part 2: Uniform stopping depth, fair-coin directions, and parity preservation -/

/-- **Proposition SL(a)** (Joint stopping-depth & nested-direction count):
In a level-`κ` stroke (`κ ≤ m ≤ s₀`), for every stopping depth `s ≤ m - κ` and every direction
word `w ∈ {false, true}^s` of length `s`, the number of offsets `o ∈ [0, Π_κ)` with stopping
depth `s` and branch word `w` is `R_{κ + s}`, where `2^s · R_{κ + s} = R_κ`. -/
theorem card_stroke_stopDepth_branchWord {s0 m κ s : ℕ} (hκ : κ ≤ m) (hms : m ≤ s0)
    (hs : s ≤ m - κ) (w : List Bool) (hw : w.length = s) :
    ((range (strokeLen s0 m κ)).filter
      (fun o => (decompStroke s0 m κ o).1 = s ∧ (decompStroke s0 m κ o).2.1 = w)).card =
      scaleR s0 (κ + s) ∧
    2 ^ s * scaleR s0 (κ + s) = scaleR s0 κ := by
  have hpow : 2 ^ s * scaleR s0 (κ + s) = scaleR s0 κ := by
    unfold scaleR
    rw [← Nat.pow_add, show s + (s0 - (κ + s)) = s0 - κ by omega]
  refine ⟨?_, hpow⟩
  have hpi := strokeLen_eq_pow_mul hκ hms
  have hrs := scaleR_eq_pow_mul (by omega : κ + s ≤ m) hms
  symm
  rw [← Finset.card_range (scaleR s0 (κ + s))]
  refine Finset.card_bij (fun rem _ => reconstructStroke s0 m κ s w rem) ?_ ?_ ?_
  · intro rem hrem
    have hrem_lt : rem < 2 ^ (m - κ - s) * scaleR s0 m := by
      rw [mem_range, hrs] at hrem; exact hrem
    have hv : ValidStrokeCode (scaleR s0 m) (m - κ) s w rem := ⟨hs, hw, hrem_lt⟩
    rw [mem_filter, mem_range]
    refine ⟨?_, ?_⟩
    · rw [hpi]; exact reconstructDepth_lt _ _ _ _ _ hv
    · simp only [decompStroke, reconstructStroke, decomp_reconstruct _ _ _ _ _ hv, and_self]
  · intro r₁ hr₁ r₂ hr₂ heq
    have h1 : r₁ < 2 ^ (m - κ - s) * scaleR s0 m := by rw [mem_range, hrs] at hr₁; exact hr₁
    have h2 : r₂ < 2 ^ (m - κ - s) * scaleR s0 m := by rw [mem_range, hrs] at hr₂; exact hr₂
    have hd1 := decomp_reconstruct (scaleR s0 m) (m - κ) s w r₁ ⟨hs, hw, h1⟩
    have hd2 := decomp_reconstruct (scaleR s0 m) (m - κ) s w r₂ ⟨hs, hw, h2⟩
    have heq' : decompDepth (scaleR s0 m) (m - κ) (reconstructStroke s0 m κ s w r₁) =
        decompDepth (scaleR s0 m) (m - κ) (reconstructStroke s0 m κ s w r₂) :=
      congrArg _ heq
    simp only [reconstructStroke, hd1, hd2, Prod.mk.injEq] at heq'
    exact heq'.2.2
  · intro o ho
    rw [mem_filter, mem_range] at ho
    obtain ⟨ho_lt, hs_eq, hw_eq⟩ := ho
    rw [hpi] at ho_lt
    have hv := decompDepth_valid (scaleR s0 m) (m - κ) o ho_lt
    have hrec := reconstruct_decomp (scaleR s0 m) (m - κ) o ho_lt
    refine ⟨(decompStroke s0 m κ o).2.2, ?_, ?_⟩
    · rw [mem_range, hrs]
      have hrem := hv.2.2
      simp only [decompStroke] at hs_eq ⊢
      rwa [hs_eq] at hrem
    · simp only [reconstructStroke, decompStroke] at hs_eq hw_eq ⊢
      rw [← hs_eq, ← hw_eq]
      exact hrec

private theorem ofFn_inj {α : Type*} {n : ℕ} :
    Function.Injective (List.ofFn : (Fin n → α) → List α) := by
  intro f₁ f₂ h
  funext i
  have hi : (List.ofFn f₁)[i.val]'(by simp) = (List.ofFn f₂)[i.val]'(by simp) := by
    simp only [h]
  simpa [List.getElem_ofFn] using hi

/-- **Proposition SL(a')** (Uniform stopping depth):
In a level-`κ` stroke (`κ ≤ m ≤ s₀`), every stopping depth `s ∈ {0, …, m - κ}` occurs on
exactly `R_κ` offsets out of `Π_κ = (m - κ + 1) R_κ`. -/
theorem card_stroke_stopDepth {s0 m κ s : ℕ} (hκ : κ ≤ m) (hms : m ≤ s0) (hs : s ≤ m - κ) :
    ((range (strokeLen s0 m κ)).filter (fun o => (decompStroke s0 m κ o).1 = s)).card =
      scaleR s0 κ := by
  classical
  let fiber : (Fin s → Bool) → Finset ℕ := fun f =>
    (range (strokeLen s0 m κ)).filter
      (fun o => (decompStroke s0 m κ o).1 = s ∧ (decompStroke s0 m κ o).2.1 = List.ofFn f)
  have hpart : (range (strokeLen s0 m κ)).filter (fun o => (decompStroke s0 m κ o).1 = s) =
      (univ : Finset (Fin s → Bool)).biUnion fiber := by
    ext o
    simp only [mem_filter, mem_range, mem_biUnion, mem_univ, true_and, fiber]
    constructor
    · rintro ⟨ho, hso⟩
      have hpi := strokeLen_eq_pow_mul hκ hms
      have hv := decompDepth_valid (scaleR s0 m) (m - κ) o (hpi ▸ ho)
      have hlen : (decompStroke s0 m κ o).2.1.length = s := by
        unfold decompStroke at hso ⊢
        rw [hv.2.1, hso]
      let f : Fin s → Bool := fun i => (decompStroke s0 m κ o).2.1[i.val]'(by omega)
      refine ⟨f, ho, hso, ?_⟩
      apply List.ext_getElem (by simp [hlen])
      intro i hi1 hi2
      simp [f, List.getElem_ofFn]
    · rintro ⟨_, ho, hso, _⟩
      exact ⟨ho, hso⟩
  have hdisj : Set.PairwiseDisjoint (↑(univ : Finset (Fin s → Bool)) : Set (Fin s → Bool)) fiber := by
    intro f₁ _ f₂ _ hne
    change Disjoint (fiber f₁) (fiber f₂)
    rw [Finset.disjoint_left]
    intro o h1 h2
    have hw1 := (mem_filter.mp h1).2.2
    have hw2 := (mem_filter.mp h2).2.2
    exact hne (ofFn_inj (hw1.symm.trans hw2))
  rw [hpart, Finset.card_biUnion hdisj]
  have hcard_each : ∀ f : Fin s → Bool, (fiber f).card = scaleR s0 (κ + s) :=
    fun f => (card_stroke_stopDepth_branchWord hκ hms hs (List.ofFn f) List.length_ofFn).1
  simp only [hcard_each, sum_const, card_univ, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_bool, smul_eq_mul]
  exact (card_stroke_stopDepth_branchWord hκ hms hs (List.replicate s false)
    (List.length_replicate)).2

/-- **Proposition SL(b)** (Parity-conditioned joint stopping-depth & nested-direction count):
When `m < s₀` (so `R_m ≥ 2` is even), for every parity `p : Fin 2`, stopping depth `s ≤ m - κ`,
and direction word `w` of length `s`, the number of offsets `o ∈ [0, Π_κ)` with `o % 2 = p` and
decomposition `(s, w)` is `R_{κ + s} / 2`. -/
theorem card_stroke_stopDepth_branchWord_parity {s0 m κ s : ℕ} (hκ : κ ≤ m) (hms : m < s0)
    (hs : s ≤ m - κ) (p : Fin 2) (w : List Bool) (hw : w.length = s) :
    ((range (strokeLen s0 m κ)).filter
      (fun o => o % 2 = p.val ∧ (decompStroke s0 m κ o).1 = s ∧
        (decompStroke s0 m κ o).2.1 = w)).card =
      scaleR s0 (κ + s) / 2 := by
  have hms_le : m ≤ s0 := Nat.le_of_lt hms
  have heven_rm : 2 ∣ scaleR s0 m := even_scaleR hms
  have heven_rs : 2 ∣ scaleR s0 (κ + s) := even_scaleR (by omega)
  have hpi := strokeLen_eq_pow_mul hκ hms_le
  have hrs := scaleR_eq_pow_mul (by omega : κ + s ≤ m) hms_le
  have hp_lt : p.val < 2 := p.isLt
  have hmod2 : ∀ rem, reconstructStroke s0 m κ s w rem % 2 = rem % 2 := by
    intro rem
    have hrm := reconstructDepth_mod_base (scaleR s0 m) (m - κ) s w rem
    have h1 := Nat.mod_mod_of_dvd (reconstructStroke s0 m κ s w rem) heven_rm
    have h2 := Nat.mod_mod_of_dvd rem heven_rm
    unfold reconstructStroke at h1 ⊢
    rw [← h1, hrm, h2]
  symm
  rw [← Finset.card_range (scaleR s0 (κ + s) / 2)]
  refine Finset.card_bij (fun k _ => reconstructStroke s0 m κ s w (2 * k + p.val)) ?_ ?_ ?_
  · intro k hk
    rw [mem_range] at hk
    obtain ⟨m2, hm2⟩ := heven_rs
    have hrem_lt_rs : 2 * k + p.val < scaleR s0 (κ + s) := by omega
    have hrem_lt : 2 * k + p.val < 2 ^ (m - κ - s) * scaleR s0 m := hrs ▸ hrem_lt_rs
    have hv : ValidStrokeCode (scaleR s0 m) (m - κ) s w (2 * k + p.val) := ⟨hs, hw, hrem_lt⟩
    rw [mem_filter, mem_range]
    refine ⟨hpi ▸ reconstructDepth_lt _ _ _ _ _ hv, ?_, ?_⟩
    · rw [hmod2]; omega
    · simp only [decompStroke, reconstructStroke, decomp_reconstruct _ _ _ _ _ hv, and_self]
  · intro k₁ hk₁ k₂ hk₂ heq
    rw [mem_range] at hk₁ hk₂
    obtain ⟨m2, hm2⟩ := heven_rs
    have h1 : 2 * k₁ + p.val < 2 ^ (m - κ - s) * scaleR s0 m := hrs ▸ (by omega)
    have h2 : 2 * k₂ + p.val < 2 ^ (m - κ - s) * scaleR s0 m := hrs ▸ (by omega)
    have hd1 := decomp_reconstruct (scaleR s0 m) (m - κ) s w (2 * k₁ + p.val) ⟨hs, hw, h1⟩
    have hd2 := decomp_reconstruct (scaleR s0 m) (m - κ) s w (2 * k₂ + p.val) ⟨hs, hw, h2⟩
    have heq' : decompDepth (scaleR s0 m) (m - κ) (reconstructStroke s0 m κ s w (2 * k₁ + p.val)) =
        decompDepth (scaleR s0 m) (m - κ) (reconstructStroke s0 m κ s w (2 * k₂ + p.val)) :=
      congrArg _ heq
    simp only [reconstructStroke, hd1, hd2, Prod.mk.injEq] at heq'
    omega
  · intro o ho
    rw [mem_filter, mem_range] at ho
    obtain ⟨ho_lt, ho_par, hs_eq, hw_eq⟩ := ho
    have hv := decompDepth_valid (scaleR s0 m) (m - κ) o (hpi ▸ ho_lt)
    have hrec := reconstruct_decomp (scaleR s0 m) (m - κ) o (hpi ▸ ho_lt)
    let rem := (decompStroke s0 m κ o).2.2
    have hrem_lt : rem < scaleR s0 (κ + s) := by
      rw [hrs]
      have hr := hv.2.2
      simp only [decompStroke] at hs_eq
      rwa [hs_eq] at hr
    have ho_re : reconstructStroke s0 m κ s w rem = o := by
      simp only [reconstructStroke, decompStroke, rem] at hs_eq hw_eq ⊢
      rw [← hs_eq, ← hw_eq]
      exact hrec
    have hrem_par : rem % 2 = p.val := by
      have := hmod2 rem
      rw [ho_re] at this
      omega
    refine ⟨rem / 2, ?_, ?_⟩
    · rw [mem_range]
      obtain ⟨m2, hm2⟩ := heven_rs
      omega
    · rw [show 2 * (rem / 2) + p.val = rem by omega]
      exact ho_re

/-- **Proposition SL(b')** (Parity-conditioned uniform stopping depth):
When `m < s₀`, for every parity `p : Fin 2` and stopping depth `s ≤ m - κ`, the number of offsets
`o ∈ [0, Π_κ)` with `o % 2 = p` and stopping depth `s` is `R_κ / 2`. -/
theorem card_stroke_stopDepth_parity {s0 m κ s : ℕ} (hκ : κ ≤ m) (hms : m < s0)
    (hs : s ≤ m - κ) (p : Fin 2) :
    ((range (strokeLen s0 m κ)).filter
      (fun o => o % 2 = p.val ∧ (decompStroke s0 m κ o).1 = s)).card =
      scaleR s0 κ / 2 := by
  classical
  have hms_le : m ≤ s0 := Nat.le_of_lt hms
  let fiber : (Fin s → Bool) → Finset ℕ := fun f =>
    (range (strokeLen s0 m κ)).filter
      (fun o => o % 2 = p.val ∧ (decompStroke s0 m κ o).1 = s ∧
        (decompStroke s0 m κ o).2.1 = List.ofFn f)
  have hpart : (range (strokeLen s0 m κ)).filter
      (fun o => o % 2 = p.val ∧ (decompStroke s0 m κ o).1 = s) =
      (univ : Finset (Fin s → Bool)).biUnion fiber := by
    ext o
    simp only [mem_filter, mem_range, mem_biUnion, mem_univ, true_and, fiber]
    constructor
    · rintro ⟨ho, hp, hso⟩
      have hpi := strokeLen_eq_pow_mul hκ hms_le
      have hv := decompDepth_valid (scaleR s0 m) (m - κ) o (hpi ▸ ho)
      have hlen : (decompStroke s0 m κ o).2.1.length = s := by
        unfold decompStroke at hso ⊢
        rw [hv.2.1, hso]
      let f : Fin s → Bool := fun i => (decompStroke s0 m κ o).2.1[i.val]'(by omega)
      refine ⟨f, ho, hp, hso, ?_⟩
      apply List.ext_getElem (by simp [hlen])
      intro i hi1 hi2
      simp [f, List.getElem_ofFn]
    · rintro ⟨_, ho, hp, hso, _⟩
      exact ⟨ho, hp, hso⟩
  have hdisj : Set.PairwiseDisjoint (↑(univ : Finset (Fin s → Bool)) : Set (Fin s → Bool)) fiber := by
    intro f₁ _ f₂ _ hne
    change Disjoint (fiber f₁) (fiber f₂)
    rw [Finset.disjoint_left]
    intro o h1 h2
    exact hne (ofFn_inj ((mem_filter.mp h1).2.2.2.symm.trans (mem_filter.mp h2).2.2.2))
  rw [hpart, Finset.card_biUnion hdisj]
  have hcard_each : ∀ f : Fin s → Bool, (fiber f).card = scaleR s0 (κ + s) / 2 :=
    fun f => card_stroke_stopDepth_branchWord_parity hκ hms hs p (List.ofFn f) List.length_ofFn
  simp only [hcard_each, sum_const, card_univ, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_bool, smul_eq_mul]
  obtain ⟨q2, hq2⟩ := even_scaleR (by omega : κ + s < s0)
  have hpow := (card_stroke_stopDepth_branchWord hκ hms_le hs (List.replicate s false)
    List.length_replicate).2
  have hmul : scaleR s0 κ = 2 * (2 ^ s * q2) := by rw [← hpow, hq2]; ring
  set x := 2 ^ s * q2
  have h1 : scaleR s0 (κ + s) / 2 = q2 := by omega
  have h2 : scaleR s0 κ / 2 = x := by omega
  rw [h1, h2]

/-! ### Part 3: `O(m)` recursive turn-potential evaluator and equivalence with turn jumps -/

/-- Total turn-jump mass `M(V_{κ+1}) = ∑_{l = κ + 1}^m c_f(l)` of the inner V inside a level-`κ`
stroke (`0` when `κ ≥ m`). -/
def strokeMass (m : ℕ) (cf : ℕ → ℤ) (κ : ℕ) : ℤ :=
  ∑ l ∈ Icc (κ + 1) m, cf l

theorem strokeMass_eq_zero {m : ℕ} (cf : ℕ → ℤ) {κ : ℕ} (h : m ≤ κ) :
    strokeMass m cf κ = 0 := by
  unfold strokeMass
  have hemp : Icc (κ + 1) m = ∅ := Icc_eq_empty (by omega)
  simp [hemp]

theorem strokeMass_succ {m : ℕ} (cf : ℕ → ℤ) {κ : ℕ} (h : κ < m) :
    strokeMass m cf κ = cf (κ + 1) + strokeMass m cf (κ + 1) := by
  unfold strokeMass
  have hset : Icc (κ + 1) m = insert (κ + 1) (Icc (κ + 1 + 1) m) := by
    ext x; simp only [mem_Icc, mem_insert]; omega
  rw [hset, Finset.sum_insert (by simp)]

/-- Auxiliary `O(d)` recursive evaluator for the potential inside a level-`κ` stroke with remaining
nesting depth `d = m - κ`. -/
def strokePhiAux (s0 m : ℕ) (cb cf : ℕ → ℤ) (κ : ℕ) : ℕ → ℕ → ℤ
  | 0, _ => 0
  | d + 1, o =>
    let rCur := scaleR s0 κ
    if o < rCur then 0
    else
      let o' := o - rCur
      let piNext := strokeLen s0 m (κ + 1)
      if o' < piNext then cb (κ + 1) + strokePhiAux s0 m cb cf (κ + 1) d o'
      else cf (κ + 1) + strokePhiAux s0 m cb cf (κ + 1) d (o' - piNext)

/-- `O(m - κ)` recursive potential increment `Y_κ(o)` at offset `o ∈ [0, Π_κ)` inside a level-`κ`
stroke of `U(s₀, m, 1)`. -/
def strokePhiRec (s0 m : ℕ) (cb cf : ℕ → ℤ) (κ o : ℕ) : ℤ :=
  strokePhiAux s0 m cb cf κ (m - κ) o

/-- Back-stroke path-sum decomposition along the V of level `κ` (`1 ≤ κ ≤ m`) inside a
level-`(κ - 1)` stroke: at offset `o < Π_κ` from the apex `R_{κ - 1}`, the stroke potential is
`cb κ + strokePhiRec ... κ o`. -/
theorem strokePhiRec_back {s0 m : ℕ} (cb cf : ℕ → ℤ) {κ o : ℕ}
    (hκ1 : 1 ≤ κ) (hκm : κ ≤ m) (ho : o < strokeLen s0 m κ) :
    strokePhiRec s0 m cb cf (κ - 1) (scaleR s0 (κ - 1) + o) =
      cb κ + strokePhiRec s0 m cb cf κ o := by
  unfold strokePhiRec
  rw [show m - (κ - 1) = (m - κ) + 1 by omega]
  simp only [strokePhiAux, show κ - 1 + 1 = κ by omega]
  have hnot : ¬ (scaleR s0 (κ - 1) + o < scaleR s0 (κ - 1)) := by omega
  have hsub : scaleR s0 (κ - 1) + o - scaleR s0 (κ - 1) = o := by omega
  simp [hnot, hsub, ho]

/-- Forward-stroke path-sum decomposition along the V of level `κ` (`1 ≤ κ ≤ m`) inside a
level-`(κ - 1)` stroke: at offset `o < Π_κ` from the valley `R_{κ - 1} + Π_κ`, the stroke
potential is `cf κ + strokePhiRec ... κ o`. -/
theorem strokePhiRec_fwd {s0 m : ℕ} (cb cf : ℕ → ℤ) {κ o : ℕ}
    (hκ1 : 1 ≤ κ) (hκm : κ ≤ m) (_ho : o < strokeLen s0 m κ) :
    strokePhiRec s0 m cb cf (κ - 1) (scaleR s0 (κ - 1) + strokeLen s0 m κ + o) =
      cf κ + strokePhiRec s0 m cb cf κ o := by
  unfold strokePhiRec
  rw [show m - (κ - 1) = (m - κ) + 1 by omega]
  simp only [strokePhiAux, show κ - 1 + 1 = κ by omega]
  have hnot1 : ¬ (scaleR s0 (κ - 1) + strokeLen s0 m κ + o < scaleR s0 (κ - 1)) := by omega
  have hsub1 : scaleR s0 (κ - 1) + strokeLen s0 m κ + o - scaleR s0 (κ - 1) =
      strokeLen s0 m κ + o := by omega
  have hnot2 : ¬ (strokeLen s0 m κ + o < strokeLen s0 m κ) := by omega
  have hsub2 : strokeLen s0 m κ + o - strokeLen s0 m κ = o := by omega
  simp [hnot1, hsub1, hnot2, hsub2]

/-- Explicit turn jump at internal step `τ` (`1 ≤ τ < Π_κ`) inside a level-`κ` stroke with
remaining nesting depth `d = m - κ`, matching `J(α_V) = c_b(l)` at apex turns and
`J(ν_V) = c_f(l) - c_b(l) - M(V^b)` at valley turns. -/
def strokeTurnJumpAux (s0 m : ℕ) (cb cf : ℕ → ℤ) (κ : ℕ) : ℕ → ℕ → ℤ
  | 0, _ => 0
  | d + 1, τ =>
    let rCur := scaleR s0 κ
    let piNext := strokeLen s0 m (κ + 1)
    if τ < rCur then 0
    else if τ = rCur then cb (κ + 1)
    else if τ < rCur + piNext then strokeTurnJumpAux s0 m cb cf (κ + 1) d (τ - rCur)
    else if τ = rCur + piNext then cf (κ + 1) - cb (κ + 1) - strokeMass m cf (κ + 1)
    else if τ < rCur + 2 * piNext then
      strokeTurnJumpAux s0 m cb cf (κ + 1) d (τ - rCur - piNext)
    else 0

/-- Turn jump at internal step `τ` inside a level-`κ` stroke of `U(s₀, m, 1)`. -/
def strokeTurnJump (s0 m : ℕ) (cb cf : ℕ → ℤ) (κ τ : ℕ) : ℤ :=
  strokeTurnJumpAux s0 m cb cf κ (m - κ) τ

private theorem sum_Ioc_split (f : ℕ → ℤ) {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    ∑ x ∈ Ioc a c, f x = (∑ x ∈ Ioc a b, f x) + ∑ x ∈ Ioc b c, f x := by
  have hunion : Ioc a c = Ioc a b ∪ Ioc b c := by
    ext x; simp only [mem_Ioc, mem_union]; omega
  have hdisj : Disjoint (Ioc a b) (Ioc b c) := by
    rw [Finset.disjoint_left]; intro x hx1 hx2; rw [mem_Ioc] at hx1 hx2; omega
  rw [hunion, Finset.sum_union hdisj]

private theorem sum_Ioc_shift_sub (f : ℕ → ℤ) (a n : ℕ) :
    ∑ τ ∈ Ioc a (a + n), f (τ - a) = ∑ k ∈ Ioc 0 n, f k := by
  refine Finset.sum_bij (fun τ _ => τ - a) ?_ ?_ ?_ ?_
  · intro τ hτ; rw [mem_Ioc] at hτ ⊢; omega
  · intro τ₁ h₁ τ₂ h₂ heq; rw [mem_Ioc] at h₁ h₂; omega
  · intro k hk; rw [mem_Ioc] at hk
    exact ⟨a + k, mem_Ioc.mpr ⟨by omega, by omega⟩, by omega⟩
  · intros; rfl

private theorem strokeTurnJumpAux_end_zero (s0 m : ℕ) (cb cf : ℕ → ℤ) (hms : m ≤ s0)
    (i d : ℕ) (hid : i + d = m) :
    strokeTurnJumpAux s0 m cb cf i d (strokeLen s0 m i) = 0 := by
  cases d with
  | zero => rfl
  | succ d' =>
    have hi_lt : i < m := by omega
    have hsp := strokeLen_succ hi_lt hms
    have hp1 := strokeLen_pos s0 m (i + 1)
    have h1 : ¬ (strokeLen s0 m i < scaleR s0 i) := by omega
    have h2 : strokeLen s0 m i ≠ scaleR s0 i := by omega
    have h3 : ¬ (strokeLen s0 m i < scaleR s0 i + strokeLen s0 m (i + 1)) := by omega
    have h4 : strokeLen s0 m i ≠ scaleR s0 i + strokeLen s0 m (i + 1) := by omega
    have h5 : ¬ (strokeLen s0 m i < scaleR s0 i + 2 * strokeLen s0 m (i + 1)) := by omega
    simp [strokeTurnJumpAux, h1, h2, h3, h4, h5]

private theorem sum_strokeTurnJumpAux_full (s0 m : ℕ) (cb cf : ℕ → ℤ) (hms : m ≤ s0) :
    ∀ (d κ : ℕ), κ + d = m →
      ∑ τ ∈ Ioc 0 (strokeLen s0 m κ), strokeTurnJumpAux s0 m cb cf κ d τ = strokeMass m cf κ := by
  intro d
  induction d with
  | zero =>
    intro κ hκ
    rw [strokeMass_eq_zero cf (by omega)]
    simp [strokeTurnJumpAux]
  | succ d ih =>
    intro κ hκ
    have hκ_lt : κ < m := by omega
    have hsplit := strokeLen_succ hκ_lt hms
    set rCur := scaleR s0 κ
    set piNext := strokeLen s0 m (κ + 1)
    have hr_pos : 0 < rCur := scaleR_pos s0 κ
    have hpi_pos : 0 < piNext := strokeLen_pos s0 m (κ + 1)
    -- Split `(0, rCur + 2 * piNext]` at `rCur`, `rCur + piNext`
    rw [hsplit]
    rw [sum_Ioc_split _ (by omega : 0 ≤ rCur) (by omega : rCur ≤ rCur + 2 * piNext)]
    rw [sum_Ioc_split _ (by omega : rCur ≤ rCur + piNext)
      (by omega : rCur + piNext ≤ rCur + 2 * piNext)]
    -- First segment `(0, rCur]`: `(0, rCur - 1]` is `0`, `rCur` gives `cb (κ + 1)`
    have hseg1 : ∑ x ∈ Ioc 0 rCur, strokeTurnJumpAux s0 m cb cf κ (d + 1) x = cb (κ + 1) := by
      rw [sum_Ioc_split _ (by omega : 0 ≤ rCur - 1) (by omega : rCur - 1 ≤ rCur)]
      have h0 : ∑ x ∈ Ioc 0 (rCur - 1), strokeTurnJumpAux s0 m cb cf κ (d + 1) x = 0 := by
        apply Finset.sum_eq_zero
        intro x hx; rw [mem_Ioc] at hx
        have hlt : x < scaleR s0 κ := by omega
        simp [strokeTurnJumpAux, hlt]
      have h1 : Ioc (rCur - 1) rCur = {rCur} := by
        ext x; simp only [mem_Ioc, mem_singleton]; omega
      rw [h0, zero_add, h1, Finset.sum_singleton]
      simp [strokeTurnJumpAux, rCur]
    -- Second segment `(rCur, rCur + piNext]`: `(rCur, rCur + piNext - 1]` gives `M(V^b)`, endpoint gives valley jump
    have hseg2 : ∑ x ∈ Ioc rCur (rCur + piNext), strokeTurnJumpAux s0 m cb cf κ (d + 1) x =
        cf (κ + 1) - cb (κ + 1) := by
      rw [sum_Ioc_split _ (by omega : rCur ≤ rCur + (piNext - 1))
        (by omega : rCur + (piNext - 1) ≤ rCur + piNext)]
      have hback : ∑ x ∈ Ioc rCur (rCur + (piNext - 1)),
          strokeTurnJumpAux s0 m cb cf κ (d + 1) x = strokeMass m cf (κ + 1) := by
        have heq_f : ∀ x ∈ Ioc rCur (rCur + (piNext - 1)),
            strokeTurnJumpAux s0 m cb cf κ (d + 1) x =
              strokeTurnJumpAux s0 m cb cf (κ + 1) d (x - rCur) := by
          intro x hx; rw [mem_Ioc] at hx
          have h1 : ¬ (x < scaleR s0 κ) := by omega
          have h2 : x ≠ scaleR s0 κ := by omega
          have h3 : x < scaleR s0 κ + strokeLen s0 m (κ + 1) := by omega
          simp [strokeTurnJumpAux, h1, h2, h3, rCur]
        rw [Finset.sum_congr rfl heq_f, sum_Ioc_shift_sub]
        have hfull := ih (κ + 1) (by omega)
        rw [sum_Ioc_split _ (by omega : 0 ≤ piNext - 1) (by omega : piNext - 1 ≤ piNext)]
          at hfull
        have hend : Ioc (piNext - 1) piNext = {piNext} := by
          ext x; simp only [mem_Ioc, mem_singleton]; omega
        have hend0 : strokeTurnJumpAux s0 m cb cf (κ + 1) d piNext = 0 :=
          strokeTurnJumpAux_end_zero s0 m cb cf hms (κ + 1) d (by omega)
        rw [hend, Finset.sum_singleton, hend0, add_zero] at hfull
        exact hfull
      have hval_set : Ioc (rCur + (piNext - 1)) (rCur + piNext) = {rCur + piNext} := by
        ext x; simp only [mem_Ioc, mem_singleton]; omega
      have hval_eq : strokeTurnJumpAux s0 m cb cf κ (d + 1) (rCur + piNext) =
          cf (κ + 1) - cb (κ + 1) - strokeMass m cf (κ + 1) := by
        change strokeTurnJumpAux s0 m cb cf κ (d + 1) (scaleR s0 κ + strokeLen s0 m (κ + 1)) = _
        have h1 : ¬ (scaleR s0 κ + strokeLen s0 m (κ + 1) < scaleR s0 κ) := by omega
        have hpi_ne : strokeLen s0 m (κ + 1) ≠ 0 := by omega
        simp [strokeTurnJumpAux, h1, hpi_ne]
      rw [hback, hval_set, Finset.sum_singleton, hval_eq]
      ring
    -- Third segment `(rCur + piNext, rCur + 2 * piNext]`: gives `strokeMass m cf (κ + 1)`
    have hseg3 : ∑ x ∈ Ioc (rCur + piNext) (rCur + 2 * piNext),
        strokeTurnJumpAux s0 m cb cf κ (d + 1) x = strokeMass m cf (κ + 1) := by
      rw [sum_Ioc_split _ (by omega : rCur + piNext ≤ (rCur + piNext) + (piNext - 1))
        (by omega : (rCur + piNext) + (piNext - 1) ≤ rCur + 2 * piNext)]
      have hfwd : ∑ x ∈ Ioc (rCur + piNext) ((rCur + piNext) + (piNext - 1)),
          strokeTurnJumpAux s0 m cb cf κ (d + 1) x = strokeMass m cf (κ + 1) := by
        have heq_f : ∀ x ∈ Ioc (rCur + piNext) ((rCur + piNext) + (piNext - 1)),
            strokeTurnJumpAux s0 m cb cf κ (d + 1) x =
              strokeTurnJumpAux s0 m cb cf (κ + 1) d (x - (rCur + piNext)) := by
          intro x hx; rw [mem_Ioc] at hx
          have h1 : ¬ (x < scaleR s0 κ) := by omega
          have h2 : x ≠ scaleR s0 κ := by omega
          have h3 : ¬ (x < scaleR s0 κ + strokeLen s0 m (κ + 1)) := by omega
          have h4 : x ≠ scaleR s0 κ + strokeLen s0 m (κ + 1) := by omega
          have h5 : x < scaleR s0 κ + 2 * strokeLen s0 m (κ + 1) := by omega
          have hsub : x - scaleR s0 κ - strokeLen s0 m (κ + 1) = x - (rCur + piNext) := by omega
          simp [strokeTurnJumpAux, h1, h2, h3, h4, h5, hsub]
        rw [Finset.sum_congr rfl heq_f, sum_Ioc_shift_sub]
        have hfull := ih (κ + 1) (by omega)
        rw [sum_Ioc_split _ (by omega : 0 ≤ piNext - 1) (by omega : piNext - 1 ≤ piNext)]
          at hfull
        have hend : Ioc (piNext - 1) piNext = {piNext} := by
          ext x; simp only [mem_Ioc, mem_singleton]; omega
        have hend0 : strokeTurnJumpAux s0 m cb cf (κ + 1) d piNext = 0 :=
          strokeTurnJumpAux_end_zero s0 m cb cf hms (κ + 1) d (by omega)
        rw [hend, Finset.sum_singleton, hend0, add_zero] at hfull
        exact hfull
      have hend_set : Ioc ((rCur + piNext) + (piNext - 1)) (rCur + 2 * piNext) =
          {rCur + 2 * piNext} := by
        ext x; simp only [mem_Ioc, mem_singleton]; omega
      have hend0 : strokeTurnJumpAux s0 m cb cf κ (d + 1) (rCur + 2 * piNext) = 0 := by
        have h1 : ¬ (rCur + 2 * piNext < scaleR s0 κ) := by omega
        have h2 : rCur + 2 * piNext ≠ scaleR s0 κ := by omega
        have h3 : ¬ (rCur + 2 * piNext < scaleR s0 κ + strokeLen s0 m (κ + 1)) := by omega
        have h4 : rCur + 2 * piNext ≠ scaleR s0 κ + strokeLen s0 m (κ + 1) := by omega
        have h5 : ¬ (rCur + 2 * piNext < scaleR s0 κ + 2 * strokeLen s0 m (κ + 1)) := by omega
        simp [strokeTurnJumpAux, h1, h2, h3, h4, h5]
      rw [hfwd, hend_set, Finset.sum_singleton, hend0, add_zero]
    rw [hseg1, hseg2, hseg3, strokeMass_succ cf hκ_lt]
    ring

/-- Inside any level-`κ` stroke (`κ ≤ m ≤ s₀`), the `O(m - κ)` recursive formula `strokePhiRec`
equals the cumulative sum of explicit turn jumps `strokeTurnJump` over `(0, o]`. -/
theorem strokePhiRec_eq_sum_turnJumps {s0 m : ℕ} (cb cf : ℕ → ℤ) (hms : m ≤ s0)
    {κ o : ℕ} (hκ : κ ≤ m) (ho : o < strokeLen s0 m κ) :
    strokePhiRec s0 m cb cf κ o = ∑ τ ∈ Ioc 0 o, strokeTurnJump s0 m cb cf κ τ := by
  unfold strokePhiRec strokeTurnJump
  have hκd : κ + (m - κ) = m := by omega
  generalize m - κ = d at hκd ⊢
  induction d generalizing κ o with
  | zero => simp [strokePhiAux, strokeTurnJumpAux]
  | succ d ih =>
    have hκ_lt : κ < m := by omega
    have hsplit := strokeLen_succ hκ_lt hms
    set rCur := scaleR s0 κ
    set piNext := strokeLen s0 m (κ + 1)
    have hr_pos : 0 < rCur := scaleR_pos s0 κ
    have hpi_pos : 0 < piNext := strokeLen_pos s0 m (κ + 1)
    simp only [strokePhiAux]
    split_ifs with h1 h2
    · symm
      apply Finset.sum_eq_zero
      intro τ hτ; rw [mem_Ioc] at hτ
      have hlt : τ < scaleR s0 κ := by omega
      simp [strokeTurnJumpAux, hlt]
    · -- `rCur ≤ o < rCur + piNext`
      rw [sum_Ioc_split _ (by omega : 0 ≤ rCur) (by omega : rCur ≤ o)]
      have hseg1 : ∑ x ∈ Ioc 0 rCur, strokeTurnJumpAux s0 m cb cf κ (d + 1) x = cb (κ + 1) := by
        rw [sum_Ioc_split _ (by omega : 0 ≤ rCur - 1) (by omega : rCur - 1 ≤ rCur)]
        have h0 : ∑ x ∈ Ioc 0 (rCur - 1), strokeTurnJumpAux s0 m cb cf κ (d + 1) x = 0 := by
          apply Finset.sum_eq_zero
          intro x hx; rw [mem_Ioc] at hx
          have hlt : x < scaleR s0 κ := by omega
          simp [strokeTurnJumpAux, hlt]
        have h1s : Ioc (rCur - 1) rCur = {rCur} := by
          ext x; simp only [mem_Ioc, mem_singleton]; omega
        rw [h0, zero_add, h1s, Finset.sum_singleton]
        simp [strokeTurnJumpAux, rCur]
      have hseg2 : ∑ x ∈ Ioc rCur o, strokeTurnJumpAux s0 m cb cf κ (d + 1) x =
          ∑ k ∈ Ioc 0 (o - rCur), strokeTurnJumpAux s0 m cb cf (κ + 1) d k := by
        have heq_f : ∀ x ∈ Ioc rCur o,
            strokeTurnJumpAux s0 m cb cf κ (d + 1) x =
              strokeTurnJumpAux s0 m cb cf (κ + 1) d (x - rCur) := by
          intro x hx; rw [mem_Ioc] at hx
          have ha : ¬ (x < scaleR s0 κ) := by omega
          have hb : x ≠ scaleR s0 κ := by omega
          have hc : x < scaleR s0 κ + strokeLen s0 m (κ + 1) := by omega
          simp [strokeTurnJumpAux, ha, hb, hc, rCur]
        rw [Finset.sum_congr rfl heq_f, ← sum_Ioc_shift_sub]
        have : rCur + (o - rCur) = o := by omega
        rw [this]
      rw [hseg1, hseg2, ih (by omega) h2 (by omega)]
    · -- `rCur + piNext ≤ o < rCur + 2 * piNext`
      have ho'' : o - rCur - piNext < piNext := by omega
      rw [sum_Ioc_split _ (by omega : 0 ≤ rCur + piNext) (by omega : rCur + piNext ≤ o)]
      -- First `rCur + piNext` steps sum to `cf (κ + 1)`!
      have hfirst : ∑ x ∈ Ioc 0 (rCur + piNext), strokeTurnJumpAux s0 m cb cf κ (d + 1) x =
          cf (κ + 1) := by
        rw [sum_Ioc_split _ (by omega : 0 ≤ rCur) (by omega : rCur ≤ rCur + piNext)]
        have hs1 : ∑ x ∈ Ioc 0 rCur, strokeTurnJumpAux s0 m cb cf κ (d + 1) x = cb (κ + 1) := by
          rw [sum_Ioc_split _ (by omega : 0 ≤ rCur - 1) (by omega : rCur - 1 ≤ rCur)]
          have h0 : ∑ x ∈ Ioc 0 (rCur - 1), strokeTurnJumpAux s0 m cb cf κ (d + 1) x = 0 := by
            apply Finset.sum_eq_zero
            intro x hx; rw [mem_Ioc] at hx
            have hlt : x < scaleR s0 κ := by omega
            simp [strokeTurnJumpAux, hlt]
          have h1s : Ioc (rCur - 1) rCur = {rCur} := by
            ext x; simp only [mem_Ioc, mem_singleton]; omega
          rw [h0, zero_add, h1s, Finset.sum_singleton]
          simp [strokeTurnJumpAux, rCur]
        rw [sum_Ioc_split _ (by omega : rCur ≤ rCur + (piNext - 1))
          (by omega : rCur + (piNext - 1) ≤ rCur + piNext)]
        have hs2 : ∑ x ∈ Ioc rCur (rCur + (piNext - 1)),
            strokeTurnJumpAux s0 m cb cf κ (d + 1) x = strokeMass m cf (κ + 1) := by
          have heq_f : ∀ x ∈ Ioc rCur (rCur + (piNext - 1)),
              strokeTurnJumpAux s0 m cb cf κ (d + 1) x =
                strokeTurnJumpAux s0 m cb cf (κ + 1) d (x - rCur) := by
            intro x hx; rw [mem_Ioc] at hx
            have ha : ¬ (x < scaleR s0 κ) := by omega
            have hb : x ≠ scaleR s0 κ := by omega
            have hc : x < scaleR s0 κ + strokeLen s0 m (κ + 1) := by omega
            simp [strokeTurnJumpAux, ha, hb, hc, rCur]
          rw [Finset.sum_congr rfl heq_f, sum_Ioc_shift_sub]
          have hfull := sum_strokeTurnJumpAux_full s0 m cb cf hms d (κ + 1) (by omega)
          rw [sum_Ioc_split _ (by omega : 0 ≤ piNext - 1) (by omega : piNext - 1 ≤ piNext)]
            at hfull
          have hend : Ioc (piNext - 1) piNext = {piNext} := by
            ext x; simp only [mem_Ioc, mem_singleton]; omega
          have hend0 : strokeTurnJumpAux s0 m cb cf (κ + 1) d piNext = 0 :=
            strokeTurnJumpAux_end_zero s0 m cb cf hms (κ + 1) d (by omega)
          rw [hend, Finset.sum_singleton, hend0, add_zero] at hfull
          exact hfull
        have hval_set : Ioc (rCur + (piNext - 1)) (rCur + piNext) = {rCur + piNext} := by
          ext x; simp only [mem_Ioc, mem_singleton]; omega
        have hval_eq : strokeTurnJumpAux s0 m cb cf κ (d + 1) (rCur + piNext) =
            cf (κ + 1) - cb (κ + 1) - strokeMass m cf (κ + 1) := by
          change strokeTurnJumpAux s0 m cb cf κ (d + 1) (scaleR s0 κ + strokeLen s0 m (κ + 1)) = _
          have ha : ¬ (scaleR s0 κ + strokeLen s0 m (κ + 1) < scaleR s0 κ) := by omega
          have hpi_ne : strokeLen s0 m (κ + 1) ≠ 0 := by omega
          simp [strokeTurnJumpAux, ha, hpi_ne]
        rw [hs1, hs2, hval_set, Finset.sum_singleton, hval_eq]
        ring
      have hrest : ∑ x ∈ Ioc (rCur + piNext) o, strokeTurnJumpAux s0 m cb cf κ (d + 1) x =
          ∑ k ∈ Ioc 0 (o - rCur - piNext), strokeTurnJumpAux s0 m cb cf (κ + 1) d k := by
        have heq_f : ∀ x ∈ Ioc (rCur + piNext) o,
            strokeTurnJumpAux s0 m cb cf κ (d + 1) x =
              strokeTurnJumpAux s0 m cb cf (κ + 1) d (x - (rCur + piNext)) := by
          intro x hx; rw [mem_Ioc] at hx
          have ha : ¬ (x < scaleR s0 κ) := by omega
          have hb : x ≠ scaleR s0 κ := by omega
          have hc : ¬ (x < scaleR s0 κ + strokeLen s0 m (κ + 1)) := by omega
          have hd' : x ≠ scaleR s0 κ + strokeLen s0 m (κ + 1) := by omega
          have he : x < scaleR s0 κ + 2 * strokeLen s0 m (κ + 1) := by omega
          have hsub : x - scaleR s0 κ - strokeLen s0 m (κ + 1) = x - (rCur + piNext) := by omega
          simp [strokeTurnJumpAux, ha, hb, hc, hd', he, hsub]
        rw [Finset.sum_congr rfl heq_f]
        have hlen_eq : o = (rCur + piNext) + (o - rCur - piNext) := by omega
        conv_lhs => rw [hlen_eq]
        exact sum_Ioc_shift_sub _ (rCur + piNext) (o - rCur - piNext)
      rw [hfirst, hrest, ih (by omega) ho'' (by omega)]

/-- Explicit turn jump `J(τ)` at step `τ ∈ (0, P)` over one period `P = 4 Π₀` of `U(s₀, m, 1)`,
with tip jumps `jTip` at the two tips `Π₀` and `3 Π₀` and level-uniform jumps inside each of the
four level-`0` strokes. -/
def periodTurnJump (s0 m : ℕ) (cb cf : ℕ → ℤ) (jTip : ℤ) (τ : ℕ) : ℤ :=
  let pi0 := strokeLen s0 m 0
  if τ = pi0 ∨ τ = 3 * pi0 then jTip
  else if τ < 4 * pi0 ∧ τ % pi0 ≠ 0 then strokeTurnJump s0 m cb cf 0 (τ % pi0)
  else 0

/-- **`O(m)` recursive turn-potential evaluator** `Φ(t)` for `t ∈ [0, P)` on `U(s₀, m, 1)`. -/
def evalPhiRec (s0 m : ℕ) (cb cf : ℕ → ℤ) (jTip : ℤ) (t : ℕ) : ℤ :=
  let pi0 := strokeLen s0 m 0
  Nat.cast (t / pi0) * strokeMass m cf 0 +
    (if pi0 ≤ t then jTip else 0) +
    (if 3 * pi0 ≤ t then jTip else 0) +
    strokePhiRec s0 m cb cf 0 (t % pi0)

private theorem strokeTurnJump_end_zero {s0 m : ℕ} (cb cf : ℕ → ℤ) (hms : m ≤ s0) :
    strokeTurnJump s0 m cb cf 0 (strokeLen s0 m 0) = 0 :=
  strokeTurnJumpAux_end_zero s0 m cb cf hms 0 (m - 0) (by omega)

private theorem sum_period_stroke (s0 m : ℕ) (cb cf : ℕ → ℤ) (jTip : ℤ) (hms : m ≤ s0)
    (q : ℕ) (hq : q < 4) :
    ∑ τ ∈ Ioc (q * strokeLen s0 m 0) ((q + 1) * strokeLen s0 m 0),
      periodTurnJump s0 m cb cf jTip τ =
      strokeMass m cf 0 + (if q = 0 ∨ q = 2 then jTip else 0) := by
  set pi0 := strokeLen s0 m 0
  have hpi0 : 0 < pi0 := strokeLen_pos s0 m 0
  have hq_succ : (q + 1) * pi0 = q * pi0 + pi0 := by ring
  rw [sum_Ioc_split _ (by omega : q * pi0 ≤ q * pi0 + (pi0 - 1))
    (by omega : q * pi0 + (pi0 - 1) ≤ (q + 1) * pi0)]
  have hinter : ∑ τ ∈ Ioc (q * pi0) (q * pi0 + (pi0 - 1)),
      periodTurnJump s0 m cb cf jTip τ = strokeMass m cf 0 := by
    have heq_f : ∀ τ ∈ Ioc (q * pi0) (q * pi0 + (pi0 - 1)),
        periodTurnJump s0 m cb cf jTip τ = strokeTurnJump s0 m cb cf 0 (τ - q * pi0) := by
      intro τ hτ; rw [mem_Ioc] at hτ
      have hmod : τ % pi0 = τ - q * pi0 := by
        have hτ_eq : τ = (τ - q * pi0) + pi0 * q := by
          have : q * pi0 = pi0 * q := Nat.mul_comm q pi0
          omega
        conv_lhs => rw [hτ_eq]
        rw [Nat.add_mul_mod_self_left]
        exact Nat.mod_eq_of_lt (by omega)
      have hbounds : τ ≠ pi0 ∧ τ ≠ 3 * pi0 ∧ τ < 4 * pi0 := by
        rcases (show q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 by omega) with rfl | rfl | rfl | rfl <;> omega
      have hsub_ne : τ - q * strokeLen s0 m 0 ≠ 0 := by dsimp only [pi0] at hτ; omega
      simp [periodTurnJump, pi0, hbounds.1, hbounds.2.1, hbounds.2.2, hmod, hsub_ne]
    rw [Finset.sum_congr rfl heq_f, sum_Ioc_shift_sub]
    have hfull := sum_strokeTurnJumpAux_full s0 m cb cf hms m 0 (by omega)
    unfold strokeTurnJump
    rw [Nat.sub_zero]
    rw [sum_Ioc_split _ (by omega : 0 ≤ pi0 - 1) (by omega : pi0 - 1 ≤ pi0)] at hfull
    have hend : Ioc (pi0 - 1) pi0 = {pi0} := by
      ext x; simp only [mem_Ioc, mem_singleton]; omega
    have hend0 := strokeTurnJump_end_zero cb cf hms
    unfold strokeTurnJump at hend0
    rw [Nat.sub_zero] at hend0
    rw [hend, Finset.sum_singleton, hend0, add_zero] at hfull
    exact hfull
  have hend_set : Ioc (q * pi0 + (pi0 - 1)) ((q + 1) * pi0) = {(q + 1) * pi0} := by
    ext x; simp only [mem_Ioc, mem_singleton]; omega
  rw [hinter, hend_set, Finset.sum_singleton]
  congr 1
  rcases (show q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 by omega) with rfl | rfl | rfl | rfl
  · simp [periodTurnJump, pi0]
  · have hne1 : (1 + 1) * pi0 ≠ pi0 := by omega
    have hne3 : (1 + 1) * pi0 ≠ 3 * pi0 := by omega
    have hmod0 : (1 + 1) * pi0 % pi0 = 0 := Nat.mul_mod_left _ _
    simp [periodTurnJump, pi0, hne1, hne3, hmod0]
  · have h3 : (2 + 1) * pi0 = 3 * pi0 := by ring
    simp [periodTurnJump, pi0, h3]
  · have hne1 : (3 + 1) * pi0 ≠ pi0 := by omega
    have hne3 : (3 + 1) * pi0 ≠ 3 * pi0 := by omega
    simp [periodTurnJump, pi0, hne1, hne3]

/-- **Proposition SL(c)** (`O(m)` recursive potential equals cumulative turn jumps):
For every `t < dnpPeriod s0 m` (`m ≤ s₀`), `evalPhiRec s0 m cb cf jTip t` equals the exact sum of
turn jumps `∑ τ ∈ Ioc 0 t, periodTurnJump s0 m cb cf jTip τ`. -/
theorem evalPhiRec_eq_sum_turnJumps {s0 m : ℕ} (cb cf : ℕ → ℤ) (jTip : ℤ) (hms : m ≤ s0)
    {t : ℕ} (ht : t < dnpPeriod s0 m) :
    evalPhiRec s0 m cb cf jTip t = ∑ τ ∈ Ioc 0 t, periodTurnJump s0 m cb cf jTip τ := by
  unfold dnpPeriod at ht
  unfold evalPhiRec
  dsimp only
  have hpi0 : 0 < strokeLen s0 m 0 := strokeLen_pos s0 m 0
  have ht_decomp : t = (t / strokeLen s0 m 0) * strokeLen s0 m 0 + t % strokeLen s0 m 0 := by
    have := Nat.div_add_mod t (strokeLen s0 m 0)
    rw [Nat.mul_comm] at this
    exact this.symm
  have hq_lt : t / strokeLen s0 m 0 < 4 :=
    Nat.div_lt_of_lt_mul (by linarith : t < strokeLen s0 m 0 * 4)
  have hrem_lt : t % strokeLen s0 m 0 < strokeLen s0 m 0 := Nat.mod_lt t hpi0
  generalize t / strokeLen s0 m 0 = q at ht_decomp hq_lt ⊢
  generalize t % strokeLen s0 m 0 = rem at ht_decomp hrem_lt ⊢
  rw [sum_Ioc_split _ (by omega : 0 ≤ q * strokeLen s0 m 0) (by omega : q * strokeLen s0 m 0 ≤ t)]
  -- Tail `(q * pi0, q * pi0 + rem]` equals `strokePhiRec s0 m cb cf 0 rem`
  have htail : ∑ τ ∈ Ioc (q * strokeLen s0 m 0) t, periodTurnJump s0 m cb cf jTip τ =
      strokePhiRec s0 m cb cf 0 rem := by
    rw [strokePhiRec_eq_sum_turnJumps cb cf hms (Nat.zero_le m) hrem_lt]
    have heq_f : ∀ τ ∈ Ioc (q * strokeLen s0 m 0) t,
        periodTurnJump s0 m cb cf jTip τ =
          strokeTurnJump s0 m cb cf 0 (τ - q * strokeLen s0 m 0) := by
      intro τ hτ; rw [mem_Ioc] at hτ
      have hmod : τ % strokeLen s0 m 0 = τ - q * strokeLen s0 m 0 := by
        have hτ_eq : τ = (τ - q * strokeLen s0 m 0) + strokeLen s0 m 0 * q := by
          have : q * strokeLen s0 m 0 = strokeLen s0 m 0 * q := Nat.mul_comm q _
          omega
        conv_lhs => rw [hτ_eq]
        rw [Nat.add_mul_mod_self_left]
        exact Nat.mod_eq_of_lt (by omega)
      have hbounds : τ ≠ strokeLen s0 m 0 ∧ τ ≠ 3 * strokeLen s0 m 0 ∧
          τ < 4 * strokeLen s0 m 0 := by
        rcases (show q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 by omega) with rfl | rfl | rfl | rfl <;> omega
      have hsub_ne : τ - q * strokeLen s0 m 0 ≠ 0 := by omega
      simp [periodTurnJump, hbounds.1, hbounds.2.1, hbounds.2.2, hmod, hsub_ne]
    rw [Finset.sum_congr rfl heq_f]
    conv_lhs => rw [ht_decomp]
    exact sum_Ioc_shift_sub _ (q * strokeLen s0 m 0) rem
  rw [htail]
  rcases (show q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 by omega) with rfl | rfl | rfl | rfl
  · have h1 : ¬ (strokeLen s0 m 0 ≤ t) := by omega
    have h3 : ¬ (3 * strokeLen s0 m 0 ≤ t) := by omega
    simp [h1, h3]
  · have h1 : strokeLen s0 m 0 ≤ t := by omega
    have h3 : ¬ (3 * strokeLen s0 m 0 ≤ t) := by omega
    have hs0 := sum_period_stroke s0 m cb cf jTip hms 0 (by omega)
    rw [Nat.zero_mul, Nat.zero_add] at hs0
    rw [hs0]
    simp only [h1, h3, true_or, ↓reduceIte]
    push_cast; ring
  · have h1 : strokeLen s0 m 0 ≤ t := by omega
    have h3 : ¬ (3 * strokeLen s0 m 0 ≤ t) := by omega
    rw [sum_Ioc_split _ (by omega : 0 ≤ 1 * strokeLen s0 m 0)
      (by omega : 1 * strokeLen s0 m 0 ≤ 2 * strokeLen s0 m 0)]
    have hs0 := sum_period_stroke s0 m cb cf jTip hms 0 (by omega)
    have hs1 := sum_period_stroke s0 m cb cf jTip hms 1 (by omega)
    rw [Nat.zero_mul, Nat.zero_add] at hs0
    rw [show (1 + 1) * strokeLen s0 m 0 = 2 * strokeLen s0 m 0 by ring] at hs1
    rw [hs0, hs1]
    simp only [h1, h3, true_or, show ¬(1 = 0 ∨ 1 = 2) by decide, ↓reduceIte]
    push_cast; ring
  · have h1 : strokeLen s0 m 0 ≤ t := by omega
    have h3 : 3 * strokeLen s0 m 0 ≤ t := by omega
    rw [sum_Ioc_split _ (by omega : 0 ≤ 2 * strokeLen s0 m 0)
      (by omega : 2 * strokeLen s0 m 0 ≤ 3 * strokeLen s0 m 0)]
    rw [sum_Ioc_split _ (by omega : 0 ≤ 1 * strokeLen s0 m 0)
      (by omega : 1 * strokeLen s0 m 0 ≤ 2 * strokeLen s0 m 0)]
    have hs0 := sum_period_stroke s0 m cb cf jTip hms 0 (by omega)
    have hs1 := sum_period_stroke s0 m cb cf jTip hms 1 (by omega)
    have hs2 := sum_period_stroke s0 m cb cf jTip hms 2 (by omega)
    rw [Nat.zero_mul, Nat.zero_add] at hs0
    rw [show (1 + 1) * strokeLen s0 m 0 = 2 * strokeLen s0 m 0 by ring] at hs1
    rw [show (2 + 1) * strokeLen s0 m 0 = 3 * strokeLen s0 m 0 by ring] at hs2
    rw [hs0, hs1, hs2]
    simp only [h1, h3, true_or, or_true, show ¬(1 = 0 ∨ 1 = 2) by decide, ↓reduceIte]
    push_cast; ring

end DirectedReciprocity
