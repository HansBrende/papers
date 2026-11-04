import BoundedStackDepth.Display
import BoundedStackDepth.Revealing

/-!
# The tail of the display

Bits `ξ : ι → Fin Q` are uniform; an entry `e` is *unbroken* when `ξ e ≠ 0`. The *candidates* at a
value `y` are the entries with `bot e ≤ y < top e` (`cands`). The tail bound needs only that every value
has at most `n` candidates; one candidate per head and value (`OneCandidate`, with `n` heads) gives this
(`card_cands_le`).

The *front process* from a start value `s` (`front`): `x₀ = s`, and `x_{i+1}` is the least top of an
unbroken candidate at `x_i`; if there is none, the front has stopped and `x_{i+1} = x_i`. It *runs* at
step `i` (`Running`) if some candidate at `x_i` is unbroken. Running steps form an initial segment
(`Running.anti`).

* `disp_top`, `shownSet_subset` (closure): every displayed entry has top `0` or a front value from a
  seed or from a top in `zeroTops` (the tops of fresh entries, at most `n` of them); hence
  `card_shownSet_le`: if all these fronts stop by step `K`, the shown set has at most
  `1 + #(seeds ∪ zeroTops) (K + 1)` values.
* `isRevealing_newCands`: the entries first examined at step `i` (`newCands`) form an adaptive
  revealing scheme with at most `n` entries per round.
* `exists_newCands_unbroken`: the number of unbroken candidates drops at every step whose new entries
  are all broken, so a front that runs at step `c + n` has an unbroken new entry in one of the rounds
  `c + 1, …, c + n`.
* `card_running_le`: the front from `s` runs at step `j n` for at most `(1 − Q^{−n²})^j Q^{|ι|}` bit
  vectors.
* `card_shownSet_tail`: **the display tail (Lemma D).** The shown set has more than
  `1 + (#seeds + n)(j n + 1)` values for at most `(#seeds + n)(1 − Q^{−n²})^j Q^{|ι|}` bit vectors.
-/

namespace BoundedStackDepth

open Finset

variable {ι : Type*} [Fintype ι] {n : ℕ} {head : ι → Fin n} {bot top : ι → ℕ}

/-! ### Candidates -/

/-- The candidates at `y`: the entries with `bot e ≤ y < top e`. -/
def cands (bot top : ι → ℕ) (y : ℕ) : Finset ι := univ.filter (fun e => bot e ≤ y ∧ y < top e)

theorem mem_cands {y : ℕ} {e : ι} : e ∈ cands bot top y ↔ bot e ≤ y ∧ y < top e := by
  simp [cands]

/-- Under `OneCandidate` there are at most `n` candidates at every value. -/
theorem card_cands_le (hone : OneCandidate head bot top) (y : ℕ) : (cands bot top y).card ≤ n := by
  calc (cands bot top y).card ≤ (univ : Finset (Fin n)).card :=
        card_le_card_of_injOn head (fun _ _ => mem_coe.mpr (mem_univ _)) fun e he e' he' h => by
          rw [mem_coe, mem_cands] at he he'
          exact hone (head e) y e e' rfl h.symm he.1 he.2 he'.1 he'.2
    _ = n := by simp

/-- The tops `≥ 1` of the entries whose window starts at `0`. -/
def zeroTops (bot top : ι → ℕ) : Finset ℕ :=
  (univ.filter (fun e => bot e = 0 ∧ 1 ≤ top e)).image top

theorem card_zeroTops_le (hone : ∀ y, (cands bot top y).card ≤ n) : (zeroTops bot top).card ≤ n :=
  card_image_le.trans <| (card_le_card fun e he => by
    rw [mem_filter] at he
    exact mem_cands.mpr ⟨he.2.1.le, he.2.2⟩).trans (hone 0)

/-! ### The front process -/

variable {Q : ℕ} [NeZero Q]

/-- The unbroken candidates at `y`. -/
def ucands (bot top : ι → ℕ) (ξ : ι → Fin Q) (y : ℕ) : Finset ι :=
  (cands bot top y).filter (fun e => ξ e ≠ 0)

/-- One step of the front: the least top of an unbroken candidate at `x`, or `x` if there is none. -/
def frontStep (bot top : ι → ℕ) (ξ : ι → Fin Q) (x : ℕ) : ℕ :=
  if h : (ucands bot top ξ x).Nonempty then (ucands bot top ξ x).inf' h top else x

/-- The front process from `s`: `x₀ = s` and `x_{i+1} = frontStep x_i`. -/
def front (bot top : ι → ℕ) (ξ : ι → Fin Q) (s : ℕ) : ℕ → ℕ
  | 0 => s
  | i + 1 => frontStep bot top ξ (front bot top ξ s i)

/-- The front from `s` runs at step `i`: some candidate at its value `x_i` is unbroken. -/
def Running (bot top : ι → ℕ) (ξ : ι → Fin Q) (s i : ℕ) : Prop :=
  (ucands bot top ξ (front bot top ξ s i)).Nonempty

instance (bot top : ι → ℕ) (ξ : ι → Fin Q) (s i : ℕ) : Decidable (Running bot top ξ s i) :=
  inferInstanceAs (Decidable (ucands bot top ξ (front bot top ξ s i)).Nonempty)

variable {ξ : ι → Fin Q}

@[simp] theorem front_zero (s : ℕ) : front bot top ξ s 0 = s := rfl

@[simp] theorem front_succ (s i : ℕ) :
    front bot top ξ s (i + 1) = frontStep bot top ξ (front bot top ξ s i) := rfl

theorem mem_ucands {y : ℕ} {e : ι} :
    e ∈ ucands bot top ξ y ↔ (bot e ≤ y ∧ y < top e) ∧ ξ e ≠ 0 := by
  rw [ucands, mem_filter, mem_cands]

theorem frontStep_of_not {x : ℕ} (h : ¬ (ucands bot top ξ x).Nonempty) : frontStep bot top ξ x = x :=
  dite_eq_right h

theorem frontStep_le {x : ℕ} {e : ι} (he : e ∈ ucands bot top ξ x) :
    frontStep bot top ξ x ≤ top e := by
  rw [frontStep, dite_eq_left ⟨e, he⟩]
  exact inf'_le top he

theorem lt_frontStep {x : ℕ} (h : (ucands bot top ξ x).Nonempty) : x < frontStep bot top ξ x := by
  rw [frontStep, dite_eq_left h, lt_inf'_iff]
  exact fun e he => (mem_ucands.mp he).1.2

theorem exists_top_eq_frontStep {x : ℕ} (h : (ucands bot top ξ x).Nonempty) :
    ∃ e ∈ ucands bot top ξ x, top e = frontStep bot top ξ x := by
  rw [frontStep, dite_eq_left h]
  obtain ⟨e, he, h'⟩ := exists_mem_eq_inf' h top
  exact ⟨e, he, h'.symm⟩

theorem le_frontStep (x : ℕ) : x ≤ frontStep bot top ξ x := by
  by_cases h : (ucands bot top ξ x).Nonempty
  · exact (lt_frontStep h).le
  · rw [frontStep_of_not h]

theorem front_mono (s : ℕ) : Monotone (front bot top ξ s) :=
  monotone_nat_of_le_succ fun _ => le_frontStep _

/-- A stopped front stays where it is. -/
theorem front_add_of_not_running {s i : ℕ} (h : ¬ Running bot top ξ s i) (k : ℕ) :
    front bot top ξ s (i + k) = front bot top ξ s i := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [← add_assoc, front_succ, ih]
    exact frontStep_of_not h

/-- Running steps form an initial segment. -/
theorem Running.anti {s i i' : ℕ} (h : Running bot top ξ s i') (hi : i ≤ i') :
    Running bot top ξ s i := by
  by_contra hn
  have hfix := front_add_of_not_running hn (i' - i)
  rw [Nat.add_sub_cancel' hi] at hfix
  unfold Running at h hn
  rw [hfix] at h
  exact hn h

/-- **Key lemma.** An unbroken candidate at `x_i` has its top among the later values of the front. -/
theorem exists_front_eq_top {s i : ℕ} {e : ι} (he : e ∈ ucands bot top ξ (front bot top ξ s i)) :
    ∃ i', i < i' ∧ front bot top ξ s i' = top e := by
  suffices h : ∀ d i, top e - front bot top ξ s i ≤ d →
      e ∈ ucands bot top ξ (front bot top ξ s i) → ∃ i', i < i' ∧ front bot top ξ s i' = top e from
    h _ i le_rfl he
  intro d
  induction d with
  | zero =>
    intro i hd he
    have := (mem_ucands.mp he).1.2
    omega
  | succ d ih =>
    intro i hd he
    have hlt := lt_frontStep ⟨e, he⟩
    have hle := frontStep_le he
    rcases hle.lt_or_eq with h | h
    · obtain ⟨i', hi', h'⟩ := ih (i + 1) (by rw [front_succ]; omega)
        (by
          rw [front_succ, mem_ucands]
          have := (mem_ucands.mp he).1.1
          exact ⟨⟨by omega, h⟩, (mem_ucands.mp he).2⟩)
      exact ⟨i', by omega, h'⟩
    · exact ⟨i + 1, by omega, h⟩

/-- One step of the front only reads the bits of the candidates at its value. -/
theorem frontStep_congr {x : ℕ} {ξ' : ι → Fin Q} (h : ∀ e ∈ cands bot top x, ξ' e = ξ e) :
    frontStep bot top ξ' x = frontStep bot top ξ x := by
  have hu : ucands bot top ξ' x = ucands bot top ξ x :=
    filter_congr fun e he => by rw [h e he]
  simp only [frontStep, hu]

/-- The first `i` steps of the front only read the bits of the candidates at `x_0, …, x_{i-1}`. -/
theorem front_congr {s i : ℕ} {ξ' : ι → Fin Q}
    (h : ∀ i' < i, ∀ e ∈ cands bot top (front bot top ξ s i'), ξ' e = ξ e) :
    front bot top ξ' s i = front bot top ξ s i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [front_succ, front_succ, ih fun i' hi' => h i' (by omega)]
    exact frontStep_congr (h i (by omega))

/-! ### Closure: the shown set lies in the fronts -/

/-- **Closure.** Every displayed entry has top `0` or a value of the front from a seed or from a top
in `zeroTops`. -/
theorem disp_top {seeds : Finset ℕ} {e : ι} (hD : Disp bot top (fun e => ξ e ≠ 0) seeds e) :
    top e = 0 ∨ ∃ s ∈ seeds ∪ zeroTops bot top, ∃ i, front bot top ξ s i = top e := by
  have hz : ∀ e, bot e = 0 →
      top e = 0 ∨ ∃ s ∈ seeds ∪ zeroTops bot top, ∃ i, front bot top ξ s i = top e := by
    intro e he
    rcases Nat.eq_zero_or_pos (top e) with h | h
    · exact Or.inl h
    · exact Or.inr ⟨top e, mem_union_right _ (mem_image.mpr ⟨e, mem_filter.mpr ⟨mem_univ _, he, h⟩,
        rfl⟩), 0, rfl⟩
  induction hD with
  | zero h => exact hz _ h
  | @seed e s hs hu hb ht =>
    rcases ht.lt_or_eq with h | h
    · obtain ⟨i', -, h'⟩ := exists_front_eq_top (ξ := ξ) (s := s) (i := 0)
        (by rw [front_zero]; exact mem_ucands.mpr ⟨⟨hb, h⟩, hu⟩)
      exact Or.inr ⟨s, mem_union_left _ hs, i', h'⟩
    · exact Or.inr ⟨s, mem_union_left _ hs, 0, h⟩
  | @step e e' _ hu hb ht ih =>
    rcases ht.lt_or_eq with h | h
    · rcases ih with h0 | ⟨s, hs, i, hi⟩
      · exact hz e (by omega)
      · obtain ⟨i', -, h'⟩ := exists_front_eq_top (ξ := ξ) (s := s) (i := i)
          (mem_ucands.mpr ⟨⟨hb.trans_eq hi.symm, hi.trans_lt h⟩, hu⟩)
        exact Or.inr ⟨s, hs, i', h'⟩
    · rw [← h]
      exact ih

/-- **Closure**, for the shown set: it consists of `0` and of values of the fronts from the seeds and
from the tops in `zeroTops`. -/
theorem shownSet_subset {seeds : Finset ℕ} :
    (shownSet bot top (fun e => ξ e ≠ 0) seeds : Set ℕ) ⊆
      insert 0 (⋃ s ∈ seeds ∪ zeroTops bot top, Set.range (front bot top ξ s)) := by
  intro v hv
  simp only [mem_coe, shownSet, dispVals, mem_insert, mem_union, mem_image, mem_filter, mem_univ,
    true_and] at hv
  simp only [Set.mem_insert_iff, Set.mem_iUnion, Set.mem_range, exists_prop]
  rcases hv with h | h | ⟨e, he, rfl⟩
  · exact Or.inl h
  · exact Or.inr ⟨v, mem_union_left _ h, 0, rfl⟩
  · exact disp_top he

/-- If the fronts from all seeds and from all tops in `zeroTops` have stopped by step `K`, the shown
set has at most `1 + #(seeds ∪ zeroTops) (K + 1)` values. -/
theorem card_shownSet_le {seeds : Finset ℕ} {K : ℕ}
    (hstop : ∀ s ∈ seeds ∪ zeroTops bot top, ¬ Running bot top ξ s K) :
    (shownSet bot top (fun e => ξ e ≠ 0) seeds).card
      ≤ 1 + (seeds ∪ zeroTops bot top).card * (K + 1) := by
  set S := seeds ∪ zeroTops bot top
  have hval : ∀ s ∈ S, ∀ i, front bot top ξ s i ∈
      S.biUnion fun s => (range (K + 1)).image (front bot top ξ s) := by
    intro s hs i
    refine mem_biUnion.mpr ⟨s, hs, mem_image.mpr ?_⟩
    rcases Nat.lt_or_ge i (K + 1) with h | h
    · exact ⟨i, mem_range.mpr h, rfl⟩
    · have hfix := front_add_of_not_running (hstop s hs) (i - K)
      rw [Nat.add_sub_cancel' (by omega)] at hfix
      exact ⟨K, mem_range.mpr (Nat.lt_succ_self K), hfix.symm⟩
  have hsub : shownSet bot top (fun e => ξ e ≠ 0) seeds ⊆
      insert 0 (S.biUnion fun s => (range (K + 1)).image (front bot top ξ s)) := by
    intro v hv
    rcases Set.mem_insert_iff.mp (shownSet_subset (mem_coe.mpr hv)) with h | h
    · exact mem_insert.mpr (Or.inl h)
    · simp only [Set.mem_iUnion, Set.mem_range, exists_prop] at h
      obtain ⟨s, hs, i, rfl⟩ := h
      exact mem_insert_of_mem (hval s hs i)
  calc (shownSet bot top (fun e => ξ e ≠ 0) seeds).card
      ≤ (S.biUnion fun s => (range (K + 1)).image (front bot top ξ s)).card + 1 :=
        (card_le_card hsub).trans (card_insert_le _ _)
    _ ≤ (∑ s ∈ S, ((range (K + 1)).image (front bot top ξ s)).card) + 1 :=
        Nat.add_le_add_right card_biUnion_le _
    _ ≤ (∑ _s ∈ S, (K + 1)) + 1 :=
        Nat.add_le_add_right (sum_le_sum fun s _ => card_image_le.trans (card_range _).le) _
    _ = 1 + S.card * (K + 1) := by rw [sum_const, smul_eq_mul, Nat.add_comm]

/-! ### The front as an adaptive revealing scheme -/

variable [DecidableEq ι]

/-- The entries first examined at step `i`: the candidates at `x_i` that are not candidates at any
earlier value. -/
def newCands (bot top : ι → ℕ) (s i : ℕ) (ξ : ι → Fin Q) : Finset ι :=
  cands bot top (front bot top ξ s i) \ (range i).biUnion fun i' => cands bot top (front bot top ξ s i')

theorem card_newCands_le (hone : ∀ y, (cands bot top y).card ≤ n) (s i : ℕ) (ξ : ι → Fin Q) :
    (newCands bot top s i ξ).card ≤ n :=
  (card_le_card sdiff_subset).trans (hone _)

/-- Every candidate at `x_i` is a new candidate at some step `i' ≤ i`. -/
theorem exists_mem_newCands {s i : ℕ} {e : ι} (he : e ∈ cands bot top (front bot top ξ s i)) :
    ∃ i' ≤ i, e ∈ newCands bot top s i' ξ := by
  have hex : ∃ k, e ∈ cands bot top (front bot top ξ s k) := ⟨i, he⟩
  refine ⟨Nat.find hex, Nat.find_min' hex he, mem_sdiff.mpr ⟨Nat.find_spec hex, fun h => ?_⟩⟩
  obtain ⟨k, hk, hek⟩ := mem_biUnion.mp h
  exact Nat.find_min hex (mem_range.mp hk) hek

/-- **The new candidates form an adaptive revealing scheme.** -/
theorem isRevealing_newCands (s : ℕ) :
    IsRevealing (newCands bot top s : ℕ → (ι → Fin Q) → Finset ι) where
  adapt i ξ ξ' h := by
    have hf : ∀ i' ≤ i, front bot top ξ' s i' = front bot top ξ s i' := fun i' hi' =>
      front_congr fun i'' hi'' e he => by
        obtain ⟨k, hk, hek⟩ := exists_mem_newCands he
        exact h k (by omega) e hek
    simp only [newCands]
    rw [hf i le_rfl, biUnion_congr rfl fun i' hi' => by rw [hf i' (mem_range.mp hi').le]]
  fresh i ξ i' hi' :=
    disjoint_sdiff_self_left.mono_right fun e he =>
      mem_biUnion.mpr ⟨i', mem_range.mpr hi', (mem_sdiff.mp he).1⟩

/-! ### The potential -/

/-- If the front runs at step `i` and the new candidates of step `i + 1` are all broken, the number of
unbroken candidates drops: the minimizer leaves, and every other unbroken candidate at `x_{i+1}` was
one at `x_i`. -/
theorem card_ucands_succ_lt {s i : ℕ} (hrun : Running bot top ξ s i)
    (hz : ∀ e ∈ newCands bot top s (i + 1) ξ, ξ e = 0) :
    (ucands bot top ξ (front bot top ξ s (i + 1))).card
      < (ucands bot top ξ (front bot top ξ s i)).card := by
  obtain ⟨e₀, he₀, htop⟩ := exists_top_eq_frontStep hrun
  have hstep := le_frontStep (bot := bot) (top := top) (ξ := ξ) (front bot top ξ s i)
  have hsub :
      ucands bot top ξ (front bot top ξ s (i + 1)) ⊆ ucands bot top ξ (front bot top ξ s i) := by
    intro e he
    have he' := mem_ucands.mp he
    have hnot : e ∉ newCands bot top s (i + 1) ξ := fun h => he'.2 (hz e h)
    rw [newCands, mem_sdiff, not_and, not_not] at hnot
    obtain ⟨k, hk, hek⟩ := mem_biUnion.mp (hnot (mem_cands.mpr he'.1))
    have hk' := mem_cands.mp hek
    have hmono : front bot top ξ s k ≤ front bot top ξ s i :=
      front_mono s (Nat.lt_succ_iff.mp (mem_range.mp hk))
    rw [front_succ] at he'
    exact mem_ucands.mpr ⟨⟨by omega, by omega⟩, he'.2⟩
  refine card_lt_card ((ssubset_iff_of_subset hsub).mpr ⟨e₀, he₀, fun h => ?_⟩)
  have := (mem_ucands.mp h).1.2
  rw [front_succ] at this
  omega

/-- While the front runs and the rounds `c + 1, …, c + t` reveal only broken entries, at least `t`
unbroken candidates have been used up. -/
theorem card_ucands_add_le (hone : ∀ y, (cands bot top y).card ≤ n) {s c : ℕ} (t : ℕ)
    (hrun : Running bot top ξ s (c + t))
    (hz : ∀ i ∈ Ico (c + 1) (c + t + 1), ∀ e ∈ newCands bot top s i ξ, ξ e = 0) :
    (ucands bot top ξ (front bot top ξ s (c + t))).card + t ≤ n := by
  induction t with
  | zero => exact (card_le_card (filter_subset _ _)).trans (hone _)
  | succ t ih =>
    rw [← add_assoc c t 1] at hrun hz ⊢
    have hrun' : Running bot top ξ s (c + t) := hrun.anti (by omega)
    have h1 := ih hrun' fun i hi => hz i (by rw [mem_Ico] at hi ⊢; omega)
    have h2 := card_ucands_succ_lt hrun' (hz (c + t + 1) (by rw [mem_Ico]; omega))
    omega

/-- **A running front reveals.** A front that runs at step `c + n` has an unbroken new candidate in
one of the rounds `c + 1, …, c + n`. -/
theorem exists_newCands_unbroken (hone : ∀ y, (cands bot top y).card ≤ n) {s c : ℕ}
    (hrun : Running bot top ξ s (c + n)) :
    ∃ i ∈ Ico (c + 1) (c + n + 1), ∃ e ∈ newCands bot top s i ξ, ξ e ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have h := card_ucands_add_le hone n hrun hcon
  have := card_pos.mpr hrun
  omega

/-- **The front rarely runs long.** The front from `s` runs at step `j n` (it makes more than `j n`
steps) for at most `(1 − Q^{−n²})^j · Q^{|ι|}` bit vectors. -/
theorem card_running_le (hone : ∀ y, (cands bot top y).card ≤ n) (s j : ℕ) :
    ((univ.filter (fun ξ : ι → Fin Q => Running bot top ξ s (j * n))).card : ℝ)
      ≤ (1 - ((Q : ℝ) ^ (n * n))⁻¹) ^ j * (Q : ℝ) ^ Fintype.card ι := by
  refine le_trans ?_ (card_blocks_le (isRevealing_newCands s)
    (fun i ξ => card_newCands_le hone s i ξ) 1 n j)
  refine Nat.cast_le.mpr (card_le_card fun ξ hξ => ?_)
  rw [mem_filter] at hξ ⊢
  refine ⟨mem_univ _, fun b hb => ?_⟩
  have hbn : b * n + n ≤ j * n := by
    have h : (b + 1) * n ≤ j * n := Nat.mul_le_mul_right n hb
    rwa [Nat.add_mul, Nat.one_mul] at h
  obtain ⟨i, hi, e, he, hne⟩ := exists_newCands_unbroken hone (hξ.2.anti hbn)
  exact ⟨i, by rw [mem_Ico] at hi ⊢; omega, e, he, hne⟩

/-- **The display tail.** The shown set has more than `1 + (#seeds + n)(j n + 1)` values for at most
`(#seeds + n)(1 − Q^{−n²})^j · Q^{|ι|}` bit vectors. -/
theorem card_shownSet_tail (hone : ∀ y, (cands bot top y).card ≤ n) (seeds : Finset ℕ) (j : ℕ) :
    ((univ.filter (fun ξ : ι → Fin Q => 1 + (seeds.card + n) * (j * n + 1) <
      (shownSet bot top (fun e => ξ e ≠ 0) seeds).card)).card : ℝ)
      ≤ (seeds.card + n) * (1 - ((Q : ℝ) ^ (n * n))⁻¹) ^ j * (Q : ℝ) ^ Fintype.card ι := by
  set S := seeds ∪ zeroTops bot top
  have hScard : S.card ≤ seeds.card + n :=
    (card_union_le _ _).trans (Nat.add_le_add_left (card_zeroTops_le hone) _)
  have hsub : univ.filter (fun ξ : ι → Fin Q => 1 + (seeds.card + n) * (j * n + 1) <
      (shownSet bot top (fun e => ξ e ≠ 0) seeds).card)
      ⊆ S.biUnion fun s => univ.filter (fun ξ : ι → Fin Q => Running bot top ξ s (j * n)) := by
    intro ξ hξ
    rw [mem_filter] at hξ
    by_contra hcon
    simp only [mem_biUnion, mem_filter, mem_univ, true_and, not_exists, not_and] at hcon
    have h : (shownSet bot top (fun e => ξ e ≠ 0) seeds).card ≤ 1 + S.card * (j * n + 1) :=
      card_shownSet_le hcon
    have := Nat.mul_le_mul_right (j * n + 1) hScard
    omega
  have hp : (1 : ℝ) ≤ (Q : ℝ) ^ (n * n) := one_le_pow₀ (by exact_mod_cast NeZero.one_le)
  have hq : 0 ≤ (1 - ((Q : ℝ) ^ (n * n))⁻¹) ^ j * (Q : ℝ) ^ Fintype.card ι :=
    mul_nonneg (pow_nonneg (sub_nonneg.mpr (inv_le_one_of_one_le₀ hp)) j)
      (pow_nonneg (Nat.cast_nonneg Q) _)
  calc _ ≤ ((S.biUnion fun s => univ.filter (fun ξ : ι → Fin Q =>
          Running bot top ξ s (j * n))).card : ℝ) := Nat.cast_le.mpr (card_le_card hsub)
    _ ≤ ∑ s ∈ S, ((univ.filter (fun ξ : ι → Fin Q => Running bot top ξ s (j * n))).card : ℝ) :=
        by exact_mod_cast card_biUnion_le
    _ ≤ ∑ _s ∈ S, (1 - ((Q : ℝ) ^ (n * n))⁻¹) ^ j * (Q : ℝ) ^ Fintype.card ι :=
        sum_le_sum fun s _ => card_running_le hone s j
    _ = S.card * ((1 - ((Q : ℝ) ^ (n * n))⁻¹) ^ j * (Q : ℝ) ^ Fintype.card ι) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ (seeds.card + n) * ((1 - ((Q : ℝ) ^ (n * n))⁻¹) ^ j * (Q : ℝ) ^ Fintype.card ι) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hScard) hq
    _ = _ := by ring

end BoundedStackDepth
