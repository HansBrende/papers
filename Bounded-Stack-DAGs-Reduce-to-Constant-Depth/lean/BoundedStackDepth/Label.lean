import BoundedStackDepth.Basic
import BoundedNesting.MCost

/-!
# The label of the shown set, and Lemma V

At each time `t` the composition shows a finite set `O t` of band groups. The label lists the shown groups
from the top: position `i < P` holds the event counter of the group of rank `i` (counted from the top),
shifted by a digit offset `ω i` and reduced modulo `K` (`digits`). The label is the rank of this digit
vector in the lexicographic order of `[0, K)^P` (`lexRank`), so it takes fewer than `K ^ P` values
(`label_lt`), and comparing labels is comparing digit vectors lexicographically.

* `label_lt_label` (**Lemma V**): a hop whose deciding group `d` is shown at both ends, with rank `< P`
  and the same shown groups above it, whose counter of `d` strictly increases and whose digits of rank at
  most that of `d` do not wrap, is not violated.
* `trunc_or_above_or_wrap`: hence a violated hop is truncated, changes the shown set above `d`, or wraps.
* `label_le_label_of_eq`: a state edge with the same shown set at both ends and no wrap is not cut;
  `shown_ne_or_wrap` is the contrapositive.
* `card_wrap_offsets_le`: for one position, at most `n' - n` of the `K ^ P` offset vectors make it wrap.

The counters are abstract (`cnt g t`, monotone in `t`); validity (`eventCount_lt_decGroup`) supplies the strict increase.
The digit comparisons reuse the earlier paper (`digit_le_of_no_wrap`, `digit_lt_of_no_wrap`,
`Fam.card_wrap_le`, `Fam.card_piFinset_coord`).
-/

namespace BoundedStackDepth

open BoundedNesting Finset

/-! ### Ranks from the top -/

/-- The rank of `g` in `S`, counted from the top: the number of elements of `S` above `g`. -/
def topRank (S : Finset ℕ) (g : ℕ) : ℕ := (S.filter (g < ·)).card

theorem topRank_lt_of_lt {S : Finset ℕ} {g g' : ℕ} (hg' : g' ∈ S) (h : g < g') :
    topRank S g' < topRank S g :=
  card_lt_card ⟨monotone_filter_right S fun _ _ hy => h.trans hy, fun hs => by
    have := (mem_filter.mp (hs (mem_filter.mpr ⟨hg', h⟩))).2
    exact lt_irrefl _ this⟩

theorem lt_of_topRank_lt {S : Finset ℕ} {g g' : ℕ} (hg : g ∈ S) (h : topRank S g' < topRank S g) :
    g < g' := by
  by_contra hle
  push Not at hle
  rcases eq_or_lt_of_le hle with he | hlt
  · subst he; exact lt_irrefl _ h
  · exact lt_asymm h (topRank_lt_of_lt hg hlt)

theorem topRank_injOn (S : Finset ℕ) : Set.InjOn (topRank S) S := by
  intro g hg g' hg' he
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact (topRank_lt_of_lt (Finset.mem_coe.mp hg') hlt).ne' he
  · exact (topRank_lt_of_lt (Finset.mem_coe.mp hg) hlt).ne he

theorem topRank_lt_card {S : Finset ℕ} {g : ℕ} (hg : g ∈ S) : topRank S g < S.card :=
  card_lt_card ⟨filter_subset _ _, fun hs => by
    have := (mem_filter.mp (hs hg)).2
    exact lt_irrefl _ this⟩

/-- The rank of `g` depends only on the part of the set above `g`. -/
theorem topRank_eq_of_above {S S' : Finset ℕ} {d g : ℕ} (hdg : d ≤ g)
    (h : S.filter (d < ·) = S'.filter (d < ·)) : topRank S g = topRank S' g := by
  unfold topRank
  have e : ∀ S : Finset ℕ, S.filter (g < ·) = (S.filter (d < ·)).filter (g < ·) := fun S => by
    rw [filter_filter]
    exact filter_congr fun y _ => ⟨fun hy => ⟨by omega, hy⟩, fun hy => hy.2⟩
  rw [e S, e S', h]

/-! ### Lexicographic ranks -/

/-- A digit vector that agrees up to position `r`, weakly before it and strictly at it, is
lexicographically larger. -/
theorem toLex_lt_of_prefix {P : ℕ} {a b : Fin P → ℕ} (r : Fin P) (hle : ∀ i, i < r → a i ≤ b i)
    (hlt : a r < b r) : toLex a < toLex b := by
  obtain ⟨i, hi, hmin⟩ := WellFounded.has_min wellFounded_lt {i | a i ≠ b i}
    ⟨r, show a r ≠ b r from hlt.ne⟩
  have hir : i ≤ r := not_lt.mp fun h => hmin r hlt.ne h
  refine ⟨i, fun j hj => ?_, ?_⟩
  · by_contra hne
    exact hmin j hne hj
  · rcases eq_or_lt_of_le hir with he | hl
    · subst he; exact hlt
    · exact (hle i hl).lt_of_ne hi

open Classical in
/-- The rank of a digit vector among the vectors with digits below `K`, in the lexicographic order. -/
noncomputable def lexRank (K P : ℕ) (a : Fin P → ℕ) : ℕ :=
  ((Fintype.piFinset fun _ : Fin P => range K).filter (fun y => toLex y < toLex a)).card

theorem lexRank_le_of_le {K P : ℕ} {a b : Fin P → ℕ} (h : toLex a ≤ toLex b) :
    lexRank K P a ≤ lexRank K P b := by
  classical
  exact card_le_card (monotone_filter_right _ fun _ _ hy => lt_of_lt_of_le hy h)

theorem lexRank_lt_of_lt {K P : ℕ} {a b : Fin P → ℕ} (ha : ∀ i, a i < K) (h : toLex a < toLex b) :
    lexRank K P a < lexRank K P b := by
  classical
  refine card_lt_card ⟨monotone_filter_right _ fun _ _ hy => lt_trans hy h, fun hs => ?_⟩
  have := (mem_filter.mp (hs (mem_filter.mpr
    ⟨Fintype.mem_piFinset.mpr fun i => mem_range.mpr (ha i), h⟩))).2
  exact lt_irrefl _ this

theorem lexRank_lt_pow {K P : ℕ} {a : Fin P → ℕ} (ha : ∀ i, a i < K) : lexRank K P a < K ^ P := by
  classical
  have hcard : (Fintype.piFinset fun _ : Fin P => range K).card = K ^ P := by
    rw [Fintype.card_piFinset]; simp
  rw [← hcard]
  refine card_lt_card ⟨filter_subset _ _, fun hs => ?_⟩
  have := (mem_filter.mp (hs (Fintype.mem_piFinset.mpr fun i => mem_range.mpr (ha i)))).2
  exact lt_irrefl _ this

/-! ### Digits and the label -/

/-- The digits at one time: position `i` holds `(c g + ω i) mod K` for the shown group `g` of rank `i`,
and `0` if there is none. -/
def digits (K P : ℕ) (O : Finset ℕ) (c : ℕ → ℕ) (ω : Fin P → ℕ) (i : Fin P) : ℕ :=
  ∑ g ∈ O.filter (fun g : ℕ => topRank O g = (i : ℕ)), (c g + ω i) % K

theorem digits_eq {K P : ℕ} {O : Finset ℕ} {c : ℕ → ℕ} {ω : Fin P → ℕ} {g : ℕ} (hg : g ∈ O)
    {i : Fin P} (hi : topRank O g = i) : digits K P O c ω i = (c g + ω i) % K := by
  unfold digits
  rw [sum_eq_single_of_mem g (mem_filter.mpr ⟨hg, hi⟩) fun g' hg' hne => ?_]
  obtain ⟨hg'O, hg'i⟩ := mem_filter.mp hg'
  exact absurd (topRank_injOn O hg'O hg (hg'i.trans hi.symm)) hne

theorem digits_of_not_mem {K P : ℕ} {O : Finset ℕ} {c : ℕ → ℕ} {ω : Fin P → ℕ} {i : Fin P}
    (h : ∀ g ∈ O, topRank O g ≠ i) : digits K P O c ω i = 0 :=
  sum_eq_zero fun g hg => absurd (mem_filter.mp hg).2 (h g (mem_filter.mp hg).1)

theorem digits_lt {K P : ℕ} (hK : 0 < K) (O : Finset ℕ) (c : ℕ → ℕ) (ω : Fin P → ℕ) (i : Fin P) :
    digits K P O c ω i < K := by
  by_cases h : ∃ g ∈ O, topRank O g = i
  · obtain ⟨g, hg, hi⟩ := h
    rw [digits_eq hg hi]
    exact Nat.mod_lt _ hK
  · push Not at h
    rw [digits_of_not_mem h]
    exact hK

variable {K P : ℕ} {O : ℕ → Finset ℕ} {cnt : ℕ → ℕ → ℕ} {ω : Fin P → ℕ}

/-- **The label** at time `t`: the lexicographic rank of the digit vector. -/
noncomputable def label (K P : ℕ) (O : ℕ → Finset ℕ) (cnt : ℕ → ℕ → ℕ) (ω : Fin P → ℕ) (t : ℕ) : ℕ :=
  lexRank K P (digits K P (O t) (fun g => cnt g t) ω)

/-- The label takes fewer than `K ^ P` values. -/
theorem label_lt (hK : 0 < K) (t : ℕ) : label K P O cnt ω t < K ^ P :=
  lexRank_lt_pow fun i => digits_lt hK _ _ _ i

/-- **Lemma V.** Let `d` be shown at `p` and `u`, with the same shown groups above it and rank `< P`.
If the counters of `d` and the groups above it do not decrease, the counter of `d` strictly
increases, and none of their digits wraps, then the label strictly increases from `p` to `u`. -/
theorem label_lt_label (hK : 0 < K) {p u d : ℕ} (hdp : d ∈ O p) (hdu : d ∈ O u)
    (habove : (O p).filter (d < ·) = (O u).filter (d < ·)) (hrank : topRank (O p) d < P)
    (hmono : ∀ g ∈ O p, d ≤ g → cnt g p ≤ cnt g u) (hd : cnt d p < cnt d u)
    (hwrap : ∀ g ∈ O p, d ≤ g → ∀ i : Fin P, topRank (O p) g = i →
      (cnt g p + ω i) / K = (cnt g u + ω i) / K) :
    label K P O cnt ω p < label K P O cnt ω u := by
  set r : Fin P := ⟨topRank (O p) d, hrank⟩
  refine lexRank_lt_of_lt (fun i => digits_lt hK _ _ _ i) (toLex_lt_of_prefix r (fun i hi => ?_) ?_)
  · by_cases h : ∃ g ∈ O p, topRank (O p) g = i
    · obtain ⟨g, hg, hgi⟩ := h
      have hdg : d < g := lt_of_topRank_lt hdp (by rw [hgi]; exact hi)
      have hgu : g ∈ O u := by
        have : g ∈ (O p).filter (d < ·) := mem_filter.mpr ⟨hg, hdg⟩
        rw [habove] at this
        exact (mem_filter.mp this).1
      rw [digits_eq hg hgi, digits_eq hgu ((topRank_eq_of_above hdg.le habove).symm.trans hgi)]
      exact digit_le_of_no_wrap (hmono g hg hdg.le) (hwrap g hg hdg.le i hgi)
    · push Not at h
      rw [digits_of_not_mem h]
      exact Nat.zero_le _
  · rw [digits_eq hdp rfl, digits_eq hdu ((topRank_eq_of_above le_rfl habove).symm.trans rfl)]
    exact digit_lt_of_no_wrap hd (hwrap d hdp le_rfl r rfl)

/-- **The cut classification of kept hops.** A hop whose deciding group `d` is shown at both ends,
whose counters do not decrease and whose counter of `d` strictly increases, and which is violated,
is *truncated* (rank of `d` at least `P` at `p`), changes the shown set *above* `d`, or *wraps* a digit
of rank at most that of `d`. -/
theorem trunc_or_above_or_wrap (hK : 0 < K) {p u d : ℕ} (hdp : d ∈ O p) (hdu : d ∈ O u)
    (hmono : ∀ g ∈ O p, d ≤ g → cnt g p ≤ cnt g u) (hd : cnt d p < cnt d u)
    (hviol : label K P O cnt ω u ≤ label K P O cnt ω p) :
    P ≤ topRank (O p) d ∨ (O p).filter (d < ·) ≠ (O u).filter (d < ·) ∨
      ∃ g ∈ O p, d ≤ g ∧ ∃ i : Fin P, topRank (O p) g = i ∧
        (cnt g p + ω i) / K ≠ (cnt g u + ω i) / K := by
  by_contra h
  push Not at h
  obtain ⟨hr, ha, hw⟩ := h
  exact absurd hviol (not_le.mpr (label_lt_label hK hdp hdu ha hr hmono hd hw))

/-- **State edges.** If the shown set is the same at `p` and `u`, the counters of the shown groups do
not decrease and none of their digits wraps, the label does not decrease. -/
theorem label_le_label_of_eq {p u : ℕ} (hO : O p = O u) (hmono : ∀ g ∈ O p, cnt g p ≤ cnt g u)
    (hwrap : ∀ g ∈ O p, ∀ i : Fin P, topRank (O p) g = i →
      (cnt g p + ω i) / K = (cnt g u + ω i) / K) :
    label K P O cnt ω p ≤ label K P O cnt ω u := by
  refine lexRank_le_of_le (Pi.toLex_monotone fun i => ?_)
  by_cases h : ∃ g ∈ O p, topRank (O p) g = i
  · obtain ⟨g, hg, hgi⟩ := h
    show digits K P (O p) _ ω i ≤ digits K P (O u) _ ω i
    rw [digits_eq hg hgi, digits_eq (hO ▸ hg) (hO ▸ hgi)]
    exact digit_le_of_no_wrap (hmono g hg) (hwrap g hg i hgi)
  · push Not at h
    show digits K P (O p) _ ω i ≤ _
    rw [digits_of_not_mem h]
    exact Nat.zero_le _

/-- A state edge whose label decreases changes the shown set or wraps a digit. -/
theorem shown_ne_or_wrap {p u : ℕ} (hmono : ∀ g ∈ O p, cnt g p ≤ cnt g u)
    (hcut : label K P O cnt ω u < label K P O cnt ω p) :
    O p ≠ O u ∨ ∃ g ∈ O p, ∃ i : Fin P, topRank (O p) g = i ∧
      (cnt g p + ω i) / K ≠ (cnt g u + ω i) / K := by
  by_contra h
  push Not at h
  exact absurd hcut (not_lt.mpr (label_le_label_of_eq h.1 hmono h.2))

/-! ### Wraps over the digit offsets -/

/-- For one position `i` and counts `n ≤ n'`, at most `(n' - n) K ^ (P - 1)` of the `K ^ P` offset
vectors make the digit at `i` wrap. -/
theorem card_wrap_offsets_le (hK : 0 < K) (i : Fin P) {n n' : ℕ} (h : n ≤ n') :
    ((Fintype.piFinset fun _ : Fin P => range K).filter
      (fun ω : Fin P → ℕ => (n + ω i) / K ≠ (n' + ω i) / K)).card ≤ (n' - n) * K ^ (P - 1) := by
  rw [Fam.card_piFinset_coord i (fun c => (n + c) / K ≠ (n' + c) / K)]
  exact Nat.mul_le_mul_right _ (Fam.card_wrap_le hK h)

end BoundedStackDepth
