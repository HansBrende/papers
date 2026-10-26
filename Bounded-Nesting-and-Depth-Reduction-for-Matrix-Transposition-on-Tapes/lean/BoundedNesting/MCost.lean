import BoundedNesting.MLevels
import BoundedNesting.ClockCost

/-!
# The label of Theorem M

The label combines the head-`0` counters of `q + 1` levels (`lcnt`) with the event counts of the
bounded walks, one per window (`nev`). Its digits have a static order, most significant first:
`d_q, e_q, d_{q-1}, e_{q-1}, …, d_1, e_1, d_0`. In Lean, `d_{j+1}` sits at position `2(q-1-j)`,
`e_{j+1}` at position `2(q-1-j)+1`, and `d_0` at position `2q`; windows and positive levels are
indexed by `j : Fin q`, window `j` corresponding to level `j + 1`. The digits `d_i, e_i` have radix
`K` and `d_0` has radix `K₀` (`mdig`).

* `mdig_lt`: digit bounds. `depth_le_of_mixedRadix`: a label with digits in `[0, K_p)` has depth at
  most `∏ K_p - 1`.
* `chord_lt`: a chord at a cell that is not a line, with no wrap of the counter of its deciding
  level and no wrap of `e_j` for the windows above it, is not violated.
* `ahop_lt`: a hop of a bounded walk of window `j`, not at a line time, along which head `0`
  visits no level-`(j+1)` line and no `e_{j'}`, `j' ≥ j`, wraps, is not violated.
* `state_le`: along a state edge between non-line times, without a wrap of `d_0` or of any `e_j`,
  the label does not decrease.
-/

namespace BoundedNesting

open Finset

/-! ### Mixed-radix depth -/

/-- **Labels in a mixed-radix range.** A path along which a label with digits in `[0, K_p)` never
increases, and strictly decreases at the marked steps, has at most `∏ K_p - 1` marked steps. -/
theorem depth_le_of_mixedRadix {n : ℕ} {α : Type*} (Kv : Fin n → ℕ) (Ψ : α → Fin n → ℕ)
    (hΨ : ∀ a i, Ψ a i < Kv i) (f : ℕ → α) (m : ℕ) (marked : ℕ → Prop) [DecidablePred marked]
    (hmono : ∀ i < m, toLex (Ψ (f (i + 1))) ≤ toLex (Ψ (f i)))
    (hstrict : ∀ i < m, marked i → toLex (Ψ (f (i + 1))) < toLex (Ψ (f i))) :
    ((range m).filter marked).card ≤ (∏ i, Kv i) - 1 := by
  classical
  set S := Fintype.piFinset fun i => range (Kv i)
  let rank : α → ℕ := fun a => (S.filter fun y => toLex y < toLex (Ψ a)).card
  have hmem : ∀ a, Ψ a ∈ S := fun a => Fintype.mem_piFinset.mpr fun i => mem_range.mpr (hΨ a i)
  have hcardS : S.card = ∏ i, Kv i := by
    rw [Fintype.card_piFinset]; simp
  have hrank : ∀ a, rank a < ∏ i, Kv i := by
    intro a
    rw [← hcardS]
    refine card_lt_card ⟨filter_subset _ _, fun h => ?_⟩
    have := mem_filter.mp (h (hmem a))
    exact lt_irrefl _ this.2
  refine depth_le_of_label rank hrank f m marked (fun i hi => ?_) (fun i hi hm => ?_)
  · exact card_le_card fun y hy => by
      obtain ⟨h1, h2⟩ := mem_filter.mp hy
      exact mem_filter.mpr ⟨h1, lt_of_lt_of_le h2 (hmono i hi)⟩
  · refine card_lt_card ⟨fun y hy => ?_, fun h => ?_⟩
    · obtain ⟨h1, h2⟩ := mem_filter.mp hy
      exact mem_filter.mpr ⟨h1, lt_trans h2 (hstrict i hi hm)⟩
    · have := mem_filter.mp (h (mem_filter.mpr ⟨hmem (f (i + 1)), hstrict i hi hm⟩))
      exact lt_irrefl _ this.2

/-! ### The label -/

section Label

variable {ι : Type*} [Fintype ι] {N : ℕ}
variable (x0 : ℕ → ℤ) (W : ℕ → ℕ) (ρ : ℕ) (A : Fam ι N) {q : ℕ} (β : Fin q → ℕ)

/-- The event count of window `j`: owners up to `t` of scale at least `β j`. -/
def nev (j : Fin q) (t : ℕ) : ℕ := (univ.filter fun F => A.o F ≤ t ∧ β j ≤ lam (A.d F)).card

/-- The window index of position `p < 2q`. -/
def posIdx {q : ℕ} (p : ℕ) (hp : p < 2 * q) : Fin q := ⟨q - 1 - p / 2, by omega⟩

variable (K₀ K : ℕ) (ω₀ : ℕ) (ωd ωe : Fin q → ℕ)

/-- **The digits of the label of Theorem M.** -/
def mdig (t : ℕ) (p : Fin (2 * q + 1)) : ℕ :=
  if hp : p.val < 2 * q then
    if p.val % 2 = 0 then (lcnt x0 W ρ ((posIdx p.val hp).val + 1) t + ωd (posIdx p.val hp)) % K
    else (nev A β (posIdx p.val hp) t + ωe (posIdx p.val hp)) % K
  else (lcnt x0 W ρ 0 t + ω₀) % K₀

/-- The radices: `K₀` for `d_0` and `K` for the other digits. -/
def mradix (p : Fin (2 * q + 1)) : ℕ := if p.val < 2 * q then K else K₀

theorem mdig_lt (hK₀ : 0 < K₀) (hK : 0 < K) (t : ℕ) (p : Fin (2 * q + 1)) :
    mdig x0 W ρ A β K₀ K ω₀ ωd ωe t p < mradix K₀ K p := by
  unfold mdig mradix
  split_ifs <;> exact Nat.mod_lt _ (by assumption)

theorem prod_mradix (K₀ K : ℕ) : ∏ p : Fin (2 * q + 1), mradix K₀ K p = K₀ * K ^ (2 * q) := by
  rw [Fin.prod_univ_castSucc]
  simp only [mradix, Fin.val_castSucc, Fin.is_lt, ↓reduceIte, Fin.val_last, lt_irrefl,
    prod_const, card_univ, Fintype.card_fin]
  ring

/-- The position of `d_{j+1}`. -/
def posD {q : ℕ} (j : Fin q) : Fin (2 * q + 1) := ⟨2 * (q - 1 - j.val), by omega⟩

/-- The position of `e_{j+1}`. -/
def posE {q : ℕ} (j : Fin q) : Fin (2 * q + 1) := ⟨2 * (q - 1 - j.val) + 1, by omega⟩

/-- The position of `d_0`. -/
def pos0 (q : ℕ) : Fin (2 * q + 1) := ⟨2 * q, by omega⟩

/-- Every position is that of some digit. -/
theorem pos_cases (p : Fin (2 * q + 1)) :
    p = pos0 q ∨ (∃ hp : p.val < 2 * q, p.val % 2 = 0 ∧ p = posD (posIdx p.val hp)) ∨
      (∃ hp : p.val < 2 * q, p.val % 2 = 1 ∧ p = posE (posIdx p.val hp)) := by
  by_cases hp : p.val < 2 * q
  · rcases Nat.mod_two_eq_zero_or_one p.val with h | h
    · right; left
      refine ⟨hp, h, Fin.ext ?_⟩
      simp only [posD, posIdx]
      omega
    · right; right
      refine ⟨hp, h, Fin.ext ?_⟩
      simp only [posE, posIdx]
      omega
  · left
    exact Fin.ext (by simp only [pos0]; have := p.isLt; omega)

theorem mdig_posD (t : ℕ) (j : Fin q) :
    mdig x0 W ρ A β K₀ K ω₀ ωd ωe t (posD j) = (lcnt x0 W ρ (j.val + 1) t + ωd j) % K := by
  have hp : (posD j).val < 2 * q := by simp only [posD]; omega
  have hidx : posIdx (posD j).val hp = j := Fin.ext (by simp only [posIdx, posD]; omega)
  unfold mdig
  simp only [hp, ↓reduceDIte, show (posD j).val % 2 = 0 by simp only [posD]; omega, ↓reduceIte,
    hidx]

theorem mdig_posE (t : ℕ) (j : Fin q) :
    mdig x0 W ρ A β K₀ K ω₀ ωd ωe t (posE j) = (nev A β j t + ωe j) % K := by
  have hp : (posE j).val < 2 * q := by simp only [posE]; omega
  have hidx : posIdx (posE j).val hp = j := Fin.ext (by simp only [posIdx, posE]; omega)
  unfold mdig
  simp only [hp, ↓reduceDIte, show ¬ ((posE j).val % 2 = 0) by simp only [posE]; omega,
    ↓reduceIte, hidx]

theorem mdig_pos0 (t : ℕ) :
    mdig x0 W ρ A β K₀ K ω₀ ωd ωe t (pos0 q) = (lcnt x0 W ρ 0 t + ω₀) % K₀ := by
  unfold mdig
  simp [pos0]

/-- The label as a lexicographic tuple. -/
def mlab (t : ℕ) : Lex (Fin (2 * q + 1) → ℕ) := toLex (mdig x0 W ρ A β K₀ K ω₀ ωd ωe t)

end Label

/-! ### Comparisons -/

section Compare

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}
variable {x0 : ℕ → ℤ} {W : ℕ → ℕ} {ρ : ℕ} {A : Fam ι N} {q : ℕ} {β : Fin q → ℕ}
variable {K₀ K ω₀ : ℕ} {ωd ωe : Fin q → ℕ}

omit [DecidableEq ι] in
theorem nev_mono (j : Fin q) {t t' : ℕ} (h : t ≤ t') : nev A β j t ≤ nev A β j t' :=
  card_le_card fun F hF => by
    obtain ⟨h1, h2, h3⟩ := mem_filter.mp hF
    exact mem_filter.mpr ⟨h1, le_trans h2 h, h3⟩

/-- Digits that grow without a wrap. -/
theorem digit_le_of_no_wrap {n n' c K : ℕ} (hn : n ≤ n') (h : (n + c) / K = (n' + c) / K) :
    (n + c) % K ≤ (n' + c) % K := by
  have := Fam.mod_of_no_wrap (K := K) hn h; omega

theorem digit_lt_of_no_wrap {n n' c K : ℕ} (hn : n < n') (h : (n + c) / K = (n' + c) / K) :
    (n + c) % K < (n' + c) % K := by
  have := Fam.mod_of_no_wrap (K := K) hn.le h; omega

variable (hx0 : IsWalk x0) (hW : ∀ i, 2 ≤ W i) (hdiv : ∀ i j, i ≤ j → W i ∣ W j)

omit [DecidableEq ι] in
include hx0 hW hdiv in
/-- **Chords.** A chord at a cell that is not a line is not violated unless the counter of its
deciding level wraps, or some `e_j` with `j + 1` above the deciding level wraps. -/
theorem chord_lt {T p u : ℕ} (hγ : IsHop x0 T p u) (hc : ¬ LineAt W ρ 0 (x0 p))
    (hd : chordLevel x0 W ρ q p u = 0 →
      (lcnt x0 W ρ 0 p + ω₀) / K₀ = (lcnt x0 W ρ 0 u + ω₀) / K₀)
    (hd' : ∀ j : Fin q, chordLevel x0 W ρ q p u = j.val + 1 →
      (lcnt x0 W ρ (j.val + 1) p + ωd j) / K = (lcnt x0 W ρ (j.val + 1) u + ωd j) / K)
    (he : ∀ j : Fin q, chordLevel x0 W ρ q p u < j.val + 1 →
      (nev A β j p + ωe j) / K = (nev A β j u + ωe j) / K) :
    mlab x0 W ρ A β K₀ K ω₀ ωd ωe p < mlab x0 W ρ A β K₀ K ω₀ ωd ωe u := by
  have hpu : p ≤ u := by have := hγ.1; omega
  have hlevq := chordLevel_le (x0 := x0) (W := W) (ρ := ρ) q p u
  -- the counters above the deciding level do not change, and that of the level rises
  have heq : ∀ j : Fin q, chordLevel x0 W ρ q p u < j.val + 1 →
      lcnt x0 W ρ (j.val + 1) u = lcnt x0 W ρ (j.val + 1) p := fun j hj =>
    lcnt_chord_eq hdiv hγ hc hj (by omega)
  have hlt := lcnt_chord_lt hx0 hW hdiv (q := q) hγ hc
  rcases Nat.eq_zero_or_pos (chordLevel x0 W ρ q p u) with h0 | hpos
  · rw [h0] at hlt
    apply Fam.lex_lt_of_le_of_lt (pos0 q)
    · intro p' _
      rcases pos_cases p' with rfl | ⟨hp, -, hpe⟩ | ⟨hp, -, hpe⟩
      · rw [mdig_pos0, mdig_pos0]
        exact (digit_lt_of_no_wrap hlt (hd h0)).le
      · rw [hpe, mdig_posD, mdig_posD, heq _ (by omega)]
      · rw [hpe, mdig_posE, mdig_posE]
        exact digit_le_of_no_wrap (nev_mono _ hpu) (he _ (by omega))
    · show mdig x0 W ρ A β K₀ K ω₀ ωd ωe p (pos0 q) < mdig x0 W ρ A β K₀ K ω₀ ωd ωe u (pos0 q)
      rw [mdig_pos0, mdig_pos0]
      exact digit_lt_of_no_wrap hlt (hd h0)
  · obtain ⟨j0, hj0⟩ : ∃ j0 : Fin q, chordLevel x0 W ρ q p u = j0.val + 1 :=
      ⟨⟨chordLevel x0 W ρ q p u - 1, by omega⟩, by simp only; omega⟩
    rw [hj0] at hlt
    have hnw := hd' j0 hj0
    apply Fam.lex_lt_of_le_of_lt (posD j0)
    · intro p' hp'
      have hp'' : p'.val ≤ 2 * (q - 1 - j0.val) := hp'
      rcases pos_cases p' with rfl | ⟨hp, -, hpe⟩ | ⟨hp, -, hpe⟩
      · simp only [pos0] at hp''; omega
      · rw [hpe, mdig_posD, mdig_posD]
        by_cases hjj : posIdx p'.val hp = j0
        · rw [hjj]
          exact (digit_lt_of_no_wrap hlt hnw).le
        · have : chordLevel x0 W ρ q p u < (posIdx p'.val hp).val + 1 := by
            have h1 : (posIdx p'.val hp).val ≠ j0.val := fun h => hjj (Fin.ext h)
            simp only [posIdx] at h1 ⊢
            rw [hpe] at hp''
            simp only [posD, posIdx] at hp''
            omega
          rw [heq _ this]
      · rw [hpe, mdig_posE, mdig_posE]
        have : chordLevel x0 W ρ q p u < (posIdx p'.val hp).val + 1 := by
          rw [hpe] at hp''
          simp only [posE, posIdx] at hp''
          simp only [posIdx]
          omega
        exact digit_le_of_no_wrap (nev_mono _ hpu) (he _ this)
    · show mdig x0 W ρ A β K₀ K ω₀ ωd ωe p (posD j0) < mdig x0 W ρ A β K₀ K ω₀ ωd ωe u (posD j0)
      rw [mdig_posD, mdig_posD]
      exact digit_lt_of_no_wrap hlt hnw

omit [DecidableEq ι] in
include hx0 hW hdiv in
/-- **Hops of the bounded walks.** A hop of window `j`, in the span of its family with the owner
strictly inside, not at a line time, along which head `0` visits no level-`(j+1)` line and no
`e_{j'}` with `j' ≥ j` wraps, is not violated. -/
theorem ahop_lt {p u : ℕ} {F0 : ι} (j : Fin q) (hpo : p < A.o F0) (hou : A.o F0 < u)
    (hβ : β j ≤ lam (A.d F0)) (hp : ¬ LineAt W ρ 0 (x0 p)) (hu : ¬ LineAt W ρ 0 (x0 u))
    (hnl : ∀ t ∈ Ioo p u, ¬ LineAt W ρ (j.val + 1) (x0 t))
    (he : ∀ j' : Fin q, j ≤ j' → (nev A β j' p + ωe j') / K = (nev A β j' u + ωe j') / K) :
    mlab x0 W ρ A β K₀ K ω₀ ωd ωe p < mlab x0 W ρ A β K₀ K ω₀ ωd ωe u := by
  have hpu : p < u := by omega
  apply Fam.lex_lt_of_le_of_lt (posE j)
  · intro p' hp'
    have hp'' : p'.val ≤ 2 * (q - 1 - j.val) + 1 := hp'
    rcases pos_cases p' with rfl | ⟨hp1, -, hpe⟩ | ⟨hp1, -, hpe⟩
    · simp only [pos0] at hp''; omega
    · rw [hpe, mdig_posD, mdig_posD]
      have hjj : j.val + 1 ≤ (posIdx p'.val hp1).val + 1 := by
        rw [hpe] at hp''
        simp only [posD, posIdx] at hp''
        simp only [posIdx]
        omega
      rw [lcnt_window_eq hx0 hW hdiv hpu (by omega) hp hu hnl hjj]
    · rw [hpe, mdig_posE, mdig_posE]
      have hjj : j ≤ posIdx p'.val hp1 := by
        rw [hpe] at hp''
        simp only [posE, posIdx] at hp''
        show j.val ≤ (posIdx p'.val hp1).val
        simp only [posIdx]
        omega
      exact digit_le_of_no_wrap (nev_mono _ hpu.le) (he _ hjj)
  · show mdig x0 W ρ A β K₀ K ω₀ ωd ωe p (posE j) < mdig x0 W ρ A β K₀ K ω₀ ωd ωe u (posE j)
    rw [mdig_posE, mdig_posE]
    refine digit_lt_of_no_wrap ?_ (he j le_rfl)
    unfold nev
    refine card_lt_card ⟨fun F' hF' => ?_, fun hsub => ?_⟩
    · obtain ⟨h1, h2, h3⟩ := mem_filter.mp hF'
      exact mem_filter.mpr ⟨h1, by omega, h3⟩
    · have := mem_filter.mp (hsub (mem_filter.mpr ⟨mem_univ F0, hou.le, hβ⟩))
      omega

omit [DecidableEq ι] in
include hx0 hW hdiv in
/-- **State edges.** Along a state edge between non-line times, without a wrap of `d_0` or of any
`e_j`, the label does not decrease. -/
theorem state_le {t : ℕ} (ht : 1 ≤ t) (h1 : ¬ LineAt W ρ 0 (x0 t))
    (h2 : ¬ LineAt W ρ 0 (x0 (t - 1)))
    (hd : (lcnt x0 W ρ 0 (t - 1) + ω₀) / K₀ = (lcnt x0 W ρ 0 t + ω₀) / K₀)
    (he : ∀ j : Fin q, (nev A β j (t - 1) + ωe j) / K = (nev A β j t + ωe j) / K) :
    mlab x0 W ρ A β K₀ K ω₀ ωd ωe (t - 1) ≤ mlab x0 W ρ A β K₀ K ω₀ ωd ωe t := by
  apply Fam.lex_le_of_le
  intro p'
  rcases pos_cases p' with rfl | ⟨hp1, -, hpe⟩ | ⟨hp1, -, hpe⟩
  · rw [mdig_pos0, mdig_pos0]
    refine digit_le_of_no_wrap ?_ hd
    rw [lcnt_state_zero hx0 hW ht h1 h2]
    omega
  · rw [hpe, mdig_posD, mdig_posD, lcnt_state_pos hx0 hW hdiv ht (by omega) h1 h2]
  · rw [hpe, mdig_posE, mdig_posE]
    exact digit_le_of_no_wrap (nev_mono _ (by omega)) (he _)

end Compare

end BoundedNesting
