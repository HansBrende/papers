import BoundedStackDepth.HopData

/-!
# Accounting: counting tools for the cut

* `card_spanning_near_lt` (the counting fact for aligned hops): at a time `c`, the hops of one walk
  spanning `c` whose cells lie within distance `< R` of a point number fewer than `2R`, because each cell
  carries at most one hop spanning `c` (`hop_unique`).
* `card_aligned_spanning_lt`: in a frame system, fewer than `2^{θ+3}` hops aligned at offset `r` span a
  time `c` with the floor above their group at most `θ`: they are home-near, so their cells lie within
  `2^{θ+2}` of the home at `c`.
* `card_ground_spanning_lt`: fewer than `2 · 2^θ` upper hops that are ground at offset `r` span `c`, for
  `θ ≥ θ(1)`: their extent is below the owner's prominence, which is below `2^{θ(1)}` (P1, then P3).
-/

namespace BoundedStackDepth

open BoundedNesting Finset

/-- At a time `c`, fewer than `2R` hops of one walk span `c` with cells within distance `< R` of `h`. -/
theorem card_spanning_near_lt (x : ℕ → ℤ) (T c : ℕ) (h : ℤ) {R : ℕ} (hR : 1 ≤ R) :
    ((hops x T).filter (fun e => e.1 < c ∧ c ≤ e.2 ∧ (x e.1 - h).natAbs < R)).card < 2 * R := by
  have hinj : Set.InjOn (fun e : ℕ × ℕ => x e.1)
      ((hops x T).filter (fun e => e.1 < c ∧ c ≤ e.2 ∧ (x e.1 - h).natAbs < R) : Set (ℕ × ℕ)) := by
    intro e he e' he' hc
    obtain ⟨he, h1, h2, -⟩ := mem_filter.mp (Finset.mem_coe.mp he)
    obtain ⟨he', h1', h2', -⟩ := mem_filter.mp (Finset.mem_coe.mp he')
    obtain ⟨hp, hu⟩ := hop_unique (mem_hops.mp he) (mem_hops.mp he') hc ⟨h1, h2⟩ ⟨h1', h2'⟩
    exact Prod.ext hp hu
  calc ((hops x T).filter (fun e => e.1 < c ∧ c ≤ e.2 ∧ (x e.1 - h).natAbs < R)).card
      ≤ (Ioo (h - R) (h + R)).card := card_le_card_of_injOn _ (fun e he => by
        have := (mem_filter.mp he).2.2.2
        exact Finset.mem_coe.mpr (mem_Ioo.mpr ⟨by omega, by omega⟩)) hinj
    _ < 2 * R := by rw [Int.card_Ioo]; omega

open Classical in
/-- **The counting fact for aligned hops.** At a time `c`, fewer than `2^{θ+3}` hops of the walk of a frame
system span `c`, are aligned at offset `r`, and have `θ(d + 1) ≤ θ` for their group `d`. -/
theorem card_aligned_spanning_lt (S : FrameSystem) (h₀ r c θ : ℕ) :
    ((hops S.x S.T).filter (fun e => e.1 < c ∧ c ≤ e.2 ∧
      Aligned h₀ r (bandP S e) (bandU S e) (ownerScale S e) (homeBand S e) (pushMax S e)
        (FrameMicro S e) ∧ flr h₀ r (grp h₀ r (bandU S e) + 1) ≤ θ)).card < 2 * 2 ^ (θ + 2) := by
  refine lt_of_le_of_lt (card_le_card fun e he => ?_)
    (card_spanning_near_lt S.x S.T c (S.home c) (R := 2 ^ (θ + 2)) (Nat.one_le_two_pow))
  obtain ⟨hh, h1, h2, hal, hθ⟩ := mem_filter.mp he
  refine mem_filter.mpr ⟨hh, h1, h2, ?_⟩
  have hnear : band ((Icc e.1 e.2).sup fun c => (S.x e.1 - S.home c).natAbs) < θ + 2 :=
    lt_of_lt_of_le hal.2.1 (by omega)
  have hM := lt_pow_band_succ ((Icc e.1 e.2).sup fun c => (S.x e.1 - S.home c).natAbs)
  have hc : (S.x e.1 - S.home c).natAbs ≤ (Icc e.1 e.2).sup fun c => (S.x e.1 - S.home c).natAbs :=
    le_sup (f := fun c => (S.x e.1 - S.home c).natAbs) (mem_Icc.mpr ⟨h1.le, h2⟩)
  calc (S.x e.1 - S.home c).natAbs < 2 ^ (band ((Icc e.1 e.2).sup fun c =>
        (S.x e.1 - S.home c).natAbs) + 1) := lt_of_le_of_lt hc hM
    _ ≤ 2 ^ (θ + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- The extent of an upper hop is at most its owner's height above the cell. -/
theorem extent_le_owner {x : ℕ → ℤ} {p u : ℕ} (hu : IsUpperHop x p u) :
    (extent x p u : ℤ) ≤ x (hopOwner x p u) - x p := by
  have ho := isOwner_hopOwner_of_upper hu
  unfold extent
  rcases (Ioo p u).eq_empty_or_nonempty with h | h
  · rw [h, sup_empty]
    have := hu.above _ ho.gt ho.lt
    simp only [bot_eq_zero', Nat.cast_zero]
    omega
  · obtain ⟨t, ht, he⟩ := exists_mem_eq_sup _ h fun t => (x t - x p).natAbs
    rw [he]
    obtain ⟨h1, h2⟩ := mem_Ioo.mp ht
    have := hu.above t h1 h2
    have := ho.max t h1 h2
    omega

/-- **The counting fact for ground hops.** For `θ ≥ θ(1)`, fewer than `2 · 2^θ` upper hops of the walk of
a frame system that are ground at offset `r` span a time `c`. -/
theorem card_ground_spanning_lt (S : FrameSystem) (hx : IsWalk S.x) {h₀ r : ℕ} (hpos : 0 < h₀)
    (c θ : ℕ) (hθ : flr h₀ r 1 ≤ θ) :
    ((upperHops S.x S.T).filter (fun e => e.1 < c ∧ c ≤ e.2 ∧ Ground h₀ r (ownerScale S e))).card <
      2 * 2 ^ θ := by
  refine lt_of_le_of_lt (card_le_card fun e he => ?_)
    (card_spanning_hops_lt S.x S.T c (2 ^ θ) Nat.one_le_two_pow)
  obtain ⟨heU, h1, h2, hg⟩ := mem_filter.mp he
  obtain ⟨hh, hu⟩ := (mem_upperHops hx).mp heU
  refine mem_filter.mpr ⟨mem_hops.mpr hh, h1, h2, ?_⟩
  have hP := sub_le_prom hu (isOwner_hopOwner_of_upper hu) hh.2.1
  have hext := extent_le_owner hu
  have hσ : band (prom S.x S.T (hopOwner S.x e.1 e.2)) < flr h₀ r 1 := by
    unfold Ground ownerScale grp at hg
    unfold flr
    have := (Nat.div_eq_zero_iff_lt (by omega)).mp hg
    omega
  have hlt := lt_pow_band_succ (prom S.x S.T (hopOwner S.x e.1 e.2))
  have hpow : 2 ^ (band (prom S.x S.T (hopOwner S.x e.1 e.2)) + 1) ≤ 2 ^ θ :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have : (extent S.x e.1 e.2 : ℤ) < 2 ^ θ := by
    have h3 : ((prom S.x S.T (hopOwner S.x e.1 e.2) : ℕ) : ℤ) < ((2 ^ θ : ℕ) : ℤ) := by
      exact_mod_cast lt_of_lt_of_le hlt hpow
    push_cast at h3
    linarith
  exact_mod_cast this

end BoundedStackDepth
