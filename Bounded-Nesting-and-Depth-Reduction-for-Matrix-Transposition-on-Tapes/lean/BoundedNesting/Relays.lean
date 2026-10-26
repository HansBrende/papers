import BoundedNesting.Stacks

/-!
# Relays must be allowed

For walks without pauses, `RF k` says: for every `ε > 0` there are `D(ε)` and `δ(ε)`, with
`δ(ε) → 0` as `ε → 0`, such that all `k` walks of length `T` have a set `R` of pairs `(h, c)` with
`|R| ≤ δ(ε) T` and a genie `Γ ⊆ [0, T)` with `|Γ| ≤ εT` such that, on every path of the walk DAG whose
vertices after the first avoid `Γ`, every hop carried by an edge after the first `D(ε)` edges lies
at a pair of `R`. `TCPgenie k` is TCP in genie form for `k` walks without pauses.

`tcpGenie_of_rf`: `RF (k + 1)` implies `TCPgenie k`. The extra walk is the zigzag `zig M`, which on
the block `[jM, (j+1)M)` alternates between `j` and `j + 1`; for odd `M` it has no pauses. Every
time that is neither a first visit of the zigzag, nor the end of one of its hops at a pair of `R`,
nor the end of a hop that starts in `Γ`, can extend a long `Γ`-free path by a hop edge of the
zigzag. So the ends of long `Γ`-free paths form a set `Δ` of fewer than about `T/M + 2M|R| + |Γ|`
times, and `Γ ∪ Δ` is the genie.
-/

namespace BoundedNesting

open Finset Filter Topology

variable {k : ℕ}

/-- A path `f 0 → f 1 → ⋯ → f n` of the walk DAG of `xs` on `[0, T)`. -/
def IsDagPath (xs : Fin k → ℕ → ℤ) (T : ℕ) (f : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ i < n, (f (i + 1) + 1 = f i ∧ 1 ≤ f i ∧ f i < T) ∨ (f (i + 1), f i) ∈ hopPairs (allHops xs T)

/-- Walks without pauses before `T`. -/
def NoPauses (xs : Fin k → ℕ → ℤ) (T : ℕ) : Prop := ∀ h t, t + 1 < T → xs h (t + 1) ≠ xs h t

/-- **`RF k`**: relay-free certificates for `k` walks without pauses. -/
def RF (k : ℕ) : Prop :=
  ∃ (D : ℝ → ℕ) (δ : ℝ → ℝ), Tendsto δ (𝓝[>] 0) (𝓝 0) ∧
    ∀ ε : ℝ, 0 < ε → ∀ (T : ℕ) (xs : Fin k → ℕ → ℤ), (∀ h, IsWalk (xs h)) → NoPauses xs T →
      ∃ (R : Finset (Fin k × ℤ)) (Γ : Finset ℕ), (R.card : ℝ) ≤ δ ε * T ∧ Γ ⊆ range T ∧
        (Γ.card : ℝ) ≤ ε * T ∧
        ∀ f n, IsDagPath xs T f n → (∀ i, 1 ≤ i → i ≤ n → f i ∉ Γ) →
          ∀ i, D ε < i → i ≤ n → (f i, f (i - 1)) ∈ hopPairs (allHops xs T) →
            ∀ h, IsHop (xs h) T (f i) (f (i - 1)) → (h, xs h (f i)) ∈ R

/-- **TCP in genie form** for `k` walks without pauses. -/
def TCPgenie (k : ℕ) : Prop :=
  ∀ ε' : ℝ, 0 < ε' → ∃ D' : ℕ, ∀ (T : ℕ) (xs : Fin k → ℕ → ℤ), (∀ h, IsWalk (xs h)) →
    NoPauses xs T → ∃ Γ' : Finset ℕ, Γ' ⊆ range T ∧ (Γ'.card : ℝ) ≤ ε' * T ∧
      ∀ f n, IsDagPath xs T f n → (∀ i, 1 ≤ i → i ≤ n → f i ∉ Γ') → n ≤ D'

/-! ### Paths go back in time -/

theorem IsDagPath.lt {xs : Fin k → ℕ → ℤ} {T : ℕ} {f : ℕ → ℕ} {n : ℕ} (hf : IsDagPath xs T f n)
    {i : ℕ} (hi : i < n) : f (i + 1) < f i ∧ f i < T := by
  rcases hf i hi with ⟨h1, -, h3⟩ | h
  · exact ⟨by omega, h3⟩
  · obtain ⟨η, hη, he⟩ := mem_image.mp h
    have := mem_allHops.mp hη
    simp only [Prod.mk.injEq] at he
    rw [← he.1, ← he.2]
    exact ⟨by have := this.1; omega, this.2.1⟩

theorem IsDagPath.length_le {xs : Fin k → ℕ → ℤ} {T : ℕ} {f : ℕ → ℕ} {n : ℕ}
    (hf : IsDagPath xs T f n) : ∀ i ≤ n, f i + i ≤ f 0 := by
  intro i hi
  induction i with
  | zero => simp
  | succ i ih =>
    have := (hf.lt (i := i) (by omega)).1
    have := ih (by omega)
    omega

theorem IsDagPath.lt_T {xs : Fin k → ℕ → ℤ} {T : ℕ} {f : ℕ → ℕ} {n : ℕ} (hf : IsDagPath xs T f n)
    (hn : 1 ≤ n) : n < T := by
  have h1 := hf.length_le n le_rfl
  have h2 := (hf.lt (i := 0) (by omega)).2
  omega

/-! ### The zigzag -/

/-- The zigzag with blocks of length `M`: on `[jM, (j+1)M)` it alternates between `j` and `j + 1`. -/
def zig (M : ℕ) (t : ℕ) : ℤ := ((t / M : ℕ) : ℤ) + (((t % M) % 2 : ℕ) : ℤ)

theorem zig_step {M : ℕ} (hM : Odd M) (t : ℕ) :
    zig M (t + 1) - zig M t = 1 ∨ zig M (t + 1) - zig M t = -1 := by
  have hM0 : 0 < M := hM.pos
  have h1 := Nat.div_add_mod t M
  have h2 := Nat.mod_lt t hM0
  obtain ⟨m, hm⟩ := hM
  unfold zig
  by_cases hb : t % M + 1 = M
  · have e : t + 1 = M * (t / M + 1) := by rw [Nat.mul_add, Nat.mul_one]; omega
    have hq : (t + 1) / M = t / M + 1 := by rw [e, Nat.mul_div_cancel_left _ hM0]
    have hr : (t + 1) % M = 0 := by rw [e, Nat.mul_mod_right]
    rw [hq, hr]
    push_cast
    omega
  · have hq : (t + 1) / M = t / M := by
      rw [show t + 1 = (t % M + 1) + M * (t / M) by omega, Nat.add_mul_div_left _ _ hM0,
        Nat.div_eq_of_lt (by omega), zero_add]
    have hr : (t + 1) % M = t % M + 1 := by
      rw [show t + 1 = (t % M + 1) + M * (t / M) by omega, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt (by omega)]
    rw [hq, hr]
    push_cast
    omega

theorem zig_isWalk {M : ℕ} (hM : Odd M) : IsWalk (zig M) := by
  intro t
  rcases zig_step hM t with h | h <;> rw [h] <;> norm_num

theorem zig_ne {M : ℕ} (hM : Odd M) (t : ℕ) : zig M (t + 1) ≠ zig M t := by
  rcases zig_step hM t with h | h <;> omega

theorem zig_nonneg (M t : ℕ) : 0 ≤ zig M t := by unfold zig; positivity

theorem zig_le (M t : ℕ) : zig M t ≤ ((t / M : ℕ) : ℤ) + 1 := by
  unfold zig
  have : (t % M) % 2 < 2 := Nat.mod_lt _ (by norm_num)
  omega

/-- Every cell is visited at most `2M` times by the zigzag. -/
theorem card_zig_visits_le {M : ℕ} (hM0 : 0 < M) (T : ℕ) (c : ℤ) :
    ((range T).filter fun t => zig M t = c).card ≤ 2 * M := by
  by_cases hc : 0 ≤ c
  · obtain ⟨c', rfl⟩ : ∃ c' : ℕ, c = c' := ⟨c.toNat, (Int.toNat_of_nonneg hc).symm⟩
    calc ((range T).filter fun t => zig M t = c').card ≤ (Ico ((c' - 1) * M) ((c' + 1) * M)).card := by
          refine card_le_card fun t ht => ?_
          obtain ⟨-, hz⟩ := mem_filter.mp ht
          have h1 := Nat.div_add_mod t M
          have h2 := Nat.mod_lt t hM0
          have hq : t / M = c' ∨ t / M + 1 = c' := by
            unfold zig at hz
            have : (t % M) % 2 < 2 := Nat.mod_lt _ (by norm_num)
            omega
          refine mem_Ico.mpr ⟨?_, ?_⟩
          · rcases hq with hq | hq
            · calc (c' - 1) * M ≤ c' * M := Nat.mul_le_mul_right _ (by omega)
                _ = M * (t / M) := by rw [hq, mul_comm]
                _ ≤ t := by omega
            · calc (c' - 1) * M = M * (t / M) := by rw [← hq, Nat.add_sub_cancel, mul_comm]
                _ ≤ t := by omega
          · rcases hq with hq | hq
            · calc t < M * (t / M) + M := by omega
                _ = (c' + 1) * M := by rw [hq]; ring
            · calc t < M * (t / M) + M := by omega
                _ = c' * M := by rw [← hq]; ring
                _ ≤ (c' + 1) * M := Nat.mul_le_mul_right _ (by omega)
      _ ≤ 2 * M := by
          rw [Nat.card_Ico]
          have : (c' + 1) * M ≤ (c' - 1) * M + 2 * M := by
            rcases Nat.eq_zero_or_pos c' with rfl | hc'
            · simp only [zero_add, one_mul, Nat.zero_sub, zero_mul]; omega
            · have : (c' + 1) * M = (c' - 1) * M + 2 * M := by
                rw [show c' + 1 = (c' - 1) + 2 by omega, add_mul]
              omega
          omega
  · have : (range T).filter (fun t => zig M t = c) = ∅ :=
      filter_eq_empty_iff.mpr fun t _ h => hc (h ▸ zig_nonneg M t)
    rw [this]
    simp

/-- Every visit of the zigzag that is not a first visit ends a long hop of the zigzag. -/
theorem exists_prev_hop {M : ℕ} (hM : Odd M) {T s : ℕ} (hs : s < T)
    (h : ∃ t < s, zig M t = zig M s) : ∃ p, IsHop (zig M) T p s := by
  classical
  have hne : ((range s).filter fun t => zig M t = zig M s).Nonempty := by
    obtain ⟨t, ht, he⟩ := h
    exact ⟨t, mem_filter.mpr ⟨mem_range.mpr ht, he⟩⟩
  set p := ((range s).filter fun t => zig M t = zig M s).max' hne
  obtain ⟨hp1, hp2⟩ := mem_filter.mp (max'_mem _ hne)
  have hp1 := mem_range.mp hp1
  refine ⟨p, ⟨?_, hs, hp2.symm, fun t ht => ?_⟩⟩
  · by_contra hlt
    have hps : p + 1 = s := by omega
    exact zig_ne hM p (by rw [hps]; exact hp2.symm)
  · obtain ⟨ht1, ht2⟩ := mem_Ioo.mp ht
    intro he
    have := le_max' ((range s).filter fun t => zig M t = zig M s) t
      (mem_filter.mpr ⟨mem_range.mpr ht2, he.trans hp2⟩)
    omega

/-- The first visits of the zigzag number at most `(T - 1)/M + 2`. -/
theorem card_firstVisits_le (M T : ℕ) :
    ((range T).filter fun s => ∀ t < s, zig M t ≠ zig M s).card ≤ (T - 1) / M + 2 := by
  classical
  calc ((range T).filter fun s => ∀ t < s, zig M t ≠ zig M s).card
      ≤ (Icc (0 : ℤ) (((T - 1) / M : ℕ) + 1)).card := by
        refine card_le_card_of_injOn (zig M) (fun s hs => ?_) (fun s hs s' hs' he => ?_)
        · obtain ⟨hsT, -⟩ := mem_filter.mp (Finset.mem_coe.mp hs)
          have h1 := zig_le M s
          have h2 : s / M ≤ (T - 1) / M := Nat.div_le_div_right (by have := mem_range.mp hsT; omega)
          exact Finset.mem_coe.mpr (mem_Icc.mpr ⟨zig_nonneg M s, by
            have : ((s / M : ℕ) : ℤ) ≤ (((T - 1) / M : ℕ) : ℤ) := by exact_mod_cast h2
            omega⟩)
        · obtain ⟨-, h1⟩ := mem_filter.mp (Finset.mem_coe.mp hs)
          obtain ⟨-, h2⟩ := mem_filter.mp (Finset.mem_coe.mp hs')
          rcases lt_trichotomy s s' with hlt | heq | hgt
          · exact absurd he (h2 s hlt)
          · exact heq
          · exact absurd he.symm (h1 s' hgt)
    _ = (T - 1) / M + 2 := by
        generalize (T - 1) / M = q
        rw [Int.card_Icc]
        omega

/-- The walks `xs` with the zigzag as the last head. -/
def withZig (xs : Fin k → ℕ → ℤ) (M : ℕ) : Fin (k + 1) → ℕ → ℤ :=
  Fin.lastCases (motive := fun _ => ℕ → ℤ) (zig M) xs

theorem withZig_last (xs : Fin k → ℕ → ℤ) (M : ℕ) : withZig xs M (Fin.last k) = zig M := by
  simp [withZig]

theorem withZig_castSucc (xs : Fin k → ℕ → ℤ) (M : ℕ) (h : Fin k) :
    withZig xs M h.castSucc = xs h := by
  simp [withZig]

/-- The walk DAG of `xs` is a sub-DAG of that of `xs` with the zigzag. -/
theorem hopPairs_subset_withZig (xs : Fin k → ℕ → ℤ) (M T : ℕ) :
    hopPairs (allHops xs T) ⊆ hopPairs (allHops (withZig xs M) T) := by
  intro e he
  obtain ⟨η, hη, rfl⟩ := mem_image.mp he
  refine mem_image.mpr ⟨(η.1.castSucc, η.2.1, η.2.2), mem_allHops.mpr ?_, rfl⟩
  simp only [withZig_castSucc]
  exact mem_allHops.mp hη

theorem IsDagPath.mono {xs : Fin k → ℕ → ℤ} {M T : ℕ} {f : ℕ → ℕ} {n : ℕ}
    (hf : IsDagPath xs T f n) : IsDagPath (withZig xs M) T f n := fun i hi =>
  (hf i hi).imp id fun h => hopPairs_subset_withZig xs M T h

/-- **Relays must be allowed.** `RF (k + 1)` implies TCP in genie form for `k` walks without
pauses. -/
theorem tcpGenie_of_rf (h : RF (k + 1)) : TCPgenie k := by
  classical
  obtain ⟨D, δ, hδ, hRF⟩ := h
  intro ε' hε'
  by_cases hbig : 1 ≤ ε'
  · refine ⟨0, fun T xs hx hnp => ⟨range T, Subset.refl _, ?_, fun f n hf hΓ => ?_⟩⟩
    · rw [card_range]
      have : (0 : ℝ) ≤ T := by positivity
      nlinarith
    · by_contra hn
      push Not at hn
      have h01 := hf.lt (i := 0) hn
      simp only [zero_add] at h01
      exact hΓ 1 le_rfl hn (mem_range.mpr (by omega))
  push Not at hbig
  -- the block length of the zigzag, odd and at least `4/ε'`
  set M := 2 * ⌈2 / ε'⌉₊ + 1 with hMdef
  have hMo : Odd M := ⟨⌈2 / ε'⌉₊, rfl⟩
  have hM0 : 0 < M := by omega
  have hMge : 4 / ε' ≤ (M : ℝ) := by
    have := Nat.le_ceil (2 / ε')
    rw [hMdef]; push_cast
    have : 4 / ε' = 2 * (2 / ε') := by ring
    linarith
  -- a small `ε` with `2M δ(ε) ≤ ε'/8`
  obtain ⟨ε, hε0, hε1, hε2⟩ : ∃ ε, 0 < ε ∧ ε ≤ ε' / 8 ∧ 2 * (M : ℝ) * δ ε ≤ ε' / 8 := by
    have hc : (0 : ℝ) < ε' / (16 * M) := by positivity
    have h1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), δ ε < ε' / (16 * M) := hδ (Iio_mem_nhds hc)
    have h2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < ε' / 8 :=
      nhdsWithin_le_nhds (Iio_mem_nhds (by positivity))
    have h3 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
    obtain ⟨ε, ⟨hε1, hε2⟩, hε3⟩ := ((h1.and h2).and h3).exists
    refine ⟨ε, hε3, hε2.le, ?_⟩
    have hMpos : (0 : ℝ) < M := by exact_mod_cast hM0
    calc 2 * (M : ℝ) * δ ε ≤ 2 * M * (ε' / (16 * M)) :=
          mul_le_mul_of_nonneg_left hε1.le (by positivity)
      _ = ε' / 8 := by field_simp; ring
  refine ⟨max (D ε) ⌈16 / ε'⌉₊, fun T xs hx hnp => ?_⟩
  by_cases hT : (T : ℝ) < 16 / ε'
  · -- short walks: every path is shorter than `T`
    refine ⟨∅, empty_subset _, by simp only [card_empty, Nat.cast_zero]; positivity,
      fun f n hf _ => ?_⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact Nat.zero_le _
    · have h1 := hf.lt_T hn
      have h2 : (n : ℝ) < 16 / ε' := lt_trans (by exact_mod_cast h1) hT
      have h3 : n ≤ ⌈16 / ε'⌉₊ := by
        have := Nat.le_ceil (16 / ε')
        exact_mod_cast (le_of_lt (lt_of_lt_of_le h2 this))
      exact h3.trans (le_max_right _ _)
  push Not at hT
  -- the walks with the zigzag
  set xs' := withZig xs M
  have hx' : ∀ h, IsWalk (xs' h) := by
    intro h
    refine Fin.lastCases ?_ (fun h => ?_) h
    · rw [show xs' (Fin.last k) = zig M from withZig_last xs M]; exact zig_isWalk hMo
    · rw [show xs' h.castSucc = xs h from withZig_castSucc xs M h]; exact hx h
  have hnp' : NoPauses xs' T := by
    intro h t ht
    refine Fin.lastCases ?_ (fun h => ?_) h
    · rw [show xs' (Fin.last k) = zig M from withZig_last xs M]; exact zig_ne hMo t
    · rw [show xs' h.castSucc = xs h from withZig_castSucc xs M h]; exact hnp h t ht
  obtain ⟨R, Γ, hR, hΓT, hΓ, hcert⟩ := hRF ε hε0 T xs' hx' hnp'
  -- the ends of long `Γ`-free paths
  set Δ := (range T).filter fun s => ∃ f n, IsDagPath xs' T f n ∧
    (∀ i, 1 ≤ i → i ≤ n → f i ∉ Γ) ∧ D ε < n ∧ f n = s
  set FV := (range T).filter fun s => ∀ t < s, zig M t ≠ zig M s
  set HR := (range T).filter fun s => (∃ t < s, zig M t = zig M s) ∧ (Fin.last k, zig M s) ∈ R
  set HΓ := (range T).filter fun s => ∃ p ∈ Γ, IsHop (zig M) T p s
  have hΔ : Δ ⊆ FV ∪ HR ∪ HΓ := by
    intro s hs
    obtain ⟨hsT, f, n, hf, hfΓ, hn, hfn⟩ := mem_filter.mp hs
    by_contra hnot
    simp only [mem_union, not_or] at hnot
    obtain ⟨⟨hFV, hHR⟩, hHΓ⟩ := hnot
    have hprev : ∃ t < s, zig M t = zig M s := by
      by_contra h'
      push Not at h'
      exact hFV (mem_filter.mpr ⟨hsT, h'⟩)
    obtain ⟨p, hp⟩ := exists_prev_hop hMo (mem_range.mp hsT) hprev
    have hpΓ : p ∉ Γ := fun h' => hHΓ (mem_filter.mpr ⟨hsT, p, h', hp⟩)
    have hRs : (Fin.last k, zig M s) ∉ R := fun h' => hHR (mem_filter.mpr ⟨hsT, hprev, h'⟩)
    -- extend the path by the hop edge `s → p` of the zigzag
    set f' : ℕ → ℕ := fun i => if i ≤ n then f i else p
    have hf'n : f' n = s := by simp [f', hfn]
    have hf'n1 : f' (n + 1) = p := by simp [f']
    have hpair : (p, s) ∈ hopPairs (allHops xs' T) := by
      refine mem_image.mpr ⟨(Fin.last k, p, s), mem_allHops.mpr ?_, rfl⟩
      simp only [show xs' (Fin.last k) = zig M from withZig_last xs M]
      exact hp
    have hpath : IsDagPath xs' T f' (n + 1) := by
      intro i hi
      by_cases hin : i < n
      · have h1 : f' i = f i := by simp [f', show i ≤ n by omega]
        have h2 : f' (i + 1) = f (i + 1) := by simp [f', show i + 1 ≤ n by omega]
        rw [h1, h2]
        exact hf i hin
      · have hi' : i = n := by omega
        subst hi'
        right
        rw [hf'n1, hf'n]
        exact hpair
    have havoid : ∀ i, 1 ≤ i → i ≤ n + 1 → f' i ∉ Γ := by
      intro i hi1 hi2
      by_cases hin : i ≤ n
      · have h1 : f' i = f i := by simp [f', hin]
        rw [h1]; exact hfΓ i hi1 hin
      · have hi' : i = n + 1 := by omega
        rw [hi', hf'n1]; exact hpΓ
    have hcert' := hcert f' (n + 1) hpath havoid (n + 1) (by omega) le_rfl
      (by rw [Nat.add_sub_cancel, hf'n1, hf'n]; exact hpair) (Fin.last k)
      (by rw [Nat.add_sub_cancel, hf'n1, hf'n, show xs' (Fin.last k) = zig M from withZig_last xs M]
          exact hp)
    rw [hf'n1, show xs' (Fin.last k) = zig M from withZig_last xs M,
      show zig M p = zig M s from hp.2.2.1.symm] at hcert'
    exact hRs hcert'
  -- the counts
  have hFV : (FV.card : ℝ) ≤ T / M + 2 := by
    have h1 := card_firstVisits_le M T
    have h2 : (((T - 1) / M : ℕ) : ℝ) ≤ T / M := by
      calc (((T - 1) / M : ℕ) : ℝ) ≤ ((T - 1 : ℕ) : ℝ) / M := Nat.cast_div_le
        _ ≤ T / M := by
            apply div_le_div_of_nonneg_right _ (by positivity)
            exact_mod_cast Nat.sub_le T 1
    have h3 : (FV.card : ℝ) ≤ (((T - 1) / M : ℕ) : ℝ) + 2 := by exact_mod_cast h1
    linarith
  have hHR : (HR.card : ℝ) ≤ 2 * M * R.card := by
    have h1 : HR ⊆ R.biUnion fun r => (range T).filter fun s => zig M s = r.2 := by
      intro s hs
      obtain ⟨hsT, -, hsR⟩ := mem_filter.mp hs
      exact mem_biUnion.mpr ⟨_, hsR, mem_filter.mpr ⟨hsT, rfl⟩⟩
    have h2 : HR.card ≤ 2 * M * R.card := by
      calc HR.card ≤ (R.biUnion fun r => (range T).filter fun s => zig M s = r.2).card :=
            card_le_card h1
        _ ≤ ∑ r ∈ R, ((range T).filter fun s => zig M s = r.2).card := card_biUnion_le
        _ ≤ ∑ _r ∈ R, 2 * M := sum_le_sum fun r _ => card_zig_visits_le hM0 T r.2
        _ = 2 * M * R.card := by rw [sum_const, smul_eq_mul, mul_comm]
    exact_mod_cast h2
  have hHΓ : HΓ.card ≤ Γ.card := by
    refine card_le_card_of_injOn (fun s => if h : ∃ p ∈ Γ, IsHop (zig M) T p s then
      Classical.choose h else 0) (fun s hs => ?_) (fun s hs s' hs' he => ?_)
    · have h := (mem_filter.mp (Finset.mem_coe.mp hs)).2
      simp only [h, ↓reduceDIte]
      exact Finset.mem_coe.mpr (Classical.choose_spec h).1
    · have h := (mem_filter.mp (Finset.mem_coe.mp hs)).2
      have h' := (mem_filter.mp (Finset.mem_coe.mp hs')).2
      simp only [h, h', ↓reduceDIte] at he
      have e1 := (Classical.choose_spec h).2
      have e2 := (Classical.choose_spec h').2
      rw [he] at e1
      exact hop_start_unique e1 e2
  -- the genie
  refine ⟨Γ ∪ Δ, union_subset hΓT (filter_subset _ _), ?_, fun f n hf hfΓ => ?_⟩
  · have h1 := card_union_le Γ Δ
    have h2 := card_le_card hΔ
    have h3 := card_union_le (FV ∪ HR) HΓ
    have h4 := card_union_le FV HR
    have hsum : ((Γ ∪ Δ).card : ℝ) ≤ Γ.card + (FV.card + HR.card + HΓ.card) := by
      exact_mod_cast (h1.trans (Nat.add_le_add_left (h2.trans (h3.trans
        (Nat.add_le_add_right h4 _))) _))
    have hHΓ' : (HΓ.card : ℝ) ≤ Γ.card := by exact_mod_cast hHΓ
    have hTM : (T : ℝ) / M ≤ ε' * T / 4 := by
      have hMpos : (0 : ℝ) < M := by exact_mod_cast hM0
      rw [div_le_div_iff₀ hMpos (by norm_num)]
      have := mul_le_mul_of_nonneg_left hMge (show (0 : ℝ) ≤ ε' * T by positivity)
      rw [show ε' * T * (4 / ε') = 4 * T by field_simp] at this
      linarith
    have hR' : 2 * (M : ℝ) * R.card ≤ ε' * T / 8 := by
      calc 2 * (M : ℝ) * R.card ≤ 2 * M * (δ ε * T) :=
            mul_le_mul_of_nonneg_left hR (by positivity)
        _ = (2 * M * δ ε) * T := by ring
        _ ≤ ε' / 8 * T := mul_le_mul_of_nonneg_right hε2 (by positivity)
        _ = ε' * T / 8 := by ring
    have hΓ' : (Γ.card : ℝ) ≤ ε' * T / 8 := by
      calc (Γ.card : ℝ) ≤ ε * T := hΓ
        _ ≤ ε' / 8 * T := mul_le_mul_of_nonneg_right hε1 (by positivity)
        _ = ε' * T / 8 := by ring
    have h2' : (2 : ℝ) ≤ ε' * T / 8 := by
      have := mul_le_mul_of_nonneg_left hT hε'.le
      rw [show ε' * (16 / ε') = 16 by field_simp] at this
      linarith
    linarith
  · -- long paths of `xs` that avoid the genie would end in `Δ`
    by_contra hlong
    push Not at hlong
    have hn : D ε < n := lt_of_le_of_lt (le_max_left _ _) hlong
    have hn1 : 1 ≤ n := by omega
    have hfnT : f n < T := by
      have := hf.lt (i := n - 1) (by omega)
      rw [Nat.sub_add_cancel hn1] at this
      omega
    have hmem : f n ∈ Δ := mem_filter.mpr ⟨mem_range.mpr hfnT, f, n, hf.mono,
      fun i hi1 hi2 h' => hfΓ i hi1 hi2 (mem_union_left _ h'), hn, rfl⟩
    exact hfΓ n hn1 le_rfl (mem_union_right _ hmem)

end BoundedNesting
