import BoundedNesting.Labels

/-!
# The family clock

The counting core of Theorem F, stated for abstract family data. There are `N` virtual heads and
a finite set of families; a family `F` has a virtual head `vh F`, a span `[P F, U F]`, an owner
`o F` and a height `d F`, and every hop `η = (F, p, u)` of `H` lies in the span of its family with
the owner strictly inside (`Fam.Valid`). Families of one virtual head have disjoint spans.

For integers `a, K ≥ 1`, an offset `r < a` and `ω : Fin N → [0, K)`, the family clock
(`Fam.clock`) is a lexicographic tuple of `N` digits in `[0, K)`. Its cut consists of the violated
hops (`clock u ≤ clock p`) and the descents (`clock t < clock (t - 1)`).

The cost of the cut is bounded in `ClockCost.lean` (`Fam.Valid.cost_sum_le`). Here:
* `Fam.Valid.overlap`, `Fam.Valid.sum_d_le`: the overlap bound and the area bound of the families;
* `Fam.clock_lt_of_no_wrap`, `Fam.clock_le_of_no_wrap`: if no digit wraps, the clock increases
  along a hop and does not decrease along a state edge;
* `Fam.depth_le_of_lex`: along a path on which a lexicographic label with `N` digits in `[0, K)`
  never increases, and decreases strictly at the marked steps, at most `K^N - 1` steps are marked.
-/

namespace BoundedNesting

open Finset

/-- `⌊log₂ d⌋`, the band of a height `d`. -/
abbrev lam (d : ℕ) : ℕ := Nat.log 2 d

/-- Abstract family data: virtual heads, spans `[P, U]`, owners `o`, heights `d`, and hops
`(F, p, u)`. -/
structure Fam (ι : Type*) (N : ℕ) where
  vh : ι → Fin N
  P : ι → ℕ
  U : ι → ℕ
  o : ι → ℕ
  d : ι → ℕ
  H : Finset (ι × ℕ × ℕ)

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

/-- The hypotheses on family data, for times in `[0, T)`. -/
structure Fam.Valid (A : Fam ι N) (T : ℕ) : Prop where
  hop_in : ∀ η ∈ A.H, A.P η.1 ≤ η.2.1 ∧ η.2.1 < A.o η.1 ∧ A.o η.1 < η.2.2 ∧ η.2.2 ≤ A.U η.1
  span_end : ∀ η ∈ A.H, η.2.2 = A.U η.1 → η.2.1 = A.P η.1
  disj : ∀ F F', F ≠ F' → A.vh F = A.vh F' → A.U F ≤ A.P F' ∨ A.U F' ≤ A.P F
  card_le : ∀ F, (A.H.filter (fun η => η.1 = F)).card ≤ A.d F
  d_pos : ∀ F, 1 ≤ A.d F
  long : ∀ F, A.P F + 2 * A.d F ≤ A.U F
  lt_T : ∀ F, A.U F < T

/-- The group of a band, for the offset `r`. -/
def grp (a r b : ℕ) : ℕ := (b + r) / a

/-- The floor of a group. -/
def flr (a r g : ℕ) : ℕ := a * g - r

namespace Fam

variable (A : Fam ι N)

/-- The families of `v` that start at or before `t`. -/
def started (v : Fin N) (t : ℕ) : Finset ι := univ.filter (fun F => A.vh F = v ∧ A.P F ≤ t)

/-- The band of `v` at `t`: that of the family of `v` that started last, or `0`. -/
noncomputable def band (v : Fin N) (t : ℕ) : ℕ :=
  if h : (A.started v t).Nonempty then
    lam (A.d (Classical.choose ((A.started v t).exists_max_image A.P h)))
  else 0

/-- The group of `v` at `t`. -/
noncomputable def group (a r : ℕ) (v : Fin N) (t : ℕ) : ℕ := grp a r (A.band v t)

/-- The occupied groups at `t`. -/
noncomputable def occ (a r t : ℕ) : Finset ℕ := univ.image (fun v => A.group a r v t)

/-- The position of a group: the number of occupied groups above it. -/
noncomputable def rk (a r t g : ℕ) : ℕ := ((A.occ a r t).filter (fun g' => g < g')).card

/-- The count of a group: events up to `t` of scale at least its floor. -/
def cnt (a r t g : ℕ) : ℕ := (univ.filter (fun F => A.o F ≤ t ∧ flr a r g ≤ lam (A.d F))).card

/-- The digit at position `i`. -/
noncomputable def digit (a K r : ℕ) (ω : Fin N → ℕ) (t : ℕ) (i : Fin N) : ℕ :=
  ∑ g ∈ A.occ a r t, if A.rk a r t g = i.val then (A.cnt a r t g + ω i) % K else 0

/-- **The family clock.** -/
noncomputable def clock (a K r : ℕ) (ω : Fin N → ℕ) (t : ℕ) : Lex (Fin N → ℕ) :=
  toLex (A.digit a K r ω t)

open Classical in
/-- The violated hops. -/
noncomputable def violated (a K r : ℕ) (ω : Fin N → ℕ) : Finset (ι × ℕ × ℕ) :=
  A.H.filter (fun η => A.clock a K r ω η.2.2 ≤ A.clock a K r ω η.2.1)

open Classical in
/-- The descents. -/
noncomputable def descents (a K r : ℕ) (ω : Fin N → ℕ) (T : ℕ) : Finset ℕ :=
  (Ico 1 T).filter (fun t => A.clock a K r ω t < A.clock a K r ω (t - 1))

variable {A} {T : ℕ}

/-! ### Structure -/

omit [Fintype ι] in
theorem Valid.P_lt_U (hA : A.Valid T) (F : ι) : A.P F + 2 ≤ A.U F := by
  have := hA.long F; have := hA.d_pos F; omega

omit [Fintype ι] in
theorem Valid.P_ne (hA : A.Valid T) {F F' : ι} (hne : F ≠ F') (hv : A.vh F = A.vh F') :
    A.P F ≠ A.P F' := by
  intro he
  have h1 := hA.P_lt_U F; have h2 := hA.P_lt_U F'
  rcases hA.disj F F' hne hv with h | h <;> omega

omit [DecidableEq ι] in
theorem mem_started {v : Fin N} {t : ℕ} {F : ι} :
    F ∈ A.started v t ↔ A.vh F = v ∧ A.P F ≤ t := by
  simp [started]

/-- The band is that of the last family started. -/
theorem Valid.band_eq (hA : A.Valid T) {v : Fin N} {t : ℕ} {F : ι} (hF : F ∈ A.started v t)
    (hmax : ∀ F' ∈ A.started v t, A.P F' ≤ A.P F) : A.band v t = lam (A.d F) := by
  have hne : (A.started v t).Nonempty := ⟨F, hF⟩
  unfold band
  simp only [hne, ↓reduceDIte]
  obtain ⟨h1, h2⟩ := Classical.choose_spec ((A.started v t).exists_max_image A.P hne)
  set G := Classical.choose ((A.started v t).exists_max_image A.P hne)
  have hPG : A.P G = A.P F := le_antisymm (hmax G h1) (h2 F hF)
  by_contra hGF
  have hG : G ≠ F := fun h => hGF (by rw [h])
  exact hA.P_ne hG ((mem_started.mp h1).1.trans (mem_started.mp hF).1.symm) hPG

/-- Inside the span of a family, the band of its virtual head is its band. -/
theorem Valid.band_of_mem (hA : A.Valid T) {F : ι} {t : ℕ} (h1 : A.P F ≤ t) (h2 : t < A.U F) :
    A.band (A.vh F) t = lam (A.d F) := by
  refine hA.band_eq (mem_started.mpr ⟨rfl, h1⟩) fun F' hF' => ?_
  obtain ⟨hv, hP⟩ := mem_started.mp hF'
  by_cases hFF : F' = F
  · rw [hFF]
  · rcases hA.disj F' F hFF hv with h | h
    · have := hA.P_lt_U F'; omega
    · omega

/-- At the end of a span the band is unchanged unless a family of the same virtual head starts
there. -/
theorem Valid.band_at_end (hA : A.Valid T) {F : ι}
    (hno : ∀ F', F' ≠ F → A.vh F' = A.vh F → A.P F' ≠ A.U F) :
    A.band (A.vh F) (A.U F) = lam (A.d F) := by
  refine hA.band_eq (mem_started.mpr ⟨rfl, by have := hA.P_lt_U F; omega⟩) fun F' hF' => ?_
  obtain ⟨hv, hP⟩ := mem_started.mp hF'
  by_cases hFF : F' = F
  · rw [hFF]
  · have := hno F' hFF hv
    rcases hA.disj F' F hFF hv with h | h
    · have := hA.P_lt_U F'; omega
    · omega

omit [DecidableEq ι] in
/-- The band changes only where a family starts. -/
theorem band_eq_prev {v : Fin N} {t : ℕ} (ht : 1 ≤ t) (hno : ∀ F, A.vh F = v → A.P F ≠ t) :
    A.band v t = A.band v (t - 1) := by
  have : A.started v t = A.started v (t - 1) := by
    ext F
    simp only [mem_started]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by have := hno F h1; omega⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
  unfold band
  simp only [this]

/-- The spans of the families of one virtual head fit in `[1, T)`, so their heights sum to less
than `T / 2`. -/
theorem Valid.sum_d_le (hA : A.Valid T) (v : Fin N) :
    2 * ∑ F ∈ univ.filter (fun F => A.vh F = v), A.d F ≤ T - 1 := by
  classical
  have hdisj : ((univ.filter (fun F => A.vh F = v)) : Set ι).PairwiseDisjoint
      (fun F => Ioc (A.P F) (A.U F)) := by
    intro F hF F' hF' hne
    simp only [coe_filter, mem_univ, true_and] at hF hF'
    change A.vh F = v at hF
    change A.vh F' = v at hF'
    rw [Function.onFun, Finset.disjoint_left]
    intro t ht ht'
    simp only [mem_Ioc] at ht ht'
    rcases hA.disj F F' hne (hF.trans hF'.symm) with h | h <;> omega
  have hsub : (univ.filter (fun F => A.vh F = v)).biUnion (fun F => Ioc (A.P F) (A.U F)) ⊆
      Ioc 0 (T - 1) := by
    intro t ht
    obtain ⟨F, -, hF⟩ := mem_biUnion.mp ht
    simp only [mem_Ioc] at hF ⊢
    have := hA.lt_T F
    omega
  have hcard := card_le_card hsub
  rw [card_biUnion hdisj, Nat.card_Ioc] at hcard
  rw [mul_sum]
  calc ∑ F ∈ univ.filter (fun F => A.vh F = v), 2 * A.d F
      ≤ ∑ F ∈ univ.filter (fun F => A.vh F = v), (Ioc (A.P F) (A.U F)).card := by
        refine sum_le_sum fun F _ => ?_
        rw [Nat.card_Ioc]; have := hA.long F; omega
    _ ≤ T - 1 - 0 := hcard
    _ = T - 1 := by omega

/-- All heights together: `2 ∑ d ≤ N T`. -/
theorem Valid.sum_d_all (hA : A.Valid T) : 2 * ∑ F, A.d F ≤ N * T := by
  classical
  rw [← sum_fiberwise univ A.vh A.d, mul_sum]
  calc ∑ v, 2 * ∑ F ∈ univ.filter (fun F => A.vh F = v), A.d F ≤ ∑ _v : Fin N, T :=
        sum_le_sum fun v _ => (hA.sum_d_le v).trans (Nat.sub_le T 1)
    _ = N * T := by simp

omit [Fintype ι] in
/-- At every time at most one family of a virtual head has the time in its half-open span. -/
theorem Valid.unique_span (hA : A.Valid T) {F F' : ι} (hne : F ≠ F') (hv : A.vh F = A.vh F')
    {τ : ℕ} (h : A.P F < τ ∧ τ ≤ A.U F) : ¬ (A.P F' < τ ∧ τ ≤ A.U F') := by
  rintro ⟨h1, h2⟩
  have := hA.P_lt_U F
  have := hA.P_lt_U F'
  rcases hA.disj F F' hne hv with h' | h' <;> omega

omit [Fintype ι] in
/-- **Overlap.** At most `N (2^θ - 1)` hops spanning `τ` lie in families of band less than `θ`. -/
theorem Valid.overlap (hA : A.Valid T) (τ θ : ℕ) :
    (A.H.filter (fun η => η.2.1 < τ ∧ τ ≤ η.2.2 ∧ lam (A.d η.1) < θ)).card ≤ N * (2 ^ θ - 1) := by
  classical
  set S := A.H.filter (fun η => η.2.1 < τ ∧ τ ≤ η.2.2 ∧ lam (A.d η.1) < θ)
  rw [card_eq_sum_card_fiberwise (f := fun η => A.vh η.1) (t := univ) (fun _ _ => mem_univ _)]
  calc ∑ v, (S.filter (fun η => A.vh η.1 = v)).card ≤ ∑ _v : Fin N, (2 ^ θ - 1) := by
        refine sum_le_sum fun v _ => ?_
        rcases (S.filter (fun η => A.vh η.1 = v)).eq_empty_or_nonempty with he | ⟨η₀, hη₀⟩
        · rw [he]; simp
        · obtain ⟨hη₀S, hv₀⟩ := mem_filter.mp hη₀
          obtain ⟨hη₀H, hp₀, hu₀, hl₀⟩ := mem_filter.mp hη₀S
          have hin₀ := hA.hop_in η₀ hη₀H
          -- every hop of the fibre lies in the family of `η₀`
          have hsub : S.filter (fun η => A.vh η.1 = v) ⊆ A.H.filter (fun η => η.1 = η₀.1) := by
            intro η hη
            obtain ⟨hηS, hv⟩ := mem_filter.mp hη
            obtain ⟨hηH, hp, hu, -⟩ := mem_filter.mp hηS
            have hin := hA.hop_in η hηH
            refine mem_filter.mpr ⟨hηH, ?_⟩
            by_contra hne
            rcases hA.disj η.1 η₀.1 hne (hv.trans hv₀.symm) with h | h <;> omega
          have hd : A.d η₀.1 < 2 ^ θ := by
            calc A.d η₀.1 < 2 ^ (lam (A.d η₀.1) + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
              _ ≤ 2 ^ θ := Nat.pow_le_pow_right (by norm_num) (by omega)
          have := (card_le_card hsub).trans (hA.card_le η₀.1)
          omega
    _ = N * (2 ^ θ - 1) := by simp

/-! ### Counting tools -/

/-- At most `n' - n` offsets `c < K` separate `n + c` and `n' + c` into different blocks of `K`. -/
theorem card_wrap_le {K n n' : ℕ} (hK : 0 < K) (hn : n ≤ n') :
    ((range K).filter (fun c => (n + c) / K ≠ (n' + c) / K)).card ≤ n' - n := by
  by_cases hδ : K ≤ n' - n
  · exact (card_filter_le _ _).trans (by rw [card_range]; exact hδ)
  push Not at hδ
  set S := (range K).filter (fun c => (n + c) / K ≠ (n' + c) / K)
  have hinj : Set.InjOn (fun c => (n + c) % K) S := by
    intro c hc c' hc' h
    have hc1 := mem_range.mp (mem_filter.mp hc).1
    have hc1' := mem_range.mp (mem_filter.mp hc').1
    have hmod : c ≡ c' [MOD K] := Nat.ModEq.add_left_cancel' n h
    rwa [Nat.ModEq, Nat.mod_eq_of_lt hc1, Nat.mod_eq_of_lt hc1'] at hmod
  have himg : S.image (fun c => (n + c) % K) ⊆ Ico (K - (n' - n)) K := by
    intro x hx
    obtain ⟨c, hc, rfl⟩ := mem_image.mp hx
    have hne := (mem_filter.mp hc).2
    refine mem_Ico.mpr ⟨?_, Nat.mod_lt _ hK⟩
    by_contra hlt
    apply hne
    have h1 := Nat.div_add_mod (n + c) K
    have h2 : n' + c = (n + c) % K + (n' - n) + K * ((n + c) / K) := by omega
    have h3 : (n' + c) / K = (n + c) / K := by
      rw [h2, Nat.add_mul_div_left _ _ hK,
        Nat.div_eq_of_lt (show (n + c) % K + (n' - n) < K by omega), zero_add]
    exact h3.symm
  calc S.card = (S.image (fun c => (n + c) % K)).card := (card_image_of_injOn hinj).symm
    _ ≤ (Ico (K - (n' - n)) K).card := card_le_card himg
    _ = n' - n := by rw [Nat.card_Ico]; omega

/-- Without a wrap, the residue grows by the difference. -/
theorem mod_of_no_wrap {K n n' c : ℕ} (hn : n ≤ n') (h : (n + c) / K = (n' + c) / K) :
    (n' + c) % K = (n + c) % K + (n' - n) := by
  have h1 := Nat.div_add_mod (n + c) K
  have h2 := Nat.div_add_mod (n' + c) K
  rw [← h] at h2
  omega

/-- Choices of `ω : Fin N → [0, K)` with a condition on one coordinate. -/
theorem card_piFinset_coord {K : ℕ} (i : Fin N) (q : ℕ → Prop) [DecidablePred q] :
    ((Fintype.piFinset (fun _ : Fin N => range K)).filter (fun ω => q (ω i))).card =
      ((range K).filter q).card * K ^ (N - 1) := by
  classical
  have : (Fintype.piFinset (fun _ : Fin N => range K)).filter (fun ω => q (ω i)) =
      Fintype.piFinset (fun j => if j = i then (range K).filter q else range K) := by
    ext ω
    simp only [mem_filter, Fintype.mem_piFinset]
    constructor
    · rintro ⟨h1, h2⟩ j
      by_cases hj : j = i
      · subst hj; simp [h1 j, h2]
      · simp [hj, h1 j]
    · intro h
      refine ⟨fun j => ?_, ?_⟩
      · by_cases hj : j = i
        · have := h j; simp only [hj, ↓reduceIte, mem_filter] at this; subst hj; exact this.1
        · have := h j; simpa [hj] using this
      · have := h i; simp only [↓reduceIte, mem_filter] at this; exact this.2
  rw [this, Fintype.card_piFinset]
  simp only [apply_ite Finset.card]
  rw [Finset.prod_ite, prod_const, prod_const]
  have h1 : (univ.filter (fun j : Fin N => j = i)).card = 1 := by
    rw [filter_eq' univ i]; simp
  have h2 : (univ.filter (fun j : Fin N => ¬ j = i)).card = N - 1 := by
    rw [filter_ne' univ i, card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin]
  rw [h1, h2, pow_one, card_range]

theorem card_piFinset_range (K : ℕ) :
    (Fintype.piFinset (fun _ : Fin N => range K)).card = K ^ N := by
  rw [Fintype.card_piFinset, prod_const, card_range, card_univ, Fintype.card_fin]

theorem sum_pow_two_lt (n : ℕ) : ∑ i ∈ range n, 2 ^ i < 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, pow_succ]; omega

/-! ### Lexicographic comparison -/

/-- If `x ≤ y` up to position `j` and `x j < y j`, then `x < y` lexicographically. -/
theorem lex_lt_of_le_of_lt {x y : Fin N → ℕ} (j : Fin N) (hle : ∀ i, i ≤ j → x i ≤ y i)
    (hlt : x j < y j) : toLex x < toLex y := by
  classical
  have hne : (univ.filter (fun i : Fin N => i ≤ j ∧ x i ≠ y i)).Nonempty :=
    ⟨j, mem_filter.mpr ⟨mem_univ _, le_refl j, hlt.ne⟩⟩
  set i₀ := (univ.filter (fun i : Fin N => i ≤ j ∧ x i ≠ y i)).min' hne
  have hi₀ := mem_filter.mp ((univ.filter (fun i : Fin N => i ≤ j ∧ x i ≠ y i)).min'_mem hne)
  refine ⟨i₀, fun i hi => ?_, ?_⟩
  · by_contra hxy
    have : i₀ ≤ i := (univ.filter (fun i : Fin N => i ≤ j ∧ x i ≠ y i)).min'_le i
      (mem_filter.mpr ⟨mem_univ _, (le_of_lt hi).trans hi₀.2.1, hxy⟩)
    exact absurd hi (not_lt.mpr this)
  · exact lt_of_le_of_ne (hle i₀ hi₀.2.1) hi₀.2.2

theorem lex_le_of_le {x y : Fin N → ℕ} (h : ∀ i, x i ≤ y i) : toLex x ≤ toLex y :=
  Pi.toLex_monotone h

/-- **Labels in a finite lexicographic range.** A path along which a label with `N` digits in
`[0, K)` never increases, and strictly decreases at the marked steps, has at most `K^N - 1` marked
steps. -/
theorem depth_le_of_lex {α : Type*} {K : ℕ} (Ψ : α → Fin N → ℕ) (hΨ : ∀ a i, Ψ a i < K)
    (f : ℕ → α) (n : ℕ) (marked : ℕ → Prop) [DecidablePred marked]
    (hmono : ∀ i < n, toLex (Ψ (f (i + 1))) ≤ toLex (Ψ (f i)))
    (hstrict : ∀ i < n, marked i → toLex (Ψ (f (i + 1))) < toLex (Ψ (f i))) :
    ((range n).filter marked).card ≤ K ^ N - 1 := by
  classical
  set S := Fintype.piFinset (fun _ : Fin N => range K)
  let rank : α → ℕ := fun a => (S.filter (fun y => toLex y < toLex (Ψ a))).card
  have hmem : ∀ a, Ψ a ∈ S := fun a => Fintype.mem_piFinset.mpr fun i => mem_range.mpr (hΨ a i)
  have hrank : ∀ a, rank a < K ^ N := by
    intro a
    rw [← card_piFinset_range K]
    refine card_lt_card ⟨filter_subset _ _, fun h => ?_⟩
    have := mem_filter.mp (h (hmem a))
    exact lt_irrefl _ this.2
  refine depth_le_of_label rank hrank f n marked (fun i hi => ?_) (fun i hi hm => ?_)
  · exact card_le_card fun y hy => by
      obtain ⟨h1, h2⟩ := mem_filter.mp hy
      exact mem_filter.mpr ⟨h1, lt_of_lt_of_le h2 (hmono i hi)⟩
  · refine card_lt_card ⟨fun y hy => ?_, fun h => ?_⟩
    · obtain ⟨h1, h2⟩ := mem_filter.mp hy
      exact mem_filter.mpr ⟨h1, lt_trans h2 (hstrict i hi hm)⟩
    · have := mem_filter.mp (h (mem_filter.mpr ⟨hmem (f (i + 1)), hstrict i hi hm⟩))
      exact lt_irrefl _ this.2

/-! ### Ranks and the comparison of clocks -/

section Compare

variable (A : Fam ι N) (a K r : ℕ) (ω : Fin N → ℕ)

omit [DecidableEq ι] in
theorem card_occ_le (t : ℕ) : (A.occ a r t).card ≤ N := by
  unfold occ
  exact card_image_le.trans (by simp)

omit [DecidableEq ι] in
theorem rk_lt_card {t g : ℕ} (hg : g ∈ A.occ a r t) : A.rk a r t g < (A.occ a r t).card := by
  unfold rk
  exact card_lt_card ⟨filter_subset _ _, fun h => lt_irrefl g (mem_filter.mp (h hg)).2⟩

omit [DecidableEq ι] in
theorem rk_lt_N {t g : ℕ} (hg : g ∈ A.occ a r t) : A.rk a r t g < N :=
  lt_of_lt_of_le (A.rk_lt_card a r hg) (A.card_occ_le a r t)

omit [DecidableEq ι] in
theorem rk_strict {t g g' : ℕ} (hg' : g' ∈ A.occ a r t) (h : g < g') :
    A.rk a r t g' < A.rk a r t g := by
  unfold rk
  refine card_lt_card ⟨fun x hx => ?_, fun hsub => ?_⟩
  · obtain ⟨h1, h2⟩ := mem_filter.mp hx; exact mem_filter.mpr ⟨h1, lt_trans h h2⟩
  · exact lt_irrefl g' (mem_filter.mp (hsub (mem_filter.mpr ⟨hg', h⟩))).2

omit [DecidableEq ι] in
theorem rk_inj {t g g' : ℕ} (hg : g ∈ A.occ a r t) (hg' : g' ∈ A.occ a r t)
    (h : A.rk a r t g = A.rk a r t g') : g = g' := by
  rcases lt_trichotomy g g' with hlt | heq | hgt
  · have := A.rk_strict a r hg' hlt; omega
  · exact heq
  · have := A.rk_strict a r hg hgt; omega

omit [DecidableEq ι] in
theorem cnt_mono {t t' : ℕ} (h : t ≤ t') (g : ℕ) : A.cnt a r t g ≤ A.cnt a r t' g := by
  unfold cnt
  exact card_le_card fun F hF => by
    obtain ⟨h1, h2, h3⟩ := mem_filter.mp hF
    exact mem_filter.mpr ⟨h1, le_trans h2 h, h3⟩

omit [DecidableEq ι] in
theorem digit_eq_filter (t : ℕ) (i : Fin N) :
    A.digit a K r ω t i = ∑ g ∈ (A.occ a r t).filter (fun g => A.rk a r t g = i.val),
      (A.cnt a r t g + ω i) % K := by
  unfold digit
  rw [sum_filter]

omit [DecidableEq ι] in
/-- **Hops.** If the occupied groups above `g₀` are the same at `p` and `u`, the count of `g₀`
grows, and no digit at or above `g₀` wraps, then the clock increases from `p` to `u`. -/
theorem clock_lt_of_no_wrap {p u g₀ : ℕ} (hpu : p ≤ u) (hp : g₀ ∈ A.occ a r p)
    (hu : g₀ ∈ A.occ a r u)
    (habove : (A.occ a r p).filter (fun g => g₀ < g) = (A.occ a r u).filter (fun g => g₀ < g))
    (hΔ : A.cnt a r p g₀ < A.cnt a r u g₀)
    (hwrap : ∀ g ∈ A.occ a r p, g₀ ≤ g → ∀ i : Fin N, i.val = A.rk a r p g →
      (A.cnt a r p g + ω i) / K = (A.cnt a r u g + ω i) / K) :
    A.clock a K r ω p < A.clock a K r ω u := by
  classical
  -- groups at or above `g₀` are occupied at `p` iff at `u`, with the same positions
  have hmem : ∀ g, g₀ ≤ g → (g ∈ A.occ a r p ↔ g ∈ A.occ a r u) := by
    intro g hg
    rcases eq_or_lt_of_le hg with rfl | hlt
    · exact ⟨fun _ => hu, fun _ => hp⟩
    · constructor
      · intro h
        have : g ∈ (A.occ a r p).filter (fun g => g₀ < g) := mem_filter.mpr ⟨h, hlt⟩
        rw [habove] at this; exact (mem_filter.mp this).1
      · intro h
        have : g ∈ (A.occ a r u).filter (fun g => g₀ < g) := mem_filter.mpr ⟨h, hlt⟩
        rw [← habove] at this; exact (mem_filter.mp this).1
  have hrk : ∀ g, g₀ ≤ g → A.rk a r p g = A.rk a r u g := by
    intro g hg
    unfold rk
    congr 1
    ext g'
    simp only [mem_filter]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨(hmem g' (by omega)).mp h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨(hmem g' (by omega)).mpr h1, h2⟩
  set j : Fin N := ⟨A.rk a r p g₀, A.rk_lt_N a r hp⟩
  -- positions up to `j` belong to groups at or above `g₀`
  have hge : ∀ (t : ℕ) (g : ℕ), g ∈ A.occ a r t → (t = p ∨ t = u) →
      A.rk a r t g ≤ A.rk a r p g₀ → g₀ ≤ g := by
    intro t g hg ht hle
    by_contra hlt
    push Not at hlt
    rcases ht with rfl | rfl
    · have := A.rk_strict a r hp hlt; omega
    · have := A.rk_strict a r hu hlt; rw [← hrk g₀ le_rfl] at this; omega
  have hset : ∀ i : Fin N, i ≤ j → (A.occ a r p).filter (fun g => A.rk a r p g = i.val) =
      (A.occ a r u).filter (fun g => A.rk a r u g = i.val) := by
    intro i hi
    have hi' : i.val ≤ A.rk a r p g₀ := hi
    ext g
    simp only [mem_filter]
    constructor
    · rintro ⟨h1, h2⟩
      have hg := hge p g h1 (Or.inl rfl) (by omega)
      exact ⟨(hmem g hg).mp h1, by rw [← hrk g hg]; exact h2⟩
    · rintro ⟨h1, h2⟩
      have hg := hge u g h1 (Or.inr rfl) (by omega)
      exact ⟨(hmem g hg).mpr h1, by rw [hrk g hg]; exact h2⟩
  have hterm : ∀ g ∈ A.occ a r p, g₀ ≤ g → ∀ i : Fin N, i.val = A.rk a r p g →
      (A.cnt a r u g + ω i) % K = (A.cnt a r p g + ω i) % K + (A.cnt a r u g - A.cnt a r p g) :=
    fun g hg hg0 i hi => mod_of_no_wrap (A.cnt_mono a r hpu g) (hwrap g hg hg0 i hi)
  apply lex_lt_of_le_of_lt j
  · intro i hi
    show A.digit a K r ω p i ≤ A.digit a K r ω u i
    rw [A.digit_eq_filter, A.digit_eq_filter, ← hset i hi]
    refine sum_le_sum fun g hg => ?_
    obtain ⟨h1, h2⟩ := mem_filter.mp hg
    have hg0 := hge p g h1 (Or.inl rfl) (by have : i.val ≤ A.rk a r p g₀ := hi; omega)
    rw [hterm g h1 hg0 i h2.symm]
    omega
  · show A.digit a K r ω p j < A.digit a K r ω u j
    rw [A.digit_eq_filter, A.digit_eq_filter, ← hset j le_rfl]
    have hsingle : (A.occ a r p).filter (fun g => A.rk a r p g = j.val) = {g₀} := by
      ext g
      simp only [mem_filter, mem_singleton]
      constructor
      · rintro ⟨h1, h2⟩; exact A.rk_inj a r h1 hp h2
      · rintro rfl; exact ⟨hp, rfl⟩
    rw [hsingle, sum_singleton, sum_singleton, hterm g₀ hp le_rfl j rfl]
    omega

omit [DecidableEq ι] in
/-- **States.** If the occupied groups do not change and no digit wraps, the clock does not
decrease. -/
theorem clock_le_of_no_wrap {t t' : ℕ} (htt : t ≤ t') (hocc : A.occ a r t = A.occ a r t')
    (hwrap : ∀ g ∈ A.occ a r t, ∀ i : Fin N, i.val = A.rk a r t g →
      (A.cnt a r t g + ω i) / K = (A.cnt a r t' g + ω i) / K) :
    A.clock a K r ω t ≤ A.clock a K r ω t' := by
  have hrk : ∀ g, A.rk a r t g = A.rk a r t' g := by intro g; unfold rk; rw [hocc]
  apply lex_le_of_le
  intro i
  show A.digit a K r ω t i ≤ A.digit a K r ω t' i
  rw [A.digit_eq_filter, A.digit_eq_filter]
  have hs : (A.occ a r t).filter (fun g => A.rk a r t g = i.val) =
      (A.occ a r t').filter (fun g => A.rk a r t' g = i.val) := by
    rw [hocc]; simp only [hrk]
  rw [← hs]
  refine sum_le_sum fun g hg => ?_
  obtain ⟨h1, h2⟩ := mem_filter.mp hg
  rw [mod_of_no_wrap (A.cnt_mono a r htt g) (hwrap g h1 i h2.symm)]
  omega

end Compare

end Fam

end BoundedNesting
