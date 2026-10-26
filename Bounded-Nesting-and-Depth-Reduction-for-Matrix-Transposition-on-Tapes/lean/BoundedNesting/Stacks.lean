import BoundedNesting.OwnerLoad

/-!
# TCP is depth reduction for stack DAGs

An `s`-stack DAG on `[0, N)` (`StackDag`) has the spine edges `t → t - 1` and arcs `u → p` with
`u - p ≥ 2`, partitioned into `s` families; within a family no two arcs cross, and every vertex is
the left endpoint of at most one arc and the right endpoint of at most one arc. A cut is a set of
spine edges (given by their upper ends) and arcs, and a path that avoids it (`AvoidPath`) carries
`arcCount` arcs. `SRat s ε D` says that every `s`-stack DAG on `[0, N)` has a cut of at most `εN`
edges and depth at most `D`. `TCPat k ε D` says the same for walk DAGs of `k` walks, with pauses,
and `TCPnpAt k ε D` for walks without pauses.

* (a) `walkDag_isStack`: the walk DAG of `k` walks, pauses allowed, is a `2k`-stack DAG. The
  families are head and side; a pair that is a long hop of several heads is kept once.
* (b) `StackDag.walk_upperHop`, `StackDag.walk_hop`, `StackDag.walk_noPause`,
  `StackDag.pullback_cut`: an `s`-stack DAG is realized by `s`
  walks of length `2N` without pauses. Arc `(p, u)` of family `i` is the upper long hop
  `(2p, 2u)` of walk `i`, and a cut of their walk DAG pulls back to a cut of the stack DAG of no
  larger size and depth.
* `srAt_of_tcpnpAt`: TCP for `k` walks without pauses at `ε/2` gives `SR(k)` at `ε` with the same
  depth. `tcpAt_of_srAt`: `SR(2k)` gives TCP for `k` walks with pauses.
-/

namespace BoundedNesting

open Finset

/-! ### Paths that avoid a cut -/

/-- A path `f 0 → f 1 → ⋯ → f n` of the DAG on `[0, N)` with spine edges `t → t - 1` and arcs
`u → p` for `(p, u) ∈ E` that avoids the spine edges at `cutS` and the arcs `cutA`. -/
def AvoidPath (N : ℕ) (E cutA : Finset (ℕ × ℕ)) (cutS : Finset ℕ) (f : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ i < n, (f (i + 1) + 1 = f i ∧ 1 ≤ f i ∧ f i < N ∧ f i ∉ cutS) ∨
    ((f (i + 1), f i) ∈ E ∧ (f (i + 1), f i) ∉ cutA)

/-- The number of arcs on a path. -/
def arcCount (E : Finset (ℕ × ℕ)) (f : ℕ → ℕ) (n : ℕ) : ℕ :=
  ((range n).filter fun i => (f (i + 1), f i) ∈ E).card

theorem arcCount_succ (E : Finset (ℕ × ℕ)) (f : ℕ → ℕ) (n : ℕ) :
    arcCount E f (n + 1) = (if (f 1, f 0) ∈ E then 1 else 0) + arcCount E (fun i => f (i + 1)) n := by
  unfold arcCount
  rw [card_filter, card_filter, sum_range_succ']
  simp only [zero_add]
  ring

/-- **Concatenation.** Two paths that meet concatenate, and their arc counts add. -/
theorem AvoidPath.append {N : ℕ} {E cutA : Finset (ℕ × ℕ)} {cutS : Finset ℕ} {f g : ℕ → ℕ}
    {n n' : ℕ} (hf : AvoidPath N E cutA cutS f n) (hg : AvoidPath N E cutA cutS g n')
    (hfg : f n = g 0) :
    AvoidPath N E cutA cutS (fun i => if i ≤ n then f i else g (i - n)) (n + n') ∧
      arcCount E (fun i => if i ≤ n then f i else g (i - n)) (n + n') =
        arcCount E f n + arcCount E g n' := by
  set h : ℕ → ℕ := fun i => if i ≤ n then f i else g (i - n)
  have hlo : ∀ i, i ≤ n → h i = f i := fun i hi => by simp [h, hi]
  have hhi : ∀ i, h (n + i) = g i := by
    intro i
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp [h, hfg]
    · simp only [h, show ¬ (n + i ≤ n) by omega, ↓reduceIte, Nat.add_sub_cancel_left]
  refine ⟨fun i hi => ?_, ?_⟩
  · by_cases hin : i < n
    · rw [hlo i hin.le, hlo (i + 1) hin]
      exact hf i hin
    · obtain ⟨j, rfl⟩ : ∃ j, i = n + j := ⟨i - n, by omega⟩
      rw [show n + j + 1 = n + (j + 1) by omega, hhi, hhi]
      exact hg j (by omega)
  · unfold arcCount
    rw [range_add, filter_union, card_union_of_disjoint]
    · congr 1
      · refine congrArg card (filter_congr fun i hi => ?_)
        rw [hlo i (by have := mem_range.mp hi; omega), hlo (i + 1) (by have := mem_range.mp hi; omega)]
      · rw [filter_map, card_map]
        refine congrArg card (filter_congr fun i _ => ?_)
        simp only [Function.comp_apply, addLeftEmbedding_apply]
        rw [show n + i + 1 = n + (i + 1) by omega, hhi, hhi]
    · exact disjoint_filter_filter (by
        rw [disjoint_left]
        intro x hx hx'
        obtain ⟨y, hy, rfl⟩ := mem_map.mp hx'
        simp only [mem_range, addLeftEmbedding_apply] at hx
        omega)

/-! ### Stack DAGs -/

/-- An `s`-stack DAG on `[0, N)`: arcs `(p, u)` with `u ≥ p + 2`, partitioned into `s` families,
non-crossing within a family, with at most one arc of each family at each endpoint. -/
structure StackDag (s N : ℕ) where
  arcs : Fin s → Finset (ℕ × ℕ)
  long : ∀ i, ∀ e ∈ arcs i, e.1 + 2 ≤ e.2 ∧ e.2 < N
  noCross : ∀ i, ∀ e ∈ arcs i, ∀ e' ∈ arcs i, ¬ (e.1 < e'.1 ∧ e'.1 < e.2 ∧ e.2 < e'.2)
  leftUnique : ∀ i, ∀ e ∈ arcs i, ∀ e' ∈ arcs i, e.1 = e'.1 → e = e'
  rightUnique : ∀ i, ∀ e ∈ arcs i, ∀ e' ∈ arcs i, e.2 = e'.2 → e = e'
  disj : ∀ i j, i ≠ j → Disjoint (arcs i) (arcs j)

/-- All arcs of a stack DAG. -/
def StackDag.arcSet {s N : ℕ} (H : StackDag s N) : Finset (ℕ × ℕ) := univ.biUnion H.arcs

/-- `SR(s)` at `ε` and `D`: every `s`-stack DAG on `[0, N)` has a cut of at most `εN` edges and depth
at most `D`. -/
def SRat (s : ℕ) (ε : ℝ) (D : ℕ) : Prop :=
  ∀ (N : ℕ) (H : StackDag s N), ∃ (cutS : Finset ℕ) (cutA : Finset (ℕ × ℕ)),
    cutS ⊆ Ico 1 N ∧ cutA ⊆ H.arcSet ∧ ((cutS.card + cutA.card : ℕ) : ℝ) ≤ ε * N ∧
    ∀ f n, AvoidPath N H.arcSet cutA cutS f n → arcCount H.arcSet f n ≤ D

/-- `SR(s)`. -/
def SR (s : ℕ) : Prop := ∀ ε : ℝ, 0 < ε → ∃ D, SRat s ε D

variable {k : ℕ}

/-- TCP for `k` walks with pauses, at `ε` and `D`: the walk DAG of every `k` walks of length `T` has a
cut of at most `εT` edges and depth at most `D`. -/
def TCPat (k : ℕ) (ε : ℝ) (D : ℕ) : Prop :=
  ∀ (T : ℕ) (xs : Fin k → ℕ → ℤ), (∀ h, IsWalk (xs h)) →
    ∃ (cutS : Finset ℕ) (cutH : Finset (ℕ × ℕ)), cutS ⊆ Ico 1 T ∧
      cutH ⊆ hopPairs (allHops xs T) ∧ ((cutS.card + cutH.card : ℕ) : ℝ) ≤ ε * T ∧
      ∀ f n, AvoidPath T (hopPairs (allHops xs T)) cutH cutS f n →
        arcCount (hopPairs (allHops xs T)) f n ≤ D

/-- TCP for `k` walks without pauses, at `ε` and `D`. -/
def TCPnpAt (k : ℕ) (ε : ℝ) (D : ℕ) : Prop :=
  ∀ (T : ℕ) (xs : Fin k → ℕ → ℤ), (∀ h, IsWalk (xs h)) →
    (∀ h t, t + 1 < T → xs h (t + 1) ≠ xs h t) →
    ∃ (cutS : Finset ℕ) (cutH : Finset (ℕ × ℕ)), cutS ⊆ Ico 1 T ∧
      cutH ⊆ hopPairs (allHops xs T) ∧ ((cutS.card + cutH.card : ℕ) : ℝ) ≤ ε * T ∧
      ∀ f n, AvoidPath T (hopPairs (allHops xs T)) cutH cutS f n →
        arcCount (hopPairs (allHops xs T)) f n ≤ D

/-- `TCP(k)` with pauses. -/
def TCP (k : ℕ) : Prop := ∀ ε : ℝ, 0 < ε → ∃ D, TCPat k ε D

/-- `TCP(k)` without pauses. -/
def TCPnp (k : ℕ) : Prop := ∀ ε : ℝ, 0 < ε → ∃ D, TCPnpAt k ε D

/-! ### (a) Walk DAGs are stack DAGs -/

/-- Two upper hops of one walk do not cross. -/
theorem upper_no_cross {y : ℕ → ℤ} {p u p' u' : ℕ} (h : IsUpperHop y p u) (h' : IsUpperHop y p' u') :
    ¬ (p < p' ∧ p' < u ∧ u < u') := by
  rintro ⟨h1, h2, h3⟩
  have a1 := h.above p' h1 h2
  have a2 := h'.above u (by omega) h3
  have := h.eq
  omega

/-- The head of a code `c < 2k`. -/
def codeHead (c : Fin (2 * k)) : Fin k := ⟨c.val / 2, by have := c.isLt; omega⟩

/-- The side of a code `c < 2k`: upper for odd codes. -/
def codeSide (c : Fin (2 * k)) : Bool := decide (c.val % 2 = 1)

/-- The hop pairs of the long hops of head `codeHead c` on side `codeSide c`. -/
def hopsOf (xs : Fin k → ℕ → ℤ) (T : ℕ) (c : Fin (2 * k)) : Finset (ℕ × ℕ) :=
  ((allHops xs T).filter fun η => η.1 = codeHead c ∧ side xs η = codeSide c).image
    fun η => (η.2.1, η.2.2)

/-- The code of a hop: `2h + 1` for upper hops of head `h`, `2h` for lower ones. -/
def hopCode (xs : Fin k → ℕ → ℤ) (η : Fin k × ℕ × ℕ) : Fin (2 * k) :=
  ⟨2 * η.1.val + (if side xs η then 1 else 0), by have := η.1.isLt; split_ifs <;> omega⟩

theorem mem_hopsOf_hopCode {xs : Fin k → ℕ → ℤ} {T : ℕ} {η : Fin k × ℕ × ℕ}
    (hη : η ∈ allHops xs T) : (η.2.1, η.2.2) ∈ hopsOf xs T (hopCode xs η) := by
  refine mem_image.mpr ⟨η, mem_filter.mpr ⟨hη, ?_, ?_⟩, rfl⟩
  · apply Fin.ext
    simp only [codeHead, hopCode]
    split_ifs <;> omega
  · simp only [codeSide, hopCode]
    rcases Bool.eq_false_or_eq_true (side xs η) with h | h
    · have h2 : (2 * (η.1 : ℕ) + 1) % 2 = 1 := by omega
      simp [h, h2]
    · have h2 : (2 * (η.1 : ℕ)) % 2 = 0 := by omega
      simp [h, h2]

/-- **(a)** The walk DAG of `k` walks, pauses allowed, is a `2k`-stack DAG. -/
theorem walkDag_isStack (xs : Fin k → ℕ → ℤ) (hx : ∀ h, IsWalk (xs h)) (T : ℕ) :
    ∃ H : StackDag (2 * k) T, H.arcSet = hopPairs (allHops xs T) := by
  classical
  -- a pair goes to the least code for which it is a long hop
  let arcs : Fin (2 * k) → Finset (ℕ × ℕ) := fun c =>
    (hopsOf xs T c).filter fun e => ∀ c' < c, e ∉ hopsOf xs T c'
  have hsub : ∀ c, ∀ e ∈ arcs c, ∃ η ∈ allHops xs T, η.1 = codeHead c ∧
      side xs η = codeSide c ∧ e = (η.2.1, η.2.2) := by
    intro c e he
    obtain ⟨η, hη, rfl⟩ := mem_image.mp (mem_filter.mp he).1
    obtain ⟨hη, h1, h2⟩ := mem_filter.mp hη
    exact ⟨η, hη, h1, h2, rfl⟩
  -- two hops of one code are upper hops of one walk seen from its side
  have hup : ∀ c, ∀ e ∈ arcs c, IsUpperHop (sw xs (codeHead c) (codeSide c)) e.1 e.2 ∧
      IsHop (xs (codeHead c)) T e.1 e.2 := by
    intro c e he
    obtain ⟨η, hη, h1, h2, rfl⟩ := hsub c e he
    have hh := mem_allHops.mp hη
    have := isUpperHop_sw hx hh
    rw [h2, h1] at this
    rw [h1] at hh
    exact ⟨this, hh⟩
  refine ⟨⟨arcs, fun c e he => ?_, fun c e he e' he' => ?_, fun c e he e' he' h => ?_,
    fun c e he e' he' h => ?_, fun c c' hne => ?_⟩, ?_⟩
  · have := (hup c e he).2
    exact ⟨this.1, this.2.1⟩
  · exact upper_no_cross (hup c e he).1 (hup c e' he').1
  · have h1 := (hup c e he).2
    have h2 := (hup c e' he').2
    rw [← h] at h2
    exact Prod.ext h (hop_start_unique h1 h2)
  · have h1 := (hup c e he).2
    have h2 := (hup c e' he').2
    rw [← h] at h2
    exact Prod.ext (hop_end_unique h1 h2) h
  · rw [disjoint_left]
    intro e he he'
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact (mem_filter.mp he').2 c hlt (mem_filter.mp he).1
    · exact (mem_filter.mp he).2 c' hlt (mem_filter.mp he').1
  · ext e
    simp only [StackDag.arcSet, mem_biUnion, mem_univ, true_and]
    constructor
    · rintro ⟨c, he⟩
      obtain ⟨η, hη, -, -, rfl⟩ := hsub c e he
      exact mem_image_of_mem _ hη
    · intro he
      obtain ⟨η, hη, rfl⟩ := mem_image.mp he
      have hne : (univ.filter fun c => (η.2.1, η.2.2) ∈ hopsOf xs T c).Nonempty :=
        ⟨hopCode xs η, mem_filter.mpr ⟨mem_univ _, mem_hopsOf_hopCode hη⟩⟩
      set c₀ := (univ.filter fun c => (η.2.1, η.2.2) ∈ hopsOf xs T c).min' hne
      refine ⟨c₀, mem_filter.mpr ⟨(mem_filter.mp (min'_mem _ hne)).2, fun c' hc' hmem => ?_⟩⟩
      have := Finset.min'_le (univ.filter fun c => (η.2.1, η.2.2) ∈ hopsOf xs T c) c'
        (mem_filter.mpr ⟨mem_univ _, hmem⟩)
      exact absurd hc' (not_lt.mpr this)

/-! ### (b) Stack DAGs are walk DAGs -/

namespace StackDag

variable {s N : ℕ} (H : StackDag s N)

/-- The nesting depth `d_i(t)`: the arcs of family `i` that contain `t` strictly inside. -/
def dep (i : Fin s) (t : ℕ) : ℕ := ((H.arcs i).filter fun e => e.1 < t ∧ t < e.2).card

/-- The walk of family `i`: `x(2t) = 2 d_i(t)` and `x(2t + 1) = min (x(2t)) (x(2t + 2)) + 1`. -/
def walk (i : Fin s) (τ : ℕ) : ℤ :=
  if τ % 2 = 0 then 2 * (H.dep i (τ / 2) : ℤ)
  else min (2 * (H.dep i (τ / 2) : ℤ)) (2 * (H.dep i (τ / 2 + 1) : ℤ)) + 1

theorem card_left_le (i : Fin s) (t : ℕ) : ((H.arcs i).filter fun e => e.1 = t).card ≤ 1 :=
  card_le_one.mpr fun e he e' he' =>
    H.leftUnique i e (mem_filter.mp he).1 e' (mem_filter.mp he').1
      ((mem_filter.mp he).2.trans (mem_filter.mp he').2.symm)

theorem card_right_le (i : Fin s) (t : ℕ) : ((H.arcs i).filter fun e => e.2 = t).card ≤ 1 :=
  card_le_one.mpr fun e he e' he' =>
    H.rightUnique i e (mem_filter.mp he).1 e' (mem_filter.mp he').1
      ((mem_filter.mp he).2.trans (mem_filter.mp he').2.symm)

/-- `d(t + 1) + #(arcs ending at t + 1) = d(t) + #(arcs starting at t)`. -/
theorem dep_succ (i : Fin s) (t : ℕ) :
    H.dep i (t + 1) + ((H.arcs i).filter fun e => e.2 = t + 1).card =
      H.dep i t + ((H.arcs i).filter fun e => e.1 = t).card := by
  unfold dep
  rw [← card_union_of_disjoint, ← card_union_of_disjoint]
  · congr 1
    ext e
    simp only [mem_union, mem_filter]
    constructor
    · rintro (⟨he, h1, h2⟩ | ⟨he, h⟩)
      · by_cases h : e.1 = t
        · exact Or.inr ⟨he, h⟩
        · exact Or.inl ⟨he, by omega, by omega⟩
      · have := H.long i e he; exact Or.inl ⟨he, by omega, by omega⟩
    · rintro (⟨he, h1, h2⟩ | ⟨he, h⟩)
      · by_cases h : e.2 = t + 1
        · exact Or.inr ⟨he, h⟩
        · exact Or.inl ⟨he, by omega, by omega⟩
      · have := H.long i e he; exact Or.inl ⟨he, by omega, by omega⟩
  · exact disjoint_filter.mpr fun e _ h1 h2 => by omega
  · exact disjoint_filter.mpr fun e _ h1 h2 => by omega

theorem walk_even (i : Fin s) (t : ℕ) : H.walk i (2 * t) = 2 * (H.dep i t : ℤ) := by
  simp [walk]

theorem walk_odd (i : Fin s) (t : ℕ) :
    H.walk i (2 * t + 1) = min (2 * (H.dep i t : ℤ)) (2 * (H.dep i (t + 1) : ℤ)) + 1 := by
  simp only [walk, show ¬ ((2 * t + 1) % 2 = 0) by omega, ↓reduceIte,
    show (2 * t + 1) / 2 = t by omega]

/-- The walk moves by exactly one cell per step: it is a walk without pauses. -/
theorem walk_step (i : Fin s) (τ : ℕ) :
    H.walk i (τ + 1) - H.walk i τ = 1 ∨ H.walk i (τ + 1) - H.walk i τ = -1 := by
  rcases Nat.even_or_odd τ with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · have hd := H.dep_succ i t
    have hl := H.card_left_le i t
    have hr := H.card_right_le i (t + 1)
    rw [show t + t + 1 = 2 * t + 1 by omega, show t + t = 2 * t by omega, walk_odd, walk_even]
    rcases le_total (2 * (H.dep i t : ℤ)) (2 * (H.dep i (t + 1) : ℤ)) with h | h
    · rw [min_eq_left h]; omega
    · rw [min_eq_right h]; omega
  · have hd := H.dep_succ i t
    have hl := H.card_left_le i t
    have hr := H.card_right_le i (t + 1)
    rw [show 2 * t + 1 + 1 = 2 * (t + 1) by omega, walk_odd, walk_even]
    rcases le_total (2 * (H.dep i t : ℤ)) (2 * (H.dep i (t + 1) : ℤ)) with h | h
    · rw [min_eq_left h]; omega
    · rw [min_eq_right h]; omega

theorem walk_isWalk (i : Fin s) : IsWalk (H.walk i) := by
  intro τ
  rcases H.walk_step i τ with h | h <;> rw [h] <;> norm_num

theorem walk_noPause (i : Fin s) (τ : ℕ) : H.walk i (τ + 1) ≠ H.walk i τ := by
  rcases H.walk_step i τ with h | h <;> omega

/-- An arc of the family contains the left end of an arc strictly inside if and only if it contains
its right end strictly inside. -/
theorem contains_left_iff {i : Fin s} {e e' : ℕ × ℕ} (he : e ∈ H.arcs i) (he' : e' ∈ H.arcs i) :
    (e'.1 < e.1 ∧ e.1 < e'.2) ↔ (e'.1 < e.2 ∧ e.2 < e'.2) := by
  have hl := H.long i e he
  have hl' := H.long i e' he'
  constructor
  · rintro ⟨h1, h2⟩
    have hnc := H.noCross i e' he' e he
    have hne : e'.2 ≠ e.2 := fun h => by
      have := H.rightUnique i e' he' e he h; rw [this] at h1; omega
    refine ⟨by omega, ?_⟩
    by_contra hle
    exact hnc ⟨h1, h2, by omega⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, by omega⟩
    by_contra hge
    rcases Nat.eq_or_lt_of_le (not_lt.mp hge) with heq | hlt
    · have := H.leftUnique i e he e' he' heq; rw [← this] at h2; omega
    · exact H.noCross i e he e' he' ⟨hlt, h1, h2⟩

/-- The two ends of an arc have the same nesting depth. -/
theorem dep_eq_of_arc {i : Fin s} {e : ℕ × ℕ} (he : e ∈ H.arcs i) : H.dep i e.1 = H.dep i e.2 := by
  unfold dep
  congr 1
  ext e'
  simp only [mem_filter, and_congr_right_iff]
  exact fun he' => H.contains_left_iff he he'

/-- Inside an arc the nesting depth exceeds that at its ends. -/
theorem dep_lt_of_mem {i : Fin s} {e : ℕ × ℕ} (he : e ∈ H.arcs i) {t : ℕ} (h1 : e.1 < t)
    (h2 : t < e.2) : H.dep i e.1 < H.dep i t := by
  unfold dep
  refine card_lt_card ⟨fun e' he'' => ?_, fun hsub => ?_⟩
  · obtain ⟨he', h3, h4⟩ := mem_filter.mp he''
    obtain ⟨h5, h6⟩ := (H.contains_left_iff he he').mp ⟨h3, h4⟩
    exact mem_filter.mpr ⟨he', by omega, by omega⟩
  · have := mem_filter.mp (hsub (mem_filter.mpr ⟨he, h1, h2⟩))
    omega

/-- Strictly inside the image of an arc, the walk of its family is above its ends. -/
theorem walk_above {i : Fin s} {e : ℕ × ℕ} (he : e ∈ H.arcs i) {τ : ℕ} (hτ1 : 2 * e.1 < τ)
    (hτ2 : τ < 2 * e.2) : H.walk i (2 * e.1) < H.walk i τ := by
  have heq := H.dep_eq_of_arc he
  rw [walk_even]
  rcases Nat.even_or_odd τ with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · rw [show t + t = 2 * t by omega, walk_even]
    have := H.dep_lt_of_mem he (t := t) (by omega) (by omega)
    omega
  · rw [walk_odd]
    have h3 : H.dep i e.1 ≤ H.dep i t := by
      rcases Nat.eq_or_lt_of_le (show e.1 ≤ t by omega) with h | h
      · rw [h]
      · exact (H.dep_lt_of_mem he h (by omega)).le
    have h4 : H.dep i e.1 ≤ H.dep i (t + 1) := by
      rcases Nat.eq_or_lt_of_le (show t + 1 ≤ e.2 by omega) with h | h
      · rw [h, heq]
      · exact (H.dep_lt_of_mem he (by omega) h).le
    have : 2 * (H.dep i e.1 : ℤ) + 1 ≤ min (2 * (H.dep i t : ℤ)) (2 * (H.dep i (t + 1) : ℤ)) + 1 := by
      have := le_min (show 2 * (H.dep i e.1 : ℤ) ≤ 2 * (H.dep i t : ℤ) by omega)
        (show 2 * (H.dep i e.1 : ℤ) ≤ 2 * (H.dep i (t + 1) : ℤ) by omega)
      omega
    omega

/-- **(b)** Arc `(p, u)` of family `i` is the upper long hop `(2p, 2u)` of walk `i`. -/
theorem walk_upperHop {i : Fin s} {e : ℕ × ℕ} (he : e ∈ H.arcs i) :
    IsUpperHop (H.walk i) (2 * e.1) (2 * e.2) := by
  have hl := H.long i e he
  have heq := H.dep_eq_of_arc he
  exact ⟨by omega, by rw [walk_even, walk_even, heq], fun τ h1 h2 => H.walk_above he h1 h2⟩

/-- **(b)** Arc `(p, u)` of family `i` is a long hop `(2p, 2u)` of walk `i` before `2N`. -/
theorem walk_hop {i : Fin s} {e : ℕ × ℕ} (he : e ∈ H.arcs i) :
    IsHop (H.walk i) (2 * N) (2 * e.1) (2 * e.2) := by
  have hl := H.long i e he
  have hu := H.walk_upperHop he
  exact ⟨hu.long, by omega, hu.eq, fun τ hτ => ne_of_gt (hu.above τ (mem_Ioo.mp hτ).1 (mem_Ioo.mp hτ).2)⟩

/-- The pulled-back spine cut: `t → t - 1` is cut if an edge of its image `2t → 2t - 1 → 2t - 2`
is. -/
def pullS (N : ℕ) (cutS : Finset ℕ) : Finset ℕ :=
  (Ico 1 N).filter fun t => 2 * t ∈ cutS ∨ 2 * t - 1 ∈ cutS

/-- The pulled-back arc cut: an arc `(p, u)` is cut if the hop edge `2u → 2p` is. -/
def pullA (cutH : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  H.arcSet.filter fun e => (2 * e.1, 2 * e.2) ∈ cutH

omit H in
theorem card_pullS_le (N : ℕ) (cutS : Finset ℕ) : (pullS N cutS).card ≤ cutS.card := by
  classical
  refine card_le_card_of_injOn (fun t => if 2 * t ∈ cutS then 2 * t else 2 * t - 1)
    (fun t ht => ?_) (fun t ht t' ht' h => ?_)
  · obtain ⟨-, h⟩ := mem_filter.mp (Finset.mem_coe.mp ht)
    simp only [Finset.mem_coe]
    split_ifs with h' <;> tauto
  · have h1 := (mem_Ico.mp (mem_filter.mp (Finset.mem_coe.mp ht)).1).1
    have h2 := (mem_Ico.mp (mem_filter.mp (Finset.mem_coe.mp ht')).1).1
    simp only at h
    split_ifs at h <;> omega

theorem card_pullA_le (cutH : Finset (ℕ × ℕ)) : (H.pullA cutH).card ≤ cutH.card :=
  card_le_card_of_injOn (fun e => (2 * e.1, 2 * e.2)) (fun e he => (mem_filter.mp he).2)
    (fun e _ e' _ h => by
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (by omega) (by omega))

theorem arc_mem_hopPairs {e : ℕ × ℕ} (he : e ∈ H.arcSet) :
    (2 * e.1, 2 * e.2) ∈ hopPairs (allHops H.walk (2 * N)) := by
  obtain ⟨i, -, hi⟩ := mem_biUnion.mp he
  exact mem_image.mpr ⟨(i, 2 * e.1, 2 * e.2), mem_allHops.mpr (H.walk_hop hi), rfl⟩

theorem not_hopPair_of_step {E : Finset (ℕ × ℕ)} (hE : ∀ e ∈ E, e.1 + 2 ≤ e.2) {a b : ℕ}
    (h : a + 1 = b) : (a, b) ∉ E := fun hm => by have := hE _ hm; simp only at this; omega

theorem hopPairs_long (xs : Fin k → ℕ → ℤ) (T : ℕ) :
    ∀ e ∈ hopPairs (allHops xs T), e.1 + 2 ≤ e.2 := by
  intro e he
  obtain ⟨η, hη, rfl⟩ := mem_image.mp he
  exact (mem_allHops.mp hη).1

/-- **Paths lift.** A path of the stack DAG that avoids the pulled-back cut maps to a path of the
walk DAG that avoids the cut, from `2 f 0` to `2 f n`, with as many hop edges as arcs. -/
theorem lift_path (cutS : Finset ℕ) (cutH : Finset (ℕ × ℕ)) : ∀ (n : ℕ) (f : ℕ → ℕ),
    AvoidPath N H.arcSet (H.pullA cutH) (pullS N cutS) f n →
    ∃ (g : ℕ → ℕ) (n' : ℕ), g 0 = 2 * f 0 ∧ g n' = 2 * f n ∧
      AvoidPath (2 * N) (hopPairs (allHops H.walk (2 * N))) cutH cutS g n' ∧
      arcCount (hopPairs (allHops H.walk (2 * N))) g n' = arcCount H.arcSet f n := by
  intro n
  induction n with
  | zero =>
    intro f _
    exact ⟨fun _ => 2 * f 0, 0, rfl, rfl, fun i hi => absurd hi (Nat.not_lt_zero _), by
      simp [arcCount]⟩
  | succ n ih =>
    intro f hf
    have hlong := hopPairs_long H.walk (2 * N)
    have hlongA : ∀ e ∈ H.arcSet, e.1 + 2 ≤ e.2 := fun e he => by
      obtain ⟨i, -, hi⟩ := mem_biUnion.mp he
      exact (H.long i e hi).1
    obtain ⟨g₂, n₂, hg0, hgn, hg, hgc⟩ := ih (fun i => f (i + 1)) (fun i hi => hf (i + 1) (by omega))
    -- the image of the first step
    have hfirst : ∃ (g₁ : ℕ → ℕ) (n₁ : ℕ), g₁ 0 = 2 * f 0 ∧ g₁ n₁ = 2 * f 1 ∧
        AvoidPath (2 * N) (hopPairs (allHops H.walk (2 * N))) cutH cutS g₁ n₁ ∧
        arcCount (hopPairs (allHops H.walk (2 * N))) g₁ n₁ =
          if (f 1, f 0) ∈ H.arcSet then 1 else 0 := by
      have hf0 := hf 0 (by omega)
      simp only [zero_add] at hf0
      rcases hf0 with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2⟩
      · have h4' : ¬ (2 * f 0 ∈ cutS ∨ 2 * f 0 - 1 ∈ cutS) := fun h =>
          h4 (mem_filter.mpr ⟨mem_Ico.mpr ⟨h2, h3⟩, h⟩)
        push Not at h4'
        refine ⟨fun i => 2 * f 0 - i, 2, by simp, by simp only; omega, fun i hi => ?_, ?_⟩
        · left
          interval_cases i
          · exact ⟨by simp only; omega, by simp only; omega, by simp only; omega, by simpa using h4'.1⟩
          · exact ⟨by simp only; omega, by simp only; omega, by simp only; omega, by
              simpa using h4'.2⟩
        · have hn := not_hopPair_of_step hlongA h1
          simp only [hn, ↓reduceIte]
          unfold arcCount
          rw [card_eq_zero, filter_eq_empty_iff]
          intro i hi
          exact not_hopPair_of_step hlong (by
            have := mem_range.mp hi; interval_cases i <;> simp only <;> omega)
      · have h2' : (2 * f 1, 2 * f 0) ∉ cutH := fun h => h2 (mem_filter.mpr ⟨h1, h⟩)
        refine ⟨fun i => if i = 0 then 2 * f 0 else 2 * f 1, 1, by simp, by simp,
          fun i hi => ?_, ?_⟩
        · have : i = 0 := by omega
          subst this
          right
          exact ⟨by simpa using H.arc_mem_hopPairs h1, by simpa using h2'⟩
        · have hm := H.arc_mem_hopPairs h1
          simp only [h1, ↓reduceIte]
          unfold arcCount
          rw [range_one, filter_singleton]
          have hm' : (2 * f 1, 2 * f 0) ∈ hopPairs (allHops H.walk (2 * N)) := by simpa using hm
          simp only [zero_add, one_ne_zero, ↓reduceIte, hm', card_singleton]
    obtain ⟨g₁, n₁, h10, h1n, hg1, hc1⟩ := hfirst
    obtain ⟨happ, hcount⟩ := hg1.append hg (h1n.trans hg0.symm)
    refine ⟨_, n₁ + n₂, ?_, ?_, happ, ?_⟩
    · simp [h10]
    · by_cases hn₂ : n₂ = 0
      · subst hn₂
        simp only [add_zero, le_refl, ↓reduceIte]
        rw [h1n, ← hg0, hgn]
      · simp only [show ¬ (n₁ + n₂ ≤ n₁) by omega, ↓reduceIte, Nat.add_sub_cancel_left, hgn]
    · rw [hcount, hc1, hgc, arcCount_succ]

/-- **The cut pulls back.** If every path of the walk DAG of the walks of `H` that avoids a cut
carries at most `D` hop edges, every path of `H` that avoids the pulled-back cut carries at most `D`
arcs. -/
theorem pullback_cut (cutS : Finset ℕ) (cutH : Finset (ℕ × ℕ)) (D : ℕ)
    (hD : ∀ g n, AvoidPath (2 * N) (hopPairs (allHops H.walk (2 * N))) cutH cutS g n →
      arcCount (hopPairs (allHops H.walk (2 * N))) g n ≤ D) :
    ∀ f n, AvoidPath N H.arcSet (H.pullA cutH) (pullS N cutS) f n → arcCount H.arcSet f n ≤ D := by
  intro f n hf
  obtain ⟨g, n', -, -, hg, hc⟩ := H.lift_path cutS cutH n f hf
  rw [← hc]
  exact hD g n' hg

end StackDag

/-! ### Consequences -/

/-- **TCP without pauses gives SR**: `TCP(k)` without pauses at `ε/2` gives `SR(k)` at `ε`, with the
same depth. -/
theorem srAt_of_tcpnpAt {s : ℕ} {ε : ℝ} {D : ℕ} (h : TCPnpAt s (ε / 2) D) : SRat s ε D := by
  intro N H
  obtain ⟨cutS, cutH, -, -, hsize, hdepth⟩ :=
    h (2 * N) H.walk H.walk_isWalk (fun i t _ => H.walk_noPause i t)
  refine ⟨StackDag.pullS N cutS, H.pullA cutH, filter_subset _ _, filter_subset _ _, ?_,
    H.pullback_cut cutS cutH D hdepth⟩
  have h1 := StackDag.card_pullS_le N cutS
  have h2 := H.card_pullA_le cutH
  have h3 : ((StackDag.pullS N cutS).card + (H.pullA cutH).card : ℝ) ≤ cutS.card + cutH.card := by
    exact_mod_cast Nat.add_le_add h1 h2
  push_cast at hsize ⊢
  nlinarith

/-- **SR gives TCP with pauses**: `SR(2k)` at `ε` gives `TCP(k)` with pauses at `ε`. -/
theorem tcpAt_of_srAt {ε : ℝ} {D : ℕ} (h : SRat (2 * k) ε D) : TCPat k ε D := by
  intro T xs hx
  obtain ⟨H, hH⟩ := walkDag_isStack xs hx T
  obtain ⟨cutS, cutA, hS, hA, hsize, hdepth⟩ := h T H
  rw [hH] at hA hdepth
  exact ⟨cutS, cutA, hS, hA, hsize, hdepth⟩

/-- `TCP(k)` without pauses implies `SR(k)`. -/
theorem sr_of_tcpnp (h : TCPnp k) : SR k := by
  intro ε hε
  obtain ⟨D, hD⟩ := h (ε / 2) (by positivity)
  exact ⟨D, srAt_of_tcpnpAt hD⟩

/-- `SR(2k)` implies `TCP(k)` with pauses. -/
theorem tcp_of_sr (h : SR (2 * k)) : TCP k := by
  intro ε hε
  obtain ⟨D, hD⟩ := h ε hε
  exact ⟨D, tcpAt_of_srAt hD⟩

/-- The forms of TCP with and without pauses are equivalent up to a factor `2` in the number of
walks: `TCP(k)` gives `TCP(k)` without pauses, and `TCP(2k)` without pauses gives `TCP(k)`. -/
theorem tcpnp_of_tcp (h : TCP k) : TCPnp k := by
  intro ε hε
  obtain ⟨D, hD⟩ := h ε hε
  exact ⟨D, fun T xs hx _ => hD T xs hx⟩

theorem tcp_of_tcpnp_two_mul (h : TCPnp (2 * k)) : TCP k := tcp_of_sr (sr_of_tcpnp h)

end BoundedNesting
