import BoundedNesting.WalkDag

/-!
# Owner-load from bounded entry, and the capacity of depth

* `owner_entries_lower`: the owner lemma for lower hops, by the reflection `x ↦ -x`.
* `ownerLoad_le_of_entries` (Corollary "bounded entry bounds the owner-load"): if every hop of `H'`
  lies at a cell that its head enters at most `V` times, then `H'` has owner-load at most `2V - 1`
  for the owners of the paper (`hopOwner`). The hops of one head and side open at a time `t` form
  a chain; one hop per owner, sorted by start, is a strictly nested sequence to which the owner
  lemma applies, seen from the side of the hops.
* `tcp_of_entries` (Corollary "bounded entry implies TCP").
* `card_heavyPairs_mul_le`, `card_span_heavyPairs_le`, `capacity_cut` (Corollary "the capacity of
  depth"): the pairs `R` entered more than `V` times number at most `kT/(V + 1)`, at most `|R|` of
  their hops span any time, and the rest of the walk DAG is cut by Theorem F.
-/

namespace BoundedNesting

open Finset

/-! ### Lower hops -/

/-- `(p, u)` is a lower hop of `x`: `u ≥ p + 2`, `x u = x p`, and the walk is strictly below `x p`
at every time strictly between. -/
structure IsLowerHop (x : ℕ → ℤ) (p u : ℕ) : Prop where
  long : p + 2 ≤ u
  eq : x u = x p
  below : ∀ t, p < t → t < u → x t < x p

/-- `o` is the owner of the lower hop `(p, u)`: the first time strictly inside at which the walk is
lowest. -/
structure IsLowerOwner (x : ℕ → ℤ) (p u o : ℕ) : Prop where
  gt : p < o
  lt : o < u
  min : ∀ t, p < t → t < u → x o ≤ x t
  first : ∀ t, p < t → t < o → x o < x t

theorem IsLowerHop.neg {x : ℕ → ℤ} {p u : ℕ} (h : IsLowerHop x p u) :
    IsUpperHop (fun t => -x t) p u :=
  ⟨h.long, by simp [h.eq], fun t h1 h2 => by have := h.below t h1 h2; omega⟩

theorem IsLowerOwner.neg {x : ℕ → ℤ} {p u o : ℕ} (h : IsLowerOwner x p u o) :
    IsOwner (fun t => -x t) p u o :=
  ⟨h.gt, h.lt, fun t h1 h2 => by have := h.min t h1 h2; omega,
    fun t h1 h2 => by have := h.first t h1 h2; omega⟩

/-- Reflection does not change entries. -/
theorem entries_neg (x : ℕ → ℤ) (c : ℤ) (T : ℕ) :
    entries (fun t => -x t) (-c) T = entries x c T := by
  ext t
  simp only [entries, mem_filter, neg_inj, ne_eq]

/-- **The owner lemma for lower hops**, by the reflection `x ↦ -x`. -/
theorem owner_entries_lower {x : ℕ → ℤ} (hx : IsWalk x) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (p u o : ℕ → ℕ)
    (hhop : ∀ i < ℓ, IsLowerHop x (p i) (u i))
    (hnest : ∀ i, i + 1 < ℓ → p i < p (i + 1) ∧ u (i + 1) < u i)
    (hown : ∀ i < ℓ, IsLowerOwner x (p i) (u i) (o i))
    (hdist : ∀ i j, i < ℓ → j < ℓ → i ≠ j → o i ≠ o j)
    {T : ℕ} (hT : u 0 ≤ T) :
    ℓ + 1 ≤ 2 * (entries x (x (p (ℓ - 1))) T).card := by
  have := owner_entries hx.neg hℓ p u o (fun i hi => (hhop i hi).neg) hnest
    (fun i hi => (hown i hi).neg) hdist hT
  rwa [entries_neg] at this

/-! ### Owners seen from the side of a hop -/

variable {k : ℕ}

theorem abs_sw_sub (xs : Fin k → ℕ → ℤ) (h : Fin k) (σ : Bool) (s t : ℕ) :
    |sw xs h σ t - sw xs h σ s| = |xs h t - xs h s| := by
  cases σ
  · simp only [sw, Bool.false_eq_true, ↓reduceIte]
    rw [show -xs h t - -xs h s = -(xs h t - xs h s) by ring, abs_neg]
  · simp [sw]

theorem entries_sw (xs : Fin k → ℕ → ℤ) (h : Fin k) (σ : Bool) (p T : ℕ) :
    entries (sw xs h σ) (sw xs h σ p) T = entries (xs h) (xs h p) T := by
  cases σ
  · have e : sw xs h false = fun t => -xs h t := by funext t; simp [sw]
    rw [e]
    exact entries_neg _ _ _
  · have e : sw xs h true = xs h := by funext t; simp [sw]
    rw [e]

theorem isUpperHop_sw {xs : Fin k → ℕ → ℤ} (hx : ∀ h, IsWalk (xs h)) {T : ℕ}
    {η : Fin k × ℕ × ℕ} (hh : IsHop (xs η.1) T η.2.1 η.2.2) :
    IsUpperHop (sw xs η.1 (side xs η)) η.2.1 η.2.2 :=
  ⟨hh.1, (isHop_sw hh _).2.2.1, sw_above hx hh⟩

/-- Seen from its side, the owner of the paper of a hop is its owner in the sense of `IsOwner`: the
first time strictly inside at which the walk is highest. -/
theorem isOwner_hopOwner {xs : Fin k → ℕ → ℤ} (hx : ∀ h, IsWalk (xs h)) {T : ℕ}
    {η : Fin k × ℕ × ℕ} (hh : IsHop (xs η.1) T η.2.1 η.2.2) :
    IsOwner (sw xs η.1 (side xs η)) η.2.1 η.2.2 (hopOwner (xs η.1) η.2.1 η.2.2) := by
  obtain ⟨h1, h2, h3, h4⟩ := hopOwner_spec (xs η.1) hh.1
  have hab := sw_above hx hh
  have key : ∀ t, η.2.1 < t → t < η.2.2 → |xs η.1 t - xs η.1 η.2.1| =
      sw xs η.1 (side xs η) t - sw xs η.1 (side xs η) η.2.1 := by
    intro t ht1 ht2
    rw [← abs_sw_sub xs η.1 (side xs η) η.2.1 t]
    exact abs_of_pos (by have := hab t ht1 ht2; linarith)
  refine ⟨h1, h2, fun t ht1 ht2 => ?_, fun t ht1 ht2 => ?_⟩
  · have := h3 t ht1 ht2
    rw [key t ht1 ht2, key _ h1 h2] at this
    linarith
  · have := h4 t ht1 ht2
    rw [key t ht1 (by omega), key _ h1 h2] at this
    linarith

/-! ### Bounded entry bounds the owner-load -/

/-- **Bounded entry bounds the owner-load.** Let every hop of `H'` of head `h` at a cell `c` be such
that `x_h` enters `c` at most `V` times up to `T - 1`. Then `H'` has owner-load at most `2V - 1`
for the owners of the paper. -/
theorem ownerLoad_le_of_entries {T V : ℕ} {xs : Fin k → ℕ → ℤ} (hx : ∀ h, IsWalk (xs h))
    {H' : Finset (Fin k × ℕ × ℕ)} (hH : ∀ η ∈ H', IsHop (xs η.1) T η.2.1 η.2.2)
    (hV : ∀ η ∈ H', (entries (xs η.1) (xs η.1 η.2.1) (T - 1)).card ≤ V) :
    OwnerLoadLE xs H' (fun η => hopOwner (xs η.1) η.2.1 η.2.2) (2 * V - 1) := by
  classical
  intro h σ t
  set S := H'.filter (fun η => η.1 = h ∧ side xs η = σ ∧ η.2.1 < t ∧ t < η.2.2) with hS
  set O := S.image (fun η => hopOwner (xs η.1) η.2.1 η.2.2) with hO
  rcases Nat.eq_zero_or_pos O.card with h0 | hpos
  · rw [h0]; exact Nat.zero_le _
  have hSmem : ∀ η ∈ S, η ∈ H' ∧ η.1 = h ∧ side xs η = σ ∧ η.2.1 < t ∧ t < η.2.2 :=
    fun η hη => mem_filter.mp hη
  -- one hop for each owner
  have hex : ∀ o, ∃ η, o ∈ O → η ∈ S ∧ hopOwner (xs η.1) η.2.1 η.2.2 = o := by
    intro o
    by_cases ho : o ∈ O
    · obtain ⟨η, hη, he⟩ := mem_image.mp ho
      exact ⟨η, fun _ => ⟨hη, he⟩⟩
    · exact ⟨(h, 0, 0), fun h' => absurd h' ho⟩
  choose g hg using hex
  have hgS : ∀ o ∈ O, g o ∈ S := fun o ho => (hg o ho).1
  have hgo : ∀ o ∈ O, hopOwner (xs (g o).1) (g o).2.1 (g o).2.2 = o := fun o ho => (hg o ho).2
  have hhop : ∀ η ∈ S, IsHop (xs h) T η.2.1 η.2.2 := by
    intro η hη
    obtain ⟨hH', h1, -⟩ := hSmem η hη
    have := hH η hH'
    rwa [h1] at this
  have hup : ∀ η ∈ S, IsUpperHop (sw xs h σ) η.2.1 η.2.2 := by
    intro η hη
    obtain ⟨hH', h1, h2, -, -⟩ := hSmem η hη
    have := isUpperHop_sw hx (hH η hH')
    rw [h2, h1] at this
    exact this
  have hown : ∀ η ∈ S, IsOwner (sw xs h σ) η.2.1 η.2.2 (hopOwner (xs h) η.2.1 η.2.2) := by
    intro η hη
    obtain ⟨hH', h1, h2, -, -⟩ := hSmem η hη
    have := isOwner_hopOwner hx (hH η hH')
    rw [h2, h1] at this
    exact this
  -- the chosen hops start at distinct times
  have hstart_inj : Set.InjOn (fun o => (g o).2.1) O := by
    intro o ho o' ho' he
    simp only at he
    have h2 : IsHop (xs h) T (g o).2.1 (g o').2.2 := by rw [he]; exact hhop _ (hgS o' ho')
    have hu := hop_start_unique (hhop _ (hgS o ho)) h2
    have heq : g o = g o' := Prod.ext ((hSmem _ (hgS o ho)).2.1.trans (hSmem _ (hgS o' ho')).2.1.symm)
      (Prod.ext he hu)
    rw [← hgo o ho, ← hgo o' ho', heq]
  -- sort the starts
  have hStcard : (O.image (fun o => (g o).2.1)).card = O.card := card_image_of_injOn hstart_inj
  set e := (O.image (fun o => (g o).2.1)).orderEmbOfFin hStcard
  have hex2 : ∀ i : ℕ, ∃ o, ∀ hi : i < O.card, o ∈ O ∧ (g o).2.1 = e ⟨i, hi⟩ := by
    intro i
    by_cases hi : i < O.card
    · obtain ⟨o, ho, he⟩ := mem_image.mp
        ((O.image (fun o => (g o).2.1)).orderEmbOfFin_mem hStcard ⟨i, hi⟩)
      exact ⟨o, fun _ => ⟨ho, he⟩⟩
    · exact ⟨0, fun h' => absurd h' hi⟩
  choose q hq using hex2
  have hqO : ∀ i (hi : i < O.card), q i ∈ O := fun i hi => (hq i hi).1
  have hpmono : ∀ i j (hi : i < O.card) (hj : j < O.card), i < j → (g (q i)).2.1 < (g (q j)).2.1 := by
    intro i j hi hj hij
    rw [(hq i hi).2, (hq j hj).2]
    exact e.strictMono (show (⟨i, hi⟩ : Fin O.card) < ⟨j, hj⟩ from hij)
  have hcont : ∀ i (hi : i < O.card), (g (q i)).2.1 < t ∧ t < (g (q i)).2.2 := fun i hi =>
    ⟨(hSmem _ (hgS _ (hqO i hi))).2.2.2.1, (hSmem _ (hgS _ (hqO i hi))).2.2.2.2⟩
  have hnest : ∀ i, i + 1 < O.card → (g (q i)).2.1 < (g (q (i + 1))).2.1 ∧
      (g (q (i + 1))).2.2 < (g (q i)).2.2 := by
    intro i hi
    have h1 := hpmono i (i + 1) (by omega) hi (by omega)
    refine ⟨h1, ?_⟩
    have hu1 := hup _ (hgS _ (hqO i (by omega)))
    have hu2 := hup _ (hgS _ (hqO (i + 1) hi))
    have c1 := hcont i (by omega)
    have c2 := hcont (i + 1) hi
    rcases lt_trichotomy (g (q (i + 1))).2.2 (g (q i)).2.2 with hlt | heq | hgt
    · exact hlt
    · exfalso
      have h2 : IsHop (xs h) T (g (q (i + 1))).2.1 (g (q i)).2.2 := by
        rw [← heq]; exact hhop _ (hgS _ (hqO (i + 1) hi))
      have := hop_end_unique (hhop _ (hgS _ (hqO i (by omega)))) h2
      omega
    · exfalso
      have a1 := hu1.above (g (q (i + 1))).2.1 h1 (by omega)
      have a2 := hu2.above (g (q i)).2.2 (by omega) hgt
      have := hu1.eq
      omega
  have hdist : ∀ i j, i < O.card → j < O.card → i ≠ j → q i ≠ q j := by
    intro i j hi hj hij he
    rcases Nat.lt_or_gt_of_ne hij with h' | h'
    · have := hpmono i j hi hj h'; rw [he] at this; omega
    · have := hpmono j i hj hi h'; rw [he] at this; omega
  have hownq : ∀ i (hi : i < O.card), IsOwner (sw xs h σ) (g (q i)).2.1 (g (q i)).2.2 (q i) := by
    intro i hi
    have h1 := hown _ (hgS _ (hqO i hi))
    have h2 := hgo _ (hqO i hi)
    rw [(hSmem _ (hgS _ (hqO i hi))).2.1] at h2
    rwa [h2] at h1
  have hT : (g (q 0)).2.2 ≤ T - 1 := by
    have := (hhop _ (hgS _ (hqO 0 hpos))).2.1
    omega
  have key := owner_entries (isWalk_sw hx h σ) hpos (fun i => (g (q i)).2.1) (fun i => (g (q i)).2.2) q
    (fun i hi => hup _ (hgS _ (hqO i hi))) hnest (fun i hi => hownq i hi) hdist hT
  rw [entries_sw] at key
  have hlast := hgS _ (hqO (O.card - 1) (by omega))
  have hbound := hV _ (hSmem _ hlast).1
  rw [(hSmem _ hlast).2.1] at hbound
  omega

/-! ### Bounded entry implies TCP -/

/-- **Bounded entry implies TCP.** If every walk enters every cell at most `V` times up to `T - 1`,
then for every `ε > 0` the walk DAG has a cut of at most `εT` edges and depth less than
`DF k (2V - 1) ε`. -/
theorem tcp_of_entries {T V : ℕ} (hk : 1 ≤ k) (hV : 1 ≤ V) {ε : ℝ} (hε : 0 < ε)
    (xs : Fin k → ℕ → ℤ) (hx : ∀ h, IsWalk (xs h))
    (hent : ∀ h c, (entries (xs h) c (T - 1)).card ≤ V) :
    ∃ (cutS : Finset ℕ) (cutH : Finset (ℕ × ℕ)), cutS ⊆ Ico 1 T ∧
      cutH ⊆ hopPairs (allHops xs T) ∧ ((cutS.card + cutH.card : ℕ) : ℝ) ≤ ε * T ∧
      ∀ (f : ℕ → ℕ) (n : ℕ),
        (∀ i < n, (f (i + 1) + 1 = f i ∧ 1 ≤ f i ∧ f i < T ∧ f i ∉ cutS) ∨
          ((f (i + 1), f i) ∈ hopPairs (allHops xs T) ∧ (f (i + 1), f i) ∉ cutH)) →
        ((range n).filter (fun i => (f (i + 1), f i) ∈ hopPairs (allHops xs T))).card <
          DF k (2 * V - 1) ε :=
  theoremF_owner hk (by omega) hε xs hx (allHops xs T) (fun η hη => mem_allHops.mp hη)
    (ownerLoad_le_of_entries hx (fun η hη => mem_allHops.mp hη) (fun η _ => hent _ _))

/-! ### The capacity of depth -/

/-- The pairs `(h, c)` such that `x_h` visits `c` before `T` and enters it more than `V` times up to
`T - 1`. -/
def heavyPairs (xs : Fin k → ℕ → ℤ) (T V : ℕ) : Finset (Fin k × ℤ) :=
  univ.biUnion fun h => (((range T).image (xs h)).filter
    (fun c => V < (entries (xs h) c (T - 1)).card)).image (fun c => (h, c))

theorem mem_heavyPairs {xs : Fin k → ℕ → ℤ} {T V : ℕ} {h : Fin k} {c : ℤ} :
    (h, c) ∈ heavyPairs xs T V ↔
      (∃ t < T, xs h t = c) ∧ V < (entries (xs h) c (T - 1)).card := by
  simp only [heavyPairs, mem_biUnion, mem_univ, true_and, mem_image, mem_filter, mem_range,
    Prod.mk.injEq]
  constructor
  · rintro ⟨h', c', ⟨⟨t, ht, rfl⟩, hV⟩, rfl, rfl⟩
    exact ⟨⟨t, ht, rfl⟩, hV⟩
  · rintro ⟨⟨t, ht, rfl⟩, hV⟩
    exact ⟨h, xs h t, ⟨⟨t, ht, rfl⟩, hV⟩, rfl, rfl⟩

/-- The hops at pairs entered at most `V` times: the hop edges of `G - R`. -/
def lightHops (xs : Fin k → ℕ → ℤ) (T V : ℕ) : Finset (Fin k × ℕ × ℕ) :=
  (allHops xs T).filter (fun η => (η.1, xs η.1 η.2.1) ∉ heavyPairs xs T V)

/-- A walk enters cells at most `T` times in all up to `T - 1`. -/
theorem sum_card_entries_le (x : ℕ → ℤ) {T : ℕ} (hT : 1 ≤ T) (C : Finset ℤ) :
    ∑ c ∈ C, (entries x c (T - 1)).card ≤ T := by
  rw [← card_biUnion]
  · calc (C.biUnion fun c => entries x c (T - 1)).card ≤ (range T).card := by
          refine card_le_card fun t ht => ?_
          obtain ⟨c, -, hc⟩ := mem_biUnion.mp ht
          have := (mem_filter.mp hc).1
          rw [mem_range] at this ⊢
          omega
      _ = T := card_range T
  · intro c _ c' _ hne
    simp only [Function.onFun]
    rw [disjoint_left]
    intro t h1 h2
    exact hne ((mem_filter.mp h1).2.1.symm.trans (mem_filter.mp h2).2.1)

/-- **The pairs entered more than `V` times** number at most `kT/(V + 1)`. -/
theorem card_heavyPairs_mul_le (xs : Fin k → ℕ → ℤ) (T V : ℕ) :
    (heavyPairs xs T V).card * (V + 1) ≤ k * T := by
  rcases Nat.eq_zero_or_pos T with rfl | hT
  · have : heavyPairs xs 0 V = ∅ := by ext x; simp [heavyPairs]
    simp [this]
  have hh : ∀ h : Fin k, (((range T).image (xs h)).filter
      (fun c => V < (entries (xs h) c (T - 1)).card)).card * (V + 1) ≤ T := by
    intro h
    set C := ((range T).image (xs h)).filter (fun c => V < (entries (xs h) c (T - 1)).card)
    calc C.card * (V + 1) = ∑ _c ∈ C, (V + 1) := by rw [sum_const, smul_eq_mul]
      _ ≤ ∑ c ∈ C, (entries (xs h) c (T - 1)).card :=
          sum_le_sum fun c hc => (mem_filter.mp hc).2
      _ ≤ T := sum_card_entries_le (xs h) hT C
  calc (heavyPairs xs T V).card * (V + 1)
      ≤ (∑ h : Fin k, ((((range T).image (xs h)).filter
          (fun c => V < (entries (xs h) c (T - 1)).card)).image (fun c => (h, c))).card) * (V + 1) :=
        Nat.mul_le_mul_right _ card_biUnion_le
    _ ≤ (∑ h : Fin k, (((range T).image (xs h)).filter
          (fun c => V < (entries (xs h) c (T - 1)).card)).card) * (V + 1) :=
        Nat.mul_le_mul_right _ (sum_le_sum fun h _ => card_image_le)
    _ = ∑ h : Fin k, (((range T).image (xs h)).filter
          (fun c => V < (entries (xs h) c (T - 1)).card)).card * (V + 1) := by rw [sum_mul]
    _ ≤ ∑ _h : Fin k, T := sum_le_sum fun h _ => hh h
    _ = k * T := by simp

/-- With `V = ⌈1/ε⌉`, fewer than `kεT` pairs are entered more than `V` times. -/
theorem card_heavyPairs_lt (xs : Fin k → ℕ → ℤ) {T : ℕ} (hk : 1 ≤ k) (hT : 1 ≤ T) {ε : ℝ}
    (hε : 0 < ε) : ((heavyPairs xs T ⌈1 / ε⌉₊).card : ℝ) < k * ε * T := by
  have h1 := card_heavyPairs_mul_le xs T ⌈1 / ε⌉₊
  have h2 : 1 / ε ≤ (⌈1 / ε⌉₊ : ℝ) := Nat.le_ceil _
  have h1' : ((heavyPairs xs T ⌈1 / ε⌉₊).card : ℝ) * ((⌈1 / ε⌉₊ : ℝ) + 1) ≤ k * T := by
    exact_mod_cast h1
  have hkT : (0 : ℝ) < k * T := by positivity
  have h3 : (1 : ℝ) < ε * ((⌈1 / ε⌉₊ : ℝ) + 1) := by
    have := mul_le_mul_of_nonneg_left h2 hε.le
    rw [mul_one_div_cancel hε.ne'] at this
    nlinarith
  by_contra hge
  push Not at hge
  have h4 : (k : ℝ) * T < (heavyPairs xs T ⌈1 / ε⌉₊).card * ((⌈1 / ε⌉₊ : ℝ) + 1) := by
    calc (k : ℝ) * T = k * T * 1 := by ring
      _ < k * T * (ε * ((⌈1 / ε⌉₊ : ℝ) + 1)) := mul_lt_mul_of_pos_left h3 hkT
      _ = k * ε * T * ((⌈1 / ε⌉₊ : ℝ) + 1) := by ring
      _ ≤ (heavyPairs xs T ⌈1 / ε⌉₊).card * ((⌈1 / ε⌉₊ : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right hge (by positivity)
  linarith

/-- **(P1) at the heavy pairs.** At every time `τ`, at most `|R|` hops at pairs of `R` span `τ`. -/
theorem card_span_heavyPairs_le (xs : Fin k → ℕ → ℤ) (T V τ : ℕ) :
    ((allHops xs T).filter (fun η => (η.1, xs η.1 η.2.1) ∈ heavyPairs xs T V ∧
      η.2.1 < τ ∧ τ ≤ η.2.2)).card ≤ (heavyPairs xs T V).card := by
  refine card_le_card_of_injOn (fun η => (η.1, xs η.1 η.2.1)) (fun η hη => ?_)
    (fun η hη η' hη' he => ?_)
  · exact (mem_filter.mp (Finset.mem_coe.mp hη)).2.1
  · obtain ⟨hA, -, hτ⟩ := mem_filter.mp (Finset.mem_coe.mp hη)
    obtain ⟨hA', -, hτ'⟩ := mem_filter.mp (Finset.mem_coe.mp hη')
    simp only [Prod.mk.injEq] at he
    obtain ⟨hh, hc⟩ := he
    have h1 := mem_allHops.mp hA
    have h2 := mem_allHops.mp hA'
    rw [hh] at h1 hc
    obtain ⟨hp, hu⟩ := hop_unique h1 h2 hc hτ hτ'
    exact Prod.ext hh (Prod.ext hp hu)

/-- Hops at pairs outside `R` lie at cells entered at most `V` times. -/
theorem entries_le_of_lightHops {xs : Fin k → ℕ → ℤ} {T V : ℕ} {η : Fin k × ℕ × ℕ}
    (hη : η ∈ lightHops xs T V) : (entries (xs η.1) (xs η.1 η.2.1) (T - 1)).card ≤ V := by
  obtain ⟨hA, hR⟩ := mem_filter.mp hη
  by_contra hlt
  push Not at hlt
  exact hR (mem_heavyPairs.mpr ⟨⟨η.2.1, by have := (mem_allHops.mp hA).2.1; have := (mem_allHops.mp hA).1; omega, rfl⟩, hlt⟩)

/-- **The capacity of depth.** With `V = ⌈1/ε⌉`, the DAG `G - R` of the state edges and the hops at
pairs entered at most `V` times has a cut of at most `εT` edges and depth less than
`DF k (2V - 1) ε`. -/
theorem capacity_cut {T : ℕ} (hk : 1 ≤ k) {ε : ℝ} (hε : 0 < ε) (xs : Fin k → ℕ → ℤ)
    (hx : ∀ h, IsWalk (xs h)) :
    ∃ (cutS : Finset ℕ) (cutH : Finset (ℕ × ℕ)), cutS ⊆ Ico 1 T ∧
      cutH ⊆ hopPairs (lightHops xs T ⌈1 / ε⌉₊) ∧ ((cutS.card + cutH.card : ℕ) : ℝ) ≤ ε * T ∧
      ∀ (f : ℕ → ℕ) (n : ℕ),
        (∀ i < n, (f (i + 1) + 1 = f i ∧ 1 ≤ f i ∧ f i < T ∧ f i ∉ cutS) ∨
          ((f (i + 1), f i) ∈ hopPairs (lightHops xs T ⌈1 / ε⌉₊) ∧ (f (i + 1), f i) ∉ cutH)) →
        ((range n).filter (fun i => (f (i + 1), f i) ∈ hopPairs (lightHops xs T ⌈1 / ε⌉₊))).card <
          DF k (2 * ⌈1 / ε⌉₊ - 1) ε := by
  have hV : 1 ≤ ⌈1 / ε⌉₊ := Nat.one_le_iff_ne_zero.mpr (by
    rw [Ne, Nat.ceil_eq_zero, not_le]; positivity)
  have hH : ∀ η ∈ lightHops xs T ⌈1 / ε⌉₊, IsHop (xs η.1) T η.2.1 η.2.2 :=
    fun η hη => mem_allHops.mp (mem_filter.mp hη).1
  exact theoremF_owner hk (by omega) hε xs hx _ hH
    (ownerLoad_le_of_entries hx hH fun η hη => entries_le_of_lightHops hη)

end BoundedNesting
