import BoundedStackDepth.Walks

/-!
# The canonical decomposition of one walk by tops

Let `x` be a walk (pauses allowed) and `T` a horizon. The *upper hops* (`upperHops`) are the hops
before `T` along which the walk steps up after the start; they are exactly the hops that are
upper hops (`mem_upperHops`). The *top* of an upper hop is its owner `hopOwner`, the first time
strictly inside at which the walk is highest (`tops`). The *ladder* of `τ` is the set of upper
hops with top `τ` (`ladder`), its *height* is the number of its hops (`height`), and its *base
cell* is `x τ - height`.

* `image_cell_ladder`, `ladder_cell_iff`, `ladder_eq_of_cell`: the cells of the ladder of `τ` are
  exactly `[x τ - height, x τ)`, one hop per cell. The hop of cell `z`
  runs from the last visit to `z` before `τ` to the first visit after (`exists_ladder_cell`).
  Every upper hop lies in exactly one ladder, that of its top (`mem_ladder_hopOwner`,
  `eq_of_mem_ladder`).
* `ladder_lt`, `ladder_above`, `ladder_last_visit`, `ladder_first_visit`, `ladder_nested`,
  `exists_ladder_outer`: a ladder hop spans its top, the walk is strictly above its cell inside,
  its start is the last visit to the cell up to the top and its end the first visit from the top
  on; a higher cell gives a later start and an earlier end, and the hop of the base cell contains
  all the others.
* `top_spec`, `top_ne_start`, `top_ne_end`: a top `τ` has `1 ≤ τ`, `τ + 1 < T`,
  `x (τ - 1) < x τ` and `x (τ + 1) ≤ x τ`; it is neither the start nor the end of an upper hop.
* `card_upperHops_add_card_tops_le`, `sum_height_eq`: the start map of upper hops is injective and
  avoids the tops, and the heights add up to the number of upper hops.
* `hops_neg`, `upperHops_neg`: the lower hops (`lowerHops`) are the upper hops of `-x`, so everything
  above applies to the lower side; every hop is upper or lower (`upperHops_union_lowerHops`).
* `ladder_eq_filter`, `tops_eq_filter`: decidable forms of the ladders and the tops (`hopOwner` is
  noncomputable), used by the kernel-checked examples at the end.
-/

namespace BoundedStackDepth

open BoundedNesting Finset

/-! ### Last and first visits -/

/-- A walk at or below `z` at `a` and above `z` at `b ≥ a` has a last visit to `z` in `[a, b)`. -/
theorem exists_last_visit {x : ℕ → ℤ} (hx : IsWalk x) {a b : ℕ} {z : ℤ} (hab : a ≤ b)
    (ha : x a ≤ z) (hb : z < x b) :
    ∃ L, a ≤ L ∧ L < b ∧ x L = z ∧ ∀ t, L < t → t ≤ b → x t ≠ z := by
  obtain ⟨s, hs1, hs2, hs3, -⟩ := exists_up_crossing hx (c := z) (b - a) a ha
    (by rw [show a + (b - a) = b by omega]; omega)
  obtain ⟨L, hL, hmax⟩ := ((Ico a b).filter (fun t => x t = z)).exists_max_image id
    ⟨s, mem_filter.mpr ⟨mem_Ico.mpr ⟨hs1, by omega⟩, hs3⟩⟩
  obtain ⟨hL1, hL2⟩ := mem_filter.mp hL
  obtain ⟨hL3, hL4⟩ := mem_Ico.mp hL1
  refine ⟨L, hL3, hL4, hL2, fun t ht1 ht2 htz => ?_⟩
  rcases Nat.lt_or_ge t b with h | h
  · have := hmax t (mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega, h⟩, htz⟩)
    simp only [id] at this
    omega
  · rw [show t = b by omega] at htz
    omega

/-- A walk above `z` at `a` and at or below `z` at `b ≥ a` has a first visit to `z` in `(a, b]`. -/
theorem exists_first_visit {x : ℕ → ℤ} (hx : IsWalk x) {a b : ℕ} {z : ℤ} (hab : a ≤ b)
    (ha : z < x a) (hb : x b ≤ z) :
    ∃ D, a < D ∧ D ≤ b ∧ x D = z ∧ ∀ t, a ≤ t → t < D → x t ≠ z := by
  obtain ⟨s, hs1, hs2, -, hs4⟩ := exists_down_crossing hx (c := z) (b - a) a (by omega)
    (by rw [show a + (b - a) = b by omega]; exact hb)
  obtain ⟨D, hD, hmin⟩ := ((Ioc a b).filter (fun t => x t = z)).exists_min_image id
    ⟨s + 1, mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega, by omega⟩, hs4⟩⟩
  obtain ⟨hD1, hD2⟩ := mem_filter.mp hD
  obtain ⟨hD3, hD4⟩ := mem_Ioc.mp hD1
  refine ⟨D, hD3, hD4, hD2, fun t ht1 ht2 htz => ?_⟩
  rcases Nat.eq_or_lt_of_le ht1 with h | h
  · rw [← h] at htz
    omega
  · have := hmin t (mem_filter.mpr ⟨mem_Ioc.mpr ⟨h, by omega⟩, htz⟩)
    simp only [id] at this
    omega

/-! ### Upper hops, tops and ladders -/

/-- The upper hops of `x` before `T`: the hops along which the walk steps up after the start. -/
def upperHops (x : ℕ → ℤ) (T : ℕ) : Finset (ℕ × ℕ) :=
  (hops x T).filter (fun e => x e.1 < x (e.1 + 1))

/-- The lower hops of `x` before `T`: the hops along which the walk steps down after the start. -/
def lowerHops (x : ℕ → ℤ) (T : ℕ) : Finset (ℕ × ℕ) :=
  (hops x T).filter (fun e => x (e.1 + 1) < x e.1)

/-- The tops of `x` before `T`: the owners of the upper hops. -/
noncomputable def tops (x : ℕ → ℤ) (T : ℕ) : Finset ℕ :=
  (upperHops x T).image (fun e => hopOwner x e.1 e.2)

/-- The ladder of `τ`: the upper hops with top `τ`. -/
noncomputable def ladder (x : ℕ → ℤ) (T τ : ℕ) : Finset (ℕ × ℕ) :=
  (upperHops x T).filter (fun e => hopOwner x e.1 e.2 = τ)

/-- The height of `τ`: the number of hops of its ladder. -/
noncomputable def height (x : ℕ → ℤ) (T τ : ℕ) : ℕ := (ladder x T τ).card

variable {x : ℕ → ℤ} {T τ : ℕ} {e e' : ℕ × ℕ}

theorem isHop_of_mem_upperHops (he : e ∈ upperHops x T) : IsHop x T e.1 e.2 :=
  mem_hops.mp (mem_filter.mp he).1

/-- The upper hops are the hops that are upper hops. -/
theorem mem_upperHops (hx : IsWalk x) :
    e ∈ upperHops x T ↔ IsHop x T e.1 e.2 ∧ IsUpperHop x e.1 e.2 := by
  rw [upperHops, mem_filter, mem_hops]
  constructor
  · rintro ⟨hh, hup⟩
    exact ⟨hh, ⟨hh.1, hh.2.2.1, above_of_step hx hh hup⟩⟩
  · rintro ⟨hh, hu⟩
    exact ⟨hh, hu.above _ (by omega) (by have := hu.long; omega)⟩

/-- The owner of an upper hop is its first argmax. -/
theorem hopOwner_eq_iff {p u o : ℕ} (hu : IsUpperHop x p u) :
    hopOwner x p u = o ↔ IsOwner x p u o :=
  ⟨fun h => h ▸ isOwner_hopOwner_of_upper hu, fun h => (isOwner_hopOwner_of_upper hu).unique h⟩

theorem mem_ladder (hx : IsWalk x) :
    e ∈ ladder x T τ ↔ IsHop x T e.1 e.2 ∧ IsUpperHop x e.1 e.2 ∧ IsOwner x e.1 e.2 τ := by
  rw [ladder, mem_filter, mem_upperHops hx]
  constructor
  · rintro ⟨⟨hh, hu⟩, ho⟩
    exact ⟨hh, hu, (hopOwner_eq_iff hu).mp ho⟩
  · rintro ⟨hh, hu, ho⟩
    exact ⟨⟨hh, hu⟩, (hopOwner_eq_iff hu).mpr ho⟩

theorem mem_tops : τ ∈ tops x T ↔ (ladder x T τ).Nonempty := by
  simp only [tops, ladder, mem_image, Finset.Nonempty, mem_filter]

theorem one_le_height (hτ : τ ∈ tops x T) : 1 ≤ height x T τ :=
  card_pos.mpr (mem_tops.mp hτ)

theorem mem_upperHops_of_mem_ladder (he : e ∈ ladder x T τ) : e ∈ upperHops x T :=
  (mem_filter.mp he).1

theorem isHop_of_mem_ladder (he : e ∈ ladder x T τ) : IsHop x T e.1 e.2 :=
  isHop_of_mem_upperHops (mem_upperHops_of_mem_ladder he)

/-- Every upper hop lies in the ladder of its top. -/
theorem mem_ladder_hopOwner (he : e ∈ upperHops x T) : e ∈ ladder x T (hopOwner x e.1 e.2) :=
  mem_filter.mpr ⟨he, rfl⟩

/-- An upper hop lies in one ladder only. -/
theorem eq_of_mem_ladder {τ' : ℕ} (he : e ∈ ladder x T τ) (he' : e ∈ ladder x T τ') : τ = τ' :=
  (mem_filter.mp he).2.symm.trans (mem_filter.mp he').2

/-- A ladder hop spans its top. -/
theorem ladder_lt (he : e ∈ ladder x T τ) : e.1 < τ ∧ τ < e.2 := by
  obtain ⟨he1, rfl⟩ := mem_filter.mp he
  have := hopOwner_spec x (isHop_of_mem_upperHops he1).1
  exact ⟨this.1, this.2.1⟩

/-- The walk is strictly above the cell of a ladder hop inside it. -/
theorem ladder_above (hx : IsWalk x) (he : e ∈ ladder x T τ) :
    ∀ t, e.1 < t → t < e.2 → x e.1 < x t :=
  ((mem_ladder hx).mp he).2.1.above

theorem ladder_cell_lt (hx : IsWalk x) (he : e ∈ ladder x T τ) : x e.1 < x τ :=
  ladder_above hx he τ (ladder_lt he).1 (ladder_lt he).2

/-- The start of a ladder hop is the last visit to its cell up to the top. -/
theorem ladder_last_visit (hx : IsWalk x) (he : e ∈ ladder x T τ) {t : ℕ} (ht : t ≤ τ)
    (hxt : x t = x e.1) : t ≤ e.1 := by
  by_contra h
  have := ladder_above hx he t (by omega) (by have := (ladder_lt he).2; omega)
  omega

/-- The end of a ladder hop is the first visit to its cell from the top on. -/
theorem ladder_first_visit (hx : IsWalk x) (he : e ∈ ladder x T τ) {t : ℕ} (ht : τ ≤ t)
    (hxt : x t = x e.1) : e.2 ≤ t := by
  by_contra h
  have := ladder_above hx he t (by have := (ladder_lt he).1; omega) (by omega)
  omega

/-- Two hops of one ladder with the same cell coincide. -/
theorem ladder_eq_of_cell (he : e ∈ ladder x T τ) (he' : e' ∈ ladder x T τ)
    (hc : x e.1 = x e'.1) : e = e' := by
  obtain ⟨h1, h2⟩ := hop_unique (isHop_of_mem_ladder he) (isHop_of_mem_ladder he') hc
    ⟨(ladder_lt he).1, (ladder_lt he).2.le⟩ ⟨(ladder_lt he').1, (ladder_lt he').2.le⟩
  exact Prod.ext h1 h2

/-- Ladder hops nest: a higher cell gives a later start and an earlier end. -/
theorem ladder_nested (hx : IsWalk x) (he : e ∈ ladder x T τ) (he' : e' ∈ ladder x T τ)
    (hc : x e.1 < x e'.1) : e.1 < e'.1 ∧ e'.2 < e.2 := by
  have hu := ((mem_ladder hx).mp he).2.1
  have hu' := ((mem_ladder hx).mp he').2.1
  have h1 := ladder_lt he
  have h2 := ladder_lt he'
  constructor
  · by_contra hcon
    rcases Nat.eq_or_lt_of_le (not_lt.mp hcon) with h | h
    · rw [h] at hc
      exact lt_irrefl _ hc
    · have := hu'.above e.1 h (by omega)
      omega
  · by_contra hcon
    rcases Nat.eq_or_lt_of_le (not_lt.mp hcon) with h | h
    · have h3 := hu.eq
      have h4 := hu'.eq
      rw [h] at h3
      omega
    · have := hu'.above e.2 (by omega) h
      have := hu.eq
      omega

/-- **Completeness of a ladder.** If `e` is a hop of the ladder of `τ` and `x e.1 ≤ z < x τ`, the
ladder has a hop of cell `z` inside `e`: from the last visit to `z` before `τ` to the first visit
after. -/
theorem exists_ladder_cell (hx : IsWalk x) (he : e ∈ ladder x T τ) {z : ℤ} (hz1 : x e.1 ≤ z)
    (hz2 : z < x τ) : ∃ e' ∈ ladder x T τ, x e'.1 = z ∧ e.1 ≤ e'.1 ∧ e'.2 ≤ e.2 := by
  obtain ⟨hh, hu, ho⟩ := (mem_ladder hx).mp he
  obtain ⟨L, hL1, hL2, hL3, hL4⟩ := exists_last_visit hx ho.gt.le hz1 hz2
  obtain ⟨D, hD1, hD2, hD3, hD4⟩ := exists_first_visit hx ho.lt.le hz2 (by rw [hu.eq]; exact hz1)
  have hLD : IsHop x T L D := by
    refine ⟨by omega, by have := hh.2.1; omega, by rw [hL3, hD3], fun t ht => ?_⟩
    obtain ⟨ht1, ht2⟩ := mem_Ioo.mp ht
    rw [hL3]
    rcases Nat.lt_or_ge t τ with h | h
    · exact hL4 t ht1 h.le
    · exact hD4 t h ht2
  have hup : IsUpperHop x L D := by
    rcases IsHop.upper_or_lower hx hLD with h | h
    · exact h
    · have := h.below τ hL2 hD1
      omega
  refine ⟨(L, D), (mem_ladder hx).mpr ⟨hLD, hup, ?_⟩, hL3, hL1, hD2⟩
  exact ⟨hL2, hD1, fun t ht1 ht2 => ho.max t (by omega) (by omega),
    fun t ht1 ht2 => ho.first t (by omega) ht2⟩

/-- **One hop per cell.** The cells of the ladder of `τ` are exactly `[x τ - height, x τ)`. -/
theorem image_cell_ladder (hx : IsWalk x) (T τ : ℕ) :
    (ladder x T τ).image (fun e => x e.1) = Ico (x τ - height x T τ) (x τ) := by
  rcases (ladder x T τ).eq_empty_or_nonempty with h | h
  · simp [height, h]
  obtain ⟨e₀, he₀, hmin⟩ := (ladder x T τ).exists_min_image (fun e => x e.1) h
  have key : (ladder x T τ).image (fun e => x e.1) = Ico (x e₀.1) (x τ) := by
    ext z
    simp only [mem_image, mem_Ico]
    constructor
    · rintro ⟨e, he, rfl⟩
      exact ⟨hmin e he, ladder_cell_lt hx he⟩
    · rintro ⟨hz1, hz2⟩
      obtain ⟨e', he', hc, -⟩ := exists_ladder_cell hx he₀ hz1 hz2
      exact ⟨e', he', hc⟩
  have hcard : height x T τ = (x τ - x e₀.1).toNat := by
    rw [height, ← card_image_of_injOn (f := fun e => x e.1)
      (fun e he e' he' hc => ladder_eq_of_cell he he' hc), key, Int.card_Ico]
  have hlt := ladder_cell_lt hx he₀
  rw [key, show x τ - height x T τ = x e₀.1 by rw [hcard]; omega]

/-- **One hop per cell.** The ladder of `τ` has a hop of cell `z` iff `x τ - height ≤ z < x τ` (both
sides are false for every `z` if `τ` is not a top). -/
theorem ladder_cell_iff (hx : IsWalk x) {z : ℤ} :
    (∃ e ∈ ladder x T τ, x e.1 = z) ↔ x τ - height x T τ ≤ z ∧ z < x τ := by
  rw [← mem_Ico, ← image_cell_ladder hx T τ, mem_image]

theorem ladder_cell_bounds (hx : IsWalk x) (he : e ∈ ladder x T τ) :
    x τ - height x T τ ≤ x e.1 ∧ x e.1 < x τ :=
  (ladder_cell_iff hx).mp ⟨e, he, rfl⟩

/-- The hop of the base cell of a top contains every hop of its ladder. -/
theorem exists_ladder_outer (hx : IsWalk x) (hτ : τ ∈ tops x T) :
    ∃ e ∈ ladder x T τ, x e.1 = x τ - height x T τ ∧
      ∀ e' ∈ ladder x T τ, e.1 ≤ e'.1 ∧ e'.2 ≤ e.2 := by
  have hh := one_le_height hτ
  obtain ⟨e, he, hc⟩ := (ladder_cell_iff hx (z := x τ - height x T τ)).mpr ⟨le_rfl, by omega⟩
  refine ⟨e, he, hc, fun e' he' => ?_⟩
  have h' := (ladder_cell_bounds hx he').1
  rcases eq_or_lt_of_le (show x e.1 ≤ x e'.1 by omega) with h | h
  · obtain rfl := ladder_eq_of_cell he he' h
    exact ⟨le_rfl, le_rfl⟩
  · have := ladder_nested hx he he' h
    exact ⟨this.1.le, this.2.le⟩

/-! ### Tops -/

/-- **A top is a peak.** A top `τ` has `1 ≤ τ`, `τ + 1 < T`, `x (τ - 1) < x τ` and
`x (τ + 1) ≤ x τ`. -/
theorem top_spec (hx : IsWalk x) (hτ : τ ∈ tops x T) :
    1 ≤ τ ∧ τ + 1 < T ∧ x (τ - 1) < x τ ∧ x (τ + 1) ≤ x τ := by
  obtain ⟨e, he⟩ := mem_tops.mp hτ
  obtain ⟨hh, hu, ho⟩ := (mem_ladder hx).mp he
  have h1 := ho.gt
  have h2 := ho.lt
  have h3 := hh.2.1
  refine ⟨by omega, by omega, ?_, ?_⟩
  · rcases Nat.eq_or_lt_of_le (show e.1 ≤ τ - 1 by omega) with h | h
    · rw [← h]
      exact hu.above τ h1 h2
    · exact ho.first (τ - 1) h (by omega)
  · rcases Nat.eq_or_lt_of_le (show τ + 1 ≤ e.2 by omega) with h | h
    · rw [h, hu.eq]
      exact (hu.above τ h1 h2).le
    · exact ho.max (τ + 1) (by omega) h

/-- A top is never the start of an upper hop. -/
theorem top_ne_start (hx : IsWalk x) (hτ : τ ∈ tops x T) (he : e ∈ upperHops x T) : e.1 ≠ τ := by
  intro h
  have h1 : x e.1 < x (e.1 + 1) := (mem_filter.mp he).2
  rw [h] at h1
  have := (top_spec hx hτ).2.2.2
  omega

/-- A top is never the end of an upper hop. -/
theorem top_ne_end (hx : IsWalk x) (hτ : τ ∈ tops x T) (he : e ∈ upperHops x T) : e.2 ≠ τ := by
  intro h
  obtain ⟨-, hu⟩ := (mem_upperHops hx).mp he
  have h1 := hu.above (e.2 - 1) (by have := hu.long; omega) (by have := hu.long; omega)
  have h2 := hu.eq
  rw [h] at h1 h2
  have := (top_spec hx hτ).2.2.1
  omega

/-! ### Counting -/

/-- **Counting.** The starts of the upper hops are distinct, and distinct from the tops. -/
theorem card_upperHops_add_card_tops_le (hx : IsWalk x) (T : ℕ) :
    (upperHops x T).card + (tops x T).card ≤ T := by
  have hinj : Set.InjOn (fun e : ℕ × ℕ => e.1) (upperHops x T : Set (ℕ × ℕ)) := by
    intro e he e' he' h
    have hh := isHop_of_mem_upperHops (mem_coe.mp he)
    have hh' := isHop_of_mem_upperHops (mem_coe.mp he')
    simp only at h
    rw [← h] at hh'
    exact Prod.ext h (hop_start_unique hh hh')
  have hdisj : Disjoint ((upperHops x T).image (fun e => e.1)) (tops x T) := by
    rw [disjoint_left]
    intro t ht hτ
    obtain ⟨e, he, rfl⟩ := mem_image.mp ht
    exact top_ne_start hx hτ he rfl
  have hsub : (upperHops x T).image (fun e => e.1) ∪ tops x T ⊆ range T := by
    intro t ht
    rcases mem_union.mp ht with ht | ht
    · obtain ⟨e, he, rfl⟩ := mem_image.mp ht
      have hh := isHop_of_mem_upperHops he
      exact mem_range.mpr (by have := hh.1; have := hh.2.1; omega)
    · exact mem_range.mpr (by have := (top_spec hx ht).2.1; omega)
  have := card_le_card hsub
  rwa [card_union_of_disjoint hdisj, card_image_of_injOn hinj, card_range] at this

/-- The heights of the tops add up to the number of upper hops. -/
theorem sum_height_eq (x : ℕ → ℤ) (T : ℕ) :
    ∑ τ ∈ tops x T, height x T τ = (upperHops x T).card :=
  (card_eq_sum_card_fiberwise (f := fun e : ℕ × ℕ => hopOwner x e.1 e.2) (s := upperHops x T)
    (t := tops x T) (fun _ he => mem_image_of_mem _ he)).symm

/-! ### Reflection -/

theorem isHop_neg {p u : ℕ} : IsHop (fun t => -x t) T p u ↔ IsHop x T p u := by
  simp only [IsHop, neg_inj, ne_eq]

/-- Reflection does not change the hops. -/
theorem hops_neg (x : ℕ → ℤ) (T : ℕ) : hops (fun t => -x t) T = hops x T := by
  ext e
  rw [mem_hops, mem_hops, isHop_neg]

/-- The upper hops of `-x` are the lower hops of `x`. -/
theorem upperHops_neg (x : ℕ → ℤ) (T : ℕ) : upperHops (fun t => -x t) T = lowerHops x T := by
  simp only [upperHops, lowerHops, hops_neg, neg_lt_neg_iff]

/-- Every hop is an upper hop or a lower hop. -/
theorem upperHops_union_lowerHops (x : ℕ → ℤ) (T : ℕ) :
    upperHops x T ∪ lowerHops x T = hops x T := by
  ext e
  simp only [upperHops, lowerHops, mem_union, mem_filter]
  constructor
  · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
  · intro h
    have hh := mem_hops.mp h
    have hne := hh.2.2.2 (e.1 + 1) (mem_Ioo.mpr ⟨by omega, by have := hh.1; omega⟩)
    rcases lt_or_gt_of_ne hne with h' | h'
    · exact Or.inr ⟨h, h'⟩
    · exact Or.inl ⟨h, h'⟩

/-! ### Decidable forms -/

/-- `IsOwner` with bounded quantifiers. -/
theorem isOwner_iff {p u o : ℕ} : IsOwner x p u o ↔
    o ∈ Ioo p u ∧ (∀ t ∈ Ioo p u, x t ≤ x o) ∧ ∀ t ∈ Ioo p o, x t < x o := by
  simp only [mem_Ioo]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨h1, h2⟩, fun t ht => h3 t ht.1 ht.2, fun t ht => h4 t ht.1 ht.2⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨h1, h2, fun t ht1 ht2 => h3 t ⟨ht1, ht2⟩, fun t ht1 ht2 => h4 t ⟨ht1, ht2⟩⟩

/-- The ladder of `τ`, in decidable form. -/
theorem ladder_eq_filter (hx : IsWalk x) (T τ : ℕ) :
    ladder x T τ = (upperHops x T).filter (fun e =>
      τ ∈ Ioo e.1 e.2 ∧ (∀ t ∈ Ioo e.1 e.2, x t ≤ x τ) ∧ ∀ t ∈ Ioo e.1 τ, x t < x τ) := by
  ext e
  simp only [ladder, mem_filter]
  constructor
  · rintro ⟨he, ho⟩
    exact ⟨he, isOwner_iff.mp ((hopOwner_eq_iff ((mem_upperHops hx).mp he).2).mp ho)⟩
  · rintro ⟨he, ho⟩
    exact ⟨he, (hopOwner_eq_iff ((mem_upperHops hx).mp he).2).mpr (isOwner_iff.mpr ho)⟩

/-- The tops, in decidable form. -/
theorem tops_eq_filter (hx : IsWalk x) (T : ℕ) :
    tops x T = (range T).filter (fun τ => ∃ e ∈ upperHops x T,
      τ ∈ Ioo e.1 e.2 ∧ (∀ t ∈ Ioo e.1 e.2, x t ≤ x τ) ∧ ∀ t ∈ Ioo e.1 τ, x t < x τ) := by
  ext τ
  rw [mem_tops, mem_filter, ladder_eq_filter hx]
  constructor
  · rintro ⟨e, he⟩
    obtain ⟨he1, he2⟩ := mem_filter.mp he
    have := (isHop_of_mem_upperHops he1).2.1
    have := (mem_Ioo.mp he2.1).2
    exact ⟨mem_range.mpr (by omega), e, he1, he2⟩
  · rintro ⟨-, e, he1, he2⟩
    exact ⟨e, mem_filter.mpr ⟨he1, he2⟩⟩

/-! ### Examples

The walk `0, 1, 2, 3, 2, 3, 2, 1, 0` of the paper's example: the hop `(2, 4)` of the top `3` ends
where the hop `(4, 6)` of the top `5` starts. The walk `0, 1, 1, 0` pauses at its top. The examples
are checked by the kernel. -/

/-- A finite walk as a function, `0` after its end. -/
private def ofList (l : List ℤ) : ℕ → ℤ := fun t => l.getD t 0

private theorem isWalk_ofList (l : List ℤ)
    (h : ∀ t < l.length, |ofList l (t + 1) - ofList l t| ≤ 1) : IsWalk (ofList l) := by
  intro t
  rcases Nat.lt_or_ge t l.length with ht | ht
  · exact h t ht
  · show |l.getD (t + 1) 0 - l.getD t 0| ≤ 1
    rw [List.getD_eq_default _ _ ht, List.getD_eq_default _ _ (show l.length ≤ t + 1 by omega)]
    decide

example : upperHops (ofList [0, 1, 2, 3, 2, 3, 2, 1, 0]) 9 = {(0, 8), (1, 7), (2, 4), (4, 6)} := by
  decide

example : lowerHops (ofList [0, 1, 2, 3, 2, 3, 2, 1, 0]) 9 = {(3, 5)} := by decide

example : tops (ofList [0, 1, 2, 3, 2, 3, 2, 1, 0]) 9 = {3, 5} := by
  rw [tops_eq_filter (isWalk_ofList _ (by decide))]; decide

example : ladder (ofList [0, 1, 2, 3, 2, 3, 2, 1, 0]) 9 3 = {(0, 8), (1, 7), (2, 4)} := by
  rw [ladder_eq_filter (isWalk_ofList _ (by decide))]; decide

example : ladder (ofList [0, 1, 2, 3, 2, 3, 2, 1, 0]) 9 5 = {(4, 6)} := by
  rw [ladder_eq_filter (isWalk_ofList _ (by decide))]; decide

example : tops (ofList [0, 1, 1, 0]) 4 = {1} := by
  rw [tops_eq_filter (isWalk_ofList _ (by decide))]; decide

end BoundedStackDepth
