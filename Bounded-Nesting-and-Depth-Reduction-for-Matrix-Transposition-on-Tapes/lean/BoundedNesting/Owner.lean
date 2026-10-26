import Mathlib

/-!
# Nesting with distinct owners costs visits

A walk with steps in `{-1, 0, 1}` (pauses allowed) visits cells of `ℤ`. An upper hop `(p, u)` is
a pair of visits of one cell with the walk strictly above it in between and `u ≥ p + 2`; its owner
is the first time strictly inside at which the walk is highest.

`owner_entries`: if `ℓ` nested upper hops have pairwise distinct owners, the cell of the innermost
hop is entered at least `(ℓ + 1)/2` times. Each outer hop forces a crossing of the edge just above
that cell between its own endpoints and those of the next hop (its owner lies outside the next
hop, since owners are first maxima, and above the cell), the innermost hop crosses it twice, and
every entry accounts for at most two crossings (`card_crossings_le`).
-/

namespace BoundedNesting

open Finset

/-- A walk with steps in `{-1, 0, 1}`. -/
def IsWalk (x : ℕ → ℤ) : Prop := ∀ t, |x (t + 1) - x t| ≤ 1

/-- `(p, u)` is an upper hop of `x`: `u ≥ p + 2`, `x u = x p`, and the walk is strictly above `x p`
at every time strictly between. -/
structure IsUpperHop (x : ℕ → ℤ) (p u : ℕ) : Prop where
  long : p + 2 ≤ u
  eq : x u = x p
  above : ∀ t, p < t → t < u → x p < x t

/-- `o` is the owner of the hop `(p, u)`: the first time strictly inside at which the walk is
highest. -/
structure IsOwner (x : ℕ → ℤ) (p u o : ℕ) : Prop where
  gt : p < o
  lt : o < u
  max : ∀ t, p < t → t < u → x t ≤ x o
  first : ∀ t, p < t → t < o → x t < x o

/-- The entries into the cell `c` up to time `T`: the first visits of maximal runs of visits. -/
def entries (x : ℕ → ℤ) (c : ℤ) (T : ℕ) : Finset ℕ :=
  (range (T + 1)).filter (fun t => x t = c ∧ (t = 0 ∨ x (t - 1) ≠ c))

/-- The crossings of the edge between `c` and `c + 1` before time `T`. -/
def crossings (x : ℕ → ℤ) (c : ℤ) (T : ℕ) : Finset ℕ :=
  (range T).filter (fun t => (x t = c ∧ x (t + 1) = c + 1) ∨ (x t = c + 1 ∧ x (t + 1) = c))

theorem IsWalk.step {x : ℕ → ℤ} (hx : IsWalk x) (t : ℕ) :
    x (t + 1) ≤ x t + 1 ∧ x t ≤ x (t + 1) + 1 := by
  have := abs_le.mp (hx t); omega

theorem IsOwner.unique {x : ℕ → ℤ} {p u o o' : ℕ} (h : IsOwner x p u o) (h' : IsOwner x p u o') :
    o = o' := by
  rcases lt_trichotomy o o' with hlt | heq | hgt
  · have := h'.first o h.gt hlt; have := h.max o' h'.gt h'.lt; omega
  · exact heq
  · have := h.first o' h'.gt hgt; have := h'.max o h.gt h.lt; omega

theorem exists_down_crossing {x : ℕ → ℤ} (hx : IsWalk x) {c : ℤ} :
    ∀ n a, c + 1 ≤ x a → x (a + n) ≤ c → ∃ t, a ≤ t ∧ t < a + n ∧ x t = c + 1 ∧ x (t + 1) = c := by
  intro n
  induction n with
  | zero => intro a h1 h2; simp at h2; omega
  | succ n ih =>
    intro a h1 h2
    by_cases h : c + 1 ≤ x (a + 1)
    · obtain ⟨t, ht1, ht2, ht3, ht4⟩ :=
        ih (a + 1) h (by rwa [show a + 1 + n = a + (n + 1) by omega])
      exact ⟨t, by omega, by omega, ht3, ht4⟩
    · have := hx.step a
      exact ⟨a, le_refl a, by omega, by omega, by omega⟩

theorem exists_up_crossing {x : ℕ → ℤ} (hx : IsWalk x) {c : ℤ} :
    ∀ n a, x a ≤ c → c + 1 ≤ x (a + n) → ∃ t, a ≤ t ∧ t < a + n ∧ x t = c ∧ x (t + 1) = c + 1 := by
  intro n
  induction n with
  | zero => intro a h1 h2; simp at h2; omega
  | succ n ih =>
    intro a h1 h2
    by_cases h : x (a + 1) ≤ c
    · obtain ⟨t, ht1, ht2, ht3, ht4⟩ :=
        ih (a + 1) h (by rwa [show a + 1 + n = a + (n + 1) by omega])
      exact ⟨t, by omega, by omega, ht3, ht4⟩
    · have := hx.step a
      exact ⟨a, le_refl a, by omega, by omega, by omega⟩

/-- A visit at time `t ≤ T` lies in a run whose start is an entry at or before `t`, with every
time from the start to `t` a visit. -/
theorem exists_run_start {x : ℕ → ℤ} {c : ℤ} {T t : ℕ} (htT : t ≤ T) (ht : x t = c) :
    ∃ s, s ∈ entries x c T ∧ s ≤ t ∧ ∀ r, s ≤ r → r ≤ t → x r = c := by
  classical
  have hex : ∃ s, ∀ r, s ≤ r → r ≤ t → x r = c :=
    ⟨t, fun r h1 h2 => by rw [show r = t by omega]; exact ht⟩
  refine ⟨Nat.find hex, ?_, ?_, Nat.find_spec hex⟩
  · have hle : Nat.find hex ≤ t := Nat.find_min' hex (fun r h1 h2 => by
      rw [show r = t by omega]; exact ht)
    refine mem_filter.mpr ⟨mem_range.mpr (by omega), Nat.find_spec hex _ le_rfl hle, ?_⟩
    by_cases h0 : Nat.find hex = 0
    · exact Or.inl h0
    · right
      intro hprev
      have hmin := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
      apply hmin
      intro r h1 h2
      rcases Nat.eq_or_lt_of_le h1 with h | h
      · rw [← h]; exact hprev
      · exact Nat.find_spec hex r (by omega) h2
  · exact Nat.find_min' hex (fun r h1 h2 => by rw [show r = t by omega]; exact ht)

/-- **Crossings and entries.** Every crossing of the edge above `c` either enters `c` (a
down-crossing, followed by an entry) or leaves it (an up-crossing, the last visit of a run); each
run is entered once and left at most once. -/
theorem card_crossings_le (x : ℕ → ℤ) (c : ℤ) (T : ℕ) :
    (crossings x c T).card ≤ 2 * (entries x c T).card := by
  classical
  set ups := (range T).filter (fun t => x t = c ∧ x (t + 1) = c + 1)
  set downs := (range T).filter (fun t => x t = c + 1 ∧ x (t + 1) = c)
  have hsplit : crossings x c T = ups ∪ downs := by
    ext t; simp only [crossings, ups, downs, mem_filter, mem_union]; tauto
  have hdowns : downs.card ≤ (entries x c T).card := by
    refine card_le_card_of_injOn (fun t => t + 1) (fun t ht => ?_)
      (fun a _ b _ h => by simp only at h; omega)
    obtain ⟨htT, h1, h2⟩ := (by simpa [downs] using ht : t < T ∧ x t = c + 1 ∧ x (t + 1) = c)
    show t + 1 ∈ entries x c T
    refine mem_filter.mpr ⟨mem_range.mpr (by omega), h2, Or.inr ?_⟩
    simp only [Nat.add_sub_cancel]; omega
  have hups : ups.card ≤ (entries x c T).card := by
    -- each up-crossing is mapped to the latest entry at or before it
    have hne : ∀ t ∈ ups, ((entries x c T).filter (· ≤ t)).Nonempty := by
      intro t ht
      obtain ⟨htT, h1, -⟩ := (by simpa [ups] using ht : t < T ∧ x t = c ∧ x (t + 1) = c + 1)
      obtain ⟨s, hs, hst, -⟩ := exists_run_start (show t ≤ T by omega) h1
      exact ⟨s, mem_filter.mpr ⟨hs, hst⟩⟩
    let f : ℕ → ℕ := fun t =>
      if h : ((entries x c T).filter (· ≤ t)).Nonempty then
        ((entries x c T).filter (· ≤ t)).max' h else 0
    refine card_le_card_of_injOn f (fun t ht => ?_) ?_
    · have h := hne t ht
      simp only [f, h, ↓reduceDIte]
      exact (mem_filter.mp (max'_mem _ h)).1
    · -- two up-crossings with the same latest entry: the later one's run starts after the
      -- earlier one, a later entry
      have key : ∀ t ∈ ups, ∀ t' ∈ ups, t < t' → f t ≠ f t' := by
        intro t ht t' ht' htt' he
        obtain ⟨htT, h1, h2⟩ := (by simpa [ups] using ht : t < T ∧ x t = c ∧ x (t + 1) = c + 1)
        obtain ⟨htT', h1', -⟩ :=
          (by simpa [ups] using ht' : t' < T ∧ x t' = c ∧ x (t' + 1) = c + 1)
        obtain ⟨s, hs, hst, hrun⟩ := exists_run_start (show t' ≤ T by omega) h1'
        have hs1 : t + 1 < s := by
          by_contra hcon
          have := hrun (t + 1) (by omega) (by omega)
          omega
        have hmem : s ∈ (entries x c T).filter (· ≤ t') := mem_filter.mpr ⟨hs, hst⟩
        have hft' : s ≤ f t' := by
          simp only [f, hne t' ht', ↓reduceDIte]
          exact le_max' _ _ hmem
        have hft : f t ≤ t := by
          simp only [f, hne t ht, ↓reduceDIte]
          exact (mem_filter.mp (max'_mem _ (hne t ht))).2
        omega
      intro a ha b hb hab
      rcases lt_trichotomy a b with h | h | h
      · exact absurd hab (key a ha b hb h)
      · exact h
      · exact absurd hab.symm (key b hb a ha h)
  rw [hsplit]
  calc (ups ∪ downs).card ≤ ups.card + downs.card := card_union_le _ _
    _ ≤ 2 * (entries x c T).card := by omega

/-- **Nesting with distinct owners costs visits.** Let `(p i, u i)`, `i < ℓ`, be nested upper hops
of a walk (`0` outermost, `ℓ - 1` innermost) with pairwise distinct owners `o i`. Then the cell of
the innermost hop is entered at least `(ℓ + 1)/2` times up to any time `T ≥ u 0`. The same holds
for lower hops by reflection. -/
theorem owner_entries {x : ℕ → ℤ} (hx : IsWalk x) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (p u o : ℕ → ℕ)
    (hhop : ∀ i < ℓ, IsUpperHop x (p i) (u i))
    (hnest : ∀ i, i + 1 < ℓ → p i < p (i + 1) ∧ u (i + 1) < u i)
    (hown : ∀ i < ℓ, IsOwner x (p i) (u i) (o i))
    (hdist : ∀ i j, i < ℓ → j < ℓ → i ≠ j → o i ≠ o j)
    {T : ℕ} (hT : u 0 ≤ T) :
    ℓ + 1 ≤ 2 * (entries x (x (p (ℓ - 1))) T).card := by
  classical
  set n := ℓ - 1 with hn
  set c := x (p n) with hc
  -- the nesting is transitive
  have hmono : ∀ i j, i ≤ j → j < ℓ → p i ≤ p j ∧ u j ≤ u i := by
    intro i j hij hj
    induction j, hij using Nat.le_induction with
    | base => exact ⟨le_rfl, le_rfl⟩
    | succ j hij ih =>
      have h1 := hnest j (by omega)
      have h2 := ih (by omega)
      exact ⟨by omega, by omega⟩
  -- the cells increase inwards
  have hcell : ∀ i j, i ≤ j → j < ℓ → x (p i) ≤ x (p j) := by
    intro i j hij hj
    induction j, hij using Nat.le_induction with
    | base => exact le_rfl
    | succ j hij ih =>
      have h1 := hnest j (by omega)
      have h2 := (hhop (j + 1) hj).long
      have h3 := (hhop j (by omega)).above (p (j + 1)) h1.1 (by omega)
      have := ih (by omega)
      omega
  have hinner := hhop n (by omega)
  -- every owner is above the innermost cell
  have hhigh : ∀ i < ℓ, c + 1 ≤ x (o i) := by
    intro i hi
    have hm := hmono i n (by omega) (by omega)
    have h1 := hinner.above (p n + 1) (by omega) (by have := hinner.long; omega)
    have h2 := (hown i hi).max (p n + 1) (by omega) (by have := hinner.long; omega)
    omega
  -- the owner of an outer hop lies outside the next hop
  have hplace : ∀ i, i + 1 < ℓ → o i < p (i + 1) ∨ u (i + 1) < o i := by
    intro i hi
    have hhi := hhigh i (by omega)
    have hcp := hcell (i + 1) n (by omega) (by omega)
    have heq := (hhop (i + 1) hi).eq
    by_contra hcon
    simp only [not_or, not_lt] at hcon
    rcases Nat.eq_or_lt_of_le hcon.1 with h | h
    · rw [← h] at hhi; omega
    rcases Nat.eq_or_lt_of_le hcon.2 with h' | h'
    · rw [h', heq] at hhi; omega
    have hown' : IsOwner x (p (i + 1)) (u (i + 1)) (o i) :=
      ⟨h, h', fun t ht1 ht2 => (hown i (by omega)).max t (by have := hnest i hi; omega)
          (by have := hnest i hi; omega),
        fun t ht1 ht2 => (hown i (by omega)).first t (by have := hnest i hi; omega) ht2⟩
    exact hdist i (i + 1) (by omega) hi (by omega) (hown'.unique (hown (i + 1) hi))
  -- one crossing of the edge above `c` for every outer hop
  have hcross : ∀ i, i + 1 < ℓ → ∃ τ, τ ∈ crossings x c T ∧
      ((p i < τ ∧ τ < p (i + 1)) ∨ (u (i + 1) ≤ τ ∧ τ < u i)) := by
    intro i hi
    have hown_i := hown i (by omega)
    have hhi := hhigh i (by omega)
    have hcp : x (p (i + 1)) ≤ c := hcell (i + 1) n (by omega) (by omega)
    have heq := (hhop (i + 1) hi).eq
    have hu0 := hmono 0 i (by omega) (by omega)
    have hlong' := (hhop (i + 1) hi).long
    have hnest' := hnest i hi
    have hlt := hown_i.lt
    have hgt := hown_i.gt
    rcases hplace i hi with h | h
    · have e : o i + (p (i + 1) - o i) = p (i + 1) := by omega
      obtain ⟨τ, h1, h2, h3, h4⟩ := exists_down_crossing hx (c := c) (p (i + 1) - o i) (o i) hhi
        (by rw [e]; exact hcp)
      rw [e] at h2
      exact ⟨τ, mem_filter.mpr ⟨mem_range.mpr (by omega), Or.inr ⟨h3, h4⟩⟩,
        Or.inl ⟨by omega, h2⟩⟩
    · have e : u (i + 1) + (o i - u (i + 1)) = o i := by omega
      obtain ⟨τ, h1, h2, h3, h4⟩ := exists_up_crossing hx (c := c) (o i - u (i + 1)) (u (i + 1))
        (by rw [heq]; exact hcp) (by rw [e]; exact hhi)
      rw [e] at h2
      exact ⟨τ, mem_filter.mpr ⟨mem_range.mpr (by omega), Or.inl ⟨h3, h4⟩⟩,
        Or.inr ⟨h1, by omega⟩⟩
  choose! τ hτ using hcross
  -- the innermost hop crosses twice
  have hstep0 := hx.step (p n)
  have hstep1 := hx.step (u n - 1)
  have hlong := hinner.long
  have hin1 : x (p n + 1) = c + 1 := by
    have := hinner.above (p n + 1) (by omega) (by omega); omega
  have hin2 : x (u n - 1) = c + 1 := by
    have h := hinner.above (u n - 1) (by omega) (by omega)
    have heq := hinner.eq
    rw [show u n - 1 + 1 = u n by omega] at hstep1
    omega
  have hu0n := hmono 0 n (by omega) (by omega)
  have hA : p n ∈ crossings x c T :=
    mem_filter.mpr ⟨mem_range.mpr (by omega), Or.inl ⟨rfl, hin1⟩⟩
  have hB : u n - 1 ∈ crossings x c T := by
    refine mem_filter.mpr ⟨mem_range.mpr (by omega), Or.inr ⟨hin2, ?_⟩⟩
    rw [show u n - 1 + 1 = u n by omega]; exact hinner.eq
  -- the crossings are distinct
  have hpos : ∀ i, i < n → τ i < p n ∨ u n ≤ τ i := by
    intro i hi
    have hm := hmono (i + 1) n (by omega) (by omega)
    rcases (hτ i (by omega)).2 with h | h
    · left; omega
    · right; omega
  have hinj : Set.InjOn τ (range n) := by
    intro i hi j hj hij
    simp only [coe_range, Set.mem_Iio] at hi hj
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have hm := hmono (i + 1) j (by omega) (by omega)
      have hm' := hmono (j + 1) n (by omega) (by omega)
      have hmi := hmono (i + 1) n (by omega) (by omega)
      rcases (hτ i (by omega)).2 with h1 | h1 <;> rcases (hτ j (by omega)).2 with h2 | h2 <;> omega
    · have hm := hmono (j + 1) i (by omega) (by omega)
      have hm' := hmono (i + 1) n (by omega) (by omega)
      have hmj := hmono (j + 1) n (by omega) (by omega)
      rcases (hτ i (by omega)).2 with h1 | h1 <;> rcases (hτ j (by omega)).2 with h2 | h2 <;> omega
  have hsub : insert (p n) (insert (u n - 1) ((range n).image τ)) ⊆ crossings x c T := by
    intro y hy
    simp only [mem_insert, mem_image, mem_range] at hy
    rcases hy with rfl | rfl | ⟨i, hi, rfl⟩
    · exact hA
    · exact hB
    · exact (hτ i (by omega)).1
  have hcard : (insert (p n) (insert (u n - 1) ((range n).image τ))).card = n + 2 := by
    rw [card_insert_of_notMem, card_insert_of_notMem, card_image_of_injOn hinj, card_range]
    · simp only [mem_image, mem_range, not_exists, not_and]
      intro i hi h; have := hpos i hi; omega
    · simp only [mem_insert, mem_image, mem_range, not_or, not_exists, not_and]
      exact ⟨by omega, fun i hi h => by have := hpos i hi; omega⟩
  have h1 := card_le_card hsub
  have h2 := card_crossings_le x c T
  omega

end BoundedNesting
