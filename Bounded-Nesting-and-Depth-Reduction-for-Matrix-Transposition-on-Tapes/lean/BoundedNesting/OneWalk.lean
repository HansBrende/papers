import BoundedNesting.Owner
import BoundedNesting.Labels

/-!
# Lemma W: the strip cut for one walk

Let `x` be a walk with steps in `{-1, 0, 1}` on the times `[0, T)`. Its walk DAG has the state
edges `t → t - 1` and an edge `u → p` for every hop `(p, u)` (consecutive visits of one cell with
`u ≥ p + 2`). For integers `w ≥ 2` and `r ≥ 1`:
* choose a residue `ρ` mod `w` whose cells are visited at most `T / w` times (`Z`, the line times);
* the cells strictly between consecutive lines form strips; count the visits to each strip;
* label a time by its strip's count plus an offset `ω`, modulo `r`;
* cut the edges at `Z`, the hops along which the label does not decrease, and the state edges
  along which it increases.

`strip_cut`: for some `ρ` and `ω` the cut has at most `4T/w + wT/r` edges
(`w r · #cut ≤ 4 r T + w² T`); `strip_cut_depth`: every path of the remaining DAG carries at most
`r − 1` hop edges. With `w = ⌈8/ε⌉`, `r = ⌈2w/ε⌉` this is a cut of at most `εT` edges and depth
`O(1/ε²)`.
-/

namespace BoundedNesting

open Finset

/-- `(p, u)` is a hop of `x` before `T`: consecutive visits of one cell with `u ≥ p + 2`. -/
def IsHop (x : ℕ → ℤ) (T p u : ℕ) : Prop :=
  p + 2 ≤ u ∧ u < T ∧ x u = x p ∧ ∀ t ∈ Ioo p u, x t ≠ x p

instance (x : ℕ → ℤ) (T p u : ℕ) : Decidable (IsHop x T p u) := by
  unfold IsHop; infer_instance

/-- The hops of `x` before `T`. -/
def hops (x : ℕ → ℤ) (T : ℕ) : Finset (ℕ × ℕ) :=
  ((range T) ×ˢ (range T)).filter (fun e => IsHop x T e.1 e.2)

theorem mem_hops {x : ℕ → ℤ} {T : ℕ} {e : ℕ × ℕ} : e ∈ hops x T ↔ IsHop x T e.1 e.2 := by
  simp only [hops, mem_filter, mem_product, mem_range]
  constructor
  · exact fun h => h.2
  · intro h; exact ⟨⟨by have := h.1; have := h.2.1; omega, h.2.1⟩, h⟩

/-- At every time each cell carries at most one hop spanning it. -/
theorem hop_unique {x : ℕ → ℤ} {T p u p' u' τ : ℕ} (h : IsHop x T p u) (h' : IsHop x T p' u')
    (hc : x p = x p') (hτ : p < τ ∧ τ ≤ u) (hτ' : p' < τ ∧ τ ≤ u') : p = p' ∧ u = u' := by
  obtain ⟨hl, -, he, hin⟩ := h
  obtain ⟨hl', -, he', hin'⟩ := h'
  have hp : p = p' := by
    rcases lt_trichotomy p p' with hlt | heq | hgt
    · exact absurd hc.symm (hin p' (mem_Ioo.mpr ⟨hlt, by omega⟩))
    · exact heq
    · exact absurd hc (hin' p (mem_Ioo.mpr ⟨hgt, by omega⟩))
  subst hp
  refine ⟨rfl, ?_⟩
  rcases lt_trichotomy u u' with hlt | heq | hgt
  · exact absurd he (hin' u (mem_Ioo.mpr ⟨by omega, hlt⟩))
  · exact heq
  · exact absurd he' (hin u' (mem_Ioo.mpr ⟨by omega, hgt⟩))

theorem hop_start_unique {x : ℕ → ℤ} {T p u u' : ℕ} (h : IsHop x T p u) (h' : IsHop x T p u') :
    u = u' := by
  rcases lt_trichotomy u u' with hlt | heq | hgt
  · exact absurd h.2.2.1 (h'.2.2.2 u (mem_Ioo.mpr ⟨by have := h.1; omega, hlt⟩))
  · exact heq
  · exact absurd h'.2.2.1 (h.2.2.2 u' (mem_Ioo.mpr ⟨by have := h'.1; omega, hgt⟩))

theorem hop_end_unique {x : ℕ → ℤ} {T p p' u : ℕ} (h : IsHop x T p u) (h' : IsHop x T p' u) :
    p = p' := by
  have hc : x p = x p' := by rw [← h.2.2.1, h'.2.2.1]
  exact (hop_unique h h' hc ⟨by have := h.1; omega, le_rfl⟩ ⟨by have := h'.1; omega, le_rfl⟩).1

section Strips

variable (x : ℕ → ℤ) (w : ℕ) (ρ : ℤ)

/-- The line cells are the cells `≡ ρ (mod w)`. -/
def IsLine (c : ℤ) : Prop := c % (w : ℤ) = ρ

instance (c : ℤ) : Decidable (IsLine w ρ c) := by unfold IsLine; infer_instance

/-- The strip of a cell: the number of lines below it. -/
def strip (c : ℤ) : ℤ := (c - ρ) / (w : ℤ)

/-- The visits to the strip of `x t` up to time `t`. -/
def stripCount (t : ℕ) : ℕ :=
  ((range (t + 1)).filter (fun s => ¬ IsLine w ρ (x s) ∧ strip w ρ (x s) = strip w ρ (x t))).card

end Strips

/-- Adjacent cells that are not lines lie in the same strip. -/
theorem strip_eq_of_adj {w : ℕ} (hw : 2 ≤ w) {ρ : ℤ} (hρ : 0 ≤ ρ ∧ ρ < w) {a b : ℤ}
    (hab : b = a + 1) (hb : ¬ IsLine w ρ b) : strip w ρ a = strip w ρ b := by
  unfold strip IsLine at *
  subst hab
  have hw0 : (0 : ℤ) < w := by omega
  have hwne : (w : ℤ) ≠ 0 := by omega
  have h1 := Int.emod_add_mul_ediv (a - ρ) w
  have h3 := Int.emod_nonneg (a - ρ) hwne
  have h4 := Int.emod_lt_of_pos (a - ρ) hw0
  rcases lt_or_eq_of_le (show (a - ρ) % w + 1 ≤ w by omega) with h | h
  · have e : a + 1 - ρ = ((a - ρ) % w + 1) + (a - ρ) / w * w := by linarith
    rw [e, Int.add_mul_ediv_right _ _ hwne, Int.ediv_eq_zero_of_lt (by omega) h, zero_add]
  · exfalso; apply hb
    have e : a + 1 = ρ + ((a - ρ) / w + 1) * w := by linarith
    rw [e, Int.add_mul_emod_self_right, Int.emod_eq_of_lt hρ.1 hρ.2]

/-- A counter that steps up by one at the marked times wraps modulo `r` between two marked times
along which its label does not increase. -/
theorem exists_wrap (V : ℕ → Prop) [DecidablePred V] {r ω p u : ℕ} (hr : 1 ≤ r) (hpu : p < u)
    (hVu : V u)
    (hle : (((range (u + 1)).filter V).card + ω) % r ≤ (((range (p + 1)).filter V).card + ω) % r) :
    ∃ τ, p < τ ∧ τ ≤ u ∧ V τ ∧ r ∣ ((range (τ + 1)).filter V).card + ω := by
  classical
  set g : ℕ → ℕ := fun t => ((range (t + 1)).filter V).card with hg
  have gstep : ∀ t, g (t + 1) = g t + if V (t + 1) then 1 else 0 := by
    intro t
    simp only [hg]
    rw [range_add_one, filter_insert]
    split_ifs with h
    · rw [card_insert_of_notMem (by simp)]
    · rfl
  have gmono : ∀ a b, a ≤ b → g a ≤ g b := by
    intro a b hab
    induction b, hab using Nat.le_induction with
    | base => exact le_rfl
    | succ b _ ih => rw [gstep]; split_ifs <;> omega
  have hpu' : g p + 1 ≤ g u := by
    have h1 := gmono p (u - 1) (by omega)
    have h2 := gstep (u - 1)
    rw [show u - 1 + 1 = u by omega] at h2
    simp only [hVu, ↓reduceIte] at h2
    omega
  -- a multiple of `r` lies in `(g p + ω, g u + ω]`
  set A := g p + ω
  set B := g u + ω
  have hA := Nat.div_add_mod A r
  have hB := Nat.div_add_mod B r
  have hAr := Nat.mod_lt A (show 0 < r by omega)
  have hBr := Nat.mod_lt B (show 0 < r by omega)
  have hq : A / r < B / r := by
    by_contra hcon
    have hle' : B / r ≤ A / r := by omega
    have hge : A / r ≤ B / r := Nat.div_le_div_right (by omega)
    have heq : A / r = B / r := le_antisymm hge hle'
    have : r * (A / r) = r * (B / r) := by rw [heq]
    omega
  set v := r * (A / r + 1) with hv
  have hvA : A < v := by rw [hv, mul_add, mul_one]; omega
  have hvB : v ≤ B := by
    have : r * (A / r + 1) ≤ r * (B / r) := Nat.mul_le_mul_left r hq
    omega
  -- the first time the counter reaches `v - ω`
  have hex : ∃ t, v - ω ≤ g t := ⟨u, by omega⟩
  set τ := Nat.find hex with hτ
  have hτspec : v - ω ≤ g τ := Nat.find_spec hex
  have hτu : τ ≤ u := Nat.find_min' hex (by omega)
  have hτp : p < τ := by
    by_contra hcon
    have := gmono τ p (by omega)
    omega
  have hprev : g (τ - 1) < v - ω := by
    have := Nat.find_min hex (show τ - 1 < τ by omega)
    omega
  have hstep := gstep (τ - 1)
  rw [show τ - 1 + 1 = τ by omega] at hstep
  have hVτ : V τ := by
    by_contra hcon
    simp only [hcon, ↓reduceIte] at hstep
    omega
  simp only [hVτ, ↓reduceIte] at hstep
  refine ⟨τ, hτp, hτu, hVτ, ?_⟩
  have : g τ + ω = v := by omega
  show r ∣ g τ + ω
  rw [this, hv]
  exact Dvd.intro _ rfl

section Cut

variable (x : ℕ → ℤ) (T w r : ℕ) (ρ : ℤ) (ω : ℕ)

/-- The strip label: the strip's visit count plus `ω`, modulo `r`. -/
def stripLabel (t : ℕ) : ℕ := (stripCount x w ρ t + ω) % r

/-- The line times. -/
def lineTimes : Finset ℕ := (range T).filter (fun t => IsLine w ρ (x t))

/-- The cut state edges `t → t - 1`: at a line time, or where the label increases along the
edge. -/
def cutStates : Finset ℕ :=
  (Ico 1 T).filter (fun t => IsLine w ρ (x t) ∨ IsLine w ρ (x (t - 1)) ∨
    stripLabel x w r ρ ω t < stripLabel x w r ρ ω (t - 1))

/-- The cut hops `u → p`: at a line cell, or where the label does not decrease along the edge. -/
def cutHops : Finset (ℕ × ℕ) :=
  (hops x T).filter (fun e => IsLine w ρ (x e.1) ∨ stripLabel x w r ρ ω e.2 ≤ stripLabel x w r ρ ω e.1)

/-- The wraps: visits to a strip at which the label is `0`. -/
def wraps : Finset ℕ :=
  (range T).filter (fun τ => ¬ IsLine w ρ (x τ) ∧ r ∣ stripCount x w ρ τ + ω)

end Cut

theorem stripCount_eq_filter (x : ℕ → ℤ) (w : ℕ) (ρ : ℤ) (S : ℤ) (t : ℕ)
    (ht : strip w ρ (x t) = S) :
    stripCount x w ρ t = ((range (t + 1)).filter (fun s => ¬ IsLine w ρ (x s) ∧ strip w ρ (x s) = S)).card := by
  unfold stripCount; rw [ht]

/-- A non-line cell is `ρ` plus `w` times its strip plus an offset in `[1, w)`. -/
theorem offset_spec {w : ℕ} (hw : 2 ≤ w) {ρ : ℤ} (hρ : 0 ≤ ρ ∧ ρ < w) {c : ℤ}
    (hc : ¬ IsLine w ρ c) :
    1 ≤ (c - ρ) % w ∧ (c - ρ) % w < w ∧ c = ρ + w * strip w ρ c + (c - ρ) % w := by
  have hw0 : (0 : ℤ) < w := by omega
  have hwne : (w : ℤ) ≠ 0 := by omega
  have h1 := Int.emod_add_mul_ediv (c - ρ) w
  have h3 := Int.emod_nonneg (c - ρ) hwne
  have h4 := Int.emod_lt_of_pos (c - ρ) hw0
  refine ⟨?_, h4, by unfold strip; linarith⟩
  by_contra h0
  apply hc
  unfold IsLine
  have e : c = ρ + (c - ρ) / w * w := by
    have : (c - ρ) % w = 0 := by omega
    linarith
  rw [e, Int.add_mul_emod_self_right, Int.emod_eq_of_lt hρ.1 hρ.2]

/-- **The state-edge bound.** -/
theorem card_cutStates_le {x : ℕ → ℤ} (hx : IsWalk x) {T w r : ℕ} (hw : 2 ≤ w) (hr : 1 ≤ r)
    {ρ : ℤ} (hρ : 0 ≤ ρ ∧ ρ < w) (ω : ℕ) :
    (cutStates x T w r ρ ω).card ≤ 2 * (lineTimes x T w ρ).card + (wraps x T w r ρ ω).card := by
  classical
  have hsub : cutStates x T w r ρ ω ⊆
      lineTimes x T w ρ ∪ ((lineTimes x T w ρ).image (· + 1) ∪ wraps x T w r ρ ω) := by
    intro t ht
    simp only [cutStates, mem_filter, mem_Ico] at ht
    obtain ⟨⟨ht1, ht2⟩, h⟩ := ht
    rcases h with h | h | h
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_range.mpr ht2, h⟩)
    · exact mem_union_right _ (mem_union_left _ (mem_image.mpr
        ⟨t - 1, mem_filter.mpr ⟨mem_range.mpr (by omega), h⟩, by omega⟩))
    · by_cases hl : IsLine w ρ (x t)
      · exact mem_union_left _ (mem_filter.mpr ⟨mem_range.mpr ht2, hl⟩)
      by_cases hl' : IsLine w ρ (x (t - 1))
      · exact mem_union_right _ (mem_union_left _ (mem_image.mpr
          ⟨t - 1, mem_filter.mpr ⟨mem_range.mpr (by omega), hl'⟩, by omega⟩))
      -- inside one strip the count steps up by one, so a label increase is a wrap
      apply mem_union_right; apply mem_union_right
      have hstep := hx.step (t - 1)
      rw [show t - 1 + 1 = t by omega] at hstep
      have hS : strip w ρ (x t) = strip w ρ (x (t - 1)) := by
        rcases (show x t = x (t - 1) ∨ x t = x (t - 1) + 1 ∨ x (t - 1) = x t + 1 by omega)
          with e | e | e
        · rw [e]
        · exact (strip_eq_of_adj hw hρ e hl).symm
        · exact strip_eq_of_adj hw hρ e hl'
      have hc : stripCount x w ρ t = stripCount x w ρ (t - 1) + 1 := by
        rw [stripCount_eq_filter x w ρ _ t rfl, stripCount_eq_filter x w ρ _ (t - 1) hS.symm]
        conv_lhs => rw [show t + 1 = (t - 1 + 1) + 1 by omega, range_add_one, filter_insert]
        simp only [show t - 1 + 1 = t by omega, hl, not_false_eq_true, true_and, ↓reduceIte]
        rw [card_insert_of_notMem (by simp)]
      refine mem_filter.mpr ⟨mem_range.mpr ht2, hl, ?_⟩
      simp only [stripLabel, hc] at h
      have h1 : (stripCount x w ρ (t - 1) + 1 + ω) % r =
          if r ≤ (stripCount x w ρ (t - 1) + ω) % r + 1 % r then
            (stripCount x w ρ (t - 1) + ω) % r + 1 % r - r
          else (stripCount x w ρ (t - 1) + ω) % r + 1 % r := by
        rw [show stripCount x w ρ (t - 1) + 1 + ω = (stripCount x w ρ (t - 1) + ω) + 1 by ring]
        exact Nat.add_mod_eq_ite
      have hlt := Nat.mod_lt (stripCount x w ρ (t - 1) + ω) (show 0 < r by omega)
      rw [hc]
      apply Nat.dvd_of_mod_eq_zero
      rw [show stripCount x w ρ (t - 1) + 1 + ω = (stripCount x w ρ (t - 1) + 1 + ω) by rfl]
      rcases Nat.lt_or_ge 1 r with hr1 | hr1
      · rw [Nat.mod_eq_of_lt hr1] at h1
        split_ifs at h1 <;> omega
      · have : r = 1 := by omega
        subst this
        exact Nat.mod_one _
  calc (cutStates x T w r ρ ω).card
      ≤ (lineTimes x T w ρ ∪ ((lineTimes x T w ρ).image (· + 1) ∪ wraps x T w r ρ ω)).card :=
        card_le_card hsub
    _ ≤ (lineTimes x T w ρ).card + ((lineTimes x T w ρ).image (· + 1)).card +
          (wraps x T w r ρ ω).card := by
        have := card_union_le (lineTimes x T w ρ) ((lineTimes x T w ρ).image (· + 1) ∪
          wraps x T w r ρ ω)
        have := card_union_le ((lineTimes x T w ρ).image (· + 1)) (wraps x T w r ρ ω)
        omega
    _ ≤ 2 * (lineTimes x T w ρ).card + (wraps x T w r ρ ω).card := by
        have := card_image_le (s := lineTimes x T w ρ) (f := (· + 1)); omega

/-- **The hop bound.** -/
theorem card_cutHops_le {x : ℕ → ℤ} {T w r : ℕ} (hw : 2 ≤ w) (hr : 1 ≤ r)
    {ρ : ℤ} (hρ : 0 ≤ ρ ∧ ρ < w) (ω : ℕ) :
    (cutHops x T w r ρ ω).card ≤ (lineTimes x T w ρ).card + (w - 1) * (wraps x T w r ρ ω).card := by
  classical
  have hsplit := card_filter_add_card_filter_not (s := cutHops x T w r ρ ω)
    (fun e => IsLine w ρ (x e.1))
  -- hops at a line cell: their start is a line time, and it determines the hop
  have hA : ((cutHops x T w r ρ ω).filter (fun e => IsLine w ρ (x e.1))).card ≤
      (lineTimes x T w ρ).card := by
    refine card_le_card_of_injOn (fun e => e.1) (fun e he => ?_) (fun e he e' he' h => ?_)
    · obtain ⟨he1, he2⟩ := mem_filter.mp he
      have hh := mem_hops.mp (mem_filter.mp he1).1
      exact mem_filter.mpr ⟨mem_range.mpr (show e.1 < T by have := hh.1; have := hh.2.1; omega), he2⟩
    · have hh := mem_hops.mp (mem_filter.mp (mem_filter.mp he).1).1
      have hh' := mem_hops.mp (mem_filter.mp (mem_filter.mp he').1).1
      simp only at h
      rw [← h] at hh'
      exact Prod.ext h (hop_start_unique hh hh')
  -- the other cut hops contain a wrap of their strip
  have hwrap : ∀ e ∈ (cutHops x T w r ρ ω).filter (fun e => ¬ IsLine w ρ (x e.1)),
      ∃ τ, e.1 < τ ∧ τ ≤ e.2 ∧ τ ∈ wraps x T w r ρ ω ∧ strip w ρ (x τ) = strip w ρ (x e.1) := by
    intro e he
    obtain ⟨he1, hnl⟩ := mem_filter.mp he
    obtain ⟨hhop, hlab⟩ := mem_filter.mp he1
    have hh := mem_hops.mp hhop
    have hlab' : stripLabel x w r ρ ω e.2 ≤ stripLabel x w r ρ ω e.1 := hlab.resolve_left hnl
    have hcu : x e.2 = x e.1 := hh.2.2.1
    obtain ⟨τ, hτ1, hτ2, hVτ, hdiv⟩ := exists_wrap
      (fun s => ¬ IsLine w ρ (x s) ∧ strip w ρ (x s) = strip w ρ (x e.1)) hr
      (show e.1 < e.2 by have := hh.1; omega) ⟨by rw [hcu]; exact hnl, by rw [hcu]⟩ (by
        unfold stripLabel at hlab'
        rwa [stripCount_eq_filter x w ρ (strip w ρ (x e.1)) e.2 (by rw [hcu]),
          stripCount_eq_filter x w ρ (strip w ρ (x e.1)) e.1 rfl] at hlab')
    refine ⟨τ, hτ1, hτ2, mem_filter.mpr ⟨mem_range.mpr (by have := hh.2.1; omega), hVτ.1, ?_⟩,
      hVτ.2⟩
    rwa [stripCount_eq_filter x w ρ _ τ hVτ.2]
  choose! τ hτ using hwrap
  have hB : ((cutHops x T w r ρ ω).filter (fun e => ¬ IsLine w ρ (x e.1))).card ≤
      (w - 1) * (wraps x T w r ρ ω).card := by
    -- the wrap and the offset of the cell in its strip determine the hop
    have := card_le_card_of_injOn (fun e => (τ e, ((x e.1 - ρ) % w).toNat))
      (s := (cutHops x T w r ρ ω).filter (fun e => ¬ IsLine w ρ (x e.1)))
      (t := (wraps x T w r ρ ω) ×ˢ Ico 1 w) (fun e he => by
        obtain ⟨-, hnl⟩ := mem_filter.mp he
        have ho := offset_spec hw hρ hnl
        have h0 : 0 ≤ (x e.1 - ρ) % w := by omega
        have hlt : ((x e.1 - ρ) % w).toNat < w := (Int.toNat_lt h0).mpr ho.2.1
        have hpos : 1 ≤ ((x e.1 - ρ) % w).toNat := by
          have h3 := Int.toNat_of_nonneg h0
          have h4 := ho.1
          rw [← h3] at h4
          exact_mod_cast h4
        exact mem_product.mpr ⟨(hτ e he).2.2.1, mem_Ico.mpr ⟨hpos, hlt⟩⟩)
      (fun e he e' he' h => by
        simp only [Prod.mk.injEq] at h
        obtain ⟨h1, h2⟩ := h
        obtain ⟨he1, hnl⟩ := mem_filter.mp he
        obtain ⟨he1', hnl'⟩ := mem_filter.mp he'
        have hh := mem_hops.mp (mem_filter.mp he1).1
        have hh' := mem_hops.mp (mem_filter.mp he1').1
        have ho := offset_spec hw hρ hnl
        have ho' := offset_spec hw hρ hnl'
        have hs : strip w ρ (x e.1) = strip w ρ (x e'.1) := by
          rw [← (hτ e he).2.2.2, ← (hτ e' he').2.2.2, h1]
        have hoff : (x e.1 - ρ) % w = (x e'.1 - ρ) % w := by
          rw [← Int.toNat_of_nonneg (show 0 ≤ (x e.1 - ρ) % w by omega),
            ← Int.toNat_of_nonneg (show 0 ≤ (x e'.1 - ρ) % w by omega), h2]
        have hcell : x e.1 = x e'.1 := by rw [ho.2.2, ho'.2.2, hs, hoff]
        have hspan' : e'.1 < τ e ∧ τ e ≤ e'.2 := by
          rw [h1]; exact ⟨(hτ e' he').1, (hτ e' he').2.1⟩
        obtain ⟨hp, hu⟩ := hop_unique hh hh' hcell ⟨(hτ e he).1, (hτ e he).2.1⟩ hspan'
        exact Prod.ext hp hu)
    rw [card_product, Nat.card_Ico] at this
    rw [mul_comm]; exact this
  omega

/-- A residue whose cells are visited at most `T / w` times. -/
theorem exists_line_residue (x : ℕ → ℤ) (T w : ℕ) (hw : 1 ≤ w) :
    ∃ ρ : ℤ, 0 ≤ ρ ∧ ρ < w ∧ w * (lineTimes x T w ρ).card ≤ T := by
  classical
  have hsum : ∑ ρ ∈ range w, (lineTimes x T w (ρ : ℤ)).card = T := by
    have hfib := card_eq_sum_card_fiberwise (f := fun t => ((x t) % (w : ℤ)).toNat) (s := range T)
      (t := range w) (fun t _ => by
        have h1 := Int.emod_lt_of_pos (x t) (show (0 : ℤ) < w by omega)
        have h2 := Int.emod_nonneg (x t) (show (w : ℤ) ≠ 0 by omega)
        exact mem_range.mpr ((Int.toNat_lt h2).mpr h1))
    rw [card_range] at hfib
    have key : ∀ ρ ∈ range w, (lineTimes x T w (ρ : ℤ)).card =
        ((range T).filter (fun t => ((x t) % (w : ℤ)).toNat = ρ)).card := by
      intro ρ _
      congr 1
      ext t
      have h2 := Int.emod_nonneg (x t) (show (w : ℤ) ≠ 0 by omega)
      rw [lineTimes, mem_filter, mem_filter, IsLine]
      constructor
      · rintro ⟨ht, h⟩; exact ⟨ht, by rw [h]; simp⟩
      · rintro ⟨ht, h⟩; exact ⟨ht, by rw [← h, Int.toNat_of_nonneg h2]⟩
    rw [sum_congr rfl key]
    exact hfib.symm
  obtain ⟨ρ, hρ, hle⟩ := exists_le_of_sum_le (nonempty_range_iff.mpr (by omega))
    (show ∑ ρ ∈ range w, w * (lineTimes x T w (ρ : ℤ)).card ≤ ∑ _ρ ∈ range w, T by
      rw [← mul_sum, hsum, sum_const, card_range, smul_eq_mul])
  exact ⟨ρ, by positivity, by have := mem_range.mp hρ; omega, hle⟩

/-- An offset with at most `T / r` wraps. -/
theorem exists_offset (x : ℕ → ℤ) (T w r : ℕ) (hr : 1 ≤ r) (ρ : ℤ) :
    ∃ ω < r, r * (wraps x T w r ρ ω).card ≤ T := by
  classical
  have hsum : ∑ ω ∈ range r, (wraps x T w r ρ ω).card ≤ T := by
    rw [← card_sigma]
    calc ((range r).sigma (fun ω => wraps x T w r ρ ω)).card ≤ (range T).card := by
          refine card_le_card_of_injOn (fun p => p.2) (fun p hp => ?_) (fun p hp q hq h => ?_)
          · exact (mem_filter.mp (mem_sigma.mp hp).2).1
          · obtain ⟨hp1, hp2⟩ := mem_sigma.mp hp
            obtain ⟨hq1, hq2⟩ := mem_sigma.mp hq
            simp only at h
            have d1 := (mem_filter.mp hp2).2.2
            have d2 := (mem_filter.mp hq2).2.2
            rw [h] at d1
            have hp1' := mem_range.mp hp1
            have hq1' := mem_range.mp hq1
            -- at most one offset in `[0, r)` makes a given count divisible by `r`
            have key : ∀ a b : ℕ, a < r → b < r → a ≤ b → r ∣ stripCount x w ρ q.2 + a →
                r ∣ stripCount x w ρ q.2 + b → a = b := by
              intro a b ha hb hab da db
              have hd := Nat.dvd_sub db da
              rw [Nat.add_sub_add_left] at hd
              have := Nat.eq_zero_of_dvd_of_lt hd (by omega)
              omega
            have he : p.1 = q.1 := by
              rcases le_total p.1 q.1 with hle | hle
              · exact key _ _ hp1' hq1' hle d1 d2
              · exact (key _ _ hq1' hp1' hle d2 d1).symm
            exact Sigma.ext he (heq_of_eq h)
      _ = T := card_range T
  obtain ⟨ω, hω, hle⟩ := exists_le_of_sum_le (nonempty_range_iff.mpr (by omega))
    (show ∑ ω ∈ range r, r * (wraps x T w r ρ ω).card ≤ ∑ _ω ∈ range r, T by
      rw [← mul_sum, sum_const, card_range, smul_eq_mul]
      exact Nat.mul_le_mul_left r hsum)
  exact ⟨ω, mem_range.mp hω, hle⟩

/-- **Lemma W (the strip cut for one walk).** For integers `w ≥ 2` and `r ≥ 1` there are a line
residue `ρ` and an offset `ω` whose cut has at most `4T/w + wT/r` edges. -/
theorem strip_cut {x : ℕ → ℤ} (hx : IsWalk x) (T w r : ℕ) (hw : 2 ≤ w) (hr : 1 ≤ r) :
    ∃ (ρ : ℤ) (ω : ℕ), 0 ≤ ρ ∧ ρ < w ∧ ω < r ∧
      w * r * ((cutStates x T w r ρ ω).card + (cutHops x T w r ρ ω).card) ≤
        4 * r * T + w * w * T := by
  obtain ⟨ρ, hρ0, hρw, hL⟩ := exists_line_residue x T w (by omega)
  obtain ⟨ω, hω, hW⟩ := exists_offset x T w r hr ρ
  refine ⟨ρ, ω, hρ0, hρw, hω, ?_⟩
  have h1 := card_cutStates_le (T := T) hx hw hr ⟨hρ0, hρw⟩ ω
  have h2 := card_cutHops_le (x := x) (T := T) hw hr ⟨hρ0, hρw⟩ ω
  set L := (lineTimes x T w ρ).card
  set W := (wraps x T w r ρ ω).card
  have hwW : (w - 1) * W + W = w * W := by
    rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega)]
  have hcut : (cutStates x T w r ρ ω).card + (cutHops x T w r ρ ω).card ≤ 3 * L + w * W := by
    omega
  calc w * r * ((cutStates x T w r ρ ω).card + (cutHops x T w r ρ ω).card)
      ≤ w * r * (3 * L + w * W) := Nat.mul_le_mul_left _ hcut
    _ = 3 * r * (w * L) + w * w * (r * W) := by ring
    _ ≤ 3 * r * T + w * w * T :=
        Nat.add_le_add (Nat.mul_le_mul_left _ hL) (Nat.mul_le_mul_left _ hW)
    _ ≤ 4 * r * T + w * w * T := by
        have : 3 * r * T ≤ 4 * r * T := Nat.mul_le_mul_right _ (by omega)
        omega

/-- **Depth of the strip cut.** A path `f 0, f 1, …, f n` of the walk DAG (state edges
`t → t - 1` and hop edges `u → p`) that avoids the cut carries at most `r − 1` hop edges. -/
theorem strip_cut_depth {x : ℕ → ℤ} {T w r : ℕ} (hr : 1 ≤ r) (ρ : ℤ) (ω : ℕ) (f : ℕ → ℕ)
    (n : ℕ)
    (hpath : ∀ i < n, (f (i + 1) + 1 = f i ∧ 1 ≤ f i ∧ f i < T ∧
        f i ∉ cutStates x T w r ρ ω) ∨
      ((f (i + 1), f i) ∈ hops x T ∧ (f (i + 1), f i) ∉ cutHops x T w r ρ ω)) :
    ((range n).filter (fun i => (f (i + 1), f i) ∈ hops x T)).card ≤ r - 1 := by
  classical
  refine depth_le_of_label (stripLabel x w r ρ ω) (fun a => Nat.mod_lt _ (by omega)) f n _
    (fun i hi => ?_) (fun i hi hm => ?_)
  · rcases hpath i hi with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2⟩
    · simp only [cutStates, mem_filter, mem_Ico, not_and, not_or, not_lt] at h4
      have := (h4 ⟨h2, h3⟩).2.2
      rw [show f (i + 1) = f i - 1 by omega]
      exact this
    · simp only [cutHops, mem_filter, not_and, not_or, not_le] at h2
      exact (h2 h1).2.le
  · rcases hpath i hi with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2⟩
    · have := (mem_hops.mp hm).1; simp only at this; omega
    · simp only [cutHops, mem_filter, not_and, not_or, not_le] at h2
      exact (h2 h1).2

end BoundedNesting
