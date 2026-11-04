import BoundedStackDepth.Basic

/-!
# The random grid

The grid of width `h₀ ≥ 1` with offset `r < h₀` groups bands: `grp h₀ r b = ⌊(b + r)/h₀⌋`, with floors
`flr h₀ r g = h₀ g − r`. The offset is uniform on `[0, h₀)`. Every probability bound the paper needs is an
upper bound on a number of offsets, and all of them follow from one fact: **an integer `θ` is a grid floor
for at most one offset** (`card_dvd_add_le_one`).

* `flr_grp_le`, `lt_flr_grp_succ`: `flr (grp b) ≤ b < flr (grp b + 1)`.
* `exists_floor_of_grp_lt`: if the group of `a` is below that of `b`, a grid floor lies in `(a, b]`.
* `card_grp_ne_le`: **the group of a band changes between `a` and `b` for at most `b − a` offsets.**
  This is the per-hop "spread" bound.
* `card_one_le_grp_le`: `grp s ≥ 1` for at most `s` offsets (lost hops need a positive group).
* `card_flr_grp_succ_le`: the next floor above `b` is at most `c` for at most `c − b` offsets (the
  home-near deficit).
* `card_lt_flr_grp_le`: the floor of the group of `β` exceeds `s` for at most `β − s` offsets
  (the eventfulness term).
* `sum_two_pow_flr_grp_le`: summed over the offsets whose floor below `s` is a grid floor `≥ 1`, the weights
  `2 ^ floor` total at most `2^{s+1}` (the event budgets).
-/

namespace BoundedStackDepth

open Finset

variable {h₀ : ℕ}

theorem flr_grp_le (h₀ r b : ℕ) : flr h₀ r (grp h₀ r b) ≤ b := by
  unfold flr grp
  have h := Nat.div_mul_le_self (b + r) h₀
  rw [Nat.mul_comm] at h
  omega

theorem lt_flr_grp_succ (hh : 0 < h₀) (r b : ℕ) : b < flr h₀ r (grp h₀ r b + 1) := by
  unfold flr grp
  have h := Nat.lt_div_mul_add (a := b + r) hh
  rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm]
  omega

/-- The group of the band `0` is `0`. -/
theorem grp_zero {r : ℕ} (hr : r < h₀) : grp h₀ r 0 = 0 := by
  unfold grp; simp [Nat.div_eq_of_lt hr]

theorem grp_mono (h₀ r : ℕ) {a b : ℕ} (hab : a ≤ b) : grp h₀ r a ≤ grp h₀ r b :=
  Nat.div_le_div_right (by omega)

/-- **An integer is a grid floor for at most one offset.** -/
theorem card_dvd_add_le_one (θ : ℕ) : ((range h₀).filter (fun r => h₀ ∣ θ + r)).card ≤ 1 := by
  refine card_le_one.mpr fun r hr r' hr' => ?_
  simp only [mem_filter, mem_range] at hr hr'
  have h1 : θ + r ≡ θ + r' [MOD h₀] :=
    (Nat.modEq_zero_iff_dvd.mpr hr.2).trans (Nat.modEq_zero_iff_dvd.mpr hr'.2).symm
  exact (Nat.ModEq.add_left_cancel' θ h1).eq_of_lt_of_lt hr.1 hr'.1

/-- If the group of `a` is below the group of `b`, some `θ ∈ (a, b]` is a grid floor: `h₀ ∣ θ + r`. -/
theorem exists_floor_of_grp_lt {r a b : ℕ} (h : grp h₀ r a < grp h₀ r b) :
    ∃ θ ∈ Ioc a b, h₀ ∣ θ + r := by
  have hh : 0 < h₀ := Nat.pos_of_ne_zero fun h0 => by simp [grp, h0] at h
  unfold grp at h
  set g := (b + r) / h₀ with hg
  have hle : g * h₀ ≤ b + r := Nat.div_mul_le_self _ _
  have hlt : a + r < (a + r) / h₀ * h₀ + h₀ := Nat.lt_div_mul_add hh
  have hmono : ((a + r) / h₀ + 1) * h₀ ≤ g * h₀ := Nat.mul_le_mul_right _ h
  rw [Nat.add_mul, Nat.one_mul] at hmono
  refine ⟨g * h₀ - r, mem_Ioc.mpr ⟨by omega, by omega⟩, ?_⟩
  rw [Nat.sub_add_cancel (by omega)]
  exact Dvd.intro_left g rfl

/-- **The group of a band changes between `a ≤ b` for at most `b − a` offsets.** -/
theorem card_grp_ne_le {a b : ℕ} (hab : a ≤ b) :
    ((range h₀).filter (fun r => grp h₀ r a ≠ grp h₀ r b)).card ≤ b - a := by
  calc ((range h₀).filter (fun r => grp h₀ r a ≠ grp h₀ r b)).card
      ≤ ((Ioc a b).biUnion fun θ => (range h₀).filter (fun r => h₀ ∣ θ + r)).card := by
        refine card_le_card fun r hr => ?_
        simp only [mem_filter, mem_range] at hr
        have hlt : grp h₀ r a < grp h₀ r b := lt_of_le_of_ne (grp_mono h₀ r hab) hr.2
        obtain ⟨θ, hθ, hd⟩ := exists_floor_of_grp_lt hlt
        exact mem_biUnion.mpr ⟨θ, hθ, mem_filter.mpr ⟨mem_range.mpr hr.1, hd⟩⟩
    _ ≤ ∑ θ ∈ Ioc a b, ((range h₀).filter (fun r => h₀ ∣ θ + r)).card := card_biUnion_le
    _ ≤ ∑ _θ ∈ Ioc a b, 1 := sum_le_sum fun θ _ => card_dvd_add_le_one θ
    _ = b - a := by simp

/-- The group of `s` is positive for at most `s` offsets. -/
theorem card_one_le_grp_le (s : ℕ) :
    ((range h₀).filter (fun r => 1 ≤ grp h₀ r s)).card ≤ s := by
  calc ((range h₀).filter (fun r => 1 ≤ grp h₀ r s)).card
      ≤ ((range h₀).filter (fun r => grp h₀ r 0 ≠ grp h₀ r s)).card := by
        refine card_le_card fun r hr => ?_
        simp only [mem_filter, mem_range] at hr ⊢
        refine ⟨hr.1, ?_⟩
        have := grp_zero hr.1
        omega
    _ ≤ s - 0 := card_grp_ne_le (Nat.zero_le s)
    _ = s := Nat.sub_zero s

/-- The next floor above `b` is at most `c` for at most `c − b` offsets. -/
theorem card_flr_grp_succ_le (b c : ℕ) :
    ((range h₀).filter (fun r => flr h₀ r (grp h₀ r b + 1) ≤ c)).card ≤ c - b := by
  rcases Nat.lt_or_ge c b with hcb | hbc
  · have : (range h₀).filter (fun r => flr h₀ r (grp h₀ r b + 1) ≤ c) = ∅ := by
      refine filter_eq_empty_iff.mpr fun r hr0 hr => ?_
      have hh : 0 < h₀ := by have := mem_range.mp hr0; omega
      have := lt_flr_grp_succ hh r b
      omega
    simp [this]
  · calc ((range h₀).filter (fun r => flr h₀ r (grp h₀ r b + 1) ≤ c)).card
        ≤ ((range h₀).filter (fun r => grp h₀ r b ≠ grp h₀ r c)).card := by
          refine card_le_card fun r hr => ?_
          simp only [mem_filter, mem_range] at hr ⊢
          refine ⟨hr.1, ?_⟩
          have hc : h₀ * (grp h₀ r b + 1) ≤ c + r := by unfold flr at hr; omega
          have : grp h₀ r b + 1 ≤ grp h₀ r c := by
            unfold grp at hc ⊢
            exact (Nat.le_div_iff_mul_le (by omega)).mpr (by rw [Nat.mul_comm]; exact hc)
          omega
      _ ≤ c - b := card_grp_ne_le hbc

/-- The floor of the group of `β` exceeds `s` for at most `β − s` offsets. -/
theorem card_lt_flr_grp_le (s β : ℕ) :
    ((range h₀).filter (fun r => s < flr h₀ r (grp h₀ r β))).card ≤ β - s := by
  rcases Nat.lt_or_ge β s with hβs | hsβ
  · have : (range h₀).filter (fun r => s < flr h₀ r (grp h₀ r β)) = ∅ := by
      refine filter_eq_empty_iff.mpr fun r _ hr => ?_
      have := flr_grp_le h₀ r β
      omega
    simp [this]
  · calc ((range h₀).filter (fun r => s < flr h₀ r (grp h₀ r β))).card
        ≤ ((range h₀).filter (fun r => grp h₀ r s ≠ grp h₀ r β)).card := by
          refine card_le_card fun r hr => ?_
          simp only [mem_filter, mem_range] at hr ⊢
          refine ⟨hr.1, ?_⟩
          have h1 : s + r < h₀ * grp h₀ r β := by unfold flr at hr; omega
          have h2 : grp h₀ r s < grp h₀ r β := by
            unfold grp at h1 ⊢
            exact (Nat.div_lt_iff_lt_mul (by omega)).mpr (by rw [Nat.mul_comm]; exact h1)
          omega
      _ ≤ β - s := card_grp_ne_le hsβ

/-- `∑_{i<n} 2^i < 2^n`. -/
theorem sum_range_two_pow_lt (n : ℕ) : ∑ i ∈ range n, 2 ^ i < 2 ^ n :=
  Nat.geomSum_lt le_rfl fun _ => mem_range.mp

/-- Distinct offsets give distinct positive floors below `s`. -/
theorem flr_grp_injOn (s : ℕ) :
    Set.InjOn (fun r => flr h₀ r (grp h₀ r s))
      ((range h₀).filter (fun r => 1 ≤ flr h₀ r (grp h₀ r s)) : Set ℕ) := by
  intro r hr r' hr' heq
  simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hr hr'
  simp only [flr] at heq hr hr'
  set g := grp h₀ r s
  set g' := grp h₀ r' s
  -- h₀ g − r = h₀ g' − r' with both positive, so h₀ (g − g') = r − r' with |r − r'| < h₀
  rcases lt_trichotomy g g' with hlt | heqg | hgt
  · have : h₀ * g + h₀ ≤ h₀ * g' := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hlt
    omega
  · rw [heqg] at heq; omega
  · have : h₀ * g' + h₀ ≤ h₀ * g := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hgt
    omega

/-- **Event budget.** Over the offsets whose floor below `s` is a grid floor `≥ 1`, the weights
`2 ^ floor` total at most `2^{s+1}`. -/
theorem sum_two_pow_flr_grp_le (s : ℕ) :
    ∑ r ∈ (range h₀).filter (fun r => 1 ≤ flr h₀ r (grp h₀ r s)), 2 ^ flr h₀ r (grp h₀ r s)
      ≤ 2 ^ (s + 1) := by
  set S := (range h₀).filter (fun r => 1 ≤ flr h₀ r (grp h₀ r s))
  rw [← sum_image (flr_grp_injOn (h₀ := h₀) s)]
  calc ∑ θ ∈ S.image (fun r => flr h₀ r (grp h₀ r s)), 2 ^ θ
      ≤ ∑ θ ∈ range (s + 1), 2 ^ θ := by
        refine sum_le_sum_of_subset fun θ hθ => ?_
        obtain ⟨r, -, rfl⟩ := mem_image.mp hθ
        exact mem_range.mpr (Nat.lt_succ_of_le (flr_grp_le h₀ r s))
    _ ≤ 2 ^ (s + 1) := (sum_range_two_pow_lt (s + 1)).le

end BoundedStackDepth
