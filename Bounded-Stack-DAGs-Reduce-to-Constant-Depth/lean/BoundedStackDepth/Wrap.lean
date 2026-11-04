import BoundedStackDepth.Grid

/-!
# WRAP: the exchange of sums (generic part)

The wraps of a hop are paid by the events inside it: a digit of group `g` wraps only if events of scale
`≥ θ(g)` occur between the hop's ends. Summed over hops, this is exchanged into a sum over events
(`sum_hops_events_le`): each event `a`, of time `τ a` and scale `σ a`, pays for the hops spanning it,
once for every group `g` with `θ(g) ≤ σ a` (`flr_le_iff`, so `g ≤ G(σ a)`).

* `sum_two_pow_flr_succ_le`: the floors `θ(g + 1)`, `g ≤ G`, are distinct, so their powers of two sum to
  less than `2^{θ(G + 1) + 1}`;
* `flr_grp_succ_le`: `θ(G(s) + 1) ≤ s + h₀`.
-/

namespace BoundedStackDepth

open Finset

variable {h₀ : ℕ}

/-- `θ(g) ≤ s` iff `g ≤ G(s)`. -/
theorem flr_le_iff (hh : 0 < h₀) (r g s : ℕ) : flr h₀ r g ≤ s ↔ g ≤ grp h₀ r s := by
  unfold flr grp
  rw [Nat.le_div_iff_mul_le hh, Nat.mul_comm g h₀]
  omega

/-- The floor above `G(s)` is at most `s + h₀`. -/
theorem flr_grp_succ_le (r s : ℕ) :
    flr h₀ r (grp h₀ r s + 1) ≤ s + h₀ := by
  have h1 := flr_grp_le h₀ r s
  unfold flr at h1 ⊢
  rw [Nat.mul_succ]
  omega

/-- The floors `θ(g + 1)`, `g ≤ G`, are distinct, so their powers of two sum to less than
`2^{θ(G+1) + 1}`. -/
theorem sum_two_pow_flr_succ_le {r : ℕ} (hr : r < h₀) (G : ℕ) :
    ∑ g ∈ range (G + 1), 2 ^ flr h₀ r (g + 1) < 2 ^ (flr h₀ r (G + 1) + 1) := by
  have hh : 0 < h₀ := by omega
  have hinj : Set.InjOn (fun g => flr h₀ r (g + 1)) (range (G + 1) : Set ℕ) := by
    intro a _ b _ h
    simp only [flr] at h
    have : h₀ * (a + 1) = h₀ * (b + 1) := by
      have h1 : r ≤ h₀ * (a + 1) := by nlinarith
      have h2 : r ≤ h₀ * (b + 1) := by nlinarith
      omega
    have := Nat.eq_of_mul_eq_mul_left hh this
    omega
  calc ∑ g ∈ range (G + 1), 2 ^ flr h₀ r (g + 1)
      = ∑ i ∈ (range (G + 1)).image (fun g => flr h₀ r (g + 1)), 2 ^ i :=
        (sum_image (f := fun i => 2 ^ i) hinj).symm
    _ ≤ ∑ i ∈ range (flr h₀ r (G + 1) + 1), 2 ^ i := by
        refine sum_le_sum_of_subset fun i hi => ?_
        obtain ⟨g, hg, rfl⟩ := mem_image.mp hi
        refine mem_range.mpr (Nat.lt_succ_of_le ?_)
        unfold flr
        have := mem_range.mp hg
        have : h₀ * (g + 1) ≤ h₀ * (G + 1) := Nat.mul_le_mul_left _ (by omega)
        omega
    _ < 2 ^ (flr h₀ r (G + 1) + 1) := sum_range_two_pow_lt _

/-- **The exchange of sums, per event.** If each hop `e` sums over a set `B e` of groups `≥ d e`, and
`θ g ≤ s` forces `g ≤ G s`, then summing over hops and groups the events in `(p e, u e]` of scale `≥ θ g` is
at most summing over events and groups `g ≤ G(σ a)` the hops spanning the event with `d e ≤ g`. -/
theorem sum_hops_events_le {α β : Type*} (A : Finset α) (τ σ : α → ℕ) (H : Finset β)
    (p u d : β → ℕ) (B : β → Finset ℕ) (θ G : ℕ → ℕ) (hB : ∀ e, ∀ g ∈ B e, d e ≤ g)
    (hθ : ∀ g s, θ g ≤ s → g ≤ G s) :
    ∑ e ∈ H, ∑ g ∈ B e, (A.filter fun a => p e < τ a ∧ τ a ≤ u e ∧ θ g ≤ σ a).card ≤
      ∑ a ∈ A, ∑ g ∈ range (G (σ a) + 1),
        (H.filter fun e => p e < τ a ∧ τ a ≤ u e ∧ d e ≤ g).card := by
  classical
  calc ∑ e ∈ H, ∑ g ∈ B e, (A.filter fun a => p e < τ a ∧ τ a ≤ u e ∧ θ g ≤ σ a).card
      = ∑ e ∈ H, ∑ a ∈ A, ∑ g ∈ B e,
          if p e < τ a ∧ τ a ≤ u e ∧ θ g ≤ σ a then (1 : ℕ) else 0 := by
        refine sum_congr rfl fun e _ => ?_
        rw [sum_comm]
        exact sum_congr rfl fun g _ => by rw [card_eq_sum_ones, sum_filter]
    _ ≤ ∑ e ∈ H, ∑ a ∈ A, ∑ g ∈ range (G (σ a) + 1),
          if p e < τ a ∧ τ a ≤ u e ∧ d e ≤ g then (1 : ℕ) else 0 := by
        refine sum_le_sum fun e _ => sum_le_sum fun a _ => ?_
        rw [← sum_filter, ← sum_filter, ← card_eq_sum_ones, ← card_eq_sum_ones]
        refine card_le_card fun g hg => ?_
        obtain ⟨hgB, h1, h2, h3⟩ := mem_filter.mp hg
        exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le (hθ g _ h3)), h1, h2, hB e g hgB⟩
    _ = ∑ a ∈ A, ∑ g ∈ range (G (σ a) + 1),
          (H.filter fun e => p e < τ a ∧ τ a ≤ u e ∧ d e ≤ g).card := by
        rw [sum_comm]
        refine sum_congr rfl fun a _ => ?_
        rw [sum_comm]
        exact sum_congr rfl fun g _ => by rw [card_eq_sum_ones, sum_filter]

end BoundedStackDepth
