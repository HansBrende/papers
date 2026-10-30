import MergeDepth.HopRouting
import MergeDepth.SkeletonPaired

/-!
# Proposition 3.16 with the count of Lemma 3.14(a)

`hop_routing_count`: Proposition 3.16(b) with the number of exceptional positions bounded by
Lemma 3.14(a) (`ball_self_demands`). A position `ℓ` is exceptional when `tpos ℓ` lies in the ball of
radius `D''` around its output step; through the involution `tpos` these positions correspond to
the self-demands of the relation `q ↦ B^{D''}(tpos q)` (`card_exceptional_eq`).
-/

namespace MergeDepth

open Finset BoundedNesting DirectedRecovery

variable {k : ℕ}

/-- The transposition of positions as a map of `Fin (d²b)`. -/
def tposF (d b : ℕ) (hb : 0 < b) (q : Fin (d * d * b)) : Fin (d * d * b) :=
  ⟨tpos d b q, tpos_lt hb q.2⟩

theorem tposF_tposF {d b : ℕ} (hb : 0 < b) (q : Fin (d * d * b)) :
    tposF d b hb (tposF d b hb q) = q :=
  Fin.ext (tpos_tpos hb q.2)

open Classical in
/-- The exceptional positions of Proposition 3.16 are, through `tpos`, the self-demands of the
relation `q ↦ B^{D''}(tpos q)`. -/
theorem card_exceptional_eq {d b : ℕ} (hb : 0 < b) (xs : Fin k → ℕ → ℤ) (T : ℕ)
    (rdStep : ℕ → Option (Fin (d * d * b))) (D'' : ℕ) (tout : ℕ → ℕ) :
    ((univ : Finset (Fin (d * d * b))).filter fun ℓ : Fin (d * d * b) =>
        tposF d b hb ℓ ∈ stepBall xs T rdStep D'' (tout (ℓ : ℕ))).card =
      (selfDemandCoordinates fun q : Fin (d * d * b) =>
        stepBall xs T rdStep D'' (tout (tpos d b q))).card := by
  refine card_bij (fun ℓ _ => tposF d b hb ℓ) (fun ℓ hℓ => ?_) (fun ℓ _ ℓ' _ h => ?_)
    (fun p hp => ?_)
  · have hℓ' := (mem_filter.mp hℓ).2
    simp only [selfDemandCoordinates, mem_filter, mem_univ, true_and]
    have : tpos d b (tposF d b hb ℓ) = ℓ := tpos_tpos hb ℓ.2
    rwa [this]
  · have := congrArg (tposF d b hb) h
    rwa [tposF_tposF, tposF_tposF] at this
  · simp only [selfDemandCoordinates, mem_filter, mem_univ, true_and] at hp
    refine ⟨tposF d b hb p, mem_filter.mpr ⟨mem_univ _, ?_⟩, tposF_tposF hb p⟩
    rw [tposF_tposF]
    exact hp

open Classical in
/-- **Proposition 3.16(b)** with the count of Lemma 3.14(a). For a machine at dimension `d ≥ 2`
given by its head walks `z` (the input head reads the position under it, and output position `r`
is appended at a step `tout r` after which the output count is `r`), a cold genie of depth
`D ≥ 1`, `D ≤ D''` and `T ≤ c (L + 1)`: weights on `Γ_F`-free dependency paths from the output
steps to steps that read the transposed positions, with total at most one per position and load at
most `c₀` on every deep edge, have total at most `(2 c K'' (k + 2)(k + 3) + 3) L / log₂ d + c₀ N_R / h`,
where `K'' = ∑_{i ≤ D''} (k + 1)^i`, `h = ⌈(D'' + 2 - D)/D⌉` and `N_R ≤ k T` counts the deep hops. -/
theorem hop_routing_count {d b : ℕ} (hd : 2 ≤ d) (hb : 1 ≤ b) {z : Tp k → ℕ → ℤ}
    (hz : ∀ c, IsWalk (z c)) {T V β : ℕ} {ε : ℝ} {D : ℕ} {ΓF : Finset ℕ}
    (hcold : IsColdGenie (L := d * d * b) (fun j => z (some (some j))) T V β ε D ΓF)
    (hD : 1 ≤ D) (rdStep : ℕ → Option (Fin (d * d * b)))
    (hrd : ∀ u j, rdStep u = some j → z none u = j) (tout : ℕ → ℕ)
    (htout : ∀ q : Fin (d * d * b),
      tout (tpos d b q) < T ∧ z (some none) (tout (tpos d b q)) = tpos d b q)
    {c : ℝ} (hc : 0 ≤ c) (hT : (T : ℝ) ≤ c * (d * d * b + 1)) (D'' : ℕ) (hD'' : D ≤ D'')
    (P : Fin (d * d * b) → Finset (List ℕ))
    (hP : ∀ ℓ, ∀ π ∈ P ℓ, ∃ π', π = tout ℓ :: π' ∧
      IsDepPath (fun j => z (some (some j))) T π ∧ LinNet.GFree ΓF π ∧
      rdStep (π.getLastD (tout ℓ)) = some (tposF d b hb ℓ))
    (f : Fin (d * d * b) → List ℕ → ℝ) (hf0 : ∀ ℓ π, 0 ≤ f ℓ π)
    (hf1 : ∀ ℓ, ∑ π ∈ P ℓ, f ℓ π ≤ 1) (c₀ : ℝ) (hc₀ : 0 ≤ c₀)
    (hload : ∀ a b', DeepStep (fun j => z (some (some j))) T V a b' →
      ∑ ℓ, ∑ π ∈ (P ℓ).filter ((a, b') ∈ edgesOf ·), f ℓ π ≤ c₀) :
    ∑ ℓ, ∑ π ∈ P ℓ, f ℓ π ≤
        (2 * c * (∑ i ∈ range (D'' + 1), (k + 1) ^ i : ℕ) * (k + 2 : ℕ) * ((k + 2 : ℕ) + 1) + 3) *
          ((d : ℝ) ^ 2 * b) / Real.logb 2 d +
        c₀ * (deepHops (fun j => z (some (some j))) T V).card / ⌈((D'' + 2 - D : ℕ) : ℝ) / D⌉₊ ∧
      (deepHops (fun j => z (some (some j))) T V).card ≤ k * T := by
  obtain ⟨hmain, hN⟩ := hop_routing_b (fun j => z (some (some j))) hcold hD rdStep D'' hD''
    (fun ℓ => tout ℓ) (tposF d b hb) P hP f hf0 hf1 c₀ hc₀ hload
  refine ⟨hmain.trans ?_, hN⟩
  have hcount := ball_self_demands hd hb hz rdStep hrd tout htout
    (fun q => stepBall (fun j => z (some (some j))) T rdStep D'' (tout (tpos d b q)))
    (fun q => subset_refl _) hc hT
  rw [← card_exceptional_eq (Nat.lt_of_lt_of_le Nat.zero_lt_one hb)] at hcount
  linarith

end MergeDepth
