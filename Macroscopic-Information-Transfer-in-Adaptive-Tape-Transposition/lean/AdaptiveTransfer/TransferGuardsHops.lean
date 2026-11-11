import AdaptiveTransfer.TransferBandPaths

/-! Finite guards for actual consecutive work visits. Monotonicity of the
projection clock makes each (cut time, head, nearby cell) charge at most one
straddling original hop. No input-revisit dependency edges are added. -/
namespace AdaptiveTransfer.TransferGuards
open Finset BoundedNesting MergeDepth
open scoped BigOperators

noncomputable def straddlingHops {k : ℕ} (xs ys : Fin k → ℕ → ℤ)
    (q : ℕ → ℕ) (U R b : ℕ) : Finset (Fin k × ℕ × ℕ) := by
  classical
  exact (allHops ys U).filter fun e => q e.2.1 < b ∧ b < q e.2.2 ∧
    |ys e.1 e.2.2 - xs e.1 b| ≤ R

noncomputable def hopGuard {k : ℕ} (xs ys : Fin k → ℕ → ℤ)
    (q : ℕ → ℕ) (U R : ℕ) (B : Finset ℕ) : Finset ℕ :=
  B.biUnion fun b => (straddlingHops xs ys q U R b).image fun e => e.2.2

/-- Two consecutive visits to one cell cannot both strictly straddle the
same projected source time under a nondecreasing clock. -/
theorem straddling_hop_injective {k U R b : ℕ} {xs ys : Fin k → ℕ → ℤ}
    {q : ℕ → ℕ} (hq : Monotone q) :
    Set.InjOn (fun e : Fin k × ℕ × ℕ => (e.1, ys e.1 e.2.2))
      (straddlingHops xs ys q U R b) := by
  intro e he e' he' hcode
  rcases e with ⟨h, p, u⟩
  rcases e' with ⟨h', p', u'⟩
  obtain ⟨hh, hc⟩ := Prod.mk.inj hcode
  dsimp only at hh hc
  subst h'
  obtain ⟨he, hp, hu, _⟩ := mem_filter.mp he
  obtain ⟨he', hp', hu', _⟩ := mem_filter.mp he'
  change q p < b at hp
  change b < q u at hu
  change q p' < b at hp'
  change b < q u' at hu'
  have hop : IsHop (ys h) U p u := mem_allHops.mp he
  have hop' : IsHop (ys h) U p' u' := mem_allHops.mp he'
  have hpu' : p < u' := by
    by_contra hn
    have hh := hq (show u' ≤ p by omega)
    omega
  have hp'u : p' < u := by
    by_contra hn
    have hh := hq (show u ≤ p' by omega)
    omega
  have hcell : ys h p = ys h p' := by rw [← hop.2.2.1, ← hop'.2.2.1]; exact hc
  obtain ⟨hep, heu⟩ := hop_unique hop hop' hcell
    (τ := max p p' + 1) ⟨by omega, by have := hop.1; omega⟩
    ⟨by omega, by have := hop'.1; omega⟩
  exact Prod.ext rfl (Prod.ext hep heu)

theorem straddlingHops_card_le {k U R b : ℕ} {xs ys : Fin k → ℕ → ℤ}
    {q : ℕ → ℕ} (hq : Monotone q) :
    (straddlingHops xs ys q U R b).card ≤ k * (2 * R + 1) := by
  classical
  let cells := univ.biUnion fun h : Fin k =>
    (Icc (xs h b - R) (xs h b + R)).image fun z => (h, z)
  have hcode : ∀ e ∈ straddlingHops xs ys q U R b, (e.1, ys e.1 e.2.2) ∈ cells := by
    intro e he
    have hh := abs_le.mp (mem_filter.mp he).2.2.2
    exact mem_biUnion.mpr ⟨e.1, mem_univ _, mem_image.mpr
      ⟨ys e.1 e.2.2, mem_Icc.mpr ⟨by omega, by omega⟩, rfl⟩⟩
  calc
    _ ≤ cells.card := card_le_card_of_injOn _ hcode (straddling_hop_injective hq)
    _ ≤ ∑ h : Fin k, ((Icc (xs h b - R) (xs h b + R)).image fun z => (h, z)).card := card_biUnion_le
    _ ≤ ∑ _h : Fin k, (2 * R + 1) := by
      apply sum_le_sum
      intro h _
      apply card_image_le.trans
      rw [Int.card_Icc]
      omega
    _ = _ := by simp

theorem hopGuard_card_le {k U R : ℕ} (xs ys : Fin k → ℕ → ℤ)
    {q : ℕ → ℕ} (hq : Monotone q) (B : Finset ℕ) :
    (hopGuard xs ys q U R B).card ≤ k * (2 * R + 1) * B.card := by
  classical
  unfold hopGuard
  calc
    _ ≤ ∑ b ∈ B, ((straddlingHops xs ys q U R b).image fun e => e.2.2).card := card_biUnion_le
    _ ≤ ∑ _b ∈ B, k * (2 * R + 1) :=
      sum_le_sum fun _b _ => card_image_le.trans (straddlingHops_card_le hq)
    _ = _ := by simp [Nat.mul_comm]

theorem mem_hopGuard {k U R b p u : ℕ} {xs ys : Fin k → ℕ → ℤ}
    {q : ℕ → ℕ} {B : Finset ℕ} (h : Fin k) (hh : IsHop (ys h) U p u)
    (hb : b ∈ B) (hp : q p < b) (hu : b < q u) (hcell : |ys h u - xs h b| ≤ R) :
    u ∈ hopGuard xs ys q U R B := by
  classical
  exact mem_biUnion.mpr ⟨b, hb, mem_image.mpr ⟨(h, p, u),
    mem_filter.mpr ⟨mem_allHops.mpr hh, hp, hu, hcell⟩, rfl⟩⟩

theorem hopGuard_time {k U R u : ℕ} {xs ys : Fin k → ℕ → ℤ}
    {q : ℕ → ℕ} {B : Finset ℕ} (hu : u ∈ hopGuard xs ys q U R B) : u < U := by
  obtain ⟨b, _, hu⟩ := mem_biUnion.mp hu
  obtain ⟨e, he, rfl⟩ := mem_image.mp hu
  exact (mem_allHops.mp (mem_filter.mp he).1).2.1

end AdaptiveTransfer.TransferGuards
