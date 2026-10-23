import Mathlib

/-!
# Depth labels: the cost identity and labels exact on one head

A *depth label* assigns to each time `t` of a cyclic schedule a value
`G t ∈ {0, …, q − 1}`. A hop `(p, u)` (from a visit of a cell to the next visit
of the same cell by the same head) is violated when `G u ≤ G p`. A descent is a
time `t` with `G t < G (tprev t)`. The cost of a label counts violated hops and
descents.

* **Lemma Zq** (`lemma_Zq`): `q · cost = #hops + Σ_h e_h + Σ_t x_t`, where
  `e_h = (G u − G p − 1) mod q` and `x_t = (G t − G (tprev t)) mod q`. It needs
  only that each head's hops form chains closed into cycles.
* **Theorem E** (`cost_ge_of_negative_cycles`, abstract form): if `G` is exact
  on head 1 (equal to the visit index `κ` modulo `q` up to a function of the
  cell), then around every cycle of head-2 hops through interior head-1 cells
  the errors sum to the defect `δ` modulo `q`. A family of hop-disjoint cycles
  with `δ < 0` therefore forces `q · cost ≥ #hops + Σ_C (q + δ(C))`.
-/

namespace MotionDepthCodes

open Finset
open scoped BigOperators
set_option autoImplicit false

/-- For `−q ≤ y < q`, `y mod q` is `y`, plus `q` exactly when `y < 0`. -/
theorem emod_of_bounds {q y : ℤ} (h1 : -q ≤ y) (h2 : y < q) :
    y % q = y + q * (if y < 0 then 1 else 0) := by
  split_ifs with hy
  · have h := Int.emod_eq_of_lt (a := y + 1 * q) (b := q) (by omega) (by omega)
    rw [Int.add_mul_emod_self_right] at h
    rw [h]
    ring
  · rw [Int.emod_eq_of_lt (by omega) h2]
    ring

section Zq

variable {τ H : Type*} [Fintype τ] [Fintype H]

omit [Fintype τ] in
/-- **Lemma Zq, hop part.** If the hops form closed chains (a successor bijection
`succ` with `p (succ h) = u h`), the violated hops satisfy
`q · #violated = #hops + Σ_h (G (u h) − G (p h) − 1) mod q`. -/
theorem card_violated_eq (q : ℤ) (G : τ → ℤ) (hG : ∀ t, 0 ≤ G t ∧ G t < q)
    (p u : H → τ) (succ : H ≃ H) (hsucc : ∀ h, p (succ h) = u h) :
    q * ((univ.filter fun h => G (u h) ≤ G (p h)).card : ℤ) =
      Fintype.card H + ∑ h, (G (u h) - G (p h) - 1) % q := by
  have e1 : ∀ h, (G (u h) - G (p h) - 1) % q =
      (G (u h) - G (p h) - 1) + q * (if G (u h) ≤ G (p h) then 1 else 0) := by
    intro h
    have hu := hG (u h)
    have hp := hG (p h)
    rw [emod_of_bounds (by omega) (by omega)]
    simp only [show (G (u h) - G (p h) - 1 < 0) ↔ (G (u h) ≤ G (p h)) by omega]
  have bal : ∑ h, G (u h) = ∑ h, G (p h) := by
    rw [← Equiv.sum_comp succ (fun h => G (p h))]
    simp only [hsucc]
  simp only [e1, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, bal]
  rw [Finset.card_filter]
  push_cast
  simp

/-- **Lemma Zq, time part.** `q · #descents = Σ_t (G t − G (tprev t)) mod q`. -/
theorem card_descents_eq (q : ℤ) (G : τ → ℤ) (hG : ∀ t, 0 ≤ G t ∧ G t < q) (tprev : τ ≃ τ) :
    q * ((univ.filter fun t => G t < G (tprev t)).card : ℤ) =
      ∑ t, (G t - G (tprev t)) % q := by
  have e2 : ∀ t, (G t - G (tprev t)) % q =
      (G t - G (tprev t)) + q * (if G t < G (tprev t) then 1 else 0) := by
    intro t
    have ht := hG t
    have hpt := hG (tprev t)
    rw [emod_of_bounds (by omega) (by omega)]
    simp only [show (G t - G (tprev t) < 0) ↔ (G t < G (tprev t)) by omega]
  simp only [e2, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
    Equiv.sum_comp tprev G, sub_self, zero_add]
  rw [Finset.card_filter]
  push_cast
  rfl

/-- **Lemma Zq.** `q · cost = #hops + Σ_h e_h + Σ_t x_t`. -/
theorem lemma_Zq (q : ℤ) (G : τ → ℤ) (hG : ∀ t, 0 ≤ G t ∧ G t < q) (tprev : τ ≃ τ)
    (p u : H → τ) (succ : H ≃ H) (hsucc : ∀ h, p (succ h) = u h) :
    q * (((univ.filter fun h => G (u h) ≤ G (p h)).card : ℤ) +
        ((univ.filter fun t => G t < G (tprev t)).card : ℤ)) =
      Fintype.card H + ∑ h, (G (u h) - G (p h) - 1) % q + ∑ t, (G t - G (tprev t)) % q := by
  rw [mul_add, card_violated_eq q G hG p u succ hsucc, card_descents_eq q G hG tprev]

end Zq

section ExactHead

variable {τ C : Type*}

/-- **Chain decomposition, exact case.** If `G` and the visit index `κ`
both increase by `1` modulo `q` along every head-1 hop into an interior cell, and
the visits of each cell form one orbit of `prev`, then `G − κ` is constant
modulo `q` on each interior cell. -/
theorem congr_of_exact (q : ℤ) (G κ : τ → ℤ) (prev : τ → τ) (cell : τ → C) (S : Set C)
    (hcell : ∀ t, cell (prev t) = cell t)
    (horbit : ∀ s t, cell s = cell t → ∃ n : ℕ, prev^[n] t = s)
    (hexact : ∀ t, cell t ∈ S → G t - G (prev t) ≡ 1 [ZMOD q])
    (hκ : ∀ t, cell t ∈ S → κ t - κ (prev t) ≡ 1 [ZMOD q]) :
    ∀ s t, cell s = cell t → cell t ∈ S → G s - κ s ≡ G t - κ t [ZMOD q] := by
  have step : ∀ n t, cell t ∈ S →
      cell (prev^[n] t) = cell t ∧ G (prev^[n] t) - κ (prev^[n] t) ≡ G t - κ t [ZMOD q] := by
    intro n
    induction n with
    | zero => intro t _; exact ⟨rfl, Int.ModEq.refl _⟩
    | succ n ih =>
      intro t ht
      obtain ⟨hc, hm⟩ := ih t ht
      rw [Function.iterate_succ_apply']
      set s := prev^[n] t
      have hs : cell s ∈ S := hc ▸ ht
      refine ⟨(hcell s).trans hc, ?_⟩
      have h1 := hexact s hs
      have h2 := hκ s hs
      have h3 : G (prev s) - κ (prev s) ≡ G s - κ s [ZMOD q] := by
        have h4 : (G s - G (prev s)) - (κ s - κ (prev s)) ≡ 1 - 1 [ZMOD q] := Int.ModEq.sub h1 h2
        have h5 : G (prev s) - κ (prev s) =
            (G s - κ s) - ((G s - G (prev s)) - (κ s - κ (prev s))) := by ring
        rw [h5]
        calc (G s - κ s) - ((G s - G (prev s)) - (κ s - κ (prev s)))
            ≡ (G s - κ s) - (1 - 1) [ZMOD q] := Int.ModEq.sub_left _ h4
          _ = G s - κ s := by ring
      exact h3.trans hm
  intro s t hst ht
  obtain ⟨n, hn⟩ := horbit s t hst
  have := (step n t ht).2
  rwa [hn] at this

/-- The defect of a cycle of head-2 hops: `Σ_j (κ (end) − κ (start) − 1)`. -/
def cycleDefect (κ : τ → ℤ) (prev₂ : τ → τ) {ℓ : ℕ} (b : Fin ℓ → τ) : ℤ :=
  ∑ j, (κ (b j) - κ (prev₂ (b j)) - 1)

/-- **Transfer identity, exact case.** Around a cycle of head-2 hops
whose consecutive hops meet in interior head-1 cells, the label errors sum to the
defect modulo `q`. -/
theorem cycle_errors_congr (q : ℤ) (G κ : τ → ℤ) (prev₂ : τ → τ) (cell : τ → C) (S : Set C)
    (hcongr : ∀ s t, cell s = cell t → cell t ∈ S → G s - κ s ≡ G t - κ t [ZMOD q])
    {ℓ : ℕ} (b : Fin ℓ → τ) (hconn : ∀ j, cell (b j) = cell (prev₂ (b (finRotate ℓ j))))
    (hint : ∀ j, cell (b j) ∈ S) :
    ∑ j, (G (b j) - G (prev₂ (b j)) - 1) ≡ cycleDefect κ prev₂ b [ZMOD q] := by
  unfold cycleDefect
  apply Int.ModEq.symm
  rw [Int.modEq_iff_dvd]
  have hre : ∑ j, (G (prev₂ (b j)) - κ (prev₂ (b j))) =
      ∑ j, (G (prev₂ (b (finRotate ℓ j))) - κ (prev₂ (b (finRotate ℓ j)))) :=
    (Equiv.sum_comp (finRotate ℓ) (fun j => G (prev₂ (b j)) - κ (prev₂ (b j)))).symm
  have hdiff : ∑ j, (G (b j) - G (prev₂ (b j)) - 1) - ∑ j, (κ (b j) - κ (prev₂ (b j)) - 1) =
      ∑ j, ((G (b j) - κ (b j)) - (G (prev₂ (b (finRotate ℓ j))) -
        κ (prev₂ (b (finRotate ℓ j))))) := by
    rw [← Finset.sum_sub_distrib, Finset.sum_sub_distrib (f := fun j => G (b j) - κ (b j)), ← hre,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hdiff]
  apply Finset.dvd_sum
  intro j _
  have h := hcongr (prev₂ (b (finRotate ℓ j))) (b j) (hconn j).symm (hint j)
  exact Int.modEq_iff_dvd.mp h

/-- A nonnegative integer congruent to a negative defect `δ` is at least `q + δ`. -/
theorem le_of_modEq_neg {q E δ : ℤ} (hq : 0 < q) (hE : 0 ≤ E) (hmod : E ≡ δ [ZMOD q])
    (h2 : δ < 0) : q + δ ≤ E := by
  obtain ⟨m, hm⟩ := Int.modEq_iff_dvd.mp hmod.symm
  have hm1 : 1 ≤ m := by
    by_contra h
    push Not at h
    have : m ≤ 0 := by omega
    nlinarith
  nlinarith

/-- **Theorem E (abstract form).** Let `G` be a label on a cyclic time set with two
heads, whose hops are `(prev₁ t, t)` and `(prev₂ t, t)`, and suppose `G − κ` is
constant modulo `q` on every interior head-1 cell (`congr_of_exact`: labels exact
on head 1). Let `cyc i` (for `i < k`) be hop-disjoint cycles of head-2 hops whose
consecutive hops meet in interior head-1 cells, each with negative defect.
Then `q · cost ≥ 2|τ| + Σ_i (q + δ_i)`: a cycle with `−q < δ < 0` costs about
one violation. -/
theorem cost_ge_of_negative_cycles [Fintype τ] [DecidableEq τ] (q : ℤ) (hq : 0 < q) (G : τ → ℤ)
    (hG : ∀ t, 0 ≤ G t ∧ G t < q) (tprev prev₁ prev₂ : τ ≃ τ) (cell : τ → C) (S : Set C)
    (κ : τ → ℤ)
    (hcongr : ∀ s t, cell s = cell t → cell t ∈ S → G s - κ s ≡ G t - κ t [ZMOD q])
    {k : ℕ} (len : Fin k → ℕ) (cyc : (i : Fin k) → Fin (len i) → τ)
    (hinj : Function.Injective fun x : (Σ i, Fin (len i)) => cyc x.1 x.2)
    (hconn : ∀ i j, cell (cyc i j) = cell (prev₂ (cyc i (finRotate (len i) j))))
    (hint : ∀ i j, cell (cyc i j) ∈ S)
    (hneg : ∀ i, cycleDefect κ prev₂ (cyc i) < 0) :
    2 * (Fintype.card τ : ℤ) + ∑ i, (q + cycleDefect κ prev₂ (cyc i)) ≤
      q * (((univ.filter fun t => G t ≤ G (prev₁ t)).card : ℤ) +
        ((univ.filter fun t => G t ≤ G (prev₂ t)).card : ℤ) +
        ((univ.filter fun t => G t < G (tprev t)).card : ℤ)) := by
  have hZ1 := card_violated_eq q G hG prev₁ id prev₁.symm (fun t => by simp)
  have hZ2 := card_violated_eq q G hG prev₂ id prev₂.symm (fun t => by simp)
  have hZt := card_descents_eq q G hG tprev
  simp only [id] at hZ1 hZ2
  have hnn : ∀ x : ℤ, 0 ≤ x % q := fun x => Int.emod_nonneg x hq.ne'
  have hsum1 : 0 ≤ ∑ t, (G t - G (prev₁ t) - 1) % q := Finset.sum_nonneg fun t _ => hnn _
  have hsumt : 0 ≤ ∑ t, (G t - G (tprev t)) % q := Finset.sum_nonneg fun t _ => hnn _
  -- the head-2 errors dominate the errors on the cycles
  let e : τ → ℤ := fun t => (G t - G (prev₂ t) - 1) % q
  have hcyc : ∀ i, q + cycleDefect κ prev₂ (cyc i) ≤ ∑ j, e (cyc i j) := by
    intro i
    have hc := cycle_errors_congr q G κ prev₂ cell S hcongr (cyc i) (hconn i) (hint i)
    have hres : ∑ j, e (cyc i j) ≡ ∑ j, (G (cyc i j) - G (prev₂ (cyc i j)) - 1) [ZMOD q] :=
      Int.ModEq.sum fun j _ => Int.mod_modEq _ _
    exact le_of_modEq_neg hq (Finset.sum_nonneg fun j _ => hnn _) (hres.trans hc) (hneg i)
  have hsub : ∑ x : (Σ i, Fin (len i)), e (cyc x.1 x.2) ≤ ∑ t, e t := by
    rw [← Finset.sum_image (f := e) (s := Finset.univ)
      (g := fun x : (Σ i, Fin (len i)) => cyc x.1 x.2) (fun x _ y _ hxy => hinj hxy)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun t _ _ => hnn _)
  rw [Fintype.sum_sigma] at hsub
  have hsumcyc : ∑ i, (q + cycleDefect κ prev₂ (cyc i)) ≤ ∑ i, ∑ j, e (cyc i j) :=
    Finset.sum_le_sum fun i _ => hcyc i
  simp only [e] at hsub hsumcyc
  linarith

end ExactHead

end MotionDepthCodes
