import SharedDecoders.CapacityAmbient
import Mathlib.Tactic.LinearCombination
import Mathlib.Basic.Real.Basic

/-! # A sparse difference cover and the many-class translate bound -/

namespace SharedDecoders

open Module

variable {d : ℕ} [NeZero d] {κ : Type*}

omit [NeZero d] in
theorem link_of_interval_collision {p : ZMod d → κ} {Δ : Finset (ZMod d)}
    {R : ℕ}
    (hΔ : ∀ n ≤ R, ∃ s ∈ Δ, ∃ t ∈ Δ, (n : ZMod d) = s - t)
    {c e : ZMod d} (hp : p c = p e) (i j : Fin (R + 1))
    (heq : c + (i.val : ZMod d) = e + (j.val : ZMod d)) : Link p Δ c e := by
  by_cases hij : j.val ≤ i.val
  · obtain ⟨s, hs, t, ht, hst⟩ := hΔ (i.val - j.val) (by omega)
    rw [Nat.cast_sub hij] at hst
    refine ⟨hp, s, hs, t, ht, ?_⟩
    linear_combination heq - hst
  · obtain ⟨s, hs, t, ht, hst⟩ := hΔ (j.val - i.val) (by omega)
    rw [Nat.cast_sub (by omega : i.val ≤ j.val)] at hst
    refine ⟨hp, t, ht, s, hs, ?_⟩
    linear_combination heq + hst

/-- Each color's components admit disjoint forward intervals of length R+1.
This avoids choosing and sorting cyclic gaps. -/
theorem componentCount_le_classes_mul_div [Fintype κ]
    (p : ZMod d → κ) (Δ : Finset (ZMod d)) (R : ℕ) (hR : R + 1 ≤ d)
    (hΔ : ∀ n ≤ R, ∃ s ∈ Δ, ∃ t ∈ Δ, (n : ZMod d) = s - t) :
    componentCount p Δ ≤ Fintype.card κ * (d / (R + 1)) := by
  classical
  let label : LinkComponent p Δ → κ := fun q => p q.out
  have hfiber : ∀ a : κ, Fintype.card {q : LinkComponent p Δ // label q = a} ≤ d / (R + 1) := by
    intro a
    let enc : ({q : LinkComponent p Δ // label q = a} × Fin (R + 1)) → ZMod d :=
      fun z => z.1.val.out + (z.2.val : ZMod d)
    have hinj : Function.Injective enc := by
      rintro ⟨q, i⟩ ⟨q', j⟩ heq
      have hp : p q.val.out = p q'.val.out := q.property.trans q'.property.symm
      have hlink := link_of_interval_collision hΔ hp i j heq
      have hqq : q.val = q'.val := Quotient.out_equiv_out.mp (Relation.EqvGen.rel _ _ hlink)
      have hq : q = q' := Subtype.ext hqq
      subst q'
      have hcast : (i.val : ZMod d) = (j.val : ZMod d) := add_left_cancel heq
      have hiv : i.val < d := lt_of_lt_of_le i.isLt hR
      have hjv : j.val < d := lt_of_lt_of_le j.isLt hR
      have hij := congrArg ZMod.val hcast
      simp only [ZMod.val_natCast_of_lt hiv, ZMod.val_natCast_of_lt hjv] at hij
      exact Prod.ext rfl (Fin.ext hij)
    have hcard := Fintype.card_le_of_injective enc hinj
    simp only [Fintype.card_prod, Fintype.card_fin, ZMod.card] at hcard
    exact (Nat.le_div_iff_mul_le (by omega)).2 hcard
  have hcard := Fintype.card_congr (Equiv.sigmaFiberEquiv label)
  rw [Fintype.card_sigma] at hcard
  change Fintype.card (LinkComponent p Δ) ≤ _
  rw [← hcard]
  calc
    ∑ a : κ, Fintype.card {q : LinkComponent p Δ // label q = a} ≤
        ∑ _a : κ, d / (R + 1) := Finset.sum_le_sum (fun a _ => hfiber a)
    _ = Fintype.card κ * (d / (R + 1)) := by simp

def sparseShifts (u v : ℕ) : Finset (ZMod d) :=
  (Finset.range u).image (fun n : ℕ => (n : ZMod d)) ∪
    (Finset.Icc 1 v).image (fun j => ((j * u : ℕ) : ZMod d))

omit [NeZero d] in
theorem sparseShifts_card_le (u v : ℕ) : (sparseShifts (d := d) u v).card ≤ u + v := by
  calc
    (sparseShifts (d := d) u v).card ≤
        ((Finset.range u).image (fun n : ℕ => (n : ZMod d))).card +
        ((Finset.Icc 1 v).image (fun j => ((j * u : ℕ) : ZMod d))).card :=
      Finset.card_union_le _ _
    _ ≤ (Finset.range u).card + (Finset.Icc 1 v).card :=
      Nat.add_le_add (Finset.card_image_le) (Finset.card_image_le)
    _ = u + v := by simp

omit [NeZero d] in
theorem zero_mem_sparseShifts {u v : ℕ} (hu : 0 < u) :
    (0 : ZMod d) ∈ sparseShifts u v := by
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hu, by simp⟩

omit [NeZero d] in
theorem sparseShifts_cover {u v : ℕ} (hu : 0 < u) (_hv : 0 < v)
    (n : ℕ) (hn : n ≤ u * v) :
    ∃ s ∈ sparseShifts (d := d) u v, ∃ t ∈ sparseShifts u v, (n : ZMod d) = s - t := by
  classical
  by_cases hn0 : n = 0
  · subst n
    exact ⟨0, zero_mem_sparseShifts hu, 0, zero_mem_sparseShifts hu, by simp⟩
  generalize hq : n / u = q
  generalize harem : n % u = a
  have ha : a < u := by rw [← harem]; exact Nat.mod_lt n hu
  have hnqa : n = q * u + a := by
    have hh := (Nat.mod_add_div n u).symm
    rw [hq, harem] at hh
    simpa [add_comm, mul_comm] using hh
  by_cases ha0 : a = 0
  · have hqpos : 1 ≤ q := by
      by_contra hh
      have hq0 : q = 0 := by omega
      simp [hq0, ha0] at hnqa
      exact hn0 hnqa
    have hqle : q ≤ v := by nlinarith
    have hqs : ((q * u : ℕ) : ZMod d) ∈ sparseShifts u v := by
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨q, Finset.mem_Icc.mpr ⟨hqpos, hqle⟩, rfl⟩
    refine ⟨_, hqs, 0, zero_mem_sparseShifts hu, ?_⟩
    rw [sub_zero, show n = q * u by omega]
  · have hapos : 0 < a := Nat.pos_of_ne_zero ha0
    have hqle : q + 1 ≤ v := by nlinarith
    have hsmall : u - a < u := by omega
    have hlarge : ((q + 1) * u : ℕ) ≥ u - a := by nlinarith
    have heq : n = (q + 1) * u - (u - a) := by
      rw [add_mul, one_mul]
      omega
    have hs : (((q + 1) * u : ℕ) : ZMod d) ∈ sparseShifts u v := by
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨q + 1, Finset.mem_Icc.mpr ⟨by omega, hqle⟩, rfl⟩
    have ht : ((u - a : ℕ) : ZMod d) ∈ sparseShifts u v := by
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨u - a, Finset.mem_range.mpr hsmall, rfl⟩
    refine ⟨_, hs, _, ht, ?_⟩
    rw [← Nat.cast_sub hlarge, ← heq]

theorem componentCount_le_d (p : ZMod d → κ) (Δ : Finset (ZMod d)) :
    componentCount p Δ ≤ d := by
  have hh := Fintype.card_le_of_surjective
    (Quotient.mk (Relation.EqvGen.setoid (Link p Δ))) Quotient.mk_surjective
  simpa only [componentCount, ZMod.card] using hh

variable {F A : Type*} [Field F] [AddCommGroup A] [Module F A]
  [FiniteDimensional F A] [Fintype κ]

/-- End-to-end many-class estimate, including the actual sparse-shift graph. -/
theorem IsSharedCode.difference_cover_bound {p : ZMod d → κ}
    {C : Submodule F (State d A)} (h : IsSharedCode F p C)
    {u v : ℕ} (hu : 0 < u) (hv : 0 < v) :
    let R := min (u * v) (d - 1)
    let U := min d (Fintype.card κ * (d / (R + 1)))
    (u + v) * finrank F C + d * finrank F A * (d - U) ≤
      (u + v) * (d * d * finrank F A) := by
  classical
  dsimp only
  let R := min (u * v) (d - 1)
  let U := min d (Fintype.card κ * (d / (R + 1)))
  let Δ := sparseShifts (d := d) u v
  let N := d * d * finrank F A
  have hd : 0 < d := NeZero.pos d
  have hR : R + 1 ≤ d := by dsimp [R]; omega
  have hcover : ∀ n ≤ R, ∃ s ∈ Δ, ∃ t ∈ Δ, (n : ZMod d) = s - t := by
    intro n hn
    exact sparseShifts_cover hu hv n (hn.trans (min_le_left _ _))
  have hcomp : componentCount p Δ ≤ U :=
    le_min (componentCount_le_d p Δ)
      (componentCount_le_classes_mul_div p Δ R hR hcover)
  have hdim := h.component_finrank_le (show Δ.Nonempty from ⟨0, zero_mem_sparseShifts hu⟩)
  have hcard : Δ.card ≤ u + v := sparseShifts_card_le u v
  have hcardpos : 0 < Δ.card := Finset.card_pos.mpr ⟨0, zero_mem_sparseShifts hu⟩
  have hdimC : finrank F C ≤ N := by
    simpa only [N, finrank_state] using (Submodule.finrank_le C)
  have hU : U ≤ d := min_le_left _ _
  have hdim' : Δ.card * finrank F C + N ≤ Δ.card * N + d * U * finrank F A := by
    have hc := Nat.mul_le_mul_left (d * finrank F A) hcomp
    have hn := Nat.sub_add_cancel (by omega : 1 ≤ Δ.card)
    dsimp [N] at *
    nlinarith
  have hreplace : (u + v - Δ.card) * finrank F C ≤ (u + v - Δ.card) * N :=
    Nat.mul_le_mul_left _ hdimC
  have hcsub := Nat.sub_add_cancel hcard
  have husub := Nat.sub_add_cancel hU
  have hc₁ := congrArg (fun x => x * finrank F C) hcsub
  have hc₂ := congrArg (fun x => x * N) hcsub
  simp only [add_mul] at hc₁ hc₂
  have htotal : (u + v) * finrank F C + N ≤ (u + v) * N + d * U * finrank F A := by
    simp only [add_mul]
    omega
  have hcost : d * finrank F A * (d - U) + d * U * finrank F A = N := by
    have hh := congrArg (fun x => d * finrank F A * x) husub
    dsimp [N]
    nlinarith only [hh]
  change (u + v) * finrank F C + d * finrank F A * (d - U) ≤ (u + v) * N
  omega

theorem IsSharedCode.difference_cover_real_bound {p : ZMod d → κ}
    {C : Submodule F (State d A)} (h : IsSharedCode F p C)
    {u v : ℕ} (hu : 0 < u) (hv : 0 < v) :
    let R := min (u * v) (d - 1)
    let U := min d (Fintype.card κ * (d / (R + 1)))
    (finrank F C : ℝ) ≤ d * d * finrank F A -
      (d * finrank F A * (d - U) : ℕ) / (u + v : ℕ) := by
  dsimp only
  have hh := h.difference_cover_bound hu hv
  dsimp only at hh
  have hreal := (Nat.cast_le (α := ℝ)).2 hh
  push_cast at hreal
  have huv : (0 : ℝ) < (u + v : ℕ) := by exact_mod_cast (by omega : 0 < u + v)
  apply (le_sub_iff_add_le).2
  have hdiv : ((d * finrank F A * (d - min d (Fintype.card κ * (d / (min (u * v) (d - 1) + 1)))) : ℕ) : ℝ) /
      (u + v : ℕ) ≤ d * d * finrank F A - (finrank F C : ℝ) := by
    apply (div_le_iff₀ huv).2
    push_cast
    nlinarith
  linarith

/-- The square-cover consequence. Any positive integer square covering 2M
suffices, in particular the ceiling of its square root. -/
theorem IsSharedCode.square_cover_bound {p : ZMod d → κ}
    {C : Submodule F (State d A)} (h : IsSharedCode F p C)
    {t : ℕ} (ht : 0 < t) (hM : 2 * Fintype.card κ ≤ d)
    (hsq : 2 * Fintype.card κ ≤ t * t) :
    4 * t * finrank F C + d * d * finrank F A ≤
      4 * t * (d * d * finrank F A) := by
  let R := min (t * t) (d - 1)
  let U := min d (Fintype.card κ * (d / (R + 1)))
  have hh := h.difference_cover_bound ht ht
  change (t + t) * finrank F C + d * finrank F A * (d - U) ≤
    (t + t) * (d * d * finrank F A) at hh
  have hden : 2 * Fintype.card κ ≤ R + 1 := by
    dsimp [R]
    omega
  have hdiv := Nat.div_mul_le_self d (R + 1)
  have hmul := Nat.mul_le_mul_right (d / (R + 1)) hden
  have hUle : U ≤ Fintype.card κ * (d / (R + 1)) := min_le_right _ _
  have hU2 : 2 * U ≤ d := by nlinarith
  have hU : U ≤ d := by omega
  have hsub := Nat.sub_add_cancel hU
  have hcost : d * d * finrank F A ≤ 2 * (d * finrank F A * (d - U)) := by
    have hmul' := Nat.mul_le_mul_left (d * finrank F A) (show d ≤ 2 * (d - U) by omega)
    nlinarith only [hmul']
  nlinarith only [hh, hcost]

theorem IsSharedCode.saturated_cover_bound {p : ZMod d → κ}
    {C : Submodule F (State d A)} (h : IsSharedCode F p C)
    {t : ℕ} (ht : 0 < t) (hM : Fintype.card κ ≤ d)
    (hsq : d - 1 ≤ t * t) :
    2 * t * finrank F C + d * finrank F A * (d - Fintype.card κ) ≤
      2 * t * (d * d * finrank F A) := by
  have hh := h.difference_cover_bound ht ht
  dsimp only at hh
  have hd : 1 ≤ d := NeZero.pos d
  simpa only [min_eq_right hsq, Nat.sub_add_cancel hd, Nat.div_self (NeZero.pos d),
    mul_one, min_eq_right hM, ← two_mul] using hh

end SharedDecoders
