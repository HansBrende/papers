import SharedDecoders.CapacityRetentionFinite

/-! # Full symmetric retention and coprime partners

The exceptional rows are exactly those with no same-class partner at a coprime
cyclic displacement. In prime dimension they are the singleton receiver classes.
-/

namespace SharedDecoders

open Module

variable {d : ℕ} [NeZero d] {κ : Type*}

noncomputable def coprimeShifts (d : ℕ) [NeZero d] : Finset (ZMod d) := by
  classical
  exact Finset.univ.filter (fun s => Nat.gcd d s.val = 1)

noncomputable def coprimeUncoveredRows (p : ZMod d → κ) : Finset (ZMod d) :=
  uncoveredRows (fun s : coprimeShifts d => coveredRows p s.val)

theorem mem_coprimeUncoveredRows (p : ZMod d → κ) (c : ZMod d) :
    c ∈ coprimeUncoveredRows p ↔ ∀ s : ZMod d, Nat.gcd d s.val = 1 → p c ≠ p (c + s) := by
  classical
  simp [coprimeUncoveredRows, uncoveredRows, coveredRows, coprimeShifts]

variable {F A : Type*} [Field F] [AddCommGroup A] [Module F A]
  [FiniteDimensional F A]

/-- This strengthens the prime-dimension assertion: only same-class partners
at coprime displacements are needed, in any positive dimension. -/
theorem IsSharedCode.full_symmetric_retention {p : ZMod d → κ}
    {C : Submodule F (State d A)} (hC : IsSharedCode F p C)
    (hS : symmetricSpace ≤ C) :
    (finrank F C : ℝ) ≤ finrank F (symmetricSpace (F := F) (A := A) (I := ZMod d)) +
      (finrank F A : ℝ) / 2 * (coprimeUncoveredRows p).card *
        ((coprimeUncoveredRows p).card - 1) := by
  classical
  have h := hC.retention_bound (fun s : coprimeShifts d => s.val)
  dsimp only at h
  rw [inf_eq_right.mpr hS] at h
  have hsum : (∑ s : coprimeShifts d, ((Nat.gcd d s.val.val : ℝ) - 1)) = 0 := by
    apply Finset.sum_eq_zero
    intro s _
    rw [(Finset.mem_filter.mp s.property).2]
    norm_num
  simpa only [sub_self, mul_zero, add_zero, hsum,
    coprimeUncoveredRows] using h

/-- Even one exceptional row leaves no alternating degree of freedom. -/
theorem IsSharedCode.eq_symmetric_of_at_most_one_exception {p : ZMod d → κ}
    {C : Submodule F (State d A)} (hC : IsSharedCode F p C)
    (hS : symmetricSpace ≤ C) (hu : (coprimeUncoveredRows p).card ≤ 1) :
    C = symmetricSpace := by
  have h := hC.full_symmetric_retention hS
  have hu' : (coprimeUncoveredRows p).card = 0 ∨ (coprimeUncoveredRows p).card = 1 := by omega
  rcases hu' with hu' | hu' <;>
    simp only [hu', Nat.cast_zero, Nat.cast_one, sub_self, mul_zero, zero_mul, add_zero] at h <;>
    exact (Submodule.eq_of_le_of_finrank_le hS (Nat.cast_le.mp h)).symm

theorem IsSharedCode.eq_symmetric_of_coprime_partners {p : ZMod d → κ}
    {C : Submodule F (State d A)} (hC : IsSharedCode F p C)
    (hS : symmetricSpace ≤ C)
    (hp : ∀ c, ∃ s : ZMod d, Nat.gcd d s.val = 1 ∧ p c = p (c + s)) :
    C = symmetricSpace := by
  have hempty : coprimeUncoveredRows p = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro c hc
    obtain ⟨s, hs, hps⟩ := hp c
    exact (mem_coprimeUncoveredRows p c).mp hc s hs hps
  have h := hC.full_symmetric_retention hS
  simp only [hempty, Finset.card_empty, Nat.cast_zero, mul_zero, zero_mul, add_zero] at h
  exact (Submodule.eq_of_le_of_finrank_le hS (Nat.cast_le.mp h)).symm

noncomputable def singletonRows (p : ZMod d → κ) : Finset (ZMod d) := by
  classical
  exact Finset.univ.filter (fun c => ∀ e, p e = p c → e = c)

omit [FiniteDimensional F A] [Module F A] [AddCommGroup A] [Field F] in
theorem coprimeUncoveredRows_eq_singletonRows (hd : d.Prime) (p : ZMod d → κ) :
    coprimeUncoveredRows p = singletonRows p := by
  classical
  ext c
  rw [mem_coprimeUncoveredRows]
  simp only [singletonRows, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hc e he
    by_contra hne
    have hs : e - c ≠ 0 := sub_ne_zero.mpr hne
    have hval : (e - c).val ≠ 0 := by simpa using hs
    have hcop := Nat.coprime_of_lt_prime hval (ZMod.val_lt (e - c)) hd
    exact hc (e - c) hcop (by simpa using he.symm)
  · intro hc s hs he
    have hz : s = 0 := by
      have h := hc (c + s) he.symm
      exact add_right_injective c (by simpa using h)
    rw [hz] at hs
    simp only [ZMod.val_zero, Nat.gcd_zero_right] at hs
    exact hd.ne_one hs

theorem IsSharedCode.prime_full_symmetric_retention {p : ZMod d → κ}
    {C : Submodule F (State d A)} (hC : IsSharedCode F p C)
    (hS : symmetricSpace ≤ C) (hd : d.Prime) :
    (finrank F C : ℝ) ≤ finrank F (symmetricSpace (F := F) (A := A) (I := ZMod d)) +
      (finrank F A : ℝ) / 2 * (singletonRows p).card * ((singletonRows p).card - 1) := by
  simpa only [coprimeUncoveredRows_eq_singletonRows hd] using hC.full_symmetric_retention hS

end SharedDecoders
