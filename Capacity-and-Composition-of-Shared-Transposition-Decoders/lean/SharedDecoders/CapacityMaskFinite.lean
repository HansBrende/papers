import SharedDecoders.CapacityUniversal

/-! # A finite two-certificate bound

The two orders `(1,3)` and `(2,1)` use the same source and the same run
budget.  Their weighted average gives `6 D ≤ 4 b d² + 5 b d`.
-/

namespace SharedDecoders

open Module CapacityRuns Finset

variable {d : ℕ} [NeZero d]

private def finiteTicketLength (i : Fin 7) : ℕ :=
  if i < 2 then 1 else if i < 4 then 2 else if i = 4 then 3 else 4

private theorem finiteTicket_lt (i : Fin 7) : i.val / 2 < finiteTicketLength i := by
  fin_cases i <;> norm_num [finiteTicketLength]

/-- Seven run-prefix tickets fit in two copies of the cycle. -/
theorem finite_weighted_run_budget (p : ZMod d → Bool) (s : ZMod d) :
    2 * runCount p s 1 + 2 * runCount p s 2 + runCount p s 3 +
      2 * runCount p s 4 ≤ 2*d := by
  classical
  let Tickets := Σ i : Fin 7, {x // Start p s (finiteTicketLength i) x}
  let mark : Tickets → ZMod d × Fin 2 := fun t =>
    (t.2.1 + (t.1.val/2) • s, ⟨t.1.val%2, Nat.mod_lt _ (by omega)⟩)
  have hinj : Function.Injective mark := by
    intro a b hab
    have hpoint := congrArg Prod.fst hab
    have hlane := congrArg (fun z : ZMod d × Fin 2 => z.2.val) hab
    obtain ⟨hoff, hx⟩ := start_offset_injective a.2.2 b.2.2
      (finiteTicket_lt a.1) (finiteTicket_lt b.1) hpoint
    have hi : a.1=b.1 := by apply Fin.ext; dsimp [mark] at hlane; omega
    cases a with
    | mk i x =>
      cases b with
      | mk j y =>
        dsimp at hi hx
        subst j
        congr 1
        exact Subtype.ext hx
  have hcard := Fintype.card_le_of_injective mark hinj
  have hsum : Fintype.card Tickets =
      2 * runCount p s 1 + 2 * runCount p s 2 + runCount p s 3 +
        2 * runCount p s 4 := by
    rw [Fintype.card_sigma]
    simp only [Fin.sum_univ_succ]
    norm_num [finiteTicketLength, runCount]
    omega
  simpa only [hsum, Fintype.card_prod, Fintype.card_fin, ZMod.card, mul_comm] using hcard

omit [NeZero d] in theorem two_one_covers :
    CoversRadius (extendShifts (extendShifts {0} (2 : ZMod d)) 1) 1 3 := by
  intro j hj
  interval_cases j
  · exact ⟨0, by simp [extendShifts], 0, by simp [extendShifts], by simp⟩
  · exact ⟨1, by simp [extendShifts], 0, by simp [extendShifts], by simp⟩
  · exact ⟨2, by simp [extendShifts], 0, by simp [extendShifts], by simp⟩
  · refine ⟨2+1, ?_, 0, by simp [extendShifts], ?_⟩
    · apply Finset.mem_union_right
      exact Finset.mem_image_of_mem _ (by simp [extendShifts])
    · norm_num

variable {F A κ : Type*} [Field F] [AddCommGroup A] [Module F A]
  [FiniteDimensional F A]

theorem IsSharedCode.four_mul_finrank_le {p : ZMod d → κ}
    {C : Submodule F (State d A)} (h : IsSharedCode F p C) (s t : ZMod d) :
    4 * finrank F C ≤ 2 * (d*d*finrank F A) +
      d * componentCount p (extendShifts {0} s) * finrank F A +
      d * componentCount p (extendShifts (extendShifts {0} s) t) * finrank F A := by
  have h₀ := h.two_mul_commonPreimage_finrank_le {0} s
  have h₁ := h.two_mul_commonPreimage_finrank_le (extendShifts {0} s) t
  have h₂ := h.commonPreimage_finrank_le (extendShifts (extendShifts {0} s) t)
  rw [commonPreimage_zero, componentCount_zero] at h₀
  omega

/-- The finite alternative to the asymptotic `41/64` bound. The entry module
may mix all lanes, and the shared decoders need not be linear. -/
theorem IsSharedCode.six_mul_finrank_le {p : ZMod d → Bool}
    {C : Submodule F (State d A)} (h : IsSharedCode F p C) (hd : 8<d) :
    6 * finrank F C ≤ 4 * (d*d*finrank F A) + 5 * d * finrank F A := by
  have hval1 : (1 : ZMod d).val = 1 := by
    simpa using (ZMod.val_natCast (n := d) 1).trans (Nat.mod_eq_of_lt (by omega))
  have hval2 : (2 : ZMod d).val = 2 := by
    simpa using (ZMod.val_natCast (n := d) 2).trans (Nat.mod_eq_of_lt (by omega))
  have hg1 : Nat.gcd d (1 : ZMod d).val = 1 := by rw [hval1, Nat.gcd_one_right]
  have hg2 : Nat.gcd d (2 : ZMod d).val ≤ 2 := by
    rw [hval2]
    exact Nat.gcd_le_right d (by omega)
  have hfirst := h.four_mul_finrank_le 1 3
  have hsecond := h.four_mul_finrank_le 2 1
  have hc1 := componentCount_first_shift p (1 : ZMod d)
  have hc4 := componentCount_second_shift p (1 : ZMod d)
  have hc2 := componentCount_first_shift p (2 : ZMod d)
  have hc3 := componentCount_le_runs_add_two_gcd p
    (extendShifts (extendShifts {0} 2) 1) 1 3 (by omega) two_one_covers
  have hr := finite_weighted_run_budget p (1 : ZMod d)
  have hdouble := changeCount_double p (1 : ZMod d)
  rw [hg1] at hc1 hc4 hc3
  simp only [nsmul_eq_mul, mul_one] at hc4 hdouble
  norm_num only [Nat.cast_ofNat] at hdouble hc4
  rw [hdouble] at hc2
  rw [← runCount_one] at hc1
  have hc2' : componentCount p (extendShifts {0} (2 : ZMod d)) ≤
      2 * runCount p 1 2 + 2 := hc2.trans (Nat.add_le_add_left hg2 _)
  have hb1 := Nat.mul_le_mul_left (d*finrank F A) hc1
  have hb4 := Nat.mul_le_mul_left (d*finrank F A) hc4
  have hb2 := Nat.mul_le_mul_left (d*finrank F A) hc2'
  have hb3 := Nat.mul_le_mul_left (d*finrank F A) hc3
  have hbudget := Nat.mul_le_mul_left (d*finrank F A) hr
  nlinarith only [hfirst, hsecond, hb1, hb4, hb2, hb3, hbudget]

end SharedDecoders
