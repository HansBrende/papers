import TapeStorageRates.NativeWindow
import MergeDepth.HCStarQ91

/-! # Packet addresses for actual native head positions

The physical origin of an input packet includes the tails of the entries to its left. This
description clips the number of tails at both input ends. Thus even negative and exterior head
positions have a definite packet address, and every exterior packet has width exactly `s`.
-/

namespace TapeStorageRates.PacketCompiler

open BoundedNesting MergeDepth Transpose

set_option autoImplicit false

/-- A consecutive partition of the whole integer tape, starting at zero. Each cell contains
at least `s` and at most `s+r` physical symbols. -/
structure CellLayout (s r : ℕ) where
  start : ℤ → ℤ
  zero : start 0 = 0
  lower : ∀ q, start q + s ≤ start (q + 1)
  upper : ∀ q, start (q + 1) ≤ start q + s + r

/-- Completed matrix entries preceding a packet, clipped at the two ends. -/
def pastTails (d a : ℕ) (q : ℤ) : ℤ := max 0 (min ((d * d : ℕ) : ℤ) (q / a))

private theorem pastTails_step (d : ℕ) {a : ℕ} (ha : 0 < a) (q : ℤ) :
    pastTails d a q ≤ pastTails d a (q + 1) ∧ pastTails d a (q + 1) ≤ pastTails d a q + 1 := by
  have ha' : 0 < (a : ℤ) := by exact_mod_cast ha
  have h₁ := Int.ediv_le_ediv ha' (show q ≤ q + 1 by omega)
  have h₂ := Int.ediv_le_ediv ha' (show q + 1 ≤ q + a by omega)
  have hdiv : (q + a) / (a : ℤ) = q / a + 1 := by
    simpa using Int.add_mul_ediv_left q 1 (show (a : ℤ) ≠ 0 by omega)
  rw [hdiv] at h₂
  unfold pastTails; omega

/-- Public ragged input and output framing for a `d × d` matrix with `a` packets per entry.
The same formula at `r=0` gives an ordinary work-tape partition. -/
def raggedLayout (d a s r : ℕ) (ha : 0 < a) : CellLayout s r where
  start q := q * s + pastTails d a q * r
  zero := by simp [pastTails]
  lower q := by
    have h := (pastTails_step d ha q).1
    nlinarith [mul_nonneg (sub_nonneg.2 h) (Int.natCast_nonneg r)]
  upper q := by
    have h := (pastTails_step d ha q).2
    nlinarith [mul_nonneg (sub_nonneg.2 h) (Int.natCast_nonneg r)]

theorem ragged_start_nonpos {d a s r : ℕ} (ha : 0 < a) {q : ℤ} (hq : q ≤ 0) :
    (raggedLayout d a s r ha).start q = q * s := by
  have hz : q / (a : ℤ) ≤ 0 := by simpa using
    (Int.ediv_le_ediv (show 0 < (a : ℤ) by exact_mod_cast ha) hq)
  simp [raggedLayout, pastTails, max_eq_left (show min _ (q / (a : ℤ)) ≤ 0 from (min_le_right _ _).trans hz)]

theorem ragged_start_nat {d a s r q : ℕ} (ha : 0 < a) (hq : q ≤ d*d*a) :
    (raggedLayout d a s r ha).start (q : ℤ) = ((q*s + q/a*r : ℕ) : ℤ) := by
  have h : q / a ≤ d*d := (Nat.div_le_div_right hq).trans (by rw [Nat.mul_div_cancel _ ha])
  have hdiv : (q : ℤ) / a ≤ ((d*d : ℕ) : ℤ) := by exact_mod_cast h
  have hnn := Int.ediv_nonneg (Int.natCast_nonneg q) (Int.natCast_nonneg a)
  push_cast at hdiv
  simp [raggedLayout, pastTails, min_eq_right hdiv, max_eq_right hnn]

theorem ragged_start_end {d a s r : ℕ} (ha : 0 < a) :
    (raggedLayout d a s r ha).start ((d*d*a : ℕ) : ℤ) = ((d*d*(a*s+r) : ℕ) : ℤ) := by
  rw [ragged_start_nat ha le_rfl, Nat.mul_div_cancel _ ha]
  push_cast; ring

/-- Each work cell consists of exactly `s` native tape symbols. -/
def workLayout (s : ℕ) : CellLayout s 0 where
  start q := q * s
  zero := by simp
  lower _ := by simp [add_mul]
  upper _ := by simp [add_mul]

variable {s r : ℕ} (L : CellLayout s r) (hs : 0 < s)

include hs in
theorem CellLayout.strictMono : StrictMono L.start := by
  apply strictMono_int_of_lt_succ
  intro q
  have := L.lower q
  omega

include hs in
private theorem CellLayout.exists_cell (p : ℤ) :
    ∃ q, L.start q ≤ p ∧ p < L.start (q + 1) := by
  refine Int.inductionOn' (motive := fun t : ℤ => ∃ q, L.start q ≤ t ∧ t < L.start (q+1)) p 0 ?_ ?_ ?_
  · exact ⟨0, L.zero.le, by simpa [L.zero] using L.strictMono hs (show (0 : ℤ) < 0 + 1 by decide)⟩
  · rintro t _ ⟨q, hlo, hhi⟩
    by_cases h : t + 1 < L.start (q + 1)
    · exact ⟨q, by omega, h⟩
    · exact ⟨q + 1, by omega, by have := L.strictMono hs (show q+1 < q+1+1 by omega); omega⟩
  · rintro t _ ⟨q, hlo, hhi⟩
    by_cases h : L.start q ≤ t - 1
    · exact ⟨q, h, by omega⟩
    · refine ⟨q - 1, ?_, ?_⟩
      · have := L.strictMono hs (show q - 1 < q by omega); omega
      · simpa using (show t - 1 < L.start q by omega)

/-- The unique coarse cell containing the physical address `p`. -/
noncomputable def CellLayout.cell (p : ℤ) : ℤ := (L.exists_cell hs p).choose

theorem CellLayout.contains (p : ℤ) :
    L.start (L.cell hs p) ≤ p ∧ p < L.start (L.cell hs p + 1) := (L.exists_cell hs p).choose_spec

theorem CellLayout.cell_eq {p q : ℤ} (hlo : L.start q ≤ p) (hhi : p < L.start (q+1)) :
    L.cell hs p = q := by
  have hh := L.contains hs p
  have hm := (L.strictMono hs).monotone
  by_contra! h
  rcases lt_or_gt_of_ne h with h | h
  · have := hm (show L.cell hs p + 1 ≤ q by omega); omega
  · have := hm (show q + 1 ≤ L.cell hs p by omega); omega

@[simp] theorem CellLayout.cell_zero : L.cell hs 0 = 0 := by
  apply L.cell_eq hs L.zero.le
  simpa [L.zero] using L.strictMono hs (show (0 : ℤ) < 0 + 1 by decide)

/-- At most `s` fine moves cross at most one packet boundary, including from within a long cell. -/
theorem CellLayout.near_cell {p q : ℤ} (hpq : |p - q| ≤ s) :
    |L.cell hs p - L.cell hs q| ≤ 1 := by
  have h := abs_le.1 hpq
  have hp := L.contains hs p
  have hq := L.contains hs q
  have hm := (L.strictMono hs).monotone
  apply abs_le.2
  constructor
  · by_contra! hbad
    have hh := hm (show L.cell hs p + 1 + 1 ≤ L.cell hs q by omega)
    have := L.lower (L.cell hs p + 1)
    omega
  · by_contra! hbad
    have hh := hm (show L.cell hs q + 1 + 1 ≤ L.cell hs p by omega)
    have := L.lower (L.cell hs q + 1)
    omega

/-- Fine offsets live in a fixed alphabet even for dimension-dependent cell layouts. -/
noncomputable def CellLayout.offset (p : ℤ) : Fin (s + r) :=
  ⟨(p - L.start (L.cell hs p)).toNat, by
    have h := L.contains hs p
    have hu := L.upper (L.cell hs p)
    omega⟩

theorem CellLayout.start_add_offset (p : ℤ) :
    L.start (L.cell hs p) + ((L.offset hs p).val : ℤ) = p := by
  have h := (L.contains hs p).1
  change L.start (L.cell hs p) + ((p - L.start (L.cell hs p)).toNat : ℤ) = p
  omega

/-- Sampling an actual fine walk every `s` ticks gives a unit walk at packet addresses. -/
theorem CellLayout.sampled_walk {w : ℕ → ℤ} (hw : IsWalk w) :
    IsWalk (fun j => L.cell hs (w (j * s))) := by
  intro j
  apply L.near_cell hs
  have h := hw.lip (show j * s ≤ (j+1) * s by rw [Nat.add_mul]; omega)
  rw [Nat.add_mul, one_mul, Nat.add_sub_cancel_left] at h
  rw [Nat.add_mul, one_mul]
  exact abs_le.2 ⟨by omega, h.1⟩

end TapeStorageRates.PacketCompiler
