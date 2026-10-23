import BitWord.AddressGates
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.NormNum

namespace BitWord

/-- Number of bits needed to index the padded entry lanes. -/
def laneBits (h : ℕ) : ℕ := Nat.clog 2 h
/-- One extra low address bit makes the total address length even. -/
def dummyBits (h : ℕ) : ℕ := laneBits h % 2

def tailBits (h : ℕ) : ℕ := laneBits h + dummyBits h

def halfAddress (h : ℕ) : ℕ := h + tailBits h / 2

theorem tailBits_even (h : ℕ) : tailBits h % 2 = 0 := by
  unfold tailBits dummyBits
  omega

theorem halfAddress_double (h : ℕ) : 2 * halfAddress h = 2*h+tailBits h := by
  have := tailBits_even h
  unfold halfAddress
  omega

theorem tailBits_small {h : ℕ} (hh : h < 32) : tailBits h ≤ 6 := by
  have hu : laneBits h ≤ 5 := Nat.clog_le_of_le_pow (by norm_num; omega)
  unfold tailBits dummyBits
  omega

private theorem exponential_dominates {u : ℕ} (hu : 5 ≤ u) :
    5*(u+1) ≤ 2^u := by
  induction u, hu using Nat.le_induction with
  | base => decide
  | succ u hu ih => rw [Nat.pow_succ]; omega

theorem large_halfAddress {h : ℕ} (hh : 32 ≤ h) :
    3 * tailBits h ≤ halfAddress h := by
  have hu : 5 ≤ laneBits h := by
    have hm := Nat.clog_mono_right 2 hh
    norm_num [laneBits] at *
    exact hm
  have hp := Nat.pow_pred_clog_lt_self (b := 2) (by decide) (x := h) (by omega)
  have he := exponential_dominates hu
  have hu0 : 0 < laneBits h := by omega
  have hu1 : laneBits h = (laneBits h - 1)+1 := by omega
  have hp2 : 2 ^ laneBits h < 2*h := by
    rw [hu1, Nat.pow_succ]
    change 2^(laneBits h-1)*2 < 2*h
    change 2^(laneBits h-1) < h at hp
    omega
  have hw : tailBits h ≤ laneBits h+1 := by unfold tailBits dummyBits; omega
  have hpar := tailBits_even h
  unfold halfAddress
  omega

/-- A uniform arithmetic recipe; no size-dependent table or search. -/
def canonicalGates (h : ℕ) : List Gate :=
  if h < 32 then rotationGates h (tailBits h)
  else elevenGates h (halfAddress h) (tailBits h)

theorem canonicalGates_length (h : ℕ) : (canonicalGates h).length ≤ 13 := by
  unfold canonicalGates
  split_ifs with hh
  · rw [rotationGates_length]; have := tailBits_small hh; omega
  · rw [elevenGates_length]; decide

theorem canonicalGates_legal {h : ℕ} (hh : 0 < h) :
    ∀ g ∈ canonicalGates h, g.Legal (2*h+tailBits h) := by
  unfold canonicalGates
  split_ifs with hs
  · exact rotationGates_legal hh
  · rw [← halfAddress_double]
    exact elevenGates_legal (halfAddress_double h) (large_halfAddress (by omega))

theorem canonicalGates_correct {h x : ℕ} (hh : 0 < h)
    (hx : x < 2*h+tailBits h) :
    runGates (2*h+tailBits h) (canonicalGates h) x = headSwap h x := by
  unfold canonicalGates
  split_ifs with hs
  · exact rotationGates_correct hh hx
  · rw [← halfAddress_double] at hx ⊢
    exact elevenGates_correct (halfAddress_double h) (large_halfAddress (by omega)) hx

theorem lane_padding_bounds {h : ℕ} (hh : 0 < h) :
    h ≤ 2 ^ laneBits h ∧ 2 ^ laneBits h < 2*h := by
  refine ⟨Nat.le_pow_clog (by decide) h, ?_⟩
  by_cases h1 : h = 1
  · simp [h1, laneBits]
  have hu : 0 < laneBits h := Nat.clog_pos (by decide) (by omega)
  have hp := Nat.pow_pred_clog_lt_self (b := 2) (by decide) (x := h) (by omega)
  change 2^(laneBits h-1) < h at hp
  have he : laneBits h = laneBits h - 1 + 1 := by omega
  rw [he, Nat.pow_succ]
  omega

theorem tail_padding_bound {h : ℕ} (hh : 0 < h) : 2 ^ tailBits h < 4*h := by
  have hp := (lane_padding_bounds hh).2
  unfold tailBits dummyBits
  rw [Nat.pow_add]
  have hm : laneBits h % 2 = 0 ∨ laneBits h % 2 = 1 := by omega
  rcases hm with hm | hm
  · rw [hm]; simp only [Nat.pow_zero, Nat.mul_one]; omega
  · rw [hm]; simp only [Nat.pow_one]; omega

end BitWord
