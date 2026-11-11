import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-! # Divisor counting and the actual average of a multiplied cyclic step -/

namespace SharedDecoders

open scoped BigOperators

theorem divisor_count_le_two_sqrt (n : ℕ) : n.divisors.card ≤ 2 * n.sqrt := by
  classical
  by_cases hn : n = 0
  · simp [hn]
  let lo := n.divisors.filter (fun e => e ≤ n.sqrt)
  let hi := n.divisors.filter (fun e => ¬e ≤ n.sqrt)
  have hlo : lo.card ≤ n.sqrt := by
    have hs : lo ⊆ Finset.Icc 1 n.sqrt := by
      intro e he
      obtain ⟨he, hel⟩ := Finset.mem_filter.mp he
      exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors he, hel⟩
    simpa using Finset.card_le_card hs
  have hinj : Set.InjOn (fun e => n / e) (↑hi : Set ℕ) := by
    intro e he f hf hef
    have he' := (Finset.mem_filter.mp he).1
    have hf' := (Finset.mem_filter.mp hf).1
    have heq := Nat.div_mul_cancel (Nat.dvd_of_mem_divisors he')
    have hfq := Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hf')
    have hp : 0 < n / e := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn)
      (Nat.dvd_of_mem_divisors he')) (Nat.pos_of_mem_divisors he')
    change n / e = n / f at hef
    apply Nat.eq_of_mul_eq_mul_left hp
    rw [heq, hef, hfq]
  have hhi : hi.card ≤ n.sqrt := by
    have hs : hi.image (fun e => n / e) ⊆ Finset.Icc 1 n.sqrt := by
      intro q hq
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hq
      obtain ⟨he, hel⟩ := Finset.mem_filter.mp he
      have hep := Nat.pos_of_mem_divisors he
      have hed := Nat.dvd_of_mem_divisors he
      have hqpos : 0 < n / e := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hed) hep
      refine Finset.mem_Icc.mpr ⟨hqpos, ?_⟩
      by_contra hq
      have hlarge := Nat.mul_le_mul (Nat.succ_le_of_lt (Nat.lt_of_not_ge hel))
        (Nat.succ_le_of_lt (Nat.lt_of_not_ge hq))
      have heq : e * (n / e) = n := Nat.mul_div_cancel' hed
      rw [heq] at hlarge
      exact (Nat.not_le_of_lt (Nat.lt_succ_sqrt n)) hlarge
    have := Finset.card_le_card hs
    rw [Finset.card_image_of_injOn hinj] at this
    simpa using this
  have hsplit : lo.card + hi.card = n.divisors.card := by
    exact Finset.card_filter_add_card_filter_not _
  omega

theorem count_multiples_of_dvd {n e : ℕ} (hn : 0 < n) (he : e ∣ n) :
    ((Finset.range n).filter (fun a => e ∣ a)).card = n / e := by
  have hep : 0 < e := Nat.pos_of_dvd_of_pos he hn
  have heq : n / e * e = n := Nat.div_mul_cancel he
  have hset : (Finset.range n).filter (fun a => e ∣ a) =
      (Finset.range (n / e)).image (fun a => a * e) := by
    ext a
    constructor
    · intro ha
      obtain ⟨ha, hed⟩ := Finset.mem_filter.mp ha
      obtain ⟨k, hk⟩ := hed
      refine Finset.mem_image.mpr ⟨k, ?_, by simpa [Nat.mul_comm] using hk.symm⟩
      apply Finset.mem_range.mpr
      apply (Nat.mul_lt_mul_right hep).mp
      rw [heq, Nat.mul_comm k e, ← hk]
      exact Finset.mem_range.mp ha
    · intro ha
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp ha
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr ?_, dvd_mul_left e k⟩
      rw [← heq]
      exact Nat.mul_lt_mul_of_pos_right (Finset.mem_range.mp hk) hep
  rw [hset, Finset.card_image_of_injective _ (fun x y h =>
    Nat.eq_of_mul_eq_mul_right hep h), Finset.card_range]

theorem sum_gcd_le_divisor_count (n : ℕ) (hn : 0 < n) :
    (∑ a ∈ Finset.range n, Nat.gcd n a) ≤ n * n.divisors.card := by
  have hpoint (a : ℕ) : Nat.gcd n a ≤
      ∑ e ∈ n.divisors, if e ∣ a then e else 0 := by
    have hgmem : Nat.gcd n a ∈ n.divisors :=
      Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left n a, hn.ne'⟩
    have h := Finset.single_le_sum (f := fun e => if e ∣ a then e else 0)
      (fun e _ => Nat.zero_le _) hgmem
    simpa [Nat.gcd_dvd_right n a] using h
  calc
    (∑ a ∈ Finset.range n, Nat.gcd n a) ≤
        ∑ a ∈ Finset.range n, ∑ e ∈ n.divisors, if e ∣ a then e else 0 :=
      Finset.sum_le_sum (fun a _ => hpoint a)
    _ = ∑ e ∈ n.divisors, ∑ a ∈ Finset.range n, if e ∣ a then e else 0 :=
      Finset.sum_comm
    _ = ∑ _e ∈ n.divisors, n := by
      apply Finset.sum_congr rfl
      intro e he
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul, count_multiples_of_dvd hn (Nat.dvd_of_mem_divisors he)]
      exact Nat.div_mul_cancel (Nat.dvd_of_mem_divisors he)
    _ = n * n.divisors.card := by simp [Nat.mul_comm]

theorem multiplied_gcd (d m a : ℕ) (hd : 0 < d) :
    Nat.gcd d (m * a) = Nat.gcd d m * Nat.gcd (d / Nat.gcd d m) a := by
  let g := Nat.gcd d m
  let n := d / g
  let t := m / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left m hd
  have hdg : g * n = d := Nat.mul_div_cancel' (Nat.gcd_dvd_left d m)
  have hmg : g * t = m := Nat.mul_div_cancel' (Nat.gcd_dvd_right d m)
  have hcop : n.Coprime t := Nat.coprime_div_gcd_div_gcd hg
  calc
    Nat.gcd d (m * a) = Nat.gcd (g * n) (g * (t * a)) := by rw [← mul_assoc, hdg, hmg]
    _ = g * Nat.gcd n (t * a) := Nat.gcd_mul_left g n (t * a)
    _ = g * Nat.gcd n a := by
      congr 1
      rw [Nat.gcd_comm n, hcop.symm.gcd_mul_left_cancel a, Nat.gcd_comm]

theorem sum_gcd_repeated (n k : ℕ) :
    (∑ a ∈ Finset.range (k * n), Nat.gcd n a) =
      k * (∑ a ∈ Finset.range n, Nat.gcd n a) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih]
    have heq : (∑ a ∈ Finset.range n, Nat.gcd n (k * n + a)) =
        ∑ a ∈ Finset.range n, Nat.gcd n a := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Nat.add_comm, Nat.gcd_add_mul_right_right]
    rw [heq, Nat.succ_mul]

/-- Exact reduction to the true uniform image of multiplication modulo d.
In particular it does not pretend a noninvertible cyclic multiplication is uniform. -/
theorem sum_multiplied_gcd (d m : ℕ) (hd : 0 < d) :
    (∑ a ∈ Finset.range d, Nat.gcd d (m * a)) =
      Nat.gcd d m ^ 2 *
        (∑ a ∈ Finset.range (d / Nat.gcd d m), Nat.gcd (d / Nat.gcd d m) a) := by
  let g := Nat.gcd d m
  let n := d / g
  have hdg : g * n = d := Nat.mul_div_cancel' (Nat.gcd_dvd_left d m)
  calc
    (∑ a ∈ Finset.range d, Nat.gcd d (m * a)) =
        g * (∑ a ∈ Finset.range d, Nat.gcd n a) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun a _ => multiplied_gcd d m a hd)
    _ = g * (g * (∑ a ∈ Finset.range n, Nat.gcd n a)) := by
      rw [← hdg, sum_gcd_repeated]
    _ = _ := by ring

theorem cast_sqrt_le_real_sqrt (n : ℕ) : (n.sqrt : ℝ) ≤ Real.sqrt n := by
  have h : (n.sqrt : ℝ) * n.sqrt ≤ (n : ℝ) := by exact_mod_cast Nat.sqrt_le n
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ n by positivity)
  have hn := Real.sqrt_nonneg (n : ℝ)
  nlinarith

/-- Uniform average gcd after multiplying a cyclic coordinate, with the
square-root loss of the actual multiplication kernel. -/
theorem sum_multiplied_gcd_le (d m : ℕ) (hd : 0 < d) (hm : 0 < m) :
    (∑ a ∈ Finset.range d, (Nat.gcd d (m * a) : ℝ)) ≤
      2 * d * Real.sqrt d * Real.sqrt m := by
  let g := Nat.gcd d m
  let n := d / g
  have hgp : 0 < g := Nat.gcd_pos_of_pos_left m hd
  have hgn : g * n = d := Nat.mul_div_cancel' (Nat.gcd_dvd_left d m)
  have hnp : 0 < n := Nat.pos_of_mul_pos_left (hgn.symm ▸ hd)
  have hcount := sum_gcd_le_divisor_count n hnp
  have hcount' : (∑ a ∈ Finset.range n, Nat.gcd n a) ≤ n * (2 * n.sqrt) :=
    hcount.trans (Nat.mul_le_mul_left n (divisor_count_le_two_sqrt n))
  have hnat : (∑ a ∈ Finset.range d, Nat.gcd d (m * a)) ≤
      g ^ 2 * (n * (2 * n.sqrt)) := by
    rw [sum_multiplied_gcd d m hd]
    exact Nat.mul_le_mul_left (g ^ 2) hcount'
  have hreal : (∑ a ∈ Finset.range d, (Nat.gcd d (m * a) : ℝ)) ≤
      (g : ℝ) ^ 2 * (n * (2 * n.sqrt)) := by exact_mod_cast hnat
  have hgnr : (g : ℝ) * n = d := by exact_mod_cast hgn
  have hgmr : (g : ℝ) ≤ m := by exact_mod_cast Nat.gcd_le_right d hm
  have hsqn := Real.sq_sqrt (show (0 : ℝ) ≤ n by positivity)
  have hsqg : ((g : ℝ) * Real.sqrt n) ^ 2 = (d : ℝ) * g := by
    rw [mul_pow, hsqn]
    nlinarith [congrArg (fun x : ℝ => x * g) hgnr]
  have hsqm : (Real.sqrt d * Real.sqrt m) ^ 2 = (d : ℝ) * m := by
    rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  have hroot : (g : ℝ) * Real.sqrt n ≤ Real.sqrt d * Real.sqrt m := by
    have hp : 0 ≤ (g : ℝ) * Real.sqrt n := by positivity
    have hp' : 0 ≤ Real.sqrt d * Real.sqrt m := by positivity
    have hc : (d : ℝ) * g ≤ d * m := mul_le_mul_of_nonneg_left hgmr (by positivity)
    nlinarith
  calc
    (∑ a ∈ Finset.range d, (Nat.gcd d (m * a) : ℝ)) ≤
        (g : ℝ) ^ 2 * (n * (2 * n.sqrt)) := hreal
    _ ≤ (g : ℝ) ^ 2 * (n * (2 * Real.sqrt n)) := by
      gcongr
      exact cast_sqrt_le_real_sqrt n
    _ = 2 * d * ((g : ℝ) * Real.sqrt n) := by
      rw [← hgnr]
      ring
    _ ≤ 2 * d * (Real.sqrt d * Real.sqrt m) := by gcongr
    _ = _ := by ring

/-- The estimate needed at every doubling scale, as an ordinary finite sum.
The term a=0 is included. -/
theorem mean_doubled_gcd_le (d r : ℕ) (hd : 0 < d) :
    (∑ a ∈ Finset.range d, (Nat.gcd d (2 ^ r * a) : ℝ)) / d ≤
      2 * Real.sqrt d * (Real.sqrt 2) ^ r := by
  have h := sum_multiplied_gcd_le d (2 ^ r) hd (by positivity)
  have hpow : Real.sqrt (2 ^ r : ℕ) = (Real.sqrt (2 : ℝ)) ^ r := by
    clear h
    push_cast
    induction r with
    | zero => norm_num
    | succ r ih => rw [pow_succ, Real.sqrt_mul (by positivity), ih, pow_succ]
  rw [hpow] at h
  apply (div_le_iff₀ (by exact_mod_cast hd : (0 : ℝ) < d)).mpr
  nlinarith

end SharedDecoders
