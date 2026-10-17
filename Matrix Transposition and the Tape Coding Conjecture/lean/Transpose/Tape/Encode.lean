import Transpose.Tape.Defs

/-!
# Facts about the encoding

* Bit positions of `encode` for general entry width `b`.
* The transposition of bit positions, `tpos`.
* The encodings of `n × n` matrices with `b`-bit entries are exactly the words of length `n²b`.
* `readInput` at natural positions; `readInput_eq_of_nth`: inputs of equal length that agree at a
  read position read the same symbol there.
-/

namespace Transpose.Tape.Impl

open Transpose

/-- The frozen `nth` is list indexing. -/
theorem nth_eq_getElem? : ∀ (l : List Bool) (i : ℕ), nth l i = l[i]?
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, i + 1 => nth_eq_getElem? l i

theorem nth_eq_none_of_le {l : List Bool} {i : ℕ} (h : l.length ≤ i) : nth l i = none := by
  rw [nth_eq_getElem?]; exact List.getElem?_eq_none h

theorem length_encode (n b : ℕ) (A : Matrix) : (encode n b A).length = n * n * b := by
  unfold encode
  rw [Sanity.length_concatUpTo _ (n * b)]
  · rw [Nat.mul_assoc]
  · intro i
    rw [Sanity.length_concatUpTo _ b]
    intro j
    rw [Sanity.length_concatUpTo _ 1]
    · simp
    · intro _; rfl

/-- Decomposition of a bit position `d < n²b` as `(i n + j) b + t`. -/
theorem pos_decomp {n b d : ℕ} (hd : d < n * n * b) :
    d / b / n < n ∧ d / b % n < n ∧ d % b < b ∧ d = (d / b / n * n + d / b % n) * b + d % b := by
  have hb : 0 < b := by
    rcases Nat.eq_zero_or_pos b with h | h
    · subst h; simp at hd
    · exact h
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp at hd
    · exact h
  have he : d / b < n * n := by
    rw [Nat.div_lt_iff_lt_mul hb]; exact hd
  refine ⟨?_, Nat.mod_lt _ hn, Nat.mod_lt _ hb, ?_⟩
  · rw [Nat.div_lt_iff_lt_mul hn]; exact he
  · rw [Nat.div_add_mod' (d / b) n, Nat.div_add_mod' d b]

/-- Bit `d` of the encoding. -/
theorem nth_encode_pos {n b d : ℕ} (A : Matrix) (hd : d < n * n * b) :
    nth (encode n b A) d = some (A (d / b / n) (d / b % n) (d % b)) := by
  obtain ⟨hi, hj, ht, hdec⟩ := pos_decomp hd
  conv_lhs => rw [hdec]
  exact nth_encode A _ _ _ hi hj ht

theorem nth_encode_ge {n b d : ℕ} (A : Matrix) (hd : n * n * b ≤ d) :
    nth (encode n b A) d = none :=
  nth_eq_none_of_le (by rw [length_encode]; exact hd)

theorem tpos_spec {n b i j t : ℕ} (hj : j < n) (ht : t < b) :
    tpos n b ((i * n + j) * b + t) = (j * n + i) * b + t := by
  have hb : 0 < b := Nat.lt_of_le_of_lt (Nat.zero_le _) ht
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) hj
  have h1 : ((i * n + j) * b + t) / b = i * n + j := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hb, Nat.div_eq_of_lt ht, Nat.zero_add]
  have h2 : ((i * n + j) * b + t) % b = t := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht]
  have h3 : (i * n + j) % n = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  have h4 : (i * n + j) / n = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hj, Nat.zero_add]
  unfold tpos
  rw [h1, h2, h3, h4]

theorem tpos_lt {n b d : ℕ} (hd : d < n * n * b) : tpos n b d < n * n * b := by
  obtain ⟨hi, hj, ht, hdec⟩ := pos_decomp hd
  have := tpos_spec (i := d / b / n) hj ht
  rw [← hdec] at this
  rw [this]
  calc (d / b % n * n + d / b / n) * b + d % b < (d / b % n * n + d / b / n) * b + b :=
        Nat.add_lt_add_left ht _
    _ = (d / b % n * n + d / b / n + 1) * b := by ring
    _ ≤ (d / b % n * n + n) * b := by
        apply Nat.mul_le_mul_right; omega
    _ = (d / b % n + 1) * n * b := by ring
    _ ≤ n * n * b := by
        apply Nat.mul_le_mul_right; apply Nat.mul_le_mul_right; omega

/-- The transposed output holds input bit `d` at position `tpos n b d`. -/
theorem nth_encode_transpose_tpos {n b d : ℕ} (A : Matrix) (hd : d < n * n * b) :
    nth (encode n b (transpose A)) (tpos n b d) = nth (encode n b A) d := by
  obtain ⟨hi, hj, ht, hdec⟩ := pos_decomp hd
  have htp := tpos_spec (i := d / b / n) hj ht
  rw [← hdec] at htp
  rw [htp, nth_encode _ _ _ _ hj hi ht, nth_encode_pos A hd]
  rfl

theorem matrixInputs_eq (n b : ℕ) : matrixInputs n b = inputsOfLength (n * n * b) := by
  ext w
  constructor
  · rintro ⟨A, rfl⟩
    exact length_encode n b A
  · intro hw
    simp only [inputsOfLength, Set.mem_ofPred_eq] at hw
    refine ⟨fun i j t => (nth w ((i * n + j) * b + t)).getD false, ?_⟩
    apply List.ext_getElem?
    intro d
    rw [← nth_eq_getElem?, ← nth_eq_getElem?]
    rcases Nat.lt_or_ge d (n * n * b) with hd | hd
    · rw [nth_encode_pos _ hd, ← (pos_decomp hd).2.2.2]
      rw [nth_eq_getElem?, List.getElem?_eq_getElem (by rw [hw]; exact hd)]
      simp
    · rw [nth_encode_ge _ hd, nth_eq_none_of_le (by rw [hw]; exact hd)]

/-- `readInput` at a natural position is `nth`. -/
theorem readInput_natCast (w : List Bool) (d : ℕ) : readInput w (d : ℤ) = nth w d := by
  simp [readInput]

/-- `readInput` outside `[0, |w|)` is `none`. -/
theorem readInput_eq_none {w : List Bool} {p : ℤ} (hp : p < 0 ∨ (w.length : ℤ) ≤ p) :
    readInput w p = none := by
  unfold readInput
  rcases hp with hp | hp
  · simp [hp]
  · rw [ite_eq_right (by omega)]
    apply nth_eq_none_of_le
    omega

/-- Two inputs of the same length `L` read the same symbol at `p` if they agree at `p` whenever `p`
is a position of the input. -/
theorem readInput_eq_of_nth {L : ℕ} {w w' : List Bool} (hw : w.length = L) (hw' : w'.length = L)
    {p : ℤ} (h : ∀ d : ℕ, (d : ℤ) = p → d < L → nth w d = nth w' d) :
    readInput w p = readInput w' p := by
  rcases lt_or_ge p 0 with hneg | hnn
  · rw [readInput_eq_none (Or.inl hneg), readInput_eq_none (Or.inl hneg)]
  obtain ⟨d, rfl⟩ : ∃ d : ℕ, p = d := ⟨p.toNat, by omega⟩
  rcases lt_or_ge d L with hdL | hdL
  · rw [readInput_natCast, readInput_natCast]; exact h d rfl hdL
  · rw [readInput_eq_none (Or.inr (by rw [hw]; exact_mod_cast hdL)),
      readInput_eq_none (Or.inr (by rw [hw']; exact_mod_cast hdL))]

end Transpose.Tape.Impl
