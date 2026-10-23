import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.SplitIfs

/-! Address-position permutations used by the bit-to-word reduction.
All maps below describe movement of source positions, numbered from the
most significant end. The identities hold for arbitrary address contents. -/
namespace BitWord

/-- Exchange the final two fields of `k` positions in an `N`-position address. -/
def suffixSwap (N k x : ℕ) : ℕ :=
  if x < N - 2*k then x else if x < N-k then x+k else x-k

/-- Exchange the first and last `w` positions, preserving internal order. -/
def endSwap (N w x : ℕ) : ℕ :=
  if x < w then N-w+x else if x < N-w then x else x-(N-w)

/-- Exchange the first two fields of `h` positions. -/
def headSwap (h x : ℕ) : ℕ :=
  if x < h then x+h else if x < 2*h then x-h else x

 theorem suffixSwap_lt {N k x : ℕ} (hk : 2*k ≤ N) (hx : x < N) :
    suffixSwap N k x < N := by
  unfold suffixSwap
  split_ifs <;> omega

 theorem suffixSwap_involutive {N k x : ℕ} (hk : 2*k ≤ N) (hx : x < N) :
    suffixSwap N k (suffixSwap N k x) = x := by
  unfold suffixSwap
  split_ifs <;> omega

 theorem endSwap_lt {N w x : ℕ} (hw : 2*w ≤ N) (hx : x < N) :
    endSwap N w x < N := by
  unfold endSwap
  split_ifs <;> omega

 theorem endSwap_involutive {N w x : ℕ} (hw : 2*w ≤ N) (hx : x < N) :
    endSwap N w (endSwap N w x) = x := by
  unfold endSwap
  split_ifs <;> omega

theorem suffixSwap_cases (N k x : ℕ) :
    (x < N-2*k ∧ suffixSwap N k x = x) ∨
    (N-2*k ≤ x ∧ x < N-k ∧ suffixSwap N k x = x+k) ∨
    (N-k ≤ x ∧ suffixSwap N k x = x-k) := by
  unfold suffixSwap
  split_ifs <;> omega

/-- The five suffix exchanges implement an end-block exchange. -/
theorem five_suffix_end {n w x : ℕ} (hw : 3*w ≤ n) (hx : x < 2*n) :
    suffixSwap (2*n) n
      (suffixSwap (2*n) (n-w)
        (suffixSwap (2*n) w
          (suffixSwap (2*n) (n-w) (suffixSwap (2*n) n x)))) =
    endSwap (2*n) w x := by
  have h1 := suffixSwap_cases (2*n) n x
  have h2 := suffixSwap_cases (2*n) (n-w) (suffixSwap (2*n) n x)
  have h3 := suffixSwap_cases (2*n) w
    (suffixSwap (2*n) (n-w) (suffixSwap (2*n) n x))
  have h4 := suffixSwap_cases (2*n) (n-w)
    (suffixSwap (2*n) w (suffixSwap (2*n) (n-w) (suffixSwap (2*n) n x)))
  have h5 := suffixSwap_cases (2*n) n
    (suffixSwap (2*n) (n-w)
      (suffixSwap (2*n) w (suffixSwap (2*n) (n-w) (suffixSwap (2*n) n x))))
  unfold endSwap
  split_ifs <;> omega

/-- Moving the tail to the front by end exchange conjugates a suffix
transpose to the desired row/column exchange. -/
theorem conjugate_head {h w x : ℕ} (hw : w ≤ h) (hx : x < 2*h+w) :
    endSwap (2*h+w) w
      (suffixSwap (2*h+w) h (endSwap (2*h+w) w x)) = headSwap h x := by
  unfold endSwap suffixSwap headSwap
  split_ifs <;> omega

/-- Five exchanges, one suffix transpose, and the same five exchanges. -/
def elevenSuffix (h n w : ℕ) (x : ℕ) : ℕ :=
  let Q := fun y => suffixSwap (2*n) n
    (suffixSwap (2*n) (n-w)
      (suffixSwap (2*n) w
        (suffixSwap (2*n) (n-w) (suffixSwap (2*n) n y))))
  Q (suffixSwap (2*n) h (Q x))

theorem elevenSuffix_eq_head {h n w x : ℕ} (hn : 2*n = 2*h+w)
    (hw : 3*w ≤ n) (hx : x < 2*n) :
    elevenSuffix h n w x = headSwap h x := by
  have hwh : w ≤ h := by omega
  have hsw : 2*w ≤ 2*n := by omega
  have hsh : 2*h ≤ 2*n := by omega
  dsimp only [elevenSuffix]
  rw [five_suffix_end hw hx]
  rw [five_suffix_end hw (suffixSwap_lt hsh (endSwap_lt hsw hx))]
  rw [hn]
  exact conjugate_head hwh (by omega)

end BitWord
