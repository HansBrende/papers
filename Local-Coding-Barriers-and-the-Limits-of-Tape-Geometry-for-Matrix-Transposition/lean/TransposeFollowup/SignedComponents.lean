import TransposeFollowup.SignedPairData
import TransposeFollowup.DenseOverlapScan

/-! Bounds on the two nonnegative components, not merely their difference.
These are arithmetic specifications for the row implementation; this file
neither loads component words nor supplies an unimplemented native update. -/

namespace TransposeFollowup
namespace SignedComponents

set_option autoImplicit false

structure Pair where
  positive : ℕ
  negative : ℕ
  deriving DecidableEq

def Pair.denote (p : Pair) : ℤ := (p.positive : ℤ) - p.negative

def Pair.mass (p : Pair) : ℕ := p.positive + p.negative

def Pair.zero : Pair := ⟨0, 0⟩

def Pair.ofInt (z : ℤ) : Pair := ⟨z.toNat, (-z).toNat⟩

def Pair.add (p q : Pair) : Pair := ⟨p.positive+q.positive, p.negative+q.negative⟩

def Pair.neg (p : Pair) : Pair := ⟨p.negative, p.positive⟩

def Pair.mul (p q : Pair) : Pair :=
  ⟨p.positive*q.positive+p.negative*q.negative,
    p.positive*q.negative+p.negative*q.positive⟩

def Pair.scale (n : ℕ) (p : Pair) : Pair := ⟨n*p.positive, n*p.negative⟩

def Pair.less (p q : Pair) : Bool :=
  decide (p.positive + q.negative < q.positive + p.negative)

theorem less_spec (p q : Pair) : p.less q = true ↔ p.denote < q.denote := by
  simp only [Pair.less, decide_eq_true_eq, Pair.denote]
  omega

theorem ofInt_denote (z : ℤ) : (Pair.ofInt z).denote = z := by
  simp only [Pair.ofInt, Pair.denote]
  omega

theorem ofInt_mass (z : ℤ) : (Pair.ofInt z).mass = z.natAbs := by
  cases z <;> simp [Pair.ofInt, Pair.mass]

theorem add_denote (p q : Pair) : (p.add q).denote = p.denote + q.denote := by
  simp only [Pair.add, Pair.denote, Nat.cast_add]
  ring

theorem add_mass (p q : Pair) : (p.add q).mass = p.mass + q.mass := by
  simp only [Pair.add, Pair.mass]
  omega

theorem neg_denote (p : Pair) : p.neg.denote = -p.denote := by
  simp [Pair.neg, Pair.denote]

theorem neg_mass (p : Pair) : p.neg.mass = p.mass := by
  simp [Pair.neg, Pair.mass, Nat.add_comm]

theorem mul_denote (p q : Pair) : (p.mul q).denote = p.denote * q.denote := by
  simp only [Pair.mul, Pair.denote, Nat.cast_add, Nat.cast_mul]
  ring

theorem mul_mass (p q : Pair) : (p.mul q).mass = p.mass * q.mass := by
  simp only [Pair.mul, Pair.mass]
  ring

theorem scale_denote (n : ℕ) (p : Pair) : (p.scale n).denote = (n : ℤ) * p.denote := by
  simp only [Pair.scale, Pair.denote, Nat.cast_mul]
  ring

theorem scale_mass (n : ℕ) (p : Pair) : (p.scale n).mass = n * p.mass := by
  simp only [Pair.scale, Pair.mass]
  ring

def scan (left right : Pair) : ℕ → Pair × Pair
  | 0 => (left, Pair.zero)
  | j+1 => let v := scan left right j; (v.1.add left, v.2.add right)

theorem scan_eq (left right : Pair) (j : ℕ) :
    scan left right j = (left.scale (j+1), right.scale j) := by
  induction j with
  | zero => cases left; cases right; simp [scan, Pair.zero, Pair.scale]
  | succ j ih =>
    simp only [scan, ih, Pair.add, Pair.scale]
    congr 2 <;> ring

theorem scan_denote (left right : Pair) (j : ℕ) :
    ((scan left right j).1.denote, (scan left right j).2.denote) =
      crossingScan left.denote right.denote j := by
  rw [scan_eq, scale_denote, scale_denote, crossingScan_eq]
  simp

/-- Linear mass in each increment yields quadratic component bounds over
n target cells, even when the two signs nearly cancel. -/
theorem scan_mass_bounds (E n j : ℕ) (left right : Pair)
    (hj : j ≤ n) (hl : left.mass ≤ E*(n+1)) (hr : right.mass ≤ E*(n+1)) :
    (scan left right j).1.mass ≤ E*(n+1)^2 ∧
    (scan left right j).2.mass ≤ E*(n+1)^2 := by
  rw [scan_eq, scale_mass, scale_mass]
  constructor
  · calc
      _ ≤ (n+1)*(E*(n+1)) := Nat.mul_le_mul (by omega) hl
      _ = _ := by ring
  · calc
      _ ≤ (n+1)*(E*(n+1)) := Nat.mul_le_mul (by omega) hr
      _ = _ := by ring

/-- Control of total mass bounds BOTH cross-sums used by the native caller. -/
theorem comparison_fit (p q : Pair) (m : ℕ)
    (hp : p.mass < 2^m) (hq : q.mass < 2^m) :
    p.positive+q.negative < 2^(m+1) ∧ q.positive+p.negative < 2^(m+1) := by
  apply SignedPair.cross_sums_fit
  all_goals dsimp [Pair.mass] at hp hq; omega

theorem component_size (p : Pair) (C n : ℕ) (h : p.mass ≤ C*(n+1)^2) :
    p.positive.size ≤ C.size + 2*(n+1).size+1 ∧
    p.negative.size ≤ C.size + 2*(n+1).size+1 := by
  constructor <;> apply natSize_le_poly
  · exact (show p.positive ≤ p.mass by dsimp [Pair.mass]; omega).trans h
  · exact (show p.negative ≤ p.mass by dsimp [Pair.mass]; omega).trans h

end SignedComponents
end TransposeFollowup
