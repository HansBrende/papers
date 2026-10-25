import Mathlib

/-! # Canonical monotone buckets with a uniform minimum size

All buckets contain `d/B` consecutive rows. The final bucket absorbs the
remainder. This gives exactly the lower fibre-size bound used by the
independent-rectangle argument, without a partition-existence premise.
-/

namespace LeanMachine.CanonicalBuckets

open Classical Finset
set_option autoImplicit false

/-- Clipped quotient buckets on a finite interval. -/
def bucket {d B : ℕ} (hB : 0 < B) (i : Fin d) : Fin B :=
  ⟨min (i.val / (d / B)) (B - 1), lt_of_le_of_lt (Nat.min_le_right _ _) (by omega)⟩

theorem bucket_monotone {d B : ℕ} (hB : 0 < B) : Monotone (bucket (d := d) hB) := by
  intro i j hij
  exact min_le_min_right _ (Nat.div_le_div_right hij)

/-- Every bucket has at least `d/B` members whenever the buckets are nonempty. -/
theorem bucket_fibre_card {d B : ℕ} (hB : 0 < B) (hBd : B ≤ d) (a : Fin B) :
    d / B ≤ (univ.filter (fun i => bucket (d := d) hB i = a)).card := by
  have hq : 0 < d / B := Nat.div_pos hBd hB
  have htotal : B * (d / B) ≤ d := Nat.mul_div_le d B
  let f : Fin (d / B) → {i : Fin d // bucket hB i = a} := fun j =>
    ⟨⟨a.val * (d / B) + j.val, by
      have hstep : (a.val + 1) * (d / B) ≤ B * (d / B) :=
        Nat.mul_le_mul_right _ (by omega)
      nlinarith [j.isLt]⟩, by
      apply Fin.ext
      dsimp [bucket]
      have hdiv : (a.val * (d / B) + j.val) / (d / B) = a.val := by
        rw [Nat.mul_comm a.val (d / B), Nat.mul_add_div hq,
          Nat.div_eq_of_lt j.isLt, add_zero]
      rw [hdiv, Nat.min_eq_left (by omega)]⟩
  have hf : Function.Injective f := by
    intro i j hij
    have hval := congrArg (fun x => x.val.val) hij
    dsimp [f] at hval
    apply Fin.ext
    omega
  have hcard := Fintype.card_le_of_injective f hf
  simpa [Fintype.card_subtype] using hcard

end LeanMachine.CanonicalBuckets
