import SharedDecoders.CapacityRuns
import SharedDecoders.GcdAverage

/-! # The actual finite cyclic means used by the capacity estimate -/

namespace SharedDecoders

open scoped BigOperators
open CapacityRuns

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

theorem sum_changeCount_eq (p : G → Bool) :
    (∑ s : G, changeCount p s) =
      2 * Fintype.card {x // p x = true} * Fintype.card {x // p x = false} := by
  classical
  let e : (Σ s : G, {x // p (x + s) ≠ p x}) ≃ {z : G × G // p z.1 ≠ p z.2} :=
    { toFun := fun z => ⟨(z.2.val, z.2.val + z.1), z.2.property.symm⟩
      invFun := fun z => ⟨z.1.2 - z.1.1, ⟨z.1.1, by simpa using z.2.symm⟩⟩
      left_inv := by
        rintro ⟨s, x, hx⟩
        have hidx : x + s - x = s := by abel
        apply Sigma.ext hidx
        apply (Subtype.heq_iff_coe_eq (fun y => by dsimp only; rw [hidx])).2
        rfl
      right_inv := by rintro ⟨⟨x, y⟩, hxy⟩; simp }
  have he := Fintype.card_congr e
  rw [Fintype.card_sigma] at he
  change (∑ s : G, changeCount p s) = _ at he
  rw [he, Fintype.card_subtype]
  let B := Finset.univ.filter (fun x : G => p x = true)
  let A := Finset.univ.filter (fun x : G => p x = false)
  have hset : Finset.univ.filter (fun z : G × G => p z.1 ≠ p z.2) =
      B ×ˢ A ∪ A ×ˢ B := by
    ext z
    rcases z with ⟨x, y⟩
    cases hx : p x <;> cases hy : p y <;> simp [A, B, hx, hy]
  have hd : Disjoint (B ×ˢ A) (A ×ˢ B) := by
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    have hx := (Finset.mem_filter.mp (Finset.mem_product.mp hz).1).2
    have hx' := (Finset.mem_filter.mp (Finset.mem_product.mp hz').1).2
    simp [hx] at hx'
  rw [hset, Finset.card_union_of_disjoint hd, Finset.card_product, Finset.card_product]
  simp only [A, B, Fintype.card_subtype]
  ring

theorem two_mul_sum_changeCount_le (p : G → Bool) :
    2 * (∑ s : G, changeCount p s) ≤ Fintype.card G * Fintype.card G := by
  classical
  let t := Fintype.card {x // p x = true}
  let f := Fintype.card {x // p x = false}
  have hsum : t + f = Fintype.card G := by
    have hh := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun x : G => p x = true)
    simpa [t, f, Fintype.card_subtype] using hh
  rw [sum_changeCount_eq]
  change 2 * (2 * t * f) ≤ Fintype.card G * Fintype.card G
  have hsq : (0 : ℤ) ≤ ((t : ℤ) - f) ^ 2 := sq_nonneg _
  exact_mod_cast (show (2 : ℤ) * (2 * t * f) ≤ Fintype.card G * Fintype.card G by
    have hsum' : (t : ℤ) + f = Fintype.card G := by exact_mod_cast hsum
    nlinarith)

variable {d : ℕ} [NeZero d]

theorem mean_changeCount_le (p : ZMod d → Bool) :
    (∑ s : ZMod d, (changeCount p s : ℝ)) / d ≤ (d : ℝ) / 2 := by
  have hh := two_mul_sum_changeCount_le p
  rw [ZMod.card] at hh
  have hreal : 2 * (∑ s : ZMod d, (changeCount p s : ℝ)) ≤ (d : ℝ) * d := by
    exact_mod_cast hh
  apply (div_le_iff₀ (by exact_mod_cast NeZero.pos d : (0 : ℝ) < d)).2
  nlinarith

theorem sum_zmod_eq_sum_range {B : Type*} [AddCommMonoid B] (f : ZMod d → B) :
    (∑ s : ZMod d, f s) = ∑ a ∈ Finset.range d, f (a : ZMod d) := by
  classical
  symm
  apply Finset.sum_bij (fun (a : ℕ) _ => (a : ZMod d))
  · intro a _
    exact Finset.mem_univ _
  · intro a ha b hb hab
    have hh := congrArg ZMod.val hab
    simpa only [ZMod.val_natCast_of_lt (Finset.mem_range.mp ha),
      ZMod.val_natCast_of_lt (Finset.mem_range.mp hb)] using hh
  · intro s _
    exact ⟨s.val, Finset.mem_range.mpr s.val_lt, ZMod.natCast_zmod_val s⟩
  · intros
    rfl

omit [NeZero d] in
theorem gcd_doubled_natCast_val (r a : ℕ) :
    Nat.gcd d ((2 ^ r) • (a : ZMod d)).val = Nat.gcd d (2 ^ r * a) := by
  rw [nsmul_eq_mul, ← Nat.cast_mul, ZMod.val_natCast, Nat.gcd_comm d]
  exact (Nat.gcd_rec d (2 ^ r * a)).symm

theorem mean_doubled_gcd_zmod_le (r : ℕ) :
    (∑ a : ZMod d, (Nat.gcd d ((2 ^ r) • a).val : ℝ)) / d ≤
      2 * Real.sqrt d * (Real.sqrt 2) ^ r := by
  rw [sum_zmod_eq_sum_range]
  simp only [gcd_doubled_natCast_val]
  exact mean_doubled_gcd_le d r (NeZero.pos d)

end SharedDecoders
