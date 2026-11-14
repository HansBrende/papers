import StatementsRowSpread
import TapeStorageRates.PaidInputs

/-!
# Finite transfer from bit cones to whole-row codes

Fixing a common index message, a raw-bit observation, and the exceptional
columns turns a cone-code fibre into a whole-row code over bit-vector entries.
The finite counting bound charges each observation once. It needs neither
linearity nor a sign condition on the whole-row cardinality exponent.
-/

namespace LeanBacklog.RowSpread

open Finset MergeDepth TapeStorageRates.PaidInputs
open scoped BigOperators

/-- Group a raw row-major bit word into its entries. -/
def entryWord {d b : ℕ} (x : Fin (d * d * b) → Bool) :
    Entry d → Fin b → Bool :=
  fun p t => x (matrixAddr p.1 p.2 t)

theorem entryWord_injective {d b : ℕ} :
    Function.Injective (entryWord (d := d) (b := b)) := by
  intro x y h
  funext p
  obtain ⟨⟨e,t⟩, rfl⟩ := (finProdFinEquiv : Fin (d*d) × Fin b ≃ _).surjective p
  obtain ⟨⟨i,j⟩, rfl⟩ := (finProdFinEquiv : Fin d × Fin d ≃ _).surjective e
  exact congrFun (congrFun h (i,j)) t

/-- The input-row quotient of an entry address is its first coordinate. -/
theorem matrixAddr_row {d b : ℕ} (i j : Fin d) (t : Fin b) :
    (matrixAddr i j t).val / (d * b) = i.val := by
  have hb : 0 < b := Nat.zero_lt_of_lt t.isLt
  have hd : 0 < d := Nat.zero_lt_of_lt i.isLt
  have hsmall : j.val * b + t.val < d * b := by
    calc
      _ < j.val * b + b := Nat.add_lt_add_left t.isLt _
      _ = (j.val + 1) * b := by ring
      _ ≤ d * b := Nat.mul_le_mul_right b (Nat.succ_le_of_lt j.isLt)
  rw [matrixAddr_val]
  have he : (i.val * d + j.val) * b + t.val =
      (d*b) * i.val + (j.val*b+t.val) := by ring
  rw [he, Nat.mul_add_div (Nat.mul_pos hd hb), Nat.div_eq_of_lt hsmall, Nat.add_zero]

/-- The existing exceptional-column counting theorem also works with an
arbitrary real exponent: round its bound down before applying it. -/
theorem WholeRowCardinalityBound.except {d w : ℕ} {α : Type*} [Fintype α]
    {a : ℝ} (hbound : WholeRowCardinalityBound d w α a)
    (ρ : Fin d → Finset (Fin d)) (E : Finset (Fin d))
    (C : Finset (Entry d → α)) (hρ : ∀ r, (ρ r).card ≤ w)
    (hC : IsWholeRowCodeExcept ρ E C) :
    (C.card : ℝ) ≤ (Fintype.card α : ℝ) ^ (d * E.card) *
      (Fintype.card α : ℝ) ^ a := by
  have hnat := exceptional_column_card_bound
    (fun ρ C hρ hC => Nat.le_floor (hbound ρ C hρ hC)) ρ E C hρ hC
  calc
    (C.card : ℝ) ≤ (Fintype.card α : ℝ) ^ (d * E.card) *
        (⌊(Fintype.card α : ℝ) ^ a⌋₊ : ℝ) := by exact_mod_cast hnat
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (by positivity)

/-- A common index-message fibre with the raw set `U` fixed is a whole-row
code after grouping bits into entries; only the specified columns remain
exceptional. No machine semantics or chosen zero fibre is assumed. -/
theorem entryWord_wholeRow_of_cones {d b : ℕ} {β : Type*}
    (ρ : Fin d → Finset (Fin d)) (E : Finset (Fin d))
    (U : Finset (Fin (d*d*b)))
    (I J : Fin (d*d*b) → Finset (Fin (d*d*b)))
    (hcover : ∀ ℓ, I ℓ ⊆ J ℓ ∪ U) (hrows : ConeRowsExcept J ρ E)
    (encoder : (Fin (d*d*b) → Bool) → β)
    (hindex : IsIndexCode encoder I (tposOf d b))
    (C : Finset (Fin (d*d*b) → Bool))
    (hmessage : ∀ x ∈ C, ∀ y ∈ C, encoder x = encoder y)
    (hraw : ∀ x ∈ C, ∀ y ∈ C, ∀ p ∈ U, x p = y p) :
    IsWholeRowCodeExcept ρ E (C.image entryWord) := by
  classical
  rw [wholeRowCode_iff]
  intro x hx y hy r hr hxy i
  obtain ⟨x₀, hx₀, rfl⟩ := mem_image.mp hx
  obtain ⟨y₀, hy₀, rfl⟩ := mem_image.mp hy
  funext t
  change x₀ (matrixAddr i r t) = y₀ (matrixAddr i r t)
  have hrec := hindex (matrixAddr r i t) x₀ y₀ (hmessage x₀ hx₀ y₀ hy₀)
  rw [tpos_matrixAddr] at hrec
  apply hrec
  intro p hp
  rcases mem_union.mp (hcover _ hp) with hpJ | hpU
  · obtain ⟨s, hs, hps⟩ := hrows r hr _ (matrixAddr_row r i t) p hpJ
    obtain ⟨⟨e,u⟩, rfl⟩ := (finProdFinEquiv : Fin (d*d) × Fin b ≃ _).surjective p
    obtain ⟨⟨s',j⟩, rfl⟩ := (finProdFinEquiv : Fin d × Fin d ≃ _).surjective e
    have he : s' = s := Fin.ext ((matrixAddr_row s' j u).symm.trans hps)
    subst s'
    exact congrFun (hxy s hs j) u
  · exact hraw x₀ hx₀ y₀ hy₀ p hpU

/-- Sum arbitrary real fibre bounds over a finite observation alphabet. -/
theorem card_le_of_real_fibre_bound {X β : Type*} [Fintype β] [DecidableEq β]
    (C : Finset X) (f : X → β) (A : ℝ)
    (hfibre : ∀ z, ((C.filter fun x => f x = z).card : ℝ) ≤ A) :
    (C.card : ℝ) ≤ Fintype.card β * A := by
  classical
  have hcount : ∑ z : β, (C.filter fun x => f x = z).card = C.card := by
    simpa using sum_card_fiberwise_eq_card_filter C (univ : Finset β) f
  calc
    (C.card : ℝ) = ∑ z : β, ((C.filter fun x => f x = z).card : ℝ) := by
      exact_mod_cast hcount.symm
    _ ≤ ∑ _z : β, A := sum_le_sum fun z _ => hfibre z
    _ = _ := by simp

/-- A finite index code pays for its message, the raw bits in `U`, and the
exceptional columns. The remaining cost is any valid whole-row exponent.
No positivity hypotheses on `d`, `b`, or `a` are needed. -/
theorem indexCode_length_le_of_wholeRowBound {d b w m : ℕ}
    (ρ : Fin d → Finset (Fin d)) (E : Finset (Fin d))
    (U : Finset (Fin (d*d*b)))
    (I J : Fin (d*d*b) → Finset (Fin (d*d*b))) (a : ℝ)
    (hcover : ∀ ℓ, I ℓ ⊆ J ℓ ∪ U) (hrows : ConeRowsExcept J ρ E)
    (hwidth : ∀ r, (ρ r).card ≤ w)
    (hbound : WholeRowCardinalityBound d w (Fin b → Bool) a)
    (encoder : (Fin (d*d*b) → Bool) → (Fin m → Bool))
    (hindex : IsIndexCode encoder I (tposOf d b)) :
    (d*d*b : ℝ) ≤ m + U.card + (d*E.card*b : ℕ) + (b:ℝ)*a := by
  classical
  let obs : (Fin (d*d*b) → Bool) → ((Fin m → Bool) × (U → Bool)) :=
    fun x => (encoder x, fun p => x p)
  let A : ℝ := (Fintype.card (Fin b → Bool) : ℝ) ^ (d*E.card) *
    (Fintype.card (Fin b → Bool) : ℝ) ^ a
  have hfibre (z : (Fin m → Bool) × (U → Bool)) :
      (((univ : Finset (Fin (d*d*b) → Bool)).filter fun x => obs x = z).card : ℝ)
        ≤ A := by
    let C := (univ : Finset (Fin (d*d*b) → Bool)).filter fun x => obs x = z
    have hf (x) (hx : x ∈ C) : obs x = z := (mem_filter.mp hx).2
    have hcode : IsWholeRowCodeExcept ρ E (C.image entryWord) :=
      entryWord_wholeRow_of_cones ρ E U I J hcover hrows encoder hindex C
        (fun x hx y hy => congrArg Prod.fst ((hf x hx).trans (hf y hy).symm))
        (fun x hx y hy p hp => congrFun
          (congrArg Prod.snd ((hf x hx).trans (hf y hy).symm)) ⟨p,hp⟩)
    have hcard := hbound.except ρ E (C.image entryWord) hwidth hcode
    simpa only [card_image_of_injective C entryWord_injective] using hcard
  have hcount := card_le_of_real_fibre_bound
    (univ : Finset (Fin (d*d*b) → Bool)) obs A hfibre
  have hp : (2 : ℝ) ^ (d*d*b : ℕ) ≤
      ((2 : ℝ)^m * (2:ℝ)^U.card) *
        (((2 : ℝ)^b)^(d*E.card) * ((2 : ℝ)^b)^a) := by
    simpa only [A, card_univ, Fintype.card_fun, Fintype.card_prod,
      Fintype.card_fin, Fintype.card_bool, Fintype.card_coe,
      Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hcount
  apply (Real.rpow_le_rpow_left_iff (by norm_num : (1:ℝ) < 2)).mp
  convert hp using 1 <;> simp only [Real.rpow_add (by norm_num : (0:ℝ) < 2),
    Real.rpow_natCast, Nat.cast_mul, Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  <;> ring

#print axioms entryWord_injective
#print axioms matrixAddr_row
#print axioms WholeRowCardinalityBound.except
#print axioms entryWord_wholeRow_of_cones
#print axioms card_le_of_real_fibre_bound
#print axioms indexCode_length_le_of_wholeRowBound

end LeanBacklog.RowSpread
