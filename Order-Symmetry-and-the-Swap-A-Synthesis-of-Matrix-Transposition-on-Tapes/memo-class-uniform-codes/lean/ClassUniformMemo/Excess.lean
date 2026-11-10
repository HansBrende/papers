import ClassUniformMemo.Fields
import ClassUniformMemo.BlowUp

/-!
# A family whose excess over the interval value grows

Blowing up the code of dimension `25` for the classes `{0, 1, 3}` and `{2, 4, 5}` of `ZMod 6`
(`ClassUniformMemo.exists_code_of_three_ne_zero`) gives, for every `k ≥ 1` and over every field in
which `3 ≠ 0`, a class-uniform code of dimension `25 * k ^ 2` on `ZMod (6 * k)` for a colouring
with `2 * k` classes (`exists_blowUp_code`).  The interval value `((6 * k) ^ 2 + (6 * k) * (2 * k)) / 2`
is `24 * k ^ 2`, so the excess is `k ^ 2` and grows with `k` (`two_mul_finrank_blowUp_code`).  The
number of classes grows with `k` as well: the excess is `d * M / 12` for `d = 6 * k` and `M = 2 * k`,
of the same order as the term `d * M / 2` of the interval value.

The decoders of these codes must know the position `c mod k`: merging the classes over the position
gives two classes forming four cyclic intervals, and by Theorem TP every code for them has dimension
less than `25 * k ^ 2` once `k ≥ 2` (`finrank_lt_of_mergedCls`).

## Main results

* `blowCls_surjective`: the blown-up colouring uses all `2 * k` classes.
* `exists_blowUp_code`: the codes of dimension `25 * k ^ 2`.
* `two_mul_finrank_blowUp_code`: twice their dimension exceeds the interval value by `2 * k ^ 2`.
* `two_mul_finrank_le_merged`, `finrank_lt_of_mergedCls`: the bound for the two merged classes.
-/

namespace ClassUniformMemo

open Module SwapRigidity

variable {k : ℕ} [NeZero k]

/-- The blown-up colouring of `ZMod (6 * k)` uses all `2 * k` classes of `Bool × Fin k`. -/
theorem blowCls_surjective : Function.Surjective (blowCls k aperiodicCls) := by
  rintro ⟨b, u⟩
  refine ⟨emb k (if b then 0 else 2) u, ?_⟩
  simp only [blowCls, hi_emb, lo_emb, Prod.mk.injEq, and_true]
  cases b <;> decide

omit [NeZero k] in
/-- The blown-up colouring has `2 * k` classes. -/
theorem card_blowClasses : Fintype.card (Bool × Fin k) = 2 * k := by
  simp

/-- **Codes of dimension `25 * k ^ 2` for `2 * k` classes on `ZMod (6 * k)`**, over every field in
which `3 ≠ 0`: the blow-ups of the code of dimension `25`. -/
theorem exists_blowUp_code (F : Type*) [Field F] (h3 : (3 : F) ≠ 0) (k : ℕ) [NeZero k] :
    ∃ 𝒳 : Submodule F (Matrix (ZMod (6 * k)) (ZMod (6 * k)) F),
      IsClassUniformCode (blowCls k aperiodicCls) 𝒳 ∧ finrank F 𝒳 = 25 * k ^ 2 := by
  obtain ⟨𝒳₀, h𝒳₀, hdim⟩ := exists_code_of_three_ne_zero F h3
  refine ⟨blowUp k 𝒳₀, isClassUniformCode_blowUp h𝒳₀, ?_⟩
  rw [finrank_blowUp, hdim]
  ring

/-- **The excess grows.**  Twice the dimension of the codes of `exists_blowUp_code` exceeds the
interval value `d ^ 2 + d * M`, for `d = 6 * k` and `M = 2 * k` classes, by `2 * k ^ 2`. -/
theorem two_mul_finrank_blowUp_code (F : Type*) [Field F] (h3 : (3 : F) ≠ 0) (k : ℕ) [NeZero k] :
    ∃ 𝒳 : Submodule F (Matrix (ZMod (6 * k)) (ZMod (6 * k)) F),
      IsClassUniformCode (blowCls k aperiodicCls) 𝒳 ∧
        2 * finrank F 𝒳 = (6 * k) ^ 2 + (6 * k) * Fintype.card (Bool × Fin k) + 2 * k ^ 2 := by
  obtain ⟨𝒳, h𝒳, hdim⟩ := exists_blowUp_code F h3 k
  refine ⟨𝒳, h𝒳, ?_⟩
  rw [hdim, card_blowClasses]
  ring

/-! ### The two merged classes -/

variable (k) in
/-- The merged colouring of `ZMod (6 * k)`: the class of the block, forgetting the position.  It
has two classes, and they form four cyclic intervals. -/
def mergedCls (c : ZMod (6 * k)) : Bool :=
  aperiodicCls (hi k c)

variable (k) in
/-- The rows at which the merged colouring changes class: the first rows of the blocks `0`, `2`,
`3` and `4`. -/
def mergedChanges : Finset (ZMod (6 * k)) :=
  {emb k 0 0, emb k 2 0, emb k 3 0, emb k 4 0}

/-- Outside `mergedChanges`, the merged colouring does not change from one row to the next. -/
theorem mergedCls_sub_one (c : ZMod (6 * k)) (hc : c ∉ mergedChanges k) :
    mergedCls k (c - 1) = mergedCls k c := by
  by_cases hu : (lo c).val = 0
  · have hc' : c = emb k (hi k c) 0 := by
      conv_lhs => rw [← emb_hi_lo c]
      congr 1
      exact Fin.ext hu
    have hblock : hi k c ≠ 0 ∧ hi k c ≠ 2 ∧ hi k c ≠ 3 ∧ hi k c ≠ 4 := by
      refine ⟨?_, ?_, ?_, ?_⟩ <;> intro ha <;> apply hc <;> rw [hc', ha] <;> simp [mergedChanges]
    simp only [mergedCls, hi_sub_one_of_lo_eq_zero c hu]
    generalize hi k c = a at hblock
    revert a
    decide
  · simp only [mergedCls, hi_sub_one_of_lo_ne_zero c hu]

/-- **Theorem TP for the merged classes**: every class-uniform code for them has
`2 * dim 𝒳 ≤ (6 * k) ^ 2 + (6 * k) * 4`. -/
theorem two_mul_finrank_le_merged {F : Type*} [Field F]
    {𝒳 : Submodule F (Matrix (ZMod (6 * k)) (ZMod (6 * k)) F)}
    (h : IsClassUniformCode (mergedCls k) 𝒳) :
    2 * finrank F 𝒳 ≤ (6 * k) ^ 2 + (6 * k) * 4 := by
  have hcard : (mergedChanges k).card ≤ 4 := by
    simp only [mergedChanges]
    refine (Finset.card_insert_le _ _).trans ?_
    refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
    refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
    simp
  have hTP := h.two_mul_finrank_le (S := mergedChanges k) (by simp [mergedChanges])
    (fun c hc => mergedCls_sub_one c hc)
  have : (6 * k) * (mergedChanges k).card ≤ (6 * k) * 4 := Nat.mul_le_mul_left _ hcard
  omega

/-- **The decoders need the position.**  For `k ≥ 2`, every class-uniform code for the two merged
classes has dimension less than `25 * k ^ 2`, the dimension of the codes of `exists_blowUp_code`. -/
theorem finrank_lt_of_mergedCls {F : Type*} [Field F] (hk : 2 ≤ k)
    {𝒳 : Submodule F (Matrix (ZMod (6 * k)) (ZMod (6 * k)) F)}
    (h : IsClassUniformCode (mergedCls k) 𝒳) :
    finrank F 𝒳 < 25 * k ^ 2 := by
  have := two_mul_finrank_le_merged h
  nlinarith

end ClassUniformMemo
