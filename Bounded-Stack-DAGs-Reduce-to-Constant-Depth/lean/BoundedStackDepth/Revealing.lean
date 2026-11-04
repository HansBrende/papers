import Mathlib

/-!
# Adaptive revealing

Bits `ξ : ι → Fin Q` are uniform; an entry `e` is *broken* when `ξ e = 0`. Rounds `i = 0, 1, …` reveal
sets `R i ξ` of entries. Every probability bound is a count of bit vectors.

A revealing scheme (`IsRevealing`) is *adaptive*: round `i` is determined by the bits revealed in the
earlier rounds (`RevAgree`); and *fresh*: round `i` is disjoint from the earlier rounds.

* `card_le_pow_mul_card_zero` (the zeroing lemma): if an event is determined by the rounds before `i`
  and round `i` reveals at most `m` entries, then requiring round `i` to be all broken loses at most a
  factor `Q ^ m`. Proof: setting the bits of round `i` to `0` keeps the event and the round, and each
  fiber of this map has at most `Q ^ m` elements.
* `card_le_pow_mul_card_block`: the same for `t` consecutive rounds, with the factor `Q ^ (t m)`.
* `card_blocks_le`: if every round reveals at most `m` entries, then each of `j` blocks of `n`
  consecutive rounds reveals an unbroken entry for at most `(1 − Q^{−nm})^j · Q^{|ι|}` bit vectors.
-/

namespace BoundedStackDepth

open Finset

variable {ι : Type*} {Q : ℕ}

/-- `ξ'` agrees with `ξ` on every set revealed for `ξ` before round `i`. -/
def RevAgree (R : ℕ → (ι → Fin Q) → Finset ι) (i : ℕ) (ξ ξ' : ι → Fin Q) : Prop :=
  ∀ i' < i, ∀ e ∈ R i' ξ, ξ' e = ξ e

/-- An adaptive revealing scheme: each round is determined by the bits revealed before it, and it is
disjoint from the earlier rounds. -/
structure IsRevealing (R : ℕ → (ι → Fin Q) → Finset ι) : Prop where
  adapt : ∀ i ξ ξ', RevAgree R i ξ ξ' → R i ξ' = R i ξ
  fresh : ∀ i ξ, ∀ i' < i, Disjoint (R i ξ) (R i' ξ)

variable {R : ℕ → (ι → Fin Q) → Finset ι}

theorem RevAgree.mono {i i' : ℕ} {ξ ξ' : ι → Fin Q} (h : RevAgree R i' ξ ξ') (hi : i ≤ i') :
    RevAgree R i ξ ξ' :=
  fun i'' hi'' => h i'' (lt_of_lt_of_le hi'' hi)

/-- Agreement before round `i` gives the same earlier rounds. -/
theorem IsRevealing.eq_of_agree (hR : IsRevealing R) {i i' : ℕ} {ξ ξ' : ι → Fin Q}
    (h : RevAgree R i ξ ξ') (hi' : i' < i) : R i' ξ' = R i' ξ :=
  hR.adapt i' ξ ξ' (h.mono hi'.le)

variable [Fintype ι] [DecidableEq ι] [NeZero Q]

/-- **Zeroing lemma.** If `A` is determined by the rounds before `i` and round `i` reveals at most `m`
entries, then `#A ≤ Q ^ m · #(A ∩ {round i all broken})`. -/
theorem card_le_pow_mul_card_zero (hR : IsRevealing R) {i m : ℕ} (hm : ∀ ξ, (R i ξ).card ≤ m)
    (A : Finset (ι → Fin Q)) (hA : ∀ ξ ξ', RevAgree R i ξ ξ' → ξ ∈ A → ξ' ∈ A) :
    A.card ≤ Q ^ m * (A.filter (fun ξ => ∀ e ∈ R i ξ, ξ e = 0)).card := by
  let φ : (ι → Fin Q) → ι → Fin Q := fun ξ e => if e ∈ R i ξ then 0 else ξ e
  have hout : ∀ ξ e, e ∉ R i ξ → φ ξ e = ξ e := fun ξ e he => by simp [φ, he]
  have hag : ∀ ξ, RevAgree R i ξ (φ ξ) := fun ξ i' hi' e he =>
    hout ξ e (disjoint_right.mp (hR.fresh i ξ i' hi') he)
  have hRφ : ∀ ξ, R i (φ ξ) = R i ξ := fun ξ => hR.adapt i ξ (φ ξ) (hag ξ)
  refine card_le_mul_card_image_of_maps_to (f := φ)
    (fun ξ hξ => mem_filter.mpr ⟨hA ξ _ (hag ξ) hξ, fun e he => ?_⟩) _ (fun η _ => ?_)
  · rw [hRφ] at he
    simp [φ, he]
  · calc (A.filter (fun ξ => φ ξ = η)).card ≤ (univ : Finset (R i η → Fin Q)).card := by
          refine card_le_card_of_injOn (fun ξ (x : R i η) => ξ x) (fun _ _ => mem_coe.mpr
            (mem_univ _)) fun ξ hξ ξ' hξ' h => ?_
          simp only [mem_coe, mem_filter] at hξ hξ'
          funext e
          by_cases he : e ∈ R i η
          · exact congrFun h ⟨e, he⟩
          · rw [← hout ξ e (by rwa [← hRφ, hξ.2]), ← hout ξ' e (by rwa [← hRφ, hξ'.2]), hξ.2,
              hξ'.2]
      _ = Q ^ (R i η).card := by simp
      _ ≤ Q ^ m := pow_le_pow_right₀ NeZero.one_le (hm η)

/-- **Iterated zeroing.** If `A` is determined by the rounds before `c`, then requiring the `t` rounds
`c, …, c + t − 1` to be all broken loses at most a factor `Q ^ (t m)`. -/
theorem card_le_pow_mul_card_block (hR : IsRevealing R) {m : ℕ} (hm : ∀ i ξ, (R i ξ).card ≤ m)
    (A : Finset (ι → Fin Q)) (c : ℕ) (hA : ∀ ξ ξ', RevAgree R c ξ ξ' → ξ ∈ A → ξ' ∈ A)
    (t : ℕ) :
    A.card ≤
      Q ^ (t * m) * (A.filter (fun ξ => ∀ i ∈ Ico c (c + t), ∀ e ∈ R i ξ, ξ e = 0)).card := by
  induction t with
  | zero => simp
  | succ t ih =>
    set B := A.filter (fun ξ => ∀ i ∈ Ico c (c + t), ∀ e ∈ R i ξ, ξ e = 0) with hBdef
    have hB : ∀ ξ ξ', RevAgree R (c + t) ξ ξ' → ξ ∈ B → ξ' ∈ B := by
      intro ξ ξ' h hξ
      rw [hBdef, mem_filter] at hξ ⊢
      refine ⟨hA ξ ξ' (h.mono (by omega)) hξ.1, fun i hi e he => ?_⟩
      have hi' : i < c + t := (mem_Ico.mp hi).2
      rw [hR.eq_of_agree h hi'] at he
      rw [h i hi' e he]
      exact hξ.2 i hi e he
    calc A.card ≤ Q ^ (t * m) * B.card := ih
      _ ≤ Q ^ (t * m) * (Q ^ m * (B.filter (fun ξ => ∀ e ∈ R (c + t) ξ, ξ e = 0)).card) :=
          Nat.mul_le_mul_left _ (card_le_pow_mul_card_zero hR (hm (c + t)) B hB)
      _ ≤ _ := by
          rw [← mul_assoc, ← pow_add, show t * m + m = (t + 1) * m by ring]
          refine Nat.mul_le_mul_left _ (card_le_card fun ξ hξ => ?_)
          rw [hBdef, mem_filter, mem_filter] at hξ
          refine mem_filter.mpr ⟨hξ.1.1, fun i hi => ?_⟩
          obtain ⟨h1, h2⟩ := mem_Ico.mp hi
          rcases Nat.lt_or_ge i (c + t) with h | h
          · exact hξ.1.2 i (mem_Ico.mpr ⟨h1, h⟩)
          · rw [show i = c + t by omega]
            exact hξ.2

/-- **Blocks of rounds.** If every round reveals at most `m` entries, then for at most
`(1 − Q^{−nm})^j · Q^{|ι|}` bit vectors each of the `j` blocks `[a + b n, a + b n + n)`, `b < j`,
reveals an unbroken entry. -/
theorem card_blocks_le (hR : IsRevealing R) {m : ℕ} (hm : ∀ i ξ, (R i ξ).card ≤ m) (a n j : ℕ) :
    ((univ.filter (fun ξ : ι → Fin Q => ∀ b < j, ∃ i ∈ Ico (a + b * n) (a + b * n + n),
      ∃ e ∈ R i ξ, ξ e ≠ 0)).card : ℝ)
      ≤ (1 - ((Q : ℝ) ^ (n * m))⁻¹) ^ j * (Q : ℝ) ^ Fintype.card ι := by
  have hp : (1 : ℝ) ≤ (Q : ℝ) ^ (n * m) := one_le_pow₀ (by exact_mod_cast NeZero.one_le)
  have hp0 : (0 : ℝ) < (Q : ℝ) ^ (n * m) := lt_of_lt_of_le one_pos hp
  have hq : 0 ≤ 1 - ((Q : ℝ) ^ (n * m))⁻¹ := sub_nonneg.mpr (inv_le_one_of_one_le₀ hp)
  induction j with
  | zero =>
    rw [pow_zero, one_mul]
    calc _ ≤ ((univ : Finset (ι → Fin Q)).card : ℝ) := by exact_mod_cast card_filter_le _ _
      _ = _ := by simp
  | succ j ih =>
    set E := univ.filter (fun ξ : ι → Fin Q => ∀ b < j, ∃ i ∈ Ico (a + b * n) (a + b * n + n),
      ∃ e ∈ R i ξ, ξ e ≠ 0) with hEdef
    set Z := E.filter (fun ξ => ∀ i ∈ Ico (a + j * n) (a + j * n + n), ∀ e ∈ R i ξ, ξ e = 0)
      with hZdef
    have hdet : ∀ ξ ξ', RevAgree R (a + j * n) ξ ξ' → ξ ∈ E → ξ' ∈ E := by
      intro ξ ξ' h hξ
      simp only [hEdef, mem_filter, mem_univ, true_and] at hξ ⊢
      intro b hb
      obtain ⟨i, hi, e, he, hne⟩ := hξ b hb
      have hi' : i < a + j * n := by
        have h1 := (mem_Ico.mp hi).2
        have h2 : (b + 1) * n ≤ j * n := Nat.mul_le_mul_right n hb
        rw [Nat.add_mul, Nat.one_mul] at h2
        omega
      refine ⟨i, hi, e, (hR.eq_of_agree h hi').symm ▸ he, ?_⟩
      rw [h i hi' e he]
      exact hne
    have h1 : (univ.filter (fun ξ : ι → Fin Q => ∀ b < j + 1,
        ∃ i ∈ Ico (a + b * n) (a + b * n + n), ∃ e ∈ R i ξ, ξ e ≠ 0)).card + Z.card
          ≤ E.card := by
      rw [← card_filter_add_card_filter_not (s := E)
        (fun ξ => ∀ i ∈ Ico (a + j * n) (a + j * n + n), ∀ e ∈ R i ξ, ξ e = 0), add_comm]
      refine Nat.add_le_add_left (card_le_card fun ξ hξ => ?_) _
      simp only [mem_filter, mem_univ, true_and] at hξ
      refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, fun b hb => hξ b (by omega)⟩, ?_⟩
      obtain ⟨i, hi, e, he, hne⟩ := hξ j (by omega)
      exact fun hz => hne (hz i hi e he)
    have h2 : E.card ≤ Q ^ (n * m) * Z.card := card_le_pow_mul_card_block hR hm E _ hdet n
    have h1' : ((univ.filter (fun ξ : ι → Fin Q => ∀ b < j + 1,
        ∃ i ∈ Ico (a + b * n) (a + b * n + n), ∃ e ∈ R i ξ, ξ e ≠ 0)).card : ℝ) + Z.card
          ≤ E.card := by exact_mod_cast h1
    have h2' : (E.card : ℝ) ≤ (Q : ℝ) ^ (n * m) * Z.card := by exact_mod_cast h2
    have hz : ((Q : ℝ) ^ (n * m))⁻¹ * E.card ≤ Z.card := (inv_mul_le_iff₀ hp0).mpr h2'
    calc _ ≤ (E.card : ℝ) - ((Q : ℝ) ^ (n * m))⁻¹ * E.card := by linarith
      _ = (1 - ((Q : ℝ) ^ (n * m))⁻¹) * E.card := by ring
      _ ≤ (1 - ((Q : ℝ) ^ (n * m))⁻¹) * ((1 - ((Q : ℝ) ^ (n * m))⁻¹) ^ j *
          (Q : ℝ) ^ Fintype.card ι) := mul_le_mul_of_nonneg_left ih hq
      _ = _ := by ring

end BoundedStackDepth
