import Mathlib

/-!
# Entropy of a function of a uniform input

For a finite nonempty type `Ω` with the uniform distribution and a map `f : Ω → α`,
`entropy f = ∑_a p_a log₂ (1/p_a)` over the values `a` of `f`, with `p_a` the probability of the
fibre of `a`.

* `entropy_le_of_fibres`: if `g = proj ∘ f` and every fibre of `proj` meets the values of `f` in at most
  `N` points, then `H(f) ≤ H(g) + log₂ N`. The proof uses only `log x ≤ x - 1`.
* `exists_large_fibre`: some value of `f` has a fibre of at least `|Ω| 2^{-H(f)}` points.
-/

namespace MergeDepth

open Finset Real

variable {Ω α β : Type*} [Fintype Ω] [Nonempty Ω] [DecidableEq α] [DecidableEq β]

/-- The probability of the value `a` of `f` under the uniform distribution. -/
noncomputable def prob (f : Ω → α) (a : α) : ℝ :=
  ((univ.filter fun x => f x = a).card : ℝ) / Fintype.card Ω

/-- Shannon entropy, in bits, of `f` under the uniform distribution. -/
noncomputable def entropy (f : Ω → α) : ℝ :=
  ∑ a ∈ univ.image f, prob f a * logb 2 (1 / prob f a)

theorem prob_pos {f : Ω → α} {a : α} (ha : a ∈ univ.image f) : 0 < prob f a := by
  obtain ⟨x, -, rfl⟩ := mem_image.mp ha
  unfold prob
  have : 0 < (univ.filter fun y => f y = f x).card := card_pos.mpr ⟨x, by simp⟩
  have hΩ : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  positivity

theorem sum_prob (f : Ω → α) : ∑ a ∈ univ.image f, prob f a = 1 := by
  unfold prob
  rw [← sum_div, div_eq_one_iff_eq (by exact_mod_cast Fintype.card_pos.ne')]
  have := card_eq_sum_card_image f (univ : Finset Ω)
  rw [card_univ] at this
  exact_mod_cast this.symm

omit [Nonempty Ω] in
/-- The probability of a value of `proj ∘ f` is the sum over the values of `f` above it. -/
theorem prob_comp (f : Ω → α) (proj : α → β) (b : β) :
    prob (proj ∘ f) b = ∑ a ∈ (univ.image f).filter (proj · = b), prob f a := by
  classical
  unfold prob
  rw [← sum_div]
  congr 1
  have hset : (univ.filter fun x => (proj ∘ f) x = b) =
      ((univ.image f).filter (proj · = b)).biUnion fun a => univ.filter fun x => f x = a := by
    ext x
    simp only [mem_filter, mem_univ, true_and, Function.comp_apply, mem_biUnion, mem_image]
    constructor
    · intro h; exact ⟨f x, ⟨⟨x, rfl⟩, h⟩, rfl⟩
    · rintro ⟨a, ⟨-, ha⟩, rfl⟩; exact ha
  rw [hset, card_biUnion]
  · push_cast; rfl
  · intro a _ a' _ hne
    simp only [Function.onFun]
    rw [disjoint_left]
    intro x h1 h2
    exact hne ((mem_filter.mp h1).2.symm.trans (mem_filter.mp h2).2)

/-- **The fibre bound.** If every fibre of `proj` contains at most `N` values of `f`, then
`H(f) ≤ H(proj ∘ f) + log₂ N`. -/
theorem entropy_le_of_fibres (f : Ω → α) (proj : α → β) {N : ℝ}
    (hfib : ∀ b, (((univ.image f).filter (proj · = b)).card : ℝ) ≤ N) :
    entropy f ≤ entropy (proj ∘ f) + logb 2 N := by
  have hlog2 : 0 < log 2 := log_pos (by norm_num)
  have himg : univ.image (proj ∘ f) = (univ.image f).image proj := by
    rw [image_image]
  -- regroup the sum over `f` by the values of `proj`
  have hsplit : entropy f = ∑ b ∈ univ.image (proj ∘ f),
      ∑ a ∈ (univ.image f).filter (proj · = b), prob f a * logb 2 (1 / prob f a) := by
    unfold entropy
    rw [himg, sum_fiberwise_of_maps_to (fun a ha => mem_image_of_mem proj ha)]
  -- inside one fibre: `∑ p_a log(1/p_a) ≤ q log(1/q) + q log N`
  have hfibre : ∀ b ∈ univ.image (proj ∘ f),
      ∑ a ∈ (univ.image f).filter (proj · = b), prob f a * logb 2 (1 / prob f a) ≤
        prob (proj ∘ f) b * logb 2 (1 / prob (proj ∘ f) b) + prob (proj ∘ f) b * logb 2 N := by
    intro b hb
    set A := (univ.image f).filter (proj · = b)
    set q := prob (proj ∘ f) b
    have hq : 0 < q := prob_pos hb
    have hqsum : q = ∑ a ∈ A, prob f a := prob_comp f proj b
    set n := A.card
    have hn1 : 1 ≤ n := by
      obtain ⟨x, -, hx⟩ := mem_image.mp hb
      exact card_pos.mpr ⟨f x, mem_filter.mpr ⟨mem_image_of_mem f (mem_univ x), hx⟩⟩
    have hnN : n ≤ N := hfib b
    have hnr : (0 : ℝ) < n := by exact_mod_cast hn1
    -- `p log(1/p) = p log(1/q) + p log N' + p log(q/(n p))`, and `log y ≤ y - 1`
    have hterm : ∀ a ∈ A, prob f a * log (1 / prob f a) ≤
        prob f a * log (1 / q) + prob f a * log n + (q / n - prob f a) := by
      intro a ha
      have hp : 0 < prob f a := prob_pos (mem_filter.mp ha).1
      have hy : 0 < q / (n * prob f a) := by positivity
      have hlog := log_le_sub_one_of_pos hy
      have e : log (1 / prob f a) = log (1 / q) + log n + log (q / (n * prob f a)) := by
        rw [← log_mul (by positivity) (by positivity), ← log_mul (by positivity) (by positivity)]
        congr 1
        field_simp
      rw [e]
      have : prob f a * log (q / (n * prob f a)) ≤ prob f a * (q / (n * prob f a) - 1) :=
        mul_le_mul_of_nonneg_left hlog hp.le
      have e2 : prob f a * (q / (n * prob f a) - 1) = q / n - prob f a := by
        field_simp
      nlinarith
    have hsum : ∑ a ∈ A, prob f a * log (1 / prob f a) ≤ q * log (1 / q) + q * log n := by
      calc ∑ a ∈ A, prob f a * log (1 / prob f a)
          ≤ ∑ a ∈ A, (prob f a * log (1 / q) + prob f a * log n + (q / n - prob f a)) :=
            sum_le_sum hterm
        _ = q * log (1 / q) + q * log n := by
            rw [sum_add_distrib, sum_add_distrib, ← sum_mul, ← sum_mul, sum_sub_distrib,
              sum_const, ← hqsum]
            rw [nsmul_eq_mul]
            field_simp
            ring
    have hlogn : log n ≤ log N := log_le_log hnr hnN
    have hL : ∑ a ∈ A, prob f a * logb 2 (1 / prob f a) =
        (∑ a ∈ A, prob f a * log (1 / prob f a)) / log 2 := by
      rw [sum_div]
      exact sum_congr rfl fun a _ => by rw [logb]; ring
    have hR : q * logb 2 (1 / q) + q * logb 2 N = (q * log (1 / q) + q * log N) / log 2 := by
      rw [logb, logb]; ring
    rw [hL, hR]
    apply div_le_div_of_nonneg_right _ hlog2.le
    nlinarith
  rw [hsplit]
  calc ∑ b ∈ univ.image (proj ∘ f),
        ∑ a ∈ (univ.image f).filter (proj · = b), prob f a * logb 2 (1 / prob f a)
      ≤ ∑ b ∈ univ.image (proj ∘ f),
          (prob (proj ∘ f) b * logb 2 (1 / prob (proj ∘ f) b) + prob (proj ∘ f) b * logb 2 N) :=
        sum_le_sum hfibre
    _ = entropy (proj ∘ f) + logb 2 N := by
        rw [sum_add_distrib, ← sum_mul, sum_prob, one_mul]
        rfl

/-- **A large fibre.** Some value of `f` has a fibre of at least `|Ω| 2^{-H(f)}` points. -/
theorem exists_large_fibre (f : Ω → α) :
    ∃ a, (Fintype.card Ω : ℝ) * (2 : ℝ) ^ (-entropy f) ≤
      ((univ.filter fun x => f x = a).card : ℝ) := by
  classical
  -- the largest probability `p*` satisfies `H(f) ≥ log₂ (1/p*)`
  obtain ⟨a, ha, hmax⟩ := exists_max_image (univ.image f) (prob f)
    (by obtain ⟨x⟩ := ‹Nonempty Ω›; exact ⟨f x, mem_image_of_mem f (mem_univ x)⟩)
  refine ⟨a, ?_⟩
  have hp : 0 < prob f a := prob_pos ha
  have hH : logb 2 (1 / prob f a) ≤ entropy f := by
    unfold entropy
    calc logb 2 (1 / prob f a) = ∑ b ∈ univ.image f, prob f b * logb 2 (1 / prob f a) := by
          rw [← sum_mul, sum_prob, one_mul]
      _ ≤ ∑ b ∈ univ.image f, prob f b * logb 2 (1 / prob f b) := by
          refine sum_le_sum fun b hb => mul_le_mul_of_nonneg_left ?_ (prob_pos hb).le
          exact logb_le_logb_of_le (by norm_num) (by have := prob_pos hb; positivity)
            (one_div_le_one_div_of_le (prob_pos hb) (hmax b hb))
  have hΩ : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  -- `2^{-H} ≤ 2^{-log₂(1/p)} = p`
  have h2 : (2 : ℝ) ^ (-entropy f) ≤ prob f a := by
    calc (2 : ℝ) ^ (-entropy f) ≤ (2 : ℝ) ^ (-logb 2 (1 / prob f a)) :=
          rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = prob f a := by
          rw [rpow_neg (by norm_num), rpow_logb (by norm_num) (by norm_num) (by positivity)]
          field_simp
  calc (Fintype.card Ω : ℝ) * (2 : ℝ) ^ (-entropy f) ≤ Fintype.card Ω * prob f a :=
        mul_le_mul_of_nonneg_left h2 hΩ.le
    _ = ((univ.filter fun x => f x = a).card : ℝ) := by
        unfold prob; field_simp

end MergeDepth
