import Transpose.Tape.Coverage

/-!
# Theorem P and P_γ (oblivious, frozen model), also on a set of inputs (robust form)

* `sum_combSet_all`: the combs of the `⌈n/γ⌉` groups partition the `n²b` input bits.
  `comb_split_le`: on any run, the comb bits of the groups are those the group forests do not read,
  plus at most `𝓗 (γ+1) n b` read ones (the coverage count `coverage_grouped`).
* `amgm_nat` and `pow_le_of_sum_pow_le`: the final step of P and P′ (AM–GM).
* `theoremP_grouped_on` (on a set `W` of co-entropy `≤ m`, i.e. `2^{n²b} ≤ 2^m |W|`, on which the
  machine is oblivious and correct; correctness forces `W ⊆ matrixInputs n b`): per group, the
  information count (`forest_info_on`) bounds the comb bits the group forest does not read, at `m`
  extra bits. `theoremP_grouped` is its case `W` = all matrix inputs, `m = 0`.
* Arithmetic shared with Theorem P′ (`PPrime.lean`): `bits_of_logfree` (log-free to bits),
  `div_of_sq` (per-`n` form), `pow_of_div` (power form), `robust_arith_gamma` and `robust_arith`
  (the robust co-entropy level `C n b`).
* `theoremP_grouped_on_bits`, `theoremP_grouped_bits`; `theoremP` (`γ = 1`) and its bits, bits
  with `+1`, per-`n`, power and greedy forms.
* Theorem P on a set: `theoremP_on` (`γ = 1`), `theoremP_on_bits`, `theoremP_on_div` and
  `theoremP_on_pow` (co-entropy `C n`: `log_{k+1} n − O(1)` passes survive), `theoremP_on_robust_gamma`
  and `theoremP_on_robust` (co-entropy `C n b`, grouping `γ = 2C`: `𝓗 ≳ n/(2(2C+1))`).
-/

namespace Transpose.Tape.Impl

open Transpose

/-! ### The combs partition the input -/

theorem combSet_card_split {n b o₁ o₂ o₃ : ℕ} (h₁ : o₁ ≤ o₂) (h₂ : o₂ ≤ o₃) :
    (combSet n b o₁ o₃).card = (combSet n b o₁ o₂).card + (combSet n b o₂ o₃).card := by
  classical
  have e1 : (combSet n b o₁ o₃).filter (fun d => tpos n b d < o₂) = combSet n b o₁ o₂ := by
    ext d
    simp only [combSet, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨⟨h1, h2, -⟩, h4⟩; exact ⟨h1, h2, h4⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2, by omega⟩, h3⟩
  have e2 : (combSet n b o₁ o₃).filter (fun d => ¬ tpos n b d < o₂) = combSet n b o₂ o₃ := by
    ext d
    simp only [combSet, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨⟨h1, -, h3⟩, h4⟩; exact ⟨h1, by omega, h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, by omega, h3⟩, by omega⟩
  rw [← Finset.card_filter_add_card_filter_not (s := combSet n b o₁ o₃)
    (fun d => tpos n b d < o₂), e1, e2]

theorem sum_combSet_groups (n b γ K : ℕ) :
    ∑ s ∈ Finset.range K, (combSet n b (segLo n b γ s) (segHi n b γ s)).card =
      (combSet n b 0 (segLo n b γ K)).card := by
  classical
  induction K with
  | zero =>
    have : combSet n b 0 (segLo n b γ 0) = ∅ := by
      apply Finset.filter_false_of_mem
      intro d _ h
      simp [segLo] at h
    simp [this]
  | succ K ih =>
    rw [Finset.sum_range_succ, ih,
      combSet_card_split (o₂ := segLo n b γ K) (Nat.zero_le _) (segLo_mono n b γ (Nat.le_succ K))]
    rfl

theorem combSet_full (n b : ℕ) : (combSet n b 0 (n * (n * b))).card = n * n * b := by
  classical
  rw [show combSet n b 0 (n * (n * b)) = Finset.range (n * n * b) from
    Finset.filter_true_of_mem fun d hd => ⟨Nat.zero_le _, by
      rw [← Nat.mul_assoc]; exact tpos_lt (Finset.mem_range.1 hd)⟩, Finset.card_range]

/-- The combs of the groups partition the `n²b` input bits. -/
theorem sum_combSet_all (n b : ℕ) {γ : ℕ} (hγ : 1 ≤ γ) :
    ∑ s ∈ Finset.range (numGroups n γ), (combSet n b (segLo n b γ s) (segHi n b γ s)).card =
      n * n * b := by
  rw [sum_combSet_groups, segLo_numGroups n b hγ, combSet_full]

/-- **Per run, the comb bits split** into those the group forests do not read and at most
`𝓗 (γ+1) n b` read ones. -/
theorem comb_split_le {M : TM} {w : List Bool} {n b T r γ : ℕ} {p : ℕ → ℕ}
    (hp : PassPartition M w T r p) (hγ : 1 ≤ γ) :
    n * n * b ≤ ∑ s ∈ Finset.range (numGroups n γ),
      (combSet n b (segLo n b γ s) (segHi n b γ s) \ readSet (inTraj M w) (n * n * b)
        (forest M w p r (segLo n b γ s) (segHi n b γ s))).card +
      addrCount M.k r * ((γ + 1) * n * b) :=
  calc n * n * b = _ := (sum_combSet_all n b hγ).symm
    _ = _ := Finset.sum_congr rfl (fun s _ => (Finset.card_sdiff_add_card_inter _
          (readSet (inTraj M w) (n * n * b) (forest M w p r (segLo n b γ s) (segHi n b γ s)))).symm)
    _ = _ := Finset.sum_add_distrib
    _ ≤ _ := Nat.add_le_add_left ((coverage_grouped hp).trans
          (Nat.mul_le_mul_right _ (card_addresses_le M.k r))) _

/-! ### AM–GM and the final step -/

/-- **AM–GM**, natural-number form: `G^G ∏ z ≤ (∑ z)^G` with `G = |s|`. -/
theorem amgm_nat {ι : Type*} (s : Finset ι) (z : ι → ℕ) :
    s.card ^ s.card * ∏ i ∈ s, z i ≤ (∑ i ∈ s, z i) ^ s.card := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  have hG : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have key := Real.geom_mean_le_arith_mean_weighted s (fun _ => (1 : ℝ) / s.card)
    (fun i => (z i : ℝ)) (fun _ _ => by positivity)
    (by rw [Finset.sum_const, nsmul_eq_mul]; field_simp) (fun _ _ => by positivity)
  have h1 : (∏ i ∈ s, ((z i : ℝ) ^ ((1 : ℝ) / s.card))) ^ s.card = ∏ i ∈ s, (z i : ℝ) := by
    rw [← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro i _
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), one_div,
      inv_mul_cancel₀ (ne_of_gt hG), Real.rpow_one]
  have h2 : ∑ i ∈ s, (1 : ℝ) / s.card * z i = (∑ i ∈ s, (z i : ℝ)) / s.card := by
    rw [← Finset.mul_sum]; field_simp
  have h3 := pow_le_pow_left₀ (Finset.prod_nonneg (fun i _ => by positivity)) key s.card
  rw [h1, h2, div_pow, le_div_iff₀ (by positivity)] at h3
  have h4 : ((s.card ^ s.card * ∏ i ∈ s, z i : ℕ) : ℝ) ≤ (((∑ i ∈ s, z i) ^ s.card : ℕ) : ℝ) := by
    push_cast
    linarith [h3]
  exact_mod_cast h4

/-- **The final step of P and P′** (AM–GM): from `L ≤ Σ_{s<G} m_s + X` and
`Σ_{s<G} 2^{m_s} ≤ G B`, `2^L ≤ 2^X B^G`. -/
theorem pow_le_of_sum_pow_le {G L X B : ℕ} (mm : ℕ → ℕ)
    (hL : L ≤ ∑ s ∈ Finset.range G, mm s + X) (hS : ∑ s ∈ Finset.range G, 2 ^ mm s ≤ G * B) :
    2 ^ L ≤ 2 ^ X * B ^ G := by
  have hprod : ∏ s ∈ Finset.range G, 2 ^ mm s ≤ B ^ G := by
    rcases Nat.eq_zero_or_pos G with rfl | hG
    · simp
    have h1 : G ^ G * ∏ s ∈ Finset.range G, 2 ^ mm s ≤ G ^ G * B ^ G :=
      calc _ ≤ (∑ s ∈ Finset.range G, 2 ^ mm s) ^ G := by
            simpa using amgm_nat (Finset.range G) (fun s => 2 ^ mm s)
        _ ≤ (G * B) ^ G := Nat.pow_le_pow_left hS G
        _ = G ^ G * B ^ G := mul_pow _ _ _
    exact Nat.le_of_mul_le_mul_left h1 (by positivity)
  rw [Finset.prod_pow_eq_pow_sum] at hprod
  calc 2 ^ L ≤ 2 ^ (∑ s ∈ Finset.range G, mm s + X) := Nat.pow_le_pow_right (by norm_num) hL
    _ = 2 ^ X * 2 ^ (∑ s ∈ Finset.range G, mm s) := by rw [pow_add, Nat.mul_comm]
    _ ≤ 2 ^ X * B ^ G := Nat.mul_le_mul_left _ hprod

theorem sum_le_card_mul {G B : ℕ} {f : ℕ → ℕ} (h : ∀ s < G, f s ≤ B) :
    ∑ s ∈ Finset.range G, f s ≤ G * B :=
  (Finset.sum_le_sum (fun s hs => h s (Finset.mem_range.1 hs))).trans (by simp)

/-! ### Arithmetic of the corollaries -/

/-- `(q+1)(g+1)^k ≤ 2^σ`. -/
theorem side_le_pow (M : TM) :
    (M.q + 1) * (M.g + 1) ^ M.k ≤ 2 ^ (Nat.clog 2 (M.q + 1) + M.k * Nat.clog 2 (M.g + 1)) := by
  have h1 := Nat.le_pow_clog (by norm_num : 1 < 2) (M.q + 1)
  have h2 := Nat.pow_le_pow_left (Nat.le_pow_clog (by norm_num : 1 < 2) (M.g + 1)) M.k
  calc (M.q + 1) * (M.g + 1) ^ M.k
      ≤ 2 ^ Nat.clog 2 (M.q + 1) * (2 ^ Nat.clog 2 (M.g + 1)) ^ M.k := Nat.mul_le_mul h1 h2
    _ = 2 ^ (Nat.clog 2 (M.q + 1) + M.k * Nat.clog 2 (M.g + 1)) := by
        rw [← pow_mul, ← pow_add, Nat.mul_comm (Nat.clog 2 (M.g + 1))]

/-- **From a log-free bound to the bits form**: with `K ≤ 2^κ`,
`2^L ≤ 2^{G m} (2^{H X} K^{G H})` gives `L ≤ G m + H (X + G κ)`. -/
theorem bits_of_logfree {L G m H X κ K : ℕ} (hK : K ≤ 2 ^ κ)
    (h : 2 ^ L ≤ 2 ^ (G * m) * (2 ^ (H * X) * K ^ (G * H))) : L ≤ G * m + H * (X + G * κ) := by
  refine (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 (h.trans ?_)
  calc _ ≤ 2 ^ (G * m) * (2 ^ (H * X) * (2 ^ κ) ^ (G * H)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hK _))
    _ = _ := by rw [← pow_mul, ← pow_add, ← pow_add]; congr 1; ring

/-- **The per-`n` form**: `n·n·b ≤ n X + H (n Y)` gives `n b ≤ X + H Y`. -/
theorem div_of_sq {n b X H Y : ℕ} (h : n * n * b ≤ n * X + H * (n * Y)) : n * b ≤ X + H * Y := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact Nat.le_of_mul_le_mul_left (by linarith [h]) hn

/-- **The power form**: `n b ≤ X + 𝓗 Y` gives `k (n b) ≤ k X + ((k+1)^r − 1) Y`. -/
theorem pow_of_div {n b k r X Y : ℕ} (h : n * b ≤ X + addrCount k r * Y) :
    k * (n * b) ≤ k * X + ((k + 1) ^ r - 1) * Y := by
  have : (k + 1) ^ r - 1 = k * addrCount k r := by have := addrCount_mul k r; omega
  rw [this]; nlinarith

/-- **The robust level, any grouping `γ`**: from the grouped bits bound at co-entropy `C n b`,
`(γ − C) n² b ≤ γ C n b + 𝓗 (γ(γ+1) n b + (n + γ) σ)`. -/
theorem robust_arith_gamma {n b C H σ G γ : ℕ} (hG : γ * G ≤ n + γ)
    (h3 : n * n * b ≤ G * (C * (n * b)) + H * ((γ + 1) * n * b + G * σ)) :
    (γ - C) * (n * n * b) ≤ γ * C * (n * b) + H * (γ * (γ + 1) * (n * b) + (n + γ) * σ) := by
  have e1 : (γ * G) * (C * (n * b)) ≤ (n + γ) * (C * (n * b)) := Nat.mul_le_mul_right _ hG
  have e2 : (γ * G) * (H * σ) ≤ (n + γ) * (H * σ) := Nat.mul_le_mul_right _ hG
  have key : γ * (n * n * b) ≤
      (n + γ) * (C * (n * b)) + γ * (H * ((γ + 1) * n * b)) + (n + γ) * (H * σ) := by
    have := Nat.mul_le_mul_left γ h3
    nlinarith
  rcases Nat.lt_or_ge γ C with h | h
  · rw [Nat.sub_eq_zero_of_le h.le, zero_mul]; exact Nat.zero_le _
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [Nat.add_sub_cancel_left]
    nlinarith

/-- **The robust level, grouping `γ = 2C`** (from `robust_arith_gamma`):
`C n b ≤ 2C² b + 𝓗 (2C(2C+1) b + 2σ)`. -/
theorem robust_arith {n b C H σ G : ℕ} (hG : 2 * C * G ≤ n + 2 * C)
    (h3 : n * n * b ≤ G * (C * (n * b)) + H * ((2 * C + 1) * n * b + G * σ)) :
    C * (n * b) ≤ 2 * C * C * b + H * (2 * C * (2 * C + 1) * b + 2 * σ) := by
  rcases Nat.lt_or_ge n (2 * C) with hn | hn
  · have := Nat.mul_le_mul_left C (Nat.mul_le_mul_right b hn.le)
    have e : C * (2 * C * b) = 2 * C * C * b := by ring
    omega
  rcases Nat.eq_zero_or_pos n with rfl | hnpos
  · simp
  have h := robust_arith_gamma hG h3
  rw [show 2 * C - C = C by omega] at h
  have e : (n + 2 * C) * σ ≤ 2 * n * σ := Nat.mul_le_mul_right _ (by omega)
  exact Nat.le_of_mul_le_mul_left (by nlinarith [Nat.mul_le_mul_left H e]) hnpos

theorem numGroups_one (n : ℕ) : numGroups n 1 = n := by simp [numGroups]

/-! ### Theorem P_γ on a set -/

section P

variable {M : TM} {n b T r : ℕ}

/-- **Theorem P_γ on a set of co-entropy `≤ m`, log-free.** Every group pays `m` bits. -/
theorem theoremP_grouped_on {γ : ℕ} {W : Set (List Bool)} (hobl : ObliviousOn M W T)
    (hcorr : ∀ w ∈ W, ∃ A : Matrix, w = encode n b A ∧
      (run M w T).outRev.reverse = encode n b (transpose A))
    {w₀ : List Bool} (hw₀ : w₀ ∈ W) {p : ℕ → ℕ} (hp : PassPartition M w₀ T r p) (hγ : 1 ≤ γ) {m : ℕ}
    (hco : 2 ^ (n * n * b) ≤ 2 ^ m * W.ncard) :
    2 ^ (n * n * b) ≤
      2 ^ (numGroups n γ * m) * (2 ^ (addrCount M.k r * ((γ + 1) * n * b)) *
        ((M.q + 1) * (M.g + 1) ^ M.k) ^ (numGroups n γ * addrCount M.k r)) := by
  have hB : 1 ≤ (M.q + 1) * (M.g + 1) ^ M.k := Nat.one_le_iff_ne_zero.2 (by positivity)
  have h := pow_le_of_sum_pow_le _ (comb_split_le (n := n) (b := b) hp hγ) (sum_le_card_mul
    fun s _ => (forest_info_on hobl hcorr hw₀ hp hco).trans
      (Nat.mul_le_mul_left (2 ^ m) (Nat.pow_le_pow_right hB (card_addresses_le M.k r))))
  calc _ ≤ _ := h
    _ = _ := by rw [mul_pow, ← pow_mul, ← pow_mul]; ring

/-- **Theorem P_γ on a set, bits form**: `n² b ≤ ⌈n/γ⌉ m + 𝓗 ((γ+1) n b + ⌈n/γ⌉ σ)`. -/
theorem theoremP_grouped_on_bits {γ : ℕ} {W : Set (List Bool)} (hobl : ObliviousOn M W T)
    (hcorr : ∀ w ∈ W, ∃ A : Matrix, w = encode n b A ∧
      (run M w T).outRev.reverse = encode n b (transpose A))
    {w₀ : List Bool} (hw₀ : w₀ ∈ W) {p : ℕ → ℕ} (hp : PassPartition M w₀ T r p) (hγ : 1 ≤ γ)
    {m : ℕ} (hco : 2 ^ (n * n * b) ≤ 2 ^ m * W.ncard) :
    n * n * b ≤ numGroups n γ * m + addrCount M.k r * ((γ + 1) * n * b +
      numGroups n γ * (Nat.clog 2 (M.q + 1) + M.k * Nat.clog 2 (M.g + 1))) :=
  bits_of_logfree (side_le_pow M) (theoremP_grouped_on hobl hcorr hw₀ hp hγ hco)

/-! ### Theorem P_γ and Theorem P -/

/-- **Theorem P_γ, log-free**: the case `W` = all matrix inputs, `m = 0` of `theoremP_grouped_on`. -/
theorem theoremP_grouped {γ : ℕ} (hobl : ObliviousOn M (matrixInputs n b) T)
    (hcorr : Transposes M n b) {w₀ : List Bool} (hw₀ : w₀ ∈ matrixInputs n b) {p : ℕ → ℕ}
    (hp : PassPartition M w₀ T r p) (hγ : 1 ≤ γ) :
    2 ^ (n * n * b) ≤
      2 ^ (addrCount M.k r * ((γ + 1) * n * b)) *
        ((M.q + 1) * (M.g + 1) ^ M.k) ^ (numGroups n γ * addrCount M.k r) := by
  have h := theoremP_grouped_on (m := 0) hobl
    (fun w hw => correct_of_transposes hcorr hw (hobl.1 w hw)) hw₀ hp hγ
    (by rw [ncard_matrixInputs, pow_zero, one_mul])
  simpa using h

/-- **Theorem P_γ, bits form**: the case `m = 0` of `theoremP_grouped_on_bits`. -/
theorem theoremP_grouped_bits {γ : ℕ} (hobl : ObliviousOn M (matrixInputs n b) T)
    (hcorr : Transposes M n b) {w₀ : List Bool} (hw₀ : w₀ ∈ matrixInputs n b) {p : ℕ → ℕ}
    (hp : PassPartition M w₀ T r p) (hγ : 1 ≤ γ) :
    n * n * b ≤ addrCount M.k r * ((γ + 1) * n * b +
      numGroups n γ * (Nat.clog 2 (M.q + 1) + M.k * Nat.clog 2 (M.g + 1))) := by
  have h := theoremP_grouped_on_bits (m := 0) hobl
    (fun w hw => correct_of_transposes hcorr hw (hobl.1 w hw)) hw₀ hp hγ
    (by rw [ncard_matrixInputs, pow_zero, one_mul])
  simpa using h

/-- **Theorem P, log-free.** -/
theorem theoremP (hobl : ObliviousOn M (matrixInputs n b) T)
    (hcorr : Transposes M n b) {w₀ : List Bool} (hw₀ : w₀ ∈ matrixInputs n b) {p : ℕ → ℕ}
    (hp : PassPartition M w₀ T r p) :
    2 ^ (n * n * b) ≤
      2 ^ (addrCount M.k r * (2 * n * b)) * ((M.q + 1) * (M.g + 1) ^ M.k) ^ (n * addrCount M.k r) := by
  have := theoremP_grouped (γ := 1) hobl hcorr hw₀ hp le_rfl
  simpa [numGroups_one] using this

/-- **Theorem P, bits form.** -/
theorem theoremP_bits (hobl : ObliviousOn M (matrixInputs n b) T)
    (hcorr : Transposes M n b) {w₀ : List Bool} (hw₀ : w₀ ∈ matrixInputs n b) {p : ℕ → ℕ}
    (hp : PassPartition M w₀ T r p) :
    n * n * b ≤
      addrCount M.k r * (n * (2 * b + (Nat.clog 2 (M.q + 1) + M.k * Nat.clog 2 (M.g + 1)))) := by
  have := theoremP_grouped_bits (γ := 1) hobl hcorr hw₀ hp le_rfl
  rw [numGroups_one] at this
  calc n * n * b ≤ _ := this
    _ = _ := by ring

/-- **Theorem P, bits form with `+1`**: `n²b ≤ 𝓗 · (n (2b + σ) + 1)`. -/
theorem theoremP_bits_add_one (hobl : ObliviousOn M (matrixInputs n b) T)
    (hcorr : Transposes M n b) {w₀ : List Bool} (hw₀ : w₀ ∈ matrixInputs n b) {p : ℕ → ℕ}
    (hp : PassPartition M w₀ T r p) :
    n * n * b ≤
      addrCount M.k r * (n * (2 * b + (Nat.clog 2 (M.q + 1) + M.k * Nat.clog 2 (M.g + 1))) + 1) :=
  le_trans (theoremP_bits hobl hcorr hw₀ hp) (Nat.mul_le_mul_left _ (Nat.le_succ _))

/-- **Theorem P, per-`n` form.** -/
theorem theoremP_div (hobl : ObliviousOn M (matrixInputs n b) T)
    (hcorr : Transposes M n b) {w₀ : List Bool} (hw₀ : w₀ ∈ matrixInputs n b) {p : ℕ → ℕ}
    (hp : PassPartition M w₀ T r p) :
    n * b ≤ addrCount M.k r * (2 * b + (Nat.clog 2 (M.q + 1) + M.k * Nat.clog 2 (M.g + 1))) := by
  simpa using div_of_sq (X := 0) (by simpa using theoremP_bits hobl hcorr hw₀ hp)

/-- **Theorem P, power form.** -/
theorem theoremP_pow (hobl : ObliviousOn M (matrixInputs n b) T)
    (hcorr : Transposes M n b) {w₀ : List Bool} (hw₀ : w₀ ∈ matrixInputs n b) {p : ℕ → ℕ}
    (hp : PassPartition M w₀ T r p) :
    M.k * (n * b) ≤
      ((M.k + 1) ^ r - 1) * (2 * b + (Nat.clog 2 (M.q + 1) + M.k * Nat.clog 2 (M.g + 1))) := by
  simpa using pow_of_div (X := 0) (by simpa using theoremP_div hobl hcorr hw₀ hp)

/-- **Theorem P with the greedy pass count.** -/
theorem theoremP_greedy (hobl : ObliviousOn M (matrixInputs n b) T)
    (hcorr : Transposes M n b) {w₀ : List Bool} (hw₀ : w₀ ∈ matrixInputs n b) :
    n * n * b ≤ addrCount M.k (greedyPasses M w₀ T) *
      (n * (2 * b + (Nat.clog 2 (M.q + 1) + M.k * Nat.clog 2 (M.g + 1)))) :=
  theoremP_bits hobl hcorr hw₀ (greedy_passPartition M w₀ T)

/-! ### Theorem P on a set of inputs (robust form) -/

/-- **Theorem P on a set of co-entropy `≤ m`, log-free** (`γ = 1`). -/
theorem theoremP_on {W : Set (List Bool)} (hobl : ObliviousOn M W T)
    (hcorr : ∀ w ∈ W, ∃ A : Matrix, w = encode n b A ∧
      (run M w T).outRev.reverse = encode n b (transpose A))
    {w₀ : List Bool} (hw₀ : w₀ ∈ W) {p : ℕ → ℕ} (hp : PassPartition M w₀ T r p) {m : ℕ}
    (hco : 2 ^ (n * n * b) ≤ 2 ^ m * W.ncard) :
    2 ^ (n * n * b) ≤
      2 ^ (n * m) * (2 ^ (addrCount M.k r * (2 * n * b)) *
        ((M.q + 1) * (M.g + 1) ^ M.k) ^ (n * addrCount M.k r)) := by
  have := theoremP_grouped_on (γ := 1) hobl hcorr hw₀ hp le_rfl hco
  simpa [numGroups_one] using this

/-- **Theorem P on a set, bits form**: `n² b ≤ n m + 𝓗 n (2b + σ)`. -/
theorem theoremP_on_bits {W : Set (List Bool)} (hobl : ObliviousOn M W T)
    (hcorr : ∀ w ∈ W, ∃ A : Matrix, w = encode n b A ∧
      (run M w T).outRev.reverse = encode n b (transpose A))
    {w₀ : List Bool} (hw₀ : w₀ ∈ W) {p : ℕ → ℕ} (hp : PassPartition M w₀ T r p) {m : ℕ}
    (hco : 2 ^ (n * n * b) ≤ 2 ^ m * W.ncard) :
    n * n * b ≤ n * m +
      addrCount M.k r * (n * (2 * b + (Nat.clog 2 (M.q + 1) + M.k * Nat.clog 2 (M.g + 1)))) := by
  have h := theoremP_grouped_on_bits (γ := 1) hobl hcorr hw₀ hp le_rfl hco
  rw [numGroups_one] at h
  calc n * n * b ≤ _ := h
    _ = _ := by ring

/-- **Theorem P on a set of co-entropy `≤ C n`, per-`n` form**: `n b ≤ C n + 𝓗 (2b + σ)`, so
`𝓗 ≥ n (b − C) / (2b + σ)`. -/
theorem theoremP_on_div {W : Set (List Bool)} (hobl : ObliviousOn M W T)
    (hcorr : ∀ w ∈ W, ∃ A : Matrix, w = encode n b A ∧
      (run M w T).outRev.reverse = encode n b (transpose A))
    {w₀ : List Bool} (hw₀ : w₀ ∈ W) {p : ℕ → ℕ} (hp : PassPartition M w₀ T r p) {C : ℕ}
    (hco : 2 ^ (n * n * b) ≤ 2 ^ (C * n) * W.ncard) :
    n * b ≤ C * n +
      addrCount M.k r * (2 * b + (Nat.clog 2 (M.q + 1) + M.k * Nat.clog 2 (M.g + 1))) :=
  div_of_sq (theoremP_on_bits hobl hcorr hw₀ hp hco)

/-- **Theorem P on a set of co-entropy `≤ C n`, power form**:
`k (n b) ≤ k C n + ((k+1)^r − 1)(2b + σ)`. -/
theorem theoremP_on_pow {W : Set (List Bool)} (hobl : ObliviousOn M W T)
    (hcorr : ∀ w ∈ W, ∃ A : Matrix, w = encode n b A ∧
      (run M w T).outRev.reverse = encode n b (transpose A))
    {w₀ : List Bool} (hw₀ : w₀ ∈ W) {p : ℕ → ℕ} (hp : PassPartition M w₀ T r p) {C : ℕ}
    (hco : 2 ^ (n * n * b) ≤ 2 ^ (C * n) * W.ncard) :
    M.k * (n * b) ≤ M.k * (C * n) +
      ((M.k + 1) ^ r - 1) * (2 * b + (Nat.clog 2 (M.q + 1) + M.k * Nat.clog 2 (M.g + 1))) :=
  pow_of_div (theoremP_on_div hobl hcorr hw₀ hp hco)

/-- **Theorem P at the robust co-entropy level `C n b`, any grouping `γ`**:
`(γ − C) n² b ≤ γ C n b + 𝓗 (γ(γ+1) n b + (n + γ) σ)`. -/
theorem theoremP_on_robust_gamma {W : Set (List Bool)} (hobl : ObliviousOn M W T)
    (hcorr : ∀ w ∈ W, ∃ A : Matrix, w = encode n b A ∧
      (run M w T).outRev.reverse = encode n b (transpose A))
    {w₀ : List Bool} (hw₀ : w₀ ∈ W) {p : ℕ → ℕ} (hp : PassPartition M w₀ T r p) {C γ : ℕ}
    (hγ : 1 ≤ γ) (hco : 2 ^ (n * n * b) ≤ 2 ^ (C * (n * b)) * W.ncard) :
    (γ - C) * (n * n * b) ≤ γ * C * (n * b) + addrCount M.k r * (γ * (γ + 1) * (n * b) +
      (n + γ) * (Nat.clog 2 (M.q + 1) + M.k * Nat.clog 2 (M.g + 1))) :=
  robust_arith_gamma (mul_numGroups_lt n hγ).le (theoremP_grouped_on_bits hobl hcorr hw₀ hp hγ hco)

/-- **Theorem P at the robust co-entropy level `C n b`** (grouping `γ = 2C`). Charging the co-entropy
once per group of `2C` columns instead of once per column gives
`C n b ≤ 2C² b + 𝓗 (2C(2C+1) b + 2σ)`, so `𝓗 ≳ n / (2(2C+1))`: still `log_{k+1} n − O(log C)` passes
(for `b = ⌈log₂ n⌉`, `k ≥ 1`). -/
theorem theoremP_on_robust {W : Set (List Bool)} (hobl : ObliviousOn M W T)
    (hcorr : ∀ w ∈ W, ∃ A : Matrix, w = encode n b A ∧
      (run M w T).outRev.reverse = encode n b (transpose A))
    {w₀ : List Bool} (hw₀ : w₀ ∈ W) {p : ℕ → ℕ} (hp : PassPartition M w₀ T r p) {C : ℕ}
    (hco : 2 ^ (n * n * b) ≤ 2 ^ (C * (n * b)) * W.ncard) :
    C * (n * b) ≤ 2 * C * C * b + addrCount M.k r *
      (2 * C * (2 * C + 1) * b + 2 * (Nat.clog 2 (M.q + 1) + M.k * Nat.clog 2 (M.g + 1))) := by
  rcases Nat.eq_zero_or_pos C with rfl | hC
  · simp
  exact robust_arith (mul_numGroups_lt n (by omega)).le
    (theoremP_grouped_on_bits (γ := 2 * C) hobl hcorr hw₀ hp (by omega) hco)

end P

end Transpose.Tape.Impl
