import TransposeFollowup.RationalNearIdentityFreePair

/-! Exact denominator and slow real growth bounds for words in the fixed
rational free pair. The seed parameter stays fixed as word length grows. -/
namespace TransposeFollowup.RationalFreePair
open Classical
set_option autoImplicit false

def HasDenominator (D : ℕ) (g : Group) : Prop :=
  ∀ i j : Fin 2, ∃ z : ℤ, (D : ℚ) * g i j = z

theorem hasDenominator_one : HasDenominator 1 (1 : Group) := by
  intro i j
  refine ⟨(1 : Matrix (Fin 2) (Fin 2) ℤ) i j, ?_⟩
  fin_cases i <;> fin_cases j <;> norm_num

theorem HasDenominator.mul {D E : ℕ} {g h : Group}
    (hg : HasDenominator D g) (hh : HasDenominator E h) :
    HasDenominator (D * E) (g * h) := by
  intro i j
  obtain ⟨x0, hx0⟩ := hg i 0
  obtain ⟨x1, hx1⟩ := hg i 1
  obtain ⟨y0, hy0⟩ := hh 0 j
  obtain ⟨y1, hy1⟩ := hh 1 j
  refine ⟨x0 * y0 + x1 * y1, ?_⟩
  change (↑(D * E) : ℚ) * (g.1 * h.1) i j = _
  rw [Matrix.mul_apply, Fin.sum_univ_two, Nat.cast_mul]
  calc
    _ = ((D : ℚ) * g i 0) * ((E : ℚ) * h 0 j) +
        ((D : ℚ) * g i 1) * ((E : ℚ) * h 1 j) := by ring
    _ = _ := by rw [hx0, hx1, hy0, hy1]; push_cast; rfl

theorem HasDenominator.inv {D : ℕ} {g : Group} (hg : HasDenominator D g) :
    HasDenominator D g⁻¹ := by
  intro i j
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  fin_cases i <;> fin_cases j
  · exact hg 1 1
  · obtain ⟨z, hz⟩ := hg 0 1
    refine ⟨-z, ?_⟩
    change (D : ℚ) * (-g 0 1) = ((-z : ℤ) : ℚ)
    rw [mul_neg, hz, Int.cast_neg]
  · obtain ⟨z, hz⟩ := hg 1 0
    refine ⟨-z, ?_⟩
    change (D : ℚ) * (-g 1 0) = ((-z : ℤ) : ℚ)
    rw [mul_neg, hz, Int.cast_neg]
  · exact hg 0 0

theorem hasDenominator_conjugator : HasDenominator 1 conjugator := by
  intro i j
  fin_cases i <;> fin_cases j
  · exact ⟨1, by norm_num [conjugator]⟩
  · exact ⟨1, by norm_num [conjugator]⟩
  · exact ⟨1, by norm_num [conjugator]⟩
  · exact ⟨2, by norm_num [conjugator]⟩

def seedDenominator (n : ℕ) : ℕ := baseDenominator n * (baseDenominator n + 1)

theorem seedDenominator_pos (n : ℕ) : 0 < seedDenominator n :=
  Nat.mul_pos (baseDenominator_pos n) (Nat.succ_pos _)

theorem seed_hasDenominator (n : ℕ) (k : Bool) : HasDenominator (seedDenominator n) (seed n k) := by
  have hq : (baseDenominator n : ℚ) ≠ 0 := by exact_mod_cast (baseDenominator_pos n).ne'
  have hq1 : (baseDenominator n : ℚ) + 1 ≠ 0 := by positivity
  have ha : (seedDenominator n : ℚ) * parameter n =
      (((baseDenominator n : ℤ) + 1) ^ 2 : ℤ) := by
    unfold seedDenominator parameter
    push_cast
    field_simp
  have hai : (seedDenominator n : ℚ) * (parameter n)⁻¹ =
      (((baseDenominator n : ℤ)) ^ 2 : ℤ) := by
    unfold seedDenominator parameter
    push_cast
    field_simp
  have hd : HasDenominator (seedDenominator n)
      (diagonal (parameter n) (parameter_pos n).ne') := by
    intro i j
    fin_cases i <;> fin_cases j
    · exact ⟨((baseDenominator n : ℤ) + 1) ^ 2, ha⟩
    · exact ⟨0, by simp [diagonal]⟩
    · exact ⟨0, by simp [diagonal]⟩
    · exact ⟨(baseDenominator n : ℤ) ^ 2, hai⟩
  cases k with
  | false => exact hd
  | true =>
    simpa only [seed, generators, Nat.one_mul, Nat.mul_one] using
      (hasDenominator_conjugator.mul hd).mul hasDenominator_conjugator.inv

def signedSeed (n : ℕ) (letter : Bool × Bool) : Group :=
  cond letter.2 (seed n letter.1) (seed n letter.1)⁻¹

theorem signedSeed_hasDenominator (n : ℕ) (letter : Bool × Bool) :
    HasDenominator (seedDenominator n) (signedSeed n letter) := by
  rcases letter with ⟨k, b⟩
  cases b
  · exact (seed_hasDenominator n k).inv
  · exact seed_hasDenominator n k

theorem list_product_hasDenominator (D : ℕ) (w : List Group)
    (hw : ∀ g ∈ w, HasDenominator D g) : HasDenominator (D ^ w.length) w.prod := by
  induction w with
  | nil => simpa using hasDenominator_one
  | cons g w ih =>
    have hh := (hw g (by simp)).mul (ih (fun h hh => hw h (by simp [hh])))
    simpa only [List.length_cons, List.prod_cons, pow_succ, Nat.mul_comm] using hh

theorem seed_word_hasDenominator (n : ℕ) (w : List (Bool × Bool)) :
    HasDenominator (seedDenominator n ^ w.length) (w.map (signedSeed n)).prod := by
  simpa only [List.length_map] using list_product_hasDenominator (seedDenominator n)
    (w.map (signedSeed n)) (by
      intro g hg
      obtain ⟨letter, _, rfl⟩ := List.mem_map.mp hg
      exact signedSeed_hasDenominator n letter)

theorem inverse_entry_error {g : Group} {δ : ℚ}
    (hg : ∀ i j, |g i j - (1 : Matrix (Fin 2) (Fin 2) ℚ) i j| ≤ δ) :
    ∀ i j, |g⁻¹ i j - (1 : Matrix (Fin 2) (Fin 2) ℚ) i j| ≤ δ := by
  intro i j
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  have h00 := hg 0 0
  have h01 := hg 0 1
  have h10 := hg 1 0
  have h11 := hg 1 1
  fin_cases i <;> fin_cases j <;> norm_num at h00 h01 h10 h11 ⊢ <;> assumption

theorem signedSeed_entry_error (n : ℕ) (letter : Bool × Bool) (i j : Fin 2) :
    |signedSeed n letter i j - (1 : Matrix (Fin 2) (Fin 2) ℚ) i j| ≤
      4 / (baseDenominator n : ℚ) := by
  rcases letter with ⟨k, b⟩
  cases b
  · exact inverse_entry_error (seed_entry_error n k) i j
  · exact seed_entry_error n k i j

theorem row_sum_le_of_entry_error {g : Group} {δ : ℚ}
    (hg : ∀ i j, |g i j - (1 : Matrix (Fin 2) (Fin 2) ℚ) i j| ≤ δ) (i : Fin 2) :
    |g i 0| + |g i 1| ≤ 1 + 2 * δ := by
  have h0 := hg i 0
  have h1 := hg i 1
  fin_cases i
  · norm_num at h0 h1 ⊢
    change |g 0 0 - 1| ≤ δ at h0
    have he := abs_le.mp h0
    have hd : |g 0 0| ≤ 1 + δ := abs_le.mpr ⟨by linarith [he.1], by linarith [he.2]⟩
    linarith
  · norm_num at h0 h1 ⊢
    change |g 1 1 - 1| ≤ δ at h1
    have he := abs_le.mp h1
    have hd : |g 1 1| ≤ 1 + δ := abs_le.mpr ⟨by linarith [he.1], by linarith [he.2]⟩
    linarith

theorem list_product_entry_bound {s : ℚ} (hs : 1 ≤ s) (w : List Group)
    (hw : ∀ g ∈ w, ∀ i, |g i 0| + |g i 1| ≤ s) :
    ∀ i j, |w.prod i j| ≤ s ^ w.length := by
  induction w with
  | nil => intro i j; fin_cases i <;> fin_cases j <;> norm_num
  | cons g w ih =>
    have hw' := ih (fun h hh => hw h (by simp [hh]))
    intro i j
    change |(g.1 * w.prod.1) i j| ≤ s ^ (w.length + 1)
    rw [Matrix.mul_apply, Fin.sum_univ_two, pow_succ]
    calc
      _ ≤ |g i 0| * |w.prod 0 j| + |g i 1| * |w.prod 1 j| := by
        simpa only [abs_mul] using abs_add_le (g i 0 * w.prod 0 j) (g i 1 * w.prod 1 j)
      _ ≤ |g i 0| * s ^ w.length + |g i 1| * s ^ w.length :=
        add_le_add (mul_le_mul_of_nonneg_left (hw' 0 j) (abs_nonneg _))
          (mul_le_mul_of_nonneg_left (hw' 1 j) (abs_nonneg _))
      _ = (|g i 0| + |g i 1|) * s ^ w.length := by ring
      _ ≤ s * s ^ w.length := mul_le_mul_of_nonneg_right (hw g (by simp) i)
        (pow_nonneg (by linarith) _)
      _ = _ := mul_comm _ _

theorem seed_word_entry_bound (n : ℕ) (w : List (Bool × Bool)) (i j : Fin 2) :
    |(w.map (signedSeed n)).prod i j| ≤
      (1 + 8 / (baseDenominator n : ℚ)) ^ w.length := by
  have hs : (1 : ℚ) ≤ 1 + 8 / (baseDenominator n : ℚ) :=
    le_add_of_nonneg_right (by positivity)
  have hb := list_product_entry_bound hs (w.map (signedSeed n)) (by
    intro g hg i
    obtain ⟨letter, _, rfl⟩ := List.mem_map.mp hg
    have he := row_sum_le_of_entry_error (signedSeed_entry_error n letter) i
    convert he using 1
    ring) i j
  simpa only [List.length_map] using hb

theorem HasDenominator.separated {D : ℕ} (hD : 0 < D) {g h : Group}
    (hg : HasDenominator D g) (hh : HasDenominator D h) (hne : g ≠ h) :
    ∃ i j : Fin 2, 1 / (D : ℚ) ≤ |g i j - h i j| := by
  have hd : (0 : ℚ) < D := by exact_mod_cast hD
  have he : ∃ i j : Fin 2, g i j ≠ h i j := by
    by_contra he
    push Not at he
    apply hne
    apply Subtype.ext
    ext i j
    exact he i j
  obtain ⟨i, j, hij⟩ := he
  obtain ⟨x, hx⟩ := hg i j
  obtain ⟨y, hy⟩ := hh i j
  have hxy : x - y ≠ 0 := by
    intro hz
    have hcast : (x : ℚ) = y := by exact_mod_cast (sub_eq_zero.mp hz)
    apply hij
    exact mul_left_cancel₀ hd.ne' (hx.trans (hcast.trans hy.symm))
  have ha : (1 : ℤ) ≤ |x - y| := by
    have := abs_pos.mpr hxy
    omega
  have hdiff : (D : ℚ) * (g i j - h i j) = ((x - y : ℤ) : ℚ) := by
    rw [mul_sub, hx, hy, Int.cast_sub]
  have habs := congrArg abs hdiff
  rw [abs_mul, abs_of_pos hd] at habs
  refine ⟨i, j, (div_le_iff₀ hd).mpr ?_⟩
  have ha' : (1 : ℚ) ≤ |((x - y : ℤ) : ℚ)| := by exact_mod_cast ha
  rw [← habs] at ha'
  simpa only [mul_comm] using ha'

theorem seed_word_eq_lift (n : ℕ) (w : List (Bool × Bool)) :
    (w.map (signedSeed n)).prod = FreeGroup.lift (seed n) (FreeGroup.mk w) := rfl

theorem seed_word_products_eq_iff (n : ℕ) (u v : List (Bool × Bool)) :
    (u.map (signedSeed n)).prod = (v.map (signedSeed n)).prod ↔
      FreeGroup.mk u = FreeGroup.mk v := by
  rw [seed_word_eq_lift, seed_word_eq_lift]
  exact (seed_free n).eq_iff

theorem seed_words_separated (n : ℕ) (u v : List (Bool × Bool))
    (hlen : u.length = v.length)
    (hne : FreeGroup.mk u ≠ FreeGroup.mk v) :
    ∃ i j : Fin 2, 1 / ((seedDenominator n : ℚ) ^ u.length) ≤
      |(u.map (signedSeed n)).prod i j - (v.map (signedSeed n)).prod i j| := by
  have hv := seed_word_hasDenominator n v
  rw [← hlen] at hv
  simpa only [Nat.cast_pow] using (seed_word_hasDenominator n u).separated
    (pow_pos (seedDenominator_pos n) _) hv ((seed_word_products_eq_iff n u v).not.mpr hne)

theorem real_seed_words_separated (n : ℕ) (u v : List (Bool × Bool))
    (hlen : u.length = v.length)
    (hne : FreeGroup.mk u ≠ FreeGroup.mk v) :
    ∃ i j : Fin 2, 1 / ((seedDenominator n : ℝ) ^ u.length) ≤
      |realEmbedding (u.map (signedSeed n)).prod i j -
        realEmbedding (v.map (signedSeed n)).prod i j| := by
  obtain ⟨i, j, he⟩ := seed_words_separated n u v hlen hne
  refine ⟨i, j, ?_⟩
  simp only [realEmbedding_entry]
  have hc := (Rat.cast_le (K := ℝ)).mpr he
  push_cast at hc
  exact hc

theorem real_identityDistanceSq_inv (g : RealMobius.Group) :
    RealMobius.mobiusIdentityDistanceSq g⁻¹ = RealMobius.mobiusIdentityDistanceSq g := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  simp [RealMobius.mobiusIdentityDistanceSq]
  ring

theorem exists_seed_symmetric_near_identity {η : ℝ} (hη : 0 < η) :
    ∃ n : ℕ, Function.Injective (FreeGroup.lift (realSeed n)) ∧
      ∀ k, realSeed n k ∈ RealMobius.mobiusIdentityBall η ∧
        (realSeed n k)⁻¹ ∈ RealMobius.mobiusIdentityBall η := by
  obtain ⟨n, hf, hn⟩ := exists_realSeed_near_identity hη
  refine ⟨n, hf, fun k => ⟨hn k, ?_⟩⟩
  change RealMobius.mobiusIdentityDistanceSq (realSeed n k)⁻¹ < η ^ 2
  rw [real_identityDistanceSq_inv]
  exact hn k

end TransposeFollowup.RationalFreePair
