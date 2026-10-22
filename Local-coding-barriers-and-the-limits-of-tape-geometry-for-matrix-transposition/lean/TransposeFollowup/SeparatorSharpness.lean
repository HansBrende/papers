import TransposeFollowup.AdaptiveSeparator

/-! Exact sharpness witnesses for the separate deficit and helper losses.
The constructions are protocols in the same original-row interface, rather
than numerical assignments to the terms of the lower bound. -/

namespace TransposeFollowup

open scoped BigOperators
set_option autoImplicit false

theorem componentRows_empty_id {n : ℕ} (i : Fin n) :
    componentRows ∅ id i = {i} := by
  ext j
  simp [componentRows]

theorem internalFreeBits_empty_id (n b : ℕ) :
    (internalFreeBits (b := b) (∅ : Finset (Fin n)) id).card = n * b := by
  rw [card_internalFreeBits]
  simp [componentRows_empty_id, Nat.mul_comm]

theorem RowCode.empty_separator_loss {n b : ℕ} {H : Type*}
    (C : RowCode n b H) (x : FiniteMatrix n b) :
    C.separatorLoss (fun _ _ => ∅) (fun _ _ => id) x = n * b := by
  simp only [separatorLoss, Finset.card_empty, Nat.mul_zero, zero_add, internalFreeBits_empty_id]

namespace SeparatorSharpness

abbrev Word (b : ℕ) := Fin b → Bool
abbrev SymData (b : ℕ) := Fin 3 → Word b

def symmetricFamily (b : ℕ) : Finset (FiniteMatrix 2 b) :=
  Finset.univ.filter (fun x => x 0 1 = x 1 0)

def symEncode {b : ℕ} (a : SymData b) : FiniteMatrix 2 b :=
  fun i j => if i = 0 then (if j = 0 then a 0 else a 1)
    else (if j = 0 then a 1 else a 2)

def symDecode {b : ℕ} (x : FiniteMatrix 2 b) : SymData b :=
  fun k => if k = 0 then x 0 0 else if k = 1 then x 0 1 else x 1 1

def symmetricFamilyEquiv (b : ℕ) : SymData b ≃ symmetricFamily b where
  toFun a := ⟨symEncode a, by simp [symmetricFamily, symEncode]⟩
  invFun x := symDecode x.val
  left_inv a := by
    funext k t
    fin_cases k <;> simp [symDecode, symEncode]
  right_inv x := by
    apply Subtype.ext
    funext i j t
    have hx : x.val 0 1 = x.val 1 0 := (Finset.mem_filter.mp x.property).2
    fin_cases i <;> fin_cases j <;> simp [symEncode, symDecode, hx]

theorem symmetricFamily_card (b : ℕ) : (symmetricFamily b).card = 2 ^ (3 * b) := by
  have h := Fintype.card_congr (symmetricFamilyEquiv b)
  rw [Fintype.card_coe] at h
  rw [← h]
  simp only [SymData, Word, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
  rw [← pow_mul, Nat.mul_comm]

instance symmetricFamily_nonempty (b : ℕ) : Nonempty (symmetricFamily b) :=
  ⟨symmetricFamilyEquiv b (fun _ _ => false)⟩

def symmetryCode (b : ℕ) : RowCode 2 b PUnit where
  helper := fun _ => PUnit.unit
  protocol := fun _ => .halt
  decode := fun _ _ row _ => row

theorem symmetryCode_correct (b : ℕ) :
    (symmetryCode b).CorrectOn (symmetricFamily b : Set _) := by
  intro x hx j
  funext i t
  have hsym : x 0 1 = x 1 0 := (Finset.mem_filter.mp hx).2
  change x j i t = transposed x j i t
  rw [transposed_apply]
  fin_cases i <;> fin_cases j <;> simp [hsym]

@[simp] theorem symmetryCode_transcript {b : ℕ} (x : FiniteMatrix 2 b) :
    (symmetryCode b).transcript x = [] := rfl

theorem symmetryCode_cost (b : ℕ) :
    (∑ x : symmetricFamily b, uniformWeight (symmetricFamily b) x *
      (((symmetryCode b).transcript x.val).length : ℝ)) = 0 := by simp

theorem symmetryCode_helper_entropy (b : ℕ) :
    observationEntropy (uniformWeight (symmetricFamily b))
      (fun x : symmetricFamily b => (symmetryCode b).helper x.val) = 0 := by
  change observationEntropy (uniformWeight (symmetricFamily b)) (fun _ => PUnit.unit) = 0
  rw [observationEntropy_const, sum_uniformWeight, Real.negMulLog_one]

theorem symmetricFamily_deficit (b : ℕ) :
    (4 * b : ℕ) - Real.log ((symmetricFamily b).card : ℝ) / Real.log 2 = (b : ℝ) := by
  rw [symmetricFamily_card, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  field_simp
  ring

/-- A putative deficit coefficient valid for this explicit zero-message
family must be at least two. The construction works at every positive width. -/
theorem deficit_coefficient_at_least_two (b : ℕ) (hb : 0 < b) (c : ℝ)
    (hbound :
      (∑ x : symmetricFamily b, uniformWeight (symmetricFamily b) x *
        (((symmetryCode b).transcript x.val).length : ℝ)) ≥
      (4 * b : ℕ) - (2 * b : ℕ) -
        c * ((4 * b : ℕ) - Real.log ((symmetricFamily b).card : ℝ) / Real.log 2)) :
    2 ≤ c := by
  rw [symmetryCode_cost, symmetricFamily_deficit] at hbound
  have hb' : 0 < (b : ℝ) := by exact_mod_cast hb
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hbound
  nlinarith

def fullFamily (b : ℕ) : Finset (FiniteMatrix 2 b) := Finset.univ

instance fullFamily_nonempty (b : ℕ) : Nonempty (fullFamily b) :=
  ⟨⟨fun _ _ _ => false, Finset.mem_univ _⟩⟩

theorem fullFamily_card (b : ℕ) : (fullFamily b).card = 2 ^ (4 * b) := by
  simpa only [fullFamily, Finset.card_univ] using card_finiteMatrix 2 b

def xorCode (b : ℕ) : RowCode 2 b (Word b) where
  helper := fun x t => x 0 1 t ^^ x 1 0 t
  protocol := fun _ => .halt
  decode := fun z j row _ i t => if i = j then row i t else row i t ^^ z t

theorem xorCode_correct (b : ℕ) : (xorCode b).CorrectOn (fullFamily b : Set _) := by
  intro x _ j
  funext i t
  change (if i = j then x j i t else x j i t ^^ (x 0 1 t ^^ x 1 0 t)) = transposed x j i t
  rw [transposed_apply]
  fin_cases i <;> fin_cases j <;> simp [Bool.xor_left_comm]

@[simp] theorem xorCode_transcript {b : ℕ} (x : FiniteMatrix 2 b) :
    (xorCode b).transcript x = [] := rfl

theorem xorCode_cost (b : ℕ) :
    (∑ x : fullFamily b, uniformWeight (fullFamily b) x *
      (((xorCode b).transcript x.val).length : ℝ)) = 0 := by simp

theorem fullFamily_deficit (b : ℕ) :
    (4 * b : ℕ) - Real.log ((fullFamily b).card : ℝ) / Real.log 2 = (0 : ℝ) := by
  rw [fullFamily_card, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  field_simp
  ring

theorem xorCode_helper_surjective (b : ℕ) : Function.Surjective (xorCode b).helper := by
  intro z
  refine ⟨fun i j t => if i = 1 ∧ j = 0 then z t else false, ?_⟩
  funext t
  simp [xorCode]

theorem xorCode_helper_values (b : ℕ) :
    ((fullFamily b).image (xorCode b).helper).card = 2 ^ b := by
  have heq : (fullFamily b).image (xorCode b).helper = Finset.univ :=
    Finset.image_univ_of_surjective (xorCode_helper_surjective b)
  rw [heq]
  simp [Word]

theorem xorCode_helper_entropy_le (b : ℕ) :
    observationEntropy (uniformWeight (fullFamily b))
      (fun x : fullFamily b => (xorCode b).helper x.val) ≤ (b : ℝ) * Real.log 2 := by
  have h := entropy_le_log_card
    (pushforward (uniformWeight (fullFamily b)) (fun x : fullFamily b => (xorCode b).helper x.val))
    (pushforward_nonneg _ (uniformWeight_nonneg _) _)
    (by rw [sum_pushforward, sum_uniformWeight])
  simpa only [observationEntropy, Word, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] using h

/-- The constructed helper has exactly b bits of entropy. Its alphabet gives
the upper bound; the already proved separator theorem gives the matching lower
bound. The main theorem does not depend on this sharpness module. -/
theorem xorCode_helper_entropy (b : ℕ) :
    observationEntropy (uniformWeight (fullFamily b))
      (fun x : fullFamily b => (xorCode b).helper x.val) = (b : ℝ) * Real.log 2 := by
  apply le_antisymm (xorCode_helper_entropy_le b)
  have h := (xorCode b).expected_separator_bound_log (fullFamily b) (xorCode_correct b)
    (fun _ _ => ∅) (fun _ _ => id) (fun _ _ => trivial)
  simp_rw [xorCode_transcript, RowCode.empty_separator_loss] at h
  simp only [List.length_nil, Nat.zero_add] at h
  rw [← Finset.sum_mul, sum_uniformWeight, one_mul, fullFamily_card,
    Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at h
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at h
  nlinarith

theorem xorCode_helper_bits (b : ℕ) :
    observationEntropy (uniformWeight (fullFamily b))
      (fun x : fullFamily b => (xorCode b).helper x.val) / Real.log 2 = (b : ℝ) := by
  rw [xorCode_helper_entropy]
  exact mul_div_cancel_right₀ _ (Real.log_pos (by norm_num)).ne'

/-- A putative helper-entropy coefficient valid for this explicit full-cube
zero-message code must be at least two. Its correct-family deficit is zero. -/
theorem helper_coefficient_at_least_two (b : ℕ) (hb : 0 < b) (c : ℝ)
    (hbound :
      (∑ x : fullFamily b, uniformWeight (fullFamily b) x *
        (((xorCode b).transcript x.val).length : ℝ)) ≥
      (4 * b : ℕ) - (2 * b : ℕ) - c *
        (observationEntropy (uniformWeight (fullFamily b))
          (fun x : fullFamily b => (xorCode b).helper x.val) / Real.log 2)) :
    2 ≤ c := by
  rw [xorCode_cost, xorCode_helper_bits] at hbound
  have hb' : 0 < (b : ℝ) := by exact_mod_cast hb
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hbound
  nlinarith

end SeparatorSharpness
end TransposeFollowup
