import TransposeFollowup.SL2OffDiagonalBounds

/-! Entrywise bounds for products and differences of products. The estimates
use the actual two-term matrix multiplication and the stated entry bounds. -/
namespace TransposeFollowup.SL2Escape
open Classical Matrix
set_option autoImplicit false
local notation "M" => Matrix (Fin 2) (Fin 2) ℂ

theorem complex_matrix_mul_entry_bound {a b : M} {A B : ℝ}
    (ha : ∀ i j, ‖a i j‖ ≤ A) (hb : ∀ i j, ‖b i j‖ ≤ B) :
    ∀ i j, ‖(a * b) i j‖ ≤ 2 * A * B := by
  have hA : 0 ≤ A := (norm_nonneg _).trans (ha 0 0)
  intro i j
  calc
    _ = ‖a i 0 * b 0 j + a i 1 * b 1 j‖ := by rw [Matrix.mul_apply, Fin.sum_univ_two]
    _ ≤ ‖a i 0 * b 0 j‖ + ‖a i 1 * b 1 j‖ := norm_add_le _ _
    _ ≤ A * B + A * B := by simp only [norm_mul]; gcongr <;> first | apply ha | apply hb
    _ = _ := by ring

theorem complex_matrix_mul_error {a a' b b' : M} {A B δ ε : ℝ}
    (ha' : ∀ i j, ‖a' i j‖ ≤ A) (hb : ∀ i j, ‖b i j‖ ≤ B)
    (ha : ∀ i j, ‖a i j - a' i j‖ ≤ δ) (hb' : ∀ i j, ‖b i j - b' i j‖ ≤ ε) :
    ∀ i j, ‖(a * b) i j - (a' * b') i j‖ ≤ 2 * δ * B + 2 * A * ε := by
  have h₁ := complex_matrix_mul_entry_bound (a := a - a') ha hb
  have h₂ := complex_matrix_mul_entry_bound (b := b - b') ha' hb'
  have he : a * b - a' * b' = (a - a') * b + a' * (b - b') := by noncomm_ring
  intro i j
  calc
    _ = ‖((a - a') * b) i j + (a' * (b - b')) i j‖ := by
      change ‖(a * b - a' * b') i j‖ = _
      rw [he]; rfl
    _ ≤ ‖((a - a') * b) i j‖ + ‖(a' * (b - b')) i j‖ := norm_add_le _ _
    _ ≤ _ := add_le_add (h₁ i j) (h₂ i j)

theorem complex_matrix_list_prod_bound {ι : Type*} (l : List ι) (f : ι → M)
    {R : ℝ} (hf : ∀ a ∈ l, ∀ i j, ‖f a i j‖ ≤ R) :
    ∀ i j, ‖(l.map f).prod i j‖ ≤ (2 * R) ^ l.length := by
  induction l with
  | nil => intro i j; fin_cases i <;> fin_cases j <;> norm_num
  | cons a l ih =>
    have hl := ih (fun b hb => hf b (List.mem_cons_of_mem _ hb))
    have ha := hf a (List.mem_cons_self ..)
    intro i j
    simpa only [List.map_cons, List.prod_cons, List.length_cons, pow_succ, mul_assoc, mul_comm,
      mul_left_comm] using complex_matrix_mul_entry_bound ha hl i j

theorem complex_matrix_list_prod_error {ι : Type*} (l : List ι) (f g : ι → M)
    {R δ : ℝ} (hR : 1 ≤ R) (hδ : 0 ≤ δ)
    (hf : ∀ a ∈ l, ∀ i j, ‖f a i j‖ ≤ R)
    (hg : ∀ a ∈ l, ∀ i j, ‖g a i j‖ ≤ R)
    (he : ∀ a ∈ l, ∀ i j, ‖f a i j - g a i j‖ ≤ δ) :
    ∀ i j, ‖(l.map f).prod i j - (l.map g).prod i j‖ ≤
      (l.length : ℝ) * (2 * R) ^ l.length * δ := by
  induction l with
  | nil => intro i j; simp
  | cons a l ih =>
    have hf' := fun b hb => hf b (List.mem_cons_of_mem _ hb)
    have hg' := fun b hb => hg b (List.mem_cons_of_mem _ hb)
    have he' := fun b hb => he b (List.mem_cons_of_mem _ hb)
    have hi := ih hf' hg' he'
    have hl := complex_matrix_list_prod_bound l f hf'
    have ha := hg a (List.mem_cons_self ..)
    have heₐ := he a (List.mem_cons_self ..)
    intro i j
    have hh := complex_matrix_mul_error ha hl heₐ hi i j
    simp only [List.map_cons, List.prod_cons, List.length_cons, Nat.cast_add, Nat.cast_one, pow_succ]
    calc
      _ ≤ 2 * δ * (2 * R) ^ l.length + 2 * R * ((l.length : ℝ) * (2 * R) ^ l.length * δ) := hh
      _ ≤ 2 * R * δ * (2 * R) ^ l.length +
          2 * R * ((l.length : ℝ) * (2 * R) ^ l.length * δ) := by
        gcongr
        linarith
      _ = _ := by ring

theorem complex_matrix_trace_error {b g : M} {δ R : ℝ}
    (hb : ∀ i j, ‖b i j - (1 : M) i j‖ ≤ δ) (hg : ∀ i j, ‖g i j‖ ≤ R) :
    ‖Matrix.trace (b * g) - Matrix.trace g‖ ≤ 4 * δ * R := by
  have hm := complex_matrix_mul_entry_bound (a := b - 1) hb hg
  have he : Matrix.trace (b * g) - Matrix.trace g = Matrix.trace ((b - 1) * g) := by
    rw [sub_mul, one_mul, Matrix.trace_sub]
  rw [he]
  simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_two]
  have hh := norm_add_le (((b - 1) * g) 0 0) (((b - 1) * g) 1 1)
  linarith [hm 0 0, hm 1 1]

end TransposeFollowup.SL2Escape
