import TransposeFollowup.SL2SpanCertificate
import TransposeFollowup.RationalTraceCertificate
import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-! A rational nontrivial bicommutator supplies four quantitatively
independent actual matrices. The two cases use either its two commutator
inputs or the bicommutator itself and its already proved trace-test witness. -/
namespace TransposeFollowup.RationalFreePair
open Classical Matrix Set SL2Escape
open scoped Pointwise commutatorElement
set_option autoImplicit false
local notation "G" => RealMobius.Group
local notation "M" => Matrix (Fin 2) (Fin 2) ℝ

theorem rational_bicommutator_span_certificate {D : ℕ} (hD : 0 < D)
    {a x y : G} (ha : a ∈ denominatorCarrier D)
    (hx : x ∈ denominatorCarrier D) (hy : y ∈ denominatorCarrier D)
    (hne : ⁅⁅a, x⁆, ⁅a, y⁆⁆ ≠ 1) :
    ∃ p q : G,
      ((p = ⁅a, x⁆ ∧ q = ⁅a, y⁆) ∨
        (p = ⁅⁅a, x⁆, ⁅a, y⁆⁆ ∧ (q = 1 ∨ q = a ∨ q = x ∨ q = y))) ∧
      1 / (D : ℝ) ^ 34 ≤ |(pairSpanMatrix (p : M) (q : M)).det| := by
  let B := ⁅⁅a, x⁆, ⁅a, y⁆⁆
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  by_cases htr : Matrix.trace (B : M) = 2
  · obtain ⟨g, hg, hgap, _⟩ := rational_bicommutator_trace_certificate hD ha hx hy hne
    refine ⟨B, g, Or.inr ⟨rfl, hg⟩, ?_⟩
    rw [pairSpanMatrix_det_trace_two B g htr, abs_neg, abs_pow]
    have hh := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 / (D : ℝ) ^ 17) hgap 2
    simpa only [div_pow, one_pow, ← pow_mul, show (17 : ℕ) * 2 = 34 from rfl] using hh
  · have hBD := (rational_bicommutator_separated hD ha hx hy hne).1
    have hsep : 1 / (D : ℝ) ^ 16 ≤ |Matrix.trace (B : M) - 2| := by
      simpa only [Nat.cast_pow, Matrix.SpecialLinearGroup.coe_one, Matrix.trace_one,
        Fintype.card_fin, Nat.cast_ofNat] using denominatorCarrier_trace_separated
        (pow_pos hD 16) hBD (denominatorCarrier_one (D ^ 16))
        (by simpa only [Matrix.SpecialLinearGroup.coe_one, Matrix.trace_one,
          Fintype.card_fin, Nat.cast_ofNat] using htr)
    refine ⟨⁅a, x⁆, ⁅a, y⁆, Or.inl ⟨rfl, rfl⟩, ?_⟩
    rw [pairSpanMatrix_det_commutator, abs_sub_comm]
    have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
    exact (one_div_le_one_div_of_le (pow_pos hD0 16)
      (pow_le_pow_right₀ hD1 (by decide : 16 ≤ 34))).trans hsep

theorem symmetric_commutator_mem_pow {Γ : Type*} [_root_.Group Γ]
    {A : Set Γ} (hAi : A⁻¹ = A) {m n : ℕ} {a b : Γ}
    (ha : a ∈ A ^ m) (hb : b ∈ A ^ n) : ⁅a, b⁆ ∈ A ^ (2 * (m + n)) := by
  have hinv {k : ℕ} {g : Γ} (hg : g ∈ A ^ k) : g⁻¹ ∈ A ^ k := by
    have hh := Set.inv_mem_inv.mpr hg
    simpa only [← inv_pow, hAi] using hh
  have hh := Set.mul_mem_mul (Set.mul_mem_mul (Set.mul_mem_mul ha hb) (hinv ha)) (hinv hb)
  simpa only [commutatorElement_def, ← pow_add,
    show m + n + m + n = 2 * (m + n) by omega] using hh

theorem rational_conjugated_spanning {D : ℕ} (hD : 0 < D)
    {A : Set G} (hA1 : 1 ∈ A) (hAi : A⁻¹ = A)
    (u : G) {a x y : G}
    (haD : a ∈ denominatorCarrier D) (hxD : x ∈ denominatorCarrier D)
    (hyD : y ∈ denominatorCarrier D)
    (ha : u⁻¹ * a * u ∈ A ^ 2) (hx : u⁻¹ * x * u ∈ A ^ 2)
    (hy : u⁻¹ * y * u ∈ A ^ 2) (hne : ⁅⁅a, x⁆, ⁅a, y⁆⁆ ≠ 1) :
    ∃ p q : G, p ∈ A ^ 34 ∧ q ∈ A ^ 34 ∧ p * q ∈ A ^ 34 ∧
      1 / (D : ℝ) ^ 34 ≤ |(pairSpanMatrix (p : M) (q : M)).det| ∧
      LinearIndependent ℝ (pairSpanMatrix (p : M) (q : M)).col := by
  let f := MulAut.conj u⁻¹
  have hf (g : G) : f g = u⁻¹ * g * u := by
    change u⁻¹ * g * (u⁻¹)⁻¹ = _
    rw [inv_inv]
  have ha' : f a ∈ A ^ 2 := by simpa only [hf] using ha
  have hx' : f x ∈ A ^ 2 := by simpa only [hf] using hx
  have hy' : f y ∈ A ^ 2 := by simpa only [hf] using hy
  have hp8 : f ⁅a, x⁆ ∈ A ^ 8 := by
    simpa only [map_commutatorElement, show 2 * (2 + 2) = (8 : ℕ) from rfl] using
      symmetric_commutator_mem_pow hAi ha' hx'
  have hq8 : f ⁅a, y⁆ ∈ A ^ 8 := by
    simpa only [map_commutatorElement, show 2 * (2 + 2) = (8 : ℕ) from rfl] using
      symmetric_commutator_mem_pow hAi ha' hy'
  have hB32 : f ⁅⁅a, x⁆, ⁅a, y⁆⁆ ∈ A ^ 32 := by
    simpa only [map_commutatorElement, show 2 * (8 + 8) = (32 : ℕ) from rfl] using
      symmetric_commutator_mem_pow hAi hp8 hq8
  obtain ⟨p, q, hchoice, hgap⟩ := rational_bicommutator_span_certificate hD haD hxD hyD hne
  have hmem : f p ∈ A ^ 34 ∧ f q ∈ A ^ 34 ∧ f p * f q ∈ A ^ 34 := by
    rcases hchoice with ⟨rfl, rfl⟩ | ⟨rfl, hq⟩
    · refine ⟨Set.pow_subset_pow_right hA1 (by decide : 8 ≤ 34) hp8,
        Set.pow_subset_pow_right hA1 (by decide : 8 ≤ 34) hq8, ?_⟩
      apply Set.pow_subset_pow_right hA1 (by decide : 16 ≤ 34)
      simpa only [← pow_add, show (8 : ℕ) + 8 = 16 from rfl] using Set.mul_mem_mul hp8 hq8
    · have hq2 : f q ∈ A ^ 2 := by
        rcases hq with rfl | rfl | rfl | rfl
        · simpa only [map_one] using Set.one_mem_pow hA1 (n := 2)
        · exact ha'
        · exact hx'
        · exact hy'
      refine ⟨Set.pow_subset_pow_right hA1 (by decide : 32 ≤ 34) hB32,
        Set.pow_subset_pow_right hA1 (by decide : 2 ≤ 34) hq2, ?_⟩
      simpa only [← pow_add, show (32 : ℕ) + 2 = 34 from rfl] using Set.mul_mem_mul hB32 hq2
  have hdet : (pairSpanMatrix (f p : M) (f q : M)).det =
      (pairSpanMatrix (p : M) (q : M)).det := by
    simpa only [hf, inv_inv] using pairSpanMatrix_det_conjugate u⁻¹ p q
  have hgap' : 1 / (D : ℝ) ^ 34 ≤ |(pairSpanMatrix (f p : M) (f q : M)).det| := by
    rw [hdet]; exact hgap
  refine ⟨f p, f q, hmem.1, hmem.2.1, hmem.2.2, hgap', ?_⟩
  apply Matrix.linearIndependent_cols_of_det_ne_zero
  exact abs_pos.mp ((by positivity : (0 : ℝ) < 1 / (D : ℝ) ^ 34).trans_le hgap')

end TransposeFollowup.RationalFreePair
