import SharedDecoders.CapacityReflectionBlocks
import SharedDecoders.CapacityReflectionBaseChange
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Complete all-width reflection barriers from actual decoder equations

The endpoints assume only containment in the literal reflection source and
the original linear shared-decoder rules. A splitting character, scalar
extension, Fourier equations and paired-block recovery are all constructed.
The linear bounds hold at every odd side length; primeness is needed for
the separate existence of the nonlinear decoder by disjoint views.
-/

namespace SharedDecoders.CapacityReflection

open Module

variable {F : Type*} [Field F] [CharP F 2] {m b : ℕ}

theorem one_class_finrank_le_split
    (χ : AddChar (ZMod (2*m+1)) F) (hχ : Function.Injective χ)
    (C : Submodule F (State (2*m+1) (Fin b → F)))
    (hsource : C ≤ source (F := F) (2*m+1))
    (hC : IsLinearSharedCode (fun _ => ()) C) :
    finrank F C ≤ b*m*(m+1) := by
  obtain ⟨f,hf⟩ := hC
  let e := squareFourierEquiv (b := b) χ hχ
  let D := C.map e.symm.toLinearMap
  have hmem (X : State (2*m+1) (Fin b → F)) (hX : X ∈ D) :
      squareSynthesis χ X ∈ C := by
    obtain ⟨Y,hY,rfl⟩ := hX
    change e (e.symm Y) ∈ C
    rw [LinearEquiv.apply_symm_apply]
    exact hY
  have hb := reflected_equations_finrank_le (frequencyDecoder χ hχ (f ())) D
    (fun X hX => reflected_fourier_zero_column χ hχ X (hsource (hmem X hX)))
    (fun X hX => reflected_fourier_columns χ hχ X (hsource (hmem X hX)))
    (fun X hX => frequency_decoder_equation χ hχ (f ()) X
      (fun c => hf _ (hmem X hX) c))
  have hd : finrank F D = finrank F C := e.symm.finrank_map_eq C
  rwa [hd] at hb

/-- Actual one-decoder bound for arbitrary coupled lanes. The splitting
field and extended source/decoder are constructed inside the proof. -/
theorem one_class_finrank_le
    (C : Submodule F (State (2*m+1) (Fin b → F)))
    (hsource : C ≤ source (F := F) (2*m+1))
    (hC : IsLinearSharedCode (fun _ => ()) C) :
    finrank F C ≤ b*m*(m+1) := by
  have hd : ((2*m+1 : ℕ) : F) ≠ 0 := by
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_two, Nat.cast_one,
      CharTwo.two_eq_zero, zero_mul, zero_add, ne_eq, one_ne_zero, not_false_eq_true]
  let dn : ℕ+ := ⟨2*m+1, by omega⟩
  let ψ := AddChar.primitiveZModChar dn F hd
  let E := CyclotomicField ψ.n F
  let : CharP E 2 := charP_of_injective_algebraMap (algebraMap F E).injective 2
  let χ : AddChar (ZMod (2*m+1)) E := ψ.char
  have hχ : Function.Injective χ := by
    intro a c hac
    have hz : χ (a-c)=1 := by
      calc
        χ (a-c) = χ a*χ (-c) := by rw [sub_eq_add_neg, χ.map_add_eq_mul]
        _ = χ c*χ (-c) := by rw [hac]
        _ = 1 := by rw [← χ.map_add_eq_mul, add_neg_cancel, χ.map_zero_eq_one]
    exact sub_eq_zero.mp ((ψ.prim.zmod_char_eq_one_iff (2*m+1) (a-c)).mp hz)
  have hb := one_class_finrank_le_split χ hχ (extendedCode (E := E) C)
    (extendedCode_le_source hsource) (extendedCode_shared hC)
  rwa [finrank_extendedCode] at hb

/-- The two classes are the original singleton zero and its complement.
The bulk decoder is cut in original coordinates before scalar extension. -/
theorem two_class_finrank_le
    (C : Submodule F (State (2*m+1) (Fin b → F)))
    (hsource : C ≤ source (F := F) (2*m+1))
    (hC : IsLinearSharedCode singletonPartition C) :
    finrank F C ≤ b*(m*(m+1)+(2*m+1)) := by
  obtain ⟨H,hHC,hH,f,hdef⟩ := bulk_cut_one_class C hC
  have hb := one_class_finrank_le H (hHC.trans hsource) hH
  have hc := bulk_cut_finrank C f
  rw [← hdef] at hc
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hc
  nlinarith

/-- The deletion cost, expressed without truncated subtraction in the
statement, applies to the actual reflection-source dimension. -/
theorem two_class_codimension
    (C : Submodule F (State (2*m+1) (Fin b → F)))
    (hsource : C ≤ source (F := F) (2*m+1))
    (hC : IsLinearSharedCode singletonPartition C) :
    b*m*m ≤ (finrank F (source (F := F) (A := Fin b → F) (2*m+1)) - finrank F C) +
      b*(2*m+1) := by
  have hb := two_class_finrank_le C hsource hC
  have hle := Submodule.finrank_mono hsource
  have he := finrank_source (F := F) (A := Fin b → F) m
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at he
  have hd := Nat.sub_add_cancel hle
  nlinarith

theorem two_class_codimension_lower
    (C : Submodule F (State (2*m+1) (Fin b → F)))
    (hsource : C ≤ source (F := F) (2*m+1))
    (hC : IsLinearSharedCode singletonPartition C) :
    b*(m*m-(2*m+1)) ≤
      finrank F (source (F := F) (A := Fin b → F) (2*m+1)) - finrank F C := by
  rw [Nat.mul_sub_left_distrib]
  apply Nat.sub_le_iff_le_add.mpr
  simpa only [mul_assoc] using two_class_codimension C hsource hC

theorem two_class_positive_deletion (hm : 3 ≤ m) (hb : 0 < b)
    (C : Submodule F (State (2*m+1) (Fin b → F)))
    (hsource : C ≤ source (F := F) (2*m+1))
    (hC : IsLinearSharedCode singletonPartition C) :
    finrank F C < finrank F (source (F := F) (A := Fin b → F) (2*m+1)) := by
  have hc := two_class_codimension C hsource hC
  have hm' : 2*m+1 < m*m := by nlinarith
  have hmul : b*(2*m+1) < b*m*m := by nlinarith
  omega

omit [Field F] [CharP F 2] in
/-- The width cancels from the normalized deletion coefficient. -/
theorem deletion_rate_limit :
    Filter.Tendsto (fun m : ℕ =>
      ((m : ℝ)^2-(2*m+1))/((2*m+1)^2/4)) Filter.atTop (nhds 1) := by
  have h₁ := tendsto_add_mul_div_add_mul_atTop_nhds (𝕜 := ℝ) 0 1 1
    (d := 2) (by norm_num)
  have h₀ := tendsto_add_mul_div_add_mul_atTop_nhds (𝕜 := ℝ) 1 1 0
    (d := 2) (by norm_num)
  have h := (h₁.pow 2).const_mul 4 |>.sub (h₀.const_mul 4)
  convert h using 1
  · funext m
    have hn : (1+2*(m : ℝ)) ≠ 0 := by positivity
    have hn' : (2*(m : ℝ)+1) ≠ 0 := by positivity
    field_simp
    ring
  · norm_num

end SharedDecoders.CapacityReflection
