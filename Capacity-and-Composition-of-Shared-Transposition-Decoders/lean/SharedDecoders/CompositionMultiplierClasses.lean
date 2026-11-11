import SharedDecoders.CompositionMultiplierGetters
import SharedDecoders.CompositionRatio

/-! Class costs for the literal conjugated multiplier operations. The final
residue conclusion starts from actual covariance and balanced fibre sizes. -/

namespace SharedDecoders

open Module IntermediateField

variable {F E : Type*} [Field F] [Fintype F] [Field E] [Finite E] [Algebra F E]

/-- `Phi^c L Phi L^-1 Phi^-c` in the field coordinates of a reversed
normal basis. For a nonzero multiplier all five factors are permutations. -/
noncomputable def fieldMultiplierConjugate (lam : E) (c : ℕ) (x : E) : E :=
  let φ := FiniteField.frobeniusAlgEquivOfAlgebraic F E
  (φ ^ c) (lam * φ (lam⁻¹ * (φ ^ c).symm x))

theorem fieldMultiplierConjugate_eq (lam : E) (c : ℕ) (x : E) :
    fieldMultiplierConjugate (F := F) lam c x =
      (FiniteField.frobeniusAlgEquivOfAlgebraic F E ^ c)
        (multiplierCoefficient (F := F) lam) *
          FiniteField.frobeniusAlgEquivOfAlgebraic F E x := by
  let φ := FiniteField.frobeniusAlgEquivOfAlgebraic F E
  have hc (y : E) : (φ ^ c) (φ y) = φ ((φ ^ c) y) := by
    simpa only [pow_one, AlgEquiv.mul_apply] using
      congrArg (fun e : E ≃ₐ[F] E => e y) (pow_mul_comm φ c 1)
  change (φ ^ c) (lam * φ (lam⁻¹ * (φ ^ c).symm x)) =
    (φ ^ c) (lam / φ lam) * φ x
  simp only [map_mul, hc, map_inv₀, AlgEquiv.apply_symm_apply,
    div_eq_mul_inv, mul_assoc]

omit [Field F] [Finite E] [Algebra F E] in
theorem multiplierCoefficient_ne_zero (lam : E) (hlam : lam ≠ 0) :
    multiplierCoefficient (F := F) lam ≠ 0 := div_ne_zero hlam (pow_ne_zero _ hlam)

/-- The ratio scope check uses the displayed actual conjugates, not a
separately supplied semilinear covariance identity. -/
theorem ratio_multiplier_conjugate_covariance (lam : E) (hlam : lam ≠ 0)
    (c : ℕ) (x : E × E × E) :
    ratioDecoder (fieldMultiplierConjugate (F := F) lam c x.1,
      fieldMultiplierConjugate (F := F) lam c x.2.1,
      fieldMultiplierConjugate (F := F) lam c x.2.2) =
        FiniteField.frobeniusAlgEquivOfAlgebraic F E (ratioDecoder x) := by
  simp only [fieldMultiplierConjugate_eq]
  simpa only [AlgEquiv.coe_ringEquiv] using ratioDecoder_semilinear
    (FiniteField.frobeniusAlgEquivOfAlgebraic F E).toRingEquiv
    ((FiniteField.frobeniusAlgEquivOfAlgebraic F E ^ c) (multiplierCoefficient (F := F) lam))
    ((map_ne_zero _).mpr (multiplierCoefficient_ne_zero lam hlam)) x

/-- A shared second-layer decoder can join only equal Frobenius phases of
the actual conjugate coefficient. -/
theorem multiplier_class_residue {d : ℕ} {I K Z : Type*} [Finite I] [Nontrivial Z]
    (lam : E) (hlam : lam ≠ 0) (p : Fin d → K) (f : K → (I → E) → Z)
    (σ : Z → Z) (n : ℕ)
    (hcov : ∀ c x, f (p c) (fun i => fieldMultiplierConjugate (F := F) lam c (x i)) =
      σ (f (p c) x))
    (hbal : ∀ c z, Nat.card {x : I → E // f (p c) x = z} = Fintype.card F ^ n)
    {c e : Fin d} (hp : p c = p e) :
    c.val % finrank F (adjoin F {multiplierCoefficient (F := F) lam}) =
      e.val % finrank F (adjoin F {multiplierCoefficient (F := F) lam}) := by
  let φ := FiniteField.frobeniusAlgEquivOfAlgebraic F E
  let coeff := multiplierCoefficient (F := F) lam
  have hn (i : ℕ) : (φ ^ i) coeff ≠ 0 :=
    (map_ne_zero (φ ^ i)).mpr (multiplierCoefficient_ne_zero lam hlam)
  let μ : Eˣ := Units.mk0 ((φ ^ c.val) coeff) (hn c)
  let ν : Eˣ := Units.mk0 ((φ ^ e.val) coeff) (hn e)
  obtain ⟨z, hz⟩ := exists_ne (f (p c) 0)
  have hcop : Nat.Coprime (Nat.card E - 1) (Fintype.card F) := by
    apply extension_card_coprime _ (finrank F E) Fintype.card_pos Module.finrank_pos
    simpa only [Nat.card_eq_fintype_card] using
      Module.natCard_eq_pow_finrank (K := F) (V := E)
  have hμν := semilinear_covariance_multipliers_equal φ.toRingEquiv μ ν σ
    (Fintype.card F) n hcop (f (p c))
    (by intro x; simpa only [μ, φ, coeff, Units.val_mk0, fieldMultiplierConjugate_eq, AlgEquiv.coe_ringEquiv] using hcov c x)
    (by intro x; simpa only [ν, φ, coeff, Units.val_mk0, fieldMultiplierConjugate_eq, AlgEquiv.coe_ringEquiv, ← hp] using hcov e x)
    z hz (hbal c z)
  apply (LeanMachine.frobenius_powers_equal_iff F E coeff c e).mp
  exact congrArg Units.val hμν

/-- Any initial receiver interval realizes as many distinct classes as its
length or the coefficient degree, whichever is smaller. No full-period or
extension-degree lower bound on the receiver count is needed. -/
theorem multiplier_class_count_prefix {d : ℕ} {I K Z : Type*}
    [Finite I] [Nontrivial Z]
    (lam : E) (hlam : lam ≠ 0) (p : Fin d → K) (f : K → (I → E) → Z)
    (σ : Z → Z) (n : ℕ)
    (hcov : ∀ c x, f (p c) (fun i => fieldMultiplierConjugate (F := F) lam c (x i)) =
      σ (f (p c) x))
    (hbal : ∀ c z, Nat.card {x : I → E // f (p c) x = z} = Fintype.card F ^ n) :
    min d (finrank F (adjoin F {multiplierCoefficient (F := F) lam})) ≤
      Nat.card (Set.range p) := by
  let h := finrank F (adjoin F {multiplierCoefficient (F := F) lam})
  let emb (c : Fin (min d h)) : Fin d := ⟨c, c.2.trans_le (min_le_left _ _)⟩
  have hi : Function.Injective (fun c : Fin (min d h) => p (emb c)) := by
    intro c e hce
    apply Fin.ext
    have he := multiplier_class_residue lam hlam p f σ n hcov hbal hce
    change c.val % h = e.val % h at he
    simpa only [Nat.mod_eq_of_lt (c.2.trans_le (min_le_right _ _)),
      Nat.mod_eq_of_lt (e.2.trans_le (min_le_right _ _))] using he
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective
    (fun c : Fin (min d h) => (⟨p (emb c), emb c, rfl⟩ : Set.range p))
    (fun c e hce => hi (congrArg Subtype.val hce))

/-- The full-degree class bound, retained as a consequence of the sharper
prefix count. -/
theorem multiplier_class_count {d : ℕ} {I K Z : Type*} [Finite I] [Fintype K] [Nontrivial Z]
    (lam : E) (hlam : lam ≠ 0) (p : Fin d → K) (f : K → (I → E) → Z)
    (σ : Z → Z) (n : ℕ) (hd : finrank F E ≤ d)
    (hcov : ∀ c x, f (p c) (fun i => fieldMultiplierConjugate (F := F) lam c (x i)) =
      σ (f (p c) x))
    (hbal : ∀ c z, Nat.card {x : I → E // f (p c) x = z} = Fintype.card F ^ n) :
    finrank F (adjoin F {multiplierCoefficient (F := F) lam}) ≤ Fintype.card K := by
  have hh : finrank F (adjoin F {multiplierCoefficient (F := F) lam}) ≤ d :=
    (Submodule.finrank_le (adjoin F {multiplierCoefficient (F := F) lam}).toSubalgebra.toSubmodule).trans hd
  have hcount := multiplier_class_count_prefix lam hlam p f σ n hcov hbal
  have hrange : Nat.card (Set.range p) ≤ Fintype.card K := by
    simpa only [Nat.card_eq_fintype_card] using
      Nat.card_le_card_of_injective (Subtype.val : Set.range p → K) Subtype.val_injective
  have hc : finrank F (adjoin F {multiplierCoefficient (F := F) lam}) ≤ Nat.card (Set.range p) := by
    simpa only [min_eq_right hh] using hcount
  exact hc.trans hrange

end SharedDecoders
