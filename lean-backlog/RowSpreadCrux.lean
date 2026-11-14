import ConeCodeTransfer
import WindowSpread

/-!
# Whole-row cardinality bounds imply the native coding crux

The open whole-row bound is a hypothesis, not an axiom or a proved capacity
statement. The transfer uses the actual native cone system and allows arbitrary
nonlinear binary index codes. Canonical widths and all positive widths are
separate corollaries of one proof.
-/

namespace LeanBacklog.RowSpread

open Finset BoundedNesting MergeDepth BoundedStackDepth Transpose Transpose.Tape
open WindowSpread
open scoped BigOperators

/-- Number of possible raw reads in an old cone at edge depth D. -/
def rawConeSize (k D : ℕ) : ℕ :=
  ∑ j ∈ range (D + 1), (k + 1) ^ j

/-- Finite coding transfer for any trace with a complete output prefix.
No correctness, obliviousness, or cheapness of the old cut is assumed.
The payment is 63/64 + 21/32 = 105/64 before capacity slack. -/
theorem native_indexCode_bound_of_wholeRow
    {k d b T D m : ℕ} {C ε a : ℝ}
    (hC : 1 ≤ C) (hε : 0 < ε) (hd : 4 ≤ d) (hb : 1 ≤ b)
    (τ : Trace k)
    (hT : (T : ℝ) ≤ C * ((d * d * b : ℕ) + 1))
    (happ : d * d * b ≤ (appendList τ T).length)
    (Γ : Finset ℕ)
    (hdepth : ∀ π, IsDepPath τ.work T π → LinNet.GFree Γ π →
      π.length ≤ D + 1)
    (hbound : WholeRowCardinalityBound d
      (rowSpreadWindow k (rawConeSize k D) D C ε) (Fin b → Bool) a)
    (enc : (Fin (d * d * b) → Bool) → (Fin m → Bool))
    (henc : IsIndexCode enc (coneSystem τ T Γ d b) (tposOf d b)) :
    (d * d * b : ℕ) ≤ (m : ℝ) + (105 / 64 : ℝ) * ε * (d * d * b : ℕ)
      + (b : ℝ) * a := by
  classical
  obtain ⟨Γ', E, ρ, hΓ, _, hcut, hE, hwidth, hrows, _⟩ :=
    native_row_spread_prefix (β := rawConeSize k D) hC hε hd hb τ T hT happ Γ hdepth
  let U := (Γ' \ Γ).biUnion (fun u =>
    depCone τ.work T (readPos τ (d * d * b)) Γ u)
  have hUcard : U.card ≤ (Γ' \ Γ).card * rawConeSize k D :=
    card_new_cut_raw_support_le τ.work (readPos τ (d * d * b)) Γ Γ' hdepth
  have hU : (U.card : ℝ) ≤ (63 / 64 : ℝ) * ε * (d * d * b : ℕ) := by
    have hU' : (U.card : ℝ) ≤ ((Γ' \ Γ).card : ℝ) * rawConeSize k D := by
      exact_mod_cast hUcard
    nlinarith
  have hcolumns : (d * E.card * b : ℕ) ≤
      (21 / 32 : ℝ) * ε * (d * d * b : ℕ) := by
    have hmul := mul_le_mul_of_nonneg_right hE
      (show (0 : ℝ) ≤ (d : ℝ) * b by positivity)
    push_cast at hmul ⊢
    nlinarith
  have hfinite := indexCode_length_le_of_wholeRowBound
    ρ E U (coneSystem τ T Γ d b) (coneSystem τ T Γ' d b)
    a (coneSystem_change_cut τ Γ Γ') hrows hwidth hbound enc henc
  push_cast at hfinite hU hcolumns ⊢
  nlinarith only [hfinite, hU, hcolumns]

/-- One proof covers any prescribed family of positive bit widths. The
threshold is uniform in widths satisfying widthOK. -/
theorem cruxOn_of_wholeRowBounds
    {k β D : ℕ} {C δ : ℝ} (hC : 1 ≤ C)
    (widthOK : ℕ → ℕ → Prop)
    (hpos : ∀ d b, widthOK d b → 1 ≤ b)
    (hbound : ∀ (w : ℕ) (η : ℝ), 0 < η → ∃ d₀ : ℕ, ∀ d ≥ d₀,
      ∀ b, widthOK d b →
        WholeRowCardinalityBound d w (Fin b → Bool)
          ((1 - δ + η) * (d : ℝ) ^ 2)) :
    CruxOn widthOK k C β D δ := by
  intro η hη
  let ε := η / 3
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨d₀, hd₀⟩ := hbound (rowSpreadWindow k (rawConeSize k D) D C ε) ε hε
  refine ⟨max d₀ 4, ?_⟩
  intro d hd b hb I hI m enc henc
  obtain ⟨M, T, Γ, hk, _, _, hT, happ, hdepth, rfl⟩ := hI
  subst k
  have hcode := native_indexCode_bound_of_wholeRow hC hε (by omega : 4 ≤ d)
    (hpos d b hb) (traceAt M (d * d * b)) hT (le_of_eq happ.symm) Γ hdepth
    (hd₀ d (by omega) b hb) enc henc
  have hnonneg : 0 ≤ η * (d * d * b : ℕ) := by positivity
  dsimp [ε] at hcode
  push_cast at hcode hnonneg ⊢
  nlinarith

/-- Corollary 4 at exactly the canonical, growing bit-entry alphabets.
The common deficit remains an explicit hypothesis. -/
theorem uniformWholeRowRateCanonicalBits_crux
    {k β D : ℕ} {C δ : ℝ} (hC : 1 ≤ C)
    (hbound : UniformWholeRowRateCanonicalBits (1 - δ)) :
    Crux k C β D δ := by
  apply cruxOn_of_wholeRowBounds hC (fun d b => b = entryBits d)
    (fun d b hb => by simpa [hb] using one_le_entryBits d)
  intro w η hη
  obtain ⟨d₀, hd₀⟩ := hbound w η hη
  exact ⟨d₀, fun d hd b hb => by subst b; exact hd₀ d hd⟩

/-- The all-alphabet hypothesis yields a dimension threshold uniform in
every positive bit width; it is stronger than the canonical-width claim. -/
theorem uniformWholeRowRate_cruxOn
    {k β D : ℕ} {C δ : ℝ} (hC : 1 ≤ C)
    (hbound : UniformWholeRowRate.{0} (1 - δ)) :
    CruxOn (fun _ b => 1 ≤ b) k C β D δ := by
  apply cruxOn_of_wholeRowBounds hC (fun _ b => 1 ≤ b) (fun _ _ hb => hb)
  intro w η hη
  obtain ⟨d₀, hd₀⟩ := hbound w η hη
  refine ⟨d₀, fun d hd b hb => hd₀ d hd (Fin b → Bool) ?_⟩
  simpa using (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hb)

/-- A common positive canonical whole-row deficit rules out oblivious
linear-time transposers, using Paper 14's existing crux_excludes. -/
theorem uniformWholeRowRateCanonicalBits_excludes
    {k β : ℕ} {C δ : ℝ} (hC : 1 ≤ C) (hδ : 0 < δ)
    (hbound : UniformWholeRowRateCanonicalBits (1 - δ)) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ M : TM, M.k = k → valueWidth M ≤ β → ∀ T : ℕ,
      ¬ ObliviousLinTime M d (entryBits d) C T :=
  crux_excludes (ε := δ / 2) hC (by positivity) (by linarith)
    (uniformWholeRowRateCanonicalBits_crux hC hbound)

/-- The direct machine route, Corollary 3: it only needs a capacity bound
at its one explicit window, and retains the sharper 169/64 invoice. -/
theorem wholeRow_window_bound_excludes
    {k β : ℕ} {C ε δ : ℝ} (hC : 1 ≤ C) (hε : 0 < ε)
    (hgap : (169 / 64 : ℝ) * ε < δ)
    (hbound : ∀ η : ℝ, 0 < η → ∃ d₀ : ℕ, ∀ d ≥ d₀,
      WholeRowCardinalityBound d
        (rowSpreadWindow k β (genieDepth k β C ε) C ε)
        (Fin (entryBits d) → Bool) ((1 - δ + η) * (d : ℝ) ^ 2)) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ M : TM, M.k = k → valueWidth M ≤ β → ∀ T : ℕ,
      ¬ ObliviousLinTime M d (entryBits d) C T := by
  let η := (δ - (169 / 64 : ℝ) * ε) / 2
  have hη : 0 < η := by dsimp [η]; linarith
  obtain ⟨d₀, hd₀⟩ := hbound η hη
  refine ⟨max d₀ 4, ?_⟩
  intro d hd M hk hβ T ⟨hobl, hT, htr⟩
  subst k
  have hd4 : 4 ≤ d := by omega
  have hd1 : 1 ≤ d := by omega
  have hb : 1 ≤ entryBits d := one_le_entryBits d
  have hL : 1 ≤ d * d * entryBits d := Nat.mul_pos (Nat.mul_pos hd1 hd1) hb
  have hβ1 : 1 ≤ β := (by omega : 1 ≤ 2).trans ((two_le_valueWidth M).trans hβ)
  obtain ⟨hM, happ⟩ := obliviousTransposer_of_transposes hobl htr (fun _ => false)
  obtain ⟨Γ, hcost, hpath⟩ :=
    genie_of_trace M (List.ofFn fun _ : Fin (d * d * entryBits d) => false)
      hβ1 hL hC hε hT
  obtain ⟨Γ', E, ρ, hΓ, _, hnew, hE, hwidth, hrows, _⟩ :=
    native_row_spread_prefix (β := β) hC hε hd4 hb
      (traceAt M (d * d * entryBits d)) T hT (le_of_eq happ.symm) Γ
      (fun π hp hf => (hpath π hp hf).trans (Nat.le_succ _))
  obtain ⟨enc, henc⟩ := exists_indexCode hM hβ Γ'
  have hfinite := indexCode_length_le_of_wholeRowBound
    ρ E ∅ _ _ ((1 - δ + η) * (d : ℝ) ^ 2)
    (fun _ => subset_union_left) hrows hwidth
    (hd₀ d (by omega)) enc henc
  have hsplit : ((Γ' \ Γ).card : ℝ) + Γ.card = Γ'.card := by
    exact_mod_cast card_sdiff_add_card_eq_card hΓ
  have htotal : (β * Γ'.card : ℝ) ≤
      (127 / 64 : ℝ) * ε * (d * d * entryBits d : ℕ) := by
    push_cast at hcost hnew ⊢
    nlinarith
  have hcolumns : (d * E.card * entryBits d : ℕ) ≤
      (21 / 32 : ℝ) * ε * (d * d * entryBits d : ℕ) := by
    have hmul := mul_le_mul_of_nonneg_right hE
      (show (0 : ℝ) ≤ (d : ℝ) * entryBits d by positivity)
    push_cast at hmul ⊢
    nlinarith
  have hpositive : 0 < (δ - (169 / 64 : ℝ) * ε) *
      (d * d * entryBits d : ℕ) := mul_pos (by linarith) (by exact_mod_cast (show 0 < d * d * entryBits d by omega))
  simp only [card_empty, Nat.cast_zero, add_zero] at hfinite
  dsimp [η] at hfinite
  push_cast at hfinite htotal hcolumns hpositive
  nlinarith

#print axioms native_indexCode_bound_of_wholeRow
#print axioms cruxOn_of_wholeRowBounds
#print axioms uniformWholeRowRateCanonicalBits_crux
#print axioms uniformWholeRowRate_cruxOn
#print axioms uniformWholeRowRateCanonicalBits_excludes
#print axioms wholeRow_window_bound_excludes

end LeanBacklog.RowSpread
