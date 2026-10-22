import TransposeFollowup.DyadicCenterTrimming
import TransposeFollowup.NilpotentExtractionParameters
import TransposeFollowup.LocalizedFixedProductEnvelope
import TransposeFollowup.TraceReextractionCubicBound

/-! Pay the full second-extraction trace bound from the actual profile.
The chart proof is shared with the first extraction, using a smaller
radius and the spare exponent margin in the actual-word growth theorem. -/
namespace TransposeFollowup.SL2Projection
open Classical Matrix Set RealMobius BoundedCoordinatePacking
open scoped Pointwise Matrix.Norms.Frobenius ENNReal NNReal
set_option autoImplicit false
local notation "RMat" => Matrix (Fin 2) (Fin 2) ℝ
local notation "G" => RealMobius.Group
local notation "H₀" => (4 : ℝ) ^ 34
local notation "R₀" => (4 : ℝ) ^ 68
local notation "M₀" => 128 * R₀ ^ 2

/-- The actual word cost can be paid at any fixed length. The older
283-length cutoff is only one numerical specialization. -/
theorem profile_power_exponent_bound_of_cost {η θ τ h : ℝ} {n : ℕ}
    (hη : 0 < η) (hηone : η ≤ 1) (hh : 0 ≤ h)
    (hprofile : h ≤ η ^ (-τ))
    (hmargin : ((8802*n+4427 : ℕ) : ℝ)*τ ≤ θ) :
    h ^ (8802*n+4427) ≤ η ^ (-θ) := by
  calc
    _ ≤ (η ^ (-τ)) ^ (8802*n+4427) := pow_le_pow_left₀ hh hprofile _
    _ = η ^ (-(((8802*n+4427 : ℕ) : ℝ)*τ)) := by
      rw [← Real.rpow_mul_natCast hη.le]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hη hηone (neg_le_neg hmargin)

theorem profile_power_exponent_bound {η θ τ h : ℝ} {n : ℕ}
    (hη : 0 < η) (hηone : η ≤ 1) (hτ : 0 ≤ τ) (hh : 0 ≤ h)
    (hprofile : h ≤ η ^ (-τ)) (hmargin : 3000000 * τ ≤ θ) (hn : n ≤ 283) :
    h ^ (8802 * n + 4427) ≤ η ^ (-θ) := by
  have hnR : ((8802*n+4427 : ℕ) : ℝ) ≤ 3000000 := by
    exact_mod_cast (show 8802*n+4427 ≤ 3000000 by omega)
  exact profile_power_exponent_bound_of_cost hη hηone hh hprofile
    ((mul_le_mul_of_nonneg_right hnR hτ).trans hmargin)

theorem full_trace_coefficient_power_bound
    {η θ H S L E P J N Hc Sc Lc Ec : ℝ}
    (hη : 0 < η) (hηone : η ≤ 1) (hθ : 0 ≤ θ)
    (hH : 0 ≤ H) (hS : 0 ≤ S) (hL : 0 ≤ L) (hE : 0 ≤ E)
    (hP : 0 ≤ P) (hJ : 0 ≤ J) (hN : 1 ≤ N)
    (hHc : 0 ≤ Hc) (hSc : 0 ≤ Sc) (hLc : 0 ≤ Lc) (hEc : 0 ≤ Ec)
    (hHb : H ≤ Hc * η ^ (-(16 * θ)))
    (hSb : S ≤ Sc * η ^ (-(72 * θ)))
    (hLb : L ≤ Lc * η ^ (-(88 * θ)))
    (hEb : E ≤ Ec * η ^ (-(16 * θ)))
    (hPb : P ≤ η ^ (-θ)) (hJb : J ≤ η ^ (-θ)) :
    (9 * P * H) ^ 3 * (4 * (S * L) ^ 3 * (E * J * N + 1)) ≤
      ((9 * Hc) ^ 3 * (4 * (Sc * Lc) ^ 3 * (Ec + 1))) * η ^ (-(548 * θ)) * N := by
  let T := η ^ (-θ)
  have hT : 1 ≤ T := Real.one_le_rpow_of_pos_of_le_one_of_nonpos
    hη hηone (neg_nonpos.mpr hθ)
  have hT0 : 0 ≤ T := zero_le_one.trans hT
  have hN0 : 0 ≤ N := zero_le_one.trans hN
  have hp (n : ℕ) : T ^ n = η ^ (-((n : ℝ) * θ)) := by
    dsimp only [T]
    rw [← Real.rpow_mul_natCast hη.le]
    congr 1
    ring
  have hH' : H ≤ Hc * T ^ 16 := by simpa only [hp, Nat.cast_ofNat] using hHb
  have hS' : S ≤ Sc * T ^ 72 := by simpa only [hp, Nat.cast_ofNat] using hSb
  have hL' : L ≤ Lc * T ^ 88 := by simpa only [hp, Nat.cast_ofNat] using hLb
  have hE' : E ≤ Ec * T ^ 16 := by simpa only [hp, Nat.cast_ofNat] using hEb
  have he : E * J * N ≤ Ec * T ^ 17 * N := by
    calc
      _ ≤ (Ec * T ^ 16) * T * N := by gcongr
      _ = _ := by ring
  have hone : 1 ≤ T ^ 17 * N := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hT) hN
  have hinner : E * J * N + 1 ≤ (Ec + 1) * T ^ 17 * N := by
    nlinarith only [he, hone]
  have hfinal : (9 * P * H) ^ 3 * (4 * (S * L) ^ 3 * (E * J * N + 1)) ≤
      ((9 * Hc) ^ 3 * (4 * (Sc * Lc) ^ 3 * (Ec + 1))) * T ^ 548 * N := by
    calc
      _ ≤ (9 * T * (Hc * T ^ 16)) ^ 3 *
          (4 * ((Sc * T ^ 72) * (Lc * T ^ 88)) ^ 3 * ((Ec + 1) * T ^ 17 * N)) := by
        gcongr
      _ = _ := by ring
  simpa only [hp, Nat.cast_ofNat] using hfinal

/-- The full reextraction argument is uniform in word length. Its two
covering costs are paid by the maximum of indices k+1 and 141. -/
theorem exists_reextracted_trace_power_bound_of_cost {θ a : ℝ}
    (hθ : 0 ≤ θ) (hθquarter : θ < 1 / 4) (ha : 0 < a) (haone : a ≤ 1) :
    ∃ U₀ : ℝ, 0 < U₀ ∧ ∃ J₀ : ℕ, ∀ j : ℕ, J₀ ≤ j →
      let η := (1 / 4 : ℝ) ^ j
      let ηn : ℝ≥0 := ⟨η, by positivity⟩
      ∀ {U A D : Set G} (Y : Finset G) (k : ℕ) {p q : G}
        {h Q α q₀ τ : ℝ} {Nprofile : ℕ},
      (2 : ℝ) ^ 100 ≤ h → (Nprofile : ℝ) ≤ h → 1 ≤ Q → Q ≤ h →
      0 < α → α ≤ 1 → α⁻¹ ^ 4 ≤ h → 0 < q₀ → q₀⁻¹ ≤ h →
      0 ≤ τ → ((8802*max (k+1) 141+4427 : ℕ) : ℝ)*τ ≤ θ → h ≤ η ^ (-τ) →
      (Y.card : ℝ) ≤ 512 * ((2 : ℝ) ^ 55 * (8 * ((64 * (Nprofile : ℝ) ^ 4) ^ 2 / q₀ ^ 2)) ^ 21) ^ 16 →
      U ⊆ matrixEntryBox Q → U⁻¹ = U → (Y : Set G) ⊆ U ^ 2 → U ^ 2 ⊆ (Y : Set G) * U →
      A = U ^ 2 ∩ mobiusIdentityBall α → 1 ∈ A → A⁻¹ = A →
      2 * (5 : ℝ) ^ 34 * α ≤ 1 →
      p ∈ A ^ 34 → q ∈ A ^ 34 → p * q ∈ A ^ 34 →
      η ^ θ ≤ |(SL2Escape.pairSpanMatrix (p : RMat) (q : RMat)).det| →
      D.Nonempty → D ⊆ A ^ k → D ⊆ mobiusIdentityBall (1 / 2) →
      (∀ w ∈ D, a * η ^ (3 * θ) ≤ dist (w : RMat) 1) →
      let N := (Metric.externalCoveringNumber ηn ((fun x : G => (x : RMat)) '' A) : ℝ≥0∞).toReal
      let T := (fun w : G => Matrix.trace (w : RMat)) '' D
      Metric.externalCoveringNumber ηn ((fun x : G => (x : RMat)) '' A) ≠ ⊤ ∧
      ∀ δ : ℝ≥0, ηn ≤ δ → Metric.externalCoveringNumber δ T ≠ ⊤ ∧
        (Metric.externalCoveringNumber δ T : ℝ≥0∞).toReal ^ 3 ≤
          U₀ * η ^ (-(548 * θ)) * N := by
  obtain ⟨b, s, l, e, f, rc, hb, hs, _hl, _he, hf, hrc, _hleq, _heeq, hparams⟩ :=
    exists_scaled_extraction_parameters (by norm_num : 1 ≤ H₀)
      (by norm_num : (1 : ℝ) ≤ 9) (by norm_num : 1 ≤ M₀) ha haone
  let e₂ := 819200 / a
  have he₂ : 0 < e₂ := by dsimp only [e₂]; positivity
  let Hc := (102400 * (2 : ℝ) ^ 7 / a + 8 * 2 + 1) ^ 4
  let Sc := 6561 * (4 * s + 1) ^ 4
  let Lc := (2 * 9 / b + 1) ^ 4
  let Ec := (80 * (2 * R₀) ^ 10 * e₂ + 8 * R₀ + 1) ^ 4
  let Uc := (9 * Hc) ^ 3 * (4 * (Sc * Lc) ^ 3 * (Ec + 1))
  have hHc : 0 ≤ Hc := by dsimp only [Hc]; positivity
  have hSc : 0 ≤ Sc := by dsimp only [Sc]; positivity
  have hLc : 0 ≤ Lc := by dsimp only [Lc]; positivity
  have hEc : 0 ≤ Ec := by dsimp only [Ec]; positivity
  have hUc : 0 ≤ Uc := by dsimp only [Uc]; positivity
  obtain ⟨J₀, hJ₀⟩ := exists_dyadic_scaled_rpow_bound he₂
    (show 0 < 1 - 4 * θ by linarith only [hθquarter])
  refine ⟨1 + Uc, by positivity, J₀, ?_⟩
  intro j hj η ηn U A D Y k p q h Q α q₀ τ Nprofile hlarge hNprofile hQ hQh
    hα hαone hαinv hq₀ hq₀inv hτ hmargin hprofile hYcard hU hUi hY hdouble
    hAloc hA1 hAi hαsmall hp hq hpq hspan hDn hDpow hDnear hDfar N T
  have hη : 0 < η := by dsimp only [η]; positivity
  have hηone : η ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have htwotheta : 0 ≤ 2 * θ := by positivity
  let r₀ := a * η ^ (2 * (2 * θ))
  let σ : ℝ≥0 := ⟨s * η ^ (1 - 9 * (2 * θ)), by positivity⟩
  have hr₀ : 0 < r₀ := by dsimp only [r₀]; positivity
  have hσ : 0 < σ := by change 0 < s * η ^ (1 - 9 * (2 * θ)); positivity
  have hDfar' (w : G) (hw : w ∈ D) : r₀ ≤ dist (w : RMat) 1 :=
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge hη hηone (by linarith only [hθ])) ha.le).trans (hDfar w hw)
  have hspan' : η ^ (2 * θ) ≤ |(SL2Escape.pairSpanMatrix (p : RMat) (q : RMat)).det| :=
    (Real.rpow_le_rpow_of_exponent_ge hη hηone (by linarith only [hθ])).trans hspan
  have herror : 819200 * η ≤ r₀ := by
    have hh := mul_le_mul_of_nonneg_right (hJ₀ j hj)
      (show 0 ≤ a * η ^ (4 * θ) by positivity)
    have heq : (e₂ * η ^ (1 - 4 * θ)) * (a * η ^ (4 * θ)) = 819200 * η := by
      calc
        _ = (e₂ * a) * (η ^ (1 - 4 * θ) * η ^ (4 * θ)) := by ring
        _ = 819200 * η := by
          rw [← Real.rpow_add hη, sub_add_cancel, Real.rpow_one]
          dsimp only [e₂]
          field_simp
    change (e₂ * η ^ (1 - 4 * θ)) * (a * η ^ (4 * θ)) ≤ 1 * (a * η ^ (4 * θ)) at hh
    rw [heq, one_mul] at hh
    simpa only [r₀, show 2 * (2 * θ) = 4 * θ by ring] using hh
  obtain ⟨hrone, hrsmall, hrabsorb, hbranch, hradius, hframe, hspacing, _hησ, _hL, _hε, _hscalar⟩ :=
    hparams η (2 * θ) hη hηone htwotheta
  obtain ⟨hTfin, hAfin, htrace⟩ := trace_reextraction_cubic_bound (η := ηn) (σ := σ) Y k
    hQ hU hUi hY hdouble hAloc hA1 hAi hα hαone hαsmall hp hq hpq
    (Real.rpow_pos_of_pos hη (2 * θ)) hspan' hDn hDpow hDnear hr₀ hDfar' hη hσ herror
    (by norm_num : 1 ≤ M₀) le_rfl (show 0 < b * η ^ (11 * (2 * θ)) by positivity)
    (show 0 ≤ rc * η ^ (9 * (2 * θ)) by positivity) hrone hbranch hradius.le
    (show 0 < f * η ^ (9 * (2 * θ)) by positivity) hframe.le hrsmall hrabsorb hspacing
  let P := fun n : ℕ => (8 * (2 * Q) ^ (4 * n + 3) + 1) ^ 4 *
    (Y.card : ℝ) ^ (2 * n + 1) * (33 ^ 4 * Q ^ 8 / α ^ 4)
  have hP (n : ℕ) (hn : n ≤ max (k+1) 141) : P n ≤ η ^ (-θ) :=
    (fixed_power_coefficient_bound n hlarge hNprofile (zero_le_one.trans hQ) hQh
      hα hαinv hq₀ hq₀inv (Nat.cast_nonneg _) hYcard).trans
      (profile_power_exponent_bound_of_cost hη hηone
        ((by norm_num : (0 : ℝ) ≤ 2 ^ 100).trans hlarge) hprofile
        ((mul_le_mul_of_nonneg_right
          (by exact_mod_cast (show 8802*n+4427 ≤ 8802*max (k+1) 141+4427 by omega)) hτ).trans hmargin))
  have hNpos := (Metric.externalCoveringNumber_pos_iff (ε := ηn)).mpr
    (show ((fun x : G => (x : RMat)) '' A).Nonempty from ⟨1, ⟨1, hA1, rfl⟩⟩)
  have hN1 : 1 ≤ N := by
    have hEN : (1 : ℕ∞) ≤ Metric.externalCoveringNumber ηn ((fun x : G => (x : RMat)) '' A) :=
      Order.one_le_iff_pos.mpr hNpos
    have hh := ENNReal.toReal_mono (ENat.toENNReal_ne_top.mpr hAfin) (ENat.toENNReal_mono hEN)
    simpa only [ENat.toENNReal_one, ENNReal.toReal_one] using hh
  obtain ⟨hHb, hSb, hLb, hEb, _⟩ := first_extraction_cost_bounds
    (l := 1) hη hηone htwotheta ha hb hs he₂.le
    (by norm_num : (0 : ℝ) ≤ 9) (by norm_num : (0 : ℝ) ≤ 2) (by positivity : 0 ≤ R₀)
  have heps : e₂ * η ^ (1 - 2 * (2 * θ)) = 819200 * η / r₀ := by
    dsimp only [e₂, r₀]
    rw [Real.rpow_sub hη, Real.rpow_one]
    ring
  rw [heps] at hEb
  simp only [show 8 * (2 * θ) = 16 * θ by ring,
    show 36 * (2 * θ) = 72 * θ by ring, show 44 * (2 * θ) = 88 * θ by ring] at hHb hSb hLb hEb
  have hcost := full_trace_coefficient_power_bound hη hηone hθ
    (by positivity) (by positivity) (Nat.cast_nonneg _) (by positivity)
    (show 0 ≤ P (k + 1) by dsimp only [P]; positivity)
    (show 0 ≤ P 141 by dsimp only [P]; positivity)
    hN1 hHc hSc hLc hEc hHb hSb hLb hEb (hP (k + 1) (le_max_left _ _)) (hP 141 (le_max_right _ _))
  have hnative : (Metric.externalCoveringNumber ηn T : ℝ≥0∞).toReal ^ 3 ≤
      (1 + Uc) * η ^ (-(548 * θ)) * N := by
    apply (htrace.trans hcost).trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (by positivity))
      (zero_le_one.trans hN1)
  refine ⟨hAfin, ?_⟩
  intro δ hηδ
  have hmono := Metric.externalCoveringNumber_anti (A := T) hηδ
  refine ⟨ne_top_of_le_ne_top hTfin hmono, ?_⟩
  exact (pow_le_pow_left₀ ENNReal.toReal_nonneg
    (ENNReal.toReal_mono (ENat.toENNReal_ne_top.mpr hTfin) (ENat.toENNReal_mono hmono)) 3).trans hnative

end TransposeFollowup.SL2Projection
