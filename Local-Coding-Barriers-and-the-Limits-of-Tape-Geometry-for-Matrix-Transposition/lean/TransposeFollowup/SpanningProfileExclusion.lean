import TransposeFollowup.TraceSquareDyadicTraceGrowth
import TransposeFollowup.QuantitativeSpanningExtraction
import TransposeFollowup.NilpotentProfileExclusion

/-! Exclude the spanning localized profile by constructing the original
commuting family, applying actual trace-square growth, and comparing it
with the full reextraction bound. The common profile cost pays the actual
(universally chosen) extraction length as well as the length-420 words. -/
namespace TransposeFollowup.SL2Projection
open Classical Matrix Set RealMobius
open scoped Pointwise Matrix.Norms.Frobenius ENNReal NNReal
set_option autoImplicit false
local notation "RMat" => Matrix (Fin 2) (Fin 2) ℝ
local notation "G" => RealMobius.Group

/-- There is no input satisfying all the displayed localized-profile,
spanning-frame, distribution and size hypotheses at sufficiently fine
native scales. The source family and its quantitative extraction cube
are constructed in the proof, not assumed. -/
theorem exists_spanning_profile_exclusion {κ : ℝ} (hκ : 0 < κ) (hκone : κ ≤ 1) :
    ∃ θ α₀ : ℝ, ∃ L J : ℕ,
      0 < θ ∧ θ < 1/4 ∧ 0 < α₀ ∧ α₀ ≤ 1 ∧ 0 < L ∧
      ∀ j : ℕ, J ≤ j →
        let η := (1/4 : ℝ)^j
        let ηn : ℝ≥0 := ⟨η, by positivity⟩
        ∀ {U A : Set G} (Y : Finset G) {h Q α q₀ τ : ℝ} {Nprofile : ℕ},
        (2 : ℝ)^100 ≤ h → (Nprofile : ℝ) ≤ h → 1 ≤ Q → Q ≤ h →
        0 < α → α ≤ α₀ → α⁻¹^4 ≤ h → 0 < q₀ → q₀⁻¹ ≤ h →
        0 ≤ τ → (L : ℝ)*τ ≤ θ → h ≤ η^(-τ) →
        (Y.card : ℝ) ≤ 512*((2 : ℝ)^55*(8*((64*(Nprofile : ℝ)^4)^2/q₀^2))^21)^16 →
        U ⊆ matrixEntryBox Q → U⁻¹=U → (Y : Set G) ⊆ U^2 → U^2 ⊆ (Y : Set G)*U →
        A=U^2 ∩ mobiusIdentityBall α → 1 ∈ A → A⁻¹=A →
        ∀ {p q : G}, p ∈ A^34 → q ∈ A^34 → p*q ∈ A^34 →
        η^θ ≤ |(SL2Escape.pairSpanMatrix (p : RMat) (q : RMat)).det| →
        (∀ ρ : ℝ, η < ρ → ρ < η^(θ/2) →
          ∃ T : Finset G, (T : Set G) ⊆ A ∧
            Metric.IsSeparated (ENNReal.ofReal ρ) ((fun x : G => (x : RMat)) '' (T : Set G)) ∧
            ρ^(-κ) ≤ (T.card : ℝ)) →
        let N := (Metric.externalCoveringNumber ηn ((fun x : G => (x : RMat)) '' A) : ℝ≥0∞).toReal
        N ≤ η^(-(3-κ)) → False := by
  obtain ⟨n₀, αext, Cext, _hn₀, hαext, hαextHalf, hCext, hextract⟩ :=
    exists_quantitative_spanning_commuting_extraction
  obtain ⟨Θ, θ, gain, αg, a₂, Ws, Jg, hΘ, hΘquarter, hθ, hθΘ,
    _hgain, hgainMargin, hαg, ha₂, hWs, hgrowth⟩ :=
    exists_trace_square_dyadic_trace_growth hκ hκone hCext
  let a := min a₂ 1
  have ha : 0 < a := lt_min ha₂ zero_lt_one
  have haone : a ≤ 1 := min_le_right _ _
  obtain ⟨U₀, hU₀, Ju, hupper⟩ :=
    exists_reextracted_trace_power_bound_of_cost hΘ.le hΘquarter ha haone
  obtain ⟨Jc, hcharge⟩ := exists_dyadic_scaled_rpow_bound
    (show 0 < 250^3*U₀*Ws by positivity)
    (show 0 < 3*gain-691*Θ by linarith only [hgainMargin])
  have hθquarter : θ < 1/4 := hθΘ.trans_lt hΘquarter
  obtain ⟨Je, herror⟩ := exists_dyadic_scaled_rpow_bound
    (by norm_num : (0 : ℝ) < 786432)
    (show 0 < 1-θ by linarith only [hθquarter])
  let B := max 421 (n₀+2)
  let L := 8802*B+4427
  let α₀ := min αext (min αg (1/(2*(5 : ℝ)^34)))
  have hα₀ : 0 < α₀ := by dsimp only [α₀]; positivity
  have hα₀one : α₀ ≤ 1 := (min_le_left _ _).trans (hαextHalf.trans (by norm_num))
  refine ⟨θ, α₀, L, max Jg (max Ju (max Jc Je)), hθ, hθquarter, hα₀, hα₀one,
    by dsimp only [L]; omega, ?_⟩
  intro j hj η ηn U A Y h Q α q₀ τ Nprofile hlarge hNprofile hQ hQh hα hαbound hαinv
    hq₀ hq₀inv hτ hmargin hprofile hYcard hU hUi hY hdouble hAloc hA1 hAi p q hp hq hpq hspan
    hdistribution N hNbound
  have hjg : Jg ≤ j := (le_max_left _ _).trans hj
  have hju : Ju ≤ j := by omega
  have hjc : Jc ≤ j := by omega
  have hje : Je ≤ j := by omega
  have hη : 0 < η := by dsimp only [η]; positivity
  have hηone : η ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hαextBound : α ≤ αext := hαbound.trans (min_le_left _ _)
  have hαgBound : α ≤ αg := hαbound.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hαone : α ≤ 1 := hαbound.trans hα₀one
  have hαsmall : 2*(5 : ℝ)^34*α ≤ 1 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2*(5 : ℝ)^34)).mp
      (hαbound.trans ((min_le_right _ _).trans (min_le_right _ _)))
    simpa only [mul_comm] using hh
  have hA : A ⊆ mobiusIdentityBall α := by rw [hAloc]; exact Set.inter_subset_right
  have hcost (n : ℕ) (hn : n ≤ B) : ((8802*n+4427 : ℕ) : ℝ)*τ ≤ θ :=
    (mul_le_mul_of_nonneg_right
      (by exact_mod_cast (show 8802*n+4427 ≤ L by dsimp only [L]; omega)) hτ).trans hmargin
  have hcoef (n : ℕ) (hn : n ≤ B) :
      (8*(2*Q)^(4*n+3)+1)^4*(Y.card : ℝ)^(2*n+1)*(33^4*Q^8/α^4) ≤ η^(-θ) :=
    (fixed_power_coefficient_bound n hlarge hNprofile (zero_le_one.trans hQ) hQh
      hα hαinv hq₀ hq₀inv (Nat.cast_nonneg _) hYcard).trans
      (profile_power_exponent_bound_of_cost hη hηone
        ((by norm_num : (0 : ℝ) ≤ 2^100).trans hlarge) hprofile (hcost n hn))
  have hcover (n : ℕ) (hn : n ≤ B) :
      Metric.externalCoveringNumber ηn ((fun x : G => (x : RMat)) '' A) ≠ ⊤ ∧
      Metric.externalCoveringNumber ηn ((fun x : G => (x : RMat)) '' (A^(n+1))) ≠ ⊤ ∧
      (Metric.externalCoveringNumber ηn ((fun x : G => (x : RMat)) '' (A^(n+1))) : ℝ≥0∞).toReal ≤
        η^(-θ)*N := by
    obtain ⟨hAfin, hPfin, hPbound⟩ := localized_set_pow_coveringNumber (η := ηn) Y n
      hQ hα hαone hη hU hUi hY hdouble
    rw [← hAloc] at hAfin hPfin hPbound
    exact ⟨hAfin, hPfin, hPbound.trans (mul_le_mul_of_nonneg_right (hcoef n hn) ENNReal.toReal_nonneg)⟩
  have hB421 : 421 ≤ B := le_max_left _ _
  have hBn₀ : n₀+2 ≤ B := le_max_right _ _
  have h284 := (hcover 283 (by omega)).2.2
  have h142 := (hcover 141 (by omega)).2.2
  have hd : 0 < η^θ := Real.rpow_pos_of_pos hη _
  have hd1 : η^θ ≤ 1 := Real.rpow_le_one hη.le hηone hθ.le
  have hsmall : 1536*(2 : ℝ)^4*η ≤ η^θ/32 := by
    have hh := mul_le_mul_of_nonneg_right (herror j hje) hd.le
    have heq : η^(1-θ)*η^θ = η := by rw [← Real.rpow_add hη, sub_add_cancel, Real.rpow_one]
    change (786432*η^(1-θ))*η^θ ≤ 1*η^θ at hh
    rw [mul_assoc, heq, one_mul] at hh
    norm_num only [show (2 : ℝ)^4=16 by norm_num]
    linarith only [hh]
  obtain ⟨D₀, hD₀power, _hD₀n, hD₀near, hD₀gap, hD₀mixed,
    z, hz, v, base, hbaseS, f, hform, hclose, _hcomm, _hAfin, _hMixedFin, _hVfin, hcube⟩ :=
    hextract hA1 hAi hα hαextBound hA hd hd1 (show 0 < ηn from hη) hsmall hp hq hpq hspan
  let S := {x : G | x ∈ A ∧ dist ((x*z*x⁻¹ : G) : RMat) v ≤ η}
  let Dset := A*D₀*A⁻¹
  have hDset : Dset ⊆ A^((n₀+2)+1) := by
    simpa only [show n₀+3=(n₀+2)+1 by omega] using hD₀mixed
  have hsourceMixed := hcover (n₀+2) hBn₀
  have hmixed : (Metric.externalCoveringNumber ηn ((fun x : G => (x : RMat)) '' Dset) : ℝ≥0∞).toReal ≤
      η^(-θ)*N :=
    (ENNReal.toReal_mono (ENat.toENNReal_ne_top.mpr hsourceMixed.2.1)
      (ENat.toENNReal_mono (Metric.externalCoveringNumber_mono_set (ε := ηn)
        (Set.image_mono hDset)))).trans hsourceMixed.2.2
  choose cs ts hcoords using hform
  have hX (i : S) : (i : G) ∈ A := i.property.1
  have hfn : (Set.range (fun i : S => (f i : RMat))).Nonempty :=
    ⟨_, ⟨⟨base, hbaseS⟩, rfl⟩⟩
  have herrorEq : 12800*(2 : ℝ)^6*η/(η^θ/32) = 26214400*η^(1-θ) := by
    rw [Real.rpow_sub hη, Real.rpow_one]
    simp only [div_eq_mul_inv, _root_.mul_inv_rev, inv_inv]
    ring
  have hsourceClose (i : S) :
      dist (f i : RMat) ((base⁻¹*(i : G) : G) : RMat) ≤ 26214400*η^(1-θ) := by
    rw [dist_comm]
    exact (hclose i).2.trans_eq herrorEq
  have hH : (102400*(2 : ℝ)^7/(η^θ/32)+17)^4 = (419430400/η^θ+17)^4 := by
    congr 1
    simp only [div_eq_mul_inv, _root_.mul_inv_rev, inv_inv]
    ring
  rw [hH] at hcube
  obtain ⟨k, _hk, hηδ, _hδlo, _hδhi, hfamily⟩ := hgrowth j hjg
  let δn : ℝ≥0 := ⟨(1/2 : ℝ)^k, by positivity⟩
  obtain ⟨m, hm, hretain, D, hDn, hDpower, hDgeom, hDgrowth⟩ :=
    hfamily f (fun i : S => (i : G)) cs ts base z Dset
      hA1 hAi hα hαgBound hA hp hq hpq hspan (hD₀near hz)
      (hD₀gap z hz).1.le (hD₀gap z hz).2.le hbaseS.1 hX hcoords hfn hsourceClose
      hdistribution hNbound h284 h142 hmixed hcube
  have hspanΘ : η^Θ ≤ |(SL2Escape.pairSpanMatrix (p : RMat) (q : RMat)).det| :=
    (Real.rpow_le_rpow_of_exponent_ge hη hηone hθΘ).trans hspan
  have hmarginUpper : ((8802*max (420+1) 141+4427 : ℕ) : ℝ)*τ ≤ Θ :=
    (hcost 421 hB421).trans hθΘ
  obtain ⟨_, hbound⟩ := hupper j hju Y 420 hlarge hNprofile hQ hQh hα hαone hαinv
    hq₀ hq₀inv hτ hmarginUpper hprofile hYcard hU hUi hY hdouble hAloc hA1 hAi hαsmall
    hp hq hpq hspanΘ (show (D : Set G).Nonempty from hDn) hDpower
    (fun w hw => (hDgeom w hw).1)
    (fun w hw => (mul_le_mul_of_nonneg_right (min_le_left a₂ 1)
      (Real.rpow_nonneg hη.le (3*Θ))).trans (hDgeom w hw).2)
  have hTbound := (hbound δn (show ηn ≤ δn from hηδ)).2
  simp only [← Finset.coe_image] at hTbound
  exact cubic_trace_budget_contradiction hη hU₀.le hm.le hretain hTbound (hcharge j hjc)
    (hDgrowth.trans_le (mul_le_mul_of_nonneg_right (by norm_num : (25 : ℝ) ≤ 250)
      ENNReal.toReal_nonneg))

end TransposeFollowup.SL2Projection
