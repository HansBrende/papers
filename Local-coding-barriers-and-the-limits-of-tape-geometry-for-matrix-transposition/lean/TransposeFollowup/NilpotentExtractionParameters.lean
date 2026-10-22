import TransposeFollowup.BoundedCoordinatePacking
import TransposeFollowup.CubicSampleNormalization

/-! Exact first-extraction coefficients and their powers of the native
scale. Fixed constants remain explicit, and the chart and sampling
parameters are shared by the scalar concentration and size bounds. -/
namespace TransposeFollowup.SL2Projection
open BoundedCoordinatePacking
set_option autoImplicit false

theorem first_extraction_cost_bounds
    {η θ a b s l e B B₀ R : ℝ}
    (hη : 0 < η) (hηone : η ≤ 1) (hθ : 0 ≤ θ)
    (ha : 0 < a) (hb : 0 < b) (hs : 0 < s) (he : 0 ≤ e)
    (hB : 0 ≤ B) (hB₀ : 0 ≤ B₀) (hR : 0 ≤ R) :
    let r₀ := a * η ^ (2 * θ)
    let δ := b * η ^ (11 * θ)
    let σ := s * η ^ (1 - 9 * θ)
    let ε := e * η ^ (1 - 2 * θ)
    let L := l * η ^ (3 * θ)
    let Hc := (102400 * B₀ ^ 7 / a + 8 * B₀ + 1) ^ 4
    let Sc := 6561 * (4 * s + 1) ^ 4
    let Lc := (2 * B / b + 1) ^ 4
    let Ec := (80 * (2 * R) ^ 10 * e + 8 * R + 1) ^ 4
    let Dc := 40 * (2 * R) ^ 11 * (48 / l + 2)
    (102400 * B₀ ^ 7 / r₀ + 8 * B₀ + 1) ^ 4 ≤ Hc * η ^ (-(8 * θ)) ∧
      6561 * (4 * σ / η + 1) ^ 4 ≤ Sc * η ^ (-(36 * θ)) ∧
      ((binCount B δ ^ 4 : ℕ) : ℝ) ≤ Lc * η ^ (-(44 * θ)) ∧
      (4 * (20 * (2 * R) ^ 10 * ε + 2 * R * η) / η + 1) ^ 4 ≤
        Ec * η ^ (-(8 * θ)) ∧
      40 * (2 * R) ^ 11 * (3 * 32 / (2 * L) + 2) ≤ Dc * η ^ (-(3 * θ)) := by
  intro r₀ δ σ ε L Hc Sc Lc Ec Dc
  have hone (p : ℝ) (hp : 0 ≤ p) : 1 ≤ η ^ (-p) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hη hηone (neg_nonpos.mpr hp)
  have hdiv (C A p : ℝ) : C / (A * η ^ p) = (C / A) * η ^ (-p) := by
    rw [Real.rpow_neg hη.le]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hratio (p : ℝ) : η ^ (1 - p) / η = η ^ (-p) := by
    have hh := Real.rpow_sub hη (1 - p) 1
    rw [Real.rpow_one] at hh
    convert hh.symm using 1
    congr 1
    ring
  have hsum (C D p : ℝ) (hD : 0 ≤ D) (hp : 0 ≤ p) :
      C * η ^ (-p) + D ≤ (C + D) * η ^ (-p) := by
    have hh := mul_le_mul_of_nonneg_left (hone p hp) hD
    nlinarith only [hh]
  have hfour (p : ℝ) : (η ^ (-p)) ^ 4 = η ^ (-(4 * p)) := by
    rw [← Real.rpow_mul_natCast hη.le]
    congr 1
    norm_num
    ring
  have hHbase : 102400 * B₀ ^ 7 / r₀ + 8 * B₀ + 1 ≤
      (102400 * B₀ ^ 7 / a + 8 * B₀ + 1) * η ^ (-(2 * θ)) := by
    dsimp only [r₀]
    rw [hdiv, add_assoc]
    simpa only [add_assoc] using hsum (102400 * B₀ ^ 7 / a) (8 * B₀ + 1) (2 * θ)
      (by positivity) (by positivity)
  have hσ : σ / η = s * η ^ (-(9 * θ)) := by
    dsimp only [σ]
    rw [mul_div_assoc, hratio]
  have hε : ε / η = e * η ^ (-(2 * θ)) := by
    dsimp only [ε]
    rw [mul_div_assoc, hratio]
  have hSbase : 4 * σ / η + 1 ≤ (4 * s + 1) * η ^ (-(9 * θ)) := by
    rw [mul_div_assoc, hσ, ← mul_assoc]
    exact hsum _ _ _ zero_le_one (by positivity)
  have hLbase : (binCount B δ : ℝ) ≤ (2 * B / b + 1) * η ^ (-(11 * θ)) := by
    calc
      _ ≤ 2 * B / δ + 1 := binCount_le hB (by dsimp only [δ]; positivity)
      _ = (2 * B / b) * η ^ (-(11 * θ)) + 1 := by dsimp only [δ]; rw [hdiv]
      _ ≤ _ := hsum _ _ _ zero_le_one (by positivity)
  have hEbase : 4 * (20 * (2 * R) ^ 10 * ε + 2 * R * η) / η + 1 ≤
      (80 * (2 * R) ^ 10 * e + 8 * R + 1) * η ^ (-(2 * θ)) := by
    have heq : 4 * (20 * (2 * R) ^ 10 * ε + 2 * R * η) / η + 1 =
        80 * (2 * R) ^ 10 * (ε / η) + (8 * R + 1) := by
      field_simp
      ring
    rw [heq, hε, ← mul_assoc]
    simpa only [add_assoc] using hsum (80 * (2 * R) ^ 10 * e) (8 * R + 1) (2 * θ)
      (by positivity) (by positivity)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hh := pow_le_pow_left₀ (by dsimp only [r₀]; positivity) hHbase 4
    rw [mul_pow, hfour] at hh
    simpa only [Hc, show 4 * (2 * θ) = 8 * θ by ring] using hh
  · have hh := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by dsimp only [σ]; positivity) hSbase 4)
      (by norm_num : (0 : ℝ) ≤ 6561)
    rw [mul_pow, hfour] at hh
    simpa only [Sc, show 4 * (9 * θ) = 36 * θ by ring, mul_assoc] using hh
  · have hh := pow_le_pow_left₀ (Nat.cast_nonneg _) hLbase 4
    rw [mul_pow, hfour] at hh
    simpa only [Lc, Nat.cast_pow, show 4 * (11 * θ) = 44 * θ by ring] using hh
  · have hh := pow_le_pow_left₀ (by dsimp only [ε]; positivity) hEbase 4
    rw [mul_pow (80 * (2 * R) ^ 10 * e + 8 * R + 1) (η ^ (-(2 * θ))) 4, hfour] at hh
    simpa only [Ec, show 4 * (2 * θ) = 8 * θ by ring] using hh
  · have hbase : 3 * 32 / (2 * L) + 2 ≤ (48 / l + 2) * η ^ (-(3 * θ)) := by
      have heq : 3 * 32 / (2 * L) = 48 / L := by ring
      rw [heq]
      dsimp only [L]
      rw [hdiv]
      exact hsum _ _ _ (by norm_num) (by positivity)
    simpa only [Dc, mul_assoc] using mul_le_mul_of_nonneg_left hbase
      (by positivity : 0 ≤ 40 * (2 * R) ^ 11)

theorem scalar_concentration_power_bounds
    {η θ κ γ H S L E D P K J Cp Hc Sc Lc Ec Dc : ℝ}
    (hη : 0 < η) (hηone : η ≤ 1) (hθ : 0 ≤ θ)
    (hκ : 0 ≤ κ) (hκone : κ ≤ 1) (hγ : 0 ≤ γ) (hγθ : γ ≤ θ)
    (hH : 0 ≤ H) (hS : 0 ≤ S) (hL : 0 ≤ L) (hD : 0 ≤ D)
    (hP : 0 ≤ P) (hK : 0 ≤ K) (hJ : 0 ≤ J) (hCp : 0 ≤ Cp)
    (hHc : 0 ≤ Hc) (hEc : 0 ≤ Ec) (hDc : 0 ≤ Dc)
    (hHb : H ≤ Hc * η ^ (-(8 * θ)))
    (hSb : S ≤ Sc * η ^ (-(36 * θ)))
    (hLb : L ≤ Lc * η ^ (-(44 * θ)))
    (hEb : E ≤ Ec * η ^ (-(8 * θ)))
    (hDb : D ≤ Dc * η ^ (-(3 * θ)))
    (hPb : P ≤ η ^ (-θ)) (hKb : K ≤ η ^ (-θ)) (hJb : J ≤ η ^ (-θ)) :
    let Q := 4 * L ^ 3 * (E * (Cp * K * J * η ^ (-(γ * κ))) * D ^ κ + (2 : ℝ) ^ κ)
    let W := (9 * P * H) ^ 3 * η ^ (-(8 * θ)) * S ^ 3
    let Qc := 4 * Lc ^ 3 * (Ec * Cp * Dc ^ κ + (2 : ℝ) ^ κ)
    let Wc := (9 * Hc) ^ 3 * Sc ^ 3
    Q ≤ Qc * η ^ (-(146 * θ)) ∧ W ≤ Wc * η ^ (-(143 * θ)) := by
  intro Q W Qc Wc
  let T := η ^ (-θ)
  have hT : 1 ≤ T :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hη hηone (neg_nonpos.mpr hθ)
  have hT0 : 0 ≤ T := zero_le_one.trans hT
  have hp (n : ℕ) : T ^ n = η ^ (-((n : ℝ) * θ)) := by
    dsimp only [T]
    rw [← Real.rpow_mul_natCast hη.le]
    congr 1
    ring
  have hH' : H ≤ Hc * T ^ 8 := by simpa only [hp, Nat.cast_ofNat] using hHb
  have hS' : S ≤ Sc * T ^ 36 := by simpa only [hp, Nat.cast_ofNat] using hSb
  have hL' : L ≤ Lc * T ^ 44 := by simpa only [hp, Nat.cast_ofNat] using hLb
  have hE' : E ≤ Ec * T ^ 8 := by simpa only [hp, Nat.cast_ofNat] using hEb
  have hD' : D ≤ Dc * T ^ 3 := by simpa only [hp, Nat.cast_ofNat] using hDb
  have hηγκ : η ^ (-(γ * κ)) ≤ T :=
    Real.rpow_le_rpow_of_exponent_ge hη hηone
      (by nlinarith only [hγ, hκone, hγθ])
  have hDκ : D ^ κ ≤ Dc ^ κ * T ^ 3 := by
    calc
      _ ≤ (Dc * T ^ 3) ^ κ := Real.rpow_le_rpow hD hD' hκ
      _ = Dc ^ κ * (T ^ 3) ^ κ := Real.mul_rpow hDc (by positivity)
      _ ≤ Dc ^ κ * (T ^ 3) ^ (1 : ℝ) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ hT) hκone)
          (Real.rpow_nonneg hDc κ)
      _ = _ := by rw [Real.rpow_one]
  have hinner : E * (Cp * K * J * η ^ (-(γ * κ))) * D ^ κ ≤
      Ec * Cp * Dc ^ κ * T ^ 14 := by
    calc
      _ ≤ (Ec * T ^ 8) * (Cp * T * T * T) * (Dc ^ κ * T ^ 3) := by
        gcongr
      _ = _ := by ring
  have hone : (2 : ℝ) ^ κ ≤ (2 : ℝ) ^ κ * T ^ 14 :=
    le_mul_of_one_le_right (by positivity) (one_le_pow₀ hT)
  have hsum : E * (Cp * K * J * η ^ (-(γ * κ))) * D ^ κ + (2 : ℝ) ^ κ ≤
      (Ec * Cp * Dc ^ κ + (2 : ℝ) ^ κ) * T ^ 14 := by
    nlinarith only [hinner, hone]
  constructor
  · have hQ : Q ≤ Qc * T ^ 146 := by
      calc
        _ ≤ 4 * L ^ 3 * ((Ec * Cp * Dc ^ κ + (2 : ℝ) ^ κ) * T ^ 14) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
        _ ≤ 4 * (Lc * T ^ 44) ^ 3 *
            ((Ec * Cp * Dc ^ κ + (2 : ℝ) ^ κ) * T ^ 14) := by gcongr
        _ = _ := by dsimp only [Qc]; ring
    simpa only [hp, Nat.cast_ofNat] using hQ
  · have hW : W ≤ Wc * T ^ 143 := by
      change (9 * P * H) ^ 3 * η ^ (-(8 * θ)) * S ^ 3 ≤ _
      rw [← show T ^ 8 = η ^ (-(8 * θ)) by simpa only [Nat.cast_ofNat] using hp 8]
      calc
        _ ≤ (9 * T * (Hc * T ^ 8)) ^ 3 * T ^ 8 * (Sc * T ^ 36) ^ 3 := by
          gcongr
        _ = _ := by dsimp only [Wc]; ring
    simpa only [hp, Nat.cast_ofNat] using hW

/-- Shared conversion of the concentration and normalization power bounds
into the cubic budget. Both scalar-coordinate applications use it. -/
theorem concentration_budget_of_power_bounds {η θ Q W Qc Wc : ℝ}
    (hη : 0 < η) (hηone : η ≤ 1) (hθ : 0 ≤ θ)
    (hW : 0 ≤ W) (hQc : 0 ≤ Qc) (hWc : 0 ≤ Wc)
    (hQb : Q ≤ Qc*η^(-(146*θ))) (hWb : W ≤ Wc*η^(-(143*θ))) :
    Q*W ≤ ((1+Qc*Wc)*η^(-(100*θ)))^3 := by
  let C₀ := 1+Qc*Wc
  have hC₀ : 1 ≤ C₀ := le_add_of_nonneg_right (mul_nonneg hQc hWc)
  have hconst : Qc * Wc ≤ C₀ ^ 3 := by
    have hleft : Qc * Wc ≤ C₀ := le_add_of_nonneg_left zero_le_one
    have hh := pow_le_pow_right₀ hC₀ (by norm_num : (1 : ℕ) ≤ 3)
    exact hleft.trans (by simpa only [pow_one] using hh)
  have hp : η ^ (-(146 * θ)) * η ^ (-(143 * θ)) = η ^ (-(289 * θ)) := by
    rw [← Real.rpow_add hη]
    congr 1
    ring
  have hbig : η ^ (-(289 * θ)) ≤ η ^ (-(300 * θ)) :=
    Real.rpow_le_rpow_of_exponent_ge hη hηone (by linarith only [hθ])
  have hcube : (η ^ (-(100 * θ))) ^ 3 = η ^ (-(300 * θ)) := by
    rw [← Real.rpow_mul_natCast hη.le]
    congr 1
    norm_num
    ring
  calc
    Q * W ≤ (Qc * η ^ (-(146 * θ))) * (Wc * η ^ (-(143 * θ))) :=
      mul_le_mul hQb hWb hW (by positivity)
    _ = (Qc * Wc) * (η ^ (-(146 * θ)) * η ^ (-(143 * θ))) :=
      mul_mul_mul_comm Qc _ Wc _
    _ = (Qc * Wc) * η ^ (-(289 * θ)) := by rw [hp]
    _ ≤ C₀ ^ 3 * η ^ (-(300 * θ)) :=
      mul_le_mul hconst hbig (by positivity) (by positivity)
    _ = _ := by rw [mul_pow C₀ (η ^ (-(100 * θ))) 3, hcube]

/-- Fixed constants chosen before the scale jointly pay chart localization,
frame absorption, matrix spacing and scalar spacing. -/
theorem exists_scaled_extraction_parameters {H B M a : ℝ}
    (hH : 1 ≤ H) (hB : 1 ≤ B) (hM : 1 ≤ M) (ha : 0 < a) (haone : a ≤ 1) :
    ∃ b s l e f rc : ℝ,
      0 < b ∧ 0 < s ∧ 0 < l ∧ 0 < e ∧ 0 < f ∧ 0 < rc ∧
      l = a / (9216 * H ^ 4) ∧
      e = 12800 * (4 * H) ^ 6 / a ∧
      ∀ η θ : ℝ, 0 < η → η ≤ 1 → 0 ≤ θ →
        let r₀ := a * η ^ (2 * θ)
        let d₀ := η ^ θ
        let d := f * η ^ (9 * θ)
        let r := rc * η ^ (9 * θ)
        let δ := b * η ^ (11 * θ)
        let σ := s * η ^ (1 - 9 * θ)
        let L := l * η ^ (3 * θ)
        let ε := e * η ^ (1 - 2 * θ)
        r ≤ 1 ∧ 3 * M * r ≤ 1 ∧ 36864 * M ^ 6 * r ≤ d ∧
        8 * B * δ ≤ 1 ∧ 8 * B * δ = (r₀ / 8) * r ∧
        d = (r₀ / 8) ^ 3 / (3456 * (96 * H ^ 4 / d₀) ^ 3) ∧
        10 * B * M * (384 * M ^ 4 / d * η) ≤ 2 * σ ∧ η ≤ σ ∧
        L = (r₀ / 8) * d₀ / (1152 * H ^ 4) ∧
        ε = 12800 * (4 * H) ^ 6 * η / r₀ ∧
        ∀ δs : ℝ, δs ≤ 2 * η ^ (1 - 3 * θ) → 96 * δs ≤ 4 * L * σ := by
  have hHp : 0 < H := zero_lt_one.trans_le hH
  have hBp : 0 < B := zero_lt_one.trans_le hB
  have hMp : 0 < M := zero_lt_one.trans_le hM
  let f := (a / 8) ^ 3 / (3456 * (96 * H ^ 4) ^ 3)
  have hf : 0 < f := by dsimp only [f]; positivity
  let rc := min 1 (min (1 / (3 * M)) (f / (36864 * M ^ 6)))
  have hrc : 0 < rc := by dsimp only [rc]; positivity
  have hrcone : rc ≤ 1 := min_le_left _ _
  have hrcM : rc ≤ 1 / (3 * M) := (min_le_right _ _).trans (min_le_left _ _)
  have hrcf : rc ≤ f / (36864 * M ^ 6) := (min_le_right _ _).trans (min_le_right _ _)
  have hrcsmall : 3 * M * rc ≤ 1 := by
    simpa only [mul_comm] using (le_div_iff₀ (by positivity : 0 < 3 * M)).mp hrcM
  have hrcabsorb : 36864 * M ^ 6 * rc ≤ f := by
    simpa only [mul_comm] using (le_div_iff₀ (by positivity : 0 < 36864 * M ^ 6)).mp hrcf
  let b := a * rc / (64 * B)
  have hb : 0 < b := by dsimp only [b]; positivity
  have hbrel : 8 * B * b = (a / 8) * rc := by
    dsimp only [b]
    field_simp
    ring
  let l := a / (9216 * H ^ 4)
  have hl : 0 < l := by dsimp only [l]; positivity
  let e := 12800 * (4 * H) ^ 6 / a
  have he : 0 < e := by dsimp only [e]; positivity
  let s := max 1 (max (1920 * B * M ^ 5 / f) (48 / l))
  have hsone : 1 ≤ s := le_max_left _ _
  have hs : 0 < s := zero_lt_one.trans_le hsone
  have hsM : 1920 * B * M ^ 5 / f ≤ s :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hsl : 48 / l ≤ s := (le_max_right _ _).trans (le_max_right _ _)
  have hls : 48 ≤ l * s := by simpa only [mul_comm] using (div_le_iff₀ hl).mp hsl
  refine ⟨b, s, l, e, f, rc, hb, hs, hl, he, hf, hrc, rfl, rfl, ?_⟩
  intro η θ hη hηone hθ r₀ d₀ d r δ σ L ε
  have hp (p : ℝ) : 0 < η ^ p := Real.rpow_pos_of_pos hη p
  have h9 : η ^ (9 * θ) ≤ 1 :=
    Real.rpow_le_one hη.le hηone (by positivity)
  have h2 : η ^ (2 * θ) ≤ 1 :=
    Real.rpow_le_one hη.le hηone (by positivity)
  have hr0 : 0 ≤ r := mul_nonneg hrc.le (hp _).le
  have hrone : r ≤ 1 := (mul_le_mul hrcone h9 (hp _).le zero_le_one).trans_eq (one_mul 1)
  have hr₀one : r₀ ≤ 1 := (mul_le_mul haone h2 (hp _).le zero_le_one).trans_eq (one_mul 1)
  have hprod (p q : ℝ) : η ^ p * η ^ q = η ^ (p + q) := (Real.rpow_add hη p q).symm
  have hradius : 8 * B * δ = (r₀ / 8) * r := by
    change 8 * B * (b * η ^ (11 * θ)) = (a * η ^ (2 * θ) / 8) * (rc * η ^ (9 * θ))
    calc
      _ = (8 * B * b) * η ^ (11 * θ) := by ring
      _ = (a / 8 * rc) * η ^ (11 * θ) := by rw [hbrel]
      _ = (a / 8 * rc) * (η ^ (2 * θ) * η ^ (9 * θ)) := by
        rw [hprod, show 2 * θ + 9 * θ = 11 * θ by ring]
      _ = _ := by ring
  have hframe : d = (r₀ / 8) ^ 3 / (3456 * (96 * H ^ 4 / d₀) ^ 3) := by
    have hc : (η ^ (2 * θ)) ^ 3 * (η ^ θ) ^ 3 = η ^ (9 * θ) := by
      rw [← Real.rpow_mul_natCast hη.le, ← Real.rpow_mul_natCast hη.le, hprod]
      congr 1
      norm_num
      ring
    calc
      d = f * ((η ^ (2 * θ)) ^ 3 * (η ^ θ) ^ 3) := by rw [hc]
      _ = _ := by
        dsimp only [f, r₀, d₀]
        field_simp
  have hspace : 10 * B * M * (384 * M ^ 4 / d * η) ≤ 2 * σ := by
    have heq : 10 * B * M * (384 * M ^ 4 / d * η) =
        2 * (1920 * B * M ^ 5 / f) * η ^ (1 - 9 * θ) := by
      rw [Real.rpow_sub hη, Real.rpow_one]
      dsimp only [d]
      field_simp
      ring
    rw [heq]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsM (by norm_num))
      (hp _).le |>.trans_eq (by dsimp only [σ]; ring)
  have hL : L = (r₀ / 8) * d₀ / (1152 * H ^ 4) := by
    have heq : 3 * θ = 2 * θ + θ := by ring
    dsimp only [L, l, r₀, d₀]
    rw [heq, Real.rpow_add hη]
    ring
  have hε : ε = 12800 * (4 * H) ^ 6 * η / r₀ := by
    dsimp only [ε, e, r₀]
    rw [Real.rpow_sub hη, Real.rpow_one]
    ring
  refine ⟨hrone, ?_, ?_, ?_, hradius, hframe, hspace, ?_, hL, hε, ?_⟩
  · calc
      3 * M * r = (3 * M * rc) * η ^ (9 * θ) := by dsimp only [r]; ring
      _ ≤ 1 * 1 := mul_le_mul hrcsmall h9 (hp _).le zero_le_one
      _ = 1 := one_mul 1
  · calc
      36864 * M ^ 6 * r = (36864 * M ^ 6 * rc) * η ^ (9 * θ) := by dsimp only [r]; ring
      _ ≤ f * η ^ (9 * θ) := mul_le_mul_of_nonneg_right hrcabsorb (hp _).le
      _ = d := rfl
  · rw [hradius]
    have hr₀eight : r₀ / 8 ≤ 1 := by linarith only [hr₀one]
    exact (mul_le_mul hr₀eight hrone hr0 zero_le_one).trans_eq (one_mul 1)
  · calc
      η = η ^ (1 : ℝ) := (Real.rpow_one η).symm
      _ ≤ η ^ (1 - 9 * θ) := Real.rpow_le_rpow_of_exponent_ge hη hηone (by linarith only [hθ])
      _ ≤ s * η ^ (1 - 9 * θ) := le_mul_of_one_le_left (hp _).le hsone
      _ = σ := rfl
  · intro δs hδs
    have hscale : η ^ (1 - 3 * θ) ≤ η ^ (1 - 6 * θ) :=
      Real.rpow_le_rpow_of_exponent_ge hη hηone (by linarith only [hθ])
    have heq : 4 * L * σ = (4 * l * s) * η ^ (1 - 6 * θ) := by
      change 4 * (l * η ^ (3 * θ)) * (s * η ^ (1 - 9 * θ)) = _
      calc
        _ = (4 * l * s) * (η ^ (3 * θ) * η ^ (1 - 9 * θ)) := by ring
        _ = _ := by rw [hprod, show 3 * θ + (1 - 9 * θ) = 1 - 6 * θ by ring]
    rw [heq]
    calc
      96 * δs ≤ 192 * η ^ (1 - 3 * θ) := by linarith only [hδs]
      _ ≤ 192 * η ^ (1 - 6 * θ) := mul_le_mul_of_nonneg_left hscale (by norm_num)
      _ ≤ (4 * l * s) * η ^ (1 - 6 * θ) :=
        mul_le_mul_of_nonneg_right (by linarith only [hls]) (hp _).le


/-- The actual sampling, binning and error formulas meet the upper-size
budget; only the existing geometric cube and product envelope are inputs. -/
theorem exists_first_extraction_size_constant {b s e B R : ℝ}
    (hb : 0 < b) (hs : 0 < s) (he : 0 ≤ e) (hB : 0 ≤ B) (hR : 0 ≤ R) :
    ∃ V₀ : ℝ, 0 < V₀ ∧ ∀ η θ κ N T V m : ℝ,
      0 < η → η ≤ 1 → 0 ≤ θ → κ ≤ 3 → 0 ≤ m → 0 ≤ T →
      let δ := b * η ^ (11 * θ)
      let σ := s * η ^ (1 - 9 * θ)
      let ε := e * η ^ (1 - 2 * θ)
      let S := 6561 * (4 * σ / η + 1) ^ 4
      let L := ((binCount B δ ^ 4 : ℕ) : ℝ)
      let E := (4 * (20 * (2 * R) ^ 10 * ε + 2 * R * η) / η + 1) ^ 4
      m ≤ V → V ^ 3 ≤ 4 * (S * L) ^ 3 * (E * T + 1) →
      N ≤ η ^ (-(3 - κ)) → T ≤ η ^ (-θ) * N →
      m ≤ V₀ * η ^ (-(1 - κ / 3 + 83 * θ)) := by
  let Sc := 6561 * (4 * s + 1) ^ 4
  let Lc := (2 * B / b + 1) ^ 4
  let Ec := (80 * (2 * R) ^ 10 * e + 8 * R + 1) ^ 4
  have hSc : 0 ≤ Sc := by dsimp only [Sc]; positivity
  have hLc : 0 ≤ Lc := by dsimp only [Lc]; positivity
  have hEc : 0 ≤ Ec := by dsimp only [Ec]; positivity
  let U := 4 * (Sc * Lc) ^ 3 * (Ec + 1)
  have hU : 0 ≤ U := by dsimp only [U]; positivity
  let V₀ := 1 + U
  have hV₀ : 1 ≤ V₀ := le_add_of_nonneg_right hU
  have hbudget : 4 * (Sc * Lc) ^ 3 * (Ec * 1 + 1) ≤ V₀ ^ 3 := by
    have hsmall : U ≤ V₀ := le_add_of_nonneg_left zero_le_one
    have hpow : V₀ ≤ V₀ ^ 3 := by
      simpa only [pow_one] using pow_le_pow_right₀ hV₀ (by norm_num : (1 : ℕ) ≤ 3)
    simpa only [mul_one] using hsmall.trans hpow
  refine ⟨V₀, zero_lt_one.trans_le hV₀, ?_⟩
  intro η θ κ N T V m hη hηone hθ hκ hm hT δ σ ε S L E hcard hcube hNbound hTbound
  obtain ⟨_, hSb, hLb, hEb, _⟩ := first_extraction_cost_bounds
    (a := 1) (l := 1) (B₀ := 0) hη hηone hθ zero_lt_one hb hs he hB le_rfl hR
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hL : 0 ≤ L := Nat.cast_nonneg _
  have hT' : T ≤ 1 * η ^ (-θ) * N := by simpa only [one_mul] using hTbound
  have hh := sample_cardinality_upper_of_cubic hη hηone hκ
    (show 0 ≤ 8 * θ by positivity) hθ hm hT hS hL hSc hLc hEc zero_le_one
    (zero_le_one.trans hV₀) hcard hcube hNbound hT' hSb hLb hEb hbudget
  simpa only [show 36 * θ + 44 * θ + (3 - κ + 8 * θ + θ) / 3 =
    1 - κ / 3 + 83 * θ by ring] using hh

end TransposeFollowup.SL2Projection
