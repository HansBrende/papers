import MergeDepth.Q91Uniform
import MergeDepth.Trimming

/-!
# Lemma 3.14(b): relations inside balls, given [Q9.1]

The setting of Lemma 3.14 (`ball_paired_packing`, `ball_trimming`): head walks `z` of an oblivious
schedule with `k` work tapes (input head `z none`, which reads position `j` at step `u` when
`rdStep u = some j`; output count `z (some none)`, equal to `tpos q` at the step `tout (tpos q) < T`
that appends position `tpos q`; work heads `z (some (some j))`), `T ≤ c (L + 1)`, `L = d² b`, and a
relation `N` with `N(q) ⊆ B^{D'}(t_{tpos q})` (`stepBall`).

* `ball_rate_binary`: **Lemma 3.14(b), binary codes**, from binary [Q9.1]. For every `δ > 0` there
  is `d₁`, depending only on `k`, `D'`, `c` and `δ`, such that for `d ≥ d₁`, every width `b ≥ 1`,
  every such schedule and relation, every binary storage code `𝒞` for `N` has
  `log₂ |𝒞| ≤ (1/2 + δ) L`.
* `ball_rate`: **Lemma 3.14(b) as stated** (every finite alphabet with `|𝒜| ≥ 2`, uniformly), from
  [Q9.1] for all alphabets.

The proof is the paper's (the fifth paper's Proposition 9.2 with Lemma 3.14(a)): with
`K = ∑_{h ≤ D'} (k + 1)^h`, `δ₀ = min(δ, 1/4)` and the trimming threshold `ϑ = ⌈4K/δ₀⌉`, the
coordinates `H` of left degree more than `ϑ` number at most `δ₀ L/4` (`ball_trimming`); the
induced relations on `Q = [0, L) ∖ H` (`BallInst`) have degree at most `max(K, ϑ)`, at least `L/2`
coordinates, and at most `A_r L/log₂ d` short pairs (`ball_paired_packing`), so the uniformity
argument (`uniform_rate_binary`, `uniform_rate`) bounds their codes by `(1/2 + δ₀/2) |Q|`, and paid
conditioning on `H` (`logb_card_le_of_conditioning`) gives `(1/2 + δ₀/2) L + |H|/2 ≤ (1/2 + δ) L`.
-/

namespace MergeDepth

open Finset Filter BoundedNesting DirectedRecovery MotionDepthCodes

set_option autoImplicit false

/-- `K = ∑_{h ≤ D} (k + 1)^h ≥ 1`. -/
theorem one_le_ballSize (k D : ℕ) : 1 ≤ ∑ h ∈ range (D + 1), (k + 1) ^ h := by
  calc 1 = (k + 1) ^ 0 := by simp
    _ ≤ ∑ h ∈ range (D + 1), (k + 1) ^ h :=
      single_le_sum (f := fun h => (k + 1) ^ h) (fun _ _ => Nat.zero_le _) (by simp)

/-- **Heavy coordinates are few.** If `H ϑ ≤ K L` and `ϑ ≥ K/δ`, then `H ≤ δ L`. -/
theorem card_heavy_le {H K L ϑ : ℕ} {δ : ℝ} (hδ : 0 < δ) (hK : 0 < K) (hϑ : (K : ℝ) / δ ≤ ϑ)
    (h : H * ϑ ≤ K * L) : (H : ℝ) ≤ δ * L := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have h1 : (H : ℝ) * ϑ ≤ K * L := by exact_mod_cast h
  have h2 : (H : ℝ) * ((K : ℝ) / δ) ≤ (H : ℝ) * ϑ := mul_le_mul_of_nonneg_left hϑ (by positivity)
  have h3 : (H : ℝ) * K ≤ δ * L * K := by
    have e : (H : ℝ) * ((K : ℝ) / δ) * δ = H * K := by field_simp
    nlinarith
  nlinarith

/-- **The instances of Lemma 3.14(b).** At `(d, b)`: `b ≥ 1`, `d ≥ 2`, a schedule as in
Lemma 3.14 with `T ≤ c (L + 1)`, a relation `N` inside the balls of radius `D'`, and the retained
set `Q = (H_ϑ)ᶜ` of coordinates whose left port has degree at most `ϑ`. -/
def BallInst (k D' : ℕ) (c : ℝ) (ϑ : ℕ) : InstFamily := fun d b Q N =>
  1 ≤ b ∧ 2 ≤ d ∧
    (∃ (z : Tp k → ℕ → ℤ) (T : ℕ) (rdStep : ℕ → Option (Fin (d * d * b))) (tout : ℕ → ℕ),
      (∀ c', IsWalk (z c')) ∧ (∀ u j, rdStep u = some j → z none u = j) ∧
      (∀ q : Fin (d * d * b),
        tout (tpos d b q) < T ∧ z (some none) (tout (tpos d b q)) = tpos d b q) ∧
      (T : ℝ) ≤ c * (d * d * b + 1) ∧
      ∀ q, N q ⊆ stepBall (fun j => z (some (some j))) T rdStep D' (tout (tpos d b q))) ∧
    Q = (heavyCoords N ϑ)ᶜ

open Classical in
/-- The degree bound `max(K, ϑ)` on the instances (Corollary 3.8 of the fifth paper for balls). -/
theorem ballInst_deg (k D' : ℕ) (c : ℝ) (ϑ : ℕ) :
    ∀ d b Q N, BallInst k D' c ϑ d b Q N →
      ∀ v, (pairedIncidenceGraph (inducedNeighborhood N Q)).degree v ≤
        max (∑ h ∈ range (D' + 1), (k + 1) ^ h) ϑ := by
  rintro d b Q N ⟨-, -, ⟨z, T, rdStep, tout, -, -, -, -, hN⟩, rfl⟩
  exact (ball_trimming (fun j => z (some (some j))) T rdStep D' (fun q => tout (tpos d b q)) N hN
    ϑ).2

open Classical in
/-- The omitted coordinates `Qᶜ = H_ϑ` number at most `δ' L` when `ϑ ≥ K/δ'`. -/
theorem ballInst_compl (k D' : ℕ) (c : ℝ) {ϑ : ℕ} {δ' : ℝ} (hδ' : 0 < δ')
    (hϑ : ((∑ h ∈ range (D' + 1), (k + 1) ^ h : ℕ) : ℝ) / δ' ≤ ϑ) :
    ∀ d b Q N, BallInst k D' c ϑ d b Q N → (Qᶜ.card : ℝ) ≤ δ' * (d * d * b : ℕ) := by
  rintro d b Q N ⟨-, -, ⟨z, T, rdStep, tout, -, -, -, -, hN⟩, rfl⟩
  rw [compl_compl]
  exact card_heavy_le hδ' (one_le_ballSize k D') hϑ (ball_trimming (fun j => z (some (some j))) T
    rdStep D' (fun q => tout (tpos d b q)) N hN ϑ).1

open Classical in
/-- The short-pair bound on the instances (Theorem 3.3 of the fifth paper for balls). -/
theorem ballInst_short (k D' : ℕ) {c : ℝ} (hc : 0 ≤ c) (ϑ : ℕ) :
    ∀ r : ℕ, 0 < r → ∃ (A : ℝ) (d₁ : ℕ), ∀ d ≥ d₁, ∀ b Q N, BallInst k D' c ϑ d b Q N →
      ((shortPairedCoordinates (inducedNeighborhood N Q) r).card : ℝ) ≤
        A * ((d * d * b : ℕ) / Real.logb 2 d) := by
  intro r _
  refine ⟨pathPackingConstant r (max (∑ h ∈ range (D' + 1), (k + 1) ^ h) ϑ)
    (fun s => 2 * s * c * (∑ h ∈ range (D' + 1), (k + 1) ^ h : ℕ) * (k + 2 : ℕ) *
      ((k + 2 : ℕ) + 1) + 3), 0, ?_⟩
  intro d _ b Q N hinst
  have hdeg := ballInst_deg k D' c ϑ d b Q N hinst
  obtain ⟨hb, hd, ⟨z, T, rdStep, tout, hz, hrd, htout, hT, hN⟩, -⟩ := hinst
  have h := ball_paired_packing hd hb hz rdStep hrd tout htout N hN hc hT Q r _ hdeg
  have e : ((d : ℝ) ^ 2 * b) = ((d * d * b : ℕ) : ℝ) := by push_cast; ring
  rw [e] at h
  exact h

open Classical in
/-- **Lemma 3.14(b), binary codes, from binary [Q9.1].** For every `δ > 0` there is `d₁`,
depending only on `k`, `D'`, `c` and `δ`, such that for `d ≥ d₁` and every width `b ≥ 1`: for
every schedule as in Lemma 3.14 with `T ≤ c (L + 1)`, `L = d² b`, and every relation `N` on
`[0, L)` with `N(q) ⊆ B^{D'}(t_{tpos q})`, every binary storage code `𝒞` for `N` has
`log₂ |𝒞| ≤ (1/2 + δ) L`. -/
theorem ball_rate_binary (hQ : Q91Binary) (k D' : ℕ) {c δ : ℝ} (hc : 0 ≤ c) (hδ : 0 < δ) :
    ∃ d₁ : ℕ, ∀ d ≥ d₁, ∀ b, 1 ≤ b → ∀ (z : Tp k → ℕ → ℤ), (∀ c', IsWalk (z c')) →
      ∀ (T : ℕ) (rdStep : ℕ → Option (Fin (d * d * b))),
      (∀ u j, rdStep u = some j → z none u = j) →
      ∀ tout : ℕ → ℕ, (∀ q : Fin (d * d * b),
        tout (tpos d b q) < T ∧ z (some none) (tout (tpos d b q)) = tpos d b q) →
      (T : ℝ) ≤ c * (d * d * b + 1) →
      ∀ N : Fin (d * d * b) → Finset (Fin (d * d * b)),
        (∀ q, N q ⊆ stepBall (fun j => z (some (some j))) T rdStep D' (tout (tpos d b q))) →
      ∀ C : Finset (Fin (d * d * b) → Bool), IsStorageCode N C →
        Real.logb 2 C.card ≤ (1 / 2 + δ) * (d * d * b : ℕ) := by
  set δ₀ := min δ (1 / 4)
  have hδ₀ : 0 < δ₀ := lt_min hδ (by norm_num)
  have hδ₀δ : δ₀ ≤ δ := min_le_left _ _
  have hδ₀q : δ₀ ≤ 1 / 4 := min_le_right _ _
  set K := ∑ h ∈ range (D' + 1), (k + 1) ^ h
  set ϑ := ⌈(K : ℝ) / (δ₀ / 4)⌉₊
  have hϑ : (K : ℝ) / (δ₀ / 4) ≤ ϑ := Nat.le_ceil _
  have hcompl := ballInst_compl k D' c (by positivity : 0 < δ₀ / 4) hϑ
  obtain ⟨d₀, hd₀⟩ := uniform_rate_binary hQ (BallInst k D' c ϑ) (max K ϑ) (κ := 1 / 2)
    (by norm_num) (fun _ _ _ _ h => h.1) (ballInst_deg k D' c ϑ)
    ⟨0, fun d _ b Q N h => by
      have h1 := hcompl d b Q N h
      have h2 : (Q.card : ℝ) + Qᶜ.card = (d * d * b : ℕ) := by
        rw [← Nat.cast_add, Finset.card_add_card_compl, Fintype.card_fin]
      have h3 : (0 : ℝ) ≤ (d * d * b : ℕ) := Nat.cast_nonneg _
      nlinarith⟩
    (ballInst_short k D' hc ϑ) (half_pos hδ₀)
  refine ⟨max d₀ 2, fun d hd b hb z hz T rdStep hrd tout htout hT N hN C hC => ?_⟩
  have hinst : BallInst k D' c ϑ d b (heavyCoords N ϑ)ᶜ N :=
    ⟨hb, le_of_max_le_right hd, ⟨z, T, rdStep, tout, hz, hrd, htout, hT, hN⟩, rfl⟩
  have hcond := logb_card_le_of_conditioning (by simp) hC (heavyCoords N ϑ)ᶜ
    (hd₀ d (le_of_max_le_left hd) b _ N hinst)
  have h1 := hcompl d b _ N hinst
  have h2 : (((heavyCoords N ϑ)ᶜ).card : ℝ) + ((heavyCoords N ϑ)ᶜᶜ).card = (d * d * b : ℕ) := by
    rw [← Nat.cast_add, Finset.card_add_card_compl, Fintype.card_fin]
  have h3 := conditioning_arith (L := ((d * d * b : ℕ) : ℝ)) (half_pos hδ₀).le
    (Nat.cast_nonneg ((heavyCoords N ϑ)ᶜᶜ.card)) h2
  rw [Fintype.card_bool, Nat.cast_ofNat] at hcond
  have h4 : (0 : ℝ) ≤ (d * d * b : ℕ) := Nat.cast_nonneg _
  nlinarith

open Classical in
/-- **Lemma 3.14(b) as stated in the paper, from [Q9.1] for all alphabets.** The threshold `d₁`
depends only on `k`, `D'`, `c` and `δ`; it works for every finite alphabet `𝒜` with `|𝒜| ≥ 2`. -/
theorem ball_rate (hQ : Q91) (k D' : ℕ) {c δ : ℝ} (hc : 0 ≤ c) (hδ : 0 < δ) :
    ∃ d₁ : ℕ, ∀ d ≥ d₁, ∀ b, 1 ≤ b → ∀ (z : Tp k → ℕ → ℤ), (∀ c', IsWalk (z c')) →
      ∀ (T : ℕ) (rdStep : ℕ → Option (Fin (d * d * b))),
      (∀ u j, rdStep u = some j → z none u = j) →
      ∀ tout : ℕ → ℕ, (∀ q : Fin (d * d * b),
        tout (tpos d b q) < T ∧ z (some none) (tout (tpos d b q)) = tpos d b q) →
      (T : ℝ) ≤ c * (d * d * b + 1) →
      ∀ N : Fin (d * d * b) → Finset (Fin (d * d * b)),
        (∀ q, N q ⊆ stepBall (fun j => z (some (some j))) T rdStep D' (tout (tpos d b q))) →
      ∀ (A : Type) [Fintype A], 2 ≤ Fintype.card A → ∀ C : Finset (Fin (d * d * b) → A),
        IsStorageCode N C → Real.logb (Fintype.card A) C.card ≤ (1 / 2 + δ) * (d * d * b : ℕ) := by
  set δ₀ := min δ (1 / 4)
  have hδ₀ : 0 < δ₀ := lt_min hδ (by norm_num)
  have hδ₀δ : δ₀ ≤ δ := min_le_left _ _
  have hδ₀q : δ₀ ≤ 1 / 4 := min_le_right _ _
  set K := ∑ h ∈ range (D' + 1), (k + 1) ^ h
  set ϑ := ⌈(K : ℝ) / (δ₀ / 4)⌉₊
  have hϑ : (K : ℝ) / (δ₀ / 4) ≤ ϑ := Nat.le_ceil _
  have hcompl := ballInst_compl k D' c (by positivity : 0 < δ₀ / 4) hϑ
  obtain ⟨d₀, hd₀⟩ := uniform_rate hQ (BallInst k D' c ϑ) (max K ϑ) (κ := 1 / 2)
    (by norm_num) (fun _ _ _ _ h => h.1) (ballInst_deg k D' c ϑ)
    ⟨0, fun d _ b Q N h => by
      have h1 := hcompl d b Q N h
      have h2 : (Q.card : ℝ) + Qᶜ.card = (d * d * b : ℕ) := by
        rw [← Nat.cast_add, Finset.card_add_card_compl, Fintype.card_fin]
      have h3 : (0 : ℝ) ≤ (d * d * b : ℕ) := Nat.cast_nonneg _
      nlinarith⟩
    (ballInst_short k D' hc ϑ) (half_pos hδ₀)
  refine ⟨max d₀ 2, fun d hd b hb z hz T rdStep hrd tout htout hT N hN A _ hA C hC => ?_⟩
  have hinst : BallInst k D' c ϑ d b (heavyCoords N ϑ)ᶜ N :=
    ⟨hb, le_of_max_le_right hd, ⟨z, T, rdStep, tout, hz, hrd, htout, hT, hN⟩, rfl⟩
  have hcond := logb_card_le_of_conditioning hA hC (heavyCoords N ϑ)ᶜ
    (hd₀ d (le_of_max_le_left hd) b _ N hinst A hA)
  have h1 := hcompl d b _ N hinst
  have h2 : (((heavyCoords N ϑ)ᶜ).card : ℝ) + ((heavyCoords N ϑ)ᶜᶜ).card = (d * d * b : ℕ) := by
    rw [← Nat.cast_add, Finset.card_add_card_compl, Fintype.card_fin]
  have h3 := conditioning_arith (L := ((d * d * b : ℕ) : ℝ)) (half_pos hδ₀).le
    (Nat.cast_nonneg ((heavyCoords N ϑ)ᶜᶜ.card)) h2
  have h4 : (0 : ℝ) ≤ (d * d * b : ℕ) := Nat.cast_nonneg _
  nlinarith

end MergeDepth
