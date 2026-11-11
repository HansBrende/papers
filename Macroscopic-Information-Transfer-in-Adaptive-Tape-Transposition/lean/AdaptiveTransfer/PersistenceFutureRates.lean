import AdaptiveTransfer.PersistenceFutureSelection
import AdaptiveTransfer.PersistenceRates

/-! Explicit exponential rates for actual future-word escape. The source
future-readable catalogue theorem remains the sole native premise: all
finite selection, masking, successful-return and rate estimates are derived.
-/

namespace AdaptiveTransfer.PersistenceFutureRates

universe u

open Transpose Transpose.Tape LeanMachine Finset BoundedNesting
open PersistenceRates FiniteTimeGrid FiniteObservationTopSets
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem future_mask_numeric_rate {h₀ C : ℝ} {A k m : ℕ}
    (hh : 0 < h₀) (hA : 1 ≤ A) (hC : 0 ≤ C) (hm : m ≤ k) :
    ∃ P₀ : ℕ, ∀ P, P₀ ≤ P → ∀ T : ℕ, (T : ℝ) ≤ C * (P + 1) →
      2 ≤ radius (beta h₀ A) P ∧ 0 < intervalLength (beta h₀ A) P ∧
      beta h₀ A * P / 4 ≤ intervalLength (beta h₀ A) P ∧
      ∀ p : ℝ, 1 / 2 ≤ p →
        selectionMass k m C (beta h₀ A) ≤
          p / (k.choose m * (T / intervalLength (beta h₀ A) P + 1) : ℕ) ∧
        ∀ a : ℕ, a ≤ A →
          (((2 * T + 1) * a ^ (2 * remoteRadius (alpha h₀) A P + 1) : ℕ) : ℝ) *
              (k.choose m * (T / intervalLength (beta h₀ A) P + 1) : ℕ) /
            ((topSize (alpha h₀) P + 1) * p) ≤ (2 : ℝ) ^ (-alpha h₀ * P / 2) := by
  let M := choiceMenu k m C (beta h₀ A)
  have hM : 1 ≤ M := choiceMenu_pos hm C (beta h₀ A)
  obtain ⟨P₁, hgrid⟩ := grid_rates (beta_pos hh hA) hC k m
  obtain ⟨P₂, hatom⟩ := remote_mask_atom_rate (C := C) (alpha_pos hh) hA hM
  refine ⟨max P₁ P₂, ?_⟩
  intro P hP T hT
  obtain ⟨hR, hell, hlen, hmenu⟩ := hgrid P ((le_max_left _ _).trans hP) T hT
  refine ⟨hR, hell, hlen, ?_⟩
  intro p hp
  let L := k.choose m * (T / intervalLength (beta h₀ A) P + 1)
  have hLp : (0 : ℝ) < L := by exact_mod_cast Nat.mul_pos (Nat.choose_pos hm) (Nat.succ_pos _)
  have hMp : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hLM : (L : ℝ) ≤ M := by exact_mod_cast hmenu
  have hpp : 0 < p := by linarith
  have hKp : (0 : ℝ) < topSize (alpha h₀) P := by exact_mod_cast topSize_pos (alpha h₀) P
  constructor
  · change 1 / (2 * (M : ℝ)) ≤ p / (L : ℝ)
    calc
      _ = (1 / 2) / (M : ℝ) := by ring
      _ ≤ _ := div_le_div₀ hpp.le hp hLp hLM
  · intro a ha
    have hpow : (a : ℝ) ^ (2 * remoteRadius (alpha h₀) A P + 1) ≤
        (A : ℝ) ^ (2 * remoteRadius (alpha h₀) A P + 1) := by gcongr
    calc
      _ ≤ (2 * T + 1 : ℕ) * (A : ℝ) ^ (2 * remoteRadius (alpha h₀) A P + 1) * M /
          ((topSize (alpha h₀) P : ℝ) * (1 / 2)) := by
        apply div_le_div₀ (by positivity) ?_ (by positivity) ?_
        · push_cast
          apply mul_le_mul (by gcongr) (by simpa only [L, Nat.cast_mul, Nat.cast_add, Nat.cast_one] using hLM)
            (by positivity) (by positivity)
        · nlinarith
      _ = (2 * T + 1 : ℕ) * (A : ℝ) ^ (2 * remoteRadius (alpha h₀) A P + 1) /
          ((topSize (alpha h₀) P : ℝ) * (1 / (2 * (M : ℝ)))) := by field_simp
      _ ≤ _ := hatom P ((le_max_right _ _).trans hP) T hT

theorem whole_word_numeric_rate {h₀ C : ℝ} {A k m : ℕ}
    (hh : 0 < h₀) (hA : 1 ≤ A) (hC : 0 ≤ C) (hm : m ≤ k) :
    ∃ P₀ : ℕ, ∀ P, P₀ ≤ P → ∀ T : ℕ, (T : ℝ) ≤ C * (P + 1) →
      ∀ p : ℝ, 1 / 2 ≤ p →
        (2 * T + 1 : ℕ) * (k.choose m * (T / intervalLength (beta h₀ A) P + 1) : ℕ) /
          ((topSize (alpha h₀) P + 1) * p) ≤ (2 : ℝ) ^ (-alpha h₀ * P / 2) := by
  obtain ⟨P₀, hr⟩ := future_mask_numeric_rate hh hA hC hm
  refine ⟨P₀, fun P hP T hT p hp => ?_⟩
  simpa only [one_pow, Nat.mul_one] using ((hr P hP T hT).2.2.2 p hp).2 1 hA

theorem word_catalogue_fits {Ω : Type*} [Fintype Ω]
    (M : TM) (input : Ω → List Bool) (τ : Ω → ℕ) (w : Ω → ℝ)
    (h₀ : ℝ) (A T P t : ℕ) (hA : M.g + 1 ≤ A) (h : Fin M.k) :
    (PersistenceFutureCatalogues.wordCatalogue M input τ w T (topSize (alpha h₀) P)
      (radius (beta h₀ A) P) t h).card ≤ futureCatalogue h₀ A P := by
  apply (PersistenceFutureCatalogues.word_catalogue_card M input τ w T
    (topSize (alpha h₀) P) (radius (beta h₀ A) P) t h).trans
  unfold futureCatalogue
  gcongr

/-- An integer distance exceeding the literal floor radius exceeds the
underlying positive linear radius, without losing another constant. -/
theorem remote_distance_real (α : ℝ) (A P : ℕ) (z : ℤ)
    (hz : (remoteRadius α A P : ℤ) < |z|) :
    α / (8 * Real.logb 2 (6 * A)) * P < (|z| : ℝ) := by
  have hi : (remoteRadius α A P : ℤ) + 1 ≤ |z| := by omega
  have hr : (remoteRadius α A P : ℝ) + 1 ≤ (|z| : ℝ) := by exact_mod_cast hi
  exact (Nat.lt_floor_add_one (α / (8 * Real.logb 2 (6 * A)) * P)).trans_le hr

/-- The literal retained event and interval, with probabilities under its
conditional law and successful returns on the actual original executions. -/
def Information {Ω : Type u} [Fintype Ω]
    (M : TM) (input : Ω → List Bool) (τ : Ω → ℕ) (w : Ω → ℝ) (B : Finset Ω)
    (T R m Hmask : ℕ) (p₀ atomBound : ℝ) : Prop :=
  ∃ H : Finset (Fin M.k), H.card = m ∧ ∃ j < T / (R / 2) + 1,
    ∃ E ⊆ B, p₀ ≤ ContextPruning.mass w E ∧
      (∀ x ∈ E, ∀ h ∈ H, ∀ t ∈ interval (R / 2) j, t < τ x) ∧
      (∀ h ∈ H, ∀ t ∈ interval (R / 2) j, ∀ v,
        atom (fun x => if x ∈ E then w x else 0) (fun _ => ())
            (fun x => PersistenceFuture.word M (input x) (τ x) t h) () v /
          ContextPruning.mass w E ≤ atomBound) ∧
      (∀ h ∈ H, ∀ t ∈ interval (R / 2) j, ∀ v,
        atom (fun x => if x ∈ E then w x else 0) (fun _ => ())
            (fun x => PersistenceFutureWindow.remoteWord M (input x) (τ x) T t Hmask h) () v /
          ContextPruning.mass w E ≤ atomBound) ∧
      ∀ x ∈ E, ∀ h ∈ H, ∀ t ∈ interval (R / 2) j, ∀ z,
        PersistenceFutureWindow.remoteWord M (input x) (τ x) T t Hmask h z ≠ 0 →
        ∃ p q, p < t ∧ t < q ∧ IsHop (fun s => (run M (input x) s).workPos h) (τ x) p q ∧
          transAt M (input x) p ≠ none ∧ transAt M (input x) q ≠ none ∧
          (run M (input x) p).workPos h = z ∧
          (Hmask : ℤ) < |(run M (input x) t).workPos h - (run M (input x) p).workPos h|

/-- A fixed-resource, fixed-length statement with only literal whole-word
catalogue escape left as a premise. The law and actual halting times are
universally quantified after the length threshold. -/
def AtLength (h₀ C : ℝ) (A k m P : ℕ) : Prop :=
  ∀ T : ℕ, (T : ℝ) ≤ C * (P + 1) →
    (⌈Real.logb 2 (futureCatalogue h₀ A P)⌉₊ : ℝ) ≤ h₀ * P ∧
    beta h₀ A * P / 4 ≤ intervalLength (beta h₀ A) P ∧
    ∀ M : TM, M.k = k → M.g + 1 ≤ A →
    ∀ (Ω : Type u) [Fintype Ω] (input : Ω → List Bool) (τ : Ω → ℕ) (w : Ω → ℝ),
      (∀ x, 0 ≤ w x) → (∑ x, w x = 1) →
      ∀ B : Finset Ω, 1 / 2 ≤ ContextPruning.mass w B →
        (∀ x ∈ B, τ x ≤ T) → (∀ x ∈ B, HaltsAt M (input x) (τ x)) →
        (∀ x ∈ B, ∃ t ≤ τ x, ∃ H : Finset (Fin M.k), H.card = m ∧
          ∀ h ∈ H, PersistenceFuture.word M (input x) (τ x) t h ∉
            PersistenceFutureCatalogues.wordCatalogue M input τ w T (topSize (alpha h₀) P)
              (radius (beta h₀ A) P) t h) →
        Information M input τ w B T (radius (beta h₀ A) P) m (remoteRadius (alpha h₀) A P)
          (selectionMass k m C (beta h₀ A)) ((2 : ℝ) ^ (-alpha h₀ * P / 2))

/-- Complete ordinary persistence assembly from a half-mass literal future
catalogue escape event. The threshold depends only on the displayed resource
constants, not the machine, input law, or input-dependent halting times. -/
theorem of_half_mass_escapes {h₀ C : ℝ} {A k m : ℕ}
    (hh : 0 < h₀) (hA : 1 ≤ A) (hC : 0 ≤ C) (hm : m ≤ k) :
    ∃ P₀ : ℕ, ∀ P, P₀ ≤ P → AtLength.{u} h₀ C A k m P := by
  obtain ⟨P₁, hcat⟩ := future_catalogue_bits_small hh hA
  obtain ⟨P₂, hrate⟩ := future_mask_numeric_rate hh hA hC hm
  refine ⟨max P₁ P₂, ?_⟩
  intro P hP T hT
  obtain ⟨hR, _hell, hlen, hbound⟩ := hrate P ((le_max_right _ _).trans hP) T hT
  refine ⟨hcat P ((le_max_left _ _).trans hP), hlen, ?_⟩
  intro M hMk hMA Ω inst input τ w hw hprob B hB hτ hhalt hescape
  have hp : 0 < ContextPruning.mass w B := (by norm_num : (0 : ℝ) < 1 / 2).trans_le hB
  obtain ⟨H, hH, j, hj, E, hEB, hmass, hlive, hwhole, hremote, hreturn⟩ :=
    PersistenceFutureSelection.exists_common_interval_atoms M input τ w hw hprob T
      (topSize (alpha h₀) P) (radius (beta h₀ A) P) m
      (topSize_pos (alpha h₀) P) hR B hp hτ hhalt hescape
  obtain ⟨hmassRate, hatomRate⟩ := hbound (ContextPruning.mass w B) hB
  refine ⟨H, hH, j, hj, E, hEB, ?_, hlive, ?_, ?_, ?_⟩
  · apply le_trans _ hmass
    simpa only [hMk, intervalLength] using hmassRate
  · intro h hh' t ht v
    apply (hwhole h hh' t ht v).trans
    simpa only [hMk, intervalLength, one_pow, Nat.mul_one] using hatomRate 1 hA
  · intro h hh' t ht v
    apply (hremote (remoteRadius (alpha h₀) A P) h hh' t ht v).trans
    simpa only [hMk, intervalLength] using hatomRate (M.g + 1) hMA
  · exact hreturn (remoteRadius (alpha h₀) A P)

/-- A single side-length threshold works for every positive bit width and
every machine and original law satisfying the fixed resource bounds. -/
theorem of_half_mass_escapes_all_widths {h₀ C : ℝ} {A k m : ℕ}
    (hh : 0 < h₀) (hA : 1 ≤ A) (hC : 0 ≤ C) (hm : m ≤ k) :
    ∃ d₀ : ℕ, ∀ d, d₀ ≤ d → ∀ b, 1 ≤ b → AtLength.{u} h₀ C A k m (d * d * b) := by
  obtain ⟨P₀, hr⟩ := of_half_mass_escapes.{u} hh hA hC hm
  exact AdaptiveTransfer.uniform_positive_width_threshold _ P₀ hr

end AdaptiveTransfer.PersistenceFutureRates
