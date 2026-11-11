import AdaptiveTransfer.CarrierBudgetRates
import AdaptiveTransfer.ReturnHeads
import AdaptiveTransfer.Storage

/-! The simultaneous-storage consequence of an actual one-head carrier
simulation. The common simulator and its halt/output correspondence remain
explicit hypotheses; its complete bit budget and the success count are derived.
-/

namespace AdaptiveTransfer

open Transpose Transpose.Tape MergeDepth NativeRelations LeanMachine Finset
attribute [local instance] Classical.propDecidable

/-- On every time within the cap this finite support is the entire nonblank
support of the actual infinite native work tape. -/
theorem native_support_window_complete (M : TM) (w : List Bool) {t T : ℕ}
    (ht : t ≤ T) (h : Fin M.k) (z : ℤ) :
    z ∈ nonblankWithin (run M w t) h (Icc (-(T : ℤ)) T) ↔
      (run M w t).work h z ≠ 0 := by
  constructor
  · exact fun hz => (mem_filter.mp hz).2
  · intro hz
    refine mem_filter.mpr ⟨?_, hz⟩
    have habs : |z| ≤ T := by
      by_contra hn
      apply hz
      apply Transpose.Tape.Impl.work_eq_blank
      intro u hu he
      have hpos := Transpose.Tape.Impl.abs_workPos_le (M := M) w u h
      rw [he] at hpos
      exact hn (hpos.trans (by exact_mod_cast hu.le.trans ht))
    exact mem_Icc.mpr (abs_le.mp habs)

noncomputable def denseHeads (M : TM) (w : List Bool) (T m t : ℕ) : Finset (Fin M.k) :=
  univ.filter (fun h => m < (nonblankWithin (run M w t) h (Icc (-(T : ℤ)) T)).card)

def OneDensePromise (M : TM) (w : List Bool) (T m : ℕ) : Prop :=
  ∀ t ≤ (trace M w).haltTime, (denseHeads M w T m t).card ≤ 1

noncomputable def storeBadInputs (M : TM) (d b m : ℕ) (C : ℝ) :
    Finset (Fin (d*d*b) → Bool) :=
  univ.filter (fun X => TransposesInput M d b C X ∧
    OneDensePromise M (List.ofFn X) (returnTime (d*d*b) C) m)

/-- Failure of the integer sparse promise is exactly a simultaneous pair of
large actual supports, including the terminal configuration. -/
theorem not_oneDensePromise_iff {M : TM} {w : List Bool} {T : ℕ} {D : ℝ}
    (hD : 0 ≤ D) :
    ¬ OneDensePromise M w T ⌊D⌋₊ ↔
      ∃ t ≤ (trace M w).haltTime, ∃ f g : Fin M.k, f ≠ g ∧
        D < ((nonblankWithin (run M w t) f (Icc (-(T : ℤ)) T)).card : ℝ) ∧
        D < ((nonblankWithin (run M w t) g (Icc (-(T : ℤ)) T)).card : ℝ) := by
  simp only [OneDensePromise, not_forall, not_le]
  constructor
  · rintro ⟨t, ht, hpair⟩
    obtain ⟨f, hf, g, hg, hfg⟩ := one_lt_card.mp hpair
    exact ⟨t, ht, f, g, hfg,
      (Nat.floor_lt hD).mp (mem_filter.mp hf).2,
      (Nat.floor_lt hD).mp (mem_filter.mp hg).2⟩
  · rintro ⟨t, ht, f, g, hfg, hf, hg⟩
    exact ⟨t, ht, one_lt_card.mpr ⟨f,
      mem_filter.mpr ⟨mem_univ _, (Nat.floor_lt hD).mpr hf⟩, g,
      mem_filter.mpr ⟨mem_univ _, (Nat.floor_lt hD).mpr hg⟩, hfg⟩⟩

theorem native_two_dense_heads {M : TM} {d b : ℕ} {C δ : ℝ} (hδ : 0 ≤ δ)
    {X : Fin (d*d*b) → Bool} (hc : TransposesInput M d b C X)
    (hg : X ∉ storeBadInputs M d b ⌊δ * (d*d*b : ℕ)⌋₊ C) :
    let T := returnTime (d*d*b) C
    ∃ t ≤ (trace M (List.ofFn X)).haltTime, ∃ f g : Fin M.k, f ≠ g ∧
      δ * (d*d*b : ℕ) < ((nonblankWithin (run M (List.ofFn X) t) f (Icc (-(T : ℤ)) T)).card : ℝ) ∧
      δ * (d*d*b : ℕ) < ((nonblankWithin (run M (List.ofFn X) t) g (Icc (-(T : ℤ)) T)).card : ℝ) := by
  apply (not_oneDensePromise_iff (mul_nonneg hδ (Nat.cast_nonneg _))).mp
  intro hp
  exact hg (mem_filter.mpr ⟨mem_univ _, hc, hp⟩)

/-- The halt/output portion of the written carrier compiler's stronger
step-for-step contract. This definition supplies no simulator by itself. -/
def SameTimedOutput (M R : TM) (w : List Bool) (T : ℕ) : Prop :=
  ∀ t ≤ T, HaltsAt M w t →
    HaltsAt R w t ∧ (run R w t).outRev = (run M w t).outRev

theorem transposes_of_sameTimedOutput {M R : TM} {d b : ℕ} {C : ℝ}
    {X : Fin (d*d*b) → Bool} (hc : TransposesInput M d b C X)
    (hsim : SameTimedOutput M R (List.ofFn X) (returnTime (d*d*b) C)) :
    TransposesInput R d b C X := by
  obtain ⟨matrix, he, hc⟩ := hc
  obtain ⟨t, ht, hhalt, hout⟩ := (Transpose.Tape.Impl.computesWithin_iff _ _).mp hc
  obtain ⟨hR, houtput⟩ := hsim t ht hhalt
  refine ⟨matrix, he, (Transpose.Tape.Impl.computesWithin_iff _ _).mpr ⟨t, ht, hR, ?_⟩⟩
  rw [houtput]
  exact hout

/-- A single real simulator on the whole promise set suffices. The theorem
derives its bit budget from the literal carrier state expression; neither
a final bit-cost certificate nor a counting bound is supplied. -/
theorem stores_tail_of_carrier (k a : ℕ) (hk : 1 ≤ k) (ha : 1 ≤ a) {C : ℝ} (hC : 1 ≤ C) :
    let N := slabRunCap a C
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 8 ∧ ∃ d₀ : ℕ, ∀ d, d₀ ≤ d → ∀ b, 1 ≤ b →
      ∀ M : TM, M.k = k → ∀ q : ℕ, M.q + 1 ≤ 2 ^ q → M.g + 1 ≤ 2 ^ a →
      (q : ℝ) ≤ (d*d*b : ℕ) / (128 * (N : ℝ) ^ 2) →
      ∀ R : TM, R.k = 1 → R.g = M.g →
      R.q + 1 ≤ carrierStateBound M.k a (M.q + 1) (returnTime (d*d*b) C) ⌊δ * (d*d*b : ℕ)⌋₊ →
      (∀ X ∈ storeBadInputs M d b ⌊δ * (d*d*b : ℕ)⌋₊ C,
        SameTimedOutput M R (List.ofFn X) (returnTime (d*d*b) C)) →
      ((storeBadInputs M d b ⌊δ * (d*d*b : ℕ)⌋₊ C).card : ℝ) <
        (2 : ℝ) ^ ((1 - returnTailEta N) * (d*d*b : ℕ)) := by
  let N := slabRunCap a C
  have hN : 1 ≤ N := by dsimp [N, slabRunCap]; omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  let ρ : ℝ := 1 / (64 * (N : ℝ) ^ 2)
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  obtain ⟨δ, hδ, hδcap, P₀, hbits⟩ := carrier_state_bits_small k a hk
    (C := C) (ρ := ρ) (by linarith) hρ
  obtain ⟨d₁, hsize⟩ := uniform_positive_width_threshold (fun P => P₀ ≤ P) P₀ (fun _ h => h)
  obtain ⟨γ, _hγ, _hγcap, d₂, htail⟩ := native_macroscopic_return_tail 1 a (by norm_num) ha hC
  refine ⟨δ, hδ, hδcap, max d₁ d₂, ?_⟩
  intro d hd b hb M hMk q hq hA hbudget R hRk hRg hRstates hsim
  let P := d*d*b
  let T := returnTime P C
  let states := carrierStateBound k a (M.q + 1) T ⌊δ * (P : ℝ)⌋₊
  let bits := Nat.clog 2 states
  have hT : (T : ℝ) ≤ C * (P + 1) := Nat.floor_le (by positivity)
  have hsource : (q : ℝ) ≤ ρ * P / 2 := by
    have he : (P : ℝ) / (128 * (N : ℝ) ^ 2) = ρ * P / 2 := by dsimp [ρ]; ring
    exact he ▸ hbudget
  have hsmall := hbits P (hsize d ((le_max_left _ _).trans hd) b hb) T hT (M.q + 1) q hq hsource
  have hbitsR : (bits : ℝ) ≤ (P : ℝ) / (64 * (N : ℝ) ^ 2) := by
    convert hsmall using 1
    dsimp [ρ]
    ring
  have hstates : R.q + 1 ≤ 2 ^ bits := by
    apply le_trans _ (Nat.le_pow_clog (by norm_num : 1 < 2) states)
    simpa only [states, hMk] using hRstates
  have hAR : R.g + 1 ≤ 2 ^ a := by simpa only [hRg] using hA
  have htailR := htail d ((le_max_right _ _).trans hd) b hb R hRk bits hstates hAR hbitsR
  have hsub : storeBadInputs M d b ⌊δ * (P : ℝ)⌋₊ C ⊆
      nativeBadInputs R d b C ⌊returnTailEpsilon 1 a N * (P : ℝ)⌋₊ ⌊γ * (P : ℝ)⌋₊ := by
    intro X hX
    apply native_one_head_bad hRk
    exact transposes_of_sameTimedOutput (mem_filter.mp hX).2.1 (hsim X hX)
  exact (show ((storeBadInputs M d b ⌊δ * (P : ℝ)⌋₊ C).card : ℝ) ≤
    (nativeBadInputs R d b C ⌊returnTailEpsilon 1 a N * (P : ℝ)⌋₊ ⌊γ * (P : ℝ)⌋₊).card by
      exact_mod_cast card_le_card hsub).trans_lt htailR

end AdaptiveTransfer
