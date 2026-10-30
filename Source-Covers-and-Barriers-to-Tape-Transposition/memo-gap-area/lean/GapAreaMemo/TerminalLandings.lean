import GapAreaMemo.LandingGaps

set_option autoImplicit false

/-!
# Theorem B: single-sweep terminal-landing geometries are excluded

For one geometry, the largest raw jump of a core step between landing times,
over all selections up to a prefix `J₀`, bounds the point area at every
selection with a larger prefix (the step persists as a family of the larger
core). Theorem G then forces these jumps to vanish in mean along a joint
profile. At the selection itself, the raw values lie in linearly many short
intervals, so the point area stays of order `1/R`; Theorem G then forces a
positive limiting hop tail, which is impossible.
-/

namespace SourceCovers

open Classical Finset Filter LeanMachine LeanMachine.MonotonePatches
open scoped BigOperators Topology
noncomputable section

theorem Finset.sup_eq_zero_or {α : Type*} (s : Finset α) (f : α → ℕ) :
    s.sup f = 0 ∨ ∃ a ∈ s, s.sup f = f a := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · exact Or.inl (Finset.sup_empty)
  · exact Or.inr (Finset.exists_mem_eq_sup s hs f)

namespace AdmissibleGeometry

variable {c β : ℝ} {N q : ℕ} (G : AdmissibleGeometry c β N q) (O : SortedCore G.core)
variable (D : G.TerminalLanding)

/-- The largest raw jump of a landing step over all selections `R ≤ J ≤ J₀`
with modulus `2R + 2` and all legal phases, at the root of column `j`. -/
def landingGamma (J₀ j : ℕ) : ℕ :=
  (range (J₀ + 1)).sup fun J => (range (J + 1)).sup fun R =>
    (admissiblePhases (O.selectedPrefix J) (O.subprefix J R) (2 * R + 2)).sup fun ρ =>
      stepMax (O.selectedPrefix J) (2 * R + 2) ρ D.g D.e G.x (columnFirst G.t (G.d * G.b) j)

theorem stepMax_le_landingGamma {J₀ J R ρ j : ℕ} (hJ : J ≤ J₀) (hR : R ≤ J)
    (hρ : ρ ∈ admissiblePhases (O.selectedPrefix J) (O.subprefix J R) (2 * R + 2)) :
    stepMax (O.selectedPrefix J) (2 * R + 2) ρ D.g D.e G.x (columnFirst G.t (G.d * G.b) j) ≤
      G.landingGamma O D J₀ j := by
  unfold landingGamma
  refine le_trans ?_ (le_sup (f := fun J => (range (J + 1)).sup fun R =>
    (admissiblePhases (O.selectedPrefix J) (O.subprefix J R) (2 * R + 2)).sup fun ρ =>
      stepMax (O.selectedPrefix J) (2 * R + 2) ρ D.g D.e G.x (columnFirst G.t (G.d * G.b) j))
    (mem_range.mpr (Nat.lt_succ_of_le hJ)))
  refine le_trans ?_ (le_sup (f := fun R =>
    (admissiblePhases (O.selectedPrefix J) (O.subprefix J R) (2 * R + 2)).sup fun ρ =>
      stepMax (O.selectedPrefix J) (2 * R + 2) ρ D.g D.e G.x (columnFirst G.t (G.d * G.b) j))
    (mem_range.mpr (Nat.lt_succ_of_le hR)))
  exact le_sup (f := fun ρ =>
      stepMax (O.selectedPrefix J) (2 * R + 2) ρ D.g D.e G.x (columnFirst G.t (G.d * G.b) j)) hρ

/-- The largest jump is attained by an actual landing step at some selection. -/
theorem landingGamma_attained (J₀ j : ℕ) :
    G.landingGamma O D J₀ j = 0 ∨ ∃ J ≤ J₀, ∃ R ≤ J,
      ∃ ρ ∈ admissiblePhases (O.selectedPrefix J) (O.subprefix J R) (2 * R + 2),
      ∃ u ∈ landingSet (O.selectedPrefix J) (2 * R + 2) ρ D.g D.e (columnFirst G.t (G.d * G.b) j),
      ∃ b ∈ phaseSurvivors (O.selectedPrefix J) (2 * R + 2) ρ,
        IsLandingStep (O.selectedPrefix J) D.e u b ∧
          stepJump (O.selectedPrefix J) D.e G.x u b = G.landingGamma O D J₀ j := by
  unfold landingGamma
  rcases Finset.sup_eq_zero_or (range (J₀ + 1)) _ with h | ⟨J, hJ, h⟩
  · exact Or.inl h
  rw [h]
  rcases Finset.sup_eq_zero_or (range (J + 1)) _ with h' | ⟨R, hR, h'⟩
  · exact Or.inl h'
  rw [h']
  rcases Finset.sup_eq_zero_or (admissiblePhases (O.selectedPrefix J) (O.subprefix J R)
    (2 * R + 2)) _ with h'' | ⟨ρ, hρ, h''⟩
  · exact Or.inl h''
  rw [h'']
  unfold stepMax
  rcases Finset.sup_eq_zero_or _ _ with h''' | ⟨p, hp, h'''⟩
  · exact Or.inl h'''
  rw [h''']
  obtain ⟨hpm, hstep⟩ := mem_filter.mp hp
  obtain ⟨hu, hb⟩ := mem_product.mp hpm
  exact Or.inr ⟨J, Nat.lt_succ_iff.mp (mem_range.mp hJ), R, Nat.lt_succ_iff.mp (mem_range.mp hR),
    ρ, hρ, p.1, hu, p.2, hb, hstep, rfl⟩

theorem landingSet_lt {K : Finset (ActualFamily G.xs G.T)} (hc : HasSpanColoring K 2) {M ρ : ℕ}
    (hρ : ρ < M) {j u : ℕ} (hj : j < G.d)
    (hu : u ∈ landingSet K M ρ D.g D.e (columnFirst G.t (G.d * G.b) j)) : u < G.T :=
  (newerClosure_le hc hρ D.g (mem_filter.mp hu).1).trans_lt (columnFirst_lt G hj)

theorem landingGamma_le (J₀ : ℕ) {j : ℕ} (hj : j < G.d) :
    G.landingGamma O D J₀ j ≤ G.inputLength := by
  rcases G.landingGamma_attained O D J₀ j with h | ⟨J, _, R, _, ρ, hρ, u, hu, b, _, hstep, h⟩
  · rw [h]; exact Nat.zero_le _
  · rw [← h]
    have huT := G.landingSet_lt D (G.core_coloring.mono (O.selectedPrefix_subset J))
      (admissiblePhase_lt hρ) hj hu
    have hle : D.e.shadow (b.val.shadow u) ≤ G.T - 1 := by
      have h1 := D.e.shadowAction.apply_le (b.val.shadow u)
      have h2 := b.val.shadowAction.apply_le u
      change D.e.shadow (b.val.shadow u) ≤ b.val.shadow u at h1
      change b.val.shadow u ≤ u at h2
      omega
    have := G.raw_range _ hle
    unfold stepJump
    simp only [inputLength]
    omega

/-- Mean squared relative jump over columns. -/
def landingEnergy (J₀ : ℕ) : ℝ :=
  (∑ j ∈ range G.d, ((G.landingGamma O D J₀ j : ℝ) / G.inputLength) ^ 2) / G.d

theorem landingEnergy_bounds (J₀ : ℕ) : 0 ≤ G.landingEnergy O D J₀ ∧ G.landingEnergy O D J₀ ≤ 1 := by
  have hL : (0 : ℝ) < G.inputLength := by exact_mod_cast G.inputLength_pos
  have hd : (0 : ℝ) < G.d := by exact_mod_cast G.hd
  have hpt : ∀ j ∈ range G.d, ((G.landingGamma O D J₀ j : ℝ) / G.inputLength) ^ 2 ≤ 1 := by
    intro j hj
    have h := G.landingGamma_le O D J₀ (mem_range.mp hj)
    have h1 : (G.landingGamma O D J₀ j : ℝ) / G.inputLength ≤ 1 := by
      rw [div_le_one hL]; exact_mod_cast h
    have h0 : 0 ≤ (G.landingGamma O D J₀ j : ℝ) / G.inputLength := by positivity
    nlinarith
  refine ⟨by unfold landingEnergy; positivity, ?_⟩
  unfold landingEnergy
  rw [div_le_one hd]
  calc
    _ ≤ ∑ _j ∈ range G.d, (1 : ℝ) := sum_le_sum hpt
    _ = G.d := by simp

/-- Averaging a column bound that does not depend on the phase. -/
theorem le_prefixMeanGapArea_of_columns {J R M : ℕ} (hM : 2 ≤ M) (hRM : R < M) (f : ℕ → ℝ)
    (hf : ∀ ρ ∈ admissiblePhases (O.selectedPrefix J) (O.subprefix J R) M, ∀ j < G.d,
      f j ≤ phaseGapArea (G.core_coloring.mono (O.selectedPrefix_subset J)) hM
        G.exceptions G.x G.t G.d G.b ρ j) :
    (∑ j ∈ range G.d, f j) / G.d ≤ G.prefixMeanGapArea O J R M hM := by
  have hA := (protected_phase_average (O.selectedPrefix J) (O.subprefix J R)
    (O.subprefix_card_le J R) hRM).1
  set A := admissiblePhases (O.selectedPrefix J) (O.subprefix J R) M
  have hAne : A.Nonempty := card_pos.mp (lt_of_lt_of_le (Nat.sub_pos_of_lt hRM) hA)
  have hAc : (0 : ℝ) < A.card := by exact_mod_cast card_pos.mpr hAne
  have hd : (0 : ℝ) < G.d := by exact_mod_cast G.hd
  unfold prefixMeanGapArea meanGapArea
  rw [div_le_div_iff₀ hd (mul_pos hAc hd)]
  calc
    (∑ j ∈ range G.d, f j) * (A.card * G.d) =
        (∑ _ρ ∈ A, ∑ j ∈ range G.d, f j) * G.d := by
      rw [sum_const, nsmul_eq_mul]; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ hd.le
      exact sum_le_sum fun ρ hρ => sum_le_sum fun j hj => hf ρ hρ j (mem_range.mp hj)

/-- The point-area constant of a step at modulus `2R + 2`. -/
def stepConstant (R : ℕ) : ℝ := 2 * (((1 + (2 * (2 * R + 2) + 4) * 11 : ℕ) : ℝ) + 2)

theorem stepConstant_pos (R : ℕ) : 0 < stepConstant R := by unfold stepConstant; positivity

/-- **Later selections.** Every selection with prefix at least `J₀` has mean
point area at least the landing energy at `J₀`, divided by the step constant. -/
theorem prefixMeanGapArea_ge_later {J₀ J R : ℕ} (hJ : J₀ ≤ J) :
    G.landingEnergy O D J₀ / stepConstant R ≤
      G.prefixMeanGapArea O J R (2 * R + 2) (by omega) := by
  have hmean := G.le_prefixMeanGapArea_of_columns O (J := J) (R := R) (M := 2 * R + 2)
    (by omega) (by omega)
    (fun j => ((G.landingGamma O D J₀ j : ℝ) / G.inputLength) ^ 2 / stepConstant R) (by
      intro ρ hρ j hj
      rcases G.landingGamma_attained O D J₀ j with h0 | ⟨J', hJ', R', _, ρ', hρ', u, hu, b, hb,
          hstep, hjump⟩
      · rw [h0]
        simp only [Nat.cast_zero, zero_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
          zero_pow]
        exact (phaseGapArea_bounds _ (by omega) (admissiblePhase_lt hρ) G.exceptions G.x G.t
          G.hd G.hb hj G.append_lt G.raw_range).1
      · have hsub : O.selectedPrefix J' ⊆ O.selectedPrefix J := O.selectedPrefix_mono (hJ'.trans hJ)
        let b'' : CoreFamily (O.selectedPrefix J) := ⟨b.val, hsub b.property⟩
        have huT := G.landingSet_lt D (G.core_coloring.mono (O.selectedPrefix_subset J'))
          (admissiblePhase_lt hρ') hj hu
        have h := D.gap_of_step (O.selectedPrefix_subset J)
          (G.core_coloring.mono (O.selectedPrefix_subset J)) (M := 2 * R + 2) (by omega)
          (admissiblePhase_lt hρ) hj b'' hstep.1 (mem_filter.mp hu).2 ⟨hstep.2.1, hstep.2.2⟩ huT
        have hj' : (G.x (D.e.shadow (b''.val.shadow u)) - G.x (D.e.shadow u) : ℕ) =
            G.landingGamma O D J₀ j := hjump
        rw [hj'] at h
        unfold stepConstant
        exact h)
  have heq : (∑ j ∈ range G.d,
      ((G.landingGamma O D J₀ j : ℝ) / G.inputLength) ^ 2 / stepConstant R) / G.d =
      G.landingEnergy O D J₀ / stepConstant R := by
    unfold landingEnergy
    rw [← sum_div]
    ring
  rwa [heq] at hmean

/-- The interval count and length factor at modulus `2R + 2`. -/
def startCount (R : ℕ) : ℝ := ((1 + 5 * (2 * (2 * R + 2) + 4) : ℕ) : ℝ)

def startFactor (R : ℕ) : ℝ := ((5 * (2 * (2 * R + 2) + 4) * (2 * R + 2 + 1) : ℕ) : ℝ)

theorem startCount_pos (R : ℕ) : 0 < startCount R := by unfold startCount; positivity

/-- **The selection itself.** -/
theorem prefixMeanGapArea_ge_own {J R : ℕ} (hRJ : R ≤ J) :
    (1 / 2 - 2 * startFactor R ^ 2 * G.landingEnergy O D J) / (2 * startCount R) ≤
      G.prefixMeanGapArea O J R (2 * R + 2) (by omega) := by
  have hL : (0 : ℝ) < G.inputLength := by exact_mod_cast G.inputLength_pos
  have hmean := G.le_prefixMeanGapArea_of_columns O (J := J) (R := R) (M := 2 * R + 2)
    (by omega) (by omega)
    (fun j => (1 / 2 - 2 * startFactor R ^ 2 *
      ((G.landingGamma O D J j : ℝ) / G.inputLength) ^ 2) / (2 * startCount R)) (by
      intro ρ hρ j hj
      have h := D.gap_of_starts (O.selectedPrefix_subset J)
        (G.core_coloring.mono (O.selectedPrefix_subset J)) (M := 2 * R + 2) (by omega)
        (admissiblePhase_lt hρ) hj
      refine le_trans ?_ h
      have hst := G.stepMax_le_landingGamma O D (J₀ := J) (j := j) le_rfl hRJ hρ
      set y : ℝ := (G.landingGamma O D J j : ℝ) / G.inputLength
      set α : ℝ := (((5 * (2 * (2 * R + 2) + 4) * ((2 * R + 2 + 1) * stepMax (O.selectedPrefix J)
        (2 * R + 2) ρ D.g D.e G.x (columnFirst G.t (G.d * G.b) j)) : ℕ) : ℝ)) / G.inputLength
      have hα : α ≤ startFactor R * y := by
        have hnat : 5 * (2 * (2 * R + 2) + 4) * ((2 * R + 2 + 1) * stepMax (O.selectedPrefix J)
            (2 * R + 2) ρ D.g D.e G.x (columnFirst G.t (G.d * G.b) j)) ≤
            5 * (2 * (2 * R + 2) + 4) * (2 * R + 2 + 1) * G.landingGamma O D J j := by
          calc
            _ = 5 * (2 * (2 * R + 2) + 4) * (2 * R + 2 + 1) * stepMax (O.selectedPrefix J)
                (2 * R + 2) ρ D.g D.e G.x (columnFirst G.t (G.d * G.b) j) := by ring
            _ ≤ _ := Nat.mul_le_mul_left _ hst
        have hrw : startFactor R * y = (((5 * (2 * (2 * R + 2) + 4) * (2 * R + 2 + 1) *
            G.landingGamma O D J j : ℕ) : ℝ)) / G.inputLength := by
          simp only [startFactor, y]
          push_cast
          ring
        rw [hrw]
        exact div_le_div_of_nonneg_right (by exact_mod_cast hnat) hL.le
      have hy : 0 ≤ y := by positivity
      have hF : 0 ≤ startFactor R := by unfold startFactor; positivity
      have hsq : 1 / 2 - 2 * startFactor R ^ 2 * y ^ 2 ≤ max (1 - α) 0 ^ 2 := by
        have h1 : 1 - 2 * α ≤ max (1 - α) 0 ^ 2 := by
          rcases le_total α 1 with hα1 | hα1
          · rw [max_eq_left (by linarith)]; nlinarith [sq_nonneg α]
          · have : 0 ≤ max (1 - α) 0 ^ 2 := by positivity
            linarith
        nlinarith [sq_nonneg (startFactor R * y - 1 / 2)]
      have hcnt : startCount R = ((1 + 5 * (2 * (2 * R + 2) + 4) : ℕ) : ℝ) := rfl
      rw [hcnt]
      exact div_le_div_of_nonneg_right hsq (by positivity))
  have heq : (∑ j ∈ range G.d, (1 / 2 - 2 * startFactor R ^ 2 *
      ((G.landingGamma O D J j : ℝ) / G.inputLength) ^ 2) / (2 * startCount R)) / G.d =
      (1 / 2 - 2 * startFactor R ^ 2 * G.landingEnergy O D J) / (2 * startCount R) := by
    have hd : (G.d : ℝ) ≠ 0 := by exact_mod_cast G.hd.ne'
    unfold landingEnergy
    rw [← sum_div, sum_sub_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul]
    field_simp
  rwa [heq] at hmean

end AdmissibleGeometry

namespace NearFullSequence

variable {c β : ℝ} {N q : ℕ}

/-- **Theorem B.** No near-full sequence consists, from some point on, of
single-sweep terminal-landing geometries. No size envelope is assumed. -/
theorem not_eventually_terminalLanding (S : NearFullSequence c β N q)
    (hD : ∀ᶠ ν in atTop, Nonempty (S.geometry ν).TerminalLanding) : False := by
  obtain ⟨P⟩ := S.exists_jointProfile
  have hDn : ∀ᶠ n in atTop, Nonempty (S.geometry (P.subsequence n)).TerminalLanding :=
    P.strictMono.tendsto_atTop.eventually hD
  let Y : ℕ → ℕ → ℝ := fun J₀ n =>
    if h : Nonempty (S.geometry (P.subsequence n)).TerminalLanding then
      (S.geometry (P.subsequence n)).landingEnergy (S.order (P.subsequence n))
        (Classical.choice h) J₀
    else 0
  have hYeq : ∀ J₀ n (h : Nonempty (S.geometry (P.subsequence n)).TerminalLanding),
      Y J₀ n = (S.geometry (P.subsequence n)).landingEnergy (S.order (P.subsequence n))
        (Classical.choice h) J₀ := fun J₀ n h => dite_eq_left h
  have hβ : 0 ≤ β := recordCapacity_nonneg (S.geometry 0).capacity
  have hτ : ∀ R, 0 ≤ β * P.hopTail R := fun R => mul_nonneg hβ (P.tails_nonneg R).1
  have htail : Tendsto (fun R => β * P.hopTail R) atTop (𝓝 0) := by
    simpa only [mul_zero] using P.tails_tendsto_zero.1.const_mul β
  have hbdd : ∀ J R, ∀ n, P.prefixGapArea J R (2 * R + 2) (by omega) n ≤ 1 := fun J R n =>
    (P.prefixGapArea_bounds (J := J) (by omega) (by omega) n).2.trans (by norm_num)
  have hbddJ : ∀ R J, limsup (P.prefixGapArea J R (2 * R + 2) (by omega)) atTop ≤ 1 := fun R J =>
    (P.prefixGapArea_limsup_bounds (J := J) (R := R) (M := 2 * R + 2) (by omega) (by omega)).2.trans
      (by norm_num)
  -- Step 1: the landing energies vanish along the subsequence
  have henergy : ∀ J₀, ∀ ε > 0, ∀ᶠ n in atTop, Y J₀ n < ε := by
    intro J₀ ε hε
    by_contra hfreq
    rw [not_eventually] at hfreq
    have hfreq' : ∃ᶠ n in atTop, ε ≤ Y J₀ n ∧
        Nonempty (S.geometry (P.subsequence n)).TerminalLanding :=
      (hfreq.and_eventually hDn).mono fun n h => ⟨not_lt.mp h.1, h.2⟩
    have hR : ∀ R, ε ≤ 91 * (β * P.hopTail R) := by
      intro R
      have hJ : ∀ J ≥ max J₀ R, ε / AdmissibleGeometry.stepConstant R ≤
          limsup (P.prefixGapArea J R (2 * R + 2) (by omega)) atTop := by
        intro J hJ
        apply le_limsup_of_frequently_le _
          (isBoundedUnder_of_eventually_le (Eventually.of_forall (hbdd J R)))
        refine hfreq'.mono ?_
        rintro n ⟨hn, hne⟩
        have h := (S.geometry (P.subsequence n)).prefixMeanGapArea_ge_later
          (S.order (P.subsequence n)) (Classical.choice hne) (J₀ := J₀) (J := J) (R := R)
          (le_of_max_le_left hJ)
        rw [← hYeq J₀ n hne] at h
        exact (div_le_div_of_nonneg_right hn (AdmissibleGeometry.stepConstant_pos R).le).trans h
      have hlim : ε / AdmissibleGeometry.stepConstant R ≤ P.gapAreaLimit R (2 * R + 2) (by omega) :=
        BoundedLimsup.le_limsup (hbddJ R) (eventually_atTop.2 ⟨max J₀ R, hJ⟩)
      have hG := hlim.trans (P.necessary_gap_area_default R)
      have hC := AdmissibleGeometry.stepConstant_pos R
      have hCle : AdmissibleGeometry.stepConstant R ≤ 91 * ((R : ℝ) + 2) := by
        unfold AdmissibleGeometry.stepConstant
        push_cast
        nlinarith
      rw [div_le_div_iff₀ hC (by positivity)] at hG
      have := hτ R
      nlinarith
    obtain ⟨R, hR'⟩ := (htail.const_mul 91).eventually (gt_mem_nhds (by simpa using hε)) |>.exists
    exact absurd (hR R) (not_le.mpr hR')
  -- Step 2: the selections themselves keep point area of order `1/R`
  have hfinal : ∀ R, 1 / 164 ≤ β * P.hopTail R := by
    intro R
    have hF : 0 < AdmissibleGeometry.startFactor R := by
      unfold AdmissibleGeometry.startFactor; positivity
    have hC := AdmissibleGeometry.startCount_pos R
    have hJ : ∀ J ≥ R, 1 / (8 * AdmissibleGeometry.startCount R) ≤
        limsup (P.prefixGapArea J R (2 * R + 2) (by omega)) atTop := by
      intro J hJ
      apply BoundedLimsup.le_limsup (hbdd J R)
      filter_upwards [hDn, henergy J (1 / (8 * AdmissibleGeometry.startFactor R ^ 2))
        (by positivity)] with n hne hsmall
      have h := (S.geometry (P.subsequence n)).prefixMeanGapArea_ge_own
        (S.order (P.subsequence n)) (Classical.choice hne) (J := J) (R := R) hJ
      rw [← hYeq J n hne] at h
      refine le_trans ?_ h
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h2 : 2 * AdmissibleGeometry.startFactor R ^ 2 * Y J n ≤ 1 / 4 := by
        have hm := mul_lt_mul_of_pos_left hsmall
          (by positivity : (0 : ℝ) < 2 * AdmissibleGeometry.startFactor R ^ 2)
        have heq : 2 * AdmissibleGeometry.startFactor R ^ 2 *
            (1 / (8 * AdmissibleGeometry.startFactor R ^ 2)) = 1 / 4 := by
          field_simp
          ring
        linarith
      nlinarith
    have hlim : 1 / (8 * AdmissibleGeometry.startCount R) ≤ P.gapAreaLimit R (2 * R + 2) (by omega) :=
      BoundedLimsup.le_limsup (hbddJ R) (eventually_atTop.2 ⟨R, hJ⟩)
    have hG := hlim.trans (P.necessary_gap_area_default R)
    have hcnt : AdmissibleGeometry.startCount R = 20 * (R : ℝ) + 41 := by
      unfold AdmissibleGeometry.startCount; push_cast; ring
    rw [hcnt, div_le_div_iff₀ (by positivity) (by positivity)] at hG
    nlinarith [hτ R]
  obtain ⟨R, hR⟩ := htail.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 164)) |>.exists
  exact absurd (hfinal R) (not_le.mpr hR)

/-- The same conclusion when such geometries occur only along a subsequence. -/
theorem not_frequently_terminalLanding (S : NearFullSequence c β N q)
    (hD : ∃ᶠ ν in atTop, Nonempty (S.geometry ν).TerminalLanding) : False := by
  obtain ⟨φ, hφ, hφD⟩ := Filter.extraction_of_frequently_atTop hD
  exact (S.subseq φ hφ).not_eventually_terminalLanding (Eventually.of_forall hφD)

end NearFullSequence

end
end SourceCovers
