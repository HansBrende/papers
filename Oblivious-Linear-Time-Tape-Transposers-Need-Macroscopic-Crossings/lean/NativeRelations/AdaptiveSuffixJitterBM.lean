import NativeRelations.SuffixMassCrux
import NativeRelations.JitterMacroBank

/-!
# Adaptive Suffix Jitter-Bank Exclusion and Whole-Run Specialization (Theorem J)

Proves the native storage-code rate gap and adaptive linear-time exclusion for `AdaptiveSuffixJitterBM`
(`nativeGapBound_of_adaptiveSuffixJitterBM`, `adaptiveSuffixJitterBM_excludes_transposesAt`,
`adaptiveSuffixJitterBM_not_linearTimeTransposer`), and deduces the whole-run `AdaptiveJitterBM`
gap and exclusions (`nativeGapBound_of_adaptiveJitterBM`, `adaptiveJitterBM_excludes_transposesAt`,
`adaptiveJitterBM_not_linearTimeTransposer`) as the `δ₀ = 1` specialization.
-/

set_option autoImplicit false

namespace NativeRelations

open Filter Finset Transpose Transpose.Tape BoundedNesting MergeDepth MotionDepthCodes
  BoundedStackDepth TapeStorageRates
open scoped BigOperators Topology

/-! ## §1. Suffix Jitter-BM Predicates (Theorem 9.4 / Theorem J) -/

/-- **Single-trace suffix + jittered-BM predicate (`TraceHasSuffixJitterBM`)**:
on `[0, T)`, no output occurs before `t_suf` (`z (some none) t_suf ≤ 0`), the suffix `[t_suf, T)`
partitions into `M_ph` coarse-monotone macro-phases of amplitude `A` for `z none` and `B_bank` with
at most `S` visited cells per workspace head `w ∉ B_bank`, and during `[0, t_suf)` the input head
`z none` never enters the `E_pad`-interior `[i * d * b + E_pad, (i + 1) * d * b - E_pad)` of any raw
row `i ∈ R_suf`. -/
def TraceHasSuffixJitterBM {k : ℕ} (z : Tp k → ℕ → ℤ) (d b T t_suf M_ph : ℕ)
    (B_bank : Finset (Fin k)) (R_suf : Finset (Fin d)) (E_pad A S : ℕ) : Prop :=
  t_suf ≤ T ∧
  z (some none) t_suf ≤ 0 ∧
  (∃ a : ℕ → ℕ, a 0 = t_suf ∧ a M_ph = T ∧ (∀ α < M_ph, a α ≤ a (α + 1)) ∧
    (∀ α < M_ph, CoarseMonoOnInterval (z none) (a α) (a (α + 1)) A) ∧
    (∀ α < M_ph, ∀ j ∈ B_bank,
      CoarseMonoOnInterval (z (some (some j))) (a α) (a (α + 1)) A)) ∧
  (∀ w : Fin k, w ∉ B_bank →
    ((Finset.Ico t_suf T).image (z (some (some w)))).card ≤ S) ∧
  (∀ t < t_suf, ∀ i ∈ R_suf,
    ¬ (((i.1 * (d * b) + E_pad : ℕ) : ℤ) ≤ z none t ∧
        z none t < (((i.1 + 1) * (d * b) : ℕ) : ℤ) - (E_pad : ℤ)))

/-- Sanity check: `TraceHasJitterBM` with `z (some none) 0 ≤ 0` is the `t_suf = 0, R_suf = univ,
E_pad = 0` specialization of `TraceHasSuffixJitterBM`. -/
theorem traceHasSuffixJitterBM_of_traceHasJitterBM {k : ℕ} {z : Tp k → ℕ → ℤ}
    (d b : ℕ) {T M_ph : ℕ} {B_bank : Finset (Fin k)} {A S : ℕ}
    (hz0 : z (some none) 0 ≤ 0)
    (hBM : TraceHasJitterBM z T M_ph B_bank A S) :
    TraceHasSuffixJitterBM z d b T 0 M_ph B_bank Finset.univ 0 A S := by
  obtain ⟨hph, hwork⟩ := hBM
  refine ⟨Nat.zero_le T, hz0, hph, ?_, ?_⟩
  · intro w hw
    simpa [Nat.Ico_zero_eq_range] using hwork w hw
  · intro t ht
    omega

/-- **Adaptive Suffix Jitter-BM machine class (`AdaptiveSuffixJitterBM`)**:
for all `d ≥ d_suf` (`b := entryBits d`, `L := d² b`), every input `X : Fin L → Bool` on which `M`
halts at `T ≤ C (L + 1)` admits an input-dependent suffix start `t_suf ≤ T` and untouched raw-row
set `R_suf ⊆ Fin d` with `|R_suf| ≥ δ₀ d` and
`TraceHasSuffixJitterBM (runWalks M (List.ofFn X)) d b T t_suf M_ph B_bank R_suf 0 (A d) (S d)`. -/
def AdaptiveSuffixJitterBM (M : TM) (C : ℝ) (M_ph : ℕ) (δ₀ : ℝ)
    (B_bank : Finset (Fin M.k)) (A S : ℕ → ℕ) : Prop :=
  ∃ d_suf : ℕ, ∀ d ≥ d_suf,
    let b := entryBits d
    let L := d * d * b
    ∀ (X : Fin L → Bool) (T : ℕ),
      Transpose.Tape.HaltsAt M (List.ofFn X) T →
      (T : ℝ) ≤ C * ((L : ℝ) + 1) →
      ∃ (t_suf : ℕ) (R_suf : Finset (Fin d)),
        δ₀ * (d : ℝ) ≤ (R_suf.card : ℝ) ∧
        TraceHasSuffixJitterBM (runWalks M (List.ofFn X)) d b T t_suf M_ph B_bank R_suf 0 (A d) (S d)

/-- Sanity check: `AdaptiveJitterBM` is the `δ₀ = 1` specialization of `AdaptiveSuffixJitterBM`. -/
theorem adaptiveSuffixJitterBM_of_adaptiveJitterBM {M : TM} {C : ℝ} {M_ph : ℕ}
    {B_bank : Finset (Fin M.k)} {A S : ℕ → ℕ}
    (hBM : AdaptiveJitterBM M C M_ph B_bank A S) :
    AdaptiveSuffixJitterBM M C M_ph 1 B_bank A S := by
  obtain ⟨d_BM, hd_BM⟩ := hBM
  refine ⟨d_BM, fun d hd X T hHalt hT => ?_⟩
  have hz0 : runWalks M (List.ofFn X) (some none) 0 ≤ 0 := by
    simp [runWalks, Transpose.Tape.Impl.run_zero, init]
  refine ⟨0, Finset.univ, by simp,
    traceHasSuffixJitterBM_of_traceHasJitterBM d (entryBits d) hz0 (hd_BM d hd X T hHalt hT)⟩

/-! ## §2. Suffix-Confined Intra-Phase Invariance & Coarse Signature Pullback -/

/-- Suffix version of `tcut_eq_of_intra_step`: replaces `longWorkHops` with
`longWorkHopsSuffix xs B_bank t_suf T τ_cut` whenever `t_suf ≤ lo ≤ v < u < hi`. -/
theorem tcut_eq_of_intra_step_suffix {k : ℕ} {xs : Fin k → ℕ → ℤ} {B_bank : Finset (Fin k)}
    {t_suf T τ_cut lo hi u v : ℕ} (hτ : 1 ≤ τ_cut) (pos : Bool) (θ : ℕ)
    (hstep : DepStep xs T u v) (ht_suf_lo : t_suf ≤ lo) (hv_lo : lo ≤ v) (hu_hi : u < hi)
    (hno_long : u ∉ longWorkHopsSuffix xs B_bank t_suf T τ_cut)
    (hno_win : u ∉ Finset.Icc θ (θ + τ_cut))
    (hno_strad : ∀ j ∈ B_bank, u ∉ intraStradGuard (xs j) T lo hi θ) :
    tcut pos θ u ↔ tcut pos θ v := by
  classical
  rcases hstep with ⟨hb, _⟩ | hhop_mem
  · exact tcut_eq_of_notMem_window (by omega) (by omega) hno_win
  · obtain ⟨⟨j, v', u'⟩, hη, heq⟩ := Finset.mem_image.mp hhop_mem
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    have hhop : IsHop (xs j) T v' u' := mem_allHops.mp hη
    have huv : v' < u' := by have := hhop.1; omega
    have huT : u' < T := hhop.2.1
    by_cases hj : j ∈ B_bank
    · have hnot := hno_strad j hj
      have hno_cross : ¬ (v' < θ ∧ θ ≤ u') := by
        intro ⟨hvθ, hθu⟩
        apply hnot
        unfold intraStradGuard
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr huT, by omega, hu_hi, hθu,
          v', hv_lo, hvθ, hhop⟩
      cases pos <;> simp only [tcut, ↓reduceIte, Bool.false_eq_true] <;> omega
    · have hshort : u' - v' ≤ τ_cut := by
        by_contra hgt
        apply hno_long
        unfold longWorkHopsSuffix
        exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, huT⟩, j, hj, v', hhop, by omega⟩
      exact tcut_eq_of_notMem_window huv.le (by omega) hno_win

/-- Suffix path-level `tcut` invariance along an intra-phase dependency path `t₀ :: π`. -/
theorem tcut_eq_along_intra_path_suffix {k : ℕ} {xs : Fin k → ℕ → ℤ} {B_bank : Finset (Fin k)}
    {t_suf T τ_cut lo hi : ℕ} (hτ : 1 ≤ τ_cut) (ht_suf_lo : t_suf ≤ lo) (pos : Bool) (θ : ℕ) :
    ∀ (π : List ℕ) (t₀ : ℕ),
      IsDepPath xs T (t₀ :: π) →
      (∀ x ∈ t₀ :: π, lo ≤ x ∧ x < hi ∧
        x ∉ longWorkHopsSuffix xs B_bank t_suf T τ_cut ∧
        x ∉ Finset.Icc θ (θ + τ_cut) ∧
        (∀ j ∈ B_bank, x ∉ intraStradGuard (xs j) T lo hi θ)) →
      (tcut pos θ t₀ ↔ tcut pos θ ((t₀ :: π).getLastD t₀))
  | [], _, _, _ => Iff.rfl
  | t₁ :: π₁, t₀, ⟨hstep, htail⟩, hall => by
    obtain ⟨_, ht₀_hi, hnl₀, hnw₀, hns₀⟩ := hall t₀ List.mem_cons_self
    obtain ⟨ht₁_lo, _, _, _, _⟩ := hall t₁ (List.mem_cons_of_mem t₀ List.mem_cons_self)
    have hedge := tcut_eq_of_intra_step_suffix hτ pos θ hstep ht_suf_lo ht₁_lo ht₀_hi hnl₀ hnw₀ hns₀
    have hih := tcut_eq_along_intra_path_suffix hτ ht_suf_lo pos θ π₁ t₁ htail
      (fun x hx => hall x (List.mem_cons_of_mem t₀ hx))
    rw [LinNet.getLastD_cons_cons]
    exact hedge.trans hih

/-- Suffix coarse phase splitting along a dependency path `t₀ :: ρ` with `a 0 ≤ (t₀ :: ρ).getLastD t₀`:
either the entire path stays inside `[a α, a (α + 1))`, or an intra-phase prefix `t₀ :: π_in` stays
inside `[a α, a (α + 1))` up to an inter-phase bank hop `u₁ → v₁` (`v₁ < a α`, `j ∈ B_bank`). -/
theorem depPath_coarse_phase_split_suffix {k : ℕ} {xs : Fin k → ℕ → ℤ} {T M_ph τ_cut : ℕ}
    (hτ : 1 ≤ τ_cut) {B_bank : Finset (Fin k)} {a : ℕ → ℕ}
    (haM : a M_ph = T) (ha : ∀ α < M_ph, a α ≤ a (α + 1)) :
    ∀ (ρ : List ℕ) (t₀ : ℕ), a 0 ≤ (t₀ :: ρ).getLastD t₀ → t₀ < T →
      IsDepPath xs T (t₀ :: ρ) →
      (∀ x ∈ t₀ :: ρ, x ∉ longWorkHopsSuffix xs B_bank (a 0) T τ_cut ∧
        x ∉ phaseStartGuard M_ph a τ_cut) →
      let α := phaseOf M_ph a t₀
      let t_last := (t₀ :: ρ).getLastD t₀
      (∀ x ∈ t₀ :: ρ, a α ≤ x ∧ x < a (α + 1)) ∨
      (∃ (π_in : List ℕ) (u₁ v₁ : ℕ) (ρ' : List ℕ) (j : B_bank),
        IsDepPath xs T (t₀ :: π_in) ∧
        (t₀ :: π_in).getLastD t₀ = u₁ ∧
        (∀ x ∈ t₀ :: π_in, a α ≤ x ∧ x < a (α + 1) ∧ x ∈ t₀ :: ρ) ∧
        v₁ < a α ∧ IsHop (xs j.1) T v₁ u₁ ∧
        IsDepPath xs T (v₁ :: ρ') ∧
        (v₁ :: ρ').getLastD v₁ = t_last ∧
        (∀ x ∈ v₁ :: ρ', x ∈ t₀ :: ρ))
  | [], t₀, hge, ht₀, _, _ => by
    have ht₀_ge : a 0 ≤ t₀ := by simpa using hge
    obtain ⟨_, hlo, hhi⟩ := phaseOf_spec_of_ge haM ht₀_ge ht₀
    left
    intro x hx
    simp only [List.mem_singleton] at hx
    subst hx
    exact ⟨hlo, hhi⟩
  | t₁ :: ρ₁, t₀, hge, ht₀, ⟨hstep, htail⟩, havoid => by
    classical
    have ht₀_ge : a 0 ≤ t₀ :=
      hge.trans (getLastD_le_of_mem_depPath (t₁ :: ρ₁) t₀ ⟨hstep, htail⟩ List.mem_cons_self)
    have hlast_eq : (t₀ :: t₁ :: ρ₁).getLastD t₀ = (t₁ :: ρ₁).getLastD t₁ :=
      LinNet.getLastD_cons_cons t₀ t₁ ρ₁
    have hge₁ : a 0 ≤ (t₁ :: ρ₁).getLastD t₁ := by rwa [← hlast_eq]
    have ht₁_ge : a 0 ≤ t₁ :=
      hge₁.trans (getLastD_le_of_mem_depPath ρ₁ t₁ htail List.mem_cons_self)
    obtain ⟨hlt10, _⟩ := depStep_lt hstep
    have ht₁ : t₁ < T := hlt10.trans ht₀
    obtain ⟨hαM, hlo0, hhi0⟩ := phaseOf_spec_of_ge haM ht₀_ge ht₀
    obtain ⟨hno_long, hno_guard⟩ := havoid t₀ List.mem_cons_self
    by_cases ht1_ge : a (phaseOf M_ph a t₀) ≤ t₁
    · have hph_eq : phaseOf M_ph a t₁ = phaseOf M_ph a t₀ :=
        (phaseOf_eq_iff_of_ge haM ha ht₁_ge ht₁ hαM).mpr ⟨ht1_ge, hlt10.trans hhi0⟩
      have havoid1 : ∀ x ∈ t₁ :: ρ₁, x ∉ longWorkHopsSuffix xs B_bank (a 0) T τ_cut ∧
          x ∉ phaseStartGuard M_ph a τ_cut :=
        fun x hx => havoid x (List.mem_cons_of_mem t₀ hx)
      rcases depPath_coarse_phase_split_suffix hτ haM ha ρ₁ t₁ hge₁ ht₁ htail havoid1 with
        hall1 | ⟨π_in, u₁, v₁, ρ', j, hdep_in, hlast_in, hall_in, hv_lt, hhop, hdep', hlast', hsub'⟩
      · left
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx1
        · exact ⟨hlo0, hhi0⟩
        · have h := hall1 x hx1
          rwa [hph_eq] at h
      · right
        rw [hph_eq] at hv_lt
        refine ⟨t₁ :: π_in, u₁, v₁, ρ', j, ⟨hstep, hdep_in⟩,
          (LinNet.getLastD_cons_cons t₀ t₁ π_in).trans hlast_in, ?_,
          hv_lt, hhop, hdep', hlast'.trans hlast_eq.symm,
          fun x hx => List.mem_cons_of_mem t₀ (hsub' x hx)⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx_in
        · exact ⟨hlo0, hhi0, List.mem_cons_self⟩
        · obtain ⟨h1, h2, h3⟩ := hall_in x hx_in
          rw [hph_eq] at h1 h2
          exact ⟨h1, h2, List.mem_cons_of_mem t₀ h3⟩
    · have ht0_guard : a (phaseOf M_ph a t₀) + τ_cut ≤ t₀ := by
        by_contra hlt_g
        apply hno_guard
        unfold phaseStartGuard
        exact Finset.mem_biUnion.mpr ⟨phaseOf M_ph a t₀, Finset.mem_range.mpr hαM,
          Finset.mem_Ico.mpr ⟨hlo0, by omega⟩⟩
      have hgap : τ_cut < t₀ - t₁ := by omega
      rcases hstep with ⟨hb, _⟩ | hhop_mem
      · omega
      · obtain ⟨⟨w, v, u⟩, hη, heq⟩ := Finset.mem_image.mp hhop_mem
        simp only [Prod.mk.injEq] at heq
        have hhop : IsHop (xs w) T t₁ t₀ := heq.2 ▸ heq.1 ▸ mem_allHops.mp hη
        by_cases hw : w ∈ B_bank
        · right
          refine ⟨[], t₀, t₁, ρ₁, ⟨w, hw⟩, trivial, rfl, ?_, by omega, hhop, htail,
            hlast_eq.symm, fun x hx => List.mem_cons_of_mem t₀ hx⟩
          intro x hx
          simp only [List.mem_singleton] at hx
          subst hx
          exact ⟨hlo0, hhi0, List.mem_cons_self⟩
        · exfalso
          apply hno_long
          unfold longWorkHopsSuffix
          exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨ht₀_ge, ht₀⟩, w, hw, t₁, hhop, hgap⟩

private theorem getLastD_cons_mem_local : ∀ (ρ : List ℕ) (t₀ : ℕ),
    (t₀ :: ρ).getLastD t₀ ∈ t₀ :: ρ
  | [], _ => List.mem_cons_self
  | t₁ :: ρ₁, t₀ => by
    rw [LinNet.getLastD_cons_cons]
    exact List.mem_cons_of_mem t₀ (getLastD_cons_mem_local ρ₁ t₁)

/-- Suffix coarse signature pullback theorem: every dependency path `t₀ :: ρ` satisfying
`a 0 ≤ (t₀ :: ρ).getLastD t₀`, avoiding `longWorkHopsSuffix ∪ phaseStartGuard`, and ending at
`x_in t_last = q` admits a single signature `s : SigAt B_bank α` that simultaneously pulls back
every threshold `pStar` whose `coarseGuardsOf` the path avoids and whose `[pStar, pStar + A)` band
`q` avoids. -/
theorem depPath_coarse_signature_exists_suffix {k : ℕ} {x_in : ℕ → ℤ} {xs : Fin k → ℕ → ℤ}
    {T M_ph τ_cut A : ℕ} (hτ : 1 ≤ τ_cut) {B_bank : Finset (Fin k)} {a : ℕ → ℕ}
    (haM : a M_ph = T) (ha : ∀ α < M_ph, a α ≤ a (α + 1))
    (hin : ∀ α < M_ph, CoarseMonoOnInterval x_in (a α) (a (α + 1)) A) :
    ∀ (α : ℕ), α < M_ph →
      ∀ {t₀ : ℕ} (_ht₀ : t₀ < T) (_hα : phaseOf M_ph a t₀ = α)
        {ρ : List ℕ} (_hge : a 0 ≤ (t₀ :: ρ).getLastD t₀)
        (_hdep : IsDepPath xs T (t₀ :: ρ))
        (_havoid : ∀ x ∈ t₀ :: ρ, x ∉ longWorkHopsSuffix xs B_bank (a 0) T τ_cut ∧
          x ∉ phaseStartGuard M_ph a τ_cut)
        {q : ℕ} (_hrd : x_in ((t₀ :: ρ).getLastD t₀) = (q : ℤ)),
        ∃ s : SigAt B_bank α, ∀ pStar : ℕ,
          ¬ (pStar ≤ q ∧ q < pStar + A) →
          (∀ x ∈ t₀ :: ρ, x ∉ coarseGuardsOf x_in xs T τ_cut A B_bank a α (liftSig s) pStar) →
          (tcut (coarseCutOf x_in xs T A B_bank a α (liftSig s) pStar).1
            (coarseCutOf x_in xs T A B_bank a α (liftSig s) pStar).2 t₀ ↔ q < pStar) := by
  intro α
  induction α using Nat.strong_induction_on with
  | h α ih =>
    intro hαM t₀ ht₀ hα ρ hge hdep havoid q hrd
    subst hα
    let α := phaseOf M_ph a t₀
    have ha0_le_aα : a 0 ≤ a α := phase_le_of_step ha (Nat.zero_le α) (by omega)
    rcases depPath_coarse_phase_split_suffix (B_bank := B_bank) hτ haM ha ρ t₀ hge ht₀
        hdep havoid with
      hall_in | ⟨π_in, u₁, v₁, ρ', j, hdep_in, hlast_in, hall_in, hv_lt, hhop, hdep', hlast', hsub'⟩
    · -- Base case: entire path remains inside `[a α, a (α + 1))`.
      let s₀ : SigAt B_bank α := fun _ => none
      refine ⟨s₀, fun pStar hnoband hnogrd => ?_⟩
      let c := coarseCutOf x_in xs T A B_bank a α (liftSig s₀) pStar
      have hself := mem_coarseGuardsOf_self x_in xs T τ_cut A B_bank a α (liftSig s₀) pStar
      have hintra := tcut_eq_along_intra_path_suffix (xs := xs) (B_bank := B_bank) (lo := a α)
        (hi := a (α + 1)) hτ ha0_le_aα c.1 c.2 ρ t₀ hdep fun x hx => by
          obtain ⟨hlo, hhi⟩ := hall_in x hx
          obtain ⟨hnl, _⟩ := havoid x hx
          have hng : x ∉ phaseIntraGuard xs T τ_cut B_bank a α c.2 :=
            fun hm => hnogrd x hx (hself hm)
          refine ⟨hlo, hhi, hnl, fun hw => hng (Finset.mem_union_left _ hw),
            fun j' hj' hs => hng (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j', hj', hs⟩))⟩
      let t_m := (t₀ :: ρ).getLastD t₀
      have htm_mem : t_m ∈ t₀ :: ρ := getLastD_cons_mem_local ρ t₀
      obtain ⟨htm_lo, htm_hi⟩ := hall_in t_m htm_mem
      have hhiT : a (α + 1) ≤ T := haM ▸ phase_le_of_step ha (by omega) le_rfl
      have hpull := coarsePullRead_spec hhiT (hin α hαM) htm_lo htm_hi hrd hnoband
      rw [← coarseCutOf_none x_in xs T A B_bank a α pStar] at hpull
      exact hintra.trans hpull
    · -- Inductive step: intra-phase prefix `t₀ :: π_in` followed by `u₁ → v₁` into `α' < α`.
      have hvT : v₁ < T := hv_lt.trans_le (haM ▸ phase_le_of_step ha (by omega) (by omega))
      have hge' : a 0 ≤ (v₁ :: ρ').getLastD v₁ := by rwa [hlast']
      have hv_ge : a 0 ≤ v₁ :=
        hge'.trans (getLastD_le_of_mem_depPath ρ' v₁ hdep' List.mem_cons_self)
      let α' := phaseOf M_ph a v₁
      obtain ⟨hα'M, hlo', hhi'⟩ := phaseOf_spec_of_ge haM hv_ge hvT
      have hlt_ph : α' < α := by
        by_contra hge_ph
        have hstep_le := phase_le_of_step ha (α := α) (β := α') (by omega) (by omega)
        dsimp only [α', α] at hstep_le hv_lt hlo'
        omega
      have havoid' : ∀ x ∈ v₁ :: ρ', x ∉ longWorkHopsSuffix xs B_bank (a 0) T τ_cut ∧
          x ∉ phaseStartGuard M_ph a τ_cut := fun x hx => havoid x (hsub' x hx)
      have hrd' : x_in ((v₁ :: ρ').getLastD v₁) = (q : ℤ) := by rw [hlast']; exact hrd
      obtain ⟨s', hs'⟩ := ih α' hlt_ph hα'M hvT rfl hge' hdep' havoid' hrd'
      refine ⟨consSig hlt_ph j s', fun pStar hnoband hnogrd => ?_⟩
      obtain ⟨hcut_cons, hinter_sub, htail_sub⟩ :=
        coarseCutOf_consSig x_in xs T τ_cut A B_bank a hlt_ph j s' pStar
      have hnogrd' : ∀ x ∈ v₁ :: ρ',
          x ∉ coarseGuardsOf x_in xs T τ_cut A B_bank a α' (liftSig s') pStar :=
        fun x hx hm => hnogrd x (hsub' x hx) (htail_sub hm)
      have ih_eq := hs' pStar hnoband hnogrd'
      let c := coarseCutOf x_in xs T A B_bank a α (liftSig (consSig hlt_ph j s')) pStar
      have hself := mem_coarseGuardsOf_self x_in xs T τ_cut A B_bank a α
        (liftSig (consSig hlt_ph j s')) pStar
      have hintra := tcut_eq_along_intra_path_suffix (xs := xs) (B_bank := B_bank) (lo := a α)
        (hi := a (α + 1)) hτ ha0_le_aα c.1 c.2 π_in t₀ hdep_in fun x hx => by
          obtain ⟨hlo, hhi, hx_full⟩ := hall_in x hx
          obtain ⟨hnl, _⟩ := havoid x hx_full
          have hng : x ∉ phaseIntraGuard xs T τ_cut B_bank a α c.2 :=
            fun hm => hnogrd x hx_full (hself hm)
          refine ⟨hlo, hhi, hnl, fun hw => hng (Finset.mem_union_left _ hw),
            fun j' hj' hs => hng (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j', hj', hs⟩))⟩
      rw [hlast_in] at hintra
      have hu₁_in : u₁ ∈ t₀ :: π_in := hlast_in ▸ getLastD_cons_mem_local π_in t₀
      obtain ⟨hu_lo, hu_hi, hu_full⟩ := hall_in u₁ hu₁_in
      have hR : BankInterRel (xs j.1) T (a α') (a (α' + 1)) (a α) (a (α + 1)) u₁ v₁ :=
        ⟨hu_lo, hu_hi, hlo', hhi', hhop⟩
      have hu₁_not_inter : u₁ ∉ interBankGuard (xs j.1) T (a α') (a (α' + 1)) (a α) (a (α + 1)) A
          (coarseCutOf x_in xs T A B_bank a α' (liftSig s') pStar) :=
        fun hm => hnogrd u₁ hu_full (hinter_sub hm)
      have hpull := interBankPull_spec hR hu₁_not_inter
      rw [← hcut_cons] at hpull
      exact hintra.trans (hpull.trans ih_eq)

/-! ## §3. Single-Trace Suffix + Jitter Independent Set & Storage-Code Deficit -/

/-- **Suffix Jitter-BM Independent Set (`suffixJitterBM_independent_exists`)**: explicit finite independent set in
`MergeDepth.coneRel 1 z T Γ ot (fun q => MergeDepth.tpos d b q)` for any single frozen walk tuple
satisfying `TraceHasSuffixJitterBM`. -/
theorem suffixJitterBM_independent_exists {k M_ph D d b T t_suf E_pad A S_val : ℕ}
    (hMph : 1 ≤ M_ph) (hd : 1 ≤ d) (hb : 1 ≤ b)
    {z : Tp k → ℕ → ℤ} {B_bank : Finset (Fin k)} {R_suf : Finset (Fin d)}
    {Γ : Finset ℕ} {ot : ℕ → ℕ}
    (hout_mono : ∀ t₁ t₂, t₁ ≤ t₂ → z (some none) t₁ ≤ z (some none) t₂)
    (hdepth : ∀ π, IsDepPath (fun j => skel 1 (z (some (some j)))) T π → LinNet.GFree Γ π →
      π.length ≤ D + 1)
    (hot : ∀ q : Fin (d * d * b),
      ot (MergeDepth.tpos d b q) < T ∧
        (MergeDepth.tpos d b q : ℤ) / (1 : ℕ) =
          z (some none) (ot (MergeDepth.tpos d b q)) / (1 : ℕ))
    (hBM : TraceHasSuffixJitterBM z d b T t_suf M_ph B_bank R_suf E_pad A S_val) :
    let K₀ := (B_bank.card + 1) ^ (M_ph - 1)
    let B := 2 * K₀
    let τ_cut := Nat.sqrt (max 1 S_val * (T + 1)) + 1
    let C_split := (M_ph + 2) + M_ph * (K₀ * B)
    let C_cone := (k + 2) ^ D * (k + M_ph + M_ph * (K₀ * (B * (M_ph * (2 * k + 3)))))
    ∃ S_ind : Finset (Fin (d * d * b)),
      DirectedRecovery.IsIndependent
        (MergeDepth.coneRel 1 z T Γ ot (fun q => MergeDepth.tpos d b q)) S_ind ∧
      (R_suf.card / B) * ((d - C_split) / 2) * b ≤
        S_ind.card + C_cone * (τ_cut + A + 1) + B * A + 2 * d * E_pad := by
  dsimp only
  classical
  set L := d * d * b
  set W := d * b
  have hW : 1 ≤ W := Nat.mul_pos hd hb
  set K₀ := (B_bank.card + 1) ^ (M_ph - 1)
  have hK₀ : 1 ≤ K₀ := Nat.one_le_pow _ _ (by omega)
  set B := 2 * K₀
  have hB2 : 2 ≤ B := by omega
  have hB0 : 0 < B := by omega
  set τ_cut := Nat.sqrt (max 1 S_val * (T + 1)) + 1
  have hτ : 1 ≤ τ_cut := by omega
  set C_split := (M_ph + 2) + M_ph * (K₀ * B)
  set C_cone := (k + 2) ^ D * (k + M_ph + M_ph * (K₀ * (B * (M_ph * (2 * k + 3)))))
  -- Degenerate small-`R_suf` guard: when `R_suf.card < B`, `R_suf.card / B = 0`.
  by_cases hNB : R_suf.card < B
  · refine ⟨∅, ?_, ?_⟩
    · intro q hq
      exact False.elim (Finset.notMem_empty q hq)
    · rw [Nat.div_eq_of_lt hNB, Nat.zero_mul, Nat.zero_mul]
      exact Nat.zero_le _
  have hBN : B ≤ R_suf.card := Nat.le_of_not_lt hNB
  set N := R_suf.card
  have hN_pos : 0 < N := by omega
  let x_in : ℕ → ℤ := z none
  let xs : Fin k → ℕ → ℤ := fun j => z (some (some j))
  have hskel_eq : (fun j : Fin k => skel (1 : ℤ) (z (some (some j)))) = xs := by
    funext j t
    exact Int.ediv_one _
  obtain ⟨_, hout_suf, ⟨a, ha0, haM, ha, hin, hbank⟩, hwork, hno_pre⟩ := hBM
  have hot_point : ∀ r (hr : r < L), ot r < T ∧ z (some none) (ot r) = (r : ℤ) := by
    intro r hr
    let q_r : Fin L := tposOf d b ⟨r, hr⟩
    have htpos_eq : MergeDepth.tpos d b q_r = r := by
      rw [← tape_tpos_eq, ← tposOf_val]
      exact congrArg Fin.val (tposOf_tposOf d b ⟨r, hr⟩)
    obtain ⟨h1, h2⟩ := hot q_r
    rw [htpos_eq] at h1 h2
    simp only [Nat.cast_one, Int.ediv_one] at h2
    exact ⟨h1, h2.symm⟩
  obtain ⟨hot_lt, hot_strict⟩ := ot_strictMonoOn_of_coneRel1 hout_mono hot
  have hot_mono : ∀ {x y : ℕ}, x ≤ y → y < L → ot x ≤ ot y := by
    intro x y hxy hyL
    rcases eq_or_lt_of_le hxy with rfl | hlt
    · exact le_rfl
    · exact (hot_strict x y hlt hyL).le
  have hot_ge_a0 : ∀ r, 1 ≤ r → r < L → a 0 ≤ ot r := by
    intro r hr1 hrL
    rw [ha0]
    have hval := (hot_point r hrL).2
    by_contra hlt_suf
    have hle := hout_mono (ot r) t_suf (by omega)
    omega
  -- Order-quantile buckets and raw bit thresholds on `R_suf`.
  let e : Fin N ≃o R_suf := R_suf.orderIsoOfFin rfl
  let idxBucket : Fin B → Finset (Fin N) := fun c =>
    Finset.univ.filter fun m : Fin N => c.1 * N / B ≤ m.1 ∧ m.1 < (c.1 + 1) * N / B
  let bucketR : Fin B → Finset (Fin d) := fun c =>
    (idxBucket c).image fun m => (e m).1
  have hbucket_sub : ∀ c : Fin B, bucketR c ⊆ R_suf := by
    intro c u hu
    obtain ⟨m, -, rfl⟩ := Finset.mem_image.mp hu
    exact (e m).2
  have hbucket_card : ∀ c : Fin B, N / B ≤ (bucketR c).card := by
    intro c
    have hinj : Function.Injective (fun m : Fin N => (e m).1) :=
      Subtype.val_injective.comp e.injective
    calc N / B ≤ (idxBucket c).card := bucketR_card_ge (d := N) hB0 c
      _ = (bucketR c).card := (Finset.card_image_of_injective _ hinj).symm
  have hthresh_lt : ∀ m : Fin (B - 1), (m.1 + 1) * N / B < N := by
    intro m
    rw [Nat.div_lt_iff_lt_mul hB0, Nat.mul_comm N B]
    exact Nat.mul_lt_mul_of_pos_right (by omega) hN_pos
  let kThresh : Fin (B - 1) → Fin N := fun m => ⟨(m.1 + 1) * N / B, hthresh_lt m⟩
  let rThresh : Fin (B - 1) → ℕ := fun m => (e (kThresh m)).1.1
  let pThresh : Fin (B - 1) → ℕ := fun m => rThresh m * W
  let P_set : Finset ℕ := (Finset.univ : Finset (Fin (B - 1))).image pThresh
  have hP_card : P_set.card ≤ B := by
    calc P_set.card ≤ (Finset.univ : Finset (Fin (B - 1))).card := Finset.card_image_le
      _ = B - 1 := by simp
      _ ≤ B := Nat.sub_le B 1
  have hSig_card : ∀ α < M_ph, (Finset.univ : Finset (SigAt B_bank α)).card ≤ K₀ := by
    intro α hα
    rw [Finset.card_univ, card_sigAt]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  -- Assemble suffix `X_bad` and bound `(ancestors xs T X_bad D).card`.
  let U_long := longWorkHopsSuffix xs B_bank (a 0) T τ_cut
  let A_start := phaseStartGuard M_ph a τ_cut
  let W_all : Finset ℕ :=
    (Finset.range M_ph).biUnion fun α =>
      (Finset.univ : Finset (SigAt B_bank α)).biUnion fun s =>
        P_set.biUnion fun pStar =>
          coarseGuardsOf x_in xs T τ_cut A B_bank a α (liftSig s) pStar
  let X_bad : Finset ℕ := U_long ∪ A_start ∪ W_all
  have hwork_a0 : ∀ w : Fin k, w ∉ B_bank →
      ((Finset.Ico (a 0) T).image (xs w)).card ≤ S_val := by
    rwa [ha0]
  have hU_long_card : U_long.card ≤ k * τ_cut := by
    have h1 := card_longWorkHopsSuffix_le xs B_bank (a 0) T τ_cut S_val hτ hwork_a0
    have hsq : S_val * (T / τ_cut) ≤ τ_cut := by
      have hdiv_le : S_val * (T / τ_cut) * τ_cut ≤ max 1 S_val * (T + 1) := by
        calc S_val * (T / τ_cut) * τ_cut
            = S_val * ((T / τ_cut) * τ_cut) := by ring
          _ ≤ S_val * T := Nat.mul_le_mul_left _ (Nat.div_mul_le_self T τ_cut)
          _ ≤ max 1 S_val * (T + 1) := Nat.mul_le_mul (le_max_right 1 S_val) (by omega)
      have hlt_sq : max 1 S_val * (T + 1) < τ_cut * τ_cut := Nat.lt_succ_sqrt _
      by_contra hgt
      have : τ_cut * τ_cut ≤ S_val * (T / τ_cut) * τ_cut := Nat.mul_le_mul_right τ_cut (by omega)
      omega
    exact h1.trans (Nat.mul_le_mul_left k hsq)
  have hA_start_card : A_start.card ≤ M_ph * τ_cut := card_phaseStartGuard_le M_ph a τ_cut
  have hW_all_card :
      W_all.card ≤ M_ph * (K₀ * (B * (M_ph * ((2 * k + 3) * (τ_cut + A + 1))))) := by
    calc W_all.card
        ≤ ∑ α ∈ Finset.range M_ph,
            ((Finset.univ : Finset (SigAt B_bank α)).biUnion fun s =>
              P_set.biUnion fun pStar =>
                coarseGuardsOf x_in xs T τ_cut A B_bank a α (liftSig s) pStar).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _α ∈ Finset.range M_ph,
            (K₀ * (B * (M_ph * ((2 * k + 3) * (τ_cut + A + 1))))) := by
          refine Finset.sum_le_sum fun α hα => ?_
          have hαM : α < M_ph := Finset.mem_range.mp hα
          calc _ ≤ ∑ s ∈ (Finset.univ : Finset (SigAt B_bank α)),
                  (P_set.biUnion fun pStar =>
                    coarseGuardsOf x_in xs T τ_cut A B_bank a α (liftSig s) pStar).card :=
                Finset.card_biUnion_le
            _ ≤ ∑ _s ∈ (Finset.univ : Finset (SigAt B_bank α)),
                  (B * (M_ph * ((2 * k + 3) * (τ_cut + A + 1)))) := by
                refine Finset.sum_le_sum fun s _ => ?_
                calc _ ≤ ∑ pStar ∈ P_set,
                        (coarseGuardsOf x_in xs T τ_cut A B_bank a α (liftSig s) pStar).card :=
                      Finset.card_biUnion_le
                  _ ≤ ∑ _pStar ∈ P_set, (M_ph * ((2 * k + 3) * (τ_cut + A + 1))) := by
                      refine Finset.sum_le_sum fun pStar _ => ?_
                      exact (card_coarseGuardsOf_le x_in xs T τ_cut A M_ph B_bank ha hbank hαM
                        (liftSig s) pStar).trans (Nat.mul_le_mul_right _ (by omega))
                  _ = P_set.card * (M_ph * ((2 * k + 3) * (τ_cut + A + 1))) := by simp
                  _ ≤ B * (M_ph * ((2 * k + 3) * (τ_cut + A + 1))) :=
                      Nat.mul_le_mul_right _ hP_card
            _ = (Finset.univ : Finset (SigAt B_bank α)).card *
                  (B * (M_ph * ((2 * k + 3) * (τ_cut + A + 1)))) := by simp
            _ ≤ K₀ * (B * (M_ph * ((2 * k + 3) * (τ_cut + A + 1)))) :=
                Nat.mul_le_mul_right _ (hSig_card α hαM)
      _ = M_ph * (K₀ * (B * (M_ph * ((2 * k + 3) * (τ_cut + A + 1))))) := by simp
  have hX_bad : X_bad.card ≤
      (k + M_ph + M_ph * (K₀ * (B * (M_ph * (2 * k + 3))))) * (τ_cut + A + 1) := by
    have hu1 : X_bad.card ≤ U_long.card + A_start.card + W_all.card := by
      calc (U_long ∪ A_start ∪ W_all).card
          ≤ (U_long ∪ A_start).card + W_all.card := Finset.card_union_le _ _
        _ ≤ U_long.card + A_start.card + W_all.card :=
          Nat.add_le_add_right (Finset.card_union_le _ _) _
    calc X_bad.card
        ≤ k * τ_cut + M_ph * τ_cut +
            M_ph * (K₀ * (B * (M_ph * ((2 * k + 3) * (τ_cut + A + 1))))) := by omega
      _ ≤ k * (τ_cut + A + 1) + M_ph * (τ_cut + A + 1) +
            M_ph * (K₀ * (B * (M_ph * (2 * k + 3)))) * (τ_cut + A + 1) := by
          have h1 : k * τ_cut ≤ k * (τ_cut + A + 1) := Nat.mul_le_mul_left k (by omega)
          have h2 : M_ph * τ_cut ≤ M_ph * (τ_cut + A + 1) := Nat.mul_le_mul_left M_ph (by omega)
          have h3 : M_ph * (K₀ * (B * (M_ph * ((2 * k + 3) * (τ_cut + A + 1))))) =
              M_ph * (K₀ * (B * (M_ph * (2 * k + 3)))) * (τ_cut + A + 1) := by ring
          omega
      _ = (k + M_ph + M_ph * (K₀ * (B * (M_ph * (2 * k + 3))))) * (τ_cut + A + 1) := by ring
  let Anc := ancestors xs T X_bad D
  let Z_cone : Finset (Fin L) := Finset.univ.filter fun q => ot (MergeDepth.tpos d b q) ∈ Anc
  have hZ_cone_card : Z_cone.card ≤ C_cone * (τ_cut + A + 1) := by
    let f : Fin L → ℕ := fun q => ot (MergeDepth.tpos d b q)
    have hinj : Set.InjOn f (Z_cone : Set (Fin L)) := by
      intro q₁ _ q₂ _ heq
      have ht₁ : MergeDepth.tpos d b q₁ = (tposOf d b q₁).1 := by rw [← tape_tpos_eq, ← tposOf_val]
      have ht₂ : MergeDepth.tpos d b q₂ = (tposOf d b q₂).1 := by rw [← tape_tpos_eq, ← tposOf_val]
      have hlt₁ : (tposOf d b q₁).1 < L := (tposOf d b q₁).2
      have hlt₂ : (tposOf d b q₂).1 < L := (tposOf d b q₂).2
      have hval_eq : (tposOf d b q₁).1 = (tposOf d b q₂).1 := by
        dsimp [f] at heq
        rw [ht₁, ht₂] at heq
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · exact absurd heq (hot_strict _ _ hlt hlt₂).ne
        · exact absurd heq.symm (hot_strict _ _ hgt hlt₁).ne
      have htp_eq : tposOf d b q₁ = tposOf d b q₂ := Fin.ext hval_eq
      calc q₁ = tposOf d b (tposOf d b q₁) := (tposOf_tposOf d b q₁).symm
        _ = tposOf d b (tposOf d b q₂) := by rw [htp_eq]
        _ = q₂ := tposOf_tposOf d b q₂
    have hsub : Z_cone.image f ⊆ Anc := by
      intro t ht
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp ht
      exact (Finset.mem_filter.mp hq).2
    calc Z_cone.card
        = (Z_cone.image f).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ Anc.card := Finset.card_le_card hsub
      _ ≤ (k + 2) ^ D * X_bad.card := card_ancestors_le xs T X_bad D
      _ ≤ (k + 2) ^ D *
            ((k + M_ph + M_ph * (K₀ * (B * (M_ph * (2 * k + 3))))) * (τ_cut + A + 1)) :=
          Nat.mul_le_mul_left _ hX_bad
      _ = C_cone * (τ_cut + A + 1) := by dsimp [C_cone]; ring
  -- Raw threshold-band coordinate guard `Z_in` of size `≤ B * A`.
  let Z_in : Finset (Fin L) :=
    P_set.biUnion fun pStar => Finset.univ.filter fun p : Fin L => pStar ≤ p.1 ∧ p.1 < pStar + A
  have hZ_in_card : Z_in.card ≤ B * A := by
    have hband : ∀ pStar : ℕ,
        (Finset.univ.filter fun p : Fin L => pStar ≤ p.1 ∧ p.1 < pStar + A).card ≤ A := by
      intro pStar
      let S_p := Finset.univ.filter fun p : Fin L => pStar ≤ p.1 ∧ p.1 < pStar + A
      have hinj : Set.InjOn (fun p : Fin L => p.1 - pStar) (S_p : Set (Fin L)) := by
        intro p₁ hp₁ p₂ hp₂ heq
        have h1 := (Finset.mem_filter.mp (Finset.mem_coe.mp hp₁)).2.1
        have h2 := (Finset.mem_filter.mp (Finset.mem_coe.mp hp₂)).2.1
        exact Fin.ext (by dsimp at heq; omega)
      have hsub : S_p.image (fun p : Fin L => p.1 - pStar) ⊆ Finset.range A := by
        intro r hr
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hr
        have h := (Finset.mem_filter.mp hp).2
        exact Finset.mem_range.mpr (by omega)
      calc S_p.card
          = (S_p.image fun p : Fin L => p.1 - pStar).card := (Finset.card_image_of_injOn hinj).symm
        _ ≤ (Finset.range A).card := Finset.card_le_card hsub
        _ = A := Finset.card_range A
    calc Z_in.card
        ≤ ∑ pStar ∈ P_set,
            (Finset.univ.filter fun p : Fin L => pStar ≤ p.1 ∧ p.1 < pStar + A).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _pStar ∈ P_set, A := Finset.sum_le_sum fun pStar _ => hband pStar
      _ = P_set.card * A := by simp
      _ ≤ B * A := Nat.mul_le_mul_right A hP_card
  -- Row-margin coordinate guard `Z_pad` of size `≤ 2 * d * E_pad`.
  let Z_pad_lo : Finset (Fin L) := Finset.univ.filter fun p : Fin L => p.1 % W < E_pad
  let Z_pad_hi : Finset (Fin L) := Finset.univ.filter fun p : Fin L => W - E_pad ≤ p.1 % W
  let Z_pad : Finset (Fin L) :=
    Finset.univ.filter fun p : Fin L => p.1 % W < E_pad ∨ W - E_pad ≤ p.1 % W
  have hdivW_lt : ∀ p : Fin L, p.1 / W < d := by
    intro p
    rw [Nat.div_lt_iff_lt_mul hW, Nat.mul_comm d W]
    have hpL : p.1 < d * d * b := p.2
    have hLW : d * d * b = W * d := by dsimp [W]; ring
    omega
  have hZ_pad_card : Z_pad.card ≤ 2 * d * E_pad := by
    let box_pad : Finset (ℕ × ℕ) := Finset.range d ×ˢ Finset.range E_pad
    have hbox_card : box_pad.card = d * E_pad := by simp [box_pad]
    have hlo_card : Z_pad_lo.card ≤ d * E_pad := by
      let φ : Fin L → ℕ × ℕ := fun p => (p.1 / W, p.1 % W)
      have hφ_inj : Set.InjOn φ (Z_pad_lo : Set (Fin L)) := by
        intro p₁ _ p₂ _ heq
        dsimp [φ] at heq
        obtain ⟨hd_eq, hm_eq⟩ := Prod.mk.inj heq
        have h1 := Nat.div_add_mod p₁.1 W
        have h2 := Nat.div_add_mod p₂.1 W
        exact Fin.ext (by rw [← h1, ← h2, hd_eq, hm_eq])
      have hφ_sub : Z_pad_lo.image φ ⊆ box_pad := by
        intro pair hpair
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hpair
        have hmod := (Finset.mem_filter.mp hp).2
        exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (hdivW_lt p), Finset.mem_range.mpr hmod⟩
      calc Z_pad_lo.card
          = (Z_pad_lo.image φ).card := (Finset.card_image_of_injOn hφ_inj).symm
        _ ≤ box_pad.card := Finset.card_le_card hφ_sub
        _ = d * E_pad := hbox_card
    have hhi_card : Z_pad_hi.card ≤ d * E_pad := by
      let ψ : Fin L → ℕ × ℕ := fun p => (p.1 / W, p.1 % W - (W - E_pad))
      have hψ_inj : Set.InjOn ψ (Z_pad_hi : Set (Fin L)) := by
        intro p₁ hp₁ p₂ hp₂ heq
        dsimp [ψ] at heq
        obtain ⟨hd_eq, hm_eq⟩ := Prod.mk.inj heq
        have hg₁ := (Finset.mem_filter.mp (Finset.mem_coe.mp hp₁)).2
        have hg₂ := (Finset.mem_filter.mp (Finset.mem_coe.mp hp₂)).2
        have hm12 : p₁.1 % W = p₂.1 % W := by omega
        have h1 := Nat.div_add_mod p₁.1 W
        have h2 := Nat.div_add_mod p₂.1 W
        exact Fin.ext (by rw [← h1, ← h2, hd_eq, hm12])
      have hψ_sub : Z_pad_hi.image ψ ⊆ box_pad := by
        intro pair hpair
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hpair
        have hge := (Finset.mem_filter.mp hp).2
        have hltW : p.1 % W < W := Nat.mod_lt p.1 hW
        dsimp [ψ]
        exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (hdivW_lt p),
          Finset.mem_range.mpr (by omega)⟩
      calc Z_pad_hi.card
          = (Z_pad_hi.image ψ).card := (Finset.card_image_of_injOn hψ_inj).symm
        _ ≤ box_pad.card := Finset.card_le_card hψ_sub
        _ = d * E_pad := hbox_card
    have hsub_u : Z_pad ⊆ Z_pad_lo ∪ Z_pad_hi := by
      intro p hp
      rcases (Finset.mem_filter.mp hp).2 with h1 | h2
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩)
    calc Z_pad.card
        ≤ (Z_pad_lo ∪ Z_pad_hi).card := Finset.card_le_card hsub_u
      _ ≤ Z_pad_lo.card + Z_pad_hi.card := Finset.card_union_le _ _
      _ ≤ d * E_pad + d * E_pad := Nat.add_le_add hlo_card hhi_card
      _ = 2 * d * E_pad := by ring
  -- Unsplit output rows (`Step 4`), explicitly excluding output row `0` (`⟨0, hd⟩`).
  let loOut : Fin d → ℕ := fun j => j.1 * W
  let hiOut : Fin d → ℕ := fun j => (j.1 + 1) * W - 1
  have hlo_hi_lt : ∀ j : Fin d, loOut j ≤ hiOut j ∧ hiOut j < L := by
    intro j
    have h1 : j.1 * W + 1 ≤ (j.1 + 1) * W := by rw [Nat.add_mul, Nat.one_mul]; omega
    have h2 : (j.1 + 1) * W ≤ L := by
      show (j.1 + 1) * (d * b) ≤ d * d * b
      calc (j.1 + 1) * (d * b) ≤ d * (d * b) := Nat.mul_le_mul_right _ (by omega)
        _ = d * d * b := by ring
    exact ⟨by dsimp [loOut, hiOut]; omega, by dsimp [hiOut]; omega⟩
  let SplitsRow : ℕ → Fin d → Prop := fun θ j => ot (loOut j) < θ ∧ θ ≤ ot (hiOut j)
  have hSplits_le_one : ∀ θ : ℕ, ((Finset.univ : Finset (Fin d)).filter (SplitsRow θ)).card ≤ 1 := by
    intro θ
    refine Finset.card_le_one.mpr fun j₁ hj₁ j₂ hj₂ => ?_
    have hs1 := (Finset.mem_filter.mp hj₁).2
    have hs2 := (Finset.mem_filter.mp hj₂).2
    by_contra hne
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
    · have hlt_idx : hiOut j₁ < loOut j₂ := by
        dsimp [loOut, hiOut]
        have h1 : (j₁.1 + 1) * W ≤ j₂.1 * W := Nat.mul_le_mul_right W (by omega)
        have h2 : 1 ≤ (j₁.1 + 1) * W := Nat.mul_pos (by omega) hW
        omega
      have hlt_ot := hot_strict _ _ hlt_idx ((hlo_hi_lt j₂).1.trans_lt (hlo_hi_lt j₂).2)
      omega
    · have hlt_idx : hiOut j₂ < loOut j₁ := by
        dsimp [loOut, hiOut]
        have h1 : (j₂.1 + 1) * W ≤ j₁.1 * W := Nat.mul_le_mul_right W (by omega)
        have h2 : 1 ≤ (j₂.1 + 1) * W := Nat.mul_pos (by omega) hW
        omega
      have hlt_ot := hot_strict _ _ hlt_idx ((hlo_hi_lt j₁).1.trans_lt (hlo_hi_lt j₁).2)
      omega
  let Θ_cuts : Finset ℕ :=
    (Finset.range M_ph).biUnion fun α =>
      (Finset.univ : Finset (SigAt B_bank α)).biUnion fun s =>
        P_set.image fun pStar => (coarseCutOf x_in xs T A B_bank a α (liftSig s) pStar).2
  have hΘ_cuts_card : Θ_cuts.card ≤ M_ph * (K₀ * B) := by
    calc Θ_cuts.card
        ≤ ∑ α ∈ Finset.range M_ph,
            ((Finset.univ : Finset (SigAt B_bank α)).biUnion fun s =>
              P_set.image fun pStar =>
                (coarseCutOf x_in xs T A B_bank a α (liftSig s) pStar).2).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _α ∈ Finset.range M_ph, (K₀ * B) := by
          refine Finset.sum_le_sum fun α hα => ?_
          have hαM : α < M_ph := Finset.mem_range.mp hα
          calc _ ≤ ∑ s ∈ (Finset.univ : Finset (SigAt B_bank α)),
                  (P_set.image fun pStar =>
                    (coarseCutOf x_in xs T A B_bank a α (liftSig s) pStar).2).card :=
                Finset.card_biUnion_le
            _ ≤ ∑ _s ∈ (Finset.univ : Finset (SigAt B_bank α)), B :=
                Finset.sum_le_sum fun _ _ => Finset.card_image_le.trans hP_card
            _ = (Finset.univ : Finset (SigAt B_bank α)).card * B := by simp
            _ ≤ K₀ * B := Nat.mul_le_mul_right B (hSig_card α hαM)
      _ = M_ph * (K₀ * B) := by simp
  let Θ_all : Finset ℕ := (Finset.range (M_ph + 1)).image a ∪ Θ_cuts
  let J_split : Finset (Fin d) :=
    Θ_all.biUnion fun θ => (Finset.univ : Finset (Fin d)).filter (SplitsRow θ)
  let J_split' : Finset (Fin d) := insert ⟨0, hd⟩ J_split
  have hJ_split'_card : J_split'.card ≤ C_split := by
    have hJs : J_split.card ≤ (M_ph + 1) + M_ph * (K₀ * B) := by
      calc J_split.card
          ≤ ∑ θ ∈ Θ_all, ((Finset.univ : Finset (Fin d)).filter (SplitsRow θ)).card :=
            Finset.card_biUnion_le
        _ ≤ ∑ _θ ∈ Θ_all, 1 := Finset.sum_le_sum fun θ _ => hSplits_le_one θ
        _ = Θ_all.card := by simp
        _ ≤ ((Finset.range (M_ph + 1)).image a).card + Θ_cuts.card := Finset.card_union_le _ _
        _ ≤ (M_ph + 1) + M_ph * (K₀ * B) := by
            refine Nat.add_le_add ?_ hΘ_cuts_card
            exact Finset.card_image_le.trans (by simp)
    calc J_split'.card
        ≤ J_split.card + 1 := Finset.card_insert_le _ _
      _ ≤ ((M_ph + 1) + M_ph * (K₀ * B)) + 1 := Nat.add_le_add_right hJs 1
      _ = C_split := by dsimp [C_split]; omega
  let J_good : Finset (Fin d) := Finset.univ \ J_split'
  let α₀ : Fin d → ℕ := fun j =>
    if j.1 = 0 then 0 else phaseOf M_ph a (ot (loOut j))
  have hloOut_pos_of_ne : ∀ j : Fin d, j.1 ≠ 0 → 1 ≤ loOut j := fun j hj =>
    Nat.mul_pos (Nat.pos_of_ne_zero hj) hW
  have hα₀_lt : ∀ j : Fin d, α₀ j < M_ph := by
    intro j
    dsimp [α₀]
    split_ifs with hj0
    · omega
    · have hloL : loOut j < L := (hlo_hi_lt j).1.trans_lt (hlo_hi_lt j).2
      exact (phaseOf_spec_of_ge haM (hot_ge_a0 (loOut j) (hloOut_pos_of_ne j hj0) hloL)
        (hot_lt (loOut j) hloL)).1
  -- Forbidden quantile-bucket set `F j` (`≤ K₀` buckets out of `B = 2 * K₀`).
  let matchBuckets : (j : Fin d) → SigAt B_bank (α₀ j) → Finset (Fin B) := fun j s =>
    Finset.univ.filter fun c : Fin B =>
      ∃ u ∈ bucketR c, ∀ m : Fin (B - 1),
        (u.1 < rThresh m ↔
          tcut (coarseCutOf x_in xs T A B_bank a (α₀ j) (liftSig s) (pThresh m)).1
            (coarseCutOf x_in xs T A B_bank a (α₀ j) (liftSig s) (pThresh m)).2
            (ot (loOut j)))
  have hsep_buckets : ∀ {c₁ c₂ : Fin B}, c₁.1 < c₂.1 →
      ∀ u₁ ∈ bucketR c₁, ∀ u₂ ∈ bucketR c₂,
        ∃ m : Fin (B - 1), u₁.1 < rThresh m ∧ ¬ (u₂.1 < rThresh m) := by
    intro c₁ c₂ hlt u₁ hu₁ u₂ hu₂
    let m : Fin (B - 1) := ⟨c₁.1, by omega⟩
    obtain ⟨k₁, hk₁, rfl⟩ := Finset.mem_image.mp hu₁
    obtain ⟨k₂, hk₂, rfl⟩ := Finset.mem_image.mp hu₂
    have hb₁ := (Finset.mem_filter.mp hk₁).2
    have hb₂ := (Finset.mem_filter.mp hk₂).2
    refine ⟨m, ?_, ?_⟩
    · have hk_lt : k₁ < kThresh m := Fin.lt_def.mpr hb₁.2
      exact Fin.lt_def.mp (show (e k₁).1 < (e (kThresh m)).1 from e.strictMono hk_lt)
    · have hle_div : (c₁.1 + 1) * N / B ≤ c₂.1 * N / B :=
        Nat.div_le_div_right (Nat.mul_le_mul_right N (by omega))
      have hk_le : kThresh m ≤ k₂ := Fin.le_def.mpr (hle_div.trans hb₂.1)
      have he_le : rThresh m ≤ (e k₂).1.1 :=
        Fin.le_def.mp (show (e (kThresh m)).1 ≤ (e k₂).1 from e.monotone hk_le)
      omega
  have hmatch_le_one : ∀ (j : Fin d) (s : SigAt B_bank (α₀ j)), (matchBuckets j s).card ≤ 1 := by
    intro j s
    refine Finset.card_le_one.mpr fun c₁ hc₁ c₂ hc₂ => ?_
    obtain ⟨_, u₁, hu₁, hm₁⟩ := Finset.mem_filter.mp hc₁
    obtain ⟨_, u₂, hu₂, hm₂⟩ := Finset.mem_filter.mp hc₂
    by_contra hne
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
    · obtain ⟨m, h1, h2⟩ := hsep_buckets hlt u₁ hu₁ u₂ hu₂
      exact h2 (((hm₁ m).trans (hm₂ m).symm).mp h1)
    · obtain ⟨m, h2, h1⟩ := hsep_buckets hgt u₂ hu₂ u₁ hu₁
      exact h1 (((hm₂ m).trans (hm₁ m).symm).mp h2)
  let F : Fin d → Finset (Fin B) := fun j =>
    (Finset.univ : Finset (SigAt B_bank (α₀ j))).biUnion (matchBuckets j)
  have hF_card : ∀ j : Fin d, (F j).card ≤ K₀ := by
    intro j
    calc (F j).card
        ≤ ∑ s ∈ (Finset.univ : Finset (SigAt B_bank (α₀ j))), (matchBuckets j s).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _s ∈ (Finset.univ : Finset (SigAt B_bank (α₀ j))), 1 :=
          Finset.sum_le_sum fun s _ => hmatch_le_one j s
      _ = (Finset.univ : Finset (SigAt B_bank (α₀ j))).card := by simp
      _ ≤ K₀ := hSig_card (α₀ j) (hα₀_lt j)
  -- Pigeonhole a quantile bucket `cStar` avoided by at least half of `J_good`.
  let J_of : Fin B → Finset (Fin d) := fun c => J_good.filter fun j => c ∉ F j
  have hpigeon : ∃ cStar : Fin B, J_good.card ≤ 2 * (J_of cStar).card := by
    have hsum : J_good.card * K₀ ≤ ∑ c : Fin B, (J_of c).card := by
      have hswap : ∑ c : Fin B, (J_of c).card =
          ∑ j ∈ J_good, ((Finset.univ : Finset (Fin B)).filter fun c => c ∉ F j).card := by
        simp only [J_of, Finset.card_filter]
        exact Finset.sum_comm
      rw [hswap]
      calc J_good.card * K₀
          = ∑ _j ∈ J_good, K₀ := by simp
        _ ≤ ∑ j ∈ J_good, ((Finset.univ : Finset (Fin B)).filter fun c => c ∉ F j).card := by
            refine Finset.sum_le_sum fun j _ => ?_
            have hsdiff : ((Finset.univ : Finset (Fin B)).filter fun c => c ∉ F j) =
                Finset.univ \ F j := by ext c; simp
            rw [hsdiff]
            have hleF := hF_card j
            have hcardU : (Finset.univ : Finset (Fin B)).card = 2 * K₀ := by simp [B]
            have hadd := Finset.card_sdiff_add_card_inter (Finset.univ : Finset (Fin B)) (F j)
            have hinter : (Finset.univ ∩ F j).card = (F j).card := by simp
            omega
    by_contra hall
    push Not at hall
    have hlt_sum : ∑ c : Fin B, (2 * (J_of c).card) < ∑ _c : Fin B, J_good.card :=
      Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty_iff.mpr ⟨⟨0, hB0⟩⟩) fun c _ => hall c
    have h1 : ∑ c : Fin B, (2 * (J_of c).card) = 2 * ∑ c : Fin B, (J_of c).card := by
      rw [Finset.mul_sum]
    have h2 : (∑ _c : Fin B, J_good.card) = 2 * K₀ * J_good.card := by simp [B]
    have hmul_comm : 2 * (J_good.card * K₀) = 2 * K₀ * J_good.card := by ring
    omega
  obtain ⟨cStar, hcStar⟩ := hpigeon
  -- Construct `Rect` and `S_ind := ((Rect \ Z_cone) \ Z_in) \ Z_pad`.
  let outRow : Fin L → Fin d := fun q => ⟨q.1 / b % d, (Transpose.Tape.Impl.pos_decomp q.2).2.1⟩
  let Rect : Finset (Fin L) :=
    Finset.univ.filter fun q : Fin L => rawRowOf q ∈ bucketR cStar ∧ outRow q ∈ J_of cStar
  let S_ind : Finset (Fin L) := ((Rect \ Z_cone) \ Z_in) \ Z_pad
  refine ⟨S_ind, ?_, ?_⟩
  · -- Prove `IsIndependent (coneRel 1 z T Γ ot (fun q => tpos d b q)) S_ind`.
    intro q hqS p hpN hpS
    obtain ⟨hqRZI, _⟩ := Finset.mem_sdiff.mp hqS
    obtain ⟨hqRZ, _⟩ := Finset.mem_sdiff.mp hqRZI
    obtain ⟨hqRect, hqNotZ⟩ := Finset.mem_sdiff.mp hqRZ
    obtain ⟨hpRZI, hpNotZpad⟩ := Finset.mem_sdiff.mp hpS
    obtain ⟨hpRZ, hpNotZin⟩ := Finset.mem_sdiff.mp hpRZI
    obtain ⟨hpRect, _⟩ := Finset.mem_sdiff.mp hpRZ
    obtain ⟨_, _, hqJ⟩ := Finset.mem_filter.mp hqRect
    obtain ⟨_, hpR, _⟩ := Finset.mem_filter.mp hpRect
    obtain ⟨hjGood, hcNotF⟩ := Finset.mem_filter.mp hqJ
    have hjNotSplit' : outRow q ∉ J_split' := (Finset.mem_sdiff.mp hjGood).2
    have hj_ne0 : (outRow q).1 ≠ 0 := by
      intro h0
      exact hjNotSplit' (Finset.mem_insert.mpr (Or.inl (Fin.ext h0)))
    have hjNotSplit : outRow q ∉ J_split :=
      fun hm => hjNotSplit' (Finset.mem_insert_of_mem hm)
    have hnot_splits : ∀ θ ∈ Θ_all, ¬ SplitsRow θ (outRow q) := fun θ hθ hs =>
      hjNotSplit (Finset.mem_biUnion.mpr ⟨θ, hθ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩⟩)
    -- Unpack `p ∈ coneRel 1 z T Γ ot (tpos d b) q`.
    simp only [MergeDepth.coneRel, Finset.mem_filter, Finset.mem_univ, true_and,
      Nat.cast_one, Int.ediv_one] at hpN
    obtain ⟨ρ, hdep_skel, hfree, hrd_eq⟩ := hpN
    have hdep : IsDepPath xs T (ot (MergeDepth.tpos d b q) :: ρ) := by
      rwa [hskel_eq] at hdep_skel
    have htpos_eq : MergeDepth.tpos d b q = (tposOf d b q).1 := by
      rw [← tape_tpos_eq, ← tposOf_val]
    set ℓ := MergeDepth.tpos d b q
    set t₀ := ot ℓ
    -- Since `p ∈ Rect \ Z_pad`, `p` lies in the `E_pad`-interior of `rawRowOf p ∈ R_suf`,
    -- forcing `a 0 = t_suf ≤ (t₀ :: ρ).getLastD t₀`.
    have hp_suf : rawRowOf p ∈ R_suf := hbucket_sub cStar hpR
    have ht_last_ge : a 0 ≤ (t₀ :: ρ).getLastD t₀ := by
      rw [ha0]
      by_contra hlt_suf
      have hnot_pad : ¬ (p.1 % W < E_pad ∨ W - E_pad ≤ p.1 % W) :=
        fun hm => hpNotZpad (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩)
      have hraw_div : (rawRowOf p).1 = p.1 / W := by
        show p.1 / b / d = p.1 / (d * b)
        rw [Nat.div_div_eq_div_mul, Nat.mul_comm b d]
      have hp_decomp : p.1 = (rawRowOf p).1 * W + p.1 % W := by
        have h := Nat.div_add_mod p.1 W
        rw [← hraw_div, Nat.mul_comm] at h
        exact h.symm
      have hlo_p : (rawRowOf p).1 * W + E_pad ≤ p.1 := by omega
      have hhi_p : p.1 + E_pad < ((rawRowOf p).1 + 1) * W := by
        rw [Nat.add_mul, Nat.one_mul]
        omega
      have hin_int :
          (((rawRowOf p).1 * (d * b) + E_pad : ℕ) : ℤ) ≤ x_in ((t₀ :: ρ).getLastD t₀) ∧
          x_in ((t₀ :: ρ).getLastD t₀) <
            ((((rawRowOf p).1 + 1) * (d * b) : ℕ) : ℤ) - (E_pad : ℤ) := by
        dsimp [x_in]
        rw [← hrd_eq]
        change (((rawRowOf p).1 * W + E_pad : ℕ) : ℤ) ≤ (p.1 : ℤ) ∧
          (p.1 : ℤ) < ((((rawRowOf p).1 + 1) * W : ℕ) : ℤ) - (E_pad : ℤ)
        omega
      exact hno_pre ((t₀ :: ρ).getLastD t₀) (Nat.lt_of_not_ge hlt_suf) (rawRowOf p) hp_suf hin_int
    have hℓ_bounds := (coord_row_bounds q).2
    rw [← htpos_eq] at hℓ_bounds
    have hlo_ℓ : loOut (outRow q) ≤ ℓ := hℓ_bounds.1
    have hℓ_hi : ℓ ≤ hiOut (outRow q) := hℓ_bounds.2
    have hℓ_lt : ℓ < L := by rw [htpos_eq]; exact (tposOf d b q).2
    have ht₀_lt : t₀ < T := hot_lt ℓ hℓ_lt
    have hlo_lt_L : loOut (outRow q) < L :=
      (hlo_hi_lt (outRow q)).1.trans_lt (hlo_hi_lt (outRow q)).2
    have hlo_ge_a0 : a 0 ≤ ot (loOut (outRow q)) :=
      hot_ge_a0 (loOut (outRow q)) (hloOut_pos_of_ne (outRow q) hj_ne0) hlo_lt_L
    have ht0_lo : ot (loOut (outRow q)) ≤ t₀ := hot_mono hlo_ℓ hℓ_lt
    have ht0_hi : t₀ ≤ ot (hiOut (outRow q)) := hot_mono hℓ_hi (hlo_hi_lt (outRow q)).2
    have hα₀_eq : α₀ (outRow q) = phaseOf M_ph a (ot (loOut (outRow q))) := by
      simp [α₀, hj_ne0]
    have hph_t₀ : phaseOf M_ph a t₀ = α₀ (outRow q) := by
      have hlo_lt_T : ot (loOut (outRow q)) < T := hot_lt _ hlo_lt_L
      obtain ⟨hαM, ha_lo, _⟩ := phaseOf_spec_of_ge haM hlo_ge_a0 hlo_lt_T
      have hmemΘ : a (α₀ (outRow q) + 1) ∈ Θ_all :=
        Finset.mem_union_left _ (Finset.mem_image_of_mem a
          (Finset.mem_range.mpr (by have := hα₀_lt (outRow q); omega)))
      have hns := hnot_splits _ hmemΘ
      have hhi_lt : ot (hiOut (outRow q)) < a (α₀ (outRow q) + 1) := by
        dsimp [SplitsRow] at hns
        rw [hα₀_eq] at hns ⊢
        omega
      rw [hα₀_eq]
      exact (phaseOf_eq_iff_of_ge haM ha (hlo_ge_a0.trans ht0_lo) ht₀_lt hαM).mpr
        ⟨ha_lo.trans ht0_lo, ht0_hi.trans_lt (by rwa [← hα₀_eq])⟩
    have hlen_ρ : ρ.length ≤ D := by
      have h1 := hdepth (t₀ :: ρ) hdep_skel hfree
      simp at h1; omega
    have havoid_X : ∀ x ∈ t₀ :: ρ, x ∉ X_bad := by
      intro x hx hx_bad
      have ht0_anc := ancestors_mono xs T X_bad hlen_ρ
        (head_mem_ancestors_of_mem_path ρ t₀ hdep hx hx_bad)
      exact hqNotZ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht0_anc⟩)
    have havoid_guard : ∀ x ∈ t₀ :: ρ,
        x ∉ longWorkHopsSuffix xs B_bank (a 0) T τ_cut ∧ x ∉ phaseStartGuard M_ph a τ_cut :=
      fun x hx =>
        ⟨fun h => havoid_X x hx (Finset.mem_union_left _ (Finset.mem_union_left _ h)),
         fun h => havoid_X x hx (Finset.mem_union_left _ (Finset.mem_union_right _ h))⟩
    have hrd : x_in ((t₀ :: ρ).getLastD t₀) = (p.1 : ℤ) := hrd_eq.symm
    obtain ⟨s, hs⟩ := depPath_coarse_signature_exists_suffix (τ_cut := τ_cut) hτ haM ha hin
      (α₀ (outRow q)) (hα₀_lt (outRow q)) ht₀_lt hph_t₀ ht_last_ge hdep havoid_guard hrd
    apply hcNotF
    refine Finset.mem_biUnion.mpr ⟨s, Finset.mem_univ _, ?_⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, rawRowOf p, hpR, fun m => ?_⟩
    have hp_mem_P : pThresh m ∈ P_set := Finset.mem_image_of_mem pThresh (Finset.mem_univ m)
    have hnoband : ¬ (pThresh m ≤ p.1 ∧ p.1 < pThresh m + A) := fun hband =>
      hpNotZin (Finset.mem_biUnion.mpr ⟨pThresh m, hp_mem_P,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hband⟩⟩)
    have hnogrd : ∀ x ∈ t₀ :: ρ,
        x ∉ coarseGuardsOf x_in xs T τ_cut A B_bank a (α₀ (outRow q)) (liftSig s) (pThresh m) := by
      intro x hx hmem
      apply havoid_X x hx
      refine Finset.mem_union_right _ ?_
      exact Finset.mem_biUnion.mpr ⟨α₀ (outRow q), Finset.mem_range.mpr (hα₀_lt (outRow q)),
        Finset.mem_biUnion.mpr ⟨s, Finset.mem_univ _,
          Finset.mem_biUnion.mpr ⟨pThresh m, hp_mem_P, hmem⟩⟩⟩
    have htcut_t₀ := hs (pThresh m) hnoband hnogrd
    let c₀ := coarseCutOf x_in xs T A B_bank a (α₀ (outRow q)) (liftSig s) (pThresh m)
    have hc₀_mem : c₀.2 ∈ Θ_all := by
      refine Finset.mem_union_right _ ?_
      exact Finset.mem_biUnion.mpr ⟨α₀ (outRow q), Finset.mem_range.mpr (hα₀_lt (outRow q)),
        Finset.mem_biUnion.mpr ⟨s, Finset.mem_univ _,
          Finset.mem_image.mpr ⟨pThresh m, hp_mem_P, rfl⟩⟩⟩
    have hns_c₀ := hnot_splits c₀.2 hc₀_mem
    have htcut_unsplit : tcut c₀.1 c₀.2 t₀ ↔ tcut c₀.1 c₀.2 (ot (loOut (outRow q))) := by
      dsimp [SplitsRow] at hns_c₀
      cases c₀.1 <;> simp only [tcut, ↓reduceIte, Bool.false_eq_true] <;> omega
    exact ((coord_row_bounds p).1 (rThresh m)).trans (htcut_t₀.symm.trans htcut_unsplit)
  · -- Lower-bound `Rect.card` and deduce the size bound on `S_ind`.
    let ProdSet := (bucketR cStar ×ˢ J_of cStar) ×ˢ (Finset.univ : Finset (Fin b))
    let g : (Fin d × Fin d) × Fin b → Fin L := fun x =>
      ⟨(x.1.1.1 * d + x.1.2.1) * b + x.2.1, by
        calc (x.1.1.1 * d + x.1.2.1) * b + x.2.1
            < (x.1.1.1 * d + x.1.2.1) * b + b := Nat.add_lt_add_left x.2.2 _
          _ = (x.1.1.1 * d + x.1.2.1 + 1) * b := by ring
          _ ≤ (x.1.1.1 * d + d) * b := Nat.mul_le_mul_right b (by omega)
          _ = (x.1.1.1 + 1) * d * b := by ring
          _ ≤ d * d * b := Nat.mul_le_mul_right b (Nat.mul_le_mul_right d (by omega))⟩
    have hg_parts : ∀ x : (Fin d × Fin d) × Fin b,
        (g x).1 / b = x.1.1.1 * d + x.1.2.1 ∧ (g x).1 % b = x.2.1 ∧
        (g x).1 / b / d = x.1.1.1 ∧ (g x).1 / b % d = x.1.2.1 := by
      intro x
      have hdivb : ((x.1.1.1 * d + x.1.2.1) * b + x.2.1) / b = x.1.1.1 * d + x.1.2.1 := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hb, Nat.div_eq_of_lt x.2.2, zero_add]
      have hmodb : ((x.1.1.1 * d + x.1.2.1) * b + x.2.1) % b = x.2.1 := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt x.2.2]
      have hdivd : (x.1.1.1 * d + x.1.2.1) / d = x.1.1.1 := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hd, Nat.div_eq_of_lt x.1.2.2, zero_add]
      have hmodd : (x.1.1.1 * d + x.1.2.1) % d = x.1.2.1 := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt x.1.2.2]
      refine ⟨hdivb, hmodb, ?_, ?_⟩
      · dsimp [g]; rw [hdivb, hdivd]
      · dsimp [g]; rw [hdivb, hmodd]
    have hg_inj : Set.InjOn g ProdSet := by
      intro x₁ _ x₂ _ heq
      have hv : (g x₁).1 = (g x₂).1 := congrArg Fin.val heq
      obtain ⟨_, hs1, hu1, hj1⟩ := hg_parts x₁
      obtain ⟨_, hs2, hu2, hj2⟩ := hg_parts x₂
      ext
      · rw [← hu1, ← hu2, hv]
      · rw [← hj1, ← hj2, hv]
      · rw [← hs1, ← hs2, hv]
    have hg_sub : ProdSet.image g ⊆ Rect := by
      intro q hq
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
      obtain ⟨hp_pair, -⟩ := Finset.mem_product.mp hx
      obtain ⟨hu_mem, hj_mem⟩ := Finset.mem_product.mp hp_pair
      obtain ⟨-, -, hu_eq, hj_eq⟩ := hg_parts x
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
      · have : rawRowOf (g x) = x.1.1 := Fin.ext hu_eq
        rwa [this]
      · have : outRow (g x) = x.1.2 := Fin.ext hj_eq
        rwa [this]
    have hJgood_ge : d - C_split ≤ J_good.card := by
      have hadd := Finset.card_sdiff_add_card_inter (Finset.univ : Finset (Fin d)) J_split'
      change J_good.card + (Finset.univ ∩ J_split').card =
        (Finset.univ : Finset (Fin d)).card at hadd
      have hinter : (Finset.univ ∩ J_split').card = J_split'.card := by simp
      have huniv : (Finset.univ : Finset (Fin d)).card = d := by simp
      omega
    have hJof_ge : (d - C_split) / 2 ≤ (J_of cStar).card := by omega
    have hR_ge : N / B ≤ (bucketR cStar).card := hbucket_card cStar
    have hRect_ge : (N / B) * ((d - C_split) / 2) * b ≤ Rect.card := by
      calc (N / B) * ((d - C_split) / 2) * b
          ≤ (bucketR cStar).card * (J_of cStar).card * b :=
            Nat.mul_le_mul_right b (Nat.mul_le_mul hR_ge hJof_ge)
        _ = ProdSet.card := by simp [ProdSet]
        _ = (ProdSet.image g).card := (Finset.card_image_of_injOn hg_inj).symm
        _ ≤ Rect.card := Finset.card_le_card hg_sub
    have hsdiff1 := Finset.card_sdiff_add_card_inter Rect Z_cone
    have hinter1 : (Rect ∩ Z_cone).card ≤ Z_cone.card := Finset.card_le_card inter_subset_right
    have hsdiff2 := Finset.card_sdiff_add_card_inter (Rect \ Z_cone) Z_in
    have hinter2 : ((Rect \ Z_cone) ∩ Z_in).card ≤ Z_in.card :=
      Finset.card_le_card inter_subset_right
    have hsdiff3 := Finset.card_sdiff_add_card_inter ((Rect \ Z_cone) \ Z_in) Z_pad
    have hinter3 : (((Rect \ Z_cone) \ Z_in) ∩ Z_pad).card ≤ Z_pad.card :=
      Finset.card_le_card inter_subset_right
    change S_ind.card + (((Rect \ Z_cone) \ Z_in) ∩ Z_pad).card =
      ((Rect \ Z_cone) \ Z_in).card at hsdiff3
    omega

/-- Asymptotic arithmetic bridge turning `suffixJitterBM_independent_exists` + `storageCode_log_le`
into `(1 - δ₀ / (4 * K₀) + δ) * L` whenever `A(d) / L → 0`, `S(d) / L → 0`, and
`(d * E_pad(d)) / L → 0`. -/
private theorem storage_bound_of_suffix_jitter_card_bound (K₀ C_split C_cone : ℕ)
    (hK₀_pos : 1 ≤ K₀) {C δ₀ δ : ℝ} (hC : 1 ≤ C) (hδ₀ : 0 < δ₀) (hδ : 0 < δ)
    {E_pad A S : ℕ → ℕ}
    (hE : Tendsto (fun d : ℕ => ((d * E_pad d : ℕ) : ℝ) / ((d * d * entryBits d : ℕ) : ℝ))
      atTop (nhds 0))
    (hA : Tendsto (fun d : ℕ => (A d : ℝ) / ((d * d * entryBits d : ℕ) : ℝ)) atTop (nhds 0))
    (hS : Tendsto (fun d : ℕ => (S d : ℝ) / ((d * d * entryBits d : ℕ) : ℝ)) atTop (nhds 0)) :
    ∃ d_0 : ℕ, ∀ d ≥ d_0, ∀ (T N S_card : ℕ),
      let b := entryBits d
      let L := d * d * b
      let B := 2 * K₀
      let τ_cut := Nat.sqrt (max 1 (S d) * (T + 1)) + 1
      (T : ℝ) ≤ C * ((L : ℝ) + 1) →
      δ₀ * (d : ℝ) ≤ (N : ℝ) →
      (N / B) * ((d - C_split) / 2) * b ≤
        S_card + C_cone * (τ_cut + A d + 1) + B * A d + 2 * d * E_pad d →
      ((L : ℝ) - (S_card : ℝ)) ≤
        (1 - δ₀ / (4 * (K₀ : ℝ)) + δ) * (L : ℝ) := by
  let B := 2 * K₀
  let C_A : ℝ := (C_cone : ℝ) + (B : ℝ) + 1
  have hCA_pos : 0 < C_A := by positivity
  let η_tau : ℝ := δ / (12 * ((C_cone : ℝ) + 1))
  have hη_tau : 0 < η_tau := by positivity
  let ε_S : ℝ := η_tau ^ 2 / (2 * C + 1)
  have hε_S : 0 < ε_S := by positivity
  let ε_A : ℝ := δ / (4 * C_A)
  have hε_A : 0 < ε_A := by positivity
  let ε_E : ℝ := δ / 8
  have hε_E : 0 < ε_E := by positivity
  obtain ⟨d_S, hd_S⟩ := eventually_atTop.mp ((tendsto_order.mp hS).2 ε_S hε_S)
  obtain ⟨d_A, hd_A⟩ := eventually_atTop.mp ((tendsto_order.mp hA).2 ε_A hε_A)
  obtain ⟨d_E, hd_E⟩ := eventually_atTop.mp ((tendsto_order.mp hE).2 ε_E hε_E)
  let coef_lin : ℝ := δ₀ * ((C_split : ℝ) + 1) + 2
  have hcoef_pos : 0 < coef_lin := by positivity
  let d_one : ℕ := max ⌈1 / ε_S⌉₊ ⌈1 / η_tau⌉₊ + 1
  let d_lin : ℕ := ⌈(16 * coef_lin) / δ⌉₊ + ⌈(B : ℝ) / δ₀⌉₊ + C_split + B + 2
  refine ⟨max (max d_S (max d_A d_E)) (max d_one d_lin),
    fun d hd T N S_card hT hN_ge hcard_nat => ?_⟩
  have hd_ge_S : d_S ≤ d := (le_max_left _ _).trans ((le_max_left _ _).trans hd)
  have hd_ge_AE : max d_A d_E ≤ d := (le_max_right _ _).trans ((le_max_left _ _).trans hd)
  have hd_ge_A : d_A ≤ d := (le_max_left _ _).trans hd_ge_AE
  have hd_ge_E : d_E ≤ d := (le_max_right _ _).trans hd_ge_AE
  have hd_ge_one : d_one ≤ d := (le_max_left _ _).trans ((le_max_right _ _).trans hd)
  have hd_ge_lin : d_lin ≤ d := (le_max_right _ _).trans ((le_max_right _ _).trans hd)
  set b := entryBits d
  set L := d * d * b
  set τ_cut := Nat.sqrt (max 1 (S d) * (T + 1)) + 1
  have hb1 : 1 ≤ b := one_le_entryBits d
  have hd1 : 1 ≤ d := by omega
  have hL_ge_d : d ≤ L := by
    calc d = d * 1 * 1 := by ring
      _ ≤ d * d * b := Nat.mul_le_mul (Nat.mul_le_mul_left d hd1) hb1
  have hL1 : 1 ≤ L := hd1.trans hL_ge_d
  have hL_pos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL1
  -- 1. Bound `C_cone * (τ_cut + 1) ≤ (δ / 4) * L`.
  have hSd_lt : (S d : ℝ) < ε_S * (L : ℝ) := (div_lt_iff₀ hL_pos).mp (hd_S d hd_ge_S)
  have h1_le_εL : (1 : ℝ) ≤ ε_S * (L : ℝ) := by
    have hceil : 1 / ε_S ≤ (d : ℝ) := by
      calc 1 / ε_S ≤ (⌈1 / ε_S⌉₊ : ℝ) := Nat.le_ceil _
        _ ≤ (d_one : ℝ) := by exact_mod_cast (show ⌈1 / ε_S⌉₊ ≤ d_one by omega)
        _ ≤ (d : ℝ) := by exact_mod_cast hd_ge_one
    have hdL : (d : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL_ge_d
    exact (div_le_iff₀' hε_S).mp (hceil.trans hdL)
  have hmaxS_le : ((max 1 (S d) : ℕ) : ℝ) ≤ ε_S * (L : ℝ) := by
    rw [Nat.cast_max, Nat.cast_one]
    exact max_le h1_le_εL hSd_lt.le
  have hT1_le : ((T + 1 : ℕ) : ℝ) ≤ (2 * C + 1) * (L : ℝ) := by
    have h1L : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL1
    push_cast
    nlinarith
  have hN_le : ((max 1 (S d) * (T + 1) : ℕ) : ℝ) ≤ (η_tau * (L : ℝ)) ^ 2 := by
    rw [Nat.cast_mul]
    calc ((max 1 (S d) : ℕ) : ℝ) * ((T + 1 : ℕ) : ℝ)
        ≤ (ε_S * (L : ℝ)) * ((2 * C + 1) * (L : ℝ)) := by gcongr
      _ = (η_tau * (L : ℝ)) ^ 2 := by dsimp [ε_S]; field_simp
  have hsqrt_le : (Nat.sqrt (max 1 (S d) * (T + 1)) : ℝ) ≤ η_tau * (L : ℝ) := by
    have hsq_r : (Nat.sqrt (max 1 (S d) * (T + 1)) : ℝ) *
        (Nat.sqrt (max 1 (S d) * (T + 1)) : ℝ) ≤ ((max 1 (S d) * (T + 1) : ℕ) : ℝ) := by
      exact_mod_cast Nat.sqrt_le (max 1 (S d) * (T + 1))
    have hnn1 : (0 : ℝ) ≤ (Nat.sqrt (max 1 (S d) * (T + 1)) : ℝ) := by positivity
    have hnn2 : (0 : ℝ) ≤ η_tau * (L : ℝ) := by positivity
    nlinarith
  have h1_le_ηL : (1 : ℝ) ≤ η_tau * (L : ℝ) := by
    have hceil : 1 / η_tau ≤ (d : ℝ) := by
      calc 1 / η_tau ≤ (⌈1 / η_tau⌉₊ : ℝ) := Nat.le_ceil _
        _ ≤ (d_one : ℝ) := by exact_mod_cast (show ⌈1 / η_tau⌉₊ ≤ d_one by omega)
        _ ≤ (d : ℝ) := by exact_mod_cast hd_ge_one
    have hdL : (d : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL_ge_d
    exact (div_le_iff₀' hη_tau).mp (hceil.trans hdL)
  have hτ_err : (C_cone : ℝ) * ((τ_cut : ℝ) + 1) ≤ (δ / 4) * (L : ℝ) := by
    have hτ1_r : (τ_cut : ℝ) + 1 ≤ 3 * η_tau * (L : ℝ) := by
      have : (τ_cut : ℝ) = (Nat.sqrt (max 1 (S d) * (T + 1)) : ℝ) + 1 := by
        dsimp [τ_cut]; push_cast; rfl
      linarith
    have hC_nn : (0 : ℝ) ≤ (C_cone : ℝ) := by positivity
    calc (C_cone : ℝ) * ((τ_cut : ℝ) + 1)
        ≤ (C_cone : ℝ) * (3 * η_tau * (L : ℝ)) := mul_le_mul_of_nonneg_left hτ1_r hC_nn
      _ ≤ ((C_cone : ℝ) + 1) * (3 * η_tau * (L : ℝ)) := by nlinarith
      _ = (δ / 4) * (L : ℝ) := by dsimp [η_tau]; field_simp; ring
  -- 2. Bound `(C_cone + B) * A d ≤ (δ / 4) * L`.
  have hAd_lt : (A d : ℝ) < ε_A * (L : ℝ) := (div_lt_iff₀ hL_pos).mp (hd_A d hd_ge_A)
  have hA_err : ((C_cone : ℝ) + (B : ℝ)) * (A d : ℝ) ≤ (δ / 4) * (L : ℝ) := by
    calc ((C_cone : ℝ) + (B : ℝ)) * (A d : ℝ)
        ≤ C_A * (A d : ℝ) := by
          have : (C_cone : ℝ) + (B : ℝ) ≤ C_A := by dsimp [C_A]; linarith
          exact mul_le_mul_of_nonneg_right this (by positivity)
      _ ≤ C_A * (ε_A * (L : ℝ)) := mul_le_mul_of_nonneg_left hAd_lt.le hCA_pos.le
      _ = (δ / 4) * (L : ℝ) := by dsimp [ε_A]; field_simp
  -- 3. Bound `2 * d * E_pad d ≤ (δ / 4) * L`.
  have hEd_lt : ((d * E_pad d : ℕ) : ℝ) < ε_E * (L : ℝ) :=
    (div_lt_iff₀ hL_pos).mp (hd_E d hd_ge_E)
  have hE_err : 2 * (d : ℝ) * (E_pad d : ℝ) ≤ (δ / 4) * (L : ℝ) := by
    have hcast_E : ((d * E_pad d : ℕ) : ℝ) = (d : ℝ) * (E_pad d : ℝ) := by push_cast; rfl
    rw [hcast_E] at hEd_lt
    dsimp [ε_E] at hEd_lt
    linarith
  -- 4. Bound rectangle term `≥ (δ₀ / (4 * K₀) - δ / 4) * L`.
  have hd_sub : C_split ≤ d := by omega
  have hBr : (0 : ℝ) < (B : ℝ) := by positivity
  have hdivB_r : (δ₀ * (d : ℝ)) / (B : ℝ) - 1 ≤ ((N / B : ℕ) : ℝ) := by
    have hmod := Nat.div_add_mod N B
    have hlt := Nat.mod_lt N (show 0 < B by omega)
    have h1 : (N : ℝ) ≤ ((B * (N / B) + B : ℕ) : ℝ) := by
      exact_mod_cast (by omega : N ≤ B * (N / B) + B)
    push_cast at h1
    have hNB_div : (N : ℝ) / (B : ℝ) - 1 ≤ ((N / B : ℕ) : ℝ) := by
      rw [sub_le_iff_le_add, div_le_iff₀ hBr]
      linarith
    have hδN : (δ₀ * (d : ℝ)) / (B : ℝ) ≤ (N : ℝ) / (B : ℝ) :=
      div_le_div_of_nonneg_right hN_ge hBr.le
    linarith
  have hdiv2_r : ((d : ℝ) - (C_split : ℝ) - 1) / 2 ≤ (((d - C_split) / 2 : ℕ) : ℝ) := by
    have h1 : d - C_split ≤ 2 * ((d - C_split) / 2) + 1 := by omega
    have h1r : ((d - C_split : ℕ) : ℝ) ≤ ((2 * ((d - C_split) / 2) + 1 : ℕ) : ℝ) := by
      exact_mod_cast h1
    rw [Nat.cast_sub hd_sub] at h1r
    push_cast at h1r
    linarith
  have hpos_f1 : (0 : ℝ) ≤ (δ₀ * (d : ℝ)) / (B : ℝ) - 1 := by
    rw [sub_nonneg, le_div_iff₀ hBr]
    have hceil_B : (B : ℝ) / δ₀ ≤ (d : ℝ) := by
      calc (B : ℝ) / δ₀ ≤ (⌈(B : ℝ) / δ₀⌉₊ : ℝ) := Nat.le_ceil _
        _ ≤ (d_lin : ℝ) := Nat.cast_le.mpr (by omega)
        _ ≤ (d : ℝ) := Nat.cast_le.mpr hd_ge_lin
    have hmul_B := (div_le_iff₀ hδ₀).mp hceil_B
    linarith
  have hpos_f2 : (0 : ℝ) ≤ ((d : ℝ) - (C_split : ℝ) - 1) / 2 := by
    have : C_split + 1 ≤ d := by omega
    have hr : ((C_split + 1 : ℕ) : ℝ) ≤ (d : ℝ) := by exact_mod_cast this
    push_cast at hr
    linarith
  have hrect_r : ((δ₀ / (4 * (K₀ : ℝ)) - δ / 4) * (L : ℝ)) ≤
      (((N / B) * ((d - C_split) / 2) * b : ℕ) : ℝ) := by
    have hprod : ((δ₀ * (d : ℝ)) / (B : ℝ) - 1) * (((d : ℝ) - (C_split : ℝ) - 1) / 2) * (b : ℝ) ≤
        (((N / B) * ((d - C_split) / 2) * b : ℕ) : ℝ) := by
      rw [Nat.cast_mul ((N / B) * ((d - C_split) / 2)) b,
        Nat.cast_mul (N / B) ((d - C_split) / 2)]
      have hb_nn : (0 : ℝ) ≤ (b : ℝ) := by positivity
      exact mul_le_mul_of_nonneg_right (mul_le_mul hdivB_r hdiv2_r hpos_f2
        (hpos_f1.trans hdivB_r)) hb_nn
    have hB_eq : (B : ℝ) = 2 * (K₀ : ℝ) := by simp [B]
    have hK₀_r : (1 : ℝ) ≤ (K₀ : ℝ) := by exact_mod_cast hK₀_pos
    let ceil_term := ⌈(16 * coef_lin) / δ⌉₊
    have hlin_ge : (16 * coef_lin) / δ ≤ (d : ℝ) := by
      calc (16 * coef_lin) / δ
          ≤ (ceil_term : ℝ) := Nat.le_ceil _
        _ ≤ (d_lin : ℝ) := Nat.cast_le.mpr (by omega)
        _ ≤ (d : ℝ) := Nat.cast_le.mpr hd_ge_lin
    have hδd : 16 * coef_lin ≤ δ * (d : ℝ) := by
      have h1 := (div_le_iff₀ hδ).mp hlin_ge
      linarith only [h1]
    have hL_eq : (L : ℝ) = (d : ℝ) * (d : ℝ) * (b : ℝ) := by simp [L]
    have hident : ((δ₀ * (d : ℝ)) / (B : ℝ) - 1) * (((d : ℝ) - (C_split : ℝ) - 1) / 2) * (b : ℝ) =
        (δ₀ / (4 * (K₀ : ℝ))) * ((d : ℝ) * (d : ℝ) * (b : ℝ)) -
          ((δ₀ * ((C_split : ℝ) + 1)) / (4 * (K₀ : ℝ)) + 1 / 2) * ((d : ℝ) * (b : ℝ)) +
          (((C_split : ℝ) + 1) / 2) * (b : ℝ) := by
      rw [hB_eq]
      field_simp
      ring
    have herr_lin : ((δ₀ * ((C_split : ℝ) + 1)) / (4 * (K₀ : ℝ)) + 1 / 2) * ((d : ℝ) * (b : ℝ)) ≤
        (δ / 4) * ((d : ℝ) * (d : ℝ) * (b : ℝ)) := by
      have hcoef : (δ₀ * ((C_split : ℝ) + 1)) / (4 * (K₀ : ℝ)) + 1 / 2 ≤ coef_lin := by
        have hdiv_le : (δ₀ * ((C_split : ℝ) + 1)) / (4 * (K₀ : ℝ)) ≤ δ₀ * ((C_split : ℝ) + 1) :=
          div_le_self (by positivity) (by linarith only [hK₀_r])
        dsimp [coef_lin]
        linarith only [hdiv_le]
      have hdb_nn : (0 : ℝ) ≤ (d : ℝ) * (b : ℝ) := by positivity
      calc ((δ₀ * ((C_split : ℝ) + 1)) / (4 * (K₀ : ℝ)) + 1 / 2) * ((d : ℝ) * (b : ℝ))
          ≤ coef_lin * ((d : ℝ) * (b : ℝ)) := mul_le_mul_of_nonneg_right hcoef hdb_nn
        _ ≤ ((δ * (d : ℝ)) / 16) * ((d : ℝ) * (b : ℝ)) := by
            refine mul_le_mul_of_nonneg_right ?_ hdb_nn
            linarith only [hδd]
        _ = (δ / 16) * ((d : ℝ) * (d : ℝ) * (b : ℝ)) := by ring
        _ ≤ (δ / 4) * ((d : ℝ) * (d : ℝ) * (b : ℝ)) := by
            have hddb : (0 : ℝ) ≤ (d : ℝ) * (d : ℝ) * (b : ℝ) := by positivity
            exact mul_le_mul_of_nonneg_right (by linarith only [hδ]) hddb
    have hb_nn : (0 : ℝ) ≤ (((C_split : ℝ) + 1) / 2) * (b : ℝ) := by positivity
    rw [hL_eq]
    linarith only [hprod, hident, herr_lin, hb_nn]
  have hcard_r : (((N / B) * ((d - C_split) / 2) * b : ℕ) : ℝ) ≤
      (S_card : ℝ) + (C_cone : ℝ) * ((τ_cut : ℝ) + (A d : ℝ) + 1) +
        (B : ℝ) * (A d : ℝ) + 2 * (d : ℝ) * (E_pad d : ℝ) := by
    exact_mod_cast hcard_nat
  have hsplit_err : (C_cone : ℝ) * ((τ_cut : ℝ) + (A d : ℝ) + 1) +
      (B : ℝ) * (A d : ℝ) + 2 * (d : ℝ) * (E_pad d : ℝ) =
      (C_cone : ℝ) * ((τ_cut : ℝ) + 1) + ((C_cone : ℝ) + (B : ℝ)) * (A d : ℝ) +
        2 * (d : ℝ) * (E_pad d : ℝ) := by ring
  linarith only [hrect_r, hcard_r, hsplit_err, hτ_err, hA_err, hE_err]

/-- **Suffix Jitter-BM Storage-Code Bound (`suffixJitterBM_storageCode_log_le`)**:
for any fixed `(k, M_ph, D, C, δ₀ > 0)`, bank set `B_bank ⊆ Fin k`, and functions
`E_pad, A, S : ℕ → ℕ` with `(d * E_pad(d)) / L → 0`, `A(d) / L → 0`, and `S(d) / L → 0`
(`L = d² entryBits(d)`), binary storage codes on any scale-`1` frozen-trace cone relation
satisfying `TraceHasSuffixJitterBM` with `|R_suf| ≥ δ₀ d` have log-size at most
`(1 - δ₀ / (4 * K₀) + δ) * L` for all sufficiently large `d`. -/
theorem suffixJitterBM_storageCode_log_le {k M_ph D : ℕ} {C δ₀ : ℝ}
    (hC : 1 ≤ C) (hMph : 1 ≤ M_ph) (hδ₀ : 0 < δ₀) (B_bank : Finset (Fin k))
    {E_pad A S : ℕ → ℕ}
    (hE : Tendsto (fun d : ℕ => ((d * E_pad d : ℕ) : ℝ) / ((d * d * entryBits d : ℕ) : ℝ))
      atTop (nhds 0))
    (hA : Tendsto (fun d : ℕ => (A d : ℝ) / ((d * d * entryBits d : ℕ) : ℝ)) atTop (nhds 0))
    (hS : Tendsto (fun d : ℕ => (S d : ℝ) / ((d * d * entryBits d : ℕ) : ℝ)) atTop (nhds 0))
    {δ : ℝ} (hδ : 0 < δ) :
    let K₀ := (B_bank.card + 1) ^ (M_ph - 1)
    ∃ d₀ : ℕ, ∀ d ≥ d₀,
      let b := entryBits d
      let L := d * d * b
      ∀ (z : Tp k → ℕ → ℤ) (T t_suf : ℕ) (R_suf : Finset (Fin d)) (Γ : Finset ℕ) (ot : ℕ → ℕ),
        (T : ℝ) ≤ C * ((L : ℝ) + 1) →
        δ₀ * (d : ℝ) ≤ (R_suf.card : ℝ) →
        (∀ t₁ t₂, t₁ ≤ t₂ → z (some none) t₁ ≤ z (some none) t₂) →
        (∀ π, IsDepPath (fun j => skel 1 (z (some (some j)))) T π → LinNet.GFree Γ π →
          π.length ≤ D + 1) →
        (∀ q : Fin L, ot (MergeDepth.tpos d b q) < T ∧
          (MergeDepth.tpos d b q : ℤ) / (1 : ℕ) =
            z (some none) (ot (MergeDepth.tpos d b q)) / (1 : ℕ)) →
        TraceHasSuffixJitterBM z d b T t_suf M_ph B_bank R_suf (E_pad d) (A d) (S d) →
        ∀ Code : Finset (Fin L → Bool),
          IsStorageCode (MergeDepth.coneRel 1 z T Γ ot (fun q => MergeDepth.tpos d b q)) Code →
          Real.logb 2 Code.card ≤ (1 - δ₀ / (4 * (K₀ : ℝ)) + δ) * (L : ℝ) := by
  dsimp only
  set K₀ := (B_bank.card + 1) ^ (M_ph - 1)
  have hK₀_pos : 1 ≤ K₀ := Nat.one_le_pow _ _ (by omega)
  let B := 2 * K₀
  let C_split := (M_ph + 2) + M_ph * (K₀ * B)
  let C_cone := (k + 2) ^ D * (k + M_ph + M_ph * (K₀ * (B * (M_ph * (2 * k + 3)))))
  obtain ⟨d_asymp, hd_asymp⟩ := storage_bound_of_suffix_jitter_card_bound K₀ C_split C_cone
    hK₀_pos hC hδ₀ hδ hE hA hS
  refine ⟨max d_asymp 1,
    fun d hd z T t_suf R_suf Γ ot hT hR_ge hout_mono hdepth hot hBM Code hCode => ?_⟩
  have hd_ge : d_asymp ≤ d := (le_max_left _ _).trans hd
  have hd1 : 1 ≤ d := (le_max_right _ _).trans hd
  have hb1 : 1 ≤ entryBits d := one_le_entryBits d
  obtain ⟨S_ind, hInd, hcard_nat⟩ := suffixJitterBM_independent_exists hMph hd1 hb1
    hout_mono hdepth hot hBM
  have hlog := storageCode_log_le_of_independent hInd hCode
  have hasymp := hd_asymp d hd_ge T R_suf.card S_ind.card hT hR_ge hcard_nat
  exact hlog.trans hasymp

/-! ## §4. Simulator Suffix Preservation -/

/-- **Simulator Suffix Preservation (`native_machine_preserves_suffixJitterBM`)**:
if `M` halts on `w` at time `T_M` with
`TraceHasSuffixJitterBM (runWalks M w) d b T_M t_suf M_ph B_bank R_suf E_pad A_val S_val`
(`1 ≤ M_ph`), then `N := Native.machine M hs` (`hs : 0 < s`) halts on `w` at
`U := (10 * s + 1) * (T_M / s + 1) + s` and satisfies `TraceHasSuffixJitterBM` at
`U_suf := (10 * s + 1) * (t_suf / s)` with row-interior halo `E_pad + 12 * s + 1`, coarse
amplitude `A_val + 26 * s + 2`, and workspace cell bound `(26 * s + 3) * (S_val + 1)`. -/
theorem native_machine_preserves_suffixJitterBM (M : TM) {s : ℕ} (hs : 0 < s) (w : List Bool)
    {d b T_M t_suf M_ph E_pad A_val S_val : ℕ} (hMph : 1 ≤ M_ph)
    {B_bank : Finset (Fin M.k)} {R_suf : Finset (Fin d)}
    (H : Transpose.Tape.HaltsAt M w T_M)
    (hBM : TraceHasSuffixJitterBM (runWalks M w) d b T_M t_suf M_ph B_bank R_suf
      E_pad A_val S_val) :
    let U := (10 * s + 1) * (T_M / s + 1) + s
    let U_suf := (10 * s + 1) * (t_suf / s)
    Transpose.Tape.HaltsAt (Native.machine M hs) w U ∧
      TraceHasSuffixJitterBM (runWalks (Native.machine M hs) w) d b U U_suf M_ph B_bank R_suf
        (E_pad + 12 * s + 1) (A_val + 26 * s + 2) ((26 * s + 3) * (S_val + 1)) := by
  dsimp only
  classical
  set U := (10 * s + 1) * (T_M / s + 1) + s
  set U_suf := (10 * s + 1) * (t_suf / s)
  have hHaltN : Transpose.Tape.HaltsAt (Native.machine M hs) w U :=
    (Native.simulates_halt M hs w H).1
  obtain ⟨ht_suf_le, hout_suf, ⟨a, ha0, haM, ha, hin, hbank⟩, hwork, hno_pre⟩ := hBM
  have hjsuf_div : t_suf / s ≤ T_M / s := Nat.div_le_div_right ht_suf_le
  have hUsuf_le_U : U_suf ≤ U := by
    dsimp [U_suf, U]
    have hmul : (10 * s + 1) * (t_suf / s) ≤ (10 * s + 1) * (T_M / s + 1) :=
      Nat.mul_le_mul_left _ (hjsuf_div.trans (Nat.le_succ _))
    omega
  -- 1. Zero physical output at `U_suf = (10 * s + 1) * (t_suf / s)` via `Native.full_blocks`.
  have hout_Usuf : runWalks (Native.machine M hs) w (some none) U_suf ≤ 0 := by
    let j_suf := t_suf / s
    have hjsuf_le_tsuf : j_suf * s ≤ t_suf := Nat.div_mul_le_self t_suf s
    have hjsuf_le_TM : j_suf * s ≤ T_M := hjsuf_le_tsuf.trans ht_suf_le
    have Htr := (haltsAt_iff_trace T_M).mp H
    have halive : ∀ i < j_suf * s, transAt M w i ≠ none :=
      fun i hi h => Htr.1 i (hi.trans_le hjsuf_le_TM) ((Native.traceFrom_none_iff M w none i).mpr h)
    obtain ⟨r, ai, aw, out, hrun, _, _, _, hout_eq⟩ := Native.full_blocks M hs w j_suf halive
    change run (Native.machine M hs) w U_suf = _ at hrun
    have houtN : (run (Native.machine M hs) w U_suf).outRev = out := by
      rw [hrun]
      simp [Native.Frame.native, Native.anchored]
    have hlen_le_js : (out.length : ℤ) ≤ runWalks M w (some none) (j_suf * s) := by
      simp only [runWalks, hout_eq, List.length_append]
      omega
    have hlen_le_tsuf := hlen_le_js.trans (runWalks_out_mono M w hjsuf_le_tsuf)
    have hwalkN : runWalks (Native.machine M hs) w (some none) U_suf = (out.length : ℤ) := by
      simp [runWalks, houtN]
    linarith
  refine ⟨hHaltN, hUsuf_le_U, hout_Usuf, ?_⟩
  -- Helper for the degenerate suffix case `t_suf = T_M` (`U = U_suf + 11 * s + 1`).
  have hdeg_suffix : t_suf = T_M →
      (∃ b_ph : ℕ → ℕ, b_ph 0 = U_suf ∧ b_ph M_ph = U ∧ (∀ α < M_ph, b_ph α ≤ b_ph (α + 1)) ∧
        (∀ α < M_ph, CoarseMonoOnInterval (runWalks (Native.machine M hs) w none)
          (b_ph α) (b_ph (α + 1)) (A_val + 26 * s + 2)) ∧
        (∀ α < M_ph, ∀ j ∈ B_bank,
          CoarseMonoOnInterval (runWalks (Native.machine M hs) w (some (some j)))
            (b_ph α) (b_ph (α + 1)) (A_val + 26 * s + 2))) ∧
      (∀ wh : Fin M.k, wh ∉ B_bank →
        ((Finset.Ico U_suf U).image (runWalks (Native.machine M hs) w (some (some wh)))).card ≤
          (26 * s + 3) * (S_val + 1)) := by
    intro hts_eq
    have hU_eq : U = U_suf + 11 * s + 1 := by
      dsimp [U, U_suf]
      rw [hts_eq]
      ring
    let b_ph : ℕ → ℕ := fun α => if α = 0 then U_suf else U
    have hb0 : b_ph 0 = U_suf := rfl
    have hbM : b_ph M_ph = U := by simp only [b_ph, show M_ph ≠ 0 by omega, ↓reduceIte]
    have hble : ∀ α < M_ph, b_ph α ≤ b_ph (α + 1) := by
      intro α _
      simp only [b_ph, Nat.add_one_ne_zero, ↓reduceIte]
      split_ifs <;> omega
    have hwalk_bound : ∀ (c : Tp (Native.machine M hs).k) (u : ℕ), U_suf ≤ u → u < U →
        |runWalks (Native.machine M hs) w c u - runWalks (Native.machine M hs) w c U_suf| ≤
          (11 * s : ℤ) := by
      intro c u hlo hhi
      have hlip := walk_lip (runWalks_isWalk (Native.machine M hs) w c) U_suf (u - U_suf)
      rw [Nat.add_sub_of_le hlo] at hlip
      have hu_le : ((u - U_suf : ℕ) : ℤ) ≤ (11 * s : ℤ) := by omega
      exact hlip.trans hu_le
    refine ⟨⟨b_ph, hb0, hbM, hble, fun α _ => ?_, fun α _ j _ => ?_⟩, fun wh _ => ?_⟩
    · left
      intro t t' hbt htt' ht'b
      have hb_lo : U_suf ≤ b_ph α := by dsimp [b_ph]; split_ifs <;> omega
      have hb_hi : b_ph (α + 1) ≤ U := by simp [b_ph]
      have h1 := abs_le.mp (hwalk_bound none t (hb_lo.trans hbt) (by omega))
      have h2 := abs_le.mp (hwalk_bound none t' (hb_lo.trans (hbt.trans htt')) (by omega))
      omega
    · left
      intro t t' hbt htt' ht'b
      have hb_lo : U_suf ≤ b_ph α := by dsimp [b_ph]; split_ifs <;> omega
      have hb_hi : b_ph (α + 1) ≤ U := by simp [b_ph]
      have h1 := abs_le.mp (hwalk_bound (some (some j)) t (hb_lo.trans hbt) (by omega))
      have h2 := abs_le.mp (hwalk_bound (some (some j)) t' (hb_lo.trans (hbt.trans htt')) (by omega))
      omega
    · let z0 := runWalks (Native.machine M hs) w (some (some wh)) U_suf
      let box : Finset ℤ :=
        (Finset.range (22 * s + 1)).image fun i : ℕ => z0 - (11 * s : ℤ) + (i : ℤ)
      have hsub : (Finset.Ico U_suf U).image (runWalks (Native.machine M hs) w (some (some wh))) ⊆
          box := by
        intro y hy
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hy
        obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hu
        have h1 := abs_le.mp (hwalk_bound (some (some wh)) u hlo hhi)
        refine Finset.mem_image.mpr
          ⟨(runWalks (Native.machine M hs) w (some (some wh)) u - (z0 - (11 * s : ℤ))).toNat,
            Finset.mem_range.mpr (by omega), ?_⟩
        omega
      calc ((Finset.Ico U_suf U).image (runWalks (Native.machine M hs) w (some (some wh)))).card
          ≤ box.card := Finset.card_le_card hsub
        _ ≤ 22 * s + 1 := Finset.card_image_le.trans (by simp)
        _ ≤ (26 * s + 3) * (S_val + 1) := by nlinarith
  rcases Nat.eq_zero_or_pos T_M with rfl | hTM_pos
  · -- Instant-halt case `T_M = 0`: `t_suf = 0 = T_M` and `U_suf = 0`.
    have hts0 : t_suf = 0 := by omega
    obtain ⟨hphN, hwkN⟩ := hdeg_suffix hts0
    have hUsuf0 : U_suf = 0 := by dsimp [U_suf]; rw [hts0]; simp
    refine ⟨hphN, hwkN, ?_⟩
    intro u hu
    omega
  · -- Main case `1 ≤ T_M`: set up base clock `π_M` and uniform `12 * s + 1` tracking on `[0, U)`.
    let j₀ : ℕ → ℕ := fun u => min (T_M / s) (u / (10 * s + 1))
    let π_M : ℕ → ℕ := fun u => min (T_M - 1) (j₀ u * s)
    have hπ_mono : ∀ {u₁ u₂ : ℕ}, u₁ ≤ u₂ → π_M u₁ ≤ π_M u₂ := by
      intro u₁ u₂ hle
      have hj : j₀ u₁ ≤ j₀ u₂ := min_le_min le_rfl (Nat.div_le_div_right hle)
      exact min_le_min le_rfl (Nat.mul_le_mul_right s hj)
    have hπ_lt : ∀ u : ℕ, π_M u < T_M := fun u =>
      (min_le_left _ _).trans_lt (by omega)
    have htrack : ∀ (u : ℕ), u < U →
        |runWalks (Native.machine M hs) w none u - runWalks M w none (π_M u)| ≤
          (12 * s + 1 : ℤ) ∧
        ∀ h : Fin M.k,
          |runWalks (Native.machine M hs) w (some (some h)) u -
              runWalks M w (some (some h)) (π_M u)| ≤
            (12 * s + 1 : ℤ) := by
      intro u hu
      have hj_le : j₀ u ≤ T_M / s := min_le_left _ _
      have hu_lo : (10 * s + 1) * j₀ u ≤ u := by
        calc (10 * s + 1) * j₀ u
            ≤ (10 * s + 1) * (u / (10 * s + 1)) := Nat.mul_le_mul_left _ (min_le_right _ _)
          _ ≤ u := Nat.mul_div_le u (10 * s + 1)
      have hu_hi : u ≤ (10 * s + 1) * j₀ u + 11 * s := by
        by_cases hdiv : u / (10 * s + 1) ≤ T_M / s
        · have hj_eq : j₀ u = u / (10 * s + 1) := min_eq_right hdiv
          have hmod := Nat.div_add_mod u (10 * s + 1)
          have hrem := Nat.mod_lt u (by omega : 0 < 10 * s + 1)
          rw [hj_eq]
          omega
        · have hj_eq : j₀ u = T_M / s := min_eq_left (by omega)
          have hU_def : U = (10 * s + 1) * (T_M / s) + 11 * s + 1 := by dsimp [U]; ring
          rw [hj_eq]
          omega
      have hπ_lo : π_M u ≤ j₀ u * s := min_le_right _ _
      have hjs_le_TM : j₀ u * s ≤ T_M :=
        (Nat.mul_le_mul_right s hj_le).trans (Nat.div_mul_le_self T_M s)
      have hπ_hi : j₀ u * s ≤ π_M u + 1 := by dsimp [π_M]; omega
      obtain ⟨hb_in, hb_wk⟩ := native_boundary_head_dist M hs w H hj_le
      refine ⟨?_, fun h => ?_⟩
      · have hlipN := walk_lip (runWalks_isWalk (Native.machine M hs) w none)
          ((10 * s + 1) * j₀ u) (u - (10 * s + 1) * j₀ u)
        rw [Nat.add_sub_of_le hu_lo] at hlipN
        have hlipM := walk_lip (runWalks_isWalk M w none) (π_M u) (j₀ u * s - π_M u)
        rw [Nat.add_sub_of_le hπ_lo] at hlipM
        have hd1 : ((u - (10 * s + 1) * j₀ u : ℕ) : ℤ) ≤ (11 * s : ℤ) := by omega
        have hd2 : ((j₀ u * s - π_M u : ℕ) : ℤ) ≤ 1 := by omega
        have h1 := abs_le.mp (hlipN.trans hd1)
        have h2 := abs_le.mp hb_in
        have h3 := abs_le.mp (hlipM.trans hd2)
        rw [abs_le]
        constructor <;> omega
      · have hlipN := walk_lip (runWalks_isWalk (Native.machine M hs) w (some (some h)))
          ((10 * s + 1) * j₀ u) (u - (10 * s + 1) * j₀ u)
        rw [Nat.add_sub_of_le hu_lo] at hlipN
        have hlipM := walk_lip (runWalks_isWalk M w (some (some h))) (π_M u) (j₀ u * s - π_M u)
        rw [Nat.add_sub_of_le hπ_lo] at hlipM
        have hd1 : ((u - (10 * s + 1) * j₀ u : ℕ) : ℤ) ≤ (11 * s : ℤ) := by omega
        have hd2 : ((j₀ u * s - π_M u : ℕ) : ℤ) ≤ 1 := by omega
        have h1 := abs_le.mp (hlipN.trans hd1)
        have h2 := abs_le.mp (hb_wk h)
        have h3 := abs_le.mp (hlipM.trans hd2)
        rw [abs_le]
        constructor <;> omega
    -- 2. Prefix row-interior halo `E_pad + 12 * s + 1` on `[0, U_suf)`.
    have hno_pre_N : ∀ u < U_suf, ∀ i ∈ R_suf,
        ¬ (((i.1 * (d * b) + (E_pad + 12 * s + 1) : ℕ) : ℤ) ≤
              runWalks (Native.machine M hs) w none u ∧
            runWalks (Native.machine M hs) w none u <
              (((i.1 + 1) * (d * b) : ℕ) : ℤ) - ((E_pad + 12 * s + 1 : ℕ) : ℤ)) := by
      intro u hu_suf i hi hbandN
      have hu_U : u < U := hu_suf.trans_le hUsuf_le_U
      have hdiv_lt : u / (10 * s + 1) < t_suf / s := by
        rw [Nat.div_lt_iff_lt_mul (by omega : 0 < 10 * s + 1), Nat.mul_comm]
        exact hu_suf
      have hj_lt : j₀ u < t_suf / s := (min_le_right _ _).trans_lt hdiv_lt
      have hjs_lt : j₀ u * s < t_suf := by
        calc j₀ u * s < (j₀ u + 1) * s := by rw [Nat.add_mul, Nat.one_mul]; omega
          _ ≤ (t_suf / s) * s := Nat.mul_le_mul_right s hj_lt
          _ ≤ t_suf := Nat.div_mul_le_self t_suf s
      have hπ_lt_tsuf : π_M u < t_suf := (min_le_right _ _).trans_lt hjs_lt
      have hd_in := abs_le.mp (htrack u hu_U).1
      apply hno_pre (π_M u) hπ_lt_tsuf i hi
      omega
    -- 3. Suffix phases & workspace on `[U_suf, U)`.
    rcases eq_or_lt_of_le ht_suf_le with hts_eq | hts_lt
    · obtain ⟨hphN, hwkN⟩ := hdeg_suffix hts_eq
      exact ⟨hphN, hwkN, hno_pre_N⟩
    · -- Nondegenerate suffix `t_suf < T_M`: use clamped suffix clock `π_suf u := max t_suf (π_M u)`.
      let π_suf : ℕ → ℕ := fun u => max t_suf (π_M u)
      have hπs_mono : ∀ {u₁ u₂ : ℕ}, u₁ ≤ u₂ → π_suf u₁ ≤ π_suf u₂ :=
        fun hle => max_le_max le_rfl (hπ_mono hle)
      have hπs_lo : ∀ u : ℕ, t_suf ≤ π_suf u := fun _ => le_max_left _ _
      have hπs_lt : ∀ u : ℕ, π_suf u < T_M := fun u => max_lt hts_lt (hπ_lt u)
      have htrack_suf : ∀ u : ℕ, U_suf ≤ u → u < U →
          |runWalks (Native.machine M hs) w none u - runWalks M w none (π_suf u)| ≤
            (13 * s + 1 : ℤ) ∧
          ∀ h : Fin M.k,
            |runWalks (Native.machine M hs) w (some (some h)) u -
                runWalks M w (some (some h)) (π_suf u)| ≤
              (13 * s + 1 : ℤ) := by
        intro u hu_lo hu_hi
        have hdiv_ge : t_suf / s ≤ u / (10 * s + 1) := by
          rw [Nat.le_div_iff_mul_le (by omega : 0 < 10 * s + 1), Nat.mul_comm]
          exact hu_lo
        have hj_ge : t_suf / s ≤ j₀ u := le_min hjsuf_div hdiv_ge
        have hts_le_js : t_suf ≤ j₀ u * s + s := by
          have hmod := Nat.div_add_mod t_suf s
          have hrem := Nat.mod_lt t_suf hs
          have hmul : (t_suf / s) * s ≤ j₀ u * s := Nat.mul_le_mul_right s hj_ge
          have hcomm : s * (t_suf / s) = (t_suf / s) * s := Nat.mul_comm _ _
          omega
        have hπ_le_πs : π_M u ≤ π_suf u := le_max_right _ _
        have hπs_le_π : π_suf u ≤ π_M u + s := by
          dsimp [π_suf, π_M]
          omega
        have hd_step : ((π_suf u - π_M u : ℕ) : ℤ) ≤ (s : ℤ) := by omega
        obtain ⟨ht_in, ht_wk⟩ := htrack u hu_hi
        refine ⟨?_, fun h => ?_⟩
        · have hlip := walk_lip (runWalks_isWalk M w none) (π_M u) (π_suf u - π_M u)
          rw [Nat.add_sub_of_le hπ_le_πs] at hlip
          have h1 := abs_le.mp ht_in
          have h2 := abs_le.mp (hlip.trans hd_step)
          rw [abs_le]
          constructor <;> omega
        · have hlip := walk_lip (runWalks_isWalk M w (some (some h))) (π_M u) (π_suf u - π_M u)
          rw [Nat.add_sub_of_le hπ_le_πs] at hlip
          have h1 := abs_le.mp (ht_wk h)
          have h2 := abs_le.mp (hlip.trans hd_step)
          rw [abs_le]
          constructor <;> omega
      -- Pull back suffix phase boundaries `a` along `π_suf` on `Finset.Ico U_suf U`.
      let F_set : ℕ → Finset ℕ := fun α => (Finset.Ico U_suf U).filter fun u => a α ≤ π_suf u
      let b_ph : ℕ → ℕ := fun α =>
        if α = 0 then U_suf
        else if M_ph ≤ α then U
        else if h : (F_set α).Nonempty then (F_set α).min' h else U
      have hb0 : b_ph 0 = U_suf := rfl
      have hbM : b_ph M_ph = U := by
        simp only [b_ph, show M_ph ≠ 0 by omega, le_rfl, ↓reduceIte]
      have hb_bounds : ∀ α : ℕ, U_suf ≤ b_ph α ∧ b_ph α ≤ U := by
        intro α
        dsimp [b_ph]
        split_ifs with h1 h2 h3
        · exact ⟨le_rfl, hUsuf_le_U⟩
        · exact ⟨hUsuf_le_U, le_rfl⟩
        · obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp (Finset.mem_filter.mp (Finset.min'_mem _ h3)).1
          exact ⟨hlo, hhi.le⟩
        · exact ⟨hUsuf_le_U, le_rfl⟩
      have hble : ∀ α < M_ph, b_ph α ≤ b_ph (α + 1) := by
        intro α hα
        rcases Nat.eq_zero_or_pos α with rfl | hα_pos
        · rw [hb0]; exact (hb_bounds 1).1
        · by_cases htop : α + 1 = M_ph
          · rw [htop, hbM]; exact (hb_bounds α).2
          · have hsubF : F_set (α + 1) ⊆ F_set α := by
              intro u hu
              obtain ⟨huIco, hle⟩ := Finset.mem_filter.mp hu
              exact Finset.mem_filter.mpr ⟨huIco, (ha α hα).trans hle⟩
            have hb_α : b_ph α = if h : (F_set α).Nonempty then (F_set α).min' h else U := by
              simp only [b_ph, show α ≠ 0 by omega, show ¬ M_ph ≤ α by omega, ↓reduceIte]
            have hb_α1 : b_ph (α + 1) =
                if h : (F_set (α + 1)).Nonempty then (F_set (α + 1)).min' h else U := by
              simp only [b_ph, Nat.add_one_ne_zero, show ¬ M_ph ≤ α + 1 by omega, ↓reduceIte]
            by_cases hne2 : (F_set (α + 1)).Nonempty
            · have hne1 : (F_set α).Nonempty := hne2.mono hsubF
              rw [hb_α, hb_α1]
              simp only [hne1, hne2, ↓reduceDIte]
              exact Finset.min'_le _ _ (hsubF (Finset.min'_mem _ hne2))
            · rw [hb_α1]
              simp only [hne2, ↓reduceDIte]
              exact (hb_bounds α).2
      have hb_interval : ∀ α < M_ph, ∀ u : ℕ, b_ph α ≤ u → u < b_ph (α + 1) →
          U_suf ≤ u ∧ u < U ∧ a α ≤ π_suf u ∧ π_suf u < a (α + 1) := by
        intro α hα u hbu hub1
        have hu_lo : U_suf ≤ u := (hb_bounds α).1.trans hbu
        have huU : u < U := hub1.trans_le (hb_bounds (α + 1)).2
        refine ⟨hu_lo, huU, ?_, ?_⟩
        · rcases Nat.eq_zero_or_pos α with rfl | hα_pos
          · rw [ha0]; exact hπs_lo u
          · have hb_α : b_ph α = if h : (F_set α).Nonempty then (F_set α).min' h else U := by
              simp only [b_ph, show α ≠ 0 by omega, show ¬ M_ph ≤ α by omega, ↓reduceIte]
            rw [hb_α] at hbu
            by_cases hne : (F_set α).Nonempty
            · simp only [hne, ↓reduceDIte] at hbu
              have hmin := (Finset.mem_filter.mp (Finset.min'_mem _ hne)).2
              exact hmin.trans (hπs_mono hbu)
            · simp only [hne, ↓reduceDIte] at hbu
              omega
        · by_cases htop : α + 1 = M_ph
          · rw [htop, haM]; exact hπs_lt u
          · have hb_α1 : b_ph (α + 1) =
                if h : (F_set (α + 1)).Nonempty then (F_set (α + 1)).min' h else U := by
              simp only [b_ph, Nat.add_one_ne_zero, show ¬ M_ph ≤ α + 1 by omega, ↓reduceIte]
            rw [hb_α1] at hub1
            by_contra hge
            have hu_mem : u ∈ F_set (α + 1) :=
              Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hu_lo, huU⟩, by omega⟩
            have hne : (F_set (α + 1)).Nonempty := ⟨u, hu_mem⟩
            simp only [hne, ↓reduceDIte] at hub1
            have hle := Finset.min'_le _ _ hu_mem
            omega
      refine ⟨⟨b_ph, hb0, hbM, hble, fun α hα => ?_, fun α hα j hj => ?_⟩, fun wh hwh => ?_,
        hno_pre_N⟩
      · rcases hin α hα with hinc | hdec
        · left
          intro t t' hbt htt' ht'b
          obtain ⟨ht_lo, htU, hπt_lo, _⟩ := hb_interval α hα t hbt (htt'.trans_lt ht'b)
          obtain ⟨ht'_lo, ht'U, _, hπt'_hi⟩ := hb_interval α hα t' (hbt.trans htt') ht'b
          have hM := hinc (π_suf t) (π_suf t') hπt_lo (hπs_mono htt') hπt'_hi
          have hd1 := abs_le.mp (htrack_suf t ht_lo htU).1
          have hd2 := abs_le.mp (htrack_suf t' ht'_lo ht'U).1
          omega
        · right
          intro t t' hbt htt' ht'b
          obtain ⟨ht_lo, htU, hπt_lo, _⟩ := hb_interval α hα t hbt (htt'.trans_lt ht'b)
          obtain ⟨ht'_lo, ht'U, _, hπt'_hi⟩ := hb_interval α hα t' (hbt.trans htt') ht'b
          have hM := hdec (π_suf t) (π_suf t') hπt_lo (hπs_mono htt') hπt'_hi
          have hd1 := abs_le.mp (htrack_suf t ht_lo htU).1
          have hd2 := abs_le.mp (htrack_suf t' ht'_lo ht'U).1
          omega
      · rcases hbank α hα j hj with hinc | hdec
        · left
          intro t t' hbt htt' ht'b
          obtain ⟨ht_lo, htU, hπt_lo, _⟩ := hb_interval α hα t hbt (htt'.trans_lt ht'b)
          obtain ⟨ht'_lo, ht'U, _, hπt'_hi⟩ := hb_interval α hα t' (hbt.trans htt') ht'b
          have hM := hinc (π_suf t) (π_suf t') hπt_lo (hπs_mono htt') hπt'_hi
          have hd1 := abs_le.mp ((htrack_suf t ht_lo htU).2 j)
          have hd2 := abs_le.mp ((htrack_suf t' ht'_lo ht'U).2 j)
          omega
        · right
          intro t t' hbt htt' ht'b
          obtain ⟨ht_lo, htU, hπt_lo, _⟩ := hb_interval α hα t hbt (htt'.trans_lt ht'b)
          obtain ⟨ht'_lo, ht'U, _, hπt'_hi⟩ := hb_interval α hα t' (hbt.trans htt') ht'b
          have hM := hdec (π_suf t) (π_suf t') hπt_lo (hπs_mono htt') hπt'_hi
          have hd1 := abs_le.mp ((htrack_suf t ht_lo htU).2 j)
          have hd2 := abs_le.mp ((htrack_suf t' ht'_lo ht'U).2 j)
          omega
      · -- Bound suffix visited workspace cells of `N` by `(26 * s + 3) * (S_val + 1)`.
        let C_M := (Finset.Ico t_suf T_M).image (runWalks M w (some (some wh)))
        have hCM : C_M.card ≤ S_val := hwork wh hwh
        let winOf : ℤ → Finset ℤ := fun y =>
          (Finset.range (26 * s + 3)).image fun i : ℕ => y - (13 * s + 1 : ℤ) + (i : ℤ)
        have hsub : (Finset.Ico U_suf U).image (runWalks (Native.machine M hs) w (some (some wh))) ⊆
            C_M.biUnion winOf := by
          intro z hz
          obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
          obtain ⟨hu_lo, huU⟩ := Finset.mem_Ico.mp hu
          have hy_mem : runWalks M w (some (some wh)) (π_suf u) ∈ C_M :=
            Finset.mem_image_of_mem _ (Finset.mem_Ico.mpr ⟨hπs_lo u, hπs_lt u⟩)
          have hd := abs_le.mp ((htrack_suf u hu_lo huU).2 wh)
          refine Finset.mem_biUnion.mpr ⟨runWalks M w (some (some wh)) (π_suf u), hy_mem, ?_⟩
          refine Finset.mem_image.mpr
            ⟨(runWalks (Native.machine M hs) w (some (some wh)) u -
                (runWalks M w (some (some wh)) (π_suf u) - (13 * s + 1 : ℤ))).toNat,
              Finset.mem_range.mpr (by omega), ?_⟩
          omega
        calc ((Finset.Ico U_suf U).image (runWalks (Native.machine M hs) w (some (some wh)))).card
            ≤ (C_M.biUnion winOf).card := Finset.card_le_card hsub
          _ ≤ ∑ y ∈ C_M, (winOf y).card := Finset.card_biUnion_le
          _ ≤ ∑ _y ∈ C_M, (26 * s + 3) :=
              Finset.sum_le_sum fun _ _ => Finset.card_image_le.trans (by simp)
          _ = C_M.card * (26 * s + 3) := by simp
          _ ≤ S_val * (26 * s + 3) := Nat.mul_le_mul_right _ hCM
          _ ≤ (26 * s + 3) * (S_val + 1) := by nlinarith

/-! ## §5. Unconditional Exclusion of Adaptive Suffix-BM Linear-Time Transposers (Theorem 9.4 / Theorem J) -/

/-- **Theorem 9.4 Native-Gap Bound (`nativeGapBound_of_adaptiveSuffixJitterBM`)**:
if `M` satisfies `AdaptiveSuffixJitterBM M c M_ph δ₀ B_bank A S` (`0 < δ₀`) with `A = o(L)` and
`S = o(L)`, then for every batch size `s > 0` and genie depth `D`, `Native.machine M hs` satisfies
`NativeGapBound (δ₀ / (4 * K₀))` at scale `1` and physical time constant `11 * c + 1` on
`B d b := (b = entryBits d ∧ TransposesAt M d c)`. -/
theorem nativeGapBound_of_adaptiveSuffixJitterBM {M : TM} {c : ℝ} (hc : 0 < c)
    {M_ph : ℕ} (hMph : 1 ≤ M_ph) {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    {B_bank : Finset (Fin M.k)} {A S : ℕ → ℕ}
    (hBM : AdaptiveSuffixJitterBM M c M_ph δ₀ B_bank A S)
    (hA : Tendsto (fun d : ℕ => (A d : ℝ) / ((d * d * entryBits d : ℕ) : ℝ)) atTop (nhds 0))
    (hS : Tendsto (fun d : ℕ => (S d : ℝ) / ((d * d * entryBits d : ℕ) : ℝ)) atTop (nhds 0))
    {s : ℕ} (hs : 0 < s) (D : ℕ) :
    let K₀ : ℝ := (((B_bank.card + 1) ^ (M_ph - 1) : ℕ) : ℝ)
    NativeGapBound (δ₀ / (4 * K₀)) (fun d b => b = entryBits d ∧ TransposesAt M d c)
      (Native.machine M hs) 1 D (11 * c + 1) := by
  dsimp only
  intro δ hδ
  set N := Native.machine M hs
  have hc' : 1 ≤ 11 * c + 1 := by linarith
  obtain ⟨d_BM, hd_BM⟩ := hBM
  let E' : ℕ → ℕ := fun _ => 12 * s + 1
  let A' : ℕ → ℕ := fun d => A d + 26 * s + 2
  let S' : ℕ → ℕ := fun d => (26 * s + 3) * (S d + 1)
  have hconst_db : ∀ K : ℕ,
      Tendsto (fun d : ℕ => (K : ℝ) / ((d * entryBits d : ℕ) : ℝ)) atTop (nhds 0) := by
    intro K
    have hinv : Tendsto (fun d : ℕ => (K : ℝ) * ((d : ℝ)⁻¹)) atTop (nhds 0) := by
      simpa using (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul (K : ℝ)
    refine squeeze_zero_norm' ?_ hinv
    filter_upwards [eventually_ge_atTop 1] with d hd
    rw [Real.norm_of_nonneg (by positivity)]
    have hle : d ≤ d * entryBits d := by
      calc d = d * 1 := by ring
        _ ≤ d * entryBits d := Nat.mul_le_mul_left d (one_le_entryBits d)
    have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    rw [← div_eq_mul_inv]
    exact div_le_div_of_nonneg_left (by positivity) hd_pos (by exact_mod_cast hle)
  have hconst_o : ∀ K : ℕ,
      Tendsto (fun d : ℕ => (K : ℝ) / ((d * d * entryBits d : ℕ) : ℝ)) atTop (nhds 0) :=
    fun K => tendsto_div_L_of_tendsto_div_db (hconst_db K)
  have hE' : Tendsto (fun d : ℕ => ((d * E' d : ℕ) : ℝ) / ((d * d * entryBits d : ℕ) : ℝ))
      atTop (nhds 0) := by
    refine squeeze_zero_norm' ?_ (hconst_db (12 * s + 1))
    filter_upwards [eventually_ge_atTop 1] with d hd
    rw [Real.norm_of_nonneg (by positivity)]
    have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    have heq : ((d * E' d : ℕ) : ℝ) / ((d * d * entryBits d : ℕ) : ℝ) =
        ((12 * s + 1 : ℕ) : ℝ) / ((d * entryBits d : ℕ) : ℝ) := by
      dsimp [E']
      push_cast
      field_simp [hd_pos.ne']
    exact heq.le
  have hA' : Tendsto (fun d : ℕ => (A' d : ℝ) / ((d * d * entryBits d : ℕ) : ℝ)) atTop (nhds 0) := by
    have hsum := hA.add (hconst_o (26 * s + 2))
    rw [add_zero] at hsum
    refine hsum.congr fun d => ?_
    dsimp [A']
    push_cast
    ring
  have hS' : Tendsto (fun d : ℕ => (S' d : ℝ) / ((d * d * entryBits d : ℕ) : ℝ)) atTop (nhds 0) := by
    have h1 := hS.add (hconst_o 1)
    rw [add_zero] at h1
    have h2 := h1.const_mul ((26 * s + 3 : ℕ) : ℝ)
    rw [mul_zero] at h2
    refine h2.congr fun d => ?_
    dsimp [S']
    push_cast
    ring
  obtain ⟨d_code, hd_code⟩ := suffixJitterBM_storageCode_log_le (k := N.k) (D := D)
    hc' hMph hδ₀ B_bank hE' hA' hS' hδ
  refine ⟨max d_BM d_code, fun d hd b ⟨hb_eq, htrM⟩ X T_N hHaltN hTN Γ hdepth ot hot Code hCode => ?_⟩
  subst hb_eq
  have hd_ge_BM : d_BM ≤ d := (le_max_left _ _).trans hd
  have hd_ge_code : d_code ≤ d := (le_max_right _ _).trans hd
  obtain ⟨T_M, hTM_floor, hHaltM⟩ := (htrM.transposesInput X).halts
  have hTM_real : (T_M : ℝ) ≤ c * (((d * d * entryBits d : ℕ) : ℝ) + 1) :=
    (Nat.cast_le.mpr hTM_floor).trans (Nat.floor_le (by positivity))
  obtain ⟨t_suf, R_suf, hR_ge, hBM_M⟩ := hd_BM d hd_ge_BM X T_M hHaltM hTM_real
  obtain ⟨hHaltN_sim, hBM_N⟩ :=
    native_machine_preserves_suffixJitterBM M hs (List.ofFn X) hMph hHaltM hBM_M
  have hTN_eq : T_N = (10 * s + 1) * (T_M / s + 1) + s :=
    Transpose.Tape.Impl.haltsAt_unique hHaltN hHaltN_sim
  subst hTN_eq
  have hBM_N' : TraceHasSuffixJitterBM (runWalks N (List.ofFn X)) d (entryBits d)
      ((10 * s + 1) * (T_M / s + 1) + s) ((10 * s + 1) * (t_suf / s)) M_ph B_bank R_suf
      (E' d) (A' d) (S' d) := by
    simpa [E', A', S'] using hBM_N
  exact hd_code d hd_ge_code (runWalks N (List.ofFn X)) _ _ R_suf Γ ot hTN hR_ge
    (fun t₁ t₂ hle => runWalks_out_mono N (List.ofFn X) hle) hdepth hot hBM_N' Code hCode

/-- **Theorem 9.4 Single-Constant Exclusion (`adaptiveSuffixJitterBM_excludes_transposesAt`)**:
if every halting run of `M` within `c (L + 1)` steps admits a suffix `[t_suf, T)` of jittered BM
shape (`A(d) = o(L)`, `S(d) = o(L)`) leaving `≥ δ₀ d` raw rows untouched in `[0, t_suf)`, then `M`
fails to transpose at width `entryBits d` within `c (L + 1)` steps for all sufficiently large `d`. -/
theorem adaptiveSuffixJitterBM_excludes_transposesAt {M : TM} {c : ℝ} (hc : 0 < c)
    {M_ph : ℕ} (hMph : 1 ≤ M_ph) {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    {B_bank : Finset (Fin M.k)} {A S : ℕ → ℕ}
    (hBM : AdaptiveSuffixJitterBM M c M_ph δ₀ B_bank A S)
    (hA : Tendsto (fun d : ℕ => (A d : ℝ) / ((d * d * entryBits d : ℕ) : ℝ)) atTop (nhds 0))
    (hS : Tendsto (fun d : ℕ => (S d : ℝ) / ((d * d * entryBits d : ℕ) : ℝ)) atTop (nhds 0)) :
    ∀ᶠ d in atTop, ¬ TransposesAt M d c := by
  set K₀ : ℝ := (((B_bank.card + 1) ^ (M_ph - 1) : ℕ) : ℝ)
  have hK₀_pos : (0 : ℝ) < K₀ := by dsimp [K₀]; positivity
  set ρ : ℝ := δ₀ / (4 * K₀)
  have hρ : 0 < ρ := by positivity
  set η : ℝ := ρ / 2
  have hη0 : 0 < η := by positivity
  have hηρ : η < ρ := by dsimp [η]; linarith
  obtain ⟨s, hs, hlow⟩ := aligned_low_trace_dimensions M hc.le hη0
  set N := Native.machine M hs
  set c' : ℝ := 11 * c + 1
  have hc' : 0 < c' := by dsimp [c']; linarith
  let D_genie := genieDepth N.k (blockWidth N 1) (max c' 1) ((ρ - η) / 2)
  have hnat := nativeGapBound_of_adaptiveSuffixJitterBM hc hMph hδ₀ hBM hA hS hs D_genie
  obtain ⟨d₀, hd₀⟩ := fSecond_native_gap (ρ := ρ)
    (B := fun d b => b = entryBits d ∧ TransposesAt M d c)
    (M := N) (c := c') (η := η) hc' hηρ hnat
  filter_upwards [eventually_ge_atTop d₀, hlow] with d hd htr_low
  intro htrM
  obtain ⟨htrN, hsize⟩ := htr_low (entryBits d) (one_le_entryBits d) htrM
  have hent_le := (skeleton_entropy_le_trace_support N 1
    (fun x : Fin (d * d * entryBits d) → Bool => List.ofFn x)).trans hsize
  have hent_gt := hd₀ d hd (entryBits d) ⟨rfl, htrM⟩ (one_le_entryBits d) htrN.transposesInput
  exact (not_lt_of_ge hent_le) hent_gt

/-- **Theorem 9.4 Fixed-Slope Exclusion (`adaptiveSuffixJitterBM_excludes_transposesWithin`)**:
excludes `TransposesWithin M (fun L => c * (L + 1))` for any adaptive machine `M` satisfying
`AdaptiveSuffixJitterBM M (max (c : ℝ) 1) M_ph δ₀ B_bank A S` (`1 ≤ M_ph`, `0 < δ₀`, `A = o(L)`,
`S = o(L)`). -/
theorem adaptiveSuffixJitterBM_excludes_transposesWithin {M : TM} {c : ℕ}
    {M_ph : ℕ} (hMph : 1 ≤ M_ph) {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    {B_bank : Finset (Fin M.k)} {A S : ℕ → ℕ}
    (hBM : AdaptiveSuffixJitterBM M (max (c : ℝ) 1) M_ph δ₀ B_bank A S)
    (hA : Tendsto (fun d : ℕ => (A d : ℝ) / ((d * d * entryBits d : ℕ) : ℝ)) atTop (nhds 0))
    (hS : Tendsto (fun d : ℕ => (S d : ℝ) / ((d * d * entryBits d : ℕ) : ℝ)) atTop (nhds 0)) :
    ¬ TransposesWithin M (fun L => c * (L + 1)) := by
  intro htr
  have hc_pos : (0 : ℝ) < max (c : ℝ) 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hev := adaptiveSuffixJitterBM_excludes_transposesAt hc_pos hMph hδ₀ hBM hA hS
  obtain ⟨d₀, hd₀⟩ := eventually_atTop.mp hev
  let d := max d₀ 1
  have hd_ge : d₀ ≤ d := le_max_left _ _
  have hd1 : 1 ≤ d := le_max_right _ _
  have htr_c : TransposesAt M d c := transposesAt_of_transposesWithin htr hd1
  have htr_max : TransposesAt M d (max (c : ℝ) 1) := by
    intro A_mat
    obtain ⟨s, hs, hrest⟩ := htr_c A_mat
    refine ⟨s, hs.trans ?_, hrest⟩
    exact Nat.floor_mono (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  exact hd₀ d hd_ge htr_max

/-- **Theorem 9.4 Linear-Time Exclusion (`adaptiveSuffixJitterBM_not_linearTimeTransposer`)**:
if for every runtime constant `C ≥ 1`, all halting runs of `M` within `C (L + 1)` steps have a
suffix `[t_suf, T)` of jittered BM shape (`1 ≤ M_ph`, `0 < δ₀`, `A = o(L)`, `S = o(L)`), then `M`
is not a linear-time matrix transposer (`¬ ∃ c : ℕ, TransposesWithin M (fun L => c * (L + 1))`). -/
theorem adaptiveSuffixJitterBM_not_linearTimeTransposer (M : TM)
    (h : ∀ C : ℝ, 1 ≤ C →
      ∃ (M_ph : ℕ) (δ₀ : ℝ) (B_bank : Finset (Fin M.k)) (A S : ℕ → ℕ),
        1 ≤ M_ph ∧ 0 < δ₀ ∧
        AdaptiveSuffixJitterBM M C M_ph δ₀ B_bank A S ∧
        Tendsto (fun d : ℕ => (A d : ℝ) / ((d * d * entryBits d : ℕ) : ℝ)) atTop (nhds 0) ∧
        Tendsto (fun d : ℕ => (S d : ℝ) / ((d * d * entryBits d : ℕ) : ℝ)) atTop (nhds 0)) :
    ¬ ∃ c : ℕ, TransposesWithin M (fun L => c * (L + 1)) := by
  rintro ⟨c, htr⟩
  obtain ⟨M_ph, δ₀, B_bank, A, S, hMph, hδ₀, hBM, hA, hS⟩ :=
    h (max (c : ℝ) 1) (le_max_right _ _)
  exact adaptiveSuffixJitterBM_excludes_transposesWithin hMph hδ₀ hBM hA hS htr

/-! ## Whole-Run `AdaptiveJitterBM` Corollaries (`δ₀ = 1` Specialization) -/

/-- If `M` satisfies `AdaptiveJitterBM M c M_ph B_bank A S` with `A = o(L)` and `S = o(L)`, then for
every batch size `s > 0` and every genie depth `D`, the aligned simulator `Native.machine M hs`
satisfies `NativeGapBound (1 / (4 * K₀))` at scale `1` and time constant `11 * c + 1`. -/
theorem nativeGapBound_of_adaptiveJitterBM {M : TM} {c : ℝ} (hc : 0 < c)
    {M_ph : ℕ} (hMph : 1 ≤ M_ph) {B_bank : Finset (Fin M.k)} {A S : ℕ → ℕ}
    (hBM : AdaptiveJitterBM M c M_ph B_bank A S)
    (hA : Tendsto (fun d : ℕ => (A d : ℝ) / ((d * d * entryBits d : ℕ) : ℝ)) atTop (nhds 0))
    (hS : Tendsto (fun d : ℕ => (S d : ℝ) / ((d * d * entryBits d : ℕ) : ℝ)) atTop (nhds 0))
    {s : ℕ} (hs : 0 < s) (D : ℕ) :
    let K₀ : ℝ := (((B_bank.card + 1) ^ (M_ph - 1) : ℕ) : ℝ)
    NativeGapBound (1 / (4 * K₀)) (fun d b => b = entryBits d ∧ TransposesAt M d c)
      (Native.machine M hs) 1 D (11 * c + 1) :=
  nativeGapBound_of_adaptiveSuffixJitterBM hc hMph zero_lt_one
    (adaptiveSuffixJitterBM_of_adaptiveJitterBM hBM) hA hS hs D

/-- Whole-run `AdaptiveJitterBM` exclusion at time constant `c`. -/
theorem adaptiveJitterBM_excludes_transposesAt {M : TM} {c : ℝ} (hc : 0 < c)
    {M_ph : ℕ} (hMph : 1 ≤ M_ph) {B_bank : Finset (Fin M.k)} {A S : ℕ → ℕ}
    (hBM : AdaptiveJitterBM M c M_ph B_bank A S)
    (hA : Tendsto (fun d : ℕ => (A d : ℝ) / ((d * d * entryBits d : ℕ) : ℝ)) atTop (nhds 0))
    (hS : Tendsto (fun d : ℕ => (S d : ℝ) / ((d * d * entryBits d : ℕ) : ℝ)) atTop (nhds 0)) :
    ∀ᶠ d in atTop, ¬ TransposesAt M d c :=
  adaptiveSuffixJitterBM_excludes_transposesAt hc hMph zero_lt_one
    (adaptiveSuffixJitterBM_of_adaptiveJitterBM hBM) hA hS

/-- If for every `C ≥ 1` all halting runs of `M` within `C (L + 1)` steps have jittered BM shape
(`1 ≤ M_ph`, `A = o(L)`, `S = o(L)`), then `M` is not a linear-time matrix transposer. -/
theorem adaptiveJitterBM_not_linearTimeTransposer (M : TM)
    (h : ∀ C : ℝ, 1 ≤ C →
      ∃ (M_ph : ℕ) (B_bank : Finset (Fin M.k)) (A S : ℕ → ℕ),
        1 ≤ M_ph ∧
        AdaptiveJitterBM M C M_ph B_bank A S ∧
        Tendsto (fun d : ℕ => (A d : ℝ) / ((d * d * entryBits d : ℕ) : ℝ)) atTop (nhds 0) ∧
        Tendsto (fun d : ℕ => (S d : ℝ) / ((d * d * entryBits d : ℕ) : ℝ)) atTop (nhds 0)) :
    ¬ ∃ c : ℕ, TransposesWithin M (fun L => c * (L + 1)) := by
  refine adaptiveSuffixJitterBM_not_linearTimeTransposer M fun C hC => ?_
  obtain ⟨M_ph, B_bank, A, S, hMph, hBM, hA, hS⟩ := h C hC
  exact ⟨M_ph, 1, B_bank, A, S, hMph, zero_lt_one,
    adaptiveSuffixJitterBM_of_adaptiveJitterBM hBM, hA, hS⟩

end NativeRelations
