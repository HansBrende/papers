import NativeRelations.MachineCrux
import DirectedRecovery.StorageCode

/-!
# Bounded Macro-Phase Bank Schedules (Theorem B)

Defines `WeakMonoOnInterval` and the class `BoundedMacroBank` of Theorem B, and develops the
machinery of its proof: signed-monotone threshold pullbacks across weakly monotone phases, phase
signatures and their pulled-back cuts, reverse dependency cones, and raw-row buckets. Theorem B
(`boundedMacroBank_has_crux`, `boundedMacroBank_excludes`: oblivious schedules whose input head and
bank work heads are weakly monotone on boundedly many phases while other heads visit `o(L)` cells
cannot transpose in linear time) is proved in `SuffixMassCrux` as the `δ₀ = 1` case of its suffix
form.
-/

set_option autoImplicit false

namespace NativeRelations

open Filter Finset Transpose Transpose.Tape BoundedNesting MergeDepth BoundedStackDepth
  TapeStorageRates
open scoped BigOperators Topology

/-! ## §1. Class BM (`BoundedMacroBank`) -/

/-- A trajectory `x : ℕ → ℤ` is weakly monotone on the half-open time interval `[lo, hi)`:
either non-decreasing throughout `[lo, hi)` or non-increasing throughout `[lo, hi)`. -/
def WeakMonoOnInterval (x : ℕ → ℤ) (lo hi : ℕ) : Prop :=
  (∀ t t', lo ≤ t → t ≤ t' → t' < hi → x t ≤ x t') ∨
    (∀ t t', lo ≤ t → t ≤ t' → t' < hi → x t' ≤ x t)

/-- **Class BM (`BoundedMacroBank`)**, matching verbatim:
for all `d ≥ d_BM` and every halting horizon `T ≤ C (L + 1)` at which `M` is oblivious on
`inputsOfLength L` (`L = d² entryBits(d)`), `[0, T)` partitions into `M_ph` contiguous macro-phases
on each of which the input walk and every bank walk `j ∈ B_bank` are weakly monotone (arbitrary
pauses allowed), while every workspace head `w ∉ B_bank` visits at most `S d` cells before `T`. -/
def BoundedMacroBank (M : TM) (C : ℝ) (M_ph : ℕ) (B_bank : Finset (Fin M.k))
    (S : ℕ → ℕ) : Prop :=
  ∃ d_BM : ℕ, ∀ d ≥ d_BM, ∀ T : ℕ,
    let L := d * d * entryBits d
    let τ₀ := traceAt M L
    ObliviousOn M (inputsOfLength L) T →
    (T : ℝ) ≤ C * ((L : ℝ) + 1) →
    (∃ a : ℕ → ℕ, a 0 = 0 ∧ a M_ph = T ∧ (∀ α < M_ph, a α ≤ a (α + 1)) ∧
      (∀ α < M_ph, WeakMonoOnInterval τ₀.input (a α) (a (α + 1))) ∧
      (∀ α < M_ph, ∀ j ∈ B_bank, WeakMonoOnInterval (τ₀.work j) (a α) (a (α + 1)))) ∧
    (∀ w : Fin M.k, w ∉ B_bank → ((Finset.range T).image (τ₀.work w)).card ≤ S d)

/-! ## §2. Combinatorial bridge: independent sets lower-bound index codes -/

/-- Any independent set `S_ind` in the demand-labelled cone relation `q ↦ I (tposOf d b q)`
forces every binary index code for `(I, tposOf d b)` to use at least `S_ind.card` bits. -/
theorem indexCode_length_ge_of_independent {d b m : ℕ}
    {I : Fin (d * d * b) → Finset (Fin (d * d * b))}
    {E : (Fin (d * d * b) → Bool) → (Fin m → Bool)}
    (hE : MergeDepth.IsIndexCode E I (tposOf d b))
    {S_ind : Finset (Fin (d * d * b))}
    (hInd : DirectedRecovery.IsIndependent (fun q => I (tposOf d b q)) S_ind) :
    (S_ind.card : ℝ) ≤ (m : ℝ) := by
  have hG : DirectedRecovery.IsIndexCode (fun q => I (tposOf d b q)) E := by
    intro x y hExy q hxy
    have h1 := hE (tposOf d b q) x y hExy hxy
    rwa [tposOf_tposOf] at h1
  refine DirectedRecovery.indexCode_length_ge hG fun C hC => ?_
  have hcard := DirectedRecovery.storageCode_card_le_of_independent hInd hC
  have hle : S_ind.card ≤ Fintype.card (Fin (d * d * b)) := S_ind.card_le_univ
  rw [Fintype.card_bool] at hcard
  rw [← Nat.cast_sub hle, Real.rpow_natCast]
  exact_mod_cast hcard

/-! ## §3. Step 1: Intra-phase hops, signed-monotone pullbacks, and long workspace hops -/

/-- Step 1(a): a walk that is weakly monotone on `[lo, hi)` has no long hop `(v, u)` (`u ≥ v + 2`)
with both endpoints inside `[lo, hi)`. -/
theorem not_isHop_of_weakMonoOnInterval {x : ℕ → ℤ} {lo hi T v u : ℕ}
    (hmono : WeakMonoOnInterval x lo hi) (hlo : lo ≤ v) (hhi : u < hi)
    (hhop : IsHop x T v u) : False := by
  have hv1 : v + 1 ∈ Finset.Ioo v u := Finset.mem_Ioo.mpr ⟨by omega, by have := hhop.1; omega⟩
  have hne : x (v + 1) ≠ x v := hhop.2.2.2 (v + 1) hv1
  have heq : x u = x v := hhop.2.2.1
  rcases hmono with hinc | hdec
  · have h1 := hinc v (v + 1) hlo (by omega) (by have := hhop.1; omega)
    have h2 := hinc (v + 1) u (by omega) (by have := hhop.1; omega) hhi
    omega
  · have h1 := hdec v (v + 1) hlo (by omega) (by have := hhop.1; omega)
    have h2 := hdec (v + 1) u (by omega) (by have := hhop.1; omega) hhi
    omega

/-- Signed threshold predicate on `ℕ`: `θ ≤ t` when `pos = true`, `t < θ` when `pos = false`. -/
def tcut (pos : Bool) (θ t : ℕ) : Prop :=
  if pos then θ ≤ t else t < θ

instance (pos : Bool) (θ t : ℕ) : Decidable (tcut pos θ t) := by
  unfold tcut; infer_instance

/-- Window invariance: a step `u → v` with `v ≤ u ≤ v + Δ` preserves `tcut pos θ` whenever
`u ∉ [θ, θ + Δ]`. -/
theorem tcut_eq_of_notMem_window {pos : Bool} {θ Δ u v : ℕ}
    (huv : v ≤ u) (hΔ : u ≤ v + Δ) (hnot : u ∉ Finset.Icc θ (θ + Δ)) :
    tcut pos θ u ↔ tcut pos θ v := by
  simp only [Finset.mem_Icc, not_and_or] at hnot
  cases pos <;> simp only [tcut, ↓reduceIte, Bool.false_eq_true] <;> omega

/-- Canonical orientation sign of a partial relation `R : ℕ → ℕ → Prop`. -/
noncomputable def relSign (R : ℕ → ℕ → Prop) : Bool :=
  by classical exact decide (∀ u₁ v₁ u₂ v₂, R u₁ v₁ → R u₂ v₂ → u₁ ≤ u₂ → v₁ ≤ v₂)

/-- Total sharp-threshold pullback across `R : ℕ → ℕ → Prop` on `range T`. -/
noncomputable def pullCut (T : ℕ) (R : ℕ → ℕ → Prop) (eta : Bool) (c : Bool × ℕ) : Bool × ℕ := by
  classical
  let S := (Finset.range T).filter fun u => ∃ v, R u v ∧ tcut c.1 c.2 v
  let pos' := (eta == c.1)
  exact if pos' then
    (true, if h : S.Nonempty then S.min' h else T)
  else
    (false, if h : S.Nonempty then S.max' h + 1 else 0)

theorem relSign_spec {R : ℕ → ℕ → Prop}
    (h : (∀ u₁ v₁ u₂ v₂, R u₁ v₁ → R u₂ v₂ → u₁ ≤ u₂ → v₁ ≤ v₂) ∨
      (∀ u₁ v₁ u₂ v₂, R u₁ v₁ → R u₂ v₂ → u₁ ≤ u₂ → v₂ ≤ v₁)) :
    ∀ u₁ v₁ u₂ v₂, R u₁ v₁ → R u₂ v₂ → u₁ ≤ u₂ →
      (if relSign R then v₁ ≤ v₂ else v₂ ≤ v₁) := by
  classical
  unfold relSign
  by_cases h1 : ∀ u₁ v₁ u₂ v₂, R u₁ v₁ → R u₂ v₂ → u₁ ≤ u₂ → v₁ ≤ v₂
  · simp only [decide_eq_true_eq.mpr h1, ↓reduceIte]
    exact h1
  · have h2 : ∀ u₁ v₁ u₂ v₂, R u₁ v₁ → R u₂ v₂ → u₁ ≤ u₂ → v₂ ≤ v₁ :=
      h.resolve_left h1
    have hdec : decide (∀ u₁ v₁ u₂ v₂, R u₁ v₁ → R u₂ v₂ → u₁ ≤ u₂ → v₁ ≤ v₂) = false :=
      decide_eq_false h1
    simp only [hdec, Bool.false_eq_true, ↓reduceIte]
    exact h2

/-- Exact threshold pullback for any signed-monotone relation `R` with domain in `range T`. -/
theorem pullCut_spec {T : ℕ} {R : ℕ → ℕ → Prop} (hdom : ∀ u v, R u v → u < T)
    {eta : Bool}
    (hmono : ∀ u₁ v₁ u₂ v₂, R u₁ v₁ → R u₂ v₂ → u₁ ≤ u₂ → (if eta then v₁ ≤ v₂ else v₂ ≤ v₁))
    (c : Bool × ℕ) {u v : ℕ} (hR : R u v) :
    tcut (pullCut T R eta c).1 (pullCut T R eta c).2 u ↔ tcut c.1 c.2 v := by
  classical
  have huT : u < T := hdom u v hR
  -- Transfer `tcut c.1 c.2` along `u₁ ≤ u₂` according to `eta == c.1`.
  have htrans : ∀ u₁ v₁ u₂ v₂, R u₁ v₁ → R u₂ v₂ → u₁ ≤ u₂ →
      (if (eta == c.1) then tcut c.1 c.2 v₁ → tcut c.1 c.2 v₂
       else tcut c.1 c.2 v₂ → tcut c.1 c.2 v₁) := by
    intro u₁ v₁ u₂ v₂ h1 h2 hle
    have hm := hmono u₁ v₁ u₂ v₂ h1 h2 hle
    cases eta <;> cases c.1 <;> simp [tcut] at hm ⊢ <;> omega
  let S := (Finset.range T).filter fun x => ∃ y, R x y ∧ tcut c.1 c.2 y
  have hpull_eq : pullCut T R eta c =
      (if (eta == c.1) then
        (true, if h : S.Nonempty then S.min' h else T)
      else
        (false, if h : S.Nonempty then S.max' h + 1 else 0)) := by
    unfold pullCut
    rfl
  rw [hpull_eq]
  by_cases hp : (eta == c.1) = true
  · simp only [hp, ↓reduceIte]
    by_cases hS : S.Nonempty
    · simp only [hS, ↓reduceDIte, tcut, ↓reduceIte]
      constructor
      · intro hmin
        have hmem := Finset.min'_mem S hS
        obtain ⟨_, v₀, hRv₀, hcv₀⟩ := Finset.mem_filter.mp hmem
        have ht := htrans (S.min' hS) v₀ u v hRv₀ hR hmin
        simp only [hp, ↓reduceIte] at ht
        exact ht hcv₀
      · intro hcv
        exact Finset.min'_le S u (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr huT, v, hR, hcv⟩)
    · simp only [hS, ↓reduceDIte, tcut, ↓reduceIte]
      constructor
      · intro hle; omega
      · intro hcv
        exfalso
        exact hS ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr huT, v, hR, hcv⟩⟩
  · have hpf : (eta == c.1) = false := Bool.eq_false_iff.mpr hp
    simp only [hpf, Bool.false_eq_true, ↓reduceIte]
    by_cases hS : S.Nonempty
    · simp only [hS, ↓reduceDIte, tcut, Bool.false_eq_true, ↓reduceIte]
      constructor
      · intro hlt
        have hle : u ≤ S.max' hS := by omega
        have hmem := Finset.max'_mem S hS
        obtain ⟨_, v₀, hRv₀, hcv₀⟩ := Finset.mem_filter.mp hmem
        have ht := htrans u v (S.max' hS) v₀ hR hRv₀ hle
        rw [hpf] at ht
        simp only [Bool.false_eq_true, ↓reduceIte] at ht
        exact ht hcv₀
      · intro hcv
        have hle := Finset.le_max' S u
          (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr huT, v, hR, hcv⟩)
        omega
    · simp only [hS, ↓reduceDIte, tcut, Bool.false_eq_true, ↓reduceIte]
      constructor
      · intro hlt; omega
      · intro hcv
        exfalso
        exact hS ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr huT, v, hR, hcv⟩⟩

/-- Inter-phase bank hop relation from `[lo, hi)` back into an earlier phase `[lo', hi')`. -/
def BankInterRel (x : ℕ → ℤ) (T lo' hi' lo hi u v : ℕ) : Prop :=
  lo ≤ u ∧ u < hi ∧ lo' ≤ v ∧ v < hi' ∧ IsHop x T v u

/-- Step 1(b): inter-phase bank hops between weakly monotone phases form a signed-monotone
partial injection. -/
theorem bankInterRel_signed_mono {x : ℕ → ℤ} {T lo' hi' lo hi : ℕ}
    (hsep : hi' ≤ lo) (hmono' : WeakMonoOnInterval x lo' hi')
    (hmono : WeakMonoOnInterval x lo hi) :
    (∀ u₁ v₁ u₂ v₂, BankInterRel x T lo' hi' lo hi u₁ v₁ →
      BankInterRel x T lo' hi' lo hi u₂ v₂ → u₁ ≤ u₂ → v₁ ≤ v₂) ∨
    (∀ u₁ v₁ u₂ v₂, BankInterRel x T lo' hi' lo hi u₁ v₁ →
      BankInterRel x T lo' hi' lo hi u₂ v₂ → u₁ ≤ u₂ → v₂ ≤ v₁) := by
  have hneq : ∀ {u₁ v₁ u₂ v₂}, BankInterRel x T lo' hi' lo hi u₁ v₁ →
      BankInterRel x T lo' hi' lo hi u₂ v₂ → u₁ < u₂ → x u₁ ≠ x u₂ := by
    intro u₁ v₁ u₂ v₂ h1 h2 hlt heq
    have hv2 : v₂ < hi' := h2.2.2.2.1
    have hu1 : lo ≤ u₁ := h1.1
    have hu1_in : u₁ ∈ Finset.Ioo v₂ u₂ := Finset.mem_Ioo.mpr ⟨by omega, hlt⟩
    exact h2.2.2.2.2.2.2.2 u₁ hu1_in (heq.trans h2.2.2.2.2.2.2.1)
  rcases hmono' with hinc' | hdec' <;> rcases hmono with hinc | hdec
  · left
    intro u₁ v₁ u₂ v₂ h1 h2 hle
    rcases eq_or_lt_of_le hle with rfl | hlt
    · exact (hop_end_unique h1.2.2.2.2 h2.2.2.2.2).le
    · have hxle := hinc u₁ u₂ h1.1 hle h2.2.1
      have hxne := hneq h1 h2 hlt
      have hxv : x v₁ < x v₂ := by
        rw [← h1.2.2.2.2.2.2.1, ← h2.2.2.2.2.2.2.1]; omega
      by_contra hcon
      have hvle := hinc' v₂ v₁ h2.2.2.1 (by omega) h1.2.2.2.1
      omega
  · right
    intro u₁ v₁ u₂ v₂ h1 h2 hle
    rcases eq_or_lt_of_le hle with rfl | hlt
    · exact (hop_end_unique h2.2.2.2.2 h1.2.2.2.2).le
    · have hxle := hdec u₁ u₂ h1.1 hle h2.2.1
      have hxne := hneq h1 h2 hlt
      have hxv : x v₂ < x v₁ := by
        rw [← h1.2.2.2.2.2.2.1, ← h2.2.2.2.2.2.2.1]; omega
      by_contra hcon
      have hvle := hinc' v₁ v₂ h1.2.2.1 (by omega) h2.2.2.2.1
      omega
  · right
    intro u₁ v₁ u₂ v₂ h1 h2 hle
    rcases eq_or_lt_of_le hle with rfl | hlt
    · exact (hop_end_unique h2.2.2.2.2 h1.2.2.2.2).le
    · have hxle := hinc u₁ u₂ h1.1 hle h2.2.1
      have hxne := hneq h1 h2 hlt
      have hxv : x v₁ < x v₂ := by
        rw [← h1.2.2.2.2.2.2.1, ← h2.2.2.2.2.2.2.1]; omega
      by_contra hcon
      have hvle := hdec' v₁ v₂ h1.2.2.1 (by omega) h2.2.2.2.1
      omega
  · left
    intro u₁ v₁ u₂ v₂ h1 h2 hle
    rcases eq_or_lt_of_le hle with rfl | hlt
    · exact (hop_end_unique h1.2.2.2.2 h2.2.2.2.2).le
    · have hxle := hdec u₁ u₂ h1.1 hle h2.2.1
      have hxne := hneq h1 h2 hlt
      have hxv : x v₂ < x v₁ := by
        rw [← h1.2.2.2.2.2.2.1, ← h2.2.2.2.2.2.2.1]; omega
      by_contra hcon
      have hvle := hdec' v₂ v₁ h2.2.2.1 (by omega) h1.2.2.2.1
      omega

/-- Input-read relation inside a single macro-phase `[lo, hi)`. -/
def ReadPhaseRel {k : ℕ} (τ₀ : Trace k) (L lo hi t q : ℕ) : Prop :=
  lo ≤ t ∧ t < hi ∧ ∃ p : Fin L, readPos τ₀ L t = some p ∧ p.1 = q

theorem readPhaseRel_signed_mono {k : ℕ} {τ₀ : Trace k} {L lo hi : ℕ}
    (hmono : WeakMonoOnInterval τ₀.input lo hi) :
    (∀ u₁ v₁ u₂ v₂, ReadPhaseRel τ₀ L lo hi u₁ v₁ →
      ReadPhaseRel τ₀ L lo hi u₂ v₂ → u₁ ≤ u₂ → v₁ ≤ v₂) ∨
    (∀ u₁ v₁ u₂ v₂, ReadPhaseRel τ₀ L lo hi u₁ v₁ →
      ReadPhaseRel τ₀ L lo hi u₂ v₂ → u₁ ≤ u₂ → v₂ ≤ v₁) := by
  rcases hmono with hinc | hdec
  · left
    intro u₁ v₁ u₂ v₂ ⟨hlo1, _, p₁, hp1, hpv1⟩ ⟨_, hhi2, p₂, hp2, hpv2⟩ hle
    subst hpv1 hpv2
    have hi1 := (readPos_eq_some_iff.mp hp1)
    have hi2 := (readPos_eq_some_iff.mp hp2)
    have hstep := hinc u₁ u₂ hlo1 hle hhi2
    omega
  · right
    intro u₁ v₁ u₂ v₂ ⟨hlo1, _, p₁, hp1, hpv1⟩ ⟨_, hhi2, p₂, hp2, hpv2⟩ hle
    subst hpv1 hpv2
    have hi1 := (readPos_eq_some_iff.mp hp1)
    have hi2 := (readPos_eq_some_iff.mp hp2)
    have hstep := hdec u₁ u₂ hlo1 hle hhi2
    omega

open Classical in
theorem card_longHopsAtCell_le (x : ℕ → ℤ) (T τ_cut : ℕ) (hτ : 1 ≤ τ_cut) (z : ℤ) :
    ((Finset.range T).filter fun u => x u = z ∧ ∃ v, IsHop x T v u ∧ τ_cut < u - v).card ≤
      T / τ_cut := by
  let U := (Finset.range T).filter fun u => x u = z ∧ ∃ v, IsHop x T v u ∧ τ_cut < u - v
  let vOf : ℕ → ℕ := fun u =>
    if h : ∃ v, IsHop x T v u ∧ τ_cut < u - v then Classical.choose h else 0
  have hvOf : ∀ u ∈ U, x u = z ∧ IsHop x T (vOf u) u ∧ τ_cut < u - vOf u := by
    intro u hu
    obtain ⟨_, hxz, hex⟩ := Finset.mem_filter.mp hu
    simp only [vOf, dite_eq_left hex]
    exact ⟨hxz, Classical.choose_spec hex⟩
  have hdisj : (U : Set ℕ).PairwiseDisjoint fun u => Finset.Ico (vOf u) u := by
    intro u₁ hu₁ u₂ hu₂ hne
    change Disjoint (Finset.Ico (vOf u₁) u₁) (Finset.Ico (vOf u₂) u₂)
    rw [Finset.disjoint_left]
    intro t ht1 ht2
    obtain ⟨hlo1, hhi1⟩ := Finset.mem_Ico.mp ht1
    obtain ⟨hlo2, hhi2⟩ := Finset.mem_Ico.mp ht2
    obtain ⟨hz1, hhop1, -⟩ := hvOf u₁ hu₁
    obtain ⟨hz2, hhop2, -⟩ := hvOf u₂ hu₂
    have hc : x (vOf u₁) = x (vOf u₂) := by
      rw [← hhop1.2.2.1, hz1, ← hhop2.2.2.1, hz2]
    exact hne (hop_unique (τ := t + 1) hhop1 hhop2 hc ⟨by omega, by omega⟩ ⟨by omega, by omega⟩).2
  have hsub : U.biUnion (fun u => Finset.Ico (vOf u) u) ⊆ Finset.range T := by
    intro t ht
    obtain ⟨u, hu, htu⟩ := Finset.mem_biUnion.mp ht
    have huT := Finset.mem_range.mp (Finset.mem_filter.mp hu).1
    have hlt := (Finset.mem_Ico.mp htu).2
    exact Finset.mem_range.mpr (hlt.trans huT)
  have hmul : U.card * τ_cut ≤ T := by
    calc
      U.card * τ_cut = ∑ _u ∈ U, τ_cut := by simp
      _ ≤ ∑ u ∈ U, (Finset.Ico (vOf u) u).card := by
        refine Finset.sum_le_sum fun u hu => ?_
        have hlen := (hvOf u hu).2.2
        rw [Nat.card_Ico]
        omega
      _ = (U.biUnion fun u => Finset.Ico (vOf u) u).card := (Finset.card_biUnion hdisj).symm
      _ ≤ (Finset.range T).card := Finset.card_le_card hsub
      _ = T := Finset.card_range T
  exact (Nat.le_div_iff_mul_le (by omega)).mpr hmul

/-! ## §4. Steps 2 & 3: Phase-start guards, signatures, sharp pullback, and reverse cones -/

theorem phase_le_of_step {M_ph : ℕ} {a : ℕ → ℕ} (ha : ∀ α < M_ph, a α ≤ a (α + 1)) :
    ∀ {α β : ℕ}, α ≤ β → β ≤ M_ph → a α ≤ a β := by
  intro α β hαβ hβ
  induction β with
  | zero =>
    have : α = 0 := by omega
    subst this; exact le_rfl
  | succ β ih =>
    rcases eq_or_lt_of_le hαβ with rfl | hlt
    · exact le_rfl
    · exact (ih (by omega) (by omega)).trans (ha β (by omega))

noncomputable def phaseOf (M_ph : ℕ) (a : ℕ → ℕ) (t : ℕ) : ℕ :=
  if h : ∃ α < M_ph, a α ≤ t ∧ t < a (α + 1) then Nat.find h else 0

/-- Phase-start guard `A_start = ⋃_{α < M_ph} [a α, a α + τ_cut)`. -/
def phaseStartGuard (M_ph : ℕ) (a : ℕ → ℕ) (τ_cut : ℕ) : Finset ℕ :=
  (Finset.range M_ph).biUnion fun α => Finset.Ico (a α) (a α + τ_cut)

theorem card_phaseStartGuard_le (M_ph : ℕ) (a : ℕ → ℕ) (τ_cut : ℕ) :
    (phaseStartGuard M_ph a τ_cut).card ≤ M_ph * τ_cut := by
  calc
    (phaseStartGuard M_ph a τ_cut).card
      ≤ ∑ α ∈ Finset.range M_ph, (Finset.Ico (a α) (a α + τ_cut)).card := Finset.card_biUnion_le
    _ = M_ph * τ_cut := by simp [Nat.card_Ico]

/-- A signature starting at phase `α` assigns to each earlier phase `β < α` either `none`
(phase skipped) or `some j` (`j ∈ B_bank` enters phase `β`). -/
abbrev SigAt {k : ℕ} (B_bank : Finset (Fin k)) (α : ℕ) := Fin α → Option B_bank

theorem card_sigAt {k : ℕ} (B_bank : Finset (Fin k)) (α : ℕ) :
    Fintype.card (SigAt B_bank α) = (B_bank.card + 1) ^ α := by
  rw [Fintype.card_fun, Fintype.card_option, Fintype.card_coe, Fintype.card_fin]

def liftSig {k α : ℕ} {B_bank : Finset (Fin k)} (σ : SigAt B_bank α) (β : ℕ) : Option B_bank :=
  if h : β < α then σ ⟨β, h⟩ else none

/-- Extend a signature `σ'` at phase `α' < α` by jumping from `α` directly into `α'` via `j`. -/
def consSig {k α' α : ℕ} {B_bank : Finset (Fin k)} (_hlt : α' < α) (j : B_bank)
    (σ' : SigAt B_bank α') : SigAt B_bank α :=
  fun β => if h : β.1 < α' then σ' ⟨β.1, h⟩ else if β.1 = α' then some j else none

/-- Structural scan computing the pulled-back cut `(pos, θ)` for phase `α` scanning phases `< m`. -/
noncomputable def cutScan {k : ℕ} (τ₀ : Trace k) (L T : ℕ) (B_bank : Finset (Fin k))
    (a : ℕ → ℕ) (σ : ℕ → Option B_bank) (pStar : ℕ) : ℕ → ℕ → Bool × ℕ
  | 0, α =>
    let R_rd := ReadPhaseRel τ₀ L (a α) (a (α + 1))
    pullCut T R_rd (relSign R_rd) (false, pStar)
  | β + 1, α =>
    match σ β with
    | some j =>
      let c_tail := cutScan τ₀ L T B_bank a σ pStar β β
      let R_hop := BankInterRel (τ₀.work j.1) T (a β) (a (β + 1)) (a α) (a (α + 1))
      pullCut T R_hop (relSign R_hop) c_tail
    | none =>
      cutScan τ₀ L T B_bank a σ pStar β α

/-- Pulled-back cut `(pos, θ)` for signature `σ` starting at phase `α` and raw threshold `pStar`. -/
noncomputable def cutOf {k : ℕ} (τ₀ : Trace k) (L T : ℕ) (B_bank : Finset (Fin k))
    (a : ℕ → ℕ) (α : ℕ) (σ : ℕ → Option B_bank) (pStar : ℕ) : Bool × ℕ :=
  cutScan τ₀ L T B_bank a σ pStar α α

/-- Structural scan computing the union of `Δ`-windows `[θ_r, θ_r + Δ]` along phases visited by
`(α, σ, pStar)` when scanning phases `< m`. -/
noncomputable def windowsScan {k : ℕ} (τ₀ : Trace k) (L T Δ : ℕ) (B_bank : Finset (Fin k))
    (a : ℕ → ℕ) (σ : ℕ → Option B_bank) (pStar : ℕ) : ℕ → ℕ → Finset ℕ
  | 0, α =>
    let θ := (cutOf τ₀ L T B_bank a α σ pStar).2
    Finset.Icc θ (θ + Δ)
  | β + 1, α =>
    match σ β with
    | some _ =>
      let θ := (cutOf τ₀ L T B_bank a α σ pStar).2
      Finset.Icc θ (θ + Δ) ∪ windowsScan τ₀ L T Δ B_bank a σ pStar β β
    | none =>
      windowsScan τ₀ L T Δ B_bank a σ pStar β α

/-- Union of `Δ`-windows `[θ_r, θ_r + Δ]` along all phases visited by `(α, σ, pStar)`. -/
noncomputable def windowsOf {k : ℕ} (τ₀ : Trace k) (L T Δ : ℕ) (B_bank : Finset (Fin k))
    (a : ℕ → ℕ) (α : ℕ) (σ : ℕ → Option B_bank) (pStar : ℕ) : Finset ℕ :=
  windowsScan τ₀ L T Δ B_bank a σ pStar α α

theorem cutScan_congr {k : ℕ} (τ₀ : Trace k) (L T : ℕ) (B_bank : Finset (Fin k))
    (a : ℕ → ℕ) (pStar : ℕ) :
    ∀ (m α : ℕ) {σ₁ σ₂ : ℕ → Option B_bank}, (∀ γ < m, σ₁ γ = σ₂ γ) →
      cutScan τ₀ L T B_bank a σ₁ pStar m α = cutScan τ₀ L T B_bank a σ₂ pStar m α
  | 0, _, _, _, _ => rfl
  | β + 1, α, _, σ₂, hfg => by
    simp only [cutScan, hfg β (by omega)]
    cases σ₂ β with
    | none => exact cutScan_congr τ₀ L T B_bank a pStar β α fun γ hγ => hfg γ (by omega)
    | some _ =>
      rw [cutScan_congr τ₀ L T B_bank a pStar β β fun γ hγ => hfg γ (by omega)]

theorem cutOf_congr {k : ℕ} (τ₀ : Trace k) (L T : ℕ) (B_bank : Finset (Fin k))
    (a : ℕ → ℕ) (α : ℕ) {σ₁ σ₂ : ℕ → Option B_bank} (hfg : ∀ β < α, σ₁ β = σ₂ β) (pStar : ℕ) :
    cutOf τ₀ L T B_bank a α σ₁ pStar = cutOf τ₀ L T B_bank a α σ₂ pStar :=
  cutScan_congr τ₀ L T B_bank a pStar α α hfg

theorem windowsScan_congr {k : ℕ} (τ₀ : Trace k) (L T Δ : ℕ) (B_bank : Finset (Fin k))
    (a : ℕ → ℕ) (pStar : ℕ) :
    ∀ (m α : ℕ) {σ₁ σ₂ : ℕ → Option B_bank}, m ≤ α → (∀ γ < α, σ₁ γ = σ₂ γ) →
      windowsScan τ₀ L T Δ B_bank a σ₁ pStar m α = windowsScan τ₀ L T Δ B_bank a σ₂ pStar m α
  | 0, α, _, _, _, hfg => by
    simp only [windowsScan, cutOf_congr τ₀ L T B_bank a α hfg pStar]
  | β + 1, α, _, σ₂, hmα, hfg => by
    have hβα : β < α := by omega
    simp only [windowsScan, hfg β hβα]
    cases σ₂ β with
    | none =>
      exact windowsScan_congr τ₀ L T Δ B_bank a pStar β α (by omega) hfg
    | some _ =>
      rw [cutOf_congr τ₀ L T B_bank a α hfg pStar,
        windowsScan_congr τ₀ L T Δ B_bank a pStar β β le_rfl (fun γ hγ => hfg γ (by omega))]

theorem windowsOf_congr {k : ℕ} (τ₀ : Trace k) (L T Δ : ℕ) (B_bank : Finset (Fin k))
    (a : ℕ → ℕ) (α : ℕ) {σ₁ σ₂ : ℕ → Option B_bank} (hfg : ∀ β < α, σ₁ β = σ₂ β) (pStar : ℕ) :
    windowsOf τ₀ L T Δ B_bank a α σ₁ pStar = windowsOf τ₀ L T Δ B_bank a α σ₂ pStar :=
  windowsScan_congr τ₀ L T Δ B_bank a pStar α α le_rfl hfg

theorem card_windowsScan_le {k : ℕ} (τ₀ : Trace k) (L T Δ : ℕ) (B_bank : Finset (Fin k))
    (a : ℕ → ℕ) (σ : ℕ → Option B_bank) (pStar : ℕ) :
    ∀ (m α : ℕ), (windowsScan τ₀ L T Δ B_bank a σ pStar m α).card ≤ (m + 1) * (Δ + 1)
  | 0, α => by
    simp only [windowsScan, Nat.card_Icc]
    have : (cutOf τ₀ L T B_bank a α σ pStar).2 + Δ + 1 -
        (cutOf τ₀ L T B_bank a α σ pStar).2 = Δ + 1 := by omega
    omega
  | β + 1, α => by
    simp only [windowsScan]
    cases σ β with
    | none =>
      exact (card_windowsScan_le τ₀ L T Δ B_bank a σ pStar β α).trans
        (Nat.mul_le_mul_right _ (by omega))
    | some _ =>
      have ih := card_windowsScan_le τ₀ L T Δ B_bank a σ pStar β β
      calc
        (Finset.Icc _ _ ∪ windowsScan τ₀ L T Δ B_bank a σ pStar β β).card
          ≤ (Finset.Icc _ _).card + (windowsScan τ₀ L T Δ B_bank a σ pStar β β).card :=
            Finset.card_union_le _ _
        _ ≤ (Δ + 1) + (β + 1) * (Δ + 1) := by
            rw [Nat.card_Icc]
            have : (cutOf τ₀ L T B_bank a α σ pStar).2 + Δ + 1 -
                (cutOf τ₀ L T B_bank a α σ pStar).2 = Δ + 1 := by omega
            rw [this]
            exact Nat.add_le_add_left ih _
        _ = (β + 1 + 1) * (Δ + 1) := by ring

theorem card_windowsOf_le {k : ℕ} (τ₀ : Trace k) (L T Δ : ℕ) (B_bank : Finset (Fin k))
    (a : ℕ → ℕ) (α : ℕ) (σ : ℕ → Option B_bank) (pStar : ℕ) :
    (windowsOf τ₀ L T Δ B_bank a α σ pStar).card ≤ (α + 1) * (Δ + 1) :=
  card_windowsScan_le τ₀ L T Δ B_bank a σ pStar α α

theorem cutScan_eq_of_none {k : ℕ} (τ₀ : Trace k) (L T : ℕ) (B_bank : Finset (Fin k))
    (a : ℕ → ℕ) (σ : ℕ → Option B_bank) (pStar : ℕ) :
    ∀ (m α : ℕ), (∀ γ < m, σ γ = none) →
      cutScan τ₀ L T B_bank a σ pStar m α =
        pullCut T (ReadPhaseRel τ₀ L (a α) (a (α + 1)))
          (relSign (ReadPhaseRel τ₀ L (a α) (a (α + 1)))) (false, pStar)
  | 0, _, _ => rfl
  | β + 1, α, hnone => by
    simp only [cutScan, hnone β (by omega)]
    exact cutScan_eq_of_none τ₀ L T B_bank a σ pStar β α fun γ hγ => hnone γ (by omega)

theorem cutOf_none {k : ℕ} (τ₀ : Trace k) (L T : ℕ) (B_bank : Finset (Fin k))
    (a : ℕ → ℕ) (α pStar : ℕ) :
    cutOf τ₀ L T B_bank a α (liftSig (fun _ : Fin α => (none : Option B_bank))) pStar =
      pullCut T (ReadPhaseRel τ₀ L (a α) (a (α + 1)))
        (relSign (ReadPhaseRel τ₀ L (a α) (a (α + 1)))) (false, pStar) :=
  cutScan_eq_of_none τ₀ L T B_bank a _ pStar α α fun γ hγ => by simp [liftSig, hγ]

theorem mem_windowsScan_self {k : ℕ} (τ₀ : Trace k) (L T Δ : ℕ) (B_bank : Finset (Fin k))
    (a : ℕ → ℕ) (σ : ℕ → Option B_bank) (pStar : ℕ) :
    ∀ (m α : ℕ),
      Finset.Icc (cutOf τ₀ L T B_bank a α σ pStar).2 ((cutOf τ₀ L T B_bank a α σ pStar).2 + Δ) ⊆
        windowsScan τ₀ L T Δ B_bank a σ pStar m α
  | 0, _ => Subset.rfl
  | β + 1, α => by
    simp only [windowsScan]
    cases σ β with
    | none => exact mem_windowsScan_self τ₀ L T Δ B_bank a σ pStar β α
    | some _ => exact Finset.subset_union_left

theorem mem_windowsOf_self {k : ℕ} (τ₀ : Trace k) (L T Δ : ℕ) (B_bank : Finset (Fin k))
    (a : ℕ → ℕ) (α : ℕ) (σ : ℕ → Option B_bank) (pStar : ℕ) :
    Finset.Icc (cutOf τ₀ L T B_bank a α σ pStar).2 ((cutOf τ₀ L T B_bank a α σ pStar).2 + Δ) ⊆
      windowsOf τ₀ L T Δ B_bank a α σ pStar :=
  mem_windowsScan_self τ₀ L T Δ B_bank a σ pStar α α

theorem cutScan_eq_of_top {k : ℕ} (τ₀ : Trace k) (L T : ℕ) (B_bank : Finset (Fin k))
    (a : ℕ → ℕ) (σ : ℕ → Option B_bank) (pStar α' : ℕ) (j : B_bank) :
    ∀ (m α : ℕ), α' < m → σ α' = some j → (∀ γ, α' < γ → γ < m → σ γ = none) →
      cutScan τ₀ L T B_bank a σ pStar m α =
        pullCut T (BankInterRel (τ₀.work j.1) T (a α') (a (α' + 1)) (a α) (a (α + 1)))
          (relSign (BankInterRel (τ₀.work j.1) T (a α') (a (α' + 1)) (a α) (a (α + 1))))
          (cutOf τ₀ L T B_bank a α' σ pStar)
  | 0, _, hlt, _, _ => by omega
  | β + 1, α, hlt, htop, hnone => by
    rcases eq_or_lt_of_le (Nat.le_of_lt_succ hlt) with rfl | hlt'
    · simp only [cutScan, htop, cutOf]
    · simp only [cutScan, hnone β hlt' (by omega)]
      exact cutScan_eq_of_top τ₀ L T B_bank a σ pStar α' j β α hlt' htop
        fun γ h1 h2 => hnone γ h1 (by omega)

theorem windowsScan_sub_of_top {k : ℕ} (τ₀ : Trace k) (L T Δ : ℕ) (B_bank : Finset (Fin k))
    (a : ℕ → ℕ) (σ : ℕ → Option B_bank) (pStar α' : ℕ) (j : B_bank) :
    ∀ (m α : ℕ), α' < m → σ α' = some j → (∀ γ, α' < γ → γ < m → σ γ = none) →
      windowsOf τ₀ L T Δ B_bank a α' σ pStar ⊆ windowsScan τ₀ L T Δ B_bank a σ pStar m α
  | 0, _, hlt, _, _ => by omega
  | β + 1, α, hlt, htop, hnone => by
    rcases eq_or_lt_of_le (Nat.le_of_lt_succ hlt) with rfl | hlt'
    · simp only [windowsScan, htop, windowsOf]
      exact Finset.subset_union_right
    · simp only [windowsScan, hnone β hlt' (by omega)]
      exact windowsScan_sub_of_top τ₀ L T Δ B_bank a σ pStar α' j β α hlt' htop
        fun γ h1 h2 => hnone γ h1 (by omega)

theorem cutOf_consSig {k α' α : ℕ} (τ₀ : Trace k) (L T Δ : ℕ) (B_bank : Finset (Fin k))
    (a : ℕ → ℕ) (hlt : α' < α) (j : B_bank) (σ' : SigAt B_bank α') (pStar : ℕ) :
    cutOf τ₀ L T B_bank a α (liftSig (consSig hlt j σ')) pStar =
      pullCut T (BankInterRel (τ₀.work j.1) T (a α') (a (α' + 1)) (a α) (a (α + 1)))
        (relSign (BankInterRel (τ₀.work j.1) T (a α') (a (α' + 1)) (a α) (a (α + 1))))
        (cutOf τ₀ L T B_bank a α' (liftSig σ') pStar) ∧
    windowsOf τ₀ L T Δ B_bank a α' (liftSig σ') pStar ⊆
      windowsOf τ₀ L T Δ B_bank a α (liftSig (consSig hlt j σ')) pStar := by
  let σ := liftSig (consSig hlt j σ')
  have htop : σ α' = some j := by simp [σ, liftSig, consSig, hlt]
  have hnone : ∀ β, α' < β → β < α → σ β = none := by
    intro β h1 h2
    simp [σ, liftSig, consSig, h2, show ¬ β < α' by omega, show β ≠ α' by omega]
  have hagree : ∀ β < α', σ β = liftSig σ' β := by
    intro β hβ
    have hβα : β < α := hβ.trans hlt
    simp [σ, liftSig, consSig, hβα, hβ]
  have hcut_eq := cutOf_congr τ₀ L T B_bank a α' hagree pStar
  have hwin_eq := windowsOf_congr τ₀ L T Δ B_bank a α' hagree pStar
  constructor
  · rw [cutOf, cutScan_eq_of_top τ₀ L T B_bank a σ pStar α' j α α hlt htop hnone, hcut_eq]
  · rw [← hwin_eq]
    exact windowsScan_sub_of_top τ₀ L T Δ B_bank a σ pStar α' j α α hlt htop hnone

/-! ## §5. Reverse `DepDag` ancestors (`≤ (k + 2)^D` expansion) -/

/-- Reverse dependency neighborhood: steps `u < T` having an edge `u → x` in `DepDag`. -/
noncomputable def depIn {k : ℕ} (xs : Fin k → ℕ → ℤ) (T x : ℕ) : Finset ℕ := by
  classical exact (Finset.range T).filter fun u => DepStep xs T u x

theorem card_depIn_le {k : ℕ} (xs : Fin k → ℕ → ℤ) (T x : ℕ) :
    (depIn xs T x).card ≤ k + 1 := by
  classical
  let H_j : Fin k → Finset ℕ := fun j => (Finset.range T).filter fun u => IsHop (xs j) T x u
  have hHj : ∀ j : Fin k, (H_j j).card ≤ 1 := by
    intro j
    refine Finset.card_le_one.mpr fun u₁ hu₁ u₂ hu₂ => ?_
    exact hop_start_unique (Finset.mem_filter.mp hu₁).2 (Finset.mem_filter.mp hu₂).2
  have hsub : depIn xs T x ⊆ insert (x + 1) (Finset.univ.biUnion H_j) := by
    intro u hu
    unfold depIn at hu
    obtain ⟨huT, hstep⟩ := Finset.mem_filter.mp hu
    rcases hstep with ⟨hb, -⟩ | hhop_mem
    · exact Finset.mem_insert.mpr (Or.inl hb.symm)
    · obtain ⟨⟨j, v, u'⟩, hη, heq⟩ := Finset.mem_image.mp hhop_mem
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _,
        Finset.mem_filter.mpr ⟨huT, mem_allHops.mp hη⟩⟩))
  calc
    (depIn xs T x).card
      ≤ (insert (x + 1) (Finset.univ.biUnion H_j)).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ.biUnion H_j).card + 1 := Finset.card_insert_le _ _
    _ ≤ (∑ j : Fin k, (H_j j).card) + 1 := Nat.add_le_add_right Finset.card_biUnion_le 1
    _ ≤ (∑ _j : Fin k, 1) + 1 := Nat.add_le_add_right (Finset.sum_le_sum fun j _ => hHj j) 1
    _ = k + 1 := by simp

/-- Steps reaching `X` in at most `h` dependency steps. -/
noncomputable def ancestors {k : ℕ} (xs : Fin k → ℕ → ℤ) (T : ℕ) (X : Finset ℕ) : ℕ → Finset ℕ
  | 0 => X
  | h + 1 => ancestors xs T X h ∪ (ancestors xs T X h).biUnion (depIn xs T)

theorem ancestors_mono {k : ℕ} (xs : Fin k → ℕ → ℤ) (T : ℕ) (X : Finset ℕ) :
    ∀ {h₁ h₂ : ℕ}, h₁ ≤ h₂ → ancestors xs T X h₁ ⊆ ancestors xs T X h₂ := by
  intro h₁ h₂ hle
  induction h₂ with
  | zero =>
    have : h₁ = 0 := by omega
    subst this; exact Subset.rfl
  | succ h₂ ih =>
    rcases eq_or_lt_of_le hle with rfl | hlt
    · exact Subset.rfl
    · exact (ih (by omega)).trans Finset.subset_union_left

theorem depStep_mem_ancestors {k : ℕ} {xs : Fin k → ℕ → ℤ} {T : ℕ} {X : Finset ℕ}
    {h u x : ℕ} (hx : x ∈ ancestors xs T X h) (hstep : DepStep xs T u x) :
    u ∈ ancestors xs T X (h + 1) := by
  classical
  have huT : u < T := (depStep_lt hstep).2
  have hu_in : u ∈ depIn xs T x := by
    unfold depIn
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr huT, hstep⟩
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨x, hx, hu_in⟩)

theorem head_mem_ancestors_of_mem_path {k : ℕ} {xs : Fin k → ℕ → ℤ} {T : ℕ} {X : Finset ℕ} :
    ∀ (ρ : List ℕ) (t₀ : ℕ), IsDepPath xs T (t₀ :: ρ) →
      ∀ {x : ℕ}, x ∈ t₀ :: ρ → x ∈ X → t₀ ∈ ancestors xs T X ρ.length
  | [], t₀, _, x, hx_mem, hxX => by
    simp only [List.mem_singleton] at hx_mem
    subst hx_mem
    exact hxX
  | t₁ :: ρ₁, t₀, ⟨hstep, htail⟩, x, hx_mem, hxX => by
    rcases List.mem_cons.mp hx_mem with rfl | hx_tail
    · exact ancestors_mono xs T X (Nat.zero_le _) hxX
    · have ht1 := head_mem_ancestors_of_mem_path ρ₁ t₁ htail hx_tail hxX
      exact depStep_mem_ancestors ht1 hstep

theorem card_ancestors_le {k : ℕ} (xs : Fin k → ℕ → ℤ) (T : ℕ) (X : Finset ℕ) :
    ∀ D : ℕ, (ancestors xs T X D).card ≤ (k + 2) ^ D * X.card
  | 0 => by simp [ancestors]
  | D + 1 => by
    let A := ancestors xs T X D
    have ih := card_ancestors_le xs T X D
    calc
      (ancestors xs T X (D + 1)).card
        = (A ∪ A.biUnion (depIn xs T)).card := rfl
      _ ≤ A.card + (A.biUnion (depIn xs T)).card := Finset.card_union_le _ _
      _ ≤ A.card + ∑ x ∈ A, (depIn xs T x).card := Nat.add_le_add_left Finset.card_biUnion_le _
      _ ≤ A.card + ∑ _x ∈ A, (k + 1) :=
          Nat.add_le_add_left (Finset.sum_le_sum fun x _ => card_depIn_le xs T x) _
      _ = (k + 2) * A.card := by simp; ring
      _ ≤ (k + 2) * ((k + 2) ^ D * X.card) := Nat.mul_le_mul_left _ ih
      _ = (k + 2) ^ (D + 1) * X.card := by ring

/-! ## §6. Step 4: Raw-row buckets and coordinate bounds -/

/-- Near-equal consecutive raw-row bucket `[c * d / B, (c + 1) * d / B)` has size `≥ d / B`. -/
theorem bucketR_card_ge {d B : ℕ} (hB : 0 < B) (c : Fin B) :
    d / B ≤ (Finset.univ.filter fun u : Fin d =>
      c.1 * d / B ≤ u.1 ∧ u.1 < (c.1 + 1) * d / B).card := by
  have hstep : c.1 * d / B + d / B ≤ (c.1 + 1) * d / B := by
    simpa only [Nat.add_mul, Nat.one_mul] using
      (Nat.div_add_div_le_add_div (x := c.1 * d) (y := d) (z := B))
  have hupper : (c.1 + 1) * d / B ≤ d := by
    have hmul : (c.1 + 1) * d ≤ B * d := Nat.mul_le_mul_right d (by omega)
    have hd := Nat.div_le_div_right (c := B) hmul
    simpa [Nat.mul_div_right, hB.ne'] using hd
  let lo := c.1 * d / B
  let hi := (c.1 + 1) * d / B
  have hlo_hi : lo + d / B ≤ hi := hstep
  let emb : Fin (hi - lo) ↪ Fin d :=
    ⟨fun r => ⟨lo + r.1, by omega⟩, fun r₁ r₂ heq => Fin.ext (by
      have := congrArg Fin.val heq; dsimp at this; omega)⟩
  have hsub : Finset.univ.map emb ⊆ Finset.univ.filter fun u : Fin d => lo ≤ u.1 ∧ u.1 < hi := by
    intro u hu
    obtain ⟨r, -, rfl⟩ := Finset.mem_map.mp hu
    have hr_val : (emb r).1 = lo + r.1 := rfl
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hr_val]; omega,
      by rw [hr_val]; have := r.2; omega⟩
  calc
    d / B ≤ hi - lo := by omega
    _ = (Finset.univ.map emb).card := by simp
    _ ≤ (Finset.univ.filter fun u : Fin d => lo ≤ u.1 ∧ u.1 < hi).card := Finset.card_le_card hsub

/-- Coordinate arithmetic helper for `Fin (d * d * b)`: `q` decomposes into raw row
`u = q / b / d < d`, output row `j = q / b % d < d`, and bit `s = q % b < b`, with
`u < r ↔ q < r * (d * b)` and `j * (d * b) ≤ tposOf d b q ≤ (j + 1) * (d * b) - 1`. -/
theorem coord_row_bounds {d b : ℕ} (q : Fin (d * d * b)) :
    (∀ r : ℕ, q.1 / b / d < r ↔ q.1 < r * (d * b)) ∧
    (q.1 / b % d) * (d * b) ≤ (tposOf d b q).1 ∧
    (tposOf d b q).1 ≤ (q.1 / b % d + 1) * (d * b) - 1 := by
  obtain ⟨hu, hj, hs, hdec⟩ := Transpose.Tape.Impl.pos_decomp q.2
  set u := q.1 / b / d
  set j := q.1 / b % d
  set s := q.1 % b
  have htpos : (tposOf d b q).1 = (j * d + u) * b + s := by
    rw [tposOf_val, hdec]
    exact Transpose.Tape.Impl.tpos_spec (i := u) hj hs
  have hq_lo : u * (d * b) ≤ q.1 := by
    rw [hdec]
    calc u * (d * b) = (u * d) * b := by ring
      _ ≤ (u * d + j) * b := Nat.mul_le_mul_right b (Nat.le_add_right _ _)
      _ ≤ (u * d + j) * b + s := Nat.le_add_right _ _
  have hq_hi : q.1 < (u + 1) * (d * b) := by
    rw [hdec]
    calc (u * d + j) * b + s < (u * d + j) * b + b := Nat.add_lt_add_left hs _
      _ = (u * d + j + 1) * b := by ring
      _ ≤ (u * d + d) * b := Nat.mul_le_mul_right b (by omega)
      _ = (u + 1) * (d * b) := by ring
  refine ⟨fun r => ?_, ?_, ?_⟩
  · constructor
    · intro hur
      calc q.1 < (u + 1) * (d * b) := hq_hi
        _ ≤ r * (d * b) := Nat.mul_le_mul_right (d * b) (by omega)
    · intro hqr
      by_contra hge
      have : r * (d * b) ≤ u * (d * b) := Nat.mul_le_mul_right (d * b) (by omega)
      omega
  · rw [htpos]
    calc j * (d * b) = (j * d) * b := by ring
      _ ≤ (j * d + u) * b := Nat.mul_le_mul_right b (Nat.le_add_right _ _)
      _ ≤ (j * d + u) * b + s := Nat.le_add_right _ _
  · rw [htpos]
    have hlt : (j * d + u) * b + s < (j + 1) * (d * b) := by
      calc (j * d + u) * b + s < (j * d + u) * b + b := Nat.add_lt_add_left hs _
        _ = (j * d + u + 1) * b := by ring
        _ ≤ (j * d + d) * b := Nat.mul_le_mul_right b (by omega)
        _ = (j + 1) * (d * b) := by ring
    omega

end NativeRelations
