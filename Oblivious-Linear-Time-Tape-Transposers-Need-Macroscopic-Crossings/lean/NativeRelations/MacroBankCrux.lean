import NativeRelations.MachineCrux
import DirectedRecovery.StorageCode

/-!
# Bounded Macro-Phase Bank Schedules (Theorem B)

Defines `WeakMonoOnInterval` and `BoundedMacroBank`, constructs linear-density independent sets
(`macroBank_independent_exists`), and proves Theorem B (`boundedMacroBank_has_crux`,
`boundedMacroBank_excludes`): oblivious schedules whose input head and bank work heads are weakly
monotone on boundedly many phases while other heads visit `o(L)` cells cannot transpose in linear time.
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

/-- Step 1(c): upper endpoints of workspace hops exceeding duration `τ_cut`. -/
noncomputable def longWorkHops {k : ℕ} (xs : Fin k → ℕ → ℤ) (B_bank : Finset (Fin k))
    (T τ_cut : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range T).filter fun u =>
    ∃ w : Fin k, w ∉ B_bank ∧ ∃ v, IsHop (xs w) T v u ∧ τ_cut < u - v

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

theorem card_longWorkHops_le {k : ℕ} (xs : Fin k → ℕ → ℤ) (B_bank : Finset (Fin k))
    (T τ_cut S_val : ℕ) (hτ : 1 ≤ τ_cut)
    (hS : ∀ w : Fin k, w ∉ B_bank → ((Finset.range T).image (xs w)).card ≤ S_val) :
    (longWorkHops xs B_bank T τ_cut).card ≤ k * (S_val * (T / τ_cut)) := by
  classical
  let Wset := (Finset.univ : Finset (Fin k)).filter fun w => w ∉ B_bank
  have hW : ∀ w ∈ Wset,
      ((Finset.range T).filter fun u => ∃ v, IsHop (xs w) T v u ∧ τ_cut < u - v).card ≤
        S_val * (T / τ_cut) := by
    intro w hw
    have hwB : w ∉ B_bank := (Finset.mem_filter.mp hw).2
    let cells := (Finset.range T).image (xs w)
    have hsub : ((Finset.range T).filter fun u => ∃ v, IsHop (xs w) T v u ∧ τ_cut < u - v) ⊆
        cells.biUnion fun z =>
          (Finset.range T).filter fun u => xs w u = z ∧ ∃ v, IsHop (xs w) T v u ∧ τ_cut < u - v := by
      intro u hu
      obtain ⟨huT, hex⟩ := Finset.mem_filter.mp hu
      exact Finset.mem_biUnion.mpr ⟨xs w u, Finset.mem_image_of_mem _ huT,
        Finset.mem_filter.mpr ⟨huT, rfl, hex⟩⟩
    calc
      _ ≤ (cells.biUnion _).card := Finset.card_le_card hsub
      _ ≤ ∑ z ∈ cells, ((Finset.range T).filter fun u =>
            xs w u = z ∧ ∃ v, IsHop (xs w) T v u ∧ τ_cut < u - v).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _z ∈ cells, (T / τ_cut) :=
          Finset.sum_le_sum fun z _ => card_longHopsAtCell_le (xs w) T τ_cut hτ z
      _ = cells.card * (T / τ_cut) := by simp
      _ ≤ S_val * (T / τ_cut) := Nat.mul_le_mul_right _ (hS w hwB)
  have htotal : longWorkHops xs B_bank T τ_cut ⊆
      Wset.biUnion fun w =>
        (Finset.range T).filter fun u => ∃ v, IsHop (xs w) T v u ∧ τ_cut < u - v := by
    intro u hu
    obtain ⟨huT, w, hw, hex⟩ := Finset.mem_filter.mp hu
    exact Finset.mem_biUnion.mpr ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩,
      Finset.mem_filter.mpr ⟨huT, hex⟩⟩
  calc
    (longWorkHops xs B_bank T τ_cut).card
      ≤ (Wset.biUnion _).card := Finset.card_le_card htotal
    _ ≤ ∑ w ∈ Wset, ((Finset.range T).filter fun u =>
          ∃ v, IsHop (xs w) T v u ∧ τ_cut < u - v).card := Finset.card_biUnion_le
    _ ≤ ∑ _w ∈ Wset, (S_val * (T / τ_cut)) := Finset.sum_le_sum hW
    _ = Wset.card * (S_val * (T / τ_cut)) := by simp
    _ ≤ k * (S_val * (T / τ_cut)) := by
        refine Nat.mul_le_mul_right _ ?_
        calc Wset.card ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_le_univ _
          _ = k := by simp

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

theorem exists_phase_of_lt {m : ℕ} {a : ℕ → ℕ} (ha0 : a 0 = 0)
    (t : ℕ) (ht : t < a m) : ∃ α < m, a α ≤ t ∧ t < a (α + 1) := by
  induction m with
  | zero => omega
  | succ m ih =>
    by_cases hm : a m ≤ t
    · exact ⟨m, by omega, hm, ht⟩
    · obtain ⟨α, hα, h1, h2⟩ := ih (by omega)
      exact ⟨α, by omega, h1, h2⟩

noncomputable def phaseOf (M_ph : ℕ) (a : ℕ → ℕ) (t : ℕ) : ℕ :=
  if h : ∃ α < M_ph, a α ≤ t ∧ t < a (α + 1) then Nat.find h else 0

theorem phaseOf_spec {M_ph T : ℕ} {a : ℕ → ℕ} (ha0 : a 0 = 0) (haM : a M_ph = T)
    {t : ℕ} (ht : t < T) :
    phaseOf M_ph a t < M_ph ∧ a (phaseOf M_ph a t) ≤ t ∧ t < a (phaseOf M_ph a t + 1) := by
  have hex : ∃ α < M_ph, a α ≤ t ∧ t < a (α + 1) :=
    exists_phase_of_lt ha0 t (by omega)
  unfold phaseOf
  rw [dite_eq_left hex]
  exact Nat.find_spec hex

theorem phaseOf_eq_iff {M_ph T : ℕ} {a : ℕ → ℕ} (ha0 : a 0 = 0) (haM : a M_ph = T)
    (ha : ∀ α < M_ph, a α ≤ a (α + 1)) {t α : ℕ} (ht : t < T) (hα : α < M_ph) :
    phaseOf M_ph a t = α ↔ a α ≤ t ∧ t < a (α + 1) := by
  obtain ⟨h1, h2, h3⟩ := phaseOf_spec ha0 haM ht
  constructor
  · rintro rfl; exact ⟨h2, h3⟩
  · rintro ⟨hlo, hhi⟩
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have := phase_le_of_step ha (α := phaseOf M_ph a t + 1) (β := α) (by omega) (by omega)
      omega
    · have := phase_le_of_step ha (α := α + 1) (β := phaseOf M_ph a t) (by omega) (by omega)
      omega

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

/-! ## §5. Dependency path phase-splitting and signature existence -/

/-- Step 2: a dependency path starting at `t₀ < T` in phase `α = phaseOf M_ph a t₀` whose vertices
avoid `longWorkHops ∪ phaseStartGuard` either remains in phase `α` with total drop at most
`ρ.length * τ_cut`, or first exits below `a α` via an inter-phase bank hop `j ∈ B_bank`. -/
theorem depPath_phase_split {k : ℕ} {τ₀ : Trace k} {T M_ph τ_cut : ℕ} (hτ : 1 ≤ τ_cut)
    {B_bank : Finset (Fin k)} {a : ℕ → ℕ}
    (ha0 : a 0 = 0) (haM : a M_ph = T) (ha : ∀ α < M_ph, a α ≤ a (α + 1))
    (hbank : ∀ α < M_ph, ∀ j ∈ B_bank, WeakMonoOnInterval (τ₀.work j) (a α) (a (α + 1))) :
    ∀ (ρ : List ℕ) (t₀ : ℕ), t₀ < T →
      IsDepPath τ₀.work T (t₀ :: ρ) →
      (∀ x ∈ t₀ :: ρ, x ∉ longWorkHops τ₀.work B_bank T τ_cut ∧
        x ∉ phaseStartGuard M_ph a τ_cut) →
      let α := phaseOf M_ph a t₀
      let t_last := (t₀ :: ρ).getLastD t₀
      (a α ≤ t_last ∧ t_last ≤ t₀ ∧ t₀ ≤ t_last + ρ.length * τ_cut) ∨
      (∃ (u₁ v₁ : ℕ) (ρ' : List ℕ) (j : B_bank),
        a α ≤ u₁ ∧ u₁ ≤ t₀ ∧ t₀ ≤ u₁ + ρ.length * τ_cut ∧
        v₁ < a α ∧ IsHop (τ₀.work j.1) T v₁ u₁ ∧
        IsDepPath τ₀.work T (v₁ :: ρ') ∧
        (v₁ :: ρ').getLastD v₁ = t_last ∧
        ρ'.length ≤ ρ.length ∧
        ∀ x ∈ v₁ :: ρ', x ∈ t₀ :: ρ)
  | [], t₀, ht₀, _, _ => by
    obtain ⟨_, hlo, _⟩ := phaseOf_spec ha0 haM ht₀
    exact Or.inl ⟨hlo, le_rfl, by simp⟩
  | t₁ :: ρ₁, t₀, ht₀, hdep, havoid => by
    classical
    obtain ⟨hstep, htail⟩ := hdep
    obtain ⟨hlt10, _⟩ := depStep_lt hstep
    have ht₁ : t₁ < T := hlt10.trans ht₀
    obtain ⟨hαM, hlo0, hhi0⟩ := phaseOf_spec ha0 haM ht₀
    obtain ⟨hno_long, hno_guard⟩ := havoid t₀ List.mem_cons_self
    have hlast_eq : (t₀ :: t₁ :: ρ₁).getLastD t₀ = (t₁ :: ρ₁).getLastD t₁ :=
      LinNet.getLastD_cons_cons t₀ t₁ ρ₁
    by_cases ht1_ge : a (phaseOf M_ph a t₀) ≤ t₁
    · have hdrop : t₀ ≤ t₁ + τ_cut := by
        rcases hstep with ⟨hb, -⟩ | hhop_mem
        · omega
        · obtain ⟨⟨w, v, u⟩, hη, heq⟩ := Finset.mem_image.mp hhop_mem
          simp only [Prod.mk.injEq] at heq
          have hhop : IsHop (τ₀.work w) T t₁ t₀ := heq.2 ▸ heq.1 ▸ mem_allHops.mp hη
          by_cases hw : w ∈ B_bank
          · exfalso
            exact not_isHop_of_weakMonoOnInterval (hbank _ hαM w hw) ht1_ge hhi0 hhop
          · by_contra hgt
            apply hno_long
            unfold longWorkHops
            exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ht₀, w, hw, t₁, hhop, by omega⟩
      have hph_eq : phaseOf M_ph a t₁ = phaseOf M_ph a t₀ :=
        (phaseOf_eq_iff ha0 haM ha ht₁ hαM).mpr ⟨ht1_ge, hlt10.trans hhi0⟩
      have havoid1 : ∀ x ∈ t₁ :: ρ₁, x ∉ longWorkHops τ₀.work B_bank T τ_cut ∧
          x ∉ phaseStartGuard M_ph a τ_cut :=
        fun x hx => havoid x (List.mem_cons_of_mem t₀ hx)
      rcases depPath_phase_split hτ ha0 haM ha hbank ρ₁ t₁ ht₁ htail havoid1 with
        ⟨h1, h2, h3⟩ | ⟨u₁, v₁, ρ', j, hu_lo, hu_hi, hu_drop, hv_lt, hhop, hdep', hlast', hlen', hsub'⟩
      · left
        rw [hph_eq] at h1
        refine ⟨by rw [hlast_eq]; exact h1, ?_, ?_⟩
        · rw [hlast_eq]; omega
        · rw [hlast_eq]
          calc t₀ ≤ t₁ + τ_cut := hdrop
            _ ≤ (t₁ :: ρ₁).getLastD t₁ + ρ₁.length * τ_cut + τ_cut := Nat.add_le_add_right h3 _
            _ = (t₁ :: ρ₁).getLastD t₁ + (t₁ :: ρ₁).length * τ_cut := by rw [List.length_cons]; ring
      · right
        rw [hph_eq] at hu_lo hv_lt
        refine ⟨u₁, v₁, ρ', j, hu_lo, hu_hi.trans hlt10.le, ?_, hv_lt, hhop, hdep',
          hlast'.trans hlast_eq.symm, hlen'.trans (Nat.le_succ _),
          fun x hx => List.mem_cons_of_mem t₀ (hsub' x hx)⟩
        calc t₀ ≤ t₁ + τ_cut := hdrop
          _ ≤ u₁ + ρ₁.length * τ_cut + τ_cut := Nat.add_le_add_right hu_drop _
          _ = u₁ + (t₁ :: ρ₁).length * τ_cut := by rw [List.length_cons]; ring
    · have ht0_guard : a (phaseOf M_ph a t₀) + τ_cut ≤ t₀ := by
        by_contra hlt_g
        apply hno_guard
        unfold phaseStartGuard
        exact Finset.mem_biUnion.mpr ⟨phaseOf M_ph a t₀, Finset.mem_range.mpr hαM,
          Finset.mem_Ico.mpr ⟨hlo0, by omega⟩⟩
      have hgap : τ_cut < t₀ - t₁ := by omega
      rcases hstep with ⟨hb, -⟩ | hhop_mem
      · omega
      · obtain ⟨⟨w, v, u⟩, hη, heq⟩ := Finset.mem_image.mp hhop_mem
        simp only [Prod.mk.injEq] at heq
        have hhop : IsHop (τ₀.work w) T t₁ t₀ := heq.2 ▸ heq.1 ▸ mem_allHops.mp hη
        by_cases hw : w ∈ B_bank
        · right
          refine ⟨t₀, t₁, ρ₁, ⟨w, hw⟩, hlo0, le_rfl, by omega, by omega, hhop, htail,
            hlast_eq.symm, Nat.le_succ _, fun x hx => List.mem_cons_of_mem t₀ hx⟩
        · exfalso
          apply hno_long
          unfold longWorkHops
          exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ht₀, w, hw, t₁, hhop, hgap⟩

/-- Step 3: every dependency path of length `≤ D` avoiding `longWorkHops ∪ phaseStartGuard` and
ending at a read of `p : Fin L` has a single signature `s : SigAt B_bank (phaseOf M_ph a t₀)` that
simultaneously pulls back every raw threshold `pStar` whose `Δ`-windows the path avoids. -/
theorem depPath_signature_exists {k : ℕ} {τ₀ : Trace k} {L T M_ph τ_cut Δ : ℕ} (hτ : 1 ≤ τ_cut)
    {B_bank : Finset (Fin k)} {a : ℕ → ℕ}
    (ha0 : a 0 = 0) (haM : a M_ph = T) (ha : ∀ α < M_ph, a α ≤ a (α + 1))
    (hin : ∀ α < M_ph, WeakMonoOnInterval τ₀.input (a α) (a (α + 1)))
    (hbank : ∀ α < M_ph, ∀ j ∈ B_bank, WeakMonoOnInterval (τ₀.work j) (a α) (a (α + 1))) :
    ∀ (α : ℕ), α < M_ph →
      ∀ {t₀ : ℕ} (_ht₀ : t₀ < T) (_hα : phaseOf M_ph a t₀ = α)
        {ρ : List ℕ} (_hdep : IsDepPath τ₀.work T (t₀ :: ρ)) (_hΔ : ρ.length * τ_cut ≤ Δ)
        (_havoid : ∀ x ∈ t₀ :: ρ, x ∉ longWorkHops τ₀.work B_bank T τ_cut ∧
          x ∉ phaseStartGuard M_ph a τ_cut)
        {p : Fin L} (_hrd : readPos τ₀ L ((t₀ :: ρ).getLastD t₀) = some p),
        ∃ s : SigAt B_bank α, ∀ pStar : ℕ,
          (∀ x ∈ t₀ :: ρ, x ∉ windowsOf τ₀ L T Δ B_bank a α (liftSig s) pStar) →
          (tcut (cutOf τ₀ L T B_bank a α (liftSig s) pStar).1
            (cutOf τ₀ L T B_bank a α (liftSig s) pStar).2 t₀ ↔ p.1 < pStar) := by
  intro α
  induction α using Nat.strong_induction_on with
  | h α ih =>
    intro hαM t₀ ht₀ hα ρ hdep hΔ havoid p hrd
    obtain ⟨_, hlo0, hhi0⟩ := phaseOf_spec ha0 haM ht₀
    subst hα
    let α := phaseOf M_ph a t₀
    rcases depPath_phase_split hτ ha0 haM ha hbank ρ t₀ ht₀ hdep havoid with
      ⟨htm_lo, htm_le, htm_drop⟩ |
      ⟨u₁, v₁, ρ', j, hu_lo, hu_hi, hu_drop, hv_lt, hhop, hdep', hlast', hlen', hsub'⟩
    · let s₀ : SigAt B_bank α := fun _ => none
      refine ⟨s₀, fun pStar hnowin => ?_⟩
      let t_m := (t₀ :: ρ).getLastD t₀
      have htm_hi : t_m < a (α + 1) := htm_le.trans_lt hhi0
      have hR : ReadPhaseRel τ₀ L (a α) (a (α + 1)) t_m p.1 :=
        ⟨htm_lo, htm_hi, p, hrd, rfl⟩
      have hdom : ∀ u v, ReadPhaseRel τ₀ L (a α) (a (α + 1)) u v → u < T := by
        intro u _ hRu
        have hleT : a (α + 1) ≤ T := haM ▸ phase_le_of_step ha (by omega) le_rfl
        exact hRu.2.1.trans_le hleT
      have hmono := relSign_spec (readPhaseRel_signed_mono (L := L) (hin α hαM))
      have hpull := pullCut_spec hdom hmono (false, pStar) hR
      rw [← cutOf_none τ₀ L T B_bank a α pStar] at hpull
      have ht0_not_win : t₀ ∉ Finset.Icc
          (cutOf τ₀ L T B_bank a α (liftSig s₀) pStar).2
          ((cutOf τ₀ L T B_bank a α (liftSig s₀) pStar).2 + Δ) :=
        fun hmem => hnowin t₀ List.mem_cons_self
          (mem_windowsOf_self τ₀ L T Δ B_bank a α (liftSig s₀) pStar hmem)
      have hwin := tcut_eq_of_notMem_window
        (pos := (cutOf τ₀ L T B_bank a α (liftSig s₀) pStar).1)
        htm_le (htm_drop.trans (Nat.add_le_add_left hΔ t_m)) ht0_not_win
      exact hwin.trans (hpull.trans (by simp [tcut]))
    · have hvT : v₁ < T := hv_lt.trans_le (haM ▸ phase_le_of_step ha (by omega) (by omega))
      let α' := phaseOf M_ph a v₁
      obtain ⟨hα'M, hlo', hhi'⟩ := phaseOf_spec ha0 haM hvT
      have hlt_ph : α' < α := by
        by_contra hge
        have hstep_le := phase_le_of_step ha (α := α) (β := α') (by omega) (by omega)
        dsimp only [α', α] at hstep_le hv_lt hlo'
        omega
      have hΔ' : ρ'.length * τ_cut ≤ Δ := (Nat.mul_le_mul_right τ_cut hlen').trans hΔ
      have havoid' : ∀ x ∈ v₁ :: ρ', x ∉ longWorkHops τ₀.work B_bank T τ_cut ∧
          x ∉ phaseStartGuard M_ph a τ_cut := fun x hx => havoid x (hsub' x hx)
      have hrd' : readPos τ₀ L ((v₁ :: ρ').getLastD v₁) = some p := by rw [hlast']; exact hrd
      obtain ⟨s', hs'⟩ := ih α' hlt_ph hα'M hvT rfl hdep' hΔ' havoid' hrd'
      refine ⟨consSig hlt_ph j s', fun pStar hnowin => ?_⟩
      obtain ⟨hcut_cons, hwin_sub⟩ := cutOf_consSig τ₀ L T Δ B_bank a hlt_ph j s' pStar
      have hnowin' : ∀ x ∈ v₁ :: ρ', x ∉ windowsOf τ₀ L T Δ B_bank a α' (liftSig s') pStar :=
        fun x hx hmem => hnowin x (hsub' x hx) (hwin_sub hmem)
      have ih_eq := hs' pStar hnowin'
      have hsep : a (α' + 1) ≤ a α := phase_le_of_step ha (by omega) (by omega)
      have hR : BankInterRel (τ₀.work j.1) T (a α') (a (α' + 1)) (a α) (a (α + 1)) u₁ v₁ :=
        ⟨hu_lo, hu_hi.trans_lt hhi0, hlo', hhi', hhop⟩
      have hdom : ∀ u v,
          BankInterRel (τ₀.work j.1) T (a α') (a (α' + 1)) (a α) (a (α + 1)) u v → u < T := by
        intro u _ hRu
        have hleT : a (α + 1) ≤ T := haM ▸ phase_le_of_step ha (by omega) le_rfl
        exact hRu.2.1.trans_le hleT
      have hmono := relSign_spec
        (bankInterRel_signed_mono (T := T) hsep (hbank α' hα'M j.1 j.2) (hbank α hαM j.1 j.2))
      have hpull := pullCut_spec hdom hmono (cutOf τ₀ L T B_bank a α' (liftSig s') pStar) hR
      rw [← hcut_cons] at hpull
      have ht0_not_win : t₀ ∉ Finset.Icc
          (cutOf τ₀ L T B_bank a α (liftSig (consSig hlt_ph j s')) pStar).2
          ((cutOf τ₀ L T B_bank a α (liftSig (consSig hlt_ph j s')) pStar).2 + Δ) :=
        fun hmem => hnowin t₀ List.mem_cons_self
          (mem_windowsOf_self τ₀ L T Δ B_bank a α _ pStar hmem)
      have hwin := tcut_eq_of_notMem_window
        (pos := (cutOf τ₀ L T B_bank a α (liftSig (consSig hlt_ph j s')) pStar).1)
        hu_hi (hu_drop.trans (Nat.add_le_add_left hΔ u₁)) ht0_not_win
      exact hwin.trans (hpull.trans ih_eq)

/-! ## §6. Reverse `DepDag` ancestors (`≤ (k + 2)^D` expansion) -/

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

/-! ## §7. Step 4: Unsplit output rows, independent rectangle extraction, and main theorems -/

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

/-- Finite quantitative core of Theorem 9.2 (Theorem B): constructs an independent set `S_ind` in the
demand-labelled cone relation `q ↦ I (tposOf d b q)` with explicit size bound. -/
theorem macroBank_independent_exists {M : TM} {M_ph D d b T S_val : ℕ}
    (hMph : 1 ≤ M_ph) (hd : 1 ≤ d) (hb : 1 ≤ b)
    {B_bank : Finset (Fin M.k)} {Γ : Finset ℕ}
    (hlen : (appendList (traceAt M (d * d * b)) T).length = d * d * b)
    (hpath : ∀ π, IsDepPath (traceAt M (d * d * b)).work T π → LinNet.GFree Γ π →
      π.length ≤ D + 1)
    {a : ℕ → ℕ} (ha0 : a 0 = 0) (haM : a M_ph = T) (ha : ∀ α < M_ph, a α ≤ a (α + 1))
    (hin : ∀ α < M_ph, WeakMonoOnInterval (traceAt M (d * d * b)).input (a α) (a (α + 1)))
    (hbank : ∀ α < M_ph, ∀ j ∈ B_bank,
      WeakMonoOnInterval ((traceAt M (d * d * b)).work j) (a α) (a (α + 1)))
    (hwork : ∀ w : Fin M.k, w ∉ B_bank →
      ((Finset.range T).image ((traceAt M (d * d * b)).work w)).card ≤ S_val) :
    let K₀ := (B_bank.card + 1) ^ (M_ph - 1)
    let B := 2 * K₀
    let τ_cut := Nat.sqrt (max 1 S_val * (T + 1)) + 1
    let C_split := (M_ph + 1) + M_ph * (K₀ * B)
    let C_cone := (M.k + 2) ^ D * (M.k + M_ph + M_ph * (K₀ * (B * (M_ph * (D + 1)))))
    ∃ S_ind : Finset (Fin (d * d * b)),
      DirectedRecovery.IsIndependent
        (fun q => coneSystem (traceAt M (d * d * b)) T Γ d b (tposOf d b q)) S_ind ∧
      (d / B) * ((d - C_split) / 2) * b ≤ S_ind.card + C_cone * τ_cut := by
  classical
  set L := d * d * b
  set W := d * b
  have hW : 1 ≤ W := Nat.mul_pos hd hb
  have hL : 1 ≤ L := Nat.mul_pos (Nat.mul_pos hd hd) hb
  set τ₀ := traceAt M L
  have hlenL : (appendList τ₀ T).length = L := hlen
  set K₀ := (B_bank.card + 1) ^ (M_ph - 1)
  have hK₀ : 1 ≤ K₀ := Nat.one_le_pow _ _ (by omega)
  set B := 2 * K₀
  have hB : 2 ≤ B := by omega
  have hB0 : 0 < B := by omega
  set τ_cut := Nat.sqrt (max 1 S_val * (T + 1)) + 1
  have hτ : 1 ≤ τ_cut := by omega
  set Δ := D * τ_cut
  -- Bound `S_val * (T / τ_cut) ≤ τ_cut`.
  have hSdiv : S_val * (T / τ_cut) ≤ τ_cut := by
    have hlt_sq : max 1 S_val * (T + 1) < τ_cut * τ_cut := Nat.lt_succ_sqrt _
    have hmul : (max 1 S_val * (T / τ_cut)) * τ_cut ≤ τ_cut * τ_cut := by
      calc (max 1 S_val * (T / τ_cut)) * τ_cut
          = max 1 S_val * ((T / τ_cut) * τ_cut) := by ring
        _ ≤ max 1 S_val * T := Nat.mul_le_mul_left _ (Nat.div_mul_le_self T τ_cut)
        _ ≤ max 1 S_val * (T + 1) := Nat.mul_le_mul_left _ (Nat.le_succ T)
        _ ≤ τ_cut * τ_cut := hlt_sq.le
    calc S_val * (T / τ_cut)
        ≤ max 1 S_val * (T / τ_cut) := Nat.mul_le_mul_right _ (Nat.le_max_right 1 S_val)
      _ ≤ τ_cut := Nat.le_of_mul_le_mul_right hmul hτ
  -- Raw-row buckets and thresholds.
  let bucketR : Fin B → Finset (Fin d) := fun c =>
    Finset.univ.filter fun u : Fin d => c.1 * d / B ≤ u.1 ∧ u.1 < (c.1 + 1) * d / B
  let rThresh : Fin (B - 1) → ℕ := fun m => (m.1 + 1) * d / B
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
  -- Bad DAG vertices `X_bad` and cone-bad coordinates `Z_cone`.
  let W_bad : Finset ℕ :=
    (Finset.range M_ph).biUnion fun α =>
      (Finset.univ : Finset (SigAt B_bank α)).biUnion fun s =>
        P_set.biUnion fun pStar =>
          windowsOf τ₀ L T Δ B_bank a α (liftSig s) pStar
  have hW_bad : W_bad.card ≤ M_ph * (K₀ * (B * (M_ph * (D + 1)))) * τ_cut := by
    have h1 : W_bad.card ≤ M_ph * (K₀ * (B * (M_ph * (Δ + 1)))) := by
      calc W_bad.card
          ≤ ∑ α ∈ Finset.range M_ph,
              ((Finset.univ : Finset (SigAt B_bank α)).biUnion fun s =>
                P_set.biUnion fun pStar => windowsOf τ₀ L T Δ B_bank a α (liftSig s) pStar).card :=
            Finset.card_biUnion_le
        _ ≤ ∑ _α ∈ Finset.range M_ph, (K₀ * (B * (M_ph * (Δ + 1)))) := by
            refine Finset.sum_le_sum fun α hα => ?_
            have hαM : α < M_ph := Finset.mem_range.mp hα
            calc _ ≤ ∑ s ∈ (Finset.univ : Finset (SigAt B_bank α)),
                    (P_set.biUnion fun pStar =>
                      windowsOf τ₀ L T Δ B_bank a α (liftSig s) pStar).card :=
                    Finset.card_biUnion_le
              _ ≤ ∑ _s ∈ (Finset.univ : Finset (SigAt B_bank α)), (B * (M_ph * (Δ + 1))) := by
                    refine Finset.sum_le_sum fun s _ => ?_
                    calc _ ≤ ∑ pStar ∈ P_set,
                            (windowsOf τ₀ L T Δ B_bank a α (liftSig s) pStar).card :=
                            Finset.card_biUnion_le
                      _ ≤ ∑ _pStar ∈ P_set, (M_ph * (Δ + 1)) := by
                            refine Finset.sum_le_sum fun pStar _ => ?_
                            exact (card_windowsOf_le τ₀ L T Δ B_bank a α (liftSig s) pStar).trans
                              (Nat.mul_le_mul_right (Δ + 1) (by omega))
                      _ = P_set.card * (M_ph * (Δ + 1)) := by simp
                      _ ≤ B * (M_ph * (Δ + 1)) := Nat.mul_le_mul_right _ hP_card
              _ = (Finset.univ : Finset (SigAt B_bank α)).card * (B * (M_ph * (Δ + 1))) := by simp
              _ ≤ K₀ * (B * (M_ph * (Δ + 1))) := Nat.mul_le_mul_right _ (hSig_card α hαM)
        _ = M_ph * (K₀ * (B * (M_ph * (Δ + 1)))) := by simp
    have hΔ1 : Δ + 1 ≤ (D + 1) * τ_cut := by
      show D * τ_cut + 1 ≤ (D + 1) * τ_cut
      rw [Nat.add_mul, Nat.one_mul]
      omega
    calc W_bad.card
        ≤ M_ph * (K₀ * (B * (M_ph * ((D + 1) * τ_cut)))) :=
          h1.trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
            (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hΔ1))))
      _ = M_ph * (K₀ * (B * (M_ph * (D + 1)))) * τ_cut := by ring
  let X_bad : Finset ℕ :=
    longWorkHops τ₀.work B_bank T τ_cut ∪ phaseStartGuard M_ph a τ_cut ∪ W_bad
  have hX_bad : X_bad.card ≤ (M.k + M_ph + M_ph * (K₀ * (B * (M_ph * (D + 1))))) * τ_cut := by
    have hlong : (longWorkHops τ₀.work B_bank T τ_cut).card ≤ M.k * τ_cut :=
      (card_longWorkHops_le τ₀.work B_bank T τ_cut S_val hτ hwork).trans
        (Nat.mul_le_mul_left M.k hSdiv)
    have hguard : (phaseStartGuard M_ph a τ_cut).card ≤ M_ph * τ_cut :=
      card_phaseStartGuard_le M_ph a τ_cut
    calc X_bad.card
        ≤ (longWorkHops τ₀.work B_bank T τ_cut ∪ phaseStartGuard M_ph a τ_cut).card + W_bad.card :=
          Finset.card_union_le _ _
      _ ≤ (longWorkHops τ₀.work B_bank T τ_cut).card + (phaseStartGuard M_ph a τ_cut).card +
            W_bad.card := Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ ≤ M.k * τ_cut + M_ph * τ_cut + M_ph * (K₀ * (B * (M_ph * (D + 1)))) * τ_cut :=
          Nat.add_le_add (Nat.add_le_add hlong hguard) hW_bad
      _ = (M.k + M_ph + M_ph * (K₀ * (B * (M_ph * (D + 1))))) * τ_cut := by ring
  let Anc := ancestors τ₀.work T X_bad D
  let Z_cone : Finset (Fin L) :=
    Finset.univ.filter fun q : Fin L => appendTime τ₀ T (tposOf d b q) ∈ Anc
  have hZ_card : Z_cone.card ≤
      (M.k + 2) ^ D * (M.k + M_ph + M_ph * (K₀ * (B * (M_ph * (D + 1))))) * τ_cut := by
    let f : Fin L → ℕ := fun q => appendTime τ₀ T (tposOf d b q)
    have hinj : Set.InjOn f Z_cone := by
      intro q₁ _ q₂ _ heq
      have h1 : (tposOf d b q₁).1 < (appendList τ₀ T).length := by rw [hlen]; exact (tposOf d b q₁).2
      have h2 : (tposOf d b q₂).1 < (appendList τ₀ T).length := by rw [hlen]; exact (tposOf d b q₂).2
      have htp_eq : tposOf d b q₁ = tposOf d b q₂ :=
        Fin.ext ((appendTime_strictMonoOn τ₀ T).injOn h1 h2 heq)
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
      _ ≤ (M.k + 2) ^ D * X_bad.card := card_ancestors_le τ₀.work T X_bad D
      _ ≤ (M.k + 2) ^ D * ((M.k + M_ph + M_ph * (K₀ * (B * (M_ph * (D + 1))))) * τ_cut) :=
          Nat.mul_le_mul_left _ hX_bad
      _ = (M.k + 2) ^ D * (M.k + M_ph + M_ph * (K₀ * (B * (M_ph * (D + 1))))) * τ_cut := by ring
  -- Unsplit output rows (`Step 4`).
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
  have happ_mono : ∀ {x y : ℕ}, x ≤ y → y < L → appendTime τ₀ T x ≤ appendTime τ₀ T y := by
    intro x y hxy hyL
    rcases eq_or_lt_of_le hxy with rfl | hlt
    · exact le_rfl
    · exact ((appendTime_strictMonoOn τ₀ T)
        (Set.mem_Iio.mpr (by rw [hlenL]; omega))
        (Set.mem_Iio.mpr (by rw [hlenL]; exact hyL)) hlt).le
  let SplitsRow : ℕ → Fin d → Prop := fun θ j =>
    appendTime τ₀ T (loOut j) < θ ∧ θ ≤ appendTime τ₀ T (hiOut j)
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
      have hlt_app : appendTime τ₀ T (hiOut j₁) < appendTime τ₀ T (loOut j₂) :=
        (appendTime_strictMonoOn τ₀ T) (by rw [hlen]; exact (hlo_hi_lt j₁).2)
          (by rw [hlen]; exact (hlo_hi_lt j₂).1.trans_lt (hlo_hi_lt j₂).2) hlt_idx
      omega
    · have hlt_idx : hiOut j₂ < loOut j₁ := by
        dsimp [loOut, hiOut]
        have h1 : (j₂.1 + 1) * W ≤ j₁.1 * W := Nat.mul_le_mul_right W (by omega)
        have h2 : 1 ≤ (j₂.1 + 1) * W := Nat.mul_pos (by omega) hW
        omega
      have hlt_app : appendTime τ₀ T (hiOut j₂) < appendTime τ₀ T (loOut j₁) :=
        (appendTime_strictMonoOn τ₀ T) (by rw [hlen]; exact (hlo_hi_lt j₂).2)
          (by rw [hlen]; exact (hlo_hi_lt j₁).1.trans_lt (hlo_hi_lt j₁).2) hlt_idx
      omega
  let Θ_cuts : Finset ℕ :=
    (Finset.range M_ph).biUnion fun α =>
      (Finset.univ : Finset (SigAt B_bank α)).biUnion fun s =>
        P_set.image fun pStar => (cutOf τ₀ L T B_bank a α (liftSig s) pStar).2
  have hΘ_cuts_card : Θ_cuts.card ≤ M_ph * (K₀ * B) := by
    calc Θ_cuts.card
        ≤ ∑ α ∈ Finset.range M_ph,
            ((Finset.univ : Finset (SigAt B_bank α)).biUnion fun s =>
              P_set.image fun pStar => (cutOf τ₀ L T B_bank a α (liftSig s) pStar).2).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _α ∈ Finset.range M_ph, (K₀ * B) := by
          refine Finset.sum_le_sum fun α hα => ?_
          have hαM : α < M_ph := Finset.mem_range.mp hα
          calc _ ≤ ∑ s ∈ (Finset.univ : Finset (SigAt B_bank α)),
                  (P_set.image fun pStar => (cutOf τ₀ L T B_bank a α (liftSig s) pStar).2).card :=
                  Finset.card_biUnion_le
            _ ≤ ∑ _s ∈ (Finset.univ : Finset (SigAt B_bank α)), B :=
                  Finset.sum_le_sum fun _ _ => Finset.card_image_le.trans hP_card
            _ = (Finset.univ : Finset (SigAt B_bank α)).card * B := by simp
            _ ≤ K₀ * B := Nat.mul_le_mul_right B (hSig_card α hαM)
      _ = M_ph * (K₀ * B) := by simp
  let Θ_all : Finset ℕ := (Finset.range (M_ph + 1)).image a ∪ Θ_cuts
  let J_split : Finset (Fin d) :=
    Θ_all.biUnion fun θ => (Finset.univ : Finset (Fin d)).filter (SplitsRow θ)
  have hJ_split_card : J_split.card ≤ (M_ph + 1) + M_ph * (K₀ * B) := by
    calc J_split.card
        ≤ ∑ θ ∈ Θ_all, ((Finset.univ : Finset (Fin d)).filter (SplitsRow θ)).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _θ ∈ Θ_all, 1 := Finset.sum_le_sum fun θ _ => hSplits_le_one θ
      _ = Θ_all.card := by simp
      _ ≤ ((Finset.range (M_ph + 1)).image a).card + Θ_cuts.card := Finset.card_union_le _ _
      _ ≤ (M_ph + 1) + M_ph * (K₀ * B) := by
          refine Nat.add_le_add ?_ hΘ_cuts_card
          exact Finset.card_image_le.trans (by simp)
  let J_good : Finset (Fin d) := Finset.univ \ J_split
  let α₀ : Fin d → ℕ := fun j => phaseOf M_ph a (appendTime τ₀ T (loOut j))
  have hα₀_lt : ∀ j : Fin d, α₀ j < M_ph := by
    intro j
    have hltL : loOut j < (appendList τ₀ T).length := by
      rw [hlen]; exact (hlo_hi_lt j).1.trans_lt (hlo_hi_lt j).2
    exact (phaseOf_spec ha0 haM (appendTime_lt τ₀ T hltL)).1
  -- Forbidden raw-row bucket set `F(j)` of size `≤ K₀` for each `j ∈ J_good`.
  let matchBuckets : (j : Fin d) → SigAt B_bank (α₀ j) → Finset (Fin B) := fun j s =>
    Finset.univ.filter fun c : Fin B =>
      ∃ u ∈ bucketR c, ∀ m : Fin (B - 1),
        (u.1 < rThresh m ↔
          tcut (cutOf τ₀ L T B_bank a (α₀ j) (liftSig s) (pThresh m)).1
            (cutOf τ₀ L T B_bank a (α₀ j) (liftSig s) (pThresh m)).2
            (appendTime τ₀ T (loOut j)))
  have hmatch_le_one : ∀ (j : Fin d) (s : SigAt B_bank (α₀ j)), (matchBuckets j s).card ≤ 1 := by
    intro j s
    refine Finset.card_le_one.mpr fun c₁ hc₁ c₂ hc₂ => ?_
    obtain ⟨_, u₁, hu₁, hm₁⟩ := Finset.mem_filter.mp hc₁
    obtain ⟨_, u₂, hu₂, hm₂⟩ := Finset.mem_filter.mp hc₂
    have hb₁ := (Finset.mem_filter.mp hu₁).2
    have hb₂ := (Finset.mem_filter.mp hu₂).2
    by_contra hne
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
    · let m : Fin (B - 1) := ⟨c₁.1, by omega⟩
      have h1 : u₁.1 < rThresh m := hb₁.2
      have h2 : ¬ (u₂.1 < rThresh m) := by
        dsimp [rThresh, m]
        have hle_div : (c₁.1 + 1) * d / B ≤ c₂.1 * d / B :=
          Nat.div_le_div_right (Nat.mul_le_mul_right d (by omega))
        omega
      have heq_iff := (hm₁ m).trans (hm₂ m).symm
      exact h2 (heq_iff.mp h1)
    · let m : Fin (B - 1) := ⟨c₂.1, by omega⟩
      have h2 : u₂.1 < rThresh m := hb₂.2
      have h1 : ¬ (u₁.1 < rThresh m) := by
        dsimp [rThresh, m]
        have hle_div : (c₂.1 + 1) * d / B ≤ c₁.1 * d / B :=
          Nat.div_le_div_right (Nat.mul_le_mul_right d (by omega))
        omega
      have heq_iff := (hm₂ m).trans (hm₁ m).symm
      exact h1 (heq_iff.mp h2)
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
  -- Pigeonhole a bucket `cStar : Fin B` avoided by at least half of `J_good`.
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
                Finset.univ \ F j := by
              ext c; simp
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
  -- Construct the rectangle `Rect` and `S_ind := Rect \ Z_cone`.
  let rawRow : Fin L → Fin d := fun q => ⟨q.1 / b / d, (Transpose.Tape.Impl.pos_decomp q.2).1⟩
  let outRow : Fin L → Fin d := fun q => ⟨q.1 / b % d, (Transpose.Tape.Impl.pos_decomp q.2).2.1⟩
  let Rect : Finset (Fin L) :=
    Finset.univ.filter fun q : Fin L => rawRow q ∈ bucketR cStar ∧ outRow q ∈ J_of cStar
  let S_ind : Finset (Fin L) := Rect \ Z_cone
  refine ⟨S_ind, ?_, ?_⟩
  · -- Prove `IsIndependent (fun q => coneSystem τ₀ T Γ d b (tposOf d b q)) S_ind`.
    intro q hqS p hpN hpS
    obtain ⟨hqRect, hqNotZ⟩ := Finset.mem_sdiff.mp hqS
    obtain ⟨hpRect, -⟩ := Finset.mem_sdiff.mp hpS
    obtain ⟨-, hqR, hqJ⟩ := Finset.mem_filter.mp hqRect
    obtain ⟨-, hpR, -⟩ := Finset.mem_filter.mp hpRect
    obtain ⟨hjGood, hcNotF⟩ := Finset.mem_filter.mp hqJ
    have hjNotSplit : outRow q ∉ J_split := (Finset.mem_sdiff.mp hjGood).2
    have hnot_splits : ∀ θ ∈ Θ_all, ¬ SplitsRow θ (outRow q) := by
      intro θ hθ hs
      exact hjNotSplit (Finset.mem_biUnion.mpr ⟨θ, hθ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩⟩)
    -- Extract the `Γ`-free dependency path reading `p` from `t₀ = appendTime τ₀ T (tposOf d b q)`.
    simp only [coneSystem, depCone, Finset.mem_filter, Finset.mem_univ, true_and] at hpN
    obtain ⟨ρ, hdep, hfree, hrd⟩ := hpN
    set ℓ := (tposOf d b q).1
    set t₀ := appendTime τ₀ T ℓ
    have hℓ_bounds := (coord_row_bounds q).2
    have hlo_ℓ : loOut (outRow q) ≤ ℓ := hℓ_bounds.1
    have hℓ_hi : ℓ ≤ hiOut (outRow q) := hℓ_bounds.2
    have hℓ_lt : ℓ < L := (tposOf d b q).2
    have ht₀_lt : t₀ < T := appendTime_lt τ₀ T (by rw [hlen]; exact hℓ_lt)
    have ht0_lo : appendTime τ₀ T (loOut (outRow q)) ≤ t₀ := happ_mono hlo_ℓ hℓ_lt
    have ht0_hi : t₀ ≤ appendTime τ₀ T (hiOut (outRow q)) :=
      happ_mono hℓ_hi (hlo_hi_lt (outRow q)).2
    -- Show `phaseOf M_ph a t₀ = α₀ (outRow q)`.
    have hph_t₀ : phaseOf M_ph a t₀ = α₀ (outRow q) := by
      have hlo_lt_T : appendTime τ₀ T (loOut (outRow q)) < T :=
        appendTime_lt τ₀ T (by rw [hlen]; exact (hlo_hi_lt (outRow q)).1.trans_lt (hlo_hi_lt (outRow q)).2)
      obtain ⟨hαM, ha_lo, ha_hi⟩ := phaseOf_spec ha0 haM hlo_lt_T
      have hmemΘ : a (α₀ (outRow q) + 1) ∈ Θ_all :=
        Finset.mem_union_left _ (Finset.mem_image_of_mem a
          (Finset.mem_range.mpr (by dsimp only [α₀] at *; omega)))
      have hns := hnot_splits _ hmemΘ
      have hhi_lt : appendTime τ₀ T (hiOut (outRow q)) < a (α₀ (outRow q) + 1) := by
        dsimp [SplitsRow] at hns
        dsimp only [α₀] at *
        omega
      exact (phaseOf_eq_iff ha0 haM ha ht₀_lt hαM).mpr ⟨ha_lo.trans ht0_lo, ht0_hi.trans_lt hhi_lt⟩
    -- Bound path length and show `t₀ :: ρ` avoids `X_bad`.
    have hlen_ρ : ρ.length ≤ D := by
      have h1 := hpath (t₀ :: ρ) hdep hfree
      simp at h1; omega
    have hΔ_ρ : ρ.length * τ_cut ≤ Δ := Nat.mul_le_mul_right τ_cut hlen_ρ
    have havoid_X : ∀ x ∈ t₀ :: ρ, x ∉ X_bad := by
      intro x hx hx_bad
      have ht0_anc := ancestors_mono τ₀.work T X_bad hlen_ρ
        (head_mem_ancestors_of_mem_path ρ t₀ hdep hx hx_bad)
      exact hqNotZ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht0_anc⟩)
    have havoid_guard : ∀ x ∈ t₀ :: ρ,
        x ∉ longWorkHops τ₀.work B_bank T τ_cut ∧ x ∉ phaseStartGuard M_ph a τ_cut := by
      intro x hx
      refine ⟨fun h => havoid_X x hx (Finset.mem_union_left _ (Finset.mem_union_left _ h)),
        fun h => havoid_X x hx (Finset.mem_union_left _ (Finset.mem_union_right _ h))⟩
    obtain ⟨s, hs⟩ := depPath_signature_exists (L := L) (Δ := Δ) hτ ha0 haM ha hin hbank
      (α₀ (outRow q)) (hα₀_lt (outRow q)) ht₀_lt hph_t₀ hdep hΔ_ρ havoid_guard hrd
    -- Show `rawRow p ∈ bucketR cStar` forces `cStar ∈ matchBuckets (outRow q) s ⊆ F (outRow q)`.
    apply hcNotF
    refine Finset.mem_biUnion.mpr ⟨s, Finset.mem_univ _, ?_⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, rawRow p, hpR, fun m => ?_⟩
    have hp_mem_P : pThresh m ∈ P_set := Finset.mem_image_of_mem pThresh (Finset.mem_univ m)
    have hnowin : ∀ x ∈ t₀ :: ρ,
        x ∉ windowsOf τ₀ L T Δ B_bank a (α₀ (outRow q)) (liftSig s) (pThresh m) := by
      intro x hx hmem
      apply havoid_X x hx
      refine Finset.mem_union_right _ ?_
      exact Finset.mem_biUnion.mpr ⟨α₀ (outRow q), Finset.mem_range.mpr (hα₀_lt (outRow q)),
        Finset.mem_biUnion.mpr ⟨s, Finset.mem_univ _,
          Finset.mem_biUnion.mpr ⟨pThresh m, hp_mem_P, hmem⟩⟩⟩
    have htcut_t₀ := hs (pThresh m) hnowin
    let c₀ := cutOf τ₀ L T B_bank a (α₀ (outRow q)) (liftSig s) (pThresh m)
    have hc₀_mem : c₀.2 ∈ Θ_all := by
      refine Finset.mem_union_right _ ?_
      exact Finset.mem_biUnion.mpr ⟨α₀ (outRow q), Finset.mem_range.mpr (hα₀_lt (outRow q)),
        Finset.mem_biUnion.mpr ⟨s, Finset.mem_univ _,
          Finset.mem_image.mpr ⟨pThresh m, hp_mem_P, rfl⟩⟩⟩
    have hns_c₀ := hnot_splits c₀.2 hc₀_mem
    have htcut_unsplit : tcut c₀.1 c₀.2 t₀ ↔
        tcut c₀.1 c₀.2 (appendTime τ₀ T (loOut (outRow q))) := by
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
      · have : rawRow (g x) = x.1.1 := Fin.ext hu_eq
        rwa [this]
      · have : outRow (g x) = x.1.2 := Fin.ext hj_eq
        rwa [this]
    have hRect_card : (d / B) * ((d - ((M_ph + 1) + M_ph * (K₀ * B))) / 2) * b ≤ Rect.card := by
      have hJgood_ge : d - ((M_ph + 1) + M_ph * (K₀ * B)) ≤ J_good.card := by
        have hadd := Finset.card_sdiff_add_card_inter (Finset.univ : Finset (Fin d)) J_split
        change J_good.card + (Finset.univ ∩ J_split).card =
          (Finset.univ : Finset (Fin d)).card at hadd
        have hinter : (Finset.univ ∩ J_split).card = J_split.card := by simp
        have huniv : (Finset.univ : Finset (Fin d)).card = d := by simp
        omega
      have hJof_ge : (d - ((M_ph + 1) + M_ph * (K₀ * B))) / 2 ≤ (J_of cStar).card := by omega
      have hR_ge : d / B ≤ (bucketR cStar).card := bucketR_card_ge hB0 cStar
      calc (d / B) * ((d - ((M_ph + 1) + M_ph * (K₀ * B))) / 2) * b
          ≤ (bucketR cStar).card * (J_of cStar).card * b :=
            Nat.mul_le_mul_right b (Nat.mul_le_mul hR_ge hJof_ge)
        _ = ProdSet.card := by simp [ProdSet]
        _ = (ProdSet.image g).card := (Finset.card_image_of_injOn hg_inj).symm
        _ ≤ Rect.card := Finset.card_le_card hg_sub
    have hRect_sub : Rect ⊆ S_ind ∪ Z_cone := by
      intro q hq
      by_cases hqZ : q ∈ Z_cone
      · exact Finset.mem_union_right _ hqZ
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hq, hqZ⟩)
    have hRect_le : Rect.card ≤ S_ind.card + Z_cone.card :=
      (Finset.card_le_card hRect_sub).trans (Finset.card_union_le _ _)
    exact hRect_card.trans (hRect_le.trans (Nat.add_le_add_left hZ_card S_ind.card))

/-- Pure asymptotic/rounding helper for `boundedMacroBank_has_crux`, stated over plain `ℕ`
constants `K₀, C_split, C_cone` so real arithmetic elaborates without unfolding power terms. -/
private theorem crux_bound_of_card_bound (K₀ C_split C_cone : ℕ) (hK₀_pos : 1 ≤ K₀)
    {C η : ℝ} (hC : 1 ≤ C) (hη : 0 < η) {S : ℕ → ℕ}
    (hS : Tendsto (fun d : ℕ => (S d : ℝ) / ((d * d * entryBits d : ℕ) : ℝ)) atTop (nhds 0)) :
    ∃ d_asymp : ℕ, ∀ d ≥ d_asymp, ∀ T S_card m : ℕ,
      let b := entryBits d
      let L := d * d * b
      let B := 2 * K₀
      let τ_cut := Nat.sqrt (max 1 (S d) * (T + 1)) + 1
      (T : ℝ) ≤ C * ((L : ℝ) + 1) →
      (d / B) * ((d - C_split) / 2) * b ≤ S_card + C_cone * τ_cut →
      (S_card : ℝ) ≤ (m : ℝ) →
      (1 / (4 * (K₀ : ℝ)) - η) * (L : ℝ) ≤ (m : ℝ) := by
  set B := 2 * K₀
  have hB_pos : 2 ≤ B := by omega
  set δ : ℝ := η / (4 * ((C_cone : ℝ) + 1))
  have hδ : 0 < δ := by positivity
  have h2C1 : 0 < 2 * C + 1 := by linarith
  set ε_S : ℝ := δ ^ 2 / (2 * C + 1)
  have hε_S : 0 < ε_S := by positivity
  rw [Metric.tendsto_atTop] at hS
  obtain ⟨d_S, hd_S⟩ := hS ε_S hε_S
  let d_lin := ⌈(8 * ((C_split : ℝ) + (B : ℝ) + 2)) / η⌉₊ + C_split + B + 2
  let d_one := ⌈1 / ε_S⌉₊ + ⌈1 / δ⌉₊ + 1
  refine ⟨max d_S (max d_lin d_one), fun d hd T S_card m hT hcard_nat hm_ge => ?_⟩
  have hd_ge_S : d_S ≤ d := (le_max_left _ _).trans hd
  have hd_ge_lin : d_lin ≤ d := (le_max_left _ _).trans ((le_max_right _ _).trans hd)
  have hd_ge_one : d_one ≤ d := (le_max_right _ _).trans ((le_max_right _ _).trans hd)
  have hd1 : 1 ≤ d := by omega
  set b := entryBits d
  have hb1 : 1 ≤ b := one_le_entryBits d
  set L := d * d * b
  have hL_ge_d : d ≤ L := by
    calc d = d * 1 * 1 := by ring
      _ ≤ d * d * b := Nat.mul_le_mul (Nat.mul_le_mul_left d hd1) hb1
  have hL1 : 1 ≤ L := hd1.trans hL_ge_d
  have hLr_pos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL1
  set τ_cut := Nat.sqrt (max 1 (S d) * (T + 1)) + 1
  have hS_lt : (S d : ℝ) ≤ ε_S * (L : ℝ) := by
    have hdist := hd_S d hd_ge_S
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hdist
    exact (div_lt_iff₀ hLr_pos).mp hdist |>.le
  have h1_le_εL : (1 : ℝ) ≤ ε_S * (L : ℝ) := by
    have hceil : 1 / ε_S ≤ (d : ℝ) := by
      calc 1 / ε_S ≤ (⌈1 / ε_S⌉₊ : ℝ) := Nat.le_ceil _
        _ ≤ (d_one : ℝ) := by exact_mod_cast (show ⌈1 / ε_S⌉₊ ≤ d_one by omega)
        _ ≤ (d : ℝ) := by exact_mod_cast hd_ge_one
    have hdL : (d : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL_ge_d
    exact (div_le_iff₀' hε_S).mp (hceil.trans hdL)
  have hmax_le : ((max 1 (S d) : ℕ) : ℝ) ≤ ε_S * (L : ℝ) := by
    rw [Nat.cast_max, Nat.cast_one]
    exact max_le h1_le_εL hS_lt
  have hT1_le : ((T + 1 : ℕ) : ℝ) ≤ (2 * C + 1) * (L : ℝ) := by
    change (T : ℝ) ≤ C * ((L : ℝ) + 1) at hT
    have hL1r : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL1
    have hCL : C ≤ C * (L : ℝ) := le_mul_of_one_le_right (by linarith) hL1r
    rw [Nat.cast_add, Nat.cast_one]
    linarith
  have hN_le : ((max 1 (S d) * (T + 1) : ℕ) : ℝ) ≤ (δ * (L : ℝ)) ^ 2 := by
    rw [Nat.cast_mul]
    calc ((max 1 (S d) : ℕ) : ℝ) * ((T + 1 : ℕ) : ℝ)
        ≤ (ε_S * (L : ℝ)) * ((2 * C + 1) * (L : ℝ)) := by gcongr
      _ = (δ * (L : ℝ)) ^ 2 := by
          dsimp [ε_S]
          field_simp
  have hsqrt_le : (Nat.sqrt (max 1 (S d) * (T + 1)) : ℝ) ≤ δ * (L : ℝ) := by
    have hsq_nat := Nat.sqrt_le (max 1 (S d) * (T + 1))
    have hsq_r : (Nat.sqrt (max 1 (S d) * (T + 1)) : ℝ) *
        (Nat.sqrt (max 1 (S d) * (T + 1)) : ℝ) ≤ ((max 1 (S d) * (T + 1) : ℕ) : ℝ) := by
      exact_mod_cast hsq_nat
    have hnn1 : (0 : ℝ) ≤ (Nat.sqrt (max 1 (S d) * (T + 1)) : ℝ) := by positivity
    have hnn2 : (0 : ℝ) ≤ δ * (L : ℝ) := by positivity
    nlinarith
  have h1_le_δL : (1 : ℝ) ≤ δ * (L : ℝ) := by
    have hceil : 1 / δ ≤ (d : ℝ) := by
      calc 1 / δ ≤ (⌈1 / δ⌉₊ : ℝ) := Nat.le_ceil _
        _ ≤ (d_one : ℝ) := by exact_mod_cast (show ⌈1 / δ⌉₊ ≤ d_one by omega)
        _ ≤ (d : ℝ) := by exact_mod_cast hd_ge_one
    have hdL : (d : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL_ge_d
    exact (div_le_iff₀' hδ).mp (hceil.trans hdL)
  have hcone_err : (C_cone : ℝ) * (τ_cut : ℝ) ≤ (η / 2) * (L : ℝ) := by
    have hτ_r : (τ_cut : ℝ) ≤ 2 * δ * (L : ℝ) := by
      show ((Nat.sqrt (max 1 (S d) * (T + 1)) + 1 : ℕ) : ℝ) ≤ 2 * δ * (L : ℝ)
      push_cast
      linarith
    have hC_nn : (0 : ℝ) ≤ (C_cone : ℝ) := by positivity
    calc (C_cone : ℝ) * (τ_cut : ℝ)
        ≤ (C_cone : ℝ) * (2 * δ * (L : ℝ)) := mul_le_mul_of_nonneg_left hτ_r hC_nn
      _ ≤ ((C_cone : ℝ) + 1) * (2 * δ * (L : ℝ)) := by nlinarith
      _ = (η / 2) * (L : ℝ) := by
          dsimp [δ]
          field_simp
          ring
  have hd_sub : C_split ≤ d := by omega
  have hdivB_r : (d : ℝ) / (B : ℝ) - 1 ≤ ((d / B : ℕ) : ℝ) := by
    have hmod := Nat.div_add_mod d B
    have hlt := Nat.mod_lt d (show 0 < B by omega)
    have hBr : (0 : ℝ) < (B : ℝ) := by positivity
    rw [sub_le_iff_le_add, div_le_iff₀ hBr]
    have h1 : (d : ℝ) ≤ ((B * (d / B) + B : ℕ) : ℝ) := by
      exact_mod_cast (by omega : d ≤ B * (d / B) + B)
    push_cast at h1
    linarith
  have hdiv2_r : ((d : ℝ) - (C_split : ℝ) - 1) / 2 ≤ (((d - C_split) / 2 : ℕ) : ℝ) := by
    have h1 : d - C_split ≤ 2 * ((d - C_split) / 2) + 1 := by omega
    have h1r : ((d - C_split : ℕ) : ℝ) ≤ ((2 * ((d - C_split) / 2) + 1 : ℕ) : ℝ) := by
      exact_mod_cast h1
    rw [Nat.cast_sub hd_sub] at h1r
    push_cast at h1r
    linarith
  have hpos_f1 : (0 : ℝ) ≤ (d : ℝ) / (B : ℝ) - 1 := by
    have hBr : (0 : ℝ) < (B : ℝ) := by positivity
    rw [sub_nonneg, le_div_iff₀ hBr]
    have : B ≤ d := by omega
    have hr : (B : ℝ) ≤ (d : ℝ) := by exact_mod_cast this
    linarith
  have hpos_f2 : (0 : ℝ) ≤ ((d : ℝ) - (C_split : ℝ) - 1) / 2 := by
    have : C_split + 1 ≤ d := by omega
    have hr : ((C_split + 1 : ℕ) : ℝ) ≤ (d : ℝ) := by exact_mod_cast this
    push_cast at hr
    linarith
  have hrect_r : ((1 / (4 * (K₀ : ℝ)) - η / 2) * (L : ℝ)) ≤
      (((d / B) * ((d - C_split) / 2) * b : ℕ) : ℝ) := by
    have hprod : ((d : ℝ) / (B : ℝ) - 1) * (((d : ℝ) - (C_split : ℝ) - 1) / 2) * (b : ℝ) ≤
        (((d / B) * ((d - C_split) / 2) * b : ℕ) : ℝ) := by
      rw [Nat.cast_mul ((d / B) * ((d - C_split) / 2)) b,
        Nat.cast_mul (d / B) ((d - C_split) / 2)]
      have hb_nn : (0 : ℝ) ≤ (b : ℝ) := by positivity
      exact mul_le_mul_of_nonneg_right (mul_le_mul hdivB_r hdiv2_r hpos_f2
        (hpos_f1.trans hdivB_r)) hb_nn
    have hB_eq : (B : ℝ) = 2 * (K₀ : ℝ) := by simp [B]
    have hK₀_r : (1 : ℝ) ≤ (K₀ : ℝ) := by exact_mod_cast hK₀_pos
    let ceil_term := ⌈(8 * ((C_split : ℝ) + (B : ℝ) + 2)) / η⌉₊
    have hlin_ge : (8 * ((C_split : ℝ) + (B : ℝ) + 2)) / η ≤ (d : ℝ) := by
      calc (8 * ((C_split : ℝ) + (B : ℝ) + 2)) / η
          ≤ (ceil_term : ℝ) := Nat.le_ceil _
        _ ≤ (d_lin : ℝ) := Nat.cast_le.mpr (by omega)
        _ ≤ (d : ℝ) := Nat.cast_le.mpr hd_ge_lin
    have hηd : 8 * ((C_split : ℝ) + (B : ℝ) + 2) ≤ η * (d : ℝ) := by
      have h1 := (div_le_iff₀ hη).mp hlin_ge
      linarith only [h1]
    have hL_eq : (L : ℝ) = (d : ℝ) * (d : ℝ) * (b : ℝ) := by simp [L]
    have hident : ((d : ℝ) / (B : ℝ) - 1) * (((d : ℝ) - (C_split : ℝ) - 1) / 2) * (b : ℝ) =
        (1 / (4 * (K₀ : ℝ))) * ((d : ℝ) * (d : ℝ) * (b : ℝ)) -
          (((C_split : ℝ) + 1) / (4 * (K₀ : ℝ)) + 1 / 2) * ((d : ℝ) * (b : ℝ)) +
          (((C_split : ℝ) + 1) / 2) * (b : ℝ) := by
      rw [hB_eq]
      field_simp
      ring
    have herr_lin : (((C_split : ℝ) + 1) / (4 * (K₀ : ℝ)) + 1 / 2) * ((d : ℝ) * (b : ℝ)) ≤
        (η / 2) * ((d : ℝ) * (d : ℝ) * (b : ℝ)) := by
      have hcoef : ((C_split : ℝ) + 1) / (4 * (K₀ : ℝ)) + 1 / 2 ≤
          (C_split : ℝ) + (B : ℝ) + 2 := by
        have hdiv_le : ((C_split : ℝ) + 1) / (4 * (K₀ : ℝ)) ≤ (C_split : ℝ) + 1 :=
          div_le_self (by positivity) (by linarith only [hK₀_r])
        have hB_nn : (0 : ℝ) ≤ (B : ℝ) := by positivity
        linarith only [hdiv_le, hB_nn]
      have hdb_nn : (0 : ℝ) ≤ (d : ℝ) * (b : ℝ) := by positivity
      calc (((C_split : ℝ) + 1) / (4 * (K₀ : ℝ)) + 1 / 2) * ((d : ℝ) * (b : ℝ))
          ≤ ((C_split : ℝ) + (B : ℝ) + 2) * ((d : ℝ) * (b : ℝ)) :=
            mul_le_mul_of_nonneg_right hcoef hdb_nn
        _ ≤ ((η * (d : ℝ)) / 8) * ((d : ℝ) * (b : ℝ)) := by
            refine mul_le_mul_of_nonneg_right ?_ hdb_nn
            linarith only [hηd]
        _ = (η / 8) * ((d : ℝ) * (d : ℝ) * (b : ℝ)) := by ring
        _ ≤ (η / 2) * ((d : ℝ) * (d : ℝ) * (b : ℝ)) := by
            have hddb : (0 : ℝ) ≤ (d : ℝ) * (d : ℝ) * (b : ℝ) := by positivity
            exact mul_le_mul_of_nonneg_right (by linarith only [hη]) hddb
    have hb_nn : (0 : ℝ) ≤ (((C_split : ℝ) + 1) / 2) * (b : ℝ) := by positivity
    rw [hL_eq]
    linarith only [hprod, hident, herr_lin, hb_nn]
  have hcard_r : (((d / B) * ((d - C_split) / 2) * b : ℕ) : ℝ) ≤
      (S_card : ℝ) + (C_cone : ℝ) * (τ_cut : ℝ) := by
    exact_mod_cast hcard_nat
  linarith only [hrect_r, hcard_r, hcone_err, hm_ge]

/-- **Theorem 9.2(1) (`boundedMacroBank_has_crux`, Theorem B)**: every machine in Class BM with sublinear
workspace cell bound `S(d) / (d² entryBits(d)) → 0` satisfies the depth-independent machine crux
`MachineCrux M C (1 / (4 * K₀))`, where `K₀ = (B_bank.card + 1) ^ (M_ph - 1)`. -/
theorem boundedMacroBank_has_crux {M : TM} {C : ℝ} {M_ph : ℕ} {B_bank : Finset (Fin M.k)}
    {S : ℕ → ℕ} (hC : 1 ≤ C) (hMph : 1 ≤ M_ph)
    (hBM : BoundedMacroBank M C M_ph B_bank S)
    (hS : Tendsto (fun d : ℕ => (S d : ℝ) / ((d * d * entryBits d : ℕ) : ℝ)) atTop (nhds 0)) :
    MachineCrux M C (1 / (4 * (((B_bank.card + 1) ^ (M_ph - 1) : ℕ) : ℝ))) := by
  intro D η hη
  obtain ⟨d_BM, hd_BM⟩ := hBM
  have hK₀_pos : 1 ≤ (B_bank.card + 1) ^ (M_ph - 1) := Nat.one_le_pow _ _ (by omega)
  obtain ⟨d_asymp, hd_asymp⟩ := crux_bound_of_card_bound
    ((B_bank.card + 1) ^ (M_ph - 1))
    ((M_ph + 1) + M_ph * (((B_bank.card + 1) ^ (M_ph - 1)) *
      (2 * ((B_bank.card + 1) ^ (M_ph - 1)))))
    ((M.k + 2) ^ D * (M.k + M_ph + M_ph * (((B_bank.card + 1) ^ (M_ph - 1)) *
      ((2 * ((B_bank.card + 1) ^ (M_ph - 1))) * (M_ph * (D + 1))))))
    hK₀_pos hC hη hS
  refine ⟨max d_BM (max d_asymp 1), fun d hd I hI m E hE => ?_⟩
  have hd_ge_BM : d_BM ≤ d := (le_max_left _ _).trans hd
  have hd_ge_asymp : d_asymp ≤ d := (le_max_left _ _).trans ((le_max_right _ _).trans hd)
  have hd1 : 1 ≤ d := (le_max_right _ _).trans ((le_max_right _ _).trans hd)
  have hb1 : 1 ≤ entryBits d := one_le_entryBits d
  obtain ⟨T, Γ, hobl, hT, hlen, hpath, rfl⟩ := hI
  obtain ⟨⟨a, ha0, haM, ha, hin, hbank⟩, hwork⟩ := hd_BM d hd_ge_BM T hobl hT
  obtain ⟨S_ind, hInd, hcard_nat⟩ := macroBank_independent_exists hMph hd1 hb1 hlen hpath
    ha0 haM ha hin hbank hwork
  exact hd_asymp d hd_ge_asymp T S_ind.card m hT hcard_nat
    (indexCode_length_ge_of_independent hE hInd)

/-- **Theorem 9.2(2) (`boundedMacroBank_excludes`, Theorem B)**: no machine in Class BM with sublinear
workspace cell bound `S(d) / (d² entryBits(d)) → 0` can transpose in oblivious linear time. -/
theorem boundedMacroBank_excludes {M : TM} {C : ℝ} {M_ph : ℕ} {B_bank : Finset (Fin M.k)}
    {S : ℕ → ℕ} (hC : 1 ≤ C) (hMph : 1 ≤ M_ph)
    (hBM : BoundedMacroBank M C M_ph B_bank S)
    (hS : Tendsto (fun d : ℕ => (S d : ℝ) / ((d * d * entryBits d : ℕ) : ℝ)) atTop (nhds 0)) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ T : ℕ, ¬ ObliviousLinTime M d (entryBits d) C T := by
  have hcrux := boundedMacroBank_has_crux hC hMph hBM hS
  set K₀ : ℝ := (((B_bank.card + 1) ^ (M_ph - 1) : ℕ) : ℝ)
  have hK₀_pos : (0 : ℝ) < K₀ := by positivity
  refine machine_crux_excludes hC (ε := 1 / (8 * K₀)) (ρ := 1 / (4 * K₀)) (by positivity) ?_
    (hcrux _)
  have : 1 / (8 * K₀) < 1 / (4 * K₀) := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    linarith
  exact this

end NativeRelations
