import NativeRelations.MacroBankCrux
import NativeRelations.NativeGapCriterion

/-!
# Coarse Monotone Sweeps, Jitter Guards, and Simulator Preservation

Defines `CoarseMonoOnInterval`, `TraceHasJitterBM`, and `AdaptiveJitterBM`, develops the intra-phase
and inter-phase guard machinery (`hop_upper_injOn`) for bounded-jitter sweeps, and proves that the
fifteenth paper's aligned simulator `Native.machine M hs` preserves bounded-jitter bank schedules
(`native_machine_preserves_jitterBM`).
-/

set_option autoImplicit false

namespace NativeRelations

open Filter Finset Transpose Transpose.Tape BoundedNesting MergeDepth MotionDepthCodes
  BoundedStackDepth TapeStorageRates
open scoped BigOperators Topology

/-! ## §1. Coarse Monotonicity and Jittered BM Definitions -/

/-- A walk `x : ℕ → ℤ` is coarsely monotone on `[lo, hi)` with reversal amplitude `A : ℕ`:
either `x t - A ≤ x t'` for all `lo ≤ t ≤ t' < hi`, or `x t' ≤ x t + A` for all
`lo ≤ t ≤ t' < hi`. -/
def CoarseMonoOnInterval (x : ℕ → ℤ) (lo hi A : ℕ) : Prop :=
  (∀ t t', lo ≤ t → t ≤ t' → t' < hi → x t - (A : ℤ) ≤ x t') ∨
    (∀ t t', lo ≤ t → t ≤ t' → t' < hi → x t' ≤ x t + (A : ℤ))

/-- Single-trace jittered BM predicate: `[0, T)` partitions into
`M_ph` contiguous macro-phases on each of which the input walk `z none` and every bank walk
`z (some (some j))` (`j ∈ B_bank`) are `A`-coarsely monotone, while every workspace walk
`w ∉ B_bank` visits at most `S` distinct cells before `T`. -/
def TraceHasJitterBM {k : ℕ} (z : Tp k → ℕ → ℤ) (T M_ph : ℕ) (B_bank : Finset (Fin k))
    (A S : ℕ) : Prop :=
  (∃ a : ℕ → ℕ, a 0 = 0 ∧ a M_ph = T ∧ (∀ α < M_ph, a α ≤ a (α + 1)) ∧
    (∀ α < M_ph, CoarseMonoOnInterval (z none) (a α) (a (α + 1)) A) ∧
    (∀ α < M_ph, ∀ j ∈ B_bank, CoarseMonoOnInterval (z (some (some j))) (a α) (a (α + 1)) A)) ∧
  (∀ w : Fin k, w ∉ B_bank → ((Finset.range T).image (z (some (some w)))).card ≤ S)

/-- Adaptive jittered BM class: for all `d ≥ d_BM` and every input
`X : Fin L → Bool` (`L = d² entryBits(d)`) on which `M` halts at time `T ≤ C (L + 1)`, the run's
head walks satisfy `TraceHasJitterBM` with parameters `(M_ph, B_bank, A d, S d)`. Phase boundaries,
orientation signs, pause schedules, and workspace cell sets may vary arbitrarily across inputs. -/
def AdaptiveJitterBM (M : TM) (C : ℝ) (M_ph : ℕ) (B_bank : Finset (Fin M.k))
    (A S : ℕ → ℕ) : Prop :=
  ∃ d_BM : ℕ, ∀ d ≥ d_BM,
    let L := d * d * entryBits d
    ∀ (X : Fin L → Bool) (T : ℕ),
      Transpose.Tape.HaltsAt M (List.ofFn X) T →
      (T : ℝ) ≤ C * ((L : ℝ) + 1) →
      TraceHasJitterBM (runWalks M (List.ofFn X)) T M_ph B_bank (A d) (S d)

/-! ## §2. Crossing-Hop Spatial Injectivity and Coarse Pullback Guards -/

/-- Upper endpoints `u ∈ [θ, T)` of long hops `v → u` crossing `θ` (`v < θ ≤ u`). -/
noncomputable def crossingHops (x : ℕ → ℤ) (T θ : ℕ) : Finset ℕ := by
  classical exact (Finset.range T).filter fun u => θ ≤ u ∧ ∃ v < θ, IsHop x T v u

/-- Universal spatial injectivity on crossing hops ( Step 1(a)): if two hops both
start strictly before `θ` and end at `θ ≤ u₁ < u₂`, they cannot visit the same tape cell because
`u₁ ∈ (v₂, u₂)` would violate the first-return property of `IsHop x T v₂ u₂`. -/
theorem hop_upper_injOn (x : ℕ → ℤ) (T θ : ℕ) :
    Set.InjOn x (crossingHops x T θ : Set ℕ) := by
  classical
  intro u₁ hu₁ u₂ hu₂ heq
  unfold crossingHops at hu₁ hu₂
  obtain ⟨_, hθ₁, v₁, hv₁, hhop₁⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hu₁)
  obtain ⟨_, hθ₂, v₂, hv₂, hhop₂⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hu₂)
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hmem : u₁ ∈ Finset.Ioo v₂ u₂ := Finset.mem_Ioo.mpr ⟨by omega, hlt⟩
    exact hhop₂.2.2.2 u₁ hmem (heq.trans hhop₂.2.2.1)
  · have hmem : u₂ ∈ Finset.Ioo v₁ u₁ := Finset.mem_Ioo.mpr ⟨by omega, hgt⟩
    exact hhop₁.2.2.2 u₂ hmem (heq.symm.trans hhop₁.2.2.1)

/-- Any subset `G ⊆ crossingHops x T θ` whose cell positions lie in `[z₀ - A, z₀ + A]` has
cardinality at most `2 * A + 1`. -/
theorem card_subset_crossingHops_le {x : ℕ → ℤ} {T θ A : ℕ} {G : Finset ℕ}
    (hsub : G ⊆ crossingHops x T θ) {z₀ : ℤ}
    (himg : ∀ u ∈ G, z₀ - (A : ℤ) ≤ x u ∧ x u ≤ z₀ + (A : ℤ)) :
    G.card ≤ 2 * A + 1 := by
  classical
  have hinj : Set.InjOn x (G : Set ℕ) := (hop_upper_injOn x T θ).mono (Finset.coe_subset.mpr hsub)
  let box : Finset ℤ := (Finset.range (2 * A + 1)).image fun i : ℕ => z₀ - (A : ℤ) + (i : ℤ)
  have hbox_sub : G.image x ⊆ box := by
    intro y hy
    obtain ⟨u, huG, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hlo, hhi⟩ := himg u huG
    refine Finset.mem_image.mpr ⟨(x u - (z₀ - (A : ℤ))).toNat, Finset.mem_range.mpr (by omega), ?_⟩
    omega
  calc G.card
      = (G.image x).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ box.card := Finset.card_le_card hbox_sub
    _ ≤ (Finset.range (2 * A + 1)).card := Finset.card_image_le
    _ = 2 * A + 1 := Finset.card_range _

/-- Intra-phase straddling hop guard: upper endpoints `u ∈ [lo, hi)` of hops `v → u` with
`lo ≤ v < θ ≤ u < hi`. -/
noncomputable def intraStradGuard (x : ℕ → ℤ) (T lo hi θ : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range T).filter fun u =>
    lo ≤ u ∧ u < hi ∧ θ ≤ u ∧ ∃ v, lo ≤ v ∧ v < θ ∧ IsHop x T v u

theorem card_intraStradGuard_le {x : ℕ → ℤ} {T lo hi θ A : ℕ}
    (hmono : CoarseMonoOnInterval x lo hi A) :
    (intraStradGuard x T lo hi θ).card ≤ 2 * A + 1 := by
  classical
  by_cases hθ_in : lo < θ ∧ θ < hi
  · obtain ⟨hlo_θ, hθ_hi⟩ := hθ_in
    have hsub : intraStradGuard x T lo hi θ ⊆ crossingHops x T θ := by
      intro u hu
      unfold intraStradGuard at hu
      unfold crossingHops
      obtain ⟨huT, _, _, hθu, v, _, hvθ, hhop⟩ := Finset.mem_filter.mp hu
      exact Finset.mem_filter.mpr ⟨huT, hθu, v, hvθ, hhop⟩
    refine card_subset_crossingHops_le hsub (z₀ := x θ) fun u hu => ?_
    unfold intraStradGuard at hu
    obtain ⟨_, hlo_u, hu_hi, hθu, v, hlo_v, hvθ, hhop⟩ := Finset.mem_filter.mp hu
    have heq : x u = x v := hhop.2.2.1
    rcases hmono with hinc | hdec
    · have h1 := hinc v θ hlo_v (by omega) hθ_hi
      have h2 := hinc θ u (by omega) hθu hu_hi
      omega
    · have h1 := hdec v θ hlo_v (by omega) hθ_hi
      have h2 := hdec θ u (by omega) hθu hu_hi
      omega
  · have hemp : intraStradGuard x T lo hi θ = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro u hu
      unfold intraStradGuard at hu
      obtain ⟨_, _, hu_hi, hθu, v, hlo_v, hvθ, _⟩ := Finset.mem_filter.mp hu
      omega
    rw [hemp]
    simp

/-- Canonical coarse orientation sign on `[lo, hi)` at amplitude `A`. -/
noncomputable def coarseSign (x : ℕ → ℤ) (lo hi A : ℕ) : Bool := by
  classical exact decide (∀ t t', lo ≤ t → t ≤ t' → t' < hi → x t - (A : ℤ) ≤ x t')

theorem coarseSign_spec {x : ℕ → ℤ} {lo hi A : ℕ} (h : CoarseMonoOnInterval x lo hi A) :
    if coarseSign x lo hi A then
      (∀ t t', lo ≤ t → t ≤ t' → t' < hi → x t - (A : ℤ) ≤ x t')
    else
      (∀ t t', lo ≤ t → t ≤ t' → t' < hi → x t' ≤ x t + (A : ℤ)) := by
  classical
  unfold coarseSign
  by_cases h1 : ∀ t t', lo ≤ t → t ≤ t' → t' < hi → x t - (A : ℤ) ≤ x t'
  · simp only [decide_eq_true_eq.mpr h1, ↓reduceIte]
    exact h1
  · have h2 := h.resolve_left h1
    simp only [decide_eq_false h1, Bool.false_eq_true, ↓reduceIte]
    exact h2

/-- Pulled-back cut across inter-phase bank hops `BankInterRel x T lo' hi' lo hi` under coarse
orientation signs at amplitude `A`. -/
noncomputable def interBankPull (x : ℕ → ℤ) (T lo' hi' lo hi A : ℕ) (c : Bool × ℕ) : Bool × ℕ :=
  pullCut T (BankInterRel x T lo' hi' lo hi)
    (coarseSign x lo hi A == coarseSign x lo' hi' A) c

/-- Guard of upper endpoints `u ∈ [lo, hi)` where `interBankPull` disagrees with `c`. -/
noncomputable def interBankGuard (x : ℕ → ℤ) (T lo' hi' lo hi A : ℕ) (c : Bool × ℕ) :
    Finset ℕ := by
  classical
  let cp := interBankPull x T lo' hi' lo hi A c
  exact (Finset.range T).filter fun u =>
    ∃ v, BankInterRel x T lo' hi' lo hi u v ∧ ¬ (tcut cp.1 cp.2 u ↔ tcut c.1 c.2 v)

theorem interBankPull_spec {x : ℕ → ℤ} {T lo' hi' lo hi A : ℕ} {c : Bool × ℕ} {u v : ℕ}
    (hR : BankInterRel x T lo' hi' lo hi u v)
    (hnot : u ∉ interBankGuard x T lo' hi' lo hi A c) :
    tcut (interBankPull x T lo' hi' lo hi A c).1
      (interBankPull x T lo' hi' lo hi A c).2 u ↔ tcut c.1 c.2 v := by
  classical
  have huT : u < T := hR.2.2.2.2.2.1
  by_contra hmis
  apply hnot
  unfold interBankGuard
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr huT, v, hR, hmis⟩

/-- Key bound ( Step 1(c)): `interBankGuard` has size at most `2 * A + 1`. -/
theorem card_interBankGuard_le {x : ℕ → ℤ} {T lo' hi' lo hi A : ℕ}
    (hsep : hi' ≤ lo) (hmono' : CoarseMonoOnInterval x lo' hi' A)
    (hmono : CoarseMonoOnInterval x lo hi A) (c : Bool × ℕ) :
    (interBankGuard x T lo' hi' lo hi A c).card ≤ 2 * A + 1 := by
  classical
  set G := interBankGuard x T lo' hi' lo hi A c
  by_cases hG : G.Nonempty
  · have hsub : G ⊆ crossingHops x T lo := by
      intro u hu
      obtain ⟨huT, v, hR, _⟩ := Finset.mem_filter.mp hu
      unfold crossingHops
      exact Finset.mem_filter.mpr ⟨huT, hR.1, v, hR.2.2.2.1.trans_le hsep, hR.2.2.2.2⟩
    let R := BankInterRel x T lo' hi' lo hi
    let s := coarseSign x lo hi A
    let s' := coarseSign x lo' hi' A
    let eta := (s == s')
    let S := (Finset.range T).filter fun x' => ∃ y', R x' y' ∧ tcut c.1 c.2 y'
    have hpull_eq : interBankPull x T lo' hi' lo hi A c =
        (if (eta == c.1) then
          (true, if h : S.Nonempty then S.min' h else T)
        else
          (false, if h : S.Nonempty then S.max' h + 1 else 0)) := by
      unfold interBankPull pullCut
      rfl
    -- Show `S` must be nonempty because `G` is nonempty.
    obtain ⟨u_ex, hu_ex⟩ := hG
    obtain ⟨hu_ex_T, v_ex, hR_ex, hmis_ex⟩ := Finset.mem_filter.mp hu_ex
    have hu_ex_lt : u_ex < T := Finset.mem_range.mp hu_ex_T
    have hS : S.Nonempty := by
      by_contra hSno
      apply hmis_ex
      rw [hpull_eq]
      have hnc : ¬ tcut c.1 c.2 v_ex := fun hcv =>
        hSno ⟨u_ex, Finset.mem_filter.mpr ⟨hu_ex_T, v_ex, hR_ex, hcv⟩⟩
      by_cases hp : (eta == c.1) = true
      · simp only [hp, ↓reduceIte, hSno, ↓reduceDIte, tcut]
        exact ⟨fun h => by omega, fun h => absurd h hnc⟩
      · have hpf : (eta == c.1) = false := Bool.eq_false_iff.mpr hp
        simp only [hpf, Bool.false_eq_true, ↓reduceIte, hSno, ↓reduceDIte, tcut]
        exact ⟨fun h => by omega, fun h => absurd h hnc⟩
    let uStar : ℕ := if (eta == c.1) then S.min' hS else S.max' hS
    have huStar_mem : uStar ∈ S := by
      dsimp only [uStar]
      split_ifs
      · exact Finset.min'_mem S hS
      · exact Finset.max'_mem S hS
    obtain ⟨_, vStar, hRStar, hcStar⟩ := Finset.mem_filter.mp huStar_mem
    have hs_spec := coarseSign_spec hmono
    have hs'_spec := coarseSign_spec hmono'
    change (if s then _ else _) at hs_spec
    change (if s' then _ else _) at hs'_spec
    refine card_subset_crossingHops_le hsub (z₀ := x uStar) fun u hu => ?_
    obtain ⟨hu_r, v, hR, hmis⟩ := Finset.mem_filter.mp hu
    have huT : u < T := Finset.mem_range.mp hu_r
    -- First show `¬ tcut c.1 c.2 v` and `tcut cp.1 cp.2 u`.
    have hnot_cv : ¬ tcut c.1 c.2 v := by
      intro hcv
      apply hmis
      have huS : u ∈ S := Finset.mem_filter.mpr ⟨hu_r, v, hR, hcv⟩
      rw [hpull_eq]
      by_cases hp : (eta == c.1) = true
      · simp only [hp, ↓reduceIte, hS, ↓reduceDIte, tcut]
        exact ⟨fun _ => hcv, fun _ => Finset.min'_le S u huS⟩
      · have hpf : (eta == c.1) = false := Bool.eq_false_iff.mpr hp
        simp only [hpf, Bool.false_eq_true, ↓reduceIte, hS, ↓reduceDIte, tcut]
        have hle := Finset.le_max' S u huS
        exact ⟨fun _ => hcv, fun _ => by omega⟩
    have hcp_u : tcut (interBankPull x T lo' hi' lo hi A c).1
        (interBankPull x T lo' hi' lo hi A c).2 u := by
      by_contra hncp
      exact hmis ⟨fun h => absurd h hncp, fun h => absurd h hnot_cv⟩
    rw [hpull_eq] at hcp_u
    have hx_eq : x u = x v := hR.2.2.2.2.2.2.1
    have hxStar_eq : x uStar = x vStar := hRStar.2.2.2.2.2.2.1
    have hu_lo : lo ≤ u := hR.1
    have hu_hi : u < hi := hR.2.1
    have hv_lo : lo' ≤ v := hR.2.2.1
    have hv_hi : v < hi' := hR.2.2.2.1
    have huS_lo : lo ≤ uStar := hRStar.1
    have huS_hi : uStar < hi := hRStar.2.1
    have hvS_lo : lo' ≤ vStar := hRStar.2.2.1
    have hvS_hi : vStar < hi' := hRStar.2.2.2.1
    -- Extract ordering between `(u, uStar)` and `(v, vStar)` across all 8 sign cases.
    have hu_ord : if (eta == c.1) then uStar ≤ u else u ≤ uStar := by
      by_cases hp : (eta == c.1) = true
      · simp only [hp, ↓reduceIte, hS, ↓reduceDIte, tcut] at hcp_u ⊢
        simpa [uStar, hp] using hcp_u
      · have hpf : (eta == c.1) = false := Bool.eq_false_iff.mpr hp
        simp only [hpf, Bool.false_eq_true, ↓reduceIte, hS, ↓reduceDIte, tcut] at hcp_u ⊢
        have : u < S.max' hS + 1 := hcp_u
        dsimp only [uStar]
        rw [hpf]
        simp only [Bool.false_eq_true, ↓reduceIte]
        omega
    have hv_ord : if c.1 then v ≤ vStar else vStar ≤ v := by
      cases hc1 : c.1 <;> simp only [hc1, tcut, ↓reduceIte, Bool.false_eq_true] at hcStar hnot_cv ⊢ <;>
        omega
    dsimp only [eta] at hu_ord
    cases hs_val : s <;> cases hs'_val : s' <;> cases hc1 : c.1
    all_goals
      simp [hs_val, hs'_val, hc1] at hs_spec hs'_spec hu_ord hv_ord
    · have h1 := hs_spec u uStar hu_lo hu_ord huS_hi
      have h2 := hs'_spec vStar v hvS_lo hv_ord hv_hi
      omega
    · have h1 := hs_spec uStar u huS_lo hu_ord hu_hi
      have h2 := hs'_spec v vStar hv_lo hv_ord hvS_hi
      omega
    · have h1 := hs_spec uStar u huS_lo hu_ord hu_hi
      have h2 := hs'_spec vStar v hvS_lo hv_ord hv_hi
      omega
    · have h1 := hs_spec u uStar hu_lo hu_ord huS_hi
      have h2 := hs'_spec v vStar hv_lo hv_ord hvS_hi
      omega
    · have h1 := hs_spec uStar u huS_lo hu_ord hu_hi
      have h2 := hs'_spec vStar v hvS_lo hv_ord hv_hi
      omega
    · have h1 := hs_spec u uStar hu_lo hu_ord huS_hi
      have h2 := hs'_spec v vStar hv_lo hv_ord hvS_hi
      omega
    · have h1 := hs_spec u uStar hu_lo hu_ord huS_hi
      have h2 := hs'_spec vStar v hvS_lo hv_ord hv_hi
      omega
    · have h1 := hs_spec uStar u huS_lo hu_ord hu_hi
      have h2 := hs'_spec v vStar hv_lo hv_ord hvS_hi
      omega
  · rw [Finset.not_nonempty_iff_eq_empty.mp hG]
    simp

/-- Input-read relation on `[lo, hi)` for an arbitrary input walk `x_in : ℕ → ℤ`. -/
def ReadIntRel (x_in : ℕ → ℤ) (lo hi t q : ℕ) : Prop :=
  lo ≤ t ∧ t < hi ∧ x_in t = (q : ℤ)

/-- Coarse input-read threshold pullback on `[lo, hi)`. -/
noncomputable def coarsePullRead (x_in : ℕ → ℤ) (T lo hi A pStar : ℕ) : Bool × ℕ :=
  pullCut T (ReadIntRel x_in lo hi) (coarseSign x_in lo hi A) (false, pStar)

/-- Zero-time-exception read pullback ( Step 1(d)): for every `t ∈ [lo, hi)` and
every raw coordinate `q` avoiding `[pStar, pStar + A)`, `coarsePullRead` agrees with `q < pStar`. -/
theorem coarsePullRead_spec {x_in : ℕ → ℤ} {T lo hi A pStar t q : ℕ}
    (hhiT : hi ≤ T) (hmono : CoarseMonoOnInterval x_in lo hi A)
    (hlo : lo ≤ t) (hhi : t < hi) (hx : x_in t = (q : ℤ))
    (hnot_band : ¬ (pStar ≤ q ∧ q < pStar + A)) :
    tcut (coarsePullRead x_in T lo hi A pStar).1
      (coarsePullRead x_in T lo hi A pStar).2 t ↔ q < pStar := by
  classical
  have htT : t < T := hhi.trans_le hhiT
  have hR : ReadIntRel x_in lo hi t q := ⟨hlo, hhi, hx⟩
  let s_in := coarseSign x_in lo hi A
  let S := (Finset.range T).filter fun x => ∃ y, ReadIntRel x_in lo hi x y ∧ tcut false pStar y
  have hpull_eq : coarsePullRead x_in T lo hi A pStar =
      (if (s_in == false) then
        (true, if h : S.Nonempty then S.min' h else T)
      else
        (false, if h : S.Nonempty then S.max' h + 1 else 0)) := by
    unfold coarsePullRead pullCut
    rfl
  have hs_spec := coarseSign_spec hmono
  change (if s_in then _ else _) at hs_spec
  rw [hpull_eq]
  cases hs_val : s_in
  · -- `s_in = false` (`x_in` coarsely non-increasing): `(s_in == false) = true`.
    simp only [hs_val, Bool.false_beq, ↓reduceIte, Bool.false_eq_true] at hs_spec ⊢
    change tcut true (if h : S.Nonempty then S.min' h else T) t ↔ q < pStar
    by_cases hS : S.Nonempty
    · simp only [hS, ↓reduceDIte, tcut, ↓reduceIte]
      constructor
      · intro hmin
        obtain ⟨_, qStar, ⟨hloS, _, hxS⟩, hltS⟩ := Finset.mem_filter.mp (Finset.min'_mem S hS)
        simp only [tcut, Bool.false_eq_true, ↓reduceIte] at hltS
        have hstep := hs_spec (S.min' hS) t hloS hmin hhi
        omega
      · intro hqp
        exact Finset.min'_le S t (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr htT, q, hR, hqp⟩)
    · simp only [hS, ↓reduceDIte, tcut, ↓reduceIte]
      constructor
      · intro hle; omega
      · intro hqp
        exfalso
        exact hS ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr htT, q, hR, hqp⟩⟩
  · -- `s_in = true` (`x_in` coarsely non-decreasing): `(s_in == false) = false`.
    simp only [hs_val, Bool.true_beq, Bool.false_eq_true, ↓reduceIte] at hs_spec ⊢
    change tcut false (if h : S.Nonempty then S.max' h + 1 else 0) t ↔ q < pStar
    by_cases hS : S.Nonempty
    · simp only [hS, ↓reduceDIte, tcut, Bool.false_eq_true, ↓reduceIte]
      constructor
      · intro hlt_max
        have hle_max : t ≤ S.max' hS := by omega
        obtain ⟨_, qStar, ⟨_, hhiS, hxS⟩, hltS⟩ := Finset.mem_filter.mp (Finset.max'_mem S hS)
        simp only [tcut, Bool.false_eq_true, ↓reduceIte] at hltS
        have hstep := hs_spec t (S.max' hS) hlo hle_max hhiS
        omega
      · intro hqp
        have hle := Finset.le_max' S t
          (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr htT, q, hR, hqp⟩)
        omega
    · simp only [hS, ↓reduceDIte, tcut, Bool.false_eq_true, ↓reduceIte]
      constructor
      · intro hlt; omega
      · intro hqp
        exfalso
        exact hS ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr htT, q, hR, hqp⟩⟩

/-! ## §3. Coarse Signature Scans, Guard Budgets, and Path Induction -/

/-- Intra-phase guard at phase `α` and threshold `θ`: `[θ, θ + τ_cut]` together with all bank
straddling-hop guards `intraStradGuard`. -/
noncomputable def phaseIntraGuard {k : ℕ} (xs : Fin k → ℕ → ℤ) (T τ_cut : ℕ)
    (B_bank : Finset (Fin k)) (a : ℕ → ℕ) (α θ : ℕ) : Finset ℕ :=
  Finset.Icc θ (θ + τ_cut) ∪
    B_bank.biUnion fun j => intraStradGuard (xs j) T (a α) (a (α + 1)) θ

theorem card_phaseIntraGuard_le {k : ℕ} {xs : Fin k → ℕ → ℤ} {T τ_cut A : ℕ}
    {B_bank : Finset (Fin k)} {a : ℕ → ℕ} {α : ℕ}
    (hbank : ∀ j ∈ B_bank, CoarseMonoOnInterval (xs j) (a α) (a (α + 1)) A) (θ : ℕ) :
    (phaseIntraGuard xs T τ_cut B_bank a α θ).card ≤ (τ_cut + 1) + k * (2 * A + 1) := by
  have hwin : (Finset.Icc θ (θ + τ_cut)).card = τ_cut + 1 := by
    rw [Nat.card_Icc]; omega
  have hstrad : (B_bank.biUnion fun j => intraStradGuard (xs j) T (a α) (a (α + 1)) θ).card ≤
      k * (2 * A + 1) := by
    calc (B_bank.biUnion fun j => intraStradGuard (xs j) T (a α) (a (α + 1)) θ).card
        ≤ ∑ j ∈ B_bank, (intraStradGuard (xs j) T (a α) (a (α + 1)) θ).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _j ∈ B_bank, (2 * A + 1) :=
          Finset.sum_le_sum fun j hj => card_intraStradGuard_le (hbank j hj)
      _ = B_bank.card * (2 * A + 1) := by simp
      _ ≤ k * (2 * A + 1) := by
          refine Nat.mul_le_mul_right _ ?_
          calc B_bank.card ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_le_univ _
            _ = k := by simp
  calc (phaseIntraGuard xs T τ_cut B_bank a α θ).card
      ≤ (Finset.Icc θ (θ + τ_cut)).card +
          (B_bank.biUnion fun j => intraStradGuard (xs j) T (a α) (a (α + 1)) θ).card :=
        Finset.card_union_le _ _
    _ ≤ (τ_cut + 1) + k * (2 * A + 1) := by rw [hwin]; exact Nat.add_le_add_left hstrad _

/-- Structural scan computing the coarse pulled-back cut `(pos, θ)` for phase `α` scanning `< m`. -/
noncomputable def coarseCutScan {k : ℕ} (x_in : ℕ → ℤ) (xs : Fin k → ℕ → ℤ) (T A : ℕ)
    (B_bank : Finset (Fin k)) (a : ℕ → ℕ) (σ : ℕ → Option B_bank) (pStar : ℕ) :
    ℕ → ℕ → Bool × ℕ
  | 0, α => coarsePullRead x_in T (a α) (a (α + 1)) A pStar
  | β + 1, α =>
    match σ β with
    | some j =>
      let c_tail := coarseCutScan x_in xs T A B_bank a σ pStar β β
      interBankPull (xs j.1) T (a β) (a (β + 1)) (a α) (a (α + 1)) A c_tail
    | none =>
      coarseCutScan x_in xs T A B_bank a σ pStar β α

/-- Coarse pulled-back cut `(pos, θ)` for `(α, σ, pStar)`. -/
noncomputable def coarseCutOf {k : ℕ} (x_in : ℕ → ℤ) (xs : Fin k → ℕ → ℤ) (T A : ℕ)
    (B_bank : Finset (Fin k)) (a : ℕ → ℕ) (α : ℕ) (σ : ℕ → Option B_bank) (pStar : ℕ) :
    Bool × ℕ :=
  coarseCutScan x_in xs T A B_bank a σ pStar α α

/-- Structural scan computing the union of intra-phase and inter-phase guards along phases visited
by `(α, σ, pStar)` when scanning `< m`. -/
noncomputable def coarseGuardsScan {k : ℕ} (x_in : ℕ → ℤ) (xs : Fin k → ℕ → ℤ) (T τ_cut A : ℕ)
    (B_bank : Finset (Fin k)) (a : ℕ → ℕ) (σ : ℕ → Option B_bank) (pStar : ℕ) :
    ℕ → ℕ → Finset ℕ
  | 0, α =>
    let θ := (coarseCutOf x_in xs T A B_bank a α σ pStar).2
    phaseIntraGuard xs T τ_cut B_bank a α θ
  | β + 1, α =>
    match σ β with
    | some j =>
      let θ := (coarseCutOf x_in xs T A B_bank a α σ pStar).2
      let c_tail := coarseCutOf x_in xs T A B_bank a β σ pStar
      (phaseIntraGuard xs T τ_cut B_bank a α θ ∪
        interBankGuard (xs j.1) T (a β) (a (β + 1)) (a α) (a (α + 1)) A c_tail) ∪
        coarseGuardsScan x_in xs T τ_cut A B_bank a σ pStar β β
    | none =>
      coarseGuardsScan x_in xs T τ_cut A B_bank a σ pStar β α

/-- Complete guard set along all phases visited by `(α, σ, pStar)`. -/
noncomputable def coarseGuardsOf {k : ℕ} (x_in : ℕ → ℤ) (xs : Fin k → ℕ → ℤ) (T τ_cut A : ℕ)
    (B_bank : Finset (Fin k)) (a : ℕ → ℕ) (α : ℕ) (σ : ℕ → Option B_bank) (pStar : ℕ) :
    Finset ℕ :=
  coarseGuardsScan x_in xs T τ_cut A B_bank a σ pStar α α

theorem coarseCutScan_congr {k : ℕ} (x_in : ℕ → ℤ) (xs : Fin k → ℕ → ℤ) (T A : ℕ)
    (B_bank : Finset (Fin k)) (a : ℕ → ℕ) (pStar : ℕ) :
    ∀ (m α : ℕ) {σ₁ σ₂ : ℕ → Option B_bank}, (∀ γ < m, σ₁ γ = σ₂ γ) →
      coarseCutScan x_in xs T A B_bank a σ₁ pStar m α =
        coarseCutScan x_in xs T A B_bank a σ₂ pStar m α
  | 0, _, _, _, _ => rfl
  | β + 1, α, _, σ₂, hfg => by
    simp only [coarseCutScan, hfg β (by omega)]
    cases σ₂ β with
    | none => exact coarseCutScan_congr x_in xs T A B_bank a pStar β α fun γ hγ => hfg γ (by omega)
    | some _ =>
      rw [coarseCutScan_congr x_in xs T A B_bank a pStar β β fun γ hγ => hfg γ (by omega)]

theorem coarseCutOf_congr {k : ℕ} (x_in : ℕ → ℤ) (xs : Fin k → ℕ → ℤ) (T A : ℕ)
    (B_bank : Finset (Fin k)) (a : ℕ → ℕ) (α : ℕ) {σ₁ σ₂ : ℕ → Option B_bank}
    (hfg : ∀ β < α, σ₁ β = σ₂ β) (pStar : ℕ) :
    coarseCutOf x_in xs T A B_bank a α σ₁ pStar = coarseCutOf x_in xs T A B_bank a α σ₂ pStar :=
  coarseCutScan_congr x_in xs T A B_bank a pStar α α hfg

theorem coarseGuardsScan_congr {k : ℕ} (x_in : ℕ → ℤ) (xs : Fin k → ℕ → ℤ) (T τ_cut A : ℕ)
    (B_bank : Finset (Fin k)) (a : ℕ → ℕ) (pStar : ℕ) :
    ∀ (m α : ℕ) {σ₁ σ₂ : ℕ → Option B_bank}, m ≤ α → (∀ γ < α, σ₁ γ = σ₂ γ) →
      coarseGuardsScan x_in xs T τ_cut A B_bank a σ₁ pStar m α =
        coarseGuardsScan x_in xs T τ_cut A B_bank a σ₂ pStar m α
  | 0, α, _, _, _, hfg => by
    simp only [coarseGuardsScan, coarseCutOf_congr x_in xs T A B_bank a α hfg pStar]
  | β + 1, α, _, σ₂, hmα, hfg => by
    have hβα : β < α := by omega
    simp only [coarseGuardsScan, hfg β hβα]
    cases σ₂ β with
    | none =>
      exact coarseGuardsScan_congr x_in xs T τ_cut A B_bank a pStar β α (by omega) hfg
    | some _ =>
      rw [coarseCutOf_congr x_in xs T A B_bank a α hfg pStar,
        coarseCutOf_congr x_in xs T A B_bank a β (fun γ hγ => hfg γ (by omega)) pStar,
        coarseGuardsScan_congr x_in xs T τ_cut A B_bank a pStar β β le_rfl
          (fun γ hγ => hfg γ (by omega))]

theorem coarseGuardsOf_congr {k : ℕ} (x_in : ℕ → ℤ) (xs : Fin k → ℕ → ℤ) (T τ_cut A : ℕ)
    (B_bank : Finset (Fin k)) (a : ℕ → ℕ) (α : ℕ) {σ₁ σ₂ : ℕ → Option B_bank}
    (hfg : ∀ β < α, σ₁ β = σ₂ β) (pStar : ℕ) :
    coarseGuardsOf x_in xs T τ_cut A B_bank a α σ₁ pStar =
      coarseGuardsOf x_in xs T τ_cut A B_bank a α σ₂ pStar :=
  coarseGuardsScan_congr x_in xs T τ_cut A B_bank a pStar α α le_rfl hfg

theorem card_coarseGuardsScan_le {k : ℕ} (x_in : ℕ → ℤ) (xs : Fin k → ℕ → ℤ)
    (T τ_cut A M_ph : ℕ) (B_bank : Finset (Fin k)) {a : ℕ → ℕ}
    (ha : ∀ α < M_ph, a α ≤ a (α + 1))
    (hbank : ∀ α < M_ph, ∀ j ∈ B_bank, CoarseMonoOnInterval (xs j) (a α) (a (α + 1)) A)
    (σ : ℕ → Option B_bank) (pStar : ℕ) :
    ∀ (m α : ℕ), m ≤ α → α < M_ph →
      (coarseGuardsScan x_in xs T τ_cut A B_bank a σ pStar m α).card ≤
        (m + 1) * ((2 * k + 3) * (τ_cut + A + 1))
  | 0, α, _, hαM => by
    simp only [coarseGuardsScan, zero_add, one_mul]
    have h1 := card_phaseIntraGuard_le (T := T) (τ_cut := τ_cut) (hbank α hαM)
      (coarseCutOf x_in xs T A B_bank a α σ pStar).2
    nlinarith
  | β + 1, α, hmα, hαM => by
    have hβα : β < α := by omega
    have hβM : β < M_ph := hβα.trans hαM
    simp only [coarseGuardsScan]
    cases σ β with
    | none =>
      exact (card_coarseGuardsScan_le x_in xs T τ_cut A M_ph B_bank ha hbank σ pStar β α
        (by omega) hαM).trans (Nat.mul_le_mul_right _ (by omega))
    | some j =>
      have ih := card_coarseGuardsScan_le x_in xs T τ_cut A M_ph B_bank ha hbank σ pStar β β
        le_rfl hβM
      have h1 := card_phaseIntraGuard_le (T := T) (τ_cut := τ_cut) (hbank α hαM)
        (coarseCutOf x_in xs T A B_bank a α σ pStar).2
      have hsep : a (β + 1) ≤ a α := phase_le_of_step ha (by omega) (by omega)
      have h2 := card_interBankGuard_le (T := T) hsep (hbank β hβM j.1 j.2) (hbank α hαM j.1 j.2)
        (coarseCutOf x_in xs T A B_bank a β σ pStar)
      have hlocal : (phaseIntraGuard xs T τ_cut B_bank a α
            (coarseCutOf x_in xs T A B_bank a α σ pStar).2 ∪
          interBankGuard (xs j.1) T (a β) (a (β + 1)) (a α) (a (α + 1)) A
            (coarseCutOf x_in xs T A B_bank a β σ pStar)).card ≤
          (2 * k + 3) * (τ_cut + A + 1) := by
        have hu := Finset.card_union_le
          (phaseIntraGuard xs T τ_cut B_bank a α (coarseCutOf x_in xs T A B_bank a α σ pStar).2)
          (interBankGuard (xs j.1) T (a β) (a (β + 1)) (a α) (a (α + 1)) A
            (coarseCutOf x_in xs T A B_bank a β σ pStar))
        nlinarith
      calc ((phaseIntraGuard _ _ _ _ _ _ _ ∪ interBankGuard _ _ _ _ _ _ _ _) ∪
              coarseGuardsScan x_in xs T τ_cut A B_bank a σ pStar β β).card
          ≤ (phaseIntraGuard _ _ _ _ _ _ _ ∪ interBankGuard _ _ _ _ _ _ _ _).card +
              (coarseGuardsScan x_in xs T τ_cut A B_bank a σ pStar β β).card :=
            Finset.card_union_le _ _
        _ ≤ (2 * k + 3) * (τ_cut + A + 1) + (β + 1) * ((2 * k + 3) * (τ_cut + A + 1)) :=
            Nat.add_le_add hlocal ih
        _ = (β + 1 + 1) * ((2 * k + 3) * (τ_cut + A + 1)) := by ring

theorem card_coarseGuardsOf_le {k : ℕ} (x_in : ℕ → ℤ) (xs : Fin k → ℕ → ℤ)
    (T τ_cut A M_ph : ℕ) (B_bank : Finset (Fin k)) {a : ℕ → ℕ}
    (ha : ∀ α < M_ph, a α ≤ a (α + 1))
    (hbank : ∀ α < M_ph, ∀ j ∈ B_bank, CoarseMonoOnInterval (xs j) (a α) (a (α + 1)) A)
    {α : ℕ} (hαM : α < M_ph) (σ : ℕ → Option B_bank) (pStar : ℕ) :
    (coarseGuardsOf x_in xs T τ_cut A B_bank a α σ pStar).card ≤
      (α + 1) * ((2 * k + 3) * (τ_cut + A + 1)) :=
  card_coarseGuardsScan_le x_in xs T τ_cut A M_ph B_bank ha hbank σ pStar α α le_rfl hαM

theorem coarseCutScan_eq_of_none {k : ℕ} (x_in : ℕ → ℤ) (xs : Fin k → ℕ → ℤ) (T A : ℕ)
    (B_bank : Finset (Fin k)) (a : ℕ → ℕ) (σ : ℕ → Option B_bank) (pStar : ℕ) :
    ∀ (m α : ℕ), (∀ γ < m, σ γ = none) →
      coarseCutScan x_in xs T A B_bank a σ pStar m α =
        coarsePullRead x_in T (a α) (a (α + 1)) A pStar
  | 0, _, _ => rfl
  | β + 1, α, hnone => by
    simp only [coarseCutScan, hnone β (by omega)]
    exact coarseCutScan_eq_of_none x_in xs T A B_bank a σ pStar β α fun γ hγ => hnone γ (by omega)

theorem coarseCutOf_none {k : ℕ} (x_in : ℕ → ℤ) (xs : Fin k → ℕ → ℤ) (T A : ℕ)
    (B_bank : Finset (Fin k)) (a : ℕ → ℕ) (α pStar : ℕ) :
    coarseCutOf x_in xs T A B_bank a α (liftSig (fun _ : Fin α => (none : Option B_bank))) pStar =
      coarsePullRead x_in T (a α) (a (α + 1)) A pStar :=
  coarseCutScan_eq_of_none x_in xs T A B_bank a _ pStar α α fun γ hγ => by simp [liftSig, hγ]

theorem mem_coarseGuardsScan_self {k : ℕ} (x_in : ℕ → ℤ) (xs : Fin k → ℕ → ℤ) (T τ_cut A : ℕ)
    (B_bank : Finset (Fin k)) (a : ℕ → ℕ) (σ : ℕ → Option B_bank) (pStar : ℕ) :
    ∀ (m α : ℕ),
      phaseIntraGuard xs T τ_cut B_bank a α (coarseCutOf x_in xs T A B_bank a α σ pStar).2 ⊆
        coarseGuardsScan x_in xs T τ_cut A B_bank a σ pStar m α
  | 0, _ => Subset.rfl
  | β + 1, α => by
    simp only [coarseGuardsScan]
    cases σ β with
    | none => exact mem_coarseGuardsScan_self x_in xs T τ_cut A B_bank a σ pStar β α
    | some _ => exact Finset.subset_union_left.trans Finset.subset_union_left

theorem mem_coarseGuardsOf_self {k : ℕ} (x_in : ℕ → ℤ) (xs : Fin k → ℕ → ℤ) (T τ_cut A : ℕ)
    (B_bank : Finset (Fin k)) (a : ℕ → ℕ) (α : ℕ) (σ : ℕ → Option B_bank) (pStar : ℕ) :
    phaseIntraGuard xs T τ_cut B_bank a α (coarseCutOf x_in xs T A B_bank a α σ pStar).2 ⊆
      coarseGuardsOf x_in xs T τ_cut A B_bank a α σ pStar :=
  mem_coarseGuardsScan_self x_in xs T τ_cut A B_bank a σ pStar α α

theorem coarseCutScan_eq_of_top {k : ℕ} (x_in : ℕ → ℤ) (xs : Fin k → ℕ → ℤ) (T A : ℕ)
    (B_bank : Finset (Fin k)) (a : ℕ → ℕ) (σ : ℕ → Option B_bank) (pStar α' : ℕ) (j : B_bank) :
    ∀ (m α : ℕ), α' < m → σ α' = some j → (∀ γ, α' < γ → γ < m → σ γ = none) →
      coarseCutScan x_in xs T A B_bank a σ pStar m α =
        interBankPull (xs j.1) T (a α') (a (α' + 1)) (a α) (a (α + 1)) A
          (coarseCutOf x_in xs T A B_bank a α' σ pStar)
  | 0, _, hlt, _, _ => by omega
  | β + 1, α, hlt, htop, hnone => by
    rcases eq_or_lt_of_le (Nat.le_of_lt_succ hlt) with rfl | hlt'
    · simp only [coarseCutScan, htop, coarseCutOf]
    · simp only [coarseCutScan, hnone β hlt' (by omega)]
      exact coarseCutScan_eq_of_top x_in xs T A B_bank a σ pStar α' j β α hlt' htop
        fun γ h1 h2 => hnone γ h1 (by omega)

theorem coarseGuardsScan_sub_of_top {k : ℕ} (x_in : ℕ → ℤ) (xs : Fin k → ℕ → ℤ) (T τ_cut A : ℕ)
    (B_bank : Finset (Fin k)) (a : ℕ → ℕ) (σ : ℕ → Option B_bank) (pStar α' : ℕ) (j : B_bank) :
    ∀ (m α : ℕ), α' < m → σ α' = some j → (∀ γ, α' < γ → γ < m → σ γ = none) →
      interBankGuard (xs j.1) T (a α') (a (α' + 1)) (a α) (a (α + 1)) A
          (coarseCutOf x_in xs T A B_bank a α' σ pStar) ⊆
        coarseGuardsScan x_in xs T τ_cut A B_bank a σ pStar m α ∧
      coarseGuardsOf x_in xs T τ_cut A B_bank a α' σ pStar ⊆
        coarseGuardsScan x_in xs T τ_cut A B_bank a σ pStar m α
  | 0, _, hlt, _, _ => by omega
  | β + 1, α, hlt, htop, hnone => by
    rcases eq_or_lt_of_le (Nat.le_of_lt_succ hlt) with rfl | hlt'
    · simp only [coarseGuardsScan, htop, coarseGuardsOf]
      exact ⟨Finset.subset_union_right.trans Finset.subset_union_left, Finset.subset_union_right⟩
    · simp only [coarseGuardsScan, hnone β hlt' (by omega)]
      exact coarseGuardsScan_sub_of_top x_in xs T τ_cut A B_bank a σ pStar α' j β α hlt' htop
        fun γ h1 h2 => hnone γ h1 (by omega)

theorem coarseCutOf_consSig {k α' α : ℕ} (x_in : ℕ → ℤ) (xs : Fin k → ℕ → ℤ) (T τ_cut A : ℕ)
    (B_bank : Finset (Fin k)) (a : ℕ → ℕ) (hlt : α' < α) (j : B_bank) (σ' : SigAt B_bank α')
    (pStar : ℕ) :
    coarseCutOf x_in xs T A B_bank a α (liftSig (consSig hlt j σ')) pStar =
      interBankPull (xs j.1) T (a α') (a (α' + 1)) (a α) (a (α + 1)) A
        (coarseCutOf x_in xs T A B_bank a α' (liftSig σ') pStar) ∧
    interBankGuard (xs j.1) T (a α') (a (α' + 1)) (a α) (a (α + 1)) A
        (coarseCutOf x_in xs T A B_bank a α' (liftSig σ') pStar) ⊆
      coarseGuardsOf x_in xs T τ_cut A B_bank a α (liftSig (consSig hlt j σ')) pStar ∧
    coarseGuardsOf x_in xs T τ_cut A B_bank a α' (liftSig σ') pStar ⊆
      coarseGuardsOf x_in xs T τ_cut A B_bank a α (liftSig (consSig hlt j σ')) pStar := by
  let σ := liftSig (consSig hlt j σ')
  have htop : σ α' = some j := by simp [σ, liftSig, consSig, hlt]
  have hnone : ∀ β, α' < β → β < α → σ β = none := by
    intro β h1 h2
    simp [σ, liftSig, consSig, h2, show ¬ β < α' by omega, show β ≠ α' by omega]
  have hagree : ∀ β < α', σ β = liftSig σ' β := by
    intro β hβ
    have hβα : β < α := hβ.trans hlt
    simp [σ, liftSig, consSig, hβα, hβ]
  have hcut_eq := coarseCutOf_congr x_in xs T A B_bank a α' hagree pStar
  have hgrd_eq := coarseGuardsOf_congr x_in xs T τ_cut A B_bank a α' hagree pStar
  obtain ⟨hinter_sub, htail_sub⟩ :=
    coarseGuardsScan_sub_of_top x_in xs T τ_cut A B_bank a σ pStar α' j α α hlt htop hnone
  refine ⟨?_, ?_, ?_⟩
  · rw [coarseCutOf, coarseCutScan_eq_of_top x_in xs T A B_bank a σ pStar α' j α α hlt htop hnone,
      hcut_eq]
  · rw [← hcut_eq]; exact hinter_sub
  · rw [← hgrd_eq]; exact htail_sub

/-! ## §4. Single-Trace Jitter-Tolerant BM Independent Set & Storage-Code Deficit -/

/-- At scale `w = 1`, if `z (some none)` is non-decreasing and `hot` witnesses output positions for
every transposition demand, then `ot` is strictly monotone on `[0, d² b)` and maps into `[0, T)`. -/
theorem ot_strictMonoOn_of_coneRel1 {k d b T : ℕ} {z : Tp k → ℕ → ℤ}
    (hout_mono : ∀ t₁ t₂, t₁ ≤ t₂ → z (some none) t₁ ≤ z (some none) t₂)
    {ot : ℕ → ℕ}
    (hot : ∀ q : Fin (d * d * b),
      ot (MergeDepth.tpos d b q) < T ∧
        (MergeDepth.tpos d b q : ℤ) / (1 : ℕ) = z (some none) (ot (MergeDepth.tpos d b q)) / (1 : ℕ)) :
    (∀ r < d * d * b, ot r < T) ∧
      (∀ r₁ r₂, r₁ < r₂ → r₂ < d * d * b → ot r₁ < ot r₂) := by
  have hpoint : ∀ r (hr : r < d * d * b), ot r < T ∧ z (some none) (ot r) = (r : ℤ) := by
    intro r hr
    let q_r : Fin (d * d * b) := tposOf d b ⟨r, hr⟩
    have htpos_eq : MergeDepth.tpos d b q_r = r := by
      rw [← tape_tpos_eq, ← tposOf_val]
      exact congrArg Fin.val (tposOf_tposOf d b ⟨r, hr⟩)
    obtain ⟨h1, h2⟩ := hot q_r
    rw [htpos_eq] at h1 h2
    simp only [Nat.cast_one, Int.ediv_one] at h2
    exact ⟨h1, h2.symm⟩
  refine ⟨fun r hr => (hpoint r hr).1, fun r₁ r₂ hlt hr₂ => ?_⟩
  have h1 := (hpoint r₁ (hlt.trans hr₂)).2
  have h2 := (hpoint r₂ hr₂).2
  by_contra hge
  have hle := hout_mono (ot r₂) (ot r₁) (by omega)
  omega

/-- Any independent set `S_ind` in `N` bounds the binary log-cardinality of every storage code `C`
on `N` by `L - S_ind.card` (holding even when `C = ∅`, since `Real.logb 2 0 = 0`). -/
theorem storageCode_log_le_of_independent {L : ℕ} {N : Fin L → Finset (Fin L)}
    {S_ind : Finset (Fin L)} (hInd : DirectedRecovery.IsIndependent N S_ind)
    {C : Finset (Fin L → Bool)} (hC : IsStorageCode N C) :
    Real.logb 2 C.card ≤ (L : ℝ) - (S_ind.card : ℝ) := by
  have hle : S_ind.card ≤ L := by
    simpa using S_ind.card_le_univ
  by_cases hC0 : C.card = 0
  · rw [hC0, Nat.cast_zero, Real.logb_zero]
    have : (S_ind.card : ℝ) ≤ (L : ℝ) := by exact_mod_cast hle
    linarith
  · have hCpos : (0 : ℝ) < (C.card : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hC0
    have hcard := DirectedRecovery.storageCode_card_le_of_independent hInd hC
    rw [Fintype.card_bool, Fintype.card_fin] at hcard
    have hcard_r : (C.card : ℝ) ≤ (2 : ℝ) ^ ((L : ℝ) - (S_ind.card : ℝ)) := by
      rw [← Nat.cast_sub hle, Real.rpow_natCast]
      exact_mod_cast hcard
    exact (Real.logb_le_iff_le_rpow (by norm_num) hCpos).mpr hcard_r

/-- Sub-row jitter `A(d) = o(d * entryBits d)` implies `A(d) = o(d² * entryBits d)`. -/
theorem tendsto_div_L_of_tendsto_div_db {A : ℕ → ℕ}
    (hA : Tendsto (fun d : ℕ => (A d : ℝ) / ((d * entryBits d : ℕ) : ℝ)) atTop (nhds 0)) :
    Tendsto (fun d : ℕ => (A d : ℝ) / ((d * d * entryBits d : ℕ) : ℝ)) atTop (nhds 0) := by
  refine squeeze_zero_norm' ?_ hA
  filter_upwards [eventually_ge_atTop 1] with d hd
  rw [Real.norm_of_nonneg (by positivity)]
  have hle_nat : d * entryBits d ≤ d * d * entryBits d := by
    calc d * entryBits d = 1 * (d * entryBits d) := by ring
      _ ≤ d * (d * entryBits d) := Nat.mul_le_mul_right _ hd
      _ = d * d * entryBits d := by ring
  have hpos : (0 : ℝ) < ((d * entryBits d : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos hd (one_le_entryBits d)
  exact div_le_div_of_nonneg_left (by positivity) hpos (by exact_mod_cast hle_nat)

/-! ## §5. Simulator Head-Motion Preservation -/

/-- At every completed batch boundary `j ≤ T_M / s` of `Native.machine M hs`, all input and work
head positions of `Native.machine M hs` at physical step `(10 * s + 1) * j` lie within `s` cells of
the corresponding head positions of `M` at step `j * s`. -/
theorem native_boundary_head_dist (M : TM) {s : ℕ} (hs : 0 < s) (w : List Bool) {T_M : ℕ}
    (H : Transpose.Tape.HaltsAt M w T_M) {j : ℕ} (hj : j ≤ T_M / s) :
    |runWalks (Native.machine M hs) w none ((10 * s + 1) * j) -
        runWalks M w none (j * s)| ≤ (s : ℤ) ∧
      ∀ h : Fin M.k,
        |runWalks (Native.machine M hs) w (some (some h)) ((10 * s + 1) * j) -
            runWalks M w (some (some h)) (j * s)| ≤ (s : ℤ) := by
  have hjs_le : j * s ≤ T_M :=
    (Nat.mul_le_mul_right s hj).trans (Nat.div_mul_le_self T_M s)
  have Htr := (haltsAt_iff_trace T_M).mp H
  have halive : ∀ i < j * s, transAt M w i ≠ none :=
    fun i hi h => Htr.1 i (hi.trans_le hjs_le) ((Native.traceFrom_none_iff M w none i).mpr h)
  obtain ⟨r, ai, aw, out, hrun, _, hin, hwk, _⟩ := Native.full_blocks M hs w j halive
  change run (Native.machine M hs) w ((10 * s + 1) * j) = _ at hrun
  have hin_N : (run (Native.machine M hs) w ((10 * s + 1) * j)).inPos = ai := by
    rw [hrun]
    simp [Native.Frame.native, Native.anchored]
  have hwk_N : ∀ h : Fin M.k,
      (run (Native.machine M hs) w ((10 * s + 1) * j)).workPos h = aw h := by
    intro h
    rw [hrun]
    simp [Native.Frame.native, Native.anchored]
  refine ⟨?_, fun h => ?_⟩
  · simp only [runWalks, hin_N, hin]
    have hoi := r.oi.isLt
    rw [abs_le]
    constructor <;> omega
  · simp only [runWalks]
    have hwN := hwk_N h
    have hwM := hwk h
    rw [hwN, hwM]
    have how := (r.ow h).isLt
    rw [abs_le]
    constructor <;> omega

/-- **Simulator preservation of jittered macro-phases (Theorem 9.4 / Theorem J):**
if `M` halts on `w` at time `T_M` with `TraceHasJitterBM (runWalks M w) T_M M_ph B_bank A_val S_val`
(`1 ≤ M_ph`), then `N := Native.machine M hs` (`hs : 0 < s`) halts on `w` at
`U := (10 * s + 1) * (T_M / s + 1) + s` and satisfies `TraceHasJitterBM` with jitter amplitude
`A_val + 24 * s + 2` and workspace cell bound `(24 * s + 3) * (S_val + 1)`. -/
theorem native_machine_preserves_jitterBM (M : TM) {s : ℕ} (hs : 0 < s) (w : List Bool)
    {T_M M_ph A_val S_val : ℕ} (hMph : 1 ≤ M_ph) {B_bank : Finset (Fin M.k)}
    (H : Transpose.Tape.HaltsAt M w T_M)
    (hBM : TraceHasJitterBM (runWalks M w) T_M M_ph B_bank A_val S_val) :
    let U := (10 * s + 1) * (T_M / s + 1) + s
    Transpose.Tape.HaltsAt (Native.machine M hs) w U ∧
      TraceHasJitterBM (runWalks (Native.machine M hs) w) U M_ph B_bank
        (A_val + 24 * s + 2) ((24 * s + 3) * (S_val + 1)) := by
  dsimp only
  classical
  set U := (10 * s + 1) * (T_M / s + 1) + s
  have hHaltN : Transpose.Tape.HaltsAt (Native.machine M hs) w U :=
    (Native.simulates_halt M hs w H).1
  refine ⟨hHaltN, ?_⟩
  rcases Nat.eq_zero_or_pos T_M with rfl | hTM_pos
  · -- Degenerate instant-halt case `T_M = 0`: `U = 11 * s + 1`.
    have hU_eq : U = 11 * s + 1 := by dsimp [U]; simp; omega
    let b : ℕ → ℕ := fun α => if α = 0 then 0 else U
    have hb0 : b 0 = 0 := rfl
    have hbM : b M_ph = U := by simp only [b, show M_ph ≠ 0 by omega, ↓reduceIte]
    have hble : ∀ α < M_ph, b α ≤ b (α + 1) := by
      intro α _
      simp only [b, Nat.add_one_ne_zero, ↓reduceIte]
      split_ifs <;> omega
    have hwalk_bound : ∀ (c : Tp (Native.machine M hs).k) (u : ℕ), u < U →
        |runWalks (Native.machine M hs) w c u - runWalks (Native.machine M hs) w c 0| ≤
          (11 * s : ℤ) := by
      intro c u hu
      have hlip := walk_lip (runWalks_isWalk (Native.machine M hs) w c) 0 u
      rw [Nat.zero_add] at hlip
      have hu_le : (u : ℤ) ≤ (11 * s : ℤ) := by omega
      exact hlip.trans hu_le
    refine ⟨⟨b, hb0, hbM, hble, fun α _ => ?_, fun α _ j _ => ?_⟩, fun wh _ => ?_⟩
    · left
      intro t t' _ _ ht'
      have hb_le : b (α + 1) ≤ U := by simp [b]
      have htU : t < U := by omega
      have ht'U : t' < U := by omega
      have h1 := abs_le.mp (hwalk_bound none t htU)
      have h2 := abs_le.mp (hwalk_bound none t' ht'U)
      omega
    · left
      intro t t' _ _ ht'
      have hb_le : b (α + 1) ≤ U := by simp [b]
      have htU : t < U := by omega
      have ht'U : t' < U := by omega
      have h1 := abs_le.mp (hwalk_bound (some (some j)) t htU)
      have h2 := abs_le.mp (hwalk_bound (some (some j)) t' ht'U)
      omega
    · let z0 := runWalks (Native.machine M hs) w (some (some wh)) 0
      let box : Finset ℤ :=
        (Finset.range (22 * s + 1)).image fun i : ℕ => z0 - (11 * s : ℤ) + (i : ℤ)
      have hsub : (Finset.range U).image (runWalks (Native.machine M hs) w (some (some wh))) ⊆
          box := by
        intro y hy
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hy
        have h1 := abs_le.mp (hwalk_bound (some (some wh)) u (Finset.mem_range.mp hu))
        refine Finset.mem_image.mpr
          ⟨(runWalks (Native.machine M hs) w (some (some wh)) u - (z0 - (11 * s : ℤ))).toNat,
            Finset.mem_range.mpr (by omega), ?_⟩
        omega
      calc ((Finset.range U).image (runWalks (Native.machine M hs) w (some (some wh)))).card
          ≤ box.card := Finset.card_le_card hsub
        _ ≤ 22 * s + 1 := Finset.card_image_le.trans (by simp)
        _ ≤ (24 * s + 3) * (S_val + 1) := by nlinarith
  · -- Main case `1 ≤ T_M`: construct monotone clock projection `π_M : ℕ → ℕ`.
    obtain ⟨⟨a, ha0, haM, ha, hin, hbank⟩, hwork⟩ := hBM
    let j₀ : ℕ → ℕ := fun u => min (T_M / s) (u / (10 * s + 1))
    let π_M : ℕ → ℕ := fun u => min (T_M - 1) (j₀ u * s)
    have hπ_mono : ∀ {u₁ u₂ : ℕ}, u₁ ≤ u₂ → π_M u₁ ≤ π_M u₂ := by
      intro u₁ u₂ hle
      have hj : j₀ u₁ ≤ j₀ u₂ := min_le_min le_rfl (Nat.div_le_div_right hle)
      exact min_le_min le_rfl (Nat.mul_le_mul_right s hj)
    have hπ_lt : ∀ u : ℕ, π_M u < T_M := fun u =>
      (min_le_left _ _).trans_lt (by omega)
    -- Prove uniform tracking bound `≤ 12 * s + 1` for `u < U`.
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
      have hjs_le_TM : j₀ u * s ≤ T_M :=
        (Nat.mul_le_mul_right s hj_le).trans (Nat.div_mul_le_self T_M s)
      have hπ_lo : π_M u ≤ j₀ u * s := min_le_right _ _
      have hπ_hi : j₀ u * s ≤ π_M u + 1 := by
        dsimp [π_M]
        omega
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
    -- Pull back phase boundaries `a` along monotone `π_M`.
    let F_set : ℕ → Finset ℕ := fun α => (Finset.range U).filter fun u => a α ≤ π_M u
    let b : ℕ → ℕ := fun α =>
      if α = 0 then 0
      else if M_ph ≤ α then U
      else if h : (F_set α).Nonempty then (F_set α).min' h else U
    have hb0 : b 0 = 0 := rfl
    have hbM : b M_ph = U := by
      simp only [b, show M_ph ≠ 0 by omega, le_rfl, ↓reduceIte]
    have hb_le_U : ∀ α : ℕ, b α ≤ U := by
      intro α
      dsimp [b]
      split_ifs with h1 h2 h3
      · omega
      · exact le_rfl
      · exact (Finset.mem_range.mp (Finset.mem_filter.mp (Finset.min'_mem _ h3)).1).le
      · exact le_rfl
    have hble : ∀ α < M_ph, b α ≤ b (α + 1) := by
      intro α hα
      rcases Nat.eq_zero_or_pos α with rfl | hα_pos
      · simp [hb0]
      · by_cases htop : α + 1 = M_ph
        · rw [htop, hbM]; exact hb_le_U α
        · have hα1_lt : α + 1 < M_ph := by omega
          have hsubF : F_set (α + 1) ⊆ F_set α := by
            intro u hu
            obtain ⟨huU, hle⟩ := Finset.mem_filter.mp hu
            exact Finset.mem_filter.mpr ⟨huU, (ha α hα).trans hle⟩
          have hb_α : b α = if h : (F_set α).Nonempty then (F_set α).min' h else U := by
            simp only [b, show α ≠ 0 by omega, show ¬ M_ph ≤ α by omega, ↓reduceIte]
          have hb_α1 : b (α + 1) =
              if h : (F_set (α + 1)).Nonempty then (F_set (α + 1)).min' h else U := by
            simp only [b, Nat.add_one_ne_zero, show ¬ M_ph ≤ α + 1 by omega, ↓reduceIte]
          by_cases hne2 : (F_set (α + 1)).Nonempty
          · have hne1 : (F_set α).Nonempty := hne2.mono hsubF
            rw [hb_α, hb_α1]
            simp only [hne1, hne2, ↓reduceDIte]
            exact Finset.min'_le _ _ (hsubF (Finset.min'_mem _ hne2))
          · rw [hb_α1]
            simp only [hne2, ↓reduceDIte]
            exact hb_le_U α
    have hb_interval : ∀ α < M_ph, ∀ u : ℕ, b α ≤ u → u < b (α + 1) →
        u < U ∧ a α ≤ π_M u ∧ π_M u < a (α + 1) := by
      intro α hα u hbu hub1
      have huU : u < U := hub1.trans_le (hb_le_U (α + 1))
      refine ⟨huU, ?_, ?_⟩
      · rcases Nat.eq_zero_or_pos α with rfl | hα_pos
        · rw [ha0]; exact Nat.zero_le _
        · have hb_α : b α = if h : (F_set α).Nonempty then (F_set α).min' h else U := by
            simp only [b, show α ≠ 0 by omega, show ¬ M_ph ≤ α by omega, ↓reduceIte]
          rw [hb_α] at hbu
          by_cases hne : (F_set α).Nonempty
          · simp only [hne, ↓reduceDIte] at hbu
            have hmin := (Finset.mem_filter.mp (Finset.min'_mem _ hne)).2
            exact hmin.trans (hπ_mono hbu)
          · simp only [hne, ↓reduceDIte] at hbu
            omega
      · by_cases htop : α + 1 = M_ph
        · rw [htop, haM]; exact hπ_lt u
        · have hb_α1 : b (α + 1) =
              if h : (F_set (α + 1)).Nonempty then (F_set (α + 1)).min' h else U := by
            simp only [b, Nat.add_one_ne_zero, show ¬ M_ph ≤ α + 1 by omega, ↓reduceIte]
          rw [hb_α1] at hub1
          by_contra hge
          have hu_mem : u ∈ F_set (α + 1) :=
            Finset.mem_filter.mpr ⟨Finset.mem_range.mpr huU, by omega⟩
          have hne : (F_set (α + 1)).Nonempty := ⟨u, hu_mem⟩
          simp only [hne, ↓reduceDIte] at hub1
          have hle := Finset.min'_le _ _ hu_mem
          omega
    refine ⟨⟨b, hb0, hbM, hble, fun α hα => ?_, fun α hα j hj => ?_⟩, fun wh hwh => ?_⟩
    · rcases hin α hα with hinc | hdec
      · left
        intro t t' hbt htt' ht'b
        obtain ⟨htU, hπt_lo, _⟩ := hb_interval α hα t hbt (htt'.trans_lt ht'b)
        obtain ⟨ht'U, _, hπt'_hi⟩ := hb_interval α hα t' (hbt.trans htt') ht'b
        have hM := hinc (π_M t) (π_M t') hπt_lo (hπ_mono htt') hπt'_hi
        have hd1 := abs_le.mp (htrack t htU).1
        have hd2 := abs_le.mp (htrack t' ht'U).1
        omega
      · right
        intro t t' hbt htt' ht'b
        obtain ⟨htU, hπt_lo, _⟩ := hb_interval α hα t hbt (htt'.trans_lt ht'b)
        obtain ⟨ht'U, _, hπt'_hi⟩ := hb_interval α hα t' (hbt.trans htt') ht'b
        have hM := hdec (π_M t) (π_M t') hπt_lo (hπ_mono htt') hπt'_hi
        have hd1 := abs_le.mp (htrack t htU).1
        have hd2 := abs_le.mp (htrack t' ht'U).1
        omega
    · rcases hbank α hα j hj with hinc | hdec
      · left
        intro t t' hbt htt' ht'b
        obtain ⟨htU, hπt_lo, _⟩ := hb_interval α hα t hbt (htt'.trans_lt ht'b)
        obtain ⟨ht'U, _, hπt'_hi⟩ := hb_interval α hα t' (hbt.trans htt') ht'b
        have hM := hinc (π_M t) (π_M t') hπt_lo (hπ_mono htt') hπt'_hi
        have hd1 := abs_le.mp ((htrack t htU).2 j)
        have hd2 := abs_le.mp ((htrack t' ht'U).2 j)
        omega
      · right
        intro t t' hbt htt' ht'b
        obtain ⟨htU, hπt_lo, _⟩ := hb_interval α hα t hbt (htt'.trans_lt ht'b)
        obtain ⟨ht'U, _, hπt'_hi⟩ := hb_interval α hα t' (hbt.trans htt') ht'b
        have hM := hdec (π_M t) (π_M t') hπt_lo (hπ_mono htt') hπt'_hi
        have hd1 := abs_le.mp ((htrack t htU).2 j)
        have hd2 := abs_le.mp ((htrack t' ht'U).2 j)
        omega
    · -- Bound visited workspace cells of `N` by `(24 * s + 3) * (S_val + 1)`.
      let C_M := (Finset.range T_M).image (runWalks M w (some (some wh)))
      have hCM : C_M.card ≤ S_val := hwork wh hwh
      let winOf : ℤ → Finset ℤ := fun y =>
        (Finset.range (24 * s + 3)).image fun i : ℕ => y - (12 * s + 1 : ℤ) + (i : ℤ)
      have hsub : (Finset.range U).image (runWalks (Native.machine M hs) w (some (some wh))) ⊆
          C_M.biUnion winOf := by
        intro z hz
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
        have huU : u < U := Finset.mem_range.mp hu
        have hy_mem : runWalks M w (some (some wh)) (π_M u) ∈ C_M :=
          Finset.mem_image_of_mem _ (Finset.mem_range.mpr (hπ_lt u))
        have hd := abs_le.mp ((htrack u huU).2 wh)
        refine Finset.mem_biUnion.mpr ⟨runWalks M w (some (some wh)) (π_M u), hy_mem, ?_⟩
        refine Finset.mem_image.mpr
          ⟨(runWalks (Native.machine M hs) w (some (some wh)) u -
              (runWalks M w (some (some wh)) (π_M u) - (12 * s + 1 : ℤ))).toNat,
            Finset.mem_range.mpr (by omega), ?_⟩
        omega
      calc ((Finset.range U).image (runWalks (Native.machine M hs) w (some (some wh)))).card
          ≤ (C_M.biUnion winOf).card := Finset.card_le_card hsub
        _ ≤ ∑ y ∈ C_M, (winOf y).card := Finset.card_biUnion_le
        _ ≤ ∑ _y ∈ C_M, (24 * s + 3) :=
            Finset.sum_le_sum fun _ _ => Finset.card_image_le.trans (by simp)
        _ = C_M.card * (24 * s + 3) := by simp
        _ ≤ S_val * (24 * s + 3) := Nat.mul_le_mul_right _ hCM
        _ ≤ (24 * s + 3) * (S_val + 1) := by nlinarith

/-! ## §6. Class-Restricted Native Criterion Excluding Adaptive Linear-Time Transposers -/

/-- Output-count walk `runWalks N x (some none)` is monotone in time. -/
theorem runWalks_out_mono (N : TM) (x : List Bool) {t₁ t₂ : ℕ} (hle : t₁ ≤ t₂) :
    runWalks N x (some none) t₁ ≤ runWalks N x (some none) t₂ := by
  simp only [runWalks]
  exact_mod_cast Transpose.Tape.Impl.outRev_length_mono (M := N) (w := x) hle

end NativeRelations
