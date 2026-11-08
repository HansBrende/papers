import TapeStorageRates.TraceTransfer
import BoundedStackDepth.Machines
import BoundedStackDepth.LowAdaptivity

/-!
# Native Storage-Code Rate Gaps and Low-Adaptivity Exclusion

Formalizes the native storage-code gap predicate `NativeGapBound` on single-run cone relations,
relates it to the fourteenth paper's half-rate bound (`nativeGapBound_half_iff`), and proves
Theorem G (`native_gap_tests_exclude_linear`, `native_gap_exists_exclude_linear`) and Corollary 9.6
(`fSecond_native_gap`, `native_gap_exclusion_of_trace_support`).
-/

namespace NativeRelations

open Filter Finset Transpose BoundedNesting MergeDepth MotionDepthCodes BoundedStackDepth
  TapeStorageRates

set_option autoImplicit false

/-- The aligned batch simulator preserves the work-tape count of the source machine for every
batch size `s`. -/
theorem native_machine_k (M : TM) {s : ℕ} (hs : 0 < s) :
    (Native.machine M hs).k = M.k :=
  rfl

open Classical in
/-- **The native gap bound for the frozen traces of `M`** with deficit `ρ`, at scale `w`, depth `D`,
runtime constant `c`, and widths `b` satisfying `B d b`: identical to
`BoundedStackDepth.NativeBound B M w D c` with `(1 - ρ + δ)` in place of `(1 / 2 + δ)`. -/
def NativeGapBound (ρ : ℝ) (B : ℕ → ℕ → Prop) (M : TM) (w D : ℕ) (c : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ b, B d b →
    ∀ (X : Fin (d * d * b) → Bool) (T : ℕ), Transpose.Tape.HaltsAt M (List.ofFn X) T →
    (T : ℝ) ≤ c * ((d * d * b : ℕ) + 1) → ∀ Γ : Finset ℕ,
    (∀ π, IsDepPath (fun j => skel w (runWalks M (List.ofFn X) (some (some j)))) T π →
      LinNet.GFree Γ π → π.length ≤ D + 1) →
    ∀ ot : ℕ → ℕ, (∀ q : Fin (d * d * b), ot (tpos d b q) < T ∧
      (tpos d b q : ℤ) / w = runWalks M (List.ofFn X) (some none) (ot (tpos d b q)) / w) →
    ∀ C : Finset (Fin (d * d * b) → Bool),
      IsStorageCode (coneRel w (runWalks M (List.ofFn X)) T Γ ot fun q => tpos d b q) C →
      Real.logb 2 C.card ≤ (1 - ρ + δ) * (d * d * b : ℕ)

/-- At `ρ = 1 / 2`, `NativeGapBound` is equivalent to `BoundedStackDepth.NativeBound`. -/
theorem nativeGapBound_half_iff (B : ℕ → ℕ → Prop) (M : TM) (w D : ℕ) (c : ℝ) :
    NativeGapBound (1 / 2) B M w D c ↔ NativeBound B M w D c := by
  unfold NativeGapBound NativeBound
  have h : ∀ δ : ℝ, 1 - (1 / 2 : ℝ) + δ = 1 / 2 + δ := fun δ => by ring
  simp only [h]

open Classical in
/-- Gap generalization of `BoundedStackDepth.se_class_native`: if `NativeGapBound ρ` holds at scale
`w ≥ 1` and depth `genieDepth M.k (blockWidth M w) (max c 1) (θ / 2)` (`θ > 0`), then for large `d`
no skeleton class at scale `w` of size at least `2^{(1 - ρ + θ) L}` can have every member transposed
within `c (L + 1)` steps. -/
theorem se_class_native_gap {ρ : ℝ} {B : ℕ → ℕ → Prop} {M : TM} {w : ℕ} (hw : 1 ≤ w)
    {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    (hnat : NativeGapBound ρ B M w (genieDepth M.k (blockWidth M w) (max c 1) (θ / 2)) c) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ b, B d b → 1 ≤ b → ∀ σ : Skeleton M.k,
      (2 : ℝ) ^ ((1 - ρ + θ) * (d * d * b : ℕ)) ≤
        ((univ.filter fun X : Fin (d * d * b) → Bool => X ∈ skelClass M w (d * d * b) σ).card : ℝ) →
      (∀ X ∈ skelClass M w (d * d * b) σ, TransposesInput M d b c X) → False := by
  have hw0 : 0 < w := by omega
  set ε : ℝ := θ / 2 with hεdef
  have hε : 0 < ε := by positivity
  set β := blockWidth M w
  have hβ : 1 ≤ β := one_le_blockWidth M w
  obtain ⟨d₁, hd₁⟩ := hnat (θ / 4) (by positivity)
  refine ⟨max d₁ 1, fun d hd b hB hb σ hcard htr => ?_⟩
  have hd1 : 1 ≤ d := le_of_max_le_right hd
  have hL : 1 ≤ d * d * b := Nat.mul_pos (Nat.mul_pos hd1 hd1) hb
  have hLr : (0 : ℝ) < (d * d * b : ℕ) := by exact_mod_cast hL
  set S := univ.filter fun X : Fin (d * d * b) → Bool => X ∈ skelClass M w (d * d * b) σ
  have hSpos : (0 : ℝ) < S.card := lt_of_lt_of_le (by positivity) hcard
  obtain ⟨X₀, hX₀S⟩ := card_pos.mp (by exact_mod_cast hSpos : 0 < S.card)
  have hX₀ : X₀ ∈ skelClass M w (d * d * b) σ := (mem_filter.mp hX₀S).2
  have hx : InClass M w σ (List.ofFn X₀) := hX₀
  have hT : (σ.T : ℝ) ≤ c * ((d * d * b : ℕ) + 1) := by
    obtain ⟨s, hs, hhs⟩ := (htr X₀ hX₀).halts
    obtain rfl := Transpose.Tape.Impl.haltsAt_unique hhs hx.1
    exact (Nat.cast_le.mpr hs).trans (Nat.floor_le (by positivity))
  have hagree : ∀ j t, t < σ.T → σ.s j t = skel (w : ℤ) (workWalk M (List.ofFn X₀) j) t :=
    fun j t ht => ((hx.2 t ht).2.1 j).symm
  have hTC : (σ.T : ℝ) ≤ max c 1 * ((d * d * b : ℕ) + 1) :=
    hT.trans (mul_le_mul_of_nonneg_right (le_max_left c 1) (by positivity))
  obtain ⟨Γ, hcost, hpath0⟩ := genie_cost (k := M.k) hβ hL (le_max_right c 1) hε hTC
    (fun j => skel (w : ℤ) (workWalk M (List.ofFn X₀) j))
    (fun j => isWalk_skel (by exact_mod_cast hw0) (workWalk_isWalk _ j))
  have hpath : ∀ π, IsDepPath σ.s σ.T π → LinNet.GFree Γ π →
      π.length ≤ genieDepth M.k β (max c 1) ε + 1 :=
    fun π hπ hfree => (hpath0 π ((isDepPath_congr hagree π).mp hπ) hfree).trans (Nat.le_succ _)
  set E := fun X : Fin (d * d * b) → Bool => fun u : Γ => blockVal M w (List.ofFn X) u
  have himg : (S.image E).card ≤ 2 ^ (β * Γ.card) := card_revealed_le (M := M) hw0 Γ S
  have hSne : (S.image E).Nonempty := ⟨E X₀, mem_image_of_mem E hX₀S⟩
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ (β * Γ.card) := by positivity
  obtain ⟨e, he, hfib⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    (s := S) (t := S.image E) (f := E) (b := (S.card : ℝ) / (2 : ℝ) ^ (β * Γ.card))
    (fun X hX => mem_image_of_mem E hX) hSne (by
      rw [nsmul_eq_mul, mul_div_assoc']
      rw [div_le_iff₀ h2pos]
      have : ((S.image E).card : ℝ) ≤ (2 : ℝ) ^ (β * Γ.card) := by exact_mod_cast himg
      nlinarith)
  obtain ⟨X₁, -, rfl⟩ := mem_image.mp he
  have hsub : S.filter (fun X => E X = E X₁) ⊆ (blockMachine M hw0 (d * d * b) σ).fibre Γ
      (fun v => (blockMachine M hw0 (d * d * b) σ).val X₁ v) := by
    intro X hX
    obtain ⟨hXS, hXE⟩ := mem_filter.mp hX
    have hXc : X ∈ skelClass M w (d * d * b) σ := (mem_filter.mp hXS).2
    rw [mem_blockFibre]
    refine ⟨hXc, fun v hv => ?_⟩
    show (blockMachine M hw0 (d * d * b) σ).val X v = (blockMachine M hw0 (d * d * b) σ).val X₁ v
    by_cases hvT : v < σ.T
    · rw [blockMachine_val hw0 _ σ hvT, blockMachine_val hw0 _ σ hvT]
      exact congrArg some (congrFun hXE ⟨v, hv⟩)
    · rw [blockMachine_val_of_le hw0 _ σ (by omega), blockMachine_val_of_le hw0 _ σ (by omega)]
  set W := (blockMachine M hw0 (d * d * b) σ).fibre Γ
    (fun v => (blockMachine M hw0 (d * d * b) σ).val X₁ v)
  have hWcard : (S.card : ℝ) / (2 : ℝ) ^ (β * Γ.card) ≤ W.card :=
    hfib.trans (by exact_mod_cast card_le_card hsub)
  have htr' : ∀ X ∈ skelClass M w (d * d * b) σ, OutputsTranspose M d b X :=
    fun X hX => (htr X hX).outputsTranspose
  have hW := blockMachine_isStorageCode_fibre hw0 σ htr' Γ
    (fun v => (blockMachine M hw0 (d * d * b) σ).val X₁ v)
  set NJ := fun q : Fin (d * d * b) =>
    (blockMachine M hw0 (d * d * b) σ).coneJ Γ (outTime σ w (MergeDepth.tpos d b q))
  have hWJ : IsStorageCode NJ W := by
    have eqNJ : (fun q : Fin (d * d * b) => (blockMachine M hw0 (d * d * b) σ).coneJ Γ
        (outTime σ w (Transpose.Tape.tpos d b q))) = NJ :=
      funext fun q => by simp only [NJ, tape_tpos_eq]
    rw [← eqNJ]
    exact hW
  have hlenX₀ : d * d * b ≤ (Transpose.Tape.run M (List.ofFn X₀) σ.T).outRev.length := by
    obtain ⟨s, hs, hl, -⟩ := (htr' X₀ hX₀).output
    obtain rfl := Transpose.Tape.Impl.haltsAt_unique hs hx.1
    rw [← List.length_reverse, hl]
  obtain ⟨hdepthR, hotR, hNsub⟩ := classRel_subset_coneRel hw0 hb hX₀ hlenX₀ hpath
  have hWR : IsStorageCode (coneRel w (runWalks M (List.ofFn X₀)) σ.T Γ (outTime σ w)
      fun q => MergeDepth.tpos d b q) W :=
    fun x hx' y hy v h => hWJ x hx' y hy v fun u hu => h u (hNsub v hu)
  have hup := hd₁ d (le_of_max_le_left hd) b hB X₀ σ.T hx.1 hT Γ hdepthR (outTime σ w) hotR W hWR
  have hWpos : (0 : ℝ) < W.card := lt_of_lt_of_le (by positivity) hWcard
  have hcost' : (2 : ℝ) ^ (β * Γ.card) ≤ (2 : ℝ) ^ (ε * (d * d * b : ℕ)) := by
    rw [← Real.rpow_natCast]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have h := hcost
    push_cast at h ⊢
    exact h
  have hlow : (2 : ℝ) ^ ((1 - ρ + θ - ε) * (d * d * b : ℕ)) ≤ W.card := by
    have eqPow : (2 : ℝ) ^ ((1 - ρ + θ - ε) * (d * d * b : ℕ)) =
        (2 : ℝ) ^ ((1 - ρ + θ) * (d * d * b : ℕ)) / (2 : ℝ) ^ (ε * (d * d * b : ℕ)) := by
      rw [← Real.rpow_sub (by norm_num)]
      ring_nf
    rw [eqPow]
    calc (2 : ℝ) ^ ((1 - ρ + θ) * (d * d * b : ℕ)) / (2 : ℝ) ^ (ε * (d * d * b : ℕ))
        ≤ (S.card : ℝ) / (2 : ℝ) ^ (ε * (d * d * b : ℕ)) :=
          div_le_div_of_nonneg_right hcard (by positivity)
      _ ≤ (S.card : ℝ) / (2 : ℝ) ^ (β * Γ.card) := div_le_div_of_nonneg_left hSpos.le h2pos hcost'
      _ ≤ W.card := hWcard
  have hlow' : (1 - ρ + θ - ε) * (d * d * b : ℕ) ≤ Real.logb 2 W.card :=
    (Real.le_logb_iff_rpow_le (by norm_num) hWpos).mpr hlow
  have hθL : 0 < θ * (d * d * b : ℕ) := mul_pos hθ hLr
  have hgap_arith : (1 - ρ + θ / 4) * (d * d * b : ℕ) < (1 - ρ + θ - ε) * (d * d * b : ℕ) := by
    rw [hεdef]; nlinarith only [hθL]
  linarith only [hup, hlow', hgap_arith]

open Classical in
/-- Gap generalization of `BoundedStackDepth.se_native`: under `NativeGapBound ρ` at scale `w ≥ 1`,
every machine transposing all inputs within `c (L + 1)` steps has coarse skeleton entropy strictly
above `(ρ - θ) L`. -/
theorem se_native_gap {ρ : ℝ} {B : ℕ → ℕ → Prop} {M : TM} {w : ℕ} (hw : 1 ≤ w)
    {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    (hnat : NativeGapBound ρ B M w (genieDepth M.k (blockWidth M w) (max c 1) (θ / 2)) c) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ b, B d b → 1 ≤ b →
      (∀ X : Fin (d * d * b) → Bool, TransposesInput M d b c X) →
      (ρ - θ) * (d * d * b : ℕ) <
        entropy (fun X : Fin (d * d * b) → Bool => runSkeleton M w (List.ofFn X)) := by
  obtain ⟨d₀, hd₀⟩ := se_class_native_gap hw hc hθ hnat
  refine ⟨d₀, fun d hd b hB hb htr => ?_⟩
  by_contra hH
  push Not at hH
  set f := fun X : Fin (d * d * b) → Bool => runSkeleton M w (List.ofFn X)
  obtain ⟨σ₀, hσ₀⟩ := exists_large_fibre f
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] at hσ₀
  have hbig : (2 : ℝ) ^ ((1 - ρ + θ) * (d * d * b : ℕ)) ≤
      ((univ.filter fun X => f X = σ₀).card : ℝ) := by
    refine le_trans ?_ hσ₀
    rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hpos : (0 : ℝ) < ((univ.filter fun X => f X = σ₀).card : ℝ) :=
    lt_of_lt_of_le (by positivity) hbig
  obtain ⟨X₀, hX₀⟩ := card_pos.mp (by exact_mod_cast hpos : 0 < (univ.filter fun X => f X = σ₀).card)
  have hfX₀ : f X₀ = σ₀ := (mem_filter.mp hX₀).2
  have hmem : ∀ X, f X = σ₀ → X ∈ skelClass M w (d * d * b) σ₀ := by
    intro X hX
    rw [mem_skelClass, inClass_iff_runSkeleton]
    obtain ⟨s, -, hs⟩ := (htr X).halts
    refine ⟨⟨s, hs⟩, ?_⟩
    rw [← hfX₀, runSkeleton_normalize]
    exact hX.trans hfX₀.symm
  have hcard : (2 : ℝ) ^ ((1 - ρ + θ) * (d * d * b : ℕ)) ≤
      ((univ.filter fun X : Fin (d * d * b) → Bool =>
        X ∈ skelClass M w (d * d * b) σ₀).card : ℝ) := by
    refine hbig.trans ?_
    exact_mod_cast card_le_card fun X hX => mem_filter.mpr ⟨mem_univ _, hmem X (mem_filter.mp hX).2⟩
  exact hd₀ d hd b hB hb σ₀ hcard (fun X _ => htr X)

open Classical in
/-- Gap generalization of `BoundedStackDepth.fSecond_native`: for any `η < ρ`, `NativeGapBound ρ`
at scale `1` and depth `genieDepth M.k (blockWidth M 1) (max c 1) ((ρ - η) / 2)` forces scale-`1`
skeleton entropy strictly above `η L`. -/
theorem fSecond_native_gap {ρ : ℝ} {B : ℕ → ℕ → Prop} {M : TM} {c η : ℝ} (hc : 0 < c) (hη : η < ρ)
    (hnat : NativeGapBound ρ B M 1 (genieDepth M.k (blockWidth M 1) (max c 1) ((ρ - η) / 2)) c) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ b, B d b → 1 ≤ b →
      (∀ X : Fin (d * d * b) → Bool, TransposesInput M d b c X) →
      η * (d * d * b : ℕ) <
        entropy (fun X : Fin (d * d * b) → Bool => runSkeleton M 1 (List.ofFn X)) := by
  obtain ⟨d₀, hd₀⟩ := se_native_gap le_rfl hc (by linarith : 0 < ρ - η) hnat
  refine ⟨d₀, fun d hd b hB hb htr => ?_⟩
  have h := hd₀ d hd b hB hb htr
  have eqCoef : (ρ - (ρ - η)) * (d * d * b : ℕ) = η * (d * d * b : ℕ) := by ring
  rwa [eqCoef] at h

open Classical Transpose.Tape Transpose.Tape.Impl in
/-- Gap generalization of `TapeStorageRates.native_exclusion_of_trace_support`: any deficit `ρ > η`
on `N`'s scale-`1` frozen-trace cone relations excludes any dimension property transmitted to `N`
with trace support at most `2^{η L}`. -/
theorem native_gap_exclusion_of_trace_support (N : TM) {ρ c η : ℝ} (hc : 0 < c) (hη : η < ρ)
    (hnative : NativeGapBound ρ (fun d b => b = entryBits d) N 1
      (genieDepth N.k (blockWidth N 1) (max c 1) ((ρ - η) / 2)) c)
    (Good : ℕ → Prop)
    (htransfer : ∀ᶠ d in atTop, Good d → TransposesAt N d c ∧
      Real.logb 2 (univ.image
        (fun x : Fin (d * d * entryBits d) → Bool => trace N (List.ofFn x))).card
        ≤ η * (d * d * entryBits d : ℕ)) :
    ∀ᶠ d in atTop, ¬ Good d := by
  obtain ⟨d₀, h₀⟩ := fSecond_native_gap hc hη hnative
  filter_upwards [eventually_ge_atTop d₀, htransfer] with d hd h
  intro hgood
  obtain ⟨hsuccess, hsize⟩ := h hgood
  have hlow := (skeleton_entropy_le_trace_support N 1
    (fun x : Fin (d * d * entryBits d) → Bool => List.ofFn x)).trans hsize
  exact (not_lt_of_ge hlow) (h₀ d hd _ rfl (one_le_entryBits d) hsuccess.transposesInput)

/-- Gap generalization of `TapeStorageRates.native_frozen_trace_exclusion`: for a source machine `M`,
time constant `c > 0`, and any `0 < η < ρ`, there exists an aligned simulator `Native.machine M hs`
(having `(Native.machine M hs).k = M.k` and physical time constant `11 * c + 1`) whose scale-`1`
`NativeGapBound ρ` excludes `TransposesAt M d c` for all sufficiently large `d`. -/
theorem native_gap_frozen_trace_exclusion (M : TM) {ρ c η : ℝ} (hc : 0 < c)
    (hη0 : 0 < η) (hηρ : η < ρ) :
    ∃ s : ℕ, ∃ hs : 0 < s, ∃ c' : ℝ, c' = 11 * c + 1 ∧ 1 ≤ c' ∧
      let N := Native.machine M hs
      NativeGapBound ρ (fun d b => b = entryBits d) N 1
        (genieDepth N.k (blockWidth N 1) (max c' 1) ((ρ - η) / 2)) c' →
      ∀ᶠ d in atTop, ¬ TransposesAt M d c := by
  obtain ⟨s, hs, h⟩ := aligned_low_trace_dimensions M hc.le hη0
  have hc1 : 1 ≤ 11 * c + 1 := by linarith
  have hc0 : 0 < 11 * c + 1 := by linarith
  refine ⟨s, hs, 11 * c + 1, rfl, hc1, fun hnative => ?_⟩
  apply native_gap_exclusion_of_trace_support (Native.machine M hs) hc0 hηρ hnative
    (fun d => TransposesAt M d c)
  exact h.mono fun d hd => hd (entryBits d) (one_le_entryBits d)

/-- **Corollary 9.6: The native gap form of the fifteenth paper's low-adaptivity criterion.**
Suppose for every work-tape count `k` and physical time constant `C ≥ 1` there is a deficit
`ρ k C > 0`, uniform over all machines `M` with `M.k = k` and all genie depths `D`, such that
`NativeGapBound (ρ k C) (fun d b => b = entryBits d) M 1 D C` holds. Then linear-time matrix
transposition on multitape Turing machines is impossible (`¬ LinearTimeTransposable`). -/
theorem native_gap_tests_exclude_linear (ρ : ℕ → ℝ → ℝ)
    (hρ : ∀ (k : ℕ) (C : ℝ), 1 ≤ C → 0 < ρ k C)
    (hgap : ∀ (k : ℕ) (C : ℝ), 1 ≤ C → ∀ (M : TM), M.k = k → ∀ D : ℕ,
      NativeGapBound (ρ k C) (fun d b => b = entryBits d) M 1 D C) :
    ¬ LinearTimeTransposable := by
  intro hlinear
  obtain ⟨M, c, hc, hgood⟩ := unbounded_success_of_linear hlinear
  set C : ℝ := 11 * c + 1
  have hC1 : 1 ≤ C := by dsimp [C]; linarith
  have hρpos : 0 < ρ M.k C := hρ M.k C hC1
  obtain ⟨s, hs, c', rfl, -, htest⟩ :=
    native_gap_frozen_trace_exclusion M (ρ := ρ M.k C) (η := ρ M.k C / 2) hc
      (by linarith) (by linarith)
  have hN : NativeGapBound (ρ M.k C) (fun d b => b = entryBits d) (Native.machine M hs) 1
      (genieDepth (Native.machine M hs).k (blockWidth (Native.machine M hs) 1)
        (max (11 * c + 1) 1) ((ρ M.k C - ρ M.k C / 2) / 2)) (11 * c + 1) :=
    hgap M.k (11 * c + 1) hC1 (Native.machine M hs) (native_machine_k M hs) _
  obtain ⟨d₀, hd₀⟩ := eventually_atTop.mp (htest hN)
  obtain ⟨d, hd, htr⟩ := hgood d₀
  exact hd₀ d hd htr

/-- Existential variant of `native_gap_tests_exclude_linear`. -/
theorem native_gap_exists_exclude_linear
    (h : ∀ (k : ℕ) (C : ℝ), 1 ≤ C → ∃ ρ : ℝ, 0 < ρ ∧
      ∀ (M : TM), M.k = k → ∀ D : ℕ,
        NativeGapBound ρ (fun d b => b = entryBits d) M 1 D C) :
    ¬ LinearTimeTransposable := by
  classical
  let ρ : ℕ → ℝ → ℝ := fun k C =>
    if hC : 1 ≤ C then Classical.choose (h k C hC) else 1
  refine native_gap_tests_exclude_linear ρ (fun k C hC => ?_) (fun k C hC M hMk D => ?_)
  · dsimp only [ρ]
    rw [dite_eq_left_of_eq_true (eq_true hC)]
    exact (Classical.choose_spec (h k C hC)).1
  · dsimp only [ρ]
    rw [dite_eq_left_of_eq_true (eq_true hC)]
    exact (Classical.choose_spec (h k C hC)).2 M hMk D

end NativeRelations
