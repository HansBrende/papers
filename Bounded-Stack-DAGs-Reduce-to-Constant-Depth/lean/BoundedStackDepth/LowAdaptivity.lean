import BoundedStackDepth.Machines
import MergeDepth.SkeletonSE

/-!
# Corollary L: low adaptivity without bounded entry

The eighth paper's Corollary F″ (its Corollary 6.4) excludes linear-time transposers whose traces
have entropy at most `ηL`, `η < 1/2`, if every likely trace enters every work-tape cell boundedly
often; its November 2026 update replaces the refuted Question 9.1 by the *native bound*, a half
bound for the binary storage codes on the cone relations of frozen traces. The eleventh paper's
Theorem SE has the same structure on the classes of inputs with a common coarse skeleton at a scale
`w`; at `w = 1` the skeleton of a run (`MergeDepth.runSkeleton`) records the positions of all heads and the output count
before the halting time, a function of the trace, so its classes are unions of trace classes. Both proofs use the
bounded entry only to obtain a genie from the eighth paper's Theorem F. Theorem T gives the genie for
every walk (`genie_cost`), so the hypothesis goes.

* `NativeBound B M w D c`: **the native bound for the frozen traces of `M`** at scale `w` and depth
  `D`, runtime constant `c`, at the widths `b` with `B d b`: the binary storage codes for the cone
  relation (`MergeDepth.coneRel`) of the run of `M` on an input of length `L`, before its halting time
  `T ≤ c (L + 1)`, for a set `Γ` of steps of full depth at most `D` and any output times in the output
  blocks, have at most `2^{(1/2 + δ) L}` words for large `d`. The eighth paper's native bound is
  uniform over the machines with `k` work tapes at the widths `b(d)`, and implies this one for each
  such `M` with `B d b ↔ b = b(d)`.
* `se_class_native`, `se_native`: **(a)** the eleventh paper's Theorem SE (its Theorem 4.13), both
  statements, without its bounded-entry hypothesis, given the native bound at scale `w`: no skeleton
  class at scale `w` with at least `2^{(1/2 + η) L}` members is transposed within `c (L + 1)` steps,
  and every linear-time transposer has `H(σ_w(X)) > (1/2 - η) L`, at the widths allowed by `B`. The proof is that of
  `MergeDepth.thm_SE_class`, with the genie of Theorem T in place of `skeleton_genie` and the native
  bound in place of Question 9.1 and the paid trimming.
* `fSecond_native_class`, `fSecond_native`: **(b)** Corollary F″ without its hypothesis (ii), given
  the native bound for frozen traces: no skeleton class at scale `1` with at least `2^{(1 - η) L}`
  members is transposed within `c (L + 1)` steps, so a machine that transposes every input within
  `c (L + 1)` steps has no trace followed by that many inputs, and `H(σ_1(X)) > ηL`, `η < 1/2`; since
  `σ_1` is a function of the trace, the trace has entropy above `ηL` as well.
-/

namespace BoundedStackDepth

open Finset BoundedNesting MergeDepth MotionDepthCodes Transpose

/-- The block width is at least `1`. -/
theorem one_le_blockWidth (M : TM) (w : ℕ) : 1 ≤ blockWidth M w := by
  unfold blockWidth
  omega

open Classical in
/-- **The native bound for the frozen traces of `M`** at scale `w` and depth `D`, runtime constant
`c`, at the widths `b` with `B d b`. For every `δ > 0` there is `d₀` such that for `d ≥ d₀` and every
width `b` with `B d b` (`L = d² b`): for every input `X ∈ {0,1}^L` on which `M` halts at a time
`T ≤ c (L + 1)`, every set `Γ` of steps under which every `Γ`-free path of the dependency DAG of the
coarse work walks of the run at scale `w` has at most `D + 1` vertices, and all output times `ot`
before `T` in the output blocks of the transposed positions, every binary storage code for the cone
relation `coneRel w (runWalks M X) T Γ ot tpos` has at most `2^{(1/2 + δ) L}` words. At `w = 1` the
coarse walks are the head walks of the run, the output times are the append times, and the relation
is the cone relation of the frozen trace; at `w > 1` the output times are any times in the output
blocks, a mild strengthening of the relations of the skeleton classes, whose output times are `t̂`.
The eighth paper's native bound is uniform over the machines with `M.k` work tapes at the widths
`b(d)`; it implies this one with `B d b ↔ b = b(d)`. -/
def NativeBound (B : ℕ → ℕ → Prop) (M : TM) (w D : ℕ) (c : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ b, B d b →
    ∀ (X : Fin (d * d * b) → Bool) (T : ℕ), Transpose.Tape.HaltsAt M (List.ofFn X) T →
    (T : ℝ) ≤ c * ((d * d * b : ℕ) + 1) → ∀ Γ : Finset ℕ,
    (∀ π, IsDepPath (fun j => skel w (runWalks M (List.ofFn X) (some (some j)))) T π →
      LinNet.GFree Γ π → π.length ≤ D + 1) →
    ∀ ot : ℕ → ℕ, (∀ q : Fin (d * d * b), ot (tpos d b q) < T ∧
      (tpos d b q : ℤ) / w = runWalks M (List.ofFn X) (some none) (ot (tpos d b q)) / w) →
    ∀ C : Finset (Fin (d * d * b) → Bool),
      IsStorageCode (coneRel w (runWalks M (List.ofFn X)) T Γ ot fun q => tpos d b q) C →
      Real.logb 2 C.card ≤ (1 / 2 + δ) * (d * d * b : ℕ)

open Classical in
/-- **(a) of Corollary L, class form: Theorem SE without bounded entry.** Let `w ≥ 1`, `c > 0` and
`η > 0`, and let the native bound hold at scale `w` and at the depth of the genie of Theorem T,
`genieDepth M.k (blockWidth M w) (max c 1) (η/2)`, at the widths `b` with `B d b`. There is `d₀`
such that for no `d ≥ d₀` and no width `b ≥ 1` with `B d b` is there a skeleton class `𝒳_σ` at scale
`w` with at least `2^{(1/2 + η) L}` members on every one of which `M` halts within `c (L + 1)` steps
with the transposed output. -/
theorem se_class_native {B : ℕ → ℕ → Prop} {M : TM} {w : ℕ} (hw : 1 ≤ w) {c η : ℝ} (hc : 0 < c)
    (hη : 0 < η) (hnat : NativeBound B M w (genieDepth M.k (blockWidth M w) (max c 1) (η / 2)) c) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ b, B d b → 1 ≤ b → ∀ σ : Skeleton M.k,
      (2 : ℝ) ^ ((1 / 2 + η) * (d * d * b : ℕ)) ≤
        ((univ.filter fun X : Fin (d * d * b) → Bool => X ∈ skelClass M w (d * d * b) σ).card : ℝ) →
      (∀ X ∈ skelClass M w (d * d * b) σ, TransposesInput M d b c X) → False := by
  have hw0 : 0 < w := by omega
  set ε : ℝ := η / 2 with hεdef
  have hε : 0 < ε := by positivity
  set β := blockWidth M w
  have hβ : 1 ≤ β := one_le_blockWidth M w
  obtain ⟨d₁, hd₁⟩ := hnat (η / 4) (by positivity)
  refine ⟨max d₁ 1, fun d hd b hB hb σ hcard htr => ?_⟩
  have hd1 : 1 ≤ d := le_of_max_le_right hd
  have hL : 1 ≤ d * d * b := Nat.mul_pos (Nat.mul_pos hd1 hd1) hb
  have hLr : (0 : ℝ) < (d * d * b : ℕ) := by exact_mod_cast hL
  -- a member of the class
  set S := univ.filter fun X : Fin (d * d * b) → Bool => X ∈ skelClass M w (d * d * b) σ
  have hSpos : (0 : ℝ) < S.card := lt_of_lt_of_le (by positivity) hcard
  obtain ⟨X₀, hX₀S⟩ := card_pos.mp (by exact_mod_cast hSpos : 0 < S.card)
  have hX₀ : X₀ ∈ skelClass M w (d * d * b) σ := (mem_filter.mp hX₀S).2
  have hx : InClass M w σ (List.ofFn X₀) := hX₀
  -- the halting time is at most `c (L + 1)`
  have hT : (σ.T : ℝ) ≤ c * ((d * d * b : ℕ) + 1) := by
    obtain ⟨s, hs, hhs⟩ := (htr X₀ hX₀).halts
    obtain rfl := Transpose.Tape.Impl.haltsAt_unique hhs hx.1
    exact (Nat.cast_le.mpr hs).trans (Nat.floor_le (by positivity))
  -- the genie of Theorem T on the coarse work walks of `X₀`, transferred to `σ`
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
  -- a large fibre of the revealed word
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
    (fun v => (blockMachine M hw0 (d * d * b) σ).val X₁ v) with hWdef
  have hWcard : (S.card : ℝ) / (2 : ℝ) ^ (β * Γ.card) ≤ W.card :=
    hfib.trans (by exact_mod_cast card_le_card hsub)
  -- `W` is a storage code for the class relation, which lies inside the cone relation
  have htr' : ∀ X ∈ skelClass M w (d * d * b) σ, OutputsTranspose M d b X :=
    fun X hX => (htr X hX).outputsTranspose
  have hW := blockMachine_isStorageCode_fibre hw0 σ htr' Γ
    (fun v => (blockMachine M hw0 (d * d * b) σ).val X₁ v)
  set NJ := fun q : Fin (d * d * b) =>
    (blockMachine M hw0 (d * d * b) σ).coneJ Γ (outTime σ w (tpos d b q)) with hNJ
  have hWJ : IsStorageCode NJ W := by
    have e : (fun q : Fin (d * d * b) => (blockMachine M hw0 (d * d * b) σ).coneJ Γ
        (outTime σ w (Transpose.Tape.tpos d b q))) = NJ :=
      funext fun q => by simp only [NJ, tape_tpos_eq]
    rw [← e]
    exact hW
  have hlenX₀ : d * d * b ≤ (Transpose.Tape.run M (List.ofFn X₀) σ.T).outRev.length := by
    obtain ⟨s, hs, hl, -⟩ := (htr' X₀ hX₀).output
    obtain rfl := Transpose.Tape.Impl.haltsAt_unique hs hx.1
    rw [← List.length_reverse, hl]
  obtain ⟨hdepthR, hotR, hNsub⟩ := classRel_subset_coneRel hw0 hb hX₀ hlenX₀ hpath
  have hWR : IsStorageCode (coneRel w (runWalks M (List.ofFn X₀)) σ.T Γ (outTime σ w)
      fun q => tpos d b q) W :=
    fun x hx' y hy v h => hWJ x hx' y hy v fun u hu => h u (hNsub v hu)
  -- the native bound: `log₂ |W| ≤ (1/2 + η/4) L`
  have hup := hd₁ d (le_of_max_le_left hd) b hB X₀ σ.T hx.1 hT Γ hdepthR (outTime σ w) hotR W hWR
  -- the lower bound `log₂ |W| ≥ (1/2 + η - ε) L`
  have hWpos : (0 : ℝ) < W.card := lt_of_lt_of_le (by positivity) hWcard
  have hcost' : (2 : ℝ) ^ (β * Γ.card) ≤ (2 : ℝ) ^ (ε * (d * d * b : ℕ)) := by
    rw [← Real.rpow_natCast]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have h := hcost
    push_cast at h ⊢
    exact h
  have hlow : (2 : ℝ) ^ ((1 / 2 + η - ε) * (d * d * b : ℕ)) ≤ W.card := by
    have e : (2 : ℝ) ^ ((1 / 2 + η - ε) * (d * d * b : ℕ)) =
        (2 : ℝ) ^ ((1 / 2 + η) * (d * d * b : ℕ)) / (2 : ℝ) ^ (ε * (d * d * b : ℕ)) := by
      rw [← Real.rpow_sub (by norm_num)]
      ring_nf
    rw [e]
    calc (2 : ℝ) ^ ((1 / 2 + η) * (d * d * b : ℕ)) / (2 : ℝ) ^ (ε * (d * d * b : ℕ))
        ≤ (S.card : ℝ) / (2 : ℝ) ^ (ε * (d * d * b : ℕ)) :=
          div_le_div_of_nonneg_right hcard (by positivity)
      _ ≤ (S.card : ℝ) / (2 : ℝ) ^ (β * Γ.card) := div_le_div_of_nonneg_left hSpos.le h2pos hcost'
      _ ≤ W.card := hWcard
  have hlow' : (1 / 2 + η - ε) * (d * d * b : ℕ) ≤ Real.logb 2 W.card :=
    (Real.le_logb_iff_rpow_le (by norm_num) hWpos).mpr hlow
  -- the contradiction: `(1/2 + η/2) L ≤ (1/2 + η/4) L`
  have hηL : 0 < η * (d * d * b : ℕ) := mul_pos hη hLr
  nlinarith

open Classical in
/-- **(a) of Corollary L: Theorem SE without bounded entry.** Let `w ≥ 1`, `c > 0`, `η > 0`, and
let the native bound hold at scale `w`, at the depth of the genie of Theorem T and at the widths
`b` with `B d b`. There is `d₀` such that for `d ≥ d₀` and every width `b ≥ 1` with `B d b`: if `M`
transposes every input `X ∈ {0,1}^L` within `c (L + 1)` steps, then `H(σ_w(X)) > (1/2 - η) L` for a
uniformly random input. -/
theorem se_native {B : ℕ → ℕ → Prop} {M : TM} {w : ℕ} (hw : 1 ≤ w) {c η : ℝ} (hc : 0 < c)
    (hη : 0 < η) (hnat : NativeBound B M w (genieDepth M.k (blockWidth M w) (max c 1) (η / 2)) c) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ b, B d b → 1 ≤ b →
      (∀ X : Fin (d * d * b) → Bool, TransposesInput M d b c X) →
      (1 / 2 - η) * (d * d * b : ℕ) <
        entropy (fun X : Fin (d * d * b) → Bool => runSkeleton M w (List.ofFn X)) := by
  obtain ⟨d₀, hd₀⟩ := se_class_native hw hc hη hnat
  refine ⟨d₀, fun d hd b hB hb htr => ?_⟩
  by_contra hH
  push Not at hH
  set f := fun X : Fin (d * d * b) → Bool => runSkeleton M w (List.ofFn X)
  obtain ⟨σ₀, hσ₀⟩ := exists_large_fibre f
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] at hσ₀
  -- the fibre has at least `2^{(1/2 + η) L}` elements
  have hbig : (2 : ℝ) ^ ((1 / 2 + η) * (d * d * b : ℕ)) ≤
      ((univ.filter fun X => f X = σ₀).card : ℝ) := by
    refine le_trans ?_ hσ₀
    rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hpos : (0 : ℝ) < ((univ.filter fun X => f X = σ₀).card : ℝ) :=
    lt_of_lt_of_le (by positivity) hbig
  obtain ⟨X₀, hX₀⟩ := card_pos.mp (by exact_mod_cast hpos : 0 < (univ.filter fun X => f X = σ₀).card)
  have hfX₀ : f X₀ = σ₀ := (mem_filter.mp hX₀).2
  -- the fibre lies in the class of `σ₀`
  have hmem : ∀ X, f X = σ₀ → X ∈ skelClass M w (d * d * b) σ₀ := by
    intro X hX
    rw [mem_skelClass, inClass_iff_runSkeleton]
    obtain ⟨s, -, hs⟩ := (htr X).halts
    refine ⟨⟨s, hs⟩, ?_⟩
    rw [← hfX₀, runSkeleton_normalize]
    exact hX.trans hfX₀.symm
  have hcard : (2 : ℝ) ^ ((1 / 2 + η) * (d * d * b : ℕ)) ≤
      ((univ.filter fun X : Fin (d * d * b) → Bool =>
        X ∈ skelClass M w (d * d * b) σ₀).card : ℝ) := by
    refine hbig.trans ?_
    exact_mod_cast card_le_card fun X hX => mem_filter.mpr ⟨mem_univ _, hmem X (mem_filter.mp hX).2⟩
  exact hd₀ d hd b hB hb σ₀ hcard (fun X _ => htr X)

open Classical in
/-- **(b) of Corollary L, likely-trace form: Corollary F″ without bounded entry.** Let `c > 0`,
`η < 1/2`, and let the native bound for frozen traces hold at the depth of the genie of Theorem T,
`genieDepth M.k (blockWidth M 1) (max c 1) ((1/2 - η)/2)`, at the widths `b` with `B d b`. There
is `d₀` such that for no `d ≥ d₀` and no width `b ≥ 1` with `B d b` does `M` transpose, within
`c (L + 1)` steps, every input of a skeleton class at scale `1` with at least `2^{(1 - η) L}` members.
A skeleton class at scale `1` is a union of trace classes, so if `M` transposes every input, no trace
is followed by that many inputs: the single condition of Corollary F″, a trace of probability at
least `2^{-ηL}`, is excluded. -/
theorem fSecond_native_class {B : ℕ → ℕ → Prop} {M : TM} {c η : ℝ} (hc : 0 < c) (hη : η < 1 / 2)
    (hnat : NativeBound B M 1 (genieDepth M.k (blockWidth M 1) (max c 1) ((1 / 2 - η) / 2)) c) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ b, B d b → 1 ≤ b → ∀ σ : Skeleton M.k,
      (2 : ℝ) ^ ((1 - η) * (d * d * b : ℕ)) ≤
        ((univ.filter fun X : Fin (d * d * b) → Bool => X ∈ skelClass M 1 (d * d * b) σ).card : ℝ) →
      (∀ X ∈ skelClass M 1 (d * d * b) σ, TransposesInput M d b c X) → False := by
  obtain ⟨d₀, hd₀⟩ := se_class_native le_rfl hc (by linarith : 0 < 1 / 2 - η) hnat
  refine ⟨d₀, fun d hd b hB hb σ hcard htr => hd₀ d hd b hB hb σ ?_ htr⟩
  have e : (1 / 2 + (1 / 2 - η)) * (d * d * b : ℕ) = (1 - η) * (d * d * b : ℕ) := by ring
  rwa [e]

open Classical in
/-- **(b) of Corollary L: Corollary F″ without bounded entry.** Let `c > 0`, `η < 1/2`, and let the
native bound for frozen traces hold at the depth of the genie of Theorem T and at the widths `b`
with `B d b`. There is `d₀` such that for `d ≥ d₀` and every width `b ≥ 1` with `B d b`: if `M`
transposes every input `X ∈ {0,1}^L` within `c (L + 1)` steps, then its skeleton at scale `1` has
entropy `H(σ_1(X)) > ηL` for a uniformly random input. `σ_1(X)` is a function of the trace, so the
trace has entropy above `ηL` as well: hypothesis (iii) of Corollary F″ fails. -/
theorem fSecond_native {B : ℕ → ℕ → Prop} {M : TM} {c η : ℝ} (hc : 0 < c) (hη : η < 1 / 2)
    (hnat : NativeBound B M 1 (genieDepth M.k (blockWidth M 1) (max c 1) ((1 / 2 - η) / 2)) c) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ b, B d b → 1 ≤ b →
      (∀ X : Fin (d * d * b) → Bool, TransposesInput M d b c X) →
      η * (d * d * b : ℕ) <
        entropy (fun X : Fin (d * d * b) → Bool => runSkeleton M 1 (List.ofFn X)) := by
  obtain ⟨d₀, hd₀⟩ := se_native le_rfl hc (by linarith : 0 < 1 / 2 - η) hnat
  refine ⟨d₀, fun d hd b hB hb htr => ?_⟩
  have h := hd₀ d hd b hB hb htr
  have e : (1 / 2 - (1 / 2 - η)) * (d * d * b : ℕ) = η * (d * d * b : ℕ) := by ring
  rwa [e] at h

end BoundedStackDepth
