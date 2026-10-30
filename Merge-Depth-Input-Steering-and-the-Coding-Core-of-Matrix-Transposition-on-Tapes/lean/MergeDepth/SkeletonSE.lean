import MergeDepth.SkelUniformQ91
import MergeDepth.HCStarQ91
import MergeDepth.BlockMachine
import MergeDepth.Entropy

/-!
# Theorem SE (skeleton entropy), given binary [Q9.1]

The machine is the frozen `Transpose.TM`; skeletons, skeleton classes and the block machine are
those of `MergeDepth.BlockMachine`.

* `runWalks M x`: the head walks of the run on `x` (input head, output count, work heads) for all
  times; they are walks (`runWalks_isWalk`).
* `depStep_congr`, `coneJ_subset_coneRel_of_lt`: the bridge of Lemma 4.7 to the cone relation of
  Lemma 4.9 that needs the reference walks only before `T` (the block machine of `σ` reads the
  components of `σ`, which agree with the walks of a member only before `T`).
* `classRel_subset_coneRel`: for a member `X₀` of a class on which `M` transposes, the relation
  `N_Γ(q) = J_Γ(t̂_{tpos q})` of the block machine lies inside the cone relation of the reference
  walks of `X₀`, with output times `t̂` (`outTime`) in the output blocks.
* `skel_uniform_class`: **Lemma 4.12 as stated** (the relations of the skeleton classes of a
  machine), from the machine-free `skel_uniform_binary`.
* `thm_SE_class`: **Theorem SE, second ("more precisely") statement.** Given binary [Q9.1], for
  `k ≥ 1` work tapes, `V, w ≥ 1`, `c > 0` and `η > 0` there is `d₀` such that at no `d ≥ d₀` and
  no width `b ≥ 1` is there a skeleton class `𝒳_σ` at scale `w` with at least `2^{(1/2+η)L}`
  elements, on every member of which `M` halts within `c (L + 1)` steps with the transposed output,
  and with a member of entry at most `V` on every work tape.
* `thm_SE`: **Theorem SE, first statement.** Under (i) and (ii), `H(σ_w(X)) > (1/2 - η) L`.
-/

namespace MergeDepth

open Finset Filter BoundedNesting DirectedRecovery MotionDepthCodes Transpose

set_option autoImplicit false

/-! ### The head walks of a run -/

/-- The head walks of the run on `x`, for all times: the input head, the output count and the work
heads. -/
def runWalks (M : TM) (x : List Bool) : Tp M.k → ℕ → ℤ
  | none => fun t => (Transpose.Tape.run M x t).inPos
  | some none => fun t => ((Transpose.Tape.run M x t).outRev.length : ℤ)
  | some (some j) => fun t => (Transpose.Tape.run M x t).workPos j

theorem runWalks_isWalk (M : TM) (x : List Bool) : ∀ c, IsWalk (runWalks M x c)
  | none => fun t => by
    simp only [runWalks]
    rw [inPos_eq_input, inPos_eq_input]
    exact (trace M x).abs_input_succ_sub_le t
  | some none => fun t => by
    simp only [runWalks]
    have h := Transpose.Tape.Impl.outRev_length_succ (M := M) x t
    rw [h]
    split_ifs <;> simp
  | some (some j) => workWalk_isWalk x j

/-! ### The bridge to the cone relation, before `T` -/

section Bridge

variable {k : ℕ}

/-- Dependency steps depend only on the walks before `T`. -/
theorem depStep_congr {s s' : Fin k → ℕ → ℤ} {T : ℕ} (h : ∀ j t, t < T → s j t = s' j t)
    (a b : ℕ) : DepStep s T a b ↔ DepStep s' T a b := by
  simp only [DepStep, allHops_congr h]

open Classical in
/-- **The cone of a block DAG lies in the cone relation**, for a start time `ot (dm q) < T`, if the
out-edges are dependency steps of the coarse reference walks and the input blocks read before `T`
lie in the blocks of the input reference walk. -/
theorem coneJ_subset_coneRel_of_lt {L : ℕ} {α : Type*} (G : BlockFunDag L α) {w : ℕ}
    {z : Tp k → ℕ → ℤ} {T : ℕ} {Γ : Finset ℕ}
    (hout : ∀ t, ∀ u ∈ G.out t, DepStep (fun j => skel w (z (some (some j)))) T t u)
    (hblk : ∀ u < T, ∀ p ∈ G.blk u, (p : ℤ) / w = z none u / w) (ot : ℕ → ℕ) (dm : Fin L → ℕ)
    (q : Fin L) (hq : ot (dm q) < T) : G.coneJ Γ (ot (dm q)) ⊆ coneRel w z T Γ ot dm q := by
  intro p hp
  obtain ⟨u, hu, hpu⟩ := mem_biUnion.mp hp
  obtain ⟨π, hπ, hfree, hlast⟩ := (mem_coneV G.net).mp hu
  have hdep : ∀ t, ∀ u ∈ G.net.out t, DepStep (fun j => skel w (z (some (some j)))) T t u :=
    fun t u hu => hout t u hu
  have hπdep := isDepPath_of_paths hdep π _ hπ
  have hule : u ≤ ot (dm q) := hlast ▸ getLastD_le_of_paths G.net _ π hπ
  obtain ⟨π', rfl⟩ := G.net.mem_paths_head hπ
  refine mem_filter.mpr ⟨mem_univ _, π', hπdep, hfree, ?_⟩
  rw [hlast]
  exact hblk u (by omega) p hpu

/-- Membership in a fibre of the revealed word. -/
theorem mem_blockFibre {L : ℕ} {α : Type*} (G : BlockFunDag L α) (Γ : Finset ℕ) (g : ℕ → α)
    (X : Fin L → Bool) : X ∈ G.fibre Γ g ↔ X ∈ G.S ∧ ∀ v ∈ Γ, G.val X v = g v := by
  classical
  unfold BlockFunDag.fibre
  rw [Finset.mem_filter]
  simp

end Bridge

/-! ### The relation of a skeleton class lies in a cone relation -/

section Class

variable {M : TM} {w : ℕ} (hw : 0 < w) {d b : ℕ} {σ : Skeleton M.k}

include hw in
open Classical in
/-- **The class relation inside the cone relation.** Let `X₀` be a member of `𝒳_σ` that appends at
least `L` bits before `T`, and let `Γ` be a genie whose `Γ`-free paths in the block DAG of
`σ` have at most `D + 1` vertices. With the reference walks `runWalks M x` and the output times
`t̂ = outTime σ w`: the reference walks are walks, `Γ` has full depth at most `D` in the block DAG of
their coarse work walks, the output times lie in the output blocks, and the relation of the block
machine, `N_Γ(q) = J_Γ(t̂_{tpos q})`, lies inside the cone relation. -/
theorem classRel_subset_coneRel (hb : 1 ≤ b) {X₀ : Fin (d * d * b) → Bool}
    (hX₀ : X₀ ∈ skelClass M w (d * d * b) σ)
    (hlen : d * d * b ≤ (Transpose.Tape.run M (List.ofFn X₀) σ.T).outRev.length) {Γ : Finset ℕ}
    {D : ℕ} (hpath : ∀ π, IsDepPath σ.s σ.T π → LinNet.GFree Γ π → π.length ≤ D + 1) :
    (∀ π, IsDepPath (fun j => skel w (runWalks M (List.ofFn X₀) (some (some j)))) σ.T π →
      LinNet.GFree Γ π → π.length ≤ D + 1) ∧
    (∀ q : Fin (d * d * b), outTime σ w (tpos d b q) < σ.T ∧
      (tpos d b q : ℤ) / w = runWalks M (List.ofFn X₀) (some none) (outTime σ w (tpos d b q)) / w) ∧
    ∀ q : Fin (d * d * b), (blockMachine M hw (d * d * b) σ).coneJ Γ (outTime σ w (tpos d b q)) ⊆
      coneRel w (runWalks M (List.ofFn X₀)) σ.T Γ (outTime σ w)
        (fun q : Fin (d * d * b) => tpos d b q) q := by
  have hx : InClass M w σ (List.ofFn X₀) := hX₀
  have hagree : ∀ j t, t < σ.T →
      σ.s j t = skel w (runWalks M (List.ofFn X₀) (some (some j))) t := by
    intro j t ht
    have h := (hx.2 t ht).2.1 j
    exact h.symm
  have hot : ∀ q : Fin (d * d * b), outTime σ w (tpos d b q) < σ.T ∧
      (tpos d b q : ℤ) / w =
        runWalks M (List.ofFn X₀) (some none) (outTime σ w (tpos d b q)) / w := by
    intro q
    have hr : tpos d b q < (Transpose.Tape.run M (List.ofFn X₀) σ.T).outRev.length :=
      lt_of_lt_of_le (tpos_lt (by omega) q.2) hlen
    obtain ⟨h1, h2, -, -⟩ := outTime_spec hx hr
    refine ⟨h1, ?_⟩
    have h3 := (hx.2 _ h1).2.2
    have e : runWalks M (List.ofFn X₀) (some none) (outTime σ w (tpos d b q)) =
        ((Transpose.Tape.run M (List.ofFn X₀) (outTime σ w (tpos d b q))).outRev.length : ℤ) :=
      rfl
    rw [e, ← Int.natCast_div, ← Int.natCast_div, h3, h2]
  have hout : ∀ t, ∀ u ∈ (blockMachine M hw (d * d * b) σ).out t,
      DepStep (fun j => skel w (runWalks M (List.ofFn X₀) (some (some j)))) σ.T t u := by
    intro t u hu
    have hu' : u ∈ (range σ.T).filter (BlockStep σ.s σ.T t ·) := hu
    exact (depStep_congr hagree t u).mp ((blockStep_iff _ _ t u).mp (mem_filter.mp hu').2)
  have hblk : ∀ u < σ.T, ∀ p ∈ (blockMachine M hw (d * d * b) σ).blk u,
      (p : ℤ) / w = runWalks M (List.ofFn X₀) none u / w := by
    intro u hu p hp
    have hp' : p ∈ inBlock (d * d * b) w (σ.s0 u) := hp
    rw [mem_inBlock] at hp'
    rw [hp']
    exact ((hx.2 u hu).1).symm
  refine ⟨fun π hπ hfree => hpath π ((isDepPath_congr hagree π).mpr hπ) hfree, hot, fun q => ?_⟩
  exact coneJ_subset_coneRel_of_lt (blockMachine M hw (d * d * b) σ)
    (z := runWalks M (List.ofFn X₀)) (T := σ.T) (Γ := Γ) hout hblk (outTime σ w)
    (fun q : Fin (d * d * b) => tpos d b q) q (hot q).1

end Class

open Classical in
/-- **Lemma 4.12 as stated in the paper, given binary [Q9.1]**: the relations of the skeleton
classes of a machine `M` with `k` work tapes. Let `w ≥ 1`, `D`, `c ≥ 0`, `0 < δ < 1`,
`ϑ ≥ w B/δ` (`B = ∑_{h ≤ D} (k + 1)^h`) and `ζ > 0`. There is `d₀` such that for `d ≥ d₀`, every
width `b ≥ 1`, every skeleton `σ` at scale `w` with `T_σ ≤ c (L + 1)` and a member `X₀` that
appends at least `L` bits before `T_σ`, and every genie `Γ` of full depth at most `D` in the block
DAG `H̄_σ`: for the relation `N_Γ(q) = J_Γ(t̂_{tpos q})` of Lemma 4.7 and
`Q = [0, L) ∖ (H_ϑ ∪ S_Γ)`, every binary storage code `𝒞` for `(N_Γ)_Q` has
`log₂ |𝒞| ≤ (1/2 + ζ) |Q|`. The threshold depends only on `k`, `w`, `D`, `c`, `δ`, `ϑ` and `ζ`. -/
theorem skel_uniform_class (hQ : Q91Binary) (k : ℕ) {w D ϑ : ℕ} (hw : 0 < w) {c δ : ℝ}
    (hc : 0 ≤ c) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hϑ : ((w * ∑ h ∈ range (D + 1), (k + 1) ^ h : ℕ) : ℝ) / δ ≤ ϑ) {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ b : ℕ, 1 ≤ b → ∀ (M : TM), M.k = k → ∀ σ : Skeleton M.k,
      (σ.T : ℝ) ≤ c * (d * d * b + 1) → ∀ X₀ ∈ skelClass M w (d * d * b) σ,
      d * d * b ≤ (Transpose.Tape.run M (List.ofFn X₀) σ.T).outRev.length →
      ∀ Γ : Finset ℕ, (∀ π, IsDepPath σ.s σ.T π → LinNet.GFree Γ π → π.length ≤ D + 1) →
      ∀ C : Finset (skelRetained (fun q : Fin (d * d * b) =>
          (blockMachine M hw (d * d * b) σ).coneJ Γ (outTime σ w (tpos d b q))) ϑ → Bool),
        IsStorageCode (inducedNeighborhood (fun q : Fin (d * d * b) =>
          (blockMachine M hw (d * d * b) σ).coneJ Γ (outTime σ w (tpos d b q)))
          (skelRetained (fun q : Fin (d * d * b) =>
            (blockMachine M hw (d * d * b) σ).coneJ Γ (outTime σ w (tpos d b q))) ϑ)) C →
        Real.logb 2 C.card ≤ (1 / 2 + ζ) * (skelRetained (fun q : Fin (d * d * b) =>
          (blockMachine M hw (d * d * b) σ).coneJ Γ (outTime σ w (tpos d b q))) ϑ).card := by
  obtain ⟨d₀, hd₀⟩ := skel_uniform_binary hQ k (w := w) (D := D) (by omega) hc hδ hδ1 hϑ hζ
  refine ⟨d₀, fun d hd b hb M hk σ hT X₀ hX₀ hlen Γ hpath C hC => ?_⟩
  subst hk
  obtain ⟨hdepthR, hotR, hNsub⟩ := classRel_subset_coneRel hw hb hX₀ hlen hpath
  exact hd₀ d hd b hb (runWalks M (List.ofFn X₀)) (runWalks_isWalk M _) σ.T Γ hdepthR
    (outTime σ w) hotR hT _ hNsub C hC

/-! ### Theorem SE -/

open Classical in
/-- **Theorem SE, the class form ("more precisely"), given binary [Q9.1].** Let `M` have `k ≥ 1`
work tapes, `V, w ≥ 1`, `c > 0` and `η > 0`. There is `d₀` such that for no `d ≥ d₀` and no width
`b ≥ 1` (with `L = d² b`) is there a skeleton `σ` at scale `w` whose class `𝒳_σ` has at least
`2^{(1/2 + η) L}` elements, such that `M` transposes every member within `c (L + 1)` steps and has
entry at most `V` on every work tape on some member. -/
theorem thm_SE_class (hQ : Q91Binary) {M : TM} (hk : 1 ≤ M.k) {V w : ℕ} (hV : 1 ≤ V)
    (hw : 1 ≤ w) {c η : ℝ} (hc : 0 < c) (hη : 0 < η) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ b, 1 ≤ b → ∀ σ : Skeleton M.k,
      (2 : ℝ) ^ ((1 / 2 + η) * (d * d * b : ℕ)) ≤
        ((univ.filter fun X : Fin (d * d * b) → Bool => X ∈ skelClass M w (d * d * b) σ).card : ℝ) →
      (∀ X ∈ skelClass M w (d * d * b) σ, TransposesInput M d b c X) →
      (∃ X ∈ skelClass M w (d * d * b) σ,
        ∀ j cell, (entries (workWalk M (List.ofFn X) j) cell (σ.T - 1)).card ≤ V) →
      False := by
  have hw0 : 0 < w := by omega
  -- the constants of the proof
  set ε : ℝ := η / 2 with hεdef
  set δ : ℝ := min (η / 2) (1 / 2) with hδdef
  have hε : 0 < ε := by positivity
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδ1 : δ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hδη : δ ≤ η / 2 := min_le_left _ _
  set β := blockWidth M w
  set Dv := DF M.k (4 * V - 1) (ε / (4 * β * max c 1)) * ⌈4 * β * max c 1 / ε⌉₊
  set D := Dv - 1
  set B := ∑ h ∈ range (D + 1), (M.k + 1) ^ h
  set ϑ := ⌈((w * B : ℕ) : ℝ) / δ⌉₊
  have hϑ : ((w * B : ℕ) : ℝ) / δ ≤ ϑ := Nat.le_ceil _
  obtain ⟨d₁, hd₁⟩ := skel_uniform_binary hQ M.k hw hc.le hδ hδ1 hϑ (ζ := η / 8) (by positivity)
  set A₁ : ℝ := 2 * c * (w * B : ℕ) * ((M.k + 2) * (2 * w - 1) : ℕ) *
    (((M.k + 2) * (2 * w - 1) : ℕ) + 1) + 3
  have hlogt : Tendsto (fun d : ℕ => A₁ / Real.logb 2 d) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop ((Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp
      tendsto_natCast_atTop_atTop)
  obtain ⟨d₂, hd₂⟩ := eventually_atTop.mp ((tendsto_order.mp hlogt).2 (η / 4) (by positivity))
  refine ⟨max (max d₁ d₂) (2 * w), fun d hd b hb σ hcard htr hentry => ?_⟩
  have hdw : 2 * w ≤ d := le_of_max_le_right hd
  have hd2 : 2 ≤ d := by omega
  have hdbw : 2 * w - 1 ≤ d * b := by
    have := Nat.mul_le_mul hdw hb
    omega
  have hL : 1 ≤ d * d * b := Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) hb
  have hLr : (0 : ℝ) < (d * d * b : ℕ) := by exact_mod_cast hL
  obtain ⟨X₀, hX₀, hV₀⟩ := hentry
  have hx : InClass M w σ (List.ofFn X₀) := hX₀
  -- the halting time is at most `c (L + 1)`
  have hT : (σ.T : ℝ) ≤ c * ((d * d * b : ℕ) + 1) := by
    obtain ⟨s, hs, hhs⟩ := (htr X₀ hX₀).halts
    obtain rfl := Transpose.Tape.Impl.haltsAt_unique hhs hx.1
    exact (Nat.cast_le.mpr hs).trans (Nat.floor_le (by positivity))
  -- the genie of Lemma 4.6
  obtain ⟨Γ, hcost, hpath⟩ := skeleton_genie hk hV hw0 hL hε σ hT
    ⟨List.ofFn X₀, hx, hV₀⟩
  have hsub1 : ∀ n : ℕ, n ≤ n - 1 + 1 := fun n => by omega
  have hpath' : ∀ π, IsDepPath σ.s σ.T π → LinNet.GFree Γ π → π.length ≤ D + 1 :=
    fun π hπ hfree => (hpath π hπ hfree).trans (hsub1 _)
  -- a large fibre of the revealed word
  set S := univ.filter fun X : Fin (d * d * b) → Bool => X ∈ skelClass M w (d * d * b) σ
  set E := fun X : Fin (d * d * b) → Bool => fun u : Γ => blockVal M w (List.ofFn X) u
  have himg : (S.image E).card ≤ 2 ^ (β * Γ.card) := card_revealed_le (M := M) hw0 Γ S
  have hSpos : (0 : ℝ) < S.card := lt_of_lt_of_le (by positivity) hcard
  have hSne : (S.image E).Nonempty := by
    obtain ⟨X, hX⟩ := card_pos.mp (by exact_mod_cast hSpos : 0 < S.card)
    exact ⟨E X, mem_image_of_mem E hX⟩
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ (β * Γ.card) := by positivity
  obtain ⟨e, he, hfib⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    (s := S) (t := S.image E) (f := E) (b := (S.card : ℝ) / (2 : ℝ) ^ (β * Γ.card))
    (fun X hX => mem_image_of_mem E hX) hSne (by
      rw [nsmul_eq_mul, mul_div_assoc']
      rw [div_le_iff₀ h2pos]
      have : ((S.image E).card : ℝ) ≤ (2 : ℝ) ^ (β * Γ.card) := by exact_mod_cast himg
      nlinarith)
  obtain ⟨X₁, hX₁, rfl⟩ := mem_image.mp he
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
  -- `W` is a storage code for the class relation, which lies inside a cone relation
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
  obtain ⟨hdepthR, hotR, hNsub⟩ := classRel_subset_coneRel hw0 hb hX₀ hlenX₀ hpath'
  have hTR : (σ.T : ℝ) ≤ c * (d * d * b + 1) := by
    have := hT
    push_cast at this
    exact this
  -- Lemma 4.12 on the retained coordinates, and paid conditioning
  have hcode := hd₁ d (le_trans (le_max_left _ _) (le_of_max_le_left hd)) b hb
    (runWalks M (List.ofFn X₀)) (runWalks_isWalk M _) σ.T Γ hdepthR (outTime σ w) hotR hTR NJ
    hNsub
  have hcond := logb_card_le_of_conditioning (by simp) hWJ (skelRetained NJ ϑ) hcode
  rw [Fintype.card_bool, Nat.cast_ofNat] at hcond
  have hinst : SkelInst M.k w D c ϑ d b (skelRetained NJ ϑ) NJ :=
    ⟨hb, ⟨runWalks M (List.ofFn X₀), σ.T, Γ, outTime σ w, runWalks_isWalk M _, hdepthR, hotR, hTR,
      hNsub⟩, rfl⟩
  have hcompl := skelInst_compl M.k hw hc.le hδ hϑ hd2 hdbw _ _ hinst
  have h2 : ((skelRetained NJ ϑ).card : ℝ) + ((skelRetained NJ ϑ)ᶜ).card = (d * d * b : ℕ) := by
    rw [← Nat.cast_add, Finset.card_add_card_compl, Fintype.card_fin]
  have h3 := conditioning_arith (L := ((d * d * b : ℕ) : ℝ)) (by positivity : (0 : ℝ) ≤ η / 8)
    (Nat.cast_nonneg ((skelRetained NJ ϑ)ᶜ.card)) h2
  -- `A₁ L/log₂ d < η L/4`
  have hlog : 0 < Real.logb 2 d := Real.logb_pos (by norm_num) (by exact_mod_cast hd2)
  have hA : A₁ * ((d * d * b : ℕ) / Real.logb 2 d) < η / 4 * (d * d * b : ℕ) := by
    have h4 := hd₂ d (le_trans (le_max_right _ _) (le_of_max_le_left hd))
    rw [div_lt_iff₀ hlog] at h4
    rw [← mul_div_assoc, div_lt_iff₀ hlog]
    nlinarith
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
  -- the contradiction
  have hδL : δ * (d * d * b : ℕ) ≤ η / 2 * (d * d * b : ℕ) := mul_le_mul_of_nonneg_right hδη hLr.le
  nlinarith

/-- The skeleton of a run is normalized. -/
theorem runSkeleton_normalize {M : TM} {w : ℕ} (x : List Bool) :
    (runSkeleton M w x).normalize = runSkeleton M w x := by
  simp only [Skeleton.normalize, runSkeleton, Skeleton.mk.injEq, true_and]
  refine ⟨funext fun t => ?_, funext fun j => funext fun t => ?_, funext fun t => ?_⟩ <;>
    split_ifs <;> rfl

open Classical in
/-- **Theorem SE, given binary [Q9.1].** Let `M` have `k ≥ 1` work tapes, `V, w ≥ 1`, `c > 0` and
`η > 0`. There is `d₀` such that for `d ≥ d₀` and every width `b ≥ 1`: if (i) `M` transposes every
input `X ∈ {0,1}^L` within `c (L + 1)` steps and (ii) on every input every work-tape cell is entered
at most `V` times before the halting time, then (iii) fails: `H(σ_w(X)) > (1/2 - η) L` for a
uniformly random input. -/
theorem thm_SE (hQ : Q91Binary) {M : TM} (hk : 1 ≤ M.k) {V w : ℕ} (hV : 1 ≤ V) (hw : 1 ≤ w)
    {c η : ℝ} (hc : 0 < c) (hη : 0 < η) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ b, 1 ≤ b →
      (∀ X : Fin (d * d * b) → Bool, TransposesInput M d b c X) →
      (∀ (X : Fin (d * d * b) → Bool) (T : ℕ), Transpose.Tape.HaltsAt M (List.ofFn X) T →
        ∀ j cell, (entries (workWalk M (List.ofFn X) j) cell (T - 1)).card ≤ V) →
      (1 / 2 - η) * (d * d * b : ℕ) <
        entropy (fun X : Fin (d * d * b) → Bool => runSkeleton M w (List.ofFn X)) := by
  obtain ⟨d₀, hd₀⟩ := thm_SE_class hQ hk hV hw hc hη
  refine ⟨d₀, fun d hd b hb htr hentry => ?_⟩
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
  have hX₀c := hmem X₀ hfX₀
  exact hd₀ d hd b hb σ₀ hcard (fun X _ => htr X)
    ⟨X₀, hX₀c, fun j cell => hentry X₀ σ₀.T hX₀c.1 j cell⟩

end MergeDepth
