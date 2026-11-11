import BoundedArityDecoders.DiagnosisAndBarriers
import BoundedStackDepth.Machines
import TapeStorageRates.TraceTransfer
import MergeDepth.HCStarQ91
import DirectedRecovery.StorageCode
import LeanMachine.LinearRecovery
import LeanMachine.BlockRankSparsity
import LeanMachine.BinomialTail
import LeanMachine.OddPowerChoice
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.PiTensorProduct.Finite
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Combinatorics.SimpleGraph.Walk.Operations

/-!
# Proofs for Section I Diagnosis, Prior Spine Benchmarks & Machine-Level Controls

Complete kernel-verified proofs of all seven claim specifications in
`BoundedArityDecoders/DiagnosisAndBarriers.lean`.
-/

namespace BoundedArityDecoders

open SharedDecoders Module
open scoped BigOperators TensorProduct

/-! ### Helper lemmas for Diagnosis 1 -/

private theorem exists_large_obs_fibre {X Y : Type*} [DecidableEq Y] {S : Finset X}
    (hne : S.Nonempty) (f : X → Y) :
    ∃ y ∈ S.image f, S.card ≤ (S.image f).card * (S.filter (fun x => f x = y)).card := by
  obtain ⟨y, hy, hmax⟩ := Finset.exists_max_image (S.image f)
    (fun a => (S.filter (fun x => f x = a)).card) (hne.image f)
  refine ⟨y, hy, ?_⟩
  calc
    S.card = ∑ a ∈ S.image f, (S.filter (fun x => f x = a)).card :=
      Finset.card_eq_sum_card_fiberwise (fun _ hx => Finset.mem_image_of_mem f hx)
    _ ≤ ∑ _a ∈ S.image f, (S.filter (fun x => f x = y)).card :=
      Finset.sum_le_sum hmax
    _ = _ := by simp

private theorem log_card_pay {m a n : ℕ} (hm : 0 < m) (ha : 0 < a) (hn : 0 < n)
    (h : m ≤ a * n) : Real.logb 2 m ≤ Real.logb 2 a + Real.logb 2 n := by
  have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by exact_mod_cast hm : (0 : ℝ) < m) (by exact_mod_cast h : (m : ℝ) ≤ (a : ℝ) * n)
  rwa [Real.logb_mul (by positivity) (by positivity)] at hh

section NativeFibrePullback

open Finset Filter Transpose Transpose.Tape Transpose.Tape.Impl
open MergeDepth BoundedNesting BoundedStackDepth MotionDepthCodes TapeStorageRates

private structure LocalNativeFibre (M : TM) (d b : ℕ) (c η ε : ℝ) where
  representative : Fin (d * d * b) → Bool
  time : ℕ
  genie : Finset ℕ
  depth : ∀ π, IsDepPath (fun j => skel 1 (runWalks M (List.ofFn representative)
    (some (some j)))) time π → LinNet.GFree genie π →
    π.length ≤ genieDepth M.k (blockWidth M 1) (max c 1) ε + 1
  outputTime : ℕ → ℕ
  code : Finset (Fin (d * d * b) → Bool)
  representative_mem : representative ∈ code
  storage : IsStorageCode (coneRel 1 (runWalks M (List.ofFn representative)) time genie
    outputTime (fun q => MergeDepth.tpos d b q)) code
  code_size : (1 - η - ε) * (d * d * b : ℕ) ≤ Real.logb 2 code.card

private theorem local_inClass_of_trace_eq {M : TM} {d b : ℕ} {c : ℝ} {x y : Fin (d * d * b) → Bool}
    (hx : TransposesInput M d b c x) (htr : trace M (List.ofFn x) = trace M (List.ofFn y)) :
    InClass M 1 (runSkeleton M 1 (List.ofFn y)) (List.ofFn x) := by
  rw [inClass_iff_runSkeleton, runSkeleton_normalize]
  obtain ⟨t, _, ht⟩ := hx.halts
  exact ⟨⟨t, ht⟩, by simpa only [skeletonOfTrace_eq] using congrArg (skeletonOfTrace 1) htr⟩

private theorem local_class_time {M : TM} {d b : ℕ} {c : ℝ} {σ : Skeleton M.k} (hc : 0 ≤ c)
    {x : Fin (d * d * b) → Bool} (hx : InClass M 1 σ (List.ofFn x)) (hgood : TransposesInput M d b c x) :
    (σ.T : ℝ) ≤ c * ((d * d * b : ℕ) + 1) := by
  obtain ⟨t, ht, halt⟩ := hgood.halts
  obtain rfl := haltsAt_unique halt hx.1
  exact (Nat.cast_le.mpr ht).trans (Nat.floor_le (by positivity))

private theorem local_class_output {M : TM} {d b : ℕ} {σ : Skeleton M.k} {x : Fin (d * d * b) → Bool}
    (hx : InClass M 1 σ (List.ofFn x)) (hgood : OutputsTranspose M d b x) :
    (run M (List.ofFn x) σ.T).outRev.length = d * d * b ∧
      ∀ q : Fin (d * d * b),
        (run M (List.ofFn x) σ.T).outRev.reverse[MergeDepth.tpos d b q]? = some (x q) := by
  obtain ⟨t, halt, hlen, hout⟩ := hgood.output
  obtain rfl := haltsAt_unique halt hx.1
  exact ⟨by simpa using hlen, by simpa only [tape_tpos_eq] using hout⟩

private theorem local_class_decode {M : TM} {d b : ℕ} (hb : 0 < b) {σ : Skeleton M.k} {Γ : Finset ℕ}
    {x y : Fin (d * d * b) → Bool} (hx : InClass M 1 σ (List.ofFn x))
    (hy : InClass M 1 σ (List.ofFn y)) (gx : OutputsTranspose M d b x) (gy : OutputsTranspose M d b y)
    (hΓ : ∀ t ∈ Γ, blockVal M 1 (List.ofFn x) t = blockVal M 1 (List.ofFn y) t)
    (q : Fin (d * d * b)) (hJ : ∀ u ∈ (blockMachine M (by decide : 0 < 1) _ σ).coneJ Γ
      (outTime σ 1 (MergeDepth.tpos d b q)), x u = y u) : x q = y q := by
  obtain ⟨lx, vx⟩ := local_class_output hx gx
  obtain ⟨ly, vy⟩ := local_class_output hy gy
  have hq := MergeDepth.tpos_lt hb q.isLt
  have h := blockMachine_output_eq (by decide : 0 < 1) σ Γ (mem_skelClass.mpr hx)
    (mem_skelClass.mpr hy) (fun t ht _ => hΓ t ht) (hq.trans_le lx.ge) (hq.trans_le ly.ge) hJ
  exact Option.some.inj ((vx q).symm.trans (h.trans (vy q)))

private theorem local_class_genie {M : TM} {σ : Skeleton M.k} {w : List Bool}
    (hclass : InClass M 1 σ w) {L : ℕ} (hlen : 0 < L) {c ε : ℝ}
    (hT : (σ.T : ℝ) ≤ c * ((L : ℝ) + 1)) (hε : 0 < ε) :
    ∃ Γ : Finset ℕ, (blockWidth M 1 * Γ.card : ℝ) ≤ ε * L ∧
      ∀ π, IsDepPath σ.s σ.T π → LinNet.GFree Γ π →
        π.length ≤ genieDepth M.k (blockWidth M 1) (max c 1) ε + 1 := by
  have htime := hT.trans (mul_le_mul_of_nonneg_right (le_max_left c 1) (by positivity))
  obtain ⟨Γ, hcost, hdepth⟩ := genie_cost (k := M.k) (one_le_blockWidth M 1) hlen
    (le_max_right c 1) hε htime (fun j => skel 1 (workWalk M w j))
    (fun j => isWalk_skel (by decide : (0 : ℤ) < 1) (workWalk_isWalk _ j))
  have hagree : ∀ j t, t < σ.T → σ.s j t = skel 1 (workWalk M w j) t :=
    fun j t ht => ((hclass.2 t ht).2.1 j).symm
  exact ⟨Γ, hcost, fun π hπ hf => (hdepth π ((isDepPath_congr hagree π).mp hπ) hf).trans
    (Nat.le_succ _)⟩

open Classical in
private theorem local_native_fibre_of_trace_support (M : TM) {d b : ℕ} (hd : 0 < d) (hb : 0 < b)
    {c η ε : ℝ} (hc : 0 < c) (hε : 0 < ε) (hgood : TransposesAtWidth M d b c)
    (hsupport : Real.logb 2 (univ.image (fun x : Fin (d * d * b) → Bool => trace M (List.ofFn x))).card
      ≤ η * (d * d * b : ℕ)) : Nonempty (LocalNativeFibre M d b c η ε) := by
  let L := d * d * b
  let β := blockWidth M 1
  let tr (x : Fin L → Bool) := trace M (List.ofFn x)
  obtain ⟨τ, hτ, hS⟩ := exists_large_obs_fibre (S := (univ : Finset (Fin L → Bool)))
    univ_nonempty tr
  obtain ⟨x₀, _, rfl⟩ := mem_image.mp hτ
  let S := univ.filter (fun x => tr x = tr x₀)
  have hx₀ : x₀ ∈ S := mem_filter.mpr ⟨mem_univ _, rfl⟩
  have hSne : S.Nonempty := ⟨_, hx₀⟩
  have hpay₁ := log_card_pay (univ_nonempty.card_pos (α := Fin L → Bool))
    (univ_nonempty.image tr).card_pos hSne.card_pos hS
  have hScard : (1 - η) * (L : ℝ) ≤ Real.logb 2 S.card := by
    simp only [card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, Nat.cast_pow,
      Nat.cast_ofNat, Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at hpay₁
    change _ ≤ η * (L : ℝ) at hsupport
    change (L : ℝ) ≤ Real.logb 2 (univ.image tr).card + Real.logb 2 S.card at hpay₁
    linarith
  let σ := runSkeleton M 1 (List.ofFn x₀)
  have hσ {x} (hx : x ∈ S) : InClass M 1 σ (List.ofFn x) :=
    local_inClass_of_trace_eq (hgood.transposesInput x) (mem_filter.mp hx).2
  have hclass := hσ hx₀
  have hT := local_class_time hc.le hclass (hgood.transposesInput x₀)
  have hlen : 0 < L := Nat.mul_pos (Nat.mul_pos hd hd) hb
  obtain ⟨Γ, hcost, hpath⟩ := local_class_genie hclass hlen hT hε
  let E (x : Fin L → Bool) := fun t : Γ => blockVal M 1 (List.ofFn x) t
  have hcap : (S.image E).card ≤ 2 ^ (β * Γ.card) := card_revealed_le (M := M) (by decide : 0 < 1) Γ S
  obtain ⟨e, he, hF⟩ := exists_large_obs_fibre hSne E
  obtain ⟨x₁, hx₁, rfl⟩ := mem_image.mp he
  let F := S.filter (fun x => E x = E x₁)
  have hx₁F : x₁ ∈ F := mem_filter.mpr ⟨hx₁, rfl⟩
  have hcostlog : Real.logb 2 (S.image E).card ≤ ε * L := by
    have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by exact_mod_cast (hSne.image E).card_pos : (0 : ℝ) < (S.image E).card)
      (by exact_mod_cast hcap : ((S.image E).card : ℝ) ≤ ((2 ^ (β * Γ.card) : ℕ) : ℝ))
    simp only [Nat.cast_pow, Nat.cast_ofNat, Real.logb_pow,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one, Nat.cast_mul] at hh
    exact hh.trans hcost
  have hfsize := log_card_pay hSne.card_pos (hSne.image E).card_pos
    (show F.Nonempty from ⟨_, hx₁F⟩).card_pos hF
  have hFc : (1 - η - ε) * (L : ℝ) ≤ Real.logb 2 F.card := by linarith
  have hctx := hσ hx₁
  have hcomplete {x} (hx : x ∈ S) :=
    (local_class_output (hσ hx) (hgood.transposesInput x).outputsTranspose).1.ge
  obtain ⟨hdepthR, _, hcone⟩ := classRel_subset_coneRel (by decide : 0 < 1) hb
    (mem_skelClass.mpr hctx) (hcomplete hx₁) hpath
  refine ⟨{
    representative := x₁, time := σ.T, genie := Γ, depth := hdepthR, outputTime := outTime σ 1,
    code := F, representative_mem := hx₁F,
    storage := fun x hx y hy q hxy =>
      local_class_decode hb (hσ (mem_filter.mp hx).1) (hσ (mem_filter.mp hy).1)
        (hgood.transposesInput x).outputsTranspose (hgood.transposesInput y).outputsTranspose
        (fun t ht => congrFun ((mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm) ⟨t, ht⟩)
        q (fun u hu => hxy u (hcone q hu)),
    code_size := hFc }⟩

private theorem local_aligned_native_fibres (M : TM) {c η ε : ℝ} (hc : 0 < c)
    (hη : 0 < η) (hε : 0 < ε) :
    ∃ s : ℕ, ∃ hs : 0 < s, ∃ c' : ℝ, 0 < c' ∧ ∀ᶠ d : ℕ in atTop,
      TransposesAt M d c →
        Nonempty (LocalNativeFibre (Native.machine M hs) d (entryBits d) c' η ε) := by
  obtain ⟨s, hs, h⟩ := aligned_low_trace_dimensions M hc.le hη
  have ht : 0 < 11 * c + 1 := by positivity
  refine ⟨s, hs, 11 * c + 1, ht, ?_⟩
  filter_upwards [h, eventually_ge_atTop 1] with d hd hpos
  intro hgood
  obtain ⟨htr, hcount⟩ := hd (entryBits d) (one_le_entryBits d) hgood
  exact local_native_fibre_of_trace_support _ hpos (one_le_entryBits d) ht hε htr hcount

end NativeFibrePullback

private theorem sum_pow_succ_le_pow {k : ℕ} (hk : 1 ≤ k) :
    ∀ D : ℕ, ∑ h ∈ Finset.range D, (k + 1) ^ h ≤ (k + 1) ^ D
  | 0 => by simp
  | D + 1 => by
    rw [Finset.sum_range_succ, pow_succ]
    have ih := sum_pow_succ_le_pow hk D
    have hmul : (k + 1) ^ D * (k + 1) = (k + 1) ^ D * k + (k + 1) ^ D := by ring
    rw [hmul]
    have h1 : ∑ h ∈ Finset.range D, (k + 1) ^ h ≤ (k + 1) ^ D * k :=
      ih.trans (Nat.le_mul_of_pos_right _ (by omega))
    omega

private theorem tmDepStep_iff_blockStep {k : ℕ} (workPos : ℕ → Fin k → Int) (T u v : ℕ) :
    TMDepStep workPos T u v ↔ MergeDepth.BlockStep (fun h t => workPos t h) T v u := by
  unfold TMDepStep MergeDepth.BlockStep IsLastWorkVisit
  refine and_congr_right fun _ => or_congr ⟨fun h => by omega, fun h => by omega⟩
    (exists_congr fun h => ?_)
  rw [MergeDepth.prevS_spec]

private theorem tmDepStep_lt {k : ℕ} {workPos : ℕ → Fin k → Int} {T u v : ℕ}
    (h : TMDepStep workPos T u v) : u < v ∧ v < T := by
  have hb := (MergeDepth.blockStep_iff (fun h t => workPos t h) T v u).mp
    ((tmDepStep_iff_blockStep workPos T u v).mp h)
  exact MergeDepth.depStep_lt hb

private theorem cutFree_to_depPath {k : ℕ} {workPos : ℕ → Fin k → Int} {T : ℕ}
    {Γ₀ : Finset ℕ} :
    ∀ π : List ℕ, IsCutFreeCausalPath workPos T (Γ₀.filter (· < T)) π →
      MergeDepth.IsDepPath (fun h t => workPos t h) T π ∧ BoundedNesting.LinNet.GFree Γ₀ π
  | [], _ => ⟨trivial, fun _ hv => by simp at hv⟩
  | [_], _ => ⟨trivial, fun _ hv => by simp at hv⟩
  | v :: u :: rest, ⟨hstep, huΓ, hrest⟩ => by
    obtain ⟨hudep, hufree⟩ := cutFree_to_depPath (u :: rest) hrest
    obtain ⟨huv, hvT⟩ := tmDepStep_lt hstep
    have huT : u < T := Nat.lt_trans huv hvT
    have hu0 : u ∉ Γ₀ := fun hm => huΓ (Finset.mem_filter.mpr ⟨hm, huT⟩)
    have hdep : MergeDepth.DepStep (fun h t => workPos t h) T v u :=
      (MergeDepth.blockStep_iff (fun h t => workPos t h) T v u).mp
        ((tmDepStep_iff_blockStep workPos T u v).mp hstep)
    exact ⟨⟨hdep, hudep⟩, (MergeDepth.gfree_cons_cons).mpr ⟨hu0, hufree⟩⟩

open Classical in
private noncomputable def tmCausalLinNet {k : ℕ} (workPos : ℕ → Fin k → Int) (T : ℕ) :
    BoundedNesting.LinNet ℚ 1 1 where
  out v := (Finset.range T).filter (fun u => MergeDepth.BlockStep (fun h t => workPos t h) T v u)
  out_lt v u hu := by
    have hb := (Finset.mem_filter.mp hu).2
    have hd := (MergeDepth.blockStep_iff (fun h t => workPos t h) T v u).mp hb
    exact (MergeDepth.depStep_lt hd).1
  c := fun _ => 0
  A := fun _ _ => 0
  a := fun _ => 0
  rd := fun _ => none

open Classical in
private theorem cutFree_mem_paths {k : ℕ} (workPos : ℕ → Fin k → Int) (T : ℕ) (Γ : Finset ℕ) :
    ∀ (π : List ℕ) (v : ℕ),
      π.head? = some v →
      IsCutFreeCausalPath workPos T Γ π →
      π ∈ (tmCausalLinNet workPos T).paths v ∧ BoundedNesting.LinNet.GFree Γ π
  | [], _, hhead, _ => by simp at hhead
  | [w], v, hhead, _ => by
    simp only [List.head?_cons, Option.some.injEq] at hhead
    subst hhead
    exact ⟨MergeDepth.singleton_mem_paths _ _, MergeDepth.gfree_singleton _ _⟩
  | w :: u :: rest, v, hhead, ⟨hstep, huΓ, hrest⟩ => by
    simp only [List.head?_cons, Option.some.injEq] at hhead
    subst hhead
    obtain ⟨hupaths, hufree⟩ := cutFree_mem_paths workPos T Γ (u :: rest) u rfl hrest
    obtain ⟨huv, hvT⟩ := tmDepStep_lt hstep
    have huT : u < T := Nat.lt_trans huv hvT
    have hout : u ∈ (tmCausalLinNet workPos T).out w := by
      dsimp only [tmCausalLinNet]
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr huT,
        (tmDepStep_iff_blockStep workPos T u w).mp hstep⟩
    exact ⟨(MergeDepth.cons_cons_mem_paths).mpr ⟨hout, hupaths⟩,
      (MergeDepth.gfree_cons_cons).mpr ⟨huΓ, hufree⟩⟩

private theorem getLastD_eq_of_getLast_some :
    ∀ (π : List ℕ) (d u : ℕ), π.getLast? = some u → π.getLastD d = u
  | [], _, _, h => by simp at h
  | [x], _, u, h => by
    simp only [List.getLast?_singleton, Option.some.injEq] at h
    subst h; rfl
  | x :: y :: rest, d, u, h => by
    rw [List.getLastD_cons]
    exact getLastD_eq_of_getLast_some (y :: rest) x u (by simpa using h)

private def flatBitsToStateEquiv (d b : ℕ) [NeZero d] (hb : 0 < b) :
    (Fin (d * d * b) → Bool) ≃ State d (Fin b → Bool) where
  toFun x i j ℓ :=
    x ⟨(ZMod.val i * d + ZMod.val j) * b + ℓ.val, by
      have hd : 0 < d := NeZero.pos d
      have hi : ZMod.val i < d := ZMod.val_lt i
      have hj : ZMod.val j < d := ZMod.val_lt j
      have h1 : ZMod.val i * d + ZMod.val j < d * d := by
        calc ZMod.val i * d + ZMod.val j < ZMod.val i * d + d := Nat.add_lt_add_left hj _
          _ = (ZMod.val i + 1) * d := by ring
          _ ≤ d * d := Nat.mul_le_mul_right d (by omega)
      calc (ZMod.val i * d + ZMod.val j) * b + ℓ.val
          < (ZMod.val i * d + ZMod.val j) * b + b := Nat.add_lt_add_left ℓ.isLt _
        _ = (ZMod.val i * d + ZMod.val j + 1) * b := by ring
        _ ≤ (d * d) * b := Nat.mul_le_mul_right b (by omega)⟩
  invFun X p :=
    X ((p.val / b / d : ℕ) : ZMod d) ((p.val / b % d : ℕ) : ZMod d) ⟨p.val % b, Nat.mod_lt _ hb⟩
  left_inv x := by
    funext p
    obtain ⟨hi, hj, _, hdec⟩ := Transpose.Tape.Impl.pos_decomp p.isLt
    dsimp only
    congr 1
    apply Fin.ext
    simp only [ZMod.val_natCast_of_lt hi, ZMod.val_natCast_of_lt hj]
    exact hdec.symm
  right_inv X := by
    funext i j ℓ
    have hd : 0 < d := NeZero.pos d
    have hj : ZMod.val j < d := ZMod.val_lt j
    set pos := (ZMod.val i * d + ZMod.val j) * b + ℓ.val
    have hdivb : pos / b = ZMod.val i * d + ZMod.val j := by
      dsimp [pos]
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hb, Nat.div_eq_of_lt ℓ.isLt, zero_add]
    have hmodb : pos % b = ℓ.val := by
      dsimp [pos]
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ℓ.isLt]
    have hdivd : (ZMod.val i * d + ZMod.val j) / d = ZMod.val i := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hd, Nat.div_eq_of_lt hj, zero_add]
    have hmodd : (ZMod.val i * d + ZMod.val j) % d = ZMod.val j := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
    change X ((pos / b / d : ℕ) : ZMod d) ((pos / b % d : ℕ) : ZMod d) ⟨pos % b, _⟩ = X i j ℓ
    rw [hdivb, hdivd, hmodd, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    congr 1
    exact Fin.ext hmodb

theorem diagnosis_TCPAndAdaptiveConeReduction : Diagnosis_TCPAndAdaptiveConeReductionSpec := by
  constructor
  · -- Part 1: Paper 14 `BoundedStackDepth.genie`
    intro k ε hk hε
    let ε' : ℝ := ε / 2
    have hε' : 0 < ε' := by dsimp [ε']; linarith
    let R : ℕ := max 1 ⌈2 / ε⌉₊
    have hR : 1 ≤ R := le_max_left _ _
    let D : ℕ := max 1 (BoundedStackDepth.parK k ε' ^ BoundedStackDepth.parP k ε' * R)
    refine ⟨D, le_max_left _ _, fun T workPos hwalk => ?_⟩
    by_cases hT0 : T = 0
    · subst hT0
      refine ⟨∅, by simp, by simp, ?_, fun v hv => absurd hv (Nat.not_lt_zero _)⟩
      intro π hπ
      cases π with
      | nil => simp [D]
      | cons v rest =>
        cases rest with
        | nil => simp [IsCutFreeCausalPath] at hπ
        | cons u rest' => exact absurd (tmDepStep_lt hπ.1).2 (Nat.not_lt_zero _)
    · let xs : Fin k → ℕ → ℤ := fun h t => workPos t h
      have hxs : ∀ h, BoundedNesting.IsWalk (xs h) := fun h t => hwalk t h
      obtain ⟨Γ₀, hcard₀, hpath₀⟩ := BoundedStackDepth.genie k hε' hR xs hxs T
      let Γ := Γ₀.filter (· < T)
      have hΓ_lt : ∀ u ∈ Γ, u < T := fun u hu => (Finset.mem_filter.mp hu).2
      have hΓ_card : (Γ.card : ℝ) ≤ ε * (T : ℝ) := by
        have hc1 : (Γ.card : ℝ) ≤ (Γ₀.card : ℝ) :=
          Nat.cast_le.mpr (Finset.card_filter_le _ _)
        have hRpos : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hR
        have hRceil : 2 / ε ≤ (R : ℝ) :=
          (Nat.le_ceil (2 / ε)).trans (by exact_mod_cast le_max_right 1 ⌈2 / ε⌉₊)
        have hTR : (T : ℝ) ≤ (R : ℝ) * (ε / 2) * (T : ℝ) := by
          have h2 : 2 ≤ (R : ℝ) * ε := (div_le_iff₀ hε).mp hRceil
          have hTnn : (0 : ℝ) ≤ (T : ℝ) := Nat.cast_nonneg T
          nlinarith
        have hRΓ : (R : ℝ) * (Γ₀.card : ℝ) ≤ (R : ℝ) * ε * (T : ℝ) := by
          dsimp [ε'] at hcard₀
          linarith
        have hΓ0 : (Γ₀.card : ℝ) ≤ ε * (T : ℝ) :=
          le_of_mul_le_mul_left (by linarith) hRpos
        exact hc1.trans hΓ0
      have hΓ_depth : ∀ π : List ℕ, IsCutFreeCausalPath workPos T Γ π → π.length ≤ D := by
        intro π hπ
        obtain ⟨hdep, hfree⟩ := cutFree_to_depPath π hπ
        exact (hpath₀ π hdep hfree).trans (le_max_right _ _)
      refine ⟨Γ, hΓ_lt, hΓ_card, hΓ_depth, fun v hv => ?_⟩
      classical
      let net := tmCausalLinNet workPos T
      refine ⟨MergeDepth.coneV net Γ v, ?_, ?_⟩
      · have hdeg : ∀ u, (net.out u).card ≤ k + 1 := fun u => by
          dsimp only [net, tmCausalLinNet]
          convert MergeDepth.card_blockOut_le xs T u
        have hD1 : D = (D - 1) + 1 := (Nat.sub_add_cancel (le_max_left _ _)).symm
        have hnetD : ∀ π ∈ net.paths v, BoundedNesting.LinNet.GFree Γ π →
            π.length ≤ (D - 1) + 1 := by
          intro π hπ hfree
          have hconv : ∀ (w : ℕ) (ρ : List ℕ), w < T → ρ ∈ net.paths w →
              BoundedNesting.LinNet.GFree Γ ρ → IsCutFreeCausalPath workPos T Γ ρ := by
            intro w ρ
            induction ρ generalizing w with
            | nil => intros; trivial
            | cons a rest ih =>
              intro hwT hρ hfr
              have ha := MergeDepth.head_eq_of_mem_paths hρ
              rw [ha] at hρ hfr ⊢
              cases rest with
              | nil => exact hwT
              | cons b rest' =>
                obtain ⟨hbout, hbrest⟩ := (MergeDepth.cons_cons_mem_paths).mp hρ
                obtain ⟨hbΓ, hfr'⟩ := (MergeDepth.gfree_cons_cons).mp hfr
                dsimp only [net, tmCausalLinNet] at hbout
                obtain ⟨hbT_mem, hb_blk⟩ := Finset.mem_filter.mp hbout
                have hbT : b < T := Finset.mem_range.mp hbT_mem
                have hbstep : TMDepStep workPos T b w :=
                  (tmDepStep_iff_blockStep workPos T b w).mpr hb_blk
                exact ⟨hbstep, hbΓ, ih b hbT hbrest hfr'⟩
          rw [← hD1]
          exact hΓ_depth π (hconv v π hv hπ hfree)
        have hcardV := MergeDepth.card_coneV_le net hdeg hnetD
        rw [← hD1] at hcardV
        exact hcardV.trans (sum_pow_succ_le_pow hk D)
      · intro u _ hcone
        obtain ⟨π, hhead, hlast, hcut⟩ := hcone
        obtain ⟨hpaths, hfree⟩ := cutFree_mem_paths workPos T Γ π v hhead hcut
        exact (MergeDepth.mem_coneV net).mpr
          ⟨π, hpaths, hfree, getLastD_eq_of_getLast_some π v u hlast⟩
  · -- Part 2: Adaptive aligned simulator cut-cone pullback
    intro M c₀ ε hk hε0 hε1 hM
    have hM' : Transpose.TransposesWithin M (fun L => (c₀ + 1) * (L + 1)) := by
      intro n hn A
      obtain ⟨s, hs, cfg, hstep, hhalt, hout⟩ := hM n hn A
      exact ⟨s, hs.trans (by nlinarith), cfg, hstep, hhalt, hout⟩
    have hcpos : (0 : ℝ) < ((c₀ + 1 : ℕ) : ℝ) := by positivity
    have hε2 : 0 < ε / 2 := by linarith
    obtain ⟨s, hs, c', _, hev⟩ :=
      local_aligned_native_fibres M hcpos hε2 hε2
    obtain ⟨D₀, hD₀⟩ := Filter.eventually_atTop.mp hev
    let N := TapeStorageRates.Native.machine M hs
    let D_genie := BoundedStackDepth.genieDepth N.k (MergeDepth.blockWidth N 1) (max c' 1) (ε / 2)
    let D := D_genie + 1
    refine ⟨D, D₀, Nat.succ_pos _, fun d _ hd => ?_⟩
    classical
    have hdD₀ : D₀ ≤ d := (le_max_left D₀ 2).trans hd
    have hd1 : 1 ≤ d := (show 1 ≤ 2 by decide).trans ((le_max_right D₀ 2).trans hd)
    have htr : MergeDepth.TransposesAt M d ((c₀ + 1 : ℕ) : ℝ) :=
      MergeDepth.transposesAt_of_transposesWithin hM' hd1
    obtain ⟨F⟩ := hD₀ d hdD₀ htr
    let b := Transpose.entryBits d
    have hb : 0 < b := MergeDepth.one_le_entryBits d
    let eqv := flatBitsToStateEquiv d b hb
    let C : Set (State d (CanonicalWordAlphabet d)) := eqv '' (F.code : Set (Fin (d * d * b) → Bool))
    refine ⟨C, ∅, ?_, ?_, ?_⟩
    · have hcard_eq : Nat.card C = F.code.card := by
        rw [Nat.card_image_of_injective eqv.injective, Nat.card_coe_set_eq, Set.ncard_coe_finset]
      rw [hcard_eq]
      have hne : F.code.Nonempty := ⟨F.representative, F.representative_mem⟩
      have hlog := F.code_size
      have h1 : (1 - ε / 2 - ε / 2) * ((d * d * b : ℕ) : ℝ) =
          (1 - ε) * (Transpose.inputLength d : ℝ) := by
        unfold Transpose.inputLength
        dsimp [b]
        ring
      rw [h1] at hlog
      exact (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2)
        (by exact_mod_cast hne.card_pos)).mp hlog
    · simp only [Finset.card_empty, Nat.cast_zero]
      positivity
    · intro r c ℓ _
      have hc_lt : ZMod.val c < d := ZMod.val_lt c
      have hr_lt : ZMod.val r < d := ZMod.val_lt r
      let q : Fin (d * d * b) := ⟨(ZMod.val c * d + ZMod.val r) * b + ℓ.val, by
        have h1 : ZMod.val c * d + ZMod.val r < d * d := by
          calc ZMod.val c * d + ZMod.val r < ZMod.val c * d + d := Nat.add_lt_add_left hr_lt _
            _ = (ZMod.val c + 1) * d := by ring
            _ ≤ d * d := Nat.mul_le_mul_right d (by omega)
        calc (ZMod.val c * d + ZMod.val r) * b + ℓ.val
            < (ZMod.val c * d + ZMod.val r) * b + b := Nat.add_lt_add_left ℓ.isLt _
          _ = (ZMod.val c * d + ZMod.val r + 1) * b := by ring
          _ ≤ (d * d) * b := Nat.mul_le_mul_right b (by omega)⟩
      let coneBits := MergeDepth.coneRel 1
        (MergeDepth.runWalks N (List.ofFn F.representative)) F.time F.genie
        F.outputTime (fun p => MergeDepth.tpos d b p) q
      let Q_bit : Finset (ZMod d × ZMod d) := coneBits.image fun p : Fin (d * d * b) =>
        (((p.val / b / d : ℕ) : ZMod d), ((p.val / b % d : ℕ) : ZMod d))
      refine ⟨Q_bit, ?_, ?_⟩
      · have himg : Q_bit.card ≤ coneBits.card := Finset.card_image_le
        have hcone_card : coneBits.card ≤ 1 * ∑ h ∈ Finset.range (D_genie + 1), (N.k + 1) ^ h :=
          MergeDepth.subrel_card_le (Nat.le_refl 1) F.depth (fun _ => Finset.Subset.refl _) q
        rw [one_mul] at hcone_card
        have hNk : N.k = M.k := rfl
        rw [hNk] at hcone_card
        exact (himg.trans hcone_card).trans (sum_pow_succ_le_pow hk D)
      · rintro X₁ ⟨x₁, hx₁, rfl⟩ X₂ ⟨x₂, hx₂, rfl⟩ hagree
        have hx12 : x₁ q = x₂ q := by
          apply F.storage x₁ hx₁ x₂ hx₂ q
          intro p hp
          have hpQ : (((p.val / b / d : ℕ) : ZMod d), ((p.val / b % d : ℕ) : ZMod d)) ∈ Q_bit :=
            Finset.mem_image.mpr ⟨p, hp, rfl⟩
          have hentry := hagree _ hpQ
          have hbit := congrFun hentry ⟨p.val % b, Nat.mod_lt _ hb⟩
          have hl1 := congrFun (eqv.left_inv x₁) p
          have hl2 := congrFun (eqv.left_inv x₂) p
          exact hl1.symm.trans (hbit.trans hl2)
        exact hx12

/-! ### Diagnosis 2: Odd-Majority Tensor Amplification & Numerical Threshold -/

section OddMajorityAmplification

open Finset PiTensorProduct DirectedRecovery MotionDepthCodes

private def majSign {K : Type*} [Field K] (b : Bool) : K := if b then 1 else -1

@[simp] private theorem majSign_false {K : Type*} [Field K] : majSign (K := K) false = -1 := rfl
@[simp] private theorem majSign_true {K : Type*} [Field K] : majSign (K := K) true = 1 := rfl

@[simp] private theorem majSign_not {K : Type*} [Field K] (b : Bool) :
    majSign (K := K) (!b) = -majSign (K := K) b := by
  cases b <;> simp [majSign]

private def majPosCount {m : ℕ} (σ : Fin m → Bool) : ℕ :=
  (univ.filter fun i => σ i = true).card

private def majPatternSign {K : Type*} [Field K] {m : ℕ} (σ : Fin m → Bool) : K :=
  if m < 2 * majPosCount σ then 1 else -1

private theorem majPosCount_add_not {m : ℕ} (σ : Fin m → Bool) :
    majPosCount σ + majPosCount (fun i => !σ i) = m := by
  simpa [majPosCount] using
    (card_filter_add_card_filter_not (s := (univ : Finset (Fin m))) (fun i => σ i = true))

private theorem majPatternSign_not {K : Type*} [Field K] {m : ℕ} (hm : Odd m) (σ : Fin m → Bool) :
    majPatternSign (K := K) (fun i => !σ i) = -majPatternSign (K := K) σ := by
  have hc := majPosCount_add_not σ
  obtain ⟨k, hk⟩ := hm
  by_cases h : m < 2 * majPosCount σ
  · have hn : ¬m < 2 * majPosCount (fun i => !σ i) := by omega
    simp [majPatternSign, h, hn]
  · have hn : m < 2 * majPosCount (fun i => !σ i) := by omega
    simp [majPatternSign, h, hn]

private noncomputable def majCorner {K W : Type*} [Field K] [AddCommGroup W] [Module K W] {m : ℕ}
    (A : Module.End K W) (σ : Fin m → Bool) : Module.End K (⨂[K] _ : Fin m, W) :=
  PiTensorProduct.map fun i => LinearMap.id + majSign (K := K) (σ i) • A

private noncomputable def majOperator {K W : Type*} [Field K] [AddCommGroup W] [Module K W]
    (A : Module.End K W) (m : ℕ) : Module.End K (⨂[K] _ : Fin m, W) :=
  ((2 : K) ^ m)⁻¹ • ∑ σ : Fin m → Bool, majPatternSign (K := K) σ • majCorner A σ

private theorem sum_majCorner {K W : Type*} [Field K] [AddCommGroup W] [Module K W] {m : ℕ}
    (A : Module.End K W) :
    (∑ σ : Fin m → Bool, majCorner A σ) = (2 : K) ^ m • LinearMap.id := by
  let f := PiTensorProduct.mapMultilinear K (fun _ : Fin m => W) (fun _ : Fin m => W)
  have h := f.map_sum (fun (_ : Fin m) (b : Bool) => LinearMap.id + majSign (K := K) b • A)
  have hsum : (fun _ : Fin m => ∑ b : Bool, (LinearMap.id + majSign (K := K) b • A)) =
      fun _ : Fin m => (2 : K) • (LinearMap.id : Module.End K W) := by
    funext i; ext x
    simp [majSign, two_smul, add_assoc, add_left_comm, add_comm]
  rw [hsum] at h
  change PiTensorProduct.map (fun _ : Fin m => (2 : K) • (LinearMap.id : Module.End K W)) =
      ∑ σ : Fin m → Bool, majCorner A σ at h
  rw [← h]
  ext x
  simp [MultilinearMap.map_smul_univ]

private theorem majCorner_tprod_zero {K W : Type*} [Field K] [AddCommGroup W] [Module K W] {m : ℕ}
    (A : Module.End K W) (x : Fin m → W) {S : Finset (Fin m)} (hS : m < 2 * S.card)
    (hfix : ∀ i ∈ S, A (x i) = x i) {σ : Fin m → Bool} (hσ : ¬m < 2 * majPosCount σ) :
    majCorner A σ (tprod K x) = 0 := by
  have hex : ∃ i ∈ S, σ i = false := by
    by_contra! h
    have hsub : S ⊆ univ.filter (fun i => σ i = true) := fun i hi =>
      mem_filter.mpr ⟨mem_univ _, by cases he : σ i <;> simp_all⟩
    have hc := card_le_card hsub
    unfold majPosCount at hσ
    omega
  obtain ⟨i, hi, hneg⟩ := hex
  simp only [majCorner, PiTensorProduct.map_tprod]
  apply (PiTensorProduct.tprod K).map_coord_zero i
  simp [hneg, hfix i hi]

private theorem majOperator_tprod_self {K W : Type*} [Field K] [AddCommGroup W] [Module K W] {m : ℕ}
    (A : Module.End K W) (h2 : (2 : K) ≠ 0) (x : Fin m → W) {S : Finset (Fin m)}
    (hS : m < 2 * S.card) (hfix : ∀ i ∈ S, A (x i) = x i) :
    majOperator A m (tprod K x) = tprod K x := by
  have hsum : (∑ σ : Fin m → Bool, majPatternSign (K := K) σ • majCorner A σ) (tprod K x) =
      (∑ σ : Fin m → Bool, majCorner A σ) (tprod K x) := by
    simp only [LinearMap.sum_apply, LinearMap.smul_apply]
    apply sum_congr rfl
    intro σ _
    by_cases hσ : m < 2 * majPosCount σ
    · simp [majPatternSign, hσ]
    · simp [majCorner_tprod_zero A x hS hfix hσ]
  simp only [majOperator, LinearMap.smul_apply, hsum, sum_majCorner, LinearMap.id_apply]
  simp [smul_smul, pow_ne_zero m h2]

private def majGoodIndices {ι : Type*} [Fintype ι] [DecidableEq ι] (P : Finset ι) (m : ℕ) :
    Finset (Fin m → ι) :=
  univ.filter fun p => m < 2 * (univ.filter fun i => p i ∈ P).card

private def majLeftIndices (k l : ℕ) : Finset (Fin k ⊕ Fin l) :=
  univ.map ⟨Sum.inl, Sum.inl_injective⟩

private theorem majSubspace_goodIndices_le_ker {K W : Type*} [Field K] [AddCommGroup W] [Module K W]
    [Module.Finite K W] (A : Module.End K W) (h2 : (2 : K) ≠ 0) (U : Submodule K W)
    (hfix : ∀ x ∈ U, A x = x) (n : ℕ) (hn : finrank K W = n) (m : ℕ) :
    (majGoodIndices (majLeftIndices (finrank K U) (n - finrank K U)) m).card ≤
      finrank K (LinearMap.ker (LinearMap.id - majOperator A m)) := by
  subst n
  classical
  obtain ⟨Z, hUZ⟩ := U.exists_isCompl
  have hdim := Submodule.finrank_add_eq_of_isCompl hUZ
  have hZ : finrank K Z = finrank K W - finrank K U := by omega
  let bU := Module.finBasis K U
  let bZ := Module.finBasisOfFinrankEq K Z hZ
  let b := (bU.prod bZ).map (U.prodEquivOfIsCompl Z hUZ)
  let bt := Basis.piTensorProduct (fun _ : Fin m => b)
  have : Module.Finite K (⨂[K] _ : Fin m, W) := Module.Finite.of_basis bt
  let P := majLeftIndices (finrank K U) (finrank K W - finrank K U)
  have hli := bt.linearIndependent.comp (fun p : majGoodIndices P m => p.val) Subtype.val_injective
  have hmem (p : majGoodIndices P m) : bt p.val ∈ LinearMap.ker (LinearMap.id - majOperator A m) := by
    have hmaj : m < 2 * (univ.filter fun i => p.val i ∈ P).card := (mem_filter.mp p.property).2
    have hfixed := majOperator_tprod_self A h2 (fun i => b (p.val i)) hmaj (fun i hi => by
      obtain ⟨idx, _, hidx⟩ := mem_map.mp (mem_filter.mp hi).2
      change Sum.inl idx = p.val i at hidx
      rw [← hidx]
      simpa [b, Basis.prod_apply] using hfix (bU idx) (bU idx).property)
    simpa [bt, LinearMap.mem_ker, Basis.piTensorProduct_apply] using sub_eq_zero.mpr hfixed.symm
  let Zker : Submodule K (⨂[K] _ : Fin m, W) := LinearMap.ker (LinearMap.id - majOperator A m)
  have hliZ : LinearIndependent K (fun p : majGoodIndices P m => (⟨bt p.val, hmem p⟩ : Zker)) :=
    LinearIndependent.of_comp Zker.subtype hli
  simpa only [Fintype.card_coe] using hliZ.fintype_card_le_finrank

private theorem majGoodIndices_card_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Finset ι) (m : ℕ) :
    (majGoodIndices P m).card =
      ∑ a ∈ (range (m + 1)).filter (fun a => m < 2 * a),
        m.choose a * P.card ^ a * (Fintype.card ι - P.card) ^ (m - a) := by
  classical
  let pat (p : Fin m → ι) : Finset (Fin m) := univ.filter fun i => p i ∈ P
  have hpat_card (S : Finset (Fin m)) :
      (univ.filter fun p : Fin m → ι => pat p = S).card =
        P.card ^ S.card * (Fintype.card ι - P.card) ^ (m - S.card) := by
    have hfib : (univ.filter fun p : Fin m → ι => pat p = S) =
        Fintype.piFinset (fun i : Fin m => if i ∈ S then P else Pᶜ) := by
      ext p
      simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset, Finset.ext_iff, pat]
      exact ⟨fun h i => by by_cases hi : i ∈ S <;> simpa [hi] using h i,
        fun h i => by by_cases hi : i ∈ S <;> simpa [hi] using h i⟩
    rw [hfib, Fintype.card_piFinset]
    simp_rw [apply_ite]
    rw [Finset.prod_ite]
    have hcompl : (univ.filter fun i : Fin m => i ∉ S) = Sᶜ := by ext i; simp
    simp [hcompl, card_compl]
  have hgood_fib (S : Finset (Fin m)) :
      ((majGoodIndices P m).filter fun p => pat p = S).card =
        if m < 2 * S.card then P.card ^ S.card * (Fintype.card ι - P.card) ^ (m - S.card) else 0 := by
    by_cases hm : m < 2 * S.card
    · rw [ite_eq_left hm, ← hpat_card S]
      congr 1; ext p
      simp only [majGoodIndices, mem_filter, mem_univ, true_and]
      change (m < 2 * (pat p).card ∧ pat p = S) ↔ pat p = S
      exact ⟨fun h => h.2, fun h => ⟨h.symm ▸ hm, h⟩⟩
    · rw [ite_eq_right hm, card_eq_zero, eq_empty_iff_forall_notMem]
      intro p hp
      obtain ⟨hg, hps⟩ := mem_filter.mp hp
      have h1 : m < 2 * (pat p).card := (mem_filter.mp hg).2
      exact hm (hps ▸ h1)
  rw [card_eq_sum_card_fiberwise (s := majGoodIndices P m)
    (t := (univ : Finset (Fin m)).powerset) (f := pat) (fun p _ => mem_powerset.mpr (subset_univ _))]
  simp_rw [hgood_fib]
  rw [sum_powerset_apply_card (fun a => if m < 2 * a then
    P.card ^ a * (Fintype.card ι - P.card) ^ (m - a) else 0)]
  simp only [card_univ, Fintype.card_fin, nsmul_eq_mul, sum_filter]
  apply sum_congr rfl
  intro a _
  by_cases ha : m < 2 * a <;> simp [ha, mul_assoc]

private theorem majGoodIndices_card_ge_exp {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Finset ι) (m : ℕ) (hn : 0 < Fintype.card ι) {ρ : ℝ} (hρ : 1 / 2 < ρ) (hρ1 : ρ < 1)
    (hr : ρ ≤ (P.card : ℝ) / Fintype.card ι) :
    (1 - Real.exp (-LeanMachine.BinomialTail.decay ρ * m)) *
      (Fintype.card ι : ℝ) ^ m ≤ (majGoodIndices P m).card := by
  let r : ℝ := (P.card : ℝ) / Fintype.card ι
  let f (a : ℕ) : ℝ := (m.choose a : ℝ) * r ^ a * (1 - r) ^ (m - a)
  have hnR : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hn
  have hr1 : r ≤ 1 := (div_le_one hnR).mpr (by exact_mod_cast card_le_univ P)
  have htail := LeanMachine.BinomialTail.half_sum_le_exp hρ hρ1 hr hr1 m
  have hsplit := sum_filter_add_sum_filter_not (range (m + 1)) (fun a => m < 2 * a) f
  simp only [not_lt] at hsplit
  have hfull : ∑ a ∈ range (m + 1), f a = 1 := by
    have h := add_pow r (1 - r) m
    rw [add_sub_cancel, one_pow] at h
    simpa only [f, mul_comm, mul_left_comm, mul_assoc] using h.symm
  rw [hfull] at hsplit
  have hgood : 1 - Real.exp (-LeanMachine.BinomialTail.decay ρ * m) ≤
      ∑ a ∈ (range (m + 1)).filter (fun a => m < 2 * a), f a := by
    change (∑ a ∈ (range (m + 1)).filter (fun a => 2 * a ≤ m), f a) ≤ _ at htail
    linarith
  have hnorm : ((majGoodIndices P m).card : ℝ) =
      (Fintype.card ι : ℝ) ^ m * ∑ a ∈ (range (m + 1)).filter (fun a => m < 2 * a), f a := by
    rw [majGoodIndices_card_eq_sum, Nat.cast_sum, mul_sum]
    apply sum_congr rfl
    intro a ha
    have ha_le : a ≤ m := by have := mem_range.mp (mem_filter.mp ha).1; omega
    have hk_le : P.card ≤ Fintype.card ι := card_le_univ P
    have hn0 : (Fintype.card ι : ℝ) ≠ 0 := hnR.ne'
    have hdiff : 1 - r = ((Fintype.card ι : ℝ) - P.card) / Fintype.card ι := by
      dsimp [r]; field_simp
    have hpow : (Fintype.card ι : ℝ) ^ m =
        (Fintype.card ι : ℝ) ^ a * (Fintype.card ι : ℝ) ^ (m - a) := by
      rw [← pow_add, Nat.add_sub_of_le ha_le]
    dsimp [f, r]
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hk_le]
    rw [show 1 - (P.card : ℝ) / Fintype.card ι =
        ((Fintype.card ι : ℝ) - P.card) / Fintype.card ι from hdiff,
      div_pow, div_pow, hpow]
    field_simp
  calc
    _ ≤ (∑ a ∈ (range (m + 1)).filter (fun a => m < 2 * a), f a) * (Fintype.card ι : ℝ) ^ m :=
      mul_le_mul_of_nonneg_right hgood (pow_nonneg hnR.le _)
    _ = _ := by rw [mul_comm, hnorm]

private noncomputable def majCoordBasis (K : Type*) [Field K] (V : Type*) [Fintype V]
    [DecidableEq V] (m : ℕ) : Basis (Fin m → V) K (⨂[K] _ : Fin m, V → K) :=
  Basis.piTensorProduct fun _ : Fin m => Pi.basisFun K V

private noncomputable def majMatrix {K V : Type*} [Field K] [Fintype V] [DecidableEq V]
    (A : Matrix V V K) (m : ℕ) : Matrix (Fin m → V) (Fin m → V) K :=
  LinearMap.toMatrix (majCoordBasis K V m) (majCoordBasis K V m) (majOperator A.mulVecLin m)

private theorem majMatrix_support {K V : Type*} [Field K] [Fintype V] [DecidableEq V] {m : ℕ}
    (A : Matrix V V K) (hdiag : ∀ v, A v v = 0) (h2 : (2 : K) ≠ 0) (hm : Odd m)
    {u v : Fin m → V} (huv : majMatrix A m u v ≠ 0) :
    Odd ((univ.filter fun i => u i ≠ v i).card) ∧ ∀ i, u i ≠ v i → A (u i) (v i) ≠ 0 := by
  let S := univ.filter fun i => u i ≠ v i
  have happly : majMatrix A m u v =
      (((2 : K) ^ m)⁻¹ * ∑ σ : Fin m → Bool, majPatternSign (K := K) σ *
        ∏ i ∈ S, majSign (K := K) (σ i)) * ∏ i ∈ S, A (u i) (v i) := by
    have h1 : majMatrix A m u v = ((2 : K) ^ m)⁻¹ *
        ∑ σ : Fin m → Bool, majPatternSign (K := K) σ *
          ∏ i, ((if u i = v i then 1 else 0) + majSign (K := K) (σ i) * A (u i) (v i)) := by
      simp [majMatrix, LinearMap.toMatrix_apply, majCoordBasis, majOperator, majCorner,
        Pi.basisFun_apply, Pi.single_apply]
    have hprod (σ : Fin m → Bool) :
        (∏ i, ((if u i = v i then 1 else 0) + majSign (K := K) (σ i) * A (u i) (v i))) =
        (∏ i ∈ S, majSign (K := K) (σ i)) * ∏ i ∈ S, A (u i) (v i) := by
      rw [← Finset.prod_mul_distrib, show S = univ.filter (fun i => u i ≠ v i) from rfl, prod_filter]
      apply prod_congr rfl
      intro i _
      by_cases hi : u i = v i <;> simp [hi, hdiag]
    rw [h1]
    simp_rw [hprod, ← mul_assoc]
    rw [← sum_mul, mul_assoc]
  rw [happly] at huv
  obtain ⟨hc, hp⟩ := mul_ne_zero_iff.mp huv
  refine ⟨?_, fun i hi => prod_ne_zero_iff.mp hp i (mem_filter.mpr ⟨mem_univ _, hi⟩)⟩
  by_contra hnot
  have hev : Even S.card := Nat.not_odd_iff_even.mp hnot
  let e : (Fin m → Bool) ≃ (Fin m → Bool) :=
    ⟨(fun σ i => !σ i), (fun σ i => !σ i), fun σ => by funext i; simp, fun σ => by funext i; simp⟩
  let f : (Fin m → Bool) → K := fun σ => majPatternSign (K := K) σ * ∏ i ∈ S, majSign (K := K) (σ i)
  have hneg (σ : Fin m → Bool) : f (e σ) = -f σ := by
    simp [f, e, majPatternSign_not hm, Finset.prod_neg, hev.neg_one_pow]
  have hsum : (∑ σ, f σ) = -(∑ σ, f σ) := by
    calc (∑ σ, f σ) = ∑ σ, f (e σ) := (e.sum_comp f).symm
      _ = -(∑ σ, f σ) := by simp_rw [hneg]; rw [sum_neg_distrib]
  have hz : ∑ σ, f σ = 0 := by
    apply (mul_eq_zero.mp (show (2 : K) * (∑ σ, f σ) = 0 from ?_)).resolve_left h2
    rw [two_mul]
    conv_lhs => rhs; rw [hsum]
    exact add_neg_cancel _
  exact hc (by change ((2 : K) ^ m)⁻¹ * (∑ σ, f σ) = 0; rw [hz, mul_zero])

private theorem majCheck_diag_one {K V : Type*} [Field K] [Fintype V] [DecidableEq V] {m : ℕ}
    (A : Matrix V V K) (hdiag : ∀ v, A v v = 0) (h2 : (2 : K) ≠ 0) (hm : Odd m) (u : Fin m → V) :
    (1 - majMatrix A m) u u = 1 := by
  have hd0 : majMatrix A m u u = 0 := by
    by_contra h
    have ho := (majMatrix_support A hdiag h2 hm h).1
    simp at ho
  simp [Matrix.sub_apply, hd0]

private theorem majCheck_rank_le_exp {K V : Type*} [Field K] [Fintype V] [DecidableEq V]
    (A : Matrix V V K) (h2 : (2 : K) ≠ 0) (U : Submodule K (V → K))
    (hU : U ≤ LinearMap.ker (1 - A).mulVecLin) (m : ℕ) (hV : 0 < Fintype.card V)
    {ρ : ℝ} (hρ : 1 / 2 < ρ) (hρ1 : ρ < 1) (hρU : ρ * Fintype.card V ≤ finrank K U) :
    ((1 - majMatrix A m).rank : ℝ) ≤
      Real.exp (-LeanMachine.BinomialTail.decay ρ * m) * (Fintype.card V : ℝ) ^ m := by
  have hfix : ∀ x ∈ U, A.mulVecLin x = x := by
    intro x hx
    have h := hU hx
    change (1 - A).mulVec x = 0 at h
    have he : x - A.mulVec x = 0 := by simpa only [Matrix.sub_mulVec, Matrix.one_mulVec] using h
    exact (sub_eq_zero.mp he).symm
  have hrn : (1 - majMatrix A m).rank +
      finrank K (LinearMap.ker (LinearMap.id - majOperator A.mulVecLin m)) = Fintype.card V ^ m := by
    let b := majCoordBasis K V m
    have : Module.Finite K (⨂[K] _ : Fin m, V → K) := Module.Finite.of_basis b
    have he : 1 - majMatrix A m =
        LinearMap.toMatrix b b (LinearMap.id - majOperator A.mulVecLin m) := by
      have hs := (LinearMap.toMatrix b b).map_sub LinearMap.id (majOperator A.mulVecLin m)
      change LinearMap.toMatrix b b (LinearMap.id - majOperator A.mulVecLin m) =
        LinearMap.toMatrix b b LinearMap.id - LinearMap.toMatrix b b (majOperator A.mulVecLin m) at hs
      rw [LinearMap.toMatrix_id] at hs
      exact hs.symm
    rw [he, Matrix.rank_eq_finrank_range_toLin _ b b, Matrix.toLin_toMatrix,
      LinearMap.finrank_range_add_finrank_ker, Module.finrank_eq_card_basis b]
    exact Fintype.card_pi_const V m
  have hk : finrank K U ≤ Fintype.card V := by simpa only [Module.finrank_pi] using U.finrank_le
  let P := majLeftIndices (finrank K U) (Fintype.card V - finrank K U)
  have hsub : (majGoodIndices P m).card ≤
      finrank K (LinearMap.ker (LinearMap.id - majOperator A.mulVecLin m)) :=
    majSubspace_goodIndices_le_ker A.mulVecLin h2 U hfix (Fintype.card V)
      (Module.finrank_pi K) m
  have hbudget : (1 - majMatrix A m).rank + (majGoodIndices P m).card ≤ Fintype.card V ^ m := by
    omega
  have hc : Fintype.card (Fin (finrank K U) ⊕ Fin (Fintype.card V - finrank K U)) = Fintype.card V := by
    simp only [Fintype.card_sum, Fintype.card_fin, Nat.add_sub_of_le hk]
  have hn : 0 < Fintype.card (Fin (finrank K U) ⊕ Fin (Fintype.card V - finrank K U)) := hc.symm ▸ hV
  have hr : ρ ≤ (P.card : ℝ) /
      Fintype.card (Fin (finrank K U) ⊕ Fin (Fintype.card V - finrank K U)) := by
    have hP : P.card = finrank K U := by simp [P, majLeftIndices]
    rw [hc, hP]
    exact (le_div_iff₀ (by exact_mod_cast hV)).mpr hρU
  have hgood := majGoodIndices_card_ge_exp P m hn hρ hρ1 hr
  rw [hc] at hgood
  have hbudgetR : ((1 - majMatrix A m).rank : ℝ) + ((majGoodIndices P m).card : ℝ) ≤
      (Fintype.card V : ℝ) ^ m := by exact_mod_cast hbudget
  nlinarith

open Classical in
private noncomputable def majMatrixHelpers {K V : Type*} [Field K] [Fintype V] [DecidableEq V]
    (H : Matrix V V K) (v : V) : Finset V :=
  univ.filter fun u => u ≠ v ∧ H v u ≠ 0

private theorem majExists_syndrome_code {K V : Type*} [Field K] [Fintype K] [Fintype V]
    [DecidableEq V] [Nonempty V] (H : Matrix V V K) (hd : ∀ v, H v v ≠ 0) :
    ∃ C : Finset (V → Bool), C.Nonempty ∧ IsStorageCode (majMatrixHelpers H) C ∧
      (2 : ℝ) ^ Fintype.card V ≤ (Fintype.card K : ℝ) ^ H.rank * (C.card : ℝ) := by
  classical
  let e : Bool → K := fun b => if b then 1 else 0
  have he : Function.Injective e := fun x y h => by cases x <;> cases y <;> simp_all [e]
  let syn : (V → Bool) → (V → K) := fun x => H.mulVec (e ∘ x)
  obtain ⟨y, hy, hcard⟩ := exists_large_obs_fibre (S := (univ : Finset (V → Bool))) univ_nonempty syn
  obtain ⟨x₀, _, hx₀⟩ := mem_image.mp hy
  let C := univ.filter fun x : V → Bool => syn x = y
  have hxC : x₀ ∈ C := mem_filter.mpr ⟨mem_univ _, hx₀⟩
  have hstor : IsStorageCode (majMatrixHelpers H) C := by
    intro x hx x' hx' v hhelp
    apply he
    have hxy : syn x = syn x' := (mem_filter.mp hx).2.trans (mem_filter.mp hx').2.symm
    have hoff : ∑ u ∈ univ.erase v, H v u * e (x u) = ∑ u ∈ univ.erase v, H v u * e (x' u) := by
      apply sum_congr rfl
      intro u hu
      by_cases hz : H v u = 0
      · simp [hz]
      · have hm : u ∈ majMatrixHelpers H v := by
          dsimp only [majMatrixHelpers]
          exact mem_filter.mpr ⟨mem_univ _, (mem_erase.mp hu).1, hz⟩
        rw [hhelp u hm]
    have hrow := congrFun hxy v
    change (∑ u, H v u * e (x u)) = ∑ u, H v u * e (x' u) at hrow
    rw [← sum_erase_add _ _ (mem_univ v), ← sum_erase_add _ _ (mem_univ v), hoff] at hrow
    exact mul_left_cancel₀ (hd v) (add_left_cancel hrow)
  have himg : ((univ : Finset (V → Bool)).image syn).card ≤ Fintype.card K ^ H.rank := by
    let f : (V → Bool) → LinearMap.range H.mulVecLin := fun x => ⟨syn x, ⟨e ∘ x, rfl⟩⟩
    have him : (univ : Finset (V → Bool)).image syn = (univ.image f).image Subtype.val := by
      rw [image_image]; rfl
    rw [him]
    calc ((univ.image f).image Subtype.val).card ≤ (univ.image f).card := card_image_le
      _ ≤ Fintype.card (LinearMap.range H.mulVecLin) := card_le_univ _
      _ = Fintype.card K ^ H.rank := Module.card_eq_pow_finrank
  have hnat : 2 ^ Fintype.card V ≤ Fintype.card K ^ H.rank * C.card := by
    have h1 : 2 ^ Fintype.card V ≤ ((univ : Finset (V → Bool)).image syn).card * C.card := by
      simpa only [card_univ, Fintype.card_fun, Fintype.card_bool] using hcard
    exact h1.trans (Nat.mul_le_mul_right _ himg)
  exact ⟨C, ⟨x₀, hxC⟩, hstor, by exact_mod_cast hnat⟩

private def localOddProductGraph {V : Type*} [DecidableEq V] (G : SimpleGraph V) (m : ℕ) :
    SimpleGraph (Fin m → V) where
  Adj x y := (∀ i, x i = y i ∨ G.Adj (x i) (y i)) ∧
    Odd ((univ.filter fun i => x i ≠ y i).card)
  symm := by
    constructor
    intro x y h
    refine ⟨fun i => (h.1 i).imp Eq.symm (fun hi => hi.symm), ?_⟩
    simpa only [ne_comm] using h.2
  loopless := by
    constructor
    intro x h
    simpa using h.2

private def localProjectWalk {V : Type*} [DecidableEq V] {G : SimpleGraph V} {m : ℕ}
    {x y : Fin m → V} (w : (localOddProductGraph G m).Walk x y) (i : Fin m) :
    G.Walk (x i) (y i) :=
  match w with
  | .nil => .nil
  | .cons h w =>
    if heq : _ = _ then (localProjectWalk w i).copy heq.symm rfl
    else .cons ((h.1 i).resolve_left heq) (localProjectWalk w i)

private theorem localProjectWalk_length_le {V : Type*} [DecidableEq V] {G : SimpleGraph V} {m : ℕ}
    {x y : Fin m → V} (w : (localOddProductGraph G m).Walk x y) (i : Fin m) :
    (localProjectWalk w i).length ≤ w.length := by
  induction w with
  | nil => simp [localProjectWalk]
  | @cons x y z h w ih =>
    by_cases heq : x i = y i <;> simp [localProjectWalk, heq] <;> omega

private theorem localProjectWalk_sum_mod_two {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {m : ℕ} {x y : Fin m → V} (w : (localOddProductGraph G m).Walk x y) :
    (∑ i : Fin m, (localProjectWalk w i).length) % 2 = w.length % 2 := by
  induction w with
  | nil => simp [localProjectWalk]
  | @cons x y z h w ih =>
    have hc : ((univ.filter fun i => x i ≠ y i).card) % 2 = 1 := Nat.odd_iff.mp h.2
    have hcons (i : Fin m) : (localProjectWalk (.cons h w) i).length =
        (localProjectWalk w i).length + if x i = y i then 0 else 1 := by
      by_cases heq : x i = y i <;> simp [localProjectWalk, heq]
    have heq : (∑ i : Fin m, (localProjectWalk (.cons h w) i).length) =
        (∑ i : Fin m, (localProjectWalk w i).length) + (univ.filter fun i => x i ≠ y i).card := by
      simp_rw [hcons]
      rw [sum_add_distrib]
      congr 1
      simp only [card_filter, ite_not]
    rw [heq, Nat.add_mod, ih, hc, SimpleGraph.Walk.length_cons, Nat.add_mod]
    omega

private theorem localOddProduct_closed_gt {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {m G₀ : ℕ} (hG : ∀ v (w : G.Walk v v), Odd w.length → G₀ < w.length)
    {x : Fin m → V} (w : (localOddProductGraph G m).Walk x x) (hw : Odd w.length) :
    G₀ < w.length := by
  have hsum : Odd (∑ i : Fin m, (localProjectWalk w i).length) := by
    rw [Nat.odd_iff, localProjectWalk_sum_mod_two]
    exact Nat.odd_iff.mp hw
  have hex : ∃ i : Fin m, Odd (localProjectWalk w i).length := by
    by_contra hall
    push Not at hall
    have heven : Even (∑ i : Fin m, (localProjectWalk w i).length) :=
      Finset.even_sum _ fun i _ => Nat.not_odd_iff_even.mp (hall i)
    exact (Nat.not_even_iff_odd.mpr hsum) heven
  obtain ⟨i, hi⟩ := hex
  exact (hG (x i) (localProjectWalk w i) hi).trans_le (localProjectWalk_length_le w i)

private theorem alternatingListToWalk {W : Type*} (H : SimpleGraph W) :
    ∀ (l : List (Bool × W)),
      (∀ t : ℕ, ∀ h : t + 1 < l.length,
        let p := l.get ⟨t, Nat.lt_of_succ_lt h⟩
        let q := l.get ⟨t + 1, h⟩
        p.1 ≠ q.1 ∧ H.Adj p.2 q.2) →
      ∀ (p q : Bool × W), l.head? = some p → l.getLast? = some q →
        ∃ w : H.Walk p.2 q.2, w.length + 1 = l.length ∧ (p.1 ≠ q.1 ↔ Odd w.length)
  | [], _, _, _, hh, _ => by simp at hh
  | [a], _, p, q, hh, hl => by
    simp only [List.head?_cons, List.getLast?_singleton, Option.some.injEq] at hh hl
    subst hh; subst hl
    exact ⟨.nil, rfl, by simp⟩
  | a :: b :: rest, hstep, p, q, hh, hl => by
    simp only [List.head?_cons, Option.some.injEq] at hh
    obtain ⟨ha1, hadj⟩ := hstep 0 (by simp)
    have hstep' : ∀ t : ℕ, ∀ h : t + 1 < (b :: rest).length,
        let p' := (b :: rest).get ⟨t, Nat.lt_of_succ_lt h⟩
        let q' := (b :: rest).get ⟨t + 1, h⟩
        p'.1 ≠ q'.1 ∧ H.Adj p'.2 q'.2 :=
      fun t ht => hstep (t + 1) (Nat.add_lt_add_right ht 1)
    rw [List.getLast?_cons_cons] at hl
    obtain ⟨w, hwlen, hwpar⟩ := alternatingListToWalk H (b :: rest) hstep' b q rfl hl
    subst hh
    refine ⟨.cons hadj w, by simp only [SimpleGraph.Walk.length_cons, List.length_cons] at hwlen ⊢; omega, ?_⟩
    simp only [SimpleGraph.Walk.length_cons]
    have hb_iff : (a.1 ≠ q.1) ↔ (b.1 = q.1) := by
      cases ha : a.1 <;> cases hb : b.1 <;> cases hq : q.1 <;> simp_all
    rw [hb_iff]
    constructor
    · intro hbq
      have hnot : ¬ Odd w.length := fun ho => (hwpar.mpr ho) hbq
      exact (Nat.not_odd_iff_even.mp hnot).add_one
    · intro hodd1
      by_contra hne
      obtain ⟨k1, hk1⟩ := hwpar.mp hne
      obtain ⟨k2, hk2⟩ := hodd1
      omega

open Classical in
private theorem transport_separated_code {V : Type*} [Fintype V] [DecidableEq V]
    {n Delta G : ℕ} (eqv : V ≃ Fin n)
    (H_graph : SimpleGraph V)
    (hdeg_H : ∀ x : V, (univ.filter fun y : V => H_graph.Adj x y).card ≤ Delta)
    (hodd_H : ∀ (v : V) (w : H_graph.Walk v v), Odd w.length → G < w.length)
    (N_V : V → Finset V)
    (hsupp : ∀ q p : V, p ∈ N_V q → H_graph.Adj q p)
    (C_V : Finset (V → Bool))
    (hstor : IsStorageCode N_V C_V) :
    let N_fin : Fin n → Finset (Fin n) := fun v => (N_V (eqv.symm v)).map eqv.toEmbedding
    let C_fin : Set (Fin n → Bool) :=
      (fun (x : V → Bool) (v : Fin n) => x (eqv.symm v)) '' (C_V : Set (V → Bool))
    IsBoundedDegreeSeparatedRelation Delta G N_fin ∧
    IsBinaryStorageCodeFor N_fin C_fin ∧
    Nat.card C_fin = C_V.card := by
  intro N_fin C_fin
  have hinj_word : Function.Injective (fun (x : V → Bool) (v : Fin n) => x (eqv.symm v)) := by
    intro x y hxy; funext u
    have h := congrFun hxy (eqv u)
    simpa using h
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro v
    dsimp only [N_fin]
    rw [Finset.card_map]
    refine (Finset.card_le_card (fun u hu => ?_)).trans (hdeg_H (eqv.symm v))
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsupp _ _ hu⟩
  · intro u
    have hbij : (Finset.univ.filter fun v : Fin n => u ∈ N_fin v).card =
        (Finset.univ.filter fun w : V => eqv.symm u ∈ N_V w).card := by
      apply Finset.card_bij (fun v _ => eqv.symm v)
      · intro v hv
        have hm_u : u ∈ N_fin v := (Finset.mem_filter.mp hv).2
        simp only [N_fin, Finset.mem_map, Equiv.coe_toEmbedding] at hm_u
        obtain ⟨z, hz, hzeq⟩ := hm_u
        have hzu : z = eqv.symm u := (eqv.symm_apply_eq.mpr hzeq.symm).symm
        subst hzu
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩
      · intro v₁ _ v₂ _ h12; exact eqv.symm.injective h12
      · intro w hw
        refine ⟨eqv w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, eqv.symm_apply_apply w⟩
        simp only [N_fin, Finset.mem_map, Equiv.coe_toEmbedding, eqv.symm_apply_apply]
        exact ⟨eqv.symm u, (Finset.mem_filter.mp hw).2, eqv.apply_symm_apply u⟩
    rw [hbij]
    refine (Finset.card_le_card (fun w hw => ?_)).trans (hdeg_H (eqv.symm u))
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hsupp _ _ (Finset.mem_filter.mp hw).2).symm⟩
  · intro v walk hhead hlast hstep
    let vwalk : List (Bool × V) := walk.map fun pv => (pv.1, eqv.symm pv.2)
    have hvw_len : vwalk.length = walk.length := List.length_map _
    have hvw_hd : vwalk.head? = some (false, eqv.symm v) := by
      rw [List.head?_map, hhead]; rfl
    have hvw_lst : vwalk.getLast? = some (true, eqv.symm v) := by
      rw [List.getLast?_map, hlast]; rfl
    have hvw_step : ∀ t : ℕ, ∀ h : t + 1 < vwalk.length,
        let p := vwalk.get ⟨t, Nat.lt_of_succ_lt h⟩
        let q := vwalk.get ⟨t + 1, h⟩
        p.1 ≠ q.1 ∧ H_graph.Adj p.2 q.2 := by
      intro t ht
      rw [hvw_len] at ht
      have hg1 : vwalk.get ⟨t, by rw [hvw_len]; exact Nat.lt_of_succ_lt ht⟩ =
          ((walk.get ⟨t, Nat.lt_of_succ_lt ht⟩).1,
            eqv.symm (walk.get ⟨t, Nat.lt_of_succ_lt ht⟩).2) := by simp [vwalk]
      have hg2 : vwalk.get ⟨t + 1, by rw [hvw_len]; exact ht⟩ =
          ((walk.get ⟨t + 1, ht⟩).1, eqv.symm (walk.get ⟨t + 1, ht⟩).2) := by simp [vwalk]
      dsimp only
      rw [hg1, hg2]
      rcases hstep t ht with ⟨hp1, hq1, hmem⟩ | ⟨hp1, hq1, hmem⟩
      · refine ⟨by rw [hp1, hq1]; decide, ?_⟩
        simp only [N_fin, Finset.mem_map, Equiv.coe_toEmbedding] at hmem
        obtain ⟨z, hz, hzeq⟩ := hmem
        have hzu : z = eqv.symm (walk.get ⟨t, Nat.lt_of_succ_lt ht⟩).2 :=
          (eqv.symm_apply_eq.mpr hzeq.symm).symm
        subst hzu
        exact (hsupp _ _ hz).symm
      · refine ⟨by rw [hp1, hq1]; decide, ?_⟩
        simp only [N_fin, Finset.mem_map, Equiv.coe_toEmbedding] at hmem
        obtain ⟨z, hz, hzeq⟩ := hmem
        have hzu : z = eqv.symm (walk.get ⟨t + 1, ht⟩).2 :=
          (eqv.symm_apply_eq.mpr hzeq.symm).symm
        subst hzu
        exact hsupp _ _ hz
    obtain ⟨w, hwlen, hwpar⟩ := alternatingListToWalk H_graph vwalk hvw_step
      (false, eqv.symm v) (true, eqv.symm v) hvw_hd hvw_lst
    have hodd : Odd w.length := hwpar.mp Bool.false_ne_true
    have hgt : G < w.length := hodd_H (eqv.symm v) w hodd
    omega
  · rintro x ⟨x₀, hx₀, rfl⟩ y ⟨y₀, hy₀, rfl⟩ v hagree
    apply hstor x₀ hx₀ y₀ hy₀ (eqv.symm v)
    intro u hu
    have hu_mem : eqv u ∈ N_fin v := by
      simp only [N_fin, Finset.mem_map, Equiv.coe_toEmbedding]
      exact ⟨u, hu, rfl⟩
    have heq := hagree (eqv u) hu_mem
    simpa using heq
  · dsimp only [C_fin]
    rw [Nat.card_image_of_injective hinj_word, Nat.card_coe_set_eq, Set.ncard_coe_finset]

private theorem seed_rate_and_exponent {K : Type} [Field K] [Fintype K] {D_seed : ℕ} {ρ : ℝ}
    (hρ : 1 / 2 < ρ) (hρ1 : ρ < 1) {n : ℕ} (hn : 0 < n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hdeg : ∀ u, G.degree u ≤ D_seed)
    (U : Submodule K (Fin n → K))
    (hrec : ∀ x ∈ U, ∀ u, (∀ v, G.Adj u v → x v = 0) → x u = 0)
    (hdim : ρ * (n : ℝ) ≤ finrank K U) :
    0 < D_seed ∧
    0 < LeanMachine.BinomialTail.decay ρ / Real.log ((D_seed : ℝ) + 1) ∧
    LeanMachine.BinomialTail.decay ρ / Real.log ((D_seed : ℝ) + 1) < 1 / 2 := by
  classical
  have hrecL : LeanMachine.LinearRecovery.IsRecoverable (fun p q => G.Adj q p) U := by
    intro q x hx y hy hagree
    have hxy : x - y ∈ U := U.sub_mem hx hy
    have h0 : (x - y) q = 0 := hrec (x - y) hxy q fun v huv => by
      simp [Pi.sub_apply, hagree v huv]
    exact sub_eq_zero.mp h0
  obtain ⟨A, hAsupp, hUker⟩ := hrecL.exists_recovery_matrix
  have hcard_le : n ≤ (D_seed + 1) * (1 - A).rank := by
    let S (v : Fin n) : Finset (Fin n) := insert v (G.neighborFinset v)
    have hdiag_ne (c : Fin n) : (1 - A) c c ≠ 0 := by
      simp [Matrix.sub_apply, hAsupp c c (G.loopless.irrefl c)]
    have hi (c : Fin n) : Function.Injective
        ((1 - A).mulVecLin.comp (LinearMap.single K (fun _ : Fin n => K) c)) := by
      intro x y h
      have hv := congrFun h c
      simp only [LinearMap.comp_apply, LinearMap.single_apply, Matrix.mulVecLin_apply,
        Matrix.mulVec_single] at hv
      exact mul_left_cancel₀ (hdiag_ne c) hv
    have hr (c : Fin n) : finrank K (LinearMap.range
        ((1 - A).mulVecLin.comp (LinearMap.single K (fun _ : Fin n => K) c))) = 1 := by
      rw [LinearMap.finrank_range_of_inj (hi c), Module.finrank_self]
    have hsp := LeanMachine.SparseProjection.sum_column_ranks_le (1 - A).mulVecLin S (D_seed + 1)
      (fun v => by
        simpa [S, card_insert_of_notMem (G.notMem_neighborFinset_self v),
          SimpleGraph.card_neighborFinset_eq_degree] using Nat.add_le_add_right (hdeg v) 1)
      (fun a c hca => by
        apply LinearMap.ext; intro x
        have hac_ne : a ≠ c := fun he => hca (mem_insert.mpr (Or.inl he.symm))
        have hca_adj : ¬G.Adj a c := fun he =>
          hca (mem_insert.mpr (Or.inr ((G.mem_neighborFinset a c).mpr he)))
        simp [Matrix.mulVec_single, Pi.single_eq_of_ne hac_ne, hAsupp a c hca_adj])
    simpa [hr, Matrix.rank] using hsp
  have hbudget : finrank K U + (1 - A).rank ≤ n := by
    simpa only [Fintype.card_fin] using LeanMachine.LinearRecovery.finrank_add_rank_le U A hUker
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hbudgetR : (finrank K U : ℝ) + ((1 - A).rank : ℝ) ≤ n := by exact_mod_cast hbudget
  have hcardR : (n : ℝ) ≤ ((D_seed : ℝ) + 1) * ((1 - A).rank : ℝ) := by exact_mod_cast hcard_le
  have hrk : ((1 - A).rank : ℝ) ≤ (1 - ρ) * n := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hrk (by positivity : (0 : ℝ) ≤ (D_seed : ℝ) + 1)
  have hc : 1 ≤ ((D_seed : ℝ) + 1) * (1 - ρ) :=
    (mul_le_mul_iff_of_pos_right hnR).mp (by nlinarith [hcardR, hm])
  have hfrac : ρ ≤ (D_seed : ℝ) / ((D_seed : ℝ) + 1) :=
    (le_div_iff₀ (by positivity : (0 : ℝ) < (D_seed : ℝ) + 1)).mpr (by nlinarith)
  have hDpos : 0 < D_seed := by
    by_contra h0
    have hD0 : D_seed = 0 := by omega
    subst hD0
    simp at hfrac
    linarith
  have hlog : 0 < Real.log ((D_seed : ℝ) + 1) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < D_seed + 1))
  refine ⟨hDpos, div_pos (LeanMachine.BinomialTail.decay_pos hρ hρ1) hlog, ?_⟩
  apply (div_lt_iff₀ hlog).mpr
  let d : ℝ := (D_seed : ℝ) + 1
  have hd : 0 < d := by dsimp [d]; positivity
  have hb : ρ * d ≤ D_seed := (le_div_iff₀ hd).mp hfrac
  have hc' : 1 ≤ (1 - ρ) * d := by dsimp [d] at *; nlinarith
  have hp : 0 < ρ * (1 - ρ) := mul_pos (by linarith) (by linarith)
  have hmul := mul_le_mul_of_nonneg_left hc' (by linarith : 0 ≤ 4 * ρ)
  have hprod : 1 < (4 * ρ * (1 - ρ)) * d := by nlinarith
  have hz : 0 < 4 * ρ * (1 - ρ) := by nlinarith
  have hl := Real.log_lt_log (by norm_num : (0 : ℝ) < 1) hprod
  rw [Real.log_one, Real.log_mul hz.ne' hd.ne'] at hl
  have hdec : LeanMachine.BinomialTail.decay ρ = -Real.log (4 * ρ * (1 - ρ)) / 2 := by
    have he : (2 * Real.sqrt (ρ * (1 - ρ))) ^ 2 = 4 * ρ * (1 - ρ) := by
      rw [mul_pow, Real.sq_sqrt hp.le]; ring
    have h := Real.log_pow (2 * Real.sqrt (ρ * (1 - ρ))) 2
    rw [he] at h
    dsimp [LeanMachine.BinomialTail.decay]
    norm_num at h
    linarith
  rw [hdec]
  dsimp [d] at hl
  linarith

end OddMajorityAmplification

theorem diagnosis_AbstractSeparatedHighRateCode : Diagnosis_AbstractSeparatedHighRateCodeSpec := by
  constructor
  · -- Part 1: Numerical verification at `p = 127, k = 91`
    refine ⟨by norm_num, ?_, by norm_num, by norm_num, ?_⟩
    · have h1 : (17320508 : ℝ) / 10 ^ 7 < Real.sqrt 3 := by
        rw [Real.lt_sqrt (by norm_num)]; norm_num
      have h2 : Real.sqrt 3 < (17320509 : ℝ) / 10 ^ 7 := by
        rw [Real.sqrt_lt' (by norm_num)]; norm_num
      rw [Nat.ceil_eq_iff (by norm_num)]
      constructor <;> push_cast <;> nlinarith
    · have hlog : (615 : ℝ) / 44 < Real.logb 2 (127 ^ 2) := by
        rw [Real.lt_logb_iff_rpow_lt (by norm_num) (by norm_num)]
        have hpow : ((2 : ℝ) ^ ((615 : ℝ) / 44)) ^ (44 : ℕ) = (2 : ℝ) ^ (615 : ℕ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
            show ((615 : ℝ) / 44) * ((44 : ℕ) : ℝ) = ((615 : ℕ) : ℝ) by norm_num,
            Real.rpow_natCast]
        have hnat : (2 : ℕ) ^ 615 < (127 ^ 2) ^ 44 := by
          have h3 : (2 : ℕ) ^ 615 = 2 ^ 205 * 2 ^ 205 * 2 ^ 205 := by
            rw [← pow_add, ← pow_add]
          rw [h3]
          norm_num
        have h44 : ((2 : ℝ) ^ ((615 : ℝ) / 44)) ^ (44 : ℕ) < ((127 : ℝ) ^ 2) ^ (44 : ℕ) := by
          rw [hpow]
          exact_mod_cast hnat
        exact lt_of_pow_lt_pow_left₀ 44 (by positivity) h44
      unfold Real.logb at hlog
      nlinarith
  · -- Part 2: Odd-majority tensor amplification
    intro K _ _ D_seed ρ h2 hρ hρ1 hseed
    classical
    obtain ⟨size, adj, decAdj, code, hgrow, hsymm, hloop, hdeg, hodd, hrec, hdim⟩ := hseed
    let G_seed (j : ℕ) : SimpleGraph (Fin (size j)) :=
      { Adj := adj j
        symm := ⟨fun u v huv => (hsymm j u v).mp huv⟩
        loopless := ⟨hloop j⟩ }
    have hdegG : ∀ j u, (G_seed j).degree u ≤ D_seed := by
      intro j u
      rw [← SimpleGraph.card_neighborFinset_eq_degree]
      have hsub : (G_seed j).neighborFinset u = Finset.univ.filter (fun v => adj j u v) := by
        ext v; simp [SimpleGraph.mem_neighborFinset, G_seed]
      rw [hsub]
      exact hdeg j u
    obtain ⟨j_pos, hj_pos⟩ := hgrow 1
    have hsize_pos : 0 < size j_pos := hj_pos j_pos (Nat.le_refl _)
    obtain ⟨hDpos, hα0, hαhalf⟩ := seed_rate_and_exponent hρ hρ1 hsize_pos
      (G_seed j_pos) (hdegG j_pos) (code j_pos) (hrec j_pos) (hdim j_pos)
    let α := LeanMachine.BinomialTail.decay ρ / Real.log ((D_seed : ℝ) + 1)
    let C_code := Real.logb 2 (Fintype.card K) * Real.exp (2 * LeanMachine.BinomialTail.decay ρ)
    have hCpos : 0 < C_code := by
      apply mul_pos
      · exact Real.logb_pos (by norm_num) (by exact_mod_cast Fintype.one_lt_card (α := K))
      · exact Real.exp_pos _
    refine ⟨C_code, α, D_seed + 1, hCpos, hα0, hαhalf, fun Delta G hDelta => ?_⟩
    have hp : 1 < D_seed + 1 := by omega
    have ha := LeanMachine.BinomialTail.decay_pos hρ hρ1
    obtain ⟨m, _, hm, hmcap, _, he⟩ :=
      LeanMachine.OddPowerChoice.exists_odd_power_and_decay hp hDelta ha.le
    obtain ⟨j₁, hj₁⟩ := hgrow 1
    obtain ⟨j₂, hj₂⟩ := hodd G
    let j := max j₁ j₂
    have hj_sz : 0 < size j := hj₁ j (le_max_left _ _)
    have hj_odd := hj₂ j (le_max_right _ _)
    let V0 := Fin (size j)
    have hV0_pos : 0 < Fintype.card V0 := by simpa [V0] using hj_sz
    have hrecL : LeanMachine.LinearRecovery.IsRecoverable
        (fun p q : V0 => (G_seed j).Adj q p) (code j) := by
      intro q x hx y hy hagree
      have hxy : x - y ∈ code j := (code j).sub_mem hx hy
      have h0 : (x - y) q = 0 := hrec j (x - y) hxy q fun v huv => by
        simp [Pi.sub_apply, hagree v huv]
      exact sub_eq_zero.mp h0
    obtain ⟨A, hAsupp, hUker⟩ := hrecL.exists_recovery_matrix
    have hAdiag : ∀ v : V0, A v v = 0 := fun v => hAsupp v v ((G_seed j).loopless.irrefl v)
    let V := Fin m → V0
    let n := Fintype.card V
    have hn_eq : n = size j ^ m := by simp [n, V, V0]
    have hn_pos : 0 < n := by rw [hn_eq]; exact pow_pos hj_sz m
    have hNeZero : NeZero n := ⟨hn_pos.ne'⟩
    have hNonemptyV : Nonempty V := Fintype.card_pos_iff.mp hn_pos
    let H : Matrix V V K := 1 - majMatrix A m
    have hHdiag : ∀ v : V, H v v ≠ 0 := fun v => by
      dsimp only [H]
      rw [majCheck_diag_one A hAdiag h2 hm v]
      exact one_ne_zero
    obtain ⟨C_V, hCV_ne, hCV_stor, hCV_card⟩ :=
      @majExists_syndrome_code K V _ _ _ _ hNonemptyV H hHdiag
    have hHrk : (H.rank : ℝ) ≤
        Real.exp (-LeanMachine.BinomialTail.decay ρ * m) * (Fintype.card V0 : ℝ) ^ m :=
      majCheck_rank_le_exp A h2 (code j) hUker m hV0_pos hρ hρ1
        (by simpa [V0] using hdim j)
    let H_prod : SimpleGraph V := localOddProductGraph (G_seed j) m
    have hsupp : ∀ q p : V, p ∈ majMatrixHelpers H q → H_prod.Adj q p := by
      intro q p hp_mem
      dsimp only [majMatrixHelpers] at hp_mem
      obtain ⟨_, hpq, hHqp⟩ := Finset.mem_filter.mp hp_mem
      have hMqp : majMatrix A m q p ≠ 0 := by
        have hqp : q ≠ p := Ne.symm hpq
        simpa [H, Matrix.sub_apply, Matrix.one_apply, hqp] using hHqp
      obtain ⟨hodd_act, hA_act⟩ := majMatrix_support A hAdiag h2 hm hMqp
      refine ⟨fun i => ?_, hodd_act⟩
      by_cases hi : q i = p i
      · exact Or.inl hi
      · refine Or.inr ?_
        by_contra hnadj
        exact hA_act i hi (hAsupp (q i) (p i) hnadj)
    have hdeg_prod : ∀ x : V, (Finset.univ.filter fun y : V => H_prod.Adj x y).card ≤ Delta := by
      intro x
      let box := Fintype.piFinset fun i : Fin m =>
        insert (x i) (Finset.univ.filter fun w : V0 => adj j (x i) w)
      have hsub : (Finset.univ.filter fun y : V => H_prod.Adj x y) ⊆ box := by
        intro y hy
        have hadj := (Finset.mem_filter.mp hy).2.1
        refine Fintype.mem_piFinset.mpr fun i => ?_
        rcases hadj i with heq | ha
        · exact Finset.mem_insert.mpr (Or.inl heq.symm)
        · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩))
      have hbox_card : box.card ≤ (D_seed + 1) ^ m := by
        rw [Fintype.card_piFinset]
        have hpr : (∏ i : Fin m, (insert (x i) (Finset.univ.filter fun w => adj j (x i) w)).card)
            ≤ ∏ _i : Fin m, (D_seed + 1) := by
          refine Finset.prod_le_prod fun i _ => ?_
          have hnot : x i ∉ Finset.univ.filter (fun w => adj j (x i) w) := by
            simp [hloop j (x i)]
          rw [Finset.card_insert_of_notMem hnot]
          exact Nat.add_le_add_right (hdeg j (x i)) 1
        simpa using hpr
      exact (Finset.card_le_card hsub).trans (hbox_card.trans hmcap)
    have hodd_base : ∀ (v : V0) (w : (G_seed j).Walk v v), Odd w.length → G < w.length := by
      intro v w hw
      let verts : List V0 := (List.range (w.length + 1)).map w.getVert
      have hv_len : verts.length = w.length + 1 := by simp [verts]
      have hv_head : verts.head? = some v := by
        dsimp only [verts]
        rw [List.range_eq_range', List.range'_succ]
        simp
      have hv_last : verts.getLast? = some v := by
        dsimp only [verts]
        rw [List.range_succ]
        simp [SimpleGraph.Walk.getVert_length]
      have hv_adj : ∀ i : ℕ, ∀ h : i + 1 < verts.length,
          adj j (verts.get ⟨i, Nat.lt_of_succ_lt h⟩) (verts.get ⟨i + 1, h⟩) := by
        intro i hi
        rw [hv_len] at hi
        have hi' : i < w.length := by omega
        have hg1 : verts.get ⟨i, by rw [hv_len]; omega⟩ = w.getVert i := by simp [verts]
        have hg2 : verts.get ⟨i + 1, by rw [hv_len]; exact hi⟩ = w.getVert (i + 1) := by simp [verts]
        rw [hg1, hg2]
        exact w.adj_getVert_succ hi'
      have hv_odd : Odd (verts.length - 1) := by simpa [hv_len] using hw
      simpa [hv_len] using hj_odd v verts hv_head hv_last hv_adj hv_odd
    have hodd_prod : ∀ (v : V) (w : H_prod.Walk v v), Odd w.length → G < w.length :=
      fun _ w hw => localOddProduct_closed_gt hodd_base w hw
    obtain ⟨hsep_fin, hstor_fin, hcard_eq⟩ := transport_separated_code (Fintype.equivFin V)
      H_prod hdeg_prod hodd_prod (majMatrixHelpers H) hsupp C_V hCV_stor
    refine ⟨n, hNeZero, _, _, hCV_ne.to_set.image _, hsep_fin, hstor_fin, ?_⟩
    rw [hcard_eq]
    have hCV_pos : (0 : ℝ) < (C_V.card : ℝ) := by exact_mod_cast hCV_ne.card_pos
    have hK_pos : (0 : ℝ) < (Fintype.card K : ℝ) := by exact_mod_cast Fintype.card_pos
    have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by positivity : (0 : ℝ) < (2 : ℝ) ^ Fintype.card V) hCV_card
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one,
      Real.logb_mul (pow_pos hK_pos _).ne' hCV_pos.ne', Real.logb_pow] at hlog
    have hlogK_nn : 0 ≤ Real.logb 2 (Fintype.card K) :=
      Real.logb_nonneg (by norm_num) (by exact_mod_cast Fintype.card_pos)
    have h1 : (H.rank : ℝ) * Real.logb 2 (Fintype.card K) ≤
        (Real.logb 2 (Fintype.card K) * Real.exp (-LeanMachine.BinomialTail.decay ρ * m)) *
          (n : ℝ) := by
      have hn_cast : (n : ℝ) = (Fintype.card V0 : ℝ) ^ m := by
        dsimp [n, V]; simp
      rw [hn_cast]
      have hm1 := mul_le_mul_of_nonneg_right hHrk hlogK_nn
      linarith
    have hcast : ((D_seed + 1 : ℕ) : ℝ) = (D_seed : ℝ) + 1 := by push_cast; ring
    rw [hcast] at he
    have h2_err : Real.logb 2 (Fintype.card K) * Real.exp (-LeanMachine.BinomialTail.decay ρ * m) ≤
        C_code * ((Delta : ℝ) ^ (-α)) := by
      dsimp [C_code, α]
      have hneg : -(LeanMachine.BinomialTail.decay ρ / Real.log ((D_seed : ℝ) + 1)) =
          -LeanMachine.BinomialTail.decay ρ / Real.log ((D_seed : ℝ) + 1) := by ring
      rw [hneg]
      have hm2 := mul_le_mul_of_nonneg_left he hlogK_nn
      linarith
    have hnR_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have h3 := mul_le_mul_of_nonneg_right h2_err hnR_nn
    have hn_fin : ((Fintype.card V : ℕ) : ℝ) = (n : ℝ) := rfl
    rw [hn_fin] at hlog
    change (1 - C_code * ((Delta : ℝ) ^ (-α))) * (n : ℝ) ≤ Real.logb 2 (C_V.card : ℝ)
    linarith [hlog, h1, h3]

/-! ### Diagnosis 3 -/

section ShiftAndRotationBarrier

private theorem ite_pos {α : Sort*} {c : Prop} [inst : Decidable c] {a b : α} (hc : c) :
    (if c then a else b) = a := by
  cases inst with
  | isFalse h => exact absurd hc h
  | isTrue _ => rfl

private theorem ite_neg {α : Sort*} {c : Prop} [inst : Decidable c] {a b : α} (hc : ¬ c) :
    (if c then a else b) = b := by
  cases inst with
  | isFalse _ => rfl
  | isTrue h => exact absurd h hc

private theorem dite_pos {α : Sort*} {c : Prop} [inst : Decidable c]
    {a : c → α} {b : ¬ c → α} (hc : c) : (if h : c then a h else b h) = a hc := by
  cases inst with
  | isFalse h => exact absurd hc h
  | isTrue _ => rfl

private theorem dite_neg {α : Sort*} {c : Prop} [inst : Decidable c]
    {a : c → α} {b : ¬ c → α} (hc : ¬ c) : (if h : c then a h else b h) = b hc := by
  cases inst with
  | isFalse _ => rfl
  | isTrue h => exact absurd h hc

private theorem mod_two_pow_succ_eq (u st : ℕ) :
    u % 2 ^ (st + 1) = 2 ^ st * ((u / 2 ^ st) % 2) + u % 2 ^ st := by
  have hp : 2 ^ (st + 1) = 2 ^ st * 2 := by rw [pow_succ]
  rw [hp]
  have hdiv := Nat.div_add_mod u (2 ^ st)
  have hdiv2 := Nat.div_add_mod (u / 2 ^ st) 2
  have hm_lt : u % 2 ^ st < 2 ^ st := Nat.mod_lt _ (Nat.two_pow_pos st)
  have hb_lt : (u / 2 ^ st) % 2 < 2 := Nat.mod_lt _ (by decide)
  have hlt : 2 ^ st * ((u / 2 ^ st) % 2) + u % 2 ^ st < 2 ^ st * 2 := by
    have : 2 ^ st * ((u / 2 ^ st) % 2) ≤ 2 ^ st * 1 := Nat.mul_le_mul_left _ (by omega)
    omega
  have hu_eq : u = (2 ^ st * ((u / 2 ^ st) % 2) + u % 2 ^ st) +
      (2 ^ st * 2) * ((u / 2 ^ st) / 2) := by
    calc u = 2 ^ st * (u / 2 ^ st) + u % 2 ^ st := hdiv.symm
      _ = 2 ^ st * (2 * ((u / 2 ^ st) / 2) + (u / 2 ^ st) % 2) + u % 2 ^ st := by
          congr 1; congr 1; exact hdiv2.symm
      _ = (2 ^ st * ((u / 2 ^ st) % 2) + u % 2 ^ st) + (2 ^ st * 2) * ((u / 2 ^ st) / 2) := by
          ring
  conv_lhs => rw [hu_eq]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

private def muxPrevWireNat (n st k : ℕ) : ℕ :=
  if st = 0 then k else 2 * n + (3 * ((st - 1) * n + k) + 2)

private def muxWIdx (n s k : ℕ) [NeZero n] : Fin (2 * n + s) :=
  ⟨k % (2 * n + s), Nat.mod_lt _ (Nat.add_pos_left (Nat.mul_pos (by decide) (NeZero.pos n)) s)⟩

private def muxIn1 (n m : ℕ) [NeZero n] (g : Fin (3 * (m * n))) : Fin (2 * n + 3 * (m * n)) :=
  let cell := g.val / 3
  let rem := g.val % 3
  let st := cell / n
  let j := cell % n
  if rem = 0 then muxWIdx n (3 * (m * n)) (muxPrevWireNat n st j)
  else if rem = 1 then muxWIdx n (3 * (m * n)) (muxPrevWireNat n st ((j + 2 ^ st) % n))
  else muxWIdx n (3 * (m * n)) (2 * n + 3 * cell)

private def muxIn2 (n m : ℕ) [NeZero n] (g : Fin (3 * (m * n))) : Fin (2 * n + 3 * (m * n)) :=
  let cell := g.val / 3
  let rem := g.val % 3
  let st := cell / n
  if rem = 0 then muxWIdx n (3 * (m * n)) (n + st)
  else if rem = 1 then muxWIdx n (3 * (m * n)) (n + st)
  else muxWIdx n (3 * (m * n)) (2 * n + 3 * cell + 1)

private def muxGateOp (n m : ℕ) (g : Fin (3 * (m * n))) : Bool → Bool → Bool :=
  let rem := g.val % 3
  if rem = 0 then fun a sel => a && (!sel)
  else if rem = 1 then fun b sel => b && sel
  else fun u v => u || v

private def muxXMod {n : ℕ} [NeZero n] (x : Fin n → Bool) (idx : ℕ) : Bool :=
  x ⟨idx % n, Nat.mod_lt _ (NeZero.pos n)⟩

private def muxWireVal (n m : ℕ) [NeZero n] (x : Fin n → Bool) (sh : Fin n)
    (w : Fin (2 * n + 3 * (m * n))) : Bool :=
  if w.val < n then muxXMod x w.val
  else if w.val < 2 * n then (((sh.val / 2 ^ (w.val - n)) % 2) == 1)
  else
    let gval := w.val - 2 * n
    let cell := gval / 3
    let rem := gval % 3
    let st := cell / n
    let j := cell % n
    let sel := (((sh.val / 2 ^ st) % 2) == 1)
    if rem = 0 then muxXMod x (j + sh.val % 2 ^ st) && (!sel)
    else if rem = 1 then muxXMod x ((j + 2 ^ st) % n + sh.val % 2 ^ st) && sel
    else muxXMod x (j + sh.val % 2 ^ (st + 1))

private theorem muxPrevWireNat_lt {n m st k : ℕ} (hst : st ≤ m) (hk : k < n) :
    muxPrevWireNat n st k < (if st = 0 then n else 2 * n + 3 * (st * n)) ∧
    muxPrevWireNat n st k < 2 * n + 3 * (m * n) := by
  cases st with
  | zero =>
    simp only [muxPrevWireNat, ↓reduceIte]
    exact ⟨hk, by omega⟩
  | succ st' =>
    simp only [muxPrevWireNat, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    have h1 : st' * n + k < (st' + 1) * n := by
      calc st' * n + k < st' * n + n := Nat.add_lt_add_left hk _
        _ = (st' + 1) * n := by ring
    have h2 : (st' + 1) * n ≤ m * n := Nat.mul_le_mul_right n hst
    exact ⟨by omega, by omega⟩

private theorem muxPrevWire_val {n m : ℕ} [NeZero n] (x : Fin n → Bool) (sh : Fin n)
    {st k : ℕ} (hst : st ≤ m) (hk : k < n) :
    muxWireVal n m x sh (muxWIdx n (3 * (m * n)) (muxPrevWireNat n st k)) =
      muxXMod x (k + sh.val % 2 ^ st) := by
  have hn_pos := NeZero.pos n
  have hpW := (muxPrevWireNat_lt (m := m) hst hk).2
  have hw_val : (muxWIdx n (3 * (m * n)) (muxPrevWireNat n st k)).val = muxPrevWireNat n st k :=
    Nat.mod_eq_of_lt hpW
  cases st with
  | zero =>
    have hp0 : muxPrevWireNat n 0 k = k := rfl
    unfold muxWireVal
    rw [ite_pos (by rw [hw_val, hp0]; exact hk), hw_val, hp0, pow_zero, Nat.mod_one, add_zero]
  | succ st' =>
    have hp1 : muxPrevWireNat n (st' + 1) k = 2 * n + (3 * (st' * n + k) + 2) := rfl
    have hn1 : ¬ (muxWIdx n (3 * (m * n)) (muxPrevWireNat n (st' + 1) k)).val < n := by
      rw [hw_val, hp1]; omega
    have hn2 : ¬ (muxWIdx n (3 * (m * n)) (muxPrevWireNat n (st' + 1) k)).val < 2 * n := by
      rw [hw_val, hp1]; omega
    unfold muxWireVal
    rw [ite_neg hn1, ite_neg hn2]
    dsimp only
    have hsub : (muxWIdx n (3 * (m * n)) (muxPrevWireNat n (st' + 1) k)).val - 2 * n =
        3 * (st' * n + k) + 2 := by rw [hw_val, hp1]; omega
    have hd3 : (3 * (st' * n + k) + 2) / 3 = st' * n + k := by omega
    have hm3 : (3 * (st' * n + k) + 2) % 3 = 2 := by omega
    have hdn : (st' * n + k) / n = st' := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn_pos, Nat.div_eq_of_lt hk, zero_add]
    have hmn : (st' * n + k) % n = k := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk]
    rw [hsub, hd3, hm3, hdn, hmn]
    rfl

private theorem barrelShiftCircuit_explicit :
    ∃ C_sh : ℝ, 0 < C_sh ∧
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∃ s : ℕ, (s : ℝ) ≤ C_sh * (n : ℝ) * (Real.log (n : ℝ) / Real.log 2) ∧
          HasBarrelShiftCircuit n s := by
  refine ⟨6, by norm_num, fun n _ hn2 => ?_⟩
  have hn_pos : 0 < n := NeZero.pos n
  let m : ℕ := Nat.clog 2 n
  have hm_pos : 0 < m := (Nat.lt_clog_iff_pow_lt (by decide)).mpr (by simp; omega)
  have hm_le_n : m ≤ n :=
    (Nat.clog_le_iff_le_pow (by decide)).mpr (Nat.lt_two_pow_self).le
  have hn_le_2m : n ≤ 2 ^ m := Nat.le_pow_clog (by decide) n
  refine ⟨3 * (m * n), ?_, ?_⟩
  · have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h2m1_lt : 2 ^ (m - 1) < n :=
      (Nat.lt_clog_iff_pow_lt (by decide)).mp (by omega)
    have hlog_m1 : ((m - 1 : ℕ) : ℝ) * Real.log 2 ≤ Real.log (n : ℝ) := by
      have hle : (((2 ^ (m - 1) : ℕ) : ℝ)) ≤ (n : ℝ) := by exact_mod_cast h2m1_lt.le
      have hpos : (0 : ℝ) < ((2 ^ (m - 1) : ℕ) : ℝ) := by positivity
      have hlog := Real.log_le_log hpos hle
      simpa [Real.log_pow] using hlog
    have hlog_1 : Real.log 2 ≤ Real.log (n : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hn2)
    have hm_cast : (m : ℝ) = ((m - 1 : ℕ) : ℝ) + 1 := by
      exact_mod_cast (Nat.sub_add_cancel hm_pos).symm
    have hm_log : (m : ℝ) ≤ 2 * (Real.log (n : ℝ) / Real.log 2) := by
      rw [mul_div_assoc', le_div_iff₀ hlog2]
      nlinarith
    have hs_cast : ((3 * (m * n) : ℕ) : ℝ) = 3 * (n : ℝ) * (m : ℝ) := by
      push_cast; ring
    rw [hs_cast]
    nlinarith
  · refine ⟨muxIn1 n m, muxIn2 n m, muxGateOp n m,
      fun j => muxWIdx n (3 * (m * n)) (muxPrevWireNat n m j.val), ?_, ?_⟩
    · intro g
      have hg_lt : g.val < 3 * (m * n) := g.isLt
      have hcell_lt : g.val / 3 < m * n := by omega
      have hst_lt : (g.val / 3) / n < m := Nat.div_lt_of_lt_mul (by linarith)
      have hj_lt : (g.val / 3) % n < n := Nat.mod_lt _ hn_pos
      have hst_n : ((g.val / 3) / n) * n ≤ g.val / 3 := by
        calc ((g.val / 3) / n) * n = n * ((g.val / 3) / n) := Nat.mul_comm _ _
          _ ≤ g.val / 3 := Nat.mul_div_le _ _
      have hst_le_n : (g.val / 3) / n < n := hst_lt.trans_le hm_le_n
      have hp_j := muxPrevWireNat_lt (m := m) hst_lt.le hj_lt
      have hp_sh := muxPrevWireNat_lt (m := m) hst_lt.le
        (Nat.mod_lt ((g.val / 3) % n + 2 ^ ((g.val / 3) / n)) hn_pos)
      have hsel_W : n + (g.val / 3) / n < 2 * n + 3 * (m * n) := by omega
      have hsel_g : n + (g.val / 3) / n < 2 * n + g.val := by omega
      have hpj_g : muxPrevWireNat n ((g.val / 3) / n) ((g.val / 3) % n) < 2 * n + g.val := by
        have h1 := hp_j.1; split_ifs at h1 <;> omega
      have hpsh_g : muxPrevWireNat n ((g.val / 3) / n)
          (((g.val / 3) % n + 2 ^ ((g.val / 3) / n)) % n) < 2 * n + g.val := by
        have h1 := hp_sh.1; split_ifs at h1 <;> omega
      unfold muxIn1 muxIn2
      dsimp only
      rcases (by omega : g.val % 3 = 0 ∨ g.val % 3 = 1 ∨ g.val % 3 = 2) with hr0 | hr1 | hr2
      · rw [ite_pos hr0, ite_pos hr0]
        dsimp [muxWIdx]
        rw [Nat.mod_eq_of_lt hp_j.2, Nat.mod_eq_of_lt hsel_W]
        exact ⟨hpj_g, hsel_g⟩
      · have hne0 : (1 : ℕ) ≠ 0 := by decide
        rw [ite_neg (by rw [hr1]; exact hne0), ite_pos hr1,
          ite_neg (by rw [hr1]; exact hne0), ite_pos hr1]
        dsimp [muxWIdx]
        rw [Nat.mod_eq_of_lt hp_sh.2, Nat.mod_eq_of_lt hsel_W]
        exact ⟨hpsh_g, hsel_g⟩
      · have hne0 : (2 : ℕ) ≠ 0 := by decide
        have hne1 : (2 : ℕ) ≠ 1 := by decide
        rw [ite_neg (by rw [hr2]; exact hne0), ite_neg (by rw [hr2]; exact hne1),
          ite_neg (by rw [hr2]; exact hne0), ite_neg (by rw [hr2]; exact hne1)]
        dsimp [muxWIdx]
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        exact ⟨by omega, by omega⟩
    · intro x sh
      refine ⟨muxWireVal n m x sh, ?_, ?_, ?_, ?_⟩
      · intro i
        have hiW : i.val < 2 * n + 3 * (m * n) := by omega
        have hw_eq : (muxWIdx n (3 * (m * n)) i.val).val = i.val := Nat.mod_eq_of_lt hiW
        change muxWireVal n m x sh (muxWIdx n (3 * (m * n)) i.val) = x i
        unfold muxWireVal
        rw [ite_pos (by rw [hw_eq]; exact i.isLt), hw_eq]
        unfold muxXMod
        exact congrArg x (Fin.ext (Nat.mod_eq_of_lt i.isLt))
      · intro b
        have hbW : n + b.val < 2 * n + 3 * (m * n) := by omega
        have hw_eq : (muxWIdx n (3 * (m * n)) (n + b.val)).val = n + b.val := Nat.mod_eq_of_lt hbW
        change muxWireVal n m x sh (muxWIdx n (3 * (m * n)) (n + b.val)) = _
        unfold muxWireVal
        rw [ite_neg (by rw [hw_eq]; omega), ite_pos (by rw [hw_eq]; omega),
          hw_eq, Nat.add_sub_cancel_left]
      · intro g
        change muxWireVal n m x sh (muxWIdx n (3 * (m * n)) (2 * n + g.val)) =
          muxGateOp n m g (muxWireVal n m x sh (muxIn1 n m g)) (muxWireVal n m x sh (muxIn2 n m g))
        have hg_lt : g.val < 3 * (m * n) := g.isLt
        have hgW : 2 * n + g.val < 2 * n + 3 * (m * n) := by omega
        have hgw_eq : (muxWIdx n (3 * (m * n)) (2 * n + g.val)).val = 2 * n + g.val :=
          Nat.mod_eq_of_lt hgW
        have hcell_lt : g.val / 3 < m * n := by omega
        have hst_lt : (g.val / 3) / n < m := Nat.div_lt_of_lt_mul (by linarith)
        have hj_lt : (g.val / 3) % n < n := Nat.mod_lt _ hn_pos
        have hsel_val : muxWireVal n m x sh (muxWIdx n (3 * (m * n)) (n + (g.val / 3) / n)) =
            (((sh.val / 2 ^ ((g.val / 3) / n)) % 2) == 1) := by
          have hst_n_lt : (g.val / 3) / n < n := hst_lt.trans_le hm_le_n
          have hsW : n + (g.val / 3) / n < 2 * n + 3 * (m * n) := by omega
          have hsw : (muxWIdx n (3 * (m * n)) (n + (g.val / 3) / n)).val = n + (g.val / 3) / n :=
            Nat.mod_eq_of_lt hsW
          have hn1 : ¬ (muxWIdx n (3 * (m * n)) (n + (g.val / 3) / n)).val < n := by
            rw [hsw]; exact not_lt.mpr (Nat.le_add_right _ _)
          have hn2 : (muxWIdx n (3 * (m * n)) (n + (g.val / 3) / n)).val < 2 * n := by
            rw [hsw]; omega
          unfold muxWireVal
          rw [ite_neg hn1, ite_pos hn2, hsw, Nat.add_sub_cancel_left]
        rcases (by omega : g.val % 3 = 0 ∨ g.val % 3 = 1 ∨ g.val % 3 = 2) with hr0 | hr1 | hr2
        · unfold muxIn1 muxIn2 muxGateOp
          dsimp only
          rw [ite_pos hr0, ite_pos hr0, ite_pos hr0,
            muxPrevWire_val x sh hst_lt.le hj_lt, hsel_val]
          unfold muxWireVal
          rw [ite_neg (by rw [hgw_eq]; omega), ite_neg (by rw [hgw_eq]; omega)]
          dsimp only
          rw [hgw_eq, Nat.add_sub_cancel_left, ite_pos hr0]
        · have hne0 : (1 : ℕ) ≠ 0 := by decide
          unfold muxIn1 muxIn2 muxGateOp
          dsimp only
          rw [ite_neg (by rw [hr1]; exact hne0), ite_pos hr1,
            ite_neg (by rw [hr1]; exact hne0), ite_pos hr1,
            ite_neg (by rw [hr1]; exact hne0), ite_pos hr1,
            muxPrevWire_val x sh hst_lt.le (Nat.mod_lt _ hn_pos), hsel_val]
          unfold muxWireVal
          rw [ite_neg (by rw [hgw_eq]; omega), ite_neg (by rw [hgw_eq]; omega)]
          dsimp only
          rw [hgw_eq, Nat.add_sub_cancel_left, ite_neg (by rw [hr1]; exact hne0), ite_pos hr1]
        · have hne0 : (2 : ℕ) ≠ 0 := by decide
          have hne1 : (2 : ℕ) ≠ 1 := by decide
          unfold muxIn1 muxIn2 muxGateOp
          dsimp only
          rw [ite_neg (by rw [hr2]; exact hne0), ite_neg (by rw [hr2]; exact hne1),
            ite_neg (by rw [hr2]; exact hne0), ite_neg (by rw [hr2]; exact hne1),
            ite_neg (by rw [hr2]; exact hne0), ite_neg (by rw [hr2]; exact hne1)]
          set cell := g.val / 3
          set st := cell / n
          set j := cell % n
          have hv0 : muxWireVal n m x sh (muxWIdx n (3 * (m * n)) (2 * n + 3 * cell)) =
              (muxXMod x (j + sh.val % 2 ^ st) &&
                !(((sh.val / 2 ^ st) % 2) == 1)) := by
            have hw0 : (muxWIdx n (3 * (m * n)) (2 * n + 3 * cell)).val = 2 * n + 3 * cell :=
              Nat.mod_eq_of_lt (by omega)
            unfold muxWireVal
            rw [ite_neg (by rw [hw0]; omega), ite_neg (by rw [hw0]; omega)]
            dsimp only
            have hsub : (muxWIdx n (3 * (m * n)) (2 * n + 3 * cell)).val - 2 * n = 3 * cell := by
              rw [hw0]; omega
            have hd3 : (3 * cell) / 3 = cell := by omega
            have hm3 : (3 * cell) % 3 = 0 := by omega
            rw [hsub, hd3, ite_pos hm3]
          have hv1 : muxWireVal n m x sh (muxWIdx n (3 * (m * n)) (2 * n + 3 * cell + 1)) =
              (muxXMod x ((j + 2 ^ st) % n + sh.val % 2 ^ st) &&
                (((sh.val / 2 ^ st) % 2) == 1)) := by
            have hw1 : (muxWIdx n (3 * (m * n)) (2 * n + 3 * cell + 1)).val =
                2 * n + 3 * cell + 1 := Nat.mod_eq_of_lt (by omega)
            unfold muxWireVal
            rw [ite_neg (by rw [hw1]; omega), ite_neg (by rw [hw1]; omega)]
            dsimp only
            have hsub : (muxWIdx n (3 * (m * n)) (2 * n + 3 * cell + 1)).val - 2 * n =
                3 * cell + 1 := by rw [hw1]; omega
            have hd3 : (3 * cell + 1) / 3 = cell := by omega
            have hm3 : (3 * cell + 1) % 3 = 1 := by omega
            have h1ne0 : (1 : ℕ) ≠ 0 := by decide
            rw [hsub, hd3, ite_neg (by rw [hm3]; exact h1ne0), ite_pos hm3]
          have hv2 : muxWireVal n m x sh (muxWIdx n (3 * (m * n)) (2 * n + g.val)) =
              muxXMod x (j + sh.val % 2 ^ (st + 1)) := by
            unfold muxWireVal
            rw [ite_neg (by rw [hgw_eq]; omega), ite_neg (by rw [hgw_eq]; omega)]
            dsimp only
            rw [hgw_eq, Nat.add_sub_cancel_left,
              ite_neg (by rw [hr2]; exact hne0), ite_neg (by rw [hr2]; exact hne1)]
          rw [hv0, hv1, hv2]
          have hmod_succ := mod_two_pow_succ_eq sh.val st
          rcases (by have := Nat.mod_lt (sh.val / 2 ^ st) (by decide : 0 < 2); omega :
              (sh.val / 2 ^ st) % 2 = 0 ∨ (sh.val / 2 ^ st) % 2 = 1) with hb0 | hb1
          · simp only [hb0, Nat.mul_zero, zero_add] at hmod_succ ⊢
            rw [hmod_succ]
            simp
          · simp only [hb1, Nat.mul_one] at hmod_succ ⊢
            rw [hmod_succ]
            simp only [beq_self_eq_true, Bool.not_true, Bool.and_false, Bool.and_true,
              Bool.false_or]
            unfold muxXMod
            apply congrArg x
            apply Fin.ext
            dsimp only
            rw [← Nat.add_assoc, ← Nat.mod_add_mod]
      · intro j
        change muxWireVal n m x sh (muxWIdx n (3 * (m * n)) (muxPrevWireNat n m j.val)) = _
        rw [muxPrevWire_val x sh le_rfl j.isLt]
        have hsh_lt : sh.val < 2 ^ m := sh.isLt.trans_le hn_le_2m
        unfold muxXMod
        rw [Nat.mod_eq_of_lt hsh_lt]

/-! #### Top-Level Network Embedding Definitions for Part 1 -/

private def netV (n s : ℕ) : ℕ := n + (2 * n + s) + (2 * s + n) + n

private def netSrc (n s : ℕ) (i : Fin n) : Fin (netV n s) :=
  ⟨i.val, by have := i.isLt; dsimp [netV]; omega⟩

private def netOrig (n s : ℕ) (w : Fin (2 * n + s)) : Fin (netV n s) :=
  ⟨n + w.val, by have := w.isLt; dsimp [netV]; omega⟩

private def netRelay (n s : ℕ) (p : Fin (2 * s + n)) : Fin (netV n s) :=
  ⟨n + (2 * n + s) + p.val, by have := p.isLt; dsimp [netV]; omega⟩

private def netSink (n s : ℕ) (j : Fin n) : Fin (netV n s) :=
  ⟨n + (2 * n + s) + (2 * s + n) + j.val, by have := j.isLt; dsimp [netV]; omega⟩

private def netPortWire {n s : ℕ} (in1 in2 : Fin s → Fin (2 * n + s))
    (outWire : Fin n → Fin (2 * n + s)) (p : Fin (2 * s + n)) : Fin (2 * n + s) :=
  if hp : p.val < 2 * s then
    let g : Fin s := ⟨p.val / 2, by omega⟩
    if p.val % 2 = 0 then in1 g else in2 g
  else outWire ⟨p.val - 2 * s, by have := p.isLt; omega⟩

private def netPortConsumer (n s : ℕ) (p : Fin (2 * s + n)) : Fin (netV n s) :=
  if hp : p.val < 2 * s then netOrig n s ⟨2 * n + p.val / 2, by omega⟩
  else netSink n s ⟨p.val - 2 * s, by have := p.isLt; omega⟩

private def netPrevPorts {n s : ℕ} (in1 in2 : Fin s → Fin (2 * n + s))
    (outWire : Fin n → Fin (2 * n + s)) (p : Fin (2 * s + n)) : Finset (Fin (2 * s + n)) :=
  Finset.univ.filter (fun q =>
    q < p ∧ netPortWire in1 in2 outWire q = netPortWire in1 in2 outWire p)

private def netRelayPred {n s : ℕ} (in1 in2 : Fin s → Fin (2 * n + s))
    (outWire : Fin n → Fin (2 * n + s)) (p : Fin (2 * s + n)) : Fin (netV n s) :=
  if h : (netPrevPorts in1 in2 outWire p).Nonempty then
    netRelay n s ((netPrevPorts in1 in2 outWire p).max' h)
  else netOrig n s (netPortWire in1 in2 outWire p)

private def netTopo {n s : ℕ} (in1 in2 : Fin s → Fin (2 * n + s))
    (outWire : Fin n → Fin (2 * n + s)) (u : Fin (netV n s)) : ℕ :=
  let W := 2 * n + s
  let P := 2 * s + n
  if u.val < n then 0
  else if u.val < n + W then (u.val - n) * (P + 2) + 1
  else if hp : u.val < n + W + P then
    let p : Fin P := ⟨u.val - (n + W), by omega⟩
    (netPortWire in1 in2 outWire p).val * (P + 2) + 2 + p.val
  else W * (P + 2) + 1

private def netDirEdge {n s : ℕ} (in1 in2 : Fin s → Fin (2 * n + s))
    (outWire : Fin n → Fin (2 * n + s)) (u v : Fin (netV n s)) : Prop :=
  (∃ i : Fin n, u = netSrc n s i ∧ v = netOrig n s ⟨i.val, by have := i.isLt; omega⟩) ∨
  (∃ p : Fin (2 * s + n), u = netRelayPred in1 in2 outWire p ∧ v = netRelay n s p) ∨
  (∃ p : Fin (2 * s + n), u = netRelay n s p ∧ v = netPortConsumer n s p)

private noncomputable def netAdj {n s : ℕ} (in1 in2 : Fin s → Fin (2 * n + s))
    (outWire : Fin n → Fin (2 * n + s)) (u : Fin (netV n s)) : Finset (Fin (netV n s)) :=
  open Classical in
  Finset.univ.filter (fun v =>
    netDirEdge in1 in2 outWire u v ∨ netDirEdge in1 in2 outWire v u)

private def graphBall {V : ℕ} (adj : Fin V → Finset (Fin V)) : ℕ → Fin V → Finset (Fin V)
  | 0, u => {u}
  | t + 1, u => {u} ∪ (adj u).biUnion (fun b => graphBall adj t b)

private theorem self_mem_graphBall {V : ℕ} (adj : Fin V → Finset (Fin V)) (t : ℕ) (u : Fin V) :
    u ∈ graphBall adj t u := by
  cases t with
  | zero => exact Finset.mem_singleton_self u
  | succ _ => exact Finset.mem_union_left _ (Finset.mem_singleton_self u)

private theorem card_graphBall_le {V : ℕ} (adj : Fin V → Finset (Fin V))
    (hdeg : ∀ u : Fin V, (adj u).card ≤ 4) :
    ∀ (t : ℕ) (u : Fin V), (graphBall adj t u).card ≤ 5 ^ t
  | 0, u => by simp [graphBall]
  | t + 1, u => by
    simp only [graphBall]
    calc ({u} ∪ (adj u).biUnion (fun b => graphBall adj t b)).card
        ≤ ({u} : Finset (Fin V)).card + ((adj u).biUnion (fun b => graphBall adj t b)).card :=
          Finset.card_union_le _ _
      _ ≤ 1 + ∑ b ∈ adj u, (graphBall adj t b).card := by
          rw [Finset.card_singleton]
          exact Nat.add_le_add_left Finset.card_biUnion_le 1
      _ ≤ 1 + ∑ _b ∈ adj u, 5 ^ t :=
          Nat.add_le_add_left (Finset.sum_le_sum fun b _ => card_graphBall_le adj hdeg t b) 1
      _ = 1 + (adj u).card * 5 ^ t := by simp
      _ ≤ 1 + 4 * 5 ^ t := Nat.add_le_add_left (Nat.mul_le_mul_right _ (hdeg u)) 1
      _ ≤ 5 ^ t + 4 * 5 ^ t := Nat.add_le_add_right (Nat.one_le_pow t 5 (by decide)) _
      _ = 5 ^ (t + 1) := by rw [pow_succ]; ring

private theorem walk_mem_graphBall {V : ℕ} (adj : Fin V → Finset (Fin V)) :
    ∀ (walk : List (Fin V)) (t : ℕ) (u v : Fin V),
      walk.head? = some u →
      walk.getLast? = some v →
      (∀ idx : ℕ, ∀ h : idx + 1 < walk.length,
        walk.get ⟨idx + 1, h⟩ ∈ adj (walk.get ⟨idx, Nat.lt_of_succ_lt h⟩)) →
      walk.length ≤ t + 1 →
      v ∈ graphBall adj t u
  | [], _, _, _, hh, _, _, _ => by simp at hh
  | [a], t, u, v, hh, hl, _, _ => by
    simp only [List.head?_cons, List.getLast?_singleton, Option.some.injEq] at hh hl
    subst hh; subst hl
    exact self_mem_graphBall adj t a
  | _ :: _ :: _, 0, _, _, _, _, _, hlen => by
    simp only [List.length_cons] at hlen
    omega
  | a :: b :: rest, t + 1, u, v, hh, hl, hstep, hlen => by
    simp only [List.head?_cons, Option.some.injEq] at hh
    subst hh
    have hb_adj : b ∈ adj a := hstep 0 (by simp)
    have hstep' : ∀ idx : ℕ, ∀ h : idx + 1 < (b :: rest).length,
        (b :: rest).get ⟨idx + 1, h⟩ ∈ adj ((b :: rest).get ⟨idx, Nat.lt_of_succ_lt h⟩) :=
      fun idx h => hstep (idx + 1) (Nat.add_lt_add_right h 1)
    rw [List.getLast?_cons_cons] at hl
    have hlen' : (b :: rest).length ≤ t + 1 := Nat.le_of_succ_le_succ hlen
    have hv_b : v ∈ graphBall adj t b :=
      walk_mem_graphBall adj (b :: rest) t b v rfl hl hstep' hlen'
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨b, hb_adj, hv_b⟩)

theorem diagnosis_ShiftAndRotationCodingGainBarrier :
    Diagnosis_ShiftAndRotationCodingGainBarrierSpec := by
  refine ⟨?_, barrelShiftCircuit_explicit⟩
  refine ⟨1 / 6, 1 / 60, 5, 32, by norm_num, by norm_num, by decide, by decide, ?_⟩
  intro n s _ hn32 hcir
  classical
  have hn_pos : 0 < n := NeZero.pos n
  obtain ⟨in1, in2, gateOp, outWire, hacyc, heval⟩ := hcir
  let W : ℕ := 2 * n + s
  have hW : 0 < W := by omega
  let wIdx (k : ℕ) : Fin W := ⟨k % W, Nat.mod_lt _ hW⟩
  let P : ℕ := 2 * s + n
  have hV_pos : 1 ≤ netV n s := by dsimp [netV]; omega
  have hV_le : netV n s ≤ 5 * (s + n) := by dsimp [netV]; omega
  have hsrc_inj : Function.Injective (netSrc n s) := fun i₁ i₂ h => by
    have hv := congrArg Fin.val h; exact Fin.ext hv
  have horig_inj : Function.Injective (netOrig n s) := fun w₁ w₂ h => by
    have hv := congrArg Fin.val h; dsimp [netOrig] at hv; exact Fin.ext (by omega)
  have hrelay_inj : Function.Injective (netRelay n s) := fun p₁ p₂ h => by
    have hv := congrArg Fin.val h; dsimp [netRelay] at hv; exact Fin.ext (by omega)
  have hsink_inj : Function.Injective (netSink n s) := fun j₁ j₂ h => by
    have hv := congrArg Fin.val h; dsimp [netSink] at hv; exact Fin.ext (by omega)
  have hsrc_ne_sink : ∀ i j : Fin n, netSrc n s i ≠ netSink n s j := fun i j h => by
    have hv := congrArg Fin.val h; dsimp [netSrc, netSink] at hv; omega
  have hprev_lt_wire : ∀ p : Fin P, ∀ h : (netPrevPorts in1 in2 outWire p).Nonempty,
      (netPrevPorts in1 in2 outWire p).max' h < p ∧
      netPortWire in1 in2 outWire ((netPrevPorts in1 in2 outWire p).max' h) =
        netPortWire in1 in2 outWire p := fun p h =>
    (Finset.mem_filter.mp ((netPrevPorts in1 in2 outWire p).max'_mem h)).2
  have hrelayPred_inj : Function.Injective (netRelayPred in1 in2 outWire) := by
    intro p₁ p₂ heq
    unfold netRelayPred at heq
    by_cases h1 : (netPrevPorts in1 in2 outWire p₁).Nonempty <;>
      by_cases h2 : (netPrevPorts in1 in2 outWire p₂).Nonempty
    · rw [dite_pos h1, dite_pos h2] at heq
      have hq_eq := hrelay_inj heq
      obtain ⟨hq1_lt, hq1_w⟩ := hprev_lt_wire p₁ h1
      obtain ⟨hq2_lt, hq2_w⟩ := hprev_lt_wire p₂ h2
      have hw12 : netPortWire in1 in2 outWire p₁ = netPortWire in1 in2 outWire p₂ := by
        rw [← hq1_w, hq_eq, hq2_w]
      rcases lt_trichotomy p₁ p₂ with hlt | rfl | hgt
      · have hp1_mem : p₁ ∈ netPrevPorts in1 in2 outWire p₂ :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt, hw12⟩
        have hp1_le := (netPrevPorts in1 in2 outWire p₂).le_max' p₁ hp1_mem
        rw [← hq_eq] at hp1_le
        exact absurd (hq1_lt.trans_le hp1_le) (lt_irrefl _)
      · rfl
      · have hp2_mem : p₂ ∈ netPrevPorts in1 in2 outWire p₁ :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt, hw12.symm⟩
        have hp2_le := (netPrevPorts in1 in2 outWire p₁).le_max' p₂ hp2_mem
        rw [hq_eq] at hp2_le
        exact absurd (hq2_lt.trans_le hp2_le) (lt_irrefl _)
    · rw [dite_pos h1, dite_neg h2] at heq
      have hv := congrArg Fin.val heq; dsimp [netRelay, netOrig] at hv; omega
    · rw [dite_neg h1, dite_pos h2] at heq
      have hv := congrArg Fin.val heq; dsimp [netRelay, netOrig] at hv; omega
    · rw [dite_neg h1, dite_neg h2] at heq
      have hw12 := horig_inj heq
      rcases lt_trichotomy p₁ p₂ with hlt | rfl | hgt
      · exfalso; exact h2 ⟨p₁, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt, hw12⟩⟩
      · rfl
      · exfalso; exact h1 ⟨p₂, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt, hw12.symm⟩⟩
  have htopo_src : ∀ i : Fin n, netTopo in1 in2 outWire (netSrc n s i) = 0 := fun i => by
    unfold netTopo netSrc; simp [i.isLt]
  have htopo_orig : ∀ w : Fin W,
      netTopo in1 in2 outWire (netOrig n s w) = w.val * (P + 2) + 1 := fun w => by
    unfold netTopo netOrig
    have h1 : ¬ (n + w.val < n) := by omega
    have h2 : n + w.val < n + (2 * n + s) := by have := w.isLt; omega
    simp only [h1, h2, ↓reduceIte, Nat.add_sub_cancel_left]
    rfl
  have htopo_relay : ∀ p : Fin P,
      netTopo in1 in2 outWire (netRelay n s p) =
        (netPortWire in1 in2 outWire p).val * (P + 2) + 2 + p.val := fun p => by
    unfold netTopo netRelay
    have h1 : ¬ (n + (2 * n + s) + p.val < n) := by omega
    have h2 : ¬ (n + (2 * n + s) + p.val < n + (2 * n + s)) := by omega
    have h3 : n + (2 * n + s) + p.val < n + (2 * n + s) + (2 * s + n) := by
      have := p.isLt; omega
    have hsub : n + (2 * n + s) + p.val - (n + (2 * n + s)) = p.val := by omega
    rw [ ite_neg h1, ite_neg h2, dite_pos h3 ]
    dsimp only
    congr 2
    exact congrArg (fun x => (netPortWire in1 in2 outWire x).val * (P + 2)) (Fin.ext hsub)
  have htopo_sink : ∀ j : Fin n,
      netTopo in1 in2 outWire (netSink n s j) = W * (P + 2) + 1 := fun j => by
    unfold netTopo netSink
    have h1 : ¬ (n + (2 * n + s) + (2 * s + n) + j.val < n) := by omega
    have h2 : ¬ (n + (2 * n + s) + (2 * s + n) + j.val < n + (2 * n + s)) := by omega
    have h3 : ¬ (n + (2 * n + s) + (2 * s + n) + j.val < n + (2 * n + s) + (2 * s + n)) := by
      omega
    rw [ite_neg h1, ite_neg h2, dite_neg h3]
  have hdir_topo : ∀ u v : Fin (netV n s),
      netDirEdge in1 in2 outWire u v →
      netTopo in1 in2 outWire u < netTopo in1 in2 outWire v := by
    intro u v hdir
    rcases hdir with ⟨i, rfl, rfl⟩ | ⟨p, rfl, rfl⟩ | ⟨p, rfl, rfl⟩
    · rw [htopo_src, htopo_orig]; omega
    · rw [htopo_relay]
      unfold netRelayPred
      by_cases hne : (netPrevPorts in1 in2 outWire p).Nonempty
      · rw [dite_pos hne, htopo_relay]
        obtain ⟨hlt, hweq⟩ := hprev_lt_wire p hne
        rw [hweq]
        have : ((netPrevPorts in1 in2 outWire p).max' hne).val < p.val := hlt
        omega
      · rw [dite_neg hne, htopo_orig]
        omega
    · rw [htopo_relay]
      unfold netPortConsumer
      by_cases hp : p.val < 2 * s
      · rw [dite_pos hp, htopo_orig]
        let g : Fin s := ⟨p.val / 2, by omega⟩
        have hpw_lt : (netPortWire in1 in2 outWire p).val < 2 * n + g.val := by
          unfold netPortWire
          rw [dite_pos hp]
          dsimp only
          split_ifs
          · exact (hacyc g).1
          · exact (hacyc g).2
        have hpw_le : ((netPortWire in1 in2 outWire p).val + 1) * (P + 2) ≤
            (2 * n + p.val / 2) * (P + 2) :=
          Nat.mul_le_mul_right _ (by dsimp [g] at hpw_lt; omega)
        have hp_lt_P : p.val < P := p.isLt
        dsimp only
        nlinarith
      · rw [dite_neg hp, htopo_sink]
        have hpw_lt : (netPortWire in1 in2 outWire p).val < W :=
          (netPortWire in1 in2 outWire p).isLt
        have hpw_le : ((netPortWire in1 in2 outWire p).val + 1) * (P + 2) ≤ W * (P + 2) :=
          Nat.mul_le_mul_right _ hpw_lt
        have hp_lt_P : p.val < P := p.isLt
        nlinarith
  have hadj_mem : ∀ u v : Fin (netV n s),
      v ∈ netAdj in1 in2 outWire u ↔
        (netDirEdge in1 in2 outWire u v ∨ netDirEdge in1 in2 outWire v u) := by
    intro u v
    unfold netAdj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hadj_loopless : ∀ u : Fin (netV n s), u ∉ netAdj in1 in2 outWire u := fun u hu => by
    rcases (hadj_mem u u).mp hu with h | h <;> exact lt_irrefl _ (hdir_topo u u h)
  have hadj_symm : ∀ u v : Fin (netV n s),
      v ∈ netAdj in1 in2 outWire u ↔ u ∈ netAdj in1 in2 outWire v := fun u v => by
    rw [hadj_mem, hadj_mem, or_comm]
  have hadj_orient : ∀ u v : Fin (netV n s),
      (v ∈ netAdj in1 in2 outWire u ∧
        netTopo in1 in2 outWire u < netTopo in1 in2 outWire v) ↔
      netDirEdge in1 in2 outWire u v := by
    intro u v
    rw [hadj_mem]
    constructor
    · rintro ⟨h1 | h2, hlt⟩
      · exact h1
      · exact absurd (hdir_topo v u h2) (not_lt_of_gt hlt)
    · intro h1
      exact ⟨Or.inl h1, hdir_topo u v h1⟩
  have hadj_in : ∀ w u : Fin (netV n s),
      netDirEdge in1 in2 outWire w u →
      (w ∈ netAdj in1 in2 outWire u ∧
        netTopo in1 in2 outWire w < netTopo in1 in2 outWire u) := fun w u h => by
    have h' := (hadj_orient w u).mpr h
    exact ⟨(hadj_symm _ _).mp h'.1, h'.2⟩
  let baseCandOf (u : Fin (netV n s)) : Finset (Fin (netV n s)) :=
    if hu1 : u.val < n then {netOrig n s ⟨u.val, by omega⟩}
    else if hu2 : u.val < n + W then
      let wval := u.val - n
      if hw1 : wval < n then {netSrc n s ⟨wval, hw1⟩}
      else if wval < 2 * n then ∅
      else
        let gval := wval - 2 * n
        if hg : gval < s then
          {netRelay n s ⟨2 * gval, by omega⟩, netRelay n s ⟨2 * gval + 1, by omega⟩}
        else ∅
    else if hu3 : u.val < n + W + P then
      let p : Fin P := ⟨u.val - (n + W), by omega⟩
      {netRelayPred in1 in2 outWire p, netPortConsumer n s p}
    else
      let jval := u.val - (n + W + P)
      if hj : jval < n then {netRelay n s ⟨2 * s + jval, by omega⟩} else ∅
  have hadj_deg : ∀ u : Fin (netV n s), (netAdj in1 in2 outWire u).card ≤ 4 := by
    intro u
    let nextRelaySet : Finset (Fin (netV n s)) :=
      (Finset.univ.filter (fun p : Fin P => netRelayPred in1 in2 outWire p = u)).image
        (netRelay n s)
    have hnext_card : nextRelaySet.card ≤ 1 := by
      calc nextRelaySet.card
          ≤ (Finset.univ.filter (fun p : Fin P => netRelayPred in1 in2 outWire p = u)).card :=
            Finset.card_image_le
        _ ≤ 1 := Finset.card_le_one.mpr (fun p₁ hp₁ p₂ hp₂ =>
            hrelayPred_inj ((Finset.mem_filter.mp hp₁).2.trans (Finset.mem_filter.mp hp₂).2.symm))
    have hbase_card : (baseCandOf u).card ≤ 2 := by
      dsimp only [baseCandOf]
      split_ifs
      · simp
      · simp
      · simp
      · exact Finset.card_insert_le _ _
      · simp
      · exact Finset.card_insert_le _ _
      · simp
      · simp
    have hsub : netAdj in1 in2 outWire u ⊆ baseCandOf u ∪ nextRelaySet := by
      intro v hv
      have hdir_or := (hadj_mem u v).mp hv
      rw [Finset.mem_union]
      rcases hdir_or with (⟨i, rfl, rfl⟩ | ⟨p, rfl, rfl⟩ | ⟨p, rfl, rfl⟩) |
          (⟨i, rfl, rfl⟩ | ⟨p, rfl, rfl⟩ | ⟨p, rfl, rfl⟩)
      · left
        have hi : (netSrc n s i).val < n := i.isLt
        dsimp only [baseCandOf]
        rw [dite_pos hi]
        exact Finset.mem_singleton_self _
      · right
        exact Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩, rfl⟩
      · left
        have h1 : ¬ (netRelay n s p).val < n := by dsimp [netRelay]; omega
        have h2 : ¬ (netRelay n s p).val < n + W := by dsimp [netRelay, W]; omega
        have h3 : (netRelay n s p).val < n + W + P := by
          have := p.isLt; dsimp [netRelay, W, P]; omega
        have hp_eq : (⟨(netRelay n s p).val - (n + W), by omega⟩ : Fin P) = p :=
          Fin.ext (by dsimp [netRelay, W]; omega)
        dsimp only [baseCandOf]
        rw [dite_neg h1, dite_neg h2, dite_pos h3, hp_eq]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      · left
        let wi : Fin W := ⟨i.val, by have := i.isLt; omega⟩
        change netSrc n s i ∈ baseCandOf (netOrig n s wi)
        have h1 : ¬ (netOrig n s wi).val < n := by dsimp [netOrig, wi]; omega
        have h2 : (netOrig n s wi).val < n + W := by
          have := i.isLt; dsimp [netOrig, wi, W]; omega
        have hw1 : (netOrig n s wi).val - n < n := by
          have := i.isLt; dsimp [netOrig, wi]; omega
        dsimp only [baseCandOf]
        rw [dite_neg h1, dite_pos h2, dite_pos hw1, Finset.mem_singleton]
        exact congrArg (netSrc n s) (Fin.ext (by dsimp [netOrig, wi]; omega))
      · left
        have h1 : ¬ (netRelay n s p).val < n := by dsimp [netRelay]; omega
        have h2 : ¬ (netRelay n s p).val < n + W := by dsimp [netRelay, W]; omega
        have h3 : (netRelay n s p).val < n + W + P := by
          have := p.isLt; dsimp [netRelay, W, P]; omega
        have hp_eq : (⟨(netRelay n s p).val - (n + W), by omega⟩ : Fin P) = p :=
          Fin.ext (by dsimp [netRelay, W]; omega)
        dsimp only [baseCandOf]
        rw [dite_neg h1, dite_neg h2, dite_pos h3, hp_eq]
        exact Finset.mem_insert_self _ _
      · left
        by_cases hp : p.val < 2 * s
        · let wp : Fin W := ⟨2 * n + p.val / 2, by omega⟩
          have hcons : netPortConsumer n s p = netOrig n s wp := by
            unfold netPortConsumer; rw [dite_pos hp]
          rw [hcons]
          have h1 : ¬ (netOrig n s wp).val < n := by dsimp [netOrig, wp]; omega
          have h2 : (netOrig n s wp).val < n + W := by dsimp [netOrig, wp, W]; omega
          have hw1 : ¬ (netOrig n s wp).val - n < n := by dsimp [netOrig, wp]; omega
          have hw2 : ¬ (netOrig n s wp).val - n < 2 * n := by dsimp [netOrig, wp]; omega
          have hg : (netOrig n s wp).val - n - 2 * n < s := by dsimp [netOrig, wp]; omega
          dsimp only [baseCandOf]
          rw [dite_neg h1, dite_pos h2, dite_neg hw1, ite_neg hw2, dite_pos hg,
            Finset.mem_insert, Finset.mem_singleton]
          have hgval : (netOrig n s wp).val - n - 2 * n = p.val / 2 := by
            dsimp [netOrig, wp]; omega
          rcases (by omega : p.val = 2 * (p.val / 2) ∨ p.val = 2 * (p.val / 2) + 1) with h0 | h1'
          · left; exact congrArg (netRelay n s) (Fin.ext (by dsimp only; omega))
          · right; exact congrArg (netRelay n s) (Fin.ext (by dsimp only; omega))
        · let jp : Fin n := ⟨p.val - 2 * s, by have := p.isLt; omega⟩
          have hcons : netPortConsumer n s p = netSink n s jp := by
            unfold netPortConsumer; rw [dite_neg hp]
          rw [hcons]
          have hp_lt_P : p.val < 2 * s + n := p.isLt
          have h1 : ¬ (netSink n s jp).val < n := by dsimp [netSink, jp]; omega
          have h2 : ¬ (netSink n s jp).val < n + W := by dsimp [netSink, jp, W]; omega
          have h3 : ¬ (netSink n s jp).val < n + W + P := by dsimp [netSink, jp, W, P]; omega
          have hj : (netSink n s jp).val - (n + W + P) < n := by
            dsimp [netSink, jp, W, P]; omega
          dsimp only [baseCandOf]
          rw [dite_neg h1, dite_neg h2, dite_neg h3, dite_pos hj, Finset.mem_singleton]
          exact congrArg (netRelay n s) (Fin.ext (by dsimp [netSink, jp, W, P]; omega))
    calc (netAdj in1 in2 outWire u).card ≤ (baseCandOf u ∪ nextRelaySet).card :=
          Finset.card_le_card hsub
      _ ≤ (baseCandOf u).card + nextRelaySet.card := Finset.card_union_le _ _
      _ ≤ 2 + 1 := Nat.add_le_add hbase_card hnext_card
      _ ≤ 4 := by decide
  -- Causal Complete Exchange Code
  have hexchange : HasCausalCompleteExchangeCode (netAdj in1 in2 outWire)
      (netSrc n s) (netSink n s) := by
    refine ⟨hsrc_inj, hsink_inj, hsrc_ne_sink, ?_⟩
    let edgeFn (r : Fin n) (u _v : Fin (netV n s))
        (inBits : Fin (netV n s) → Bool) (msgAtU : Fin n → Bool) : Bool :=
      if _hu1 : u.val < n then
        msgAtU ⟨(u.val + (n - r.val)) % n, Nat.mod_lt _ hn_pos⟩
      else if hu2 : u.val < n + W then
        let wval := u.val - n
        if hw1 : wval < n then inBits (netSrc n s ⟨wval, hw1⟩)
        else if wval < 2 * n then (((r.val / 2 ^ (wval - n)) % 2) == 1)
        else
          let gval := wval - 2 * n
          if hg : gval < s then
            gateOp ⟨gval, hg⟩ (inBits (netRelay n s ⟨2 * gval, by omega⟩))
              (inBits (netRelay n s ⟨2 * gval + 1, by omega⟩))
          else false
      else if hu3 : u.val < n + W + P then
        inBits (netRelayPred in1 in2 outWire ⟨u.val - (n + W), by omega⟩)
      else false
    let roundOf (i j : Fin n) : Fin n := ⟨(i.val + (n - j.val)) % n, Nat.mod_lt _ hn_pos⟩
    let sinkFn (j _r : Fin n) (inBits : Fin (netV n s) → Bool) : Bool :=
      inBits (netRelay n s ⟨2 * s + j.val, by omega⟩)
    refine ⟨netTopo in1 in2 outWire, edgeFn, roundOf, sinkFn, fun msg => ?_⟩
    let x_vec (r : Fin n) (i : Fin n) : Bool :=
      msg i ⟨(i.val + (n - r.val)) % n, Nat.mod_lt _ hn_pos⟩
    choose wireVal hw_in hw_sh hw_gate hw_out using fun r : Fin n => heval (x_vec r) r
    let nodeVal (r : Fin n) (u : Fin (netV n s)) : Bool :=
      if hu1 : u.val < n then x_vec r ⟨u.val, hu1⟩
      else if hu2 : u.val < n + W then wireVal r ⟨u.val - n, by omega⟩
      else if hu3 : u.val < n + W + P then
        wireVal r (netPortWire in1 in2 outWire ⟨u.val - (n + W), by omega⟩)
      else false
    have hnode_src : ∀ r i, nodeVal r (netSrc n s i) = x_vec r i := fun r i => by
      dsimp [nodeVal, netSrc]; rw [dite_pos i.isLt]
    have hnode_orig : ∀ r w, nodeVal r (netOrig n s w) = wireVal r w := fun r w => by
      dsimp only [nodeVal]
      have h1 : ¬ (netOrig n s w).val < n := by dsimp [netOrig]; omega
      have h2 : (netOrig n s w).val < n + W := by have := w.isLt; dsimp [netOrig, W]; omega
      rw [dite_neg h1, dite_pos h2]
      exact congrArg (wireVal r) (Fin.ext (by dsimp [netOrig]; omega))
    have hnode_relay : ∀ r p,
        nodeVal r (netRelay n s p) = wireVal r (netPortWire in1 in2 outWire p) := fun r p => by
      dsimp only [nodeVal]
      have h1 : ¬ (netRelay n s p).val < n := by dsimp [netRelay]; omega
      have h2 : ¬ (netRelay n s p).val < n + W := by dsimp [netRelay, W]; omega
      have h3 : (netRelay n s p).val < n + W + P := by
        have := p.isLt; dsimp [netRelay, W, P]; omega
      rw [dite_neg h1, dite_neg h2, dite_pos h3]
      exact congrArg (fun q => wireVal r (netPortWire in1 in2 outWire q))
        (Fin.ext (by dsimp [netRelay, W]; omega))
    have hnode_relayPred : ∀ r p,
        nodeVal r (netRelayPred in1 in2 outWire p) =
          wireVal r (netPortWire in1 in2 outWire p) := fun r p => by
      unfold netRelayPred
      by_cases hne : (netPrevPorts in1 in2 outWire p).Nonempty
      · rw [dite_pos hne, hnode_relay, (hprev_lt_wire p hne).2]
      · rw [dite_neg hne, hnode_orig]
    refine ⟨fun r u _v => nodeVal r u, ?_, ?_⟩
    · intro r u v hv hlt
      dsimp only
      by_cases hu1 : u.val < n
      · let i : Fin n := ⟨u.val, hu1⟩
        have hu_eq : u = netSrc n s i := rfl
        rw [hu_eq, hnode_src]
        dsimp only [edgeFn]
        rw [dite_pos (by dsimp [netSrc]; exact i.isLt)]
        have hany : ∀ k : Fin n,
            ((List.finRange n).any fun i' =>
              decide (netSrc n s i' = netSrc n s i) && msg i' k) = msg i k := by
          intro k
          cases hmk : msg i k
          · rw [Bool.eq_false_iff]
            intro hany_true
            rw [List.any_eq_true] at hany_true
            obtain ⟨i', _, hi'⟩ := hany_true
            rw [Bool.and_eq_true, decide_eq_true_eq] at hi'
            have hii' : i' = i := hsrc_inj hi'.1
            subst hii'
            rw [hmk] at hi'
            exact Bool.false_ne_true hi'.2
          · rw [List.any_eq_true]
            exact ⟨i, List.mem_finRange i, by simp [hmk]⟩
        exact (hany _).symm
      · by_cases hu2 : u.val < n + W
        · let w : Fin W := ⟨u.val - n, by omega⟩
          have hu_eq : u = netOrig n s w := Fin.ext (by dsimp [netOrig, w]; omega)
          rw [hu_eq, hnode_orig]
          dsimp only [edgeFn]
          have hn1 : ¬ (netOrig n s w).val < n := by dsimp [netOrig]; omega
          have hn2 : (netOrig n s w).val < n + W := by have := w.isLt; dsimp [netOrig, W]; omega
          have hsub : (netOrig n s w).val - n = w.val := by dsimp [netOrig]; omega
          rw [dite_neg hn1, dite_pos hn2]
          by_cases hw1 : w.val < n
          · rw [dite_pos (by rw [hsub]; exact hw1)]
            let i : Fin n := ⟨w.val, hw1⟩
            have hi_eq : (⟨(netOrig n s w).val - n, by rw [hsub]; exact hw1⟩ : Fin n) = i :=
              Fin.ext hsub
            rw [hi_eq]
            have horig_i : (⟨i.val, by omega⟩ : Fin W) = w := Fin.ext rfl
            have hin_cond := hadj_in (netSrc n s i) (netOrig n s w)
              (Or.inl ⟨i, rfl, congrArg (netOrig n s) horig_i⟩)
            rw [ite_pos hin_cond, hnode_src]
            have hw_eq := hw_in r i
            dsimp only at hw_eq
            rw [← hw_eq]
            exact congrArg (wireVal r) (Fin.ext (Nat.mod_eq_of_lt w.isLt).symm)
          · rw [dite_neg (by rw [hsub]; exact hw1)]
            by_cases hw2 : w.val < 2 * n
            · rw [ite_pos (by rw [hsub]; exact hw2), hsub]
              let b : Fin n := ⟨w.val - n, by omega⟩
              have hwb : n + b.val = w.val := by dsimp [b]; omega
              have hw_eq := hw_sh r b
              dsimp only at hw_eq
              rw [hwb] at hw_eq
              rw [← hw_eq]
              exact congrArg (wireVal r) (Fin.ext (Nat.mod_eq_of_lt w.isLt).symm)
            · rw [ite_neg (by rw [hsub]; exact hw2)]
              have hg : w.val - 2 * n < s := by have := w.isLt; omega
              rw [dite_pos (by rw [hsub]; exact hg)]
              let g : Fin s := ⟨w.val - 2 * n, hg⟩
              let p0 : Fin P := ⟨2 * g.val, by omega⟩
              let p1 : Fin P := ⟨2 * g.val + 1, by omega⟩
              have hwg : 2 * n + g.val = w.val := by dsimp [g]; omega
              have hg_eq : (⟨(netOrig n s w).val - n - 2 * n, by rw [hsub]; exact hg⟩ : Fin s) = g :=
                Fin.ext (by dsimp only; rw [hsub])
              have hp0_eq : (⟨2 * ((netOrig n s w).val - n - 2 * n), by omega⟩ : Fin P) = p0 :=
                Fin.ext (by dsimp only; rw [hsub])
              have hp1_eq : (⟨2 * ((netOrig n s w).val - n - 2 * n) + 1, by omega⟩ : Fin P) = p1 :=
                Fin.ext (by dsimp only; rw [hsub])
              rw [hg_eq, hp0_eq, hp1_eq]
              have hcons0 : netPortConsumer n s p0 = netOrig n s w := by
                unfold netPortConsumer
                rw [dite_pos (by dsimp [p0]; omega)]
                exact congrArg (netOrig n s) (Fin.ext (by dsimp [p0]; omega))
              have hcons1 : netPortConsumer n s p1 = netOrig n s w := by
                unfold netPortConsumer
                rw [dite_pos (by dsimp [p1]; omega)]
                exact congrArg (netOrig n s) (Fin.ext (by dsimp [p1]; omega))
              have hin0 := hadj_in (netRelay n s p0) (netOrig n s w)
                (Or.inr (Or.inr ⟨p0, rfl, hcons0.symm⟩))
              have hin1 := hadj_in (netRelay n s p1) (netOrig n s w)
                (Or.inr (Or.inr ⟨p1, rfl, hcons1.symm⟩))
              have hpw0 : netPortWire in1 in2 outWire p0 = in1 g := by
                unfold netPortWire
                rw [dite_pos (by dsimp [p0]; omega)]
                dsimp only
                rw [ite_pos (by dsimp [p0]; omega)]
                exact congrArg in1 (Fin.ext (by dsimp [p0]; omega))
              have hpw1 : netPortWire in1 in2 outWire p1 = in2 g := by
                unfold netPortWire
                rw [dite_pos (by dsimp [p1]; omega)]
                dsimp only
                rw [ite_neg (by dsimp [p1]; omega)]
                exact congrArg in2 (Fin.ext (by dsimp [p1]; omega))
              rw [ite_pos hin0, ite_pos hin1, hnode_relay, hnode_relay, hpw0, hpw1]
              have hw_eq := hw_gate r g
              dsimp only at hw_eq
              rw [hwg] at hw_eq
              rw [← hw_eq]
              exact congrArg (wireVal r) (Fin.ext (Nat.mod_eq_of_lt w.isLt).symm)
        · by_cases hu3 : u.val < n + W + P
          · let p : Fin P := ⟨u.val - (n + W), by omega⟩
            have hu_eq : u = netRelay n s p := Fin.ext (by dsimp [netRelay, W, p]; omega)
            rw [hu_eq, hnode_relay]
            dsimp only [edgeFn]
            have hn1 : ¬ (netRelay n s p).val < n := by dsimp [netRelay]; omega
            have hn2 : ¬ (netRelay n s p).val < n + W := by dsimp [netRelay, W]; omega
            have hn3 : (netRelay n s p).val < n + W + P := by
              have := p.isLt; dsimp [netRelay, W, P]; omega
            have hp_eq : (⟨(netRelay n s p).val - (n + W), by omega⟩ : Fin P) = p :=
              Fin.ext (by dsimp [netRelay, W]; omega)
            rw [dite_neg hn1, dite_neg hn2, dite_pos hn3, hp_eq]
            have hin := hadj_in (netRelayPred in1 in2 outWire p) (netRelay n s p)
              (Or.inr (Or.inl ⟨p, rfl, rfl⟩))
            rw [ite_pos hin, hnode_relayPred]
          · exfalso
            have hdir := (hadj_orient u v).mp ⟨hv, hlt⟩
            rcases hdir with ⟨i, rfl, _⟩ | ⟨p, rfl, _⟩ | ⟨p, rfl, _⟩
            · exact hu1 i.isLt
            · unfold netRelayPred at hu3
              by_cases hne : (netPrevPorts in1 in2 outWire p).Nonempty
              · rw [dite_pos hne] at hu3
                exact hu3 (by
                  have := ((netPrevPorts in1 in2 outWire p).max' hne).isLt
                  dsimp [netRelay, W, P]; omega)
              · rw [dite_neg hne] at hu3
                exact hu3 (by
                  have := (netPortWire in1 in2 outWire p).isLt
                  dsimp [netOrig, W, P]; omega)
            · exact hu3 (by have := p.isLt; dsimp [netRelay, W, P]; omega)
    · intro i j
      let r := roundOf i j
      let p : Fin P := ⟨2 * s + j.val, by omega⟩
      have hp_not : ¬ (p.val < 2 * s) := by dsimp [p]; omega
      have hcons : netPortConsumer n s p = netSink n s j := by
        unfold netPortConsumer
        rw [dite_neg hp_not]
        exact congrArg (netSink n s) (Fin.ext (by dsimp [p]; omega))
      have hpw : netPortWire in1 in2 outWire p = outWire j := by
        unfold netPortWire
        rw [dite_neg hp_not]
        exact congrArg outWire (Fin.ext (by dsimp [p]; omega))
      have hin := (hadj_orient (netRelay n s p) (netSink n s j)).mpr
        (Or.inr (Or.inr ⟨p, rfl, hcons.symm⟩))
      have hin' : netRelay n s p ∈ netAdj in1 in2 outWire (netSink n s j) ∧
          netTopo in1 in2 outWire (netRelay n s p) < netTopo in1 in2 outWire (netSink n s j) :=
        ⟨(hadj_symm _ _).mp hin.1, hin.2⟩
      dsimp only [sinkFn]
      change (if netRelay n s p ∈ netAdj in1 in2 outWire (netSink n s j) ∧
          netTopo in1 in2 outWire (netRelay n s p) < netTopo in1 in2 outWire (netSink n s j) then
        nodeVal r (netRelay n s p) else false) = msg i j
      rw [ite_pos hin', hnode_relay, hpw, hw_out r j]
      have hi_lt : i.val < n := i.isLt
      have hj_lt : j.val < n := j.isLt
      have hr_val : r.val = (i.val + (n - j.val)) % n := rfl
      by_cases hji : j.val ≤ i.val
      · have hr_eq : r.val = i.val - j.val := by
          rw [hr_val]
          have h1 : i.val + (n - j.val) = (i.val - j.val) + n * 1 := by omega
          rw [h1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
        have hidx1 : (⟨(j.val + r.val) % n, Nat.mod_lt _ hn_pos⟩ : Fin n) = i :=
          Fin.ext (by dsimp only; rw [hr_eq, Nat.add_sub_of_le hji, Nat.mod_eq_of_lt hi_lt])
        have hidx2 : (⟨(i.val + (n - r.val)) % n, Nat.mod_lt _ hn_pos⟩ : Fin n) = j := by
          apply Fin.ext; dsimp only
          have h2 : i.val + (n - r.val) = j.val + n * 1 := by omega
          rw [h2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj_lt]
        rw [hidx1]
        dsimp only [x_vec]
        rw [hidx2]
      · have hr_eq : r.val = i.val + (n - j.val) := by
          rw [hr_val]; exact Nat.mod_eq_of_lt (by omega)
        have hidx1 : (⟨(j.val + r.val) % n, Nat.mod_lt _ hn_pos⟩ : Fin n) = i := by
          apply Fin.ext; dsimp only
          have h1 : j.val + r.val = i.val + n * 1 := by omega
          rw [h1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi_lt]
        have hidx2 : (⟨(i.val + (n - r.val)) % n, Nat.mod_lt _ hn_pos⟩ : Fin n) = j := by
          apply Fin.ext; dsimp only
          have h2 : i.val + (n - r.val) = j.val := by omega
          rw [h2, Nat.mod_eq_of_lt hj_lt]
        rw [hidx1]
        dsimp only [x_vec]
        rw [hidx2]
  -- Distance bound & coding-gain lower bound
  let adj := netAdj in1 in2 outWire
  let k : ℕ := Nat.log 5 (n / 2)
  have hk_ge1 : 1 ≤ k := Nat.le_log_of_pow_le (by decide) (by omega)
  have h5k_le : 5 ^ k ≤ n / 2 := Nat.pow_log_le_self 5 (by omega)
  have hn2_lt_5k1 : n / 2 < 5 ^ (k + 1) := Nat.lt_pow_succ_log_self (by decide) (n / 2)
  let distBound (i j : Fin n) : ℕ :=
    if netSink n s j ∈ graphBall adj k (netSrc n s i) then 0 else k + 1
  have hsum_ge : (1 / 6 : ℝ) * ((n : ℝ) ^ 2) * (Real.log (n : ℝ) / Real.log 2) ≤
      (∑ i : Fin n, ∑ j : Fin n, (distBound i j : ℝ)) := by
    have hn_lt_8k1 : n < 2 ^ (3 * (k + 1)) := by
      have h2_5_le_8 : ∀ m : ℕ, 1 ≤ m → 2 * 5 ^ (m + 1) ≤ 8 ^ (m + 1) := by
        intro m hm
        induction m with
        | zero => omega
        | succ m' ih =>
          cases m' with
          | zero => decide
          | succ m'' =>
            have ih' := ih (by omega)
            calc 2 * 5 ^ (m'' + 2 + 1) = 5 * (2 * 5 ^ (m'' + 1 + 1)) := by rw [pow_succ]; ring
              _ ≤ 8 * 8 ^ (m'' + 1 + 1) := Nat.mul_le_mul (by decide) ih'
              _ = 8 ^ (m'' + 2 + 1) := by rw [pow_succ]; ring
      have hn_lt_2_5 : n < 2 * 5 ^ (k + 1) := by omega
      have h8_eq : 8 ^ (k + 1) = 2 ^ (3 * (k + 1)) := by
        rw [pow_mul]; norm_num
      exact (hn_lt_2_5.trans_le (h2_5_le_8 k hk_ge1)).trans_eq h8_eq
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hk1_log : (1 / 3 : ℝ) * (Real.log (n : ℝ) / Real.log 2) ≤ ((k + 1 : ℕ) : ℝ) := by
      have hn_le_R : (n : ℝ) ≤ ((2 ^ (3 * (k + 1)) : ℕ) : ℝ) := by exact_mod_cast hn_lt_8k1.le
      have hlog_le := Real.log_le_log (by exact_mod_cast hn_pos) hn_le_R
      rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at hlog_le
      push_cast at hlog_le ⊢
      rw [mul_div_assoc', div_le_iff₀ hlog2]
      linarith
    have hrow_sum : ∀ i : Fin n, n * (k + 1) ≤ 2 * ∑ j : Fin n, distBound i j := by
      intro i
      let near : Finset (Fin n) :=
        Finset.univ.filter (fun j => netSink n s j ∈ graphBall adj k (netSrc n s i))
      let far : Finset (Fin n) :=
        Finset.univ.filter (fun j => netSink n s j ∉ graphBall adj k (netSrc n s i))
      have hpart : near.card + far.card = n := by
        simpa [near, far, Finset.card_univ, Fintype.card_fin] using
          Finset.card_filter_add_card_filter_not
            (s := (Finset.univ : Finset (Fin n)))
            (fun j => netSink n s j ∈ graphBall adj k (netSrc n s i))
      have hnear_le : near.card ≤ n / 2 := by
        have hsub : near.image (netSink n s) ⊆ graphBall adj k (netSrc n s i) := by
          intro v hv
          obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hv
          exact (Finset.mem_filter.mp hj).2
        calc near.card = (near.image (netSink n s)).card :=
              (Finset.card_image_of_injective _ hsink_inj).symm
          _ ≤ (graphBall adj k (netSrc n s i)).card := Finset.card_le_card hsub
          _ ≤ 5 ^ k := card_graphBall_le adj hadj_deg k (netSrc n s i)
          _ ≤ n / 2 := h5k_le
      have h2far : n ≤ 2 * far.card := by omega
      have hsum_eq : (∑ j : Fin n, distBound i j) = far.card * (k + 1) := by
        dsimp only [distBound]
        rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
          (fun j : Fin n => netSink n s j ∈ graphBall adj k (netSrc n s i))]
        have h1 : ∑ j ∈ near,
            (if netSink n s j ∈ graphBall adj k (netSrc n s i) then 0 else k + 1) = 0 :=
          Finset.sum_eq_zero (fun j hj => by simp [(Finset.mem_filter.mp hj).2])
        have h2 : ∑ j ∈ far,
            (if netSink n s j ∈ graphBall adj k (netSrc n s i) then 0 else k + 1) =
            far.card * (k + 1) := by
          calc ∑ j ∈ far,
                (if netSink n s j ∈ graphBall adj k (netSrc n s i) then 0 else k + 1)
              = ∑ _j ∈ far, (k + 1) :=
                Finset.sum_congr rfl (fun j hj => by simp [(Finset.mem_filter.mp hj).2])
            _ = far.card * (k + 1) := by simp
        change (∑ j ∈ near, _) + (∑ j ∈ far, _) = _
        rw [h1, h2, zero_add]
      rw [hsum_eq]
      calc n * (k + 1) ≤ (2 * far.card) * (k + 1) := Nat.mul_le_mul_right _ h2far
        _ = 2 * (far.card * (k + 1)) := by ring
    have htot_nat : n * n * (k + 1) ≤ 2 * ∑ i : Fin n, ∑ j : Fin n, distBound i j := by
      calc n * n * (k + 1) = ∑ _i : Fin n, n * (k + 1) := by simp [mul_assoc]
        _ ≤ ∑ i : Fin n, 2 * ∑ j : Fin n, distBound i j :=
            Finset.sum_le_sum (fun i _ => hrow_sum i)
        _ = 2 * ∑ i : Fin n, ∑ j : Fin n, distBound i j := (Finset.mul_sum _ _ _).symm
    have htot_R : (n : ℝ) ^ 2 * ((k + 1 : ℕ) : ℝ) ≤
        2 * (∑ i : Fin n, ∑ j : Fin n, (distBound i j : ℝ)) := by
      calc (n : ℝ) ^ 2 * ((k + 1 : ℕ) : ℝ)
          = ((n * n * (k + 1) : ℕ) : ℝ) := by push_cast; ring
        _ ≤ ((2 * ∑ i : Fin n, ∑ j : Fin n, distBound i j : ℕ) : ℝ) := by
            exact_mod_cast htot_nat
        _ = 2 * (∑ i : Fin n, ∑ j : Fin n, (distBound i j : ℝ)) := by push_cast; rfl
    have hprod_le : (n : ℝ) ^ 2 * ((1 / 3 : ℝ) * (Real.log (n : ℝ) / Real.log 2)) ≤
        (n : ℝ) ^ 2 * ((k + 1 : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hk1_log (sq_nonneg _)
    linarith
  refine ⟨netV n s, adj, netSrc n s, netSink n s, distBound, hV_pos, hV_le,
    hadj_loopless, hadj_symm, hadj_deg, hexchange, ?_, hsum_ge, ?_⟩
  · intro i j walk hhead hlast hstep
    dsimp only [distBound]
    split_ifs with hmem
    · cases walk with
      | nil => simp at hhead
      | cons a rest => simp
    · by_contra hlt_not
      have hlen_le : walk.length ≤ k + 1 := by omega
      exact hmem (walk_mem_graphBall adj walk k (netSrc n s i) (netSink n s j)
        hhead hlast hstep hlen_le)
  · intro rateRoute hrate_pos hweak
    have hdeg_sum_nat : (∑ u : Fin (netV n s), (adj u).card) ≤ 20 * (s + n) := by
      calc (∑ u : Fin (netV n s), (adj u).card) ≤ ∑ _u : Fin (netV n s), 4 :=
            Finset.sum_le_sum (fun u _ => hadj_deg u)
        _ = netV n s * 4 := by simp
        _ ≤ (5 * (s + n)) * 4 := Nat.mul_le_mul_right 4 hV_le
        _ = 20 * (s + n) := by ring
    have hedges_le : ((∑ u : Fin (netV n s), (adj u).card : ℕ) : ℝ) / 2 ≤
        10 * ((s : ℝ) + (n : ℝ)) := by
      have hcast : ((∑ u : Fin (netV n s), (adj u).card : ℕ) : ℝ) ≤
          ((20 * (s + n) : ℕ) : ℝ) := by
        exact_mod_cast hdeg_sum_nat
      rw [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] at hcast
      linarith
    have hchain : rateRoute * ((1 / 6 : ℝ) * ((n : ℝ) ^ 2) * (Real.log (n : ℝ) / Real.log 2)) ≤
        10 * ((s : ℝ) + (n : ℝ)) :=
      (mul_le_mul_of_nonneg_left hsum_ge hrate_pos.le).trans (hweak.trans hedges_le)
    have hn_R : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
    have hsn_R : (0 : ℝ) < (s : ℝ) + (n : ℝ) := by positivity
    rw [div_le_div_iff₀ hsn_R hrate_pos]
    apply le_of_mul_le_mul_right _ hn_R
    calc 1 / 60 * (n : ℝ) * (Real.log (n : ℝ) / Real.log 2) * rateRoute * (n : ℝ)
        = (1 / 10 : ℝ) * (rateRoute * ((1 / 6 : ℝ) * ((n : ℝ) ^ 2) *
            (Real.log (n : ℝ) / Real.log 2))) := by ring
      _ ≤ (1 / 10 : ℝ) * (10 * ((s : ℝ) + (n : ℝ))) :=
          mul_le_mul_of_nonneg_left hchain (by norm_num)
      _ = (1 / (n : ℝ)) * ((s : ℝ) + (n : ℝ)) * (n : ℝ) := by
          have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_R
          field_simp [hn_ne]

end ShiftAndRotationBarrier

/-! ### Diagnosis 4 -/

theorem diagnosis_LinearSharedDecoderBoundsAndMaskFloors :
    Diagnosis_LinearSharedDecoderBoundsAndMaskFloorsSpec := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro F A _ _ _ _ d _ p C hC
    exact hC.two_class_capacity_bound
  · intro F A _ _ _ _ d M t _ p C hC ht hMd hMt
    exact hC.square_cover_bound ht (by simpa using hMd) (by simpa using hMt)
  · intro d _ η hη
    exact SharedDecoders.CapacityMaskProbability.isolation_rate_probability η hη
  · intro d _ η hη
    exact SharedDecoders.CapacityMaskProbability.component_floor_probability η hη

/-! ### Diagnosis 5 -/

theorem diagnosis_RamseyHalesJewettTwoStage : Diagnosis_RamseyHalesJewettTwoStageSpec := by
  constructor
  · intro M₁ M₂ _ _
    obtain ⟨D₀, hD₀⟩ := SharedDecoders.exists_twoHop_cutoff (Fin M₁) (Fin M₂)
    refine ⟨D₀ + 1, Nat.succ_pos _, ?_⟩
    intro F _ d b _ p₁ p₂ K₁ K₂ hb hNd hK₁ hK₂ hexact
    let idx0 : Fin b := ⟨0, hb⟩
    have : Nontrivial (Fin b → F) := ⟨⟨fun _ => 1, fun _ => 0, fun h =>
      one_ne_zero (congrFun h idx0)⟩⟩
    have h1 := SharedDecoders.linearClassUniform_of_classUniform p₁ K₁ hK₁
    have h2 := SharedDecoders.linearClassUniform_of_classUniform p₂ K₂ hK₂
    have heq : ∀ X, K₂ (K₁ X) = swap X := fun X => by
      have h := LinearMap.congr_fun hexact X
      exact h
    have hd_le := hD₀ F (Fin b → F) d p₁ p₂ K₁ K₂ h1 h2 heq
    omega
  · intro M₁ M₂ k _ _ hk
    obtain ⟨N, hN, hbound⟩ :=
      SharedDecoders.exists_twoHop_rank_threshold (κ₁ := Fin M₁) (κ₂ := Fin M₂) (k := k) hk
    refine ⟨N, hN, ?_⟩
    intro F _ d b _ p₁ p₂ K₁ K₂ hd h2N hK₁ hK₂
    have h1 := hbound F d b hd (by omega) p₁ p₂ K₁ K₂ hK₁ hK₂
    refine ⟨h1, ?_⟩
    have htwice : d ≤ 2 * (d - N + 1) := by omega
    have hmul := Nat.mul_le_mul_left (b * k) htwice
    nlinarith

/-! ### Diagnosis 6 -/

section BehrendAndRandomAP

private def baseEval (M : ℕ) : {m : ℕ} → (Fin m → ℕ) → ℕ
  | 0, _ => 0
  | m + 1, x => x 0 + M * baseEval M (fun i : Fin m => x i.succ)

private theorem baseEval_lt (M : ℕ) (hM : 1 ≤ M) :
    ∀ {m : ℕ} (x : Fin m → ℕ), (∀ i, x i < M) → baseEval M x < M ^ m
  | 0, _, _ => by simp [baseEval]
  | m + 1, x, hx => by
    simp only [baseEval, pow_succ]
    have ih := baseEval_lt M hM (fun i : Fin m => x i.succ) (fun i => hx i.succ)
    have h0 := hx 0
    nlinarith

private theorem baseEval_inj (M : ℕ) (hM : 1 ≤ M) :
    ∀ {m : ℕ} (x y : Fin m → ℕ),
      (∀ i, x i < M) → (∀ i, y i < M) → baseEval M x = baseEval M y → x = y
  | 0, x, y, _, _, _ => by funext i; exact i.elim0
  | m + 1, x, y, hx, hy, heq => by
    simp only [baseEval] at heq
    have hx0 := hx 0
    have hy0 := hy 0
    have hmod : (x 0 + M * baseEval M (fun i : Fin m => x i.succ)) % M =
        (y 0 + M * baseEval M (fun i : Fin m => y i.succ)) % M := congrArg (· % M) heq
    rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hx0, Nat.mod_eq_of_lt hy0] at hmod
    have hdiv : baseEval M (fun i : Fin m => x i.succ) =
        baseEval M (fun i : Fin m => y i.succ) := by nlinarith
    have ih := baseEval_inj M hM _ _ (fun i => hx i.succ) (fun i => hy i.succ) hdiv
    funext i
    cases i using Fin.cases with
    | zero => exact hmod
    | succ j => exact congrFun ih j

private theorem baseEval_add (M : ℕ) :
    ∀ {m : ℕ} (x y : Fin m → ℕ),
      baseEval M (fun i => x i + y i) = baseEval M x + baseEval M y
  | 0, _, _ => by simp [baseEval]
  | m + 1, x, y => by
    simp only [baseEval, baseEval_add M (fun i : Fin m => x i.succ) (fun i : Fin m => y i.succ)]
    ring

private theorem baseEval_two_mul (M : ℕ) :
    ∀ {m : ℕ} (x : Fin m → ℕ),
      baseEval M (fun i => 2 * x i) = 2 * baseEval M x
  | 0, _ => by simp [baseEval]
  | m + 1, x => by
    simp only [baseEval, baseEval_two_mul M (fun i : Fin m => x i.succ)]
    ring

private theorem behrend_sphere_finset (m B : ℕ) (hm : 1 ≤ m) (hB : 1 ≤ B) :
    ∃ S : Finset ℕ,
      (∀ u ∈ S, u < (2 * B) ^ m) ∧
      (∀ a s : ℕ, 1 ≤ s → ¬ (a ∈ S ∧ a + s ∈ S ∧ a + 2 * s ∈ S)) ∧
      B ^ m ≤ (2 * m * B ^ 2) * S.card := by
  classical
  let normSq (x : Fin m → Fin B) : ℕ := ∑ i : Fin m, (x i).val ^ 2
  let shells : Finset ℕ := Finset.range (m * B ^ 2 + 1)
  have hmem_shells : ∀ x : Fin m → Fin B, normSq x ∈ shells := by
    intro x
    rw [Finset.mem_range]
    have hle : ∑ i : Fin m, (x i).val ^ 2 ≤ ∑ _i : Fin m, B ^ 2 :=
      Finset.sum_le_sum fun i _ => Nat.pow_le_pow_left (x i).isLt.le 2
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hle
    exact Nat.lt_succ_of_le hle
  have hsum_fib : (Finset.univ : Finset (Fin m → Fin B)).card =
      ∑ R ∈ shells, (Finset.univ.filter (fun x => normSq x = R)).card :=
    Finset.card_eq_sum_card_fiberwise (fun x _ => hmem_shells x)
  have hne_shells : shells.Nonempty := ⟨0, Finset.mem_range.mpr (by omega)⟩
  obtain ⟨R, _, hR_max⟩ := shells.exists_max_image
    (fun R => (Finset.univ.filter (fun x => normSq x = R)).card) hne_shells
  let F_R : Finset (Fin m → Fin B) := Finset.univ.filter (fun x => normSq x = R)
  have hfibre : (Finset.univ : Finset (Fin m → Fin B)).card ≤ F_R.card * shells.card := by
    rw [hsum_fib]
    calc ∑ r ∈ shells, (Finset.univ.filter (fun x => normSq x = r)).card
        ≤ ∑ _r ∈ shells, F_R.card := Finset.sum_le_sum (fun r hr => hR_max r hr)
      _ = shells.card * F_R.card := by simp
      _ = F_R.card * shells.card := Nat.mul_comm _ _
  let enc (x : Fin m → Fin B) : ℕ := baseEval (2 * B) (fun i => (x i).val)
  have henc_inj : Function.Injective enc := by
    intro x y hxy
    have hv := baseEval_inj (2 * B) (by omega) (fun i => (x i).val) (fun i => (y i).val)
      (fun i => by have := (x i).isLt; omega)
      (fun i => by have := (y i).isLt; omega) hxy
    funext i
    exact Fin.ext (congrFun hv i)
  let S : Finset ℕ := F_R.image enc
  refine ⟨S, ?_, ?_, ?_⟩
  · intro u hu
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hu
    exact baseEval_lt (2 * B) (by omega) _ (fun i => by have := (x i).isLt; omega)
  · rintro a s hs ⟨ha, has, ha2s⟩
    obtain ⟨x, hx, hax⟩ := Finset.mem_image.mp ha
    obtain ⟨y, hy, hay⟩ := Finset.mem_image.mp has
    obtain ⟨z, hz, haz⟩ := Finset.mem_image.mp ha2s
    have hxR : normSq x = R := (Finset.mem_filter.mp hx).2
    have hyR : normSq y = R := (Finset.mem_filter.mp hy).2
    have hzR : normSq z = R := (Finset.mem_filter.mp hz).2
    have hsum_eval : baseEval (2 * B) (fun i => (x i).val + (z i).val) =
        baseEval (2 * B) (fun i => 2 * (y i).val) := by
      rw [baseEval_add, baseEval_two_mul]
      change enc x + enc z = 2 * enc y
      omega
    have hdigit := baseEval_inj (2 * B) (by omega)
      (fun i => (x i).val + (z i).val) (fun i => 2 * (y i).val)
      (fun i => by have := (x i).isLt; have := (z i).isLt; omega)
      (fun i => by have := (y i).isLt; omega) hsum_eval
    have hpar : ∑ i : Fin m, (((x i).val : ℤ) - ((z i).val : ℤ)) ^ 2 = 0 := by
      have hpt : ∀ i : Fin m, (((x i).val : ℤ) + ((z i).val : ℤ)) = 2 * ((y i).val : ℤ) :=
        fun i => by exact_mod_cast congrFun hdigit i
      have hid : ∀ i : Fin m,
          (((x i).val : ℤ) - ((z i).val : ℤ)) ^ 2 =
            2 * ((x i).val : ℤ) ^ 2 + 2 * ((z i).val : ℤ) ^ 2 - 4 * ((y i).val : ℤ) ^ 2 := by
        intro i; have hi := hpt i; nlinarith
      simp_rw [hid]
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
      have hxZ : ∑ i : Fin m, ((x i).val : ℤ) ^ 2 = (R : ℤ) := by exact_mod_cast hxR
      have hyZ : ∑ i : Fin m, ((y i).val : ℤ) ^ 2 = (R : ℤ) := by exact_mod_cast hyR
      have hzZ : ∑ i : Fin m, ((z i).val : ℤ) ^ 2 = (R : ℤ) := by exact_mod_cast hzR
      rw [hxZ, hyZ, hzZ]; ring
    have hall0 : ∀ i ∈ (Finset.univ : Finset (Fin m)),
        (((x i).val : ℤ) - ((z i).val : ℤ)) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)).mp hpar
    have hxz : x = z := by
      funext i
      have hi0 := sq_eq_zero_iff.mp (hall0 i (Finset.mem_univ i))
      exact Fin.ext (by omega)
    rw [hxz] at hax
    omega
  · have hS_card : S.card = F_R.card := Finset.card_image_of_injective _ henc_inj
    rw [hS_card]
    have huniv_card : (Finset.univ : Finset (Fin m → Fin B)).card = B ^ m := by
      rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    have hshells_card : shells.card ≤ 2 * m * B ^ 2 := by
      rw [Finset.card_range]
      have : 1 ≤ m * B ^ 2 := Nat.mul_pos hm (Nat.pow_pos hB)
      nlinarith
    calc B ^ m = (Finset.univ : Finset (Fin m → Fin B)).card := huniv_card.symm
      _ ≤ F_R.card * shells.card := hfibre
      _ ≤ F_R.card * (2 * m * B ^ 2) := Nat.mul_le_mul_left _ hshells_card
      _ = (2 * m * B ^ 2) * F_R.card := Nat.mul_comm _ _

theorem diagnosis_BehrendAndRandomAPBound : Diagnosis_BehrendAndRandomAPBoundSpec := by
  constructor
  · -- Part 1: Behrend `3`-AP-free subset with `C_beh = 32`
    refine ⟨32, by norm_num, fun d hd => ?_⟩
    let t : ℝ := Real.sqrt (Real.log (d : ℝ))
    have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
    have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    -- Elementary lower bound `1 / 2 < t` for all `d ≥ 2`
    have hlog2_half : (1 : ℝ) / 2 ≤ Real.log 2 := by
      have hexp_neg := Real.add_one_le_exp (-(1 / 2 : ℝ))
      have hexp_pos : 0 < Real.exp (1 / 2 : ℝ) := Real.exp_pos _
      have hprod : Real.exp (-(1 / 2 : ℝ)) * Real.exp (1 / 2 : ℝ) = 1 := by
        rw [← Real.exp_add]; norm_num
      have hexp_le : Real.exp (1 / 2 : ℝ) ≤ 2 := by nlinarith
      have hlog := Real.log_le_log hexp_pos hexp_le
      rwa [Real.log_exp] at hlog
    have hlogd_half : (1 : ℝ) / 2 ≤ Real.log (d : ℝ) :=
      hlog2_half.trans (Real.log_le_log (by norm_num) hd2)
    have ht_nonneg : 0 ≤ t := Real.sqrt_nonneg _
    have ht_sq : t ^ 2 = Real.log (d : ℝ) := Real.sq_sqrt (by linarith)
    have ht_gt_half : (1 : ℝ) / 2 < t := by nlinarith
    by_cases ht4 : t < 4
    · -- Small `d` (`t < 4`): singleton `{0}` suffices
      refine ⟨{0}, ?_, ?_, ?_⟩
      · intro x hx
        simp only [Finset.mem_singleton] at hx
        omega
      · rintro a s hs ⟨ha, has, _⟩
        simp only [Finset.mem_singleton] at ha has
        omega
      · simp only [Finset.card_singleton, Nat.cast_one]
        change (d : ℝ) * Real.exp (-32 * t) ≤ 1
        rw [← Real.exp_log hd_pos, ← Real.exp_add, ← ht_sq]
        have hexp_neg : t ^ 2 + (-32 * t) ≤ 0 := by nlinarith
        exact Real.exp_le_one_iff.mpr hexp_neg
    · -- Large `d` (`4 ≤ t`): Behrend sphere in base `2 * B`
      push Not at ht4
      let m : ℕ := ⌊t⌋₊
      let B : ℕ := ⌊Real.exp t / 2⌋₊
      have hm4 : 4 ≤ m := Nat.le_floor (by exact_mod_cast ht4)
      have hm1 : 1 ≤ m := by omega
      have hm_le : (m : ℝ) ≤ t := Nat.floor_le ht_nonneg
      have ht_lt_m1 : t < (m : ℝ) + 1 := Nat.lt_floor_add_one t
      -- Show `2 ≤ exp 1`, hence `16 ≤ exp 4 ≤ exp t`, so `8 ≤ B` and `exp(t - 2) ≤ B`
      have hexp1 : (2 : ℝ) ≤ Real.exp 1 := by
        have h := Real.add_one_le_exp 1; linarith
      have hexp2 : (4 : ℝ) ≤ Real.exp 2 := by
        have h : (2 : ℝ) ^ 2 ≤ (Real.exp 1) ^ 2 := pow_le_pow_left₀ (by norm_num) hexp1 2
        rw [← Real.exp_nat_mul] at h
        norm_num at h
        exact h
      have hexp4 : (16 : ℝ) ≤ Real.exp 4 := by
        have h : (4 : ℝ) ^ 2 ≤ (Real.exp 2) ^ 2 := pow_le_pow_left₀ (by norm_num) hexp2 2
        rw [← Real.exp_nat_mul] at h
        norm_num at h
        exact h
      have hexpt16 : (16 : ℝ) ≤ Real.exp t := hexp4.trans (Real.exp_le_exp.mpr ht4)
      have hB8 : 8 ≤ B := Nat.le_floor (by dsimp; linarith)
      have hB1 : 1 ≤ B := by omega
      have hB_le : (B : ℝ) ≤ Real.exp t / 2 := Nat.floor_le (by positivity)
      have hB_gt : Real.exp t / 2 < (B : ℝ) + 1 := Nat.lt_floor_add_one _
      have hB_ge_exp : Real.exp (t - 2) ≤ (B : ℝ) := by
        have hexp_m2 : Real.exp (-2 : ℝ) ≤ 1 / 4 := by
          have hp : Real.exp 2 * Real.exp (-2 : ℝ) = 1 := by rw [← Real.exp_add]; norm_num
          have hpos : 0 < Real.exp (-2 : ℝ) := Real.exp_pos _
          nlinarith
        have hB8R : (8 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB8
        have hquarter : Real.exp t * (1 / 4) ≤ (B : ℝ) := by linarith
        calc Real.exp (t - 2) = Real.exp t * Real.exp (-2 : ℝ) := by
              rw [sub_eq_add_neg, Real.exp_add]
          _ ≤ Real.exp t * (1 / 4) :=
              mul_le_mul_of_nonneg_left hexp_m2 (Real.exp_pos t).le
          _ ≤ (B : ℝ) := hquarter
      -- `(2 * B) ^ m ≤ d`
      have h2Bm_le_d : (2 * B) ^ m ≤ d := by
        have h2B_le : ((2 * B : ℕ) : ℝ) ≤ Real.exp t := by push_cast; linarith
        have hpow_le : (((2 * B) ^ m : ℕ) : ℝ) ≤ (d : ℝ) := by
          calc (((2 * B) ^ m : ℕ) : ℝ) = ((2 * B : ℕ) : ℝ) ^ m := by push_cast; rfl
            _ ≤ (Real.exp t) ^ m := pow_le_pow_left₀ (by positivity) h2B_le m
            _ = Real.exp ((m : ℝ) * t) := (Real.exp_nat_mul t m).symm
            _ ≤ Real.exp (Real.log (d : ℝ)) := by
              apply Real.exp_le_exp.mpr
              rw [← ht_sq]
              nlinarith
            _ = (d : ℝ) := Real.exp_log hd_pos
        exact_mod_cast hpow_le
      obtain ⟨S, hS_lt, hS_ap, hS_card⟩ := behrend_sphere_finset m B hm1 hB1
      refine ⟨S, fun x hx => (hS_lt x hx).trans_le h2Bm_le_d, hS_ap, ?_⟩
      -- Cancel `B^2` in `B^m ≤ (2 * m * B^2) * S.card`
      have hm_split : m = (m - 2) + 2 := by omega
      have hBm2_le : B ^ (m - 2) ≤ 2 * m * S.card := by
        have h1 : B ^ (m - 2) * B ^ 2 ≤ (2 * m * S.card) * B ^ 2 := by
          calc B ^ (m - 2) * B ^ 2 = B ^ m := by rw [← pow_add, ← hm_split]
            _ ≤ (2 * m * B ^ 2) * S.card := hS_card
            _ = (2 * m * S.card) * B ^ 2 := by ring
        exact Nat.le_of_mul_le_mul_right h1 (by positivity)
      have hBm2_R : (B : ℝ) ^ (m - 2) ≤ 2 * (m : ℝ) * (S.card : ℝ) := by
        exact_mod_cast hBm2_le
      have hexp_m2_le : Real.exp (((m - 2 : ℕ) : ℝ) * (t - 2)) ≤ (B : ℝ) ^ (m - 2) := by
        calc Real.exp (((m - 2 : ℕ) : ℝ) * (t - 2)) = (Real.exp (t - 2)) ^ (m - 2) :=
              Real.exp_nat_mul (t - 2) (m - 2)
          _ ≤ (B : ℝ) ^ (m - 2) := pow_le_pow_left₀ (Real.exp_pos _).le hB_ge_exp (m - 2)
      have h2m_exp : 2 * (m : ℝ) * Real.exp (-2 * t) ≤ 1 := by
        have hlin := Real.add_one_le_exp (2 * t)
        have hpos : 0 < Real.exp (-2 * t) := Real.exp_pos _
        have hprod : Real.exp (2 * t) * Real.exp (-2 * t) = 1 := by
          rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
        have h2m_le : 2 * (m : ℝ) ≤ Real.exp (2 * t) := by linarith
        nlinarith
      have hScard_ge : Real.exp (((m - 2 : ℕ) : ℝ) * (t - 2) - 2 * t) ≤ (S.card : ℝ) := by
        calc Real.exp (((m - 2 : ℕ) : ℝ) * (t - 2) - 2 * t)
            = Real.exp (((m - 2 : ℕ) : ℝ) * (t - 2)) * Real.exp (-2 * t) := by
              rw [sub_eq_add_neg, Real.exp_add]; ring_nf
          _ ≤ (2 * (m : ℝ) * (S.card : ℝ)) * Real.exp (-2 * t) :=
              mul_le_mul_of_nonneg_right (hexp_m2_le.trans hBm2_R) (Real.exp_pos _).le
          _ = (2 * (m : ℝ) * Real.exp (-2 * t)) * (S.card : ℝ) := by ring
          _ ≤ 1 * (S.card : ℝ) :=
              mul_le_mul_of_nonneg_right h2m_exp (Nat.cast_nonneg _)
          _ = (S.card : ℝ) := one_mul _
      have hexp_target : (d : ℝ) * Real.exp (-32 * t) ≤
          Real.exp (((m - 2 : ℕ) : ℝ) * (t - 2) - 2 * t) := by
        rw [← Real.exp_log hd_pos, ← Real.exp_add, ← ht_sq]
        apply Real.exp_le_exp.mpr
        have hm_sub : ((m - 2 : ℕ) : ℝ) = (m : ℝ) - 2 := by
          have : 2 ≤ m := by omega
          exact Nat.cast_sub this
        rw [hm_sub]
        nlinarith
      exact hexp_target.trans hScard_ge
  · -- Part 2: Random `M₁`-colorings (`M₁ ≥ 2`), `C_ap = 6 / Real.log 2`, `D₀ = 2`
    intro M₁ hM₁
    let C_ap : ℝ := 6 / Real.log 2
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hCap : 0 < C_ap := div_pos (by norm_num) hlog2
    refine ⟨C_ap, 2, hCap, by decide, fun d _ hd => ?_⟩
    classical
    have hd_pos : 0 < d := NeZero.pos d
    let P_good (p₁ : Fin d → Fin M₁) : Prop :=
      ∀ (a s ℓ : ℕ), 1 ≤ s → 1 ≤ ℓ → a + (ℓ - 1) * s < d →
        (∀ j < ℓ,
          p₁ ⟨(a + j * s) % d, Nat.mod_lt _ hd_pos⟩ = p₁ ⟨a % d, Nat.mod_lt _ hd_pos⟩) →
        (ℓ : ℝ) ≤ C_ap * Real.log (d : ℝ)
    let Good : Finset (Fin d → Fin M₁) := Finset.univ.filter P_good
    let Bad : Finset (Fin d → Fin M₁) := Finset.univ.filter (fun p₁ => ¬ P_good p₁)
    have hNatCard : Nat.card { p₁ : Fin d → Fin M₁ | P_good p₁ } = Good.card := by
      have hset : { p₁ : Fin d → Fin M₁ | P_good p₁ } = (Good : Set (Fin d → Fin M₁)) := by
        ext p₁; simp [Good]
      rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset]
    change Fintype.card (Fin d → Fin M₁) < 2 * Nat.card { p₁ : Fin d → Fin M₁ | P_good p₁ }
    rw [hNatCard]
    have hsum_card : Good.card + Bad.card = Fintype.card (Fin d → Fin M₁) := by
      simpa [Good, Bad, Finset.card_univ] using
        Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin d → Fin M₁))) P_good
    have huniv_pow : Fintype.card (Fin d → Fin M₁) = M₁ ^ d := by
      rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    -- Suffices to show `2 * Bad.card < M₁ ^ d`
    suffices hbad_lt : 2 * Bad.card < M₁ ^ d by omega
    let k : ℕ := ⌊C_ap * Real.log (d : ℝ)⌋₊ + 1
    have hlogd_ge : Real.log 2 ≤ Real.log (d : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hd)
    have hCap_ge6 : 6 ≤ C_ap * Real.log (d : ℝ) := by
      dsimp [C_ap]
      rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
      linarith
    have hk_gt : C_ap * Real.log (d : ℝ) < (k : ℝ) := by
      dsimp [k]; exact_mod_cast Nat.lt_floor_add_one (C_ap * Real.log (d : ℝ))
    have hk7 : 7 ≤ k := by
      have h6 : 6 ≤ ⌊C_ap * Real.log (d : ℝ)⌋₊ := Nat.le_floor hCap_ge6
      dsimp [k]; omega
    by_cases hkd : d < k
    · -- No `k`-term progression fits in `[0, d)`!
      have hBad_empty : Bad = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro p₁ hp₁
        have hnot := (Finset.mem_filter.mp hp₁).2
        apply hnot
        intro a s ℓ hs hℓ hbound _
        by_contra hlt_not
        push Not at hlt_not
        have hk_le_l : k ≤ ℓ := by
          have hfl : ⌊C_ap * Real.log (d : ℝ)⌋₊ < ℓ :=
            (Nat.floor_lt (by positivity)).mpr hlt_not
          dsimp [k]; omega
        have h1 : k - 1 ≤ (ℓ - 1) * s := calc
          k - 1 ≤ ℓ - 1 := by omega
          _ = (ℓ - 1) * 1 := (Nat.mul_one _).symm
          _ ≤ (ℓ - 1) * s := Nat.mul_le_mul_left _ hs
        omega
      rw [hBad_empty, Finset.card_empty, mul_zero]
      exact pow_pos (by omega) d
    · -- `k ≤ d`: union bound over `(a, s) ∈ Fin d ×ˢ Fin d`
      push Not at hkd
      let pairs : Finset (Fin d × Fin d) :=
        (Finset.univ ×ˢ Finset.univ).filter fun p => 1 ≤ p.2.val ∧ p.1.val + (k - 1) * p.2.val < d
      let fiber (p : Fin d × Fin d) : Finset (Fin d → Fin M₁) :=
        Finset.univ.filter fun p₁ =>
          ∀ j < k, p₁ ⟨(p.1.val + j * p.2.val) % d, Nat.mod_lt _ hd_pos⟩ = p₁ p.1
      have hBad_sub : Bad ⊆ pairs.biUnion fiber := by
        intro p₁ hp₁
        have hnot := (Finset.mem_filter.mp hp₁).2
        unfold P_good at hnot
        push Not at hnot
        obtain ⟨a, s, ℓ, hs, _, hbound, hmono, hgt⟩ := hnot
        have hk_le_l : k ≤ ℓ := by
          have hfl : ⌊C_ap * Real.log (d : ℝ)⌋₊ < ℓ :=
            (Nat.floor_lt (by positivity)).mpr hgt
          dsimp [k]; omega
        have hk_bound : a + (k - 1) * s < d := by
          have hle : (k - 1) * s ≤ (ℓ - 1) * s := Nat.mul_le_mul_right s (by omega)
          omega
        have ha_lt : a < d := by omega
        have hs_lt : s < d := by
          have : 1 * s ≤ (k - 1) * s := Nat.mul_le_mul_right s (by omega)
          omega
        refine Finset.mem_biUnion.mpr ⟨(⟨a, ha_lt⟩, ⟨s, hs_lt⟩), ?_, ?_⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩,
            hs, hk_bound⟩
        · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j hj => ?_⟩
          have hj' := hmono j (hj.trans_le hk_le_l)
          have hamod : a % d = a := Nat.mod_eq_of_lt ha_lt
          simpa [hamod] using hj'
      have hfib_le : ∀ p ∈ pairs, (fiber p).card ≤ M₁ ^ (d - (k - 1)) := by
        intro p hp
        obtain ⟨_, hs_p, hb_p⟩ := Finset.mem_filter.mp hp
        let apTail : Finset (Fin d) := (Finset.range (k - 1)).image fun j =>
          ⟨(p.1.val + (j + 1) * p.2.val) % d, Nat.mod_lt _ hd_pos⟩
        have hap_card : apTail.card = k - 1 := by
          rw [Finset.card_image_of_injOn, Finset.card_range]
          intro j₁ hj₁ j₂ hj₂ heq
          have hj1_lt : j₁ < k - 1 := Finset.mem_range.mp hj₁
          have hj2_lt : j₂ < k - 1 := Finset.mem_range.mp hj₂
          have hlt1 : p.1.val + (j₁ + 1) * p.2.val < d := by
            have : (j₁ + 1) * p.2.val ≤ (k - 1) * p.2.val := Nat.mul_le_mul_right _ (by omega)
            omega
          have hlt2 : p.1.val + (j₂ + 1) * p.2.val < d := by
            have : (j₂ + 1) * p.2.val ≤ (k - 1) * p.2.val := Nat.mul_le_mul_right _ (by omega)
            omega
          have hv := congrArg Fin.val heq
          dsimp only at hv
          rw [Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2] at hv
          have hm_eq : (j₁ + 1) * p.2.val = (j₂ + 1) * p.2.val := by omega
          have h12 := Nat.eq_of_mul_eq_mul_right (by omega : 0 < p.2.val) hm_eq
          omega
        have hp1_notMem : p.1 ∉ apTail := by
          intro hmem
          obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp hmem
          have hj_lt : j < k - 1 := Finset.mem_range.mp hj
          have hlt1 : p.1.val + (j + 1) * p.2.val < d := by
            have : (j + 1) * p.2.val ≤ (k - 1) * p.2.val := Nat.mul_le_mul_right _ (by omega)
            omega
          have hv := congrArg Fin.val heq
          dsimp only at hv
          rw [Nat.mod_eq_of_lt hlt1] at hv
          have hpos : 0 < (j + 1) * p.2.val := Nat.mul_pos (by omega) (by omega)
          omega
        let restrict (p₁ : Fin d → Fin M₁) : { x : Fin d // x ∈ apTailᶜ } → Fin M₁ :=
          fun x => p₁ x.val
        have hinj_on : Set.InjOn restrict (fiber p : Set (Fin d → Fin M₁)) := by
          intro f₁ hf₁ f₂ hf₂ hreq
          have hf1_m := (Finset.mem_filter.mp hf₁).2
          have hf2_m := (Finset.mem_filter.mp hf₂).2
          funext x
          by_cases hx : x ∈ apTail
          · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
            have hj_k : j + 1 < k := by have := Finset.mem_range.mp hj; omega
            rw [hf1_m (j + 1) hj_k, hf2_m (j + 1) hj_k]
            exact congrFun hreq ⟨p.1, Finset.mem_compl.mpr hp1_notMem⟩
          · exact congrFun hreq ⟨x, Finset.mem_compl.mpr hx⟩
        calc (fiber p).card = (Finset.image restrict (fiber p)).card :=
              (Finset.card_image_of_injOn hinj_on).symm
          _ ≤ Fintype.card ({ x : Fin d // x ∈ apTailᶜ } → Fin M₁) := Finset.card_le_univ _
          _ = M₁ ^ (d - (k - 1)) := by
            rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe, Finset.card_compl,
              Fintype.card_fin, hap_card]
      have hpairs_card : pairs.card ≤ d ^ 2 := by
        calc pairs.card ≤ (Finset.univ ×ˢ Finset.univ : Finset (Fin d × Fin d)).card :=
              Finset.card_filter_le _ _
          _ = d ^ 2 := by simp [sq]
      have hBad_le : Bad.card ≤ d ^ 2 * M₁ ^ (d - (k - 1)) := by
        calc Bad.card ≤ (pairs.biUnion fiber).card := Finset.card_le_card hBad_sub
          _ ≤ ∑ p ∈ pairs, (fiber p).card := Finset.card_biUnion_le
          _ ≤ ∑ _p ∈ pairs, M₁ ^ (d - (k - 1)) := Finset.sum_le_sum hfib_le
          _ = pairs.card * M₁ ^ (d - (k - 1)) := by simp
          _ ≤ d ^ 2 * M₁ ^ (d - (k - 1)) := Nat.mul_le_mul_right _ hpairs_card
      -- Show `2 * d^2 < 2^(k - 1) ≤ M₁^(k - 1)`
      have hd5_lt : d ^ 5 < 2 ^ (k - 1) := by
        have h5_lt : 5 * Real.log (d : ℝ) < ((k - 1 : ℕ) : ℝ) * Real.log 2 := by
          have hk1_cast : (k : ℝ) = ((k - 1 : ℕ) : ℝ) + 1 := by
            dsimp [k]; push_cast; ring
          have h6_lt : 6 * Real.log (d : ℝ) < (k : ℝ) * Real.log 2 := by
            have h := mul_lt_mul_of_pos_right hk_gt hlog2
            dsimp [C_ap] at h
            rwa [mul_right_comm, div_mul_cancel₀ 6 (ne_of_gt hlog2)] at h
          nlinarith
        have hexp := Real.exp_lt_exp.mpr h5_lt
        have hlhs : Real.exp (5 * Real.log (d : ℝ)) = ((d ^ 5 : ℕ) : ℝ) := by
          rw [show (5 : ℝ) * Real.log (d : ℝ) = ((5 : ℕ) : ℝ) * Real.log (d : ℝ) by norm_num,
            Real.exp_nat_mul, Real.exp_log (by exact_mod_cast hd_pos)]
          push_cast; rfl
        have hrhs : Real.exp (((k - 1 : ℕ) : ℝ) * Real.log 2) = ((2 ^ (k - 1) : ℕ) : ℝ) := by
          rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
          push_cast; rfl
        rw [hlhs, hrhs] at hexp
        exact_mod_cast hexp
      have h2d2_lt : 2 * d ^ 2 < M₁ ^ (k - 1) := by
        have h2d2_le : 2 * d ^ 2 ≤ d ^ 5 := by
          have : 2 ≤ d := hd
          calc 2 * d ^ 2 ≤ d * d ^ 2 := Nat.mul_le_mul_right _ hd
            _ = d ^ 3 := by ring
            _ ≤ d ^ 5 := Nat.pow_le_pow_right (by omega) (by decide)
        exact (h2d2_le.trans_lt hd5_lt).trans_le (Nat.pow_le_pow_left hM₁ (k - 1))
      calc 2 * Bad.card ≤ 2 * (d ^ 2 * M₁ ^ (d - (k - 1))) := Nat.mul_le_mul_left 2 hBad_le
        _ = (2 * d ^ 2) * M₁ ^ (d - (k - 1)) := by ring
        _ < M₁ ^ (k - 1) * M₁ ^ (d - (k - 1)) :=
            Nat.mul_lt_mul_of_pos_right h2d2_lt (pow_pos (by omega) _)
        _ = M₁ ^ d := by rw [← pow_add]; congr 1; omega

end BehrendAndRandomAP

/-! ### Diagnosis 7 Part 3 Helper: Simultaneous Dyadic Commutator Rank -/

section DyadicCommutator

private def diffInvolutionLinear (F : Type*) [Field F] {Q : Type*} (α β : Q → Q) :
    (Q → F) →ₗ[F] (Q → F) where
  toFun f q := f (α q) - f (β q)
  map_add' f g := by funext q; simp [add_sub_add_comm]
  map_smul' c f := by funext q; simp [mul_sub]

private theorem fpfInvolutionRank {Q : Type*} [Fintype Q] [DecidableEq Q]
    (F : Type*) [Field F] (α β : Q → Q) (idx : Q → ℕ)
    (hα : Function.Involutive α) (hβ : Function.Involutive β)
    (hcomm : ∀ q, α (β q) = β (α q))
    (hidx_ne : ∀ q, idx (β (α q)) ≠ idx q) :
    finrank F (LinearMap.range (diffInvolutionLinear F α β)) = Fintype.card Q / 2 := by
  let L := diffInvolutionLinear F α β
  let γ : Q → Q := fun q => β (α q)
  have hγ_inv : Function.Involutive γ := fun q => by
    dsimp [γ]; rw [hcomm (α q), hα q, hβ q]
  have hγ_ne : ∀ q, idx (γ q) ≠ idx q := hidx_ne
  let S_half : Finset Q := Finset.univ.filter (fun q => idx q < idx (γ q))
  have hpart : S_half ∪ S_half.image γ = Finset.univ := by
    ext q
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image, iff_true, S_half]
    rcases lt_trichotomy (idx q) (idx (γ q)) with hlt | heq | hgt
    · exact Or.inl hlt
    · exact absurd heq.symm (hγ_ne q)
    · refine Or.inr ⟨γ q, ?_, hγ_inv q⟩
      rw [hγ_inv q]
      exact hgt
  have hdisj : Disjoint S_half (S_half.image γ) := by
    rw [Finset.disjoint_left]
    intro q hq1 hq2
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq2
    have h1 : idx (γ p) < idx (γ (γ p)) := (Finset.mem_filter.mp hq1).2
    have h2 : idx p < idx (γ p) := (Finset.mem_filter.mp hp).2
    rw [hγ_inv p] at h1
    exact lt_asymm h1 h2
  have hcard_two : 2 * S_half.card = Fintype.card Q := by
    have hu := Finset.card_union_of_disjoint hdisj
    rw [hpart, Finset.card_univ, Finset.card_image_of_injective _ hγ_inv.injective] at hu
    omega
  have hmem_ker : ∀ f : Q → F, f ∈ LinearMap.ker L ↔ ∀ q, f q = f (γ q) := by
    intro f
    rw [LinearMap.mem_ker]
    constructor
    · intro hf q
      have hq := congrFun hf (α q)
      simp only [L, diffInvolutionLinear, LinearMap.coe_mk, AddHom.coe_mk,
        Pi.zero_apply, sub_eq_zero] at hq
      rwa [hα q] at hq
    · intro hf
      funext q
      simp only [L, diffInvolutionLinear, LinearMap.coe_mk, AddHom.coe_mk,
        Pi.zero_apply, sub_eq_zero]
      have hq := hf (α q)
      dsimp [γ] at hq
      rwa [hα q] at hq
  let kerEquiv : LinearMap.ker L ≃ₗ[F] (S_half → F) :=
    { toFun := fun f x => f.1 x.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun g => ⟨fun q =>
        if h : idx q < idx (γ q) then g ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩
        else g ⟨γ q, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
          rw [hγ_inv q]
          rcases lt_trichotomy (idx (γ q)) (idx q) with hlt | heq | hgt
          · exact hlt
          · exact absurd heq (hγ_ne q)
          · exact absurd hgt h⟩⟩, by
        rw [hmem_ker]
        intro q
        by_cases h : idx q < idx (γ q)
        · have h' : ¬ (idx (γ q) < idx (γ (γ q))) := by rw [hγ_inv q]; exact not_lt_of_gt h
          split_ifs
          congr 1
          exact Subtype.ext (hγ_inv q).symm
        · have hlt : idx (γ q) < idx q := by
            rcases lt_trichotomy (idx (γ q)) (idx q) with h1 | h1 | h1
            · exact h1
            · exact absurd h1 (hγ_ne q)
            · exact absurd h1 h
          have h' : idx (γ q) < idx (γ (γ q)) := by rwa [hγ_inv q]
          split_ifs; rfl⟩
      left_inv := fun f => by
        apply Subtype.ext
        funext q
        dsimp only
        split_ifs with h
        · rfl
        · exact ((hmem_ker f.1).mp f.2 q).symm
      right_inv := fun g => by
        funext ⟨q, hq⟩
        have h : idx q < idx (γ q) := (Finset.mem_filter.mp hq).2
        dsimp only
        split_ifs
        rfl }
  have hker_dim : finrank F (LinearMap.ker L) = S_half.card := by
    rw [LinearEquiv.finrank_eq kerEquiv, Module.finrank_pi, Fintype.card_coe]
  have hrn := LinearMap.finrank_range_add_finrank_ker L
  rw [Module.finrank_pi, hker_dim, ← hcard_two] at hrn
  change finrank F (LinearMap.range L) = Fintype.card Q / 2
  omega

private theorem xor_div_two_pow (x y s : ℕ) : (x ^^^ y) / 2 ^ s = (x / 2 ^ s) ^^^ (y / 2 ^ s) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_div_two_pow, Nat.testBit_xor, Nat.testBit_xor,
    Nat.testBit_div_two_pow, Nat.testBit_div_two_pow]

private theorem xor_mod_two_pow (x y s : ℕ) : (x ^^^ y) % 2 ^ s = (x % 2 ^ s) ^^^ (y % 2 ^ s) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_xor, Nat.testBit_xor,
    Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
  by_cases hi : i < s <;> simp [hi]

private theorem xor_lt_two_pow {x y s : ℕ} (hx : x < 2 ^ s) (hy : y < 2 ^ s) :
    x ^^^ y < 2 ^ s :=
  Nat.xor_lt_two_pow hx hy

private theorem two_mul_add_div_mod (u v : ℕ) (hv : v < 2) :
    (2 * u + v) / 2 = u ∧ (2 * u + v) % 2 = v := by
  omega

private theorem dyadicCommutatorRank :
    ∀ (F : Type*) [Field F] (m b : ℕ) (j : Fin m),
      1 ≤ m → 1 ≤ b →
      let S := stoneShuffleGridLinear F m b
      let G := colBitFlipGridLinear F b j
      finrank F (LinearMap.range (S.comp G - G.comp S)) = b * ((2 ^ m) ^ 2) / 2 := by
  intro F _ m b j hm _
  cases m with
  | zero => omega
  | succ m' =>
    dsimp only
    let d := 2 ^ (m' + 1)
    have hd : 0 < d := Nat.two_pow_pos (m' + 1)
    have hd_split : d = 2 * 2 ^ m' := by dsimp [d]; rw [pow_succ]; ring
    have hd_mod : ∀ x : ℕ, x % d = x % (2 * 2 ^ m') := fun x => congrArg (x % ·) hd_split
    let S := stoneShuffleGridLinear F (m' + 1) b
    let U := stoneUnshuffleGridLinear F (m' + 1) b
    let G := colBitFlipGridLinear F b j
    -- Coordinate maps on `Fin d × Fin d`
    let σ (rc : Fin d × Fin d) : Fin d × Fin d :=
      (⟨((rc.2.val % 2) * 2 ^ m' + rc.1.val / 2) % d, Nat.mod_lt _ hd⟩,
       ⟨((rc.1.val % 2) * 2 ^ m' + rc.2.val / 2) % d, Nat.mod_lt _ hd⟩)
    let τ (rc : Fin d × Fin d) : Fin d × Fin d :=
      (⟨(2 * rc.1.val + rc.2.val / 2 ^ m') % d, Nat.mod_lt _ hd⟩,
       ⟨(2 * rc.2.val + rc.1.val / 2 ^ m') % d, Nat.mod_lt _ hd⟩)
    have hτ_val : ∀ r c : Fin d,
        (τ (r, c)).1.val = 2 * (r.val % 2 ^ m') + c.val / 2 ^ m' ∧
        (τ (r, c)).2.val = 2 * (c.val % 2 ^ m') + r.val / 2 ^ m' := by
      intro r c
      have hr : r.val < 2 * 2 ^ m' := by linarith [r.isLt, hd_split]
      have hc : c.val < 2 * 2 ^ m' := by linarith [c.isLt, hd_split]
      have h1 : ∀ u v : ℕ, u < 2 * 2 ^ m' → v < 2 * 2 ^ m' →
          (2 * u + v / 2 ^ m') % (2 * 2 ^ m') = 2 * (u % 2 ^ m') + v / 2 ^ m' := by
        intro u v hu hv
        have hvd : v / 2 ^ m' < 2 := Nat.div_lt_of_lt_mul (by linarith)
        have hdiv_u : u = 2 ^ m' * (u / 2 ^ m') + u % 2 ^ m' := (Nat.div_add_mod u (2 ^ m')).symm
        have hum : u % 2 ^ m' < 2 ^ m' := Nat.mod_lt _ (Nat.two_pow_pos m')
        have heq : 2 * u + v / 2 ^ m' =
            (2 * (u % 2 ^ m') + v / 2 ^ m') + (2 * 2 ^ m') * (u / 2 ^ m') := by
          conv_lhs => rw [hdiv_u]
          ring
        rw [heq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
      exact ⟨by dsimp [τ]; rw [hd_mod]; exact h1 r.val c.val hr hc,
             by dsimp [τ]; rw [hd_mod]; exact h1 c.val r.val hc hr⟩
    have hσ_val : ∀ p : Fin d × Fin d,
        (σ p).1.val = (p.2.val % 2) * 2 ^ m' + p.1.val / 2 ∧
        (σ p).2.val = (p.1.val % 2) * 2 ^ m' + p.2.val / 2 := by
      rintro ⟨r', c'⟩
      have hr'_lt : r'.val < 2 * 2 ^ m' := by linarith [r'.isLt, hd_split]
      have hc'_lt : c'.val < 2 * 2 ^ m' := by linarith [c'.isLt, hd_split]
      have hr' : r'.val / 2 < 2 ^ m' := Nat.div_lt_of_lt_mul hr'_lt
      have hc' : c'.val / 2 < 2 ^ m' := Nat.div_lt_of_lt_mul hc'_lt
      have hrm : r'.val % 2 < 2 := Nat.mod_lt _ (by decide)
      have hcm : c'.val % 2 < 2 := Nat.mod_lt _ (by decide)
      have hlt1 : (c'.val % 2) * 2 ^ m' + r'.val / 2 < d := by
        have : (c'.val % 2) * 2 ^ m' ≤ 1 * 2 ^ m' := Nat.mul_le_mul_right _ (by omega)
        linarith [hd_split]
      have hlt2 : (r'.val % 2) * 2 ^ m' + c'.val / 2 < d := by
        have : (r'.val % 2) * 2 ^ m' ≤ 1 * 2 ^ m' := Nat.mul_le_mul_right _ (by omega)
        linarith [hd_split]
      exact ⟨Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2⟩
    have hστ : ∀ p : Fin d × Fin d, σ (τ p) = p := by
      rintro ⟨r, c⟩
      obtain ⟨hτ1, hτ2⟩ := hτ_val r c
      obtain ⟨hσ1, hσ2⟩ := hσ_val (τ (r, c))
      have hrd : r.val / 2 ^ m' < 2 := Nat.div_lt_of_lt_mul (by linarith [r.isLt, hd_split])
      have hcd : c.val / 2 ^ m' < 2 := Nat.div_lt_of_lt_mul (by linarith [c.isLt, hd_split])
      ext
      · dsimp only
        rw [hσ1, hτ1, hτ2]
        rw [(two_mul_add_div_mod _ _ hrd).2, (two_mul_add_div_mod _ _ hcd).1]
        have hdiv_r := Nat.div_add_mod r.val (2 ^ m')
        linarith
      · dsimp only
        rw [hσ2, hτ1, hτ2]
        rw [(two_mul_add_div_mod _ _ hcd).2, (two_mul_add_div_mod _ _ hrd).1]
        have hdiv_c := Nat.div_add_mod c.val (2 ^ m')
        linarith
    have hτσ : ∀ p : Fin d × Fin d, τ (σ p) = p := by
      rintro ⟨r', c'⟩
      obtain ⟨hσ1, hσ2⟩ := hσ_val (r', c')
      obtain ⟨hτ1, hτ2⟩ := hτ_val (σ (r', c')).1 (σ (r', c')).2
      have hr2 : r'.val / 2 < 2 ^ m' := Nat.div_lt_of_lt_mul (by linarith [r'.isLt, hd_split])
      have hc2 : c'.val / 2 < 2 ^ m' := Nat.div_lt_of_lt_mul (by linarith [c'.isLt, hd_split])
      have hp_pos : 0 < 2 ^ m' := Nat.two_pow_pos m'
      ext
      · dsimp only
        rw [hτ1, hσ1, hσ2]
        have hm : ((c'.val % 2) * 2 ^ m' + r'.val / 2) % 2 ^ m' = r'.val / 2 := by
          rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr2]
        have hdv : ((r'.val % 2) * 2 ^ m' + c'.val / 2) / 2 ^ m' = r'.val % 2 := by
          rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp_pos, Nat.div_eq_of_lt hc2, zero_add]
        rw [hm, hdv]; omega
      · dsimp only
        rw [hτ2, hσ1, hσ2]
        have hm : ((r'.val % 2) * 2 ^ m' + c'.val / 2) % 2 ^ m' = c'.val / 2 := by
          rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc2]
        have hdv : ((c'.val % 2) * 2 ^ m' + r'.val / 2) / 2 ^ m' = c'.val % 2 := by
          rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp_pos, Nat.div_eq_of_lt hr2, zero_add]
        rw [hm, hdv]; omega
    -- `U` as a linear equivalence composed with uncurrying to `Q = Fin d × Fin d × Fin b`
    let Q := Fin d × Fin d × Fin b
    let curryEqv : (Q → F) ≃ₗ[F] GridState F d b :=
      { toFun := fun f r c ℓ => f (r, c, ℓ)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        invFun := fun X q => X q.1 q.2.1 q.2.2
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    let U_eqv : GridState F d b ≃ₗ[F] GridState F d b :=
      { U with
        invFun := S
        left_inv := fun X => by
          funext r' c' ℓ
          have h := hτσ (r', c')
          change X (τ (σ (r', c'))).1 (τ (σ (r', c'))).2 ℓ = X r' c' ℓ
          rw [h]
        right_inv := fun X => by
          funext r c ℓ
          have h := hστ (r, c)
          change X (σ (τ (r, c))).1 (σ (τ (r, c))).2 ℓ = X r c ℓ
          rw [h] }
    -- Define `α, β : Q → Q`
    let gFlip (rc : Fin d × Fin d) : Fin d × Fin d :=
      (rc.1, ⟨(rc.2.val ^^^ 2 ^ j.val) % d, Nat.mod_lt _ hd⟩)
    have h2j_lt : 2 ^ j.val < d := Nat.pow_lt_pow_right (by decide) j.isLt
    have hgFlip_val : ∀ p : Fin d × Fin d, (gFlip p).2.val = p.2.val ^^^ 2 ^ j.val := by
      intro p
      dsimp [gFlip]
      exact Nat.mod_eq_of_lt (xor_lt_two_pow p.2.isLt h2j_lt)
    let α (q : Q) : Q := ((gFlip (q.1, q.2.1)).1, (gFlip (q.1, q.2.1)).2, q.2.2)
    let β (q : Q) : Q :=
      let p := σ (gFlip (τ (q.1, q.2.1)))
      (p.1, p.2, q.2.2)
    -- Verify `curryEqv.symm ∘ U_eqv ∘ (S ∘ G - G ∘ S) ∘ curryEqv = diffInvolutionLinear F α β`
    let M_op : GridState F d b →ₗ[F] GridState F d b := S.comp G - G.comp S
    have hconj : (curryEqv.symm.toLinearMap.comp (U_eqv.toLinearMap.comp
        (M_op.comp curryEqv.toLinearMap))) = diffInvolutionLinear F α β := by
      apply LinearMap.ext
      intro f
      funext ⟨r, c, ℓ⟩
      change (U (S (G (curryEqv f)) - G (S (curryEqv f)))) r c ℓ = f (α (r, c, ℓ)) - f (β (r, c, ℓ))
      have hUS : U (S (G (curryEqv f))) r c ℓ = (G (curryEqv f)) r c ℓ :=
        congrFun (congrFun (congrFun (U_eqv.right_inv (G (curryEqv f))) r) c) ℓ
      have hlin : (U (S (G (curryEqv f)) - G (S (curryEqv f)))) r c ℓ =
          U (S (G (curryEqv f))) r c ℓ - U (G (S (curryEqv f))) r c ℓ := by
        rw [map_sub]; rfl
      rw [hlin, hUS]
      rfl
    have hrk_eq : finrank F (LinearMap.range M_op) =
        finrank F (LinearMap.range (diffInvolutionLinear F α β)) := by
      rw [← hconj]
      let outEqv : GridState F d b ≃ₗ[F] (Q → F) := U_eqv.trans curryEqv.symm
      change finrank F (LinearMap.range M_op) =
        finrank F (LinearMap.range (outEqv.toLinearMap.comp (M_op.comp curryEqv.toLinearMap)))
      have h1 : LinearMap.range (M_op.comp curryEqv.toLinearMap) = LinearMap.range M_op :=
        LinearMap.range_comp_of_range_eq_top M_op curryEqv.range
      rw [LinearMap.range_comp, h1]
      exact (LinearEquiv.finrank_map_eq outEqv (LinearMap.range M_op)).symm
    -- Prove `α, β` are commuting involutions with `α q ≠ β q`
    have hα_inv : Function.Involutive α := by
      rintro ⟨r, c, ℓ⟩
      ext
      · rfl
      · dsimp [α]
        rw [hgFlip_val, hgFlip_val, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
      · rfl
    have hβ_inv : Function.Involutive β := by
      rintro ⟨r, c, ℓ⟩
      have hg_inv : ∀ p : Fin d × Fin d, gFlip (gFlip p) = p := by
        rintro ⟨r₀, c₀⟩
        ext
        · rfl
        · rw [hgFlip_val, hgFlip_val, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
      dsimp [β]
      have hstep : σ (gFlip (τ (σ (gFlip (τ (r, c)))))) = (r, c) := by
        rw [hτσ, hg_inv, hστ]
      rw [hstep]
    -- Explicit formula for `σ (gFlip (τ (r, c)))` in the two cases `j.val = 0` vs `j.val = k + 1`
    have hβ_explicit : ∀ r c : Fin d,
        (j.val = 0 →
          (σ (gFlip (τ (r, c)))).1.val = r.val ^^^ 2 ^ m' ∧
          (σ (gFlip (τ (r, c)))).2.val = c.val) ∧
        (∀ k : ℕ, j.val = k + 1 →
          (σ (gFlip (τ (r, c)))).1.val = r.val ∧
          (σ (gFlip (τ (r, c)))).2.val = c.val ^^^ 2 ^ k) := by
      intro r c
      obtain ⟨hτ1, hτ2⟩ := hτ_val r c
      have hg2 := hgFlip_val (τ (r, c))
      obtain ⟨hσ1, hσ2⟩ := hσ_val (gFlip (τ (r, c)))
      have hg1 : (gFlip (τ (r, c))).1 = (τ (r, c)).1 := rfl
      have hrd : r.val / 2 ^ m' < 2 := Nat.div_lt_of_lt_mul (by linarith [r.isLt, hd_split])
      have hcd : c.val / 2 ^ m' < 2 := Nat.div_lt_of_lt_mul (by linarith [c.isLt, hd_split])
      have hr1_div : (τ (r, c)).1.val / 2 = r.val % 2 ^ m' := by
        rw [hτ1]; exact (two_mul_add_div_mod _ _ hcd).1
      have hr1_mod : (τ (r, c)).1.val % 2 = c.val / 2 ^ m' := by
        rw [hτ1]; exact (two_mul_add_div_mod _ _ hcd).2
      constructor
      · intro hj0
        rw [hj0, pow_zero] at hg2
        have hc2_div : (gFlip (τ (r, c))).2.val / 2 = c.val % 2 ^ m' := by
          rw [hg2]
          have h := xor_div_two_pow (τ (r, c)).2.val 1 1
          simp only [pow_one] at h
          rw [h, hτ2, (two_mul_add_div_mod _ _ hrd).1]
          simp
        have hc2_mod : (gFlip (τ (r, c))).2.val % 2 = (r.val / 2 ^ m') ^^^ 1 := by
          rw [hg2]
          have h := xor_mod_two_pow (τ (r, c)).2.val 1 1
          simp only [pow_one] at h
          rw [h, hτ2, (two_mul_add_div_mod _ _ hrd).2]
        constructor
        · rw [hσ1, hg1, hc2_mod, hr1_div]
          have hd_xor := xor_div_two_pow r.val (2 ^ m') m'
          have hm_xor := xor_mod_two_pow r.val (2 ^ m') m'
          have hself_div : 2 ^ m' / 2 ^ m' = 1 := Nat.div_self (Nat.two_pow_pos m')
          have hself_mod : 2 ^ m' % 2 ^ m' = 0 := Nat.mod_self _
          rw [hself_div] at hd_xor
          rw [hself_mod, Nat.xor_zero] at hm_xor
          have hdiv_add := Nat.div_add_mod (r.val ^^^ 2 ^ m') (2 ^ m')
          rw [hd_xor, hm_xor] at hdiv_add
          linarith
        · rw [hσ2, hg1, hr1_mod, hc2_div]
          have hdiv_c := Nat.div_add_mod c.val (2 ^ m')
          linarith
      · intro k hjk
        have hk_lt : k < m' := by have := j.isLt; omega
        rw [hjk] at hg2
        have hc2_div : (gFlip (τ (r, c))).2.val / 2 = (c.val % 2 ^ m') ^^^ 2 ^ k := by
          rw [hg2]
          have h := xor_div_two_pow (τ (r, c)).2.val (2 ^ (k + 1)) 1
          simp only [pow_one] at h
          have hpk : 2 ^ (k + 1) / 2 = 2 ^ k := by rw [pow_succ]; omega
          rw [h, hτ2, (two_mul_add_div_mod _ _ hrd).1, hpk]
        have hc2_mod : (gFlip (τ (r, c))).2.val % 2 = r.val / 2 ^ m' := by
          rw [hg2]
          have h := xor_mod_two_pow (τ (r, c)).2.val (2 ^ (k + 1)) 1
          simp only [pow_one] at h
          have hpk : 2 ^ (k + 1) % 2 = 0 := by rw [pow_succ]; omega
          rw [h, hτ2, (two_mul_add_div_mod _ _ hrd).2, hpk, Nat.xor_zero]
        constructor
        · rw [hσ1, hg1, hc2_mod, hr1_div]
          have hdiv_r := Nat.div_add_mod r.val (2 ^ m')
          linarith
        · rw [hσ2, hg1, hr1_mod, hc2_div]
          have hd_xor := xor_div_two_pow c.val (2 ^ k) m'
          have hm_xor := xor_mod_two_pow c.val (2 ^ k) m'
          have h2k_lt : 2 ^ k < 2 ^ m' := Nat.pow_lt_pow_right (by decide) hk_lt
          rw [Nat.div_eq_of_lt h2k_lt, Nat.xor_zero] at hd_xor
          rw [Nat.mod_eq_of_lt h2k_lt] at hm_xor
          have hdiv_add := Nat.div_add_mod (c.val ^^^ 2 ^ k) (2 ^ m')
          rw [hd_xor, hm_xor] at hdiv_add
          linarith
    have hcomm : ∀ q : Q, α (β q) = β (α q) := by
      rintro ⟨r, c, ℓ⟩
      cases hk : j.val with
      | zero =>
        obtain ⟨hb1, hb2⟩ := (hβ_explicit r c).1 hk
        obtain ⟨hb1', hb2'⟩ := (hβ_explicit (α (r, c, ℓ)).1 (α (r, c, ℓ)).2.1).1 hk
        ext
        · dsimp [α, β, gFlip] at hb1 hb1' ⊢
          rw [hb1, hb1']
        · dsimp [α, β]
          rw [hgFlip_val, hb2, hb2', hgFlip_val]
        · rfl
      | succ k =>
        obtain ⟨hb1, hb2⟩ := (hβ_explicit r c).2 k hk
        obtain ⟨hb1', hb2'⟩ := (hβ_explicit (α (r, c, ℓ)).1 (α (r, c, ℓ)).2.1).2 k hk
        ext
        · dsimp [α, β, gFlip] at hb1 hb1' ⊢
          rw [hb1, hb1']
        · dsimp [α, β]
          rw [hgFlip_val, hb2, hb2', hgFlip_val, Nat.xor_assoc,
            Nat.xor_comm (2 ^ k) (2 ^ j.val), ← Nat.xor_assoc]
        · rfl
    have hne_c : ∀ q : Q, (α q).2.1.val ≠ (β q).2.1.val := by
      rintro ⟨r, c, ℓ⟩ hc_eq
      dsimp [α, β] at hc_eq
      rw [hgFlip_val] at hc_eq
      cases hk : j.val with
      | zero =>
        obtain ⟨_, hb2⟩ := (hβ_explicit r c).1 hk
        rw [hb2, hk, pow_zero] at hc_eq
        have hx := congrArg (c.val ^^^ ·) hc_eq
        rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor] at hx
        omega
      | succ k =>
        obtain ⟨_, hb2⟩ := (hβ_explicit r c).2 k hk
        rw [hb2, hk] at hc_eq
        have hx := congrArg (c.val ^^^ ·) hc_eq
        rw [← Nat.xor_assoc, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor, Nat.zero_xor] at hx
        have hlt : 2 ^ k < 2 ^ (k + 1) := Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self k)
        omega
    have hidx_ne : ∀ q : Q, (β (α q)).2.1.val ≠ q.2.1.val := fun q h => by
      have hc := hne_c (α q)
      rw [hα_inv q] at hc
      exact hc h.symm
    change finrank F (LinearMap.range M_op) = b * (d ^ 2) / 2
    rw [hrk_eq, fpfInvolutionRank F α β (fun q => q.2.1.val) hα_inv hβ_inv hcomm hidx_ne]
    have hQ_card : Fintype.card Q = b * (d ^ 2) := by
      dsimp [Q]
      rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
      ring
    rw [hQ_card]

end DyadicCommutator

section ShufShearTM

/-! ### 1. Encoding Index Characterization & Entry-Width Bounds -/

private theorem nth_eq_getElem?_tm : ∀ (xs : List Bool) (i : ℕ), Transpose.nth xs i = xs[i]?
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: bs, i + 1 => by
    simpa only [Transpose.nth, List.getElem?_cons_succ] using nth_eq_getElem?_tm bs i

private theorem readInput_of_nonneg (w : List Bool) (n : ℕ) :
    Transpose.readInput w (n : Int) = w[n]? := by
  unfold Transpose.readInput
  have h : ¬ ((n : Int) < 0) := by omega
  rw [ite_eq_right h, Int.toNat_natCast, nth_eq_getElem?_tm]

private theorem mul_add_div_mod_tm {q s r : ℕ} (hr : r < s) :
    (q * s + r) / s = q ∧ (q * s + r) % s = r := by
  have hs : 0 < s := by omega
  constructor
  · calc (q * s + r) / s = (r + s * q) / s := by rw [Nat.add_comm, Nat.mul_comm]
      _ = r / s + q := Nat.add_mul_div_left r q hs
      _ = q := by rw [Nat.div_eq_zero_iff.mpr (Or.inr hr), Nat.zero_add]
  · calc (q * s + r) % s = (r + s * q) % s := by rw [Nat.add_comm, Nat.mul_comm]
      _ = r % s := Nat.add_mul_mod_self_left r s q
      _ = r := Nat.mod_eq_of_lt hr

private theorem concatUpTo_len_get {f : ℕ → List Bool} {m s : ℕ}
    (hlen : ∀ i < m, (f i).length = s) :
    (Transpose.concatUpTo f m).length = m * s ∧
      ∀ k < m * s, (Transpose.concatUpTo f m)[k]? = (f (k / s))[k % s]? := by
  induction m with
  | zero =>
    simp [Transpose.concatUpTo]
  | succ m ih =>
    obtain ⟨ihL, ihG⟩ := ih (fun i hi => hlen i (Nat.lt_succ_of_lt hi))
    have hmL : (f m).length = s := hlen m (Nat.lt_succ_self m)
    refine ⟨?_, ?_⟩
    · simp only [Transpose.concatUpTo, List.length_append, ihL, hmL]
      ring
    · intro k hk
      simp only [Transpose.concatUpTo]
      by_cases hk1 : k < m * s
      · have hkLen : k < (Transpose.concatUpTo f m).length := by omega
        rw [List.getElem?_append_left hkLen]
        exact ihG k hk1
      · have hkGe : m * s ≤ k := Nat.le_of_not_gt hk1
        have hkGeLen : (Transpose.concatUpTo f m).length ≤ k := by omega
        rw [List.getElem?_append_right hkGeLen, ihL]
        have hrem : k - m * s < s := by
          have : (m + 1) * s = m * s + s := by ring
          omega
        have hkEq : m * s + (k - m * s) = k := Nat.add_sub_of_le hkGe
        obtain ⟨hdiv, hmod⟩ := mul_add_div_mod_tm hrem
        rw [hkEq] at hdiv hmod
        rw [hdiv, hmod]

private theorem encode_len_get (d b : ℕ) (A : Transpose.Matrix) :
    (Transpose.encode d b A).length = d * d * b ∧
      ∀ idx < d * d * b,
        (Transpose.encode d b A)[idx]? =
          some (A (idx / (d * b)) ((idx % (d * b)) / b) ((idx % (d * b)) % b)) := by
  let g₃ (i j t : ℕ) : List Bool := [A i j t]
  let g₂ (i j : ℕ) : List Bool := Transpose.concatUpTo (g₃ i j) b
  have hg₂ : ∀ i j, (g₂ i j).length = b ∧
      ∀ t < b, (g₂ i j)[t]? = some (A i j t) := by
    intro i j
    obtain ⟨hL, hG⟩ := concatUpTo_len_get (f := g₃ i j) (m := b) (s := 1)
      (fun _ _ => rfl)
    refine ⟨by simpa using hL, fun t ht => ?_⟩
    have hGt := hG t (by omega)
    rw [Nat.div_one, Nat.mod_one] at hGt
    exact hGt
  let g₁ (i : ℕ) : List Bool := Transpose.concatUpTo (g₂ i) d
  have hg₁ : ∀ i, (g₁ i).length = d * b ∧
      ∀ rem < d * b, (g₁ i)[rem]? = some (A i (rem / b) (rem % b)) := by
    intro i
    obtain ⟨hL, hG⟩ := concatUpTo_len_get (f := g₂ i) (m := d) (s := b)
      (fun j _ => (hg₂ i j).1)
    refine ⟨hL, fun rem hrem => ?_⟩
    have hbPos : 0 < b := by
      by_contra hb0
      have hb0' : b = 0 := by omega
      rw [hb0', mul_zero] at hrem
      exact Nat.not_lt_zero rem hrem
    rw [hG rem hrem, (hg₂ i (rem / b)).2 (rem % b) (Nat.mod_lt rem hbPos)]
  obtain ⟨hL, hG⟩ := concatUpTo_len_get (f := g₁) (m := d) (s := d * b)
    (fun i _ => (hg₁ i).1)
  have hAssoc : d * (d * b) = d * d * b := (Nat.mul_assoc d d b).symm
  refine ⟨by simpa only [Transpose.encode, g₁, g₂, hAssoc] using hL, ?_⟩
  intro idx hidx
  have hidx' : idx < d * (d * b) := by omega
  have hdbPos : 0 < d * b := by
    by_contra h0
    have h0' : d * b = 0 := by omega
    rw [h0', mul_zero] at hidx'
    exact Nat.not_lt_zero idx hidx'
  change (Transpose.concatUpTo g₁ d)[idx]? = _
  rw [hG idx hidx', (hg₁ (idx / (d * b))).2 (idx % (d * b)) (Nat.mod_lt idx hdbPos)]

private theorem encode_entry_bit (d b : ℕ) (A : Transpose.Matrix)
    {e t : ℕ} (he : e < d * d) (ht : t < b) :
    (Transpose.encode d b A)[e * b + t]? = some (A (e / d) (e % d) t) := by
  have hd_pos : 0 < d := by
    by_contra h0; have : d = 0 := by omega
    rw [this] at he; simp at he
  have hidx : e * b + t < d * d * b := by
    calc e * b + t < e * b + b := by omega
      _ = (e + 1) * b := by ring
      _ ≤ (d * d) * b := Nat.mul_le_mul_right b (by omega)
  rw [(encode_len_get d b A).2 (e * b + t) hidx]
  have hed : e = (e / d) * d + (e % d) := by
    rw [Nat.mul_comm, Nat.div_add_mod]
  have hrem_lt : (e % d) * b + t < d * b := by
    have : e % d < d := Nat.mod_lt e hd_pos
    calc (e % d) * b + t < (e % d) * b + b := by omega
      _ = (e % d + 1) * b := by ring
      _ ≤ d * b := Nat.mul_le_mul_right b (by omega)
  have hsplit : e * b + t = (e / d) * (d * b) + ((e % d) * b + t) := by
    calc e * b + t = ((e / d) * d + (e % d)) * b + t := by rw [← hed]
      _ = (e / d) * (d * b) + ((e % d) * b + t) := by ring
  obtain ⟨hd1, hm1⟩ := mul_add_div_mod_tm hrem_lt
  obtain ⟨hd2, hm2⟩ := mul_add_div_mod_tm ht
  rw [hsplit, hd1, hm1, hd2, hm2]

private theorem entryBits_pos_tm (d : ℕ) : 1 ≤ Transpose.entryBits d := by
  unfold Transpose.entryBits; omega

private theorem inputLength_pos {d : ℕ} (hd : 1 ≤ d) : 1 ≤ Transpose.inputLength d := by
  unfold Transpose.inputLength
  have hb := entryBits_pos_tm d
  nlinarith

private theorem entryBits_quad_upper {d : ℕ} (hd : 1 ≤ d) :
    Transpose.inputLength d ≤ 4 ^ (Transpose.entryBits d) * Transpose.entryBits d := by
  unfold Transpose.inputLength Transpose.entryBits
  set b := (d - 1).log2 + 1
  have hlt : d - 1 < 2 ^ b := Nat.lt_log2_self
  have hd_le : d ≤ 2 ^ b := by omega
  have hsq : d * d ≤ 4 ^ b := by
    calc d * d ≤ 2 ^ b * 2 ^ b := Nat.mul_le_mul hd_le hd_le
      _ = (2 * 2) ^ b := (Nat.mul_pow 2 2 b).symm
      _ = 4 ^ b := rfl
  exact Nat.mul_le_mul_right b hsq

private theorem entryBits_quad_lower {d s : ℕ} (hs1 : 1 ≤ s) (hsb : s < Transpose.entryBits d) :
    4 ^ s * s < Transpose.inputLength d := by
  unfold Transpose.entryBits at hsb
  unfold Transpose.inputLength Transpose.entryBits
  set b := (d - 1).log2 + 1
  have hdm1 : d - 1 ≠ 0 := by
    intro h0
    have : (d - 1).log2 = 0 := by rw [h0]; rfl
    omega
  have h2le : 2 ^ (b - 1) ≤ d - 1 := Nat.log2_self_le hdm1
  have hs_le : s ≤ b - 1 := by omega
  have h2s_lt : 2 ^ s < d := by
    have : 2 ^ s ≤ 2 ^ (b - 1) := Nat.pow_le_pow_right (by decide) hs_le
    omega
  have h4s_lt : 4 ^ s < d * d := by
    calc 4 ^ s = (2 * 2) ^ s := rfl
      _ = 2 ^ s * 2 ^ s := Nat.mul_pow 2 2 s
      _ < d * d := Nat.mul_lt_mul_of_lt_of_lt h2s_lt h2s_lt
  exact Nat.mul_lt_mul_of_lt_of_lt h4s_lt hsb

private theorem entryBits_quad_le_four_L {d : ℕ} (hd : 1 ≤ d) :
    4 ^ (Transpose.entryBits d) * Transpose.entryBits d ≤ 4 * Transpose.inputLength d := by
  by_cases hd1 : d = 1
  · subst hd1; decide
  · unfold Transpose.inputLength Transpose.entryBits
    set k := (d - 1).log2
    have hdm1 : d - 1 ≠ 0 := by omega
    have h2le : 2 ^ k ≤ d - 1 := Nat.log2_self_le hdm1
    have h4k_le : 4 ^ k ≤ d * d := by
      have hk_le : 2 ^ k ≤ d := by omega
      calc 4 ^ k = (2 * 2) ^ k := rfl
        _ = 2 ^ k * 2 ^ k := Nat.mul_pow 2 2 k
        _ ≤ d * d := Nat.mul_le_mul hk_le hk_le
    calc 4 ^ (k + 1) * (k + 1) = (4 * 4 ^ k) * (k + 1) := by rw [pow_succ']
      _ ≤ (4 * (d * d)) * (k + 1) := Nat.mul_le_mul_right (k + 1) (Nat.mul_le_mul_left 4 h4k_le)
      _ = 4 * (d * d * (k + 1)) := by ring

private theorem entryBits_two_pow {m : ℕ} (hm : 1 ≤ m) :
    Transpose.entryBits (2 ^ m) = m := by
  have hd2 : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) hm
  unfold Transpose.entryBits
  have hm0 : 2 ^ m - 1 ≠ 0 := by omega
  obtain ⟨m', rfl⟩ := Nat.exists_eq_add_of_le' hm
  have hlo : 2 ^ m' ≤ 2 ^ (m' + 1) - 1 := by
    have : 1 ≤ 2 ^ m' := Nat.two_pow_pos m'
    rw [pow_succ]; omega
  have hhi : 2 ^ (m' + 1) - 1 < 2 ^ (m' + 1) := by
    have : 1 ≤ 2 ^ (m' + 1) := Nat.two_pow_pos (m' + 1)
    omega
  have h1 : m' ≤ (2 ^ (m' + 1) - 1).log2 := (Nat.le_log2 hm0).mpr hlo
  have h2 : (2 ^ (m' + 1) - 1).log2 < m' + 1 := (Nat.log2_lt hm0).mpr hhi
  omega

private theorem stoneShuffle_encode_bit {m' : ℕ} (A : Transpose.Matrix) :
    let m := m' + 1
    let d := 2 ^ m
    let b := Transpose.entryBits d
    let H := 2 * 4 ^ m'
    ∀ e < 2 * H, ∀ t < b,
      (Transpose.encode d b (stoneShuffleTMMatrix m A))[e * b + t]? =
        (Transpose.encode d b A)[((e % 2) * H + e / 2) * b + t]? := by
  intro m d b H e he t ht
  have hd_eq : d = 2 * 2 ^ m' := by dsimp [d, m]; rw [pow_succ']
  have hdd_eq : d * d = 2 * H := by
    dsimp [H]; rw [hd_eq]
    calc (2 * 2 ^ m') * (2 * 2 ^ m') = 2 * (2 * (2 ^ m' * 2 ^ m')) := by ring
      _ = 2 * (2 * (2 * 2) ^ m') := by rw [Nat.mul_pow 2 2 m']
      _ = 2 * (2 * 4 ^ m') := rfl
  have he_dd : e < d * d := by omega
  have hsrc_lt : (e % 2) * H + e / 2 < d * d := by
    have h1 : e % 2 ≤ 1 := by omega
    have h2 : (e % 2) * H ≤ 1 * H := Nat.mul_le_mul_right H h1
    omega
  rw [encode_entry_bit d b (stoneShuffleTMMatrix m A) he_dd ht,
      encode_entry_bit d b A hsrc_lt ht]
  congr 1
  set r' := e / d
  set c' := e % d
  have hd_pos : 0 < d := Nat.two_pow_pos m
  have hr'_lt : r' < d := Nat.div_lt_of_lt_mul (by omega)
  have hc'_lt : c' < d := Nat.mod_lt e hd_pos
  have he_decomp : e = r' * d + c' := by
    dsimp [r', c']; rw [Nat.mul_comm, Nat.div_add_mod]
  have hr'2_lt : r' / 2 < 2 ^ m' := by omega
  have hc'2_lt : c' / 2 < 2 ^ m' := by omega
  have hc'mod : c' % 2 ≤ 1 := by omega
  have hr'mod : r' % 2 ≤ 1 := by omega
  have hsrcR_lt : (c' % 2) * 2 ^ m' + r' / 2 < d := by
    have : (c' % 2) * 2 ^ m' ≤ 1 * 2 ^ m' := Nat.mul_le_mul_right _ hc'mod
    omega
  have hsrcC_lt : (r' % 2) * 2 ^ m' + c' / 2 < d := by
    have : (r' % 2) * 2 ^ m' ≤ 1 * 2 ^ m' := Nat.mul_le_mul_right _ hr'mod
    omega
  let srcR := (c' % 2) * 2 ^ m' + r' / 2
  let srcC := (r' % 2) * 2 ^ m' + c' / 2
  have he_mod2 : e % 2 = c' % 2 := by
    calc e % 2 = (r' * (2 * 2 ^ m') + c') % 2 := by rw [← hd_eq, ← he_decomp]
      _ = (c' + 2 * (r' * 2 ^ m')) % 2 := by ring_nf
      _ = c' % 2 := Nat.add_mul_mod_self_left c' 2 (r' * 2 ^ m')
  have he_div2 : e / 2 = r' * 2 ^ m' + c' / 2 := by
    calc e / 2 = (c' + 2 * (r' * 2 ^ m')) / 2 := by
          have : e = c' + 2 * (r' * 2 ^ m') := by rw [he_decomp, hd_eq]; ring
          rw [this]
      _ = c' / 2 + r' * 2 ^ m' := Nat.add_mul_div_left c' (r' * 2 ^ m') (by decide)
      _ = r' * 2 ^ m' + c' / 2 := Nat.add_comm _ _
  have hflat : (e % 2) * H + e / 2 = srcR * d + srcC := by
    have hr'_split : 2 * (r' / 2) + r' % 2 = r' := Nat.div_add_mod r' 2
    have hH_eq : H = 2 ^ m' * d := by
      dsimp [H]; rw [hd_eq]
      calc 2 * 4 ^ m' = 2 * (2 * 2) ^ m' := rfl
        _ = 2 * (2 ^ m' * 2 ^ m') := by rw [Nat.mul_pow 2 2 m']
        _ = 2 ^ m' * (2 * 2 ^ m') := by ring
    rw [he_mod2, he_div2, hH_eq]
    dsimp [srcR, srcC]
    rw [hd_eq]
    nlinarith [hr'_split]
  obtain ⟨hdiv_src, hmod_src⟩ := mul_add_div_mod_tm hsrcC_lt
  rw [hflat, hdiv_src, hmod_src]
  change A ((c' % 2 * 2 ^ m' + r' / 2) % d) ((r' % 2 * 2 ^ m' + c' / 2) % d) t =
    A srcR srcC t
  rw [Nat.mod_eq_of_lt hsrcR_lt, Nat.mod_eq_of_lt hsrcC_lt]

/-! ### 2. Compositional Block Compiler to `Transpose.TM` -/

private structure Mem (k : ℕ) (Sym : Type) where
  inPos   : Int
  work    : Fin k → Int → Sym
  workPos : Fin k → Int
  outRev  : List Bool

private theorem Mem.eq_of_fields {k : ℕ} {Sym : Type} {m₁ m₂ : Mem k Sym}
    (hIn : m₁.inPos = m₂.inPos)
    (hWork : ∀ i p, m₁.work i p = m₂.work i p)
    (hPos : ∀ i, m₁.workPos i = m₂.workPos i)
    (hOut : m₁.outRev = m₂.outRev) : m₁ = m₂ := by
  cases m₁; cases m₂
  simp only [Mem.mk.injEq]
  exact ⟨hIn, funext fun i => funext fun p => hWork i p, funext hPos, hOut⟩

private abbrev Action (k : ℕ) (Sym : Type) :=
  Option Bool → (Fin k → Sym) → (Transpose.Dir × (Fin k → Sym × Transpose.Dir) × Option Bool)

private def applyAct {k : ℕ} {Sym : Type} (w : List Bool) (a : Action k Sym) (m : Mem k Sym) :
    Mem k Sym :=
  let res := a (Transpose.readInput w m.inPos) (fun i => m.work i (m.workPos i))
  { inPos   := res.1.shift m.inPos
    work    := fun i p => if p = m.workPos i then (res.2.1 i).1 else m.work i p
    workPos := fun i => (res.2.1 i).2.shift (m.workPos i)
    outRev  := match res.2.2 with | none => m.outRev | some b => b :: m.outRev }

private abbrev GStep (k : ℕ) (Sym : Type) :=
  ℕ → Option Bool → (Fin k → Sym) →
    Option (ℕ × Transpose.Dir × (Fin k → Sym × Transpose.Dir) × Option Bool)

private def gStepOne {k : ℕ} {Sym : Type} (G : GStep k Sym) (w : List Bool)
    (cm : ℕ × Mem k Sym) : Option (ℕ × Mem k Sym) :=
  match G cm.1 (Transpose.readInput w cm.2.inPos) (fun i => cm.2.work i (cm.2.workPos i)) with
  | none => none
  | some res =>
    some (res.1,
      { inPos   := res.2.1.shift cm.2.inPos
        work    := fun i p => if p = cm.2.workPos i then (res.2.2.1 i).1 else cm.2.work i p
        workPos := fun i => (res.2.2.1 i).2.shift (cm.2.workPos i)
        outRev  := match res.2.2.2 with | none => cm.2.outRev | some b => b :: cm.2.outRev })

private def gStepN {k : ℕ} {Sym : Type} (G : GStep k Sym) (w : List Bool) :
    ℕ → (ℕ × Mem k Sym) → Option (ℕ × Mem k Sym)
  | 0, cm => some cm
  | n + 1, cm =>
    match gStepOne G w cm with
    | none => none
    | some cm' => gStepN G w n cm'

private theorem gStepN_add {k : ℕ} {Sym : Type} (G : GStep k Sym) (w : List Bool) :
    ∀ (a b : ℕ) (cm : ℕ × Mem k Sym),
      gStepN G w (a + b) cm =
        match gStepN G w a cm with
        | none => none
        | some cm' => gStepN G w b cm'
  | 0, _, cm => by simp [gStepN]
  | a + 1, b, cm => by
    rw [Nat.succ_add]
    simp only [gStepN]
    cases gStepOne G w cm with
    | none => rfl
    | some cm' => exact gStepN_add G w a b cm'

private def GReach {k : ℕ} {Sym : Type} (G : GStep k Sym) (w : List Bool)
    (cm₁ cm₂ : ℕ × Mem k Sym) (t : ℕ) : Prop :=
  ∃ s ≤ t, gStepN G w s cm₁ = some cm₂

private theorem GReach.refl {k : ℕ} {Sym : Type} {G : GStep k Sym} {w : List Bool}
    (cm : ℕ × Mem k Sym) : GReach G w cm cm 0 :=
  ⟨0, le_rfl, rfl⟩

private theorem GReach.of_le {k : ℕ} {Sym : Type} {G : GStep k Sym} {w : List Bool}
    {cm₁ cm₂ : ℕ × Mem k Sym} {t₁ t₂ : ℕ}
    (h : GReach G w cm₁ cm₂ t₁) (hle : t₁ ≤ t₂) :
    GReach G w cm₁ cm₂ t₂ :=
  let ⟨s, hs, hst⟩ := h
  ⟨s, hs.trans hle, hst⟩

private theorem GReach.one {k : ℕ} {Sym : Type} {G : GStep k Sym} {w : List Bool}
    {cm₁ cm₂ : ℕ × Mem k Sym} (h1 : gStepOne G w cm₁ = some cm₂) :
    GReach G w cm₁ cm₂ 1 :=
  ⟨1, le_rfl, by simp [gStepN, h1]⟩

private theorem GReach.trans {k : ℕ} {Sym : Type} {G : GStep k Sym} {w : List Bool}
    {cm₀ cm₁ cm₂ : ℕ × Mem k Sym} {t₁ t₂ : ℕ}
    (h1 : GReach G w cm₀ cm₁ t₁) (h2 : GReach G w cm₁ cm₂ t₂) :
    GReach G w cm₀ cm₂ (t₁ + t₂) := by
  obtain ⟨s₁, hs₁, hst₁⟩ := h1
  obtain ⟨s₂, hs₂, hst₂⟩ := h2
  refine ⟨s₁ + s₂, by omega, ?_⟩
  rw [gStepN_add, hst₁]
  exact hst₂

private structure Block (k : ℕ) (Sym : Type) where
  n : ℕ
  hn : 1 ≤ n
  step : ℕ → Option Bool → (Fin k → Sym) →
    (ℕ × Transpose.Dir × (Fin k → Sym × Transpose.Dir) × Option Bool)
  next_le : ∀ s < n, ∀ inp sc, (step s inp sc).1 ≤ n

private def Embeds {k : ℕ} {Sym : Type} (B : Block k Sym) (G : GStep k Sym) (f : ℕ → ℕ) : Prop :=
  ∀ s < B.n, ∀ inp sc,
    let res := B.step s inp sc
    G (f s) inp sc = some (f res.1, res.2)

private def Runs {k : ℕ} {Sym : Type} (B : Block k Sym) (w : List Bool)
    (m₀ m₁ : Mem k Sym) (t : ℕ) : Prop :=
  ∀ (G : GStep k Sym) (f : ℕ → ℕ), Embeds B G f →
    GReach G w (f 0, m₀) (f B.n, m₁) t

private theorem Runs.of_le {k : ℕ} {Sym : Type} {B : Block k Sym} {w : List Bool}
    {m₀ m₁ : Mem k Sym} {t₁ t₂ : ℕ}
    (h : Runs B w m₀ m₁ t₁) (hle : t₁ ≤ t₂) :
    Runs B w m₀ m₁ t₂ :=
  fun G f hEmb => (h G f hEmb).of_le hle

private def Block.act {k : ℕ} {Sym : Type} (a : Action k Sym) : Block k Sym where
  n := 1
  hn := le_rfl
  step := fun _ inp sc => (1, a inp sc)
  next_le := fun _ _ _ _ => le_rfl

private theorem Runs.act {k : ℕ} {Sym : Type} {w : List Bool}
    (a : Action k Sym) (m : Mem k Sym) :
    Runs (Block.act a) w m (applyAct w a m) 1 := by
  intro G f hEmb
  apply GReach.one
  have h0 := hEmb 0 (Nat.zero_lt_one) (Transpose.readInput w m.inPos) (fun i => m.work i (m.workPos i))
  dsimp only [Block.act] at h0
  unfold gStepOne applyAct
  dsimp only [Block.act]
  rw [h0]

private def Block.seq {k : ℕ} {Sym : Type} (P Q : Block k Sym) : Block k Sym where
  n := P.n + Q.n
  hn := by have := P.hn; omega
  step := fun s inp sc =>
    if s < P.n then P.step s inp sc
    else
      let res := Q.step (s - P.n) inp sc
      (P.n + res.1, res.2)
  next_le := by
    intro s hs inp sc
    by_cases hlt : s < P.n
    · rw [ite_eq_left hlt]
      have := P.next_le s hlt inp sc
      omega
    · rw [ite_eq_right hlt]
      have hQ := Q.next_le (s - P.n) (by omega) inp sc
      dsimp only
      omega

private theorem Runs.seq {k : ℕ} {Sym : Type} {P Q : Block k Sym} {w : List Bool}
    {m₀ m₁ m₂ : Mem k Sym} {t₁ t₂ : ℕ}
    (hP : Runs P w m₀ m₁ t₁) (hQ : Runs Q w m₁ m₂ t₂) :
    Runs (P.seq Q) w m₀ m₂ (t₁ + t₂) := by
  intro G f hEmb
  have hEmbP : Embeds P G f := by
    intro s hs inp sc
    have hsPQ : s < (P.seq Q).n := by dsimp [Block.seq]; omega
    have h := hEmb s hsPQ inp sc
    simpa only [Block.seq, ite_eq_left hs] using h
  have hEmbQ : Embeds Q G (fun s => f (P.n + s)) := by
    intro s hs inp sc
    have hsPQ : P.n + s < (P.seq Q).n := by dsimp [Block.seq]; omega
    have h := hEmb (P.n + s) hsPQ inp sc
    have hnot : ¬ (P.n + s < P.n) := by omega
    simpa only [Block.seq, ite_eq_right hnot, Nat.add_sub_cancel_left] using h
  exact (hP G f hEmbP).trans (hQ G (fun s => f (P.n + s)) hEmbQ)

private def Block.while1 {k : ℕ} {Sym : Type}
    (cond : Option Bool → (Fin k → Sym) → Bool)
    (bodyAct exitAct : Action k Sym) : Block k Sym where
  n := 1
  hn := le_rfl
  step := fun _ inp sc =>
    if cond inp sc then (0, bodyAct inp sc)
    else (1, exitAct inp sc)
  next_le := by
    intro _ _ inp sc
    by_cases hc : cond inp sc = true
    · rw [ite_eq_left hc]; exact Nat.zero_le 1
    · rw [ite_eq_right hc]

private theorem Runs.while1 {k : ℕ} {Sym : Type} {w : List Bool}
    (cond : Option Bool → (Fin k → Sym) → Bool)
    (bodyAct exitAct : Action k Sym) :
    ∀ (N : ℕ) (inv : ℕ → Mem k Sym),
      (∀ i < N,
        cond (Transpose.readInput w (inv i).inPos)
          (fun t => (inv i).work t ((inv i).workPos t)) = true ∧
        applyAct w bodyAct (inv i) = inv (i + 1)) →
      cond (Transpose.readInput w (inv N).inPos)
        (fun t => (inv N).work t ((inv N).workPos t)) = false →
      Runs (Block.while1 cond bodyAct exitAct) w (inv 0) (applyAct w exitAct (inv N)) (N + 1)
  | 0, inv, _, hExit => by
    intro G f hEmb
    apply GReach.one
    have h0 := hEmb 0 Nat.zero_lt_one (Transpose.readInput w (inv 0).inPos)
      (fun t => (inv 0).work t ((inv 0).workPos t))
    have hnot : ¬ (cond (Transpose.readInput w (inv 0).inPos)
        (fun t => (inv 0).work t ((inv 0).workPos t)) = true) := by
      rw [hExit]; decide
    dsimp only [Block.while1] at h0
    rw [ite_eq_right hnot] at h0
    unfold gStepOne applyAct
    dsimp only [Block.while1]
    rw [h0]
  | N + 1, inv, hStep, hExit => by
    intro G f hEmb
    obtain ⟨hCond0, hNext0⟩ := hStep 0 (Nat.zero_lt_succ N)
    have h1 : gStepOne G w (f 0, inv 0) = some (f 0, inv 1) := by
      have h0 := hEmb 0 Nat.zero_lt_one (Transpose.readInput w (inv 0).inPos)
        (fun t => (inv 0).work t ((inv 0).workPos t))
      dsimp only [Block.while1] at h0
      rw [ite_eq_left hCond0] at h0
      unfold gStepOne
      dsimp only
      rw [h0, ← hNext0]
      rfl
    have hRest := Runs.while1 cond bodyAct exitAct N (fun i => inv (i + 1))
      (fun i hi => hStep (i + 1) (Nat.add_lt_add_right hi 1))
      hExit G f hEmb
    simpa only [Nat.add_comm 1 (N + 1)] using (GReach.one h1).trans hRest

private def Block.loop {k : ℕ} {Sym : Type}
    (cond : Option Bool → (Fin k → Sym) → Bool)
    (enterAct exitAct : Action k Sym)
    (B : Block k Sym) : Block k Sym where
  n := 1 + B.n
  hn := by omega
  step := fun s inp sc =>
    if s = 0 then
      if cond inp sc then (1, enterAct inp sc)
      else (1 + B.n, exitAct inp sc)
    else
      let res := B.step (s - 1) inp sc
      (if res.1 = B.n then 0 else 1 + res.1, res.2)
  next_le := by
    intro s hs inp sc
    have hBn := B.hn
    by_cases hs0 : s = 0
    · rw [ite_eq_left hs0]
      by_cases hc : cond inp sc = true
      · rw [ite_eq_left hc]; omega
      · rw [ite_eq_right hc]
    · rw [ite_eq_right hs0]
      have hnx := B.next_le (s - 1) (by omega) inp sc
      dsimp only
      split_ifs <;> omega

private theorem Runs.loop {k : ℕ} {Sym : Type} {w : List Bool}
    (cond : Option Bool → (Fin k → Sym) → Bool)
    (enterAct exitAct : Action k Sym)
    (B : Block k Sym) (tBody : ℕ) :
    ∀ (N : ℕ) (inv : ℕ → Mem k Sym),
      (∀ i < N,
        cond (Transpose.readInput w (inv i).inPos)
          (fun t => (inv i).work t ((inv i).workPos t)) = true ∧
        Runs B w (applyAct w enterAct (inv i)) (inv (i + 1)) tBody) →
      cond (Transpose.readInput w (inv N).inPos)
        (fun t => (inv N).work t ((inv N).workPos t)) = false →
      Runs (Block.loop cond enterAct exitAct B) w
        (inv 0) (applyAct w exitAct (inv N)) (N * (1 + tBody) + 1)
  | 0, inv, _, hExit => by
    intro G f hEmb
    have h0lt : 0 < (Block.loop cond enterAct exitAct B).n := by dsimp [Block.loop]; omega
    have h0 := hEmb 0 h0lt (Transpose.readInput w (inv 0).inPos)
      (fun t => (inv 0).work t ((inv 0).workPos t))
    have hnot : ¬ (cond (Transpose.readInput w (inv 0).inPos)
        (fun t => (inv 0).work t ((inv 0).workPos t)) = true) := by
      rw [hExit]; decide
    dsimp only [Block.loop] at h0
    rw [ite_eq_left rfl, ite_eq_right hnot] at h0
    have h1 : gStepOne G w (f 0, inv 0) = some (f (1 + B.n), applyAct w exitAct (inv 0)) := by
      unfold gStepOne applyAct
      dsimp only
      rw [h0]
    simpa [Block.loop] using GReach.one h1
  | N + 1, inv, hStep, hExit => by
    intro G f hEmb
    obtain ⟨hCond0, hBody0⟩ := hStep 0 (Nat.zero_lt_succ N)
    have hBn := B.hn
    have h0lt : 0 < (Block.loop cond enterAct exitAct B).n := by dsimp [Block.loop]; omega
    have hEnter : gStepOne G w (f 0, inv 0) = some (f 1, applyAct w enterAct (inv 0)) := by
      have h0 := hEmb 0 h0lt (Transpose.readInput w (inv 0).inPos)
        (fun t => (inv 0).work t ((inv 0).workPos t))
      dsimp only [Block.loop] at h0
      rw [ite_eq_left rfl, ite_eq_left hCond0] at h0
      unfold gStepOne applyAct
      dsimp only
      rw [h0]
    let g : ℕ → ℕ := fun s => if s = B.n then f 0 else f (1 + s)
    have hEmbB : Embeds B G g := by
      intro s hs inp sc
      have hs1 : 1 + s < (Block.loop cond enterAct exitAct B).n := by dsimp [Block.loop]; omega
      have h := hEmb (1 + s) hs1 inp sc
      have hne0 : 1 + s ≠ 0 := by omega
      have hsne : s ≠ B.n := by omega
      dsimp only [Block.loop] at h
      rw [ite_eq_right hne0, Nat.add_sub_cancel_left] at h
      dsimp only [g]
      rw [ite_eq_right hsne]
      rw [h]
      congr 1
      split_ifs <;> rfl
    have hB0 : GReach G w (f 1, applyAct w enterAct (inv 0)) (f 0, inv 1) tBody := by
      have hg0 : g 0 = f 1 := by dsimp [g]; rw [ite_eq_right (by omega)]
      have hgN : g B.n = f 0 := by dsimp [g]; rw [ite_eq_left rfl]
      rw [← hg0, ← hgN]
      exact hBody0 G g hEmbB
    have hIter0 : GReach G w (f 0, inv 0) (f 0, inv 1) (1 + tBody) :=
      (GReach.one hEnter).trans hB0
    have hRest := Runs.loop cond enterAct exitAct B tBody N (fun i => inv (i + 1))
      (fun i hi => hStep (i + 1) (Nat.add_lt_add_right hi 1))
      hExit G f hEmb
    have hTime : (1 + tBody) + (N * (1 + tBody) + 1) = (N + 1) * (1 + tBody) + 1 := by ring
    rw [← hTime]
    exact hIter0.trans hRest

private def natSum : ℕ → (ℕ → ℕ) → ℕ
  | 0, _ => 0
  | n + 1, f => f 0 + natSum n (fun i => f (i + 1))

private theorem Runs.loop_sum {k : ℕ} {Sym : Type} {w : List Bool}
    (cond : Option Bool → (Fin k → Sym) → Bool)
    (enterAct exitAct : Action k Sym)
    (B : Block k Sym) :
    ∀ (N : ℕ) (tBody : ℕ → ℕ) (inv : ℕ → Mem k Sym),
      (∀ i < N,
        cond (Transpose.readInput w (inv i).inPos)
          (fun t => (inv i).work t ((inv i).workPos t)) = true ∧
        Runs B w (applyAct w enterAct (inv i)) (inv (i + 1)) (tBody i)) →
      cond (Transpose.readInput w (inv N).inPos)
        (fun t => (inv N).work t ((inv N).workPos t)) = false →
      Runs (Block.loop cond enterAct exitAct B) w
        (inv 0) (applyAct w exitAct (inv N)) (natSum N (fun i => 1 + tBody i) + 1)
  | 0, _, inv, _, hExit => by
    simpa [natSum] using Runs.loop cond enterAct exitAct B 0 0 inv
      (fun _ h => absurd h (Nat.not_lt_zero _)) hExit
  | N + 1, tBody, inv, hStep, hExit => by
    intro G f hEmb
    obtain ⟨hCond0, hBody0⟩ := hStep 0 (Nat.zero_lt_succ N)
    have h0lt : 0 < (Block.loop cond enterAct exitAct B).n := by dsimp [Block.loop]; omega
    have hEnter : gStepOne G w (f 0, inv 0) = some (f 1, applyAct w enterAct (inv 0)) := by
      have h0 := hEmb 0 h0lt (Transpose.readInput w (inv 0).inPos)
        (fun t => (inv 0).work t ((inv 0).workPos t))
      dsimp only [Block.loop] at h0
      rw [ite_eq_left rfl, ite_eq_left hCond0] at h0
      unfold gStepOne applyAct; dsimp only; rw [h0]
    let g : ℕ → ℕ := fun s => if s = B.n then f 0 else f (1 + s)
    have hEmbB : Embeds B G g := by
      intro s hs inp sc
      have hs1 : 1 + s < (Block.loop cond enterAct exitAct B).n := by dsimp [Block.loop]; omega
      have h := hEmb (1 + s) hs1 inp sc
      have hne0 : 1 + s ≠ 0 := by omega
      have hsne : s ≠ B.n := by omega
      dsimp only [Block.loop] at h
      rw [ite_eq_right hne0, Nat.add_sub_cancel_left] at h
      dsimp only [g]; rw [ite_eq_right hsne, h]
      congr 1; split_ifs <;> rfl
    have hB0 : GReach G w (f 1, applyAct w enterAct (inv 0)) (f 0, inv 1) (tBody 0) := by
      have hg0 : g 0 = f 1 := by dsimp [g]; rw [ite_eq_right (by have := B.hn; omega)]
      have hgN : g B.n = f 0 := by dsimp [g]; rw [ite_eq_left rfl]
      rw [← hg0, ← hgN]
      exact hBody0 G g hEmbB
    have hIter0 : GReach G w (f 0, inv 0) (f 0, inv 1) (1 + tBody 0) :=
      (GReach.one hEnter).trans hB0
    have hRest := Runs.loop_sum cond enterAct exitAct B N (fun i => tBody (i + 1))
      (fun i => inv (i + 1))
      (fun i hi => hStep (i + 1) (Nat.add_lt_add_right hi 1))
      hExit G f hEmb
    simpa only [natSum, Nat.add_assoc] using hIter0.trans hRest

private def Block.branch {k : ℕ} {Sym : Type}
    (cond : Option Bool → (Fin k → Sym) → Bool)
    (trueAct falseAct : Action k Sym)
    (T F : Block k Sym) : Block k Sym where
  n := 1 + T.n + F.n
  hn := by omega
  step := fun s inp sc =>
    if s = 0 then
      if cond inp sc then (1, trueAct inp sc)
      else (1 + T.n, falseAct inp sc)
    else if s < 1 + T.n then
      let res := T.step (s - 1) inp sc
      (if res.1 = T.n then 1 + T.n + F.n else 1 + res.1, res.2)
    else
      let res := F.step (s - (1 + T.n)) inp sc
      (1 + T.n + res.1, res.2)
  next_le := by
    intro s hs inp sc
    have hTn := T.hn; have hFn := F.hn
    by_cases hs0 : s = 0
    · rw [ite_eq_left hs0]
      by_cases hc : cond inp sc = true
      · rw [ite_eq_left hc]; dsimp only; omega
      · rw [ite_eq_right hc]; dsimp only; omega
    · rw [ite_eq_right hs0]
      by_cases hltT : s < 1 + T.n
      · rw [ite_eq_left hltT]
        have hnx := T.next_le (s - 1) (by omega) inp sc
        dsimp only; split_ifs <;> omega
      · rw [ite_eq_right hltT]
        have hnx := F.next_le (s - (1 + T.n)) (by omega) inp sc
        dsimp only; omega

private theorem Runs.branch_true {k : ℕ} {Sym : Type} {w : List Bool}
    {cond : Option Bool → (Fin k → Sym) → Bool}
    {trueAct falseAct : Action k Sym} {T F : Block k Sym}
    {m₀ m₂ : Mem k Sym} {t : ℕ}
    (hCond : cond (Transpose.readInput w m₀.inPos) (fun i => m₀.work i (m₀.workPos i)) = true)
    (hT : Runs T w (applyAct w trueAct m₀) m₂ t) :
    Runs (Block.branch cond trueAct falseAct T F) w m₀ m₂ (1 + t) := by
  intro G f hEmb
  have hTn := T.hn; have hFn := F.hn
  have h0lt : 0 < (Block.branch cond trueAct falseAct T F).n := by dsimp [Block.branch]; omega
  have hEnter : gStepOne G w (f 0, m₀) = some (f 1, applyAct w trueAct m₀) := by
    have h0 := hEmb 0 h0lt (Transpose.readInput w m₀.inPos) (fun i => m₀.work i (m₀.workPos i))
    dsimp only [Block.branch] at h0
    rw [ite_eq_left rfl, ite_eq_left hCond] at h0
    unfold gStepOne applyAct; dsimp only; rw [h0]
  let g : ℕ → ℕ := fun s => if s = T.n then f (1 + T.n + F.n) else f (1 + s)
  have hEmbT : Embeds T G g := by
    intro s hs inp sc
    have hsB : 1 + s < (Block.branch cond trueAct falseAct T F).n := by dsimp [Block.branch]; omega
    have h := hEmb (1 + s) hsB inp sc
    have hne0 : 1 + s ≠ 0 := by omega
    have hltT : 1 + s < 1 + T.n := by omega
    have hsne : s ≠ T.n := by omega
    dsimp only [Block.branch] at h
    rw [ite_eq_right hne0, ite_eq_left hltT, Nat.add_sub_cancel_left] at h
    dsimp only [g]; rw [ite_eq_right hsne, h]
    congr 1; split_ifs <;> rfl
  have hRunT : GReach G w (f 1, applyAct w trueAct m₀) (f (1 + T.n + F.n), m₂) t := by
    have hg0 : g 0 = f 1 := by dsimp [g]; rw [ite_eq_right (by omega)]
    have hgN : g T.n = f (1 + T.n + F.n) := by dsimp [g]; rw [ite_eq_left rfl]
    rw [← hg0, ← hgN]
    exact hT G g hEmbT
  exact (GReach.one hEnter).trans hRunT

private theorem Runs.branch_false {k : ℕ} {Sym : Type} {w : List Bool}
    {cond : Option Bool → (Fin k → Sym) → Bool}
    {trueAct falseAct : Action k Sym} {T F : Block k Sym}
    {m₀ m₂ : Mem k Sym} {t : ℕ}
    (hCond : cond (Transpose.readInput w m₀.inPos) (fun i => m₀.work i (m₀.workPos i)) = false)
    (hF : Runs F w (applyAct w falseAct m₀) m₂ t) :
    Runs (Block.branch cond trueAct falseAct T F) w m₀ m₂ (1 + t) := by
  intro G f hEmb
  have hTn := T.hn; have hFn := F.hn
  have h0lt : 0 < (Block.branch cond trueAct falseAct T F).n := by dsimp [Block.branch]; omega
  have hEnter : gStepOne G w (f 0, m₀) = some (f (1 + T.n), applyAct w falseAct m₀) := by
    have h0 := hEmb 0 h0lt (Transpose.readInput w m₀.inPos) (fun i => m₀.work i (m₀.workPos i))
    have hnot : ¬ (cond (Transpose.readInput w m₀.inPos) (fun i => m₀.work i (m₀.workPos i)) = true) := by
      rw [hCond]; decide
    dsimp only [Block.branch] at h0
    rw [ite_eq_left rfl, ite_eq_right hnot] at h0
    unfold gStepOne applyAct; dsimp only; rw [h0]
  let g : ℕ → ℕ := fun s => f (1 + T.n + s)
  have hEmbF : Embeds F G g := by
    intro s hs inp sc
    have hsB : 1 + T.n + s < (Block.branch cond trueAct falseAct T F).n := by
      dsimp [Block.branch]; omega
    have h := hEmb (1 + T.n + s) hsB inp sc
    have hne0 : 1 + T.n + s ≠ 0 := by omega
    have hnltT : ¬ (1 + T.n + s < 1 + T.n) := by omega
    dsimp only [Block.branch] at h
    rw [ite_eq_right hne0, ite_eq_right hnltT, Nat.add_sub_cancel_left] at h
    exact h
  exact (GReach.one hEnter).trans (hF G g hEmbF)

private def Block.toTM {k g : ℕ} {Sym : Type}
    (encSym : Sym → Fin (g + 1)) (decSym : Fin (g + 1) → Sym)
    (B : Block k Sym) : Transpose.TM where
  k := k
  g := g
  q := B.n
  δ := fun s inp sc =>
    if hs : s.val < B.n then
      let res := B.step s.val inp (fun i => decSym (sc i))
      have hnx : res.1 < B.n + 1 := Nat.lt_succ_of_le (B.next_le s.val hs inp _)
      some (⟨res.1, hnx⟩, res.2.1, fun i => (encSym (res.2.2.1 i).1, (res.2.2.1 i).2), res.2.2.2)
    else
      none

private theorem Block.computesWithin {k g : ℕ} {Sym : Type}
    (blank : Sym)
    (encSym : Sym → Fin (g + 1)) (decSym : Fin (g + 1) → Sym)
    (hSym : ∀ a, decSym (encSym a) = a)
    (hBlank : encSym blank = 0)
    (B : Block k Sym)
    {w out : List Bool} {mHalt : Mem k Sym} {t : ℕ}
    (hRun : Runs B w
      { inPos := 0, work := fun _ _ => blank, workPos := fun _ => 0, outRev := [] }
      mHalt t)
    (hOut : mHalt.outRev.reverse = out) :
    Transpose.ComputesWithin (B.toTM encSym decSym) w out t := by
  let G : GStep k Sym := fun s inp sc =>
    if s < B.n then some (B.step s inp sc) else none
  have hEmb : Embeds B G id := by
    intro s hs inp sc
    dsimp only [G, id]
    rw [ite_eq_left hs]
  let m0 : Mem k Sym :=
    { inPos := 0, work := fun _ _ => blank, workPos := fun _ => 0, outRev := [] }
  obtain ⟨steps, hsteps_le, hGstepN⟩ := hRun G id hEmb
  let toCfg (s : ℕ) (hs : s < B.n + 1) (m : Mem k Sym) :
      Transpose.Config (B.toTM encSym decSym) :=
    { state   := ⟨s, hs⟩
      inPos   := m.inPos
      work    := fun i p => encSym (m.work i p)
      workPos := m.workPos
      outRev  := m.outRev }
  have hOne : ∀ (s : ℕ) (hs : s < B.n + 1) (m : Mem k Sym) (s' : ℕ) (m' : Mem k Sym),
      gStepOne G w (s, m) = some (s', m') →
      ∃ hs' : s' < B.n + 1,
        Transpose.step (B.toTM encSym decSym) w (toCfg s hs m) = some (toCfg s' hs' m') := by
    intro s hs m s' m' h1
    unfold gStepOne G at h1
    dsimp only at h1
    by_cases hsB : s < B.n
    · rw [ite_eq_left hsB] at h1
      simp only [Option.some.injEq, Prod.mk.injEq] at h1
      rcases h1 with ⟨rfl, rfl⟩
      have hnx : (B.step s (Transpose.readInput w m.inPos) (fun i => m.work i (m.workPos i))).1 <
          B.n + 1 :=
        Nat.lt_succ_of_le (B.next_le s hsB _ _)
      refine ⟨hnx, ?_⟩
      unfold Transpose.step toCfg Block.toTM
      dsimp only
      rw [dite_eq_left hsB]
      have hsc : (fun i => decSym (encSym (m.work i (m.workPos i)))) =
          (fun i => m.work i (m.workPos i)) := by
        funext i; exact hSym _
      dsimp only
      congr 1
      rw [Transpose.Config.mk.injEq]
      refine ⟨Fin.ext (by dsimp only; rw [hsc]), ?_, ?_, ?_, ?_⟩
      · rw [hsc]
      · funext i p
        rw [hsc]
        split_ifs <;> rfl
      · funext i
        rw [hsc]
      · rw [hsc]; rfl
    · rw [ite_eq_right hsB] at h1
      cases h1
  have hMany : ∀ (n : ℕ) (s : ℕ) (hs : s < B.n + 1) (m : Mem k Sym) (s' : ℕ) (m' : Mem k Sym),
      gStepN G w n (s, m) = some (s', m') →
      ∃ hs' : s' < B.n + 1,
        Transpose.stepN (B.toTM encSym decSym) w n (toCfg s hs m) = some (toCfg s' hs' m') := by
    intro n
    induction n with
    | zero =>
      intro s hs m s' m' h0
      simp only [gStepN, Option.some.injEq, Prod.mk.injEq] at h0
      rcases h0 with ⟨rfl, rfl⟩
      exact ⟨hs, rfl⟩
    | succ n ih =>
      intro s hs m s' m' hsn
      simp only [gStepN] at hsn
      cases hg1 : gStepOne G w (s, m) with
      | none => rw [hg1] at hsn; cases hsn
      | some cm1 =>
        rw [hg1] at hsn
        rcases cm1 with ⟨s1, m1⟩
        obtain ⟨hs1, htm1⟩ := hOne s hs m s1 m1 hg1
        obtain ⟨hs', htmN⟩ := ih s1 hs1 m1 s' m' hsn
        refine ⟨hs', ?_⟩
        simp only [Transpose.stepN, htm1, htmN]
  have h0lt : 0 < B.n + 1 := Nat.zero_lt_succ B.n
  obtain ⟨hNlt, hStepNM⟩ := hMany steps 0 h0lt m0 B.n mHalt hGstepN
  have hInitEq : toCfg 0 h0lt m0 = Transpose.init (B.toTM encSym decSym) := by
    unfold toCfg m0 Transpose.init Block.toTM
    dsimp only
    rw [Transpose.Config.mk.injEq]
    refine ⟨rfl, rfl, ?_, rfl, rfl⟩
    funext i p; exact hBlank
  have hHaltEq : Transpose.step (B.toTM encSym decSym) w (toCfg B.n hNlt mHalt) = none := by
    unfold Transpose.step toCfg Block.toTM
    dsimp only
    have hnot : ¬ (B.n < B.n) := lt_irrefl _
    rw [dite_eq_right hnot]
  refine ⟨steps, hsteps_le, toCfg B.n hNlt mHalt, ?_, hHaltEq, hOut⟩
  rw [← hInitEq]
  exact hStepNM

private theorem natSum_le_of_step :
    ∀ {N : ℕ} {f g : ℕ → ℕ},
      (∀ i < N, f i + g i ≤ g (i + 1)) →
      natSum N f + g 0 ≤ g N
  | 0, _, _, _ => by simp [natSum]
  | N + 1, f, g, hstep => by
    have h0 := hstep 0 (Nat.zero_lt_succ N)
    have hrest := natSum_le_of_step (N := N) (f := fun i => f (i + 1)) (g := fun i => g (i + 1))
      (fun i hi => hstep (i + 1) (Nat.add_lt_add_right hi 1))
    dsimp only [natSum]
    omega

/-! ### 3. Work Alphabet, Generic Tape Primitives & `discoverEntryBits` -/

private inductive WorkSym where
  | blank
  | b0
  | b1
  | u
  | wall
  | oddD
  | oddAux
  | save
  | emitStart
  | emitCont
  deriving DecidableEq, Repr

private def encWorkSym : WorkSym → Fin 10
  | .blank     => 0
  | .b0        => 1
  | .b1        => 2
  | .u         => 3
  | .wall      => 4
  | .oddD      => 5
  | .oddAux    => 6
  | .save      => 7
  | .emitStart => 8
  | .emitCont  => 9

private def decWorkSym : Fin 10 → WorkSym
  | ⟨0, _⟩ => .blank
  | ⟨1, _⟩ => .b0
  | ⟨2, _⟩ => .b1
  | ⟨3, _⟩ => .u
  | ⟨4, _⟩ => .wall
  | ⟨5, _⟩ => .oddD
  | ⟨6, _⟩ => .oddAux
  | ⟨7, _⟩ => .save
  | ⟨8, _⟩ => .emitStart
  | ⟨9, _⟩ => .emitCont

private theorem decWorkSym_encWorkSym (a : WorkSym) : decWorkSym (encWorkSym a) = a := by
  cases a <;> rfl

private theorem encWorkSym_blank : encWorkSym .blank = 0 := rfl

private def bitSym : Bool → WorkSym
  | false => .b0
  | true  => .b1

private def symBit : WorkSym → Option Bool
  | .b0 => some false
  | .b1 => some true
  | _   => none

private theorem symBit_bitSym (b : Bool) : symBit (bitSym b) = some b := by
  cases b <;> rfl

private theorem bitSym_ne_blank (b : Bool) : bitSym b ≠ .blank := by
  cases b <;> decide

private def unaryTape (N : ℕ) : Int → WorkSym :=
  fun p => if 0 ≤ p ∧ p < (N : Int) then .u else .blank

private theorem unaryTape_zero : unaryTape 0 = fun _ => .blank := by
  funext p
  unfold unaryTape
  split_ifs with h <;> first | rfl | omega

private theorem unaryTape_lt {N i : ℕ} (hi : i < N) : unaryTape N (i : Int) = .u := by
  unfold unaryTape
  have h : 0 ≤ (i : Int) ∧ (i : Int) < (N : Int) := by omega
  rw [ite_eq_left h]

private theorem unaryTape_ge {N : ℕ} {p : Int} (hp : (N : Int) ≤ p) : unaryTape N p = .blank := by
  unfold unaryTape
  have h : ¬ (0 ≤ p ∧ p < (N : Int)) := by omega
  rw [ite_eq_right h]

private theorem unaryTape_neg {N : ℕ} {p : Int} (hp : p < 0) : unaryTape N p = .blank := by
  unfold unaryTape
  have h : ¬ (0 ≤ p ∧ p < (N : Int)) := by omega
  rw [ite_eq_right h]

private theorem unaryTape_write_end (N : ℕ) :
    (fun p : Int => if p = (N : Int) then WorkSym.u else unaryTape N p) = unaryTape (N + 1) := by
  funext p
  unfold unaryTape
  by_cases hp : p = (N : Int)
  · subst hp
    have h2 : 0 ≤ (N : Int) ∧ (N : Int) < ((N + 1 : ℕ) : Int) := by omega
    simp [h2]
  · rw [ite_eq_right hp]
    by_cases h1 : 0 ≤ p ∧ p < (N : Int)
    · have h2 : 0 ≤ p ∧ p < ((N + 1 : ℕ) : Int) := by omega
      rw [ite_eq_left h1, ite_eq_left h2]
    · have h2 : ¬ (0 ≤ p ∧ p < ((N + 1 : ℕ) : Int)) := by omega
      rw [ite_eq_right h1, ite_eq_right h2]

private def wordTape (xs : List Bool) : Int → WorkSym :=
  fun p =>
    if 0 ≤ p then
      match xs[p.toNat]? with
      | some b => bitSym b
      | none   => .blank
    else .blank

private theorem wordTape_nil : wordTape [] = fun _ => .blank := by
  funext p; unfold wordTape; split_ifs <;> simp

private theorem wordTape_lt {xs : List Bool} {i : ℕ} {b : Bool} (hb : xs[i]? = some b) :
    wordTape xs (i : Int) = bitSym b := by
  unfold wordTape
  have h0 : 0 ≤ (i : Int) := by omega
  rw [ite_eq_left h0, Int.toNat_natCast, hb]

private theorem wordTape_ge {xs : List Bool} {p : Int} (hp : (xs.length : Int) ≤ p) :
    wordTape xs p = .blank := by
  unfold wordTape
  by_cases h0 : 0 ≤ p
  · rw [ite_eq_left h0]
    have hge : xs.length ≤ p.toNat := by omega
    rw [List.getElem?_eq_none hge]
  · rw [ite_eq_right h0]

private theorem wordTape_neg {xs : List Bool} {p : Int} (hp : p < 0) :
    wordTape xs p = .blank := by
  unfold wordTape
  rw [ite_eq_right (by omega)]

private theorem wordTape_take_succ {xs : List Bool} {i : ℕ} {b : Bool} (hb : xs[i]? = some b) :
    (fun p : Int => if p = (i : Int) then bitSym b else wordTape (xs.take i) p) =
      wordTape (xs.take (i + 1)) := by
  have hi_lt : i < xs.length := by
    by_contra hge
    rw [List.getElem?_eq_none (Nat.le_of_not_gt hge)] at hb
    cases hb
  funext p
  by_cases hp : p = (i : Int)
  · subst hp
    rw [ite_eq_left rfl]
    have hget : (xs.take (i + 1))[i]? = some b := by
      rw [List.getElem?_take_of_lt (Nat.lt_succ_self i), hb]
    exact (wordTape_lt hget).symm
  · rw [ite_eq_right hp]
    unfold wordTape
    by_cases h0 : 0 ≤ p
    · rw [ite_eq_left h0, ite_eq_left h0]
      by_cases hpi : p.toNat < i
      · rw [List.getElem?_take_of_lt hpi, List.getElem?_take_of_lt (Nat.lt_succ_of_lt hpi)]
      · have hpge : i + 1 ≤ p.toNat := by omega
        have hlen1 : (xs.take i).length ≤ p.toNat := by simp; omega
        have hlen2 : (xs.take (i + 1)).length ≤ p.toNat := by simp; omega
        rw [List.getElem?_eq_none hlen1, List.getElem?_eq_none hlen2]
    · rw [ite_eq_right h0, ite_eq_right h0]

private theorem bne_blank_of_ne {a : WorkSym} (h : a ≠ .blank) : (a != .blank) = true := by
  cases a <;> first | exact absurd rfl h | rfl

private def actStay {k : ℕ} : Action k WorkSym :=
  fun _ sc => (.stay, fun i => (sc i, .stay), none)

private theorem applyAct_actStay {k : ℕ} (w : List Bool) (m : Mem k WorkSym) :
    applyAct w actStay m = m := by
  unfold applyAct actStay
  refine Mem.eq_of_fields rfl (fun i p => ?_) (fun _ => rfl) rfl
  dsimp only
  by_cases hp : p = m.workPos i
  · subst hp; simp
  · rw [ite_eq_right hp]

private def mkAct1 {k : ℕ} (t₀ : Fin k)
    (inDir : Option Bool → WorkSym → Transpose.Dir)
    (wAct : Option Bool → WorkSym → WorkSym × Transpose.Dir)
    (outBit : Option Bool → WorkSym → Option Bool) : Action k WorkSym :=
  fun inp sc =>
    (inDir inp (sc t₀),
     fun i => if i = t₀ then wAct inp (sc t₀) else (sc i, .stay),
     outBit inp (sc t₀))

private theorem applyAct_mkAct1 {k : ℕ} (w : List Bool) (m : Mem k WorkSym) (t₀ : Fin k)
    (inDir : Option Bool → WorkSym → Transpose.Dir)
    (wAct : Option Bool → WorkSym → WorkSym × Transpose.Dir)
    (outBit : Option Bool → WorkSym → Option Bool) :
    let inp := Transpose.readInput w m.inPos
    let s₀ := m.work t₀ (m.workPos t₀)
    applyAct w (mkAct1 t₀ inDir wAct outBit) m =
      { inPos   := (inDir inp s₀).shift m.inPos
        work    := fun i p =>
          if i = t₀ then (if p = m.workPos t₀ then (wAct inp s₀).1 else m.work t₀ p)
          else m.work i p
        workPos := fun i => if i = t₀ then (wAct inp s₀).2.shift (m.workPos t₀) else m.workPos i
        outRev  := match outBit inp s₀ with | none => m.outRev | some b => b :: m.outRev } := by
  dsimp only
  unfold applyAct mkAct1
  refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
  · dsimp only
    by_cases hi : i = t₀
    · subst hi; simp
    · simp only [hi, ↓reduceIte]
      by_cases hp : p = m.workPos i
      · subst hp; simp
      · rw [ite_eq_right hp]
  · dsimp only
    by_cases hi : i = t₀
    · subst hi; simp
    · simp [hi, Transpose.Dir.shift]

private def mkAct2 {k : ℕ} (t₀ t₁ : Fin k)
    (inDir : Option Bool → WorkSym → WorkSym → Transpose.Dir)
    (wAct₀ wAct₁ : Option Bool → WorkSym → WorkSym → WorkSym × Transpose.Dir)
    (outBit : Option Bool → WorkSym → WorkSym → Option Bool) : Action k WorkSym :=
  fun inp sc =>
    (inDir inp (sc t₀) (sc t₁),
     fun i =>
       if i = t₀ then wAct₀ inp (sc t₀) (sc t₁)
       else if i = t₁ then wAct₁ inp (sc t₀) (sc t₁)
       else (sc i, .stay),
     outBit inp (sc t₀) (sc t₁))

private theorem applyAct_mkAct2 {k : ℕ} (w : List Bool) (m : Mem k WorkSym) {t₀ t₁ : Fin k}
    (hne : t₀ ≠ t₁)
    (inDir : Option Bool → WorkSym → WorkSym → Transpose.Dir)
    (wAct₀ wAct₁ : Option Bool → WorkSym → WorkSym → WorkSym × Transpose.Dir)
    (outBit : Option Bool → WorkSym → WorkSym → Option Bool) :
    let inp := Transpose.readInput w m.inPos
    let s₀ := m.work t₀ (m.workPos t₀)
    let s₁ := m.work t₁ (m.workPos t₁)
    applyAct w (mkAct2 t₀ t₁ inDir wAct₀ wAct₁ outBit) m =
      { inPos   := (inDir inp s₀ s₁).shift m.inPos
        work    := fun i p =>
          if i = t₀ then (if p = m.workPos t₀ then (wAct₀ inp s₀ s₁).1 else m.work t₀ p)
          else if i = t₁ then (if p = m.workPos t₁ then (wAct₁ inp s₀ s₁).1 else m.work t₁ p)
          else m.work i p
        workPos := fun i =>
          if i = t₀ then (wAct₀ inp s₀ s₁).2.shift (m.workPos t₀)
          else if i = t₁ then (wAct₁ inp s₀ s₁).2.shift (m.workPos t₁)
          else m.workPos i
        outRev  := match outBit inp s₀ s₁ with | none => m.outRev | some b => b :: m.outRev } := by
  dsimp only
  unfold applyAct mkAct2
  refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
  · dsimp only
    by_cases hi0 : i = t₀
    · subst hi0; simp
    · by_cases hi1 : i = t₁
      · subst hi1; simp [Ne.symm hne]
      · simp only [hi0, hi1, ↓reduceIte]
        by_cases hp : p = m.workPos i
        · subst hp; simp
        · rw [ite_eq_right hp]
  · dsimp only
    by_cases hi0 : i = t₀
    · subst hi0; simp
    · by_cases hi1 : i = t₁
      · subst hi1; simp [hi0]
      · simp [hi0, hi1, Transpose.Dir.shift]

private theorem ite_self_cell {Sym : Type} (f : Int → Sym) (q : Int) :
    (fun p => if p = q then f q else f p) = f := by
  funext p
  by_cases hp : p = q
  · subst hp; simp
  · rw [ite_eq_right hp]

private def stepDirAct {k : ℕ} (t₀ : Fin k) (d : Transpose.Dir) : Action k WorkSym :=
  mkAct1 t₀ (fun _ _ => .stay) (fun _ s => (s, d)) (fun _ _ => none)

private def writeDirAct {k : ℕ} (t₀ : Fin k) (sym : WorkSym) (d : Transpose.Dir) : Action k WorkSym :=
  mkAct1 t₀ (fun _ _ => .stay) (fun _ _ => (sym, d)) (fun _ _ => none)

private def inStepDirAct {k : ℕ} (d : Transpose.Dir) : Action k WorkSym :=
  fun _ sc => (d, fun i => (sc i, .stay), none)

private theorem applyAct_inStepDir {k : ℕ} (w : List Bool) (m : Mem k WorkSym) (d : Transpose.Dir) :
    applyAct w (inStepDirAct d) m = { m with inPos := d.shift m.inPos } := by
  unfold applyAct inStepDirAct
  refine Mem.eq_of_fields rfl (fun i p => ?_) (fun _ => rfl) rfl
  dsimp only
  by_cases hp : p = m.workPos i
  · subst hp; simp
  · rw [ite_eq_right hp]

/-- Rewind tape `t₀` from `workPos t₀ = N` back to `0` across non-blank `[0, N)` with blank `-1`. -/
private def rewindFromEnd {k : ℕ} (t₀ : Fin k) : Block k WorkSym :=
  (Block.act (stepDirAct t₀ .left)).seq
    (Block.while1 (fun _ sc => sc t₀ != .blank)
      (stepDirAct t₀ .left) (stepDirAct t₀ .right))

private theorem Runs_rewindFromEnd {k : ℕ} {w : List Bool} (t₀ : Fin k)
    (m : Mem k WorkSym) (N : ℕ)
    (hPos : m.workPos t₀ = (N : Int))
    (hNonBlank : ∀ j < N, m.work t₀ (j : Int) ≠ .blank)
    (hNeg1 : m.work t₀ (-1) = .blank) :
    Runs (rewindFromEnd t₀) w m
      { m with workPos := fun i => if i = t₀ then 0 else m.workPos i } (N + 2) := by
  unfold rewindFromEnd
  let mAt (q : Int) : Mem k WorkSym :=
    { m with workPos := fun i => if i = t₀ then q else m.workPos i }
  have hFirst : applyAct w (stepDirAct t₀ .left) m = mAt ((N : Int) - 1) := by
    unfold stepDirAct
    rw [applyAct_mkAct1]
    refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
    · dsimp only [mAt]
      by_cases hi : i = t₀
      · subst hi; simp only [↓reduceIte]; exact congrFun (ite_self_cell (m.work i) (m.workPos i)) p
      · simp [hi]
    · dsimp only [mAt, Transpose.Dir.shift]
      by_cases hi : i = t₀
      · subst hi; simp [hPos]
      · simp [hi]
  have h1 : Runs (Block.act (stepDirAct t₀ .left)) w m (mAt ((N : Int) - 1)) 1 := by
    rw [← hFirst]; exact Runs.act _ m
  let inv (j : ℕ) : Mem k WorkSym := mAt ((N : Int) - 1 - (j : Int))
  have hInv0 : mAt ((N : Int) - 1) = inv 0 := by
    refine Mem.eq_of_fields rfl (fun _ _ => rfl) (fun i => ?_) rfl
    dsimp only [inv, mAt]
    by_cases hi : i = t₀
    · subst hi; simp
    · simp [hi]
  have hLoop := Runs.while1 (w := w)
    (fun _ (sc : Fin k → WorkSym) => sc t₀ != .blank)
    (stepDirAct t₀ .left) (stepDirAct t₀ .right) N inv
    (fun j hj => by
      have hidx : (N : Int) - 1 - (j : Int) = ((N - 1 - j : ℕ) : Int) := by omega
      have hcell : (inv j).work t₀ ((inv j).workPos t₀) ≠ .blank := by
        dsimp only [inv, mAt]; simp only [↓reduceIte]
        rw [hidx]
        exact hNonBlank (N - 1 - j) (by omega)
      refine ⟨bne_blank_of_ne hcell, ?_⟩
      unfold stepDirAct
      rw [applyAct_mkAct1]
      refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
      · dsimp only [inv, mAt]
        by_cases hi : i = t₀
        · subst hi; simp only [↓reduceIte]; exact congrFun (ite_self_cell (m.work i) _) p
        · simp [hi]
      · dsimp only [inv, mAt, Transpose.Dir.shift]
        by_cases hi : i = t₀
        · subst hi; simp only [↓reduceIte]; omega
        · simp [hi])
    (by
      dsimp only [inv, mAt]; simp only [↓reduceIte]
      have hm1 : (N : Int) - 1 - (N : Int) = -1 := by omega
      rw [hm1, hNeg1]; rfl)
  have hExitEq : applyAct w (stepDirAct t₀ .right) (inv N) = mAt 0 := by
    unfold stepDirAct
    rw [applyAct_mkAct1]
    refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
    · dsimp only [inv, mAt]
      by_cases hi : i = t₀
      · subst hi; simp only [↓reduceIte]; exact congrFun (ite_self_cell (m.work i) _) p
      · simp [hi]
    · dsimp only [inv, mAt, Transpose.Dir.shift]
      by_cases hi : i = t₀
      · subst hi; simp only [↓reduceIte]; omega
      · simp [hi]
  rw [← hInv0, hExitEq] at hLoop
  have hTime : 1 + (N + 1) = N + 2 := by omega
  rw [← hTime]
  exact h1.seq hLoop

/-- Erase `[0, N)` on tape `t₀` starting from `workPos t₀ = N` and return head to `0`. -/
private def eraseFromEnd {k : ℕ} (t₀ : Fin k) : Block k WorkSym :=
  (Block.act (stepDirAct t₀ .left)).seq
    (Block.while1 (fun _ sc => sc t₀ != .blank)
      (writeDirAct t₀ .blank .left) (stepDirAct t₀ .right))

private theorem Runs_eraseFromEnd {k : ℕ} {w : List Bool} (t₀ : Fin k)
    (m : Mem k WorkSym) (N : ℕ)
    (hPos : m.workPos t₀ = (N : Int))
    (hNonBlank : ∀ j < N, m.work t₀ (j : Int) ≠ .blank)
    (hOutside : ∀ p : Int, (p < 0 ∨ (N : Int) ≤ p) → m.work t₀ p = .blank) :
    Runs (eraseFromEnd t₀) w m
      { m with
        work    := fun i p => if i = t₀ then .blank else m.work i p
        workPos := fun i => if i = t₀ then 0 else m.workPos i } (N + 2) := by
  unfold eraseFromEnd
  let inv (j : ℕ) : Mem k WorkSym :=
    { m with
      work := fun i p =>
        if i = t₀ then
          if (N : Int) - (j : Int) ≤ p then .blank else m.work t₀ p
        else m.work i p
      workPos := fun i => if i = t₀ then (N : Int) - 1 - (j : Int) else m.workPos i }
  have hFirst : applyAct w (stepDirAct t₀ .left) m = inv 0 := by
    unfold stepDirAct
    rw [applyAct_mkAct1]
    refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
    · dsimp only [inv]
      by_cases hi : i = t₀
      · subst hi
        simp only [↓reduceIte]
        rw [congrFun (ite_self_cell (m.work i) (m.workPos i)) p]
        split_ifs with hge
        · exact hOutside p (Or.inr (by omega))
        · rfl
      · simp [hi]
    · dsimp only [inv, Transpose.Dir.shift]
      by_cases hi : i = t₀
      · subst hi; simp [hPos]
      · simp [hi]
  have h1 : Runs (Block.act (stepDirAct t₀ .left)) w m (inv 0) 1 := by
    rw [← hFirst]; exact Runs.act _ m
  have hLoop := Runs.while1 (w := w)
    (fun _ (sc : Fin k → WorkSym) => sc t₀ != .blank)
    (writeDirAct t₀ .blank .left) (stepDirAct t₀ .right) N inv
    (fun j hj => by
      have hidx : (N : Int) - 1 - (j : Int) = ((N - 1 - j : ℕ) : Int) := by omega
      have hnotge : ¬ ((N : Int) - (j : Int) ≤ (N : Int) - 1 - (j : Int)) := by omega
      have hcell : (inv j).work t₀ ((inv j).workPos t₀) ≠ .blank := by
        dsimp only [inv]; simp only [↓reduceIte]
        rw [ite_eq_right hnotge, hidx]
        exact hNonBlank (N - 1 - j) (by omega)
      refine ⟨bne_blank_of_ne hcell, ?_⟩
      unfold writeDirAct
      rw [applyAct_mkAct1]
      refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
      · dsimp only [inv]
        by_cases hi : i = t₀
        · subst hi
          simp only [↓reduceIte]
          split_ifs <;> first | rfl | omega
        · simp [hi]
      · dsimp only [inv, Transpose.Dir.shift]
        by_cases hi : i = t₀
        · subst hi; simp only [↓reduceIte]; omega
        · simp [hi])
    (by
      dsimp only [inv]; simp only [↓reduceIte]
      have hnot : ¬ ((N : Int) - (N : Int) ≤ (N : Int) - 1 - (N : Int)) := by omega
      rw [ite_eq_right hnot]
      have hm1 : (N : Int) - 1 - (N : Int) = -1 := by omega
      rw [hm1, hOutside (-1) (Or.inl (by omega))]; rfl)
  have hExit : applyAct w (stepDirAct t₀ .right) (inv N) =
      { m with
        work    := fun i p => if i = t₀ then .blank else m.work i p
        workPos := fun i => if i = t₀ then 0 else m.workPos i } := by
    unfold stepDirAct
    rw [applyAct_mkAct1]
    refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
    · dsimp only [inv]
      by_cases hi : i = t₀
      · subst hi
        simp only [↓reduceIte]
        split_ifs
        · rfl
        · exact hOutside _ (Or.inl (by omega))
        · rfl
        · exact hOutside p (Or.inl (by omega))
      · simp [hi]
    · dsimp only [inv, Transpose.Dir.shift]
      by_cases hi : i = t₀
      · subst hi; simp only [↓reduceIte]; omega
      · simp [hi]
  rw [hExit] at hLoop
  have hTime : 1 + (N + 1) = N + 2 := by omega
  rw [← hTime]
  exact h1.seq hLoop

/-- Rewind `inPos` from `(P : Int)` (`P ≤ w.length`) back to `0` without touching work tapes. -/
private def rewindInputFromPos {k : ℕ} : Block k WorkSym :=
  (Block.act (inStepDirAct .left)).seq
    (Block.while1 (fun inp _ => inp.isSome) (inStepDirAct .left) (inStepDirAct .right))

private theorem Runs_rewindInputFromPos {k : ℕ} {w : List Bool}
    (m : Mem k WorkSym) (P : ℕ) (hPos : m.inPos = (P : Int)) (hLe : P ≤ w.length) :
    Runs rewindInputFromPos w m { m with inPos := 0 } (P + 2) := by
  unfold rewindInputFromPos
  let inv (j : ℕ) : Mem k WorkSym := { m with inPos := (P : Int) - 1 - (j : Int) }
  have h1 : Runs (Block.act (inStepDirAct .left)) w m (inv 0) 1 := by
    have heq : applyAct w (inStepDirAct .left) m = inv 0 := by
      rw [applyAct_inStepDir, hPos]
      refine Mem.eq_of_fields ?_ (fun _ _ => rfl) (fun _ => rfl) rfl
      dsimp only [inv, Transpose.Dir.shift]; omega
    rw [← heq]; exact Runs.act _ m
  have hLoop := Runs.while1 (w := w) (fun inp (_ : Fin k → WorkSym) => inp.isSome)
    (inStepDirAct .left) (inStepDirAct .right) P inv
    (fun j hj => by
      have hidx : (P : Int) - 1 - (j : Int) = ((P - 1 - j : ℕ) : Int) := by omega
      have hlt : P - 1 - j < w.length := by omega
      have hsome : (Transpose.readInput w (inv j).inPos).isSome = true := by
        dsimp only [inv]
        rw [hidx, readInput_of_nonneg, List.getElem?_eq_getElem hlt]
        rfl
      refine ⟨hsome, ?_⟩
      rw [applyAct_inStepDir]
      refine Mem.eq_of_fields ?_ (fun _ _ => rfl) (fun _ => rfl) rfl
      dsimp only [inv, Transpose.Dir.shift]; omega)
    (by
      dsimp only [inv]
      have hm1 : (P : Int) - 1 - (P : Int) = -1 := by omega
      rw [hm1]
      unfold Transpose.readInput
      have hlt : (-1 : Int) < 0 := by omega
      rw [ite_eq_left hlt]; rfl)
  have hExit : applyAct w (inStepDirAct .right) (inv P) = { m with inPos := 0 } := by
    rw [applyAct_inStepDir]
    refine Mem.eq_of_fields ?_ (fun _ _ => rfl) (fun _ => rfl) rfl
    dsimp only [inv, Transpose.Dir.shift]; omega
  rw [hExit] at hLoop
  have hTime : 1 + (P + 1) = P + 2 := by omega
  rw [← hTime]
  exact h1.seq hLoop

/-- Append one `.u` mark to `unaryTape N` on tape `t₀` (head `0 → 0`) in `2 N + 4` steps. -/
private def appendOneUnary {k : ℕ} (t₀ : Fin k) : Block k WorkSym :=
  (Block.while1 (fun _ sc => sc t₀ == .u)
    (stepDirAct t₀ .right) (writeDirAct t₀ .u .right)).seq
    (rewindFromEnd t₀)

private theorem Runs_appendOneUnary {k : ℕ} {w : List Bool} (t₀ : Fin k)
    (m : Mem k WorkSym) (N : ℕ)
    (hTape : m.work t₀ = unaryTape N) (hPos : m.workPos t₀ = 0) :
    Runs (appendOneUnary t₀) w m
      { m with work := fun i p => if i = t₀ then unaryTape (N + 1) p else m.work i p }
      (2 * N + 4) := by
  unfold appendOneUnary
  let inv (j : ℕ) : Mem k WorkSym :=
    { m with workPos := fun i => if i = t₀ then (j : Int) else m.workPos i }
  have hInv0 : inv 0 = m := by
    refine Mem.eq_of_fields rfl (fun _ _ => rfl) (fun i => ?_) rfl
    dsimp only [inv]
    by_cases hi : i = t₀ <;> simp [hi, hPos]
  have hScan := Runs.while1 (w := w)
    (fun _ (sc : Fin k → WorkSym) => sc t₀ == .u)
    (stepDirAct t₀ .right) (writeDirAct t₀ .u .right) N inv
    (fun j hj => by
      have hcell : ((inv j).work t₀ ((inv j).workPos t₀) == .u) = true := by
        dsimp only [inv]; simp only [↓reduceIte]; rw [hTape, unaryTape_lt hj]; rfl
      refine ⟨hcell, ?_⟩
      unfold stepDirAct
      rw [applyAct_mkAct1]
      refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
      · dsimp only [inv]
        by_cases hi : i = t₀
        · subst hi; simp only [↓reduceIte]; exact congrFun (ite_self_cell (m.work i) _) p
        · simp [hi]
      · dsimp only [inv, Transpose.Dir.shift]
        by_cases hi : i = t₀
        · subst hi; simp only [↓reduceIte]; omega
        · simp [hi])
    (by dsimp only [inv]; simp only [↓reduceIte]; rw [hTape, unaryTape_ge le_rfl]; rfl)
  let mMid : Mem k WorkSym :=
    { m with
      work    := fun i p => if i = t₀ then unaryTape (N + 1) p else m.work i p
      workPos := fun i => if i = t₀ then ((N + 1 : ℕ) : Int) else m.workPos i }
  have hMidEq : applyAct w (writeDirAct t₀ .u .right) (inv N) = mMid := by
    unfold writeDirAct
    rw [applyAct_mkAct1]
    refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
    · dsimp only [inv, mMid]
      by_cases hi : i = t₀
      · subst hi
        simp only [↓reduceIte, hTape]
        exact congrFun (unaryTape_write_end N) p
      · simp [hi]
    · dsimp only [inv, mMid, Transpose.Dir.shift]
      by_cases hi : i = t₀
      · subst hi; simp only [↓reduceIte]; omega
      · simp [hi]
  rw [hInv0, hMidEq] at hScan
  have hRew := Runs_rewindFromEnd (w := w) t₀ mMid (N + 1)
    (by dsimp only [mMid]; simp only [↓reduceIte])
    (fun j hj => by dsimp only [mMid]; simp only [↓reduceIte]; rw [unaryTape_lt hj]; decide)
    (by dsimp only [mMid]; simp only [↓reduceIte]; exact unaryTape_neg (by omega))
  have hFinal : { mMid with workPos := fun i => if i = t₀ then 0 else mMid.workPos i } =
      { m with work := fun i p => if i = t₀ then unaryTape (N + 1) p else m.work i p } := by
    refine Mem.eq_of_fields rfl (fun _ _ => rfl) (fun i => ?_) rfl
    dsimp only [mMid]
    by_cases hi : i = t₀ <;> simp [hi, hPos]
  rw [hFinal] at hRew
  have hTime : (N + 1) + ((N + 1) + 2) = 2 * N + 4 := by omega
  rw [← hTime]
  exact hScan.seq hRew

private def clampRightAct {k : ℕ} (t₁ : Fin k) : Action k WorkSym :=
  mkAct1 t₁ (fun inp _ => if inp.isSome then .right else .stay)
    (fun _ sym => (sym, .right)) (fun _ _ => none)

/-- Advance `inPos` from `0` to `min (M * s) w.length` using unary rulers `M` on `t₀` and `s` on `t₁`. -/
private def advanceClampedByPair {k : ℕ} (t₀ t₁ : Fin k) : Block k WorkSym :=
  (Block.loop (fun _ sc => sc t₀ == .u)
    (stepDirAct t₀ .right) actStay
    ((Block.while1 (fun _ sc => sc t₁ == .u) (clampRightAct t₁) actStay).seq
      (rewindFromEnd t₁))).seq
    (rewindFromEnd t₀)

private theorem Runs_advanceClampedByPair {k : ℕ} {w : List Bool} {t₀ t₁ : Fin k}
    (hne : t₀ ≠ t₁) (m : Mem k WorkSym) (M s : ℕ)
    (hIn : m.inPos = 0)
    (hT0 : m.work t₀ = unaryTape M) (hP0 : m.workPos t₀ = 0)
    (hT1 : m.work t₁ = unaryTape s) (hP1 : m.workPos t₁ = 0) :
    Runs (advanceClampedByPair t₀ t₁) w m
      { m with inPos := ((min (M * s) w.length : ℕ) : Int) }
      (2 * M * s + 5 * M + 3) := by
  unfold advanceClampedByPair
  have hInner : ∀ (base : ℕ) (mB : Mem k WorkSym),
      mB.inPos = ((min base w.length : ℕ) : Int) →
      mB.work t₁ = unaryTape s →
      mB.workPos t₁ = 0 →
      Runs ((Block.while1 (fun _ sc => sc t₁ == .u) (clampRightAct t₁) actStay).seq
        (rewindFromEnd t₁)) w mB
        { mB with inPos := ((min (base + s) w.length : ℕ) : Int) } (2 * s + 3) := by
    intro base mB hBIn hBT1 hBP1
    let inv (j : ℕ) : Mem k WorkSym :=
      { mB with
        inPos   := ((min (base + j) w.length : ℕ) : Int)
        workPos := fun i => if i = t₁ then (j : Int) else mB.workPos i }
    have hInv0 : inv 0 = mB := by
      refine Mem.eq_of_fields ?_ (fun _ _ => rfl) (fun i => ?_) rfl
      · dsimp only [inv]; rw [Nat.add_zero, hBIn]
      · dsimp only [inv]; by_cases hi : i = t₁ <;> simp [hi, hBP1]
    have hW := Runs.while1 (w := w)
      (fun _ (sc : Fin k → WorkSym) => sc t₁ == .u)
      (clampRightAct t₁) actStay s inv
      (fun j hj => by
        have hcell : ((inv j).work t₁ ((inv j).workPos t₁) == .u) = true := by
          dsimp only [inv]; simp only [↓reduceIte]; rw [hBT1, unaryTape_lt hj]; rfl
        refine ⟨hcell, ?_⟩
        unfold clampRightAct
        rw [applyAct_mkAct1]
        refine Mem.eq_of_fields ?_ (fun i p => ?_) (fun i => ?_) rfl
        · dsimp only [inv]
          rw [readInput_of_nonneg]
          by_cases hlt : base + j < w.length
          · have hmin1 : min (base + j) w.length = base + j := Nat.min_eq_left (by omega)
            have hmin2 : min (base + (j + 1)) w.length = base + j + 1 := Nat.min_eq_left (by omega)
            rw [hmin1, hmin2, List.getElem?_eq_getElem hlt]
            simp only [Option.isSome, ↓reduceIte, Transpose.Dir.shift]; omega
          · have hmin1 : min (base + j) w.length = w.length := Nat.min_eq_right (by omega)
            have hmin2 : min (base + (j + 1)) w.length = w.length := Nat.min_eq_right (by omega)
            rw [hmin1, hmin2, List.getElem?_eq_none le_rfl]
            rfl
        · dsimp only [inv]
          by_cases hi : i = t₁
          · subst hi; simp only [↓reduceIte]; exact congrFun (ite_self_cell (mB.work i) _) p
          · simp [hi]
        · dsimp only [inv, Transpose.Dir.shift]
          by_cases hi : i = t₁
          · subst hi; simp only [↓reduceIte]; omega
          · simp [hi])
      (by dsimp only [inv]; simp only [↓reduceIte]; rw [hBT1, unaryTape_ge le_rfl]; rfl)
    rw [hInv0, applyAct_actStay] at hW
    have hRew := Runs_rewindFromEnd (w := w) t₁ (inv s) s
      (by dsimp only [inv]; simp only [↓reduceIte])
      (fun j hj => by dsimp only [inv]; rw [hBT1, unaryTape_lt hj]; decide)
      (by dsimp only [inv]; rw [hBT1]; exact unaryTape_neg (by omega))
    have hEnd : { inv s with workPos := fun i => if i = t₁ then 0 else (inv s).workPos i } =
        { mB with inPos := ((min (base + s) w.length : ℕ) : Int) } := by
      refine Mem.eq_of_fields rfl (fun _ _ => rfl) (fun i => ?_) rfl
      dsimp only [inv]
      by_cases hi : i = t₁ <;> simp [hi, hBP1]
    rw [hEnd] at hRew
    have hTime : (s + 1) + (s + 2) = 2 * s + 3 := by omega
    rw [← hTime]
    exact hW.seq hRew
  let outerInv (q : ℕ) : Mem k WorkSym :=
    { m with
      inPos   := ((min (q * s) w.length : ℕ) : Int)
      workPos := fun i => if i = t₀ then (q : Int) else m.workPos i }
  have hOuter0 : outerInv 0 = m := by
    refine Mem.eq_of_fields ?_ (fun _ _ => rfl) (fun i => ?_) rfl
    · dsimp only [outerInv]; simp [hIn]
    · dsimp only [outerInv]; by_cases hi : i = t₀ <;> simp [hi, hP0]
  have hOuter := Runs.loop (w := w)
    (fun _ (sc : Fin k → WorkSym) => sc t₀ == .u)
    (stepDirAct t₀ .right) actStay _ (2 * s + 3) M outerInv
    (fun q hq => by
      have hcell : ((outerInv q).work t₀ ((outerInv q).workPos t₀) == .u) = true := by
        dsimp only [outerInv]; simp only [↓reduceIte]; rw [hT0, unaryTape_lt hq]; rfl
      refine ⟨hcell, ?_⟩
      let mEnter : Mem k WorkSym :=
        { m with
          inPos   := ((min (q * s) w.length : ℕ) : Int)
          workPos := fun i => if i = t₀ then ((q + 1 : ℕ) : Int) else m.workPos i }
      have hEnt : applyAct w (stepDirAct t₀ .right) (outerInv q) = mEnter := by
        unfold stepDirAct
        rw [applyAct_mkAct1]
        refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
        · dsimp only [outerInv, mEnter]
          by_cases hi : i = t₀
          · subst hi; simp only [↓reduceIte]; exact congrFun (ite_self_cell (m.work i) _) p
          · simp [hi]
        · dsimp only [outerInv, mEnter, Transpose.Dir.shift]
          by_cases hi : i = t₀
          · subst hi; simp only [↓reduceIte]; omega
          · simp [hi]
      rw [hEnt]
      have hInQ := hInner (q * s) mEnter rfl hT1
        (by dsimp only [mEnter]; rw [ite_eq_right (Ne.symm hne), hP1])
      have hMul : q * s + s = (q + 1) * s := by ring
      simpa only [mEnter, outerInv, hMul] using hInQ)
    (by dsimp only [outerInv]; simp only [↓reduceIte]; rw [hT0, unaryTape_ge le_rfl]; rfl)
  rw [hOuter0, applyAct_actStay] at hOuter
  have hRew0 := Runs_rewindFromEnd (w := w) t₀ (outerInv M) M
    (by dsimp only [outerInv]; simp only [↓reduceIte])
    (fun j hj => by dsimp only [outerInv]; rw [hT0, unaryTape_lt hj]; decide)
    (by dsimp only [outerInv]; rw [hT0]; exact unaryTape_neg (by omega))
  have hEnd0 : { outerInv M with workPos := fun i => if i = t₀ then 0 else (outerInv M).workPos i } =
      { m with inPos := ((min (M * s) w.length : ℕ) : Int) } := by
    refine Mem.eq_of_fields rfl (fun _ _ => rfl) (fun i => ?_) rfl
    dsimp only [outerInv]; by_cases hi : i = t₀ <;> simp [hi, hP0]
  rw [hEnd0] at hRew0
  have hTime : (M * (1 + (2 * s + 3)) + 1) + (M + 2) = 2 * M * s + 5 * M + 3 := by ring
  rw [← hTime]
  exact hOuter.seq hRew0

private def quadEnterPush {k : ℕ} (t₀ t₁ : Fin k) : Action k WorkSym :=
  mkAct2 t₀ t₁ (fun _ _ _ => .stay)
    (fun _ s₀ _ => (s₀, .right)) (fun _ _ _ => (.u, .left)) (fun _ _ _ => none)

private def quadCopyBack {k : ℕ} (t₀ t₁ : Fin k) : Action k WorkSym :=
  mkAct2 t₀ t₁ (fun _ _ _ => .stay)
    (fun _ _ _ => (.u, .right)) (fun _ _ _ => (.blank, .right)) (fun _ _ _ => none)

/-- Quadruple `unaryTape M` on `t₀` to `unaryTape (4 * M)` using negative cells of `t₁` (`10 M + 6` steps). -/
private def quadrupleUnary {k : ℕ} (t₀ t₁ : Fin k) : Block k WorkSym :=
  ((((Block.act (stepDirAct t₁ .left)).seq (Block.act (stepDirAct t₁ .left))).seq
    (Block.loop (fun _ sc => sc t₀ == .u)
      (quadEnterPush t₀ t₁) (stepDirAct t₁ .right)
      ((Block.act (writeDirAct t₁ .u .left)).seq (Block.act (writeDirAct t₁ .u .left))))).seq
    (Block.while1 (fun _ sc => sc t₁ == .u)
      (quadCopyBack t₀ t₁) (stepDirAct t₁ .right))).seq
    (rewindFromEnd t₀)

private theorem Runs_quadrupleUnary {k : ℕ} {w : List Bool} {t₀ t₁ : Fin k}
    (hne : t₀ ≠ t₁) (m : Mem k WorkSym) (M s : ℕ)
    (hT0 : m.work t₀ = unaryTape M) (hP0 : m.workPos t₀ = 0)
    (hT1 : m.work t₁ = unaryTape s) (hP1 : m.workPos t₁ = 0) :
    Runs (quadrupleUnary t₀ t₁) w m
      { m with work := fun i p => if i = t₀ then unaryTape (4 * M) p else m.work i p }
      (10 * M + 6) := by
  unfold quadrupleUnary
  let negScratch (cnt : ℕ) (p : Int) : WorkSym :=
    if -1 - (cnt : Int) ≤ p ∧ p ≤ -2 then .u else unaryTape s p
  have hScratch0 : negScratch 0 = unaryTape s := by
    funext p; unfold negScratch
    split_ifs <;> first | rfl | omega
  let pushInv (j : ℕ) : Mem k WorkSym :=
    { m with
      work := fun i p => if i = t₁ then negScratch (3 * j) p else m.work i p
      workPos := fun i =>
        if i = t₀ then (j : Int)
        else if i = t₁ then -2 - (3 * (j : Int))
        else m.workPos i }
  -- Step 1: two left steps on `t₁` (`0 → -1 → -2`)
  let mL1 : Mem k WorkSym :=
    { m with workPos := fun i => if i = t₁ then -1 else m.workPos i }
  have hL1 : applyAct w (stepDirAct t₁ .left) m = mL1 := by
    unfold stepDirAct; rw [applyAct_mkAct1]
    refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
    · dsimp only [mL1]
      by_cases hi : i = t₁
      · subst hi; simp only [↓reduceIte]; exact congrFun (ite_self_cell (m.work i) _) p
      · simp [hi]
    · dsimp only [mL1, Transpose.Dir.shift]
      by_cases hi : i = t₁ <;> simp [hi, hP1]
  have hL2 : applyAct w (stepDirAct t₁ .left) mL1 = pushInv 0 := by
    unfold stepDirAct; rw [applyAct_mkAct1]
    refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
    · dsimp only [mL1, pushInv]
      by_cases hi : i = t₁
      · subst hi
        simp only [↓reduceIte, Nat.mul_zero, hScratch0, ← hT1]
        exact congrFun (ite_self_cell (m.work i) _) p
      · simp [hi]
    · dsimp only [mL1, pushInv, Transpose.Dir.shift]
      by_cases hi0 : i = t₀
      · subst hi0; simp [hne, hP0]
      · by_cases hi1 : i = t₁
        · subst hi1; simp [hi0]
        · simp [hi0, hi1]
  have hStepTwo : Runs ((Block.act (stepDirAct t₁ .left)).seq (Block.act (stepDirAct t₁ .left)))
      w m (pushInv 0) 2 := by
    have r1 : Runs (Block.act (stepDirAct t₁ .left)) w m mL1 1 := by rw [← hL1]; exact Runs.act _ _
    have r2 : Runs (Block.act (stepDirAct t₁ .left)) w mL1 (pushInv 0) 1 := by
      rw [← hL2]; exact Runs.act _ _
    exact r1.seq r2
  -- Helper for extending `negScratch c` at `-2 - c`
  have hExtendScratch : ∀ (c : ℕ),
      (fun p : Int => if p = -2 - (c : Int) then WorkSym.u else negScratch c p) =
        negScratch (c + 1) := by
    intro c; funext p; unfold negScratch
    by_cases hp : p = -2 - (c : Int)
    · subst hp
      have h : -1 - ((c + 1 : ℕ) : Int) ≤ -2 - (c : Int) ∧ -2 - (c : Int) ≤ -2 := by omega
      rw [ite_eq_left rfl, ite_eq_left h]
    · rw [ite_eq_right hp]
      by_cases h1 : -1 - (c : Int) ≤ p ∧ p ≤ -2
      · have h2 : -1 - ((c + 1 : ℕ) : Int) ≤ p ∧ p ≤ -2 := by omega
        rw [ite_eq_left h1, ite_eq_left h2]
      · have h2 : ¬ (-1 - ((c + 1 : ℕ) : Int) ≤ p ∧ p ≤ -2) := by omega
        rw [ite_eq_right h1, ite_eq_right h2]
  -- Step 2: `pushThreeLoop` (`M` iterations, `3 M + 1` steps)
  have hPush := Runs.loop (w := w)
    (fun _ (sc : Fin k → WorkSym) => sc t₀ == .u)
    (quadEnterPush t₀ t₁) (stepDirAct t₁ .right)
    ((Block.act (writeDirAct t₁ .u .left)).seq (Block.act (writeDirAct t₁ .u .left))) 2 M pushInv
    (fun j hj => by
      have hcell : ((pushInv j).work t₀ ((pushInv j).workPos t₀) == .u) = true := by
        dsimp only [pushInv]
        simp only [hne, ↓reduceIte, hT0, unaryTape_lt hj]; rfl
      refine ⟨hcell, ?_⟩
      let mP1 : Mem k WorkSym :=
        { m with
          work := fun i p => if i = t₁ then negScratch (3 * j + 1) p else m.work i p
          workPos := fun i =>
            if i = t₀ then ((j + 1 : ℕ) : Int)
            else if i = t₁ then -2 - (3 * (j : Int) + 1)
            else m.workPos i }
      let mP2 : Mem k WorkSym :=
        { m with
          work := fun i p => if i = t₁ then negScratch (3 * j + 2) p else m.work i p
          workPos := fun i =>
            if i = t₀ then ((j + 1 : ℕ) : Int)
            else if i = t₁ then -2 - (3 * (j : Int) + 2)
            else m.workPos i }
      have hE1 : applyAct w (quadEnterPush t₀ t₁) (pushInv j) = mP1 := by
        unfold quadEnterPush
        rw [applyAct_mkAct2 w (pushInv j) hne]
        refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
        · dsimp only [pushInv, mP1]
          by_cases hi0 : i = t₀
          · subst hi0
            simp only [hne, ↓reduceIte]
            exact congrFun (ite_self_cell (m.work i) _) p
          · by_cases hi1 : i = t₁
            · subst hi1
              simp only [Ne.symm hne, ↓reduceIte]
              have hc : -2 - 3 * (j : Int) = -2 - ((3 * j : ℕ) : Int) := by omega
              rw [hc]
              exact congrFun (hExtendScratch (3 * j)) p
            · simp [hi0, hi1]
        · dsimp only [pushInv, mP1, Transpose.Dir.shift]
          by_cases hi0 : i = t₀
          · subst hi0; simp only [↓reduceIte]; omega
          · by_cases hi1 : i = t₁
            · subst hi1; simp only [hi0, ↓reduceIte]; omega
            · simp [hi0, hi1]
      have hE2 : applyAct w (writeDirAct t₁ .u .left) mP1 = mP2 := by
        unfold writeDirAct; rw [applyAct_mkAct1]
        refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
        · dsimp only [mP1, mP2]
          by_cases hi1 : i = t₁
          · subst hi1
            simp only [Ne.symm hne, ↓reduceIte]
            have hc : -2 - (3 * (j : Int) + 1) = -2 - ((3 * j + 1 : ℕ) : Int) := by omega
            rw [hc]
            exact congrFun (hExtendScratch (3 * j + 1)) p
          · simp [hi1]
        · dsimp only [mP1, mP2, Transpose.Dir.shift]
          by_cases hi0 : i = t₀
          · subst hi0; simp [hne]
          · by_cases hi1 : i = t₁
            · subst hi1; simp only [hi0, ↓reduceIte]; omega
            · simp [hi0, hi1]
      have hE3 : applyAct w (writeDirAct t₁ .u .left) mP2 = pushInv (j + 1) := by
        unfold writeDirAct; rw [applyAct_mkAct1]
        refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
        · dsimp only [mP2, pushInv]
          by_cases hi1 : i = t₁
          · subst hi1
            simp only [Ne.symm hne, ↓reduceIte]
            have hc : -2 - (3 * (j : Int) + 2) = -2 - ((3 * j + 2 : ℕ) : Int) := by omega
            have h3 : 3 * j + 2 + 1 = 3 * (j + 1) := by omega
            rw [hc, ← h3]
            exact congrFun (hExtendScratch (3 * j + 2)) p
          · simp [hi1]
        · dsimp only [mP2, pushInv, Transpose.Dir.shift]
          by_cases hi0 : i = t₀
          · subst hi0; simp [hne]
          · by_cases hi1 : i = t₁
            · subst hi1; simp only [hi0, ↓reduceIte]; omega
            · simp [hi0, hi1]
      rw [hE1]
      have r1 : Runs (Block.act (writeDirAct t₁ .u .left)) w mP1 mP2 1 := by
        rw [← hE2]; exact Runs.act _ _
      have r2 : Runs (Block.act (writeDirAct t₁ .u .left)) w mP2 (pushInv (j + 1)) 1 := by
        rw [← hE3]; exact Runs.act _ _
      exact r1.seq r2)
    (by
      dsimp only [pushInv]
      simp only [hne, ↓reduceIte, hT0, unaryTape_ge le_rfl]; rfl)
  -- Step 3: `drainLoop` (`3 M` iterations, `3 M + 1` steps)
  let drainInv (r : ℕ) : Mem k WorkSym :=
    { m with
      work := fun i p =>
        if i = t₀ then unaryTape (M + r) p
        else if i = t₁ then negScratch (3 * M - r) p
        else m.work i p
      workPos := fun i =>
        if i = t₀ then ((M + r : ℕ) : Int)
        else if i = t₁ then -1 - (3 * (M : Int)) + (r : Int)
        else m.workPos i }
  have hPushExit : applyAct w (stepDirAct t₁ .right) (pushInv M) = drainInv 0 := by
    unfold stepDirAct; rw [applyAct_mkAct1]
    refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
    · dsimp only [pushInv, drainInv]
      by_cases hi0 : i = t₀
      · subst hi0; simp [hne, hT0]
      · by_cases hi1 : i = t₁
        · subst hi1
          simp only [Ne.symm hne, ↓reduceIte, Nat.sub_zero]
          exact congrFun (ite_self_cell (negScratch (3 * M)) _) p
        · simp [hi0, hi1]
    · dsimp only [pushInv, drainInv, Transpose.Dir.shift]
      by_cases hi0 : i = t₀
      · subst hi0; simp [hne]
      · by_cases hi1 : i = t₁
        · subst hi1; simp only [hi0, ↓reduceIte]; omega
        · simp [hi0, hi1]
  rw [hPushExit] at hPush
  have hDrain := Runs.while1 (w := w)
    (fun _ (sc : Fin k → WorkSym) => sc t₁ == .u)
    (quadCopyBack t₀ t₁) (stepDirAct t₁ .right) (3 * M) drainInv
    (fun r hr => by
      have hcell : ((drainInv r).work t₁ ((drainInv r).workPos t₁) == .u) = true := by
        dsimp only [drainInv]
        simp only [Ne.symm hne, ↓reduceIte]
        unfold negScratch
        have hcond : -1 - ((3 * M - r : ℕ) : Int) ≤ -1 - 3 * (M : Int) + (r : Int) ∧
            -1 - 3 * (M : Int) + (r : Int) ≤ -2 := by omega
        rw [ite_eq_left hcond]; rfl
      refine ⟨hcell, ?_⟩
      unfold quadCopyBack
      rw [applyAct_mkAct2 w (drainInv r) hne]
      refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
      · dsimp only [drainInv]
        by_cases hi0 : i = t₀
        · subst hi0
          simp only [↓reduceIte]
          have hMR : M + (r + 1) = (M + r) + 1 := by omega
          rw [hMR]
          exact congrFun (unaryTape_write_end (M + r)) p
        · by_cases hi1 : i = t₁
          · subst hi1
            simp only [Ne.symm hne, ↓reduceIte]
            unfold negScratch
            by_cases hp : p = -1 - 3 * (M : Int) + (r : Int)
            · subst hp
              rw [ite_eq_left rfl]
              have hnot : ¬ (-1 - ((3 * M - (r + 1) : ℕ) : Int) ≤ -1 - 3 * (M : Int) + (r : Int) ∧
                  -1 - 3 * (M : Int) + (r : Int) ≤ -2) := by omega
              rw [ite_eq_right hnot, unaryTape_neg (by omega)]
            · rw [ite_eq_right hp]
              by_cases h1 : -1 - ((3 * M - r : ℕ) : Int) ≤ p ∧ p ≤ -2
              · have h2 : -1 - ((3 * M - (r + 1) : ℕ) : Int) ≤ p ∧ p ≤ -2 := by omega
                rw [ite_eq_left h1, ite_eq_left h2]
              · have h2 : ¬ (-1 - ((3 * M - (r + 1) : ℕ) : Int) ≤ p ∧ p ≤ -2) := by omega
                rw [ite_eq_right h1, ite_eq_right h2]
          · simp [hi0, hi1]
      · dsimp only [drainInv, Transpose.Dir.shift]
        by_cases hi0 : i = t₀
        · subst hi0; simp only [↓reduceIte]; omega
        · by_cases hi1 : i = t₁
          · subst hi1; simp only [hi0, ↓reduceIte]; omega
          · simp [hi0, hi1])
    (by
      dsimp only [drainInv]
      simp only [Ne.symm hne, ↓reduceIte, Nat.sub_self, hScratch0]
      have hm1 : -1 - 3 * (M : Int) + ((3 * M : ℕ) : Int) = -1 := by omega
      rw [hm1, unaryTape_neg (by omega)]; rfl)
  let mBeforeRew : Mem k WorkSym :=
    { m with
      work    := fun i p => if i = t₀ then unaryTape (4 * M) p else m.work i p
      workPos := fun i => if i = t₀ then ((4 * M : ℕ) : Int) else m.workPos i }
  have hDrainExit : applyAct w (stepDirAct t₁ .right) (drainInv (3 * M)) = mBeforeRew := by
    unfold stepDirAct; rw [applyAct_mkAct1]
    refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
    · dsimp only [drainInv, mBeforeRew]
      by_cases hi0 : i = t₀
      · subst hi0
        simp only [hne, ↓reduceIte]
        have h4 : M + 3 * M = 4 * M := by omega
        rw [h4]
      · by_cases hi1 : i = t₁
        · subst hi1
          simp only [Ne.symm hne, ↓reduceIte, Nat.sub_self, hScratch0, ← hT1]
          exact congrFun (ite_self_cell (m.work i) _) p
        · simp [hi0, hi1]
    · dsimp only [drainInv, mBeforeRew, Transpose.Dir.shift]
      by_cases hi0 : i = t₀
      · subst hi0
        simp only [hne, ↓reduceIte]
        have h4 : M + 3 * M = 4 * M := by omega
        rw [h4]
      · by_cases hi1 : i = t₁
        · subst hi1; simp only [hi0, ↓reduceIte, hP1]; omega
        · simp [hi0, hi1]
  rw [hDrainExit] at hDrain
  have hRew := Runs_rewindFromEnd (w := w) t₀ mBeforeRew (4 * M)
    (by dsimp only [mBeforeRew]; simp only [↓reduceIte])
    (fun j hj => by dsimp only [mBeforeRew]; simp only [↓reduceIte]; rw [unaryTape_lt hj]; decide)
    (by dsimp only [mBeforeRew]; simp only [↓reduceIte]; exact unaryTape_neg (by omega))
  have hFinal : { mBeforeRew with workPos := fun i => if i = t₀ then 0 else mBeforeRew.workPos i } =
      { m with work := fun i p => if i = t₀ then unaryTape (4 * M) p else m.work i p } := by
    refine Mem.eq_of_fields rfl (fun _ _ => rfl) (fun i => ?_) rfl
    dsimp only [mBeforeRew]; by_cases hi : i = t₀ <;> simp [hi, hP0]
  rw [hFinal] at hRew
  have hTime : ((2 + (M * (1 + 2) + 1)) + (3 * M + 1)) + (4 * M + 2) = 10 * M + 6 := by ring
  rw [← hTime]
  exact ((hStepTwo.seq hPush).seq hDrain).seq hRew

/-- Discover `b = Transpose.entryBits d` on `t₁` and `4 ^ b` on `t₀` in `≤ 120 * L` steps! -/
private def discoverEntryBits {k : ℕ} (t₀ t₁ : Fin k) : Block k WorkSym :=
  (((((((appendOneUnary t₀).seq (appendOneUnary t₀)).seq
    (appendOneUnary t₀)).seq (appendOneUnary t₀)).seq
    (appendOneUnary t₁)).seq (advanceClampedByPair t₀ t₁)).seq
    (Block.loop (fun inp _ => inp.isSome) actStay actStay
      (((rewindInputFromPos.seq (appendOneUnary t₁)).seq
        (quadrupleUnary t₀ t₁)).seq (advanceClampedByPair t₀ t₁)))).seq
    rewindInputFromPos

private theorem Runs_discoverEntryBits {k : ℕ} {t₀ t₁ : Fin k} (hne : t₀ ≠ t₁)
    {d : ℕ} (hd : 1 ≤ d) {w : List Bool}
    (hwLen : w.length = Transpose.inputLength d)
    (m : Mem k WorkSym)
    (hIn : m.inPos = 0)
    (hB0 : m.work t₀ = fun _ => .blank) (hP0 : m.workPos t₀ = 0)
    (hB1 : m.work t₁ = fun _ => .blank) (hP1 : m.workPos t₁ = 0) :
    let b := Transpose.entryBits d
    Runs (discoverEntryBits t₀ t₁) w m
      { m with
        work := fun i p =>
          if i = t₀ then unaryTape (4 ^ b) p
          else if i = t₁ then unaryTape b p
          else m.work i p }
      (120 * Transpose.inputLength d) := by
  intro b
  unfold discoverEntryBits
  have hb1 : 1 ≤ b := entryBits_pos_tm d
  have hL1 : 1 ≤ Transpose.inputLength d := inputLength_pos hd
  -- `init4`: 4 marks on `t₀`, 1 mark on `t₁`
  let mkState (s : ℕ) (pos : ℕ) : Mem k WorkSym :=
    { m with
      inPos := (pos : Int)
      work  := fun i p =>
        if i = t₀ then unaryTape (4 ^ s) p
        else if i = t₁ then unaryTape s p
        else m.work i p }
  have hApp0 : ∀ (n : ℕ) (mCur : Mem k WorkSym),
      mCur.work t₀ = unaryTape n →
      mCur.workPos = m.workPos →
      Runs (appendOneUnary t₀) w mCur
        { mCur with work := fun i p => if i = t₀ then unaryTape (n + 1) p else mCur.work i p }
        (2 * n + 4) := fun n mCur hT hP =>
    Runs_appendOneUnary t₀ mCur n hT (by rw [hP, hP0])
  let mU1 : Mem k WorkSym := { m with work := fun i p => if i = t₀ then unaryTape 1 p else m.work i p }
  let mU2 : Mem k WorkSym := { m with work := fun i p => if i = t₀ then unaryTape 2 p else m.work i p }
  let mU3 : Mem k WorkSym := { m with work := fun i p => if i = t₀ then unaryTape 3 p else m.work i p }
  let mU4 : Mem k WorkSym := { m with work := fun i p => if i = t₀ then unaryTape 4 p else m.work i p }
  have rU1 : Runs (appendOneUnary t₀) w m mU1 4 := by
    simpa [mU1] using hApp0 0 m (by rw [hB0, unaryTape_zero]) rfl
  have rU2 : Runs (appendOneUnary t₀) w mU1 mU2 6 := by
    have h := hApp0 1 mU1 (by funext p; dsimp only [mU1]; simp) rfl
    have heq : { mU1 with work := fun i p => if i = t₀ then unaryTape 2 p else mU1.work i p } = mU2 := by
      refine Mem.eq_of_fields rfl (fun i p => ?_) (fun _ => rfl) rfl
      dsimp only [mU1, mU2]; by_cases hi : i = t₀ <;> simp [hi]
    rw [heq] at h; exact h
  have rU3 : Runs (appendOneUnary t₀) w mU2 mU3 8 := by
    have h := hApp0 2 mU2 (by funext p; dsimp only [mU2]; simp) rfl
    have heq : { mU2 with work := fun i p => if i = t₀ then unaryTape 3 p else mU2.work i p } = mU3 := by
      refine Mem.eq_of_fields rfl (fun i p => ?_) (fun _ => rfl) rfl
      dsimp only [mU2, mU3]; by_cases hi : i = t₀ <;> simp [hi]
    rw [heq] at h; exact h
  have rU4 : Runs (appendOneUnary t₀) w mU3 mU4 10 := by
    have h := hApp0 3 mU3 (by funext p; dsimp only [mU3]; simp) rfl
    have heq : { mU3 with work := fun i p => if i = t₀ then unaryTape 4 p else mU3.work i p } = mU4 := by
      refine Mem.eq_of_fields rfl (fun i p => ?_) (fun _ => rfl) rfl
      dsimp only [mU3, mU4]; by_cases hi : i = t₀ <;> simp [hi]
    rw [heq] at h; exact h
  have rS1 : Runs (appendOneUnary t₁) w mU4 (mkState 1 0) 4 := by
    have h := Runs_appendOneUnary (w := w) t₁ mU4 0
      (by funext p; dsimp only [mU4]; simp [Ne.symm hne, hB1, unaryTape_zero]) hP1
    have heq : { mU4 with work := fun i p => if i = t₁ then unaryTape 1 p else mU4.work i p } =
        mkState 1 0 := by
      refine Mem.eq_of_fields hIn (fun i p => ?_) (fun _ => rfl) rfl
      dsimp only [mU4, mkState]
      by_cases hi0 : i = t₀
      · subst hi0; simp [hne]
      · by_cases hi1 : i = t₁
        · subst hi1; simp [hi0]
        · simp [hi0, hi1]
    rw [heq] at h; exact h
  have rInit : Runs (((((appendOneUnary t₀).seq (appendOneUnary t₀)).seq
      (appendOneUnary t₀)).seq (appendOneUnary t₀)).seq (appendOneUnary t₁))
      w m (mkState 1 0) 32 := by
    simpa using (((rU1.seq rU2).seq rU3).seq rU4).seq rS1
  -- Initial `advanceClampedByPair` at `s = 1` (`4^1 * 1 = 4`, `2*4*1 + 5*4 + 3 = 31` steps)
  let loopInv (j : ℕ) : Mem k WorkSym :=
    mkState (j + 1) (min (4 ^ (j + 1) * (j + 1)) w.length)
  have rAdv0 : Runs (advanceClampedByPair t₀ t₁) w (mkState 1 0) (loopInv 0) 31 := by
    have h := Runs_advanceClampedByPair (w := w) hne (mkState 1 0) 4 1 rfl
      (by funext p; dsimp only [mkState]; simp) hP0
      (by funext p; dsimp only [mkState]; simp [Ne.symm hne]) hP1
    simpa [loopInv, mkState] using h
  -- Main geometric loop (`b - 1` iterations, `j = 0 .. b - 2`, `s = j + 1`)
  let tBody (j : ℕ) : ℕ :=
    let s := j + 1
    (min (4 ^ s * s) w.length + 2) + (2 * s + 4) + (10 * 4 ^ s + 6) +
      (2 * 4 ^ (s + 1) * (s + 1) + 5 * 4 ^ (s + 1) + 3)
  have rLoop := Runs.loop_sum (w := w)
    (fun inp (_ : Fin k → WorkSym) => inp.isSome) actStay actStay
    (((rewindInputFromPos.seq (appendOneUnary t₁)).seq
      (quadrupleUnary t₀ t₁)).seq (advanceClampedByPair t₀ t₁))
    (b - 1) tBody loopInv
    (fun j hj => by
      set s := j + 1
      have hsb : s < b := by omega
      have hltL : 4 ^ s * s < w.length := by
        rw [hwLen]; exact entryBits_quad_lower (by omega) hsb
      have hminEq : min (4 ^ s * s) w.length = 4 ^ s * s := Nat.min_eq_left hltL.le
      have hCond : (Transpose.readInput w (loopInv j).inPos).isSome = true := by
        dsimp only [loopInv, mkState]
        rw [readInput_of_nonneg, hminEq, List.getElem?_eq_getElem hltL]
        rfl
      refine ⟨hCond, ?_⟩
      rw [applyAct_actStay]
      -- 1) `rewindInputFromPos`
      have r1 := Runs_rewindInputFromPos (w := w) (loopInv j) (min (4 ^ s * s) w.length)
        rfl (Nat.min_le_right _ _)
      have hSt1 : { loopInv j with inPos := 0 } = mkState s 0 := rfl
      rw [hSt1] at r1
      -- 2) `appendOneUnary t₁` (`s → s + 1`)
      let mS2 : Mem k WorkSym :=
        { m with
          inPos := 0
          work  := fun i p =>
            if i = t₀ then unaryTape (4 ^ s) p
            else if i = t₁ then unaryTape (s + 1) p
            else m.work i p }
      have r2 := Runs_appendOneUnary (w := w) t₁ (mkState s 0) s
        (by funext p; dsimp only [mkState]; simp [Ne.symm hne]) hP1
      have hSt2 :
          { mkState s 0 with
            work := fun i p =>
              if i = t₁ then unaryTape (s + 1) p else (mkState s 0).work i p } = mS2 := by
        refine Mem.eq_of_fields rfl (fun i p => ?_) (fun _ => rfl) rfl
        dsimp only [mkState, mS2]
        by_cases hi1 : i = t₁
        · subst hi1; simp [Ne.symm hne]
        · by_cases hi0 : i = t₀
          · subst hi0; simp [hi1]
          · simp [hi0, hi1]
      rw [hSt2] at r2
      -- 3) `quadrupleUnary t₀ t₁` (`4 ^ s → 4 ^ (s + 1)`)
      have r3 := Runs_quadrupleUnary (w := w) hne mS2 (4 ^ s) (s + 1)
        (by funext p; dsimp only [mS2]; simp) hP0
        (by funext p; dsimp only [mS2]; simp [Ne.symm hne]) hP1
      have hSt3 :
          { mS2 with
            work := fun i p =>
              if i = t₀ then unaryTape (4 * 4 ^ s) p else mS2.work i p } = mkState (s + 1) 0 := by
        refine Mem.eq_of_fields rfl (fun i p => ?_) (fun _ => rfl) rfl
        dsimp only [mS2, mkState]
        by_cases hi0 : i = t₀
        · subst hi0; simp [pow_succ']
        · simp [hi0]
      rw [hSt3] at r3
      -- 4) `advanceClampedByPair t₀ t₁` at `(4^(s+1), s+1)`
      have r4 := Runs_advanceClampedByPair (w := w) hne (mkState (s + 1) 0) (4 ^ (s + 1)) (s + 1)
        rfl (by funext p; dsimp only [mkState]; simp) hP0
        (by funext p; dsimp only [mkState]; simp [Ne.symm hne]) hP1
      have hSt4 :
          { mkState (s + 1) 0 with
            inPos := ((min (4 ^ (s + 1) * (s + 1)) w.length : ℕ) : Int) } = loopInv (j + 1) := rfl
      rw [hSt4] at r4
      exact ((r1.seq r2).seq r3).seq r4)
    (by
      have hbEq : b - 1 + 1 = b := by omega
      dsimp only [loopInv, mkState]
      rw [hbEq, readInput_of_nonneg]
      have hUpper : w.length ≤ 4 ^ b * b := by
        rw [hwLen]; exact entryBits_quad_upper hd
      rw [Nat.min_eq_right hUpper, List.getElem?_eq_none le_rfl]
      rfl)
  rw [applyAct_actStay] at rLoop
  -- Final `rewindInputFromPos` from `min (4^b * b) w.length = w.length` to `0`
  have hbEq : b - 1 + 1 = b := by omega
  have hUpper : w.length ≤ 4 ^ b * b := by rw [hwLen]; exact entryBits_quad_upper hd
  have hFinalRew := Runs_rewindInputFromPos (w := w) (loopInv (b - 1)) w.length
    (by dsimp only [loopInv, mkState]; rw [hbEq, Nat.min_eq_right hUpper]) le_rfl
  have hFinalEq : { loopInv (b - 1) with inPos := 0 } =
      { m with
        work := fun i p =>
          if i = t₀ then unaryTape (4 ^ b) p
          else if i = t₁ then unaryTape b p
          else m.work i p } := by
    refine Mem.eq_of_fields hIn.symm (fun i p => ?_) (fun _ => rfl) rfl
    dsimp only [loopInv, mkState]; rw [hbEq]
  rw [hFinalEq] at hFinalRew
  have hAll := ((rInit.seq rAdv0).seq rLoop).seq hFinalRew
  -- Bound total time by `120 * inputLength d` via `natSum_le_of_step`
  apply hAll.of_le
  let g (j : ℕ) : ℕ := 14 * (4 ^ (j + 1) * (j + 1))
  have hStepBound : ∀ j < b - 1, (1 + tBody j) + g j ≤ g (j + 1) := by
    intro j _
    dsimp only [tBody, g]
    set s := j + 1
    have hs1 : 1 ≤ s := by omega
    have hpow1 : 1 ≤ 4 ^ s := Nat.one_le_pow s 4 (by decide)
    have hps : s ≤ 4 ^ s * s := by nlinarith
    have hmin_le : min (4 ^ s * s) w.length ≤ 4 ^ s * s := Nat.min_le_left _ _
    have hp4 : 4 ^ (s + 1) = 4 * 4 ^ s := pow_succ' 4 s
    rw [hp4]
    nlinarith
  have hSumLe := natSum_le_of_step hStepBound
  dsimp only [g] at hSumLe
  rw [hbEq] at hSumLe
  have hQuad4L : 4 ^ b * b ≤ 4 * Transpose.inputLength d := entryBits_quad_le_four_L hd
  rw [hwLen]
  omega

/-! ### 4. Theorem 7 Part 1: `O(L)` Turing Machine for Stone's Shuffle (`k = 3`) -/

private def halveEnterAct : Action 3 WorkSym :=
  mkAct2 0 2 (fun _ _ _ => .stay)
    (fun _ s₀ _ => (s₀, .right)) (fun _ _ _ => (.u, .right)) (fun _ _ _ => none)

private def halveUnaryBlock : Block 3 WorkSym :=
  ((Block.loop (fun _ sc => sc 0 == .u)
    halveEnterAct actStay (Block.act (stepDirAct 0 .right))).seq
    (eraseFromEnd 0)).seq
    (rewindFromEnd 2)

private theorem Runs_halveUnaryBlock {w : List Bool} (m : Mem 3 WorkSym) (H : ℕ)
    (hT0 : m.work 0 = unaryTape (2 * H)) (hP0 : m.workPos 0 = 0)
    (hB2 : m.work 2 = fun _ => .blank) (hP2 : m.workPos 2 = 0) :
    Runs halveUnaryBlock w m
      { m with
        work := fun i p =>
          if i = 0 then .blank
          else if i = 2 then unaryTape H p
          else m.work i p }
      (5 * H + 5) := by
  unfold halveUnaryBlock
  let inv (j : ℕ) : Mem 3 WorkSym :=
    { m with
      work    := fun i p => if i = 2 then unaryTape j p else m.work i p
      workPos := fun i =>
        if i = 0 then ((2 * j : ℕ) : Int)
        else if i = 2 then (j : Int)
        else m.workPos i }
  have hInv0 : inv 0 = m := by
    refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
    · dsimp only [inv]
      by_cases hi : i = 2
      · subst hi; simp only [↓reduceIte, unaryTape_zero, hB2]
      · simp [hi]
    · dsimp only [inv]
      fin_cases i <;> simp [hP0, hP2]
  have hLoop := Runs.loop (w := w)
    (fun _ (sc : Fin 3 → WorkSym) => sc 0 == .u)
    halveEnterAct actStay (Block.act (stepDirAct 0 .right)) 1 H inv
    (fun j hj => by
      have hcell : ((inv j).work 0 ((inv j).workPos 0) == .u) = true := by
        dsimp only [inv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
        rw [hT0, unaryTape_lt (by omega : 2 * j < 2 * H)]; rfl
      refine ⟨hcell, ?_⟩
      let mMid : Mem 3 WorkSym :=
        { m with
          work    := fun i p => if i = 2 then unaryTape (j + 1) p else m.work i p
          workPos := fun i =>
            if i = 0 then ((2 * j + 1 : ℕ) : Int)
            else if i = 2 then ((j + 1 : ℕ) : Int)
            else m.workPos i }
      have hEnt : applyAct w halveEnterAct (inv j) = mMid := by
        unfold halveEnterAct
        rw [applyAct_mkAct2 w (inv j) (by decide : (0 : Fin 3) ≠ 2)]
        refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
        · dsimp only [inv, mMid]
          fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Fin.reduceEq, ↓reduceIte]
          · exact congrFun (ite_self_cell (m.work 0) _) p
          · exact congrFun (unaryTape_write_end j) p
        · dsimp only [inv, mMid, Transpose.Dir.shift]
          fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Fin.reduceEq, ↓reduceIte] <;> omega
      have hBody : applyAct w (stepDirAct 0 .right) mMid = inv (j + 1) := by
        unfold stepDirAct; rw [applyAct_mkAct1]
        refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
        · dsimp only [mMid, inv]
          fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Fin.reduceEq, ↓reduceIte]
          exact congrFun (ite_self_cell (m.work 0) _) p
        · dsimp only [mMid, inv, Transpose.Dir.shift]
          fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Fin.reduceEq, ↓reduceIte]; omega
      rw [hEnt, ← hBody]; exact Runs.act _ _)
    (by
      dsimp only [inv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
      rw [hT0, unaryTape_ge le_rfl]; rfl)
  rw [hInv0, applyAct_actStay] at hLoop
  have hEr0 := Runs_eraseFromEnd (w := w) (0 : Fin 3) (inv H) (2 * H)
    (by dsimp only [inv]; simp)
    (fun j hj => by dsimp only [inv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]; rw [hT0, unaryTape_lt hj]; decide)
    (fun p hp => by
      dsimp only [inv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]; rw [hT0]
      rcases hp with hneg | hge
      · exact unaryTape_neg hneg
      · exact unaryTape_ge hge)
  let mAfterEr : Mem 3 WorkSym :=
    { inv H with
      work    := fun i p => if i = 0 then WorkSym.blank else (inv H).work i p
      workPos := fun i => if i = 0 then 0 else (inv H).workPos i }
  have hErEq : { inv H with
      work    := fun i p => if i = 0 then WorkSym.blank else (inv H).work i p
      workPos := fun i => if i = 0 then 0 else (inv H).workPos i } = mAfterEr := rfl
  rw [hErEq] at hEr0
  have hRew2 := Runs_rewindFromEnd (w := w) (2 : Fin 3) mAfterEr H
    (by dsimp only [mAfterEr, inv]; simp)
    (fun j hj => by dsimp only [mAfterEr, inv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]; rw [unaryTape_lt hj]; decide)
    (by dsimp only [mAfterEr, inv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]; exact unaryTape_neg (by omega))
  have hEnd : { mAfterEr with workPos := fun i => if i = 2 then 0 else mAfterEr.workPos i } =
      { m with
        work := fun i p =>
          if i = 0 then .blank
          else if i = 2 then unaryTape H p
          else m.work i p } := by
    refine Mem.eq_of_fields rfl (fun _ _ => rfl) (fun i => ?_) rfl
    dsimp only [mAfterEr, inv]
    fin_cases i <;> simp [hP0, hP2]
  rw [hEnd] at hRew2
  have hTime : ((H * (1 + 1) + 1) + (2 * H + 2)) + (H + 2) = 5 * H + 5 := by ring
  rw [← hTime]
  exact (hLoop.seq hEr0).seq hRew2

private def copyBitAct3 : Action 3 WorkSym :=
  mkAct2 0 1 (fun _ _ _ => .right)
    (fun inp _ _ => (bitSym (inp.getD false), .right))
    (fun _ _ s₁ => (s₁, .right))
    (fun _ _ _ => none)

private def copyHalfToTape0Block : Block 3 WorkSym :=
  ((Block.loop (fun _ sc => sc 2 == .u)
    (stepDirAct 2 .right) actStay
    ((Block.while1 (fun _ sc => sc 1 == .u) copyBitAct3 actStay).seq
      (rewindFromEnd 1))).seq
    (rewindFromEnd 0)).seq
    (rewindFromEnd 2)

private theorem Runs_copyHalfToTape0Block {w : List Bool} (m : Mem 3 WorkSym) (H b : ℕ)
    (hwLen : 2 * H * b ≤ w.length)
    (hIn : m.inPos = 0)
    (hB0 : m.work 0 = fun _ => .blank) (hP0 : m.workPos 0 = 0)
    (hT1 : m.work 1 = unaryTape b) (hP1 : m.workPos 1 = 0)
    (hT2 : m.work 2 = unaryTape H) (hP2 : m.workPos 2 = 0) :
    Runs copyHalfToTape0Block w m
      { m with
        inPos := ((H * b : ℕ) : Int)
        work  := fun i p => if i = 0 then wordTape (w.take (H * b)) p else m.work i p }
      (3 * H * b + 5 * H + 5) := by
  unfold copyHalfToTape0Block
  let outerInv (e : ℕ) : Mem 3 WorkSym :=
    { m with
      inPos   := ((e * b : ℕ) : Int)
      work    := fun i p => if i = 0 then wordTape (w.take (e * b)) p else m.work i p
      workPos := fun i =>
        if i = 0 then ((e * b : ℕ) : Int)
        else if i = 2 then (e : Int)
        else m.workPos i }
  have hOuter0 : outerInv 0 = m := by
    refine Mem.eq_of_fields ?_ (fun i p => ?_) (fun i => ?_) rfl
    · dsimp only [outerInv]; simp [hIn]
    · dsimp only [outerInv]
      fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Fin.reduceEq, ↓reduceIte]
      simp [wordTape_nil, hB0]
    · dsimp only [outerInv]
      fin_cases i <;> simp [hP0, hP1, hP2]
  have hLoop := Runs.loop (w := w)
    (fun _ (sc : Fin 3 → WorkSym) => sc 2 == .u)
    (stepDirAct 2 .right) actStay
    ((Block.while1 (fun _ sc => sc 1 == .u) copyBitAct3 actStay).seq (rewindFromEnd 1))
    (2 * b + 3) H outerInv
    (fun e he => by
      have hcell2 : ((outerInv e).work 2 ((outerInv e).workPos 2) == .u) = true := by
        dsimp only [outerInv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
        rw [hT2, unaryTape_lt he]; rfl
      refine ⟨hcell2, ?_⟩
      let innerInv (t : ℕ) : Mem 3 WorkSym :=
        { m with
          inPos   := ((e * b + t : ℕ) : Int)
          work    := fun i p => if i = 0 then wordTape (w.take (e * b + t)) p else m.work i p
          workPos := fun i =>
            if i = 0 then ((e * b + t : ℕ) : Int)
            else if i = 1 then (t : Int)
            else ((e + 1 : ℕ) : Int) }
      have hEnt : applyAct w (stepDirAct 2 .right) (outerInv e) = innerInv 0 := by
        unfold stepDirAct; rw [applyAct_mkAct1]
        refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
        · dsimp only [outerInv, innerInv]
          fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Fin.reduceEq, ↓reduceIte, Nat.add_zero]
          exact congrFun (ite_self_cell (m.work 2) _) p
        · dsimp only [outerInv, innerInv, Transpose.Dir.shift]
          fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Fin.reduceEq, ↓reduceIte]
          · rfl
          · exact hP1
          · omega
      rw [hEnt]
      have hW := Runs.while1 (w := w)
        (fun _ (sc : Fin 3 → WorkSym) => sc 1 == .u)
        copyBitAct3 actStay b innerInv
        (fun t ht => by
          have hcell1 : ((innerInv t).work 1 ((innerInv t).workPos 1) == .u) = true := by
            dsimp only [innerInv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
            rw [hT1, unaryTape_lt ht]; rfl
          refine ⟨hcell1, ?_⟩
          have hIdxLt : e * b + t < w.length := by
            have : e * b + t < (e + 1) * b := by ring_nf; omega
            have : (e + 1) * b ≤ 2 * H * b := Nat.mul_le_mul_right b (by omega)
            omega
          have hGet : w[e * b + t]? = some w[e * b + t] := List.getElem?_eq_getElem hIdxLt
          unfold copyBitAct3
          rw [applyAct_mkAct2 w (innerInv t) (by decide : (0 : Fin 3) ≠ 1)]
          refine Mem.eq_of_fields ?_ (fun i p => ?_) (fun i => ?_) rfl
          · dsimp only [innerInv, Transpose.Dir.shift]; omega
          · dsimp only [innerInv]
            fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Fin.reduceEq, ↓reduceIte]
            · rw [readInput_of_nonneg, hGet]
              dsimp only [Option.getD]
              exact congrFun (wordTape_take_succ hGet) p
            · exact congrFun (ite_self_cell (m.work 1) _) p
          · dsimp only [innerInv, Transpose.Dir.shift]
            fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Fin.reduceEq, ↓reduceIte] <;> omega)
        (by
          dsimp only [innerInv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
          rw [hT1, unaryTape_ge le_rfl]; rfl)
      rw [applyAct_actStay] at hW
      have hRew1 := Runs_rewindFromEnd (w := w) (1 : Fin 3) (innerInv b) b
        (by dsimp only [innerInv]; simp)
        (fun j hj => by dsimp only [innerInv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]; rw [hT1, unaryTape_lt hj]; decide)
        (by dsimp only [innerInv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]; rw [hT1]; exact unaryTape_neg (by omega))
      have hEndInner : { innerInv b with workPos := fun i => if i = 1 then 0 else (innerInv b).workPos i } =
          outerInv (e + 1) := by
        have hmul : e * b + b = (e + 1) * b := by ring
        refine Mem.eq_of_fields ?_ (fun i p => ?_) (fun i => ?_) rfl
        · dsimp only [innerInv, outerInv]; exact congrArg Nat.cast hmul
        · dsimp only [innerInv, outerInv]
          fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Fin.reduceEq, ↓reduceIte]
          rw [hmul]
        · dsimp only [innerInv, outerInv]
          fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Fin.reduceEq, ↓reduceIte]
          · exact congrArg Nat.cast hmul
          · exact hP1.symm
      rw [hEndInner] at hRew1
      have hTime : (b + 1) + (b + 2) = 2 * b + 3 := by omega
      rw [← hTime]
      exact hW.seq hRew1)
    (by
      dsimp only [outerInv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
      rw [hT2, unaryTape_ge le_rfl]; rfl)
  rw [hOuter0, applyAct_actStay] at hLoop
  have hHbLe : H * b ≤ w.length := by nlinarith
  have hHbLen : (w.take (H * b)).length = H * b := List.length_take_of_le hHbLe
  have hRew0 := Runs_rewindFromEnd (w := w) (0 : Fin 3) (outerInv H) (H * b)
    (by dsimp only [outerInv]; simp)
    (fun j hj => by
      dsimp only [outerInv]; simp only [Fin.isValue, ↓reduceIte]
      have hjLen : j < (w.take (H * b)).length := by omega
      rw [wordTape_lt (List.getElem?_eq_getElem hjLen)]
      exact bitSym_ne_blank _)
    (by dsimp only [outerInv]; simp only [Fin.isValue, ↓reduceIte]; exact wordTape_neg (by omega))
  let mAfter0 : Mem 3 WorkSym :=
    { outerInv H with workPos := fun i => if i = 0 then 0 else (outerInv H).workPos i }
  have hRew0Eq : { outerInv H with workPos := fun i => if i = 0 then 0 else (outerInv H).workPos i } =
      mAfter0 := rfl
  rw [hRew0Eq] at hRew0
  have hRew2 := Runs_rewindFromEnd (w := w) (2 : Fin 3) mAfter0 H
    (by dsimp only [mAfter0, outerInv]; simp)
    (fun j hj => by dsimp only [mAfter0, outerInv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]; rw [hT2, unaryTape_lt hj]; decide)
    (by dsimp only [mAfter0, outerInv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]; rw [hT2]; exact unaryTape_neg (by omega))
  have hEnd : { mAfter0 with workPos := fun i => if i = 2 then 0 else mAfter0.workPos i } =
      { m with
        inPos := ((H * b : ℕ) : Int)
        work  := fun i p => if i = 0 then wordTape (w.take (H * b)) p else m.work i p } := by
    refine Mem.eq_of_fields rfl (fun _ _ => rfl) (fun i => ?_) rfl
    dsimp only [mAfter0, outerInv]
    fin_cases i <;> simp [hP0, hP1, hP2]
  rw [hEnd] at hRew2
  have hTime : ((H * (1 + (2 * b + 3)) + 1) + (H * b + 2)) + (H + 2) =
      3 * H * b + 5 * H + 5 := by ring
  rw [← hTime]
  exact (hLoop.seq hRew0).seq hRew2

private def emitTape0Act3 : Action 3 WorkSym :=
  mkAct2 0 1 (fun _ _ _ => .stay)
    (fun _ s₀ _ => (s₀, .right)) (fun _ _ s₁ => (s₁, .right))
    (fun _ s₀ _ => symBit s₀)

private def emitInputAct3 : Action 3 WorkSym :=
  mkAct1 1 (fun _ _ => .right) (fun _ s₁ => (s₁, .right)) (fun inp _ => inp)

private def riffleInterleaveBlock : Block 3 WorkSym :=
  Block.loop (fun _ sc => sc 2 == .u)
    (stepDirAct 2 .right) actStay
    (((Block.while1 (fun _ sc => sc 1 == .u) emitTape0Act3 actStay).seq (rewindFromEnd 1)).seq
      ((Block.while1 (fun _ sc => sc 1 == .u) emitInputAct3 actStay).seq (rewindFromEnd 1)))

private theorem take_succ_of_getElem?_tm {α : Type*} {xs : List α} {i : ℕ} {x : α}
    (h : xs[i]? = some x) :
    xs.take (i + 1) = xs.take i ++ [x] := by
  have hi : i < xs.length := by
    by_contra hge
    rw [List.getElem?_eq_none (Nat.le_of_not_gt hge)] at h
    cases h
  rw [List.take_add_one, h]
  rfl

private theorem Runs_riffleInterleaveBlock {m' : ℕ} (A : Transpose.Matrix)
    (m : Mem 3 WorkSym) :
    let mExp := m' + 1
    let d := 2 ^ mExp
    let b := Transpose.entryBits d
    let H := 2 * 4 ^ m'
    let w := Transpose.encode d b A
    let out := Transpose.encode d b (stoneShuffleTMMatrix mExp A)
    m.inPos = ((H * b : ℕ) : Int) →
    m.work 0 = wordTape (w.take (H * b)) → m.workPos 0 = 0 →
    m.work 1 = unaryTape b → m.workPos 1 = 0 →
    m.work 2 = unaryTape H → m.workPos 2 = 0 →
    m.outRev = [] →
    ∃ mHalt : Mem 3 WorkSym,
      Runs riffleInterleaveBlock w m mHalt (H * (4 * b + 7) + 1) ∧
      mHalt.outRev.reverse = out := by
  intro mExp d b H w out hIn hT0 hP0 hT1 hP1 hT2 hP2 hOut0
  unfold riffleInterleaveBlock
  have hdd : d * d = 2 * H := by
    have hd_eq : d = 2 * 2 ^ m' := by dsimp [d, mExp]; rw [pow_succ']
    dsimp [H]; rw [hd_eq]
    calc (2 * 2 ^ m') * (2 * 2 ^ m') = 2 * (2 * (2 ^ m' * 2 ^ m')) := by ring
      _ = 2 * (2 * (2 * 2) ^ m') := by rw [Nat.mul_pow 2 2 m']
      _ = 2 * (2 * 4 ^ m') := rfl
  have hwLen : w.length = 2 * H * b := by
    rw [(encode_len_get d b A).1, hdd]
  have houtLen : out.length = 2 * H * b := by
    rw [(encode_len_get d b (stoneShuffleTMMatrix mExp A)).1, hdd]
  let outerInv (q : ℕ) : Mem 3 WorkSym :=
    { m with
      inPos   := (((H + q) * b : ℕ) : Int)
      workPos := fun i =>
        if i = 0 then ((q * b : ℕ) : Int)
        else if i = 2 then (q : Int)
        else m.workPos i
      outRev  := (out.take (2 * q * b)).reverse }
  have hOuter0 : outerInv 0 = m := by
    refine Mem.eq_of_fields ?_ (fun _ _ => rfl) (fun i => ?_) ?_
    · dsimp only [outerInv]; rw [Nat.add_zero, hIn]
    · dsimp only [outerInv]; fin_cases i <;> simp [hP0, hP1, hP2]
    · dsimp only [outerInv]; simp [hOut0]
  have hLoop := Runs.loop (w := w)
    (fun _ (sc : Fin 3 → WorkSym) => sc 2 == .u)
    (stepDirAct 2 .right) actStay _ (4 * b + 6) H outerInv
    (fun q hq => by
      have hcell2 : ((outerInv q).work 2 ((outerInv q).workPos 2) == .u) = true := by
        dsimp only [outerInv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
        rw [hT2, unaryTape_lt hq]; rfl
      refine ⟨hcell2, ?_⟩
      -- Phase A: emit `b` bits from Tape 0 (`e = 2 * q`)
      let invA (t : ℕ) : Mem 3 WorkSym :=
        { m with
          inPos   := (((H + q) * b : ℕ) : Int)
          workPos := fun i =>
            if i = 0 then ((q * b + t : ℕ) : Int)
            else if i = 1 then (t : Int)
            else ((q + 1 : ℕ) : Int)
          outRev  := (out.take ((2 * q) * b + t)).reverse }
      have hEnt : applyAct w (stepDirAct 2 .right) (outerInv q) = invA 0 := by
        unfold stepDirAct; rw [applyAct_mkAct1]
        refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) ?_
        · dsimp only [outerInv, invA]
          fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Fin.reduceEq, ↓reduceIte]
          exact congrFun (ite_self_cell (m.work 2) _) p
        · dsimp only [outerInv, invA, Transpose.Dir.shift]
          fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Fin.reduceEq, ↓reduceIte]
          · rfl
          · exact hP1
          · omega
        · dsimp only [outerInv, invA, Nat.add_zero]
      rw [hEnt]
      have hWA := Runs.while1 (w := w)
        (fun _ (sc : Fin 3 → WorkSym) => sc 1 == .u)
        emitTape0Act3 actStay b invA
        (fun t ht => by
          have hcell1 : ((invA t).work 1 ((invA t).workPos 1) == .u) = true := by
            dsimp only [invA]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
            rw [hT1, unaryTape_lt ht]; rfl
          refine ⟨hcell1, ?_⟩
          have hqbLt : q * b + t < H * b := by
            calc q * b + t < q * b + b := by omega
              _ = (q + 1) * b := by ring
              _ ≤ H * b := Nat.mul_le_mul_right b (by omega)
          have hwLt : q * b + t < w.length := by nlinarith [hwLen, hqbLt]
          have hTakeGet : (w.take (H * b))[q * b + t]? = some w[q * b + t] := by
            rw [List.getElem?_take_of_lt hqbLt, List.getElem?_eq_getElem hwLt]
          have hShufBit : out[(2 * q) * b + t]? = some w[q * b + t] := by
            have h := stoneShuffle_encode_bit (m' := m') A (2 * q) (by omega) t ht
            have hmod : (2 * q) % 2 = 0 := by omega
            have hdiv : (2 * q) / 2 = q := by omega
            change out[(2 * q) * b + t]? = w[((2 * q) % 2 * H + (2 * q) / 2) * b + t]? at h
            rw [hmod, hdiv, Nat.zero_mul, Nat.zero_add] at h
            rw [h, List.getElem?_eq_getElem hwLt]
          unfold emitTape0Act3
          rw [applyAct_mkAct2 w (invA t) (by decide : (0 : Fin 3) ≠ 1)]
          refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) ?_
          · dsimp only [invA]
            fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Fin.reduceEq, ↓reduceIte]
            · exact congrFun (ite_self_cell (m.work 0) _) p
            · exact congrFun (ite_self_cell (m.work 1) _) p
          · dsimp only [invA, Transpose.Dir.shift]
            fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Fin.reduceEq, ↓reduceIte] <;> omega
          · dsimp only [invA]
            simp only [Fin.isValue, ↓reduceIte]
            rw [hT0, wordTape_lt hTakeGet, symBit_bitSym]
            have htk := take_succ_of_getElem?_tm hShufBit
            have hidxEq : (2 * q) * b + (t + 1) = (2 * q) * b + t + 1 := by omega
            rw [hidxEq, htk, List.reverse_append, List.reverse_singleton]
            rfl)
        (by
          dsimp only [invA]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
          rw [hT1, unaryTape_ge le_rfl]; rfl)
      rw [applyAct_actStay] at hWA
      have hRewA := Runs_rewindFromEnd (w := w) (1 : Fin 3) (invA b) b
        (by dsimp only [invA]; simp)
        (fun j hj => by dsimp only [invA]; rw [hT1, unaryTape_lt hj]; decide)
        (by dsimp only [invA]; rw [hT1]; exact unaryTape_neg (by omega))
      -- Phase B: emit `b` bits from `inPos` (`e = 2 * q + 1`)
      let invB (t : ℕ) : Mem 3 WorkSym :=
        { m with
          inPos   := (((H + q) * b + t : ℕ) : Int)
          workPos := fun i =>
            if i = 0 then (((q + 1) * b : ℕ) : Int)
            else if i = 1 then (t : Int)
            else ((q + 1 : ℕ) : Int)
          outRev  := (out.take ((2 * q + 1) * b + t)).reverse }
      have hMidAB : { invA b with workPos := fun i => if i = 1 then 0 else (invA b).workPos i } =
          invB 0 := by
        have h1 : q * b + b = (q + 1) * b := by ring
        have h2 : (2 * q) * b + b = (2 * q + 1) * b := by ring
        refine Mem.eq_of_fields rfl (fun _ _ => rfl) (fun i => ?_) ?_
        · dsimp only [invA, invB]
          fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Fin.reduceEq, ↓reduceIte, Nat.cast_zero]
          exact congrArg Nat.cast h1
        · dsimp only [invA, invB, Nat.add_zero]; rw [h2]
      rw [hMidAB] at hRewA
      have hWB := Runs.while1 (w := w)
        (fun _ (sc : Fin 3 → WorkSym) => sc 1 == .u)
        emitInputAct3 actStay b invB
        (fun t ht => by
          have hcell1 : ((invB t).work 1 ((invB t).workPos 1) == .u) = true := by
            dsimp only [invB]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
            rw [hT1, unaryTape_lt ht]; rfl
          refine ⟨hcell1, ?_⟩
          have hwLt : (H + q) * b + t < w.length := by
            have : (H + q) * b + t < (H + q + 1) * b := by ring_nf; omega
            have : (H + q + 1) * b ≤ 2 * H * b := Nat.mul_le_mul_right b (by omega)
            omega
          have hShufBit : out[(2 * q + 1) * b + t]? = some w[(H + q) * b + t] := by
            have h := stoneShuffle_encode_bit (m' := m') A (2 * q + 1) (by omega) t ht
            have hmod : (2 * q + 1) % 2 = 1 := by omega
            have hdiv : (2 * q + 1) / 2 = q := by omega
            change out[(2 * q + 1) * b + t]? = w[((2 * q + 1) % 2 * H + (2 * q + 1) / 2) * b + t]? at h
            rw [hmod, hdiv, Nat.one_mul] at h
            rw [h, List.getElem?_eq_getElem hwLt]
          unfold emitInputAct3
          rw [applyAct_mkAct1]
          refine Mem.eq_of_fields ?_ (fun i p => ?_) (fun i => ?_) ?_
          · dsimp only [invB, Transpose.Dir.shift]; omega
          · dsimp only [invB]
            fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Fin.reduceEq, ↓reduceIte]
            exact congrFun (ite_self_cell (m.work 1) _) p
          · dsimp only [invB, Transpose.Dir.shift]
            fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Fin.reduceEq, ↓reduceIte]; omega
          · dsimp only [invB]
            rw [readInput_of_nonneg, List.getElem?_eq_getElem hwLt]
            have htk := take_succ_of_getElem?_tm hShufBit
            have hidxEq : (2 * q + 1) * b + (t + 1) = (2 * q + 1) * b + t + 1 := by omega
            rw [hidxEq, htk, List.reverse_append, List.reverse_singleton]
            rfl)
        (by
          dsimp only [invB]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
          rw [hT1, unaryTape_ge le_rfl]; rfl)
      rw [applyAct_actStay] at hWB
      have hRewB := Runs_rewindFromEnd (w := w) (1 : Fin 3) (invB b) b
        (by dsimp only [invB]; simp)
        (fun j hj => by dsimp only [invB]; rw [hT1, unaryTape_lt hj]; decide)
        (by dsimp only [invB]; rw [hT1]; exact unaryTape_neg (by omega))
      have hEndB : { invB b with workPos := fun i => if i = 1 then 0 else (invB b).workPos i } =
          outerInv (q + 1) := by
        have h1 : (H + q) * b + b = (H + (q + 1)) * b := by ring
        have h2 : (2 * q + 1) * b + b = 2 * (q + 1) * b := by ring
        refine Mem.eq_of_fields ?_ (fun _ _ => rfl) (fun i => ?_) ?_
        · dsimp only [invB, outerInv]; exact congrArg Nat.cast h1
        · dsimp only [invB, outerInv]
          fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Fin.reduceEq, ↓reduceIte]
          exact hP1.symm
        · dsimp only [invB, outerInv]; rw [h2]
      rw [hEndB] at hRewB
      have hTime : ((b + 1) + (b + 2)) + ((b + 1) + (b + 2)) = 4 * b + 6 := by omega
      rw [← hTime]
      exact (hWA.seq hRewA).seq (hWB.seq hRewB))
    (by
      dsimp only [outerInv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
      rw [hT2, unaryTape_ge le_rfl]; rfl)
  rw [hOuter0, applyAct_actStay] at hLoop
  have hTimeEq : H * (1 + (4 * b + 6)) + 1 = H * (4 * b + 7) + 1 := by ring
  rw [hTimeEq] at hLoop
  refine ⟨outerInv H, hLoop, ?_⟩
  dsimp only [outerInv]
  rw [List.reverse_reverse, List.take_of_length_le (by omega)]

private def stoneShuffleProg : Block 3 WorkSym :=
  (((discoverEntryBits 0 1).seq halveUnaryBlock).seq copyHalfToTape0Block).seq
    riffleInterleaveBlock

private theorem stoneShuffleTM_linear :
    ∃ (M_shuf : Transpose.TM) (C_shuf : ℕ),
      ∀ (m : ℕ) (A : Transpose.Matrix), 1 ≤ m →
        let d := 2 ^ m
        Transpose.ComputesWithin M_shuf
          (Transpose.encode d (Transpose.entryBits d) A)
          (Transpose.encode d (Transpose.entryBits d) (stoneShuffleTMMatrix m A))
          (C_shuf * Transpose.inputLength d) := by
  refine ⟨stoneShuffleProg.toTM encWorkSym decWorkSym, 150, ?_⟩
  intro m A hm
  obtain ⟨m', rfl⟩ := Nat.exists_eq_add_of_le' hm
  set mExp := m' + 1
  set d := 2 ^ mExp
  set b := Transpose.entryBits d
  set H := 2 * 4 ^ m'
  set L := Transpose.inputLength d
  set w := Transpose.encode d b A
  have hd1 : 1 ≤ d := Nat.two_pow_pos mExp
  have hbEq : b = mExp := entryBits_two_pow hm
  have hb1 : 1 ≤ b := entryBits_pos_tm d
  have hH1 : 1 ≤ H := by dsimp [H]; have := Nat.one_le_pow m' 4 (by decide); omega
  have h4b : 4 ^ b = 2 * H := by
    rw [hbEq]; dsimp [mExp, H]
    rw [pow_succ']
    ring
  have hdd : d * d = 2 * H := by
    have hd_eq : d = 2 * 2 ^ m' := by dsimp [d, mExp]; rw [pow_succ']
    dsimp [H]; rw [hd_eq]
    calc (2 * 2 ^ m') * (2 * 2 ^ m') = 2 * (2 * (2 ^ m' * 2 ^ m')) := by ring
      _ = 2 * (2 * (2 * 2) ^ m') := by rw [Nat.mul_pow 2 2 m']
      _ = 2 * (2 * 4 ^ m') := rfl
  have hL_eq : L = 2 * H * b := by
    dsimp [L, Transpose.inputLength, b]; rw [hdd]
  have hL1 : 1 ≤ L := inputLength_pos hd1
  have hwLen : w.length = L := (encode_len_get d b A).1
  let m0 : Mem 3 WorkSym :=
    { inPos := 0, work := fun _ _ => .blank, workPos := fun _ => 0, outRev := [] }
  -- 1. `discoverEntryBits 0 1`
  have r1 := Runs_discoverEntryBits (k := 3) (t₀ := 0) (t₁ := 1) (by decide) hd1 hwLen
    m0 rfl rfl rfl rfl rfl
  change Runs (discoverEntryBits 0 1) w m0 _ (120 * L) at r1
  rw [h4b] at r1
  let m1 : Mem 3 WorkSym :=
    { m0 with
      work := fun i p =>
        if i = 0 then unaryTape (2 * H) p
        else if i = 1 then unaryTape b p
        else .blank }
  have hm1Eq : { m0 with
      work := fun i p =>
        if i = 0 then unaryTape (2 * H) p
        else if i = 1 then unaryTape b p
        else m0.work i p } = m1 := rfl
  rw [hm1Eq] at r1
  -- 2. `halveUnaryBlock`
  have r2 := Runs_halveUnaryBlock (w := w) m1 H rfl rfl rfl rfl
  let m2 : Mem 3 WorkSym :=
    { m0 with
      work := fun i p =>
        if i = 0 then .blank
        else if i = 1 then unaryTape b p
        else unaryTape H p }
  have hm2Eq : { m1 with
      work := fun i p =>
        if i = 0 then .blank
        else if i = 2 then unaryTape H p
        else m1.work i p } = m2 := by
    refine Mem.eq_of_fields rfl (fun i p => ?_) (fun _ => rfl) rfl
    fin_cases i <;> rfl
  rw [hm2Eq] at r2
  -- 3. `copyHalfToTape0Block`
  have h2Hb_le_w : 2 * H * b ≤ w.length := by rw [hwLen, hL_eq]
  have r3 := Runs_copyHalfToTape0Block (w := w) m2 H b h2Hb_le_w rfl rfl rfl rfl rfl rfl rfl
  let m3 : Mem 3 WorkSym :=
    { m0 with
      inPos := ((H * b : ℕ) : Int)
      work  := fun i p =>
        if i = 0 then wordTape (w.take (H * b)) p
        else if i = 1 then unaryTape b p
        else unaryTape H p }
  have hm3Eq : { m2 with
      inPos := ((H * b : ℕ) : Int)
      work  := fun i p => if i = 0 then wordTape (w.take (H * b)) p else m2.work i p } = m3 := by
    refine Mem.eq_of_fields rfl (fun i p => ?_) (fun _ => rfl) rfl
    fin_cases i <;> rfl
  rw [hm3Eq] at r3
  -- 4. `riffleInterleaveBlock`
  obtain ⟨mHalt, r4, hOut⟩ := Runs_riffleInterleaveBlock (m' := m') A m3
    rfl rfl rfl rfl rfl rfl rfl rfl
  change Runs riffleInterleaveBlock w m3 mHalt (H * (4 * b + 7) + 1) at r4
  change mHalt.outRev.reverse = Transpose.encode d b (stoneShuffleTMMatrix mExp A) at hOut
  have rTotal : Runs stoneShuffleProg w m0 mHalt (150 * L) := by
    unfold stoneShuffleProg
    apply (((r1.seq r2).seq r3).seq r4).of_le
    have hL2 : L = 2 * (H * b) := by rw [hL_eq]; ring
    have hH_le : H ≤ H * b := Nat.le_mul_of_pos_right H hb1
    nlinarith
  exact Block.computesWithin .blank encWorkSym decWorkSym decWorkSym_encWorkSym encWorkSym_blank
    stoneShuffleProg rTotal hOut

/-! ### 5. Theorem 7 Part 2: `O(L)` `2`-Work-Tape Turing Machine for Within-Row Shear -/

/-- Clear `unaryTape N` on tape `t₀` (`pos = 0 → 0`) in `2 * N + 3` steps. -/
private def clearUnary {k : ℕ} (t₀ : Fin k) : Block k WorkSym :=
  (Block.while1 (fun _ sc => sc t₀ == .u) (stepDirAct t₀ .right) actStay).seq
    (eraseFromEnd t₀)

private theorem Runs_clearUnary {k : ℕ} {w : List Bool} (t₀ : Fin k)
    (m : Mem k WorkSym) (N : ℕ)
    (hT : m.work t₀ = unaryTape N) (hP : m.workPos t₀ = 0) :
    Runs (clearUnary t₀) w m
      { m with work := fun i p => if i = t₀ then .blank else m.work i p }
      (2 * N + 3) := by
  unfold clearUnary
  let inv (j : ℕ) : Mem k WorkSym :=
    { m with workPos := fun i => if i = t₀ then (j : Int) else m.workPos i }
  have hInv0 : inv 0 = m := by
    refine Mem.eq_of_fields rfl (fun _ _ => rfl) (fun i => ?_) rfl
    dsimp only [inv]; by_cases hi : i = t₀ <;> simp [hi, hP]
  have hW := Runs.while1 (w := w)
    (fun _ (sc : Fin k → WorkSym) => sc t₀ == .u)
    (stepDirAct t₀ .right) actStay N inv
    (fun j hj => by
      have hcell : ((inv j).work t₀ ((inv j).workPos t₀) == .u) = true := by
        dsimp only [inv]; simp only [↓reduceIte]; rw [hT, unaryTape_lt hj]; rfl
      refine ⟨hcell, ?_⟩
      unfold stepDirAct; rw [applyAct_mkAct1]
      refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
      · dsimp only [inv]
        by_cases hi : i = t₀
        · subst hi; simp only [↓reduceIte]; exact congrFun (ite_self_cell (m.work i) _) p
        · simp [hi]
      · dsimp only [inv, Transpose.Dir.shift]
        by_cases hi : i = t₀
        · subst hi; simp only [↓reduceIte]; omega
        · simp [hi])
    (by dsimp only [inv]; simp only [↓reduceIte]; rw [hT, unaryTape_ge le_rfl]; rfl)
  rw [hInv0, applyAct_actStay] at hW
  have hEr := Runs_eraseFromEnd (w := w) t₀ (inv N) N
    (by dsimp only [inv]; simp only [↓reduceIte])
    (fun j hj => by dsimp only [inv]; rw [hT, unaryTape_lt hj]; decide)
    (fun p hp => by
      dsimp only [inv]; rw [hT]
      rcases hp with hneg | hge
      · exact unaryTape_neg hneg
      · exact unaryTape_ge hge)
  have hEnd :
      { inv N with
        work    := fun i p => if i = t₀ then WorkSym.blank else (inv N).work i p
        workPos := fun i => if i = t₀ then 0 else (inv N).workPos i } =
      { m with work := fun i p => if i = t₀ then .blank else m.work i p } := by
    refine Mem.eq_of_fields rfl (fun _ _ => rfl) (fun i => ?_) rfl
    dsimp only [inv]; by_cases hi : i = t₀ <;> simp [hi, hP]
  rw [hEnd] at hEr
  have hTime : (N + 1) + (N + 2) = 2 * N + 3 := by omega
  rw [← hTime]
  exact hW.seq hEr

private def divAdvanceAct : Action 2 WorkSym :=
  mkAct1 1 (fun _ _ => .right) (fun _ s₁ => (s₁, .right)) (fun _ _ => none)

/-- Divide `w.length = Q * b` by `b` (`unaryTape b` on Tape 1) to write `unaryTape Q` on Tape 0. -/
private def divInputByB : Block 2 WorkSym :=
  ((Block.loop (fun inp _ => inp.isSome)
    (writeDirAct 0 .u .right) actStay
    ((Block.while1 (fun _ sc => sc 1 == .u) divAdvanceAct actStay).seq
      (rewindFromEnd 1))).seq
    rewindInputFromPos).seq
    (rewindFromEnd 0)

private theorem Runs_divInputByB {w : List Bool} (m : Mem 2 WorkSym) (Q b : ℕ)
    (hb1 : 1 ≤ b) (hwLen : w.length = Q * b)
    (hIn : m.inPos = 0)
    (hB0 : m.work 0 = fun _ => .blank) (hP0 : m.workPos 0 = 0)
    (hT1 : m.work 1 = unaryTape b) (hP1 : m.workPos 1 = 0) :
    Runs divInputByB w m
      { m with work := fun i p => if i = 0 then unaryTape Q p else m.work i p }
      (3 * Q * b + 5 * Q + 5) := by
  unfold divInputByB
  let outerInv (q : ℕ) : Mem 2 WorkSym :=
    { m with
      inPos   := ((q * b : ℕ) : Int)
      work    := fun i p => if i = 0 then unaryTape q p else m.work i p
      workPos := fun i => if i = 0 then (q : Int) else m.workPos i }
  have hOuter0 : outerInv 0 = m := by
    refine Mem.eq_of_fields ?_ (fun i p => ?_) (fun i => ?_) rfl
    · dsimp only [outerInv]; simp [hIn]
    · dsimp only [outerInv]
      fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]
      rw [unaryTape_zero, hB0]
    · dsimp only [outerInv]
      fin_cases i <;> simp [hP0, hP1]
  have hLoop := Runs.loop (w := w)
    (fun inp (_ : Fin 2 → WorkSym) => inp.isSome)
    (writeDirAct 0 .u .right) actStay
    ((Block.while1 (fun _ sc => sc 1 == .u) divAdvanceAct actStay).seq (rewindFromEnd 1))
    (2 * b + 3) Q outerInv
    (fun q hq => by
      have hqbLt : q * b < w.length := by
        have : (q + 1) * b ≤ Q * b := Nat.mul_le_mul_right b (by omega)
        have : q * b < (q + 1) * b := by ring_nf; omega
        omega
      have hCond : (Transpose.readInput w (outerInv q).inPos).isSome = true := by
        dsimp only [outerInv]
        rw [readInput_of_nonneg, List.getElem?_eq_getElem hqbLt]; rfl
      refine ⟨hCond, ?_⟩
      let innerInv (t : ℕ) : Mem 2 WorkSym :=
        { m with
          inPos   := ((q * b + t : ℕ) : Int)
          work    := fun i p => if i = 0 then unaryTape (q + 1) p else m.work i p
          workPos := fun i => if i = 0 then ((q + 1 : ℕ) : Int) else (t : Int) }
      have hEnt : applyAct w (writeDirAct 0 .u .right) (outerInv q) = innerInv 0 := by
        unfold writeDirAct; rw [applyAct_mkAct1]
        refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
        · dsimp only [outerInv, innerInv]
          fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]
          exact congrFun (unaryTape_write_end q) p
        · dsimp only [outerInv, innerInv, Transpose.Dir.shift]
          fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]
          · omega
          · exact hP1
      rw [hEnt]
      have hW := Runs.while1 (w := w)
        (fun _ (sc : Fin 2 → WorkSym) => sc 1 == .u)
        divAdvanceAct actStay b innerInv
        (fun t ht => by
          have hcell1 : ((innerInv t).work 1 ((innerInv t).workPos 1) == .u) = true := by
            dsimp only [innerInv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
            rw [hT1, unaryTape_lt ht]; rfl
          refine ⟨hcell1, ?_⟩
          unfold divAdvanceAct; rw [applyAct_mkAct1]
          refine Mem.eq_of_fields ?_ (fun i p => ?_) (fun i => ?_) rfl
          · dsimp only [innerInv, Transpose.Dir.shift]; omega
          · dsimp only [innerInv]
            fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]
            exact congrFun (ite_self_cell (m.work 1) _) p
          · dsimp only [innerInv, Transpose.Dir.shift]
            fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]; omega)
        (by
          dsimp only [innerInv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
          rw [hT1, unaryTape_ge le_rfl]; rfl)
      rw [applyAct_actStay] at hW
      have hRew1 := Runs_rewindFromEnd (w := w) (1 : Fin 2) (innerInv b) b
        (by dsimp only [innerInv]; simp)
        (fun j hj => by dsimp only [innerInv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]; rw [hT1, unaryTape_lt hj]; decide)
        (by dsimp only [innerInv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]; rw [hT1]; exact unaryTape_neg (by omega))
      have hEndInner :
          { innerInv b with workPos := fun i => if i = 1 then 0 else (innerInv b).workPos i } =
          outerInv (q + 1) := by
        have hmul : q * b + b = (q + 1) * b := by ring
        refine Mem.eq_of_fields ?_ (fun _ _ => rfl) (fun i => ?_) rfl
        · dsimp only [innerInv, outerInv]; exact congrArg Nat.cast hmul
        · dsimp only [innerInv, outerInv]
          fin_cases i <;> simp [hP1]
      rw [hEndInner] at hRew1
      have hTime : (b + 1) + (b + 2) = 2 * b + 3 := by omega
      rw [← hTime]
      exact hW.seq hRew1)
    (by
      dsimp only [outerInv]
      rw [readInput_of_nonneg, List.getElem?_eq_none (by omega)]; rfl)
  rw [hOuter0, applyAct_actStay] at hLoop
  have hRewIn := Runs_rewindInputFromPos (w := w) (outerInv Q) (Q * b) rfl (by omega)
  let mAfterIn : Mem 2 WorkSym := { outerInv Q with inPos := 0 }
  have hInEq : { outerInv Q with inPos := 0 } = mAfterIn := rfl
  rw [hInEq] at hRewIn
  have hRew0 := Runs_rewindFromEnd (w := w) (0 : Fin 2) mAfterIn Q
    (by dsimp only [mAfterIn, outerInv]; simp)
    (fun j hj => by dsimp only [mAfterIn, outerInv]; simp only [Fin.isValue, ↓reduceIte]; rw [unaryTape_lt hj]; decide)
    (by dsimp only [mAfterIn, outerInv]; simp only [Fin.isValue, ↓reduceIte]; exact unaryTape_neg (by omega))
  have hEnd :
      { mAfterIn with workPos := fun i => if i = 0 then 0 else mAfterIn.workPos i } =
      { m with work := fun i p => if i = 0 then unaryTape Q p else m.work i p } := by
    refine Mem.eq_of_fields hIn.symm (fun _ _ => rfl) (fun i => ?_) rfl
    dsimp only [mAfterIn, outerInv]
    fin_cases i <;> simp [hP0, hP1]
  rw [hEnd] at hRew0
  have hTime : ((Q * (1 + (2 * b + 3)) + 1) + (Q * b + 2)) + (Q + 2) =
      3 * Q * b + 5 * Q + 5 := by ring
  rw [← hTime]
  exact (hLoop.seq hRewIn).seq hRew0

/-- Tape 1 scratch layout during `unarySqrt` and `buildRowTemplate`:
for `k = 0`, `oddScratch b 0 = unaryTape b`; for `k ≥ 1`, `-1` holds `.wall`,
`[-2k, -2]` holds `.oddD` at even cells and `.oddAux` at odd cells, `< -2k` is `.blank`,
and `[0, ∞)` holds `unaryTape b`. -/
private def oddScratch (b k : ℕ) : Int → WorkSym :=
  fun p =>
    if 1 ≤ k ∧ p = -1 then .wall
    else if -2 * (k : Int) ≤ p ∧ p ≤ -2 then
      if p % 2 = 0 then .oddD else .oddAux
    else unaryTape b p

private theorem oddScratch_zero (b : ℕ) : oddScratch b 0 = unaryTape b := by
  funext p; unfold oddScratch
  split_ifs <;> first | rfl | omega

private theorem oddScratch_init (b : ℕ) :
    (fun p : Int =>
      if p = -2 then WorkSym.oddD
      else if p = -1 then WorkSym.wall
      else unaryTape b p) = oddScratch b 1 := by
  funext p; unfold oddScratch
  by_cases hp2 : p = -2
  · subst hp2; simp
  · by_cases hp1 : p = -1
    · subst hp1; simp
    · have h1 : ¬ (1 ≤ 1 ∧ p = -1) := by omega
      have h2 : ¬ (-2 * ((1 : ℕ) : Int) ≤ p ∧ p ≤ -2) := by omega
      rw [ite_eq_right hp2, ite_eq_right hp1, ite_eq_right h1, ite_eq_right h2]

private theorem oddScratch_wall {b k : ℕ} (hk : 1 ≤ k) :
    oddScratch b k (-1) = .wall := by
  unfold oddScratch; simp [hk]

private theorem oddScratch_mid_ne_blank {b k : ℕ} {p : Int}
    (hlo : -2 * (k : Int) ≤ p) (hhi : p ≤ -2) :
    oddScratch b k p ≠ .blank := by
  unfold oddScratch
  have hnot1 : ¬ (1 ≤ k ∧ p = -1) := by omega
  have hmid : -2 * (k : Int) ≤ p ∧ p ≤ -2 := ⟨hlo, hhi⟩
  rw [ite_eq_right hnot1, ite_eq_left hmid]
  split_ifs <;> decide

private theorem oddScratch_mid_ne_wall {b k : ℕ} {p : Int}
    (hlo : -2 * (k : Int) ≤ p) (hhi : p ≤ -2) :
    oddScratch b k p ≠ .wall := by
  unfold oddScratch
  have hnot1 : ¬ (1 ≤ k ∧ p = -1) := by omega
  have hmid : -2 * (k : Int) ≤ p ∧ p ≤ -2 := ⟨hlo, hhi⟩
  rw [ite_eq_right hnot1, ite_eq_left hmid]
  split_ifs <;> decide

private theorem oddScratch_lt_blank (b k : ℕ) {p : Int}
    (hlt : p < -2 * (k : Int)) (h1 : ¬ (1 ≤ k ∧ p = -1)) (hneg : p < 0) :
    oddScratch b k p = .blank := by
  unfold oddScratch
  have h2 : ¬ (-2 * (k : Int) ≤ p ∧ p ≤ -2) := by omega
  rw [ite_eq_right h1, ite_eq_right h2]
  exact unaryTape_neg hneg

private theorem oddScratch_nonneg (b k : ℕ) {p : Int} (hp : 0 ≤ p) :
    oddScratch b k p = unaryTape b p := by
  unfold oddScratch
  have h1 : ¬ (1 ≤ k ∧ p = -1) := by omega
  have h2 : ¬ (-2 * (k : Int) ≤ p ∧ p ≤ -2) := by omega
  rw [ite_eq_right h1, ite_eq_right h2]

private theorem oddScratch_left_end {b k : ℕ} (hk : 1 ≤ k) :
    oddScratch b k (-2 * (k : Int)) = .oddD := by
  unfold oddScratch
  have h1 : ¬ (1 ≤ k ∧ -2 * (k : Int) = -1) := by omega
  have h2 : -2 * (k : Int) ≤ -2 * (k : Int) ∧ -2 * (k : Int) ≤ -2 := by omega
  have h3 : (-2 * (k : Int)) % 2 = 0 := by omega
  rw [ite_eq_right h1, ite_eq_left h2, ite_eq_left h3]

private theorem oddScratch_neg_ne_u (b k : ℕ) {p : Int}
    (hlo : -2 * (k : Int) ≤ p) (hneg : p < 0) :
    oddScratch b k p ≠ .u := by
  have hk1 : 1 ≤ k := by omega
  by_cases hp1 : p = -1
  · subst hp1; rw [oddScratch_wall hk1]; decide
  · unfold oddScratch
    have h1 : ¬ (1 ≤ k ∧ p = -1) := by omega
    have h2 : -2 * (k : Int) ≤ p ∧ p ≤ -2 := by omega
    rw [ite_eq_right h1, ite_eq_left h2]
    split_ifs <;> decide

private theorem oddScratch_extend {b k : ℕ} (hk : 1 ≤ k) :
    (fun p : Int =>
      if p = -2 * ((k + 1 : ℕ) : Int) then WorkSym.oddD
      else if p = -2 * (k : Int) - 1 then WorkSym.oddAux
      else oddScratch b k p) = oddScratch b (k + 1) := by
  funext p
  by_cases hpD : p = -2 * ((k + 1 : ℕ) : Int)
  · subst hpD
    simp only [↓reduceIte]
    exact (oddScratch_left_end (by omega : 1 ≤ k + 1)).symm
  · by_cases hpA : p = -2 * (k : Int) - 1
    · subst hpA
      simp only [hpD, ↓reduceIte]
      unfold oddScratch
      have h1 : ¬ (1 ≤ k + 1 ∧ -2 * (k : Int) - 1 = -1) := by omega
      have h2 : -2 * ((k + 1 : ℕ) : Int) ≤ -2 * (k : Int) - 1 ∧ -2 * (k : Int) - 1 ≤ -2 := by omega
      have h3 : ¬ ((-2 * (k : Int) - 1) % 2 = 0) := by omega
      rw [ite_eq_right h1, ite_eq_left h2, ite_eq_right h3]
    · simp only [hpD, hpA, ↓reduceIte]
      unfold oddScratch
      by_cases h1 : p = -1
      · subst h1; simp [hk]
      · have hn1 : ¬ (1 ≤ k ∧ p = -1) := by omega
        have hn2 : ¬ (1 ≤ k + 1 ∧ p = -1) := by omega
        rw [ite_eq_right hn1, ite_eq_right hn2]
        by_cases hm : -2 * (k : Int) ≤ p ∧ p ≤ -2
        · have hm' : -2 * ((k + 1 : ℕ) : Int) ≤ p ∧ p ≤ -2 := by omega
          rw [ite_eq_left hm, ite_eq_left hm']
        · have hm' : ¬ (-2 * ((k + 1 : ℕ) : Int) ≤ p ∧ p ≤ -2) := by omega
          rw [ite_eq_right hm, ite_eq_right hm']

private theorem oddScratch_erase_pair {b m : ℕ} (hm : 1 ≤ m) :
    (fun p : Int =>
      if p = -2 * (m : Int) + 1 then WorkSym.blank
      else if p = -2 * (m : Int) then WorkSym.blank
      else oddScratch b m p) = oddScratch b (m - 1) := by
  funext p
  by_cases hp1 : p = -2 * (m : Int) + 1
  · subst hp1; simp only [↓reduceIte]
    exact (oddScratch_lt_blank b (m - 1) (by omega) (by omega) (by omega)).symm
  · by_cases hp0 : p = -2 * (m : Int)
    · subst hp0; simp only [hp1, ↓reduceIte]
      exact (oddScratch_lt_blank b (m - 1) (by omega) (by omega) (by omega)).symm
    · simp only [hp1, hp0, ↓reduceIte]
      unfold oddScratch
      by_cases hm2 : 2 ≤ m
      · by_cases hwall : p = -1
        · subst hwall
          have ha : 1 ≤ m ∧ (-1 : Int) = -1 := ⟨hm, rfl⟩
          have hb : 1 ≤ m - 1 ∧ (-1 : Int) = -1 := ⟨by omega, rfl⟩
          rw [ite_eq_left ha, ite_eq_left hb]
        · have ha : ¬ (1 ≤ m ∧ p = -1) := by omega
          have hb : ¬ (1 ≤ m - 1 ∧ p = -1) := by omega
          rw [ite_eq_right ha, ite_eq_right hb]
          by_cases hmid : -2 * ((m - 1 : ℕ) : Int) ≤ p ∧ p ≤ -2
          · have hmid' : -2 * (m : Int) ≤ p ∧ p ≤ -2 := by omega
            rw [ite_eq_left hmid', ite_eq_left hmid]
          · have hmid' : ¬ (-2 * (m : Int) ≤ p ∧ p ≤ -2) := by omega
            rw [ite_eq_right hmid', ite_eq_right hmid]
      · have hmEq : m = 1 := by omega
        subst hmEq
        have ha : ¬ (1 ≤ 1 ∧ p = -1) := by omega
        have hb : ¬ (1 ≤ 1 - 1 ∧ p = -1) := by omega
        have hc : ¬ (-2 * ((1 : ℕ) : Int) ≤ p ∧ p ≤ -2) := by omega
        have hd : ¬ (-2 * ((1 - 1 : ℕ) : Int) ≤ p ∧ p ≤ -2) := by omega
        rw [ite_eq_right ha, ite_eq_right hc, ite_eq_right hb, ite_eq_right hd]

private def sqrtInit1 : Action 2 WorkSym :=
  mkAct2 0 1 (fun _ _ _ => .stay)
    (fun _ s₀ _ => (s₀, .right)) (fun _ _ s₁ => (s₁, .left)) (fun _ _ _ => none)

private def sqrtStepBoth : Action 2 WorkSym :=
  mkAct2 0 1 (fun _ _ _ => .stay)
    (fun _ s₀ _ => (s₀, .right)) (fun _ _ s₁ => (s₁, .left)) (fun _ _ _ => none)

private def sqrtWriteAux : Action 2 WorkSym :=
  mkAct2 0 1 (fun _ _ _ => .stay)
    (fun _ s₀ _ => (s₀, .right)) (fun _ _ _ => (.oddAux, .left)) (fun _ _ _ => none)

private def sqrtWriteD : Action 2 WorkSym :=
  mkAct2 0 1 (fun _ _ _ => .stay)
    (fun _ s₀ _ => (s₀, .right)) (fun _ _ _ => (.oddD, .right)) (fun _ _ _ => none)

/-- Extract `d` from `unaryTape (d * d)` on Tape 0 via `1 + 3 + ... + (2d - 1) = d^2`,
erasing Tape 0 (`pos = 0`) and leaving `oddScratch b d` (`pos = -1`) on Tape 1. -/
private def unarySqrtBlock : Block 2 WorkSym :=
  (((((Block.act sqrtInit1).seq (Block.act (writeDirAct 1 .wall .left))).seq
    (Block.act (writeDirAct 1 .oddD .right))).seq
    (Block.loop (fun _ sc => sc 0 == .u)
      (stepDirAct 1 .left) actStay
      (((Block.while1 (fun _ sc => sc 1 != .blank) sqrtStepBoth sqrtWriteAux).seq
        (Block.act sqrtWriteD)).seq
        (Block.while1 (fun _ sc => sc 1 != .wall) (stepDirAct 1 .right) actStay)))).seq
    (eraseFromEnd 0))

private theorem Runs_unarySqrtBlock {w : List Bool} (m : Mem 2 WorkSym) (d b : ℕ)
    (hd1 : 1 ≤ d)
    (hT0 : m.work 0 = unaryTape (d * d)) (hP0 : m.workPos 0 = 0)
    (hT1 : m.work 1 = unaryTape b) (hP1 : m.workPos 1 = 0) :
    ∃ t ≤ 5 * d * d + 6,
      Runs unarySqrtBlock w m
        { m with
          work    := fun i p => if i = 0 then .blank else oddScratch b d p
          workPos := fun i => if i = 0 then 0 else -1 } t := by
  unfold unarySqrtBlock
  let outerInv (idx : ℕ) : Mem 2 WorkSym :=
    let k := idx + 1
    { m with
      work    := fun i p => if i = 1 then oddScratch b k p else m.work i p
      workPos := fun i => if i = 0 then ((k * k : ℕ) : Int) else -1 }
  -- 3-step initialization to `outerInv 0` (`k = 1`)
  let mI1 : Mem 2 WorkSym :=
    { m with workPos := fun i => if i = 0 then 1 else -1 }
  have hI1 : applyAct w sqrtInit1 m = mI1 := by
    unfold sqrtInit1; rw [applyAct_mkAct2 w m (by decide : (0 : Fin 2) ≠ 1)]
    refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
    · dsimp only [mI1]
      fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]
      · exact congrFun (ite_self_cell (m.work 0) _) p
      · exact congrFun (ite_self_cell (m.work 1) _) p
    · dsimp only [mI1, Transpose.Dir.shift]
      fin_cases i <;> simp [hP0, hP1]
  let mI2 : Mem 2 WorkSym :=
    { m with
      work    := fun i p => if i = 1 then (if p = -1 then .wall else m.work 1 p) else m.work i p
      workPos := fun i => if i = 0 then 1 else -2 }
  have hI2 : applyAct w (writeDirAct 1 .wall .left) mI1 = mI2 := by
    unfold writeDirAct; rw [applyAct_mkAct1]
    refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
    · dsimp only [mI1, mI2]
      fin_cases i <;> simp
    · dsimp only [mI1, mI2, Transpose.Dir.shift]
      fin_cases i <;> simp
  have hI3 : applyAct w (writeDirAct 1 .oddD .right) mI2 = outerInv 0 := by
    unfold writeDirAct; rw [applyAct_mkAct1]
    refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
    · dsimp only [mI2, outerInv]
      fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]
      rw [hT1]
      exact congrFun (oddScratch_init b) p
    · dsimp only [mI2, outerInv, Transpose.Dir.shift]
      fin_cases i <;> simp
  have rInit : Runs (((Block.act sqrtInit1).seq (Block.act (writeDirAct 1 .wall .left))).seq
      (Block.act (writeDirAct 1 .oddD .right))) w m (outerInv 0) 3 := by
    have r1 : Runs (Block.act sqrtInit1) w m mI1 1 := by rw [← hI1]; exact Runs.act _ _
    have r2 : Runs (Block.act (writeDirAct 1 .wall .left)) w mI1 mI2 1 := by rw [← hI2]; exact Runs.act _ _
    have r3 : Runs (Block.act (writeDirAct 1 .oddD .right)) w mI2 (outerInv 0) 1 := by rw [← hI3]; exact Runs.act _ _
    simpa using (r1.seq r2).seq r3
  -- Outer loop (`d - 1` iterations, `idx = 0 .. d - 2`, `k = idx + 1`)
  let tBody (idx : ℕ) : ℕ := 4 * (idx + 1) + 2
  have rLoop := Runs.loop_sum (w := w)
    (fun _ (sc : Fin 2 → WorkSym) => sc 0 == .u)
    (stepDirAct 1 .left) actStay
    (((Block.while1 (fun _ sc => sc 1 != .blank) sqrtStepBoth sqrtWriteAux).seq
      (Block.act sqrtWriteD)).seq
      (Block.while1 (fun _ sc => sc 1 != .wall) (stepDirAct 1 .right) actStay))
    (d - 1) tBody outerInv
    (fun idx hidx => by
      set k := idx + 1
      have hk1 : 1 ≤ k := by omega
      have hkd : k < d := by omega
      have hkk_lt : k * k < d * d := Nat.mul_lt_mul_of_lt_of_lt hkd hkd
      have hCond : ((outerInv idx).work 0 ((outerInv idx).workPos 0) == .u) = true := by
        dsimp only [outerInv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
        rw [hT0, unaryTape_lt hkk_lt]; rfl
      refine ⟨hCond, ?_⟩
      -- Part A: scan `2 * k - 1` non-blank cells `-2 .. -2k`, then write `.oddAux` at `-2k - 1`
      let scanInv (j : ℕ) : Mem 2 WorkSym :=
        { m with
          work    := fun i p => if i = 1 then oddScratch b k p else m.work i p
          workPos := fun i =>
            if i = 0 then ((k * k + j : ℕ) : Int)
            else -2 - (j : Int) }
      have hEnt : applyAct w (stepDirAct 1 .left) (outerInv idx) = scanInv 0 := by
        unfold stepDirAct; rw [applyAct_mkAct1]
        refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
        · dsimp only [outerInv, scanInv]
          fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]
          exact congrFun (ite_self_cell (oddScratch b k) _) p
        · dsimp only [outerInv, scanInv, k, Transpose.Dir.shift]
          fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte, Nat.add_zero]; omega
      rw [hEnt]
      have hWA := Runs.while1 (w := w)
        (fun _ (sc : Fin 2 → WorkSym) => sc 1 != .blank)
        sqrtStepBoth sqrtWriteAux (2 * k - 1) scanInv
        (fun j hj => by
          have hcell : (scanInv j).work 1 ((scanInv j).workPos 1) ≠ .blank := by
            dsimp only [scanInv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
            exact oddScratch_mid_ne_blank (by omega) (by omega)
          refine ⟨bne_blank_of_ne hcell, ?_⟩
          unfold sqrtStepBoth; rw [applyAct_mkAct2 w (scanInv j) (by decide : (0 : Fin 2) ≠ 1)]
          refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
          · dsimp only [scanInv]
            fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]
            · exact congrFun (ite_self_cell (m.work 0) _) p
            · exact congrFun (ite_self_cell (oddScratch b k) _) p
          · dsimp only [scanInv, Transpose.Dir.shift]
            fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte] <;> omega)
        (by
          dsimp only [scanInv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
          have hpEq : -2 - ((2 * k - 1 : ℕ) : Int) = -2 * (k : Int) - 1 := by omega
          rw [hpEq, oddScratch_lt_blank b k (by omega) (by omega) (by omega)]; rfl)
      let mAfterAux : Mem 2 WorkSym :=
        { m with
          work := fun i p =>
            if i = 1 then (if p = -2 * (k : Int) - 1 then .oddAux else oddScratch b k p)
            else m.work i p
          workPos := fun i =>
            if i = 0 then ((k * k + 2 * k : ℕ) : Int)
            else -2 * ((k + 1 : ℕ) : Int) }
      have hAuxEq : applyAct w sqrtWriteAux (scanInv (2 * k - 1)) = mAfterAux := by
        unfold sqrtWriteAux; rw [applyAct_mkAct2 w _ (by decide : (0 : Fin 2) ≠ 1)]
        refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
        · dsimp only [scanInv, mAfterAux]
          fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]
          · exact congrFun (ite_self_cell (m.work 0) _) p
          · have hpEq : -2 - ((2 * k - 1 : ℕ) : Int) = -2 * (k : Int) - 1 := by omega
            rw [hpEq]
        · dsimp only [scanInv, mAfterAux, Transpose.Dir.shift]
          fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte] <;> omega
      rw [hAuxEq] at hWA
      have hTimeA : (2 * k - 1) + 1 = 2 * k := by omega
      rw [hTimeA] at hWA
      -- Part B: write `.oddD` at `-2*(k+1)`, advancing `t₀` to `(k+1)^2` and `t₁` to `-2k - 1`
      let backInv (j : ℕ) : Mem 2 WorkSym :=
        { m with
          work    := fun i p => if i = 1 then oddScratch b (k + 1) p else m.work i p
          workPos := fun i =>
            if i = 0 then (((k + 1) * (k + 1) : ℕ) : Int)
            else -2 * (k : Int) - 1 + (j : Int) }
      have hDEq : applyAct w sqrtWriteD mAfterAux = backInv 0 := by
        unfold sqrtWriteD; rw [applyAct_mkAct2 w _ (by decide : (0 : Fin 2) ≠ 1)]
        refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
        · dsimp only [mAfterAux, backInv]
          fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]
          · exact congrFun (ite_self_cell (m.work 0) _) p
          · exact congrFun (oddScratch_extend hk1) p
        · dsimp only [mAfterAux, backInv, Transpose.Dir.shift]
          have hsq : k * k + 2 * k + 1 = (k + 1) * (k + 1) := by ring
          fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte] <;> omega
      have hWB : Runs (Block.act sqrtWriteD) w mAfterAux (backInv 0) 1 := by
        rw [← hDEq]; exact Runs.act _ _
      -- Part C: return `t₁` right to `.wall` at `-1` (`2 * k` steps)
      have hWC := Runs.while1 (w := w)
        (fun _ (sc : Fin 2 → WorkSym) => sc 1 != .wall)
        (stepDirAct 1 .right) actStay (2 * k) backInv
        (fun j hj => by
          have hneW : (backInv j).work 1 ((backInv j).workPos 1) ≠ .wall := by
            dsimp only [backInv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
            exact oddScratch_mid_ne_wall (by omega) (by omega)
          have hbne : ((backInv j).work 1 ((backInv j).workPos 1) != .wall) = true := by
            cases h : (backInv j).work 1 ((backInv j).workPos 1) <;>
              first | exact absurd h hneW | rfl
          refine ⟨hbne, ?_⟩
          unfold stepDirAct; rw [applyAct_mkAct1]
          refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
          · dsimp only [backInv]
            fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]
            exact congrFun (ite_self_cell (oddScratch b (k + 1)) _) p
          · dsimp only [backInv, Transpose.Dir.shift]
            fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]; omega)
        (by
          dsimp only [backInv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
          have hm1 : -2 * (k : Int) - 1 + (2 * k : ℕ) = -1 := by omega
          rw [hm1, oddScratch_wall (by omega : 1 ≤ k + 1)]; rfl)
      rw [applyAct_actStay] at hWC
      have hBackEnd : backInv (2 * k) = outerInv (idx + 1) := by
        refine Mem.eq_of_fields rfl (fun _ _ => rfl) (fun i => ?_) rfl
        dsimp only [backInv, outerInv, k]
        fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]; omega
      rw [hBackEnd] at hWC
      have hTime : (2 * k + 1) + (2 * k + 1) = tBody idx := by dsimp [tBody, k]; omega
      rw [← hTime]
      exact (hWA.seq hWB).seq hWC)
    (by
      have hdEq : d - 1 + 1 = d := by omega
      dsimp only [outerInv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte, hdEq]
      rw [hT0, unaryTape_ge le_rfl]; rfl)
  rw [applyAct_actStay] at rLoop
  -- Erase `[0, d * d)` on Tape 0
  have hdEq : d - 1 + 1 = d := by omega
  have hEr0 := Runs_eraseFromEnd (w := w) (0 : Fin 2) (outerInv (d - 1)) (d * d)
    (by dsimp only [outerInv]; simp [hdEq])
    (fun j hj => by dsimp only [outerInv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]; rw [hT0, unaryTape_lt hj]; decide)
    (fun p hp => by
      dsimp only [outerInv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]; rw [hT0]
      rcases hp with hneg | hge
      · exact unaryTape_neg hneg
      · exact unaryTape_ge hge)
  have hFinalEq :
      { outerInv (d - 1) with
        work    := fun i p => if i = 0 then WorkSym.blank else (outerInv (d - 1)).work i p
        workPos := fun i => if i = 0 then 0 else (outerInv (d - 1)).workPos i } =
      { m with
        work    := fun i p => if i = 0 then .blank else oddScratch b d p
        workPos := fun i => if i = 0 then 0 else -1 } := by
    refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
    · dsimp only [outerInv]; fin_cases i <;> simp [hdEq]
    · dsimp only [outerInv]; fin_cases i <;> simp
  rw [hFinalEq] at hEr0
  have hAll := (rInit.seq rLoop).seq hEr0
  refine ⟨_, ?_, hAll⟩
  have hSumLe := natSum_le_of_step (f := fun idx => 1 + tBody idx)
    (g := fun idx => idx * (4 * d)) (N := d - 1)
    (fun idx hidx => by dsimp only [tBody]; nlinarith)
  have hMulLe : (d - 1) * (4 * d) ≤ 4 * d * d := by nlinarith
  nlinarith

/-- Row-template tape prefix on `[0, len)` with `saveCount` leading `.save` cells,
followed by `.emitStart` at multiples of `b` and `.emitCont` elsewhere. -/
private def tplPrefix (len b saveCount : ℕ) : Int → WorkSym :=
  fun p =>
    if 0 ≤ p ∧ p < (len : Int) then
      if p < (saveCount : Int) then .save
      else if p.toNat % b = 0 then .emitStart
      else .emitCont
    else .blank

private theorem tplPrefix_zero (b s : ℕ) : tplPrefix 0 b s = fun _ => .blank := by
  funext p; unfold tplPrefix
  split_ifs <;> first | rfl | omega

private theorem tplPrefix_nonblank {len b s j : ℕ} (hj : j < len) :
    tplPrefix len b s (j : Int) ≠ .blank := by
  unfold tplPrefix
  have h : 0 ≤ (j : Int) ∧ (j : Int) < (len : Int) := by omega
  rw [ite_eq_left h]
  split_ifs <;> decide

private theorem tplPrefix_outside {len b s : ℕ} {p : Int}
    (hp : p < 0 ∨ (len : Int) ≤ p) :
    tplPrefix len b s p = .blank := by
  unfold tplPrefix
  have h : ¬ (0 ≤ p ∧ p < (len : Int)) := by omega
  rw [ite_eq_right h]

private theorem tplPrefix_append_start {len b : ℕ} (hmod : len % b = 0) :
    (fun p : Int => if p = (len : Int) then WorkSym.emitStart else tplPrefix len b 0 p) =
      tplPrefix (len + 1) b 0 := by
  funext p; unfold tplPrefix
  by_cases hp : p = (len : Int)
  · subst hp
    have h1 : 0 ≤ (len : Int) ∧ (len : Int) < ((len + 1 : ℕ) : Int) := by omega
    have h2 : ¬ ((len : Int) < ((0 : ℕ) : Int)) := by omega
    rw [ite_eq_left rfl, ite_eq_left h1, ite_eq_right h2, Int.toNat_natCast, ite_eq_left hmod]
  · rw [ite_eq_right hp]
    by_cases h1 : 0 ≤ p ∧ p < (len : Int)
    · have h2 : 0 ≤ p ∧ p < ((len + 1 : ℕ) : Int) := by omega
      rw [ite_eq_left h1, ite_eq_left h2]
    · have h2 : ¬ (0 ≤ p ∧ p < ((len + 1 : ℕ) : Int)) := by omega
      rw [ite_eq_right h1, ite_eq_right h2]

private theorem tplPrefix_append_cont {len b : ℕ} (hmod : len % b ≠ 0) :
    (fun p : Int => if p = (len : Int) then WorkSym.emitCont else tplPrefix len b 0 p) =
      tplPrefix (len + 1) b 0 := by
  funext p; unfold tplPrefix
  by_cases hp : p = (len : Int)
  · subst hp
    have h1 : 0 ≤ (len : Int) ∧ (len : Int) < ((len + 1 : ℕ) : Int) := by omega
    have h2 : ¬ ((len : Int) < ((0 : ℕ) : Int)) := by omega
    rw [ite_eq_left rfl, ite_eq_left h1, ite_eq_right h2, Int.toNat_natCast, ite_eq_right hmod]
  · rw [ite_eq_right hp]
    by_cases h1 : 0 ≤ p ∧ p < (len : Int)
    · have h2 : 0 ≤ p ∧ p < ((len + 1 : ℕ) : Int) := by omega
      rw [ite_eq_left h1, ite_eq_left h2]
    · have h2 : ¬ (0 ≤ p ∧ p < ((len + 1 : ℕ) : Int)) := by omega
      rw [ite_eq_right h1, ite_eq_right h2]

private theorem tplPrefix_write_save {len b k : ℕ} (hk : k < len) :
    (fun p : Int => if p = (k : Int) then WorkSym.save else tplPrefix len b k p) =
      tplPrefix len b (k + 1) := by
  funext p; unfold tplPrefix
  by_cases hp : p = (k : Int)
  · subst hp
    have h1 : 0 ≤ (k : Int) ∧ (k : Int) < (len : Int) := by omega
    have h2 : (k : Int) < ((k + 1 : ℕ) : Int) := by omega
    rw [ite_eq_left rfl, ite_eq_left h1, ite_eq_left h2]
  · rw [ite_eq_right hp]
    by_cases h1 : 0 ≤ p ∧ p < (len : Int)
    · rw [ite_eq_left h1, ite_eq_left h1]
      by_cases hs : p < (k : Int)
      · have hs' : p < ((k + 1 : ℕ) : Int) := by omega
        rw [ite_eq_left hs, ite_eq_left hs']
      · have hs' : ¬ (p < ((k + 1 : ℕ) : Int)) := by omega
        rw [ite_eq_right hs, ite_eq_right hs']
    · rw [ite_eq_right h1, ite_eq_right h1]

private def tplEmitStartAct : Action 2 WorkSym :=
  mkAct2 0 1 (fun _ _ _ => .stay)
    (fun _ _ _ => (.emitStart, .right)) (fun _ _ s₁ => (s₁, .right)) (fun _ _ _ => none)

private def tplEmitContAct : Action 2 WorkSym :=
  mkAct2 0 1 (fun _ _ _ => .stay)
    (fun _ _ _ => (.emitCont, .right)) (fun _ _ s₁ => (s₁, .right)) (fun _ _ _ => none)

/-- Build `tplPrefix (d * b) b 0` on Tape 0 (`pos = 0`) and clear Tape 1 (`pos = 0`)
from `oddScratch b d` (`pos = -1`) on Tape 1 in `O(d^2 + d * b)` steps. -/
private def buildRowTemplate : Block 2 WorkSym :=
  ((((Block.while1 (fun _ sc => sc 1 != .blank) (stepDirAct 1 .left) (stepDirAct 1 .right)).seq
    (Block.loop (fun _ sc => sc 1 == .oddD)
      (writeDirAct 1 .blank .right) actStay
      ((((Block.act (writeDirAct 1 .blank .right)).seq
        (Block.while1 (fun _ sc => sc 1 != .u) (stepDirAct 1 .right) tplEmitStartAct)).seq
        (Block.while1 (fun _ sc => sc 1 == .u) tplEmitContAct (stepDirAct 1 .left))).seq
        (Block.while1 (fun _ sc => sc 1 != .blank) (stepDirAct 1 .left) (stepDirAct 1 .right))))).seq
    (clearUnary 1)).seq
    (rewindFromEnd 0))

private theorem Runs_buildRowTemplate {w : List Bool} (m : Mem 2 WorkSym) (d b : ℕ)
    (hd1 : 1 ≤ d) (hb1 : 1 ≤ b)
    (hB0 : m.work 0 = fun _ => .blank) (hP0 : m.workPos 0 = 0)
    (hT1 : m.work 1 = oddScratch b d) (hP1 : m.workPos 1 = -1) :
    ∃ t ≤ 4 * d * d + 3 * d * b + 6 * d + 2 * b + 7,
      Runs buildRowTemplate w m
        { m with
          work    := fun i p => if i = 0 then tplPrefix (d * b) b 0 p else .blank
          workPos := fun _ => 0 } t := by
  unfold buildRowTemplate
  let outerInv (q : ℕ) : Mem 2 WorkSym :=
    { m with
      work := fun i p =>
        if i = 0 then tplPrefix (q * b) b 0 p
        else oddScratch b (d - q) p
      workPos := fun i =>
        if i = 0 then ((q * b : ℕ) : Int)
        else -2 * ((d - q : ℕ) : Int) }
  -- Step 1: walk Tape 1 left from `-1` to `-2 * d` (`2 * d + 1` steps)
  let walkInv (j : ℕ) : Mem 2 WorkSym :=
    { m with workPos := fun i => if i = 0 then 0 else -1 - (j : Int) }
  have hWalk0 : walkInv 0 = m := by
    refine Mem.eq_of_fields rfl (fun _ _ => rfl) (fun i => ?_) rfl
    dsimp only [walkInv]; fin_cases i <;> simp [hP0, hP1]
  have hWalk := Runs.while1 (w := w)
    (fun _ (sc : Fin 2 → WorkSym) => sc 1 != .blank)
    (stepDirAct 1 .left) (stepDirAct 1 .right) (2 * d) walkInv
    (fun j hj => by
      have hne : (walkInv j).work 1 ((walkInv j).workPos 1) ≠ .blank := by
        dsimp only [walkInv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
        rw [hT1]
        by_cases hj0 : j = 0
        · subst hj0; simp [oddScratch_wall hd1]
        · exact oddScratch_mid_ne_blank (by omega) (by omega)
      refine ⟨bne_blank_of_ne hne, ?_⟩
      unfold stepDirAct; rw [applyAct_mkAct1]
      refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
      · dsimp only [walkInv]
        fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]
        exact congrFun (ite_self_cell (m.work 1) _) p
      · dsimp only [walkInv, Transpose.Dir.shift]
        fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]; omega)
    (by
      dsimp only [walkInv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
      rw [hT1, oddScratch_lt_blank b d (by omega) (by omega) (by omega)]; rfl)
  have hWalkExit : applyAct w (stepDirAct 1 .right) (walkInv (2 * d)) = outerInv 0 := by
    unfold stepDirAct; rw [applyAct_mkAct1]
    refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
    · dsimp only [walkInv, outerInv]
      fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte, Nat.zero_mul, Nat.sub_zero]
      · rw [tplPrefix_zero, hB0]
      · rw [congrFun (ite_self_cell (m.work 1) _) p, hT1]
    · dsimp only [walkInv, outerInv, Transpose.Dir.shift]
      fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte, Nat.zero_mul, Nat.sub_zero] <;> omega
  rw [hWalk0, hWalkExit] at hWalk
  -- Step 2: `d` iterations of `outerInv q → outerInv (q + 1)`
  let tBody (q : ℕ) : ℕ := 4 * (d - 1 - q) + 2 * b + 3
  have hLoop := Runs.loop_sum (w := w)
    (fun _ (sc : Fin 2 → WorkSym) => sc 1 == .oddD)
    (writeDirAct 1 .blank .right) actStay
    ((((Block.act (writeDirAct 1 .blank .right)).seq
      (Block.while1 (fun _ sc => sc 1 != .u) (stepDirAct 1 .right) tplEmitStartAct)).seq
      (Block.while1 (fun _ sc => sc 1 == .u) tplEmitContAct (stepDirAct 1 .left))).seq
      (Block.while1 (fun _ sc => sc 1 != .blank) (stepDirAct 1 .left) (stepDirAct 1 .right)))
    d tBody outerInv
    (fun q hq => by
      set mRem := d - q
      have hm1 : 1 ≤ mRem := by omega
      have hremEq : mRem - 1 = d - (q + 1) := by omega
      have hCond : ((outerInv q).work 1 ((outerInv q).workPos 1) == .oddD) = true := by
        dsimp only [outerInv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
        rw [oddScratch_left_end hm1]; rfl
      refine ⟨hCond, ?_⟩
      -- Enter + erase second cell of pair (`-2 * mRem` and `-2 * mRem + 1`)
      let mEr1 : Mem 2 WorkSym :=
        { m with
          work := fun i p =>
            if i = 0 then tplPrefix (q * b) b 0 p
            else (if p = -2 * (mRem : Int) then .blank else oddScratch b mRem p)
          workPos := fun i =>
            if i = 0 then ((q * b : ℕ) : Int)
            else -2 * (mRem : Int) + 1 }
      have hEnt : applyAct w (writeDirAct 1 .blank .right) (outerInv q) = mEr1 := by
        unfold writeDirAct; rw [applyAct_mkAct1]
        refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
        · dsimp only [outerInv, mEr1, mRem]
          fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]
        · dsimp only [outerInv, mEr1, mRem, Transpose.Dir.shift]
          fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]
      rw [hEnt]
      set nScan := 2 * (mRem - 1)
      let scanUInv (j : ℕ) : Mem 2 WorkSym :=
        { m with
          work := fun i p =>
            if i = 0 then tplPrefix (q * b) b 0 p
            else oddScratch b (mRem - 1) p
          workPos := fun i =>
            if i = 0 then ((q * b : ℕ) : Int)
            else -(nScan : Int) + (j : Int) }
      have hEr2Eq : applyAct w (writeDirAct 1 .blank .right) mEr1 = scanUInv 0 := by
        unfold writeDirAct; rw [applyAct_mkAct1]
        refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
        · dsimp only [mEr1, scanUInv]
          fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]
          exact congrFun (oddScratch_erase_pair hm1) p
        · dsimp only [mEr1, scanUInv, Transpose.Dir.shift, nScan]
          fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]; omega
      have rEr2 : Runs (Block.act (writeDirAct 1 .blank .right)) w mEr1 (scanUInv 0) 1 := by
        rw [← hEr2Eq]; exact Runs.act _ _
      -- Scan right to `0` (`sc 1 != .u`), then write `.emitStart` at `q * b` on Tape 0
      have rScanU := Runs.while1 (w := w)
        (fun _ (sc : Fin 2 → WorkSym) => sc 1 != .u)
        (stepDirAct 1 .right) tplEmitStartAct nScan scanUInv
        (fun j hj => by
          have hneU : (scanUInv j).work 1 ((scanUInv j).workPos 1) ≠ .u := by
            dsimp only [scanUInv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
            exact oddScratch_neg_ne_u b (mRem - 1) (by omega) (by omega)
          have hbneU : ((scanUInv j).work 1 ((scanUInv j).workPos 1) != .u) = true := by
            cases h : (scanUInv j).work 1 ((scanUInv j).workPos 1) <;>
              first | exact absurd h hneU | rfl
          refine ⟨hbneU, ?_⟩
          unfold stepDirAct; rw [applyAct_mkAct1]
          refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
          · dsimp only [scanUInv]
            fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]
            exact congrFun (ite_self_cell (oddScratch b (mRem - 1)) _) p
          · dsimp only [scanUInv, Transpose.Dir.shift]
            fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]; omega)
        (by
          dsimp only [scanUInv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
          have h0 : -(nScan : Int) + (nScan : Int) = (0 : ℕ) := by omega
          rw [h0, oddScratch_nonneg b (mRem - 1) (by omega), unaryTape_lt (by omega : 0 < b)]; rfl)
      -- Emit `b - 1` `.emitCont` cells across `[1, b)` on Tape 1
      let contInv (j : ℕ) : Mem 2 WorkSym :=
        { m with
          work := fun i p =>
            if i = 0 then tplPrefix (q * b + 1 + j) b 0 p
            else oddScratch b (mRem - 1) p
          workPos := fun i =>
            if i = 0 then ((q * b + 1 + j : ℕ) : Int)
            else ((1 + j : ℕ) : Int) }
      have hStartEq : applyAct w tplEmitStartAct (scanUInv nScan) = contInv 0 := by
        unfold tplEmitStartAct; rw [applyAct_mkAct2 w _ (by decide : (0 : Fin 2) ≠ 1)]
        refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
        · dsimp only [scanUInv, contInv, Nat.add_zero]
          fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]
          · exact congrFun (tplPrefix_append_start (Nat.mul_mod_left q b)) p
          · exact congrFun (ite_self_cell (oddScratch b (mRem - 1)) _) p
        · dsimp only [scanUInv, contInv, Transpose.Dir.shift]
          fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte] <;> omega
      rw [hStartEq] at rScanU
      have rCont := Runs.while1 (w := w)
        (fun _ (sc : Fin 2 → WorkSym) => sc 1 == .u)
        tplEmitContAct (stepDirAct 1 .left) (b - 1) contInv
        (fun j hj => by
          have hcellU : ((contInv j).work 1 ((contInv j).workPos 1) == .u) = true := by
            dsimp only [contInv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
            rw [oddScratch_nonneg b (mRem - 1) (by omega), unaryTape_lt (by omega : 1 + j < b)]; rfl
          refine ⟨hcellU, ?_⟩
          have hmodNe : (q * b + 1 + j) % b ≠ 0 := by
            have h1 : q * b + 1 + j = (1 + j) + q * b := by ring
            rw [h1, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega : 1 + j < b)]
            omega
          unfold tplEmitContAct; rw [applyAct_mkAct2 w _ (by decide : (0 : Fin 2) ≠ 1)]
          refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
          · dsimp only [contInv]
            fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]
            · have hadd : q * b + 1 + (j + 1) = (q * b + 1 + j) + 1 := by omega
              rw [hadd]
              exact congrFun (tplPrefix_append_cont hmodNe) p
            · exact congrFun (ite_self_cell (oddScratch b (mRem - 1)) _) p
          · dsimp only [contInv, Transpose.Dir.shift]
            fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte] <;> omega)
        (by
          dsimp only [contInv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
          have hbEq : 1 + (b - 1) = b := by omega
          rw [hbEq, oddScratch_nonneg b (mRem - 1) (by omega), unaryTape_ge le_rfl]; rfl)
      have hTimeC : (b - 1) + 1 = b := by omega
      rw [hTimeC] at rCont
      -- Scan left across `[ -nScan, b - 1 ]` back to `-nScan` (`nScan + b + 1` steps)
      let retInv (j : ℕ) : Mem 2 WorkSym :=
        { m with
          work := fun i p =>
            if i = 0 then tplPrefix ((q + 1) * b) b 0 p
            else oddScratch b (mRem - 1) p
          workPos := fun i =>
            if i = 0 then (((q + 1) * b : ℕ) : Int)
            else ((b - 1 : ℕ) : Int) - (j : Int) }
      have hContExit : applyAct w (stepDirAct 1 .left) (contInv (b - 1)) = retInv 0 := by
        unfold stepDirAct; rw [applyAct_mkAct1]
        have hqb : q * b + 1 + (b - 1) = (q + 1) * b := by
          have : 1 + (b - 1) = b := by omega
          calc q * b + 1 + (b - 1) = q * b + (1 + (b - 1)) := by omega
            _ = q * b + b := by rw [this]
            _ = (q + 1) * b := by ring
        refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
        · dsimp only [contInv, retInv]
          fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]
          · rw [hqb]
          · exact congrFun (ite_self_cell (oddScratch b (mRem - 1)) _) p
        · dsimp only [contInv, retInv, Transpose.Dir.shift]
          fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]
          · exact congrArg Nat.cast hqb
          · omega
      rw [hContExit] at rCont
      have rRet := Runs.while1 (w := w)
        (fun _ (sc : Fin 2 → WorkSym) => sc 1 != .blank)
        (stepDirAct 1 .left) (stepDirAct 1 .right) (nScan + b) retInv
        (fun j hj => by
          have hneB : (retInv j).work 1 ((retInv j).workPos 1) ≠ .blank := by
            dsimp only [retInv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
            set pos1 : Int := ((b - 1 : ℕ) : Int) - (j : Int)
            by_cases hpos0 : 0 ≤ pos1
            · rw [oddScratch_nonneg b (mRem - 1) hpos0]
              have hnat : pos1 = ((pos1.toNat : ℕ) : Int) := (Int.toNat_of_nonneg hpos0).symm
              rw [hnat, unaryTape_lt (by omega : pos1.toNat < b)]; decide
            · by_cases hpos1 : pos1 = -1
              · rw [hpos1, oddScratch_wall (by omega : 1 ≤ mRem - 1)]; decide
              · exact oddScratch_mid_ne_blank (by omega) (by omega)
          refine ⟨bne_blank_of_ne hneB, ?_⟩
          unfold stepDirAct; rw [applyAct_mkAct1]
          refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
          · dsimp only [retInv]
            fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]
            exact congrFun (ite_self_cell (oddScratch b (mRem - 1)) _) p
          · dsimp only [retInv, Transpose.Dir.shift]
            fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]; omega)
        (by
          dsimp only [retInv, nScan]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
          rw [oddScratch_lt_blank b (mRem - 1) (by omega) (by omega) (by omega)]; rfl)
      have hRetExit : applyAct w (stepDirAct 1 .right) (retInv (nScan + b)) = outerInv (q + 1) := by
        unfold stepDirAct; rw [applyAct_mkAct1]
        refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
        · dsimp only [retInv, outerInv]
          fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]
          rw [congrFun (ite_self_cell (oddScratch b (mRem - 1)) _) p, hremEq]
        · dsimp only [retInv, outerInv, Transpose.Dir.shift, nScan]
          fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]
          omega
      rw [hRetExit] at rRet
      have hTimeIter : ((1 + (nScan + 1)) + b) + ((nScan + b) + 1) = tBody q := by
        dsimp [tBody, nScan, mRem]; omega
      rw [← hTimeIter]
      exact ((rEr2.seq rScanU).seq rCont).seq rRet)
    (by
      dsimp only [outerInv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte, Nat.sub_self]
      have h0 : -2 * ((0 : ℕ) : Int) = ((0 : ℕ) : Int) := by omega
      rw [oddScratch_zero, h0, unaryTape_lt (by omega : 0 < b)]; rfl)
  rw [applyAct_actStay] at hLoop
  -- Clear `unaryTape b` on Tape 1 and rewind Tape 0 from `d * b` to `0`
  have rClr1 := Runs_clearUnary (w := w) (1 : Fin 2) (outerInv d) b
    (by dsimp only [outerInv]; simp [oddScratch_zero])
    (by dsimp only [outerInv]; simp)
  let mAfterClr : Mem 2 WorkSym :=
    { outerInv d with work := fun i p => if i = 1 then .blank else (outerInv d).work i p }
  have hClrEq : { outerInv d with work := fun i p => if i = 1 then .blank else (outerInv d).work i p } =
      mAfterClr := rfl
  rw [hClrEq] at rClr1
  have rRew0 := Runs_rewindFromEnd (w := w) (0 : Fin 2) mAfterClr (d * b)
    (by dsimp only [mAfterClr, outerInv]; simp)
    (fun j hj => by dsimp only [mAfterClr, outerInv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]; exact tplPrefix_nonblank hj)
    (by dsimp only [mAfterClr, outerInv]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]; exact tplPrefix_outside (Or.inl (by omega)))
  have hFinalEq :
      { mAfterClr with workPos := fun i => if i = 0 then 0 else mAfterClr.workPos i } =
      { m with
        work    := fun i p => if i = 0 then tplPrefix (d * b) b 0 p else .blank
        workPos := fun _ => 0 } := by
    refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) rfl
    · dsimp only [mAfterClr, outerInv]; fin_cases i <;> simp
    · dsimp only [mAfterClr, outerInv]; fin_cases i <;> simp
  rw [hFinalEq] at rRew0
  have hAll := ((hWalk.seq hLoop).seq rClr1).seq rRew0
  refine ⟨_, ?_, hAll⟩
  have hSumLe := natSum_le_of_step (f := fun q => 1 + tBody q)
    (g := fun q => q * (4 * d + 2 * b + 4)) (N := d)
    (fun q hq => by
      dsimp only [tBody]
      have : d - 1 - q ≤ d := by omega
      nlinarith)
  nlinarith

private theorem tplPrefix_save_lt {len b s j : ℕ} (hj : j < s) (hs : s ≤ len) :
    tplPrefix len b s (j : Int) = .save := by
  unfold tplPrefix
  have h1 : 0 ≤ (j : Int) ∧ (j : Int) < (len : Int) := by omega
  have h2 : (j : Int) < (s : Int) := by omega
  rw [ite_eq_left h1, ite_eq_left h2]

private theorem tplPrefix_emitStart_at {d b r : ℕ} (hr : r < d) (hb1 : 1 ≤ b) :
    tplPrefix (d * b) b (r * b) ((r * b : ℕ) : Int) = .emitStart := by
  unfold tplPrefix
  have hrb_lt : r * b < d * b := by
    calc r * b < r * b + b := by omega
      _ = (r + 1) * b := by ring
      _ ≤ d * b := Nat.mul_le_mul_right b (by omega)
  have h1 : 0 ≤ ((r * b : ℕ) : Int) ∧ ((r * b : ℕ) : Int) < ((d * b : ℕ) : Int) := by omega
  have h2 : ¬ (((r * b : ℕ) : Int) < ((r * b : ℕ) : Int)) := by omega
  rw [ite_eq_left h1, ite_eq_right h2, Int.toNat_natCast, ite_eq_left (Nat.mul_mod_left r b)]

private theorem tplPrefix_emitCont_at {d b r t : ℕ} (hr : r < d) (ht : t < b - 1) :
    tplPrefix (d * b) b (r * b + 1 + t) ((r * b + 1 + t : ℕ) : Int) = .emitCont := by
  unfold tplPrefix
  have hlt : r * b + 1 + t < d * b := by
    have : r * b + 1 + t < (r + 1) * b := by ring_nf; omega
    have : (r + 1) * b ≤ d * b := Nat.mul_le_mul_right b (by omega)
    omega
  have h1 : 0 ≤ ((r * b + 1 + t : ℕ) : Int) ∧
      ((r * b + 1 + t : ℕ) : Int) < ((d * b : ℕ) : Int) := by omega
  have h2 : ¬ (((r * b + 1 + t : ℕ) : Int) < ((r * b + 1 + t : ℕ) : Int)) := by omega
  have hmod : (r * b + 1 + t) % b ≠ 0 := by
    have heq : r * b + 1 + t = (1 + t) + r * b := by ring
    rw [heq, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega : 1 + t < b)]
    omega
  rw [ite_eq_left h1, ite_eq_right h2, Int.toNat_natCast, ite_eq_right hmod]

private theorem tplPrefix_not_emitCont_boundary {d b r : ℕ} :
    (tplPrefix (d * b) b ((r + 1) * b) (((r + 1) * b : ℕ) : Int) == .emitCont) = false := by
  unfold tplPrefix
  by_cases h1 : 0 ≤ (((r + 1) * b : ℕ) : Int) ∧
      (((r + 1) * b : ℕ) : Int) < ((d * b : ℕ) : Int)
  · rw [ite_eq_left h1]
    have h2 : ¬ ((((r + 1) * b : ℕ) : Int) < (((r + 1) * b : ℕ) : Int)) := by omega
    rw [ite_eq_right h2, Int.toNat_natCast, ite_eq_left (Nat.mul_mod_left (r + 1) b)]
    rfl
  · rw [ite_eq_right h1]; rfl

private theorem encode_get_triple {d b : ℕ} (A : Transpose.Matrix) {r c t : ℕ}
    (hr : r < d) (hc : c < d) (ht : t < b) :
    (Transpose.encode d b A)[(r * d + c) * b + t]? = some (A r c t) := by
  have hlt : (r * d + c) * b + t < d * d * b := by
    have h1 : r * d + c < d * d := by
      calc r * d + c < r * d + d := by omega
        _ = (r + 1) * d := by ring
        _ ≤ d * d := Nat.mul_le_mul_right d (by omega)
    calc (r * d + c) * b + t < (r * d + c) * b + b := by omega
      _ = (r * d + c + 1) * b := by ring
      _ ≤ (d * d) * b := Nat.mul_le_mul_right b (by omega)
  rw [(encode_len_get d b A).2 _ hlt]
  have heq : (r * d + c) * b + t = r * (d * b) + (c * b + t) := by ring
  have hcb : c * b + t < d * b := by
    calc c * b + t < c * b + b := by omega
      _ = (c + 1) * b := by ring
      _ ≤ d * b := Nat.mul_le_mul_right b (by omega)
  obtain ⟨hd1, hm1⟩ := mul_add_div_mod_tm hcb
  obtain ⟨hd2, hm2⟩ := mul_add_div_mod_tm ht
  rw [heq, hd1, hm1, hd2, hm2]

private theorem rowShear_bit_first {d : ℕ} (A : Transpose.Matrix) {r k : ℕ}
    (hr : r < d) (hk : k < (d - r) * Transpose.entryBits d) :
    let b := Transpose.entryBits d
    (Transpose.encode d b (rowShearTMMatrix d A))[r * d * b + k]? =
      (Transpose.encode d b A)[r * d * b + r * b + k]? := by
  intro b
  have hk' : k < (d - r) * b := hk
  have hbPos : 0 < b := entryBits_pos_tm d
  set c := k / b
  set t := k % b
  have hkt : k = c * b + t := by
    have := Nat.div_add_mod k b; dsimp [c, t]; linarith
  have ht_lt : t < b := Nat.mod_lt k hbPos
  have hc_lt_dr : c < d - r := by
    by_contra hge
    have : (d - r) * b ≤ c * b := Nat.mul_le_mul_right b (Nat.le_of_not_gt hge)
    linarith
  have hc_lt : c < d := by omega
  have hcr_lt : c + r < d := by omega
  have hmod : (c + r) % d = c + r := Nat.mod_eq_of_lt hcr_lt
  have hidx1 : r * d * b + k = (r * d + c) * b + t := by rw [hkt]; ring
  have hidx2 : r * d * b + r * b + k = (r * d + (c + r)) * b + t := by rw [hkt]; ring
  rw [hidx1, hidx2, encode_get_triple (rowShearTMMatrix d A) hr hc_lt ht_lt,
    encode_get_triple A hr hcr_lt ht_lt]
  unfold rowShearTMMatrix
  rw [hmod]

private theorem rowShear_bit_wrap {d : ℕ} (A : Transpose.Matrix) {r j : ℕ}
    (hr : r < d) (hj : j < r * Transpose.entryBits d) :
    let b := Transpose.entryBits d
    (Transpose.encode d b (rowShearTMMatrix d A))[r * d * b + (d - r) * b + j]? =
      (Transpose.encode d b A)[r * d * b + j]? := by
  intro b
  have hj' : j < r * b := hj
  have hbPos : 0 < b := entryBits_pos_tm d
  set q := j / b
  set t := j % b
  have hjt : j = q * b + t := by
    have := Nat.div_add_mod j b; dsimp [q, t]; linarith
  have ht_lt : t < b := Nat.mod_lt j hbPos
  have hq_lt : q < r := by
    by_contra hge
    have : r * b ≤ q * b := Nat.mul_le_mul_right b (Nat.le_of_not_gt hge)
    linarith
  set c := d - r + q
  have hc_lt : c < d := by omega
  have hcr : c + r = q + d := by dsimp [c]; omega
  have hmod : (c + r) % d = q := by
    rw [hcr, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : q < d)]
  have hidx1 : r * d * b + (d - r) * b + j = (r * d + c) * b + t := by
    rw [hjt]; dsimp [c]; ring
  have hidx2 : r * d * b + j = (r * d + q) * b + t := by rw [hjt]; ring
  rw [hidx1, hidx2, encode_get_triple (rowShearTMMatrix d A) hr hc_lt ht_lt,
    encode_get_triple A hr (by omega : q < d) ht_lt]
  unfold rowShearTMMatrix
  rw [hmod]

private def shearSaveAct : Action 2 WorkSym :=
  mkAct2 0 1 (fun _ _ _ => .right)
    (fun _ s₀ _ => (s₀, .right))
    (fun inp _ _ => (bitSym (inp.getD false), .right))
    (fun _ _ _ => none)

private def shearEmitFlipAct : Action 2 WorkSym :=
  mkAct1 0 (fun _ _ => .right) (fun _ _ => (.save, .right)) (fun inp _ => inp)

private def shearEmitKeepAct : Action 2 WorkSym :=
  mkAct1 0 (fun _ _ => .right) (fun _ s₀ => (s₀, .right)) (fun inp _ => inp)

private def shearEmitSavedAct : Action 2 WorkSym :=
  mkAct1 1 (fun _ _ => .stay) (fun _ s₁ => (s₁, .right)) (fun _ s₁ => symBit s₁)

private def shearRowBody : Block 2 WorkSym :=
  ((((((Block.while1 (fun _ sc => sc 0 == .save) shearSaveAct shearEmitFlipAct).seq
    (Block.while1 (fun _ sc => sc 0 == .emitCont) shearEmitFlipAct actStay)).seq
    (Block.while1 (fun _ sc => sc 0 != .blank) shearEmitKeepAct actStay)).seq
    (rewindFromEnd 0)).seq
    (rewindFromEnd 1)).seq
    (Block.while1 (fun _ sc => sc 1 != .blank) shearEmitSavedAct actStay)).seq
    (eraseFromEnd 1)

private def streamRowShear : Block 2 WorkSym :=
  Block.loop (fun inp _ => inp.isSome) actStay actStay shearRowBody

private theorem Runs_streamRowShear {d : ℕ} (hd1 : 1 ≤ d) (A : Transpose.Matrix)
    (m : Mem 2 WorkSym) :
    let b := Transpose.entryBits d
    let w := Transpose.encode d b A
    let out := Transpose.encode d b (rowShearTMMatrix d A)
    m.inPos = 0 →
    m.work 0 = tplPrefix (d * b) b 0 → m.workPos 0 = 0 →
    m.work 1 = (fun _ => .blank) → m.workPos 1 = 0 →
    m.outRev = [] →
    ∃ (t : ℕ) (mHalt : Mem 2 WorkSym),
      t ≤ 5 * d * d * b + 10 * d + 1 ∧
      Runs streamRowShear w m mHalt t ∧
      mHalt.outRev.reverse = out := by
  intro b w out hIn hT0 hP0 hB1 hP1 hOut0
  unfold streamRowShear
  have hb1 : 1 ≤ b := entryBits_pos_tm d
  have hwLen : w.length = d * d * b := (encode_len_get d b A).1
  have houtLen : out.length = d * d * b := (encode_len_get d b (rowShearTMMatrix d A)).1
  let rowInv (r : ℕ) : Mem 2 WorkSym :=
    { inPos   := ((r * d * b : ℕ) : Int)
      work    := fun i p => if i = 0 then tplPrefix (d * b) b (r * b) p else .blank
      workPos := fun _ => 0
      outRev  := (out.take (r * d * b)).reverse }
  have hRow0 : rowInv 0 = m := by
    refine Mem.eq_of_fields ?_ (fun i p => ?_) (fun i => ?_) ?_
    · dsimp only [rowInv]; simp [hIn]
    · dsimp only [rowInv]; fin_cases i <;> simp [hT0, hB1]
    · dsimp only [rowInv]; fin_cases i <;> simp [hP0, hP1]
    · dsimp only [rowInv]; simp [hOut0]
  let tRow (r : ℕ) : ℕ := 2 * d * b + 3 * r * b + 9
  have hLoop := Runs.loop_sum (w := w)
    (fun inp (_ : Fin 2 → WorkSym) => inp.isSome)
    actStay actStay shearRowBody d tRow rowInv
    (fun r hr => by
      have hrdb_lt : r * d * b < w.length := by
        have h1 : (r + 1) * (d * b) ≤ d * (d * b) := Nat.mul_le_mul_right (d * b) (by omega)
        have h2 : 0 < d * b := Nat.mul_pos (by omega) hb1
        nlinarith
      have hCond : (Transpose.readInput w (rowInv r).inPos).isSome = true := by
        dsimp only [rowInv]
        rw [readInput_of_nonneg, List.getElem?_eq_getElem hrdb_lt]; rfl
      refine ⟨hCond, ?_⟩
      rw [applyAct_actStay]
      unfold shearRowBody
      set wRow := w.drop (r * d * b)
      have hwRowGet : ∀ idx (hlt : r * d * b + idx < w.length), wRow[idx]? = some w[r * d * b + idx] := by
        intro idx hlt
        dsimp only [wRow]
        rw [List.getElem?_drop, List.getElem?_eq_getElem hlt]
      -- Phase 1: save `r * b` prefix bits onto Tape 1, then on exit emit bit `0` of `A r r`
      let p1Inv (j : ℕ) : Mem 2 WorkSym :=
        { inPos   := ((r * d * b + j : ℕ) : Int)
          work    := fun i p =>
            if i = 0 then tplPrefix (d * b) b (r * b) p
            else wordTape (wRow.take j) p
          workPos := fun _ => (j : Int)
          outRev  := (out.take (r * d * b)).reverse }
      have hP1_0 : p1Inv 0 = rowInv r := by
        refine Mem.eq_of_fields rfl (fun i p => ?_) (fun _ => rfl) rfl
        dsimp only [p1Inv, rowInv]
        fin_cases i <;> simp [wordTape_nil]
      have rP1 := Runs.while1 (w := w)
        (fun _ (sc : Fin 2 → WorkSym) => sc 0 == .save)
        shearSaveAct shearEmitFlipAct (r * b) p1Inv
        (fun j hj => by
          have hrb_le : r * b ≤ d * b := Nat.mul_le_mul_right b (by omega)
          have hcell : ((p1Inv j).work 0 ((p1Inv j).workPos 0) == .save) = true := by
            dsimp only [p1Inv]; simp only [Fin.isValue, ↓reduceIte]
            rw [tplPrefix_save_lt hj hrb_le]; rfl
          refine ⟨hcell, ?_⟩
          have hj_lt_w : r * d * b + j < w.length := by
            have : r * d * b + j < r * d * b + d * b := by omega
            have : (r + 1) * d * b ≤ d * d * b :=
              Nat.mul_le_mul_right b (Nat.mul_le_mul_right d (by omega))
            nlinarith
          have hwGet : w[r * d * b + j]? = some w[r * d * b + j] := List.getElem?_eq_getElem hj_lt_w
          have hDropGet : wRow[j]? = some w[r * d * b + j] := hwRowGet j hj_lt_w
          unfold shearSaveAct; rw [applyAct_mkAct2 w _ (by decide : (0 : Fin 2) ≠ 1)]
          refine Mem.eq_of_fields ?_ (fun i p => ?_) (fun i => ?_) rfl
          · dsimp only [p1Inv, Transpose.Dir.shift]; omega
          · dsimp only [p1Inv]
            fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]
            · exact congrFun (ite_self_cell (tplPrefix (d * b) b (r * b)) _) p
            · rw [readInput_of_nonneg, hwGet]; dsimp only [Option.getD]
              exact congrFun (wordTape_take_succ hDropGet) p
          · dsimp only [p1Inv, Transpose.Dir.shift]
            fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte] <;> omega)
        (by
          dsimp only [p1Inv]; simp only [Fin.isValue, ↓reduceIte]
          rw [tplPrefix_emitStart_at hr hb1]; rfl)
      -- Phase 2 invariant (`t = 0 .. b - 1`)
      let savedTape := wordTape (wRow.take (r * b))
      let p2Inv (t : ℕ) : Mem 2 WorkSym :=
        { inPos   := ((r * d * b + r * b + 1 + t : ℕ) : Int)
          work    := fun i p =>
            if i = 0 then tplPrefix (d * b) b (r * b + 1 + t) p
            else savedTape p
          workPos := fun i =>
            if i = 0 then ((r * b + 1 + t : ℕ) : Int)
            else ((r * b : ℕ) : Int)
          outRev  := (out.take (r * d * b + 1 + t)).reverse }
      have hP1Exit : applyAct w shearEmitFlipAct (p1Inv (r * b)) = p2Inv 0 := by
        have hrb_lt : r * b < d * b := by
          calc r * b < r * b + b := by omega
            _ = (r + 1) * b := by ring
            _ ≤ d * b := Nat.mul_le_mul_right b (by omega)
        have hwLt : r * d * b + r * b < w.length := by
          have : (r + 1) * d * b ≤ d * d * b :=
            Nat.mul_le_mul_right b (Nat.mul_le_mul_right d (by omega))
          nlinarith
        have hOutBit : out[r * d * b]? = some w[r * d * b + r * b] := by
          have h := rowShear_bit_first A hr (k := 0) (by
            have : 1 ≤ d - r := by omega
            exact Nat.mul_pos this hb1)
          change out[r * d * b + 0]? = w[r * d * b + r * b + 0]? at h
          rw [Nat.add_zero, Nat.add_zero] at h
          rw [h, List.getElem?_eq_getElem hwLt]
        unfold shearEmitFlipAct; rw [applyAct_mkAct1]
        refine Mem.eq_of_fields ?_ (fun i p => ?_) (fun i => ?_) ?_
        · dsimp only [p1Inv, p2Inv, Transpose.Dir.shift]; omega
        · dsimp only [p1Inv, p2Inv, savedTape, Nat.add_zero]
          fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]
          exact congrFun (tplPrefix_write_save hrb_lt) p
        · dsimp only [p1Inv, p2Inv, Transpose.Dir.shift]
          fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]; omega
        · dsimp only [p1Inv, p2Inv, Nat.add_zero]
          rw [readInput_of_nonneg, List.getElem?_eq_getElem hwLt]
          have htk := take_succ_of_getElem?_tm hOutBit
          rw [htk, List.reverse_append, List.reverse_singleton]; rfl
      rw [hP1_0, hP1Exit] at rP1
      -- Phase 2: emit remaining `b - 1` bits of `A r r` while flipping `.emitCont → .save`
      have rP2 := Runs.while1 (w := w)
        (fun _ (sc : Fin 2 → WorkSym) => sc 0 == .emitCont)
        shearEmitFlipAct actStay (b - 1) p2Inv
        (fun t ht => by
          have hcell : ((p2Inv t).work 0 ((p2Inv t).workPos 0) == .emitCont) = true := by
            dsimp only [p2Inv]; simp only [Fin.isValue, ↓reduceIte]
            rw [tplPrefix_emitCont_at hr ht]; rfl
          refine ⟨hcell, ?_⟩
          have hk_lt_dr : 1 + t < (d - r) * b := by
            have : 1 ≤ d - r := by omega
            have : b ≤ (d - r) * b := Nat.le_mul_of_pos_left b this
            omega
          have hpos_lt : r * b + 1 + t < d * b := by
            have : r * b + (d - r) * b = d * b := by
              rw [← Nat.add_mul, Nat.add_sub_of_le (by omega : r ≤ d)]
            omega
          have hwLt : r * d * b + r * b + 1 + t < w.length := by
            have : (r + 1) * d * b ≤ d * d * b :=
              Nat.mul_le_mul_right b (Nat.mul_le_mul_right d (by omega))
            nlinarith
          have hOutBit : out[r * d * b + (1 + t)]? = some w[r * d * b + r * b + 1 + t] := by
            have h := rowShear_bit_first A hr hk_lt_dr
            change out[r * d * b + (1 + t)]? = w[r * d * b + r * b + (1 + t)]? at h
            have heq : r * d * b + r * b + (1 + t) = r * d * b + r * b + 1 + t := by omega
            rw [heq, List.getElem?_eq_getElem hwLt] at h; exact h
          unfold shearEmitFlipAct; rw [applyAct_mkAct1]
          refine Mem.eq_of_fields ?_ (fun i p => ?_) (fun i => ?_) ?_
          · dsimp only [p2Inv, Transpose.Dir.shift]; omega
          · dsimp only [p2Inv]
            fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]
            have hadd : r * b + 1 + (t + 1) = (r * b + 1 + t) + 1 := by omega
            rw [hadd]
            exact congrFun (tplPrefix_write_save hpos_lt) p
          · dsimp only [p2Inv, Transpose.Dir.shift]
            fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]; omega
          · dsimp only [p2Inv]
            rw [readInput_of_nonneg, List.getElem?_eq_getElem hwLt]
            have htk := take_succ_of_getElem?_tm hOutBit
            have hidx1 : r * d * b + 1 + (t + 1) = r * d * b + (1 + t) + 1 := by omega
            have hidx2 : r * d * b + (1 + t) = r * d * b + 1 + t := by omega
            rw [hidx1, htk, hidx2, List.reverse_append, List.reverse_singleton]; rfl)
        (by
          dsimp only [p2Inv]; simp only [Fin.isValue, ↓reduceIte]
          have hrb1 : r * b + 1 + (b - 1) = (r + 1) * b := by
            have : 1 + (b - 1) = b := by omega
            calc r * b + 1 + (b - 1) = r * b + (1 + (b - 1)) := by omega
              _ = r * b + b := by rw [this]
              _ = (r + 1) * b := by ring
          rw [hrb1]
          exact tplPrefix_not_emitCont_boundary)
      rw [applyAct_actStay] at rP2
      have hTime2 : (b - 1) + 1 = b := by omega
      rw [hTime2] at rP2
      -- Phase 3: emit remaining `(d - 1 - r) * b` bits while scanning `[(r + 1) * b, d * b)`
      let p3Inv (j : ℕ) : Mem 2 WorkSym :=
        { inPos   := ((r * d * b + (r + 1) * b + j : ℕ) : Int)
          work    := fun i p =>
            if i = 0 then tplPrefix (d * b) b ((r + 1) * b) p
            else savedTape p
          workPos := fun i =>
            if i = 0 then (((r + 1) * b + j : ℕ) : Int)
            else ((r * b : ℕ) : Int)
          outRev  := (out.take (r * d * b + b + j)).reverse }
      have hP2End : p2Inv (b - 1) = p3Inv 0 := by
        have hrb1 : r * b + 1 + (b - 1) = (r + 1) * b := by
          have : 1 + (b - 1) = b := by omega
          calc r * b + 1 + (b - 1) = r * b + (1 + (b - 1)) := by omega
            _ = r * b + b := by rw [this]
            _ = (r + 1) * b := by ring
        refine Mem.eq_of_fields ?_ (fun i p => ?_) (fun i => ?_) ?_
        · dsimp only [p2Inv, p3Inv]; omega
        · dsimp only [p2Inv, p3Inv]; fin_cases i <;> simp [hrb1]
        · dsimp only [p2Inv, p3Inv]; fin_cases i <;> simp [hrb1]
        · dsimp only [p2Inv, p3Inv]
          have : r * d * b + 1 + (b - 1) = r * d * b + b + 0 := by omega
          rw [this]
      rw [hP2End] at rP2
      have rP3 := Runs.while1 (w := w)
        (fun _ (sc : Fin 2 → WorkSym) => sc 0 != .blank)
        shearEmitKeepAct actStay ((d - 1 - r) * b) p3Inv
        (fun j hj => by
          have hpos_lt : (r + 1) * b + j < d * b := by
            have : (r + 1) + (d - 1 - r) = d := by omega
            calc (r + 1) * b + j < (r + 1) * b + (d - 1 - r) * b := by omega
              _ = ((r + 1) + (d - 1 - r)) * b := by ring
              _ = d * b := by rw [this]
          have hneB : (p3Inv j).work 0 ((p3Inv j).workPos 0) ≠ .blank := by
            dsimp only [p3Inv]; simp only [Fin.isValue, ↓reduceIte]
            exact tplPrefix_nonblank hpos_lt
          refine ⟨bne_blank_of_ne hneB, ?_⟩
          have hk_lt_dr : b + j < (d - r) * b := by
            have : 1 + (d - 1 - r) = d - r := by omega
            calc b + j < 1 * b + (d - 1 - r) * b := by omega
              _ = (1 + (d - 1 - r)) * b := by ring
              _ = (d - r) * b := by rw [this]
          have hwLt : r * d * b + (r + 1) * b + j < w.length := by
            have : (r + 1) * d * b ≤ d * d * b :=
              Nat.mul_le_mul_right b (Nat.mul_le_mul_right d (by omega))
            nlinarith
          have hOutBit : out[r * d * b + (b + j)]? = some w[r * d * b + (r + 1) * b + j] := by
            have h := rowShear_bit_first A hr hk_lt_dr
            change out[r * d * b + (b + j)]? = w[r * d * b + r * b + (b + j)]? at h
            have heq : r * d * b + r * b + (b + j) = r * d * b + (r + 1) * b + j := by ring
            rw [heq, List.getElem?_eq_getElem hwLt] at h; exact h
          unfold shearEmitKeepAct; rw [applyAct_mkAct1]
          refine Mem.eq_of_fields ?_ (fun i p => ?_) (fun i => ?_) ?_
          · dsimp only [p3Inv, Transpose.Dir.shift]; omega
          · dsimp only [p3Inv]
            fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]
            exact congrFun (ite_self_cell (tplPrefix (d * b) b ((r + 1) * b)) _) p
          · dsimp only [p3Inv, Transpose.Dir.shift]
            fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]; omega
          · dsimp only [p3Inv]
            rw [readInput_of_nonneg, List.getElem?_eq_getElem hwLt]
            have htk := take_succ_of_getElem?_tm hOutBit
            have hidx1 : r * d * b + b + (j + 1) = r * d * b + (b + j) + 1 := by omega
            have hidx2 : r * d * b + (b + j) = r * d * b + b + j := by omega
            rw [hidx1, htk, hidx2, List.reverse_append, List.reverse_singleton]; rfl)
        (by
          dsimp only [p3Inv]; simp only [Fin.isValue, ↓reduceIte]
          have hdb : (r + 1) * b + (d - 1 - r) * b = d * b := by
            have : (r + 1) + (d - 1 - r) = d := by omega
            calc (r + 1) * b + (d - 1 - r) * b = ((r + 1) + (d - 1 - r)) * b := by ring
              _ = d * b := by rw [this]
          rw [hdb, tplPrefix_outside (Or.inr le_rfl)]; rfl)
      rw [applyAct_actStay] at rP3
      -- Phase 4: `rewindFromEnd 0` (`d * b + 2` steps) + `rewindFromEnd 1` (`r * b + 2` steps)
      have hdbEq : (r + 1) * b + (d - 1 - r) * b = d * b := by
        have : (r + 1) + (d - 1 - r) = d := by omega
        calc (r + 1) * b + (d - 1 - r) * b = ((r + 1) + (d - 1 - r)) * b := by ring
          _ = d * b := by rw [this]
      have rRew0 := Runs_rewindFromEnd (w := w) (0 : Fin 2) (p3Inv ((d - 1 - r) * b)) (d * b)
        (by dsimp only [p3Inv]; simp [hdbEq])
        (fun j hj => by dsimp only [p3Inv]; simp only [Fin.isValue, ↓reduceIte]; exact tplPrefix_nonblank hj)
        (by dsimp only [p3Inv]; simp only [Fin.isValue, ↓reduceIte]; exact tplPrefix_outside (Or.inl (by omega)))
      let mAfterR0 : Mem 2 WorkSym :=
        { p3Inv ((d - 1 - r) * b) with
          workPos := fun i => if i = 0 then 0 else (p3Inv ((d - 1 - r) * b)).workPos i }
      have hR0Eq :
          { p3Inv ((d - 1 - r) * b) with
            workPos := fun i => if i = 0 then 0 else (p3Inv ((d - 1 - r) * b)).workPos i } =
          mAfterR0 := rfl
      rw [hR0Eq] at rRew0
      have hwRowTakeLen : (wRow.take (r * b)).length = r * b := by
        dsimp only [wRow]
        rw [List.length_take_of_le]
        rw [List.length_drop, hwLen]
        have h1 : r * d * b + d * b ≤ d * d * b := by
          have : (r + 1) * d * b ≤ d * d * b :=
            Nat.mul_le_mul_right b (Nat.mul_le_mul_right d (by omega))
          linarith
        have h2 : r * b ≤ d * b := Nat.mul_le_mul_right b (by omega)
        omega
      have rRew1 := Runs_rewindFromEnd (w := w) (1 : Fin 2) mAfterR0 (r * b)
        (by dsimp only [mAfterR0, p3Inv]; simp)
        (fun j hj => by
          dsimp only [mAfterR0, p3Inv, savedTape]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
          have hjLen : j < (wRow.take (r * b)).length := by omega
          rw [wordTape_lt (List.getElem?_eq_getElem hjLen)]
          exact bitSym_ne_blank _)
        (by
          dsimp only [mAfterR0, p3Inv, savedTape]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
          exact wordTape_neg (by omega))
      -- Phase 5: emit `r * b` saved bits from Tape 1, then `eraseFromEnd 1`
      let p5Inv (j : ℕ) : Mem 2 WorkSym :=
        { inPos   := (((r + 1) * d * b : ℕ) : Int)
          work    := fun i p =>
            if i = 0 then tplPrefix (d * b) b ((r + 1) * b) p
            else savedTape p
          workPos := fun i => if i = 0 then 0 else (j : Int)
          outRev  := (out.take (r * d * b + (d - r) * b + j)).reverse }
      have hR1End :
          { mAfterR0 with workPos := fun i => if i = 1 then 0 else mAfterR0.workPos i } =
          p5Inv 0 := by
        have hinEq : r * d * b + (r + 1) * b + (d - 1 - r) * b = (r + 1) * d * b := by
          rw [Nat.add_assoc, hdbEq]; ring
        have hdrEq : b + (d - 1 - r) * b = (d - r) * b := by
          have : 1 + (d - 1 - r) = d - r := by omega
          calc b + (d - 1 - r) * b = (1 + (d - 1 - r)) * b := by ring
            _ = (d - r) * b := by rw [this]
        refine Mem.eq_of_fields ?_ (fun _ _ => rfl) (fun i => ?_) ?_
        · dsimp only [mAfterR0, p3Inv, p5Inv]; exact congrArg Nat.cast hinEq
        · dsimp only [mAfterR0, p3Inv, p5Inv]; fin_cases i <;> simp
        · dsimp only [mAfterR0, p3Inv, p5Inv, Nat.add_zero]
          rw [Nat.add_assoc (r * d * b), hdrEq]
      rw [hR1End] at rRew1
      have rP5 := Runs.while1 (w := w)
        (fun _ (sc : Fin 2 → WorkSym) => sc 1 != .blank)
        shearEmitSavedAct actStay (r * b) p5Inv
        (fun j hj => by
          have hj_lt_w : r * d * b + j < w.length := by
            have : (r + 1) * d * b ≤ d * d * b :=
              Nat.mul_le_mul_right b (Nat.mul_le_mul_right d (by omega))
            have : r * b ≤ d * b := Nat.mul_le_mul_right b (by omega)
            nlinarith
          have hSavedGet : (wRow.take (r * b))[j]? = some w[r * d * b + j] := by
            rw [List.getElem?_take_of_lt hj, hwRowGet j hj_lt_w]
          have hcell : (p5Inv j).work 1 ((p5Inv j).workPos 1) ≠ .blank := by
            dsimp only [p5Inv, savedTape]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
            rw [wordTape_lt hSavedGet]; exact bitSym_ne_blank _
          refine ⟨bne_blank_of_ne hcell, ?_⟩
          have hOutBit : out[r * d * b + (d - r) * b + j]? = some w[r * d * b + j] := by
            have h := rowShear_bit_wrap A hr hj
            change out[r * d * b + (d - r) * b + j]? = w[r * d * b + j]? at h
            rw [h, List.getElem?_eq_getElem hj_lt_w]
          unfold shearEmitSavedAct; rw [applyAct_mkAct1]
          refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) ?_
          · dsimp only [p5Inv]
            fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]
            exact congrFun (ite_self_cell savedTape _) p
          · dsimp only [p5Inv, Transpose.Dir.shift]
            fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte]; omega
          · dsimp only [p5Inv, savedTape]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
            rw [wordTape_lt hSavedGet, symBit_bitSym]
            have htk := take_succ_of_getElem?_tm hOutBit
            have hidx : r * d * b + (d - r) * b + (j + 1) = (r * d * b + (d - r) * b + j) + 1 := by omega
            rw [hidx, htk, List.reverse_append, List.reverse_singleton]; rfl)
        (by
          dsimp only [p5Inv, savedTape]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
          rw [wordTape_ge (by rw [hwRowTakeLen])]; rfl)
      rw [applyAct_actStay] at rP5
      have rEr1 := Runs_eraseFromEnd (w := w) (1 : Fin 2) (p5Inv (r * b)) (r * b)
        (by dsimp only [p5Inv]; simp)
        (fun j hj => by
          dsimp only [p5Inv, savedTape]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
          have hjLen : j < (wRow.take (r * b)).length := by omega
          rw [wordTape_lt (List.getElem?_eq_getElem hjLen)]
          exact bitSym_ne_blank _)
        (fun p hp => by
          dsimp only [p5Inv, savedTape]; simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
          rcases hp with hneg | hge
          · exact wordTape_neg hneg
          · exact wordTape_ge (by rw [hwRowTakeLen]; omega))
      have hErEnd :
          { p5Inv (r * b) with
            work    := fun i p => if i = 1 then WorkSym.blank else (p5Inv (r * b)).work i p
            workPos := fun i => if i = 1 then 0 else (p5Inv (r * b)).workPos i } =
          rowInv (r + 1) := by
        have houtIdx : r * d * b + (d - r) * b + r * b = (r + 1) * d * b := by
          have : (d - r) + r = d := Nat.sub_add_cancel (by omega : r ≤ d)
          calc r * d * b + (d - r) * b + r * b
              = r * d * b + ((d - r) + r) * b := by ring
            _ = r * d * b + d * b := by rw [this]
            _ = (r + 1) * d * b := by ring
        refine Mem.eq_of_fields rfl (fun i p => ?_) (fun i => ?_) ?_
        · dsimp only [p5Inv, rowInv]; fin_cases i <;> simp
        · dsimp only [p5Inv, rowInv]; fin_cases i <;> simp
        · dsimp only [p5Inv, rowInv]; rw [houtIdx]
      rw [hErEnd] at rEr1
      have hRowTime :
          ((((((r * b + 1) + b) + ((d - 1 - r) * b + 1)) + (d * b + 2)) + (r * b + 2)) +
            (r * b + 1)) + (r * b + 2) = tRow r := by
        dsimp only [tRow]
        have : r * b + b + (d - 1 - r) * b = d * b := by
          have hsum : r + 1 + (d - 1 - r) = d := by omega
          calc r * b + b + (d - 1 - r) * b = (r + 1 + (d - 1 - r)) * b := by ring
            _ = d * b := by rw [hsum]
        linarith
      rw [← hRowTime]
      exact (((((rP1.seq rP2).seq rP3).seq rRew0).seq rRew1).seq rP5).seq rEr1)
    (by
      dsimp only [rowInv]
      rw [readInput_of_nonneg, List.getElem?_eq_none (by omega)]; rfl)
  rw [hRow0, applyAct_actStay] at hLoop
  refine ⟨_, rowInv d, ?_, hLoop, ?_⟩
  · have hSumLe := natSum_le_of_step (f := fun r => 1 + tRow r)
      (g := fun r => r * (5 * d * b + 10)) (N := d)
      (fun r hr => by
        dsimp only [tRow]
        have : r * b ≤ d * b := Nat.mul_le_mul_right b (by omega)
        nlinarith)
    nlinarith
  · dsimp only [rowInv]
    rw [List.reverse_reverse, List.take_of_length_le (by omega)]

private def rowShearProg : Block 2 WorkSym :=
  (((((discoverEntryBits 0 1).seq (clearUnary 0)).seq divInputByB).seq
    unarySqrtBlock).seq buildRowTemplate).seq streamRowShear

private theorem rowShearTM_twoTape_linear :
    ∃ (M_shear : Transpose.TM) (C_shear : ℕ),
      M_shear.k = 2 ∧
      ∀ (d : ℕ) (A : Transpose.Matrix), 1 ≤ d →
        Transpose.ComputesWithin M_shear
          (Transpose.encode d (Transpose.entryBits d) A)
          (Transpose.encode d (Transpose.entryBits d) (rowShearTMMatrix d A))
          (C_shear * Transpose.inputLength d) := by
  refine ⟨rowShearProg.toTM encWorkSym decWorkSym, 200, rfl, ?_⟩
  intro d A hd1
  set b := Transpose.entryBits d
  set L := Transpose.inputLength d
  set w := Transpose.encode d b A
  have hb1 : 1 ≤ b := entryBits_pos_tm d
  have hL_eq : L = d * d * b := rfl
  have hL1 : 1 ≤ L := inputLength_pos hd1
  have hwLen : w.length = L := (encode_len_get d b A).1
  let m0 : Mem 2 WorkSym :=
    { inPos := 0, work := fun _ _ => .blank, workPos := fun _ => 0, outRev := [] }
  -- 1. `discoverEntryBits 0 1`
  have r1 := Runs_discoverEntryBits (k := 2) (t₀ := 0) (t₁ := 1) (by decide) hd1 hwLen
    m0 rfl rfl rfl rfl rfl
  change Runs (discoverEntryBits 0 1) w m0 _ (120 * L) at r1
  let m1 : Mem 2 WorkSym :=
    { m0 with
      work := fun i p => if i = 0 then unaryTape (4 ^ b) p else unaryTape b p }
  have hm1Eq :
      { m0 with
        work := fun i p =>
          if i = 0 then unaryTape (4 ^ b) p
          else if i = 1 then unaryTape b p
          else m0.work i p } = m1 := by
    refine Mem.eq_of_fields rfl (fun i p => ?_) (fun _ => rfl) rfl
    fin_cases i <;> rfl
  rw [hm1Eq] at r1
  -- 2. `clearUnary 0`
  have r2 := Runs_clearUnary (w := w) (0 : Fin 2) m1 (4 ^ b) rfl rfl
  let m2 : Mem 2 WorkSym :=
    { m0 with work := fun i p => if i = 0 then .blank else unaryTape b p }
  have hm2Eq :
      { m1 with work := fun i p => if i = 0 then .blank else m1.work i p } = m2 := by
    refine Mem.eq_of_fields rfl (fun i p => ?_) (fun _ => rfl) rfl
    fin_cases i <;> rfl
  rw [hm2Eq] at r2
  -- 3. `divInputByB` (`Q = d * d`)
  have r3 := Runs_divInputByB (w := w) m2 (d * d) b hb1 hwLen rfl rfl rfl rfl rfl
  let m3 : Mem 2 WorkSym :=
    { m0 with work := fun i p => if i = 0 then unaryTape (d * d) p else unaryTape b p }
  have hm3Eq :
      { m2 with work := fun i p => if i = 0 then unaryTape (d * d) p else m2.work i p } = m3 := by
    refine Mem.eq_of_fields rfl (fun i p => ?_) (fun _ => rfl) rfl
    fin_cases i <;> rfl
  rw [hm3Eq] at r3
  -- 4. `unarySqrtBlock`
  obtain ⟨t4, ht4, r4⟩ := Runs_unarySqrtBlock (w := w) m3 d b hd1 rfl rfl rfl rfl
  let m4 : Mem 2 WorkSym :=
    { m0 with
      work    := fun i p => if i = 0 then .blank else oddScratch b d p
      workPos := fun i => if i = 0 then 0 else -1 }
  have hm4Eq :
      { m3 with
        work    := fun i p => if i = 0 then .blank else oddScratch b d p
        workPos := fun i => if i = 0 then 0 else -1 } = m4 := rfl
  rw [hm4Eq] at r4
  -- 5. `buildRowTemplate`
  obtain ⟨t5, ht5, r5⟩ := Runs_buildRowTemplate (w := w) m4 d b hd1 hb1 rfl rfl rfl rfl
  let m5 : Mem 2 WorkSym :=
    { m0 with
      work    := fun i p => if i = 0 then tplPrefix (d * b) b 0 p else .blank
      workPos := fun _ => 0 }
  have hm5Eq :
      { m4 with
        work    := fun i p => if i = 0 then tplPrefix (d * b) b 0 p else .blank
        workPos := fun _ => 0 } = m5 := rfl
  rw [hm5Eq] at r5
  -- 6. `streamRowShear`
  obtain ⟨t6, mHalt, ht6, r6, hOut⟩ := Runs_streamRowShear hd1 A m5 rfl rfl rfl rfl rfl rfl
  change mHalt.outRev.reverse = Transpose.encode d b (rowShearTMMatrix d A) at hOut
  have rTotal : Runs rowShearProg w m0 mHalt (200 * L) := by
    unfold rowShearProg
    apply (((((r1.seq r2).seq r3).seq r4).seq r5).seq r6).of_le
    have h4bL : 4 ^ b * b ≤ 4 * L := entryBits_quad_le_four_L hd1
    have h4b : 4 ^ b ≤ 4 ^ b * b := Nat.le_mul_of_pos_right (4 ^ b) hb1
    have hddL : d * d ≤ L := by dsimp [L, Transpose.inputLength]; exact Nat.le_mul_of_pos_right (d * d) hb1
    have hd_le_dd : d ≤ d * d := Nat.le_mul_self d
    have hdbL : d * b ≤ L := by
      have : 1 * (d * b) ≤ d * (d * b) := Nat.mul_le_mul_right (d * b) hd1
      dsimp [L, Transpose.inputLength]; linarith
    have hb_le_db : b ≤ d * b := Nat.le_mul_of_pos_left b hd1
    nlinarith
  exact Block.computesWithin .blank encWorkSym decWorkSym decWorkSym_encWorkSym encWorkSym_blank
    rowShearProg rTotal hOut

end ShufShearTM

theorem diagnosis_StoneShuffleAndRowShearMachineComplexity :
    Diagnosis_StoneShuffleAndRowShearMachineComplexitySpec :=
  ⟨stoneShuffleTM_linear, rowShearTM_twoTape_linear, dyadicCommutatorRank⟩

end BoundedArityDecoders
