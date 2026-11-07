import TapeStorageRates.TraceTransfer
import TapeStorageRates.Conditioning
import MergeDepth.HCStarQ91

/-!
# Actual append-time native storage fibres

Fixing a frequently attained full trace and a bounded-cost genie costs the
sum of the two bills. The output root for each demanded coordinate is a step
that actually appends the required output bit, on every word retained.
-/

namespace TapeStorageRates

open Finset Filter Transpose Transpose.Tape Transpose.Tape.Impl
open MergeDepth BoundedNesting BoundedStackDepth MotionDepthCodes

set_option autoImplicit false

open Classical in
/-- The full motion class of a representative at a fixed raw length. -/
noncomputable def nativeTraceClass {L : ℕ} (M : TM) (x₀ : Fin L → Bool) :
    Finset (Fin L → Bool) :=
  univ.filter fun x => trace M (List.ofFn x) = trace M (List.ofFn x₀)

/-- A native storage-code witness on one common complete trace and one common
genie word. The defining properties include the genuine append at every root. -/
structure NativeFibreWitness (M : TM) (d b : ℕ) (c η ε : ℝ) where
  representative : Fin (d*d*b) → Bool
  time : ℕ
  halt : HaltsAt M (List.ofFn representative) time
  time_le : (time : ℝ) ≤ c * ((d*d*b : ℕ) + 1)
  genie : Finset ℕ
  cost : (blockWidth M 1 * genie.card : ℝ) ≤ ε * (d*d*b : ℕ)
  depth : ∀ π, IsDepPath (fun j => skel 1 (runWalks M (List.ofFn representative)
    (some (some j)))) time π → LinNet.GFree genie π →
    π.length ≤ genieDepth M.k (blockWidth M 1) (max c 1) ε + 1
  outputTime : ℕ → ℕ
  code : Finset (Fin (d*d*b) → Bool)
  representative_mem : representative ∈ code
  common_trace : code ⊆ nativeTraceClass M representative
  common_genie : ∀ x ∈ code, ∀ t ∈ genie,
    blockVal M 1 (List.ofFn x) t = blockVal M 1 (List.ofFn representative) t
  append : ∀ x ∈ code, ∀ q : Fin (d*d*b), outputTime q < time ∧
    (run M (List.ofFn x) (outputTime q)).outRev.length = q.val ∧
    (run M (List.ofFn x) (outputTime q+1)).outRev.length = q.val+1
  storage : IsStorageCode (coneRel 1 (runWalks M (List.ofFn representative)) time genie
    outputTime (fun q => MergeDepth.tpos d b q)) code
  trace_size : (1-η) * (d*d*b : ℕ) ≤ Real.logb 2 (nativeTraceClass M representative).card
  code_size : (1-η-ε) * (d*d*b : ℕ) ≤ Real.logb 2 code.card

/-- The last visit to the output count `q` at scale one is the actual append:
the native count is `q` before this step and `q+1` immediately after it. -/
theorem scale_one_output_appends {M : TM} {σ : Skeleton M.k} {x : List Bool}
    (hx : InClass M 1 σ x) {q : ℕ} (hq : q < (run M x σ.T).outRev.length) :
    outTime σ 1 q < σ.T ∧ (run M x (outTime σ 1 q)).outRev.length = q ∧
      (run M x (outTime σ 1 q+1)).outRev.length = q+1 := by
  obtain ⟨ht,hat,hlast,_⟩ := outTime_spec hx hq
  obtain ⟨u,hu,hu0,hu1⟩ := exists_append_step x σ.T hq
  have hcount : (run M x (outTime σ 1 q)).outRev.length = q := by
    simpa only [Nat.div_one] using ((hx.2 _ ht).2.2.trans hat)
  have he : u = outTime σ 1 q := by
    apply Nat.le_antisymm
    · by_contra! hlate
      apply hlast u hlate hu
      rw [← (hx.2 u hu).2.2,hu0]
    · by_contra! hearly
      have hmono := outRev_length_mono (M := M) x (show u+1≤outTime σ 1 q from hearly)
      rw [hu1,hcount] at hmono
      omega
  exact ⟨ht,hcount,he ▸ hu1⟩

/-- Correctness supplies halting, so equality of complete motion traces puts the word in
the representative's actual scale-one skeleton class. -/
theorem native_inClass_of_trace_eq {M : TM} {d b : ℕ} {c : ℝ} {x y : Fin (d*d*b) → Bool}
    (hx : TransposesInput M d b c x) (htr : trace M (List.ofFn x) = trace M (List.ofFn y)) :
    InClass M 1 (runSkeleton M 1 (List.ofFn y)) (List.ofFn x) := by
  rw [inClass_iff_runSkeleton, runSkeleton_normalize]
  obtain ⟨t, _, ht⟩ := hx.halts
  exact ⟨⟨t,ht⟩, by simpa only [skeletonOfTrace_eq] using congrArg (skeletonOfTrace 1) htr⟩

theorem native_class_time {M : TM} {d b : ℕ} {c : ℝ} {σ : Skeleton M.k} (hc : 0 ≤ c)
    {x : Fin (d*d*b) → Bool} (hx : InClass M 1 σ (List.ofFn x)) (hgood : TransposesInput M d b c x) :
    (σ.T : ℝ) ≤ c*((d*d*b : ℕ)+1) := by
  obtain ⟨t,ht,halt⟩ := hgood.halts
  obtain rfl := haltsAt_unique halt hx.1
  exact (Nat.cast_le.mpr ht).trans (Nat.floor_le (by positivity))

theorem native_class_output {M : TM} {d b : ℕ} {σ : Skeleton M.k} {x : Fin (d*d*b) → Bool}
    (hx : InClass M 1 σ (List.ofFn x)) (hgood : OutputsTranspose M d b x) :
    (run M (List.ofFn x) σ.T).outRev.length = d*d*b ∧
      ∀ q : Fin (d*d*b), (run M (List.ofFn x) σ.T).outRev.reverse[MergeDepth.tpos d b q]? = some (x q) := by
  obtain ⟨t,halt,hlen,hout⟩ := hgood.output
  obtain rfl := haltsAt_unique halt hx.1
  exact ⟨by simpa using hlen, by simpa only [tape_tpos_eq] using hout⟩

/-- On any set of correct inputs in one skeleton class, equality on the actual revealed
values and the root cone suffices for the demanded bit. -/
theorem native_class_decode {M : TM} {d b : ℕ} (hb : 0<b) {σ : Skeleton M.k} {Γ : Finset ℕ}
    {x y : Fin (d*d*b) → Bool} (hx : InClass M 1 σ (List.ofFn x))
    (hy : InClass M 1 σ (List.ofFn y)) (gx : OutputsTranspose M d b x) (gy : OutputsTranspose M d b y)
    (hΓ : ∀ t ∈ Γ, blockVal M 1 (List.ofFn x) t = blockVal M 1 (List.ofFn y) t)
    (q : Fin (d*d*b)) (hJ : ∀ u ∈ (blockMachine M (by decide : 0<1) _ σ).coneJ Γ
      (outTime σ 1 (MergeDepth.tpos d b q)), x u = y u) : x q = y q := by
  obtain ⟨lx,vx⟩ := native_class_output hx gx
  obtain ⟨ly,vy⟩ := native_class_output hy gy
  have hq := MergeDepth.tpos_lt hb q.isLt
  have h := blockMachine_output_eq (by decide : 0<1) σ Γ (mem_skelClass.mpr hx)
    (mem_skelClass.mpr hy) (fun t ht _ => hΓ t ht) (hq.trans_le lx.ge) (hq.trans_le ly.ge) hJ
  exact Option.some.inj ((vx q).symm.trans (h.trans (vy q)))

/-- The bounded-depth genie of one native skeleton class, charged at the actual record width. -/
theorem native_class_genie {M : TM} {σ : Skeleton M.k} {w : List Bool} (hclass : InClass M 1 σ w)
    {L : ℕ} (hlen : 0 < L) {c ε : ℝ} (hT : (σ.T : ℝ) ≤ c*((L:ℝ)+1)) (hε : 0<ε) :
    ∃ Γ : Finset ℕ, (blockWidth M 1 * Γ.card : ℝ) ≤ ε*L ∧
      ∀ π, IsDepPath σ.s σ.T π → LinNet.GFree Γ π →
        π.length ≤ genieDepth M.k (blockWidth M 1) (max c 1) ε + 1 := by
  have htime := hT.trans (mul_le_mul_of_nonneg_right (le_max_left c 1) (by positivity))
  obtain ⟨Γ,hcost,hdepth⟩ := genie_cost (k := M.k) (one_le_blockWidth M 1) hlen
    (le_max_right c 1) hε htime (fun j => skel 1 (workWalk M w j))
    (fun j => isWalk_skel (by decide : (0:ℤ)<1) (workWalk_isWalk _ j))
  have hagree : ∀ j t, t<σ.T → σ.s j t = skel 1 (workWalk M w j) t :=
    fun j t ht => ((hclass.2 t ht).2.1 j).symm
  exact ⟨Γ,hcost,fun π hπ hf => (hdepth π ((isDepPath_congr hagree π).mp hπ) hf).trans
    (Nat.le_succ _)⟩

private theorem log_card_pay {m a n : ℕ} (hm : 0 < m) (ha : 0 < a) (hn : 0 < n)
    (h : m ≤ a*n) : Real.logb 2 m ≤ Real.logb 2 a + Real.logb 2 n := by
  have hh := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2)
    (by exact_mod_cast hm : (0 : ℝ) < m) (by exact_mod_cast h : (m : ℝ) ≤ (a : ℝ)*n)
  rwa [Real.logb_mul (by positivity) (by positivity)] at hh

open Classical in
/-- Any successful machine at a single dimension whose actual trace support
costs at most `ηL` has a code on genuine append-time cones of rate at least
`1-η-ε`. No coding bound is a premise. -/
theorem native_fibre_of_trace_support (M : TM) {d b : ℕ} (hd : 0<d) (hb : 0<b)
    {c η ε : ℝ} (hc : 0<c) (hε : 0<ε) (hgood : TransposesAtWidth M d b c)
    (hsupport : Real.logb 2 (univ.image (fun x : Fin (d*d*b) → Bool => trace M (List.ofFn x))).card
      ≤ η * (d*d*b : ℕ)) : Nonempty (NativeFibreWitness M d b c η ε) := by
  let L := d*d*b
  let β := blockWidth M 1
  let tr (x : Fin L → Bool) := trace M (List.ofFn x)
  obtain ⟨τ,hτ,hS⟩ := exists_large_observation_fibre (S := (univ : Finset (Fin L → Bool)))
    univ_nonempty tr
  obtain ⟨x₀,_,rfl⟩ := mem_image.mp hτ
  let S := univ.filter (fun x => tr x = tr x₀)
  have hx₀ : x₀ ∈ S := mem_filter.mpr ⟨mem_univ _,rfl⟩
  have hSne : S.Nonempty := ⟨_,hx₀⟩
  have hpay₁ := log_card_pay (univ_nonempty.card_pos (α := Fin L → Bool))
    (univ_nonempty.image tr).card_pos hSne.card_pos hS
  have hScard : (1-η)*(L:ℝ) ≤ Real.logb 2 S.card := by
    simp only [card_univ,Fintype.card_fun,Fintype.card_fin,Fintype.card_bool,Nat.cast_pow,
      Nat.cast_ofNat,Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1:ℝ)<2),mul_one] at hpay₁
    change _ ≤ η*(L:ℝ) at hsupport
    change (L:ℝ) ≤ Real.logb 2 (univ.image tr).card + Real.logb 2 S.card at hpay₁
    linarith
  let σ := runSkeleton M 1 (List.ofFn x₀)
  have hσ {x} (hx : x∈S) : InClass M 1 σ (List.ofFn x) :=
    native_inClass_of_trace_eq (hgood.transposesInput x) (mem_filter.mp hx).2
  have hclass := hσ hx₀
  have hT := native_class_time hc.le hclass (hgood.transposesInput x₀)
  have hlen : 0 < L := Nat.mul_pos (Nat.mul_pos hd hd) hb
  obtain ⟨Γ,hcost,hpath⟩ := native_class_genie hclass hlen hT hε
  let E (x : Fin L → Bool) := fun t : Γ => blockVal M 1 (List.ofFn x) t
  have hcap : (S.image E).card ≤ 2^(β*Γ.card) := card_revealed_le (M := M) (by decide : 0<1) Γ S
  obtain ⟨e,he,hF⟩ := exists_large_observation_fibre hSne E
  obtain ⟨x₁,hx₁,rfl⟩ := mem_image.mp he
  let F := S.filter (fun x => E x = E x₁)
  have hx₁F : x₁ ∈ F := mem_filter.mpr ⟨hx₁,rfl⟩
  have htrace : S = nativeTraceClass M x₁ := by
    have htr : tr x₁ = tr x₀ := (mem_filter.mp hx₁).2
    ext x
    change x ∈ univ.filter (fun x => tr x=tr x₀) ↔ x ∈ univ.filter (fun x => tr x=tr x₁)
    rw [htr]
  have hcostlog : Real.logb 2 (S.image E).card ≤ ε*L := by
    have hh := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2)
      (by exact_mod_cast (hSne.image E).card_pos : (0:ℝ)<(S.image E).card)
      (by exact_mod_cast hcap : ((S.image E).card : ℝ) ≤ ((2^(β*Γ.card) : ℕ) : ℝ))
    simp only [Nat.cast_pow,Nat.cast_ofNat,Real.logb_pow,
      Real.logb_self_eq_one (by norm_num : (1:ℝ)<2),mul_one,Nat.cast_mul] at hh
    exact hh.trans hcost
  have hfsize := log_card_pay hSne.card_pos (hSne.image E).card_pos
    (show F.Nonempty from ⟨_,hx₁F⟩).card_pos hF
  have hFc : (1-η-ε)*(L:ℝ) ≤ Real.logb 2 F.card := by linarith
  have hctx := hσ hx₁
  have hcomplete {x} (hx : x∈S) := (native_class_output (hσ hx) (hgood.transposesInput x).outputsTranspose).1.ge
  obtain ⟨hdepthR,_,hcone⟩ := classRel_subset_coneRel (by decide : 0<1) hb
    (mem_skelClass.mpr hctx) (hcomplete hx₁) hpath
  refine ⟨{
    representative := x₁, time := σ.T, halt := hctx.1, time_le := hT
    genie := Γ, cost := hcost, depth := hdepthR, outputTime := outTime σ 1
    code := F, representative_mem := hx₁F, common_trace := htrace ▸ filter_subset _ _
    common_genie := fun _ hx t ht => congrFun (mem_filter.mp hx).2 ⟨t,ht⟩
    append := fun _ hx q => scale_one_output_appends (hσ (mem_filter.mp hx).1)
      (q.isLt.trans_le (hcomplete (mem_filter.mp hx).1))
    storage := ?_, trace_size := htrace ▸ hScard, code_size := hFc }⟩
  intro x hx y hy q hxy
  exact native_class_decode hb (hσ (mem_filter.mp hx).1) (hσ (mem_filter.mp hy).1)
    (hgood.transposesInput x).outputsTranspose (hgood.transposesInput y).outputsTranspose
    (fun t ht => congrFun ((mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm) ⟨t,ht⟩)
    q (fun u hu => hxy u (hcone q hu))

private theorem append_flag_of_count {M : TM} {w : List Bool} {t : ℕ}
    (h : (run M w t).outRev.length < (run M w (t+1)).outRev.length) :
    (trace M w).appends t = true := by
  rw [outRev_length_succ,outBit_isSome_eq] at h
  split_ifs at h with ha
  · exact ha
  · omega

/-- Every recorded root has its append flag set on every retained native run. -/
theorem NativeFibreWitness.appends {M : TM} {d b : ℕ} {c η ε : ℝ}
    (F : NativeFibreWitness M d b c η ε) {x} (hx : x∈F.code) (q : Fin (d*d*b)) :
    (trace M (List.ofFn x)).appends (F.outputTime q) = true := by
  obtain ⟨_,h0,h1⟩ := F.append x hx q
  exact append_flag_of_count (by rw [h0,h1]; omega)

/-- On every trace the append list sends a flagged step's output ordinal back to that step. -/
theorem appendTime_at_flag {k : ℕ} (τ : Trace k) {t T : ℕ} (ht : t < T) (ha : τ.appends t = true) :
    appendTime τ T (appendList τ t).length = t := by
  obtain ⟨i,hi,hit⟩ := List.getElem_of_mem (show t ∈ appendList τ T from
    List.mem_filter.mpr ⟨List.mem_range.mpr ht,ha⟩)
  have ht' := (appendTime_eq_getElem τ T hi).trans hit
  have hcount := appendCount_appendTime τ T hi
  change ((appendList τ (appendTime τ T i)).length : ℤ) = i at hcount
  rw [ht'] at hcount
  rwa [show (appendList τ t).length = i by exact_mod_cast hcount]

/-- The step that raises the output count from q to q+1 is its actual append time. -/
theorem actual_append_time {M : TM} (w : List Bool) {T t q : ℕ} (ht : t < T)
    (h0 : (run M w t).outRev.length = q) (h1 : (run M w (t+1)).outRev.length = q+1) :
    t = appendTime (trace M w) T q := by
  have ha := append_flag_of_count (by rw [h0,h1]; omega :
    (run M w t).outRev.length < (run M w (t+1)).outRev.length)
  rw [← h0,outRev_length_eq_appendList]
  exact (appendTime_at_flag _ ht ha).symm

/-- The witness root literally equals Paper 11's q-th actual append time. -/
theorem NativeFibreWitness.outputTime_eq_appendTime {M : TM} {d b : ℕ} {c η ε : ℝ}
    (F : NativeFibreWitness M d b c η ε) {x} (hx : x∈F.code) (q : Fin (d*d*b)) :
    F.outputTime q = appendTime (trace M (List.ofFn x)) F.time q := by
  obtain ⟨ht,h0,h1⟩ := F.append x hx q
  exact actual_append_time _ ht h0 h1

/-- Fix one aligned simulator before dimensions grow. At every sufficiently
large successful dimension it has an actual native fibre paying only the two
specified rates, with the value width of that simulator. -/
theorem aligned_native_fibres (M : TM) {c η ε : ℝ} (hc : 0<c) (hη : 0<η) (hε : 0<ε) :
    ∃ s : ℕ, ∃ hs : 0<s, ∃ c' : ℝ, 0<c' ∧ ∀ᶠ d : ℕ in atTop,
      TransposesAt M d c → Nonempty (NativeFibreWitness (Native.machine M hs) d (entryBits d) c' η ε) := by
  obtain ⟨s,hs,h⟩ := aligned_low_trace_dimensions M hc.le hη
  have ht : 0 < 11*c+1 := by positivity
  refine ⟨s,hs,11*c+1,ht,?_⟩
  filter_upwards [h,eventually_ge_atTop 1] with d hd hpos
  intro hgood
  obtain ⟨htr,hcount⟩ := hd (entryBits d) (one_le_entryBits d) hgood
  exact native_fibre_of_trace_support _ hpos (one_le_entryBits d) ht hε htr hcount

/-- The paper's native witness: at least `2^(3L/4)` inputs share one true
motion trace and at least `2^(5L/8)` share the actual genie word and recover
at their actual append steps. This assumes only successful native transposition. -/
theorem native_five_eighths (M : TM) {c : ℝ} (hc : 0<c) :
    ∃ s : ℕ, ∃ hs : 0<s, ∃ c' : ℝ, 0<c' ∧ ∀ᶠ d : ℕ in atTop, TransposesAt M d c →
      ∃ F : NativeFibreWitness (Native.machine M hs) d (entryBits d) c' (1/4) (1/8),
        (2:ℝ) ^ ((3/4:ℝ)*(d*d*entryBits d:ℕ)) ≤
          (nativeTraceClass (Native.machine M hs) F.representative).card ∧
        (2:ℝ) ^ ((5/8:ℝ)*(d*d*entryBits d:ℕ)) ≤ F.code.card := by
  obtain ⟨s,hs,c',hc',h⟩ := aligned_native_fibres M hc (by norm_num : 0<(1/4:ℝ))
    (by norm_num : 0<(1/8:ℝ))
  refine ⟨s,hs,c',hc',?_⟩
  filter_upwards [h] with d hd
  intro hsuccess
  obtain ⟨F⟩ := hd hsuccess
  have hF : F.code.Nonempty := ⟨_,F.representative_mem⟩
  have hT : (nativeTraceClass (Native.machine M hs) F.representative).Nonempty :=
    hF.mono F.common_trace
  refine ⟨F,?_,?_⟩
  · apply (Real.le_logb_iff_rpow_le (by norm_num : (1:ℝ)<2)
      (by exact_mod_cast hT.card_pos)).mp
    convert F.trace_size using 1
    ring
  · apply (Real.le_logb_iff_rpow_le (by norm_num : (1:ℝ)<2)
      (by exact_mod_cast hF.card_pos)).mp
    convert F.code_size using 1
    ring

end TapeStorageRates
