import TapeStorageRates.NativeFibre
import TapeStorageRates.FiniteTransfer

/-! # A bounded-depth cut and two coordinate trims on an attained native trace -/

namespace TapeStorageRates

open Finset Transpose Transpose.Tape Transpose.Tape.Impl
open MergeDepth BoundedNesting BoundedStackDepth DirectedRecovery MotionDepthCodes

set_option autoImplicit false

noncomputable abbrev nativeConeFan (M : TM) (c ε : ℝ) :=
  packetFan M.k (genieDepth M.k (blockWidth M 1) (max c 1) ε)

open Classical in
/-- Geometry and decoding on a nonempty set of timely correct raw inputs following one trace.
The retained coordinates are nested subtypes of the original input positions. -/
structure NativeTypicalCut (M : TM) (d b : ℕ) (c ε : ℝ) (θ r : ℕ)
    (S : Finset (Fin (d*d*b) → Bool))
    (D : ℕ := genieDepth M.k (blockWidth M 1) (max c 1) ε) where
  representative : Fin (d*d*b) → Bool
  representative_mem : representative ∈ S
  common_trace : ∀ x ∈ S, trace M (List.ofFn x) = trace M (List.ofFn representative)
  time : ℕ
  halt : ∀ x ∈ S, HaltsAt M (List.ofFn x) time
  time_le : (time : ℝ) ≤ c * ((d*d*b : ℕ) + 1)
  genie : Finset ℕ
  record_count : ((S.image fun x => fun t : genie => blockVal M 1 (List.ofFn x) t).card : ℝ) ≤
    (2:ℝ) ^ (ε * (d*d*b : ℕ))
  depth : ∀ π, IsDepPath (fun j => (runWalks M (List.ofFn representative)) (some (some j)))
    time π → LinNet.GFree genie π → π.length ≤ D + 1
  outputTime : ℕ → ℕ
  append : ∀ x ∈ S, ∀ q : Fin (d*d*b),
    outputTime q = appendTime (trace M (List.ofFn x)) time q
  decode : ∀ x ∈ S, ∀ y ∈ S, (∀ t ∈ genie,
    blockVal M 1 (List.ofFn x) t = blockVal M 1 (List.ofFn y) t) → ∀ q : Fin (d*d*b),
    (∀ u ∈ coneRel 1 (runWalks M (List.ofFn representative)) time genie outputTime
      (fun v : Fin (d*d*b) => MergeDepth.tpos d b v) q, x u = y u) → x q = y q
  Q : Finset (Fin (d*d*b))
  U : Finset Q
  retention : ((d*d*b : ℕ) : ℝ) ≤ U.card + (packetFan M.k D : ℝ) * (d*d*b : ℕ) / (θ+1) +
    shortPairCost M.k (packetFan M.k D) θ r c * ((d*d*b : ℕ) / Real.logb 2 d)
  degree : ∀ v, (pairedIncidenceGraph (inducedNeighborhood (inducedNeighborhood
    (coneRel 1 (runWalks M (List.ofFn representative)) time genie outputTime
      (fun q : Fin (d*d*b) => MergeDepth.tpos d b q)) Q) U)).degree v ≤ max (packetFan M.k D) θ
  far : ∀ q : U, ¬ (pairedIncidenceGraph (inducedNeighborhood (inducedNeighborhood
    (coneRel 1 (runWalks M (List.ofFn representative)) time genie outputTime
      (fun q : Fin (d*d*b) => MergeDepth.tpos d b q)) Q) U)).edist (Sum.inl q) (Sum.inr q) ≤ r

open Classical in
/-- Decode and trim at any physical depth, charging the joint record support. -/
theorem exists_native_typical_cut_of_genie (M : TM) {d b : ℕ} (hd : 2 ≤ d) (hb : 1 ≤ b)
    {c ε : ℝ} (hc : 0<c) {S : Finset (Fin (d*d*b) → Bool)}
    {x₀ : Fin (d*d*b) → Bool} (hx₀ : x₀ ∈ S)
    (htr : ∀ x ∈ S, trace M (List.ofFn x) = trace M (List.ofFn x₀))
    (hgood : ∀ x ∈ S, TransposesInput M d b c x) (θ r : ℕ)
    {D : ℕ} (Γ : Finset ℕ)
    (hcount : ((S.image fun x => fun t : Γ => blockVal M 1 (List.ofFn x) t).card : ℝ) ≤
      (2:ℝ) ^ (ε * (d*d*b : ℕ)))
    (hpath : ∀ π, IsDepPath (runSkeleton M 1 (List.ofFn x₀)).s
      (runSkeleton M 1 (List.ofFn x₀)).T π → LinNet.GFree Γ π → π.length ≤ D + 1) :
    Nonempty (NativeTypicalCut M d b c ε θ r S D) := by
  classical
  let L := d*d*b
  let σ := runSkeleton M 1 (List.ofFn x₀)
  have hσ {x} (hx : x∈S) : InClass M 1 σ (List.ofFn x) :=
    native_inClass_of_trace_eq (hgood x hx) (htr x hx)
  have hcomplete {x} (hx : x∈S) := (native_class_output (hσ hx) (hgood x hx).outputsTranspose).1.ge
  have hT := native_class_time hc.le (hσ hx₀) (hgood x₀ hx₀)
  obtain ⟨hdepthR, hotR, hcone⟩ := classRel_subset_coneRel (by decide : 0<1) hb
    (mem_skelClass.mpr (hσ hx₀)) (hcomplete hx₀) hpath
  simp only [Nat.cast_one, skel_one] at hdepthR
  simp only [Nat.cast_one, Int.ediv_one] at hotR
  obtain ⟨Q,U,hheavy,hshort,hdeg,hfar⟩ := packet_schedule_trim hd hb _ (runWalks_isWalk M _)
    Γ _ hdepthR hotR hc.le (by simpa only [L, Nat.cast_mul] using hT) θ r
  refine ⟨{
    representative := x₀, representative_mem := hx₀, common_trace := htr
    time := σ.T, halt := fun _ hx => (hσ hx).1, time_le := hT, genie := Γ, record_count := hcount
    depth := hdepthR, outputTime := outTime σ 1, Q := Q, U := U, degree := hdeg, far := hfar
    append := ?_, decode := ?_, retention := ?_ }⟩
  · intro x hx q
    obtain ⟨ht,h0,h1⟩ := scale_one_output_appends (hσ hx) (q.isLt.trans_le (hcomplete hx))
    exact actual_append_time _ ht h0 h1
  · intro x hx y hy hxy q hN
    exact native_class_decode hb (hσ hx) (hσ hy) (hgood x hx).outputsTranspose
      (hgood y hy).outputsTranspose hxy q (fun u hu => hN u (hcone q hu))
  · exact packet_trim_retention hheavy hshort

/-- The original whole-step genie is a constructor of the support-based interface. -/
theorem exists_native_typical_cut (M : TM) {d b : ℕ} (hd : 2 ≤ d) (hb : 1 ≤ b)
    {c ε : ℝ} (hc : 0<c) (hε : 0<ε) {S : Finset (Fin (d*d*b) → Bool)}
    {x₀ : Fin (d*d*b) → Bool} (hx₀ : x₀ ∈ S)
    (htr : ∀ x ∈ S, trace M (List.ofFn x) = trace M (List.ofFn x₀))
    (hgood : ∀ x ∈ S, TransposesInput M d b c x) (θ r : ℕ) :
    Nonempty (NativeTypicalCut M d b c ε θ r S) := by
  classical
  have hσ := native_inClass_of_trace_eq (hgood x₀ hx₀) (htr x₀ hx₀)
  have hT := native_class_time hc.le hσ (hgood x₀ hx₀)
  have hlen : 0 < d*d*b := Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) hb
  obtain ⟨Γ,hcost,hpath⟩ := native_class_genie hσ hlen hT hε
  refine exists_native_typical_cut_of_genie M hd hb hc hx₀ htr hgood θ r Γ ?_ hpath
  calc
    _ ≤ ((2 ^ (blockWidth M 1 * Γ.card) : ℕ) : ℝ) :=
      Nat.cast_le.mpr (card_revealed_le (M := M) (by decide : 0<1) Γ S)
    _ ≤ _ := by
      simp only [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      simpa only [Nat.cast_mul] using hcost

end TapeStorageRates
