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
    (S : Finset (Fin (d*d*b) → Bool)) where
  representative : Fin (d*d*b) → Bool
  representative_mem : representative ∈ S
  common_trace : ∀ x ∈ S, trace M (List.ofFn x) = trace M (List.ofFn representative)
  time : ℕ
  halt : ∀ x ∈ S, HaltsAt M (List.ofFn x) time
  time_le : (time : ℝ) ≤ c * ((d*d*b : ℕ) + 1)
  genie : Finset ℕ
  cost : (blockWidth M 1 * genie.card : ℝ) ≤ ε * (d*d*b : ℕ)
  depth : ∀ π, IsDepPath (fun j => (runWalks M (List.ofFn representative)) (some (some j)))
    time π → LinNet.GFree genie π → π.length ≤ genieDepth M.k (blockWidth M 1) (max c 1) ε + 1
  outputTime : ℕ → ℕ
  append : ∀ x ∈ S, ∀ q : Fin (d*d*b),
    outputTime q = appendTime (trace M (List.ofFn x)) time q
  decode : ∀ x ∈ S, ∀ y ∈ S, (∀ t ∈ genie,
    blockVal M 1 (List.ofFn x) t = blockVal M 1 (List.ofFn y) t) → ∀ q : Fin (d*d*b),
    (∀ u ∈ coneRel 1 (runWalks M (List.ofFn representative)) time genie outputTime
      (fun v : Fin (d*d*b) => MergeDepth.tpos d b v) q, x u = y u) → x q = y q
  Q : Finset (Fin (d*d*b))
  U : Finset Q
  retention : ((d*d*b : ℕ) : ℝ) ≤ U.card + (nativeConeFan M c ε : ℝ) * (d*d*b : ℕ) / (θ+1) +
    shortPairCost M.k (nativeConeFan M c ε) θ r c * ((d*d*b : ℕ) / Real.logb 2 d)
  degree : ∀ v, (pairedIncidenceGraph (inducedNeighborhood (inducedNeighborhood
    (coneRel 1 (runWalks M (List.ofFn representative)) time genie outputTime
      (fun q : Fin (d*d*b) => MergeDepth.tpos d b q)) Q) U)).degree v ≤ max (nativeConeFan M c ε) θ
  far : ∀ q : U, ¬ (pairedIncidenceGraph (inducedNeighborhood (inducedNeighborhood
    (coneRel 1 (runWalks M (List.ofFn representative)) time genie outputTime
      (fun q : Fin (d*d*b) => MergeDepth.tpos d b q)) Q) U)).edist (Sum.inl q) (Sum.inr q) ≤ r

/-- Choose a cut and retained bit coordinates on any attained correct trace, regardless of
how unlikely that trace is. Its inputs may form an arbitrary subset of the trace class. -/
theorem exists_native_typical_cut (M : TM) {d b : ℕ} (hd : 2 ≤ d) (hb : 1 ≤ b)
    {c ε : ℝ} (hc : 0<c) (hε : 0<ε) {S : Finset (Fin (d*d*b) → Bool)}
    {x₀ : Fin (d*d*b) → Bool} (hx₀ : x₀ ∈ S)
    (htr : ∀ x ∈ S, trace M (List.ofFn x) = trace M (List.ofFn x₀))
    (hgood : ∀ x ∈ S, TransposesInput M d b c x) (θ r : ℕ) :
    Nonempty (NativeTypicalCut M d b c ε θ r S) := by
  classical
  let L := d*d*b
  let σ := runSkeleton M 1 (List.ofFn x₀)
  have hσ {x} (hx : x∈S) : InClass M 1 σ (List.ofFn x) :=
    native_inClass_of_trace_eq (hgood x hx) (htr x hx)
  have hcomplete {x} (hx : x∈S) := (native_class_output (hσ hx) (hgood x hx).outputsTranspose).1.ge
  have hT := native_class_time hc.le (hσ hx₀) (hgood x₀ hx₀)
  have hlen : 0<L := Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) hb
  obtain ⟨Γ,hcost,hpath⟩ := native_class_genie (hσ hx₀) hlen hT hε
  obtain ⟨hdepthR, hotR, hcone⟩ := classRel_subset_coneRel (by decide : 0<1) hb
    (mem_skelClass.mpr (hσ hx₀)) (hcomplete hx₀) hpath
  simp only [Nat.cast_one, skel_one] at hdepthR
  simp only [Nat.cast_one, Int.ediv_one] at hotR
  obtain ⟨Q,U,hheavy,hshort,hdeg,hfar⟩ := packet_schedule_trim hd hb _ (runWalks_isWalk M _)
    Γ _ hdepthR hotR hc.le (by simpa only [L, Nat.cast_mul] using hT) θ r
  refine ⟨{
    representative := x₀, representative_mem := hx₀, common_trace := htr
    time := σ.T, halt := fun _ hx => (hσ hx).1, time_le := hT, genie := Γ, cost := hcost
    depth := hdepthR, outputTime := outTime σ 1, Q := Q, U := U, degree := hdeg, far := hfar
    append := ?_, decode := ?_, retention := ?_ }⟩
  · intro x hx q
    obtain ⟨ht,h0,h1⟩ := scale_one_output_appends (hσ hx) (q.isLt.trans_le (hcomplete hx))
    exact actual_append_time _ ht h0 h1
  · intro x hx y hy hxy q hN
    exact native_class_decode hb (hσ hx) (hσ hy) (hgood x hx).outputsTranspose
      (hgood y hy).outputsTranspose hxy q (fun u hu => hN u (hcone q hu))
  · exact packet_trim_retention hheavy hshort

end TapeStorageRates
