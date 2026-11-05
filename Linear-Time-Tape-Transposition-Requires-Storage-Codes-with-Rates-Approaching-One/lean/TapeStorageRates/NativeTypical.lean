import TapeStorageRates.NativeCutCells

/-! # Exponential mass bound for small fibres on actual native cones

A cut and geometry policy is fixed for each attained trace before choosing an input in it.
The two trims and the alphabet of exposed values may differ on every trace.
-/

namespace TapeStorageRates

open Finset Transpose MergeDepth DirectedRecovery MotionDepthCodes

set_option autoImplicit false
noncomputable section

open Classical in
/-- Full motion traces attained by a specified finite input set. -/
def nativeTraceSupport {L : ℕ} (M : TM) (G : Finset (Fin L → Bool)) : Finset (Trace M.k) :=
  G.image fun x => trace M (List.ofFn x)

open Classical in
/-- Inputs of G which take this particular full trace. -/
def nativeTraceSlice {L : ℕ} (M : TM) (G : Finset (Fin L → Bool)) (τ : Trace M.k) :
    Finset (Fin L → Bool) := G.filter fun x => trace M (List.ofFn x) = τ

/-- One geometry choice per attained full trace. -/
structure NativeTypicalPartition (M : TM) (d b : ℕ) (c ε : ℝ) (θ r : ℕ)
    (G : Finset (Fin (d*d*b) → Bool)) where
  onTrace : ∀ τ : nativeTraceSupport M G,
    NativeTypicalCut M d b c ε θ r (nativeTraceSlice M G τ)

/-- Every set of timely, correct inputs admits such a policy. No condition is imposed on
the other inputs of the same length. -/
theorem native_typical_partition (M : TM) {d b : ℕ} (hd : 2 ≤ d) (hb : 1 ≤ b)
    {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) (G : Finset (Fin (d*d*b) → Bool))
    (hgood : ∀ x ∈ G, TransposesInput M d b c x) (θ r : ℕ) :
    Nonempty (NativeTypicalPartition M d b c ε θ r G) := by
  classical
  refine ⟨⟨fun τ => Classical.choice ?_⟩⟩
  obtain ⟨x₀,hx₀,he⟩ := mem_image.mp τ.property
  have hxS : x₀ ∈ nativeTraceSlice M G τ := mem_filter.mpr ⟨hx₀,he⟩
  exact exists_native_typical_cut M hd hb hc hε hxS
    (fun _ hx => (mem_filter.mp hx).2.trans he.symm)
    (fun x hx => hgood x (mem_filter.mp hx).1) θ r

namespace NativeTypicalPartition

variable {M : TM} {d b θ r : ℕ} {c ε : ℝ} {G : Finset (Fin (d*d*b) → Bool)}

/-- A raw input determines the attained trace used to select its cut. -/
def traceKey (M : TM) {L : ℕ} {G : Finset (Fin L → Bool)} (x : G) : nativeTraceSupport M G :=
  ⟨trace M (List.ofFn x.val), by classical exact mem_image_of_mem _ x.property⟩

variable (P : NativeTypicalPartition M d b c ε θ r G)

abbrev cut (x : G) := P.onTrace (traceKey M x)

abbrev code (x : G) := (P.cut x).code x.val

theorem projected_mem (x : G) :
    restrictWord (P.cut x).U (restrictWord (P.cut x).Q x.val) ∈ P.code x :=
  (P.cut x).projected_mem (by classical exact mem_filter.mpr ⟨x.property,rfl⟩)

/-- Absolute deficit on the retained physical coordinates of the actual input's cell. -/
def deficit (x : G) : ℝ := (P.cut x).U.card - Real.logb 2 (P.code x).card

/-- A budget can be chosen separately for each complete record on each trace. -/
abbrev RecordBudget := (τ : nativeTraceSupport M G) → (P.onTrace τ).Tag → ℝ

def recordCost (bill : P.RecordBudget) (x : G) := bill (traceKey M x) ((P.cut x).tag x.val)

open Classical in
/-- Fraction of inputs in G whose own deficit exceeds their observed record's budget. -/
def badProbabilityOn (bill : P.RecordBudget) :=
  (((univ : Finset G).filter fun x => P.recordCost bill x < P.deficit x).card : ℝ) / G.card

/-- Uniform deficit budget on all traces. -/
abbrev badProbability (bill : ℝ) := P.badProbabilityOn (fun _ _ => bill)

open Classical in
/-- The exact exponential moment counts every attained complete record once, weighted by
its trace's number of retained coordinates and that record's individual budget. -/
theorem deficit_moment (bill : P.RecordBudget) :
    ∑ x : G, (2:ℝ)^(P.deficit x-P.recordCost bill x) =
      ∑ τ : nativeTraceSupport M G, ∑ z ∈ (nativeTraceSlice M G τ).image (P.onTrace τ).tag,
        (2:ℝ)^(((P.onTrace τ).U.card:ℝ)-bill τ z) := by
  rw [← sum_fiberwise_of_maps_to (fun (x : G) _ => mem_univ (traceKey M x)) _]
  apply sum_congr rfl
  intro τ _
  rw [← (P.onTrace τ).deficit_moment]
  apply sum_bij (fun x _ => x.val)
  · intro x hx
    exact mem_filter.mpr ⟨x.property,congrArg Subtype.val (mem_filter.mp hx).2⟩
  · intro _ _ _ _ h
    exact Subtype.ext h
  · intro x hx
    exact ⟨⟨x,(mem_filter.mp hx).1⟩,mem_filter.mpr ⟨mem_univ _,Subtype.ext (mem_filter.mp hx).2⟩,rfl⟩
  · intro x hx
    obtain rfl := (mem_filter.mp hx).2
    rfl

open Classical in
/-- A record-dependent deficit budget incurs the size-weighted sum over its actual
genie-and-exterior records. Empty ensembles also satisfy the cardinality bound. -/
theorem badProbabilityOn_le (bill : P.RecordBudget) :
    P.badProbabilityOn bill ≤
      (∑ τ : nativeTraceSupport M G, ∑ z ∈ (nativeTraceSlice M G τ).image (P.onTrace τ).tag,
        (2:ℝ)^(((P.onTrace τ).U.card:ℝ)-bill τ z)) / G.card := by
  rw [← P.deficit_moment]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  let bad := (univ : Finset G).filter fun x => P.recordCost bill x < P.deficit x
  calc
    (bad.card:ℝ) = ∑ _x ∈ bad, (1:ℝ) := by simp
    _ ≤ ∑ x ∈ bad, (2:ℝ)^(P.deficit x-P.recordCost bill x) :=
      sum_le_sum fun x hx => Real.one_le_rpow (by norm_num) (sub_nonneg.mpr (mem_filter.mp hx).2.le)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => by positivity)

/-- The number of pairs of full trace and revealed word actually attained on G. -/
def jointRecordCount : ℕ :=
  ∑ τ : nativeTraceSupport M G, (P.onTrace τ).revealed.card

/-- Charge the jointly attained trace and genie record. No independence or uniform
record count across traces is required. -/
theorem tail_of_joint_count (hG : G.Nonempty) {h : ℝ}
    (hcount : (P.jointRecordCount : ℝ) ≤ (2:ℝ)^h) (t : ℝ) :
    P.badProbability (((d*d*b : ℕ) : ℝ) - Real.logb 2 G.card + h + t) ≤ (2:ℝ)^(-t) := by
  classical
  let L := d*d*b
  let bill : ℝ := L-Real.logb 2 G.card+h+t
  have hGP : 0 < (G.card : ℝ) := by exact_mod_cast hG.card_pos
  apply (P.badProbabilityOn_le (fun _ _ => bill)).trans ((div_le_iff₀ hGP).mpr ?_)
  calc
    _ ≤ ∑ τ : nativeTraceSupport M G, ((P.onTrace τ).revealed.card : ℝ) * (2:ℝ)^(L-bill) :=
      sum_le_sum fun τ _ => by simpa [L] using (P.onTrace τ).tag_weight_le bill
    _ = (P.jointRecordCount : ℝ) * (2:ℝ)^(L-bill) := by
      rw [← sum_mul, jointRecordCount, Nat.cast_sum]
    _ ≤ (2:ℝ)^h * (2:ℝ)^(L-bill) := mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = (2:ℝ)^(-t) * G.card := by
      rw [← Real.rpow_add (by norm_num : (0:ℝ)<2),
        show h + (L-bill) = -t + Real.logb 2 G.card by dsimp [bill]; ring,
        Real.rpow_add (by norm_num : (0:ℝ)<2), Real.rpow_logb (by norm_num) (by norm_num) hGP]

/-- Separate support bounds for the full trace and each trace's revealed word give the
usual additive bill, even if different numbers of input bits survive each trace. -/
theorem tail_of_reveal_support (hG : G.Nonempty) {h g : ℝ}
    (htr : Real.logb 2 (nativeTraceSupport M G).card ≤ h)
    (hwords : ∀ τ, ((P.onTrace τ).revealed.card : ℝ) ≤ (2:ℝ)^g) (t : ℝ) :
    P.badProbability (((d*d*b : ℕ) : ℝ) - Real.logb 2 G.card + h + g + t) ≤ (2:ℝ)^(-t) := by
  classical
  have hpos : 0 < ((nativeTraceSupport M G).card : ℝ) := by
    exact_mod_cast (hG.image (fun x => trace M (List.ofFn x))).card_pos
  have htags := (Real.logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2) hpos).mp htr
  rw [add_assoc (_ - _) h g]
  apply P.tail_of_joint_count hG
  rw [jointRecordCount, Nat.cast_sum, Real.rpow_add (by norm_num : (0:ℝ)<2)]
  calc
    _ ≤ ∑ _τ : nativeTraceSupport M G, (2:ℝ)^g := sum_le_sum fun τ _ => hwords τ
    _ ≤ _ := by simpa using mul_le_mul_of_nonneg_right htags (Real.rpow_nonneg (by norm_num) g)

/-- The whole-step cost of a native genie bounds the number of values it reveals.
Positive t gives an exponential exceptional fraction. -/
theorem tail (hG : G.Nonempty) {h : ℝ} (htr : Real.logb 2 (nativeTraceSupport M G).card ≤ h)
    (t : ℝ) :
    P.badProbability (((d*d*b : ℕ) : ℝ) - Real.logb 2 G.card + h + ε*(d*d*b : ℕ) + t) ≤
      (2:ℝ)^(-t) :=
  P.tail_of_reveal_support hG htr (fun τ => (P.onTrace τ).revealed_le) t

end NativeTypicalPartition
end
end TapeStorageRates
