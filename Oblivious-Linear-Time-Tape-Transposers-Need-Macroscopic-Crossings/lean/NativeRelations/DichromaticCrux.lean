import NativeRelations.MachineCrux
import NativeRelations.NativeGapCriterion
import DirectedRecovery.StorageCode
import HalfRate.Corollaries

/-!
# Acyclic Sets, Storage-Code Bounds, and Index-Code Lengths

Proves topological outside-word injectivity (`acyclicIn_outside_injOn`), the cardinality bound
`storageCode_card_le_of_isAcyclicIn` for storage codes on arbitrary relations, and the index-code
length bound `indexCode_bits_ge_of_isAcyclicIn` yielding `machineCrux_of_isAcyclicIn` and
`oblivious_excludes_of_isAcyclicIn`.
-/

set_option autoImplicit false

namespace NativeRelations

open Filter Finset Transpose Transpose.Tape BoundedNesting MergeDepth MotionDepthCodes
  BoundedStackDepth TapeStorageRates
open scoped BigOperators

section AcyclicStorageBounds

variable {V α : Type*} [DecidableEq V]

/-- **Sink/source uniqueness on an acyclic coordinate set.**
If `A` induces an acyclic sub-relation (`HalfRate.IsAcyclicIn N A`), then on any storage code `C`
for `N`, fixing the coordinates outside `A` uniquely determines the entire word. -/
theorem acyclicIn_outside_injOn {N : V → Finset V} {A : Finset V}
    (hA : HalfRate.IsAcyclicIn N A) {C : Finset (V → α)} (hC : IsStorageCode N C) :
    Set.InjOn (DirectedRecovery.outsideWord A) (C : Set (V → α)) := by
  classical
  intro x hx y hy hxy
  by_contra hne
  have hTne : (A.filter fun v => x v ≠ y v).Nonempty := by
    obtain ⟨v, hv⟩ : ∃ v, x v ≠ y v := Function.ne_iff.mp hne
    by_cases hvA : v ∈ A
    · exact ⟨v, mem_filter.mpr ⟨hvA, hv⟩⟩
    · exact absurd (congrFun hxy ⟨v, hvA⟩) hv
  obtain ⟨v, hvT, hsrc⟩ := hA (A.filter fun v => x v ≠ y v) (filter_subset _ _) hTne
  obtain ⟨-, hvne⟩ := mem_filter.mp hvT
  apply hvne
  apply hC x hx y hy v
  intro u hu
  by_cases huA : u ∈ A
  · by_contra hune
    exact hsrc u hu (mem_filter.mpr ⟨huA, hune⟩)
  · exact congrFun hxy ⟨u, huA⟩

variable [Fintype V] [Fintype α]

/-- **Acyclic storage-code bound.** Any `A : Finset V` with `HalfRate.IsAcyclicIn N A` forces
`C.card ≤ |α|^{|V| - |A|}` for every storage code `C` on `N`. -/
theorem storageCode_card_le_of_isAcyclicIn {N : V → Finset V} {A : Finset V}
    (hA : HalfRate.IsAcyclicIn N A) {C : Finset (V → α)} (hC : IsStorageCode N C) :
    C.card ≤ Fintype.card α ^ (Fintype.card V - A.card) := by
  classical
  have h : C.card ≤ Fintype.card ({v // v ∉ A} → α) := by
    rw [← Finset.card_image_of_injOn (acyclicIn_outside_injOn hA hC)]
    exact Finset.card_le_univ _
  simpa using h

end AcyclicStorageBounds

section IndexCodeAndCrux

/-- **Direct single-acyclic-set index-code bit lower bound.**
If `A : Finset (Fin (d * d * b))` induces an acyclic sub-relation of the demand-labelled cone
relation `q ↦ I (tposOf d b q)`, then every `msgLen`-bit binary index code for `(I, tposOf d b)`
satisfies `(A.card : ℝ) ≤ (msgLen : ℝ)`. -/
theorem indexCode_bits_ge_of_isAcyclicIn {d b msgLen : ℕ}
    {I : Fin (d * d * b) → Finset (Fin (d * d * b))}
    {E : (Fin (d * d * b) → Bool) → (Fin msgLen → Bool)}
    (hE : MergeDepth.IsIndexCode E I (tposOf d b))
    {A : Finset (Fin (d * d * b))}
    (hA : HalfRate.IsAcyclicIn (fun q => I (tposOf d b q)) A) :
    (A.card : ℝ) ≤ (msgLen : ℝ) := by
  have hG : DirectedRecovery.IsIndexCode (fun q => I (tposOf d b q)) E := by
    intro x y hExy q hxy
    have h1 := hE (tposOf d b q) x y hExy hxy
    rwa [tposOf_tposOf] at h1
  refine DirectedRecovery.indexCode_length_ge hG fun C hC => ?_
  have hcard := storageCode_card_le_of_isAcyclicIn hA hC
  have hle : A.card ≤ Fintype.card (Fin (d * d * b)) := A.card_le_univ
  rw [Fintype.card_bool] at hcard
  rw [← Nat.cast_sub hle, Real.rpow_natCast]
  exact_mod_cast hcard

/-- **`MachineCruxAt M C D ρ` from asymptotic `(ρ - δ) L` acyclic subsets.** -/
theorem machineCruxAt_of_isAcyclicIn {M : TM} {C ρ : ℝ} {D : ℕ}
    (hacyc : ∀ δ : ℝ, 0 < δ → ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ I ∈ SConeOf M C D d (entryBits d),
      ∃ A : Finset (Fin (d * d * entryBits d)),
        HalfRate.IsAcyclicIn (fun q => I (tposOf d (entryBits d) q)) A ∧
        (ρ - δ) * (d * d * entryBits d : ℕ) ≤ (A.card : ℝ)) :
    MachineCruxAt M C D ρ := by
  intro η hη
  obtain ⟨d₀, hd₀⟩ := hacyc η hη
  refine ⟨d₀, fun d hd I hI msgLen E hE => ?_⟩
  obtain ⟨A, hA, hcard⟩ := hd₀ d hd I hI
  exact hcard.trans (indexCode_bits_ge_of_isAcyclicIn hE hA)

/-- **Depth-uniform `MachineCrux M C ρ` from `D`-uniform `(ρ - δ) L` acyclic subsets.** -/
theorem machineCrux_of_isAcyclicIn {M : TM} {C ρ : ℝ}
    (hacyc : ∀ (D : ℕ) (δ : ℝ), 0 < δ → ∃ d₀ : ℕ, ∀ d ≥ d₀,
      ∀ I ∈ SConeOf M C D d (entryBits d),
        ∃ A : Finset (Fin (d * d * entryBits d)),
          HalfRate.IsAcyclicIn (fun q => I (tposOf d (entryBits d) q)) A ∧
          (ρ - δ) * (d * d * entryBits d : ℕ) ≤ (A.card : ℝ)) :
    MachineCrux M C ρ :=
  fun D => machineCruxAt_of_isAcyclicIn (hacyc D)

/-- **Oblivious linear-time exclusion from an acyclic subset of density `ρ > ε` at `genieDepth`.** -/
theorem oblivious_excludes_of_isAcyclicIn {M : TM} {C ε ρ : ℝ}
    (hC : 1 ≤ C) (hε : 0 < ε) (hερ : ε < ρ)
    (hacyc : ∀ δ : ℝ, 0 < δ → ∃ d₀ : ℕ, ∀ d ≥ d₀,
      ∀ I ∈ SConeOf M C (genieDepth M.k (valueWidth M) C ε) d (entryBits d),
        ∃ A : Finset (Fin (d * d * entryBits d)),
          HalfRate.IsAcyclicIn (fun q => I (tposOf d (entryBits d) q)) A ∧
          (ρ - δ) * (d * d * entryBits d : ℕ) ≤ (A.card : ℝ)) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ T : ℕ, ¬ ObliviousLinTime M d (entryBits d) C T :=
  machine_crux_excludes hC hε hερ (machineCruxAt_of_isAcyclicIn hacyc)

end IndexCodeAndCrux

end NativeRelations
