import AdaptiveTransfer.ClusterGoodInputs
import AdaptiveTransfer.ReturnHeads

/-! Singleton clusters recover every free-head consequence using the same
simultaneous exceptional event. -/
namespace AdaptiveTransfer
open Transpose MergeDepth BoundedNesting NativeRelations Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable

noncomputable def singletonSignature {k : ℕ} (f : Fin k) : ClusterSignature k :=
  fun h => if h = f then some false else none

@[simp] theorem singletonSignature_ne_none {k : ℕ} (f h : Fin k) :
    singletonSignature f h ≠ none ↔ h = f := by simp [singletonSignature]

noncomputable instance singletonHeadsUnique {k : ℕ} (f : Fin k) :
    Unique (ClusterHeads (singletonSignature f)) where
  default := ⟨f, by simp⟩
  uniq h := Subtype.ext ((singletonSignature_ne_none f h.val).mp h.property)

noncomputable def singletonChart {k T : ℕ} (xs : Fin k → ℕ → ℤ) (f : Fin k)
    {error : ℝ} (he : 0 ≤ error) : ClusterChart xs T error where
  signature := singletonSignature f
  nonempty := ⟨f, by simp⟩
  map _ := id
  monotone _ := monotone_id
  lipschitz _ := LipschitzWith.id
  normalized z := by simp
  error t _ h := by
    have hh : h.val = f := (singletonSignature_ne_none f h.val).mp h.property
    have hcarrier : clusterCarrier (singletonSignature f) xs t = xs f t := by
      have hd : (default : ClusterHeads (singletonSignature f)).val = f :=
        (singletonSignature_ne_none f _).mp (default : ClusterHeads (singletonSignature f)).property
      simpa [clusterCarrier, singletonSignature, clusterOrient] using congrArg (fun u => xs u t) hd
    simpa [hcarrier, hh, singletonSignature, clusterOrient] using he

@[simp] theorem singletonChart_included {k T : ℕ} (xs : Fin k → ℕ → ℤ) (f : Fin k)
    {error : ℝ} (he : 0 ≤ error) : (singletonChart (T := T) xs f he).included = {f} := by
  ext h
  simp [ClusterChart.included, singletonChart]

theorem offClusterReturns_singleton {k : ℕ} (xs : Fin k → ℕ → ℤ) (f : Fin k) (T H : ℕ) :
    offClusterReturns xs {f} T H = offCarrierReturns xs f T H := by
  ext e
  simp [offClusterReturns, offCarrierReturns]

/-- Every good input has the original two distinct busy heads, now at the
cluster constants, since every singleton is an exact coherent chart. -/
theorem native_cluster_two_return_heads {M : TM} {d b H : ℕ} {c error γ : ℝ}
    (hk : 2 ≤ M.k) (he : 0 ≤ error) {X : Fin (d * d * b) → Bool}
    (hcorrect : TransposesInput M d b c X)
    (hgood : X ∉ nativeBadClusterReturns M d b c error H ⌊γ * (d * d * b : ℕ)⌋₊) :
    let y := (trace M (List.ofFn X)).work
    let T := (trace M (List.ofFn X)).haltTime
    ∃ f g : Fin M.k, f ≠ g ∧
      γ * (d * d * b : ℕ) / (M.k - 1 : ℕ) < ((headReturns y f T H).card : ℝ) ∧
      γ * (d * d * b : ℕ) / (M.k - 1 : ℕ) < ((headReturns y g T H).card : ℝ) := by
  apply native_two_return_heads hk hcorrect
  intro hbad
  obtain ⟨_, _, f, hf⟩ := mem_filter.mp hbad
  apply hgood
  refine mem_filter.mpr ⟨mem_univ _, hcorrect,
    singletonChart (trace M (List.ofFn X)).work f he, ?_⟩
  simpa only [singletonChart_included, offClusterReturns_singleton] using hf

/-- With one physical head every timely correct input belongs to the
same cluster bad event, since its singleton cluster has empty complement. -/
theorem native_cluster_one_head_bad {M : TM} {d b H J : ℕ} {c error : ℝ}
    (hk : M.k = 1) (he : 0 ≤ error) {X : Fin (d * d * b) → Bool}
    (hcorrect : TransposesInput M d b c X) :
    X ∈ nativeBadClusterReturns M d b c error H J := by
  let f : Fin M.k := ⟨0, by omega⟩
  refine mem_filter.mpr ⟨mem_univ _, hcorrect,
    singletonChart (trace M (List.ofFn X)).work f he, ?_⟩
  rw [singletonChart_included, offClusterReturns_singleton,
    offCarrierReturns_eq_empty_of_one hk, card_empty]
  exact Nat.zero_le _

end AdaptiveTransfer
