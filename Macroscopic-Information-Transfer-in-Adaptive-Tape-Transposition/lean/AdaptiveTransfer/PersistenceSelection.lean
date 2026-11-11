import AdaptiveTransfer.PersistenceCatalogues
import LeanMachine.FiniteIntervalSelection
import LeanMachine.FiniteMaskFibres

/-! Actual catalogue escapes select one common tape set, time interval and
retained event. All top sets are computed under the original law. The result
is conditional on the literal escape event, not on a supplied heavy cell or
conditional entropy certificate. -/

namespace AdaptiveTransfer.PersistenceSelection

open Transpose Transpose.Tape LeanMachine Finset
open PersistenceGraph PersistenceCatalogues FiniteTimeGrid
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {Ω : Type*} [Fintype Ω]

/-- The same selection works for any number of escaping tapes;
the manuscript uses two. The number of choices is the exact unordered
tape-set count times the finite grid count. -/
theorem exists_fixed_escape_interval (M : TM) (input : Ω → List Bool)
    (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (hprob : ∑ x, w x = 1)
    (T K R m : ℕ) (hK : 1 ≤ K) (hR : 2 ≤ R)
    (limit : Ω → ℕ) (B : Finset Ω) (hp : 0 < ContextPruning.mass w B)
    (hlimit : ∀ x ∈ B, limit x ≤ T)
    (hescape : ∀ x ∈ B, ∃ t ≤ limit x, ∃ H : Finset (Fin M.k), H.card = m ∧
      ∀ h ∈ H, vertex M (input x) T t h ∉
        catalogue (nativeTop M input w T K h) t R
          (PrefixOutput.word (outBit M (input x)) t)) :
    ∃ H : Finset (Fin M.k), H.card = m ∧ ∃ j < T / (R / 2) + 1,
      ∃ E ⊆ B,
        ContextPruning.mass w B /
          (M.k.choose m * (T / (R / 2) + 1) : ℕ) ≤ ContextPruning.mass w E ∧
        ∀ x ∈ E, ∀ h ∈ H, ∀ u ∈ interval (R / 2) j,
          u < limit x ∧ vertex M (input x) T u h ∉ nativeTop M input w T K h u
            (PrefixOutput.word (outBit M (input x)) u) := by
  apply FiniteIntervalSelection.exists_fixed_interval w hw B hp M.k m T (R / 2)
    (fun x h u => u < limit x ∧ vertex M (input x) T u h ∉ nativeTop M input w T K h u
      (PrefixOutput.word (outBit M (input x)) u))
  intro x hx
  obtain ⟨t, ht, H, hH, hout⟩ := hescape x hx
  refine ⟨t, ht.trans (hlimit x hx), H, hH, ?_⟩
  intro h hh u hu
  have hg := native_escape_grid M input w hprob T K R hK hR h x
    (ht.trans (hlimit x hx)) (hout h hh) u hu
  exact ⟨hg.1.trans_le ht, hg.2⟩

end AdaptiveTransfer.PersistenceSelection
