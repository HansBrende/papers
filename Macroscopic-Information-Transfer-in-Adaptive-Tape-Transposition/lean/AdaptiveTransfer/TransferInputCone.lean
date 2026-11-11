import AdaptiveTransfer.FrozenCutInvoice
import BoundedStackDepth.Machines

/-! The existing root-exempt dependency cone, specialized to actual raw reads.
Its determination property is derived from the frozen native cut recursion.
-/

namespace AdaptiveTransfer
open Transpose MergeDepth BoundedNesting BoundedStackDepth NativeRelations Finset
attribute [local instance] Classical.propDecidable

noncomputable abbrev nativeInputCone {k : ℕ} (τ : Trace k) (L T : ℕ)
    (Γ : Finset ℕ) (root : ℕ) : Finset (Fin L) :=
  depCone τ.work T (readPos τ L) Γ root

theorem mem_nativeInputCone {k L T root : ℕ} {τ : Trace k} {Γ : Finset ℕ} {p : Fin L} :
    p ∈ nativeInputCone τ L T Γ root ↔
      ∃ ρ : List ℕ, IsDepPath τ.work T (root :: ρ) ∧ LinNet.GFree Γ (root :: ρ) ∧
        readPos τ L ((root :: ρ).getLastD root) = some p := by
  simp only [nativeInputCone, depCone, mem_filter, mem_univ, true_and]

theorem mem_nativeInputCone_iff_position {k L T root : ℕ} {τ : Trace k} {Γ : Finset ℕ} {p : Fin L} :
    p ∈ nativeInputCone τ L T Γ root ↔
      ∃ ρ : List ℕ, IsDepPath τ.work T (root :: ρ) ∧ LinNet.GFree Γ (root :: ρ) ∧
        τ.input ((root :: ρ).getLastD root) = (p.val : ℤ) := by
  simp only [mem_nativeInputCone, readPos_eq_some_iff]

/-- Every path to a raw address outside the root-exempt cone meets the cut,
including its endpoints. No native projection theorem is used here. -/
theorem nativeInputCone_complement_cut {k L T : ℕ} (τ : Trace k) (Γ : Finset ℕ) (root : ℕ) :
    IsMengerVertexCut τ.work T {root}
      (demandedReadSteps τ L T (nativeInputCone τ L T Γ root)ᶜ) Γ := by
  intro ρ t ht hpath hend
  have htroot : t = root := mem_singleton.mp ht
  subst t
  by_contra hn
  push Not at hn
  have hfree : LinNet.GFree Γ (root :: ρ) := by
    intro z hz
    exact hn z (List.mem_cons_of_mem root hz)
  obtain ⟨_, p, hp, hread⟩ := mem_filter.mp hend
  exact (mem_compl.mp hp) (mem_nativeInputCone.mpr ⟨ρ, hpath, hfree, hread⟩)

/-- Exact native cone determination on two inputs with one frozen simulator
trace. The complete cut values include the output field, so guarded roots
require no additional output-bit surcharge. -/
theorem nativeInputCone_determines {M : TM} {L T t : ℕ} {τ : Trace M.k}
    {X Y : Fin L → Bool} {Γ : Finset ℕ} (ht : t < T)
    (hX : ∀ u < T, trace M (List.ofFn X) u = τ u)
    (hY : ∀ u < T, trace M (List.ofFn Y) u = τ u)
    (hΓ : ∀ u ∈ Γ, stepValue M (List.ofFn X) u = stepValue M (List.ofFn Y) u)
    (hraw : ∀ p ∈ nativeInputCone τ L T Γ t, X p = Y p) :
    stepValue M (List.ofFn X) t = stepValue M (List.ofFn Y) t := by
  by_cases htΓ : t ∈ Γ
  · exact hΓ t htΓ
  · apply stepValue_eq_of_uncut_native_cut (Q := (nativeInputCone τ L T Γ t)ᶜ)
      hX hY (fun p hp => hraw p (by simpa only [mem_compl, not_not] using hp))
      (fun u hu => congrArg (fun v : Value M => (v.1, v.2.1)) (hΓ u hu)) t ht htΓ
    exact nativeInputCone_complement_cut τ Γ t

end AdaptiveTransfer
