import TransposeFollowup.AdaptiveBankProtocol
import TransposeFollowup.FullFiberAveraging

/-! Finite outcome indices for the full raw stored cube, retaining the actual
variable-length public answer strings as their prefix-free code. -/

namespace TransposeFollowup.PublicProtocol

open Classical
set_option autoImplicit false

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def fullOutputs (p : PublicProtocol V (fun _ => Bool)) : Finset (List Bool) :=
  Finset.univ.image p.run

noncomputable def outcome (p : PublicProtocol V (fun _ => Bool)) (y : V → Bool) : p.fullOutputs :=
  ⟨p.run y, Finset.mem_image.mpr ⟨y, Finset.mem_univ _, rfl⟩⟩

instance fullOutputs_nonempty (p : PublicProtocol V (fun _ => Bool)) : Nonempty p.fullOutputs :=
  ⟨p.outcome (fun _ => false)⟩

theorem outcome_prefixFree (p : PublicProtocol V (fun _ => Bool)) :
    InformationTheory.IsPrefixFree (Set.range (Subtype.val : p.fullOutputs → List Bool)) := by
  intro u hu v hv huv
  obtain ⟨a, rfl⟩ := hu
  obtain ⟨b, rfl⟩ := hv
  obtain ⟨x, _, hx⟩ := Finset.mem_image.mp a.property
  obtain ⟨y, _, hy⟩ := Finset.mem_image.mp b.property
  apply p.run_prefixFree (x := a.val) (y := b.val)
  · exact ⟨x, hx⟩
  · exact ⟨y, hy⟩
  · exact huv

theorem outcome_fiberCard (p : PublicProtocol V (fun _ => Bool)) (a : p.fullOutputs) :
    fiberCard p.outcome a = (p.fullFiber a.val).card := by
  unfold fiberCard fullFiber
  congr 1
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact Subtype.ext_iff

end TransposeFollowup.PublicProtocol
