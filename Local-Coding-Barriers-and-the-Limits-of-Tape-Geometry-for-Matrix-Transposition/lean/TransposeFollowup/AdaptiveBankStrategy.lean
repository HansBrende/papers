import TransposeFollowup.AdaptiveBankHelper

/-! Arbitrary public strategies are compiled only on their finite correct
family. They may fail to terminate on every other full-cube assignment. -/

namespace TransposeFollowup

open Classical
set_option autoImplicit false

namespace PublicStrategy

variable {V : Type*}

/-- Reuse the finite public protocol's support list at the exact answer length. -/
def querySupports (s : PublicStrategy V (fun _ => Bool)) (h m : List Bool) :
    List (Finset V) := (s.truncate m.length h).querySupports m

def bankInteractionGraph (s : PublicStrategy V (fun _ => Bool))
    (h m : List Bool) : SimpleGraph V := (s.truncate m.length h).interactionGraph m

/-- Sufficient truncation preserves the supports of any public answer word,
even one that is not a complete execution on any stored assignment. -/
theorem truncate_querySupports_of_length (s : PublicStrategy V (fun _ => Bool))
    (h m : List Bool) (k : ℕ) (hk : m.length ≤ k) :
    (s.truncate k h).querySupports m = s.querySupports h m := by
  induction m generalizing h k with
  | nil =>
    cases k <;> cases hs : s h <;>
      simp [querySupports, truncate, hs, PublicProtocol.querySupports]
  | cons a m ih =>
    cases k with
    | zero => simp at hk
    | succ k =>
      cases hs : s h with
      | none => simp [querySupports, truncate, hs, PublicProtocol.querySupports]
      | some q =>
        simpa only [querySupports, List.length_cons, truncate, hs,
          PublicProtocol.querySupports] using
          congrArg (List.cons q.support) (ih (h ++ [a]) k (by simpa using hk))

theorem truncate_querySupports (s : PublicStrategy V (fun _ => Bool)) (x : V → Bool)
    {h m : List Bool} (_hrun : s.Executes x h m) (k : ℕ) (hk : m.length ≤ k) :
    (s.truncate k h).querySupports m = s.querySupports h m :=
  s.truncate_querySupports_of_length h m k hk

theorem truncate_bankInteractionGraph_of_length (s : PublicStrategy V (fun _ => Bool))
    (h m : List Bool) (k : ℕ) (hk : m.length ≤ k) :
    (s.truncate k h).interactionGraph m = s.bankInteractionGraph h m := by
  ext v w
  simp only [bankInteractionGraph, PublicProtocol.interactionGraph,
    s.truncate_querySupports_of_length h m k hk, querySupports]

theorem truncate_bankInteractionGraph (s : PublicStrategy V (fun _ => Bool)) (x : V → Bool)
    {h m : List Bool} (_hrun : s.Executes x h m) (k : ℕ) (hk : m.length ≤ k) :
    (s.truncate k h).interactionGraph m = s.bankInteractionGraph h m :=
  s.truncate_bankInteractionGraph_of_length h m k hk

end PublicStrategy

structure HelperGapBankStrategy (d b sigma : ℕ) (H : Type*) where
  helper : FiniteMatrix d b → H
  bank : H → GapBank d b sigma
  strategy : H → PublicStrategy (MatrixBit d b) (fun _ => Bool)
  decode : H → Fin d → Row d b → List Bool → Row d b

namespace HelperGapBankStrategy

variable {d b sigma : ℕ} {H : Type*} (C : HelperGapBankStrategy d b sigma H)

def CorrectOn (F : Set (FiniteMatrix d b)) (message : FiniteMatrix d b → List Bool) : Prop :=
  ∀ x ∈ F, ∀ j, C.decode (C.helper x) j (x j) (message x) = transposed x j

def TerminatesOn (F : Set (FiniteMatrix d b)) (message : FiniteMatrix d b → List Bool) : Prop :=
  ∀ x ∈ F, (C.strategy (C.helper x)).Executes ((C.bank (C.helper x)).recode x) [] (message x)

noncomputable def compile (F : Finset (FiniteMatrix d b))
    (message : FiniteMatrix d b → List Bool) : HelperGapBankCode d b sigma H where
  helper := C.helper
  branch a :=
    { bank := C.bank a
      protocol := (C.strategy a).truncate (F.sup (fun x => (message x).length)) []
      decode := C.decode a }

theorem compile_transcript (F : Finset (FiniteMatrix d b))
    (message : FiniteMatrix d b → List Bool) (ht : C.TerminatesOn F message)
    (x : FiniteMatrix d b) (hx : x ∈ F) :
    ((C.compile F message).branch (C.helper x)).transcript x = message x :=
  PublicStrategy.truncate_run_eq _ _ (ht x hx) _ (Finset.le_sup (f := fun x => (message x).length) hx)

theorem compile_correct (F : Finset (FiniteMatrix d b))
    (message : FiniteMatrix d b → List Bool) (ht : C.TerminatesOn F message)
    (hc : C.CorrectOn F message) : (C.compile F message).CorrectOn F := by
  intro a x hx j
  have he : C.helper x = a := hx.2
  have hm := C.compile_transcript F message ht x hx.1
  rw [he] at hm
  change C.decode a j (x j) _ = _
  rw [hm, ← he]
  exact hc x hx.1 j

theorem compile_graph (F : Finset (FiniteMatrix d b))
    (message : FiniteMatrix d b → List Bool) (ht : C.TerminatesOn F message)
    (x : FiniteMatrix d b) (hx : x ∈ F) :
    ((C.compile F message).branch (C.helper x)).protocol.interactionGraph
      (((C.compile F message).branch (C.helper x)).transcript x) =
        (C.strategy (C.helper x)).bankInteractionGraph [] (message x) := by
  rw [C.compile_transcript F message ht x hx]
  exact PublicStrategy.truncate_bankInteractionGraph _ _ (ht x hx) _
    (Finset.le_sup (f := fun x => (message x).length) hx)

theorem compile_along (F : Finset (FiniteMatrix d b))
    (message : FiniteMatrix d b → List Bool) (ht : C.TerminatesOn F message)
    (x : FiniteMatrix d b) (hx : x ∈ F) (P : Finset (MatrixBit d b) → Prop)
    (hP : (C.strategy (C.helper x)).Along P [] (message x)) :
    ((C.compile F message).branch (C.helper x)).protocol.Along P
      (((C.compile F message).branch (C.helper x)).transcript x) := by
  rw [C.compile_transcript F message ht x hx]
  exact PublicStrategy.truncate_along _ _ _ _ _ hP

end HelperGapBankStrategy
end TransposeFollowup
