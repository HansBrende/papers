import TransposeFollowup.LocalProtocol

/-! A public strategy can be infinite and need not terminate off the correct
input family. Finite families of terminating executions admit one uniform
finite truncation, preserving their charged transcripts and support properties. -/

namespace TransposeFollowup

universe u v
set_option autoImplicit false

abbrev PublicStrategy (ι : Type u) (V : ι → Type v) :=
  List Bool → Option (LocalQuery ι V)

namespace PublicStrategy

variable {ι : Type u} {V : ι → Type v}

inductive Executes (s : PublicStrategy ι V) (x : (i : ι) → V i) :
    List Bool → List Bool → Prop where
  | halt (h : List Bool) (hn : s h = none) : Executes s x h []
  | step (h : List Bool) (q : LocalQuery ι V) (m : List Bool)
      (hn : s h = some q) (tail : Executes s x (h ++ [q.read x]) m) :
      Executes s x h (q.read x :: m)

def truncate (s : PublicStrategy ι V) : ℕ → List Bool → PublicProtocol ι V
  | 0, _ => .halt
  | k + 1, h => match s h with
      | none => .halt
      | some q => .query q (fun a => truncate s k (h ++ [a]))

def Along (s : PublicStrategy ι V) (P : Finset ι → Prop) :
    List Bool → List Bool → Prop
  | _, [] => True
  | h, a :: m => match s h with
      | none => False
      | some q => P q.support ∧ Along s P (h ++ [a]) m

theorem truncate_run_eq (s : PublicStrategy ι V) (x : (i : ι) → V i)
    {h m : List Bool} (hrun : s.Executes x h m) (k : ℕ) (hk : m.length ≤ k) :
    (s.truncate k h).run x = m := by
  induction hrun generalizing k with
  | halt h hn =>
      cases k <;> simp [truncate, hn, PublicProtocol.run]
  | step h q m hn tail ih =>
      cases k with
      | zero => simp at hk
      | succ k =>
          simp only [List.length_cons, Nat.add_le_add_iff_right] at hk
          simpa only [truncate, hn, PublicProtocol.run] using
            congrArg (List.cons (q.read x)) (ih k hk)

theorem truncate_along (s : PublicStrategy ι V) (P : Finset ι → Prop)
    (k : ℕ) (h m : List Bool) (hs : s.Along P h m) :
    (s.truncate k h).Along P m := by
  induction k generalizing h m with
  | zero => trivial
  | succ k ih =>
      cases hn : s h with
      | none => simp [truncate, hn, PublicProtocol.Along]
      | some q =>
          cases m with
          | nil => simp [truncate, hn, PublicProtocol.Along]
          | cons a m =>
              have hs' : P q.support ∧ s.Along P (h ++ [a]) m := by
                simpa only [Along, hn] using hs
              simp only [truncate, hn, PublicProtocol.Along]
              exact ⟨hs'.1, ih (h ++ [a]) m hs'.2⟩

/-- On a complete execution no queried support is lost by a sufficiently
deep truncation. This is the converse needed to use its actual leaf graph. -/
theorem along_of_truncate (s : PublicStrategy ι V) (x : (i : ι) → V i)
    (P : Finset ι → Prop) {h m : List Bool} (hrun : s.Executes x h m)
    (k : ℕ) (hk : m.length ≤ k) (hP : (s.truncate k h).Along P m) :
    s.Along P h m := by
  induction hrun generalizing k with
  | halt h hn => trivial
  | step h q m hn tail ih =>
      cases k with
      | zero => simp at hk
      | succ k =>
          have hP' : P q.support ∧ (s.truncate k (h ++ [q.read x])).Along P m := by
            simpa only [truncate, hn, PublicProtocol.Along] using hP
          have hk' : m.length ≤ k := by simpa only [List.length_cons, Nat.add_le_add_iff_right] using hk
          simp only [Along, hn]
          exact ⟨hP'.1, ih k hk' hP'.2⟩

/-- One depth bound works for the whole finite correct family, even when
helpers select different strategies. No behavior is required on other inputs. -/
theorem finite_family_truncation {H : Type*}
    (F : Finset ((i : ι) → V i)) (helper : ((i : ι) → V i) → H)
    (strategy : H → PublicStrategy ι V) (M : ((i : ι) → V i) → List Bool)
    (hrun : ∀ x ∈ F, (strategy (helper x)).Executes x [] (M x)) :
    ∃ p : H → PublicProtocol ι V,
      (∀ x ∈ F, (p (helper x)).run x = M x) ∧
      ∀ x ∈ F, ∀ P, (strategy (helper x)).Along P [] (M x) →
        (p (helper x)).Along P (M x) := by
  let B := F.sup (fun x => (M x).length)
  refine ⟨fun z => (strategy z).truncate B [], ?_, ?_⟩
  · intro x hx
    exact truncate_run_eq _ x (hrun x hx) B (Finset.le_sup (f := fun x => (M x).length) hx)
  · intro x _ P hP
    exact truncate_along _ P B [] (M x) hP

end PublicStrategy
end TransposeFollowup
