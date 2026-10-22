import Transpose.Statement
import Mathlib.Data.Finset.Card
import Mathlib.InformationTheory.Coding.PrefixFree
import Mathlib.Tactic

/-!
# Public protocols with original-row queries

The transcript determines every queried support and the stopping decision.
The query functions may be nonlinear. The input type is dependent, so a row
may contain any fixed finite block; finiteness is not needed for the component gluing
lemmas. A public helper is represented later by a family of these protocols.

These are protocol-interface lemmas, not a normalization of arbitrary tape
computation into original-row access.
-/

namespace TransposeFollowup

universe u v
set_option autoImplicit false

/-- A Boolean query of specified original input blocks. -/
structure LocalQuery (ι : Type u) (V : ι → Type v) where
  support : Finset ι
  read : ((i : ι) → V i) → Bool
  locality : ∀ x y, (∀ i ∈ support, x i = y i) → read x = read y

/-- The public history chooses both the next query and when to stop. -/
inductive PublicProtocol (ι : Type u) (V : ι → Type v) where
  | halt
  | query (q : LocalQuery ι V) (next : Bool → PublicProtocol ι V)

namespace PublicProtocol

variable {ι : Type u} {V : ι → Type v}

/-- Actual charged bits, including any bits used for public control. -/
def run : PublicProtocol ι V → ((i : ι) → V i) → List Bool
  | .halt, _ => []
  | .query q next, x => q.read x :: run (next (q.read x)) x

/-- Consistency with the full path, including its terminal halt. -/
def Consistent : PublicProtocol ι V → List Bool → ((i : ι) → V i) → Prop
  | .halt, m, _ => m = []
  | .query _ _, [], _ => False
  | .query q next, a :: m, x => q.read x = a ∧ Consistent (next a) m x

/-- A property required only of supports used along this public path. -/
def Along (P : Finset ι → Prop) : PublicProtocol ι V → List Bool → Prop
  | .halt, _ => True
  | .query _ _, [] => True
  | .query q next, a :: m => P q.support ∧ Along P (next a) m

theorem run_eq_iff_consistent (p : PublicProtocol ι V) (m : List Bool)
    (x : (i : ι) → V i) : p.run x = m ↔ p.Consistent m x := by
  induction p generalizing m with
  | halt => simp [run, Consistent, eq_comm]
  | query q next ih =>
    cases m with
    | nil => simp [run, Consistent]
    | cons a m =>
      simp only [run, Consistent, List.cons.injEq]
      constructor
      · rintro ⟨h, hm⟩
        refine ⟨h, ?_⟩
        rw [h] at hm
        exact (ih a m).mp hm
      · rintro ⟨h, hm⟩
        refine ⟨h, ?_⟩
        rw [h]
        exact (ih a m).mpr hm

theorem run_eq_of_prefix (p : PublicProtocol ι V) (x y : (i : ι) → V i)
    (h : p.run x <+: p.run y) : p.run x = p.run y := by
  induction p with
  | halt => rfl
  | query q next ih =>
    simp only [run, List.cons_prefix_cons] at h
    simp only [run, List.cons.injEq]
    refine ⟨h.1, ?_⟩
    have he := h.1
    rw [he]
    apply ih (q.read y)
    simpa [he] using h.2

theorem run_prefixFree (p : PublicProtocol ι V) :
    InformationTheory.IsPrefixFree (Set.range p.run) := by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ h
  exact run_eq_of_prefix p x y h

/-- A support meets at most one component outside the separator. The first
case handles an empty complement without requiring a nonempty component type. -/
def Separated {κ : Type*} (separator : Finset ι) (component : ι → κ)
    (s : Finset ι) : Prop :=
  (∀ i ∈ s, i ∈ separator) ∨
    ∃ c, ∀ i ∈ s, i ∈ separator ∨ component i = c

open Classical in
/-- Glue independently chosen component assignments, fixing separator blocks. -/
noncomputable def glue {κ : Type*} (separator : Finset ι) (component : ι → κ)
    (base : (i : ι) → V i) (xs : κ → (i : ι) → V i) : (i : ι) → V i :=
  fun i => if i ∈ separator then base i else xs (component i) i

/-- A fixed public leaf and fixed separator assignment admit arbitrary
componentwise combinations of their full-input witnesses. -/
theorem consistent_glue {κ : Type*} (p : PublicProtocol ι V) (m : List Bool)
    (separator : Finset ι) (component : ι → κ)
    (base : (i : ι) → V i) (xs : κ → (i : ι) → V i)
    (hb : p.Consistent m base) (hx : ∀ c, p.Consistent m (xs c))
    (hfix : ∀ c i, i ∈ separator → xs c i = base i)
    (hs : p.Along (Separated separator component) m) :
    p.Consistent m (glue separator component base xs) := by
  classical
  induction p generalizing m with
  | halt => exact hb
  | query q next ih =>
    cases m with
    | nil => exact hb.elim
    | cons a m =>
      rcases hb with ⟨hb, hbs⟩
      rcases hs with ⟨hs, hss⟩
      refine ⟨?_, ih a m hbs (fun c => (hx c).2) hss⟩
      rcases hs with hsep | ⟨c, hc⟩
      · calc
          q.read (glue separator component base xs) = q.read base := by
            apply q.locality
            intro i hi
            simp [glue, hsep i hi]
          _ = a := hb
      · calc
          q.read (glue separator component base xs) = q.read (xs c) := by
            apply q.locality
            intro i hi
            by_cases h : i ∈ separator
            · simp [glue, h, hfix c i h]
            · have hg : component i = c := (hc i hi).resolve_left h
              simp [glue, h, hg]
          _ = a := (hx c).1

/-- Exact factorization of a nonempty full transcript fiber after fixing
separator rows. Each component factor is its projection; no factorization
or independence of a smaller correct-input family is assumed. -/
theorem fiber_factorization {κ : Type*} (p : PublicProtocol ι V) (m : List Bool)
    (separator : Finset ι) (component : ι → κ)
    (base x : (i : ι) → V i) (hb : p.run base = m)
    (hs : p.Along (Separated separator component) m) :
    (p.run x = m ∧ ∀ i ∈ separator, x i = base i) ↔
      (∀ i ∈ separator, x i = base i) ∧
        ∀ c, ∃ y : (i : ι) → V i,
          p.run y = m ∧ (∀ i ∈ separator, y i = base i) ∧
            ∀ i, component i = c → y i = x i := by
  classical
  constructor
  · rintro ⟨hx, hfix⟩
    exact ⟨hfix, fun _ => ⟨x, hx, hfix, fun _ _ => rfl⟩⟩
  · rintro ⟨hfix, hw⟩
    choose xs hx hsep hcomp using hw
    have hg := consistent_glue p m separator component base xs
      ((run_eq_iff_consistent p m base).mp hb)
      (fun c => (run_eq_iff_consistent p m (xs c)).mp (hx c)) hsep hs
    have he : glue separator component base xs = x := by
      funext i
      by_cases hi : i ∈ separator
      · simp [glue, hi, hfix i hi]
      · simp [glue, hi, hcomp (component i) i rfl]
    rw [he] at hg
    exact ⟨(run_eq_iff_consistent p m x).mpr hg, hfix⟩

end PublicProtocol
end TransposeFollowup
