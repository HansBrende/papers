import TransposeFollowup.AdaptiveBankProtocol
import TransposeFollowup.MatrixView

/-! Full-cube nonlinear banks with forward column locality and inverse gap
states. Gap states are analytical records; no evaluation cost is asserted.
Original raw rows, rather than recoded rows, are the receivers' side information. -/

namespace TransposeFollowup

open Classical
set_option autoImplicit false

def IsRowInterval {d : ℕ} (I : Finset (Fin d)) : Prop :=
  I.Nonempty ∧ ∀ i ∈ I, ∀ j ∈ I, ∀ k, i ≤ k → k ≤ j → k ∈ I

def columnWindow {d : ℕ} (sigma : ℕ) (c : Fin d) : Finset (Fin d) :=
  Finset.univ.filter (fun j => j.val ≤ c.val + sigma ∧ c.val ≤ j.val + sigma)

@[simp] theorem mem_columnWindow {d : ℕ} (sigma : ℕ) (c j : Fin d) :
    j ∈ columnWindow sigma c ↔ j.val ≤ c.val + sigma ∧ c.val ≤ j.val + sigma := by
  simp [columnWindow]

theorem mem_columnWindow_self {d : ℕ} (sigma : ℕ) (c : Fin d) :
    c ∈ columnWindow sigma c := by simp

structure GapBank (d b sigma : ℕ) where
  recode : FiniteMatrix d b ≃ (MatrixBit d b → Bool)
  State : Finset (Fin d) → Type
  stateFinite : ∀ I, Fintype (State I)
  state : (I : Finset (Fin d)) → FiniteMatrix d b → State I
  forward_local : ∀ (x x' : FiniteMatrix d b) (v : MatrixBit d b),
    (∀ j ∈ columnWindow sigma v.2.1, transposed x j = transposed x' j) →
      recode x v = recode x' v
  gap_inverse : ∀ I, IsRowInterval I → ∀ x x',
    (∀ i ∈ I, ∀ j t, recode x (i, (j, t)) = recode x' (i, (j, t))) →
    state I x = state I x' → ∀ i ∈ I, x i = x' i

instance {d b sigma : ℕ} (A : GapBank d b sigma) (I : Finset (Fin d)) :
    Fintype (A.State I) := A.stateFinite I

namespace GapBank

variable {d b sigma : ℕ} (A : GapBank d b sigma)

/-- A bound on the possible analytical state values, in bits. -/
def StateBudget (s : ℝ) : Prop := ∀ I, IsRowInterval I →
  (Fintype.card (A.State I) : ℝ) ≤ (2 : ℝ) ^ s

end GapBank

structure GapBankCode (d b sigma : ℕ) where
  bank : GapBank d b sigma
  protocol : PublicProtocol (MatrixBit d b) (fun _ => Bool)
  decode : Fin d → Row d b → List Bool → Row d b

namespace GapBankCode

variable {d b sigma : ℕ} (C : GapBankCode d b sigma)

def transcript (x : FiniteMatrix d b) : List Bool := C.protocol.run (C.bank.recode x)

def CorrectOn (F : Set (FiniteMatrix d b)) : Prop :=
  ∀ x ∈ F, ∀ j, C.decode j (x j) (C.transcript x) = transposed x j

theorem column_eq_of_same_view {F : Set (FiniteMatrix d b)} (hc : C.CorrectOn F)
    {x x' : FiniteMatrix d b} (hx : x ∈ F) (hx' : x' ∈ F)
    (ht : C.transcript x = C.transcript x') (j : Fin d) (hr : x j = x' j) :
    transposed x j = transposed x' j := by
  rw [← hc x hx j, ← hc x' hx' j, ht, hr]

/-- The concrete whole-group comparison. Every far coordinate has its whole
forward window in a gap whose stored rows are outside the group. Only two
actual correct inputs are compared; no hybrid is supplied to a decoder. -/
theorem group_eq_of_records {F : Set (FiniteMatrix d b)} (hc : C.CorrectOn F)
    (S N : Finset (MatrixBit d b)) {J : Type*} (gap : J → Finset (Fin d))
    (hgaps : ∀ j, IsRowInterval (gap j))
    (houtside : ∀ j, ∀ i ∈ gap j, ∀ c t, (i, (c, t)) ∉ S)
    (hcover : ∀ v ∈ S, v ∉ N → ∃ j, columnWindow sigma v.2.1 ⊆ gap j)
    {x x' : FiniteMatrix d b} (hx : x ∈ F) (hx' : x' ∈ F)
    (ht : C.transcript x = C.transcript x')
    (ho : ∀ v ∉ S, C.bank.recode x v = C.bank.recode x' v)
    (hn : ∀ v ∈ N, C.bank.recode x v = C.bank.recode x' v)
    (hs : ∀ j, C.bank.state (gap j) x = C.bank.state (gap j) x') :
    ∀ v ∈ S, C.bank.recode x v = C.bank.recode x' v := by
  intro v hv
  by_cases hvn : v ∈ N
  · exact hn v hvn
  · obtain ⟨j, hj⟩ := hcover v hv hvn
    have hrows : ∀ i ∈ gap j, x i = x' i :=
      C.bank.gap_inverse (gap j) (hgaps j) x x'
        (fun i hi c t => ho (i, (c, t)) (houtside j i hi c t)) (hs j)
    apply C.bank.forward_local x x' v
    intro c hcwin
    exact C.column_eq_of_same_view hc hx hx' ht c (hrows c (hj hcwin))

/-- With the other groups already fixed, the near values and gap states
determine the complete bank, hence the raw input by full-cube bijectivity. -/
theorem input_eq_of_records {F : Set (FiniteMatrix d b)} (hc : C.CorrectOn F)
    (S N : Finset (MatrixBit d b)) {J : Type*} (gap : J → Finset (Fin d))
    (hgaps : ∀ j, IsRowInterval (gap j))
    (houtside : ∀ j, ∀ i ∈ gap j, ∀ c t, (i, (c, t)) ∉ S)
    (hcover : ∀ v ∈ S, v ∉ N → ∃ j, columnWindow sigma v.2.1 ⊆ gap j)
    {x x' : FiniteMatrix d b} (hx : x ∈ F) (hx' : x' ∈ F)
    (ht : C.transcript x = C.transcript x')
    (ho : ∀ v ∉ S, C.bank.recode x v = C.bank.recode x' v)
    (hn : ∀ v ∈ N, C.bank.recode x v = C.bank.recode x' v)
    (hs : ∀ j, C.bank.state (gap j) x = C.bank.state (gap j) x') : x = x' := by
  apply C.bank.recode.injective
  funext v
  by_cases hv : v ∈ S
  · exact C.group_eq_of_records hc S N gap hgaps houtside hcover hx hx' ht ho hn hs v hv
  · exact ho v hv

end GapBankCode

end TransposeFollowup
