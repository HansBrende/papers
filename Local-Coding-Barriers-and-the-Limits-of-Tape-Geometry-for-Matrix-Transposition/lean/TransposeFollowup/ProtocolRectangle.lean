import TransposeFollowup.RowCode
import TransposeFollowup.RectangleEntropy

/-! The finite-entropy argument connected to actual adaptive row protocols.
All mathematical matrix operations continue to use the upstream adapter. -/

namespace TransposeFollowup

open scoped BigOperators
set_option autoImplicit false

def rowGroup {n : ℕ} {κ : Type*} (S : Finset (Fin n)) (component : Fin n → κ)
    (i : Fin n) : Option κ := if i ∈ S then none else some (component i)

def bitOwner {n b : ℕ} {κ : Type*} (S : Finset (Fin n)) (component : Fin n → κ)
    (i : MatrixBit n b) : Option κ := rowGroup S component i.1

def bitDemander {n b : ℕ} {κ : Type*} (S : Finset (Fin n)) (component : Fin n → κ)
    (i : MatrixBit n b) : Option κ := rowGroup S component i.2.1

def separatorBits {n b : ℕ} (S : Finset (Fin n)) : Finset (MatrixBit n b) :=
  Finset.univ.filter (fun i => i.1 ∈ S)

def protocolFiberBits {n b : ℕ} (p : PublicProtocol (Fin n) (fun _ => Row n b))
    (m : List Bool) (S : Finset (Fin n)) (base : FiniteMatrix n b) :
    Finset (MatrixBit n b → Bool) :=
  Finset.univ.filter (fun x => p.run (bitsMatrix x) = m ∧
    ∀ i ∈ S, bitsMatrix x i = base i)

theorem row_eq_of_group_view {n b : ℕ} {κ : Type*} [DecidableEq κ]
    (S : Finset (Fin n)) (component : Fin n → κ)
    (x y : MatrixBit n b → Bool) (a : Option κ)
    (hview : bitView (ownedCoordinates (bitOwner S component) a) x =
      bitView (ownedCoordinates (bitOwner S component) a) y)
    (i : Fin n) (hi : rowGroup S component i = a) :
    bitsMatrix x i = bitsMatrix y i := by
  funext j t
  exact (bitView_eq_iff _ _ _).mp hview (i, (j, t))
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)

theorem protocolFiberBits_rectangle {n b : ℕ} {κ : Type*} [DecidableEq κ]
    (p : PublicProtocol (Fin n) (fun _ => Row n b)) (m : List Bool)
    (S : Finset (Fin n)) (component : Fin n → κ) (base : FiniteMatrix n b)
    (hb : p.run base = m)
    (hs : p.Along (PublicProtocol.Separated S component) m) :
    CoordinateRectangle (bitOwner S component) (protocolFiberBits p m S base) := by
  classical
  intro x hx
  have hfix : ∀ i ∈ S, bitsMatrix x i = base i := by
    obtain ⟨y, hy, hv⟩ := hx none
    have hy' := (Finset.mem_filter.mp hy).2
    intro i hi
    exact (row_eq_of_group_view S component x y none hv i (by simp [rowGroup, hi])).trans
      (hy'.2 i hi)
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  apply (p.fiber_factorization m S component base (bitsMatrix x) hb hs).mpr
  refine ⟨hfix, ?_⟩
  intro c
  obtain ⟨y, hy, hv⟩ := hx (some c)
  have hy' := (Finset.mem_filter.mp hy).2
  refine ⟨bitsMatrix y, hy'.1, hy'.2, ?_⟩
  intro i hci
  by_cases hi : i ∈ S
  · exact (hy'.2 i hi).trans (hfix i hi).symm
  · exact (row_eq_of_group_view S component x y (some c) hv i
      (by simp [rowGroup, hi, hci])).symm

/-- Within a correct helper/transcript fiber, every component's demanded
coordinates are determined by its own rows. This includes separator columns:
their receivers' entire rows are fixed on the fiber. -/
theorem RowCode.group_decoding {n b : ℕ} {H Ω κ : Type*} [DecidableEq κ]
    (C : RowCode n b H) (F : Set (FiniteMatrix n b)) (hc : C.CorrectOn F)
    (X : Ω → FiniteMatrix n b) (hF : ∀ x, X x ∈ F)
    (hz : ∀ x y, C.helper (X x) = C.helper (X y))
    (hm : ∀ x y, C.transcript (X x) = C.transcript (X y))
    (S : Finset (Fin n)) (component : Fin n → κ) (a : Option κ) :
    (fun x => bitView (ownedCoordinates (bitDemander S component) a) (matrixBits (X x))).FactorsThrough
      (fun x => bitView (ownedCoordinates (bitOwner S component) a) (matrixBits (X x))) := by
  intro x y hv
  apply (bitView_eq_iff _ _ _).mpr
  intro i hi
  have hg : rowGroup S component i.2.1 = a := by
    exact (Finset.mem_filter.mp hi).2
  have hr := row_eq_of_group_view S component (matrixBits (X x)) (matrixBits (X y))
    a hv i.2.1 hg
  have hcol := C.column_eq_of_same_view hc (hF x) (hF y) (hz x y) (hm x y) i.2.1 hr
  have hbit := congrFun (congrFun hcol i.1) i.2.2
  simpa only [matrixBits, transposed_apply] using hbit

end TransposeFollowup
