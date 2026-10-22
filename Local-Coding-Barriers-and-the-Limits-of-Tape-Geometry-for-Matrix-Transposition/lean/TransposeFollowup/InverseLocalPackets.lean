import TransposeFollowup.InverseRowBank
import TransposeFollowup.CoordinatePackets
import TransposeFollowup.CoordinateEntropy

/-! Fixed nonlinear coordinate packets after a globally bijective bank.
The receiver retains its original row; inverse locality is stated explicitly.
Correctness on a family is separate from the full-cube bank bijection. -/

namespace TransposeFollowup

open Classical
set_option autoImplicit false

structure InverseLocalPacketCode (d b B : ℕ) where
  bank : InverseRowBank d b
  system : CoordinateSystem (MatrixBit d b) B
  decode : Fin d → Row d b → (Fin B → Bool) → Row d b

namespace InverseLocalPacketCode

variable {d b B : ℕ} (C : InverseLocalPacketCode d b B)

def broadcast (x : FiniteMatrix d b) : Fin B → Bool :=
  C.system.broadcast (C.bank.recode x)

def CorrectOn (F : Set (FiniteMatrix d b)) : Prop :=
  ∀ x ∈ F, ∀ j, C.decode j (x j) (C.broadcast x) = transposed x j

def LocalTo (G : SimpleGraph (Fin d)) : Prop :=
  ∀ k, ∀ v ∈ (C.system.packet k).support, ∀ w ∈ (C.system.packet k).support,
    v.1 = w.1 ∨ G.Adj v.1 w.1

theorem column_eq_of_same_view {F : Set (FiniteMatrix d b)} (hc : C.CorrectOn F)
    {x x' : FiniteMatrix d b} (hx : x ∈ F) (hx' : x' ∈ F)
    (hm : C.broadcast x = C.broadcast x') (j : Fin d) (hr : x j = x' j) :
    transposed x j = transposed x' j := by
  rw [← hc x hx j, ← hc x' hx' j, hm, hr]

theorem local_variable_edge {G : SimpleGraph (Fin d)} (hG : C.LocalTo G)
    {v w : MatrixBit d b} (h : C.system.graph.Adj v w) :
    v.1 = w.1 ∨ G.Adj v.1 w.1 := by
  obtain ⟨_, k, hv, hw⟩ := h
  exact hG k v hv w hw

theorem component_coordinates_near {G : SimpleGraph (Fin d)} (hG : C.LocalTo G)
    {S : Finset (MatrixBit d b)} (hS : S ∈ C.system.components)
    {ell : ℕ} (hsize : S.card ≤ ell) {v w : MatrixBit d b}
    (hv : v ∈ S) (hw : w ∈ S) : GraphNear G ell v.1 w.1 := by
  have hvS := (C.system.mem_component_iff hS v).mp hv
  have hwC : w ∈ C.system.component v := by rw [hvS]; exact hw
  obtain ⟨p, hp⟩ := component_short_walk C.system.graph hwC
  obtain ⟨q, hq⟩ := project_walk Prod.fst (C.local_variable_edge hG) p
  refine ⟨q, hq.trans_lt ?_⟩
  change p.length < (C.system.component v).card at hp
  rw [hvS] at hp
  exact hp.trans_le hsize

/-- The latent components required to recover a particular original row. -/
noncomputable def rowComponents (U : Finset (Finset (MatrixBit d b))) (i : Fin d) :
    Finset (Finset (MatrixBit d b)) :=
  U.filter (fun S => ∃ v ∈ S, v.1 ∈ C.bank.support i)

theorem rowComponents_disjoint_of_not_near
    {G : SimpleGraph (Fin d)} (hG : C.LocalTo G) {ell : ℕ}
    {U : Finset (Finset (MatrixBit d b))}
    (hU : ∀ S ∈ U, S ∈ C.system.components ∧ S.card ≤ ell)
    {i j : Fin d} (hfar : ¬ InverseSupportNear C.bank.support G ell i j) :
    Disjoint (C.rowComponents U i) (C.rowComponents U j) := by
  apply Finset.disjoint_left.mpr
  intro S hi hj
  obtain ⟨hSU, v, hv, hvi⟩ := Finset.mem_filter.mp hi
  obtain ⟨_, w, hw, hwj⟩ := Finset.mem_filter.mp hj
  exact hfar ⟨v.1, hvi, w.1, hwj,
    C.component_coordinates_near hG (hU S hSU).1 (hU S hSU).2 hv hw⟩

theorem row_eq_of_component_views
    (U : Finset (Finset (MatrixBit d b))) (i : Fin d)
    {x x' : FiniteMatrix d b}
    (hout : ∀ v ∉ U.biUnion id, C.bank.recode x v = C.bank.recode x' v)
    (hcomponents : ∀ S ∈ C.rowComponents U i, ∀ v ∈ S,
      C.bank.recode x v = C.bank.recode x' v) : x i = x' i := by
  apply C.bank.row_eq_of_recode_eq
  intro u hu j t
  by_cases hv : (u, (j, t)) ∈ U.biUnion id
  · obtain ⟨S, hSU, hvS⟩ := Finset.mem_biUnion.mp hv
    exact hcomponents S (Finset.mem_filter.mpr ⟨hSU, (u, (j, t)), hvS, hu⟩)
      (u, (j, t)) hvS
  · exact hout _ hv

end InverseLocalPacketCode
end TransposeFollowup
