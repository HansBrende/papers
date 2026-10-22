import TransposeFollowup.CoordinatePackets
import TransposeFollowup.ComponentDistance

/-! Arbitrary two-coordinate Boolean packets after independent, bijective,
possibly nonlinear row recodings. Correctness is on every raw input. -/

namespace TransposeFollowup

open Classical
set_option autoImplicit false

structure RecodedPacketCode (n b B : ℕ) where
  recode : (i : Fin n) → Row n b ≃ Row n b
  system : CoordinateSystem (MatrixBit n b) B
  decode : Fin n → Row n b → (Fin B → Bool) → Row n b

namespace RecodedPacketCode

variable {n b B : ℕ} (C : RecodedPacketCode n b B)

def transformedEquiv : FiniteMatrix n b ≃ (MatrixBit n b → Bool) := rowRecodingEquiv C.recode

def broadcast (x : FiniteMatrix n b) : Fin B → Bool := C.system.broadcast (C.transformedEquiv x)

def Correct : Prop := ∀ x j, C.decode j (x j) (C.broadcast x) = transposed x j

def LocalTo (G : SimpleGraph (Fin n)) : Prop :=
  ∀ k v w, v ∈ (C.system.packet k).support → w ∈ (C.system.packet k).support →
    v.1 = w.1 ∨ G.Adj v.1 w.1

theorem local_variable_edge (G : SimpleGraph (Fin n)) (hG : C.LocalTo G)
    {v w : MatrixBit n b} (h : C.system.graph.Adj v w) : v.1 = w.1 ∨ G.Adj v.1 w.1 := by
  obtain ⟨_, k, hv, hw⟩ := h
  exact hG k v w hv hw

theorem component_rows_near (G : SimpleGraph (Fin n)) (hG : C.LocalTo G)
    {S : Finset (MatrixBit n b)} (hS : S ∈ C.system.components)
    (ell : ℕ) (hsize : S.card ≤ ell) {i j : Fin n}
    (hi : i ∈ RecodedXorCode.rowsOf S) (hj : j ∈ RecodedXorCode.rowsOf S) :
    GraphNear G ell i j := by
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hj
  have hvS := (C.system.mem_component_iff hS v).mp hv
  have hwC : w ∈ C.system.component v := by rw [hvS]; exact hw
  obtain ⟨p, hp⟩ := component_short_walk C.system.graph hwC
  obtain ⟨q, hq⟩ := project_walk Prod.fst (C.local_variable_edge G hG) p
  refine ⟨q, hq.trans_lt ?_⟩
  change p.length < (C.system.component v).card at hp
  rw [hvS] at hp
  exact hp.trans_le hsize

theorem inverse_row_eq_of_outside {S : Finset (MatrixBit n b)}
    {z z' : MatrixBit n b → Bool} (hz : ∀ v ∉ S, z v = z' v)
    {i : Fin n} (hi : i ∉ RecodedXorCode.rowsOf S) :
    C.transformedEquiv.symm z i = C.transformedEquiv.symm z' i := by
  change (C.recode i).symm _ = (C.recode i).symm _
  congr 1
  funext j t
  apply hz
  intro h
  exact hi (Finset.mem_image_of_mem Prod.fst h)

theorem column_eq_of_same_view (hc : C.Correct) {x y : FiniteMatrix n b}
    (hm : C.broadcast x = C.broadcast y) (j : Fin n) (hr : x j = y j) :
    transposed x j = transposed y j := by
  rw [← hc x j, ← hc y j, hm, hr]

/-- A same-broadcast change inside one recoded component changes raw bits
only in the square of that component's represented rows. -/
theorem same_broadcast_outside_square (hc : C.Correct)
    {S : Finset (MatrixBit n b)} {z z' : MatrixBit n b → Bool}
    (hz : ∀ v ∉ S, z v = z' v) (hm : C.system.broadcast z = C.system.broadcast z')
    (v : MatrixBit n b)
    (hv : v.1 ∉ RecodedXorCode.rowsOf S ∨ v.2.1 ∉ RecodedXorCode.rowsOf S) :
    matrixBits (C.transformedEquiv.symm z) v = matrixBits (C.transformedEquiv.symm z') v := by
  rcases hv with hi | hj
  · exact congrFun (congrFun (C.inverse_row_eq_of_outside hz hi) v.2.1) v.2.2
  · have hb : C.broadcast (C.transformedEquiv.symm z) =
        C.broadcast (C.transformedEquiv.symm z') := by
      simpa only [broadcast, C.transformedEquiv.apply_symm_apply] using hm
    have hcol := C.column_eq_of_same_view hc hb v.2.1 (C.inverse_row_eq_of_outside hz hj)
    simpa only [transposed_apply, matrixBits] using congrFun (congrFun hcol v.1) v.2.2

end RecodedPacketCode

noncomputable def RecodedXorCode.toRecodedPacketCode {n b B : ℕ} (C : RecodedXorCode n b B) :
    RecodedPacketCode n b B where
  recode := C.recode
  system := C.system.toCoordinateSystem
  decode := C.decode

theorem RecodedXorCode.toRecodedPacketCode_correct {n b B : ℕ} (C : RecodedXorCode n b B)
    (hc : C.Correct) : C.toRecodedPacketCode.Correct := by
  intro x j
  simpa [RecodedPacketCode.broadcast, RecodedXorCode.toRecodedPacketCode,
    RecodedPacketCode.transformedEquiv, RecodedXorCode.broadcast,
    RecodedXorCode.transformedEquiv] using hc x j

theorem RecodedXorCode.toRecodedPacketCode_local {n b B : ℕ} (C : RecodedXorCode n b B)
    (G : SimpleGraph (Fin n)) (hG : C.LocalTo G) : C.toRecodedPacketCode.LocalTo G := by
  intro k v w hv hw
  change v ∈ (C.system.packet k).toCoordinatePacket.support at hv
  change w ∈ (C.system.packet k).toCoordinatePacket.support at hw
  cases hk : C.system.packet k with
  | single a =>
      simp only [hk, XorPacket.toCoordinatePacket, Finset.mem_singleton] at hv hw
      exact Or.inl (by rw [hv, hw])
  | pair a e =>
      simp only [hk, XorPacket.toCoordinatePacket, Finset.mem_insert, Finset.mem_singleton] at hv hw
      rcases hv with rfl | rfl <;> rcases hw with rfl | rfl
      · exact Or.inl rfl
      · exact hG k _ _ hk
      · exact (hG k _ _ hk).elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)
      · exact Or.inl rfl

end TransposeFollowup
