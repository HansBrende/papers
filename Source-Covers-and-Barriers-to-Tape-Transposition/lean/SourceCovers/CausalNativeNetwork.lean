import SourceCovers.CausalRoutingBound
import SourceCovers.NativeShortCount
import Mathlib.Logic.Equiv.Fin.Basic

/-! The actual native tape network underlying the causal-group theorem.
The bit equivalence retains row-major input indexing and transposed outputs. -/

namespace SourceCovers.CausalGroups

open LeanMachine Transpose Transpose.Tape Transpose.Tape.Impl Finset
open scoped BigOperators Classical
noncomputable section

variable {d b h k r : ℕ}

/-- Row-major indexing, obtained by composing the standard finite-product
equivalences rather than reproving division/modulo inverses. -/
def bitIndex : Bit d b ≃ Fin (d * d * b) :=
  (Equiv.prodAssoc (Fin d) (Fin d) (Fin b)).symm.trans
    ((Equiv.prodCongr finProdFinEquiv (Equiv.refl (Fin b))).trans finProdFinEquiv)

theorem bitIndex_val (ξ : Bit d b) :
    (bitIndex ξ).val = (ξ.1.val * d + ξ.2.1.val) * b + ξ.2.2.val := by
  change ξ.2.2.val + b * (ξ.2.1.val + d * ξ.1.val) = _
  ring

theorem bitIndex_row (ξ : Bit d b) : (bitIndex ξ).val / (d * b) = ξ.1.val := by
  have hd : 0 < d := Nat.pos_of_ne_zero fun he => by simpa [he] using ξ.1.isLt
  have hb : 0 < b := Nat.pos_of_ne_zero fun he => by simpa [he] using ξ.2.2.isLt
  rw [bitIndex_val, Nat.mul_comm d b, ← Nat.div_div_eq_div_mul]
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hb, Nat.div_eq_of_lt ξ.2.2.isLt,
    Nat.zero_add, Nat.add_comm, Nat.add_mul_div_right _ _ hd,
    Nat.div_eq_of_lt ξ.2.1.isLt, Nat.zero_add]

theorem bitIndex_tpos (ξ : Bit d b) :
    tpos d b (bitIndex ξ).val = (ξ.2.1.val * d + ξ.1.val) * b + ξ.2.2.val := by
  rw [bitIndex_val]
  exact tpos_spec ξ.2.1.isLt ξ.2.2.isLt

theorem bitIndex_tpos_order (ξ η : Bit d b) (hcol : ξ.2.1 < η.2.1) :
    tpos d b (bitIndex ξ).val ≤ tpos d b (bitIndex η).val := by
  rw [bitIndex_tpos, bitIndex_tpos]
  have hcol : ξ.2.1.val + 1 ≤ η.2.1.val := hcol
  have hrows := ξ.1.isLt
  have hbits := ξ.2.2.isLt
  have hc := Nat.mul_le_mul_right d hcol
  have hc' := Nat.mul_le_mul_right b (show ξ.2.1.val * d + ξ.1.val + 1 ≤
      η.2.1.val * d + η.1.val by nlinarith)
  nlinarith

abbrev NativeEdge (D : TSDiagram k) (r : ℕ) := ↥(D.edges r)

/-- The original tape edges, memory spine, row attachments and output blocks;
capacities and the consecutive column partition are supplied without change. -/
def nativeNetwork (D : TSDiagram k) (hD : D.Valid (d * d * b)) (hr : 1 ≤ r)
    (P : ColumnPartition d h) (cap : NativeEdge D r → ℝ) (hcap : ∀ e, 0 ≤ cap e) :
    Network d b h (D.nodes r) (NativeEdge D r) where
  partition := P
  source e := ⟨e.val.1, (edges_lt D _ e.property).1⟩
  target e := ⟨e.val.2, (edges_lt D _ e.property).2⟩
  earlier e := edges_fst_lt D _ e.property
  spine v := ⟨(v.val, v.val + 1), Finset.mem_union_left _
    ((mem_memEdges D).mpr ⟨rfl, by have := v.isLt; omega⟩)⟩
  spine_source _ := rfl
  spine_target _ := rfl
  attached i := {v | i.val ∈ D.rowsAt d b r v.val}
  output ξ := ⟨D.outNode r (tpos d b (bitIndex ξ).val),
    outNode_lt hD hr (by have := (bitIndex ξ).isLt; omega) _⟩
  output_order ξ η hcol := by
    apply Nat.findGreatest_mono_left
    exact fun v hv => hv.trans (bitIndex_tpos_order ξ η hcol)
  capacity := cap
  capacity_nonneg := hcap

namespace NativeNetwork

variable (D : TSDiagram k) (hD : D.Valid (d * d * b)) (hr : 1 ≤ r)
  (P : ColumnPartition d h) (cap : NativeEdge D r → ℝ) (hcap : ∀ e, 0 ≤ cap e)

local notation "N" => nativeNetwork D hD hr P cap hcap

/-- Every adjacency is an original physical tape edge in one direction. -/
theorem adj_edges {u v : Fin (D.nodes r)} (hadj : (N).physicalFlow.graph.Adj u v) :
    (u.val, v.val) ∈ D.edges r ∨ (v.val, u.val) ∈ D.edges r := by
  rcases hadj.2 with ⟨e, hs, ht⟩ | ⟨e, hs, ht⟩
  · have hs' : e.val.1 = u.val := congrArg Fin.val hs
    have ht' : e.val.2 = v.val := congrArg Fin.val ht
    exact Or.inl (by simpa only [← hs', ← ht'] using e.property)
  · have hs' : e.val.1 = v.val := congrArg Fin.val hs
    have ht' : e.val.2 = u.val := congrArg Fin.val ht
    exact Or.inr (by simpa only [← hs', ← ht'] using e.property)

/-- Ordinary graph walks reach the native finite balls with their exact length. -/
theorem walk_mem_ball {u v : Fin (D.nodes r)} (p : (N).physicalFlow.graph.Walk u v) :
    ∀ a j, u.val ∈ ball (D.edges r) (D.nodes r) a j →
      v.val ∈ ball (D.edges r) (D.nodes r) a (j + p.length) := by
  induction p with
  | nil => intro a j hu; simpa using hu
  | @cons u v w huv p ih =>
    intro a j hu
    have hv := mem_ball_succ hu v.isLt (adj_edges D hD hr P cap hcap huv)
    simpa only [SimpleGraph.Walk.length_cons, Nat.add_assoc, Nat.add_left_comm,
      Nat.add_comm] using ih a (j + 1) hv

/-- A short routed commodity maps to precisely its original raw bit in the
native attachment-and-distance count. No disconnected-row default is used. -/
theorem shortBit_mem_native {ξ : Bit d b} {ℓ : ℕ} (hξ : ξ ∈ (N).shortBits ℓ) :
    (bitIndex ξ).val ∈ attachedShortBits D d b r ℓ := by
  obtain ⟨a, ha, hd⟩ := ((N).mem_shortBits_iff ξ ℓ).mp hξ
  obtain ⟨p, hp⟩ := (iInf_lt_iff.mp hd : ∃ p : (N).physicalFlow.graph.Walk a ((N).output ξ),
    (p.length : ℕ∞) < ℓ)
  have hp' : p.length < ℓ := by exact_mod_cast hp
  have hℓ : 1 ≤ ℓ := by omega
  apply (mem_attachedShortBits_iff hℓ).mpr
  refine ⟨(bitIndex ξ).isLt, a.val, a.isLt, ?_, ?_⟩
  · rw [bitIndex_row]
    exact ha
  · have hb := walk_mem_ball D hD hr P cap hcap p a.val 0 (by simp [ball])
    exact ball_mono a.val (show 0 + p.length ≤ ℓ - 1 by omega) hb

theorem card_shortBits_le_native (ℓ : ℕ) :
    ((N).shortBits ℓ).card ≤ (attachedShortBits D d b r ℓ).card := by
  apply Finset.card_le_card_of_injOn (fun ξ => (bitIndex ξ).val)
  · intro ξ hξ; exact shortBit_mem_native D hD hr P cap hcap hξ
  · intro ξ _ η _ he; exact bitIndex.injective (Fin.ext he)

/-- The finite bound applies to the actual native network, for every positive
entry width and any radius, including zero. -/
theorem card_shortBits_le (hrdb : r ≤ d * b) (ℓ : ℕ) :
    ((N).shortBits ℓ).card ≤ min (d * d * b)
      ((2 * D.nodes r - 1) * b * (2 * k + 3) ^ (ℓ - 1)) :=
  (card_shortBits_le_native D hD hr P cap hcap ℓ).trans
    (card_attachedShortBits_le hD hrdb)

end NativeNetwork

end
end SourceCovers.CausalGroups
