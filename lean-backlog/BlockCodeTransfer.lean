import BlockRowGrouping
import BlockCutPrice

/-!
# Robust block-code fibres are whole-row codes

Only messages on the solving input set need obey their capacities. The
observation uses residues to be a total finite-valued function; on that
set the residues equal the actual messages. Exceptional columns are paid
by the existing whole-row fibre bound.
-/

namespace LeanBacklog.BlockTCC

open Finset Transpose Transpose.Tape Transpose.Tape.Impl MergeDepth
open RowSpread TapeStorageRates.PaidInputs
open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Classical in
noncomputable def cutEdges {k : ℕ} (Dg : TSDiagram k) (r : ℕ) (Γ : Finset ℕ) :
    Finset (ℕ × ℕ) := (Dg.edges r).filter fun e => e.1 ∈ Γ

open Classical in
noncomputable def cutOutputs {k : ℕ} (Dg : TSDiagram k) (L r : ℕ) (Γ : Finset ℕ) :
    Finset (Fin L) := univ.filter fun o => Dg.outNode r o.val ∈ Γ

abbrev BlockRecord {k : ℕ} (Dg : TSDiagram k) (d b r : ℕ)
    (cap : ℕ × ℕ → ℕ) (Γ : Finset ℕ) :=
  ((e : cutEdges Dg r Γ) → Fin (2 ^ cap e.val)) × (cutOutputs Dg (d * d * b) r Γ → Bool)

noncomputable def observe {k : ℕ} (Dg : TSDiagram k) (d b r : ℕ)
    (cap : ℕ × ℕ → ℕ) (Γ : Finset ℕ) (code : NetCode)
    (x : Fin (d * d * b) → Bool) : BlockRecord Dg d b r cap Γ :=
  (fun e => ⟨code.edgeVal (Dg.edges r) (fun y => Dg.visible d b r y x) e.val % 2 ^ cap e.val,
      Nat.mod_lt _ (by positivity)⟩,
   fun o => x (tposOf d b o.val))

theorem card_blockRecord {k d b r : ℕ} (Dg : TSDiagram k)
    (cap : ℕ × ℕ → ℕ) (Γ : Finset ℕ) :
    Fintype.card (BlockRecord Dg d b r cap Γ) =
      2 ^ ((∑ e ∈ cutEdges Dg r Γ, cap e) + (cutOutputs Dg (d * d * b) r Γ).card) := by
  classical
  simp only [BlockRecord, Fintype.card_prod, Fintype.card_pi, Fintype.card_fin,
    Fintype.card_bool, prod_pow_eq_pow_sum]
  simp only [prod_const, card_univ, Fintype.card_coe]
  rw [sum_coe_sort, ← pow_add]

theorem observe_edge_eq {k d b r : ℕ} {Dg : TSDiagram k}
    {cap : ℕ × ℕ → ℕ} {Γ : Finset ℕ} {code : NetCode}
    {x y : Fin (d * d * b) → Bool}
    (hx : ∀ e ∈ Dg.edges r, code.edgeVal (Dg.edges r) (fun v => Dg.visible d b r v x) e < 2 ^ cap e)
    (hy : ∀ e ∈ Dg.edges r, code.edgeVal (Dg.edges r) (fun v => Dg.visible d b r v y) e < 2 ^ cap e)
    (hobs : observe Dg d b r cap Γ code x = observe Dg d b r cap Γ code y)
    {e : ℕ × ℕ} (he : e ∈ Dg.edges r) (heΓ : e.1 ∈ Γ) :
    code.edgeVal (Dg.edges r) (fun v => Dg.visible d b r v x) e =
      code.edgeVal (Dg.edges r) (fun v => Dg.visible d b r v y) e := by
  classical
  have he' : e ∈ cutEdges Dg r Γ := mem_filter.mpr ⟨he, heΓ⟩
  have hh := congrArg Fin.val (congrFun (congrArg Prod.fst hobs) ⟨e, he'⟩)
  simpa only [observe, Nat.mod_eq_of_lt (hx e he), Nat.mod_eq_of_lt (hy e he)] using hh

theorem observe_output_eq {k d b r : ℕ} {Dg : TSDiagram k}
    {cap : ℕ × ℕ → ℕ} {Γ : Finset ℕ} {code : NetCode}
    {x y : Fin (d * d * b) → Bool}
    (hobs : observe Dg d b r cap Γ code x = observe Dg d b r cap Γ code y)
    (o : Fin (d * d * b)) (ho : Dg.outNode r o.val ∈ Γ) :
    x (tposOf d b o) = y (tposOf d b o) := by
  classical
  exact congrFun (congrArg Prod.snd hobs) ⟨o, mem_filter.mpr ⟨mem_univ _, ho⟩⟩

/-- The actual code fibre, grouped into the canonical entries. No
full-cube correctness or independent sources are assumed. -/
theorem fibre_wholeRow {k d G D M : ℕ} {Dg : TSDiagram k}
    (hDg : Dg.Valid (d * d * entryBits d)) (hr : 1 ≤ TSDiagram.blockSize G d)
    (Γ : Finset ℕ) (rank : ℕ → ℕ)
    (hrank_le : ∀ v, rank v ≤ D)
    (hrank : ∀ e ∈ Dg.edges (TSDiagram.blockSize G d),
      e.1 ∉ Γ → e.2 ∉ Γ → rank e.1 < rank e.2)
    {cap : ℕ × ℕ → ℕ} {F : Set (Fin (d * d * entryBits d) → Bool)} {code : NetCode}
    (hsolve : Dg.Solves d G cap F code)
    (C : Finset (Fin (d * d * entryBits d) → Bool)) (hCF : ∀ x ∈ C, x ∈ F)
    (hobs : ∀ x ∈ C, ∀ y ∈ C,
      observe Dg d (entryBits d) (TSDiagram.blockSize G d) cap Γ code x =
      observe Dg d (entryBits d) (TSDiagram.blockSize G d) cap Γ code y) :
    IsWholeRowCodeExcept
      (blockHelpers Dg d (entryBits d) (TSDiagram.blockSize G d) D M)
      (badOutputRows Dg d (entryBits d) (TSDiagram.blockSize G d) M)
      (C.image entryWord) := by
  classical
  let b := entryBits d
  let r := TSDiagram.blockSize G d
  rw [wholeRowCode_iff]
  intro x hx y hy j hj hxy i
  obtain ⟨x₀, hx₀, rfl⟩ := mem_image.mp hx
  obtain ⟨y₀, hy₀, rfl⟩ := mem_image.mp hy
  funext t
  change x₀ (matrixAddr i j t) = y₀ (matrixAddr i j t)
  let o := matrixAddr j i t
  let v := Dg.outNode r o.val
  have hm := hobs x₀ hx₀ y₀ hy₀
  by_cases hvΓ : v ∈ Γ
  · simpa only [o, tpos_matrixAddr] using observe_output_eq hm o hvΓ
  · have hxsol := hsolve x₀ (hCF x₀ hx₀)
    have hysol := hsolve y₀ (hCF y₀ hy₀)
    have hvN : v < Dg.nodes r := outNode_lt hDg hr (by have := o.isLt; omega) o.val
    have hvSlots : v ∈ rowSlots Dg d b r j :=
      mem_rowSlots hDg hr o j (matrixAddr_row j i t)
    have hagree : ∀ p : Fin (d * d * b), p.val / (d * b) ∈ nodeRows Dg d b r D v →
        x₀ p = y₀ p := by
      intro p hp
      obtain ⟨⟨e,u⟩, rfl⟩ := (finProdFinEquiv : Fin (d*d) × Fin b ≃ _).surjective p
      obtain ⟨⟨s,l⟩, rfl⟩ := (finProdFinEquiv : Fin d × Fin d ≃ _).surjective e
      change (matrixAddr s l u).val / (d * b) ∈ nodeRows Dg d b r D v at hp
      have hs : s ∈ blockHelpers Dg d b r D M j :=
        mem_blockHelpers hj hvSlots (by simpa only [matrixAddr_row] using hp)
      exact congrFun (hxy s hs l) u
    have hout := code_local rank (edges_lt Dg) hrank code
      (fun z => Dg.visible d b r z x₀) (fun z => Dg.visible d b r z y₀)
      (fun e he heΓ => observe_edge_eq hxsol.1 hysol.1 hm he heΓ)
      hvN hvΓ (hrank_le v) (fun z hz => visible_eq_of_rows Dg x₀ y₀ hagree hz) o.val
    have htpos : Transpose.Tape.tpos d b (matrixAddr i j t).val = o.val := by
      exact congrArg Fin.val (tpos_matrixAddr i j t)
    have hxout := hxsol.2 (matrixAddr i j t).val (matrixAddr i j t).isLt
    have hyout := hysol.2 (matrixAddr i j t).val (matrixAddr i j t).isLt
    rw [htpos] at hxout hyout
    exact hxout.symm.trans (hout.trans hyout)

#print axioms cutEdges
#print axioms cutOutputs
#print axioms BlockRecord
#print axioms observe
#print axioms card_blockRecord
#print axioms observe_edge_eq
#print axioms observe_output_eq
#print axioms fibre_wholeRow

end LeanBacklog.BlockTCC
