import BlockCut
import ConeCodeTransfer
import Transpose.Tape.CEProfile
import Transpose.Tape.MStarTM

/-!
# Local determination in a cut block network

The network code may be nonlinear and nonuniform. Equal outgoing cut
messages and equal rows in a bounded ball determine every uncut output.
-/

namespace LeanBacklog.BlockTCC

open Finset Transpose Transpose.Tape Transpose.Tape.Impl
open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem self_mem_ball (E : Finset (ℕ × ℕ)) (N a j : ℕ) : a ∈ ball E N a j :=
  ball_mono a (Nat.zero_le j) (by simp [ball_zero])

/-- Moving the centre across an edge increases the radius by at most one. -/
theorem ball_move {E : Finset (ℕ × ℕ)} {N a b : ℕ} (ha : a < N)
    (hab : (a, b) ∈ E ∨ (b, a) ∈ E) (j : ℕ) :
    ball E N a j ⊆ ball E N b (j + 1) := by
  classical
  induction j with
  | zero =>
    intro u hu
    have : u = a := by simpa [ball_zero] using hu
    subst u
    exact mem_ball_succ (by simp [ball_zero]) ha hab.symm
  | succ j ih =>
    intro u hu
    rw [ball_succ] at hu
    rcases mem_union.mp hu with hu | hu
    · exact ball_mono_succ _ _ (ih hu)
    · obtain ⟨huN, v, hv, he⟩ := mem_filter.mp hu
      exact mem_ball_succ (ih hv) (mem_range.mp huN) he

/-- Locality on a robust input set is an equality argument. Capacity
bounds and independence are unnecessary for this lemma. -/
theorem code_local {E : Finset (ℕ × ℕ)} {N D : ℕ} {Γ : Finset ℕ}
    (rank : ℕ → ℕ) (hE : ∀ e ∈ E, e.1 < N ∧ e.2 < N)
    (hrank : ∀ e ∈ E, e.1 ∉ Γ → e.2 ∉ Γ → rank e.1 < rank e.2)
    (code : NetCode) (vis vis' : ℕ → ℕ → Bool)
    (hcut : ∀ e ∈ E, e.1 ∈ Γ → code.edgeVal E vis e = code.edgeVal E vis' e)
    {v : ℕ} (hv : v < N) (hvΓ : v ∉ Γ) (hvD : rank v ≤ D)
    (hvis : ∀ u ∈ ball E N v D, vis u = vis' u) (o : ℕ) :
    code.outVal E vis v o = code.outVal E vis' v o := by
  classical
  have hlocal : ∀ v, v < N → v ∉ Γ →
      (∀ u ∈ ball E N v (rank v), vis u = vis' u) →
      code.inVals E vis v = code.inVals E vis' v := by
    intro v
    induction v using Nat.strong_induction_on with
    | h v ih =>
      intro hv hvΓ hagree
      funext e
      rw [inVals_eq, inVals_eq]
      split_ifs with he
      · by_cases heΓ : e.1 ∈ Γ
        · exact hcut e he.1 heΓ
        · have heN := (hE e he.1).1
          have hlt : rank e.1 < rank v := by
            simpa only [he.2.1] using hrank e he.1 heΓ (by rwa [he.2.1])
          have hev : (e.1, v) = e := Prod.ext rfl he.2.1.symm
          have hsub : ball E N e.1 (rank e.1) ⊆ ball E N v (rank v) :=
            (ball_move heN (Or.inl (show (e.1, v) ∈ E by rw [hev]; exact he.1)) _).trans
              (ball_mono v hlt)
          have hvals := ih e.1 he.2.2 heN heΓ (fun u hu => hagree u (hsub hu))
          have hraw := hagree e.1 (hsub (self_mem_ball E N e.1 (rank e.1)))
          rw [hvals, hraw]
      · rfl
  have hvals := hlocal v hv hvΓ (fun u hu => hvis u (ball_mono v hvD hu))
  have hraw := hvis v (self_mem_ball E N v D)
  simp only [NetCode.outVal, hvals, hraw]

/-- Whole input rows exposed in a radius-`D` block ball. -/
noncomputable def nodeRows {k : ℕ} (Dg : TSDiagram k) (d b r D v : ℕ) : Finset ℕ :=
  (ball (Dg.edges r) (Dg.nodes r) v D).biUnion (Dg.rowsAt d b r)

theorem card_nodeRows {k L d b r : ℕ} {Dg : TSDiagram k}
    (hDg : Dg.Valid L) (hr : 1 ≤ r) (hwidth : r ≤ d * b) (D v : ℕ) :
    (nodeRows Dg d b r D v).card ≤ 2 * (2 * k + 3) ^ D := by
  classical
  calc
    _ ≤ ∑ u ∈ ball (Dg.edges r) (Dg.nodes r) v D, (Dg.rowsAt d b r u).card := card_biUnion_le
    _ ≤ ∑ _u ∈ ball (Dg.edges r) (Dg.nodes r) v D, 2 :=
      sum_le_sum fun u _ => card_rowsAt_le hDg hwidth u
    _ = 2 * (ball (Dg.edges r) (Dg.nodes r) v D).card := by simp [mul_comm]
    _ ≤ _ := Nat.mul_le_mul_left 2 (card_ball_le hDg hr v D)

theorem visible_eq_of_rows {k d b r L D v : ℕ} (Dg : TSDiagram k)
    (x y : Fin L → Bool)
    (hrows : ∀ p : Fin L, p.val / (d * b) ∈ nodeRows Dg d b r D v → x p = y p)
    {u : ℕ} (hu : u ∈ ball (Dg.edges r) (Dg.nodes r) v D) :
    Dg.visible d b r u x = Dg.visible d b r u y := by
  classical
  funext p
  unfold TSDiagram.visible
  split_ifs with hp hr
  · exact hrows ⟨p, hp⟩ (mem_biUnion.mpr ⟨u, hu, hr⟩)
  · rfl
  · rfl

#print axioms self_mem_ball
#print axioms ball_move
#print axioms code_local
#print axioms nodeRows
#print axioms card_nodeRows
#print axioms visible_eq_of_rows

end LeanBacklog.BlockTCC
